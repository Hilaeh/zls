//! Implementation of [`textDocument/references`](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_references)

const std = @import("std");
const Ast = std.zig.Ast;

const Server = @import("../Server.zig");
const DocumentStore = @import("../DocumentStore.zig");
const Analyser = @import("../analysis.zig");
const lsp = @import("lsp");
const types = lsp.types;
const Uri = @import("../Uri.zig");
const offsets = @import("../offsets.zig");
const ast = @import("../ast.zig");
const tracy = @import("tracy");

fn labelReferences(
    allocator: std.mem.Allocator,
    handle: *DocumentStore.Handle,
    decl: @FieldType(Analyser.Declaration, "label"),
    encoding: offsets.Encoding,
    include_decl: bool,
) error{OutOfMemory}!std.ArrayList(types.Location) {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    const tree = &handle.tree;

    // Find while / for / block from label -> iterate over children nodes, find break and continues, change their labels if they match.
    // This case can be implemented just by scanning tokens.
    const first_tok = decl.identifier;
    const last_tok = ast.lastToken(tree, decl.block);

    var locations: std.ArrayList(types.Location) = .empty;
    errdefer locations.deinit(allocator);

    if (include_decl) {
        // The first token is always going to be the label
        try locations.append(allocator, .{
            .uri = handle.uri.raw,
            .range = offsets.tokenToRange(tree, first_tok, encoding),
        });
    }

    var curr_tok = first_tok + 1;
    while (curr_tok < last_tok - 2) : (curr_tok += 1) {
        const curr_id = tree.tokenTag(curr_tok);

        if (curr_id != .keyword_break and curr_id != .keyword_continue) continue;
        if (tree.tokenTag(curr_tok + 1) != .colon) continue;
        if (tree.tokenTag(curr_tok + 2) != .identifier) continue;

        if (!std.mem.eql(u8, tree.tokenSlice(curr_tok + 2), tree.tokenSlice(first_tok))) continue;

        try locations.append(allocator, .{
            .uri = handle.uri.raw,
            .range = offsets.tokenToRange(tree, curr_tok + 2, encoding),
        });
    }

    return locations;
}

const Builder = struct {
    locations: std.ArrayList(types.Location) = .empty,
    /// this is the declaration we are searching for
    target_symbol: Analyser.DeclWithHandle,
    /// the decl is local to a function, block, etc
    local_only_decl: bool,
    /// Whether the `target_symbol` has been added
    did_add_target_symbol: bool = false,
    resolve_aliases: bool,
    analyser: *Analyser,
    encoding: offsets.Encoding,

    fn add(self: *Builder, handle: *DocumentStore.Handle, token_index: Ast.TokenIndex) error{OutOfMemory}!void {
        if (self.target_symbol.handle == handle and
        self.target_symbol.nameToken() == token_index)
    {
            if (self.did_add_target_symbol) return;
            self.did_add_target_symbol = true;
        }
        try self.locations.append(self.analyser.arena, .{
            .uri = handle.uri.raw,
            .range = offsets.tokenToRange(&handle.tree, token_index, self.encoding),
        });
    }

    fn collectReferences(self: *Builder, handle: *DocumentStore.Handle, node: Ast.Node.Index) Analyser.Error!void {
        const tracy_zone = tracy.trace(@src());
        defer tracy_zone.end();

        const arena = self.analyser.arena;
        try referenceNode(self, handle, node);
        var walker: ast.Walker = try .init(arena, &handle.tree, node);
        defer walker.deinit(arena);
        while (try walker.nextIgnoreClose(arena, &handle.tree)) |child| {
            try referenceNode(self, handle, child);
        }
    }

    fn referenceNode(
        builder: *Builder,
        handle: *DocumentStore.Handle,
        node: Ast.Node.Index,
    ) Analyser.Error!void {
        const tree = &handle.tree;
        const target_symbol_name = offsets.identifierTokenToNameSlice(
            &builder.target_symbol.handle.tree,
            builder.target_symbol.nameToken(),
        );

        var candidate: Analyser.DeclWithHandle, const name_token = candidate: switch (tree.nodeTag(node)) {
            .identifier,
            .test_decl,
            => |tag| {
                const name_token = switch (tag) {
                    .identifier => ast.identifierTokenFromIdentifierNode(tree, node) orelse return,
                    .test_decl => blk: {
                        const name_token = tree.nodeData(node).opt_token_and_node[0].unwrap() orelse return;
                        if (tree.tokenTag(name_token) != .identifier) return;
                        break :blk name_token;
                    },
                    else => unreachable,
                };
                const name = offsets.identifierTokenToNameSlice(tree, name_token);
                const is_escaped_identifier = tree.source[tree.tokenStart(name_token)] == '@';

                if (!is_escaped_identifier) {
                    if (std.mem.eql(u8, name, "_")) return;
                    if (std.zig.isPrimitive(name)) return;
                }

                if (!std.mem.eql(u8, name, target_symbol_name)) return;

                const candidate = try builder.analyser.lookupSymbolGlobal(
                    handle,
                    name,
                    tree.tokenStart(name_token),
                ) orelse return;
                break :candidate .{ candidate, name_token };
            },
            .field_access => {
                if (builder.local_only_decl) return;
                const lhs_node, const field_token = tree.nodeData(node).node_and_token;
                const name = offsets.identifierTokenToNameSlice(tree, field_token);
                if (!std.mem.eql(u8, name, target_symbol_name)) return;

                const lhs = try builder.analyser.resolveTypeOfNode(.of(lhs_node, handle)) orelse return;
                const deref_lhs = try builder.analyser.resolveDerefType(lhs) orelse lhs;

                const candidate = try deref_lhs.lookupSymbol(builder.analyser, name) orelse return;
                break :candidate .{ candidate, field_token };
            },
            .struct_init_one,
            .struct_init_one_comma,
            .struct_init,
            .struct_init_comma,
            .struct_init_dot,
            .struct_init_dot_comma,
            .struct_init_dot_two,
            .struct_init_dot_two_comma,
            => {
                if (builder.local_only_decl) return;
                var buffer: [2]Ast.Node.Index = undefined;
                const struct_init = tree.fullStructInit(&buffer, node).?;
                for (struct_init.ast.fields) |value_node| { // the node of `value` in `.name = value`
                    const name_token = tree.firstToken(value_node) - 2; // math our way two token indexes back to get the `name`
                    const name = offsets.identifierTokenToNameSlice(tree, name_token);
                    if (!std.mem.eql(u8, name, target_symbol_name)) continue;

                    const nodes = switch (tree.nodeTag(node)) {
                        .struct_init_dot,
                        .struct_init_dot_comma,
                        .struct_init_dot_two,
                        .struct_init_dot_two_comma,
                        => try ast.nodesOverlappingIndex(
                            builder.analyser.arena,
                            tree,
                            tree.tokenStart(name_token),
                        ),
                        // if this isn't an anonymous struct the type can be determined from the `T{}` directly
                        .struct_init_one,
                        .struct_init_one_comma,
                        .struct_init,
                        .struct_init_comma,
                        => &.{node},
                        else => unreachable,
                    };

                    const candidate = try builder.analyser.lookupSymbolFieldInit(
                        handle,
                        name,
                        nodes[0],
                        nodes[1..],
                    ) orelse return;

                    // if we get here then we know that the name of the field matched
                    // and duplicate fields are invalid so just return early
                    break :candidate .{ candidate, name_token };
                }
                return;
            },
            .enum_literal => {
                if (builder.local_only_decl) return;
                const name_token = tree.nodeMainToken(node);
                const name = offsets.identifierTokenToNameSlice(&handle.tree, name_token);
                if (!std.mem.eql(u8, name, target_symbol_name)) return;
                const candidate = try builder.analyser.getSymbolEnumLiteral(handle, tree.tokenStart(name_token), name) orelse return;
                break :candidate .{ candidate, name_token };
            },
            .global_var_decl,
            .local_var_decl,
            .aligned_var_decl,
            .simple_var_decl,
            => {
                if (builder.local_only_decl) return;
                const var_decl = tree.fullVarDecl(node).?;

                const alias_name_token = var_decl.ast.mut_token + 1;
                const alias_name = offsets.identifierTokenToNameSlice(&handle.tree, alias_name_token);
                if (!std.mem.eql(u8, alias_name, target_symbol_name)) return;

                const init_node = var_decl.ast.init_node.unwrap() orelse return;
                if (tree.tokenTag(var_decl.ast.mut_token) != .keyword_const) return;

                if (tree.nodeTag(init_node) != .field_access) return;
                const lhs_node, const field_token = tree.nodeData(init_node).node_and_token;
                const field_name = offsets.identifierTokenToNameSlice(tree, field_token);
                if (!std.mem.eql(u8, field_name, target_symbol_name)) return;

                const lhs = try builder.analyser.resolveTypeOfNode(.of(lhs_node, handle)) orelse return;
                const deref_lhs = try builder.analyser.resolveDerefType(lhs) orelse lhs;

                const candidate = try deref_lhs.lookupSymbol(builder.analyser, field_name) orelse return;
                break :candidate .{ candidate, alias_name_token };
            },
            else => return,
        };

        if (builder.resolve_aliases) {
            candidate = try builder.analyser.resolveVarDeclAlias(candidate) orelse candidate;
        }

        if (builder.target_symbol.eql(candidate)) {
            try builder.add(handle, name_token);
        }
    }
};

fn symbolReferences(
    analyser: *Analyser,
    request: GeneralReferencesRequest,
    target_symbol: Analyser.DeclWithHandle,
    encoding: offsets.Encoding,
    /// add `target_symbol` as a references
    include_decl: bool,
    /// The file on which the request was initiated.
    current_handle: *DocumentStore.Handle,
) Analyser.Error!std.ArrayList(types.Location) {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    std.debug.assert(target_symbol.decl != .label); // use `labelReferences` instead

    const resolve_aliases = blk: {
        const dealiased_symbol = try analyser.resolveVarDeclAlias(target_symbol) orelse target_symbol;
        break :blk dealiased_symbol.eql(target_symbol);
    };
    // const target_symbol, const resolve_aliases = switch (request) {
    //     .highlight, .rename => .{ root_symbol, dealiased_symbol.eql(root_symbol) },
    //     .references => .{ dealiased_symbol, true },
    // };

    const doc_scope = try target_symbol.handle.getDocumentScope();
    const source_index = target_symbol.handle.tree.tokenStart(target_symbol.nameToken());
    const scope_index = Analyser.innermostScopeAtIndexWithTag(doc_scope, source_index, .init(.{
        .block = true,
        .container = true,
        .function = false,
        .other = false,
    })).unwrap().?;
    const scope_node = doc_scope.getScopeAstNode(scope_index).?;

    // If `local_node != null`, references to the declaration can only be
    // found inside of the given ast node.
    const local_node: ?Ast.Node.Index = switch (target_symbol.decl) {
        .ast_node => switch (doc_scope.getScopeTag(scope_index)) {
            .block => scope_node,
            .container => null,
            .function, .other => unreachable,
        },
        .optional_payload,
        .error_union_payload,
        .error_union_error,
        .for_loop_payload,
        .assign_destructure,
        => scope_node,
        .switch_payload,
        .switch_inline_tag_payload,
        => |payload| payload.node,
        .function_parameter => |payload| payload.func,
        .label => unreachable, // handled separately by labelReferences
        .error_token => return .empty,
    };

    var builder: Builder = .{
        .analyser = analyser,
        .target_symbol = target_symbol,
        .local_only_decl = local_node != null,
        .resolve_aliases = resolve_aliases,
        .encoding = encoding,
    };
    blk: {
        if (!include_decl) break :blk;
        if (request == .highlight and !target_symbol.handle.uri.eql(current_handle.uri)) break :blk;
        try builder.add(target_symbol.handle, target_symbol.nameToken());
    }

    try builder.collectReferences(current_handle, local_node orelse .root);

    const workspace = local_node == null and request != .highlight and target_symbol.isPublic();
    if (workspace) {
        var uris = try gatherWorkspaceReferenceCandidates(
            analyser.store,
            analyser.arena,
            current_handle,
            target_symbol.handle,
        );
        for (uris.keys()) |uri| {
            if (uri.eql(current_handle.uri)) continue;
            const dependency_handle = analyser.store.getHandle(uri) orelse continue;
            try builder.collectReferences(dependency_handle, .root);
        }
    }

    return builder.locations;
}

fn resolveAssociatedBuildFile(
    store: *DocumentStore,
    handle: *DocumentStore.Handle,
) error{ Canceled, OutOfMemory }!DocumentStore.Handle.AssociatedBuildFile {
    const result = try handle.getAssociatedBuildFile(store);
    if (result != .unresolved) return result;
    // await build runner and retry once
    try store.wait_group.await(store.io);
    return handle.getAssociatedBuildFile(store);
}

fn collectAllModulesInBuildFile(arena: std.mem.Allocator, found_uris: *Uri.ArrayHashMap(void), build_file: *DocumentStore.BuildFile) error{OutOfMemory}!void {
    for (build_file.modules_imported_by.map.keys()) |module_path| {
        const module_uri: Uri = try .fromPath(arena, module_path);
        const gop = try found_uris.getOrPut(arena, module_uri);
        if (gop.found_existing) {
            module_uri.deinit(arena);
        }
    }
}

fn collectAllNonDependencyModulesInBuildFile(arena: std.mem.Allocator, found_uris: *Uri.ArrayHashMap(void), build_file: *DocumentStore.BuildFile) error{OutOfMemory}!void {
    for (build_file.modules_imported_by.map.keys(), build_file.modules_imported_by.map.values()) |module_path, entry| {
        if (entry.is_dependency) {
            continue;
        }

        const module_uri: Uri = try .fromPath(arena, module_path);
        const gop = try found_uris.getOrPut(arena, module_uri);
        if (gop.found_existing) {
            module_uri.deinit(arena);
        }
    }
}

/// Returns true if at least one build file was found.
fn collectAllNonDependencyBuildFiles(arena: std.mem.Allocator, found_uris: *Uri.ArrayHashMap(void), store: *DocumentStore) error{OutOfMemory}!bool {

    const build_files = store.build_files.values();

    if (build_files.len == 0) return false;

    var found = false;

    for (build_files) |build_file| {
        if (!isDependency(build_file, store)) {
            try collectAllNonDependencyModulesInBuildFile(arena, found_uris, build_file);
            found = true;
        }
    }

    return found;
}

/// module_root_file -> root source file of the module with the definition of the symbol
/// this will not handle a case where a module imports a module that imports a module with definition.
/// so a potential cross module alias
fn collectAllNonDepImporterModulesInBuildFile(arena: std.mem.Allocator, found_uris: *Uri.ArrayHashMap(void), module_root_file: []const u8, build_file: *DocumentStore.BuildFile) error{OutOfMemory}!void {

    // This part will add root files of all modules that import this one.
    const imported_by = build_file.modules_imported_by.map.get(module_root_file);

    if (imported_by) |entry| {
        if (!entry.is_dependency) {
            const module_uri = try Uri.fromPath(arena, module_root_file);
            const mod_gop = try found_uris.getOrPut(arena, module_uri);
            if (mod_gop.found_existing) {
                module_uri.deinit(arena);
            }
        }

        // importers will always be non dependency,
        // the method populating importers array list is called only with non dep modules.
        for (entry.importers.items) |importer_path| {
            const importer_uri = try Uri.fromPath(arena, importer_path);
            const gop = try found_uris.getOrPut(arena, importer_uri);
            if (gop.found_existing) {
                importer_uri.deinit(arena);
            }
        }
    }
}
fn collectAllImporterModulesInBuildFile(arena: std.mem.Allocator, found_uris: *Uri.ArrayHashMap(void), module_root_file: []const u8, build_file: *DocumentStore.BuildFile) error{OutOfMemory}!void {

    // This part will add root files of all modules that import this one.
    const imported_by = build_file.modules_imported_by.map.get(module_root_file);

    if (imported_by) |entry| {
        for (entry.importers.items) |importer_path| {
            const importer_uri = try Uri.fromPath(arena, importer_path);
            const gop = try found_uris.getOrPut(arena, importer_uri);
            if (gop.found_existing) {
                importer_uri.deinit(arena);
            }
        }
    }
}

// if there is an error with the path, then the return is true to exclude it
fn isDependency(build_file: *DocumentStore.BuildFile, store: *DocumentStore) bool {

    var buffer: [std.Io.Dir.max_path_bytes]u8 = undefined;
    const build_file_path = build_file.uri.toFsPathBuffer(&buffer) catch return true;

    for (store.build_files.values()) |check_build_file| {

        if (check_build_file.dependency_paths.map.contains(build_file_path)) {
            return true;
        }
    }
    return false;
}
/// Caller owns memory.
fn isDependencyOfWhat(arena: std.mem.Allocator, build_file: *DocumentStore.BuildFile, store: *DocumentStore) error{OutOfMemory}![]*DocumentStore.BuildFile {

    const build_file_path = build_file.uri.toFsPath(arena) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.UnsupportedScheme => return &.{},
    };

    var build_files: std.ArrayList(*DocumentStore.BuildFile) = .empty;

    for (store.build_files.values()) |check_build_file| {

        if (check_build_file.dependency_paths.map.contains(build_file_path)) {
            try build_files.append(arena, check_build_file);
        }
    }
    return try build_files.toOwnedSlice(arena);
}

fn gatherWorkspaceReferenceCandidates(
    store: *DocumentStore,
    arena: std.mem.Allocator,
    /// The file on which the request was initiated.
    root_handle: *DocumentStore.Handle,
    /// The file which contains the symbol that is being searched for.
    target_handle: *DocumentStore.Handle,
) Analyser.Error!Uri.ArrayHashMap(void) {

    var found_uris: Uri.ArrayHashMap(void) = .empty;

    // unfortunately, to get the imports from importing dependencies by name,
    // the build file needs to load first.
    // this is the problem with lazy build_runners.

    if (DocumentStore.supports_build_system) no_build_file: {
        // if (DocumentStore.supports_build_system) {
        const resolved = switch (try resolveAssociatedBuildFile(store, root_handle)) {
            .unresolved => return found_uris, 
            // .none => break :no_build_file,
            .none => {
                // looking outside of a build file for something...
                // should I care about the location of the definition?
                // probably this should search all internals.
                // how do I do this though without adding complexity?
                // make a special case here with declaring found uris and populating it here?
                // and doing return here?
                // std.debug.print("root no build file | ", .{});

                // This part scans all non dependency modules in non dependency build files,
                // with addition of the file in the std, but this is probably because of 
                // the input into found uris before this gathering function is called.
                // if (DocumentStore.isBuildFile(root_handle.uri)) {
                //     try found_uris.put(store.allocator, root_handle.uri, {});
                // }
                if (DocumentStore.isInStd(root_handle.uri)) {
                    // if path is null, then found uris is returned empty
                    if (store.config.zig_lib_dir.?.path) |path| {

                        const std_root = try std.Io.Dir.path.join(arena, &.{ path, "std.zig" });
                        defer arena.free(std_root);

                        const std_uri = try Uri.fromPath(arena, std_root);
                        errdefer std_uri.deinit(arena);

                        try found_uris.put(arena, std_uri, {});
                    }
                } else {
                    const found_some = try collectAllNonDependencyBuildFiles(arena, &found_uris, store);
                    // std.debug.print("found some: {any} | ", .{ found_some });
                    if (!found_some) {
                        // std.debug.print("found none | ", .{});
                        break :no_build_file;
                    }
                }

                var i: usize = 0;
                while (i < found_uris.count()) : (i += 1) {
                    const uri = found_uris.keys()[i];
                    const handle = try store.getOrLoadHandle(uri) orelse continue;

                    try found_uris.ensureUnusedCapacity(arena, handle.file_imports.len);
                    for (handle.file_imports) |import_uri| found_uris.putAssumeCapacity(import_uri, {});
                }

                // std.debug.print("build file count: {d} | ", .{ store.build_files.count() });
                for (store.build_files.values()) |build_file| {
                    // if (build_file.all_file_imports.contains(root_handle.uri.raw)) {
                    //     // root belongs in build file imports
                    // }
                    // if target is in build imoprt graph, then root is as well
                    // std.debug.print("imports count: {d} if contains: {s} for build file: {s} | ", .{ build_file.imports.count(), target_handle.uri.raw, build_file.uri.raw });
                    if (build_file.imports.contains(target_handle.uri)) {
                        // std.debug.print("build file imports duping: {s} | ", .{ build_file.uri.raw });
                        try found_uris.put(arena, build_file.uri, {});

                        try found_uris.ensureUnusedCapacity(arena, build_file.imports.count());
                        for (build_file.imports.keys()) |uri| {
                            found_uris.putAssumeCapacity(uri, {});
                        }
                    } 
                    // else {
                    //     std.debug.print("no contain | ", .{});
                    // }
                }
                return found_uris;
            }, 
            .resolved => |resolved| resolved,
        };

        // const root_module_root_uri: Uri = try .fromPath(arena, resolved.root_source_file);

        // var found_uris: Uri.ArrayHashMap(void) = .empty;
        // try found_uris.put(arena, root_module_root_uri, {});


        // a handle will be assigned to only one build file, so if the handles are the same,
        // then it is safe to assue that both build files are the same too.
        if (root_handle.uri.eql(target_handle.uri)) {

            // std.debug.print("root and target the same | ", .{});
            // std.debug.print("resolved: resolved | ", .{});

            const files = try isDependencyOfWhat(arena, resolved.build_file, store);
            defer arena.free(files);
            if (files.len == 0) {
                // is not a dependency of anything
                // std.debug.print("root is not a dependency of anything | ", .{});
                try collectAllNonDepImporterModulesInBuildFile(arena, &found_uris, resolved.root_source_file, resolved.build_file);

            } else {
                // is a dependency of files
                for (files) |candidate_file| {
                    // std.debug.print("root is a dependency of {s} | ", .{ candidate_file.uri.raw });
                    try collectAllNonDepImporterModulesInBuildFile(arena, &found_uris, resolved.root_source_file, candidate_file);
                }
            }
            // if the current handle is in dependency, show imports from the main project and also
            // this dependency.
            try collectAllNonDepImporterModulesInBuildFile(arena, &found_uris, resolved.root_source_file, resolved.build_file);

        } else {
            switch (try resolveAssociatedBuildFile(store, target_handle)) {
                .unresolved, .none => {

                    // std.debug.print("resolved: resolved, resolved2: none | ", .{});
                    const files = try isDependencyOfWhat(arena, resolved.build_file, store);
                    defer arena.free(files);
                    if (files.len == 0) {
                        // is not a dependency of anything
                        // std.debug.print("root is not a dependency of anything | ", .{});
                        try collectAllNonDependencyModulesInBuildFile(arena, &found_uris, resolved.build_file);
                    } else {
                        // is a dependency of files
                        for (files) |candidate_file| {
                            // std.debug.print("root is a dependency of {s} | ", .{ candidate_file.uri.raw });
                            try collectAllNonDependencyModulesInBuildFile(arena, &found_uris, candidate_file);
                        }
                        try collectAllNonDepImporterModulesInBuildFile(arena, &found_uris, resolved.root_source_file, resolved.build_file);
                    }
                },
                .resolved => |resolved2| {

                    // if two build files are different
                    // it is obvious that root imports target,
                    // so target is a dependency of root


                    // std.debug.print("not the same | ", .{});
                    // std.debug.print("resolved: resolved, resolved2: resolved | ", .{});

                    const files = try isDependencyOfWhat(arena, resolved.build_file, store);
                    defer arena.free(files);
                    if (files.len == 0) {
                        // is not a dependency of anything
                        // std.debug.print("root is not a dependency of anything | ", .{});
                        try collectAllNonDepImporterModulesInBuildFile(arena, &found_uris, resolved2.root_source_file, resolved.build_file);

                    } else {
                        // is a dependency of files
                        for (files) |candidate_file| {
                            // std.debug.print("root is a dependency of {s} | ", .{ candidate_file.uri.raw });
                            try collectAllNonDepImporterModulesInBuildFile(arena, &found_uris, resolved2.root_source_file, candidate_file);
                        }
                        try collectAllNonDepImporterModulesInBuildFile(arena, &found_uris, resolved2.root_source_file, resolved.build_file);
                    }
                },

            }
        }


        var i: usize = 0;
        while (i < found_uris.count()) : (i += 1) {
            const uri = found_uris.keys()[i];
            const handle = try store.getOrLoadHandle(uri) orelse continue;

            try found_uris.ensureUnusedCapacity(arena, handle.file_imports.len);
            for (handle.file_imports) |import_uri| found_uris.putAssumeCapacity(import_uri, {});
        }
        return found_uris;
    }

    var per_file_dependants: Uri.ArrayHashMap(std.ArrayList(Uri)) = .empty;

    var it: DocumentStore.HandleIterator = .{ .store = store };
    while (it.next()) |handle| {
        for (handle.file_imports) |import_uri| {
            const gop = try per_file_dependants.getOrPutValue(arena, import_uri, .empty);
            try gop.value_ptr.append(arena, handle.uri);
        }
    }

    // var found_uris: Uri.ArrayHashMap(void) = .empty;
    try found_uris.put(arena, target_handle.uri, {});

    var i: usize = 0;
    while (i < found_uris.count()) : (i += 1) {
        const uri = found_uris.keys()[i];
        const dependants: std.ArrayList(Uri) = per_file_dependants.get(uri) orelse .empty;
        try found_uris.ensureUnusedCapacity(arena, dependants.items.len);
        for (dependants.items) |dependant_uri| found_uris.putAssumeCapacity(dependant_uri, {});
    }

    return found_uris;
}
fn controlFlowReferences(
    allocator: std.mem.Allocator,
    token_handle: Analyser.TokenWithHandle,
    encoding: offsets.Encoding,
    include_decl: bool,
) error{OutOfMemory}!std.ArrayList(types.Location) {
    const handle = token_handle.handle;
    const tree = &handle.tree;
    const kw_token = token_handle.token;

    var results: std.ArrayList(Ast.TokenIndex) = .empty;
    defer results.deinit(allocator);

    switch (tree.tokenTag(kw_token)) {
        .keyword_continue,
        .keyword_break,
        => {
            const nodes = try ast.nodesOverlappingIndex(allocator, tree, handle.tree.tokenStart(kw_token));
            defer allocator.free(nodes);

            const maybe_label = blk: {
                if (kw_token + 2 >= tree.tokens.len) break :blk null;
                if (tree.tokenTag(kw_token + 1) != .colon) break :blk null;
                if (tree.tokenTag(kw_token + 2) != .identifier) break :blk null;
                break :blk offsets.identifierTokenToNameSlice(tree, kw_token + 2);
            };
            for (nodes) |node| switch (tree.nodeTag(node)) {
                .for_simple,
                .@"for",
                .while_cont,
                .while_simple,
                .@"while",
                => {
                    // if the break/continue is unlabeled it must belong to the first loop we encounter
                    const main_token = tree.nodeMainToken(node);
                    const label = maybe_label orelse break try results.append(allocator, main_token);
                    const loop_label = if (tree.isTokenPrecededByTags(main_token, &.{ .identifier, .colon }))
                        offsets.identifierTokenToNameSlice(tree, main_token - 2)
                        else
                        continue;
                    if (std.mem.eql(u8, label, loop_label)) {
                        try results.append(allocator, main_token);
                    }
                },
                .switch_comma,
                .@"switch",
                => {
                    const label = maybe_label orelse continue;
                    const main_token = tree.nodeMainToken(node);
                    const switch_label = if (tree.tokenTag(main_token) == .identifier)
                        offsets.identifierTokenToNameSlice(tree, main_token)
                        else
                        continue;
                    if (std.mem.eql(u8, label, switch_label)) {
                        try results.append(
                            allocator,
                            // we already know the switch is labeled so we can just offset
                            main_token + 2,
                        );
                    }
                },
                else => {},
            };
        },
        .keyword_for,
        .keyword_while,
        .keyword_switch,
        => |tag| {
            const maybe_label = if (tree.isTokenPrecededByTags(kw_token, &.{ .identifier, .colon }))
                offsets.identifierTokenToNameSlice(tree, kw_token - 2)
                else
                null;

            if (tag == .keyword_switch and maybe_label == null) return .empty;

            const nodes = try ast.nodesOverlappingIndex(allocator, tree, tree.tokenStart(kw_token));
            defer allocator.free(nodes);

            var walker: ast.Walker = try .init(allocator, tree, nodes[0]);
            defer walker.deinit(allocator);

            _ = try walker.nextIgnoreClose(allocator, tree);

            var loop_depth: usize = 1;

            while (try walker.next(allocator, tree)) |event| {
                switch (event) {
                    .open => |node| switch (tree.nodeTag(node)) {
                        .@"break", .@"continue" => {
                            const label_token = tree.nodeData(node).opt_token_and_opt_node[0].unwrap();
                            if (label_token) |actual_label_token| {
                                const actual_label = offsets.identifierTokenToNameSlice(tree, actual_label_token);
                                if (maybe_label) |expected_label| {
                                    if (!std.mem.eql(u8, expected_label, actual_label)) continue;
                                }
                            } else if (loop_depth > 1) continue;
                            try results.append(allocator, tree.nodeMainToken(node));
                        },

                        .@"while",
                        .while_simple,
                        .while_cont,
                        .@"for",
                        .for_simple,
                        => {
                            if (maybe_label == null) {
                                walker.skip();
                            } else {
                                loop_depth += 1;
                            }
                        },
                        else => {},
                    },
                    .close => |node| switch (tree.nodeTag(node)) {
                        .@"while",
                        .while_simple,
                        .while_cont,
                        .@"for",
                        .for_simple,
                        => {
                            if (maybe_label != null) {
                                loop_depth -= 1;
                            }
                        },
                        else => {},
                    },
                }
            }
        },
        else => return .empty,
    }

    var locations: std.ArrayList(types.Location) = try .initCapacity(allocator, results.items.len + @intFromBool(include_decl));
    errdefer locations.deinit(allocator);

    if (include_decl) {
        locations.appendAssumeCapacity(.{
            .uri = handle.uri.raw,
            .range = offsets.tokenToRange(tree, kw_token, encoding),
        });
    }

    for (results.items) |token| {
        locations.appendAssumeCapacity(.{
            .uri = handle.uri.raw,
            .range = offsets.tokenToRange(tree, token, encoding),
        });
    }
    return locations;
}

const CallBuilder = struct {
    callsites: std.ArrayList(Analyser.NodeWithHandle) = .empty,
    /// this is the declaration we are searching for
    target_decl: Analyser.DeclWithHandle,
    analyser: *Analyser,

    fn add(self: *CallBuilder, handle: *DocumentStore.Handle, call_node: Ast.Node.Index) error{OutOfMemory}!void {
        try self.callsites.append(self.analyser.arena, .{
            .handle = handle,
            .node = call_node,
        });
    }

    fn collectReferences(self: *CallBuilder, handle: *DocumentStore.Handle, node: Ast.Node.Index) Analyser.Error!void {
        const tracy_zone = tracy.trace(@src());
        defer tracy_zone.end();

        const arena = self.analyser.arena;
        var walker: ast.Walker = try .init(arena, &handle.tree, node);
        defer walker.deinit(arena);
        while (try walker.nextIgnoreClose(arena, &handle.tree)) |child| {
            try referenceNode(self, handle, child);
        }
    }

    fn referenceNode(
        builder: *CallBuilder,
        handle: *DocumentStore.Handle,
        node: Ast.Node.Index,
    ) Analyser.Error!void {
        const tree = &handle.tree;
        switch (tree.nodeTag(node)) {
            .call,
            .call_comma,
            .call_one,
            .call_one_comma,
            => {
                var buf: [1]Ast.Node.Index = undefined;
                const call = tree.fullCall(&buf, node).?;

                const called_node = call.ast.fn_expr;

                switch (tree.nodeTag(called_node)) {
                    .identifier => {
                        const identifier_token = ast.identifierTokenFromIdentifierNode(tree, called_node) orelse return;

                        const child = (try builder.analyser.lookupSymbolGlobal(
                            handle,
                            offsets.identifierTokenToNameSlice(tree, identifier_token),
                            tree.tokenStart(identifier_token),
                        )) orelse return;

                        if (builder.target_decl.eql(child)) {
                            try builder.add(handle, node);
                        }
                    },
                    .field_access => {
                        const lhs_node, const field_name = tree.nodeData(called_node).node_and_token;
                        const lhs = (try builder.analyser.resolveTypeOfNode(.of(lhs_node, handle))) orelse return;
                        const deref_lhs = try builder.analyser.resolveDerefType(lhs) orelse lhs;

                        const symbol = offsets.tokenToSlice(tree, field_name);
                        const child = (try deref_lhs.lookupSymbol(builder.analyser, symbol)) orelse return;

                        if (builder.target_decl.eql(child)) {
                            try builder.add(handle, node);
                        }
                    },
                    else => {},
                }
            },
            else => {},
        }
    }
};

pub fn callsiteReferences(
    analyser: *Analyser,
    decl_handle: Analyser.DeclWithHandle,
    /// search other files for references
    workspace: bool,
) Analyser.Error!std.ArrayList(Analyser.NodeWithHandle) {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    std.debug.assert(decl_handle.decl == .ast_node);

    var builder: CallBuilder = .{
        .analyser = analyser,
        .target_decl = decl_handle,
    };

    try builder.collectReferences(decl_handle.handle, .root);

    if (workspace) {
        var uris = try gatherWorkspaceReferenceCandidates(
            analyser.store,
            analyser.arena,
            decl_handle.handle,
            decl_handle.handle,
        );
        for (uris.keys()) |uri| {
            if (uri.eql(decl_handle.handle.uri)) continue;
            const dependency_handle = analyser.store.getHandle(uri) orelse continue;
            try builder.collectReferences(dependency_handle, .root);
        }
    }

    return builder.callsites;
}

pub const GeneralReferencesRequest = union(enum) {
    rename: types.rename.Params,
    references: types.reference.Params,
    highlight: types.DocumentHighlight.Params,

    fn uri(self: @This()) []const u8 {
        return switch (self) {
            .rename => |rename| rename.textDocument.uri,
            .references => |ref| ref.textDocument.uri,
            .highlight => |highlight| highlight.textDocument.uri,
        };
    }

    fn position(self: @This()) types.Position {
        return switch (self) {
            .rename => |rename| rename.position,
            .references => |ref| ref.position,
            .highlight => |highlight| highlight.position,
        };
    }
};

pub const GeneralReferencesResponse = union {
    rename: types.WorkspaceEdit,
    references: []types.Location,
    highlight: []types.DocumentHighlight,
};

pub fn referencesHandler(server: *Server, arena: std.mem.Allocator, request: GeneralReferencesRequest) Server.Error!?GeneralReferencesResponse {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    const uri = Uri.parse(arena, request.uri()) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => return error.InvalidParams,
    };
    const handle = server.document_store.getHandle(uri) orelse return null;
    if (handle.tree.mode == .zon) return null;

    const source_index = offsets.positionToIndex(handle.tree.source, request.position(), server.offset_encoding);
    const pos_context = try Analyser.getPositionContext(server.allocator, &handle.tree, source_index, true);

    var analyser = server.initAnalyser(arena, handle);
    defer analyser.deinit();

    const include_decl = switch (request) {
        .references => |ref| ref.context.includeDeclaration,
        else => true,
    };

    // TODO: Make this work with branching types
    const locations = locs: {
        if (pos_context == .keyword and request != .rename) {
            break :locs try controlFlowReferences(
                arena,
                .{ .token = offsets.sourceIndexToTokenIndex(&handle.tree, source_index).preferLeft(), .handle = handle },
                server.offset_encoding,
                include_decl,
            );
        }

        const name_loc = offsets.identifierLocFromIndex(&handle.tree, source_index) orelse return null;
        const name = offsets.locToSlice(handle.tree.source, name_loc);

        const target_decl = switch (pos_context) {
            .var_access, .test_doctest_name => try analyser.lookupSymbolGlobal(handle, name, source_index),
            .field_access => |loc| z: {
                const held_loc = offsets.locMerge(loc, name_loc);
                const a = try analyser.getSymbolFieldAccesses(arena, handle, source_index, held_loc, name);
                if (a) |b| {
                    if (b.len != 0) break :z b[0];
                }

                break :z null;
            },
            .label_access, .label_decl => try Analyser.lookupLabel(handle, name, source_index),
            .enum_literal => try analyser.getSymbolEnumLiteral(handle, source_index, name),
            .keyword => null,
            else => null,
        } orelse return null;



        // pub const id_3 = 1;
        //
        // const stable = @import("cells_stable.zig");
        // pub const example_cell22 = stable.id_3;
        //
        // const cell22_reference = example_cell22;
        //
        // if the resolve is made, then renaming the example_cell22 will rename id_2 instead.
        // it is wrong
        // also when looking for references of example_cell22, it does not show cell22_reference,
        // it locks into references of stable.id_3, which there is only one.
        // this function needs to go away.

        // target_decl = try analyser.resolveVarDeclAlias(target_decl) orelse target_decl;

        // std.debug.print("check target decl: {any}", .{ target_decl });

        break :locs switch (target_decl.decl) {
            .label => |payload| try labelReferences(
                arena,
                target_decl.handle,
                payload,
                server.offset_encoding,
                include_decl,
            ),
            else => try symbolReferences(
                &analyser,
                request,
                target_decl,
                server.offset_encoding,
                include_decl,
                handle,
            ),
        };
    };

    switch (request) {
        .rename => |rename| {
            const escaped_rename = try std.fmt.allocPrint(arena, "{f}", .{std.zig.fmtId(rename.newName)});
            var changes: std.array_hash_map.String(std.ArrayList(types.TextEdit)) = .empty;

            for (locations.items) |loc| {
                const gop = try changes.getOrPutValue(arena, loc.uri, .empty);
                try gop.value_ptr.append(arena, .{
                    .range = loc.range,
                    .newText = escaped_rename,
                });
            }

            var new_changes: lsp.parser.Map(types.DocumentUri, []const types.TextEdit) = .{};
            try new_changes.map.ensureTotalCapacity(arena, changes.count());

            var changes_it = changes.iterator();
            while (changes_it.next()) |entry| {
                new_changes.map.putAssumeCapacityNoClobber(entry.key_ptr.*, try entry.value_ptr.toOwnedSlice(arena));
            }

            return .{ .rename = .{ .changes = new_changes } };
        },
        .references => return .{ .references = locations.items },
        .highlight => {
            var highlights: std.ArrayList(types.DocumentHighlight) = try .initCapacity(arena, locations.items.len);
            for (locations.items) |loc| {
                std.debug.assert(std.mem.eql(u8, handle.uri.raw, loc.uri));
                highlights.appendAssumeCapacity(.{
                    .range = loc.range,
                    .kind = .Text,
                });
            }
            return .{ .highlight = highlights.items };
        },
    }
}

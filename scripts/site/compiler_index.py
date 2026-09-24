"""Build one semantic index from explicit compiler documents and payloads.

This is the sole joining point between declaration names, Unicode source ranges,
scope resolution, vocabulary forwarding, and recursively inspectable signatures.
"""
from html_contract import *
from agda_semantics import *
from document_renderer import CodeContext

def build_code_context(corpus, internal, rendered, semantics, types_raw, expression_types_raw):
    rendered_set = set(rendered)
    PRELUDE_MODULE = semantics.prelude_module
    render_type = semantics.render_type
    prelude_reexport_index = semantics.prelude_reexport_index
    rewrite_links = semantics.rewrite_links
    build_types = semantics.build_types
    add_prelude_reexport_types = semantics.add_prelude_reexport_types
    build_expression_types = semantics.build_expression_types
    inline_reference_resolver = semantics.inline_reference_resolver
    inline_ref = semantics.inline_ref
    # first pass: index every definition (names, positions, aspects) across ALL rendered modules
    name2pos, pos_aspect, local_types = {}, {}, {}
    notations = []
    compiler_scopes = {}
    prelude_reexports = {"by_href": {}, "by_name": {}}
    for m in rendered:
        content, literate = corpus.read(m)
        compiler_scopes[m] = compiler_reference_scope(content)
        notations.extend(syntax_notations(content))
        if literate:
            if m == PRELUDE_MODULE:
                prelude_reexports = prelude_reexport_index(content)
            for blk in PRE_RE.findall(content):
                index_definitions(blk, m, name2pos, pos_aspect)
                local_types.setdefault(m, {}).update(local_signature_types(blk, m))
        else:
            index_definitions(content, m, name2pos, pos_aspect)   # whole .html is code
            local_types[m] = local_signature_types(content, m)
    internal_q = {f"{m}.{n}": (m, p) for m in name2pos for n, p in name2pos[m].items()}
    add_instantiated_type_aliases(internal_q, types_raw, compiler_scopes)
    vocabulary = {}
    for m in internal:
        for name, position in name2pos.get(m, {}).items():
            aspect = pos_aspect.get(m, {}).get(position, '')
            if _BARE_REFERENCE_ASPECTS.intersection(aspect.split()):
                vocabulary.setdefault(name, set()).add((f'{m}.html#{position}', aspect))
    prelude_reexports['origin_vocabulary'] = {
        name: next(iter(targets)) for name, targets in vocabulary.items() if len(targets) == 1}
    # Actual exported vocabulary includes locally defined and renamed names.
    # Exclude pre-renaming spellings that are not in Prelude's public scope.
    exported = types_raw.get(PRELUDE_MODULE, {})
    prelude_reexports['inline'] = {
        name: (f'{PRELUDE_MODULE}.html#{position}', aspect)
        for name, (_, position, aspect, _) in prelude_reexports['by_name'].items()
        if name in exported
    }
    for name, position in name2pos.get(PRELUDE_MODULE, {}).items():
        if name in exported:
            prelude_reexports['inline'][name] = (
                f'{PRELUDE_MODULE}.html#{position}', pos_aspect[PRELUDE_MODULE].get(position, ''))
    prelude_reexports['syntax'] = []
    for href, parts in notations:
        bridge = prelude_reexports['by_href'].get(href)
        if bridge and bridge[3] in prelude_reexports['inline']:
            prelude_reexports['syntax'].append((bridge[3], parts))
    add_prelude_qualified_names(internal_q, prelude_reexports)
    types_by_module = build_types(rendered, name2pos, types_raw, internal_q,
                                  pos_aspect, prelude_reexports)
    add_prelude_reexport_types(types_by_module, types_raw, prelude_reexports,
                               internal_q, pos_aspect)
    name_pattern = qualified_name_pattern(internal_q)
    canonical_names = {module: names_by_position(module, name2pos)
                       for module in rendered}
    for name, (href, _) in prelude_reexports['inline'].items():
        canonical_names.setdefault(PRELUDE_MODULE, {})[href.rsplit('#', 1)[1]] = name
    highlighted_local_types = []
    for module, declarations in local_types.items():
        for position, declaration in declarations.items():
            full_type = types_raw.get(module, {}).get(declaration["name"])
            if full_type:
                type_html = render_type(full_type, internal_q, name_pattern,
                                        pos_aspect, module, prelude_reexports)
            else:
                type_html = declaration["type"]
                highlighted_local_types.append((module, position, type_html))
            types_by_module.setdefault(module, {}).setdefault(position, type_html)
    # Every local target is now present, so links between two declarations whose
    # types came only from highlighted HTML can both receive hover payloads.
    for module, position, type_html in highlighted_local_types:
        types_by_module[module][position] = decorate_type_nodes(rewrite_links(
            type_html, rendered_set, types_by_module, canonical_names, module,
            prelude_reexports
        ))
    expression_types = build_expression_types(
        expression_types_raw, internal_q, pos_aspect, prelude_reexports
    )
    for module, nodes in expression_types.items():
        for node in nodes:
            if node.get("kind") == "definition":
                types_by_module.setdefault(module, {}).setdefault(
                    str(node["start"]), node["type"]
                )
            elif node.get("kind") in ("binding", "variable", "binder"):
                types_by_module.setdefault(node["targetModule"], {}).setdefault(
                    str(node["target"]), node["type"]
                )

    # Hovered types are code surfaces too. Rebuild their ranges solely from the
    # compiler-traced application nodes used by source blocks. Balanced
    # delimiters are not nodes. Every visible range points into $expressions,
    # so every coloured node can open another typed hover.
    for module, nodes in expression_types.items():
        semantic_nodes = [dict(node) for node in nodes]
        semantic_index = semantic_type_index(semantic_nodes)
        module_types = types_by_module.get(module, {})
        for position, type_html in list(module_types.items()):
            module_types[position] = decorate_type_nodes(
                TYPE_NODE_TAG_RE.sub("", type_html), semantic_index, module
            )
        for node in nodes:
            node["type"] = decorate_type_nodes(
                TYPE_NODE_TAG_RE.sub("", node["type"]), semantic_index, module
            )

    for module_types in types_by_module.values():
        for position, type_html in module_types.items():
            module_types[position] = resolve_type_hover_links(type_html, types_by_module)
    for nodes in expression_types.values():
        for node in nodes:
            node["type"] = resolve_type_hover_links(node["type"], types_by_module)


    return CodeContext(semantics, set(internal), rendered_set, name2pos,
                       canonical_names, types_by_module, expression_types,
                       prelude_reexports, pos_aspect)

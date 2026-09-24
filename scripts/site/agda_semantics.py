"""Optional Agda semantic enhancement, independent of a particular textbook.

Compiler tokens and ranges are authoritative. Vocabulary forwarding and page
addresses are supplied by the caller, never inferred from a project name.
"""
import html as htmllib
import re
import json
import os
from html_contract import *
from agda_help import HELP, annotate_inline_code, annotate_keywords, inline_syntax_ranges

def ref_link(href, aspect, label, extra_class=""):
    """An inline-ref anchor; hover data only when the href has a position."""
    mod, _, pos = href.rpartition(".html#")
    dt = f' data-type="{mod}#{pos}"' if mod and pos.isdigit() else ""
    cls = (extra_class + (" " + aspect if aspect else "")).strip()
    cls = f' class="{cls}"' if cls else ""
    return f'<a href="{href}"{cls}{dt}>{label}</a>'


def index_definitions(code_html, module, name2pos, pos_aspect):
    """Record (module-local name -> pos) and (pos -> aspect) from highlighted code."""
    for name, pos, aspect in DEF_RE.findall(code_html):
        name2pos.setdefault(module, {})[name] = pos
        pos_aspect.setdefault(module, {})[pos] = aspect.split()[-1] if aspect else ""
    for pos, aspect, name in RENAMED_RE.findall(code_html):
        if aspect == "Keyword" or aspect == "Module":
            continue
        name = htmllib.unescape(name)
        name2pos.setdefault(module, {}).setdefault(name, pos)
        pos_aspect.setdefault(module, {}).setdefault(
            pos, aspect.split()[-1] if aspect else ""
        )


def qualified_name_pattern(internal_q):
    """Compile one longest-first matcher instead of scanning every known name."""
    alternatives = sorted(internal_q, key=len, reverse=True)
    # A module prefix or a renamed field such as `s` must not consume part of
    # an unknown qualified name such as Helpers.isContr or Isomorphism.section.
    return re.compile(r"(?<![^\s(){};])(?:" + "|".join(map(re.escape, alternatives))
                      + r")(?![^\s(){};])") if alternatives else None


def add_prelude_qualified_names(internal_q, prelude_reexports):
    """Make Prelude's public vocabulary available to type rendering.

    Re-export anchors are not declarations, so Agda's ordinary definition index
    does not contain qualified names such as ``Base.Prelude.Type``.  They are
    nevertheless the canonical reader-facing targets used by source blocks.
    Index them alongside declarations so a name remains the same interactive
    leaf when it occurs inside a rendered hover type.
    """
    for shown, (module, position, _aspect, _label) in (
            prelude_reexports.get("by_name", {}).items()):
        internal_q.setdefault(f"{module}.{shown}", (module, position))


def wrap_expression_ranges(block, nodes, by_start, by_end, opening_for,
                           split_multiline=False):
    """Wrap compiler-backed ranges using one nesting algorithm on every surface."""
    usable = [node for node in nodes
              if node["start"] in by_start and node["end"] in by_end]
    if not usable:
        return block

    # Count containing ranges in O(n log n). The wrapper is shared by source
    # blocks and hover types, so their nesting levels and event ordering cannot
    # drift apart.
    unique_ranges = sorted(
        {(node["start"], node["end"]) for node in usable},
        key=lambda interval: (interval[0], -interval[1]),
    )
    ends = sorted({end for _, end in unique_ranges})
    end_index = {end: index + 1 for index, end in enumerate(ends)}
    tree = [0] * (len(ends) + 1)

    def add(index):
        while index < len(tree):
            tree[index] += 1
            index += index & -index

    def prefix(index):
        total = 0
        while index:
            total += tree[index]
            index -= index & -index
        return total

    depth_by_range = {}
    inserted = 0
    for start, end in unique_ranges:
        before_end = prefix(end_index[end] - 1)
        depth_by_range[(start, end)] = inserted - before_end
        add(end_index[end])
        inserted += 1

    openings, closings = {}, {}
    for node in usable:
        start, end = node["start"], node["end"]
        depth = depth_by_range[(start, end)]
        opening = opening_for(node, depth)
        openings.setdefault(by_start[start], []).append((end, opening))
        closings.setdefault(by_end[end], []).append((start, "</span>"))
    events = {}
    for position in set(openings) | set(closings):
        closing = "".join(text for _, text in sorted(
            closings.get(position, []), reverse=True
        ))
        opening = "".join(text for _, text in sorted(
            openings.get(position, []), reverse=True
        ))
        events[position] = closing + opening
    for position in sorted(events, reverse=True):
        block = block[:position] + events[position] + block[position:]
    return split_multiline_expression_nodes(block) if split_multiline else block


def semantic_type_index(nodes):
    """Index unambiguous compiler nodes by a short source prefix."""
    candidates = {}
    ambiguous = set()
    for node in nodes:
        source = " ".join(node.get("source", "").split())
        if node.get("kind") != "application" or not source:
            continue
        signature = node.get("type", "")
        previous = candidates.get(source)
        if previous and previous.get("type") != signature:
            ambiguous.add(source)
        else:
            candidates[source] = node
    for source in ambiguous:
        candidates.pop(source, None)
    prefixes = {}
    for source, node in candidates.items():
        prefix = source[:min(4, len(source))]
        prefixes.setdefault(prefix, []).append((source, node))
    for bucket in prefixes.values():
        bucket.sort(key=lambda item: len(item[0]), reverse=True)
    return prefixes


def is_universe_type_text(text):
    """Whether reader-facing source text is exactly one universe application."""
    normalized = " ".join((text or "").split())
    if re.fullmatch(r"Type(?:ω|[₀-₉]+)?", normalized):
        return True
    if not normalized.startswith("Type "):
        return False
    return not re.search(r"[→,:{}\[\]=≃×]", normalized[5:])


def is_universe_former_signature(text):
    """Whether a type is the polymorphic universe former's own signature."""
    normalized = " ".join((text or "").split())
    normalized = re.sub(r"(?:[A-Za-z][\w']*\.)+", "", normalized)
    match = re.fullmatch(
        r"\(\s*([^():{}\[\],→\s]+)\s*:\s*Level\s*\)\s*→\s*"
        r"(?:Type|Set)\s+([^()\s→,:{}\[\]=≃×]+)",
        normalized,
    )
    return bool(match and match.group(1) == match.group(2))


def decorate_type_nodes(type_html, semantic_nodes=None, module=""):
    """Add only compiler-backed source-expression ranges to a rendered type.

    Agda does not emit an AST trace for the separately rendered type sidecar.
    We may reuse an application range when its exact source text occurs in the
    type, but punctuation and balanced delimiters are not evidence of a node.
    Consequently every emitted type node has a real expression payload and can
    open another hover. Terminal universe applications keep their linked names
    but have no structural wrapper to colour or select.
    """
    pairs = {"(": ")", "[": "]", "{": "}"}

    semantic_index = (semantic_nodes if isinstance(semantic_nodes, dict)
                      else semantic_type_index(semantic_nodes or []))
    if not semantic_index:
        return type_html

    def split_delimiter_token(match):
        opening, inner = match.group(1), match.group(2)
        if "<" in inner:
            return match.group(0)
        label = htmllib.unescape(inner)
        pieces, plain = [], []

        def flush_plain():
            if plain:
                pieces.append("".join(plain))
                plain.clear()

        for character in label:
            if character in pairs or character in pairs.values():
                flush_plain()
                pieces.append(character)
            else:
                plain.append(character)
        flush_plain()
        if len(pieces) <= 1:
            return match.group(0)
        return "".join(opening + htmllib.escape(piece, quote=False) + "</a>"
                       for piece in pieces)

    # Agda sometimes colours adjacent delimiters as one token, for example
    # ``((``.  A structural boundary can fall between them.  Split only that
    # token, preserving every link attribute, just as source-expression
    # annotation splits punctuation tokens at exact AST boundaries.
    type_html = re.sub(r'(<a\b[^>]*>)(.*?)</a>', split_delimiter_token,
                       type_html, flags=re.DOTALL)
    units = []
    visible = []
    for match in re.finditer(r'<[^>]+>|&(?:#\d+|#x[0-9a-fA-F]+|\w+);|.',
                             type_html, re.DOTALL):
        token = match.group(0)
        if token.startswith("<"):
            continue
        decoded = htmllib.unescape(token)
        for character in decoded:
            visible.append(character)
            units.append((match.start(), match.end()))
    visible_text = "".join(visible)

    def token_boundary(position):
        # Exact text is insufficient inside a longer identifier: neither
        # Resizing in ΩResizing nor ℓ in ℓ₁ is the traced token.
        if position == 0 or position == len(visible_text):
            return True
        left, right = visible_text[position - 1:position + 1]
        return (left.isspace() or right.isspace()
                or left in "(){};" or right in "(){};")

    # The compiler trace already gives real application nodes and their types.
    # Reuse those nodes when their exact source occurs in a rendered type.  The
    # resulting data key resolves through the same $expressions sidecar used by
    # source Agda blocks, so a node in a hover can open another hover indefinitely.
    visible_ranges = []
    for start in range(len(visible_text)):
        if not token_boundary(start):
            continue
        for prefix_length in range(min(4, len(visible_text) - start), 0, -1):
            bucket = semantic_index.get(
                visible_text[start:start + prefix_length], []
            )
            for source, node in bucket:
                if (visible_text.startswith(source, start)
                        and token_boundary(start + len(source))):
                    if not is_universe_type_text(source):
                        visible_ranges.append((
                            start, start + len(source), f'{module}#{node["id"]}',
                        ))

    # After delimiter tokens have been split, semantic spans can expand to
    # complete anchors without swallowing a neighbouring delimiter.
    anchors = [(match.start(), match.end())
               for match in re.finditer(r"<a\b[^>]*>.*?</a>", type_html, re.DOTALL)]

    def outside_start(position):
        return next((start for start, end in anchors if start < position < end), position)

    def outside_end(position):
        return next((end for start, end in anchors if start < position < end), position)

    ranges = {(start, end): expression_key
              for start, end, expression_key in visible_ranges
              if start < end and end <= len(units)}

    # Matches borrowed from other source occurrences must still form the same
    # laminar range tree as Agda's own source trace. A crossing pair cannot be
    # an AST nesting relation, so neither is shown as a node.
    crossing = set()
    intervals = sorted(ranges)
    for index, (left_start, left_end) in enumerate(intervals):
        for right_start, right_end in intervals[index + 1:]:
            if right_start >= left_end:
                break
            if left_start < right_start < left_end < right_end:
                crossing.update(((left_start, left_end), (right_start, right_end)))
    nodes = [{"start": start, "end": end,
              "expressionKey": ranges[(start, end)]}
             for start, end in intervals if (start, end) not in crossing]
    by_start = {node["start"]: outside_start(units[node["start"]][0])
                for node in nodes}
    by_end = {node["end"]: outside_end(units[node["end"] - 1][1])
              for node in nodes}

    def type_opening(node, depth):
        return (f'<span class="type-node" '
                f'data-expression-type="{node["expressionKey"]}" '
                f'data-expr-start="{node["start"]}" '
                f'data-expr-end="{node["end"]}" '
                f'style="--expr-level:{depth % 6}">')

    return wrap_expression_ranges(
        type_html, nodes, by_start, by_end, type_opening
    )


def type_reference_attribute(module, position, types_global):
    """Source and hover surfaces advertise only an available type payload."""
    payload = types_global.get(module, {}).get(position)
    if not payload:
        return ""
    # This is a compiler type judgement, not a naming convention (i, j, α and
    # ℓ may all be levels). LevelUniv is the *sort of Level*, not a level value.
    plain = htmllib.unescape(re.sub(r'<[^>]+>', '', payload)).strip()
    level = bool(re.fullmatch(r'\(?\s*(?:(?:Agda\.Primitive|Cubical\.Core\.Primitives)\.)?Level\s*\)?', plain))
    return f' data-type="{module}#{position}"' + (' data-universe-level="true"' if level else '')


def resolve_type_hover_links(type_html, types_global):
    # Type rendering precedes completion of the global type map. Resolve its
    # provisional references only after all local and traced types are present.
    return re.sub(r' data-type="([^"#]+)#([^"#]+)"',
                  lambda match: type_reference_attribute(
                      match.group(1), match.group(2), types_global),
                  re.sub(r' data-universe-level="[^"]*"', '', type_html))


def compiler_reference_scope(content):
    """Only unambiguous definition targets actually resolved by Agda in this module."""
    candidates = {}
    for attrs, label in A_TAG_RE.findall(content):
        href, aspect = HREF_RE.search(attrs), CLASS_RE.search(attrs)
        if not href or not aspect or not _BARE_REFERENCE_ASPECTS.intersection(aspect[1].split()):
            continue
        if '.html#' not in href[1]:
            continue
        candidates.setdefault(htmllib.unescape(label), set()).add((href[1], aspect[1]))
    return {name: next(iter(values)) for name, values in candidates.items() if len(values) == 1}


def add_instantiated_type_aliases(internal_q, types_raw, scopes):
    """Agda prints instance-qualified names absent from declaration anchors.

    Resolve V.Model.Model.isZFModel through V.Model's compiler-resolved links,
    before qualifiers are abbreviated. Never guess from a global short name.
    """
    for definitions in types_raw.values():
        for term in definitions.values():
            for match in re.finditer(r"(?:[A-Za-z][\w']*\.)+[^\s(){}:;,]+", term):
                name = match[0]
                if name in internal_q:
                    continue
                parts = name.split('.')
                owner = next(('.'.join(parts[:i]) for i in range(len(parts) - 1, 0, -1)
                              if '.'.join(parts[:i]) in scopes), None)
                target = scopes.get(owner, {}).get(parts[-1])
                if target:
                    module, _, position = target[0].rpartition('.html#')
                    internal_q[name] = (module, position)


def local_signature_types(code_html, module):
    """Names and checked signatures at declaration sites without named anchors."""
    result = {}
    declaration_aspects = {
        "Function", "Record", "Datatype", "Postulate", "Primitive", "Field",
        "InductiveConstructor",
    }
    for match in LOCAL_SIGNATURE_RE.finditer(code_html):
        if match.group("module") != module:
            continue
        if not declaration_aspects.intersection(match.group("aspect").split()):
            continue
        # Sidecars are inserted into the live page, so source-position ids from
        # the highlighted declaration must not be duplicated in the popup.
        type_html = re.sub(r'\s+id="\d+"', "", match.group("type")).strip()
        result[match.group("pos")] = {
            "name": htmllib.unescape(match.group("name")),
            "type": type_html,
        }
    # Agda permits several declarations to share one signature (``A P : V``)
    # and may place the colon on the following line.  The narrow expression
    # above intentionally handles the common case; this line-oriented pass
    # supplies every declaration preceding the shared colon.
    pending = ""
    for line in code_html.splitlines():
        colon = TYPE_COLON_RE.search(line)
        if colon:
            prefix = line[:colon.start()]
            declarations = list(LOCAL_DECL_RE.finditer(prefix))
            if not declarations and pending:
                declarations = list(LOCAL_DECL_RE.finditer(pending + prefix))
            type_html = re.sub(r'\s+id="\d+"', "", line[colon.end():]).strip()
            for declaration in declarations:
                aspects = declaration.group("aspect").split()
                if (declaration.group("module") == module
                        and declaration_aspects.intersection(aspects)
                        and type_html):
                    result.setdefault(declaration.group("pos"), {
                        "name": htmllib.unescape(declaration.group("name")),
                        "type": type_html,
                    })
            pending = ""
        elif ("class=\"Symbol\">=</a>" not in line
              and LOCAL_DECL_RE.search(line)):
            pending = line
        else:
            pending = ""
    return result


def names_by_position(module, name2pos):
    """Invert Agda's definition anchors for canonical hover labels."""
    return {str(position): name
            for name, position in name2pos.get(module, {}).items()}


def split_multiline_expression_nodes(block):
    """Split visual expression spans at newlines without splitting the AST node.

    A single inline span continued across a preformatted newline paints the
    continuation indentation as part of the expression.  Close and reopen the
    active span stack around each newline instead.  Reopened expression spans
    retain their ``data-expr-id``, so the browser can treat all line fragments
    as one logical source node while leaving indentation unpainted.
    """
    output = []
    stack = []
    cursor = 0
    for match in SPAN_EVENT_RE.finditer(block):
        output.append(block[cursor:match.start()])
        token = match.group(0)
        if token.startswith("<span"):
            stack.append(token)
            output.append(token)
        elif token == "</span>":
            if stack:
                stack.pop()
            output.append(token)
        elif stack and any('class="expr-node"' in opening for opening in stack):
            output.append("</span>" * len(stack))
            output.append(token)
            output.extend(stack)
        else:
            output.append(token)
        cursor = match.end()
    output.append(block[cursor:])
    return "".join(output)


def annotate_expression_nodes(block, nodes):
    """Wrap source-range application nodes around Agda's highlighted token anchors."""
    boundaries = {node[position] for node in nodes for position in ("start", "end")}

    def split_token(match):
        start = int(match.group(1))
        inner = match.group(2)
        label = htmllib.unescape(inner)
        cuts = sorted(boundary - start for boundary in boundaries
                      if start < boundary < start + len(label))
        if not cuts:
            return match.group(0)
        opening = match.group(0)[:match.group(0).find(">") + 1]
        pieces = []
        offsets = [0, *cuts, len(label)]
        for left, right in zip(offsets, offsets[1:]):
            piece_opening = re.sub(
                r'\bid="\d+"', f'id="{start + left}"', opening, count=1
            )
            pieces.append(piece_opening + htmllib.escape(label[left:right], quote=False)
                          + "</a>")
        return "".join(pieces)

    # Agda may highlight adjacent punctuation as one anchor, for example `_))`.
    # Split such an anchor when an AST node ends between the two closing
    # parentheses, so expression spans can remain properly nested HTML.
    block = TOKEN_RE.sub(split_token, block)
    tokens = []
    for match in TOKEN_RE.finditer(block):
        start = int(match.group(1))
        label = htmllib.unescape(re.sub(r"<[^>]+>", "", match.group(2)))
        tokens.append((start, start + len(label), match.start(), match.end()))
    by_start = {start: html_start for start, _, html_start, _ in tokens}
    by_end = {end: html_end for _, end, _, html_end in tokens}

    def source_opening(node, depth):
        return (f'<span class="expr-node" data-expr-id="{node["id"]}" '
                f'data-expr-start="{node["start"]}" '
                f'data-expr-end="{node["end"]}" '
                f'style="--expr-level:{depth % 6}">')

    return wrap_expression_ranges(
        block, nodes, by_start, by_end, source_opening, split_multiline=True
    )


def annotate_unlinked_bound_types(block, module, module_types):
    """Attach occurrence types to Bound tokens for which Agda emitted no href."""
    def annotate(match):
        token = match.group(0)
        position = match.group(1)
        opening_end = token.find(">")
        opening = token[:opening_end]
        if ("href=" in opening or "data-type=" in opening
                or not re.search(r'\bclass="[^"]*\bBound\b', opening)
                or position not in module_types):
            return token
        return (opening + type_reference_attribute(module, position, {module: module_types})
                + token[opening_end:])
    return TOKEN_RE.sub(annotate, block)


def write_type_sidecar(module, langs, out_dir, types_global, name2pos,
                       expression_types):
    """Write the hover payload independently of rendering the module page."""
    sidecar_data = dict(types_global.get(module, {}))
    sidecar_data["$names"] = names_by_position(module, name2pos)
    sidecar_data["$expressions"] = {
        str(node["id"]): {key: node[key]
                          for key in ("type", "source", "start", "end", "kind")}
        for node in expression_types.get(module, [])
        if node.get("kind") not in ("definition", "binding", "variable", "binder")
    }
    for lang in langs:
        localized = {key: annotate_keywords(value, lang) if isinstance(value, str) else value
                     for key, value in sidecar_data.items()}
        localized['$expressions'] = {key: dict(value, type=annotate_keywords(value['type'], lang))
                                      for key, value in sidecar_data['$expressions'].items()}
        sidecar = json.dumps(localized, ensure_ascii=False)
        tdir = os.path.join(out_dir, lang, "types")
        os.makedirs(tdir, exist_ok=True)
        with open(os.path.join(tdir, module + ".json"), "w", encoding="utf-8") as output:
            output.write(sidecar)


def inline_ref_link(label, module, name, name2pos):
    """Render an Agda-styled label for a specified internal declaration."""
    position = name2pos.get(module, {}).get(name)
    if position is None:
        raise ValueError(f"unknown Agda reference {module}.{name}")
    href = f"{module}.html#{position}"
    return ('<span class="Agda">'
            + ref_link(href, "", htmllib.escape(label), "inline-ref") + '</span>')


def linked_inline_ref(href, aspect, label, defined):
    """Only a standalone link to a declaration may appear without a code box."""
    if defined:
        return ('<span class="Agda">'
                + ref_link(href, aspect, label, "inline-ref") + '</span>')
    return ('<span class="Agda inline-ref inline-code">'
            + ref_link(href, aspect, label) + '</span>')


def syntax_notations(content):
    """Read notation parts from compiler-classified syntax declarations."""
    declarations = []
    for line in content.splitlines():
        if not re.search(r'class="Keyword">syntax</a>', line):
            continue
        target = re.search(r'href="([^"]+)"[^>]*>([^<]+)</a>', line)
        if not target:
            continue
        rhs = re.split(r'<a\b[^>]*class="Symbol">=</a>', line)[-1]
        parts = [htmllib.unescape(text) for aspect, text in
                 re.findall(r'<a\b[^>]*class="([^"]+)"[^>]*>([^<]+)</a>', rhs)
                 if _BARE_REFERENCE_ASPECTS.intersection(aspect.split())]
        if parts:
            declarations.append((htmllib.unescape(target[1]), parts))
    return declarations


class AgdaSemantics:
    def __init__(self, *, prelude_module="", chapter_href=None):
        self.prelude_module = prelude_module
        self.chapter_href = chapter_href or (lambda module, anchor="": module + ".html" + anchor)

    def render_type(self, term, internal_q, name_pattern=None, pos_aspect=None,
                    current_module="", prelude_reexports=None):
        """Abbreviate and link an Agda type string."""
        universe_former = is_universe_former_signature(term)
        s = htmllib.escape(term.replace("\n", " "), quote=False)
        links, level_names = [], []
        def protect_level_name(match):
            token = f"{NUL}V{len(level_names)}{NUL}"
            level_names.append(match.group(0))
            return token
        # Agda disambiguates independently quantified universe levels as A.ℓ and
        # B.ℓ. They are binder names rather than module qualification and must
        # survive the qualifier abbreviation below.
        s = re.sub(r"\b[A-Z][A-Za-z0-9_']*\.ℓ[\w']*\b", protect_level_name, s)
        if name_pattern:
            def protect_link(match):
                q = match.group(0)
                mod, pos = internal_q[q]
                tok = f"{NUL}L{len(links)}{NUL}"
                last = q.split(".")[-1]
                bridge = ((prelude_reexports or {}).get("by_href", {}).get(
                    f"{mod}.html#{pos}"
                ) if current_module != self.prelude_module else None)
                target_mod, target_pos, target_name = mod, pos, last
                if bridge:
                    target_mod, target_pos, _, target_name = bridge
                aspect = (pos_aspect or {}).get(target_mod, {}).get(target_pos, "")
                class_ = f' class="{aspect}"' if aspect else ""
                primitive_stop = (aspect == "Primitive"
                                  and target_name in NON_HOVER_PRIMITIVE_SORTS)
                type_data = ("" if primitive_stop
                             else f' data-type="{target_mod}#{target_pos}"')
                if primitive_stop:
                    hover_stop = ' data-hover-stop="primitive-sort"'
                elif universe_former and target_name in {"Type", "Set"}:
                    hover_stop = ' data-hover-stop="universe-former"'
                else:
                    hover_stop = ""
                links.append(
                    f'<a href="{self.chapter_href(target_mod, "#" + target_pos)}"'
                    f'{type_data}'
                    f'{hover_stop}'
                    f' data-name="{htmllib.escape(target_name, quote=True)}"'
                    f'{class_}>{htmllib.escape(last)}</a>'
                )
                return tok
            s = name_pattern.sub(protect_link, s)
        s = re.sub(r"(?:[A-Za-z][\w']*\.)+", "", s)        # strip remaining (external) qualifiers
        # A sort without its own hover payload remains ordinary code text. Agda
        # prints universes as Set, Set₁, Setω, and so on; use the cubical name.
        s = re.sub(r"\bSet(?=$|[₀-₉ω]|[^\w'])", "Type", s)
        for i, level_name in enumerate(level_names):
            s = s.replace(f"{NUL}V{i}{NUL}", level_name)
        for i, link in enumerate(links):
            s = s.replace(f"{NUL}L{i}{NUL}", link)
        # Hover signatures use the same lexical syntax pass as prose code, while
        # preserving the compiler-derived definition links already inserted above.
        prefix, suffix = '<span class="Agda">', '</span>'
        s = annotate_inline_code(prefix + s + suffix)[len(prefix):-len(suffix)]
        return decorate_type_nodes(s)


    def prelude_reexport_index(self, content):
        """Index names explicitly re-exported by ``Base.Prelude``.

        Agda quite correctly links an imported occurrence to the library declaration.
        The textbook needs one extra hop: later chapters first lead readers to the
        explanatory import in Base.Prelude, while that import keeps Agda's original
        library link.  The index is derived from highlighted ``public using`` blocks,
        so adding a name to the foundational vocabulary automatically adds the hop.
        """
        by_href, by_name = {}, {}
        public_using = re.compile(
            r'<a id="\d+" class="Keyword">public</a>.*?'
            r'<a id="\d+" class="Keyword">using</a>(?P<body>[^\n]*)',
            re.DOTALL,
        )
        for block in PRE_RE.findall(content):
            for match in public_using.finditer(block):
                for attrs, shown in A_TAG_RE.findall(match.group("body")):
                    href = HREF_RE.search(attrs)
                    pos = ID_RE.search(attrs)
                    if not href or not pos:
                        continue
                    cls = CLASS_RE.search(attrs)
                    entry = (self.prelude_module, pos.group(1), cls.group(1) if cls else "",
                             htmllib.unescape(shown))
                    by_href.setdefault(href.group(1), entry)
                    by_name.setdefault(entry[3], entry)
        return {"by_href": by_href, "by_name": by_name}


    def rewrite_links(self, body, rendered, types_global, canonical_names=None,
                      current_module="", prelude_reexports=None):
        """Keep links to any rendered module (internal or external), tagging data-type when the
        TARGET has a type (drives hover, including on cubical identifiers). Links to a module we
        did not render lose their dead href (the <a> element stays so the </a> still matches).

        `types_global` is {module: {pos: type-html}} across ALL rendered modules."""
        def repl(m):
            idpart, mod, anchor, rest = m.group(1) or "", m.group(2), m.group(3) or "", m.group(4)
            if "://" in mod:
                return m.group(0)
            rest = re.sub(r' data-(?:type|universe-level)="[^"]*"', '', rest)
            original_href = f"{mod}.html{anchor}"
            bridge = ((prelude_reexports or {}).get("by_href", {}).get(original_href)
                      if current_module != self.prelude_module else None)
            if bridge:
                bridge_module, bridge_pos, _, bridge_name = bridge
                extra = f' data-name="{htmllib.escape(bridge_name, quote=True)}"'
                extra += type_reference_attribute(bridge_module, bridge_pos, types_global)
                return (f'<a {idpart}href="{self.chapter_href(bridge_module, "#" + bridge_pos)}"'
                        f'{rest}{extra}>')
            if mod in rendered:
                pos = anchor[1:] if anchor else ""
                extra = type_reference_attribute(mod, pos, types_global)
                canonical = (canonical_names or {}).get(mod, {}).get(pos, "")
                if canonical:
                    extra += f' data-name="{htmllib.escape(canonical, quote=True)}"'
                return f'<a {idpart}href="{self.chapter_href(mod, anchor)}"{rest}{extra}>'
            return f'<a{rest}>'                          # not rendered: drop the dead href
        return LINK_RE.sub(repl, body)


    def build_types(self, modules, name2pos, types_raw, internal_q, pos_aspect,
                    prelude_reexports=None):
        """Global {module: {pos: abbreviated/hyperlinked type-html}} for hover + sidecars."""
        g = {}
        name_pattern = qualified_name_pattern(internal_q)
        for m in modules:
            g[m] = {}
            for name, pos in name2pos.get(m, {}).items():
                if (pos_aspect.get(m, {}).get(pos) == "Primitive"
                        and name in NON_HOVER_PRIMITIVE_SORTS):
                    continue
                t = (types_raw.get(m, {}).get(name)
                     or types_raw.get(m, {}).get(name.split(".")[-1]))
                if t:
                    g[m][pos] = self.render_type(t, internal_q, name_pattern,
                                            pos_aspect, m, prelude_reexports)
        return g


    def add_prelude_reexport_types(self, types_by_module, types_raw, reexports,
                                   internal_q, pos_aspect):
        """Give Prelude's explanatory import anchors the imported names' types."""
        prelude = types_by_module.setdefault(self.prelude_module, {})
        name_pattern = qualified_name_pattern(internal_q)
        for original_href, (_, position, _, shown) in reexports["by_href"].items():
            if shown == "Type":
                # Agda's extractor reports the sort occupied by the imported
                # primitive itself (Set₁).  The reader-facing Type is the
                # level-indexed universe former used throughout this book.
                prelude[position] = self.render_type(
                    f"(ℓ : {self.prelude_module}.Level) → {self.prelude_module}.Type ℓ",
                    internal_q, name_pattern, pos_aspect, self.prelude_module, reexports,
                )
                continue
            if position in prelude:
                continue
            raw_type = types_raw.get(self.prelude_module, {}).get(shown)
            if raw_type:
                prelude[position] = self.render_type(raw_type, internal_q, name_pattern,
                                                pos_aspect, self.prelude_module, reexports)
                continue
            module, _, original_position = original_href.rpartition(".html#")
            original_type = types_by_module.get(module, {}).get(original_position)
            if original_type:
                prelude[position] = original_type


    def build_expression_types(self, raw, internal_q, pos_aspect, prelude_reexports=None):
        """Render application and local-definition types with their source ranges."""
        result = {}
        name_pattern = qualified_name_pattern(internal_q)
        type_cache = {}
        for module, nodes in raw.items():
            rendered = []
            for node in nodes:
                if not node.get("type"):
                    continue
                type_ = node["type"]
                cache_key = (module, type_)
                if cache_key not in type_cache:
                    type_cache[cache_key] = self.render_type(
                        type_, internal_q, name_pattern, pos_aspect, module,
                        prelude_reexports
                    )
                rendered.append({**node, "type": type_cache[cache_key]})
            result[module] = rendered
        return result


    def inline_reference_resolver(self, local_refs, current_module, prelude_reexports=None):
        """Use real Prelude exports and compiler links, including mixfix spellings."""
        prelude = prelude_reexports or {}
        references = dict(prelude.get('inline', {}))
        if 'inline' not in prelude:
            for name, (module, position, aspect, _) in prelude.get('by_name', {}).items():
                references.setdefault(name, (f'{module}.html#{position}', aspect))
        for name, (href, aspect) in local_refs.items():
            if name in references:
                # Prelude is the vocabulary authority, including renamed imports.
                # A real chapter-local declaration may shadow it, a borrowed token
                # (or a coincidentally named local binder) may not.
                if current_module == self.prelude_module or not href.startswith(current_module + '.html#'):
                    continue
            if not _BARE_REFERENCE_ASPECTS.intersection(aspect.split()):
                continue
            bridge = prelude.get('by_href', {}).get(href)
            references[name] = ((f'{bridge[0]}.html#{bridge[1]}', bridge[2])
                                if bridge else (href, aspect))
        aliases, openings = {}, {}
        for name in references:
            parts = [part for part in name.split('_') if part]
            if len(parts) == 1 and parts[0] == name:
                continue
            if len(parts) == 1:
                aliases.setdefault(parts[0], set()).add(references[name])
            elif parts:
                openings.setdefault(parts[0], []).append((name, parts))
        for name, parts in prelude.get('syntax', []):
            if name in references and parts:
                openings.setdefault(parts[0], []).append((name, parts))

        cached_tokens, matched = None, {}

        def match_parts(tokens):
            """Pair actual mixfix parts, respecting nesting and alternative endings."""
            stack, matches = [], {}
            for index, (_, _, token, syntax) in enumerate(tokens):
                if stack:
                    candidates, positions = stack[-1]
                    narrowed = [(name, parts) for name, parts in candidates
                                if len(parts) > len(positions) and parts[len(positions)] == token]
                    if narrowed:
                        positions = positions + [index]
                        complete = [(name, parts) for name, parts in narrowed if len(parts) == len(positions)]
                        if complete:
                            options = {references[name] for name, _ in complete}
                            if len(options) == 1:
                                for position in positions:
                                    matches[position] = next(iter(options))
                            stack.pop()
                        else:
                            stack[-1] = (narrowed, positions)
                        continue
                if token in openings:
                    stack.append((openings[token], [index]))
                elif syntax and token in ('=', ';'):
                    stack.clear()
            return matches

        def resolve(token, tokens, index):
            nonlocal cached_tokens, matched
            if tokens is not cached_tokens:
                cached_tokens, matched = tokens, match_parts(tokens)
            info = matched.get(index) or references.get(token)
            if info is None and token.startswith(self.prelude_module + '.'):
                info = references.get(token[len(self.prelude_module) + 1:])
            if info is None:
                unique = set(aliases.get(token, ()))
                if len(unique) == 1:
                    info = unique.pop()
            return ref_link(info[0], info[1], htmllib.escape(token)) if info else None
        return resolve


    def inline_ref(self, name, internal, name2pos, local_refs, current_module="",
                   prelude_reexports=None):
        """Render Agda prose, linking declarations but not temporary variables."""
        href_aspect = local_refs.get(name)
        label = htmllib.escape(name)
        if any(inline_syntax_ranges(name)) and name in HELP:
            return annotate_inline_code(f'<code class="Agda inline-ref">{label}</code>')
        if href_aspect and not _BARE_REFERENCE_ASPECTS.intersection(href_aspect[1].split()):
            return f'<code class="Agda inline-ref">{label}</code>'
        exported = (prelude_reexports or {}).get('inline', {}).get(name)
        if exported and (current_module == self.prelude_module or not href_aspect
                         or not href_aspect[0].startswith(current_module + '.html#')):
            return linked_inline_ref(*exported, label, True)
        bridge = None
        if prelude_reexports:
            if href_aspect:
                bridge = (prelude_reexports or {}).get("by_href", {}).get(href_aspect[0])
            else:
                local_name = name.rpartition(".")[2]
                bridge = (prelude_reexports or {}).get("by_name", {}).get(local_name)
        if bridge:
            mod, pos, bridge_aspect, _ = bridge
            aspect = href_aspect[1] if href_aspect else bridge_aspect
            defined = not aspect or bool(_BARE_REFERENCE_ASPECTS.intersection(aspect.split()))
            return linked_inline_ref(f"{mod}.html#{pos}", aspect, label, defined)
        target = None
        if "." in name:
            mod, _, local = name.rpartition(".")
            if mod in internal and local in name2pos.get(mod, {}):
                target = (mod, name2pos[mod][local])
        if target is None and name in name2pos.get(current_module, {}):
            target = (current_module, name2pos[current_module][name])
        if target:
            mod, pos = target
            # reuse the aspect of the module's own code tokens, and wrap in a
            # span.Agda so the .Agda .<Aspect> colour rules apply to prose refs too
            aspect = href_aspect[1] if href_aspect else ""
            defined = not aspect or bool(_BARE_REFERENCE_ASPECTS.intersection(aspect.split()))
            return linked_inline_ref(f"{mod}.html#{pos}", aspect, label, defined)
        if href_aspect:
            # a link agda already resolved in this module's own code; this is how
            # prose references library identifiers (Type, refl, ...) and modules
            aspect = href_aspect[1]
            defined = bool(_BARE_REFERENCE_ASPECTS.intersection(aspect.split()))
            return linked_inline_ref(href_aspect[0], aspect, label, defined)
        return annotate_inline_code(f'<code class="Agda inline-ref">{label}</code>',
                                    self.inline_reference_resolver(local_refs, current_module, prelude_reexports))


__all__ = ['ref_link', 'index_definitions', 'qualified_name_pattern', 'add_prelude_qualified_names', 'wrap_expression_ranges', 'semantic_type_index', 'is_universe_type_text', 'is_universe_former_signature', 'decorate_type_nodes', 'type_reference_attribute', 'resolve_type_hover_links', 'compiler_reference_scope', 'add_instantiated_type_aliases', 'local_signature_types', 'names_by_position', 'split_multiline_expression_nodes', 'annotate_expression_nodes', 'annotate_unlinked_bound_types', 'write_type_sidecar', 'inline_ref_link', 'linked_inline_ref', 'syntax_notations', 'AgdaSemantics']

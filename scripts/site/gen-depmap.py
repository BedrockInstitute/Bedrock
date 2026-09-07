#!/usr/bin/env python3
"""Generate and embed the per-language dependency map from the masters.

Everything about the page is derived, never hand-maintained (the two-catalog
doctrine's third view): nodes and edges come from the `import` lines of the
masters under src/, the reading order and the per-module one-line descriptions
come from the Everything reading catalog (its import block and its bullet
lists, per language), lanes mirror the sidebar's namespace grouping, and the
default layout follows dependency depth vertically; an alternate view groups
chapters by the learning stages in the reading catalog. The generated fragment
is embedded into each language's index and also written separately for testing.
The former depmap.html route redirects to the dependency-map tab.

Usage:
  gen-depmap.py [--src src] [--out _build/site] [--langs en,zh,ja]
"""

import glob
import html as htmllib
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from i18n_markers import weave  # noqa: E402

AGGREGATOR = "Everything"
HUBS = ["Base.Prelude", "Base.Truth"]   # the designated hub modules (STYLE-agda §2)
FENCE_RE = re.compile(r"^```agda\s*\n(.*?)^```\s*$", re.M | re.S)
IMPORT_RE = re.compile(r'^\s*(?:open\s+)?import\s+([A-Za-z][\w.]*)', re.M)
BULLET_RE = re.compile(r'^- `([A-Za-z][\w.]*)`\{\.Agda\}[:：]\s*(.*)$')

# lane colour slots, assigned by lane order of first appearance in the catalog
SLOTS = [
    ("#0F766E", "#5EEAD4"), ("#5B6B7F", "#94A3B8"), ("#0054F4", "#119DDB"),
    ("#8A1060", "#EC97B7"), ("#3B45D4", "#7C8AF0"), ("#207B1D", "#2FCB8F"),
    ("#A16207", "#EAD16E"), ("#B3323C", "#F08080"),
]

UI = {
    "en": {
        "title": "Dependency map", "back": "← Bedrock",
        "sub": ("Dependencies between {n} chapters flow from top to bottom. "
                "A → B means B imports A. Every layout shows the same prerequisite "
                "partial order. Topics with no dependency path may be interleaved. "
                "Hover to trace prerequisites; click to pin."),
        "layout": "Layout:", "compact": "Compact", "teaching": "Learning stages", "namespace": "Namespaces",
        "edgemode": "Edges:", "skeleton": "skeleton (transitive reduction)",
        "alledges": "all direct imports", "lmk": "include Landmarks' references",
        "hint": "Select a chapter to trace its prerequisites",
        "hubnote": ("The widely used Base.Prelude and Base.Truth imports are omitted "
                    "from the drawing but retained in chapter details."),
        "reading": "example route position", "imports": "direct imports", "consumers": "direct consumers",
        "legend": "Color key", "fit": "Fit whole graph", "readable": "Readable size",
        "scrollhint": "Scroll the graph in both directions, or fit the whole graph for an overview.",
        "none": "None",
        "noscript": "The dependency map requires JavaScript. You can still use the",
        "catalog": "chapter catalog",
        "footer": ("The skeleton preserves reachability, not every direct use of a definition. "
                   "An omitted edge is not permission to delete an import. Learning stages do not "
                   "make every chapter a serial step: finish the listed prerequisites before a "
                   "converging chapter. Everything supplies one example route. Landmarks is the "
                   "opening preview and appears at the bottom here as the endpoint."),
    },
    "zh": {
        "title": "依赖地图", "back": "← Bedrock",
        "sub": ("{n} 个章节的依赖从上向下展开。A → B 表示 B 导入 A。各布局展示同一份先修偏序；没有依赖路径的主题可以穿插学习。悬停追踪先修关系，点击固定。"),
        "layout": "布局：", "compact": "紧凑总览", "teaching": "学习阶段", "namespace": "命名空间",
        "edgemode": "边：", "skeleton": "骨架 (传递约简)", "alledges": "全部直接边",
        "lmk": "包含 Landmarks 的引用边", "hint": "选择章节以追踪先修关系",
        "hubnote": "图中省略广泛使用的 Base.Prelude 和 Base.Truth 导入边，章节详情仍保留它们。",
        "reading": "示例路线序号", "imports": "直接导入", "consumers": "直接消费者",
        "legend": "颜色图例", "fit": "适合全图", "readable": "可读字号",
        "scrollhint": "可向两个方向滚动图；也可切换为全图概览。", "none": "无",
        "noscript": "依赖图需要 JavaScript。仍可改读同页的", "catalog": "章节目录",
        "footer": ("骨架保留可达关系，并不展示每一次直接使用；省略一条边不表示可以删除对应导入。学习阶段不要求把所有章节依次串行；进入汇合章节前，应完成图中所列先修。Everything 给出一条示例路线。Landmarks 是开篇预览，在此作为终点置于底部。"),
    },
    "ja": {
        "title": "依存マップ", "back": "← Bedrock",
        "sub": "{n} 章の依存関係を上から下へ表示。A → B は B が A を import することを表します。どの配置も同じ前提関係の半順序を示し、依存経路のない主題は交互に学べます。",
        "layout": "配置：", "compact": "コンパクト", "teaching": "学習段階", "namespace": "名前空間",
        "edgemode": "辺：", "skeleton": "骨格 (推移簡約)", "alledges": "直接 import 全体",
        "lmk": "Landmarks の参照を含める", "hint": "章を選択して前提を確認",
        "hubnote": "広く使われる Base.Prelude と Base.Truth の辺は図から省略し、章の詳細には残します。",
        "reading": "例示ルート順", "imports": "直接 import", "consumers": "直接の利用者",
        "legend": "色の凡例", "fit": "全体を表示", "readable": "読みやすい大きさ",
        "scrollhint": "図は縦横にスクロールできます。全体表示に切り替えると概観できます。", "none": "なし",
        "noscript": "依存マップには JavaScript が必要です。同じページの", "catalog": "章の目次",
        "footer": "骨格は到達関係を保ちます。省略された辺の import が不要とは限りません。学習段階は全章を直列に並べるものではありません。合流する章へ進む前に、表示された前提を終えてください。Everything は一例となるルートを示します。冒頭の予告 Landmarks は、この図では終点として下部に置きます。",
    },
}


def imports(text):
    return [name for block in FENCE_RE.findall(text) for name in IMPORT_RE.findall(block)]


def teaching_stages(text, lang):
    stages, membership, current, inside = [], {}, None, False
    for line in weave(text, lang).splitlines():
        if line == "```agda":
            inside = True
        elif inside and line == "```":
            inside = False
        elif not inside and line.startswith("## "):
            current = str(len(stages))
            stages.append({"key": current, "label": line[3:]})
        elif inside:
            found = IMPORT_RE.match(line)
            if found and current is not None:
                membership[found.group(1)] = current
    return stages, membership


def reduced_edges(nodes, edges):
    adjacency = {n: set() for n in nodes}
    for a, b in edges:
        adjacency[a].add(b)
    def alternate(a, b):
        pending, seen = list(adjacency[a] - {b}), set()
        while pending:
            n = pending.pop()
            if n == b:
                return True
            if n not in seen:
                seen.add(n)
                pending.extend(adjacency[n])
        return False
    return [(a, b) for a, b in edges if not alternate(a, b)]


def packed_layout(nodes, edges, ranks, order, top=34):
    """Place each depth on one row; use adjacent ranks to reduce crossings."""
    levels = {}
    for n in sorted(nodes, key=lambda n: order[n]):
        levels.setdefault(ranks[n], []).append(n)
    parents = {n: [] for n in nodes}
    children = {n: [] for n in nodes}
    for a, b in edges:
        if a in parents and b in parents:
            parents[b].append(a)
            children[a].append(b)
    for sweep in range(8):
        adjacent = parents if sweep % 2 == 0 else children
        positions = {n: (i + .5) / len(row) for row in levels.values() for i, n in enumerate(row)}
        for rank in sorted(levels, reverse=bool(sweep % 2)):
            def score(n):
                xs = [positions[a] for a in adjacent[n]]
                return sum(xs) / len(xs) if xs else positions[n]
            levels[rank].sort(key=lambda n: (score(n), order[n]))
            positions.update({n: (i + .5) / len(levels[rank]) for i, n in enumerate(levels[rank])})
    width = max((len(row) for row in levels.values()), default=1) * 142 + 28
    positions = {}
    for rank, row in levels.items():
        offset = (width - len(row) * 142) / 2
        for i, n in enumerate(row):
            positions[n] = {"x": offset + i * 142 + 7, "y": top + rank * 66}
    return {"width": width, "height": top + (max(ranks.values(), default=0) + 1) * 66,
            "positions": positions, "bands": []}


def layouts(nodes, edges, order, depth, row, lanes, stages, membership):
    skeleton = reduced_edges(nodes, [(a, b) for a, b in edges if a not in HUBS])
    compact = packed_layout(nodes, skeleton, depth, order)
    compact["bands"] = []
    x, positions, bands = 4, {}, []
    for lane in lanes:
        group = [n for n in nodes if lane_of(n) == lane]
        width = max(row[n] + 1 for n in group) * 142 + 14
        bands.append({"x": x, "y": 0, "width": width, "height": compact["height"], "label": lane})
        for n in group:
            positions[n] = {"x": x + 14 + row[n] * 142, "y": 34 + depth[n] * 66}
        x += width
    namespace = {"width": x + 4, "height": compact["height"], "positions": positions, "bands": bands}
    # Landmarks is read as a preview but depends on the final results.
    stage_order = [s for s in stages if s["key"] != membership.get("Landmarks")]
    stage_order += [s for s in stages if s["key"] == membership.get("Landmarks")]
    teaching = {"width": 0, "height": 0, "positions": {}, "bands": []}
    for stage in stage_order:
        group = [n for n in nodes if membership[n] == stage["key"]]
        ranks = {}
        for n in sorted(group, key=lambda n: depth[n]):
            ranks[n] = max((ranks[a] + 1 for a, b in edges if b == n and a in ranks), default=0)
        block = packed_layout(group, skeleton, ranks, order)
        y = teaching["height"]
        teaching["bands"].append({"x": 0, "y": y, "width": block["width"], "height": block["height"], "label": stage["label"]})
        teaching["positions"].update({n: {"x": p["x"], "y": p["y"] + y} for n, p in block["positions"].items()})
        teaching["width"] = max(teaching["width"], block["width"])
        teaching["height"] += block["height"]
    for band in teaching["bands"]:
        offset = (teaching["width"] - band["width"]) / 2
        for point in teaching["positions"].values():
            if band["y"] <= point["y"] < band["y"] + band["height"]:
                point["x"] += offset
        band["width"] = teaching["width"]
    return {"compact": compact, "teaching": teaching, "namespace": namespace}


def masters(src):
    out = {}
    for p in sorted(glob.glob(os.path.join(src, "**", "*.lagda.md"), recursive=True)):
        mod = os.path.relpath(p, src)[:-len(".lagda.md")].replace(os.sep, ".")
        out[mod] = open(p, encoding="utf-8").read()
    return out


def lane_of(mod):
    parts = mod.split(".")
    if len(parts) >= 3:                      # sub-namespace clusters get their own lane
        return ".".join(parts[:2])
    return parts[0]


def descriptions(everything_text, lang, fallback):
    """Per-module one-liners from the reading catalog's bullets (wrapped lines joined)."""
    text = weave(everything_text, lang)
    descs, cur = {}, None
    for line in text.split("\n"):
        m = BULLET_RE.match(line)
        if m:
            cur = m.group(1)
            descs[cur] = m.group(2)
        elif cur and re.match(r'^  \S', line):
            descs[cur] += ("" if descs[cur].endswith("：") else " ") + line.strip()
        else:
            cur = None
    clean = {}
    for k, v in descs.items():
        v = re.sub(r'`([^`]*)`\{\.Agda\}', r'\1', v)
        v = v.replace("**", "").replace("`", "")
        clean[k] = v
    if fallback:
        for k, v in fallback.items():
            clean.setdefault(k, v)
    return clean


def build_graph(src):
    mods = masters(src)
    everything = mods.pop(AGGREGATOR)
    internal = set(mods)
    edges = []
    for mod, text in sorted(mods.items()):
        for imp in sorted(set(imports(text))):
            if imp in internal and imp != mod:
                edges.append((imp, mod))
    order = [m for m in imports(everything) if m in internal]
    ordnum = {m: i + 1 for i, m in enumerate(order)}

    # dependency depth: longest path over the full edge set
    dep = {m: [] for m in internal}
    for a, b in edges:
        dep[b].append(a)
    col = {}

    def depth(m):
        if m not in col:
            col[m] = 0                       # cycle guard; Agda imports are acyclic
            col[m] = max((depth(a) + 1 for a in dep[m]), default=0)
        return col[m]
    for m in internal:
        depth(m)

    # lanes by first appearance in the reading order, rows packed per column
    lanes = []
    for m in order:
        ln = lane_of(m)
        if ln not in lanes:
            lanes.append(ln)
    for m in sorted(internal):               # safety: modules outside the catalog
        if lane_of(m) not in lanes:
            lanes.append(lane_of(m))
    row, used = {}, {}
    for m in sorted(internal, key=lambda m: (ordnum.get(m, 999), m)):
        key = (lane_of(m), col[m])
        row[m] = used.get(key, 0)
        used[key] = row[m] + 1
    return everything, internal, edges, ordnum, col, row, lanes


TEMPLATE = open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                             "depmap-template.html"), encoding="utf-8").read() \
    if os.path.exists(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                   "depmap-template.html")) else None

MARKER = "<!-- DEPENDENCY_MAP -->"
GENERATED_START = "<!-- DEPENDENCY_MAP GENERATED START -->"
GENERATED_END = "<!-- DEPENDENCY_MAP GENERATED END -->"


def render_fragment(data, lang, ui):
    """Fill the fragment template without introducing a second panel id."""
    fragment = TEMPLATE
    for key in ("layout", "compact", "teaching", "namespace", "edgemode",
                "skeleton", "alledges", "lmk", "hint", "hubnote", "footer",
                "legend", "fit", "scrollhint", "noscript", "catalog"):
        fragment = fragment.replace("__" + key.upper() + "__", htmllib.escape(ui[key]))
    fragment = fragment.replace("__TITLE__", htmllib.escape(ui["title"]))
    fragment = fragment.replace("__SUB__", htmllib.escape(ui["sub"].format(n=len(data["nodes"]))))
    strings = {key: ui[key] for key in
               ("reading", "imports", "consumers", "hint", "hubnote", "fit", "readable", "none")}
    fragment = fragment.replace("__DATA__", json.dumps(data, ensure_ascii=False).replace("</", "<\\/"))
    fragment = fragment.replace("__STR__", json.dumps(strings, ensure_ascii=False).replace("</", "<\\/"))
    return fragment


def embed_fragment(index, fragment):
    """Replace either the source marker or a fragment generated on an earlier run."""
    managed = f"{GENERATED_START}\n{fragment}\n{MARKER}\n{GENERATED_END}"
    generated = re.compile(re.escape(GENERATED_START) + r".*?" + re.escape(GENERATED_END), re.S)
    if generated.search(index):
        return generated.sub(lambda _: managed, index, count=1)
    if MARKER in index:
        return index.replace(MARKER, managed, 1)
    raise ValueError(f"index has neither {MARKER} nor a generated dependency-map block")


def standalone_fragment(fragment, lang, title):
    """Wrap the same fragment so a generator test can open it without an index."""
    return ("<!DOCTYPE html>\n"
            f'<html lang="{lang}"><head><meta charset="utf-8"><meta name="viewport" '
            'content="width=device-width, initial-scale=1">'
            f'<title>{htmllib.escape(title)} · Bedrock</title>'
            '<link rel="stylesheet" href="../static/bedrock.css"></head><body>'
            f'<main><section id="dependency-map">{fragment}</section></main></body></html>')


def compatibility_page(lang, ui):
    target = "index.html#dependency-map"
    return ("<!DOCTYPE html>\n"
            f'<html lang="{lang}"><head><meta charset="utf-8">'
            f'<meta http-equiv="refresh" content="0; url={target}">'
            f'<title>{htmllib.escape(ui["title"])} · Bedrock</title>'
            f'<link rel="canonical" href="{target}"></head><body>'
            f'<p><a href="{target}">{htmllib.escape(ui["title"])}</a></p>'
            f'<script>location.replace("{target}");</script></body></html>')


def main(argv):
    src, out, langs = "src", "_build/site", ["en", "zh", "ja"]
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--src": i += 1; src = argv[i]
        elif a == "--out": i += 1; out = argv[i]
        elif a == "--langs": i += 1; langs = argv[i].split(",")
        else: sys.stderr.write(f"unknown option: {a}\n"); return 2
        i += 1

    if TEMPLATE is None:
        sys.stderr.write("depmap: missing depmap-template.html\n")
        return 2

    everything, internal, edges, ordnum, col, row, lanes = build_graph(src)
    slot = {ln: SLOTS[i % len(SLOTS)] for i, ln in enumerate(lanes)}

    desc_en = descriptions(everything, "en", {})
    embedded = 0
    errors = 0
    for lang in langs:
        ui = UI.get(lang, UI["en"])
        descs = descriptions(everything, lang, desc_en)
        nodes = [{
            "id": m, "lane": lane_of(m), "col": col[m], "row": row[m],
            "ord": ordnum.get(m, 0), "desc": descs.get(m, ""),
        } for m in sorted(internal, key=lambda m: (ordnum.get(m, 999), m))]
        stages, membership = teaching_stages(everything, lang)
        stage_labels = {stage["key"]: stage["label"] for stage in stages}
        for node in nodes:
            node["stage"] = stage_labels[membership[node["id"]]]
        data = {
            "layouts": layouts(internal, edges, ordnum, col, row, lanes, stages, membership),
            "nodes": nodes,
            "edges": [list(e) for e in edges],
            "lanes": [{"key": ln, "light": slot[ln][0], "dark": slot[ln][1]}
                      for ln in lanes],
            "hubs": HUBS,
            "landmark": "Landmarks",
        }
        fragment = render_fragment(data, lang, ui)
        lang_dir = os.path.join(out, lang)
        os.makedirs(lang_dir, exist_ok=True)
        open(os.path.join(lang_dir, "depmap.html"), "w", encoding="utf-8").write(
            compatibility_page(lang, ui))
        index_path = os.path.join(lang_dir, "index.html")
        if not os.path.exists(index_path):
            open(os.path.join(lang_dir, "depmap-fragment.html"), "w", encoding="utf-8").write(
                standalone_fragment(fragment, lang, ui["title"]))
            print(f"depmap: {index_path} missing; wrote standalone depmap-fragment.html", file=sys.stderr)
            continue
        index = open(index_path, encoding="utf-8").read()
        try:
            index = embed_fragment(index, fragment)
        except ValueError as error:
            print(f"depmap: {index_path}: {error}", file=sys.stderr)
            errors += 1
            continue
        open(index_path, "w", encoding="utf-8").write(index)
        embedded += 1
    print(f"depmap: {len(internal)} node(s), {len(edges)} edge(s) "
          f"-> {embedded} index fragment(s), {len(langs)} compatibility redirect(s)", file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

#!/usr/bin/env python3
"""Generate the per-language dependency-map page from the masters.

Everything about the page is derived, never hand-maintained (the two-catalog
doctrine's third view): nodes and edges come from the `import` lines of the
masters under src/, the reading order and the per-module one-line descriptions
come from the Everything reading catalog (its import block and its bullet
lists, per language), lanes mirror the sidebar's namespace grouping, and the
horizontal position is the longest-path dependency depth. Output is a fully
self-contained HTML page (inline CSS/JS, no external assets) written to
<out>/<lang>/depmap.html; render-site.py links to it from the sidebar.

Usage:
  gen-depmap.py [--src src] [--out _build/site] [--langs en,zh]
"""

import glob
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from i18n_markers import weave  # noqa: E402

AGGREGATOR = "Everything"
HUBS = ["Base.Prelude", "Base.Truth"]   # the designated hub modules (STYLE-agda §2)
IMPORT_RE = re.compile(r'^(?:open )?import ([A-Za-z][\w.]*)', re.M)
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
        "sub": ("Direct imports between the {n} literate chapters. Horizontal axis is "
                "dependency depth (no dependencies at the left, the root theorem at the "
                "right); lanes are the sidebar's namespace tree. <b>A → B means B imports "
                "A</b>. Hover for a chapter's dependency cones; click to pin."),
        "edgemode": "Edges:", "skeleton": "skeleton (transitive reduction)",
        "alledges": "all direct imports",
        "lmk": "include Landmarks' references",
        "legfront": "dashed: temporary chapter (the frontier; deleted once its debts are paid)",
        "hint": "— hover or click any chapter —",
        "hubnote": ("The hubs <span class=mono>Base.Prelude</span> and <span class=mono>"
                    "Base.Truth</span> are imported by every chapter; those edges are "
                    "omitted (the detail card still lists them)."),
        "frontnote": ("The dashed <span class=mono>L.Frontier</span> is the debt registry: "
                      "a temporary chapter, deleted once its fields are proven."),
        "reading": "reading position", "imports": "direct imports", "consumers": "direct consumers",
        "footer": ("Reading order (corner numbers) and dependency order differ on purpose: "
                   "this page is the third derived view of the two-catalog doctrine "
                   "(PLAN §5). Regenerated from the import lines of "
                   "<span class=mono>src/**.lagda.md</span> on every site build."),
    },
    "zh": {
        "title": "依赖地图", "back": "← Bedrock",
        "sub": ("{n} 个文学化章节的直接导入关系。横轴为依赖深度 (左端无依赖，右端是根定理)；"
                "泳道即侧边栏的命名空间结构树。<b>A → B 表示 B 导入 A</b>。悬停看依赖锥，点击钉住。"),
        "edgemode": "边：", "skeleton": "骨架 (传递约简)",
        "alledges": "全部直接边",
        "lmk": "包含 Landmarks 的引用边",
        "legfront": "虚线：临时章节 (前沿登记簿，债务偿清即删)",
        "hint": "— 悬停或点击任一章节 —",
        "hubnote": ("中枢 <span class=mono>Base.Prelude</span> 与 <span class=mono>Base.Truth"
                    "</span> 被每一章导入，图中省略这些边 (详情卡仍列出)。"),
        "frontnote": ("虚线边框的 <span class=mono>L.Frontier</span> 是债务登记簿：临时章节，"
                      "字段证毕即删。"),
        "reading": "阅读序号", "imports": "直接导入", "consumers": "直接消费者",
        "footer": ("阅读顺序 (角标数字) 与依赖顺序刻意不同：本页是两目录法条 (PLAN §5) 的第三个"
                   "派生视图。每次站点构建都从 <span class=mono>src/**.lagda.md</span> 的 "
                   "import 行重新生成。"),
    },
    "ja": {
        "title": "依存マップ", "back": "← Bedrock",
        "sub": ("{n} 章の直接 import 関係。横軸は依存の深さ、レーンはサイドバーの名前空間ツリー。"
                "<b>A → B は B が A を import する</b>ことを表す。ホバーで依存錐、クリックで固定。"),
        "edgemode": "辺：", "skeleton": "骨格 (推移簡約)",
        "alledges": "すべての直接 import",
        "lmk": "Landmarks の参照を含める",
        "legfront": "破線：一時的な章 (フロンティア、完済で削除)",
        "hint": "— 章にホバーまたはクリック —",
        "hubnote": ("ハブ <span class=mono>Base.Prelude</span> と <span class=mono>Base.Truth"
                    "</span> は全章から import されるため、辺は省略 (詳細カードには表示)。"),
        "frontnote": ("破線の <span class=mono>L.Frontier</span> は負債台帳：一時的な章で、"
                      "証明され次第削除される。"),
        "reading": "読書順", "imports": "直接 import", "consumers": "直接の消費者",
        "footer": ("読書順 (隅の番号) と依存順は意図的に異なる。本頁はサイトビルドごとに "
                   "<span class=mono>src/**.lagda.md</span> から再生成される。"),
    },
}


def masters(src):
    out = {}
    for p in sorted(glob.glob(os.path.join(src, "**", "*.lagda.md"), recursive=True)):
        mod = os.path.relpath(p, src)[:-len(".lagda.md")].replace(os.sep, ".")
        out[mod] = open(p, encoding="utf-8").read()
    return out


def lane_of(mod):
    parts = mod.split(".")
    if mod.startswith("FOL.Reification"):
        return "FOL.Reification"
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
        for imp in sorted(set(IMPORT_RE.findall(text))):
            if imp in internal and imp != mod:
                edges.append((imp, mod))
    order = [m for m in IMPORT_RE.findall(everything) if m in internal]
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


def main(argv):
    src, out, langs = "src", "_build/site", ["en", "zh"]
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--src": i += 1; src = argv[i]
        elif a == "--out": i += 1; out = argv[i]
        elif a == "--langs": i += 1; langs = argv[i].split(",")
        else: sys.stderr.write(f"unknown option: {a}\n"); return 2
        i += 1

    everything, internal, edges, ordnum, col, row, lanes = build_graph(src)
    slot = {ln: SLOTS[i % len(SLOTS)] for i, ln in enumerate(lanes)}

    desc_en = descriptions(everything, "en", {})
    for lang in langs:
        ui = UI.get(lang, UI["en"])
        descs = descriptions(everything, lang, desc_en)
        nodes = [{
            "id": m, "lane": lane_of(m), "col": col[m], "row": row[m],
            "ord": ordnum.get(m, 0), "desc": descs.get(m, ""),
        } for m in sorted(internal, key=lambda m: (ordnum.get(m, 999), m))]
        data = {
            "nodes": nodes,
            "edges": [list(e) for e in edges],
            "lanes": [{"key": ln, "light": slot[ln][0], "dark": slot[ln][1]}
                      for ln in lanes],
            "hubs": HUBS,
            "frontier": "L.Frontier",
            "landmark": "Landmarks",
        }
        page = TEMPLATE
        page = page.replace("__LANG__", lang)
        page = page.replace("__TITLE__", ui["title"])
        page = page.replace("__BACK__", ui["back"])
        page = page.replace("__SUB__", ui["sub"].format(n=len(internal)))
        page = page.replace("__EDGEMODE__", ui["edgemode"])
        page = page.replace("__SKELETON__", ui["skeleton"])
        page = page.replace("__ALLEDGES__", ui["alledges"])
        page = page.replace("__LMK__", ui["lmk"])
        page = page.replace("__LEGFRONT__", ui["legfront"])
        page = page.replace("__HINT__", ui["hint"])
        page = page.replace("__HUBNOTE__", ui["hubnote"])
        page = page.replace("__FRONTNOTE__", ui["frontnote"])
        page = page.replace("__READING__", ui["reading"])
        page = page.replace("__IMPORTS__", ui["imports"])
        page = page.replace("__CONSUMERS__", ui["consumers"])
        page = page.replace("__FOOTER__", ui["footer"])
        page = page.replace("__DATA__", json.dumps(data, ensure_ascii=False))
        dest = os.path.join(out, lang, "depmap.html")
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        open(dest, "w", encoding="utf-8").write(page)
    print(f"depmap: {len(internal)} node(s), {len(edges)} edge(s) "
          f"-> {out}/<lang>/depmap.html x{len(langs)}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

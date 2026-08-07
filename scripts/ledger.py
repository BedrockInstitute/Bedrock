#!/usr/bin/env python3
"""Size ledger for Bedrock: MEASURES standing from the tree, then sums the endpoint.

The canonical ledger data is dev/ledger.toml (read here via tomllib); the prose that
explains it is this file's own header comment. This script exists because of a measured failure: the goal
register carried a standing figure of 12,633 for nine consecutive dispatches, and
[L3.32-T55] found it had never been a measurement, only a projection fixed at [T25] and
then re-quoted by every report that followed. The cure is not a tidier document. The cure
is that standing is COMPUTED here and written nowhere.

What it measures: non-blank lines inside ```agda fences, over git-tracked *.lagda.md under
src/. The archive (archive/) is outside every gate (D20) and is never counted. Probe files
(src/Probe*.agda) are untracked by standing rule (D-1) and so never appear.

Standing = tracked total MINUS the D18-booked retirement set declared in dev/ledger.toml.
Endpoint = standing PLUS the remaining rows, in both calibers (PLAN section 6.2): naive is
the component sum, calibrated applies each row's own class (about x1.3 for a row anchored
by a probe or a delivered comparable, x3 for a row only a survey could reach).

The 25k reference line is a best-effort target, NOT a decision procedure (D26). This script
prints the overage as a plain number and draws no conclusion from it. Neither should you.

The owner reads the same figures on the dashboard (`make dashboard`), which sees the
numbers without running anything. That block is written by --write and verified by --check, so
it fails the commit gate the moment it goes stale. That is the whole trick: the numbers are
visible AND they cannot rot, because nobody is trusted to retype them.

Usage:
  ledger.py              print the full ledger
  ledger.py --check      validate the declaration against the tree
                         (exit 1 on a defect); this is the mode `make check` runs
  ledger.py --write      a no-op alias for --check, kept so old invocations work
                         move, which D27 says is at every return that could move them
  ledger.py --brief      one line: standing, endpoint band, overage
  ledger.py --trophy-split
                         one line: the four parts of the per-trophy caliber,
                         and the AC total. It measures the SURVIVING tree and
                         sums to standing, like every other figure here
  ledger.py --trophy-matrix
                         one line: the nine cells, three calibers by three
                         trophies. The AC-and-GCH column must equal --brief,
                         and the gate fails if it does not
Exit status: 0 clean, 1 defect found, 2 usage error.
"""

from __future__ import annotations

import re
import subprocess
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEDGER = ROOT / "dev" / "ledger.toml"
FENCE = re.compile(r"```agda\n(.*?)```", re.S)


def tracked_masters() -> list[str]:
    """Git-tracked .lagda.md under src/. Untracked probes never appear here (D-1)."""
    out = subprocess.run(
        ["git", "ls-files", "src/"], cwd=ROOT, capture_output=True, text=True, check=True
    ).stdout.split()
    return sorted(f for f in out if f.endswith(".lagda.md"))


def head_text(path: str) -> str:
    """The file's text at HEAD, or empty when the file is not in HEAD yet."""
    out = subprocess.run(["git", "show", f"HEAD:{path}"], cwd=ROOT,
                         capture_output=True, text=True)
    return out.stdout if out.returncode == 0 else ""


def count(path: str, at_head: bool = True) -> int:
    """Non-blank lines inside ```agda fences: the one pinned caliber.

    Read from HEAD, not the working tree. A ledger records the REPOSITORY, and reading the
    working tree meant an agent's half-written chapter was counted as standing: it happened
    twice on 2026-08-05 and once got committed. Pass at_head=False for a live view."""
    if at_head:
        text = head_text(path)
        if not text:
            return 0  # staged-but-never-committed: not yet part of the repository
    else:
        text = (ROOT / path).read_text(encoding="utf-8")
    return sum(
        1
        for block in FENCE.findall(text)
        for line in block.split("\n")
        if line.strip()
    )


def retiring(files: list[str], data: dict) -> tuple[dict[str, list[str]], list[str]]:
    """Partition the tracked files by the declared retirement set. Returns (buckets, defects)."""
    buckets: dict[str, list[str]] = {}
    defects: list[str] = []
    claimed: set[str] = set()
    for entry in data.get("retire", []):
        label = entry.get("prefix") or entry.get("path")
        excepted = set(entry.get("except", []))
        if "prefix" in entry:
            hit = [f for f in files if f.startswith(entry["prefix"]) and f not in excepted]
            if not hit:
                defects.append(f"retirement prefix matches nothing in the tree: {entry['prefix']}")
            for missing in excepted - set(files):
                defects.append(f"retirement exception names a file not in the tree: {missing}")
        else:
            hit = [f for f in files if f == entry["path"]]
            if not hit:
                defects.append(f"retirement path is not in the tree: {entry['path']}")
        for f in hit:
            if f in claimed:
                defects.append(f"file claimed by two retirement entries: {f}")
            claimed.add(f)
        buckets[label] = hit
    return buckets, defects


def validate_rows(data: dict) -> list[str]:
    """Every remaining row needs both bands and a provenance. Unpriced is stated, never zero."""
    defects: list[str] = []
    seen: set[str] = set()
    for row in data.get("remaining", []):
        rid = row.get("id", "<no id>")
        if rid in seen:
            defects.append(f"duplicate remaining row id: {rid}")
        seen.add(rid)
        for field in ("naive_low", "naive_high", "calibrated_low", "calibrated_high"):
            if field not in row:
                defects.append(f"remaining row {rid} is missing {field}")
        if not row.get("provenance"):
            defects.append(f"remaining row {rid} has no provenance (a row without one is unpriced, not zero)")
        if row.get("trophy") not in {"AC", "GCH", "BOTH"}:
            defects.append(f"remaining row {rid} has no trophy (a row without one is unattributed, not shared)")
        if row.get("naive_low", 0) > row.get("naive_high", 0):
            defects.append(f"remaining row {rid} has an inverted naive band")
        if row.get("calibrated_low", 0) < row.get("naive_low", 0):
            defects.append(f"remaining row {rid} is calibrated below naive, which the two-caliber discipline forbids")
    VALID = {"delivered", "ready", "in-flight", "blocked", "at-risk", "frozen", "exempt"}
    seen_owed: set[str] = set()
    for row in data.get("owed", []):
        rid = row.get("id", "<no id>")
        if rid in seen_owed:
            defects.append(f"duplicate owed id: {rid}")
        seen_owed.add(rid)
        if row.get("trophy") not in {"AC", "GCH", "BOTH"}:
            defects.append(f"owed {rid}: trophy must be AC, GCH or BOTH")
        if row.get("status") not in VALID:
            defects.append(f"owed {rid}: status must be one of {', '.join(sorted(VALID))}")
        if not row.get("evidence"):
            defects.append(f"owed {rid}: no evidence. An item with no evidence is a guess "
                           f"and must say so in its title")
        if row.get("status") == "blocked" and not row.get("blocked_by"):
            defects.append(f"owed {rid}: status is blocked but blocked_by is empty; say what "
                           f"it waits on or the item cannot be scheduled")
        # An exemption is NAMED or it is not an exemption. A freeze that can be
        # escaped by editing one word is not a freeze, so a row that leaves
        # `frozen` this way must carry the authority that released it and the
        # reason, and both are checked here rather than trusted to prose.
        if row.get("status") == "exempt":
            if not row.get("exempt_by"):
                defects.append(f"owed {rid}: status is exempt but exempt_by is empty. An "
                               f"exemption names the ruling that granted it, or it is just "
                               f"an unfrozen row")
            if not row.get("exempt_why"):
                defects.append(f"owed {rid}: status is exempt but exempt_why is empty. The "
                               f"reason is the scope: without it the next reader cannot tell "
                               f"what the exemption does NOT cover")
    for row in data.get("owed", []):
        for dep in [d.strip() for d in row.get("blocked_by", "").split(",") if d.strip()]:
            if dep not in seen_owed and " " not in dep:
                defects.append(f"owed {row.get('id')}: blocked_by names {dep!r}, which is not "
                               f"an owed id")
    for row in data.get("excluded", []):
        if not row.get("why"):
            defects.append(f"excluded row {row.get('id', '<no id>')} does not say why it is excluded")
    return defects



def retired_str(buckets, sizes) -> str:
    return f"{sum(sizes[f] for hit in buckets.values() for f in hit):,}"


IMPORT_RE = re.compile(r"^\s*(?:open )?import ([A-Za-z0-9_.]+)", re.M)


def import_graph(files: list[str]) -> dict[str, set[str]]:
    """One master's imported masters, from the import lines at HEAD.

    A name that has no tracked master (an archived module, a library module)
    has no edge, because only tracked masters are counted and classified."""
    names = {f.removesuffix(".lagda.md").removeprefix("src/").replace("/", "."): f
             for f in files}
    graph: dict[str, set[str]] = {}
    for f in files:
        text = head_text(f)
        graph[f] = {names[n] for n in IMPORT_RE.findall(text) if n in names}
    return graph


def closure(graph: dict[str, set[str]], roots: list[str]) -> set[str]:
    """The transitive import closure of the roots."""
    seen: set[str] = set()
    stack = list(roots)
    while stack:
        f = stack.pop()
        if f in seen:
            continue
        seen.add(f)
        stack.extend(graph.get(f, ()))
    return seen


def trophy_roots(data: dict, files: list[str]) -> tuple[dict[str, list[str]], list[str]]:
    """The declared AC and GCH roots from [[trophy_split]], with defects.

    Every root must exist in the tree. A stale root fails the gate exactly
    like a stale [[retire]] row does."""
    roots: dict[str, list[str]] = {"ac": [], "gch": []}
    defects: list[str] = []
    entries = data.get("trophy_split")
    if entries is None:
        defects.append("trophy_split: no [[trophy_split]] declaration in dev/ledger.toml")
        return roots, defects
    for entry in entries:
        if entry.get("rule"):
            if entry.get("ambiguous") not in {None, "shared"}:
                defects.append("trophy_split: ambiguous must be 'shared'")
            continue
        side = entry.get("side")
        path = entry.get("path")
        if side not in roots:
            defects.append(f"trophy_split: side must be ac or gch, got {side!r}")
            continue
        if not path:
            defects.append("trophy_split: entry has no path")
            continue
        if path not in files:
            defects.append(f"trophy_split: root is not in the tree: {path}")
        roots[side].append(path)
    return roots, defects


def trophy_split(data: dict, files: list[str],
                 sizes: dict[str, int]) -> tuple[dict[str, int], list[str], list[str]]:
    """The per-trophy caliber, computed from the import graph.

    Part 1 is everything outside L. Part 2 is the L content only AC needs.
    Part 3 is the L content both trophies need. Part 4 is the L content only
    GCH needs. The AC total is parts 1 to 3. An L module in neither closure is
    ambiguous and lands in part 3, which the report lists.

    IT MEASURES THE SURVIVING TREE ONLY, and it sums to standing, not to the
    tracked total. The owner ruled this on 2026-08-07 and the first version was
    wrong the other way.

    The first version counted every tracked file. That made the AC total 22,680
    against a standing figure of 19,079, so the caliber for ONE trophy was
    larger than the whole project. The cause: all 12,654 retiring lines sat
    inside the AC total. Part 2 alone held 4,500 retiring lines against 115
    that survive, because `L models AC` today runs through the choice tree that
    D18 retires.

    That version answered "what does AC touch today". This one answers "what
    does AC cost on the route we are building", which is the question the board
    already answers everywhere else: every other figure on it excludes the
    retirement set.
    """
    roots, defects = trophy_roots(data, files)
    graph = import_graph(files)
    ac = closure(graph, roots["ac"])
    gch = closure(graph, roots["gch"])
    buckets, _ = retiring(files, data)
    retired = {f for hit in buckets.values() for f in hit}
    files = [f for f in files if f not in retired]
    total = sum(sizes[f] for f in files)
    parts = {"base": 0, "ac_only": 0, "shared": 0, "gch_only": 0}
    ambiguous: list[str] = []
    for f in files:
        if not f.startswith("src/L/"):
            parts["base"] += sizes[f]
            continue
        in_ac, in_gch = f in ac, f in gch
        if in_ac and not in_gch:
            parts["ac_only"] += sizes[f]
        elif in_ac and in_gch:
            parts["shared"] += sizes[f]
        elif not in_ac and in_gch:
            parts["gch_only"] += sizes[f]
        else:
            parts["shared"] += sizes[f]
            ambiguous.append(f)
    parts["ac_total"] = parts["base"] + parts["ac_only"] + parts["shared"]
    # THE SAME NUMBER WITHOUT THE AMBIGUOUS MODULES, added 2026-08-07 after
    # [L3.32-T139] rated the single figure WEAK. The rule puts an L module in
    # neither closure into the shared part, which adds 4,077 lines from ten rud
    # modules. The reviewer's words: "A reader acting on 10,026 as the
    # delivered need would over-allocate by 4,077 lines."
    #
    # Both numbers are honest and they answer different questions.
    # `ac_total` is the route projection: it assumes the rud engine serves AC,
    # which the bridge landing will make true. `ac_delivered` is what the AC
    # endpoint's own import closure reaches today. The board shows both,
    # because showing one invites the reader to act on the wrong one.
    parts["ac_delivered"] = parts["ac_total"] - sum(sizes[f] for f in ambiguous)
    got = sum(parts[k] for k in ("base", "ac_only", "shared", "gch_only"))
    if got != total:
        msg = f"trophy split does not sum to standing: {got} != {total}"
        defects.append(msg)
        raise AssertionError(msg)
    return parts, ambiguous, defects


def trophy_matrix(rows: list[dict], split: dict[str, int],
                  standing: int) -> dict[str, dict]:
    """The nine cells of the trophy matrix, computed from the declared rows.

    The endpoint for one trophy is its standing plus the rows that trophy
    needs. A row marked AC serves the AC column. A row marked GCH serves the
    GCH column. A row marked BOTH serves both columns. The AC-and-GCH column
    is standing plus EVERY row.

    The three columns do not add up, and they must not. AC standing and GCH
    standing both count the base and the shared parts. Thus
    AC + GCH > AC-and-GCH. That is correct, not a bug.

    The identity that must hold: the AC-and-GCH column equals the endpoint
    that --brief prints. This function builds that column from every row and
    asserts the equality, so a future edit that filters the column fires the
    gate instead of silently moving the board.
    """
    ac_standing = split["ac_total"]
    gch_standing = split["base"] + split["shared"] + split["gch_only"]

    def row_sums(wanted: set[str]) -> tuple[int, int, int, int]:
        return (
            sum(r.get("naive_low", 0) for r in rows if r.get("trophy") in wanted),
            sum(r.get("naive_high", 0) for r in rows if r.get("trophy") in wanted),
            sum(r.get("calibrated_low", 0) for r in rows if r.get("trophy") in wanted),
            sum(r.get("calibrated_high", 0) for r in rows if r.get("trophy") in wanted),
        )

    cells: dict[str, dict] = {}
    for column, wanted, base in (
        ("ac", {"AC", "BOTH"}, ac_standing),
        ("gch", {"GCH", "BOTH"}, gch_standing),
        ("both", {"AC", "GCH", "BOTH"}, standing),
    ):
        nl, nh, cl, ch = row_sums(wanted)
        cells[column] = {
            "standing": base,
            "naive": (base + nl, base + nh),
            "calibrated": (base + cl, base + ch),
        }
    all_nl, all_nh, all_cl, all_ch = row_sums({"AC", "GCH", "BOTH"})
    if (cells["both"]["naive"] != (standing + all_nl, standing + all_nh)
            or cells["both"]["calibrated"] != (standing + all_cl, standing + all_ch)):
        raise AssertionError("the AC-and-GCH column does not equal the --brief endpoint")
    return cells


def main(argv: list[str]) -> int:
    mode = "full"
    for arg in argv[1:]:
        if arg == "--check":
            mode = "check"
        elif arg == "--write":
            mode = "write"
        elif arg == "--brief":
            mode = "brief"
        elif arg == "--trophy-split":
            mode = "trophy-split"
        elif arg == "--trophy-matrix":
            mode = "trophy-matrix"
        else:
            print(__doc__, file=sys.stderr)
            return 2

    data = tomllib.loads(LEDGER.read_text(encoding="utf-8"))
    files = tracked_masters()
    sizes = {f: count(f) for f in files}
    total = sum(sizes.values())

    buckets, defects = retiring(files, data)
    defects += validate_rows(data)
    try:
        split, ambiguous, split_defects = trophy_split(data, files, sizes)
    except AssertionError as exc:
        split_defects = [str(exc)]
        split, ambiguous = {}, []
    defects += split_defects

    retired = sum(sizes[f] for hit in buckets.values() for f in hit)
    standing = total - retired

    rows = data.get("remaining", [])
    nl = sum(r.get("naive_low", 0) for r in rows)
    nh = sum(r.get("naive_high", 0) for r in rows)
    cl = sum(r.get("calibrated_low", 0) for r in rows)
    ch = sum(r.get("calibrated_high", 0) for r in rows)
    line = data["basis"]["reference_line"]

    matrix = None
    matrix_defects: list[str] = []
    if split:
        try:
            matrix = trophy_matrix(rows, split, standing)
        except AssertionError as exc:
            matrix_defects = [str(exc)]
    defects += matrix_defects

    # There is no longer a prose document to render into. That document was
    # deleted on 2026-08-06: 44 percent of it was this generated block, and the
    # rest was orientation for the owner, who now reads `make dashboard`. The
    # three passages that had no other home moved into dev/ledger.toml's header
    # comment, which is where a reader editing the declaration will actually be.
    # `--write` is kept as a no-op alias for `--check` so old invocations and
    # the Makefile do not break.
    if mode == "write":
        mode = "check"

    if mode == "check":
        for d in defects:
            print(f"ledger: {d}", file=sys.stderr)
        if defects:
            print(f"ledger: {len(defects)} defect(s) in dev/ledger.toml", file=sys.stderr)
            return 1
        print(f"ledger: declaration clean; standing {standing:,} lines measured over {len(files)} masters")
        return 0

    if mode == "brief":
        print(
            f"standing {standing:,} | endpoint {(standing+nl)/1000:.2f}-{(standing+nh)/1000:.2f}k naive, "
            f"{(standing+cl)/1000:.2f}-{(standing+ch)/1000:.2f}k calibrated | "
            f"naive corner {(standing+nh-line)/1000:+.2f}k against the {line/1000:.0f}k reference"
        )
        return 1 if defects else 0

    if mode == "trophy-split":
        if split_defects:
            for d in split_defects:
                print(f"ledger: {d}", file=sys.stderr)
            return 1
        print(
            f"trophy split base {split['base']:,} | ac-only {split['ac_only']:,} "
            f"| shared {split['shared']:,} | gch-only {split['gch_only']:,} "
            # The denominator is STANDING, not the tracked total. The parts
            # exclude the retirement set, so naming `tracked` here would invite
            # the same reading that made the first version wrong.
            f"| ac-total {split['ac_total']:,} "
            f"| ac-delivered {split['ac_delivered']:,} | standing {standing:,}"
        )
        return 1 if defects else 0

    if mode == "trophy-matrix":
        if matrix is None or split_defects or matrix_defects:
            for d in split_defects + matrix_defects:
                print(f"ledger: {d}", file=sys.stderr)
            return 1
        ac = matrix["ac"]
        gch = matrix["gch"]
        both = matrix["both"]
        print(
            "trophy matrix "
            f"| ac-standing {ac['standing']:,} | gch-standing {gch['standing']:,} "
            f"| both-standing {both['standing']:,} "
            f"| ac-naive {ac['naive'][0]:,}-{ac['naive'][1]:,} "
            f"| gch-naive {gch['naive'][0]:,}-{gch['naive'][1]:,} "
            f"| both-naive {both['naive'][0]:,}-{both['naive'][1]:,} "
            f"| ac-calibrated {ac['calibrated'][0]:,}-{ac['calibrated'][1]:,} "
            f"| gch-calibrated {gch['calibrated'][0]:,}-{gch['calibrated'][1]:,} "
            f"| both-calibrated {both['calibrated'][0]:,}-{both['calibrated'][1]:,} "
            "| both-equals-brief yes"
        )
        return 1 if defects else 0

    print("Bedrock size ledger")
    print(f"  basis: {data['basis']['unit']}, {data['basis']['scope']}")
    print()
    print(f"  tracked masters                  {total:8,}  ({len(files)} files)")
    print("  booked retirements (D18):")
    for label, hit in buckets.items():
        if hit:
            print(f"    {label:<34} {sum(sizes[f] for f in hit):8,}  ({len(hit)} files)")
    print(f"    {'subtotal':<34} {retired:8,}")
    print()
    print(f"  STANDING                         {standing:8,}")
    print()
    print("  remaining work:")
    for r in rows:
        mark = " (derived)" if r.get("derived") else ""
        print(
            f"    {r['id']:<20} {r['naive_low']:6,}-{r['naive_high']:<6,} naive   "
            f"{r['calibrated_low']:6,}-{r['calibrated_high']:<6,} calibrated{mark}"
        )
    print(f"    {'subtotal':<20} {nl:6,}-{nh:<6,} naive   {cl:6,}-{ch:<6,} calibrated")
    print()
    print(f"  ENDPOINT   naive       {(standing+nl)/1000:6.2f}-{(standing+nh)/1000:.2f}k   centre {(standing+(nl+nh)/2)/1000:.2f}k")
    print(f"             calibrated  {(standing+cl)/1000:6.2f}-{(standing+ch)/1000:.2f}k   centre {(standing+(cl+ch)/2)/1000:.2f}k")
    print()
    if split:
        print("  PER-TROPHY CALIBER (AC total = parts 1 + 2 + 3):")
        print(f"    part 1 common base, outside L     {split['base']:8,}")
        print(f"    part 2 AC alone on L              {split['ac_only']:8,}")
        print(f"    part 3 shared with GCH            {split['shared']:8,}")
        print(f"    part 4 GCH alone on L             {split['gch_only']:8,}")
        print(f"    {'four parts, tracked total':<32} {total:8,}")
        print(f"    AC total (parts 1 to 3)           {split['ac_total']:8,}")
        if ambiguous:
            print(f"    ambiguous -> shared ({len(ambiguous)} modules): "
                  + ", ".join(f.removeprefix("src/L/").removesuffix(".lagda.md")
                              for f in ambiguous))
    if matrix:
        print()
        print("  TROPHY MATRIX (standing measured, endpoints computed):")
        for label, key in (("AC trophy", "ac"), ("GCH trophy", "gch"),
                           ("AC and GCH", "both")):
            c = matrix[key]
            print(
                f"    {label:<12} standing {c['standing']:7,}  "
                f"naive {c['naive'][0]:6,}-{c['naive'][1]:<6,}  "
                f"calibrated {c['calibrated'][0]:6,}-{c['calibrated'][1]:<6,}"
            )
        print("    the three columns do not add up. That is correct: AC and GCH "
              "both count the base and the shared parts.")
    print()
    print(f"  against the {line/1000:.0f}k reference line, recorded and not argued from (D26):")
    print(f"    naive corner      {(standing+nh-line)/1000:+.2f}k")
    print(f"    calibrated band   {(standing+cl-line)/1000:+.2f}k to {(standing+ch-line)/1000:+.2f}k")
    tim = data.get("timing", {})
    if tim:
        print()
        print(f"  check cost, measured {tim.get('measured','?')[:38]}")
        print(f"    full cold: {tim.get('full_cold_seconds',0)//60}m{tim.get('full_cold_seconds',0)%60:02d}s "
              f"(profile-instrumented)")
        for h in data.get("hot", []):
            sl = h["seconds"] / h["lines"]
            print(f"    HOT  {h['module']:<24} {h['seconds']:5d}s over {h['lines']:5d} lines "
                  f"= {sl:.2f} s/line")
        for r in data.get("tree_cost", []):
            print(f"         {r['tree'][:40]:<42} {r['seconds']:5d}s / {r['lines']:6d} lines "
                  f"= {r['per_line']:.3f} s/line")
    lev = data.get("lever", [])
    # The lever array also carries decision rows (rewrite-worst, rud-rewrite,
    # rud-architecture) with no band. They are not compression levers, so the
    # net block filters them out. Without the filter, full print mode crashed
    # on a KeyError; the defect predates [L3.32-T137] and this line is the fix.
    levers = [r for r in lev if "net_low" in r and "net_high" in r]
    if levers:
        nl = sum(r["net_low"] for r in levers if not r.get("gated"))
        nh = sum(r["net_high"] for r in levers if not r.get("gated"))
        print()
        print(f"  compression levers, measured but NOT funded and NOT in the sum above:")
        for r in sorted(levers, key=lambda r: -r["net_low"]):
            g = "  GATED" if r.get("gated") else ""
            print(f"    {r['id']:<20} net +{r['net_low']}-{r['net_high']:<5} "
                  f"cost {r['cost_low']}-{r['cost_high']:<5} risk {r['risk'][:22]}{g}")
        print(f"    {'ungated total':<20} net +{nl}-{nh}")
    if data.get("excluded"):
        print()
        print("  deliberately NOT in the sum:")
        for r in data["excluded"]:
            print(f"    {r['id']:<20} {r['title']}")
    if defects:
        print()
        for d in defects:
            print(f"  DEFECT: {d}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

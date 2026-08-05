#!/usr/bin/env python3
"""Size ledger for Bedrock: MEASURES standing from the tree, then sums the endpoint.

The canonical ledger data is dev/ledger.toml (read here via tomllib); the prose that
explains it is dev/LEDGER.md. This script exists because of a measured failure: the goal
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

The figures are ALSO rendered into a generated block in dev/LEDGER.md, so a reader sees the
numbers without running anything. That block is written by --write and verified by --check, so
it fails the commit gate the moment it goes stale. That is the whole trick: the numbers are
visible AND they cannot rot, because nobody is trusted to retype them.

Usage:
  ledger.py              print the full ledger
  ledger.py --check      validate the declaration and verify dev/LEDGER.md's generated block
                         (exit 1 on a defect); this is the mode `make check` runs
  ledger.py --write      regenerate that block in place; run it whenever the tree or the rows
                         move, which D27 says is at every return that could move them
  ledger.py --brief      one line: standing, endpoint band, overage
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
DOC = ROOT / "dev" / "LEDGER.md"
BEGIN = "<!-- ledger:begin -->"
END = "<!-- ledger:end -->"
FENCE = re.compile(r"```agda\n(.*?)```", re.S)


def tracked_masters() -> list[str]:
    """Git-tracked .lagda.md under src/. Untracked probes never appear here (D-1)."""
    out = subprocess.run(
        ["git", "ls-files", "src/"], cwd=ROOT, capture_output=True, text=True, check=True
    ).stdout.split()
    return sorted(f for f in out if f.endswith(".lagda.md"))


def count(path: str) -> int:
    """Non-blank lines inside ```agda fences: the one pinned caliber."""
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
        if row.get("naive_low", 0) > row.get("naive_high", 0):
            defects.append(f"remaining row {rid} has an inverted naive band")
        if row.get("calibrated_low", 0) < row.get("naive_low", 0):
            defects.append(f"remaining row {rid} is calibrated below naive, which the two-caliber discipline forbids")
    VALID = {"delivered", "ready", "in-flight", "blocked", "at-risk"}
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
    for row in data.get("owed", []):
        for dep in [d.strip() for d in row.get("blocked_by", "").split(",") if d.strip()]:
            if dep not in seen_owed and " " not in dep:
                defects.append(f"owed {row.get('id')}: blocked_by names {dep!r}, which is not "
                               f"an owed id")
    for row in data.get("excluded", []):
        if not row.get("why"):
            defects.append(f"excluded row {row.get('id', '<no id>')} does not say why it is excluded")
    return defects


def render(total, files, buckets, sizes, standing, rows, sums, line, excluded, owed) -> str:
    """The generated block for dev/LEDGER.md. Verified by --check, so it can never go stale."""
    nl, nh, cl, ch = sums
    k = lambda v: f"{v/1000:.2f}k"
    out = [BEGIN, "",
           "*Generated by `python3 scripts/ledger.py --write`, and verified by `make check`. Do",
           "not edit this block by hand: the gate compares it against the tree and fails if the",
           "two disagree.*", "",
           "### Standing", "",
           "| | lines |", "|---|---:|",
           f"| tracked masters ({len(files)} files) | {total:,} |",
           f"| booked retirements, D18 ({sum(len(h) for h in buckets.values())} files) | {retired_str(buckets, sizes)} |",
           f"| **standing** | **{standing:,}** |", "",
           "### Remaining work", "",
           "| row | naive | calibrated | class | gate |",
           "|---|---:|---:|---|---|"]
    for r in rows:
        mark = " (derived)" if r.get("derived") else ""
        out.append(
            f"| {r['title']}{mark} | {r['naive_low']:,}-{r['naive_high']:,} | "
            f"{r['calibrated_low']:,}-{r['calibrated_high']:,} | {r.get('klass','')} | {r.get('gate','none')} |")
    out += [f"| **total** | **{nl:,}-{nh:,}** | **{cl:,}-{ch:,}** | | |", "",
            "Each row's provenance is in [dev/ledger.toml](ledger.toml); a row marked derived is",
            "obtained by subtracting what has landed from a booked band, which is weaker evidence",
            "than a cited figure and must never be quoted as though a report had measured it.", "",
            "### Endpoint", "",
            "| caliber | band | centre |", "|---|---:|---:|",
            f"| naive | {(standing+nl)/1000:.2f}-{k(standing+nh)} | {k(standing+(nl+nh)/2)} |",
            f"| calibrated | {(standing+cl)/1000:.2f}-{k(standing+ch)} | {k(standing+(cl+ch)/2)} |", "",
            f"Against the {line/1000:.0f}k reference line, **recorded and not argued from** (D26):",
            f"the naive band's pessimistic corner sits {(standing+nh-line)/1000:+.2f}k from the line, and the calibrated",
            f"band sits {(standing+cl-line)/1000:+.2f}k to {(standing+ch-line)/1000:+.2f}k from it.", ""]
    if excluded:
        out += ["### Deliberately not in the sum", "",
                "An absence recorded here is a decision; an absence recorded nowhere is an oversight.", "",
                "| item | why it is out |", "|---|---|"]
        out += [f"| {r['title']} | {r['why']} |" for r in excluded]
        out.append("")
    if owed:
        out += ["### What is still owed to each trophy", "",
                "In work, not in lines. A row above can be large and unblocking, or small and on",
                "the critical path, and a band does not show the difference. Status is one of",
                "**delivered**, **ready** (dispatchable now), **in-flight**, **blocked** (with what",
                "it waits on), or **at-risk** (delivered, but on machinery scheduled to retire).", ""]
        for trophy, heading in (("AC", "L satisfies AC"), ("GCH", "L satisfies GCH"),
                                ("BOTH", "Owed to both")):
            rows_t = [r for r in owed if r.get("trophy") == trophy]
            if not rows_t:
                continue
            out += [f"**{heading}**", "", "| item | status | blocked by | what it is |",
                    "|---|---|---|---|"]
            order = {"at-risk": 0, "blocked": 1, "in-flight": 2, "ready": 3, "delivered": 4}
            for r in sorted(rows_t, key=lambda r: order.get(r.get("status"), 9)):
                out.append(f"| {r.get('title','')} | **{r.get('status','')}** | "
                           f"{r.get('blocked_by','') or '-'} | {r.get('detail','')} |")
            out.append("")
    out.append(END)
    return "\n".join(out)


def retired_str(buckets, sizes) -> str:
    return f"{sum(sizes[f] for hit in buckets.values() for f in hit):,}"


def main(argv: list[str]) -> int:
    mode = "full"
    for arg in argv[1:]:
        if arg == "--check":
            mode = "check"
        elif arg == "--write":
            mode = "write"
        elif arg == "--brief":
            mode = "brief"
        else:
            print(__doc__, file=sys.stderr)
            return 2

    data = tomllib.loads(LEDGER.read_text(encoding="utf-8"))
    files = tracked_masters()
    sizes = {f: count(f) for f in files}
    total = sum(sizes.values())

    buckets, defects = retiring(files, data)
    defects += validate_rows(data)

    retired = sum(sizes[f] for hit in buckets.values() for f in hit)
    standing = total - retired

    rows = data.get("remaining", [])
    nl = sum(r.get("naive_low", 0) for r in rows)
    nh = sum(r.get("naive_high", 0) for r in rows)
    cl = sum(r.get("calibrated_low", 0) for r in rows)
    ch = sum(r.get("calibrated_high", 0) for r in rows)
    line = data["basis"]["reference_line"]

    block = render(total, files, buckets, sizes, standing, rows, (nl, nh, cl, ch), line,
                   data.get("excluded", []), data.get("owed", []))
    doc = DOC.read_text(encoding="utf-8")
    if BEGIN in doc and END in doc:
        pre, _, restdoc = doc.partition(BEGIN)
        _, _, post = restdoc.partition(END)
        current = BEGIN + doc.partition(BEGIN)[2].partition(END)[0] + END
        if current != block:
            defects.append("dev/LEDGER.md's generated block is stale; run `python3 scripts/ledger.py --write`")
    else:
        pre, post = doc.rstrip() + "\n\n", "\n"
        defects.append("dev/LEDGER.md has no ledger:begin/ledger:end block")

    if mode == "write":
        DOC.write_text(pre + block + post, encoding="utf-8")
        print(f"ledger: dev/LEDGER.md regenerated; standing {standing:,}")
        return 0

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
    print(f"  against the {line/1000:.0f}k reference line, recorded and not argued from (D26):")
    print(f"    naive corner      {(standing+nh-line)/1000:+.2f}k")
    print(f"    calibrated band   {(standing+cl-line)/1000:+.2f}k to {(standing+ch-line)/1000:+.2f}k")
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

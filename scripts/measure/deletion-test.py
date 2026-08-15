#!/usr/bin/env python3
"""The deletion test: D36's judgment, runnable on demand.

WHY THIS EXISTS. Ruling D36 makes the DELETION TEST the cap's pass-or-fail
judgment. At the AC landing, the AC endpoint must typecheck, exit 0, in a
tree with every gch-side master removed. The surviving tree must count under
20,000 non-blank in-fence lines (raised from 16,000 by the owner, 2026-08-09). [T147] ran that test once by hand. This
tool makes it runnable at any time and at the landing.

The shadow mode is the daily proxy. It reuses scripts/measure/ledger.py's trophy
split by import, so the two can never drift apart silently. A second
implementation would drift, which is the defect class this repository keeps
finding. It reports the AC-side count, the cap, the headroom, and the file
list on request. The count is file-granular. [T155] measured the granularity
error at 2,069-2,248 lines, and the board carries that disclosure.

WHAT IT REFUSES. --run refuses without --yes, because a cold run costs
minutes. It refuses when another Agda process is live (pgrep -x agda). It
also refuses when pgrep cannot verify the process list, because the guard
fails closed. The tool is a MEASUREMENT, not a gate. It is deliberately NOT
part of make check, because --run is far too expensive for the commit gate.
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import tomllib
from pathlib import Path

# LJ-1.291: the root is found by walking up to the repository marker, never by
# counting directories; `scripts/repo_root.py` holds the one walk. LJ-1.295:
# this script lives in a group directory under scripts/, so the SCRIPTS root,
# where `repo_root.py` and `agents_tree.py` sit flat, is found the same way,
# by walking up to `repo_root.py` itself; the group directory joins sys.path
# for siblings imported by bare name.
_HERE = Path(__file__).resolve()
sys.path.insert(0, str(_HERE.parent))
_SCRIPTS = next((p for p in _HERE.parents if (p / "repo_root.py").is_file()), None)
if _SCRIPTS is None:
    raise FileNotFoundError(
        f"no repo_root.py above {_HERE}: refusing to guess the scripts root (C-43)")
sys.path.insert(0, str(_SCRIPTS))
from repo_root import find_root  # noqa: E402

ROOT = find_root(__file__)

import ledger  # noqa: E402  (sibling import; the split must never be re-implemented)

OPTIONS_RE = re.compile(r"\{-# OPTIONS .*? #-\}")
EVERYTHING = "src/Everything.lagda.md"
AC_TOTAL_RE = re.compile(r"ac-total ([0-9,]+)")


def shadow_state() -> dict:
    """The trophy split, the AC-side file set, and the count, by import."""
    data = tomllib.loads(ledger.LEDGER.read_text(encoding="utf-8"))
    files = ledger.countable_masters()
    sizes = {f: ledger.count(f) for f in files}
    try:
        split, ambiguous, defects = ledger.trophy_split(data, files, sizes)
    except AssertionError as exc:
        split, ambiguous, defects = {}, [], [str(exc)]
    parts = split.get("_files", {})
    ac_files = sorted(parts.get("base", []) + parts.get("ac_only", [])
                      + parts.get("shared", []))
    gch_files = sorted(parts.get("gch_only", []))
    return {
        "data": data,
        "split": split,
        "sizes": sizes,
        "ac_files": ac_files,
        "gch_files": gch_files,
        "ac_total": sum(sizes[f] for f in ac_files),
        "ambiguous": ambiguous,
        "defects": defects,
    }


def ac_cap(st: dict) -> int | None:
    """The cap from [trophy_budget], or None when undeclared or SUSPENDED.

    Suspended 2026-08-09 by the owner: DD5 replaced the absolute cap with a
    benchmark that is not quantified yet, so the test still MEASURES and
    still prints, and it does not fail on a retired number.
    """
    budget = st["data"].get("trophy_budget", {})
    if budget.get("thresholds_suspended"):
        return "SUSPENDED"
    return budget.get("ac_cap")


def split_vacuous(st: dict) -> bool:
    """True when there is no gch side to delete, so the test proves nothing.

    THE SECOND SUSPENSION, which this tool did not read until [LJ-0.1] found
    it. `trophy_split_suspended` empties the partition: shared and gch-only
    both read 0, so "delete the gch side and typecheck the rest" deletes
    NOTHING and typechecks the whole tree. That is not a weaker deletion
    test, it is not a deletion test at all, and the tool used to print
    "the structural test is UNCHANGED and still worth running" over exactly
    that state. A vacuous pass is worse than a refusal, because a pass gets
    quoted.
    """
    return bool(st["data"].get("trophy_split_suspended")) or not st["gch_files"]


def run_root_files(st: dict) -> list[str]:
    """The import set for --run: every AC-side master except the tree index.

    Everything imports every gch-side master by construction. A root that
    imported it would fail before it checked anything, so [T147] excluded it
    and this tool does the same.

    ITS LINES NO LONGER STAY IN THE COUNT. They did until 2026-08-10, when the
    owner ruled both catalogs, Everything and Landmarks, out of every size
    figure: a catalog grows with the project, so a threshold measured against
    a total containing one drifts away from the mathematics it bounds. The
    file list here now comes from `ledger.countable_masters()`, so the index
    is absent from the count AND from the root, which is one rule instead of
    two."""
    return [f for f in st["ac_files"] if f != EVERYTHING]


def expected_cost(ac_count: int) -> str:
    """The cost warning: minutes, anchored on [T147] and marked as a hypothesis."""
    return (f"expected cost: minutes. [T147] measured 170.94 s for the "
            f"77-master surviving tree; today's AC-side set has {ac_count} "
            f"masters. P-l: an anchored figure is a hypothesis, not a price.")


def agda_blocker() -> str | None:
    """The reason a run is refused, or None when no Agda process is live.

    pgrep exits 0 on a match, 1 on no match, and 3 on a fatal error. A guard
    that cannot see the process list fails closed: it refuses, because its
    one job is to not run beside another typecheck (C-12)."""
    probe = subprocess.run(["pgrep", "-x", "agda"], capture_output=True, text=True)
    if probe.returncode == 0:
        return "another Agda process is live."
    if probe.returncode == 1:
        return None
    lines = probe.stderr.strip().splitlines()
    tail = lines[-1] if lines else f"pgrep exit {probe.returncode}"
    return (f"pgrep cannot verify the process list ({tail}). "
            "The guard fails closed.")


def options_line() -> str:
    """The tree's own OPTIONS line, copied from Everything at HEAD."""
    text = ledger.head_text(EVERYTHING)
    match = OPTIONS_RE.search(text)
    if match is None:
        raise RuntimeError(f"{EVERYTHING} has no OPTIONS line at HEAD")
    return match.group(0)


def module_name(path: str) -> str:
    """The Agda module name for a master path."""
    return path.removeprefix("src/").removesuffix(".lagda.md").replace("/", ".")


def write_root(wt: Path, ac_files: list[str]) -> Path:
    """The green root: the tree's OPTIONS line plus one import per master."""
    lines = [options_line(), ""]
    lines += [f"import {module_name(f)}" for f in ac_files]
    root = wt / "src" / "AllButGch.agda"
    root.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return root


def fmt_wall(seconds: float) -> str:
    """Wall time as m:ss."""
    minutes, rest = divmod(int(seconds), 60)
    return f"{minutes}:{rest:02d}"


def cmd_shadow(args) -> int:
    """The cheap proxy: count, cap, headroom, and the file list on request."""
    st = shadow_state()
    for defect in st["defects"]:
        print(f"deletion-test: {defect}", file=sys.stderr)
    if st["defects"]:
        print("deletion-test: split defects; the shadow figure is not "
              "trustworthy", file=sys.stderr)
        return 1
    cap = ac_cap(st)
    if cap == "SUSPENDED" or split_vacuous(st):
        if split_vacuous(st):
            print("deletion-test: THE TEST IS VACUOUS TODAY, and this is the "
                  "honest report rather than a pass.\n"
                  "  trophy_split_suspended empties the partition: shared and "
                  "gch-only both read 0,\n"
                  "  so deleting the gch side deletes nothing and the AC total "
                  "is just the whole tree.\n"
                  "  Re-arm: LJ-2.1 rebuilds the split for the two-tower "
                  "route.", file=sys.stderr)
        if cap == "SUSPENDED":
            print("deletion-test [thresholds SUSPENDED by the owner, "
                  "2026-08-09]: DD5 replaced the absolute cap with a benchmark "
                  "nobody has measured, so there is no pass-or-fail either. "
                  "Re-arm: LJ-2.1 measures the internalization double trophy.",
                  file=sys.stderr)
        count = st["ac_total"]
        print(f"deletion test | shadow (file-granular) | ac-total {count:,} "
              f"| no cap in force | "
              f"{'SPLIT VACUOUS' if split_vacuous(st) else 'split live'}")
        if args.files:
            for part in ("base", "ac_only", "shared"):
                for path in st["split"]["_files"].get(part, []):
                    print(f"{part}\t{st['sizes'][path]:6,}\t{path}")
        return 0
    if cap is None:
        print("deletion-test: no ac_cap declared in [trophy_budget]; the "
              "deletion test needs the D36 cap", file=sys.stderr)
        return 1
    count = st["ac_total"]
    headroom = cap - count
    print(f"deletion test | shadow (file-granular) | ac-total {count:,} "
          f"| cap {cap:,} | headroom {headroom:+,}")
    print("disclosure: file-granular; the board carries the granularity "
          "error [T155] measured at 2,069-2,248 lines "
          "(agents/tasks/archive/L3-32-T155/l3.32-t155-report.md:137)")
    if args.files:
        for part in ("base", "ac_only", "shared"):
            for path in st["split"]["_files"].get(part, []):
                print(f"{part}\t{st['sizes'][path]:6,}\t{path}")
    if count >= cap:
        print("deletion test: ac-total has reached the cap. No commit may "
              "grow the AC closure (D36).", file=sys.stderr)
        return 1
    return 0


def cmd_run(args) -> int:
    """The real test, guarded: a worktree, gch-side masters deleted, one root."""
    st = shadow_state()
    cap = ac_cap(st)
    count = st["ac_total"]
    print(f"deletion test: {expected_cost(len(st['ac_files']))}")
    if not args.yes:
        print("deletion test: REFUSED. --run needs --yes to proceed.",
              file=sys.stderr)
        return 1
    blocker = agda_blocker()
    if blocker is not None:
        print(f"deletion test: REFUSED. {blocker} The deletion test must not "
              "run beside another typecheck (C-12).", file=sys.stderr)
        return 1
    for defect in st["defects"]:
        print(f"deletion-test: {defect}", file=sys.stderr)
    if st["defects"]:
        print("deletion-test: split defects; the deletion test will not run",
              file=sys.stderr)
        return 1
    if split_vacuous(st):
        # REFUSE. A run here would delete zero files, typecheck the whole
        # tree, and print a PASS. That costs minutes and proves nothing, and
        # the number it prints would be quoted as if the test had run.
        print("deletion test: REFUSED. The trophy split is suspended, so "
              "there is no gch side to delete: this run would typecheck the "
              "whole tree and call it a pass. Re-arm at LJ-2.1.",
              file=sys.stderr)
        return 1
    if cap == "SUSPENDED":
        # The structural half is still valuable when the split is live: it
        # deletes the gch side and typechecks the AC side, which is what
        # keeps the accounting honest. Only the number it compares against
        # is retired, so the run proceeds and reports without a verdict.
        print("deletion-test [thresholds SUSPENDED by the owner, 2026-08-09]: "
              "running the structural test and reporting the count; no "
              "pass-or-fail, because DD5's benchmark is not quantified yet.")
        cap = None
    elif cap is None:
        print("deletion-test: no ac_cap declared; the deletion test needs "
              "a cap", file=sys.stderr)
        return 1
    root_files = run_root_files(st)
    print(f"deletion test: deleting {len(st['gch_files'])} gch-side masters; "
          f"importing {len(root_files)} AC-side masters (Everything is "
          "excluded: it imports the gch side by construction).")
    if args.files:
        for path in root_files:
            print(f"import\t{st['sizes'][path]:6,}\t{path}")
    wt_path = None
    tmpdir = None
    try:
        tmpdir = tempfile.mkdtemp(prefix="l3.32-t190-deletion-test-")
        wt = Path(tmpdir) / "tree"
        added = subprocess.run(
            ["git", "worktree", "add", "--detach", str(wt), "HEAD"],
            cwd=ROOT, capture_output=True, text=True)
        if added.returncode != 0:
            print(f"deletion-test: git worktree add failed: "
                  f"{added.stderr.strip()}", file=sys.stderr)
            return 1
        wt_path = wt
        for path in st["gch_files"]:
            (wt / path).unlink()
        write_root(wt, root_files)
        env = os.environ.copy()
        env["GHCRTS"] = "-M8g"
        start = time.monotonic()
        proc = subprocess.run(["agda", "src/AllButGch.agda"], cwd=wt, env=env)
        wall = time.monotonic() - start
        passed = proc.returncode == 0 and count < cap
        verdict = "PASS" if passed else "FAIL"
        print(f"deletion test | run | exit {proc.returncode} | "
              f"wall {fmt_wall(wall)} | ac-total {count:,} | cap {cap:,} "
              f"| verdict {verdict}")
        return 0 if passed else 1
    finally:
        if wt_path is not None:
            subprocess.run(["git", "worktree", "remove", "--force",
                            str(wt_path)], cwd=ROOT, capture_output=True,
                           text=True)
        if tmpdir:
            shutil.rmtree(tmpdir, ignore_errors=True)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--shadow", action="store_true",
                       help="the cheap proxy: count, cap, headroom (default)")
    group.add_argument("--run", action="store_true",
                       help="the real deletion test (guarded)")
    parser.add_argument("--files", action="store_true",
                        help="print the AC-side file set")
    parser.add_argument("--yes", action="store_true",
                        help="confirm --run; a cold run costs minutes")
    args = parser.parse_args(argv[1:])
    if args.run:
        return cmd_run(args)
    return cmd_shadow(args)


if __name__ == "__main__":
    sys.exit(main(sys.argv))

#!/usr/bin/env python3
"""The deletion test: D36's judgment, runnable on demand.

WHY THIS EXISTS. Ruling D36 makes the DELETION TEST the cap's pass-or-fail
judgment. At the AC landing, the AC endpoint must typecheck, exit 0, in a
tree with every gch-side master removed. The surviving tree must count under
16,000 non-blank in-fence lines. [T147] ran that test once by hand. This
tool makes it runnable at any time and at the landing.

The shadow mode is the daily proxy. It reuses scripts/ledger.py's trophy
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

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(Path(__file__).resolve().parent))

import ledger  # noqa: E402  (sibling import; the split must never be re-implemented)

OPTIONS_RE = re.compile(r"\{-# OPTIONS .*? #-\}")
EVERYTHING = "src/Everything.lagda.md"
AC_TOTAL_RE = re.compile(r"ac-total ([0-9,]+)")


def shadow_state() -> dict:
    """The trophy split, the AC-side file set, and the count, by import."""
    data = tomllib.loads(ledger.LEDGER.read_text(encoding="utf-8"))
    files = ledger.tracked_masters()
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
    """The D36 cap from [trophy_budget], or None when undeclared."""
    return st["data"].get("trophy_budget", {}).get("ac_cap")


def run_root_files(st: dict) -> list[str]:
    """The import set for --run: every AC-side master except the tree index.

    Everything imports every gch-side master by construction. A root that
    imported it would fail before it checked anything, so [T147] excluded it
    and this tool does the same. Its lines stay in the count, because the
    ledger split books it in the base part and the judgment counts the
    surviving tree, not the imported root."""
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
          "(_build/l3.32-t155-report.md:137)")
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
    if cap is None:
        print("deletion-test: no ac_cap declared; the deletion test needs "
              "the D36 cap", file=sys.stderr)
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

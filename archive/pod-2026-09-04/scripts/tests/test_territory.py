#!/usr/bin/env python3
"""Regression tests for the write-territory refusal.

WHY THIS FILE EXISTS. On 2026-08-08 two live lanes were dispatched with `the
shared home you propose` in their SCOPE (write). Both proposed
`src/L/LevelKit.lagda.md`, and both wrote it. Nothing was lost, because they
happened to append to different regions, but that is luck and not a mechanism.
`brief_in_flight` did not fire: it keys on the brief PATH, and these were two
different briefs.

The refusal has two halves and both are pinned here. A NAMED collision is a set
intersection. An UNNAMED one has no path to compare, so two open grants live at
once is itself the refusal. The negative cases matter as much: a prohibition
line grants nothing, and every brief writes a report under `_build/`, so if
either counted as territory the check would refuse every parallel dispatch and
be turned off within a day.

IT WAS ORPHANED AND IT IS NOT NOW. The file sat under `.claude/skills/codex-dispatch/`
and loaded `dispatch.py` from that directory. The POD cutover moved the refusal into
`scripts/pod/launcher.py` and archived `dispatch.py`, so this file died at IMPORT and the
regression it pins went unguarded in silence. `.claude/` is git-ignored, so nothing could
see it. The logic itself survived the move whole: `write_paths`, `open_grant`,
`territory_in_flight`, `running` and `load` are all in the launcher, and every check below
passes against it unchanged.

Run: `.venv/bin/python scripts/tests/test_territory.py`   (or: make test)
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

# The repository root is two directories up from `scripts/tests/`, and the module under
# test is the launcher, which is where AD17's territory check lives after the cutover.
ROOT = Path(__file__).resolve().parents[2]
_s = importlib.util.spec_from_file_location(
    "pod_launcher", ROOT / "scripts" / "pod" / "launcher.py")
D = importlib.util.module_from_spec(_s)
sys.modules["pod_launcher"] = D
_s.loader.exec_module(D)

failures = 0


def check(label, got, want):
    global failures
    ok = got == want
    if not ok:
        failures += 1
    print(f"  {'ok  ' if ok else 'FAIL'} {label}" + ("" if ok else f": {got!r} != {want!r}"))


def brief(tmp: Path, name: str, scope: str) -> Path:
    p = tmp / name
    p.write_text(f"# b\n\ntier: codex\n\n## SCOPE (write)\n\n{scope}\n\n"
                 f"## RETURN\n\nEvidence is file:line.\n", encoding="utf-8")
    return p


def live(monkey_brief: Path, name: str):
    """Pin the registry to one live lane holding `monkey_brief`."""
    D.running = lambda _reg=None: {name: {"brief": str(monkey_brief)}}
    D.load = lambda: {}


def main() -> int:
    import tempfile
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)

        print("write_paths: what a scope actually grants")
        b = brief(tmp, "a.md", "- `src/L/Rud/StepGraph.lagda.md`\n- `_build/r.md`")
        check("grant lines are territory", D.write_paths(b),
              {"src/L/Rud/StepGraph.lagda.md", "_build/r.md"})
        b2 = brief(tmp, "b.md", "- `src/L/A.lagda.md`\n\nNever `src/Everything.lagda.md`.")
        check("a prohibition grants nothing", D.write_paths(b2), {"src/L/A.lagda.md"})
        check("no scope section is no territory",
              D.write_paths(tmp / "missing.md"), set())

        print("open_grant: the write whose target the brief cannot name")
        b3 = brief(tmp, "c.md", "- `src/L/A.lagda.md`, and the shared home you propose")
        check("an unnamed home is an open grant", D.open_grant(b3), True)
        check("a fully named scope is not", D.open_grant(b2), False)
        p = tmp / "e.md"
        p.write_text("# b\n\ntier: codex\n\nArgue the home you propose in the report.\n\n"
                     "## SCOPE (write)\n\n- `src/L/A.lagda.md`\n\n## RETURN\n\nfile:line\n",
                     encoding="utf-8")
        check("the phrase outside SCOPE (write) grants nothing", D.open_grant(p), False)

        print("territory_in_flight: the refusal")
        x = brief(tmp, "x.md", "- `src/L/Rud/LevelSigma.lagda.md`")
        y = brief(tmp, "y.md", "- `src/L/Rud/LevelSigma.lagda.md`")
        live(x, "t225")
        got = D.territory_in_flight(y, "t226")
        check("a named collision refuses", got is not None and got[0], "t225")
        check("and names the contested file",
              "src/L/Rud/LevelSigma.lagda.md" in (got[1] if got else set()), True)

        # THE CASE THAT ACTUALLY HAPPENED: nothing shared is named anywhere.
        a1 = brief(tmp, "a1.md", "- `src/L/Rud/StepGraph.lagda.md`, and the home you propose")
        a2 = brief(tmp, "a2.md", "- `src/L/Rud/StepStory.lagda.md`, and the home you propose")
        check("no path is named in common", D.write_paths(a1) & D.write_paths(a2), set())
        live(a1, "t225")
        got = D.territory_in_flight(a2, "t226")
        check("two open grants refuse anyway", got is not None and got[0], "t225")

        r1 = brief(tmp, "r1.md", "- `_build/l3.32-t1-report.md`")
        r2 = brief(tmp, "r2.md", "- `_build/l3.32-t1-report.md`")
        live(r1, "t1")
        check("reports alone never clash", D.territory_in_flight(r2, "t2"), None)

        s = brief(tmp, "s.md", "- `src/L/A.lagda.md`")
        live(s, "t9")
        check("a lane never clashes with itself", D.territory_in_flight(s, "t9"), None)

        print("wrapped prohibitions")
        w = tmp / "w.md"
        w.write_text("# b\n\ntier: codex\n\n## SCOPE (write)\n\n"
                     "- `_build/r.md`\n\n"
                     "Never any master. Never `src/Everything.lagda.md`. Never\n"
                     "`dev/JOURNAL.md` or `src/L/Rud/BelowLim.lagda.md`:\n"
                     "siblings hold both. No git.\n\n"
                     "## RETURN\n\nfile:line\n", encoding="utf-8")
        check("a prohibition that WRAPS grants nothing", D.write_paths(w), {"_build/r.md"})

    print(f"\n{13 - failures}/13 checks passed")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())


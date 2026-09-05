#!/usr/bin/env python3
"""LJ-1.177: census every module telescope in a master, by parenthesis depth.

WHY. `[LJ-1.155]` measured that a long module telescope is prepended to the
STORED TYPE of every definition inside the module, and that Agda's
`DeadCode.DeadCodeReachable` pass then walks those stored types once per
definition.  `[LJ-1.158]` cured the three `*Agree` masters that way and named
`src/L/Condensation.lagda.md`'s OWN row telescopes as the next unmeasured term
(`agents/tasks/LJ-1-158/lj-1.158-report.md:320-330`).

This script finds them.  A module header runs from `module <Name>` to the
`where` that closes it AT PAREN DEPTH ZERO, so a `where` inside a hypothesis
type never ends the header.  A hypothesis is one top-level parenthesis group.

Usage:
    census_telescopes.py <master> [<master> ...]
"""
from __future__ import annotations

import pathlib
import re
import sys

MODULE = re.compile(r"^(\s*)module\s+([^\s{(]+)")
# `module X = Y args` is a module APPLICATION.  It declares no telescope, so it
# must never be read as a header.  MEASURED: without this guard the parser runs
# past the application to the next unrelated `where` and reports a 231-line
# telescope at `src/L/Condensation.lagda.md:4811`, which is a module BODY.
APPLICATION = re.compile(r"^\s*module\s+[^\s{(]+\s*=")


def fences(lines: list[str]) -> list[bool]:
    """True on a line that sits INSIDE an ```agda fence."""
    inside, out = False, []
    for line in lines:
        if line.startswith("```agda"):
            inside = True
            out.append(False)
            continue
        if line.startswith("```"):
            inside = False
            out.append(False)
            continue
        out.append(inside)
    return out


def telescopes(path: pathlib.Path):
    lines = path.read_text().split("\n")
    live = fences(lines)
    rows = []
    i = 0
    while i < len(lines):
        if not live[i]:
            i += 1
            continue
        m = MODULE.match(lines[i])
        if not m or APPLICATION.match(lines[i]):
            i += 1
            continue
        # Walk to the `where` at depth 0.  Track parens and braces together.
        depth, j, end = 0, i, None
        header: list[str] = []
        while j < len(lines) and j - i < 500:
            line = lines[j]
            header.append(line)
            k = 0
            while k < len(line):
                ch = line[k]
                if ch in "({":
                    depth += 1
                elif ch in ")}":
                    depth -= 1
                elif depth == 0 and line.startswith("where", k) and (
                    k == 0 or not line[k - 1].isalnum()
                ):
                    end = j
                    break
                k += 1
            if end is not None:
                break
            j += 1
        if end is None:
            i += 1
            continue
        text = "\n".join(header)
        # Count top-level parenthesis groups AFTER the module name.
        after = text[text.index(m.group(2)) + len(m.group(2)):]
        depth, groups, implicit = 0, 0, 0
        for ch in after:
            if ch == "(":
                if depth == 0:
                    groups += 1
                depth += 1
            elif ch == ")":
                depth -= 1
            elif ch == "{":
                if depth == 0:
                    implicit += 1
                depth += 1
            elif ch == "}":
                depth -= 1
        rows.append(
            {
                "name": m.group(2),
                "start": i + 1,
                "end": end + 1,
                "lines": end - i + 1,
                "explicit": groups,
                "implicit": implicit,
                "chars": len(text),
                "indent": len(m.group(1)),
            }
        )
        i = end + 1
    return rows


def main() -> int:
    for arg in sys.argv[1:]:
        path = pathlib.Path(arg)
        rows = telescopes(path)
        rows.sort(key=lambda r: -r["explicit"])
        print(f"\n=== {arg} : {len(rows)} modules with a header ===")
        print(f"{'module':24s} {'start':>6s} {'end':>6s} {'lines':>5s} "
              f"{'expl':>5s} {'impl':>5s} {'chars':>6s} {'ind':>4s}")
        for r in rows[:30]:
            print(f"{r['name']:24s} {r['start']:6d} {r['end']:6d} "
                  f"{r['lines']:5d} {r['explicit']:5d} {r['implicit']:5d} "
                  f"{r['chars']:6d} {r['indent']:4d}")
        print(f"TOTAL header lines {sum(r['lines'] for r in rows)}, "
              f"explicit hypotheses {sum(r['explicit'] for r in rows)}")
        big = [r for r in rows if r["explicit"] >= 10]
        print(f"MODULES WITH 10+ EXPLICIT HYPOTHESES: {len(big)}, "
              f"holding {sum(r['explicit'] for r in big)} hypotheses over "
              f"{sum(r['lines'] for r in big)} header lines")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

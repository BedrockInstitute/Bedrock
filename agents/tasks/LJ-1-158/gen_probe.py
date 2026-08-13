#!/usr/bin/env python3
"""LJ-1.158 probe generator: one master's telescope, as a TELESCOPE or as a RECORD.

`[LJ-1.155]` measured the telescope-to-record collapse on `UpperAgree`'s 36
hypotheses only, and named the rest as its own unmeasured term: `TwelveAgree`
carries 62 hypotheses and 13,976 of the 24,469 ms. P-l forbids a transplant by
analogy. This generator makes the controlled pair cheap for the other two
masters.

It extends `agents/tasks/LJ-1-155/gen_record_probe.py` to any of the three
masters and to both sides of the pair. Every hypothesis comes from the master
VERBATIM; nothing is retyped.

Usage:
    gen_probe.py <suffix> <upper|lower|twelve> <telescope|record> [keep,in,telescope]
"""
from __future__ import annotations

import pathlib
import sys

ROOT = pathlib.Path("/Users/alsg/Agentic/Bedrock")

# master key -> (path, module header line, first hypothesis line, last
# hypothesis line, gamma name), all 1-indexed and inclusive, at HEAD.
MASTERS = {
    "upper": ("src/L/Condensation/UpperAgree.lagda.md", 77, 80, 178, "γ"),
    "lower": ("src/L/Condensation/LowerAgree.lagda.md", 76, 79, 187, "γ"),
    "twelve": ("src/L/Condensation/TwelveAgree.lagda.md", 114, 117, 287, "γ'"),
}


def split_groups(text: str) -> list[str]:
    """Split a telescope's source into one string per parenthesised hypothesis."""
    groups: list[str] = []
    depth, cur = 0, []
    for ch in text:
        if ch == "(":
            if depth == 0:
                cur = []
            depth += 1
            if depth == 1:
                continue
        if ch == ")":
            depth -= 1
            if depth == 0:
                groups.append("".join(cur))
                continue
        if depth >= 1:
            cur.append(ch)
    return groups


def read_master(key: str) -> tuple[list[str], str, list[str], str]:
    path, head, first, last, gam = MASTERS[key]
    src = (ROOT / path).read_text().split("\n")
    lead = src[head : first - 1]          # the Fin block and the gamma line
    raw = "\n".join(src[first - 1 : last])  # the hypotheses, verbatim
    return lead, raw, split_groups(raw), gam


#: A name the master DEFINES rather than imports, which a probe over its
#: telescope must therefore import from the master. MEASURED: `LowerAgree`
#: states `someEnv : someEnvDef {n} K γ` and declares `someEnvDef` at `:51`.
EXTRA = {
    "lower": "open import L.Condensation.LowerAgree {ℓ} lem using ( someEnvDef )",
}


def imports(key: str) -> str:
    """The master's own import block, verbatim, from `open import FOL.ZFStructure`."""
    path = MASTERS[key][0]
    src = (ROOT / path).read_text().split("\n")
    start = next(i for i, s in enumerate(src) if s.startswith("open import FOL.ZFStructure"))
    end = next(i for i, s in enumerate(src) if s.startswith("open AbsL renaming"))
    block = "\n".join(src[start : end + 1])
    if key in EXTRA:
        block += "\n" + EXTRA[key]
    return block


def params(lead: list[str]) -> str:
    """The record's argument list, read off the lead lines."""
    out = []
    for line in lead:
        body = line.strip().lstrip("(").rstrip(")")
        out.append(body.split(":")[0].strip())
    return " ".join(out)


HEADER = """-- LJ-1.158, probe {sfx}.  THE CONTROLLED PAIR AT `{key}`.
--
-- `[LJ-1.155]` measured the telescope-to-record collapse on `UpperAgree`'s 36
-- hypotheses: `DeadCode.DeadCodeReachable` 2,652 ms to 25 ms.  It named its own
-- unmeasured term: `TwelveAgree` carries a longer telescope and 13,976 of the
-- 24,469 ms, and a measured cure does not transfer by analogy (P-l).
--
-- THIS FILE IS THE {mode} SIDE of that pair at `{key}`.  It carries {count}
-- hypotheses and the SAME eight definitions that do no work, so the two sides
-- differ in the statement of the block and in nothing else.
--
-- Every hypothesis is `{path}` verbatim,
-- machine-extracted by `agents/tasks/LJ-1-158/gen_probe.py`.
--
-- Read with `agda --profile=internal`.

{{-# OPTIONS --cubical --safe --guardedness #-}}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-158.ProbeLJ1158{sfx} {{ℓ : Level}} (lem : LEM (ℓ-suc ℓ)) where

{imports}

"""

DEFS = """
  -- Eight definitions that do no work.  Their stored types carry whatever the
  -- module telescope is, and `DeadCode.DeadCodeReachable` walks those types.
"""

ONE_DEF = """
  d{i} : (a : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) {gam}) ⟩
     → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) {gam}) ⟩
  d{i} a h = h
"""


def main() -> int:
    sfx, key, mode = sys.argv[1], sys.argv[2], sys.argv[3]
    keep = set(sys.argv[4].split(",")) if len(sys.argv) > 4 else set()
    lead, raw, groups, gam = read_master(key)
    names = [g.split(":")[0].strip() for g in groups]
    tele = [g for g, nm in zip(groups, names) if nm in keep]
    fields = [g for g, nm in zip(groups, names) if nm not in keep]

    out = HEADER.format(
        sfx=sfx, key=key, mode=mode.upper(), count=len(groups),
        path=MASTERS[key][0], imports=imports(key),
    )
    if mode == "record":
        out += "record RFacts {n : ℕ}\n"
        out += "\n".join(lead) + " : Type (ℓ-suc ℓ) where\n  field\n"
        for g in fields:
            lines = g.split("\n")
            out += "    " + lines[0].strip() + "\n"
            for extra in lines[1:]:
                out += "      " + extra.strip() + "\n"
        out += "\nmodule Big {n : ℕ}\n" + "\n".join(lead) + "\n"
        for g in tele:
            lines = g.split("\n")
            out += "  (" + lines[0].strip() + "\n"
            for extra in lines[1:-1]:
                out += "   " + extra.strip() + "\n"
            if len(lines) > 1:
                out += "   " + lines[-1].strip() + ")\n"
            else:
                out = out[:-1] + ")\n"
        out += f"  (f : RFacts {params(lead)})\n  where\n"
    else:
        out += "module Big {n : ℕ}\n" + "\n".join(lead) + "\n" + raw + "\n  where\n"
    out += DEFS
    for i in range(8):
        out += ONE_DEF.format(i=i, gam=gam)
    dest = ROOT / f"agents/tasks/LJ-1-158/ProbeLJ1158{sfx}.agda"
    dest.write_text(out)
    print(f"{dest}: {key} {mode}, {len(groups)} hypotheses, "
          f"{len(fields)} in the record, {len(tele)} kept in the telescope")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

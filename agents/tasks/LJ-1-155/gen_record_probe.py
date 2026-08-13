#!/usr/bin/env python3
"""Generate one LJ-1.155 record probe over a chosen subset of the telescope.

Probe B4 measured that stating `UpperAgree`'s 36 hypotheses as a RECORD
exhausts an 8 GB heap, while stating the SAME 36 as a module telescope costs
5.7 s (probe B1).  This generator makes the bisection cheap: it writes a file
that declares a record over any subset of the 36, and nothing else.

Every field comes from `src/L/Condensation/UpperAgree.lagda.md:80-178`
verbatim.  Nothing is retyped.

Usage:
    gen_record_probe.py <suffix> <first-index> <last-index-inclusive> [drop,drop]
"""
from __future__ import annotations

import pathlib
import sys

ROOT = pathlib.Path("/Users/alsg/Agentic/Bedrock")
MASTER = ROOT / "src/L/Condensation/UpperAgree.lagda.md"


def telescope() -> tuple[list[str], list[str]]:
    src = MASTER.read_text().split("\n")
    tel = src[76:178]
    lead = tel[1:3]
    text = "\n".join(tel[3:])
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
    assert len(groups) == 36, len(groups)
    return lead, groups


HEADER = """-- LJ-1.155, probe B{sfx}.  BISECTING THE RECORD WALL.
--
-- Probe B4 stated `UpperAgree`'s 36 telescope hypotheses as a RECORD and
-- exhausted an 8 GB heap in 117 s.  Probe B1 stated the SAME 36 as a module
-- telescope and cost 5.7 s.  This file narrows the wall to a field range.
--
-- FIELDS {lo} to {hi} of 36, named: {names}
--
-- Every field is `src/L/Condensation/UpperAgree.lagda.md:80-178` verbatim,
-- machine-extracted by `agents/tasks/LJ-1-155/gen_record_probe.py`.
--
-- Read with `agda --profile=internal`.

{{-# OPTIONS --cubical --safe --guardedness #-}}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-155.ProbeLJ1155B{sfx} {{ℓ : Level}} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_ )
import FOL.Absoluteness
open import V.Hierarchy {{ℓ}} using ( 𝒮ᵥ )
open import V.Coding {{ℓ}} using ( pr )
open import L.Constructible {{ℓ}} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {{ℓ}} using ( numeralL; sucʟ; sucʟ-fst )
open import L.Coding.Model {{ℓ}}
  using ( prʟ; prʟ-fst; envSetAt; envOverAt; tmValAt; consAtL; subValSuccAt )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

"""


def main() -> int:
    sfx, lo, hi = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    drop = {int(x) for x in sys.argv[4].split(",")} if len(sys.argv) > 4 else set()
    lead, groups = telescope()
    chosen = [g for i, g in enumerate(groups) if lo <= i <= hi and i not in drop]
    names = ", ".join(g.split(":")[0].strip() for g in chosen)
    out = HEADER.format(sfx=sfx, lo=lo, hi=hi, names=names)
    out += "record UFacts {n : ℕ}\n"
    out += "\n".join(lead) + " : Type (ℓ-suc ℓ) where\n  field\n"
    for g in chosen:
        lines = g.split("\n")
        out += "    " + lines[0].strip() + "\n"
        for extra in lines[1:]:
            out += "      " + extra.strip() + "\n"
    dest = ROOT / f"agents/tasks/LJ-1-155/ProbeLJ1155B{sfx}.agda"
    dest.write_text(out)
    print(f"{dest}: fields {lo}..{hi} ({len(chosen)}) -> {names}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

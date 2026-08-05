#!/usr/bin/env python3
"""Regression tests for the caliber counter.

WHY THIS FILE EXISTS. `dev/ledger.toml` claimed two parser fixes were "covered
by regression tests in the tool". They were not: the tests had been run inline
in a shell and never written down, so the claim was false and
`[L3.32-T95]`'s adversarial pass caught it. Every case below is a defect that
was once live and shipped a wrong published number, or a construct that must
keep working.

Run: `python3 scripts/tests/test_obligations.py`
"""

from __future__ import annotations

import importlib.util
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
spec = importlib.util.spec_from_file_location(
    "obligations", ROOT / "scripts" / "obligations.py"
)
obligations = importlib.util.module_from_spec(spec)
spec.loader.exec_module(obligations)


def count(body: str) -> int:
    d = Path(tempfile.mkdtemp()) / "T.lagda.md"
    d.write_text("```agda\n" + body + "\n```\n", encoding="utf-8")
    return obligations.scan(d)["signatures"]


CASES = [
    # --- defects that shipped a wrong number ---
    ("-- The range read, at the meta level: x in ran f", 0,
     "line comment with a colon: scored 8, inflating both trees ~11 percent"),
    ("  -- indented comment: with a colon", 0,
     "indented line comment"),
    ("{- a block: with a colon -}", 0,
     "single-line block comment"),
    ("{- opening a block:\nstill inside: here\n-}", 0,
     "block comment spanning lines"),
    ("  let z∈m : ⟨ z ∈ˢ m ⟩", 1,
     "let binding declares z∈m, not `let`: scored 2 at 47 sites"),
    ("  with h : A", 1,
     "with-abstraction binder is not itself a name"),

    # --- constructs that must keep working ---
    ("f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : Op16", 16,
     "the genuine 16-name signature at L.Rud.Step:202"),
    ("csb : (a b : S) (f : ⟪ a ⟫ → ⟪ b ⟫)", 1,
     "ordinary top-level signature with a telescope"),
    ("  foo : Bar", 1, "indented local signature"),
    ("_∈ˢ_ : S → S → Type", 1, "operator name"),
    ("open import Base.Prelude using ( f ; g )", 0, "import line"),
    ("module L.Rud.Bridge {ℓ : Level} (lem : LEM ℓ) where", 0,
     "module header with a parameter telescope"),
    ("data Foo : Type where", 0, "data header"),
    ("record Bar : Type where", 0, "record header"),
    ("variable x : S", 0, "variable block header"),
    ("infixl 5 _∈ˢ_", 0, "fixity"),

    # --- the known blind spot, asserted so a future change is deliberate ---
    ("fib = ∈-asFiber {a = ε} {b = α} ε∈α", 0,
     "signature-less definition is NOT counted: real at Bridge:814. "
     "[T95] measured this class at 421 lines retiring against 216 surviving, "
     "an asymmetry that moves the cross-tree ratio 4.20 to 4.38. If this "
     "assertion ever flips, the ledger's caliber block must be re-derived."),
]


def main() -> int:
    failures = 0
    for body, want, why in CASES:
        got = count(body)
        ok = got == want
        failures += not ok
        print(f"  {'ok  ' if ok else 'FAIL'} want {want:2d} got {got:2d}  {why}")
    print(f"\n{len(CASES) - failures}/{len(CASES)} passed")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())

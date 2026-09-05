#!/usr/bin/env python3
"""LJ-1.209 probe generator: the sealed and unsealed arms of one paired series.

Each probe is the ```agda code of src/L/Condensation.lagda.md in the working
tree, with the top module renamed, written as a plain .agda file under this
task dir.  A probe is never a master edit.

Arms:
  --arm plain   verbatim copy, module renamed.  The UNSEALED baseline.
  --arm seal    the same code, plus an `opaque isNumeral` definition, with
                every occurrence of the numeral property rewritten to
                `isNumeral (fst ar)` or `isNumeral (fst N)`.

Usage:
  python3 gen_probes.py --arm plain --out Plain
  python3 gen_probes.py --arm seal  --out Seal
"""
import sys
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent.parent
FENCE = re.compile(r"```agda\n(.*?)```", re.S)
MODDECL = re.compile(r"module L\.Condensation\b")

# The two spellings of the property, exactly as they sit in the master.
PROP_AR = "∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁"
PROP_N = "∥ Σ[ n ∈ ℕ ] (fst N ≡ # n) ∥₁"

SEAL = """
-- LJ-1.209 SEAL.  The numeral property, named once and sealed.  The
-- consumers never look inside it: in this wing the property is only ever
-- a hypothesis, so the elaborator meets a stuck head at every type site.
opaque
  isNumeral : V ℓ → Type (ℓ-suc ℓ)
  isNumeral x = ∥ Σ[ n ∈ ℕ ] (x ≡ # n) ∥₁
"""

# The discriminator.  It keeps the extra telescope COMPONENT and throws the
# numeral CONTENT away.  It is not mathematics; it isolates one term.
TRIVIAL = """
-- LJ-1.209 DISCRIMINATOR.  The component stays, the content goes.  This
-- probe answers one question: does the 8.4 s follow the numeral property,
-- or does it follow the extra telescope component alone?
-- `x ≡ x` sits at the same level and holds no numeral machinery: no ℕ,
-- no `#`, no Σ, no truncation.  It is not mathematics; it is a placeholder
-- of the right shape.
isNumeral : V ℓ → Type (ℓ-suc ℓ)
isNumeral x = x ≡ x
"""


def code_blocks(text: str) -> list[str]:
    return FENCE.findall(text)


def main() -> int:
    args = sys.argv[1:]
    arm = "plain"
    out_name = None
    i = 0
    while i < len(args):
        if args[i] == "--arm":
            arm = args[i + 1]
            i += 2
        elif args[i] == "--out":
            out_name = args[i + 1]
            i += 2
        else:
            i += 1

    text = (ROOT / "src/L/Condensation.lagda.md").read_text(encoding="utf-8")
    blocks = code_blocks(text)
    n_ar = sum(b.count(PROP_AR) for b in blocks)
    n_n = sum(b.count(PROP_N) for b in blocks)

    if arm in ("seal", "trivial"):
        blocks = list(blocks)
        blocks[0] = blocks[0] + (SEAL if arm == "seal" else TRIVIAL)
        blocks = [
            b.replace(PROP_AR, "isNumeral (fst ar)").replace(
                PROP_N, "isNumeral (fst N)")
            if k > 0 else b
            for k, b in enumerate(blocks)
        ]

    code = "\n".join(blocks)
    newname = out_name or arm.capitalize()
    code = MODDECL.sub(f"module LJ-1-209.Probe{newname}", code, count=1)
    dest = ROOT / "agents/tasks/LJ-1-209" / f"Probe{newname}.agda"
    dest.write_text(code, encoding="utf-8")
    print(f"wrote {dest} ({len(code.splitlines())} lines, {len(blocks)} blocks)")
    print(f"  arm={arm}  fst-ar sites={n_ar}  fst-N sites={n_n}  total={n_ar + n_n}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

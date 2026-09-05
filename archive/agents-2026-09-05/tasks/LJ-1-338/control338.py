"""[LJ-1.338] The two negative controls, built by ONE-LINE edits.

`[LJ-1.336]` ran two controls and one of them fired INSIDE a copied
proof, which is why its zero was believable.  This script builds the same
two shapes for site 3.

CONTROL A, LOCALITY INSIDE THE COPIED BLOCK.  It changes one field of the
VERBATIM copy of `module KValue`, from `B.num∈λ 0` to `B.num∈λ 1`.  Agda
must refuse, and it must refuse at that field.

CONTROL B, NON-VACUITY OF SITE 3's ENVIRONMENT.  It changes the code slot
`e1` from a real tagged pair to a numeral.  The tie `keyValK` still
holds, because it holds for ANY code slot inside the bound; the
INHABITANT `keyValK-live` must die.  Without this control the tie could
be true because nothing meets it.

Run it from the repository root.  It writes the two files and prints the
diff line count, which must be 1 for each.
"""

from pathlib import Path

TASK = Path(__file__).resolve().parent

CONTROLS = [
    ("ProbeKValue338.agda", "ControlA338.agda", "ProbeKValue338", "ControlA338",
     "    ; numK0 = B.num∈λ 0 ; numK1 = B.num∈λ 1 ; numK2 = B.num∈λ 2",
     "    ; numK0 = B.num∈λ 1 ; numK1 = B.num∈λ 1 ; numK2 = B.num∈λ 2"),
    ("ProbeLeaf338.agda", "ControlB338.agda", "ProbeLeaf338", "ControlB338",
     "  e1 = prʟ (PKV.numeralL 1) (PKV.numeralL 0)",
     "  e1 = PKV.numeralL 0"),
    # CONTROL C, THE SHARPER NON-VACUITY.  It changes the TAG the
    # inhabitant claims, from one to two.  The tie `keyValK` is
    # untouched and stays green; only the INHABITANT dies, at its own
    # line.  So the hypothesis of tie 9 is a real constraint and the
    # environment meets it for one tag only.
    ("ProbeLeaf338.agda", "ControlC338.agda", "ProbeLeaf338", "ControlC338",
     "  keyValK-live : ⟨ (PKV.numeralL 0 ∷ γ) ⊨ tagAtL (suc (suc zero)) 1 zero ⟩",
     "  keyValK-live : ⟨ (PKV.numeralL 0 ∷ γ) ⊨ tagAtL (suc (suc zero)) 2 zero ⟩"),
]


def main():
    for src, dst, oldmod, newmod, old, new in CONTROLS:
        text = (TASK / src).read_text(encoding="utf-8")
        if old not in text:
            raise SystemExit("control line not found in %s: %r" % (src, old))
        out = text.replace(old, new).replace(oldmod, newmod)
        (TASK / dst).write_text(out, encoding="utf-8")
        a = text.replace(oldmod, newmod).splitlines()
        b = out.splitlines()
        changed = sum(1 for x, y in zip(a, b) if x != y)
        print("%s -> %s: %d changed line(s)" % (src, dst, changed))


if __name__ == "__main__":
    main()

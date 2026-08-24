# [LJ-1.618] stop: the circle reaches the site grain, and the residue is the untruncation of the least-cardinal injection

## THE STOP

**NO-GO on `pairing-at-alpha`.** The brief's obligation is a pairing
with its injectivity at ONE infinite ordinal, for every infinite
ordinal:

```
pairing-at-alpha :
  (α : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → Σ[ f ∈ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫) ]
      ((x y : ⟪ α ⟫ × ⟪ α ⟫) → f x ≡ f y → x ≡ y)
```

The probe proves the obligation FROM one named residue,
`Inj-extract` (`agents/tasks/LJ-1-618/Probe618.agda:151-154`), by the
recursion of the tree's own closed chapter with the motive untruncated
(`pairing-from-extract`, `agents/tasks/LJ-1-618/Probe618.agda:210-211`).
The residue is the untruncation of the least-cardinal injection:

```
Inj-extract = (a : S) (oa : IsOrd (fst a))
            → ∥ ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫ ∥₁
            → ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫
```

No row of the probe, and no term of the tree, inhabits it. So the
question "does one instance also need the untruncation" has a measured
answer: **YES. At every infinite ordinal that is neither ω nor initial,
the only route the tree has is the least-cardinal descent, and its one
missing ingredient is a data payload held inside a truncation.**

## THE EVIDENCE, ALL AT `file:line`

**1. THE TREE HOLDS THE FIBER AT TWO KINDS OF ONE α, HONEST.** Both are
re-ascribed at the brief's own Σ, TYPE ONLY, and both typecheck
(`agents/tasks/LJ-1-618/runs/W3.agda:62-78`, green in 1.51 s under a
120 s cap, `runs/w3-3.out`):

| supply | reaches | truncation | home |
|---|---|---|---|
| `squareω : sq ω` | ω only | none | `src/L/InjChain.lagda.md:184-185` |
| `via-col-square : (α : S) → Init α → sq α` | every `Init` ordinal, one at a time | none | `src/L/Ordinal/SquareLaw.lagda.md:960-961` |

`Init` demands ω as a STRICT member
(`src/L/Ordinal/SquareLaw.lagda.md:694`), so the second row does not
reach ω and does not reach a non-initial ordinal.

**2. THE OBLIGATION QUANTIFIES OVER ALL INFINITE ORDINALS, AND THE
NON-INITIAL ONES ARE THE HOLE.** The recursion that reaches every
infinite ordinal exists in the tree, truncated
(`sq-trunc-closed`, `src/L/SquareLawClosed.lagda.md:325-328`), and its
descent case is the only case that does not close untruncated
(`src/L/SquareLawClosed.lagda.md:314-318`): it needs the honest
injection `⟪ x ⟫ ↪ ⟪ fst κ ⟫`, and what the tree holds is
`κ-injL : ∥ ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫ ∥₁`
(`src/L/Cardinal.lagda.md:133-134`).

**3. THE TRUNCATION IS BY CONSTRUCTION, AND IT IS NOT A dne.** The
least-cardinal search feeds `leastOf` an hProp, so the injection
existence enters the search truncated
(`InjP γ = ∥ Inj γ ∥₁ , squash₁`, `src/L/Cardinal.lagda.md:66-67`), and
the least index comes out honest while the payload does not
(`dev/literature/truncation-and-selection.md:145-148`). The payload is
a Σ whose first component is a function
(`_↪_`, `src/L/Cardinal.lagda.md:47-48`), so it is not a proposition,
and LEM's `dne` does not apply. This is the measurement `[LJ-1.107]`
already recorded, in the same words: the non-initial case needs an
injection the truncated least-of witness cannot give
(`archive/dev/LJ-dispatch-index.md:183`).

**4. THIS IS THE SAME WALL, ONE GRAIN DOWN, NOT A NEW OBJECT.**
`[LJ-1.605]` measured that the untruncation of the BAND supply is the
square law at the band
(`agents/tasks/LJ-1-605/review-of-uniform-pairing.md:96-98`). The residue
here is strictly weaker than that object: it asks at every ordinal, one
at a time, with no uniformity and no coherence over the band. The probe
separates the two grains exactly: the band object is `Band`
(`agents/tasks/LJ-1-618/Probe618.agda:122-123`), the one-α object is
`Obligation` (`:90-91`), and the gap between the tree and the one-α
object is `Inj-extract` alone, because
`Inj-extract → Obligation` is proved (`:210-211`).

## WHY A STOP AND NOT A RESTRUCTURE

The heap-wall clause does not apply: nothing here walls. The probe is
green at 1.56 s, 1.52 s and 1.50 s under a 300 s cap
(`agents/tasks/LJ-1-618/runs/final-1.out` to `final-3.out`), with the
floor measured first at 7.01 s (`runs/floor-1.out`). The stop is a
SPECIFICATION stop: the ingredient the site needs is a choice
principle, per site, and the campaign has measured twice that the tree
does not carry it (`archive/dev/LJ-dispatch-index.md:183`, `:190`) and
once that at the band grain it IS the square law, whose dispatch is
forbidden (`agents/tasks/LJ-1-593/review-of-square-coded.md:82-84`).
Inventing it here would be the fifth arrival, at one grain lower.

## WHAT THE MATHEMATICIAN SHOULD READ OFF THIS

- `[LJ-1.617]`'s question, whether the bill ever needs the wider grain,
  now has a floor under it: even the NARROW grain, one α, does not
  close without a per-site untruncation. The two grains differ by
  uniformity only, and the missing ingredient is the same at both.
- The class-pred formula remains one ingredient short of (iii) at the
  spend grain: `[LJ-1.613]`'s (i) and (ii) are internal, (iv) and (v)
  are paid, and (iii) at one α is this residue.
- The residue `Inj-extract` is now a named type with a proved
  consequence. If the owner funds it, the funding is for the
  untruncation itself, and the site grain is the cheapest place it can
  be asked.

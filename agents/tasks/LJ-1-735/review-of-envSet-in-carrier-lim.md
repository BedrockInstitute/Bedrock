# Review of `envSet-in-carrier-lim`

**GO.** The corrected target the 730 review named under `closedω γ`
is TRUE, and the strongest evidence a truth check can have is
recorded here: the target is INHABITED, machine-checked, at
`agents/tasks/LJ-1-735/Probe735.agda::envSet-in-carrier-lim`
(Probe735.agda:65, term at :71-124), green at EXIT=0
(`agents/tasks/LJ-1-735/runs/p-6.out`, 1.74 s, 401,096,704 B peak),
under `--cubical --safe --guardedness`, no postulate and no hole.

## 1. The target

The brief's obligation, verbatim up to the membership glyph (the
hypothesis reads at the V structure, whose `∈ˢ` IS the raw membership;
the conclusion reads at the L structure, whose `∈ˢ` is
`fst a ∈ˢᵥ fst b`, so facts cross without a conversion):

    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    → ⟨ ω ∈ˢᵥ γ ⟩
    → (A : S) → ⟨ fst A ∈ Lset γ ⟩
    → (n : ℕ)
    → ⟨ envSet A n ∈ˢ LsetS γ oγ ⟩

## 2. The truth check

**TRUE at the corrected scope, and for a reason stronger than the
route.** Three facts, each checkable:

1. The 730 counterexample does not reach here. The refutation of
   `envSet-in-carrier-stage` (730) ran at `γ = sucV (sucV ω)`, which
   satisfies `ω ∈ˢ γ` but NOT `closedω γ`: closure demands
   `+ω ω ∈ˢ γ`, and `+ω ω` strictly dominates every finite iterate of
   `ω`, so it cannot sit inside `ω+2`. The old scope's failure site
   is strictly below this scope.
2. At the corrected scope the bound has REAL HEADROOM, not a lucky
   margin: the landed bound places `envSet A n` at
   `sucIter 4 (+ω m)` for any `m ∈ˢ γ` carrying `ω` and the carrier's
   one-up stage (`envSetNumeral∈`, `src/L/Coding/Key.lagda.md:486`),
   and `closedω` absorbs ANY fixed iterate, so the 4 is not tight and
   no consumer choice of `n` moves it.
3. The hypothesis `ω ∈ˢ γ` is still needed and still used: it pins
   `m := ω` in the two upper trichotomy cases and enters the merge in
   the lower one. A scope that dropped it while keeping `closedω`
   would still be true for the limit ordinal `ω`-containing `γ` in
   most sites, but the probe never claims that weaker form.

## 3. What would reopen it

- The scope is exactly `closedω γ` with `ω ∈ˢ γ`. At a successor `γ`
  with only a slack hypothesis, the 730 counterexample class returns;
  any narrower scope (a fixed iterate of the carrier's stage, or a
  non-closed successor) must be re-priced, not analogized.
- The proof absorbs iterate 4 at `+ω m`. No claim is made for
  `envSet A n` sitting BELOW `sucIter 4 (+ω m)`; a consumer needing a
  tighter iterate must price it separately.
- The D-10 residue the 730 review recorded ("price the truth before
  the proof") is hereby DISCHARGED for the corrected target: the
  corrected target is true and inhabited. The other two scopes it
  named (a limit `γ ≥ ω`, a per-instance rank hypothesis) remain
  unpriced.

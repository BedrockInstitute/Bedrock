# Three orphaned blocks of the soundness chapter (retired 2026-09-06)

From `src/L/Coding/Sound.lagda.md`.  `module TermAgree` was the husk of
the two-term-readers section: three private abbreviations for the code,
the environment and the value slot, with nothing built on them, and an
empty `private` block after it where the agreement statement had been.
`module AmbientHoldsGen` was the generic-arity twin of
`module AmbientHolds`, forwarding to `Generic.Holds`.
`module NumeralFromGeneric` was an empty module.

THE TREE HAD NO CONSUMER FOR ANY OF THEM.  The one importer of
`L.Coding.Sound` is `src/L/Coding/Tower.lagda.md:22`, which takes
`module Ambient` and `module AmbientHolds` and nothing else; both stay
in the live file.

With these gone the chapter's remaining code names only `numL`,
`envSetAt`, `envOverAt`, `envOverAt-transport`, `extAt-out`, `extAt-in`,
`extAt-in-both`, `envSet`, `envSet-in`, `envSet-out`, `envS`, `envOver`,
`module Recover`, `#_` and `_∈_`, so the imports of `FOL.Syntax`,
`V.Coding`, `L.Axioms.Numerals`, `L.Coding.Sat`, `L.Coding.Table`,
`Cubical.Foundations.HLevels`, `Cubical.Functions.Logic`,
`Cubical.Data.Empty`, `Cubical.Data.Unit`, `Cubical.Data.Nat`,
`Cubical.Data.FinData`, `Cubical.Data.Sum` and `subst2` were dropped
with them.

```agda
module TermAgree {k : ℕ} (γ : S ^ k) (ti ei vi : Fin k) where
  private
    Tc = fst (lookup ti γ)
    Ev = fst (lookup ei γ)
    Vl = fst (lookup vi γ)

module AmbientHoldsGen (B ar : S) {k : ℕ} (γ : S ^ k) (Ei di bi : Fin k)
  (qE : fst (lookup Ei γ) ≡ fst (Generic.envSetGen B ar))
  (qd : fst (lookup di γ) ≡ fst ar) (qb : fst (lookup bi γ) ≡ fst B)
  where

  holds : ⟨ γ ⊨ envSetAt Ei di bi ⟩
  holds = H.holds
    where
    module G = Generic B ar
    module H = G.Holds γ Ei di bi qE qd qb

module NumeralFromGeneric (B : S) (n : ℕ) where
```

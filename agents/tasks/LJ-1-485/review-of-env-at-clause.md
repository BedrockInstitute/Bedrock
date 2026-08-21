# Review of `env-at-clause`

`ω∈γ` has no source at the clause telescope. This
file is the obstruction, for the branch `stop-stated`.
The supplier was not applied. The work names the second
unsourced hypothesis. I did not gate `ω∈γ`. I did not
gate slot 0.

## THE STATEMENT

The brief names:

```
env-at-clause :
    (ya yc b a ar c : S)
  → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
  → ⟨ fst ya ∈ fst K ⟩ → ⟨ fst yc ∈ fst K ⟩ → ⟨ fst ar ∈ fst K ⟩
  → Σ S (λ E → ⟨ fst E ∈ fst K ⟩
      × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 {11 + n} zero K' ⟩)
```

`someEnvDef`'s conclusion with the numeral truncation added,
at `[LJ-1.457]`'s layout with the carrier in slot 0. Exact
slot indices from `src/L/Condensation/LowerAgree.lagda.md:52-58`.
The frame is the `[LJ-1.473]` pad (`Probe473.agda:61-67`).
Predecessor `[LJ-1.483]` is a critic-upheld STOP
(`agents/tasks/LJ-1-483/lj-1.483-report.md:90`). Predecessor
`[LJ-1.473]` is NO-GO on the ungated body and GO on slot 0
(`agents/tasks/LJ-1-473/lj-1.473-report.md:114`). Predecessor
`[LJ-1.467]` is NO-GO on `ω∈γ`
(`agents/tasks/LJ-1-467/lj-1.467-report.md:105`).

The body was to come from `SupplyEnv.someEnv`
(`src/L/Coding/EnvSupply.lagda.md:417-424`), with `arNum`
taken as a hypothesis. The brief forbids gating `ω∈γ` or
slot 0 silently.

I did not write `env-at-clause`. The type forms at `n = 9`.
The body has no source.

## D-10

`[LJ-1.473]` named three supplier inputs
(`lj-1.473-report.md:76-99`):

1. The numeral truncation. The clause binds it as `arNum` at
   `src/L/Condensation.lagda.md:3509`. This brief hypothesises
   it.
2. The carrier in slot 0. The `[LJ-1.473]` filler puts
   `LsetS gam ordγ` there (`Probe473.agda:61-64`). This brief
   rebuilds that filler.
3. `ω∈γ : ⟨ ω ∈ sucV gam ⟩`. `SupplyEnv` takes it
   (`EnvSupply.lagda.md:111`). `KValue` does not
   (`Condensation.lagda.md:7380-7384`). `someEnvDef` does not
   (`LowerAgree.lagda.md:52-58`). `PropAgree` does not
   (`Condensation.lagda.md:3285-3320`). The clause at
   `:3505-3515` does not bind it.

The brief hypothesises (1). (2) has a source. (3) does not.
The brief says: if either of the other two has no source at
this telescope, name it and STOP.

The brief writes `⟨ ω ∈ˢ fst gam ⟩`. That type does not form
(`ZFStructure.lagda.md:48-50`, `Condensation.lagda.md:7384`).
The predecessor type is `⟨ ω ∈ sucV gam ⟩`.

## W3

GO on the emptiness. NO-GO on the source
`⟨ ω ∈ sucV gam ⟩` with no binders.

```
carrier-at-instance :
    fst (lookup zero Inst.Kenv') ≡ fst (LsetS ∅ ∅-ord)

omega-source : ⟨ ω ∈ sucV ∅ ⟩ → Empty.⊥
```

at `Probe485.agda:115-118` and `:102-104`, in
`module Countermodel`. `module Inst = W3` at `:100`
at `lam = ω`, `gam = ∅` is a legal instance of this layout.
Slot 0 is still the carrier there. That filler does not
produce `ω ∈ sucV ∅`.

Typechecked ALONE, obligation omitted, caliber
`GHCRTS="-A64m -I0 -M8g"`. See the report for the three rechecks.

## THE MISSING SOURCE, AS A TYPE

```
omega-in-gamma :
    (lam : V ℓ) (ordλ : IsOrd lam)
    (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
    (∅∈λ : ⟨ ∅ ∈ lam ⟩)
    (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  → ⟨ ω ∈ sucV gam ⟩
```

`omega-source` refutes every inhabitant of this type at the
legal instance `lam = ω`, `gam = ∅`. I did not inhabit it.
I did not add it to `env-at-clause`. I did not add it to
`someEnvDef`. I did not apply `SupplyEnv.someEnv`.

## WHAT WAS NOT DONE

No `env-at-clause` term was written. No hole. No `TFacts`
record. The other 27 fields were not inhabited. No
postulate. The transport from the four-slot frame onto
`envHypB2` was not attempted: `SupplyEnv` cannot be opened
at this frame, and the brief stops there.

## CORRECTED TARGET

The clause binds the truncation. It does not bind `ω∈γ`.
Reading the field as inhabitable at `PropAgree.back:3515`
from `SupplyEnv.someEnv` plus `arNum` is still missing the
module hypothesis `ω∈γ`. The clause site is not sufficient.
The field's neighbourhood needs restating.

A next brief that wants the body must take `ω∈γ` as well, or
name a supplier that does not take it, or name a frame that
excludes `lam = ω` and `gam = ∅`. Do not fund it against this
W3 price. Re-measure it.

`TwelveAgree.AbstractFrame` takes `TFacts` as a whole
(`TwelveAgree.lagda.md:337-343`). It cannot reach a local
at `PropAgree.back:3515`. Inlining `SupplyEnv.someEnv` there
still needs `ω∈γ` in scope at `PropAgree`, which does not
have it (`Condensation.lagda.md:3285-3320`).

Do not inhabit `TFacts.someEnv` at this pad. That field is
`someEnvDef` with no truncation and no `ω∈γ`
(`TwelveAgree.lagda.md:289`). `[LJ-1.467]` refuted `ω∈γ` at
a legal instance. `[LJ-1.473]` named the missing truncation.
`[LJ-1.480]` refuted the truncation from K-membership.
`[LJ-1.483]` named the missing domain of `codesK` at the
field. This return names the missing `ω∈γ` at the clause.

## C-42

The measurement is this one site: `ω∈γ` at
`EnvSupply.lagda.md:111`, against the clause at
`Condensation.lagda.md:3505-3515` and against `someEnvDef`
at `LowerAgree.lagda.md:52-58`. It says that input has no
source at this frame. It does not measure how many other
sites carry the same missing hypothesis.

See the report for the counts.

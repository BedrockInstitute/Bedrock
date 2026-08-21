# Review of `someEnv-gated`

The second of the three supplier hypotheses has no source at this
frame. This file is the obstruction, for the branch `no-go-stated`.
The transport was not attempted.

## THE STATEMENT

The brief names:

```
someEnv-gated : someEnvDef {9} iK' Kenv'
```

It is `Probe473.agda:92-99`. `someEnvDef` is
`src/L/Condensation/LowerAgree.lagda.md:52-58`. `iK'` and `Kenv'`
are the `[LJ-1.457]` layout with the carrier in slot 0
(`Probe473.agda:61-64`, `:81-90`). Predecessor `[LJ-1.457]` is GO
(`agents/tasks/LJ-1-457/lj-1.457-report.md:87`). Predecessor `[LJ-1.467]` is NO-GO,
critic-upheld (`agents/tasks/LJ-1-467/lj-1.467-report.md:105`,
`agents/tasks/LJ-1-467/review-of-LJ-1-467-1.md:203`). The type forms at `n = 9`. Layout
is not the break. Slot 0 is not the break: W3 inhabits
`slot-zero` by `refl` (`Probe473.agda:69-70`).

The body was to come from `SupplyEnv.someEnv`
(`src/L/Coding/EnvSupply.lagda.md:417-424`). That supplier takes
`∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` (`EnvSupply.lagda.md:418`).
`someEnvDef` does not (`LowerAgree.lagda.md:52-58`). The brief
forbids gating that hypothesis.

The module hypothesis is `ω∈γ : ⟨ ω ∈ sucV gam ⟩`
(`EnvSupply.lagda.md:111`, `Probe473.agda:97`). The brief wrote
`⟨ ω ∈ˢ fst gam ⟩`. That type does not form
(`src/FOL/ZFStructure.lagda.md:48-50`: `_∈ˢ_` is `S → S → Ω`;
`gam` is `V ℓ` at `Condensation.lagda.md:7384`). Audit F1: take
the type the predecessor delivered
(`dev/pod/audit-2026-08-20.md:34-41`). I took `⟨ ω ∈ sucV gam ⟩`.

## D-10

`someEnvDef {9}` wants `K : Fin (5 + 9)` and `γ : S ^ (11 + 9)`.
The probe delivers `iK' : Fin (5 + 9)` and `Kenv' : Vec S (11 + 9)`.
They meet. See `lj-1.473-report.md` section D-10.

Three hypotheses the supplier takes that the target does not give,
named by `[LJ-1.467]` (`agents/tasks/LJ-1-467/lj-1.467-report.md:90-97`):

1. `ω∈γ`. Source: stated module hypothesis at
   `Probe473.agda:97`. Type from the predecessor, not from the
   brief.
2. Numeral truncation `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁`.
   `SupplyEnv.someEnv` takes it (`EnvSupply.lagda.md:418`).
   `someEnvDef` does not (`LowerAgree.lagda.md:52-58`). No
   source. Measured below.
3. Carrier in slot 0. Source: the filler
   `LsetS gam ordγ` at `Probe473.agda:62`. W3 inhabits
   `slot-zero` (`:69-70`).

The brief says: if either of the other two has no source, STOP.
The second is enough. The brief forbids gating it.

## W3

GO. `slot-zero` is definitional.

```
slot-zero : fst (lookup zero Kenv') ≡ fst (LsetS gam ordγ)
slot-zero = refl
```

at `Probe473.agda:69-70`, inside `module W3` at a real `KValue`
frame. `Kenv'` puts `LsetS gam ordγ` in slot 0 and keeps five
dummy `numeralL 0` fillers, then `Kenv` (`:61-64`).

Typechecked ALONE, obligation omitted, caliber
`GHCRTS="-A64m -I0 -M8g"`. See the report for the three rechecks.

`suc^6` reads `Kenv`, so changing slot 0 does not touch the
24-field transfer of `[LJ-1.457]`. That is why the layout and
the supplier can share this frame on slot 0. They still cannot
share it on the truncation.

## THE MISSING SOURCE, AS A TYPE

The brief forbids gating the truncation. The supplier's body
uses it at `EK` and at `envInK₀` (`EnvSupply.lagda.md:433`,
`:439`). The type that has no source is:

```
truncation :
    (ar : S)
  → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK'))))))
                           (Kenv' lam ordλ succλ ∅∈λ gam ordγ γ∈λ)) ⟩
  → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
```

`someEnvDef` does not take this. Sibling `TFacts` fields do
(e.g. `envK-mem` at `TwelveAgree.lagda.md:186-187`). `TFacts.someEnv`
does not (`:289`). I did not inhabit `truncation`. I did not
add it to `someEnv-gated`. I did not apply `SupplyEnv.someEnv`.

## WHAT WAS NOT DONE

No numeral hypothesis was added. No filler beyond slot 0 was
rewritten. No `TFacts` record was written. The other 27 fields
were not inhabited. No postulate. The transport from the
four-slot frame onto `envHypB2` was not attempted: the
truncation has no source, and the brief stops there.

The obligation `someEnv-gated` has a hole
(`Probe473.agda:99`). The body is not `SupplyEnv.someEnv`.

## CORRECTED TARGET

W3 is GO: the carrier sits in slot 0. `ω∈γ` is stated. The
delivered supplier still cannot be applied, because
`someEnvDef` does not give the truncation.

A next brief that wants that body must give the truncation a
source, or it must inhabit a type that takes the truncation.
`[LJ-1.463]` named the fully gated type
(`agents/tasks/LJ-1-463/review-of-someEnv-at-K.md:97-118`). This brief gated one of
the three and put the carrier in the frame. Gating the last
one is the remaining shape. Do not fund it against this W3
price. Re-measure it.

Do not inhabit `TFacts.someEnv` at this pad. That field is
`someEnvDef` with no `ω∈γ` and no truncation
(`TwelveAgree.lagda.md:289`). `[LJ-1.467]` refuted the ungated
`ω∈γ`. This return names the missing truncation. The field as
declared is not this gated type.

## C-42

The measurement is this one site: the truncation argument of
`SupplyEnv.someEnv` at `EnvSupply.lagda.md:418`, against
`someEnvDef` at `LowerAgree.lagda.md:52-58`. It says that
argument has no source at this frame. It does not measure how
many other sites carry the same missing truncation.

COUNT of `someEnvDef` in `src/`: **3**.
`LowerAgree.lagda.md:52` (the type), `:218` (the LFacts field),
`TwelveAgree.lagda.md:289` (the TFacts field). None of the three
takes the truncation. None takes `ω∈γ`.

COUNT of `SupplyEnv.someEnv` in `src/`: **1**,
`EnvSupply.lagda.md:417`. It takes `ω∈γ` at `:111` and the
truncation at `:418`.

COUNT of `module KValue` in `src/`: **1**,
`Condensation.lagda.md:7380`. It takes neither.

A cure of the truncation at this site is not a measured cure
of `LFacts.someEnv` or of `TFacts.someEnv`. It is not a
measured cure of the 4-to-27 transport onto `envHypB2`.

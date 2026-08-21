# Review of `someEnv-numeral`

The first of the three supplier hypotheses has no source at this
frame. This file is the obstruction, for the branch `no-go-stated`.
The transport was not attempted.

## THE STATEMENT

The brief names:

```
someEnv-numeral : someEnvDef {9} iK' Kenv'
```

It is `Probe467.agda:127-133`. `someEnvDef` is
`src/L/Condensation/LowerAgree.lagda.md:52-58`. `iK'` and `Kenv'`
are the frame `[LJ-1.457]` delivered
(`Probe457.agda:52-55`, `:74-75`). Predecessor `[LJ-1.457]` is GO
(`lj-1.457-report.md:87`). Predecessor `[LJ-1.463]` is NO-GO
(`lj-1.463-report.md:61`). The type forms at `n = 9`. Layout is
not the break.

The body was to come from `SupplyEnv.someEnv`
(`src/L/Coding/EnvSupply.lagda.md:417-424`). That supplier's
module takes `ω∈γ : ⟨ ω ∈ sucV gam ⟩`
(`EnvSupply.lagda.md:111`). `KValue` does not
(`Condensation.lagda.md:7380-7383`). The brief forbids a new
hypothesis.

## D-10

`someEnvDef {9}` wants `K : Fin (5 + 9)` and `γ : S ^ (11 + 9)`.
The probe delivers `iK' : Fin (5 + 9)` and `Kenv' : Vec S (11 + 9)`.
They meet. See `lj-1.467-report.md` section D-10.

Three hypotheses the supplier takes that the target does not give,
named by `[LJ-1.463]` (`lj-1.463-report.md:310-316`):

1. `ω∈γ`. No source. Measured below.
2. Numeral truncation `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁`.
   `SupplyEnv.someEnv` takes it (`EnvSupply.lagda.md:418`).
   `someEnvDef` does not (`LowerAgree.lagda.md:52-58`).
3. Carrier in slot 0. The delivered `Kenv'` puts dummy
   `numeralL 0` there (`Probe457.agda:53-54`). The supplier
   builds at `B₀ = LsetS gam` (`EnvSupply.lagda.md:124-125`).

The brief says: if one of the three has no source, STOP. The
first is enough.

## W3

`KValue` is a limit bound and a stage below it
(`Condensation.lagda.md:7380-7386`). That telescope is inhabited
at `lam = ω`, `gam = ∅`:

```
module Inst = KValue ω ω-ord succω ∅∈ω ∅ ∅-ord ∅∈ω
```

at `Probe467.agda:95`. `succω` is successor-closure of `ω`
(`:89-92`). `∅∈ω` is `#∈ω 0` (`:86-87`).

At that instance the supplier's type is `⟨ ω ∈ sucV ∅ ⟩`. W3
inhabits the negation:

```
supplies : ⟨ ω ∈ sucV ∅ ⟩ → Empty.⊥
```

at `Probe467.agda:104-107` (`runs/w3-4.out`, exit 0, 2.60 s,
caliber `GHCRTS="-A64m -I0 -M8g"`). So `ω∈γ` is not a consequence
of the frame. It is empty at a legal instance.

`[LJ-1.252]` measured the same emptiness for `ω ∈ lam` at
`lam = ω` (`ProbeLJ1252A.agda:51-65`). This return re-measures
at `KValue`'s own site, with `gam = ∅`. It does not transfer
that probe by analogy.

## WHAT WAS NOT DONE

No numeral hypothesis was added. No `ω∈γ` was added. No filler
was rewritten. No `TFacts` record was written. The other 27
fields were not inhabited. No postulate. The transport from the
four-slot frame onto `envHypB2` was not attempted: the first
hypothesis has no source, and the brief stops there.

The obligation `someEnv-numeral` has a hole
(`Probe467.agda:133`). The body is not `SupplyEnv.someEnv`.

## CORRECTED TARGET

The delivered supplier cannot be applied at `[LJ-1.457]`'s
frame. A next brief that wants that body must give the three
hypotheses a source. Two shapes, not both in one brief:

1. Thread `ω∈γ`, the numeral truncation, and the carrier in
   slot 0 into the frame. That is the gated type
   `[LJ-1.463]` named
   (`review-of-someEnv-at-K.md:97-118`). This brief forbade
   adding those hypotheses, so that type was not inhabited
   here.
2. Derive `ω∈γ` from a hypothesis the consumer already has.
   `[LJ-1.252]` inhabits `⟨ ω ∈ sucV α ⟩` from `α∉ω`
   (`ProbeLJ1252A.agda:93-99`). `KValue` does not carry
   `α∉ω`. `BoundedSubsetAt` does
   (`src/L/BoundedSubset.lagda.md:1385-1387`).

Do not fund either against this 2.21 s. Re-measure it.

## C-42

The measurement is this one site: `Countermodel.supplies` at
`Probe467.agda:104`. It says `⟨ ω ∈ sucV gam ⟩` is empty at a
legal `KValue` instance. It does not measure how many other
sites carry the same missing `ω∈γ`.

COUNT of `someEnvDef` in `src/`: **3**.
`LowerAgree.lagda.md:52` (the type), `:218` (the LFacts field),
`TwelveAgree.lagda.md:289` (the TFacts field). None of the three
takes `ω∈γ`.

COUNT of `SupplyEnv.someEnv` in `src/`: **1**,
`EnvSupply.lagda.md:417`. It takes `ω∈γ` at `:111`.

COUNT of `module KValue` in `src/`: **1**,
`Condensation.lagda.md:7380`. It does not take `ω∈γ`.

A cure of `ω∈γ` at this site is not a measured cure of
`LFacts.someEnv` or of `TFacts.someEnv`. It is not a measured
cure of the numeral truncation or of the dummy in slot 0.

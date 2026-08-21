# Review of `someEnv-at-K`

The membership half does not close. This file is the obstruction, for
the branch `no-go-stated`. Satisfaction was not attempted.

## THE STATEMENT

The brief names:

```
someEnv-at-K : someEnvDef {9} iK' Kenv'
```

It is `Probe463.agda:107-113`. `someEnvDef` is
`src/L/Condensation/LowerAgree.lagda.md:52-58`. `iK'` and `Kenv'`
are the frame `[LJ-1.457]` delivered
(`Probe457.agda:52-55`, `:74-75`). Predecessor `[LJ-1.457]` is GO
(`lj-1.457-report.md:87`). The type forms at `n = 9`. Layout is
not the break.

W3 built THE environment set and asked it to lie in the bound:

```
E = Generic.envSetGen B ar
EK = KFacts.numK0 facts
```

at `Probe463.agda:77-87`, inside `module W3` at a real `KValue`
frame. `B` is slot 0 of `Kenv'`, the first dummy filler.

Agda reports `[UnequalTerms]` at `Probe463.agda:87`
(`runs/w3-1.out`, exit 42, 2.16 s, caliber
`GHCRTS="-A64m -I0 -M8g"`):

```
fst (numeralL 0) != fst G.envSetGen of type V ℓ
when checking that the expression KFacts.numK0 facts has type
⟨ fst E ∈ fst bound ⟩
```

The construction exists as a term of type `S`. The bound's
delivered closure facts do not put it in `K`.

## D-10

`someEnvDef {9}` wants `K : Fin (5 + 9)` and `γ : S ^ (11 + 9)`.
The probe delivers `iK' : Fin (5 + 9)` and `Kenv' : Vec S (11 + 9)`.
They meet. See `lj-1.463-report.md` section D-10.

The membership half is the unrestricted `envSetK`. `[LJ-1.172]`
named that field FALSE at `K = Lset lam` for the `lam` that
`HullStage` gives (`lj-1.172-report.md:709-713`). `[LJ-1.173]`
restricted the TFacts field to a numeral arity
(`TwelveAgree.lagda.md:306-310`). The supplier
`SupplyEnv.envSetK` (`EnvSupply.lagda.md:140-142`) takes
`fst ar ≡ # n` and the module hypothesis `ω∈γ`
(`EnvSupply.lagda.md:111`). `SupplyEnv.someEnv`
(`EnvSupply.lagda.md:417-424`) takes the same numeral
truncation. `someEnvDef` takes none of these. `KValue` does not
carry `ω∈γ` (`Condensation.lagda.md:7380-7383`). The brief
forbids a new hypothesis.

`KFacts` at `Condensation.lagda.md:7413-7425` supplies `tagEq`,
`numK`, `innerK`, `innerPairK`, `pairK`, `carrierK`, `arityK`.
It does not supply `envSetK`. `numK0` is membership of
`numeralL 0`. It is not membership of `envSetGen`.

Slot 0 of the delivered `Kenv'` is dummy `numeralL 0`
(`Probe457.agda:53-54`). `envHypB2 {11 + n} zero` reads that
slot as `B` (`LowerAgree.lagda.md:58` against
`Condensation.lagda.md:654-658`). The supplier builds the
environment set at the carrier `B₀ = LsetS gam`
(`EnvSupply.lagda.md:124-125`, `:427`). The dummy is not the
carrier. A next brief that wants the And/Or `B` must put the
carrier in slot 0. It must not reuse this dummy.

## WHAT WAS NOT DONE

No numeral hypothesis was added. No `ω∈γ` was added. No filler
was rewritten. No `TFacts` record was written. The other 27
fields were not inhabited. No postulate. Satisfaction of
`envHypB2` was not attempted: the membership half did not close,
and the brief stops there.

`[LJ-1.113]` named `someEnv` NEEDS NEW CONTENT
(`lj-1.113-report.md:52`) and named it the widest unmeasured
term (`:147-152`). It did not name the statement FALSE. This
NO-GO is the membership of `envSetGen` at the re-laid-out
frame, not a repeat of that classification.

## CORRECTED TARGET

Gate the arity and name the two supplies the delivered
constructor already uses. Put the carrier in slot 0:

```
KenvB :
    (lam : V ℓ) (ordλ : IsOrd lam)
    (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
    (∅∈λ : ⟨ ∅ ∈ lam ⟩)
    (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  → Vec S (11 + 9)
KenvB lam ordλ succλ ∅∈λ gam ordγ γ∈λ =
  let open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ
  in  LsetS gam ordγ ∷ numeralL 0 ∷ numeralL 0
    ∷ numeralL 0 ∷ numeralL 0 ∷ numeralL 0
    ∷ Kenv

someEnv-numeral :
    (lam : V ℓ) (ordλ : IsOrd lam)
    (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
    (∅∈λ : ⟨ ∅ ∈ lam ⟩)
    (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
    (ω∈γ : ⟨ ω ∈ sucV gam ⟩)
  → (ya yc b a ar c : S)
  → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
  → someEnvDef {9} iK' (KenvB lam ordλ succλ ∅∈λ gam ordγ γ∈λ)
```

The body is `SupplyEnv.someEnv` at `EnvSupply.lagda.md:425-444`,
transported from its 4-slot frame `E ∷ ar ∷ B₀ ∷ level ∷ []` onto
`envHypB2` at the padded environment. This file names that type.
It does not inhabit it.

## C-42

The measurement is this one site: `W3.env-in-K` at
`Probe463.agda:87`. It says `KFacts.numK0` does not inhabit
`Generic.envSetGen ∈ bound`. It does not measure how many other
sites carry the same missing numeral.

COUNT of `someEnvDef` in `src/`: **3**.
`LowerAgree.lagda.md:52` (the type), `:218` (the LFacts field),
`TwelveAgree.lagda.md:289` (the TFacts field). None of the three
gates the arity.

COUNT of numeral-gated `envSetK` in `src/`: **2**.
`TwelveAgree.lagda.md:306` (the TFacts field),
`EnvSupply.lagda.md:140` (the supplier). Both take
`fst ar ≡ # n`.

COUNT of `SupplyEnv.someEnv` in `src/`: **1**,
`EnvSupply.lagda.md:417`. It takes the truncation and `ω∈γ`.

A cure at `someEnv-at-K` alone does not close the two ungated
fields. The numeral gate above is the adapter at this one type.
It is not a measured cure of `LFacts.someEnv` or of
`TFacts.someEnv`.

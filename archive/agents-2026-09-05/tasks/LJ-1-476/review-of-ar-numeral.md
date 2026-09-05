# Review of `ar-numeral`

The numeral truncation has no source at this frame, and the
implication from membership in `K` is FALSE at a legal instance.
This file is the obstruction, for the branch `no-go-stated`.
The transport was not attempted.

## THE STATEMENT

The brief names:

```
ar-numeral :
    (ar : S) → ⟨ fst ar ∈ fst K ⟩ → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
```

It is `Probe476.agda:133-137`. `K` is the bound slot of
`[LJ-1.457]`'s frame, `lookup iK Kenv`, which is `LsetS lam`
(`src/L/Condensation.lagda.md:7387-7397`). The probe instantiates
that frame at `lam = ω`, `gam = ∅`, the legal instance
`[LJ-1.467]` delivered (`Probe467.agda:83-95`). Predecessor
`[LJ-1.457]` is GO (`lj-1.457-report.md:87`). Predecessor
`[LJ-1.473]` is NO-GO, critic-upheld
(`lj-1.473-report.md:114`, `review-of-LJ-1-473-1.md:179`).
Predecessor `[LJ-1.467]` is NO-GO, critic-upheld
(`lj-1.467-report.md:105`). I did not inhabit a predecessor
NO-GO.

`someEnvDef` does not take this truncation
(`LowerAgree.lagda.md:52-58`). `SupplyEnv.someEnv` does
(`EnvSupply.lagda.md:418`). The brief forbids a new hypothesis.

## D-10

`K` is a constructible level. Its members are not all numerals.
W3 exhibits one member that is a Kuratowski pair. The refutation
shows that pair is not a numeral. The implication is empty at
that member. See `lj-1.476-report.md` section D-10.

## W3

`KValue` is a limit bound and a stage below it
(`Condensation.lagda.md:7380-7386`). That telescope is inhabited
at `lam = ω`, `gam = ∅`:

```
module Inst = KValue ω ω-ord succω ∅∈ω ∅ ∅-ord ∅∈ω
```

at `Probe476.agda:63`. `K = lookup Inst.iK Inst.Kenv` (`:67-68`).

W3 inhabits a member of that slot:

```
witness : Σ[ ar ∈ S ] ⟨ fst ar ∈ fst K ⟩
witness = prʟ (numeralL 0) (numeralL 0)
        , pairK (numeralL 0) (numeralL 0) numK0 numK0
```

at `Probe476.agda:72-74` (`runs/w3-4.out`, exit 0, median
**1.85 s** on three forced rechecks, caliber
`GHCRTS="-A64m -I0 -M8g"`). The member is the L-pair of two
copies of `numeralL 0`. `pairK` is `KValue.facts`
(`Condensation.lagda.md:7423`).

## THE REFUTATION

At that witness the truncation is empty:

```
ar-numeral-refute :
    (∥ Σ[ n ∈ ℕ ] (fst (fst witness) ≡ # n) ∥₁) → Empty.⊥
```

at `Probe476.agda:121-124`. The body is `pr00≢#`
(`:98-113`): a Kuratowski pair is not an ordinal, because
transitivity of `# n` (`numeral-ord`, `L.Ordinal.lagda.md:244`)
puts `# 0` inside the pair, so `# 0` equals `⁅ # 0 ⁆s` or
`⁅ # 0 , # 0 ⁆`, so `# 0 ∈ # 0`, which `∈-irrefl` forbids
(`V.Hierarchy.lagda.md:155`). Classification is `pairing-ax`
only (`Condensation.lagda.md:2827-2844`). No nested brace goal.

The named obligation is a hole at `Probe476.agda:137`
(`runs/full-4.out`, exit 42, `[UnsolvedInteractionMetas]`,
the hole the only error). I did not inhabit `ar-numeral`.
I did not add a hypothesis to make it true.

## WHAT WAS NOT DONE

- I did not inhabit `ar-numeral`.
- I did not transport `SupplyEnv.someEnv`.
- I did not build `someEnv-gated`.
- I did not postulate.
- I did not write in `src/`.
- I did not choose between the two readings in
  `lj-1.476-report.md` section WHAT THE FIELD MUST BECOME.

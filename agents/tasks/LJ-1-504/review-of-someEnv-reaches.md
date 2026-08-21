# review-of-someEnv-reaches: the obligation is NOT inhabited, and the gap is a type

slot: `coder`. This file is how the slot states a stop
(`dev/pod/instructions/coder.md`, the module-hypothesis clause). It does
not close the task: the critic reads it.

## THE STOP, IN ONE SENTENCE

`TFacts.someEnv` is **NOT** reachable from `SupplyEnv.someEnv` as both
are written today, and the whole remaining distance is ONE hypothesis:
`∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁`, which the supplier asks at
`src/L/Coding/EnvSupply.lagda.md:418` and which `someEnvDef` does not
carry at `src/L/Condensation/LowerAgree.lagda.md:52-58`.

## THE GAP, AS A TYPE

`agents/tasks/LJ-1-504/Probe504.agda:120-126`.

```agda
someEnvDef-gap : Type (ℓ-suc ℓ)
someEnvDef-gap =
    (g1 g2 g3 g4 g5 : S) (ya yc b a ar c : S)
  → ⟨ fst ya ∈ fst (lookup K6 (gam' g1 g2 g3 g4 g5)) ⟩
  → ⟨ fst yc ∈ fst (lookup K6 (gam' g1 g2 g3 g4 g5)) ⟩
  → ⟨ fst ar ∈ fst (lookup K6 (gam' g1 g2 g3 g4 g5)) ⟩
  → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
```

`lookup K6 (gam' g1 g2 g3 g4 g5)` is `LsetS lam ordλ`
(`agents/tasks/LJ-1-504/Probe504.agda:91-92` against
`src/L/Condensation.lagda.md:7389-7390` and `:7397`), so the type reads: **at
`KValue`'s bound, a member of `K` is a numeral.**

## THE DISTANCE IS EXACTLY THAT TYPE, AND AGDA CHECKED IT

`gap-suffices` (`agents/tasks/LJ-1-504/Probe504.agda:133-138`) is

```agda
gap-suffices : someEnvDef-gap
             → ((g1 g2 g3 g4 g5 : S) → someEnvDef {9} KV.iK (gam' g1 g2 g3 g4 g5))
```

and it typechecks (exit 0, `runs/full-1.out`). Its body is
`someEnv-gated` applied to the gap and nothing else. So `someEnvDef-gap`
is SUFFICIENT, and the two other differences the brief named are closed.

## THE GAP AS WRITTEN IS NOT A ROUTE

**I did not machine-check this and I do not report it as measured.**
`someEnvDef-gap` says every member of `Lset lam` that reaches the `ar`
slot is a numeral. `SupplyEnv` itself puts non-numerals into that same
bound: `B₀∈σ` (`src/L/Coding/EnvSupply.lagda.md:127`) places
`fst B₀ = Lset gam` inside the tower under the bound. So the gap is not
a lemma to prove. **It is the measurement of what the record's field
type omits.**

The neighbouring refutation is on the record already and I do not
transfer it (`AGENTS.md:45`): `[LJ-1.172]` refuted the UNRESTRICTED
`envSetK` at this bound, and `src/L/Condensation/TwelveAgree.lagda.md
:296-301` states the reason in the master. `envSetK` is the term
`SupplyEnv.someEnv` uses to build `E ∈ K`
(`src/L/Coding/EnvSupply.lagda.md:433`). Whether that refutation reaches
`someEnvDef` itself is a MEASUREMENT NOBODY HAS MADE, and it is the
mathematician's next call, not mine.

## WHAT THE FIX WOULD BE, NAMED AND NOT PERFORMED

Add the truncation to `someEnvDef` and thread it. The sweep (C-42) in
`lj-1.504-report.md` counts the sites. The one APPLICATION site already
binds it one line above the call: `src/L/Condensation.lagda.md:3509`
binds `arNum`, `:3515` calls `someEnv` without it.

**I did not edit `someEnvDef` and I did not weaken it.** The brief
forbids both.

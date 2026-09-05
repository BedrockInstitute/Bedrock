# Review of `someEnv-at-codesK`

The two inputs of `codesK` have no source at `someEnvDef`. This
file is the obstruction, for the branch `stop-stated`. The
transport was not attempted. The work forces Reading 1. I did
not gate `someEnvDef`.

## THE STATEMENT

The brief names:

```
someEnv-at-codesK : someEnvDef {n} K γ
```

at a frame where `codesK` is a module hypothesis at
`src/L/Condensation.lagda.md:2782-2786`. `someEnvDef` is
`src/L/Condensation/LowerAgree.lagda.md:52-58`. The frame is
the `[LJ-1.473]` pad with the carrier in slot 0
(`Probe473.agda:61-64`). Predecessor `[LJ-1.480]` is GO on the
refutation (`agents/tasks/LJ-1-480/lj-1.480-report.md:66`).
Predecessor `[LJ-1.473]` is NO-GO on the ungated body
(`agents/tasks/LJ-1-473/lj-1.473-report.md:112`) and GO on
slot 0. Predecessor `[LJ-1.457]` is GO
(`agents/tasks/LJ-1-457/lj-1.457-report.md:87`).

The body was to come from `SupplyEnv.someEnv`
(`src/L/Coding/EnvSupply.lagda.md:417-424`), with `arNum`
taken from `codesK`'s third component. The brief forbids
changing `someEnvDef` and forbids gating it (Reading 2).

I did not write `someEnv-at-codesK`. The type forms at `n = 9`.
The body has no source.

## D-10

`codesK`'s third component is exactly `arNum`'s type
(`Condensation.lagda.md:2785`, `EnvSupply.lagda.md:418`).
`codesK` needs two inputs before it yields that triple
(`Condensation.lagda.md:2782-2784`):

1. `c∈ : ⟨ fst c ∈ fst (lookup C γ) ⟩`
2. `shEq : fst c ≡ pr (fst ar) (pr (# 7) (fst a))`

`someEnvDef` does not take them (`LowerAgree.lagda.md:52-58`).

At this frame, AbstractFrame's C is `suc (suc zero)` of `γ'`
(`TwelveAgree.lagda.md:494`, `LowerAgree.lagda.md:255`). The
pad puts dummy `numeralL 0` in that slot (`Probe473.agda:62-64`,
`Probe483.agda:86-87`). So (1) has no inhabitant: C is
`# 0`. W3 inhabits `no-code` (`Probe483.agda:90-96`).
(2) is not produced from `someEnvDef`'s three memberships.

The brief says: if those inputs have no source at this frame,
name them and STOP.

## W3

GO on the type match and on the empty domain. NO-GO on the
naked truncation `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` with no
binders.

```
C-slot : lookup C Kenv' ≡ numeralL 0
C-slot = refl

no-code : (c : S) → ⟨ fst c ∈ fst (lookup C Kenv') ⟩ → Empty.⊥
```

at `Probe483.agda:86-87` and `:90-96`. `arNum-from-codesK`
(`:109-114`) is the third projection of `codesK`. It
typechecks. Its first two arguments are (1) and (2). Those
have no source at `someEnvDef`. `no-code` says (1) has no
inhabitant at this pad.

Typechecked ALONE, obligation omitted, caliber
`GHCRTS="-A64m -I0 -M8g"`. See the report for the three rechecks.

## THE MISSING SOURCES, AS TYPES

```
code-in-C :
    (c : S)
  → ⟨ fst c ∈ fst (lookup (suc (suc zero)) Kenv') ⟩

shape-eq :
    (c ar a : S)
  → fst c ≡ pr (fst ar) (pr (# 7) (fst a))
```

`no-code` refutes every inhabitant of `code-in-C` at this
frame. `shape-eq` is not a consequence of `someEnvDef`'s
memberships. I did not inhabit either. I did not add them to
`someEnvDef`. I did not apply `SupplyEnv.someEnv`.

## WHAT WAS NOT DONE

No `someEnv-at-codesK` term was written. No hole. No
`TFacts` record. The other 27 fields were not inhabited. No
postulate. The transport from the four-slot frame onto
`envHypB2` was not attempted: `codesK` cannot be applied at
this frame, and the brief stops there.

## CORRECTED TARGET

Reading 2 cannot inhabit `someEnvDef`. Applying `codesK`
needs `c∈` and `shEq`. Putting those on `someEnvDef` is
Reading 1, which the brief forbids. A coder's evidence
outranks a mathematician's ruling. The reversal is this
file.

The truncation has a source at the clause lambdas, not at
the field:

- `BotAgree.bot-in` at `Condensation.lagda.md:2801-2806`
  has `c∈` and `shEq`. BotAgree does not call `someEnv`.
- `PropAgree.back` at `:3505-3515` has `arNum` from binary
  `codesK` at `:3509` and calls `someEnv` at `:3515`
  without passing it.

A next brief that wants the body must inhabit a type that
takes `c∈` and `shEq` (or takes `arNum` directly), at the
consumer, or it must put a code class in slot 2 of the pad.
Do not fund it against this W3 price. Re-measure it.

`TwelveAgree.AbstractFrame` takes `TFacts` as a whole
(`TwelveAgree.lagda.md:337-343`). It cannot reach a local
at `PropAgree.back:3515`. If the field is inhabitable only
under `codesK` plus `c∈` plus `shEq`, `TFacts` may need
splitting. The split type is `someEnvDef` with those two
inputs in the telescope. I did not write it. I did not
inhabit it.

Do not inhabit `TFacts.someEnv` at this pad. That field is
`someEnvDef` with no `codesK`, no `c∈`, no `shEq`
(`TwelveAgree.lagda.md:289`). `[LJ-1.480]` refuted the
truncation from K-membership. This return names the missing
domain of `codesK` at the field.

## C-42

The measurement is this one site: the two inputs of
`codesK` at `Condensation.lagda.md:2782-2784`, against
`someEnvDef` at `LowerAgree.lagda.md:52-58`. It says those
inputs have no source at this frame. It does not measure
how many other sites carry the same missing domain.

See the report for the counts.

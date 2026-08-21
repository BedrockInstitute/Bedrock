# LJ-1.485 report: the environment at the clause where its hypothesis is already bound

slot: `coder`. Written early as a skeleton and filled as runs land (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-485/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: one term `env-at-clause` in
`agents/tasks/LJ-1-485/Probe485.agda`. The type is `someEnvDef`'s
conclusion with the numeral truncation added as a hypothesis, at
`[LJ-1.457]`'s layout with the carrier in slot 0. Slot indices from
`src/L/Condensation/LowerAgree.lagda.md:52-58`. Body from
`SupplyEnv.someEnv`. Nothing lands in `src/`.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection. It does not start phase 3.
No Boundary clause is in conflict.

Predecessor `[LJ-1.483]` is a critic-upheld **STOP**
(`agents/tasks/LJ-1-483/lj-1.483-report.md:90`,
`agents/tasks/LJ-1-483/review-of-LJ-1-483-1.md:6`). I took the
verdict from its report. I quote `## WHERE THE FIELD LIVES` below.
I did not inhabit `someEnv-at-codesK`. Predecessor `[LJ-1.473]` is
**NO-GO** on `someEnv-gated` and **GO** on slot 0
(`agents/tasks/LJ-1-473/lj-1.473-report.md:114`). I took the layout
from its probe (`Probe473.agda:61-67`), not from its brief.
Predecessor `[LJ-1.467]` is **NO-GO** on `ω∈γ`
(`agents/tasks/LJ-1-467/lj-1.467-report.md:105`). I took the type
`⟨ ω ∈ sucV gam ⟩` from that report and from
`src/L/Coding/EnvSupply.lagda.md:111`. I did not inhabit the brief's
`⟨ ω ∈ˢ fst gam ⟩`. Audit F1: a predecessor taken as a hypothesis is
the report (`dev/pod/audit-2026-08-20.md:34-41`).

## WHERE THE FIELD LIVES, quoted from `[LJ-1.483]`

From `agents/tasks/LJ-1-483/lj-1.483-report.md:233-265`:

> `someEnv` is inhabitable at the clause lambda, not at the
> field and not at this pad.
>
> **Not inhabitable**, at `file:line`:
>
> - `TFacts.someEnv` at `src/L/Condensation/TwelveAgree.lagda.md:289`.
>   The field is `someEnvDef {n} K γ'`. No `codesK`, no `c∈`,
>   no `shEq`.
> - `LFacts.someEnv` at `src/L/Condensation/LowerAgree.lagda.md:218`.
>   The same type.
> - `someEnvDef` itself at `LowerAgree.lagda.md:52-58`. Three
>   memberships, no numeral fact, no C-membership, no shape
>   equation.
> - This pad, `Probe483.agda:70-73`. Slot 2 is dummy
>   `numeralL 0`. AbstractFrame's C is that slot
>   (`TwelveAgree.lagda.md:494`, `LowerAgree.lagda.md:255`,
>   `LFacts.codesK` at `LowerAgree.lagda.md:116`). `no-code`
>   (`Probe483.agda:90-96`) refutes every C-membership.
>
> **Inhabitable**, at `file:line`, as a local, not as the field:
>
> - `PropAgree.back` at `src/L/Condensation.lagda.md:3505-3515`.
>   `arNum` is bound at `:3509` from binary `codesK`. `someEnv`
>   is called at `:3515` with `yaK ycK arK` and without
>   `arNum`. Inlining `SupplyEnv.someEnv` there, feeding
>   `:3509`, would inhabit the call. It would not inhabit
>   `someEnvDef`.
> - `BotAgree.bot-in` at `:2801-2806` spends `arNum` from
>   unary `codesK`. BotAgree does not take `someEnv`. The
>   brief named this site as the consumer of the truncation.
>   It is not a consumer of the field.

The verdict of that report is a stated STOP
(`agents/tasks/LJ-1-483/lj-1.483-report.md:90`). I proceed.

## D-10, BEFORE ANY AGDA

`someEnvDef` at `src/L/Condensation/LowerAgree.lagda.md:52-58`:

```
someEnvDef : {n : ℕ} (K : Fin (5 + n)) (γ : S ^ (11 + n)) → Type (ℓ-suc ℓ)
someEnvDef {n} K γ =
  (ya yc b a ar c : S) → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  → Σ S (λ E → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 {11 + n} zero (suc (suc (suc (suc (suc (suc K)))))) ⟩)
```

The clause `let` block at `src/L/Condensation.lagda.md:3505-3515`:

```
  back h = λ c c∈ ar a b yc shD hc ya yb hya hyb →
    let shEq = transport (cong fst (arityTagPairAtL-adequate
                   (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) k
                   (suc (suc zero)) (suc zero) (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))) shD
        (arK , (aK , (bK , arNum))) = codesK c ar a b c∈ shEq
        ycK = valK c ar a b yc c∈ shEq (GraphEntry.bin {m} T γ c ar a b yc hc)
        shB = BinaryShape.in' {m} N K k (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
                tagEq numK innerK pairK aK bK shD
        yaK = subK₁ yb ya yc b a ar c hya
        ybK = subK₀ yb ya yc b a ar c hyb
        (E , (EK , henvE)) = someEnv ya yc b a ar c yaK ycK arK
```

`SupplyEnv.someEnv` at `src/L/Coding/EnvSupply.lagda.md:417-424`
takes the three hypotheses `[LJ-1.473]` named
(`agents/tasks/LJ-1-473/lj-1.473-report.md:76-99`):

1. Numeral truncation `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁`.
   `SupplyEnv.someEnv` takes it (`EnvSupply.lagda.md:418`).
   The clause binds it as `arNum` at
   `Condensation.lagda.md:3509` from binary `codesK`.
   `someEnv` is called at `:3515` without it.
   **Source at this telescope: the clause binds it. This brief
   hypothesises it.**

2. Carrier in slot 0. `envHypB2` reads `B` at index `zero`
   (`Condensation.lagda.md:654-658`). `AndAgree` instantiates
   `B` as `zero` (`LowerAgree.lagda.md:269`). `[LJ-1.473]` put
   `LsetS gam ordγ` in slot 0 of the pad (`Probe473.agda:61-64`,
   GO at `lj-1.473-report.md:114`). This brief rebuilds that
   filler. **Source at this telescope: the filler.** That is
   not a gate.

3. `ω∈γ : ⟨ ω ∈ sucV gam ⟩`. `SupplyEnv` takes it
   (`EnvSupply.lagda.md:111`). `KValue` does not
   (`Condensation.lagda.md:7380-7384`). `someEnvDef` does not
   (`LowerAgree.lagda.md:52-58`). `PropAgree` does not
   (`Condensation.lagda.md:3285-3320`). The clause lambda at
   `:3505` does not bind it. The named obligation
   `env-at-clause` does not take it. The brief forbids gating
   it silently.
   **No source at this telescope.**

The brief hypothesises ONE of the three, the truncation. Slot 0
has a source. `ω∈γ` does not. The brief says: if either of the
other two is still unsourced, name it and STOP. The named gap is
`ω∈γ`.

The brief writes W3 as `⟨ ω ∈ˢ fst gam ⟩`. That type does not
form. `_∈ˢ_` is `S → S → Ω`
(`src/FOL/ZFStructure.lagda.md:48-50`). `gam` is `V ℓ`
(`src/L/Condensation.lagda.md:7384`). `[LJ-1.473]` already
recorded this (`lj-1.473-report.md:33-39`). Audit F1 forbids
taking a brief type over the type a predecessor delivered. The
type I measure is `⟨ ω ∈ sucV gam ⟩`.

`[LJ-1.467]` inhabited the negation at `lam = ω`, `gam = ∅`
(`Probe467.agda:104-107`). This frame uses the same `KValue`
telescope plus the carrier in slot 0. The filler does not
constrain `lam` or `gam`. The frame does not exclude that
instance. W3 re-measures the emptiness at this layout. It does
not transfer the 467 price by analogy.

W3 runs first. The obligation is omitted. I do not gate `ω∈γ`.
I do not apply `SupplyEnv.someEnv`.

## VERDICT

**STOP.** W3 is GO on the emptiness: `omega-source` typechecks
(`Probe485.agda:115-118`, exit 0, median **2.36 s** on three
forced rechecks). The type `⟨ ω ∈ sucV gam ⟩` is empty at a
legal instance of this layout (`lam = ω`, `gam = ∅`). The
carrier sits in slot 0 at that instance
(`carrier-at-instance`, `Probe485.agda:102-104`). The named
obligation was not written. I wrote `review-of-env-at-clause.md`.
The second unsourced hypothesis is `ω∈γ`. I did not gate it.
I did not inhabit `env-at-clause`. I did not apply
`SupplyEnv.someEnv`.

This does not inhabit the `TFacts` record. It does not supply
`twelve-out` or `twelve-back`. It does not touch
`src/Landmarks.lagda.md`. It does not close the campaign. It
does not claim a trophy.

## 1. W2

W2 (from DD4): write the mathematics once at a generic carrier and
instantiate it.

The frame is generic in `KValue`'s bound `lam` and stage `gam`.
`n = 9` is the layout integer from `[LJ-1.457]`. The countermodel
instantiates that telescope at `lam = ω` and `gam = ∅`. One copy.
No band, no numeral-as-carrier, and no site is named as a fixed
form of `someEnv`. There is no conflict with W2. The stop is the
missing `ω∈γ`, not a fixed-form rewrite.

W4 does not fire: no module was retired.

P-l did not fire: the types name `lookup` of `Kenv'` and
`LsetS`. They do not name a transparent `sucV`-chain of a stage.

D-26 did not fire: this is a source check for a module
hypothesis, not a well-founded key.

## 2. W3: `ω∈γ` at this layout, first

**GO on the emptiness. NO-GO on the source.** The widest
unmeasured term was `ω∈γ`. The brief wrote

```
omega-source : ⟨ ω ∈ˢ fst gam ⟩
```

That type does not form (`ZFStructure.lagda.md:48-50`,
`Condensation.lagda.md:7384`). The predecessor type, from
`EnvSupply.lagda.md:111` and `[LJ-1.467]`, is
`⟨ ω ∈ sucV gam ⟩`. The derived form at a legal instance of
this layout is

```
omega-source : ⟨ ω ∈ sucV ∅ ⟩ → Empty.⊥
```

at `Probe485.agda:115-118`, inside `module Countermodel`.
`module Inst = W3 ω ω-ord succω ∅∈ω ∅ ∅-ord ∅∈ω`
(`:100`) is a legal instance of this layout. `∅∈ω = #∈ω 0`
(`:91-92`). `succω` is `ω-next` (`:94-97`).
`carrier-at-instance` (`:102-104`) is `refl`: slot 0 is
`LsetS ∅` at that instance. The body of `omega-source` is
`∈sucV-elim` on `⟨ ω ∈ sucV ∅ ⟩`, empty in `∅` and empty on
`ω ≡ ∅` (`:116-118`). The filler does not produce
`ω ∈ sucV ∅`. The frame does not exclude the 467 instance.

Typechecked ALONE, obligation omitted, caliber `-A64m -I0 -M8g`,
set on the pane, untouched. One Agda process. Dependencies warm.
The probe interface was deleted before every kept recheck
(`_build/2.8.0/agda/agents/tasks/LJ-1-485/Probe485.agdai`).

First landing: 3.01 s, peak RSS 468221952 bytes, exit 0, printed
`Checking`. `runs/w3-1.out` / `w3-1.time`.

Three forced rechecks, exit 0 every time, each printed
`Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-2.out` / `w3-2.time` | 2.40 | 604913664 |
| `runs/w3-3.out` / `w3-3.time` | 2.36 | 604913664 |
| `runs/w3-4.out` / `w3-4.time` | 2.35 | 604913664 |

Median wall **2.36 s**. Median peak RSS **604913664 bytes**. No
heap event.

**55** non-blank non-comment lines in the probe.
`module W3` is 14 of those. `module Countermodel` is 19.
`omega-source` is 4. `carrier-at-instance` is 3. The estimate
was about 8 lines and under 20 seconds. Measured, the named
term is that size and in that second. Nothing is funded against
the estimate. Nothing is funded against `[LJ-1.467]`'s 2.21 s:
that measurement was the 457 pad, not this layout.

## 3. The obligation

`env-at-clause` was not written. The type `someEnvDef {9}` with
the truncation added forms at this layout. The body cannot come
from `SupplyEnv.someEnv`, because that module takes `ω∈γ`
(`EnvSupply.lagda.md:111`) and this telescope does not supply
it. Gating `ω∈γ` is forbidden. The work names that gap. STOP.

I did not add a hole. I did not postulate. I did not inhabit
the other 27 fields. I did not write a `TFacts` record. I
did not import a probe. I did not re-derive the layout
arithmetic. I did not apply `SupplyEnv.someEnv`. I did not
transport the four-slot `envSetB` onto `envHypB2`.

The shape that resisted was `ω∈γ` at the clause, not the
truncation. The clause binds `arNum` at `:3509`. It does not
bind `ω∈γ`. Slot 0 is sourced by the filler.

The full file is W3: the obligation was omitted. First
landing of that file: 2.36 s, peak RSS 604897280 bytes,
exit 0, printed `Checking`. `runs/full-1.out` / `full-1.time`.

Three forced rechecks of the full file, interface deleted
each time, same caliber, one Agda process, exit 0 every time:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-2.out` / `full-2.time` | 2.36 | 604913664 |
| `runs/full-3.out` / `full-3.time` | 2.35 | 604979200 |
| `runs/full-4.out` / `full-4.time` | 2.32 | 604962816 |

Median wall **2.35 s**. Median peak RSS **604962816 bytes**. No
heap event.

The brief's estimate was about 170 lines, of which the
obligation was about 45, comparables of SHAPE. Measured, the
file is 55 lines because the obligation was not written.
Nothing is funded against the estimate.

## WHAT THE FIELD SHOULD BECOME

The term was not obtained. The two candidates the brief named
are still types. I do not choose. Both still lack `ω∈γ`.

### Candidate 1. The field gains the truncation

Type, slot indices from `LowerAgree.lagda.md:52-58`:

```
someEnvDef-with-arNum :
    {n : ℕ} (K : Fin (5 + n)) (γ : S ^ (11 + n))
  → (ya yc b a ar c : S)
  → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
  → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  → Σ S (λ E → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
      × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
            envHypB2 {11 + n} zero (suc (suc (suc (suc (suc (suc K)))))) ⟩)
```

Evidence: the clause already binds `arNum` at
`Condensation.lagda.md:3509` and throws it away at `:3515`.
Sibling fields already take the truncation (`envK-mem` at
`TwelveAgree.lagda.md:186-187`). `TFacts.someEnv` does not
(`:289`).

This type still does not take `ω∈γ`. It does not let
`SupplyEnv.someEnv` apply. A landing would still need a second
gate, which this task was forbidden to add.

Edits to landed chapters, named not performed:

- `src/L/Condensation/LowerAgree.lagda.md:52-58` (`someEnvDef`)
- `src/L/Condensation/LowerAgree.lagda.md:218` (`LFacts.someEnv`)
- `src/L/Condensation/TwelveAgree.lagda.md:289` (`TFacts.someEnv`)
- `src/L/Condensation.lagda.md:3317`, `:3569`, `:3624` (the three
  ungated `someEnv` parameters)
- `src/L/Condensation.lagda.md:3515` (pass `arNum`)

### Candidate 2. The field is removed. `SupplyEnv.someEnv` is inlined at `:3515`

Type of the local, at the clause:

```
inline-someEnv :
    (ya yc b a ar c : S)
  → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
  → ⟨ fst ya ∈ fst (lookup K γ) ⟩
  → ⟨ fst yc ∈ fst (lookup K γ) ⟩
  → ⟨ fst ar ∈ fst (lookup K γ) ⟩
  → Σ S (λ E → ⟨ fst E ∈ fst (lookup K γ) ⟩
      × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 {m} B K ⟩)
```

Evidence: `[LJ-1.483]` located the inhabitable site at
`Condensation.lagda.md:3505-3515`. `arNum` is in scope at
`:3509`. The call at `:3515` is the one consumer of the field
among the clause lambdas.

`PropAgree` still does not take `ω∈γ`
(`Condensation.lagda.md:3285-3320`). `SupplyEnv` still does
(`EnvSupply.lagda.md:111`). Inlining at `:3515` still needs
`lam`, `gam`, and `ω∈γ` in scope at `PropAgree`, or a different
supplier that does not take `ω∈γ`. `AbstractFrame` takes
`TFacts` as a whole (`TwelveAgree.lagda.md:337-343`). A local
does not close `twelve-out`.

Edits to landed chapters, named not performed:

- Delete `TFacts.someEnv` at `TwelveAgree.lagda.md:289`
- Delete `LFacts.someEnv` at `LowerAgree.lagda.md:218`
- Delete or retire `someEnvDef` at `LowerAgree.lagda.md:52-58`
- Remove the `someEnv` parameter at `Condensation.lagda.md:3317`,
  `:3569`, `:3624`
- Replace the call at `:3515` with `SupplyEnv.someEnv` applied
  to `:3509`
- Open `SupplyEnv` at a module that currently has no `ω∈γ`

I do not choose. The mathematician chooses. The clause site is
not sufficient for either candidate until `ω∈γ` has a source,
or until a supplier that does not take it is named.

## 5. WHAT IS LEFT

The obligation `env-at-clause` at `someEnvDef {9}` with `arNum`
as a hypothesis and the carrier in slot 0. This task did not
inhabit it.

`ω∈γ` still has no source at the clause, at `someEnvDef`, at
`KValue`, or at this pad. `[LJ-1.467]` refuted it at a legal
`KValue` instance. This return re-measures that emptiness at
the `[LJ-1.473]` layout. The carrier in slot 0 does not close
the gap.

The 4-to-27 reindex from `E ∷ ar ∷ B₀ ∷ level ∷ []` onto
`envHypB2` is still unmeasured. This task did not reach it.

The other 27 `TFacts` fields. This task did not inhabit them.

`twelve-out` and `twelve-back`
(`TwelveAgree.lagda.md:527-537`) still need a `TFacts` value at
a real `K`. `SatGraphAgree` still leaves those two parameters
unsupplied (`src/L/Condensation.lagda.md:6971-6976`).

A next brief that wants the body must gate `ω∈γ` as well, or
name a supplier that does not take it, or name a frame that
excludes `lam = ω` and `gam = ∅`. Do not fund it against this
2.36 s. Re-measure it.

## 6. C-42

This return is a STOP at one site: `ω∈γ` at
`EnvSupply.lagda.md:111`, against the clause telescope at
`Condensation.lagda.md:3505-3515` and against `someEnvDef` at
`LowerAgree.lagda.md:52-58`. It says that input has no source
at this frame. It does not measure how many other sites carry
the same missing hypothesis.

COUNT of the type `⟨ ω ∈ sucV gam ⟩` in `src/`: **1**,
`EnvSupply.lagda.md:111`. In `archive/src/`: **0**.

COUNT of the identifier `ω∈γ` in `src/`: **7**.
`EnvSupply.lagda.md` 2 (`:111`, `:146`).
`SquareLawClosed.lagda.md` 5 (`:120`, `:122`, `:123`, `:150`,
`:158`). The SquareLawClosed uses have type `⟨ ω ∈ˢ γ ⟩`
(`:119`), not `⟨ ω ∈ sucV gam ⟩`. They are a different site.
A cure of `SupplyEnv`'s `ω∈γ` is not a measured cure of them.

COUNT of `someEnvDef` in `src/`: **5** raw, **3** typed.
Raw: `LowerAgree.lagda.md:52`, `:53`; `:218`;
`TwelveAgree.lagda.md:33`, `:289`. Typed sites, where the
identifier carries a type: `:52`, `:218`, `:289`. None of the
five takes `ω∈γ`. None takes the truncation. In
`archive/src/`: **0**.

COUNT of `SupplyEnv.someEnv` in `src/`: **1**,
`EnvSupply.lagda.md:417`. It takes the truncation at `:418`
and lives under `ω∈γ` at `:111`.

COUNT of the ungated `someEnv` parameter (three memberships,
no truncation, not via `someEnvDef`) in `src/`: **3**,
`Condensation.lagda.md:3317`, `:3569`, `:3624`. One call that
throws `arNum` away: `:3515`. None of the three takes `ω∈γ`.
A cure of `TFacts.someEnv` is not a measured cure of these
three.

COUNT of `module KValue` in `src/`: **1**,
`Condensation.lagda.md:7380`. It takes neither `ω∈γ` nor the
truncation.

COUNT of the truncation string
`∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` in `src/`: **87**.
`Condensation.lagda.md` 50, `LowerAgree.lagda.md` 8,
`UpperAgree.lagda.md` 8, `TwelveAgree.lagda.md` 11,
`EnvSupply.lagda.md` 10. In `archive/src/`: **0**.

A cure of `env-at-clause` at this site is not a measured
cure of `TFacts.someEnv`. It is not a measured cure of
`LFacts.someEnv`. It is not a measured cure of the 3 ungated
`someEnv` parameters. It is not a measured cure of the
4-to-27 transport. It is not a measured cure of
`SquareLawClosed`'s `⟨ ω ∈ˢ γ ⟩`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX, archived 2026-08-18". Declined. The live producer is `dev/pod/queue.toml`. This task does not consult the archived dispatch rows.
- `archive/dev/JOURNAL-archived.md:1`, read: "# Archived journal: the retired route". Declined. The retired-route journal does not bear on whether `ω∈γ` has a source at this clause.
- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined. The per-episode journal is retired. The product of this task lives in this directory.
- `dev/ARCHIVE.md:1`, read: "# ARCHIVE.md: the archive registry". Declined. This task does not retire a module.
- `archive/dev/DD-archived.md:1`, read: "# THE `DD` RULING SERIES, archived in full 2026-08-18". Declined. The live rulings are `dev/pod/rulings.toml`. This task does not consult the archived DD rows.

## LITERATURE USED

- `dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the Condensation Lemma and the GCH in L". Declined as a source for a producer. Devlin 5.5 does not inhabit `env-at-clause` at a frame whose `KValue` instance has `gam = ∅`.
- `dev/literature/truncation-and-selection.md:1`, read: "# Truncation and selection: how the two literatures pick a witness". Declined. The work is a source check for `ω∈γ`, not a truncated witness selection from the literature.
- `dev/literature/terms-2026-08.md:1`, read: "# The terminology dossier: fourteen renderings for the owner's ruling". Declined. No glossary term is at issue.
- `dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the rud route, pinned from the collected literature". Declined. This task measures a module hypothesis of `SupplyEnv`. It does not consult the orthodox rud digest.
- `dev/literature/glossary-review-2026-08.md:1`, read: "# Glossary review: the 119 pre-protocol entries". Declined. This task adds no glossary entry.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process from this slot.
- I did not write in `src/`.
- I did not inhabit `env-at-clause`.
- I did not inhabit the other 27 `TFacts` fields.
- I did not write a `TFacts` record.
- I did not import a probe.
- I did not postulate.
- I did not change `someEnvDef`.
- I did not gate `someEnvDef`.
- I did not gate `ω∈γ`.
- I did not apply `SupplyEnv.someEnv`.
- I did not transport.

## WHAT THE NEXT BRIEF NEEDS

W3 is GO on the emptiness. `omega-source` is green.
`carrier-at-instance` is green. The `[LJ-1.473]` layout with
the carrier in slot 0 still admits `lam = ω` and `gam = ∅`.
At that instance `⟨ ω ∈ sucV gam ⟩` is empty. The clause binds
the truncation and does not bind `ω∈γ`. Slot 0 is sourced.
The second unsourced hypothesis is `ω∈γ`. The clause site is
not sufficient. The field's neighbourhood needs restating.

What a next brief can order, one at a time:

1. Gate `ω∈γ` as well, at the clause or at the field. The
   type is `⟨ ω ∈ sucV gam ⟩` (`EnvSupply.lagda.md:111`), not
   `⟨ ω ∈ˢ fst gam ⟩`. That excludes the legal instance
   `lam = ω`, `gam = ∅`. `[LJ-1.473]` already gated it at the
   pad and still lacked the truncation. Do not fund it against
   this 2.36 s. Re-measure it.
2. Name a supplier that does not take `ω∈γ`. `SupplyEnv.someEnv`
   is not that supplier. Do not fund a new construction against
   this source STOP. C-42 forbids a transfer onto it
   (`dev/LESSONS.md:3752`).
3. Name a frame that excludes `lam = ω` and `gam = ∅` by a
   stated fact, not by a silent gate. Re-measure `ω∈γ` at that
   frame.
4. Candidate 1 or candidate 2 above, once `ω∈γ` has a source.
   Neither lands today. Name the split of `TFacts` if that is
   the ruling. Do not fund it against this pad.
5. The 4-to-27 transport. This task did not reach it. Do not
   fund it against this 2.36 s.
6. The 25 closure lemmas. The 250-line hypothesis still stands
   (`agents/tasks/LJ-1-113/lj-1.113-report.md:135-146`). Do
   not fund them against this source STOP.

The condensation front is open for those briefs. It is not open
for a landing in `src/` until a brief names a type that takes
`ω∈γ`, or names a supplier that does not, and names the
consumer's two parameters.

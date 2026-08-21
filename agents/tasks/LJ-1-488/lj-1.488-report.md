# LJ-1.488 report: both gates at once

slot: `coder`. Written early as a skeleton and filled as runs land (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-488/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: one term `someEnv-doubly-gated` in
`agents/tasks/LJ-1-488/Probe488.agda`. The type is `someEnvDef`'s
conclusion with BOTH missing hypotheses added, at `[LJ-1.457]`'s
layout with the carrier in slot 0. Slot indices from
`agents/tasks/LJ-1-485/lj-1.485-report.md` Candidate 1. Body from
`SupplyEnv.someEnv`, then the generic `EnvSet` transfer at 27
slots. Nothing lands in `src/`.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection. It does not start phase 3.
No Boundary clause is in conflict.

Predecessor `[LJ-1.485]` is a critic-upheld **STOP**
(`agents/tasks/LJ-1-485/lj-1.485-report.md:159`,
`agents/tasks/LJ-1-485/review-of-LJ-1-485-1.md:6`). I took the
verdict from its report. I quote Candidate 1 below. I did not
inhabit `env-at-clause`. Audit F1: a predecessor taken as a
hypothesis is the report (`dev/pod/audit-2026-08-20.md:34-41`).

The brief writes the second gate as `⟨ ω ∈ˢ fst gam ⟩`. That type
does not form. `_∈ˢ_` is `S → S → Ω`
(`src/FOL/ZFStructure.lagda.md:48-50`). `gam` is `V ℓ`
(`src/L/Condensation.lagda.md:7383`). `[LJ-1.485]` already recorded
this (`lj-1.485-report.md:139-145`). The type I take is
`⟨ ω ∈ sucV gam ⟩` from `src/L/Coding/EnvSupply.lagda.md:111` and
from the 485 probe that typechecked (`Probe485.agda:115`).

## CANDIDATE 1, quoted from `[LJ-1.485]`

From `agents/tasks/LJ-1-485/lj-1.485-report.md:296-321`:

> ### Candidate 1. The field gains the truncation
>
> Type, slot indices from `LowerAgree.lagda.md:52-58`:
>
> ```
> someEnvDef-with-arNum :
>     {n : ℕ} (K : Fin (5 + n)) (γ : S ^ (11 + n))
>   → (ya yc b a ar c : S)
>   → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
>   → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
>   → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
>   → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
>   → Σ S (λ E → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
>       × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
>             envHypB2 {11 + n} zero (suc (suc (suc (suc (suc (suc K)))))) ⟩)
> ```

From `agents/tasks/LJ-1-485/lj-1.485-report.md:319-321`:

> This type still does not take `ω∈γ`. It does not let
> `SupplyEnv.someEnv` apply. A landing would still need a second
> gate, which this task was forbidden to add.

The verdict of that report is a stated STOP
(`agents/tasks/LJ-1-485/lj-1.485-report.md:159`). I proceed.

## D-10, BEFORE ANY AGDA

`SupplyEnv` at `src/L/Coding/EnvSupply.lagda.md:107-111` and
`someEnv` at `:417-424`. Inputs, and whether this telescope binds
each one.

Module telescope of `SupplyEnv`:

1. `lam`, `ordλ`, `succλ`, `∅∈λ`, `gam`, `ordγ`, `γ∈λ`.
   `KValue` binds them (`Condensation.lagda.md:7380-7384`).
   This pad is that telescope. **Sourced.**
2. `ω∈γ : ⟨ ω ∈ sucV gam ⟩` (`EnvSupply.lagda.md:111`).
   **Hypothesis here.** The brief wrote `⟨ ω ∈ˢ fst gam ⟩`.
   I take the predecessor type.

Function telescope of `someEnv`:

3. `ya yc b a ar c : S`. Bound by the obligation.
4. `arNum : ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁`
   (`EnvSupply.lagda.md:418`). **Hypothesis here.**
5. Three memberships `⟨ fst ya ∈ Lset lam ⟩`, and the same for
   `yc` and `ar` (`EnvSupply.lagda.md:419-421`).
   `someEnvDef` gives `⟨ fst ya ∈ fst (lookup (suc^6 K) γ) ⟩`
   (`LowerAgree.lagda.md:54-56`). At this layout `K = iK' = iK`
   and slot `suc^6 iK'` is `LsetS lam`
   (`Condensation.lagda.md:7390-7397`, pad of `[LJ-1.485]`
   `Probe485.agda:70-76`). `fst (LsetS lam ordλ) ≡ Lset lam`
   (`src/L/Axioms/Basic.lagda.md:160-161`). **Sourced from
   `someEnvDef`'s shape.**
6. Carrier `B₀ = LsetS gam ordγ` (`EnvSupply.lagda.md:124-125`).
   Slot 0 of the pad is that carrier
   (`Probe485.agda:70-72`, GO at `lj-1.485-report.md:163-164`).
   **Sourced by the filler.** That is not a gate.

No fourth unsourced input. I did not stop. W3 is the application.

`someEnv`'s conclusion is a 4-slot `envSetB`
(`EnvSupply.lagda.md:423-424`). The obligation's satisfaction
half is `envHypB2` on `E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ`
(`LowerAgree.lagda.md:58`). That half is a conclusion, not a
fourth input. W3 omits it, as the brief orders.

## VERDICT

**GO.** W3 is GO: `W3.applied` typechecks
(`Probe488.agda:78-89`, exit 0, median **2.21 s** on three
forced rechecks). `SupplyEnv.someEnv` applies with both gates
in scope. It refuses no argument. There is no fourth unsourced
input.

The obligation `someEnv-doubly-gated` typechecks
(`Probe488.agda:95-123` and the top-level alias at `:131`,
exit 0, median **2.49 s** on three forced rechecks) and PASSes
the program's witness meter
(`/opt/homebrew/bin/python3.11 scripts/pod/witness.py --code LJ-1-488
--brief agents/tasks/LJ-1-488/LJ-1.488.md`, exit 0, 2.19 s, 0
UNRESOLVED of 1, `probe_red=False`, `runs/witness-1.out`).
`.venv/bin/python` is absent in this worktree. I added no
dependency.

I did not write `review-of-someEnv-doubly-gated.md`. The verdict
is GO.

A GO settles the nine-dispatch question at this pad: with both
gates, the delivered supplier serves the field. It does not
inhabit the `TFacts` record. It does not supply `twelve-out` or
`twelve-back`. It does not touch `src/Landmarks.lagda.md`. It
does not close the campaign. It does not claim a trophy. It
does not choose between the two repairs below.

## 1. W2

W2 (from DD4): write the mathematics once at a generic carrier and
instantiate it.

The frame is generic in `KValue`'s bound `lam` and stage `gam`.
`n = 9` is the layout integer from `[LJ-1.457]`. `SupplyEnv.someEnv`
is one copy. The satisfaction half is `EnvSet.back` of
`Generic.Holds` (`src/L/Condensation.lagda.md:3045-3048`,
`src/L/Coding/EnvSet.lagda.md:521-541`), the same generic transfer `someEnv`
uses at 4 slots (`EnvSupply.lagda.md:440-444`), instantiated
here at 27. One copy. No band, no numeral-as-carrier, and no
site is named as a fixed form. There is no conflict with W2.

W4 does not fire: no module was retired.

P-l did not fire: the types name `lookup` of `Kenv'` and
`LsetS`. They do not name a transparent `sucV`-chain of a stage.
The gate `⟨ ω ∈ sucV gam ⟩` is the type `SupplyEnv` already
declares (`EnvSupply.lagda.md:111`).

D-26 did not fire: this is an application of a delivered
supplier, not a well-founded key.

## 2. W3: the application, first

**GO.** The widest unmeasured term was the application itself.
The brief wrote

```
applied : Σ S (λ E → ⟨ fst E ∈ fst K ⟩ × _)
```

I wrote it at this layout as `W3.applied`
(`Probe488.agda:78-89`). Both gates are in scope. The
satisfaction half is omitted. The body is

```
let module SE = SupplyEnv lam ordλ succλ ∅∈λ gam ordγ γ∈λ ω∈γ
    (E , (EK , _)) = SE.someEnv ya yc b a ar c arNum yaK ycK arK
in  E , EK
```

Agda accepted every argument: the three memberships at
`lookup (suc^6 iK') Kenv'` unified with `Lset lam`, and `ω∈γ`
unified with `⟨ ω ∈ sucV gam ⟩`. No argument was refused.

The first Agda run was a missing `∅` import (`runs/w3-1.out`,
exit 42, `[NotInScope]` at `Probe488.agda:58`, 2.39 s). That is
not a fourth input. I added `∅` to the import. I did not change
the term.

Typechecked ALONE, obligation omitted, caliber `-A64m -I0 -M8g`,
set on the pane, untouched. One Agda process. Dependencies warm.
The probe interface was deleted before every kept recheck
(`_build/2.8.0/agda/agents/tasks/LJ-1-488/Probe488.agdai`).

First green landing: 2.21 s, peak RSS 705806336 bytes, exit 0,
printed `Checking`. `runs/w3-1b.out` / `w3-1b.time`.

Three forced rechecks, exit 0 every time, each printed
`Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-2.out` / `w3-2.time` | 2.21 | 705773568 |
| `runs/w3-3.out` / `w3-3.time` | 2.21 | 705773568 |
| `runs/w3-4.out` / `w3-4.time` | 2.21 | 705773568 |

Median wall **2.21 s**. Median peak RSS **705773568 bytes**. No
heap event.

**79** non-blank non-comment lines in the final probe.
`W3.applied` is 12 of those (`:78-89`). The estimate was about
12 lines and under 25 seconds. Measured, the named term is that
size and in that second. Nothing is funded against the estimate.
Nothing is funded against `[LJ-1.473]`'s or `[LJ-1.485]`'s
seconds: neither reached this line.

## 3. The obligation

**GO.** `someEnv-doubly-gated` is `someEnvDef {9}` with both
gates, Candidate 1 slot indices, carrier in slot 0
(`Probe488.agda:95-123`). The top-level name the witness reads
is the alias at `:131`.

The body applies `SE.someEnv` for `(E, EK)`, then instantiates
`EnvSet {7 + (11 + 9)}` and `Generic.Holds {7 + (11 + 9)}` at

```
γ27 = E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Kenv'
```

with `ar` at `suc^5 zero`, `B` at `suc^7 zero` (slot 0 of the
pad, the carrier), and `K` at `suc^13 iK'`, which is
`suc^7 (suc^6 iK')` as `envHypB2` lays out
(`Condensation.lagda.md:654-658`). `arityK27` is `SE.transK`.
`envInK27` is `SE.envInK-gen` at those indices. The satisfaction
half is `ES.back H.holds`.

I did not import a probe. I did not re-derive the layout
arithmetic. I did not postulate. I did not add a third gate.
I did not edit `someEnvDef`, `TFacts` or `LFacts`. I did not
inhabit the other 27 `TFacts` fields. I did not write a
`TFacts` record.

The shape that resisted was not the application. The 4-to-27
half closed by instantiating the generic transfer already in
the tree. The memberships matched definitionally. I weakened
nothing except the brief's ill-typed `⟨ ω ∈ˢ fst gam ⟩`, which
I replaced with the predecessor type. That is a correction,
not a weaker statement.

First landing of the full file: 2.50 s, peak RSS 649396224
bytes, exit 0, printed `Checking`. `runs/full-1.out` /
`full-1.time`.

Three forced rechecks of the full file, interface deleted
each time, same caliber, one Agda process, exit 0 every time:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-2.out` / `full-2.time` | 2.49 | 649396224 |
| `runs/full-3.out` / `full-3.time` | 2.50 | 649379840 |
| `runs/full-4.out` / `full-4.time` | 2.49 | 649379840 |

Median wall **2.49 s**. Median peak RSS **649379840 bytes**. No
heap event.

The brief's estimate was about 175 lines, of which the
obligation was about 45, comparables of SHAPE. Measured, the
file is 79 non-blank non-comment lines, of which
`someEnv-doubly-gated` in `W3` is 29 (`:95-123`) and the alias
is 1 (`:131`). Nothing is funded against the estimate.

## WHAT THE DOUBLE GATE COSTS

Named, not performed. I do not choose.

`someEnvDef` at `src/L/Condensation/LowerAgree.lagda.md:52-58`
takes `{n} (K : Fin (5 + n)) (γ : S ^ (11 + n))` and three
memberships. It does not bind `gam`. `⟨ ω ∈ sucV gam ⟩` cannot
be stated there without adding `gam` as a parameter. The
truncation can: it mentions only `ar`.

The clause `let` at `src/L/Condensation.lagda.md:3505-3515`
binds `arNum` at `:3509` and calls `someEnv` at `:3515`
without it. It does not bind `ω∈γ`. `PropAgree` at
`:3285-3320` takes neither. `KValue` at `:7380-7384` takes
neither.

### Repair A. Both hypotheses go into `someEnvDef`

Sites, 3 landed chapters:

1. `src/L/Condensation/LowerAgree.lagda.md:52-58` (`someEnvDef`
   gains the truncation and a `gam` binder plus `ω∈γ`)
2. `src/L/Condensation/LowerAgree.lagda.md:218` (`LFacts.someEnv`)
3. `src/L/Condensation/TwelveAgree.lagda.md:289` (`TFacts.someEnv`)
4. `src/L/Condensation/TwelveAgree.lagda.md:442` (the record fill)
5. `src/L/Condensation.lagda.md:3317`, `:3569`, `:3624` (the three
   `someEnv` parameters of `PropAgree` / `AndAgree` / `OrAgree`)
6. `src/L/Condensation.lagda.md:3285-3320` (`PropAgree` must take
   `ω∈γ`, and `SupplyEnv` still needs the `KValue` telescope)
7. `src/L/Condensation.lagda.md:3515` (pass `arNum` and `ω∈γ`)

**3 chapters, 7 named site groups.** The extra cost against a
truncation-only gate is the `gam` binder on a type that is
today tower-generic. `someEnvDef` is not a `KValue` local.
Adding `gam` there is a presentation in the type (P-l), not
only a fact about a concrete stage.

### Repair B. The field stays. `SupplyEnv.someEnv` is inlined at `:3515`

Sites, 3 landed chapters:

1. `src/L/Condensation.lagda.md:3515` (replace the call; `arNum`
   is already bound at `:3509`)
2. `src/L/Condensation.lagda.md:3285-3320` (`PropAgree` must open
   `SupplyEnv`, so it must take `lam`, `gam`, and `ω∈γ`)
3. `src/L/Condensation.lagda.md:3317`, `:3569`, `:3624` (the
   `someEnv` parameter can then go)
4. `src/L/Condensation/LowerAgree.lagda.md:52-58`, `:218`, `:273`,
   `:279` (delete or retire `someEnvDef` / `LFacts.someEnv` and
   stop passing it)
5. `src/L/Condensation/TwelveAgree.lagda.md:289`, `:442` (delete
   `TFacts.someEnv` and stop filling it)

**3 chapters, 5 named site groups.** The field is not grown.
`someEnvDef` never has to mention `gam`. The cost that remains
is the same missing `ω∈γ` at `PropAgree`, plus opening
`SupplyEnv` at a module that currently has no `KValue`
telescope.

### Which is smaller in edits to landed chapters

Both edit **3** landed chapters:
`LowerAgree.lagda.md`, `TwelveAgree.lagda.md`,
`Condensation.lagda.md`. Equal in chapter count.

Repair B names fewer site groups (5 against 7) and does not
add a `gam` binder to a generic field type. Repair A keeps the
field and reuses the `:3515` call, where `arNum` is already
bound. I do not choose.

## 5. WHAT IS LEFT

The obligation at this pad is inhabited. The two repairs above
are still types. The mathematician chooses.

`ω∈γ` still has no source at `someEnvDef`, at `KValue`, or at
`PropAgree`. This pad hypothesises it. `[LJ-1.467]` and
`[LJ-1.485]` still refute it at `lam = ω`, `gam = ∅`. A landing
in `src/` must carry the gate, or name a frame that excludes
that instance, or name a supplier that does not take `ω∈γ`.

The other 27 `TFacts` fields. This task did not inhabit them.

`twelve-out` and `twelve-back`
(`TwelveAgree.lagda.md:528-537`) still need a `TFacts` value at
a real `K`. `SatGraphAgree` still leaves those two parameters
unsupplied (`src/L/Condensation.lagda.md:6971-6976`).

The 25 closure lemmas. The 250-line hypothesis still stands
(`agents/tasks/LJ-1-113/lj-1.113-report.md:135-146`). Do not
fund them against this 2.49 s.

Do not fund a landing against this pad. Re-measure it at the
chosen repair.

## 6. C-42

This return is a GO at one site: `SupplyEnv.someEnv` at
`EnvSupply.lagda.md:417-424`, applied at the `[LJ-1.457]` layout
with the carrier in slot 0 and both gates hypothesised. It says
the supplier serves this field at that telescope. It does not
measure a landing in `src/`.

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

A cure that lands `someEnv-doubly-gated` into `TFacts.someEnv`
is not a measured cure of the 3 ungated `someEnv` parameters.
It is not a measured cure of `SquareLawClosed`'s `⟨ ω ∈ˢ γ ⟩`.
It is not a measured cure of `twelve-out`. Re-measure each.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX, archived 2026-08-18". Declined. The live producer is `dev/pod/queue.toml`. This task does not consult the archived dispatch rows.
- `archive/dev/JOURNAL-archived.md:1`, read: "# Archived journal: the retired route". Declined. The retired-route journal does not bear on whether `SupplyEnv.someEnv` applies with both gates.
- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined. The per-episode journal is retired. The product of this task lives in this directory.
- `dev/ARCHIVE.md:1`, read: "# ARCHIVE.md: the archive registry". Declined. This task does not retire a module.
- `archive/dev/DD-archived.md:1`, read: "# THE `DD` RULING SERIES, archived in full 2026-08-18". Declined. The live rulings are `dev/pod/rulings.toml`. This task does not consult the archived DD rows.

## LITERATURE USED

- `dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the Condensation Lemma and the GCH in L". Declined as a source for a producer. Devlin 5.5 does not inhabit `someEnv-doubly-gated` at this pad.
- `dev/literature/truncation-and-selection.md:1`, read: "# Truncation and selection: how the two literatures pick a witness". Declined. The truncation is a hypothesis here. The work is an application of a delivered supplier, not a literature selection.
- `dev/literature/terms-2026-08.md:1`, read: "# The terminology dossier: fourteen renderings for the owner's ruling". Declined. No glossary term is at issue.
- `dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the rud route, pinned from the collected literature". Declined. This task measures a module application of `SupplyEnv`. It does not consult the orthodox rud digest.
- `dev/literature/glossary-review-2026-08.md:1`, read: "# Glossary review: the 119 pre-protocol entries". Declined. This task adds no glossary entry.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process from this slot.
- I did not write in `src/`.
- I did not inhabit the other 27 `TFacts` fields.
- I did not write a `TFacts` record.
- I did not import a probe.
- I did not postulate.
- I did not change `someEnvDef`.
- I did not change `TFacts` or `LFacts`.
- I did not add a third gate silently.
- I did not inhabit the brief's ill-typed `⟨ ω ∈ˢ fst gam ⟩`.
- I did not write `review-of-someEnv-doubly-gated.md`.
- I did not choose between Repair A and Repair B.

## WHAT THE NEXT BRIEF NEEDS

W3 is GO. The obligation is GO. `SupplyEnv.someEnv` applies
with both gates. The 4-to-27 half is the generic `EnvSet`
transfer at 27 slots. There is no fourth unsourced input.

What a next brief can order, one at a time:

1. Repair A or Repair B above. Both edit 3 landed chapters.
   Repair B names fewer site groups. Repair A keeps the field
   and must add `gam` to `someEnvDef`. Name the split of
   `TFacts` if that is the ruling. Do not fund it against this
   2.49 s. Re-measure it.
2. A source for `ω∈γ` at `PropAgree` or at `KValue`, if the
   chosen repair is to land without hypothesising the gate at
   every consumer. `[LJ-1.467]` and `[LJ-1.485]` still refute
   it at `lam = ω`, `gam = ∅`. Do not fund it against this
   pad.
3. The other 27 `TFacts` fields, and then `twelve-out` /
   `twelve-back`. Do not fund them against this supplier GO.
4. The 25 closure lemmas
   (`agents/tasks/LJ-1-113/lj-1.113-report.md:135-146`).

The condensation front is open for those briefs. It is open
for a landing in `src/` only after a brief names Repair A or
Repair B and names the consumer's two parameters.

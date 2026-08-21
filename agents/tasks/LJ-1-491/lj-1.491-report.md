# LJ-1.491 report: can the frame carry the hypothesis that has no home

slot: `coder`. Written early as a skeleton and filled as runs land (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-491/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: one term `kvalue-with-omega` in
`agents/tasks/LJ-1-491/Probe491.agda`. The type is `KValue`'s
`KFacts` record with `ω∈γ` added to the telescope and every
existing field unchanged. Nothing lands in `src/`.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection. It does not start phase 3.
No Boundary clause is in conflict.

Predecessor `[LJ-1.488]` is **GO**
(`agents/tasks/LJ-1-488/lj-1.488-report.md:108`). I took the
verdict from that report. I did not stop. Audit F1: a predecessor
taken as a hypothesis is the report
(`dev/pod/audit-2026-08-20.md:34-41`). 488's inhabited type is
`⟨ ω ∈ sucV gam ⟩` (`Probe488.agda:81`). This brief names a
different binder. See D-10.

## D-10 AND W3 CENSUS, BEFORE ANY AGDA

`[LJ-1.488]` `## WHAT THE DOUBLE GATE COSTS`
(`lj-1.488-report.md:271-285`) records that `someEnvDef` cannot
state `ω∈γ` because it does not bind `gam`, and that the clause
`let`, `PropAgree` and `KValue` each bind neither. Verdict of
that report is GO (`:108`). I proceed.

D-10 of this brief: adding `ω ∈ gam` to `KValue` excludes
instances that are legal today. `[LJ-1.467]` exhibited
`lam = ω`, `gam = ∅` (`lj-1.467-report.md:105-107`,
`Probe467.agda:95`).

The brief wrote `⟨ ω ∈ˢ gam ⟩`. `_∈ˢ_` on `𝒮ʟ` is
`S → S → Ω` (`src/FOL/ZFStructure.lagda.md:48`). `gam` is
`V ℓ` (`src/L/Condensation.lagda.md:7383`). That type does
not form under `𝒮ʟ`. `_∈ˢ_` on `𝒮ᵥ` is `_∈_`
(`src/V/Hierarchy.lagda.md:83`). This brief's D-10 paragraph
names `ω ∈ gam`. The type I take is `⟨ ω ∈ gam ⟩`. That is
not `[LJ-1.488]`'s `⟨ ω ∈ sucV gam ⟩`
(`src/L/Coding/EnvSupply.lagda.md:111`). `ω ∈ gam` implies
the `sucV` gate by the first disjunct of `∈sucV`. I did not
inhabit the weaker type. `ω ∈ gam` also excludes `gam = ω`,
which the `sucV` gate does not.

W3 is the consumer census. RUN `grep -rn "KValue" src/`.
Output in `runs/census.out`. One hit:

```
src/L/Condensation.lagda.md:7380:module KValue (lam : V ℓ) (ordλ : IsOrd lam)
```

That is the definition. It is not a consumer.

`grep -rn "KValue" archive/src/` is empty
(`runs/census-archive.out`).

No `open KValue`, no `module KV = KValue`, no
`module Inst = KValue` in `src/`.

Premise 8 names the consumer: `consed` at
`src/L/Condensation.lagda.md:7429-7434`. It applies
`KFactsCons` to `facts`. It lives in `KValue`'s own
telescope. It does not pass a concrete `gam`. It is generic.

No src/ consumer passes a finite stage. The restriction is
not refuted. I build.

## VERDICT

**GO.** `kvalue-with-omega` typechecks
(`agents/tasks/LJ-1-491/Probe491.agda:54-66`, exit 0, median
**2.40 s** on three forced rechecks) and PASSes the program's
witness meter
(`/opt/homebrew/bin/python3.11 scripts/pod/witness.py --code LJ-1-491
--brief agents/tasks/LJ-1-491/LJ-1.491.md`, exit 0, 2.51 s, 0
UNRESOLVED of 1, `probe_red=False`, `runs/witness-1.out`).
`.venv/bin/python` is absent in this worktree. I added no
dependency.

I did not write `review-of-kvalue-with-omega.md`. The verdict
is GO.

A GO gives `ω∈γ` a home at `KValue`: the extra binder sits
on the telescope, the `KFacts` record is the existing
`facts`, and the tree's own consumer `consed` is not
refuted by a finite-stage application. It does not land the
restriction in `src/`. It does not inhabit `TFacts.someEnv`.
It does not supply `twelve-out` or `twelve-back`. It does
not touch `src/Landmarks.lagda.md`. It does not close the
campaign. It does not claim a trophy. It does not choose
Repair A or Repair B of `[LJ-1.488]`.

## 1. W2

W2 (from DD4): write the mathematics once at a generic carrier and
instantiate it.

The body is `KValue.facts` (`Probe491.agda:61-64`). One copy
of the record, already in the tree. The extra binder is
unused. Instantiated at `KValue`'s generic `lam` and `gam`.
No second copy of the fourteen-slot fill. No band, no
numeral-as-carrier, and no site is named as a fixed form.
There is no conflict with W2.

W4 does not fire: no module was retired.

P-l did not fire: the type names `ω` and `gam`. It does not
name a transparent `sucV`-chain of a stage.

D-26 did not fire: this is a telescope restriction, not a
well-founded key.

## 2. W3: the census, first

**GO.** The widest unmeasured term was the consumer census.
`grep -rn "KValue" src/` returned one line
(`runs/census.out`): the definition at
`src/L/Condensation.lagda.md:7380`. The only consumer of
the record is `consed` at `:7429-7434`, generic in `gam`.
COUNT of applications at a finite `gam` in `src/`: **0**.
The restriction is not refuted. The term is not misleading
work.

The census is a grep. It has no Agda price.

## 3. The obligation

**GO.** `kvalue-with-omega` is `KValue`'s telescope plus
`⟨ ω ∈ gam ⟩` (`Probe491.agda:54-64`). The top-level name
the witness reads is the alias at `:66`.

The body is

```
open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ
kvalue-with-omega = facts
```

`ω∈γ` is not used in any field. The record is
`KValue.facts` (`src/L/Condensation.lagda.md:7411-7425`)
unchanged. I did not restate the fourteen-slot fill. I did
not import a probe. I did not postulate. I did not weaken a
field. I did not edit `src/L/Condensation.lagda.md`.

The shape that resisted was the brief's `⟨ ω ∈ˢ gam ⟩`
under `𝒮ʟ`. I replaced it with `⟨ ω ∈ gam ⟩`, which is
`𝒮ᵥ`'s `_∈ˢ_` (`src/V/Hierarchy.lagda.md:83`) and the D-10
wording of this brief. That is a notation correction, not a
weaker statement. Against `[LJ-1.488]`'s `⟨ ω ∈ sucV gam ⟩`
it is a stronger statement: it excludes `gam = ω`.

First landing of the full file: 2.87 s, peak RSS 611123200
bytes, exit 0, printed `Checking`. `runs/full-1.out` /
`full-1.time`.

Three forced rechecks of the full file, interface deleted
each time
(`_build/2.8.0/agda/agents/tasks/LJ-1-491/Probe491.agdai`),
same caliber, one Agda process, exit 0 every time, each
printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-2.out` / `full-2.time` | 2.81 | 611074048 |
| `runs/full-3.out` / `full-3.time` | 2.40 | 611090432 |
| `runs/full-4.out` / `full-4.time` | 2.38 | 611172352 |

Median wall **2.40 s**. Median peak RSS **611090432 bytes**.
No heap event.

The brief's estimate was about 120 lines, of which the
obligation was about 60, comparables of SHAPE. Measured, the
file is 66 lines, **25** non-blank non-comment, of which
`W3.kvalue-with-omega` is 2 (`:63-64`) and the alias is 1
(`:66`). Nothing is funded against the estimate. Nothing is
funded against `[LJ-1.488]`'s 2.49 s.

## WHO LOSES THE EXCLUDED INSTANCES

Required list. Every `KValue` consumer at `file:line`, the
`gam` it passes, and whether that `gam` is infinite.

| site | role | gam | infinite? |
|---|---|---|---|
| `src/L/Condensation.lagda.md:7380` | definition of `module KValue` | binder, not an application | n/a |
| `src/L/Condensation.lagda.md:7429-7434` | `consed`, the tree's own consumer of `facts` via `KFactsCons` | the same generic `gam` as the module telescope | not instantiated |

COUNT of applications of `KValue` at a concrete `gam` in
`src/`: **0**.

COUNT of applications of `KValue` at a finite `gam` in
`src/`: **0**.

No landed consumer loses the excluded instances, because no
landed consumer instantiates `KValue`.

Probes that instantiate the legal finite instance
`lam = ω`, `gam = ∅`. These are not src/ consumers. They
are frozen measurements of the unrestricted telescope. They
would not apply under the restriction:

- `agents/tasks/LJ-1-467/Probe467.agda:95`
  `module Inst = KValue ω ω-ord succω ∅∈ω ∅ ∅-ord ∅∈ω`
- `agents/tasks/LJ-1-476/Probe476.agda:63` same instance
- `agents/tasks/LJ-1-480/Probe480.agda:61` same instance

`gam = ∅` is finite. Those three probes used it as a
countermodel for other statements. They do not consume
`KValue` in `src/`.

Probes that open `KValue` generically, same telescope as
today, no concrete `gam`: 338, 383, 450, 457, 463, 467
(the generic half), 473, 483, 485, 488. They would gain the
binder if `KValue` itself were restricted. That is a landing
question. It is not a finite-stage consumer.

The restriction also excludes `gam = ω`, because `∈` is
irreflexive. No src/ consumer instantiates that case
either. `[LJ-1.488]`'s `⟨ ω ∈ sucV gam ⟩` would keep
`gam = ω`. This term does not.

## 5. WHAT IS LEFT

The restricted frame builds. The mathematician chooses
whether to restrict the landed `KValue`.

`[LJ-1.488]` Repair A and Repair B
(`lj-1.488-report.md:287-338`) are still types. This GO
gives `ω∈γ` a home at `KValue`. It does not thread the
binder to `someEnvDef`, `PropAgree`, or the clause `let`.
It does not inhabit `TFacts.someEnv`.

The truncation `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` still has
no home at `KValue`. `[LJ-1.488]` measured that it can go
into `someEnvDef` because it mentions only `ar`
(`lj-1.488-report.md:278-279`).

If the landing wants the `SupplyEnv` gate exactly, take
`⟨ ω ∈ sucV gam ⟩` (`EnvSupply.lagda.md:111`), not
`⟨ ω ∈ gam ⟩`. The stronger gate excludes `gam = ω`.

The other 27 `TFacts` fields. This task did not inhabit
them.

`twelve-out` and `twelve-back`
(`src/L/Condensation/TwelveAgree.lagda.md:528-537`) still
need a `TFacts` value at a real `K`.

The 25 closure lemmas. The 250-line hypothesis still stands
(`agents/tasks/LJ-1-113/lj-1.113-report.md:135-146`). Do not
fund them against this 2.40 s.

Do not fund a landing against this pad. Re-measure it at
the chosen repair.

## 6. C-42

This return is a GO at one site: `KValue` at
`src/L/Condensation.lagda.md:7380-7434`, rebuilt with
`⟨ ω ∈ gam ⟩` hypothesised and `facts` reused. It says the
record still inhabits. It does not measure a landing in
`src/`.

COUNT of `module KValue` in `src/`: **1**,
`Condensation.lagda.md:7380`. In `archive/src/`: **0**.

COUNT of applications of `KValue` at a concrete `gam` in
`src/`: **0**.

COUNT of the type `⟨ ω ∈ sucV gam ⟩` in `src/`: **1**,
`EnvSupply.lagda.md:111`. In `archive/src/`: **0**.

COUNT of the type `⟨ ω ∈ gam ⟩` in `src/`: **0**.

COUNT of the identifier `ω∈γ` in `src/`: **7**.
`EnvSupply.lagda.md` 2 (`:111`, `:146`).
`SquareLawClosed.lagda.md` 5 (`:120`, `:122`, `:123`,
`:150`, `:158`). The SquareLawClosed uses have type
`⟨ ω ∈ˢ γ ⟩` (`:119`), which under `𝒮ᵥ` is `⟨ ω ∈ γ ⟩`.
They are a different module and a different `γ`. A cure of
`KValue`'s telescope is not a measured cure of them.

COUNT of `KFactsCons` in `src/`: **14**, all in
`Condensation.lagda.md`. The one that consumes
`KValue.facts` is `consed` at `:7433-7434`. The others
consume a generic `KFacts`. A restriction of `KValue` is
not a measured cure of those.

COUNT of `TFacts.someEnv` in `src/`: still the sites
`[LJ-1.488]` counted. A home for `ω∈γ` at `KValue` is not
a measured cure of `TFacts.someEnv`. Re-measure each.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX, archived 2026-08-18". Declined. The live producer is `dev/pod/queue.toml`. This task does not consult the archived dispatch rows.
- `archive/dev/JOURNAL-archived.md:1`, read: "# Archived journal: the retired route". Declined. The retired-route journal does not bear on whether `KValue` can carry `ω ∈ gam`.
- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined. The per-episode journal is retired. The product of this task lives in this directory.
- `dev/ARCHIVE.md:1`, read: "# ARCHIVE.md: the archive registry". Declined. This task does not retire a module.
- `archive/dev/DD-archived.md:1`, read: "# THE `DD` RULING SERIES, archived in full 2026-08-18". Declined. The live rulings are `dev/pod/rulings.toml`. This task does not consult the archived DD rows.

## LITERATURE USED

- `dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the Condensation Lemma and the GCH in L". Declined as a source for a producer. Devlin 5.5 does not inhabit `kvalue-with-omega`.
- `dev/literature/truncation-and-selection.md:1`, read: "# Truncation and selection: how the two literatures pick a witness". Declined. This task adds a membership hypothesis to a frame. It does not select a truncated witness from the literature.
- `dev/literature/terms-2026-08.md:1`, read: "# The terminology dossier: fourteen renderings for the owner's ruling". Declined. No glossary term is at issue.
- `dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the rud route, pinned from the collected literature". Declined. This task measures a telescope restriction of `KValue`. It does not consult the orthodox rud digest.
- `dev/literature/glossary-review-2026-08.md:1`, read: "# Glossary review: the 119 pre-protocol entries". Declined. This task adds no glossary entry.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process from this slot.
- I did not write in `src/`.
- I did not use `ω∈γ` in any field.
- I did not restate `KValue.facts`.
- I did not import a probe.
- I did not postulate.
- I did not weaken a field.
- I did not inhabit `⟨ ω ∈ sucV gam ⟩`.
- I did not inhabit the brief's ill-typed `⟨ ω ∈ˢ gam ⟩` under `𝒮ʟ`.
- I did not write `review-of-kvalue-with-omega.md`.
- I did not choose between Repair A and Repair B.
- I did not inhabit `TFacts` or `TFacts.someEnv`.

## WHAT THE NEXT BRIEF NEEDS

W3 is GO: no src/ consumer passes a finite `gam`. The
obligation is GO: `KValue`'s record still inhabits with
`⟨ ω ∈ gam ⟩` unused on the telescope. `ω∈γ` has a home at
the only module in the chain that binds `gam`.

What a next brief can order, one at a time:

1. Land the restriction on `KValue` at
   `src/L/Condensation.lagda.md:7380-7384`, or decline it.
   The census is the evidence. Do not fund it against this
   2.40 s. Re-measure it.
2. Choose the gate. This pad took `⟨ ω ∈ gam ⟩`. SupplyEnv
   takes `⟨ ω ∈ sucV gam ⟩`. The stronger gate excludes
   `gam = ω`. Name which one the landing carries.
3. Repair A or Repair B of `[LJ-1.488]`, now with a source
   for `ω∈γ` at `KValue` if the ruling is to thread it
   down. The truncation still wants `someEnvDef` or the
   clause `let`. Do not fund that against this pad.
4. The other 27 `TFacts` fields, and then `twelve-out` /
   `twelve-back`. Do not fund them against this frame GO.
5. The 25 closure lemmas
   (`agents/tasks/LJ-1-113/lj-1.113-report.md:135-146`).

The condensation front is open for those briefs. It is open
for a landing in `src/` only after a brief names the gate
and names the consumer's two parameters.

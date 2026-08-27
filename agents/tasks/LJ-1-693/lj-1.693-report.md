# LJ-1.693 report: 𝒟ₒ-intro does not reach HierInK at the bridge stage

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.693
obligation: agents/tasks/LJ-1-693/Probe693.agda::hier-in-K-placement
verdict: **NO-GO. `hier-in-K-placement` is not inhabited.** Stage
placement through `𝒟ₒ-intro` does not construct `HierInK`. The
statement is not false. `agents/tasks/LJ-1-693/review-of-hier-in-K-placement.md`
states the stop.

The probe is green (`runs/p-2.out`, EXIT=0, 10.63 s, 783,712,256
bytes). The witness meter is 1 UNRESOLVED of 1, `probe_red=False`
(`runs/meter-obligation.out`, `missing exit=42 2.26 s`, `[NotInScope]`
at the generated witness for `hier-in-K-placement`).

**READ THESE FIVE SENTENCES BEFORE YOU QUEUE ANYTHING.**

1. **A CARVE FROM `Lset α` LANDS IN `Lset (sucV α)`, NOT IN `Lset α`.**
   `door-next` (`Probe693.agda:127-129`) is `𝒟ₒ-intro` plus
   `Lset-suc` (`src/L/Axioms/Basic.lagda.md:196`). The bridge wants
   membership in `Lset α`. The door at the bound itself is the wrong
   stage.
2. **`ThroughDoor` IS THE 𝒟ₒ-INTRO SHAPE OF `HierInK`.** Some
   `δ ∈ α` and `Door (Lset δ) (hierL β)` (`Probe693.agda:135-139`).
   `from-door` (`:141-150`) is `ThroughDoor → HierInK`. `ThroughDoor`
   is not inhabited.
3. **`AtStage` AT THAT BOUND STILL WANTS `Δ₀`.**
   `AtBound.wants-Δ₀` (`Probe693.agda:166-171`) is `imageIn`
   (`src/L/Axioms/Separation.lagda.md:225-229`). A larger stage does
   not drop the hypothesis. `LsetGraphAt` is not `Δ₀` and not `Σ₁`
   (`Probe693.agda:194-198`). `levelFo` is not `Δ₀` (`:191-192`).
4. **`HierBelowAll` WOULD PAY `HierInK`, AND IT IS STILL A HYPOTHESIS.**
   `from-HierBelow` (`Probe693.agda:221-225`) is green. `[LJ-1.536]`
   did not inhabit `HierBelowAll`. Room is not the miss:
   `steps-stay` (`:214-219`) is green.
5. **`[LJ-1.684]`'S COMPOSITION IS NOT WITHDRAWN.** Adequacy at the
   bounded graph still takes the bridge as a hypothesis. This file
   does not pay the membership that hypothesis consumes. Do not
   rebuild `adequacy-bnd`. Do not fund DOWN. Do not inhabit
   `ApproxInK`.

Written as a skeleton before any Agda beyond the predecessor read
and filled as each answer landed (C-22). No commit, no push. I wrote
only inside `agents/tasks/LJ-1-693/`. Agda ran under the caliber the
program set on this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier,
ONE Agda process at a time. I did not set `GHCRTS`. Nothing is
postulated, the delivered probe carries `--safe` and no hole, and
nothing lands in `src/`. The probe is a raw `.agda` file, so it
carries no ` ```agda ` fence, counts 0 in-fence lines, and the
ratio bar cannot fire on it.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict. W4 does not apply: no module is
retired.

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE.**
The first run loaded `Probe520` and its `src/` cone
(`runs/p-1.out`). No number here is a cold-cache number, and this
report does not bound one.

**NO HEAP WALL WAS MET ANYWHERE IN THIS TASK.** The highest peak of
any run is 783,712,256 bytes against the 2,147,483,648-byte wide cap
(`runs/p-2.out`), which is 36 percent of it. The longest Agda run is
10.63 s (`runs/p-2.out`) against the 300 s cap. The caps are
wall-clock caps enforced by a perl alarm (`runs/run.sh`).

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

The standing coder clause says: take the type from the probe that
typechecked, and the verdict from the report. If the report is NO-GO,
or names the statement FALSE, do not inhabit that type.

| piece | type | site | verdict |
|---|---|---|---|
| `HierInK` | `hierL β ∈ Lset α` | `Probe532.agda:274-277` | TYPE, green; not inhabited. Taken as the obligation type. |
| `ApproxInK` | every `ApproxAt` witness lies in `K` | `Probe532.agda:108-117` | **FALSE** (`:206-209`). Not inhabited. |
| `Pin.down` | `LsetGraphAt → graphBndAt` at one environment | `Probe688.agda:156-159` | GO as a composition. Consumes `HierInK`. Not rebuilt. |
| `HierBelow` / `HierBelowAll` | `hierL γ ∈ Lset (step 3 γ)` | `Probe536.agda:186-187`, `:354-355` | TYPE, green; not inhabited. |
| `StageHigh` | `hierL (sucV γ) ∈ Lset (step 4 γ)` | `Probe536.agda:350-352` | NO-GO at the door of `𝒟ₒ-intro`. Not inhabited. |
| `AdjoinAt.adjoin∈` | successor step of `HierBelow` | `Probe536.agda:278-280` | GO. Not rebuilt. |
| `reduction` | `HierBelowAll → StageHigh` | `Probe536.agda:357-358` | GO. Not rebuilt. |
| `no-Σ₁-graph` | `Σ₁ (LsetGraphAt w b) → ⊥*` | `Probe520.agda:202-204` | GO as a refutation. Imported, not rebuilt. |
| `adequacy-bnd` | `Lset-defines` then hypothesized DOWN | `Probe684.agda:77-83` | GO. Names `HierInK` as remaining debt. |

The 688 report is NO-GO at `hier-in-K` via DOWN, not at the type
`HierInK`. The 536 report is NO-GO at `StageHigh` via the door, not
at `HierBelow` as a type. I take those types. I do not inhabit
`ApproxInK`. I do not inhabit `StageHigh`. I do not inhabit
`hier-in-K` under the name `hier-in-K-placement`.

## 2. D-10, BEFORE THE PROOF IS PRICED

The recorded residue is stage placement, `HierBelow` / `StageHigh`,
through `𝒟ₒ-intro`, named by `[LJ-1.688]` as what a consumer of
`HierInK` must fund (`lj-1.688-report.md:220-225`).

**THE TARGET IS NOT FALSE.** Devlin 2.6(ii) is the sequence
`(L_δ | δ ≤ γ) ∈ L_α` for `γ < α` at a limit
(`dev/literature/devlin-II5.md:221-222`). The tree's `IsLimit`
(`Probe693.agda:72-75`) is successor-closure plus `∅ ∈ α`. It does
not carry `α > ω`. The tail at `ω` is `[LJ-1.519]`'s `StageLow`,
and a finite table at a finite bound is not a Tarskian or
cardinality obstruction. I did not build a term of the negation.

**THE TARGET IS NOT REACHABLE FROM 𝒟ₒ-INTRO AT THE BRIDGE STAGE.**
Carving from `Lset α` lands one successor too high (`door-next`).
Carving from an earlier stage is `ThroughDoor`, which wants a
`Formula ⟪ Lset δ ⟫ 1` whose `defSet` is `hierL β`. The only
bridge from an external formula to that inner reading is `AtStage`,
and it wants `Δ₀`. The delivered graph is not `Δ₀` and not `Σ₁`.
The graded substitute is not `Δ₀`. The successor step is paid
(`AdjoinAt`) and is not this file. The limit collection is not paid.

Corrected remaining target beside this NO-GO: `ThroughDoor`
(`Probe693.agda:135-139`), or `HierBelowAll` (`:92-93`) whose unpaid
case is `HierBelowLimit` (`Probe536.agda:408-409`). Not a graph-agreement
brief and not a DOWN construction.

C-42 does not fire. This is not a refutation of `HierInK`. No false
shape was counted. `no-Δ₀-graph` restates a grade `[LJ-1.516]` and
`[LJ-1.520]` already refuted at `LsetGraphAt`. `no-Δ₀-levelFo`
restates `[LJ-1.536]`.

D-26: a stage built as a definable power carries no generation data.
Members of `Lset α` are sets. They do not carry the approximation
`hierL` was built from. A well-founded key on the stage does not
place the table in the stage.

P-l is observed: the types name `Lset α` and `Lset δ`, which are
opaque (`src/L/Constructible.lagda.md:221-223`). They do not name
`sucV (sucV (sucV _))`. `[LJ-1.536]` walled on that presentation.
`HierBelow` keeps `step 3 γ` as 536 wrote it.

## 3. THE FLOOR, MEASURED BEFORE ANY PROOF

Coder clause, owner 2026-08-23: price the frame before the term. I
did not attempt a body for `hier-in-K-placement`. The delivered
probe is the W3 measurement: the obligation TYPE, the door at the
bridge stage, the grade, and the two reductions that take unpaid
hypotheses. That frame is green.

**THE FRAME COSTS 10.63 s AND 784 MB, AND IT DOES NOT WALL.**
`runs/p-2.out`: exit 0 at 10.63 s, peak 783,712,256 bytes. **The
obligation TYPE is well-formed.** No import trim beyond `src/` was
required. `no-Σ₁-graph` is imported from `[LJ-1.520]`. Predecessor
probes 536 and 688 were not imported: the types they delivered are
restated, each cited at the line they were read.

The first run (`runs/p-1.out`) was EXIT=42 at 2.75 s, 658,669,568
bytes, `[NoParseForApplication]` at `⟪ Lset σ ⟫↪ m` because
`⟪_⟫↪` was not in scope (`Probe693.agda:46` now). That is a new
shape, not a rerun of the same file.

| run | file | exit | wall s | peak bytes |
|---|---|---:|---:|---:|
| `p-1` | probe, `⟪_⟫↪` not in scope | 42 | 2.75 | 658,669,568 |
| `p-2` | delivered probe | 0 | 10.63 | 783,712,256 |
| meter | `witness.py --brief` | 1 | 2.26 | 605,093,888 |

The meter row is `missing`, `[NotInScope]` for `hier-in-K-placement`.
That is the designed absence.

## 4. W3, THE WIDEST UNMEASURED TERM

The brief names it: whether `𝒟ₒ-intro` reaches `HierBelow` at the
stage the bridge uses. Estimate 110 to 240 lines, basis `[LJ-1.688]`.

**NO. 𝒟ₒ-INTRO DOES NOT REACH `HierBelow` AT `Lset α`.**

- At `A = Lset α`, `door-next` lands in `Lset (sucV α)`. That is
  not `HierInK` and not `HierBelow`.
- At an earlier `δ ∈ α`, `ThroughDoor` is the whole of the extra
  premise. It is not discharged. `AtBound.wants-Δ₀` still wants
  `Δ₀` at that δ. The characterizing formula is not `Δ₀`.
- `HierBelow` itself is membership in `Lset (step 3 γ)`, which is
  `ThroughDoor` at a named finite offset. The door there is the
  same door. The successor step is paid. The limit case is not.

The estimate was for a rebuilt membership lemma from stage
placement. There is none that does not take `HierBelowAll` or
`ThroughDoor` as a hypothesis. The delivered probe is 239 lines,
104 non-blank and not a comment. The new mathematics is `door-next`,
`ThroughDoor`, `from-door`, `from-HierBelow`, and the ascription of
`AtStage` at the bound.

**WHAT THIS TERM IS NOT.** It is not `HierInK`. It is not
`StageHigh`. It is not `AdjoinAt`. It is not `Pin.down`.
`[LJ-1.536]` already has the successor step. `[LJ-1.688]` already
has DOWN. This file does not rebuild them.

## 5. W2 ANSWER

W2: write the mathematics once at a generic carrier and instantiate it.

`HierInK` already quantifies over `α` and `β`
(`Probe532.agda:274-277`, restated `Probe693.agda:77-80`). `Door`
already quantifies over the stage `A` (`Probe693.agda:103-107`).
`AtBound` instantiates `AtStage` at generic `σ`. `from-HierBelow`
and `from-door` are the same terms at every arity. Instantiation at
`n = 0` is the same term. Instantiation at `DefBodyB` is a later
consumer.

A deadline does not apply. There is no conflict with a fixed form.
Do not fund a second copy at `n = 0`. Do not fund 𝒟ₒ-intro again as
a construction of `HierInK` at a named finite offset: `from-HierBelow`
already records that reduction.

## 6. WHAT THE SHAPE RESISTED

- **What it cost.** First run 2.75 s, 659 MB, EXIT=42. Delivered
  probe 10.63 s, 784 MB. Meter 2.26 s, 605 MB. File 239 lines, 104
  code. No heap wall.
- **What the shape resisted.** 𝒟ₒ-intro as a route to the membership
  at the bridge's own stage. The door at that stage lands one
  successor too high. The door at an earlier stage wants a formula
  the tree does not supply at `Δ₀`.
- **What I had to weaken.** Nothing of the obligation type. I did
  not inhabit a smaller type and call it `hier-in-K-placement`. I
  did not take `HierBelowAll` as a hypothesis and name the consumer
  `hier-in-K-placement`.
- **What I could not close.** `HierInK` itself. `ThroughDoor`.
  `HierBelowAll`. `StageHigh`. `HierBelowLimit`.

## 7. WHAT THE NEXT BRIEF NEEDS

- **If the consumer is 681's bridge.** Take DOWN at one environment
  from `Pin.down` (`Probe688.agda:156-159`). Take `adequacy-bnd`
  (`Probe684.agda:77-83`). Do not rebuild them. Do not inhabit
  `ApproxInK`. Take `HierInK` as a HYPOTHESIS. This file does not
  pay it.
- **If the consumer is `HierInK` through 𝒟ₒ-intro.** The remaining
  target is `ThroughDoor` (`Probe693.agda:135-139`). `from-door`
  already composes it to `HierInK`. Do not fund a carve from
  `Lset α` itself: `door-next` shows that lands in `Lset (sucV α)`.
  Do not feed `AtStage` with `LsetGraphAt` or `levelFo`: the grade
  is refuted.
- **If the consumer is `HierInK` from `HierBelow`.** Take
  `from-HierBelow` (`Probe693.agda:221-225`). Do not rebuild it.
  The unpaid case is `HierBelowLimit` (`Probe536.agda:408-409`).
  The successor step is `AdjoinAt` (`Probe536.agda:278-280`).
- **If the consumer is `[LJ-1.684]`'s recipe.** Do not rebuild
  `adequacy-bnd`. The composition is still GO. Its unpaid membership
  is still unpaid. Stage placement does not discharge it.
- **Do not re-dispatch this measurement.** 𝒟ₒ-intro does not reach
  `HierInK` at the stage the bridge uses. The 110-to-240-line
  estimate was for a membership lemma written from the door. That
  lemma does not exist without `ThroughDoor` or `HierBelowAll`.
- This task changed nothing in `src/`.

## 8. PRICE

| item | measured |
|---|---|
| first run (`⟪_⟫↪` scope) | 2.75 s, 658,669,568 bytes, EXIT=42 |
| delivered probe | 10.63 s, 783,712,256 bytes, EXIT=0 |
| witness meter | 2.26 s, 605,093,888 bytes, 1 UNRESOLVED of 1, `probe_red=False` |
| file lines / code lines | 239 / 104 |
| brief estimate | 110 to 240 lines |
| in-fence lines | 0 (raw `.agda`) |
| caliber | `-A64m -I0 -M2g`, never set here |
| heap wall | none |
| `src/` edits | none |

The estimate was for a rebuilt membership from stage placement.
Nothing of 110 to 240 lines of `HierInK` was needed as a body, and
nothing of that length was written as one. The file is 239 lines
because it carries the door, the grade, and the two reductions.

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md:1` `# ORCHESTRATION: the orchestrator's operating rules`. Declined: not used. This dispatch measures a live `src/` door against a live membership, not archived dispatch rules.
- `archive/dev/DD-archived.md:1` `# THE `DD` RULING SERIES, archived in full 2026-08-18`. Declined: not used. The live W2 home is the coder slot file, not this archive.
- `archive/dev/PLAN-archived.md:1` `# ARCHIVED 2026-08-20`. Declined: not used.
- `archive/dev/STATUS-archived.md:1` `# STATUS-archived: the goal table of the internalization route`. Declined: not used.
- `archive/dev/TASKS-archived.md:1` `# Archived task index: the `L3.32-T` series`. Declined: not used.

## LITERATURE USED

- `dev/literature/level-formula-slot-roles.md:24` `| 2 | Devlin 2.6 | `G(f,α) = ∃w[K(w, ⋃ran(f)) ∧ F(w,f,α)]`; `G` says `f = (L_γ ∣ γ ≤ α)` | 2 | `w`, ONE bound, determined | `f`, `α` | SEQUENCE, ORDINAL | `_build/literature/dev2.txt:655-659` |`. Read. `HierInK` is that sequence at the tree's `hierL`, asked to lie in `Lset α`.
- `dev/literature/level-formula-slot-roles.md:35` `### 2.1 The free pair is the VALUE and the ORDINAL, in every source`. Read. The door is at a bound slot `K ≡ Lset α`, not a free pair.
- `dev/literature/glossary-review-2026-08.md:1` `# Glossary review: the 119 pre-protocol entries`. Declined: not used.
- `dev/literature/primary-sources.md:1` `# Primary sources, second round: Jensen manuscript, Devlin, Jech`. Declined: not used. Slot roles already cite those sources.
- `dev/literature/devlin-errata.md:1` `# Devlin errata: documented error classes (do-not-repeat checklist)`. Declined: not used. The term is a live membership, not a Devlin erratum.
- `dev/literature/BIBLIOGRAPHY.md:1` `# Bibliography for the rud route`. Declined: not used.

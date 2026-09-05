# LJ-1.688 report: DOWN does not reach HierInK

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.688
obligation: agents/tasks/LJ-1-688/Probe688.agda::hier-in-K
verdict: **NO-GO. `hier-in-K` is not inhabited.** DOWN at one
environment CONSUMES `HierInK` and does not construct it. The
statement is not false. `agents/tasks/LJ-1-688/review-of-hier-in-K.md`
states the stop.

The probe is green (`runs/p-2.out`, EXIT=0, 2.47 s, 607,436,800
bytes). The witness meter is 1 UNRESOLVED of 1, `probe_red=False`
(`runs/meter-obligation.out`, `missing exit=42 2.50 s`, `[NotInScope]`
at the generated witness for `hier-in-K`).

**READ THESE FIVE SENTENCES BEFORE YOU QUEUE ANYTHING.**

1. **DOWN IS THE COMPOSITION, NOT THE MEMBERSHIP.** `Pin.down`
   (`Probe688.agda:156-159`) takes `approx-down`, `step-down` and
   `witK` and returns `graphBndAt` from `LsetGraphAt`. It does not
   inhabit `HierInK`.
2. **`witK` AT THE CANONICAL WITNESS IS `HierInK`.**
   `from-HierInK` (`Probe688.agda:97-107`) transports `HierInK` along
   `fst (lookup K γ) ≡ Lset α`. That is the one-environment form
   `[LJ-1.684]` named. A BARE `∀K` form is not taken.
3. **`ApproxInK` STAYS UNINHABITED.** `[LJ-1.532]` refuted it
   (`Probe532.agda:206-209`). This file does not take that type.
4. **THE INNER FRAMES DO NOT PLACE THE TABLE.** `approx-up` /
   `step-up` and their reverses, and `powK`
   (`ProbeLJ1162A.agda:140-141`, `:211-216`), agree bounded rows with
   unbounded rows. They are hypotheses of `Down`. They are not a
   stage membership for `hierL`.
5. **UP IS NOT REBUILT.** `Graph.up` stands
   (`ProbeLJ1162A.agda:218-222`). This file writes only the reverse
   composition, with membership as a premise.

Written as a skeleton before any Agda beyond the predecessor read
and filled as each answer landed (C-22). No commit, no push. I wrote
only inside `agents/tasks/LJ-1-688/`. Agda ran under the caliber the
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
No number here is a cold-cache number, and this report does not bound
one.

**NO HEAP WALL WAS MET ANYWHERE IN THIS TASK.** The highest peak of
any run is 607,436,800 bytes against the 2,147,483,648-byte wide cap
(`runs/p-2.out`), which is 28 percent of it. The longest Agda run is
2.57 s (`runs/p-1.out`) against the 300 s cap. The caps are
wall-clock caps enforced by a perl alarm (`runs/run.sh`).

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

The standing coder clause says: take the type from the probe that
typechecked, and the verdict from the report. If the report is NO-GO,
or names the statement FALSE, do not inhabit that type.

| piece | type | site | verdict |
|---|---|---|---|
| `HierInK` | `hierL β ∈ Lset α` | `Probe532.agda:274-277` | TYPE, green; not inhabited. Taken as the obligation type. |
| `ApproxInK` | every `ApproxAt` witness lies in `K` | `Probe532.agda:108-117` | **FALSE** (`:206-209`). Not inhabited. |
| `Graph.up` | `graphBndAt → LsetGraphAt` | `ProbeLJ1162A.agda:218-222` | GO. Not rebuilt. |
| `adequacy-bnd` | `Lset-defines` then hypothesized DOWN | `Probe684.agda:77-83` | GO. Names `HierInK` as remaining debt (`lj-1.684-report.md:39-43`). |
| `HierInStageLimit` | `hierL (sucV γ) ∈ Lset α` | `Probe519.agda:148-150` | STOP. Reduced to `StageHigh` and `StageLow`. |
| `StageHigh` | `hierL (sucV γ) ∈ Lset (γ+4)` | `Probe536.agda:350-352` | NO-GO at the door of `𝒟ₒ-intro`. |
| `hier-in-stage` | `hierL δ ∈ Lset α` | `lj-1.494-report.md:66-67` | NO-GO. The tree does not bound `hierL δ` by `α`. |

The 532 report is NO-GO at `ApproxInK`, not at `HierInK`. `HierInK`
is the corrected statement that 532 left uninhabited. I take that
type. I do not inhabit `ApproxInK`. I do not inhabit `StageHigh` or
`HierInStageLimit`: those reports name the same classical fact unpaid,
and they name a door this file does not open.

## 2. D-10, BEFORE THE PROOF IS PRICED

The recorded residue is `HierInK`, named by `[LJ-1.684]` as what the
bridge still owes (`lj-1.684-report.md:39-43`) and by `[LJ-1.532]` as
the corrected membership (`Probe532.agda:274-277`).

**THE TARGET IS NOT FALSE.** Devlin 2.6(ii) is the sequence
`(L_δ | δ ≤ γ) ∈ L_α` for `γ < α` at a limit (`dev/literature/devlin-II5.md:221-222`).
The tree's `IsLimit` (`Probe688.agda:54-57`) is successor-closure
plus `∅ ∈ α`. It does not carry `α > ω`. The tail at `ω` is
`[LJ-1.519]`'s `StageLow`, and a finite table at a finite bound is
not a Tarskian or cardinality obstruction. I did not build a term of
the negation.

**THE TARGET IS NOT REACHABLE FROM DOWN.** DOWN's extra premise is
membership of the graph witness in `K` (`Probe688.agda:151`,
`:118-122`). That is the residue, restated, not a proof of it. The
inner frames do not mention `hierL`. `hasReplacementL` builds `hierL`
and discards the bound it computes
(`src/L/Axioms/Full.lagda.md:277-280`; `img∈βimg` is local at `:231`). The only door into a named stage
is `𝒟ₒ-intro` (`src/L/Constructible.lagda.md:301-304`), and the only
bridge `AtStage` requires `Δ₀`
(`agents/tasks/LJ-1-536/review-of-StageHigh.md:23-32`). `PairGraphAt`
and `LsetGraphAt` are unbounded existentials
(`src/L/Coding/Sequence.lagda.md:328-329`, `:291-292`).

Corrected remaining target beside this NO-GO: `HierBelow` /
`StageHigh`, the stage-placement fact `[LJ-1.536]` reduced to, not a
graph-agreement brief and not a DOWN construction.

C-42 does not fire. This is not a refutation of a site. No false
shape was counted.

D-26: a stage built as a definable power carries no generation data.
Members of `Lset α` are sets. They do not carry the approximation
`hierL` was built from. A well-founded key on the stage does not
place the table in the stage.

P-l is observed: the type names `Lset α`, which is opaque
(`src/L/Constructible.lagda.md:221-223`). It does not name
`sucV (sucV (sucV _))`. `[LJ-1.536]` walled on that presentation.

## 3. THE FLOOR, MEASURED BEFORE ANY PROOF

Coder clause, owner 2026-08-23: price the frame before the term. I
did not attempt a body for `hier-in-K`. The delivered probe is the
W3 measurement: the obligation TYPE, the one-environment packaging,
and DOWN as a composition with membership as a premise. That frame
is green.

**THE FRAME COSTS 2.47 s AND 607 MB, AND IT DOES NOT WALL.**
`runs/p-2.out`: exit 0 at 2.47 s, peak 607,436,800 bytes. **The
obligation TYPE is well-formed.** No import trim beyond `src/` was
required. Predecessor probes were not imported.

The first run (`runs/p-1.out`) was EXIT=42 at 2.57 s, 605,421,568
bytes, `[NotInScope] sucV`. The import was taken from
`InfinitySet` (`Probe688.agda:36-37`). That is a new shape, not a
rerun of the same file.

| run | file | exit | wall s | peak bytes |
|---|---|---:|---:|---:|
| `p-1` | probe, `sucV` not in scope | 42 | 2.57 | 605,421,568 |
| `p-2` | delivered probe | 0 | 2.47 | 607,436,800 |
| meter | `witness.py --brief` | 1 | 2.50 | 596,688,896 |

The meter row is `missing`, `[NotInScope]` for `hier-in-K`. That is
the designed absence.

## 4. W3, THE WIDEST UNMEASURED TERM

The brief names it: whether DOWN at one environment reaches
`HierInK`. Estimate 100 to 220 lines, basis `[LJ-1.684]`.

**NO. DOWN DOES NOT REACH `HierInK`.**

`Pin.down` (`Probe688.agda:156-159`) is the reverse of `Graph.up`
at one environment, `K` a slot. It is one `∃-down`
(`Probe688.agda:118-122`, from `ProbeLJ1162A.agda:69-73`). The extra
premise `witK` is membership of the witness in `K`.

- If the witness is arbitrary, `witK` is `ApproxInK`, which is FALSE.
- If the witness is `hierL`, `witK` is `HierInKAt`, and
  `from-HierInK` (`Probe688.agda:97-107`) is `HierInK` along `qK`.

DOWN therefore takes `HierInK` as input. It does not pay it. The
estimate was for a rebuilt membership lemma. There is none. The
delivered probe is 172 lines, 84 non-blank and not a comment. The
new mathematics is the one-environment packaging and the reverse
composition.

**WHAT THIS TERM IS NOT.** It is not `HierInK`. It is not
`StageHigh`. It is not `AdjoinAt`. `[LJ-1.536]` already has the
successor step of Devlin's bound (`Probe536.agda:357-358`). This
file does not rebuild it.

## 5. W2 ANSWER

W2: write the mathematics once at a generic carrier and instantiate it.

`HierInK` already quantifies over `α` and `β`
(`Probe532.agda:274-277`, restated `Probe688.agda:59-62`). `GraphB`
already quantifies over the two leaves
(`src/L/Condensation.lagda.md:2486-2493`). This probe instantiates
DOWN at generic `m`, `ψs`, `ψa`, `w`, `b`, `K`, and one environment
`γ`. Instantiation at `n = 0` is the same term. Instantiation at
`DefBodyB` is LevelHood's instance and a later consumer.

A deadline does not apply. There is no conflict with a fixed form.
Do not fund a second copy at `n = 0`. Do not fund DOWN again as a
construction of `HierInK`.

## 6. WHAT THE SHAPE RESISTED

- **What it cost.** Probe 2.47 s, 607 MB. Meter 2.50 s, 597 MB.
  File 172 lines, 84 code. No heap wall.
- **What the shape resisted.** DOWN as a route to the membership.
  The extra premise of `∃-down` IS the membership. The inner frames
  do not discharge it.
- **What I had to weaken.** Nothing of the obligation type. I did
  not inhabit a smaller type and call it `hier-in-K`. I did not
  take `HierInK` as a hypothesis and name the consumer `hier-in-K`.
- **What I could not close.** `HierInK` itself. `StageHigh`.
  `HierBelowAll`. The `DefBodyB` instance.

## 7. WHAT THE NEXT BRIEF NEEDS

- **If the consumer is 681's bridge.** Take DOWN at one environment
  from `Pin.down` (`Probe688.agda:156-159`). Do not rebuild it. Do
  not inhabit `ApproxInK`. Take `HierInK` as a HYPOTHESIS, the way
  `[LJ-1.684]` took the bridge as a hypothesis. The inner frames
  remain hypotheses until a later brief discharges them.
- **If the consumer is `HierInK`.** Do not fund DOWN. The residue
  is stage placement: `HierBelow` / `StageHigh`
  (`Probe536.agda:186-187`, `:350-352`). The door is `𝒟ₒ-intro` with
  `AtStage`, and the characterizing formula is not `Δ₀`. The
  successor step is paid (`AdjoinAt`, `Probe536.agda:278-280`). The
  limit collection is not.
- **If the consumer is `⟨δ ⊨ levelHoodB⟩`.** Row six still owes the
  canonical witness in `K`. This file does not pay it.
- **Do not re-dispatch this measurement.** DOWN does not reach
  `HierInK`. The 100-to-220-line estimate was for a membership
  lemma written from the graph reverse. That lemma does not exist,
  because the reverse consumes the lemma.
- This task changed nothing in `src/`.

## 8. PRICE

| item | measured |
|---|---|
| first run (`sucV` scope) | 2.57 s, 605,421,568 bytes, EXIT=42 |
| delivered probe | 2.47 s, 607,436,800 bytes, EXIT=0 |
| witness meter | 2.50 s, 596,688,896 bytes, 1 UNRESOLVED of 1, `probe_red=False` |
| file lines / code lines | 172 / 84 |
| brief estimate | 100 to 220 lines |
| in-fence lines | 0 (raw `.agda`) |
| caliber | `-A64m -I0 -M2g`, never set here |
| heap wall | none |
| `src/` edits | none |

The estimate was for a rebuilt membership. DOWN does not write one.
Nothing of 100 to 220 lines of `HierInK` was needed, and nothing of
that length was written.

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md:1` `# ORCHESTRATION: the orchestrator's operating rules`. Declined: not used. This dispatch measures a live `src/` membership against a live graph reverse, not archived dispatch rules.
- `archive/dev/PLAN-archived.md:1` `# ARCHIVED 2026-08-20`. Declined: not used.
- `archive/dev/DD-archived.md:1` `# THE `DD` RULING SERIES, archived in full 2026-08-18`. Declined: not used. The live W2 home is the coder slot file, not this archive.
- `archive/dev/STATUS-archived.md:1` `# STATUS-archived: the goal table of the internalization route`. Declined: not used.
- `archive/dev/TASKS-archived.md:1` `# Archived task index: the `L3.32-T` series`. Declined: not used.

## LITERATURE USED

- `dev/literature/level-formula-slot-roles.md:24` `| 2 | Devlin 2.6 | `G(f,α) = ∃w[K(w, ⋃ran(f)) ∧ F(w,f,α)]`; `G` says `f = (L_γ ∣ γ ≤ α)` | 2 | `w`, ONE bound, determined | `f`, `α` | SEQUENCE, ORDINAL | `_build/literature/dev2.txt:655-659` |`. Read. `HierInK` is that sequence at the tree's `hierL`, asked to lie in `Lset α`.
- `dev/literature/level-formula-slot-roles.md:35` `### 2.1 The free pair is the VALUE and the ORDINAL, in every source`. Read. The one-environment form keeps `K` as a bound slot, not a free pair.
- `dev/literature/glossary-review-2026-08.md:1` `# Glossary review: the 119 pre-protocol entries`. Declined: not used.
- `dev/literature/primary-sources.md:1` `# Primary sources, second round: Jensen manuscript, Devlin, Jech`. Declined: not used. Slot roles already cite those sources.
- `dev/literature/devlin-errata.md:1` `# Devlin errata: documented error classes (do-not-repeat checklist)`. Declined: not used. The term is a live membership, not a Devlin erratum.
- `dev/literature/BIBLIOGRAPHY.md:1` `# Bibliography for the rud route`. Declined: not used.

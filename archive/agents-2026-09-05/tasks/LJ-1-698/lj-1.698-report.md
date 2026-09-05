# LJ-1.698 report: the door the corrected membership goes through

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.698
obligation: agents/tasks/LJ-1-698/Probe698.agda::through-door
verdict: **NO-GO. `through-door` is not inhabited.** The statement is
not false. `𝒟ₒ-intro` fires on a Δ₀ presentation of the delivered
pair-graph. The carved set is not identified with `hierL`, and the
bounding stage is not shown to lie in the bridge's `α`.
`agents/tasks/LJ-1-698/review-of-through-door.md` states the stop.

The probe is green (`runs/p-7.out`, EXIT=0, 18.08 s, 801,521,664
bytes). The witness meter is 1 UNRESOLVED of 1, `probe_red=False`
(`runs/meter-obligation.out`, `missing exit=42 2.23 s`, `[NotInScope]`
at the generated witness for `through-door`).

**READ THESE FIVE SENTENCES BEFORE YOU QUEUE ANYTHING.**

1. **THE EMPTY TABLE IS DEFINABLE BY `⊥̇`.** `empty-door`
   (`Probe698.agda:173-177`) is `Door (Lset σ) (hierL ∅)` at a generic
   stage. `empty-in-limit` (`Probe698.agda:184-185`) is `∅ ∈ α` from `IsLimit`.
   The zero case of ThroughDoor is not the miss.
2. **`PairGraphAt` RELATIVIZED IS `Δ₀`.** `recordedΔ₀`
   (`Probe698.agda:87-88`) is `Δ₀-relativize` applied to the delivered
   pair-graph, bound by the ordinal
   (`src/L/Coding/Sequence.lagda.md:328-329`,
   `src/FOL/Manipulation/Relativize.lagda.md:72`). This is the
   differently presented `Δ₀` formula `[LJ-1.693]`'s critic did not
   exclude (`agents/tasks/LJ-1-693/review-of-LJ-1-693-1.md:125-129`).
3. **`mkBoundedFo` BOUNDS THAT FORMULA, AND `𝒟ₒ-INTRO` FIRES ON THE
   LIFT.** `bound-of` (`Probe698.agda:97-101`) is total.
   `Carved.carved-door` (`Probe698.agda:128-129`) is `Door (Lset σ) carved` at
   `σ = fst (bound-of γ …)`. The door opens on that set.
4. **THAT IS NOT ThroughDoor.** ThroughDoor wants
   `Door (Lset δ) (hierL β)` with `δ ∈ α`. `carved ≡ hierL γ` is not
   proved. `fst (bound-of γ) ∈ α` is not proved. Do not retire the
   `𝒟ₒ-intro` route: the door opened on an unidentified set.
5. **`[LJ-1.684]`'S COMPOSITION IS NOT WITHDRAWN.** Adequacy at the
   bounded graph still takes the bridge as a hypothesis. This file
   does not pay the membership that hypothesis consumes. Do not
   rebuild `adequacy-bnd`. Do not fund DOWN. Do not inhabit
   `ApproxInK`.

Written as a skeleton before any Agda beyond the predecessor read
and filled as each answer landed (C-22). No commit, no push. I wrote
only inside `agents/tasks/LJ-1-698/`. Agda ran under the caliber the
program set on this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier,
ONE Agda process at a time. I did not set `GHCRTS`. Nothing is
postulated, the delivered probe carries `--safe` and no hole, and
nothing lands in `src/`. The probe is a raw `.agda` file, so it
carries no fence, counts 0 in-fence lines, and the ratio bar cannot
fire on it.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict. W4 does not apply: no module is
retired.

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE
AFTER `runs/floor-1.out`, EXCEPT THE FLOOR ROW ITSELF.** The floor
loaded `Probe693` and its `src/` cone (`runs/floor-1.out`). No number
here is a cold-cache number except that row, and this report does not
bound a second cold run.

**NO HEAP WALL WAS MET ANYWHERE IN THIS TASK.** The highest peak of
any run is 807,747,584 bytes against the 2,147,483,648-byte wide cap
(`runs/p-6.out`), which is 37 percent of it. The longest Agda run is
18.30 s (`runs/p-6.out`) against the 300 s and 600 s caps. The caps
are wall-clock caps enforced by a perl alarm (`runs/run.sh`).

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

The standing coder clause says: take the type from the probe that
typechecked, and the verdict from the report. If the report is NO-GO,
or names the statement FALSE, do not inhabit that type.

| piece | type | site | verdict |
|---|---|---|---|
| `ThroughDoor` | some `δ ∈ α` and `Door (Lset δ) (hierL β)` | `Probe693.agda:135-139` | TYPE, green; not inhabited. Taken as the obligation type. |
| `from-door` | `ThroughDoor → HierInK` | `Probe693.agda:141-150` | GO as a composition. Not rebuilt. |
| `HierInK` | `hierL β ∈ Lset α` | `Probe693.agda:77-80` | TYPE, green; not inhabited. |
| `ApproxInK` | every `ApproxAt` witness lies in `K` | `Probe532.agda:108-117` | **FALSE** (`:206-209`). Not inhabited. |
| `Pin.down` | `LsetGraphAt → graphBndAt` at one environment | `Probe688.agda:156-159` | GO as a composition. Consumes `HierInK`. Not rebuilt. |
| `adequacy-bnd` | `Lset-defines` then hypothesized DOWN | `Probe684.agda:77-83` | GO. Names `HierInK` as remaining debt. |
| `HierBelow` / `HierBelowAll` | `hierL γ ∈ Lset (step 3 γ)` | `Probe536.agda:186-187`, `:354-355` | TYPE, green; not inhabited. |
| `AdjoinAt.adjoin∈` | successor step of `HierBelow` | `Probe536.agda:278-280` | GO. Not rebuilt. |
| `LimitDefinableIH` | `Door (Lset γ) (hierL γ)` from tables below | `Probe579.agda:430-433` | TYPE, green; not inhabited. |
| `hier-in-K-placement` | `HierInK` through `𝒟ₒ-intro` | `Probe693.agda` | **NO-GO**. Not inhabited. The remaining target is this type. |

The 693 report is NO-GO at `hier-in-K-placement`, not at the type
`ThroughDoor`. I take that type. I do not inhabit `ApproxInK`. I do
not rebuild `Pin.down`. I do not rebuild `adequacy-bnd`.

## 2. D-10, BEFORE THE PROOF IS PRICED

The recorded residue is `ThroughDoor` (`Probe693.agda:135-139`).

**THE TARGET IS NOT FALSE.** Devlin 2.6(ii) is the sequence
`(L_δ | δ ≤ γ) ∈ L_α` for `γ < α` at a limit
(`dev/literature/devlin-II5.md:221-222`). Slot roles name the same
sequence (`dev/literature/level-formula-slot-roles.md:24`). The tree's
`IsLimit` (`Probe693.agda:72-75`) is successor-closure plus `∅ ∈ α`.
It does not carry `α > ω`. A finite table at a finite bound is not a
Tarskian or cardinality obstruction. I did not build a term of the
negation.

**THE TARGET IS NOT INHABITED.** The empty case is paid. The
relativized pair-graph is `Δ₀` and its constants are bounded, and
`𝒟ₒ-intro` fires on the lift. The two unpaid rows are the
identification of the carved set with the table, and the membership
of the bounding stage in `α`.

Corrected remaining target beside this NO-GO:
`Carved.carved ≡ fst (hierL γ hγ oγ)` together with
`⟨ fst (bound-of γ oγ hγ) ∈ α ⟩` for `β ∈ α`, or equivalently
`LimitDefinableIH` (`Probe579.agda:430-433`). Not a graph-agreement
brief and not a DOWN construction. Not another `Δ₀` check.

C-42 does not fire. This is not a refutation of `ThroughDoor`. No
false shape was counted.

D-26: a stage built as a definable power carries no generation data.
Members of `Lset δ` are sets. A well-founded key on the stage does
not place the table in the stage. `recordedFo` does not use the
table as a constant. It uses the ordinal as a constant.

P-l is observed: types name `Lset α` and `Lset δ`, which are opaque
(`src/L/Constructible.lagda.md:221-223`). They do not name
`sucV (sucV (sucV _))`. `Carved` is parameterized by a variable
stage `γ`.

## 3. THE FLOOR, MEASURED BEFORE ANY PROOF

Coder clause, owner 2026-08-23: price the frame before the term. A
hole is not available under `--safe`. The floor is the obligation
TYPE, formed, in the trimmed frame (`runs/floor-1.out`).

**THE FRAME COSTS 11.64 s AND 797 MB, AND IT DOES NOT WALL.**
`runs/floor-1.out`: exit 0 at 11.64 s, peak 797,409,280 bytes. **The
obligation TYPE is well-formed.** No import trim beyond `src/` was
required. `ThroughDoor` is imported from the probe that typechecked
it (`Probe693.agda:135-139`).

The next runs added the empty door, then the `Δ₀` ascription, then
`mkBoundedFo`, then the carved door. Each is a new shape.

| run | file | exit | wall s | peak bytes |
|---|---|---:|---:|---:|
| `floor-1` | type only, `ThroughDoor` imported | 0 | 11.64 | 797,409,280 |
| `p-1` | `∅` not in `V.Model` | 42 | 2.31 | 608,534,528 |
| `p-2` | `tt` not in scope | 42 | 1.71 | 608,419,840 |
| `p-3` | `UnequalSorts` on `Recorded` | 42 | 2.78 | 610,435,072 |
| `p-4` | `empty-door` and `recordedΔ₀` | 0 | 5.43 | 705,003,520 |
| `p-5` | `bound-of` | 0 | 7.31 | 718,520,320 |
| `p-6` | `Carved.carved-door` | 0 | 18.30 | 807,747,584 |
| `p-7` | delivered probe | 0 | 18.08 | 801,521,664 |
| meter | `witness.py --brief` | 1 | 2.29 | 604,028,928 |

The meter row is `missing`, `[NotInScope]` for `through-door`.
That is the designed absence.

## 4. W3, THE WIDEST UNMEASURED TERM

The brief names it: whether `𝒟ₒ-intro` reaches the door at the
bridge's stage. Estimate 100 to 220 lines, basis `[LJ-1.693]`.

**`𝒟ₒ-INTRO` REACHES A DOOR AT THE BOUND OF THE FORMULA'S CONSTANTS.
IT DOES NOT REACH ThroughDoor.**

- At `β = ∅`, `empty-door` is `Door (Lset σ) (hierL ∅)` at a generic
  stage. `empty-in-limit` places `∅` in every `IsLimit` bound.
- At a general `γ`, `recordedFo` is `PairGraphAt` bound by the
  ordinal. `recordedΔ₀` (`Probe698.agda:87-88`) is its relativization, `Δ₀`. `bound-of`
  (`:97-101`) is `mkBoundedFo` of that formula, 7.31 s and 719 MB, not a wall.
- `Carved.carved-door` (`:128-129`) is `𝒟ₒ-intro` on the lift of that formula at
  `σ = fst (bound-of γ …)`. 18.30 s and 808 MB. The door opens on
  `carved`.
- ThroughDoor wants that carved set to be `hierL β` and that `σ` to
  be a member of `α`. Neither row is paid.

The estimate was for a rebuilt membership lemma from the door. The
delivered probe is 193 lines, 101 non-blank and not a comment. The
new mathematics is `recordedFo`, `recordedΔ₀`, `bound-of`, `Carved`,
and `empty-door`.

**WHAT THIS TERM IS NOT.** It is not `ThroughDoor`. It is not
`HierInK`. It is not `AdjoinAt`. It is not `Pin.down`.
`[LJ-1.536]` already has the successor step. `[LJ-1.688]` already
has DOWN. This file does not rebuild them.

## 5. W2 ANSWER

W2: write the mathematics once at a generic carrier and instantiate it.

`ThroughDoor` already quantifies over `α` and `β`
(`Probe693.agda:135-139`). `Door` already quantifies over the stage
`A`. `recordedFo` is generic in the carrier `γ : S`. `empty-door` is
generic in the stage `σ`. `Carved` is generic in `γ`. Instantiation
at `n = 0` is the same term. Instantiation at `DefBodyB` is a later
consumer.

A deadline does not apply. There is no conflict with a fixed form.
Do not fund a second copy at `n = 0`. Do not fund a second `Δ₀`
ascription of `relativize PairGraphAt`.

## 6. WHAT THE SHAPE RESISTED

- **What it cost.** Floor 11.64 s, 797 MB, EXIT=0. Delivered
  probe 18.08 s, 802 MB. Meter 2.29 s, 604 MB. File 193 lines, 101
  code. No heap wall.
- **What the shape resisted.** The identification of the carved set
  with `hierL`, and the membership of `mkBoundedFo`'s stage in `α`.
  `AtStage.imageIn` wants outer satisfaction of the relativized
  formula. `Lset-defines` is the unbounded graph. The two readings
  are not connected here.
- **What I had to weaken.** Nothing of the obligation type. I did
  not inhabit `Door (Lset σ) carved` and name it `through-door`. I
  did not take `HierBelowAll` as a hypothesis and name the consumer
  `through-door`.
- **What I could not close.** `ThroughDoor` itself. The equation
  `Carved.carved ≡ fst (hierL γ hγ oγ)`. The membership
  `fst (bound-of γ oγ hγ) ∈ α`. `HierBelowAll`. `LimitDefinableIH`.

## 7. WHAT THE NEXT BRIEF NEEDS

- **If the consumer is 681's bridge.** Take DOWN at one environment
  from `Pin.down` (`Probe688.agda:156-159`). Take `adequacy-bnd`
  (`Probe684.agda:77-83`). Do not rebuild them. Do not inhabit
  `ApproxInK`. Take `HierInK` as a HYPOTHESIS. This file does not
  pay it.
- **If the consumer is `ThroughDoor` through 𝒟ₒ-intro.** Take
  `empty-door` (`Probe698.agda:173-177`) for the zero case. Take
  `recordedΔ₀` (`:87-88`) and `bound-of` (`:97-101`) and
  `Carved.carved-door` (`:128-129`) as the door on an unidentified
  set. The remaining rows are `Carved.carved ≡ fst (hierL γ hγ oγ)`
  and `⟨ fst (bound-of γ oγ hγ) ∈ α ⟩`. Do not re-check that
  `relativize PairGraphAt` is `Δ₀`. Do not re-run `mkBoundedFo` as
  the obligation.
- **If the consumer is `HierInK` from `HierBelow`.** Take
  `from-HierBelow` (`Probe693.agda:221-225`). Do not rebuild it.
  The unpaid case is `HierBelowLimit` (`Probe536.agda:408-409`) or
  `LimitDefinableIH` (`Probe579.agda:430-433`). The successor step
  is `AdjoinAt` (`Probe536.agda:278-280`).
- **If the consumer is `[LJ-1.684]`'s recipe.** Do not rebuild
  `adequacy-bnd`. The composition is still GO. Its unpaid membership
  is still unpaid.
- **Do not re-dispatch this measurement.** `𝒟ₒ-intro` reaches a
  door at the bound of the pair-graph's constants. It does not
  reach ThroughDoor until the carved set is the table and that
  bound lies in `α`. The 100-to-220-line estimate was for a
  membership lemma written from the door. The identification was
  not written.
- This task changed nothing in `src/`.

## 8. PRICE

| item | measured |
|---|---|
| floor (type only) | 11.64 s, 797,409,280 bytes, EXIT=0 |
| first run (`∅` scope) | 2.31 s, 608,534,528 bytes, EXIT=42 |
| delivered probe | 18.08 s, 801,521,664 bytes, EXIT=0 |
| witness meter | 2.29 s, 604,028,928 bytes, 1 UNRESOLVED of 1, `probe_red=False` |
| file lines / code lines | 193 / 101 |
| brief estimate | 100 to 220 lines |
| in-fence lines | 0 (raw `.agda`) |
| caliber | `-A64m -I0 -M2g`, never set here |
| heap wall | none |
| `src/` edits | none |

The estimate was for a rebuilt membership from the door. The file
is 193 lines because it carries the empty door, the `Δ₀` ascription,
the bound, and the carved door. It does not carry a body for
`through-door`.

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md:1` `# ORCHESTRATION: the orchestrator's operating rules`. Declined: not used. This dispatch measures a live `src/` door against a live membership, not archived dispatch rules.
- `archive/dev/DD-archived.md:1` `# THE `DD` RULING SERIES, archived in full 2026-08-18`. Declined: not used. The live W2 home is the coder slot file, not this archive.
- `archive/dev/PLAN-archived.md:1` `# ARCHIVED 2026-08-20`. Declined: not used.
- `archive/dev/TASKS-archived.md:1` `# Archived task index: the `L3.32-T` series`. Declined: not used.
- `archive/dev/STATUS-archived.md:1` `# STATUS-archived: the goal table of the internalization route`. Declined: not used.

## LITERATURE USED

- `dev/literature/level-formula-slot-roles.md:24` `| 2 | Devlin 2.6 | `G(f,α) = ∃w[K(w, ⋃ran(f)) ∧ F(w,f,α)]`; `G` says `f = (L_γ ∣ γ ≤ α)` | 2 | `w`, ONE bound, determined | `f`, `α` | SEQUENCE, ORDINAL | `_build/literature/dev2.txt:655-659` |`. Read. `ThroughDoor` is that sequence at the tree's `hierL`, asked to be a definable subset of an earlier stage.
- `dev/literature/level-formula-slot-roles.md:35` `### 2.1 The free pair is the VALUE and the ORDINAL, in every source`. Read. The door is at a bound slot, not a free pair.
- `dev/literature/glossary-review-2026-08.md:1` `# Glossary review: the 119 pre-protocol entries`. Declined: not used.
- `dev/literature/BIBLIOGRAPHY.md:1` `# Bibliography for the rud route`. Declined: not used.
- `dev/literature/primary-sources.md:1` `# Primary sources, second round: Jensen manuscript, Devlin, Jech`. Declined: not used. Slot roles already cite those sources.
- `dev/literature/fine-structure.md:1` `# Fine structure: projecta, standard codes, the reductions, and their dependencies`. Declined: not used. The term is a live membership door, not a projectum.

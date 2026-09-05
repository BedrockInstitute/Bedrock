# LJ-1.725-SPLIT report: `stage-read`, the reverse inclusion's missing input

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.725-SPLIT
obligation: agents/tasks/LJ-1-725-SPLIT/Probe725Split.agda::stage-read
verdict: **STOP, STATED.** The name `stage-read` is exported as its TYPE
(verbatim from `agents/tasks/LJ-1-725/Probe725.agda:251-258`) and is not
inhabited. `review-of-stage-read.md` states the stop at the failing
site. What IS delivered and green: `Lset-trans-set` (the corrected
target's reusable half 1, one `PT.rec` over the landed `Lset-out` and
`𝒟ₒ∋⊆` plus `Lset-in`) and `ord-in-Lset` (`[LJ-1.724]`'s cure,
re-measured here from the landed `L.Ordinal.Stages`). The probe
TYPECHECKS: see the run table below. Nothing is postulated, the probe
carries `--safe` and no hole, nothing lands in `src/`, and the names
`carved-is-hier` and `table-sat` are absent.

## 0. THE PREDECESSOR QUESTION

| piece | taken from | verdict there | use here |
|---|---|---|---|
| `stage-read`'s type | agents/tasks/LJ-1-725/Probe725.agda:251-258 | 725 stated it, did not inhabit it | transcribed verbatim |
| the membrane finding | agents/tasks/LJ-1-724/lj-1.724-report.md (verdict, item 4) | 724 NO-GO: DefAt membranes demand codes inside `Lset γ` | the stop's measured basis |
| `ord-in-Lset` | agents/tasks/LJ-1-724/Probe724.agda:67-71 | compiles there | re-measured here from `L.Ordinal.Stages` (that probe is not in this worktree) |
| half 1 of the corrected target | agents/tasks/LJ-1-725/review-of-carved-is-hier.md (THE CORRECTED TARGET) | 725 NO-GO review | `Lset-trans-set`, delivered |

## 1. WHAT WAS BUILT

1. `Lset-trans-set` (Probe725Split.agda, section 1). REAL. Members of
   members of `Lset γ` lie in `Lset γ`: one `PT.rec` over `Lset-out`,
   closed by the landed `𝒟ₒ∋⊆` (the operator's refinement) and
   `Lset-in`. The two-step iterate `Lset-trans-set²` is what the
   spine's recorded-pair sites consume (a pair's components sit two
   membership steps below a member of the bound), and iteration is
   what replaces the false shortcut through pair-transitivity.
2. `ord-in-Lset` (section 2). REAL. A member of an ordinal lies in the
   ordinal's own stage: `Lset-cumul` plus `ord∈Lset-suc`, both landed
   in `src/L/Ordinal/Stages.lagda.md`. This is the fact that puts
   every member of `fst u` inside the relativization's bound.
3. `stage-read` (section 3). STATED, NOT INHABITED.

## 2. THE FLOOR

The probe's frame is the import cone of `L.Coding.Sequence` and
`L.Axioms.Basic` (a sub-cone of [LJ-1.725]'s, which paid 23.55 s for
its verdict run with Probe698 included); the probe's own rows are the
two lemmas above, no induction over satisfaction. Per the heavy-object
rule the floor was priced first: the file is its own floor, because
every delivered row is an assembly of landed readings. Runs p-1 to
p-6 restructured the file six times, each fixing one distinct defect,
and no failing run was ever repeated unchanged. p-8 is the verdict
run on the delivered bytes. Peak 374,603,776 B is 17 percent of the
2,147,483,648-byte wide cap;
no heap wall was met and no run timed out. The wall times are warm on
the pod's shared interface cache, like [LJ-1.725]'s own verdict run;
the number this dispatch reports is the number the run measured.
| run | wall | peak | note |
|---|---|---|---|
| p-1 | 1.75 s | 372,588,544 B | scope error: `𝒟ₒ` used but not imported |
| p-2 | 1.75 s | 373,882,880 B | wrong closing lemma: the step needs `Lset-mono`, not `Lset-in` |
| p-3 | 1.75 s | 372,588,544 B | `Lset-mono` missing from the import list |
| p-4 | 1.53 s | 374,652,928 B | `mem-ord`'s implicit stage not injective for the unifier; metas blocked |
| p-5 | 1.74 s | 372,555,776 B | field is mixfix `_∈ˢ_`; the rename missed |
| p-6 | 1.77 s | 374,587,392 B | same metas as p-4, still implicit |
| p-7 | 1.87 s | 374,587,392 B | green; comment pass after re-read |
| p-8 (verdict) | **1.77 s** | **374,603,776 B** | **EXIT=0, green, delivered bytes** |

## 3. WHERE THE SHAPE RESISTED, AND THE STOP

The site is in `review-of-stage-read.md`, one paragraph summary here.
The backward half of `fst z ≡ Lset (fst u)` must feed the relativized
`Step (suc w) (suc b) zero` at a member of `Lset (fst u)`; that
conjunct's payload `∃̇∃̇∃̇ (StepBody b f)` carries `DefAt zero (suc
zero)`, and under the bound `relativize (LsetS γ oγ)` its three
existential witnesses must lie inside `Lset γ`. The true witnesses are
the coding constructions (`keyS`, `Sat`, the environment sets), and no
landed lemma bounds them by the carrier's stage: `CodeSet`'s
`smallAny` returns an unspecified stage, and `[LJ-1.724]` measured the
same membrane class failing outright below a fixed finite stage. Two
things were checked and are NOT the wall: (a) the residual conjunct's
truth is not refuted here, the two-set counterexample this dispatch
first priced dies because `domAt`'s domain slot is `fst u` and the
bound cannot hold the required recorded pair at small stages; (b) the
syntax bridge is not the wall, `relativize-correct` is landed and is
not re-funded.

## 4. W3 ANSWER

The brief's W3: whether `Lset-trans-set` plus the un-guarding spine
close `stage-read`, estimated 80 to 180 lines. Answer: **half 1
closes at 6 lines and is delivered; the spine does not close
stage-read.** The forward inclusion's extraction sites all discharge
by `Lset-trans-set` (iterated) and `ord-in-Lset`; the backward
inclusion's fill dies at the DefAt membrane, and the missing lemma is
not a spine conversion but a stage bound for the coding constructions
relative to the carrier. Price above the estimate; the corrected
target is in the review.

## 5. W2 ANSWER

Both delivered lemmas are stated once at the generic carrier (`γ` is a
parameter of each; no sibling proof is duplicated), and each reuses
the landed readings (`Lset-out`, `Lset-in`, `𝒟ₒ∋⊆`, `Lset-cumul`,
`ord∈Lset-suc`, `mem-ord`) with no re-derivation. `stage-read` itself
is transcribed once, verbatim. No deadline forced a fixed form.

## 6. WHAT THE NEXT BRIEF NEEDS

1. Fund the stage bound first, as its own obligation: for a carrier
   `A` with `⟨ fst A ∈ Lset γ ⟩` of the right shape, the coding
   constructions over `A` (`keyS A ψ`, `Sat A (toS ψ)`, the
   environment sets) land inside `Lset γ` (or inside a stated finite
   successor of the carrier's stage, with the successor arithmetic
   against `γ` landed alongside). Until that lemma lands, no spine
   assembly can feed the backward conjunct, and any brief that prices
   the spine below the membrane repeats this stop.
2. After the stage bound: the backward half is one assembly per the
   review's reconstruction; the forward half's cost is the bounded
   `DefAt` read (the `qd` equation of `Sequence.readBody` under the
   bound), which the same stage bound also dissolves. Price both after
   the bound is measured, not before.
3. Do not re-fund `relativize-correct`, the graph census, or
   `Lset-trans-set`/`ord-in-Lset`: all four are green and the two new
   ones are reusable from this probe's sections 1 and 2.
4. `table-sat` stays `[LJ-1.724]`'s NO-GO; its corrected scope is the
   mathematician's to settle, and `carved-is-hier-from` waits on both
   that ruling and this stop.

## 7. PRICE

| item | value |
|---|---|
| Agda wall, verdict run | 1.77 s (`runs/p-8.out`) |
| peak, verdict run | 374,603,776 B, 17 percent of cap |
| runs this dispatch | p-1, p-2, p-3, p-4, p-5, p-6, p-7, p-8 |
| in-file / in-fence lines | 126 / 0 (raw `.agda`) |
| brief estimate | 80 to 180 lines (W3) |
| caliber | `-A64m -I0 -M2g`, never set here |
| heap wall | none |
| `src/` edits | none |

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md:1` `# ORCHESTRATION: the orchestrator's operating rules`. Declined: not read. This dispatch measures its own probe; no archived dispatching rule bears on the stop.
- `archive/dev/DD-archived.md:1` `# THE \`DD\` RULING SERIES, archived in full 2026-08-18`. Declined: not read. The coder clauses this dispatch answers to live in the slot file and the brief, not in the archive.
- `archive/dev/PLAN-archived.md:1` `# ARCHIVED 2026-08-20`. Declined: not read. The live screen is `dev/pod/screen.toml` and the live direction is `dev/pod/direction.md`; this task follows those.
- `archive/dev/STATUS-archived.md:1` `# STATUS-archived: the goal table of the internalization route`. Declined: not read. The route this task sits on is the live queue's, not the archived table's.
- `archive/dev/TASKS-archived.md:1` `# Archived task index: the \`L3.32-T\` series`. Declined: not read. The `L3.32-T` series predates the POD and shares no obligation with LJ-1.725-SPLIT.

## LITERATURE USED

- `dev/literature/devlin-II5.md:1` `# Devlin II.5: the Condensation Lemma and the GCH in L`. Read. This is the primary-source digest for the lemma family the corrected target belongs to (stages of `L` against ordinals, condensation); it is the standing record the next brief's stage-bound obligation should be read against.
- `dev/literature/glossary-review-2026-08.md`: declined, not read. A raw `.agda` probe carries no translation surface.
- `dev/literature/devlin-errata.md`: declined, not read. This dispatch cites no Devlin page; the errata scope is the literature team's to keep.
- `dev/literature/primary-sources.md`: declined, not read. The fetch map is the literature team's record; this dispatch fetches nothing.
- `dev/literature/level-formula-slot-roles.md`: declined, not read. [LJ-1.725] read it for the graph's slot census; this dispatch re-funds no census.
- `dev/literature/BIBLIOGRAPHY.md`: declined, not read. No new source is cited by this dispatch beyond the digest named above.

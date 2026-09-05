# LJ-1.724 report — the `table-sat` probe

**NO-GO (the stated target is false).** The obligation `table-sat` is **not
inhabitable as stated**: at a successor ordinal `γ` and `x` its predecessor, the
frame's A-bounded reading of the recording has no approximation inside
`Lset γ`, so `pr x (Lset x) ∈ˢ carved` fails. The minimal counterexample is
`γ = 2, x = 1`. Nothing lands in `src/`. The probe is green; the obligation
name is absent on purpose; `review-of-table-sat.md` carries the refutation,
the corrected scopes, and what survives for the next brief.

(This skeleton is filled in as the runs land; see C-22.)

## Verdict, five sentences

1. `carveSat` (`src/L/Axioms/Separation.lagda.md:163-168`) reduces
   `pr x (Lset x) ∈ˢ carved` to the satisfaction of `φᵣ` at the pair, and
   `φᵣ = relativize (LsetS γ oγ) (recordedFo (γ , hγ))`
   (`agents/tasks/LJ-1-698/Probe698.agda:108-109`).
2. Relativization binds every raw existential at `con A`, `A = Lset γ`
   (`src/FOL/Manipulation/Relativize.lagda.md:57`), and the recording's
   `GraphAt` conjunct (`src/L/Coding/Sequence.lagda.md:291,328-329`) holds a
   raw `∃̇` over the approximation: the reading demands `f ∈ˢ Lset γ`.
3. The `Step` conjunct (`src/L/Coding/Sequence.lagda.md:120,291`) covers every
   `z' ∈ Lset x`; at `γ = 2, x = 1` it forces a pair `⟨ 0 , w' ⟩` (rank ≥ 2)
   into `f`, and no member of `Lset 2` has rank ≥ 2: no such `f` exists.
4. So the reading fails at the top entry of every successor ordinal, and
   separately the `DefAt` membranes demand formula codes inside `Lset γ`,
   which fails outright below a fixed finite bound.
5. The corrected scope (limit `γ ≥ ω`, or re-bounding the frame at a limit
   stage) is stated in the review and needs the mathematician's ruling.

## Deliverables

| Item | Location | Status |
|---|---|---|
| Frame wiring + `dφ : Δ₀ φᵣ` | `Probe724.agda:53-61` | **in-tree, compiles** |
| `ord-in-Lset` (704's fact, re-measured) | `Probe724.agda:67-71` | compiles here |
| Obligation `table-sat` | `Probe724.agda:75-83` | **absent on purpose**, false as stated |
| Review (NO-GO, counterexample, corrected scope) | `review-of-table-sat.md` | filed |

## Runs

| Run | Result | Notes |
|---|---|---|
| probe (is its own floor: the obligation is absent, so the file is all frame) | `runs/p-1.out` | **GREEN, EXIT=0, 26.43 s, 776,470,528 bytes**, `GHCRTS=[-A64m -I0 -M2g]` |

Command: `bash agents/tasks/LJ-1-724/runs/run.sh agents/tasks/LJ-1-724/Probe724.agda p-1 1800`
(GHCRTS wide caliber, set by the program, untouched.)

## Key evidence

- `src/FOL/Manipulation/Relativize.lagda.md:57,60` — raw quantifiers get the
  `con A` bound; already-bounded ones pass through untouched.
- `src/L/Coding/Sequence.lagda.md:120,286-291,328-329` — `StepAt`/`ApproxAt`/
  `GraphAt`/`PairGraphAt`, the four readers whose existential slots the A-bound
  touches.
- `src/L/Coding/Model.lagda.md:662-663` — `extAt` is two raw `∀̇`:  its
  relativization only adds antecedents, which is why the counterexample is an
  existential obstruction and not a universal one.
- `src/L/Definability.lagda.md:137` — `defSet⊆A`:  members of `𝒟ₒ w'` are
  subsets of `w'`;  this is what forces `w' ⊇ z'`'s content in the
  counterexample.
- `src/L/Axioms/Basic.lagda.md:196` — `Lset-suc`, the successor stage is the
  definable powerset:  the rank arithmetic of the counterexample reads through
  it.
- `src/L/Axioms/Basic.lagda.md:592-599` — `sgl∈Lset-suc`, `pr∈Lset-suc`:  the
  pairing-in-stage facts the corrected target's fiber work needs, already in
  the tree.

## Notes

- The probe ran green on the first attempt at 26.43 s under the wide caliber; the
  cost is the import closure (698 pulls 693, which pulls the Hierarchy chapter),
  not the probe's own thirty lines.
- The refutation is model-side (rank arithmetic on the cumulative hierarchy);
  the tree-side facts it consumes are cited in the review. No in-tree term
  refutes `table-sat`: the negative would have to decide the non-existence of
  the reading's witnesses through the opaque `carve`, which is heavier than
  this task's price and is not attempted.
- `[LJ-1.704]`'s report is NO-GO at `carved-is-hier` and calls `table-sat`
  model-true; this dispatch's measurement corrects that: the reading's
  approximation existential cannot be witnessed inside `A = Lset γ` at the top
  entry of a successor ordinal, so the missing fact was missing because it is
  false, not because the satisfaction chain is unlanded.
- The world-discipline pits from 704 were re-verified here: `mem-ord` needs the
  explicit implicit `{γ}`, and the stage facts are stated in the `𝒮ᵥ` world
  (`∈ˢ` over `V`) to line up with `L.Ordinal.Stages`.

## ARCHIVE USED

Every candidate below was opened for this return; each bullet quotes the line
its citation names. This return is a target-refutation inside one probe, built
from live `src/` and `agents/tasks/` files only, so each archived record is
declined with the reason.

- `archive/dev/ORCHESTRATION.md:1` "ORCHESTRATION: the orchestrator's operating
  rules": read. It governs dispatch and landing of work; this return makes no
  dispatch or landing decision of its own. Declined.
- `archive/dev/DD-archived.md:3` "**Status: ARCHIVED RECORD. Never rewritten,
  never deleted.**": read. The frozen DD rows are superseded by
  `dev/pod/rulings.toml`, and no row of them is cited here. Declined.
- `archive/dev/PLAN-archived.md:1` "# ARCHIVED 2026-08-20": read. The live
  plan is `dev/pod/screen.toml` and `dev/pod/queue.toml`; the archived plan
  adds nothing to a target-refutation. Declined.
- `archive/dev/STATUS-archived.md:1` "STATUS-archived: the goal table of the
  internalization route": read. That route left the tree on 2026-08-09, before
  the `Carved` frame existed. Declined.
- `archive/dev/TASKS-archived.md:1` "Archived task index: the `L3.32-T`
  series": read. The retired `L3.32-T` series predates the `LJ-1` campaign this
  task belongs to. Declined.

## LITERATURE USED

Every candidate below was opened for this return; each bullet quotes the line
its citation names. The refutation reads the tree's own coding and stage
machinery, so the external-account notes are out of scope here.

- `dev/literature/glossary-review-2026-08.md:1` "Glossary review: the 119
  pre-protocol entries": read. This return adds no term to `dev/glossary.toml`
  and cites none. Declined.
- `dev/literature/devlin-errata.md:1` "Devlin errata: documented error classes
  (do-not-repeat checklist)": read. The checklist covers external accounts of
  constructibility; the obstruction here is measured inside the tree's own
  frame. Declined.
- `dev/literature/rudimentary-functions.md:1` "Rudimentary functions, closure,
  and the comprehension theorem": read. The rud-route closure facts play no
  role in the rank obstruction or the recording's reading. Declined.
- `dev/literature/primary-sources.md:1` "Primary sources, second round: Jensen
  manuscript, Devlin, Jech": read. The fetched texts back external claims;
  this return asserts only what the tree's own files prove. Declined.
- `dev/literature/formalizations-landscape.md:1` "Formalization landscape
  sweep: L, V=L, condensation, AC-in-L, GCH-in-L, rud (OPEN item 7)": read. A
  survey of formalization approaches bears on no step of this refutation.
  Declined.

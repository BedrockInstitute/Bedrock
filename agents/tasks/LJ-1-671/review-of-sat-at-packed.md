# [LJ-1-671] Review of `sat-at-packed`: NO-GO, the target is true and undelivered

## 1. THE STATEMENT

The brief orders one term:

    sat-at-packed : SatAtPacked delivered

with `SatAtPacked` copied verbatim from
`agents/tasks/LJ-1-663/Probe663.agda:135-138`:

    SatAtPacked : Formula Code 2 → Type (ℓ-suc ℓ)
    SatAtPacked lf =
      (γ : SL) (oγ : IsOrd (fst γ))
      → ⟨ (γ ∷ packed γ oγ ∷ []) ⊨c lf ⟩

and `delivered` the [LJ-1-651] value `lset-formula`
(`agents/tasks/LJ-1-651/Probe651.agda:142`), the arity-2 bounded
level-hood matrix of the condensation chapter in the delivered
convention (all 16 Fin slot positions zero,
`agents/tasks/LJ-1-651/Probe651.agda:63`), at the packed slot order
(ordinal 0, value 1, `agents/tasks/LJ-1-651/Probe651.agda:110-111`).

**Verdict: NO-GO.** The term cannot be built in this probe. The target
is **true**; the wall is that the tree delivers no satisfaction lemma
for the bounded-graph machinery, and the measured cost of one frame
step at this site exceeds the 1200 s run cap. Section 6 names the
route a larger task must take.

The probe file is green and states the obligation under the brief's
name
(`agents/tasks/LJ-1-671/Probe671.agda`). The attempt record is
`agents/tasks/LJ-1-671/runs/ATK-1.agda` (green) with the red version
preserved as `runs/ATK-1-red.agda.txt`.

## 2. THE TARGET IS TRUE

D-10 orders the truth of the target checked before any proof effort.
Checked. The zero-instance matrix is the intended level-hood reading,
and its clause structure reproduces the unbounded, already-proven
step clause of the sequence chapter.

### 2.1 The environment layout

The formula `delivered` reaches the matrix through five operations
(`agents/tasks/LJ-1-651/Probe651.agda:81-111`):

1. `step1 = ∃̇ LH0.matrix` closes the unused slot 0.
2. `step2 = renameFo rot step1` rotates the bound to the front.
3. `step3 = ∃̇ step2` closes the bound.
4. `twoSlot = renameFo swap step3` orders the slots ordinal, value.
5. `lset-formula = mapFo slide twoSlot` moves the carrier to `Code`.

The obligation environment is `(γ ∷ v ∷ [])`. After the ∃̇ prepends and
the two renames, the matrix environment is
`(u ∷ v ∷ γ ∷ K₀)`: the closed slot `u`, the packed value
`v = packed γ oγ`, the ordinal `γ`, and the closed bound `K₀`.

### 2.2 The step clause, verbatim

The step frame of the bounded matrix is
`src/L/Condensation.lagda.md:2392-2418` (`module StepB`):

    bodyB =
      (var 2 ∈̇ var (sh4 b))
      ∧̇ ( appAt (sh4 f) 2 1
         ∧̇ ( leafB ∧̇ (var 3 ∈̇ var 0) ) )
    witB =
      ∃̇∈ (var (suc b))
        (∃̇∈ (var (suc (suc K)))
          (∃̇∈ (var (suc (suc (suc K))))
            bodyB))
    stepBndAt = extAtB v K witB

Read at the zero instance (all Fin parameters zero, so the columns
collapse onto the slots derived in 2.1), the step clause says:

- for every `z` in the graph element `w`;
- there is an argument `c` below the ordinal (`c ∈ u`, `u ≈ˢ γ`);
- a recorded value `w₁` in the value (`w₁ ∈ v`);
- a set `d` below the ordinal (`d ∈ γ`);
- such that `c` lies in `w`, `w''` (the graph element that is a
  function) sends `c` to `d`, the leaf `leafB` holds (`d` is the
  definable powerset of `w₁`), and **`z ∈ d`**.

The fourth conjunct is `var 3 ∈̇ var 0`: the **step variable `z`** lies
in `d`. This is the same clause, verbatim, in the unbounded step body
of the sequence chapter, `src/L/Coding/Sequence.lagda.md:114-118`:

    StepBody b f = (var 2 ∈̇ var (sh4 b))
                 ∧̇ ( appAt (sh4 f) 2 1
                   ∧̇ ( DefAt zero (suc zero)
                     ∧̇ (var 3 ∈̇ var 0) ) )

and the green machinery there builds and reads exactly this clause:
`fill` supplies the fourth conjunct with the step variable's
membership in the definable powerset
(`src/L/Coding/Sequence.lagda.md:203-207`), and the Hierarchy chapter
proves the graph determines the value from it
(`src/L/Hierarchy.lagda.md:334-338`, `Lset-only`).

So the bounded zero instance says what the unbounded chapter says and
the Hierarchy chapter proves: the value is the level at the ordinal.
The witnesses are set-sized and live in the stage: the bound is a
stage set above `Lset γ`, the graph element is a set containing the
ordinals below `γ`, the level pairs, and a function recording the
definable powersets; each step variable lies in the definable
powerset of its recorded value. **The [LJ-1-666] review's statement
stands: the bounded matrix is true; the witnesses exist; the formula
holds** (`agents/tasks/LJ-1-666/review-of-sat-at-level.md`, section 2).

### 2.3 A correction of record

Mid-attempt, this task derived the matrix unsatisfiable. The
derivation rested on reading the fourth conjunct as `var 6 ∈̇ var 0`
(a free environment slot `u ≈ˢ γ` lying in `d`, against `d ∈ γ` — a
rank contradiction). The verbatim source is `var 3` (section 2.2).
The unsatisfiability claim is **retracted**; it was an artifact of a
misquoted clause, not a reading of the tree. The retraction is
recorded here because the misquoted reading appeared in this task's
working notes, and a future reader must not mistake it for a measured
fact.

## 3. THE WALL

Three walls, in order.

### Wall 1: No satisfaction lemma exists in the tree

The obligation is a stage satisfaction of the bounded matrix. The
tree delivers the **formula** and its Δ₀ certificate:

- `src/L/Condensation.lagda.md:2392-2480` — `StepB` and `ApproxB`,
  the bounded frames, with their `Δ₀-` certificates.
- `src/L/Condensation.lagda.md:2449-2458` — the row leaf
  (`StepAtB`), with its Δ₀ certificate.
- `src/L/BoundedSubset.lagda.md:108-114` — `levelHoodB` and its
  `Δ₀-levelHoodB`.

The tree delivers **no** satisfaction lemma for any of them: no
`approxBndAt` or `stepBndAt` or `leafB` satisfaction result exists
under `src/` (searched; the same wall is documented at
`agents/tasks/LJ-1-666/review-of-sat-at-level.md`, section 2, Wall 2).
The unbounded chapter's machinery (`StepAt-in`, `fill`,
`src/L/Coding/Sequence.lagda.md:203-231`) works on the unbounded
formula `StepAt` with the `PowOK` side condition; the bounded frame
`StepB` differs in the ∃̇∈ binders, the `extAtB` clause, and the leaf
`leafB`, and no adapter is delivered.

### Wall 2: The delivered bridge does not apply

The only delivered bridge from bounded to unbounded satisfaction is
`LeafAgree` / `extAtB→extAt`
(`src/L/Condensation.lagda.md:7224`), and it requires `KFacts`
(`src/L/Condensation.lagda.md:6079`) at **fourteen** environment
slots. The obligation's formula has **two**. This is the
[LJ-1-666] wall, unchanged: the gap is twelve slots, and folding the
tag equations into the formula body does not create slots
(`agents/tasks/LJ-1-666/review-of-sat-at-level.md`, sections 2-3).

### Wall 3: The measured cost of the direct route

The direct route is to build the satisfaction from the definition,
clause by clause, in the stage. One frame step was measured:

- `runs/atk-3.out`: the deep witness attempt (the inner truncated
  ∃̇, with the step variable instantiated to the packed value and a
  reflexive matrix satisfaction asserted) **capped at the 1200 s
  wall**; peak memory 946,241,536 bytes. Agda spent the whole budget
  reducing the wrapped matrix to report the inequality; it did not
  finish one step of the proof.
- `runs/atk-1.out`: the same skeleton with the residue left as a
  hole: 48.52 s, peak 1,911,406,592 bytes — the type of the residue
  is `∥ Σ[ x ∈ SL ] ⟨ (x ∷ K₀ ∷ γ ∷ v) ⊨c F ⟩ ∥₁` where `F` is the
  fully renamed matrix (printed in `runs/atk-2.out`).

The residue is not one step. It is the full satisfaction: the
approxBndAt frame, the stepBndAt frame with its three ∃̇∈ binders, the
leafB row with its two ∃̇∈ binders, and the Δ₀ leaf — all at the stage,
all in a context where one clause's reduction already exceeds the
run cap. This is a new module of chapter scale, not a probe
(delivery convention C-19: a probe measures and decides; it does not
deliver a chapter).

## 4. SITE COUNT

The refutation-against-construction question applies to one site:
the `SatAtPacked delivered` obligation. `SatAtPacked` appears in one
file, `agents/tasks/LJ-1-663/Probe663.agda:135-138`, and this task's
probe. Count: **1**.

## 5. RUNS

| run | file | real | peak bytes | exit | note |
|---|---|---|---|---|---|
| floor-1 | runs/Floor671.agda | 4.95 s | 851,214,336 | 0 | floor green, cache valid |
| atk-1 | runs/ATK-1.agda | 48.52 s | 1,911,406,592 | 42 | residue as hole; type not printed |
| atk-2 | runs/ATK-1.agda | 2.58 s | 692,928,512 | 42 | wrong term; goal type printed |
| atk-3 | runs/ATK-1.agda | capped 1200 s | 946,241,536 | 142 | deep witness; one frame step |
| probe-5 | Probe671.agda | 3.56 s | 730,726,400 | 0 | deliverable green |
| atk-6 | runs/ATK-1.agda | 3.21 s | 760,102,912 | 0 | attempt record green |

Every `.out` carries the GHCRTS line, the start and end stamps, and
the exit code. `GHCRTS=-A64m -I0 -M2g`, caliber from the pane, never
set in the run script.

## 6. THE ROUTE A LARGER TASK TAKES

The obligation is true and the route is a construction, not a
measurement. Two shapes, both chapter scale, both new modules under
`src/` (hence not this probe's business):

1. **A satisfaction module for the bounded frames.** A
   `satBnd`/`unsatBnd` pair for `approxBndAt`, `stepBndAt` and the
   row leaf, at the stage, transferring the unbounded chapter's
   `fill`/`readBody` machinery across the ∃̇∈ binders and the `extAtB`
   clause. This is the direct analog of the delivered unbounded
   mechanism and the natural home of the obligation.
2. **A re-derivation of the level-hood at the arity the `KFacts`
   wants.** The [LJ-1-666] review (section 3) shows the commitment
   sits in the bounded-graph machinery itself, at any arity: the
   fourteen-slot `KFacts` and the arity-2 obligation are in
   structural tension. A reformulation that keeps the tag columns
   alive at the satisfaction level closes the bridge; it also
   changes the delivered formula, which is the program's call.

Neither shape is inside this probe's scope, and neither is a stop
condition for the program: the target is true, the witnesses are
named, and the wall is a delivery gap, not a theorem gap.

## 7. FILES

- `agents/tasks/LJ-1-671/Probe671.agda` — green; the verbatim
  `SatAtPacked` and the obligation's type; the stop points here.
- `agents/tasks/LJ-1-671/runs/ATK-1.agda` — green attempt record.
- `agents/tasks/LJ-1-671/runs/ATK-1-red.agda.txt` — the red version
  (the structural skeleton with the residue left open).
- `agents/tasks/LJ-1-671/runs/runs.md` — the run table, expanded.
- This file — the review.

Nothing lands in `src/`. Nothing is postulated.

## ARCHIVE USED

None read. The five named candidates, each declined in writing:

- `archive/dev/ORCHESTRATION.md` — not read; the task's stop is a
  delivery gap in `src/`, not an orchestration question.
- `archive/dev/DD-archived.md` — not read; no archived ruling is
  needed to price the wall, which is measured, not ruled.
- `archive/dev/PLAN-archived.md` — not read; the plan of record is the
  live queue, and this task does not move the plan.
- `archive/dev/TASKS-archived.md` — not read; the predecessor tasks
  (651, 661, 663, 665, 666, 669) are live files under `agents/tasks/`
  and were read there.
- `archive/dev/STATUS-archived.md` — not read; standing status lives
  in `dev/pod/screen.toml`.

## LITERATURE USED

None read. The five named candidates, each declined in writing:

- `dev/literature/level-formula-slot-roles.md` — not read; the slot
  roles were read off the verbatim formula source
  (`src/L/Condensation.lagda.md:2392-2418`), not the digest.
- `dev/literature/devlin-errata.md` — not read; the Devlin direction
  is provenance, not load-bearing for the wall.
- `dev/literature/glossary-review-2026-08.md` — not read; no new
  term is coined here.
- `dev/literature/BIBLIOGRAPHY.md` — not read.
- `dev/literature/formalizations-landscape.md` — not read.

# LJ-1.59: the direction question, then the rest of the leaf chain

Status: COMPLETE, written incrementally per C-22. ASD-STE100.
No commit. No push. The working tree carries this dispatch's edits:
the master placements (if the gate stays under the bar) and the probes
`src/ProbeLJ159*.agda`. This report is `_build/lj-1.59-report.md`.

## 0. THE DIRECTION ANSWER (PLACED FIRST, PER THE BRIEF)

**YES. Producing `Adeq m` needs the machine -> story direction, and
`out` must be placed.**

The evidence, at `file:line`:

- `Adeq m` asserts a STORY-side witness: `K' v' w'` with
  `w' ∈ K'` and the BOUNDED matrix at `w' ∷ v' ∷ m ∷ K'`
  (`src/ProbeLJ152A.agda:78-81`). The matrix is `LH0.matrix =
  LH.levelHoodB = ∃̇∈ (var ...) (G.graphBndAt ∧̇ ...)`
  (`src/L/BoundedSubset.lagda.md:107-112`, `:847-849`), so the
  witness is a member of the BOUNDED graph `graphBndAt`.
- Nothing in the tree produces `graphBndAt` at a real ordinal.
  `graph-assembly` (`src/ProbeLJ152B.agda:71-87`) is the decode
  direction only: `graphBndAt -> LsetGraphAt`. It is a consumer of a
  story witness, not a producer of one.
- The one construction lemma for the level graph at a real ordinal is
  `Lset-defines` (`src/L/Hierarchy.lagda.md:646-649`): it takes the
  MACHINE side (`LsetGraphAt w b`) and produces the machine truth
  from `w = Lset b`. `Lset-defines` itself is a theorem about the
  machine graph; the story-side bounded graph is a DIFFERENT formula
  (`DefBodyB`-based), so even with `Lset-defines` the bounded witness
  must be produced by a transfer.
- The transfer that produces the bounded story formula from the
  machine formula is the machine -> story direction of the leaf
  chain: `DefBody -> DefBodyB` (the `out` direction of `LeafAgree`,
  `src/ProbeLJ157A.agda` section 5), whose pieces are the `out`
  directions of `ClosedAgree`, `DomainAgree`, `SatGraphAgree`,
  `ShapedAgree`, `WitnessAgree` and `KeyAgree`/`DefinesAgree`.
  Every one of these exists in the probes in the machine -> story
  direction and none is placed (`_build/lj-1.58-report.md:117-122`).

Therefore the answer to the question is YES, and the placement of the
leaf chain must carry BOTH directions. The `back` directions alone
(story -> machine) serve the decode/consumer side (`adeq-decode`,
`src/ProbeLJ152A.agda:85-104`, and the `Condense` hypotheses at
`src/L/BoundedSubset.lagda.md:916-917`), but the discharge of
`levelIn`/`cover` needs `Adeq m` to be PRODUCED at ordinal hull
members, and that production is machine -> story.

This answer is MEASURED from the pinned statements above, not inferred
from the literature: it is a fact about which formulas the tree's
lemmas produce (`Lset-defines` produces the machine graph; the probes'
`out` directions produce the bounded graph from the machine one), read
at `file:line`.

## 1. WHAT WAS PLACED, AND THE WHOLE-FILE RATE AFTER EACH

### 1.1 The baseline, re-measured

Caliber: C-12 `GHCRTS="-A64m -I0 -M8g"`, user seconds from
`/usr/bin/time -p`, cold module (the module's own interface moved
aside before EVERY run), dependencies warm, one process. Tree clean at
`29b8ea4`, three completed runs.

| module | runs, user s | mean | spread | content lines | rate |
|---|---:|---:|---:|---:|---:|
| `L.Condensation` baseline (HEAD 29b8ea4) | 62.60 / 62.30 / 62.91 | 62.60 | 0.61 (1.0 pc) | 5,027 | 0.01245 |

**LOAD CAVEAT, MEASURED:** the machine load average during these runs
was 11.9 (4 users), against the quiet machine the protocol assumes.
The 62.60 s baseline is 16.8 pc above `[LJ-1.58]`'s 53.58 s at the
same commit; the pairwise spread is still 1.0 pc, so the runs are
self-consistent but NOT comparable to the quiet-machine figure. Every
placement figure below is compared against this same-session baseline;
the absolute numbers carry the load caveat.

### 1.2 Placement 1: the `in'` directions of the shape transfers

`UnShapeClosed.in'` (machine `arityTagAtL` -> story `arTagBS`) and
`BinShapeClosed.in'` (machine `arityTagPairAtL` -> story
`arTagPairBS`) added to `src/L/Condensation.lagda.md`, ported
verbatim from `src/ProbeLJ156A.agda:101-148` and `:201-255`. The
file gains 79 in-fence lines (5,027 to 5,106). This is the minimal
machine -> story content the direction answer requires, and it is the
content `ClosedAgree`'s frame agreement consumes.

| module | runs, user s | mean | spread | content lines | rate |
|---|---:|---:|---:|---:|---:|
| `L.Condensation` + placement 1 | 64.24 / 63.78 / 63.83 | 63.95 | 0.46 (0.7 pc) | 5,106 | 0.01253 |

The marginal rate of placement 1 is (63.95 - 62.60) / 79 =
0.0171 s per line; the pairwise deltas are 0.0208 / 0.0149 / 0.0156.
This is the same rate class as `[LJ-1.58]`'s back-direction content
(0.01765), as predicted: both are instantiation-class satisfaction
content (P-m). The whole-file rate 0.01253 is under the DD24 live bar
0.012716. No wall.

### 1.3 Placement 2: the closedness and domain transfers, both directions

`BinFrameAgree`, `UnFrameAgree`, `BothSameRel`, `OneSameRel`,
`OneSuccRel`, `SuccSndRel`, `ClosedAgree` and `DomainAgree` added to
`src/L/Condensation.lagda.md`, ported MECHANICALLY (extracted
verbatim) from `src/ProbeLJ156A.agda:234-523`. The file gains 249
in-fence lines (5,106 to 5,355). The content class is mixed: the two
frame agreements are parameterized content (P-m's cheap class), the
relations and the two transfers are instantiation content.

| module | runs, user s | mean | spread | content lines | rate |
|---|---:|---:|---:|---:|---:|
| `L.Condensation` + placement 2 | 66.24 / 67.04 / 65.82 | 66.37 | 1.22 (1.8 pc) | 5,355 | 0.01239 |

The marginal rate of placement 2 is (66.37 - 62.60) / 249 =
0.0151 s per line; the pairwise deltas are 0.0146 / 0.0178 / 0.0129.
This is cheaper than the walk-class rate, consistent with the
parameterized frame-agreement share. The whole-file rate 0.01239 is
under the DD24 live bar 0.012716. No wall.

### 1.4 Placement 3 attempted and REVERTED: the two-way walk, MEASURED WALL

The `out` (machine -> story) direction of the twelve-row walk was
placed as a second probe-style attempt: the two-way `TmBranch`/
`TmAgree` (from `src/ProbeLJ156A.agda:524-616`), the two-way walk
relations (`src/ProbeLJ157A.agda:228-315`), the two-way frame
agreements (`:78-227`) and the probe's hand-written two-way
`ShapesAgree` (`:316-659`), all re-pointed to the master's modules.
The file typechecked at 5,759 in-fence lines.

| module | runs, user s | mean | spread | content lines | rate |
|---|---:|---:|---:|---:|---:|
| `L.Condensation` + placement 3 | 91.71 / 90.84 / 91.02 | 91.19 | 0.87 (1.0 pc) | 5,759 | 0.01584 |

The marginal rate of placement 3 is (91.19 - 62.60) / 732 =
0.0788 s per line; the pairwise deltas are 0.0798 / 0.0772 / 0.0774.
This is 4.6x the `[LJ-1.58]` walk-class rate and matches the
`[LJ-1.57]` as-spelled probe rate (0.0755), because the probe's
forward direction is the hand-written `o1..o11` disjunction chain:
each helper states a concrete partial tree, and the elaborator
normalizes it per helper (the exact cost P-t removed from the back
direction). The whole-file rate 0.01584 is OVER the DD24 live bar
0.012716 (68.1 s at 5,355 lines would be the ceiling; the measured
91.2 s is 34 pc over).

**Decision, MEASURED:** placement 3 was REVERTED. The tree now carries
placements 1 and 2 only, and `L.Condensation` measures 66.37 s over
5,355 in-fence lines = 0.01239, under the bar. The wall is not a
refutation of the direction answer: the forward walk EXISTS in the
probes and typechecks in the master; it is a PRICE wall. The price of
the forward direction at the hand-written spelling is 0.0788 s per
line; the cure the `[LJ-1.58]` spelling says to test is the `Lift12Out`
mirror of `Lift12Back` (the forward assembly as a generic lift kit at
abstract propositions, so each full tree normalizes once per
statement), which was NOT built here (the budget went to measuring the
wall). That cure is INFERRED to close the wall from the measured
back-direction analogue (0.0171) and is the first thing a follow-up
dispatch should test.

## 2. levelIn AND cover

**Neither is discharged.** The direction answer is settled (section 0),
and the leaf chain is placed up to and including the closedness and
domain transfers in both directions. The remaining chain, in order,
is: the walk `out` direction at the `Lift12Out` spelling (the wall of
section 1.4), `ShapedAgree`, `WitnessAgree`, `KeyAgree`/`DefinesAgree`,
the `TwelveAgree` composition, `SatGraphAgree`, `LeafAgree`, then the
post-leaf five of `[LJ-1.57]` section 8: `StepAgree`/`ApproxAgree`,
`GraphAgree`, the stage truth of `Adeq m`, the ElemDown wiring, and
the collapse-of-the-level `π (Lset m) = Lset (π m)`.

The term I could not write this dispatch, per C-36: the `out` direction
of the twelve-row walk in a spelling that keeps the whole-file rate
under the bar. The hand-written form typechecks but measures
0.0788 s/line and takes the file to 0.01584; the unbuilt spelling is
the `Lift12Out` kit. Everything downstream of the walk (`ShapedAgree`
through `LeafAgree`) is a port of green probe content once the walk's
`out` exists, priced by this dispatch's measured classes.

## 3. THE RATES

Caliber: C-12 `GHCRTS="-A64m -I0 -M8g"`, user seconds from
`/usr/bin/time -p`, cold module (the module's own interface moved
aside before EVERY run), dependencies warm, one process. Three
completed runs per figure. The machine load average during the runs
was 11.9 (4 users); the load caveat of section 1.1 applies to every
absolute figure, while the pairwise deltas are same-session and
comparable.

| module | runs, user s | mean | spread | in-fence lines | rate |
|---|---:|---:|---:|---:|---:|
| `L.Condensation` baseline (HEAD 29b8ea4) | 62.60 / 62.30 / 62.91 | 62.60 | 0.61 (1.0 pc) | 5,027 | 0.01245 |
| + placement 1 (`in'` directions) | 64.24 / 63.78 / 63.83 | 63.95 | 0.46 (0.7 pc) | 5,106 | 0.01253 |
| + placement 2 (closedness/domain) | 66.24 / 67.04 / 65.82 | 66.37 | 1.22 (1.8 pc) | 5,355 | 0.01239 |
| placement 3 (two-way walk), reverted | 91.71 / 90.84 / 91.02 | 91.19 | 0.87 (1.0 pc) | 5,759 | 0.01584 |

| marginal | lines | mean user s | rate |
|---|---:|---:|---:|
| placement 1 | 79 | 63.95 - 62.60 = 1.35 | 0.0171 |
| placement 2 | 249 | 66.37 - 62.60 = 3.77 | 0.0151 |
| placement 3 (reverted) | 732 | 91.19 - 62.60 = 28.59 | 0.0788 |

Pairwise deltas: placement 1: 0.0208 / 0.0149 / 0.0156. Placement 2:
0.0146 / 0.0178 / 0.0129. Placement 3: 0.0798 / 0.0772 / 0.0774.

The cone: `L.BoundedSubset` (the one consumer), cold with its own
interface aside and dependencies warm, ONE run: 14.29 s user. This is
the per-invocation interface cost class the ledger records
(`dev/ledger.toml:2580-2586`); the probe cones of prior dispatches
measured 1.30-1.48 s for a single probe import, and the BoundedSubset
cone is higher because the module's own content (the LevelHood/AtHull
region) is warm-stale in this run. The cone is interface cost, not
content cost, and no placed definition changed it (the consumer
re-checks green; section 5).

## 4. DD4

**The placed content keeps the template shape.** `UnShapeClosed.in'`,
`BinShapeClosed.in'`, `BinFrameAgree`, `UnFrameAgree`, the four
relations, `ClosedAgree` and `DomainAgree` all state slots,
environments and site facts as module parameters at `S ^ n`
environments; no placed type mentions a concrete carrier. The J tower
inherits the whole generic layer unchanged, instantiated at its own
slots and site facts. The direction answer forces no tower-specific
spelling: the machine -> story direction is the same template content
either tower consumes, and the reverted walk placement carried no
concrete carrier either (its price wall is the hand-written assembly,
not the parameterization).

## 5. THE CONVERGENCE ANSWER

**The question is settled and the phase has a priced wall, not a
renamed obligation.** `Adeq m` production needs the machine -> story
direction, so the `[LJ-1.58]` narrowing is not the whole chain: the
decode side consumes story -> machine, but the discharge side must
produce the bounded witness, and the only construction lemma for the
level graph at a real ordinal is `Lset-defines`
(`src/L/Hierarchy.lagda.md:646-649`), which sits on the machine side.
The master now carries the machine -> story shape transfers, the
closedness transfer and the domain transfer in both directions, all
under the DD24 bar (0.01239 whole-file). The remaining chain is
downstream composition of green probe content, except the walk `out`
direction, whose hand-written spelling is measured at 0.0788 s/line
(the wall) and whose `Lift12Out` cure is the first thing to test.
`levelIn` and `cover` are NOT discharged; the ledger stands as section
2 says.

## 6. NEGATIVES AND THEIR STATUS

1. Producing `Adeq m` needs the machine -> story direction:
   **MEASURED** (the pinned statements: `Adeq`
   `src/ProbeLJ152A.agda:78-81`, `Lset-defines`
   `src/L/Hierarchy.lagda.md:646-649`, `graph-assembly`
   `src/ProbeLJ152B.agda:71-87`; section 0).
2. The `in'` directions place at 0.0171 s/line: **MEASURED** (three
   cold runs each side, section 3).
3. `ClosedAgree`/`DomainAgree` place at 0.0151 s/line: **MEASURED**
   (three cold runs, section 3).
4. The hand-written forward walk places at 0.0788 s/line and takes
   the file over the bar: **MEASURED** (three cold runs, section 1.4).
5. The `Lift12Out` kit would close that wall at the back-direction
   rate class: **INFERRED** (from the measured back-direction
   analogue; not built, because the budget went to measuring the
   wall). This inference sets no verdict and is the first thing a
   follow-up dispatch should test.
6. The absolute baseline (62.60 s) vs `[LJ-1.58]`'s 53.58 s:
   **MEASURED** but load-confounded (section 1.1); the same-session
   deltas are the comparable figures.

## 7. ARCHIVE USED

- `_build/lj-1.58-report.md`, read WHOLE. Took the spelling (sections
  2 and 5), the measurement protocol and the rates; the direction
  argument it drew (section 5) is what this dispatch checked and
  found one-sided: it proves the CONSUMERS need story -> machine, not
  that production needs nothing else.
- `src/ProbeLJ158A.agda`, read WHOLE. Took the back-only spelling the
  master already carried.
- `_build/lj-1.57-report.md`, read WHOLE (section 8: the five
  post-leaf terms). Took the as-spelled probe rate 0.0755
  (`:114-122`), which the reverted placement 3 re-measured at 0.0788.
- `src/ProbeLJ157A.agda`, read WHOLE (sections 1-5). Took the two-way
  frame agreements, relations, `ShapesAgree`, `ShapedAgree`,
  `WitnessAgree`, `LeafAgree`; the walk `out` content was placed and
  measured, then reverted.
- `src/ProbeLJ152A.agda` and `src/ProbeLJ152B.agda`, read WHOLE.
  Took `Adeq` (`:78-81`), `adeq-decode` (`:85-104`) and
  `graph-assembly` (`:71-87`): the pinned statements that decide the
  direction question.
- `src/ProbeLJ156A.agda`, read WHOLE (sections 1-7). Took the `in'`
  directions, the frame agreements, relations, `ClosedAgree`,
  `DomainAgree` (placed), and `TmAgree.in'`/`SatGraphAgree` (still
  probe-only).
- `src/ProbeLJ155B.agda`, read the twelve-row composition sections.
  Took `TwelveAgree`'s shape; not placed this dispatch.
- `src/ProbeLJ154A.agda`, read WHOLE. Took `KeyAgree`/`DefinesAgree`;
  not placed this dispatch.
- `_build/lj-1.52-report.md` and `_build/lj-1.51-report.md`, read
  WHOLE. Took the `levelIn`/`cover` survivor statements and the
  post-leaf chain (section 8 of the 1.57 report).
- `src/L/BoundedSubset.lagda.md`, read the `LevelHood0`/`Condense`
  regions (`:74-142`, `:840-880`, `:916-1019`). Took the matrix and
  the two hypotheses; the consumer re-checks green after the
  placements.
- `src/L/Hierarchy.lagda.md:646-649`, read `Lset-defines` and its
  prose (`:671-698`). Took the graph-construction direction: the
  lemma produces the MACHINE graph from `w = Lset b`.
- `src/L/Coding/Model.lagda.md:278-304` and `:2191-2192`, read for
  `domAt` and `closedAt` availability in the master's import cone.
- `dev/ledger.toml:2580-2586`, the cone note; the DD24 bar.
- `dev/LESSONS.md`, via `scripts/rules.py --for build` (whole bundle).
  Took P-t (the lift-kit spelling), P-m (the content classes), P-l
  (re-measure at the site: placements 1-3 were each measured at the
  master), C-36 (the term not written), C-37 (naming the laws), C-32
  (re-measure the gate on the cured tree).
- `archive/rud-route/`, SHAPE only. WHY NOT more: `[LJ-1.11]` ruled
  its condensation target classically false, and the brief forbids
  taking a price from it.

## 8. LITERATURE USED

- `dev/literature/devlin-II5.md:216-231` (Step C), read. TOOK: the
  level-hood statement is Sigma-1 with a Sigma-0 bounded matrix
  (`∃z Φ(z, v, γ)` with z the bounded witness), and the elementarity
  step transfers the bounded statement itself. The conclusion
  `[LJ-1.58]` drew from it (the decode side never needs machine ->
  story) IS supported for the elementarity step; the production side
  is a tree fact, not a literature fact: nothing in Devlin's Step C
  constructs the story-side bounded witness from the machine graph.
  The tree's only construction lemma, `Lset-defines`, produces the
  machine graph (`src/L/Hierarchy.lagda.md:646-649`), which is why
  the direction question is answered from the tree, with the
  literature agreeing rather than deciding it.
- `_build/literature/dev2.txt:1372-1385` (5.5), read. TOOK: the
  condensation step as "let π : M ≅ L_γ", which the formal proof
  supplies via the level-hood adequacy; nothing there prices the
  direction.
- The errata were NOT re-checked. WHY NOT: `[LJ-1.14]` verified that
  Chapter II section 5 is not covered, and the brief forbids
  re-checking.
- `dev/literature/j-hierarchy.md` and the J-side digest were NOT read.
  WHY NOT: the direction question is decided by L-side tree facts at
  `file:line`, and the J tower's level story changes neither the
  statement of `Adeq` nor the placement cost.

## 9. GATES

`scripts/check-fences.py --check` clean (84 masters).
`scripts/lint-prose.py --check` exit 0 on the edited master.
`scripts/lint-agda.py --check` exit 0. `scripts/ledger.py --check`
clean; the worktree count of `L.Condensation` is 5,355 in-fence lines
(HEAD 5,027). `L.BoundedSubset` (the only consumer) re-checks green.
No `make check` was run, per the brief. No commit, no push. The
working tree carries the master edit and this report; the probe
`src/ProbeLJ157A.agda` (the only machine -> story proof) is
untouched.

## 2. THE RATES

(Filled from the cold runs.)

## 3. levelIn AND cover

(Filled as the chain is placed.)

## 4. DD4

(Filled at the end.)

## 5. THE CONVERGENCE ANSWER

(Filled at the end.)

## 6. NEGATIVES AND THEIR STATUS

(Filled at the end.)

## 7. ARCHIVE USED

(Filled at the end.)

## 8. LITERATURE USED

(Filled at the end.)

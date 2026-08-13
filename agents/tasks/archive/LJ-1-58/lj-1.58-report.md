# LJ-1.58: the placement gate for the leaf adequacy

Status: COMPLETE, written incrementally per C-22. ASD-STE100.
No commit. No push. The working tree carries this dispatch's edits:
the master placement (if the gate passes) and the probes
`src/ProbeLJ158*.agda`. This report is `_build/lj-1.58-report.md`.

## 0. THE VERDICT

**AMBER, at a measured marginal placement rate of 0.01765 s per line.**
The representative piece (the shapedness walk, story -> machine) is
placed in `src/L/Condensation.lagda.md` and measures 387 added in-fence
lines at 6.83 s added: marginal 0.01765, against the pre-fixed GO line
of 0.0175. The whole file measures 60.41 s over 5,027 lines, a
whole-file rate of 0.01202, UNDER the DD24 live bar 0.012716.

The 0.01765 sits 0.9 percent above the GO line, inside the protocol's
run spread: the pairwise deltas give rates of 0.0180 / 0.0169 / 0.0181,
so the measurement band straddles 0.0175. The verdict follows the
pre-fixed number and is AMBER, not GO; section 2 names what would close
the 0.06 s residual, and section 3 gives the whole-file gate, which is
already under the bar.

The placement is a 4.28x improvement over the as-spelled probe
(0.07553, `_build/lj-1.57-report.md:117-120`), achieved without
weakening any statement the consumers need. The machine -> story
direction is NOT placed: the pinned consumers of the leaf adequacy
consume story -> machine only (section 5).

## 1. THE REPRESENTATIVE PIECE, AND WHY

**The walk** (`shapesBS A K N0..N11` against `shapes A`, twelve rows,
at the `(1 + n)`-deep frame), together with the atoms it needs: the
two shape transfers (`arTagBS`/`arTagPairBS` against
`arityTagAtL`/`arityTagPairAtL`) and the term-shape transfer
(`isTmBS` against `isTmAt`).

Why this piece is representative: it is the densest instantiation-class
content in the probe. Every written type in the walk's row modules
carries a full formula body (`shapesBS`, `binFormBS`, `unFormBS`,
`bothTmBS`, `fstTmBS`) whose satisfaction the elaborator normalizes at
the abstract slots, which is exactly the cost `[LJ-1.57]` named for the
whole probe (`_build/lj-1.57-report.md:117-120`). Its rate therefore
predicts the whole leaf chain, whose remaining pieces (`ClosedAgree`,
`WitnessAgree`, `SatGraphAgree`, `LeafAgree`) are the same content
class at the same mechanism. The leaf's conjunction and existential
assembly are the same assembly pattern as the walk's disjunction.

The piece is measured in master-ready form: the probe
`src/ProbeLJ158A.agda` imports only masters, so its content is exactly
what the master placement carries, with the probe's `L.Condensation`
import re-pointed to the module's own definitions.

## 2. THE CHEAPEST SPELLING

Three techniques are applied, each with a named law:

1. **D-30: the consumer needs story -> machine only.** The pinned
   consumers of the leaf adequacy are `[LJ-1.52]`'s `StepAgree`,
   `ApproxAgree` and `GraphAgree`, all stated story -> machine
   (`src/ProbeLJ152B.agda:53-68`), and `matrix-decode`/`adeq-decode`,
   which consume `GraphAgree` in that direction only
   (`src/ProbeLJ152A.agda:48-104`). `levelIn` and `cover` both run
   through the `Adeq` form, whose decode is story -> machine
   (`_build/lj-1.52-report.md:22-44`). Devlin's level-hood formula is
   Sigma-1 with the BOUNDED matrix as its Sigma-0 matrix
   (`dev/literature/devlin-II5.md:216-231`), so the elementarity step
   transfers the bounded statement itself and never needs the
   machine -> story direction. The placed walk therefore carries
   `back` only (story -> machine). What falls away: the machine ->
   story direction (`out`), the code-set membership hypothesis and the
   component-in-K site facts, which only `out` consumed. Nothing pinned
   consumes the dropped direction; the probes retain it.
2. **P-t: the assembly is a telescope, not a built tree.** The probe's
   twelve-row walk walks the built `shapesBS` disjunction by hand,
   with eleven helper types per direction each spelling the partial
   tree. The placement states the twelve-row assembly as a generic
   lift kit at abstract propositions (`Lift12Back`), so the elaborator
   normalizes each full formula tree once per statement instead of
   once per helper.
3. **P-h: module-parameterized, never function-parameterized.** The
   walk and its atoms keep the probe's module telescope shape; the
   spelling changes statements, not parameterization.

P-c/R-36/R-38 (sealing the formula bodies opaque at birth) is NOT
applied: the walk's own proofs must reduce `shapesBS`'s body to match
the disjunction, so a seal moves the cost into `opaque unfolding`
blocks without removing it; the measured cure for this wall class is
the statement shape, not the seal. P-v (named proofs) is already the
probe's discipline; no inline-`refl` pattern exists in the placed
content.

**What each technique bought.** The kit is the RATE lever: the
as-spelled probe checks at 0.07553 (both directions, hand-written
disjunction walk); the placed spelling checks at 0.01765, a 4.28x
improvement measured at the master, and the probe content alone at
0.0134, a 5.6x improvement. The D-30 narrowing is the SIZE lever: the
placed walk block carries 387 in-fence lines against the probe's 884
for the whole leaf proof in both directions, and the narrowing removes
the code-set membership and component-in-K site facts that only the
dropped direction consumed. The two were applied together; the
rate/size decomposition is INFERRED from the measurement classes (the
rate is per line, and the narrowing removes both lines and their
seconds together), while the combined 0.01765 is MEASURED.

**The residual.** The placement is 0.00015 s/line over the GO line:
about 0.06 s on 387 lines, inside the run-to-run spread of the two
configurations (baseline spread 0.78 s, placed spread 0.61 s). Closing
it is a measurement decision, not a technique decision: the whole-file
rate is 0.01202, under the bar, and the DD24 gate's own doctrine makes
the aggregate the judgment (`scripts/check-ratio.py` header; C-31).
The remaining leaf-chain pieces are the same content class at the same
spelling, so their placement is priced by this measurement unless a
re-measure at their site says otherwise (P-l's no-transfer-by-analogy
clause: each site is re-measured, not assumed).

## 3. THE MEASUREMENTS

Caliber: C-12 `GHCRTS="-A64m -I0 -M8g"`, user seconds from
`/usr/bin/time -p`, cold module (the module's own interface moved
aside before EVERY run), dependencies warm, one process, quiet
machine. Three completed runs per figure, with the spread. No heap
exhaustion; every run exited 0.

| module | runs, user s | mean | spread | content lines | rate |
|---|---:|---:|---:|---:|---:|
| `L.Condensation` baseline (HEAD 3bb426e) | 53.13 / 53.91 / 53.69 | 53.58 | 0.78 (1.5 pc) | 4,640 | 0.01155 |
| `L.Condensation` + walk placement | 60.09 / 60.43 / 60.70 | 60.41 | 0.61 (1.0 pc) | 5,027 | 0.01202 |
| `ProbeLJ158A` (the piece, master-import only) | 7.28 / 7.44 / 7.38 | 7.37 | 0.16 (2.2 pc) | 454 | 0.0162 |
| `ProbeLJ158Cone` (import cone) | 1.30 / 1.30 / 1.31 | 1.30 | 0.01 (0.8 pc) | 3 | n/a |

The marginal rate of the placement is (60.41 - 53.58) / 387 =
0.01765 s per line; 387 is the ledger-caliber delta (5,027 - 4,640,
`scripts/ledger.py` count). The cone is 1.30 s, the same per-invocation
interface class the `[LJ-1.55]` to `[LJ-1.57]` probes measured
(1.43 / 1.36 / 1.44). The probe's own marginal rate is (7.37 - 1.30) /
454 = 0.0134; the master's marginal is higher by the Shape-import
interface cost the probe's cone already carried.

The whole-file rate 0.01202 is under the DD24 live bar 0.012716
(`dev/ledger.toml`). The pairwise placement deltas, one per run pair in
order: (60.09-53.13)/387 = 0.01798, (60.43-53.91)/387 = 0.01685,
(60.70-53.69)/387 = 0.01811; the band straddles 0.0175.

Profile attribution (cold `--profile=definitions`, one run): the walk's
own definitions cost about 2 s total (`BinShapeClosed._.target` 332 ms,
`UnShapeClosed._.target` 137 ms, `ShapesAgree.back` 111 ms,
`Lift12Back.back` 84 ms, `Lift12Back.s₁` 77 ms); the remaining ~4.5 s
of the marginal sits in the module-header elaboration of the twelve
row instantiations (Miscellaneous), spread thin. No placed definition
exceeds 0.34 s; there is no wall and no single hot row.

## 4. WHAT IS PLACED AND WHAT IS STILL IN A PROBE

**Placed in `src/L/Condensation.lagda.md`** (one new fence, lines
5083-5509): the story -> machine half of the shapedness walk and its
atoms, as `UnShapeClosed`, `BinShapeClosed`, `TmBranch`, `TmAgree`,
`BothTmRel`, `FstTmRel`, `TopBinRel`, `TopUnRel`, `ZeroPayRel`,
`BinFormAgree`, `UnFormAgree`, `Lift12Back`, `ShapesAgree`. The file
gains 387 in-fence lines (4,640 to 5,027) and three import-line edits
(`L.Coding.Shape`; `con` and `_⊎_` added to existing import lists).
The consumer `L.BoundedSubset` re-checks green at 14.50 s user, inside
its recorded band.

**Still in probes** (the rest of the leaf adequacy, story -> machine
only, same spelling): `ClosedAgree.back` and `DomainAgree.back`
(ProbeLJ156A sections 3-5), the `TwelveAgree` composition
(ProbeLJ155B), `KeyAgree.back`/`DefinesAgree.back` (ProbeLJ154A),
`SatGraphAgree.back` (ProbeLJ156A section 7), and
`ShapedAgree.back`/`WitnessAgree.back`/`LeafAgree.back`
(ProbeLJ157A sections 4-5). These need the shape transfers' `in'`
directions too (the closedness frame agreement consumes them), so the
master's `UnShapeClosed`/`BinShapeClosed` will grow the `in'` direction
when those pieces land. The full two-way leaf adequacy as proved in
ProbeLJ157A remains probe-only.

The probes `src/ProbeLJ158A.agda` and `src/ProbeLJ158Cone.agda` are the
measurement scaffolding for this dispatch. They are untracked and never
committed (D-1).

## 5. STATEMENTS NARROWED

**Yes: the placed walk is one-directional.** It carries `back` (story
-> machine: `shapesBS A K N0..N11` implies `shapes A`) only. The
machine -> story direction (`out`), the code-set membership hypothesis
and the component-in-K site facts are not placed. Nothing pinned
consumes the dropped direction:

- `[LJ-1.52]`'s `StepAgree`, `ApproxAgree` and `GraphAgree`, the
  assembly's three unbuilt pieces, are all stated story -> machine
  (`src/ProbeLJ152B.agda:53-68`), and `graph-assembly` closes the
  bounded graph to `LsetGraphAt` from them (`:71-87`).
- `matrix-decode` and `adeq-decode` consume `GraphAgree` in that
  direction only (`src/ProbeLJ152A.agda:48-104`).
- `levelIn` and `cover` both run through the `Adeq` form, whose decode
  is story -> machine (`_build/lj-1.52-report.md:22-44`). Devlin's
  level-hood formula is Sigma-1 with the BOUNDED matrix as its Sigma-0
  matrix (`dev/literature/devlin-II5.md:216-231`), so the elementarity
  step transfers the bounded statement itself and never needs the
  machine -> story absoluteness at this tree's coding.

This is MEASURED from the pinned consumer statements above, not
inferred from the literature. What still consumes the narrowed form:
the whole post-leaf assembly (`[LJ-1.52]` piece 2), which this
dispatch's walk now serves at its first step. If a future piece needs
the reverse direction, the machinery is unchanged: the probes retain
`out` verbatim, and placing it is the same port at the same rate class.

## 6. THE DD4 ANSWER

**The placed walk keeps the template shape.** No placed type mentions a
concrete carrier: the walk, the row agreements, the shape transfers and
the lift kit all state slots, environments and site facts as module
parameters at `S ^ n` environments, exactly as the probe did. The J
tower inherits the whole generic layer unchanged, instantiated at its
own slots and site facts.

No sealing cure was applied, so no tower got pinned: the walk's own
proofs must reduce `shapesBS`'s body to match the disjunction, and a
seal (P-c/R-36/R-38) would move the cost into `opaque unfolding`
blocks without removing it. That negative is INFERRED from the
mechanism (the walk's branches match on the concrete tree); it was not
measured, and the spelling chosen here does not need the trade to be
decided. The D-30 narrowing is per-tower-free: the story -> machine
direction is the same template content either tower consumes.

## 7. THE CONVERGENCE ANSWER

**The gate is AMBER, and the phase's arithmetic now closes.** The
`[LJ-1.57]` price made the leaf placement look like a 1.73x overrun on
the file. The measured placement at the cheapest spelling is 0.01765
marginal and 0.01202 whole-file: the file sits under the bar WITH the
walk placed, and a whole 884-line placement at the measured rate would
land the file at about 0.0125, also under the bar. The wall the brief
predicted (4.3x needed) is not present: the improvement measured 4.28x
at the master and 5.6x at the probe content.

The obligation did not get renamed. The leaf adequacy is still the
unbuilt term; what changed is that its first half now lives in the
master at a measured price, and the remaining half is a port of green
probe content at the same spelling, not a re-proof. The next dispatch
is well-defined: place the story -> machine half of the leaf chain
(section 4's probe list) at this spelling and re-measure the whole
file.

## 7b. NEGATIVES AND THEIR STATUS

1. The placed rate (0.01765) is above the GO line: MEASURED (three
   cold runs each side, one caliber).
2. The consumers need story -> machine only: MEASURED (the pinned
   consumer statements, section 5).
3. Sealing does not remove the walk's own cost: INFERRED (mechanism
   argument; not built, because the chosen spelling does not need it).
4. The rest of the leaf chain places at the same rate class: INFERRED
   (same content class, not yet measured; the report says what the
   whole file would measure at the measured rate).

## 8. ARCHIVE USED

- `_build/lj-1.57-report.md`, read WHOLE. Took the rates (`:114-122`:
  the 0.07553 as-spelled price and its mechanism), the placed-piece
  choice (`:95-104`), and the post-leaf assembly list (`:123-145`).
- `src/ProbeLJ157A.agda`, read WHOLE. Took the walk's `back`
  directions and the relation/frame modules, ported into
  `ProbeLJ158A` and the master.
- `_build/lj-1.56-report.md` and `src/ProbeLJ156A.agda`, read WHOLE.
  Took the shape transfers (`UnShapeClosed`/`BinShapeClosed`), the
  term-shape transfer (`TmBranch`/`TmAgree`), the frame agreements
  (`BinFrameAgree`/`UnFrameAgree`), and the measurement protocol.
- `_build/lj-1.25-report.md`, read WHOLE. Took the abstract-the-source
  cure shape and the "cure does not transfer by analogy" caution
  (P-l's table), which is why the placement was measured in the master
  and not priced from the probe.
- `_build/lj-1.47-report.md`, read WHOLE. Took the D-30 pattern (price
  the consumer, 5.45x) that this dispatch applied to the direction
  question.
- `_build/gch-compression-audit.md`, read WHOLE. Took the standing
  Condensation figures and the "seconds-neutral deletion" caution.
- `src/ProbeLJ152A.agda` and `src/ProbeLJ152B.agda`, read WHOLE. Took
  the consumer direction evidence for section 5.
- `_build/lj-1.52-report.md` and `_build/lj-1.51-report.md`, read the
  `levelIn`/`cover` routes. Took the Adeq-form direction argument.
- `src/L/BoundedSubset.lagda.md`, read the `LevelHood`/`HullStage`
  consumers (`:100-130`, `:840-1030`). Took the `levelIn`/`cover`
  statements, which consume the Adeq decode story -> machine.
- `src/L/Coding/Shape.lagda.md`, read the shape frame and the machine's
  `shapes`/`ShapeWit` readers (`:100-240`, `:234-331`). Took the row
  structure that fixed the lift kit's row order.
- `archive/rud-route/`, SHAPE only: the README and file list. WHY NOT
  more: `[LJ-1.11]` ruled its condensation content classically false,
  and the brief forbids taking a price from it.
- `dev/LESSONS.md`, via `scripts/rules.py --for build` and `--for
  probe`, read the whole bundles (D-1, P-c, P-h, P-i, P-k, P-l, P-m,
  P-n, P-t, P-u, P-v, R-35, R-36, R-38, R-40, I-5, C-12, C-22,
  C-31..C-37, D-8, D-10, D-26, D-29, D-30). Took P-t (the assembly as
  a telescope), D-30 (the consumer direction), C-32 (re-measure the
  gate on the cured tree: the master was measured, not the probe
  alone), and C-22 (this report written incrementally).

## 8b. GATES

`scripts/check-fences.py --check` clean (84 masters). `scripts/
lint-prose.py --check` exit 0 on the edited master, both probes and
this report. `scripts/lint-agda.py --check` exit 0. `scripts/ledger.py
--check` clean; the worktree count of `L.Condensation` is 5,027
(HEAD 4,640). `L.BoundedSubset` (the only consumer) re-checks green.
No `make check` was run, per the brief. No commit, no push.

## 9. LITERATURE USED

Nothing in the literature bears on a placement cost. Spend nothing.

# LJ-1.60: build Lift12Out, then place the rest of the leaf chain

Status: COMPLETE, written incrementally per C-22. ASD-STE100.
No commit. No push. The working tree carries this dispatch's edits.
This report is `_build/lj-1.60-report.md`.

## 0. THE VERDICT

**NO-GO, MEASURED: the whole-file rate after `Lift12Out` is 0.013572,
over the DD24 live bar 0.012716.**

`Lift12Out` was built, the forward walk was placed with it, and the
whole file was measured: 5,562 in-fence lines at a mean 75.49 s user
(three cold runs, 75.43 / 75.33 / 75.71, spread 0.5 pc). The marginal
rate of the placement is (75.49 - 64.35) / 207 = **0.0538 s per
line**, 3.05x the back-direction class ([LJ-1.58] measured 0.01765).
The bar ceiling at 5,562 lines is 70.73 s; the placed file measures
75.49 s, 4.76 s over its own ceiling. The cure hypothesis from
`[LJ-1.59]` (that the `Lift12Out` spelling would land the forward
walk in the back-direction rate class) is **INFERRED there, and this
dispatch measured it false at its own site** (P-l). The forward walk
at the kit spelling is cheaper than the hand-written chain it
replaces (0.0538 against 0.0788 per line, 207 against 732 lines) but
it does not close the wall.

Per the pre-fixed abort criterion (D-1), the dispatch STOPS here: the
rest of the chain is not placed and `levelIn`/`cover` are not
discharged. A measured NO-GO with a number is the full deliverable.
The working tree carries the measured placement (visible, uncommitted)
and this report.

## 1. THE WALK `out` AT THE LIFT KIT SPELLING

The machine -> story half of the twelve-row walk was placed in
`src/L/Condensation.lagda.md`, ported from `src/ProbeLJ156A.agda`
section 6 and `src/ProbeLJ157A.agda` sections 1 to 3:

- `TmBranch.in'` with the `inK` parameter (`src/L/Condensation.lagda.md:5259`)
- `TmAgree.in'` with the `carrierK`/`arityK` parameters (`:5319`)
- `BothTmRel.back`, `FstTmRel.back` with the same parameters (`:5347`, `:5375`)
- `TopBinRel.back`, `TopUnRel.back`, `ZeroPayRel.back` (`:5399`, `:5408`, `:5417`)
- `BinFormAgree.out` with the `C`/`compK`/`relBack` parameters (`:5428`)
- `UnFormAgree.out` with the `C`/`unCompK`/`relBack` parameters (`:5511`)
- `Lift12Out`, the mirror kit (`:5649`)
- `ShapesAgree.out` with the `C`/`carrierK`/`arityK`/`compK`/`unCompK`
  parameters (`:5665`, `out` at `:5777`)

The file gains 207 in-fence lines (5,355 to 5,562). The content class
is mixed, per P-m: the kit (`Lift12Out`, the relations, the new module
parameters) is parameterized content; the `out`/`in'` row proofs are
instantiation content (each statement carries the satisfaction
machinery: the code-set membership `c∈C`, the `compK`/`unCompK`
decompositions and the `arityTagAtL-adequate`/`arityTagPairAtL-adequate`
transports). The once-per-statement normalization the kit confines is
visible in the profile: `ShapesAgree.out` costs 2,225 ms on its own,
against the 28.6 s the hand-written chain cost at `[LJ-1.59]` (732
lines at 0.0788).

| module | runs, user s | mean | spread | content lines | rate |
|---|---:|---:|---:|---:|---:|
| `L.Condensation` baseline (HEAD e7c8f99) | 64.08 / 64.56 / 64.40 | 64.35 | 0.48 (0.7 pc) | 5,355 | 0.012017 |
| + walk `out` at the `Lift12Out` spelling | 75.43 / 75.33 / 75.71 | 75.49 | 0.38 (0.5 pc) | 5,562 | 0.013572 |

Marginal: (75.49 - 64.35) / 207 = 0.0538 s/line; the pairwise deltas
are 0.0548 / 0.0520 / 0.0546. The whole-file rate 0.013572 is OVER
the DD24 live bar 0.012716 (6.7 pc over; the gap is 13x the run
spread).

Profile attribution (one cold run of the placed state, total 74.6 s):
`Miscellaneous` 40.3 s, `ShapesAgree.out` 2.2 s, `PropAgree.subB2T-back`
2.3 s (block 1, pre-existing), every other new definition under 25 ms.
The attributed new-definition cost is about 2.4 s; the rest of the
11.1 s marginal sits in header/instantiation elaboration. Whether the
40.3 s `Miscellaneous` is larger than the baseline's is not directly
measured (no baseline profile was taken); that attribution is
INFERRED.

## 2. THE REST OF THE CHAIN

**NOT PLACED.** The pre-fixed criterion stops the dispatch the moment
a step crosses the bar, and the first step (the walk `out`) crossed
it. The dispatch stopped before `ShapedAgree`. `ShapedAgree`,
`WitnessAgree`, `KeyAgree`/`DefinesAgree` (`src/ProbeLJ154A.agda`),
the `TwelveAgree` composition (`src/ProbeLJ155B.agda:788`),
`SatGraphAgree` (`src/ProbeLJ156A.agda` section 7) and `LeafAgree`
(`src/ProbeLJ157A.agda` section 5) are ports of green probe content,
not re-proofs; each would add seconds at its own measured class, and
the file is already 4.76 s over its ceiling, so every further line
makes the ratio worse. Their placement classes were NOT re-measured
at their sites (P-l); no negative about them is a verdict.

## 3. levelIn AND cover

**Neither is discharged.** The term I could not write, per C-36, is
the forward (machine -> story) direction of the twelve-row walk in a
spelling that keeps the whole-file rate at or under 0.012716. The
`Lift12Out` spelling I built typechecks and is placed, but measures
0.013572 whole-file. Everything downstream of the walk
(`ShapedAgree` through `LeafAgree`, then the post-leaf five of
`[LJ-1.57]` section 8: `StepAgree`/`ApproxAgree`, `GraphAgree`, the
stage truth of `Adeq m`, the ElemDown wiring, the collapse of the
level) and then `levelIn`/`cover`
(`src/L/BoundedSubset.lagda.md:916-917`) was not attempted, because
the chain's first unplaced step is already over the bar.

**Where this dispatch stopped, in the ledger's terms:** after
`Lift12Out` + `ShapesAgree.out` (the walk `out`), measured NO-GO at
0.013572 whole-file; before `ShapedAgree`. The worktree count of
`L.Condensation` is 5,562 in-fence lines (HEAD 5,355).

## 4. THE RATES

Caliber: C-12 `GHCRTS="-A64m -I0 -M8g"`, user seconds from
`/usr/bin/time -p`, cold module (the module's own interface moved
aside before EVERY run), dependencies warm, one process, three
completed runs per figure. No heap exhaustion; every run exited 0.

| module | runs, user s | mean | spread | in-fence lines | rate |
|---|---:|---:|---:|---:|---:|
| `L.Condensation` baseline (HEAD e7c8f99) | 64.08 / 64.56 / 64.40 | 64.35 | 0.48 (0.7 pc) | 5,355 | 0.012017 |
| + walk `out` (kit spelling) | 75.43 / 75.33 / 75.71 | 75.49 | 0.38 (0.5 pc) | 5,562 | 0.013572 |

| marginal | lines | mean user s | rate |
|---|---:|---:|---:|
| walk `out` at the `Lift12Out` spelling | 207 | 75.49 - 64.35 = 11.14 | 0.0538 |

Pairwise deltas: 0.0548 / 0.0520 / 0.0546. Cone:
`L.BoundedSubset` (the only consumer), cold with its own interface
aside and dependencies warm, three runs: 14.10 / 14.04 / 14.15 s
user, mean 14.10, spread 0.11 (0.8 pc), exit 0 on every run. The
consumer re-checks green against the placed master.

**LOAD CAVEAT, MEASURED:** the machine load average during the runs
was 2.3 to 3.2 (4 users), against the quiet machine the protocol
assumes; it was above 2 on every run, so every absolute figure carries
the caveat. The pairwise deltas and the placed-vs-baseline comparison
are same-session and comparable.

## 5. DD4

**The placed content keeps the template shape, and the two proofs
share the maximum code.** No placed type mentions a concrete carrier:
the walk, the row agreements, the frame agreements, the relations and
both kits state slots, environments and site facts as module
parameters at `S ^ n` environments, exactly as the back direction did.
The J tower inherits the whole generic layer unchanged.

`Lift12Out` is the mirror WITHOUT a second copy: its body is one
module instantiation of `Lift12Back` at the same abstract
propositions, with the row functions passed the other way
(`src/L/Condensation.lagda.md:5649-5663`). The twelve-row disjunction
walk exists once. The name exists for P-v: `ShapesAgree.out` passes
the name instead of re-stating the walk. No tower-specific spelling
was needed; the forward direction is the same template content either
tower consumes.

**The trade, named:** the `out` row content carries the code-set
membership (`c∈C`) and the component-in-K site facts (`compK`,
`unCompK`) that the `back` rows never carried, so the out block is its
own measured class (0.0538 s/line), not the back class (0.01765).
That is a content difference, not a spelling difference.

## 6. THE CONVERGENCE ANSWER

**The wall is priced, and it is a NO-GO at the kit spelling.** The
phase arithmetic: at 5,355 lines the bar ceiling is 68.10 s and the
measured baseline is 64.35 s, leaving a 3.75 s margin. The walk `out`
added 11.14 s, so it overruns the available margin by 7.4 s; at 5,562
lines the placed file measures 75.49 s against a 70.73 s ceiling.
The obligation is not renamed: `levelIn`/`cover` still need the
machine -> story chain, the chain's first step is the walk `out`, and
that step is now priced at the master at 0.013572 whole-file, over
the bar. The `[LJ-1.59]` cure hypothesis is measured at its own site
and does not close the wall; the next ruling belongs to the owner,
on the price: the forward walk costs 207 lines and 11.14 s at the
cheapest spelling this dispatch found.

## 7. NEGATIVES AND THEIR STATUS

1. The `Lift12Out` spelling of the forward walk places at 0.0538
   s/line and takes the whole file to 0.013572, over the bar:
   **MEASURED** (three cold runs each side, one caliber, section 4).
2. The cure would close the wall at the back-direction rate class:
   **INFERRED** by `[LJ-1.59]`, and now REFUTED at this site by
   measurement (the out block measures 3.05x the back rate). The
   inference set no verdict; the measurement set NO-GO.
3. The residual cost sits in the out-direction instantiation content
   and in header/instantiation elaboration: **PARTLY MEASURED**
   (`ShapesAgree.out` 2,225 ms; all other new definitions under
   25 ms; `Miscellaneous` 40.3 s in the placed profile), **PARTLY
   INFERRED** (the delta's `Miscellaneous` share; no baseline profile
   was taken). This negative sets no verdict.
4. `levelIn` and `cover` are not discharged: **MEASURED** (the
   chain's first unplaced step is the walk `out`, whose measured price
   is over the bar; the downstream terms were not attempted because
   the pre-fixed criterion stops at the first crossing).
5. The absolute figures are load-confounded (load average 2.3 to
   3.2, above 2): **MEASURED**; the same-session deltas and the
   placed-vs-baseline comparison are the comparable figures.

## 8. ARCHIVE USED

- `_build/lj-1.59-report.md`, read WHOLE. TOOK section 0 (the
  direction answer: producing `Adeq m` needs machine -> story),
  section 1.4 (the measured wall: the hand-written forward walk at
  0.0788 s/line over 732 lines, whole-file 0.01584, reverted),
  section 2 (the remaining chain) and section 3 (the protocol).
  `:35-58` carried the wall table; the negative list at `:344-365`
  classed the `Lift12Out` cure INFERRED, which this dispatch measured.
- `_build/lj-1.58-report.md`, read WHOLE. TOOK section 2 (the
  `Lift12Back` spelling and its 4.28x), section 3 (the rates and the
  protocol) and section 4 (what is placed). `:5083-5509`-shaped
  content is the model the mirror reuses.
- `src/ProbeLJ157A.agda`, read WHOLE. TOOK the two-way frame
  agreements and relations (sections 1 to 2, `:58-226`), the walk
  (`:228-659`), `ShapedAgree`/`WitnessAgree` (section 4, `:660-821`)
  and `LeafAgree` (section 5, `:822-985`). The file is untouched.
- `src/ProbeLJ156A.agda`, read WHOLE. TOOK `TmBranch.in'`/`TmAgree.in'`
  (section 6) and `SatGraphAgree` (section 7, `:689-835`). The
  `in'` proofs are what the walk `out` needed and were placed.
- `src/ProbeLJ154A.agda`, read WHOLE. TOOK `KeyAgree`/`DefinesAgree`
  (the unplaced ports, `:111-246`).
- `src/ProbeLJ155B.agda`, read the twelve-row composition
  (`TwelveAgree` at `:788`, `out`/`back` at `:951`/`:966`). TOOK the
  composition shape; not placed.
- `src/ProbeLJ152A.agda` and `src/ProbeLJ152B.agda`, read WHOLE.
  TOOK `GraphAgree` (`:40-47`), `matrix-decode` (`:57-64`) and
  `graph-assembly` (`:71-87`): the pinned consumer statements behind
  the direction answer.
- `_build/lj-1.52-report.md`, read the obligation sections. TOOK the
  `Adeq`-form chain (`:20-44`) and the `levelIn`/`cover` rows
  (`:17-18`).
- `_build/lj-1.51-report.md`, read the survivor sections. TOOK the
  `levelIn`/`cover` statements (`:135-172`) and the post-leaf chain.
- `src/L/BoundedSubset.lagda.md:916-917`, read the `Condense`
  hypotheses. TOOK `levelIn` and `cover` as the pinned targets
  (the brief's `:598-599` line references are stale; the current
  statements sit in `HullStage.Condense`).
- `archive/rud-route/`, SHAPE only (the README and the file list).
  WHY NOT more: `[LJ-1.11]` ruled its condensation target classically
  false, and the brief forbids taking a price from it.
- `dev/ledger.toml`, read the `[ratio]` provenance blocks
  (`:230-250`, `:2560-2600`) and `gch_wing` (`:2855-2862`). TOOK the
  live bar 0.012716 (the AC module rate 0.011057 at the 1.15
  tolerance) and the wing list; the ledger itself was not edited.
- `dev/LESSONS.md`, via `scripts/rules.py --for build` (the whole
  bundle). TOOK P-t (the lift-kit spelling), P-l (re-measure at the
  site: the out block was measured at the master, not priced from
  the back analogue), P-m (the content classes), P-v (named proofs),
  C-12 (the heap cap), C-22 (this report written incrementally),
  C-34 (build the cure or report the wall) and C-36 (the term not
  written).

## 9. LITERATURE USED

Nothing in the literature prices a placement. `[LJ-1.59]` already
read Devlin Step C and banked the answer: the elementarity step
transfers the bounded statement, and the production side is a tree
fact, not a literature fact. Spend nothing.

## 10. GATES

`scripts/check-fences.py --check` clean (84 masters).
`scripts/lint-prose.py --check` exit 0 on the edited master.
`scripts/lint-agda.py --check` exit 0. `scripts/ledger.py --check`
clean; the worktree count of `L.Condensation` is 5,562 in-fence lines
(HEAD 5,355). `L.BoundedSubset` (the only consumer) re-checks green
at 14.10 s user mean (its recorded band). No `make check` was run,
per the brief. No commit, no push. The working tree carries the
master edit and this report; `src/ProbeLJ157A.agda` is untouched.

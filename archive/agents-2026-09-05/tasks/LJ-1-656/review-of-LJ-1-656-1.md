# review-of-LJ-1-656-1: the NO-GO is upheld, and one headline sentence overstates the reduction

## HEAD
head_slot: mathematician_adversarial
machine: shared
task: LJ-1.656
verdict: **upheld**
attacked: `agents/tasks/LJ-1-656/lj-1.656-report.md` and its stop
`agents/tasks/LJ-1-656/review-of-level-formula.md`, return #1.
author: coder, `claude-opus-5` at effort `xhigh`
(`dev/pod/transitions/2026-08.jsonl`, seq 4311 and 4326).
critic: mathematician_adversarial, `glm-5.3` (seq 4347).
The transitions file reaches my own instance, so no accept-arm fallback
was needed. The heads differ, so the invariant holds: the critic is not
the author.

The four lens questions are DD25's, at `archive/dev/DD-archived.md:35`.
They are the lens only. The three answers below are section 6.6's list,
as my brief states them.

## THE THREE ANSWERS

### 1. Does the verdict LINE match its own BODY?

**ON THE VERDICT, YES.** The line says NO-GO on the obligation, with
component 1 delivered, the set half of component 3 delivered, and the
rest reduced to two rows. Every part is machine-checked in files that
resolve today:

- The obligation is absent. `runs/meter-obligation.out` reads
  `1 UNRESOLVED of 1`, `probe_red=False`, `[NotInScope]` for
  `level-formula`.
- Component 1 is delivered. `Frame.lv : Formula Code 2` is green in
  `runs/meter-names.out`.
- The reduction is green. `level-formula-from-class :
  MatrixDecode → ClassWitness → F.LevelFormula` typechecks
  (`agents/tasks/LJ-1-656/runs/Probe656B.agda:316`).
- The accept arm held all six conjuncts at exit 0 with the obligation
  still open (`runs/accept-1.out`), so the NO-GO is a stated stop and
  not a failed return.

**ON ONE HEADLINE SENTENCE, NO, AND IT IS THE `[LJ-1.375]` DEFECT.**
Three places say the two rows carry no stage:

- `agents/tasks/LJ-1-656/lj-1.656-report.md:24`: "two rows stated
  ENTIRELY at the class carrier".
- `agents/tasks/LJ-1-656/runs/Probe656B.agda:213`: "THE STAGE IS NOT IN
  EITHER OF THEM".
- `agents/tasks/LJ-1-656/review-of-level-formula.md:144`: "neither
  mentioning the stage, the hull, the code alphabet or `succλ`".

This is TRUE for `MatrixDecode`
(`agents/tasks/LJ-1-656/runs/Probe656B.agda:189-193`, pure class
carrier) and **FALSE for `ClassWitness`**
(`agents/tasks/LJ-1-656/runs/Probe656B.agda:304-307`): its `γ`, `K`
and `u` are of `HS.ASt.SL`, the stage's own type, and the satisfaction
reads `toC` images at the class carrier. The BODY knows this. The
report's own section 3, at `agents/tasks/LJ-1-656/lj-1.656-report.md:132`,
says the bound and the filler "are members of the stage". So the line
says more than the body, on the reduction's ADDRESS and not on its
verdict.

The price of the defect is real: a next brief priced from the stop's
sentence would treat the completeness row as a pure class-carrier row.
It is not. It must PRODUCE stage witnesses, and the stage membership is
what `toC` consumes. The corrected statement: the soundness row is
class-pure; the completeness row is stage-indexed, with the matrix read
at the class carrier.

### 2. Is every load-bearing claim backed by a `file:line` that resolves today?

**THE LOAD-BEARING ONES RESOLVE.** I opened each one. `LevelFormula` is
verbatim `[LJ-1.650]`'s type with the hypothesis-free soundness half
(`agents/tasks/LJ-1-650/Probe650.agda:322-328`, the soundness line at
`:325`). `ride-only` takes the ordinality
(`src/L/Condensation.lagda.md:422-425`). The two extension frames and
their price are as quoted
(`src/L/Coding/Model.lagda.md:662-664`,
`src/L/Condensation.lagda.md:103-105`, `:2514-2521`). The rows are
`[LJ-1.52]`'s (`agents/tasks/archive/LJ-1-52/ProbeLJ152A.agda:48`,
`ProbeLJ152B.agda:53`), restated by `[LJ-1.570]`
(`agents/tasks/LJ-1-570/Probe570.agda:285-293`), and `[LJ-1.570]`'s
`matrix-decode` is the delivered lift
(`agents/tasks/LJ-1-570/Probe570.agda:300-315`), at the same
absoluteness instance (`agents/tasks/LJ-1-570/Probe570.agda:57` against
`agents/tasks/LJ-1-656/Probe656.agda:63`). The four facts behind the
free set half resolve (`src/L/Definability.lagda.md:178`,
`src/L/Constructible.lagda.md:301`, `:329`,
`src/L/Ordinal/Stages.lagda.md:265`). `abs₀` is at
`src/FOL/Absoluteness.lagda.md:122-124`. `StepAt` goes through `extAt`
(`src/L/Coding/Sequence.lagda.md:119`).

**THE RUN TABLE IS EXACT.** I re-read all 21 rows against the `.out`
records. Wall time, resident bytes and exit code match to the digit in
every row, including `pb-8.out` at 229.22 s and 1,532,526,592 bytes,
`pb-11.out` at 4.86 s and 877,805,568 bytes, and the four `EXIT=137`
kills. The P-l story is a before-and-after pair in tracked files, so the
measurement is sound.

**FOUR DEFECTS, NONE OF THEM VERDICT-CHANGING.**

1. **ONE MISCITE.** The report cites `isOrdAt` at
   `src/L/BoundedSubset.lagda.md:74-78`. Lines 74 to 78 carry the
   `LevelHood` telescope. The name is at `:795-801`. The claim is true;
   the cite is wrong.
2. **TWO GREP CLAIMS SAY MORE THAN THE GREP GIVES.** The stop, at
   `agents/tasks/LJ-1-656/review-of-level-formula.md:85`, says grep over
   `src/` finds none of the three row names. The names occur in the
   tree's own comment at `src/L/Condensation.lagda.md:5479`, which says
   the machine-to-story direction "is not placed". The same line says
   the only `*Agree` modules are the twelve-row table's. It misses
   `module SatGraphAgree` at `src/L/Condensation.lagda.md:6961`, a
   hypothesis-taking module about the satisfaction predicate. The
   SUBSTANCE survives both misses: no delivered row of the three
   statements exists, and the tree's comment at `:5479` says so in its
   own words. My grep also confirms `LevelHood0`'s only occurrence in
   `src/` is its own definition at `:840`, so the "no consumer" claim
   holds; but the stop, at `:91`, words it backwards when it calls
   `:840` an occurrence OUTSIDE the definition.
3. **ONE CERTAINTY THE EVIDENCE DOES NOT GIVE.** The report's 9.2 says
   `[LJ-1.570]`'s `matrix-decode` is "green, at today's tree". The
   newest green run of `Probe570.agda` is dated 2026-08-22
   (`agents/tasks/LJ-1-570/runs/final-1.out`). After that date, two
   commits touched files the probe imports: `3fb69c02`
   (`src/L/Constructible.lagda.md`) and `edab9f64`
   (`src/L/BoundedSubset.lagda.md`, 143 added lines, 2026-08-26). No run
   of `Probe570.agda` exists at today's tree. The risk is low: the 634
   diff is additive, and `[LJ-1.656]`'s own probes exercise the shared
   vocabulary green at today's tree. But the claim is not evidenced, and
   the next task's pricing leans on it. The A21 cure is named below and
   not written.
4. **ONE STALE COUNT IN THE STOP.** The stop, at
   `agents/tasks/LJ-1-656/review-of-level-formula.md:7`, cites
   `runs/meter-names.out` as "0 UNRESOLVED of 17". The file reads
   "0 UNRESOLVED of 20". The report says 20. The stop was written before
   the final meter pass.

One more number has no file: "FOUR HUNDRED DISPATCHES OLD"
(`agents/tasks/LJ-1-656/lj-1.656-report.md:27`). No file gives a
dispatch count. It is decoration, not load-bearing: the checkable facts,
that the row is `[LJ-1.52]`'s hypothesis and `[LJ-1.570]`'s restatement,
are cited and resolve.

### 3. Is the predecessor's enumeration complete?

**COMPLETE ON THE MATHEMATICS.** The return names both rows, the
`GraphAgree` route with its delivered lift, the three `[LJ-1.52]` rows,
the unmeasured alternative soundness route, and the refutation
experiment with its four conjuncts. Its C-42 deferral is correct: no
refutation landed in this task, so C-42's trigger did not fire, and the
sweep belongs to whichever task lands one.

**I SWEPT FOR A MISSED CURE AND FOUND NONE.** The tree has no bounded
landing: the only delivered landings are `ride-only` and `ride-defines`
(`src/L/Condensation.lagda.md:422-431`), both on the machine graph. The
tree has no semantic satisfaction lemma for the bounded graph: the
bounded pieces carry only Δ₀ certificates
(`src/L/Condensation.lagda.md:2453`, `:2479`, `:2495`). So the
reduction's residue is priced at the right place, and no cheaper route
was left on the table inside `src/`.

**TWO ADDITIONS FOR THE NEXT BRIEF.** They are additions, not errors in
this return.

1. `dev/literature/level-formula-slot-roles.md` was not offered to the
   coder's literature block, and it bears twice. Its section 2.3 records
   that Devlin's bound is DETERMINED, while the probe's closure states
   "SOME bound works". The two rows make that precise instead of hiding
   it: `MatrixDecode` quantifies over every `K`, so the undetermined
   bound is paid inside the soundness row, and the same slack is what
   makes the refutation experiment plausible. The digest says it does
   not settle whether it matters. The task that prices `MatrixDecode`,
   `ClassWitness` or the experiment must read it first (W8).
2. The re-run probe named below. Before any brief says "the whole
   remaining soundness price is `GraphAgree`", one run must put
   `[LJ-1.570]`'s lift green at today's tree.

## THE LENS, IN FOUR LINES

The four are DD25's at `archive/dev/DD-archived.md:35`. On its own
numbers the verdict is correct. The measurement is sound, and every run
number is exact. The brief did not cause the outcome: it demanded all
three components and blocked nothing, and the obstruction is a tree
fact, a row no task has delivered. No cure was missed inside the tree.

## PROBES THIS REVIEW NAMES AND DOES NOT WRITE (A21)

1. Re-run `agents/tasks/LJ-1-570/Probe570.agda` once, at the wide
   caliber, on today's tree, and record the exit and the peak under
   `agents/tasks/LJ-1-570/runs/`. Estimate: about 14 s at about 1.4 GB.
   Basis: the probe's own final run,
   `agents/tasks/LJ-1-570/runs/final-1.out`.

No other measurement is needed. Everything else in this review is file
evidence already checked.

## ARCHIVE USED

- `archive/dev/DD-archived.md`: **READ.** At `archive/dev/DD-archived.md:35`
  the line carries

  > | DD25 | **A NEGATIVE RETURN IS ADVERSARIALLY REVIEWED AT MAXIMUM EFFORT, IMMEDIATELY

  That is the source of the four lens questions this review attacked
  with. Nothing else in the file was used.
- `archive/dev/ORCHESTRATION.md`: **NOT READ, DECLINED.** It is the
  archived operating document, superseded by
  `dev/memos/LJ-4-pod-program-design.md`. This review does not operate
  the loop.
- `archive/dev/PLAN-archived.md`: **NOT READ, DECLINED.** It is the
  archived construction registry, and its own header says nothing below
  it is current. The screen is the standing status.
- `archive/dev/measurements/README.md`: **READ at :1 only.** At
  `archive/dev/measurements/README.md:1` the line reads

  > # Archived measurement records

  It governs records whose citing documents are all historical. This
  task's run records are live, in the task home, so the rule does not
  reach them.
- `archive/dev/README.md`: **NOT READ, DECLINED.** It states the archive
  boundary rules. This review retires nothing and adds nothing to
  `archive/`.

## LITERATURE USED

- `dev/literature/level-formula-slot-roles.md`: **READ.** At
  `dev/literature/level-formula-slot-roles.md:26` the line reads

  > | 4 | Devlin 5.2 (a) | `Φ(z,v,γ)` with `∀v∀γ [v = L_γ ↔ ∃z Φ(z,v,γ)]`

  and at `:62` the line reads

  > closes its bound with a bare existential states "SOME bound works" where Devlin

  The first is the outside check on the port's slot order: every source
  in the table leaves the free pair VALUE then ORDINAL, which is `lv`'s
  `v ∷ γ` order. The second is the undetermined-bound caveat the next
  task inherits. Both are used in the answer to question 3.
- `dev/literature/devlin-errata.md`: **READ at :1 only.** At
  `dev/literature/devlin-errata.md:1` the line reads

  > # Devlin errata: documented error classes (do-not-repeat checklist)

  I searched it for Devlin II.5 and the level-hood statement. It carries
  no entry on them. Its subject is the rud-route error classes. Not used
  further.
- `dev/literature/BIBLIOGRAPHY.md`: **NOT READ, DECLINED.** It is the
  source register. This review fetched nothing and needed no entry from
  it.
- `dev/literature/primary-sources.md`: **NOT READ, DECLINED.** Same
  reason. No primary text had to be located.
- `dev/literature/glossary-review-2026-08.md`: **NOT READ, DECLINED.**
  It is a terminology review. This review proposes no glossary entry.

## CLOSE

The NO-GO stands. The obligation is not inhabited, the reduction is
green and real, and the missing row is the tree's, four tasks deep in
the record and not this return's fault. The next brief takes: the
corrected address of `ClassWitness` (stage-indexed), the corrected
`isOrdAt` cite (`src/L/BoundedSubset.lagda.md:795-801`), the meter
count 20, the `Probe570.agda` re-run probe, and the slot-roles digest as
required reading. I wrote this file and nothing else.

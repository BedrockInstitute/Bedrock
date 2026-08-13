# LJ-1.38 report: the step and graph stack, and leg D at the master

Status: COMPLETE. Written incrementally per C-22. No commit, no push.
The report uses ASD-STE100.

## 1. THE VERDICT

**REFUSED with a measurement.** The bounded matrices land. The
story-to-machine agreement does not. The delivered story rows do not
agree with the machine's rows. The brief's atom-row quirk is
mislocated: the machine reads the term slot `b`, and the story's rows
carry the deviations. The stop-line fires at the atom rows, for the
opposite reason from the brief's premise.

What lands: block 3 of `src/L/Condensation.lagda.md`, 110 in-fence
non-blank lines, the bounded matrices for `StepAt`, `ApproxAt` and
`LsetGraphAt`. The master checks cold in 9.60 and 9.65 seconds of user
time, one process, at `GHCRTS="-A64m -I0 -M8g"`, dependencies warm.
The rate is 0.00449 seconds per line over 2,141 in-fence lines, 0.34
of DD24's bar of 0.013193.

## 2. THE ATOM ROW

**The brief's quirk is not in the machine.** The machine's `atomBody`
reads the second term from the TERM slot `b`, not the VALUE slot `yc`.
The slot definitions are at `src/L/Coding/Model.lagda.md:1746-1751`:

| slot | value | the comment's name |
|---|---|---|
| `a9″` | 6 | `a` |
| `b9″` | 5 | `b` |
| `e9″` | 2 | `e` |
| `v9″` | 1 | `v` |
| `w9″` | 0 | `w` |

The innermost point is `w = 0, v = 1, e = 2, E = 3, yc = 4, b = 5,
a = 6` (`Model.lagda.md:1745`). The machine reads
`tmValAt a e v` and `tmValAt b e w`, at the extAt candidate `e`
(`:1753-1759`). That is the correct reading. The cited lines
`1765-1770` are inside `AtomWit`, not the slot definitions. The git
history confirms `b9″` has always been `suc (suc (suc (suc (suc
zero))))` in every commit that touched the file. The LJ-1.37 finding
misread the machine.

**The real deviation is story-side.** The story's atom rows evaluate
the two terms at the frame's member `e` of `yc`, not at the extAt
candidate. In `atomBodyB` (`Condensation.lagda.md:940-957`), the two
`tmValB` environment arguments are `suc (suc (suc zero))` (`:946`,
`:952`), which is the frame's `e` at the innermost point. The machine
evaluates at its candidate. The story's frame `binEnvAt`
(`:710-722`) adds an `e ∈ yc` binder the machine does not have, and
the body uses it.

The story-side deviations, by row:

| row | story | machine | evidence |
|---|---|---|---|
| Mem, Eq | terms at frame `e` | terms at extAt candidate | `Condensation:946,952` against `Model:1753-1759` |
| Forall | extended env in `E` | extended env in the subvalue | `Condensation:1142` against `Model:1570-1573` |
| AllIn, ExIn | bound term at frame `e`; extended env in `E` | bound term at candidate; extended env in the subvalue | `Condensation:1000,1009, 1018,1027` against `Model:1854-1865` |
| Exist | no `extAt`, one direction only | `extAt`, both directions | `Condensation:1375-1381` against `Model:1590-1594` |
| all rows | `e ∈ yc` binder makes the row vacuous for empty values | `extAt` constrains empty values | the five frames at `Condensation:632,652,671,688,710` |

The fifth row is the systematic one. Every story frame ends in
`∀̇∈ (var (suc (suc zero))) body`, which is `for every e ∈ yc`. For an
empty value `yc` the universal is vacuously true, so the row asserts
nothing. The machine's rows end in `extAt yc body`, whose second
direction `∀̇ (body ⇒̇ z ∈ yc)` constrains an empty value: it forces
the satisfier set to be empty. The two are not equivalent, so the
adequacy cannot close for any row.

**What each option costs.**

| option | cost | verdict |
|---|---|---|
| fix the machine's private body | not needed; there is no machine defect. The one-character edit would re-check Model and its 26 consumers, far over the 4-second survey (C-32) | walled, and unnecessary |
| re-derive the machine's row | not needed; the machine is correct | walled, and unnecessary |
| rework the story's rows | a re-lay of the five frames, the twelve bodies, the certificates and the frame decodes, with every row's semantics re-verified against the machine. It re-opens LJ-1.37's delivered block 2 and invalidates its measurements (C-32) | exceeds the block's survey; a new dispatch |

The honest agreement for the atom rows is not definitional, and it is
not closeable as delivered. It is closeable after the story-side
rework, at the price above. I did not silently weaken the story to
make the rows fit.

## 3. DID YOU NEED A PLACEMENT ANYWHERE?

**NO.** No `absFo`, no `placeFo`, no constant vector and no appended
environment appear anywhere in block 3. The matrices are constant-free
at the outer level (the leaf content `DefBodyB` carries the numerals,
which are delivered). Every certificate is stated on the unplaced
formula. P-u holds.

## 4. WHAT LANDED

Block 3 of `src/L/Condensation.lagda.md` (`:2255-2381`):

1. `StepB`, the bounded step matrix, generic in the leaf content `ψ`
   (`:2275-2321`). This is the [LJ-1.34-R] D5 shape with K a
   parameter. Its certificate closes from `Δ₀ ψ`.
2. `StepAtB`, the concrete step matrix at the class carrier, with the
   leaf fixed to `DefBodyB` (`:2327-2341`). Its certificate closes
   from the delivered `Δ₀-DefBodyB`.
3. `ApproxB`, the bounded approximation matrix (`:2350-2367`).
4. `GraphB`, the bounded graph matrix (`:2369-2381`).

Each matrix rides the delivered bounded atoms and the delivered
description. Nothing re-states the machine's reading.

What does NOT land: the leg-D agreements and the description's
adequacy. Both are blocked at the rows (section 2). The step
agreement's shape is the D5 generic layer, which is green in
`src/ProbeDD25D5.agda` and carries the site facts as hypotheses; the
concrete discharge is the adequacy, which the rows block.

## 5. THE NUMBER

| file | in-fence non-blank lines |
|---|---:|
| `src/L/Condensation.lagda.md` | 2,141 |
| of which block 3 | 110 |
| `src/ProbeLJ138A.agda` | 176 |
| `src/ProbeLJ138Ctrl.agda` | 23 |

The ledger's standing figure for Condensation was 2,031
(`_build/lj-1.37-report.md:105-108`); block 3 adds 110. The catalog is
untouched.

## 6. SECONDS AND RATE

Cold runs, one Agda process each, quiet machine, at
`GHCRTS="-A64m -I0 -M8g"`, the master's own interface moved aside per
run, dependencies warm:

| run | user s | wall s |
|---|---:|---:|
| 1 | 9.65 | 9.91 |
| 2 | 10.24 | 10.61 |
| 3 | 9.60 | 9.96 |

Run 2 is the outlier; runs 1 and 3 are flat (delta 0.05). The reported
figure is the flat pair: 9.60 to 9.65 seconds of user time. The rate
is 9.65 / 2,141 = 0.00449 seconds per line, 0.34 of DD24's bar of
0.013193.

The cone, measured with the imports-only control
`src/ProbeLJ138Ctrl.agda` in the same session: 1.15 and 1.04 seconds
of user time. The net content cost is about 8.5 seconds over the
2,141 lines, which is 0.00397 seconds per line.

C-31 framing: the GCH side's whole budget is 99.6 to 147.7 seconds
(`dev/ledger.toml:305`). This master's whole measured cost is about
9.6 seconds, 10 percent of the budget's low end. The block-3 content
adds about 0.3 to 0.6 seconds of check time on top of the delivered
2,031-line master, against the block's 1.5 to 4 second survey.

The meter caveat from `[LJ-1.35]` applies: the cone is about 1.1
seconds of the 9.6, so the per-module rate mostly measures the cone
plus the delivered deep-leaf witnesses. The block-3 content itself
checks at the formula class.

## 7. WHAT CONDENSATION STILL OWES

1. The story-side row rework, priced in section 2: re-lay the five
   frames, the twelve bodies, the certificates and the frame decodes
   so the rows match the machine's `extAt` semantics. Survey: the
   delivered block 2 is 1,496 lines of row content
   (`_build/lj-1.37-report.md:105-108`); the rework touches most of
   it. Check time at the measured 0.0045 seconds per line is within
   the 4-second survey, but the rework re-opens delivered content and
   invalidates its measurements (C-32). It needs a dispatch of its
   own, with the machine's row semantics pinned first.
2. The twelve-row agreement, after the rework: the bounded rows
   against the machine's rows under the site facts. `[LJ-1.36]`
   measured the row extraction class at under 0.12 seconds total; the
   agreement class is the same family.
3. The description's adequacy, after the row agreement: `DefBodyB`
   against the machine's `DefBody` leaves under the site facts, codes
   in K and values in K. The certificate is delivered; the
   satisfaction-level agreement is not.
4. Leg D at the master: the step, approximation and graph agreements,
   D5-shaped, with the adequacy as the leaf discharge.

`[LJ-1.7]` needs this block. It needs the row rework first.

## 8. DD4

| piece | side |
|---|---|
| `StepB`, `ApproxB`, `GraphB`, the matrix frames | TEMPLATE. Generic in the leaf content and the K slot; nothing names the Def syntax. The J tower instantiates the same frames with its own leaf content |
| `StepAtB`, the concrete instance at `DefBodyB` | PER-TOWER (Def). One instantiation at the delivered description |
| the row layer that the rework touches | PER-TOWER (Def), TEMPLATE SHAPE. The rows are Def syntax; the frame shape is generic. D-26's prediction holds: anything keyed on the Def syntax is per-tower |
| the row agreement and the adequacy | PER-TOWER (Def). They read the Def tower's built rows through Def-specific content |

The matrices instantiate rather than duplicate: one frame per matrix,
one certificate per matrix. Nothing in block 3 is copied per tower.

## 9. LITERATURE USED

`dev/literature/devlin-II5.md`, Step C (`:209-256`, summary
`:299-302`). Took the requirement: bind every quantifier of the Def
step by the concrete set K(u) inside the matrix.

The single-description question from `[LJ-1.37]`: yes, his
single-description shape is available here, and the twelve clauses are
a formalization artefact. The story's `satGraphB`
(`Condensation:2209-2220`) is one bounded graph formula containing the
twelve-row conjunction, exactly Devlin's single D(v, u) with the K(u)
bound. The twelve separate rows exist because the machine's
satisfaction recursion is a twelve-clause table. This block's finding
does not move that answer: the rows are the machine's table, and the
table's clauses are the formalization artefact, not the mathematics.

`dev/literature/devlin-errata.md`. NOT read. WHY NOT: `[LJ-1.14]`
verified it does not cover Chapter II section 5, and the brief rules
out re-checking it.

## 10. ARCHIVE USED

`src/L/Condensation.lagda.md`, whole, as delivered and after block 3.
Took the rows' slot layout, the frames at `:632-732`, the atom body at
`:940-957`, the quantifier bodies at `:993-1058` and `:1136-1147`, the
Exist row at `:1375-1381`, and the description at `:2234-2251`. The
row-by-row comparison in section 2 is the evidence for the refusal.

`_build/lj-1.37-report.md`, whole. Took the delivered figures: 2,031
lines at 0.0046 (`:105-108`), the atom-row quirk claim (`:12-18`,
`:243-249`), and the next-block list. The quirk claim is the premise
this report refutes; the cited lines do not contain the slot
definitions.

`_build/lj-1.34-review.md` and `src/ProbeDD25D5.agda`, whole. Took the
leg-D shape: the generic layer, the site facts as hypotheses, and the
0.0072 seconds per line figure. The story's matrices in block 3 are
the D5 shape with K a parameter.

`_build/lj-1.36-report.md` and `src/ProbeLJ136.agda`, whole. Took the
row extraction class (under 0.12 seconds total) and the finding that
eight rows have no public whole-row reader. That finding is why the
row semantics were never compared: the machine's rows are private, and
an outside reader never unfolds them.

`_build/lj-1.35-report.md` and `src/ProbeLJ135.agda`, whole. Took the
leaf layout (`v' ∷ c' ∷ x ∷ δ`, carrier at δ slot 1, bound at δ slot
4), the site-fact family, and the cone discipline.

`_build/lj-1.28-report.md`, whole. Took the leg-D definition: a
two-way decode between the bounded table's clause and the delivered
machine's clause at variable slots (`:34-36`), and the survey figures.

`src/L/Coding/Sequence.lagda.md`, whole. Took the delivered readings
`StepAt` (`:119-120`), `ApproxAt` (`:173-176`) and `LsetGraphAt`
(`:182-184`), and their layouts.

`src/L/Coding/Model.lagda.md`, whole. Took the atom row slots at
`:1746-1751`, the atom body at `:1753-1759`, the extAt-based row
relations at `:1590-1594`, `:1760-1762`, `:1960-1963`, and the frames
at `:897-1023`. This is the machine side of every row comparison.

`src/L/Coding/Graph.lagda.md`, whole. Took `twelveAt` at `:94-105` and
`satGraphAt` at `:104-112`.

`src/L/Coding/Powerset.lagda.md`, the coding sections. Took `DefBody`
at `:437-440` and `DefAt` at `:442-443`.

`archive/rud-route/src/L/Condensation.lagda.md`, whole, for SHAPE
only. Its target is classically false (`[LJ-1.11]`); no price was
taken from it.

`dev/LESSONS.md` is not archived and binds. P-l, P-m, P-n, P-t, P-u,
P-v, P-h, R-35, R-38, R-40, I-5, C-12, C-22, C-31, C-32, C-33, C-34
and D-10 were read through `scripts/rules.py --for build`. P-v
decided the machine's spelling throughout; the finding is that the
story's rows do not use it. C-34 is why the finding is a refusal with
the priced cure rather than a caveat.

## 11. WHAT I AM NOT SURE OF

1. The row-by-row comparison is by source inspection, not by a
   machine-checked decode. The evidence is the slot arithmetic, which
   a script verified. The decisive test, the row decode, is exactly
   the blocked work; it would settle each row definitively after the
   rework.
2. The empty-value vacuity (section 2, row 5) depends on the reading
   of the story's frames. I verified the frames end in
   `∀̇∈ (var (suc (suc zero))) body`, which is the vacuous universal.
   If the intended reading is different, that row of the table is
   wrong.
3. The machine's `b9″` claim is certain by direct inspection and by
   git history. The brief's cited lines `1765-1770` do not contain the
   slot definitions, which suggests the original finding cited a
   wrong range.
4. Block 1's `Clause` (`:54-204`) has the same one-directional shape
   as the Exist row. I did not change it; the report records it. Its
   agreement with the machine's existential row has the same problem.
5. Cold discipline: dependencies were warm through
   `_build/2.8.0/agda/src/`; only the master's own interface was cold
   per run. The third run (9.60) and the first (9.65) are the flat
   pair; the second (10.24) is the outlier, reported for honesty.
6. The block-3 marginal cost (about 0.3 to 0.6 seconds) rests on the
   LJ-1.37 residue of 9.06 seconds. D-10 applies: the residue was not
   re-measured in this session.

# LJ-1.236: A4 and A7, the gate list's last two, and A7 audits the rest

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.**

## GOAL

**`[LJ-1.227]` named five probes. Three have run.** A2 at 186 against 170
(`[LJ-1.229]`), A1 at 54 against 40 and A3 at 26 against 45 (`[LJ-1.232]`).
**Run the last two. One dispatch, two separate answers.**

**A7 FIRST, and this is a reversal of the obvious order.** `[LJ-1.136]` section
6.1 already ruled that the statement should be written second, straight after
A2, **as the consumer that AUDITS the rest**
(`agents/tasks/LJ-1-136/lj-1.136-report.md:381-392`). **A2 is now green. So A7
is due, and it gates whether A4, A5 and A6 are even the right objects.**

## PROBE ONE: A7, the internal GCH statement, standing 110 lines

**What it is.** The statement `L ⊨ GCH`, in the shape of the delivered
`ChoiceStatement` (`src/L/Choice/Transversal.lagda.md:372-384`, 13 in-fence
lines).

**No dissolution is possible: the statement IS the trophy.**

**The widest unmeasured term is the FORMULATION, not the lines.** **A7's 110
are mostly reading, because the statement must name the internal cardinal (A4)
and the square law (A5, A6) in exactly the shape those blocks deliver.** **If
the statement is formulated wrong, A5 and A6 cannot discharge it whatever their
line counts.**

**The probe, in two checks.**

1. **It elaborates**, and names only `S`, `∈ˢ`, internal `IsCardinal` and the
   square-law shape.
2. **A5's `sq` and A6's `absorbs` have CONCLUSIONS that match its
   HYPOTHESES.** **This is the audit and it is the point of running A7 now.**

**INFERRED cost: under 1 Agda minute.** It is a statement.

**D-10: the target is not false; the risk is that it is the WRONG
statement**, and this probe settles that before A4, A5 or A6 is funded.

## PROBE TWO: A4, internal least cardinal, standing 190 lines

**What it is.** The internal form of `LeastCard`: the least `δ` such that an
L-element codes an injection `⟪ κ ⟫ ↪ ⟪ δ ⟫`, plus internal `IsCardinal`.

**It is needed. MEASURED.** The ambient `IsCardinal` is delivered at
`src/L/BoundedSubset.lagda.md:1046-1047`, but it is the geometric form over the
ambient carrier. **The internal form is the object the GCH statement quantifies
over, they are different objects, and no delivered lemma converts them**
(`agents/tasks/LJ-1-136/lj-1.136-report.md:243-247`).

**THE WIDEST UNMEASURED TERM IS THE SECONDS, NOT THE LINES.** **The ambient
`LeastCardInj` is 44 lines and 100.64 s, which is 76 percent of the whole
chain's 133 s** (`agents/tasks/LJ-1-156/lj-1.156-report.md:208`, `:216`). **The
internal form adds a truncated L-element existential INSIDE the same least-of,
and `[LJ-1.136]` INFERRED the seconds RISE, not fall**
(`lj-1.136-report.md:454`).

**So: build internal `LeastCard`, instantiate at ONE real ordinal, and measure
COLD SECONDS under the cap. Report the rate against DD24's bar.**

**INFERRED cost: 2 to 4 Agda minutes.**

## THE DOUBLE-COUNT IS ALREADY CLOSED, so do not reopen it

**`[LJ-1.229]` MEASURED that A4 consumes A2's description plus adequacy, 27
lines, and NOT the readback.** **Take that. Do not re-derive it, and do not
count those 27 lines again in A4's figure.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1), PER PROBE

**A7:**

- **THE STATEMENT ELABORATES AND THE SHAPES MATCH.** Report its written lines
  against the standing 110. **Then the trophy has a target and A4, A5 and A6
  are funding the right objects.** STOP.
- **A SHAPE DOES NOT MATCH.** **NAME the mismatch: which block's conclusion
  fails which hypothesis** (C-36). **That is the most valuable outcome in this
  task, because it re-aims three blocks before any of them is built.**
- **THE STATEMENT CANNOT BE WRITTEN IN THE `ChoiceStatement` SHAPE.** Say why.

**A4:**

- **BUILT, AND HERE ARE THE COLD SECONDS.** Report seconds, lines, and the rate
  against DD24's bar. **Then A4 is measured and the route's seconds risk is
  priced.** STOP.
- **THE SECONDS RISE STEEPLY.** **`[LJ-1.136]` predicted a rise. Confirm or
  refute it with figures.** A steep rise is a real result and it re-prices the
  route.
- **A WALL.** The ambient term is already 100 s at 2.26 s per line.
  **A single `agda` invocation past 20 MINUTES is a wall**: interrupt, report
  the ELAPSED SECONDS, bisect. **Every cut gets the SAME bound as its green
  control, and the control's elapsed time is reported BEFORE any cut is
  interpreted** (`[LJ-1.215]`'s law).

**BOTH: do not merge the answers.** Two verdicts, two line counts, and for A4
the seconds.

## WHAT IS GREEN, so you extend rather than rebuild

- **`agents/tasks/LJ-1-229/ProbeLJ1229A.agda`**: A2's predicate `injAt` with
  both adequacy directions at its S1, plus the range set and `ranAt`. **A4
  needs S1.**
- **`agents/tasks/LJ-1-232/ProbeLJ1232A1.agda` and `ProbeLJ1232A3.agda`**: the
  L-carrier restatement and the canonical selection with `β` produced free.
- **`agents/tasks/LJ-1-234/ProbeLJ1234A.agda`**: the zero-arithmetic base at
  `ω`, which DISSOLVED A5's `pairω`. **A7 must match the shape A5 actually
  delivers, and that shape changed today.**

## WHAT YOU MUST NOT DO

- **Do not rebuild A2, A1 or A3.** All three are measured.
- **Do not price A5 or A6.** `[LJ-1.176]` measured A5 at 547 and `[LJ-1.217]`
  measured A6 at 446, and `pairω` DISSOLVED today.
- **Do not quote a total for Route A-prime.** Five reports refuse one.
- **Do not edit any master.** This is a probe. **Nothing lands in `src/`, and a
  probe under `src/` is forbidden by I-5.**
- **Do not touch `agents/tasks/LJ-1-235/`.** A sibling is live there.
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **A probe goes in `agents/tasks/LJ-1-236/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **A sibling
  holds the other Agda slot.** **Report the load beside every absolute figure**,
  discard a warm-up, and take at least three kept runs for any figure a decision
  rests on. **A4's whole deliverable is a seconds figure, so its load discipline
  is not optional.**
- **Report a heap exhaustion as a wall.** Never raise the cap. **`[LJ-1.234]`
  met one today and it was R-34's unpinned `InfinitySet` level meta. Check that
  before you call a heap wall yours.**
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## CITE THE REPORT THAT MEASURED, NEVER THE ONE THAT QUOTED

**C-44 entered `dev/LESSONS.md` today with my own session as its
measurement.** **If this brief asserts anything you cannot find, say so and
treat it as unproven.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.227]` MEASURED that A7 is TOWER-NEUTRAL: it is a statement, and it
names the structure and the internal cardinal exactly as `ChoiceStatement`
does.** **So write A7 with a STRUCTURE PARAMETER from its first line.** **A4 is
PER-TOWER, Devlin's second object applied to cardinality.**

**Say for each whether the parameter form cost anything.** `[LJ-1.210]`
measured that retrofitting one costs 42 lines on a 1,288-line module.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-227/lj-1.227-report.md`** sections 4, 5 and 8, read
  WHOLE. **Your two probes are specified there.**
- **`agents/tasks/LJ-1-136/lj-1.136-report.md:243-247`, `:381-392`, `:454`**:
  why A4 is needed, why A7 comes now, and the inferred seconds rise. **Read
  those lines, not a report about them.**
- `agents/tasks/LJ-1-156/lj-1.156-report.md:208`, `:216`: the ambient
  `LeastCardInj` at 44 lines and 100.64 s.
- `agents/tasks/LJ-1-229/lj-1.229-report.md`: A2 green, and the 27-line
  description plus adequacy that A4 consumes.
- **`src/L/Choice/Transversal.lagda.md:372-384` and
  `src/L/BoundedSubset.lagda.md:1046-1047`: read the delivered statement shape
  and the ambient `IsCardinal` at the source.**
- **`archive/dev/TASKS-archived.md` and `archive/src/2026-08-09-rud-route/`.**
  **The retired route reached a trophy and had to state it. Take SHAPE from the
  archive, never a claim**, and say what would NOT transfer.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Devlin states GCH in L and `dev/literature/devlin-II5.md` carries the
route.** **Say whether the delivered `ChoiceStatement` shape matches how the
literature states it**, and whether the internal cardinal is the object the
literature quantifies over. Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-227/lj-1.227-report.md` sections 4 and 5 FIRST.

## SCOPE (write)

`agents/tasks/LJ-1-236/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for build`.

- **D-1.** The abort criterion is fixed above, per probe.
- **D-10.** **A7's risk is the WRONG statement, not a false one. That is D-10's
  case exactly.**
- **DD8.** One estimate each, and each names its basis.
- **P-l.** 100.64 s and 44 lines are comparables and NOT A4's price.
- **C-33.** Name the OBLIGATION, never one delivered entry point.
- **C-36.** Write the term you could not write.
- **C-44.** A brief's claim that something was never done is unchecked until
  you check it.
- **C-42, C-38, C-39, C-40. I-5, R-34. P-i, P-k, P-m, P-t, P-y, R-40. C-12,
  C-22. DD0, DD24, D-26, D-29, D-30.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with A7's verdict FIRST, because it audits the rest: do the shapes
match?** Then A7's written lines against 110. Then A4's cold seconds with load
and run count, its lines against 190, and its rate against DD24's bar. Then any
shape mismatch named at `file:line`. Then whether the structure-parameter form
cost anything. **Mark every negative MEASURED or INFERRED.**

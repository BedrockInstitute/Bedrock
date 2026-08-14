# LJ-1.225: does the ported chain discharge `[LJ-1.7]`'s residue, or have we priced the wrong thing?

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**. **This task runs
NO Agda and holds no slot, so the model rule would give flash. I override it and
record why: the task READS Agda source and judges what a hypothesis needs, which
is the subject matter the `--agda` flag cannot see.** The clock selected the
mode.

## GOAL

**Six dispatches have now built, priced and censused the class-generic port.
NOT ONE has checked that it unblocks the thing phase 1 exists for.**

**`dev/PLAN.md:49` is the live status of `[LJ-1.7]`, and it names the
obstruction in four words: the ENVIRONMENT LIFT.**

> `levelIn` and `cover` are BUILT (`[LJ-1.178]`) and `theorem` does NOT derive.
> `AmbientRead` is SUPPLIED (`[LJ-1.184]`), closing one of four hypotheses.
> ... the obstruction is the ENVIRONMENT LIFT, not a missing `Δ₀` cure ... **the
> class-parameter generalization whose surface `[LJ-1.200]` measures at 17
> lines**.

**`[LJ-1.220]` has now TYPECHECKED that generalization at the ambient class,
exit 0.**

**So answer the question nobody asked: does the green ambient body SUPPLY the
environment lift `theorem` needs, or does it stop short of it?**

## WHY THIS RUNS NOW AND NOT AFTER THE PORT LANDS

**`[LJ-1.221]` measured my own worst pattern this week and it is category 2 of
`[LJ-1.211]`'s split, the largest at four of ten: a brief fixes a method that
cannot answer the question.** **Six dispatches walking a chain is a method. Not
one of them could have discovered that the chain is the wrong chain.**

**The port costs about 200 written lines by `[LJ-1.223]`'s reading. That is
cheap. It is not cheap if it discharges nothing.**

## THE THREE QUESTIONS

**1. WHAT ARE THE FOUR HYPOTHESES, and where does each stand?** `dev/PLAN.md:49`
says four, with `AmbientRead` SUPPLIED by `[LJ-1.184]`. **Name all four at
`file:line` in the delivered tree.** **Say which are BUILT, which are SUPPLIED,
and which are neither.** **A hypothesis is discharged when something SUPPLIES
it** (C-38 as extended), and BUILT is not SUPPLIED.

**2. DOES THE AMBIENT BODY SUPPLY THE ENVIRONMENT LIFT?** Read
`agents/tasks/LJ-1-220/Probe.agda`, which exits 0, and read what `theorem`
actually demands. **Answer in one word, YES or NO, and then at `file:line`.**

**3. IF NO, WHAT IS MISSING?** **Name the term.** **That name is worth more than
everything else in this report** (C-36: write the term you could not write).

## WHAT `[LJ-1.200]` MEASURED AND WHAT IT DID NOT

**`[LJ-1.200]` UPHELD `[LJ-1.196]`'s NO-GO and REFUTED its stated cause.** It
measured the class-parameter generalization's SURFACE at 17 lines. **A surface
is not a discharge.** **Check whether anything since has closed that gap, or
whether the 17 lines are still a surface with nothing behind them.**

**The tree already carries `Δ₀-extAtB`, `Δ₀-DefBodyB` and `abs₀`, spent for this
very ambient transfer.** **Find where each is spent and say whether the port
reaches them.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE PORT DISCHARGES IT.** Name the hypothesis, the supplier and the
  `file:line` on both sides. **Then landing the port is the phase's next move
  and I sequence it.** STOP.
- **THE PORT DISCHARGES PART OF IT.** Say which part and what remains. **Give
  the remaining term a name.**
- **THE PORT DISCHARGES NOTHING.** **This is a real and serious outcome and I
  want it if it is true.** Say what the port DOES buy, which is DD4 and the
  second tower, and say plainly that `[LJ-1.7]` is blocked on something else.
  **Then name that something else.**
- **THE RESIDUE IS NOT WHAT `dev/PLAN.md:49` SAYS.** If the record is stale or
  wrong, **say so with the evidence.** `dev/PLAN.md` is a live status screen and
  a stale row there costs more than a stale report.

## WHAT YOU MUST NOT DO

- **DO NOT RUN AGDA.** Two siblings hold both Agda slots (C-12).
- **Do not edit any master, brief or report.** **Write your own report and
  nothing else.**
- **Do not re-price the port.** `[LJ-1.223]` did that: 2 thin, 8 thick, 2,971
  shared delivered lines, about 200 plumbing, 0 per-tower residual in the chain.
  **Take those figures; do not re-derive them.**
- **Do not re-litigate `[LJ-1.196]` or `[LJ-1.200]`.** The verdict is upheld and
  the cause is refuted. **You are asking what the cure reaches.**
- **Do not touch `agents/tasks/LJ-1-217/` or `LJ-1-224/`.** Two siblings are
  live there.
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** **A hypothesis you read in a signature
is MEASURED. A judgement that a body would supply it is INFERRED until Agda
says so, and this task runs no Agda.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**DD4 and `[LJ-1.7]` are two different reasons to port, and only one of them is
measured.** `[LJ-1.223]` gives DD4 its best figure ever: about 200 plumbing
lines against 2,971 shared, and a per-tower residual of 0 in the chain. **That
figure stands whatever you find.** **Say plainly whether the port is worth
landing on DD4 alone, if the answer to question 2 is NO.** **A refactor that
serves both towers and unblocks nothing is still a DD4 result, and calling it
one honestly is better than pretending it is a cure.**

## ARCHIVE (DD18)

- **`dev/PLAN.md:36-70`**, the live status screen, read WHOLE. **It is your
  brief within this brief.**
- **`agents/tasks/LJ-1-200/LJ-1.200-report.md`**: the upheld verdict, the
  refuted cause, and the 17-line surface.
- `agents/tasks/LJ-1-196/`: the NO-GO and the chapter claim.
- `agents/tasks/LJ-1-178/` and `LJ-1-184/`: `levelIn` and `cover` BUILT, and
  `AmbientRead` SUPPLIED. **Read what SUPPLIED meant there; it is your
  template.**
- `agents/tasks/LJ-1-220/lj-1.220-report.md` and **`Probe.agda`, read WHOLE**:
  the green ambient body.
- `agents/tasks/LJ-1-223/lj-1.223-report.md`: the price. **Take it.**
- **`src/L/Condensation.lagda.md` and `src/L/BoundedSubset.lagda.md:917`,
  `:1555`: where `levelIn` and `cover` are hypotheses. Read the source, never a
  report about it.**
- **`archive/dev/TASKS-archived.md` and `archive/dev/JOURNAL-archived.md`.**
  **The retired route reached a trophy and its records may name this same
  lift. Take SHAPE from the archive, never a claim.**

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md:387-389` says the per-tower content is exactly
two objects, the level-hood certificate and the definable well-order.**
**`[LJ-1.223]` measured that both live ABOVE the coding chain, not inside it.**
**Say whether `[LJ-1.7]`'s residue is one of those two objects.** **If it is,
the port was never going to reach it and Devlin said so.** Return a
**LITERATURE USED** section.

## SCOPE (read)

`dev/PLAN.md:36-70` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-225/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for recon` and read every statement.

- **D-10.** Price the truth of a recorded residue before pricing its proof.
  **This task IS D-10 applied to a whole phase.**
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
- **C-36.** Write the term you could not write.
- **C-22.** Write the deliverable incrementally.
- **C-42.** A refutation measures the site it names, never its extent.
- **P-l.** A cure measured at one site is a hypothesis at another.
- **D-26.** A well-founded key on a tower needs generation data, or syntax.
- **C-32, C-39, C-40. DD0, DD2, DD4, DD8, DD24. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `.venv/bin/python scripts/lint-prose.py --check` on your report.
- **No em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with one word on question 2: does the ported chain supply the environment
lift, YES or NO.** Then the four hypotheses, each with its state and its
`file:line`. Then, if NO, the name of the missing term. Then whether the residue
is one of Devlin's two per-tower objects. Then your one-paragraph judgement on
whether the port is worth landing on DD4 alone. **Mark every negative MEASURED
or INFERRED.**

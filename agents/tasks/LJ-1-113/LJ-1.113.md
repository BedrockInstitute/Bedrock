# LJ-1.113: who supplies the twenty nine?

tier: codex (default)

## GOAL

**Measure the distance from instantiable to proved.** The composer
instantiates with nothing unsupplied, but 29 of its facts come from
hypotheses the consumer STATES. **Find out which of them the delivered
machinery can actually prove.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`75fa586`. `make check` passes.** A sibling agent works on the cardinal side
and will not touch `src/L/Condensation*`.

## WHAT IS MEASURED

`[LJ-1.112]`: **zero unsolved metas.** 39 became 11 became 0. I re-ran it:
exit 0, and `consume-out = F.out` (`src/ProbeLJ1112A.agda:437-439`) forces
the composer's body to elaborate, not only its telescope.

**The 59 frame facts come from three places:** 28 from the `KFacts` record,
2 from the consumer's site facts, and **29 from the extended consumer
frame** (`src/ProbeLJ1112A.agda`, modules `Extended` and the `sucK` at
`:317-319`).

**Those 29 are NEW HYPOTHESES, not discharges.** C-38. The obligation moved
from a frame nobody could hold to a frame the consumer can state. **That is
real and it is not a proof.**

## WHAT TO DO

1. **List the 29 from the source**, at `file:line`, with their types.
   `[LJ-1.100]` section 2 tabulated 28 of them and `[LJ-1.112]` added
   `sucK`. **Verify against `src/ProbeLJ1112A.agda`; do not copy the old
   table.**
2. **For each, answer ONE question: can the delivered machinery prove it?**
   Classify each as
   - **PROVABLE**, with the delivered lemma at `file:line` that does it;
   - **NEEDS NEW CONTENT**, with a one-line statement of what;
   - **UNKNOWN**, and say what you would have to read to decide.
   **The classification is by reading. Do not build twenty nine proofs.**
3. **Then machine-check at least THREE**, chosen for decisiveness rather
   than ease: **pick the ones whose failure would most change the plan.**
   Report each term at `file:line` with its seconds.
4. **Price the rest.** One best-effort figure with its basis named, plus the
   widest unmeasured term and the probe that would measure it. DD8.

**Most of these facts are about the coding machinery under
`src/L/Coding/`, which you may READ but never edit.** The `envK-*`,
`envInK-*`, `valV`, `valW`, `wKfact`, `subK-*` and `consK-*` families all
conclude a membership in `K` from a satisfaction of a machine formula, so
`src/L/Coding/Model.lagda.md` is where their proofs would live or fail.

## THE RULE ON HYPOTHESES, stated as a test and not as a shape

**Do not add a fact to make a proof go through. Name what supplies each at
`file:line`, or say NEEDS NEW CONTENT.**

**Run `scripts/check-unbound-hyp.py` on anything you write** and report what
it says. Rule 3 catches a premise-free telescope, rule 1 an unconstrained
conclusion subject, rule 2 an unconstrained premise object.

## THE ABORT CRITERION

- **The classification is complete and three are machine-checked**: report
  and STOP.
- **A fact turns out to be REFUTABLE**: STOP and report it. **Seven were
  this phase, and each was found only when somebody attacked it.**
- **A fact needs content the tree cannot have**: report it and CONTINUE.
  **Say how many are in that class, not just the first.**
- **Anything walls**: STOP, report the wall with its seconds.

**Do not stop at the first negative.**

**Work in `src/ProbeLJ1113*.agda`. Do not touch any master.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. If a
check does not return, KILL IT before you start another, and report the wall
with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not weaken any of the 29.** They are the consumer's statements and
  the composer consumes them as they stand.
- **Do not edit anything under `src/L/Coding/` or `src/V/`.** Read only.
- **Do not touch any master.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers and types from the source, never from a report.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.** **A reading-based classification is INFERRED, and that is fine
here as long as you say so: only the three you machine-check are MEASURED.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**Say which of the 29 are about the CODING machinery and which are about the
tower.** The coding half is shared by construction; the tower half is not.
**That split is the DD4 answer and it is what decides how much of this the J
tower repeats.**

## ARCHIVE (DD18)

- **`_build/lj-1.112-report.md`**, read WHOLE, and **`src/ProbeLJ1112A.agda`**,
  read WHOLE. **The 29 and the instantiation that consumes them.**
- `_build/lj-1.100-report.md` section 2, the earlier table of 28.
- `_build/lj-1.109-report.md` section 2, `sucK`'s named inhabitant and P-x.
- `src/L/Coding/Model.lagda.md`, the environment and value machinery.
  **READ ONLY.**
- `src/L/Condensation.lagda.md`, the `KFacts` record and the consumer.
- `dev/LESSONS.md` **C-38 as extended, C-39, C-40, P-x**, C-35, C-36, D-8,
  D-30, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Say in two lines what Devlin assumes about the coding at 5.5**, from
`dev/literature/devlin-II5.md`. Spend little.

## SCOPE (read)

`src/ProbeLJ1112A.agda` FIRST, then `src/L/Coding/Model.lagda.md`, then
`src/L/Condensation.lagda.md`'s consumer telescope.

## SCOPE (write)

`src/ProbeLJ1113*.agda` only. Your report is `_build/lj-1.113-report.md`.
**No master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for recon`, and read every
statement.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it. **This dispatch measures how far that is.**
- **C-39.** A brief's prohibition binds harder than its goal. **If a line of
  this brief blocks a route you can see, say so in the report and name the
  route. That is a required section, not a courtesy.**
- **C-40.** Verify the CONSUMERS of a changed master, never the master
  alone.
- **C-35, C-36, D-8, D-30, D-10.**
- **P-l.** A price from a comparable elsewhere is a hypothesis.
- **P-x, P-i, P-w, P-h, P-k, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as the
  bundle gives them.
- **P-c, R-36, R-38, R-35, R-40.**
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally. **Write each row of the
  classification as it lands.**
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-26, D-29.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- **Run `scripts/check-unbound-hyp.py` on your probe** and report what it
  says.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.113-report.md` incrementally, skeleton first.

**Lead with the three counts: PROVABLE, NEEDS NEW CONTENT, UNKNOWN.** Then
the full table, one row per fact, with its `file:line` and its verdict. Then
the three you machine-checked, with terms and seconds. Then the price for
the rest with its basis, and the widest unmeasured term. Then the C-39
section. **Mark every negative MEASURED or INFERRED.** Then the DD4 split:
coding machinery against tower.

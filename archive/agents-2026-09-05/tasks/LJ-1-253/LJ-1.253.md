# LJ-1.253: close A-prime's last two reading residues and make 1,150 a price

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**. **This task runs
NO Agda and holds no slot, so the model rule would give flash. I override it and
record why: the task READS Agda probes and delivered masters and judges what a
master would owe over a probe, which the `--agda` flag cannot see.** The clock
selected the mode.

## GOAL

**`[LJ-1.248]` summed Route A-prime to 1,150 and called it ARITHMETIC, not a
price, and it named THREE causes rather than guessing one. Two are still
open.**

| cause | size | state |
|---|---:|---|
| A4's 43 is a MINIMAL CORE; the master owes the full object-language internal `IsCardinal` with adequacy | **about 30, INFERRED** | **yours** |
| A6's 150 base still carries reading in its theorem wrapper | **47, MEASURED as reading** (`agents/tasks/LJ-1-217/lj-1.217-report.md:160`) | **yours** |
| A7 double-counts lines A2 and A4 already count | about 14 | **`[LJ-1.248]` closed it: corrected A7 about 33** |

**Close the two. Then A-prime's total is a PRICE for the first time, and the
route's last reading residue is gone.**

## WHY THIS IS SMALL AND WHY IT MATTERS

**47 of 1,150 is 4 percent.** **This morning the reading residue was 555.**

**A price and an arithmetic sum look identical in a table.** Six reports
refused a total for exactly this reason, and `[LJ-1.248]` was the first able to
say what was missing rather than that something was.

## THE TWO QUESTIONS

**1. WHAT DOES A4's MASTER OWE OVER ITS PROBE?** `[LJ-1.236]` measured the core
at 43 and said the master adds「the full object-language internal `IsCardinal`
formula with its adequacy, and the concrete nonempty witness (A2's `lid`, which
is A5's deliverable, not A4's)」. **Price that.** **`[LJ-1.229]` measured a
comparable: A2's `injAt` plus both adequacy directions is 27 lines.** **P-l: a
comparable and NOT a price.**

**2. WHAT IS IN A6's 47?** `[LJ-1.217]` records A6's base as 150, of which 103
is MEASURED by `[LJ-1.107]` and **47 is reading, being the theorem wrapper**.
**Open it and say what those 47 lines are.** **If they are a wrapper around
measured content, they may be cheaper than 47; if they hide a build, they may
be dearer.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **BOTH CLOSE.** Give A-prime's total as a PRICE with its basis. STOP. **That
  is the first price this route has ever had.**
- **ONE CLOSES.** Say which, and what the other still needs.
- **A GAP IS BIGGER THAN ITS FIGURE.** **Say so with both numbers.** **A4's 30
  is INFERRED by `[LJ-1.248]` and nobody has opened the master's requirement.**
- **A GAP DISSOLVES.** **If A4's master does not owe what `[LJ-1.236]` thought,
  or if A6's wrapper is already measured somewhere, say so.** **Five items have
  dissolved this month.**
- **NEITHER CAN BE PRICED BY READING.** **Say what probe each needs** (DD8).
  **Naming two probes is a complete answer and it beats a guessed figure.**

## WHAT YOU MUST NOT DO

- **DO NOT RUN AGDA.** A sibling holds a slot.
- **Do not re-measure any block.** All seven are measured.
- **Do not touch `[LJ-1.7]`'s residue.** Priced at about 400 and gated at
  `[LJ-1.252]`, which is live.
- **Do not touch `agents/tasks/LJ-1-252/`.**
- **Do not edit any master, brief or report.** **Write your own report and
  nothing else.** **I write the status screen.**
- **Create your report file in your FIRST five minutes (C-22).**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## SIX RULES THIS CHAIN EARNED

**SEARCH THE OPEN-WORK LIST BY CONTENT, NOT BY NAME.** Ten dispatches
re-derived a price `dev/PLAN.md` section 0.0 already carried. **Before you
price anything here, grep that section and `dev/ledger.toml` for the object by
its content.**

**THE ARCHIVE BEARS UNTIL YOU OPEN IT.**

**`exit 0` IS NOT A SUPPLY** (C-45). **A probe's figure is not a master's
figure, and that is question 1 exactly.**

**CARRY A CLAIM'S QUALIFIER OR CARRY NEITHER.**

**A FAILED SUBSTITUTION IS NOT A PROOF OF IMPOSSIBILITY** (C-36).

**C-44: if THIS brief states anything you cannot find, say so and treat it as
unproven.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** **A figure read in a report is
MEASURED by that report. A master's requirement judged from a probe is
INFERRED.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.251]` corrected `[LJ-1.248]`'s per-tower half from a figure to a BAND:
146 to 196, because the partition is a survey marked MEASURED and it excludes
A5.** **Narrow that band if your two answers touch it.** **A4 contributes 22
per-tower lines by `[LJ-1.236]`, so A4's master gap may add more.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-248/lj-1.248-report.md`**, read WHOLE, especially its
  sections 2 and 3.
- **`agents/tasks/LJ-1-236/lj-1.236-report.md`** section 4: what A4's core
  excludes and why.
- **`agents/tasks/LJ-1-217/lj-1.217-report.md:156-162`**: A6's 150 base split
  into 103 measured and 47 reading.
- `agents/tasks/LJ-1-107/`: the 103 that IS measured.
- `agents/tasks/LJ-1-229/lj-1.229-report.md`: A2's 27-line comparable.
- **`archive/dev/TASKS-archived.md`.** **The retired route reached a trophy and
  had a total. Say what its total counted.** Take SHAPE, never a claim.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**Say in one line whether the literature bounds either gap.** Return a
**LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-248/lj-1.248-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-253/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for recon` and read every statement.

- **DD8.** One estimate, and it names its basis. **If you cannot price a gap,
  name its probe.**
- **D-10.** Price the truth of a recorded residue before pricing its proof.
- **P-l.** A comparable is not a price. **A2's 27 is a comparable for A4's
  gap.**
- **D-26.** A well-founded key on a tower needs generation data, or syntax.
- **C-44, C-45, C-36, C-42, C-38, C-32, C-39, C-40. C-22. I-5. DD0, DD18,
  DD24.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `.venv/bin/python scripts/lint-prose.py --check` on your report.
- **No em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with A-prime's total and ONE word: PRICE or ARITHMETIC.** Then A4's
master gap, priced or with its probe named. Then what A6's 47 lines actually
are. Then the per-tower band, narrowed if you can. **Mark every negative
MEASURED or INFERRED.**

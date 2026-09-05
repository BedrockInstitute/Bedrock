# LJ-1.351: measure `graphWitK`, where only 1 of 5 premise conjuncts is inhabited

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## THE RULING THAT FUNDS THIS

**`[LJ-1.349]`, the adversarial review, ruled it in these words:**

> `graphWitK`'s INFERRED verdict **must be measured before it is believed.** The
> inference is honestly marked, but **only ONE of five premise conjuncts was
> inhabited**; `domAt`, `appAt` and `twelveAt` at the proposed `d` are untested,
> and **premise inhabitation is this chain's pivot every time.** The
> about-120-line price has a legal basis; **the row must read INFERRED until the
> countermodel is green with its premise term.**

**So: inhabit the premise, or fail to and say why.**

## WHY THE PIVOT IS ALWAYS THE PREMISE

**Three refutations on this chain each turned on it, and every one was
strengthened by a term rather than an argument:**

- `[LJ-1.341]` inhabited both premises at the refutation's own witnesses.
- `[LJ-1.345]` rebuilt the countermodel itself rather than take a transcription.
- `[LJ-1.349]` went further and showed the countermodel lives INSIDE the
  chapter's intended premise class, **closing the last escape by a term.**

**A refutation whose premise is empty refutes nothing.** **That is the whole
risk here, and it is why the review refused to let the verdict stand.**

## WHAT IS ALREADY KNOWN

**`[LJ-1.348]` measured:**

- `graphWitK` concludes a **TRIPLE** at `src/L/Condensation.lagda.md:7295-7297`;
- **the missing field EXISTS at another sort** and closes only the **THIRD**
  conclusion, in **2 lines**, from `src/L/Axioms/Basic.lagda.md:156-158` carried
  by `Lset-in` at `src/L/Constructible.lagda.md:319`;
- `d` and `e` carry `witK`'s defect, and **`d`'s premise is `closedAt` with NO
  shapedness at all**;
- the rest is priced at about **120 lines**, unbuilt.

**And `[LJ-1.350]` just measured something that may change the whole reading:**
**shapedness is NOT the bound anywhere in this family. `arityNumAtL` at
`src/L/Coding/CodeSet.lagda.md:185-188` is, with both adequacy directions
delivered.** **Check whether it closes `d` and `e` too.** **That is the cheapest
possible outcome and it has now been the answer twice.**

## THE ABORT CRITERION (D-1)

- **THE PREMISE IS INHABITED AND THE CONCLUSION REFUTED.** **Then `graphWitK` is
  MEASURED FALSE and the row changes.** Report the term. STOP.
- **`arityNumAtL` CLOSES IT.** **Then it is TRUE and supplied, and the 120 lines
  evaporate.** **`[LJ-1.350]` found exactly this at a sibling tie, and the tree
  had written the answer in English.**
- **THE PREMISE CANNOT BE INHABITED.** **Then the tie is VACUOUS rather than
  false, which is a different verdict with a different repair.** **`[LJ-1.341]`
  drew that distinction explicitly; hold it.**
- **A WALL.** **C-58: replace a numeral pattern-match split with the library
  eliminator before bisecting the mathematics.** `[LJ-1.350]` never walled
  because it imported the eliminator form from the start.

## CONSTRAINTS

- **LAND NOTHING. This is a probe.** Write only in `agents/tasks/LJ-1-351/`.
  **`src/` is forbidden** (I-5).
- **`agents/tasks/LJ-1-344/Supply344.agda` is RED and EXPECTED**, and
  `agents/tasks/LJ-1-350/MustFail350.agda` is **EXPECTED RED**. **Repair
  neither.**
- **Chapter line numbers have DRIFTED 109 lines.** Re-derive every citation you
  rely on (C-44).
- **The public pair access is `ChainZ` in the chapter itself**; three tasks have
  now measured that. **Do not re-write those four lines a seventh time.**
- **COUNT THE AGDA SLOTS** before every invocation, exactly:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **Both obvious alternatives OVER-COUNT, MEASURED.** A sibling is live.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the empty-file floor beside any seconds figure** (C-53 as extended).
- **RUN A NEGATIVE CONTROL that MEASURES, and include NON-VACUITY**, which is the
  point of the task. **`[LJ-1.350]`'s standard: the conjunct HOLDS at one
  argument and FAILS at another, one argument apart in one file.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-351/lj-1.351-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check`. **No em dash.**
- Evidence is `file:line`. ASD-STE100. Mark every negative **MEASURED** or
  **INFERRED**, in those words.

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Ten of my last twenty-three briefs carried a claim an agent measured FALSE.**
**The one at risk: 「`arityNumAtL` may close `d` and `e` too」.** **That is my
extrapolation from `[LJ-1.350]`'s site to yours, and P-l says a judgement at one
site is a hypothesis at another.** **`[LJ-1.350]` itself confirmed a sibling's
reading at a different tag, a different frame and a different tie before
believing it. Do the same.**

## THE RULES

**C-45** is the law of this chain, and **premise inhabitation is its sharpest
form**. **D-10, C-42, C-44, C-53, C-57, C-58, C-36, P-l.**
**C-12, C-22, C-32, C-39, C-40.** I-5. **D-1, D-26.**
**DD0, DD4, DD8, DD18, DD23, DD24.**

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **NAME YOUR AXIS** (C-46), fixed at
`scripts/measure/ledger.py:50`. **Every term on this chain has been class-free;
say whether yours is.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-349/lj-1.349-report.md`, read WHOLE.** The ruling that
  funds you, and its non-vacuity standard is the one you must meet.
- **`agents/tasks/LJ-1-348/lj-1.348-report.md`**, which priced your tie and
  found the field at another sort.
- **`agents/tasks/LJ-1-350/lj-1.350-report.md`**, which found the real bound in
  this family and measured that shapedness is not it.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md`.** **Say in one line whether a tie concluding a
triple has any counterpart in his text.** Return a **LITERATURE USED** section.

## SCOPE (read)

`src/L/Coding/CodeSet.lagda.md:185-207` FIRST: it is the bound that closed a
sibling tie and it may close yours.

## SCOPE (write)

`agents/tasks/LJ-1-351/` only.

## RETURN

**Lead with ONE word: FALSE, TRUE, VACUOUS or STILL-INFERRED.** Then the premise,
inhabited or not, as a TERM. Then whether the delivered bound closes `d` and `e`.
Then what the 120 becomes. Then your negative control including non-vacuity.
**Mark every negative MEASURED or INFERRED.**

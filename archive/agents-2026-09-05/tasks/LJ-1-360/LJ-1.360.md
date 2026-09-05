# LJ-1.360: price the `hasWitnessAt` restatement, the last unpriced term on this chain

tier: pi (pi-subagent-mode), model `glm-5.3`. **I ran
`scripts/dispatch/dispatch_policy.py` before writing this line and took the
head it gave.** Agda. **This is a PROBE. Land nothing.**

## WHY, and this is the term the whole chain now rests on

**`[LJ-1.350]` priced the 28 repaired telescopes at about 43 insertions,
7 of the 8 per site being shared.** **Then it said in its own words:**

> **What the 43 buys is the cost of stating the repaired telescopes, ONCE THE
> WITNESS STEP SUPPLIES THE BOUND. The witness step is `hasWitnessAt` in
> `src/L/Coding/CodeSet.lagda.md`, and this task did NOT price its
> restatement.**

**So 43 is a FLOOR with an unpriced term under it.** **DD8 says a build brief
must name its widest unmeasured term and the probe that measures it. This is
that probe.** **Until it runs, nobody can fund the repair.**

## THE TWO CANDIDATES, from `[LJ-1.348]` section 6, and they are NOT equal

**1. THE HONEST RESTATEMENT, which is Devlin's own.** **The witness is not any
set carrying the body; it IS the bounded set.** That changes `hasWitnessAt`
itself, or the step that consumes it. **UNPRICED. This is your target.**

**2. THE CHEAP RESTATEMENT**, adding `⟨ fst w ∈ fst (lookup A γ) ⟩`. **It
TYPECHECKS** (`agents/tasks/LJ-1-348/Refute348.agda:338-346`) **and it has NO
SUPPLIER at `:6721`** (`agents/tasks/LJ-1-348/MustFail348.agda`, EXPECTED RED,
exit 42). **`[LJ-1.348]` warned: a brief that orders it gets a second
unsuppliable tie one level up.** **Do not price it as a cure. Price it only as
the control that shows why candidate 1 is needed.**

## WHAT IS ALREADY SETTLED, and re-opening any of it wastes your budget

- **`witK` is FALSE**, `[LJ-1.348]` section 2, `Refute348.agda:247-252`.
  **A repair that threads a hypothesis out of a false parameter buys nothing.**
- **Shapedness is NOT the bound anywhere in this family**, `[LJ-1.350]`,
  `Refute350.agda`, exit 0 in 2.56 s.
- **The real bound is `arityNumAtL`**, `src/L/Coding/CodeSet.lagda.md:185-188`,
  with `arityNumAtL-out` at `:189-197` and `arityNumAtL-in` at `:201-207`,
  **both directions delivered.** `Cure350.agda` supplies a tie's last conjunct
  from it in **7 lines**, exit 0 in 2.90 s.
- **Four of six construction ties are MEASURED FALSE**, each with a DD25
  review that UPHELD it.
- **The downstream count is 2 producers and 6 consumers in EACH of
  `LowerAgree.lagda.md` and `UpperAgree.lagda.md`**, `[LJ-1.350]` section 5.3,
  swept and read rather than extrapolated.

## THE QUESTION, in three parts

**1. WHAT DOES `hasWitnessAt` SAY TODAY, and what would Devlin's form say?**
Read it in `src/L/Coding/CodeSet.lagda.md` and state both, as types.
**Re-derive the line numbers** (C-44): the chapter has drifted before.

**2. WHAT DOES THE RESTATEMENT COST, in lines and in consumers?** **Every
consumer of `hasWitnessAt` must be swept and read, not extrapolated**, to
`[LJ-1.350]`'s standard. **Say how many consumers change and how many do
not.** **A restatement whose consumer diff is EMPTY is the best possible
outcome and it has happened twice on this chain** (`[LJ-1.337]`'s `sq-below`,
`[LJ-1.342]`'s generic mu).

**3. DOES IT ACTUALLY SUPPLY THE BOUND?** **This is the whole point and it is
where a miniature settles the question.** **Build the smallest term that takes
the restated `hasWitnessAt` and produces the conjunct the 28 telescopes need.**
**If it does not, the 43 is not a floor, it is a wrong number.**

## THE ABORT CRITERION (D-1)

- **CHEAP AND IT SUPPLIES.** Give lines, consumers, and the miniature.
  **Then the 43 becomes a real price and the repair can be funded.** Best.
- **EXPENSIVE.** **Price it and name what dominates.** **A large number here
  is valuable: it may mean the 28-site repair is not worth funding at all, and
  that is a route-level answer.**
- **IT DOES NOT SUPPLY.** **Then `[LJ-1.350]`'s 43 rests on a false premise.**
  **Say so with the term that fails. That is the most valuable outcome.**
- **A WALL.** **C-58: replace a numeral pattern-match split with the library
  eliminator before bisecting the mathematics.** **`[LJ-1.350]` never walled
  because it imported the eliminator form from the start. Do the same.**

## CONSTRAINTS

- **LAND NOTHING. `src/` is forbidden** (I-5). Write only in
  `agents/tasks/LJ-1-360/`.
- **DD23: the chapter's mathematical prose is the orchestrator's.** **You price
  a restatement; you do not choose it.**
- **`agents/tasks/LJ-1-344/Supply344.agda`, `LJ-1-350/MustFail350.agda` and
  `LJ-1-348/MustFail348.agda` are EXPECTED RED. Repair none of them.**
- **Do not edit another task's directory.** You may READ and COPY from
  `LJ-1-348/` and `LJ-1-350/`; both hold green miniatures you should reuse
  rather than rebuild.
- **`[LJ-1.358]` is live and writes only in `agents/tasks/LJ-1-358/`.** It
  holds no Agda slot.
- **COUNT THE AGDA SLOTS** before every invocation, exactly:
  `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`. **Both obvious
  alternatives OVER-COUNT, MEASURED.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the empty-file floor beside any seconds figure** (C-53 as extended).
- **RUN A NEGATIVE CONTROL that MEASURES, and include NON-VACUITY.**
  **`[LJ-1.350]`'s standard: the conjunct HOLDS at one argument and FAILS at
  another, one argument apart in one file.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-360/lj-1.360-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `lint-agda.py --check`. **No em dash.** Evidence is `file:line`. ASD-STE100.
  Mark every negative **MEASURED** or **INFERRED**.

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Eleven of my last twenty-nine briefs carried a claim an agent measured
FALSE, and `[LJ-1.359]` found two stale citations in the brief I wrote an hour
ago.** **The one at risk here: 「the restatement is what supplies the bound」.**
**That is `[LJ-1.350]`'s sentence, not a measurement, and `[LJ-1.350]` says so
itself: it did NOT price this.** **If the bound comes from somewhere else, or
from nowhere, say so and the chain changes shape.** **Re-derive every line
number I have quoted; two of my last three briefs quoted a stale one.**

## THE RULES

**C-45: `exit 0` is not a supply, and premise inhabitation is its sharpest
form on this chain.** **C-57: the search that finds it and the reading that
discards it are two different failures; twice on this chain the answer was
written in English in a delivered chapter.** **D-10, C-42, C-44, C-53, C-55,
C-58, P-l, P-k.** **C-12, C-22, C-32, C-36, C-39, C-40.** I-5. **D-1, D-26.**
**DD0, DD4, DD8, DD18, DD23, DD24, DD25.**

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker. **NAME YOUR AXIS** (C-46), fixed at
`scripts/measure/ledger.py:50`.

**Every term on this chain has been class-free so far; say whether yours is.**
**`hasWitnessAt` sits in the coding substrate, which both towers read**, so a
restatement there is either a DD4 win or a DD4 cost depending entirely on
whether it stays generic. **Say which, with the import list rather than with
an opinion.**

## ARCHIVE (DD18)

**A live `agents/tasks/` path is NOT an archive citation, MEASURED by
`[LJ-1.357]` today** (`scripts/gate/check-archive-cited.py:26-27`). **The four
corpora are the archives. Cite archived CODE, not only records.**

- **`archive/src/2026-08-09-rud-route/`**: **grep it for a witness or
  boundedness predicate and say what the retired route did here.** **It ran a
  different coding scheme, so the answer may be「nothing transfers」; that is a
  fine answer and it must be MEASURED, not assumed.**
- **`archive/dev/JOURNAL-archived.md`**: **search for the retired route's own
  witness step.** WHY NOT if nothing bears.
- **`archive/dev/DECISIONS-archived.md`**: any ruling on the coding
  substrate's shape. WHY NOT if none.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim.

**Return an ARCHIVE USED section naming ONE line read per archived file, with
WHY NOT for anything you decline.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md`.** **Candidate 1 is called「Devlin's own」by
`[LJ-1.348]`. VERIFY THAT AGAINST THE DIGEST**: does Devlin state the witness
as the bounded set itself? **If the digest does not say so, the name is wrong
and the candidate needs a different justification.** Return a **LITERATURE
USED** section.

## SCOPE (read)

`src/L/Coding/CodeSet.lagda.md`, the `hasWitnessAt` block WHOLE, FIRST. Then
`agents/tasks/LJ-1-350/Cure350.agda`, which is the shape of a supply that
worked.

## SCOPE (write)

`agents/tasks/LJ-1-360/` only.

## RETURN

**Lead with ONE line: does the restated `hasWitnessAt` supply the bound, and
at what price.** Then both candidates as types. Then the consumer sweep, read
and not extrapolated. Then your miniature. Then whether the 43 survives. Then
your negative control including non-vacuity. **Mark every negative MEASURED or
INFERRED.**

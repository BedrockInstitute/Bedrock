# LJ-1.379: measure the BACK direction at the chain, `[LJ-1.360]`'s last unmeasured term

tier: pi (pi-subagent-mode), model `glm-5.3`. **I ran
`scripts/dispatch/dispatch_policy.py` before writing this line and took the
head it gave.** Agda. **PROBE. Land nothing.**

## WHAT FUNDS THIS

**`[LJ-1.360]` priced the `hasWitnessAt` restatement and it SUPPLIES**, at 8
insertions at the coding substrate, 2 edited lines at the chain's `out`, and
about 3 at the bounded mirror. **`[LJ-1.350]`'s 43 survives as the telescope
share of a repair totalling about 54 to 56.**

**Its own words on what is left:**

> **ONE unmeasured term left under it: the BACK direction at the chain, whose
> closest candidate the bounded form offers was REFUSED**,
> `agents/tasks/LJ-1-360/MustFail360.agda`, **EXPECTED RED, exit 42.**

**So the 54 to 56 is a FLOOR with exactly one term under it, and that term has
a failed candidate rather than no candidate.** **That is the cheapest possible
probe shape: the failure is already in the tree with its type.**

**Read `agents/tasks/LJ-1-360/lj-1.360-report.md` section 4.3 FIRST**, and
`MustFail360.agda` whole. **RE-RUN both, they are hours old** (C-44).

## THE QUESTION

**1. WHY does the bounded form's candidate fail?** **Report Agda's own type,
not a paraphrase.** **`[LJ-1.360]` marked it EXPECTED RED, which means it
predicted the failure; say whether the failure is the one it predicted.**

**2. IS THERE ANOTHER CANDIDATE?** **`[LJ-1.350]` measured that the real bound
in this family is `arityNumAtL`, `src/L/Coding/CodeSet.lagda.md:185-188`, with
BOTH adequacy directions delivered at `:189-197` and `:201-207`.** **The BACK
direction is exactly where a two-directional adequacy should pay. Check
whether it does.**

**3. WHAT DOES THE 54 TO 56 BECOME?** **A number with its last term measured
is a price; without it, it is a floor.** **Give the price, or say what still
blocks it.**

## THE ABORT CRITERION (D-1)

- **IT IS SUPPLIED.** **Then the whole `hasWitnessAt` repair is priced end to
  end and the 28-site chain can be funded.** Report the term. STOP.
- **IT IS NOT.** **Name what is missing at `file:line`.** **If the BACK
  direction needs something the tree does not deliver, that is a route-level
  finding and it may mean the repair is not worth funding at all.**
- **THE REPAIR IS NOT WORTH IT.** **`[LJ-1.348]` measured `witK` itself FALSE
  and warned that threading a hypothesis out of a false parameter buys
  nothing. If that objection reaches here too, say so and stop.**
- **A WALL.** **C-58: replace a numeral pattern-match split with the library
  eliminator before bisecting the mathematics.**

## CONSTRAINTS

- **LAND NOTHING. `src/` is forbidden** (I-5). Write only in
  `agents/tasks/LJ-1-379/`.
- **You may READ and COPY from `LJ-1-348/`, `LJ-1-350/` and `LJ-1-360/`. Edit
  none of them.** **Their `MustFail*.agda` files are EXPECTED RED; repair
  none.**
- **`[LJ-1.377]` and `[LJ-1.378]` are live.** `[LJ-1.378]` holds one Agda
  slot. **COUNT THE SLOTS** before every invocation, exactly:
  `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`. **Both obvious
  alternatives OVER-COUNT, MEASURED.** Cap TWO. **If it reads 2, WAIT.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the empty-file floor beside any seconds figure** (C-53).
- **RUN A NEGATIVE CONTROL that MEASURES.** **`[LJ-1.368]` measured this week
  that a green can be a tautology when `squash₁` meets a motive that unfolds
  to a truncation. Do not produce one.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-379/lj-1.379-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `lint-agda.py --check`. **No em dash.** ASD-STE100. Evidence is `file:line`.
  Mark every negative **MEASURED** or **INFERRED**.

## PREMISES

- **The `hasWitnessAt` restatement supplies the bound at 8 insertions**, at
  `agents/tasks/LJ-1-360/Probe360.agda:109-115`.
- **The BACK direction is the one term left unmeasured**, at
  `agents/tasks/LJ-1-360/lj-1.360-report.md:11-13`.
- **Its closest candidate was refused**, at
  `agents/tasks/LJ-1-360/MustFail360.agda:1`, exit 42.
- **`arityNumAtL` has BOTH adequacy directions delivered**, at
  `src/L/Coding/CodeSet.lagda.md:189-197` and `:201-207`.

**Mark each VERIFIED or REFUTED at `file:line`.**

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Eleven of my last forty briefs carried a claim an agent measured FALSE, and
today three returns corrected a citation or a figure I had relayed.** **The one
at risk: 「the two-directional adequacy should pay at the BACK direction」.**
**That is my hope from `[LJ-1.350]`'s site, not a measurement at yours, and
P-l says a judgement at one site is a hypothesis at another.**

## THE RULES

**C-45: `exit 0` is not a supply, and its mirror, exit 42 is not an
impossibility, which `[LJ-1.368]` proved on a sibling chain this week.**
**C-57, C-44, D-10, C-42, C-53, C-55, C-58, P-l, P-k.**
**C-12, C-22, C-32, C-36, C-39, C-40.** I-5. **D-1, D-26.**
**DD0, DD4, DD8, DD18, DD23, DD24, DD25, DD28.**

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement.

## DD4

**Maximize the code the two proofs share, and write it generic.** **NAME YOUR
AXIS** (C-46), fixed at `scripts/measure/ledger.py:50`. **Every term on this
chain has been class-free; say whether yours is.** **`hasWitnessAt` sits in
the coding substrate that both towers read, so the answer is a DD4 fact and
not a formality.**

## ARCHIVE (DD18)

**`scripts/gate/check-dd18-survey.py` GATES your return: name each of the four
corpora, cited or declined in ONE line, and QUOTE one line per archived file
you read, at its real line number.**

- **`archive/src/2026-08-09-rud-route/`**: **grep for a witness or
  boundedness predicate with a two-directional adequacy.** **The retired route
  ran a different coding scheme, so「nothing transfers」is a fine answer and it
  must be MEASURED rather than assumed.**
- **`archive/dev/JOURNAL-archived.md`**: the retired witness step. **WHY NOT
  in one line if nothing bears.**
- **`archive/dev/DECISIONS-archived.md`**: any ruling on the coding
  substrate's shape. **WHY NOT in one line if none.**
- **`archive/dev/TASKS-archived.md`**: taking SHAPE and never a claim.

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md`.** **`[LJ-1.348]` called the restatement
「Devlin's own」. `[LJ-1.360]` was asked to verify that; read what it found and
say in ONE line whether the BACK direction has any counterpart in the text.**
Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-360/lj-1.360-report.md` section 4.3 FIRST, then
`MustFail360.agda` whole, and RE-RUN it.

## SCOPE (write)

`agents/tasks/LJ-1-379/` only.

## RETURN

**Lead with ONE word: SUPPLIED, BLOCKED, or NOT-WORTH-FUNDING.** Then Agda's
own type for the refusal. Then whether `arityNumAtL`'s two directions pay
here. Then what the 54 to 56 becomes. Then your negative control, and say why
it is not a tautology. **Mark every negative MEASURED or INFERRED.**

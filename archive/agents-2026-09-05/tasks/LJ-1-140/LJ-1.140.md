# LJ-1.140: close the D-against-DD retarget, everywhere, and give it a checker

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**A `D` code cited with no home resolves against a `DD` row of the same number
that means something else.** `[LJ-1.139]` repaired the memo headers and found
eight more places. **Finish the sweep, then make the defect impossible to
reintroduce.**

## THE DEFECT, and I verified every instance below myself

The whole `D` series was archived on 2026-08-09 and the live series is `DD`.
**The two series share numbers and mean different things.** So a bare `D7` in a
live document silently retargets to `DD7`.

**`scripts/check-rule-ids.py` is GREEN through all of it.** It verifies that a
code RESOLVES. It never verifies that a code resolves to the series the author
meant. **That is the same shape as the stale-probe rule this morning: green
while wrong.**

MEASURED, by me, at these lines:

| site | what it says | what happens |
|---|---|---|
| `dev/STYLE-agda.md:73` and `:152` | 「PLAN D7」 for naming hygiene | `dev/PLAN.md:164` says **DD7 is REVOKED OUTRIGHT**. A reader concludes the naming rule is dead. **It is not** |
| `scripts/README.md:483` | 「(D20, `dev/PLAN.md` section 3)」 | Section 3 holds no D20. The location is named and wrong |
| `dev/PLAN.md:193` | sends the struck D8 row to `DECISIONS-archived.md` | it is in `archive/dev/JOURNAL-archived.md:4275` |
| `dev/PLAN.md:307` | 「the L0 standing track (§6.0)」 | the L0 row is section 11, at `:343` |

`[LJ-1.139]` reports **eight sites across three files, plus two in
`dev/PLAN.md`**. **Its report at `agents/reports/lj-1.139-report.md` lists
them. Read it first and treat its list as a starting point, not a census.**

## WHAT TO DO

### Part 1: the sweep, and make it a census

**Find every `D<n>` citation in every LIVE document.** Live means: `AGENTS.md`,
`dev/*.md`, `dev/memos/*.md`, `scripts/*.py`, `scripts/README.md`,
`src/**/*.lagda.md`. **NOT `agents/` and NOT `archive/`: those are frozen
records and nobody rewrites them.**

**For each, decide which series the author meant**, and say how you decided.
**The test is what the sentence CLAIMS, not what the code resolves to.**
`dev/STYLE-agda.md:73` claims a naming rule; DD7 is a revocation; so the author
meant archived D7.

**Then write the home beside the code.** `dev/PLAN.md:307` already does this
for D11 and it is the cheap general cure `[LJ-1.139]` recommends.

**Fix the two locator errors too** (`dev/PLAN.md:193` and `:307`), which are
the same family: a citation that names a location and names the wrong one.

### Part 2: the checker, and it must not overclaim

**Teach `scripts/check-rule-ids.py` the difference.** The rule to enforce, and
you may sharpen it:

> **In a live document, a bare `D<n>` with no home is a defect when a `DD<n>`
> row exists.** Writing the home clears it.

**Add a test for every rule you add.** `scripts/tests/` exists and
`scripts/tests/test_probe_lifecycle.py` landed today as the model.

**Then state the checker's honest limit in `scripts/README.md`, and in the
`AGENTS.md` enforcement column if the row needs it.** `AGENTS.md` warns that a
row claiming more than its checker delivers turns a rule into false safety, and
**a checker that cannot tell which series an author MEANT should say so.**

### Part 3: the lesson

**Propose a `dev/LESSONS.md` entry with its measurement.** The measurement is
`[LJ-1.139]`'s: ten bad pointers, eight of which resolve, found in nine
headers, after **two prior audits saw the pair and filed it as cosmetic**.

**The orchestrator assigns the ID; you propose the text and the measurement.**
A law is not admitted without its measurement.

**The candidate law, which you may replace with a better statement:** when a
numbering series is retired and a new one reuses its numbers, **every citation
of the old series must carry its home**, because a checker that tests
resolution cannot see intent.

## WHY IT MATTERS MORE THAN IT LOOKS

**`dev/STYLE-agda.md` is a style rulebook that dispatched agents read before
they write code.** Two of its lines currently tell a reader that a live naming
rule is revoked. **That is a rule being switched off by a citation.**

## THE ABORT CRITERION

- **The census completes and the checker lands**: report and STOP.
- **The checker cannot be written without false positives you cannot bound**:
  **say so, ship the sweep alone, and say what the residual risk is.** An
  honest 「no checker」 beats a noisy gate that trains people to ignore it.
- **A citation's intended series genuinely cannot be settled**: leave it, list
  it, say what would decide it. **Do not guess: guessing is what created this.**
- **Anything walls**: STOP, report it.

## WHAT YOU MUST NOT DO

- **Do not renumber a `D` code to a `DD` code.** They are different rules.
  Fixing a citation means adding its HOME, never changing its number.
- **Do not edit anything under `agents/` or `archive/`.** Frozen records.
- **Do not edit `AGENTS.md`.** DD19: propose the line and the owner rules. It
  changed twice today, so **read it fresh rather than from any report.**
- **Do not touch `src/*.lagda.md` content**, only a citation inside prose, and
  **only if you find one**. A master edit needs its consumers re-checked (C-40)
  and I am not funding a typecheck for a citation.
- **Do not run Agda. A sibling is running probes right now.**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** 「This is every site」 is MEASURED
only if you ran the census and say which search.

## ARCHIVE (DD18)

- **`agents/reports/lj-1.139-report.md`**, read WHOLE. The eight sites, the
  pattern, and why two audits missed it.
- **`archive/dev/DECISIONS-archived.md`**, for what each `D` code actually
  says. **You need this to decide which series an author meant.**
- **`dev/PLAN.md:161-186`**, section 3, the live `DD` table, and `:164`, the
  consolidation and revocation paragraph.
- `agents/reports/archive/lj-0.1-consistency.md` and `lj-0.2-sufficiency.md`.
  **Both missed this. `lj-0.2` found the pair and filed it under preferences.
  Read how it classified, because your census must not repeat it.**
- `scripts/check-rule-ids.py`, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature governs a citation series. Say so in one line.**

## SCOPE (read)

`agents/reports/lj-1.139-report.md` FIRST, then `scripts/check-rule-ids.py`,
then `dev/PLAN.md:161-186`.

## SCOPE (write)

`dev/*.md`, `dev/memos/*.md`, `scripts/*.py`, `scripts/README.md`,
`scripts/tests/`. Your report is `agents/reports/lj-1.140-report.md`.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for rewrite` and read every
statement.

- **C-22.** Write the deliverable incrementally.
- **C-26.** A duplicated rule drifts. **Two series sharing numbers is that law
  in a new shape.**
- **C-36.** Write the term you could not write.
- **C-39.** A brief's prohibition binds harder than its goal.
- **C-40.** Verify the CONSUMERS of `check-rule-ids.py`: `make check`,
  `scripts/tests/`, and the `AGENTS.md` enforcement column.
- **C-31, C-32, C-33, C-34, C-37, D-10, D-26, D-29.**

## CONSTRAINTS

- `.venv/bin/python scripts/lint-prose.py --check` on everything you write.
- `.venv/bin/python scripts/check-rule-ids.py` and
  `.venv/bin/python scripts/check-dev-docs.py` must both be green.
- **Run the full `scripts/tests/` suite**, not only your own.
- **No em dash, in any language.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the census: sites found, sites fixed, and how many RESOLVED to the
wrong rule.** Then the table, site by site, with how you decided which series
the author meant. Then the checker, its test count, and its honest limit. Then
the proposed `dev/LESSONS.md` entry with its measurement. Then anything you
could not settle. **Mark every negative MEASURED or INFERRED.**

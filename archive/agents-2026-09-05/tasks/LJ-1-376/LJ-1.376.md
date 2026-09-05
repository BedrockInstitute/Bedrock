# LJ-1.376: audit the tree for detours caused by the orchestrator

tier: fable (pi-subagent-mode), **the EMERGENCY tier, taken on the owner's
EXPRESS instruction of 2026-08-16. DEFAULT effort, which the owner named.**
**DD0 binds: this is a ONE-OFF instruction and NOT a standing head choice.**
In-harness. No Agda required.

## THE OWNER'S CHARGE, in their own words

> **「`BandChoice` is an instance of `SetChoice (ℓ-suc ℓ)`」is COMMON
> KNOWLEDGE. I find your foundations in mathematical logic are weak. Dispatch
> one round of fable 5 at default effort to audit the whole tree for detours
> caused by this kind of missing common knowledge, together with laziness
> about the archive survey and the literature survey.**

**The charge is against the orchestrator, not against any dispatched agent.**
**Audit accordingly: the defect to look for is in BRIEFS and in ORCHESTRATOR
DECISIONS, not in returns.**

## THE ADMITTED INSTANCE, so you start from a real one

`SetChoice ℓ` at `src/Base/Choice.lagda.md:54-55` is choice over a
SET-INDEXED family. `BandChoice = LimitBandT → ∥ LimitBand ∥₁`
(`agents/tasks/LJ-1-368/Probe368.agda:226-227`) is a selection from a
truncated family. **That it is an instance is recognition at the level of the
definitions.**

**What it cost instead: `[LJ-1.373]`, a probe with an Agda run, and
`[LJ-1.375]`, an adversarial review dispatched to check the「discovery」.**
**And the orchestrator reported it to the owner as a finding.**

**Also admitted, same day:** the orchestrator dispatched `[LJ-1.373]` to find
out by experiment whether a selection from a truncated family is provable.
**The HoTT Book's section 3.8 answers that, and the digest was already in the
tree at `dev/literature/truncation-and-selection.md`.** **The owner stopped
the run and ruled DD28 from it.**

## WHAT TO AUDIT, and the three kinds are different

**KIND A, MISSING COMMON KNOWLEDGE.** A brief that funds work to discover
something a competent logician knows by definition: a standard equivalence, a
standard non-implication, a principle's standard name, the standard strength
of an axiom.

**KIND B, THE ARCHIVE NOT SURVEYED.** Work funded to rebuild or re-price what
`archive/` already holds. **The known case is `[LJ-1.107]`, and BEWARE: the
story that it「failed to survey」was itself FALSE, measured by `[LJ-1.357]`,
and a delivered checker carried the false version for months. Do not inherit
that story; check every instance yourself.**

**KIND C, THE LITERATURE NOT SURVEYED.** Work funded to settle by experiment
what `dev/literature/` already digests. **DD28 was ruled today from exactly
one instance; your audit decides whether it had more.**

**A detour is not a wrong answer.** A refutation that cost a dispatch and
taught the project something is NOT a detour. **A detour is spend that a
reading would have saved.** **Say which of the three kinds each one is, and
what it cost in dispatches.**

## THE CORPUS

`agents/tasks/LJ-1-*/` holds about 270 brief-and-report pairs, plus
`agents/tasks/archive/`. `dev/PLAN.md` section 11 indexes every dispatch in
one row. `dev/JOURNAL.md` holds what each found. **`dev/PLAN.md`'s index is
the cheapest way in: read the rows, then open only the pairs that look like a
detour.** **Say how many rows you read and how many pairs you opened, so the
audit's own coverage is known.**

## WHAT I EXPECT, AND YOU SHOULD DISTRUST IT

**The orchestrator writing this brief is the subject of the audit.** **My
guess is that Kind A is rare and Kinds B and C are common, because the
archive-survey decay is measured** (`[LJ-1.358]`: 246 of 264 briefs never
named the archived DECISIONS, one bullet verbatim in 19). **That guess is
convenient for me: it blames a process rather than a competence.** **Test it.
If Kind A is the common one, say so plainly.**

## THE ABORT CRITERION (D-1)

- **DETOURS FOUND.** List them, each with its kind, its cost in dispatches,
  and the reading that would have prevented it. **Rank by cost.**
- **FEW OR NONE.** **Say so.** **The owner's charge would then be a fair
  judgement about one episode rather than a pattern, and that is worth knowing
  exactly as much.** **Do not manufacture a pattern to justify the dispatch.**
- **THE PATTERN IS REAL BUT DIFFERENT.** **If the recurring defect is
  something neither the owner nor I named, that is the most valuable return.**

## WHAT TO PRODUCE BESIDES THE LIST

**One section: what would have caught each one.** **DD28 now catches Kind C
for provability questions. Say whether it would have caught the ones you
find, and what it does NOT catch.** **Do not design a mechanism; name what
the evidence supports.**

## CONSTRAINTS

- **AUDIT ONLY. Land nothing, repair nothing.** Write only in
  `agents/tasks/LJ-1-376/`. **`src/` is forbidden** (I-5).
- **Do NOT edit `dev/PLAN.md`, `dev/LESSONS.md` or `AGENTS.md`.** Any proposed
  text goes in your report.
- **`[LJ-1.374]` and `[LJ-1.375]` are live.** `[LJ-1.374]` holds one Agda
  slot; `[LJ-1.375]` is in-harness. **You need no Agda; if you run any, count
  the slots first with
  `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`, cap TWO, and use
  `GHCRTS="-A64m -I0 -M8g"`.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-376/lj-1.376-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check`. **No em dash.**
  ASD-STE100. **Evidence is `file:line`, and for a count, the command.** Mark
  every negative **MEASURED** or **INFERRED**.

## PREMISES

- **`BandChoice` is an instance of `SetChoice (ℓ-suc ℓ)`**, at
  `src/Base/Choice.lagda.md:54-55` and
  `agents/tasks/LJ-1-368/Probe368.agda:226-227`.
- **It cost `[LJ-1.373]` and `[LJ-1.375]`.**
- **The archive-survey decay is measured**, `[LJ-1.358]`.
- **DD28 was ruled from exactly one literature instance.**

**Mark each VERIFIED or REFUTED at `file:line`.**

## THE RULES

**DD28, ruled today.** **DD18: the archive and literature surveys are brief
and return sections, not a hope.** **C-57: the search that finds it and the
reading that discards it are two different failures.** **C-59: a gate you do
not run is worth what a gate you do not have is worth.** **C-48, C-45, C-44,
C-42, D-10, P-l, P-k.** **C-22, C-32, C-36, C-39, C-40.** I-5. **D-1, D-26.**
**DD0, DD4, DD13, DD19, DD23, DD25.**

Run `.venv/bin/python scripts/dispatch/rules.py --for review` and read every
statement.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker. **NAME YOUR AXIS** (C-46).

**Your axis is not the two towers; say so plainly rather than force the
section.** **What IS live: a detour spends the budget that DD4's real work
needs, and this project's endpoint is two trophies under DD5's constraints.
If any detour you find cost work that DD4 would have valued, say which.**

## ARCHIVE (DD18)

**`scripts/gate/check-dd18-survey.py` GATES your return, and Kind B is about
this very duty, so meet it exactly: name each of the four corpora, cited or
declined in ONE line, and QUOTE one line per archived file you read, at its
real line number.**

- **`archive/dev/TASKS-archived.md`**: **265 rows of what the RETIRED route's
  dispatches found. Kind B detours are found by comparing live work against
  these rows, so this file is your primary instrument rather than a
  formality.**
- **`archive/dev/JOURNAL-archived.md`**: why the retired route did what it
  did. **A live task that re-derived a retired WHY is a Kind B detour.**
- **`archive/dev/DECISIONS-archived.md`**: the retired rulings.
- **`archive/src/2026-08-09-rud-route/`**: the retired CODE. **`[LJ-1.357]`
  measured that 155 of 264 briefs never named it.**

## LITERATURE (DD18)

**`ls dev/literature/` and read what bears.** **Kind C is about this corpus,
so a formal decline here would be self-refuting.** **Say which digests exist
and which live tasks should have consulted one.** Return a **LITERATURE
USED** section.

## SCOPE (read)

`dev/PLAN.md` section 11's index rows FIRST, whole. It is one row per
dispatch and it is the cheapest map of where a detour could be.

## SCOPE (write)

`agents/tasks/LJ-1-376/` only.

## RETURN

**Lead with ONE line: how many detours, and which kind dominates.** Then the
list, ranked by cost in dispatches, each with its kind and the reading that
would have prevented it. Then whether my guess (Kind A rare, B and C common)
survives. Then what would have caught each, and what DD28 does not catch.
Then your coverage: rows read, pairs opened. **Mark every negative MEASURED
or INFERRED.**

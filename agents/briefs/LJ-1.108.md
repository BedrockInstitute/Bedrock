# LJ-1.108: delete the unused refuted hypotheses from the remaining rows

tier: codex (default)

## GOAL

**Finish what `[LJ-1.105]` started.** The shared half is landed and green.
**Eight rows still STATE the refuted hypotheses, unused. Until they are
deleted, those rows are still vacuous.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`. **HEAD is
`d6da722` and `src/L/Condensation.lagda.md` carries `[LJ-1.105]`'s landed
repair, uncommitted and GREEN.** A sibling agent works on the cardinal side
and will not touch this file.

## WHAT IS LANDED, and I am re-checking it as you start

`[LJ-1.105]` landed the shared half in the master:

- **`EnvSet` now carries `arityK`, `E ∈ K` and `ar ∈ K`**, and derives the
  ChainZ `entryK` tie and the `arSubK` tie inside itself
  (`src/L/Condensation.lagda.md:2883-2903`).
- **The Mem row states `arityK` and no longer states `tmKeyK`, `entryK` or
  `arSubK`.** Its block shrank from 96 to 85 non-blank lines.
- **The other eight EnvSet rows and `ClauseAgree` gained `arityK`** and
  their `EnvSet` applications pass `arityK EK arK`.
- **Master GREEN.** 122.3 s cold before, 140.5 s after, +184 lines.

**And here is the part that is not finished, in the return's own words: the
eight rows' `entryK` and `arSubK` hypotheses "stay (unused) per the brief's
minimum-change rule", and `Eq`'s `tmKeyK` stays unused too.**

**An unused hypothesis of an EMPTY type still makes its module vacuous.**
`entryK`, `arSubK` and `tmKeyK` are refuted (`src/ProbeLJ197A.agda`,
`src/ProbeLJ195A.agda:45-48`). **So eight rows are still unusable, and the
repair is not done until they are deleted.**

## WHAT TO DO

1. **Delete the now-unused refuted hypotheses** from `TopAgree`,
   `NegAgree`, `ForallAgree`, `ExistAgree`, `EqAgree`, `AllInAgree`,
   `ExInAgree`, `ImpAgree` and `ClauseAgree`. `[LJ-1.105]` prices this at
   -5 non-blank lines per row, -6 where `tmKeyK` also goes.
2. **`AllInAgree` and `ExInAgree` need the `tmKeyK` derivation at the allin
   layout**, a `BndLeaf` `keyK-of` ported from `AtomLeaf`
   (`src/L/Condensation.lagda.md:4172-4195`). `[LJ-1.105]` prices each at
   about +35 lines and +1 to +2 s.
3. **The master is GREEN when you finish, or you revert it and say so.**
4. **Then grep the whole of `src/L/Condensation.lagda.md` for every
   remaining occurrence of the eleven refuted names** and **report what is
   left, by name and at `file:line`**, whether used or not. **That list is
   the honest state of the repair and it is a required part of the return.**

**The eleven refuted names:** `tmKeyK`, `entryK`, `arSubK-mem`,
`arSubK-neg`, `arSubK-top`, `arSubK-imp`, `keyK-neg`, `succK`, `keyK-un`,
`succK-allin`, `keyK-allin`. **Read their types in
`src/L/Condensation/TwelveAgree.lagda.md:86-243` so you recognise the
shapes; the row telescopes spell them differently.**

## THE RULE ON HYPOTHESES, stated as a test and not as a shape

**Every hypothesis you add must be one the CONSUMER can supply. Name what
supplies each, at `file:line`.** `arityK` is a `KFacts` field and is
supplied.

**Try to refute every tied form you write.** `src/ProbeLJ1104A.agda:118-120`
caught an empty tie one dispatch after the rule was written.

## THE ABORT CRITERION

- **All nine rows land green**: report the diff, the master's cold seconds
  before and after, and the remaining-occurrence list. Then STOP.
- **A row cannot lose its hypothesis because a use remains**: **report which
  row and which use, and CONTINUE to the next row.** **Report the count of
  rows that failed, not just the first.**
- **Anything walls**: STOP, report the wall with its seconds. **The master's
  cold check is about 140 s now. A wall is a real measurement.**

**Do not stop at the first negative.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. If a
check does not return, KILL IT before you start another, and report the wall
with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not weaken any row's conclusion.** Every row proves the SAME
  statement it proves today.
- **Do not delete a hypothesis that is still used.** If a use remains, that
  is the finding: report it.
- **Do not touch `src/L/Condensation/`, `src/L/Coding/`, `src/V/` or
  `src/L/BoundedSubset.lagda.md`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers from the source, never from a report.** **The master
  moved by 184 lines this morning, so every line number in every earlier
  report is stale.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**`[LJ-1.105]` already made the DD4 move: one derivation inside `EnvSet`
instead of nine copies.** This dispatch collects the saving. **Report the
net line change, and say whether the `BndLeaf` `keyK-of` should live in one
place rather than two.**

## THE COST QUESTION

The wing is over DD24 and the owner ruled the threshold question is settled
when the phase's content is complete. **So measure, do not gate.** Report
the master's cold seconds before and after, and the net non-blank in-fence
lines, with the load average.

## ARCHIVE (DD18)

- **`_build/lj-1.105-report.md`**, read WHOLE. **Its section 2 is your work
  list and its prices are what you are testing.**
- `src/ProbeLJ1104A.agda` and `_build/lj-1.104-report.md`, the proved row
  and the `keyK-of` derivation.
- `src/ProbeLJ197A.agda` and `src/ProbeLJ195A.agda`, the eleven refutations.
- `_build/lj-1.99-report.md`, the per-row supply table for the key-fact
  family, which is NOT part of this repair.
- `dev/LESSONS.md` **C-38 as extended, C-39**, C-35, C-36, D-29, D-30, P-i,
  P-w, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked. Spend nothing.** Say so in one line.

## SCOPE (read)

`_build/lj-1.105-report.md` section 2 FIRST, then the nine row telescopes
in `src/L/Condensation.lagda.md`, then `AtomLeaf`'s `keyK-of`.

## SCOPE (write)

`src/L/Condensation.lagda.md` (**green at the end or reverted**) and
`src/ProbeLJ1108*.agda`. Your report is `_build/lj-1.108-report.md`.
**Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for rewrite`, and read
every statement.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it. **An unused hypothesis of an empty type is still an empty telescope.**
- **C-39.** A brief's prohibition binds harder than its goal. **If a line of
  this brief blocks a route you can see, say so in the report and name the
  route. That is a required section, not a courtesy.**
- **C-35, C-36, D-29, D-30, D-10.**
- **P-i.** The conversion-explosion playbook. **Read it whole.**
- **P-w.** A module application COPIES, and the copy is paid at USE.
- **P-h, P-k, P-l, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as the bundle gives
  them.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-8, D-26.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **The working tree carries
  `[LJ-1.105]`'s uncommitted repair. Losing it would cost a dispatch.**
- Do NOT run `make check`.
- **Run `scripts/check-fences.py --check`** and say the master count.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check` on anything you touch.
- DD23 freezes mathematical prose. **Change the code, not the prose, unless
  a sentence becomes false. If one does, say which and leave it.**
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.108-report.md` incrementally, skeleton first.

**Lead with how many of the nine rows lost their refuted hypotheses**, and
whether the master is green, with cold seconds before and after. Then the
per-row table. Then **the remaining-occurrence list for all eleven refuted
names, at `file:line`, used or not**. Then any row that could not lose its
hypothesis, with the use that remains. Then the C-39 section. **Mark every
negative MEASURED or INFERRED.** Then the DD4 answer with the net lines.

# LJ-1.140 report: the D-against-DD retarget, closed and gated

STATUS: COMPLETE, with ONE file handed over rather than written.

## READ THIS FIRST: the gate is RED on four lines, on purpose

**`scripts/check-rule-ids.py` reports 5 findings and ALL 5 are in
`scripts/README.md`.** The rest of the tree is clean.

**The reason is the coordinator's mid-task instruction**, which arrived after I
had already repaired that file: `[LJ-1.141]` holds `scripts/README.md`, so I
**reversed all three of my edits there** and the file is now byte-identical to
`HEAD` (MEASURED: `git diff --stat scripts/README.md` prints nothing). I did
not use `git checkout`, which would have destroyed the sibling's work in the
same file.

**The finished replacement text is in "THE `scripts/README.md` HANDOVER"
below**, as three hunks with their exact anchors. Applying it turns the gate
green. Nothing else is needed.

**I did not narrow the checker to hide this.** Dropping `scripts/README.md`
from scope would have made the gate green while the worst instance the brief
names stood untouched, which is the exact "green while wrong" failure this task
exists to close. The test suite is written to pass both before and after the
handover lands.

## The other three carve-outs the coordinator named

| File | Held by | What I did |
|---|---|---|
| `scripts/check-probes.py` | `[LJ-1.141]` | **Not touched.** My census found no defect in it |
| `dev/ORCHESTRATION.md` | `[LJ-1.141]` | **Not touched.** MEASURED clean: its only citations are `archived D26(B)` at `:348`, which already carries its home, and D30/D35, which have no `DD` twin |
| `dev/ledger.toml` | `[LJ-1.141]` | **Not touched.** It is not a scanned file type |
| `dev/LESSONS.md` **D-1 entry** | `[LJ-1.141]` | **Not touched.** D-1 is at `:1038`. My nine edits are at `:228, :236, :846, :848, :855, :1484, :1520, :1647, :2450`, none inside D-1, and the coordinator's message keeps `dev/*.md` mine |

**VERIFIED, not assumed.** `git diff dev/LESSONS.md` shows my nine repairs AND
the sibling's probe-path rewrites side by side, intact. Neither of us used a
whole-file write, which is why nothing was clobbered. **If either agent later
uses `Write` on `dev/LESSONS.md`, the other's work vanishes silently**, so the
orchestrator should re-read that diff before committing.

## COUNT (lead)

**MEASURED, by the checker this task built, run against the HEAD content of
every live document** (`git show HEAD:<file>` fed to `series_findings`):

- **87 defective LINES in 15 files.** 137 findings, because one line can carry
  the same defect twice.
- **ALL 87 RESOLVE.** Not one is dangling, which is why
  `scripts/check-rule-ids.py` was green through every one of them.
- **68 lines are a genuine archived-decision citation with no home**, and each
  has a live `DD` row of the same number that states a DIFFERENT rule. That is
  the defect the brief names, and it is **8.5 times the eight sites
  `[LJ-1.139]` reported.**
- **19 lines are a code that was NEVER a decision**, colliding with the
  decision series by shape. **This is a new finding and it is a wider defect
  than the brief's**: FOUR more numbering series write `D<n>`, and one of them
  is inside `dev/LESSONS.md`, which binds new code. See "Four more series".
- **2 lines send a `D` code to `dev/PLAN.md` section 3**, which holds the `DD`
  table and no `D` row. The brief called this the worst instance and it is: the
  reader is told exactly where to look and looks there.
- **83 of the 87 are repaired in the tree. The remaining 4 are the
  `scripts/README.md` handover above**, written as finished prose rather than
  applied, because a sibling holds the file.
- **Plus the 2 locator errors the brief named** (`dev/PLAN.md:193` and `:307`),
  which no checker can see. Both repaired.
- **Nothing under `agents/` or `archive/` was edited. No `D` code was
  renumbered to `DD`.** MEASURED: `git diff --name-only` names no path under
  `agents/`, `archive/` or `src/` from my work.

## THE CENSUS, and which search

**MEASURED.** The search is the regex `check-rule-ids.py` already uses for a
decision reference, `(?<![\w-])(D\d{1,2})(?![\w-])`, whose lookbehind is what
stops `DD5` matching as `D5`. I ran it over `AGENTS.md`, `dev/**/*.md`,
`scripts/*.py`, `scripts/README.md`, `scripts/tests/*.py` and
`src/**/*.lagda.md`: **312 raw hits.** I then classified each by hand and turned
the classification into the checker, so the census and the gate are one
mechanism rather than two that can disagree.

**The 312 reduce to 87 by three exclusions, and each is stated rather than
assumed:**

- **`dev/JOURNAL.md` and `dev/memos/`** are dated records. The checker already
  skipped them for decision currency and I did not change that. `[LJ-1.139]`
  repaired the memo line-3 headers, which ARE live guidance, and left the
  bodies alone for the same reason.
- **`agents/` is a frozen record.** MEASURED: with the rest of the tree green,
  `--briefs` carried 487 findings and **485 of them were series findings inside
  `agents/`**, on text nobody may rewrite. I excluded the tree in the checker
  and said why in the code. `lint-prose.py:440` already drops it on the same
  doctrine.
- **`scripts/tests/`** carries fixtures that reproduce PLAN rows verbatim to
  pin what the checkers do to real text. Rewriting a fixture falsifies its test.
- **`src/**/*.lagda.md` had ONE hit and it is not a citation.**
  `src/L/BoundedSubset.lagda.md:892` is `module D0 = Δ₀Small ...`, an Agda
  module alias inside a code fence. `DD0` does not exist, so the rule never
  fires on it. **I touched no master**, as the brief required.
- **`AGENTS.md` carries ZERO `D<n>` citations.** MEASURED.

**`[LJ-1.139]`'s list was a starting point and not a census, exactly as the
brief warned.** It reported eight sites in three files plus two in PLAN. The
true figure is 87 lines in 15 files. It missed `dev/ARCHIVE.md` entirely, all
of `scripts/*.py`, and `dev/LESSONS.md`, because its write scope was
`dev/memos/` and it reported only what it happened to open.

## THE SITE TABLE, by class, with how I decided which series

**The test is what the sentence CLAIMS, and I read the archived text of every
code I judged.** `archive/dev/DECISIONS-archived.md` gives what the `D` code
says; `dev/PLAN.md:166-186` gives what the `DD` row says.

### Class A: the archived decision cited with no home (68 lines)

| Site | What it claims | The `DD` twin it retargets to | Verdict |
|---|---|---|---|
| `dev/STYLE-agda.md:73`, `:152` | naming hygiene, no primes or iteration numbers | **DD7 is REVOKED OUTRIGHT** (`dev/PLAN.md:164`) | archived D7. **This is a live rule being switched off by a citation** |
| `dev/STYLE-agda.md:52` | classical principles are module parameters | DD2 is the endpoint and architecture ruling | archived D2; the LIVE home is DD9, which `dev/PLAN.md:193` states |
| `dev/STYLE-agda.md:69` | the book parts are fixed | DD5 is the two quantitative constraints | archived D5; the LIVE statement is PLAN section 4 |
| `dev/STYLE-agda.md:284` | authoring order, English first | DD6 merged into DD5, which carries the size caliber | archived D6; the LIVE statement is `AGENTS.md` Boundaries |
| `dev/STYLE-agda.md:11` | provisional rules harden with experience | DD11 is code and prose craft | archived D11. **The word `archived` was already on the line, 27 characters away, about the tension REGISTER.** This is the case that killed the window design |
| `dev/PLAN.md:154` | the postulate is removed by parameterization | DD2 is the endpoint | archived D2; live home DD9 |
| `dev/PLAN.md:189` (twice) | the part level is fixed | DD5 is the quantitative constraints | archived D5. Section 4 is its own live statement |
| `dev/PLAN.md:294` | the build constraints, and the old budgets | DD10 merged into DD9 and DD11; DD13 is retirement | struck D10, archived D13. **"struck on 2026-08-05" dates it to the D era, four days before the DD series existed** |
| `dev/PLAN.md:364`, `:370` | the archive regime and the consolidation gate | DD20 and DD21 both merged into DD19, governance | archived D20 and D21. Same dating evidence, 2026-08-04 |
| `dev/ARCHIVE.md`, 29 lines | 70 dated retirement records, plus the file's own header rules | DD17 dispatch, DD18 archive surveys, DD20 governance | archived, every one. Dated 2026-08-06 to 2026-08-09 |
| `scripts/check-tree.py`, 9 lines | the archive boundary, SPDX, the retiring set, the two-step | DD20, DD4 (maximum reuse), DD18, DD15 | archived D20/D4/D18/D15. **Live homes: DD13 for the archive rule, DD22 for licensing**, and I wrote both in |
| `scripts/ledger.py`, 6 lines | the archive is uncounted, re-measure at every return, the retirement set | DD20, DD27 (the hull index), DD26 (catalogs uncounted) | archived. Live homes DD13 and DD15 |
| `scripts/README.md`, 4 lines | the same four rules the tools state | DD20, DD4, DD18 | archived |
| `scripts/lint-prose.py` `:29` `:437`, `scripts/lint-agda.py` `:287` `:374`, `scripts/weave-i18n.py:121`, `scripts/check-glossary.py:23` `:291` | the archive boundary and the postulate ban | DD20, DD2 | archived D20 and D2; live homes DD13 and DD9 |
| `dev/LESSONS.md:1647`, `:2450` | a red archive is not a defect; the retiring subtree's rate | DD20 governance, DD18 archive surveys | archived D20 and D18 |

**How I decided, in one sentence per family.** A citation is archived when the
sentence states a rule the `DD` row of that number does not state; four of them
carry a second proof, a DATE before 2026-08-09, which is the day the `DD`
series was created.

### Class B: the locator defect (2 lines by checker, plus 2 by hand)

| Site | What it said | What is there | Fixed to |
|---|---|---|---|
| `scripts/README.md:483` | "(D20, `dev/PLAN.md` section 3)" | section 3 holds no `D20` | archived D20 in the archive; **the live home is DD13 in section 3** |
| `dev/ARCHIVE.md:8` | "ruling D20 ([dev/PLAN.md](../dev/PLAN.md) section 3, 2026-08-04)" | same | same, plus the file-level declaration |
| `dev/PLAN.md:193` | the struck D8 row is in `DECISIONS-archived.md` | **that file names D8 only in its retired-decisions paragraph; the row's text is at `archive/dev/JOURNAL-archived.md:4275`** | the row's real address, and a sentence saying what the other file does hold |
| `dev/PLAN.md:307` | "the L0 standing track (§6.0)" | section 6.0 is the coding rules; **the L0 row is section 11, at `dev/PLAN.md:343`** | "the L0 row of §11" |

**The last two are invisible to any checker I can write**, because both name a
real section that exists and simply is not the one holding the thing. I fixed
them by reading. `[LJ-1.139]` found both and I confirmed both at `file:line`.

### Class C: FOUR MORE SERIES write `D<n>` (19 lines). NEW FINDING.

**This is the finding the brief did not ask for and it is the one that
generalizes.** The brief's defect is two series sharing numbers. **There are
six.** Each of these resolves against the archived decision series and means
something else entirely.

| Series | Where | Evidence it is not a decision | What I wrote |
|---|---|---|---|
| **The R5 recon batch**, `D1` and `D2` | `dev/LESSONS.md:228, 236, 846, 848, 855, 1484, 1520` | `dev/LESSONS.md:857` lists "the D2, R5a-2, and K1 datums" against `agents/reports/archive/r5d2-report.md`, `r5a-report.md`, `k1-report.md`, in that order; `:1487` pairs the `D1` datum with `r5d1-report.md` | `R5-D1`, `R5-D2`, which is the report filename spelled out. **The hyphen stops the decision regex, so the collision is gone by construction** |
| **`[T95]`'s own defect numbering**, `D1`, `D3`, `D6`, `D6.5` | `scripts/check-timing.py:182, 320, 356` | the sentences read "the [T95] D1 failure mode: the ledger lost its data blocks", which is a defect report, not a ruling | "[T95]'s defect 1", "defects 3 and 6", "defect 6.5" |
| **A task code**, `D1` | `dev/literature/owner-notes-rud.md:7` | line 4 of the same file writes it in full as `[L3.30-D1]` (the digestion document) | `[L3.30-D1]` |
| **The notation itself**, in checker prose | `scripts/check-dev-docs.py:340-341`, `scripts/check-rule-ids.py:11-56` | the sentences EXPLAIN the two shapes; they cite nothing | rewritten to describe the shapes without writing a bare number |

**`dev/LESSONS.md` is the serious one.** It binds new code, `check-rule-ids.py`
excluded it from every scan (`p.name != "LESSONS.md"`), and it carried seven
citations that resolve to archived decisions D1 and D2 while meaning a recon
batch. **I put LESSONS.md inside the series check**, which is a scope change to
`make check` and is tested.

## THE CHECKER

`scripts/check-rule-ids.py`, two new rules, **63 tests** in
`scripts/tests/test_rule_series.py`, registered in the `Makefile` `test` target
(the target's own comment demands it in the same commit).

**RULE 1, the retarget.** In a live document, a bare `D<n>` is a defect when a
`DD<n>` row exists. Writing the home clears it: `archived D7`, `struck D8`, and
the same forms with a quote, a bracket or a possessive. The marker may sit at
the end of the PREVIOUS line, because `dev/` prose wraps at about 80 columns
and a checker that fires on reflow gets fought and then disabled.

**RULE 2, the locator.** A `D<n>` sent to `dev/PLAN.md` section 3 is a defect
whatever else the line says, because that section holds the `DD` table and no
`D` row.

**THE DESIGN DECISION WORTH RECORDING.** I built the home marker as a proximity
WINDOW first and **refused it on measurement**. `dev/STYLE-agda.md:11` reads
"(PLAN D11; tension T1's register is archived at ...)", where `archived`
describes the REGISTER and sits 27 characters from the code. **Every window
wide enough to be useful cleared that line, and that line was a real defect.**
So the marker must be the word immediately beside the code. The test
`a distant \`archived\` about ANOTHER noun does not clear` pins it, along with
two siblings: `archive` without the `d` does not clear, and naming the archive
DIRECTORY does not clear. Those three are what stopped 25 script comments
reading "the archive is outside every gate (D20)" from passing green.

**THE SCOPE IS WIDER THAN THE CITATION CHECK, and both differences are
deliberate.** `dev/LESSONS.md` was excluded from every scan because it holds
the headings the citation check resolves against; it cites decisions like any
other live document, so the series rule binds it. `scripts/*.py` is prose an
agent reads before it edits a checker, and 27 of its lines carried the defect.
**Both are tested by INJECTION**, not by trusting the file list: the test
appends a defect to each file, asserts the run goes red, and restores the file
in a `finally`. A checker that silently stopped reading a directory would
otherwise still print "clean".

### THE HONEST LIMIT, and it is in three places

Stated in the module docstring, in the `scripts/README.md` handover below, and
here.

**IT CANNOT TELL WHICH SERIES AN AUTHOR MEANT.** It reads the word beside the
code, never the sentence. A citation labelled `archived D5` that argues DD5's
content passes green. **It removes the SILENT retarget, where nothing beside
the code warns the reader at all, and claims nothing beyond that.**

**Three exemptions let real text through, and each is stated:**

1. **`dev/JOURNAL.md` and `dev/memos/`** are dated records. Pre-existing, and I
   did not widen or narrow it.
2. **A file may declare its whole series ONCE**, in a fixed `**D-SERIES NOTE.**`
   sentence. `dev/ARCHIVE.md` is the case: 70 dated retirement rows, and
   repeating the home 70 times would say one thing seventy times. **Nothing
   checks that the declaration is true of every row below it.** The declaration
   is prose a reader sees rather than an invisible marker, because a marker
   would warn the checker and not the reader, which is the wrong way round. The
   test measures the exemption's blast radius: an injected BARE code is cleared
   inside that file, and an injected LOCATOR defect still fires there.
3. **The locator rule skips a line that names a `DD` code**, because the
   repaired sentences read "archived D11; DD11 in section 3 is a DIFFERENT
   rule". **So a line that cites one code correctly and misdirects a second one
   passes.** Without this exemption the rule false-positives on `dev/PLAN.md:193`
   and on every sentence I wrote to fix the defect, which would have made the
   cure fail its own gate.

**I did NOT hit the abort criterion.** The false positives were bounded, named,
and each is either exempted with its reason or fixed by rewriting text that was
genuinely ambiguous. Nothing needed guessing.

## THE `scripts/README.md` HANDOVER

**Three hunks. Finished prose, apply as written.** Line numbers are as the file
stands at `HEAD` today; the anchor text is given so they survive `[LJ-1.141]`'s
edits. Applying all three turns `check-rule-ids.py` green.

### Hunk 1, at `scripts/README.md:243-247`, the `check-tree.py` invariant list

REPLACE these five lines, which begin "in-progress chapter sitting outside the
gate. The others:":

```
in-progress chapter sitting outside the gate. The others: **archive** (no live master imports a
module that lives only in `archive/`, D20), **shared-cjk** (no CJK in marker-free prose, which
would reach the English book verbatim, C-8), **spdx** (licensing has one source of truth, D4),
**retiring**, WARN only and SILENT today (it flagged a surviving master importing a chapter
the retired route's D18 was retiring; `retire_suspended` empties that set, so the check returns
```

WITH:

```
in-progress chapter sitting outside the gate. The others: **archive** (no live master imports a
module that lives only in `archive/`, archived D20, live home DD13), **shared-cjk** (no CJK in
marker-free prose, which would reach the English book verbatim, C-8), **spdx** (licensing has
one source of truth, archived D4, live home DD22),
**retiring**, WARN only and SILENT today (it flagged a surviving master importing a chapter
the retired route's archived D18 was retiring; `retire_suspended` empties that set, so the check returns
```

### Hunk 2, INSERT after `scripts/README.md:398`

That is the line "hygiene shipped a fake id.", which closes the
`## check-rule-ids.py` section, and before `## check-task-index.py` at `:400`.
**This is the checker's honest limit, which the brief requires stated here.**
Insert a blank line, then:

```
**THE SERIES CHECK, added 2026-08-13 by `[LJ-1.140]`.** Resolving is not enough
while two series share the numbers. The `D` series was archived on 2026-08-09
and the live series is `DD`, so a bare code resolves against the archive and
points the reader at the `DD` row of the same number, which is a different
rule. Archived D7 is naming hygiene; DD7 is REVOKED, so two lines of
`dev/STYLE-agda.md` told every agent that a live naming rule was dead. The
check has two parts. **A bare `D<n>` in a live document is a defect when a
`DD<n>` row exists**: the home goes beside the code, as `archived D7` or
`struck D8`, and the marker may sit at the end of the previous line, so a
reflow costs nothing. **A `D<n>` sent to `dev/PLAN.md` section 3 is a defect
whatever else the line says**, because that section holds the `DD` table and no
`D` row. The scope is wider than the citation check: `dev/LESSONS.md`, which
binds new code, and `scripts/*.py`, which agents read before they edit a
checker. `scripts/tests/` is excluded because its fixtures reproduce document
text verbatim. Pinned by `scripts/tests/test_rule_series.py`, 63 checks.

**WHAT THE SERIES CHECK CANNOT DO, and the limit is real.** It reads the word
beside the code, never the sentence, so **it cannot tell which series an author
MEANT.** A citation labelled `archived D5` that argues DD5's content passes
green. It removes the SILENT retarget, where nothing beside the code warns the
reader at all, and claims nothing beyond that. Three exemptions let real text
through and each is deliberate. `dev/JOURNAL.md`, `dev/memos/` and `agents/`
are dated records, so a July entry citing an August-struck code is correct as
history and nobody rewrites it. **A file may declare its whole series ONCE**,
in a fixed `**D-SERIES NOTE.**` sentence that a reader sees, which is what
keeps `dev/ARCHIVE.md`'s 70 dated retirement rows from saying one thing seventy
times; **nothing checks that the declaration is true of every row below it.**
The locator rule **skips a line that names a `DD` code**, because the repaired
sentences read "archived D11; DD11 in section 3 is a DIFFERENT rule", so a line
that cites one code correctly and misdirects a second one passes.
```

### Hunk 3, at `scripts/README.md:483`, in `## The archive`

REPLACE the line:

```
every gate is structurally blind to them (D20, `dev/PLAN.md` section 3).
```

WITH:

```
every gate is structurally blind to them (archived D20, in
`archive/dev/DECISIONS-archived.md`; the live home is DD13 in `dev/PLAN.md` section 3).
```

**This is the worst instance in the tree**, and the brief said so: it names a
location explicitly and the location cannot hold the code. Section 3 holds the
`DD` table; `DD20` there is only a merge note into DD19, and the archive rule
lives in DD13.

### C-40: THE CONSUMERS, verified

| Consumer | State |
|---|---|
| `make check` (`Makefile:104`, `ruleids` target) | **RED on 5 findings, all in `scripts/README.md`**, which is the pending handover above. Every other scanned file is clean |
| `make check`'s companion `rules.py --check` | GREEN, `clean (5 bundles, cap 12, 141 lessons)` |
| `--briefs` mode | **Was 487 findings with my change and no exclusion; is 7 now**, being the 5 handover lines plus 2 pre-existing dangling `R-9`/`R-16` citations at `agents/briefs/l3.32-t110-brief.md:20` that I did not touch and must not |
| `scripts/tests/` | New suite `test_rule_series.py`, **63 checks**, added to the `Makefile` `test` target, whose own comment demands it in the same commit |
| `scripts/check-dev-docs.py` | GREEN, `clean (6 subcheck(s))`. Its `:55` comment names `check-rule-ids.py` as the enforcer of rule IDs and still reads true |
| `scripts/check-task-index.py` | GREEN, 442 cited codes, 456 rows |
| Explicit-path mode (`check-rule-ids.py <file>`) | Unchanged, and now tested: an explicit list is NOT widened to `scripts/` |
| Explicit-DIRECTORY mode | **Was broken before this task and is fixed.** `check-rule-ids.py dev/` raised `IsADirectoryError`, because `Path.exists()` is true of a directory and `read_text()` is not. A directory argument now expands. Tested |
| `scripts/lint-prose.py:443` | cites `check-rule-ids.py:83` for the JOURNAL exemption. **That line number MOVED.** The citation names a line rather than a symbol, so it is now stale. **Flagged, not fixed:** `lint-prose.py` is not in my brief's write scope for this, it is the same defect class one layer down, and see "COULD NOT SETTLE" |
| `AGENTS.md` enforcement column | **Needs a line. DD19 forbids me to edit it. Proposal below** |

### THE `AGENTS.md` LINE I PROPOSE (DD19: the owner rules, I do not edit)

The **Project rulings** row currently ends its enforcement column with
`` `scripts/check-rule-ids.py`; the orchestrator; briefs ``. That claims more
than the checker delivered until today and less than it delivers now. **Read
`AGENTS.md` fresh before applying this: the brief says it changed twice today.**
Proposed replacement for that cell:

> `scripts/check-rule-ids.py`, which resolves every code AND refuses a bare `D<n>` where a `DD<n>` row exists, so the two series cannot be confused silently. **It cannot tell which series an author MEANT**; `dev/JOURNAL.md`, `dev/memos/` and `agents/` are exempt as dated records, and a file may declare its whole series once. The orchestrator; briefs

## THE PROPOSED `dev/LESSONS.md` ENTRY

**The orchestrator assigns the ID.** The class is C (craft and process). The
measurement is `[LJ-1.139]`'s and `[LJ-1.140]`'s together.

> ### C-nn. A retired numbering series must carry its home at every citation, because a resolution check cannot see intent
>
> **Rule:** When a numbering series is retired and a new series reuses its
> numbers, **every citation of the old series carries its home beside the
> code**, in the same clause: `archived D7`, `struck D8`. A checker that tests
> whether a code RESOLVES cannot see this defect, because both codes resolve.
> **Do not renumber the old code**; the fix is the home, never the number. And
> **before reusing any number, check what else in the tree already writes that
> shape**: the collision is rarely with only one other series.
>
> **Measured, 2026-08-13, two dispatches.** `[LJ-1.139]` found **10 bad
> pointers in 9 memo headers, 8 of which RESOLVE** and lead to a rule the
> author never meant. `[LJ-1.140]` then ran the census the same day and found
> **87 defective lines in 15 live files, all 87 resolving**, of which 68 are a
> genuine archived-decision citation with a live `DD` twin that states a
> different rule. `scripts/check-rule-ids.py` was GREEN through every one, for
> 4 days, because it verifies that a code resolves and never that it resolves
> to the series the author meant.
>
> **The two multipliers, and they are the reason this is a law rather than a
> chore.** **(1) Detection is not the failure; CLASSIFICATION is.** Two audits
> saw it first. `agents/reports/archive/lj-0.2-sufficiency.md:214-218` found
> the pair, wrote that both memos "name the revoked two-caliber discipline as
> current", and then filed it **under preferences** with "fix when next
> touched"; `lj-0.1-consistency.md` never scanned the memos at all. **A pointer
> that resolves to a REVERSED rule was priced as cosmetic staleness, and that
> bought it a deferral instead of a fix.** **(2) A retarget can switch a live
> rule OFF.** `dev/STYLE-agda.md:73` and `:152` cited `PLAN D7` for naming
> hygiene while DD7 reads REVOKED OUTRIGHT, so a style rulebook that every
> dispatched agent reads before it writes code told them a live rule was dead.
>
> **The corollary that generalizes, and it is measured too.** The census found
> **four MORE numbering series writing `D<n>`**: a recon batch inside
> `dev/LESSONS.md` (7 lines, where `D2` means `agents/reports/archive/r5d2-report.md`),
> `[T95]`'s own defect numbers in `scripts/check-timing.py` (3 lines), a task
> code in `dev/literature/`, and the checkers' own prose about the notation.
> **A shape that two series share is usually shared by more than two.**
>
> **Enforcement:** `scripts/check-rule-ids.py`'s series check, pinned by
> `scripts/tests/test_rule_series.py`, with its limit stated in
> `scripts/README.md`: it reads the word beside the code, never the sentence.
>
> **Provenance:** `agents/reports/lj-1.139-report.md`,
> `agents/reports/lj-1.140-report.md`.

## COULD NOT SETTLE

**One item, and it is small.** `scripts/lint-prose.py:443` cites
"`scripts/check-rule-ids.py:83`" for the JOURNAL exemption, and my edits moved
that line to 101. **A citation by line number into a file that changes is the
same defect class this task closes**, one layer down: it resolves to a line,
and the line now says something else. **What would decide it:** the owner's
call on whether a cross-file citation may name a line at all, or must name a
symbol (`HISTORICAL`). I did not fix it, because rewriting an unrelated
checker's comment is scope I was not given, and because the honest repair is
the general rule rather than one line number.

**Nothing else is unsettled. Every one of the 87 lines was decided from the
archived text plus, where available, a date that predates the `DD` series. No
citation needed a guess.**

## DID NOT DO, and why

- **`scripts/README.md`.** Held by `[LJ-1.141]`. Reverted to `HEAD`, handed
  over as three finished hunks.
- **`AGENTS.md`.** DD19. Proposal above, unapplied.
- **`agents/` and `archive/`.** Frozen. Not read for edits, only for evidence.
- **`src/**/*.lagda.md`.** One hit, and it is an Agda module alias rather than a
  citation. No master edited, so no consumer needs re-checking (C-40) and no
  typecheck is owed.
- **No Agda ran.** A sibling holds the slot.
- **No commit, no push, no `make check`.**

## CONSTRAINTS MET

- `.venv/bin/python scripts/lint-prose.py --check dev/`, exit 0. Same on this
  report.
- `.venv/bin/python scripts/check-rule-ids.py`: **5 findings, all in
  `scripts/README.md`**, which is the handover. Every other file clean.
- `.venv/bin/python scripts/check-dev-docs.py`, `clean (6 subcheck(s))`, exit 0.
- `.venv/bin/python scripts/check-task-index.py`, OK, 442 cited codes.
- `.venv/bin/python scripts/rules.py --check`, `clean (5 bundles, cap 12, 141 lessons)`.
- **The FULL `scripts/tests/` suite ran, not only mine.** 11 suites. **9 pass.
  My new suite passes at 63/63.** Two fail and **NEITHER is mine, MEASURED:**
  - `test_probe_lifecycle.py` dies with `AttributeError: module 'check_probes'
    has no attribute 'stem_codes'`. `scripts/check-probes.py` is modified in the
    working tree by `[LJ-1.141]`, `archive/tooling/check-probes-lifecycle.py`
    is new and untracked, and a replacement `test_probe_gate.py` has appeared
    and PASSES. That suite is mid-retirement by the sibling.
  - `test_ratio_baseline.py` fails `the bucket EQUALS the cone: want 17185 got
    20286`. That is a line count over `src/`. **I edited no file under `src/`,
    and my whole `scripts/ledger.py` diff is comments plus one printed label**,
    which `git diff scripts/ledger.py` shows in full. `src/L/Condensation.lagda.md`
    was already modified when this session started.
- **The test suite writes nothing.** Its first version proved scope by appending
  a defect to each scanned file and restoring it in a `finally`. **That is a
  real edit to a file another agent may be holding**, and today one was, so I
  refactored the scope into `series_target_paths()` and the suite now asserts
  against the returned list. No disk write, no clobber window.
- **No `D` code renumbered to a `DD` code.** Every archived `D` number in every
  line I touched is still that number; only its home was added.
- **No em dash. No half-width sentence punctuation in CJK.** `lint-prose` green.
- Evidence is `file:line` throughout. ASD-STE100.

## ARCHIVE USED (DD18)

- **`agents/reports/lj-1.139-report.md`, read WHOLE.** Taken: the eight
  out-of-scope sites at `:104-111` and the two PLAN defects at `:115-122`, which
  I confirmed independently and which seeded the census; the cheap general cure
  at `:203`, "write the location beside the code", which is Rule 1; and the
  classification finding at `:144-151`, which is the lesson's first multiplier.
  **Its list proved to be 8 of 87.**
- **`archive/dev/DECISIONS-archived.md:29` D1, `:30` D2, `:32` D5, `:33` D6,
  `:34` D7, `:36` D11, `:42` D20, `:47` D26.** Taken: what each archived code
  actually says, which is how I decided every Class A row. Without D7's text at
  `:34` I could not have shown that `dev/STYLE-agda.md:73` states a LIVE rule.
- **`archive/dev/DECISIONS-archived.md:25`.** Taken: the struck-decision
  paragraph, which is the only place that file names D8. This is the evidence
  that `dev/PLAN.md:193` sent the reader to the wrong file.
- **`archive/dev/JOURNAL-archived.md:4275`.** Taken: the struck D8 row's text
  lives HERE. This is the repair for `dev/PLAN.md:193`.
- **`agents/reports/archive/lj-0.2-sufficiency.md:214-218` and `:287-289`.**
  Taken: it found the pair and wrote "I list these under preferences", then
  recommended "fix when next touched". **Read for HOW it classified, as the
  brief required.** My census avoided the repeat by not searching for a known
  event: the checker enumerates every code with a twin, so it cannot be
  keyword-shaped.
- **`agents/reports/archive/lj-0.1-consistency.md`.** Taken: it scanned
  `dev/PLAN.md` and `AGENTS.md` only, which is why the memos and `scripts/`
  survived it.
- **`dev/PLAN.md:162`, `:164`, `:166-186`.** Taken: the consolidation and
  revocation paragraph, which is what makes DD7 a revocation and DD20/DD21
  merges into DD19; and the live `DD` table, which is what each number means
  today.
- **`scripts/check-rule-ids.py`, read WHOLE**, before editing.

## LITERATURE (DD18)

**Nothing in `dev/literature/` governs a citation series, and I read none of it
as mathematics.** I opened `dev/literature/owner-notes-rud.md:1-10` only
because the census flagged line 7, and what I took there is a task code, not a
mathematical claim.

## DD4, MAXIMUM REUSE

**No Agda was written, so the generic-or-fixed choice does not arise. The
document-and-tooling analogue does, and I applied it three times.**

1. **The census and the gate are ONE mechanism.** I wrote the checker first and
   used its output as the census, rather than hand-listing 87 sites and then
   writing a checker that might disagree with my list. The classification I
   made by hand became `SERIES_HOME_BEFORE` and `SERIES_HOME_AFTER`, so the
   next census costs one command.
2. **One declaration replaces 70 repairs.** `dev/ARCHIVE.md`'s 70 dated
   retirement rows are cleared by a single sentence a reader sees, rather than
   by 70 edits that say the same thing. The mechanism is generic: any future
   record file uses the same sentence.
3. **I reused `dev/PLAN.md:307`'s existing phrasing** as the shared repair form,
   as `[LJ-1.139]` did for the memo headers, so a reader who learns the
   convention once reads it the same everywhere. **I did NOT invent a per-site
   wording.**

**Where I chose the more expensive shape and why.** The line-wrap tolerance
(`LINE_START`, plus carrying the previous line) cost about six lines and one
test. Without it every author who reflows a paragraph gets a red gate for a
formatting change, and DD4's attitude clause applies to tooling too: the cheap
version would have been paid for by everyone else, forever.

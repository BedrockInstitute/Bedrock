# LJ-1.183 report: audit of the orchestrator against every DD, under DD0

tier: pi (override). Read-only audit. No master, brief or report was edited.
No Agda ran. No commit, no push. Every finding is marked MEASURED or INFERRED.

## 0. LEAD: FOUR new violations beyond the admitted six

**The most expensive one: the struck DD27 figure still ships in the brief of
the build `[LJ-1.178]`, and the correction commit claims it is fixed.** The
brief tells the agent two opposite things. The bar section says DD24 is the
whole rule and not to judge against a tightened figure. Three other spots in
the same brief still tell the agent to report against the struck module rate.

The other three are: the same struck question still sits in the live status
screen; the orchestrator's own rulebook still names the heads, which is the
DD19 violation its own commit fixed elsewhere; and DD4 lapsed on 11 briefs.

**One residual of an admitted item** (DD25 index rows still do not name their
review codes) and **one claim-vs-diff discrepancy** follow the four.

| # | ruling | act at `file:line` or commit | cost | self-reported |
|---|---|---|---|---|
| F1 | DD24 | `agents/tasks/LJ-1-178/LJ-1.178.md:40,156,168` | one build brief self-contradictory; frozen record carries a struck ruling | partly, claims fixed |
| F2 | DD24 | `dev/PLAN.md:85-93` | live status screen carries the struck question | no |
| F3 | DD19 | `dev/ORCHESTRATION.md:32-37,88,129-130` | orchestrator's rulebook names wrong heads | no |
| F4 | DD4 | 11 briefs and 8 reports, all 2026-08-13 | the rule with repetition as its only enforcement lapsed | no |
| F5 | DD25 | `dev/PLAN.md:737,740,744,747` | enforcement point unmet | admitted |
| F6 | DD13 | commit `8bc2ae5` | one README deleted, claim says zero | no |

## 1. THE FINDINGS, RANKED BY COST

### F1. The struck DD27 figure still ships in the `[LJ-1.178]` brief. MEASURED

**The rule.** The owner struck the duplicate DD27 at commit `cda4619`. The
commit body says: "there is no module-rate-against-wing-rate question, no spent
tolerance, no per-module tightening and no debt to collect." DD24 is the whole
rule, and `0.009143` (the module rate) is not a bar.

**The act.** The brief `agents/tasks/LJ-1-178/LJ-1.178.md` still carries the
struck figure in three places:

- `:40` "Report the lines, the seconds against DD27's figure".
- `:156` "DD8, DD27, D-1, D-10, D-26, D-29, D-30".
- `:168` "the seconds against 0.009143".

The same brief says the opposite at `:70-76`: "THE BAR, AND IT IS DD24
UNCHANGED ... do NOT judge this build against a tightened figure."

**Why the correction missed it.** The brief went out at `142637c` with the
wrong bar. Commit `cda4619` then fixed the bar section at `:70-76` but not the
abort criterion at `:40`, the mandatory rules at `:156`, or the RETURN at
`:168`. The commit claims "all three [briefs] are corrected, in the files".
This brief is corrected in one place and wrong in three.

**The cost.** `[LJ-1.178]` is a build that funds work today. The agent received
a brief that is self-contradictory, and a mid-flight message telling it the
bar changed. The agent's own report records the damage:
`agents/tasks/LJ-1-178/lj-1.178-report.md:376-380` says "The bar changed under
me" and "I judge nothing against 0.009143 at 1.00x". It was also sent to read
a struck ruling (`lj-1.178-report.md:465`). The brief is a frozen record that
now carries a struck ruling into every future reader.

**Self-reported?** Partly. `cda4619` admits the wrong bar went to three agents,
but claims all three files are corrected. This file is not.

### F2. The struck question still sits in the live status screen. MEASURED

**The rule.** The same commit `cda4619` struck the module-rate question.

**The act.** `dev/PLAN.md:85-93` still carries a section titled "WHICH BAR
PRICES A NEW MODULE" and ends "My recommendation is the MODULE rate for a new
module". That is the exact question the owner ruled does not exist. The section
sits under the heading "WHAT IS WAITING ON THE OWNER", so it is presented as
open.

**The cost.** `dev/PLAN.md` section 0.0 is the live status screen. Every brief
points its agent at it. A reader gets the struck reading one hour after the
owner struck it. The cost is wrong-bar risk for the next module that is priced.

**Self-reported?** No.

### F3. The orchestrator's own rulebook still names the heads. MEASURED

**The rule.** DD19: nothing is canonical twice. Commit `d6ba60d` fixed PLAN's
DD17 and DD25 for exactly this, and its body states the rule: the heads were
canonical twice, "which is exactly what DD19 forbids".

**The act.** `dev/ORCHESTRATION.md` was not swept:

- `:32-37` restates both versions' heads: "leads with pi and reviews with
  in-harness Opus 5" and "leads with in-harness Opus 5 and reviews with pi".
  The heads now live twice, which is what `d6ba60d` removed from PLAN.
- `:88` says "Audit the codex return and the Opus review". Those are the
  normal-version heads, not the override heads in force.
- `:129-130` says "a codex return ... re-dispatched to Fable 5". The emergency
  tier no longer names a head, per the fixed DD17.

**The cost.** The file is the rulebook the orchestrator works to. It names
wrong heads for the DD25 read-together step and the emergency tier. This is
the C-41 shape the brief predicted would appear a fourth time: a text that
keeps reading true after the world changed.

**Self-reported?** No. The orchestrator's own `d6ba60d` commit names the
defect, but the sweep stopped at PLAN.

### F4. DD4 lapsed on 11 briefs, all on 2026-08-13. MEASURED

**The rule.** DD4 is stated in every brief, whatever the kind, and every return
answers it. Repetition is its only enforcement.

**The census.** Search: `grep -qi DD4` over every brief at
`agents/tasks/LJ-1-*/LJ-1.*.md`, then `grep -q '^## DD4'` for the section form.
86 live briefs. 74 carry a `## DD4` section. 1 mentions DD4 with no section
(`LJ-1.137`). **11 carry no DD4 at all**: `LJ-1.132`, `133`, `138`, `139`,
`140`, `141`, `142`, `143`, `148`, `149`, `157`.

The last one is the previous audit of this same orchestrator. Its brief
`agents/tasks/LJ-1-157/LJ-1.157.md` has no DD4, and its report
`agents/tasks/LJ-1-157/lj-1.157-report.md` has zero DD4 mentions. The audit of
the orchestrator's rule compliance itself dropped the rule whose only
enforcement is repetition.

**The return side.** Search: `grep -qi DD4` over every report. 8 reports carry
no DD4 answer: `126`, `128`, `129`, `130`, `135`, `141`, `148`, `157`.

**The cost.** DD4 has no checker and no metric. It survives only if it is said
out loud. It was not said on 11 briefs and 8 returns in one day. The cost is
the decay of the rule the brief itself names as the core constraint.

**Self-reported?** No. The admitted list does not mention DD4 lapses.

### F5. The DD25 enforcement point is still unmet. MEASURED, residual

**The rule.** DD25: the index row for a negative return names its review's
code.

**The act.** The four negative returns still do not name their reviews.
`dev/PLAN.md:737` (`LJ-1.162`), `:740` (`LJ-1.165`), `:744` (`LJ-1.169`),
`:747` (`LJ-1.172`) name no review code, while the reviews `LJ-1.179` to
`1.182` are registered at `:754-758`.

**The cost.** Low. The reviews are dispatched and three have returned. The
wiring is not done. This is the residue of admitted item 5, so I do not count
it as a new violation. I list it because the fix the orchestrator announced is
not complete.

### F6. A commit claims zero deletions and deletes one file. MEASURED, minor

**The rule.** The brief orders: read what a commit claims against what its diff
does.

**The act.** Commit `8bc2ae5` states "182 renames, 0 deletions".
`git show --diff-filter=D --name-only 8bc2ae5` returns one file:
`archive/probes/README.md`.

**The cost.** About nothing. The file is a README mapping old probe paths, not
code, so DD13's never-delete does not clearly bite. The claim is still false,
and the deletion is not named in the commit body.

## 2. METHOD AND COVERAGE

**Sources read whole.** `dev/PLAN.md` section 3 (every DD) and section 11 (the
task index); `dev/ORCHESTRATION.md` whole; `dev/LESSONS.md` C-39 through C-43;
`agents/tasks/LJ-1-157/lj-1.157-report.md` whole; the briefs and reports of
`LJ-1.175` through `LJ-1.182`; the four DD25 review briefs and reports.

**Mechanical sweeps.** `grep -qi DD4` over all 86 briefs and all reports (F4);
`grep -n DD27` over `agents/`, `dev/`, `scripts/` (F1, F2);
`grep -n codex/fable/opus` over `AGENTS.md` and `ORCHESTRATION.md` (F3);
`git log --since=2026-08-13 --diff-filter=D` for deletions (F6);
`git log --since=2026-08-13` commit bodies read for the window.

**Rows checked and the verdict.**

| ruling | checked | result |
|---|---|---|
| DD4 | every brief and report | lapsed, F4 |
| DD8 | build briefs `LJ-1.176`, `1.178` | the gate is named; no new violation found |
| DD13 | `git log --diff-filter=D` | one README deletion, F6 |
| DD15 | commit bodies, ledger source | no foreground `make check` found in the record |
| DD17 | every `tier:` line | heads and versions correct after the re-dispatch |
| DD18 | `scripts/check-archive-cited.py` | 37 of 86 briefs drift, already reported by `[LJ-1.157]` |
| DD19 | `check-agents-guard.py`, head-naming sweep | ORCHESTRATION.md not swept, F3 |
| DD23 | `git log` over `src/*.lagda.md` | code only, no prose added |
| DD24 | struck-figure sweep | persists in two files, F1 and F2 |
| DD25 | index rows of the four negatives | enforcement point unmet, F5 |

**Boundary.** I did not replay the full `_build/` or `archive/dev/` corpus. The
DD15 foreground/background question is not directly observable from git; I
state it as checked-by-record, not measured. The DD18 drift (37 of 86) is the
admitted C-41 finding and I did not re-litigate it.

## 3. DD4 COMPLIANCE COUNTS

Briefs: 74 of 86 carry a `## DD4` section. 1 mentions DD4 with no section.
11 carry no DD4 at all, all dated 2026-08-13.

Returns: 8 of the live reports carry no DD4 answer. They are `LJ-1.126`, `128`,
`129`, `130`, `135`, `141`, `148`, `157`.

## ARCHIVE USED (DD18)

- `dev/PLAN.md:230-271` read whole; took DD0, DD4, DD17, DD19, DD24, DD25.
- `dev/PLAN.md:505-786` read whole; took the task index rows for the four
  negative returns and their reviews.
- `dev/PLAN.md:78-100` read whole; took the struck "WHICH BAR" section (F2).
- `dev/ORCHESTRATION.md:25-135` read whole; took the head-naming lines (F3).
- `dev/LESSONS.md:3539-3800` read whole; took C-39 through C-43.
- `agents/tasks/LJ-1-157/lj-1.157-report.md` read whole; took the method.
- `agents/tasks/LJ-1-157/LJ-1.157.md` read whole; took the DD4 absence.
- `agents/tasks/LJ-1-178/LJ-1.178.md` read whole; took the struck figures (F1).
- `agents/tasks/LJ-1-178/lj-1.178-report.md:376-465`; took the bar-change cost.
- Commit bodies `cda4619`, `d6ba60d`, `8bc2ae5`, `1716971`, `eb9bf0d` read
  whole; took the rulings and the claims.

## LITERATURE (DD18)

Not this task's subject. None read.

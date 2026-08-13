# LJ-1.137 report: apply the four ruled `AGENTS.md` blocks and pay from the file's fat

STATUS: DONE. The tree is edited and unstaged. Nothing is committed.

## 1. Headline

| | words |
|---|---:|
| `AGENTS.md` final | **2,244** |
| cap, `scripts/check-dev-docs.py:105` | **2,300** |
| **headroom** | **56** |

Before this task the headroom was 43. It is now 56, and the file carries 130
words of new ruled content.

## 2. The arithmetic, verified myself

| step | words |
|---|---:|
| `AGENTS.md` at start | 2,257 |
| after the four blocks | 2,387 (+130) |
| after the six cuts | **2,244** (-143) |

**All three figures are MEASURED** with `len(text.split())`, the count that
`scripts/check-dev-docs.py:209` uses.

**The brief said +129 for the four blocks. The true figure is +130.** The
`_build` Never line is 32 words of prose, but it lands as a Boundaries bullet,
and the leading `-` is a word to `str.split()`. I did not raise the cap.

I cut 143, which is 13 above the brief's band of 110 to 130. Every one of the
six cuts is MEASURED against a canonical home that still holds the content.
The extra 13 words come from one cut, C6, whose canonical home I found only
after I had the first five.

## 3. The six cuts

### C1. The two suspended endpoint constraints (34 words)

Cut from THE ROUTE:

> Two quantitative constraints bind the double-trophy endpoint against the
> internalization route, one on lines and one on seconds, and **NEITHER binds
> until it is measured**: both are suspended and the ledger names the re-arm.

**What an agent does differently without it: nothing. MEASURED.** The sentence
says the constraints do not bind. A rule that binds nothing cannot change an
action. The content and the re-arm are at `dev/ledger.toml:690-705`
(`thresholds_suspended = true`, `thresholds_suspended_since = "2026-08-09"`,
`thresholds_rearm = "LJ-2.1 ... LJ-2.2 ..."`), and `AGENTS.md`'s own size-ledger
row points at that file. Search: `grep -n -i "re-arm\|rearm\|suspend"
dev/ledger.toml`.

### C2. "An idle agent slot is a defect" (31 words)

**What an agent does differently without it: nothing. MEASURED.** The rule is
at `dev/ORCHESTRATION.md:122` ("**An idle slot is a defect** (PLAN DD17)") and
its audit clause at `:126` ("Auditing a return is not a reason to idle"). It
also addressed the wrong reader: `AGENTS.md:117` says the orchestrator works to
`dev/ORCHESTRATION.md`, and a dispatched agent fills no slots. Search: `grep -n
-i "idle" dev/ORCHESTRATION.md`.

### C3. The nine-checker enumeration in the `make check` bullet (19 words)

Cut: "`: i18n markers, prose, Agda style, rule citations, glossary, size
ledger, the never-commit rule, whole-tree invariants, and `reuse lint``".

**What an agent does differently without it: nothing. MEASURED.** The same
sentence links `scripts/README.md`, which carries one `##` section per script,
including every checker the enumeration named. An enumeration is not a summary,
so the file's own rule "Nothing is
canonical twice ... this one summarizes" makes it fat. Search: `grep -n "^## "
scripts/README.md`.

### C4. The `tomllib` reason and the `[L3.32-T120]` history (27 words)

Cut: "The scripts need `tomllib` from Python 3.11: with an older system
`python3` the FIRST command in this file dies, and `[L3.32-T120]` lost two runs
to exactly that."

**What an agent does differently without it: nothing. MEASURED.** The action
survives in full and unweakened at the head of the same paragraph: "**Run every
`python3` command as `.venv/bin/python`**". Two lines below, the Requirements
paragraph still states "Python 3.11 or later". `[L3.32-T120]` is a closed task
in `archive/dev/TASKS-archived.md:155`.

### C5. The rules-drift history (16 words)

Cut: "Memory drifted for five days while an imported playbook sat uncited in
102 of 112 briefs."

**What an agent does differently without it: nothing. MEASURED.** The
instruction "**Never pick rules from memory.**" stays, with the command that
executes it in the same bullet. The episode is at
`dev/ORCHESTRATION.md:239-240`.

### C6. The two-caliber revocation (17 words)

Cut: "**The two-caliber rule is REVOKED** (owner, 2026-08-09): state a
projection once and say what it rests on,". The basis list is KEPT and moved up
one clause, so the paragraph now reads "**An estimate is ONE best-effort
number, and it names its basis** (`dev/PLAN.md` DD8): a probe, a delivered
comparable or a survey."

**What an agent does differently without it: nothing. MEASURED, and this is a
dead cross-reference, the brief's candidate 4.** No live document states the
two-caliber rule; `grep -rn "two-caliber"` outside `agents/` returns
`AGENTS.md` itself plus three `archive/dev/` files and nothing else. An agent
was being told that a rule it has never seen is revoked. The revocation with
its date is at `dev/PLAN.md:172` (DD8), which the surviving sentence already
cites: "**THE TWO-CALIBER RULE IS REVOKED** (owner, 2026-08-09, retiring DD7)
... a projection is stated ONCE ... with its basis named: probe, delivered
comparable, or survey."

**A prior audit found this same passage:** `agents/reports/archive/
lj-0.1-consistency.md:422`, finding D25, "`AGENTS.md` keeps the two-caliber
factors three lines before revoking them". The factors were removed later; the
revocation notice was left behind.

### Nothing on the forbidden list was touched

MEASURED against the diff: DD4 is untouched, the Never list gained a line and
lost none, the "Ask first" list is untouched, and no `file:line` or command was
removed except `[L3.32-T120]`, which is a task code and not a command.

## 4. The four blocks applied, each against its source

| # | source, verbatim | delta | site |
|---|---|---:|---|
| 1 | `agents/reports/lj-1.127-agents-diff.md:34` | +15 | `AGENTS.md:94`, one row replaced |
| 2 | `agents/reports/lj-1.130-report.md:200-201` | +34 | `AGENTS.md:104-105`, one row becomes two |
| 3 | `agents/reports/lj-1.132-report.md:346-348` | +33 | `AGENTS.md:54-56`, new Boundaries bullet |
| 4 | `agents/reports/lj-1.133-report.md:247-252` | +48 | `AGENTS.md:136-141` |

**Each text is taken from the report that proposed it, not from the brief's
summary.** I copied the strings and diffed the word counts before editing.

**Block 3 placement.** The report calls it "one line for the Never list". The
Never list is a single bullet of semicolon clauses, and the ruled text is three
sentences, so it lands as its own Boundaries bullet directly after the Never
bullet. The words are verbatim; only the leading `- ` is mine, and it is the
one word that makes the total 130 rather than 129.

**Block 2 note.** The old row also covered "probe reports", which block 4 now
routes to `archive/probes/`. The two blocks agree.

## 5. Judged fat, did not cut (C-36)

### 5.1 The nine-rule ASD-STE100 restatement (56 words), `AGENTS.md:31-35`

**This is fat by the file's own rule and I did not dare cut it.** Line 26, four
lines above, says "Each skill holds its full rule set". The file then restates
the full rule set anyway, 56 words of it, which is the exact shape the brief
named as candidate 1.

**Why I kept it. INFERRED, not measured.** The rules bind "all agent-to-agent
text, so every brief and every report", and a non-Claude harness may not load
`.claude/skills/asd-ste100/`. I did not test a codex session, so I cannot call
this MEASURED. **If the owner confirms every dispatch head can read the skill
directory, this is a clean 56 words** and it is the largest single block of fat
left in the file.

### 5.2 The P-l bullet (31 words), `AGENTS.md:129-130`

"**A measured cure does not transfer by analogy.** Re-measure it at its own
site..." **MEASURED: `dev/LESSONS.md` P-l ships in ALL FIVE `rules.py`
bundles** (build, probe, recon, rewrite, review, one hit each), and `AGENTS.md`
already orders every agent to read that bundle before writing.

**Why I kept it: it is arguable, so I list it rather than apply it**, per the
brief's third abort branch. The Working-rules section is what a dispatched
agent reads first, and this is the only place the law reaches an agent that
skips the tool. Cutting it would take the total to 174.

### 5.3 Two small ones I left

- "A rule with no enforcement point is a wish" (9 words, `:84`) restates the
  sentence before it. Cheap, and it is the file's own design principle.
- The Deployment row (20 words, `:103`) tells an agent to do nothing. It is a
  table row, and the table is the index the preamble sends readers to.

## 6. The three items NOT ruled in

**I applied none of them, and my reading of the file does not call for any.**

- `[LJ-1.130]`'s Never-list "build output" rewrite (+16). The owner is right
  that the line is not false. I add one MEASURED point in its favour: block 3
  now puts the word `_build/` in a second Boundaries bullet three lines below,
  so the section states the `_build` regime twice and the rewrite would be a
  third statement.
- `[LJ-1.130]`'s "never rewrite a brief or a report" line (+22). No enforcement
  point, and the new routing row already says "a record is never rewritten".
- `[LJ-1.132]`'s 73-word lifecycle table row. Block 3 carries the action.

## 7. Checkers, all four clean

```
.venv/bin/python scripts/check-dev-docs.py       -> check-dev-docs: clean (6 subcheck(s))          exit 0
.venv/bin/python scripts/check-agents-guard.py   -> clean (12 guarded commit(s), 30 pre-guard)      exit 0
.venv/bin/python scripts/lint-prose.py --check AGENTS.md                                            exit 0
.venv/bin/python scripts/check-rule-ids.py       -> clean (45 files, 141 lessons, 66 decisions)     exit 0
```

**C-40, one consumer beyond the four.** Block 1 names the dispatch switch, and
`check-dispatch-policy.py` gates a governed document that names a head model
without pointing at the switch. Run: `dispatch policy OK: 'override' in force,
412 brief(s) read`, exit 0.

**`CLAUDE.md` is untouched. MEASURED:** `git status --porcelain` reports
` M AGENTS.md` and nothing else in scope.

## 8. Every negative, marked

- **MEASURED.** Nothing else in the live tree states the two-caliber rule
  (`grep -rn "two-caliber"`, three archive files only).
- **MEASURED.** `dev/ORCHESTRATION.md:122-126` carries the idle-slot rule.
- **MEASURED.** `dev/ledger.toml:690-705` carries the suspended thresholds and
  the re-arm.
- **MEASURED.** P-l is in all five `rules.py` bundles.
- **MEASURED.** `scripts/README.md` documents each checker in its own section.
- **INFERRED.** A non-Claude dispatch head cannot load
  `.claude/skills/asd-ste100/`. I did not test this, and it is why 5.1 is
  uncut.

## 9. Tree state

`AGENTS.md` modified, **unstaged and uncommitted**. No other file changed. I
did not stage, commit, push, stash, reset or clean. I did not touch `src/` and
I ran no Agda.

## 10. DD4

Not applicable to this task: it changed no Agda and shares no proof code. The
DD4 bullet in `AGENTS.md` is on the do-not-cut list and is untouched.

## 11. ARCHIVE USED

- `agents/reports/lj-1.127-agents-diff.md:1-63`, read whole. Took the row at
  `:34`.
- `agents/reports/lj-1.130-report.md:185-211`, section 9. Took `:200-201`.
- `agents/reports/lj-1.132-report.md:334-353`, section 10.5. Took `:346-348`.
- `agents/reports/lj-1.133-report.md:233-256`, section 6. Took `:247-252`.
- `agents/reports/archive/lj-0.1-consistency.md:422-440`, finding D25. Took the
  history of the two-caliber passage.
- `scripts/check-agents-guard.py:1-113`, read whole. Docstring `:4-12` records
  the 2026-08-04 incident behind DD19; it is why nothing here is committed.
- `scripts/check-dev-docs.py:105-115` (the cap and its raise procedure) and
  `:207-214` (`check_agents_size`, the `len(text.split())` count).
- `dev/PLAN.md:164` and `:172` (DD8, and DD7's revocation).
- `dev/ORCHESTRATION.md:122-126`, `:239-240`.
- `dev/ledger.toml:690-705`.
- `archive/dev/TASKS-archived.md:155` (`L3.32-T120` closed).

## 12. LITERATURE

Nothing in the literature governs a rulebook.

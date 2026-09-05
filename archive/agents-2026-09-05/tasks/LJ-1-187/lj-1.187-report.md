# LJ-1.187 report: put every part of `dev/` in the place its KIND belongs

tier: pi (deepseek-subagent-mode).

## Result

**Two passages moved. 1,440 characters moved to `dev/JOURNAL.md`; `dev/PLAN.md`
net 1,150 characters smaller.** Both passages are EPISODE sitting in a document
whose kind is not episode. Nothing lost: each appears at its destination whole,
and the source keeps a pointer.

| count | what |
|---|---|
| 2 | EPISODE passages moved to `dev/JOURNAL.md` |
| 1,440 | characters moved, before |
| 1,150 | characters net removed from `dev/PLAN.md` (the two pointers cost 290) |
| 4 | canonical-twice defects found and left in place (owner rules them) |
| 1 | passage stopped on (borderline EPISODE, kept) |

Every document under `dev/` was classified. The result: the division holds.
`dev/LESSONS.md` entries are LAWs with measurements and none is an episode
without one. `dev/ORCHESTRATION.md` is RULE and its DD citations are the
operational form the DD rows name. The memos and `dev/literature/` are
REFERENCE and EPISODE in the right home, with status headers. The only
misplacements were the two PLAN passages moved, plus the canonical-twice
defects named below.

## Move table

One line per move. Characters are the exact text moved and the pointer left
behind.

| # | source | destination heading | moved (chars) | pointer left (chars) |
|---|---|---|---|---|
| 1 | `dev/PLAN.md` task-index preamble, was `dev/PLAN.md:471-484` | `dev/JOURNAL.md` "2026-08-14, `[LJ-1.187]`" -> "#### The task-index preamble, PLAN section 11" (`dev/JOURNAL.md:661`) | 1,022 | 144 (`dev/PLAN.md:467`) |
| 2 | `dev/PLAN.md` section 0.0, was `dev/PLAN.md:109-114` | `dev/JOURNAL.md` "2026-08-14, `[LJ-1.187]`" -> "#### The orchestrator habit that cost three times, PLAN section 0.0" (`dev/JOURNAL.md:678`) | 418 | 146 (`dev/PLAN.md:109`) |

Both moved blocks appear verbatim at the destination. The journal entry is one
dated entry, `2026-08-14, [LJ-1.187]`, matching the file's existing voice.

## Judgements (RULE, EPISODE, LAW, FIGURE, REFERENCE)

- **Move 1, "TWO PIECES OF EVIDENCE THE RULING IS OWED...": EPISODE.** It is a
  record of one probe's exit code, seconds and line count, and of four documents
  that carried a false claim for four days. That is the owner's own example of
  a journal entry sitting in a section header. Moved.
- **Move 2, "ONE ORCHESTRATOR HABIT THAT COST THREE TIMES...": EPISODE.** It
  records three incidents and their cost, in its own words "recorded here
  because no checker catches it". A record, not a rule. Moved. Its one rule
  sentence ("commit by explicit path, land a tool change only when no agent
  holds it") moved with it verbatim, so nothing is lost; the sentence's rule
  home, if it needs one beyond the journal, is the orchestrator's to assign.
- **The paragraphs kept around Move 1 are RULE.** "The code is
  `LJ-<phase>.<step>`" and "A phase is a barrier" define the index and stay, as
  the owner's example says. "THE ARCHITECTURE RULING SITS AT `[LJ-2.5]`" is
  RULE: it explains why phase 2 holds the reuse map and the adversarial review,
  and why two rows are marked SUPERSEDED. Kept.
- **`dev/PLAN.md` section 4, "TWO CLAUSES THIS SECTION CARRIED ARE NO LONGER
  TRUE OF THE TREE": borderline, KEPT as REFERENCE.** It carries the episode
  marker "found by `[LJ-1.149]` 2026-08-13" but its body states the part level
  and the layout as they are now, which is the pointer section correcting
  itself. Moving it would orphan the correction. A borderline passage kept is
  cheaper than one moved.
- **`dev/PLAN.md` sections 0 and 0.0: status.** The division names five kinds
  and status is not one of them. A status screen carries episodes by design and
  is rewritten, not archived. Left whole except for Move 2.

## Canonical-twice defects (found, left in place, owner rules them)

- **`dev/ORCHESTRATION.md` section 3 states DD4 twice.**
  `dev/ORCHESTRATION.md:189` ("DD4 GOES IN EVERY BRIEF...") and
  `dev/ORCHESTRATION.md:321` ("DD4, generic writing and maximum reuse, in EVERY
  brief") both carry the recon/build/stop-line clauses. The DD4 row names
  "the standing brief clause in dev/ORCHESTRATION.md section 3" as its
  enforcement point, so exactly one of the two is that clause and the other is
  a duplicate. This is the DD19 canonical-twice defect in its purest form.
- **`dev/PLAN.md` section 11, "EVERY BRIEF SURVEYS THE ARCHIVE BEFORE IT IS
  SENT...", restates DD18.** The paragraph (`dev/PLAN.md:485-494` after this
  edit) re-states the archive-survey mechanism that is DD18's row in section 3,
  with no "operational form" pointer of the kind DD17, DD18 and DD25 give to
  `dev/ORCHESTRATION.md`. It is a RULING outside its home, so it is left in
  place and named, per the brief.
- **`dev/PLAN.md` section 0 restates DD4's core constraint.**
  `dev/PLAN.md:133` ("MAXIMIZE THE CODE THE TWO PROOFS SHARE") is the status
  screen's restatement of DD4's obligation. The brief's DD4 test says any
  restatement outside the row and outside a brief is the defect; this one is
  reported, not moved, because section 0 is a status screen and the owner rules
  it.
- **`dev/PLAN.md` section 6.2 restates DD8 and the DD7 revocation
  (borderline).** "THE TWO-CALIBER DISCIPLINE IS REVOKED" and "a projection is
  now stated ONCE... and it NAMES ITS BASIS" also sit in DD8's row. Section 6.2
  is declared a live-rule section in the PLAN opening, so the overlap may be
  deliberate; named here rather than resolved.

## Passages stopped on

- **`dev/PLAN.md` section 4, the two-clause correction.** See the judgement
  above. EPISODE provenance wrapped around current REFERENCE facts; the
  division does not decide it cleanly, so it is left.
- **`dev/LESSONS.md` entry C-43** (`dev/LESSONS.md:3758`). It opens "THE RULING
  IS `dev/PLAN.md` DD0 and this entry does not restate it" and then carries the
  measured episode as the LAW's evidence. That is the correct shape: a lesson
  with its measurement, not an episode without one. Left.
- **`dev/ARCHIVE.md`, "The retirement of `archive/probes/`".** An EPISODE in
  the archive registry, but the registry is exactly where a non-module
  retirement is recorded ("it gets a record here rather than a row"). Correct
  home. Left.
- **No `dev/LESSONS.md` entry is an episode without a measurement.** Each
  entry checked carries a Measured block and a provenance pointer. The trap the
  brief names did not catch anything: the DD restatements that live there are
  C-43's explicit non-restatement and citations, not restated rules.

## Citations a move would have broken

None of the two moved passages is cited by `file:line` from any brief or
report. The frozen citations nearest the moved region are already stale from
prior `dev/PLAN.md` growth and do not point at the moved text:

- `agents/tasks/archive/GCH-COMPRESSION-AUDIT/gch-compression-audit.md:177,203,288`
  cite `dev/PLAN.md:483` for "StageArith's registered purpose"; that row is at
  `dev/PLAN.md:561` and the citation already dangled before this edit.
- `agents/tasks/archive/LJ-0-1-CONSISTENCY/lj-0.1-consistency.md:306-307` cite
  `dev/PLAN.md:460,462` for pre-renumbering row text; already stale.
- `agents/tasks/LJ-1-157/lj-1.157-report.md:229` cites `dev/PLAN.md:487-496`
  for the "EVERY BRIEF SURVEYS" paragraph, which is a range that this edit
  moves closer to its target, not further.

Every `dev/PLAN.md` edit shifts its line numbers; LJ-1.186 did the same. The
task-index rows themselves were not touched, so citations to them by content
still resolve.

## Searches run (by shape, never one spelling)

- `TWO PIECES OF EVIDENCE` and `ONE ORCHESTRATOR HABIT` across `dev/`, to
  confirm each moved passage left PLAN and landed in the journal.
- `maximize the code the two proofs share` / `MAXIMIZE THE CODE THE TWO PROOFS
  SHARE` / `write it generic` / `WRITE IT GENERIC` across `dev/*.md`, to find
  DD4 restatements outside the row and outside briefs.
- `EVERY BRIEF SURVEYS` and `ARCHIVE USED` across `dev/*.md`, to find DD18
  restatements.
- `recorded here`, `was wrong`, `paid for`, `cost three`, `never ran` in
  `dev/PLAN.md`, to sweep for episode-shaped prose by trigger word.
- `PLAN.md:10[5-9]`, `PLAN.md:11[0-5]`, `PLAN.md:47[1-9]`, `PLAN.md:48[0-4]`
  across `agents/`, `dev/`, `archive/`, to find `file:line` citations into the
  moved passages.
- The status header of every `dev/memos/*.md`, to confirm each carries a
  STATUS line and no memo holds a current RULE under a STANDING header.

## ARCHIVE USED

- `agents/tasks/LJ-1-186/lj-1.186-report.md` whole: the method, the per-row
  table, and the RULE-against-READING test I extended.
- `dev/JOURNAL.md` whole, for the voice and structure my new entry matches.
- `AGENTS.md` "Where the rules live" table whole: the specification of the
  division (ruling / episode / law / figure / term).
- `dev/PLAN.md` whole, and section 3 read to confirm what is off limits.
- `archive/dev/DECISIONS-archived.md` and `archive/dev/JOURNAL-archived.md`
  (via the D-SERIES notes and the memo status headers): how the retired series
  reads after the fact. No compression pattern came from them; the retired rows
  stay verbatim.

## LITERATURE (DD18)

Not this task's subject.

## Working tree

`dev/PLAN.md`'s two pointer edits were swept into a commit by the orchestrator
mid-task (`82dd1fb`, which also carried LJ-1.188), so the working tree shows
`dev/JOURNAL.md` modified and this report untracked, and `dev/PLAN.md` clean
against HEAD. The two PLAN pointers are present in HEAD at
`dev/PLAN.md:109` and `dev/PLAN.md:467`. Nothing else was touched.

## Checks

- `lint-prose.py --check dev/PLAN.md dev/JOURNAL.md agents/tasks/LJ-1-187/lj-1.187-report.md`: exit 0.
- `check-rule-ids.py`: clean (45 files, 145 lessons, 67 decisions).
- `check-task-index.py`: OK (491 cited codes, 503 unique rows, all within 200 characters).
- `check-dd4-stated.py`: 78 of 90 live briefs state DD4, 12 frozen pre-epoch. Unchanged by this task.
- `check-archive-cited.py`: advisory, 53 of 90 live briefs cite an archive. Unchanged by this task; no brief was touched.
- No em dash in any written file.

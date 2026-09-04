# LJ-1.716: adversarial review of LJ-1.716#1

## HEAD
head_slot: mathematician_adversarial
machine: shared

## SCOPE (write)
- agents/tasks/LJ-1-716/review-of-LJ-1-716-1.md

## THE OBLIGATION
Attack the return of LJ-1.716#1. Write agents/tasks/LJ-1-716/review-of-LJ-1-716-1.md and nothing else.
If you UPHELD the predecessor's NO-GO, that file plus exit 0 closes the
task (row sys-critic-upheld-no-go). Put `verdict: upheld` in HEAD when you
agree, or `verdict: overturned` when you do not.

## WHAT YOU READ, and where each one lives
- the newest `agents/tasks/LJ-1-716/*-report.md`
- the work brief `agents/tasks/LJ-1-716/LJ-1.716.md`
- the probes `agents/tasks/LJ-1-716/*.agda`
- the acceptance arm `agents/tasks/LJ-1-716/runs/accept-*.out`,
  newest last. It is written into THIS checkout and carries the six facts of
  the run you are attacking. Read them there.
- `dev/pod/transitions/2026-08.jsonl` for `model`, `effort`
  and `heads_sha256`. Every line carrying `"task": "LJ-1.716"` is this
  task's own history. **It is a tracked file, so an isolated worktree holds it
  at that worktree's base commit and it can end before your instance.** When
  it does, say so and use the accept arm; never infer a fact it does not carry.

## THE THREE QUESTIONS, and answer only these
These three are section 6.6's own list, at
`dev/memos/LJ-4-pod-program-design.md:2853-2858`. Your slot file gives you a
different set of FOUR as the lens you attack with. Use the four to find the
answers; write these three.

1. Does the predecessor's verdict LINE match its own BODY? The project measured
   that failure twice on 2026-08-16: `[LJ-1.375]` caught it on `[LJ-1.373]`, and
   `[LJ-1.376]` named the orchestrator's own unread live record the costliest
   defect in the tree.
2. Is every load-bearing claim backed by a `file:line` that resolves today?
3. Is the predecessor's enumeration complete?

## STANDING (program-generated, do not edit)

The records every dispatch may need. They are NOT candidates, they are not the answer to any search, and no return has to account for them. The search below spends its whole budget on what is not here.

- STANDING archive/dev/JOURNAL-archived.md
- STANDING dev/literature/truncation-and-selection.md
- STANDING dev/literature/devlin-II5.md
- STANDING dev/literature/digest.md
- STANDING archive/dev/LJ-dispatch-index.md
- STANDING archive/dev/JOURNAL.md
- STANDING dev/literature/terms-2026-08.md
- STANDING dev/ARCHIVE.md
- STANDING dev/literature/geology.md
- STANDING archive/dev/DECISIONS-archived.md

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 28.659)
- CANDIDATE archive/dev/DD-archived.md  (score 27.935)
- CANDIDATE archive/dev/PLAN-archived.md  (score 27.430)
- CANDIDATE archive/dev/measurements/README.md  (score 21.994)
- CANDIDATE archive/dev/README.md  (score 21.018)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/BIBLIOGRAPHY.md  (score 6.092)
- CANDIDATE dev/literature/devlin-errata.md  (score 5.321)
- CANDIDATE dev/literature/primary-sources.md  (score 4.825)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 3.043)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 2.651)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.


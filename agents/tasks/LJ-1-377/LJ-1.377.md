# LJ-1.377: an enforcement point for the detour kind that has none

tier: pi (pi-subagent-mode), model `glm-5.3`. **I ran
`scripts/dispatch/dispatch_policy.py` before writing this line and took the
head it gave.** No Agda. **RECON, and it may become a small build. Read the
abort criterion before you decide which.**

## WHAT FUNDS THIS

**`[LJ-1.376]` was the owner's audit of the orchestrator.** It returned
**thirteen detour episodes**, and its lead is the reason you exist:

> **The dominant kind is NONE of the three named kinds. It is the
> orchestrator's own LIVE record not read**, which caused **8 of the 10
> overturned DD25 reviews** and the **four costliest episodes**.

**Its costliest single case: ten dispatches re-derived a price that stood on
`dev/PLAN.md` section 0.0 the whole time** (`dev/JOURNAL.md:1002`).

**And the gap it named without filling:** the cure for that case **exists only
as a sentence in `dev/JOURNAL.md:1026-1029` with NO enforcement point.**
**`AGENTS.md` says a rule no machine enforces must NAME its enforcement point,
and that a rule with none is a wish.**

**Read `agents/tasks/LJ-1-376/lj-1.376-report.md` WHOLE, FIRST. Its thirteen
episodes are your evidence base and this brief does not restate them.**

## THE INSTRUCTION, and the constraint on it

**Derive an enforcement point FROM THE THIRTEEN EPISODES.** **Not from first
principles, and NOT from my framing.**

**DO NOT TRUST THE ORCHESTRATOR'S JUDGEMENT HERE.** `[LJ-1.376]` measured that
my guess about this defect was **convenient for the person being audited** and
did not survive the evidence. **I am the subject of the defect you are
designing against.** **If you find yourself adopting a frame I supplied, stop
and check it against an episode.**

**So this brief deliberately proposes nothing.** **Ask instead:**

- **Which of the thirteen would a mechanism have caught, and at what moment?**
  **At brief-writing, at dispatch, at return, or at commit?** **The four
  surfaces have very different costs and only one of them is cheap.**
- **What did each missed record have in common?** `dev/PLAN.md` section 0.0,
  a task-index row, a `dev/JOURNAL.md` entry, a sibling report. **If they
  share a shape, a checker can look for it. If they do not, say so.**
- **Is「read the live record」even checkable?** **`[LJ-1.358]` measured the
  parallel case honestly: DD18's decay was LEGAL under its own clause, and no
  machine could see it.** **The same answer may be true here, and it is a
  legitimate return.**

## WHAT THE PROJECT ALREADY HAS, so you do not rebuild it

**Three enforcement points landed TODAY and you should study their shapes
rather than invent a fourth style:**

- **`scripts/gate/check-premises-stated.py`**: a TRIGGER TABLE plus an EPOCH.
  A brief carrying a trigger token must declare its premises with a basis at
  `file:line`. **Tuned against the record: the raw token list fired on 118 of
  118 briefs and was cut back, because a gate that fires on everything trains
  pasting.**
- **`scripts/gate/check-dd18-survey.py`**: gates the RETURN side and only
  PRINTS on the brief side, because a count is gamed the moment it gates.
- **`scripts/gate/check-baseline-home.py`**: derives what it guards from the
  data rather than hardcoding it.

**Say which shape fits, or that none does.**

## THE ABORT CRITERION (D-1)

- **A MECHANISM EXISTS AND IS CHEAP.** **Then this task becomes a small build:
  write it, wire it into `make check`, give it an epoch, and report its live
  numbers.** **Best.**
- **A MECHANISM EXISTS BUT IS EXPENSIVE OR NOISY.** **Then STOP at the design
  and price it.** **Do not land a gate that fires on everything; that is the
  measured failure mode of this class.**
- **NOTHING MECHANICAL WORKS.** **Then say it plainly and name the REVIEW STEP
  that must carry the rule, in words a brief can be written from.** **A named
  review step is a legitimate enforcement point; a wish is not.** **This is
  the honest answer for DD18's brief half and it may be the honest answer
  here.**
- **THE DEFECT IS NOT WHAT `[LJ-1.376]` SAYS.** **You are allowed to disagree
  with the audit, with evidence.** **It opened 17 of 283 task directories; a
  wider read may find a different pattern.**

## CONSTRAINTS

- **If you build, you MAY create ONE checker under `scripts/gate/` and add ONE
  `Makefile` target. Nothing else.** `src/` is forbidden (I-5).
- **Do NOT edit `dev/PLAN.md`, `dev/LESSONS.md`, `dev/JOURNAL.md` or
  `AGENTS.md`.** Put any proposed text in your report; the rulings are mine
  and `AGENTS.md` is DD19-gated.
- **AN EPOCH IS REQUIRED if you gate anything**, and its scale goes in the
  code's comment, never in a commit message (C-59).
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **Do not run the full `make check`; run
  YOUR target alone and read its exit with NO PIPE** (C-59).
- **Create `agents/tasks/LJ-1-377/lj-1.377-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check`. **No em dash.**
  ASD-STE100. **Evidence is `file:line`, and for a rate, the command.** Mark
  every negative **MEASURED** or **INFERRED**.

## PREMISES

- **The dominant detour kind is the live record unread**, at
  `agents/tasks/LJ-1-376/lj-1.376-report.md:1`.
- **Briefs caused 8 of 10 DD25 overturns and the reviewer 0**, at
  `agents/tasks/LJ-1-211/lj-1.211-report.md:21`.
- **The costliest case re-derived a price standing in section 0.0**, at
  `dev/JOURNAL.md:1002`.
- **Its cure has no enforcement point**, at `dev/JOURNAL.md:1026-1029`.

**Mark each VERIFIED or REFUTED at `file:line`.**

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Every framing in this brief comes from an audit of me, written because the
owner judged my foundations weak in a specific way that day.** **The one at
risk: that this defect is mine PERSONALLY rather than STRUCTURAL.** **If it is
structural, meaning any orchestrator writing briefs against a 690-row index
would miss the same rows, then the cure is a tool and not a discipline, and
that changes what you should build.** **`[LJ-1.376]` did not ask this.** **Ask
it.**

## THE RULES

**DD19: a rule that no machine enforces must NAME its enforcement point, and a
rule with none is a wish.** **C-59: a gate you do not run is worth what a gate
you do not have is worth.** **C-48: a policy that only a document states is
not enforced.** **C-28: a stale figure reports exactly like a live one.**
**C-45, C-57, D-10, C-42, C-44, C-53, P-l, P-k.**
**C-22, C-32, C-36, C-39, C-40.** I-5. **D-1, D-26.**
**DD0, DD4, DD18, DD19, DD23, DD25, DD28.**

Run `.venv/bin/python scripts/dispatch/rules.py --for recon` and read every
statement.

## DD4

**Maximize the code the two proofs share, and write it generic.** **NAME YOUR
AXIS** (C-46). **Your axis is not the two towers; say so plainly rather than
force the section.** **What IS live: every detour spends budget the two
trophies need, and `[LJ-1.376]` priced the worst single episode at about two
dispatches.**

## ARCHIVE (DD18)

**`scripts/gate/check-dd18-survey.py` GATES your return: name each of the four
corpora, cited or declined in ONE line, and QUOTE one line per archived file
you read, at its real line number.**

- **`archive/dev/JOURNAL-archived.md`**: **did the RETIRED route lose work to
  its own unread record?** **If a predecessor made this mistake, the case for
  a tool rather than a discipline is much stronger.**
- **`archive/dev/TASKS-archived.md`**: 265 rows. **The retired route ran a
  task index too; did anything enforce reading it?**
- **`archive/dev/DECISIONS-archived.md`**: any ruling on reading the record
  before dispatching.
- **`archive/src/2026-08-09-rud-route/`**: **nothing bears on process. Say so
  in one line naming what you checked.**

## LITERATURE (DD18)

**MEASURED THREE TIMES: nothing in `dev/literature/` bears on process
mechanisms** (`[LJ-1.356]`, `[LJ-1.357]`, `[LJ-1.371]`). **Cite that and move
on.** Return a **LITERATURE USED** section saying exactly that.

## SCOPE (read)

`agents/tasks/LJ-1-376/lj-1.376-report.md` WHOLE, FIRST. It is the evidence
base and this task has no other.

## SCOPE (write)

`agents/tasks/LJ-1-377/`, and IF you build: one checker under
`scripts/gate/` plus one `Makefile` target.

## RETURN

**Lead with ONE line: is there an enforcement point, and did you build it or
price it.** Then which of the thirteen a mechanism would have caught and at
which of the four moments. Then what the missed records had in common, or that
they had nothing. Then whether the defect is personal or structural. Then, if
you built, the live numbers and the epoch. **Mark every negative MEASURED or
INFERRED.**

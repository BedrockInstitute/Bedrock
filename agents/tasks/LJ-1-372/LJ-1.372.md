# LJ-1.372: land `[LJ-1.371]`'s two fixes, the false red first

tier: pi (pi-subagent-mode), model `glm-5.3`. **I ran
`scripts/dispatch/dispatch_policy.py` before writing this line and took the
head it gave.** No Agda. **BUILD.**

## WHAT FUNDS THIS

**`[LJ-1.371]` measured that three defects fired today from the registry's
blindness to an in-harness dispatch, and that MY「one shared cause」premise
was FALSE: two share it, the third does not.** **Its answer is INFERENCE, not
registration:**

> **Read the tree, not the dispatcher.** A rule of「no young write in any live
> task's declared scope, and no gated report mid-write」sees an in-harness
> agent at the only moment that matters, which is when it writes.

**MEASURED on the live corpus: it caught both live agents at N=15 minutes with
ZERO false positives.** **Its false negative is the agent that stays silent,
and that silence is SAFE for a gate, because a silent agent writes nothing.**

**READ `agents/tasks/LJ-1-371/lj-1.371-report.md` WHOLE, FIRST. It is the
design and this brief only orders it built.** **Where this brief and the
report disagree, THE REPORT WINS and you say so.**

## THE ORDER IS PART OF THE INSTRUCTION

**`[LJ-1.371]` says twice that the false-red fix「needs no registry at all」
and「should land first」** (`lj-1.371-report.md:15-16`, `:139`). **Land it
first, verify it alone, and only then do the inference half.** **If the second
half turns out harder than the report priced, the first is already banked.**

## HALF ONE: the false red. No registry.

**`scripts/gate/check-dd18-survey.py` judged `[LJ-1.368]`'s report a B2
failure while the agent was still writing it, and `make check` went red on a
defect that did not exist.** **The checker HAS a「live report in progress, not
judged」path; it could not use it because it asked the registry.**

**The fix the report gives needs only the file's own mtime.** **Build exactly
what the report specifies at `:139` onward, including「give the marker a
home」if that is what it says.** **Do not invent a variant.**

## HALF TWO: tree inference in `gate-ready`. About 30 lines.

**A SECOND OPINION, not a replacement.** `cmd_gate_ready`
(`.claude/skills/codex-dispatch/dispatch.py:2218`) answers from
`running(load())` at `:2229`. **Keep that answer and ADD the inference: if
either says an agent may be live, `gate-ready` says WAIT.**

**`.claude/skills/codex-dispatch/dispatch.py` is the orchestrator's tool and
it is UNTRACKED. You MAY edit it for this half, and only for this half.**
**Touch nothing else in that file.**

## WHAT NOT TO BUILD

- **The third defect is NOT yours.** `[LJ-1.371]` found it has a different
  cause. **Read what it says and leave it alone; a fix aimed at the wrong
  cause is worse than none.**
- **Do NOT try to register in-harness dispatches.** The report measured that
  registration cannot work: no project code runs at dispatch time.
- **`AGENTS.md` is DD19-gated.** If a line is needed, write the diff into your
  report.
- **`dev/PLAN.md`: do not edit.** Give me any row text in your report.

## THE ABORT CRITERION (D-1)

- **BOTH LAND AND `make check` STAYS GREEN.** Report each half's lines, the
  N you chose and why, and the runtime. **Best.**
- **HALF ONE LANDS, HALF TWO DOES NOT.** **That is a GOOD outcome, not a
  failure. Say what stopped the second and price it.**
- **THE INFERENCE MISFIRES ON THE LIVE CORPUS.** **`[LJ-1.371]` measured zero
  false positives at N=15 with two agents live. You will run with ZERO or ONE
  live agent, which is a different test. If your measurement disagrees with
  its measurement, YOURS is the one taken today; report both.**

## CONSTRAINTS

- **You MAY edit `scripts/gate/check-dd18-survey.py` and
  `.claude/skills/codex-dispatch/dispatch.py`'s `gate-ready` path only.**
  `src/` is forbidden (I-5).
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **Do not run the full `make check`; run
  YOUR target alone and read its exit with NO PIPE** (C-59).
- **Create `agents/tasks/LJ-1-372/lj-1.372-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check`. **No em dash.**
  ASD-STE100. **Evidence is `file:line`, and for a rate, the command.** Mark
  every negative **MEASURED** or **INFERRED**.

## PREMISES

- **The false-red fix needs no registry**, at
  `agents/tasks/LJ-1-371/lj-1.371-report.md:15-16` and `:139`.
- **`cmd_gate_ready` answers from the registry alone**, at
  `.claude/skills/codex-dispatch/dispatch.py:2218` and `:2229`.
- **The inference caught both live agents at N=15 with zero false positives**,
  MEASURED by `[LJ-1.371]` on the live corpus.
- **The third defect has a different cause** and is out of scope.

**Mark each VERIFIED or REFUTED at `file:line`.**

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Eleven of my last thirty-six briefs carried a claim an agent measured FALSE,
and `[LJ-1.371]` refuted my shared-cause premise this hour.** **The one at
risk: 「about 30 lines」.** **That is `[LJ-1.371]`'s figure for a design it did
not build, and P-l says a judgement at one site is a hypothesis at another.**
**Report the real number without apology.**

## THE RULES

**C-59: a gate you do not run is worth what a gate you do not have is worth,
and its sibling is this task: a gate that cannot SEE is worth the same.**
**C-48, C-45, C-28, C-57, D-10, C-42, C-44, C-53, P-l, P-k, P-h, P-m, P-n,
R-35, R-38, R-40.** **C-22, C-32, C-36, C-39, C-40.** I-5. **D-1, D-26.**
**DD0, DD4, DD17, DD18, DD19, DD23, DD24, DD25.**

Run `.venv/bin/python scripts/dispatch/rules.py --for build` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker. **NAME YOUR AXIS** (C-46).

**Your axis is not the two towers; say so plainly rather than force the
section.** **What IS live: two gates commissioned TODAY to protect DD18 and
DD24 both inherited this blindness, and both serve DD4's own instruments. A
blind gate reports the DD4 relationship wrongly and does so silently.**

## ARCHIVE (DD18)

**`scripts/gate/check-dd18-survey.py` GATES your return, and you are editing
it, so meet its own rule exactly: name each of the four corpora, cited or
declined in ONE line, and QUOTE one line per archived file you read, at its
real line number.**

- **`archive/dev/JOURNAL-archived.md`**: **`[LJ-1.371]` searched here for lost
  returns and unwatched agents. Cite what it found, or decline in one line.**
- **`archive/dev/DECISIONS-archived.md`**: any ruling on dispatch tooling.
  **WHY NOT in one line if none bears.**
- **`archive/dev/TASKS-archived.md`**: dispatch-tooling dispatches.
- **`archive/src/2026-08-09-rud-route/`**: **nothing bears on dispatch
  tooling. Say so in one line naming what you checked.**

## LITERATURE (DD18)

**MEASURED THREE TIMES NOW, by `[LJ-1.356]`, `[LJ-1.357]` and `[LJ-1.371]`:
nothing in `dev/literature/` bears on process mechanisms.** **Cite that and
move on.** Return a **LITERATURE USED** section saying exactly that.

## SCOPE (read)

`agents/tasks/LJ-1-371/lj-1.371-report.md` WHOLE, FIRST, and especially `:139`
onward, which is the fix you are building.

## SCOPE (write)

`scripts/gate/check-dd18-survey.py`,
`.claude/skills/codex-dispatch/dispatch.py`'s `gate-ready` path, and
`agents/tasks/LJ-1-372/`.

## RETURN

**Lead with ONE line: did half one land, and did half two.** Then each half's
real line count against the report's figures. Then the N you chose and the
measurement behind it. Then your own false positives and negatives, measured
today. Then anything the report specified that you could not build. **Mark
every negative MEASURED or INFERRED.**

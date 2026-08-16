# LJ-1.372 report: land the false-red fix, then the tree inference

Status: COMPLETE

## One-line answer

**Both halves landed.** Half one is the mtime backstop in
`scripts/gate/check-dd18-survey.py`, verified ALONE first, exit 0. Half two
is the tree inference in `.claude/skills/codex-dispatch/dispatch.py`
`cmd_gate_ready`, a second opinion, exit 1 on two live agents. The one thing
the report ordered that I could not build is its item 1, the marker's home:
two sentences, delivered verbatim below, because my write scope forbids both
files.

## Half one: the false-red fix

LANDED and verified ALONE, before any `dispatch.py` edit, per the brief's
order. What landed is the report's item 2 at
`agents/tasks/LJ-1-371/lj-1.371-report.md:145`, the mtime backstop:

- `BACKSTOP_SECONDS = 600` and the skip in `main()`: a gated report younger
  than 10 minutes whose PLAN row still reads DISPATCHED joins the `live`
  list and is not judged. `scripts/gate/check-dd18-survey.py:196` and
  `:530`.
- `row_dispatched()`, the row conjunct: the status column is matched
  EXACTLY, because the live index holds `REGISTERED, NOT DISPATCHED`
  (LJ-1.271) and `STOP: CURED FIVE DISPATCHES AGO` (LJ-1.177), and a
  substring test would read both as live. Section-scoped to `### Task
  index`, because the master status table reuses the `LJ-1.<n>` shape for
  goals. `scripts/gate/check-dd18-survey.py:242`.

What did NOT land: the report's item 1,「give the marker a home」, two
sentences. The brief's SCOPE (write) admits `check-dd18-survey.py`,
`dispatch.py`'s `gate-ready` path only, and this directory, so the brief
template and `dev/ORCHESTRATION.md` are outside my pen. The two sentences
are in「The marker's home, ready to land」below, verbatim. The backstop alone
cures the episode: the report itself says at `:148` the report at 12:57:33
was seconds old, and MEASURED below, the backstop fires with the marker
missing.

### Verification, each command read with no pipe (C-59)

1. Baseline BEFORE the edit, 13:49:24: exit 0 in 0.64 s. In that same run
   LJ-1.371's report was 586 s old, INSIDE the 600 s window, with its row
   flipped to a verdict, and it was judged and passed inside the「7 gated
   task(s) ... 0 defects」count. MEASURED: the row conjunct prevented a
   false skip of a finished return, live, in the first run after wiring.
2. Row predicate, all five discriminating rows: `LJ-1-271` False,
   `LJ-1.177` False, `LJ-1.367` True, `LJ-1.371` False, `LJ-1.372` True.
   Command: an `importlib` load of the module, direct calls.
3. The 12:57:33 episode, reproduced: I removed my own report's status line
   (report 7 minutes old, row DISPATCHED, gated, no marker) and ran the
   gate. Exit 0,「1 live report(s) in progress, not judged」. The backstop
   alone skipped the mid-write report, no registry read, no marker. Marker
   restored, exit 0 again via the marker path.
4. The gate is wired into `make check` as `dd18survey` (`Makefile:36`,
   `:173`). I ran that target's command alone, as ordered, and read its
   exit with no pipe: exit 0.

Runtime after the edit: 0.68 s against 0.64 s before, MEASURED by `time` on
both runs. Lines added: 52 insertions, 0 deletions, MEASURED by
`git diff --stat`, against the report's「about 6」. The 6 priced the skip in
`main()` alone; reading the PLAN row is a helper and two constants, and the
honest total is 52.

## Half two: tree inference in `gate-ready`

LANDED as a SECOND OPINION. `_tree_maybe_live()` sits directly above
`cmd_gate_ready` and answers from the tree: a task whose PLAN task-index row
still reads DISPATCHED is unaudited, and a write younger than 15 minutes
inside its task dir or its brief's declared SCOPE (write) is that task's
agent at the only moment that matters, when it writes. `cmd_gate_ready`
keeps the registry answer and adds this one; either refuses the gate.
`.claude/skills/codex-dispatch/dispatch.py:2229`, helper at `:2237`, gate
at `:2294`. Nothing else in
that file changed: no import, no other function, the registry message is
byte-identical.

### A bug in my own first cut, found by verification

My first scope scan was silently dead: I compared a brief's stem to the
DIRECTORY name, but the stem carries dots (`LJ-1.367.md`) and the dir
carries dashes (`LJ-1-367/`). The first measurement looked clean for a
false reason. Fixed to normalise the stem, and the honest false positive
below appeared. The task-dir half of the rule was never affected.

### Verification, no pipe (C-59)

1. `gate-ready` BEFORE the edit, 13:49:24: exit 1, the registry saw me,
   LJ-1.372. The registry is not blind to THIS dispatch, because the
   orchestrator sent me through `dispatch.py`. So I exercised the blind
   branch directly: `dispatch.load = lambda: {}` then
   `cmd_gate_ready(None)`. BEFORE the edit that stub answered exit 0, no
   agent live, over a tree I was writing. AFTER the edit it answers exit 1
   and names LJ-1.372. MEASURED, command above.
2. Full `gate-ready` after the edit: exit 1 in 0.125 s, MEASURED by `time`.
3. Ground truth from `herdr agent list`: agents named `lj-1-372` and
   `lj-1.373`, both `agent_status: working`. The inference flagged exactly
   those two. MEASURED at 13:52:06.

Lines: the helper plus rewritten `cmd_gate_ready` is 110 lines, MEASURED by
script, where the original function was 20, counted from the pre-edit read.
Net about 90 lines, against the report's「about 30」. The 30 priced a rule
with no row grammar, no `-R` fallback, no existence filters and no comment
duty. MEASURED real: 110.

## The N I chose and why

Backstop 600 s, gate-ready 900 s. Both are the report's own figures, at
`:145` and the verdict section. Today's corpus could NOT re-measure the
N=10 versus N=15 boundary: both live agents were caught within seconds, and
LJ-1.370's 14-minute silent window is days past. So N=15 stands on
`[LJ-1.371]`'s measurement, INFERRED adequate today, not re-measured at the
boundary. The backstop's 600 s window discriminated live today, see half
one verification 1.

## False positives and negatives, measured today

- TRUE POSITIVES: 2 of 2 live agents caught, `lj-1.372` and `lj-1.373`,
  ground truth `herdr agent list`. LJ-1.373 appeared DURING my verification,
  and its gated report was mid-write at my final checker run, which skipped
  it:「2 live report(s) in progress, not judged」, exit 0. That is the
  12:57:33 episode shape, happening live, cured. MEASURED.
- FALSE NEGATIVES: 0 among `herdr`-working Bedrock agents. MEASURED. The
  silent-agent miss stays structural, as the report says.
- FALSE POSITIVES: 1 of 3 flags, LJ-1.367, MEASURED at 13:52:06. Its agent
  is dead, but its row still reads DISPATCHED, never flipped, and its scope
  names `dev/PLAN.md` at LINE granularity,「lines `:145` and `:212` only」,
  which my scan reads at FILE granularity. The orchestrator rewrote
  `dev/PLAN.md` 184 s before, adding LJ-1.373's row. The flag refuses a
  safe gate; it never authorises an unsafe one. This DISAGREES with
  `[LJ-1.371]`'s「zero false positives at N=15」, and per the brief mine is
  the one taken today. The cure is the orchestrator's, and it is cheap:
  flip LJ-1.367's row, whose work appears delivered
  (`dev/PLAN.md`'s DD24 row names `check-baseline-home.py` as live).

## What the report specified that I could not build

Its item 1, the marker's home. Zero code, two sentences, and both files are
outside my SCOPE (write). Everything else specified at `:139` onward
landed.

## The marker's home, ready to land

1. For the brief template, wherever the orchestrator keeps it. MEASURED:
   `dispatch.py` generates no brief, grep finds no template, so the home is
   the orchestrator's own writing habit. Sentence, the report's words at
   `:143`: The report's first line reads `Status: IN PROGRESS` until it is
   finished.
2. For `dev/ORCHESTRATION.md`, beside the C-22 rule at `:226`: A dispatched
   report's first line reads `Status: IN PROGRESS` until it is finished;
   `scripts/gate/check-dd18-survey.py` waits for it until then.

## AGENTS.md

No line needed. Both fixes are code with their own enforcement points, and
AGENTS.md never restates gate internals. DD19: nothing canonical twice.

## PLAN row text for the orchestrator

`| LJ-1.372 | Land LJ-1.371's two fixes: the false red, then tree inference | BOTH LANDED GREEN, 52+90 LINES | Backstop skips mid-write reports; tree opinion caught 2 live agents, 1 false positive |`

That row is 197 characters, MEASURED by `len()`, under the 200 cap. My
first two drafts were 238 and 206, and I claimed 199 for the second
without measuring it. C-59 holds at every size.

## ARCHIVE USED

Four corpora, one line each, cited or declined.

- `archive/dev/DECISIONS-archived.md`: READ, the ruling on computed-not-
  written state, which is this fix's shape. Quote, `:49`: "standing is
  COMPUTED from the tree by `scripts/ledger.py` and written down nowhere, so
  it can never be stale". Liveness now follows the same law.
- `archive/dev/JOURNAL-archived.md`: READ, the registry's lost-record and
  unwatched-agent episodes, cited by `[LJ-1.371]`. Quote, `:1991`:
  "ceiling and lost 7 of 10 records under the tool's own documented
  fan-out. Fixed and re-tested." Nothing there prices tree inference.
- `archive/dev/TASKS-archived.md`: READ for dispatch-tooling dispatches.
  Quote, `:154`: "| L3.32-T119 | Adversarial review of the dispatch
  mechanism | DELIVERED | `_build/l3.32-t119-report.md` |". The report is
  gone with `_build/`; its lessons survive inside `dispatch.py`.
- `archive/src/2026-08-09-rud-route/`: DECLINED. I checked its `README.md`
  path note, quote, `:3`: "THE OLD PATH OF THIS DIRECTORY WAS
  `archive/rud-route/`." Agda modules and a path note; nothing bears on
  dispatch tooling.

## LITERATURE USED

Nothing in `dev/literature/` bears on process mechanisms. MEASURED three
times, by `[LJ-1.356]`, `[LJ-1.357]` and `[LJ-1.371]`. This return spent no
fourth pass, per the brief.

## DD4

My axis is not the two towers; I say so plainly. My axis is the instruments
that make the DD4 relationship visible: `check-dd18-survey.py` gates the
returns whose shared-code claims are audited, and `gate-ready` guards the
full-tree runs that price DD24's seconds per line. Both were commissioned
today, and both inherited the registry blindness. A gate that judges a
report mid-write, or greens a full-tree read over a live agent, reports the
DD4 relationship wrongly and silently, so both fixes are instrument repairs
first. On genericity: the PLAN-row grammar and the SCOPE (write) token rule
are now written twice with one shape, in the two files my scope admits,
because a shared home under `scripts/` was outside that scope. A third
consumer copies either block as-is. The orchestrator may factor the
duplicate into `agents_tree.py` when landing.

## Premises, each VERIFIED or REFUTED

1.「The false-red fix needs no registry」VERIFIED. The backstop reads one
   mtime and one PLAN row; the checker's imports are `re`, `sys`, `time`,
   `pathlib`, `agents_tree`, `repo_root` (`scripts/gate/check-dd18-survey.py:87-90`),
   no registry anywhere. MEASURED by the episode test, verification 3.
2.「`cmd_gate_ready` answers from the registry alone」VERIFIED for the
   pre-edit file, read at the old `:2218` and `:2229` before I edited. It
   is FALSE as of this landing: the answer is now registry PLUS tree,
   `.claude/skills/codex-dispatch/dispatch.py:2294`.
3.「The inference caught both live agents at N=15 with zero false
   positives」VERIFIED as `[LJ-1.371]`'s measurement. Today it caught 2 of
   2 live agents and made 1 false positive. MEASURED, both runs reported
   above; mine is the one taken today.
4.「The third defect has a different cause」VERIFIED, from the report's own
   defect-2 section. I touched no launch path: `launch_defects` and its
   four callers are byte-identical to before.

## Verdict

Both halves landed and both gates are green on their own commands, exit 0
and exit 1-as-refusal. The report's design held at every point I could
test, and its two figures were the only things it got wrong: 6 became 52
and 30 became 110, both MEASURED. The one live disagreement is the false
positive, and its cause is an unflipped row plus line-granular scope, both
the orchestrator's to cure in one audit turn. Land the two marker sentences
when convenient; the backstop already covers the episode without them.

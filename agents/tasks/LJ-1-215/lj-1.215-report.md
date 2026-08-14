# LJ-1.215 report: DD25 review of three negatives

**STATUS: COMPLETE.** Written incrementally under C-22, section by section. I
edited no master, no brief and no report. I ran no Agda. I committed nothing and
pushed nothing. `scripts/lint-prose.py --check` on this file is CLEAN.

**Head: the in-harness Opus 5, the switch's ADVERSARIAL row. All three targets
were written by pi, so DD17's invariant holds: the critic is not the author.**

## 0. THE THREE VERDICTS

**In three words: UPHELD. UPHELD. MISATTRIBUTED.**

| target | its verdict | mine |
|---|---|---|
| `[LJ-1.209]` 「THE SEAL DOES NOT REACH: 83 ms」 | correct | **UPHELD** |
| `[LJ-1.206]` 「DOES NOT HOLD, NOTHING LANDED」 | correct | **UPHELD** |
| `[LJ-1.198]` 「A WALL, NOT A NUMBER」 | half correct | **UPHELD BUT MISATTRIBUTED** |

**Two of three hold on their own numbers. The third holds on its conclusion and
fails on its cause, and the orchestrator named the right target in advance.**

**The one sentence per target:**

- **`[LJ-1.209]`.** Every figure reproduces from the raw runs. Its one design
  flaw runs against its own conclusion, so the negative is conservative.
- **`[LJ-1.206]`.** The conclusion is verifiable without the socket, and the
  record already holds the measurement the report filed as open. **But the report
  lost its probe.**
- **`[LJ-1.198]`.** A6 is UNPRICED, not WALLED. The bisection's control has no
  reported time, its bounds shrink as it narrows, and a sixth probe was run and
  dropped from the record.

## 1. `[LJ-1.209]`: UPHELD

**Verdict: UPHELD. The refusal is correct on its own numbers, and I re-derived
every number from the raw runs rather than from the report's tables.**

### 1.1 Question 1: is the refusal correct on its own numbers?

**YES. Every figure reproduces exactly from `agents/tasks/LJ-1-209/runs/`.**

| figure the report states | source I opened | my re-derivation |
|---|---|---|
| plain 10,020 / 9,774 / 9,289 | `runs/ProbePlain.p1.txt`, `.p2.txt`, `.p3.txt` | identical |
| seal 9,782 / 9,401 / 9,650 | `runs/ProbeSeal.s1.txt`, `.s2.txt`, `.s3.txt` | identical |
| plain mean 9,694 ms | 29,083 / 3 | 9,694.3 ms |
| seal mean 9,611 ms | 28,833 / 3 | 9,611.0 ms |
| the seal buys 83 ms, 0.86 percent | 9,694 minus 9,611 | 83 ms, 0.856 percent |
| plain own spread 7.5 percent | 731 / 9,694 | 7.54 percent |
| seal own spread 4.0 percent | 381 / 9,611 | 3.96 percent |
| trivial mean 9,448 ms | `runs/ProbeTrivial.t1-t3.txt` | 9,448.3 ms |
| plain mean series 2, 9,401 ms | `runs/ProbePlain.q1-q3.txt` | 9,400.7 ms |
| the content costs 47 ms the wrong way | 9,448 minus 9,401 | 47 ms, trivial is slower |
| rung 1, 1,165 ms | `runs/ProbeMinusArNum.r1.txt` | 1,165 ms, exit 0 |
| the term is 8,236 ms | 9,401 minus 1,165 | 8,236 ms |

**All 14 raw files carry `# exit 0` and a load header before and after. The load
spike to 26.04 that the report declares is real: it is written in
`runs/ProbePlain.p1.txt` as the load AFTER p1 and in `runs/ProbeSeal.s1.txt` as
the load BEFORE s1. The report did not hide it.**

**The site count reproduces too. I re-ran the sweep by shape:**

| the report's claim | my count over `src/` |
|---|---:|
| `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` | 57 |
| `∥ Σ[ n ∈ ℕ ] (fst N ≡ # n) ∥₁` | 6 |
| total type occurrences | **63** |
| `src/L/Condensation.lagda.md` | 46 |
| `src/L/Condensation/TwelveAgree.lagda.md` | 7 |
| `src/L/Condensation/UpperAgree.lagda.md` | 5 |
| `src/L/Condensation/LowerAgree.lagda.md` | 5 |
| the literal name `arNum` | 20 |

**So「a handful」and「about 420 ms per field」are refuted on the count alone.**

### 1.2 Question 2: is the measurement sound?

**YES, with one design flaw that the report states itself, and the flaw runs
AGAINST the report's own conclusion.**

**The flaw.** Series 1 ran plain first and seal second in all three pairs
(`agents/tasks/LJ-1-209/runs/series.log`). The machine was decaying from the
26.04 spike through the whole series. **So the running order gave the seal the
quieter half of every pair.** The report says this at
`agents/tasks/LJ-1-209/lj-1.209-report.md:220-222`.

**The report's repair is not a repair, and I say so.** Line `:222` says「Series 2
reverses the order for exactly that reason, and its result is the same」. **Series
2 contains NO seal arm.** Its arms are trivial and plain
(`agents/tasks/LJ-1-209/runs/series2.log`). **The seal was never re-run in
reversed order.**

**This does not overturn the verdict. It strengthens it.** The bias favoured the
seal, and the seal still bought only 83 ms of 8,236 ms. **A bias in the cure's
favour that still shows no cure is a conservative negative.**

**The sign flip is real and I checked the pairing.** Pair 1: 10,020 against
9,782, seal faster by 238. Pair 2: 9,774 against 9,401, seal faster by 373. Pair
3: 9,289 against 9,650, seal SLOWER by 361. **Three pairs, signs minus, minus,
plus.**

**The band is quoted correctly but cited at the wrong lines.** The report and
the `[LJ-1.209]` brief both cite `scripts/check-ratio.py:72-76` for both halves
of the band. **The between-series 12.8 percent is at `scripts/check-ratio.py:75`
and `:80`. The within-series 0.5 to 4.0 percent is at
`scripts/check-ratio.py:81-83`, outside the cited range.** The figures are right;
only the line range is short. **This is a citation defect, not a measurement
defect.**

**The seal control is real, and I certified the report's certification.**
`agents/tasks/LJ-1-209/ProbeOpaqueReal.agda:30-31` holds the red half, commented
out. The report quotes Agda's refusal at `:31.19-20`. **Column 19 of line 31 with
the comment marker removed is the final `p` of `sealed→open n p = p`. The quoted
position fits the file exactly, so the red half really ran.**

**One wording error, and it does not move the verdict.**
`agents/tasks/LJ-1-209/lj-1.209-report.md:54-55` says ProbeSeal typechecks「with
NO `unfolding` line anywhere」. **There is one, at
`agents/tasks/LJ-1-209/ProbeSeal.agda:7008`: `unfolding satGraphAt`.** It is
pre-existing. The identical line stands at `ProbePlain.agda:7001`,
`ProbeTrivial.agda:7010` and in the master at
`src/L/Condensation.lagda.md:7028`. **The substantive claim holds: `unfolding
isNumeral` appears nowhere in the tree or in any probe. The seal needed no
proof-site work.** The report should have written「no `unfolding isNumeral`」.

### 1.3 Question 3: did the brief cause the outcome?

**NO. This is the one target of the three where the brief did not shape the
answer.**

**The brief named the exact failure mode as a first-class outcome:**
`agents/tasks/LJ-1-209/LJ-1.209.md:71-73` writes「THE SEAL DOES NOT REACH」into
the abort criterion and calls it「a complete answer」. **A brief that funds its
own refutation cannot be accused of causing the refutation.**

**The brief also supplied the instrument that made the negative honest:**
`agents/tasks/LJ-1-209/LJ-1.209.md:83-94` fixes the within-series paired design,
requires the load beside every absolute figure, requires a discarded warm-up and
requires three kept runs. **The agent did all four.**

**Against `[LJ-1.211]`'s largest cause,「the brief fixed a method that could not
answer the question」: the method here could answer it, and it did.** The brief
also gave a clock cap at `:76-79`, thirty minutes on one invocation. **The
longest invocation was 142.94 s, in `runs/ProbePlain.p1.txt`. The cap was never
approached.**

### 1.4 Question 4: is there a cure the return missed?

**YES, and it follows from the report's own strongest measurement.**

**What I found that the report did not count.** I diffed the two ends of the
ladder: `agents/tasks/LJ-1-209/ProbePlain.agda` against
`agents/tasks/LJ-1-204/ProbeMinusArNum.agda`. **The revert removes 152 lines.
Only 46 of them carry the numeral spelling, and only 20 carry the name
`arNum`.** The imports are byte-identical in both arms; only their line numbers
move.

**So about 106 removed lines are NOT the numeral component.** 32 of them carry
`lookup K`. The shape is visible at `ProbePlain.agda:3661-3662` against
`ProbeMinusArNum.agda:3655`: the reverted `envInK` takes `z` as an ordinary
telescope name, and the current `envInK` takes an extra `⟨ fst ar ∈ fst (lookup
K γ) ⟩` hypothesis before it.

**This CONFIRMS the report's own OPEN item at
`agents/tasks/LJ-1-209/lj-1.209-report.md:370-374` and prices it.** The report
says rung 1 reverts a 77-line commit and that its probes cannot separate the two
causes. **My count says the numeral component is 46 of 152 removed lines, so it
is a MINORITY of the reverted surface. The report understated how much of rung 1
is not `arNum`.**

**THE CURE THE REPORT MISSED, and I mark it INFERRED because I ran nothing.**
The trivial arm measures that a telescope component's CONTENT is free and its
PRESENCE is not. **So the axis to attack is the component COUNT, never the
component's spelling.** A candidate: bundle the conjuncts that `c8a628b` added at
each site into ONE named component, so each site carries one conjunct instead of
three or four.

**And I state the evidence AGAINST my own candidate, because a cure named
without its counter-evidence is a wish.** `ProbeSeal` and `ProbeTrivial` already
replace a spelled-out conjunct with a single defined head, `isNumeral (fst ar)`,
and both read flat. **A defined head did not cost less than the spelling it
replaced.** So bundling may buy nothing. **It is a hypothesis with a probe, not a
price (DD8).**

**The report's own named next probe is the right first move and I do not
displace it.** `agents/tasks/LJ-1-209/lj-1.209-report.md:375-393` prices a fourth
arm that DELETES the numeral component, at 71 edits and about 12 minutes of
Agda, and it names the trap: `ProbeTrivial.agda:6920-6921` and `:7019-7021` bind
a different `ks` from `graphWitK`. **I checked that the trap is real by reading
the file. The five projection lines it names are `ProbeTrivial.agda:5809`,
`:5810`, `:5885`, `:6277` and `:6322`.**

### 1.5 The classification

**MEASURED.** Every negative in
`agents/tasks/LJ-1-209/lj-1.209-report.md:404-423` that is marked MEASURED is
backed by a raw run file I opened. **The two it marks INFERRED are correctly
marked: the 8.2 s attribution to a single component, and the DD4
re-instantiation figure.**

### 1.6 The brief's instruction to attack the load-bearing control

**The brief `agents/tasks/LJ-1-215/LJ-1.215.md:59-62` names the emptying control
as the one to attack. I attacked it and it holds.**

**I diffed `ProbePlain.agda` against `ProbeTrivial.agda`.** The only differences
are the module name, a nine-line comment plus a two-line definition, and 46
replacements of the numeral conjunct by `isNumeral (fst ar)` or `isNumeral (fst
N)`. **The component count is genuinely unchanged and the level is genuinely the
same: `V ℓ → Type (ℓ-suc ℓ)` in both arms.**

**The strongest objection I could build, and it fails.** `x ≡ x` still removes no
IMPORT, because the module imports `ℕ`, `#_`, `Σ` and `∥_∥₁` for other reasons.
So the trivial arm cannot show that the numeral machinery is free to LOAD. **But
that is not what the report claims.** It claims the content at 46 telescope
positions is free, and for that claim the arm is exactly right. **And the
import-identical revert at rung 1 proves the point the objection needs: the same
import set gives 1,165 ms or 9,401 ms depending only on the telescope.**

## 2. `[LJ-1.206]`: UPHELD

**Verdict: UPHELD. The verdict is correct and the record makes it FIRMER than
the report dared. But the report lost its own instrument, and I say so.**

### 2.1 Question 1: is the refusal correct on its own numbers?

**YES for everything I can re-run, and the strongest half is verifiable without
the socket at all.**

| the report's claim | my check | result |
|---|---|---|
| I landed nothing; `dispatch.py` is byte-identical | `cmp` against `agents/tasks/LJ-1-206/dispatch.py.before-lj206` | **byte-identical, 2,319 lines each** |
| the task tree is unchanged | `git status --porcelain agents/tasks/LJ-1-206/` | empty |
| `returns.log`, 389 lines | 390 lines at 16:23, 394 now | correct for its moment |
| 452 driver logs | 456 `.log` files now, 4 dispatches closed after 16:23 | correct for its moment |
| 1 DIED across the corpus | 1 line `HERDR agent DIED during the run` | **exact** |
| 2 existence-check failures | 2 files carry `agent_not_found` | **exact** |
| the control brief is refused for no DD4 | `agents/tasks/LJ-1-157/LJ-1.157.md` carries neither `DD4` nor `C-22` | **exact** |
| the five passing briefs pass | each of the five carries both `DD4` and `C-22` | **exact** |

**Every `dispatch.py` line citation resolves.** I checked the four that carry the
argument: the two-phase wait at `agents/tasks/LJ-1-206/dispatch.py.before-lj206:922-929`,
the blocked check at `:960-965`, the death guard at `:967-974`, and
close-on-clean-finish at `:985-991`.

**The load-bearing log is real and it says what the report says.**
`.claude/skills/codex-dispatch/.state/logs/LJ-1.206-20260814-160523.log` holds
five driver lines. Line 5 is the wait returning `working` at
`state_change_seq 228` to `229`. Line 6 is the wait returning `idle` at
`state_change_seq 241`. Line 7 is `HERDR done pane=w7:p12 closed`. **The first
attempt was closed while its report was a skeleton, and the driver recorded it
clean. The log proves the false-idle failure mode by itself.**

### 2.2 Question 2: is the measurement sound? NO, AND THIS IS THE DEFECT

**THE PROBE IS GONE. `lj206-waitprobe.py` DOES NOT EXIST anywhere in the
repository.** I searched the whole tree.

**Sections Q1, Q2 and Q3 quote four commands against that file:**
`subscribe 75 w7:p17 ...`, and three `wait-event ...` calls
(`agents/tasks/LJ-1-206/lj-1.206-report.md:35`, `:104`, `:112`). **None of them
can be re-run.**

**It is NOT a rename of the probe that IS there.**
`agents/tasks/LJ-1-206/probe_socket.py:14-21` gives a different command
surface: `subscribe <pane_id> <seconds>` takes ONE pane, and the wait
subcommand is `wait`, not `wait-event`. **The report's `subscribe` takes the
seconds first and then SIX panes. It is a second, different script, and the
second attempt did not leave it.**

**This breaks the probe rule.** `AGENTS.md` says a probe is written beside the
report, is tracked, and is never deleted; `dev/LESSONS.md` D-1 is the rule.
`scripts/check-probes.py` cannot catch this, because it refuses a probe in the
WRONG place and has nothing to say about a probe in NO place.

**What the defect actually costs, stated exactly rather than dramatically.**
Two figures lose their instrument: `events.wait` returning at 0.00 s on an
already-idle agent, and `events.wait` rejecting 18 of 19 event kinds with
`unsupported_event_wait_match`. **Both support the NEGATIVE.** The two figures
that support the POSITIVE half, the live subscribe deliveries at 61.5 s and
95.8 s, lose their instrument too.

**So the defect does not flip the verdict. It removes the report's ability to be
checked on two of its four questions, and the missing evidence points the same
way as the verdict.**

**Q4 needs no probe and I verified it from disk.**
`.claude/skills/herdr/SKILL.md` has no agent `stop`, no agent `kill` and no
`--interrupt`; its only stop words are at `:193-194`, about the SERVER.
`.claude/skills/dispatch-herdr/SKILL.md:356` states the same finding as a
measured heading. **Q4's REFUTED is independently supported.**

### 2.3 Question 3: did the brief cause the outcome? PARTLY, AND THE RECORD REPAIRS IT

**The brief forbade the one test that would close the gap.**
`agents/tasks/LJ-1-206/LJ-1.206.md:57` says「YOU MUST NOT CREATE A HERDR
AGENT」, for a good measured reason at `:57-63`. **So the embedded `agent.prompt`
wait went untested, and the report marks it UNMEASURABLE HERE at its `:309-311`
and makes it next-step item 1 at `:190-195`.**

**That is `[LJ-1.211]`'s largest cause in outline: the brief fixed a method that
could not reach one question. But the brief also supplied the escape hatch at
`:75-76` and the abort branch at `:88-89`, and the agent used both correctly.
The brief did not cause a WRONG answer. It caused a MISSING one.**

**AND THE MISSING ANSWER IS ALREADY IN THE RECORD. This is C-38: a hypothesis is
discharged when something SUPPLIES it.**

**`agents/tasks/LJ-1-206/dispatch.py.before-lj206:922-926`:**

> TWO PHASE, AND ONE PHASE IS NOT ENOUGH. `--until idle` matches the state the
> agent is ALREADY in at submission, so a one-phase wait returns at once whether
> or not the agent ever started. **Measured twice on 2026-08-13, once with a bare
> wait and once with prompt --wait.**

**And `:997-999`:**

> ONE-PHASE WAIT. `agent prompt --wait --until idle` **is the exact form measured
> on 2026-08-13 to return AT ONCE**, because `idle` is the state the agent is
> already in at submission.

**The embedded `agent.prompt` wait was measured on 2026-08-13 and it returned at
once.** The report read this file WHOLE and cites `:997-1001` in its own ARCHIVE
USED at `agents/tasks/LJ-1-206/lj-1.206-report.md:233-234`. **It read the answer
and filed the question as open.**

**The honest caveat, and P-l is why I write it.** The 2026-08-13 measurement does
not record the herdr version. Today's binary is 0.8.0. **So the record does not
close the question on THIS version; it moves the next step from「measure it for
the first time」to「confirm a 2026-08-13 measurement on 0.8.0」. That is a much
smaller task, and next-step item 1 should be re-priced, not funded as written.**

### 2.4 Question 4: is there a cure the return missed?

**YES, and it is cheap.** The report's own caveat 3 at
`agents/tasks/LJ-1-206/lj-1.206-report.md:61-64` says the status-change event
carries the agent KIND, not the agent NAME, so a subscriber must map pane to
task. **The driver already writes that map: `returns.log` records task code, verdict
and log path per line, and every driver log's first two lines are `HERDR
base=` and `HERDR pane=`.** So the pane-to-task map is a two-line read of an
existing file, never new state. **The report priced the subscriber as new
long-lived code without noticing that its hardest part already exists.**

**I did not price the subscriber and I do not claim it is now cheap. INFERRED.**

### 2.5 The classification

**MEASURED for「nothing landed」, for Q4, and for the false-idle log.
UNREPRODUCIBLE for the two `events.wait` figures and the two subscribe figures,
because the instrument is gone. The report's own DOCUMENTED, MEASURED and
REFUTED labels are correctly applied to what it believed it had.**

## 3. `[LJ-1.198]`: UPHELD BUT MISATTRIBUTED

**Verdict: UPHELD BUT MISATTRIBUTED.**

**UPHELD:「A6 is not ONE number today」and「the seven cells do not sum」. No
evidence contradicts either. `[LJ-1.8]`'s trophy row stays blocked.**

**MISATTRIBUTED:「A WALL」is the wrong cause. What the record supports is「one
fixed encoding of A6's L-side carve did not finish on one un-capped run, and the
bisection that would name the cause ran out of clock」. A6 is UNPRICED, not
WALLED, and the orchestrator's own reading in `agents/tasks/LJ-1-215/LJ-1.215.md:53-55`
is correct.**

### 3.1 Question 1: is the refusal correct on its own numbers?

**The cross-report citations are all correct. I checked every one.**

| the report's citation | my check |
|---|---|
| `[LJ-1.165]` measured a wall at 20 min 1 s | `agents/tasks/LJ-1-165/lj-1.165-report.md:144`, exact |
| `[LJ-1.176]` inclusion at 1.72 s | `agents/tasks/LJ-1-176/lj-1.176-report.md:95`, three runs 1.71/1.74/1.72 |
| the inclusion is 185 lines whole-file | `agents/tasks/LJ-1-176/lj-1.176-report.md:295`, exact |
| `hasReplacementL` five times, all comments | `ProbeLJ1198A.agda:12,16,36,278,463`, all comments, exact |
| `hasSeparationL` once in code at `:656` | `ProbeLJ1198A.agda:656`, exact; `:231` is its import |
| no hole and no postulate | grep for `postulate`, `{!`, `trustMe`: none |
| `ShiftAbs`/`Shiftω` copied from `[LJ-1.156]` | `agents/tasks/LJ-1-156/ProbeLJ1156A.agda:250` and `:366`, exact |
| the retired route holds the shift's shape | `archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:730-731` holds `shift-inj`. The task code `L3-32-T31` does not resolve in `archive/dev/TASKS-archived.md`, but the SHAPE claim is true at the line I give |

**So the report is honest and its reading is careful. The defect is not in what it
read. It is in what it measured.**

### 3.2 Question 2: is the measurement sound? NO. THIS IS THE FINDING

**`agents/tasks/LJ-1-198/` holds NO run artifact of any kind.** Seven `.agda`
files, the brief and the report. **No `runs/` directory, no profile, no load
header, no exit code, no wall-second file.** Compare `agents/tasks/LJ-1-209/runs/`,
which holds 14 raw profiles, each with a load line before and after and an exit
line.

**The 11,034 s figure is second-hand.**
`agents/tasks/LJ-1-198/lj-1.198-report.md:14` says it is MEASURED「by the
orchestrator's wall-clock observation of my run」. **The agent did not time it and
left no artifact. It is a real event with no record.**

**THE BISECTION IS THE PART THAT DOES NOT HOLD, and here is why.**

**Defect 1: the bounds SHRINK as the bisection narrows.** From
`agents/tasks/LJ-1-198/lj-1.198-report.md:140-146`:

| probe | bound | result the report gives |
|---|---:|---|
| B, C, D | 480 s | WALL, still running |
| **E, the GREEN control** | **300 s** | GREEN, exit 0 |
| **G, the decisive cut** | **180 s** | WALL, still running |

**The control got a 300 s bound. The cut that names the cause got 180 s. And the
control's ELAPSED TIME IS NOWHERE IN THE REPORT.**

**So「`sv` alone is already the wall (probe G, > 180 s)」at `:132` is not
interpretable. If E takes 170 s, then G exceeding 180 s means `sv` added more
than 10 s. That is not a wall. The report never gives the number that would
settle it.**

**Defect 2: a bisection probe was RUN and DROPPED from the record.**
`agents/tasks/LJ-1-198/ProbeLJ1198F.agda` exists, at 545 lines, written 16:51.
**It appears nowhere in the bisection table.** The report says at `:304` that the
bisection「left `ProbeLJ1198B` through `ProbeLJ1198G`, whose states are in
section 4.1」. **Section 4.1 has five rows and F is not one of them.**

**I read F and it is the decisive control the report needed.** F is E plus the
`ij` conjunct alone; G is E plus the `sv` conjunct alone. They differ in nothing
else, and both are 545 lines.

**And F settles the attribution against the report's own wording.** Both
conjuncts run `↪-inj`: F at `ProbeLJ1198F.agda:540` uses `↪-inj {a = fst C}`,
and G at `ProbeLJ1198G.agda:540` uses `↪-inj {a = fst D}`. **So the report's
「`sv` alone is already the wall」names one of two conjuncts that carry the same
mechanism.**

**Defect 3: I can say what F did, from the artifact rather than the report.**
`_build/2.8.0/agda/agents/tasks/LJ-1-198/` holds exactly TWO interfaces:
`ProbeLJ1198A.agdai` dated 11:27 and `ProbeLJ1198E.agdai` dated 16:46. **An
interface is written on a successful typecheck only. So B, C, D, F and G all
failed to complete, and F is a sixth unreported wall.** That corroborates the
`↪-inj` mechanism and refutes the word「alone」.

**Defect 4: the run count the brief required was not taken, and the report says
so.** `agents/tasks/LJ-1-198/LJ-1.198.md:97-99` requires three kept runs for any
figure a decision rests on. `agents/tasks/LJ-1-198/lj-1.198-report.md:120-122`
records one kept run. **The report is honest about this and I credit it.**

**What survives all four defects.** The 684-line file did not produce an
interface, and neither did five of the six cuts. **That much is MEASURED from the
build directory.「A6's L-side carve, as encoded in this probe, is expensive」
stands. Nothing narrower does.**

### 3.3 Question 3: did the brief cause the outcome? YES, AND I CAN PRICE IT

**The `[LJ-1.198]` brief has NO clock cap. I checked both briefs side by side.**

- `agents/tasks/LJ-1-209/LJ-1.209.md:76-77`:「**A single `agda` invocation past 30
  MINUTES is a wall**: interrupt it, report the elapsed seconds, and bisect.」
- `agents/tasks/LJ-1-198/LJ-1.198.md:96-100` gives the heap cap and「Report a
  heap exhaustion as a wall」. **It names no elapsed-time threshold at all.**

**THE PRICE OF THE MISSING CAP, in the dispatch's own budget.**
`.claude/skills/codex-dispatch/.state/returns.log` records the dispatch starting
at 11:10:44 and returning at 17:00:25: **5 h 50 m.** The report's own run 11 is
**3 h 04 m**, so ONE un-capped invocation took **53 percent of the whole
dispatch**.

**And the bisection got the remainder.** The probe files are stamped
`ProbeLJ1198B.agda` 16:20, `C` 16:28, `D` 16:37, `E` 16:46, `F` 16:51, `G` 16:54,
and the report 17:00. **The entire six-cut bisection ran in 34 minutes, 10
percent of the dispatch, at the very end of it.**

**That is the causal chain, and it is checkable.** The bounds shrink from 480 s
to 300 s to 180 s because the agent was running out of clock, and it was running
out of clock because one invocation had already eaten three hours with nothing
telling it to stop. **`[LJ-1.209]`'s cap would have stopped run 11 at 12:17 and
left four and a half hours for the bisection.**

**Against `[LJ-1.211]`'s cause split this is not「a method that could not answer
the question」. The method was right and it was starved.** The bisection is the
correct instrument, probe E is the correct control, and F and G are the correct
cuts. **They were run with no baseline and no clock.**

### 3.4 Question 4: is there a cure the return MISSED? YES, AND THE REPORT NAMES IT WITHOUT PRICING IT

**The report itself writes the cure and then files it as future work.**
`agents/tasks/LJ-1-198/lj-1.198-report.md:223-224`:「NOT MEASURED. Whether
sealing the conjuncts or reformulating `pair-out` cures the wall. A future task's
question, not this probe's.」

**And its own section 4.1 at `:149-153` explains why that cure is the whole
question:**

> The inclusion's `sv` in `[LJ-1.176]` needed no `↪-inj`: its `pair-out` returned
> `fst x ≡ fst y` directly. The shift's `pair-out` returns a fiber `k : ⟪ fst D
> ⟫` plus `fst y ≡ ⟪ fst C ⟫↪ (sh k)`, so `sv` must run `↪-inj` on the abstract
> domain's presentation.

**`pair-out`'s return type is a CHOICE inside this probe. It is not a fact about
A6.** The report measured the fixed shape and refused it. **DD4's question in
`agents/tasks/LJ-1-215/LJ-1.215.md:106-109` is exactly this: a NO-GO on a fixed
shape is not a NO-GO.**

**THE CHEAPEST CURE THE RETURN MISSED, and I mark it INFERRED because I ran
nothing.** Probe E is GREEN and its interface is on disk at
`_build/2.8.0/agda/agents/tasks/LJ-1-198/ProbeLJ1198E.agdai`. **So the next task
starts from a green 528-line base, not from scratch.** Three cuts answer the
whole question, and each is one conjunct on top of E:

1. **Time E itself, three kept runs.** Nothing in the record gives E's seconds,
   and every later figure needs it. This is the missing baseline.
2. **Re-run F and G with a cap that is LONGER than E's time, never shorter.**
   That separates `ij` from `sv`, which the shrinking bounds could not.
3. **Rewrite `pair-out` to return the equality directly, as `[LJ-1.176]`'s did,
   and re-run the same cut.** That is the shape test, and it is what turns「a
   wall」into either a price or a real wall.

**I do not price these in seconds. E's own time is unknown, so any figure I gave
would be an analogy, and P-l forbids it.**

### 3.5 The classification, corrected

**The report marks eleven negatives MEASURED at `:196-224`. Three of them are
INFERRED and I re-mark them:**

| the report's claim | its mark | my mark | why |
|---|---|---|---|
| A6's L-side build does not elaborate in 11,034 s | MEASURED | **MEASURED** | one run, second-hand, no artifact, but no interface was written |
| the wall is the four conjuncts, not the reading | MEASURED | **INFERRED** | E's elapsed time is unrecorded |
| `sv` alone is already the wall | MEASURED | **UNDECIDABLE ON THE RECORD** | G's bound is shorter than E's, and F is unreported |
| the wall is the `↪-inj` fiber reconstruction | MEASURED | **INFERRED** | it is a code reading. F, which also uses `↪-inj`, supports it and was dropped |
| the inclusion is 1.72 s and the shift is over 11,034 s | MEASURED | **MEASURED, but the ratio is void** | 1.72 s is 185 lines of a DIFFERENT object; 11,034 s is a non-completion. A ratio needs two completions |

**The「at least 6,400 to 1」at `:28-29` and `:211-212` is the figure I would strike
first.** A non-completion has no duration. **The honest statement is: the
inclusion completed in 1.72 s and the shift did not complete. That is a
qualitative difference and it should not be written as a number.**

### 3.6 One overstatement in the report's own defence

**`agents/tasks/LJ-1-198/lj-1.198-report.md:229-232` says the 684 lines carry
「the ambient `ShiftAbs` and `Shiftω` (both of A6's objects, copied, 103
lines)」, and offers that as why the miniature grew.**

**`Shiftω` is one line.** `ProbeLJ1198A.agda:211` is
`module Shiftω = ShiftAbs ω ω-ord (∈-irrefl ω) (λ k → #∈ω k)`, an instantiation
of `ShiftAbs` at `:97`. **So the second object did not grow the probe. The L-side
block did.** The report's own admission is right and its reason is not.

## 4. C-42 IN BOTH DIRECTIONS, ON EACH TARGET

**C-42: a refutation measures the site it NAMES and never how far that site
EXTENDS. So I ask of each: does it reach FURTHER than it claims, and does it
reach LESS far?**

### 4.1 `[LJ-1.209]`

**FURTHER than it claims: NO, and it guards its own edge.** Section 5 at
`agents/tasks/LJ-1-209/lj-1.209-report.md:306-314` refuses to re-measure the
wing aggregate and says why: a 12.8 percent between-series band cannot resolve
an 83 ms effect. **A report that refuses to widen its own claim is C-42 obeyed.**

**LESS far than it claims: YES, in one place it does not name.** The seal probe
covers `src/L/Condensation.lagda.md` alone. That is 46 of the 63 type sites; the
other 17 live in the three `*Agree` masters
(`TwelveAgree` 7, `UpperAgree` 5, `LowerAgree` 5). **The `*Agree` masters' own
`Deserialization` terms were never measured, sealed or unsealed.** The verdict is
right for the 8.2 s term, which is Condensation's. **It is INFERRED for the
wing.**

**And one place it reaches further than the wording admits.** Section 3.3's
「the numeral CONTENT costs 47 ms」is true at 46 telescope positions with the
import set held fixed. **It is not a general law that content is free.** The
imports are identical in every arm, which I verified: `ProbePlain.agda` and
`ProbeMinusArNum.agda` have byte-identical import blocks and differ only in line
number.

### 4.2 `[LJ-1.206]`

**FURTHER than it claims: YES, in the headline only.** 「DOES NOT HOLD」reads as
a flat negative on the whole automation layer. **The report's own lead at
`agents/tasks/LJ-1-206/lj-1.206-report.md:16-20` says the NOTIFICATION half DOES
hold and is only dear to land.** The body is correctly scoped; the four-word
verdict is not. **Anyone quoting the four words alone will close a line that the
report left open.**

**LESS far than it claims: YES, and the record fills it.** The report's own gap
is the embedded `agent.prompt` wait, marked UNMEASURABLE HERE. **The record
already measured it, on 2026-08-13, and it returned at once**
(`agents/tasks/LJ-1-206/dispatch.py.before-lj206:925-926` and `:997-999`). **So
the refutation reaches further than the report dared to claim, in the report's
own favour.**

### 4.3 `[LJ-1.198]`

**FURTHER than it claims: YES, and this is the misattribution.** The measured
site is ONE encoding of the shift's L-side carve, in which `pair-out` returns a
fiber. The claim written into `[LJ-1.8]`'s row is「A6's charge is a WALL」.
**Between the site and the claim sit two un-measured steps: that this encoding is
the only one, and that `Shiftω` prices like `ShiftAbs`.**

**LESS far than it claims: YES, twice.**

1. **The second object was never priced separately.** `ProbeLJ1198A.agda:211`
   instantiates `Shiftω` from `ShiftAbs` in one line. A6's cell holds two
   objects and the probe measured one module.
2. **The `sv` attribution does not reach even the conjunct it names.** F, which
   is the `ij` conjunct alone, also failed to produce an interface. **So the
   mechanism is shared by at least two conjuncts, and「`sv` alone」names one of
   them.**

## 5. WHAT EACH UNBLOCKS OR CONFIRMS

### 5.1 `[LJ-1.209]`: CONFIRMED, and it closes two doors for good

**CONFIRMED and closed.** The `opaque` seal on `isNumeral` is dead. Nobody should
fund it again. **And `[LJ-1.204]`'s「about 420 ms per field」is void, because the
field carries no term to divide.**

**CONFIRMED as a mechanism, and I add the corroboration the report did not
use.** `agents/tasks/LJ-1-204/LJ-1.204-report.md` section 3 establishes that
`Deserialization` here is the LAZY, on-demand read of imported definition bodies
during the typecheck, never a one-time read of the import list. **My import diff
supplies the proof of that: `ProbePlain` and `ProbeMinusArNum` import exactly the
same modules and read 9,401 ms against 1,165 ms.** So the term follows what the
elaborator touches, not what the module imports. **This is C-38: the record
SUPPLIES the mechanism `[LJ-1.204]` could only infer.**

**STILL OPEN, and now priced by shape.** Which part of commit `c8a628b` carries
the 8.2 s. **My count: the revert removes 152 lines, of which 46 carry the
numeral spelling and 20 carry the name. So the numeral component is a MINORITY of
the reverted surface, and about 32 removed lines carry `lookup K` membership
conjuncts instead.** The report's own next probe at `:375-393` is the right first
cut and it should be funded as written.

**AND IT MAY ALREADY BE IN FLIGHT. DO NOT FUND IT TWICE.** `git status` shows an
untracked `agents/tasks/LJ-1-214/` holding `ProbeDelete.agda`, `ProbePlain.agda`,
`ProbeMinusArNum.agda`, `gen_probes.py`, `run_series1.sh` and a `runs/`
directory. **That is the delete-the-component arm.** I did not open its report,
because it is a live sibling's working file and my brief scopes me to three
targets. **I name the directory so the orchestrator checks before it dispatches.**

### 5.2 `[LJ-1.206]`: CONFIRMED, and one named next task can be CANCELLED

**CONFIRMED.** The wait protocol keeps its lines. `dispatch.py` is byte-identical
to its aside copy, so nothing landed and nothing needs review.

**CANCELLED.** The report's next-step item 1 at
`agents/tasks/LJ-1-206/lj-1.206-report.md:190-195` asks to measure the embedded
`agent.prompt` wait on a live test agent. **It is already measured, twice, on
2026-08-13, and it is recorded in the driver's own comments.** The task shrinks to
「confirm the 2026-08-13 reading on herdr 0.8.0」, and P-l is the only reason to
confirm it at all, because the version is not recorded.

**OWED, and it is the finding of this review's second target.** `lj206-waitprobe.py`
must be reconstructed and left in `agents/tasks/LJ-1-206/`, or the report's four
socket commands must be marked UNREPRODUCIBLE in the record. **A negative that
closes a line and cannot be re-run is exactly the kind DD25 exists to catch.**

### 5.3 `[LJ-1.198]`: A DIFFERENT ROW ENTRY, and a green base to start from

**`[LJ-1.8]`'s A6 cell should read UNPRICED, not WALLED.** The two entries are not
the same: WALLED says the work stops, and UNPRICED says the measurement was not
taken. **The record supports the second.**

**UNBLOCKED, and cheaper than a fresh start.** `ProbeLJ1198E.agdai` sits green in
`_build/2.8.0/agda/agents/tasks/LJ-1-198/`, dated 16:46. **A re-price starts from
a green 528-line base with the formula, the reading and the bound already
elaborating.** The three cuts in section 3.4 answer the whole question.

**AND THE NEXT BRIEF MUST CARRY A CLOCK CAP.** `[LJ-1.209]`'s cap at
`agents/tasks/LJ-1-209/LJ-1.209.md:76-77` is the wording to copy. **On the
measured record, its absence cost 53 percent of one dispatch and left the
decisive bisection 34 minutes.**

**PROPOSED LAW, with its measurement, for the orchestrator to number or
refuse.** **A bisection's cut must never get a shorter bound than its own green
control, and the control's elapsed time is reported before any cut is
interpreted.** MEASURED at `[LJ-1.198]`: the control E ran under a 300 s bound
with its time unrecorded, and the decisive cut G ran under 180 s, so no
comparison is possible and the strongest claim in the report is undecidable.
**I do not assign an ID.**

## 6. THE THREE NEGATIVES, MARKED

**MEASURED or INFERRED, in those words, per the brief.**

| negative | mark |
|---|---|
| `[LJ-1.209]`: the seal does not reach; 83 ms of 8,236 ms | **MEASURED** |
| `[LJ-1.209]`: the numeral content is free; 47 ms the wrong way | **MEASURED** |
| `[LJ-1.209]`: which part of `c8a628b` carries the 8.2 s | **INFERRED**, and the report says so |
| `[LJ-1.206]`: nothing landed | **MEASURED**, and I re-verified it by `cmp` |
| `[LJ-1.206]`: no interrupt in the automation layer | **MEASURED**, verifiable from disk |
| `[LJ-1.206]`: `events.wait` fires at once, and rejects a death | **UNREPRODUCIBLE**, the probe is gone |
| `[LJ-1.198]`: A6 is not one number today | **MEASURED** |
| `[LJ-1.198]`: A6's charge is a WALL | **INFERRED**, and it is written as MEASURED |
| `[LJ-1.198]`: `sv` alone is the wall | **UNDECIDABLE ON THE RECORD** |
| `[LJ-1.198]`: the shift is at least 6,400 times the inclusion | **VOID**, a non-completion has no duration |

## 7. DD4, ON EACH NEGATIVE

**The question the brief sets: did the return price a FIXED shape and refuse it,
when the GENERIC shape prices differently?**

- **`[LJ-1.209]`: NO.** `isNumeral` is written over `V ℓ` and names no tower, so
  the probe measured the generic shape. **And the report states plainly at
  `agents/tasks/LJ-1-209/lj-1.209-report.md:348-349` that DD4 does not save the
  cure: three shared lines that buy 83 ms are three lines that buy 83 ms.** That
  is DD4 answered honestly against the author's own interest.
- **`[LJ-1.206]`: NOT APPLICABLE in the tower sense**, and the report gives the
  right split anyway: a mechanism herdr maintains is paid twice, and a refusal
  that encodes a Bedrock ruling cannot be delegated.
- **`[LJ-1.198]`: YES. THIS IS THE FIXED-SHAPE CASE.** The refusal is priced on a
  `pair-out` that returns a fiber. `[LJ-1.176]`'s `pair-out` returned the equality
  directly and cost 1.72 s. **The report identifies the difference at `:149-153`
  and then files the alternative as future work at `:223-224`.** A NO-GO on a
  fixed shape is not a NO-GO.

## 8. ARCHIVE USED (DD18)

**Read directly, never through a report's account of it, per the brief.**

- **`agents/tasks/LJ-1-209/` in full.** `lj-1.209-report.md` whole. All 14 raw
  runs in `runs/`, opened individually for their `Deserialization` line, wall
  seconds, exit code and load headers. `ProbePlain.agda`, `ProbeSeal.agda` and
  `ProbeTrivial.agda` diffed against each other. `ProbeOpaqueReal.agda:18-31`,
  the seal control, whose commented red half at `:30-31` matches the quoted
  refusal column. **TOOK:** every figure in section 1.1 of this report, and the
  design flaw at `:220-222`.
- **`agents/tasks/LJ-1-206/` in full.** `lj-1.206-report.md` whole.
  `probe_socket.py:14-21`, the FIRST attempt's probe, whose command surface does
  not match the report's commands. `dispatch.py.before-lj206`, read at `:908-991`
  and `:995-1005`. **TOOK:** the two-phase-wait comment at `:922-926` and the
  one-phase lesson at `:997-999`, which discharge the report's own open item.
- **`agents/tasks/LJ-1-198/` in full.** `lj-1.198-report.md` whole. All seven
  probes. `ProbeLJ1198E.agda` against `ProbeLJ1198F.agda` against
  `ProbeLJ1198G.agda`, which is how I found F. **TOOK:** the shrinking bounds at
  `:140-146`, the dropped probe, and the `↪-inj` sites at `ProbeLJ1198F.agda:540`
  and `ProbeLJ1198G.agda:540`.
- **`_build/2.8.0/agda/agents/tasks/LJ-1-198/`.** **TOOK:** the two interfaces,
  `ProbeLJ1198A.agdai` at 11:27 and `ProbeLJ1198E.agdai` at 16:46, and the ABSENCE
  of an interface for B, C, D, F and G. **This is the only completion record
  `[LJ-1.198]` left, and its report does not cite it for B through G.**
- **`agents/tasks/LJ-1-211/lj-1.211-report.md:11-16`, `:35`, `:63`, `:193-195`.**
  **TOOK:** the cause split, 8 of 10 brief-caused and 4 of 10「the brief fixed a
  method that could not answer」, and the report's own note at `:195` that the
  split survives a re-bucketing. **USED against each target in question 3.**
- **`agents/tasks/LJ-1-204/LJ-1.204-report.md`**, sections 0, 3 and 4. **TOOK:**
  the self-marked INFERRED attribution, and the lazy-deserialization finding in
  section 3, which corroborates my import diff.
- **`agents/tasks/LJ-1-176/lj-1.176-report.md:95`, `:126`, `:204`, `:295`,
  `:383`.** **TOOK:** the 1.72 s inclusion over three runs, the 112-line object,
  the 185-line whole file and the 81 percent generic figure. **All four resolve
  exactly as `[LJ-1.198]` cites them.**
- **`agents/tasks/LJ-1-165/lj-1.165-report.md:11-12`, `:144`.** **TOOK:** the 20
  min 1 s wall and the 20-minute cap it proposed. **NOTE: `[LJ-1.165]` proposed a
  20-minute clock cap and `[LJ-1.198]`'s brief did not carry one.**
- **`agents/tasks/LJ-1-156/ProbeLJ1156A.agda:250`, `:366`.** **TOOK:** the
  ambient `ShiftAbs` and `Shiftω`, confirming they were copied and not rewritten.
- **`agents/tasks/LJ-1-157/LJ-1.157.md`** and the five briefs in the acceptance
  table. **TOOK:** the presence or absence of `DD4` and `C-22`, which reproduces
  the refusal reasons exactly.
- **`.claude/skills/codex-dispatch/.state/`.** `returns.log`, 394 lines, for the
  dispatch start and return times of `[LJ-1.198]`. `logs/LJ-1.206-20260814-160523.log`,
  all 7 lines, the first attempt's self-kill at `state_change_seq 229` then `241`.
  The 456-file log corpus for the DIED and `agent_not_found` counts.
- **`.claude/skills/herdr/SKILL.md:193-194`** and
  **`.claude/skills/dispatch-herdr/SKILL.md:356`.** **TOOK:** the absence of an
  agent stop or interrupt, which makes `[LJ-1.206]`'s Q4 verifiable without the
  socket.
- **`scripts/check-ratio.py:74-83`**, read directly. **TOOK:** the constant's own
  words. **The between-series 12.8 percent is at `:75` and `:80`; the
  within-series 0.5 to 4.0 percent is at `:81-83`.** Both briefs and the
  `[LJ-1.209]` report cite `:72-76` for both halves, which is short by five lines.
- **`archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:730-731`.**
  **TOOK, AS SHAPE ONLY:** the retired route holds `shift-inj` for
  `⟪ sucV γ ⟫ → ⟪ γ ⟫`. **So `[LJ-1.198]`'s archive claim is true at this line.
  Its own citation, the task code `L3-32-T31`, does not resolve in
  `archive/dev/TASKS-archived.md`.** **NOTHING TRANSFERS as a number:** the
  retired tree is not this tree (P-l), and the archived object is the ambient
  shift, never an L-side build.
- **`archive/dev/TASKS-archived.md`: SEARCHED, NOTHING TAKEN.** It holds no
  L-side carve of the shift, no herdr record, and no interface-deserialization
  account. **Searched for `L3-32-T31`, `shift-inj` and `Shift.shift`; no hit.**

## 9. LITERATURE USED (DD18)

- **`dev/literature/devlin-II5.md`, opened and searched.** **The brief says it
  bears on `[LJ-1.198]` through A6's objects. I did not find that bearing.**
  Its only successor content is about a formula-reading successor clause, at
  `:392`, `:544`, `:546` and `:567`. **Nothing in it states or builds the
  successor absorption `⟪ sucV γ ⟫ ↪ ⟪ γ ⟫`.** So `[LJ-1.198]` was right to cite
  `devlin-errata.md` instead of it.
- **`dev/literature/devlin-errata.md`, at the two places `[LJ-1.198]` cites.**
  **TOOK:** BS has no replacement, and DS carries Δ0 separation. **Both quotes
  are accurate.** They support「the shift needs no replacement AXIOM」, which is
  the report's gate answer, and they say nothing about elaboration cost.
- **ONE LINE ON THE OTHER TWO, as the brief asks. `devlin-II5.md` bears on
  neither `[LJ-1.206]` nor `[LJ-1.209]`: one is a question about a terminal
  multiplexer and the other is a question about Agda's deserialization cost, and
  no set-theory text governs either.**
- **The herdr documentation is `[LJ-1.206]`'s literature and I did NOT fetch
  it.** My brief makes this review a reading of the record. **So the report's
  three URLs and its schema-versus-binary disagreement are UNCHECKED by me, and I
  say so rather than imply I confirmed them.**

## 10. WHAT I DID, AND WHAT I DID NOT

**I ran NO Agda.** Both slots were held. Every figure here comes from a file on
disk: a raw run, a probe, a build interface, a driver log or a master.

**I edited no master, no brief and no report.** The only file I wrote is this
one. I committed nothing and pushed nothing. I ran no `make check`. I ran no
`git checkout .`, no stash, no reset and no clean.

**What I could NOT check, stated rather than implied:**

1. **`[LJ-1.206]`'s four socket readings.** The probe does not exist. No amount
   of reading recovers them.
2. **`[LJ-1.198]`'s 11,034 s.** No artifact. I confirmed only that
   `ProbeLJ1198A.agda` at 684 lines produced no interface.
3. **Probe E's elapsed time.** It is the number that would decide `[LJ-1.198]`'s
   strongest claim and it is nowhere.
4. **The herdr site.** Not fetched, by my brief.

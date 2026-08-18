# POD: the program that runs the route (goal [L9], IN FORCE)

**Status: BUILT AND IN FORCE since the POD cutover of 2026-08-18, commit
`fc676cb`. Written as a design on 2026-08-17.** This memo was the design
deliverable of goal `[L9]` in `dev/PLAN.md` section 11. The cutover built it,
and the file is now a guarded rule home: `dev/pod/spec-surface.toml` carries its
sha256 in a `[[guarded]]` entry, so a change to it needs a named owner approval
under R16.

**`AGENTS.md` holds the shared Boundary, and `dev/ARCHIVE.md:214` records
`dev/ORCHESTRATION.md` as archived.** Check the state yourself: `dev/pod/` and
`scripts/pod/` exist, and the pointer table of `AGENTS.md` sends every slot here,
under the row `The program that runs all of this`.

**THREE SECTIONS ARE RULES AND THE REST IS A DESIGN RECORD.** Section 3 is the
rule set, section 3.1 gives every written clause verbatim, and section 7.1 gives
every ruling and every gate its disposition. Read those three as rules. Read
every other section as the reason a decision was made. **Where a section and the
code disagree, the code is the fact and the section is a defect to report.**

This document assembles four audits and two adversarial reviews into one
buildable specification. Section 11 carries every open gap.

Every design claim that rests on an existing asset cites that asset at
`file:line`. Every citation below was resolved against the working tree on
2026-08-17. A claim with no citation is a proposal.

**TWO RULE SERIES, AND THEY ARE DIFFERENT.** `D<n>` names one of the 27
architecture decisions of section 2. `DD<n>` names a repository ruling in
`dev/PLAN.md` section 3, and section 7.1 gives each one a disposition. A bare
`D<n>` in an older Bedrock document belongs to a third series, archived on
2026-08-09, and never to this one.

**Fifteen amendments. Fourteen are the owner's, ruled on 2026-08-17. One is the
orchestrator's and follows from A4.** They are part of the ruled set and this
document states each where it applies. **The owner ruled once more that day, on
DD0: PUT BOTH LOST PARTS BACK.** Clause W9 carries part 3 and rules R15 and R16
carry the authorship half, so DD0 is SUPERSEDED IN PART (7.1).

- **A1.** Fact 3 reads "the change in the count of UNRESOLVED names on the task's
  own declared obligation list". Section 4.7.
- **A2.** `dispatch.py` is EXTENDED and never replaced. Section 6.2.
- **A3.** A system row whose action is `stop_loop` outranks every task row. 4.4.
- **A4.** The witness meter of fact 3 is FIXED and never replaced. An obligation
  names a probe path and a dotted name, and the meter DERIVES the witness from
  the probe file. **This NARROWS the ruled text, which asked the BRIEF for a
  witness preamble.** Section 4.7.2 discloses the departure and its two costs.
- **A5.** Fact 1 is the ACCEPTANCE RUNNER's exit code and never raw Agda's. The
  six conjuncts of AD13 sit under it, and fact 2's value set grows to name
  the five non-Agda failures. Sections 4.3 and 5.4.
- **A6, the orchestrator's.** A `done` branch satisfies pre-flight P19 EITHER by
  `obligations_delta_max <= -len(obligations)` OR by `outcome = "no-go"`. Without
  it a NO-GO is inexpressible: a NO-GO leaves every declared name unresolved, so
  the delta stays 0.
- **A7. THE DD SERIES IS NOT VOID.** It BINDS today. Cutover step 12b would set it aside IN ITS CURRENT FORM while
  the process is restructured, and its SUBSTANCE must survive. Every DD ruling
  takes exactly one of three dispositions and none may disappear: MECHANISED
  (the new flow or a hook enforces it, at a named point), WRITTEN RULE (it
  cannot be mechanised, so section 3.1 states the clause), or SUPERSEDED (it
  blocks the new flow from running mechanically, so the new flow replaces it and
  the row NAMES the contradiction). Sections 3, 3.1 and 7.1.

**FIVE MORE, ruled by the owner on 2026-08-17 after the design was read.**

- **A8. `AGENTS.md` SURVIVES THE CUTOVER, rewritten in place.** This REPLACES the
  first half of AD4 and cutover step 4b's `git mv AGENTS.md archive/AGENTS.md`.
  The file keeps its name and its path, and it holds exactly four things: a
  minimum project summary, the current milestone goal, the most important SHARED
  Boundary, and a pointer to `dev/pod/instructions/<slot>.md`. **It is the ONE
  hand-written source**, and the program GENERATES each slot file from it, so one
  source gives three slices and no slice can drift. `CLAUDE.md` keeps its
  `@AGENTS.md` import, because the file it imports is now small. Only
  `dev/ORCHESTRATION.md` is archived at step 4b.
- **A9. THE THREE DROPPED RULES ARE KEPT**, as clauses W13, W14 and W15, each
  scoped `every slot`: the document taxonomy, the obligation that a new top-level
  directory carries a `README.md`, and the ban on an unpinned or globally
  installed dependency. Section 1 recorded them as lost and they are not lost.
  Their `enforced by` value is `agent discipline`, which is an admitted value.
- **A10. DD24 IS NOT SUPERSEDED. Its RATIO form is restored**, seconds over
  in-fence lines. This overturns the 7.1 row and gap M13. **The consequence is
  stated rather than hidden:** the design retired the ratio because a ratio needs
  a seventh fact key and pre-flight P4 refuses one. So P4 admits a seventh key,
  `lines`, the in-fence line count of the task's own write scope, and section 4.3
  carries it as fact 7. One seeded system row carries the bar, and a change to
  that number needs the same approval trailer the spec surface needs.
- **A11. AN IDLE SLOT IS MECHANICALLY CURED, not merely reported.** This closes
  gap M12 by building rather than by writing a clause. `pod_tick()` gains rule
  **(g) REFILL**: when a slot is free AND `dev/pod/queue.toml` holds no
  dispatchable entry, the program dispatches the mathematician with the standing
  brief `dev/pod/instructions/refill-queue.md`. **This does not violate AD1.** The
  program decides only that someone must be asked; the head decides what the work
  is. It is the same shape as AD15's maintainer trigger and AD16's automatic
  re-dispatch, which the design already admits.
- **A12. The maintainer head is `claude-opus-5` at effort `high`.** This closes
  gap M8. Section 6.1 carries it, and AD2's fifth head is now ruled rather than
  picked.
- **A16. THE REMAINING CRASH PATHS ARE THE MAINTAINER'S WORK, ruled 2026-08-18.**
  Two adversarial rounds hardened the program and each found one layer deeper:
  the second round closed every path the first named and reported 40 more, all on
  MALFORMED input. The owner ruled the loop starts anyway and the maintainer
  fixes them as they fire. **The reasoning is that no producer of malformed input
  exists today:** `dev/pod/table.toml`, `dev/pod/replay-corpus.jsonl` and the
  transition log are all tracked and the program writes them itself. **A crash is
  therefore a REAL signal rather than a hypothetical**, and rule (f) already sends
  a second instance to a reviewer. Hardening rounds do not converge on their own,
  and this is the stop line.

**THREE MORE ON THE MEMORY DISCIPLINE, ruled 2026-08-17 after an audit of this
document against `dev/LESSONS.md` C-12 found three carry-over defects.** C-12 is
a MEASURED law and it binds new code. The audit is why these exist.

- **A13. THE WATCHDOG GETS AN OWNER, and it is the program.** C-12 says to restart
  `scripts/ops/agda-watchdog.sh` at every session, and **the POD has no session**;
  section 7's script table put the watchdog outside the POD entirely, so nothing
  would ever start it. MEASURED 2026-08-17: it was not running. **`pod.py run`
  starts it, every tick confirms the process is alive and restarts it with one log
  line if it is not, and `admits()` REFUSES every Agda task while it is down.**
  The 14 GB per-process backstop and the 8 percent system-free floor are C-12's
  and they return with it.
- **A14. C-12's TIERED CONCURRENCY IS RESTORED.** The design pinned
  `AGDA_SLOTS = 2` and silently dropped C-12's WIDE tier, halving throughput
  without saying so. A task declares its tier in its table row. **WIDE admits up
  to FOUR concurrent Agda writers at `-M8g`; HEAVY admits at most TWO at
  `-M12g`.** `admits()` keeps the worst-case heap sum at or under 32 GB across
  mixed tiers, and it fills the third and fourth slots only when system free
  memory reads above 25 percent. **R13's one caliber becomes one caliber PER
  TIER**, and a record carries its tier so two measurements are compared only
  within a tier.
- **A15. THE PROGRAM'S OWN CALIBER IS SPLIT.** A per-task acceptance run uses
  `-M8g`, the worker's caliber, so an acceptance measurement compares directly
  with the run record beside it. **A whole-tree `make check` uses `-M16g`**,
  which is C-12's orchestrator caliber, because that run holds the machine alone.
  The design named neither.

## 1. What this is

*In force since the POD cutover of 2026-08-18, commit `fc676cb`. `AGENTS.md` holds the shared Boundary, and `dev/ARCHIVE.md:214` records `dev/ORCHESTRATION.md` as archived.*

The POD replaces Bedrock's human orchestrator with a program.

**The architecture, in one paragraph.** The POD is a program and not a model. It
reads a state file, admits a brief's branches into a rule table, spawns a worker,
runs one acceptance runner, reads six facts out of that runner, matches them
against the table, and writes state. It makes no judgement. Three models attach
and none runs the loop. The mathematician writes briefs and holds all judgement.
The maintainer writes new table rows, in batches, and a mechanical replay admits
or refuses each new row. The adversarial heads attack a return. The unit of work
is one deliverable proof obligation. A task that matches no row is PARKED. At
three parked tasks the whole loop stops and the owner gets a push.

**What the POD keeps, what it voids and what it re-homes.** It VOIDS two process
documents: this repository's `AGENTS.md` and `dev/ORCHESTRATION.md`. It SETS
ASIDE the DD series in `dev/PLAN.md` section 3, under A7, and section 7.1
carries every DD ruling to a new enforcement point. It KEEPS every artifact:
`agents/tasks/`, `dev/JOURNAL.md`, `dev/LESSONS.md`, `dev/ledger.toml`, and the
measurements. It
also keeps `dev/STYLE-agda.md` and `dev/STYLE-i18n.md`, which are style documents
and not process rules, and which the gates of section 7.1 read. **The goal does
not change, and the two trophies are NOT in the same state.** `L ⊨ AC` has
landed, as `L⊨ZFC` at `src/Landmarks.lagda.md:76-77`. `L ⊨ GCH` has NOT landed:
its statement type is `GCHStatement` at `src/L/GCH.lagda.md:59-60`, and no proof
term for it exists under `src/`. Measured on 2026-08-17: `src/Landmarks.lagda.md`
is 78 lines long and the string `GCH` occurs zero times in it.

**THREE RULES OF `AGENTS.md` ARE DROPPED WITH IT AND NOTHING REPLACES THEM.** The
document taxonomy, which puts user documents trilingual under `docs/<lang>/`,
keeps developer documents in English only, and makes `README.md` follow the user
rule; the obligation that a new top-level directory gets a `README.md`; and the
ban on an unpinned or globally installed dependency. Each one needs an owner
ruling before the cutover: keep it as a clause of section 3.1, or accept the
loss. **Three more candidates are NOT lost:** the controlled style is clause W10,
the English-first authoring order is clause W11, and the `_build/` lifecycle
declaration is clause W12.

**Read this first if you build it.** Two things are still not buildable: the
acceptance test cost, unmeasured across a 34-fold band at gap B3, and the three
model IDs, unresolved at gap B4. Day 1 and day 2 settle both.

## 2. The 27 architecture decisions, AD1 to AD27

*In force since the POD cutover of 2026-08-18, commit `fc676cb`. `AGENTS.md` holds the shared Boundary, and `dev/ARCHIVE.md:214` records `dev/ORCHESTRATION.md` as archived.*

| AD# | The decision | In | AD# | The decision | In |
|---|---|---|---|---|---|
| AD1 | The POD is a program, not a model. It makes no judgement | 1, 5.1 | AD15 | The maintainer runs in batches, every 12 hours or at 3 parked | 6.7, 8.1 |
| AD2 | A maintainer model writes new table rows. It does not run the loop | 6.1, 6.7 | AD16 | A parked task resumes by automatic re-dispatch of a fresh instance | 5.5, 5.1 |
| AD3 | All judgement belongs to the mathematician | 6.4, 7.4 | AD17 | Concurrency is dynamic. A timed task gets the machine alone | 5.6 |
| AD4 | **A8 REPLACES THE FIRST HALF: `AGENTS.md` SURVIVES, rewritten in place.** `dev/ORCHESTRATION.md` becomes void AT `[L9.7]` and is LIVE until it. **A7 replaces the second half: the DD series is SET ASIDE, not void, and every DD row takes a disposition.** Artifacts are kept | 1, 3.1, 7.1 | AD18 | The launcher is the existing `dispatch.py`, extended and tracked | 6.2, 9.1 |
| AD5 | The goal is unchanged: both trophies | 1 | AD19 | The table is tracked. Runtime state is not. Every transition logs | 5.3 |
| AD6 | Clean cutover. `pre-pod-2026-08-17` is the rollback anchor | 9.1, 9.2, 9.3 | AD20 | A Chinese daily digest, plus an immediate push on stop | 8.1, 8.3 |
| AD7 | The rollback criterion is the owner's. The digest prints two numbers | 8.2 | AD21 | A cheap pre-flight on the brief before dispatch | 6.5 |
| AD8 | One TOML table. Every row carries a scope. Amended by A3 | 4.1, 4.2, 4.4 | AD22 | The trophy spec surface is protected and derived | 7.3, 5.4 |
| AD9 | Prose and branches. The branch is authoritative | 4.1, 6.3 | AD23 | Keep the LINT class. Rewrite the rest. Surveys keep function | 7.1, 7.4 |
| AD10 | A new row is admitted by mechanical regression replay | 4.5 | AD24 | mathematician: opus 5 max; adversarial: fable 5 max | 6.1 |
| AD11 | A branch may match only six facts. Facts 1, 2 and 3 are amended by A5 and A1 | 4.3, 4.7 | AD25 | coder: sonnet 5 high; adversarial: opus 5 high | 6.1 |
| AD12 | The unit of work is one deliverable proof obligation | 6.3, 5.2 | AD26 | Heads live in a config file. A change binds new tasks only | 6.1 |
| AD13 | DONE: `agda --safe` exit 0, unresolved obligations did not increase. A5 gives it a runner; R4 reads the row's `outcome`. See gap M10 | 5.4, 7.2 | AD27 | Adversarial review fires two ways | 6.6 |
| AD14 | On no match, PARK. At 3 parked, the loop stops | 5.5 |  |  |  |

## 3. The rule set, ONE list

*In force since the POD cutover of 2026-08-18, commit `fc676cb`. `AGENTS.md` holds the shared Boundary, and `dev/ARCHIVE.md:214` records `dev/ORCHESTRATION.md` as archived.*

**Every rule sits in this one list and carries an `enforced by` value of exactly
`program`, `hook` or `agent discipline`.** A rule that can name none of the three
is deleted rather than written, so no cell below is empty. R1 to R18 are the
program's own. W1 to W15 are the written clauses, and section 3.1 gives every one
of them verbatim. W1 to W9 are A7's WRITTEN RULE dispositions; W10 to W15
carry a standing repository rule that `AGENTS.md` holds and no DD code names.

| # | Rule | enforced by | The point that fires it |
|---|---|---|---|
| R1 | A branch matches only the six facts of AD11 | `program` | The table loader and pre-flight check P4, section 6.5 |
| R2 | The branch is authoritative. Prose never routes anything | `program` | The router reads the `[row.when]` block only, section 4.5 |
| R3 | A new row must not move any record an existing row already matches. Expiry is exempt | `program` | `replay()`, section 4.5.1. It runs on every table edit |
| R4 | A GO close needs all six conjuncts of section 5.4. A NO-GO close needs conjuncts 5 and 6 | `program` | The acceptance runner and the DONE handler, section 5.4 |
| R5 | No match parks the task. Three parked tasks stop the loop | `program` | `route()` returns `(None, None)`, section 4.5.1; the counter in section 5.5 |
| R6 | Write the log line before the state file, and fsync both | `program` | `emit()`, section 5.3 |
| R7 | The program never guesses a fact. It drops a return it cannot measure | `program` | Section 4.5.4. The dropped-return count prints in the digest |
| R8 | The program commits by explicit path, derived from the task's own scope. It never pushes | `program` | A program property. It never runs `git add -A`, section 7.1 |
| R9 | A change to a spec surface declaration signature blocks and needs a named approval | `program` | `check-spec-surface.py --check` at conjunct 5; the same file at the `commit-msg` hook, sections 7.3 and 5.4 |
| R10 | The program retrieves the archive and the literature. The worker never surveys by hand | `program` | The brief builder injects the hit list, section 7.4 |
| R11 | The head is resolved once, at dispatch, and copied into the tracked log | `program` | The dispatch log line carries `model`, `effort` and `heads_sha256`, section 6.1 |
| R12 | A timed task holds the machine alone. Nothing else starts beside it | `program` | `admits()`, section 5.6 |
| R13 | Every POD-owned Agda run uses one caliber, and the record carries it | `program` | `run_agda()`, section 4.3.1 |
| R14 | The LINT class of section 7.1 runs before every commit and again at every task close | `hook` | `scripts/git-hooks/pre-commit`, cutover step 11; and acceptance conjunct 6, section 5.4 |
| R15 | The maintainer writes ONE declared path. A return that touched any other path, tracked or untracked, is refused | `program` | `maintainer_scope_ok()`, at the batch return and before the replay, section 6.7. DD0 |
| R16 | A change to this rule set, to section 3.1 or to `heads.toml` needs a named owner approval | `hook` | `check-spec-surface.py --msg-file` at `commit-msg`, and `--check` at conjunct 5, sections 7.3 and 5.4. DD0 |
| R17 | Every brief carries the LAWS bundle for its derived kind, and the kind is derived from the write scope and never declared | `program` | The brief builder, section 6.3; pre-flight P21 refuses a brief with an empty or absent LAWS block |
| R18 | A task that adds a master under `src/` writes its import line into `src/Everything.lagda.md`, and the brief's write scope names that file | `program` | The brief builder adds `src/Everything.lagda.md` to `## SCOPE (write)` whenever the scope names a new master path; pre-flight P16 and acceptance conjunct 3 |
| W1 | The two towers and the bridge are a CANDIDATE architecture. Only a measurement moves it | `agent discipline` | Section 3.1, carried to the mathematician at every dispatch |
| W2 | Write it generic and share the maximum code between the two proofs | `agent discipline` | Section 3.1, to the mathematician and the coder |
| W3 | Name the widest unmeasured term and its probe. One estimate, with its basis | `agent discipline` | Section 3.1, to the mathematician |
| W4 | Archive retired code and never delete it. Price the rewrite first | `agent discipline` | Section 3.1, to the mathematician and the coder |
| W5 | One canonical home per rule, and it names its enforcer. No self-chosen glossary entry | `agent discipline` | Section 3.1, to every slot |
| W6 | No mathematical prose until both trophies are proved | `agent discipline` | Section 3.1, to every slot |
| W7 | Index the hull by the meta term algebra `Code`, never by object-language formulas | `agent discipline` | Section 3.1, to the mathematician |
| W8 | Read the injected LITERATURE block first on a provability question, and stop if it settles it | `agent discipline` | Section 3.1, to the mathematician |
| W9 | A one-off owner instruction binds only the task it names. It is never evidence about what an agent may do | `agent discipline` | Section 3.1, to every slot. DD0 part 3 |
| W10 | The audience picks the style: Chinese Tech Doc Style to the owner, ASD-STE100 to every other reader | `agent discipline` | Section 3.1, to every slot |
| W11 | Author a document in English first, then translate, then cross-check the Chinese against the Japanese | `agent discipline` | Section 3.1, to every slot |
| W12 | Declare a `_build/` file's lifecycle when you create it, or move it out | `agent discipline` | Section 3.1, to every slot |
| W13 | Place a new document by AUDIENCE. A developer document is English only and is never translated | `agent discipline` | Section 3.1, to every slot |
| W14 | A new top-level directory carries a `README.md` in the commit that creates it | `agent discipline` | Section 3.1, to every slot |
| W15 | Never add an unpinned dependency and never add a globally installed one | `agent discipline` | Section 3.1, to every slot |

**W1 to W9 are A7's WRITTEN RULE dispositions. W10 to W15 carry a standing
repository rule that `AGENTS.md` holds and no DD code names.** Amendment A9 kept
W13, W14 and W15, which section 1 first recorded as lost.

### 3.1 The written rules, executed by agent discipline

*In force since the POD cutover of 2026-08-18, commit `fc676cb`. `AGENTS.md` holds the shared Boundary, and `dev/ARCHIVE.md:214` records `dev/ORCHESTRATION.md` as archived.*

**A dispatched agent READS this section and FOLLOWS it. Nothing mechanical checks
one clause of it.** That is why each clause is short enough to hold and why the
program carries it: `dev/pod/instructions/<slot>.md` holds the clauses for that
slot and the program injects the file ahead of the brief at every dispatch
(section 6.1). **The clause text below is the rule; the summary in section 3 is not.**

| # | Carries | Injected into | The clause, verbatim |
|---|---|---|---|
| W1 | DD2 | mathematician | The two towers and the bridge are a candidate architecture and not a ruling. Only a measurement changes the architecture, and an argument never does. Queue the architecture decision as a task whose obligation is that measurement. That task is `[LJ-2.5]`, a live row in `dev/PLAN.md` section 11. |
| W2 | DD4 | mathematician, coder | Write the mathematics once at a generic carrier and instantiate it, so both proofs share the maximum code. State this rule in the brief and answer it in the return. A deadline does not permit the fixed form: report the conflict and stop for a new price. |
| W3 | DD8 | mathematician | Name the widest unmeasured term in the brief, and name the probe that measures it. Give an estimate as one best-effort number. Name the estimate's basis: a probe, a delivered comparable, or a survey. Write the probe in `agents/tasks/<CODE>/`, beside the brief and the report, and never under `src/`. The probe is tracked and is never deleted. Run it while your task is live, because nothing typechecks it after the task closes. Write the report first, and write it incrementally. |
| W4 | DD13 | mathematician, coder | Move a retired MODULE to `archive/` and never delete it. The rule is module-granular: a dead fragment inside a live master, with no consumer, is deleted, and the `dev/LESSONS.md` entry that cited it is restated generally. Record in `dev/ARCHIVE.md` what the module is, why it left, where it was last green, and what would reopen it. Price the ideal form written fresh today, then compare it with the chapter you have. |
| W5 | DD19 | every slot | Each rule has one canonical home and names its enforcer: program, hook or agent discipline. Never write a rule in two files. Never add a `dev/glossary.toml` entry that an agent chose. A term the glossary lacks is settled by two dispatches, queued like any other task: a sourced provenance dossier, then an adversarial review that returns PASS or FAIL per term. A PASS lands the entry and the landing commit cites both. A FAIL or a genuine fork escalates that term to the owner. A ruling is a table row, an episode is a `dev/JOURNAL.md` entry, a law is a `dev/LESSONS.md` entry, and a fact belongs in exactly one of the three. |
| W6 | DD23 | every slot | Write no mathematical prose until both trophies are proved in the tree. Write only code, its own comments and the project records. The prose phase opens when the double trophy lands, and not before. |
| W7 | DD27 | mathematician | Index the constructible hull by the meta term algebra `Code`, never by object-language formulas. An object-language index blocks the condensation criterion at hull parameters. |
| W8 | DD28 | mathematician | Read the injected LITERATURE block before you write Agda for a provability question. Stop the task when the literature shows the shape is an axiom with no condition this tree meets. A literature NO-GO is a full return and not a failure. |
| W9 | DD0 | every slot | A one-off instruction from the owner binds ONLY the task it names. It changes no ruling, and it is NOT evidence about what an agent may do. Never derive a standing rule from a one-off owner instruction. Ask the owner for a ruling, and wait. |
| W10 | none, a standing repository rule | every slot | Write to the repository owner in Chinese, in the Chinese Tech Doc Style: accuracy before rhetoric, one point per paragraph, one term per concept, and the condition before the action it governs. Write to every other reader in ASD-STE100 Simplified Technical English: one meaning per word, active voice, simple tenses, one instruction per sentence. A dispatched agent writes ASD-STE100 and never Chinese, because its reader is the program and the reviewer. Never add a number, a date or a certainty the evidence does not give. Never use an em dash in any language. Never use half-width sentence punctuation in CJK prose. |
| W11 | none, a standing repository rule | every slot | Author a new document in English first. Translate it into Chinese and Japanese after the English is settled. Then cross-check the Chinese against the Japanese for drift. Never translate a developer document under `dev/`. |
| W12 | none, owner ruling 2026-08-13 | every slot | Every file you create under `_build/` declares its lifecycle in `dev/build-manifest.toml` when you create it: the condition under which it may be deleted, and the condition under which it moves to a permanent home. A file with no declared class moves out of `_build/` instead. `_build/` is a temporary folder and not a rubbish bin. |
| W13 | none, kept by A9 | every slot | Place a new document by AUDIENCE. A user document is trilingual under `docs/<lang>/`. A developer document is English only and is never translated. A `README.md` follows the user rule. |
| W14 | none, kept by A9 | every slot | A new top-level directory carries a `README.md` in the same commit that creates it. |
| W15 | none, kept by A9 | every slot | Never add an unpinned dependency and never add a globally installed one. `requirements-dev.txt` pins every one. |

**Two losses this section does not repair, and both are stated rather than
absorbed.** W2 loses the per-dispatch REPETITION that `check-dd4-stated.py` gave
it: that gate's docstring at `:14` records 11 briefs carrying no DD4 at all, and
gap M4 records the same decay at 102 of 112 briefs over five days. An injected
file is read by a model and checked by nobody. W1 loses its ADDRESS: `[LJ-2.5]`
was a row in `dev/PLAN.md` section 11, which `dev/pod/queue.toml` replaces, so
the clause names a queued task whose obligation is the measurement. **The other
planned rows of `dev/PLAN.md` section 11 migrate the same way, as REQUEST
entries in `dev/pod/queue.toml`, so the route survives the replacement of that
section.**

**W1'S ADDRESS IS DANGLING TODAY, and this states it rather than absorbing it.**
MEASURED 2026-08-18: `dev/pod/queue.toml` holds 19 `[[task]]` entries, one per
non-`L9` PLANNED row of `dev/PLAN.md` section 11 plus `LJ-1.386`, and **no entry
carries the code `LJ-2.5`**. The clause text of W1 below still reads `a live row
in dev/PLAN.md section 11`, and section 11 is SET ASIDE by amendment A7. So
clause W1 names an address that the queue does not hold and that the plan no
longer operates. **The repair is one queue entry**, a REQUEST with
`code = "LJ-2.5"` and no `brief`, plus the same edit to the W1 clause text here
and to the `**W1**` clause of `dev/pod/instructions/mathematician.md` and of
`dev/pod/instructions/mathematician_adversarial.md`. Both slot files are
guarded, so the edit needs a named owner approval under R16.

## 4. The table

*In force since the POD cutover of 2026-08-18, commit `fc676cb`. `AGENTS.md` holds the shared Boundary, and `dev/ARCHIVE.md:214` records `dev/ORCHESTRATION.md` as archived.*

AD8, AD9, AD10 and AD11.

### 4.0 Where every POD file lives

Every tracked POD configuration file lives in `dev/pod/`. A brief stays under
`agents/tasks/`, and the runtime state sits outside `_build/`.

| Path | Tracked | What it holds |
|---|---|---|
| `dev/pod/table.toml` | yes | The one rule table, AD8. System rows AND live task rows |
| `dev/pod/queue.toml` | yes | The task queue. The mathematician writes it, section 5.2 |
| `dev/pod/heads.toml` | yes | The five heads and the limits, AD26 |
| `dev/pod/instructions/<slot>.md` | yes | One standing instruction file per head, section 6.1 |
| `dev/pod/spec-surface.toml` | yes | The derived signature snapshot, AD22 |
| `dev/pod/proposals/<ts>.toml` | yes | One maintainer batch's proposed rows, section 6.7 |
| `dev/pod/replay-corpus.jsonl` | yes | The frozen regression records, AD10 |
| `dev/pod/transitions/<YYYY-MM>.jsonl` | yes | The transition log, AD19 |
| `scripts/pod/pod.py` | yes | The runner, section 5.0 |
| `.pod-state/state.json` | no | The runtime state, AD19 |
| `.pod-state/logs/` | no | Worker transcripts |
| `.pod-state/witness/` | no | The fact 3 witness modules, section 4.7 |
| `dev/JOURNAL.md` | yes | The episode record, one entry per episode. It is KEPT and it needs a writer: the mathematician writes the entry at every close, and the adversarial reviewer writes one for the return it attacked. The transition log holds FACTS and can never hold a finding |

`.gitignore` gains one line, `.pod-state/`. That line matters twice: it keeps the
runtime state out of the index, and it hides the witness modules from fact 4,
because `git status --untracked-files=all` does not list an ignored path.

Four picks. **Not `_build/`**: the `clean:` target of the `Makefile` empties it, so
`make clean` would erase the runtime state. **One log file per month**: at about
124 KB per median day (5.3.1), monthly rotation holds any git blob under 11 MB.
**JSONL and not TSV**: a changed-file list in a TSV cell needs an escape
convention. **Retention for `.pod-state/logs/`: 30 days after the task reaches
DONE or PARKED**, which `prune_logs(30)` performs in rule (e), because the
comparable holds 931 MB over 1,017 files.

### 4.1 One vocabulary, two surfaces

**One grammar, and the brief's branch block IS the task's rows.** The
mathematician writes branches in the brief. At admission the program APPENDS each
branch to `dev/pod/table.toml` as a row with `scope = "task:<CODE>"`, RENAMES the
branch id to `task-<code>-<branch-id>` per section 4.2, and fills `added`,
`added_by = "mathematician"` and `reason` from the branch heading. **The rename
runs at admission and nowhere else**, so ONE file holds every row the router
reads: the system rows, the live task rows and the expired task rows.

**THE STEP THAT PERFORMS IT.** `admit_rows(code, brief)` is the function, and
**rule (f) of the tick calls it**, after the pre-flight and before `launch()`.
Nothing else writes a task row, and putting it there gives four properties.

```python
def admit_rows(code, brief):                 # scripts/pod/table.py
    """Append this brief's branches as task rows. Return True on ADMIT."""
    rows = [namespace(code, b) for b in branches_of(brief)]   # 4.2's rename
    old  = load_table(TABLE)
    if rows_of_scope(old, code) == rows:     # IDEMPOTENT. Attempt 2 writes nothing.
        return True
    new  = [r for r in old if r["scope"] != "task:" + code] + rows
    if replay(old, new, corpus())[0] != "ADMIT":              # R3, section 4.5.1
        return False
    write_table(new)              # tmp -> fsync -> rename -> fsync(dir), section 5.3
    git_commit([TABLE], "pod: admit " + code)                 # R8, explicit path
    return True
```

1. **It is idempotent.** A second instance re-writes nothing when the branch block
   is unchanged. A CHANGED brief replaces that code's rows, which is a remove plus
   an add, so section 4.5.1's third rule already guards it.
2. **R3 runs on it**, because `admit_rows()` calls `replay()` before it writes, so
   R3 holds at admission exactly as it holds for a maintainer batch.
3. **A failure never half-writes.** `replay()` runs before the write, and the write
   is temporary file then rename. On a REJECT, or on an `OSError`, `admit_rows()`
   returns False, rule (f) parks with `reason: "admission"`, and NO row enters the
   table. Rule (a2) retries on the next table edit.
4. **The commit is separate from the write.** A failed `git_commit` leaves the rows
   uncommitted in the tracked file; `pod stop` commits them, and sections 9.1 and
   9.2 run `pod stop` before any checklist that requires a clean tree.

Three reasons decide the one-grammar pick. AD8 says ONE table. AD10's replay
compares routings, and one router produces comparable routings. AD21's pre-flight
must refuse a seventh fact, and one closed key list makes that check one line.
**The alternative**, a translator from comparison strings into rows, can change a
routing with no table edit, so it is refused.

### 4.2 The TOML schema

The loader refuses an unknown key, so a typo never becomes a silent no-match row.

```toml
[meta]
schema = 1                  # int, required. The loader refuses any other value.
vocab = "six-facts/1"       # str, required. Bumped only when AD11 changes.

[[row]]
id = "sys-heap-wall"        # str, unique table-wide, kebab-case. See B7 below.
scope = "system"            # "system" | "task:<CODE>". See 4.6.
priority = 100              # int >= 0. Lower wins. See 4.4.
action = "park_and_split"   # str, from the closed set below.
# head_slot = "coder_adversarial"  # required when action is "escalate", absent otherwise.
# outcome = "go"            # "go" | "no-go". Required when action is "done", absent
                            # otherwise. It never routes. See A6.
added = 2026-08-17          # TOML local date, required.
added_by = "maintainer"     # "maintainer" | "owner" | "mathematician".
reason = "one sentence"     # str, 200 characters or fewer.
expired = false             # bool, default false. See 4.6.
expired_at = 2026-09-01     # date. Present only when expired is true.

  [row.when]                # THE BRANCH. Authoritative, AD9.
  heap_wall = true          # Every key is AND-ed. A row holds no OR.
```

**`id` is unique TABLE-WIDE, and admission is what makes that true.** A branch id
is a bare word inside one brief, so two briefs both writing `go` would collide.
**`admit_rows()` namespaces a branch id at admission**, to
`task-<code>-<branch-id>`, with the code lower-cased and every dot a dash, so
`[LJ-1.386]`'s `go` branch becomes `task-lj-1-386-go`. Pre-flight P7 checks the
BRIEF-LOCAL ids, because a brief cannot see the table.

**Two fields are CONDITIONAL, which is why the block above comments them out: a
row carrying both would be illegal.** `head_slot` is required exactly when
`action` is `escalate` and absent otherwise, and its value must name a slot in
`heads.toml`; pre-flight P11 tests both directions. Without it the loader would
refuse SYSTEM ROW 2 of 4.8, the coder row of 6.6 and the escalate branch of 6.4.
`outcome` is required exactly when `action` is `done`.

**`outcome` is a declaration and never a matcher.** It sits outside
`[row.when]`, so the router never reads it. A `done` branch that closes a task
whose answer is NO writes `outcome = "no-go"`, which is how pre-flight P19
admits it under A6. The digest counts GO and NO-GO closes from this field.

**`action`. This set is closed, so the program makes no judgement. Every one of
the eight names the function that performs it, and none is unimplemented.**

| action | What the program does | Performed by |
|---|---|---|
| `done` | Close the task. AD13 | rule (c), the DONE limb, through `commit_task()` |
| `accept` | Record the return as expected. Do not close. Continue | rule (c), the `accept` limb |
| `park` | Park the task. Continue with the others. AD14 | `apply()`, section 5.1 |
| `park_and_split` | Park, and append a queue REQUEST entry, 5.2 | `apply()`, through `queue_append(split_entry(...))` |
| `redispatch` | Fresh instance, same brief. AD16 | `apply()` |
| `redispatch_narrower` | Fresh instance, write scope cut to the failing file | `apply()`, through `first_failing_target()` |
| `escalate` | Dispatch the head in `head_slot` against this return. AD27 | `apply()` sets `t.head_slot`; rule (f) dispatches |
| `stop_loop` | Stop the loop and push to the owner. AD14 and AD20 | `apply()`, which returns STOP to rule (c) |

`escalate` covers both sides of AD27, so no per-head action is needed.

### 4.3 The six-fact vocabulary

**`[row.when]` keys. This list is closed. Nothing outside it may appear.**

| Key | Type | Fact | Meaning |
|---|---|---:|---|
| `exit_code` | int | 1 | equal. The ACCEPTANCE RUNNER's code, A5 |
| `exit_code_in` | list of int | 1 | member |
| `exit_code_absent` | bool | 1 | true when conjunct 1's Agda deadline passed |
| `error_class` | str | 2 | equal. One of the eleven class names |
| `error_class_in` | list of str | 2 | member |
| `obligations_delta_min` | int | 3 | delta >= value |
| `obligations_delta_max` | int | 3 | delta <= value |
| `changed_files_any` | list of glob | 4 | one changed path or more matches |
| `changed_files_none` | list of glob | 4 | no changed path matches |
| `changed_files_all_within` | list of glob | 4 | every changed path matches one |
| `changed_files_count_min` | int | 4 | count >= value |
| `changed_files_count_max` | int | 4 | count <= value |
| `seconds_min` | float | 5 | wall seconds >= value |
| `seconds_max` | float | 5 | wall seconds <= value |
| `heap_wall` | bool | 6 | equal |

Globs match with `fnmatch.fnmatchcase` against the repository-relative path, and
the loader refuses an empty `[row.when]`, which would match everything.

**Facts 1 and 2 are the ACCEPTANCE RUNNER's, under A5.** The runner of section
5.4 owns the six conjuncts of AD13 and Agda is one of them, so one exit code covers
every way a task can fail and the number of facts stays six.

| `exit_code` | The runner ended because |
|---:|---|
| 0 | Every one of the six conjuncts held |
| 42 | Conjunct 1's Agda run reported a type, scope, parse or safety error |
| 251 | Conjunct 1's Agda run hit the GHC heap wall |
| 1 | A conjunct other than 1 failed. Fact 2 names which one |
| absent | Conjunct 1's Agda deadline passed. `exit_code_absent = true` |

**The runner owns exactly ONE deadline, `agda_deadline_s` of section 6.1.** It is
conjunct 1's, and section 5.4 shows how it reaches `exit_code`. `worker_deadline_s`
kills a hung WORKER before any acceptance run starts, so it is not a runner
deadline and never makes `exit_code` absent. Conjuncts 2 to 6 have no deadline,
each being measured in hundredths of a second.

**The eleven error classes, in snake case.** Six come from Agda, through conjunct
1: `termination`, `universe_level`, `unsolved_meta`, `heap_wall`, `timeout`,
`other`. Five come from the runner's other conjuncts and are exact by
construction, because the runner reads its own checker's exit code:
`obligations_up` (conjunct 2), `closure_open` (3), `unbound_hyp` (4),
`spec_surface` (5), `lint` (6). A green run carries `"error_class": null` and
matches no class key, so a branch that must select a green run tests
`exit_code = 0`. **The log corpus, named once:** every corpus figure below comes
from `.claude/skills/codex-dispatch/.state/logs`, 1,017 files, measured on
2026-08-17. That directory is UNTRACKED (`git check-ignore -v` reports
`.gitignore:19`), so section 9.2 must salvage it before any `git clean`.

#### 4.3.1 How the program measures each fact

`run_agda()` is the ONE place the POD starts Agda. The acceptance runner of
section 5.4 calls it for conjunct 1 and the witness meter of section 4.7 calls it
per obligation. It reads the process object and never a transcript. **Its `rc`
and `agda_class` are Agda's, not the record's**: section 5.4 folds them into
facts 1 and 2, and only there.

```python
# scripts/pod/facts.py  (NEW, about 130 lines)
import os, re, subprocess, time
from pathlib import Path

ERR  = re.compile(r"(?:^(?P<file>[^\s:]+):(?P<line>\d+)[.,]\d+[^\n]*?)?"
                  r"error: \[(?P<cls>[A-Za-z.]+)\]", re.M)
HEAP = re.compile(r"^agda: Heap exhausted;", re.M)
SAFE = re.compile(r"^\{-#\s+OPTIONS\b[^#]*--safe", re.M)
CAP  = "-A64m -I0 -M8g"          # R13, AMENDED BY A14 and A15. One caliber PER
                                 # TIER: WIDE is -M8g at four concurrent, HEAVY
                                 # is -M12g at two. A15: a per-task acceptance
                                 # run uses this; a whole-tree make check uses
                                 # -M16g, C-12's orchestrator caliber.

CLASS = {"TerminationIssue": "termination",
         "UnequalSorts": "universe_level", "UnequalLevel": "universe_level",
         "UnsolvedMetaVariables": "unsolved_meta",
         "UnsolvedInteractionMetas": "unsolved_meta",
         "UnsolvedConstraints": "unsolved_meta",
         "MetaCannotDependOn": "unsolved_meta"}

def classify(rc, names, heap, timed_out):
    if timed_out: return "timeout"
    if heap:      return "heap_wall"
    if rc == 0:   return None                  # a green run has no class
    if not names: return "other"               # the shape a missing file makes
    return CLASS.get(names[0], "other")        # FIRST name in output order

def run_agda(target, root, deadline_s, slots, include=()):
    head = Path(root, target).read_text("utf8", "replace")[:4000]   # absolute wins
    argv = (["agda"] + ["--include-path=" + p for p in include]
            + (["--safe"] if SAFE.search(head) else []) + [str(target)])
    env  = dict(os.environ, GHCRTS=CAP)
    start = time.monotonic()
    try:
        p = subprocess.run(argv, cwd=root, env=env, capture_output=True,
                           text=True, timeout=deadline_s, start_new_session=True)
        rc, out, timed_out = p.returncode, (p.stdout + p.stderr), False
    except subprocess.TimeoutExpired as e:
        rc, out, timed_out = None, (e.stdout or b"").decode("utf8", "replace"), True
    seconds = time.monotonic() - start
    names = [m.group("cls") for m in ERR.finditer(out)]
    heap  = rc == 251 or bool(HEAP.search(out))
    return {"rc": rc, "agda_class": classify(rc, names, heap, timed_out),
            "seconds": round(seconds, 2), "heap_wall": heap, "out": out,
            "caliber": CAP, "safe": "--safe" in argv, "concurrency": slots,
            "error_names_all": names}          # provenance, NOT matchable
```

**`--safe` is read and never assumed.** Measured over `git ls-files -z
agents/tasks`, `.agda` and `.lagda.md`, excluding `archive/`: 426 tracked live
files, of which 417 declare `--safe` and 9 do not. A hard-coded `--safe` would
make those 9 fail on a safety error and record a wrong class.

**Agda's own codes, MEASURED, and 1 is not among them.** Agda 2.8.0 returns 0 on
success, 42 on any type, scope, parse or safety error, and 251 on GHC heap
exhaustion; a missing input file also returns 42, with no bracketed name. Two
returns confirm the codes: `agents/tasks/LJ-1-266/lj-1.266-report.md:73` reads
`MEASURED "Heap exhausted" at 8,192 MB, exit 251`, and
`agents/tasks/LJ-1-375/lj-1.375-report.md:144-148` reads `exit 42, 2.44 s` with
`error: [UnequalSorts]`. **A5 uses that gap: 1 is free, so the runner takes it
for its own five conjuncts.** **Exit 42 is a single generic code**, shared by
`[NotInScope]`, `[UnsolvedConstraints]`, `[UnequalTerms]`, `[FileNotFound]` and
`[CoInfectiveImport]`, so a row that separates two Agda failures tests fact 2 and
never fact 1 alone.

**Fact 2, the error class. The regex takes no location, and the alternative was
measured.** Agda prints many tags with no `file:line.col` prefix. Over the log
corpus, 3,395 error tags and 49 distinct names, a form anchored on that prefix
matched 3,097 and missed 298, and the miss was not uniform: it lost 30 of 30
`UnsolvedConstraints`, the class section 6.4 routes a NO-GO on. **The form above
matches 3,395 of 3,395.**

The six Agda classes and their names. No parser produces the five runner classes.

| Class | Agda names | Corpus count |
|---|---|---:|
| `termination` | `TerminationIssue` | 7 |
| `universe_level` | `UnequalSorts`, `UnequalLevel` | 40 + 27 |
| `unsolved_meta` | `UnsolvedMetaVariables`, `UnsolvedInteractionMetas`, `UnsolvedConstraints`, `MetaCannotDependOn` | 75 + 31 + 30 + 6 |
| `heap_wall` | none. Exit 251, or the stderr string | 37 real lines |
| `timeout` | none. The POD's own deadline | not recorded today |
| `other` | the other 42 names | 3,179 |

Three parser rules, each disclosed as a choice. **Exit non-zero with an empty
name list classifies as `other`**, the shape a missing input file makes. **The
class is the FIRST name in output order**, which is Agda's print order and not a
judgement; `error_names_all` keeps the full list. **`universe_level` is exactly
`{UnequalSorts, UnequalLevel}`**, and gap M1 carries the cost.

**Fact 6, the heap wall. Two signals, and both are needed.** Agda emits no
bracketed name on a heap wall: it writes three lines to stderr and exits 251. Set
`heap_wall` true when the exit code is 251, OR when the child's own stderr carries
`agda: Heap exhausted;`, read from the same `subprocess.run` result and never from
a transcript. The string alone is not enough: over the log corpus `Heap exhausted`
appears on 472 lines and only 37 match `^agda: Heap exhausted;`.

**Fact 5, the seconds, is CONJUNCT 1's Agda wall and nothing else.** A5 moved
fact 1 to the runner and fact 5 deliberately did not follow, because every row
that uses it asks how long the PROOF took. **The witness runs of section 4.7 are
excluded too**, and recorded as `witness_seconds`, so a longer obligation list can
never read as a slower proof. `runs_all` keeps every other wall as provenance.

**`time_module()` is NOT the recorder.** At
`scripts/measure/check-timing.py:232` it runs a bare `agda` with no `--safe`,
under a bare `-M8g` (`:263`), and stashes the `.agdai` to force a COLD run; its
docstring measures 163.49 s against 133.69 s, which is 22.3 percent. **A
cross-caliber comparison is worse than no comparison**, so every second comes from
`run_agda()`, R13 states the rule, and every record carries `caliber`. Reports
quote USER seconds and `run_agda` measures WALL. **Fact 5 is also measured under
contention, so the record carries `concurrency`**, from `agda_holders()` at
`dispatch.py:422`; `matches()` refuses a seconds key against a record whose
`concurrency` is not 1. A contended cold gate measured 150.09 s against 133.69 s.

**Fact 4, the changed files. It is ONE snapshot, taken at exit, and it is scoped
to the task.** The command is `git status --porcelain --untracked-files=all`. The
flag is required: `git diff` cannot see an untracked file, and
`scripts/measure/check-timing.py:195` records that a brand-new master evaded that
gate entirely. Ignored paths do not appear, so `.pod-state/witness/` is invisible
here by construction.

**Why the EXIT snapshot and not the difference of two snapshots.** The program
commits only at DONE, so an earlier instance leaves its files dirty. On the
difference reading a second instance that edits the same already-dirty file
produces an EMPTY set, R7 drops the return and the task parks. The exit snapshot
is therefore CUMULATIVE, which is what 6.4's `no-go-stated` branch reads.

**The scope restriction stops task A being graded on task B's work.** Fact 4 holds
only the paths inside `write_paths(brief)` (`dispatch.py:1557`) or under
`agents/tasks/<CODE>/`; any other changed path goes to `changed_files_foreign`,
outside `facts`, and the digest counts it. **The union is disjoint between any two
live tasks by construction:** `territory_in_flight()` at `dispatch.py:1596`
refuses a second live task whose write scope overlaps. Without the restriction a
repository-wide snapshot would put another task's files into this record, which
misroutes every fact 4 key AND picks the verification target below. **Fact 3 is
section 4.7.**

#### 4.3.2 Which run is the verification run

The rule is mechanical and has FOUR cases. **They partition the input space.** The
input is `ch`, the fact 4 list above. Write `M` for "`ch` holds one `src/*.lagda.md`
master or more" and `P` for "`ch` holds one `.agda` or `.lagda.md` file or more
under `agents/tasks/<CODE>/`". The four conditions are `ch` empty, `M`, `¬M ∧ P`,
and `¬M ∧ ¬P ∧ ch` non-empty. They are disjoint and cover every list. Case 3
produces no record.

1. **`M`. The worker changed one `src/` master or more.** The target is
   `src/Everything.lagda.md`. That file imports 98 masters, and `check_closure()`
   at `scripts/gate/check-tree.py:131` fails the gate on any master missing from
   the import list, so one run covers the changed masters AND every consumer,
   which is AD13. A new master that `Everything` does not yet import is the one
   exception, and `check_closure_new()` at `check-tree.py:222` detects it; the
   runner runs each such file alone, then `Everything`.
2. **`¬M ∧ P`. The worker changed no master and one probe or more.** The targets
   are those changed `.agda` and `.lagda.md` files under `agents/tasks/<CODE>/`,
   in path order. `bedrock.agda-lib` reads `include: src agents/tasks`, so a probe
   there needs no extra flag. Conjunct 1 takes the FIRST failing run, or the LAST
   run when all pass. **That choice is arbitrary and it is disclosed here.**
3. **`ch` is empty. The worker changed nothing at all.** There is no verification
   target, so facts 1, 2, 5 and 6 have NO SOURCE. R7 applies: the program DROPS
   the return and PARKS the task with `reason: "no-change"`. **This is
   the second of two guards on a dead worker**; P19's delta floor is the first,
   and it stops a `go` branch closing on a zero delta.
4. **`¬M ∧ ¬P` and `ch` is not empty. The worker changed files that Agda cannot
   read.** A report-only return is the common shape; `write_paths()` at
   `dispatch.py:1557` admits it into SCOPE (write), so this case is inside the
   designed envelope. **The target list is empty, no Agda process starts, and
   CONJUNCT 1 HOLDS VACUOUSLY.** The record carries `agda_vacuous: true` outside
   `facts`, the digest counts it, and facts 1 and 2 then read the other five
   conjuncts alone: `seconds` is 0.0 and `heap_wall` is false. **A vacuous
   conjunct 1 cannot close a `go` branch**, because P19 forces every `go` branch
   to demand a negative delta.

### 4.4 Row ordering and conflict

The program collects EVERY matching row, sorts by one total order, and takes the
head. No judgement is involved. **The order, and A3 rules the first key:**

1. `action == "stop_loop"` first, whatever the row's scope. **A3.**
2. Then a `task:<CODE>` row before a `system` row. AD8.
3. Then `priority` ascending.
4. Then `id` ascending by byte order.

**Why A3 exists.** `sys-spec-surface` in section 7.3 is a system row with action
`stop_loop`. A5 already stops a surface change reaching `done`, because conjunct
5 forces `exit_code = 1` and `error_class = "spec_surface"`. But a task row keyed
on other facts still matches the same record: a branch reading only `seconds_min`
and `changed_files_count_max` never mentions fact 1. Without A3 that branch
outranks the system row and the loop keeps running.

`id` is unique, so step 4 always terminates. **The loader refuses two rows of the
SAME scope with the same priority**, which keeps step 4 an alarm and not a routine
tie-break. **Shadowing is reported, not refused:** the log line carries the
winner, and the digest re-runs the router's hit list over each record in the
window and prints how often a row lost, so no extra log field is needed. A row
that never wins in 30 days is a maintainer signal.

### 4.5 The replay

AD10. The test is REGRESSION ONLY and it needs no ground-truth label.

#### 4.5.1 The algorithm

**`route()` and `matches()` read the WHOLE record, not the facts object.** The
record carries `task`, `concurrency` and `caliber` at the top level and the six
facts nested under `facts`, which is exactly the shape section 4.5.2 stores and
section 5.3.1 logs. **The log format does not change: `facts` still holds exactly
six keys.**

**`concurrency` is read as a GUARD and never as a matcher.** No `[row.when]` key
names it, and it can only make a seconds key FAIL. The read is
`rec.get("concurrency")`, so a record that states no process count carries `null`,
never matches a seconds key, and raises no `KeyError`. A hand-copied `report`
record is exactly that case, and section 4.5.2 forbids guessing one.

```python
import fnmatch

def matches(when, rec):
    f  = rec["facts"]                        # the six. Nothing else is a fact.
    g  = fnmatch.fnmatchcase
    ch = f["changed_files"]
    for k, v in when.items():
        if   k == "exit_code":               ok = f["exit_code"] == v
        elif k == "exit_code_in":            ok = f["exit_code"] in v
        elif k == "exit_code_absent":        ok = (f["exit_code"] is None) == v
        elif k == "error_class":             ok = f["error_class"] == v
        elif k == "error_class_in":          ok = f["error_class"] in v
        elif k == "obligations_delta_min":   ok = f["obligations_delta"] >= v
        elif k == "obligations_delta_max":   ok = f["obligations_delta"] <= v
        elif k == "changed_files_any":       ok = any(g(p, q) for p in ch for q in v)
        elif k == "changed_files_none":      ok = not any(g(p, q) for p in ch for q in v)
        elif k == "changed_files_all_within":ok = all(any(g(p, q) for q in v) for p in ch)
        elif k == "changed_files_count_min": ok = len(ch) >= v
        elif k == "changed_files_count_max": ok = len(ch) <= v
        elif k == "seconds_min":             ok = rec.get("concurrency") == 1 and f["seconds"] >= v
        elif k == "seconds_max":             ok = rec.get("concurrency") == 1 and f["seconds"] <= v
        elif k == "heap_wall":               ok = f["heap_wall"] == v
        else: raise KeyError(k)              # R1. The loader caught it first.
        if not ok: return False
    return True                              # an empty block is refused by the loader

def route(table, rec):
    """Returns (row_id, action), or (None, None). No judgement, no fallback row."""
    hits = [r for r in table
            if not r["expired"]
            and (r["scope"] == "system" or r["scope"] == "task:" + rec["task"])
            and matches(r["when"], rec)]
    if not hits:
        return (None, None)                  # NO MATCH -> AD14 parks
    hits.sort(key=lambda r: (0 if r["action"] == "stop_loop" else 1,      # A3
                             0 if r["scope"].startswith("task:") else 1,
                             r["priority"], r["id"]))
    return (hits[0]["id"], hits[0]["action"])

def replay(old_table, new_table, corpus):
    """ADMIT the new table, or REJECT it and name every record it moved."""
    moved = []
    for rec in corpus:                       # each rec is one whole record
        old_id, old_act = route(old_table, rec)
        if old_id is None:
            continue            # was NO MATCH. It MAY become a match.
        new_id, new_act = route(new_table, rec)
        if (new_id, new_act) != (old_id, old_act):
            moved.append((rec["id"], old_id, old_act, new_id, new_act))
    return ("ADMIT", []) if not moved else ("REJECT", moved)
```

Three rules follow. A record that MATCHED must keep the same `row_id` AND the
same `action`. A record that did NOT match may become a match, because added
coverage is the reason to add a row. An EDIT is a remove plus an add, and the same
test guards it, which stops a maintainer widening a `when` block and capturing
another row's traffic. **`admit_rows()` is an edit of exactly that shape**, so R3
guards an admission too. The replay is pure arithmetic over frozen records.

#### 4.5.2 The corpus file

`dev/pod/replay-corpus.jsonl`, tracked, one JSON object per line, append only.
**One line is one RECORD. Its `facts` object is the six-fact TUPLE.** The corpus
record and the transition log line of section 5.3.1 carry the SAME shape, which
is why the replay can read a log line with no translation.

```json
{"id":"c-0412","task":"LJ-1.383","provenance":"probe-rerun",
 "source":"agents/tasks/LJ-1-383/Probe383.agda","recorded":"2026-08-18",
 "facts":{"exit_code":0,"error_class":null,"obligations_delta":0,
          "changed_files":["agents/tasks/LJ-1-383/Probe383.agda"],
          "seconds":1.99,"heap_wall":false},
 "caliber":"-A64m -I0 -M8g","concurrency":1,"witness_seconds":2.6,
 "error_names_all":[],"obligations_probe_red":false,
 "note":"lj-1.383-report.md:24-25 quotes 1.99 s USER; this row is WALL"}
```

- **`facts` holds exactly the six keys above.** Every other key is provenance and
  no `[row.when]` key names one; the loader refuses a `facts` object of any other
  shape. `concurrency` is the one provenance key `matches()` reads, as a guard.
- A record is never edited and never deleted, which is clause W4 again. An
  obsolete record gets `"retired": true` and stays.
- `provenance` is `live`, `probe-rerun` or `report`. A `report` record must carry
  `source` as `file:line`, and it writes `"concurrency": null` unless the report
  states the process count. No fact is ever guessed.

**`corpus()` is the reader, and it has exactly one definition.**

```python
def corpus(path=CORPUS):                     # dev/pod/replay-corpus.jsonl, 4.0
    """Every frozen record the replay must not move. Order does not matter."""
    return [r for r in map(json.loads, open(path, encoding="utf8"))
            if not r.get("retired")]         # a retired record stays and is skipped
```

**One writer puts a record in, and it is `emit()`.** Every transition line that
carries BOTH a `facts` object and a routing decision, which is every line rule (c)
writes, is appended to the corpus with `id` set to `"c-" + seq` and `provenance`
set to `live`. That is section 4.5.3's `live` stream, it makes the corpus a
subset of the log by construction, and `seq` makes the id unique and the append
idempotent after a crash. The other two streams are hand-loaded.

**DAY ONE, the corpus is EMPTY, and the consequence is stated rather than
hidden.** `replay()` iterates the corpus, so an empty corpus returns
`("ADMIT", [])` for every table and R3 guards nothing until the first record
lands. The build order bounds that window: cutover step 13 seeds the file empty,
day 4 fills it from the 426 tracked live probes plus one measured record per
runner class, and the first maintainer batch runs on day 7. **The digest prints
the corpus record count**, so an admission against an empty corpus is visible.

#### 4.5.3 The corpus is built forward, not reconstructed

**Facts 3 and 4 are reconstructible from history. Facts 1, 2, 5 and 6 are not.**

*Reconstructible, measured.* 1,326 of 1,395 commits name a task code and 298 of
the 503 distinct codes also have a task directory. For those 298 the changed-file
set comes from `git show --name-only` and an obligation delta from
`git show <sha>:<path>`, in 7.2 seconds. *Not reconstructible, measured four
ways.* The dispatch registry's 14 fields over 469 records hold no fact.
`returns.log` holds one status word over 496 lines. The codex transcripts name
`agda` in 6,508 shell blocks and **only 48 end the command chain with the agda
call**, the only case where the shell exit code is Agda's: **0.7 percent.** The pi
session store gives 73 Agda-shaped records over 127 files.

Three streams build the corpus instead.

1. **`live`.** `emit()` appends every routed record to the corpus file, per
   section 4.5.2. This IS the corpus in steady state. The other two streams exist
   only so the first table row has something to regress against.
2. **`probe-rerun`, the seed, restricted to the LIVE route.** 293 live task
   directories hold 438 `.agda` and `.lagda.md` files, of which 426 are tracked.
   The archive holds 221 more and **they are excluded**: their imports point at
   `archive/src/`, which `bedrock.agda-lib` does not put on the include path, so
   every one buckets to one scope error. The POD runs each live file under R13's
   caliber and a 300 s deadline. Fact 3 is 0 for every one, a failing record is a
   valid fixture, and the price is a projection that gap m1's probe settles.
   **A5 makes one thing explicit: fact 1 must be the RUNNER's code**, so the seed
   runs conjunct 1 per probe and conjuncts 2 to 6 ONCE.
3. **`report`.** 370 report files state `exit 0` and 101 state a non-zero exit,
   out of 673 reports. These are free-shape prose, so no parser is proposed and
   the maintainer copies a record by hand. **A report's exit code is Agda's and
   not the runner's**, so a report record is admissible only when all six facts
   can be established from the report. Otherwise R7 applies.

**Corpus balance.** The digest prints the record count per error class, and the
replay refuses a row whose `when` block names a class the corpus does not hold.
**The seed produces conjunct-1 classes only**, so day 4 adds one MEASURED record
per runner class by making each of conjuncts 2 to 6 fail on purpose and running
the acceptance runner over it. That doubles as the runner's own self-test.

#### 4.5.4 A return the program cannot measure

It drops the return, loudly, and never invents a field. The record is NOT written
to the corpus, the task PARKS, and the one line that goes to the transition log is
the PARK line itself, carrying the reason that names the missing fact. The digest
counts those lines. A half-record with a guessed exit code would license a row no
evidence supports, and the replay would then certify that row as safe.

### 4.6 Expiry

A `task:<CODE>` row is written for one task and dies with it. Exactly two events
trigger expiry, and both are mechanical: the task reaches `done` under AD13, or
the task's directory moves to `agents/tasks/archive/<CODE>/`. The program detects
the second with `scripts/agents_tree.py`, whose `task_dir()` at `:169` looks in
`agents/tasks/` and then in `agents/tasks/archive/`.

**An expired row is never deleted, which is clause W4 applied to a table row.**
The program sets `expired = true` and writes `expired_at` into
`dev/pod/table.toml`; the router skips it and the file keeps it, because it
records why one task routed differently. **`expire_rows(code)` performs it
through `write_table()`, and TWO tick steps call it:** rule (c)'s DONE limb and
rule (a1).

**Expiry is exempt from R3, and here is the reason.** The router drops an expired
row, so expiry DOES move every record that row used to win. R3 forbids a
MAINTAINER from moving traffic; it does not forbid a row from dying with its
task. The replay uses the SAME expiry state on both sides, so an expiry can never
hide inside a table edit. **The digest prints the fallout**: every corpus record
the expired row used to win falls to the next matching row, or to NO MATCH.

**A `system` row never expires by time.** The owner removes it, and removal is a
table edit, which the replay guards like any other.

### 4.7 Fact 3, amendments A1 and A4

**A1 is RULED. Fact 3 reads "the change in the count of UNRESOLVED names on the
task's own declared obligation list".** AD11's six facts keep their number
and their kind. AD21's pre-flight gains one check, P14.

**Why the amendment was needed, and it is measured.** `scan()` at
`scripts/measure/obligations.py:112` counts `signatures`, which are DISCHARGED
obligations, so the count RISES when a task lands work. Reconstructed over every
task code whose commit touched a master: 63 codes, delta min -18, median +22 and
45 positive, so that caliber would have failed 45 of the last 63 real landings.
**Nothing else counts.** The tree carries 0 `postulate` in code, 0 interaction
holes and 0 `TODO` or `OWED` markers over 99 masters;
`scripts/gate/lint-agda.py` forbids the first two at `:282`, `:291` and
`:286-289`. `dev/ledger.toml:136` declares its `[[remaining]]` rows stale.

#### 4.7.1 The name form, amendment A4

**A bare declaration name never resolves, and that is measured.** A probe in this
tree declares a directory-qualified, parameterised, top-level module. Measured
over `git ls-files -z agents/tasks` filtered to `.agda` and excluding `archive/`:
389 live tracked probes, of which 341 are directory-qualified, 340 take
parameters and 294 are both. The owner's own example is
`module LJ-1-383.Probe383 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where` at
`agents/tasks/LJ-1-383/Probe383.agda:59`.

**The obligation grammar. The brief writes ONE field per obligation.**

```
obligation   ::= <probe-path> "::" <dotted-name>
probe-path   ::= repository-relative path of the probe .agda file
dotted-name  ::= ident ( "." ident )*
```

The dotted name is relative to the probe's top-level module. Each leading `ident`
is a submodule and the last one is the declaration. Two real examples:

```toml
obligations = ["agents/tasks/LJ-1-383/Probe383.agda::Wire.residue2-false-at-record",
               "agents/tasks/LJ-1-306/GenAgree.agda::isTmAt"]
```

**The dotted path is NECESSARY and not a convenience.** `Probe383` exports no
value declaration at its own top level: its three obligations sit inside a SECOND
parameterised module at `agents/tasks/LJ-1-383/Probe383.agda:245`, which takes
eight further parameters, and the obligation is `Wire.residue2-false-at-record`
at `:266`. **MEASURED: the witness reaches it WITHOUT discharging `Wire`'s eight
parameters**, because a qualified reference into a parameterised submodule is a
legal term.

#### 4.7.2 What the meter derives, and it authors nothing

**DISCLOSED DEPARTURE FROM THE RULED TEXT, and a reviewer must be able to see it.**
Ruling 1 says the BRIEF carries a witness preamble per obligation. This section
rules the opposite: the brief writes one field per obligation and the METER
derives all four parts. The measurement below is the reason, and the two costs are
stated rather than absorbed. **Cost one:** the derivation cannot express an
obligation whose telescope types are introduced BELOW the probe's module header,
because step 1 copies only the lines above it. **Cost two:** the 8 live probes
without `--safe` can never carry an obligation, which section 4.7.4 measures.

**The brief writes no preamble. The meter derives all four parts from the probe
file**, mechanically:

1. **The preamble.** Copy every line of the probe ABOVE its module header,
   verbatim. This puts the telescope's own types in scope.
2. **The telescope.** Read the module header, joining lines until `where`.
3. **The application.** Take each binder name from the telescope. Wrap a name
   from a `{ }` group in braces. Leave a name from a `( )` group bare.
4. **The reference.** Write `witness = Target.<dotted-name>`.

One rule is added: **the witness OPTIONS line always carries `--safe`** (4.7.4).

A real witness, generated by that derivation and run on 2026-08-17:

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module WitnessA2 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import LJ-1-383.Probe383
module Target = LJ-1-383.Probe383 {ℓ} lem

witness = Target.Wire.residue2-false-at-record
```

**MEASURED: the derivation produced a green witness for 24 of the 24 sampled
probes that typecheck today.** The sample includes the widest telescope in the
tree, eight explicit parameters at `agents/tasks/LJ-1-306/GenAgree.agda:50`. The
derivation never reads a type, so telescope shape does not bound it: the 389 live
probes use only 11 distinct telescopes, 295 of them exactly
`{ℓ : Level} (lem : LEM (ℓ-suc ℓ))`.

#### 4.7.3 The command, and three include paths are needed

```
GHCRTS="-A64m -I0 -M8g" agda \
  --include-path=.pod-state/witness \
  --include-path=src \
  --include-path=agents/tasks \
  .pod-state/witness/<Witness>.agda
```

Term 1 is the directory that holds the witness. Terms 2 and 3 are the two include
roots of `bedrock.agda-lib`, which reads `include: src agents/tasks`, and the
probe's qualified name `LJ-1-383.Probe383` resolves against the second. **The POD
runs with `cwd` at the repository root, so three terms are enough.** MEASURED with
`cwd=/`, the run fails with `[FileNotFound]` in 0.1 s and `--library=cubical`
returns exit 0 in 1.7 s, so an executor elsewhere needs that fourth term.

#### 4.7.4 The pass rule, keyed on what Agda really reports

Per obligation, at each of the two measurement points:

| Result | Condition | Counts as |
|---|---|---|
| NO FILE | The probe path does not exist. No process starts | UNRESOLVED |
| PASS | exit 0 | resolved |
| MISSING | exit 42 AND an `error: [NotInScope]` whose `file` group is the WITNESS file | UNRESOLVED |
| PROBE RED | exit 42 with any other tag, or a `[NotInScope]` whose `file` group is NOT the witness | UNRESOLVED, and `obligations_probe_red` records it |

The `file` group is the one `ERR` at section 4.3.1 already captures, so the meter
adds no parser. It reads it from `run_agda()`'s `out`.

**Fact 3 is the UNRESOLVED count at exit minus the UNRESOLVED count at
dispatch.** A task that discharges two names gives -2. A task that writes nothing
gives 0, because NO FILE holds at both ends.

**Four measured rules, and each of the four would have shipped a broken meter.**

- **The term-reference form is mandatory.** `open <probe> using ( <name> )` does
  NOT fail on an absent name: Agda returns EXIT 0 and prints only
  `warning: -W[no]ModuleDoesntExport`. Written that way, every NO-GO would read
  as a PASS. `witness = Target.<dotted-name>` returns exit 42 with
  `error: [NotInScope]`.
- **One witness per obligation.** Agda stops at the FIRST unresolved name. A
  combined witness over three obligations, two of them absent, named only one.
  **A combined witness is a valid fast path when it returns exit 0**, because
  that proves every name present in one run.
- **PROBE RED is common, not rare, so it needs its own value.** `[NotInScope]`
  also fires INSIDE a red probe, measured at
  `agents/tasks/LJ-1-286/ProbeLJ1286A.agda:30` and
  `agents/tasks/LJ-1-280/ReRun.agda:66`, both printing the tag in the PROBE file.
  **A meter that greps the tag anywhere in the output reports a red probe as a
  missing obligation**, so the rule anchors on the file path in the error's
  location line. 6 of 30 sampled live probes do not typecheck today.
- **`--safe` is a free guarantee, so every witness carries it.** A witness with
  `--safe` REFUSES a probe without one: `error: [CoInfectiveImport]`, exit 42, so
  a probe cannot discharge an obligation with a postulate. The cost is stated: 8
  of the 389 live tracked probes declare no `--safe`, and an obligation inside one
  reads PROBE RED for ever. **A probe that carries an obligation must declare
  `--safe`**, and `dev/pod/instructions/mathematician.md` says so.

#### 4.7.5 The home, the isolation and the price

`.pod-state/witness/` sits outside the index and inside `.gitignore`, so neither
fact 4 nor `check-probes.py` sees it. **The witness runs are NOT part of fact 5**;
section 4.3.1 excludes them and records `witness_seconds`.

**The price, MEASURED on 2026-08-17, warm interface cache, one Agda process at a
time.** One obligation costs a median of 1.3 s, p90 2.8 s and a minimum of 0.7 s;
60 runs cost 200.5 s in total. **The worst single warm run measured 49.4 s**, so a
three-obligation task costs about 4 s at the median and can reach about 150 s in
the bad case. **Rule (f) pays this price a second time**, at the dispatch point.

**COLD CACHE IS NOT MEASURED AND THIS WORK DOES NOT BOUND IT.** The sweep sampled
only probes with a cached `.agdai`, 136 of 182 candidates. **Do not quote the
median as the price on a fresh clone.** Day 1 measures it.

**Why the declared list beats the three refuted meters.**

| Proposal | Verdict |
|---|---|
| Unsolved metas plus postulates plus holes | REFUTED. All three are zero today, so the counter is constant zero |
| `obligations.py` signature count | REFUTED. It rises on a landing, measured above |
| Module telescope hypothesis count | Works as a delta only, and it over-counts an ordinary binder such as `(n : ℕ)`. It is a whole-tree proxy, so work landed elsewhere moves it. Measured: 989 names over 99 masters in 0.041 s |
| A declared per-task obligation list, measured by a derived witness | **RULED, A1 and A4** |

**The telescope counter is kept as a reported number** in the digest; `fences()`
at `scripts/measure/check-unbound-hyp.py:92` and `hypotheses()` at `:118` give it.

### 4.8 Three worked rows

Each row is drawn from a real return, cited at `file:line`. Section 4.2 shows the
full field set, so only the varying fields are written out here.

```toml
[[row]]                      # SYSTEM ROW 1. A heap wall parks and asks for a split.
id = "sys-heap-wall"
scope = "system"
priority = 100
action = "park_and_split"
added = 2026-08-17
added_by = "maintainer"
reason = "A heap wall at the C-12 cap is a block that is too large, not a wrong proof."
expired = false

  [row.when]
  heap_wall = true

[[row]]                      # SYSTEM ROW 2. Green, slow and empty fires the coder critic.
id = "sys-slow-green-empty"   # scope, added and added_by as above; expired = false
priority = 200
action = "escalate"
head_slot = "coder_adversarial"
reason = "A long green run that lands no obligation is a conversion cost, and a second reader prices it."

  [row.when]
  exit_code = 0
  heap_wall = false
  seconds_min = 300.0
  obligations_delta_min = 0
  obligations_delta_max = 0

[[row]]                      # TASK ROW 1. A must-fail control's failure is the result.
id = "task-lj-1-375-mustfail"
scope = "task:LJ-1.375"
priority = 10
action = "accept"
added = 2026-08-17
added_by = "mathematician"
reason = "MustFail375A.agda is a negative control, so exit 42 with a sort mismatch is the measurement."
expired = false

  [row.when]
  exit_code = 42
  error_class = "universe_level"
  changed_files_any = ["agents/tasks/LJ-1-375/MustFail*.agda"]
  heap_wall = false
```

*The returns they match.* SYSTEM ROW 1 is `[LJ-1.266]`:
`agents/tasks/LJ-1-266/lj-1.266-report.md:73` states
`MEASURED "Heap exhausted" at 8,192 MB, exit 251`, and `:209` states
`only agents/tasks/LJ-1-266/ written`. SYSTEM ROW 2 is `[LJ-1.381]`:
`agents/tasks/LJ-1-381/lj-1.381-report.md:80-83` states 456 s user against a
2.5 s floor, exit 0, and nothing landed in `src/`. TASK ROW 1 is `[LJ-1.375]`:
`agents/tasks/LJ-1-375/lj-1.375-report.md:144-152` gives `MustFail375A.agda:81`,
exit 42, 2.44 s, then `error: [UnequalSorts]`.

*What TASK ROW 1 would have done.* Accept the failure and continue. Without it,
any system row on exit 42 would park a task whose deliverable IS the refusal.
**This is why task rows exist: a task row inverts the default for one task and
expires with it.** It also shows the namespaced id: the mathematician wrote
`mustfail` and `admit_rows()` made it `task-lj-1-375-mustfail`.

**The `done` shape is the fourth**, and section 6.4's `go` branch works it out.

## 5. The loop

*In force since the POD cutover of 2026-08-18, commit `fc676cb`. `AGENTS.md` holds the shared Boundary, and `dev/ARCHIVE.md:214` records `dev/ORCHESTRATION.md` as archived.*

AD1, AD12, AD13, AD14, AD16, AD17, AD18 and AD19.

### 5.0 The runner

**`scripts/pod/pod.py` is the program.** It is tracked and nothing else runs it.

| Command | What it does |
|---|---|
| `pod run` | The sleep loop. It calls `pod_tick()`, sleeps `tick_seconds`, and repeats until `pod_tick()` returns STOP or a signal arrives |
| `pod tick` | One pass, then exit. This is the testable unit and `pod run` calls it |
| `pod resume` | Clear `.pod-state/STOPPED`, re-evaluate every PARKED task (section 5.5), then return to `pod run` |
| `pod status` | Print the state file as a table. It writes nothing |
| `pod stop` | Write `.pod-state/STOPPED`, wait for every RUNNING worker, then commit the tracked table and log. Run it before the checklists of sections 9.1 and 9.2 |

`tick_seconds = 30` lives in `dev/pod/heads.toml` `[limits]`. `pod run` holds no
state of its own and re-reads the state file every tick, so an operator may stop
it at any moment. **One runner at a time:** `pod run` takes the same `flock` that
`registry_lock()` at `dispatch.py:268` takes, on a separate lock file.

### 5.1 The tick

```python
def pod_tick():                             # one pass. pod run sleeps, not this.
    st = load_state(".pod-state/state.json")
    st = replay_log(st, LOG)                # apply every log line with seq > st.seq

    # AMENDED BY A11: rule (g) REFILL is added below. When a slot is free AND
    # the queue holds no dispatchable entry, the program dispatches the
    # mathematician with dev/pod/instructions/refill-queue.md. The program
    # decides only that somebody must be asked; the head decides the work.
    # (a1) CREATE. dev/pod/queue.toml is the only producer of a task.
    for e in queue_entries_not_yet_created():
        inject_survey(e.brief)            # R10, section 7.4. Before P15 reads it
        stamp_pod_marker(e.code)          # section 9.3, one `.pod` line per task
        emit(e.code, NONE -> READY, brief=e.brief)
    for code in codes_now_under_agents_tasks_archive():
        expire_rows(code)                 # section 4.6, the second expiry trigger

    # (a2) UNPARK. AD16, and it is automatic.
    for t in st.tasks where t.status == PARKED:
        if (t.park_reason or "").startswith("preflight:"):
            if preflight(t.brief) == []:  emit(t, PARKED -> READY); continue
        elif t.park_reason in ("admission", "launch"):
            if t.parked_at < mtime(TABLE): emit(t, PARKED -> READY)  # retry, 4.1
        elif t.record is None:            continue    # a no-change park, see 5.5
        elif t.parked_at < mtime(TABLE):
            row_id, _ = route(TABLE, t.record)           # the WHOLE record, B3
            if row_id is None:            continue
            if t.park_reason == "attempt_max:" + row_id: continue   # B2
            emit(t, PARKED -> READY, row=row_id)

    # (b) OBSERVE. A worker is dead when its pid is dead, or when it ran too long.
    for t in st.tasks where t.status == RUNNING:
        if t.elapsed() > LIMITS.worker_deadline_s:
            kill_process_group(t.pid); emit(t, RUNNING -> RETURNED, why="deadline")
        elif not rec_alive(t):            emit(t, RUNNING -> RETURNED)

    # (c) ACCEPT. AD13 runs here, one task at a time.
    for t in st.tasks where t.status == RETURNED:
        if not admits(st, t, agda=True): continue   # section 5.6. The runner runs Agda
        emit(t, RETURNED -> CHECKING)
        rec = run_acceptance(t)           # section 5.4. One record, six facts nested
        if rec is None:                   # R7, section 4.3.2 case 3
            emit(t, CHECKING -> PARKED, reason="no-change"); continue
        row_id, action = route(TABLE, rec)          # section 4.5.1, the WHOLE record
        if   row_id is None:              emit(t, CHECKING -> PARKED, rec=rec,
                                               reason="no-match")   # 5.5 and 8.2
        elif action == "done":                      # R4 reads rec["conjuncts"]
            if not r4_holds(rec, row_id): emit(t, CHECKING -> PARKED, rec=rec, reason="r4")
            else:
                commit_task(t, rec)     # ledger.py --write, then R8's explicit path
                emit(t, CHECKING -> DONE, rec=rec, row=row_id)
                expire_rows(t.code)                 # section 4.6, first trigger
        elif same_row_runs(t, row_id) + 1 >= LIMITS.attempt_max:   # B2
            emit(t, CHECKING -> PARKED, rec=rec, reason="attempt_max:" + row_id)
        elif action == "accept":          emit(t, CHECKING -> READY,  rec=rec, row=row_id)
        elif apply(action, t, rec, row_id) is STOP:  return STOP   # stop_loop only

    # (d) STOP. AD14.
    if count(st, PARKED) >= 3:
        emit(LOOP -> STOPPED, why="3 parked")
        touch(".pod-state/STOPPED"); notify_owner("3 parked"); return STOP

    # (e) MAINTAINER. AD15. The digest hangs off the same trigger, section 8.1.
    harvest_batch()                       # R15 then the replay, section 6.7
    prune_logs(30)                        # the retention of section 4.0
    if hours_since_last_batch() >= 12 or count(st, PARKED) >= 3:
        spawn_maintainer(); write_digest()          # sections 6.7 and 8.1

    # (f) ADMIT AND SPAWN. This is the ONLY writer of a task row, section 4.1.
    # The stop refuses THIS rule and nothing else, section 5.5. Rules (a1) to (e)
    # keep running, so work that already returned is still observed and closed.
    if exists(".pod-state/STOPPED"): return STOP
    for t in st.tasks where t.status == READY, ordered by (t.attempt, t.code):
        d = preflight(t.brief)            # AD21, section 6.5
        if d:
            emit(t, READY -> PARKED, reason="preflight:" + d[0].split()[0], detail=d)
            continue
        if not admit_rows(t.code, t.brief):         # section 4.1. R3 guards the write
            emit(t, READY -> PARKED, reason="admission"); continue
        if not admits(st, t): continue    # section 5.6
        slot = t.head_slot or ("mathematician_adversarial"       # AD27, section 6.6
                               if t.attempt > 1 and not reviewed(t) else None)
        b, role = ((review_brief(t, slot), slot) if slot
                   else (t.brief, head_slot_of(t.brief)))
        t.head_slot = None                # R11. The head is resolved once, here
        t.obl_before = witness_unresolved(t)        # fact 3 at dispatch, section 4.7
        pid = launch(t.code, b, ...)      # dispatch.py:921, section 6.2
        if pid is None:                   # a KEPT refusal of 6.2 fired. Never silent
            emit(t, READY -> PARKED, reason="launch"); continue
        emit(t, READY -> RUNNING, pid=pid, brief=t.brief, dispatched_brief=b,
             role=role, obl_before=t.obl_before)      # K6. brief is ALWAYS the task's
    return CONTINUE
```

**`apply()` performs the six actions rule (c) does not handle inline**, so every
one of the eight actions of section 4.2 reaches an implementation. It writes one
transition line per call and returns STOP only for `stop_loop`.

```python
def apply(action, t, rec, row_id):        # scripts/pod/pod.py. Rule (c) calls it
    r = "row:" + row_id                   # the park reason, section 5.5
    if   action == "park":       emit(t, CHECKING -> PARKED, rec=rec, row=row_id, reason=r)
    elif action == "park_and_split":
        queue_append(split_entry(t, rec))          # a REQUEST entry, section 5.2
        emit(t, CHECKING -> PARKED, rec=rec, row=row_id, reason=r)
    elif action == "redispatch": emit(t, CHECKING -> READY, rec=rec, row=row_id)
    elif action == "redispatch_narrower":
        t.scope_narrow = first_failing_target(rec)  # rec["runs_all"], section 5.4
        emit(t, CHECKING -> READY, rec=rec, row=row_id)
    elif action == "escalate":
        t.head_slot = row_of(row_id)["head_slot"]   # AD27. Rule (f) dispatches it
        emit(t, CHECKING -> READY, rec=rec, row=row_id)
    elif action == "stop_loop":                 # A3, AD14 and AD20. Transition 11
        emit(t, CHECKING -> PARKED, rec=rec, row=row_id, reason="stop_loop:" + row_id)
        emit(LOOP -> STOPPED, why="row " + row_id)
        touch(".pod-state/STOPPED"); notify_owner("row " + row_id)   # push, 8.4
        return STOP
    else: raise KeyError(action)    # done and accept never arrive. Rule (c) has them
```

**`stop_loop` parks its own task first, and that order is deliberate.** The task
must not stay CHECKING across the stop; the park line names the row, and
`pod resume` re-routes it through rule (a2) like any other park. The loop line,
the `STOPPED` file and the owner push follow in the same tick (8.4).

**The order inside rule (f) is fixed and each step guards the next.** The
pre-flight refuses a malformed brief before any table write, so a branch block
that does not parse can never reach `dev/pod/table.toml`. Admission then writes
the rows, so by the time the worker returns, rule (c)'s `route()` can see this
task's rows; without that step every first instance no-matches. `admits()` then
decides concurrency, and only then does the dispatch point of fact 3 run.
**Seven helpers are named here and specified elsewhere:** `inject_survey()` is
7.4's retrieval, `stamp_pod_marker()` is 9.3's `.pod` line, `commit_task()` runs
`ledger.py --write` and then R8's explicit-path commit (7.1 row 26),
`write_digest()` is section 8's digest, `r4_holds()` reads `rec["conjuncts"]` by
the row's `outcome` (5.4), `harvest_batch()` is 6.7's R15 check plus the replay,
and `prune_logs()` is 4.0's retention. Every other name in the tick is a one-line
reader or writer of the queue, the table, the log, the state file, the process
table or the clock.

**`witness_unresolved(t)` is the dispatch-point half of fact 3.** It runs the
meter of section 4.7 over the brief's obligation list, returns the UNRESOLVED
count into `obl_before`, and `witness_delta(t)` of section 5.4 subtracts it. It
costs the price of section 4.7.5, once per dispatch. **`reviewed(t)` reads the
log and holds no state**: it is true when a `READY -> RUNNING` line for this code
carries this `attempt` and `role: "mathematician_adversarial"`, both log fields.
`review_brief(t, slot)` is program-written and section 6.6 gives its shape.

Every branch reads a file on disk. `rec_alive()` at `dispatch.py:388` reads
`ps -o lstart= -p <pid>` and `os.kill(pid, 0)`, and `run_acceptance()` runs the
six conjuncts and `git status --porcelain`. No branch asks a model.

**`worker_deadline_s` is new and it is needed.** The only other exit from RUNNING
is a dead pid, so a hung worker holds an Agda slot for ever. The kill targets the
process GROUP, which `start_new_session=True` at `dispatch.py:1294` allows.

**`attempt_max` is new, and without it `accept` and `escalate` are unbounded
loops.** `route()` is pure, so a retry that changes nothing reproduces the same
record, the same row matches, and the task cycles for ever. The cap parks it with
`reason: "attempt_max:<row id>"`, which NAMES the row that kept matching. **That
is a design error in the ROW and not in the task, and the park is how the
maintainer learns of it.** The cap covers all four looping actions: `accept`,
`escalate`, `redispatch` and `redispatch_narrower`.

**`same_row_runs()` counts the CONSECUTIVE `CHECKING -> READY` lines for this
code whose `row` is the row that just matched.** It reads the log, so the cap
survives a crash, and a DIFFERENT matching row starts a new run at zero, which is
what "the maintainer fixed the row" looks like. Rule (a2) promotes an
`attempt_max` park only when `route()` returns a different row id, so a table edit
that does not touch the guilty row costs no dispatch.

### 5.2 The state file and the task producer

**The producer is `dev/pod/queue.toml`, tracked.** Nothing else creates a task:
the mathematician writes an entry, `park_and_split` appends one, and the owner may
add one by hand. Rule (a1) turns each entry that NAMES A BRIEF into a READY task,
which respects AD2 and AD3. **An entry with no `brief` is a REQUEST and never a
task:** `split_entry()` writes `code`, `split_of` and `reason`, rule (a1) skips
it, and the digest prints it until the mathematician adds the brief path. The
program never writes a brief, because AD3 gives the brief to the mathematician.

```toml
[[task]]
code = "LJ-1.386"
brief = "agents/tasks/LJ-1-386/LJ-1.386.md"
added = 2026-08-17
added_by = "mathematician"
```

`.pod-state/state.json`, not tracked, is a cache of the log's fold.
`.claude/skills/codex-dispatch/.state/registry.json` holds 469 records and 14
fields, and supplies the record shape. **12 of the 14 carry over unchanged**:
`pid`, `proc_start`, `brief`, `agda`, `sandbox`, `model`, `log`, `final`,
`started`, `harness`, `events`, `reported`. **`session` and `resumed_from` are
dropped**, because AD16 resumes by a fresh instance. **Fourteen are added:**
`status`, `role`, `effort`, `exclusive`, `attempt`, `predecessor`, `run`,
`record`, `obl_before`, `row`, `park_reason`, `parked_at`, `head_slot` and
`scope_narrow`. `record` holds the newest acceptance record whole, which rule (a2)
routes on; `parked_at` is the clock rule (a2) compares with the table mtime;
`head_slot` and `scope_narrow` are `apply()`'s leavings; `t.code` is the map KEY.

```json
{"version": 1, "seq": 10417, "stopped": null,
 "tasks": {"LJ-2.7": {
   "pid": 44845, "proc_start": "Sun 16 Aug 22:24:19 2026", "agda": true,
   "brief": "agents/tasks/LJ-2-7/LJ-2.7.md", "sandbox": "acceptEdits",
   "model": "claude-opus-5", "effort": "max", "harness": "herdr-claude",
   "log": ".pod-state/logs/LJ-2.7-20260817-140322.log", "events": "",
   "final": ".pod-state/logs/LJ-2.7-20260817-140322-final.md",
   "started": "2026-08-17 14:03:22", "reported": true, "exclusive": false,
   "status": "RUNNING", "role": "mathematician", "attempt": 2,
   "predecessor": "LJ-2.7#1", "run": "agents/tasks/LJ-2-7/runs/accept-3.out",
   "obl_before": 2, "row": "sys-retry-on-meta", "record": null,
   "park_reason": null, "parked_at": null, "head_slot": null,
   "scope_narrow": null}}}
```

**Six states. Twelve transitions. Nothing else is legal.**

| # | Transition | Trigger |
|---:|---|---|
| 1 | `(none) -> READY` | A `dev/pod/queue.toml` entry, rule (a1) |
| 2 | `READY -> RUNNING` | `launch()` returned a pid |
| 3 | `RUNNING -> RETURNED` | `rec_alive()` is false |
| 3b | `RUNNING -> RETURNED` | `worker_deadline_s` passed. The program killed the group |
| 4 | `RETURNED -> CHECKING` | The acceptance runner started |
| 5 | `CHECKING -> DONE` | A row matched, its action is `done`, and R4 holds for its `outcome` |
| 6 | `CHECKING -> READY` | A row matched and its action retries or escalates. `attempt` rises |
| 7 | `CHECKING -> PARKED` | No row matched, or the matched action is `park`, or R7 dropped the return, or `attempt_max` was reached, or R4 refused a `done` |
| 8 | `READY -> PARKED` | The pre-flight refused the brief (6.5), admission was rejected (4.1), or `launch()` refused (6.2) |
| 9 | `PARKED -> READY` | The table changed: `route()` now matches, or an admission retry is due, rule (a2) |
| 10 | `PARKED -> READY` | The brief was repaired and the pre-flight now passes, rule (a2) |
| 11 | `CHECKING -> PARKED` | The matched action is `stop_loop`. `apply()` parks the task, then stops the loop in the same tick |

An `escalate` action moves the task to READY with `attempt` raised, so transition
6 covers it and rule (f) then sends the review dispatch of section 6.6. One more
line is not a task transition: it carries `task: ""` and `to: "STOPPED"`, and
rule (d) and `apply()` are its two writers. **`CHECKING` is a separate state on purpose:** the
acceptance test is itself an Agda run that can take minutes, and a crash inside
it must not read as a return.

### 5.3 Crash safety

**The rule: the tracked log is the truth and the state file is a cache of its
fold**, so the log line is written FIRST. A lost state file is recoverable from
the log; a lost log line is recoverable from nothing.

```
1. perform the side effect               # spawn, or run agda, or nothing
2. with registry_lock():                 # dispatch.py:268, one flock for both writers
3.     append one line to LOG; os.fsync(log_fd)
4.     st.seq += 1; save_state(st)       # tmp -> fsync -> rename -> fsync(dir)
```

Step 2 puts both writes inside the lock `dispatch.py` already uses, on a separate
file, so a corrupt state file cannot also break locking. **One hardening is
needed:** `save()` at `dispatch.py:316-321` renames a temporary file with no
`os.fsync`, which is atomic against a process crash and not durable against a
machine crash. Add `os.fsync` on the file and on the directory.

**Crash window one: log written, state not.** The log holds a line with `seq`
above the state's, and the next start applies every such line in order; this is
the designed window and it is safe. **Crash window two: side effect done, log not
written.** The side effect is re-observable: a spawned worker becomes an ORPHAN,
which `strays()` at `dispatch.py:460` finds; an acceptance run leaves its
`runs/accept-<n>.out`; and an admission is re-observable because `admit_rows()`
is idempotent. **The asymmetry copies `alive()` at `dispatch.py:373-381`:** a
dead agent holding a slot is visible, while a live agent read as dead makes a
gate green over a half-written tree.

#### 5.3.1 The transition log

`dev/pod/transitions/<YYYY-MM>.jsonl`, tracked, append only. One real line:

```json
{"ts":"2026-08-17T14:03:22Z","seq":10417,"task":"LJ-2.7","from":"RUNNING","to":"DONE","row":"sys-accept-clean","scope":"system","run":"agents/tasks/LJ-2-7/runs/accept-3.out","facts":{"exit_code":0,"error_class":null,"obligations_delta":-2,"changed_files":["src/L/Condensation/TwelveAgree.lagda.md","src/L/Condensation.lagda.md"],"seconds":41.0,"heap_wall":false},"caliber":"-A64m -I0 -M8g","concurrency":1,"pid":44845,"role":"mathematician","attempt":2,"model":"claude-opus-5","effort":"max","heads_sha256":"3f9c"}
```

`facts` carries AD11's six and nothing else. `task`, `concurrency` and
`caliber` sit at the TOP level, which is why `route()` and `matches()` read the
whole record and not the facts object. **A log line and a corpus record are the
same shape**, so the replay reads either; a corpus record adds only `id` and
`provenance`. A PARK line carries `"row": null`, a `reason` from section 5.5's nine
and the record that matched nothing, and a pre-flight park adds `detail`, the
whole refusal list. A dispatch line carries `brief`, `role` and `attempt`, which
is what `reviewed()` and `same_row_runs()` read. **`brief` is ALWAYS the TASK's
brief, and it is what the pre-flight re-reads on the next tick.
`dispatched_brief` is the file the worker was actually given; on a review
dispatch the two differ, because `review_brief()` writes a program-built file
that carries no branch block.** Writing the review brief into `brief` would park
the task with `preflight:P1` for ever, since rule (a2) would re-run P1 against a
file that can never carry a branch block. A RETURNED line and the
`STOPPED` line carry `why`.

**Growth, measured.** The registry holds 469 dispatches over 12 days, median 38.5
per day, and `agents/tasks/LJ-1-371/lj-1.371-report.md:92` measured the blind
half at 126 of 275, so the true rate is about 71 per day and the peak about 120.
At 5 transitions per clean task and about 350 bytes per line that is about 124 KB
per median day, 210 KB at the peak, and about 3.7 MB per month.

### 5.4 The acceptance runner of AD13, amendment A5

**A5 gives the acceptance test its enforcement point: it IS fact 1.** The runner
owns the six conjuncts, and `exit_code` is the runner's code. An earlier draft
listed conjuncts that no fact could see, so a task could route to `done` with
three of them red.

| # | Conjunct | Class when it fails | Why |
|---:|---|---|---|
| 5 | `check-spec-surface.py --check` exits 0 | `spec_surface` | AD22, section 7.3 |
| 1 | `agda` exit 0 over the changed masters and their consumers | the Agda class | AD13 |
| 2 | The obligation delta is 0 or negative | `obligations_up` | AD13, A1's meter |
| 3 | `check-closure.py --check closure` exits 0 | `closure_open` | Section 7.2 |
| 4 | `check-unbound-hyp.py` finds no NEW unbound hypothesis | `unbound_hyp` | Section 7.1 row 30 |
| 6 | The pre-commit gate set exits 0. **The member list is pinned: rows 1, 2, 3, 4, 6 and 33 of section 7.1, plus `check-survey-quotes.py`** | `lint` | Section 7.1, R14. A lint red parks the task |

**The runner MEASURES all six facts first, then TESTS the six conjuncts.** A
branch may route on a fact whose conjunct failed, which is how a NO-GO reaches a
`done` row, so the measuring never stops early.

```python
RUNNER_CLASS = {2: "obligations_up", 3: "closure_open", 4: "unbound_hyp",
                5: "spec_surface",   6: "lint"}

VACUOUS = {"rc": 0, "agda_class": None, "seconds": 0.0, "heap_wall": False,
           "caliber": CAP, "error_names_all": [], "runs_all": [], "vacuous": True}

def conjunct1(tgts):
    """4.3.2. FIRST failing run, or the LAST when all pass. Case 4 gives VACUOUS."""
    if not tgts: return dict(VACUOUS, concurrency=slots())     # case 4
    runs = []
    for target in tgts:                       # run_agda takes ONE target, 4.3.1
        r = run_agda(target, ROOT, LIMITS.agda_deadline_s, slots())
        runs.append({"target": target, "rc": r["rc"], "seconds": r["seconds"]})
        if r["rc"] != 0: return dict(r, runs_all=runs)
    return dict(r, runs_all=runs)

def run_acceptance(t):
    ch, foreign = changed_files(t)            # fact 4, section 4.3.1. Task-scoped.
    if not ch: return None                    # R7, section 4.3.2 case 3. No record.
    c5 = spec_surface()                       # cheapest, and A3 puts it first
    r1 = conjunct1(verification_target(ch, t.code))            # section 4.3.2
    d3, wsec, red = witness_delta(t)          # fact 3, section 4.7. Reads t.obl_before
    c3, (c4, uvac), c6 = closure(), unbound_new(ch, t.unbound_before), precommit_set()
    held = [(5, c5), (1, r1["rc"] == 0), (2, d3 <= 0), (3, c3), (4, c4), (6, c6)]
    bad  = next((n for n, ok in held if not ok), None)      # order 5,1,2,3,4,6
    return {"task": t.code, "concurrency": r1["concurrency"],
            "caliber": r1["caliber"], "witness_seconds": wsec,
            "obligations_probe_red": red, "error_names_all": r1["error_names_all"],
            "agda_vacuous": r1.get("vacuous", False), "unbound_vacuous": uvac,
            "changed_files_foreign": foreign,  # outside the scope, 4.3.1. Digest
            "runs_all": r1["runs_all"],       # every other Agda wall, provenance
            "conjuncts": dict(held),          # provenance. R4 reads it. NOT matchable
            "facts": {"exit_code":  0 if bad is None else (r1["rc"] if bad == 1 else 1),
                      "error_class": None if bad is None else
                                     (r1["agda_class"] if bad == 1 else RUNNER_CLASS[bad]),
                      "obligations_delta": d3, "changed_files": ch,
                      "seconds": r1["seconds"], "heap_wall": r1["heap_wall"]}}
```

**Four helpers, named here so day 3 can build them.** `slots()` is
`len(agda_holders(load()))` at `dispatch.py:422`. `verification_target(ch, code)`
implements section 4.3.2's four cases and returns a LIST, empty under case 4.
`witness_delta(t)` runs the meter of 4.7 at EXIT, subtracts `t.obl_before`, and
returns the delta, the witness seconds and the probe-red flag.
`unbound_new(ch, before)` re-runs the tool, subtracts the pre-flight finding SET
carried on the task as `t.unbound_before`, and returns the conjunct and its
vacuous flag. A set difference is the rule, so the five findings that stand today
fail nothing. **Every other name above is one
conjunct's own command from the table**, or fact 4's snapshot (4.3.1).

**The conjunct order is 5, 1, 2, 3, 4, 6, and the first failure names the class.**
Conjunct 5 runs first for two reasons that agree: it is the cheapest, at one
sha256 per surface file, and A3 makes the spec surface undefeatable, so an Agda
failure must never hide a surface change. **The deadline needs no special case:**
`r1["rc"]` is `None`, conjunct 1 fails, `exit_code` is `None`, and
`exit_code_absent` matches.

**R4 and a NO-GO close, and this is the contradiction A6 would otherwise open.** A
`done` row may match `exit_code = 42`, because a stated NO-GO discharges the
obligation to ANSWER. So a task can reach DONE with conjunct 1 red, and an
un-amended R4 forbade exactly that. **R4 now reads by `outcome`:**

| `outcome` | Conjuncts R4 requires | Why |
|---|---|---|
| `go` | all six | The task claims landed work, so every measure of that work must hold |
| `no-go` | 5 and 6 | A NO-GO lands no proof, so conjuncts 1 to 4 measure nothing. Conjuncts 5 and 6 protect the TREE and still bind |

The DONE handler reads `conjuncts` from the record, which costs no re-run, and on
a refusal it PARKS with `reason: "r4"` rather than closing. **Conjunct 5 needs no
separate guard**, because a surface change makes the class `spec_surface` under
the order above, and A3 then gives `sys-spec-surface` the routing. **Conjunct 1
needs one command**, because `src/Everything.lagda.md` imports every tracked
master except itself, so one run of it under R13's caliber covers every consumer.

**The consumer set, when the program needs it by name.** `import_graph()` at
`scripts/measure/ledger.py:392` gives forward edges, and `closure()` at `:406` is
direction blind. Reverse the graph and call `closure()` with no edit at all.
`import_graph` needs one new parameter, `at_head: bool = True`, because an
agent's edit is uncommitted and `head_text()` at `:134` reads `git show HEAD:`;
`count()` at `:141` already carries that parameter. Measured cost of the whole
graph, forward and reverse, over 97 countable masters: 0.041 s.

**Conjunct 4 needs a definition of NEW, because the tool has no baseline mode.**
Measured: `.venv/bin/python scripts/measure/check-unbound-hyp.py --check` prints
five findings today (`src/L/Absorption.lagda.md:398` and `:400`,
`src/L/InjChain.lagda.md:471`, `src/L/Reflect.lagda.md:365`,
`src/L/StageCardinal.lagda.md:281`) and exits 1, so a naive read fails every task
for ever. **The rule: the pre-flight snapshots the finding SET, the acceptance
re-runs it, and the conjunct fails on a set difference.** The tool reads only
tracked masters, so a task that changed no master passes VACUOUSLY and the record
carries `unbound_vacuous: true`.

**Conjuncts 3, 4 and 5 exist because exit 0 is not enough.** A master that
`Everything` does not import has no consumers, so conjunct 1 is vacuous for it. A
module telescope hypothesis whose conclusion asserts a membership no premise
constrains typechecks, is fast, and proves nothing;
`scripts/measure/check-unbound-hyp.py` records about a thousand delivered lines
lost to seven defects of that species. And a worker may edit the trophy statement
and leave the tree green, which conjunct 5 catches.

**The run record format already exists and is proven.**
`agents/tasks/LJ-1-331/run.sh` writes it and `runs/h2-valk.out` beside it is a
real one, carrying the arm, the file, the flags, `GHCRTS`, the Agda slot count,
the load average (`run.sh:25`), `# wall seconds 136` and `# exit 251`.

**The price, per conjunct. The floor is measured and the recompile term is not.**
Conjunct 1: a warm `agda --safe src/Everything.lagda.md` measured 3.18 s, and four
warm runs without `--safe` measured 3.02, 2.84, 2.87 and 2.84 s; under case 4 it
is 0.0 s. Conjunct 2: about 1.3 s per obligation warm at each of the two
measurement points, section 4.7.5. Conjuncts 3, 4 and 5 are bookkeeping: 0.041 s,
0.041 s and one sha256 per surface file. Conjunct 6 is the pre-commit gate set.
**The whole variable price is the recompile, and the recorded rates bracket it
34-fold apart.** Gap B3 carries it. Do not quote 133.19 s for a full-tree
acceptance test: that is DD24's AC-only baseline.

### 5.5 PARK, the stop at 3, and the restart

**On a PARK the program writes exactly one line, with `"row": null`.** The state
file then carries `status: "PARKED"`, `record: <the same record>` and
`park_reason`, so the maintainer batch reads one file and not the whole log.
**Nine park reasons exist and each names its cause:** `no-match`, `no-change`
(R7), `preflight:P<n>`, `attempt_max:<row id>`, `r4` (5.4), `admission` (4.1),
`launch`, which is a KEPT refusal of section 6.2 firing at the dispatch itself,
`row:<row id>` for a `park` or `park_and_split` action, and `stop_loop:<row id>`.
**Every park site writes one**, and rule (a2) branches on it: a `preflight:` park
re-runs the pre-flight, an `admission` or `launch` park retries on the next table
edit, and the rest re-route on the record. **A `no-change` park carries NO
record**, so `route()` can never un-park it; it waits for the maintainer batch's
queue request (6.7).

**A pre-flight park is NOT terminal, and rule (a2) is why.** A task refused
before dispatch has no record, so `route()` cannot un-park it, and rule (a2)
re-runs `preflight()` for any task whose `park_reason` starts with `preflight:`.
**The mathematician repairs a malformed brief**, and `harvest_batch()` appends
the queue entry that names the failed check.

**The stop stops DISPATCHING. It never touches a running worker.** The reason is
the founding incident of `dispatch.py`: on 2026-08-05 two live agents died
because somebody stopped the watcher shell that had launched them into its own
process group (`dispatch.py:7-9`), and `setsid` exists in `launch()` for exactly
that (`dispatch.py:1294-1296`). At the stop the program appends the
`to: "STOPPED"` line, writes `.pod-state/STOPPED`, pushes the owner notice, keeps
observing, and refuses only rule (f). **The consequence, stated plainly: the
PARKED count can pass 3 after the stop**, because the already-running workers keep
landing. That is the honest count.

**The restart, five steps.** Read the digest. Let the maintainer batch run. Let
the replay admit or refuse each new row. Repair any brief the pre-flight refused.
Run `pod resume`, which deletes `.pod-state/STOPPED` and runs rule (a2) once for
every PARKED task; a task that now passes goes `PARKED -> READY` and is
re-dispatched as a FRESH instance (AD16). If three still stand, the loop stops
again at once, which is correct. **Rule (a2) also runs on every ordinary tick**,
so `pod resume` is a convenience and never the only path.

### 5.6 Concurrency, AD17

**The program learns that a task measures seconds from one machine-readable line
in the brief, and never from a judgement.** `dispatch.py:691` already parses a
`tier:` line with `re.search(r"^tier:\s*([a-z0-9-]+)", text, re.M)`; the brief
gains one line of the same shape, `machine: exclusive` or `machine: shared`, and
pre-flight P13 refuses a brief with neither. The value is copied once into the
state record at admission, so a later edit of the brief cannot change a running
task's class, exactly as `dispatch.py:1324` does for the harness.

```python
# AMENDED BY A13 and A14. This body predates both. A13 adds the watchdog limb:
# admits() REFUSES every Agda task while scripts/ops/agda-watchdog.sh is down.
# A14 restores C-12's tiers: WIDE four at -M8g, HEAVY two at -M12g, the mixed
# worst-case heap sum at or under 32 GB, and slots three and four only when
# system free memory reads above 25 percent.
def admits(st, t, agda=None):
    running = [x for x in st.tasks.values() if x.status in (RUNNING, CHECKING)]
    if any(x.exclusive for x in running):            return False
    if t.exclusive and load1() > LIMITS.exclusive_max_load1: return False  # record it
    if t.exclusive:                                  return not running
    total, per_parent, blind = agda_pileup()         # dispatch.py:426
    if blind:                                        return False   # never guess
    if any(n > 1 for n in per_parent.values()):      return False   # the pile-up
    if (t.agda if agda is None else agda) and total >= AGDA_SLOTS: return False
    return True
```

**Three properties of the code above, and each one repairs a real defect.**
`agda_pileup()` returns `(total, per_parent, warning)`, so all three values are
unpacked: reading `[0]` as a boolean would refuse every admission while ONE Agda
process lives. The threshold `total >= AGDA_SLOTS` is
`agents/tasks/LJ-1-331/run.sh:14-18`'s own rule of two. The warning is never
discarded: when `ps` fails, `agda_pileup()` returns `0, {}, "...BLIND"`, and
admitting on that is the wrong direction, so the program refuses and records it.

**Step (c) passes `agda=True` whatever the brief says**, because the acceptance
runner starts Agda for every case of section 4.3.2 except case 4, and the program
cannot know which case applies until fact 4 is measured.

**What `dispatch.py` already enforces:** `AGDA_SLOTS = 2` at `dispatch.py:248`;
`AGDA_HEAP` at `:247`; `agda_holders()` at `:422`; the slot refusal at
`:993-998`; the write-territory refusal at `:1596`; the `--env GHCRTS=` hand-over
at `:1027`, because a pane inherits nothing. **Edit `AGDA_HEAP` to R13's
caliber**, `-A64m -I0 -M8g`, so a worker pane and the acceptance runner measure
at one caliber. The 8 GB heap cap does not move, so C-12 holds.

**The gap to close.** `agda_pileup()` at `dispatch.py:426-459` has ONE consumer,
`cmd_status` at `:1942`, and it only PRINTS. Its docstring records why it exists:
on 2026-08-12 one agent held six Agda processes at once, each at the 8 GB cap, so
48 GB of worst case on a 64 GB machine and a load average of 19. **Under AD17 the
POD must REFUSE on it, not print about it.** **Exclusive is not only about
slots**, which is the second limb of `admits()` above: every run record writes a
`# load before` line (`run.sh:25`), `load1()` reads `os.getloadavg()[0]`, and the
task stays READY while the tick records the refusal.

## 6. The roles

*In force since the POD cutover of 2026-08-18, commit `fc676cb`. `AGENTS.md` holds the shared Boundary, and `dev/ARCHIVE.md:214` records `dev/ORCHESTRATION.md` as archived.*

AD2, AD3, AD12, AD15, AD18, AD21, AD24, AD25, AD26 and AD27.

**The division of labour.** The program reads state, matches the table, spawns a
worker and writes state. The mathematician writes briefs, writes the queue and
holds all judgement. The maintainer writes new table rows, in batches, into one
path (R15). The two adversarial heads attack one return each. No other model
exists, and no model runs the loop.

### 6.1 `dev/pod/heads.toml`

**AMENDED BY A12 and A14.** The maintainer head is `claude-opus-5` at effort
`high`, ruled 2026-08-17, which closes gap M8. The file also carries C-12's TWO
concurrency tiers, restored by A14: WIDE at four concurrent `-M8g`, HEAVY at two
concurrent `-M12g`.

The file is tracked and the owner may change it at any time. It is the ONLY home
of a model name, an effort level, a deadline or a load threshold. **NOBODY ELSE
changes it without a named owner approval**: R16 puts the file in the spec
surface gate's guarded set (7.3), because it is not a table row and `replay()`
never sees it.

```toml
version = 1

[legal]
efforts = ["low", "medium", "high", "xhigh", "max"]
models = ["claude-opus-5", "claude-fable-5", "claude-sonnet-5",
          "opus", "fable", "sonnet"]

[limits]
tick_seconds = 30             # the runner's sleep, section 5.0
exclusive_max_load1 = 6.0     # refuse to start an exclusive task above this
agda_deadline_s = 1800        # the POD owns the deadline. See gap M2
worker_deadline_s = 14400     # a worker that runs longer is killed, section 5.1
attempt_max = 4               # consecutive retries on ONE row, then PARK. B2

[heads]
mathematician             = { model = "claude-opus-5",   effort = "max",  harness = "herdr-claude", sandbox = "acceptEdits" }
mathematician_adversarial = { model = "claude-fable-5",  effort = "max",  harness = "herdr-claude", sandbox = "acceptEdits" }
coder                     = { model = "claude-sonnet-5", effort = "high", harness = "herdr-claude", sandbox = "acceptEdits" }
coder_adversarial         = { model = "claude-opus-5",   effort = "high", harness = "herdr-claude", sandbox = "acceptEdits" }
maintainer                = { model = "claude-opus-5",   effort = "high", harness = "herdr-claude", sandbox = "acceptEdits" }
```

**The maintainer slot is an orchestrator pick and not an owner ruling.** AD24 and
AD25 name four heads; AD2 needs a fifth and names no model. Gap M8 carries it.

**The three full model IDs are NOT verified.** `grep -n "claude-" dev/vendors.toml`
returns nothing, and its own rule at `:185-186` reads: a row is added when its
model ID is known, not before. `claude --help` documents the SHAPE with the
example `claude-fable-5` and the aliases `fable`, `opus` and `sonnet`. **So
`legal.models` carries both forms, and day 2's first act resolves the three full
IDs against one throwaway pane**, and whichever form resolves is what
`heads.toml` ships. Gap B4.

**NO FIELD HAS A SILENT DEFAULT.** A missing or misspelt field is a refusal and
never an assumed value. The loader is about 40 lines: it reads the file with
`tomllib`, refuses any model outside `legal.models`, refuses any effort outside
`legal.efforts`, refuses a missing slot, and returns a frozen dict.
**A misspelt model is loud,
because the program reads it back:** a wrong ID passes the loader when it is in
`legal.models` and then fails inside a pane, which `dispatch.py`'s guards read as
a started run, so after `agent start` the POD's `launch()` wrapper runs
`herdr agent read`. A pane that does not name the model it asked for returns NO
PID, and rule (f) parks the task with `reason: "launch"`.

**`dev/pod/instructions/<slot>.md`, one tracked file per head.** The program
injects the file at dispatch, ahead of the brief. **This is where a standing
instruction lives once `AGENTS.md` is void, and section 3.1's twelve written
clauses are its content**: W1 to W4, W7 and W8 go to `mathematician.md`, W2 and
W4 also to `coder.md`, and W5, W6, W9, W10, W11 and W12 to every slot.
`instructions/mathematician_adversarial.md` is also the template section 6.6's
review brief is built from. A file that carries no clause still exists, because
the dispatch reads it unconditionally.

**Every slot file carries one more sentence, and it is not a clause because it
states a program property rather than a duty:** "Never set `GHCRTS` yourself. The
program sets the one caliber, `-A64m -I0 -M8g`, on your pane. A number you
measure under any other caliber is not comparable and must not be reported as a
price." This replaces `AGENTS.md`'s `GHCRTS=-M8g agda <file>` line, which set a
heap cap and no allocation area, so an agent that followed it measured at a
caliber R13 forbids.

**AD26, no retro-fit, and the mechanism is a record and not a policy.** The
program resolves the head ONCE, at dispatch, and writes `model`, `effort`, `role`
and `heads_sha256` into the transition log line (5.3.1). Nothing downstream
re-reads `heads.toml` for a running task, and a re-dispatch is a FRESH instance.

### 6.2 The launcher, AD18 and amendment A2

**A2: `dispatch.py` is EXTENDED and never replaced.** A probe on 2026-08-17
returned POSSIBLE and named the exact edits. Three come from A2. Two more are
blockers the probe found, and without them the first three cannot run.

**What the probe verified.** `herdr agent start --help` lists `claude` among its
`--kind` values, and native flags reach the agent after `--`.
`herdr integration status` prints `claude: current (v7)`, so a claude pane already
reports the `working`, `idle`, `done` and `blocked` lifecycle that
`dispatch.py:1120` and `:1148` wait on. `claude --help` lists `--model`,
`--effort` with exactly the five values of `legal.efforts`, and
`--permission-mode` with `acceptEdits`.

**Edit 1, at `dispatch.py:184`.** Replace
`HERDR_KIND = {"herdr": "codex", "herdr-pi": "pi"}` with
`HERDR_KIND = {"herdr": "codex", "herdr-pi": "pi", "herdr-claude": "claude"}`.
Line `:185` is `HERDR_HARNESSES = tuple(HERDR_KIND)`, so it needs no edit.

**Edit 2, at `dispatch.py:1028-1029`.** The `model_args` builder is a two-branch
conditional expression, so a `claude` kind falls into the `else` branch and emits
`-- --provider deepseek --model <model>`. The `claude` CLI has no `--provider`
flag. Replace the expression with three branches:

```python
if kind == "codex":
    model_args = ["--", "-m", model]
elif kind == "claude":
    model_args = ["--", "--model", model, "--effort", effort,
                  "--permission-mode", "acceptEdits"]
else:
    model_args = ["--", "--provider", PI_PROVIDER, "--model", model]
```

**Edit 3, the `effort` pass-through, in three places.** Add `effort: str = ""` to
the `launch()` signature at `dispatch.py:921-923`. Write `"effort": effort` into
the registry record at `:1314-1316`, beside `"model"`, so a resume recovers it
exactly as `:1324` recovers the harness. Thread it from both callers, at `:1440`
and at `:1697-1698`.

**Edit 4, at `dispatch.py:2565-2566`, and it blocks the other three.** The
argument reads `choices=("herdr", "herdr-pi", "codex", "pi"), default=HARNESS`,
and `argparse` validates a SUPPLIED value against `choices`, so
`--harness herdr-claude` is refused before any other edit can run. Add
`"herdr-claude"` to the tuple. In the same block, add the effort option beside
`--model` at `:2564`, with the five values of `legal.efforts` and `""`.

**Edit 5, the harness resolution.** `HARNESS` is a module global set at IMPORT
time: `dispatch.py:133` reads `HARNESS = POLICY.default_harness() or "herdr"`, and
`default_harness()` at `scripts/dispatch/dispatch_policy.py:840-861` ends in
`HARNESS_FOR_AGENT.get(d["agent"])`, whose map at `:784` holds no claude token,
so `default_harness()` can NEVER return `herdr-claude`. Worse, section 7.1 row 21
retires `dispatch_policy.py`, and then the handler at `dispatch.py:137-141` sets
the hard literal `HARNESS = "herdr"`, which `:184` maps to kind `codex`. **So
after the retirement every dispatch that omits `--harness` would silently start a
CODEX agent on a deepseek model.** Set the literal at `dispatch.py:133`, `:135`
and `:139` to `"herdr-claude"`, and delete the case-override block at
`:2658-2666`. **Then make the module default not load-bearing:** the POD passes
`--harness`, `--model` and `--effort` on every dispatch, because `DEFAULT_MODEL`
at `dispatch.py:86` is `deepseek-v4-pro`.

**The command the program builds.**

```
herdr agent start lj-1-386 --kind claude --pane "$PANE" --env GHCRTS="-A64m -I0 -M8g" \
      -- --model claude-opus-5 --effort max --permission-mode acceptEdits
herdr agent prompt lj-1-386 "$(cat dev/pod/instructions/mathematician.md agents/tasks/LJ-1-386/LJ-1.386.md)"
herdr agent wait  lj-1-386 --until working --timeout 120000
```

`--permission-mode acceptEdits` matters at the first launch: a trust prompt makes
herdr report `blocked`, which `dispatch.py:1159` does not treat as a death.

**The herdr driver at `dispatch.py:1010-1231` must be reused verbatim.** Every
one of its guards is a measured death: the two-phase wait, the existence check
after `agent start`, and the `STOPPED=1` flag, because ten failed waits against a
LIVE agent read exactly like a finished run and the driver then killed it.
**Functions the POD reuses with no change:** `registry_lock()` at `:268`,
`load()` at `:283` which REFUSES on a corrupt file, `proc_start()` at `:324`,
`alive()` at `:349`, `rec_alive()` at `:388`, `final_is_clean()` at `:392`,
`herdr_name()` at `:221`, `agda_holders()` at `:422`, `strays()` at `:460`,
`write_paths()` at `:1557`, `brief_in_flight()` at `:1538` and
`territory_in_flight()` at `:1596`. **`launch()` is NOT on this list.**

**Edit 6, the ten removals, and the whole of `launch_defects()` swept with
them.** `launch_defects()` at `dispatch.py:737-755` is the one funnel every launch
path crosses: it runs `validate()`, then four more functions. Without edit 6
`launch()` refuses every POD brief, so edits 1 to 5 buy nothing. **Every refusal
the funnel can raise is listed here with a verdict, and a KEEP names what
satisfies it.** Rows 15 to 17 sit outside the funnel and go with it.

| # | Refusal, in `launch_defects()` order | Verdict | Released by, or satisfied by |
|---|---|---|---|
| 1 | `validate`: brief does not exist, `:774` | KEEP | Pre-flight P1 reads the file first, so a missing brief parks the task and never reaches `launch()` |
| 2 | `validate`: brief not pinned under `agents/tasks/<CODE>/`, `:805-809` | KEEP | Section 6.3 pins it at `agents/tasks/<CODE>/<CODE>.md`. `ROOT` at `:66` is an absolute literal, so cutover step 4's move does not break it |
| 3 | `validate`: no `tier:` line, `:813-819` | REMOVE | DD17 = SUPERSEDED, section 7.1 |
| 4 | `validate`: tier mode against the switch, `:838-857` | REMOVE | DD17 = SUPERSEDED |
| 5 | `validate`: write order with a read-only sandbox, `:866-871` | KEEP | Every slot in `heads.toml` is `acceptEdits`, so it cannot fire |
| 6 | `validate`: `--agda` with a read-only sandbox, `:872-875` | KEEP | Same. It cannot fire |
| 7 | `validate`: no `SCOPE (write)` section, `:880-886` | KEEP | `## SCOPE (write)` is in the template and in the worked brief |
| 8 | `validate`: no RETURN section, `:888-891` | REMOVE | `dev/ORCHESTRATION.md` is void under AD4. The branch block is the return contract |
| 9 | `validate`: no checkable evidence, `:898-900` | REMOVE | The same document. The template would pass it anyway: `## PREMISES` writes `file:line` |
| 10 | `rule_bundle_defects()`, `:2492-2539` | REMOVE | `AGENTS.md` is void under AD4. It stays LIVE until removed, because section 7.1 row 22 KEEPS `scripts/dispatch/rules.py` and the function's only escape is that file being absent |
| 11 | `dd4_defects()`, `:2328-2364` | REMOVE | DD4 = WRITTEN RULE, clause W2. See below |
| 12 | `survey_defects()`: no ARCHIVE section, `:2366-2422` | KEEP | DD18 = MECHANISED. Section 7.4 injects `## ARCHIVE`, and P15 refuses a brief without it |
| 13 | `survey_defects()`: no LITERATURE section, `:2366-2422` | KEEP | DD18 again. Section 7.4 injects `## LITERATURE`, and P15 reads it |
| 14 | `switch_defects()`, `:648-736`, called at `:755` | REMOVE | DD17 = SUPERSEDED. It is also inert once row 21 retires `dispatch_policy.py`, which makes `POLICY_ERROR` truthy |
| 15 | `unregistered_returns()` and its status block, `:1812-1854`, `:1926-1932` | REMOVE | `dev/PLAN.md` section 11, which `dev/pod/queue.toml` and the transition log replace |
| 16 | `_tree_maybe_live()`'s PLAN-row half, `:2237-2293` | REMOVE | The same replacement |
| 17 | `cmd_wait --all` refusal, `:2120-2127` | REMOVE | Dead code. The POD never runs `wait` |

**`dd4_defects()` goes with the other nine, and A7 is why that is a re-homing and
not a loss.** DD4 is a WRITTEN RULE, clause W2, and the program carries it into
`dev/pod/instructions/mathematician.md` at every dispatch. The gate cannot travel
with it: it reads the BRIEF FILE and demands the token `DD4` or both halves of
the DD4 sentence, and neither the template nor the worked brief carries one, so
keeping it refuses every POD dispatch from day 2 onward. Injecting the
instruction file at prompt time does not satisfy it, because the refusal never
reads the prompt. **W2 has no metric, by the owner's own decision, so its
`enforced by` value is `agent discipline` and section 3.1 states the loss.**

**Four more refusals sit in `launch()` itself, outside `launch_defects()`, and all
four are KEPT.** `_require_vendor_or_die()` at `:929`, defined at `:906-918`,
becomes a no-op once row 21 archives `dispatch_policy.py`, because `POLICY` is
then `None`. `SAFE_TASK` at `:930-933` accepts `LJ-1.386`, since the pattern at
`:624` admits a dot. `check_model()` at `:936` reads `BLOCKED_MODELS`, EMPTY at
`:81`, so it passes every model. The four registry guards at `:971-998` are AD17's
and section 5.6 keeps them.

### 6.3 The brief

AD9. The brief is one Markdown file at `agents/tasks/<CODE>/<CODE>.md`. The
machine half is one fenced block with the info string `toml pod-branches`, which
the pre-flight extracts and parses with `tomllib`; everything outside the block is
prose and is never parsed. The program wrote the brief and recorded its path in
the log line, so 282 existing briefs plus `dispatch.py:806-811` keep working.
**The template:**

````markdown
# <CODE>: <one line, what the deliverable obligation is>

## HEAD
head_slot: <mathematician | mathematician_adversarial | coder | coder_adversarial>
machine: <exclusive | shared>

## THE OBLIGATION
<One deliverable proof obligation, AD12. Name the file that will hold it
and the statement it must discharge.>

## OBLIGATION NAMES
obligations = ["<probe path>::<dotted name>", ...]   # section 4.7. Non-empty.

## SCOPE (write)
<Every file the worker may change, one bullet each, repository relative. The
program writes this list, and it is the same list the branches glob over.>

## PREMISES
<Each load-bearing premise, one per line, with a basis at file:line that
resolves today. The return marks each VERIFIED or REFUTED at file:line.>

## WHAT IS DELIVERED ALREADY
<Each leg that exists today, at file:line. A claim with no file:line is not
admissible here.>

## WHAT IS MISSING
<The gap this task closes, stated as a proposition.>

## LAWS (program-generated, do not edit)
<The bundle `rules.py --for <kind>` emits for the kind DERIVED from
`## SCOPE (write)`, verbatim. `dev/rules.toml` is its declaration and the cap is
`max_ids`. R17 and pre-flight P21.>

## ARCHIVE (program-generated, do not edit)
<The corpus hit list of section 7.4.>

## LITERATURE (program-generated, do not edit)
<The literature hit list of section 7.4.>

## THE REASONING
<The mathematician's prose. This half is never executed and gates nothing.>

## WHAT GO AND NO-GO EACH EARN
<Two paragraphs. A NO-GO must be worth as much as a GO.>

## BRANCHES
```toml pod-branches
[[branch]]
id = "go"           # a bare word. Admission namespaces it, section 4.2
priority = 10
action = "done"
outcome = "go"      # required on a done branch, absent otherwise. A6 and P19

  [branch.when]     # keys from section 4.3 only. An empty block is refused.
  exit_code = 0
  obligations_delta_max = -1     # minus the obligation count, or fewer. P19

[[branch]]          # P18 requires this one in EVERY brief.
id = "attacked"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]     # P20: it must not outrank a done branch it can match with.
  exit_code = 42
```
````

**`## LAWS` is how `dev/LESSONS.md` reaches a worker, and R17 is the rule.** The
measured lesson book is KEPT as an artifact, and without this section nothing in
the new flow delivers one line of it. The brief builder derives the KIND from
`## SCOPE (write)`: a scope naming a path under `src/` is a build, a scope naming
only `agents/tasks/<CODE>/` is a probe, and the remaining kinds of
`dev/rules.toml` follow the same derivation. **The kind is never declared in the
brief**, because a declared kind is a field an author can get wrong. Pre-flight
P21 refuses a brief whose LAWS block is absent or empty.

**`## SCOPE (write)` is required, and KEPT refusal 7 reads it.**
`dispatch.py:880-886` refuses a brief without that exact heading, and
`write_paths()` at `:1557` parses the section for AD17's territory check, so it is
the ONE write list. **What the program writes into it:** one bullet per path the
task may change, repository relative, with no prohibition wording, because
`write_paths()` drops any unit holding `never`, `read-only` or `do not write`.
Its regex matches only `src/`, `dev/`, `scripts/` and `_build/` paths, so a
probe-only task grants no contested territory. Pre-flight P8 and fact 4's scope
both read this section. **R18 adds one path automatically:** when the scope names
a `src/` master path that does not exist yet, the builder also writes
`src/Everything.lagda.md` into the scope, because acceptance conjunct 3 refuses a
tree whose catalog does not import the new master and no other rule gives that
import line an author.

**`## PREMISES` is new and it replaces a retired gate.**
`agents/tasks/LJ-1-211/lj-1.211-report.md:21` reads: `The brief caused 8 of the
10. The agent caused 2. The reviewer caused 0.` `check-premises-stated.py` is the
cure the project built for that, tuned against 118 live briefs
(`scripts/gate/check-premises-stated.py:4-6`). Nothing else in the POD catches a
bad brief before dispatch, so the section survives as pre-flight check P17 and
section 7.1 row 11 becomes REWRITE. Each `[[branch]]` then becomes a row with
`scope = "task:<CODE>"` when `admit_rows()` runs, per section 4.1.

### 6.4 The worked example: `[LJ-1.386]`

`dev/PLAN.md:63-66` names `[LJ-1.386]` as the first task on resumption; it was
registered as DISPATCHED and never dispatched. **Every section below is written
out, because a worked brief that omits a section cannot be checked against the
refusals that read it.** Only the prose BODIES are cut. The obligation is the
internal existence of a pairing code at `+ω ω`, whose delivered legs are `chosen`
at `src/L/Cardinal.lagda.md:194-195` and `small-inj` at
`src/L/Coding/Injection.lagda.md:147-151`, and whose missing leg is the
inhabitation of `∥ Σ[ A ∈ Mem (Lset β) ] ⟨ Good A ⟩ ∥₁`.

````markdown
# LJ-1.386: internal existence of a pairing code at a band ordinal, GO or NO-GO

## HEAD
head_slot: mathematician
machine: shared

## THE OBLIGATION / ## WHAT IS MISSING / ## THE REASONING /
## WHAT GO AND NO-GO EACH EARN
<prose, cut here. No refusal and no pre-flight check reads these four.>

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-386/Probe386.agda::code-exists",
               "agents/tasks/LJ-1-386/Probe386.agda::code-inj"]

## SCOPE (write)
- agents/tasks/LJ-1-386/Probe386.agda
- agents/tasks/LJ-1-386/lj-1.386-report.md

## PREMISES
- `chosen` is total on a band ordinal. Basis: src/L/Cardinal.lagda.md:194-195
- `small-inj` gives the injection. Basis: src/L/Coding/Injection.lagda.md:147-151

## WHAT IS DELIVERED ALREADY
- `Good`, the predicate the code must satisfy: src/L/Cardinal.lagda.md:186-189

## ARCHIVE (program-generated, do not edit)
Corpus search for: L.Cardinal, Good, small-inj
- archive/dev/TASKS-archived.md:80    (1 key hit)
- archive/dev/JOURNAL-archived.md     NO HIT

## LITERATURE (program-generated, do not edit)
Corpus search for: pairing code, band ordinal
- dev/literature/j-hierarchy.md       NO HIT

## BRANCHES
```toml pod-branches
[[branch]]
id = "go"
priority = 10
action = "done"
outcome = "go"

  [branch.when]
  exit_code = 0
  obligations_delta_max = -2
  heap_wall = false

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-386/review-of-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-386/Probe386.agda"]
  changed_files_none = ["agents/tasks/LJ-1-386/review-of-*.md"]

[[branch]]
id = "heap-wall-escalate"
priority = 30
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  heap_wall = true

[[branch]]
id = "ran-long-and-changed-little"
priority = 50
action = "park"

  [branch.when]
  seconds_min = 3600.0
  changed_files_count_max = 1
```
````

**Read the branch set carefully, because it carries the mathematics.** A NO-GO is
a DONE and not a failure. The obligation was to answer GO or NO-GO, and a stated
NO-GO with an unsolved metavariable and a written report discharges it. But a
first-pass `done` would never be reviewed, so `no-go-attacked` sits at priority
15 and sends the return to the adversarial head first. Pre-flight check P18
requires exactly that branch shape in every brief.

**The two `done` branches pass P19 two different ways, and A6 is why.** `go`
carries `obligations_delta_max = -2`: the list holds two names, so a worker that
discharges both gives -2, and a worker that writes nothing gives 0 and no longer
matches. `no-go-stated` carries no delta key at all, because **a NO-GO leaves
every declared name unresolved and the delta stays 0**; it passes P19 by
declaring `outcome = "no-go"`. The old `died-without-a-report` branch is deleted:
section 4.3.2 case 3 covers a worker that changed nothing, and it parks under R7.

**Both `done` branches are reachable.** `go` needs `exit_code = 0`, which under A5
means all six conjuncts held. `no-go-stated` needs 42, which is conjunct 1's Agda
code: the probe states the obstruction and does not typecheck.

**The `review-of-*.md` key is what keeps `no-go-stated` alive.** Under 4.3.2 case
2 the only Agda target is `Probe386.agda`, so exit 42 is producible ONLY when
that file is in the changed set. Without the key both rows match every NO-GO
record, priority 15 beats priority 20, `route()` is pure, the re-dispatch
reproduces the record, and `attempt_max` parks the task at 4 attempts.
**The two `when` blocks are DISJOINT by construction:** the escalate row demands
that no review file has been written, the done row demands that one has, and
section 6.6's reviewer is what writes it. Fact 4 is the exit snapshot and is
cumulative over a task's instances (4.3.1), so the second return still carries
`Probe386.agda` and still reads exit 42. **Pre-flight P20 generalises the fix**,
because P18 puts an escalate branch in every brief. **Admission renames every
branch**, so `go` becomes `task-lj-1-386-go`; a brief never writes that form.

**The token budget for writing one brief.** Measured with
`agents_tree.is_brief`: 282 briefs, median 8,309 characters; 286 reports, median
18,946. **At an ESTIMATED 3.0 characters per token, whose basis is the corpus
character count and not a tokenizer, one brief-writing turn reads about 119,000
characters, or about 39,700 tokens.** The program hands over the
`## SCOPE (write)` files and the sites named at `file:line`, never a whole
chapter, and caps the turn at 60,000 input tokens.

### 6.5 The pre-flight, AD21

The program runs the pre-flight BEFORE it spawns anything. Every check is a
predicate over the brief text and the filesystem: no check runs Agda, calls a
model or touches the network. The whole pre-flight is about 80 lines.

| id | Predicate | Refusal message |
|---|---|---|
| P1 | The brief file exists, and exactly one fenced block has the info string `toml pod-branches` | `P1 no brief, no branch block, or more than one` |
| P2 | `tomllib.loads(block)` raises nothing | `P2 branch block does not parse` |
| P3 | The branch list is non-empty | `P3 branch set is empty` |
| P4 | **AMENDED BY A10: a seventh key `lines` IS admitted.** | Every `when` key is in section 4.3's closed list | `P4 branch <id> matches on <key>` |
| P5 | Every `error_class` value is one of the eleven | `P5 branch <id> names class <value>` |
| P6 | Every `action` is one of the eight in section 4.2 | `P6 branch <id> names action <value>` |
| P7 | Every branch has a unique BRIEF-LOCAL `id` and a `priority`, and no two share a priority | `P7 branch <id> is a duplicate` |
| P8 | Every path in `changed_files_*` and under `## SCOPE (write)` resolves under the root, and either the file exists or its parent directory exists | `P8 branch <id> names <path>` |
| P9 | One branch or more has `action = "done"` | `P9 no branch can finish this task` |
| P10 | No two branches have an identical `when` block | `P10 branches <a> and <b> are identical` |
| P11 | The `head_slot` line names one of the five slots, and every `escalate` branch carries one | `P11 head slot <value> is not in heads.toml` |
| P12 | The heading code equals the directory name, mapped | `P12 brief code and directory disagree` |
| P13 | The `machine:` line reads `exclusive` or `shared` | `P13 machine class is missing` |
| P14 | `obligations` is present and non-empty, and every entry reads `<probe path>::<dotted name>` with the path under the root. **A1, A4** | `P14 obligation <n> is empty or malformed` |
| P15 | The `## ARCHIVE` and `## LITERATURE` blocks are present and every path in them resolves | `P15 injected block missing or dead path` |
| P16 | `check-closure.py --check closure` exits 0 | `P16 the tree was already open before this task` |
| P17 | `## PREMISES` is non-empty and every basis `file:line` resolves | `P17 premise <n> has no live basis` |
| P18 | One branch or more has `action = "escalate"` with `head_slot = "mathematician_adversarial"` | `P18 nothing can attack this return` |
| P19 | Every `done` branch carries an `outcome`, and passes EITHER by `obligations_delta_max <= -len(obligations)` OR by `outcome = "no-go"`. **A6** | `P19 branch <id> can close on no work` |
| P20 | No branch whose `action` is not `done` may be satisfiable together with a `done` branch it OUTRANKS under section 4.4 | `P20 branch <a> shadows done branch <b>` |
| P21 | The `## LAWS` block is present and non-empty. **R17** | `P21 the LAWS bundle is absent or empty` |
| P22 | For every directory in `## SCOPE (write)`, print that directory's `README.md` path when one exists. **It prints and never refuses** | none, P22 cannot refuse |

**P8 accepts a file that does not yet exist, when its parent directory exists**,
because `agents/tasks/LJ-1-386/Probe386.agda` is what the task writes. **P16 tells
the program whether the tree was already broken before this task ran**, which
stops a task being blamed for its predecessor's orphan.

**P19's second limb is A6 and it is not a loophole.** A NO-GO leaves every
declared name unresolved, so its delta is 0 and the first limb can never hold.
Without the second limb no brief could express a refusal. The limb costs nothing,
because P18 already forces every brief to carry a branch that ATTACKS the return.

**P18 is the answer to a measured failure**, and it is DD25's mechanised half. A
brief that can finish must also be attackable: `archive/dev/ORCHESTRATION.md:113-117`
records `[LJ-0.4]` refusing four blocks on measurement, the orchestrator
accepting all four, and `[LJ-0.8]` then finding a propagated sign error standing
in five places. P18 needs no seventh fact, because the mathematician names the
negative outcome's fact pattern in the branch.

**P20 exists because P18 can kill the branch it protects.** If the escalate
branch outranks a `done` branch and both match the same record, the `done` branch
is dead code, `route()` reproduces the same winner on every retry, and
`attempt_max` parks the task instead of closing it. **P20 is decided by a fixed
contradiction table over the two `when` blocks**, and it needs no solver: two
`exit_code` values that differ; two `_in` lists that are disjoint; two delta
ranges that do not overlap; or ONE glob that appears verbatim in one block's
`changed_files_any` and in the other's `changed_files_none`. **The limit is
disclosed:** a separation written two different ways is not recognised, and P20
then REFUSES the brief, which is the safe direction.

**P22 is the one check that cannot refuse, and it exists so a per-directory
`README.md` has a named reader and a named occasion.** Twenty of them live in the
tree and no live document names most of them. The pre-flight prints the paths
that cover the write scope, so a worker meets them before it writes. This
document restates none of their content.

**On a failed pre-flight the program parks the task. It never drops it.** It
appends one line whose `reason` is `"preflight:"` and the FIRST refusal's check
id, so `reason: "preflight:P4"`, with the whole refusal list in `detail`.
`preflight()` returns a LIST of refusal strings, each starting with its check id,
so rule (f) reads `d[0].split()[0]`. The program spawns nothing and continues,
and rule (a2) un-parks the task once the brief passes.

### 6.6 Adversarial review, AD27

The review fires two ways and the two share no code.

**The mathematician half. A second instance is REVIEWED before it is re-worked.**
Rule (f) performs it: when `t.attempt > 1` and `reviewed(t)` is false, the
dispatch that goes out is the REVIEW, on
`head_slot = "mathematician_adversarial"`. **What happens after the review is the
TABLE's**, because the review's return runs through the acceptance runner and
`route()` like every other return; the program decides nothing. Section 6.4's
`no-go-stated` branch is the worked case: it fires only once a review file exists.
**The critic is never the same model as the author:** the reviewer is
`claude-fable-5` and the author was `claude-opus-5`. The review cannot be the new
instance's own first act, because the brief's `head_slot` is the mathematician's
and a re-dispatch reuses that brief.

**ONE state record per code, and section 5.2 is authoritative.** `st.tasks` is
keyed by CODE, so the review is a second DISPATCH and not a second task: `role`
names which head is live and `attempt` counts the instances. Two records under one
code would also hit `dispatch.py:984-988`.

**The review's brief is program-written, `agents/tasks/<CODE>/review-<PRED>.md`.**
`launch()` demands a brief file, so the review needs one; the mathematician never
writes it. `review_brief(t, slot)` builds it from `dev/pod/instructions/<slot>.md`,
the slot rule (f) resolved, and fills four sections: `## SCOPE (write)` naming the
review file and `dev/JOURNAL.md`, `## ARCHIVE` and `## LITERATURE` from section
7.4's retrieval, and the three questions below. **`dev/JOURNAL.md` is in that
scope because the episode record needs a writer under the new flow**, and DD0
forbids a record ABOUT a ruling landing anywhere else. **It carries NO branch block, and the pre-flight
does not read it**, because it produces no routing of its own. It satisfies the
seven KEPT refusals of section 6.2, rows 1, 2, 5, 6, 7, 12 and 13, by
construction, which is why those four sections and no fewer are written.

**What the review reads about its predecessor, and all of it is tracked:** the
newest `agents/tasks/<CODE>/*-report.md`, the work brief, the probes
`agents/tasks/<CODE>/*.agda`, and the six facts, `model`, `effort` and
`heads_sha256` in that instance's transition log lines. **What it writes** is one
tracked file, `agents/tasks/<CODE>/review-of-<PRED>.md`, answering three
questions and nothing else. 1. Does the predecessor's verdict LINE match its own
BODY? The project measured that failure twice on 2026-08-16: `[LJ-1.375]` caught
it on `[LJ-1.373]`, and `[LJ-1.376]` named the orchestrator's own unread live
record the costliest defect in the tree. 2. Is every load-bearing claim backed by
a `file:line` that resolves today? 3. Is the predecessor's enumeration complete?

**The two file names differ on purpose.** The review BRIEF is `review-<PRED>.md`
and the review OUTPUT is `review-of-<PRED>.md`, so a branch globbing
`review-of-*.md` reads the reviewer's work and never the program's own input.
**A reviewer that writes nothing therefore changes no fact**, the same row matches
again, and `attempt_max` parks the task naming that row, which is honest.

A task with no predecessor has nothing to review, so rule (f)'s `t.attempt > 1`
test is false, `slot` is `None` and the work brief goes out.

**The coder half fires from a system row inside the six-fact vocabulary.** Row 2
of section 4.8 is that row. A second row is the one to write first:

```toml
[[row]]
id = "sys-coder-adversarial-on-heap-wall"
scope = "system"
priority = 90
action = "escalate"
head_slot = "coder_adversarial"
added = 2026-08-17
added_by = "maintainer"
reason = "A heap wall inside src/ is head-sensitive, so a stronger head reads it at the same cap."
expired = false

  [row.when]
  heap_wall = true
  changed_files_any = ["src/*"]
```

`dev/PLAN.md` section 0.0 records that `sucK` is the known 8 GB waller, and a heap
wall is the one failure this project has measured as recurring and head-sensitive.
The cap is C-12's quota and is never raised, so the only lever left is a stronger
head at the same cap: **the escalation does NOT raise `GHCRTS`.** This row and
`sys-heap-wall` both match; `priority` 90 against 100 decides it.

### 6.7 The maintainer, AD2 and AD15

**The trigger is mechanical.** Rule (e) of the tick spawns the maintainer when 12
hours passed since the last `batch` line in the transition log, or when the
PARKED count reaches 3. **The input is one program-written brief**,
`agents/tasks/POD-BATCH/<ts>.md`, pinned under `agents/tasks/` so KEPT refusal 2
of section 6.2 holds and `SAFE_TASK` at `dispatch.py:624` admits the name. The
program fills it from the log: every PARKED code with its `park_reason` and its
facts, every no-match record in the window, the shadowing list and the expiry
fallout list. **An `attempt_max:<row id>` park is the loudest input**, because it
names a row that matched again and again and never changed the facts.

**The output is one tracked file**, `dev/pod/proposals/<ts>.toml`, in the row
schema of section 4.2. The maintainer writes nothing else: it never edits
`dev/pod/table.toml`, never edits a brief and never runs the loop.

**R15, and the program enforces it rather than asking.** The batch brief carries
`## SCOPE (write)` naming that ONE proposal path, so `write_paths()` at
`dispatch.py:1557` grants nothing else, plus `## ARCHIVE` and `## LITERATURE`, so
it satisfies the seven KEPT refusals as the review brief does. At the return,
`harvest_batch()` runs `maintainer_scope_ok()` BEFORE the replay: it takes fact
4's snapshot, `git status --porcelain --untracked-files=all`, and REFUSES the
batch when any path other than the proposal file appears, tracked or untracked.
**The `--untracked-files=all` flag is why the untracked half is visible, and a
check that reads only the tracked half discards the information the flag paid
for:** a maintainer that writes a NEW file writes an untracked path, which is
exactly the class the flag exists to reveal. On a refusal it
writes a `batch` line with `result: "scope"` and the offending paths, appends
nothing, and hands that line to the next batch as input. **DISCLOSED NARROWING of
the ruled text:** the ruling names `dev/pod/table.toml` as the one write path,
and the design gives the maintainer the PROPOSAL file instead, because the replay
gate must sit between the model and the table. That is narrower and never wider.
The maintainer still writes table rows and nothing else, and it can no longer
reach section 3, section 3.1 or `heads.toml`, which is what the ruling protects.

**The gate is the replay, and `harvest_batch()` of rule (e) runs it**, through
the same writer admission uses: `replay(table, table + proposal, corpus())` of
section 4.5.1. On ADMIT the program appends the rows through `write_table()` and
commits by explicit path. On REJECT it writes the moved records back into the
proposal file and parks the batch, which is a maintainer input at the next batch.

**The maintainer may also ASK for a brief repair, and the program performs it.**
For a task parked with a `preflight:` or `no-change` reason, the proposal file
carries a `[[queue]]` request naming the failed check, and `harvest_batch()`
appends the entry to `dev/pod/queue.toml`. R15 is why the request is not a write.
It never repairs a brief itself either: AD3 gives the brief to the mathematician.

## 7. The gates

*In force since the POD cutover of 2026-08-18, commit `fc676cb`. `AGENTS.md` holds the shared Boundary, and `dev/ARCHIVE.md:214` records `dev/ORCHESTRATION.md` as archived.*

AD22, AD23 and A7.

### 7.1 The dispositions: every DD ruling, then every gate

*In force since the POD cutover of 2026-08-18, commit `fc676cb`. `AGENTS.md` holds the shared Boundary, and `dev/ARCHIVE.md:214` records `dev/ORCHESTRATION.md` as archived.*

**A7 gives every DD ruling exactly one disposition and lets none disappear.** The
column below names the enforcement point in force since the cutover of
2026-08-18. **THIS TABLE IS THE LIVE ENFORCEMENT RECORD.** `dev/PLAN.md` section
3 is SET ASIDE IN THIS FORM by A7 (`dev/PLAN.md:734`) and is kept as the record
of what the owner ruled and when; its own enforcement columns are historical and
several name a gate the cutover archived. Read that section for the ruling and
its date. Read this table for the enforcer. **A gate that
enforces a MECHANISED ruling is KEPT or REWRITTEN and never retired**, which the
second table obeys: every RETIRE row there names the disposition that released
it. A NOT CARRIED note is a real loss, stated rather than absorbed.

| DD | Disposition under `[L9]` | The enforcement point in force |
|---|---|---|
| DD0 | **SUPERSEDED IN PART** | The owner ruled the remainder back in on 2026-08-17. SUPERSEDED half: the owner's exclusive authorship of a TABLE ROW is replaced by a mechanical test on the WRITE, not on the writer, because AD2 gives the maintainer the rows: R3 refuses any new row that would move a record an existing row already matches, and `admit_rows()` calls `replay()` before it writes (4.1). **Two clauses are CARRIED and not superseded. Clause 1, WRITTEN RULE: clause W9 of section 3.1**, injected into every `dev/pod/instructions/<slot>.md`. It cannot be mechanised, because the act it forbids is an INFERENCE and the tokens it produces are legal by construction, so its enforcer is `agent discipline`. **Clause 2, MECHANISED in two halves: R15**, the maintainer's one-path write scope, checked by `maintainer_scope_ok()` at the batch return and before the replay (6.7); **and R16**, a named owner approval for any change to section 3, section 3.1 or `dev/pod/heads.toml`, checked by `check-spec-surface.py` at the `commit-msg` hook and again at conjunct 5 (7.3) |
| DD1 | **MECHANISED** | `check-spec-surface.py`, under R9. Twice: `--check` as acceptance conjunct 5, which runs FIRST of the six (5.4), and `--msg-file` at the `commit-msg` hook. A change makes fact 2 `spec_surface`, and `sys-spec-surface` acts `stop_loop`, which A3 sorts ahead of every task row. **NOT CARRIED: the prose half, never claim an unqualified `Con(ZFC)`. No checker ever read it and the POD reads no prose (R2)** |
| DD2 | **WRITTEN RULE** | Clause W1, section 3.1. The ruled half, both trophies stated in L, is separately mechanised by R9 over `src/Landmarks.lagda.md` |
| DD4 | **WRITTEN RULE** | Clause W2, section 3.1, injected into `instructions/mathematician.md` and `instructions/coder.md` |
| DD5 | **MECHANISED** | `validate_benchmark()` at `scripts/measure/ledger.py:194`, reached by `--check` at `:739`. It fires at every DONE, because the DONE handler runs `ledger.py --write` first (row 26), which is more often than `make check` fires it today. The caliber half holds too: the digest reads `dev/ledger.toml` (8.2). **NOT CARRIED: the gate is silent until `lines_state` moves off its unbound text (`ledger.py:222-226`), and no POD step measures the internalization route, so the line benchmark has no producer and the TIME benchmark has no home at all** |
| DD8 | **WRITTEN RULE** | Clause W3, section 3.1. Two halves are separately mechanised: the probe location by `check-probes.py` (row 6, gap M5), and the premise basis by pre-flight P17 |
| DD9 | **MECHANISED** | `lint-agda.py`: the `--safe` OPTIONS header at `:45` and `:268-275`, the `postulate` ban at `:286-289`, the forbidden pragmas by `FORBIDDEN_PRAGMAS` at `:49-50` tested at `:278-281`. Pre-commit and conjunct 6, row 1. `run_agda()` READS `--safe` from the file head and never assumes it (4.3.1), so the linter is the enforcement point and the runner is not. **NOT CARRIED: the generated-proof clause, "cheaper to READ than what it replaces", which is a judgement AD3 gives to the mathematician** |
| DD11 | **MECHANISED** | The prose half by rows 2, 3, 4 and 33, at pre-commit AND at conjunct 6, so twice as often as today. **NOT CARRIED: the naming half, which no gate ever read.** Its canonical statement is `dev/STYLE-agda.md` section 3: the decision tree at `:119-135` and the three clauses at `:137-141`, written into that file on 2026-08-17 because the tree did not hold them and setting `dev/PLAN.md` section 3 aside would have dropped all three. Section 1 names the file so it does not survive by omission |
| DD13 | **WRITTEN RULE** | Clause W4, section 3.1. One half is mechanised: `check_archive()` moves into `pod/check-closure.py` (7.2) at conjunct 3 and P16, so a live master can never import an archive-only module. Cutover steps 5, 6 and 8 obey W4 and archive rather than delete |
| DD15 | **MECHANISED** | Three points. `ledger.py --write` in the DONE handler re-measures at every close. `run_agda()` stamps R13's one caliber into every record. `admits()` gives a `machine: exclusive` task the machine alone and refuses it above `exclusive_max_load1` (5.6). **NOT CARRIED: the COLD protocol. Fact 5 is a warm incremental wall from `time.monotonic()`, and no POD step moves the interface cache aside** |
| DD17 | **SUPERSEDED** | **THE CONTRADICTION, which is why it cannot be carried:** DD17 makes a WALL CLOCK pick the head at dispatch, and `validate()` REFUSES any brief whose `tier:` line disagrees with the mode the clock is in (`dispatch.py:813-819` and `:838-857`, section 6.2 rows 3, 4 and 14). A POD brief carries `head_slot:` and no `tier:` line, so under DD17 every POD dispatch is refused, and a head that changes with the hour also makes `route()`'s record irreproducible against R11. Replaced by a static slot: `dev/pod/heads.toml`, the brief's `head_slot:` line, pre-flight P11, and R11's tracked log line with `heads_sha256`. The critic invariant SURVIVES mechanically, because `[heads]` pairs every author with a different model (6.1) and P18 makes an attack branch mandatory. **NOT CARRIED: "an idle agent slot is a defect". An empty `dev/pod/queue.toml` idles the whole loop and no digest field counts it. Gap M12** |
| DD18 | **MECHANISED** | Three points. The brief builder injects both blocks at brief build, before dispatch (7.4). Pre-flight P15 refuses a missing block or a dead path. `check-survey-quotes.py` fails the return at conjunct 6 when an injected path is unanswered or a quote does not sit at its line. `survey_defects()` is KEPT at launch (6.2, rows 12 and 13) |
| DD19 | **WRITTEN RULE** | Clause W5, section 3.1. Part 2, registration before starting, is mechanised by `dev/pod/queue.toml` plus the program-written transition log, which makes the 200-character cap moot. Part 3a's mechanism is harvested into R9's trailer. **The two-agent naming pipeline and the ruling/episode/law division are carried INSIDE clause W5 itself**, because the ruled text retired "ask the owner" and a clause that restored it would supersede DD19 rather than carry it. `dev/ORCHESTRATION.md` section 8, the pipeline's old operational home, archives with the file |
| DD22 | **MECHANISED** | `reuse lint` at `make check`, row 34, and it survives in the rewritten check line of cutover step 10. `check_spdx` moves into `lint-agda.py` at cutover step 7 and fires at pre-commit and conjunct 6. Nothing in the new flow touches this ruling |
| DD23 | **WRITTEN RULE** | Clause W6, section 3.1. Nothing mechanical ever enforced it and nothing can: no parser separates mathematical exposition from a code comment. The obligation grammar leans the same way, because a pure-prose task resolves no dotted name and cannot close honestly under P19 |
| DD24 | **AMENDED BY A10: NOT SUPERSEDED, the RATIO form is RESTORED.** Fact 7 `lines` is added and P4 admits a seventh key. The superseded reading below is kept as the record of what the design first proposed. The bar is a RATIO, seconds over in-fence lines, and there was no `lines` fact; a ratio needs a seventh key and P4 refuses one. Replaced by fact 5, raw wall seconds under R13's caliber, which `matches()` refuses against a record whose `concurrency` is not 1. The tool survives as a maintainer profiler with its bar VOID, row 29. **NOT CARRIED: no automatic quality bar exists, no seeded row carries a `seconds_max`, and the one-home guard retires with row 18. Gap M13** |
| DD25 | **MECHANISED** | Three points, against a row that admitted no machine enforced its trigger. Pre-flight P18 refuses a brief with no branch that can attack the return. Rule (f) makes every second instance a review dispatch on `mathematician_adversarial`. An `escalate` row with a `head_slot` dispatches the named critic at routing time. `heads.toml` makes the critic a different model by construction. **NOT CARRIED: a first-instance NO-GO closes through a `done` row and never reaches attempt 2, so it gets no review. Gap M14** |
| DD26 | **MECHANISED** | `UNCOUNTED` at `scripts/measure/ledger.py:112` and `countable_masters()` at `:129`, which every size site calls. It fires at every DONE close and again at every digest. `test_ratio_baseline.py` and `test_deletion_test.py` are not archived at the cutover, so both keep pinning the exclusion |
| DD27 | **WRITTEN RULE** | Clause W7, section 3.1. It is already discharged in the tree at `src/L/Hull.lagda.md:72-73` and `:115`, and `L.Hull` is outside the spec surface, so conjunct 5 never sees the index. Conjunct 1 catches only an INCONSISTENT re-index, never a coherent one |
| DD28 | **WRITTEN RULE** | Clause W8, section 3.1. The ORDERING half is mechanised and improved: 7.4 injects the literature block into the probe's own brief before dispatch, so the survey cannot be a separate task and cannot be skipped. The ABORT half is the judgement, and AD3 gives it to the mathematician |

**Now the gates. Derive the retirement list from the `check:` line, never from the
number 19**, the file count of `scripts/gate/`: the `check:` line names 25 targets and
four gates live outside that directory. **Then add every module under `scripts/`
that has importers but no target**, because the `check:` line names no library and a
Makefile derivation is structurally blind to one. Rows 35 and 36 are the two that
rule finds. **Class** is PROCESS (a rule AD4 voids or
A7 re-homes), PHYSICS (a fact about the tree, the compiler or the clock), LINT,
HOUSEKEEPING or LICENSING. **Runner** names what fires the check.

| # | Script | Class | Disposition, and what released a retirement | Runner |
|---:|---|---|---|---|
| 1 | `gate/lint-agda.py` | LINT plus PHYSICS | **KEEP** | pre-commit; conjunct 6 |
| 2 | `gate/lint-prose.py` | LINT | **KEEP**, gains `check_shared_cjk` | pre-commit; conjunct 6 |
| 3 | `gate/check-glossary.py` | LINT | **KEEP** | pre-commit; conjunct 6 |
| 4 | `gate/check-fences.py` | PHYSICS | **KEEP** | pre-commit; conjunct 6 |
| 5 | `gate/check-tree.py` | MIXED | **REWRITE** as `pod/check-closure.py`, 7.2 | conjunct 3; P16 |
| 6 | `gate/check-probes.py` | PHYSICS | **KEEP** by amendment, gap M5 | pre-commit; conjunct 6 |
| 7 | `gate/check-live-territory.py` | PHYSICS | **RETIRE**. Released by R8, which performs the same function inside the program | retired |
| 8 | `gate/check-agents-guard.py` | PROCESS | **RETIRE**. Released by DD19 = WRITTEN RULE: the guarded file is void and 7.3 harvests the trailer mechanism | retired |
| 9 | `gate/check-archive-cited.py` | PROCESS, protected function | **REWRITE**, section 7.4. DD18 = MECHANISED | the program, at brief build |
| 10 | `gate/check-dd18-survey.py` | PROCESS, protected function | **REWRITE**, section 7.4. DD18 = MECHANISED | conjunct 6 |
| 11 | `gate/check-premises-stated.py` | PROCESS form, PHYSICS function | **REWRITE** into pre-flight P17. DD8's premise half | P17 |
| 12 | `gate/check-dd4-stated.py` | PROCESS | **RETIRE**. Released by DD4 = WRITTEN RULE, clause W2 | retired |
| 13 | `gate/check-dd25-review-named.py` | PROCESS | **REWRITE** into pre-flight P18 and rule (f). DD25 = MECHANISED, so the function moves and does not die. The FILE archives, because it reads `dev/PLAN.md` section 11 | P18; rule (f) |
| 14 | `gate/check-task-index.py` | PROCESS | **RETIRE**. Released by DD19's part 2, which `dev/pod/queue.toml` and the program-written log mechanise | retired |
| 15 | `gate/check-rule-ids.py` | HALF PROCESS | **REWRITE**, narrowed to `dev/LESSONS.md` and `dev/rules.toml`. The second target is not optional: a bundle that names an ID no entry carries is a dead reference nothing else catches | pre-commit |
| 16 | `gate/check-dev-docs.py` | PROCESS | **RETIRE, and the release covers TWO of its six subchecks. The other four are dispositioned in the note below** | retired |
| 17 | `gate/check-build-manifest.py` | HOUSEKEEPING | **RETIRE**. It never fails, and no POD file lives under `_build/` (4.0). The DATA file `dev/build-manifest.toml` is KEPT, and the owner's ruling of 2026-08-13 that it encodes is re-homed to clause W12 | retired |
| 18 | `gate/check-baseline-home.py` | PROCESS | **RETIRE**. Released by DD24 = SUPERSEDED, which voids the bar it guarded | retired |
| 19 | `gate/check-live-record-claims.py` | PROCESS | **RETIRE**. Released by AD4: it reads `dev/PLAN.md` sections 0.0 and 11, which `dev/pod/queue.toml` replaces | retired |
| 20 | `dispatch/check-dispatch-policy.py` | PROCESS | **RETIRE**. Released by DD17 = SUPERSEDED | retired |
| 21 | `dispatch/dispatch_policy.py` | PROCESS as policy | **REWRITE** into `dev/pod/heads.toml`. DD17 = SUPERSEDED | the loader, 6.1 |
| 21b | `dev/vendors.toml` (data, not a script) | PROCESS as policy | **REWRITE** into `dev/pod/heads.toml`. Its ONE programmatic reader is `dispatch_policy.py:159`, which row 21 archives, so without this row the file is an orphan. Carry the measured model IDs, the `pi auth check` finding at `:144-152` and the `pi --list-models` rule at `:151-152` into the new file's comments before archiving | the loader, 6.1 |
| 22 | `dispatch/rules.py` | HALF PROCESS | **KEEP**, out of the `make check` gate and INSIDE the brief builder: R17 makes it the producer of the `## LAWS` block, which is how `dev/LESSONS.md` reaches a worker | the program, at brief build |
| 23 | `dispatch/check-sources-read.py` | PHYSICS | **KEEP** and retarget, 7.4 | digest, from day 7 |
| 24 | `dispatch/dd25-record.py` | PROCESS | **REWRITE** into the transition log's `role` field. DD25 = MECHANISED, so the record survives; the FILE archives, because it reads the untracked registry | `emit()`, 5.3.1 |
| 25 | `dispatch/recall-hook.py` | INOPERABLE | **RETIRE**. Released by physics: a hook fires only for an in-harness subagent | retired |
| 26 | `measure/ledger.py` | PHYSICS | **KEEP**. It supplies AD7's number | the DONE handler; digest |
| 27 | `measure/obligations.py` | PHYSICS | **KEEP** as a size tool. It is not fact 3 | maintainer |
| 28 | `measure/check-timing.py` | PHYSICS | **KEEP** as a profiler. It is NOT fact 5 | maintainer, `make timing` |
| 29 | `measure/check-ratio.py` | tool PHYSICS, bar PROCESS | **KEEP** the tool, **RETIRE** the bar. DD24 = SUPERSEDED | maintainer |
| 30 | `measure/check-unbound-hyp.py` | PHYSICS | **KEEP**, promoted into conjunct 4 | the pre-flight snapshot, which carries the finding SET on the task as `unbound_before`; conjunct 4 |
| 31 | `measure/deletion-test.py` | tool PHYSICS, cap PROCESS | **KEEP** the split, **RETIRE** the cap | maintainer |
| 32 | `measure/dispatch-usage.py` | PHYSICS | **KEEP** as a maintainer profiler. Cutover step 4 repointed its store (`scripts/measure/dispatch-usage.py:85`) and NOTHING CALLS IT: the retarget to the digest was designed and not built, and section 8.1 sources no field from it | maintainer |
| 33 | `site/weave-i18n.py` | PHYSICS | **KEEP**. The `markers` gate | pre-commit; conjunct 6 |
| 34 | `reuse` (external tool) | LICENSING | **KEEP** | `make check` |
| 35 | `repo_root.py` | PHYSICS | **KEEP**. The one root walk; 31 scripts import it. Every new `scripts/pod/` file MUST use `find_root()` and must never compute a depth | imported by every gate and every pod module |
| 36 | `agents_tree.py` | PHYSICS | **KEEP**. `task_dir()` and `is_brief()`; 9 non-test scripts import it today, and the brief builder and the digest both call it | the program, at brief build and at digest |
| 37 | `.claude/skills/*/SKILL.md` and the Claude Code memory directory | PROCESS | see the third table below. Every head is `harness = "herdr-claude"` at the repository root, so all 17 files auto-load ahead of `dev/pod/instructions/<slot>.md` | auto-loaded at every dispatch |

**Totals: 6 KEEP in the lint class, 8 REWRITE, 10 KEEP as tools, 10 RETIRE**, and
the four sum to the 34 GATE rows. **Rows 35 and 36 are the two shared libraries
the `check:` line derivation cannot see, and row 21b is the data file the same
derivation cannot see. Row 37 is the auto-loaded instruction surface**, which no
Makefile target names either. KEEP-lint rows 1, 2, 3, 4, 6, 33; REWRITE rows 5, 9,
10, 11, 13, 15, 21, 24; KEEP-tool rows 22, 23, 26 to 32, 34; RETIRE rows 7, 8, 12,
14, 16 to 20, 25. Rows 29 and 31 keep a tool and retire a threshold, so they count
as KEEP. **No MECHANISED ruling lost a gate:** rows 13 and 24 are the two the
first table forced from RETIRE to REWRITE. Nine notes carry the reasons the
table cannot hold.

- **Row 16 declared SIX subchecks and its release covers TWO. The other four get
  a disposition here, written 2026-08-18 after an audit found the gap.** The
  retired file lists them at `archive/scripts/gate/check-dev-docs.py:321-328`.
  **`agents-size` and `plan-cell-size` are the two AD4 releases**, and the row
  states them. The four that remain:
  - **`lessons-imported-routing`: NOT CARRIED, and it is a real loss.** It
    refused a `dev/LESSONS.md` entry marked imported that `dev/rules.toml` routes
    into no bundle. `dev/LESSONS.md` is KEPT and R17 makes `rules.py` the only
    path from a law to a worker, so an unrouted law now reaches nobody and no
    gate says so. Row 15's narrowed `check-rule-ids.py` resolves an ID and never
    asks whether a bundle names it.
  - **`plan-section0-date`: NOT CARRIED, and cutover step 12b is its only
    remaining performer.** It refused a `dev/PLAN.md` section 0 whose heading
    date lagged the work the section describes. Section 0 stays the screen that
    `AGENTS.md:28-30` sends every slot to, so a stale screen is still a live
    cost, and nothing mechanical measures it.
  - **`memo-status-form`: NOT CARRIED.** It checked the form of a
    `**Status: ...**` header in a `dev/memos/` file. R16 covers THIS memo by
    sha256 and covers no other memo.
  - **`agents-enforcers`: NOT CARRIED, and it was the meta-gate.** It resolved
    every `scripts/*.py` path named in the enforcement table and refused a name
    that no file carries. Section 3's `enforced by` column and the two tables
    above name scripts by path, and nothing resolves them today. **The cheapest
    home is one more limb on `check-spec-surface.py --check`:** read every
    `scripts/*.py` path this section names and refuse a path that does not
    resolve. That work is not done, and this sentence is the record that it is
    owed rather than absorbed.
- **Row 4 is not optional.** `check-fences.py:4-16`: `[LJ-1.41]` reported two
  agreements machine-checked, `[LJ-1.42]` found both outside the fence with four
  real defects, and every gate passed, because unfenced text is invisible.
- **Row 7 retires and its function moves into the program.**
  `check-live-territory.py:4-6`: on 2026-08-13 two `git add -A` calls swept a
  sibling agent's work into the orchestrator's commit. The program commits now, so
  R8 covers it. **R8 also states that the program NEVER pushes**, and the reason
  is carried by R8 itself: one push is one CI run and one deploy.
- **Row 15 splits cleanly, and it must be narrowed BEFORE this document is
  committed.** `dev/LESSONS.md` is KEPT, so a `C-39` citation must still resolve,
  and `dev/PLAN.md` section 3 would be set aside, so that half would die with it. The 150 dangling references this row was written for are gone:
  section 2's decisions carry the `AD` prefix since 2026-08-17, so the code space
  no longer collides. RE-MEASURED 2026-08-17 after the rename: the un-narrowed
  checker exits 0 on the committed document. The narrowing is still correct at
  the cutover, and it is no longer urgent.
- **Row 25 retires on physics.** Hooks fire only for in-harness subagents.
- **Row 26 needs a writer, not only a reader.** `scripts/measure/ledger.py:34-35`
  fails the commit gate the moment the declaration goes stale, so **the DONE
  handler runs `ledger.py --write` before it commits**. **`--write` is a no-op
  alias for `--check` today**, recorded as such at `scripts/measure/ledger.py:42`
  and performed at `:806-809` by `if mode == "write": mode = "check"`. So day 5
  BUILDS the writer: delete that collapse, and give the `write` branch a body
  that re-derives the standing figure and writes it back into `dev/ledger.toml`.
  Leave `--check` unchanged. Without this the DONE handler commits a stale
  declaration and the same commit fails its own gate.
- **The suites need a runner, and today they have none.** `make test` runs 18
  suites of the `test:` target, `.github/workflows/typecheck.yml` runs only
  `make check`, and no hook runs either. MEASURED 2026-08-17: two of the 18 are
  red and nothing surfaced it. Cutover step 10b adds `make test` to
  `typecheck.yml` beside `make check`, so an archived script's orphaned suite
  reddens CI instead of waiting for a human.
- **Seven tracked scripts sit outside this table AND outside `make check`, and
  the POD does not touch them:** `scripts/site/extract-types.py`,
  `gen-depmap.py`, `i18n_markers.py`, `link-check.py`, `render-site.py`,
  `depmap-template.html`, and `scripts/ops/agda-watchdog.sh`. They run from
  `make site`, `make serve`, `make gen` and the two deploy workflows.
  `link-check.py` is the only script the deploy runs. Their index is
  `scripts/README.md` and it stays their canonical home.

**The third table: the auto-loaded instruction surface of row 37.** Every head is
`harness = "herdr-claude"` and the program runs with cwd at the repository root,
so a worker pane loads `CLAUDE.md`, the eight `.claude/skills/*/SKILL.md` files
and the nine memory files under
`/Users/alsg/.claude/projects/-Users-alsg-Agentic-Bedrock/memory/` BEFORE it
reads `dev/pod/instructions/<slot>.md`. None of them is tracked, so no gate reads
one.

| File | Disposition |
|---|---|
| `.claude/skills/dispatch-herdr/` | **RETIRE** at cutover step 4c. It teaches DD17's clock, the `tier:` line, the PLAN section 11 registration and ten refusals edit 6 removes. Harvest its three measured facts into `dev/LESSONS.md` first |
| `.claude/skills/codex-dispatch/SKILL.md` and `references/` | **RETIRE** at cutover step 4c. `.state/` is KEPT, because section 9.2 salvages it |
| `.claude/skills/update-agents-md/` | **RETIRE** at cutover step 4c. Its output document is void, and R16 makes `instructions/<slot>.md` owner-approved, so a skill that regenerates a rule home would defeat R16 |
| `.claude/skills/asd-ste100/` | **KEEP**. It is clause W10's reference material for English |
| `.claude/skills/tech-doc-style-chinese/` | **KEEP**. It is clause W10's reference material for Chinese. Its project-override step names section 3.1 of this memo and `dev/STYLE-i18n.md`, never `AGENTS.md` |
| `.claude/skills/artifact-over-proxy/`, `load-bearing-claim/`, `herdr/` | **KEEP**. All three are general craft and name no retired mechanism |
| `memory/MEMORY.md` | **REWRITE**. Its index sentence names `AGENTS.md` and `dev/PLAN.md` section 3, and both would be set aside |
| `memory/dispatch-doctrine.md` | **REWRITE** down to the heap caps and the 2026-08-02 crash. The rest describes DD17's clock |
| `memory/owner-communication.md` | **REWRITE**. Its ASD-STE100 restatement becomes a pointer to clause W10 |
| `memory/repo-and-docs-infrastructure.md` | **REWRITE**. Its `AGENTS.md` section names a void file and a retired gate |
| `memory/translation-terminology.md` | **REWRITE**. It points at `dev/ORCHESTRATION.md` section 8, and clause W5 is the new home |
| `memory/bedrock-canonical-docs.md`, `orchestrator-failure-modes.md`, `probe-and-retirement-doctrine.md`, `fol-reification-sister-project.md` | **KEEP**, with their dead script paths written as bare file names |

### 7.2 The closure check, and why AD13 does not cover it

`check_closure()` at `scripts/gate/check-tree.py:131` requires every master under
`src/` to appear in `src/Everything.lagda.md`'s import list. Its reason, at
`check-tree.py:10-15`: `make check` typechecks exactly one file, so a master
nobody imports is never typechecked while the gate goes green. Verified today: it
prints `clean (99 masters; closure)` and exits 0.

**AD13 leaves a hole.** A task writes a new master `src/L/Foo.lagda.md`, never
edits `src/Everything.lagda.md`, and passes: Agda is green on the file, the
consumer set is empty, and `make check` never reads `L.Foo`. But
`ledger.py:123-126` counts it, so **`src/` records a net gain from code the trophy
does not depend on, and the digest prints it as progress.** **The check gets three
homes, all program-side:** conjunct 3, pre-flight P16, and the digest's orphan
master count.

**Carry two more physics checks across with it.** `check_archive()` at
`check-tree.py:155` stops a live master importing an archive-only module, which is
DD13's mechanised half, and the archive grows at the cutover. `check_module_body()`
at `:279` catches C-11's silent empty parameterized module. **Retire
`check_retiring`**: it already returns `[]` on every run, because
`dev/ledger.toml` sets `retire_suspended` (`check-tree.py:251`).

**Two more halves, ruled here so the rename carries nothing unruled.** **KEEP
`check_closure_new()`** at `check-tree.py:222`: it is the untracked-master WARN
that section 4.3.2 case 3 relies on. **RETIRE `--gate-debt` and `--gate-passed`**
(`check-tree.py:297-321` and `:341-359`) with the batched-gate protocol they
served: the acceptance runner of section 5.4 typechecks at every return, so no
gate debt is left to count. Delete `LAST_GATE`, and delete the `.last-gate` row
at `dev/build-manifest.toml:122` in the same commit. **The file's seven subchecks
now all have a disposition**, and so do both counter modes.

**The write side has an author, and R18 is it.** The check refuses a master the
catalog does not import, and until R18 no rule said who writes the import line.
`AGENTS.md` said the orchestrator did, and the POD has no orchestrator. So the
brief builder puts `src/Everything.lagda.md` into the write scope of any task
whose scope names a `src/` path that does not yet exist, and the conjunct has an
author and not only a checker.

### 7.3 The spec surface gate, AD22

**The derivation reproduces the ruled figures exactly.** The surface is
`src/Landmarks.lagda.md` plus one file per `open import` in its fences. A bare
`import M` is excluded. Verified today at `src/Landmarks.lagda.md:21-29`, with
in-fence lines: `Landmarks` 19 (root), `Base/Prelude` 28, `Base/Impredicativity`
14, `Base/Classical` 59, `Base/Choice` 84, `V/Hierarchy` 44, `FOL/ZFModel` 89 and
`L/Constructible` 162. That is **499 lines over 8 files**, which reproduces the
ruled figures to the line. `V/Model` (285, `:28`) and `L/Model` (35, `:29`) are
bare imports and are excluded; one audit counted all 9 and reported 819 lines as
a mismatch. The two bare imports hold the PROOFS, and `src/Landmarks.lagda.md:77`
reads `L⊨ZFC = L.Model.L⊨ZFC`, so a signature change there fails to typecheck.

**The 7 `open import` files supply the VOCABULARY of the trophy statement.**
Change `isZFCModel` at `src/FOL/ZFModel.lagda.md:419`, or `𝒮ʟ` at
`src/L/Constructible.lagda.md:410-411`, or `LEM` at
`src/Base/Classical.lagda.md:41-42`, and **the trophy still typechecks while it
asserts something different.** No compiler catches that class. **The import block
is itself a guarded declaration:** delete `open import Base.Classical using (LEM)`
and inline a local `LEM`, and the surface silently shrinks to 7 files.

**THE SURFACE GUARDS THE LANDED TROPHY ONLY, and that is stated rather than
absorbed.** The derivation reads `src/Landmarks.lagda.md`'s import table, and
that file does not import `L.GCH`, so `GCHStatement` at `src/L/GCH.lagda.md:59-60`
sits outside the guarded set. R9 and AD22 therefore protect `L ⊨ AC`'s statement
and leave `L ⊨ GCH`'s statement unguarded for the whole build, which is the half
the route still has to prove. **When the GCH trophy lands, its statement is added
to `src/Landmarks.lagda.md` as an `open import`, and the surface grows to 9 files
by the same derivation with no rule change.** Gap M15 carries it until then.

**A declaration signature is any of four forms, inside an ` ```agda ` fence, with
its full type text.** A named signature, where the first token is a name and the
next token at the same nesting is `:` and not `:=`; a `data` or `record` head plus
every constructor and every `field` signature under it; a parameterized `module`
header, because the parameter is part of the statement; and an `import`,
`open import` or `open import ... public` line with its whole `using` or
`renaming` clause. A definition body, a `where` block's contents, a comment and
all prose are NOT signatures, so a worker may rewrite a proof freely.

**Extraction, without a full Agda run.** Reuse `FENCE` at `check-tree.py:101` and
`code_of()` at `:115`. Cut declarations by INDENT: a head starts at column `c`,
and its signature text runs to the first line at or left of `c`, or to a bare
`where`. Skip these leading keywords when deciding whether a line is a head:
`private`, `abstract`, `opaque`, `instance`, `variable`, `infix*`, `syntax`,
`pattern`, `{-#`. Recurse INTO `private` and `opaque` blocks, because a private
name can still appear in a public type. Strip comments, collapse whitespace, and
never sort tokens. Emit `<module>#<name> :: <type>` and hash it; `#` and not
`::`, because section 4.7 gives `::` to obligations.

**The snapshot, `dev/pod/spec-surface.toml`, tracked.** It carries
`derived_from`, `derivation`, `files`, `lines`, and one `[[declaration]]` per
signature with `file`, `name`, `text` and `sha`. Regenerate with `--write`.

**R16 rides the same snapshot, and that is the whole mechanism.** The file gains
a `[[guarded]]` entry per RULE HOME: this memo, which carries section 3 and
section 3.1, `dev/pod/heads.toml`, and every `dev/pod/instructions/*.md`. A
guarded entry is one sha256 over the WHOLE file and needs no parser. A changed
sha fails `--check` exactly as a changed signature does, so conjunct 5 gives the
record `error_class = "spec_surface"` and `sys-spec-surface` stops the loop; and
`--msg-file` refuses the commit unless the message carries the trailer. **No
second mechanism, no second trailer, no second checker.**

**The approval mechanism copies `check-agents-guard.py`, 147 lines**, which is
where DD19's harvested half lands. Three parts reuse directly: the trailer regex
at `:66`; the commit-time gate at `:120-133`, which reads
`git diff --cached --name-only` and is what tests R16's guarded paths; and the
self-anchoring history audit at `:86-117`, where `tree_has_guard` asks
`git cat-file -e <commit>:<home>`, so a commit from before the guard existed is
never judged. The trailer is `Spec-surface-approved: 2026-08-17 (choukh)`.
**Three modes:** `--check` for the POD, at conjunct 5; `--msg-file <path>` for
the `commit-msg` hook; no argument for the history audit.

**Wiring, and it needs no new fact.** Under A5 the checker IS conjunct 5, so its
verdict is fact 2 and the system row reads one key:

```toml
[[row]]
id = "sys-spec-surface"
scope = "system"
priority = 1
action = "stop_loop"
added = 2026-08-17
added_by = "owner"
reason = "A change inside the trophy spec surface stops the loop until the owner names an approval."
expired = false

  [row.when]
  error_class = "spec_surface"
```

**The row reads fact 2 and never a path glob.** A glob over the surface files
fires on a comment edit and misses a signature change outside them; the CHECKER
decides instead, and section 5.4 runs it FIRST of the six conjuncts. **A3 makes
the row undefeatable:** its action is `stop_loop`, so section 4.4 sorts it ahead
of every task row, whatever priority a brief writes.

**The honest limits, written down so no row claims more than the checker
delivers.** It cannot tell a good change from a bad one; it makes the change
visible and dated. **It cannot see a DEFINITION body, and that is a real hole:**
`src/L/Constructible.lagda.md:410-411` reads `𝒮ʟ : ...` then `𝒮ʟ = 𝒮ᵥ ↾ isL`, so
weakening `isL` makes the trophy a different theorem while every hash holds. Gap
M6. It also stops at the repository boundary, at gap m4.

### 7.4 The surveys, AD23

**What `check-dd18-survey.py` really enforces, in two unequal halves.** The
return side GATES: every archive path the brief cites must be ANSWERED in the
return (`answered()` at `:302`), a written DECLINE counts as compliance, and
**per archived file named as read, a quoted phrase of 12 characters or more must
occur AT the cited line** (`audit_quotes()` at `:339`). The brief side PRINTS and
never gates. Measured today: 19 gated tasks at or after LJ-1-363, 0 defects; 282
live briefs, of which 244 never name `JOURNAL-archived.md`. **The form is healthy
and the content is not. The replacement splits it into three parts.**

**Part 1, RETRIEVAL, moves to the program.** At brief-build time the program runs
a mechanical corpus search and INJECTS the result into the brief, under
`## ARCHIVE` and `## LITERATURE`. The worker cannot skip a survey it never had to
perform. The corpora are fixed paths: `archive/src/**`,
`archive/dev/TASKS-archived.md`, `archive/dev/JOURNAL-archived.md`,
`archive/dev/DECISIONS-archived.md` and `dev/ARCHIVE.md` for the archive block;
`dev/literature/**` for the literature block. The keys are derived and never
typed: the write scope's module names, and the obligation list's declaration
names. **Retrieval also keeps `survey_defects()` satisfiable**, because section
6.2 KEEPS that refusal and it reads exactly these two headings.

```markdown
## ARCHIVE (program-generated, do not edit)

Corpus search for: L.Rud.BelowLim, leaf residue, isLayer
- archive/src/2026-08-09-rud-route/Everything.lagda.md:1218  (3 key hits)
- archive/dev/TASKS-archived.md:80                           (1 key hit)
- archive/dev/JOURNAL-archived.md                            NO HIT
```

**A `NO HIT` line is a first-class result.** It removes the whole class of
"declined by ritual", because the program declined it and not the author.

**Part 1a, THE RETRIEVAL SEAM.** ONE function builds both blocks, and its
signature is fixed. The first implementation is scoped BM25. A later
implementation replaces this one function and nothing else.

```python
retrieve(query: str, scope: list[str], k: int) -> list[tuple[str, float]]
```

- `query`: the write scope's module names, the obligation declaration names, and
  the brief's GOAL text.
- `scope`: repository-relative directory prefixes. The builder passes the archive
  corpus above for `## ARCHIVE`, and `dev/literature` for `## LITERATURE`.
  **It never passes the whole tree.** The next paragraph is the reason.
- `k`: how many candidates to inject. It starts at 5.
- returns: `(repository-relative path, score)`, highest score first.

**THE SCOPE IS THE MEASURED PART, and the ranker is not.** MEASURED 2026-08-17
over the seven archive cases among the labelled detour episodes of
`agents/tasks/LJ-1-376/lj-1.376-report.md`. The same BM25 ran twice, with the
same constants `k1=1.5` and `b=0.75` and the same queries: once over the whole
corpus of 1,706 documents, and once over the archive scope alone. Only the scope
changed. The record is
`dev/measurements/pod-retrieval-scoping-2026-08-17.txt`.

| episode | full corpus, of 1,706 | scoped | scope size |
|---|---|---|---|
| 7 | 444 | 1 | 97 |
| 7b | 57 | 1 | 97 |
| 11 | 15 | 2 | 6 |
| 5 | 295 | 3 | 97 |
| 10 | 123 | 3 | 6 |
| 5b | 1,429 | 16 | 97 |
| 6 | 1,464 | 28 | 97 |

**THE TABLE IS THE 2026-08-17 RECORD AND TWO OF ITS SCOPED RANKS HAVE MOVED.**
Keep the table as it stands, because it is the measurement. MEASURED 2026-08-18:
episode 11 moved from scoped rank 2 to 3, and episode 10 from 3 to 5. **The
cause is the cutover itself**, which archived `dev/ORCHESTRATION.md` into
`archive/dev/`: one 604-line document entering a six-file corpus moves the
document frequencies and the average length, so every `DEV_SCOPE` query
re-ranks. **The `SRC_SCOPE` ranks did not move**, because `archive/src/` did not
change, and that is the control that proves the cause. The ranker is unchanged.
**The live figures are pinned in `scripts/tests/test_pod_gates.py:100-124` and
`:141-143`**, so the next document to enter either corpus fails a test instead of
moving a rank quietly.

Five of the seven reach the top 3 and two reach rank 1. **The measured cause of
the full-corpus miss is dilution by the live task corpus.** For episode 7, 443
documents outrank the gold file and 418 of them are live task documents. For
episode 5 the figures are 294 and 280. The archive is not outranked by other
archive files, and it is not outranked by `src/`. It is outranked by the reports
of dispatches on the same subject.

**AN EARLIER FORM OF THIS TABLE WAS WRONG AND THE CORRECTION IS KEPT.** It read
the full-corpus column off a raw term-overlap count while the scoped column used
BM25, so the two columns did not share a ranker and the sentence "only the scope
changed" was false of the numbers under it. Both columns are BM25 now. The
conclusion did not change, and the honest comparison is the stronger one: 444 to
1 with one ranker beats 499 to 1 across two.

**The two corpora grow differently, so the result holds as the project grows.**
`agents/tasks` holds 1,456 documents today and it grows with every dispatch.
`archive/src` holds 97 files and `archive/dev` holds 7 since the cutover, and
both grow only when a route retires. `git log` gives 1,455 new task documents in
one week, and one archive change since 2026-08-13. The corpus DD18 tells a brief to survey is
nearly static, so the scoped result does not decay.

**The first implementation uses the standard library only.** It ranks whole
files, keeps no index file and keeps no cache. MEASURED 2026-08-18 over
`retrieve.ARCHIVE_SCOPE`: the archive scope is 101 files and 4.8 MB, so one
ranking is one pass.

**What the builder writes.** It writes the `k` paths as candidates, each on its
own line, with the word CANDIDATE. It never says that a file bears on the task.
DD18's return duty does not change: the return still says what it read, what it
took, and WHY NOT for what it declined.

**Why a seam and not the tool.** The seam costs one function. A semantic tool
costs a binary, a weight set, an index file that needs a lifecycle declaration,
and a second home for memory beside `table.toml`. `requirements-dev.txt` carries
one dependency today.

**Part 1b, THE MISS SIGNAL.** The program measures its own retrieval, from data
the flow already gives it. At brief build it records the `k` paths it injected.
At the return it reads `ARCHIVE USED` and extracts every path there. The miss set
is what the return used and the injection did not offer. One line per dispatch
goes to the tracked transition log:

```json
{"event":"retrieval","task":"<code>","offered":5,"used":3,"missed":["<path>"],"overlap":0.0}
```

`overlap` is the discriminative overlap between the query and each missed file.
It counts the shared tokens whose document frequency is below half the scope's
file count. It separates the two failure kinds mechanically. A HIGH overlap says
the file shares real words and only ranked low, so the cure is a narrower scope
or a better ranker. A ZERO overlap says the file and the query share no
discriminative token, and no lexical method reaches it.

MEASURED precedent, episode 1, which is the one semantic case in the record: the
query and the gold passage share two tokens, `step` at document frequency 1,072
of 1,706 and `lj` at 886 of 1,706. Both are noise at corpus scale.
`dev/JOURNAL.md:1026` says the same thing in words: "Step 6 and the leaf supply
share no word".

**THE TRIGGER TO ADOPT A SEMANTIC INDEX, stated now so that nobody argues it
later.** ADOPT when both conditions hold over two consecutive weeks: the miss
rate `missed / used` goes above 20 percent, AND most missed paths carry ZERO
discriminative overlap. DO NOT ADOPT when the misses carry a high overlap,
because that is a scope problem or a ranking problem, and the measurement above
recovers four episodes by scoping alone. The digest prints both numbers every
day. It reports and it never triggers.

**ONE STATED UNCERTAINTY.** This rests on an assumption nobody measured: that
vocabulary fragmentation grows more slowly than the dispatch count. A large
renaming, for example after the architecture ruling at `[LJ-2.5]`, makes the
zero-overlap class steeper and fires the trigger earlier than any estimate. The
signal catches that by itself, and that is why the trigger is a signal and never
a date.

**Part 2, VERIFICATION, stays mechanical, and it is physics.**
`check-survey-quotes.py`, lifted from `check-dd18-survey.py`, keeps BOTH gated
halves: `answered()` at `:302`, so the return must name every injected path, and
`audit_quotes()` at `:339`, so a quoted phrase of 12 characters or more must sit
at each cited `path:line`. Keep `WINDOW = 3` and the three verdicts: off by a few
lines, quoted from elsewhere, or text the file does not hold. A real example:
`agents/tasks/LJ-1-383/lj-1.383-report.md:249-251`. **`check-sources-read.py` is
UNBUILT until day 7.** Its regex at `:70` is the codex tool-call shape, and no
claude head has ever run through this launcher, so no transcript exists to write
the new regex against. Until then it reports UNBUILT and gates nothing.

**Part 3, JUDGEMENT, moves to the mathematician.** Whether an archive BEARS on a
task is a judgement, and no checker claimed otherwise (`check-dd18-survey.py:54`).
AD27 supplies the reviewer.

| Part | Enforced by | Fires |
|---|---|---|
| Retrieval | the program | at brief build, before dispatch |
| Both blocks present, paths resolve | pre-flight P15 | before dispatch |
| Every injected path answered; quotes sit at their lines | `check-survey-quotes.py` | acceptance conjunct 6 |
| A named source was opened | `check-sources-read.py` | UNBUILT until day 7 |
| The miss rate and the zero-overlap share | the program, Part 1b | at every return, reported in the digest |
| Relevance and what to take | the adversarial reviewer | as its own dispatch, 6.6 |

**Equivalent function, checked against AD23.** Retrieval is now unskippable and
244 briefs that never named `JOURNAL-archived.md` become 0 by construction.
**What is deliberately lost:** the brief-side template counter and the per-corpus
naming score, which counted prose compliance rather than reading.

## 8. The digest and the stop push

*In force since the POD cutover of 2026-08-18, commit `fc676cb`. `AGENTS.md` holds the shared Boundary, and `dev/ARCHIVE.md:214` records `dev/ORCHESTRATION.md` as archived.*

AD7 and AD20.

### 8.1 The four sections and their sources

**The program generates the digest. No model writes it and no model edits it.**
Every field names its source, and a field with no source is not in the digest.

| Section | Fields | Source |
|---|---|---|
| 一、今日结论 | finished, dispatched, parked, net `src/` lines | the transition log; `ledger.py --brief` |
| 二、任务台账 | one row per code: state, instance, head, elapsed | the last transition per code |
| 三、报告数 | the two AD7 numbers, plus the twelve below | section 8.2 |
| 四、阻塞与待裁决 | every PARKED code with its reason; every queue REQUEST with no brief; every owner ruling outstanding | the log's park lines; `dev/pod/queue.toml`; section 11's open gaps |

**Twelve more reported numbers, all defined elsewhere in this document:** the
shadowing count (4.4), the expiry fallout count (4.6), the skipped-return count
(4.5.4), the orphan master count and their lines (7.2), the telescope hypothesis
count (4.7), the vacuous-conjunct-4 count (5.4), the vacuous-conjunct-1 count
(4.3.2), the foreign-changed-path count (4.3.1), the corpus record count (4.5.2),
the GO against NO-GO close count, from the matched row's `outcome` (4.2), and
the retrieval miss rate with the zero-overlap share of the misses (7.4, Part
1b). All of them report and none of them triggers.

**No sentence in the digest ranks anything**, because ranking is a judgement AD1
forbids the program and AD3 gives to the mathematician. It prints the newest
`to: DONE` line's task code and its matched row id, with no adjective. **The
cadence.** The digest hangs off the maintainer batch, which runs every 12
hours or at 3 parked tasks, so the owner gets two per day and each one prints its
window. AD20 says daily, and this is the one departure from it.

### 8.2 The two numbers of AD7, defined exactly

**Number one, the table's no-match rate.**
`no_match_rate = (park lines with reason "no-match") / (all return lines)`, over
the window and cumulatively. **Rule (c) writes that exact string on the one site
that produces a no-match park**, so the numerator has a source. **The
other eight park reasons are counted separately**, because none of them is a gap
in the table: `preflight:P<n>` is a malformed brief, `no-change` is a dead worker,
`attempt_max:<row id>` is a row that cannot change its own facts, `r4` is a close
the acceptance refused, `admission` is a table conflict R3 caught, `launch` is a
launcher refusal, `row:<row id>` is a row that asked for the park, and
`stop_loop:<row id>` is the stop itself.

**Number two, days since `src/` last had a net gain.** The digest records the
standing figure once per day, so the number is a lookup and not a re-derivation,
and `gain_day` is the newest day whose standing exceeded the day before it.

**A definition trap.** `git log --numstat -- src/` counts every line of a
`.lagda.md` master, prose and both translations included, while `ledger.py` counts
non-blank lines inside ` ```agda ` fences only, so the two disagree on any commit
that edits prose. **The digest uses the ledger caliber**, which is the
orchestrator's pick and not an owner ruling, at gap m2. Today `ledger.py --brief`
prints `standing 33,078 lines over 97 masters`.

**Both numbers report and neither triggers. The rollback criterion is the owner's.**

### 8.3 The worked example

**Every figure below is a placeholder. The program fills each one from the source
named in section 8.1, and nothing here is a measurement.** **`[LJ-1.386]` is the
real task of section 6.4. The other two codes are placeholders in the form
`LJ-1.N<n>`, they name no task, and the form cannot be read as a task code.**

```
POD 日报  2026-08-18  (窗口: 前 12 小时)

一、今日结论
  完成 2 个任务, 派发 3 个, 停放 1 个。src/ 净增 186 行, 口径为 ledger.toml。
  最新完成: [LJ-1.386], 命中规则 task-lj-1-386-go。

二、任务台账
  代码          状态      实例   头                        用时
  LJ-1.386      完成      2      claude-opus-5 / max       0:41
  LJ-1.N01      运行中    1      claude-opus-5 / max       1:07
  LJ-1.N02      停放      1      claude-opus-5 / max       0:04

三、报告数
  规则表未命中率: 窗口内 1/6 = 16.7%; 累计 4/58 = 6.9%。
  检索缺失率: 窗口内 1/9 = 11.1%; 其中零判别重叠 0 条。触发线为
        两周内缺失率高于 20% 且缺失多数为零重叠。
  src/ 距上次净增: 0 天。上次净增为今日。
  其他: 遮蔽 2 次; 过期回落 0 条; 丢弃返回 0 次; 孤儿母本 0 个;
        望远镜假设 989 个; 第 4 合取空过 1 次; 第 1 合取空过 0 次;
        越界改动 0 个; 语料记录 431 条; 结论 GO 2 个, NO-GO 0 个。
  以上只作报告, 不触发任何动作。是否回滚由仓库所有者判断。

四、阻塞与待裁决
  [LJ-1.N02] 停放, 原因 preflight:P8。分支 no-go-stated 指向的
  agents/tasks/LJ-1-N02/ProbeN02.agda 的父目录不存在。数学家修复该简报。
  停放计数 1/3。到 3 个停放, 整个循环停止。
  待仓库所有者裁决: 维护者头位的模型与思考档位 (见第 11 节 M8)。
```

### 8.4 The stop push

**`notify_owner(why)` is the only caller and the loop has exactly two stops:**
rule (d), when the parked count reaches 3, and `apply()`, when a `stop_loop` row
matched. Both push immediately and neither waits for the digest.

**The channel already exists.** `/Users/alsg/.claude/hooks/bark-stop-notify.sh`
pushes to Bark under AES-256-GCM, with a fresh random 12-byte IV per push at
`:105-110`, a `python3` fallback at `:118-146`, and a silent abort rather than a
plaintext push at `:158-159`. **The CHANNEL is reusable and the SCRIPT is not:** the
body derives only from a Claude Code transcript (`:36-92`), falls back to
`任务已完成` at `:92`, and no environment variable sets it.

**The amendment is one line, and it REPLACES rather than inserts.** Line 86 is
`body=""`, so an inserted line ahead of it would be overwritten at once and
`BARK_BODY` discarded. **Replace `:86` with `body="${BARK_BODY:-}"`.** The chain
at `:87-92` still fills an empty body, so the Stop hook does not change, and the
140-character truncation at `:34` and `:95` still applies.

**Where the copy lives.** The hook sits outside the repository and `.gitignore`
ignores `.claude/`, so copy it to `scripts/ops/bark-push.sh`, apply the
replacement, and **remove the hard-coded defaults for `BARK_AES_KEY` and
`BARK_KEY_URL`**. Both are deployment secrets: the repository copy reads them
from the environment and refuses to run when either is unset.

```bash
BARK_TITLE="POD 已停止" BARK_GROUP="Bedrock POD" \
BARK_BODY="3 个任务停放, 循环停止。最新: LJ-1.392 preflight:P8" \
BARK_AES_KEY="$BARK_AES_KEY" BARK_KEY_URL="$BARK_KEY_URL" \
  scripts/ops/bark-push.sh </dev/null
```

## 9. Migration

*In force since the POD cutover of 2026-08-18, commit `fc676cb`. `AGENTS.md` holds the shared Boundary, and `dev/ARCHIVE.md:214` records `dev/ORCHESTRATION.md` as archived.*

AD6. **THE CUTOVER RAN ON 2026-08-18, at commit `fc676cb`, and section 9.1 is
now the RECORD of what it did.** Read it to see what moved and why. Read section
9.2 to roll it back. The anchor, verified 2026-08-17 and unmoved:
`git log -1 --format='%H %ci' pre-pod-2026-08-17` prints
`e54da6c310ead31c5fb98ad171ac478c6b90b628 2026-08-17 10:44:02 +0800`. The tag is
annotated. Do not move it.

### 9.1 The cutover checklist

Run in order. Stop at the first non-zero exit.

```bash
# 0. Stop the loop first. The POD commits a tracked table and a tracked log,
#    so a running loop makes step 1 fail by design.
.venv/bin/python scripts/pod/pod.py stop      # a no-op before the first run

# 1. Confirm the anchor and a clean tree.
git rev-parse pre-pod-2026-08-17^{commit}     # must print e54da6c31…
git status --porcelain                        # must be empty

# 2. Branch. Never cut over on main.
git switch -c pod-cutover

# 3. Freeze the three baselines the replacement must beat, into
#    dev/measurements/2026-08-17-pre-pod-<name>.txt, redirecting stderr too.
.venv/bin/python scripts/measure/ledger.py --brief    # <name> = ledger
.venv/bin/python scripts/gate/check-dd18-survey.py    # <name> = survey
.venv/bin/python scripts/gate/check-archive-cited.py  # <name> = archive

# 4. Bring the launcher into version control (AD18).
mkdir -p scripts/pod
cp .claude/skills/codex-dispatch/dispatch.py scripts/pod/dispatch.py
shasum -a 256 scripts/pod/dispatch.py > dev/measurements/2026-08-17-dispatch-py.sha256
git add scripts/pod/dispatch.py
rm .claude/skills/codex-dispatch/dispatch.py .claude/skills/codex-dispatch/pi_stream.py
#    The launcher now has ONE home. `cp` and not `mv` would leave a second,
#    untracked copy that receives none of the six edits, that .gitignore:19
#    hides from every gate, and that both dispatch skills still point at.
#    Then repoint STATE at dispatch.py:67 and LOGS at :70 to .pod-state/.
#    Add one .gitignore line for .pod-state/. Never point them at _build/.
#    Then apply the SIX edits of 6.2: edit 6 removes ten refusals and KEEPS seven.
#    Add "pod" to GROUPS at scripts/tests/test_scripts_layout.py:37, in the same
#    commit that creates scripts/pod/. That suite pins the directory set with
#    assertEqual, so mkdir alone turns it red.
#    Repoint scripts/measure/dispatch-usage.py:85 at the new store in the same
#    commit: REGISTRY = ROOT / ".pod-state" / "registry.json". Row 32 keeps that
#    tool and the digest reads it, so a stale path silently returns zero records.

# 4b. Decommission ONE void process document (AD4, AMENDED BY A8). NEVER delete:
#     clause W4. **AGENTS.md IS NOT ARCHIVED.** A8 rewrites it in place to a
#     minimum project summary, the current milestone, the shared Boundary and a
#     pointer to dev/pod/instructions/<slot>.md, and the program GENERATES each
#     slot file from it. CLAUDE.md KEEPS its @AGENTS.md import.
git mv dev/ORCHESTRATION.md archive/dev/ORCHESTRATION.md
#     Then rewrite CLAUDE.md to a title plus one sentence, naming section 3 of
#     this memo as the rule set and dev/pod/instructions/<slot>.md as the
#     per-slot standing instruction, with NO @-import. Without this rewrite
#     every herdr-claude worker loads 179 lines of void process rules AHEAD of
#     its own instruction file.
#     Then repoint the in-scope citations at their new homes: dev/PLAN.md,
#     dev/LESSONS.md, dev/ledger.toml, dev/rules.toml, scripts/README.md,
#     agents/README.md, CONTRIBUTING.md, README.md, docs/zh/README.md and
#     docs/ja/README.md. Register both moves in dev/ARCHIVE.md at step 12.

# 4c. Retire the three superseded skills. They are untracked, so archive their
#     measured facts into dev/LESSONS.md FIRST and let the orchestrator assign
#     the IDs: the herdr two-phase wait (dispatch-herdr/SKILL.md:504-512),
#     `herdr agent prompt` queues and does not interrupt (:400-421), and a
#     supervised agent that drives its own supervisor is misread by it (:323-341).
rm -r .claude/skills/dispatch-herdr .claude/skills/update-agents-md
rm -r .claude/skills/codex-dispatch/SKILL.md .claude/skills/codex-dispatch/references
#     KEEP .claude/skills/codex-dispatch/.state/, which section 9.2 salvages.

# 5. Archive 16 files, 15 here and one at step 8, and NEVER delete one: clause
#    W4 governs this step. The 10 RETIRE rows of section 7.1, the 4 REWRITE rows
#    whose file archives (9, 11, 13, 24, of which row 9's move is step 8),
#    dispatch_policy.py, whose rewrite into heads.toml moves the file out, and
#    dev/vendors.toml under row 21b, whose one reader leaves with it.
#    archive/ mirrors the root. 10 from scripts/gate/: check-agents-guard,
#    check-dd4-stated, check-dd25-review-named, check-task-index, check-dev-docs,
#    check-build-manifest, check-baseline-home, check-live-record-claims,
#    check-live-territory, check-premises-stated. 4 from scripts/dispatch/:
#    check-dispatch-policy, dispatch_policy, dd25-record, recall-hook.
mkdir -p archive/scripts/gate archive/scripts/dispatch archive/scripts/tests archive/dev
git mv scripts/gate/check-agents-guard.py archive/scripts/gate/   # and the other 13
git mv dev/vendors.toml archive/dev/vendors.toml
#    DO NOT move check-probes.py until gap M5 is ruled.
#    check-premises-stated.py ARCHIVES with the rest, and its suite with it. Its
#    function is reimplemented as pre-flight P17 in scripts/pod/preflight.py, and
#    keeping the old file live would put one rule in two implementations, which
#    clause W5 forbids. It has no Makefile target after step 10b and no hook
#    after step 11, so leaving it in the tree leaves an orphan.

# 5b. Archive dev/ORCHESTRATION.md if step 4b has not already done it, and
#     register it in dev/ARCHIVE.md with what it enforced, why it left and its
#     last-green commit. Every rule it held has a disposition in section 7.1 or
#     a clause in section 3.1.

# 6. Archive the five retired tests beside them: test_dd25_review_named.py,
#    test_dev_docs.py, test_task_index.py, test_dispatch_clock.py and
#    test_premises_stated.py.
git mv scripts/tests/test_dd25_review_named.py archive/scripts/tests/  # and 4 more

# 7. (DAY 3, not day 6, because conjunct 3 needs it.) Split the whole-tree file.
git mv scripts/gate/check-tree.py scripts/pod/check-closure.py
#    SAME COMMIT, because the `tree:` recipe and scripts/git-hooks/pre-commit:78
#    both name the old path. Repoint the `tree:` recipe to
#    `$(PY) scripts/pod/check-closure.py --check closure`, rename the `tree`
#    target to `closure` on its own target line and in the check: line,
#    and repoint pre-commit:78 to `scripts/pod/check-closure.py --check closure`.
#    Without this the gate and every src/ commit call a missing path for three
#    days, because the rest of step 10b is day 6.
#    Then drop check_retiring; move check_shared_cjk into lint-prose.py and
#    check_spdx into lint-agda.py. KEEP check_closure_new. Delete --gate-debt,
#    --gate-passed and LAST_GATE, and delete dev/build-manifest.toml:122 in the
#    same commit (section 7.2).

# 7b. (DAY 3. NO LONGER A PREREQUISITE.) Narrow check-rule-ids.py to
#     dev/LESSONS.md and dev/rules.toml, per row 15. Drop dev/PLAN.md section 3
#     from known_decisions() and drop the bare-D<n> series rule. Then widen the
#     stray filter at scripts/tests/test_rule_series.py:247.
#     THIS STEP WAS WRITTEN AS A BLOCKER and is not one any more. It said the
#     un-narrowed checker exits 1 on this document, which was true while section
#     2 used bare D<n> codes. Those codes carry the AD prefix since 2026-08-17,
#     so the collision is gone. RE-MEASURED 2026-08-17: check-rule-ids.py exits 0
#     on the committed document and CI is green.
#     ACCEPTANCE: check-rule-ids.py exits 0 and test_rule_series.py exits 0.

# 8. Rewrite the surveys. Keep answered() (:302) AND audit_quotes() (:339);
#    delete the brief-side half; the archive-cited function moves into the
#    program's brief builder, section 7.4.
git mv scripts/gate/check-dd18-survey.py scripts/pod/check-survey-quotes.py
git mv scripts/gate/check-archive-cited.py archive/scripts/gate/   # W4: never delete

# 9. Write the new files.
#    scripts/pod/pod.py (with apply()), facts.py, witness.py (A4's meter),
#    preflight.py, table.py, replay.py, accept.py, digest.py
#    scripts/pod/check-spec-surface.py, then --write dev/pod/spec-surface.toml
#    scripts/ops/bark-push.sh, with both secrets removed from the defaults

# 9b. REWRITE scripts/README.md for the moved tree. Add one `| `scripts/pod/` |`
#     row to the layout table at :16-25 naming all ten new files, delete the
#     per-script sections for the 15 archived scripts, and rewrite the 8 REWRITE
#     entries under their new paths. test_scripts_layout.py:60-77 compares the
#     README table with the tree file by file, so the suite is the acceptance.
#     ACCEPTANCE: .venv/bin/python scripts/tests/test_scripts_layout.py exits 0.

# 10. Rewrite the check: line. The surviving check line:
#     check: venv-check typecheck markers lint lint-agda glossary ledger probes \
#            closure fences reuse ruleids specsurface surveyquotes
# 10b. WRITE THE THREE NEW RECIPES, DELETE THE FOURTEEN DEAD ONES, AND FIX THE
#      test: RECIPE.
#     New: closure -> scripts/pod/check-closure.py --check closure
#          specsurface -> scripts/pod/check-spec-surface.py --check
#          surveyquotes -> scripts/pod/check-survey-quotes.py
#     Delete: liveterritory tree devdocs taskindex agentsguard dispatchpolicy
#             dd4 dd25 premises buildmanifest archivecited dd18survey
#             baselinehome liverecord
#     Drop all fourteen from the .PHONY line. RE-MEASURED 2026-08-17: .PHONY
#     declares 38 targets and all fourteen are among them, and so are fences
#     and ratio. This replaces an earlier MEASURED claim of ten in and four
#     out, which the tree had already outgrown. ADD closure, specsurface and
#     surveyquotes to .PHONY in the same edit.
#     EDIT the ruleids recipe: keep the check-rule-ids.py line
#     and DELETE that recipe's `$(PY) scripts/dispatch/rules.py --check` line.
#     Row 22 keeps rules.py out of the gate and inside the brief builder.
#     EDIT the ratio recipe from `--check` to the report-only
#     mode, because row 29 voids the bar and keeps only the profiler. If
#     check-ratio.py has no report-only flag, add one and leave --check unwired.
#     DELETE these five lines from the test: recipe, whose files
#     steps 5 and 6 archive: :268 test_dev_docs.py, :270 test_task_index.py,
#     :278 test_dd25_review_named.py, :284 test_premises_stated.py and
#     :285 test_dispatch_clock.py.
#     ADD `make test` to .github/workflows/typecheck.yml beside `make check` at
#     :39. Nothing runs the 18 suites today, in CI or in a hook.
#     ACCEPTANCE FOR THIS STEP: `make -n check` and `make -n test` both exit 0
#     and name no missing file.

# 11. Rewrite the hooks. commit-msg -> check-spec-surface.py --msg-file "$1",
#     which is also R16's gate. pre-commit -> lint-prose, weave-i18n, lint-agda,
#     check-glossary, check-probes, check-fences, check-survey-quotes, which are
#     the conjunct-6 LINT class of section 5.4, PLUS check-closure (conjunct 3,
#     cheap enough for the hook) and check-rule-ids (row 15). The last two are
#     NOT LINT class, so conjunct 6 does not run them and the pinned member list
#     of conjunct 6 stays at seven.

# 12. Register every retirement in dev/ARCHIVE.md: one row per file, 16 of them
#     plus AGENTS.md and dev/ORCHESTRATION.md, with what it enforced, why it
#     left, its last-green commit, its size, and what it did right, from
#     measurement and never from praise.

# 12b. Write the SET ASIDE status blocks into dev/PLAN.md section 3 and section
#      11, and the historical marker into section 0. Neither section is deleted;
#      both are marked. Amendment A7 is the authority.

# 13. Seed the POD: dev/pod/table.toml (the system rows of 4.8, 6.6 and 7.3),
#     queue.toml (19 entries AS SEEDED, corrected from the 14 this step first
#     named: LJ-1.386 with a brief, plus one REQUEST entry per non-L9 PLANNED row
#     of dev/PLAN.md section 11, carrying code, reason and NO brief, so rule (a1)
#     skips them and the digest prints them until the mathematician writes each
#     brief. Section 11 carries 27 PLANNED rows and 9 of them are the L9 rows the
#     cutover itself closes, which leaves 18 REQUEST entries. THE SEED MISSED
#     LJ-2.5, clause W1's address, and section 3.1 records that gap),
#     heads.toml (five heads and the limits), instructions/ (one file
#     per slot, carrying the shared Boundary generated from AGENTS.md plus that
#     slot's own clauses out of W1 to W15, and the caliber sentence of 6.1),
#     spec-surface.toml with its [[guarded]] rule homes,
#     transitions/2026-08.jsonl (empty) and replay-corpus.jsonl (empty, seeded
#     on day 4).

# 14. Gate it. Background only. A cold typecheck is about twelve minutes.
make check                                    # must exit 0

# 14b. CLEAR THE STOP FLAG THAT STEP 0 SET. Step 0 runs `pod.py stop`, which writes
#      `.pod-state/STOPPED`, and rule (f) returns STOP on it, so `pod run` would do
#      one tick and exit 1 having dispatched nothing. `.pod-state/` is git-ignored,
#      so no gate and no `git status` can see the flag. THIS STEP WAS MISSING and the
#      final audit of 2026-08-18 found it.
rm -f .pod-state/STOPPED                      # or start with `pod resume`, never `run`

# 15. Pre-flight self-test before the first dispatch, on synthetic briefs.
.venv/bin/python scripts/pod/preflight.py --brief <a synthetic brief>
#     REFUSE: an empty branch set (P3), a block that does not parse (P2), a
#     seventh fact key (P4), a path whose parent is absent (P8), no escalate
#     branch (P18), an obligation with no "::" (P14), a done branch at delta 0
#     with no outcome = "no-go" (P19), and an escalate branch that outranks a
#     done branch it can match with (P20). ADMIT: a done branch carrying
#     outcome = "no-go" and no delta key.
# 15b. Admission self-test: two briefs both naming a branch `go` admit as
#     task-lj-1-386-go and task-lj-1-388-go; a re-admission writes nothing; a
#     branch that moves a frozen corpus record is REJECTED and the task parks.
# 15c. Loop self-test: a record matching sys-spec-surface parks its task with
#     stop_loop:sys-spec-surface, writes the STOPPED line and pushes ONCE; and a
#     maintainer return touching a second tracked file is REFUSED by R15.
```

### 9.2 The rollback checklist

The salvage set is **everything under `agents/`, plus `src/`, plus `dev/pod/`,
plus the untracked dispatch state**.

```bash
.venv/bin/python scripts/pod/pod.py stop
git status --porcelain                        # must be empty
git rev-parse HEAD > dev/measurements/pod-head-at-rollback.txt
git branch pod-final                          # a branch keeps the history reachable

mkdir -p ../bedrock-salvage
cp -a agents src dev/pod ../bedrock-salvage/
cp -a .claude/skills/codex-dispatch/.state ../bedrock-salvage/dispatch-state
cp -a .pod-state ../bedrock-salvage/pod-state

diff -r agents ../bedrock-salvage/agents && echo AGENTS-OK
diff -r src    ../bedrock-salvage/src    && echo SRC-OK

git switch -c pre-pod-restore pre-pod-2026-08-17
git clean -fdx -e .venv -e _build -e .claude  # removes POD-era untracked files

cp -a ../bedrock-salvage/agents/. agents/
cp -a ../bedrock-salvage/src/.    src/
cp -a ../bedrock-salvage/pod      dev/

.venv/bin/python scripts/gate/check-tree.py --check closure   # must exit 0
make check                                    # background only
```

**`-e .claude` is not optional.** `git check-ignore -v
.claude/skills/codex-dispatch/dispatch.py` returns `.gitignore:19:.claude/`, so a
bare `git clean -fdx` deletes the 469-record registry, `returns.log`, the log
corpus section 4.3 derives its class map from, AND the launcher's source.

**Why the closure step exists.** The salvage brings back POD-era masters under
`src/`, and `src/Everything.lagda.md` comes from the tag and does not import them.
That is the false green of section 7.2, and it is the ONE defect a rollback
creates by construction. **The table survives untouched**, because `dev/pod/` is a
new path that no pre-POD gate globs.

### 9.3 Telling a new artifact from an old one

**The primary marker is one file per task, written by the program**:
`agents/tasks/<CODE>/.pod`, one line at task creation, reading
`pod=1 table=<sha256 of table.toml> heads=<sha256 of heads.toml> at=<ISO time>`.
It survives a copy, and AD6 salvages `agents/` by copying, so a git-only marker is
lost at exactly the moment the reader needs it. **The backstop, for anything with
no stamp:** `git log --oneline pre-pod-2026-08-17..HEAD -- agents/tasks/<CODE>/`.
Empty means the directory predates the cutover.

**Do NOT use a new code prefix.** `LJ-1.<n>` and `LJ-2.<n>` are cited in 469
registry records, in `dev/JOURNAL.md`, in commit subjects and inside the reports,
and a prefix change breaks every one of those citations.

## 10. The build order

*In force since the POD cutover of 2026-08-18, commit `fc676cb`. `AGENTS.md` holds the shared Boundary, and `dev/ARCHIVE.md:214` records `dev/ORCHESTRATION.md` as archived.*

Seven days. **Each day delivers something useful on its own, even if the POD never
ships.** No day depends on a later one, checked against sections 5.4, 7.2 and 9.1.

| Day | What it builds | Useful alone because |
|---:|---|---|
| 1 | **Measure, and settle two prices.** Gap B3's recompile probe: a scratch worktree, one cold build, then one comment-character change in each of five masters, one per depth class, timing `agda src/Everything.lagda.md` after each. Gap m1's seed probe: 20 random LIVE probes at a 300 s deadline. And the COLD witness price, which section 4.7.5 measures warm and does not bound cold | The project gets a measured recompile rate per depth class. Every future cost estimate needs it |
| 2 | **The launcher.** The SIX edits of section 6.2, whose edit 6 removes all ten released refusals, `dd4_defects()` included; keeping any one of them refuses every POD brief. `dev/pod/heads.toml`, its loader and the instruction files. Move `dispatch.py` to `scripts/pod/` and repoint `STATE` and `LOGS`. **First act: resolve the three model IDs against one throwaway pane, and settle gap B4** | The repository can dispatch a Claude head at a chosen effort level for the first time, under the current orchestrator |
| 3 | **The recorder and the acceptance runner.** `scripts/pod/facts.py` with the regex and the class map of 4.3.1, `run_agda()` with its `--include-path` term, and A4's witness meter with its four derivation steps and its four-value pass rule. Cutover step 7, the `check-tree.py` rename, which conjunct 3 needs, WITH its two caller edits in the same commit: the `check:` line and the `tree:` target, and `scripts/git-hooks/pre-commit:78`. Cutover step 7b, the `check-rule-ids.py` narrowing, before this document is committed. `run_acceptance()` of section 5.4, in conjunct order 5, 1, 2, 3, 4, 6, writing the `runs/accept-<n>.out` format. `at_head` on `import_graph` | Any agent gets a one-command acceptance test that a human can run and read |
| 4 | **The table, the router, the replay, the admission and the pre-flight.** `dev/pod/table.toml` with the system rows of 4.8, 6.6 and 7.3. `route()`, `matches()`, `replay()`, `admit_rows()` and `expire_rows()` of section 4.1, with the loader's refusals and its id namespacing. `scripts/pod/preflight.py`, P1 to P20. Seed the corpus from the 426 tracked live probes, plus one MEASURED record per runner class | A maintainer can test a proposed routing against real records in milliseconds, with no loop |
| 5 | **The loop, the runner, the state and the log.** `scripts/pod/pod.py` with `run`, `tick`, `resume`, `status` and `stop`. `pod_tick()` rules (a1) to (f) and `apply()`'s six actions, including rule (f)'s admission call and its `witness_unresolved()` dispatch point. `emit()` with its write order, its corpus append, monthly log rotation and the two `os.fsync` calls. Make `agda_pileup()` refuse instead of print. The `machine:` line and `admits()`. **Build `ledger.py --write`**, which is a no-op alias for `--check` today at `scripts/measure/ledger.py:806-809`: the DONE handler calls it, so without a real writer every close commits a stale declaration | The repository gets a crash-safe loop and a TRACKED execution record. The current registry is untracked and cannot give one |
| 6 | **The gates.** Cutover steps 5, 6, 8, 10, 10b, 11 and 12. `check-spec-surface.py`, its snapshot and R16's `[[guarded]]` rule homes. The survey split of section 7.4, INCLUDING `retrieve()` at Part 1a and the miss signal at Part 1b | The trophy spec surface and the rule homes get their first protection, the archive survey stops depending on an agent remembering it, and the retrieval starts measuring itself from day one |
| 7 | **The digest, the push, the maintainer, the first dispatch.** `scripts/pod/digest.py`. `scripts/ops/bark-push.sh` with both secrets removed. Section 6.7's maintainer batch. Dispatch `[LJ-1.386]` with the brief of 6.4, then capture its transcript and write `check-sources-read.py`'s new regex. The digest prints the retrieval miss rate and the zero-overlap share, section 7.4 Part 1b | The owner gets a Chinese digest of the route's state, whichever loop produces the work |

## 11. Open gaps and risks

*In force since the POD cutover of 2026-08-18, commit `fc676cb`. `AGENTS.md` holds the shared Boundary, and `dev/ARCHIVE.md:214` records `dev/ORCHESTRATION.md` as archived.*

A BLOCKING gap stops the build, a MAJOR gap changes what the design promises, and
a minor gap is a known cost.

### 11.1 Blocking

**B1 and B2 are CLOSED on 2026-08-17.** B1 by A1, A4 and A6: section 4.7 carries
the definition, the grammar, the derivation, the four-value pass rule and the
measured price, and the meter was PROVEN on real files, 24 green witnesses of 24
with the negative returning exit 42 and `[NotInScope]` inside the witness. B2 by
A2 and the launch probe: section 6.2 names six edits and the probe verified every
flag and every line they touch. What remains of both is a price and an ID.

**B3. CLOSED 2026-08-17 by the day 1 probe, and the owner ruled the measured
value stands without a re-measure.** **Plan on 180 s per acceptance test, band
16 s to 305 s, at 0.01069 s per in-fence line.** That is 1.22 times
`ac_baseline_seconds_per_line`, the floor it lands nearest, and the 34-fold band
closes to 1.48-fold. The probe and its record are
`agents/tasks/L9-0/l9.0-b3-probe-report.md`. **The probe states its own
limitation and the owner accepted it:** the machine carried a load average of
3.88 to 7.16, so the repository's quiet-machine rule was not met. The band
collapsed 23-fold, which noise does not explain, so the direction stands; read
180 s as a planning figure and never as a precise one. **One reading is worth an
eye:** the cold build held 7.23 GB resident against the 8 GB cap.

The paragraph below is the gap as first written.

**B3, AS FIRST WRITTEN. The acceptance test cost is unmeasured across a 34-fold band.** The floor
is measured at 2.84 to 3.18 s warm. The recompile term is the whole price, and
three recorded rates bracket it: the field `ac_baseline_seconds_per_line`
(`dev/ledger.toml:2663`), which is the floor and whose VALUE this document does
not restate, 0.0257 (`L.Ordinal.SquareLaw` at the LIVE 23.3 s
of `dev/ledger.toml:1920` over 907 in-fence lines) and 0.297
(`dev/ledger.toml:1963` `content_rate_measured`). **Reproduced today with
`scripts/measure/ledger.py`:** the reverse closure of `src/L/Coding/Model.lagda.md`
is 43 files and 23,752 in-fence lines, priced at 209 s or 7,054 s. **No
throughput plan can rest on a 34-fold band. What settles it:** the day 1 probe.

**B4. CLOSED 2026-08-17 by the day 2 probe. All six entries of `legal.models`
RESOLVE**, verified by read-back on a throwaway pane rather than from a `--help`
listing: `claude-opus-5`, `claude-fable-5` and `claude-sonnet-5`, and the three
aliases `opus`, `fable` and `sonnet`. Section 6.1 needs no value change. The
record is `agents/tasks/L9-0/l9.0-b4-model-ids.md`. **It also measured the case
the read-back refusal exists for:** `claude-opus-5-20260101` passes the client
and fails at the API, so a date suffix dies after the launch looks clean.

The paragraph below is the gap as first written.

**B4, AS FIRST WRITTEN. The three model IDs are not verified.** `grep -n "claude-" dev/vendors.toml`
returns nothing, and that file's own rule at `:185-186` refuses an invented model
ID. `claude --help` documents the shape and three aliases, and it does NOT confirm
that `claude-opus-5`, `claude-fable-5` and `claude-sonnet-5` resolve. Section 6.1
carries both forms in `legal.models` and adds a read-back refusal. **What would
settle it:** day 2's first act, one
throwaway pane per ID.

### 11.2 Major

| # | Gap | What would settle it |
|---|---|---|
| M1 | `universe_level` is not reliably separable from `other`. Measured: 1,375 `UnequalTerms` blocks sampled, 181 of them (13.2 percent) name a sort or a level in the first 400 characters, while the exact names carry 67 occurrences against `UnequalTerms` at 1,513. A row keyed on `universe_level` sees roughly one in four real universe failures | Nothing in this repository. It is an upstream limit and the design absorbs it. Do NOT add a message-text heuristic: it would make the class depend on Agda's prose |
| M2 | `timeout` has no source and no fallback binary. `which timeout gtimeout` returns nothing on this machine, and Agda emits no timeout error and no timeout exit code | ABSORBED. The POD owns the deadline: `timeout=` on `subprocess.run`, catch `TimeoutExpired`, `start_new_session=True`, kill the group. Section 4.3.1 does all four. The need is measured: the largest single Agda block in the log corpus ran 1,604,413 ms |
| M3 | The historical replay corpus cannot be reconstructed for facts 1, 2, 5 and 6. Measured at 48 of 6,508 invocations, 0.7 percent | ABSORBED. Section 4.5.3 builds forward and seeds from the 426 tracked LIVE probes. AD10 tests regression against a FIXED corpus, not against history |
| M4 | **CLOSED by A7.** DD4 is a WRITTEN RULE, clause W2, injected into `dev/pod/instructions/mathematician.md` and `coder.md`, with `agent discipline` as its enforcer. `dd4_defects()` is removed on day 2 whatever else is ruled, because it refuses every POD brief | Settled. The residual cost, the lost per-dispatch repetition measured at 102 of 112 briefs over five days, is stated in section 3.1 and not hidden |
| M5 | AD23 retires `check-probes.py`, which is physics. Its docstring at `:17` records the cost: one `git add -A src/` committed 13 probe files and 3,274 lines. An ignore rule is not a gate, because `git add -f` walks past it (`:26`) | Read the LINT class as covering code hygiene, and keep `check-probes.py --staged` in the pre-commit hook. Cutover step 5 holds the file until this is ruled |
| M6 | A signature-only spec surface gate cannot see a definition body. `src/L/Constructible.lagda.md:410-411` reads `𝒮ʟ : ZFStructure (hPropAlgebra (ℓ-suc ℓ))` then `𝒮ʟ = 𝒮ᵥ ↾ isL`. Weaken `isL` and `L⊨ZFC` asserts a different theorem while every hash holds | The gate computes a second hash per surface file over the WHOLE in-fence code, and a change to it PRINTS in the digest rather than blocking. Signature changes still block. Cost: one sha256 per file |
| M7 | AD14 does not say what happens to a worker that is already running. Section 5.5 rules that the stop stops DISPATCHING only. The alternative would recreate `dispatch.py`'s founding incident (`dispatch.py:7-9`) | The owner agrees to the stated consequence: **the PARKED count can pass 3 after the stop.** This is a ruling made in this document |
| M8 | The maintainer head has no owner ruling. AD24 and AD25 name four heads; AD2 needs a fifth. Section 6.1 picks `claude-opus-5` at `high` | An owner ruling on the maintainer's model and effort |
| M9 | `check-sources-read.py` cannot be retargeted before a Claude transcript exists. Its regex at `:70` is the codex tool-call shape, and no Claude head has ever run through this launcher | Day 7 captures one transcript, pastes the tool-call line into section 7.4, and writes the regex. Until then the check reports UNBUILT and gates nothing |
| M10 | **A NO-GO close reaches DONE with `agda` exit 42**, which AD13's literal text forbids. A6 makes a NO-GO expressible and R4's `outcome` split is what stops the two rules contradicting each other. That split is the ORCHESTRATOR's ruling, not the owner's | An owner ruling: a stated NO-GO with a written report discharges the obligation to ANSWER, so it closes under conjuncts 5 and 6 only. If the owner refuses, a NO-GO needs a seventh task state and section 5.2 grows one |
| M11 | **CLOSED by the owner's ruling of 2026-08-17: PUT BOTH BACK.** DD0 is now SUPERSEDED IN PART. Part 3 is clause W9, a written rule with `agent discipline` as its enforcer, because the act it forbids is an inference. Authorship of the rule homes is mechanised in two halves, R15 and R16 | Settled. The residual cost is stated in section 6.7: R15 gives the maintainer the PROPOSAL file rather than `dev/pod/table.toml`, which is narrower than the ruled text and never wider |
| M12 | **DD17 = SUPERSEDED drops "an idle agent slot is a defect".** `admits()` caps concurrency and nothing requires the queue to be non-empty, so an empty `dev/pod/queue.toml` idles the whole loop and no digest field counts it | An owner ruling: either an eleventh reported number, the count of idle slots per tick, or a written clause in section 3.1. Both cost about one line |
| M13 | **DD24 = SUPERSEDED leaves no automatic quality bar.** No seeded row of sections 4.8, 6.6 or 7.3 carries a `seconds_max`, so slow code closes green. The measured failure the retired anti-drift clause covered is on record: a recalibration moved the bar and stood for three days | An owner ruling: seed one system row with an absolute `seconds_max`, and decide whether a change to that number needs a trailer the way the spec surface does |
| M14 | **DD25 = MECHANISED misses one ruled trigger.** Rule (f) reviews on `attempt > 1`. A first-instance NO-GO closes through a `done` row with `outcome = "no-go"` and never reaches attempt 2, so it gets no adversarial review, and DD25's trigger list names a stop taken as the deliverable | An owner ruling: seed a system row with `action = "escalate"`, `head_slot = "mathematician_adversarial"`, keyed on the record a NO-GO makes. That restores the trigger inside the six-fact vocabulary |
| M15 | **R9 and AD22 guard the LANDED trophy only.** The surface is derived from `src/Landmarks.lagda.md`'s `open import` lines, that file does not import `L.GCH`, and MEASURED 2026-08-17 the string `GCH` occurs zero times in it. So `GCHStatement` at `src/L/GCH.lagda.md:59-60` is unguarded for the whole build, and it is the half the route still has to prove | No new mechanism. When the GCH trophy lands, its statement joins `src/Landmarks.lagda.md` as an `open import` and the same derivation grows the surface to 9 files. Until then the gap is a stated limit and not a defect |

### 11.3 Minor

| # | Gap | What would settle it |
|---|---|---|
| m1 | The probe-rerun seed price is a projection from a comparable and not a measurement of the 438 live files. `dev/LESSONS.md` P-l forbids that transfer | The day 1 seed probe: 20 random LIVE probes, 300 s deadline, one process |
| m2 | AD7's second number has two calibers. Section 8.2 picks the ledger, but that is the orchestrator's pick | An owner ruling on the caliber |
| m4 | AD22 stops at the repository boundary. `bedrock.agda-lib` reads `depend: cubical` with no version, and `src/Base/Prelude.lagda.md` is pure re-export | Record the cubical version in `dev/pod/heads.toml`, which the loader of section 6.1 already reads. `dev/vendors.toml` archives at cutover step 5 under row 21b and the POD never reads it |
| m6 | `save()` at `dispatch.py:316-321` has no `os.fsync`. The rename is atomic against a process crash and not durable against a machine crash | Day 5 adds both calls. Cost: about 355 per median day |
| m7 | `import_graph()` at `ledger.py:392` scans whole file text for `import` lines, while `code_of()` at `check-tree.py:115` scopes to the fences. An `import` in prose would create a false edge | Measured today: the two readings agree on all 97 countable masters. The cure is one line, scoping `import_graph` through the fence extractor |
| m8 | The error-name map covers the 49 distinct names measured in the log corpus. The full Agda 2.8.0 tag set is not enumerated | An unknown name buckets as `other`, which parks the task and calls the maintainer. The no-match rate runs high until the map fills from real returns |
| m9 | `.pod-state/logs/` has no measured daily size. The comparable corpus reached 931 MB over 1,017 files | Section 4.0 sets a 30-day retention. Day 5 measures the real rate and re-prices it |

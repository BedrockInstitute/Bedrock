# LJ-1.278: LAND A1, A3 and A4 as `src/L/Cardinal.lagda.md`

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **I ran `scripts/dispatch_policy.py` before writing this
line**: `deepseek-subagent-mode` is IN FORCE, clock-selected, OFF-PEAK, Beijing
window 12:00 to 14:00.

## GOAL

**Land Route A-prime's blocks A1, A3 and A4 as ONE new master,
`src/L/Cardinal.lagda.md`.**

**`[LJ-1.268]` put all three in that file** (`lj-1.268-report.md:25`, `:29-30`).
A1 creates it in wave 0; A3 and A4 extend it in wave 1, after A2.

**A2 LANDED TODAY**, `src/L/Coding/Injection.lagda.md`, 238 lines, green, and a
re-run that imports it exits 0. **So wave 1 is open and all three can go in one
master in one pass.**

**AND A4 IS THE SECOND OF THREE.** `[LJ-1.274]` measured that
`dev/ledger.toml`'s `gch_root` needs A2, A4 and A7 and nothing else, because
`scripts/ledger.py:404-446` reads a PATH and an import closure and never a
proof term. **A2 is in. A4 is this task. Then only A7 stands between the
project and DD4's first real measurement.**

## PREMISES

- **A2 is delivered and importable**, at `src/L/Coding/Injection.lagda.md:1`
  and wired at `src/Everything.lagda.md:336`. **A3 and A4 both name A2's
  predicate**, per `agents/tasks/LJ-1-268/lj-1.268-report.md:28-30`.
- **A3 and A4 have no undelivered import beyond A2**, per
  `agents/tasks/LJ-1-268/lj-1.268-report.md:28-30`. **VERIFY THIS FIRST.** If
  it is false, the landing is smaller than the brief assumes.
- **A4's probe is a MINIMAL CORE and not the master**, stated by its own
  report at `agents/tasks/LJ-1-236/lj-1.236-report.md:154`: the master adds the
  full object-language content. **So A4's 43 lines are its OWN lines against a
  190-line probe core** (`agents/tasks/LJ-1-236/lj-1.236-report.md:283`).
  **This premise is the one most likely to be wrong, and it decides the size.**
- **The three blocks belong in one file**, per
  `agents/tasks/LJ-1-268/lj-1.268-report.md:25`. **If reading them together
  shows they do not, say so: a landing order is a plan and not a ruling.**
- **The prices are 54, 26 and 43 lines**, from
  `agents/tasks/LJ-1-253/lj-1.253-report.md:12-21`. **They are in the NARROW
  caliber**: `[LJ-1.277]` measured A2 delivering 238 against a priced 186, a
  ratio of 1.28, because `agents/tasks/LJ-1-229/lj-1.229-report.md:17` counts
  definitions only while DD5 counts non-blank lines inside fences. **So expect
  more than 123 and say what you get.**

## THE SOURCES

| block | probe | priced |
|---|---|---:|
| A1 | `agents/tasks/LJ-1-232/ProbeLJ1232A1.agda` | 54 |
| A3 | `agents/tasks/LJ-1-232/ProbeLJ1232A3.agda` | 26 |
| A4 | `agents/tasks/LJ-1-236/ProbeLJ1236A4.agda` | 43 |

**Read all three whole before you write anything.** **Take their content, not
their names.**

## WHAT YOU DECIDE, and say why in the report

**1. THE ORDER INSIDE THE FILE, and what each block exports.** **P-k: a read
lemma is stated where its consumers use it.** **A5 row 1, A6 and A7 are the
downstream consumers; name what each needs.**

**2. WHAT `src/Everything.lagda.md` NEEDS.** **NEVER touch that file. I wire
it.** **Name the exact line and its position, and derive the position from the
master's own imports and its consumers, as `[LJ-1.277]` did.**

## THE MEASUREMENT YOU OWE

**The delivered master's cold elapsed time, its line count by
`.venv/bin/python scripts/ledger.py`, and its rate against the 0.010514 bar.**
**A2 landed at 0.0070 s/line, 0.66x the bar, in the P-m parameterized class.**
**Say whether this master is in the same class and why.**

**And name every existing master you did NOT edit.** **`[LJ-1.268]`'s whole
order rests on no existing master gaining a line.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **ALL THREE LAND GREEN.** Report the exports, the `Everything` line, the
  timing, the rate, and the delivered size against the 123. STOP.
- **A4 IS MUCH LARGER THAN 43.** **That is the premise above and it is the one
  to test.** **Land what is real, report the figure, and do not pad or trim to
  meet a number.**
- **AN IMPORT IS NOT DELIVERED.** **Name it at `file:line`** (C-44). **That
  refutes `[LJ-1.268]`'s order and is worth more than the landing.**
- **THE THREE DO NOT BELONG TOGETHER.** **Land A1 alone, say why, and stop.**
  **A file that holds three things for no reason is worse than three files.**
- **A WALL.** **A single `agda` invocation past 30 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **Report a heap exhaustion as
  a wall. NEVER raise the cap.**

## WHAT YOU MUST NOT DO

- **NEVER touch `src/Everything.lagda.md`.** I wire it after auditing.
- **Do not edit ANY existing master**, including today's
  `src/L/Coding/Injection.lagda.md` and `src/L/Coding/EnvSupply.lagda.md`.
  **If you believe one must change, STOP and say why.**
- **Do not land A5, A6 or A7.** **A7 especially: it is the trophy statement and
  it gets its own task.**
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **Do not touch `agents/tasks/LJ-1-279/`.** **A SIBLING IS LIVE THERE**,
  landing A5 rows 5 and 1 into `src/L/InjChain.lagda.md`. **Your write
  territory is `src/L/Cardinal.lagda.md` and `agents/tasks/LJ-1-278/`, and
  nothing else under `src/`.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the load beside every absolute figure.**
- **Create your report file in your FIRST five minutes (C-22).**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE RULES THIS CHAIN EARNED

**`exit 0` IS NOT A SUPPLY** (C-45). **`[LJ-1.263]` and `[LJ-1.277]` both
proved a landing by re-running something that IMPORTS the new master.** **Do
the same. A copy that compiles is not a landing.**

**C-40. A new master has consumers the moment it exists.**

**C-49, written yesterday from this campaign.** **A heap wall and a rate can be
properties of the LAYOUT rather than the content. You are landing in a NEW
master and that is why.**

**C-44. A brief's claim is unchecked until you check it.** **Every figure in
this brief is another report's except A2's landing, which I audited.**

**THE CALIBER IS DD5'S AND NOTHING ELSE.** **`scripts/ledger.py` is the only
admissible source for a size figure.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.227]` measured A1, A3 and A4 all PER-TOWER on the Def-against-J
axis.** **So this master is the per-tower half of A-prime and that is exactly
where DD4's cost sits.** **Write it as generically as the mathematics allows,
and say plainly what a J instantiation would have to rewrite.**

**NAME YOUR AXIS** (C-46). **`[LJ-1.272]` measured that DD4's OWN axis is
AC-against-GCH, fixed in code at `scripts/ledger.py:50`.** **On THAT axis, say
whether this master lands inside the shared intersection or on the GCH side
alone.** **`[LJ-1.274]` computed that `src/L/Model.lagda.md:49-57`, the AC
root's import list, does not reach the new A-prime masters. Check it.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-232/ProbeLJ1232A1.agda` and `ProbeLJ1232A3.agda`, and
  `agents/tasks/LJ-1-236/ProbeLJ1236A4.agda`, all read WHOLE.**
- **`agents/tasks/LJ-1-236/lj-1.236-report.md:154` and `:283`**: A4's minimal
  core, which is the premise to test.
- **`agents/tasks/LJ-1-268/lj-1.268-report.md:23-48`**: the landing order.
- **`agents/tasks/LJ-1-277/lj-1.277-report.md`**: **how A2 was landed and
  PROVED today, including the re-run and the caliber finding.** **Copy the
  method.**
- `agents/tasks/LJ-1-253/lj-1.253-report.md:12-21`: the three prices.
- **`archive/dev/TASKS-archived.md` and
  `archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md`.** **The
  retired route had a cardinal module, 399 lines, and `[LJ-1.273]` measured its
  `cardFo` as the BIJECTION form against today's INJECTION form
  (`agents/tasks/LJ-1-236/lj-1.236-report.md:240-245`), so the code does not
  transfer.** **Take SHAPE only, and say what does not transfer.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md` splits II.5 into twelve rows.** **Say which
rows A1, A3 and A4 serve.** **`[LJ-1.273]` mapped row E to counting; check
that.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-232/ProbeLJ1232A1.agda` FIRST, whole.

## SCOPE (write)

`src/L/Cardinal.lagda.md`, new, and `agents/tasks/LJ-1-278/` for your report
and any working file. **No existing master. Never `src/Everything.lagda.md`.**
**Do not create any other file under `src/`.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for build` and read every statement.
**The tool prints `Full entry: dev/LESSONS.md:<line>` for every rule and says
THIS IS AN EXCERPT when it truncated. OPEN the full entry for any law you act
on.**

- **P-h.** Definability walks are module-parameterized, never
  function-parameterized.
- **P-k.** A read lemma is stated where its consumers use it. **The centre of
  your ordering decision.**
- **P-l.** A statement may be ABOUT a concrete stage without dragging that
  stage's presentation into its type.
- **P-m.** The check-cost rate is a content-class certificate.
- **P-n.** Satisfaction content at a concrete carrier is a payable floor.
- **R-35.** Union representations are meta-poisoned.
- **R-38.** A consumer's alias of a transparent imported operation is a birth
  site.
- **R-40.** A deep successor-chain membership witness normalizes
  super-linearly.
- **I-5.** Inner-world truncation branches carry written types.
- **C-12.** Agda runs under a hard heap cap.
- **D-10.** Price the truth of a recorded residue before pricing its proof.
- **C-22.** Write your deliverable incrementally.
- **C-32, C-36, C-40, C-44, C-45, C-46, C-49. D-1, D-26. DD0, DD8, DD23,
  DD24.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `.venv/bin/python scripts/lint-prose.py --check` and
  `.venv/bin/python scripts/lint-agda.py --check` on what you write.
- **`lint-agda.py` binds a MASTER and did not bind the probes.** **Expect to
  trim the using lists; A2's landing removed many.**
- **DD23 freezes mathematical prose.** **Write code and its own comments only.**
- **No em dash in any language.** Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the delivered line count, the cold elapsed seconds and the rate
against 0.010514.** Then each premise above marked VERIFIED or REFUTED at
`file:line`. Then what the master exports, per block, with its consumer. Then
the exact `src/Everything.lagda.md` line. Then the re-run that PROVES this is a
landing. Then every existing master you did not edit. Then the DD4 answer on
the AC-against-GCH axis. **Mark every negative MEASURED or INFERRED.**

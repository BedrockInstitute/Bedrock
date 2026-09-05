# LJ-1.280: LAND A7 as `src/L/GCH.lagda.md`, the last master `gch_root` needs

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **I ran `scripts/dispatch_policy.py` before writing this
line**: `deepseek-subagent-mode` is IN FORCE, clock-selected, OFF-PEAK.

## GOAL

**Land Route A-prime's block A7, the GCH statement, as
`src/L/GCH.lagda.md`.**

**THIS IS THE LAST OF THREE AND THE OTHER TWO ARE IN.** `[LJ-1.274]` measured
that `dev/ledger.toml`'s `gch_root` needs a committed `.lagda.md` under `src/`
that is not a catalog, and nothing else: `scripts/ledger.py:404-446` reads a
PATH and computes an import closure, and never reads a proof term or calls
Agda. **The three are A2, A4 and A7.** **A2 landed as
`src/L/Coding/Injection.lagda.md` and A4 landed inside
`src/L/Cardinal.lagda.md`, both green today.**

**So on the day this lands, DD4's own report runs for the first time in this
project's history.** **I declare `reuse.gch_root` after auditing your return;
you do not touch `dev/ledger.toml`.**

## WHAT A7 IS, and it is a STATEMENT rather than a proof

**`[LJ-1.273]` measured that A7 is only the statement.**
`agents/tasks/LJ-1-236/ProbeLJ1236A7.agda:147` defines `GCHStatement` as a
`Type (ℓ-suc ℓ)`, and its guard at `:165-171` builds ONE inhabited site and
supplies NEITHER `sq` NOR `absorbs`. **`exit 0` is not a supply** (C-45).

**Land it as what it is.** **Do not invent a proof, do not weaken the
statement to make something close, and do not leave a hole that reads as
proved.** **If a hypothesis is undischarged, its type says so.**

## PREMISES

- **A7 is a statement whose two hypotheses are unsupplied**, at
  `agents/tasks/LJ-1-236/ProbeLJ1236A7.agda:165-171`. **VERIFY, because the
  whole shape of the landing follows from it.**
- **A7's hypotheses are A5's and A6's conclusion types ON THE NOSE**, measured
  by `[LJ-1.236]` at `agents/tasks/LJ-1-236/lj-1.236-report.md:1`. **A5 rows 5
  and 1 landed today as `src/L/InjChain.lagda.md`.** **A6 has NOT landed.**
  **So check what A7 can now name from a delivered master and what still has
  to be a hypothesis.**
- **A7's home is `src/L/GCH.lagda.md`**, per
  `agents/tasks/LJ-1-268/lj-1.268-report.md:33-34`.
- **A7 is priced at 33 lines** from
  `agents/tasks/LJ-1-253/lj-1.253-report.md:12-21`, **in the NARROW caliber.**
  `[LJ-1.277]` measured A2 delivering at 1.28x its narrow price and
  `[LJ-1.279]` at more. **Report what lands; do not trim to 33.**
- **A7 is TOWER-NEUTRAL on the Def-against-J axis**, measured by `[LJ-1.227]`.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **IT LANDS GREEN.** Report the exports, the `Everything` line, the timing,
  the rate, and exactly which hypotheses remain. STOP.
- **A5's LANDING LETS A7 NAME SOMETHING IT COULD NOT.** **Say so and use it.**
  **That is the landing order paying off and it is worth recording.**
- **A7 CANNOT BE STATED WITHOUT A6.** **Name the term** (C-36) **and stop.**
  **A6 is wave 3 and blocked on a stale probe import, so this would re-order
  the plan and I need to hear it.**
- **A WALL.** **A single `agda` invocation past 30 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **NEVER raise the cap.**

## WHAT YOU MUST NOT DO

- **NEVER touch `src/Everything.lagda.md`** and **NEVER touch
  `dev/ledger.toml`.** I wire and declare both after auditing.
- **Do not edit ANY existing master**, including today's four.
- **Do not land A6 or A5 row 3.** **Both are wave 3.**
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **Do not touch `agents/tasks/LJ-1-281/`.** **A SIBLING IS LIVE THERE**,
  probing R-35 against `src/L/Cardinal.lagda.md`'s 98 seconds. **It writes only
  in its own task directory; your territory is `src/L/GCH.lagda.md` and
  `agents/tasks/LJ-1-280/`.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the load beside every absolute figure.**
- **Create your report file in your FIRST five minutes (C-22).**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE RULES THIS CHAIN EARNED

**`exit 0` IS NOT A SUPPLY** (C-45). **This block is the law's sharpest case:
a green file whose two hypotheses nobody supplies.** **Prove the landing by
re-running something that IMPORTS the master**, as `[LJ-1.277]` and
`[LJ-1.279]` both did.

**C-40. A new master has consumers the moment it exists.**

**C-49. A rate can be a property of the LAYOUT.** **`[LJ-1.278]` bisected its
master to answer this; do the same if your figure surprises you.**

**C-44. A brief's claim is unchecked until you check it.** **My A4 premise was
REFUTED by `[LJ-1.278]` two hours ago. Treat every line above the same way.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**THIS MASTER IS ABOUT TO BECOME DD4'S OWN MEASURING POINT.** `[LJ-1.272]`
measured that DD4's axis is AC-against-GCH, fixed in code at
`scripts/ledger.py:50`, and `[LJ-1.274]` computed what the report will print
the day this lands: **AC 73 masters and 17,197 lines, GCH 48 and 8,731, SHARED
43 and 7,596, 41.4 percent of 18,332.**

**Two things follow and I want both answered.** **First: your import list IS
the GCH closure.** **So say what you import and why each import is necessary,
because an unnecessary import inflates DD4's first figure.** **Second:
`[LJ-1.274]` measured that the figure UNDERSTATES, because a hypothesis carries
no import edge and A7 states `SqShape` and `AbsorbsShape` as hypotheses.**
**Say which hypotheses would become import edges once A6 lands.**

**NAME YOUR AXIS** (C-46).

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-236/ProbeLJ1236A7.agda`, read WHOLE. The content.**
- **`agents/tasks/LJ-1-236/lj-1.236-report.md`**: A7's statement auditing the
  rest, and the on-the-nose finding.
- **`agents/tasks/LJ-1-273/lj-1.273-report.md` and
  `agents/tasks/LJ-1-274/lj-1.274-report.md`**: **why this master matters
  beyond its 33 lines, and what the tool actually reads.**
- **`agents/tasks/LJ-1-279/lj-1.279-report.md`**: A5's landing and its
  exports, which you may now be able to name.
- **`agents/tasks/LJ-1-277/lj-1.277-report.md`**: the landing method.
- **`archive/dev/TASKS-archived.md` and `archive/dev/STATUS-archived.md`.**
  **The retired route also planned a GCH endpoint. Take SHAPE, never a
  claim**, and say what would NOT transfer.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md` splits II.5 into twelve rows.** **Say which
row A7 IS**, and whether Devlin states GCH in this shape at all. Return a
**LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-236/ProbeLJ1236A7.agda` FIRST, whole.

## SCOPE (write)

`src/L/GCH.lagda.md`, new, and `agents/tasks/LJ-1-280/` for your report.
**No existing master. Never `src/Everything.lagda.md`. Never
`dev/ledger.toml`. Do not create any other file under `src/`.**

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

**Lead with the delivered line count, the cold elapsed seconds, the rate
against 0.010514, and EXACTLY WHICH HYPOTHESES REMAIN UNSUPPLIED.** Then each
premise above marked VERIFIED or REFUTED at `file:line`. Then what the master
exports. Then the exact `src/Everything.lagda.md` line. Then the re-run that
PROVES this is a landing. Then your full import list with a reason per import,
because it becomes DD4's first GCH closure. **Mark every negative MEASURED or
INFERRED.**

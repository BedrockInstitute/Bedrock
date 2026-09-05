# LJ-1.380: diagnose `Condensation`'s seconds, on the `EnvSupply` shape

tier: pi (pi-subagent-mode), model `glm-5.3`. **I ran
`scripts/dispatch/dispatch_policy.py` before writing this line and took the
head it gave.** Agda. **PROBE. Land nothing.**

## WHY NOW, and the two figures that make it urgent

**MEASURED BY ME TODAY, 2026-08-16, cold with dependencies warm**, by deleting
the interface and timing the rebuild:

> **`src/L/Condensation.lagda.md`: 150.37 s over 6,820 in-fence lines =
> 0.022048 s/line, against the bar 0.013602 HISTORICAL(2026-08-16). THAT IS
> 1.62x THE BAR, exit 0.**

**AND 113 INSERTIONS ARE QUEUED TO LAND IN IT.** `[LJ-1.379]` measured the
`hasWitnessAt` chain end to end today: the floor of about 54 to 56 became a
PRICE of about 113 insertions, and **they all fall in this family**.

**So the question is not academic. Funding that repair without this diagnosis
means adding 113 lines to a master already 62 percent over the bar.**

## THE PRECEDENT, and it is why this is worth a dispatch

**`src/L/Coding/EnvSupply.lagda.md`: 495.23 s to 6.65 s, minus 488.59 s, for
FIVE inserted lines and three deleted. 56.5x the bar to 0.76x.**

> **The whole cost was ONE identity conversion.** The type said
> `Lset (sucIter 4 δ)` while the proof produced a `sucV` chain, and bridging
> the two spellings cost 438 seconds. **Depth is free; the mismatch is what
> costs.**

`dev/PLAN.md:163-165`. **That is the shape you are looking for: a SPELLING
mismatch that conversion has to bridge, not a hard piece of mathematics.**

## WHAT IS ALREADY KNOWN, so you do not re-derive it

**`[LJ-1.145]` diagnosed this master once and its finding was:「ONE
CONVERSION, 65 PERCENT OF ONE DEF」.** Sealing `satGraphAt` took 2,459 ms to
under 1 ms, about 21 s off, **40 percent of the gap at the time.**

**THAT WAS WEEKS AGO AND THE MASTER HAS GROWN SINCE, twice today**
(`[LJ-1.343]`'s vacuity repair and the tie supply, both ADDING lines, neither
a speed-up). **So `[LJ-1.145]`'s 40 percent is a fact about a smaller file.
Re-measure rather than subtract.**

**`[LJ-1.283]` also measured that a SHAPE-selected seal comes back VOID, minus
0.19 percent.** **So do not propose a seal because a definition looks big.
Find the cost first.**

## THE METHOD, and P-m and P-n are the laws for it

**1. PROFILE, DO NOT GUESS.** `agda --profile=definitions` charges conversion
to named definitions. **Report the Total, the `Miscellaneous` share and a
control arm from the same run** (C-53 as extended: `Miscellaneous` is the
empty account, and a verdict without it is not a verdict).

**2. FIND THE MISMATCH, NOT THE BIG DEFINITION.** **P-m: the check-cost rate
is a content-class certificate, and instantiation is the expensive class.**
**P-n: satisfaction content at a concrete carrier is a payable FLOOR, not a
defect.** **So a definition that is merely large and honest is not your
target; a definition paying for a spelling bridge is.**

**3. NAME THE TWO SPELLINGS.** If you find one, say what the type says and
what the proof produces, exactly as the `EnvSupply` record does.

## THE ABORT CRITERION (D-1)

- **A MISMATCH IS FOUND.** **Report both spellings, the seconds it costs
  measured by a control, and the smallest edit that bridges them.** **Do not
  land it; price it.** **Best.**
- **THE COST IS DIFFUSE.** **If no single site holds a large share, say so
  with the profile.** **`[LJ-1.145]`'s sibling finding on another master was
  that cost was NOT concentrated, largest definition 2.6 percent, and that is
  a legitimate and valuable answer: it means the master is honestly expensive
  and the bar conversation moves to the owner.**
- **THE FLOOR IS THE PROBLEM.** **If most of the 150 s is P-n's payable
  floor, the master is not over the bar by craft but by content. Say so; that
  is a route-level finding and the owner should hear it.**
- **A WALL.** **C-58: replace a numeral pattern-match split with the library
  eliminator before bisecting.** **This master is the known 8 GB waller's
  home; `sucK` is inside the 28.**

## CONSTRAINTS

- **LAND NOTHING. `src/` is forbidden** (I-5). Write only in
  `agents/tasks/LJ-1-380/`. **You may COPY a master into your directory and
  edit the copy.**
- **`[LJ-1.377]`'s new gate `check-live-record-claims.py` is wired; do not
  edit it.**
- **COUNT THE AGDA SLOTS** before every invocation, exactly:
  `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`. **Both obvious
  alternatives OVER-COUNT, MEASURED.** Cap TWO.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **This
  master takes about 150 s per cold run: budget your runs, and say how many
  you spent.** **Report the empty-file floor beside every seconds figure**
  (C-53).
- **A TASK THAT MEASURES CHECK TIME GETS A QUIET MACHINE.** **If the slot
  count is not 0 when you time, WAIT for it, and say in your report what it
  read before each timed run.** **A figure taken beside a live sibling is not
  a figure.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-380/lj-1.380-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `lint-agda.py --check`. **No em dash.** ASD-STE100. Evidence is `file:line`.
  Mark every negative **MEASURED** or **INFERRED**.

## PREMISES

- **The master runs 150.37 s over 6,820 lines, 1.62x the bar**, measured by me
  2026-08-16 at `src/L/Condensation.lagda.md`.
- **The bar is `ac_baseline_module_rate` times `tolerance`**, at
  `dev/ledger.toml`'s `[ratio]` table, computed at
  `scripts/measure/check-ratio.py:477`.
- **113 insertions are queued into this family**, at
  `agents/tasks/LJ-1-379/lj-1.379-report.md:1`.
- **`EnvSupply` fell 488.59 s for five inserted lines**, at
  `dev/PLAN.md:163-165`.

**Mark each VERIFIED or REFUTED at `file:line`.**

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Eleven of my last forty-one briefs carried a claim an agent measured FALSE.**
**The one at risk: 「the `EnvSupply` shape recurs here」.** **That is an analogy
from one master to another, and P-l says a measured cure does not transfer by
analogy: re-measure it at its own site.** **`EnvSupply` was 56.5x the bar and
this master is 1.62x, which is a different regime, and a 1.62x master may
simply be honestly expensive.** **Expect to tell me there is no mismatch.**

## THE RULES

**P-m and P-n are the laws of this task; read both FULL entries before you
profile.** **P-l: a measured cure does not transfer by analogy.** **P-y: a
seal in shared upstream machinery can make every master faster and the verdict
worse.** **C-53 as extended: `Miscellaneous` is the empty account and every
seconds figure states the empty-file floor.** **C-58, C-44, C-45, C-57, D-10,
C-42, P-k, P-q, P-t.** **C-12, C-22, C-32, C-36, C-39, C-40.** I-5.
**D-1, D-26.** **DD0, DD4, DD8, DD18, DD23, DD24, DD25, DD28.**

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and
`--grep seconds`, and read every statement.

## DD4

**Maximize the code the two proofs share, and write it generic.** **NAME YOUR
AXIS** (C-46), fixed at `scripts/measure/ledger.py:50`. **This master is in
the GCH closure. Say whether it is in the AC closure too**, from
`ledger.py --reuse` rather than from memory, **because P-y measured that a
cure upstream of both wings can move the DD24 ratio the wrong way while making
everything faster.** **If your cure is upstream of both, say so loudly: that
is the case the owner has already been burned by.**

## ARCHIVE (DD18)

**`scripts/gate/check-dd18-survey.py` GATES your return: name each of the four
corpora, cited or declined in ONE line, and QUOTE one line per archived file
you read, at its real line number.**

- **`archive/src/2026-08-09-rud-route/`**: **did the retired route have a
  condensation master, and what did it cost?** **A retired comparable is the
  only outside number this question has.**
- **`archive/dev/JOURNAL-archived.md`**: **grep for the retired route's
  seconds diagnoses.** **The identity-conversion shape may be recorded there
  under another name.**
- **`archive/dev/TASKS-archived.md`**: the retired performance dispatches,
  taking SHAPE and never a claim.
- **`archive/dev/DECISIONS-archived.md`**: any ruling on sealing or on
  performance. **WHY NOT in one line if none bears.**

## LITERATURE (DD18)

**`dev/literature/j-hierarchy.md`** for what condensation is supposed to cost
structurally. **Say in ONE line whether the orthodox development suggests this
chapter should be large, because「honestly expensive」is one of your possible
verdicts and the literature is the only outside check on it.** Return a
**LITERATURE USED** section.

## SCOPE (read)

`dev/PLAN.md:155-165` FIRST: the `EnvSupply` episode with its two spellings.
It is the shape you are hunting and it is 10 lines.

## SCOPE (write)

`agents/tasks/LJ-1-380/` only.

## RETURN

**Lead with ONE word: MISMATCH-FOUND, DIFFUSE, or HONESTLY-EXPENSIVE.** Then
the profile with its Total, `Miscellaneous` share and control arm. Then the two
spellings if you found them, with the seconds a control charges to the bridge.
Then the smallest edit that would fix it, priced and NOT landed. Then whether
the master is in one closure or both. Then how many cold runs you spent and
what the slot count read before each. **Mark every negative MEASURED or
INFERRED.**

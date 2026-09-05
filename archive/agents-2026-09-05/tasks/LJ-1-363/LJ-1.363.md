# LJ-1.363: land DD18's amended enforcement, B2 gating and B1 printing

tier: pi (pi-subagent-mode), model `glm-5.3`. **I ran
`scripts/dispatch/dispatch_policy.py` before writing this line and took the
head it gave.** No Agda. **BUILD.**

## THE OWNER'S RULING, 2026-08-16

> **For landing DD18's checking mechanism, do what you said: B2 in full, B1
> only in part.**

**I have already written that ruling into DD18's row in `dev/PLAN.md`.**
**READ THAT ROW FIRST. It is the specification and this brief only points at
it.** **If this brief and the row disagree, THE ROW WINS and you say so in
your report.**

## WHY THE TWO HALVES ARE UNEQUAL, because a checker written without this
## will get the balance wrong

**`[LJ-1.358]` measured that under DD18's own「one honest line」clause, the
decay was LEGAL.** One bullet was verbatim in 63 briefs; ten reports surveyed
a 265-row index at its first nine lines; **every gate stayed green, correctly**.

**`[LJ-1.357]` measured why a count must not gate:** DD4 has no metric BY THE
OWNER'S RULING, because a count is gamed the moment it gates, **and gaming a
five-brief repeat threshold was MEASURED at one keystroke, twice.**

**So: B2 GATES because it forces an ACT (open the file, quote a line). B1 only
PRINTS because it forces only a FORM, and a form is four pastable lines away
from ritual.** **`[LJ-1.358]` said so in its own words: B1 buys VISIBILITY,
not surveys.**

## WHAT TO BUILD

**ONE new checker, `scripts/gate/check-dd18-survey.py`, wired into
`make check`.**

### B2, THE GATE. The return side.

**A return's ARCHIVE USED names every archive path its brief cited, TOOK or
DECLINED, and quotes ONE line read per archived file.** **LITERATURE USED
mirrors it when the brief cites `dev/literature/`.**

**The universe is enumerable because the BRIEF defines it. That is the whole
reason this half can gate and the brief side cannot.**

**`[LJ-1.357]` measured three over-reaches in `[LJ-1.356]`'s R3 and you must
avoid all three:**

1. **51 of 92 failures were ONLY a missing LITERATURE USED heading.** **Report
   that separately from an unanswered path; they are different defects.**
2. **30 of 55 unanswered paths WERE answered by a deeper path**: the brief
   cites a directory and the report cites files inside it. **A deeper path
   ANSWERS a shallower one.**
3. **A written DECLINE is compliance, not a defect.** `[LJ-1.357]` found
   `LJ-1-168`'s report declining in writing at `:573`「NOT read」and R3
   punished the spelling. **Honest rate after all three corrections: about
   15, not 93.**

**Also MEASURED by `[LJ-1.357]`: `agents/tasks/archive/` is OUTSIDE DD18's
four corpora** (`LJ-1-153`'s case). **Do not count it.**

**And DD18's four corpora are the ARCHIVES.** **A citation of a live
`agents/tasks/` directory is NOT compliance**, `scripts/gate/check-archive-cited.py:26-27`.

**AN EPOCH IS REQUIRED, and `check-dd4-stated.py`'s `PRE_EPOCH` at `:88` is
the model to copy.** **A new gate that fails the whole corpus teaches every
author to paste.** **Freeze what predates the ruling; the ruling is dated
2026-08-16.** **Write the frozen set's SCALE into its comment, not into a
commit message** (C-59, and `check-premises-stated.py`'s `SECOND_EPOCH` is
today's worked example).

### B1, THE PRINT. The brief side. IT NEVER EXITS NONZERO.

**Report, never gate:**

- which briefs do not name each of the four corpora, cited or declined;
- **shout TEMPLATE when one ARCHIVE bullet's reason text repeats verbatim
  across five or more briefs.** **Normalize the cited path to `<PATH>` before
  comparing**, which is `[LJ-1.356]`'s method and it worked: it found four
  template bullets sharing 40 briefs.
- **`[LJ-1.357]` found `[LJ-1.356]`'s R2 blind to a FULLY drifted brief**,
  because it only read bullets that already contained an archive path
  (`probe_358_r3_fixed.py` region). **Fix that.**

**Two measured over-reaches in `[LJ-1.356]`'s R1 to avoid:** **`dev/ARCHIVE.md`
is named BY DD18 and failed R1's `archive/src/` CODE regex**; and **a brief
spelling archive paths under `_build/` scored 0 of 4 despite a 738-character
survey.**

## WHAT NOT TO BUILD

- **NO R4 term cross-reference.** **`[LJ-1.357]` REFUTED its founding
  counterfactual**: run on `[LJ-1.107]`'s own brief it keeps ZERO terms. **The
  owner did not rule it in. Leave it out.**
- **Do NOT touch `dispatch.py`'s heading refusal.** DD18's amended row says it
  stands unchanged.
- **Do NOT edit `AGENTS.md`.** DD19 gates it and nothing is canonical twice:
  the rule's home is DD18's row, which I have already amended.
- **Do NOT edit `dev/PLAN.md`.** I own the ruling text and the task index.
- **Do NOT retro-fit existing briefs or reports.** A record is never rewritten.

## THE ABORT CRITERION (D-1)

- **IT LANDS AND `make check` STAYS GREEN with the epoch set.** Report the
  frozen count, the live defect count, and the runtime. **Best.**
- **THE HONEST RATE IS NOT ABOUT 15.** **Then `[LJ-1.357]`'s correction is
  wrong in one direction or the other. Say which, with the sampled cases.**
- **B2 CANNOT BE MADE FAIR.** **If every formulation either over-reaches or
  catches nothing, say so with the evidence and STOP.** **A stop is a
  deliverable, and the owner would rather have that than a gate that trains
  pasting.**

## CONSTRAINTS

- **You MAY create `scripts/gate/check-dd18-survey.py` and add ONE target to
  `Makefile`'s `check:` line.** **Edit nothing else.** `src/` is forbidden
  (I-5).
- **RUN IT OVER THE LIVE CORPUS and report real numbers**, not a design.
- **`[LJ-1.362]` is live, writes `src/FOL/Bernstein.lagda.md`, and holds an
  Agda slot.** **Stay out of `src/` entirely and you cannot collide.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **Do not run `make check` on the whole
  tree; run YOUR target alone.** I run the full gate.
- **Create `agents/tasks/LJ-1-363/lj-1.363-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check`. **No em dash.**
  ASD-STE100. Evidence is `file:line`, and for a rate, the command that
  produced it. Mark every negative **MEASURED** or **INFERRED**.

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Eleven of my last thirty-one briefs carried a claim an agent measured
FALSE, and two of the last three quoted a stale line number.** **The one at
risk: 「the honest rate is about 15」.** **That is `[LJ-1.357]`'s number,
produced by correcting someone else's tool rather than by writing a clean
one.** **Re-derive it from scratch. If your clean implementation gives a
different number, YOURS is the measurement and theirs was an estimate.**

## THE RULES

**C-59, written today: a gate you do not run is worth what a gate you do not
have is worth; and never read a pipe's exit code for a gate.** **C-48: a
policy that only a document states is not enforced.** **C-45: `exit 0` is not
a supply.** **C-57, D-10, C-42, C-44, C-53, P-l, P-k.**
**C-22, C-32, C-36, C-39, C-40.** I-5. **D-1, D-26.**
**DD0, DD4, DD17, DD18, DD19, DD23, DD25.**

Run `.venv/bin/python scripts/dispatch/rules.py --for build` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker. **NAME YOUR AXIS** (C-46).

**Your axis is not the two towers; say so plainly rather than forcing the
section.** **The DD4 content that IS live here is the no-metric ruling
itself:** **DD4 has no threshold because a count is gamed the moment it
gates.** **Your B1 threshold of five is a count. It PRINTS, so it is legal.
State in one line why printing escapes the objection that gating does not.**
**If you conclude it does not escape it, say so: that would mean B1 should not
carry a threshold at all, and the owner should hear it.**

## ARCHIVE (DD18)

**Your own checker will judge this section, so write it as the example.**
**Name each of the four corpora, cited or declined in one line, and quote one
line per file you read.**

- **`archive/dev/DECISIONS-archived.md:42`.** **`[LJ-1.357]` UPHELD a negative
  here: D20 governs RETIRING code, not surveying it, so no survey rule existed
  to die.** **Cite it or decline it; do not re-derive a settled negative.**
- **`archive/dev/TASKS-archived.md:116`**, the T81 row. **Note the corrected
  history: `[LJ-1.107]` DID survey and CHOSE to build its own. I repaired the
  checker that said otherwise. Do not repeat the old story.**
- **`archive/dev/JOURNAL-archived.md`**: **MEASURED by `[LJ-1.357]`,
  `grep -c "LJ-1\."` returns ZERO, so it holds nothing about `[LJ-1.107]`.**
  **Decline it in one line rather than substituting another passage silently:
  that silent substitution was one of `[LJ-1.356]`'s defects.**
- **`archive/src/2026-08-09-rud-route/`**: **almost certainly nothing bears on
  checker design. Say so in one line naming what you checked.** **That honest
  decline is exactly what B1 asks of every author, and your report is the
  first worked example of it.**

## LITERATURE (DD18)

**MEASURED TWICE ALREADY, by `[LJ-1.356]` and verified by `[LJ-1.357]`:
nothing in `dev/literature/` bears on rule or checker design;
`formalizations-landscape.md` is 421 lines of systems index.** **Cite that
finding and move on. Do not spend a third pass.** Return a **LITERATURE
USED** section saying exactly that.

## SCOPE (read)

**`dev/PLAN.md`'s DD18 row, the amendment dated 2026-08-16, FIRST. It is your
specification.** Then `scripts/gate/check-premises-stated.py`, for the epoch
pattern and today's worked `SECOND_EPOCH` comment.

## SCOPE (write)

`scripts/gate/check-dd18-survey.py`, ONE line in `Makefile`, and
`agents/tasks/LJ-1-363/`.

## RETURN

**Lead with ONE line: does `make check` stay green with your target wired and
its epoch set.** Then B2's live defect count, split by the three defect kinds
`[LJ-1.357]` separated. Then the frozen count and the epoch's justification.
Then B1's print output: how many briefs miss a corpus, and every TEMPLATE
cluster with its size. Then your runtime. Then your own false negatives, named
by you. **Mark every negative MEASURED or INFERRED.**

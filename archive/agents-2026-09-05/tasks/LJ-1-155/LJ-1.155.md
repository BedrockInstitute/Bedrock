# LJ-1.155: is there a second dominant term, or is the wing intrinsically this expensive?

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**Diagnose the Condensation family to EXHAUSTION.** `[LJ-1.145]` found ONE term
and it was cured. **Nobody has looked for a second.**

**This task decides whether the owner has to rule on DD4 against DD24 at all.**

## WHY IT DECIDES A RULING

`[LJ-1.147]` sealed shared upstream machinery. **Every master got faster and
the verdict got WORSE**: the AC side gained 41.7 percent, the GCH wing 7.9, the
baseline fell 0.011828 to 0.009143, and the ratio went **1.56x to 1.91x**.

**That is a property of the bar, not an accident of that edit.** A cure in
shared code improves the ratio only when the judged side gains MORE than the
reference side.

**So there are two worlds and this task says which one we are in:**

- **The wing has more terms of its own.** Then it closes its own gap, the cure
  is craft, and **no ruling is needed.**
- **The cost is spread with no dominant term.** Then the wing is intrinsically
  this expensive, **the ruling becomes unavoidable, and the owner has the full
  evidence to make it.**

**BOTH ANSWERS ARE COMPLETE DELIVERABLES. The second is not a failure.**

## WHERE THE SECONDS ARE NOW, MEASURED after the cure

The baseline is **0.009143** and the bar is **0.0136**.

| master | s/line | lines | seconds |
|---|---:|---:|---:|
| `L/Condensation` | 0.0171 | 6,451 | **110.42** |
| `L/Cond/TwelveAgree` | 0.0823 | 309 | 25.43 |
| `L/Cond/LowerAgree` | 0.0728 | 265 | 19.30 |
| `L/Cond/UpperAgree` | 0.0426 | 268 | 11.41 |
| **wing aggregate** | **0.0174** | 11,438 | **199.50** |

**1.91x.** To reach the bar the wing needs about **156 s**, so the gap is about
**44 s** at today's line count.

**`[LJ-1.153]` has since added 55 lines to `Condensation` and its own runs put
the master near 124 s. Re-measure rather than quote these.**

## WHAT `[LJ-1.145]` ALREADY DID, so you do not repeat it

**Found and cured:** one conversion. Taking a component out of a pattern split
and naming its folded type cost 2,526 ms, **65 percent of the master's most
expensive definition**. Cured by sealing `satGraphAt`. `LeafAgree.out` went
9,833 to 1,306 ms.

**Refuted, MEASURED, and NOT to be revisited:**

- **P-x.** The record field `[LJ-1.109]`'s title names was added then REMOVED;
  `grep -c sucK` returns 0. The record that IS there costs 833 ms, 0.7 percent.
- **P-w.** `useApp` 10 ms against `useFun` 23 ms. Removing a module application
  cost MORE.

**Its method, which worked:** `agda --profile=internal` and
`--profile=definitions` on the master, then a verbatim transplant of the single
worst definition into a probe, then a bisection inside it.

## WHAT TO DO

1. **Profile the master again**, after `[LJ-1.153]`'s 55 lines. **The
   distribution may have moved.**
2. **Find the next worst definition and transplant it**, as `[LJ-1.145]` did.
   **A rate over 6,451 lines is an average and averages hide the term.** P-t
   measured a twentyeightfold spread INSIDE one file.
3. **Do the three `*Agree` masters too.** They are 0.0426 to 0.0823, three to
   six times the bar, and **nobody has profiled them at all.** 56 s across 842
   lines is 28 percent of the wing's seconds.
4. **Price whatever you find**, in lines changed and seconds saved, each with
   its basis (DD8), and **say whether the cure is upstream and shared or local
   to the wing.** That distinction is the whole DD4-against-DD24 question:
   **an upstream cure moves the baseline too and may make the ratio worse
   again.**

## THE ABORT CRITERION

- **You find a second term worth double figures of seconds**: report it with
  its cure and its price. STOP.
- **The cost is spread with no dominant term**: **STOP AND SAY SO, with the
  distribution.** State it as the finding it is: **the wing is intrinsically
  this expensive and the DD24 ruling is now unavoidable.**
- **The next term's cure is upstream and shared**: **say so explicitly**, and
  estimate what it would do to the baseline. **A cure that helps the AC side
  more is a cure that makes this verdict worse**, and the owner must see that
  before funding it.
- **Anything walls**: STOP, report it with its seconds.

## WHAT YOU MUST NOT DO

- **DO NOT REWRITE ANY MASTER.** This is a diagnosis. A cure goes in a probe.
- **Do not delete lines to improve a ratio.** DD24's own row says the ratio
  exists so the content must be the same KIND of content, and shrinking the
  denominator is the cheat it refuses. P-q measured 315 lines removed buying
  11.8 seconds.
- **Do not revisit P-x or P-w at this site.** Both refuted, MEASURED.
- **Do not touch `src/L/Coding/Graph.lagda.md`.** 21 consumers are green on
  its seal.
- **A probe goes in `agents/tasks/LJ-1-155/`**, never in `src/`, tracked, never
  deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** A sibling,
  `[LJ-1.154]`, may run Agda. **Report the load beside every absolute figure,
  discard a warm-up, and take more than one run for any figure a decision rests
  on.** `[LJ-1.148]` measured a fixed 0.9 s first-run penalty per series and
  12.8 percent between-series uncertainty, **which is most of DD24's 1.15x
  tolerance.**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** 「There is no second term」 is
MEASURED only if you profiled and say how deep you went.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**Here DD4 is the problem rather than the goal, and that is the point of this
task.** Say, for every cure you price, whether it is shared or wing-local, and
what it does to the baseline. **The owner cannot rule without that column.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-145/lj-1.145-report.md`**, read WHOLE, and its four
  probes. **The method and the two refutations.**
- **`agents/tasks/LJ-1-147/lj-1.147-report.md`**, read WHOLE. The cure, the
  measurement, and the ratio finding.
- `agents/tasks/LJ-1-153/lj-1.153-report.md`: the 55 lines that landed since.
- **`dev/LESSONS.md` P-y, P-t, P-s, P-q, P-m, P-l, C-12**, read WHOLE.
- `dev/PLAN.md` DD24, read whole, for what the bar is and why it is a ratio.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature governs elaboration cost. Say so in one line.**

## SCOPE (read)

`src/L/Condensation.lagda.md` and the three `*Agree` masters, then
`agents/tasks/LJ-1-145/lj-1.145-report.md`.

## SCOPE (write)

`agents/tasks/LJ-1-155/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for recon`.

- **P-t.** An average hides the term; the carrier never certifies the class.
- **P-s, P-q, P-m, P-l, P-y, P-w, C-12, C-22, C-36, C-38 as extended, C-39.**
- **DD8, D-1, D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-37. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`. Verify a per-module figure
  with `.venv/bin/python scripts/check-ratio.py --module <file> --runs N`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with which of the two worlds we are in**, and say it in one sentence.
Then the distribution, at the finest granularity you reached, with the load and
the run count. Then any second term, its cure and its price. Then, for every
cure, SHARED or WING-LOCAL and what it does to the baseline. Then the three
`*Agree` masters, which nobody has profiled. **Mark every negative MEASURED or
INFERRED.**

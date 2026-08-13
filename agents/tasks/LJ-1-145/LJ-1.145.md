# LJ-1.145: why the Condensation family costs 84 percent of the wing's seconds

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**Find why `src/L/Condensation.lagda.md` checks at 0.0187 s per line, and say
what would fix it and what that costs.** **DIAGNOSE. Do not rewrite.**

## WHAT IS MEASURED, and I ran the tool myself

The GCH wing was judged today against a re-selected baseline. **Baseline
0.011828 s/line, tolerance 1.15, bar 0.0136.**

| master | s/line | lines | seconds | |
|---|---:|---:|---:|---|
| **`L/Condensation`** | **0.0187** | **6,445** | **120.61** | OVER |
| `L/Cond/TwelveAgree` | 0.0819 | 309 | 25.32 | OVER |
| `L/Cond/LowerAgree` | 0.0731 | 265 | 19.38 | OVER |
| `L/Cond/UpperAgree` | 0.0424 | 268 | 11.36 | OVER |
| **the family** | **0.0242** | **7,287** | **176.67** | **2.0x baseline** |
| the wing's other eight | **0.0082** | 4,145 | 34.10 | **0.70x, all pass** |

**The family is 64 percent of the wing's lines and 84 percent of its seconds.
Everything else in the wing is 30 percent FASTER than the AC side.**

**The arithmetic that makes this the whole task:** if the family reached the
bar, 176.67 s becomes 99.1 s, and the wing lands at 0.01165 s/line, **under the
baseline itself.** **One family decides the wing's verdict.**

## THE LEAD, and it is the commit's own title

**`[LJ-1.109]` landed on this master and its subject line reads:**

> All eleven refuted names are tied or gone, **and a record field walls the
> master**

**`dev/LESSONS.md` P-x says exactly this class:** a transparent construction in
a RECORD FIELD type is paid by **every elaboration of the record**; state it as
a telescope fact instead.

**That is a lead, not a finding. It is INFERRED and you may refute it.**

## THE SECOND LEAD, and it predicted the number before anyone measured it

**`dev/PLAN.md:513`, the `[LJ-1.57-A]` audit row, standing since 2026-08-12:**

> Placing 884 lines at the measured 0.0755 puts Condensation at 0.0220, **1.73x
> over DD24's bar**

**Today it measured 0.0187, 1.58x.** The prediction was written before the
measurement and the class was right. **Read that row and its task. It may
already name the term.**

## THE THIRD LEAD, measured on a DIFFERENT master today

**`[LJ-1.136]` hit three heap walls at the C-12 cap and cured all three**, and
the cures are the shape you are hunting:

| what | seconds | result |
|---|---:|---|
| two `Small` module applications, unsealed | 138.52 | **heap exhausted at 8g** |
| one application, unsealed | 2.01 | green |
| `agree` instantiated, unsealed | 98.42 | **heap exhausted at 8g** |
| same file, `injOf` sealed `opaque` | **1.27** | green |

**P-w is now MEASURED at this tree, not inferred: a module APPLICATION copies,
and a shared helper written as a FUNCTION instead is the difference between an
exhausted heap and two seconds.** Its report is
`agents/tasks/LJ-1-136/lj-1.136-report.md`.

## WHAT TO DO

1. **Profile it.** `agda +RTS -s` and Agda's own per-module and per-definition
   profiling. **Find WHERE the seconds are**, at definition granularity if the
   tooling allows. **A rate over 6,445 lines is an average and averages hide
   the term. P-t measured a twentyeightfold spread INSIDE one file.**
2. **Test the P-x lead specifically.** Find the record field, find what its
   type constructs transparently, and **measure the difference a seal makes**.
   One `opaque`, one measurement, before and after.
3. **Test the P-w lead.** Count module applications in the family. **`[LJ-1.136]`
   measured one application at 2.01 s and two at heap exhaustion.**
4. **Then price the cure.** In lines changed and in seconds saved, each with
   its basis (DD8). **Name the widest unmeasured term of the cure itself.**

## WHAT MAKES THIS TASK EASY TO GET WRONG

**A line lever is not a seconds lever.** `dev/LESSONS.md` P-q measured 315
lines removed buying 11.8 seconds. **Do not recommend deleting lines to hit a
ratio: the ratio exists so that the content must be the same KIND of content,
and shrinking the denominator is the cheat it was designed to refuse.** DD24's
own row says so.

**And a rate does not certify a class. P-t found the carrier never does; the
formula does.**

## THE ABORT CRITERION

- **You find the term and price the cure**: report and STOP.
- **The cost is spread evenly with no dominant term**: **STOP AND SAY SO.**
  That is a real and expensive finding: it means the family is intrinsically
  this expensive and the wing's verdict is a content question for the owner,
  not a craft one.
- **The cure needs a rewrite bigger than the block**: say so and price both.
- **Anything walls**: STOP, report it with its seconds.

## WHAT YOU MUST NOT DO

- **DO NOT REWRITE THE MASTER.** This is a diagnosis. **A cure goes in a probe,
  and the probe is thrown at the question, not at the tree.**
- **Do not touch the three `*Agree` masters.** A sibling, `[LJ-1.144]`, owns
  whether they live at all. **If your diagnosis bears on that, say so; do not
  act on it.**
- **Do not delete lines to improve a ratio.**
- **Do not touch `src/ProbeLJ1134A.agda` or `src/ProbeLJ1136*.agda`.**
- **A probe goes in `agents/tasks/LJ-1-145/`, beside this brief**, never in
  `src/`, tracked, never deleted. **That rule changed today; read `AGENTS.md`
  fresh and `dev/LESSONS.md` D-1.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, and NEVER raise the cap.**
  Report a heap exhaustion as a wall; `[LJ-1.136]` did and the wall was the
  finding.
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE MACHINE

**Load at dispatch: 4.89 / 5.01 / 5.01.** A sibling, `[LJ-1.144]`, may run
Agda. **Measure the load yourself, repeatedly, and report it beside every
absolute figure. If the machine is too noisy for a seconds measurement to mean
anything, say so and stop.** `[LJ-1.135]` measured 6.9 percent machine drift on
an identical tree today, so a figure without a stated load is not a price.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** **My three leads above are INFERRED
and you may refute any of them. A refutation is a full deliverable.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker, so it is stated in every brief and answered in
every return.

**If the cure is a generic helper written once, both trophies get it. If the
cure is local to this master, say that too, because it changes what the cure is
worth.**

## ARCHIVE (DD18)

- **`agents/tasks/archive/LJ-1-109/`**, read WHOLE. **Its own title says a
  record field walls the master.**
- **`agents/tasks/LJ-1-136/lj-1.136-report.md`**, read WHOLE. Three heap walls,
  three cures, P-w measured.
- `agents/tasks/archive/LJ-1-57/`: the audit that predicted this number.
- `agents/tasks/archive/LJ-1-76/`: the split that produced the `*Agree` family.
- **`dev/LESSONS.md` P-x, P-w, P-m, P-q, P-t, P-s, C-12**, read WHOLE.
- `dev/ledger.toml`'s `[ratio]` block, for the baseline and what it is.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature governs elaboration cost. Say so in one line.**

## SCOPE (read)

`src/L/Condensation.lagda.md` whole, FIRST. Then
`agents/tasks/LJ-1-136/lj-1.136-report.md` sections on the heap walls.

## SCOPE (write)

`agents/tasks/LJ-1-145/` only, for your report and any probe. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for recon`, and read
every statement.

- **P-x.** The record-field law. **This is the lead.**
- **P-w.** A module application COPIES.
- **P-m, P-q, P-s, P-t.** Rate, class, and why an average hides the term.
- **C-12.** ONE agda process, cap never raised.
- **DD8, D-1, P-l, C-22, C-36, C-38 as extended, C-39, C-40.**
- **C-31, C-32, C-33, C-34, C-37, D-10, D-26, D-29, D-30. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`. Verify with
  `.venv/bin/python scripts/check-ratio.py --module <file>`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with WHERE the seconds are**, at the finest granularity you reached, and
the load beside it. Then whether P-x holds, MEASURED, with the before and after
of one seal. Then P-w. Then the cure, its lines and its seconds, with its
basis and its widest unmeasured term. Then whether the cure is generic or
local, for DD4. **Mark every negative MEASURED or INFERRED.**

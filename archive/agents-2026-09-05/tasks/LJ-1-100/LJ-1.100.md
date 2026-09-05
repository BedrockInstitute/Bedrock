# LJ-1.100: extend the consumer's frame and re-measure the 39

tier: codex (default)

## GOAL

**Turn the repair question into one number.** The ties are measured. The
consumer's frame is measured short. **Extend the consumer's frame with what
the rows need, re-run the instantiation, and report how many hypotheses
still have no supplier.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, clean at
`9b51977` except `dev/PLAN.md`. HEAD is green. **A sibling agent holds the
other Agda slot and has held it for over two hours.**

## WHAT IS MEASURED NOW

`[LJ-1.99]` closed the question my own brief had blocked. **I re-ran its
probe: exit 0, 1.85 s.**

- **The four-step `arityK` chain closes `entryK`.** GREEN,
  `src/ProbeLJ199A.agda:65-204`. The chain is no longer inferred.
- **`arSubK-*` is `arityK` once.** GREEN.
- **The rows supply every tie.** All nine EnvSet-using row modules hold an
  `envK` parameter and bind or derive `E ∈ K`; the report tables the `out`
  and `back` lines for each. The five key facts' sites bind `ar ∈ K` and
  `a ∈ K`. **Source-verified, per fact.**
- **`EnvSet`'s own telescope does NOT supply `E ∈ K`.** MEASURED, exit 42.
  That is a fact about the inner module, not about the rows.

**So the ten refuted facts are repairable at the row frame.** The remaining
obstacle is the one `[LJ-1.96]` and `[LJ-1.99]` both name: **the consumer's
pinned frame (`SatGraphAgree`, `src/L/Condensation.lagda.md:6476-6513`) has
no env-set slot and no `envK` family, so the repaired facts are not statable
there.**

## THE QUESTION

**If the consumer's frame gains what the rows hold, does the instantiation
close?**

`[LJ-1.93]` measured 39 of the composer's 69 hypotheses unsupplied, as 39
unsolved metas (`src/ProbeLJ193B.agda`, exit 42). **That measurement was
taken against the frame as it stands. Take it again against an extended
frame.**

1. **Build the extended consumer frame in a probe.** Start from
   `SatGraphAgree`'s telescope: the 29-field `KFacts`
   (`src/L/Condensation.lagda.md:5734-5770`) and the six site facts
   (`:6492-6513`). **Add the facts the rows hold and the consumer does not**,
   in their TIED forms where a fact was refuted. **Name each addition and
   say why the consumer can hold it.**
2. **Re-run `[LJ-1.93]`'s instantiation against that frame.** `src/ProbeLJ193B.agda`
   is the probe to copy. **Report the new unsolved-meta count.**
3. **Report which hypotheses still have no supplier**, by name, at
   `file:line`.
4. **Say what the additions cost**: how many facts, and whether each is a
   `KFacts` field, a site fact, or a new derivation.

## THE HONEST TEST, and it is the one that has caught four defects

**Every addition you make must be one the consumer could actually hold.**

- **A fact added to the frame is a new hypothesis, not a discharge.** C-38.
  **Say so in those words for every addition.**
- **Check each addition against the `tmKeyK` shape before you add it**: does
  it quantify over something no premise binds? **If it does, you have added
  an empty type and the instantiation will close for the wrong reason.**
  **Try to refute every fact you add.** `src/ProbeLJ197A.agda` is the shape.
- **Do not add a fact whose only justification is that it makes the
  instantiation close.**

## THE ABORT CRITERION, fixed in advance per D-1

- **The count reaches zero**: report the extended frame, the additions, and
  the term, then STOP. **That would mean the split is repairable end to end
  and the phase has a route again.**
- **The count does not reach zero**: report the number and the names. **A
  number is the deliverable either way. Do not stop at the first failure.**
- **An addition is refutable**: STOP and report it. **That is the most
  valuable outcome and it has happened five times this phase.**
- **Anything walls**: STOP, report the wall with its seconds.

**Work in `src/ProbeLJ1100*.agda`. Do not touch any master.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. If a
check does not return, KILL IT before you start another, and report the wall
with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not weaken any row's conclusion, and do not weaken the twelve-row
  statement.**
- **Do not repair, delete or archive any master.** This dispatch measures.
- **Do not touch anything under `src/L/Coding/` or `src/V/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers and counts from the source, never from a report.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**`[LJ-1.93]` set the test that matters: sharing is only free when the
shared frame is the frame the consumer actually holds.** **This dispatch is
that test, run against an extended consumer frame. Answer DD4 with the
count.**

## ARCHIVE (DD18)

- **`_build/lj-1.99-report.md`**, read WHOLE, and **`src/ProbeLJ199A.agda`**
  and `src/ProbeLJ199B.agda`. **The tied forms and the per-row supply
  table. Verify the row lines in the source.**
- **`_build/lj-1.93-report.md`**, read WHOLE, and **`src/ProbeLJ193B.agda`**,
  read WHOLE. **That probe is the one to copy and re-measure.**
- `_build/lj-1.97-report.md` and `src/ProbeLJ197A.agda`, the ten
  refutations and the refutation shape you must reuse on every addition.
- `_build/lj-1.96-report.md` and `_build/lj-1.98-report.md`, the two
  consumer-side negatives.
- `src/L/Condensation.lagda.md:5734-5770` and `:6476-6513`, the record and
  the consumer's telescope.
- `src/L/Condensation/TwelveAgree.lagda.md:45-243`, the composer's frame.
- `dev/LESSONS.md` **C-38 as extended**, C-35, C-36, D-29, D-30, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked. Spend nothing.** Say so in one line.

## SCOPE (read)

`src/ProbeLJ193B.agda` FIRST, then `src/ProbeLJ199A.agda`, then
`src/L/Condensation.lagda.md:6476-6513`.

## SCOPE (write)

`src/ProbeLJ1100*.agda` only. Your report is `_build/lj-1.100-report.md`.
**No master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for probe`, and read every
statement.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it. **An addition to a frame is a new hypothesis, not a discharge.**
- **C-35.** A block with no consumer is UNTESTED.
- **C-36.** Write the term you could not write.
- **D-30.** Price what the CONSUMER needs.
- **D-1, D-8, D-10, D-26, D-29.**
- **P-h, P-i, P-k, P-l, P-m, P-n, P-o, P-q, P-t, P-u, P-v, P-w** as the
  bundle gives them.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally. **`[LJ-1.94]` has not grown
  its report in over an hour and that is the rule it is breaking.**
- **C-31, C-32, C-33, C-34, C-37.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.100-report.md` incrementally, skeleton first.

**Lead with the new unsolved-meta count against the extended frame**, and
the old one, 39, beside it. Then the additions, one row each: name, form,
why the consumer can hold it, and whether you tried to refute it. Then the
hypotheses that still have no supplier, by name. **Mark every negative
MEASURED or INFERRED.** Then the DD4 answer, with the count. Confirm no
master was touched.

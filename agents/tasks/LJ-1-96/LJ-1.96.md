# LJ-1.96: price the ideal form of the three split masters

tier: codex (default)

## GOAL

**Decide the three split masters from the rewrite side.** Their frame is now
measured empty. Price the ideal form, written fresh today at the consumer's
frame, and compare it with a repair in place. **Do not build either.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, clean at
`608570f` except `dev/PLAN.md`. HEAD is green. **A sibling agent holds the
other Agda slot.**

## WHAT IS MEASURED, and I re-ran the decisive check myself

**`tmKeyK` is REFUTED.** `[LJ-1.95]` applied it at the K slot's own element
and closed with the delivered `∈-irrefl`
(`src/V/Hierarchy.lagda.md:154-155`). I re-ran `src/ProbeLJ195A.agda`: exit
0, 1.62 s, load 3.34.

**All three split masters state it**: `src/L/Condensation/LowerAgree.lagda.md:98`,
`src/L/Condensation/UpperAgree.lagda.md:88`,
`src/L/Condensation/TwelveAgree.lagda.md:96`. **So all three have an empty
telescope and no instantiation of any of them can exist.**

**`[LJ-1.93]` measured the frames apart** even before that: the composer's
`AbstractFrame` carries 69 hypotheses, the consumer holds a 29-field
`KFacts` (`src/L/Condensation.lagda.md:5734-5770`) plus six site facts, and
**39 of the 69 have no supplier**, machine-checked as 39 unsolved metas.

**Two more hypotheses have the same defect shape and are NOT refuted:**
`valK` (`TwelveAgree.lagda.md:86-88`) and `valK-un` (`:89-91`), both
universal in a variable no premise constrains.

**The association bridge is fine and green.** The twelve conjuncts match
index for index, and `[LJ-1.93]`'s `AssocBridge` is generic
(`src/ProbeLJ193A.agda:57-97`). **That work survives whatever you rule.**

## THE QUESTION, and DD13 says ask it from this side

**"We already paid for it" decides nothing, in either direction.**

1. **Price the ideal form.** The three masters restated at the frame the
   consumer actually holds: the 29-field `KFacts` and the six site facts
   (`codesK` `:6492`, `unCodesK` `:6497`, `closedEntryK` `:6501`,
   `domEntryK` `:6504`, `domK` `:6507`, `witK` `:6509`). **In in-fence
   lines, with the basis named.**
2. **Price the repair in place.** For each of `tmKeyK`, `valK` and
   `valK-un`, find **every use inside the three masters' proof bodies** and
   say what the use actually needs. **`KFacts` already carries a conditional
   closure fact, `carrierK` (`src/L/Condensation.lagda.md:5767-5768`). Say
   whether the uses can be served by it or by `arityK` (`:5769-5770`) with a
   premise available at the site.** That is the measurement that prices the
   repair.
3. **Say which is cheaper and why**, in lines and in risk.
4. **Name the widest unmeasured term in whichever you recommend, and the
   probe that would measure it.** DD8's other half.

**This is a recon and pricing task. Do not repair, do not rewrite, do not
delete.**

## THE ABORT CRITERION, fixed in advance per D-1

- **Both forms price**: report both, recommend one, name the widest
  unmeasured term, and STOP.
- **The ideal form cannot be stated at the consumer's frame**: STOP and say
  exactly which content has no home there. **That would mean the consumer's
  own frame is short of facts, which is a finding about the consumer and not
  about the split.**
- **Anything walls**: STOP, report the wall with its seconds.

**You may write `src/ProbeLJ196*.agda` to price one step. Do not touch a
master.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. If a
check does not return, KILL IT before you start another, and report the wall
with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not delete anything.** Retired code is archived, never deleted, and
  that is the owner's call and not yours.
- **Do not repair a hypothesis by weakening the theorem it serves.** Say
  what the theorem would then state.
- **Do not treat the heap wall as gone.** The split exists because the
  twelve-row composition heap-walled in one process at nine rows. **Any
  ideal form you price must still check inside the cap, and you must say how
  it does.**
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

**`[LJ-1.93]` gave the sharpest reading of DD4 this phase: sharing is only
free when the shared frame is the frame the consumer actually holds.**
Answer DD4 with that in mind, and say what frame the ideal form should be
generic in.

## ARCHIVE (DD18)

- **`_build/lj-1.95-report.md`** and **`src/ProbeLJ195A.agda`**, read WHOLE.
  The refutation.
- **`_build/lj-1.93-report.md`**, read WHOLE, and `src/ProbeLJ193A.agda`,
  `src/ProbeLJ193B.agda`, `src/ProbeLJ193C.agda`. The 69-against-29 table
  and the green association bridge.
- **`_build/lj-1.76-report.md`**, read WHOLE. **It built the three masters
  and it is the only record of why the split was drawn where it was, and of
  the heap wall that forced it.**
- `_build/lj-1.79-report.md` and `_build/lj-1.77-report.md`, the `KFacts`
  repair and the earlier refutation.
- `src/L/Condensation.lagda.md:5734-5770` and `:6476-6696`, the record and
  the consumer.
- `dev/LESSONS.md` **C-38 as extended**, C-35, C-36, D-29, D-30, D-13 if the
  bundle carries it, read WHOLE.
- `dev/ARCHIVE.md`, for what an archival record must contain, in case you
  recommend retirement.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked. Spend nothing.** No source prices our own frame. Say so in one
line.

## SCOPE (read)

`_build/lj-1.76-report.md` FIRST, then
`src/L/Condensation/TwelveAgree.lagda.md:45-243`, then
`src/L/Condensation.lagda.md:6476-6520`.

## SCOPE (write)

`src/ProbeLJ196*.agda` only. Your report is `_build/lj-1.96-report.md`.
**No master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for recon` and `--for rewrite`, and read
every statement.

- **D-13, the ideal-form rule.** Price the ideal form first. **A consumer
  does not prove that a chapter must stay.**
- **D-8.** One best-effort figure with its basis named, plus the widest
  unmeasured term and its probe.
- **C-38 as extended.** A closure hypothesis about a bounding set must be
  conditional. **`tmKeyK` is the unconditional shape and it is now
  machine-checked empty.**
- **C-35.** A block with no consumer is UNTESTED.
- **C-36.** Write the term you could not write.
- **D-30.** Price what the CONSUMER needs.
- **P-l.** A price from a comparable elsewhere is a hypothesis.
- **P-i, P-w.** The conversion playbook and the module-application cost.
- **P-h, P-k, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as the bundle gives them.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-10, D-26, D-29.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.96-report.md` incrementally, skeleton first.

**Lead with the recommendation, in one sentence**: rewrite at the consumer's
frame, repair in place, or retire. Then both prices with their bases. Then
the per-use table for `tmKeyK`, `valK` and `valK-un`: what each use needs and
whether `carrierK` or `arityK` serves it. **Mark every negative MEASURED or
INFERRED.** Then the widest unmeasured term and its probe. Then the DD4
answer. Confirm no master was touched.

# LJ-1.158: collapse the `*Agree` telescopes into one record

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**Land `[LJ-1.155]`'s cure.** It is the FIRST cure measured on this wing that
improves the DD24 verdict instead of eroding it.

## WHAT IS MEASURED, and it is a controlled pair

`DeadCode.DeadCodeReachable` is **24,469 ms, 39.7 percent** of the three
`*Agree` masters' 61,633 ms, and the largest phase in all three. In
`L/Condensation` the same phase is 4.4 percent, so it is the TELESCOPE and not
the mathematics.

**A probe restating `UpperAgree`'s 36 telescope hypotheses verbatim, with eight
definitions that do no work, reproduced 72 percent of the master's
`DeadCode` with ZERO mathematics in the file.**

**The cure, measured, two runs each side, warm-up discarded, load 2.8 to 3.1:**
state 35 of the 36 as ONE record. **`DeadCode` 2,652 ms to 25 ms, a factor of
106. The whole file minus 52 percent.**

## WHY THIS ONE IS DIFFERENT, and it is the reason it is funded first

**It is WING-LOCAL and its baseline impact is ZERO.** I verified the cone
myself: `L/Coding/Graph` and `L/Choice/Adequate` are IN the Landmarks cone, and
**all four Condensation masters are OUT of it.**

**`[LJ-1.147]`'s seal cut the denominator and made the ratio WORSE, 1.56x to
1.91x.** This one cannot: it touches nothing the baseline measures.

## THE ONE NAME THAT WALLS, measured in both directions

**`sucV`, inside `sucK`.** As a record field it **exhausts 8 GB in 108 s**.
Remove that one token and the same field costs 2.02 s. Keep only that token and
it walls again.

**So `sucK` stays a telescope hypothesis and 35 of the 36 become the record.**
The master's own comment at `src/L/Condensation/UpperAgree.lagda.md:49-51`
already ruled this on P-x's authority and had no number; `[LJ-1.155]` gave it
one.

**Do not try to put `sucV` in the record. It is measured, twice.**

## THE SHAPE TO USE

**`KFacts`, the record `[LJ-1.62]` delivered and these masters never got.**
`src/L/Condensation.lagda.md:5939-5975`. **Reuse it if it fits; say so if it
does not and what you used instead.**

## WHAT TO DO

1. **Read `[LJ-1.155]`'s report and its probes first.** The generator
   `gen_record_probe.py` takes a field range and an exclusion list.
2. **Collapse `UpperAgree` first**, since that is where the cure was measured,
   and confirm the delta at the MASTER rather than at the probe.
3. **Then `LowerAgree` and `TwelveAgree`.** **`TwelveAgree` carries a
   62-hypothesis telescope and 13,976 of the 24,469 ms, and the collapse was
   measured on `UpperAgree`'s 36 only.** `[LJ-1.155]` named that as its own
   unmeasured term. **Measure it, do not assume it.** P-l.
4. **Typecheck every consumer.** C-40.
5. **Re-measure the wing** with `check-ratio.py`, and report the ratio before
   and after with the run count and the load.

## THE ABORT CRITERION

- **The three masters collapse and the wing improves**: report and STOP.
- **`TwelveAgree` does not behave like `UpperAgree`**: **that is P-l firing and
  it is a real finding.** Report the difference and stop rather than forcing it.
- **A consumer goes RED**: STOP, report it.
- **Anything walls**: STOP, report it with its seconds. **Never raise the cap.**

## WHAT YOU MUST NOT DO

- **Do not put `sucV` in a record.** Measured twice.
- **Do not delete lines to improve a ratio.** DD24's ratio exists so the
  content must be the same KIND of content.
- **Do not touch `src/L/Coding/Graph.lagda.md`.** 21 consumers are green on
  its seal.
- **Do not change what any theorem SAYS.** A collapse is a restatement of
  hypotheses, not a change of content. **If it changes content, stop.**
- **A probe goes in `agents/tasks/LJ-1-158/`**, never in `src/`, tracked.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**A record of frame facts is template content if it names no tower.
`[LJ-1.153]` measured that its own 55 lines of repair were 100 percent
template. Check whether the collapsed record is too, and say so.**

## ARCHIVE (DD18)

**`[LJ-1.157]` measured that 37 of 61 live briefs cite no archive at all, so
this section is real and not a form.**

- **`archive/src/2026-08-09-rud-route/L/LevelFormula.lagda.md`**, which the
  archive grep names for telescope shape. **Say whether the retired route hit
  this class and what it did.**
- **`archive/src/2026-08-06-four-dead-modules/L/Rud/CodePred.lagda.md`** and
  **`archive/src/2026-08-05-realize-cone/L/Rud/Realize.lagda.md`**, the other
  two archived files that carry record-or-telescope shape.
- **Take SHAPE, never a claim.** `[LJ-1.11]` ruled the retired route's
  condensation target classically FALSE.
- `agents/tasks/LJ-1-155/lj-1.155-report.md`, read WHOLE, and its probes.
- `agents/tasks/archive/LJ-1-62/`: where `KFacts` came from.
- **`dev/LESSONS.md` P-x, P-y, P-t, P-l, C-12, C-40**, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature governs a module telescope. Say so in one line.**

## SCOPE (read)

`agents/tasks/LJ-1-155/lj-1.155-report.md` FIRST, then
`src/L/Condensation/UpperAgree.lagda.md`.

## SCOPE (write)

`src/L/Condensation/UpperAgree.lagda.md`, `LowerAgree.lagda.md`,
`TwelveAgree.lagda.md`, and `src/L/Condensation.lagda.md` ONLY if the record
must move there. Your report and probes are `agents/tasks/LJ-1-158/`.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for build` and read every statement.

- **C-40.** Verify the CONSUMERS.
- **P-l.** `TwelveAgree` is not `UpperAgree` until you measure it.
- **P-x, P-y, P-t, P-q, C-12, C-22, C-36, C-38 as extended, C-39.**
- **DD8, D-1, D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-37. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. **Code comments are not prose; write them.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the wing's ratio before and after, with the run count and the
load.** Then each master's delta. Then whether `TwelveAgree` behaved like
`UpperAgree`, MEASURED. Then every consumer's verdict. Then the DD4 answer.
**Mark every negative MEASURED or INFERRED.**

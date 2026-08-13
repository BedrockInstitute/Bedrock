# LJ-1.151: the one term two dispatches named and nobody ran

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**Run the probe that `[LJ-1.146]` and `[LJ-1.144]` independently named as the
widest unmeasured term of the whole GCH wing.** It decides whether the
instantiation side is one shared pattern or twenty-five separate proofs.

**This is the phase's critical path.** `[LJ-1.7]` is STRUCTURE ONLY because
`levelIn` and `cover` are hypotheses; `[LJ-1.8]`, the trophy, needs `[LJ-1.7]`
whole. **Nothing else in LJ-1 is blocked on anything but this.**

## THE PROBE, specified in advance by `[LJ-1.146]` section 4

**The obligation, stated as an obligation and not as an entry point (C-33):
supply ONE member of the 25-fact satisfier-in-K family at a concrete `K`, and
report the line count for THAT ONE FACT.**

- **Candidate**: `valK` (`agents/tasks/LJ-1-113/lj-1.113-report.md` row 4). Its
  missing piece is already named: the graph membership `pr c yc ∈ T`, which
  `binClause-out` binds at `src/L/Coding/Model.lagda.md:911-917` and
  `domEntryK` then closes. **Take any member of the family you find cheaper,
  and say which and why.**
- **Site facts**: the `KFacts` record,
  `src/L/Condensation.lagda.md:5939-5975`, at the stage `[LJ-1.144]` names.
- **Cold check at the C-12 cap.**

## THE ABORT CRITERION, fixed BEFORE you run it (D-1)

- **GO** if the one closure closes **at or below 60 probe lines**. Then the
  shared pattern is real and the 0.35k instantiation band tightens onto the 25.
- **NO-GO** if the site facts do not reach it. Then **the 25 are 25 separate
  proofs**, the band re-opens at the full frame rate, and the whole
  instantiation needs its own chapter price.

**Do not move the criterion after you see a number.** `[LJ-1.60]`'s own row
reads 「NO-GO on a criterion I wrote wrong」 and `[LJ-1.15]` was overturned for
the same reason.

## THE ONE THING THAT WOULD MAKE THIS RETURN WORTHLESS

**Report the line count for the ONE FACT, not for the file.**

**`[LJ-1.124]` was marked MEASURED FALSE on exactly that distinction**
(`agents/tasks/LJ-1-124/lj-1.124-report.md:129-134`). A probe file carries
imports, a module header and setup; **none of that is the fact's price.** Count
the fact, say what you excluded, and give the file total separately.

## WHY IT MATTERS, in the phase's own terms

`[LJ-1.146]` priced `levelIn` and `cover` at about **1.0k lines**, of which
about **0.35k is the instantiation this probe measures**, and the certificate
side already has one probe inside it (`[LJ-1.124]`, 147 lines, GO). **The
instantiation side has NONE.**

**`[LJ-1.144]` named the same term as its own widest, from the other end of the
chain, without having read `[LJ-1.146]`.** Two dispatches, one term, no
measurement.

## THE WALL BEHIND IT, which you are NOT asked to break

**`levelIn`'s deepest step is `π (Lset m') ≡ Lset (π m')`.** `[LJ-1.51]`'s own
section title is 「`levelIn`: the wall, and the term I cannot write」, and
`[LJ-1.121]` reached the same term by a different method and stopped.

**You are NOT funded to break that wall.** You measure the instantiation side,
which is a different term. **If your probe drifts into the wall, say so and
stop: that is a real finding and it would mean the two halves are not
separable.**

## THE ABORT CRITERION, second half

- **GO or NO-GO on the 60-line criterion**: report and STOP.
- **The site facts turn out not to exist**: STOP, name what is missing.
- **The probe cannot be written without the wall**: **STOP AND SAY SO.** That
  changes the phase's price and is the most valuable thing you could return.
- **Anything walls**: STOP, report it with its seconds.

## WHAT YOU MUST NOT DO

- **Do not edit any master.** This is a probe.
- **Do not touch `src/L/Coding/Graph.lagda.md`**: `[LJ-1.147]`'s seal is on it
  and 21 consumers are green.
- **Do not touch `src/L/Condensation/TwelveAgree.lagda.md`**: `[LJ-1.150]` is
  editing it right now.
- **Do not touch `src/ProbeLJ1134A.agda` or `src/ProbeLJ1136*.agda`.**
- **A probe goes in `agents/tasks/LJ-1-151/`**, never in `src/`, tracked, never
  deleted. **Read `AGENTS.md` and `dev/LESSONS.md` D-1 fresh; both changed
  today.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
  `[LJ-1.150]` may be running Agda. **Report the load beside every figure and
  say whether the machine was quiet.** `[LJ-1.146]` refused to run at all
  rather than corrupt a sibling's timing, and that was the right call; **your
  figure is LINES, not seconds, so a busy machine costs you nothing but time.
  Say so.**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.146]` settled the shape: both towers in SHAPE, one tower in INSTANCE,
and the per-tower half is the LARGER half of the bill.** **If your one fact
turns out to be template content, that moves the split and it belongs at the
top of your return.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-146/lj-1.146-report.md`**, read WHOLE, especially
  section 4, which specifies this probe.
- **`agents/tasks/LJ-1-113/lj-1.113-report.md`**, the 28 pieces and row 4.
- **`agents/tasks/LJ-1-124/lj-1.124-report.md:129-134`**, the ONE-fact against
  whole-file distinction that got a figure marked MEASURED FALSE.
- `agents/tasks/LJ-1-144/lj-1.144-report.md:281-294`, the same term from the
  other end.
- `agents/tasks/archive/LJ-1-51/lj-1.51-report.md:135`, the wall.
- **`dev/LESSONS.md` C-33, C-38 as extended, D-1, P-l, C-36**, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`dev/literature/devlin-II5.md`. **`[LJ-1.146]` found `levelIn` and `cover` are
Devlin's content rather than our encoding's. Say whether the 25 closure facts
are his too, or ours.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-146/lj-1.146-report.md` section 4 FIRST, then
`src/L/Condensation.lagda.md:5939-5975`, then
`src/L/Coding/Model.lagda.md:911-917`.

## SCOPE (write)

`agents/tasks/LJ-1-151/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and read every statement.

- **D-1.** The smallest decisive miniature, and the abort criterion fixed
  BEFORE the run.
- **C-33.** State the obligation as an obligation, not as an entry point.
- **C-38 as extended.** An interface nothing instantiates is a restatement.
  **This probe exists to instantiate one.**
- **DD8, P-l, P-x, C-12, C-22, C-36, C-39, C-40.**
- **C-31, C-32, C-34, C-37, D-10, D-26, D-29, D-30. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with GO or NO-GO against the 60-line criterion, and the line count for
the ONE FACT with what you excluded.** Then which family member you took and
why. Then whether the 0.35k band tightens or re-opens. Then whether the wall
came into it. Then the DD4 answer. **Mark every negative MEASURED or
INFERRED.**

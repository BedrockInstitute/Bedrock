# LJ-1.281: probe R-35 against A1's 98 seconds

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **I ran `scripts/dispatch_policy.py` before writing this
line**: `deepseek-subagent-mode` is IN FORCE, clock-selected, OFF-PEAK.

## GOAL

**`[LJ-1.278]` landed `src/L/Cardinal.lagda.md` today and bisected its cost to
ONE term. Measure whether R-35's cure moves it.**

**The bisect, MEASURED, at `agents/tasks/LJ-1-278/lj-1.278-report.md:45-60`:**

| cut | lines | cold s | rate |
|---|---:|---:|---:|
| A1 alone | 108 | **98.24** | 0.91 s/line |
| A3+A4+SiteBound, no A1 | 119 | 2.37 | 0.020 s/line |
| the whole master | 189 | 100.57 | 0.532 s/line |

**A1 alone reproduces 98.24 of the 100.57 seconds. The layout adds nothing;
the cost is content.** C-49 is already answered here, so do not re-answer it.

**THE NAMED CAUSE.** `κ-min-at` runs `leastOf` over `ordSWO (sucV α)`, and
that comparison **unfolds the union representation** `⟪ sucV α ⟫`.
`[LJ-1.236]` section 5 named it and `[LJ-1.232]` measured the same term at the
probe site at about 100.3 s.

**THAT IS R-35'S SHAPE, IN R-35'S OWN WORDS.** Read the full entry:
`dev/LESSONS.md`, `### R-35`. Its rule is to state the membership at the SMALL
INDEX instead, and its measured cure took a file from an OOM crash to 54.6 s
cold.

**NOBODY HAS TESTED THAT CURE AT THIS SITE.**

## PREMISES

- **A1 alone costs 98.24 s cold**, at
  `agents/tasks/LJ-1-278/lj-1.278-report.md:45-52`. **RE-DERIVE IT** before you
  cure anything: a cure is priced against a control you measured yourself.
- **The cost runs through `κ-min-at` unfolding `⟪ sucV α ⟫`**, per
  `agents/tasks/LJ-1-236/lj-1.236-report.md:1`. **This is the load-bearing
  premise. If the term is somewhere else, the cure is aimed at nothing.**
  **Localize it yourself, with `--profile=internal` or by bisection.**
- **`orderAt` is opaque and that is WHY A3 and A4 escape**, at
  `src/L/Choice/Step.lagda.md:740-743`. **If that is right, opacity is itself a
  candidate cure and it is already in the tree.**
- **R-35's cure is MEASURED at a different site**, `dev/LESSONS.md` R-35.
  **P-l: a cure measured at one site is a HYPOTHESIS at another.** **You are
  the measurement that turns it into a price or kills it.**

## THIS IS A PROBE. LAND NOTHING.

**Write your probe in `agents/tasks/LJ-1-281/` and run it there.** **`src/` is
forbidden** (I-5), and `scripts/check-probes.py` enforces it.

**Do not edit `src/L/Cardinal.lagda.md`.** **It landed four hours ago and it is
green.** **COPY what you need.**

## THE THREE THINGS TO BRING BACK

**1. THE CONTROL, MEASURED BY YOU.** A1 alone, cold, at least three kept runs,
with the load beside each. **Report it BEFORE any treated arm**
(`[LJ-1.215]`'s law).

**2. THE LOCALIZATION.** **Which term carries the 98 seconds?** **Name it at
`file:line` and say how you found it.** **P-t: an average hides the term.**

**3. THE TREATED ARM, or the reason there is none.** **Apply R-35's cure: state
the membership at the small index.** **Report the elapsed seconds beside the
control, in a within-series paired design with the order reversed between
cycles.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE CURE WORKS.** Report both arms and the delta. **Then a build brief is
  writable and the wing gets 98 seconds back.** STOP.
- **THE CURE DOES NOT APPLY.** **Say why, at `file:line`.** **R-35 is about
  index or path extraction from a union representation; if `κ-min-at` does
  something else, name what it does.** **A law that does not fit is a real
  answer and it stops the next agent wasting the same hour.**
- **THE CURE APPLIES AND DOES NOT HELP.** **That is the most valuable negative
  here.** **Report the figures and mark it MEASURED.** **C-36: a failed
  substitution is not a proof of impossibility, so say what you could not
  write.**
- **THE CHEAPER CURE IS OPACITY.** **`orderAt` is already opaque and A3 and A4
  escape because of it.** **If making something opaque moves the 98 seconds,
  that is a smaller change than restating a membership, and I want to hear it
  first.**
- **A WALL.** **A1 alone is 98 s, so a bisect series costs real minutes.**
  **A single `agda` invocation past 30 MINUTES is a wall**: interrupt, report
  the ELAPSED SECONDS, bisect. **Report a heap exhaustion as a wall. NEVER
  raise the cap.**

## WHAT YOU MUST NOT DO

- **LAND NOTHING.** **No master, no `src/`, no `dev/ledger.toml`, no
  `dev/PLAN.md`.** **Never `src/Everything.lagda.md`.**
- **Do not touch `agents/tasks/LJ-1-280/`.** **A SIBLING IS LIVE THERE**,
  landing A7 into `src/L/GCH.lagda.md`. **Your territory is
  `agents/tasks/LJ-1-281/` only.**
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the load beside every absolute figure**, discard a warm-up, take at least
  three kept runs per arm.
- **Create your report file in your FIRST five minutes (C-22).**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE RULES THIS CHAIN EARNED

**P-l, AND IT IS THE CENTRE.** **A cure measured at one site is a HYPOTHESIS at
another.** **R-35's 54.6 s is another file's number.**

**P-t. An average hides the term.** **98.24 s over 108 lines is an average.
WHICH lines?**

**P-m. The check-cost rate is a content-class certificate, and instantiation is
the expensive class.** **A1 is the ambient face; A3 and A4 are internal. That
split is the certificate.**

**C-49, written yesterday.** **A rate can be a property of the LAYOUT.**
**`[LJ-1.278]` already ruled that out here by bisection, so your job is the
CONTENT question.**

**C-36. A failed substitution is not a proof of impossibility.**

**C-44. A brief's claim is unchecked until you check it.** **Every figure above
is `[LJ-1.278]`'s and I audited none of them.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.227]` measured A1 PER-TOWER on the Def-against-J axis.** **So its 98
seconds are paid ONCE on that axis today and would be paid TWICE if the J tower
ever builds its own A1.** **Say whether the cure, if it works, is generic
enough that the J tower would inherit it.**

**NAME YOUR AXIS** (C-46). **`[LJ-1.272]` measured that 12 of 62 DD4 figures in
this phase name no axis, and that DD4's own axis is AC-against-GCH, fixed at
`scripts/ledger.py:50`.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-278/lj-1.278-report.md`, sections 0 and 1, read WHOLE.**
  **The bisect and the control.**
- **`agents/tasks/LJ-1-236/lj-1.236-report.md` section 5**: the named cause.
- **`agents/tasks/LJ-1-232/lj-1.232-report.md:51`**: the same term measured at
  the probe site, about 100.3 s. **Two independent measurements of one term.**
- **`dev/LESSONS.md` `### R-35`, read the FULL entry**, including the appended
  GLp probe note, which records three cures that FAILED.
- **`src/L/Choice/Step.lagda.md:740-743`**: the opacity that A3 and A4 escape
  through.
- **`archive/dev/TASKS-archived.md`.** **R-35 was learned on the retired route,
  so the archive holds its original site. Take SHAPE from the archive, never a
  claim**, and say what does not transfer.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**Nothing in the literature governs elaboration cost. Say so in one line.**
Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-278/lj-1.278-report.md` FIRST, sections 0 and 1.

## SCOPE (write)

`agents/tasks/LJ-1-281/` only. **No master, no `src/`, no ledger, no plan.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and read every statement.
**The tool prints `Full entry: dev/LESSONS.md:<line>` for every rule and says
THIS IS AN EXCERPT when it truncated. OPEN the full entry for any law you act
on.**

- **D-1.** The abort criterion is fixed above.
- **R-35.** **The law under test. Read the WHOLE entry.**
- **P-l.** A cure measured at one site is a hypothesis at another.
- **P-t.** An average hides the term.
- **P-m.** The check-cost rate is a content-class certificate.
- **P-q.** A line lever and a seconds lever are different levers.
- **R-40.** A deep successor-chain membership witness normalizes
  super-linearly. **`sucV α` is a successor.**
- **P-h, P-i, P-k, P-n, P-s, P-y, R-34, R-38. C-12, C-22, C-32, C-36, C-39,
  C-40, C-42, C-44, C-45, C-49. I-5. DD0, DD8, DD24, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `.venv/bin/python scripts/lint-prose.py --check` and
  `.venv/bin/python scripts/lint-agda.py --check` on what you write.
- DD23 freezes mathematical prose.
- **No em dash in any language.** Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the control's elapsed seconds MEASURED BY YOU, then the localized
term at `file:line`, then the treated arm or the reason there is none.** Then
each premise above marked VERIFIED or REFUTED. Then whether opacity is the
cheaper cure. Then what a build brief would have to say. Then the DD4 answer
with its axis. **Mark every negative MEASURED or INFERRED.**

# LJ-1.287: cure `sucV∈`, which is 99.2 percent of the wing's most expensive master

tier: opus (in-harness-subagent-mode), model `opus`. I ran scripts/dispatch_policy.py before dispatching: in-harness-subagent-mode is IN FORCE, clock-selected, PEAK, Beijing window 14:00 to 18:00.

## GOAL

`src/L/Coding/EnvSupply.lagda.md` is 833 lines and 482.73 s, the most expensive master in the wing, landed today by [LJ-1.276]. [LJ-1.283] profiled it and the answer is brutally narrow.

**One `agda --profile=definitions` run charges 475,710 ms of 479,311 ms, 99.2 percent, to `sucV∈` at src/L/Coding/EnvSupply.lagda.md:223-224. That is TWO LINES.** I verified both lines exist and that the file carries ZERO `opaque` in 833 lines.

    sucV∈ : ⟨ sucV a ∈ Lset (sucIter 4 δ) ⟩
    sucV∈ = union∈Lset-suc δ₃ ⁅ a , ⁅ a ⁆s ⁆ pair∈δ₃

Nothing else in that file matters. Cure this or report that it cannot be cured.

## TWO CURES ARE ALREADY MEASURED VOID. DO NOT REPEAT THEM.

[LJ-1.283], at agents/tasks/LJ-1-283/lj-1.283-report.md:

- **The layer-cap seal**, P-i's shape, on the four `Lset ∘ sucV` layers the declared type exposes: control 482.20 s, treated 481.28 s. **Minus 0.92 s, minus 0.19 percent. VOID**, and inside the content's own 0.9 percent spread.
- **An equation-bridge arm**: 485.80 s, plus 0.75 percent. **VOID.**

C-36: a failed substitution is not a proof of impossibility. But repeating a measured-void arm is waste, so read that report FIRST and build something else.

## PREMISES

- The 99.2 percent charge to `sucV∈` at :223-224. RE-DERIVE IT with your own `agda --profile=definitions` run before curing anything. A 482-second control is expensive, so budget for it and take the profile from the SAME run as your control.
- The two void arms above. VERIFY what each actually changed by reading agents/tasks/LJ-1-283/'s arm files, so you do not rebuild one by accident.
- `union∈Lset-suc` is the supplier and [LJ-1.263] landed it in src/L/Coding/Key.lagda.md:504. Read it. **The cost may be in the SUPPLIER rather than the call**, and nobody has profiled Key.lagda.md.
- R-40 says a deep successor-chain membership witness normalizes super-linearly, and `sucIter 4 δ` is a four-deep successor chain. **R-40's own cure is to climb by small closures.** That law is a candidate and it is not one of the two that failed.
- R-35 says union representations are meta-poisoned and to state the membership at the SMALL INDEX. `union∈Lset-suc` is a union membership. **Also a candidate, also untried here.**

## WHAT TO BRING BACK

1. **YOUR OWN CONTROL AND PROFILE**, from one run, with the load beside it.
2. **THE MECHANISM.** Why do two lines cost 479 seconds? Name the term that normalizes, at file:line. P-t: the average is already broken down; now break down the definition.
3. **ONE TREATED ARM AT LEAST**, in a within-series paired design, order reversed between cycles. Control first, always.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **A CURE WORKS.** Report both arms and the delta. Then a build brief is writable and the wing gets back most of 479 seconds. STOP.
- **THE COST IS IN `union∈Lset-suc`, NOT THE CALL.** Then the cure belongs in src/L/Coding/Key.lagda.md and this task's site is wrong. **Say so and stop.** That is a real finding and it re-aims the work.
- **EVERY CURE FAILS.** Report each MEASURED with its figure. **Then this is a payable floor (P-n) and the project should stop trying**, which is worth knowing after four failed arms rather than forty.
- **THE TWO LINES ARE AVOIDABLE ENTIRELY.** If `sucV∈` can be restated, weakened to what its consumers actually use, or hoisted so it is proved once instead of per-instance, that beats any seal. Check what consumes it first.
- **A WALL.** The control alone is 482 s, so budget minutes per run. **A single agda invocation past 30 MINUTES is a wall**: interrupt, report elapsed seconds, bisect. Report a heap exhaustion as a wall and NEVER raise the cap.

## CONSTRAINTS

- ONE agda process at a time, always `GHCRTS="-A64m -I0 -M8g"`. The cap is C-12's and is NEVER raised. Report the machine load beside every absolute figure, discard a warm-up, take at least three kept cold runs per arm with the interface deleted between them.
- **THIS IS A PROBE. LAND NOTHING.** Write in agents/tasks/LJ-1-287/ and run there. `src/` is forbidden for probes (I-5) and scripts/check-probes.py enforces it. Copy what you need.
- **Do not edit src/L/Coding/EnvSupply.lagda.md or src/L/Coding/Key.lagda.md.** Both are delivered and green.
- Never src/Everything.lagda.md, never dev/ledger.toml, never dev/PLAN.md, never src/L/Choice/Name.lagda.md (DD23 blocks a pending change).
- **A SIBLING IS LIVE in agents/tasks/LJ-1-286/**, editing src/L/GCH.lagda.md. Do not touch either.
- **CHECK YOUR OWN TIMING HARNESS.** [LJ-1.283] found that `time.monotonic()` is process-relative on this machine and its first wall figure read 0.02 s and was void. It used agda's own clock instead. Do the same and say which clock you used.
- Create agents/tasks/LJ-1-287/lj-1.287-report.md in your first five minutes and fill it incrementally (C-22).
- Never commit, never push, never git checkout ., git stash, git reset --hard, git clean. Do not run make check.
- Run `.venv/bin/python scripts/lint-prose.py --check` and `scripts/lint-agda.py --check` on what you write. NO EM DASH in any language. DD23 freezes mathematical prose.
- Evidence is file:line. Write ASD-STE100. Mark every negative MEASURED or INFERRED, in those words.
- Run `.venv/bin/python scripts/rules.py --for probe` and read every statement; open the full entry for any law you act on. R-35, R-40, P-i, P-l, P-m, P-n, P-t, P-y, C-36, C-49, C-50, I-5, D-1, DD8, DD24 all bear. **C-50 was written from this exact finding an hour ago: profile before you cure, and P-y prices a seal's cost while saying nothing about its benefit.**

## DD4

Maximize the code the two proofs share, and write it generic. One rule, two ends, no metric and no checker.

[LJ-1.276] measured this master NEUTRAL on DD4's own AC-against-GCH axis, so its seconds are paid ONCE. [LJ-1.283] measured that it sits in NEITHER trophy closure today. **So a cure here does not move DD4's 41.1 percent figure and must not be justified by it.** Say what the cure does to REUSE rather than to the ratio, and NAME YOUR AXIS (C-46).

## ARCHIVE (DD18)

agents/tasks/LJ-1-283/lj-1.283-report.md read WHOLE, the profile and the two void arms; agents/tasks/LJ-1-283/'s arm files, so you do not rebuild one; agents/tasks/LJ-1-276/lj-1.276-report.md, how the master was landed; agents/tasks/LJ-1-263/lj-1.263-report.md, which landed `union∈Lset-suc`; dev/LESSONS.md R-35, R-40 and P-i as FULL entries; archive/dev/TASKS-archived.md, taking SHAPE and never a claim. Return an ARCHIVE USED section naming ONE line read per archived file.

## LITERATURE (DD18)

Nothing in the literature governs elaboration cost. Say so in one line and return a LITERATURE USED section.

## SCOPE (read)

agents/tasks/LJ-1-283/lj-1.283-report.md FIRST, whole.

## SCOPE (write)

agents/tasks/LJ-1-287/ only.

## RETURN

Lead with your own control and the profile's top charge, then the mechanism at file:line, then the treated arm's delta. Then each premise VERIFIED or REFUTED. Then whether the cost is in the call or the supplier. Then whether `sucV∈` is avoidable entirely. Then which clock you timed with. Then the DD4 answer with its axis. Mark every negative MEASURED or INFERRED.

End your final message with: the control, the best treated time, and whether the site is the call or the supplier.

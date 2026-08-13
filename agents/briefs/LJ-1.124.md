# LJ-1.124: probe the bounded level-graph decode

tier: codex (default)

## GOAL

**Gate the phase's last chapter.** It re-priced from 2.8k lines to 0.6k, and
one term inside it is unmeasured. **Measure that term before the chapter is
funded.** DD8.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`3619ad4`. `make check` passes: I ran it.**

## WHAT IS MEASURED

`[LJ-1.123]` re-priced the level-hood certificate. **The inherited 2.8k to
3.3k figure covered the whole chapter, and seven of its eight components are
now DELIVERED**, because `src/L/Condensation.lagda.md` and
`src/L/BoundedSubset.lagda.md` did not exist when the figure was set and now
carry 6,445 and 1,409 in-fence lines. **The remainder is the transfer into
the hull: four pieces, 0.6k lines, band 0.35 to 0.85k.**

**That pricing rests on READ evidence, not a probe, and the return says so.**

**The widest unmeasured term is the bounded level-graph decode, MEASURED by
`rg` over `src/`:**

- `StepB`, `ApproxB` and `GraphB` are delivered with their Δ₀ witnesses
  (`src/L/Condensation.lagda.md:2410-2493`). **No master decodes them.**
- `graphBndAt` has **no two-way lemma** against `LsetGraphAt` or against
  `Lset`. `ride-only` and `ride-defines` decode the UNBOUNDED graph only
  (`:419-428`).
- `LevelHood` consumes `GraphB` (`src/L/BoundedSubset.lagda.md:81-109`), and
  **nothing consumes `LevelHood`.**

**Verify each of those in the source. The master moved three times today.**

## WHAT TO PROBE

**The two-way decode of `graphBndAt` at the class carrier**, under the
`KFacts` site facts (`src/L/Condensation.lagda.md:5939-5975`, VERIFY the
range).

- One direction **reads the level from the satisfied matrix**.
- The other **writes the matrix from the level**.

**GO if both directions close at or below 150 probe lines.** Report the
lines and the seconds either way.

**The decode is the load-bearing step of all three remaining facts**
(`hullLevel`, `piFixesLevel`, `CoverTransfer`). `[LJ-1.123]` says that with
it, the rest is a composition of delivered agreements: `LeafAgree`
(`src/L/Condensation.lagda.md:7000-7033`) and the step and approximation
decodes (`src/L/Coding/Sequence.lagda.md:217-301`). **Check that claim while
you are in there, and say whether it holds.**

## THE RULE ON HYPOTHESES, stated as a test and not as a shape

**If you leave a hypothesis standing, name what supplies it at `file:line`
and TRY TO REFUTE IT.** `src/ProbeLJ197A.agda` is the shape, and
`scripts/check-unbound-hyp.py` will tell you which of your own statements
are worth attacking. **Run it on your probe.**

## THE ABORT CRITERION

- **Both directions close**: report the terms, lines and seconds, then the
  re-priced remainder. STOP. **Do not build the chapter.**
- **One direction closes and the other does not**: report both, with the
  term you could not write. **That is a good return and it halves the
  unknown.**
- **Neither closes**: report what the decode would need. **Then the 0.6k
  figure is not safe and I need to know that before funding it.**
- **Anything walls**: STOP, report the wall with its seconds.

**Do not stop at the first negative.**

**Work in `src/ProbeLJ1124*.agda`, never `.lagda.md`.** Do not edit any
master.

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time. `GHCRTS` is set in your environment by the
dispatcher; if `env | grep GHCRTS` shows nothing, pass
`GHCRTS="-A64m -I0 -M8g"` yourself and SAY SO in the report. Never raise
it.**

## WHAT YOU MUST NOT DO

- **Do not edit any master.**
- **Do not weaken the decode's statement to make it close.** If it needs
  something, name it.
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers from the source, never from a report.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**Say whether the decode is tower-free**, as `[LJ-1.120]` found the
environment-set to be. **If it is, the J tower inherits the whole chapter.**

## ARCHIVE (DD18)

- **`_build/lj-1.123-report.md`**, read WHOLE. **Its section 3 names this
  probe and its GO line. Its section 2 is the assembly you are checking.**
- `_build/lj-1.121-report.md` and `src/ProbeLJ1121A.agda`, the three facts
  and the reduction.
- `_build/lj-1.12-report.md`, the inherited figure, for what it covered.
- **`src/L/Condensation.lagda.md:2410-2493`** and **`:400-430`**, the
  matrices and the unbounded decodes.
- **`src/L/BoundedSubset.lagda.md:81-109`**, `LevelHood`.
- `src/L/Coding/Sequence.lagda.md:217-301`, the delivered step and
  approximation decodes.
- `dev/LESSONS.md` **D-1, D-8, D-30, P-l, C-36, C-38 as extended, C-39**,
  read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked. Spend nothing.** `[LJ-1.123]` settled how Devlin proves 5.2 part
(i). Say so in one line.

## SCOPE (read)

`_build/lj-1.123-report.md` section 3 FIRST, then
`src/L/Condensation.lagda.md:2410-2493`, then
`src/L/BoundedSubset.lagda.md:81-109`.

## SCOPE (write)

`src/ProbeLJ1124*.agda` only. Your report is `_build/lj-1.124-report.md`.
**No master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for probe`, and read every
statement.

- **D-1.** The smallest decisive miniature, then throw it away.
- **D-8.** Gate a block before funding it. **This brief IS the gate.**
- **P-l.** A price from a comparable elsewhere is a hypothesis. **Three
  inherited figures came in low this session; do not inherit the fourth.**
- **C-36.** Write the term you could not write.
- **C-38 as extended, C-35, C-39, C-40, D-10, D-29, D-30.**
- **P-m, P-x, P-i, P-w, P-h, P-k, P-n, P-o, P-q, P-t, P-u, P-v** as the
  bundle gives them.
- **P-c, R-36, R-38, R-35, R-40.**
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-26.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- **Run `scripts/check-unbound-hyp.py` on your probe.**
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.124-report.md` incrementally, skeleton first.

**Lead with GO or NO-GO on the 150-line gate**, with both directions' terms
at `file:line`, their lines and their seconds. Then whether the assembly
claim of `[LJ-1.123]` section 2 holds. Then the re-priced remainder. Then
whether `GHCRTS` was in your environment. Then the C-39 section. **Mark
every negative MEASURED or INFERRED.** Then the DD4 answer.

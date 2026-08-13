# LJ-1.123: re-price the level-hood certificate, the phase's last wall

tier: codex (default)

## GOAL

**Price the chapter the phase now stands on.** `levelIn` and `cover` are
true and unsupplied, and the wall behind them is one named chapter. **Its
price is inherited, not measured. Measure it.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, clean at
`65a48d1`. `make check` passes. **A sibling agent is editing
`src/L/Coding/EnvSet.lagda.md` and `src/L/Coding/Sound.lagda.md`. Do not
touch either.**

## THIS DISPATCH RUNS UNDER A TRIAL HARNESS

**You were started inside a herdr pane rather than by the usual dispatcher.**
That changes two things for you and nothing else:

- **`GHCRTS` is NOT set in your environment.** The usual dispatcher exports
  it. **You must pass the cap yourself on every Agda call:**
  `GHCRTS="-A64m -I0 -M8g" agda <file>`. **C-12: never raise it.**
- **Your stdout is a terminal, not a log file.** Write your findings to the
  report file as you go, per C-22. **Nothing else captures them.**

## WHAT IS MEASURED

`[LJ-1.121]`: **neither `levelIn` nor `cover` is refutable, and neither is
supplied.** `scripts/check-unbound-hyp.py` is clean on both, and
`src/ProbeLJ1121A.agda` (GREEN, I re-ran it) machine-checks the reduction:

- **`levelIn` closes exactly modulo `hullLevel` and `piFixesLevel`.**
- **`cover` needs `CoverTransfer`, the covering direction**, and a grep finds
  only `Hull⊆L`, which is the wrong direction.

**The wall is the `[LJ-1.12]` crossing, the level-hood certificate, priced
2.8k to 3.3k lines and not built.**

**That figure is INHERITED from `[LJ-1.12]` and this dispatch exists because
nobody has re-measured it since.** Two prices this session came in under
their inherited estimates: the `absorbs-subset` site block at 13 lines
against 20 to 30, and `Init κ`'s successor closure inside its band.

## WHAT TO DO

1. **Read `[LJ-1.12]`'s report and say what its 2.8k to 3.3k figure
   covered**, at `file:line`. **Was it this certificate alone, or a chapter
   that has since been partly delivered?**
2. **Say what `levelIn` and `cover` actually need**, minimally: `hullLevel`,
   `piFixesLevel`, `CoverTransfer`. **For each, state whether the delivered
   tree has it, has half of it, or has nothing**, at `file:line`.
3. **Re-price the remainder.** One best-effort figure with its basis named,
   plus the widest unmeasured term and the probe that would measure it. DD8.
4. **Say whether the price fell**, and if so where the delivered content came
   from. **A chapter that shrank because the tree grew under it is the most
   useful thing you can report.**

**This is a recon and pricing task. Do not build the chapter. You may write
one small probe to price a step.**

## THE RULE ON HYPOTHESES, stated as a test and not as a shape

**If you name a fact the chapter needs, say what would supply it at
`file:line`, and try to refute it.** `src/ProbeLJ197A.agda` is the shape.
**Seven hypotheses of this layer were empty types.**

## THE ABORT CRITERION

- **The chapter prices**: report the figure, its basis, and the widest
  unmeasured term. Then STOP.
- **Part of it is already delivered**: report which part and at
  `file:line`. **That is the best outcome.**
- **A needed fact is refutable**: STOP and report it.
- **Anything walls**: STOP, report the wall with its seconds.

**Do not stop at the first negative.**

**Probes are `src/ProbeLJ1123*.agda`, never `.lagda.md`.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot.
Pass `GHCRTS="-A64m -I0 -M8g"` yourself. If a check does not return, KILL IT
before you start another, and report the wall with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not edit any master.**
- **Do not touch `src/L/Coding/`**, where a sibling works.
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers and figures from the source, never from a report.**
  **`[LJ-1.121]` corrected one of my readings by doing exactly that.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**The collapse and the hull are about well-orders and transitivity, not
about definability.** Say whether the certificate is tower-free, as
`[LJ-1.120]` found the environment-set to be.

## ARCHIVE (DD18)

- **`_build/lj-1.121-report.md`**, read WHOLE, and **`src/ProbeLJ1121A.agda`**.
  **The reduction and the three missing facts. Your starting material.**
- **The `[LJ-1.12]` report in `_build/`**, read WHOLE. **Its figure is what
  you are re-measuring.**
- `_build/lj-1.119-report.md`, the site entry that reaches these two.
- **`src/L/BoundedSubset.lagda.md:890-1050`** and **`:1400-1440`**, the
  `Condense` and `HullStage` modules.
- `src/V/Collapse.lagda.md`, the delivered Mostowski collapse.
- `dev/LESSONS.md` **D-8, D-30, P-l, C-36, C-38 as extended, C-39**, read
  WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Devlin's 5.2 part (i) is these two halves**, per `[LJ-1.121]`. **Say in
three lines how Devlin proves them**, from `dev/literature/devlin-II5.md`.
**Spend a little here: a source can settle the shape of this chapter
cheaply.**

## SCOPE (read)

`_build/lj-1.121-report.md` FIRST, then the `[LJ-1.12]` report, then
`src/L/BoundedSubset.lagda.md:890-1050`.

## SCOPE (write)

`src/ProbeLJ1123*.agda` only. Your report is `_build/lj-1.123-report.md`.
**No master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for recon` and `--for probe`, and read every
statement.

- **D-8.** Gate a block before funding it. **This brief IS the gate.**
- **D-30.** Price what the CONSUMER needs. **The consumer needs `levelIn`
  and `cover` at ONE site, not a general chapter. Check whether the site
  narrows it.**
- **P-l.** A price from a comparable elsewhere is a hypothesis. **The 2.8k
  figure is one.**
- **C-36, C-38 as extended, C-35, D-10, D-29.**
- **C-39.** A brief's prohibition binds harder than its goal. **If a line of
  this brief blocks a route you can see, say so in the report and name the
  route. That is a required section, not a courtesy.**
- **P-m, P-x, P-i, P-w, P-h, P-k, P-n, P-o, P-q, P-t, P-u, P-v** as the
  bundle gives them.
- **P-c, R-36, R-38, R-35, R-40.**
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally. **Your stdout is not
  captured, so the report file is the only record.**
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-26.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- **Run `scripts/check-unbound-hyp.py`** on anything you write.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.123-report.md` incrementally, skeleton first.

**Lead with the re-priced figure and its basis**, with the inherited 2.8k to
3.3k beside it. Then the three facts, each with delivered, half-delivered or
nothing, at `file:line`. Then the widest unmeasured term and its probe. Then
whether the site narrows the need. Then how Devlin proves it. Then the C-39
section. **Mark every negative MEASURED or INFERRED.** Then the DD4 answer.

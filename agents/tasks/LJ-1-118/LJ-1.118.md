# LJ-1.118: enter Devlin55 at the site

tier: codex (default)

## GOAL

**Instantiate `Devlin55`.** Its first parameter is now suppliable at the
site. **Supply the second, and enter the module that holds the wing's main
theorem.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`3757eeb`. `make check` passes: I ran it.** A sibling agent works on the
coding side in probes only. **Do not touch `src/L/Condensation*`.**

## WHAT IS MEASURED

`[LJ-1.117]`: **`sq` is restricted to `δ ≤ α₀`** and `L.StageCardinal` takes
the site ordinal as a parameter (`src/L/StageCardinal.lagda.md:15-19`).
**At `α₀ = ω` the honest ℕ pairing supplies it**, built not assumed, and the
restricted module, its `stage-card-upper` and the `CodeCount`-side count all
check at the site (`src/ProbeLJ1117A.agda`). **All three consumers green,
`make check` passes.**

`[LJ-1.103]`: **`absorbs-subset` was REFUTED as stated and is repaired.** It
now carries the premise `α ∉ ω` (`src/L/BoundedSubset.lagda.md`, find it by
name). **The site instance was priced at 20 to 30 lines**
(`_build/lj-1.101-report.md` section 2.3): at `α = ω` and `x = ∅`,
`∅ ∈ Lset ω` (`∅∈𝒟ₒ`, `src/L/Axioms/Basic.lagda.md:490-491`, climbed by
`Lset-in`), so `Lset ω ∪ ⁅ ∅ ⁆s ≡ Lset ω` and the injection is the identity
on presentations. **That price is INFERRED. Measure it.**

`[LJ-1.94]`: the site is `κ` the Hartogs cardinal, `α = ω`, `x = ∅`, and
**all fifteen values of the `BoundedSubsetAt` telescope are supplied**
(`src/ProbeLJ194A.agda:1189-1233`). `[LJ-1.101]`: **`cardκ` typechecks at
the master's own `IsCardinal`.**

**So `Devlin55` has never been entered, and every reason not to is gone
except this one parameter.**

## WHAT TO BUILD

1. **Supply `absorbs-subset` at the site**, in the repaired form. **Read its
   current type in the source.**
2. **Instantiate `Devlin55`** with both parameters, in a probe.
3. **Then enter `BoundedSubsetAt` inside it**, with the `[LJ-1.94]` site
   values. **Report the first hypothesis nothing can supply**, at
   `file:line`. `[LJ-1.90]` did this before `Devlin55` could be entered and
   found `cardκ`; **this is the same test one module deeper.**
4. **Force the body to elaborate, not only the telescope.** `[LJ-1.112]`'s
   `consume-out = F.out` is the pattern: name a value from inside the
   module and let it check.

**`levelIn` and `cover` (`src/L/BoundedSubset.lagda.md`, find by name) are
undischarged hypotheses of the layer. If the entry reaches them, say so and
STOP: they are a separate dispatch.**

## THE RULE ON HYPOTHESES, stated as a test and not as a shape

**Every hypothesis you supply must receive a VALUE, not another parameter.**
C-38. **Say for each whether it is supplied or restated, in those words.**

**Try to refute anything you add**, and **run
`scripts/check-unbound-hyp.py` on your probe**.

## THE ABORT CRITERION

- **`Devlin55` is entered and `BoundedSubsetAt` reaches a hypothesis nothing
  supplies**: report how far it reached, hypothesis by hypothesis, and the
  first blocker at `file:line`. Then STOP. **That is the deliverable and it
  is what `[LJ-1.90]` was for one level up.**
- **`absorbs-subset` cannot be supplied at the site**: STOP, write the term
  you could not write, and say what the tree would have to provide. **The
  20 to 30 line price is inferred and may be wrong.**
- **Anything walls**: STOP, report the wall with its seconds.

**Do not stop at the first negative. Report how far you reached.**

**Work in `src/ProbeLJ1118*.agda`. Do not touch any master.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. If a
check does not return, KILL IT before you start another, and report the wall
with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not weaken any hypothesis to make it suppliable.** If it cannot be
  supplied, that is the finding.
- **Do not add a hypothesis to the site.** A site that assumes what it
  should supply has moved the obligation, not discharged it.
- **Do not write a probe as `.lagda.md`.** `[LJ-1.113]` did, and
  `check-fences` counted five probes as masters, 87 becoming 92. **Probes
  are `src/ProbeLJ1118*.agda`.**
- **Do not touch `src/L/Condensation*`, `src/L/Coding/` or `src/V/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers and types from the source, never from a report.**
  **Two masters moved an hour ago.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**Say whether the entry is generic in the site**, so the J tower enters its
own the same way.

## ARCHIVE (DD18)

- **`_build/lj-1.117-report.md`**, read WHOLE, and **`src/ProbeLJ1117A.agda`**.
  **The restricted module and the site supply. This is your starting
  material.**
- **`_build/lj-1.94-report.md`** and **`src/ProbeLJ194A.agda`**, read the
  site block. **The fifteen values.**
- `_build/lj-1.101-report.md` section 2.3, the `absorbs-subset` price, and
  `src/ProbeLJ1101A.agda` for the `cardκ` supply at the master's type.
- `_build/lj-1.103-report.md`, the repair and why `ω ∈ α` was too strong.
- `_build/lj-1.90-report.md`, the earlier entry attempt one level up.
- **`src/L/BoundedSubset.lagda.md:1361-1627`**, `Devlin55` whole.
- `src/L/Axioms/Basic.lagda.md:485-495`, the empty set in a stage.
- `dev/LESSONS.md` **C-38 as extended, C-39, C-40, P-x**, C-35, C-36, D-8,
  D-30, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked. Spend nothing.** Say so in one line.

## SCOPE (read)

`src/ProbeLJ1117A.agda` FIRST, then `src/L/BoundedSubset.lagda.md`'s
`Devlin55` telescope and `BoundedSubsetAt`, then
`src/ProbeLJ194A.agda:1180-1240`.

## SCOPE (write)

`src/ProbeLJ1118*.agda` only. Your report is `_build/lj-1.118-report.md`.
**No master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it. **This dispatch is the supply site.**
- **C-35.** A block with no consumer is UNTESTED. **You are the consumer.**
- **C-36.** Write the term you could not write.
- **C-39.** A brief's prohibition binds harder than its goal. **If a line of
  this brief blocks a route you can see, say so in the report and name the
  route. That is a required section, not a courtesy.**
- **C-40, D-8, D-30, D-10, D-29.**
- **P-l.** A price from a comparable elsewhere is a hypothesis. **The 20 to
  30 line figure is one.**
- **P-x, P-i, P-w, P-h, P-k, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as the
  bundle gives them.
- **P-c, R-36, R-38, R-35, R-40.**
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-26.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- **Run `scripts/check-unbound-hyp.py` on your probe** and report what it
  says.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.118-report.md` incrementally, skeleton first.

**Lead with whether `Devlin55` is entered**, YES or NO, with the term at
`file:line` and its seconds. Then `absorbs-subset`'s supply, and its
measured line count against the inferred 20 to 30. Then how far
`BoundedSubsetAt` reached, hypothesis by hypothesis, and the first blocker.
Then the C-39 section. **Mark every negative MEASURED or INFERRED.** Then
the DD4 answer.

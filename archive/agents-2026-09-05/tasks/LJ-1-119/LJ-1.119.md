# LJ-1.119: restrict absorbs-subset the way sq was restricted

tier: codex (default)

## GOAL

**Apply LJ-1.117's move one parameter over.** The site value of
`absorbs-subset` is built and green. The module still demands the whole
function. **Move the hypothesis to where the consumer names its arguments.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`079c04e`. `make check` passes.** A sibling agent works on the coding side
in probes only. **Do not touch `src/L/Condensation*`.**

## WHAT IS MEASURED

`[LJ-1.118]` supplied the site instance and could not enter the module.

- **The site value is BUILT and GREEN**: `Site.site-inj :
  ⟪ Lset ω ∪ ⁅ ∅ ⁆s ⟫ ↪ ⟪ Lset ω ⟫` at `src/ProbeLJ1118A.agda:153-154`,
  3.14 s. **13 code lines against the inferred 20 to 30. MEASURED.**
- **The module parameter is the whole function**
  (`src/L/BoundedSubset.lagda.md:1363-1365`), and **its `x ∉ Lset α` branch
  cannot be written from the delivered tree.** Two routes to it exist and
  both are blocked: an injection out of the union presentation, the R-35
  class `[LJ-1.101]` named as its widest unmeasured term; or a shift of the
  stage presentation, which reduces to `stage-card-upper` at `α` and
  therefore to the `[LJ-1.107]` and `[LJ-1.114]` wall.
- **The LEM case split is not the blocker**: `Split` and `AbsorbsTotal`
  (`src/ProbeLJ1118A.agda:163-183`) machine-check that the parameter is the
  pair of its two branches, **with the out-branch as exactly one
  parameter.**

**So the hypothesis is stated more generally than the consumer uses it, and
that is the same defect `[LJ-1.117]` cured for `sq`.**

## WHAT TO BUILD

1. **Find where `Devlin55`'s body applies `absorbs-subset`.** `[LJ-1.101]`
   put it at `code-inj` inside `BoundedSubsetAt`; **verify in the source,
   the master moved twice today.**
2. **Move the hypothesis to the module that NAMES its arguments.** If the
   body applies it only at `BoundedSubsetAt`'s own `α` and `x`, the
   hypothesis belongs in that telescope at those arguments, not in
   `Devlin55`'s at all of them. **`[LJ-1.117]` did exactly this for `sq` by
   making the site ordinal a module parameter; read how.**
3. **Then enter `Devlin55` and `BoundedSubsetAt` at the site**, and report
   the first hypothesis nothing supplies. **That was `[LJ-1.118]`'s goal and
   it is still the deliverable.**
4. **Force the body to elaborate**, not only the telescope.
5. **Every master you touch is GREEN when you finish, or you revert all of
   them and say so.**

## C-40

**After you change `BoundedSubset`'s telescope, check every master that
imports it and name them at `file:line` with their results.**
`git grep -l BoundedSubset src/` is the list. `[LJ-1.117]`'s C-40 section is
the shape: three files, each with its seconds, and a statement that the list
is complete. **Do NOT run `make check`; I run it.**

## THE RULE ON HYPOTHESES, stated as a test and not as a shape

**Do not weaken a conclusion to make a hypothesis fit.** Only the
hypothesis's domain moves. **`Devlin55.theorem`'s statement must stay
byte-identical**, as it did at `[LJ-1.117]`.

**Every hypothesis you supply must receive a VALUE, not another parameter.**
C-38.

**Run `scripts/check-unbound-hyp.py` on your probe.**

## THE ABORT CRITERION

- **The restriction lands and `BoundedSubsetAt` is entered**: report how far
  it reached, hypothesis by hypothesis, the first blocker at `file:line`,
  and the consumers you checked. Then STOP.
- **The body applies `absorbs-subset` at an argument the restriction
  excludes**: STOP, name it at `file:line`, and say what the narrowest
  workable restriction is.
- **The entry reaches `levelIn` or `cover`**: **that is a good stop.** Report
  it; they are a separate dispatch.
- **Anything walls**: STOP, report the wall with its seconds.

**Do not stop at the first negative. Report how far you reached.**

**Work in `src/ProbeLJ1119*.agda` for anything exploratory. Probes are
`.agda`, never `.lagda.md`: `[LJ-1.113]` made five probes count as masters.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. If a
check does not return, KILL IT before you start another, and report the wall
with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not assume the axiom of choice.**
- **Do not re-attempt the union-presentation injection or the stage shift.**
  `[LJ-1.118]` measured both blocked, and the second reduces to a wall
  proved at `[LJ-1.114]`.
- **Do not touch `src/L/Condensation*`, `src/L/Coding/` or `src/V/`.**
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

**A restricted hypothesis is a weaker demand on both towers.** Say whether
the J tower inherits the restricted module unchanged.

## ARCHIVE (DD18)

- **`_build/lj-1.118-report.md`**, read WHOLE, and **`src/ProbeLJ1118A.agda`**.
  **The site value, the two blocked routes, and the branch decomposition.
  This is your starting material.**
- **`_build/lj-1.117-report.md`**, read WHOLE, and `src/ProbeLJ1117A.agda`.
  **The move you are repeating, and its C-40 section as the shape.**
- `_build/lj-1.94-report.md` and `src/ProbeLJ194A.agda`, the site values.
- `_build/lj-1.103-report.md`, the `absorbs-subset` repair.
- `_build/lj-1.90-report.md`, the earlier entry attempt.
- **`src/L/BoundedSubset.lagda.md:1361-1627`**, `Devlin55` whole.
- `dev/LESSONS.md` **D-30, C-40, C-39, C-38 as extended**, C-35, C-36, D-8,
  D-10, P-l, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked. Spend nothing.** Say so in one line.

## SCOPE (read)

`src/ProbeLJ1118A.agda` FIRST, then `src/L/BoundedSubset.lagda.md`'s
`Devlin55` telescope and the `code-inj` use, then
`src/ProbeLJ1117A.agda`.

## SCOPE (write)

`src/L/BoundedSubset.lagda.md` and any master its change forces (**all green
at the end, or all reverted**), plus `src/ProbeLJ1119*.agda`. Your report is
`_build/lj-1.119-report.md`. **Never `src/Everything.lagda.md`. Never
`src/L/Condensation*`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for rewrite`, and read
every statement.

- **D-30.** Price what the CONSUMER needs. **This brief IS D-30, for the
  second parameter.**
- **C-40.** Verify the CONSUMERS of a changed master, never the master
  alone.
- **C-39.** A brief's prohibition binds harder than its goal. **If a line of
  this brief blocks a route you can see, say so in the report and name the
  route. That is a required section, not a courtesy.**
- **C-38 as extended, C-35, C-36, D-10, D-29.**
- **P-l.** A price from a comparable elsewhere is a hypothesis. **The site
  block measured 13 lines against an inferred 20 to 30, so the inference was
  high; do not inherit the next one either.**
- **R-35.** The union-presentation class, which is the blocked route.
- **P-x, P-i, P-w, P-h, P-k, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as the
  bundle gives them.
- **P-c, R-36, R-38, R-40.**
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-8, D-26.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`. **I run it on your result.**
- **Run `scripts/check-fences.py --check`** and say the master count. **It
  should be 87.**
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check` on anything you touch.
- DD23 freezes mathematical prose. **Change the code, not the prose, unless
  a sentence becomes false. If one does, say which and leave it.**
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.119-report.md` incrementally, skeleton first.

**Lead with the restriction you landed, quoted, and whether
`BoundedSubsetAt` is entered.** Then how far it reached and the first
blocker. **Then the C-40 section: every consumer you checked, at
`file:line`, and its result.** Then whether any conclusion changed. Then the
C-39 section. **Mark every negative MEASURED or INFERRED.** Then the DD4
answer.

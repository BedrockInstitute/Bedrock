# LJ-1.68: narrow EnvSet to what its consumers reach

tier: codex (default)

## GOAL

A DD25 review found that every failed move so far was the same mechanism,
and named the one class nobody has tried. **Measure that class.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, at `f94a6eb`.
**The working tree carries an uncommitted, GREEN placement**:
`src/L/Condensation.lagda.md` at 6,390 in-fence lines against HEAD's 5,562.
**Do not discard it.**

## THE LAW THAT NOW BINDS YOU, admitted today as P-w

**A module application COPIES its target's definitions; it never references
them.** So interposing a module that RE-EXPORTS its target strictly ADDS one
set of copies and cannot amortize anything. **Only three moves reduce
instantiation cost: (a) fewer applications, (b) fewer definitions copied per
application, (c) cheaper types on the definitions copied.**

Read `dev/LESSONS.md` P-w whole. Its measurement table:

| move | interposes | measured |
|---|---|---:|
| shared frames in the chain wrappers | yes | +17.23 s |
| three depth frames over `EnvSet` | yes | +10.88 s |
| `TwelveAgree.twelveB` aliased | yes | +3.29 s |
| abstract-stack module inside `NegAgree` | yes | +2.82 s |
| `KFacts` bundle, class (c) | no | -30 s |
| `Lift12Back` kit, class (a) | no | 4.28x |
| `StageCardinal` dead cluster, class (a) | no | -9.85 s |

**Four interpositions, four regressions. Three moves in (a) and (c), three
wins. Do not propose a fifth interposition.**

## THE UNTESTED CLASS

`EnvSet` (`src/L/Condensation.lagda.md:2761`) exports about **fifteen**
definitions: `app3`, `app3'`, `app2`, `bnd→over`, `over→bnd`, `out`, `back`,
`memE-bnd`, `memE-at`, `t0eq`, `t1eq`, `t0K`, `keyK`, `num1K` and one more.

**Its eighteen application sites reach exactly three**: `out`, `back` and
`memE-bnd`. I counted this myself across the whole master.

**Each application costs 1.016 s, MEASURED** (`[LJ-1.66]`). Eighteen are
worth 18.29 s against a residual of 2.33 s.

**So: how much of that 1.016 s is definitions nobody reaches?**

## STEP 1, AND IT MAY ANSWER THE WHOLE QUESTION CHEAPLY

**Compute the transitive closure of `{out, back, memE-bnd}` inside
`EnvSet`.** Which of the fifteen are reachable, and which are dead weight at
every site?

**If `out` is defined through `bnd→over` which uses `app3`, those helpers are
reachable and are NOT dead weight.** Report the closure honestly. **If the
closure is all fifteen, say so and STOP: the narrowing class is empty here,
and that is a full deliverable.**

## STEP 2, ONLY IF THE CLOSURE IS PROPER

Split `EnvSet` so the three reached definitions and their closure live in one
module, and the unreachable remainder lives in a second module that the
eighteen sites never apply.

**THE DISCRIMINATOR, and it is what four dispatches got wrong.** The thin
module **MUST NOT APPLY `EnvSet`**, and must not apply anything that applies
it. If your thin module contains `module E = EnvSet ...` inside it, you have
built a fifth interposition, P-w refuses it, and you must stop and say so.
**Class (b) means the sites copy FEWER definitions, not that a smaller
wrapper sits in front of the same copies.**

The eighteen sites then apply the thin module in place of `EnvSet`. Any
consumer that needs a remainder definition applies the second module
explicitly; **I counted zero such consumers, so if you find one, say where.**

**Statements and proofs do not change.** Only where a definition lives.

## THE ABORT CRITERION, fixed in advance per D-1

Measure `L.Condensation` cold, three runs each side, same session, gate
caliber, loads reported beside every figure.

- **Closure is all fifteen**: STOP after step 1. Report it.
- **Saving 1.0 s or more across the eighteen sites**: **GO, then STOP and
  report anyway.** I want this number before anything else is funded.
- **Saving under 1.0 s, or any regression**: STOP and report the price.

**Either way this dispatch ends after at most one build.** Do not touch the
chain, `levelIn` or `cover`.

You need not run `check-ratio --check`. **I run the wing gate myself.**

## SOMETHING YOU SHOULD KNOW, because it changes what a win here means

The residual is 2.33 s, **but closing it does not save the wing.** The
pending wiring is MEASURED at 0.045 to 0.047 s per line
(`_build/lj-1.62-report.md:87-88`), which is 3.6x the bar, so 500 more lines
of it puts the wing about 19 s over on its own. **I did that arithmetic
myself.**

So the value of this probe is not the 2.33 s. **It is whether class (b) works
at all**, because if it does, the same question applies to the wiring's
content, which is the real problem. **Say what your result implies for that**,
and mark it MEASURED or INFERRED.

## WHAT YOU MUST NOT DO

- **No fifth interposition.** P-w.
- **Do not delete the band or any part of it.** `TwelveAgree` takes 24
  hypotheses and the band DISCHARGES them.
- **Do not delete content to buy the ratio.** P-q, and it was measured here:
  -46 lines at zero seconds moved the ratio the wrong way.
- **Archive, never delete**, for a whole module; a dead section inside a live
  master is a removal with a backup outside the repository.
- **You may not weaken a statement and you may not narrow a direction.**
- **Do not touch anything under `src/L/Coding/`.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

Splitting a module by what consumers reach is D-30, which measured 5.45x in
this same wing. **Say what the J tower inherits after the split**, and
whether the remainder module is still available to it.

## ARCHIVE (DD18)

- **`_build/lj-1.66-review.md`**, read WHOLE. It is why this dispatch exists.
  Section E.1 is P-w's evidence; its section 4.1 names this class.
- **`_build/lj-1.66-report.md`** and **`_build/lj-1.67-report.md`**, the two
  measurements P-w rests on.
- `_build/lj-1.47-report.md`, D-30's 5.45x and the consumer-audit shape.
- `_build/lj-1.62-report.md` sections 2-3, the `KFacts` bundle, class (c).
- `dev/LESSONS.md` **P-w (new today)**, D-30 (`:3255`), P-m (`:2460`),
  P-q (`:2633`), P-t (`:2601`), P-l (`:2305`), read WHOLE.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature prices a spelling.** Say so in one line and
spend nothing.

## SCOPE (read)

`src/L/Condensation.lagda.md:2761-2900` (`EnvSet`, whole) FIRST, then two
application sites (`:3563`, `:4734`), then `_build/lj-1.66-review.md`
section E.1.

## SCOPE (write)

`src/L/Condensation.lagda.md` and `src/ProbeLJ168*.agda`. Your report is
`_build/lj-1.68-report.md`. **No other master. Never
`src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for probe`, and read every
statement.

- **P-w.** A module application copies; no interposition. **This brief is
  P-w's exception clause.**
- **D-30.** Price what the CONSUMER needs.
- **D-1.** The probe doctrine; the abort criterion is fixed above.
- **P-h.** Module-parameterized, never function-parameterized.
- **P-i, P-k, P-l, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as above.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never
  raised. **A heap exhaustion is a WALL with its seconds.**
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-35, C-36, C-37.**
- **D-8, D-10, D-13, D-26, D-29.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **The tree carries uncommitted work
  that is not in HEAD.**
- Typecheck what you touch and every consumer. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed.**
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. Code and its own comments only.
- **The machine is quiet and both Agda slots are yours. Report the load
  average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.68-report.md` incrementally, skeleton first.

**Lead with the closure: which of the fifteen definitions are reachable from
`out`, `back` and `memE-bnd`.** Then, if you built the split, the measured
before and after, three runs each side, one caliber, with the spread and the
load, and a plain statement that your thin module does NOT apply `EnvSet`.
**Mark every negative MEASURED or INFERRED.** Then what the result implies
for the wiring's 0.045 s per line, the DD4 answer, and **the convergence
answer.**

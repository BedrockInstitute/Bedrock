# LJ-1.92: probe the order-type module, the cardinal route's widest term

tier: codex (default)

## GOAL

**Measure the widest unmeasured term before the route is funded.** DD8:
measuring that term is what turns a projection into a price.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`a1f0e95`**. HEAD is green.

## WHAT IS SETTLED

`[LJ-1.90]` instantiated `BoundedSubsetAt` for the first time. **Every
hypothesis of the agreement layer takes a value**; the first one nothing can
supply is `cardκ : IsCardinal κ`, and **nothing in the tree proves any set is
a cardinal** (I checked: `IsCardinal` appears exactly twice in `src/`, its
definition and that hypothesis).

`[LJ-1.91]` priced the route, and I verified its decisive reading in the
source: **`IsCardinal` is AMBIENT**, because `BoundedSubset` opens the
V-structure at `:56` and keeps the L-structure qualified at `:58`. So the
internal `ω₁^L` is not the route: `IsCardinal` there would assert `ω₁^L` is
uncountable in V, which is independent.

**The route is the ambient Hartogs number of `ω`**, in five steps:

| step | content | lines |
|---|---|---:|
| 1 | the set `W` of well-orders on subsets of `ω` | 60 to 120 |
| 2 | **the order type of a well-order** | **300 to 500** |
| 3 | the Hartogs set itself | a few |
| 4 | ordinality and the countability facts | 70 to 150 |
| 5 | initiality and the supply at the `[LJ-1.90]` site | 60 to 120 |

**Step 2 is the widest unmeasured term. This dispatch measures it.**

## THE PROBE

**Build the smallest decisive miniature of the order-type construction and
price it.** For a well-order `R` on a subset of `ω`:

- the ordinal `ot R` with an order isomorphism `(field R, R) ≅ (ot R, ∈)`;
- uniqueness for isomorphic well-orders.

**Do NOT build the module.** Build enough to price it: the recursion's shape,
the isomorphism's shape, and whichever of the two is the hard half.

**Survey first, at `file:line`.** The tree may already have recursion on a
well-order, ordinal comparison, or a Mostowski collapse
(`src/V/Collapse.lagda.md` is delivered and is a collapse of a well-founded
extensional relation, which is very close). **A delivered collapse would
change the price a lot. Check it before you build anything.**

## THE ABORT CRITERION, fixed in advance per D-1

- **The miniature checks**: report its seconds and in-fence lines, and a
  price for step 2 with its basis named. Then STOP.
- **A step of the miniature cannot be built**: STOP, write the term you could
  not write, and say what the tree would have to provide.
- **Anything walls**: STOP, report the wall with its seconds.

**Work in `src/ProbeLJ192*.agda`.** If you touch a master it is GREEN when
you finish or you revert it.

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time. If a check does not return, KILL IT before you
start another, and report the wall with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not assume the axiom of choice.** Say if a step needs it.
- **Do not build the chapter.** This is a gate.
- **Do not touch anything under `src/L/Coding/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers and counts from the source, never from a report**, and
  say where a module ends if you report a count.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**Order types are about well-orders and injections, not about definability**,
so this looks like the most shared block of the phase. **Say whether the J
tower inherits it unchanged.**

## ARCHIVE (DD18)

- **`_build/lj-1.91-report.md`**, read WHOLE. The route, its five steps and
  why the internal Hartogs fails.
- `_build/lj-1.90-report.md` and `src/ProbeLJ190A.agda`, the site that must
  eventually receive `cardκ`.
- **`src/V/Collapse.lagda.md`**, the delivered Mostowski collapse. **This is
  the nearest delivered comparable and it may carry most of step 2.**
- `src/V/Model.lagda.md`, the power set and separation the route rides.
- `src/L/Ordinal/`, `src/L/StageCardinal.lagda.md`, the ordinal machinery.
- `dev/LESSONS.md` D-8, D-1, D-30, P-l, C-36, read WHOLE. **P-l: a price
  from a comparable elsewhere is a hypothesis, not a price.**
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Say in two lines whether Devlin proves order types or assumes them**, from
`dev/literature/devlin-II5.md` and its surroundings. Spend little. Return a
**LITERATURE USED** section.

## SCOPE (read)

**`src/V/Collapse.lagda.md` FIRST**, then `_build/lj-1.91-report.md`
section 2, then `src/V/Model.lagda.md`'s power set and separation.

## SCOPE (write)

`src/ProbeLJ192*.agda`, and any master **only if you revert it before
finishing**. Your report is `_build/lj-1.92-report.md`. **Never
`src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for probe`, and read every
statement.

- **D-8.** Gate a block before funding it; one best-effort figure with its
  basis named. **This brief IS the gate.**
- **D-1.** The probe doctrine: the smallest decisive miniature, then throw it
  away.
- **P-l.** A measured cure does not transfer by analogy, and neither does a
  price.
- **D-30.** Price what the CONSUMER needs.
- **C-36.** Write the term you could not write.
- **P-h, P-k, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as the bundle gives them.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-35, C-37.**
- **D-10, D-26, D-29.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Typecheck what you touch. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed**
  and say the master count.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.92-report.md` incrementally, skeleton first.

**Lead with what the tree already delivers toward order types**, at
`file:line`, then the miniature's seconds and lines, then **a price for step
2 with its basis named**. Then, if a step could not be built, the term you
could not write. **Mark every negative MEASURED or INFERRED.** Then the DD4
answer. Confirm every master is green or untouched.

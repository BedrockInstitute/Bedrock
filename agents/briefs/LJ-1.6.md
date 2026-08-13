# LJ-1.6: cardinality of a stage, |L α| = |α| for infinite α

tier: codex (default)

## GOAL

Deliver the stage-cardinality result the GCH chain consumes. **Survey the
archive first and price a port against a fresh write**, then build the cheaper
one. A refusal with both prices is a full deliverable.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## WHY IT RUNS NOW

`[LJ-1.7]` needs this and `[LJ-1.5]`. `[LJ-1.5]` is blocked on `[LJ-1.12]`,
which is re-targeting the crossing beside you. **This task is independent of
that re-targeting**, which is why it goes now rather than waiting.

## THE ARCHIVE IS THE FIRST QUESTION, NOT AN AFTERTHOUGHT

`archive/rud-route/` holds four modules that did this work on the retired
route, measured at the ledger caliber:

| module | in-fence |
|---|---:|
| `archive/rud-route/src/FOL/Count.lagda.md` | 588 |
| `archive/rud-route/src/L/CardinalPredicates.lagda.md` | 399 |
| `archive/rud-route/src/L/Cardinal.lagda.md` | 299 |
| `archive/rud-route/src/L/CardinalCount.lagda.md` | 166 |

**1,452 lines exist. Do not assume they port, and do not assume they do not.**

`dev/PLAN.md` DD13 rules that a port is priced AGAINST A FRESH WRITE, and
AGENTS.md says plan from the rewrite side: **first price the ideal form of the
content written fresh today, then compare.** "We already paid for it" decides
nothing in either direction.

**The route changed under these files.** They were written for the rud tower.
Ask per module whether the content is tower-agnostic counting or rud-specific
machinery. `[LJ-1.3]` ported the hull from 241 archived lines to 343 delivered,
and `[LJ-1.4]` ported the collapse from 181 to 239, so the precedent is that a
port grows and still pays.

## WHAT THE MATHEMATICS ACTUALLY NEEDS

`dev/literature/devlin-II5.md` section 1.4 has Devlin 5.4, and it is short:

> 5.4 Corollary. Let α be a limit ordinal. For any X ⊆ L_α there is a unique
> smallest M ≺ L_α such that X ⊆ M. For this M, |M| = max(|X|, ω).

The proof is one line in the source: the language `ℒ_X` has `max(|X|, ω)` many
formulas, so the hull has at most that many definable elements
(`dev2.txt:1360`).

**So the counting you owe is a counting of FORMULAS, not of sets**, and that is
why `FOL/Count.lagda.md` is the largest archived piece. Read the digest's
section 5.2 on II.1.1(vii), which it calls the counting half of 5.5 and 5.6.

**Say in the report what |L α| = |α| needs that 5.4 does not**, if anything.
The task row states the target as `|L α| = |α|` for infinite α; the digest's
chain may want it in a different form. If the row's statement is not what the
chain consumes, say so and give the statement that is. **A corrected target is
worth more than a delivered wrong one.**

## THE THRESHOLD

DD24 is the wing's ONLY threshold and it GATES now. The bar is **0.011472 s
per line at the module caliber**, times 1.15, so **0.013193**. The wing
measures 0.0065 aggregate today, 0.57x the AC side, so there is room.

**There is NO line cap on this wing, by DD24's deliberate omission.** It exists
to measure what GCH costs. So do not compress at the expense of content, and
report your module's rate.

**P-m sets the classes**: parameterized work runs 0.010 to 0.013 s per line,
instantiation 0.22 to 0.297. **A counting module that lands in the
instantiation class is the real risk.** If your rate goes there, say so with
the number; that is a finding, not a failure.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**Counting is the most tower-agnostic content in the whole wing**, and that
makes this the best DD4 opportunity of phase 1. `[LJ-0.7]` section 4 found
that the per-tower content is exactly TWO objects, the level-hood certificate
and the definable well-order. **Counting is neither.** So:

- **Parameterize the MODULE** (P-h), and do not let `Lset`, a stage
  presentation or the Def tower reach any type (P-l).
- Write it so the J tower instantiates it **unchanged**, and say in the return
  what it would have to supply.
- **If the archived modules are rud-specific in their statements but generic
  in their proofs, say so.** That is exactly the split DD4 wants found.

## LITERATURE (DD18)

- **`dev/literature/devlin-II5.md` sections 1.4, 1.5 and 5.2.** 5.4 is your
  target and 5.5 to 5.8 is the chain that consumes it.
- `_build/literature/dev2.txt:1357-1360` for 5.4 itself, and the II.1.1(vii)
  lines the digest cites. **Two OCR items are marked UNRESOLVED in the digest;
  check whether either touches your statement.**
- `dev/literature/j-hierarchy.md` for what the J tower counts.

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## ARCHIVE (DD18)

- **The four modules above. This is the survey the task row orders.** Report
  per module: portable, portable with change, or dead.
- `archive/dev/TASKS-archived.md` for what the dispatches that wrote them
  found, and `archive/dev/JOURNAL-archived.md` for why.
- `_build/lj-1.3-report.md` and `_build/lj-1.4-report.md`, the two ports this
  phase already did, for the rate a port runs at here.
- `dev/LESSONS.md` is NOT archived and still binds. **P-h, P-l, P-m, D-13's
  rewrite-side rule and D-10 decide this block.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A BUILD

From `python3 scripts/rules.py --for build`. Run it and read each statement.

- **P-h. Definability walks are module-parameterized, never
  function-parameterized.**
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.**
- **P-k. A read lemma is stated where its consumers use it.**
- **P-m. The check-cost rate is a content-class certificate.**
- **P-n. Satisfaction content at a concrete carrier is a payable floor.**
- **R-35, R-38**: sealing and opacity.
- **R-40**: state a membership witness SHALLOW and climb.
- **I-5**: the inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process. Heap
  exhaustion is a wall to report, never a cap to raise.
- **C-22. Write the deliverable incrementally.**
- **D-10. Price the truth of a recorded residue before pricing its proof.**
  The four archived modules are residues and the route changed under them.

## THE SIBLING

`[LJ-1.12]` is running beside you. **It writes only `_build/` and runs no
Agda**, so you have the Agda slots to yourself. Keep to your own territory
anyway:

- **Never run `git checkout .`, `git stash`, `git reset --hard` or `git
  clean`.** Revert by exact path only.
- **Never commit and never push.**

## SCOPE (read)

`dev/literature/devlin-II5.md` 1.4 and 1.5 first. Then the four archived
modules. Then `src/L/Hull.lagda.md`, which is where the hull and its counting
consumer live.

## SCOPE (write)

New masters under `src/L/`, and `src/L/Hull.lagda.md` if the counting belongs
beside the hull. **At most TWO new masters**; say why if you use both. Your
report is `_build/lj-1.6-report.md`. Never `src/Everything.lagda.md`: I wire
the catalog after auditing.

## CONSTRAINTS

- **Never commit and never push.**
- **Typecheck every file you write AND every consumer you touch**, one process
  at a time. Do NOT run `make check` or a whole-tree check.
- **Count with `python3 scripts/ledger.py`'s caliber**, never by hand. DD26
  excludes the two catalogs from every size figure.
- **Report cold seconds per file**, with the noise rule: under 0.5 s or under
  5 percent, whichever is larger, is flat.
- **Run `python3 scripts/lint-prose.py --check` and `python3
  scripts/lint-agda.py --check`.**
- **DD23 freezes mathematical prose.** Code and its own comments only. No
  chapter narrative.
- **Evidence is `file:line`.**
- **A refusal with both prices is a SUCCESS.**
- Write ASD-STE100 in the report.

## RETURN

Write `_build/lj-1.6-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: delivered with lines and rate, or refused with
   both prices.
2. **THE TWO PRICES**, port against fresh write, written BEFORE you built.
3. **THE ARCHIVE SURVEY**, per module: portable, portable with change, or dead.
4. **THE STATEMENT YOU DELIVERED**, and whether it is the row's `|L α| = |α|`
   or a corrected one.
5. **THE NUMBER**: in-fence lines, ledger caliber.
6. **SECONDS AND RATE**, cold, against the 0.013193 bar and P-m's bands.
7. **WHAT THE J TOWER WOULD SUPPLY** to instantiate it (DD4).
8. **LITERATURE USED.**
9. **ARCHIVE USED.**
10. **WHAT I AM NOT SURE OF.**

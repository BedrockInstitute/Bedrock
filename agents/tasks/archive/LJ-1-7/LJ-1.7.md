# LJ-1.7: the condensation theorem, then Devlin 5.5

tier: codex (default)

## GOAL

Build the condensation theorem and the bounded-subset lemma. **This is the last
mathematical block before the trophy.** Land it, or refuse with a measurement.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, clean at
`b1bf4fb`.

## THE GATE IS OPEN AND I MEASURED IT MYSELF

`[LJ-1.48]` built the condensation core at one instance and measured its class.
**GO.** My own re-run, three cold checks with the interface removed each time:
probe 5.35 / 5.05 / 5.07 s, mean 5.16; the imports-only cone 1.81 s; so the
content delta is **3.35 s over 337 to 386 lines, 0.0087 to 0.0099 s per line.**
The GO line was 0.0127 and the NO-GO line 0.05.

**The transfer statements measured 0.003 s per line**, which is the
parameterized end, not the floor.

`[LJ-1.46]` re-prices `[LJ-1.7]` with that rate at about **1,675 lines and 22
to 25 seconds**, down from its 36-second survey.

## WHAT TO BUILD

**Devlin 5.5**, `_build/literature/dev2.txt:1372-1385`: pick α below κ with `x`
inside `L_α`; take a limit λ with `x ∈ L_λ`; take the hull `M` of
`L_α ∪ {x}` in `L_λ`; collapse `M` to `π M`; the collapse fixes `L_α ∪ {x}`, so
`x ∈ π M`; **condensation gives `π M = L_γ`**; the sizes give
`|γ| = |α| < κ`, so `γ < κ`; therefore `x ∈ L_κ`.

**The condensation theorem itself is O1 and it does not exist in the tree.**
For `M` a Σ₁-elementary extensional substructure of `L_λ` with λ a limit, the
collapse `π M` is a level `Lset γ`.

**`[LJ-1.46]`'s obligation table is your work plan. Read that report WHOLE**
rather than taking my summary: C-32 exists because a brief of mine named a
section and hid the decisive probe.

## WHAT IS DELIVERED, so you assemble rather than rebuild

The substrate is complete and I have verified each of these exists:

- the bounded twelve-row table and block 1, `src/L/Condensation.lagda.md`,
  4,564 in-fence lines, all agreements CLOSED and machine-checked;
- the bounded graph matrices, `GraphB`, `StepAtB`, `DefBodyB`, and the row
  agreements;
- the tower-landing legs `ride-only` and `ride-defines`;
- the collapse with its transitive-fixing clause, `src/V/Collapse.lagda.md`;
- the Tarski-Vaught equivalence and `hull-closed` at HULL parameters,
  `src/L/Hull.lagda.md`;
- the Levy kit `abs₀`, `σ₁-up`, `π₁-down`, `src/FOL/Absoluteness.lagda.md`;
- the level size `|Lset α| = |α|`'s upper half, `src/L/StageCardinal.lagda.md`;
- the stage arithmetic, `src/L/Ordinal/StageArith.lagda.md`.

## D-30, ADMITTED TODAY AND IT IS WORTH 5x HERE

**Price what the CONSUMER needs, never the general law.** `[LJ-1.47]` measured
this at 5.45x: the square law was taken at every infinite set because that was
convenient, the chain uses it at two initial ordinals, and the consumer's form
runs 7.94 s where the general one runs 43.26 s. **Four of five general-law
sections had no consumer at all**, and one definition held 94.3 percent of a
module because it built an order type nobody wanted.

**So before you state a general lemma, read who consumes it.** 5.5 uses
condensation at ONE shape. Do not build the general theory of Σ₁-elementary
substructures if 5.5 needs one instance.

## THE THREE OBLIGATIONS YOU INHERIT, all open

1. **`envInK` is unproved at the class carrier**, so three row agreements are
   conditional on a site fact. **If your assembly consumes those rows, discharge
   it or state the conditionality.**
2. **`fin-inj`** is a module parameter of `Upper`
   (`src/L/StageCardinal.lagda.md:508`), 50 to 100 lines, unbuilt.
3. **`sq`**, the square law, is a module parameter
   (`src/L/StageCardinal.lagda.md:15`). `[LJ-1.47]` measured the consumer's
   form at 7.94 s over 744 lines but **did not build it as a master**. **If 5.5
   needs it, say what you assumed.**

## THE LAWS THAT DECIDE THE SHAPE

- **P-u.** Certify BEFORE you place. `src/L/Condensation.lagda.md` has ZERO
  placement and that is load-bearing. **If you need `absFo` or a placed `Δ₀`,
  STOP and report it**: the wall is flat at 8 GB across constant counts 0, 1,
  2 and 5.
- **P-v.** One formula, one spelling, decided at the formula level. **This file
  paid 10 to 15x at its leaves for the two-spelling shape.**
- **P-l, P-t.** What a type names is what costs, and the class follows the
  formula.
- **P-n.** Satisfaction at a concrete carrier is a payable floor. **If a piece
  is at the floor, say so with the number.**

## THE THRESHOLD

DD24's live bar is **0.012716**, from the AC baseline 0.011057 times the 1.15
tolerance. **Do not use 0.013193**; several earlier briefs of mine quote that
stale figure. Re-derive it from `dev/ledger.toml`.

The GCH side is at **0.0124 today, within**. With the cured square law and your
block at their measured and re-priced rates, the aggregate lands at **0.0129 to
0.0132**, which is inside the 5 to 10 percent run-to-run band around the bar.
**So your seconds matter and there is no margin to spend.** Report the marginal
rate for what you add, the whole-file rate, and the module-load cone
separately, each from at least three cold runs with the spread.

**C-31: the per-module flag is ADVICE; the aggregate is the judgment.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker, so it is stated in every brief and answered in
every return.

`[LJ-0.7]` found exactly TWO per-tower objects on the whole GCH chain and DD27
removed one. **Say which parts of the condensation theorem are template and
which are the Def tower's own**, and price them separately. D-26 predicts
per-tower for anything keyed on the defining syntax.

## ARCHIVE (DD18)

- **`_build/lj-1.46-report.md`**, the obligation table, and
  **`_build/lj-1.48-report.md`** with `src/ProbeLJ148.agda`, the measured
  shape. **Read both WHOLE.**
- **`archive/rud-route/src/L/Condensation.lagda.md`**, read for SHAPE only.
  **Its target is classically FALSE (`[LJ-1.11]`), so take no price from it.**
- `_build/l3.32-t261-report.md:32-47` for the MEASURED 124-line limit case.
- `_build/lj-1.47-report.md` for the consumer-scope levers.
- `dev/LESSONS.md` is NOT archived and still binds.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

- **`_build/literature/dev2.txt:1372-1385`**, 5.5's proof, and
  `dev/literature/devlin-II5.md` sections 1.5 and 2.x.
- **Devlin assumes the cardinal arithmetic and asserts absoluteness.** Say in
  one line what he assumes that you had to supply.
- The errata do NOT cover Chapter II section 5. `[LJ-1.14]` verified it. **Do
  not re-check it.**

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## SCOPE (read)

`_build/lj-1.46-report.md` and `_build/lj-1.48-report.md` FIRST, then
`src/ProbeLJ148.agda`, then `src/L/Condensation.lagda.md`'s exports, then
`src/L/Hull.lagda.md` and `src/V/Collapse.lagda.md`.

## SCOPE (write)

**At most ONE new master under `src/L/`**, plus `src/L/Condensation.lagda.md`
if the theorem belongs there, plus `src/ProbeLJ7*.agda` if you need probes.
Your report is `_build/lj-1.7-report.md`. **Never `src/Everything.lagda.md`:**
I wire the catalog after auditing, and the gate has refused a commit for
exactly that.

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **P-h.** Module-parameterized, never function-parameterized.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-l, P-m, P-n, P-t, P-u, P-v** as above.
- **R-35.** Union representations are meta-poisoned: state the membership at
  the SMALL index and climb.
- **R-38.** Seal at the birth site, and do NOT unseal.
- **R-40.** State a membership witness SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never
  raised. **Report a heap exhaustion as a WALL with its seconds.**
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33.**
- **C-34.** Build the cure or report the wall. **"P-l forbids it" is not a
  third option.**
- **C-35.** No consumer, no DELIVERED. **A theorem nothing consumes is
  untested**, and this file has produced that failure twice.
- **C-36.** A failed substitution is not a proof of impossibility. **You may
  strengthen a statement; you may not weaken one.**
- **D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Typecheck your master and every consumer. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed.**
  `[LJ-1.41]` reported two theorems closed that sat OUTSIDE the fence as prose,
  carrying four defects, and every other gate passed.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. Code and its own comments only.
- **The machine is quiet and both Agda slots are yours.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.7-report.md` incrementally, skeleton first.

Lead with the verdict: does the condensation theorem close, does 5.5 close, and
the rates with their spreads. Then what each obligation cost against
`[LJ-1.46]`'s table. Then what you assumed about `envInK`, `fin-inj` and `sq`.
Then the DD4 split, and what you are not sure of.

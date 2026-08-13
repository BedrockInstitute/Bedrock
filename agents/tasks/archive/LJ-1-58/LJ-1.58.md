# LJ-1.58: the placement gate for the leaf adequacy

tier: codex (default)

## GOAL

`[LJ-1.57]` PROVED the leaf adequacy. **It proved it in a probe, and a probe
is never committed, so it is not in the tree.** Measure what placing it costs
under the cheapest spelling you can find, then place what the price allows.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`3bb426e`**. There are no working-tree edits.

## THE PRICE THAT MAKES THIS A GATE, and I did this arithmetic myself

| | lines | seconds | rate |
|---|---:|---:|---:|
| `L.Condensation` today | 4,640 | 54.77 | 0.01180 |
| the leaf proof, as spelled in the probe | 884 | 66.77 | **0.07553** |
| after placing it as-is | 5,524 | 121.5 | **0.02200** |
| DD24 live bar | | | **0.012716** |

**Placing it as spelled puts the file 1.73x over the bar.**

To sit ON the bar, those 884 lines may cost **15.5 s**, a rate of **0.0175**.
**That needs a 4.3x improvement on the measured spelling.**

**4.3x is not assured and it is not a wall either.** This tree has measured
12.8x on the transport cure, 5.45x on the square law and 681x on the naming
cure. **So this is a probe with an abort criterion, not a build.**

**Do not assume the prepared compression patch helps.** I checked: its 1,257
lines cost 14.52 s, close to the file average, so removing them from a more
expensive file RAISES the ratio, to 0.0251. It is worth absolute seconds and
it is not worth the ratio. **It is still not your task.**

## THE ABORT CRITERION, fixed in advance per D-1

Place ONE representative piece, measure its placement rate, and report one of:

- **GO**, the piece places at **0.0175 or below**. Then place the rest and
  say what the whole file measures.
- **AMBER**, between **0.0175 and 0.030**. Then say which technique bought
  what, what the residual is, and what you would need to close it.
- **NO-GO**, above **0.030**. **Then STOP and report the price.** Do not
  spend the rest of the budget pushing at it. A measured NO-GO is a full
  deliverable and it is the answer the owner needs.

**Choose the representative piece and justify the choice**: it must be
instantiation-class content carrying full formula bodies in written types,
so that its rate predicts the whole. Say why the one you picked is
representative.

## WHERE THE COST IS, in `[LJ-1.57]`'s own words

"every written type in the walk and the leaf carries a full formula body
(`shapesBS`, `closedBS`, `shapedBS`, `DefBodyB`) whose satisfaction the
elaborator normalizes at the abstract slots"
(`_build/lj-1.57-report.md:117-120`).

**That sentence names the target. Attack it.**

## THE TECHNIQUES, each measured in THIS tree, each with its law

**Read `python3 scripts/rules.py --for probe` and P-i first. P-i is the
conversion-explosion playbook and it says the cure is selected by its
decision tree, NOT by trial.**

1. **P-c, R-36, R-38. SEAL AT THE BIRTH SITE.** If the formula bodies are
   `opaque` at their definition, the elaborator treats them as atoms and does
   not normalize their satisfaction. Expose what a consumer needs with a read
   lemma in its own `opaque unfolding` block. **R-38: a consumer's alias of a
   transparent imported operation is itself a birth site.**
2. **P-l.** A statement may be ABOUT a concrete thing without dragging that
   thing's PRESENTATION into its type. **Naming a transparent construction in
   a type is what costs.**
3. **P-k.** State the read lemma in the form the CONSUMERS need, absorbing
   the last layer, so the conversion is paid once instead of once per
   consumer.
4. **P-v.** Give a proof a NAME and pass the name.
5. **D-30. Price what the CONSUMER needs.** **This one may be the largest
   lever and I want it answered explicitly.** The probe proved every piece
   two-way at full generality because that was the cheapest way to be sure.
   **The master may not need both directions of every piece.** Ask what
   Devlin 5.5 actually consumes, and say what falls away if you give it only
   that. That question was worth 5.45x at the square law and it produced
   `[LJ-1.55]`'s slot fix.

## WHAT YOU MUST NOT DO

- **You may not weaken a statement to make it cheap.** A cheaper theorem that
  says less is a defect, not a cure. If narrowing to the consumer's need
  drops generality, **say exactly what was dropped and what still consumes
  it.**
- **The proof must stay two-way where its consumer needs two ways.** Check
  the consumer before you narrow, do not guess.
- **Do not touch anything under `src/L/Coding/`.** If the machine looks
  wrong, STOP and report it.
- **All masters carry ZERO placement of `absFo` or a placed `Δ₀`.** If you
  need one, STOP and report it.

## WHAT IS GREEN AND IS YOUR SOURCE

- **`src/ProbeLJ157A.agda`**, 985 lines: `BinFormAgree`, `UnFormAgree`,
  `ShapesAgree` (twelve rows, both directions), `ShapedAgree`,
  `WitnessAgree`, and **`LeafAgree`, the leaf adequacy, both directions
  against the machine's imported `DefBody`.** I verified that statement and
  re-ran the probe green.
- `src/ProbeLJ156A.agda`: `ClosedAgree`, `DomainAgree`, `TmAgree`,
  `SatGraphAgree`.
- `src/ProbeLJ156Shape.agda`, `src/ProbeLJ155B.agda`, `src/ProbeLJ155C.agda`,
  `src/ProbeLJ154A.agda`.

**These are the proofs. You are not re-proving them. You are pricing and
placing them.** If you find yourself re-proving one, stop and say which.

## THE MEASUREMENT, and it decides the verdict

Caliber: C-12 `GHCRTS="-A64m -I0 -M8g"`, user seconds from `/usr/bin/time -p`,
cold module with the module's own interface moved aside before EVERY run,
dependencies warm, one process, quiet machine. **Three completed runs, with
the spread, in ONE caliber.**

Report the **marginal rate of what you place**, the **whole-file rate** and
the **cone** separately. `[LJ-1.55]` and `[LJ-1.56]` both did this correctly;
follow their tables.

**A single run is not a measurement and a warm run is not a cold one.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.** This has produced something on each of the last two dispatches.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

`[LJ-1.57]` found the whole leaf layer is TEMPLATE content: no type mentions
a concrete carrier. **Say whether your cheaper spelling keeps that.** A
sealing cure that pins the layer to the L tower would buy seconds and cost
the J tower, and I want that trade named if it appears.

## ARCHIVE (DD18)

- **`_build/lj-1.57-report.md`**, read WHOLE, and **`src/ProbeLJ157A.agda`**,
  read WHOLE. It is your source.
- **`_build/lj-1.56-report.md`** and `src/ProbeLJ156A.agda`, read WHOLE.
- **`_build/lj-1.25-report.md`**, the transport cure that measured 12.8x by
  abstracting the SOURCE. **This is the closest measured analogue to your
  task and you should read it before you choose a technique.**
- `_build/lj-1.47-report.md`, the square law's 5.45x from the D-30 question.
- `_build/gch-compression-audit.md` for what is already known removable.
- `archive/rud-route/` for SHAPE only.
- `dev/LESSONS.md` is NOT archived and still binds.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature bears on a placement cost.** Say so in one line
and spend nothing. Return a **LITERATURE USED** section saying that.

## SCOPE (read)

`_build/lj-1.57-report.md` section 6 FIRST, then `src/ProbeLJ157A.agda`, then
`_build/lj-1.25-report.md`, then `src/L/Condensation.lagda.md:1600-1700`.

## SCOPE (write)

`src/L/Condensation.lagda.md`, `src/L/BoundedSubset.lagda.md`, and
`src/ProbeLJ158*.agda`. Your report is `_build/lj-1.58-report.md`. **No other
master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` AND `--for probe`, and read every
statement.

- **D-1. The probe doctrine.** The abort criterion is fixed above.
- **P-i. The conversion-explosion playbook.** Select the cure by its decision
  tree, not by trial.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **P-h.** Module-parameterized, never function-parameterized.
- **P-k, P-l, P-m, P-n, P-t, P-u, P-v** as above, each with its action.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never
  raised. **A heap exhaustion is a WALL with its seconds.**
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-35, C-36, C-37.**
- **D-8, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **The tree is clean; keep your work
  visible in it.**
- Typecheck what you touch and every consumer. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed.**
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. Code and its own comments only.
- **The machine is quiet and both Agda slots are yours.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.58-report.md` incrementally, skeleton first.

**Lead with the verdict: GO, AMBER or NO-GO, with the measured rate.** Then
which technique bought what, each with its before and after in one caliber.
Then what you placed and what is still in a probe. Then whether any
statement narrowed, and what still consumes the narrowed form. Then the
rates with spreads, the DD4 answer, and **the convergence answer.**

# LJ-1.516 report: transport the satisfaction, not only the formula

**VERDICT: NO-GO at `graphSat-transports`.** The obligation term is not
written. The NO-GO is stated in
`agents/tasks/LJ-1-516/review-of-graphSat-transports.md`. That file is the
critic's input and it does not close the task.

**W3 IS GO, ON THE FIRST RUN.** The seam between `liftFo-correct` and the
`⊨-map` law composes. `agents/tasks/LJ-1-516/Probe516.agda:72-77`, exit 0,
`runs/w3-0.out`.

**THE ONE SENTENCE FOR THE NEXT BRIEF.** The brief expected the obstruction to
be a seam between two delivered laws. **It is not the seam. It is the Levy
grade of `LsetGraphAt`, and that grade is REFUTED and not merely unbuilt.**
Relabelling never changes the model; only absoluteness does; and absoluteness
is gated on `Δ₀`, `Σ₁` or `Π₁`, none of which this formula has.

## D-10, BEFORE ANY AGDA

The brief ordered this first and it changed the task.

**Each side of `liftFo-correct` is a FORMULA, and neither is a satisfaction.**
`src/FOL/Manipulation/Bounding.lagda.md:198-199`:

    liftFo-correct : ∀ {n} (φ : Formula K n) (h : BoundedFo P φ)
                   → mapFo up (liftFo φ h) ≡ mapFo proj φ

At this frame `W = V ℓ`, so **both sides are `Formula (V ℓ) n`**.

**A satisfaction statement can consume either side, but only in ONE
structure.** `⊨-map` (`src/FOL/Manipulation/Relabelling.lagda.md:154-155`)
takes a fixed `𝒮` and moves between two constant domains inside it. At this
frame `𝒮 = 𝒮ᵥ` for both applications. **So the composite of the two laws
relates satisfaction in `𝒮ᵥ` with satisfaction in `𝒮ᵥ`.**

The briefed statement names `AbsL.𝒮M`, which is `𝒮ᵥ ↾ (∈ Lset α)`
(`src/L/Hull.lagda.md:153`), and `𝒮ʟ`, which is `𝒮ᵥ ↾ isL`
(`src/L/Constructible.lagda.md:411`). **Those are two model changes, and
relabelling supplies neither.** That is the gap D-10 asked me to name, and I
named it before writing the transport.

**D-10's second half then fired.** The brief's target can be false. The stage
`graphFo-at-SL` lands at is `sucV σ` with `σ` the constant bound
(`agents/tasks/LJ-1-514/Probe514.agda:136-146`), chosen by the formula's
constants and by nothing else. `LsetGraphAt` asserts an approximating function
exists (`src/L/Coding/Sequence.lagda.md:292`). The right-to-left direction
needs that function inside `Lset α`. **That is `hier-in-stage`**, open since
`[LJ-1.494]` (`agents/tasks/LJ-1-494/lj-1.494-report.md:357-359`) and named by
`[LJ-1.514]` as the blocker it did NOT remove
(`agents/tasks/LJ-1-514/lj-1.514-report.md:254-255`). I did not build a term
of the negation and I do not claim one.

## W3, THE WIDEST UNMEASURED TERM

The brief named the seam. **The seam was written first, with the obligation
omitted, and typechecked alone.** It passed on the first run.

`agents/tasks/LJ-1-516/Probe516.agda:72-77`:

    seam : ∀ {n} (φ : Formula CS.S n) (h : BoundedFo (Below′ α) φ) (γ : SL ^ n)
         → ((map fst γ) AbsL.⊨ᵛ RL.liftFo φ h) ≡ ((map fst γ) ⊨ʟᵛ φ)

Three steps: `⊨-map` backwards at `SL`, one `cong` at `liftFo-correct`,
`⊨-map` forwards at `CS.S`. **No `Δ₀`. No stage hypothesis. No `hierL`.**

**IT IS GENERIC IN THE FORMULA AND IN THE STAGE.** `LsetGraphAt` is not
mentioned anywhere in it.

**The tree already holds this chain at a sibling site**, and I found it before
writing: `transferFo` (`src/L/Absoluteness.lagda.md:122-127`) runs `abs₀`,
`⊨-map`, `liftFo-correct`, `⊨-map`. **My `seam` is that chain with the `abs₀`
step REMOVED**, because `abs₀` is exactly the step this formula cannot pay.
Under the Boundary's "a measured cure does not transfer by analogy" I did not
take `transferFo`'s instance; I built the instance at `K = CS.S`, `K' = SL` and
measured it here.

## WHAT WAS BUILT

**`transports-Δ₀`, THE BRIEFED STATEMENT FOR THE WHOLE Δ₀ FAMILY.**
`Probe516.agda:115-122`:

    transports-Δ₀ : ∀ {n} (φ : Formula CS.S n) → Δ₀ φ
                  → (h : BoundedFo (Below′ α) φ) → Transports φ h

where `Transports φ h` (`:106-109`) is the briefed type:

    (γ : SL ^ n) → (γ AbsL.⊨ᵐ RL.liftFo φ h) ≡ ((map intoL γ) ⊨ʟᵐ φ)

**Unconditional in the stage. Generic in the carrier. Generic in the formula.**
Four steps: `AbsL.abs₀` inward at the stage, the seam, `AbsLʟ.abs₀` outward at
`L`. The environment correspondence `intoL` (`:95-96`) is `Lset→isL`
(`src/L/Constructible.lagda.md:395`), and it moves no set: `map-intoL`
(`:98-100`) proves the projections agree.

`transports-Σ₁` (`:125-130`) is the same for the one-direction Σ₁ case, through
`AbsLʟ.σ₁-up` (`src/FOL/Absoluteness.lagda.md:182-183`).

**So the briefed obligation is NOT blocked by the instruments. Any Δ₀ formula
over `CS.S` transports today. `LsetGraphAt` is not one.**

**THE BRIEFED TYPE FORMS.** `GraphSatTransports` (`:171-175`) is
`Transports (LsetGraphAt w b) h` at any stage and any certificate. It
typechecks. It has no term.

## THE GAP, MEASURED AND NOT READ

Every route the tree delivers from `AbsL.⊨ᵐ` to `_⊨ʟᵐ_` is gated on a Levy
witness for the formula.

| instrument | `file:line` | gate |
|---|---|---|
| `abs₀` | `src/FOL/Absoluteness.lagda.md:122-123` | `Δ₀ φ` |
| `σ₁-up` | `src/FOL/Absoluteness.lagda.md:182-183` | `Σ₁ φ` |
| `π₁-down` | `src/FOL/Absoluteness.lagda.md:187-188` | `Π₁ φ` |

`LsetGraphAt w b` has none, and the four refutations below are machine-checked
by absurd pattern.

| refutation | `Probe516.agda` |
|---|---|
| `Δ₀ (LsetGraphAt w b) → ⊥*` | `:142-143` |
| `Δ₀ (RL.liftFo (LsetGraphAt w b) h) → ⊥*` | `:147-150` |
| `Σ₁ (LsetGraphAt w b) → ⊥*` | `:157-159` |
| `Π₁ (LsetGraphAt w b) → ⊥*` | `:163-164` |

**The second row is the one that blocks.** `liftFo` is defined
constructor-for-constructor (`src/FOL/Manipulation/Bounding.lagda.md:162-174`),
so the lifted formula keeps the unbounded `∃̇` and `AbsL.abs₀` cannot be
applied to it either.

**The cause is syntactic, and it is not repairable by a better proof.** `Δ₀`
has no constructor for `∃̇` or `∀̇` (`src/FOL/LevyHierarchy.lagda.md:47-57`).
`GraphAt w b = ∃̇ (ApproxAt zero (suc b) ∧̇ Step (suc w) (suc b) zero)`
(`src/L/Coding/Sequence.lagda.md:292`) and
`ApproxAt f a = domAt f a ∧̇ ∀̇ (∀̇ (…))` (`:287-289`). An unbounded `∃̇` over a
core holding an unbounded `∀̇` is outside all three classes at once.

## C-42, THE SWEEP

C-42 (`dev/LESSONS.md:3752`) says a refutation measures one site and never how
far the shape extends, and that the next action is the sweep and the COUNT.

**THE SHAPE IS "a naming site of `LsetGraphAt` that carries no `Δ₀` witness".
THE COUNT IS 12 OF 16.** The sixteen sites are `[LJ-1.514]`'s own table
(`agents/tasks/LJ-1-514/lj-1.514-report.md:39-56`). Every number below is
machine-checked, not read.

| verdict | count | sites |
|---|---|---|
| REFUTED, no `Δ₀` witness can exist | 12 | `LsetGraphAt`, `ApproxAt`, `StepAt`, `domAt`, `DefAt`, `isCodeAt`, `satGraphAt`, `DefinesAt`, `keyArityAtL`, `hasWitnessAt`, `envOneAt`, `tagAtL` |
| GRADED ALREADY in the tree | 2 | `appAt`, `prAtL` |
| BOUNDED BY CONSTRUCTION, not refutable | 2 | `closedAt`, `shapedAt` |

Eleven refutations are one green run, `agents/tasks/LJ-1-516/runs/Sweep516.agda`
with `runs/sweep-1.out`, exit 0. `satGraphAt` is the twelfth and it needed its
seal opened, `runs/Sweep516b.agda` with `runs/sweep-3.out`, exit 0.

The two graded sites carry delivered witnesses: `Δ₀-appAtK`
(`src/L/Coding/Key.lagda.md:187`) and `Δ₀-prAtLK` (`:184`). The two bounded
sites are not guesses either: Agda named `Δ₀ (andClosedAt w)`'s valid
constructor `δ-∀∈` itself, `runs/sweep-2.out:3-6`.

**SO THE WALL IS NOT A PROPERTY OF THE TOP FORMULA. IT RUNS THE WHOLE SPINE.**
A brief that hoped to route around `LsetGraphAt` by transporting one of its
parts instead will meet the same refutation at eleven of the twelve.

**And the shape has consumers.** Nine masters name `LsetGraphAt`:
`src/L/Hierarchy.lagda.md`, `src/L/Condensation.lagda.md`,
`src/L/Coding/Sequence.lagda.md`, `src/L/Choice/Order.lagda.md`,
`src/L/Choice/Before.lagda.md`, `src/L/Choice/Limit.lagda.md`,
`src/L/Choice/Faithful.lagda.md`, `src/L/Choice/Internal.lagda.md` and
`src/Everything.lagda.md`. **I did not re-measure the refutation at each. What
transfers without re-measurement is the syntactic fact; what does not is any
consumer's own stage bound.**

## THE ROUTE THE TREE ALREADY USES, AND NEITHER THE BRIEF NOR `[LJ-1.514]`
## NAMED IT

Two delivered facts change what the next brief should order.

**FIRST, THE SEMANTIC ROUTE NEEDS NO LEVY WITNESS AT ALL.**
`src/L/Condensation.lagda.md:422-432`:

    ride-only    : ⟨ γ ⊨ LsetGraphAt w b ⟩ → IsOrd (fst (lookup b γ))
                 → fst (lookup w γ) ≡ Lset (fst (lookup b γ))
    ride-defines : IsOrd (fst (lookup b γ))
                 → fst (lookup w γ) ≡ Lset (fst (lookup b γ))
                 → ⟨ γ ⊨ LsetGraphAt w b ⟩

These ride `Lset-only` (`src/L/Hierarchy.lagda.md:334`) and `Lset-defines`
(`src/L/Hierarchy.lagda.md:646`). **They convert satisfaction into an equation
about `V ℓ` that mentions no carrier**, so it crosses carriers for free.

**SECOND, THE TREE'S OWN ANSWER TO THIS EXACT PROBLEM IS A BOUNDED REWRITE.**
`L.Condensation` carries a whole family of `…B` and `…Bnd` formulas and proves
them `Δ₀`: `Δ₀-satGraphB` at `src/L/Condensation.lagda.md:2318`, and the
`EraseTransfer` template at `:287-308` that spends `abs₀` on them. **The
chapter is the bounded rewrite of the coding chain, built for this transfer.**

`EraseTransfer` needs `countFo φ ≡ 0` (`:287`). `[LJ-1.514]` measured
`countFo (LsetGraphAt w b) = 664` (`agents/tasks/LJ-1-514/lj-1.514-report.md:30`,
basis at `:32`). **So the 664 has a consumer after all: it is exactly what
closes the erase route at the original formula.** The bounded rewrite is
parameter-free by construction, which is why it is written and not derived.

## WHAT THE CONDENSATION LEG OWES NOW

Every remaining object between the tree and `cover`, as a type. **I do not
price any of them.**

**DELIVERED, and usable today.**

1. `graphFo-at-SL : {n : ℕ} (w b : Fin n) → Formula (Stage.SL w b) n`.
   `agents/tasks/LJ-1-514/Probe514.agda:159-160`. In a probe, not in `src/`.
2. `seam`, this task, `agents/tasks/LJ-1-516/Probe516.agda:72-77`.
3. `transports-Δ₀` and `transports-Σ₁`, this task, `:115-122` and `:125-130`.
4. `ride-only` and `ride-defines`, `src/L/Condensation.lagda.md:422-432`.
5. `code-of`, as `H.hull-member`. `src/L/Hull.lagda.md:337-339`, marked BUILT
   by `[LJ-1.492]` (`agents/tasks/LJ-1-492/lj-1.492-report.md:155-157`).
6. `ambient-cover` / `ambient-level`, BUILT by `[LJ-1.484]`, rebuilt at
   `agents/tasks/LJ-1-492/Probe492.agda:137-151`.
7. `TV→elem : TarskiVaught → Elementary`, `src/L/Hull.lagda.md:239`. **This is
   the only delivered instrument that transports satisfaction of a formula of
   ANY Levy grade.** It relates `𝒮M` and `AbsL` at `AtM`, not a stage and `L`.

**UNBUILT.**

8. `hier-in-stage`. The type is `[LJ-1.494]`'s
   (`agents/tasks/LJ-1-494/lj-1.494-report.md:123-131`). It bounds `hierL δ`
   by `α`. **Still open. This task did not touch it.**
9. The `SL`-side reading and introduction of `graphFo-at-SL`, that is
   `ride-only` and `ride-defines` at the stage carrier under `AbsL.⊨ᵐ`. **The
   introduction half is `hier-in-stage` again.** No type is written for it
   anywhere in the tree today.
10. `StageBoundOfCode`. UNBUILT and WRONG SHAPE: a `Code` carries no ordinal
    (`src/L/Hull.lagda.md:72-74`), measured by `[LJ-1.492]`
    (`agents/tasks/LJ-1-492/lj-1.492-report.md:159-161`).
11. `StageSatOfCover`. The missing conversion, type at
    `agents/tasks/LJ-1-492/Probe492.agda:205-209`.
12. `CoverWitnessesInHull`. Type at
    `agents/tasks/LJ-1-492/Probe492.agda:216-219`. UNBUILT.
13. `cover`. UNBUILT, and `[LJ-1.492]` measured that it is not a join
    (`agents/tasks/LJ-1-492/lj-1.492-report.md:176`).
14. `levelIn`. Still an unpaid sibling
    (`agents/tasks/LJ-1-492/lj-1.492-report.md:177-178`).

**AND ONE THIS TASK ADDS.** A `Δ₀` or `Σ₁` presentation of the graph statement
at the class carrier, or a decision to use `ride-only` and `ride-defines`
instead. **Without one of the two, no `LsetGraphAt` satisfaction crosses a
model boundary anywhere in this leg.** That is the new entry, and it is the one
this task measured.

## W2, THE GENERIC CARRIER

**The brief did not state W2, and I answer it.** Nothing here is written twice.
`seam`, `Transports`, `transports-Δ₀` and `transports-Σ₁` are all stated at a
generic `φ : Formula CS.S n` and a generic stage `(α , ordα)`. **`LsetGraphAt`
appears only in the refutations and in the briefed type's alias**, which is
where a concrete formula belongs. `Relabel`'s own telescope is the tree's, and
this task adds no new generic layer. **No deadline forced a fixed form.**

## W4, THE RETIREMENT CLAUSE

Not applicable. No module was retired, and nothing under `src/` changed.

## PRICE

One Agda process per run, `GHCRTS="-A64m -I0 -M8g"`, the wide caliber, set on
the pane by the program and untouched. **No heap wall. No rerun of a walled
run.** Three forced rechecks each, cold: the module's build output is removed
before every timed run.

| measurement | median wall | median peak RSS | basis |
|---|---|---|---|
| W3 alone | 2.50 s | 456,048,640 bytes | `runs/w3-1.time`, `runs/w3-2.time`, `runs/w3-3.time` |
| full file | 4.61 s | 527,417,344 bytes | `runs/full-4.time`, `runs/full-5.time`, `runs/full-6.time` |
| witness | 2.49 s | 460,521,472 bytes | `runs/witness.out:2-3` |

**W3 came in at 2.50 s against the brief's "under 40 seconds".** The brief told
me not to fund W3 against `[LJ-1.514]`'s census run, and I did not: that run
counted constants and this one composes two laws.

**THE SWEEP COST FIVE FAILING RUNS AND THAT IS RECORDED.** Agda stops at the
first failing clause, so each wrongly placed absurd pattern cost one run of
about 3 s. Total about 15 s. **This is a method note: budget one run per
correction, not one run per sweep**, and read the definition before writing the
pattern. **The first two were avoidable**, by reading `ApproxAt`
(`src/L/Coding/Sequence.lagda.md:287-289`) and `extAt`
(`src/L/Coding/Model.lagda.md:662-664`) before guessing the depth. The other
three were not: `closedAt` and `shapedAt` turned out bounded, and `satGraphAt`
was stuck behind its seal, and neither fact is visible without a run.

## THE ESTIMATE AGAINST THE MEASUREMENT

| quantity | brief | measured |
|---|---|---|
| probe, non-blank non-comment | about 140 | 84 |
| obligation, non-blank non-comment | about 40 | 0 written, and the type is 5 |
| W3, non-blank non-comment | about 25 | 36 |
| W3, wall | under 40 s | 2.50 s |

**The probe came in at 60 percent of the estimate because the obligation was
never written.** What replaced it is smaller than what it replaced: four
refutations are eight lines.

## WHAT THE STATEMENT COST, WHAT RESISTED, WHAT I WEAKENED

- **What it cost.** 84 non-blank non-comment lines across the probe, 4.61 s
  median for the full recheck, 15 s of sweep corrections.
- **What resisted.** Nothing mathematical. **Four mechanical points and every
  one was a scope or level slip, not a proof problem:** `FOL.Absoluteness` had
  to be imported for `Single`; `SL` had to leave `Seam` as `public`; `∘` is not
  in `Base.Prelude`; and `Transports` sits at `Type (ℓ-suc (ℓ-suc ℓ))` and not
  one level lower, because the `⊨ᵐ` on each side is an `hProp (ℓ-suc ℓ)`.
  **The mathematics never fought back, which is itself the finding: the two
  named laws fit together at the first attempt.**
- **What I had to weaken.** The obligation, and it is not a weakening but a
  refusal. **I did not write `graphSat-transports` under any hypothesis.** I
  could have hypothesized `Δ₀ (LsetGraphAt w b)` and discharged the brief.
  **That hypothesis is refuted in this same file** (`:142-143`), so a term
  under it would be vacuous and would read as a delivery. I did not write it.
- **What I could not close.** The obligation. The reason is `hier-in-stage`,
  which the brief forbade me to attempt, and the Levy grade, which no proof
  can supply.

## CORRECTIONS TO THE BRIEF

**Premise 9 cites `⊨-map` at `src/L/Hull.lagda.md:176`. That line is not
`⊨-map`.** Line 176 is the body of `Elementary`,
`→ (δ ⊨ᵐ φ) ≡ (map inL δ AbsL.⊨ᵐ (mapFo inL φ))`. `⊨-map` is imported at
`src/L/Hull.lagda.md:22` and applied at `:419` and `:425`. **The premise's
substance holds** and the law is delivered; only the line is wrong. Its
declaration is `src/FOL/Manipulation/Relabelling.lagda.md:154-155`.

**The brief's `↔` is delivered as `≡`.** Every law in this chain is a path of
`hProp`s, so `Transports` states an equality and not a bi-implication. That is
stronger and it is what the tree's own `transferFo` states.

**Premises 1 through 8 and 10 through 13 all held as written.** I checked each
at its cited line.

## WHAT THE NEXT BRIEF NEEDS

1. **DO NOT ORDER `graphSat-transports` AGAIN AT `LsetGraphAt` WITHOUT A NEW
   INSTRUMENT.** The three the tree has are refuted at this formula, and the
   refutation is in the probe, not in prose.
2. **`transports-Δ₀` IS AVAILABLE AND IS GENERIC.** Any brief wanting this
   transport for a Δ₀ formula over `CS.S` can order it today. It costs a
   citation, not a proof.
3. **THE TWO LIVE ROUTES ARE THE SEMANTIC ONE AND THE BOUNDED REWRITE.**
   `ride-only` and `ride-defines` (`src/L/Condensation.lagda.md:422-432`) for
   the first; the `…B` family with `Δ₀-satGraphB`
   (`src/L/Condensation.lagda.md:2318`) and `EraseTransfer` (`:287-308`) for
   the second. **Name which one before writing the brief. They have different
   prices and neither is priced here.**
4. **THE SEMANTIC ROUTE'S `SL`-SIDE INTRODUCTION IS `hier-in-stage`.** It is
   not a cheaper way around the open blocker. Ordering it is ordering that.
5. **DO NOT ORDER A `Δ₀` WITNESS FOR ANY OF THE TWELVE REFUTED SITES.** The
   count is in the C-42 table above and each entry is a typechecked term.
6. **`[LJ-1.514]`'s 664 IS NOT A CURIOSITY.** It is the exact quantity that
   closes `EraseTransfer` at the original formula. A brief taking the erase
   route must order the bounded rewrite, not the original.
7. **Do not order `coverFo`, `code-of` or `ambient-level` again.** The brief
   restates this and I obeyed it. **Its basis is narrower than the brief says,
   and the next brief should know which half is measured.** `[LJ-1.492]`
   forbids `code-of` and `ambient-level` by name
   (`agents/tasks/LJ-1-492/lj-1.492-report.md:337-338`), because `[LJ-1.484]`
   built them. `coverFo` is not in that sentence; what that report says about
   it is that the formula forms and the obligation above it does not
   (`agents/tasks/LJ-1-492/lj-1.492-report.md:170-175`). This task touched
   none of the three.

## RATIO BAR

The bar is 0.0123 seconds per in-fence line and its divisor is the in-fence
line count of this task's write scope, counted the ledger's way. **This task's
write scope holds no `.lagda.md` master and no ` ```agda ` fence, so the
divisor is 0 and the bar cannot fire.** The task landed nothing in `src/`, as
the brief required.

## ARCHIVE USED

Every CANDIDATE the block named is answered.

- **`archive/dev/JOURNAL.md`. READ AND USED.** `:809`:
  `missing `Δ₀` cure**, because the tree already carries `Δ₀-extAtB`,`
  This is the passage that told me the tree spends `abs₀` on BOUNDED rewrites
  of the coding formulas rather than on the originals. It is what sent me to
  `src/L/Condensation.lagda.md:2318` and to `EraseTransfer`, and that is the
  "second live route" of this report.
- **`archive/dev/DECISIONS-archived.md`. READ AND USED.** Its D31 row, `:51`,
  says `LsetGraphAt` is "a two-line formula whose definitional cone bottoms out
  in the twelve satisfaction clauses and `DefAt`". **Twelve is the same number
  the C-42 sweep measured from the other direction**, and reading it before the
  sweep is why the sweep covered the spine and not only the top.
- **`archive/dev/JOURNAL-archived.md`. READ, NOT USED.** `:631`:
  `machine-checked measurements: `LsetGraph` weighs 169,683 syntax nodes with`
  A node weight is a size figure and this task priced no size. **Declined as
  evidence.**
- **`archive/dev/LJ-dispatch-index.md`. NOT USED, DECLINED.** `:3`:
  `**Status: ARCHIVED RECORD. It is never rewritten.** These are the 464 dispatch rows`
  It is the task index the POD cutover superseded. It carries no mathematics,
  and none of `liftFo`, `⊨-map`, `Relabel`, `Δ₀` or `LsetGraph` occurs in it.
- **`dev/ARCHIVE.md`. NOT USED, DECLINED.** `:3`:
  `The registry of Bedrock's retired modules. One entry per module, written at`
  W4 does not apply to this task: no module was retired and nothing under
  `src/` changed.

## LITERATURE USED

Every CANDIDATE the block named is answered.

- **`dev/literature/devlin-II5.md`. READ AND USED.** `:102-103`:
  `The chain (c) to (q) then runs: for each ordinal γ of the collapse, the Σ₁`
  `statement "∃v∃z φ(z, v, γ)" is transferred from L_α to X (Σ₁-elementarity,`
  **The textbook does not transport this satisfaction by absoluteness. It
  transports it by Σ₁-elementarity along the collapse.** And its own form (b),
  `:99`, is stated relativized, `L_α ⊨ ∃z φ(z, v, γ)`, not as an absoluteness
  claim. **So the brief's instrument is not the textbook's instrument at this
  step**, which is independent support for the NO-GO and it is why the leg's
  new owed item is a Levy presentation rather than a better proof.
- **`dev/literature/truncation-and-selection.md`. READ AND USED, lightly.**
  `:43`: `same move explicit because he must show the canonical well-order is Σ₁:`
  It confirms that the literature works this leg at Σ₁ and not at Δ₀, which
  agrees with the Devlin reading above. **It settles nothing this task
  measured, so I claim nothing from it beyond agreement.**
- **`dev/literature/glossary-review-2026-08.md`. NOT USED, DECLINED.** It is a
  terminology review. This task proposes no `dev/glossary.toml` entry and names
  no new term.
- **`dev/literature/terms-2026-08.md`. NOT USED, DECLINED.** Same reason. None
  of `Δ₀`, `Σ₁`, `Π₁`, `absoluteness` or `relabelling` occurs in it.
- **`dev/literature/digest.md`. NOT USED, DECLINED.** None of my search terms
  occurs in it.

## FILES

Everything is inside the task's write scope. **Nothing under `src/` changed. I
did not commit and I did not push.**

| file | state |
|---|---|
| `agents/tasks/LJ-1-516/Probe516.agda` | new, green, exit 0 |
| `agents/tasks/LJ-1-516/review-of-graphSat-transports.md` | new, the NO-GO |
| `agents/tasks/LJ-1-516/lj-1.516-report.md` | new, this file |
| `agents/tasks/LJ-1-516/runs/WitnessCheck.agda` | new, green, 8 names resolve |
| `agents/tasks/LJ-1-516/runs/WitnessNoGo.agda` | new, green, the refused name kept as a comment |
| `agents/tasks/LJ-1-516/runs/Sweep516.agda` | new, green, 11 refutations |
| `agents/tasks/LJ-1-516/runs/Sweep516b.agda` | new, green, the 12th |
| `agents/tasks/LJ-1-516/runs/*.out`, `*.time` | new, the runs |

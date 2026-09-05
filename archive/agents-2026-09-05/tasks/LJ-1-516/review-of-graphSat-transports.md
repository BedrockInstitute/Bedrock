# review-of-graphSat-transports

**NO-GO at `graphSat-transports`.** The obligation term is not written. The
obligation TYPE is written and it typechecks
(`agents/tasks/LJ-1-516/Probe516.agda:171-175`, `runs/full-4.out`, exit 0).

**The seam is NOT the obstruction.** The brief expected the possible NO-GO to be
a seam between two delivered laws. It is not. `liftFo-correct` and the `⊨-map`
law compose at the first attempt, and the composite is delivered as `seam`
(`Probe516.agda:72-77`). `runs/w3-0.out` records exit 0 on the first run of the
seam alone.

## WHAT THE TWO LAWS ACTUALLY BUY

`liftFo-correct` (`src/FOL/Manipulation/Bounding.lagda.md:198-199`) equates two
`mapFo` images. **Both sides are `Formula (V ℓ) n`.** Neither side is a
satisfaction.

`⊨-map` (`src/FOL/Manipulation/Relabelling.lagda.md:154-155`) turns a formula
into a satisfaction, but **only in the structure it is given**. At this frame
that structure is `𝒮ᵥ` on both applications.

So the composite relates two OUTER satisfactions:

    seam : (φ : Formula CS.S n) (h : BoundedFo (Below′ α) φ) (γ : SL ^ n)
         → ((map fst γ) AbsL.⊨ᵛ RL.liftFo φ h) ≡ ((map fst γ) ⊨ʟᵛ φ)

`AbsL.⊨ᵛ` and `_⊨ʟᵛ_` are both satisfaction in `𝒮ᵥ`. The quantifiers range over
all of `V ℓ` on both sides. **The two named laws never change the model.**

The briefed statement changes the model twice. It reads the left side in
`AbsL.𝒮M`, which is `𝒮ᵥ ↾ (∈ Lset α)` (`src/L/Hull.lagda.md:153`), and the right
side in `𝒮ʟ`, which is `𝒮ᵥ ↾ isL` (`src/L/Constructible.lagda.md:411`). **Two
model changes are two absoluteness steps, and relabelling supplies neither.**
This is the gap D-10 told me to name.

## THE GAP IS A LEVY GRADE, AND IT IS REFUTED AND NOT MERELY UNBUILT

The tree delivers three instruments for a model change, and every one of them is
gated on a Levy witness for the formula:

| instrument | `file:line` | gate |
|---|---|---|
| `abs₀` | `src/FOL/Absoluteness.lagda.md:122-123` | `Δ₀ φ` |
| `σ₁-up` | `src/FOL/Absoluteness.lagda.md:182-183` | `Σ₁ φ` |
| `π₁-down` | `src/FOL/Absoluteness.lagda.md:187-188` | `Π₁ φ` |

`LsetGraphAt w b` has none of the three, and this is machine-checked by absurd
pattern and not read off the source:

| refutation | `Probe516.agda` |
|---|---|
| `Δ₀ (LsetGraphAt w b) → ⊥*` | `:142-143` |
| `Δ₀ (RL.liftFo (LsetGraphAt w b) h) → ⊥*` | `:147-150` |
| `Σ₁ (LsetGraphAt w b) → ⊥*` | `:157-159` |
| `Π₁ (LsetGraphAt w b) → ⊥*` | `:163-164` |

The cause is syntactic. `Δ₀` has no constructor for `∃̇` or `∀̇`
(`src/FOL/LevyHierarchy.lagda.md:47-57`).
`GraphAt w b = ∃̇ (ApproxAt zero (suc b) ∧̇ Step (suc w) (suc b) zero)`
(`src/L/Coding/Sequence.lagda.md:292`), and
`ApproxAt f a = domAt f a ∧̇ ∀̇ (∀̇ (...))`
(`src/L/Coding/Sequence.lagda.md:287-289`). **An unbounded `∃̇` over a core that
holds an unbounded `∀̇` is outside Δ₀, outside Σ₁ and outside Π₁ at once.**

The second row of the table is the one that blocks. `liftFo` keeps the shape of
the formula (`src/FOL/Manipulation/Bounding.lagda.md:162-174`), so the stage
side inherits the refutation. `AbsL.abs₀` cannot be applied to the lifted
formula either.

## WHAT IS DELIVERED INSTEAD

**`transports-Δ₀` is the briefed statement, proved for the whole Δ₀ family**
(`Probe516.agda:115-122`). It is unconditional in the stage, generic in the
carrier and generic in the formula. It is the maximum the brief's two laws plus
the tree's absoluteness give.

    transports-Δ₀ : (φ : Formula CS.S n) → Δ₀ φ
                  → (h : BoundedFo (Below′ α) φ) → Transports φ h

`transports-Σ₁` (`:125-130`) is the same for the one-direction Σ₁ case.

**So the briefed obligation is not blocked by the instruments. It is blocked by
its formula.** Any Δ₀ formula over `CS.S` transports today. `LsetGraphAt` is not
one.

## WHY THE BRIEFED STATEMENT IS ALSO SUSPECT AS MATHEMATICS

D-10 asks for the truth of the target and not only for its proof. The stage
`graphFo-at-SL` lands at is `sucV σ`, where `σ` is the constant bound that
`mkBoundedFo` computes (`agents/tasks/LJ-1-514/Probe514.agda:136-146`). **That
stage is chosen by the formula's constants and by nothing else. It carries no
closure property.**

`LsetGraphAt` asserts that an approximating function exists
(`src/L/Coding/Sequence.lagda.md:292`). The right-to-left direction of the
briefed equivalence needs that function to lie inside `Lset α`. **That is
`hier-in-stage`**, which `[LJ-1.494]` measured as open
(`agents/tasks/LJ-1-494/lj-1.494-report.md:357-359`) and which `[LJ-1.514]`
named as the blocker it did NOT remove
(`agents/tasks/LJ-1-514/lj-1.514-report.md:254-255`).

**So the equivalence is not merely unproved at this stage. There is a named
reason to expect it false at this stage.** I did not build a term of the
negation, and I do not claim one. What I claim is measured: the three Levy
routes are refuted, and the semantic route needs the blocker the predecessor
declared open.

## THE ROUTE THE TREE ALREADY USES, AND THE BRIEF DID NOT NAME IT

`src/L/Condensation.lagda.md:422-432` transports the SAME formula with no Levy
witness at all:

    ride-only    : ⟨ γ ⊨ LsetGraphAt w b ⟩ → IsOrd (fst (lookup b γ))
                 → fst (lookup w γ) ≡ Lset (fst (lookup b γ))
    ride-defines : IsOrd (fst (lookup b γ))
                 → fst (lookup w γ) ≡ Lset (fst (lookup b γ))
                 → ⟨ γ ⊨ LsetGraphAt w b ⟩

These ride `Lset-only` (`src/L/Hierarchy.lagda.md:334`) and `Lset-defines`
(`src/L/Hierarchy.lagda.md:646`). **They convert satisfaction into a semantic
equation that mentions no carrier.** `fst (lookup w γ) ≡ Lset (fst (lookup b γ))`
is a statement about `V ℓ`, so it moves between carriers for free.

**That is the shape the next brief should order**, and it is the shape that
routes around the Levy grade instead of paying it. The price is the `SL`-side
half: a reading and an introduction for `graphFo-at-SL` at `AbsL.⊨ᵐ`. The
introduction half is `hier-in-stage` again. I did not attempt either, because
the brief forbids `hier-in-stage` and `GraphSatAtStage`.

The tree also delivers a fourth instrument the brief did not name,
`EraseTransfer` (`src/L/Condensation.lagda.md:287-308`). It needs
`countFo φ ≡ 0`. **`[LJ-1.514]` measured `countFo (LsetGraphAt w b) = 664`**
(`agents/tasks/LJ-1-514/lj-1.514-report.md:30`, basis at `:32`), so that route is closed at
this formula too, and the census now has a consumer.

## WHAT THE LITERATURE SAYS ABOUT THE SAME STEP

Devlin does not transport this satisfaction by absoluteness either. The digest
records the transfer as Σ₁-elementarity along the collapse
(`dev/literature/devlin-II5.md:102-103`), and it records the textbook form (b)
as a statement RELATIVIZED to `L_α`, not as an absoluteness claim
(`dev/literature/devlin-II5.md:96-99`). **The textbook route uses an elementary
embedding where this brief used a relabelling.**

## THE VERDICT

**NO-GO at `graphSat-transports`.** W3 is GO: the two laws compose, and `seam`
is delivered. The obligation type forms
(`Probe516.agda:171-175`). The obligation term is not written and this probe
contains no name `graphSat-transports`. The meter's own derivation refuses it:
`runs/witness-nogo.out` records `[NotInScope] Target.graphSat-transports`, exit
42. The eight names this task DOES deliver resolve from outside the probe:
`runs/witness.out`, exit 0.

This file is the critic's input. It does not close the task.

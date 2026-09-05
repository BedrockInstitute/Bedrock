{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.610]  FACE G+ OF [LJ-1.606]'s CROSSING: the stage's inner world
-- satisfies the Sigma-one closure of the graph matrix at the tower's
-- own values.
--
-- THE OBLIGATION IS NOT INHABITED, AND THE STOP IS STATED AT
-- agents/tasks/LJ-1-610/review-of-graph-stage.md.  What lands here is
-- the measurement of the statement (W3, runs/W3.agda, written first and
-- typechecked alone: exit 0 at 3.38 s, peak 668,647,424 bytes, under the
-- brief's two-minute cap, runs/w3-11-final.out) and ONE reduction that
-- prices the remainder.
--
-- THE FINDING, IN FOUR WALLS, each at file:line in the report:
--
--   WALL 1, THE WITNESS.  The face's `∃̇` is read at the stage's inner
--   world, so its witness must be a MEMBER of the stage: Devlin (b)'s
--   "witnessed inside the carrier" (dev/literature/devlin-II5.md:222).
--   The witness would be the approximation (the table) for the tower
--   below the index, and no construction of it exists anywhere in the
--   tree: this is the `Wit` that [LJ-1.598] priced
--   (agents/tasks/LJ-1-598/lj-1.598-report.md) and [LJ-1.578] marked
--   "not built anywhere", reached now from the third side.
--
--   WALL 2, THE CARRIER.  The tree's graph formulas live at the
--   constructible-CLASS carrier (src/L/Coding/Model.lagda.md:70 opens
--   `hPropStructure 𝒮ʟ using ( S )`); the face demands the hull carrier
--   `Formula CI.I.SM 3`; no total relabelling exists, and the only
--   constants the machinery carries are the L-numerals
--   (src/L/Coding/Model.lagda.md:585-586), whose hull-membership is not
--   delivered.  The stage-side twin below (section 2) pays the slide
--   every numeral it needs, and the analysis says why the face itself
--   cannot.
--
--   WALL 3, THE GRADE.  The machine matrix is not Delta-zero (`domAt`
--   and `extAt` use UNBOUNDED quantifiers, src/L/Coding/Model.lagda.md
--   :278 and :662); the tree's Delta-zero matrix carries its bound K as
--   a FOURTH variable slot (src/L/BoundedSubset.lagda.md:111); arity
--   three hosts no kit-grade matrix.  So even a landed G+ here would
--   not assemble into a `Crossing` without a ruling on the arity.
--
--   WALL 4, THE INDEX.  The face quantifies at ALL indices; Devlin's
--   (b) is `(∀γ < α)` over ORDINALS; at a non-ordinal index the graph
--   and the tower disagree ([LJ-1.598]'s reading, the `δ = {{∅}}`
--   computation), so an unguarded graph-grade matrix makes the face
--   refutable at frames whose parameters carry the bad pair.  The
--   ordinal guard below is the syntax that dodges that reading, and it
--   is more syntax than the face's type budgeted.
--
-- WHAT LANDS.  ONE reduction, `graph-stage-from-wit` (section 5): the
-- face at an ORDINAL-GUARDED machine-grade matrix follows from one named
-- residue `WitStage` -- the witness-in-carrier at the ORDINAL pairs --
-- by the guard's vacuity at every non-ordinal index and nothing else.
-- The face itself (section 3) is restated letter for letter and left
-- uninhabited; the obligation name `graph-stage` is DELIBERATELY absent
-- and the meter reports it missing.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M2g" on this pane.  I
-- did not set it.  One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-610.Probe610 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∀̇∈; ∃̇_ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∈; δ-∧; δ-∀∈ )
open import FOL.Manipulation.Relabelling using ( mapFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; isPropIsOrd; Lset )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Sequence {ℓ} lem using ( ApproxAt; StepAt )
open import L.Coding.Bound {ℓ} lem using ( module Bound )
open import L.BoundedSubset {ℓ} lem using ( module DownReflect )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( sucV )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Foundations.HLevels using ( isProp→isSet; isSetΣ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma using ( _×_; _,_ )
open import Cubical.Data.Vec using ( map; _∷_; [] )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ
open SV using ( _∈ˢ_ )

-- =====================================================================
-- THE FRAME.  [LJ-1.606]'s six slots, and the two modules the face
-- reads.  `CI.I.SM` there and `DR.SM` here are the SAME type
-- judgmentally: `HullStage.M` IS `H.T.Hull`
-- (src/L/BoundedSubset.lagda.md:917-918), `IsoInv.SM` is the sigma over
-- `M` (src/L/BoundedSubset.lagda.md:167) and `DownReflect.SM` is the
-- sigma over the same `H.T.Hull`
-- (src/L/BoundedSubset.lagda.md:364-365), both at this instantiation.
-- =====================================================================

module Frame (lam : SV.S) (ordλ : IsOrd lam)
             (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (X : SV.S)
             (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module DR = DownReflect lam ordλ X X⊆Lλ ∅∈λ
  module B = Bound lam ordλ succλ ∅∈λ

  -- ===================================================================
  -- SECTION 1.  THE CARRIER SLIDE.  Numerals into the stage, junk
  -- elsewhere.  Every constant the machine matrix carries is an
  -- L-numeral (they enter at `tagAtL`,
  -- src/L/Coding/Model.lagda.md:585-586), and `Bound.num∈λ` puts each
  -- numeral in the stage from the frame's own four hypotheses
  -- (src/L/Coding/Bound.lagda.md:139-140).  On every constant the
  -- matrix actually carries, `numSL` reads the numeral it names.
  -- ===================================================================

  isSetSL : isSet DR.ASt.SL
  isSetSL = isSetΣ SV.isSetS (λ x → isProp→isSet ((x ∈ˢ Lset lam) .snd))

  numSL : CS.S → DR.ASt.SL
  numSL c =
    Sum.rec
      (λ h → PT.rec→Set isSetSL numf numk h)
      (λ _ → ∅ , DR.H.∅∈Lsetα)
      (lem ((∥ Σ[ k ∈ ℕ ] (c ≡ numeralL k) ∥₁) , squash₁))
    where
    numf : Σ[ k ∈ ℕ ] (c ≡ numeralL k) → DR.ASt.SL
    numf (k , ck) =
      fst c , subst (λ w → ⟨ w ∈ˢ Lset lam ⟩) (sym (cong fst ck)) (B.num∈λ k)
    numk : (u v : Σ[ k ∈ ℕ ] (c ≡ numeralL k)) → numf u ≡ numf v
    numk _ _ = cong₂ _,_ refl ((fst c ∈ˢ Lset lam) .snd _ _)

  -- ===================================================================
  -- SECTION 2.  THE GRAPH MATRIX AND ITS SIGMA-ONE CLOSURE, the widest
  -- unmeasured term, measured alone in runs/W3.agda.  The matrix is the
  -- body of the tree's own `LsetGraphAt`
  -- (src/L/Coding/Sequence.lagda.md:291-292): slot 0 the approximation
  -- z, slot 1 the value v, slot 2 the index gamma.  Devlin's Phi(z, v,
  -- gamma) is this matrix; its existential closure is the Sigma-one
  -- form, and at the stage's inner world the `∃̇` ranges over the
  -- stage's members only.
  -- ===================================================================

  matrixCS : Formula CS.S 3
  matrixCS = ApproxAt zero (suc (suc zero))
           ∧̇ StepAt (suc zero) (suc (suc zero)) zero

  matrixSL : Formula DR.ASt.SL 3
  matrixSL = mapFo numSL matrixCS

  Σ₁Closure : Type (ℓ-suc ℓ)
  Σ₁Closure =
    (q γ : DR.ASt.SL) → fst q ≡ Lset (fst γ)
    → ⟨ (q ∷ γ ∷ []) DR.ASt.AbsL.⊨ᵐ (∃̇ matrixSL) ⟩

  -- ===================================================================
  -- SECTION 3.  THE FACE, RESTATED LETTER FOR LETTER
  -- (agents/tasks/LJ-1-606/Probe606.agda:156-159), at `DR.SM` for
  -- `CI.I.SM` (the judgmental identity is recorded above the frame).
  -- UNINHABITED HERE.  No graph-grade `ψ : Formula DR.SM 3` is
  -- constructible from the delivered tree: WALL 2 (the carrier) stops
  -- the relabelling and WALL 3 (the grade) stops the arity, and WALL 1
  -- (the witness) would stop the proof even if both syntax walls fell.
  -- ===================================================================

  GraphStage : Formula DR.SM 3 → Type (ℓ-suc ℓ)
  GraphStage ψ =
    (q γ : DR.SM) → fst q ≡ Lset (fst γ)
    → ⟨ map DR.inL (q ∷ γ ∷ []) DR.ASt.AbsL.⊨ᵐ mapFo DR.inL (∃̇ ψ) ⟩

  -- ===================================================================
  -- SECTION 4.  THE ORDINAL GUARD, at the stage carrier, spelled
  -- directly at slot 2.  This is `isOrdAt`
  -- (src/L/BoundedSubset.lagda.md:795-798) retargeted from its one slot
  -- to the third of three: transitivity, then transitivity of every
  -- member.  It is Delta-zero (the same witness as `Δ₀-isOrdAt`,
  -- src/L/BoundedSubset.lagda.md:800-803), and at the STAGE's inner
  -- world it still implies `IsOrd`, because Delta-zero formulas are
  -- absolute between a transitive carrier and the ambient
  -- (`abs₀`, src/FOL/Absoluteness.lagda.md:123).
  -- ===================================================================

  guardSL : Formula DR.ASt.SL 3
  guardSL =
    (∀̇∈ (var (suc (suc zero)))
         (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc (suc (suc zero)))))))
    ∧̇
    (∀̇∈ (var (suc (suc zero)))
         (∀̇∈ (var zero)
              (∀̇∈ (var zero)
                   (var zero ∈̇ var (suc (suc zero))))))

  Δ₀-guardSL : Δ₀ guardSL
  Δ₀-guardSL =
    δ-∧ (δ-∀∈ (δ-∀∈ δ-∈)) (δ-∀∈ (δ-∀∈ (δ-∀∈ δ-∈)))

  guardSL-out : (z q γ : DR.ASt.SL)
              → ⟨ (z ∷ q ∷ γ ∷ []) DR.ASt.AbsL.⊨ᵐ guardSL ⟩
              → IsOrd (fst γ)
  guardSL-out z q γ h =
    ( (λ {x} {y} y∈x x∈γ → amb .fst x x∈γ y y∈x)
    , (λ a a∈γ {x} {y} y∈x x∈a → amb .snd a a∈γ x x∈a y y∈x) )
    where
    amb : ⟨ (map fst (z ∷ q ∷ γ ∷ [])) DR.ASt.AbsL.⊨ᵛ guardSL ⟩
    amb = subst ⟨_⟩ (DR.ASt.AbsL.abs₀ Δ₀-guardSL (z ∷ q ∷ γ ∷ [])) h

  -- ===================================================================
  -- SECTION 5.  THE REDUCTION.  The face's stage-side twin, the named
  -- residue, and the term that connects them.  `WitStage` is the
  -- witness-in-carrier at the ORDINAL pairs: Devlin (b)'s forward half
  -- with its own index discipline.  `graph-stage-from-wit` says the
  -- face at the guarded matrix costs EXACTLY that and one vacuity: at
  -- an ordinal index the residue's witness serves (the implication's
  -- algebra needs no guard-reading there), at a non-ordinal index the
  -- guard cannot hold in the stage's inner world, by `guardSL-out`, and
  -- the implication is vacuous at the stage's empty member.
  -- ===================================================================

  GraphStageAt : Formula DR.ASt.SL 3 → Type (ℓ-suc ℓ)
  GraphStageAt χ =
    (q γ : DR.ASt.SL) → fst q ≡ Lset (fst γ)
    → ⟨ (q ∷ γ ∷ []) DR.ASt.AbsL.⊨ᵐ (∃̇ χ) ⟩

  WitStage : Type (ℓ-suc ℓ)
  WitStage =
    (q γ : DR.ASt.SL) → IsOrd (fst γ) → fst q ≡ Lset (fst γ)
    → ⟨ (q ∷ γ ∷ []) DR.ASt.AbsL.⊨ᵐ (∃̇ matrixSL) ⟩

  ψ₀ : Formula DR.ASt.SL 3
  ψ₀ = guardSL ⇒̇ matrixSL

  graph-stage-from-wit : WitStage → GraphStageAt ψ₀
  graph-stage-from-wit w q γ fix =
    Sum.rec
      (λ o → PT.map (λ { (z , hz) → z , (λ _ → hz) }) (w q γ o fix))
      (λ ¬o → ∣ (∅ , DR.H.∅∈Lsetα)
                 , (λ hg → Empty.rec
                     (¬o (guardSL-out (∅ , DR.H.∅∈Lsetα) q γ hg))) ∣₁)
      (lem ((IsOrd (fst γ)) , isPropIsOrd (fst γ)))

  -- ===================================================================
  -- SECTION 6.  THE STATUS.  `graph-stage` itself is NOT defined: no
  -- term of the face's type is constructible from the delivered tree
  -- (the four walls, with `file:line` in the report), and the stop is
  -- stated at agents/tasks/LJ-1-610/review-of-graph-stage.md.  The
  -- meter therefore reports the obligation MISSING (runs/meter-1.out:
  -- `missing exit=42`, `[NotInScope]` at the witness file,
  -- `1 UNRESOLVED of 1`, `probe_red=False`, 3.36 s), and this file's
  -- own green runs are the measurement of everything the statement
  -- costs short of the witness.
  -- ===================================================================

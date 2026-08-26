{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.681] THE GRAPH BRIDGE, UNBOUNDED TO BOUNDED.
--
-- [LJ-1.676] left the `graphBndAt` against `LsetGraphAt` bridge unmeasured
-- and named it the missing piece.  [LJ-1.662] confirmed the bounded graph
-- was never tied to the unbounded one.  This probe builds that one term.
--
--   bnd-vs-unbnd : the unbounded graph satisfaction at one environment
--     carries to the bounded graph at the same environment and the same
--     witness, K the bound.  Direction: unbounded -> bounded.
--
-- The structure of the two matrices is the same except that the bounded
-- side bounds every quantifier by K and replaces the code-set leaf by the
-- bounded `DefBodyB` description.  The term does the K-bounding transport:
-- the witness into K, the domain clause through the `domOut` site fact, and
-- each step clause through the delivered `extAt -> extAtB`.  The code-set leaf
-- rows are the priced cost of W3 and stand as hypotheses: they are the
-- `DefAt` against `DefBodyB` tie that [LJ-1.346] and the `LeafAgree`
-- machinery measure separately, and which the KFacts wall prices at the
-- class carrier.  No postulate; the leaf rows are arguments, not holes.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-681.Probe681 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( domAt )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt; StepAt; StepBody )
open import L.Condensation {ℓ} lem using
  ( module StepB; module ApproxB; module GraphB
  ; extAt→extAtB; domB )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.Data.Vec using ( lookup; _∷_ )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.PropositionalTruncation as PT

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- THE BRIDGE.  Both matrices live at the same environment γ : S ^ n;
-- the bounded leaf content ψs and ψa are parameters, so the term stays
-- generic and the leaf rows are the priced hypotheses.
-- =====================================================================

module _ {n : ℕ} (w b K : Fin n) (γ : S ^ n)
  (ψs : Formula S (8 + n)) (ψa : Formula S (10 + n)) where

  -- The three bounded matrices, at the same environment and the same
  -- witness slots.  SBA is the step the bounded approximation carries.
  module SB  = StepB {1 + n} ψs (suc w) (suc b) zero (suc K)
  module AB  = ApproxB {1 + n} ψa zero (suc b) (suc K)
  module SBA = AB.S
  module GB  = GraphB {n} ψs ψa w b K

  bnd-vs-unbnd :
    -- the graph witness lies in K; the corrected statement is that this
    -- is the canonical approximation, not an arbitrary one
    (fK : (f₀ : S) → ⟨ fst f₀ ∈ fst (lookup K γ) ⟩)
    → -- the domain clause, at the node f₀ ∷ γ: the unbounded domain
      -- carries to the bounded one under the entry and argument facts.
      -- This is the direction [LJ-1.162] takes as its `dom-back` in the
      -- reverse direction; here, unbounded to bounded, it is a site fact
    (domOut : (f₀ : S)
            → ⟨ (f₀ ∷ γ) ⊨ domAt zero (suc b) ⟩
            → ⟨ (f₀ ∷ γ) ⊨ domB zero (suc b) (suc K) ⟩)
    → -- the graph-level step leaf row, at the node z ∷ f₀ ∷ γ: the
      -- unbounded payload of three existentials against the bounded one
    (stepBwd : (f₀ z : S)
             → ⟨ (z ∷ f₀ ∷ γ) ⊨ ∃̇ (∃̇ (∃̇ (StepBody (suc b) zero))) ⟩
             → ⟨ (z ∷ f₀ ∷ γ) ⊨ SB.witB ⟩)
    (stepFwd : (f₀ z : S)
             → ⟨ (z ∷ f₀ ∷ γ) ⊨ SB.witB ⟩
             → ⟨ (z ∷ f₀ ∷ γ) ⊨ ∃̇ (∃̇ (∃̇ (StepBody (suc b) zero))) ⟩)
    → -- the approximation-level step leaf row, at the node
      -- z' ∷ z ∷ c ∷ f₀ ∷ γ
    (apxStepBwd : (z' z c f₀ : S)
                → ⟨ (z' ∷ z ∷ c ∷ f₀ ∷ γ) ⊨ ∃̇ (∃̇ (∃̇ (StepBody (suc zero) (suc (suc zero))))) ⟩
                → ⟨ (z' ∷ z ∷ c ∷ f₀ ∷ γ) ⊨ SBA.witB ⟩)
    (apxStepFwd : (z' z c f₀ : S)
                → ⟨ (z' ∷ z ∷ c ∷ f₀ ∷ γ) ⊨ SBA.witB ⟩
                → ⟨ (z' ∷ z ∷ c ∷ f₀ ∷ γ) ⊨ ∃̇ (∃̇ (∃̇ (StepBody (suc zero) (suc (suc zero))))) ⟩)
    → (hU : ⟨ γ ⊨ LsetGraphAt w b ⟩)
    → ⟨ γ ⊨ GB.graphBndAt ⟩
  bnd-vs-unbnd fK domOut stepBwd stepFwd apxStepBwd apxStepFwd hU =
      PT.map (λ (f₀ , (hApprox , hStep)) →
                let haB = domOut f₀ (hApprox .fst)
                    hsB = λ c cK z zK hApp → apxStep z c f₀ (hApprox .snd c z hApp)
                in (f₀ , ( fK f₀ , ( haB , hsB ) , graphStep f₀ hStep )))
            hU
    where
    -- The graph-level step clause, node f₀ ∷ γ.  The delivered frame
    -- transfer does the extAt -> extAtB; the leaf rows are the cost.
    graphStep : (f₀ : S)
              → ⟨ (f₀ ∷ γ) ⊨ StepAt (suc w) (suc b) zero ⟩
              → ⟨ (f₀ ∷ γ) ⊨ SB.stepBndAt ⟩
    graphStep f₀ h = extAt→extAtB {1 + n} (suc w) (suc K) SB.witB
                        (∃̇ (∃̇ (∃̇ (StepBody (suc b) zero)))) (f₀ ∷ γ)
                        (λ z → stepFwd f₀ z)
                        (λ z → stepBwd f₀ z)
                        h

    -- The approximation-level step clause, node z ∷ c ∷ f₀ ∷ γ.  The
    -- unbounded step is stronger (no K bound), so the bounded frame's
    -- membership proofs go unused; the leaf rows are the cost.
    apxStep : (z c f₀ : S)
            → ⟨ (z ∷ c ∷ f₀ ∷ γ) ⊨ StepAt zero (suc zero) (suc (suc zero)) ⟩
            → ⟨ (z ∷ c ∷ f₀ ∷ γ) ⊨ SBA.stepBndAt ⟩
    apxStep z c f₀ h = extAt→extAtB {3 + n} zero (suc (suc (suc K))) SBA.witB
                        (∃̇ (∃̇ (∃̇ (StepBody (suc zero) (suc (suc zero))))))
                        (z ∷ c ∷ f₀ ∷ γ)
                        (λ z' → apxStepFwd z' z c f₀)
                        (λ z' → apxStepBwd z' z c f₀)
                        h

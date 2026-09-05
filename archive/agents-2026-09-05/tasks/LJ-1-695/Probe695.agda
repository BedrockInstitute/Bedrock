{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.695] THE GRAPH BRIDGE, BOUNDED TO UNBOUNDED.
--
-- [LJ-1.681] delivered unbounded to bounded as `bnd-vs-unbnd` and
-- named `Graph.up` as the start of the other direction.
-- `Graph.up` is already delivered at
-- agents/tasks/LJ-1-162/ProbeLJ1162A.agda:218-222.  This probe does
-- not rebuild it.  It instantiates that term at [LJ-1.681]'s generic
-- carrier and fills the two hypotheses `approx-up` and `step-up`
-- from the delivered `extAtB→extAt` (src/L/Condensation.lagda.md:2514)
-- and from [LJ-1.162]'s `Approx.up` (ProbeLJ1162A.agda:201-204).
--
--   bnd-to-unbnd : the bounded graph satisfaction at one environment
--     carries to the unbounded graph at the same environment.
--     Direction: bounded -> unbounded.
--
-- The outer existential bound is discharged for free (`∃∈-up` throws
-- the membership away).  The inner `extAt` frames still need `inK`,
-- because `extAt` is an extensionality.  The approximation's two
-- universals still need `entryK`, because a bounded `∀̇∈` is weaker
-- than an unbounded `∀̇`.  The leaf rows are the same hypotheses
-- [LJ-1.681] took.  No postulate; the site facts are arguments, not
-- holes.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-695.Probe695 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∧̇_; ∃̇_; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( appAt; domAt )
open import L.Coding.Sequence {ℓ} lem using
  ( LsetGraphAt; StepAt; StepBody; ApproxAt )
open import L.Condensation {ℓ} lem using
  ( module StepB; module ApproxB; module GraphB
  ; extAtB→extAt; domB )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.Data.Vec using ( lookup; _∷_ )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.PropositionalTruncation as PT

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- Generic kit.  Written once.  A bounded existential reaches the
-- unbounded one for free.  This is Block 0 of [LJ-1.162], not a
-- rebuild of `Graph.up`.
∃∈-up : ∀ {n} (K : Fin n) (φB φ : Formula S (suc n)) (γ : S ^ n)
      → ((x : S) → ⟨ (x ∷ γ) ⊨ φB ⟩ → ⟨ (x ∷ γ) ⊨ φ ⟩)
      → ⟨ γ ⊨ ∃̇∈ (var K) φB ⟩ → ⟨ γ ⊨ ∃̇ φ ⟩
∃∈-up K φB φ γ f = PT.map (λ { (x , (_ , h)) → x , f x h })

-- =====================================================================
-- THE BRIDGE.  Both matrices live at the same environment γ : S ^ n;
-- the bounded leaf content ψs and ψa are parameters, so the term stays
-- generic and the leaf rows plus the three membership facts are the
-- priced hypotheses.  This is `Graph.up` at [LJ-1.681]'s carrier.
-- =====================================================================

module _ {n : ℕ} (w b K : Fin n) (γ : S ^ n)
  (ψs : Formula S (8 + n)) (ψa : Formula S (10 + n)) where

  module SB  = StepB {1 + n} ψs (suc w) (suc b) zero (suc K)
  module AB  = ApproxB {1 + n} ψa zero (suc b) (suc K)
  module SBA = AB.S
  module GB  = GraphB {n} ψs ψa w b K

  bnd-to-unbnd :
    (domBack : (f₀ : S)
             → ⟨ (f₀ ∷ γ) ⊨ domB zero (suc b) (suc K) ⟩
             → ⟨ (f₀ ∷ γ) ⊨ domAt zero (suc b) ⟩)
    → (stepBwd : (f₀ z : S)
               → ⟨ (z ∷ f₀ ∷ γ) ⊨ ∃̇ (∃̇ (∃̇ (StepBody (suc b) zero))) ⟩
               → ⟨ (z ∷ f₀ ∷ γ) ⊨ SB.witB ⟩)
      (stepFwd : (f₀ z : S)
               → ⟨ (z ∷ f₀ ∷ γ) ⊨ SB.witB ⟩
               → ⟨ (z ∷ f₀ ∷ γ) ⊨ ∃̇ (∃̇ (∃̇ (StepBody (suc b) zero))) ⟩)
    → (apxStepBwd : (z' z c f₀ : S)
                  → ⟨ (z' ∷ z ∷ c ∷ f₀ ∷ γ) ⊨ ∃̇ (∃̇ (∃̇ (StepBody (suc zero) (suc (suc zero))))) ⟩
                  → ⟨ (z' ∷ z ∷ c ∷ f₀ ∷ γ) ⊨ SBA.witB ⟩)
      (apxStepFwd : (z' z c f₀ : S)
                  → ⟨ (z' ∷ z ∷ c ∷ f₀ ∷ γ) ⊨ SBA.witB ⟩
                  → ⟨ (z' ∷ z ∷ c ∷ f₀ ∷ γ) ⊨ ∃̇ (∃̇ (∃̇ (StepBody (suc zero) (suc (suc zero))))) ⟩)
    → (stepK : (f₀ z : S)
             → ⟨ (z ∷ f₀ ∷ γ) ⊨ ∃̇ (∃̇ (∃̇ (StepBody (suc b) zero))) ⟩
             → ⟨ fst z ∈ fst (lookup K γ) ⟩)
    → (apxStepK : (z' z c f₀ : S)
                → ⟨ (z' ∷ z ∷ c ∷ f₀ ∷ γ) ⊨ ∃̇ (∃̇ (∃̇ (StepBody (suc zero) (suc (suc zero))))) ⟩
                → ⟨ fst z' ∈ fst (lookup K γ) ⟩)
    → (entryK : (c z f₀ : S)
              → ⟨ (z ∷ c ∷ f₀ ∷ γ) ⊨ appAt (suc (suc zero)) (suc zero) zero ⟩
              → ⟨ fst c ∈ fst (lookup K γ) ⟩ × ⟨ fst z ∈ fst (lookup K γ) ⟩)
    → (hB : ⟨ γ ⊨ GB.graphBndAt ⟩)
    → ⟨ γ ⊨ LsetGraphAt w b ⟩
  bnd-to-unbnd domBack stepBwd stepFwd apxStepBwd apxStepFwd stepK apxStepK entryK hB =
    ∃∈-up K
      (AB.approxBndAt ∧̇ SB.stepBndAt)
      (ApproxAt zero (suc b) ∧̇ StepAt (suc w) (suc b) zero)
      γ
      (λ f₀ hh → approxUp f₀ (hh .fst) , graphStep f₀ (hh .snd))
      hB
    where
    -- The graph-level step clause, node f₀ ∷ γ.  The delivered frame
    -- transfer does the extAtB -> extAt; the leaf rows plus stepK
    -- (the satisfiers-in-K fact) are the cost.  This is the reverse
    -- of [LJ-1.681]'s `graphStep`.
    graphStep : (f₀ : S)
              → ⟨ (f₀ ∷ γ) ⊨ SB.stepBndAt ⟩
              → ⟨ (f₀ ∷ γ) ⊨ StepAt (suc w) (suc b) zero ⟩
    graphStep f₀ h = extAtB→extAt {1 + n} (suc w) (suc K) SB.witB
                        (∃̇ (∃̇ (∃̇ (StepBody (suc b) zero)))) (f₀ ∷ γ)
                        (λ z → stepFwd f₀ z)
                        (λ z → stepBwd f₀ z)
                        (λ z hz → stepK f₀ z hz)
                        h

    -- The approximation-level step clause, node z ∷ c ∷ f₀ ∷ γ.
    -- Same delivered transfer; apxStepK is the extra cost this
    -- direction pays and [LJ-1.681] did not.
    apxStep : (z c f₀ : S)
            → ⟨ (z ∷ c ∷ f₀ ∷ γ) ⊨ SBA.stepBndAt ⟩
            → ⟨ (z ∷ c ∷ f₀ ∷ γ) ⊨ StepAt zero (suc zero) (suc (suc zero)) ⟩
    apxStep z c f₀ h = extAtB→extAt {3 + n} zero (suc (suc (suc K))) SBA.witB
                        (∃̇ (∃̇ (∃̇ (StepBody (suc zero) (suc (suc zero))))))
                        (z ∷ c ∷ f₀ ∷ γ)
                        (λ z' → apxStepFwd z' z c f₀)
                        (λ z' → apxStepBwd z' z c f₀)
                        (λ z' hz → apxStepK z' z c f₀ hz)
                        h

    -- [LJ-1.162]'s Approx.up at this carrier: domain through
    -- `domBack`, the two bounded universals through `entryK`.
    approxUp : (f₀ : S)
             → ⟨ (f₀ ∷ γ) ⊨ AB.approxBndAt ⟩
             → ⟨ (f₀ ∷ γ) ⊨ ApproxAt zero (suc b) ⟩
    approxUp f₀ (hd , hq) = domBack f₀ hd
      , λ c z ap → apxStep z c f₀
          (hq c (entryK c z f₀ ap .fst) z (entryK c z f₀ ap .snd) ap)

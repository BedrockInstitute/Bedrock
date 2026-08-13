{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1124A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∃̇_; ∀̇_; ∃̇∈; ∀̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ}
  using ( appAt; domAt )
open import L.Coding.Powerset {ℓ} lem using ( DefAt )
open import L.Coding.Sequence {ℓ} lem
  using ( StepAt; StepBody; ApproxAt; LsetGraphAt
        ; LsetGraph-in; LsetGraph-out )
open import L.Condensation {ℓ} lem
  using ( module StepB; module ApproxB; module GraphB
        ; extAtB→extAt; extAt→extAtB; domB )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Vec using ( lookup )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- The story-side bounded step bridge.  For one StepB instance at
-- arity m, a leaf agreement between StepB.leafB and the delivered
-- DefAt, plus the outer witness bounds and the satisfiers-in-K fact,
-- close both directions against StepAt.
module StepBridge {m : ℕ}
  (ψ : Formula S (suc (suc (suc (4 + m)))))
  (v b f K : Fin m) (γ : S ^ m)
  (leaf-out : (δ : S ^ (4 + m))
            → ⟨ δ ⊨ StepB.leafB ψ v b f K ⟩
            → ⟨ δ ⊨ DefAt zero (suc zero) ⟩)
  (leaf-in : (δ : S ^ (4 + m))
           → ⟨ δ ⊨ DefAt zero (suc zero) ⟩
           → ⟨ δ ⊨ StepB.leafB ψ v b f K ⟩)
  (outer : (z : S) → (c w d : S)
         → ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ StepBody b f ⟩
         → (_×_ (⟨ fst w ∈ fst (lookup K γ) ⟩)
                (⟨ fst d ∈ fst (lookup K γ) ⟩)))
  (satK : (z : S)
        → ⟨ (z ∷ γ) ⊨ ∃̇ (∃̇ (∃̇ (StepBody b f))) ⟩
        → ⟨ fst z ∈ fst (lookup K γ) ⟩) where

  private
    Φ : Formula S (suc m)
    Φ = ∃̇ (∃̇ (∃̇ (StepBody b f)))

    witB : Formula S (suc m)
    witB = StepB.witB ψ v b f K

    body-out : (δ : S ^ (4 + m))
             → ⟨ δ ⊨ StepB.bodyB ψ v b f K ⟩
             → ⟨ δ ⊨ StepBody b f ⟩
    body-out δ h = ( h .fst
                   , ( h .snd .fst
                     , ( leaf-out δ (h .snd .snd .fst)
                       , h .snd .snd .snd ) ) )

    body-in : (δ : S ^ (4 + m))
            → ⟨ δ ⊨ StepBody b f ⟩
            → ⟨ δ ⊨ StepB.bodyB ψ v b f K ⟩
    body-in δ h = ( h .fst
                  , ( h .snd .fst
                    , ( leaf-in δ (h .snd .snd .fst)
                      , h .snd .snd .snd ) ) )

    wit-out : (z : S)
            → ⟨ (z ∷ γ) ⊨ witB ⟩
            → ⟨ (z ∷ γ) ⊨ Φ ⟩
    wit-out z = PT.rec (snd ((z ∷ γ) ⊨ Φ))
      (λ { (c , _ , hw) →
        PT.rec (snd ((z ∷ γ) ⊨ Φ))
          (λ { (w , _ , hd) →
            PT.rec (snd ((z ∷ γ) ⊨ Φ))
              (λ { (d , _ , hb) →
                ∣ c , ∣ w , ∣ d , body-out (d ∷ w ∷ c ∷ z ∷ γ) hb ∣₁ ∣₁ ∣₁ })
              hd })
          hw })

    wit-in : (z : S)
           → ⟨ (z ∷ γ) ⊨ Φ ⟩
           → ⟨ (z ∷ γ) ⊨ witB ⟩
    wit-in z = PT.rec (snd ((z ∷ γ) ⊨ witB))
      (λ { (c , hw) →
        PT.rec (snd ((z ∷ γ) ⊨ witB))
          (λ { (w , hd) →
            PT.rec (snd ((z ∷ γ) ⊨ witB))
              (λ { (d , hb) →
                let wk , dk = outer z c w d hb
                in ∣ c , (hb .fst
                        , ∣ w , (wk
                                , ∣ d , (dk
                                        , body-in (d ∷ w ∷ c ∷ z ∷ γ) hb) ∣₁)
                          ∣₁) ∣₁ })
              hd })
          hw })

  step-out : ⟨ γ ⊨ StepB.stepBndAt ψ v b f K ⟩
           → ⟨ γ ⊨ StepAt v b f ⟩
  step-out = extAtB→extAt v K witB Φ γ wit-out wit-in satK

  step-in : ⟨ γ ⊨ StepAt v b f ⟩
          → ⟨ γ ⊨ StepB.stepBndAt ψ v b f K ⟩
  step-in = extAt→extAtB v K witB Φ γ wit-out wit-in

-- The bounded approximation bridge.  One ApproxB instance at arity m,
-- given the two-way domain agreement, the recorded-pair components-in-K
-- fact, and the inner step bridge, closes both directions against the
-- delivered ApproxAt.
module ApproxBridge {m : ℕ}
  (ψ' : Formula S (suc (suc (suc (6 + m)))))
  (f a K : Fin m) (γ : S ^ m)
  (dom-out : ⟨ γ ⊨ domB f a K ⟩ → ⟨ γ ⊨ domAt f a ⟩)
  (dom-in : ⟨ γ ⊨ domAt f a ⟩ → ⟨ γ ⊨ domB f a K ⟩)
  (entryK : (x y : S)
          → ⟨ (y ∷ x ∷ γ) ⊨ appAt (suc (suc f)) (suc zero) zero ⟩
          → (_×_ (⟨ fst x ∈ fst (lookup K γ) ⟩)
                (⟨ fst y ∈ fst (lookup K γ) ⟩)))
  (step-out : (x y : S)
            → ⟨ (y ∷ x ∷ γ) ⊨
                 StepB.stepBndAt ψ' zero (suc zero) (suc (suc f)) (suc (suc K)) ⟩
            → ⟨ (y ∷ x ∷ γ) ⊨
                 StepAt zero (suc zero) (suc (suc f)) ⟩)
  (step-in : (x y : S)
           → ⟨ (y ∷ x ∷ γ) ⊨
                StepAt zero (suc zero) (suc (suc f)) ⟩
           → ⟨ (y ∷ x ∷ γ) ⊨
                StepB.stepBndAt ψ' zero (suc zero) (suc (suc f)) (suc (suc K)) ⟩) where

  private
    all-out : ⟨ γ ⊨
                ∀̇∈ (var K)
                  (∀̇∈ (var (suc K))
                    (appAt (suc (suc f)) (suc zero) zero
                    ⇒̇ StepB.stepBndAt ψ' zero (suc zero) (suc (suc f)) (suc (suc K)))) ⟩
            → (x y : S)
            → ⟨ (y ∷ x ∷ γ) ⊨ appAt (suc (suc f)) (suc zero) zero ⟩
            → ⟨ (y ∷ x ∷ γ) ⊨ StepAt zero (suc zero) (suc (suc f)) ⟩
    all-out h x y p =
      let xk , yk = entryK x y p
      in step-out x y (h x xk y yk p)

    all-in : ((x y : S)
            → ⟨ (y ∷ x ∷ γ) ⊨ appAt (suc (suc f)) (suc zero) zero ⟩
            → ⟨ (y ∷ x ∷ γ) ⊨ StepAt zero (suc zero) (suc (suc f)) ⟩)
           → ⟨ γ ⊨
                ∀̇∈ (var K)
                  (∀̇∈ (var (suc K))
                    (appAt (suc (suc f)) (suc zero) zero
                    ⇒̇ StepB.stepBndAt ψ' zero (suc zero) (suc (suc f)) (suc (suc K)))) ⟩
    all-in h = λ x _ y _ p → step-in x y (h x y p)

  approx-out : ⟨ γ ⊨ ApproxB.approxBndAt ψ' f a K ⟩
             → ⟨ γ ⊨ ApproxAt f a ⟩
  approx-out h = dom-out (h .fst) , all-out (h .snd)

  approx-in : ⟨ γ ⊨ ApproxAt f a ⟩
            → ⟨ γ ⊨ ApproxB.approxBndAt ψ' f a K ⟩
  approx-in h = dom-in (h .fst) , all-in (h .snd)

-- The bounded graph bridge.  One GraphB instance at arity m, given the
-- inner approximation and step bridges and the witness-in-K fact,
-- closes both directions against LsetGraphAt.
module GraphBridge {m : ℕ}
  (ψs : Formula S (suc (suc (suc (5 + m)))))
  (ψa : Formula S (suc (suc (suc (7 + m)))))
  (w b K : Fin m) (γ : S ^ m)
  (approx-out : (h : S)
              → ⟨ (h ∷ γ) ⊨ ApproxB.approxBndAt ψa zero (suc b) (suc K) ⟩
              → ⟨ (h ∷ γ) ⊨ ApproxAt zero (suc b) ⟩)
  (approx-in : (h : S)
             → ⟨ (h ∷ γ) ⊨ ApproxAt zero (suc b) ⟩
             → ⟨ (h ∷ γ) ⊨ ApproxB.approxBndAt ψa zero (suc b) (suc K) ⟩)
  (step-out : (h : S)
            → ⟨ (h ∷ γ) ⊨ StepB.stepBndAt ψs (suc w) (suc b) zero (suc K) ⟩
            → ⟨ (h ∷ γ) ⊨ StepAt (suc w) (suc b) zero ⟩)
  (step-in : (h : S)
           → ⟨ (h ∷ γ) ⊨ StepAt (suc w) (suc b) zero ⟩
           → ⟨ (h ∷ γ) ⊨ StepB.stepBndAt ψs (suc w) (suc b) zero (suc K) ⟩)
  (witnessK : (h : S)
            → ⟨ (h ∷ γ) ⊨ ApproxAt zero (suc b) ⟩
            → ⟨ (h ∷ γ) ⊨ StepAt (suc w) (suc b) zero ⟩
            → ⟨ fst h ∈ fst (lookup K γ) ⟩) where

  graph-out : ⟨ γ ⊨ GraphB.graphBndAt ψs ψa w b K ⟩
            → ⟨ γ ⊨ LsetGraphAt w b ⟩
  graph-out = PT.map
    (λ { (h , _ , hahs) → h , (approx-out h (hahs .fst) , step-out h (hahs .snd)) })

  graph-in : ⟨ γ ⊨ LsetGraphAt w b ⟩
           → ⟨ γ ⊨ GraphB.graphBndAt ψs ψa w b K ⟩
  graph-in h = PT.rec (snd ((γ) ⊨ GraphB.graphBndAt ψs ψa w b K))
    (λ { (h , ha , hs) →
      ∣ h , (witnessK h ha hs
            , (approx-in h ha , step-in h hs)) ∣₁ })
    (LsetGraph-out w b γ h)

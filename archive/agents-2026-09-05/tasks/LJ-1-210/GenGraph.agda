{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure; Transitive; _↾_ )
open import V.Hierarchy using ( 𝒮ᵥ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆ ) renaming ( module InfinitySet to Inf )
open Inf using ( #_; sucV )

module LJ-1-210.GenGraph {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (M : V ℓ → hProp (ℓ-suc ℓ))
  (M-trans : Transitive (𝒮ᵥ {ℓ}) M)
  (numeralL : ℕ → Σ[ x ∈ V ℓ ] ⟨ M x ⟩)
  (numeralL-fst : (k : ℕ) → fst (numeralL k) ≡ # k)
  (pairʟ : (a b : Σ[ x ∈ V ℓ ] ⟨ M x ⟩) → Σ[ x ∈ V ℓ ] ⟨ M x ⟩)
  (pairʟ-fst : (a b : Σ[ x ∈ V ℓ ] ⟨ M x ⟩)
             → fst (pairʟ a b) ≡ ⁅ fst a , fst b ⁆)
  (sucʟ : Σ[ x ∈ V ℓ ] ⟨ M x ⟩ → Σ[ x ∈ V ℓ ] ⟨ M x ⟩)
  (sucʟ-fst : (a : Σ[ x ∈ V ℓ ] ⟨ M x ⟩) → fst (sucʟ a) ≡ sucV (fst a))
  where

open import FOL.Syntax using ( Formula; var; con; _≐_; _∧̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Coding {ℓ} using ( pr )
import LJ-1-210.GenModel
module GM = LJ-1-210.GenModel {ℓ} M M-trans
              numeralL numeralL-fst pairʟ pairʟ-fst sucʟ sucʟ-fst
open GM
  using ( closedAt; domAt; appAt; appAt-adequate
        ; memClauseAt; eqClauseAt; andClauseAt; orClauseAt; impClauseAt
        ; negClauseAt; topClauseAt; botClauseAt; existClauseAt; forallClauseAt
        ; allInClauseAt; exInClauseAt )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure (𝒮ᵥ {ℓ} ↾ M)

module AbsL = FOL.Absoluteness.Single (𝒮ᵥ {ℓ}) M M-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
private
  Ci Ti Bi : ∀ {n} → Fin (suc (suc (suc n)))
  Ci = suc (suc zero)
  Ti = suc zero
  Bi = zero

  sh3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  sh3 i = suc (suc (suc i))

twelveAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
twelveAt C T B =
  memClauseAt C T B ∧̇ (eqClauseAt C T B
  ∧̇ (andClauseAt C T ∧̇ (orClauseAt C T
  ∧̇ (impClauseAt C T B ∧̇ (negClauseAt C T B
  ∧̇ (topClauseAt C T B ∧̇ (botClauseAt C T
  ∧̇ (existClauseAt C T B ∧̇ (forallClauseAt C T B
  ∧̇ (allInClauseAt C T B ∧̇ exInClauseAt C T B))))))))))

private
  satGraphOn : ∀ {n} → Formula S (suc (suc (suc n)))
             → Fin n → Fin n → Formula S n
  satGraphOn pin x y =
    ∃̇ (∃̇ (∃̇ ( pin
            ∧̇ ( closedAt Ci
            ∧̇ ( domAt Ti Ci
            ∧̇ ( appAt Ti (sh3 x) (sh3 y)
            ∧̇ twelveAt Ci Ti Bi ))))))
private
  GraphWitOn : ∀ {n} → S → Fin n → Fin n → S ^ n → Type (ℓ-suc ℓ)
  GraphWitOn W x y γ = Σ[ C ∈ S ] (Σ[ T ∈ S ] (Σ[ b ∈ S ]
    ((fst b ≡ fst W)
     × (⟨ (b ∷ T ∷ C ∷ γ) ⊨ closedAt Ci ⟩
        × (⟨ (b ∷ T ∷ C ∷ γ) ⊨ domAt Ti Ci ⟩
           × (⟨ pr (fst (lookup x γ)) (fst (lookup y γ)) ∈ fst T ⟩
              × ⟨ (b ∷ T ∷ C ∷ γ) ⊨ twelveAt Ci Ti Bi ⟩))))))

  module _ {n : ℕ} (pin : Formula S (suc (suc (suc n)))) (W : S)
           (x y : Fin n) (γ : S ^ n) where

    graphOn-in : ((b T C : S) → fst b ≡ fst W → ⟨ (b ∷ T ∷ C ∷ γ) ⊨ pin ⟩)
               → ∥ GraphWitOn W x y γ ∥₁ → ⟨ γ ⊨ satGraphOn pin x y ⟩
    graphOn-in rd = PT.map
      (λ { (C , (T , (b , (eb , (hc , (hd , (ha , h12))))))) → C
         , ∣ T , ∣ b , (rd b T C eb , (hc , (hd
           , ( subst ⟨_⟩
                 (sym (appAt-adequate Ti (sh3 x) (sh3 y) (b ∷ T ∷ C ∷ γ))) ha
             , h12 )))) ∣₁ ∣₁ })

    graphOn-out : ((b T C : S) → ⟨ (b ∷ T ∷ C ∷ γ) ⊨ pin ⟩ → fst b ≡ fst W)
                → ⟨ γ ⊨ satGraphOn pin x y ⟩ → ∥ GraphWitOn W x y γ ∥₁
    graphOn-out rd = PT.rec squash₁
      (λ { (C , hT) → PT.rec squash₁
        (λ { (T , hb) → PT.map
          (λ { (b , (eb , (hc , (hd , (ha , h12))))) →
            C , (T , (b , (rd b T C eb , (hc , (hd
              , ( subst ⟨_⟩
                    (appAt-adequate Ti (sh3 x) (sh3 y) (b ∷ T ∷ C ∷ γ)) ha
                , h12 )))))) })
          hb })
        hT })
GraphWitAt : ∀ {n} → Fin n → Fin n → Fin n → S ^ n → Type (ℓ-suc ℓ)
GraphWitAt B x y γ = GraphWitOn (lookup B γ) x y γ

-- SEALED (P-t), and the reason is a measurement rather than a preference.
-- This formula is a conjunct of three larger ones, and every consumer of
-- those splits them.  A split REDUCES the conjunct's type while the
-- consumer's own signature names it FOLDED, so the conversion checker walks
-- the whole tree to see that the two agree.  Open, that one coercion cost
-- 2,459 ms at the site this seal serves; sealed, both sides are the same
-- stuck head and the check is syntactic.  The two readers below are the
-- official unfolding, so no consumer needs `unfolding` to build or read a
-- witness.
opaque
  satGraphAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  satGraphAt B x y = satGraphOn (var Bi ≐ var (sh3 B)) x y

opaque
  unfolding satGraphAt

  graphAt-in : ∀ {n} (B x y : Fin n) (γ : S ^ n)
             → ∥ GraphWitAt B x y γ ∥₁ → ⟨ γ ⊨ satGraphAt B x y ⟩
  graphAt-in B x y γ =
    graphOn-in (var Bi ≐ var (sh3 B)) (lookup B γ) x y γ (λ _ _ _ e → e)

  graphAt-out : ∀ {n} (B x y : Fin n) (γ : S ^ n)
              → ⟨ γ ⊨ satGraphAt B x y ⟩ → ∥ GraphWitAt B x y γ ∥₁
  graphAt-out B x y γ =
    graphOn-out (var Bi ≐ var (sh3 B)) (lookup B γ) x y γ (λ _ _ _ h → h)
satGraph : S → Formula S 2
satGraph B = satGraphOn (var Bi ≐ con B) (suc zero) zero

GraphWit : (B x y : S) → Type (ℓ-suc ℓ)
GraphWit B x y = GraphWitOn B (suc zero) zero (y ∷ x ∷ [])

graph-in : (B x y : S) → ∥ GraphWit B x y ∥₁ → ⟨ (y ∷ x ∷ []) ⊨ satGraph B ⟩
graph-in B x y =
  graphOn-in (var Bi ≐ con B) B (suc zero) zero (y ∷ x ∷ []) (λ _ _ _ e → e)

graph-out : (B x y : S) → ⟨ (y ∷ x ∷ []) ⊨ satGraph B ⟩ → ∥ GraphWit B x y ∥₁
graph-out B x y =
  graphOn-out (var Bi ≐ con B) B (suc zero) zero (y ∷ x ∷ []) (λ _ _ _ h → h)

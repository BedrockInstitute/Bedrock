{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.298] probe.  THE PRICE OF RE-INSTANTIATING `TagAgree` GENERICALLY
-- IN THE CLASS.
--
-- `src/L/Condensation.lagda.md:6670` delivers `TagAgree` at the CLASS
-- carrier: `S` is the carrier of `𝒮ʟ = 𝒮ᵥ ↾ isL`
-- (`src/L/Constructible.lagda.md:410`), the reading `⊨` is
-- `FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans` at `:73`, and the codings
-- `tagAtL`/`prAtL` are `L.Coding.Model`'s, which opens the same class.
--
-- This file is the SAME module with the class made a PARAMETER, the way
-- `[LJ-1.238]`'s `GenSequence` parameterizes it: the eight parameters are
-- `GenModel`'s (`agents/tasks/LJ-1-210/GenModel.agda:12-24`), and the
-- codings come from `GenModel` applied at them.  `PairIs`, `tagBS` and the
-- `TagAgree` body are copied VERBATIM from
-- `src/L/Condensation.lagda.md:6666-6669`, `:1484-1487` and `:6670-6697`.
-- The diff against the original is the task's number.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth

open import FOL.ZFStructure using ( module hPropStructure; Transitive; _↾_ )
open import FOL.Syntax using ( Formula; var; _≐_; _∧̇_; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy using ( 𝒮ᵥ )
open import V.Coding using ( pr )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆ ) renaming ( module InfinitySet to Inf )
open Inf using ( #_; sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

import LJ-1-210.GenModel

module LJ-1-298.GenTagAgree {ℓ : Level}
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

module GM = LJ-1-210.GenModel {ℓ} M M-trans
              numeralL numeralL-fst pairʟ pairʟ-fst sucʟ sucʟ-fst
open GM using ( prAtL; prAtL-adequate; tagAtL; tagAtL-adequate )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure (𝒮ᵥ {ℓ} ↾ M) using ( S )
module AbsL = FOL.Absoluteness.Single (𝒮ᵥ {ℓ}) M (λ {x} {y} → M-trans {x} {y})
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- BELOW THIS LINE: VERBATIM FROM `src/L/Condensation.lagda.md`.
-- `PairIs` from `:6667-6669`, `tagBS` from `:1484-1487`, `TagAgree`
-- from `:6670-6697`.  NOTHING is edited but the indentation of the
-- `private` block, which the original carries at the same depth.
-- =====================================================================

private
  PairIs : V ℓ → V ℓ → Ω
  PairIs a p = (a ≡ p) , setIsSet a p

tagBS : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
tagBS s tag x K =
  ∃̇∈ (var K) ((var zero ≐ var (suc tag))
            ∧̇ prAtL (suc s) zero (suc x))

module TagAgree {n : ℕ} (s tag x K : Fin n) (γ : S ^ n) (k : ℕ)
  (tagEq : fst (lookup tag γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup K γ) ⟩) where

  out : ⟨ γ ⊨ tagAtL s k x ⟩ → ⟨ γ ⊨ tagBS s tag x K ⟩
  out h = ∣ numeralL k , ( numK , ( sym tagEq , hp ) ) ∣₁
    where
    h' : ⟨ PairIs (fst (lookup s γ)) (pr (fst (numeralL k)) (fst (lookup x γ))) ⟩
    h' = subst ⟨_⟩
           (cong (λ w → PairIs (fst (lookup s γ)) (pr w (fst (lookup x γ))))
             (sym (numeralL-fst k)))
           (subst ⟨_⟩ (tagAtL-adequate s k x γ) h)
    hp : ⟨ (numeralL k ∷ γ) ⊨ prAtL (suc s) zero (suc x) ⟩
    hp = subst ⟨_⟩ (sym (prAtL-adequate {suc n} (suc s) zero (suc x) (numeralL k ∷ γ))) h'

  back : ⟨ γ ⊨ tagBS s tag x K ⟩ → ⟨ γ ⊨ tagAtL s k x ⟩
  back h = subst ⟨_⟩ (sym (tagAtL-adequate s k x γ))
    (subst (λ u → fst (lookup s γ) ≡ pr u (fst (lookup x γ)))
      (numeralL-fst k) go)
    where
    go : fst (lookup s γ) ≡ pr (fst (numeralL k)) (fst (lookup x γ))
    go = PT.rec (snd (PairIs (fst (lookup s γ))
                       (pr (fst (numeralL k)) (fst (lookup x γ)))))
      (λ { (t , (tK , (te , tp))) →
        subst (λ u → fst (lookup s γ) ≡ pr u (fst (lookup x γ)))
          (te ∙ tagEq)
          (subst ⟨_⟩ (prAtL-adequate {suc n} (suc s) zero (suc x) (t ∷ γ)) tp) })
      h

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.302] probe, file 1 of the pricing.  THE PORT OF `DomainAgree`
-- WITH THE CLASS AS A PARAMETER.
--
-- `DomainAgree` sits at `src/L/Condensation.lagda.md:6510`.  It is one
-- of the DIRTY SEVEN: its body names `domB`, the chapter's bounded
-- domain coding at `:1746-1753`, whose re-statement is carried BELOW
-- VERBATIM (it is pure syntax over `appAt` and the FOL syntax).
--
-- The port follows `[LJ-1.298]`'s `GenTagAgree` shape exactly: the
-- eight parameters are `GenModel`'s (`agents/tasks/LJ-1-210/GenModel.agda:12-24`),
-- the codings come from `GenModel` applied at them.  `domB` and the
-- `DomainAgree` body are copied VERBATIM from
-- `src/L/Condensation.lagda.md:1746-1753` and `:6510-6547`.  The diff
-- against the original is part of this task's number.
--
-- The telescope carries TWO site ties, `entryK` and `domK`.  They are
-- the analogue, at the domain coding, of `SatGraphAgree`'s eight
-- (`:6852-6900`): the K-closure facts `[LJ-1.153]` tied the sites
-- with.  The AMBIENT SUPPLY of these two ties is priced in
-- `ProbeLJ1302B.agda`.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth

open import FOL.ZFStructure using ( module hPropStructure; Transitive; _↾_ )
open import FOL.Syntax using ( Formula; var; _∧̇_; _⇒̇_; _∈̇_; ∀̇∈; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy using ( 𝒮ᵥ )
open import V.Coding using ( pr )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆ ) renaming ( module InfinitySet to Inf )
open Inf using ( #_; sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; squash₁ )

import LJ-1-210.GenModel

module LJ-1-302.GenDomainAgree {ℓ : Level}
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
open GM using ( domAt; appAt; appAt-adequate )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure (𝒮ᵥ {ℓ} ↾ M) using ( S )
module AbsL = FOL.Absoluteness.Single (𝒮ᵥ {ℓ}) M (λ {x} {y} → M-trans {x} {y})
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- BELOW THIS LINE: VERBATIM FROM `src/L/Condensation.lagda.md`.
-- `domB` from `:1746-1753`, `DomainAgree` from `:6510-6547`.  NOTHING
-- is edited but the indentation of the copy.
-- =====================================================================

domB : ∀ {m} → Fin m → Fin m → Fin m → Formula S m
domB f d K =
  ∀̇∈ (var K)
  (((∃̇∈ (var (suc K)) (appAt (suc (suc f)) (suc zero) zero))
      ⇒̇ (var zero ∈̇ var (suc d)))
  ∧̇ ((var zero ∈̇ var (suc d))
      ⇒̇ (∃̇∈ (var (suc K)) (appAt (suc (suc f)) (suc zero) zero))))

module DomainAgree {n : ℕ} (f d K : Fin n) (γ : S ^ n)
  (entryK : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
           → ⟨ fst x ∈ fst (lookup K γ) ⟩ × ⟨ fst y ∈ fst (lookup K γ) ⟩)
  (domK : (x : S) → ⟨ fst x ∈ fst (lookup d γ) ⟩ → ⟨ fst x ∈ fst (lookup K γ) ⟩) where

  mem : (x y : S) → ⟨ (y ∷ x ∷ γ) ⊨ appAt (suc (suc f)) (suc zero) zero ⟩
      → ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
  mem x y ap = subst ⟨_⟩ (appAt-adequate (suc (suc f)) (suc zero) zero
                 (y ∷ x ∷ γ)) ap

  out : ⟨ γ ⊨ domAt f d ⟩ → ⟨ γ ⊨ domB f d K ⟩
  out h = λ x xK →
      ( λ hx → h x .fst
          (PT.rec squash₁ (λ { (y , (_ , ap)) → ∣ y , ap ∣₁ }) hx) )
    , ( λ hx → PT.rec squash₁
          (λ { (y , ap) →
            ∣ y , ( entryK x y (mem x y ap) .snd , ap ) ∣₁ })
          (h x .snd hx) )

  back : ⟨ γ ⊨ domB f d K ⟩ → ⟨ γ ⊨ domAt f d ⟩
  back h x =
      ( λ hx → PT.rec (snd (fst x ∈ fst (lookup d γ))) go hx )
    , ( λ m → PT.rec squash₁
          (λ { (y , (yK , p)) → ∣ y , p ∣₁ })
          (h x (domK x m) .snd m) )
    where
    go : Σ[ y ∈ S ] ⟨ (y ∷ x ∷ γ) ⊨ appAt (suc (suc f)) (suc zero) zero ⟩
       → ⟨ fst x ∈ fst (lookup d γ) ⟩
    go (y , ap) = h x (entryK x y (mem x y ap) .fst) .fst
      ∣ y , ( entryK x y (mem x y ap) .snd , ap ) ∣₁

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.650]  W3, THE DECISIVE MINIATURE, TYPECHECKED ALONE.
--
--   The brief names the widest unmeasured term "whether the covering
--   ordinal's code needs `Lset` named at the STAGE rather than at a hull
--   code".  The miniature that settles it is the one term the tree does
--   not have: a Skolem witness returned AS A CODE and NOT under a
--   truncation.  `L.Hull`'s `closed` (src/L/Hull.lagda.md:118-142)
--   proves the same fact and then FORGETS the code.
--
--   Nothing is postulated.  No hole.  Nothing lands in src/.
--   ONE Agda process, caliber from the pane, never set here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-650.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Parameters
  using ( countFo; constantsFo; absFo; ⊨-abs )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.BoundedSubset {ℓ} lem using ( module HullStage )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( leastOf )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open import Cubical.Data.Vec using ( Vec; _∷_; [] )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

module Skolem (lam : SV.S) (ordλ : IsOrd lam)
              (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
              (X : SV.S)
              (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
              (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module T = HS.H.T
  open T using ( Code; val; wit; vals; Sat; _⊨c_; _⊨₀_ )

  -- THE MINIATURE.  A satisfiable one-variable formula over the CODE
  -- alphabet has a witness that is the value of a NAMED code, and the
  -- code is returned unwrapped.
  skolemCode : (φ : Formula Code 1)
             → ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (a ∷ []) ⊨c φ ⟩ ∥₁
             → Σ[ d ∈ Code ] ⟨ (val d ∷ []) ⊨c φ ⟩
  skolemCode φ h = d , sat
    where
    k : ℕ
    k = countFo φ
    ψ : Formula (⊥* {ℓ}) (suc k)
    ψ = absFo φ
    cs : Vec Code k
    cs = constantsFo φ
    w : Sat k ψ (vals cs)
    w = PT.map
      (λ { (b , hb) → b
         , subst ⟨_⟩ (cong (λ vs → (b ∷ vs) ⊨₀ ψ) (sym (T.vals≡map cs)))
             (subst ⟨_⟩
               (⊨-abs (hPropAlgebra (ℓ-suc ℓ)) HS.ASt.AbsL.𝒮M val φ (b ∷ []))
               hb) }) h
    d : Code
    d = wit k ψ cs
    a : HS.ASt.SL
    a = T.search k ψ (vals cs) w
    pa : ⟨ (a ∷ vals cs) ⊨₀ ψ ⟩
    pa = leastOf HS.ASt.wL {ℓ'' = ℓ-suc ℓ} lem
           (λ b → (b ∷ vals cs) ⊨₀ ψ) w .snd .fst
    val-d : val d ≡ a
    val-d = T.val-wit k ψ cs w
    sat-a : ⟨ (a ∷ []) ⊨c φ ⟩
    sat-a = subst ⟨_⟩
      (sym (⊨-abs (hPropAlgebra (ℓ-suc ℓ)) HS.ASt.AbsL.𝒮M val φ (a ∷ [])))
      (subst ⟨_⟩ (cong (λ vs → (a ∷ vs) ⊨₀ ψ) (T.vals≡map cs)) pa)
    sat : ⟨ (val d ∷ []) ⊨c φ ⟩
    sat = subst (λ b → ⟨ (b ∷ []) ⊨c φ ⟩) (sym val-d) sat-a

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.672] W3.  THE DIRECTION FROM THE GRAPH BACK TO THE SIGMA-1
-- READING, FIRST PIECE: the twelve tag witnesses are the numerals,
-- and pins holds of them.  That is the cheap half of the reverse:
-- the tags are determined, not chosen.
--
-- ONE Agda process, GHCRTS from the pane, never set here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-672.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure; ↾-reflects )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ⊥̇; ∃̇_; ∀̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-zero; numeralL-fst )
open import L.Coding.Model {ℓ} using ( sucAtL; sucAtL-adequate )
open import Cubical.Data.Empty as Empty using ( ⊥ )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( lookup; _∷_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
import LJ-1-520.Probe520 {ℓ} lem as P520

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- The twelve numerals, in the order Matrix pins them.
tags : S ^ 12
tags = numeralL 0 ∷ numeralL 1 ∷ numeralL 2 ∷ numeralL 3
     ∷ numeralL 4 ∷ numeralL 5 ∷ numeralL 6 ∷ numeralL 7
     ∷ numeralL 8 ∷ numeralL 9 ∷ numeralL 10 ∷ numeralL 11 ∷ []

-- Concatenate the tag block in front of an environment of length n.
tagEnv : {n : ℕ} → S ^ n → S ^ (12 + n)
tagEnv {n} γ = numeralL 0 ∷ numeralL 1 ∷ numeralL 2 ∷ numeralL 3
             ∷ numeralL 4 ∷ numeralL 5 ∷ numeralL 6 ∷ numeralL 7
             ∷ numeralL 8 ∷ numeralL 9 ∷ numeralL 10 ∷ numeralL 11 ∷ γ

-- Successor pins: tag (suc k) is sucV of tag k, by sucʟ-fst.
suc-pin : (k : ℕ) {n : ℕ} (i j : Fin n) (γ : S ^ n)
        → fst (lookup i γ) ≡ fst (numeralL k)
        → fst (lookup j γ) ≡ fst (numeralL (suc k))
        → ⟨ γ ⊨ sucAtL i j ⟩
suc-pin k i j γ pi pj =
  subst ⟨_⟩ (sym (sucAtL-adequate i j γ)) target
  where
  target : fst (lookup j γ) ≡ sucV (fst (lookup i γ))
  target =
      pj
    ∙ numeralL-fst (suc k)
    ∙ cong sucV (sym (numeralL-fst k))
    ∙ cong sucV (sym pi)

-- N0 is empty.
empty0 : {n : ℕ} (i : Fin n) (γ : S ^ n)
       → fst (lookup i γ) ≡ fst (numeralL 0)
       → ⟨ γ ⊨ ∀̇∈ (var i) ⊥̇ ⟩
empty0 i γ p x x∈ =
  Empty.rec (numeralL-zero x (subst (λ v → ⟨ fst x ∈ v ⟩) p x∈))

-- pins, at the twelve numerals in front of an arbitrary tail.
-- w, b, K are dummy slots: pins does not mention them.
module Pins {n : ℕ} (γ : S ^ n) where
  private
    m = 12 + n
    n0  : Fin m ; n0  = zero
    n1  : Fin m ; n1  = suc zero
    n2  : Fin m ; n2  = suc (suc zero)
    n3  : Fin m ; n3  = suc (suc (suc zero))
    n4  : Fin m ; n4  = suc (suc (suc (suc zero)))
    n5  : Fin m ; n5  = suc (suc (suc (suc (suc zero))))
    n6  : Fin m ; n6  = suc (suc (suc (suc (suc (suc zero)))))
    n7  : Fin m ; n7  = suc (suc (suc (suc (suc (suc (suc zero))))))
    n8  : Fin m ; n8  = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
    n9  : Fin m ; n9  = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
    n10 : Fin m ; n10 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
    n11 : Fin m ; n11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
    zz  : Fin m ; zz  = zero

  module Mx = P520.Matrix {m} zz zz zz n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11

  env : S ^ m
  env = tagEnv γ

  pins : ⟨ env ⊨ Mx.pins ⟩
  pins =
    empty0 n0 env refl
    , ( suc-pin 0 n0 n1 env refl refl
    , ( suc-pin 1 n1 n2 env refl refl
    , ( suc-pin 2 n2 n3 env refl refl
    , ( suc-pin 3 n3 n4 env refl refl
    , ( suc-pin 4 n4 n5 env refl refl
    , ( suc-pin 5 n5 n6 env refl refl
    , ( suc-pin 6 n6 n7 env refl refl
    , ( suc-pin 7 n7 n8 env refl refl
    , ( suc-pin 8 n8 n9 env refl refl
    , ( suc-pin 9 n9 n10 env refl refl
    , suc-pin 10 n10 n11 env refl refl ))))))))))

-- THE REVERSE, AT THE THIRTEEN-SLOT ENVIRONMENT.  pins holds with
-- K in the last bound slot.  Packing the thirteen existentials is
-- left for a next dispatch: pack1's formula argument did not infer
-- through a where-chain.  What remains unmeasured is producing a
-- transitive adequate K from LsetGraphAt.
module Reverse {n : ℕ} (w b : Fin n) (γ : S ^ n) (kk : S) where
  private
    M = 13 + n
    n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 kK : Fin M
    n0  = zero
    n1  = suc zero
    n2  = suc (suc zero)
    n3  = suc (suc (suc zero))
    n4  = suc (suc (suc (suc zero)))
    n5  = suc (suc (suc (suc (suc zero))))
    n6  = suc (suc (suc (suc (suc (suc zero)))))
    n7  = suc (suc (suc (suc (suc (suc (suc zero))))))
    n8  = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
    n9  = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
    n10 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
    n11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
    kK  = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
    sh : Fin n → Fin M
    sh i = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (i)))))))))))))

  module Mx = P520.Matrix {M} (sh w) (sh b) kK n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11

  env : S ^ M
  env = numeralL 0 ∷ numeralL 1 ∷ numeralL 2 ∷ numeralL 3
      ∷ numeralL 4 ∷ numeralL 5 ∷ numeralL 6 ∷ numeralL 7
      ∷ numeralL 8 ∷ numeralL 9 ∷ numeralL 10 ∷ numeralL 11
      ∷ kk ∷ γ

  hpins : ⟨ env ⊨ Mx.pins ⟩
  hpins =
    empty0 n0 env refl
    , ( suc-pin 0 n0 n1 env refl refl
    , ( suc-pin 1 n1 n2 env refl refl
    , ( suc-pin 2 n2 n3 env refl refl
    , ( suc-pin 3 n3 n4 env refl refl
    , ( suc-pin 4 n4 n5 env refl refl
    , ( suc-pin 5 n5 n6 env refl refl
    , ( suc-pin 6 n6 n7 env refl refl
    , ( suc-pin 7 n7 n8 env refl refl
    , ( suc-pin 8 n8 n9 env refl refl
    , ( suc-pin 9 n9 n10 env refl refl
    , suc-pin 10 n10 n11 env refl refl ))))))))))

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.345] INDEPENDENT REFUTATION, written by the reviewer.
--
-- The two types below are transcribed from the PRE-REPAIR chapter text,
-- commit 26d25a7^, read off the committed diff, and NOT from
-- [LJ-1.341]'s files.  Nothing under agents/tasks/LJ-1-341/ is imported.
-- Each type derives Empty.⊥, so the pre-repair hypothesis types were
-- EMPTY at every slot and every environment.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; pairing-ax ) renaming ( module InfinitySet to Inf )
open Inf using ( #_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ )
open import Cubical.Induction.WellFounded using ( Acc; acc )
open import Cubical.Data.Sum using ( inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

module LJ-1-345.Refute345 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; regularityV )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Axioms.Numerals {ℓ}
  using ( numeralL; numeralL-fst; pairʟ; pairʟ-fst )

import L.Coding.Model
module GM = L.Coding.Model {ℓ}
open GM using ( tagAtL; tagAtL-adequate; prʟ; prʟ-fst; extAt-in-both )
open GM.AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

open import L.Coding.Powerset {ℓ} lem using ( envOneAt )

open hPropStructure 𝒮ʟ using ( S )
module HV = hPropStructure 𝒮ᵥ

-- The membership-cycle engine, from the hierarchy's own regularity.
noCycle3 : (a : V ℓ) → Acc HV._∈ᵗ_ a → (b c : V ℓ)
         → ⟨ a ∈ b ⟩ → ⟨ b ∈ c ⟩ → ⟨ c ∈ a ⟩ → Empty.⊥
noCycle3 a (acc rec) b c ab bc ca = noCycle3 c (rec c ca) a b ca ab bc

noCycle4 : (a : V ℓ) → Acc HV._∈ᵗ_ a → (b c d : V ℓ)
         → ⟨ a ∈ b ⟩ → ⟨ b ∈ c ⟩ → ⟨ c ∈ d ⟩ → ⟨ d ∈ a ⟩ → Empty.⊥
noCycle4 a (acc rec) b c d ab bc cd da = noCycle4 d (rec d da) a b c da ab bc cd

x∈pair : (x y : V ℓ) → ⟨ x ∈ ⁅ x , y ⁆ ⟩
x∈pair x y =
  ∈∈ₛ {a = x} {b = ⁅ x , y ⁆} .snd (pairing-ax x y x .snd ∣ inl refl ∣₁)

y∈pair : (x y : V ℓ) → ⟨ y ∈ ⁅ x , y ⁆ ⟩
y∈pair x y =
  ∈∈ₛ {a = y} {b = ⁅ x , y ⁆} .snd (pairing-ax x y y .snd ∣ inr refl ∣₁)

pair∈pr : (x y : V ℓ) → ⟨ ⁅ x , y ⁆ ∈ pr x y ⟩
pair∈pr x y =
  ∈∈ₛ {a = ⁅ x , y ⁆} {b = pr x y} .snd
    (pairing-ax ⁅ x ⁆s ⁅ x , y ⁆ ⁅ x , y ⁆ .snd ∣ inr refl ∣₁)

pair-only : (x d : V ℓ) → ⟨ d ∈ ⁅ x , x ⁆ ⟩ → d ≡ x
pair-only x d h = PT.rec (setIsSet d x) (λ { (inl p) → p ; (inr p) → p })
  (pairing-ax x x d .fst (∈∈ₛ {a = d} {b = ⁅ x , x ⁆} .fst h))

-- The countermodel site, generic in the slot and the environment.
module Refute {n : ℕ} (Ki : Fin n) (γ : S ^ n) where

  B : S
  B = lookup Ki γ

  b : V ℓ
  b = fst B

  W : S
  W = prʟ (numeralL 0) B

  W-fst : fst W ≡ pr (# 0) b
  W-fst = prʟ-fst (numeralL 0) B ∙ cong (λ u → pr u b) (numeralL-fst 0)

  -- PRE-REPAIR `pairK`, DefinesAgree form, from the commit diff.
  DefPairK : Type (ℓ-suc ℓ)
  DefPairK = (E z w' : S)
           → ⟨ (w' ∷ E ∷ z ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
           → ⟨ fst w' ∈ fst (lookup Ki γ) ⟩

  -- Non-vacuity: the premise holds at the refutation's own witnesses.
  defPair-premise : ⟨ (W ∷ B ∷ B ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
  defPair-premise = subst ⟨_⟩
    (sym (tagAtL-adequate zero 0 (suc (suc zero)) (W ∷ B ∷ B ∷ γ))) W-fst

  defPairK-false : DefPairK → Empty.⊥
  defPairK-false h =
    noCycle3 b (regularityV b) ⁅ # 0 , b ⁆ (pr (# 0) b)
      (y∈pair (# 0) b)
      (pair∈pr (# 0) b)
      (subst (λ u → ⟨ u ∈ b ⟩) W-fst (h B B W defPair-premise))

  Esing : S
  Esing = pairʟ W W

  E-fst : fst Esing ≡ ⁅ fst W , fst W ⁆
  E-fst = pairʟ-fst W W

  -- PRE-REPAIR `envK`, DefinesAgree form, from the commit diff.
  EnvK : Type (ℓ-suc ℓ)
  EnvK = (E z : S) → ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
       → ⟨ fst E ∈ fst (lookup Ki γ) ⟩

  envK-premise : ⟨ (Esing ∷ B ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
  envK-premise =
    extAt-in-both zero (tagAtL zero 0 (suc (suc zero))) (Esing ∷ B ∷ γ) fwd bwd
    where
    fwd : (t : S) → ⟨ fst t ∈ fst (lookup zero (Esing ∷ B ∷ γ)) ⟩
        → ⟨ (t ∷ Esing ∷ B ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
    fwd t ht = subst ⟨_⟩
      (sym (tagAtL-adequate zero 0 (suc (suc zero)) (t ∷ Esing ∷ B ∷ γ)))
      (pair-only (fst W) (fst t)
        (subst (λ u → ⟨ fst t ∈ u ⟩) E-fst ht) ∙ W-fst)

    bwd : (t : S) → ⟨ (t ∷ Esing ∷ B ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
        → ⟨ fst t ∈ fst (lookup zero (Esing ∷ B ∷ γ)) ⟩
    bwd t h = subst (λ u → ⟨ fst t ∈ u ⟩) (sym E-fst)
      (subst (λ u → ⟨ u ∈ ⁅ fst W , fst W ⁆ ⟩) (sym eq)
        (x∈pair (fst W) (fst W)))
      where
      eq : fst t ≡ fst W
      eq = subst ⟨_⟩
             (tagAtL-adequate zero 0 (suc (suc zero)) (t ∷ Esing ∷ B ∷ γ)) h
         ∙ sym W-fst

  envK-false : EnvK → Empty.⊥
  envK-false h =
    noCycle4 b (regularityV b) ⁅ # 0 , b ⁆ (pr (# 0) b) ⁅ fst W , fst W ⁆
      (y∈pair (# 0) b)
      (pair∈pr (# 0) b)
      (subst (λ u → ⟨ u ∈ ⁅ fst W , fst W ⁆ ⟩) W-fst (x∈pair (fst W) (fst W)))
      (subst (λ u → ⟨ u ∈ b ⟩) E-fst (h Esing B envK-premise))

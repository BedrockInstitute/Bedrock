{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.99] probe A: the four-step arityK chain closes entryK's
-- conclusion, given the frame's E ∈ K.
--
-- entryK (src/L/Condensation/TwelveAgree.lagda.md:118-120) is refuted
-- because z is free.  [LJ-1.98] measured the T-slot tie NOT SUPPLIED
-- at the EnvSet site.  The second candidate, inferred in the brief, is
-- the transitivity-into-K chain: arityK (src/L/Condensation.lagda.md:5769-5770)
-- is one step, and four applications of it climb
--
--   z ∈ E, E ∈ K  →  z ∈ K
--   pr x y ∈ z, z ∈ K  →  pr x y ∈ K
--   ⁅ x ⁆ ∈ pr x y, pr x y ∈ K  →  ⁅ x ⁆ ∈ K
--   x ∈ ⁅ x ⁆, ⁅ x ⁆ ∈ K  →  x ∈ K
--
-- and the same for y through the second component of the pair.  The
-- L-set level uses prʟ-fst (src/L/Coding/Model.lagda.md:329), pairʟ
-- and pairʟ-fst (src/L/Axioms/Numerals.lagda.md:127), exactly as
-- src/ProbeLJ197A.agda did.  The only premise the site's own binders
-- do not supply is E ∈ K; this probe takes it as a parameter (GREEN),
-- and ProbeLJ199B measures that the EnvSet telescope itself does not
-- bind it (RED as designed).
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ199A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import V.Model {ℓ} using ( pair-singleton )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( pairʟ; pairʟ-fst )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst; envOverAt )
open import L.Condensation {ℓ} lem using ( succU; keyU )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; pairing-ax )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( _∈ₛ_; ∈∈ₛ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
open AbsL using ( _^_ )

-- =====================================================================
-- STEP 1: THE FOUR-STEP CHAIN.  arityK has exactly the delivered
-- field's type (src/L/Condensation.lagda.md:5769-5770); E ∈ K is the
-- one premise the site's binders do not supply.  The chain is generic:
-- one field plus the pair encoding, nothing about definability.
-- =====================================================================
module ChainZ {n : ℕ} (K : Fin n) (γ : S ^ n)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
          → ⟨ fst N ∈ fst (lookup K γ) ⟩
          → ⟨ fst v ∈ fst (lookup K γ) ⟩) where

  -- The V-level pair pieces, from pairing-ax alone (the pair encoding).
  -- a ∈ ⁅ a ⁆s.
  a∈singl : (a : V ℓ) → ⟨ a ∈ ⁅ a ⁆s ⟩
  a∈singl a = subst (λ w → ⟨ a ∈ w ⟩) (pair-singleton a)
    (∈∈ₛ {a = a} {b = ⁅ a , a ⁆} .snd (pairing-ax a a a .snd ∣ inl refl ∣₁))

  -- ⁅ a ⁆s ∈ pr a b, the first component of the Kuratowski pair.
  singl∈pr : (a b : V ℓ) → ⟨ ⁅ a ⁆s ∈ pr a b ⟩
  singl∈pr a b = ∈∈ₛ {a = ⁅ a ⁆s} {b = pr a b} .snd
    (pairing-ax ⁅ a ⁆s ⁅ a , b ⁆ ⁅ a ⁆s .snd ∣ inl refl ∣₁)

  -- ⁅ a , b ⁆ ∈ pr a b, the second component of the Kuratowski pair.
  pair∈pr : (a b : V ℓ) → ⟨ ⁅ a , b ⁆ ∈ pr a b ⟩
  pair∈pr a b = ∈∈ₛ {a = ⁅ a , b ⁆} {b = pr a b} .snd
    (pairing-ax ⁅ a ⁆s ⁅ a , b ⁆ ⁅ a , b ⁆ .snd ∣ inr refl ∣₁)

  -- b ∈ ⁅ a , b ⁆.
  b∈pair : (a b : V ℓ) → ⟨ b ∈ ⁅ a , b ⁆ ⟩
  b∈pair a b = ∈∈ₛ {a = b} {b = ⁅ a , b ⁆} .snd
    (pairing-ax a b b .snd ∣ inr refl ∣₁)

  -- Step 2: pr x y ∈ z and z ∈ K give pr x y ∈ K.  One arityK,
  -- through fst (prʟ x y) ≡ pr (fst x) (fst y).
  prʟxy∈z : (z x y : S) → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
           → ⟨ fst (prʟ x y) ∈ fst z ⟩
  prʟxy∈z z x y p = subst (λ w → ⟨ w ∈ fst z ⟩) (sym (prʟ-fst x y)) p

  prxy∈K : (z x y : S) → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
          → ⟨ fst z ∈ fst (lookup K γ) ⟩
          → ⟨ fst (prʟ x y) ∈ fst (lookup K γ) ⟩
  prxy∈K z x y p zK' = arityK z (prʟ x y) (prʟxy∈z z x y p) zK'

  -- Step 3x: the singleton of x lies in pr x y.  The L-set singleton
  -- is pairʟ x x, whose fst is ⁅ A , A ⁆, definitionally ⁅ A ⁆s.
  xsingl∈prxy : (x y : S) → ⟨ fst (pairʟ x x) ∈ fst (prʟ x y) ⟩
  xsingl∈prxy x y =
    subst (λ w → ⟨ fst (pairʟ x x) ∈ w ⟩) (sym (prʟ-fst x y))
      (subst (λ w → ⟨ w ∈ pr (fst x) (fst y) ⟩) (sym (pairʟ-fst x x))
        (subst (λ w → ⟨ w ∈ pr (fst x) (fst y) ⟩)
               (sym (pair-singleton (fst x)))
               (singl∈pr (fst x) (fst y))))

  -- Step 4x: x ∈ fst (pairʟ x x).
  x∈pairʟxx : (x : S) → ⟨ fst x ∈ fst (pairʟ x x) ⟩
  x∈pairʟxx x =
    subst (λ w → ⟨ fst x ∈ w ⟩) (sym (pairʟ-fst x x))
      (subst (λ w → ⟨ fst x ∈ w ⟩) (sym (pair-singleton (fst x)))
        (a∈singl (fst x)))

  -- The x half: steps 2 to 4, from the z ∈ K premise.
  xK' : (z x y : S) → ⟨ fst z ∈ fst (lookup K γ) ⟩
      → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
      → ⟨ fst x ∈ fst (lookup K γ) ⟩
  xK' z x y zK' p =
    arityK (pairʟ x x) x (x∈pairʟxx x)
      (arityK (prʟ x y) (pairʟ x x) (xsingl∈prxy x y)
        (prxy∈K z x y p zK'))

  -- Step 3y: ⁅ A , B ⁆ lies in pr A B, the second component.
  ysingl∈prxy : (x y : S) → ⟨ fst (pairʟ x y) ∈ fst (prʟ x y) ⟩
  ysingl∈prxy x y =
    subst (λ w → ⟨ fst (pairʟ x y) ∈ w ⟩) (sym (prʟ-fst x y))
      (subst (λ w → ⟨ w ∈ pr (fst x) (fst y) ⟩) (sym (pairʟ-fst x y))
        (pair∈pr (fst x) (fst y)))

  -- Step 4y: y ∈ fst (pairʟ x y).
  y∈pairʟxy : (x y : S) → ⟨ fst y ∈ fst (pairʟ x y) ⟩
  y∈pairʟxy x y =
    subst (λ w → ⟨ fst y ∈ w ⟩) (sym (pairʟ-fst x y))
      (b∈pair (fst x) (fst y))

  -- The y half: steps 2 to 4, from the z ∈ K premise.
  yK' : (z x y : S) → ⟨ fst z ∈ fst (lookup K γ) ⟩
      → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
      → ⟨ fst y ∈ fst (lookup K γ) ⟩
  yK' z x y zK' p =
    arityK (pairʟ x y) y (y∈pairʟxy x y)
      (arityK (prʟ x y) (pairʟ x y) (ysingl∈prxy x y)
        (prxy∈K z x y p zK'))

  -- THE BACK-DIRECTION SHAPE: from z ∈ K, three arityK applications
  -- close the EnvSet conclusion.  The EnvSet `over→bnd` direction
  -- binds the envOverAt satisfaction h for z
  -- (src/L/Condensation.lagda.md:2869), so envInK z h supplies the
  -- z ∈ K premise there (BackSiteSupply below).
  entryK-tied-zK : (z x y : S) → ⟨ fst z ∈ fst (lookup K γ) ⟩
                  → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
                  → ⟨ fst x ∈ fst (lookup K γ) ⟩
                    × ⟨ fst y ∈ fst (lookup K γ) ⟩
  entryK-tied-zK z x y zK' p = xK' z x y zK' p , yK' z x y zK' p

  -- STEP 3's TIE: the arSubK family's intended tie is
  -- x ∈ ar → ar ∈ K → x ∈ K, which is arityK exactly once.
  arSubK-tied : (ar x : S) → ⟨ fst x ∈ fst ar ⟩
              → ⟨ fst ar ∈ fst (lookup K γ) ⟩
              → ⟨ fst x ∈ fst (lookup K γ) ⟩
  arSubK-tied ar x hxar arK = arityK ar x hxar arK

-- =====================================================================
-- STEP 1 + THE FOUR-STEP CHAIN: ChainZ plus the first arityK step,
-- z ∈ E and E ∈ K give z ∈ K.  arityK has exactly the delivered
-- field's type (src/L/Condensation.lagda.md:5769-5770); E ∈ K is the
-- one premise the EnvSet out-direction binders do not supply
-- (ProbeLJ199B measures that).  The chain is generic: one field plus
-- the pair encoding, nothing about definability.
-- =====================================================================
module Chain {n : ℕ} (E K : Fin n) (γ : S ^ n)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
          → ⟨ fst N ∈ fst (lookup K γ) ⟩
          → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (E∈K : ⟨ fst (lookup E γ) ∈ fst (lookup K γ) ⟩) where

  module Z = ChainZ {n} K γ arityK

  -- Step 1: z ∈ E and E ∈ K give z ∈ K.  One arityK.
  z∈K : (z : S) → ⟨ fst z ∈ fst (lookup E γ) ⟩
       → ⟨ fst z ∈ fst (lookup K γ) ⟩
  z∈K z z∈E = arityK (lookup E γ) z z∈E E∈K

  -- THE SITE-USE LEMMA, OUT DIRECTION: exactly the EnvSet conclusion
  -- (src/L/Condensation.lagda.md:2815-2817), from the site's binders
  -- plus the frame's E ∈ K, in four arityK applications.  GREEN.
  entryK-tied : (z x y : S) → ⟨ fst z ∈ fst (lookup E γ) ⟩
              → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
              → ⟨ fst x ∈ fst (lookup K γ) ⟩
                × ⟨ fst y ∈ fst (lookup K γ) ⟩
  entryK-tied z x y z∈E p = Z.entryK-tied-zK z x y (z∈K z z∈E) p

-- =====================================================================
-- STEP 2, BACK DIRECTION: EnvSet's over→bnd binds the envOverAt
-- satisfaction h for z (src/L/Condensation.lagda.md:2869, the λ z h
-- binder).  The module parameter envInK is exactly the EnvSet
-- parameter (src/L/Condensation.lagda.md:2776-2777), so envInK z h
-- supplies z ∈ K, and the three-step chain closes entryK's conclusion
-- there WITHOUT E ∈ K.  GREEN.
-- =====================================================================
module BackSiteSupply {n : ℕ} (ar B K : Fin n) (γ : S ^ n)
  (envInK : (z : S) → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc ar) (suc B) ⟩
           → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
          → ⟨ fst N ∈ fst (lookup K γ) ⟩
          → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (z x y : S) (h : ⟨ (z ∷ γ) ⊨ envOverAt zero (suc ar) (suc B) ⟩)
  (p : ⟨ pr (fst x) (fst y) ∈ fst z ⟩) where

  -- The site's z ∈ K, from the bound satisfaction and envInK.
  zK : ⟨ fst z ∈ fst (lookup K γ) ⟩
  zK = envInK z h

  -- The EnvSet conclusion, three arityK applications after zK.
  entryK-back : ⟨ fst x ∈ fst (lookup K γ) ⟩
                × ⟨ fst y ∈ fst (lookup K γ) ⟩
  entryK-back = ChainZ.entryK-tied-zK K γ arityK z x y zK p

-- =====================================================================
-- STEP 4, FORMALLY ANCHORED: the tied succK/keyK shapes at the
-- ForallAgree layout (src/L/Condensation.lagda.md:3705-3706,
-- :3738-3739).  The row's out binds arK and aK (λ-position, :3705);
-- its back derives them from codesK (:3721).  This module shows the
-- TIED frame facts instantiate at exactly those binders.
-- =====================================================================
module SuccKeySite {m : ℕ} (C T B N K : Fin m) (γ : S ^ m)
  (succK-tied : (E ya yc a ar c : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
              → succU {m} C T B N K γ E ya yc a ar c)
  (keyK-tied : (E ya yc a ar c : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
             → ⟨ fst a ∈ fst (lookup K γ) ⟩
             → keyU {m} C T B N K γ E ya yc a ar c)
  (E ya yc a ar c : S)
  (arK : ⟨ fst ar ∈ fst (lookup K γ) ⟩)
  (aK : ⟨ fst a ∈ fst (lookup K γ) ⟩) where

  -- The two memberships SubValSuccB2T consumes
  -- (src/L/Condensation.lagda.md:3029-3030), from the tied frame
  -- facts at the row's binders.
  succK-use : succU {m} C T B N K γ E ya yc a ar c
  succK-use = succK-tied E ya yc a ar c arK

  keyK-use : keyU {m} C T B N K γ E ya yc a ar c
  keyK-use = keyK-tied E ya yc a ar c arK aK

-- The same anchor for keyK-neg at the NegAgree layout
-- (src/L/Condensation.lagda.md:3597, :3624): the conclusion is
-- pr (fst ar) (fst a) ∈ K, and the row binds arK and aK.
module KeyNegSite {m : ℕ} (K : Fin m) (γ : S ^ m)
  (keyK-tied : (E ya yc a ar c : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
             → ⟨ fst a ∈ fst (lookup K γ) ⟩
             → ⟨ pr (fst (lookup (suc (suc (suc (suc zero))))
                               (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)))
                     (fst (lookup (suc (suc (suc zero)))
                               (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)))
                  ∈ fst (lookup (suc (suc (suc (suc (suc (suc K))))))
                            (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (E ya yc a ar c : S)
  (arK : ⟨ fst ar ∈ fst (lookup K γ) ⟩)
  (aK : ⟨ fst a ∈ fst (lookup K γ) ⟩) where

  keyK-use : ⟨ pr (fst (lookup (suc (suc (suc (suc zero))))
                             (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)))
                   (fst (lookup (suc (suc (suc zero)))
                             (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)))
                ∈ fst (lookup (suc (suc (suc (suc (suc (suc K))))))
                          (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩
  keyK-use = keyK-tied E ya yc a ar c arK aK

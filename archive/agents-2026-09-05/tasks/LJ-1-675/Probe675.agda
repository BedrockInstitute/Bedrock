{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.675] SURVEY.  Which arity the chapter's level-hood residue
-- has to serve.  Lands nothing in src/.  Builds no satisfaction lemma.
--
--   THE BRIEF'S OBLIGATION is residue-arity: for each consumer of the
--   residue, the arity and the environment shape that consumer
--   demands, and whether one lemma can serve them all.
--
--   THREE CONSUMER TYPES, ONE KERNEL.  The types are restated in one
--   HullStage telescope (section 1).  The discrete comparison is
--   section 2.  The obligation packs both.
--
--   Predecessor types, taken from the probe that typechecked:
--     661  Formula CS.S 4, env u ∷ v ∷ γ ∷ K, K free
--          Probe661.agda:105-107.  Verdict NO-GO on inhabiting
--          hoodsound-at-levelhood0, not on the type.
--     663  SatAtPacked : Formula Code 2 → Type, env γ ∷ v
--          Probe663.agda:135-138.  Verdict STOP on level-laws, type
--          green.
--     666  SatAtLevel  : Formula ⊥* 2 → Type, env v ∷ γ
--          Probe662.agda:284-287 (the type 666 asked to inhabit).
--          Verdict NO-GO on sat-at-level, type green at 662.
--
--   Nothing is postulated.  No hole.  ONE Agda process, caliber from
--   the pane, never set here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-675.Probe675 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.Syntax using ( Formula )
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Manipulation.Relabelling using ( embed )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.BoundedSubset {ℓ} lem using ( module HullStage; module CS )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Vec using ( _∷_; [] )
open import Cubical.Data.Nat using ( ℕ; zero; suc )
open import Cubical.Data.Nat.Properties using ( znots; snotz; injSuc )
import Cubical.Data.Empty as Empty
open import Cubical.Foundations.Prelude using ( _≡_; refl; cong )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

-- =====================================================================
-- SECTION 1.  THE THREE DEMAND TYPES, IN ONE HullStage TELESCOPE.
--
--   W3 of this task: can the arity-2 and arity-4 demands be stated at
--   this frame.  They can.  The incompatibility is the TYPES, not the
--   telescope (the same split [LJ-1.665] measured for the certificate
--   clauses, Probe665.agda:160-164).
--
--   P-l: none of these types names LevelHood0.matrix.  The kernel is
--   the arity-4 formula type the chapter exports
--   (src/L/BoundedSubset.lagda.md:848-849).  Naming the matrix term
--   would unfold GraphB ([LJ-1.662] Probe662.agda:101-108).
-- =====================================================================

module Frame (lam : SV.S) (ordλ : IsOrd lam)
             (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (X : SV.S)
             (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module T = HS.H.T

  -- [LJ-1.661] Probe661.agda:105-107.  Chapter matrix at n = 0:
  -- env u ∷ v ∷ γ ∷ K, K the one free bound
  -- (src/L/BoundedSubset.lagda.md:68-72, :847-849).  Grade Δ₀, not
  -- restated here: the chapter certifies it
  -- (src/L/BoundedSubset.lagda.md:851-852).
  Kernel : Type (ℓ-suc ℓ)
  Kernel = Formula CS.S 4

  -- [LJ-1.663] Probe663.agda:135-138, with the packed value quantified
  -- rather than constructed (this survey builds no packed term).  Env
  -- γ ∷ v ∷ []: ordinal slot 0, value slot 1, the order 663 copied
  -- from [LJ-1.659] (Probe663.agda:75-76).  Alphabet: hull Code.
  SatAtPacked : Formula T.Code 2 → Type (ℓ-suc ℓ)
  SatAtPacked lf =
    (γ v : HS.ASt.SL) → IsOrd (fst γ) → fst v ≡ Lset (fst γ)
    → ⟨ (γ ∷ v ∷ []) T.⊨c lf ⟩

  -- [LJ-1.662] Probe662.agda:284-287, the type [LJ-1.666] asked to
  -- inhabit.  Env v ∷ γ ∷ []: value slot 0, ordinal slot 1, the order
  -- HoodExistsP reads (Probe662.agda:79-81).  Alphabet: parameter-free
  -- ⊥*, then embed into Code.  The 666 report forbids a KFacts route;
  -- this file does not build one.
  SatAtLevel : Formula (⊥* {ℓ-suc ℓ}) 2 → Type (ℓ-suc ℓ)
  SatAtLevel φ =
    (γ v : HS.ASt.SL) → IsOrd (fst γ) → fst v ≡ Lset (fst γ)
    → ⟨ (v ∷ γ ∷ []) T.⊨c (embed φ) ⟩

-- =====================================================================
-- SECTION 2.  EACH CONSUMER, AS ARITY AND ENVIRONMENT SHAPE.
--
--   Tags, so the comparison does not mention a transparent matrix:
--     k-free    1 = K is a free slot; 0 = K is existentially closed
--     slots     0 = u ∷ v ∷ γ ∷ K
--               1 = γ ∷ v     (ordinal then value)
--               2 = v ∷ γ     (value then ordinal)
--     alphabet  0 = CS.S (class carrier)
--               1 = Code (hull codes)
--               2 = ⊥* (parameter-free)
-- =====================================================================

data Consumer : Type where
  consumer : (arity k-free slots alphabet : ℕ) → Consumer

arity-of : Consumer → ℕ
arity-of (consumer a _ _ _) = a

k-free-of : Consumer → ℕ
k-free-of (consumer _ k _ _) = k

slots-of : Consumer → ℕ
slots-of (consumer _ _ s _) = s

alphabet-of : Consumer → ℕ
alphabet-of (consumer _ _ _ a) = a

-- [LJ-1.661] the chapter's own Δ₀ export.  Arity 4, K free, class
-- carrier, env u ∷ v ∷ γ ∷ K.
c661 : Consumer
c661 = consumer 4 1 0 0

-- [LJ-1.663] SatAtPacked.  Arity 2, K closed, hull Code, env γ ∷ v.
c663 : Consumer
c663 = consumer 2 0 1 1

-- [LJ-1.666] SatAtLevel.  Arity 2, K closed, erased ⊥*, env v ∷ γ.
c666 : Consumer
c666 = consumer 2 0 2 2

≠-4-2 : 4 ≡ 2 → Empty.⊥
≠-4-2 p = snotz (injSuc (injSuc p))

≠-1-2 : 1 ≡ 2 → Empty.⊥
≠-1-2 p = znots (injSuc p)

-- The three consumer records are not equal.  A lemma typed at one
-- consumer type is not a lemma typed at another.
c661≢c663 : c661 ≡ c663 → Empty.⊥
c661≢c663 p = ≠-4-2 (cong arity-of p)

c663≢c666 : c663 ≡ c666 → Empty.⊥
c663≢c666 p = ≠-1-2 (cong slots-of p)

c663≢c666-alphabet : alphabet-of c663 ≡ alphabet-of c666 → Empty.⊥
c663≢c666-alphabet p = ≠-1-2 p

c661≢c666 : c661 ≡ c666 → Empty.⊥
c661≢c666 p = ≠-4-2 (cong arity-of p)

-- 663 and 666 SHARE the closed arity-2 shape (K not free).  They
-- differ on slot order and alphabet.  That is the W2 split: one
-- packed satisfaction at a generic alphabet, instantiated twice,
-- is not a third kernel.
share-arity-663-666 : arity-of c663 ≡ arity-of c666
share-arity-663-666 = refl

share-closed-663-666 : k-free-of c663 ≡ k-free-of c666
share-closed-663-666 = refl

-- One lemma at the SAME consumer type cannot serve all three, because
-- the records are pairwise unequal.
SameType : Type
SameType = (c661 ≡ c663) × (c663 ≡ c666)

same-type-false : SameType → Empty.⊥
same-type-false (p , _) = c661≢c663 p

-- The two arity-2 demands are VIEWS of the arity-4 kernel: K is
-- closed, arity is 2.  The maps that build those views already exist:
--   651  twoSlot / lset-formula  (Probe651.agda:100-142)
--        unbounded ∃̇ u, rotate, unbounded ∃̇ K, swap to γ ∷ v, mapFo
--        to Code.
--   662  hood2 / φ₀              (Probe662.agda:88-123)
--        rename ρ, unbounded ∃̇ K, bounded ∃̇∈ K u, erase to ⊥*.
-- This file does not rebuild them (P-l; the brief forbids a
-- satisfaction lemma).
KernelViews : Type
KernelViews =
    (k-free-of c661 ≡ 1)
  × (k-free-of c663 ≡ 0)
  × (k-free-of c666 ≡ 0)
  × (arity-of c661 ≡ 4)
  × (arity-of c663 ≡ 2)
  × (arity-of c666 ≡ 2)

kernel-views : KernelViews
kernel-views = refl , refl , refl , refl , refl , refl

-- =====================================================================
-- THE OBLIGATION.  Each consumer's arity and environment, and whether
-- one lemma serves them all.
--
--   one lemma at a consumer type  : NO   (same-type-false)
--   one kernel, two closed views  : YES  (kernel-views)
-- =====================================================================

residue-arity :
    Consumer
  × Consumer
  × Consumer
  × (arity-of c661 ≡ 4)
  × (arity-of c663 ≡ 2)
  × (arity-of c666 ≡ 2)
  × (c661 ≡ c663 → Empty.⊥)
  × (c663 ≡ c666 → Empty.⊥)
  × (alphabet-of c663 ≡ alphabet-of c666 → Empty.⊥)
  × (c661 ≡ c666 → Empty.⊥)
  × (SameType → Empty.⊥)
  × KernelViews
residue-arity =
    c661 , c663 , c666
  , refl , refl , refl
  , c661≢c663 , c663≢c666 , c663≢c666-alphabet , c661≢c666
  , same-type-false
  , kernel-views

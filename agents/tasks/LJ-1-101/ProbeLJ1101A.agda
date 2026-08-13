{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.101] probe A: apply cardκ at the master's IsCardinal, then
-- price sq for every infinite ordinal.
--
-- Step 1: [LJ-1.94] supplied `cardκ : IsCardinal κ` at a LOCAL copy of
-- the type (src/ProbeLJ194A.agda:73-74, :1160-1161, :1196-1197), to
-- avoid importing the heavy consumer master.  This probe imports
-- L.BoundedSubset's own IsCardinal and _↪_
-- (src/L/BoundedSubset.lagda.md:1042-1046), applies SiteAt.cardκ at
-- that type and checks.  One agda process at the C-12 cap
-- (GHCRTS="-A64m -I0 -M8g").

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1101A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import ProbeLJ194A {ℓ} lem as P194
open P194 using ( module SiteAt )
import L.BoundedSubset {ℓ} lem as BS
open BS using ( IsCardinal; _↪_ )
import L.Ordinal.SquareLaw {ℓ} lem as SQ

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Model {ℓ} using ( pair-singleton )
open import L.Constructible {ℓ} using ( IsOrd; Lset; Lset-out; 𝒟ₒ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪; ∈ₛ⟪_⟫↪_; presentation )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; pairing-ax; ⋃_; union-ax; ⁅_⁆s; _∪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV; #_ )
open hPropStructure 𝒮ᵥ
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sigma using ( ΣPathP; Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.Equiv using ( equivFun )

-- The two _↪_ definitions (probe: src/ProbeLJ194A.agda:67-68; master:
-- src/L/BoundedSubset.lagda.md:1042-1043) have the same body.  If this
-- identity checks, they are definitionally equal at every carrier pair
-- and no transport is needed anywhere.
↪-agree : {X Y : Type ℓ} → (P194._↪_) X Y → (BS._↪_) X Y
↪-agree f = f

-- STEP 1: the [LJ-1.94] supply at the master's IsCardinal.  If this
-- checks, the local copy and the master's statement are the same type,
-- so cardκ is SUPPLIED at the consumer's type (C-38), not restated.
cardκ-at-master : IsCardinal SiteAt.κ
cardκ-at-master = SiteAt.cardκ

-- =====================================================================
-- STEP 2, question 1: the cardinality clause of Init SiteAt.κ.
--
-- Init forbids an injection into the SQUARE of an infinite member
-- (src/L/Ordinal/SquareLaw.lagda.md:692-701); IsCardinal forbids one
-- into the member itself (:1045-1046).  The bridge: every member of κ
-- is countable (the delivered countAt, src/ProbeLJ194A.agda:555), so an
-- injection κ ↪ β × β for β ∈ κ composes through the countability and
-- an injective pairing on ⟪ ω ⟫ into an injection κ ↪ ω, which cardκ
-- refutes at δ = ω ∈ κ.  The pairing is the one assembleable-but-not-
-- delivered piece (the tree has the ℕ-level square pairing with
-- injectivity at src/FOL/Count.lagda.md:29-30, :59-60, but no stated
-- ⟪ ω ⟫ × ⟪ ω ⟫ ↪ ⟪ ω ⟫); it is a module hypothesis here, so the
-- bridge itself is MEASURED.
module InitClauseBridge
  (pairω : ⟪ ω ⟫ × ⟪ ω ⟫ → ⟪ ω ⟫)
  (pairω-inj : (m n : ⟪ ω ⟫ × ⟪ ω ⟫) → pairω m ≡ pairω n → m ≡ n)
  where

  square-clause : (β : S) → IsOrd β → ⟨ β ∈ˢ SiteAt.κ ⟩ → ⟨ ω ∈ˢ β ⟩
                → (f : ⟪ SiteAt.κ ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
                → ((m n : ⟪ SiteAt.κ ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥
  square-clause β oβ β∈κ ω∈β f f-inj =
    PT.rec Empty.isProp⊥ go (P194.Hartogs.κ-mem β β∈κ)
    where
    go : Σ[ wo ∈ P194.SmallWO.WO ] (P194.SmallWO.ot wo ≡ β) → Empty.⊥
    go (wo , e) = P194.Hartogs.cardκ ω SiteAt.α∈κ g
      where
      i : (P194._↪_) ⟪ β ⟫ ⟪ ω ⟫
      i = P194.countAt wo β e
      g0 : ⟪ SiteAt.κ ⟫ → ⟪ ω ⟫
      g0 m = pairω (i .fst (fst (f m)) , i .fst (snd (f m)))
      g-inj : (m n : ⟪ SiteAt.κ ⟫) → g0 m ≡ g0 n → m ≡ n
      g-inj m n h = f-inj m n (ΣPathP (i .snd (fst (f m)) (fst (f n)) (cong fst h')
                                    , i .snd (snd (f m)) (snd (f n)) (cong snd h')))
        where
        h' : (i .fst (fst (f m)) , i .fst (snd (f m)))
           ≡ (i .fst (fst (f n)) , i .fst (snd (f n)))
        h' = pairω-inj (i .fst (fst (f m)) , i .fst (snd (f m)))
                       (i .fst (fst (f n)) , i .fst (snd (f n))) h
      g : (P194._↪_) ⟪ SiteAt.κ ⟫ ⟪ ω ⟫
      g = g0 , g-inj

  -- The full Init SiteAt.κ: ordκ and ω ∈ κ are delivered
  -- (src/ProbeLJ194A.agda:1193-1194, :1207-1208); the successor
  -- closure of κ is the one remaining hypothesis, priced separately.
  module InitAtSite
    (succκ : (γ : S) → ⟨ γ ∈ˢ SiteAt.κ ⟩ → ⟨ sucV γ ∈ˢ SiteAt.κ ⟩) where

    initκ : SQ.Init SiteAt.κ
    initκ = SiteAt.ordκ , SiteAt.α∈κ , succκ , square-clause

-- =====================================================================
-- STEP 2, question 3, the truth check (D-10): the general
-- absorbs-subset as stated at src/L/BoundedSubset.lagda.md:1364-1368
-- quantifies over ALL ordinals α.  At α = ∅, Lset ∅ is the empty stage
-- (Lset-out, src/L/Constructible.lagda.md:336), so with x = ∅ the
-- statement demands an injection from the singleton stage into the empty
-- stage.  There is none.  The general statement is FALSE; only the
-- consumer's infinite instances (α = ω at the site) are true content.
module AbsorbsRefute where

  L∅-empty : (y : S) → ⟨ y ∈ˢ Lset ∅ ⟩ → Empty.⊥
  L∅-empty y y∈ = PT.rec Empty.isProp⊥ go (Lset-out ∅ y y∈)
    where
    go : Σ[ δ ∈ S ] (⟨ δ ∈ˢ ∅ ⟩ × ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩) → Empty.⊥
    go (δ , δ∈∅ , _) = ∅-empty δ (∈∈ₛ {a = δ} {b = ∅} .fst δ∈∅)

  ⟪L∅⟫-empty : (m : ⟪ Lset ∅ ⟫) → Empty.⊥
  ⟪L∅⟫-empty m =
    L∅-empty (⟪ Lset ∅ ⟫↪ m)
      (∈∈ₛ {a = ⟪ Lset ∅ ⟫↪ m} {b = Lset ∅} .snd (∈ₛ⟪ Lset ∅ ⟫↪ m))

  ∅∈ₛ⁅∅⁆ : ⟨ ∅ ∈ₛ ⁅ ∅ ⁆s ⟩
  ∅∈ₛ⁅∅⁆ =
    subst (λ w → ⟨ ∅ ∈ₛ w ⟩) (pair-singleton ∅)
      (pairing-ax ∅ ∅ ∅ .snd ∣ inl refl ∣₁)

  ⁅∅⁆∈ₛpair : ⟨ ⁅ ∅ ⁆s ∈ₛ ⁅ Lset ∅ , ⁅ ∅ ⁆s ⁆ ⟩
  ⁅∅⁆∈ₛpair = pairing-ax (Lset ∅) (⁅ ∅ ⁆s) (⁅ ∅ ⁆s) .snd ∣ inr refl ∣₁

  ∅∈ₛunion : ⟨ ∅ ∈ₛ Lset ∅ ∪ ⁅ ∅ ⁆s ⟩
  ∅∈ₛunion =
    union-ax (⁅ Lset ∅ , ⁅ ∅ ⁆s ⁆) ∅ .snd
      ∣ ⁅ ∅ ⁆s , (⁅∅⁆∈ₛpair , ∅∈ₛ⁅∅⁆) ∣₁

  witness : ⟪ Lset ∅ ∪ ⁅ ∅ ⁆s ⟫
  witness = equivFun (presentation (Lset ∅ ∪ ⁅ ∅ ⁆s)) (∅ , ∅∈ₛunion)

  x⊆L∅ : (z : S) → ⟨ z ∈ˢ ∅ ⟩ → ⟨ z ∈ˢ Lset ∅ ⟩
  x⊆L∅ z z∈∅ =
    Empty.rec {A = ⟨ z ∈ˢ Lset ∅ ⟩}
      (∅-empty z (∈∈ₛ {a = z} {b = ∅} .fst z∈∅))

  refute : ((α : S) → (x : S)
           → ((z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
           → _↪_ ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ⟪ Lset α ⟫) → Empty.⊥
  refute absorbs = ⟪L∅⟫-empty (absorbs ∅ ∅ x⊆L∅ .fst witness)

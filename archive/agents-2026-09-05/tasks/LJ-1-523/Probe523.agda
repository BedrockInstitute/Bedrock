{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.523]  The last mile: from the bounded-subset theorem to GCH.
--
-- The obligation is `GCHBridge`, section 3.  Section 1 is W3, the two
-- KAPPA: the brief ordered it written first and typechecked alone.
-- That slice is kept at agents/tasks/LJ-1-523/runs/w3-slice.agda.txt.
--
-- Nothing is inhabited.  Nothing is postulated.  Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-523.Probe523 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; Lset; isL )
open import L.Cardinal {ℓ} lem using ( IsCardinalL )
open import L.BoundedSubset {ℓ} lem using ( IsCardinal; _↪_; module Devlin55 )
open import L.GCH {ℓ} lem using ( GCHStatement; SuccCardL; InjL )
import FOL.ZFModel
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; _∪_; ⁅_⁆s )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

-- The V-carrier, the theorem's carrier.
module SV = hPropStructure 𝒮ᵥ
-- The L-carrier, the statement's carrier.  `𝒮ʟ = 𝒮ᵥ ↾ isL`
-- (src/L/Constructible.lagda.md:411), so SL.S is Σ[ x ∈ SV.S ] ⟨ isL x ⟩
-- (src/FOL/ZFStructure.lagda.md:146) and `fst` is the only map to SV.S.
module SL = hPropStructure 𝒮ʟ

-- The same instance `src/L/GCH.lagda.md:30` names, at the same 𝒮ʟ.
module ModelL = FOL.ZFModel 𝒮ʟ

-- =====================================================================
-- SECTION 1.  W3.  THE TWO KAPPA.
--
--   `GCHStatement` binds its κ at SL.S with three certificates:
--   IsOrd (fst κ), IsCardinalL κ, and fst κ ∉ ω
--   (src/L/GCH.lagda.md:60-63).
--
--   `Devlin55.BoundedSubsetAt` binds its κ at SV.S with three:
--   IsOrd κ, IsCardinal κ, and κ ∉ ω
--   (src/L/BoundedSubset.lagda.md:1386).
--
--   Under κ := fst κ two of the three certificates are the SAME type.
--   `kappa-agrees` is the residue: everything the theorem's κ demands
--   that the statement's κ does not give.
-- =====================================================================

-- The two certificates that DO agree, written at the statement's
-- binding.  If this type is not the theorem's, W3 has already failed.
kappa-shared : Type (ℓ-suc ℓ)
kappa-shared =
    (κ : SL.S)
  → IsOrd (fst κ)
  → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → (IsOrd (fst κ) × (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥))

-- THE RESIDUE.  The statement gives `IsCardinalL κ`, the internal
-- cardinal (src/L/Cardinal.lagda.md:230-233).  The theorem demands
-- `IsCardinal (fst κ)`, the AMBIENT cardinal
-- (src/L/BoundedSubset.lagda.md:1046-1047).  This is the whole price of
-- putting the statement's κ into the theorem's κ slot.
kappa-agrees : Type (ℓ-suc ℓ)
kappa-agrees =
    (κ : SL.S)
  → IsOrd (fst κ)
  → IsCardinalL κ
  → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → IsCardinal (fst κ)

-- =====================================================================
-- SECTION 2.  THE BOUNDED-SUBSET THEOREM, AS A CLOSED TYPE.
--
--   `Devlin55.BoundedSubsetAt` is a module and its telescope is not a
--   Π-type.  This section writes that telescope out, hypotheses and all,
--   so the theorem can stand as the ANTECEDENT of an implication.
--   Nothing is discharged and nothing is hidden.
--   Basis: src/L/BoundedSubset.lagda.md:1385-1395 for the outer
--   telescope, :1554-1558 for `Co`, :1621-1622 for the conclusion.
-- =====================================================================

-- The square law at `sucV α`, the fifth outer hypothesis, written out
-- (src/L/BoundedSubset.lagda.md:1388-1390).
SqLaw : SV.S → Type (ℓ-suc ℓ)
SqLaw α =
    (δ : SV.S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
  → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
      ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)

-- The instance, opened so that `Co`'s two hypotheses can name the hull
-- and its collapse.  `levelIn` and `cover` speak of `HS.C.πX` and
-- `HS.M`, which exist only INSIDE the instance
-- (src/L/BoundedSubset.lagda.md:1405, :913-914).
module Tele
  (κ : SV.S) (ordκ : IsOrd κ) (cardκ : IsCardinal κ)
  (κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥)
  (α : SV.S) (ordα : IsOrd α) (α∈κ : ⟨ α ∈ˢ κ ⟩)
  (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  (sq : SqLaw α)
  (x : SV.S) (x⊆Lα : (z : SV.S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
  (absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
  (lam : SV.S) (ordλ : IsOrd lam) (α∈λ : ⟨ α ∈ˢ lam ⟩)
  (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩)
  where

  module BSA = Devlin55.BoundedSubsetAt
    κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs lam ordλ α∈λ succλ x∈Lλ

  -- `Co`'s first hypothesis (src/L/BoundedSubset.lagda.md:1555).
  LevelIn : Type (ℓ-suc ℓ)
  LevelIn = (δ : SV.S) → IsOrd δ → ⟨ δ ∈ˢ BSA.HS.C.πX ⟩
          → ⟨ Lset δ ∈ˢ BSA.HS.C.πX ⟩

  -- `Co`'s second hypothesis (src/L/BoundedSubset.lagda.md:1556-1557).
  Cover : Type (ℓ-suc ℓ)
  Cover = (y : SV.S) → ⟨ y ∈ˢ BSA.HS.M ⟩
        → ∥ Σ[ γ ∈ SV.S ]
             ( IsOrd γ
             × ⟨ γ ∈ˢ BSA.HS.C.πX ⟩
             × ⟨ BSA.HS.C.π y ∈ˢ Lset γ ⟩ ) ∥₁

  -- The conclusion, under the two carried hypotheses
  -- (src/L/BoundedSubset.lagda.md:1621-1622).
  At : Type (ℓ-suc ℓ)
  At = LevelIn → Cover → ⟨ x ∈ˢ Lset κ ⟩

-- THE THEOREM AS THE TREE HAS IT.  Every hypothesis of the module
-- telescope survives as a Π argument, `levelIn` and `cover` included.
BoundedSubsetTheorem : Type (ℓ-suc ℓ)
BoundedSubsetTheorem =
    (κ : SV.S) (ordκ : IsOrd κ) (cardκ : IsCardinal κ)
    (κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥)
    (α : SV.S) (ordα : IsOrd α) (α∈κ : ⟨ α ∈ˢ κ ⟩)
    (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    (sq : SqLaw α)
    (x : SV.S) (x⊆Lα : (z : SV.S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
    (absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
    (lam : SV.S) (ordλ : IsOrd lam) (α∈λ : ⟨ α ∈ˢ lam ⟩)
    (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
    (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩)
  → Tele.At κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
      lam ordλ α∈λ succλ x∈Lλ

-- =====================================================================
-- SECTION 3.  THE OBLIGATION.  THE LAST MILE, AS A TYPE.
--
--   The implication from the bounded-subset theorem to `GCHStatement`.
--   NO HOLES.  NOT INHABITED.  The brief ordered the type and forbade
--   the term, and section `## THE INPUT LIST` of the report says, for
--   every name this type mentions, where that name lives.
--
--   READ THE ANTECEDENT WITH SECTION 1.  `BoundedSubsetTheorem` binds
--   its κ at SV.S under `IsCardinal`; `GCHStatement` binds its κ at
--   SL.S under `IsCardinalL`.  The type below is well formed because
--   the two κ never meet inside it: the antecedent is CLOSED.  An
--   inhabitant would have to make them meet, and `kappa-agrees`
--   (section 1) is what it would have to supply.
-- =====================================================================

GCHBridge : ModelL.isZFModel → Type (ℓ-suc ℓ)
GCHBridge zf = BoundedSubsetTheorem → GCHStatement zf

-- =====================================================================
-- SECTION 4.  THE RESIDUES, AS TYPES.  NOT OBLIGATIONS.
--
--   AD12 gives this brief ONE obligation and section 3 is it.  Nothing
--   below is inhabited and nothing below is asked for.  These are the
--   rows of the report's `## WHAT IS STATED NOWHERE`, written as types
--   so that the mathematician reads a typechecked statement and not my
--   prose.  Each carries the `file:line` of the slot it fills.
-- =====================================================================

-- 4.1  THE SUCCESSOR L-CARDINAL EXISTS.  `GCHStatement` opens with a
-- truncated Σ over δ (src/L/GCH.lagda.md:65-68) and `SuccCardL δ κ`
-- (:46-53) is its first conjunct.  Nothing in src/ produces an
-- `IsCardinalL` witness at all.
SuccCardExists : Type (ℓ-suc ℓ)
SuccCardExists =
    (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ
  → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → ∥ Σ[ δ ∈ SL.S ] SuccCardL δ κ ∥₁

-- 4.2  SECTION 1's RESIDUE, AT THE SITE THE USE NEEDS.  The theorem
-- concludes `x ∈ˢ Lset κ` for its own κ (src/L/BoundedSubset.lagda.md:1621)
-- and demands `α ∈ˢ κ` (:1386-1387).  To land a subset of the statement's
-- κ in the stage at δ, the theorem's κ must be `fst δ` and the theorem's
-- α must be `fst κ`.  So the ambient cardinality is wanted at δ.
AmbientAtSucc : Type (ℓ-suc ℓ)
AmbientAtSucc =
  (κ δ : SL.S) → SuccCardL δ κ → IsCardinal (fst δ)

-- 4.2b  WHAT THE THEOREM ACTUALLY SPENDS, WHICH IS LESS THAN IT ASKS FOR.
-- `cardκ` is consumed exactly TWICE inside `BoundedSubsetAt`, at
-- src/L/BoundedSubset.lagda.md:1597 and :1601, and BOTH times as
-- `cardκ α α∈κ`: the δ argument is the telescope's own α, never anything
-- else.  So the proof never uses `IsCardinal κ` at any other member.  The
-- weakest hypothesis that carries the same two lines is this one, at the
-- α the telescope has already fixed.
CardSpentAt : SV.S → SV.S → Type ℓ
CardSpentAt κ α = ⟪ κ ⟫ ↪ ⟪ α ⟫ → Empty.⊥

-- And the residue of section 1 restated against it: this, not full
-- ambient cardinality, is what an inhabitant of the bridge must supply.
AmbientSpentAtSucc : Type (ℓ-suc ℓ)
AmbientSpentAtSucc =
  (κ δ : SL.S) → SuccCardL δ κ → CardSpentAt (fst δ) (fst κ)

-- 4.3  A CONSTRUCTIBLE SUBSET OF κ IS A SUBSET OF THE STAGE AT κ.  The
-- theorem's `x⊆Lα` slot (src/L/BoundedSubset.lagda.md:1391) at α = fst κ.
SubsetIntoStage : ModelL.isZFModel → Type (ℓ-suc ℓ)
SubsetIntoStage zf =
    (κ y : SL.S) → IsOrd (fst κ) → ⟨ fst y ∈ˢ fst (𝒫 κ) ⟩
  → (z : SV.S) → ⟨ z ∈ˢ fst y ⟩ → ⟨ z ∈ˢ Lset (fst κ) ⟩
  where open ModelL.isZFModel zf using ( 𝒫 )

-- 4.4  THE ABSORBING INJECTION, AT THE THEOREM'S OWN SHAPE.
-- `src/L/Absorption.lagda.md:635-637` delivers a term NAMED `absorbs`
-- whose type is `⟪ sucV (fst γ) ⟫ ↪ ⟪ fst γ ⟫`.  That is not this shape,
-- and C-42 forbids reading one as the other.
AbsorbsAt : Type (ℓ-suc ℓ)
AbsorbsAt =
    (α x : SV.S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → ((z : SV.S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
  → ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫

-- 4.5  THE LIMIT STAGE ABOVE α THAT ALREADY HOLDS x.  The theorem's last
-- four slots (src/L/BoundedSubset.lagda.md:1393-1395).  `isL x` gives a
-- stage by definition (src/L/Constructible.lagda.md:376), but neither the
-- successor closure nor `α ∈ˢ lam`.
LimitAbove : Type (ℓ-suc ℓ)
LimitAbove =
    (α x : SV.S) → IsOrd α → ⟨ isL x ⟩
  → ∥ Σ[ lam ∈ SV.S ]
       ( IsOrd lam
       × ⟨ α ∈ˢ lam ⟩
       × ((d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
       × ⟨ x ∈ˢ Lset lam ⟩ ) ∥₁

-- 4.6  THE STAGE AT δ IS COUNTED BY δ, WITH A CODE.  This is where the
-- counting leg lands: `L.StageCardinal.Upper.stage-card-upper`
-- (src/L/StageCardinal.lagda.md:564) is the AMBIENT injection
-- `⟪ Lset α ⟫ ↪ ⟪ α ⟫`, and `InjL` wants a coded one
-- (src/L/GCH.lagda.md:37-38).
StageCountedCoded : Type (ℓ-suc ℓ)
StageCountedCoded =
    (δ Lδ : SL.S) → IsOrd (fst δ) → (fst Lδ ≡ Lset (fst δ))
  → InjL Lδ δ

-- 4.7  THE EASY LEG.  `InjL δ (𝒫 κ)`, the third conjunct of the
-- statement (src/L/GCH.lagda.md:68).  The bounded-subset theorem says
-- nothing about it: it is not on this bridge at all.
SuccIntoPower : ModelL.isZFModel → Type (ℓ-suc ℓ)
SuccIntoPower zf =
    (κ δ : SL.S) → SuccCardL δ κ → InjL δ (𝒫 κ)
  where open ModelL.isZFModel zf using ( 𝒫 )

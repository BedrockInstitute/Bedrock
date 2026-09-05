{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.698] PROBE.  ThroughDoor, the remaining target of the
-- 𝒟ₒ-intro route to HierInK, as [LJ-1.693] states it.  Lands nothing
-- in src/.
--
--   THE OBLIGATION  through-door.  NOT INHABITED.
--                   review-of-through-door.md states the stop.
--   DELIVERED       empty-door: the empty table is definable by ⊥̇.
--                   recordedΔ₀: PairGraphAt, bound by the ordinal,
--                   relativized to a stage, is Δ₀.
--                   bound-of: mkBoundedFo of that formula.
--                   Carved.carved-door: 𝒟ₒ-intro fires on the lift.
--   NOT INHABITED   ApproxInK (532 FALSE, Probe532.agda:206-209).
--                   Pin.down is not rebuilt.  adequacy-bnd is not
--                   rebuilt.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-698.Probe698 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; ∃̇∈; ⊥̇ )
open import FOL.LevyHierarchy using ( Δ₀ )
open import FOL.Manipulation.Bounding using ( BoundedFo )
open import FOL.Manipulation.Relativize using ( relativize; Δ₀-relativize )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅; ∅-empty )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; IsOrd; Lset; 𝒟ₒ; 𝒟ₒ-inv )
open import L.Ordinal {ℓ} using ( ∅-ord )
open import L.Axioms.Basic {ℓ} using ( LsetS; extensionalL; ∅∈L )
open import L.Axioms.Separation {ℓ} lem using ( mkBoundedFo; Below′; module AtStage )
open import L.Hierarchy {ℓ} lem
  using ( hierL; hierL-spec; IsHier; Recorded; hier-unique )
open import L.Coding.Sequence {ℓ} lem using ( PairGraphAt )
open import LJ-1-693.Probe693 {ℓ} lem
  using ( ThroughDoor; Door; from-door; HierInK; IsLimit )

open import Cubical.Data.FinData using ( zero; suc )
import Cubical.Data.Empty as Empty
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; extensionality; _⊆_; ⟪_⟫ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ


-- =====================================================================
-- SECTION 1.  THE TYPE THE PREDECESSOR DELIVERED AND DID NOT INHABIT.
--
-- Verbatim Probe693.agda:135-139.  The 693 report is NO-GO at
-- hier-in-K-placement, not at this type.  from-door
-- (Probe693.agda:141-150) is ThroughDoor → HierInK and is not rebuilt.
-- =====================================================================

the-type : Type (ℓ-suc ℓ)
the-type = ThroughDoor

the-consumer : ThroughDoor → HierInK
the-consumer = from-door


-- =====================================================================
-- SECTION 2.  D-10 SYNTAX.  The delivered pair-graph, bound by the
-- ordinal, relativized to a stage, is Δ₀.
--
-- PairGraphAt (src/L/Coding/Sequence.lagda.md:328-329) says z is the
-- pair (c, L_c).  relativize of any formula is Δ₀
-- (src/FOL/Manipulation/Relativize.lagda.md:72).  This is the
-- differently presented Δ₀ formula [LJ-1.693]'s critic did not
-- exclude (review-of-LJ-1-693-1.md:125-129).
-- =====================================================================

recordedFo : (γ : S) → Formula S 1
recordedFo γ = ∃̇∈ (con γ) (PairGraphAt (suc zero) zero)

recordedΔ₀ : (γ A : S) → Δ₀ (relativize A (recordedFo γ))
recordedΔ₀ γ A = Δ₀-relativize A (recordedFo γ)

recorded-at : (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩)
            → Δ₀ (relativize (LsetS γ oγ) (recordedFo (γ , hγ)))
recorded-at γ oγ hγ = recordedΔ₀ (γ , hγ) (LsetS γ oγ)

-- The constants of that Δ₀ formula (the ordinal, the stage, and the
-- graph's numerals) lie in some stage.  mkBoundedFo is total
-- (src/L/Axioms/Separation.lagda.md:449).
bound-of : (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩)
         → Σ[ σ ∈ V ℓ ] (IsOrd σ × BoundedFo (Below′ σ)
              (relativize (LsetS γ oγ) (recordedFo (γ , hγ))))
bound-of γ oγ hγ =
  mkBoundedFo (relativize (LsetS γ oγ) (recordedFo (γ , hγ)))

-- 𝒟ₒ-intro fires on the lifted formula at the stage that bounds its
-- constants.  This is a door.  It is not yet ThroughDoor: the carved
-- set is not identified with hierL, and the stage is not shown to
-- lie in the bridge's α.
module Carved (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩) where
  φᵣ : Formula S 1
  φᵣ = relativize (LsetS γ oγ) (recordedFo (γ , hγ))

  σ : V ℓ
  σ = bound-of γ oγ hγ .fst

  oσ : IsOrd σ
  oσ = bound-of γ oγ hγ .snd .fst

  hφ : BoundedFo (Below′ σ) φᵣ
  hφ = bound-of γ oγ hγ .snd .snd

  open AtStage σ oσ

  carved : V ℓ
  carved = carve (RL.liftFo φᵣ hφ)

  carved∈𝒟ₒ : ⟨ carved ∈ 𝒟ₒ (Lset σ) ⟩
  carved∈𝒟ₒ = carve∈𝒟ₒ (RL.liftFo φᵣ hφ)

  carved-door : Door (Lset σ) carved
  carved-door = 𝒟ₒ-inv (Lset σ) carved carved∈𝒟ₒ


-- =====================================================================
-- SECTION 3.  THE EMPTY TABLE IS DEFINABLE BY ⊥̇, OVER ANY STAGE.
--
-- Recorded ∅ z is empty, so hierL ∅ is the empty set.  defSet ⊥̇ is
-- the empty set (src/L/Axioms/Basic.lagda.md:491-502).  IsLimit of
-- ThroughDoor already has ∅ ∈ α (Probe693.agda:72-75).
-- =====================================================================

∅ʟ : S
∅ʟ = ∅ , ∅∈L

empty-is : IsHier ∅ ∅ʟ
empty-is z = ⇔toPath fwd bwd
  where
  fwd : ⟨ fst z ∈ ∅ ⟩ → ⟨ Recorded ∅ (fst z) ⟩
  fwd z∈ = Empty.rec
    (∅-empty (fst z) (∈∈ₛ {a = fst z} {b = ∅} .fst z∈))
  bwd : ⟨ Recorded ∅ (fst z) ⟩ → ⟨ fst z ∈ ∅ ⟩
  bwd r = PT.rec (snd (fst z ∈ ∅))
    (λ { (c , (c∈ , _)) → Empty.rec
      (∅-empty (fst c) (∈∈ₛ {a = fst c} {b = ∅} .fst c∈)) }) r

empty-hier : (h : ⟨ isL ∅ ⟩) (o : IsOrd ∅)
           → hierL ∅ h o ≡ ∅ʟ
empty-hier h o = hier-unique ∅ (hierL ∅ h o) ∅ʟ (hierL-spec ∅ h o) empty-is

empty-fst : (h : ⟨ isL ∅ ⟩) (o : IsOrd ∅)
          → fst (hierL ∅ h o) ≡ ∅
empty-fst h o = cong fst (empty-hier h o)

empty-def : (σ : V ℓ) → DefOf.defSet (Lset σ) ⊥̇ ≡ ∅
empty-def σ = extensionality (DefOf.defSet (Lset σ) ⊥̇) ∅ (sub₁ , sub₂)
  where
  module DefC = DefOf (Lset σ)
  sub₁ : ⟨ DefC.defSet ⊥̇ ⊆ ∅ ⟩
  sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ ∅))
    (λ { ((m , hm) , q) → Empty.rec* hm })
    (∈∈ₛ {a = y} {b = DefC.defSet ⊥̇} .snd y∈ₛ)
  sub₂ : ⟨ ∅ ⊆ DefC.defSet ⊥̇ ⟩
  sub₂ y y∈ₛ = Empty.rec (∅-empty y y∈ₛ)

empty-door : (σ : V ℓ) (h : ⟨ isL ∅ ⟩) (o : IsOrd ∅)
           → Door (Lset σ) (fst (hierL ∅ h o))
empty-door σ h o =
  subst (λ x → Door (Lset σ) x) (sym (empty-fst h o))
    ∣ ⊥̇ , empty-def σ ∣₁

empty-door-at : (σ : V ℓ) → Door (Lset σ) (fst (hierL ∅ ∅∈L ∅-ord))
empty-door-at σ = empty-door σ ∅∈L ∅-ord

-- IsLimit of ThroughDoor already has ∅ ∈ α, so the empty door has a
-- stage in every bound the bridge uses.
empty-in-limit : (α : V ℓ) → IsLimit α → ⟨ ∅ ∈ α ⟩
empty-in-limit α (_ , p , _) = p


-- =====================================================================
-- SECTION 4.  THE OBLIGATION NAME IS ABSENT ON PURPOSE.  No postulate
-- stands in for it.  Carved.carved-door is a door, not ThroughDoor:
-- the carved set is not identified with hierL, and bound-of's stage
-- is not shown to lie in α.
-- =====================================================================

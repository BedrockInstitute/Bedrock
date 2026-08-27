{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.693] PROBE.  HierInK from stage placement, through 𝒟ₒ-intro,
-- at the residue [LJ-1.688] named: HierBelow / StageHigh.  Lands
-- nothing in src/.
--
--   THE OBLIGATION  hier-in-K-placement.  NOT INHABITED.  W3 measured
--                   that 𝒟ₒ-intro does not reach HierBelow at the
--                   stage the bridge uses.  review-of-hier-in-K-placement.md
--                   states the stop.
--   NOT INHABITED   ApproxInK (532 FALSE, Probe532.agda:206-209).
--                   HierInK (Probe532.agda:274-277) remains a type.
--                   HierBelow / StageHigh remain types (Probe536).
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-693.Probe693 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀; Σ₁ )
open import FOL.Manipulation.Bounding using ( BoundedFo )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono; Lset-in; Lset→isL
        ; 𝒟ₒ; 𝒟ₒ-intro )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.Axioms.Separation {ℓ} lem using ( module AtStage )
open import L.Hierarchy {ℓ} lem using ( hierL )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import LJ-1-520.Probe520 {ℓ} lem using ( levelFo-Σ₁; no-Σ₁-graph )

open import Cubical.Data.FinData using ( Fin )
open import Cubical.Data.Nat using ( ℕ; zero; suc )
import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using () renaming ( _⊨ᵐ_ to _⊨_ )


-- =====================================================================
-- SECTION 1.  THE TYPES THE PREDECESSORS DELIVERED AND DID NOT INHABIT.
--
-- HierInK is verbatim Probe532.agda:274-277, restated Probe688.agda:59-62.
-- The 532 report is NO-GO at ApproxInK, not at this type.  This file
-- does not inhabit ApproxInK.
--
-- HierBelow / HierBelowAll / step are verbatim Probe536.agda:129-131,
-- :186-187, :354-355.  StageHigh is not restated: the reduction
-- HierBelowAll → StageHigh is already green there (:357-358).
-- =====================================================================

IsLimit : V ℓ → Type (ℓ-suc ℓ)
IsLimit α = IsOrd α
          × ⟨ ∅ ∈ α ⟩
          × ((β : V ℓ) → ⟨ β ∈ α ⟩ → ⟨ sucV β ∈ α ⟩)

HierInK : Type (ℓ-suc ℓ)
HierInK = (α : V ℓ) → IsLimit α
        → (β : V ℓ) (hβ : ⟨ isL β ⟩) (oβ : IsOrd β) → ⟨ β ∈ α ⟩
        → ⟨ fst (hierL β hβ oβ) ∈ Lset α ⟩

step : ℕ → V ℓ → V ℓ
step zero    γ = γ
step (suc n) γ = sucV (step n γ)

isL-ord : (β : V ℓ) → IsOrd β → ⟨ isL β ⟩
isL-ord β oβ = Lset→isL (sucV β) (suc-ord oβ) β (ord∈Lset-suc β oβ)

HierBelow : (γ : V ℓ) → IsOrd γ → Type (ℓ-suc ℓ)
HierBelow γ oγ = ⟨ fst (hierL γ (isL-ord γ oγ) oγ) ∈ Lset (step 3 γ) ⟩

HierBelowAll : Type (ℓ-suc ℓ)
HierBelowAll = (γ : V ℓ) (oγ : IsOrd γ) → HierBelow γ oγ


-- =====================================================================
-- SECTION 2.  THE DOOR, WRITTEN OUT AND ASCRIBED AGAINST `𝒟ₒ-intro`.
--
-- Verbatim Probe536.agda:76-80.  `door` typechecks exactly when Door
-- is 𝒟ₒ-intro's premise and not a paraphrase.
-- =====================================================================

Door : V ℓ → V ℓ → Type (ℓ-suc ℓ)
Door A x = ∥ Σ[ φ ∈ Formula ⟪ A ⟫ 1 ] (DefOf.defSet A φ ≡ x) ∥₁

door : (A x : V ℓ) → Door A x → ⟨ x ∈ 𝒟ₒ A ⟩
door = 𝒟ₒ-intro


-- =====================================================================
-- SECTION 3.  WHERE THE DOOR LANDS, AND THE STAGE THE BRIDGE USES.
--
-- The bridge wants hierL β ∈ Lset α (HierInK, K ≡ Lset α along qK,
-- Probe688.agda:86-93).  𝒟ₒ-intro at A = Lset σ places x in 𝒟ₒ (Lset σ),
-- which is Lset (sucV σ) (src/L/Axioms/Basic.lagda.md:196).  So a carve
-- FROM Lset α lands in Lset (sucV α), which is not HierInK.
--
-- To land IN Lset α the door must fire at a STRICTLY EARLIER stage:
-- some δ ∈ α, and x ∈ 𝒟ₒ (Lset δ).  That is Lset-in
-- (src/L/Constructible.lagda.md:329-330).
--
-- P-l.  These types name Lset α and Lset δ, which are opaque
-- (src/L/Constructible.lagda.md:221-223).  They do not name a
-- transparent presentation of the stage.
-- =====================================================================

door-next : (σ x : V ℓ) → Door (Lset σ) x → ⟨ x ∈ Lset (sucV σ) ⟩
door-next σ x d =
  subst (λ w → ⟨ x ∈ w ⟩) (sym (Lset-suc σ)) (door (Lset σ) x d)

lands-in : (α δ x : V ℓ) → ⟨ δ ∈ α ⟩ → Door (Lset δ) x → ⟨ x ∈ Lset α ⟩
lands-in α δ x δ∈α d = Lset-in α δ x δ∈α (door (Lset δ) x d)

-- HierInK through 𝒟ₒ-intro, stated as a type.  Not inhabited.
ThroughDoor : Type (ℓ-suc ℓ)
ThroughDoor =
    (α : V ℓ) → IsLimit α
  → (β : V ℓ) (hβ : ⟨ isL β ⟩) (oβ : IsOrd β) → ⟨ β ∈ α ⟩
  → ∥ Σ[ δ ∈ V ℓ ] (⟨ δ ∈ α ⟩ × Door (Lset δ) (fst (hierL β hβ oβ))) ∥₁

from-door : ThroughDoor → HierInK
from-door td α lim β hβ oβ β∈α =
  PT.rec (snd (fst (hierL β hβ oβ) ∈ Lset α)) unpack
    (td α lim β hβ oβ β∈α)
  where
  unpack : Σ[ δ ∈ V ℓ ]
             (⟨ δ ∈ α ⟩ × Door (Lset δ) (fst (hierL β hβ oβ)))
         → ⟨ fst (hierL β hβ oβ) ∈ Lset α ⟩
  unpack (δ , (δ∈α , d)) =
    lands-in α δ (fst (hierL β hβ oβ)) δ∈α d


-- =====================================================================
-- SECTION 4.  THE SECOND DOOR AT THE BOUND THE BRIDGE USES.
--
-- AtStage (src/L/Axioms/Separation.lagda.md:119-135, :199-231),
-- re-ascribed at Probe536/runs/W3.agda:111-141.  Instantiated here at
-- a generic ordinal σ, which is the shape of K ≡ Lset α.  The two
-- hypotheses are Δ₀ and BoundedFo Below.  A larger stage does not
-- drop either hypothesis.
-- =====================================================================

module AtBound (σ : V ℓ) (oσ : IsOrd σ) where
  open AtStage σ oσ

  wants-Δ₀ :
      (φ : Formula S 1) (h : BoundedFo Below φ) (dφ : Δ₀ φ)
    → (m : ⟪ Lset σ ⟫) (xL : ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩)
    → ⟨ ((⟪ Lset σ ⟫↪ m , xL) ∷ []) ⊨ φ ⟩
    → ⟨ ⟪ Lset σ ⟫↪ m ∈ carve (RL.liftFo φ h) ⟩
  wants-Δ₀ = imageIn

  lands-in-𝒟ₒ : (ψ : Formula ⟪ Lset σ ⟫ 1) → ⟨ carve ψ ∈ 𝒟ₒ (Lset σ) ⟩
  lands-in-𝒟ₒ = carve∈𝒟ₒ


-- =====================================================================
-- SECTION 5.  THE GRADE, RE-ASCRIBED AND NOT REBUILT.
--
-- The characterizing formula of the table is not Δ₀ and not Σ₁ at the
-- delivered graph.  The graded substitute is Σ₁ and not Δ₀.  Neither
-- feeds AtBound.wants-Δ₀.  σ₁-up (src/FOL/Absoluteness.lagda.md:182-185)
-- does not apply to LsetGraphAt.  SaysLevel at levelFo is unpaid
-- (Probe520.agda:183-188).
--
-- no-Σ₁-graph is imported from the probe that typechecked it
-- (Probe520.agda:202-204).  no-Δ₀-levelFo is the ascription [LJ-1.536]
-- already ran (Probe536.agda:115-116).
-- =====================================================================

no-Δ₀-levelFo : {n : ℕ} (w b : Fin n) → Δ₀ (fst (levelFo-Σ₁ w b)) → Empty.⊥
no-Δ₀-levelFo w b ()

no-Δ₀-graph : {n : ℕ} (w b : Fin n) → Δ₀ (LsetGraphAt w b) → Empty.⊥
no-Δ₀-graph w b ()

graph-not-Σ₁ : {n : ℕ} (w b : Fin n) → Σ₁ (LsetGraphAt w b) → ⊥* {ℓ}
graph-not-Σ₁ = no-Σ₁-graph


-- =====================================================================
-- SECTION 6.  ROOM, AND THE REDUCTION HIERBELOW PAYS.
--
-- [LJ-1.519] already bought steps-stay and stage-below
-- (Probe519.agda:200, :208).  Restated here at the 3-component IsLimit
-- HierInK uses.  [LJ-1.536] said in prose that HierBelowAll pays
-- HierInK (lj-1.536-report.md:171).  from-HierBelow is that row.
--
-- THIS IS NOT THE OBLIGATION.  It takes HierBelowAll as a hypothesis.
-- [LJ-1.536] did not inhabit HierBelowAll.  The successor step of
-- HierBelow is AdjoinAt (Probe536.agda:278-280) and is not rebuilt.
-- =====================================================================

steps-stay : (α : V ℓ)
           → ((δ : V ℓ) → ⟨ δ ∈ α ⟩ → ⟨ sucV δ ∈ α ⟩)
           → (γ : V ℓ) → ⟨ γ ∈ α ⟩ → (n : ℕ) → ⟨ step n γ ∈ α ⟩
steps-stay α suc-cl γ γ∈α zero    = γ∈α
steps-stay α suc-cl γ γ∈α (suc n) =
  suc-cl (step n γ) (steps-stay α suc-cl γ γ∈α n)

from-HierBelow : HierBelowAll → HierInK
from-HierBelow hb α (_ , _ , suc-cl) β hβ oβ β∈α =
  subst (λ p → ⟨ fst (hierL β p oβ) ∈ Lset α ⟩)
    (snd (isL β) (isL-ord β oβ) hβ)
    (Lset-mono (steps-stay α suc-cl β β∈α 3) (hb β oβ))


-- =====================================================================
-- SECTION 7.  W3, LIFTED.  𝒟ₒ-intro reaches HierInK if and only if
-- ThroughDoor is paid: some δ ∈ α and a Formula ⟪ Lset δ ⟫ 1 whose
-- defSet is hierL β.  AtStage at that δ still wants Δ₀.  The delivered
-- graph is not Δ₀ and not Σ₁.  The graded substitute is not Δ₀.
-- HierBelowAll would pay HierInK by from-HierBelow, and HierBelowAll
-- is the same unpaid door at Lset (step 2 γ).  Room is not the miss:
-- steps-stay is green.  DOWN is not rebuilt (Probe688.agda:156-159).
--
-- THE OBLIGATION NAME IS ABSENT ON PURPOSE.  No postulate stands in
-- for it.
-- =====================================================================

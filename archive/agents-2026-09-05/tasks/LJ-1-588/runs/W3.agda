{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.588]  W3.  THE δ THAT `gch-from-five` SPENDS ROW 4 AT.
--             TYPE ONLY.
--
-- THE BRIEF'S W3, VERBATIM: "that δ, with its hypotheses in scope,
-- written out, TYPE ONLY".  Written FIRST and typechecked ALONE,
-- before any other Agda of this task.
--
-- THE QUESTION IT ANSWERS AND THE ONLY ONE: what is in scope at the
-- one place `gch-from-five` applies row 4?  Everything else in this
-- task follows from what is true of that one object.
--
-- D-10, ANSWERED BY GREP BEFORE THIS FILE WAS WRITTEN.  `b9` occurs
-- TWELVE times in `agents/tasks/LJ-1-564/Probe564.agda`, one to a
-- line, and it is APPLIED exactly ONCE, at `:210`,
-- `b9 δ Lδ ordδ refl`.  The other eleven are binders (`:209`, `:234`,
-- `:358`, `:376`, `:416`, `:462`) or pass-throughs (`:235`, `:359`,
-- `:378`, `:417`, `:463`), and each hands it on unchanged.  So there
-- is ONE spend site and this file is its scope.
--
-- NO TERM BELOW IS A PROOF.  Every declaration is a TYPE.
--
-- CALIBER.  The program set GHCRTS on this pane.  I did not set it.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-588.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; Lset; isL )
open import L.GCH {ℓ} lem using ( GCHStatement; SuccCardL; InjL )
import FOL.ZFModel
open import Cubical.Data.Sigma using ( _×_ )
open InfinitySet {ℓ} using ( ω; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
module ModelL = FOL.ZFModel 𝒮ʟ

-- THE PREDECESSOR, AT THE TYPE ITS REPORT DELIVERED.  `[LJ-1.564]` is
-- GO (agents/tasks/LJ-1-564/lj-1.564-report.md:1) and its probe is
-- green, so `stage-is-L` below is that file's theorem and not a
-- transcription.
import LJ-1-564.Probe564
import LJ-1-550.Probe550
import LJ-1-558.Probe558
module P564 = LJ-1-564.Probe564 {ℓ} lem
module P550 = LJ-1-550.Probe550 {ℓ} lem
module P558 = LJ-1-558.Probe558 {ℓ} lem

-- ===================================================================
-- THE SPEND SITE, WRITTEN OUT.
--
--   `power-into-succ-from-landing` (Probe564.agda:203-226) is the only
--   body that applies row 4, and `gch-from-five` reaches it through
--   `power-into-succ-at` (Probe564.agda:351-360), whose own head binds
--   `IsOrd (fst κ)` and `κ ∉ ω` (`PowerIntoSuccAt`,
--   Probe564.agda:327-330).  So THOSE TWO ARE IN SCOPE at the spend,
--   and they come from `GCHStatement`'s head
--   (src/L/GCH.lagda.md:61, :64) through
--   `gch-route-with-premised-hard` (Probe564.agda:335-341).
--
--   `δ` is not free: it is bound by `SuccCardL δ κ`
--   (src/L/GCH.lagda.md:46-53), which `[LJ-1.528]`'s `b4-paid`
--   produced (Probe564.agda:439-440).
-- ===================================================================

-- WHAT ROW 4 IS ASKED FOR, WITH EVERYTHING THE SITE HAS.  The
-- conclusion is `b9 δ Lδ ordδ refl`'s type at Probe564.agda:210, with
-- `Lδ` inlined from Probe564.agda:218-219.
Row4Spend : Type (ℓ-suc ℓ)
Row4Spend =
    (κ δ : SL.S) → IsOrd (fst κ) → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → (sc : SuccCardL δ κ)
  → InjL (Lset (fst δ) , P564.stage-is-L δ (fst sc)) δ

-- `[LJ-1.585]`'s TWO SIDE CONDITIONS AT THAT δ, AND NOWHERE ELSE.
-- `Row4Restricted` (Probe585.agda:163-166) carries `δ ∈ sucV α₀` and
-- `δ ∉ ω` (src/L/StageCardinal.lagda.md:564-566).  This is what the
-- site would have to supply.
CondsAtSpend : V ℓ → Type (ℓ-suc ℓ)
CondsAtSpend α₀ =
    (κ δ : SL.S) → IsOrd (fst κ) → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → SuccCardL δ κ
  → ⟨ fst δ ∈ˢ sucV α₀ ⟩ × (⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥)

-- AND THE SAME TWO WITH THE TOWER PARAMETER QUANTIFIED, WHICH IS HOW
-- `L.StageCardinal` ITSELF QUANTIFIES IT (src/L/StageCardinal.lagda.md
-- :15-19): the module takes α₀, so the function exists at every α₀.
CondsAtSpendGeneric : Type (ℓ-suc ℓ)
CondsAtSpendGeneric =
    (κ δ : SL.S) → IsOrd (fst κ) → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → SuccCardL δ κ
  → Σ[ α₀ ∈ V ℓ ] (⟨ fst δ ∈ˢ sucV α₀ ⟩ × (⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥))

-- THE FIVE-ROW BILL'S TYPE, RE-ASCRIBED SO THE OBLIGATION'S TYPE IS
-- NOT A TRANSCRIPTION LATER.  This is Probe564.agda:456-463.
FiveRowBill : Type (ℓ-suc (ℓ-suc ℓ))
FiveRowBill =
    (zf : ModelL.isZFModel)
  → P550.AmbientCardAtSucc → P550.SqAt → P550.CoHyps
  → P564.StageCountedCoded
  → P558.SuccIntoPower zf
  → GCHStatement zf

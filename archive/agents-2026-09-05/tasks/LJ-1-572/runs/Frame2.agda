{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.572]  THE D-10 SLICE.  THE ARITY, AND THE FRAME.
--
-- THE BRIEF ORDERS TWO READINGS BEFORE ANY OTHER AGDA IS SPENT, and
-- this file MEASURES both instead of arguing them.  It takes `lem`
-- alone: no `α₀`, no `sq`, so nothing here depends on the B9 site.
--
-- NOTHING IS POSTULATED.  Every hypothesis below is a PREMISE of the
-- row that names it, and the point of the row is that the tree does not
-- supply that premise.
--
-- CALIBER.  The program set GHCRTS on this pane.  I did not set it.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import L.Constructible using ( IsOrd )

module LJ-1-572.runs.Frame2 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Coding.Model {ℓ} using ( svAt; domAt )
open import L.Coding.Injection {ℓ} lem using ( injAt )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.GCH {ℓ} lem using ( InjL )

open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

import LJ-1-566.Probe566 {ℓ} lem as P566

-- The ordinal as an L-element, Probe568.agda:100-101's name.
isL-ord : (β : V ℓ) → IsOrd β → ⟨ isL β ⟩
isL-ord β oβ = Lset→isL (sucV β) (suc-ord oβ) β (ord∈Lset-suc β oβ)

ordS : (β : V ℓ) → IsOrd β → S
ordS β oβ = β , isL-ord β oβ


-- ===================================================================
-- 1.  D-10, FIRST READING: THE ARITY.  IT IS NOT THE OBSTRUCTION.
--
--     `Def` wants a `Formula S 3` (Probe568.agda:190 is
--     `P554.LinkAt a (val a b g)`, and `LinkAt`'s Σ is over
--     `Formula S 3`, Probe554.agda:81-82).
--
--     `InjCode`'s three formula conjuncts are used at arity 2, at the
--     environment `(F ∷ a ∷ [])` (src/L/Cardinal.lagda.md:225-227).
--     BUT THEY ARE NOT FIXED AT 2.  Each is arity-polymorphic:
--       `svAt  : ∀ {n} → Fin n → Formula S n`  src/L/Coding/Model.lagda.md:210
--       `domAt : ∀ {n} → Fin n → Fin n → Formula S n`  :278
--       `injAt : ∀ {n} → Fin n → Formula S n`  src/L/Coding/Injection.lagda.md:44
--     SO THEY COME TO 3 FOR FREE.  The three rows below are that fact,
--     checked.  The brief calls the arity "the whole risk in this
--     task": it is not a risk at all.
-- ===================================================================

svAt₃ : Formula S 3
svAt₃ = svAt zero

domAt₃ : Formula S 3
domAt₃ = domAt zero (suc zero)

injAt₃ : Formula S 3
injAt₃ = injAt zero


-- ===================================================================
-- 2.  D-10, SECOND READING: THE TWO DIRECTIONS.  `InjCode` SUPPLIES
--     NEITHER, AND THE TYPE IS THE REASON.
--
--     `Def a b g`'s two halves both mention `g`
--     (Probe554.agda:83-88: one direction sends a value to
--     satisfaction, the other reads a value back out).
--
--     `InjCode` TAKES THREE SETS AND NO FUNCTION.  So no instance of
--     it can state either half.  The row below is that arity, checked.
-- ===================================================================

injcode-names-no-function : S → S → S → Type (ℓ-suc ℓ)
injcode-names-no-function = InjCode


-- ===================================================================
-- 3.  AND `InjCode` AT B9's PAIR IS THE SITE'S CONCLUSION, NOT ITS
--     RAW MATERIAL.  `InjL a b` IS `∥ Σ[ F ] InjCode F a b ∥₁`
--     (src/L/GCH.lagda.md:37-38), and B9's obligation is
--     `InjL (LsetS δ oδ) (ordS δ oδ)` (Probe561.agda:376-378).
--
--     So a term of `InjCode` at B9's pair PAYS B9.  It is downstream
--     of the question this task asks, not upstream of it.
-- ===================================================================

B9-obligation-unfolds :
    (δ : V ℓ) (oδ : IsOrd δ)
  → InjL (LsetS δ oδ) (ordS δ oδ)
  ≡ ∥ Σ[ F ∈ S ] InjCode F (LsetS δ oδ) (ordS δ oδ) ∥₁
B9-obligation-unfolds _ _ = refl


-- ===================================================================
-- 4.  THE FRAME.  `[LJ-1.566]`'s INSTANCE IS NOT AT B9's PAIR, AND IT
--     MISSES ON BOTH COMPONENTS.
-- ===================================================================

-- 4.1  THE DELIVERED TERM, RE-ASCRIBED.  TYPE ONLY, from the file that
--      typechecked (Probe566.agda:492-500).
p566-frame :
    (a : S) (oa : IsOrd (fst a))
  → InjCode (P566.Carve.G a oa) a (P566.Carve.C a oa)
p566-frame = P566.injcode-assembled

-- 4.2  THE BISECT.  `Frame.agda` ALSO APPLIED `injcode-assembled` at
--      B9's `a`, with `IsOrd (fst (LsetS δ oδ))` as a premise.  THAT
--      FILE RAN 1360.52 s AND WAS KILLED (runs/frame-1.out, exit 143,
--      peak RSS 2.31 GB against a -M8g cap, CPU time equal to elapsed).
--      THIS FILE IS THE SAME FILE WITH THE TWO APPLICATIONS REMOVED.
--
--      WHAT REPLACES THEM COSTS NOTHING AND SAYS THE SAME THING.
--      `p566-frame` above ascribes the delivered signature, so the
--      demand `IsOrd (fst a)` is checked.  The row below identifies
--      B9's `fst a`.  Together they say: at B9's `a`,
--      `injcode-assembled` demands `IsOrd (Lset δ)`.
B9-a-carrier : (δ : V ℓ) (oδ : IsOrd δ) → fst (LsetS δ oδ) ≡ Lset δ
B9-a-carrier _ _ = refl

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.87] probe B: RED, deliberately.  The repaired witK does not
-- follow from the two premises.
--
-- The repaired witK (canonical frame of LJ-1.84, K₀ = LsetS lam):
--     (w : Sʟ) → closed ∧ shaped ∧ X₀ ∈ w
--              → w ⊆ AllCodes A₀            (premise 1, LJ-1.85)
--              → fst (AllCodes A₀) ∈ Lset lam  (premise 2, the frame
--                hypothesis, LJ-1.86)
--              → fst w ∈ Lset lam
--
-- The two premises decompose AllCodes A₀ ∈ Lset lam into
-- AllCodes A₀ ⊆ Lset δ for some δ ∈ lam (Lset-out plus 𝒟ₒ∋⊆), and
-- then bound the MEMBERS of w: every z ∈ w lies in Lset δ, hence in
-- Lset lam.  The last step needs
--     w ∈ 𝒟ₒ (Lset δ)     (w a definable subset of Lset δ)
-- and the premises do not supply it: this hierarchy is the DEFINABLE
-- power set, and a subset of a stage element need not appear one level
-- up (L.Axioms.Power.lagda.md:18-20: "Condensation is not part of
-- this").  The natural attempt below claims w ≡ defSet (Lset δ) ⊤̇,
-- i.e. w ≡ Lset δ, and Agda rejects it.
--
-- This file is expected to FAIL typechecking at w∈𝒟ₒδ.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ187B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ⊤̇ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-in; Lset-out
        ; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ∋⊆ )
open import L.Coding.Model {ℓ} using ( closedAt )
open import L.Coding.Shape {ℓ} using ( shapedAt )
open import L.Coding.InL {ℓ} using ( key; keyL; key∈closure )
open import L.Coding.Closed {ℓ} using ( clo )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import Cubical.Data.Vec using ( Vec; _∷_; [] )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

Sʟ : Type (ℓ-suc ℓ)
Sʟ = ZFStructure.S 𝒮ʟ

-- The canonical stage frame of LJ-1.84: carrier A₀ = LsetS α, bound
-- K₀ = LsetS lam, formula key X₀ = key of ⊤̇ over the empty alphabet.
module StageFrame
  (lam : V ℓ) (ordλ : IsOrd lam)
  (α : V ℓ) (ordα : IsOrd α)
  where

  A₀ : Sʟ
  A₀ = LsetS α ordα

  K₀ : Sʟ
  K₀ = LsetS lam ordλ

  K : Type ℓ
  K = Lift Empty.⊥

  ι : K → V ℓ
  ι = λ { (lift ()) }

  ιL : (k : K) → ⟨ isL (ι k) ⟩
  ιL = λ { (lift ()) }

  φ : Formula K zero
  φ = ⊤̇

  X₀ : Sʟ
  X₀ = key ι ιL φ , keyL ι ιL φ

  D : Sʟ
  D = clo ι ιL φ

  hX : ⟨ fst X₀ ∈ˢ fst D ⟩
  hX = key∈closure ι ιL φ

  γ₀ : Sʟ ^ 3
  γ₀ = A₀ ∷ K₀ ∷ X₀ ∷ []

  -- THE REPAIRED witK AT THE FRAME.  The two new premises are the
  -- second and third arguments.
  witK-repaired : (w : Sʟ)
    → ⟨ (w ∷ γ₀) ⊨ ((var (suc (suc (suc zero))) ∈̇ var zero)
         ∧̇ (closedAt zero ∧̇ shapedAt zero (suc zero))) ⟩
    → ((z : V ℓ) → ⟨ z ∈ˢ fst w ⟩ → ⟨ z ∈ˢ fst (AllCodes A₀) ⟩)
    → ⟨ fst (AllCodes A₀) ∈ˢ Lset lam ⟩
    → ⟨ fst w ∈ˢ Lset lam ⟩
  witK-repaired w _ w⊆All All∈Lλ =
    PT.rec (snd (fst w ∈ˢ Lset lam)) go
      (PT.map dec (Lset-out lam (fst (AllCodes A₀)) All∈Lλ))
    where
    dec : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ˢ lam ⟩ × ⟨ fst (AllCodes A₀) ∈ˢ 𝒟ₒ (Lset δ) ⟩)
        → Σ[ δ ∈ V ℓ ] (⟨ δ ∈ˢ lam ⟩
             × ((z : V ℓ) → ⟨ z ∈ˢ fst (AllCodes A₀) ⟩ → ⟨ z ∈ˢ Lset δ ⟩))
    dec (δ , δ∈lam , AC∈𝒟ₒδ) =
      δ , δ∈lam , 𝒟ₒ∋⊆ (Lset δ) (fst (AllCodes A₀)) AC∈𝒟ₒδ

    go : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ˢ lam ⟩
           × ((z : V ℓ) → ⟨ z ∈ˢ fst (AllCodes A₀) ⟩ → ⟨ z ∈ˢ Lset δ ⟩))
       → ⟨ fst w ∈ˢ Lset lam ⟩
    go (δ , δ∈lam , All⊆Lδ) =
      Lset-in lam δ (fst w) δ∈lam
        (w∈𝒟ₒδ (λ z z∈w → All⊆Lδ z (w⊆All z z∈w)))
      where
      -- THE TERM THAT CANNOT BE WRITTEN.  From "every member of w lies
      -- in Lset δ" the proof needs "w is a definable subset of Lset δ".
      -- The premises give only the first.  The natural attempt below
      -- exhibits w as defSet (Lset δ) ⊤̇, which is Lset δ itself, and
      -- Agda rejects the equation.
      w∈𝒟ₒδ : ((z : V ℓ) → ⟨ z ∈ˢ fst w ⟩ → ⟨ z ∈ˢ Lset δ ⟩)
            → ⟨ fst w ∈ˢ 𝒟ₒ (Lset δ) ⟩
      w∈𝒟ₒδ h = 𝒟ₒ-intro (Lset δ) (fst w) ∣ ⊤̇ , refl ∣₁

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.665] W3.  Can the three clauses' frames be stated in one module.
-- Types only.  No assembly.  src/ only: no predecessor probe is imported.
-- Typechecked ALONE first.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-665.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀ )
open import FOL.Manipulation.Relabelling using ( mapFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.BoundedSubset {ℓ} lem
  using ( module HullStage; module HullExt; module CollapseIso )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Vec using ( _∷_; [] )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module SV = hPropStructure 𝒮ᵥ

import FOL.Semantics
import Cubical.Data.Empty as Empty
module SemVᵃ = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemVᵃ using ( _^_ )
module AtP = SemVᵃ.At (⊥* {ℓ-suc ℓ}) (λ b → Empty.rec* b)

_⊨ₚ_ : {n : ℕ} → S ^ n → Formula (⊥* {ℓ-suc ℓ}) n → hProp (ℓ-suc ℓ)
_⊨ₚ_ = AtP._⊨_

module Frame (lam : SV.S) (ordλ : IsOrd lam)
             (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (X : SV.S)
             (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module T = HS.H.T
  module HE = HullExt lam ordλ X X⊆Lλ ∅∈λ
  module CIso = CollapseIso HS.M HE.hullExt
  module A = HS.ASt.AtM HS.M HS.H.Hull⊆L

  -- [LJ-1.642] Probe642.agda:125-131, the ruled index.
  ClauseIAtOrd : Type (ℓ-suc ℓ)
  ClauseIAtOrd =
    (c : T.Code) → IsOrd (fst (T.val c))
    → Σ[ φ ∈ Formula T.Code 1 ]
        ( ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (a ∷ []) T.⊨c φ ⟩ ∥₁
        × ((a : HS.ASt.SL) → ⟨ (a ∷ []) T.⊨c φ ⟩
           → fst a ≡ Lset (fst (T.val c))) )

  -- [LJ-1.650] Probe650.agda:88-92.
  CodedCover : Type (ℓ-suc ℓ)
  CodedCover = (c : T.Code)
             → Σ[ d ∈ T.Code ]
                 ( IsOrd (fst (T.val d))
                 × ⟨ fst (T.val c) ∈ˢ Lset (fst (T.val d)) ⟩ )

  -- [LJ-1.650] Probe650.agda:322-328.
  LevelFormula : Type (ℓ-suc ℓ)
  LevelFormula =
    Σ[ lv ∈ Formula T.Code 2 ]
      ( ((v γ : HS.ASt.SL) → ⟨ (v ∷ γ ∷ []) T.⊨c lv ⟩ → fst v ≡ Lset (fst γ))
      × ((γ : HS.ASt.SL) → IsOrd (fst γ)
         → ∥ Σ[ v ∈ HS.ASt.SL ]
              ((fst v ≡ Lset (fst γ)) × ⟨ (v ∷ γ ∷ []) T.⊨c lv ⟩) ∥₁) )

  -- [LJ-1.641] Probe641.agda:69-73, closed by [LJ-1.652] Probe652.agda:305.
  Commute : Type (ℓ-suc ℓ)
  Commute =
    (δ : SV.S) (δ∈M : ⟨ δ ∈ˢ HS.M ⟩) → IsOrd (HS.C.π δ)
    → (Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩)
    → HS.C.π (Lset δ) ≡ Lset (HS.C.π δ)

  -- [LJ-1.578] Probe578.agda:234-240, collapse index, NOT the ruling.
  DefinesLevel : Type (ℓ-suc ℓ)
  DefinesLevel =
    (c : T.Code) → IsOrd (HS.C.π (fst (T.val c)))
    → Σ[ φ ∈ Formula T.Code 1 ]
        ( ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (a ∷ []) T.⊨c φ ⟩ ∥₁
        × ((a : HS.ASt.SL) → ⟨ (a ∷ []) T.⊨c φ ⟩
           → fst a ≡ Lset (fst (T.val c))) )

  -- [LJ-1.578] Probe578.agda:244-251.
  DefinesCover : Type (ℓ-suc ℓ)
  DefinesCover =
    (c : T.Code)
    → Σ[ φ ∈ Formula T.Code 1 ]
        ( ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (a ∷ []) T.⊨c φ ⟩ ∥₁
        × ((a : HS.ASt.SL) → ⟨ (a ∷ []) T.⊨c φ ⟩
           → IsOrd (HS.C.π (fst a))
           × ⟨ fst (T.val c) ∈ˢ Lset (fst a) ⟩) )

  -- [LJ-1.578] Probe578.agda:503-510.
  DefinesLevelAcross : Type (ℓ-suc ℓ)
  DefinesLevelAcross =
    (δ : SV.S) (δ∈M : ⟨ δ ∈ˢ HS.M ⟩) → IsOrd (HS.C.π δ)
    → (Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩)
    → Σ[ φ ∈ Formula CIso.I.SM 1 ]
        ( ⟨ ((Lset δ , Lδ∈M) ∷ []) CIso.I.⊨ᵐ φ ⟩
        × ((b : CIso.I.SPM) → ⟨ (b ∷ []) CIso.I.⊨ᵖᵐ mapFo CIso.I.g φ ⟩
           → fst b ≡ Lset (HS.C.π δ)) )

  -- THE TWO TRIPLES, STATED TOGETHER.  That is the W3 question.
  Certificate578 : Type (ℓ-suc ℓ)
  Certificate578 = DefinesLevel × DefinesCover × DefinesLevelAcross

  CertificateNow : Type (ℓ-suc ℓ)
  CertificateNow = ClauseIAtOrd × CodedCover × Commute

  -- THE INDEX BRIDGE [LJ-1.598] named and [LJ-1.642] deleted.
  PreimageOrd : Type (ℓ-suc ℓ)
  PreimageOrd =
    (c : T.Code) → IsOrd (HS.C.π (fst (T.val c))) → IsOrd (fst (T.val c))

  -- And the one-liner that would restore 578's clause (i) from the ruling.
  to-578-i : PreimageOrd → ClauseIAtOrd → DefinesLevel
  to-578-i po cio c oπ = cio c (po c oπ)

-- [LJ-1.652] Probe652.agda:75-80, ambient, hull-free.
Matrix₂ : (SV.S → SV.S) → Type (ℓ-suc ℓ)
Matrix₂ F =
  Σ[ φ ∈ Formula (⊥* {ℓ-suc ℓ}) 2 ]
    ( Δ₀ φ
    × ((a p : SV.S) → ⟨ (a ∷ p ∷ []) ⊨ₚ φ ⟩ → a ≡ F p)
    × ((a p : SV.S) → a ≡ F p → ⟨ (a ∷ p ∷ []) ⊨ₚ φ ⟩) )

-- THE REMAINING DEBT, AS ONE TYPE.  Open hypotheses in, this week's
-- triple out.  Elementary lives one universe up (src/L/Hull.lagda.md:174).
Remainder : Type (ℓ-suc (ℓ-suc ℓ))
Remainder =
    (lam : SV.S) (ordλ : IsOrd lam)
    (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
    (X : SV.S)
    (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
    (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  → Frame.LevelFormula lam ordλ succλ X X⊆Lλ ∅∈λ
  → Frame.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ
  → Matrix₂ Lset
  → Frame.CertificateNow lam ordλ succλ X X⊆Lλ ∅∈λ

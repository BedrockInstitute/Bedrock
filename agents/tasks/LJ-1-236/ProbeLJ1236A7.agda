{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.236] probe A7.  The internal GCH statement, written in the shape
-- of the delivered ChoiceStatement (src/L/Choice/Transversal.lagda.md:372-384).
--
-- Two checks (the brief):
--   1.  It elaborates, and names only S, ∈ˢ, internal IsCardinal and the
--       square-law shape.
--   2.  A5's `sq` and A6's `absorbs` have conclusions that match its
--       hypotheses.  That check is the audit, done by reading the types
--       below against A5 (the square-law chain) and A6 (the successor
--       absorption), not by importing them.
--
--   S1  InjCode:  "F codes an injection from a into b" — A2's svAt /
--       domAt / injAt plus the value-in-b clause, at the L carrier.
--   S2  IsCardinalL:  the internal cardinal (A4).  Internal coding, not
--       the ambient IsCardinal (src/L/BoundedSubset.lagda.md:1046-1047),
--       because [LJ-1.91] measured they are different objects.
--   S3  SqShape:  A5's chain-theorem conclusion type (the square law
--       ⟪α⟫×⟪α⟫ ↪ ⟪α⟫, uniformly over infinite L-ordinals).
--   S4  AbsorbsShape:  A6's conclusion type (the successor absorption
--       ⟪sucV γ⟫ ↪ ⟪γ⟫).
--   S5  GCHStatement:  the statement, SqShape and AbsorbsShape as
--       hypotheses, internal IsCardinal as the quantifier, and the
--       square-law-shaped injection ⟪𝒫(κ)⟫ ↪ ⟪δ⟫ as the conclusion.
--
-- Probe only.  Nothing lands in src/.  ONE agda process under
-- GHCRTS="-A64m -I0 -M8g"; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-236.ProbeLJ1236A7 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _≐_; _⇒̇_; ∀̇_ )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( ω-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Coding.Model {ℓ}
  using ( appAt; svAt; domAt )
open import Cubical.Data.FinData.Base using ( Fin )
open import V.Presentation {ℓ} using ( member; ↪-inj )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV; #_ )

import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

module ModelL = FOL.ZFModel 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- The injection type, exactly as the ambient chain carries it.
_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

-- ---------------------------------------------------------------------
-- S0.  injAt, copied from [LJ-1.229] ProbeLJ1229A S1 (A2's injectivity
-- of a graph).  Not yet a master; A3's probe copies it the same way.
-- ---------------------------------------------------------------------

injAt : ∀ {n} → Fin n → Formula S n
injAt f = ∀̇ (∀̇ (∀̇ (
      appAt (suc (suc (suc f))) (suc zero) (suc (suc zero))
  ⇒̇ (appAt (suc (suc (suc f))) zero (suc (suc zero))
  ⇒̇ (var (suc zero) ≐ var zero)))))

-- ---------------------------------------------------------------------
-- S1.  "F codes an injection from a into b."
-- A2's three conjuncts (single-valued, total on a, injective) plus the
-- value-in-b clause, the four pieces A2's Small readback consumes.
-- ---------------------------------------------------------------------

InjCode : S → S → S → Type (ℓ-suc ℓ)
InjCode F a b =
    ⟨ (F ∷ a ∷ []) ⊨ svAt zero ⟩
  × ⟨ (F ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩
  × ⟨ (F ∷ a ∷ []) ⊨ injAt zero ⟩
  × ((x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst b ⟩)

-- ---------------------------------------------------------------------
-- S2.  The internal cardinal (A4).  No smaller L-ordinal admits an
-- L-element coding an injection from κ.
-- ---------------------------------------------------------------------

IsCardinalL : S → Type (ℓ-suc ℓ)
IsCardinalL κ =
  (δ : S) → ⟨ fst δ ∈ fst κ ⟩
          → (∥ Σ[ F ∈ S ] InjCode F κ δ ∥₁ → Empty.⊥)

-- ---------------------------------------------------------------------
-- S3.  A5's conclusion type: the square law, uniformly over infinite
-- L-ordinals ([LJ-1.156] ProbeLJ1156A Part 6).
-- ---------------------------------------------------------------------

SqShape : Type (ℓ-suc ℓ)
SqShape =
  (α : S) → IsOrd (fst α) → (⟨ fst α ∈ˢ ω ⟩ → Empty.⊥)
          → ⟪ fst α ⟫ × ⟪ fst α ⟫ ↪ ⟪ fst α ⟫

-- ---------------------------------------------------------------------
-- S4.  A6's conclusion type: the successor absorption, uniformly over
-- infinite L-ordinals ([LJ-1.217] ShiftAbs / Shiftω built into L, read
-- back as the ambient injection ⟪sucV γ⟫ ↪ ⟪γ⟫).
-- ---------------------------------------------------------------------

AbsorbsShape : Type (ℓ-suc ℓ)
AbsorbsShape =
  (γ : S) → IsOrd (fst γ) → (⟨ fst γ ∈ˢ ω ⟩ → Empty.⊥)
          → ((k : ℕ) → ⟨ # k ∈ fst γ ⟩)
          → ⟪ sucV (fst γ) ⟫ ↪ ⟪ fst γ ⟫

-- ---------------------------------------------------------------------
-- S5.  THE STATEMENT.  In ChoiceStatement's shape: a Type over an
-- isZFModel, quantifying over S with ∈ˢ, naming internal IsCardinal and
-- the square-law-shaped injection.  sq and absorbs are the two
-- hypotheses A5 and A6 discharge.  The conclusion is the GCH bound
-- 𝒫(κ) ↪ δ at the SUCCESSOR cardinal δ: δ is the least cardinal above κ,
-- and the powerset injects into δ.
-- ---------------------------------------------------------------------

-- δ is the successor cardinal of κ: a cardinal above κ, and every
-- cardinal above κ admits δ ↪ λ (δ is the least such).
SuccCardL : S → S → Type (ℓ-suc ℓ)
SuccCardL δ κ =
    IsCardinalL δ
  × ⟨ fst κ ∈ fst δ ⟩
  × ((c : S) → IsCardinalL c → ⟨ fst κ ∈ fst c ⟩ → (⟪ fst δ ⟫ ↪ ⟪ fst c ⟫))

GCHStatement : ModelL.isZFModel → Type (ℓ-suc ℓ)
GCHStatement zf =
  (sq : SqShape)
  → (absorbs : AbsorbsShape)
  → (κ : S)
  → IsCardinalL κ
  → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → ∥ Σ[ δ ∈ S ]
       ( SuccCardL δ κ
       × (⟪ fst (𝒫 κ) ⟫ ↪ ⟪ fst δ ⟫) ) ∥₁
  where open ModelL.isZFModel zf using ( 𝒫 )

-- ---------------------------------------------------------------------
-- The C-38 guard: ω is an L-ordinal, so the statement's quantifiers are
-- inhabited at a real site (the pieces elaborate; IsCardinalL at ω is
-- A4's deliverable, not asserted here).
-- ---------------------------------------------------------------------

module Guard where

  hω : ⟨ isL ω ⟩
  hω = Lset→isL (sucV ω) (suc-ord ω-ord) ω (ord∈Lset-suc ω ω-ord)

  aω : S
  aω = ω , hω

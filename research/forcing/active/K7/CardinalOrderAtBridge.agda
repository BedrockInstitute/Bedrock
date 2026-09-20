{-# OPTIONS --cubical --safe --guardedness #-}

-- K7 Track B, seam probe. Architecture 4.0 requires one alias per consumed
-- export whose TYPE is the consumer's parameter type character for character
-- and whose BODY is the producer's export, plus refl checks; and device D-II
-- of Part 7 requires every positive check to run at the APPLICATION and never
-- at the definition. Both are done here.
--
-- WHAT THIS FILE CHECKS, IN ORDER.
--
--   1. The ground side. K7.CardinalOrder's re-exports ARE CardinalBridge's,
--      by refl, and Track A's subsetΔ IS CardinalBridge's isSubset, by refl.
--   2. Δ₀-IsOrdinalφ at the application, by checkΔ₀ … tt, and the reading
--      theorems of the ordinal predicate and of the new surjection formula.
--   3. Trap T11. The whole of Part 3 is instantiated at a SECOND structure,
--      K6's extension structure, built by K6/Ordinals' own flat template and
--      checked byte for byte against it. `paths` is NOT available there and
--      is not needed there.
--   4. The payoff. K6/Ordinals.agda:174-180 takes chk-ordinal as a HYPOTHESIS
--      with a comment asserting both halves of its proof. Both halves are now
--      theorems (Δ₀-IsOrdinalφ and ordinalφ-mapFo), and K6's module Ordinals
--      is applied for real with the discharged hypothesis in its slot.
--
-- Per-file count for T11, written down in advance as the brief requires:
-- every ground occurrence is qualified CB. or CO. and every extension
-- occurrence is qualified CBᴱ. or COᴱ., and no name in this file is
-- unqualified vocabulary. The expectation is that neither qualifier appears
-- in the other side's block.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K7.CardinalOrderAtBridge
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext   : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import FOL.Manipulation.ConstantMapping using ( mapFo )
open import Base.Classical using ( LEM )
open import FOL.LevyHierarchy using ( Δ₀; checkΔ₀ )
open import Cubical.Data.Unit using ( tt )

import CardinalBridge
import CodedVocabulary
import K7.CardinalOrder
import K6.Ordinals

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using () renaming ( _⊨_ to _⊨ᴳ_ )

module OP = OrdinaryProfile 𝒮
module CB = CardinalBridge 𝒮
module CV = CodedVocabulary 𝒮
module CO = K7.CardinalOrder 𝒮

open OP.PathRealization paths using ( subst-member; subst-base )

--------------------------------------------------------------------------------
-- 1. THE GROUND SIDE. THE ALIASES, AND THE PARAMETERS FILLED FOR REAL
--------------------------------------------------------------------------------

-- The two congruences, filled from `paths` by OrdinaryProfile's own lemmas at
-- OrdinaryProfile.agda:188-192. This is the only use of `paths` in the whole
-- track, and section 3 below shows the extension does not need it.

module OG = CO.Order ext subst-member subst-base

-- The aliases. Each type is CardinalBridge's export written out, each body is
-- K7.CardinalOrder's re-export, and each check is refl.

isSubset-alias : S → S → Ω
isSubset-alias = CO.isSubset

isSubset-agrees : isSubset-alias ≡ CB.isSubset
isSubset-agrees = refl

isKPair-alias : S → S → S → Ω
isKPair-alias = CO.isKPair

isKPair-agrees : isKPair-alias ≡ CB.isKPair
isKPair-agrees = refl

isInjection-alias : S → S → S → Ω
isInjection-alias = CO.isInjection

isInjection-agrees : isInjection-alias ≡ CB.isInjection
isInjection-agrees = refl

injectable-alias : S → S → Ω
injectable-alias = CO.injectable

injectable-agrees : injectable-alias ≡ CB.injectable
injectable-agrees = refl

isOrdinal-alias : S → Ω
isOrdinal-alias = CO.isOrdinal

isOrdinal-agrees : isOrdinal-alias ≡ CB.isOrdinal
isOrdinal-agrees = refl

-- And the identification the architecture's Track A brief needs: the subset
-- predicate Track A takes from CodedVocabulary (CodedVocabulary.agda:202-203)
-- and the one CardinalBridge defines (CardinalBridge.agda:72-73) are the same
-- term, so injectable-mono-dom applies to a subsetΔ hypothesis unchanged and
-- Track A does not need a second monotonicity lemma.

subsetΔ-agrees : CB.isSubset ≡ CV.subsetΔ
subsetΔ-agrees = refl

--------------------------------------------------------------------------------
-- 2. THE CERTIFICATES AND THE READINGS, AT THE APPLICATION
--------------------------------------------------------------------------------

Δ₀-ordinal-at : Δ₀ CB.IsOrdinalφ
Δ₀-ordinal-at = checkΔ₀ CB.IsOrdinalφ tt

Δ₀-ordinal-agrees : Δ₀-ordinal-at ≡ CO.Δ₀-IsOrdinalφ
Δ₀-ordinal-agrees = refl

-- The reading theorems. The ordinal one is CardinalBridge's own refl and is
-- restated at the application because that is what the respelling break
-- destroys. The surjection one is this track's, and it is not refl: it runs
-- through three renamings.

ordinal-reading : (α : S) → ((α ∷ []) ⊨ᴳ CB.IsOrdinalφ) ≡ (CB.isOrdinal α)
ordinal-reading = CB.IsOrdinal-bridge

surjection-reading : (f a b : S)
  → ((f ∷ a ∷ b ∷ []) ⊨ᴳ CO.IsSurjectionφ) ≡ (CO.isSurjection f a b)
surjection-reading = CO.IsSurjection-bridge

surjectable-reading : (a b : S)
  → ((a ∷ b ∷ []) ⊨ᴳ CO.Surjectableφ) ≡ (CO.surjectable a b)
surjectable-reading = CO.Surjectable-bridge

-- The clause decomposition, at the application, and it is the check that
-- would catch a surjection formula whose fourth conjunct had drifted into
-- being injectivity.

injection-clauses-at : (f a b : S)
  → CB.isInjection f a b
    ≡ ((CB.isFunction f)
       ⊓ ((OG.DomClause f a) ⊓ ((OG.RanClause f b) ⊓ (OG.InjClause f))))
injection-clauses-at = OG.injection-clauses

--------------------------------------------------------------------------------
-- 3. TRAP T11. THE SAME THEOREMS AT K6's EXTENSION STRUCTURE
--------------------------------------------------------------------------------

-- The extension side is the flat spine of K6/Ordinals.agda:105-152, applied
-- for real rather than copied, so that a drift between this file's structure
-- and K6's is a type error and not a reading exercise.

module Extension (IsNm : S → Ω) (_≈[G]_ _∈[G]_ : S → S → Ω) where

  module KO = K6.Ordinals 𝒮
  module KN = KO.Names IsNm
  module KG = KN.AtG _≈[G]_ _∈[G]_

  open KG using ( 𝒮ᴱ; Agree ) renaming ( _⊨_ to _⊨ᴱ_ )

  module COᴱ = K7.CardinalOrder 𝒮ᴱ
  module CBᴱ = CardinalBridge 𝒮ᴱ
  module HE  = hPropStructure 𝒮ᴱ
  module OPᴱ = OrdinaryProfile 𝒮ᴱ

  -- The two refl checks architecture 4.0 demands, in K6's own names.

  carrier-agrees : HE.S ≡ KN.Nm
  carrier-agrees = refl

  ordinalφ-agrees : COᴱ.IsOrdinalφ ≡ KG.ordinalφ
  ordinalφ-agrees = refl

  bridge-agrees : CBᴱ.isOrdinal ≡ COᴱ.isOrdinal
  bridge-agrees = refl

  ----------------------------------------------------------------------------
  -- 3.1 The congruences at the extension, with NO `paths`
  ----------------------------------------------------------------------------

  -- This module is the evidence for the track's central structural finding.
  -- `paths` is FALSE at 𝒮ᴱ, because K6/Ordinals.agda:141 reads ≈ˢ off the
  -- value relation on names and KN.Nm is not a quotient. Everything Part 3
  -- proves is nevertheless available here, because Part 3 asks for the two
  -- congruences and not for `paths`, and both are sat-cong at the atomic
  -- formula var zero ∈̇ var (suc zero).

  module AtExtension
    (extᴱ : OPᴱ.Extensionality)
    -- K5/Structures.agda:400-402, in the shape K6/Ordinals.agda:170-172 takes.
    (sat-cong : ∀ {k} (ψ : Formula KN.Nm k) (ν μ : Vec KN.Nm k) → Agree ν μ
              → (ν ⊨ᴱ ψ) ≡ (μ ⊨ᴱ ψ))
    where

    memφ : Formula KN.Nm 2
    memφ = var zero ∈̇ var (suc zero)

    ≈ᴱ-refl : (σ : KN.Nm) → ⟨ HE._≈ˢ_ σ σ ⟩
    ≈ᴱ-refl = OPᴱ.≈ˢ-refl extᴱ

    mem-congˡᴱ : (σ τ ρ : KN.Nm) → ⟨ HE._≈ˢ_ σ τ ⟩
               → (HE._∈ˢ_ σ ρ) ≡ (HE._∈ˢ_ τ ρ)
    mem-congˡᴱ σ τ ρ h =
      sat-cong memφ (σ ∷ ρ ∷ []) (τ ∷ ρ ∷ [])
        (λ { zero → h ; (suc zero) → ≈ᴱ-refl ρ })

    mem-congʳᴱ : (σ τ ρ : KN.Nm) → ⟨ HE._≈ˢ_ τ ρ ⟩
               → (HE._∈ˢ_ σ τ) ≡ (HE._∈ˢ_ σ ρ)
    mem-congʳᴱ σ τ ρ h =
      sat-cong memφ (σ ∷ τ ∷ []) (σ ∷ ρ ∷ [])
        (λ { zero → ≈ᴱ-refl σ ; (suc zero) → h })

    module OE = COᴱ.Order extᴱ mem-congˡᴱ mem-congʳᴱ

    -- The ascriptions. Each type is the theorem's statement at the extension,
    -- written out, and each body is the ground-side proof instantiated there.
    -- An ascription that needed `paths` would not elaborate.

    ord-compareᴱ : OPᴱ.FoundationInduction → OPᴱ.Separation → LEM ℓ
                 → (α δ : KN.Nm)
                 → ⟨ COᴱ.isOrdinal α ⟩ → ⟨ COᴱ.isOrdinal δ ⟩
                 → ⟨ (HE._∈ˢ_ α δ) ⊔ ((HE._≈ˢ_ α δ) ⊔ (HE._∈ˢ_ δ α)) ⟩
    ord-compareᴱ = OE.ord-compare

    injectable-transᴱ : OPᴱ.Separation → OPᴱ.Collection → OPᴱ.Pairing
                      → (a b d : KN.Nm)
                      → ⟨ COᴱ.injectable a b ⟩ → ⟨ COᴱ.injectable b d ⟩
                      → ⟨ COᴱ.injectable a d ⟩
    injectable-transᴱ = OE.injectable-trans

    injectable-inclᴱ : OPᴱ.Separation → OPᴱ.Collection → OPᴱ.Pairing
                     → (a b : KN.Nm) → ⟨ COᴱ.isSubset a b ⟩
                     → ⟨ COᴱ.injectable a b ⟩
    injectable-inclᴱ = OE.injectable-incl

  ----------------------------------------------------------------------------
  -- 3.2 K6's chk-ordinal, discharged
  ----------------------------------------------------------------------------

  -- The two halves K6/Ordinals.agda:174-180 asserts in prose and does not
  -- build. groundSat is taken flat in K5/Structures.agda:670-671's exact
  -- shape, where it sits under ⟨ positive G ⟩; the Δ₀ slot it demands is what
  -- Δ₀-IsOrdinalφ fills, and the mapFo step is ordinalφ-mapFo.

  module Absolute
    (groundName : S → KN.Nm)
    (chkEnv     : ∀ {k} → Vec S k → Vec KN.Nm k)
    (chkEnv-one : (u : S) → chkEnv (u ∷ []) ≡ (groundName u ∷ []))
    (groundSat  : ∀ {k} (φ : Formula S k) → Δ₀ φ → (γ : Vec S k)
                → (chkEnv γ ⊨ᴱ mapFo groundName φ) ≡ (γ ⊨ᴳ φ))
    where

    chk-ordinal : (a : S)
                → ((groundName a ∷ []) ⊨ᴱ KG.ordinalφ)
                  ≡ ((a ∷ []) ⊨ᴳ CB.IsOrdinalφ)
    chk-ordinal a =
        cong (λ ν → ν ⊨ᴱ KG.ordinalφ) (sym (chkEnv-one a))
      ∙ cong (λ ψ → chkEnv (a ∷ []) ⊨ᴱ ψ)
          (sym (CO.Relabel.ordinalφ-mapFo 𝒮ᴱ groundName))
      ∙ groundSat CB.IsOrdinalφ CO.Δ₀-IsOrdinalφ (a ∷ [])

    -- Device D-II. The check runs at K6's own module application, so the
    -- statement "chk-ordinal is discharged" cannot be true of a lookalike.

    module K6Applied
      (sat-cong : ∀ {k} (ψ : Formula KN.Nm k) (ν μ : Vec KN.Nm k) → Agree ν μ
                → (ν ⊨ᴱ ψ) ≡ (μ ⊨ᴱ ψ))
      where

      module Discharged = KG.Ordinals sat-cong groundName chk-ordinal

      -- K6's proved half now stands with no hypothesis of its own left open
      -- other than sat-cong and groundSat.

      reflect-ordinal : (σ : KN.Nm) (a : S)
                      → ⟨ (fst σ) ≈[G] (fst (groundName a)) ⟩
                      → ⟨ (σ ∷ []) ⊨ᴱ KG.ordinalφ ⟩ → ⟨ CB.isOrdinal a ⟩
      reflect-ordinal = Discharged.reflect-ordinal

{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track A, seam probe. No mathematics.
--
-- Every parameter of K6.NameBuild.Calculus and K6.NameValid.Valid is written
-- out as a type in those files, and every one of them is meant to be a K3
-- export character for character. This file is the machine check of that
-- claim: it applies both modules at the real producers, so a drift in any of
-- twenty-eight parameter types fails HERE, in fifteen lines, rather than in a
-- consuming track's proof. K5/ClausesAtFrame.agda is the shape being copied.
--
-- The one place the flat form differs from the producer is graph→image, whose
-- third to fifth arguments are the three FIELDS of NameImage.DefinableGraphOn
-- rather than the record. Records are generative (rule 9) and K6 must not
-- re-declare one that NameImage owns; the lambda below rebuilds it at the
-- seam, which is the only place the record is mentioned in this track.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import NameSupport
import NameSpace
import NameImage
import GroundDescription
import K6.NameBuild
import K6.NameValid

module K6.NameBuildAtGround {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
open import OrdinaryProfile 𝒮 using ( Separation; Collection; PowerSet )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module NK = NameKernel 𝒮
module NS = NameSupport 𝒮
module NP = NameSpace 𝒮

-- The weight carrier of the poset side is the forcing notion's carrier, which
-- is why K6/NameValid.agda states name-adequate at (t ∷ carrierᶠ ∷ []): the
-- P side of K5/Structures.agda:777-784 instantiates K3's W at carrierᶠ.

module Seam (𝔉 : NK.Families) (acc∈ : NK.Accessibility) (carrierᶠ : S) where

  open NK.Families 𝔉 using ( sets; hasCollect )
  open NK.Sets sets using ( core; hasUnion; hasSeparation )
  open NK.Core core using ( extensional; ≈ˢ-paths )

  module GD = GroundDescription 𝒮 extensional ≈ˢ-paths
  module NI = NameImage 𝒮 extensional ≈ˢ-paths
  module PI = NP.Instantiate 𝔉 acc∈ carrierᶠ
  module K  = PI.K
  module BG = PI.BG

  -- The flat graph→image. Everything else below is a bare name.

  imageOfGraph : Collection → Separation → (f : S → S) (a : S)
               → (graph : Formula S 2)
               → ((x : S) → ⟨ x ∈ˢ a ⟩ → ⟨ (f x ∷ x ∷ []) ⊨ graph ⟩)
               → ((x : S) → ⟨ x ∈ˢ a ⟩ → (y : S)
                  → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩ → y ≡ f x)
               → Σ[ T ∈ S ] ((z : S) → (z ∈ˢ T)
                   ≡ ⋁ S (λ x → (x ∈ˢ a) ⊓ (z ≈ˢ f x)))
  imageOfGraph coll sep f a g d o =
    NI.graph→image coll sep f a
      (record { graph = g ; defines = d ; only = o })

  -- THE SEAM. Twelve slots, then fifteen.

  module Build = K6.NameBuild.Calculus 𝒮
    ≈ˢ-paths GD.ext-path carrierᶠ
    K.entry K.entry-isKPair PI.CR.kpair-unique
    NI.colAt NI.colAt-reading
    GD.separateOf GD.separateOf-spec
    imageOfGraph
    BG.⋃ᴳ BG.⋃ᴳ-spec

  module Valid = K6.NameValid.Valid 𝒮
    carrierᶠ K.entry K.entry-inj K.Child (λ x n e → e)
    K.IsName K.name-intro
    GD.separateOf GD.separateOf-spec
    ≈ˢ-paths Build.mk Build.mk-bound Build.entryBound Build.entryBound-out
    BG.support PI.nameBound PI.nameBound-contains
    (NP.nameAtˢ zero (suc zero)) PI.name-adequate

  -- The refl alias the architecture asks for: Track A's spread specification
  -- IS NameImage's image class, not a restatement of it.

  imageClass-check : (f : S → S) (a z : S)
                   → NI.ImageClass f a z ≡ ⋁ S (λ x → (x ∈ˢ a) ⊓ (z ≈ˢ f x))
  imageClass-check f a z = refl

  spread-is-image : (coll : Collection) (sep : Separation) (x e : S)
                  → (e ∈ˢ Build.spread coll sep x)
                  ≡ NI.ImageClass (K.entry x) carrierᶠ e
  spread-is-image = Build.spread-spec

  -- And the two certificates, asked for at variables by name, which is what
  -- catches a drift that a definitional alias would absorb.

  name-check : (sep : Separation) (bound : S) (θ : Formula S 1)
    → ((e : S) → ⟨ e ∈ˢ Build.mk sep bound θ ⟩
       → ∥ Σ[ x ∈ S ] Σ[ p ∈ S ]
             ((e ≡ K.entry x p) × (⟨ p ∈ˢ carrierᶠ ⟩ × ⟨ K.IsName x ⟩)) ∥₁)
    → ⟨ K.IsName (Build.mk sep bound θ) ⟩
  name-check = Valid.mk-name

  candidates-check : (sep : Separation) (pow : PowerSet) (σ χ : S)
                   → ⟨ K.IsName χ ⟩
                   → ((x : S) → K.Child x χ → ⟨ x ∈ˢ BG.support σ ⟩)
                   → ⟨ χ ∈ˢ Valid.candidates sep pow σ ⟩
  candidates-check = Valid.candidates-contains

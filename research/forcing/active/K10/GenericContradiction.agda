{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CardinalBridge

module K10.GenericContradiction
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  (hw : ⟨ CardinalBridge.isOmega 𝒮 w ⟩)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Data.Empty as Empty
import CHSentence
import FOL.Semantics
import K9.NameGround
import K9.RealValues
import K9.Theorem
import K10.CheckedOmega
import K10.CheckedInjection
import K7.CardinalOrder
import K10.CardinalContradiction
import K10.NegatedSentences

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
module Ground = K9.NameGround 𝒮 families accessible images pow κ w
module Reals = K9.RealValues 𝒮 families accessible images pow find κ w lem hw
module Injection = K9.Theorem 𝒮 families accessible images pow find κ w lem hw
module Omega = K10.CheckedOmega 𝒮 families accessible images pow κ w hw
module Checked = K10.CheckedInjection 𝒮 families accessible images pow κ w

module AtGeneric
  (G : Ground.P.Sub)
  (generic : Reals.GB.Completion.isGeneric G)
  where

  module Values = Reals.AtGeneric G generic
  module Family = Injection.AtGeneric G generic
  module Natural = Omega.AtGeneric G Values.positive
  module GroundInjection = Checked.AtGeneric G Values.positive
  module E = Ground.AtGeneric G
  module Copy = E.Copy.WithPos Values.positive
  module CB = CardinalBridge Ground.PS.𝒮ᴾ[ G ]
  module CH = CHSentence Ground.PS.𝒮ᴾ[ G ]
  module Negation = K10.NegatedSentences Ground.PS.𝒮ᴾ[ G ]
  module Contradiction = K10.CardinalContradiction Ground.PS.𝒮ᴾ[ G ]
  module Profile = OrdinaryProfile Ground.PS.𝒮ᴾ[ G ]
  private module Semantics = FOL.Semantics (hPropAlgebra ℓ) Ground.PS.𝒮ᴾ[ G ]
  open Semantics.At Ground.K.Name id using () renaming ( _⊨_ to _⊨ᴱ_ )
  open hPropStructure Ground.PS.𝒮ᴾ[ G ]
    using () renaming ( _≈ˢ_ to _≈ᴱ_; _∈ˢ_ to _∈ᴱ_ )

  checked : S → Ground.K.Name
  checked = E.Copy.groundName

  private
    memL : (x y z : Ground.K.Name) → ⟨ x ≈ᴱ y ⟩
      → (x ∈ᴱ z) ≡ (y ∈ᴱ z)
    memL x y z e = ⇔toPath (E.E.∈-congˡ e) (E.E.∈-congˡ (E.E.≈-sym e))

    memR : (x y z : Ground.K.Name) → ⟨ y ≈ᴱ z ⟩
      → (x ∈ᴱ y) ≡ (x ∈ᴱ z)
    memR x y z e = ⇔toPath (E.E.∈-congʳ e) (E.E.∈-congʳ (E.E.≈-sym e))

    module Order = K7.CardinalOrder.Order Ground.PS.𝒮ᴾ[ G ]
      (Ground.PS.P.Ext.extensional G) memL memR

  -- Preservation is still an explicit boundary here. The injection and
  -- omega facts, in contrast, are supplied by the actual K9 and K10 proofs.
  module AtPreservedCardinals
    (sep : Profile.Separation) (coll : Profile.Collection)
    (pair : Profile.Pairing) (power : Profile.PowerSet)
    (foundation : Profile.FoundationInduction)
    (δ : S) (hwδ : ⟨ w ∈ˢ δ ⟩) (hδκ : ⟨ δ ∈ˢ κ ⟩)
    (members-countable : (y : S) → ⟨ y ∈ˢ δ ⟩
      → ⟨ CardinalBridge.injectable 𝒮 y w ⟩)
    (cardinalδ : ⟨ CB.isCardinal (checked δ) ⟩)
    (cardinal : ⟨ CB.isCardinal (checked κ) ⟩)
    where

    private
      copied-wδ : ⟨ checked w ∈ᴱ checked δ ⟩
      copied-wδ = subst ⟨_⟩ (sym (Copy.check-faithful w δ)) hwδ

      copied-δκ : ⟨ checked δ ∈ᴱ checked κ ⟩
      copied-δκ = subst ⟨_⟩ (sym (Copy.check-faithful δ κ)) hδκ

    below-successor-absurd : (μ : Ground.K.Name)
      → ⟨ CB.isCardinal μ ⟩ → ⟨ checked w ∈ᴱ μ ⟩
      → ⟨ μ ∈ᴱ checked δ ⟩ → Empty.⊥
    below-successor-absurd μ hμ hwμ hμδ = PT.rec Empty.isProp⊥
      (λ { (y , hy , e) → hμ .snd (checked w) hwμ
        (Order.injectable-cong (checked y) μ (checked w) (E.E.≈-sym e)
          (GroundInjection.checked-injectable y w (members-countable y hy))) })
      (subst ⟨_⟩ (Copy.check-value δ (fst μ)) hμδ)

    successor-minimal : (μ : Ground.K.Name)
      → ⟨ CB.isCardinal μ ⊓ (checked w ∈ᴱ μ) ⟩
      → ⟨ (checked δ ≈ᴱ μ) ⊔ (checked δ ∈ᴱ μ) ⟩
    successor-minimal μ (hμ , hwμ) = PT.rec PT.squash₁ outer
      (Order.ord-compare foundation sep lem (checked δ) μ (cardinalδ .fst) (hμ .fst))
      where
        inner : ⟨ checked δ ≈ᴱ μ ⟩ ⊎ ⟨ μ ∈ᴱ checked δ ⟩
          → ⟨ (checked δ ≈ᴱ μ) ⊔ (checked δ ∈ᴱ μ) ⟩
        inner (inl e) = PT.∣ inl e ∣₁
        inner (inr h) = Empty.rec (below-successor-absurd μ hμ hwμ h)

        outer : ⟨ checked δ ∈ᴱ μ ⟩
          ⊎ ⟨ (checked δ ≈ᴱ μ) ⊔ (μ ∈ᴱ checked δ) ⟩
          → ⟨ (checked δ ≈ᴱ μ) ⊔ (checked δ ∈ᴱ μ) ⟩
        outer (inl h) = PT.∣ inr h ∣₁
        outer (inr h) = PT.rec PT.squash₁ inner h

    successor : ⟨ CB.isSuccCardinal (checked δ) (checked w) ⟩
    successor = cardinalδ , copied-wδ , successor-minimal

    private

      module AtPower (Y : Ground.K.Name)
        (hY : ⟨ CB.isPowerSet Y (checked w) ⟩)
        (hκY : ⟨ CB.injectable (checked κ) Y ⟩)
        where

        module Kernel = Contradiction.Kernel
          (Ground.PS.P.Ext.extensional G) memL memR sep coll pair
          (checked w) Y (checked δ) (checked κ)
          Natural.checked-omega hY successor cardinal copied-wδ copied-δκ hκY

    noCH : ⟨ CH.chValue ⟩ → Empty.⊥
    noCH h = PT.rec Empty.isProp⊥
      (λ { (Y , hY , hκY) → AtPower.Kernel.noCH Y hY hκY h })
      (Family.internal-cardinal-comparison power)

    noGCHω : ⟨ CH.gchωValue ⟩ → Empty.⊥
    noGCHω h = PT.rec Empty.isProp⊥
      (λ { (Y , hY , hκY) → AtPower.Kernel.noGCHω Y hY hκY h })
      (Family.internal-cardinal-comparison power)

    ¬CH-satisfaction : ⟨ [] ⊨ᴱ CH.¬CHsent ⟩
    ¬CH-satisfaction = subst ⟨_⟩ (sym CH.¬CH-agrees) noCH

    ¬GCHω-satisfaction : ⟨ [] ⊨ᴱ Negation.¬GCHωsent ⟩
    ¬GCHω-satisfaction = Negation.¬GCHω-satisfaction noGCHω

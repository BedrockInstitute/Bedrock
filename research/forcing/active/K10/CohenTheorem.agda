{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CardinalBridge
import K10.GenericContradiction
import K10.CohenZFC
import K9.Theorem
import K10.CheckedOmega

module K10.CohenTheorem
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
import Cubical.Data.Empty as Empty
import FOL.Semantics
import CHSentence
import K9.NameGround
import K10.NegatedSentences

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module Ground = K9.NameGround 𝒮 families accessible images pow κ w
module GC = K10.GenericContradiction 𝒮 families accessible images pow find κ w lem hw
module Inj = K9.Theorem 𝒮 families accessible images pow find κ w lem hw
module Omega = K10.CheckedOmega 𝒮 families accessible images pow κ w hw
module ZFC = K10.CohenZFC 𝒮 families accessible images pow κ w hw

module AtGeneric
  (G : Ground.P.Sub)
  (generic : GC.Reals.GB.Completion.isGeneric G)
  where

  module C = GC.AtGeneric G generic
  module Family = Inj.AtGeneric G generic
  module Natural = Omega.AtGeneric G C.Values.positive
  module ExtZFC = ZFC.AtGeneric G
  module Profile = OrdinaryProfile Family.extension
  private module Semantics = FOL.Semantics (hPropAlgebra ℓ) Family.extension
  open Semantics.At Ground.K.Name id using () renaming ( _⊨_ to _⊨ᴱ_ )
  module CH = CHSentence Family.extension
  module Negation = K10.NegatedSentences Family.extension

  filter : Ground.P.isFilter G
  filter = C.Values.filter

  -- Extensionality, pairing, union, infinity and foundation of M[G] are
  -- filled from the generic filter. Power, Separation, Collection and
  -- Choice remain engine-conditional.

  module WithPreservedCardinals
    (power : Profile.PowerSet)
    (sep : Profile.Separation)
    (coll : Profile.Collection)
    (choice : Profile.ChoiceSet)
    (ω₁ : S) (hwω₁ : ⟨ w ∈ˢ ω₁ ⟩) (hω₁κ : ⟨ ω₁ ∈ˢ κ ⟩)
    (members-countable : (y : S) → ⟨ y ∈ˢ ω₁ ⟩
      → ⟨ CardinalBridge.injectable 𝒮 y w ⟩)
    (cardinalω₁ : ⟨ C.CB.isCardinal (C.checked ω₁) ⟩)
    (cardinal : ⟨ C.CB.isCardinal (C.checked κ) ⟩)
    where

    private
      module As = ExtZFC.Assemble power sep coll choice filter
      open Profile.OrdinaryZFC As.ordinaryZFC using
        ( hasPair ; hasUnion ; hasPower ; hasSeparation ; hasReplacement
        ; foundation ; hasChoice )

      module P = C.AtPreservedCardinals
        hasSeparation hasReplacement hasPair hasPower foundation
        ω₁ hwω₁ hω₁κ members-countable cardinalω₁ cardinal

    extension-ZFC : Profile.OrdinaryZFC
    extension-ZFC = As.ordinaryZFC

    extension-not-CH : ⟨ [] ⊨ᴱ CH.¬CHsent ⟩
    extension-not-CH = P.¬CH-satisfaction

    extension-not-GCHω : ⟨ [] ⊨ᴱ Negation.¬GCHωsent ⟩
    extension-not-GCHω = P.¬GCHω-satisfaction

    many-reals : ⟨ ⋁ Ground.K.Name (λ Y → C.CB.isPowerSet Y (Inj.checkNm w)
      ⊓ C.CB.isInjection Inj.graph (Inj.checkNm κ) Y) ⟩
    many-reals = Family.internal-injection hasPower

    checked-omega = Natural.checked-omega

    checked-omega1 : ⟨ C.CB.isSuccCardinal (C.checked ω₁) (C.checked w) ⟩
    checked-omega1 = P.successor

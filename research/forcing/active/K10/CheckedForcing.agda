{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile

module K10.CheckedForcing
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
import K5.Frame
import K7.ForcingReflection
import K9.BooleanNameGround
import K9.NameGround

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module Ground = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
  using ( B; translated-check; translated-check-equality
        ; module NG; module IC; module Base; module Atomic; module Reflection; module Translation )
module Names = K9.NameGround 𝒮 families accessible images pow κ w
  using ( module K; module Check; chk-name )
open Ground.NG using ( extensional; ≈ˢ-paths )

module Frame = K5.Frame.Poset 𝒮 Ground.NG.C.carrier Ground.NG.C.order
module Forcing = Frame.Forcing extensional ≈ˢ-paths Ground.B
  Ground.IC.codedLattice Ground.IC.codedComplement Ground.IC.codedComplete
  (Ground.Base.codedBase lem)

module Reflection = K7.ForcingReflection 𝒮 extensional ≈ˢ-paths
  Ground.NG.C.carrier Ground.NG.C.order Ground.B
  Ground.IC.codedLattice Ground.IC.codedComplement Ground.IC.codedComplete
  (Ground.Base.codedBase lem)

-- K9 compares the translated poset checks with the canonical Boolean checks.
-- Transporting its proved reflection along that comparison discharges the
-- generic reflection datum required by the K7 primitive.

translated-check-reflection : (a b : S)
  → Reflection.Check.Reflects
    (Ground.Atomic._≈ᴮ_ (Ground.translated-check a) (Ground.translated-check b))
    (a ≈ˢ b)
translated-check-reflection a b = subst
  (λ v → Reflection.Check.Reflects v (a ≈ˢ b))
  (sym (Ground.translated-check-equality a b))
  (Ground.Reflection.check-reflects-≈ a b)

private
  module Checks = Reflection.AtCheck
    Ground.translated-check Ground.Atomic._≈ᴮ_ translated-check-reflection

-- This applies at every actual Cohen condition. It establishes only checked
-- equality reflection; deriving the forced equality from function and value
-- formulas remains the separate prerequisite for a value antichain.

forced-translated-check-equality : (r : Frame.Cond) (a b : S)
  → ⟨ Forcing._⊩ᴮ_ r
    (Ground.Atomic._≈ᴮ_ (Ground.translated-check a) (Ground.translated-check b)) ⟩
  → ⟨ a ≈ˢ b ⟩
forced-translated-check-equality = Checks.forced-check-equality

checked-name : S → Names.K.Name
checked-name a = Names.Check.chk a , Names.chk-name a

-- ValuesAtTruth.AtCheck uses the translation of the full checked name.
-- This is the actual K9 check, not a separately chosen Boolean check.
checked-name-reflection : (r : Frame.Cond) (a b : S)
  → ⟨ Forcing._⊩ᴮ_ r
    (Ground.Atomic._≈ᴮ_
      (Ground.Translation.trᴮ (fst (checked-name a)))
      (Ground.Translation.trᴮ (fst (checked-name b)))) ⟩
  → ⟨ a ≈ˢ b ⟩
checked-name-reflection = forced-translated-check-equality

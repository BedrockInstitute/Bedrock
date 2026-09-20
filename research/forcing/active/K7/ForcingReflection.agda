{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import K4.Algebra
import K4.CheckValues
import K5.Frame

module K7.ForcingReflection
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (c o B : ZFStructure.S 𝒮)
  (L : K4.Algebra.Lattice 𝒮 B)
  (Cm : K4.Algebra.Complement 𝒮 B L)
  (Kc : K4.Algebra.CodedComplete 𝒮 B L)
  (fb : K5.Frame.Poset.ForcingBase 𝒮 c o B L Cm)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Data.Sum using ( inl; inr )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open K4.Algebra 𝒮 using ( Pt )

module Frame = K5.Frame.Poset 𝒮 c o
module Forcing = Frame.Forcing ext paths B L Cm Kc fb
module Check = K4.CheckValues.Core 𝒮 ext paths B L Cm Kc

-- A condition cannot force the false branch of a reflected Boolean value.
-- This uses the actual sealed K5 forcing relation and its nonzero theorem;
-- no generic filter, truth lemma, or generic-existence principle is needed.

forced-reflection : (r : Frame.Cond) (b : Pt B) (P : Ω)
  → Check.Reflects b P → ⟨ Forcing._⊩ᴮ_ r b ⟩ → ⟨ P ⟩
forced-reflection r b P (inl (_ , h)) _ = h
forced-reflection r b P (inr (e , _)) h = Empty.rec*
  (Forcing.⊩ᴮ-⊥ r (subst (λ u → ⟨ Forcing._⊩ᴮ_ r u ⟩) e h))

-- K4.CheckValues.Classical.check-reflects-≈ supplies this reflection datum.
-- Thus this is the checked-equality step needed after functionality has
-- forced equality of two candidate values at a common refinement. The
-- missing function/formula consequence is not assumed or claimed here.

module AtCheck
  (chk : S → S) (eq : S → S → Pt B)
  (reflects : (a b : S) → Check.Reflects (eq (chk a) (chk b)) (a ≈ˢ b))
  where

  forced-check-equality : (r : Frame.Cond) (a b : S)
    → ⟨ Forcing._⊩ᴮ_ r (eq (chk a) (chk b)) ⟩ → ⟨ a ≈ˢ b ⟩
  forced-check-equality r a b =
    forced-reflection r (eq (chk a) (chk b)) (a ≈ˢ b) (reflects a b)

{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track I, PROBE 0 ITEM 1c. NOT a deliverable. THE ISOLATION RUNG.
--
-- The statement architecture section 6.7 says nobody has measured: the
-- compatibility clause of ForcingBase, whose TYPE nests the sealed meet of
-- K4/InstanceCoded.agda:150 over two applications of K2's embedding. Here the
-- embedding is SEALED as iᴷ in its own block, so the nest is
--
--     sealed-meet (sealed-i p) (sealed-i q)
--
-- and every argument of the nest is neutral. The companion file ProbeI3 is the
-- same statement with the embedding UNSEALED, which is the shape
--
--     sealed-meet (unsealed-description) (unsealed-description)
--
-- that 6.7 names as unmeasured.
--
-- Both directions of the clause are stated, because only one of them is
-- classical and the free one is the one K2 measured three drafts killed on
-- (CodedCompletion.agda:1148-1155).

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import Cubical.HITs.PropositionalTruncation as PT
import OrdinaryProfile
import CodedCompletion
import K4.Algebra
import K4.InstanceCoded

module K5.ProbeI6
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext   : OrdinaryProfile.Extensionality 𝒮)
  (pow   : OrdinaryProfile.PowerSet 𝒮)
  (sep   : OrdinaryProfile.Separation 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (𝔓     : CodedCompletion.Presentation 𝒮)
  (laws  : CodedCompletion.Coded.ForcingLaws 𝒮 𝔓)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open K4.Algebra 𝒮 using ( Pt; _≤ᴮ_; Lattice; Complement; CodedComplete )

module CD = CodedCompletion.Coded 𝒮 𝔓
open CD using ( carrier; order; Cond; _≼ᴵ_ )

module IC = K4.InstanceCoded 𝒮 ext pow sep paths 𝔓 laws
module CO = IC.CO
module CL = CodedCompletion.Classical 𝒮 ext pow sep paths 𝔓 laws

open Lattice IC.codedLattice using ( _⊓ᴮ_; ⊓-lb₁; ⊓-lb₂; ⊓-glb )

--------------------------------------------------------------------------------
-- ITEM 1c: the unsealed outer meet over ONE unsealed inner description
--------------------------------------------------------------------------------

-- ProbeI3 and ProbeI4 differ in the outer operation and pass and hang
-- respectively. This rung asks what the hang actually needs: is it the
-- unsealed outer meet applied to TWO unsealed descriptions, or does ONE
-- suffice? Here the second argument is a bare variable and the first is K2's
-- unsealed iᴮ, so the type is a nest of two coded operations with exactly one
-- nested argument.
--
-- The statement is one of K2's own order lemmas read at that composite, so
-- the body is a single application and nothing else can be blamed. Capped at
-- 200 s, one option set, same scaffold as every other rung.

oneNest : (p : Cond) (v : Pt CO.B) → ⟨ CO._⊓ᴮ_ (CO.iᴮ p) v ≤ᴮ CO.iᴮ p ⟩
oneNest p v = CO.⊓ᴮ-le₁ (CO.iᴮ p) v

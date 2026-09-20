{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track C, evidence and not a deliverable: the interface between Track C
-- and Track D, checked by the machine.
--
-- Track D wrote its module Meeting (K5/Generic.agda:345-361) against the
-- architecture's part 1.6 rather than against a compiled export, because the
-- two tracks were written in parallel; ledger clause L10 says a drift must
-- then fail in a probe instead of passing silently. This file is that probe.
-- It applies K5.Dense and K5.Generic over ONE telescope and feeds Track C's
-- eight exports to Track D's eight parameters positionally. Exit 0 means the
-- eight types agree character for character after elaboration.
--
-- Two further facts are checked here rather than asserted. First, Track C's
-- notionᶜ and Track D's frameNotion are the SAME inhabitant of K2's
-- ForcingNotion: notion-agree below is refl. Second, Track C's MeetsAll G is
-- the same type as the flat genericity hypothesis Track D writes out, so a
-- consumer may pass one where the other is expected.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import ForcingNotion as FN
import K4.Algebra
import K5.Frame
import K5.Dense
import K5.Generic

module K5.ProbeC
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext   : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (sep   : OrdinaryProfile.Separation 𝒮)
  (carrier order : ZFStructure.S 𝒮)
  (B : ZFStructure.S 𝒮)
  (L  : K4.Algebra.Lattice 𝒮 B)
  (Cm : K4.Algebra.Complement 𝒮 B L)
  (Kc : K4.Algebra.CodedComplete 𝒮 B L)
  (fb : K5.Frame.Poset.ForcingBase 𝒮 carrier order B L Cm)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
import CodedVocabulary
open CodedVocabulary 𝒮 using ( denseΔ )
open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open K5.Frame.Poset 𝒮 carrier order using ( Cond )

module C = K5.Dense 𝒮 ext paths sep carrier order B L Cm Kc fb
module D = K5.Generic.Poset.Image 𝒮 carrier order ext paths B L Cm Kc fb

-- The eight parameters of Track D's Meeting, supplied by Track C.

module M (G : D.FS.Sub) =
  D.Meeting C.decideAt      C.decideAt-sub      C.decideAt-spec
            C.decideAt-dense
            C.coneOrApart   C.coneOrApart-sub   C.coneOrApart-spec
            C.coneOrApart-dense
            G

-- The two forcing notions are one notion.

notion-agree : C.notionᶜ ≡ D.frameNotion
notion-agree = refl

-- Track C's MeetsAll is Track D's flat genericity hypothesis, the one K2
-- states at CodedCompletion.agda:1073-1074 with subsetOf and denseᴵ expanded.

meets-agree : (G : D.FS.Sub)
            → C.MeetsAll G
            ≡ ((d : S) → ⟨ d ⊆ˢ carrier ⟩
                       → ⟨ denseΔ carrier order d ⟩
                       → ⟨ ⋁ Cond (λ q → (D.FS._∈ᴾ_ q G) ⊓ (fst q ∈ˢ d)) ⟩)
meets-agree G = refl

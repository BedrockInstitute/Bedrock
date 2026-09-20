{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import NameSupport
import OrdinaryProfile
import CodedVocabulary
import K4.Algebra
import K4.Compile
import K4.Implication
import K4.AtomicGraph
import K9.BooleanAtomic
import K10.CohenTableReading
import K10.CohenGoodFormula

module K10.CohenImageValue
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import CodedVocabulary 𝒮 using ( isKPairΔ )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ ; ⊆ˢ-trans )
import Cubical.HITs.PropositionalTruncation as PT

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module BAT = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem
  using ( B ; weight ; weight-upper ; weight-least ; module Atomic ; module NG
        ; module IC ; module BK ; module BSupport )
module ISB = NameSupport.Instantiate.BG 𝒮 BAT.NG.sets accessible BAT.B
  using ( kpair-unique )
module LAT = K4.Algebra.Lattice BAT.IC.codedLattice
  using ( _⊓ᴮ_ ; ⊓-glb ; ⊓-lb₁ ; ⊓-lb₂ )
module AG = K4.AtomicGraph 𝒮 paths using ( entryΔ ; closedΔ )
module KIT = K4.Compile 𝒮 BAT.NG.extensional BAT.NG.≈ˢ-paths
  using ( meetΔ )
open module IMP = K4.Implication 𝒮 BAT.NG.extensional BAT.NG.≈ˢ-paths BAT.B
  BAT.IC.codedLattice BAT.IC.codedComplement
  using ( _⇒ᴮ_ ; ⇒ᴮ-curry ; ⇒ᴮ-uncurry ; ≤ᴮ-antisym )
module CGF = K10.CohenGoodFormula 𝒮 BAT.NG.extensional BAT.NG.≈ˢ-paths
module CTR = K10.CohenTableReading 𝒮 families accessible images pow κ w lem paths

module ImageChar (C : S) (x y : S) where

  module R = CTR.Readout C (λ x' y' → fst (BAT.Atomic._≈ᴮ_ x' y'))

  img-upper : (n z a e v : S)
    → ⟨ n ∈ˢ y ⟩ → ⟨ isKPairΔ n z a ⟩
    → ⟨ a ∈ˢ BAT.B ⟩ → ⟨ e ∈ˢ BAT.B ⟩
    → ⟨ AG.entryΔ R.G.graphH x z e ⟩
    → ⟨ KIT.meetΔ BAT.B a e v ⟩
    → ⟨ v ⊆ˢ fst (BAT.Atomic._∈ᴮ_ x y) ⟩
  img-upper n z a e v hn hpka haW heW hentry hmeet =
    ⊆ˢ-trans v≤meet mem≤memPt
    where
    hvB : ⟨ v ∈ˢ BAT.B ⟩
    hvB = fst hmeet
    v⊆a : ⟨ v ⊆ˢ a ⟩
    v⊆a = fst (snd hmeet)
    v⊆e : ⟨ v ⊆ˢ e ⟩
    v⊆e = fst (snd (snd hmeet))

    e≡eq : e ≡ fst (BAT.Atomic._≈ᴮ_ x z)
    e≡eq = snd (snd (R.entryΔ-to x z e hentry))

    v⊆eq : ⟨ v ⊆ˢ fst (BAT.Atomic._≈ᴮ_ x z) ⟩
    v⊆eq = subst (λ t → ⟨ v ⊆ˢ t ⟩) e≡eq v⊆e

    entryz : ⟨ BAT.BK.entry z a ∈ˢ y ⟩
    entryz = subst (λ t → ⟨ t ∈ˢ y ⟩) (ISB.kpair-unique n z a hpka) hn

    z∈sup : ⟨ z ∈ˢ BAT.BSupport.support y ⟩
    z∈sup = BAT.BSupport.entry-in y z a haW entryz

    a≤wt : ⟨ (a , haW) ≤ᴮ BAT.weight y z ⟩
    a≤wt = BAT.weight-upper y z (a , haW) entryz

    v≤wt : ⟨ (v , hvB) ≤ᴮ BAT.weight y z ⟩
    v≤wt = ⊆ˢ-trans v⊆a a≤wt

    v≤eq : ⟨ (v , hvB) ≤ᴮ BAT.Atomic._≈ᴮ_ x z ⟩
    v≤eq = v⊆eq

    v≤meet : ⟨ (v , hvB)
              ≤ᴮ (BAT.weight y z LAT.⊓ᴮ BAT.Atomic._≈ᴮ_ x z) ⟩
    v≤meet = LAT.⊓-glb (BAT.weight y z) (BAT.Atomic._≈ᴮ_ x z)
               (v , hvB) v≤wt v≤eq

    mem≤memPt : ⟨ (BAT.weight y z LAT.⊓ᴮ BAT.Atomic._≈ᴮ_ x z)
                 ≤ᴮ BAT.Atomic._∈ᴮ_ x y ⟩
    mem≤memPt = BAT.Atomic.∈ᴮ-ub x y z z∈sup

  module Closed (hxC : ⟨ x ∈ˢ C ⟩) (hyC : ⟨ y ∈ˢ C ⟩)
    (hclosed : ⟨ AG.closedΔ BAT.B C ⟩) where

    entry-closure : (n z a : S) → ⟨ n ∈ˢ y ⟩ → ⟨ isKPairΔ n z a ⟩
      → ⟨ z ∈ˢ C ⟩
    entry-closure n z a hn hpka =
      PT.rec (snd (z ∈ˢ C))
        (λ { (z' , hz'C , btr) →
          PT.rec (snd (z ∈ˢ C))
            (λ { (b' , hb'B , hikp) →
              subst (λ t → ⟨ t ∈ˢ C ⟩)
                (fst (BAT.BK.entry-inj
                  (sym (ISB.kpair-unique n z' b' hikp)
                    ∙ ISB.kpair-unique n z a hpka)))
                hz'C })
            btr })
        (hclosed y hyC n hn)

    support-to-C : (z : S) → ⟨ z ∈ˢ BAT.BSupport.support y ⟩ → ⟨ z ∈ˢ C ⟩
    support-to-C z hz =
      PT.rec (snd (z ∈ˢ C))
        (λ { (b , hbB , hentry) →
          entry-closure (BAT.BK.entry z b) z b hentry
            (BAT.BK.entry-isKPair z b) })
        (BAT.BSupport.entry-out y z hz)

    meetΔ-⊓ᴮ : (u v : Pt BAT.B)
      → ⟨ KIT.meetΔ BAT.B (fst u) (fst v) (fst (u LAT.⊓ᴮ v)) ⟩
    meetΔ-⊓ᴮ u v =
      ( snd (u LAT.⊓ᴮ v)
      , ( LAT.⊓-lb₁ u v
        , ( LAT.⊓-lb₂ u v
          , λ w hw hu hv → LAT.⊓-glb u v (w , hw) hu hv ) ) )

    img-least : (q : S) → ⟨ q ∈ˢ BAT.B ⟩
      → ⟨ CGF.upperΔ R.G.graphH x y BAT.B q ⟩
      → ⟨ fst (BAT.Atomic._∈ᴮ_ x y) ⊆ˢ q ⟩
    img-least q hqW hupper =
      BAT.Atomic.∈ᴮ-lub x y (q , hqW) step
      where
      step : (z : S) → ⟨ z ∈ˢ BAT.BSupport.support y ⟩
        → ⟨ (BAT.weight y z LAT.⊓ᴮ BAT.Atomic._≈ᴮ_ x z) ≤ᴮ (q , hqW) ⟩
      step z hz =
        ⇒ᴮ-uncurry (BAT.weight y z) (BAT.Atomic._≈ᴮ_ x z) (q , hqW)
          (BAT.weight-least y z
            (BAT.Atomic._≈ᴮ_ x z ⇒ᴮ (q , hqW))
            (λ b hb → ⇒ᴮ-curry b (BAT.Atomic._≈ᴮ_ x z) (q , hqW)
              (hupper (BAT.BK.entry z (fst b)) z (fst b)
                (fst (BAT.Atomic._≈ᴮ_ x z))
                (fst (b LAT.⊓ᴮ BAT.Atomic._≈ᴮ_ x z))
                hb (BAT.BK.entry-isKPair z (fst b)) (snd b)
                (snd (BAT.Atomic._≈ᴮ_ x z))
                (R.entryΔ-from x z (fst (BAT.Atomic._≈ᴮ_ x z)) hxC
                  (support-to-C z hz) refl)
                (meetΔ-⊓ᴮ b (BAT.Atomic._≈ᴮ_ x z)))))

    img-agree : (b : S) → ⟨ CGF.imgΔ R.G.graphH x y b BAT.B ⟩
      → b ≡ fst (BAT.Atomic._∈ᴮ_ x y)
    img-agree b himg = cong fst path
      where
      hbW : ⟨ b ∈ˢ BAT.B ⟩
      hbW = fst himg
      hglb : (q : S) → ⟨ q ∈ˢ BAT.B ⟩
        → ⟨ CGF.upperΔ R.G.graphH x y BAT.B q ⟩ → ⟨ b ⊆ˢ q ⟩
      hglb = snd (snd himg)

      memPt : Pt BAT.B
      memPt = BAT.Atomic._∈ᴮ_ x y

      mem-upper : ⟨ CGF.upperΔ R.G.graphH x y BAT.B (fst memPt) ⟩
      mem-upper p z a e v = img-upper p z a e v

      b≤mem : ⟨ (b , hbW) ≤ᴮ memPt ⟩
      b≤mem = hglb (fst memPt) (snd memPt) mem-upper

      mem≤b : ⟨ memPt ≤ᴮ (b , hbW) ⟩
      mem≤b = img-least b hbW (fst (snd himg))

      path : (b , hbW) ≡ memPt
      path = ≤ᴮ-antisym b≤mem mem≤b

    img-total : ⟨ CGF.imgΔ R.G.graphH x y
                   (fst (BAT.Atomic._∈ᴮ_ x y)) BAT.B ⟩
    img-total =
      ( snd (BAT.Atomic._∈ᴮ_ x y)
      , ( img-upper
        , img-least ) )

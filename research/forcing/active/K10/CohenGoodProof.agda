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
import K10.CohenAtomicTable
import K10.CohenGoodFormula
import K10.CohenImageValue
import K10.CohenWeightMeet

module K10.CohenGoodProof
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
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module BAT = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem
  using ( B ; weight ; weight-upper ; module Atomic ; module NG
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
  using ( _⇒ᴮ_ ; ⇒ᴮ-curry ; ⇒ᴮ-uncurry )
module CGF = K10.CohenGoodFormula 𝒮 BAT.NG.extensional BAT.NG.≈ˢ-paths
module CAT = K10.CohenAtomicTable 𝒮 families accessible images pow κ w lem paths
module CIV = K10.CohenImageValue 𝒮 families accessible images pow κ w lem paths
module CWM = K10.CohenWeightMeet 𝒮 families accessible images pow κ w lem paths

module Canonical (C : S) (hclosed : ⟨ AG.closedΔ BAT.B C ⟩) where

  module EQ = CAT.EQTable C
  module R = EQ.R
  graphH : S
  graphH = R.G.graphH

  child-in : (n : S) → ⟨ n ∈ˢ C ⟩ → (e z a : S)
    → ⟨ e ∈ˢ n ⟩ → ⟨ isKPairΔ e z a ⟩ → ⟨ z ∈ˢ C ⟩
  child-in n hn e z a he hpka =
    PT.rec (snd (z ∈ˢ C))
      (λ { (z' , hz'C , btr) →
        PT.rec (snd (z ∈ˢ C))
          (λ { (b' , hb'B , hikp) →
            subst (λ t → ⟨ t ∈ˢ C ⟩)
              (fst (BAT.BK.entry-inj
                (sym (ISB.kpair-unique e z' b' hikp)
                  ∙ ISB.kpair-unique e z a hpka)))
              hz'C })
          btr })
      (hclosed n hn e he)

  support-in : (n : S) → ⟨ n ∈ˢ C ⟩ → (z : S)
    → ⟨ z ∈ˢ BAT.BSupport.support n ⟩ → ⟨ z ∈ˢ C ⟩
  support-in n hn z hz =
    PT.rec (snd (z ∈ˢ C))
      (λ { (b , hbB , hentry) →
        child-in n hn (BAT.BK.entry z b) z b hentry
          (BAT.BK.entry-isKPair z b) })
      (BAT.BSupport.entry-out n z hz)

  meetΔ-⊓ᴮ : (u v : Pt BAT.B)
    → ⟨ KIT.meetΔ BAT.B (fst u) (fst v) (fst (u LAT.⊓ᴮ v)) ⟩
  meetΔ-⊓ᴮ u v =
    ( snd (u LAT.⊓ᴮ v)
    , ( LAT.⊓-lb₁ u v
      , ( LAT.⊓-lb₂ u v
        , λ q hq hu hv → LAT.⊓-glb u v (q , hq) hu hv ) ) )

  img-total : (x y : S) → ⟨ x ∈ˢ C ⟩ → ⟨ y ∈ˢ C ⟩
    → ⟨ CGF.imgΔ graphH x y (fst (BAT.Atomic._∈ᴮ_ x y)) BAT.B ⟩
  img-total x y hx hy =
    CIV.ImageChar.Closed.img-total C x y hx hy hclosed

  img-agree : (x y b : S) → ⟨ x ∈ˢ C ⟩ → ⟨ y ∈ˢ C ⟩
    → ⟨ CGF.imgΔ graphH x y b BAT.B ⟩
    → b ≡ fst (BAT.Atomic._∈ᴮ_ x y)
  img-agree x y b hx hy himg =
    CIV.ImageChar.Closed.img-agree C x y hx hy hclosed b himg

  img-least : (x y q : S) → ⟨ x ∈ˢ C ⟩ → ⟨ y ∈ˢ C ⟩
    → ⟨ q ∈ˢ BAT.B ⟩ → ⟨ CGF.upperΔ graphH x y BAT.B q ⟩
    → ⟨ fst (BAT.Atomic._∈ᴮ_ x y) ⊆ˢ q ⟩
  img-least x y q hx hy hq hupper =
    CIV.ImageChar.Closed.img-least C x y hx hy hclosed q hq hupper

  module Step (x y : S) (hxC : ⟨ x ∈ˢ C ⟩) (hyC : ⟨ y ∈ˢ C ⟩) where

    eqPt : Pt BAT.B
    eqPt = BAT.Atomic._≈ᴮ_ x y

    lower-left : (b : S) → b ≡ fst eqPt
      → (p z a c v : S)
      → ⟨ p ∈ˢ x ⟩ → ⟨ isKPairΔ p z a ⟩ → ⟨ a ∈ˢ BAT.B ⟩
      → ⟨ CGF.imgΔ graphH z y c BAT.B ⟩
      → ⟨ KIT.meetΔ BAT.B b a v ⟩
      → ⟨ v ⊆ˢ c ⟩
    lower-left b beq p z a c v hp hka haW hcimg hmeet =
      ⊆ˢ-trans v≤mem (img-least z y c zC hyC (fst hcimg) (fst (snd hcimg)))
      where
      hvB : ⟨ v ∈ˢ BAT.B ⟩
      hvB = fst hmeet
      zC : ⟨ z ∈ˢ C ⟩
      zC = child-in x hxC p z a hp hka
      entryz : ⟨ BAT.BK.entry z a ∈ˢ x ⟩
      entryz = subst (λ t → ⟨ t ∈ˢ x ⟩) (ISB.kpair-unique p z a hka) hp
      zsup : ⟨ z ∈ˢ BAT.BSupport.support x ⟩
      zsup = BAT.BSupport.entry-in x z a haW entryz
      v≤eq : ⟨ (v , hvB) ≤ᴮ eqPt ⟩
      v≤eq = subst (λ t → ⟨ v ⊆ˢ t ⟩) beq (fst (snd hmeet))
      v≤wt : ⟨ (v , hvB) ≤ᴮ BAT.weight x z ⟩
      v≤wt = ⊆ˢ-trans (fst (snd (snd hmeet)))
        (BAT.weight-upper x z (a , haW) entryz)
      v≤meet : ⟨ (v , hvB) ≤ᴮ (eqPt LAT.⊓ᴮ BAT.weight x z) ⟩
      v≤meet = LAT.⊓-glb eqPt (BAT.weight x z) (v , hvB) v≤eq v≤wt
      eqwt≤mem : ⟨ (eqPt LAT.⊓ᴮ BAT.weight x z) ≤ᴮ BAT.Atomic._∈ᴮ_ z y ⟩
      eqwt≤mem = ⇒ᴮ-uncurry eqPt (BAT.weight x z) (BAT.Atomic._∈ᴮ_ z y)
        (BAT.Atomic.≈ᴮ-lbˡ x y z zsup)
      v≤mem : ⟨ v ⊆ˢ fst (BAT.Atomic._∈ᴮ_ z y) ⟩
      v≤mem = ⊆ˢ-trans v≤meet eqwt≤mem

    lower-right : (b : S) → b ≡ fst eqPt
      → (p z a c v : S)
      → ⟨ p ∈ˢ y ⟩ → ⟨ isKPairΔ p z a ⟩ → ⟨ a ∈ˢ BAT.B ⟩
      → ⟨ CGF.imgΔ graphH z x c BAT.B ⟩
      → ⟨ KIT.meetΔ BAT.B b a v ⟩
      → ⟨ v ⊆ˢ c ⟩
    lower-right b beq p z a c v hp hka haW hcimg hmeet =
      ⊆ˢ-trans v≤mem (img-least z x c zC hxC (fst hcimg) (fst (snd hcimg)))
      where
      hvB : ⟨ v ∈ˢ BAT.B ⟩
      hvB = fst hmeet
      zC : ⟨ z ∈ˢ C ⟩
      zC = child-in y hyC p z a hp hka
      entryz : ⟨ BAT.BK.entry z a ∈ˢ y ⟩
      entryz = subst (λ t → ⟨ t ∈ˢ y ⟩) (ISB.kpair-unique p z a hka) hp
      zsup : ⟨ z ∈ˢ BAT.BSupport.support y ⟩
      zsup = BAT.BSupport.entry-in y z a haW entryz
      v≤eq : ⟨ (v , hvB) ≤ᴮ eqPt ⟩
      v≤eq = subst (λ t → ⟨ v ⊆ˢ t ⟩) beq (fst (snd hmeet))
      v≤wt : ⟨ (v , hvB) ≤ᴮ BAT.weight y z ⟩
      v≤wt = ⊆ˢ-trans (fst (snd (snd hmeet)))
        (BAT.weight-upper y z (a , haW) entryz)
      v≤meet : ⟨ (v , hvB) ≤ᴮ (eqPt LAT.⊓ᴮ BAT.weight y z) ⟩
      v≤meet = LAT.⊓-glb eqPt (BAT.weight y z) (v , hvB) v≤eq v≤wt
      eqwt≤mem : ⟨ (eqPt LAT.⊓ᴮ BAT.weight y z) ≤ᴮ BAT.Atomic._∈ᴮ_ z x ⟩
      eqwt≤mem = ⇒ᴮ-uncurry eqPt (BAT.weight y z) (BAT.Atomic._∈ᴮ_ z x)
        (BAT.Atomic.≈ᴮ-lbʳ x y z zsup)
      v≤mem : ⟨ v ⊆ˢ fst (BAT.Atomic._∈ᴮ_ z x) ⟩
      v≤mem = ⊆ˢ-trans v≤meet eqwt≤mem

    lower-at : (b : S) → b ≡ fst eqPt → ⟨ CGF.lowerΔ graphH x y BAT.B b ⟩
    lower-at b beq =
      ( (λ p z a c v hp hka haW hcimg hmeet →
          lower-left b beq p z a c v hp hka haW hcimg hmeet)
      , (λ p z a c v hp hka haW hcimg hmeet →
          lower-right b beq p z a c v hp hka haW hcimg hmeet) )

    meet-below-memˡ : (b' : Pt BAT.B) (z : S)
      → ⟨ z ∈ˢ BAT.BSupport.support x ⟩
      → ⟨ CGF.lowerΔ graphH x y BAT.B (fst b') ⟩
      → ⟨ (b' LAT.⊓ᴮ BAT.weight x z) ≤ᴮ BAT.Atomic._∈ᴮ_ z y ⟩
    meet-below-memˡ b' z hz hlower =
      CWM.weight-meet-promote x z b' (BAT.Atomic._∈ᴮ_ z y) raw
      where
      zC : ⟨ z ∈ˢ C ⟩
      zC = support-in x hxC z hz
      raw : (a : Pt BAT.B) → ⟨ BAT.BK.entry z (fst a) ∈ˢ x ⟩
        → ⟨ (b' LAT.⊓ᴮ a) ≤ᴮ BAT.Atomic._∈ᴮ_ z y ⟩
      raw a ha =
        subst (λ t → ⟨ fst (b' LAT.⊓ᴮ a) ⊆ˢ t ⟩)
          (img-agree z y (fst (BAT.Atomic._∈ᴮ_ z y)) zC hyC
            (img-total z y zC hyC))
          (fst hlower (BAT.BK.entry z (fst a)) z (fst a)
            (fst (BAT.Atomic._∈ᴮ_ z y))
            (fst (b' LAT.⊓ᴮ a))
            ha (BAT.BK.entry-isKPair z (fst a)) (snd a)
            (img-total z y zC hyC)
            (meetΔ-⊓ᴮ b' a))

    meet-below-memʳ : (b' : Pt BAT.B) (z : S)
      → ⟨ z ∈ˢ BAT.BSupport.support y ⟩
      → ⟨ CGF.lowerΔ graphH x y BAT.B (fst b') ⟩
      → ⟨ (b' LAT.⊓ᴮ BAT.weight y z) ≤ᴮ BAT.Atomic._∈ᴮ_ z x ⟩
    meet-below-memʳ b' z hz hlower =
      CWM.weight-meet-promote y z b' (BAT.Atomic._∈ᴮ_ z x) raw
      where
      zC : ⟨ z ∈ˢ C ⟩
      zC = support-in y hyC z hz
      raw : (a : Pt BAT.B) → ⟨ BAT.BK.entry z (fst a) ∈ˢ y ⟩
        → ⟨ (b' LAT.⊓ᴮ a) ≤ᴮ BAT.Atomic._∈ᴮ_ z x ⟩
      raw a ha =
        subst (λ t → ⟨ fst (b' LAT.⊓ᴮ a) ⊆ˢ t ⟩)
          (img-agree z x (fst (BAT.Atomic._∈ᴮ_ z x)) zC hxC
            (img-total z x zC hxC))
          (snd hlower (BAT.BK.entry z (fst a)) z (fst a)
            (fst (BAT.Atomic._∈ᴮ_ z x))
            (fst (b' LAT.⊓ᴮ a))
            ha (BAT.BK.entry-isKPair z (fst a)) (snd a)
            (img-total z x zC hxC)
            (meetΔ-⊓ᴮ b' a))

    greatest : (b' : S) → ⟨ b' ∈ˢ BAT.B ⟩
      → ⟨ CGF.lowerΔ graphH x y BAT.B b' ⟩
      → ⟨ b' ⊆ˢ fst eqPt ⟩
    greatest b' hb'B hlower =
      BAT.Atomic.≈ᴮ-glb x y (b' , hb'B)
        (λ z hz → ⇒ᴮ-curry (b' , hb'B) (BAT.weight x z) (BAT.Atomic._∈ᴮ_ z y)
          (meet-below-memˡ (b' , hb'B) z hz hlower))
        (λ z hz → ⇒ᴮ-curry (b' , hb'B) (BAT.weight y z) (BAT.Atomic._∈ᴮ_ z x)
          (meet-below-memʳ (b' , hb'B) z hz hlower))

    step-at-eq : ⟨ CGF.stepΔ graphH x y BAT.B (fst eqPt) ⟩
    step-at-eq =
      ( snd eqPt
      , ( lower-at (fst eqPt) refl
        , greatest ) )

    step-at : (b : S) → ⟨ AG.entryΔ graphH x y b ⟩
      → ⟨ CGF.stepΔ graphH x y BAT.B b ⟩
    step-at b hentry =
      subst (λ t → ⟨ CGF.stepΔ graphH x y BAT.B t ⟩)
        (sym (snd (snd (EQ.read-eq x y b hentry))))
        step-at-eq

  good-canonical : ⟨ CGF.goodΔ BAT.B C graphH ⟩
  good-canonical =
    ( (λ x hx y hy →
        let w = EQ.atomic-total x y hx hy
        in ∣ fst w , snd w ∣₁)
    , ( (λ x hx y hy b hentry → EQ.atomic-range x y b hentry)
      , (λ x hx y hy b hentry → Step.step-at x y hx hy b hentry) ) )

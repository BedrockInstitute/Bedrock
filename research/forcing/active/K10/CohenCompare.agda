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
import K10.CohenGoodFormula
import K10.CohenGoodProof
import K10.CohenWeightMeet

module K10.CohenCompare
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
open K4.Algebra 𝒮 using ( Pt ; Pt≡ ; _≤ᴮ_ ; ⊆ˢ-trans )
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
  using ( _⇒ᴮ_ ; ⇒ᴮ-curry ; ⇒ᴮ-uncurry ; ⊓-comm ; ≤ᴮ-antisym )
module CGF = K10.CohenGoodFormula 𝒮 BAT.NG.extensional BAT.NG.≈ˢ-paths
module CGP = K10.CohenGoodProof 𝒮 families accessible images pow κ w lem paths
module CWM = K10.CohenWeightMeet 𝒮 families accessible images pow κ w lem paths

module OnDomain (C : S) (hclosed : ⟨ AG.closedΔ BAT.B C ⟩) where

  module Can = CGP.Canonical C hclosed
  open Can using ( child-in ; support-in ; meetΔ-⊓ᴮ )

  child-of : (n z a : S) → ⟨ BAT.BK.entry z a ∈ˢ n ⟩ → BAT.BK.Child z n
  child-of n z a he = ∣ a , he ∣₁

  child-from-pair : (n p z a : S)
    → ⟨ p ∈ˢ n ⟩ → ⟨ isKPairΔ p z a ⟩ → BAT.BK.Child z n
  child-from-pair n p z a hp hka =
    child-of n z a (subst (λ t → ⟨ t ∈ˢ n ⟩) (ISB.kpair-unique p z a hka) hp)

  AgreeEq : S → S → Type ℓ
  AgreeEq x y =
    ⟨ x ∈ˢ C ⟩ → ⟨ y ∈ˢ C ⟩ →
    (H : S) → ⟨ CGF.goodΔ BAT.B C H ⟩ →
    (b : S) → ⟨ AG.entryΔ H x y b ⟩ → b ≡ fst (BAT.Atomic._≈ᴮ_ x y)

  module ImgOf (z y : S) (hzC : ⟨ z ∈ˢ C ⟩) (hyC : ⟨ y ∈ˢ C ⟩)
    (eqIH : (v : S) → BAT.BK.Child v y → AgreeEq z v)
    (H : S) (hgood : ⟨ CGF.goodΔ BAT.B C H ⟩) where

    memPt : Pt BAT.B
    memPt = BAT.Atomic._∈ᴮ_ z y

    eqPtAt : (v : S) → Pt BAT.B
    eqPtAt v = BAT.Atomic._≈ᴮ_ z v

    rangeH : (x' y' b : S) → ⟨ x' ∈ˢ C ⟩ → ⟨ y' ∈ˢ C ⟩
      → ⟨ AG.entryΔ H x' y' b ⟩ → ⟨ b ∈ˢ BAT.B ⟩
    rangeH x' y' b hx' hy' = fst (snd hgood) x' hx' y' hy' b

    totalH : (x' y' : S) → ⟨ x' ∈ˢ C ⟩ → ⟨ y' ∈ˢ C ⟩
      → ⟨ ⋁ S (λ b → (b ∈ˢ BAT.B) ⊓ AG.entryΔ H x' y' b) ⟩
    totalH x' y' hx' hy' = fst hgood x' hx' y' hy'

    img-upper-mem : ⟨ CGF.upperΔ H z y BAT.B (fst memPt) ⟩
    img-upper-mem p v a e t hp hka haW heW hentry hmeet =
      ⊆ˢ-trans t≤meet fam≤mem
      where
      hvC : ⟨ v ∈ˢ C ⟩
      hvC = child-in y hyC p v a hp hka
      e≡eq : e ≡ fst (eqPtAt v)
      e≡eq = eqIH v (child-from-pair y p v a hp hka) hzC hvC H hgood e hentry
      htB : ⟨ t ∈ˢ BAT.B ⟩
      htB = fst hmeet
      entryv : ⟨ BAT.BK.entry v a ∈ˢ y ⟩
      entryv = subst (λ u → ⟨ u ∈ˢ y ⟩) (ISB.kpair-unique p v a hka) hp
      vsup : ⟨ v ∈ˢ BAT.BSupport.support y ⟩
      vsup = BAT.BSupport.entry-in y v a haW entryv
      t≤wt : ⟨ (t , htB) ≤ᴮ BAT.weight y v ⟩
      t≤wt = ⊆ˢ-trans (fst (snd hmeet))
        (BAT.weight-upper y v (a , haW) entryv)
      t≤eq : ⟨ (t , htB) ≤ᴮ eqPtAt v ⟩
      t≤eq = subst (λ u → ⟨ t ⊆ˢ u ⟩) e≡eq (fst (snd (snd hmeet)))
      t≤meet : ⟨ (t , htB) ≤ᴮ (BAT.weight y v LAT.⊓ᴮ eqPtAt v) ⟩
      t≤meet = LAT.⊓-glb (BAT.weight y v) (eqPtAt v) (t , htB) t≤wt t≤eq
      fam≤mem : ⟨ (BAT.weight y v LAT.⊓ᴮ eqPtAt v) ≤ᴮ memPt ⟩
      fam≤mem = BAT.Atomic.∈ᴮ-ub z y v vsup

    img-least-mem : (q : S) → ⟨ q ∈ˢ BAT.B ⟩
      → ⟨ CGF.upperΔ H z y BAT.B q ⟩
      → ⟨ fst memPt ⊆ˢ q ⟩
    img-least-mem q hqW hupper =
      BAT.Atomic.∈ᴮ-lub z y (q , hqW) fam
      where
      fam : (v : S) → ⟨ v ∈ˢ BAT.BSupport.support y ⟩
        → ⟨ (BAT.weight y v LAT.⊓ᴮ eqPtAt v) ≤ᴮ (q , hqW) ⟩
      fam v hv =
        subst (λ u → ⟨ u ≤ᴮ (q , hqW) ⟩)
          (⊓-comm (eqPtAt v) (BAT.weight y v))
          (CWM.weight-meet-promote y v (eqPtAt v) (q , hqW) raw)
        where
        vC : ⟨ v ∈ˢ C ⟩
        vC = support-in y hyC v hv
        raw : (a : Pt BAT.B) → ⟨ BAT.BK.entry v (fst a) ∈ˢ y ⟩
          → ⟨ (eqPtAt v LAT.⊓ᴮ a) ≤ᴮ (q , hqW) ⟩
        raw a ha =
          PT.rec (snd ((eqPtAt v LAT.⊓ᴮ a) ≤ᴮ (q , hqW)))
            (λ { (e , heB , hentry) → raw-at a ha e heB hentry })
            (totalH z v hzC vC)
          where
          raw-at : (a : Pt BAT.B) → ⟨ BAT.BK.entry v (fst a) ∈ˢ y ⟩
            → (e : S) → ⟨ e ∈ˢ BAT.B ⟩ → ⟨ AG.entryΔ H z v e ⟩
            → ⟨ (eqPtAt v LAT.⊓ᴮ a) ≤ᴮ (q , hqW) ⟩
          raw-at a ha e heB hentry =
            subst (λ u → ⟨ u ⊆ˢ q ⟩) (sym want≡t) t⊆q
            where
            e≡ : e ≡ fst (eqPtAt v)
            e≡ = eqIH v (child-of y v (fst a) ha) hzC vC H hgood e hentry
            ePt : Pt BAT.B
            ePt = e , heB
            t : S
            t = fst (a LAT.⊓ᴮ ePt)
            t⊆q : ⟨ t ⊆ˢ q ⟩
            t⊆q = hupper (BAT.BK.entry v (fst a)) v (fst a) e t
              ha (BAT.BK.entry-isKPair v (fst a)) (snd a) heB
              hentry (meetΔ-⊓ᴮ a ePt)
            ePt≡eq : ePt ≡ eqPtAt v
            ePt≡eq = Pt≡ e≡
            want≡t : fst (eqPtAt v LAT.⊓ᴮ a) ≡ t
            want≡t =
              cong fst (⊓-comm (eqPtAt v) a
                ∙ cong (a LAT.⊓ᴮ_) (sym ePt≡eq))

    img-total : ⟨ CGF.imgΔ H z y (fst memPt) BAT.B ⟩
    img-total = snd memPt , img-upper-mem , img-least-mem

    img-agree : (c : S) → ⟨ CGF.imgΔ H z y c BAT.B ⟩
      → c ≡ fst memPt
    img-agree c himg = cong fst path
      where
      hcW : ⟨ c ∈ˢ BAT.B ⟩
      hcW = fst himg
      c≤mem : ⟨ (c , hcW) ≤ᴮ memPt ⟩
      c≤mem = snd (snd himg) (fst memPt) (snd memPt) img-upper-mem
      mem≤c : ⟨ memPt ≤ᴮ (c , hcW) ⟩
      mem≤c = img-least-mem c hcW (fst (snd himg))
      path : (c , hcW) ≡ memPt
      path = ≤ᴮ-antisym c≤mem mem≤c

  step₁ : (x y : S)
    → ((u v : S) → BAT.BK.Child u x → BAT.BK.Child v y → AgreeEq u v × AgreeEq v u)
    → AgreeEq x y
  step₁ x y IH hxC hyC H hgood b hentry =
    cong fst (≤ᴮ-antisym {u = bPt} {v = eqPt} b≤eq eq≤b)
    where
    rec : ⟨ CGF.stepΔ H x y BAT.B b ⟩
    rec = snd (snd hgood) x hxC y hyC b hentry
    hbB : ⟨ b ∈ˢ BAT.B ⟩
    hbB = fst rec
    hlower : ⟨ CGF.lowerΔ H x y BAT.B b ⟩
    hlower = fst (snd rec)
    hgreat : ⟨ ⋀ S (λ b' → (b' ∈ˢ BAT.B)
      ⇒ CGF.lowerΔ H x y BAT.B b' ⇒ (b' ⊆ˢ b)) ⟩
    hgreat = snd (snd rec)
    eqPt : Pt BAT.B
    eqPt = BAT.Atomic._≈ᴮ_ x y
    bPt : Pt BAT.B
    bPt = b , hbB

    module IMˡ (z : S) (cz : BAT.BK.Child z x) (zC : ⟨ z ∈ˢ C ⟩) =
      ImgOf z y zC hyC (λ v cv → fst (IH z v cz cv)) H hgood

    module IMʳ (z : S) (cz : BAT.BK.Child z y) (zC : ⟨ z ∈ˢ C ⟩) =
      ImgOf z x zC hxC (λ v cv → snd (IH v z cv cz)) H hgood

    lower-eq : ⟨ CGF.lowerΔ H x y BAT.B (fst eqPt) ⟩
    lower-eq =
      ( (λ p z a c v hp hka haW hcimg hmeet →
          left p z a c v hp hka haW hcimg hmeet)
      , (λ p z a c v hp hka haW hcimg hmeet →
          right p z a c v hp hka haW hcimg hmeet) )
      where
      left : (p z a c v : S)
        → ⟨ p ∈ˢ x ⟩ → ⟨ isKPairΔ p z a ⟩ → ⟨ a ∈ˢ BAT.B ⟩
        → ⟨ CGF.imgΔ H z y c BAT.B ⟩
        → ⟨ KIT.meetΔ BAT.B (fst eqPt) a v ⟩
        → ⟨ v ⊆ˢ c ⟩
      left p z a c v hp hka haW hcimg hmeet =
        ⊆ˢ-trans v≤mem (subst (λ t → ⟨ fst (BAT.Atomic._∈ᴮ_ z y) ⊆ˢ t ⟩)
          (sym (IMˡ.img-agree z cz zC c hcimg)) (λ _ h → h))
        where
        zC : ⟨ z ∈ˢ C ⟩
        zC = child-in x hxC p z a hp hka
        cz : BAT.BK.Child z x
        cz = child-from-pair x p z a hp hka
        hvB : ⟨ v ∈ˢ BAT.B ⟩
        hvB = fst hmeet
        entryz : ⟨ BAT.BK.entry z a ∈ˢ x ⟩
        entryz = subst (λ t → ⟨ t ∈ˢ x ⟩) (ISB.kpair-unique p z a hka) hp
        zsup : ⟨ z ∈ˢ BAT.BSupport.support x ⟩
        zsup = BAT.BSupport.entry-in x z a haW entryz
        v≤eq : ⟨ (v , hvB) ≤ᴮ eqPt ⟩
        v≤eq = fst (snd hmeet)
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
      right : (p z a c v : S)
        → ⟨ p ∈ˢ y ⟩ → ⟨ isKPairΔ p z a ⟩ → ⟨ a ∈ˢ BAT.B ⟩
        → ⟨ CGF.imgΔ H z x c BAT.B ⟩
        → ⟨ KIT.meetΔ BAT.B (fst eqPt) a v ⟩
        → ⟨ v ⊆ˢ c ⟩
      right p z a c v hp hka haW hcimg hmeet =
        ⊆ˢ-trans v≤mem (subst (λ t → ⟨ fst (BAT.Atomic._∈ᴮ_ z x) ⊆ˢ t ⟩)
          (sym (IMʳ.img-agree z cz zC c hcimg)) (λ _ h → h))
        where
        zC : ⟨ z ∈ˢ C ⟩
        zC = child-in y hyC p z a hp hka
        cz : BAT.BK.Child z y
        cz = child-from-pair y p z a hp hka
        hvB : ⟨ v ∈ˢ BAT.B ⟩
        hvB = fst hmeet
        entryz : ⟨ BAT.BK.entry z a ∈ˢ y ⟩
        entryz = subst (λ t → ⟨ t ∈ˢ y ⟩) (ISB.kpair-unique p z a hka) hp
        zsup : ⟨ z ∈ˢ BAT.BSupport.support y ⟩
        zsup = BAT.BSupport.entry-in y z a haW entryz
        v≤eq : ⟨ (v , hvB) ≤ᴮ eqPt ⟩
        v≤eq = fst (snd hmeet)
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

    eq≤b : ⟨ eqPt ≤ᴮ bPt ⟩
    eq≤b = hgreat (fst eqPt) (snd eqPt) lower-eq

    b≤eq : ⟨ bPt ≤ᴮ eqPt ⟩
    b≤eq = BAT.Atomic.≈ᴮ-glb x y bPt left right
      where
      left : (z : S) → ⟨ z ∈ˢ BAT.BSupport.support x ⟩
        → ⟨ bPt ≤ᴮ (BAT.weight x z ⇒ᴮ BAT.Atomic._∈ᴮ_ z y) ⟩
      left z hz = ⇒ᴮ-curry bPt (BAT.weight x z) (BAT.Atomic._∈ᴮ_ z y)
        (CWM.weight-meet-promote x z bPt (BAT.Atomic._∈ᴮ_ z y) raw)
        where
        zC : ⟨ z ∈ˢ C ⟩
        zC = support-in x hxC z hz
        raw : (a : Pt BAT.B) → ⟨ BAT.BK.entry z (fst a) ∈ˢ x ⟩
          → ⟨ (bPt LAT.⊓ᴮ a) ≤ᴮ BAT.Atomic._∈ᴮ_ z y ⟩
        raw a ha =
          subst (λ t → ⟨ fst (bPt LAT.⊓ᴮ a) ⊆ˢ t ⟩)
            (IMˡ.img-agree z (child-of x z (fst a) ha) zC
              (fst (BAT.Atomic._∈ᴮ_ z y)) (IMˡ.img-total z (child-of x z (fst a) ha) zC))
            (fst hlower (BAT.BK.entry z (fst a)) z (fst a)
              (fst (BAT.Atomic._∈ᴮ_ z y))
              (fst (bPt LAT.⊓ᴮ a))
              ha (BAT.BK.entry-isKPair z (fst a)) (snd a)
              (IMˡ.img-total z (child-of x z (fst a) ha) zC)
              (meetΔ-⊓ᴮ bPt a))
      right : (z : S) → ⟨ z ∈ˢ BAT.BSupport.support y ⟩
        → ⟨ bPt ≤ᴮ (BAT.weight y z ⇒ᴮ BAT.Atomic._∈ᴮ_ z x) ⟩
      right z hz = ⇒ᴮ-curry bPt (BAT.weight y z) (BAT.Atomic._∈ᴮ_ z x)
        (CWM.weight-meet-promote y z bPt (BAT.Atomic._∈ᴮ_ z x) raw)
        where
        zC : ⟨ z ∈ˢ C ⟩
        zC = support-in y hyC z hz
        raw : (a : Pt BAT.B) → ⟨ BAT.BK.entry z (fst a) ∈ˢ y ⟩
          → ⟨ (bPt LAT.⊓ᴮ a) ≤ᴮ BAT.Atomic._∈ᴮ_ z x ⟩
        raw a ha =
          subst (λ t → ⟨ fst (bPt LAT.⊓ᴮ a) ⊆ˢ t ⟩)
            (IMʳ.img-agree z (child-of y z (fst a) ha) zC
              (fst (BAT.Atomic._∈ᴮ_ z x)) (IMʳ.img-total z (child-of y z (fst a) ha) zC))
            (snd hlower (BAT.BK.entry z (fst a)) z (fst a)
              (fst (BAT.Atomic._∈ᴮ_ z x))
              (fst (bPt LAT.⊓ᴮ a))
              ha (BAT.BK.entry-isKPair z (fst a)) (snd a)
              (IMʳ.img-total z (child-of y z (fst a) ha) zC)
              (meetΔ-⊓ᴮ bPt a))

  Both : S → S → Type ℓ
  Both x y = AgreeEq x y × AgreeEq y x

  stepBoth : (x y : S)
    → ((u v : S) → BAT.BK.Child u x → BAT.BK.Child v y → Both u v)
    → Both x y
  stepBoth x y IH =
    ( step₁ x y IH
    , step₁ y x (λ u v cu cv → IH v u cv cu .snd , IH v u cv cu .fst) )

  module Pair = BAT.BK.RawPairRec Both stepBoth

  eq-agree : (x y : S) → AgreeEq x y
  eq-agree x y = Pair.result x y .fst

  img-agree : (x y c : S) → ⟨ x ∈ˢ C ⟩ → ⟨ y ∈ˢ C ⟩
    → (H : S) → ⟨ CGF.goodΔ BAT.B C H ⟩
    → ⟨ CGF.imgΔ H x y c BAT.B ⟩
    → c ≡ fst (BAT.Atomic._∈ᴮ_ x y)
  img-agree x y c hxC hyC H hgood himg =
    ImgOf.img-agree x y hxC hyC
      (λ v _ → eq-agree x v) H hgood c himg

eq-unique : (C D : S)
  → ⟨ AG.closedΔ BAT.B C ⟩ → ⟨ AG.closedΔ BAT.B D ⟩
  → (H K x y b c : S)
  → ⟨ CGF.goodΔ BAT.B C H ⟩ → ⟨ CGF.goodΔ BAT.B D K ⟩
  → ⟨ x ∈ˢ C ⟩ → ⟨ y ∈ˢ C ⟩ → ⟨ x ∈ˢ D ⟩ → ⟨ y ∈ˢ D ⟩
  → ⟨ AG.entryΔ H x y b ⟩ → ⟨ AG.entryΔ K x y c ⟩ → b ≡ c
eq-unique C D clC clD H K x y b c gdH gdK hxC hyC hxD hyD enH enK =
  OnDomain.eq-agree C clC x y hxC hyC H gdH b enH
    ∙ sym (OnDomain.eq-agree D clD x y hxD hyD K gdK c enK)

mem-unique : (C D : S)
  → ⟨ AG.closedΔ BAT.B C ⟩ → ⟨ AG.closedΔ BAT.B D ⟩
  → (H K x y b c : S)
  → ⟨ CGF.goodΔ BAT.B C H ⟩ → ⟨ CGF.goodΔ BAT.B D K ⟩
  → ⟨ x ∈ˢ C ⟩ → ⟨ y ∈ˢ C ⟩ → ⟨ x ∈ˢ D ⟩ → ⟨ y ∈ˢ D ⟩
  → ⟨ CGF.imgΔ H x y b BAT.B ⟩ → ⟨ CGF.imgΔ K x y c BAT.B ⟩ → b ≡ c
mem-unique C D clC clD H K x y b c gdH gdK hxC hyC hxD hyD imH imK =
  OnDomain.img-agree C clC x y b hxC hyC H gdH imH
    ∙ sym (OnDomain.img-agree D clD x y c hxD hyD K gdK imK)

{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import NameSupport
import OrdinaryProfile
import CodedVocabulary
import K4.AtomicGraph
import K9.BooleanNameGround
import K10.CohenTableGraph
import K10.CohenGoodTable

module K10.CohenTableReading
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
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.HLevels using ( isProp× )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module BG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
  using ( B ; module BK )
module ISB = NameSupport.Instantiate.BG 𝒮 (NameKernel.Families.sets families)
  accessible BG.B
  using ( kpair-unique )
module AG = K4.AtomicGraph 𝒮 paths using ( entryΔ )
module CTG = K10.CohenTableGraph 𝒮 families accessible images pow κ w lem
module CGT = K10.CohenGoodTable 𝒮 families accessible images pow κ w lem paths
  using ( entryΔ-in ; entryΔ-out )

module Readout (C : S) (f : S → S → S) where

  module G = CTG.Graph C f

  entryΔ-to : (x y b : S) → ⟨ AG.entryΔ G.graphH x y b ⟩
    → ⟨ x ∈ˢ C ⟩ × ⟨ y ∈ˢ C ⟩ × (b ≡ f x y)
  entryΔ-to x y b h =
    PT.rec target-prop
      (λ { (p , q , hqH , hqpb , hpq) →
        PT.rec target-prop
          (λ { (x' , hx' , y' , hy' , heq) →
            step x' y' q p hx' hy' heq hqpb hpq })
          (G.graphH-out q hqH) })
      (CGT.entryΔ-out G.graphH x y b h)
    where
    target : Type ℓ
    target = ⟨ x ∈ˢ C ⟩ × ⟨ y ∈ˢ C ⟩ × (b ≡ f x y)
    target-prop : isProp target
    target-prop = isProp× (snd (x ∈ˢ C))
      (isProp× (snd (y ∈ˢ C)) (isSetS b (f x y)))

    step : (x' y' q p : S)
         → (hx' : ⟨ x' ∈ˢ C ⟩) → (hy' : ⟨ y' ∈ˢ C ⟩)
         → (heq : q ≡ BG.BK.entry (BG.BK.entry x' y') (f x' y'))
         → (hqpb : ⟨ isKPairΔ q p b ⟩)
         → (hpq : ⟨ isKPairΔ p x y ⟩)
         → target
    step x' y' q p hx' hy' heq hqpb hpq =
      ( subst (λ a → ⟨ a ∈ˢ C ⟩) xp hx'
      , subst (λ a → ⟨ a ∈ˢ C ⟩) yp hy'
      , bv≡ ∙ cong₂ f xp yp )
      where
      outer-eq : BG.BK.entry p b ≡ BG.BK.entry (BG.BK.entry x' y') (f x' y')
      outer-eq = sym (ISB.kpair-unique q p b hqpb) ∙ heq
      pb-decomp : p ≡ BG.BK.entry x' y'
      pb-decomp = fst (BG.BK.entry-inj outer-eq)
      bv≡ : b ≡ f x' y'
      bv≡ = snd (BG.BK.entry-inj outer-eq)
      hpq' : ⟨ isKPairΔ (BG.BK.entry x' y') x y ⟩
      hpq' = subst (λ a → ⟨ isKPairΔ a x y ⟩) pb-decomp hpq
      xy-decomp : (x' ≡ x) × (y' ≡ y)
      xy-decomp = BG.BK.entry-inj
        (ISB.kpair-unique (BG.BK.entry x' y') x y hpq')
      xp : x' ≡ x
      xp = fst xy-decomp
      yp : y' ≡ y
      yp = snd xy-decomp

  entryΔ-from : (x y b : S) → ⟨ x ∈ˢ C ⟩ → ⟨ y ∈ˢ C ⟩ → b ≡ f x y
    → ⟨ AG.entryΔ G.graphH x y b ⟩
  entryΔ-from x y b hx hy hb≡ =
    CGT.entryΔ-in G.graphH x y b p q hpq hqpb hqH
    where
    p : S
    p = BG.BK.entry x y
    q : S
    q = BG.BK.entry p b
    hpq : ⟨ isKPairΔ p x y ⟩
    hpq = BG.BK.entry-isKPair x y
    hqpb : ⟨ isKPairΔ q p b ⟩
    hqpb = BG.BK.entry-isKPair p b
    hqH : ⟨ q ∈ˢ G.graphH ⟩
    hqH = G.graphH-in q x y hx hy (cong (BG.BK.entry p) hb≡)

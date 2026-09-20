{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile

module K9.PairNames
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sum using ( inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import CardinalBridge
import K7.CardinalOrder
import K9.NameGround

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
module Ground = K9.NameGround 𝒮 families accessible images pow κ w
private
  module GS = Ground.GS
  module Union = Ground.Union
  module C = Ground.C
  module K = Ground.K
  module Image = Ground.Image
  module Check = Ground.Check

private
  ≈ˢ-refl : (x : S) → ⟨ x ≈ˢ x ⟩
  ≈ˢ-refl x = subst ⟨_⟩ (sym (Ground.≈ˢ-paths x x)) refl

layer : S → S → Ω
layer x e = ⋁ S (λ p → (p ∈ˢ C.carrier) ⊓ (e ≈ˢ K.entry x p))

opaque
  singleCode : S → S
  singleCode = Check.spread

  single-spec : (x e : S) → (e ∈ˢ singleCode x) ≡ layer x e
  single-spec = Check.spread-spec

single-name : (σ : K.Name) → ⟨ K.IsName (singleCode (fst σ)) ⟩
single-name σ = Ground.entries-name (singleCode (fst σ)) λ e he →
  PT.map (λ { (p , hp , eq) → fst σ , p , GS.≈→≡ eq , hp , snd σ })
    (subst ⟨_⟩ (single-spec (fst σ) e) he)

singleNm : K.Name → K.Name
singleNm σ = singleCode (fst σ) , single-name σ

opaque
  pairLayers : S → S → S
  pairLayers m n = Image.imageOn (GS.pairOf m n) Check.spread

  pairCode : S → S → S
  pairCode m n = Union.bigUnion (pairLayers m n)

  pair-spec : (m n e : S) → (e ∈ˢ pairCode m n) ≡ (layer m e ⊔ layer n e)
  pair-spec m n e = ⇔toPath forward backward
    where
    target : Ω
    target = layer m e ⊔ layer n e

    forward : ⟨ e ∈ˢ pairCode m n ⟩ → ⟨ target ⟩
    forward he = PT.rec (snd target)
      (λ { (u , hu , eu) → PT.rec (snd target)
        (λ { (x , hx , ux) → PT.rec (snd target)
          (λ { (inl xm) → ∣ inl (subst (λ z → ⟨ layer z e ⟩) (GS.≈→≡ xm)
                (subst ⟨_⟩ (Check.spread-spec x e)
                  (subst (λ z → ⟨ e ∈ˢ z ⟩) (GS.≈→≡ ux) eu))) ∣₁
             ; (inr xn) → ∣ inr (subst (λ z → ⟨ layer z e ⟩) (GS.≈→≡ xn)
                (subst ⟨_⟩ (Check.spread-spec x e)
                  (subst (λ z → ⟨ e ∈ˢ z ⟩) (GS.≈→≡ ux) eu))) ∣₁ })
          (GS.pairOf-out m n x hx) })
        (subst ⟨_⟩ (Image.imageOn-spec (GS.pairOf m n) Check.spread u) hu) })
      (subst ⟨_⟩ (Union.bigUnion-spec (pairLayers m n) e) he)

    backward : ⟨ target ⟩ → ⟨ e ∈ˢ pairCode m n ⟩
    backward = PT.rec (snd (e ∈ˢ pairCode m n)) λ
      { (inl hm) → subst ⟨_⟩ (sym (Union.bigUnion-spec (pairLayers m n) e))
          ∣ Check.spread m
          , subst ⟨_⟩ (sym (Image.imageOn-spec (GS.pairOf m n) Check.spread
              (Check.spread m)))
              ∣ m , GS.pairOf-inˡ m n , ≈ˢ-refl (Check.spread m) ∣₁
          , subst ⟨_⟩ (sym (Check.spread-spec m e)) hm ∣₁
      ; (inr hn) → subst ⟨_⟩ (sym (Union.bigUnion-spec (pairLayers m n) e))
          ∣ Check.spread n
          , subst ⟨_⟩ (sym (Image.imageOn-spec (GS.pairOf m n) Check.spread
              (Check.spread n)))
              ∣ n , GS.pairOf-inʳ m n , ≈ˢ-refl (Check.spread n) ∣₁
          , subst ⟨_⟩ (sym (Check.spread-spec n e)) hn ∣₁ }

pair-name : (σ τ : K.Name) → ⟨ K.IsName (pairCode (fst σ) (fst τ)) ⟩
pair-name σ τ = Ground.entries-name (pairCode (fst σ) (fst τ)) λ e he →
  PT.rec PT.squash₁
    (λ { (inl hm) → PT.map
            (λ { (p , hp , eq) → fst σ , p , GS.≈→≡ eq , hp , snd σ }) hm
       ; (inr hn) → PT.map
            (λ { (p , hp , eq) → fst τ , p , GS.≈→≡ eq , hp , snd τ }) hn })
    (subst ⟨_⟩ (pair-spec (fst σ) (fst τ) e) he)

pairNm : K.Name → K.Name → K.Name
pairNm σ τ = pairCode (fst σ) (fst τ) , pair-name σ τ

orderedNm : K.Name → K.Name → K.Name
orderedNm σ τ = pairNm (singleNm σ) (pairNm σ τ)

module AtGeneric (G : Ground.P.Sub) where
  module A = Ground.AtGeneric G
  module E = A.E
  private module CB = CardinalBridge Ground.PS.𝒮ᴾ[ G ]

  pair-value : (fil : Ground.P.isFilter G) (m n z : S)
             → (z E.∈[G] pairCode m n) ≡ ((z E.≈[G] m) ⊔ (z E.≈[G] n))
  pair-value fil m n z = ⇔toPath forward backward
    where
    target : Ω
    target = (z E.≈[G] m) ⊔ (z E.≈[G] n)

    forward : ⟨ z E.∈[G] pairCode m n ⟩ → ⟨ target ⟩
    forward hz = PT.rec (snd target)
      (λ { (y , hy , zy) → PT.rec (snd target)
        (λ { (p , hp , member , hG) → PT.rec (snd target)
          (λ { (inl hm) → PT.map
                  (λ { (q , hq , eq) → inl (subst (λ x → ⟨ z E.≈[G] x ⟩)
                    (K.entry-inj (GS.≈→≡ eq) .fst) zy) }) hm
             ; (inr hn) → PT.map
                  (λ { (q , hq , eq) → inr (subst (λ x → ⟨ z E.≈[G] x ⟩)
                    (K.entry-inj (GS.≈→≡ eq) .fst) zy) }) hn })
          (subst ⟨_⟩ (pair-spec m n (K.entry y p)) member) }) hy }) hz

    backward : ⟨ target ⟩ → ⟨ z E.∈[G] pairCode m n ⟩
    backward h = PT.rec (snd (z E.∈[G] pairCode m n))
      (λ { ((p , hp) , hG) → PT.rec (snd (z E.∈[G] pairCode m n))
        (λ { (inl zm) → E.∈-congˡ (E.≈-sym zm)
                (E.entry-value (pairCode m n) m p hp hG
                  (subst ⟨_⟩ (sym (pair-spec m n (K.entry m p)))
                    ∣ inl ∣ p , hp , ≈ˢ-refl (K.entry m p) ∣₁ ∣₁))
           ; (inr zn) → E.∈-congˡ (E.≈-sym zn)
                (E.entry-value (pairCode m n) n p hp hG
                  (subst ⟨_⟩ (sym (pair-spec m n (K.entry n p)))
                    ∣ inr ∣ p , hp , ≈ˢ-refl (K.entry n p) ∣₁ ∣₁)) }) h })
      (Ground.P.isFilter.inhabited fil)

  single-value : (fil : Ground.P.isFilter G) (m z : S)
               → (z E.∈[G] singleCode m) ≡ (z E.≈[G] m)
  single-value fil m z = ⇔toPath forward backward
    where
    forward : ⟨ z E.∈[G] singleCode m ⟩ → ⟨ z E.≈[G] m ⟩
    forward hz = PT.rec (snd (z E.≈[G] m))
      (λ { (y , hy , zy) → PT.rec (snd (z E.≈[G] m))
        (λ { (p , hp , member , hG) → PT.rec (snd (z E.≈[G] m))
          (λ { (q , hq , eq) → subst (λ x → ⟨ z E.≈[G] x ⟩)
            (K.entry-inj (GS.≈→≡ eq) .fst) zy })
          (subst ⟨_⟩ (single-spec m (K.entry y p)) member) }) hy }) hz

    backward : ⟨ z E.≈[G] m ⟩ → ⟨ z E.∈[G] singleCode m ⟩
    backward zm = PT.rec (snd (z E.∈[G] singleCode m))
      (λ { ((p , hp) , hG) → E.∈-congˡ (E.≈-sym zm)
        (E.entry-value (singleCode m) m p hp hG
          (subst ⟨_⟩ (sym (single-spec m (K.entry m p)))
            ∣ p , hp , ≈ˢ-refl (K.entry m p) ∣₁)) })
      (Ground.P.isFilter.inhabited fil)

  single-isSingleton : (fil : Ground.P.isFilter G) (σ : K.Name)
                     → ⟨ CB.isSingleton (singleNm σ) σ ⟩
  single-isSingleton fil σ =
      subst ⟨_⟩ (sym (single-value fil (fst σ) (fst σ))) (E.≈-refl (fst σ))
    , λ ρ hρ → subst ⟨_⟩ (single-value fil (fst σ) (fst ρ)) hρ

  pair-isPair : (fil : Ground.P.isFilter G) (σ τ : K.Name)
              → ⟨ CB.isPair (pairNm σ τ) σ τ ⟩
  pair-isPair fil σ τ =
      subst ⟨_⟩ (sym (pair-value fil (fst σ) (fst τ) (fst σ)))
        ∣ inl (E.≈-refl (fst σ)) ∣₁
    , subst ⟨_⟩ (sym (pair-value fil (fst σ) (fst τ) (fst τ)))
        ∣ inr (E.≈-refl (fst τ)) ∣₁
    , λ ρ hρ → subst ⟨_⟩ (pair-value fil (fst σ) (fst τ) (fst ρ)) hρ

  private
    module CO = K7.CardinalOrder Ground.PS.𝒮ᴾ[ G ]
    module Order = CO.Order (Ground.PS.P.Ext.extensional G)
      (λ σ τ ρ e → ⇔toPath (E.∈-congˡ e) (E.∈-congˡ (E.≈-sym e)))
      (λ σ τ ρ e → ⇔toPath (E.∈-congʳ e) (E.∈-congʳ (E.≈-sym e)))

  isKPair : (fil : Ground.P.isFilter G) (σ τ : K.Name)
          → ⟨ CB.isKPair (orderedNm σ τ) σ τ ⟩
  isKPair fil σ τ ρ = forward , backward
    where
    forward : ⟨ fst ρ E.∈[G] fst (orderedNm σ τ) ⟩
            → ⟨ CB.isSingleton ρ σ ⊔ CB.isPair ρ σ τ ⟩
    forward hρ = PT.map
      (λ { (inl rs) → inl (Order.sgl-cong ρ (singleNm σ) σ rs
                              (single-isSingleton fil σ))
         ; (inr rp) → inr (Order.pr-cong ρ (pairNm σ τ) σ τ rp
                              (pair-isPair fil σ τ)) })
      (subst ⟨_⟩ (pair-value fil (singleCode (fst σ))
        (pairCode (fst σ) (fst τ)) (fst ρ)) hρ)

    backward : ⟨ CB.isSingleton ρ σ ⊔ CB.isPair ρ σ τ ⟩
             → ⟨ fst ρ E.∈[G] fst (orderedNm σ τ) ⟩
    backward h = subst ⟨_⟩ (sym (pair-value fil (singleCode (fst σ))
      (pairCode (fst σ) (fst τ)) (fst ρ)))
      (PT.map
        (λ { (inl hs) → inl (Order.sgl-unique ρ (singleNm σ) σ hs
                                (single-isSingleton fil σ))
           ; (inr hp) → inr (Order.pr-unique ρ (pairNm σ τ) σ τ hp
                                (pair-isPair fil σ τ)) }) h)

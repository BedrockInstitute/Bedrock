{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module K10.CardinalContradiction {ℓ}
  (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
import OrdinaryProfile
import CardinalBridge
import CHSentence
import K7.CardinalOrder

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module OP = OrdinaryProfile 𝒮
module CB = CardinalBridge 𝒮
module CH = CHSentence 𝒮
module CO = K7.CardinalOrder 𝒮

module Kernel
  (ext       : OP.Extensionality)
  (mem-congˡ : (x y z : S) → ⟨ x ≈ˢ y ⟩ → (x ∈ˢ z) ≡ (y ∈ˢ z))
  (mem-congʳ : (x y z : S) → ⟨ y ≈ˢ z ⟩ → (x ∈ˢ y) ≡ (x ∈ˢ z))
  (sep       : OP.Separation)
  (coll      : OP.Collection)
  (pair      : OP.Pairing)
  (w p d k   : S)
  (hw        : ⟨ CB.isOmega w ⟩)
  (hp        : ⟨ CB.isPowerSet p w ⟩)
  (hd        : ⟨ CB.isSuccCardinal d w ⟩)
  (hk        : ⟨ CB.isCardinal k ⟩)
  (hwd       : ⟨ w ∈ˢ d ⟩)
  (hdk       : ⟨ d ∈ˢ k ⟩)
  (hkp       : ⟨ CB.injectable k p ⟩)
  where

  module O = CO.Order ext mem-congˡ mem-congʳ

  d-cardinal : ⟨ CB.isCardinal d ⟩
  d-cardinal = hd .fst

  d-transitive : ⟨ CB.isTransitiveSet d ⟩
  d-transitive = d-cardinal .fst .fst

  k-transitive : ⟨ CB.isTransitiveSet k ⟩
  k-transitive = hk .fst .fst

  w-subset-d : ⟨ CB.isSubset w d ⟩
  w-subset-d x hx = d-transitive w hwd x hx

  d-subset-k : ⟨ CB.isSubset d k ⟩
  d-subset-k x hx = k-transitive d hdk x hx

  w-injects-d : ⟨ CB.injectable w d ⟩
  w-injects-d = O.injectable-incl sep coll pair w d w-subset-d

  d-injects-k : ⟨ CB.injectable d k ⟩
  d-injects-k = O.injectable-incl sep coll pair d k d-subset-k

  d-injects-p : ⟨ CB.injectable d p ⟩
  d-injects-p =
    O.injectable-trans sep coll pair d k p d-injects-k hkp

  d-does-not-inject-w : ⟨ CB.injectable d w ⟩ → Empty.⊥
  d-does-not-inject-w = d-cardinal .snd w hwd

  k-does-not-inject-d : ⟨ CB.injectable k d ⟩ → Empty.⊥
  k-does-not-inject-d = hk .snd d hdk

  ch-alternative :
    ⟨ CH.chValue ⟩
    → ⟨ (CB.injectable d w) ⊔ (CB.injectable p d) ⟩
  ch-alternative hch = hch w p (hw , hp) d (w-injects-d , d-injects-p)

  reject-ch-alternative :
    ⟨ CB.injectable d w ⟩ ⊎ ⟨ CB.injectable p d ⟩ → Empty.⊥
  reject-ch-alternative (inl hdw) = d-does-not-inject-w hdw
  reject-ch-alternative (inr hpd) =
    k-does-not-inject-d
      (O.injectable-trans sep coll pair k p d hkp hpd)

  noCH : ⟨ CH.chValue ⟩ → Empty.⊥
  noCH hch = PT.rec Empty.isProp⊥ reject-ch-alternative (ch-alternative hch)

  ¬CHsent-satisfaction : ⟨ [] ⊨ CH.¬CHsent ⟩
  ¬CHsent-satisfaction = subst ⟨_⟩ (sym CH.¬CH-agrees) noCH

  reject-successor-bound :
    (δ : S)
    → ⟨ CB.isSuccCardinal δ w ⟩
    → ⟨ CB.injectable k δ ⟩
    → Empty.⊥
  reject-successor-bound δ hδ hkδ =
    PT.rec Empty.isProp⊥ reject (hδ .snd .snd d (d-cardinal , hwd))
    where
      reject : ⟨ δ ≈ˢ d ⟩ ⊎ ⟨ δ ∈ˢ d ⟩ → Empty.⊥
      reject (inl e) =
        k-does-not-inject-d (O.injectable-cong-cod k δ d e hkδ)
      reject (inr hδd) =
        k-does-not-inject-d
          (O.injectable-trans sep coll pair k δ d hkδ
            (O.injectable-incl sep coll pair δ d
              (λ x hx → d-transitive δ hδd x hx)))

  reject-gchω-witness :
    Σ[ δ ∈ S ]
      (⟨ CB.isSuccCardinal δ w ⟩
      × (⟨ CB.injectable p δ ⟩ × ⟨ CB.injectable δ p ⟩))
    → Empty.⊥
  reject-gchω-witness (δ , hδ , hpδ , _) =
    reject-successor-bound δ hδ
      (O.injectable-trans sep coll pair k p δ hkp hpδ)

  noGCHω : ⟨ CH.gchωValue ⟩ → Empty.⊥
  noGCHω hgch =
    PT.rec Empty.isProp⊥ reject-gchω-witness (hgch w p (hw , hp))

  GCHωsent-refutation : ⟨ [] ⊨ CH.GCHωsent ⟩ → Empty.⊥
  GCHωsent-refutation h = noGCHω (subst ⟨_⟩ CH.GCHω-agrees h)

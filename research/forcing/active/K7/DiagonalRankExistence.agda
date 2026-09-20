{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import CardinalBridge
import K8.OmegaSuccessor

module K7.DiagonalRankExistence
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮) (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮) (sep : OrdinaryProfile.Separation 𝒮)
  (coll : OrdinaryProfile.Collection 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (seed : ZFStructure.S 𝒮) (lem : LEM ℓ)
  (w : ZFStructure.S 𝒮) (hw : ⟨ CardinalBridge.isOmega 𝒮 w ⟩)
  (d : ZFStructure.S 𝒮) (od : ⟨ CardinalBridge.isOrdinal 𝒮 d ⟩)
  (successor-closed : (a : ZFStructure.S 𝒮) → ⟨ ZFStructure._∈ˢ_ 𝒮 a d ⟩
    → ⟨ ZFStructure._∈ˢ_ 𝒮
      (K8.OmegaSuccessor.successor 𝒮 ext paths pair un pow sep find seed a) d ⟩)
  (members-countable : (a : ZFStructure.S 𝒮) → ⟨ ZFStructure._∈ˢ_ 𝒮 a d ⟩
    → ⟨ CardinalBridge.injectable 𝒮 a w ⟩)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ∃̇_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sum using ( inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
import K7.DiagonalOrderType
import K7.DiagonalMinimum
import K7.OrderTypeRestriction
import K7.OrderTypeUniqueness
import K7.OrdinalDiagonal
import K7.CardinalOrder
import K8.FinitePigeonhole

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )
open PT using ( ∣_∣₁ )

module Cardinal = CardinalBridge 𝒮
module Types = K7.DiagonalOrderType 𝒮 ext paths pair un pow sep coll find seed lem w hw
  d od successor-closed members-countable
  using ( relation; relation-reading; Rank; rankFormula; rank-reading; rank-unique
        ; rank-from-existence; hasOrderType; collect-ranks )
module Diagonal = K7.OrdinalDiagonal.AtOrdinal
  𝒮 ext paths pair un pow sep coll find seed lem w hw d od successor-closed members-countable
  using ( P; initial; initial-spec; lt; trichotomy; transitive )
module Uniqueness = K7.OrderTypeUniqueness 𝒮 ext paths find
  using ( Ref; isOrderIso; ≈→≡; ref-range; Onto; Preserves; order-isomorphism )
module Product = K8.FinitePigeonhole 𝒮 ext paths pair un pow sep coll find seed
  using ( module Graph )
module Order = K7.CardinalOrder.Order 𝒮 ext
  (λ x y z e → cong (λ t → t ∈ˢ z) (subst ⟨_⟩ (paths x y) e))
  (λ x y z e → cong (x ∈ˢ_) (subst ⟨_⟩ (paths y z) e))
  using ( no-self; ord-compare )
module Restriction = K7.OrderTypeRestriction 𝒮 ext paths pair un pow sep coll find seed
  using ( predecessors; predecessors-reading; proper-initial-comparison )
module Minimum = K7.DiagonalMinimum 𝒮 ext paths pair un pow sep coll find seed lem w hw
  d od successor-closed members-countable using ( induction )
module Swap = OrdinaryProfile.Swap 𝒮
open Types using ( Rank; relation )
open Uniqueness using ( Ref; isOrderIso; ≈→≡ )

opaque
  rankFormula : Formula S 2
  rankFormula = Types.rankFormula

  rank-reading : (a q : S) → ((a ∷ q ∷ []) ⊨ rankFormula) ≡ Rank a q
  rank-reading = Types.rank-reading

initial-in : (x p : S) → ⟨ x ∈ˢ Diagonal.P ⟩ → ⟨ Diagonal.lt x p ⟩
  → ⟨ x ∈ˢ Diagonal.initial p ⟩
initial-in x p hx h = subst ⟨_⟩ (sym (Diagonal.initial-spec p x)) (hx , h)

initial-out : (x p : S) → ⟨ x ∈ˢ Diagonal.initial p ⟩
  → ⟨ (x ∈ˢ Diagonal.P) ⊓ Diagonal.lt x p ⟩
initial-out x p = subst ⟨_⟩ (Diagonal.initial-spec p x)

predecessors-equal : (q z : S) → ⟨ q ∈ˢ Diagonal.P ⟩ → ⟨ z ∈ˢ Diagonal.P ⟩
  → ⟨ Diagonal.lt q z ⟩
  → Restriction.predecessors (Diagonal.initial z) relation q ≡ Diagonal.initial q
predecessors-equal q z hq hz qz = ≈→≡ _ _ (ext _ _ (λ x → forward x , backward x))
  where
  forward : (x : S) → ⟨ x ∈ˢ Restriction.predecessors (Diagonal.initial z) relation q ⟩
    → ⟨ x ∈ˢ Diagonal.initial q ⟩
  forward x h = initial-in x q (r .fst) (r .snd .snd)
    where
    r : ⟨ (x ∈ˢ Diagonal.P) ⊓ ((q ∈ˢ Diagonal.P) ⊓ Diagonal.lt x q) ⟩
    r = subst ⟨_⟩ (Types.relation-reading x q)
      (subst ⟨_⟩ (Restriction.predecessors-reading (Diagonal.initial z) relation q x) h .snd)
  backward : (x : S) → ⟨ x ∈ˢ Diagonal.initial q ⟩
    → ⟨ x ∈ˢ Restriction.predecessors (Diagonal.initial z) relation q ⟩
  backward x h = subst ⟨_⟩
    (sym (Restriction.predecessors-reading (Diagonal.initial z) relation q x))
    (initial-in x z (s .fst) (Diagonal.transitive x q z (s .fst) hq hz (s .snd) qz) ,
      subst ⟨_⟩ (sym (Types.relation-reading x q)) (s .fst , hq , s .snd))
    where
    s : ⟨ (x ∈ˢ Diagonal.P) ⊓ Diagonal.lt x q ⟩
    s = initial-out x q h

rank-ordinal : (a q : S) → ⟨ Rank a q ⟩ → ⟨ Cardinal.isOrdinal a ⟩
rank-ordinal a q h = PT.rec (snd (Cardinal.isOrdinal a)) (λ { (f , hf) → hf .fst }) (h .snd)

rank-less : (a b q z : S) → ⟨ Rank a q ⟩ → ⟨ Rank b z ⟩
  → ⟨ Diagonal.lt q z ⟩ → ⟨ a ∈ˢ b ⟩
rank-less a b q z h k qz = PT.rec (snd (a ∈ˢ b))
  (λ { (f , hf) → PT.rec (snd (a ∈ˢ b))
    (λ { (g , hg) → Restriction.proper-initial-comparison g b (Diagonal.initial z) relation q a f
      (hg .fst) (hg .snd) (initial-in q z (h .fst) qz) (hf .fst)
      (subst (λ A → ⟨ isOrderIso f a A relation ⟩)
        (sym (predecessors-equal q z (h .fst) (k .fst) qz)) (hf .snd)) }) (k .snd) }) (h .snd)

rank-injective : (a q z : S) → ⟨ Rank a q ⟩ → ⟨ Rank a z ⟩ → ⟨ q ≈ˢ z ⟩
rank-injective a q z h k = PT.rec (snd (q ≈ˢ z))
  (λ { (inl qz) → Empty.rec (Order.no-self find a (rank-less a a q z h k qz))
     ; (inr rest) → PT.rec (snd (q ≈ˢ z))
       (λ { (inl eq) → eq
          ; (inr zq) → Empty.rec (Order.no-self find a (rank-less a a z q k h zq)) }) rest })
  (Diagonal.trichotomy q z (h .fst) (k .fst))

rank-reflect : (a b q z : S) → ⟨ Rank a q ⟩ → ⟨ Rank b z ⟩
  → ⟨ a ∈ˢ b ⟩ → ⟨ Diagonal.lt q z ⟩
rank-reflect a b q z h k ab = PT.rec (snd (Diagonal.lt q z))
  (λ { (inl qz) → qz
     ; (inr rest) → PT.rec (snd (Diagonal.lt q z))
       (λ { (inl eq) → Empty.rec (Order.no-self find a
            (subst (λ t → ⟨ a ∈ˢ t ⟩)
              (sym (Types.rank-unique a b q h
                (subst (λ t → ⟨ Rank b t ⟩) (sym (≈→≡ q z eq)) k))) ab))
          ; (inr zq) → Empty.rec (Order.no-self find a
            (rank-ordinal a q h .fst b (rank-less b a z q k h zq) a ab)) }) rest })
  (Diagonal.trichotomy q z (h .fst) (k .fst))

rank-members : (a q b : S) → ⟨ Rank a q ⟩ → ⟨ b ∈ˢ a ⟩
  → ⟨ ⋁ S (λ z → (z ∈ˢ Diagonal.initial q) ⊓ Rank b z) ⟩
rank-members a q b h hb = PT.rec (snd target)
  (λ { (f , hf) → PT.map (atValue f hf) (hf .snd .fst .snd .fst b hb) }) (h .snd)
  where
  target : Ω
  target = ⋁ S (λ z → (z ∈ˢ Diagonal.initial q) ⊓ Rank b z)
  atValue : (f : S) → ⟨ Cardinal.isOrdinal a ⊓ isOrderIso f a (Diagonal.initial q) relation ⟩
    → Σ[ z ∈ S ] ⟨ Ref f b z ⟩
    → Σ[ z ∈ S ] ⟨ (z ∈ˢ Diagonal.initial q) ⊓ Rank b z ⟩
  atValue f hf (z , fz) = z , hz , s .fst ,
    ∣ Restricted.graph , Restricted.restriction-ordinal ,
      subst (λ A → ⟨ isOrderIso Restricted.graph b A relation ⟩)
        (predecessors-equal z q (s .fst) (h .fst) (s .snd)) Restricted.restriction-isomorphism ∣₁
    where
    hz : ⟨ z ∈ˢ Diagonal.initial q ⟩
    hz = Uniqueness.ref-range f a (Diagonal.initial q) relation b z (hf .snd) fz
    s : ⟨ (z ∈ˢ Diagonal.P) ⊓ Diagonal.lt z q ⟩
    s = initial-out z q hz
    module Restricted = K7.OrderTypeRestriction.AtPreimage
      𝒮 ext paths pair un pow sep coll find seed f a (Diagonal.initial q) relation b z
      (hf .fst) (hf .snd) hb fz
      using ( graph; restriction-ordinal; restriction-isomorphism )

initial-transitive : (x q p : S) → ⟨ p ∈ˢ Diagonal.P ⟩
  → ⟨ q ∈ˢ Diagonal.initial p ⟩ → ⟨ x ∈ˢ Diagonal.initial q ⟩
  → ⟨ x ∈ˢ Diagonal.initial p ⟩
initial-transitive x q p hp hq hx = initial-in x p (sx .fst)
  (Diagonal.transitive x q p (sx .fst) (sq .fst) hp (sx .snd) (sq .snd))
  where
  sx : ⟨ (x ∈ˢ Diagonal.P) ⊓ Diagonal.lt x q ⟩
  sx = initial-out x q hx
  sq : ⟨ (q ∈ˢ Diagonal.P) ⊓ Diagonal.lt q p ⟩
  sq = initial-out q p hq

module Assemble (p B : S) (hp : ⟨ p ∈ˢ Diagonal.P ⟩)
  (exists : (q : S) → ⟨ q ∈ˢ Diagonal.initial p ⟩ → ⟨ Types.hasOrderType (Diagonal.initial q) ⟩)
  (spec : (a : S) → ⟨ OrdinaryProfile.iff 𝒮 (a ∈ˢ B)
    (⋁ S (λ q → (q ∈ˢ Diagonal.initial p) ⊓ Rank a q)) ⟩)
  where

  ordinal : ⟨ Cardinal.isOrdinal B ⟩
  ordinal = transitive , linear
    where
    transitive : (a : S) → ⟨ a ∈ˢ B ⟩ → (b : S) → ⟨ b ∈ˢ a ⟩ → ⟨ b ∈ˢ B ⟩
    transitive a ha b hb = PT.rec (snd (b ∈ˢ B))
      (λ { (q , hq , h) → spec b .snd (PT.map
        (λ { (z , hz , k) → z , initial-transitive z q p hp hq hz , k })
        (rank-members a q b h hb)) }) (spec a .fst ha)
    linear : (a : S) → ⟨ a ∈ˢ B ⟩ → (b : S) → ⟨ b ∈ˢ B ⟩
      → ⟨ (a ∈ˢ b) ⊔ ((a ≈ˢ b) ⊔ (b ∈ˢ a)) ⟩
    linear a ha b hb = PT.rec (snd target)
      (λ { (q , hq , h) → PT.rec (snd target)
        (λ { (z , hz , k) → Order.ord-compare find sep lem a b
          (rank-ordinal a q h) (rank-ordinal b z k) }) (spec b .fst hb) }) (spec a .fst ha)
      where
      target : Ω
      target = (a ∈ˢ b) ⊔ ((a ≈ˢ b) ⊔ (b ∈ˢ a))

  module Graph = Product.Graph B (Diagonal.initial p) (Swap.swapFo rankFormula)
    using ( R; graph; ref-entry; ref-in; injection )

  reading : (q a : S) → Graph.R q a ≡ Rank a q
  reading q a = Swap.⊨-swap rankFormula q a ∙ rank-reading a q

  graph : S
  graph = Graph.graph

  graph-reading : (a q : S)
    → Ref graph a q ≡ ((a ∈ˢ B) ⊓ ((q ∈ˢ Diagonal.initial p) ⊓ Rank a q))
  graph-reading a q = ⇔toPath (Graph.ref-entry a q)
    (λ h → Graph.ref-in a q (h .fst) (h .snd .fst) (h .snd .snd))
    ∙ cong ((a ∈ˢ B) ⊓_) (cong ((q ∈ˢ Diagonal.initial p) ⊓_) (reading q a))

  injection : ⟨ Cardinal.isInjection graph B (Diagonal.initial p) ⟩
  injection = Graph.injection
    (λ a ha → PT.map (λ { (q , hq , h) → q , hq , subst ⟨_⟩ (sym (reading q a)) h })
      (spec a .fst ha))
    (λ a q z h k → rank-injective a q z
      (subst ⟨_⟩ (reading q a) h) (subst ⟨_⟩ (reading z a) k))
    (λ a q b h k → subst ⟨_⟩ (sym (paths a b))
      (Types.rank-unique a b q (subst ⟨_⟩ (reading q a) h) (subst ⟨_⟩ (reading q b) k)))

  onto : ⟨ Uniqueness.Onto graph B (Diagonal.initial p) ⟩
  onto q hq = ∣ chosen .fst , spec (chosen .fst) .snd ∣ q , hq , chosen .snd ∣₁ ,
    Graph.ref-in (chosen .fst) q (spec (chosen .fst) .snd ∣ q , hq , chosen .snd ∣₁) hq
      (subst ⟨_⟩ (sym (reading q (chosen .fst))) (chosen .snd)) ∣₁
    where
    chosen : Σ[ a ∈ S ] ⟨ Rank a q ⟩
    chosen = Types.rank-from-existence q (initial-out q p hq .fst) (exists q hq)

  preserves : ⟨ Uniqueness.Preserves graph B relation ⟩
  preserves a ha b hb q z (fq , fz) =
    (λ ab → subst ⟨_⟩ (sym (Types.relation-reading q z))
      (h .fst , k .fst , rank-reflect a b q z h k ab)) ,
    (λ qz → rank-less a b q z h k (subst ⟨_⟩ (Types.relation-reading q z) qz .snd .snd))
    where
    h : ⟨ Rank a q ⟩
    h = subst ⟨_⟩ (graph-reading a q) fq .snd .snd
    k : ⟨ Rank b z ⟩
    k = subst ⟨_⟩ (graph-reading b z) fz .snd .snd

  isomorphism : ⟨ isOrderIso graph B (Diagonal.initial p) relation ⟩
  isomorphism = Uniqueness.order-isomorphism graph B (Diagonal.initial p) relation injection onto preserves

  has-order-type : ⟨ Types.hasOrderType (Diagonal.initial p) ⟩
  has-order-type = ∣ B , ∣ graph , ordinal , isomorphism ∣₁ ∣₁

initial-order-type-step : (p : S) → ⟨ p ∈ˢ Diagonal.P ⟩
  → ((q : S) → ⟨ q ∈ˢ Diagonal.initial p ⟩ → ⟨ Types.hasOrderType (Diagonal.initial q) ⟩)
  → ⟨ Types.hasOrderType (Diagonal.initial p) ⟩
initial-order-type-step p hp exists = PT.rec (snd (Types.hasOrderType (Diagonal.initial p)))
  (λ { (B , spec) → Assemble.has-order-type p B hp exists spec })
  (Types.collect-ranks (Diagonal.initial p) (λ q hq → initial-out q p hq .fst) exists)

hasRankFormula : Formula S 1
hasRankFormula = ∃̇ rankFormula

hasRank : S → Ω
hasRank p = ⋁ S (λ a → Rank a p)

hasRank-reading : (p : S) → ((p ∷ []) ⊨ hasRankFormula) ≡ hasRank p
hasRank-reading p = cong (⋁ S) (funExt (λ a → rank-reading a p))

rank-to-order-type : (p : S) → ⟨ hasRank p ⟩ → ⟨ Types.hasOrderType (Diagonal.initial p) ⟩
rank-to-order-type p = PT.map (λ { (a , h) → a , h .snd })

rank-exists : (p : S) → ⟨ p ∈ˢ Diagonal.P ⟩ → ⟨ hasRank p ⟩
rank-exists p hp = subst ⟨_⟩ (hasRank-reading p) (Minimum.induction hasRankFormula step p hp)
  where
  step : (q : S) → ⟨ q ∈ˢ Diagonal.P ⟩
    → ((z : S) → ⟨ z ∈ˢ Diagonal.P ⟩ → ⟨ Diagonal.lt z q ⟩ → ⟨ (z ∷ []) ⊨ hasRankFormula ⟩)
    → ⟨ (q ∷ []) ⊨ hasRankFormula ⟩
  step q hq ih = subst ⟨_⟩ (sym (hasRank-reading q))
    (PT.map (λ { (a , h) → a , hq , h }) (initial-order-type-step q hq predecessors))
    where
    predecessors : (z : S) → ⟨ z ∈ˢ Diagonal.initial q ⟩
      → ⟨ Types.hasOrderType (Diagonal.initial z) ⟩
    predecessors z hz = rank-to-order-type z (subst ⟨_⟩ (hasRank-reading z)
      (ih z (initial-out z q hz .fst) (initial-out z q hz .snd)))

initial-has-order-type : (p : S) → ⟨ p ∈ˢ Diagonal.P ⟩
  → ⟨ Types.hasOrderType (Diagonal.initial p) ⟩
initial-has-order-type p hp = rank-to-order-type p (rank-exists p hp)

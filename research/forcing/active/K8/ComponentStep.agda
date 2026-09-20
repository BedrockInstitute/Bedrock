{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.ComponentStep
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮)
  (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  (coll : OrdinaryProfile.Collection 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (seed : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import Base.Classical using ( LEM )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_; _∨̇_; ∀̇_; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import OrdinaryProfile 𝒮 using ( iff; ChoiceSet )
open import CodedVocabulary 𝒮 using ( subsetΔ )
open import K8.FiniteVocabulary 𝒮 using ( finiteIn )
import CardinalBridge
import K8.GroundSets
import K8.CountableStars
import K8.FiniteUnion
import K8.FiniteCountable
import K8.CountableZFC
import K8.FinitePigeonhole
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )
module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module FU = K8.FiniteUnion 𝒮 ext paths pair un pow sep seed
module FC = K8.FiniteCountable 𝒮 ext paths pair un pow sep find seed
module CZ = K8.CountableZFC 𝒮 ext paths pair un pow sep coll find seed
module FP = K8.FinitePigeonhole 𝒮 ext paths pair un pow sep coll find seed
module CB = CardinalBridge 𝒮
open CB using ( _↔̇_ )

module Family (F X : S) where
  module CS = K8.CountableStars.Family 𝒮 ext paths pair un pow sep coll find seed F X

  Y : S
  Y = GS.power F

  next : S → S
  next A = GS.join A (CS.neighborhood (FU.bigUnion A))

  Adjacent : S → S → Ω
  Adjacent A b = ⋁ S (λ a → (a ∈ˢ A) ⊓ CS.meets a b)

  union-meets : (A b : S) → CS.meets (FU.bigUnion A) b ≡ Adjacent A b
  union-meets A b = ⇔toPath
    (PT.rec (snd (Adjacent A b)) (λ { (x , hx , xb) → PT.map
      (λ { (a , ha , xa) → a , ha , ∣ x , xa , xb ∣₁ })
      (subst ⟨_⟩ (FU.bigUnion-spec A x) hx) }))
    (PT.rec (snd (CS.meets (FU.bigUnion A) b)) (λ { (a , ha , meet) → PT.map
      (λ { (x , xa , xb) → x , subst ⟨_⟩ (sym (FU.bigUnion-spec A x))
        ∣ a , ha , xa ∣₁ , xb }) meet }))

  next-spec : (A b : S)
    → (b ∈ˢ next A) ≡ ((b ∈ˢ A) ⊔ ((b ∈ˢ F) ⊓ Adjacent A b))
  next-spec A b = GS.join-spec A (CS.neighborhood (FU.bigUnion A)) b
    ∙ cong ((b ∈ˢ A) ⊔_) (CS.neighborhood-spec (FU.bigUnion A) b
      ∙ cong ((b ∈ˢ F) ⊓_) (union-meets A b))

  next-sub : (A : S) → ⟨ subsetΔ A F ⟩ → ⟨ subsetΔ (next A) F ⟩
  next-sub A sub b hb = PT.rec (snd (b ∈ˢ F))
    (λ { (inl ba) → sub b ba ; (inr (bf , _)) → bf })
    (subst ⟨_⟩ (next-spec A b) hb)

  inflationary : (A : S) → ⟨ subsetΔ A (next A) ⟩
  inflationary A b hb = subst ⟨_⟩ (sym (next-spec A b)) ∣ inl hb ∣₁

  adjacent-next : (A a b : S) → ⟨ a ∈ˢ A ⟩ → ⟨ b ∈ˢ F ⟩
    → ⟨ CS.meets a b ⟩ → ⟨ b ∈ˢ next A ⟩
  adjacent-next A a b ha hb meet = subst ⟨_⟩ (sym (next-spec A b))
    ∣ inr (hb , ∣ a , ha , meet ∣₁) ∣₁

  Closed : S → Ω
  Closed d = ⋀ S (λ a → (a ∈ˢ d) ⇒
    ⋀ S (λ b → (b ∈ˢ F) ⇒ (CS.meets a b ⇒ (b ∈ˢ d))))

  next-closed : (A d : S) → ⟨ subsetΔ A d ⟩ → ⟨ Closed d ⟩
    → ⟨ subsetΔ (next A) d ⟩
  next-closed A d sub closed b hb = PT.rec (snd (b ∈ˢ d))
    (λ { (inl ba) → sub b ba
       ; (inr (bf , reach)) → PT.rec (snd (b ∈ˢ d))
           (λ { (a , ha , meet) → closed a (sub a ha) b bf meet }) reach })
    (subst ⟨_⟩ (next-spec A b) hb)

  Next : S → S → Ω
  Next B A = ⋀ S (λ b → iff (b ∈ˢ B) ((b ∈ˢ A) ⊔ ((b ∈ˢ F) ⊓ Adjacent A b)))

  nextFormula : Formula S 2
  nextFormula = ∀̇ ((var zero ∈̇ var (suc zero)) ↔̇
    ((var zero ∈̇ var (suc (suc zero))) ∨̇ ((var zero ∈̇ con F) ∧̇
      ∃̇∈ (var (suc (suc zero))) (∃̇∈ (var zero)
        (var zero ∈̇ var (suc (suc zero)))))))

  next-reading : (B A : S) → ((B ∷ A ∷ []) ⊨ nextFormula) ≡ Next B A
  next-reading B A = refl

  next-witness : (A : S) → ⟨ Next (next A) A ⟩
  next-witness A b = subst ⟨_⟩ (next-spec A b) , subst ⟨_⟩ (sym (next-spec A b))

  next-unique : (B A : S) → ⟨ Next B A ⟩ → B ≡ next A
  next-unique B A h = GS.≈→≡ (ext B (next A) λ b →
    (λ hb → next-witness A b .snd (h b .fst hb)) ,
    (λ hb → h b .snd (next-witness A b .fst hb)))

  next-in : (A : S) → ⟨ A ∈ˢ Y ⟩ → ⟨ next A ∈ˢ Y ⟩
  next-in A ha = subst ⟨_⟩ (sym (GS.power-spec F (next A)))
    (next-sub A (subst ⟨_⟩ (GS.power-spec F A) ha))

  module Graph = FP.Graph Y Y nextFormula

  transition : S
  transition = Graph.graph

  transition-function : ⟨ CB.isFunction transition ⟩
  transition-function = Graph.relation , λ p hp q hq A B C (kp , kq) →
    subst ⟨_⟩ (sym (paths B C))
      (next-unique B A (Graph.entry p hp A B kp .snd .snd)
        ∙ sym (next-unique C A (Graph.entry q hq A C kq .snd .snd)))

  transition-total : (A : S) → ⟨ A ∈ˢ Y ⟩
    → ⟨ ⋁ S (λ B → (B ∈ˢ Y) ⊓ FP.CU.Ref transition A B) ⟩
  transition-total A ha = ∣ next A , next-in A ha ,
    Graph.ref-in A (next A) ha (next-in A ha) (next-witness A) ∣₁

  transition-next : (A B : S) → ⟨ FP.CU.Ref transition A B ⟩ → B ≡ next A
  transition-next A B h = next-unique B A (Graph.ref-entry A B h .snd .snd)

  countable-next : (lem : LEM ℓ) → ChoiceSet → (w : S) → ⟨ CB.isOmega w ⟩
    → ((a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ finiteIn X a ⟩)
    → ((x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ CB.injectable (CS.star x) w ⟩)
    → (A : S) → ⟨ subsetΔ A F ⟩ → ⟨ CB.injectable A w ⟩
    → ⟨ CB.injectable (next A) w ⟩
  countable-next lem choice w hw each stars A sub countA =
    CZω.countable-join A (CS.neighborhood (FU.bigUnion A)) countA
      (CS.neighborhood-countable choice (FU.bigUnion A) w union-sub
        (CZω.countable-bigUnion A countA
          (λ a ha → FC.finite-countable lem w hw X a (each a (sub a ha)))) stars CZω.square)
    where
    module CZω = CZ.AtOmega lem choice w hw

    union-sub : ⟨ subsetΔ (FU.bigUnion A) X ⟩
    union-sub x hx = PT.rec (snd (x ∈ˢ X))
      (λ { (a , ha , xa) → each a (sub a ha) .fst x xa })
      (subst ⟨_⟩ (FU.bigUnion-spec A x) hx)

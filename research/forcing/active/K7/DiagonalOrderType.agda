{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import CardinalBridge
import K8.OmegaSuccessor

module K7.DiagonalOrderType
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
open import FOL.Syntax using ( Formula; Term; var; con; _∈̇_; _∧̇_; _⇒̇_; ∃̇_; ∀̇_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
import CodedVocabulary
import GroundDescription
import K7.OrdinalDiagonal
import K7.OrderTypeUniqueness
import K7.OrdinalTypeBounds
import K8.FinitePigeonhole

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module CB = CardinalBridge 𝒮
module Code = CodedVocabulary 𝒮
module Swap = OrdinaryProfile.Swap 𝒮
module Uniqueness = K7.OrderTypeUniqueness 𝒮 ext paths find
module Product = K8.FinitePigeonhole 𝒮 ext paths pair un pow sep coll find seed
module Ordinal = K7.OrdinalDiagonal 𝒮 ext paths pair un pow sep coll find seed lem w hw
module Diagonal = Ordinal.AtOrdinal d od successor-closed members-countable
module Graph = Product.Graph Diagonal.P Diagonal.P (Swap.swapFo Diagonal.ltFormula)

opaque
  relation : S
  relation = Graph.graph

  relation-is-relation : ⟨ CB.isRelation relation ⟩
  relation-is-relation = Graph.relation

  relation-reading : (x y : S) → Uniqueness.Ref relation x y
    ≡ ((x ∈ˢ Diagonal.P) ⊓ ((y ∈ˢ Diagonal.P) ⊓ Diagonal.lt x y))
  relation-reading x y = ⇔toPath (Graph.ref-entry x y)
    (λ h → Graph.ref-in x y (h .fst) (h .snd .fst) (h .snd .snd))
    ∙ cong ((x ∈ˢ Diagonal.P) ⊓_) (cong ((y ∈ˢ Diagonal.P) ⊓_)
      (Swap.⊨-swap Diagonal.ltFormula y x ∙ Diagonal.lt-reading x y))

initial-relation-reading : (p x y : S)
  → ⟨ x ∈ˢ Diagonal.initial p ⟩ → ⟨ y ∈ˢ Diagonal.initial p ⟩
  → Uniqueness.Ref relation x y ≡ Diagonal.lt x y
initial-relation-reading p x y hx hy = ⇔toPath
  (λ h → subst ⟨_⟩ (relation-reading x y) h .snd .snd)
  (λ h → subst ⟨_⟩ (sym (relation-reading x y))
    (subst ⟨_⟩ (Diagonal.initial-spec p x) hx .fst ,
      subst ⟨_⟩ (Diagonal.initial-spec p y) hy .fst , h))

OrderTypeBody : S → S → S → Ω
OrderTypeBody A a f = CB.isOrdinal a ⊓ Uniqueness.isOrderIso f a A relation

pattern i0 = zero
pattern i1 = suc i0
pattern i2 = suc i1
pattern i3 = suc i2

ordinalTerms : Fin 1 → Term S 3
ordinalTerms i0 = var i1

isomorphismTerms : Fin 4 → Term S 3
isomorphismTerms i0 = var i0
isomorphismTerms i1 = var i1
isomorphismTerms i2 = var i2
isomorphismTerms i3 = con relation

orderTypeFormula : Formula S 3
orderTypeFormula = Code.instFo ordinalTerms CB.IsOrdinalφ ∧̇
  Code.instFo isomorphismTerms Uniqueness.orderIsoFormula

orderType-reading : (A a f : S)
  → ((f ∷ a ∷ A ∷ []) ⊨ orderTypeFormula) ≡ OrderTypeBody A a f
orderType-reading A a f = cong₂ _⊓_
  (Code.⊨-inst ordinalTerms CB.IsOrdinalφ (f ∷ a ∷ A ∷ []) (a ∷ []) (λ { i0 → refl })
    ∙ CB.IsOrdinal-bridge a)
  (Code.⊨-inst isomorphismTerms Uniqueness.orderIsoFormula (f ∷ a ∷ A ∷ [])
    (f ∷ a ∷ A ∷ relation ∷ []) (λ { i0 → refl; i1 → refl; i2 → refl; i3 → refl })
    ∙ Uniqueness.orderIso-reading f a A relation)

hasOrderType : S → Ω
hasOrderType A = ⋁ S (λ a → ⋁ S (λ f → OrderTypeBody A a f))

hasOrderTypeFormula : Formula S 1
hasOrderTypeFormula = ∃̇ (∃̇ orderTypeFormula)

hasOrderType-reading : (A : S) → ((A ∷ []) ⊨ hasOrderTypeFormula) ≡ hasOrderType A
hasOrderType-reading A = cong (⋁ S) (funExt (λ a → cong (⋁ S)
  (funExt (λ f → orderType-reading A a f))))

OrderType : S → Type ℓ
OrderType A = Σ[ a ∈ S ] Σ[ f ∈ S ] ⟨ OrderTypeBody A a f ⟩

ordertype-unique : (A a b f g : S)
  → ⟨ OrderTypeBody A a f ⟩ → ⟨ OrderTypeBody A b g ⟩
  → ⟨ (a ≈ˢ b) ⊓ (f ≈ˢ g) ⟩
ordertype-unique A a b f g h k = Uniqueness.order-isomorphism-unique f g a b A relation
  (h .fst) (k .fst) (h .snd) (k .snd)

ordertype-is-prop : (A : S) → isProp (OrderType A)
ordertype-is-prop A (a , f , h) (b , g , k) = Σ≡Prop fiber
  (Uniqueness.≈→≡ a b (ordertype-unique A a b f g h k .fst))
  where
  fiber : (a : S) → isProp (Σ[ f ∈ S ] ⟨ OrderTypeBody A a f ⟩)
  fiber a (f , h) (g , k) = Σ≡Prop (λ t → snd (OrderTypeBody A a t))
    (Uniqueness.≈→≡ f g (ordertype-unique A a a f g h k .snd))

ordertype-from-existence : (A : S) → ⟨ hasOrderType A ⟩ → OrderType A
ordertype-from-existence A = PT.rec (ordertype-is-prop A)
  (λ { (a , h) → PT.rec (ordertype-is-prop A) (λ { (f , k) → a , f , k }) h })

InitialOrderType : S → Type ℓ
InitialOrderType p = OrderType (Diagonal.initial p)

initial-ordertype-unique : (p a b f g : S)
  → ⟨ OrderTypeBody (Diagonal.initial p) a f ⟩
  → ⟨ OrderTypeBody (Diagonal.initial p) b g ⟩
  → ⟨ (a ≈ˢ b) ⊓ (f ≈ˢ g) ⟩
initial-ordertype-unique p = ordertype-unique (Diagonal.initial p)

initial-ordertype-is-prop : (p : S) → isProp (InitialOrderType p)
initial-ordertype-is-prop p = ordertype-is-prop (Diagonal.initial p)

initial-ordertype-from-existence : (p : S)
  → ⟨ hasOrderType (Diagonal.initial p) ⟩ → InitialOrderType p
initial-ordertype-from-existence p = ordertype-from-existence (Diagonal.initial p)

module Bounds = K7.OrdinalTypeBounds 𝒮 ext paths sep find lem

initial-ordertype-bound : (p a f : S) → ⟨ p ∈ˢ Diagonal.P ⟩
  → ⟨ CB.isCardinal d ⟩ → ⟨ w ∈ˢ d ⟩
  → ⟨ OrderTypeBody (Diagonal.initial p) a f ⟩ → ⟨ a ∈ˢ d ⟩
initial-ordertype-bound p a f hp cd wd h =
  Bounds.through-injection pair coll a (Diagonal.initial p) w d
    (h .fst) cd wd PT.∣ f , h .snd .fst ∣₁ (Diagonal.initial-countable p hp)

initial-witness-bound : (p : S) → ⟨ p ∈ˢ Diagonal.P ⟩
  → ⟨ CB.isCardinal d ⟩ → ⟨ w ∈ˢ d ⟩
  → (t : InitialOrderType p) → ⟨ fst t ∈ˢ d ⟩
initial-witness-bound p hp cd wd (a , f , h) =
  initial-ordertype-bound p a f hp cd wd h

initialFormula : Formula S 2
initialFormula = ∀̇ (((var i0 ∈̇ var i1) ⇒̇ body) ∧̇ (body ⇒̇ (var i0 ∈̇ var i1)))
  where
  body : Formula S 3
  body = (var i0 ∈̇ con Diagonal.P) ∧̇
    Code.instFo (λ { i0 → var i0 ; i1 → var i2 }) Diagonal.ltFormula

initial-reading : (I q : S)
  → ((I ∷ q ∷ []) ⊨ initialFormula) ≡ (I ≈ˢ Diagonal.initial q)
initial-reading I q = ⇔toPath forward backward
  where
  body : (z : S) → ((z ∈ˢ Diagonal.P) ⊓
    ((z ∷ I ∷ q ∷ []) ⊨ Code.instFo (λ { i0 → var i0 ; i1 → var i2 }) Diagonal.ltFormula))
    ≡ (z ∈ˢ Diagonal.initial q)
  body z = cong ((z ∈ˢ Diagonal.P) ⊓_)
    (Code.⊨-inst (λ { i0 → var i0 ; i1 → var i2 }) Diagonal.ltFormula
      (z ∷ I ∷ q ∷ []) (z ∷ q ∷ []) (λ { i0 → refl ; i1 → refl })
      ∙ Diagonal.lt-reading z q) ∙ sym (Diagonal.initial-spec q z)
  forward : ⟨ (I ∷ q ∷ []) ⊨ initialFormula ⟩ → ⟨ I ≈ˢ Diagonal.initial q ⟩
  forward h = ext I (Diagonal.initial q) (λ z →
    (λ hz → subst ⟨_⟩ (body z) (h z .fst hz)) ,
    (λ hz → h z .snd (subst ⟨_⟩ (sym (body z)) hz)))
  backward : ⟨ I ≈ˢ Diagonal.initial q ⟩ → ⟨ (I ∷ q ∷ []) ⊨ initialFormula ⟩
  backward h z = subst ⟨_⟩ (sym read) , subst ⟨_⟩ read
    where
    read = body z ∙ sym (cong (z ∈ˢ_) (Uniqueness.≈→≡ I (Diagonal.initial q) h))

rankInitialTerms : Fin 2 → Term S 3
rankInitialTerms i0 = var i0
rankInitialTerms i1 = var i2

rankTypeTerms : Fin 3 → Term S 4
rankTypeTerms i0 = var i0
rankTypeTerms i1 = var i2
rankTypeTerms i2 = var i1

rankFormula : Formula S 2
rankFormula = (var i1 ∈̇ con Diagonal.P) ∧̇ ∃̇
  (Code.instFo rankInitialTerms initialFormula ∧̇ ∃̇ Code.instFo rankTypeTerms orderTypeFormula)

Rank : S → S → Ω
Rank a q = (q ∈ˢ Diagonal.P) ⊓ ⋁ S (λ f → OrderTypeBody (Diagonal.initial q) a f)

rank-reading : (a q : S) → ((a ∷ q ∷ []) ⊨ rankFormula) ≡ Rank a q
rank-reading a q = cong ((q ∈ˢ Diagonal.P) ⊓_)
  (⇔toPath
    {P = (a ∷ q ∷ []) ⊨ ∃̇ (Code.instFo rankInitialTerms initialFormula
      ∧̇ ∃̇ Code.instFo rankTypeTerms orderTypeFormula)}
    {Q = ⋁ S (λ f → OrderTypeBody (Diagonal.initial q) a f)} forward backward)
  where
  initial-read : (I : S) → ((I ∷ a ∷ q ∷ []) ⊨ Code.instFo rankInitialTerms initialFormula)
    ≡ (I ≈ˢ Diagonal.initial q)
  initial-read I = Code.⊨-inst rankInitialTerms initialFormula
    (I ∷ a ∷ q ∷ []) (I ∷ q ∷ []) (λ { i0 → refl ; i1 → refl }) ∙ initial-reading I q
  type-read : (I f : S)
    → ((f ∷ I ∷ a ∷ q ∷ []) ⊨ Code.instFo rankTypeTerms orderTypeFormula) ≡ OrderTypeBody I a f
  type-read I f = Code.⊨-inst rankTypeTerms orderTypeFormula
    (f ∷ I ∷ a ∷ q ∷ []) (f ∷ a ∷ I ∷ [])
    (λ { i0 → refl ; i1 → refl ; i2 → refl }) ∙ orderType-reading I a f
  forward : ⟨ ⋁ S (λ I → ((I ∷ a ∷ q ∷ []) ⊨ Code.instFo rankInitialTerms initialFormula)
    ⊓ ⋁ S (λ f → (f ∷ I ∷ a ∷ q ∷ []) ⊨ Code.instFo rankTypeTerms orderTypeFormula)) ⟩
    → ⟨ ⋁ S (λ f → OrderTypeBody (Diagonal.initial q) a f) ⟩
  forward = PT.rec (snd (⋁ S (λ f → OrderTypeBody (Diagonal.initial q) a f)))
    λ { (I , hI , fs) → PT.map (λ { (f , hf) → f ,
      subst (λ A → ⟨ OrderTypeBody A a f ⟩)
        (Uniqueness.≈→≡ I (Diagonal.initial q) (subst ⟨_⟩ (initial-read I) hI))
        (subst ⟨_⟩ (type-read I f) hf) }) fs }
  backward : ⟨ ⋁ S (λ f → OrderTypeBody (Diagonal.initial q) a f) ⟩
    → ⟨ ⋁ S (λ I → ((I ∷ a ∷ q ∷ []) ⊨ Code.instFo rankInitialTerms initialFormula)
      ⊓ ⋁ S (λ f → (f ∷ I ∷ a ∷ q ∷ []) ⊨ Code.instFo rankTypeTerms orderTypeFormula)) ⟩
  backward fs = PT.∣ Diagonal.initial q ,
    subst ⟨_⟩ (sym (initial-read (Diagonal.initial q)))
      (subst ⟨_⟩ (sym (paths (Diagonal.initial q) (Diagonal.initial q))) refl) ,
    PT.map (λ { (f , hf) → f , subst ⟨_⟩ (sym (type-read (Diagonal.initial q) f)) hf }) fs ∣₁

rank-unique : (a b q : S) → ⟨ Rank a q ⟩ → ⟨ Rank b q ⟩ → a ≡ b
rank-unique a b q h k = PT.rec (isSetS a b)
  (λ { (f , hf) → PT.rec (isSetS a b) (λ { (g , hg) →
    Uniqueness.≈→≡ a b (initial-ordertype-unique q a b f g hf hg .fst) }) (k .snd) }) (h .snd)

rank-is-prop : (q : S) → isProp (Σ[ a ∈ S ] ⟨ Rank a q ⟩)
rank-is-prop q (a , h) (b , k) = Σ≡Prop (λ t → snd (Rank t q)) (rank-unique a b q h k)

rank-from-existence : (q : S) → ⟨ q ∈ˢ Diagonal.P ⟩
  → ⟨ hasOrderType (Diagonal.initial q) ⟩ → Σ[ a ∈ S ] ⟨ Rank a q ⟩
rank-from-existence q hq exists = fst t , hq , PT.∣ fst (snd t) , snd (snd t) ∣₁
  where
  t : InitialOrderType q
  t = initial-ordertype-from-existence q exists

module Description = GroundDescription 𝒮 ext paths using ( hasImage′ )

collect-ranks : (A : S) → ⟨ CB.isSubset A Diagonal.P ⟩
  → ((q : S) → ⟨ q ∈ˢ A ⟩ → ⟨ hasOrderType (Diagonal.initial q) ⟩)
  → ⟨ ⋁ S (λ B → ⋀ S (λ a → OrdinaryProfile.iff 𝒮 (a ∈ˢ B)
      (⋁ S (λ q → (q ∈ˢ A) ⊓ Rank a q)))) ⟩
collect-ranks A sub exists = PT.map (λ { (B , spec) → B , λ a →
  (λ ha → PT.map (λ { (q , hq , sat) → q , hq , subst ⟨_⟩ (rank-reading a q) sat })
    (spec a .fst ha)) ,
  (λ h → spec a .snd (PT.map (λ { (q , hq , r) →
    q , hq , subst ⟨_⟩ (sym (rank-reading a q)) r }) h)) })
  (Description.hasImage′ sep coll A rankFormula fiber)
  where
  fiber : (q : S) → ⟨ q ∈ˢ A ⟩ → isContr (Σ[ a ∈ S ] ⟨ (a ∷ q ∷ []) ⊨ rankFormula ⟩)
  fiber q hq = center , λ { (a , sat) → Σ≡Prop (λ t → snd ((t ∷ q ∷ []) ⊨ rankFormula))
    (rank-unique (fst chosen) a q (snd chosen) (subst ⟨_⟩ (rank-reading a q) sat)) }
    where
    chosen = rank-from-existence q (sub q hq) (exists q hq)
    center : Σ[ a ∈ S ] ⟨ (a ∷ q ∷ []) ⊨ rankFormula ⟩
    center = fst chosen , subst ⟨_⟩ (sym (rank-reading (fst chosen) q)) (snd chosen)

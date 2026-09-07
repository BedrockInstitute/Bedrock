# The square law at the L-cardinals, internally

<!--en-->
Measured: this master checks in about 14 s at 1.5 GB peak (2026-09-05,
`GHCRTS="-A64m -I0 -M8g"`).  The 290 s of the previous measurement sat in
`Step.col-fin`'s where-bound `h-inj`; the cure (O3 bisect) was the sealed
`pair≡`/`h`/`h-fst`/`h-snd` blocks and the standalone `step-e1`/`step-e2`/
`step-inj` lemmas below, replacing `cong₂ _,_` at the concrete `Pair`.
<!--zh-->
测量：本主文件检查约 14 s，峰值 1.5 GB (2026-09-05，`GHCRTS="-A64m -I0 -M8g"`)。上次测量的 290 s 全部花在 `Step.col-fin`的 where 绑定 `h-inj` 上；治疗 (O3 二分) 是封印的 `pair≡`/`h`/`h-fst`/
`h-snd` 块与独立的 `step-e1`/`step-e2`/`step-inj` 引理，取代了在具体`Pair` 上的 `cong₂ _,_`。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.Pairing {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; ¬̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; regularityV; ∈-irrefl )
open import L.Choice.Stage {ℓ} lem using ( ord-suc-inj )
open import V.Model {ℓ} using ( ∈sucV-elim; ∈sucV-inl; self∈sucV )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset→isL )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; ω-ord; #∈ω; ω-mem-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
import L.Ordinal.SquareLaw {ℓ} lem as SQ
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( lt; eq; gt ) renaming ( Tri to TriW )
open import L.Axioms.Basic {ℓ} using ( ∅ʟ )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Axioms.Numerals {ℓ} using ( sucʟ; sucʟ-fst )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; prʟ; prʟ-fst; svAt; svAt-out; domAt; sucAtL; sucAtL-adequate )
open import L.Coding.Injection {ℓ} lem using ( injAt; module Extract; module Small )
open import L.Cardinal {ℓ} lem using ( InjCode; IsCardinalL; _↪_ )
open import L.GCH {ℓ} lem using ( InjL )
open import L.GCH.Assembly {ℓ} lem using ( inclusion-coded; injl-trans )
open import L.GCH.CardOf {ℓ} lem using ( cardOf )
open import L.GCH.Definable {ℓ} lem using ( DefinableMap; module Inj )
open import L.GCH.OrderType {ℓ} lem using ( Holds; module Code )
open import L.InjChain {ℓ} lem
  using ( appC; appC-adequate; ω-limit; finite-excl-ω )

open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Foundations.HLevels
  using ( isProp×; isSetΣSndProp )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )
import Cubical.Induction.WellFounded as WF
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
```

The V-carrier: the ambient membership lives here.

```agda
module SV = hPropStructure 𝒮ᵥ using ()
```

The L-carrier: `InjL` and `IsCardinalL` live here.

```agda
module SL = hPropStructure 𝒮ʟ using (S; _∈ˢ_)
open SL using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using (_^_; _⊨ᵐ_)
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

isSetS : isSet S
isSetS = isSetΣSndProp setIsSet (λ v → snd (isL v))
```

The pair path, sealed: `cong₂ _,_` at the concrete `Pair` made the
enclosing lemma dominate the whole check (measured in the O3 bisect).

```agda
opaque
  pair≡ : {A : Type ℓ} {B : Type ℓ} {a a' : A} {b b' : B}
        → a ≡ a' → b ≡ b' → (a , b) ≡ (a' , b')
  pair≡ e1 e2 = λ i → e1 i , e2 i
```

An ordinal is an element of L.  Sealed: a proof of a proposition.

```agda
opaque
  isL-ord : (x : V ℓ) → IsOrd x → ⟨ isL x ⟩
  isL-ord x ox = Lset→isL (sucV x) (suc-ord ox) x (ord∈Lset-suc x ox)

ordL : (x : V ℓ) → IsOrd x → S
ordL x ox = x , isL-ord x ox
```

Section 1. The product, as a set of L.

`prodL K` is the set of the ordered pairs of two members of `K`. It is carved by
separation out of the stage `PairBound` names, with the one-place description
"`e` is the pair of a member and a member". Inside the two bounded binders: `b`
is 0, `a` is 1, `e` is 2.

The shared bounded-relation construction is imported from `L.InjChain`.

```agda
open import L.InjChain {ℓ} lem public using ( module Relation )
```

The product specializes the relation to membership of both components.

```agda
private
  module Product (K : S) = Relation K K
    ((var (suc zero) ∈̇ con K) ∧̇ (var zero ∈̇ con K))
    (λ x y → (fst x ∈ˢ fst K) ⊓ (fst y ∈ˢ fst K))
    (λ x y e h → h) (λ x y e h → h)

prodL : S → S
prodL = Product.rel

InProd : S → V ℓ → Type (ℓ-suc ℓ)
InProd K e = ∥ Σ[ a ∈ S ] Σ[ b ∈ S ]
               (⟨ fst a ∈ˢ fst K ⟩ × ⟨ fst b ∈ˢ fst K ⟩
                × (e ≡ pr (fst a) (fst b))) ∥₁

prodL-in : (K a b : S) → ⟨ fst a ∈ˢ fst K ⟩ → ⟨ fst b ∈ˢ fst K ⟩
         → ⟨ pr (fst a) (fst b) ∈ˢ fst (prodL K) ⟩
prodL-in K a b ma mb = Product.into K a b ma mb (ma , mb)

prodL-out : (K e : S) → ⟨ fst e ∈ˢ fst (prodL K) ⟩ → InProd K (fst e)
prodL-out K e h = PT.map (λ { (a , b , q , ma , mb) → a , b , ma , mb , q }) (Product.out K e h)
```

The pair of two members, as an element of the product, and its components read
back. The components are unique, so the reading is untruncated when it lands in
the presentation of `K`.

```agda
prodL-fst : (K e : S) → ⟨ fst e ∈ˢ fst (prodL K) ⟩
          → Σ[ a ∈ ⟪ fst K ⟫ ] Σ[ b ∈ ⟪ fst K ⟫ ]
              (fst e ≡ pr (⟪ fst K ⟫↪ a) (⟪ fst K ⟫↪ b))
prodL-fst K e h = PT.rec isPropFib
  (λ { (a , b , ma , mb , q) →
     fiber (fst K) ma .fst , fiber (fst K) mb .fst
     , q ∙ cong₂ pr (sym (fiber (fst K) ma .snd)) (sym (fiber (fst K) mb .snd)) })
  (prodL-out K e h)
  where
  inner : (a : ⟪ fst K ⟫)
        → isProp (Σ[ b ∈ ⟪ fst K ⟫ ] (fst e ≡ pr (⟪ fst K ⟫↪ a) (⟪ fst K ⟫↪ b)))
  inner a (b , q) (b' , q') = Σ≡Prop (λ _ → setIsSet _ _)
    (↪-inj {a = fst K} (pr-inj (sym q ∙ q') .snd))
  isPropFib : isProp (Σ[ a ∈ ⟪ fst K ⟫ ] Σ[ b ∈ ⟪ fst K ⟫ ]
                        (fst e ≡ pr (⟪ fst K ⟫↪ a) (⟪ fst K ⟫↪ b)))
  isPropFib (a , b , q) (a' , b' , q') = Σ≡Prop inner
    (↪-inj {a = fst K} (pr-inj (sym q ∙ q') .fst))
```

<!--en-->
## The Gödel order, as a formula
<!--zh-->
## 作为公式的 Gödel 序
<!--/-->

Section 2. The Gödel order on pairs, in the object language.

`(a, b)` is below `(c, d)` when `max(a, b) ∈ max(c, d)`, or the two maxima agree
and `(a, b)` is lexicographically below `(c, d)`. The maximum of two ordinals is
"`b` if `a ∈ b`, else `a`", which is exactly the host `maxOrd` of
src/L/Ordinal/SquareLaw.lagda.md:200. Every connective below reads
definitionally; only the pair atoms are transported along `prAtL-adequate`.

```agda
MaxIs : S → S → S → Type (ℓ-suc ℓ)
MaxIs m a b =
  ∥ (⟨ fst a ∈ˢ fst b ⟩ × (fst m ≡ fst b))
  ⊎ ((⟨ fst a ∈ˢ fst b ⟩ → Empty.⊥) × (fst m ≡ fst a)) ∥₁

OrdIs : S → S → S → S → S → S → Type (ℓ-suc ℓ)
OrdIs m n a b c d =
  ∥ ⟨ fst m ∈ˢ fst n ⟩
  ⊎ ((fst m ≡ fst n)
     × ∥ ⟨ fst a ∈ˢ fst c ⟩ ⊎ ((fst a ≡ fst c) × ⟨ fst b ∈ˢ fst d ⟩) ∥₁) ∥₁

maxAt : ∀ {k} → Fin k → Fin k → Fin k → Formula S k
maxAt m a b = ((var a ∈̇ var b) ∧̇ (var m ≐ var b))
            ∨̇ ((¬̇ (var a ∈̇ var b)) ∧̇ (var m ≐ var a))

ordAt : ∀ {k} → Fin k → Fin k → Fin k → Fin k → Fin k → Fin k → Formula S k
ordAt m n a b c d =
    (var m ∈̇ var n)
  ∨̇ ((var m ≐ var n)
     ∧̇ ((var a ∈̇ var c) ∨̇ ((var a ≐ var c) ∧̇ (var b ∈̇ var d))))
```

Both readings are definitional.

```agda

```

"`p` is below `q`": the host reading, with the six witnesses.

```agda
Lt : V ℓ → V ℓ → Type (ℓ-suc ℓ)
Lt p q = ∥ Σ[ a ∈ S ] Σ[ b ∈ S ] Σ[ c ∈ S ] Σ[ d ∈ S ] Σ[ m ∈ S ] Σ[ n ∈ S ]
           ( (p ≡ pr (fst a) (fst b)) × (q ≡ pr (fst c) (fst d))
           × MaxIs m a b × MaxIs n c d × OrdIs m n a b c d ) ∥₁

private
  ↑6 : ∀ {k} → Fin k → Fin (suc (suc (suc (suc (suc (suc k))))))
  ↑6 i = suc (suc (suc (suc (suc (suc i)))))

  i0 : ∀ {k} → Fin (suc k)
  i0 = zero
  i1 : ∀ {k} → Fin (suc (suc k))
  i1 = suc zero
  i2 : ∀ {k} → Fin (suc (suc (suc k)))
  i2 = suc (suc zero)
  i3 : ∀ {k} → Fin (suc (suc (suc (suc k))))
  i3 = suc (suc (suc zero))
  i4 : ∀ {k} → Fin (suc (suc (suc (suc (suc k)))))
  i4 = suc (suc (suc (suc zero)))
  i5 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc k))))))
  i5 = suc (suc (suc (suc (suc zero))))
```

Six binders: `a` is 5, `b` is 4, `c` is 3, `d` is 2, `m` is 1, `n` is 0.

```agda
opaque
  ltAt : ∀ {k} → Fin k → Fin k → Formula S k
  ltAt p q = ∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (
        prAtL (↑6 p) i5 i4
     ∧̇ (prAtL (↑6 q) i3 i2
     ∧̇ (maxAt i1 i5 i4
     ∧̇ (maxAt i0 i3 i2
     ∧̇ ordAt i1 i0 i5 i4 i3 i2)))))))))

  private
    env : ∀ {k} → S ^ k → S → S → S → S → S → S
        → S ^ (suc (suc (suc (suc (suc (suc k))))))
    env γ a b c d m n = n ∷ m ∷ d ∷ c ∷ b ∷ a ∷ γ

    atP : ∀ {k} (p : Fin k) (γ : S ^ k) (a b c d m n : S)
        → ⟨ env γ a b c d m n ⊨ prAtL (↑6 p) i5 i4 ⟩
        ≡ (fst (lookup p γ) ≡ pr (fst a) (fst b))
    atP p γ a b c d m n = cong ⟨_⟩ (prAtL-adequate (↑6 p) i5 i4 (env γ a b c d m n))

    atQ : ∀ {k} (q : Fin k) (γ : S ^ k) (a b c d m n : S)
        → ⟨ env γ a b c d m n ⊨ prAtL (↑6 q) i3 i2 ⟩
        ≡ (fst (lookup q γ) ≡ pr (fst c) (fst d))
    atQ q γ a b c d m n = cong ⟨_⟩ (prAtL-adequate (↑6 q) i3 i2 (env γ a b c d m n))

  lt-out : ∀ {k} (p q : Fin k) (γ : S ^ k) → ⟨ γ ⊨ ltAt p q ⟩
         → Lt (fst (lookup p γ)) (fst (lookup q γ))
  lt-out p q γ = PT.rec squash₁ (λ { (a , ha) → PT.rec squash₁ (λ { (b , hb) →
    PT.rec squash₁ (λ { (c , hc) → PT.rec squash₁ (λ { (d , hd) →
    PT.rec squash₁ (λ { (m , hm) → PT.rec squash₁ (λ { (n , (hp , (hq , (hM , (hN , hO))))) →
      ∣ a , b , c , d , m , n
      , ( transport (atP p γ a b c d m n) hp
        , transport (atQ q γ a b c d m n) hq
        , PT.map (λ { (inl h) → inl h
                    ; (inr (n , e)) → inr ((λ k → lower (n k)) , e) }) hM
        , PT.map (λ { (inl h) → inl h
                    ; (inr (n , e)) → inr ((λ k → lower (n k)) , e) }) hN
        , hO ) ∣₁ }) hm }) hd }) hc }) hb }) ha })

  lt-in : ∀ {k} (p q : Fin k) (γ : S ^ k)
        → Lt (fst (lookup p γ)) (fst (lookup q γ)) → ⟨ γ ⊨ ltAt p q ⟩
  lt-in p q γ = PT.rec (snd (γ ⊨ ltAt p q))
    (λ { (a , b , c , d , m , n , (ep , eq' , hM , hN , hO)) →
      ∣ a , ∣ b , ∣ c , ∣ d , ∣ m , ∣ n
      , ( transport (sym (atP p γ a b c d m n)) ep
        , ( transport (sym (atQ q γ a b c d m n)) eq'
        , ( PT.map (λ { (inl h) → inl h
                      ; (inr (n , e)) → inr ((λ k → lift (n k)) , e) }) hM
          , ( PT.map (λ { (inl h) → inl h
                        ; (inr (n , e)) → inr ((λ k → lift (n k)) , e) }) hN
            , hO )))) ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ })
```

Section 3. The order, as a set of L.

`godel P` is the set of the pairs `(p, q)` of two members of `P` with `p` below
`q`. Inside the two bounded binders: `q` is 0, `p` is 1, `e` is 2.

```agda
private
  module Godel (P : S) = Relation P P
    ((var (suc zero) ∈̇ con P) ∧̇ ((var zero ∈̇ con P) ∧̇ ltAt (suc zero) zero))
    (λ p q → (fst p ∈ˢ fst P) ⊓ ((fst q ∈ˢ fst P) ⊓ (Lt (fst p) (fst q) , squash₁)))
    (λ p q e h → h .fst , h .snd .fst , lt-out (suc zero) zero (q ∷ p ∷ e ∷ []) (h .snd .snd))
    (λ p q e h → h .fst , h .snd .fst , lt-in (suc zero) zero (q ∷ p ∷ e ∷ []) (h .snd .snd))

godel : S → S
godel = Godel.rel

godel-in : (P p q : S) → ⟨ fst p ∈ˢ fst P ⟩ → ⟨ fst q ∈ˢ fst P ⟩
         → Lt (fst p) (fst q) → ⟨ pr (fst p) (fst q) ∈ˢ fst (godel P) ⟩
godel-in P p q mp mq l = Godel.into P p q mp mq (mp , mq , l)

godel-out : (P p q : S) → ⟨ pr (fst p) (fst q) ∈ˢ fst (godel P) ⟩
          → ⟨ fst p ∈ˢ fst P ⟩ × ⟨ fst q ∈ˢ fst P ⟩ × Lt (fst p) (fst q)
godel-out = Godel.pair-out
```

<!--en-->
## The transfer to the host order
<!--zh-->
## 到宿主序的搬运
<!--/-->

Section 4. At an ordinal `κ`, the formula reads as the host order.

The host order `SQ._≺_` on `⟪ κ ⟫ × ⟪ κ ⟫` carries well-foundedness,
transitivity and trichotomy (src/L/Ordinal/SquareLaw.lagda.md). `Lt` at two
coded pairs is that order, both ways.

```agda
module Order (κ : S) (oκ : IsOrd (fst κ)) where

  K : V ℓ
  K = fst κ

  ↑ : ⟪ K ⟫ → V ℓ
  ↑ = ⟪ K ⟫↪

  upK : ⟪ K ⟫ → S
  upK m = ↑ m , isL-trans {x = K} {y = ↑ m} (member K m) (snd κ)

  Pair : Type ℓ
  Pair = ⟪ K ⟫ × ⟪ K ⟫

  _≺₁_ : ⟪ K ⟫ → ⟪ K ⟫ → Type (ℓ-suc ℓ)
  _≺₁_ = SQ._≺₁_ K oκ

  _≺ₚ_ : Pair → Pair → Type (ℓ-suc ℓ)
  _≺ₚ_ = SQ._≺_ K oκ

  maxOrd : ⟪ K ⟫ → ⟪ K ⟫ → ⟪ K ⟫
  maxOrd = SQ.maxOrd K oκ

  ord↑ : (m : ⟪ K ⟫) → IsOrd (↑ m)
  ord↑ m = mem-ord {A = K} oκ (↑ m) (member K m)
```

The maximum, read off `MaxIs`, and written into it.

```agda
  max-out : (a b m : S) (a' b' : ⟪ K ⟫) → fst a ≡ ↑ a' → fst b ≡ ↑ b'
          → MaxIs m a b → fst m ≡ ↑ (maxOrd a' b')
  max-out a b m a' b' ea eb = PT.rec (setIsSet _ _) (go (SQ.tri₁ K oκ a' b'))
    where
    go : (t : TriW (a' ≺₁ b') (a' ≡ b') (b' ≺₁ a'))
       → (⟨ fst a ∈ˢ fst b ⟩ × (fst m ≡ fst b))
         ⊎ ((⟨ fst a ∈ˢ fst b ⟩ → Empty.⊥) × (fst m ≡ fst a))
       → fst m ≡ ↑ (SQ.maxGo K oκ a' b' t)
    go (lt h) (inl (_ , e))   = e ∙ eb
    go (lt h) (inr (na , _))  =
      Empty.rec (na (subst2 (λ x y → ⟨ x ∈ˢ y ⟩) (sym ea) (sym eb) h))
    go (eq p) (inl (a∈b , _)) =
      Empty.rec (∈-irrefl (↑ b')
        (subst2 (λ x y → ⟨ x ∈ˢ y ⟩) (ea ∙ cong ↑ p) eb a∈b))
    go (eq p) (inr (_ , e))   = e ∙ ea
    go (gt h) (inl (a∈b , _)) =
      Empty.rec (∈-irrefl (↑ a')
        (ord↑ a' .fst {x = ↑ b'} {y = ↑ a'}
          (subst2 (λ x y → ⟨ x ∈ˢ y ⟩) ea eb a∈b) h))
    go (gt h) (inr (_ , e))   = e ∙ ea

  max-in : (a' b' : ⟪ K ⟫) → MaxIs (upK (maxOrd a' b')) (upK a') (upK b')
  max-in a' b' = go (SQ.tri₁ K oκ a' b')
    where
    go : (t : TriW (a' ≺₁ b') (a' ≡ b') (b' ≺₁ a'))
       → MaxIs (upK (SQ.maxGo K oκ a' b' t)) (upK a') (upK b')
    go (lt h) = ∣ inl (h , refl) ∣₁
    go (eq p) = ∣ inr ((λ h → ∈-irrefl (↑ b') (subst (λ w → ⟨ ↑ w ∈ˢ ↑ b' ⟩) p h)) , refl) ∣₁
    go (gt h) = ∣ inr ((λ h' → ∈-irrefl (↑ a') (ord↑ a' .fst {x = ↑ b'} {y = ↑ a'} h' h)) , refl) ∣₁
```

The coded pair of a host pair.

```agda
  code : Pair → V ℓ
  code p = pr (↑ (fst p)) (↑ (snd p))
```

Downwards: `Lt` at two coded pairs refutes the failure of the host order, and
the host order is decidable.

```agda
  private
    refute : (p q : Pair) → (p ≺ₚ q → Empty.⊥)
           → Σ[ a ∈ S ] Σ[ b ∈ S ] Σ[ c ∈ S ] Σ[ d ∈ S ] Σ[ m ∈ S ] Σ[ n ∈ S ]
               ( (code p ≡ pr (fst a) (fst b)) × (code q ≡ pr (fst c) (fst d))
               × MaxIs m a b × MaxIs n c d × OrdIs m n a b c d )
           → Empty.⊥
    refute (a' , b') (c' , d') nk (a , b , c , d , m , n , (ep , eq' , hM , hN , hO)) =
      PT.rec Empty.isProp⊥ outer hO
      where
      ea : fst a ≡ ↑ a'
      ea = sym (pr-inj ep .fst)
      eb : fst b ≡ ↑ b'
      eb = sym (pr-inj ep .snd)
      ec : fst c ≡ ↑ c'
      ec = sym (pr-inj eq' .fst)
      ed : fst d ≡ ↑ d'
      ed = sym (pr-inj eq' .snd)
      em : fst m ≡ ↑ (maxOrd a' b')
      em = max-out a b m a' b' ea eb hM
      en : fst n ≡ ↑ (maxOrd c' d')
      en = max-out c d n c' d' ec ed hN

      inner : ⟨ fst a ∈ˢ fst c ⟩ ⊎ ((fst a ≡ fst c) × ⟨ fst b ∈ˢ fst d ⟩)
            → (a' ≺₁ c') ⊎ ((a' ≡ c') × (b' ≺₁ d'))
      inner (inl h)       = inl (subst2 (λ x y → ⟨ x ∈ˢ y ⟩) ea ec h)
      inner (inr (e , h)) =
        inr ( ↪-inj {a = K} (sym ea ∙ e ∙ ec)
            , subst2 (λ x y → ⟨ x ∈ˢ y ⟩) eb ed h )

      outer : ⟨ fst m ∈ˢ fst n ⟩
            ⊎ ((fst m ≡ fst n)
               × ∥ ⟨ fst a ∈ˢ fst c ⟩ ⊎ ((fst a ≡ fst c) × ⟨ fst b ∈ˢ fst d ⟩) ∥₁)
            → Empty.⊥
      outer (inl h)       = nk (inl (subst2 (λ x y → ⟨ x ∈ˢ y ⟩) em en h))
      outer (inr (e , h)) = PT.rec Empty.isProp⊥
        (λ w → nk (inr (↪-inj {a = K} (sym em ∙ e ∙ en) , inner w))) h

  lt→≺ : (p q : Pair) → Lt (code p) (code q) → p ≺ₚ q
  lt→≺ p q l = go (SQ.tri≺ K oκ p q)
    where
```

The decision `≺-dec` used to stand here; trichotomy's two off-diagonal cases
give the same refutand from `irr≺`/`trans≺`.

```agda
    refuted : ((p ≺ₚ q) → Empty.⊥) → p ≺ₚ q
    refuted nk = Empty.rec (PT.rec Empty.isProp⊥ (refute p q nk) l)

    go : TriW (p ≺ₚ q) (p ≡ q) (q ≺ₚ p) → p ≺ₚ q
    go (lt k) = k
    go (eq e) = refuted (λ k → SQ.irr≺ K oκ q (subst (λ w → w ≺ₚ q) e k))
    go (gt h) = refuted (λ k → SQ.irr≺ K oκ p (SQ.trans≺ K oκ p q p k h))

  ≺→lt : (p q : Pair) → p ≺ₚ q → Lt (code p) (code q)
  ≺→lt (a' , b') (c' , d') k =
    ∣ upK a' , upK b' , upK c' , upK d' , upK (maxOrd a' b') , upK (maxOrd c' d')
    , ( refl , refl , max-in a' b' , max-in c' d' , ord k ) ∣₁
    where
    ord : (a' , b') ≺ₚ (c' , d')
        → OrdIs (upK (maxOrd a' b')) (upK (maxOrd c' d')) (upK a') (upK b') (upK c') (upK d')
    ord (inl h)                 = ∣ inl h ∣₁
    ord (inr (e , inl h))       = ∣ inr (cong ↑ e , ∣ inl h ∣₁) ∣₁
    ord (inr (e , inr (f , h))) = ∣ inr (cong ↑ e , ∣ inr (cong ↑ f , h) ∣₁) ∣₁
```

Both components of a pair below `(c, d)` lie in the successor of `max(c, d)`.
The retired `InitialCore`, now at
archive/src-2026-09-06/L/Ordinal/SquareLawAmbient.lagda.md, had the same shape
in `fst∈sucmax` and never exported it.

```agda
  private
    ≤→≺ : (x y z : ⟪ K ⟫) → SQ._≤₁_ K oκ x y → y ≺₁ z → x ≺₁ z
    ≤→≺ x y z (inl h) h' = SQ.trans₁ K oκ x y z h h'
    ≤→≺ x y z (inr e) h' = subst (λ w → w ≺₁ z) (sym e) h'

    ≤→∈suc : (x y y' : ⟪ K ⟫) → SQ._≤₁_ K oκ x y → y ≡ y'
           → ⟨ ↑ x ∈ˢ sucV (↑ y') ⟩
    ≤→∈suc x y y' (inl h) e = ∈sucV-inl (subst (λ w → x ≺₁ w) e h)
    ≤→∈suc x y y' (inr q) e =
      subst (λ w → ⟨ ↑ w ∈ˢ sucV (↑ y') ⟩) (sym (q ∙ e)) (self∈sucV (↑ y'))

  fst∈suc : (r p : Pair) → r ≺ₚ p
          → ⟨ ↑ (fst r) ∈ˢ sucV (↑ (maxOrd (fst p) (snd p))) ⟩
  fst∈suc (a , b) (c , d) (inl h) =
    ∈sucV-inl (≤→≺ a (maxOrd a b) (maxOrd c d) (SQ.max-spec K oκ a b .fst) h)
  fst∈suc (a , b) (c , d) (inr (e , _)) =
    ≤→∈suc a (maxOrd a b) (maxOrd c d) (SQ.max-spec K oκ a b .fst) e

  snd∈suc : (r p : Pair) → r ≺ₚ p
          → ⟨ ↑ (snd r) ∈ˢ sucV (↑ (maxOrd (fst p) (snd p))) ⟩
  snd∈suc (a , b) (c , d) (inl h) =
    ∈sucV-inl (≤→≺ b (maxOrd a b) (maxOrd c d) (SQ.max-spec K oκ a b .snd) h)
  snd∈suc (a , b) (c , d) (inr (e , _)) =
    ≤→∈suc b (maxOrd a b) (maxOrd c d) (SQ.max-spec K oκ a b .snd) e
```

Section 5. The collapse, instantiated at `(prodL κ, godel (prodL κ))`.

`OrderType.Code` wants the relation well-founded, transitive and trichotomous on
the presentation of the product; all three are read off the host order through
the bijection `φ` below.

```agda
module Coll (κ : S) (oκ : IsOrd (fst κ)) where

  open Order κ oκ

  P : S
  P = prodL κ

  R : S
  R = godel P

  Rsub : (y x : S) → Holds R y x → ⟨ fst y ∈ fst P ⟩ × ⟨ fst x ∈ fst P ⟩
  Rsub y x h = godel-out P y x h .fst , godel-out P y x h .snd .fst

  module OT = Code P R Rsub using (Dom; Dom≡; isProp≺; toDom; up; up-mem; up-toDom; ↪; _≺_; ≺-in; ≺-out; module Conjuncts)
```

The host pair of a member of the product.

```agda
  φ : OT.Dom → Pair
  φ m = prodL-fst κ (OT.up m) (OT.up-mem m) .fst
      , prodL-fst κ (OT.up m) (OT.up-mem m) .snd .fst

  φ-eq : (m : OT.Dom) → OT.↪ m ≡ code (φ m)
  φ-eq m = prodL-fst κ (OT.up m) (OT.up-mem m) .snd .snd

  φ-inj : (m n : OT.Dom) → φ m ≡ φ n → m ≡ n
  φ-inj m n e = OT.Dom≡ (φ-eq m ∙ cong code e ∙ sym (φ-eq n))

  ≺-fwd : (m n : OT.Dom) → m OT.≺ n → φ m ≺ₚ φ n
  ≺-fwd m n k = lt→≺ (φ m) (φ n)
    (subst2 Lt (φ-eq m) (φ-eq n) (godel-out P (OT.up m) (OT.up n) (OT.≺-out m n k) .snd .snd))

  ≺-bwd : (m n : OT.Dom) → φ m ≺ₚ φ n → m OT.≺ n
  ≺-bwd m n k = OT.≺-in m n
    (godel-in P (OT.up m) (OT.up n) (OT.up-mem m) (OT.up-mem n)
      (subst2 Lt (sym (φ-eq m)) (sym (φ-eq n)) (≺→lt (φ m) (φ n) k)))

  wf : WellFounded OT._≺_
  wf m = go (SQ.wf≺ K oκ (φ m))
    where
    go : {n : OT.Dom} → Acc _≺ₚ_ (φ n) → Acc OT._≺_ n
    go {n} (acc r) = acc (λ n' k → go (r (φ n') (≺-fwd n' n k)))

  ≺-trans : {a b c : OT.Dom} → a OT.≺ b → b OT.≺ c → a OT.≺ c
  ≺-trans {a} {b} {c} k k' =
    ≺-bwd a c (SQ.trans≺ K oκ (φ a) (φ b) (φ c) (≺-fwd a b k) (≺-fwd b c k'))

  tri : (a b : OT.Dom) → (a OT.≺ b) ⊎ ((a ≡ b) ⊎ (b OT.≺ a))
  tri a b = go (SQ.tri≺ K oκ (φ a) (φ b))
    where
    go : TriW (φ a ≺ₚ φ b) (φ a ≡ φ b) (φ b ≺ₚ φ a)
       → (a OT.≺ b) ⊎ ((a ≡ b) ⊎ (b OT.≺ a))
    go (lt h) = inl (≺-bwd a b h)
    go (eq e) = inr (inl (φ-inj a b e))
    go (gt h) = inr (inr (≺-bwd b a h))

  module C = OT.Conjuncts wf ≺-trans using (module Inj; col; col-ord; col-out; colTable; colTable-in; colTable-pair; colʟ; otL; otL-out)
  module I = C.Inj tri using (code; col-inj; module Inverse)
```

The product injects into its order type, internally.

```agda
  injL-ot : InjL P C.otL
  injL-ot = ∣ C.colTable , I.code ∣₁
```

<!--en-->
## Three counting facts
<!--zh-->
## 三条计数事实
<!--/-->

Section 6. Three counting facts, ambient.

An inclusion of two sets, as an injection of the presentations.

```agda
incl : (a b : V ℓ) → ((z : V ℓ) → ⟨ z ∈ˢ a ⟩ → ⟨ z ∈ˢ b ⟩) → ⟪ a ⟫ ↪ ⟪ b ⟫
incl a b sub = ι , ι-inj
  where
  ι : ⟪ a ⟫ → ⟪ b ⟫
  ι m = fiber b (sub (⟪ a ⟫↪ m) (member a m)) .fst
  ι-inj : (m n : ⟪ a ⟫) → ι m ≡ ι n → m ≡ n
  ι-inj m n e = ↪-inj {a = a}
    (sym (fiber b (sub (⟪ a ⟫↪ m) (member a m)) .snd)
     ∙ cong ⟪ b ⟫↪ e
     ∙ fiber b (sub (⟪ a ⟫↪ n) (member a n)) .snd)
```

A coded injection, read back as an ambient one.  Sealed at the
definition, as `InclGraph.incl` is (src/L/InjChain.lagda.md).

```agda
opaque
  coded→ambient : (a b : S) → Σ[ F ∈ S ] InjCode F a b → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫
  coded→ambient a b (F , sv , dm , ij , ran) = Sm.small , Sm.small-inj
    where module Sm = Small F a b sv dm ij ran
```

An infinite ordinal contains `ω`.

```agda
ω⊆ : (a : V ℓ) → IsOrd a → (⟨ a ∈ˢ ω ⟩ → Empty.⊥)
   → (z : V ℓ) → ⟨ z ∈ˢ ω ⟩ → ⟨ z ∈ˢ a ⟩
ω⊆ a oa a∉ω z z∈ω = go (ord-tri a oa ω ω-ord)
  where
  go : ⟨ a ∈ˢ ω ⟩ ⊎ ((a ≡ ω) ⊎ ⟨ ω ∈ˢ a ⟩) → ⟨ z ∈ˢ a ⟩
  go (inl h)         = Empty.rec (a∉ω h)
  go (inr (inl e))   = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym e) z∈ω
  go (inr (inr ω∈a)) = oa .fst z∈ω ω∈a
```

An infinite ordinal has no coded injection into a finite one.

```agda
no-fin : (a b : S) → IsOrd (fst a) → (⟨ fst a ∈ˢ ω ⟩ → Empty.⊥)
       → IsOrd (fst b) → ⟨ fst b ∈ˢ ω ⟩ → InjL a b → Empty.⊥
no-fin a b oa a∉ω ob b∈ω = PT.rec Empty.isProp⊥ (λ c →
  finite-excl-ω (fst b) ob b∈ω (λ x → h c x , h c x)
    (λ x y e → ι .snd x y
       (coded→ambient a b c .snd (ι .fst x) (ι .fst y) (cong fst e))))
  where
  ι : ⟪ ω ⟫ ↪ ⟪ fst a ⟫
  ι = incl ω (fst a) (ω⊆ (fst a) oa a∉ω)
  h : Σ[ F ∈ S ] InjCode F a b → ⟪ ω ⟫ → ⟪ fst b ⟫
  h c x = coded→ambient a b c .fst (ι .fst x)
```

<!--en-->
## A coded injection lifts to the products
<!--zh-->
## 编码单射提升到乘积
<!--/-->

Section 7. A coded injection `F : a ↪ b` lifts to `prodL a ↪ prodL b`,
coordinatewise, as a definable map.

Over `(q ∷ p ∷ [])`, the graph says "`p` is the pair of `x` and `y`, `q` is the
pair of `x'` and `y'`, and `F` sends `x` to `x'` and `y` to `y'`". Inside the
four binders: `x` is 3, `y` is 2, `x'` is 1, `y'` is 0; `p` is 5, `q` is 4.

```agda
module ProdMap (a b F : S)
               (sv : ⟨ (F ∷ a ∷ []) ⊨ svAt zero ⟩)
               (dm : ⟨ (F ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩)
               (ij : ⟨ (F ∷ a ∷ []) ⊨ injAt zero ⟩)
               (ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩
                    → ⟨ fst y ∈ fst b ⟩) where

  module E = Extract F a sv dm using (toFun; toFun-graph; toFun-inj)

  Mem : S → Type (ℓ-suc ℓ)
  Mem p = ⟨ fst p ∈ˢ fst (prodL a) ⟩
```

The components of a member of the product, untruncated.

```agda
  Comp : S → Type (ℓ-suc ℓ)
  Comp p = Σ[ x ∈ S ] Σ[ y ∈ S ]
             (⟨ fst x ∈ˢ fst a ⟩ × ⟨ fst y ∈ˢ fst a ⟩ × (fst p ≡ pr (fst x) (fst y)))

  isPropComp : (p : S) → isProp (Comp p)
  isPropComp p (x , y , _ , _ , e) (x' , y' , _ , _ , e') =
    Σ≡Prop inner (Σ≡Prop (λ v → snd (isL v)) (pr-inj (sym e ∙ e') .fst))
    where
    inner : (x : S)
          → isProp (Σ[ y ∈ S ] (⟨ fst x ∈ˢ fst a ⟩ × ⟨ fst y ∈ˢ fst a ⟩
                                × (fst p ≡ pr (fst x) (fst y))))
    inner x (y , _ , _ , e) (y' , _ , _ , e') =
      Σ≡Prop (λ w → isProp× (snd (fst x ∈ˢ fst a))
                      (isProp× (snd (fst w ∈ˢ fst a)) (setIsSet _ _)))
        (Σ≡Prop (λ v → snd (isL v)) (pr-inj (sym e ∙ e') .snd))

  comp : (p : S) → Mem p → Comp p
  comp p mp = PT.rec (isPropComp p) (λ z → z) (prodL-out a p mp)
```

The value of `F` at a member of `a`. Sealed with its two readings: unsealed, the
read-back `Extract.toFun` exhausts an 8g heap at the first conversion (measured
at this site, 85 s to the heap limit).

```agda
  opaque
    val : (x : S) → ⟨ fst x ∈ˢ fst a ⟩ → S
    val x mx = E.toFun (x , mx)

    val-graph : (x : S) (mx : ⟨ fst x ∈ˢ fst a ⟩)
              → ⟨ pr (fst x) (fst (val x mx)) ∈ fst F ⟩
    val-graph x mx = E.toFun-graph (x , mx)

    val-inj : (x : S) (mx : ⟨ fst x ∈ˢ fst a ⟩) (x' : S) (mx' : ⟨ fst x' ∈ˢ fst a ⟩)
            → fst (val x mx) ≡ fst (val x' mx') → fst x ≡ fst x'
    val-inj x mx x' mx' = E.toFun-inj ij (x , mx) (x' , mx')

  fn : (p : S) → Mem p → S
  fn p mp = prʟ (val (comp p mp .fst) (comp p mp .snd .snd .fst))
                (val (comp p mp .snd .fst) (comp p mp .snd .snd .snd .fst))

  into : (p : S) (mp : Mem p) → ⟨ fst (fn p mp) ∈ˢ fst (prodL b) ⟩
  into p mp =
    subst (λ w → ⟨ w ∈ˢ fst (prodL b) ⟩) (sym (prʟ-fst (val x mx) (val y my)))
      (prodL-in b (val x mx) (val y my)
        (ran x (val x mx) (val-graph x mx)) (ran y (val y my) (val-graph y my)))
    where
    x = comp p mp .fst
    y = comp p mp .snd .fst
    mx = comp p mp .snd .snd .fst
    my = comp p mp .snd .snd .snd .fst

  Chain : S → S → S → S → S → S → Type (ℓ-suc ℓ)
  Chain q p x y x' y' =
      (fst p ≡ pr (fst x) (fst y)) × (fst q ≡ pr (fst x') (fst y'))
    × ⟨ pr (fst x) (fst x') ∈ fst F ⟩ × ⟨ pr (fst y) (fst y') ∈ fst F ⟩

  opaque
    mapFo : Formula S 2
    mapFo = ∃̇ (∃̇ (∃̇ (∃̇ (
          prAtL i5 i3 i2
       ∧̇ (prAtL i4 i1 i0
       ∧̇ (appC F i3 i1
       ∧̇ appC F i2 i0))))))

    private
      env₄ : S → S → S → S → S → S → S ^ 6
      env₄ q p x y x' y' = y' ∷ x' ∷ y ∷ x ∷ q ∷ p ∷ []

      at1 : (q p x y x' y' : S)
          → ⟨ env₄ q p x y x' y' ⊨ prAtL i5 i3 i2 ⟩ ≡ (fst p ≡ pr (fst x) (fst y))
      at1 q p x y x' y' = cong ⟨_⟩ (prAtL-adequate i5 i3 i2 (env₄ q p x y x' y'))

      at2 : (q p x y x' y' : S)
          → ⟨ env₄ q p x y x' y' ⊨ prAtL i4 i1 i0 ⟩ ≡ (fst q ≡ pr (fst x') (fst y'))
      at2 q p x y x' y' = cong ⟨_⟩ (prAtL-adequate i4 i1 i0 (env₄ q p x y x' y'))

      at3 : (q p x y x' y' : S)
          → ⟨ env₄ q p x y x' y' ⊨ appC F i3 i1 ⟩ ≡ ⟨ pr (fst x) (fst x') ∈ fst F ⟩
      at3 q p x y x' y' = cong ⟨_⟩ (appC-adequate F i3 i1 (env₄ q p x y x' y'))

      at4 : (q p x y x' y' : S)
          → ⟨ env₄ q p x y x' y' ⊨ appC F i2 i0 ⟩ ≡ ⟨ pr (fst y) (fst y') ∈ fst F ⟩
      at4 q p x y x' y' = cong ⟨_⟩ (appC-adequate F i2 i0 (env₄ q p x y x' y'))

    mapFo-out : (q p : S) → ⟨ (q ∷ p ∷ []) ⊨ mapFo ⟩
              → ∥ Σ[ x ∈ S ] Σ[ y ∈ S ] Σ[ x' ∈ S ] Σ[ y' ∈ S ] Chain q p x y x' y' ∥₁
    mapFo-out q p = PT.rec squash₁ (λ { (x , hx) → PT.rec squash₁ (λ { (y , hy) →
      PT.rec squash₁ (λ { (x' , hx') → PT.map (λ { (y' , (h1 , (h2 , (h3 , h4)))) →
        x , y , x' , y'
        , ( transport (at1 q p x y x' y') h1 , transport (at2 q p x y x' y') h2
          , transport (at3 q p x y x' y') h3 , transport (at4 q p x y x' y') h4 ) })
        hx' }) hy }) hx })

    mapFo-in : (q p x y x' y' : S) → Chain q p x y x' y' → ⟨ (q ∷ p ∷ []) ⊨ mapFo ⟩
    mapFo-in q p x y x' y' (h1 , h2 , h3 , h4) =
      ∣ x , ∣ y , ∣ x' , ∣ y'
      , ( transport (sym (at1 q p x y x' y')) h1
        , ( transport (sym (at2 q p x y x' y')) h2
        , ( transport (sym (at3 q p x y x' y')) h3
          , transport (sym (at4 q p x y x' y')) h4 ))) ∣₁ ∣₁ ∣₁ ∣₁

  only : (p : S) (mp : Mem p) (q : S) → ⟨ (q ∷ p ∷ []) ⊨ mapFo ⟩ → q ≡ fn p mp
  only p mp q h = PT.rec (isSetS q (fn p mp)) step (mapFo-out q p h)
    where
    x = comp p mp .fst
    y = comp p mp .snd .fst
    mx = comp p mp .snd .snd .fst
    my = comp p mp .snd .snd .snd .fst
    e = comp p mp .snd .snd .snd .snd

    step : Σ[ x₁ ∈ S ] Σ[ y₁ ∈ S ] Σ[ x₁' ∈ S ] Σ[ y₁' ∈ S ] Chain q p x₁ y₁ x₁' y₁'
         → q ≡ fn p mp
    step (x₁ , y₁ , x₁' , y₁' , (e₁ , e₂ , h3 , h4)) =
      Σ≡Prop (λ v → snd (isL v))
        (e₂ ∙ cong₂ pr ex ey ∙ sym (prʟ-fst (val x mx) (val y my)))
      where
      x₁≡x : fst x₁ ≡ fst x
      x₁≡x = pr-inj (sym e₁ ∙ e) .fst
      y₁≡y : fst y₁ ≡ fst y
      y₁≡y = pr-inj (sym e₁ ∙ e) .snd
      ex : fst x₁' ≡ fst (val x mx)
      ex = svAt-out zero (F ∷ a ∷ []) sv x x₁' (val x mx)
             (subst (λ w → ⟨ pr w (fst x₁') ∈ fst F ⟩) x₁≡x h3) (val-graph x mx)
      ey : fst y₁' ≡ fst (val y my)
      ey = svAt-out zero (F ∷ a ∷ []) sv y y₁' (val y my)
             (subst (λ w → ⟨ pr w (fst y₁') ∈ fst F ⟩) y₁≡y h4) (val-graph y my)

  M : DefinableMap
  M = record
    { dom = prodL a ; cod = prodL b ; fn = fn ; into = into ; graph = mapFo
    ; defines = λ p mp →
        mapFo-in (fn p mp) p (comp p mp .fst) (comp p mp .snd .fst)
          (val (comp p mp .fst) (comp p mp .snd .snd .fst))
          (val (comp p mp .snd .fst) (comp p mp .snd .snd .snd .fst))
          ( comp p mp .snd .snd .snd .snd
          , prʟ-fst _ _
          , val-graph (comp p mp .fst) (comp p mp .snd .snd .fst)
          , val-graph (comp p mp .snd .fst) (comp p mp .snd .snd .snd .fst) )
    ; only = only }

  inj : (p : S) (mp : Mem p) (p' : S) (mp' : Mem p')
      → fst (fn p mp) ≡ fst (fn p' mp') → fst p ≡ fst p'
  inj p mp p' mp' e = e₀ ∙ cong₂ pr ex ey ∙ sym e₀'
    where
    x = comp p mp .fst
    y = comp p mp .snd .fst
    mx = comp p mp .snd .snd .fst
    my = comp p mp .snd .snd .snd .fst
    e₀ = comp p mp .snd .snd .snd .snd
    x' = comp p' mp' .fst
    y' = comp p' mp' .snd .fst
    mx' = comp p' mp' .snd .snd .fst
    my' = comp p' mp' .snd .snd .snd .fst
    e₀' = comp p' mp' .snd .snd .snd .snd
    q : (fst (val x mx) ≡ fst (val x' mx')) × (fst (val y my) ≡ fst (val y' my'))
    q = pr-inj (sym (prʟ-fst (val x mx) (val y my)) ∙ e ∙ prʟ-fst (val x' mx') (val y' my'))
    ex : fst x ≡ fst x'
    ex = val-inj x mx x' mx' (fst q)
    ey : fst y ≡ fst y'
    ey = val-inj y my y' my' (snd q)

  injL : InjL (prodL a) (prodL b)
  injL = Inj.injL M inj

prod-inj : (a b : S) → InjL a b → InjL (prodL a) (prodL b)
prod-inj a b = PT.rec squash₁
  (λ { (F , sv , dm , ij , ran) → ProdMap.injL a b F sv dm ij ran })
```

<!--en-->
## The theorem
<!--zh-->
## 定理
<!--/-->

Section 8. The shift. At an infinite ordinal `m`, `m + 1` injects into `m`,
internally: `x ↦ x + 1` on the finite ordinals, every other member of `m` to
itself, and `m` to `∅`. A definable map, injective.

The graph, over `(y ∷ x ∷ [])`: "`x ∈ ω` and `y = x + 1`, or `x ∉ ω`, `x ∈ m`
and `y = x`, or `x = m` and `y = ∅`". The two decisions at a member, finite or
not and in `m` or the top, are taken once, by `lem`.

```agda
module Shift (mL : S) (om : IsOrd (fst mL)) (m∉ω : ⟨ fst mL ∈ˢ ω ⟩ → Empty.⊥) where

  private
    m : V ℓ
    m = fst mL

    D : S
    D = sucʟ mL

    S≡ : {x y : S} → fst x ≡ fst y → x ≡ y
    S≡ = Σ≡Prop (λ v → snd (isL v))

    ω⊆m : (z : V ℓ) → ⟨ z ∈ˢ ω ⟩ → ⟨ z ∈ˢ m ⟩
    ω⊆m = ω⊆ m om m∉ω

    Mem : S → Type (ℓ-suc ℓ)
    Mem x = ⟨ fst x ∈ˢ fst D ⟩
```

The two decisions at a member.

```agda
    Fin? : S → Type (ℓ-suc ℓ)
    Fin? x = ⟨ fst x ∈ˢ ω ⟩ ⊎ (⟨ fst x ∈ˢ ω ⟩ → Empty.⊥)

    Top? : S → Type (ℓ-suc ℓ)
    Top? x = ⟨ fst x ∈ˢ m ⟩ ⊎ (fst x ≡ m)

    fin? : (x : S) → Fin? x
    fin? x = lem (fst x ∈ˢ ω)

    top? : (x : S) → Mem x → Top? x
    top? x h = go (lem (fst x ∈ˢ m))
      where
      go : ⟨ fst x ∈ˢ m ⟩ ⊎ (⟨ fst x ∈ˢ m ⟩ → Empty.⊥) → Top? x
      go (inl k)  = inl k
      go (inr nk) = inr (∈sucV-elim {A = m} {x = fst x} (setIsSet (fst x) m)
        (subst (λ w → ⟨ fst x ∈ˢ w ⟩) (sucʟ-fst mL) h) (λ k → Empty.rec (nk k)) (λ q → q))
```

The two sides of each decision exclude each other.

```agda
    not-both : (x : S) → ⟨ fst x ∈ˢ m ⟩ → fst x ≡ m → Empty.⊥
    not-both x k q = ∈-irrefl m (subst (λ w → ⟨ w ∈ˢ m ⟩) q k)

    ω-fin : (x : S) → ⟨ fst x ∈ˢ ω ⟩ → fst x ≡ m → Empty.⊥
    ω-fin x k q = m∉ω (subst (λ w → ⟨ w ∈ˢ ω ⟩) q k)

    suc≢∅ : (a : V ℓ) → sucV a ≡ ∅ → Empty.⊥
    suc≢∅ a e = ∅-empty a
      (∈∈ₛ {a = a} {b = ∅} .fst (subst (λ w → ⟨ a ∈ˢ w ⟩) e (self∈sucV a)))

    value : (x : S) → Fin? x → Top? x → S
    value x (inl _) _       = sucʟ x
    value x (inr _) (inl _) = x
    value x (inr _) (inr _) = ∅ʟ

    value-in : (x : S) (f : Fin? x) (t : Top? x) → ⟨ fst (value x f t) ∈ˢ m ⟩
    value-in x (inl k) _ =
      subst (λ w → ⟨ w ∈ˢ m ⟩) (sym (sucʟ-fst x)) (ω⊆m (sucV (fst x)) (ω-limit (fst x) k))
    value-in x (inr _) (inl k) = k
    value-in x (inr _) (inr _) = ω⊆m ∅ (#∈ω zero)

    Wit : (y x : S) → Type (ℓ-suc ℓ)
    Wit y x = ∥ (⟨ fst x ∈ˢ ω ⟩ × (fst y ≡ sucV (fst x)))
              ⊎ ( ((⟨ fst x ∈ˢ ω ⟩ → Empty.⊥) × ⟨ fst x ∈ˢ m ⟩ × (fst y ≡ fst x))
                ⊎ ((fst x ≡ m) × (fst y ≡ ∅)) ) ∥₁

  opaque
    graph : Formula S 2
    graph = ((var (suc zero) ∈̇ con ωʟ) ∧̇ sucAtL (suc zero) zero)
          ∨̇ ( ( (¬̇ (var (suc zero) ∈̇ con ωʟ))
              ∧̇ ((var (suc zero) ∈̇ con mL) ∧̇ (var zero ≐ var (suc zero))) )
            ∨̇ ((var (suc zero) ≐ con mL) ∧̇ (var zero ≐ con ∅ʟ)) )

    private
      sa : (y x : S) → ⟨ (y ∷ x ∷ []) ⊨ sucAtL (suc zero) zero ⟩ ≡ (fst y ≡ sucV (fst x))
      sa y x = cong ⟨_⟩ (sucAtL-adequate (suc zero) zero (y ∷ x ∷ []))

    graph-out : (y x : S) → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩ → Wit y x
    graph-out y x = PT.rec squash₁
      (λ { (inl (k , e)) → ∣ inl (k , transport (sa y x) e) ∣₁
         ; (inr h) → PT.map (λ { (inl (n , (k , e))) →
                                  inr (inl ((λ hx → lower (n hx)) , k , e))
                              ; (inr (q , e)) → inr (inr (q , e)) }) h })

    in-fin : (y x : S) → ⟨ fst x ∈ˢ ω ⟩ → fst y ≡ sucV (fst x) → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩
    in-fin y x k e = ∣ inl (k , transport (sym (sa y x)) e) ∣₁

    in-mid : (y x : S) → (⟨ fst x ∈ˢ ω ⟩ → Empty.⊥) → ⟨ fst x ∈ˢ m ⟩ → fst y ≡ fst x
           → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩
    in-mid y x n k e = ∣ inr ∣ inl ((λ hx → lift (n hx)) , (k , e)) ∣₁ ∣₁

    in-top : (y x : S) → fst x ≡ m → fst y ≡ ∅ → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩
    in-top y x q e = ∣ inr ∣ inr (q , e) ∣₁ ∣₁

  private
    fn : (x : S) → Mem x → S
    fn x h = value x (fin? x) (top? x h)

    defines' : (x : S) (f : Fin? x) (t : Top? x) → ⟨ (value x f t ∷ x ∷ []) ⊨ graph ⟩
    defines' x (inl k) _       = in-fin (sucʟ x) x k (sucʟ-fst x)
    defines' x (inr n) (inl k) = in-mid x x n k refl
    defines' x (inr n) (inr q) = in-top ∅ʟ x q refl

    only' : (x : S) (f : Fin? x) (t : Top? x) (y : S)
          → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩ → y ≡ value x f t
    only' x f t y hy = PT.rec (isSetS y (value x f t)) (go f t) (graph-out y x hy)
      where
      go : (f : Fin? x) (t : Top? x)
         → (⟨ fst x ∈ˢ ω ⟩ × (fst y ≡ sucV (fst x)))
           ⊎ ( ((⟨ fst x ∈ˢ ω ⟩ → Empty.⊥) × ⟨ fst x ∈ˢ m ⟩ × (fst y ≡ fst x))
             ⊎ ((fst x ≡ m) × (fst y ≡ ∅)) )
         → y ≡ value x f t
      go (inl k) _       (inl (_ , e))             = S≡ (e ∙ sym (sucʟ-fst x))
      go (inl k) _       (inr (inl (n , _ , _)))   = Empty.rec (n k)
      go (inl k) _       (inr (inr (q , _)))       = Empty.rec (ω-fin x k q)
      go (inr n) (inl k) (inl (k' , _))            = Empty.rec (n k')
      go (inr n) (inl k) (inr (inl (_ , _ , e)))   = S≡ e
      go (inr n) (inl k) (inr (inr (q , _)))       = Empty.rec (not-both x k q)
      go (inr n) (inr q) (inl (k' , _))            = Empty.rec (n k')
      go (inr n) (inr q) (inr (inl (_ , k , _)))   = Empty.rec (not-both x k q)
      go (inr n) (inr q) (inr (inr (_ , e)))       = S≡ e

    M : DefinableMap
    M = record
      { dom = D ; cod = mL ; fn = fn
      ; into = λ x h → value-in x (fin? x) (top? x h)
      ; graph = graph
      ; defines = λ x h → defines' x (fin? x) (top? x h)
      ; only = λ x h → only' x (fin? x) (top? x h) }

    inj' : (x : S) (f : Fin? x) (t : Top? x) (x' : S) (f' : Fin? x') (t' : Top? x')
         → fst (value x f t) ≡ fst (value x' f' t') → fst x ≡ fst x'
    inj' x (inl k) _ x' (inl k') _ e =
      ord-suc-inj (fst x) (fst x') (mem-ord {A = ω} ω-ord (fst x) k)
        (sym (sucʟ-fst x) ∙ e ∙ sucʟ-fst x')
    inj' x (inl k) _ x' (inr n') (inl _) e =
      Empty.rec (n' (subst (λ w → ⟨ w ∈ˢ ω ⟩) (sym (sucʟ-fst x) ∙ e) (ω-limit (fst x) k)))
    inj' x (inl k) _ x' (inr n') (inr _) e =
      Empty.rec (suc≢∅ (fst x) (sym (sucʟ-fst x) ∙ e))
    inj' x (inr n) (inl _) x' (inl k') _ e =
      Empty.rec (n (subst (λ w → ⟨ w ∈ˢ ω ⟩) (sym (sucʟ-fst x') ∙ sym e) (ω-limit (fst x') k')))
    inj' x (inr n) (inl _) x' (inr n') (inl _) e = e
    inj' x (inr n) (inl _) x' (inr n') (inr _) e =
      Empty.rec (n (subst (λ w → ⟨ w ∈ˢ ω ⟩) (sym e) (#∈ω zero)))
    inj' x (inr n) (inr _) x' (inl k') _ e =
      Empty.rec (suc≢∅ (fst x') (sym (sucʟ-fst x') ∙ sym e))
    inj' x (inr n) (inr _) x' (inr n') (inl _) e =
      Empty.rec (n' (subst (λ w → ⟨ w ∈ˢ ω ⟩) e (#∈ω zero)))
    inj' x (inr n) (inr q) x' (inr n') (inr q') e = q ∙ sym q'
```

THE INJECTION, `m + 1 ↪ m`.

```agda
  injL : InjL (sucʟ mL) mL
  injL = Inj.injL M (λ x h x' h' → inj' x (fin? x) (top? x h) x' (fin? x') (top? x' h'))
```

Section 9. The theorem, by `∈`-induction on the L-cardinal.

At an infinite L-cardinal `κ`, every value of the collapse lies in `κ`. For a
pair `p` with maximum `m`: if `m` is finite, the segment below `p` sits inside
the square of a numeral, and an ordinal that injects into a finite set is a
numeral. If `m` is infinite, the segment sits inside `prodL (sucV m)`; the
collapse at `p` injects into it by the inverse collapse (a definable map whose
graph is the converse of `colTable`); `prodL (sucV m)` injects into `sucV m` by
the induction hypothesis at the internal cardinal of `sucV m`; and
`sucV m ∈ κ` by the coded shift. Were `col p` outside `κ`, `κ` would inject into
a member of itself.

Two members with the same fiber index are equal. Stated once at an abstract
carrier and sealed: measured at the concrete `g = sucV (mV p)` inside `col-fin`,
the same equation unfolded `⟪ g ⟫↪` and cost 282 s.

```agda
opaque
  fiber-inj : (g : V ℓ) {x y : V ℓ} (mx : ⟨ x ∈ˢ g ⟩) (my : ⟨ y ∈ˢ g ⟩)
            → fiber g mx .fst ≡ fiber g my .fst → x ≡ y
  fiber-inj g mx my e = sym (fiber g mx .snd) ∙ cong ⟪ g ⟫↪ e ∙ fiber g my .snd

Goal : V ℓ → Type (ℓ-suc ℓ)
Goal a = (la : ⟨ isL a ⟩) → IsOrd a → IsCardinalL (a , la)
       → (⟨ a ∈ˢ ω ⟩ → Empty.⊥) → InjL (prodL (a , la)) (a , la)

module Step (a : V ℓ) (ih : (a' : V ℓ) → ⟨ a' ∈ˢ a ⟩ → Goal a')
            (la : ⟨ isL a ⟩) (oa : IsOrd a) (carda : IsCardinalL (a , la))
            (a∉ω : ⟨ a ∈ˢ ω ⟩ → Empty.⊥) where

  κ : S
  κ = a , la

  open Order κ oa
  open Coll κ oa

  ω⊆a : (z : V ℓ) → ⟨ z ∈ˢ ω ⟩ → ⟨ z ∈ˢ a ⟩
  ω⊆a = ω⊆ a oa a∉ω
```

`κ` is closed under successor: the coded shift refutes `κ ≡ sucV m`.

```agda
  suc∈ : (m : V ℓ) → ⟨ m ∈ˢ a ⟩ → ⟨ sucV m ∈ˢ a ⟩
  suc∈ m m∈a = go (ord-tri (sucV m) (suc-ord om) a oa)
    where
    om : IsOrd m
    om = mem-ord {A = a} oa m m∈a
    mL : S
    mL = ordL m om

    go : ⟨ sucV m ∈ˢ a ⟩ ⊎ ((sucV m ≡ a) ⊎ ⟨ a ∈ˢ sucV m ⟩) → ⟨ sucV m ∈ˢ a ⟩
    go (inl h) = h
    go (inr (inl e)) = Empty.rec (fin (ord-tri m om ω ω-ord))
      where
      fin : ⟨ m ∈ˢ ω ⟩ ⊎ ((m ≡ ω) ⊎ ⟨ ω ∈ˢ m ⟩) → Empty.⊥
      fin (inl m∈ω) = a∉ω (subst (λ w → ⟨ w ∈ˢ ω ⟩) e (ω-limit m m∈ω))
      fin (inr r) =
        carda mL m∈a (subst (λ w → InjL w mL) sucL≡κ (Shift.injL mL om m∉ω))
        where
        m∉ω : ⟨ m ∈ˢ ω ⟩ → Empty.⊥
        m∉ω h = rr r
          where
          rr : (m ≡ ω) ⊎ ⟨ ω ∈ˢ m ⟩ → Empty.⊥
          rr (inl e') = ∈-irrefl ω (subst (λ w → ⟨ w ∈ˢ ω ⟩) e' h)
          rr (inr ω∈m) = ∈-irrefl ω (ω-ord .fst ω∈m h)
        sucL≡κ : sucʟ mL ≡ κ
        sucL≡κ = Σ≡Prop (λ v → snd (isL v)) (sucʟ-fst mL ∙ e)
    go (inr (inr h)) = Empty.rec*
      (∈sucV-elim {A = m} {x = a} {P = Empty.⊥* {ℓ-suc ℓ}} Empty.isProp⊥* h
        (λ a∈m → lift (∈-irrefl a (oa .fst a∈m m∈a)))
        (λ a≡m → lift (∈-irrefl m (subst (λ w → ⟨ m ∈ˢ w ⟩) a≡m m∈a))))
```

THE LEMMA. An infinite ordinal below `κ` pairs into itself: through its internal
cardinal `μ`, at which the induction hypothesis speaks.

```agda
  prod-into : (γ : S) → IsOrd (fst γ) → ⟨ fst γ ∈ˢ a ⟩
            → (⟨ fst γ ∈ˢ ω ⟩ → Empty.⊥) → InjL (prodL γ) γ
  prod-into γ oγ γ∈a γ∉ω = PT.rec squash₁ build (cardOf γ oγ)
    where
    build : Σ[ μ ∈ S ]
              ( IsOrd (fst μ) × IsCardinalL μ
              × ((z : V ℓ) → ⟨ z ∈ˢ fst μ ⟩ → ⟨ z ∈ˢ fst γ ⟩)
              × InjL γ μ × InjL μ γ )
          → InjL (prodL γ) γ
    build (μ , oμ , cardμ , μ⊆γ , γ↪μ , μ↪γ) =
      injl-trans (prodL γ) (prodL μ) γ (prod-inj γ μ γ↪μ)
        (injl-trans (prodL μ) μ γ (ih (fst μ) μ∈a (snd μ) oμ cardμ μ∉ω) μ↪γ)
      where
      μ∈a : ⟨ fst μ ∈ˢ a ⟩
      μ∈a = go (ord-tri (fst μ) oμ (fst γ) oγ)
        where
        go : ⟨ fst μ ∈ˢ fst γ ⟩ ⊎ ((fst μ ≡ fst γ) ⊎ ⟨ fst γ ∈ˢ fst μ ⟩) → ⟨ fst μ ∈ˢ a ⟩
        go (inl h)       = oa .fst h γ∈a
        go (inr (inl e)) = subst (λ w → ⟨ w ∈ˢ a ⟩) (sym e) γ∈a
        go (inr (inr h)) = Empty.rec (∈-irrefl (fst γ) (μ⊆γ (fst γ) h))
      μ∉ω : ⟨ fst μ ∈ˢ ω ⟩ → Empty.⊥
      μ∉ω h = no-fin γ μ oγ γ∉ω oμ h γ↪μ
```

The member below `p` whose collapse is `b`: unique, hence untruncated.

```agda
  Seg : OT.Dom → V ℓ → Type (ℓ-suc ℓ)
  Seg p b = Σ[ r ∈ OT.Dom ] ((r OT.≺ p) × (C.col r ≡ b))

  isPropSeg : (p : OT.Dom) (b : V ℓ) → isProp (Seg p b)
  isPropSeg p b (r , _ , e) (r' , _ , e') =
    Σ≡Prop (λ r → isProp× (OT.isProp≺ r p) (setIsSet _ _)) (I.col-inj r r' (e ∙ sym e'))

  seg : (p : OT.Dom) (b : V ℓ) → ⟨ b ∈ˢ C.col p ⟩ → Seg p b
  seg p b h = PT.rec (isPropSeg p b) (λ z → z) (C.col-out p b h)
```

The maximum of a member of the product.

```agda
  mx : OT.Dom → ⟪ K ⟫
  mx p = maxOrd (φ p .fst) (φ p .snd)

  mV : OT.Dom → V ℓ
  mV p = ↑ (mx p)
```

Both components of a member below `p` lie in `sucV (mV p)`. Sealed: proofs of
propositions that reach `tri≺`, hence `ord-tri`'s well-founded induction, if
ever normalised (measured at this site: unsealed, `col-fin` alone takes about
280 s).

```agda
  opaque
    seg-fst : (p r : OT.Dom) → r OT.≺ p → ⟨ ↑ (φ r .fst) ∈ˢ sucV (mV p) ⟩
    seg-fst p r k = fst∈suc (φ r) (φ p) (≺-fwd r p k)

    seg-snd : (p r : OT.Dom) → r OT.≺ p → ⟨ ↑ (φ r .snd) ∈ˢ sucV (mV p) ⟩
    seg-snd p r k = snd∈suc (φ r) (φ p) (≺-fwd r p k)
```

The finite-case carrier: the successor of the maximum below `p`.

```agda
  gfin : OT.Dom → V ℓ
  gfin p = sucV (mV p)
```

The pair of fibers at `p`, sealed, with explicit first and second projections
stated outside the where: the concrete `cong fst` on the unsealed `h` made
`h-inj` dominate the whole check.

```agda
  opaque
    h : (p r : OT.Dom) (k : r OT.≺ p) → ⟪ gfin p ⟫ × ⟪ gfin p ⟫
    h p r k = fiber (gfin p) (seg-fst p r k) .fst , fiber (gfin p) (seg-snd p r k) .fst

    h-fst : (p r r' : OT.Dom) (k : r OT.≺ p) (k' : r' OT.≺ p)
          → h p r k ≡ h p r' k'
          → fiber (gfin p) (seg-fst p r k) .fst
          ≡ fiber (gfin p) (seg-fst p r' k') .fst
    h-fst p r r' k k' e = cong fst e

    h-snd : (p r r' : OT.Dom) (k : r OT.≺ p) (k' : r' OT.≺ p)
          → h p r k ≡ h p r' k'
          → fiber (gfin p) (seg-snd p r k) .fst
          ≡ fiber (gfin p) (seg-snd p r' k') .fst
    h-snd p r r' k k' e = cong snd e
```

The fiber equations and the final injection, stated standalone with explicit
written types: where-bound, their elaboration dominated the whole check
(measured in the O3 bisect).

```agda
  step-e1 : (p r r' : OT.Dom) (k : r OT.≺ p) (k' : r' OT.≺ p)
          → h p r k ≡ h p r' k' → φ r .fst ≡ φ r' .fst
  step-e1 p r r' k k' e =
    ↪-inj {a = K} (fiber-inj (gfin p) (seg-fst p r k) (seg-fst p r' k') (h-fst p r r' k k' e))

  step-e2 : (p r r' : OT.Dom) (k : r OT.≺ p) (k' : r' OT.≺ p)
          → h p r k ≡ h p r' k' → φ r .snd ≡ φ r' .snd
  step-e2 p r r' k k' e =
    ↪-inj {a = K} (fiber-inj (gfin p) (seg-snd p r k) (seg-snd p r' k') (h-snd p r r' k k' e))

  step-inj : (p r r' : OT.Dom) (k : r OT.≺ p) (k' : r' OT.≺ p)
           → h p r k ≡ h p r' k' → r ≡ r'
  step-inj p r r' k k' e =
    φ-inj r r' (pair≡ (step-e1 p r r' k k' e) (step-e2 p r r' k k' e))
```

THE FINITE CASE. The segment below `p` injects into the square of the numeral
`sucV (mV p)`, so `ω` cannot inject into `col p`.

```agda
  col-fin : (p : OT.Dom) → ⟨ mV p ∈ˢ ω ⟩ → ⟨ C.col p ∈ˢ ω ⟩
  col-fin p m∈ω = go (ord-tri (C.col p) (C.col-ord p) ω ω-ord)
    where
    g : V ℓ
    g = sucV (mV p)
    og : IsOrd g
    og = suc-ord (ω-mem-ord (mV p) m∈ω)
    g∈ω : ⟨ g ∈ˢ ω ⟩
    g∈ω = ω-limit (mV p) m∈ω

    refute : ((z : V ℓ) → ⟨ z ∈ˢ ω ⟩ → ⟨ z ∈ˢ C.col p ⟩) → Empty.⊥
    refute sub = finite-excl-ω g og g∈ω f f-inj
      where
      s : (x : ⟪ ω ⟫) → Seg p (⟪ ω ⟫↪ x)
      s x = seg p (⟪ ω ⟫↪ x) (sub (⟪ ω ⟫↪ x) (member ω x))
      f : ⟪ ω ⟫ → ⟪ g ⟫ × ⟪ g ⟫
      f x = h p (s x .fst) (s x .snd .fst)
      f-inj : (x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y
      f-inj x y e = ↪-inj {a = ω}
        (sym (s x .snd .snd)
         ∙ cong C.col (step-inj p (s x .fst) (s y .fst) (s x .snd .fst) (s y .snd .fst) e)
         ∙ s y .snd .snd)

    go : ⟨ C.col p ∈ˢ ω ⟩ ⊎ ((C.col p ≡ ω) ⊎ ⟨ ω ∈ˢ C.col p ⟩) → ⟨ C.col p ∈ˢ ω ⟩
    go (inl k)         = k
    go (inr (inl e))   = Empty.rec (refute (λ z z∈ω → subst (λ w → ⟨ z ∈ˢ w ⟩) (sym e) z∈ω))
    go (inr (inr ω∈c)) = Empty.rec (refute (λ z z∈ω → C.col-ord p .fst z∈ω ω∈c))
```

THE INVERSE COLLAPSE below `p`, as a definable map into `prodL g`, for any `g`
holding both components of every member below `p`. Its graph is the converse of
`colTable`, read by `appC`.

```agda
  module Inv (p : OT.Dom) (g : S)
             (bfst : (r : OT.Dom) → r OT.≺ p → ⟨ ↑ (φ r .fst) ∈ˢ fst g ⟩)
             (bsnd : (r : OT.Dom) → r OT.≺ p → ⟨ ↑ (φ r .snd) ∈ˢ fst g ⟩) where

    private
      pre : (x : S) → ⟨ fst x ∈ˢ C.col p ⟩ → Σ[ r ∈ OT.Dom ] (C.col r ≡ fst x)
      pre x mx = seg p (fst x) mx .fst , seg p (fst x) mx .snd .snd

      bound : (x : S) (mx : ⟨ fst x ∈ˢ C.col p ⟩) → ⟨ OT.↪ (pre x mx .fst) ∈ˢ fst (prodL g) ⟩
      bound x mx = subst (λ w → ⟨ w ∈ˢ fst (prodL g) ⟩) (sym (φ-eq (seg p (fst x) mx .fst)))
        (prodL-in g (upK (φ (seg p (fst x) mx .fst) .fst))
                    (upK (φ (seg p (fst x) mx .fst) .snd))
                    (bfst _ (seg p (fst x) mx .snd .fst))
                    (bsnd _ (seg p (fst x) mx .snd .fst)))

    open I.Inverse (C.colʟ p) (prodL g) pre bound public
      using ( fn; graph; at; only; M; inj; injL ) renaming ( SourceMem to Mem )
```

EVERY VALUE OF THE COLLAPSE LIES IN `κ`.

```agda
  colIn : (p : OT.Dom) → ⟨ C.col p ∈ˢ a ⟩
  colIn p = go (ord-tri (mV p) (ord↑ (mx p)) ω ω-ord)
    where
    go : ⟨ mV p ∈ˢ ω ⟩ ⊎ ((mV p ≡ ω) ⊎ ⟨ ω ∈ˢ mV p ⟩) → ⟨ C.col p ∈ˢ a ⟩
    go (inl m∈ω) = ω⊆a (C.col p) (col-fin p m∈ω)
    go (inr inf) = go' (ord-tri (C.col p) (C.col-ord p) a oa)
      where
      m∉ω : ⟨ mV p ∈ˢ ω ⟩ → Empty.⊥
      m∉ω h = rr inf
        where
        rr : (mV p ≡ ω) ⊎ ⟨ ω ∈ˢ mV p ⟩ → Empty.⊥
        rr (inl e)   = ∈-irrefl ω (subst (λ w → ⟨ w ∈ˢ ω ⟩) e h)
        rr (inr ω∈m) = ∈-irrefl ω (ω-ord .fst ω∈m h)

      g : V ℓ
      g = sucV (mV p)
      og : IsOrd g
      og = suc-ord (ord↑ (mx p))
      gL : S
      gL = ordL g og
      g∈a : ⟨ g ∈ˢ a ⟩
      g∈a = suc∈ (mV p) (member K (mx p))
      g∉ω : ⟨ g ∈ˢ ω ⟩ → Empty.⊥
      g∉ω h = m∉ω (ω-ord .fst (self∈sucV (mV p)) h)

      module IV = Inv p gL (seg-fst p) (seg-snd p) using (injL)

      col↪g : InjL (C.colʟ p) gL
      col↪g = injl-trans (C.colʟ p) (prodL gL) gL IV.injL (prod-into gL og g∈a g∉ω)
```

Were `col p` not below `κ`, `κ` would inject into `g ∈ κ`.

```agda
      absurd : ((z : V ℓ) → ⟨ z ∈ˢ a ⟩ → ⟨ z ∈ˢ C.col p ⟩) → Empty.⊥
      absurd sub = carda gL g∈a
        (injl-trans κ (C.colʟ p) gL (inclusion-coded κ (C.colʟ p) sub) col↪g)

      go' : ⟨ C.col p ∈ˢ a ⟩ ⊎ ((C.col p ≡ a) ⊎ ⟨ a ∈ˢ C.col p ⟩) → ⟨ C.col p ∈ˢ a ⟩
      go' (inl h)       = h
      go' (inr (inl e)) = Empty.rec (absurd (λ z z∈a → subst (λ w → ⟨ z ∈ˢ w ⟩) (sym e) z∈a))
      go' (inr (inr h)) = Empty.rec (absurd (λ z z∈a → C.col-ord p .fst z∈a h))
```

The order type lies inside `κ`, and the product injects into it.

```agda
  result : InjL (prodL κ) κ
  result = injl-trans P C.otL κ injL-ot (inclusion-coded C.otL κ ot⊆a)
    where
    ot⊆a : (z : V ℓ) → ⟨ z ∈ˢ fst C.otL ⟩ → ⟨ z ∈ˢ a ⟩
    ot⊆a z hz = PT.rec (snd (z ∈ˢ a))
      (λ { (b , e) → subst (λ w → ⟨ w ∈ˢ a ⟩) e (colIn b) }) (C.otL-out z hz)
```

The theorem. At an L-cardinal `κ` above `ω`, the product of `κ` with itself
injects into `κ`, inside L.

```agda
square-law-L :
    (κ : S) → IsOrd (fst κ) → IsCardinalL κ → ⟨ ω ∈ˢ fst κ ⟩
  → InjL (prodL κ) κ
square-law-L κ oκ cκ ω∈κ =
  WF.WFI.induction regularityV {P = Goal} Step.result (fst κ) (snd κ) oκ cκ
    (λ κ∈ω → ∈-irrefl ω (ω-ord .fst ω∈κ κ∈ω))
```

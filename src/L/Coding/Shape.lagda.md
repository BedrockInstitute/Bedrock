# Well-formed keys

<!--en-->
The half of "is a code" that closedness does not say.

`closedAt`{.Agda} is eight implications keyed by tag: *if* a member has this tag,
*then* its parts are members too. Nothing there rules out a member with no
recognized tag at all, and such a member satisfies all eight vacuously. So a
closed set may hold junk, and the predicate that says otherwise is this one:
every member is an arity-tagged pair whose tag is one of the twelve, with a
payload of the shape that tag calls for.

The four leaf tags are delegated to a parameter. Their payloads mention term
codes and a numeral, never a formula code, so nothing about them descends and
nothing about them belongs in the same induction; they are written once,
elsewhere, and handed in.
<!--zh-->
「是一个码」中封闭性没有说出的那一半。

`closedAt`{.Agda} 是八条以标签为键的蕴含：**若**某个成员带这个标签，**则**它的诸部件也是成员。那里没有任何东西排除掉「压根没有可辨标签」的成员，而这样的成员平凡地满足全部八条。故一个封闭集可以含有垃圾，而说出相反之事的谓词就是这一条：每个成员都是一个带元数标签的对，其标签属于那十二个之一，且载荷具有该标签所要求的形状。

四个叶子标签交给一个参数。它们的载荷提到的是词项码与一个数码、从不提公式码，故它们身上没有任何东西会下降，也没有任何东西属于同一场归纳；它们在别处写一次，然后递进来。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Coding.Shape {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Term; Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; ⊤̇; ∃̇_; ∀̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_; sucV )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ}
  using ( tagAtL; tagAtL-adequate; tagBridge; module LCode
        ; closedAt; binShapeAt; unShapeAt; bothSameAt; oneSameAt
        ; oneSuccAt; succSndAt
        ; binSameClosed-out; unSameClosed-out
        ; unSuccClosed-out; binSuccClosed-out
        ; arityTagAtL; arityTagAtL-adequate
        ; arityTagPairAtL; arityTagPairAtL-adequate )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Ordinal {ℓ} using ( ∈#-elim )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.FinData.Properties using ( fromℕ'; toFromId' )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; squash₁ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## The two payload frames

<!--zh-->
## 两个载荷框架
<!--/-->

<!--en-->
A tag whose payload is a pair, and a tag whose payload is a single code. Twelve
tags, two shapes: which one a tag takes is the only thing that varies, and the
rest of what a tag demands of its payload is a relation the frame carries. That
is the same division the closedness predicate makes, and for the same reason.
<!--zh-->
一类标签的载荷是一个对，另一类的载荷是单个码。十二个标签，两种形状：标签取哪一种是唯一变动的东西，而它对载荷的其余要求，是框架所携带的一条关系。这与封闭性谓词所作的划分相同，理由也相同。
<!--/-->

```agda
module _ {n : ℕ} where
  binForm : ℕ → Formula S (4 + n) → Formula S (suc n)
  binForm k rel = ∃̇ (∃̇ (∃̇ (arityTagPairAtL
    (suc (suc (suc zero))) (suc (suc zero)) k (suc zero) zero ∧̇ rel)))

  unForm : ℕ → Formula S (3 + n) → Formula S (suc n)
  unForm k rel = ∃̇ (∃̇ (arityTagAtL (suc (suc zero)) (suc zero) k zero ∧̇ rel))
```

<!--en-->
## Term codes
<!--zh-->
## 词项码
<!--/-->

<!--en-->
The four tags whose payloads reach outside the formula codes need one predicate,
and it is not recursive: a term is a constant or a variable, and neither has a
part. A variable's index must lie below the arity, which is what makes the
formula the code of a term *at that arity* rather than at some larger one, and
that condition is bounded because the arity is a numeral.
<!--zh-->
那四个载荷伸到公式码之外的标签，需要一条谓词，而它不是递归的：词项要么是常元、要么是变元，二者都没有部件。变元的序号必须落在元数之下，正是这一点使那条公式成为**在该元数上**的词项之码、而非在某个更大的元数上，而这个条件是有界的，因为元数是一个数码。
<!--/-->

```agda
isTmAt : ∀ {n} → Fin n → Fin n → Formula S n
isTmAt t N = ∃̇ (tagAtL (suc t) 0 zero)
          ∨̇ ∃̇ (tagAtL (suc t) 1 zero ∧̇ (var zero ∈̇ var (suc N)))
```

<!--en-->
## The twelve, as one predicate
<!--zh-->
## 十二条，作为一条谓词
<!--/-->

<!--en-->
Every member is a well-formed key: an arity-tagged pair carrying one of the
twelve tags, with the payload that tag calls for. The relations say what
closedness does not: that an atom's two parts are term codes, that a bounded
quantifier's first part is one, and that a constant's payload is zero. The
formula parts are left to closedness, which is where they belong, since they are
the only parts anything descends into.
<!--zh-->
每个成员都是一个良构的键：一个带元数标签的对，携带那十二个标签之一，且载荷是该标签所要求的那种。诸关系说出封闭性没有说的事：原子的两个部件是词项码、有界量词的第一个部件是词项码、常元的载荷是零。公式部件留给封闭性，那也正是它们该在的地方，因为它们是唯一有东西会下降进去的部件。
<!--/-->

```agda
module _ {n : ℕ} where
  bothTm fstTm noneB : Formula S (4 + n)
  bothTm = isTmAt (suc zero) (suc (suc zero))
        ∧̇ isTmAt zero (suc (suc zero))
  fstTm  = isTmAt (suc zero) (suc (suc zero))
  noneB  = ⊤̇ {n = 4 + n}

  zeroPay noneU : Formula S (3 + n)
  zeroPay = var zero ≐ con (numeralL 0)
  noneU   = ⊤̇ {n = 3 + n}

  shapedAt : Fin n → Formula S n
  shapedAt C = ∀̇∈ (var C)
    ( binForm 0 bothTm ∨̇ (binForm 1 bothTm
    ∨̇ (binForm 2 noneB ∨̇ (binForm 3 noneB ∨̇ (binForm 4 noneB
    ∨̇ (unForm 5 noneU ∨̇ (unForm 6 zeroPay ∨̇ (unForm 7 zeroPay
    ∨̇ (unForm 8 noneU ∨̇ (unForm 9 noneU
    ∨̇ (binForm 10 fstTm ∨̇ binForm 11 fstTm)))))))))))
```

<!--en-->
## What a member is, read flat
<!--zh-->
## 一个成员是什么，摊平来读
<!--/-->

<!--en-->
Twelve alternatives. The two frames are read once each, generically in the
relation they carry, so that the walk over the disjunction below is twelve
applications of two readers rather than twelve copies of the same unnesting.
<!--zh-->
十二个可能。两个框架各读一次，且对它们所携带的关系泛型，好让下面那趟走过析取的路是两条读式的十二次施用，而不是同一段解嵌套的十二份拷贝。
<!--/-->

```agda
BinWit : ∀ {n} → ℕ → Formula S (4 + n) → S ^ n → S → Type (ℓ-suc ℓ)
BinWit k rel γ c = Σ[ N ∈ S ] (Σ[ a ∈ S ] (Σ[ b ∈ S ]
  ((fst c ≡ pr (fst N) (pr (# k) (pr (fst a) (fst b))))
   × ⟨ (b ∷ a ∷ N ∷ c ∷ γ) ⊨ rel ⟩)))

UnWit : ∀ {n} → ℕ → Formula S (3 + n) → S ^ n → S → Type (ℓ-suc ℓ)
UnWit k rel γ c = Σ[ N ∈ S ] (Σ[ a ∈ S ]
  ((fst c ≡ pr (fst N) (pr (# k) (fst a))) × ⟨ (a ∷ N ∷ c ∷ γ) ⊨ rel ⟩))

binForm-out : ∀ {n} (k : ℕ) (rel : Formula S (4 + n)) (γ : S ^ n) (c : S)
            → ⟨ (c ∷ γ) ⊨ binForm k rel ⟩ → ∥ BinWit k rel γ c ∥₁
binForm-out k rel γ c = PT.rec squash₁ (λ { (N , hN) →
  PT.rec squash₁ (λ { (a , ha) → PT.map
    (λ { (b , (hb , hr)) → N , (a , (b , (subst ⟨_⟩
       (arityTagPairAtL-adequate (suc (suc (suc zero))) (suc (suc zero)) k
          (suc zero) zero (b ∷ a ∷ N ∷ c ∷ γ)) hb , hr))) })
    ha }) hN })

unForm-out : ∀ {n} (k : ℕ) (rel : Formula S (3 + n)) (γ : S ^ n) (c : S)
           → ⟨ (c ∷ γ) ⊨ unForm k rel ⟩ → ∥ UnWit k rel γ c ∥₁
unForm-out k rel γ c = PT.rec squash₁ (λ { (N , hN) → PT.map
  (λ { (a , (ha , hr)) → N , (a , (subst ⟨_⟩
     (arityTagAtL-adequate (suc (suc zero)) (suc zero) k zero
        (a ∷ N ∷ c ∷ γ)) ha , hr)) })
  hN })

ShapeWit : ∀ {n} → S ^ n → S → Type (ℓ-suc ℓ)
ShapeWit γ c =
    BinWit 0 bothTm γ c ⊎ (BinWit 1 bothTm γ c
  ⊎ (BinWit 2 noneB γ c ⊎ (BinWit 3 noneB γ c ⊎ (BinWit 4 noneB γ c
  ⊎ (UnWit 5 noneU γ c ⊎ (UnWit 6 zeroPay γ c ⊎ (UnWit 7 zeroPay γ c
  ⊎ (UnWit 8 noneU γ c ⊎ (UnWit 9 noneU γ c
  ⊎ (BinWit 10 fstTm γ c ⊎ BinWit 11 fstTm γ c))))))))))

shaped-out : ∀ {n} (C : Fin n) (γ : S ^ n) → ⟨ γ ⊨ shapedAt C ⟩
           → (c : S) → ⟨ c ∈ˢ lookup C γ ⟩ → ∥ ShapeWit γ c ∥₁
shaped-out C γ h c c∈ = d1 (h c c∈)
  where
  d11 = PT.rec squash₁ (λ { (inl x) → PT.map inl (binForm-out 10 fstTm γ c x)
                          ; (inr x) → PT.map inr (binForm-out 11 fstTm γ c x) })
  d10 = PT.rec squash₁ (λ { (inl x) → PT.map inl (unForm-out 9 noneU γ c x)
                          ; (inr x) → PT.map inr (d11 x) })
  d9  = PT.rec squash₁ (λ { (inl x) → PT.map inl (unForm-out 8 noneU γ c x)
                          ; (inr x) → PT.map inr (d10 x) })
  d8  = PT.rec squash₁ (λ { (inl x) → PT.map inl (unForm-out 7 zeroPay γ c x)
                          ; (inr x) → PT.map inr (d9 x) })
  d7  = PT.rec squash₁ (λ { (inl x) → PT.map inl (unForm-out 6 zeroPay γ c x)
                          ; (inr x) → PT.map inr (d8 x) })
  d6  = PT.rec squash₁ (λ { (inl x) → PT.map inl (unForm-out 5 noneU γ c x)
                          ; (inr x) → PT.map inr (d7 x) })
  d5  = PT.rec squash₁ (λ { (inl x) → PT.map inl (binForm-out 4 noneB γ c x)
                          ; (inr x) → PT.map inr (d6 x) })
  d4  = PT.rec squash₁ (λ { (inl x) → PT.map inl (binForm-out 3 noneB γ c x)
                          ; (inr x) → PT.map inr (d5 x) })
  d3  = PT.rec squash₁ (λ { (inl x) → PT.map inl (binForm-out 2 noneB γ c x)
                          ; (inr x) → PT.map inr (d4 x) })
  d2  = PT.rec squash₁ (λ { (inl x) → PT.map inl (binForm-out 1 bothTm γ c x)
                          ; (inr x) → PT.map inr (d3 x) })
  d1  = PT.rec squash₁ (λ { (inl x) → PT.map inl (binForm-out 0 bothTm γ c x)
                          ; (inr x) → PT.map inr (d2 x) })
```

<!--en-->
## Terms, recovered
<!--zh-->
## 词项，被还原
<!--/-->

<!--en-->
The first decode, and the only one that needs no induction. A term is a constant
or a variable: the constant case reads its payload back as the constant, and the
variable case reads an index out of the arity numeral, which is where the bound
does its work. Nothing here descends, which is why it is separable from the
recursion that follows and why it is written first.
<!--zh-->
第一个解码，也是唯一一个不需要归纳的。词项要么是常元、要么是变元：常元那支把载荷原样读回作常元，变元那支从元数数码里读出一个序号，而界正是在那里起作用的。此处没有任何东西下降，这既是它可以从随后那场递归里分离出来的原因，也是它被先写下来的原因。
<!--/-->

```agda
TmWit : ℕ → V ℓ → Type (ℓ-suc ℓ)
TmWit n x = Σ[ t ∈ Term S n ] (fst LCode.⌜ t ⌝ᵗ ≡ x)

isTmAt-decode : ∀ {m} (t N : Fin m) (γ : S ^ m) (n : ℕ)
              → fst (lookup N γ) ≡ # n
              → ⟨ γ ⊨ isTmAt t N ⟩ → ∥ TmWit n (fst (lookup t γ)) ∥₁
isTmAt-decode {m} t N γ n qN = PT.rec squash₁
  (λ { (inl h) → PT.map
         (λ { (y , hy) → con y , (tagBridge 0 y ∙ sym
              (subst ⟨_⟩ (tagAtL-adequate (suc t) 0 zero (y ∷ γ)) hy)) })
         h
     ; (inr h) → PT.rec squash₁
         (λ { (z , (hz , z∈)) → PT.map
              (λ { (j , (j<n , ez)) →
                var (fromℕ' n j j<n)
                , ( tagBridge 1 (numeralL (toℕ (fromℕ' n j j<n)))
                  ∙ cong (λ w → pr (# 1) w)
                      ( numeralL-fst (toℕ (fromℕ' n j j<n))
                      ∙ cong #_ (toFromId' n j j<n) ∙ sym ez )
                  ∙ sym (subst ⟨_⟩
                      (tagAtL-adequate (suc t) 1 zero (z ∷ γ)) hz) ) })
              (∈#-elim n (fst z)
                (subst (λ w → ⟨ fst z ∈ w ⟩) qN z∈)) })
         h })
```

<!--en-->
## One layer off
<!--zh-->
## 剥掉一层
<!--/-->

<!--en-->
The two halves meet. Shapedness says which of the twelve a member is and hands
back its parts; closedness says those parts are members too, at the arity the
tag calls for. Neither half alone gives a step of a recursion, and together they
give exactly one.

The equation shapedness produces is, letter for letter, the one closedness
consumes, so the two compose with nothing in between. That is not luck: both
were written against the same reading of an arity-tagged pair.
<!--zh-->
两半会合。形状说出一个成员是十二者中的哪一个，并把它的部件交回；封闭性说那些部件也是成员，且在该标签所要求的元数上。两半各自都给不出递归的一步，合起来恰好给出一步。

形状产出的那条等式，正是封闭性所消费的那一条，逐字相同，故二者之间无需任何东西即可复合。这不是运气：两者都是对着「带元数标签的对」的同一条读法写下的。
<!--/-->

```agda
module Peel {m : ℕ} (C : Fin m) (γ : S ^ m)
            (hcl : ⟨ γ ⊨ closedAt C ⟩) (hsh : ⟨ γ ⊨ shapedAt C ⟩) where
  private
    D : V ℓ
    D = fst (lookup C γ)

  BinSame BinSucc : ℕ → S → Type (ℓ-suc ℓ)
  BinSame k c = Σ[ N ∈ S ] (Σ[ a ∈ S ] (Σ[ b ∈ S ]
    ((fst c ≡ pr (fst N) (pr (# k) (pr (fst a) (fst b))))
     × (⟨ pr (fst N) (fst a) ∈ D ⟩ × ⟨ pr (fst N) (fst b) ∈ D ⟩))))
  BinSucc k c = Σ[ N ∈ S ] (Σ[ a ∈ S ] (Σ[ b ∈ S ]
    ((fst c ≡ pr (fst N) (pr (# k) (pr (fst a) (fst b))))
     × (⟨ (a ∷ N ∷ c ∷ γ) ⊨ isTmAt zero (suc zero) ⟩
        × ⟨ pr (sucV (fst N)) (fst b) ∈ D ⟩))))

  UnSame UnSucc : ℕ → S → Type (ℓ-suc ℓ)
  UnSame k c = Σ[ N ∈ S ] (Σ[ a ∈ S ]
    ((fst c ≡ pr (fst N) (pr (# k) (fst a))) × ⟨ pr (fst N) (fst a) ∈ D ⟩))
  UnSucc k c = Σ[ N ∈ S ] (Σ[ a ∈ S ]
    ((fst c ≡ pr (fst N) (pr (# k) (fst a))) × ⟨ pr (sucV (fst N)) (fst a) ∈ D ⟩))

  PeelWit : S → Type (ℓ-suc ℓ)
  PeelWit c =
      BinWit 0 bothTm γ c ⊎ (BinWit 1 bothTm γ c
    ⊎ (BinSame 2 c ⊎ (BinSame 3 c ⊎ (BinSame 4 c
    ⊎ (UnSame 5 c ⊎ (UnWit 6 zeroPay γ c ⊎ (UnWit 7 zeroPay γ c
    ⊎ (UnSucc 8 c ⊎ (UnSucc 9 c
    ⊎ (BinSucc 10 c ⊎ BinSucc 11 c))))))))))

  peel : (c : S) → ⟨ c ∈ˢ lookup C γ ⟩ → ∥ PeelWit c ∥₁
  peel c c∈ = PT.map fill (shaped-out C γ hsh c c∈)
    where
    bs : (k : ℕ) → ⟨ γ ⊨ binShapeAt C k (bothSameAt C) ⟩ → BinWit k noneB γ c
       → BinSame k c
    bs k h (N , (a , (b , (e , _)))) =
      N , (a , (b , (e , binSameClosed-out C k γ h c N a b c∈ e)))

    us : (k : ℕ) → ⟨ γ ⊨ unShapeAt C k (oneSameAt C) ⟩ → UnWit k noneU γ c
       → UnSame k c
    us k h (N , (a , (e , _))) =
      N , (a , (e , unSameClosed-out C k γ h c N a c∈ e))

    uz : (k : ℕ) → ⟨ γ ⊨ unShapeAt C k (oneSuccAt C) ⟩ → UnWit k noneU γ c
       → UnSucc k c
    uz k h (N , (a , (e , _))) =
      N , (a , (e , unSuccClosed-out C k γ h c N a c∈ e))

    bz : (k : ℕ) → ⟨ γ ⊨ binShapeAt C k (succSndAt C) ⟩ → BinWit k fstTm γ c
       → BinSucc k c
    bz k h (N , (a , (b , (e , hr)))) =
      N , (a , (b , (e , (hr , binSuccClosed-out C k γ h c N a b c∈ e))))

    fill : ShapeWit γ c → PeelWit c
    fill (inl x) = inl x
    fill (inr (inl x)) = inr (inl x)
    fill (inr (inr (inl x))) = inr (inr (inl (bs 2 (hcl .fst) x)))
    fill (inr (inr (inr (inl x)))) =
      inr (inr (inr (inl (bs 3 (hcl .snd .fst) x))))
    fill (inr (inr (inr (inr (inl x))))) =
      inr (inr (inr (inr (inl (bs 4 (hcl .snd .snd .fst) x)))))
    fill (inr (inr (inr (inr (inr (inl x)))))) =
      inr (inr (inr (inr (inr (inl (us 5 (hcl .snd .snd .snd .fst) x))))))
    fill (inr (inr (inr (inr (inr (inr (inl x))))))) =
      inr (inr (inr (inr (inr (inr (inl x))))))
    fill (inr (inr (inr (inr (inr (inr (inr (inl x)))))))) =
      inr (inr (inr (inr (inr (inr (inr (inl x)))))))
    fill (inr (inr (inr (inr (inr (inr (inr (inr (inl x))))))))) =
      inr (inr (inr (inr (inr (inr (inr (inr
        (inl (uz 8 (hcl .snd .snd .snd .snd .fst) x)))))))))
    fill (inr (inr (inr (inr (inr (inr (inr (inr (inr (inl x)))))))))) =
      inr (inr (inr (inr (inr (inr (inr (inr (inr
        (inl (uz 9 (hcl .snd .snd .snd .snd .snd .fst) x))))))))))
    fill (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inl x))))))))))) =
      inr (inr (inr (inr (inr (inr (inr (inr (inr (inr
        (inl (bz 10 (hcl .snd .snd .snd .snd .snd .snd .fst) x)))))))))))
    fill (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr x))))))))))) =
      inr (inr (inr (inr (inr (inr (inr (inr (inr (inr
        (inr (bz 11 (hcl .snd .snd .snd .snd .snd .snd .snd) x)))))))))))
```

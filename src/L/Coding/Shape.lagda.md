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
open import FOL.Syntax using ( Formula; var; _∨̇_; ∃̇_; ∀̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ}
  using ( arityTagAtL; arityTagAtL-adequate
        ; arityTagPairAtL; arityTagPairAtL-adequate )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

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
A tag whose payload is a pair, and a tag whose payload is a single code. Each
binds the arity numeral and the parts, so that the disjunction below quantifies
once per tag rather than once for all of them: the parts of a conjunction and
the parts of a bounded quantifier are different things, and a single existential
over both would have to say so.
<!--zh-->
一类标签的载荷是一个对，另一类的载荷是单个码。二者各自绑定元数数码与诸部件，好让下面那个析取**逐标签**量化、而非为全体量化一次：合取的部件与有界量词的部件不是同一种东西，而横跨二者的单个存在量词将不得不把这件事说出来。
<!--/-->

```agda
module _ {n : ℕ} where
  binForm : ℕ → Formula S (suc n)
  binForm k = ∃̇ (∃̇ (∃̇ (arityTagPairAtL
                (suc (suc (suc zero))) (suc (suc zero)) k (suc zero) zero)))

  unForm : ℕ → Formula S (suc n)
  unForm k = ∃̇ (∃̇ (arityTagAtL (suc (suc zero)) (suc zero) k zero))

  shapedAt : Fin n → Formula S (suc n) → Formula S n
  shapedAt C leaf = ∀̇∈ (var C)
    ( binForm 2 ∨̇ (binForm 3 ∨̇ (binForm 4 ∨̇ (unForm 5
    ∨̇ (unForm 8 ∨̇ (unForm 9 ∨̇ (binForm 10 ∨̇ (binForm 11 ∨̇ leaf))))))))
```

<!--en-->
## What a member is, read flat
<!--zh-->
## 一个成员是什么，摊平来读
<!--/-->

<!--en-->
Nine alternatives, one per tag group, with the leaf case left as whatever the
parameter says. The two frames are read first and separately, because a frame is
three nested existentials and a nine-way disjunction of them read in one go
would be nine copies of the same unnesting.
<!--zh-->
九个可能，每个标签组一个，叶子那一支则是参数说什么就是什么。两个框架先各自单独读出，因为一个框架是三层嵌套的存在，而把它们的九路析取一口气读出，将是同一段解嵌套的九份拷贝。
<!--/-->

```agda
BinWit : ℕ → S → Type (ℓ-suc ℓ)
BinWit k c = Σ[ N ∈ S ] (Σ[ a ∈ S ] (Σ[ b ∈ S ]
  (fst c ≡ pr (fst N) (pr (# k) (pr (fst a) (fst b))))))

UnWit : ℕ → S → Type (ℓ-suc ℓ)
UnWit k c = Σ[ N ∈ S ] (Σ[ a ∈ S ] (fst c ≡ pr (fst N) (pr (# k) (fst a))))

binForm-out : ∀ {n} (k : ℕ) (γ : S ^ n) (c : S)
            → ⟨ (c ∷ γ) ⊨ binForm k ⟩ → ∥ BinWit k c ∥₁
binForm-out k γ c = PT.rec squash₁ (λ { (N , hN) →
  PT.rec squash₁ (λ { (a , ha) → PT.map
    (λ { (b , hb) → N , (a , (b , subst ⟨_⟩
       (arityTagPairAtL-adequate (suc (suc (suc zero))) (suc (suc zero)) k
          (suc zero) zero (b ∷ a ∷ N ∷ c ∷ γ)) hb)) })
    ha }) hN })

unForm-out : ∀ {n} (k : ℕ) (γ : S ^ n) (c : S)
           → ⟨ (c ∷ γ) ⊨ unForm k ⟩ → ∥ UnWit k c ∥₁
unForm-out k γ c = PT.rec squash₁ (λ { (N , hN) → PT.map
  (λ { (a , ha) → N , (a , subst ⟨_⟩
     (arityTagAtL-adequate (suc (suc zero)) (suc zero) k zero
        (a ∷ N ∷ c ∷ γ)) ha) })
  hN })

ShapeWit : ∀ {n} → S ^ n → Formula S (suc n) → S → Type (ℓ-suc ℓ)
ShapeWit γ leaf c =
    BinWit 2 c ⊎ (BinWit 3 c ⊎ (BinWit 4 c ⊎ (UnWit 5 c
  ⊎ (UnWit 8 c ⊎ (UnWit 9 c ⊎ (BinWit 10 c ⊎ (BinWit 11 c
  ⊎ ⟨ (c ∷ γ) ⊨ leaf ⟩)))))))

shaped-out : ∀ {n} (C : Fin n) (leaf : Formula S (suc n)) (γ : S ^ n)
           → ⟨ γ ⊨ shapedAt C leaf ⟩
           → (c : S) → ⟨ c ∈ˢ lookup C γ ⟩
           → ∥ ShapeWit γ leaf c ∥₁
shaped-out C leaf γ h c c∈ = d2 (h c c∈)
  where
  B : ℕ → Type (ℓ-suc ℓ)
  B k = BinWit k c
  d8 : ⟨ (c ∷ γ) ⊨ (binForm 11 ∨̇ leaf) ⟩ → ∥ (B 11 ⊎ ⟨ (c ∷ γ) ⊨ leaf ⟩) ∥₁
  d8 = PT.rec squash₁ (λ { (inl x) → PT.map inl (binForm-out 11 γ c x)
                         ; (inr x) → ∣ inr x ∣₁ })

  d7 : ⟨ (c ∷ γ) ⊨ (binForm 10 ∨̇ (binForm 11 ∨̇ leaf)) ⟩
     → ∥ (B 10 ⊎ (B 11 ⊎ ⟨ (c ∷ γ) ⊨ leaf ⟩)) ∥₁
  d7 = PT.rec squash₁ (λ { (inl x) → PT.map inl (binForm-out 10 γ c x)
                         ; (inr x) → PT.map inr (d8 x) })

  d6 = PT.rec squash₁ (λ { (inl x) → PT.map inl (unForm-out 9 γ c x)
                         ; (inr x) → PT.map inr (d7 x) })
  d5 = PT.rec squash₁ (λ { (inl x) → PT.map inl (unForm-out 8 γ c x)
                         ; (inr x) → PT.map inr (d6 x) })
  d4 = PT.rec squash₁ (λ { (inl x) → PT.map inl (unForm-out 5 γ c x)
                         ; (inr x) → PT.map inr (d5 x) })
  d3 = PT.rec squash₁ (λ { (inl x) → PT.map inl (binForm-out 4 γ c x)
                         ; (inr x) → PT.map inr (d4 x) })
  d2' = PT.rec squash₁ (λ { (inl x) → PT.map inl (binForm-out 3 γ c x)
                          ; (inr x) → PT.map inr (d3 x) })
  d2 = PT.rec squash₁ (λ { (inl x) → PT.map inl (binForm-out 2 γ c x)
                         ; (inr x) → PT.map inr (d2' x) })
```

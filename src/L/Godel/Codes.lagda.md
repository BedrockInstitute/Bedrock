# Term codes

<!--en-->
The syntax becomes data the model can hold. Each combinator term receives a
hereditarily finite code, a tag-and-pair tower over the sealed numeral chain,
so a code is an element of `L` by construction and no separate membership
argument is ever owed. Before the codes, the chapter enumerates subterms: every
term knows its size, its family of subterms indexed by a finite type, and the
places where a child's enumeration embeds in its parent's. Arities ride along
throughout, packed into the enumeration and recorded inside the codes, because
the shift constructor moves the arity and the leaves' meanings depend on it.
<!--zh-->
语法成为模型装得下的数据。每个组合子项获得一个遗传有穷的码，即封印数码链上的标签对塔，故码按构造就是 `L` 的元素，无须另欠任何隶属论证。码之前，本章先枚举子项：每个项知道自己的尺寸、以有穷类型索引的子项族，以及子项枚举嵌入父项枚举的位置。元数全程随行，打包进枚举、记录进码，因为移位构造子搬动元数，而诸叶的含义依赖它。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module L.Godel.Codes {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst )
open import L.Godel.Terms {ℓ}
  using ( KT; allK; selMemK; selEqK; selEqConK; interK; unionK; complK; shiftK )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.FinData.Properties using ( module FinSumChar )
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_ )

open hPropStructure 𝒮ʟ using ( S )
```

<!--en-->
## Subterm enumeration
<!--zh-->
## 子项枚举
<!--/-->

<!--en-->
A subterm carries its own arity, so the enumeration lands in the arity-packed
type. The term itself sits at index zero; a leaf has nothing else; a unary
node passes the successor indices straight to its child; a binary node splits
them between its children by the finite sum. The two facts consumers need are
that index zero is the term and that a child's index embeds where the split
says it does; the unary embeddings hold by definition and are not stated.
<!--zh-->
子项携带自己的元数，故枚举落在元数打包的类型里。项自身住在零号索引；叶没有别的；一元节点把后继索引原样递给孩子；二元节点按有穷和把它们分给两个孩子。消费者需要的两件事是零号索引就是项自身、孩子的索引嵌在有穷和所说的位置；一元的嵌入按定义成立，不另作陈述。
<!--/-->

```agda
SubK : Type ℓ → Type ℓ
SubK P = Σ[ m ∈ ℕ ] KT P m

sizeK : {P : Type ℓ} {n : ℕ} → KT P n → ℕ
sizeK allK = 1
sizeK (selMemK _ _) = 1
sizeK (selEqK _ _) = 1
sizeK (selEqConK _ _) = 1
sizeK (interK s t) = suc (sizeK s + sizeK t)
sizeK (unionK s t) = suc (sizeK s + sizeK t)
sizeK (complK t) = suc (sizeK t)
sizeK (shiftK t) = suc (sizeK t)

subK : {P : Type ℓ} {n : ℕ} (t : KT P n) → Fin (sizeK t) → SubK P
subSplitK : {P : Type ℓ} {n : ℕ} (s t : KT P n)
          → Fin (sizeK s) ⊎ Fin (sizeK t) → SubK P

subK {n = n} allK _ = n , allK
subK {n = n} (selMemK i j) _ = n , selMemK i j
subK {n = n} (selEqK i j) _ = n , selEqK i j
subK {n = n} (selEqConK i a) _ = n , selEqConK i a
subK {n = n} (interK s t) zero = n , interK s t
subK (interK s t) (suc k) =
  subSplitK s t (FinSumChar.inv (sizeK s) (sizeK t) k)
subK {n = n} (unionK s t) zero = n , unionK s t
subK (unionK s t) (suc k) =
  subSplitK s t (FinSumChar.inv (sizeK s) (sizeK t) k)
subK {n = n} (complK t) zero = n , complK t
subK (complK t) (suc k) = subK t k
subK {n = n} (shiftK t) zero = n , shiftK t
subK (shiftK t) (suc k) = subK t k

subSplitK s t (inl i) = subK s i
subSplitK s t (inr j) = subK t j

selfIxK : {P : Type ℓ} {n : ℕ} (t : KT P n) → Fin (sizeK t)
selfIxK allK = zero
selfIxK (selMemK _ _) = zero
selfIxK (selEqK _ _) = zero
selfIxK (selEqConK _ _) = zero
selfIxK (interK _ _) = zero
selfIxK (unionK _ _) = zero
selfIxK (complK _) = zero
selfIxK (shiftK _) = zero

sub-selfK : {P : Type ℓ} {n : ℕ} (t : KT P n) → subK t (selfIxK t) ≡ (n , t)
sub-selfK allK = refl
sub-selfK (selMemK i j) = refl
sub-selfK (selEqK i j) = refl
sub-selfK (selEqConK i a) = refl
sub-selfK (interK s t) = refl
sub-selfK (unionK s t) = refl
sub-selfK (complK t) = refl
sub-selfK (shiftK t) = refl

interIdxL : {P : Type ℓ} {n : ℕ} (s t : KT P n) (i : Fin (sizeK s))
  → subK (interK s t)
      (suc (FinSumChar.fun (sizeK s) (sizeK t) (inl i))) ≡ subK s i
interIdxL s t i = cong (subSplitK s t)
  (FinSumChar.ret (sizeK s) (sizeK t) (inl i))

interIdxR : {P : Type ℓ} {n : ℕ} (s t : KT P n) (j : Fin (sizeK t))
  → subK (interK s t)
      (suc (FinSumChar.fun (sizeK s) (sizeK t) (inr j))) ≡ subK t j
interIdxR s t j = cong (subSplitK s t)
  (FinSumChar.ret (sizeK s) (sizeK t) (inr j))

unionIdxL : {P : Type ℓ} {n : ℕ} (s t : KT P n) (i : Fin (sizeK s))
  → subK (unionK s t)
      (suc (FinSumChar.fun (sizeK s) (sizeK t) (inl i))) ≡ subK s i
unionIdxL s t i = cong (subSplitK s t)
  (FinSumChar.ret (sizeK s) (sizeK t) (inl i))

unionIdxR : {P : Type ℓ} {n : ℕ} (s t : KT P n) (j : Fin (sizeK t))
  → subK (unionK s t)
      (suc (FinSumChar.fun (sizeK s) (sizeK t) (inr j))) ≡ subK t j
unionIdxR s t j = cong (subSplitK s t)
  (FinSumChar.ret (sizeK s) (sizeK t) (inr j))
```

<!--en-->
## The codes
<!--zh-->
## 码
<!--/-->

<!--en-->
Eight constructors, eight tags. Every leaf records its arity, because a leaf's
denotation is a set the arity determines; the complement records it too,
because its meaning subtracts from the full assignment family; the two binary
nodes and the shift record only their children. The one leaf with a parameter
embeds the carrier member itself, an element of `L` by transitivity, so the
code of a term with parameters from `A` is hereditarily finite except exactly
at its parameter leaves. Everything is assembled by the sealed pairing and
numeral chain, and each constructor's code unfolds to a hierarchy-level
equation consumers rewrite along.
<!--zh-->
八个构造子，八个标签。每个叶记录自己的元数，因为叶的指称是由元数决定的集合；补也记录它，因为其含义从全体赋值族中作减；两个二元节点与移位只记录孩子。带参数的那个叶直接嵌入载体成员，经传递性是 `L` 的元素，故带 `A` 中参数的项的码除恰在参数叶处外遗传有穷。一切由封印的配对与数码链组装，而每个构造子的码展开为一条层级等式，消费者沿它重写。
<!--/-->

```agda
module Codes (A : V ℓ) (lA : ⟨ isL A ⟩) where

  paramS : ⟪ A ⟫ → S
  paramS a = ⟪ A ⟫↪ a
    , isL-trans {x = A} {y = ⟪ A ⟫↪ a}
        (∈∈ₛ {a = ⟪ A ⟫↪ a} {b = A} .snd (∈ₛ⟪ A ⟫↪ a)) lA

  codeS : {n : ℕ} → KT ⟪ A ⟫ n → S
  codeS {n} allK = prʟ (numeralL 0) (numeralL n)
  codeS {n} (selMemK i j) =
    prʟ (numeralL 1)
      (prʟ (numeralL n) (prʟ (numeralL (toℕ i)) (numeralL (toℕ j))))
  codeS {n} (selEqK i j) =
    prʟ (numeralL 2)
      (prʟ (numeralL n) (prʟ (numeralL (toℕ i)) (numeralL (toℕ j))))
  codeS {n} (selEqConK i a) =
    prʟ (numeralL 3)
      (prʟ (numeralL n) (prʟ (numeralL (toℕ i)) (paramS a)))
  codeS (interK s t) = prʟ (numeralL 4) (prʟ (codeS s) (codeS t))
  codeS (unionK s t) = prʟ (numeralL 5) (prʟ (codeS s) (codeS t))
  codeS {n} (complK t) = prʟ (numeralL 6) (prʟ (numeralL n) (codeS t))
  codeS (shiftK t) = prʟ (numeralL 7) (codeS t)

  code : {n : ℕ} → KT ⟪ A ⟫ n → V ℓ
  code t = fst (codeS t)

  code-allK : (n : ℕ) → code (allK {n = n}) ≡ pr (# 0) (# n)
  code-allK n = prʟ-fst (numeralL 0) (numeralL n)
    ∙ cong₂ pr (numeralL-fst 0) (numeralL-fst n)

  code-selMemK : (n : ℕ) (i j : Fin n)
    → code (selMemK i j)
    ≡ pr (# 1) (pr (# n) (pr (# (toℕ i)) (# (toℕ j))))
  code-selMemK n i j =
    prʟ-fst (numeralL 1)
      (prʟ (numeralL n) (prʟ (numeralL (toℕ i)) (numeralL (toℕ j))))
    ∙ cong₂ pr (numeralL-fst 1)
        ( prʟ-fst (numeralL n) (prʟ (numeralL (toℕ i)) (numeralL (toℕ j)))
        ∙ cong₂ pr (numeralL-fst n)
            ( prʟ-fst (numeralL (toℕ i)) (numeralL (toℕ j))
            ∙ cong₂ pr (numeralL-fst (toℕ i)) (numeralL-fst (toℕ j)) ) )

  code-selEqK : (n : ℕ) (i j : Fin n)
    → code (selEqK i j)
    ≡ pr (# 2) (pr (# n) (pr (# (toℕ i)) (# (toℕ j))))
  code-selEqK n i j =
    prʟ-fst (numeralL 2)
      (prʟ (numeralL n) (prʟ (numeralL (toℕ i)) (numeralL (toℕ j))))
    ∙ cong₂ pr (numeralL-fst 2)
        ( prʟ-fst (numeralL n) (prʟ (numeralL (toℕ i)) (numeralL (toℕ j)))
        ∙ cong₂ pr (numeralL-fst n)
            ( prʟ-fst (numeralL (toℕ i)) (numeralL (toℕ j))
            ∙ cong₂ pr (numeralL-fst (toℕ i)) (numeralL-fst (toℕ j)) ) )

  code-selEqConK : (n : ℕ) (i : Fin n) (a : ⟪ A ⟫)
    → code (selEqConK i a)
    ≡ pr (# 3) (pr (# n) (pr (# (toℕ i)) (⟪ A ⟫↪ a)))
  code-selEqConK n i a =
    prʟ-fst (numeralL 3)
      (prʟ (numeralL n) (prʟ (numeralL (toℕ i)) (paramS a)))
    ∙ cong₂ pr (numeralL-fst 3)
        ( prʟ-fst (numeralL n) (prʟ (numeralL (toℕ i)) (paramS a))
        ∙ cong₂ pr (numeralL-fst n)
            ( prʟ-fst (numeralL (toℕ i)) (paramS a)
            ∙ cong₂ pr (numeralL-fst (toℕ i)) refl ) )

  code-interK : {n : ℕ} (s t : KT ⟪ A ⟫ n)
    → code (interK s t) ≡ pr (# 4) (pr (code s) (code t))
  code-interK s t = prʟ-fst (numeralL 4) (prʟ (codeS s) (codeS t))
    ∙ cong₂ pr (numeralL-fst 4) (prʟ-fst (codeS s) (codeS t))

  code-unionK : {n : ℕ} (s t : KT ⟪ A ⟫ n)
    → code (unionK s t) ≡ pr (# 5) (pr (code s) (code t))
  code-unionK s t = prʟ-fst (numeralL 5) (prʟ (codeS s) (codeS t))
    ∙ cong₂ pr (numeralL-fst 5) (prʟ-fst (codeS s) (codeS t))

  code-complK : {n : ℕ} (t : KT ⟪ A ⟫ n)
    → code (complK t) ≡ pr (# 6) (pr (# n) (code t))
  code-complK {n} t = prʟ-fst (numeralL 6) (prʟ (numeralL n) (codeS t))
    ∙ cong₂ pr (numeralL-fst 6)
        (prʟ-fst (numeralL n) (codeS t) ∙ cong₂ pr (numeralL-fst n) refl)

  code-shiftK : {n : ℕ} (t : KT ⟪ A ⟫ (suc n))
    → code (shiftK t) ≡ pr (# 7) (code t)
  code-shiftK t = prʟ-fst (numeralL 7) (codeS t)
    ∙ cong₂ pr (numeralL-fst 7) refl
```

<!--en-->
## Discrimination
<!--zh-->
## 判别
<!--/-->

<!--en-->
The recorded law: discriminate tags through helpers whose numeral indices are
explicit data, never by letting unification meet a literal numeral under the
numeral function. The two helpers reduce every tag clash to an inequality of
natural numbers, which each consumer supplies as a two-line arithmetic fact.
<!--zh-->
在案的定律：经数码序号为显式数据的辅助件判别标签，绝不让合一在数码函数下遇到字面数码。两个辅助件把每次标签冲突化归为自然数的不等，消费者各以两行算术事实供给。
<!--/-->

```agda
tagNe : (j k : ℕ) {a b : V ℓ} → (j ≡ k → Empty.⊥)
      → pr (# j) a ≡ pr (# k) b → Empty.⊥
tagNe j k ne q = ne (#-inj′ (pr-inj q .fst))

payNe : (j k : ℕ) {a b : V ℓ} → (j ≡ k → Empty.⊥)
      → pr a (# j) ≡ pr b (# k) → Empty.⊥
payNe j k ne q = ne (#-inj′ (pr-inj q .snd))
```

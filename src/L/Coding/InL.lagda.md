# Codes are constructible

<!--en-->
A code is a hereditarily finite set built by pairing numerals, so it ought to be
an element of `L`, and this chapter says so. The proof is one induction over the
formula constructors with nothing in it, but the statement is what lets a later
chapter treat a code as an ordinary element of the model rather than as a set of
the hierarchy that happens to be lying around.

It matters more than it looks. A recursion internalized in `L` takes its domain
from a small family of *elements of `L`*, and the family here is the codes; a
graph naming a code as a constant needs that code to be an element of the model,
since the object language of the model has no other kind of constant. Both
requirements are this one lemma.

What is deliberately not proved is that the set of *all* codes is an element of
`L`. Nothing in this part needs it: a recursion over codes puts them inside a
stage from the small index type, one at a time, and cuts back by separation. The
set of all codes is a much harder object than any code, and the difference is the
whole reason it is not here. Whether a later part needs it is a separate question
with a separate answer: the answer is not yet in, and the place it is expected to
turn is the point where definability at a stage is internalized, since the
definable powerset takes syntax as its index type and an internalized index has
to be a set.
<!--zh-->
一个码是由配对数码造出的遗传有穷集，故它理应是 `L` 的元素，而本章就这么说。证明是沿公式构造子的一次归纳，里面什么也没有；但这条陈述使后续章节能把码当作模型的寻常元素，而非当作恰好躺在那里的层级集合。

它比看上去要紧。一个在 `L` 中内化的递归，其定义域取自 `L` **诸元素**的小族，而此处那个族就是诸码；而一个把码点名为常元的图，需要那个码是模型的元素，因为模型的对象语言没有别种常元。这两项要求都是这一条引理。

刻意不证的是「**全体**码之集是 `L` 的元素」。本部分没有东西需要它：对码的递归从小索引类型出发，把它们逐个放进一个阶段，再由分离切回来。全体码之集是比任何单个码都难得多的对象，而这个差别正是它不在此处的全部理由。后续部分是否需要它，是另一个问题、另一个答案：那个答案尚未到手，而预计会翻盘的地方是「阶段处的可定义性被内化」之时，因为可定义幂集以语法为索引类型，而被内化的索引必须是一个集合。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Coding.InL {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )

open import FOL.Syntax
  using ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.Relabelling using ( mapTm; mapFo )
open import V.Coding {ℓ} using ( pr; pr-inj; module VCode )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; IsOrd; Lset )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst; numL )
open import L.Axioms.Numerals {ℓ} using ( pairʟ; pairʟ-fst; unionʟ; unionʟ-fst )
open import L.Coding.Environment {ℓ} using ( env )
open import L.Axioms.Basic {ℓ} using ( finSet; module FinOf )

open import Cubical.Data.FinData using ( toℕ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_⁆s; ⁅_,_⁆; ⋃_; _∪_; module InfinitySet )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( Unit*; tt* )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import V.Model {ℓ} using ( pair-singleton; pair-spec; union-spec )
open InfinitySet using ( #_; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )
```

<!--en-->
## Two building blocks
<!--zh-->
## 两块砖
<!--/-->

<!--en-->
A numeral is constructible for the same reason, and was needed a chapter earlier,
so it lives there. A pair is
constructible because the model has pairing and the same equation reads it back.
A tag is a pair with a numeral on the left, so it is both.

Both are the same two-line move: build the thing inside the model, then transport
its membership along the equation saying that reading it out gives the thing.
<!--zh-->
数码可构造同理，而它早一章就被需要，故住在那里。对可构造，因为模型有配对，而同一条等式把它读回来。标签是左边放数码的对，故两者兼得。

两者都是同样的两行动作：先在模型内部把东西造出来，再沿「读出来就是那个东西」这条等式把它的隶属关系搬过去。
<!--/-->

```agda
prL : {a b : V ℓ} → ⟨ isL a ⟩ → ⟨ isL b ⟩ → ⟨ isL (pr a b) ⟩
prL {a} {b} pa pb =
  subst (λ w → ⟨ isL w ⟩) (prʟ-fst (a , pa) (b , pb))
    (prʟ (a , pa) (b , pb) .snd)

tagL : (k : ℕ) {x : V ℓ} → ⟨ isL x ⟩ → ⟨ isL (VCode.mkTag k x) ⟩
tagL k px = prL (numL k) px
```

<!--en-->
## The induction
<!--zh-->
## 归纳
<!--/-->

<!--en-->
Terms first. A term is a variable or a constant, and the two are the two tags
that terms carry: a numeral for the variable's index, and the constant's own set
for a constant. So a code is constructible provided the constants it names are,
and the induction takes that as its hypothesis rather than assuming there are
none.

That generality costs one clause and buys the parameters. A formula whose
constants are members of a stage codes to a set of `L` exactly as a
parameter-free one does, which is what lets the recursion below range over the
formulas the constructible hierarchy is actually built from. The parameter-free
case is the instance at the empty type.

Then the formulas, twelve clauses and no content: each constructor's code is a
tag on either a pair of sub-codes, a single sub-code, or a numeral, and the three
blocks above cover all three shapes. The induction is over the parameter-free
formula rather than its embedding, which costs nothing because embedding is a
relabelling and commutes with every constructor definitionally.
<!--zh-->
先看词项。一个词项要么是变元、要么是常元，而两者正是词项所携带的两个标签：变元带它的索引数码，常元带它自己那个集合。故一个码可构造，只要它所点名的诸常元可构造，而这次归纳把那一条取作假设，而非假定根本没有常元。

这份一般性花掉一条子句，换来的是诸参数。常元取自某阶段成员的公式，其编码与无参公式一样是 `L` 的集合，而正是这一点，使下面的递归得以遍历可构造层级实际由之造出的那些公式。无参情形是空类型处的实例。

然后是诸公式，十二条子句，毫无内容：每个构造子的码，都是「子码之对」「单个子码」或「数码」三者之一上的标签，而上面三块砖覆盖了这三种形状。归纳沿无参公式而非它的嵌入进行，这不费分文，因为嵌入是一次常量改名，按定义与每个构造子交换。
<!--/-->

```agda
module _ {K : Type ℓ} (f : K → V ℓ) (h : (k : K) → ⟨ isL (f k) ⟩) where

  codeTmL : ∀ {n} (t : Term K n) → ⟨ isL VCode.⌜ mapTm f t ⌝ᵗ ⟩
  codeTmL (con c) = tagL 0 (h c)
  codeTmL (var i) = tagL 1 (numL _)

  codeL : ∀ {n} (φ : Formula K n) → ⟨ isL VCode.⌜ mapFo f φ ⌝ ⟩
  codeL (t ∈̇ u)  = tagL 0  (prL (codeTmL t) (codeTmL u))
  codeL (t ≐ u)  = tagL 1  (prL (codeTmL t) (codeTmL u))
  codeL (φ ∧̇ ψ)  = tagL 2  (prL (codeL φ) (codeL ψ))
  codeL (φ ∨̇ ψ)  = tagL 3  (prL (codeL φ) (codeL ψ))
  codeL (φ ⇒̇ ψ)  = tagL 4  (prL (codeL φ) (codeL ψ))
  codeL (¬̇ φ)    = tagL 5  (codeL φ)
  codeL ⊤̇        = tagL 6  (numL 0)
  codeL ⊥̇        = tagL 7  (numL 0)
  codeL (∃̇ φ)    = tagL 8  (codeL φ)
  codeL (∀̇ φ)    = tagL 9  (codeL φ)
  codeL (∀̇∈ t φ) = tagL 10 (prL (codeTmL t) (codeL φ))
  codeL (∃̇∈ t φ) = tagL 11 (prL (codeTmL t) (codeL φ))
```

<!--en-->
## Environments
<!--zh-->
## 环境
<!--/-->

<!--en-->
An environment is a finite set: the keys are the numerals below its length and
the entries are pairs. It is, in fact, *the* finite set of the pairs, on the
nose, because both are the same image of the same lifted index type. Saying so
is one line, and it is the line that lets the finite-family lemma apply to
environments without any further argument.

The consequence is that an environment over a stage is an element of `L`
immediately: its entries are pairs of a numeral with a member of the stage, and
both are in the stage after one step. No recursion on the length, and no
replacement.
<!--zh-->
一个环境是一个有穷集：键是长度以下的诸数码，条目是诸对。事实上它**恰恰就是**那些对构成的有穷集，一分不差，因为两者是同一个被抬升的索引类型的同一个像。把这一点说出来只需一行，而正是这一行使有穷族引理无须任何进一步论证便可施于环境。

由此，落在某阶段之上的环境立刻是 `L` 的元素：它的条目是「数码与该阶段的成员」之对，而两者在一步之后都落在该阶段里。不必沿长度递归，也不必用替换。
<!--/-->

```agda
envIsFinSet : ∀ {n} (g : Fin n → V ℓ)
            → env g ≡ finSet n (λ i → pr (# (toℕ i)) (g i))
envIsFinSet g = refl

envL : (σ : V ℓ) (oσ : IsOrd σ) {n : ℕ} (g : Fin n → V ℓ)
     → ((i : Fin n) → ⟨ pr (# (toℕ i)) (g i) ∈ Lset σ ⟩)
     → ⟨ isL (env g) ⟩
envL σ oσ {n} g h =
  subst (λ w → ⟨ isL w ⟩) (sym (envIsFinSet g))
    (FinOf.finSetL σ oσ n (λ i → pr (# (toℕ i)) (g i)) h)
```

<!--en-->
## Unions and singletons
<!--zh-->
## 并与单点集
<!--/-->

<!--en-->
Two more shapes, and the model supplies both directly. A singleton is the pair of
a thing with itself, and a binary union is the union of the pair, so each is the
model's own operation read through the underlying set.

Each shape comes twice over. Once on the underlying set, with the two lemmas that
read a member of a singleton or of a binary union back, and once on the model's
own sets, where the constructibility certificate rides along and the same lemmas
are restated through the equation that reads the underlying set out. The
recursion below runs on the second, so a set it builds is an element of `L` by
construction and not by a second induction.
<!--zh-->
再来两种形状，而模型直接供给两者。单点集是一物与自身之对，二元并是那个对之并，故各是模型自家的运算沿底集读出。

每种形状都来两遍。一遍落在底集上，配两条把单元集或二元并的成员读回来的引理；一遍落在模型自己的集合上，此时可构造性证书一路带着，而同样那些引理经由「读出底集」那条等式重述一次。下面那个递归跑在第二遍上，故它造出的集合按构造就是 `L` 的元素，而不必再来一次归纳。
<!--/-->

```agda
sglL : {a : V ℓ} → ⟨ isL a ⟩ → ⟨ isL ⁅ a ⁆s ⟩
sglL {a} pa =
  subst (λ w → ⟨ isL w ⟩) (pairʟ-fst (a , pa) (a , pa) ∙ pair-singleton a)
    (pairʟ (a , pa) (a , pa) .snd)

cupL : {a b : V ℓ} → ⟨ isL a ⟩ → ⟨ isL b ⟩ → ⟨ isL (a ∪ b) ⟩
cupL {a} {b} pa pb =
  subst (λ w → ⟨ isL w ⟩)
    (unionʟ-fst (pairʟ (a , pa) (b , pb))
      ∙ cong (⋃_) (pairʟ-fst (a , pa) (b , pb)))
    (unionʟ (pairʟ (a , pa) (b , pb)) .snd)

sgl-out : (a x : V ℓ) → ⟨ x ∈ ⁅ a ⁆s ⟩ → x ≡ a
sgl-out a x h = PT.rec (setIsSet x a) (λ { (inl e) → e ; (inr e) → e })
  (subst ⟨_⟩ (pair-spec a a x)
    (subst (λ w → ⟨ x ∈ w ⟩) (sym (pair-singleton a)) h))

sgl-in : (a x : V ℓ) → x ≡ a → ⟨ x ∈ ⁅ a ⁆s ⟩
sgl-in a x e = subst (λ w → ⟨ x ∈ w ⟩) (pair-singleton a)
  (subst ⟨_⟩ (sym (pair-spec a a x)) ∣ inl e ∣₁)

cup-out : (A B x : V ℓ) → ⟨ x ∈ (A ∪ B) ⟩ → ∥ (⟨ x ∈ A ⟩ ⊎ ⟨ x ∈ B ⟩) ∥₁
cup-out A B x h = PT.rec squash₁
  (λ { (v , v∈ , x∈v) → PT.map
         (λ { (inl e) → inl (subst (λ w → ⟨ x ∈ w ⟩) e x∈v)
            ; (inr e) → inr (subst (λ w → ⟨ x ∈ w ⟩) e x∈v) })
         (subst ⟨_⟩ (pair-spec A B v) v∈) })
  (subst ⟨_⟩ (union-spec ⁅ A , B ⁆ x) h)

cup-inl : (A B x : V ℓ) → ⟨ x ∈ A ⟩ → ⟨ x ∈ (A ∪ B) ⟩
cup-inl A B x h = subst ⟨_⟩ (sym (union-spec ⁅ A , B ⁆ x))
  ∣ A , subst ⟨_⟩ (sym (pair-spec A B A)) ∣ inl refl ∣₁ , h ∣₁

cup-inr : (A B x : V ℓ) → ⟨ x ∈ B ⟩ → ⟨ x ∈ (A ∪ B) ⟩
cup-inr A B x h = subst ⟨_⟩ (sym (union-spec ⁅ A , B ⁆ x))
  ∣ B , subst ⟨_⟩ (sym (pair-spec A B B)) ∣ inr refl ∣₁ , h ∣₁

sglʟ : S → S
sglʟ a = pairʟ a a

sglʟ-fst : (a : S) → fst (sglʟ a) ≡ ⁅ fst a ⁆s
sglʟ-fst a = pairʟ-fst a a ∙ pair-singleton (fst a)

cupʟ : S → S → S
cupʟ a b = unionʟ (pairʟ a b)

cupʟ-fst : (a b : S) → fst (cupʟ a b) ≡ (fst a ∪ fst b)
cupʟ-fst a b = unionʟ-fst (pairʟ a b) ∙ cong (⋃_) (pairʟ-fst a b)

sglʟ-in : (a : S) (x : V ℓ) → x ≡ fst a → ⟨ x ∈ fst (sglʟ a) ⟩
sglʟ-in a x e = subst (λ w → ⟨ x ∈ w ⟩) (sym (sglʟ-fst a)) (sgl-in (fst a) x e)

sglʟ-out : (a : S) (x : V ℓ) → ⟨ x ∈ fst (sglʟ a) ⟩ → x ≡ fst a
sglʟ-out a x h = sgl-out (fst a) x (subst (λ w → ⟨ x ∈ w ⟩) (sglʟ-fst a) h)

cupʟ-inl : (a b : S) (x : V ℓ) → ⟨ x ∈ fst a ⟩ → ⟨ x ∈ fst (cupʟ a b) ⟩
cupʟ-inl a b x h = subst (λ w → ⟨ x ∈ w ⟩) (sym (cupʟ-fst a b))
  (cup-inl (fst a) (fst b) x h)

cupʟ-inr : (a b : S) (x : V ℓ) → ⟨ x ∈ fst b ⟩ → ⟨ x ∈ fst (cupʟ a b) ⟩
cupʟ-inr a b x h = subst (λ w → ⟨ x ∈ w ⟩) (sym (cupʟ-fst a b))
  (cup-inr (fst a) (fst b) x h)

cupʟ-out : (a b : S) (x : V ℓ) → ⟨ x ∈ fst (cupʟ a b) ⟩
         → ∥ (⟨ x ∈ fst a ⟩ ⊎ ⟨ x ∈ fst b ⟩) ∥₁
cupʟ-out a b x h = cup-out (fst a) (fst b) x
  (subst (λ w → ⟨ x ∈ w ⟩) (cupʟ-fst a b) h)
```

<!--en-->
## The subformula recursion
<!--zh-->
## 子公式递归
<!--/-->

<!--en-->
One recursion over the twelve constructors, with what it collects left as its
parameter. It gathers one thing per subformula: give it the key and it gives the
subformula closure of the next section, give it an entry and it gives the
satisfaction table of a later chapter. Both want the same inversion, so the
inversion is proved here once and instantiated twice.

`Of`{.Agda} says what a member of such a set is: one of the things gathered,
gathered at some subformula whose own set sits inside the one it came from.
`tree-inv`{.Agda} proves it, and `Parts`{.Agda} carries the memberships the other
direction needs, one for each shape a clause of the recursion produces.
<!--zh-->
沿十二个构造子的一次递归，收集什么留作它的参数。它为每条子公式收集一样东西：给它键，得到下一节那个子公式闭包；给它条目，得到后续某章那张可满足性表。两者要的是同一次求逆，故那次求逆在此只证一次，再实例化两次。

`Of`{.Agda} 说出这种集合的成员是什么：它是被收集之物之一，收集于某条子公式处，而那条子公式自己的集合坐落于它所出自的那个之内。`tree-inv`{.Agda} 证明这一点，而 `Parts`{.Agda} 携带另一方向所需的诸隶属关系，递归的每条子句所产生的每种形状各一条。
<!--/-->

```agda
module _ {ℓ' : Level} {K : Type ℓ'} where

  tree : (∀ {m} → Formula K m → S) → ∀ {n} → Formula K n → S
  tree f φ@(t ∈̇ u)  = sglʟ (f φ)
  tree f φ@(t ≐ u)  = sglʟ (f φ)
  tree f φ@⊤̇        = sglʟ (f φ)
  tree f φ@⊥̇        = sglʟ (f φ)
  tree f φ@(a ∧̇ b)  = cupʟ (sglʟ (f φ)) (cupʟ (tree f a) (tree f b))
  tree f φ@(a ∨̇ b)  = cupʟ (sglʟ (f φ)) (cupʟ (tree f a) (tree f b))
  tree f φ@(a ⇒̇ b)  = cupʟ (sglʟ (f φ)) (cupʟ (tree f a) (tree f b))
  tree f φ@(¬̇ a)    = cupʟ (sglʟ (f φ)) (tree f a)
  tree f φ@(∃̇ a)    = cupʟ (sglʟ (f φ)) (tree f a)
  tree f φ@(∀̇ a)    = cupʟ (sglʟ (f φ)) (tree f a)
  tree f φ@(∀̇∈ t a) = cupʟ (sglʟ (f φ)) (tree f a)
  tree f φ@(∃̇∈ t a) = cupʟ (sglʟ (f φ)) (tree f a)

  Of : (f g : ∀ {m} → Formula K m → S) {n : ℕ} → Formula K n → V ℓ
     → Type (ℓ-max (ℓ-suc ℓ) ℓ')
  Of f g φ x = ∥ (Σ[ m ∈ ℕ ] Σ[ χ ∈ Formula K m ]
                   ((x ≡ fst (f χ))
                    × ((z : V ℓ) → ⟨ z ∈ fst (tree g χ) ⟩
                       → ⟨ z ∈ fst (tree g φ) ⟩))) ∥₁

  private
    module _ (f g : ∀ {m} → Formula K m → S) where
      one : ∀ {n} (φ : Formula K n) (x : V ℓ)
          → ⟨ x ∈ fst (sglʟ (f φ)) ⟩ → Of f g φ x
      one {n} φ x h = ∣ n , φ , sglʟ-out (f φ) x h , (λ _ hz → hz) ∣₁

      wider : ∀ {n m} (φ : Formula K n) (χ : Formula K m) {x : V ℓ}
            → ((z : V ℓ) → ⟨ z ∈ fst (tree g χ) ⟩ → ⟨ z ∈ fst (tree g φ) ⟩)
            → Of f g χ x → Of f g φ x
      wider _ _ s = PT.map
        (λ { (m , ψ , e , t) → m , ψ , e , (λ z hz → s z (t z hz)) })

      un : ∀ {n m} (φ : Formula K n) (a : Formula K m)
         → ((z : V ℓ) → ⟨ z ∈ fst (cupʟ (sglʟ (g φ)) (tree g a)) ⟩
            → ⟨ z ∈ fst (tree g φ) ⟩)
         → ((x : V ℓ) → ⟨ x ∈ fst (tree f a) ⟩ → Of f g a x)
         → (x : V ℓ) → ⟨ x ∈ fst (cupʟ (sglʟ (f φ)) (tree f a)) ⟩ → Of f g φ x
      un φ a into ra x h = PT.rec squash₁
        (λ { (inl e) → one φ x e
           ; (inr e) → wider φ a
               (λ z hz → into z (cupʟ-inr (sglʟ (g φ)) (tree g a) z hz))
               (ra x e) })
        (cupʟ-out (sglʟ (f φ)) (tree f a) x h)

      bin : ∀ {n m} (φ : Formula K n) (a b : Formula K m)
          → ((z : V ℓ)
             → ⟨ z ∈ fst (cupʟ (sglʟ (g φ)) (cupʟ (tree g a) (tree g b))) ⟩
             → ⟨ z ∈ fst (tree g φ) ⟩)
          → ((x : V ℓ) → ⟨ x ∈ fst (tree f a) ⟩ → Of f g a x)
          → ((x : V ℓ) → ⟨ x ∈ fst (tree f b) ⟩ → Of f g b x)
          → (x : V ℓ)
          → ⟨ x ∈ fst (cupʟ (sglʟ (f φ)) (cupʟ (tree f a) (tree f b))) ⟩
          → Of f g φ x
      bin φ a b into ra rb x h = PT.rec squash₁
        (λ { (inl e) → one φ x e
           ; (inr e) → PT.rec squash₁
               (λ { (inl ea) → wider φ a (λ z hz → into z
                      (cupʟ-inr (sglʟ (g φ)) (cupʟ (tree g a) (tree g b)) z
                        (cupʟ-inl (tree g a) (tree g b) z hz)))
                      (ra x ea)
                  ; (inr eb) → wider φ b (λ z hz → into z
                      (cupʟ-inr (sglʟ (g φ)) (cupʟ (tree g a) (tree g b)) z
                        (cupʟ-inr (tree g a) (tree g b) z hz)))
                      (rb x eb) })
               (cupʟ-out (tree f a) (tree f b) x e) })
        (cupʟ-out (sglʟ (f φ)) (cupʟ (tree f a) (tree f b)) x h)

  module Parts (f : ∀ {m} → Formula K m → S) where
    self : ∀ {n} (φ : Formula K n) → ⟨ fst (f φ) ∈ fst (tree f φ) ⟩
    self φ@(t ∈̇ u)  = sglʟ-in (f φ) _ refl
    self φ@(t ≐ u)  = sglʟ-in (f φ) _ refl
    self φ@⊤̇        = sglʟ-in (f φ) _ refl
    self φ@⊥̇        = sglʟ-in (f φ) _ refl
    self φ@(a ∧̇ b)  = cupʟ-inl _ _ _ (sglʟ-in (f φ) _ refl)
    self φ@(a ∨̇ b)  = cupʟ-inl _ _ _ (sglʟ-in (f φ) _ refl)
    self φ@(a ⇒̇ b)  = cupʟ-inl _ _ _ (sglʟ-in (f φ) _ refl)
    self φ@(¬̇ a)    = cupʟ-inl _ _ _ (sglʟ-in (f φ) _ refl)
    self φ@(∃̇ a)    = cupʟ-inl _ _ _ (sglʟ-in (f φ) _ refl)
    self φ@(∀̇ a)    = cupʟ-inl _ _ _ (sglʟ-in (f φ) _ refl)
    self φ@(∀̇∈ t a) = cupʟ-inl _ _ _ (sglʟ-in (f φ) _ refl)
    self φ@(∃̇∈ t a) = cupʟ-inl _ _ _ (sglʟ-in (f φ) _ refl)

    left : ∀ {n m} (χ : Formula K n) (a b : Formula K m) (z : V ℓ)
         → ⟨ z ∈ fst (tree f a) ⟩
         → ⟨ z ∈ fst (cupʟ (sglʟ (f χ)) (cupʟ (tree f a) (tree f b))) ⟩
    left χ a b z h = cupʟ-inr (sglʟ (f χ)) (cupʟ (tree f a) (tree f b)) z
                       (cupʟ-inl (tree f a) (tree f b) z h)

    right : ∀ {n m} (χ : Formula K n) (a b : Formula K m) (z : V ℓ)
          → ⟨ z ∈ fst (tree f b) ⟩
          → ⟨ z ∈ fst (cupʟ (sglʟ (f χ)) (cupʟ (tree f a) (tree f b))) ⟩
    right χ a b z h = cupʟ-inr (sglʟ (f χ)) (cupʟ (tree f a) (tree f b)) z
                        (cupʟ-inr (tree f a) (tree f b) z h)

    only : ∀ {n m} (χ : Formula K n) (a : Formula K m) (z : V ℓ)
         → ⟨ z ∈ fst (tree f a) ⟩
         → ⟨ z ∈ fst (cupʟ (sglʟ (f χ)) (tree f a)) ⟩
    only χ a z h = cupʟ-inr (sglʟ (f χ)) (tree f a) z h

  tree-inv : (f g : ∀ {m} → Formula K m → S)
           → ∀ {n} (φ : Formula K n) (x : V ℓ)
           → ⟨ x ∈ fst (tree f φ) ⟩ → Of f g φ x
  tree-inv f g φ@(t ∈̇ u) = one f g φ
  tree-inv f g φ@(t ≐ u) = one f g φ
  tree-inv f g φ@⊤̇       = one f g φ
  tree-inv f g φ@⊥̇       = one f g φ
  tree-inv f g φ@(a ∧̇ b) = bin f g φ a b (λ _ hz → hz)
                             (tree-inv f g a) (tree-inv f g b)
  tree-inv f g φ@(a ∨̇ b) = bin f g φ a b (λ _ hz → hz)
                             (tree-inv f g a) (tree-inv f g b)
  tree-inv f g φ@(a ⇒̇ b) = bin f g φ a b (λ _ hz → hz)
                             (tree-inv f g a) (tree-inv f g b)
  tree-inv f g φ@(¬̇ a)    = un f g φ a (λ _ hz → hz) (tree-inv f g a)
  tree-inv f g φ@(∃̇ a)    = un f g φ a (λ _ hz → hz) (tree-inv f g a)
  tree-inv f g φ@(∀̇ a)    = un f g φ a (λ _ hz → hz) (tree-inv f g a)
  tree-inv f g φ@(∀̇∈ t a) = un f g φ a (λ _ hz → hz) (tree-inv f g a)
  tree-inv f g φ@(∃̇∈ t a) = un f g φ a (λ _ hz → hz) (tree-inv f g a)
```

<!--en-->
## The subformula closure
<!--zh-->
## 子公式闭包
<!--/-->

<!--en-->
A recursion on codes is stated against a *slot*: a set of codes closed under
immediate subcodes, holding the one the recursion is asked about. The smallest
such slot is the set of codes of a formula's own subformulas, and it is the
recursion above taken at the key.

Each entry carries its arity, because the recursion's own key does; a binder's
subformula therefore enters at the successor. That is the only place the
bookkeeping is visible, and it is visible because the arity is what the frames
bind.

Constructibility is not a second proof. The recursion above runs on the model's
own sets, so the certificate comes out of it together with the set.
<!--zh-->
对码的递归是相对某个**槽**陈述的：一个对直接子码封闭、且装着被问及的那个码的码集。最小的这种槽，就是一条公式自身诸子公式的码之集，而它就是上面那个递归在键处的取值。

每个条目都携带自己的元数，因为递归自己的键就携带；故绑定子的子公式在后继处进入。那是记账唯一可见之处，而它可见，是因为元数正是诸框架所绑定的东西。

可构造性不是第二次证明。上面那个递归跑在模型自己的集合上，故证书随集合一并出来。
<!--/-->

```agda
module _ {K : Type ℓ} (f : K → V ℓ) (h : (k : K) → ⟨ isL (f k) ⟩) where

  key : ∀ {n} → Formula K n → V ℓ
  key {n} φ = pr (# n) VCode.⌜ mapFo f φ ⌝

  keyL : ∀ {n} (φ : Formula K n) → ⟨ isL (key φ) ⟩
  keyL φ = prL (numL _) (codeL f h φ)

  private
    keyS : ∀ {m} → Formula K m → S
    keyS φ = key φ , keyL φ

  closure : ∀ {n} → Formula K n → V ℓ
  closure φ = fst (tree keyS φ)

  closureL : ∀ {n} (φ : Formula K n) → ⟨ isL (closure φ) ⟩
  closureL φ = snd (tree keyS φ)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`codeL`{.Agda} says every code is an element of `L`, and `numL`{.Agda},
`prL`{.Agda} and `tagL`{.Agda} are the three shapes it is built from. With it a
code may be named as a constant of the model's object language, and a family of
codes may be the domain of an internalized recursion.

`envL`{.Agda} then puts an environment in `L` with no recursion on its length and
no use of replacement, because an environment is on the nose the finite set of
its entries. `closure`{.Agda} is the smallest slot a recursion on a code can be
stated against, and `closureL`{.Agda} reads its certificate off the recursion
that built it rather than proving it a second time.

The set of all codes is still not an element of `L`, and is still not needed.
<!--zh-->
`codeL`{.Agda} 说每个码都是 `L` 的元素，而 `numL`{.Agda}、`prL`{.Agda} 与 `tagL`{.Agda} 是它所由构造的三种形状。有了它，一个码就可以被点名为模型对象语言的常元，而一族码就可以充当某个已内化递归的定义域。

`envL`{.Agda} 随后把一个环境放进 `L`，既不沿长度递归，也不用替换，因为一个环境恰恰就是它诸条目构成的有穷集。`closure`{.Agda} 是「对一个码的递归」所能相对陈述的最小的槽，而 `closureL`{.Agda} 把它的证书从造出它的那个递归上读下来，不必再证第二次。

全体码之集仍然不是 `L` 的元素，也仍然不需要是。
<!--/-->

<!--en-->
## Reading a closure back
<!--zh-->
## 把闭包读回来
<!--/-->

<!--en-->
A recursion over codes has to know what the elements of its domain are, and
"whatever the union of these singletons happens to contain" is not an answer.
The lemma below is the answer: every element of a closure is the key of a
formula, and that formula's own closure sits inside the one it came from. The
second half is what an induction consumes, since it is how the induction knows
its hypothesis is available where it wants to apply it.

It and the membership of a key in its own closure are the recursion above read
at the key, so neither is an induction here.
<!--zh-->
对码的递归必须知道自己定义域的元素是什么，而「这些单元集之并恰好含有的任何东西」不是一个回答。下面这条引理就是回答：闭包的每个元素都是某条公式的键，而那条公式自己的闭包坐落在它所出自的那个之内。后一半才是归纳所消费的，因为归纳正是靠它知道自己的假设在想用的地方可用。

它与「键属于自己的闭包」都是上面那个递归在键处的读法，故此处两者都不是归纳。
<!--/-->

```agda
  Inv : ∀ {n} → Formula K n → V ℓ → Type (ℓ-suc ℓ)
  Inv φ x = Of keyS keyS φ x

  closure-inv : ∀ {n} (φ : Formula K n) (x : V ℓ)
              → ⟨ x ∈ closure φ ⟩ → Inv φ x
  closure-inv φ x hx = tree-inv keyS keyS φ x hx

  key∈closure : ∀ {n} (φ : Formula K n) → ⟨ key φ ∈ closure φ ⟩
  key∈closure φ = Parts.self keyS φ
```

<!--en-->
## What a key of that shape has under it
<!--zh-->
## 那种形状的键之下有什么
<!--/-->

<!--en-->
The demand a closedness predicate makes is indexed by a constructor tag, and the
formula it is made of is indexed by a constructor. Matching the two is the only
real work in the first instance, and doing it clause by clause would be twelve
formulas times eight demands. It is not, because the demand can be *computed*
from the tag: one type family over the tag, one function over the formula, and
the equation between tags that the key's injectivity yields carries the second to
the first.

Below the tag, a key is an arity paired with a code, and both layers are pinned
by pairing's injectivity. What comes out is that an arity-preserving constructor
demands its components at the arity read, an arity-raising one demands them at
the successor, and a constructor with no subformula demands nothing.
<!--zh-->
封闭性谓词提的要求以构造子标签为索引，而它所谈论的公式以构造子为索引。把这两者对上，是第一个实例里唯一真正的活；而逐条去做会是十二条公式乘八项要求。不必如此，因为那项要求可以从标签**算**出来：一个以标签为索引的类型族、一个以公式为索引的函数，而键的单射性所给出的那条标签等式把后者搬到前者上。

标签之下，一个键是元数与码之对，两层都由配对的单射性钉住。得出的是：保持元数的构造子在被读出的元数处索取它的诸分量，抬升元数的在后继处索取，而没有子公式的构造子什么也不索取。
<!--/-->

```agda
  module _ (C : V ℓ) where
    BothSame : V ℓ → V ℓ → Type (ℓ-suc ℓ)
    BothSame ar p = (u v : V ℓ) → p ≡ pr u v
                  → ⟨ pr ar u ∈ C ⟩ × ⟨ pr ar v ∈ C ⟩

    SecondSucc : V ℓ → V ℓ → Type (ℓ-suc ℓ)
    SecondSucc ar p = (u v : V ℓ) → p ≡ pr u v → ⟨ pr (sucV ar) v ∈ C ⟩

    Concl : ℕ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
    Concl 2  ar p = BothSame ar p
    Concl 3  ar p = BothSame ar p
    Concl 4  ar p = BothSame ar p
    Concl 5  ar p = ⟨ pr ar p ∈ C ⟩
    Concl 8  ar p = ⟨ pr (sucV ar) p ∈ C ⟩
    Concl 9  ar p = ⟨ pr (sucV ar) p ∈ C ⟩
    Concl 10 ar p = SecondSucc ar p
    Concl 11 ar p = SecondSucc ar p
    Concl _  _  _ = Unit*

    private
      Below : ∀ {n} → Formula K n → Type (ℓ-suc ℓ)
      Below φ = (z : V ℓ) → ⟨ z ∈ closure φ ⟩ → ⟨ z ∈ C ⟩

      inC : ∀ {n m} (φ : Formula K n) (a : Formula K m)
          → Below φ → ⟨ key a ∈ closure φ ⟩ → {w : V ℓ} → key a ≡ w → ⟨ w ∈ C ⟩
      inC φ a below mem q = subst (λ w → ⟨ w ∈ C ⟩) q (below (key a) mem)

      atTag : ∀ {m k : ℕ} {ar p : V ℓ} (j : ℕ) (q : V ℓ)
            → pr (# m) (VCode.mkTag j q) ≡ pr ar (pr (# k) p)
            → (j ≡ k) × ((# m ≡ ar) × (q ≡ p))
      atTag j q e = VCode.mkTag-inj (pr-inj e .snd) .fst
                  , (pr-inj e .fst , VCode.mkTag-inj (pr-inj e .snd) .snd)

      bothOf : ∀ {n m'} (φ' : Formula K n) (a b : Formula K m')
             → Below φ' → ⟨ key a ∈ closure φ' ⟩ → ⟨ key b ∈ closure φ' ⟩
             → (ar p : V ℓ) → # m' ≡ ar
             → pr VCode.⌜ mapFo f a ⌝ VCode.⌜ mapFo f b ⌝ ≡ p
             → BothSame ar p
      bothOf φ' a b below ma mb ar p qa qp u v qu =
          inC φ' a below ma (cong₂ pr qa (pr-inj (qp ∙ qu) .fst))
        , inC φ' b below mb (cong₂ pr qa (pr-inj (qp ∙ qu) .snd))

      oneOf : ∀ {n m'} (φ' : Formula K n) (a : Formula K m')
            → Below φ' → ⟨ key a ∈ closure φ' ⟩
            → (ar p : V ℓ) → # m' ≡ ar → VCode.⌜ mapFo f a ⌝ ≡ p
            → ⟨ pr ar p ∈ C ⟩
      oneOf φ' a below ma ar p qa qp = inC φ' a below ma (cong₂ pr qa qp)

      upOf : ∀ {n m'} (φ' : Formula K n) (a : Formula K (suc m'))
           → Below φ' → ⟨ key a ∈ closure φ' ⟩
           → (ar p : V ℓ) → # m' ≡ ar → VCode.⌜ mapFo f a ⌝ ≡ p
           → ⟨ pr (sucV ar) p ∈ C ⟩
      upOf φ' a below ma ar p qa qp =
        inC φ' a below ma (cong₂ pr (cong sucV qa) qp)

      sndUpOf : ∀ {n m'} (φ' : Formula K n) (t : Term K m')
                (a : Formula K (suc m'))
              → Below φ' → ⟨ key a ∈ closure φ' ⟩
              → (ar p : V ℓ) → # m' ≡ ar
              → pr VCode.⌜ mapTm f t ⌝ᵗ VCode.⌜ mapFo f a ⌝ ≡ p
              → SecondSucc ar p
      sndUpOf φ' t a below ma ar p qa qp u v qu =
        inC φ' a below ma (cong₂ pr (cong sucV qa) (pr-inj (qp ∙ qu) .snd))

      left : ∀ {n m'} (φ' : Formula K n) (a b : Formula K m')
           → ⟨ key a ∈ fst (cupʟ (sglʟ (keyS φ'))
                              (cupʟ (tree keyS a) (tree keyS b))) ⟩
      left φ' a b = Parts.left keyS φ' a b (key a) (key∈closure a)

      right : ∀ {n m'} (φ' : Formula K n) (a b : Formula K m')
            → ⟨ key b ∈ fst (cupʟ (sglʟ (keyS φ'))
                               (cupʟ (tree keyS a) (tree keyS b))) ⟩
      right φ' a b = Parts.right keyS φ' a b (key b) (key∈closure b)

      only : ∀ {n m'} (φ' : Formula K n) (a : Formula K m')
           → ⟨ key a ∈ fst (cupʟ (sglʟ (keyS φ')) (tree keyS a)) ⟩
      only φ' a = Parts.only keyS φ' a (key a) (key∈closure a)

    byTag : ∀ {m} (φ : Formula K m) (k : ℕ) (ar p : V ℓ)
          → Below φ → key φ ≡ pr ar (pr (# k) p) → Concl k ar p
    byTag (t ∈̇ u) k ar p below eq = subst (λ j → Concl j ar p)
      (atTag 0 (pr VCode.⌜ mapTm f t ⌝ᵗ VCode.⌜ mapTm f u ⌝ᵗ) eq .fst) tt*
    byTag (t ≐ u) k ar p below eq = subst (λ j → Concl j ar p)
      (atTag 1 (pr VCode.⌜ mapTm f t ⌝ᵗ VCode.⌜ mapTm f u ⌝ᵗ) eq .fst) tt*
    byTag ⊤̇ k ar p below eq = subst (λ j → Concl j ar p)
      (atTag 6 (# 0) eq .fst) tt*
    byTag ⊥̇ k ar p below eq = subst (λ j → Concl j ar p)
      (atTag 7 (# 0) eq .fst) tt*
    byTag φ@(a ∧̇ b) k ar p below eq =
      let r = atTag 2 (pr VCode.⌜ mapFo f a ⌝ VCode.⌜ mapFo f b ⌝) eq in
      subst (λ j → Concl j ar p) (r .fst)
        (bothOf φ a b below (left φ a b) (right φ a b) ar p
          (r .snd .fst) (r .snd .snd))
    byTag φ@(a ∨̇ b) k ar p below eq =
      let r = atTag 3 (pr VCode.⌜ mapFo f a ⌝ VCode.⌜ mapFo f b ⌝) eq in
      subst (λ j → Concl j ar p) (r .fst)
        (bothOf φ a b below (left φ a b) (right φ a b) ar p
          (r .snd .fst) (r .snd .snd))
    byTag φ@(a ⇒̇ b) k ar p below eq =
      let r = atTag 4 (pr VCode.⌜ mapFo f a ⌝ VCode.⌜ mapFo f b ⌝) eq in
      subst (λ j → Concl j ar p) (r .fst)
        (bothOf φ a b below (left φ a b) (right φ a b) ar p
          (r .snd .fst) (r .snd .snd))
    byTag φ@(¬̇ a) k ar p below eq =
      let r = atTag 5 VCode.⌜ mapFo f a ⌝ eq in
      subst (λ j → Concl j ar p) (r .fst)
        (oneOf φ a below (only φ a) ar p (r .snd .fst) (r .snd .snd))
    byTag φ@(∃̇ a) k ar p below eq =
      let r = atTag 8 VCode.⌜ mapFo f a ⌝ eq in
      subst (λ j → Concl j ar p) (r .fst)
        (upOf φ a below (only φ a) ar p (r .snd .fst) (r .snd .snd))
    byTag φ@(∀̇ a) k ar p below eq =
      let r = atTag 9 VCode.⌜ mapFo f a ⌝ eq in
      subst (λ j → Concl j ar p) (r .fst)
        (upOf φ a below (only φ a) ar p (r .snd .fst) (r .snd .snd))
    byTag φ@(∀̇∈ t a) k ar p below eq =
      let r = atTag 10 (pr VCode.⌜ mapTm f t ⌝ᵗ VCode.⌜ mapFo f a ⌝) eq in
      subst (λ j → Concl j ar p) (r .fst)
        (sndUpOf φ t a below (only φ a) ar p (r .snd .fst) (r .snd .snd))
    byTag φ@(∃̇∈ t a) k ar p below eq =
      let r = atTag 11 (pr VCode.⌜ mapTm f t ⌝ᵗ VCode.⌜ mapFo f a ⌝) eq in
      subst (λ j → Concl j ar p) (r .fst)
        (sndUpOf φ t a below (only φ a) ar p (r .snd .fst) (r .snd .snd))
```

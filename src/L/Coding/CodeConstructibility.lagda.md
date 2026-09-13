<!--en-->
# Constructible codes and subformula trees
<!--zh-->
# 可构造编码与子公式树
<!--ja-->
# 構成可能なコードと部分式の木
<!--/-->

<!--en-->
This chapter proves that term codes, formula codes, and finite environment graphs belong to `L`, then builds a constructible tree that gathers data over every subformula and characterizes its members.
<!--zh-->
本章证明词项编码、公式编码与有穷环境图属于 `L`，再构造一棵可构造的树，汇集每个子公式上的数据并刻画其成员。
<!--ja-->
本章では項のコード、論理式のコード、有限環境のグラフが `L` に属することを証明し、さらに各部分式上のデータを集める構成可能な木を作って、その要素を特徴づけます。
<!--/-->

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

This chapter establishes constructibility of individual codes. The set of all
codes over a constructible alphabet is constructed later as `AllCodes`{.Agda}
in `L.Coding.CodeSet`{.Agda}; it supplies the internal syntax domain needed by
the definable powerset construction.
<!--zh-->
一个码是由配对数码造出的遗传有穷集，故它理应是 `L` 的元素，而本章就这么说。证明是沿公式构造子的一次归纳，里面什么也没有；但这条陈述使后续章节能把码当作模型的寻常元素，而非当作恰好躺在那里的层级集合。

它比看上去要紧。一个在 `L` 中内化的递归，其定义域取自 `L` **诸元素**的小族，而此处那个族就是诸码；一个把码点名为常元的图，需要那个码是模型的元素，因为模型的对象语言没有别种常元。这两项要求都是这一条引理。

本章建立单个码的可构造性。可构造字母表上的全体码之集，由后面的 `L.Coding.CodeSet`{.Agda} 构造为 `AllCodes`{.Agda}，为可定义幂集的构造提供内部语法定义域。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module L.Coding.CodeConstructibility {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )

open import FOL.Syntax
  using ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.ConstantMapping using ( mapTm; mapFo )
open import V.Coding {ℓ} using ( pr; pr-inj; module VCode )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; IsOrd; Lset )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst )
open import L.Coding.Expressions {ℓ} using ( numL )
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

open hPropStructure 𝒮ʟ using ( S )
```

<!--en-->
## Constructible pairs and tags
<!--zh-->
## 可构造的有序对与标签
<!--ja-->
## 構成可能な対とタグ
<!--/-->

<!--en-->
`prL` closes constructibility under coded pairing, and `tagL` specializes it to a numeral tag. These two lemmas cover the outer shape of every syntax constructor.
<!--zh-->
`prL` 证明可构造性在编码配对下封闭，`tagL` 再把它特化为数码标签。这两条引理覆盖每个语法构造子的外层形状。
<!--ja-->
`prL` は符号化された対を作る操作について構成可能性が閉じていることを示し、`tagL` はそれを数項のタグに特殊化します。この二補題がすべての構文構成子の外形を扱います。
<!--/-->

<!--en-->
A numeral is constructible for the same reason, but the result was already used a chapter earlier, so its proof is given there. A pair is constructible because the model has pairing, and the same equation reads it back. A tag is a pair with a numeral on the left, so it is both.

Both are the same two steps: build the thing inside the model, then transport its membership along the equation saying that reading it out gives the thing.
<!--zh-->
数码的可构造性同理，但这一结果早一章就已被用到，故其证明放在那一章。有序对可构造，因为模型有配对，而同一条等式又把它读回来；标签是左边放数码的对，故两者兼得。

两者都是同样的两步：先在模型内部把它构造出来，再沿「读出来就是那个东西」这条等式把它的隶属关系搬过去。
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
## Induction over term and formula codes
<!--zh-->
## 对词项与公式编码的归纳
<!--ja-->
## 項と論理式のコードに関する帰納法
<!--/-->

<!--en-->
Assuming each constant denotes a constructible set, `codeTmL` and `codeL` prove by structural induction that every mapped term and formula code is constructible.
<!--zh-->
假设每个常元都指称一个可构造集合，`codeTmL` 与 `codeL` 通过结构归纳证明每个映射后的词项编码和公式编码都可构造。
<!--ja-->
各定数が構成可能集合を表すと仮定し、`codeTmL` と `codeL` は構造帰納法により、写像後のすべての項と論理式のコードが構成可能であることを示します。
<!--/-->

<!--en-->
Terms first. A term is a variable or a constant, and the two are the two tags that terms carry: a numeral for the variable's index, and the constant's own set for a constant. So a code is constructible provided the constants it names are, and the induction takes that as its hypothesis rather than assuming there are none.

That generality takes one extra clause and covers the parameters. A formula whose constants are members of a stage codes to a set of `L` exactly as a parameter-free one does, which is what lets the recursion below range over the formulas the constructible hierarchy is actually built from. The parameter-free case is the instance at the empty type.

Then the formulas: ten clauses with no real content. Each constructor's code is a tag on either a pair of sub-codes, a single sub-code, or a numeral, and the three blocks above cover all three shapes. The induction is over the parameter-free formula rather than its embedding, which requires no extra argument because embedding is a relabelling and commutes with every constructor definitionally.
<!--zh-->
先看词项。一个词项要么是变元，要么是常元，而两者正是词项所携带的两种标签：变元带它的索引数码，常元带它自己那个集合。因此，只要一个码所涉及的诸常元都可构造，这个码就可构造；本次归纳把这一点取作归纳假设，而不是假定根本没有常元。

这份一般性多花一条子句，换来的是对诸参数的处理。常元取自某层成员的公式，其编码与无参公式的编码一样是 `L` 的集合；正是这一点，使下面的递归得以遍历可构造层级实际由之造出的那些公式。无参情形是空类型处的实例。

然后是诸公式：十条子句，没有实质内容。每个构造子的码都是「子码之对」「单个子码」或「数码」三者之一的标签，而前面三个基础结果覆盖这三种形状。归纳沿无参公式而非它的嵌入进行，这一步不增加任何论证，因为嵌入是一次常元改名，按定义与每个构造子交换。
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
  codeL ⊥̇        = tagL 5 (numL 0)
  codeL (∃̇ φ)    = tagL 6 (codeL φ)
  codeL (∀̇ φ)    = tagL 7 (codeL φ)
  codeL (∀̇∈ t φ) = tagL 8 (prL (codeTmL t) (codeL φ))
  codeL (∃̇∈ t φ) = tagL 9 (prL (codeTmL t) (codeL φ))
```

<!--en-->
## Constructibility of environment graphs
<!--zh-->
## 环境图的可构造性
<!--ja-->
## 環境グラフの構成可能性
<!--/-->

<!--en-->
`envIsFinSet` identifies an environment graph with a finite set of coded pairs, and `envL` uses a common ordinal stage for those pairs to place the graph in `L`.
<!--zh-->
`envIsFinSet` 把环境图等同于编码有序对的有穷集，`envL` 再用包含这些有序对的共同序数层把该图放入 `L`。
<!--ja-->
`envIsFinSet` は環境グラフを符号化された対の有限集合と同一視し、`envL` はそれらの対を含む共通の順序数段階を用いてグラフを `L` に入れます。
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
一个环境是一个有穷集：键是长度以下的诸数码，条目是诸对。事实上它**恰恰就是**那些对构成的有穷集，不差分毫，因为两者是同一个被抬升的索引类型的同一个像。说明这一点只需一行，而正是这一行使有穷族引理无须任何进一步论证便可施于环境。

由此，落在某层之上的环境立刻是 `L` 的元素：它的条目是「数码与该层的成员」之对，而两者在一步之后都落在该层里。不必沿长度递归，也不必用替换。
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
<!--ja-->
## 和集合と一元集合
<!--/-->

<!--en-->
The singleton and binary-union constructors are implemented both for underlying hierarchy sets and for elements of `L`, with introduction and elimination lemmas that expose their membership.
<!--zh-->
单点集与二元并构造既在层级的底层集合上实现，也在 `L` 的元素上实现；其引入与消去引理揭示相应成员关系。
<!--ja-->
一元集合と二項和集合の構成を、階層の台となる集合と `L` の要素の双方について実装し、導入・除去補題によってその要素条件を明らかにします。
<!--/-->

<!--en-->
Two more shapes, and the model supplies both directly. A singleton is the pair of a thing with itself, and a binary union is the union of the pair, so each is the model's own operation read through the underlying set.

Each shape comes twice over. Once on the underlying set, with the two lemmas that read a member of a singleton or of a binary union back, and once on the model's own sets, where a proof of constructibility accompanies each step and the same lemmas are restated through the equation that reads the underlying set out. The recursion below runs on the second, so a set it builds is an element of `L` by construction and not by a second induction.
<!--zh-->
再来两种形状，而模型直接供给两者。单点集是一物与自身之对，二元并是那个对之并，故两者都是模型自身的运算，沿底集读出。

每种形状都做两遍。一遍在底集上进行，配两条把单元集或二元并的成员读回来的引理；另一遍在模型自己的集合上进行，此时每一步都附带可构造性的证明，而同样那些引理经由「读出底集」那条等式重述一次。下面的递归在第二遍上进行，因此它造出的集合按构造就是 `L` 的元素，无须再作归纳。
<!--/-->

```agda
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
<!--ja-->
## 部分式上の再帰
<!--/-->

<!--en-->
`tree f φ` unions the value `f χ` over every subformula `χ` of `φ`; `tree-inv` describes any member by the subformula that contributed it, while `Parts` records the forward inclusions.
<!--zh-->
`tree f φ` 对 `φ` 的每个子公式 `χ` 合并其值 `f χ`；`tree-inv` 用贡献该成员的子公式描述任意成员，而 `Parts` 记录正向包含关系。
<!--ja-->
`tree f φ` は `φ` の各部分式 `χ` に対する値 `f χ` を合併します。`tree-inv` は任意の要素を、それを供給した部分式によって記述し、`Parts` は順方向の包含を記録します。
<!--/-->

<!--en-->
One recursion over the ten constructors, with what it collects left as its
parameter. It gathers one thing per subformula: give it the key and it gives the
subformula closure of the next section, give it an entry and it gives the
satisfaction table of a later chapter. Both want the same inversion, so the
inversion is proved here once and instantiated twice.

`Of`{.Agda} says what a member of such a set is: one of the things gathered,
gathered at some subformula whose own set sits inside the one it came from.
`tree-inv`{.Agda} proves it, and `Parts`{.Agda} carries the memberships the other
direction needs, one for each shape a clause of the recursion produces.
<!--zh-->
沿十个构造子作一次递归，收集什么由参数给出。它为每条子公式收集一样东西：给它键，得到下一节那个子公式闭包；给它条目，得到后续某章那张可满足性表。两者需要的是同一次求逆，故那次求逆在此只证一次，再实例化两次。

`Of`{.Agda} 说出这种集合的成员是什么：它是被收集之物之一，收集于某条子公式处，而那条子公式自己的集合包含于它所出自的那个集合之内。`tree-inv`{.Agda} 证明这一点，而 `Parts`{.Agda} 给出另一方向所需的诸隶属关系，递归的每条子句所产生的每种形状各一条。
<!--/-->

```agda
module _ {ℓ' : Level} {K : Type ℓ'} where

  tree : (∀ {m} → Formula K m → S) → ∀ {n} → Formula K n → S
  tree f φ@(t ∈̇ u)  = sglʟ (f φ)
  tree f φ@(t ≐ u)  = sglʟ (f φ)
  tree f φ@⊥̇        = sglʟ (f φ)
  tree f φ@(a ∧̇ b)  = cupʟ (sglʟ (f φ)) (cupʟ (tree f a) (tree f b))
  tree f φ@(a ∨̇ b)  = cupʟ (sglʟ (f φ)) (cupʟ (tree f a) (tree f b))
  tree f φ@(a ⇒̇ b)  = cupʟ (sglʟ (f φ)) (cupʟ (tree f a) (tree f b))
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
    self φ@⊥̇        = sglʟ-in (f φ) _ refl
    self φ@(a ∧̇ b)  = cupʟ-inl _ _ _ (sglʟ-in (f φ) _ refl)
    self φ@(a ∨̇ b)  = cupʟ-inl _ _ _ (sglʟ-in (f φ) _ refl)
    self φ@(a ⇒̇ b)  = cupʟ-inl _ _ _ (sglʟ-in (f φ) _ refl)
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
  tree-inv f g φ@⊥̇       = one f g φ
  tree-inv f g φ@(a ∧̇ b) = bin f g φ a b (λ _ hz → hz)
                             (tree-inv f g a) (tree-inv f g b)
  tree-inv f g φ@(a ∨̇ b) = bin f g φ a b (λ _ hz → hz)
                             (tree-inv f g a) (tree-inv f g b)
  tree-inv f g φ@(a ⇒̇ b) = bin f g φ a b (λ _ hz → hz)
                             (tree-inv f g a) (tree-inv f g b)
  tree-inv f g φ@(∃̇ a)    = un f g φ a (λ _ hz → hz) (tree-inv f g a)
  tree-inv f g φ@(∀̇ a)    = un f g φ a (λ _ hz → hz) (tree-inv f g a)
  tree-inv f g φ@(∀̇∈ t a) = un f g φ a (λ _ hz → hz) (tree-inv f g a)
  tree-inv f g φ@(∃̇∈ t a) = un f g φ a (λ _ hz → hz) (tree-inv f g a)
```

<!--en-->
## The subformula closure
<!--zh-->
## 子公式闭包
<!--ja-->
## 部分式閉包
<!--/-->

<!--en-->
Specializing the generic tree to formula keys produces `closure φ`, a constructible set containing the key of `φ` and the keys of all its subformulas, together with explicit membership maps for each constructor.
<!--zh-->
把通用树特化到公式键便得到 `closure φ`：这是一个可构造集合，包含 `φ` 的键及其所有子公式的键，并为每个构造子给出显式的成员映射。
<!--ja-->
一般の木を論理式の鍵に特殊化して `closure φ` を得ます。これは `φ` の鍵と全部分式の鍵を含む構成可能集合であり、各構成子について明示的な要素写像を備えます。
<!--/-->

<!--en-->
A recursion on codes is stated against a *slot*: a set of codes closed under immediate subcodes, holding the one the recursion is asked about. The smallest such slot is the set of codes of a formula's own subformulas, and it is the recursion above taken at the key.

Each entry carries its arity, because the recursion's own key does; a binder's subformula therefore enters at the successor. This is the only place where a change of arity appears explicitly, and it appears there because the arity is exactly what the frames bind.

Constructibility is not a second proof. The recursion above runs on the model's own sets, so the certificate comes out of it together with the set.
<!--zh-->
对码的递归是相对某个**槽**陈述的：一个对直接子码封闭、且装着被问及的那个码的码集。最小的这种槽，就是一条公式自身诸子公式的码集，而它就是上面那个递归在键处的取值。

每个条目都携带元数，因为递归的键本身包含元数。因此，绑定子的子公式在后继元数处进入定义域。这是元数变化唯一显式出现的地方，因为各个框架正是按元数绑定相应数据。

可构造性无须另证：上面的递归在模型自身的集合上进行，证书随之一并给出。
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
<!--ja-->
## まとめ
<!--/-->

<!--en-->
The results place syntax codes, environments, and subformula-indexed collections inside `L`; the remaining lemmas turn closure membership back into a concrete subformula key for later bounded recursion.
<!--zh-->
这些结果把语法编码、环境及按子公式索引的汇集都放进 `L`；余下引理把闭包成员还原为具体的子公式键，供后面的有界递归使用。
<!--ja-->
以上により、構文コード、環境、部分式で添字づけられた集まりが `L` に入ります。残る補題は閉包の要素を具体的な部分式の鍵へ戻し、後の有界再帰に備えます。
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

`envL`{.Agda} 随后把一个环境放进 `L`，既不沿长度递归，也不用替换，因为一个环境恰恰就是它的诸条目构成的有穷集。`closure`{.Agda} 是「对一个码的递归」所能相对陈述的最小的槽，而 `closureL`{.Agda} 把它的证书从造出它的那个递归上读下来，不必再证第二次。

全体码之集仍然不是 `L` 的元素，也仍然不需要是。
<!--/-->

<!--en-->
## Reading a closure back
<!--zh-->
## 把闭包读回来
<!--ja-->
## 閉包の要素を読み戻す
<!--/-->

<!--en-->
`closure-inv` applies the generic tree inversion to show that every member of `closure φ` is the key of some subformula whose closure embeds into that of `φ`.
<!--zh-->
`closure-inv` 应用通用的树反演，证明 `closure φ` 的每个成员都是某个子公式的键，且该子公式的闭包嵌入 `φ` 的闭包。
<!--ja-->
`closure-inv` は一般の木の反転を適用し、`closure φ` の各要素が、閉包から `φ` の閉包への包含をもつある部分式の鍵であることを示します。
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
对码进行递归时，必须具体知道定义域中的元素来自哪些公式。下面的引理给出所需刻画：闭包的每个元素都是某条公式的键，并且该公式自身的闭包包含在原公式的闭包中。后一个包含关系正是归纳所需的条件，它保证归纳假设在处理相应子公式时可用。

这条结论与「键属于自身闭包」都直接来自上面递归在键处的两条读式，因此这里都不需要新的归纳。
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
## Recovering a formula from its key
<!--zh-->
## 从公式键恢复公式
<!--ja-->
## 論理式の鍵から論理式を復元する
<!--/-->

<!--en-->
When a set is known to equal the key of a formula, the final lemma transports that witness into an explicit formula and retains the inclusion of its closure into the original closure.
<!--zh-->
已知某集合等于一个公式键时，最后的引理把该见证转化为一个显式公式，并保留其闭包到原闭包的包含关系。
<!--ja-->
ある集合が論理式の鍵に等しいと分かっているとき、最後の補題はその証拠を明示的な論理式へ移し、その閉包から元の閉包への包含も保ちます。
<!--/-->

<!--en-->
The demand a closedness predicate makes is indexed by a constructor tag, and the
formula it is made of is indexed by a constructor. Matching the two is the only
real work in the first instance, and doing it clause by clause would be ten
formulas times seven demands. It is not, because the demand can be *computed*
from the tag: one type family over the tag, one function over the formula, and
the equation between tags that the key's injectivity yields carries the second to
the first.

Below the tag, a key is an arity paired with a code, and both layers are pinned
by pairing's injectivity. What comes out is that an arity-preserving constructor
demands its components at the arity read, an arity-raising one demands them at
the successor, and a constructor with no subformula demands nothing.
<!--zh-->
封闭性谓词提的要求以构造子标签为索引，而它所谈论的公式以构造子为索引。把这两者对上，是第一个实例里唯一真正的活；而逐条去做会是十条公式乘七项要求。不必如此，因为那项要求可以从标签**算**出来：一个以标签为索引的类型族、一个以公式为索引的函数，而键的单射性所给出的那条标签等式把后者搬到前者上。

在标签之下，一个键是元数与码之对，这两层都由配对的单射性确定。由此得出：保持元数的构造子在所读出的元数处要求其诸分量，抬升元数的在后继处要求分量，而没有子公式的构造子则不要求任何分量。
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
    Concl 6 ar p = ⟨ pr (sucV ar) p ∈ C ⟩
    Concl 7 ar p = ⟨ pr (sucV ar) p ∈ C ⟩
    Concl 8 ar p = SecondSucc ar p
    Concl 9 ar p = SecondSucc ar p
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
    byTag ⊥̇ k ar p below eq = subst (λ j → Concl j ar p)
      (atTag 5 (# 0) eq .fst) tt*
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
    byTag φ@(∃̇ a) k ar p below eq =
      let r = atTag 6 VCode.⌜ mapFo f a ⌝ eq in
      subst (λ j → Concl j ar p) (r .fst)
        (upOf φ a below (only φ a) ar p (r .snd .fst) (r .snd .snd))
    byTag φ@(∀̇ a) k ar p below eq =
      let r = atTag 7 VCode.⌜ mapFo f a ⌝ eq in
      subst (λ j → Concl j ar p) (r .fst)
        (upOf φ a below (only φ a) ar p (r .snd .fst) (r .snd .snd))
    byTag φ@(∀̇∈ t a) k ar p below eq =
      let r = atTag 8 (pr VCode.⌜ mapTm f t ⌝ᵗ VCode.⌜ mapFo f a ⌝) eq in
      subst (λ j → Concl j ar p) (r .fst)
        (sndUpOf φ t a below (only φ a) ar p (r .snd .fst) (r .snd .snd))
    byTag φ@(∃̇∈ t a) k ar p below eq =
      let r = atTag 9 (pr VCode.⌜ mapTm f t ⌝ᵗ VCode.⌜ mapFo f a ⌝) eq in
      subst (λ j → Concl j ar p) (r .fst)
        (sndUpOf φ t a below (only φ a) ar p (r .snd .fst) (r .snd .snd))
```

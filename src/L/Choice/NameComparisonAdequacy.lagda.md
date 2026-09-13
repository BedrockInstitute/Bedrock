<!--en-->
# Adequacy of name comparison
<!--zh-->
# 名字比较的充分性
<!--ja-->
# 名前の比較の妥当性
<!--/-->

<!--en-->
This chapter proves that the object-language step describes the meta-language
name comparison exactly, by reconstructing parameter vectors, denotations, and
least names in both directions.
<!--zh-->
本章证明对象语言中的步进恰好描述元语言中的名字比较，办法是双向重构参数向量、指称与最小名字。
<!--ja-->
本章では、対象言語のステップがメタ言語の名前比較を正確に記述することを、パラメータ・ベクトル、表示、最小の名前を双方向に復元して証明する。
<!--/-->

<!--en-->
The order at every stage is an object of `L`, and the description that carves it
is faithful except at one place: the step at a single carrier. That is the last
mathematical obligation on this chain, and it is bookkeeping against chapters
that already exist. The naming chapter built the names and their order; the
previous chapters described a name at slots and proved the order description
adequate against the naming chapter's comparison. What is missing is the bridge
between the two ends of a **name** itself: the parameter sequence a description
carries is a vector of the meta-language, the denotation a description asserts is
the set the meta name denotes, and the least of the described names is the least
of the meta ones.

Six pieces, each feeding the next, and none of them a new idea.
<!--zh-->
每层上的序已经是 `L` 的对象，描述该序的公式也已在各处证明忠实，只缺单个载体上的步进充分性。这是整条构造链最后尚未完成的数学步骤，需要组合已有章节的结果。命名章构造名字及其序；前几章在槽位上描述名字，并证明序描述与命名章的比较适足。剩余工作是建立一个**名字**在两种表示之间的对应：描述携带的参数序列对应元语言向量，描述断言的指称对应元层面名字所指称的集合，而描述名字中的最小者对应元层面名字中的最小者。

这六件事层层递进，每一件都要用到前一件，而且没有一件是新想法。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module L.Choice.NameComparisonAdequacy {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import FOL.Manipulation.ConstantMapping using ( mapFo; mapFo-comp; embed )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Coding {ℓ} using ( pr; module VCode )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Ordinal {ℓ} using ( #∈ω; ω-ord )
open import L.Axioms.Basic {ℓ} using ( ∅ʟ; LsetS )
open import L.Coding.Environment {ℓ} using ( env )
open import L.Coding.Model {ℓ} using ( envOverAt; envOverAt-transport; domAt )
open import L.Coding.Expressions {ℓ} using ( extAt-in; extAt-out; numL; consAtL )
open import L.Coding.EnvironmentSet {ℓ} lem using ( module Recover; envS; envOver )
open import L.Coding.SatisfactionGraph {ℓ} lem using ( satGraphAt )
open import L.Coding.Satisfaction {ℓ} lem using ( Sat )
open import L.Coding.SatisfactionBridge {ℓ} lem
  using ( consAtL-in; consAtL-out; asConst; values; envFor; envFor-graph )
  renaming ( graph to envGraph )
open import L.Coding.CodeSet {ℓ} lem using ( keyS; AllCodes )
open import L.Coding.UniformSatisfaction {ℓ} lem
  using ( val-at; val-sat; keyIn; keyIn≡; keyIn∈; module Table )
open import L.Choice.CanonicalNames {ℓ} lem using ( module Naming; limitCode )
open import L.Choice.FiniteStageOrders {ℓ} lem using ( Limit; limitOrder )
open import L.Choice.NameComparison {ℓ} lem
  using ( NameAt; NameAt-in; LeastNameAt; ≺At; StepAt; StepOf; StepAt-in; StepAt-out; DenoteOf; DenoteBody; DenoteBody-in; DenoteBody-out
        ; FreeAt; codeFree-in; codeFree-out
        ; graphAt-value; graphAt-only
        ; domAt-numeral; domAt-fill; module Adequacy )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO )

open import Cubical.Data.Vec.Properties using ( FinVec→Vec; FinVec→Vec→FinVec )
open import Cubical.Data.Vec using ( map )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Foundations.Transport using ( constSubstCommSlice )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_; ω )

open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## One lemma about vectors

<!--zh-->
## 关于向量的一条引理
<!--ja-->
## ベクトルに関する一つの補題
<!--/-->

<!--en-->
The two helper equalities identify vectors with their index families before the
proof repeatedly crosses between those presentations.
<!--zh-->
两条辅助等式把向量与其索引族对应起来，供后文反复在这两种呈现之间往返。
<!--ja-->
二つの補助等式はベクトルとその添字族を同一視し、後の証明で二つの提示の間を繰り返し往復できるようにする。
<!--/-->

<!--en-->

Everything below moves between a vector of the meta-language and a family
indexed by the arity, so the two directions of that move are named once. A
relabelled vector is read off index by index, which is one induction; and the
round trip from a family to a vector and back is the library's, applied.
<!--zh-->

下文一切都在「元语言的一个向量」与「以元数为索引的一个族」之间来回，故这次来回的两个方向只点名一遍。其中一个方向把向量逐序号读出，这是一次归纳；而「族到向量再回来」的那次往返由库给出，直接施用。
<!--/-->

```agda
private
  sh2 : ∀ {n} → Fin n → Fin (suc (suc n))
  sh2 i = suc (suc i)

  sh3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  sh3 i = suc (suc (suc i))

  sh5 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc n)))))
  sh5 i = suc (suc (suc (suc (suc i))))

  sh6 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc (suc n))))))
  sh6 i = suc (suc (suc (suc (suc (suc i)))))

  s6a a6a e6a s6b a6b e6b : ∀ {n} → Fin (suc (suc (suc (suc (suc (suc n))))))
  s6a = suc (suc (suc (suc (suc zero))))
  a6a = suc (suc (suc (suc zero)))
  e6a = suc (suc (suc zero))
  s6b = suc (suc zero)
  a6b = suc zero
  e6b = zero

lookup-map : {ℓ' ℓ'' : Level} {X : Type ℓ'} {Y : Type ℓ''} (f : X → Y)
             {k : ℕ} (v : Vec X k) (i : Fin k)
           → lookup i (map f v) ≡ f (lookup i v)
lookup-map f (x ∷ v) zero    = refl
lookup-map f (x ∷ v) (suc i) = lookup-map f v i

lookup-tab : {ℓ' : Level} {X : Type ℓ'} {k : ℕ} (g : Fin k → X) (i : Fin k)
           → lookup i (FinVec→Vec g) ≡ g i
lookup-tab g i j = FinVec→Vec→FinVec g j i
```

<!--en-->
## The chapter's frame

<!--zh-->
## 本章的框架
<!--ja-->
## 本章のフレーム
<!--/-->

<!--en-->
The frame fixes the carrier and its well-order and assumes bidirectional
readings for the two relation slots used by the name description.
<!--zh-->
本章的框架固定载体及其上的良序，并假设名字描述所用的两个关系槽位各自配有双向读式。
<!--ja-->
このフレームは台とその整列順序を固定し、名前の記述が使う二つの関係スロットについて双方向の読みを仮定する。
<!--/-->

<!--en-->

Everything is relative to the carrier the names are written over, its
constructibility, and the well-order of its members, which is the naming
chapter's own telescope. Two of the three keys reach the description as slots
holding relations, so they arrive here the way the previous chapter's adequacy
takes them: as sets with their two readings, in both directions.
<!--zh-->

一切都相对于「诸名字据以写出的载体」、它的可构造性，以及它的诸成员上的良序，而那正是命名那一章给出的那条模块序列。三个键里有两个以「持有关系的位」的身份进入描述，故它们在此处出现的方式，与上一章的充分性取用它们的方式相同：作为集合，连同两个方向的读式。
<!--/-->

```agda
module At (A : V ℓ) (pA : ⟨ isL A ⟩) (w : SWO ⟪ A ⟫) where
  private
    Aʟ : S
    Aʟ = A , pA

    module NM = Naming A w

  open Adequacy A pA w using ( ix; pfam; module Keys )
  open NM using
    ( Name; arity; formula; params; codeOf; denote; environment
    ; _≺ₙ_ )
```

<!--en-->
## The parameter sequence, filled in

<!--zh-->
## 参数序列，填进去
<!--ja-->
## パラメータ列を埋める
<!--/-->

<!--en-->
`paramSeq-in`{.Agda} turns a name's parameter vector into the environment graph
whose domain is its arity and whose values lie in the carrier.
<!--zh-->
`paramSeq-in`{.Agda} 把名字的参数向量变成环境图，其定义域是元数，取值都落在载体中。
<!--ja-->
`paramSeq-in`{.Agda} は名前のパラメータ・ベクトルを、定義域がアリティで値が台に属する環境グラフへ変換する。
<!--/-->

<!--en-->

A name's parameters are a vector over the carrier, and the description says of
the slot holding them that it is an environment over the carrier whose domain is
the arity. That is the model chapter's four conjuncts, and each is the family the
vector gives read at a **variable** slot: single-valuedness is the graph's
functionality, the domain is the numeral of the length, the values lie in the
carrier because they are its members by construction, and every member is a pair
because every member of a graph is one.
<!--zh-->

一个名字的参数是载体之上的一个向量，而那条描述要求持有它们的那一位是载体之上、定义域为元数的一个环境。这正是模型那一章的四个合取项，每一条都对应「那个向量给出的族」读在一个**变元**位上：单值性即那张图的函数性，定义域即长度的数码，诸取值落在载体中，因为它们按构造就是载体的成员；每个成员都是一个对，因为一张图的每个成员都是。
<!--/-->

```agda
  paramSeq-in : ∀ {n} (e a B : Fin n) (γ : S ^ n) (k : ℕ) (g : Fin k → ⟪ A ⟫)
              → fst (lookup e γ) ≡ env (λ i → ix (g i))
              → fst (lookup a γ) ≡ # k
              → fst (lookup B γ) ≡ A
              → ⟨ γ ⊨ envOverAt e a B ⟩
  paramSeq-in e a B γ k g qe qa qB =
    envOverAt-transport (Aʟ ∷ (# k , numL k) ∷ envS Aʟ g ∷ []) γ
      (suc (suc zero)) (suc zero) zero e a B
      (sym qe) (sym qa) (sym qB) (envOver Aʟ g)
```

<!--en-->
## And read back as a vector

<!--zh-->
## 又被读回成一个向量
<!--ja-->
## ベクトルとして読み戻す
<!--/-->

<!--en-->
`paramSeq-out`{.Agda} recovers an untruncated parameter vector from any
single-valued environment graph with the required finite domain.
<!--zh-->
`paramSeq-out`{.Agda} 从定义域正确的任意单值环境图中，无截断地恢复参数向量。
<!--ja-->
`paramSeq-out`{.Agda} は、所定の有限な定義域をもつ任意の単値環境グラフから、命題的切り詰めなしにパラメータ・ベクトルを復元する。
<!--/-->

<!--en-->

The other direction is the environment-set chapter's own recovery, applied at
this carrier and turned into a vector. Nothing is truncated: the entry at an
index is a proposition, because the domain conjunct says there is one and
single-valuedness says there is at most one, and the index of a value is read off
the carrier's own fibres, which are not truncated either. So the parameters come
back as data, which is what a name is made of.
<!--zh-->

另一个方向是把环境那一章的恢复操作施用在这个载体上，再把它读回成一个向量。什么也不截断：某个序号处的条目是一个命题，因为定义域条款说「有一个」，单值性说「至多一个」；而取值的索引则从载体自身的纤维读出，那些纤维同样不截断。故诸参数作为数据被读回，而名字正是由这些数据造成的。
<!--/-->

```agda
  module _ {n : ℕ} (e a B : Fin n) (γ : S ^ n) (k : ℕ)
           (qa : fst (lookup a γ) ≡ # k) (qB : fst (lookup B γ) ≡ A)
           (h : ⟨ γ ⊨ envOverAt e a B ⟩) where
    private
      module R = Recover Aʟ k γ e a B qa qB h

    paramSeq-out : Vec ⟪ A ⟫ k
    paramSeq-out = FinVec→Vec R.g

    paramSeq-graph : fst (lookup e γ)
                   ≡ env (λ i → ix (lookup i paramSeq-out))
    paramSeq-graph = R.recovers
                   ∙ cong env (funExt (λ i → cong ix (sym (lookup-tab R.g i))))
```

<!--en-->
## Four elements, sealed where they are made

<!--zh-->
## 四个元素，在造出之处封印
<!--ja-->
## 四つの要素を構成箇所で不透明化する
<!--/-->

<!--en-->
The denotation proof packages the extended environment, its length numeral, its
key, and the graph value as sealed elements with exactly the equations later
satisfaction proofs consume.
<!--zh-->
指称证明把扩张环境、其长度数码、其键与图的取值封装为被封印的元素，并恰好暴露后续满足关系证明所需的等式。
<!--ja-->
表示の証明は、拡張環境、その長さの数項、鍵、グラフの値を不透明な要素としてまとめ、後の充足関係の証明が使う等式だけを公開する。
<!--/-->

<!--en-->

The denotation conjunct binds four sets, and a proof that the conjunct holds has
to supply them. Each is a construction, and each reaches a slot **inside** a
satisfaction, which is the situation the previous chapters measured twice: the
extended environment as an element of `L`, the numeral of its length, the key the
length and the skeleton make, and the table's value at that key. So all four are
sealed where they are built, and what the seal exposes is exactly the equations
the description consumes.
<!--zh-->

指称那个合取项绑定四个集合，「该合取项成立」的证明必须提供这四个集合。每一个都是一次构造，每一个都要进入满足关系**内部**的一个槽位；这正是前几章两次遇到的处境：作为 `L` 之元素的扩张后环境、其长度的数码、由长度与骨架造出的键，以及表在该键处的取值。故四者都在被造出之处封印，而封印所暴露的，恰是那条描述所用的诸等式。
<!--/-->

Perf: the four elements the denotation conjunct is satisfied at are sealed, for
the reason the two chapters before this one measured.

```agda
  opaque
    envAt : Name → ⟪ A ⟫ → S
    envAt t m = envFor Aʟ (environment t m)

    envAt-fst : (t : Name) (m : ⟪ A ⟫)
              → fst (envAt t m) ≡ envGraph Aʟ (environment t m)
    envAt-fst t m = envFor-graph Aʟ (environment t m)

    numAt : ℕ → S
    numAt j = # j , numL j

    numAt-fst : (j : ℕ) → fst (numAt j) ≡ # j
    numAt-fst j = refl

    keyAt : Name → S
    keyAt t = keyIn Aʟ (embed (formula t))

    keyAt-fst : (t : Name)
              → fst (keyAt t) ≡ fst (keyS Aʟ (embed (formula t)))
    keyAt-fst t = keyIn≡ Aʟ (embed (formula t))

    keyAt-∈ : (t : Name) → ⟨ keyAt t ∈ˢ AllCodes Aʟ ⟩
    keyAt-∈ t = keyIn∈ Aʟ (embed (formula t))

    valAt : Name → S
    valAt t = Table.val Aʟ Aʟ (keyAt t) (keyAt-∈ t)

    valAt-val : (t : Name) → valAt t ≡ Table.val Aʟ Aʟ (keyAt t) (keyAt-∈ t)
    valAt-val t = refl
```

<!--en-->
## What the key of a name's formula is

<!--zh-->
## 一个名字的公式之键是什么
<!--ja-->
## 名前の論理式の鍵
<!--/-->

<!--en-->
For a parameter-free formula, relabelling along the carrier embedding leaves
the code unchanged, so the code-set key equals the arity-and-skeleton key used
by the description.
<!--zh-->
对无参公式，沿载体嵌入的常元改名不改变其码，故码集之键等于描述所用的元数与骨架之键。
<!--ja-->
無パラメータ論理式では、台の埋め込みに沿う定数の改名が符号を変えないため、符号集合の鍵は記述が使うアリティと骨格の鍵に等しい。
<!--/-->

<!--en-->

The skeleton slot holds the code of a parameter-free formula, and the key the
description builds from it is the arity numeral paired with that code. The code
set's own key is the code of the formula relabelled along the carrier's
embedding, and a parameter-free formula's relabelling is itself, because both
readings of its constants are functions out of the empty type. So the two keys
are the same set, and saying so is one congruence.
<!--zh-->

骨架那一位持有一条无参公式的码，而这条描述由它造出的键，是元数数码与那条码之对。码集本身的键，是那条公式沿载体嵌入并经常元改名后所得的码；而一条无参公式经常元改名后仍是它自己，因为它的常元的两种读法都是从空类型出发的函数。故两个键是同一个集合，说出这句话本身就是一次同余。
<!--/-->

```agda
  private
    sameEmbed : ∀ {m} (χ : Formula (⊥* {ℓ}) m)
              → mapFo ⟪ A ⟫↪ (embed χ) ≡ embed χ
    sameEmbed χ = mapFo-comp Empty.rec* ⟪ A ⟫↪ χ
                ∙ cong (λ f → mapFo f χ) (funExt (λ b → Empty.rec* b))

    keyCode : ∀ {m} (χ : Formula (⊥* {ℓ}) m)
            → fst (keyS Aʟ (embed χ)) ≡ pr (# m) (fst (limitCode χ))
    keyCode χ = cong (λ u → pr (# _) VCode.⌜ u ⌝) (sameEmbed χ)

    valuesOf : (t : Name)
             → env (pfam t) ≡ envGraph Aʟ (map NM.DA.ι (params t))
    valuesOf t = cong env (funExt (λ i →
      sym (cong fst (lookup-map NM.DA.ι (params t) i))))

    valuesL : (t : Name) (m : ⟪ A ⟫) (i : Fin (suc (arity t)))
            → ⟨ isL (values Aʟ (environment t m) i) ⟩
    valuesL t m i =
      isL-trans (snd (lookup i (environment t m))) pA
```

<!--en-->
## The denotation, both ways

<!--zh-->
## 指称，两个方向
<!--ja-->
## 表示を双方向に読む
<!--/-->

<!--en-->
The two denotation lemmas identify the set in the description's denotation slot
with the set denoted by the corresponding meta-language name.
<!--zh-->
两条指称引理把描述的指称位中所持集合，与相应元语言名字所指称的集合对应起来。
<!--ja-->
二つの表示補題は、記述の表示スロットにある集合と、対応するメタ言語の名前が表示する集合を同一視する。
<!--/-->

<!--en-->

A description is faithful at its denotation slot when the set the slot holds is
the set the meta name denotes. Both directions are the same chain read forwards
and backwards, and the chain has four links: the extended environment is the
member pushed onto the parameters, its length is the arity plus one, the key is
that length paired with the skeleton, and the value the graph assigns at that key
is satisfaction over the carrier. The naming chapter's composite denotation
equation is the last link, and it is the only one with mathematics in it.

Two of the links are stated at the carrier the module is written over and reached
at the carrier a slot holds, so the formula travels along an equality of
carriers. That travel is a path induction, written once for the key and once for
the value, and it is the whole cost of letting the carrier be a slot.
<!--zh-->

一条描述在它的指称位上忠实，是指那一位所持有的集合就是元层面那个名字所指称的集合。两个方向是同一条链的正读与反读，而这条链有四环：扩张后的环境是被推到诸参数前面的那个成员，它的长度是元数加一，键是那个长度与骨架之对，而图在那个键处所指派的取值就是载体之上的满足关系。命名那一章的复合指称等式是最后一环，也是唯一涉及数学内容的一环。

其中两环陈述在本模块据以写出的那个载体上，却在「一位所持有的载体」处被取用，故那条公式要沿载体之间的一条等式转换；这次转换是一次路径归纳，对键做一遍、对取值做一遍，而这就是「让载体成为一位」所需的全部。
<!--/-->

```agda
  private
    denoteMem : (t : Name) (y : V ℓ) → ⟨ y ∈ denote t ⟩ → ⟨ y ∈ A ⟩
    denoteMem t y = PT.rec (snd (y ∈ A)) step
      where
      step : Σ[ p ∈ Σ[ mm ∈ ⟪ A ⟫ ] ⟨ NM.satAt t mm ⟩ ] (⟪ A ⟫↪ (p .fst) ≡ y)
           → ⟨ y ∈ A ⟩
      step (p , q) = subst (λ u → ⟨ u ∈ A ⟩) q
        (∈∈ₛ {a = ⟪ A ⟫↪ (p .fst)} {b = A} .snd (∈ₛ⟪ A ⟫↪ (p .fst)))

  module Named {n : ℕ} (B C C₀ s a e d : Fin n) (γ : S ^ n)
               (qB : lookup B γ ≡ Aʟ)
               (qC : fst (lookup C γ) ≡ fst (AllCodes Aʟ))
               (q₀ : fst (lookup C₀ γ) ≡ fst (AllCodes ∅ʟ)) where
    private
      Fo : S → ℕ → Type ℓ
      Fo X j = Formula ⟪ fst X ⟫ j

      ψAt : (t : Name) → Fo (lookup B γ) (suc (arity t))
      ψAt t = subst (λ X → Fo X (suc (arity t))) (sym qB) (embed (formula t))

      keyψ : (t : Name)
           → fst (keyS (lookup B γ) (ψAt t))
           ≡ fst (keyS Aʟ (embed (formula t)))
      keyψ t = sym (constSubstCommSlice (λ X → Fo X (suc (arity t))) (V ℓ)
        (λ X ψ → fst (keyS X ψ)) (sym qB) (embed (formula t)))

      satψ : (t : Name)
           → fst (Sat (lookup B γ) (mapFo (asConst (lookup B γ)) (ψAt t)))
           ≡ fst (Sat Aʟ (mapFo (asConst Aʟ) (embed (formula t))))
      satψ t = sym (constSubstCommSlice (λ X → Fo X (suc (arity t))) (V ℓ)
        (λ X ψ → fst (Sat X (mapFo (asConst X) ψ)))
        (sym qB) (embed (formula t)))

    Data : Name → Type (ℓ-suc ℓ)
    Data t = (fst (lookup s γ) ≡ fst (codeOf t))
           × ( (fst (lookup a γ) ≡ # (arity t))
             × ( (fst (lookup e γ) ≡ env (pfam t))
               × (fst (lookup d γ) ≡ denote t) ) )

    module Body (t : Name) (qs : fst (lookup s γ) ≡ fst (codeOf t))
                (qa : fst (lookup a γ) ≡ # (arity t))
                (qe : fst (lookup e γ) ≡ env (pfam t)) where
      private
        δp : Vec NM.DA.SM (arity t)
        δp = map NM.DA.ι (params t)

        qd' : fst (lookup e γ) ≡ envGraph Aʟ δp
        qd' = qe ∙ valuesOf t

        qkey : fst (keyAt t)
             ≡ pr (fst (numAt (suc (arity t)))) (fst (lookup s γ))
        qkey = keyAt-fst t ∙ keyCode (formula t)
             ∙ cong (pr (# (suc (arity t)))) (sym qs)
             ∙ cong (λ u → pr u (fst (lookup s γ)))
                 (sym (numAt-fst (suc (arity t))))

      denote-fill : (z : S) (m : ⟪ A ⟫) → ⟪ A ⟫↪ m ≡ fst z
                  → ⟨ ⟪ A ⟫↪ m ∈ denote t ⟩ → DenoteOf B C s e γ z
      denote-fill z m qm hz =
        envAt t m , (numAt (suc (arity t)) , (keyAt t , (valAt t
        , ( hcons , (hdom , (hkey , (qkey , (hgraph , hmem))))))))
        where
        hcons : ⟨ (envAt t m ∷ z ∷ γ) ⊨ consAtL zero (suc zero) (sh2 e) ⟩
        hcons = consAtL-in Aʟ δp (NM.DA.ι m) (envAt t m ∷ z ∷ γ)
                  zero (suc zero) (sh2 e) qd' (sym qm) (envAt-fst t m)

        hdom : ⟨ (numAt (suc (arity t)) ∷ envAt t m ∷ z ∷ γ)
                 ⊨ domAt (suc zero) zero ⟩
        hdom = domAt-fill (suc zero) zero
                 (numAt (suc (arity t)) ∷ envAt t m ∷ z ∷ γ)
                 (suc (arity t)) (values Aʟ (environment t m)) (valuesL t m)
                 (envAt-fst t m) (numAt-fst (suc (arity t)))

        hkey : ⟨ fst (keyAt t) ∈ fst (lookup C γ) ⟩
        hkey = subst (λ u → ⟨ fst (keyAt t) ∈ u ⟩) (sym qC) (keyAt-∈ t)

        hgraph : ⟨ (valAt t ∷ keyAt t ∷ numAt (suc (arity t)) ∷ envAt t m
                    ∷ z ∷ γ) ⊨ satGraphAt (sh5 B) (suc zero) zero ⟩
        hgraph = graphAt-value (sh5 B) (suc zero) zero
                   (valAt t ∷ keyAt t ∷ numAt (suc (arity t)) ∷ envAt t m
                    ∷ z ∷ γ) (ψAt t)
                   (keyAt-fst t ∙ sym (keyψ t))
                   ( cong fst (valAt-val t)
                   ∙ cong fst (val-at Aʟ Aʟ (embed (formula t))
                                 (keyAt t) (keyAt-∈ t) (keyAt-fst t))
                   ∙ sym (satψ t) )

        hmem : ⟨ fst (envAt t m) ∈ fst (valAt t) ⟩
        hmem = subst (λ u → ⟨ envAt t m ∈ˢ u ⟩) (sym (valAt-val t)) inTable
          where
          inner : ⟨ NM.DA._⊨ᵐ_ (environment t m) (embed (formula t)) ⟩
          inner = subst ⟨_⟩ (NM.denote-mem t m) hz

          inTable : ⟨ envAt t m ∈ˢ Table.val Aʟ Aʟ (keyAt t) (keyAt-∈ t) ⟩
          inTable = subst ⟨_⟩
            (sym (val-sat Aʟ (embed (formula t)) (keyAt t) (keyAt-∈ t)
                    (keyAt-fst t) (environment t m) (envAt t m)
                    (envAt-fst t m))) inner

      denote-read : (z : S) (m : ⟪ A ⟫) → ⟪ A ⟫↪ m ≡ fst z
                  → DenoteOf B C s e γ z → ⟨ ⟪ A ⟫↪ m ∈ denote t ⟩
      denote-read z m qm (c , (k , (key , (v , (hc , (hk , (hi , (hp , (hg , hm)))))))))
        = subst ⟨_⟩ (sym (NM.denote-mem t m)) inner
        where
        qcg : fst c ≡ envGraph Aʟ (environment t m)
        qcg = consAtL-out Aʟ δp (NM.DA.ι m) (c ∷ z ∷ γ)
                zero (suc zero) (sh2 e) qd' (sym qm) hc

        qk : fst k ≡ # (suc (arity t))
        qk = domAt-numeral (suc zero) zero (k ∷ c ∷ z ∷ γ) (suc (arity t))
               (values Aʟ (environment t m)) (valuesL t m) qcg hk

        qkey' : fst key ≡ fst (keyS Aʟ (embed (formula t)))
        qkey' = hp ∙ cong (λ u → pr u (fst (lookup s γ))) qk
              ∙ cong (pr (# (suc (arity t)))) qs ∙ sym (keyCode (formula t))

        key∈ : ⟨ key ∈ˢ AllCodes Aʟ ⟩
        key∈ = subst (λ u → ⟨ fst key ∈ u ⟩) qC hi

        qval : fst v ≡ fst (Table.val Aʟ Aʟ key key∈)
        qval = graphAt-only (sh5 B) (suc zero) zero
                 (v ∷ key ∷ k ∷ c ∷ z ∷ γ) (ψAt t) (qkey' ∙ sym (keyψ t)) hg
             ∙ satψ t
             ∙ sym (cong fst (val-at Aʟ Aʟ (embed (formula t)) key key∈ qkey'))

        inTable : ⟨ c ∈ˢ Table.val Aʟ Aʟ key key∈ ⟩
        inTable = subst (λ u → ⟨ fst c ∈ u ⟩) qval hm

        inner : ⟨ NM.DA._⊨ᵐ_ (environment t m) (embed (formula t)) ⟩
        inner = subst ⟨_⟩
          (val-sat Aʟ (embed (formula t)) key key∈ qkey'
             (environment t m) c qcg) inTable

      member-fill : (z : S) → ⟨ fst z ∈ denote t ⟩
                  → ⟨ fst z ∈ fst (lookup B γ) ⟩ × DenoteOf B C s e γ z
      member-fill z hz = subst (λ u → ⟨ fst z ∈ u ⟩) (sym (cong fst qB)) hA
        , denote-fill z (fib .fst) (fib .snd)
            (subst (λ u → ⟨ u ∈ denote t ⟩) (sym (fib .snd)) hz)
        where
        hA : ⟨ fst z ∈ A ⟩
        hA = denoteMem t (fst z) hz
        fib : Σ[ mm ∈ ⟪ A ⟫ ] (⟪ A ⟫↪ mm ≡ fst z)
        fib = ∈-asFiber {a = fst z} {b = A} hA

      member-read : (z : S) → ⟨ fst z ∈ fst (lookup B γ) ⟩
                  → DenoteOf B C s e γ z → ⟨ fst z ∈ denote t ⟩
      member-read z hz hDen = subst (λ u → ⟨ u ∈ denote t ⟩) (fib .snd)
        (denote-read z (fib .fst) (fib .snd) hDen)
        where
        fib : Σ[ mm ∈ ⟪ A ⟫ ] (⟪ A ⟫↪ mm ≡ fst z)
        fib = ∈-asFiber {a = fst z} {b = A}
          (subst (λ u → ⟨ fst z ∈ u ⟩) (cong fst qB) hz)
```

<!--en-->
## A name, assembled

<!--zh-->
## 一个名字，装配起来
<!--ja-->
## 名前を組み立てる
<!--/-->

<!--en-->
`NameAt-fill`{.Agda} assembles the five object-language conjuncts from a meta
name, while `NameAt-read`{.Agda} recovers its formula, arity, parameters, and
denotation.
<!--zh-->
`NameAt-fill`{.Agda} 从一个元层面名字装配五个对象语言合取项，而 `NameAt-read`{.Agda} 读回其公式、元数、参数与指称。
<!--ja-->
`NameAt-fill`{.Agda} はメタ言語の名前から五つの対象言語の連言を組み立て、`NameAt-read`{.Agda} はその論理式、アリティ、パラメータ、表示を復元する。
<!--/-->

<!--en-->

The description's five conjuncts are now five facts about a meta name, so the
adequacy is their assembly. Forwards, the skeleton is in the limit stage because
a parameter-free code is hereditarily finite, constant-freeness is the code set
at the empty alphabet read at the arity, the arity is a numeral, the parameters
are the environment the vector gives, and the denotation is the previous section.

Backwards, the same five, read. The arity comes out of the limit stage as a
numeral; the skeleton comes out of the empty-alphabet code set as a
parameter-free formula of one more variable than the arity, which is exactly a
name's formula; the parameters come back as a vector; and the three together
**are** a name. The denotation is then an equality of sets, proved by
extensionality, one direction per reading of the extension.
<!--zh-->

这条描述的五个合取项如今都是关于一个元层面名字的事实，故充分性就是把它们装配起来。正向：骨架落在极限层，因为无参的码遗传有穷；无参性是空字母表处的码集读在元数上；元数是一个数码；诸参数就是那个向量给出的环境；而指称是上一节。

反向：同样五条，读出来。元数以数码的身份从极限层出来；骨架以「比元数多一个变量的无参公式」的身份从空字母表码集出来，而那正是一个名字的公式；诸参数被读回成一个向量；三者合起来**就是**一个名字。指称随后是一条集合之间的等式，由外延性证出，那次外延的每一条读法给出一个方向。
<!--/-->

```agda
    NameAt-fill : (t : Name) → Data t → ⟨ γ ⊨ NameAt B C C₀ s a e d ⟩
    NameAt-fill t (qs , (qa , (qe , qd))) =
      NameAt-in B C C₀ s a e d γ hf ha he into back
      where
      module Bt = Body t qs qa qe

      hf : ⟨ γ ⊨ FreeAt C₀ s a ⟩
      hf = codeFree-in C₀ s a γ (arity t) q₀ qa (formula t) qs

      ha : ⟨ fst (lookup a γ) ∈ ω ⟩
      ha = subst (λ u → ⟨ u ∈ ω ⟩) (sym qa) (#∈ω (arity t))

      he : ⟨ γ ⊨ envOverAt e a B ⟩
      he = paramSeq-in e a B γ (arity t) (λ i → lookup i (params t)) qe qa
             (cong fst qB)

      into : (z : S) → ⟨ fst z ∈ fst (lookup d γ) ⟩
           → ⟨ fst z ∈ fst (lookup B γ) ⟩ × DenoteOf B C s e γ z
      into z hz = Bt.member-fill z (subst (λ u → ⟨ fst z ∈ u ⟩) qd hz)

      back : (z : S) → ⟨ fst z ∈ fst (lookup B γ) ⟩ → DenoteOf B C s e γ z
           → ⟨ fst z ∈ fst (lookup d γ) ⟩
      back z hzB hDen = subst (λ u → ⟨ fst z ∈ u ⟩) (sym qd)
        (Bt.member-read z hzB hDen)

    NameAt-read : ⟨ γ ⊨ NameAt B C C₀ s a e d ⟩ → ∥ Σ[ t ∈ Name ] Data t ∥₁
    NameAt-read (hf , (ha , (he , hd))) =
      PT.rec squash₁ atArity ha
      where
      atCode : (k : ℕ) (qa : fst (lookup a γ) ≡ # k)
             → Σ[ χ ∈ Formula (⊥* {ℓ}) (suc k) ]
                 (fst (lookup s γ) ≡ fst (limitCode χ))
             → Σ[ t ∈ Name ] Data t
      atCode k qa (χ , qs) = t , (qs , (qa , (qe , qd)))
        where
        t : Name
        t = k , (χ , paramSeq-out e a B γ k qa (cong fst qB) he)

        qe : fst (lookup e γ) ≡ env (pfam t)
        qe = paramSeq-graph e a B γ k qa (cong fst qB) he

        module Bt = Body t qs qa qe

        fwd : (y : V ℓ) → ⟨ y ∈ fst (lookup d γ) ⟩ → ⟨ y ∈ denote t ⟩
        fwd y hy = PT.rec (snd (y ∈ denote t))
          (Bt.member-read z (body .fst)) (body .snd)
          where
          z : S
          z = y , isL-trans hy (snd (lookup d γ))
          body : ⟨ fst z ∈ fst (lookup B γ) ⟩ × ∥ DenoteOf B C s e γ z ∥₁
          body = DenoteBody-out B C s e γ z
                   (extAt-out d (DenoteBody B C s e) γ hd z hy)

        bwd : (y : V ℓ) → ⟨ y ∈ denote t ⟩ → ⟨ y ∈ fst (lookup d γ) ⟩
        bwd y hy = extAt-in d (DenoteBody B C s e) γ hd z
          (DenoteBody-in B C s e γ z (body .fst) (body .snd))
          where
          z : S
          z = y , isL-trans (denoteMem t y hy) pA
          body : ⟨ fst z ∈ fst (lookup B γ) ⟩ × DenoteOf B C s e γ z
          body = Bt.member-fill z hy

        qd : fst (lookup d γ) ≡ denote t
        qd = extensionalV (λ y → ⇔toPath (fwd y) (bwd y))

      atArity : Σ[ lk ∈ Lift {ℓ-zero} {ℓ} ℕ ] (# (lower lk) ≡ fst (lookup a γ))
              → ∥ Σ[ t ∈ Name ] Data t ∥₁
      atArity (lk , qk) = PT.map (atCode (lower lk) (sym qk))
        (codeFree-out C₀ s a γ (lower lk) q₀ (sym qk) hf)
```

<!--en-->
## Least, described and meant

<!--zh-->
## 最小，描述出来与所指
<!--ja-->
## 最小性の記述と意味
<!--/-->

<!--en-->
Three sealed elements present a name's code, arity numeral, and parameter
environment to the universal clause in the least-name description.
<!--zh-->
三个被封印的元素把名字的码、元数数码与参数环境交给最小名字描述中的全称子句。
<!--ja-->
三つの不透明な要素が、名前の符号、アリティの数項、パラメータ環境を、最小の名前の記述にある全称節へ渡す。
<!--/-->

<!--en-->

Three more elements reach slots inside a satisfaction, and they are the three a
name is made of: its code, its arity as a numeral, and its parameters as an
environment over the carrier. The universal the description carries has to be
instantiated at them, so they are sealed where they are built, like the four
before them.
<!--zh-->

又有三个元素进入满足关系内部的各个槽位，而它们正是一个名字的三个组成部分：它的码、作为数码的元数，以及作为载体之上环境的诸参数。这条描述所携带的全称要在它们处实例化，故它们像前面四个一样，在被造出之处封印。
<!--/-->

Perf: a name's own three data reach slots inside a satisfaction, so they are
sealed too.

```agda
  opaque
    codeEl : Name → S
    codeEl t = fst (codeOf t)
             , isL-trans (snd (codeOf t)) (snd (LsetS ω ω-ord))

    codeEl-fst : (t : Name) → fst (codeEl t) ≡ fst (codeOf t)
    codeEl-fst t = refl

    envEl : Name → S
    envEl t = envS Aʟ (λ i → lookup i (params t))

    envEl-fst : (t : Name) → fst (envEl t) ≡ env (pfam t)
    envEl-fst t = refl
```

<!--en-->
## The least described name is the least name

<!--zh-->
## 被描述的最小名字就是最小的名字
<!--ja-->
## 記述された最小の名前は最小の名前である
<!--/-->

<!--en-->
The two readings of `LeastAt`{.Agda} equate object-language leastness with a
meta name that denotes the set and has no earlier competing name.
<!--zh-->
`LeastAt`{.Agda} 的两条读式把对象语言中的最小性与「指称该集合且没有排在它之前的名字」的元层面名字对应起来。
<!--ja-->
`LeastAt`{.Agda} の二つの読みは、対象言語の最小性を、その集合を表示し、より前の競合する名前をもたないメタ言語の名前と同一視する。
<!--/-->

<!--en-->

The description says "least" the way the meta-language says it: this is a name of
that set, and no name of that set comes before it. So the two halves are the
naming half, already done, and the universal, which is the same half read at the
three sets a name's data are, with the comparison turned by the previous
chapter's two adequacy directions.

Both relation slots carry their meaning as a hypothesis, which is the frame the
previous chapter left. Nothing here decides what those relations are; a caller
that has them as sets of the model supplies them.
<!--zh-->

这条描述按元语言的说法表达「最小」：这是该集合的一个名字，而且该集合的任何名字都不排在它之前。因此，两部分分别是命名部分 (已经完成) 与那个全称；后者仍是同一个合取项，只是读取于「一个名字的数据所对应的三个集合」，而比较由上一章充分性的两个方向转换。

两个关系位都以假设的形式携带各自的含义，这正是上一章留下的框架。此处不裁决这些关系具体是什么；持有它们 (作为模型中的集合) 的调用方会提供相应数据。
<!--/-->

```agda
  open SWO limitOrder using () renaming ( _<∙_ to _≺ˡ_ )
  open SWO w using () renaming ( _<∙_ to _≺ₚ_ )

  module Least (Rs Ps : S)
               (Rrep : (u v : Limit) → ⟨ pr (fst u) (fst v) ∈ fst Rs ⟩ → u ≺ˡ v)
               (Rfill : (u v : Limit) → u ≺ˡ v → ⟨ pr (fst u) (fst v) ∈ fst Rs ⟩)
               (Prep : (u v : ⟪ A ⟫) → ⟨ pr (ix u) (ix v) ∈ fst Ps ⟩ → u ≺ₚ v)
               (Pfill : (u v : ⟪ A ⟫) → u ≺ₚ v → ⟨ pr (ix u) (ix v) ∈ fst Ps ⟩)
               where
    private
      module K = Keys Rs Ps Rrep Rfill Prep Pfill

    module Min {n : ℕ} (R P B C C₀ s a e d : Fin n) (γ : S ^ n)
               (qR : fst (lookup R γ) ≡ fst Rs)
               (qP : fst (lookup P γ) ≡ fst Ps)
               (qB : lookup B γ ≡ Aʟ)
               (qC : fst (lookup C γ) ≡ fst (AllCodes Aʟ))
               (q₀ : fst (lookup C₀ γ) ≡ fst (AllCodes ∅ʟ)) where
      private
        module N = Named B C C₀ s a e d γ qB qC q₀

      IsMin : Name → Type (ℓ-suc ℓ)
      IsMin t = (t' : Name) → fst (lookup d γ) ≡ denote t'
              → t' ≺ₙ t → Empty.⊥

      Least : Name → Type (ℓ-suc ℓ)
      Least t = N.Data t × IsMin t

      LeastAt-fill : (t : Name) → Least t
                   → ⟨ γ ⊨ LeastNameAt R P B C C₀ s a e d ⟩
      LeastAt-fill t (dt , mt) = N.NameAt-fill t dt , univ
        where
        univ : (s' a' e' : S)
             → ⟨ (e' ∷ a' ∷ s' ∷ γ) ⊨ NameAt (sh3 B) (sh3 C) (sh3 C₀)
                   (suc (suc zero)) (suc zero) zero (sh3 d) ⟩
             → ⟨ (e' ∷ a' ∷ s' ∷ γ) ⊨ ≺At (sh3 R) (sh3 P)
                   (suc (suc zero)) (suc zero) zero (sh3 s) (sh3 a) (sh3 e) ⟩
             → Lift {j = ℓ-suc ℓ} Empty.⊥
        univ s' a' e' hn hlt = lift (PT.rec Empty.isProp⊥ step
          (Named.NameAt-read (sh3 B) (sh3 C) (sh3 C₀) (suc (suc zero))
             (suc zero) zero (sh3 d) (e' ∷ a' ∷ s' ∷ γ) qB qC q₀ hn))
          where
          step : Σ[ t' ∈ Name ] Named.Data (sh3 B) (sh3 C) (sh3 C₀)
                   (suc (suc zero)) (suc zero) zero (sh3 d)
                   (e' ∷ a' ∷ s' ∷ γ) qB qC q₀ t'
               → Empty.⊥
          step (t' , (qs' , (qa' , (qe' , qd')))) =
            PT.rec Empty.isProp⊥ (mt t' qd')
              (K.order-out (sh3 R) (sh3 P) (suc (suc zero)) (suc zero) zero
                 (sh3 s) (sh3 a) (sh3 e) (e' ∷ a' ∷ s' ∷ γ) t' t
                 qR qP qs' (dt .fst) qa' (dt .snd .fst)
                 qe' (dt .snd .snd .fst) hlt)

      LeastAt-read : ⟨ γ ⊨ LeastNameAt R P B C C₀ s a e d ⟩
                   → ∥ Σ[ t ∈ Name ] Least t ∥₁
      LeastAt-read (hn , hu) = PT.map step (N.NameAt-read hn)
        where
        step : Σ[ t ∈ Name ] N.Data t → Σ[ t ∈ Name ] Least t
        step (t , dt) = t , (dt , mt)
          where
          mt : IsMin t
          mt t' qd' lt = lower (hu (codeEl t') (numAt (arity t')) (envEl t')
            (Named.NameAt-fill (sh3 B) (sh3 C) (sh3 C₀) (suc (suc zero))
               (suc zero) zero (sh3 d)
               (envEl t' ∷ numAt (arity t') ∷ codeEl t' ∷ γ) qB qC q₀ t'
               (codeEl-fst t' , (numAt-fst (arity t')
                              , (envEl-fst t' , qd'))))
            (K.order-in (sh3 R) (sh3 P) (suc (suc zero)) (suc zero) zero
               (sh3 s) (sh3 a) (sh3 e)
               (envEl t' ∷ numAt (arity t') ∷ codeEl t' ∷ γ) t' t
               qR qP (codeEl-fst t') (dt .fst) (numAt-fst (arity t'))
               (dt .snd .fst) (envEl-fst t') (dt .snd .snd .fst) lt))
```

<!--en-->
## One step, described and meant

<!--zh-->
## 一步，描述出来与所指
<!--ja-->
## 一つのステップの記述と意味
<!--/-->

<!--en-->
`StepAt-fill`{.Agda} and `StepAt-read`{.Agda} prove that the six-binder formula
holds exactly when the least names of the two new-stage members are ordered by
the naming comparison.
<!--zh-->
`StepAt-fill`{.Agda} 与 `StepAt-read`{.Agda} 证明，这条六重绑定公式成立，当且仅当两个新层成员的最小名字按名字比较排序。
<!--ja-->
`StepAt-fill`{.Agda} と `StepAt-read`{.Agda} は、六つの束縛子をもつ論理式が成り立つことと、新段階の二要素の最小の名前が名前比較で順序づけられることが同値であると示す。
<!--/-->

<!--en-->

The step compares two members of the new stage by the least names that denote
them, and the description says exactly that: six sets carry the two names' data,
each triple is a least name of its member, and the comparison is the order
formula between the two triples. So the two readings are the previous section
twice and the order adequacy once, with the six binders packed and unpacked as
data and nothing under them unfolded.
<!--zh-->

那一步按「指称它们的最小名字」比较新层的两个成员，而这条描述说的正是这句话：六个集合承载两个名字的数据，每个三元组都是相应成员的一个最小名字，而比较就是两个三元组之间的那条序公式。故两条读法就是上一节的论证做两遍、序充分性做一遍；六层绑定作为数据装起又拆开，其下没有任何展开。
<!--/-->

```agda
    module Step {n : ℕ} (R P B C C₀ x y : Fin n) (γ : S ^ n)
                (qR : fst (lookup R γ) ≡ fst Rs)
                (qP : fst (lookup P γ) ≡ fst Ps)
                (qB : lookup B γ ≡ Aʟ)
                (qC : fst (lookup C γ) ≡ fst (AllCodes Aʟ))
                (q₀ : fst (lookup C₀ γ) ≡ fst (AllCodes ∅ʟ)) where
      LeastOf : Fin n → Name → Type (ℓ-suc ℓ)
      LeastOf i t = (fst (lookup i γ) ≡ denote t)
                  × ((t' : Name) → fst (lookup i γ) ≡ denote t'
                     → t' ≺ₙ t → Empty.⊥)

      StepAt-fill : (t₁ t₂ : Name) → LeastOf x t₁ → LeastOf y t₂ → t₁ ≺ₙ t₂
                  → ⟨ γ ⊨ StepAt R P B C C₀ x y ⟩
      StepAt-fill t₁ t₂ l₁ l₂ lt = StepAt-in R P B C C₀ x y γ
        ( codeEl t₁ , (numAt (arity t₁) , (envEl t₁
        , ( codeEl t₂ , (numAt (arity t₂) , (envEl t₂
        , ( ln₁ , (ln₂ , cmp) )))))))
        where
        ln₁ = Min.LeastAt-fill (sh6 R) (sh6 P) (sh6 B) (sh6 C) (sh6 C₀)
                s6a a6a e6a (sh6 x)
                (envEl t₂ ∷ numAt (arity t₂) ∷ codeEl t₂
                 ∷ envEl t₁ ∷ numAt (arity t₁) ∷ codeEl t₁ ∷ γ)
                qR qP qB qC q₀ t₁
                ( (codeEl-fst t₁ , (numAt-fst (arity t₁)
                                 , (envEl-fst t₁ , l₁ .fst)))
                , l₁ .snd )

        ln₂ = Min.LeastAt-fill (sh6 R) (sh6 P) (sh6 B) (sh6 C) (sh6 C₀)
                s6b a6b e6b (sh6 y)
                (envEl t₂ ∷ numAt (arity t₂) ∷ codeEl t₂
                 ∷ envEl t₁ ∷ numAt (arity t₁) ∷ codeEl t₁ ∷ γ)
                qR qP qB qC q₀ t₂
                ( (codeEl-fst t₂ , (numAt-fst (arity t₂)
                                 , (envEl-fst t₂ , l₂ .fst)))
                , l₂ .snd )

        cmp = K.order-in (sh6 R) (sh6 P) s6a a6a e6a s6b a6b e6b
                (envEl t₂ ∷ numAt (arity t₂) ∷ codeEl t₂
                 ∷ envEl t₁ ∷ numAt (arity t₁) ∷ codeEl t₁ ∷ γ) t₁ t₂
                qR qP (codeEl-fst t₁) (codeEl-fst t₂)
                (numAt-fst (arity t₁)) (numAt-fst (arity t₂))
                (envEl-fst t₁) (envEl-fst t₂) lt

      StepAt-read : ⟨ γ ⊨ StepAt R P B C C₀ x y ⟩
                  → ∥ Σ[ t₁ ∈ Name ] Σ[ t₂ ∈ Name ]
                      (LeastOf x t₁ × (LeastOf y t₂ × (t₁ ≺ₙ t₂))) ∥₁
      StepAt-read h = PT.rec squash₁ atSix (StepAt-out R P B C C₀ x y γ h)
        where
        Goal : Type (ℓ-suc ℓ)
        Goal = ∥ Σ[ t₁ ∈ Name ] Σ[ t₂ ∈ Name ]
                 (LeastOf x t₁ × (LeastOf y t₂ × (t₁ ≺ₙ t₂))) ∥₁

        atSix : StepOf R P B C C₀ x y γ → Goal
        atSix (s₁ , (k₁ , (p₁ , (s₂ , (k₂ , (p₂ , hb)))))) =
          PT.rec squash₁ atFirst
            (Min.LeastAt-read (sh6 R) (sh6 P) (sh6 B) (sh6 C) (sh6 C₀)
               s6a a6a e6a (sh6 x)
               (p₂ ∷ k₂ ∷ s₂ ∷ p₁ ∷ k₁ ∷ s₁ ∷ γ) qR qP qB qC q₀ h₁)
          where
          h₁ = hb .fst
          h₂ = hb .snd .fst
          hc = hb .snd .snd

          atSecond : (t₁ : Name)
                   → Min.Least (sh6 R) (sh6 P) (sh6 B) (sh6 C) (sh6 C₀)
                       s6a a6a e6a (sh6 x)
               (p₂ ∷ k₂ ∷ s₂ ∷ p₁ ∷ k₁ ∷ s₁ ∷ γ) qR qP qB qC q₀ t₁
                   → Σ[ t₂ ∈ Name ] Min.Least (sh6 R) (sh6 P) (sh6 B) (sh6 C)
                       (sh6 C₀) s6b a6b e6b (sh6 y)
               (p₂ ∷ k₂ ∷ s₂ ∷ p₁ ∷ k₁ ∷ s₁ ∷ γ) qR qP qB qC q₀ t₂
                   → Goal
          atSecond t₁ (d₁ , m₁) (t₂ , (d₂ , m₂)) =
            PT.map (λ lt → t₁ , (t₂ , ( (d₁ .snd .snd .snd , m₁)
                                      , ( (d₂ .snd .snd .snd , m₂) , lt ))))
              (K.order-out (sh6 R) (sh6 P) s6a a6a e6a s6b a6b e6b
                 (p₂ ∷ k₂ ∷ s₂ ∷ p₁ ∷ k₁ ∷ s₁ ∷ γ) t₁ t₂
                 qR qP (d₁ .fst) (d₂ .fst) (d₁ .snd .fst) (d₂ .snd .fst)
                 (d₁ .snd .snd .fst) (d₂ .snd .snd .fst) hc)

          atFirst : Σ[ t₁ ∈ Name ] Min.Least (sh6 R) (sh6 P) (sh6 B) (sh6 C)
                      (sh6 C₀) s6a a6a e6a (sh6 x)
               (p₂ ∷ k₂ ∷ s₂ ∷ p₁ ∷ k₁ ∷ s₁ ∷ γ) qR qP qB qC q₀ t₁
                  → Goal
          atFirst (t₁ , l₁) = PT.rec squash₁ (atSecond t₁ l₁)
            (Min.LeastAt-read (sh6 R) (sh6 P) (sh6 B) (sh6 C) (sh6 C₀)
               s6b a6b e6b (sh6 y)
               (p₂ ∷ k₂ ∷ s₂ ∷ p₁ ∷ k₁ ∷ s₁ ∷ γ) qR qP qB qC q₀ h₂)
```

<!--en-->
## Recap

<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
The exported fill/read pairs establish adequacy for parameter sequences,
denotation, complete names, least names, and finally the successor-stage step.
<!--zh-->
导出的各对填充与读取引理，依次确立参数序列、指称、完整名字、最小名字以及最终后继层步进的充分性。
<!--ja-->
公開される fill/read の各組は、パラメータ列、表示、完全な名前、最小の名前、そして最後に後者段階のステップの妥当性を確立する。
<!--/-->

<!--en-->

`paramSeq-in`{.Agda} and `paramSeq-out`{.Agda} are the parameter conjunct in both
directions: a vector over the carrier is an environment over it whose domain is
the arity, and any such environment comes back as a vector, untruncated, because
the entry at an index is a proposition and the index of a value is a fibre.

`envAt`{.Agda}, `numAt`{.Agda}, `keyAt`{.Agda} and `valAt`{.Agda} are the four
elements the denotation conjunct is satisfied at, sealed where they are built;
`codeEl`{.Agda} and `envEl`{.Agda} are two more, for the universal the least-name
description carries. `Named.Body.denote-fill`{.Agda} and
`Named.Body.denote-read`{.Agda} are the denotation in both directions, and
`NameAt-fill`{.Agda} and `NameAt-read`{.Agda} assemble the five conjuncts into a
meta name and back.

`Least.Min.LeastAt-fill`{.Agda} and `Least.Min.LeastAt-read`{.Agda} are the same
for a least name, with the universal instantiated at a name's own three data;
`Least.Step.StepAt-fill`{.Agda} and `Least.Step.StepAt-read`{.Agda} are the step,
which is two least names and one comparison.

Three measurements, and all three are laws this route already had, met at new
places. The composite denotation equation **cannot be discharged by a
substitution against a written type**, at any arguments, variable ones included:
its two factors `denote-mem`{.Agda} and `val-sat`{.Agda} each discharge in 2.4 s,
and their composite does not finish in 400 s. Substituting along the factors
separately is the cure, and the law is: a composite of adequacy equations is
consumed factor by factor, never as a composite. The six-fold binder block wants
its environment **spelled out**, not abbreviated by a `where`: abbreviated,
`StepAt-fill`{.Agda} alone does not finish in 400 s; spelled out, the whole file
checks in 20 s. And a six-fold existential's payload is read through the
chapter's own `StepOf`{.Agda}, never through a hand-written Σ, because writing it
out puts the description under it into normal form.
<!--zh-->

`paramSeq-in`{.Agda} 与 `paramSeq-out`{.Agda} 给出参数那个合取项的两个方向：载体之上的一个向量，就是其上的一个定义域为元数的环境；而任何这样的环境都能不带截断地读回成一个向量，因为某个序号处的条目是命题，而一个取值的索引是一条纤维。

`envAt`{.Agda}、`numAt`{.Agda}、`keyAt`{.Agda} 与 `valAt`{.Agda} 是指称合取项所作用的四个元素，并都在构造之处封装；`codeEl`{.Agda} 与 `envEl`{.Agda} 是另外两个元素，供最小名字描述中的全称使用。`Named.Body.denote-fill`{.Agda} 与 `Named.Body.denote-read`{.Agda} 给出指称的两个方向，`NameAt-fill`{.Agda} 与 `NameAt-read`{.Agda} 则把五个合取项组成一个元层面名字，并可再拆回这些分量。

`Least.Min.LeastAt-fill`{.Agda} 与 `Least.Min.LeastAt-read`{.Agda} 对最小名字做同样的事，那个全称在「一个名字自己的三样数据」处实例化；`Least.Step.StepAt-fill`{.Agda} 与 `Least.Step.StepAt-read`{.Agda} 是那一步，即两个最小名字加一次比较。

以下三项实测都体现了这条路线已有的规则。复合指称等式**无法由「对着写出来的类型」的一次代换证得**，无论实参还是变元都不行：两个因子 `denote-mem`{.Agda} 与 `val-sat`{.Agda} 各需 2.4 秒，而整体复合在 400 秒内无法完成。解决办法是分别沿两个因子代换，即逐因子使用充分性等式。六层绑定要求把环境**写开**，不能用 `where` 缩写：使用缩写时，仅 `StepAt-fill`{.Agda} 就在 400 秒内无法完成；写开后，整个文件在 20 秒内检查完毕。六重存在的内容经本章的 `StepOf`{.Agda} 读出，不使用手写 Σ，因为展开后者会使其下的描述化为正规形。
<!--/-->

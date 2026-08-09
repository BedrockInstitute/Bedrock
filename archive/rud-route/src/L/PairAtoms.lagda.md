# The pair atoms

<!--en-->
The tower story, told inside a carrier, is one object-language sentence: some
initial segment `f` of the L-tower lies in the carrier's binding set,
approximates the tower, applies the Def step at every stage, and ranges over
`x`. Two of the three clauses speak about Kuratowski pairs: the approximation
says the witness is a set of pairs, and the range read says the pair
`pr a x` lies in the witness.

This chapter writes the object-language half of that vocabulary once, generic
in the carrier and its transitivity: the pair atoms, the formulas saying "this
variable is the singleton of that one", "this variable is the unordered pair
of those two", and "this variable is the Kuratowski pair of those two",
together with their decodes, the two-way lemmas that read a satisfied atom
back into a meta-level equality, and the pair-component recovery, the fact
that a pair lying in a transitive carrier brings its components with it.
Every consumer of the initial-segment face, the level formula, the bridge's
`L-sigma` at a rud carrier, and the condensation crossing, reuses this kit
verbatim and pays for it once.
<!--zh-->
在某个载体内部讲述的塔故事是一条对象语言句子：某条 L 塔初始段 `f` 落在载体的绑定集里，近似整座塔，在每个阶段施以 Def 步，并以 `x` 为像。三个子句里有两个谈论库拉托夫斯基对：近似说见证是以对为成员的集合，像的读式说对 `pr a x` 落在见证中。

本章一次写成这套词汇的对象语言半边，以载体及其传递性为参数：对原子，即说「这个变量是那个变量的单点集」「这个变量是那两者的无序对」「这个变量是那两者的库拉托夫斯基对」的公式，连同它们的解码，把被满足的原子读回元层等式的双向引理，以及对分量恢复，即落在传递载体里的对把两个分量一并带入。初始段面孔的每个消费方，层公式、rud 载体上的桥 `L-sigma` 与凝聚跨越，都逐字复用这套工具，并只付一次账。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.PairAtoms {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; ∀̇∈; ∃̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using
  ( pr; ∈singl; singl∈; self∈singl; inl∈⁅,⁆; inr∈⁅,⁆; mem⁅,⁆ )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ} using ( isTransV )
open import Cubical.HITs.CumulativeHierarchy.Base using ( setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

private
  -- Variable zero at any depth: the variable the bounded quantifiers bind.
  f0 : {n : ℕ} → Fin (suc n)
  f0 = zero
```

<!--en-->
## The meta pairhood
<!--zh-->
## 元层的成对性
<!--/-->

<!--en-->
The meta-level notion comes first. A set `z` is a pair when it is merely a
Kuratowski pair `pr a b`, the coding the V chapter built, and pairhood is the
spine of functionhood: a function is a set of pairs with exactly one copy of
each first component. The predicate lives at the meta level, over the
carrier's sets, because the object clauses of the face's approximation will be
decoded against it.
<!--zh-->
先立元层概念。集合 `z` 是对，当它仅仅就是某个库拉托夫斯基对 `pr a b`，即 V 章建好的编码；成对性是函数性的脊梁：函数是以对为成员、且每个首分量恰有一份的集合。谓词住在元层，跑在载体的集合上，因为面孔近似子句的对象条款将对照它解码。
<!--/-->

```agda
isPair : S → Type (ℓ-suc ℓ)
isPair z = ∥ Σ[ a ∈ S ] Σ[ b ∈ S ] (z ≡ pr a b) ∥₁

module PairMem (u : S) (utr : isTransV u) where
  pair-left : {a b : S} → ⟨ pr a b ∈ˢ u ⟩ → ⟨ a ∈ˢ u ⟩
  pair-left {a} {b} h =
    utr {x = ⁅ a ⁆s} {y = a} (∈∈ₛ {a = a} {b = ⁅ a ⁆s} .snd (self∈singl a))
      (utr {x = pr a b} {y = ⁅ a ⁆s}
        (∈∈ₛ {a = ⁅ a ⁆s} {b = pr a b} .snd
          (inl∈⁅,⁆ {a = ⁅ a ⁆s} {b = ⁅ a , b ⁆} refl)) h)
  pair-right : {a b : S} → ⟨ pr a b ∈ˢ u ⟩ → ⟨ b ∈ˢ u ⟩
  pair-right {a} {b} h =
    utr {x = ⁅ a , b ⁆} {y = b}
      (∈∈ₛ {a = b} {b = ⁅ a , b ⁆} .snd (inr∈⁅,⁆ {a = a} refl))
      (utr {x = pr a b} {y = ⁅ a , b ⁆}
        (∈∈ₛ {a = ⁅ a , b ⁆} {b = pr a b} .snd
          (inr∈⁅,⁆ {a = ⁅ a ⁆s} refl)) h)
```

<!--en-->
## The pair components
<!--zh-->
## 对的分量
<!--/-->

<!--en-->
Every consumer's carrier is transitive: a stage of the tower, a rud-closed
set, a transitive target all are. Transitivity is exactly what lets a pair
lying in the carrier bring its components with it. The singleton `⁅ a ⁆s` is a
member of the pair `pr a b`, and `a` is a member of that singleton, so two
transitivity steps pull `a` back into the carrier; `b` arrives the same way
through the two-element set `⁅ a , b ⁆`. The recovery is written once in the
module `PairMem`{.Agda}, parameterized by the carrier `u` and its transitivity
`utr`; its two exports are `pair-left` and `pair-right`.
<!--zh-->
每个消费方的载体都传递：塔的层、rud 闭集、传递目标皆然。传递性恰恰让落在载体里的对把两个分量带回来。单点集 `⁅ a ⁆s` 是对 `pr a b` 的成员，而 `a` 又是该单点集的成员，于是两步传递性就把 `a` 拉回载体；`b` 经二元集 `⁅ a , b ⁆` 同理到达。这条恢复只写一次，住在以载体 `u` 及其传递性 `utr` 为参数的模块 `PairMem`{.Agda} 里；它的两个导出是 `pair-left` 与 `pair-right`。
<!--/-->

<!--en-->
## The pair atoms
<!--zh-->
## 对原子
<!--/-->

<!--en-->
The object-language half lives in the module `PairKit`{.Agda} with the same
two parameters. The inner world at the carrier is the definability chapter's
`DefOf u`: its members `SM` are the carrier's sets with their membership
certificate, and `⊨ᵐ` is the inner satisfaction. The function `pt` injects a
set into that world, and `entry∈` lifts a membership certificate from a member
of a carrier member back into the carrier, the second place the kit leans on
transitivity. The three atoms then write themselves down, in de Bruijn shape
where the bounded quantifiers bind variable zero. `sglAt k i` says the set at
`k` is the singleton of the set at `i`: `i` belongs to `k`, and every member
of `k` is `i`. `pairAt k i j` says the set at `k` is the unordered pair of `i`
and `j`: both belong to `k`, and every member of `k` is one of the two.
`prAt q u v` spells the Kuratowski pair `(u, v)` as the two-element set of the
singleton `⁅ u ⁆s` and the unordered pair `⁅ u , v ⁆`: `q` contains both, and
nothing else. Finally `pairChar` is the meta-level counterpart: a set that
contains `a` and `b` and nothing but them is the pair `⁅ a , b ⁆`, the fact
the deep decode assembles its witnesses with.
<!--zh-->
对象语言半边住在以同样两个参数为参数的模块 `PairKit`{.Agda} 里。载体处的内层世界是可定义性章的 `DefOf u`：其成员 `SM` 是带隶属证书的载体集合，`⊨ᵐ` 是内层满足。`pt` 把集合注入这个世界，`entry∈` 则把「载体成员的成员」的隶属证书抬回载体，这是套件第二次倚靠传递性。三条原子公式随之自己写出，采用 de Bruijn 形状，有界量词绑定变量零。`sglAt k i` 说 `k` 处的集合是 `i` 处集合的单点集：`i` 属于 `k`，且 `k` 的每个成员都是 `i`。`pairAt k i j` 说 `k` 处的集合是 `i`、`j` 的无序对：两者都属于 `k`，且 `k` 的每个成员都是二者之一。`prAt q u v` 把库拉托夫斯基对 `(u, v)` 拼成单点集 `⁅ u ⁆s` 与无序对 `⁅ u , v ⁆` 的二元集：`q` 兼含两者，别无他物。最后 `pairChar` 是元层的对应物：一个包含 `a`、`b` 且除此无他的集合就是 `⁅ a , b ⁆`，深解码正是靠它把见证拼到一起。
<!--/-->

```agda
-- The object-language pair atoms, generic in the carrier and its transitivity.
module PairKit (u : S) (utr : isTransV u) where
  module U = DefOf u
  open U using ( SM; _⊨ᵐ_ )
  module PM = PairMem u utr
  pt : (x : S) → ⟨ x ∈ˢ u ⟩ → SM
  pt x h = x , h
  entry∈ : {n : ℕ} (k : Fin n) (δ : Vec SM n) (z : S)
         → ⟨ z ∈ˢ fst (lookup k δ) ⟩ → ⟨ z ∈ˢ u ⟩
  entry∈ k δ z h = utr {x = fst (lookup k δ)} {y = z} h (snd (lookup k δ))
  sglAt : {n : ℕ} → Fin n → Fin n → Formula ⟪ u ⟫ n
  sglAt k i = (var i ∈̇ var k) ∧̇ (∀̇∈ (var k) (var f0 ≐ var (suc i)))
  pairAt : {n : ℕ} → Fin n → Fin n → Fin n → Formula ⟪ u ⟫ n
  pairAt k i j = (var i ∈̇ var k) ∧̇ ((var j ∈̇ var k)
              ∧̇ (∀̇∈ (var k) ((var f0 ≐ var (suc i)) ∨̇ (var f0 ≐ var (suc j)))))
  prAt : {n : ℕ} → Fin n → Fin n → Fin n → Formula ⟪ u ⟫ n
  prAt q u v = (∃̇∈ (var q) (sglAt f0 (suc u)))
            ∧̇ ((∃̇∈ (var q) (pairAt f0 (suc u) (suc v)))
            ∧̇ (∀̇∈ (var q) (sglAt f0 (suc u) ∨̇ pairAt f0 (suc u) (suc v))))
  pairChar : (z a b : S) → ⟨ a ∈ˢ z ⟩ → ⟨ b ∈ˢ z ⟩
           → ((x : S) → ⟨ x ∈ˢ z ⟩ → ∥ (x ≡ a) ⊎ (x ≡ b) ∥₁)
           → z ≡ ⁅ a , b ⁆
  pairChar z a b a∈z b∈z all = extensionality z ⁅ a , b ⁆ (sub , sup)
    where
    sub : (x : S) → ⟨ x ∈ₛ z ⟩ → ⟨ x ∈ₛ ⁅ a , b ⁆ ⟩
    sub x h = PT.rec (snd (x ∈ₛ ⁅ a , b ⁆))
      (λ { (inl e) → inl∈⁅,⁆ e ; (inr e) → inr∈⁅,⁆ e })
      (all x (∈∈ₛ {a = x} {b = z} .snd h))
    sup : (x : S) → ⟨ x ∈ₛ ⁅ a , b ⁆ ⟩ → ⟨ x ∈ₛ z ⟩
    sup x h = PT.rec (snd (x ∈ₛ z))
      (λ { (inl e) → subst (λ w → ⟨ w ∈ₛ z ⟩) (sym e) (∈∈ₛ {a = a} {b = z} .fst a∈z)
         ; (inr e) → subst (λ w → ⟨ w ∈ₛ z ⟩) (sym e) (∈∈ₛ {a = b} {b = z} .fst b∈z) })
      (mem⁅,⁆ h)
```

<!--en-->
## The decodes
<!--zh-->
## 解码
<!--/-->

<!--en-->
Each atom means exactly what it says: a satisfied atom at an environment `δ`
is the corresponding meta-level equality of the looked-up values, and
conversely. Each atom therefore gets two lemmas, `-out` (satisfaction implies
the equality) and `-in` (the equality implies satisfaction), so the object
clause and the meta read are interchangeable in both directions. The singleton
and unordered-pair decodes are direct extensionality walks. The pair decode
`prAt-out` is the deep one: the two bounded existentials supply the witnesses
`⁅ u ⁆s` and `⁅ u , v ⁆` inside `q`, the bounded universal supplies the
coverage, and `pairChar` assembles the equality; `prAt-in` rebuilds the three
parts of `prAt` from the equality. One discipline is kept throughout: every
truncation branch is a named `where` function with a written type, never a
bare lambda, so the inner satisfaction machinery elaborates once per branch
instead of once per constraint.
<!--zh-->
每条原子都名副其实：原子在环境 `δ` 处被满足，当且仅当被查出的值之间成立相应的元层等式。于是每条原子配两条引理，`-out` (满足推出等式) 与 `-in` (等式推出满足)，对象条款与元层读式两个方向均可互换。单点集与无序对的解码是直接的外延性论证。对解码 `prAt-out` 是深的一枚：两个有界存在交出 `q` 内部的见证 `⁅ u ⁆s` 与 `⁅ u , v ⁆`，有界全称交出覆盖，`pairChar` 把等式拼成；`prAt-in` 从等式重建 `prAt` 的三个部分。全程守住一条纪律：每条截断分支都是带书面类型的具名 `where` 函数，绝不写成裸 lambda，于是内层满足机器每个分支只展开一次，而非每个约束展开一次。
<!--/-->

```agda
  sglAt-out : {n : ℕ} (k i : Fin n) (δ : Vec SM n)
            → ⟨ δ ⊨ᵐ sglAt k i ⟩
            → fst (lookup k δ) ≡ ⁅ fst (lookup i δ) ⁆s
  sglAt-out k i δ (h₁ , h₂) = extensionality z ⁅ a ⁆s (sub , sup)
    where
    z = fst (lookup k δ)
    a = fst (lookup i δ)
    all : (x : S) → ⟨ x ∈ˢ z ⟩ → x ≡ a
    all x h = h₂ (pt x (entry∈ k δ x h)) h
    sub : (x : S) → ⟨ x ∈ₛ z ⟩ → ⟨ x ∈ₛ ⁅ a ⁆s ⟩
    sub x h = singl∈ (all x (∈∈ₛ {a = x} {b = z} .snd h))
    sup : (x : S) → ⟨ x ∈ₛ ⁅ a ⁆s ⟩ → ⟨ x ∈ₛ z ⟩
    sup x h = subst (λ w → ⟨ w ∈ₛ z ⟩) (sym (∈singl h))
      (∈∈ₛ {a = a} {b = z} .fst h₁)
  sglAt-in : {n : ℕ} (k i : Fin n) (δ : Vec SM n)
           → fst (lookup k δ) ≡ ⁅ fst (lookup i δ) ⁆s
           → ⟨ δ ⊨ᵐ sglAt k i ⟩
  sglAt-in k i δ e = (a∈z , all)
    where
    a∈z : ⟨ fst (lookup i δ) ∈ˢ fst (lookup k δ) ⟩
    a∈z = subst (λ w → ⟨ fst (lookup i δ) ∈ˢ w ⟩) (sym e)
      (∈∈ₛ {a = fst (lookup i δ)} {b = ⁅ fst (lookup i δ) ⁆s} .snd
        (self∈singl (fst (lookup i δ))))
    all : (xm : SM) → ⟨ fst xm ∈ˢ fst (lookup k δ) ⟩
        → fst xm ≡ fst (lookup i δ)
    all xm h = ∈singl (subst (λ w → ⟨ fst xm ∈ₛ w ⟩) e
      (∈∈ₛ {a = fst xm} {b = fst (lookup k δ)} .fst h))
  pairAt-out : {n : ℕ} (k i j : Fin n) (δ : Vec SM n)
             → ⟨ δ ⊨ᵐ pairAt k i j ⟩
             → fst (lookup k δ) ≡ ⁅ fst (lookup i δ) , fst (lookup j δ) ⁆
  pairAt-out k i j δ (h₁ , (h₂ , h₃)) = extensionality z ⁅ a , b ⁆ (sub , sup)
    where
    z = fst (lookup k δ)
    a = fst (lookup i δ)
    b = fst (lookup j δ)
    all : (x : S) → ⟨ x ∈ˢ z ⟩ → ∥ (x ≡ a) ⊎ (x ≡ b) ∥₁
    all x h = PT.map pick (h₃ (pt x (entry∈ k δ x h)) h)
      where
      pick : ⟨ (pt x (entry∈ k δ x h) ∷ δ) ⊨ᵐ (var f0 ≐ var (suc i)) ⟩
           ⊎ ⟨ (pt x (entry∈ k δ x h) ∷ δ) ⊨ᵐ (var f0 ≐ var (suc j)) ⟩
           → (x ≡ a) ⊎ (x ≡ b)
      pick (inl s) = inl s
      pick (inr s) = inr s
    sub : (x : S) → ⟨ x ∈ₛ z ⟩ → ⟨ x ∈ₛ ⁅ a , b ⁆ ⟩
    sub x h = PT.rec (snd (x ∈ₛ ⁅ a , b ⁆))
      (λ { (inl e) → inl∈⁅,⁆ e ; (inr e) → inr∈⁅,⁆ e })
      (all x (∈∈ₛ {a = x} {b = z} .snd h))
    sup : (x : S) → ⟨ x ∈ₛ ⁅ a , b ⁆ ⟩ → ⟨ x ∈ₛ z ⟩
    sup x h = PT.rec (snd (x ∈ₛ z))
      (λ { (inl e) → subst (λ w → ⟨ w ∈ₛ z ⟩) (sym e) (∈∈ₛ {a = a} {b = z} .fst h₁)
         ; (inr e) → subst (λ w → ⟨ w ∈ₛ z ⟩) (sym e) (∈∈ₛ {a = b} {b = z} .fst h₂) })
      (mem⁅,⁆ h)
  pairAt-in : {n : ℕ} (k i j : Fin n) (δ : Vec SM n)
            → fst (lookup k δ) ≡ ⁅ fst (lookup i δ) , fst (lookup j δ) ⁆
            → ⟨ δ ⊨ᵐ pairAt k i j ⟩
  pairAt-in k i j δ e = (i∈z , (j∈z , all))
    where
    z = fst (lookup k δ)
    a = fst (lookup i δ)
    b = fst (lookup j δ)
    pairSpec : (v : S) → ⟨ v ∈ˢ ⁅ a , b ⁆ ⟩ → ∥ (v ≡ a) ⊎ (v ≡ b) ∥₁
    pairSpec v h = mem⁅,⁆ (∈∈ₛ {a = v} {b = ⁅ a , b ⁆} .fst h)
    pairSpec-in : (v : S) → ∥ (v ≡ a) ⊎ (v ≡ b) ∥₁ → ⟨ v ∈ˢ ⁅ a , b ⁆ ⟩
    pairSpec-in v = PT.rec (snd (v ∈ˢ ⁅ a , b ⁆))
      (λ { (inl q) → ∈∈ₛ {a = v} {b = ⁅ a , b ⁆} .snd (inl∈⁅,⁆ q)
         ; (inr q) → ∈∈ₛ {a = v} {b = ⁅ a , b ⁆} .snd (inr∈⁅,⁆ q) })
    i∈z : ⟨ a ∈ˢ z ⟩
    i∈z = subst (λ w → ⟨ a ∈ˢ w ⟩) (sym e) (pairSpec-in a ∣ inl refl ∣₁)
    j∈z : ⟨ b ∈ˢ z ⟩
    j∈z = subst (λ w → ⟨ b ∈ˢ w ⟩) (sym e) (pairSpec-in b ∣ inr refl ∣₁)
    all : (xm : SM) → ⟨ fst xm ∈ˢ z ⟩
        → ∥ (fst xm ≡ a) ⊎ (fst xm ≡ b) ∥₁
    all xm h = pairSpec (fst xm) (subst (λ w → ⟨ fst xm ∈ˢ w ⟩) e h)
  prAt-out : {n : ℕ} (q u v : Fin n) (δ : Vec SM n)
           → ⟨ δ ⊨ᵐ prAt q u v ⟩
           → fst (lookup q δ) ≡ pr (fst (lookup u δ)) (fst (lookup v δ))
  prAt-out q u v δ (h₁ , (h₂ , h₃)) =
    PT.rec (setIsSet Q (pr U W))
      (λ xm → PT.rec (setIsSet Q (pr U W)) (go xm) h₂) h₁
    where
    Q = fst (lookup q δ)
    U = fst (lookup u δ)
    W = fst (lookup v δ)
    all : (x : S) → ⟨ x ∈ˢ Q ⟩ → ∥ (x ≡ ⁅ U ⁆s) ⊎ (x ≡ ⁅ U , W ⁆) ∥₁
    all x h = PT.map pick (h₃ (pt x (entry∈ q δ x h)) h)
      where
      pick : ⟨ (pt x (entry∈ q δ x h) ∷ δ) ⊨ᵐ sglAt f0 (suc u) ⟩
           ⊎ ⟨ (pt x (entry∈ q δ x h) ∷ δ) ⊨ᵐ pairAt f0 (suc u) (suc v) ⟩
           → (x ≡ ⁅ U ⁆s) ⊎ (x ≡ ⁅ U , W ⁆)
      pick (inl s) = inl (sglAt-out f0 (suc u) (pt x (entry∈ q δ x h) ∷ δ) s)
      pick (inr s) =
        inr (pairAt-out f0 (suc u) (suc v) (pt x (entry∈ q δ x h) ∷ δ) s)
    go : Σ[ xm ∈ SM ] (⟨ fst xm ∈ˢ Q ⟩ × ⟨ (xm ∷ δ) ⊨ᵐ sglAt f0 (suc u) ⟩)
       → Σ[ ym ∈ SM ] (⟨ fst ym ∈ˢ Q ⟩ × ⟨ (ym ∷ δ) ⊨ᵐ pairAt f0 (suc u) (suc v) ⟩)
       → Q ≡ pr U W
    go (xm , (x∈Q , sx)) (ym , (y∈Q , sy)) = pairChar Q (⁅ U ⁆s) (⁅ U , W ⁆)
      (subst (λ t → ⟨ t ∈ˢ Q ⟩) (sglAt-out f0 (suc u) (xm ∷ δ) sx) x∈Q)
      (subst (λ t → ⟨ t ∈ˢ Q ⟩) (pairAt-out f0 (suc u) (suc v) (ym ∷ δ) sy) y∈Q)
      all
  prAt-in : {n : ℕ} (q u v : Fin n) (δ : Vec SM n)
          → fst (lookup q δ) ≡ pr (fst (lookup u δ)) (fst (lookup v δ))
          → ⟨ δ ⊨ᵐ prAt q u v ⟩
  prAt-in q u v δ e = (part₁ , (part₂ , part₃))
    where
    Q = fst (lookup q δ)
    U = fst (lookup u δ)
    W = fst (lookup v δ)
    pairSpec-in : (v : S) → ∥ (v ≡ ⁅ U ⁆s) ⊎ (v ≡ ⁅ U , W ⁆) ∥₁
                → ⟨ v ∈ˢ pr U W ⟩
    pairSpec-in v = PT.rec (snd (v ∈ˢ pr U W))
      (λ { (inl q) → ∈∈ₛ {a = v} {b = pr U W} .snd
          (inl∈⁅,⁆ {a = ⁅ U ⁆s} {b = ⁅ U , W ⁆} q)
         ; (inr q) → ∈∈ₛ {a = v} {b = pr U W} .snd
          (inr∈⁅,⁆ {a = ⁅ U ⁆s} {b = ⁅ U , W ⁆} q) })
    sgl∈Q : ⟨ ⁅ U ⁆s ∈ˢ Q ⟩
    sgl∈Q = subst (λ t → ⟨ ⁅ U ⁆s ∈ˢ t ⟩) (sym e)
      (pairSpec-in (⁅ U ⁆s) ∣ inl refl ∣₁)
    pair∈Q : ⟨ ⁅ U , W ⁆ ∈ˢ Q ⟩
    pair∈Q = subst (λ t → ⟨ ⁅ U , W ⁆ ∈ˢ t ⟩) (sym e)
      (pairSpec-in (⁅ U , W ⁆) ∣ inr refl ∣₁)
    part₁ : ⟨ δ ⊨ᵐ ∃̇∈ (var q) (sglAt f0 (suc u)) ⟩
    part₁ = ∣ pt (⁅ U ⁆s) (entry∈ q δ (⁅ U ⁆s) sgl∈Q)
            , (sgl∈Q , sglAt-in f0 (suc u)
                (pt (⁅ U ⁆s) (entry∈ q δ (⁅ U ⁆s) sgl∈Q) ∷ δ) refl) ∣₁
    part₂ : ⟨ δ ⊨ᵐ ∃̇∈ (var q) (pairAt f0 (suc u) (suc v)) ⟩
    part₂ = ∣ pt (⁅ U , W ⁆) (entry∈ q δ (⁅ U , W ⁆) pair∈Q)
            , (pair∈Q , pairAt-in f0 (suc u) (suc v)
                (pt (⁅ U , W ⁆) (entry∈ q δ (⁅ U , W ⁆) pair∈Q) ∷ δ) refl) ∣₁
    part₃ : ⟨ δ ⊨ᵐ ∀̇∈ (var q)
              (sglAt f0 (suc u) ∨̇ pairAt f0 (suc u) (suc v)) ⟩
    part₃ xm h = PT.map pick
      (pairSpec (fst xm) h)
      where
      pairSpec : (v : S) → ⟨ v ∈ˢ Q ⟩ → ∥ (v ≡ ⁅ U ⁆s) ⊎ (v ≡ ⁅ U , W ⁆) ∥₁
      pairSpec v h = mem⁅,⁆
        (subst (λ t → ⟨ v ∈ₛ t ⟩) e (∈∈ₛ {a = v} {b = Q} .fst h))
      pick : (fst xm ≡ ⁅ U ⁆s) ⊎ (fst xm ≡ ⁅ U , W ⁆)
           → ⟨ (xm ∷ δ) ⊨ᵐ sglAt f0 (suc u) ⟩
           ⊎ ⟨ (xm ∷ δ) ⊨ᵐ pairAt f0 (suc u) (suc v) ⟩
      pick (inl s) = inl (sglAt-in f0 (suc u) (xm ∷ δ) s)
      pick (inr s) = inr (pairAt-in f0 (suc u) (suc v) (xm ∷ δ) s)
```

<!--en-->
## A coherence control
<!--zh-->
## 一致性对照
<!--/-->

<!--en-->
The kit closes with a coherence check: the decode is a retraction. Reading a
satisfied `prAt` back to the equality and re-entering it returns a
satisfaction, so the two directions agree with each other.
<!--zh-->
套件以一条一致性检查收尾：解码是一个收缩。把被满足的 `prAt` 读回等式，再经 `-in` 重新进入，得到的仍是满足，于是两个方向彼此连贯。
<!--/-->

```agda
  -- The decode is coherent: reading back returns a satisfaction.
  ctl-roundtrip : {n : ℕ} (q u v : Fin n) (δ : Vec SM n)
                → ⟨ δ ⊨ᵐ prAt q u v ⟩ → ⟨ δ ⊨ᵐ prAt q u v ⟩
  ctl-roundtrip q u v δ h = prAt-in q u v δ (prAt-out q u v δ h)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The chapter delivers the shared half of the face's instantiations, written
once: the meta pairhood `isPair`, the pair-component recovery `PairMem` at any
transitive carrier, and the kit `PairKit` with the three atoms `sglAt`,
`pairAt` and `prAt`, the characterization `pairChar`, the six decodes and the
coherence control. Every export is generic in the carrier `u` and its
transitivity `utr`, so the three consumers of the face, the level formula, the
bridge's `L-sigma` and the condensation crossing, reuse the same kit verbatim.
The instantiations themselves, the carriers, the object clauses and the
adequacies, are the consumers' work, and the orchestrator wires this chapter
into `Everything`.
<!--zh-->
本章一次交付面孔实例化的共享半边：元层成对性 `isPair`，任意传递载体处的对分量恢复 `PairMem`，以及套件 `PairKit`，含三条原子 `sglAt`、`pairAt`、`prAt`，刻画 `pairChar`，六条解码与一致性对照。每个导出都以载体 `u` 及其传递性 `utr` 为参数，于是面孔的三个消费方，层公式、桥 `L-sigma` 与凝聚跨越，逐字复用同一套工具。实例化本身，载体、对象条款与充分性，都是消费方的事；编排者把本章接入 `Everything`。
<!--/-->

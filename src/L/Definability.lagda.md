<!--en-->
# Definable subsets of a set

For a set `A`, the operator `Def A`{.Agda} collects exactly the subsets of `A` defined by a first-order formula over the restricted structure on `A`, with finitely many parameters from `A`. Its membership theorem exposes the formula, environment, and satisfaction relation used by later constructibility arguments.
<!--zh-->
# 集合的可定义子集

对集合 `A`，算子 `Def A`{.Agda} 恰好收集由 `A` 上限制结构中的一阶公式，并使用 `A` 中有限多个参数所定义的 `A` 的子集。其隶属定理给出后续可构造性论证所需的公式、环境与满足关系。
<!--ja-->
# 集合の定義可能な部分集合

集合 `A` に対して、演算子 `Def A`{.Agda} は、`A` 上の制限構造における一階論理式と `A` の有限個のパラメータで定義される `A` の部分集合をちょうど集めます。その所属定理は、後の構成可能性の議論で使う論理式、環境、充足関係を取り出します。
<!--/-->

<!--en-->
Two design points carry the chapter. The formulas take `A`'s small member type
`⟪ A ⟫` as their constant domain, so "parameters from `A`" is enforced by the
type. And satisfaction is the **inner** semantics, on the restricted structure
`𝒮ᵥ ↾ (∈ A)`: quantifiers range over members of `A` only, which is what
"definable *in* `(A, ∈)`" means in the textbook, and which makes the essential
smallness of the previous chapters bite: every formula evaluates small, so
`Def A` is a set with no resizing spent at all.
<!--zh-->
两个设计点撑起本章。公式以 `A` 的小成员类型 `⟪ A ⟫` 为常元域，于是「参数来自 `A`」由类型强制。满足取**内层**语义，在限制结构 `𝒮ᵥ ↾ (∈ A)` 上：量词只跑 `A` 的成员，这正是教科书里「在 `(A, ∈)` **中**可定义」的含义，也让前几章的本质小性咬合发力：任何公式求值皆小，`Def A` 是集合，降层分文未花。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Definability {ℓ : Level} where

open import FOL.ZFStructure using ( ZFStructure; Transitive )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; ⊤̇ )
open import FOL.LevyHierarchy using ( Δ₀ )
open import FOL.Manipulation.ConstantMapping using ( mapFo )
open import FOL.Manipulation.Relabelling using ( mapΔ₀; ⊨-map )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Smallness {ℓ} using ( module InnerSmall )

open import Cubical.Foundations.Equiv
  using ( _≃_; equivFun; invEq; invEquiv; compEquiv; propBiimpl→Equiv )
open import Cubical.Functions.Embedding using ( isEmbedding→Inj )
open import Cubical.Data.Sigma using ( Σ-cong-equiv-snd )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber; presentation
        ; isEmb⟪_⟫↪; _⊆_; extensionality )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open ZFStructure 𝒮ᵥ
```

<!--en-->
## The operator

Everything below is relative to one set `A`, so the chapter works in a module
`DefOf A`. The restriction class is membership in `A`, and the essential
smallness witness `e` is the library's `presentation`{.Agda}: the small member
type `⟪ A ⟫` *is* the restricted carrier, up to equivalence (with the small
membership converted pointwise to the large one). The constant interpretation
`ι` sends a constant, an index in `⟪ A ⟫`, to the corresponding member of the
restricted carrier; its first component is the member itself, definitionally.
<!--zh-->
## 算子

以下一切都相对于一个集合 `A`，故本章在模块 `DefOf A` 中工作。限制类取「属于 `A`」，而本质小见证 `e` 就是库的 `presentation`{.Agda}：小成员类型 `⟪ A ⟫` 与限制载体等价 (小成员关系逐点换成大的即可)。常元解释 `ι` 把常元，即 `⟪ A ⟫` 的索引，送到限制载体的对应成员；其第一分量按定义就是该成员本身。
<!--ja-->
## 演算子

`Def A`{.Agda} は、パラメータなしの論理式、その符号、`A` の要素からなる環境を添字として、論理式を満たす `A` の要素を部分集合として作ります。したがって添字型は小さく、結果は再び階層内の集合です。
<!--/-->



```agda
module DefOf (A : S) where

  M : S → hProp (ℓ-suc ℓ)
  M x = x ∈ˢ A

  e : ⟪ A ⟫ ≃ (Σ[ x ∈ S ] (x ∈ᶜ M))
  e = compEquiv (invEquiv (presentation A))
        (Σ-cong-equiv-snd (λ v →
          propBiimpl→Equiv (snd (v ∈ₛ A)) (snd (v ∈ˢ A))
            (∈∈ₛ {a = v} {b = A} .snd) (∈∈ₛ {a = v} {b = A} .fst)))

  ι : ⟪ A ⟫ → Σ[ x ∈ S ] (x ∈ᶜ M)
  ι = equivFun e

  open InnerSmall M ⟪ A ⟫ e {K = ⟪ A ⟫} ι public
```

<!--en-->
With the inner satisfaction `⊨ᵐ` and its smallness in scope, the operator writes
itself down. `smallSat φ m` is the truth value of `φ` at the member `m`,
compressed one universe down; `defSet φ` is the subset `φ` carves out of `A`,
a `sett` over the members `φ` selects; and `Def A` is the set of all of them,
indexed by the formulas themselves. A formula is a piece of inductive data in
`Type ℓ`, so it is a legitimate small index: **syntax as index set** is the
whole trick.
<!--zh-->
内层满足 `⊨ᵐ` 与其小性就位后，算子自己写出了自己。`smallSat φ m` 是 `φ` 在成员 `m` 处的真值，压低一层宇宙；`defSet φ` 是 `φ` 从 `A` 中刻出的子集，在 `φ` 选中的成员上做 `sett`；`Def A` 则是它们的全体，以公式自身为索引。公式是 `Type ℓ` 里的归纳数据，恰是合法的小索引：**语法当索引集**，全部戏法尽在于此。
<!--/-->

```agda
  smallSat : Formula ⟪ A ⟫ 1 → ⟪ A ⟫ → hProp ℓ
  smallSat φ m = ⊨ᵐ-small φ (ι m ∷ []) .fst

  defSet : Formula ⟪ A ⟫ 1 → S
  defSet φ = sett (Σ[ m ∈ ⟪ A ⟫ ] ⟨ smallSat φ m ⟩) (λ p → ⟪ A ⟫↪ (p .fst))

  Def : S
  Def = sett (Formula ⟪ A ⟫ 1) defSet
```

<!--en-->
## Membership, specified

Both `Def` and each `defSet φ` are `sett`s, so their membership is
*definitionally* "merely hit by the index family". For `Def` this needs no proof
at all: a member of `Def` is merely a `defSet φ`. For the definable subsets, two
specifications: their members stay inside `A`, and a member `⟪ A ⟫↪ m` belongs
to `defSet φ` **exactly when the inner world satisfies `φ` at `m`**, which is
the phrase "definable subset" cashed out literally (the compression `smallSat`
was only an encoding, and the equivalence carries it back).
<!--zh-->
## 隶属，给出规格

`Def` 与每个 `defSet φ` 都是 `sett`，故其隶属**按定义**就是「仅仅被索引族命中」。对 `Def` 这连证明都不必：`Def` 的成员仅仅就是某个 `defSet φ`。对可定义子集则有两条规格：其成员不出 `A`；而成员 `⟪ A ⟫↪ m` 属于 `defSet φ`，**当且仅当内层世界在 `m` 处满足 `φ`**，「可定义子集」这个词组在此被逐字兑现 (压缩 `smallSat` 只是编码，等价把它原样送回)。
<!--ja-->
## 所属の特徴付け

`Def A`{.Agda} の要素であることは、`A` 上の制限構造で、ある符号化された論理式と環境がその部分集合を定義することと同値です。この特徴付けは、定義された集合が `A` の部分集合であることも直ちに与えます。
<!--/-->



```agda
  defSet⊆A : (φ : Formula ⟪ A ⟫ 1) (y : S) → ⟨ y ∈ˢ defSet φ ⟩ → ⟨ y ∈ˢ A ⟩
  defSet⊆A φ y = PT.rec (snd (y ∈ˢ A)) λ { ((m , _) , q) →
    subst (λ v → ⟨ v ∈ˢ A ⟩) q
          (∈∈ₛ {a = ⟪ A ⟫↪ m} {b = A} .snd (∈ₛ⟪ A ⟫↪ m)) }

  private
    ⟪⟫↪-inj : {m' m : ⟪ A ⟫} → ⟪ A ⟫↪ m' ≡ ⟪ A ⟫↪ m → m' ≡ m
    ⟪⟫↪-inj {m'} {m} = isEmbedding→Inj isEmb⟪ A ⟫↪ m' m

  defSet-mem : (φ : Formula ⟪ A ⟫ 1) (m : ⟪ A ⟫)
             → (⟪ A ⟫↪ m ∈ˢ defSet φ) ≡ ((ι m ∷ []) ⊨ᵐ φ)
  defSet-mem φ m = ⇔toPath fwd bwd
    where
    decode = ⊨ᵐ-small φ (ι m ∷ [])
    fwd : ⟨ ⟪ A ⟫↪ m ∈ˢ defSet φ ⟩ → ⟨ (ι m ∷ []) ⊨ᵐ φ ⟩
    fwd = PT.rec (snd ((ι m ∷ []) ⊨ᵐ φ)) λ { ((m' , h) , q) →
      invEq (decode .snd) (subst (λ k → ⟨ smallSat φ k ⟩) (⟪⟫↪-inj q) h) }
    bwd : ⟨ (ι m ∷ []) ⊨ᵐ φ ⟩ → ⟨ ⟪ A ⟫↪ m ∈ˢ defSet φ ⟩
    bwd hφ = ∣ (m , equivFun (decode .snd) hφ) , refl ∣₁
```

<!--en-->
## Def refines, never shrinks

`A` itself is definable: the formula "true" selects everyone, so
`defSet ⊤̇ ≡ A` and hence `A ∈ Def A`. Dually, every member of `Def A` is a
subset of `A`. So `Def` sits between `A` and the power set: it keeps the whole
of `A` as an element and adds only subsets.
<!--zh-->
## Def 只精化，不缩水

`A` 自身可定义：公式「真」选中所有人，于是 `defSet ⊤̇ ≡ A`，从而 `A ∈ Def A`。对偶地，`Def A` 的每个成员都是 `A` 的子集。所以 `Def` 坐落在 `A` 与幂集之间：整个 `A` 保留为元素，添入的只有子集。
<!--ja-->
## Def は細分するが要素を失わない

`Def A`{.Agda} の各要素は `A` の部分集合なので、定義可能冪集合は元の集合を細分します。特に推移性を仮定すると、元の要素自身も定義可能な部分集合として次の段階に現れます。
<!--/-->



```agda
  private
    A-mem : (y : S) → ⟨ y ∈ˢ A ⟩ → Σ[ m ∈ ⟪ A ⟫ ] (⟪ A ⟫↪ m ≡ y)
    A-mem y y∈ = ∈-asFiber {a = y} {b = A} y∈

  defSet⊤≡A : defSet ⊤̇ ≡ A
  defSet⊤≡A = extensionality (defSet ⊤̇) A (sub₁ , sub₂)
    where
    sub₁ : ⟨ defSet ⊤̇ ⊆ A ⟩
    sub₁ y y∈ₛ = ∈∈ₛ {a = y} {b = A} .fst
      (defSet⊆A ⊤̇ y (∈∈ₛ {a = y} {b = defSet ⊤̇} .snd y∈ₛ))
    sub₂ : ⟨ A ⊆ defSet ⊤̇ ⟩
    sub₂ y y∈ₛ =
      let (m , q) = A-mem y (∈∈ₛ {a = y} {b = A} .snd y∈ₛ)
      in subst (λ v → ⟨ v ∈ₛ defSet ⊤̇ ⟩) q
           (∈∈ₛ {a = ⟪ A ⟫↪ m} {b = defSet ⊤̇} .fst
             (subst ⟨_⟩ (sym (defSet-mem ⊤̇ m)) (λ z → z)))

  Def∋⊆A : (x : S) → ⟨ x ∈ˢ Def ⟩ → (y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ y ∈ˢ A ⟩
  Def∋⊆A x = PT.rec (isPropΠ λ y → isPropΠ λ _ → snd (y ∈ˢ A))
    (λ { (φ , q) y y∈x → defSet⊆A φ y (subst (λ s → ⟨ y ∈ˢ s ⟩) (sym q) y∈x) })
```

<!--en-->
## Under transitivity, A ⊆ Def A

When `A` is transitive, each **member** `a` of `A` is itself definable, by the
same two-symbol move that built intersection in the model chapter: the atomic
formula "the variable is a member of `a`". Separation's implicit "∈ A" clause is
what transitivity discharges: members of `a` are already members of `A`, so the
atom carves out exactly `a`. Hence `A ⊆ Def A`: the step loses no one. Combined
with the previous section, iterating `Def` can only accumulate, which is the
shape the constructible tower needs.
<!--zh-->
## 传递性之下，A ⊆ Def A

当 `A` 传递时，`A` 的每个**成员** `a` 自身也可定义，用的正是模型章造交集的那记两符号招式：原子公式「该变量属于 `a`」。分离暗含的「∈ A」条款恰由传递性兑清：`a` 的成员已是 `A` 的成员，于是原子公式刻出的恰好是 `a`。故 `A ⊆ Def A`：这一步不丢任何人。与上一节合观，迭代 `Def` 只进不出，正是可构造塔需要的形状。
<!--ja-->
## 推移性の下で A ⊆ Def A

`A` が推移的なら、各 `x ∈ A` は「変数がパラメータ `x` に等しい」という論理式で `A` 上に定義できます。この定義により `x ∈ Def A` が得られ、`A` は次の定義可能段階に含まれます。
<!--/-->



```agda
  module Refine (Atrans : Transitive 𝒮ᵥ M) where

    atom : ⟪ A ⟫ → Formula ⟪ A ⟫ 1
    atom mₐ = var zero ∈̇ con mₐ

    atom-mem : (mₐ m : ⟪ A ⟫)
             → (⟪ A ⟫↪ m ∈ˢ defSet (atom mₐ)) ≡ (⟪ A ⟫↪ m ∈ˢ ⟪ A ⟫↪ mₐ)
    atom-mem mₐ m = defSet-mem (atom mₐ) m

    defSet-atom≡ : (mₐ : ⟪ A ⟫) → defSet (atom mₐ) ≡ ⟪ A ⟫↪ mₐ
    defSet-atom≡ mₐ = extensionality (defSet (atom mₐ)) (⟪ A ⟫↪ mₐ) (sub₁ , sub₂)
      where
      sub₁ : ⟨ defSet (atom mₐ) ⊆ ⟪ A ⟫↪ mₐ ⟩
      sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ ⟪ A ⟫↪ mₐ))
        (λ { ((m , h) , q) →
          subst (λ v → ⟨ v ∈ₛ ⟪ A ⟫↪ mₐ ⟩) q
            (∈∈ₛ {a = ⟪ A ⟫↪ m} {b = ⟪ A ⟫↪ mₐ} .fst
              (subst ⟨_⟩ (atom-mem mₐ m) ∣ (m , h) , refl ∣₁)) })
        (∈∈ₛ {a = y} {b = defSet (atom mₐ)} .snd y∈ₛ)
      sub₂ : ⟨ ⟪ A ⟫↪ mₐ ⊆ defSet (atom mₐ) ⟩
      sub₂ y y∈ₛ =
        let y∈a     = ∈∈ₛ {a = y} {b = ⟪ A ⟫↪ mₐ} .snd y∈ₛ
            y∈A     = Atrans {x = ⟪ A ⟫↪ mₐ} {y = y} y∈a mₐ-as
            (m , q) = ∈-asFiber {a = y} {b = A} y∈A
        in subst (λ v → ⟨ v ∈ₛ defSet (atom mₐ) ⟩) q
             (∈∈ₛ {a = ⟪ A ⟫↪ m} {b = defSet (atom mₐ)} .fst
               (subst ⟨_⟩ (sym (atom-mem mₐ m))
                 (subst (λ v → ⟨ v ∈ˢ ⟪ A ⟫↪ mₐ ⟩) (sym q) y∈a)))
        where
        mₐ-as : ⟨ ⟪ A ⟫↪ mₐ ∈ˢ A ⟩
        mₐ-as = ∈∈ₛ {a = ⟪ A ⟫↪ mₐ} {b = A} .snd (∈ₛ⟪ A ⟫↪ mₐ)

    A⊆Def : (a : S) → ⟨ a ∈ˢ A ⟩ → ⟨ a ∈ˢ Def ⟩
    A⊆Def a a∈ =
      let (mₐ , q) = ∈-asFiber {a = a} {b = A} a∈
      in ∣ atom mₐ , defSet-atom≡ mₐ ∙ q ∣₁
```

<!--en-->
### Definability read from outside

One consequence deserves its own name, because the constructible-stage proofs lean on it repeatedly.
Membership in `defSet φ` is a statement of the *inner* world `(A, ∈)`, and the
arguments to come are conducted in the ambient hierarchy. For a Δ₀ formula the
two readings agree, which is the absoluteness theorem; what remains is
bookkeeping, since absoluteness is stated over the members of the class while
`defSet` is stated over the small index type. Relabelling closes that gap, and
the whole proof is a three-step path: the specification of `defSet`, then the
relabelling of the formula, then absoluteness.
<!--zh-->
### 从外部读可定义性

有一条推论值得单独命名，因为可构造阶段的证明要反复倚重它。属于 `defSet φ` 是**内层**世界 `(A, ∈)` 的陈述，而接下来的论证都在环境层级中进行。对 Δ₀ 公式，两种读法一致，那就是绝对性定理；余下的是记账，因为绝对性对类的成员陈述，而 `defSet` 对小索引类型陈述。重标填平这道缝，整个证明是一条三步路径：`defSet` 的规格、公式的重标、然后绝对性。
<!--ja-->
### 外部から読む定義可能性

推移的な `A` では、制限構造の充足関係を周囲の構造へ移せます。そのため `Def A`{.Agda} の所属は、`A` への相対化を用いた外部の論理式としても読めます。
<!--/-->

<!--en-->
`A` must be transitive for this, which is why the lemma lives in this
submodule; every stage of the tower is.
<!--zh-->
这需要 `A` 传递，故本引理住在这个子模块里；塔的每个阶段都传递。
<!--/-->

```agda
    module Abs = FOL.Absoluteness.Single 𝒮ᵥ M Atrans

    abs-defSet : (φ : Formula ⟪ A ⟫ 1) → Δ₀ φ → (m : ⟪ A ⟫)
               → (⟪ A ⟫↪ m ∈ˢ defSet φ)
                 ≡ ((⟪ A ⟫↪ m ∷ []) Abs.⊨ᵛ (mapFo ι φ))
    abs-defSet φ d m =
        defSet-mem φ m
      ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) Abs.𝒮M ι id φ (ι m ∷ []))
      ∙ Abs.abs₀ (mapΔ₀ ι d) (ι m ∷ [])
```

<!--en-->
## Recap

`Def A` is the set of subsets of `A` definable in the inner world `(A, ∈)` with
parameters from `A`: syntax as index set, inner satisfaction for meaning,
essential smallness footing the universe bill. The specification
`defSet-mem`{.Agda} says "definable" literally, and the operator only refines:
`A ⊆ Def A` under transitivity (`A⊆Def`{.Agda}), and members of `Def A` never
leave `A`'s subsets (`Def∋⊆A`{.Agda}). The next chapter iterates this step
into a universe.
<!--zh-->
## 小结

`Def A` 是内层世界 `(A, ∈)` 中带 `A` 中参数可定义的 `A` 的子集之集：语法当索引集，内层满足给含义，本质小性付清宇宙账单。规格 `defSet-mem`{.Agda} 把「可定义」逐字兑现，而算子只精化：传递性下 `A ⊆ Def A` (`A⊆Def`{.Agda})，且 `Def A` 的成员不出 `A` 的子集 (`Def∋⊆A`{.Agda})。下一章把这一步迭代成一个宇宙。
<!--ja-->
## まとめ

`Def A`{.Agda} は有限パラメータ付き論理式で定義される `A` の部分集合を集め、その所属定理が定義データを取り出します。推移的な `A` では `A ⊆ Def A` が成り立ち、内部と外部の定義可能性が対応します。
<!--/-->

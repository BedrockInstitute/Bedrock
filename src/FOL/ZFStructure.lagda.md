```agda
{-# OPTIONS --cubical --safe --guardedness #-}
module FOL.ZFStructure where
```

<!--en-->
# Structures
<!--zh-->
# 结构
<!--ja-->
# 構造
<!--/-->

```agda
open import Base.Prelude
```

<!--en-->

The preceding chapter told us which claims about sets can be written, but not what would make one true. Before asking whether a written claim holds, we must decide what objects its expressions can refer to and how to test the two basic claims: that two objects are equal or that one belongs to the other. A **structure** supplies those choices.

This chapter specifies the data of a structure, then constructs its restriction to the objects satisfying a chosen property. No set-theoretic axiom is assumed here.
<!--zh-->

上一章规定了关于集合的陈述可以怎样写，却还没有说明它们何时成立。要讨论一条陈述是否成立，首先要选定它所谈论的对象，再为「两个对象相等」和「一个对象属于另一个」给出解释。这些数据合在一起，就构成一个**结构**。

本章先定义结构，再把对象的范围限制为满足某种性质的那些对象，构造相应的限制结构。整个过程不假设任何集合论公理。
<!--ja-->

前章では集合についてどのような主張を書けるかを定めたが、その主張がいつ成り立つかはまだ決めていない。書かれた主張の意味を定めるには、そこで指す対象の範囲と、二つの基本的な関係、すなわち対象どうしの等しさと所属をどう判定するかを選ぶ必要がある。その選択を与えるのが**構造**である。

本章ではまず構造に必要なデータを定め、続いて、ある性質を満たす対象だけに制限した構造を作る。ここでは集合論の公理を仮定しない。
<!--/-->

<!--en-->
## Carrier and relations

In the [object language]{.term-ref #object-language}, `t ≐ u`{.Agda} and `t ∈̇ u`{.Agda} are [formulas]{.term-ref #object-formula}, not yet propositions that can be proved. To interpret them, choose a type `S` of objects and two relations on it. We write `𝒮` for the resulting structure and `x`, `y` for elements of its **carrier** `S`. The superscript `ˢ` marks the relations supplied by `𝒮`.

Why supply an equality relation instead of using Agda's path equality `x ≡ y`{.Agda}? The object-language equality sign needs an interpretation of its own. The field `x ≈ˢ y`{.Agda} can assign a truth value even when no path `x ≡ y`{.Agda} is given. At this stage the field is just a binary relation; we have not required the laws of equality or any compatibility with membership.
<!--zh-->
## 载体与关系

在[对象语言]{.term-ref #object-language}中，`t ≐ u`{.Agda} 与 `t ∈̇ u`{.Agda} 是[公式]{.term-ref #object-formula}，还不是可以证明的命题。要解释它们，先选定一个类型 `S`，用它的元素表示所讨论的对象，再在 `S` 上给出相等与成员关系。类型 `S` 称为结构的**载体**。我们把整个结构记作 `𝒮`，把载体中的元素记作 `x`、`y`；关系记号上的 `ˢ` 则表示该关系由 `𝒮` 提供。

为什么相等关系也要单独给出，而不直接采用 Agda 的路径相等 `x ≡ y`{.Agda}？因为[对象语言]{.term-ref #object-language}中的相等记号可以有自己的解释，不必预先等同于路径相等。结构中的 `x ≈ˢ y`{.Agda} 给出一个真值，并不要求先有一条路径 `x ≡ y`{.Agda}。在这个定义中，`≈ˢ`{.Agda} 只是一个二元关系：我们既不要求它满足相等关系的定律，也不要求它与成员关系相容。
<!--ja-->
## 台と関係

[対象言語]{.term-ref #object-language}の `t ≐ u`{.Agda} と `t ∈̇ u`{.Agda} は[論理式]{.term-ref #object-formula}であり、まだ証明できる命題ではない。その意味を定めるには、対象の型 `S` と、その上の二つの関係を選ぶ。得られる構造を `𝒮`、その**台** `S` の元を `x`、`y` と書く。上付きの `ˢ` は、関係が構造 `𝒮` から与えられることを示す。

等号の関係まで別に与え、Agda のパス等式 `x ≡ y`{.Agda} をそのまま使わないのはなぜか。[対象言語]{.term-ref #object-language}の等号には独自の解釈が必要だからである。パス `x ≡ y`{.Agda} が与えられていなくても、フィールド `x ≈ˢ y`{.Agda} は真理値を与えられる。この段階では単なる二項関係であり、等号の法則も、所属との整合性もまだ要求しない。
<!--/-->

<!--en-->
**Definition** (`ZFStructure`{.Agda}) At carrier level `ℓ`, the `record`{.Agda} takes a truth-value type `Ω` as a parameter. Its fields are a carrier `S : Type ℓ`{.Agda}, a proof that `S` is an h-set, and two relations `S → S → Ω`{.Agda} for equality and membership. The level of `Ω` need not equal `ℓ`. Keeping this underlying definition general lets us choose the truth values separately. No laws for either relation are assumed.
<!--zh-->
**定义** (`ZFStructure`{.Agda}) 给定载体的层级 `ℓ` 和真值类型 `Ω`，用 `record`{.Agda} 定义结构。其字段包括载体 `S : Type ℓ`{.Agda}、`S` 为 h-集合的证明，以及两个类型为 `S → S → Ω`{.Agda} 的关系，分别解释相等与成员关系。`Ω` 的层级不必与 `ℓ` 相同。这样，底层定义保持一般性，真值类型可以独立选择。两种关系都不附加任何定律。
<!--ja-->
**定義** (`ZFStructure`{.Agda}) 台がレベル `ℓ` にあるとき、このレコードは真理値の型 `Ω` を引数に取る。フィールドは台 `S : Type ℓ`{.Agda}、`S` が h-集合である証明、および等号と所属を解釈する二つの `S → S → Ω`{.Agda} 型の関係である。`Ω` のレベルは `ℓ` と一致しなくてもよい。基礎となる定義をこのように一般的に保ち、具体的な真理値は別に選ぶ。この時点で二つの関係には法則を課さない。
<!--/-->

```agda
record ZFStructure (ℓ : Level) {ℓΩ : Level} (Ω : Type ℓΩ)
  : Type (ℓ-max (ℓ-suc ℓ) ℓΩ) where
  infix 20 _≈ˢ_ _∈ˢ_
  field
    S         : Type ℓ
    isSetS    : isSet S
```

<!--en-->
The remaining fields give a truth value for each ordered pair of carrier elements. The value `x ∈ˢ y`{.Agda} belongs to `Ω`; `t ∈̇ u`{.Agda} from the previous chapter is still a piece of syntax. The `record`{.Agda} does not yet say how [terms]{.term-ref #object-term} denote elements, nor whether either relation obeys a set-theoretic axiom.
<!--zh-->
余下两个字段各自接收两个载体元素，并返回一个真值。因此，`x ∈ˢ y`{.Agda} 是 `Ω` 中的一个值，而上一章的 `t ∈̇ u`{.Agda} 只是一段语法。这个 `record`{.Agda} 只提供载体和关系，不规定[词项]{.term-ref #object-term}怎样指代载体元素，也不要求两种关系满足集合论公理。
<!--ja-->
残る二つのフィールドは、台の元の組ごとに真理値を与える。`x ∈ˢ y`{.Agda} の値は `Ω` に属するが、前章の `t ∈̇ u`{.Agda} はまだ構文にすぎない。このレコードは、[項]{.term-ref #object-term}が台の元をどう指すかも、二つの関係が集合論の公理を満たすかどうかも定めない。
<!--/-->

```agda
    _≈ˢ_ _∈ˢ_ : S → S → Ω
```

<!--en-->
**Definition** (`ZFStructureₕ`{.Agda}) For the proposition-valued structures used below, choose `hProp ℓ`{.Agda} as the truth-value type Ω. The subscript `ₕ` marks this choice at the carrier's level without introducing another `record`{.Agda}.
<!--zh-->
**定义** (`ZFStructureₕ`{.Agda}) 取 `hProp ℓ`{.Agda} 为真值类型 Ω，得到下文使用的命题值结构。下标 `ₕ` 表示这一选择，其中命题与载体处于同一层级 `ℓ`。这只是原定义的一个特例，不另设 `record`{.Agda}。
<!--ja-->
**定義** (`ZFStructureₕ`{.Agda}) 以下で使う命題値の構造では、真理値の型 Ω に `hProp ℓ`{.Agda} を選ぶ。添字 `ₕ` は台のレベルでこの選択を表し、別のレコードを導入しない。
<!--/-->

```agda
ZFStructureₕ : (ℓ : Level) → Type (ℓ-suc ℓ)
ZFStructureₕ ℓ = ZFStructure ℓ (hProp ℓ)
```

<!--en-->
The name `ZFStructure`{.Agda} identifies the language whose symbols are to be interpreted, not a model already satisfying ZF. One could, for example, use natural numbers as the carrier and interpret the membership field by their usual order. That supplies the required data, but certainly does not prove the ZF axioms.

## Proposition-valued structures

For a `ZFStructureₕ`{.Agda}, the field `x ∈ˢ y`{.Agda} returns an `hProp`{.Agda}, a proposition together with its proof-irrelevance. To use a proof of that proposition as an argument, we pass to its underlying type `⟨ x ∈ˢ y ⟩`{.Agda}. The submodule `hPropView`{.Agda} keeps a structure `𝒮` fixed and gives this type the notation `x ∈ᵗ y`{.Agda}.
<!--zh-->
`ZFStructure`{.Agda} 这个名字表明它解释的是集合论语言，并不表示它已经是 ZF 模型。例如，可以用自然数作载体，用通常的大小关系解释成员关系。即使提供了定义所要求的全部数据，也不能仅凭这些数据断言 ZF 公理成立。

## 命题值结构

在命题值结构 `ZFStructureₕ`{.Agda} 中，`x ∈ˢ y`{.Agda} 包含一个类型，以及该类型为命题的证明。若要把「`x` 属于 `y`」的证明作为函数实参，就需要取出底层类型 `⟨ x ∈ˢ y ⟩`{.Agda}。子模块 `hPropView`{.Agda} 固定结构 `𝒮`，将这个类型简记为 `x ∈ᵗ y`{.Agda}。
<!--ja-->
`ZFStructure`{.Agda} という名前は解釈する記号が集合論の言語に属することを示すのであって、すでに ZF のモデルであるという意味ではない。たとえば自然数を台とし、通常の大小関係を所属のフィールドに入れても、ここで必要なデータはそろう。しかしそれだけで ZF の公理が証明されるわけではない。

## 命題値の構造

`ZFStructureₕ`{.Agda} では、フィールド `x ∈ˢ y`{.Agda} は `hProp`{.Agda}、すなわち命題とその証明無関係性を返す。その命題の証明を関数の引数として使うには、基礎となる型 `⟨ x ∈ˢ y ⟩`{.Agda} を取り出す。部分モジュール `hPropView`{.Agda} は構造 `𝒮` を固定し、この型を `x ∈ᵗ y`{.Agda} と書けるようにする。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module hPropView {ℓ} (𝒮 : ZFStructureₕ ℓ) where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
We first open `ZFStructure 𝒮`{.Agda} with `public`, so that `hPropView`{.Agda} "inherits" all the fields of `ZFStructure`{.Agda} at `𝒮`. They are available inside the submodule and re-exported to modules that open this view; no new structure is created.
<!--zh-->
先用 `public` 打开 `ZFStructure 𝒮`{.Agda}，使 `hPropView`{.Agda}「继承」`ZFStructure`{.Agda} 在 `𝒮` 上的所有字段。这些字段既可在子模块内直接使用，也会一并提供给打开此视图的模块；这里并没有新建结构。
<!--ja-->
まず `public` を付けて `ZFStructure 𝒮`{.Agda} を開き、`hPropView`{.Agda} が `𝒮` における `ZFStructure`{.Agda} の全フィールドを「継承」するようにする。これらのフィールドは部分モジュール内で使えるだけでなく、このビューを開くモジュールにも公開される。新しい構造を作るわけではない。
<!--/-->

```agda
  open ZFStructure 𝒮 public
```

<!--en-->
An inhabitant of `y ∈ᵗ x`{.Agda} is a proof that `y` belongs to `x` in this structure. The left argument is the member, just as for `∈ˢ`{.Agda}; we give the two notations the same binding strength.
<!--zh-->
`y ∈ᵗ x`{.Agda} 的元素就是「`y` 在该结构中属于 `x`」的证明。它与 `∈ˢ`{.Agda} 的写法一致：属于另一个对象的元素写在左侧，两个记号的结合强度也相同。
<!--ja-->
`y ∈ᵗ x`{.Agda} の元は、この構造で `y` が `x` に属することの証明である。`∈ˢ`{.Agda} と同じく左側が所属する元であり、二つの記法の結び付きの強さも同じにする。
<!--/-->

<!--en-->
**Definition** (`_∈ᵗ_`{.Agda}) For carrier elements `x` and `y`, let `x ∈ᵗ y`{.Agda} be the underlying type of `x ∈ˢ y`{.Agda}.
<!--zh-->
**定义** (`_∈ᵗ_`{.Agda}) 对载体元素 `x`、`y`，定义 `x ∈ᵗ y`{.Agda} 为 `x ∈ˢ y`{.Agda} 的底层类型。
<!--ja-->
**定義** (`_∈ᵗ_`{.Agda}) 台の元 `x`、`y` に対し、`x ∈ᵗ y`{.Agda} を `x ∈ˢ y`{.Agda} の基礎型と定める。
<!--/-->

```agda
  infix 20 _∈ᵗ_
  _∈ᵗ_ : S → S → Type ℓ
  x ∈ᵗ y = ⟨ x ∈ˢ y ⟩
```

<!--en-->
### Transitive classes

Suppose a class `M` selects some elements of the carrier. If `x` is selected and `y` belongs to `x` according to the structure, must `y` also be selected? A **transitive class** is one for which the answer is yes. This is closure under *members*, not under subsets.
<!--zh-->
### 传递类

设类 `M` 选出了载体中的一部分对象。若 `x` 已被选中，`y` 又按结构中的成员关系属于 `x`，那么 `y` 是否也被选中？如果答案总是肯定的，就称 `M` 为**传递类**。这里要求的是对*元素*闭合，而不是对子集闭合。
<!--ja-->
### 推移的クラス

クラス `M` が台の元をいくつか選ぶとする。選ばれた `x` に、構造の所属関係によって `y` が属するなら、`y` も選ばれるだろうか。常にそうなるクラスを**推移的クラス**という。これは*要素*についての閉性であり、部分集合についての閉性ではない。
<!--/-->

<!--en-->
Transitivity is a closure condition on a class, not a field of the structure. It uses the underlying membership proof type, so it belongs to `hPropView`{.Agda}, where the proposition-valued structure is already fixed.
<!--zh-->
传递性是对类的闭合性要求，不是结构的字段。它使用成员关系的证明类型，因此放在 `hPropView`{.Agda} 中，沿用子模块已固定的命题值结构。
<!--ja-->
推移性はクラスに課す閉性の条件であり、構造のフィールドではない。所属の証明の型を使うため、命題値の構造を固定した `hPropView`{.Agda} の中に置く。
<!--/-->


<!--en-->
**Definition** (`Transitive`{.Agda}) For a proposition-valued structure `𝒮` and a class `M`, transitivity assigns, to any carrier elements `x` and `y`, a proof of `y ∈ᶜ M`{.Agda} from proofs of `y ∈ᵗ x`{.Agda} and `x ∈ᶜ M`{.Agda}. The quantification over `x` and `y` is implicit in the code.
<!--zh-->
**定义** (`Transitive`{.Agda}) 给定命题值结构 `𝒮` 与类 `M`。若对任意载体元素 `x`、`y`，都能由 `y ∈ᵗ x`{.Agda} 和 `x ∈ᶜ M`{.Agda} 的证明得到 `y ∈ᶜ M`{.Agda} 的证明，就称 `M` 具有传递性。代码将 `x`、`y` 作为隐式参数。
<!--ja-->
**定義** (`Transitive`{.Agda}) 命題値の構造 `𝒮` とクラス `M` に対し、推移性とは、任意の台の元 `x`、`y` について、`y ∈ᵗ x`{.Agda} と `x ∈ᶜ M`{.Agda} の証明から `y ∈ᶜ M`{.Agda} の証明を与えることである。コードでは `x`、`y` を暗黙に量化する。
<!--/-->

```agda
  Transitive : (S → hProp ℓ) → Type ℓ
  Transitive M = ∀ {x y} → y ∈ᵗ x → x ∈ᶜ M → y ∈ᶜ M
```
</div>
</details>

<!--en-->
The similar membership signs now play different roles. In particular, a [class]{.term-ref #class} is a predicate `M : S → hProp ℓ`{.Agda}, so `x ∈ᶜ M`{.Agda} asks whether an element satisfies that predicate; it does not compare two carrier elements.

| notation | what it relates | what it gives |
| --- | --- | --- |
| `t ∈̇ u`{.Agda} | two [terms]{.term-ref #object-term} | a [formula]{.term-ref #object-formula}, with no truth value yet |
| `x ∈ˢ y`{.Agda} | two carrier elements | a proposition in `hProp ℓ`{.Agda} |
| `x ∈ᵗ y`{.Agda} | the same two elements | the underlying proof type of `x ∈ˢ y`{.Agda} |
| `x ∈ᶜ M`{.Agda} | an element and a class | the underlying proof type of `M x`{.Agda} |
: Four membership notations and their distinct roles
<!--zh-->
这几个成员关系记号写法相近，含义却不同。还要注意，[类]{.term-ref #class}由谓词 `M : S → hProp ℓ`{.Agda} 给出。因此，`x ∈ᶜ M`{.Agda} 表示元素 `x` 满足谓词 `M`，说的不是两个载体元素之间的关系。

| 记号 | 两侧的对象 | 得到的结果 |
| --- | --- | --- |
| `t ∈̇ u`{.Agda} | 两个[词项]{.term-ref #object-term} | 尚未赋予真值的[公式]{.term-ref #object-formula} |
| `x ∈ˢ y`{.Agda} | 两个载体元素 | `hProp ℓ`{.Agda} 中的命题 |
| `x ∈ᵗ y`{.Agda} | 同样的两个元素 | `x ∈ˢ y`{.Agda} 的底层证明类型 |
| `x ∈ᶜ M`{.Agda} | 一个元素与一个类 | `M x`{.Agda} 的底层证明类型 |
: 四种成员关系记号各自的用途
<!--ja-->
よく似た所属の記法にも、それぞれ異なる役割がある。特に[クラス]{.term-ref #class}は述語 `M : S → hProp ℓ`{.Agda} である。したがって `x ∈ᶜ M`{.Agda} は元がその述語を満たすかを問い、台の二つの元を比較するものではない。

| 記法 | 関係するもの | 得られるもの |
| --- | --- | --- |
| `t ∈̇ u`{.Agda} | 二つの[項]{.term-ref #object-term} | まだ真理値を与えていない[論理式]{.term-ref #object-formula} |
| `x ∈ˢ y`{.Agda} | 二つの台の元 | `hProp ℓ`{.Agda} の命題 |
| `x ∈ᵗ y`{.Agda} | 同じ二つの元 | `x ∈ˢ y`{.Agda} の基礎となる証明の型 |
| `x ∈ᶜ M`{.Agda} | 元とクラス | `M x`{.Agda} の基礎となる証明の型 |
: 四つの所属記法とそれぞれの役割
<!--/-->

<!--en-->
## Substructures

To make the variables range over only the elements selected by `M`, we need a new carrier. It is not enough to keep the old type `S` and merely remember `M` alongside it: a variable of type `S` could still denote an unselected element. Instead, each element of the new carrier includes both an `x : S`{.Agda} and evidence that `x ∈ᶜ M`{.Agda}. The notation `𝒮 ↾ M`{.Agda} means the structure `𝒮` restricted to this class.
<!--zh-->
## 子结构

若要让变元只在 `M` 选中的元素中取值，就需要更换载体。仅仅给出谓词 `M`，却仍以整个 `S` 为载体，并不能限制取值范围。因此，新载体的每个元素都由两部分组成：一个 `x : S`{.Agda}，以及 `x ∈ᶜ M`{.Agda} 的证明。把结构 `𝒮` 限制到类 `M` 所得的结构，记作 `𝒮 ↾ M`{.Agda}。
<!--ja-->
## 部分構造

変数が `M` に選ばれた元だけを動くようにするには、台を作り直す必要がある。元の型 `S` を残して横に `M` を添えるだけでは、`S` 型の変数は選ばれなかった元も指せてしまう。そこで新しい台の各元を、`x : S`{.Agda} と `x ∈ᶜ M`{.Agda} の証拠の組にする。`𝒮 ↾ M`{.Agda} は、構造 `𝒮` をこのクラスへ制限したものを表す。
<!--/-->

<!--en-->
Restriction does not require transitivity or proposition-valued relations: the structure may use any truth-value type `Ω`. Only the predicate selecting carrier elements must be proposition-valued. We open the carrier-related field projections at module scope, leaving the two relations to be opened at a fixed structure where needed. Unlike the opening inside `hPropView`{.Agda}, this does not fix a structure: each projection takes it as an argument, as in `S 𝒮`{.Agda}. Here `𝒮` plays the role of a subscript on `S` in mathematical notation, specifying whose carrier we mean; in Agda it is an ordinary function argument.
<!--zh-->
限制结构不要求类具有传递性，也不要求原结构的关系取命题值：真值类型 `Ω` 可以任意选择，只有筛选载体元素的谓词需要取命题值。下面在本模块中打开载体相关的字段投影，两个关系则留到使用时再针对具体结构打开。与 `hPropView`{.Agda} 内的打开方式不同，这里不固定结构，而是在使用各投影时传入结构，例如用 `S 𝒮`{.Agda} 取得 `𝒮` 的载体。其中，`𝒮` 的作用相当于数学记号中 `S` 的下标，指明这是哪个结构的载体；在 Agda 中，它仍是普通的函数实参。
<!--ja-->
構造の制限には、クラスの推移性も、関係が命題に値を取るという条件も要らない。真理値の型 `Ω` は任意であり、台の元を選ぶ述語だけが命題値であればよい。以下では台に関するフィールドの射影をモジュールのスコープで開き、二つの関係は使う場所で構造を固定して開く。`hPropView`{.Agda} の内部とは異なり、構造は固定せず、`S 𝒮`{.Agda} のように各射影へ構造を引数として渡す。ここで `𝒮` は、数学の記法で `S` に付ける添字に相当し、どの構造の台かを指定する。ただし Agda では通常の関数の引数である。
<!--/-->

```agda
open ZFStructure hiding ( _≈ˢ_; _∈ˢ_ )
```

<!--en-->
**Definition** (`_↾_`{.Agda}) For any class `M : S → hProp ℓ`{.Agda}, the restricted structure has carrier `Σ[ x ∶ S ] (x ∈ᶜ M)`{.Agda}. This is a type of dependent pairs, not a set within the structure representing the class. The previously introduced `isSetClass`{.Agda} supplies its h-set proof from `isSetS`{.Agda} and the propositionhood of each membership type.
<!--zh-->
**定义** (`_↾_`{.Agda}) 给定类 `M : S → hProp ℓ`{.Agda}，限制结构的载体为 `Σ[ x ∶ S ] (x ∈ᶜ M)`{.Agda}。这是一个依值对类型，并不是在原结构内部找到了一个代表类 `M` 的集合。原载体是 h-集合，而每个元素属于 `M` 的证明类型都是命题，因此可用前文引入的 `isSetClass`{.Agda} 证明新载体也是 h-集合。
<!--ja-->
**定義** (`_↾_`{.Agda}) 任意のクラス `M : S → hProp ℓ`{.Agda} に対し、制限された構造の台を `Σ[ x ∶ S ] (x ∈ᶜ M)`{.Agda} とする。これは依存対の型であり、構造の内部でそのクラスを表す集合ではない。先に導入した `isSetClass`{.Agda} を `isSetS`{.Agda} と各点で所属の型が命題であることに適用し、新しい台の h-集合性を得る。
<!--/-->

```agda
infixl 21 _↾_
_↾_ : ∀ {ℓ ℓΩ} {Ω : Type ℓΩ} (𝒮 : ZFStructure ℓ Ω)
    → (S 𝒮 → hProp ℓ) → ZFStructure ℓ Ω
_↾_ {ℓ} 𝒮 M = record
  { S      = Σ[ x ∶ S 𝒮 ] (x ∈ᶜ M)
  ; isSetS = isSetClass (isSetS 𝒮) (λ x → ⟨ M x ⟩isProp)
```

<!--en-->
How should the two relations act on these pairs? For restricted elements `a` and `b`, apply the relations of `𝒮` to their first projections: `a .fst ≈ˢ b .fst`{.Agda} and `a .fst ∈ˢ b .fst`{.Agda}. We open just these two relations locally in the definition below. The proofs stored in the second components certify that the elements lie in `M`; they do not alter the truth values of equality or membership. Thus the relation fields are pulled back from `𝒮` along `fst`{.Agda}.
<!--zh-->
新载体上的两种关系怎样定义？给定其中的元素 `a`、`b`，先取出各自的第一分量，再应用 `𝒮` 的关系，得到 `a .fst ≈ˢ b .fst`{.Agda} 与 `a .fst ∈ˢ b .fst`{.Agda}。下面的定义只在局部打开原结构的这两个关系。第二分量只证明第一分量属于 `M`，不影响这两种关系的真值。也就是说，新关系是原关系沿第一投影 `fst`{.Agda} 的拉回。
<!--ja-->
新しい台の上で二つの関係をどう定めるか。制限された元 `a`、`b` の第一射影に `𝒮` の関係を適用し、`a .fst ≈ˢ b .fst`{.Agda} と `a .fst ∈ˢ b .fst`{.Agda} を得る。以下の定義では、元の構造のこの二つの関係だけを局所的に開く。第二成分の証拠は元が `M` に属することを保証するだけで、等号や所属の真理値を変えない。つまり二つの関係を `fst`{.Agda} に沿って `𝒮` から引き戻す。
<!--/-->

```agda
  ; _≈ˢ_   = λ a b → a .fst ≈ˢ b .fst
  ; _∈ˢ_   = λ a b → a .fst ∈ˢ b .fst }
  where open ZFStructure 𝒮 using ( _≈ˢ_; _∈ˢ_ )
```

<!--en-->
The relations use only the first components. Does equality of the dependent pairs themselves depend on the certificates in their second components? Here we mean Agda's path equality, not the freely chosen structure relation `≈ˢ`{.Agda}.
<!--zh-->
这两种关系都只用到第一分量。那么，两个依值对本身是否相等，会不会受到第二分量的影响？这里讨论的是 Agda 的路径相等，而不是结构中另行指定的关系 `≈ˢ`{.Agda}。
<!--ja-->
二つの関係は第一成分だけを使う。それでは、依存対そのものの等しさは第二成分の証拠に左右されるだろうか。ここで扱うのは Agda のパス等式であり、自由に与えた構造の関係 `≈ˢ`{.Agda} ではない。
<!--/-->

<!--en-->
**Lemma** (`↾-reflects`{.Agda}) For `a` and `b` in the restricted carrier, a path `a .fst ≡ b .fst`{.Agda} determines a path `a ≡ b`{.Agda}.
<!--zh-->
**引理** (`↾-reflects`{.Agda}) 给定限制结构的载体元素 `a`、`b`，由路径 `a .fst ≡ b .fst`{.Agda} 可得路径 `a ≡ b`{.Agda}。
<!--ja-->
**補題** (`↾-reflects`{.Agda}) 制限された台の `a`、`b` について、パス `a .fst ≡ b .fst`{.Agda} からパス `a ≡ b`{.Agda} が定まる。
<!--/-->

<!--en-->
**Proof** Transport one certificate along the given path between the first components. The two certificates then inhabit the same proposition and hence are equal, yielding a path between the dependent pairs. The library lemma `Σ≡Prop`{.Agda} carries out this construction; `⟨ M x ⟩isProp`{.Agda} supplies its required proof that each fibre is a proposition.
<!--zh-->
**证明** 沿第一分量之间的给定路径，传输其中一份证明。传输后，两份证明属于同一个命题，因而相等，由此得到两个依值对之间的路径。库引理 `Σ≡Prop`{.Agda} 完成这一构造；所需的条件由 `⟨ M x ⟩isProp`{.Agda} 给出，即每个第二分量的类型都是命题。
<!--ja-->
**証明** 第一成分の間に与えられたパスに沿って、一方の証拠を移す。移した後の二つの証拠は同じ命題に属するので等しく、依存対の間のパスが得られる。この構成はライブラリの補題 `Σ≡Prop`{.Agda} が行う。その前提である各ファイバーの命題性は `⟨ M x ⟩isProp`{.Agda} が与える。
<!--/-->

```agda
↾-reflects : ∀ {ℓ ℓΩ} {Ω : Type ℓΩ} {𝒮 : ZFStructure ℓ Ω}
             {M : S 𝒮 → hProp ℓ} {a b : S (𝒮 ↾ M)}
           → a .fst ≡ b .fst → a ≡ b
↾-reflects {M = M} = Σ≡Prop (λ x → ⟨ M x ⟩isProp)
```

<!--en-->
The converse needs no special lemma: applying `fst`{.Agda} to a path `a ≡ b`{.Agda} gives `a .fst ≡ b .fst`{.Agda}.
<!--zh-->
反方向更直接：将 `fst`{.Agda} 作用于路径 `a ≡ b`{.Agda}，就得到 `a .fst ≡ b .fst`{.Agda}，无需另设引理。
<!--ja-->
逆向きに特別な補題は要らない。パス `a ≡ b`{.Agda} に `fst`{.Agda} を作用させれば `a .fst ≡ b .fst`{.Agda} が得られる。
<!--/-->

<!--en-->
## Recap

A structure supplies a carrier and interpretations of equality and membership. For any truth-value type, we can restrict the carrier by a proposition-valued predicate while inheriting both relations; membership proofs do not distinguish dependent pairs whose first components are equal. For proposition-valued structures, transitivity is a separate condition: members of selected objects must also be selected. The next chapter uses a chosen structure to interpret [terms]{.term-ref #object-term} and [formulas]{.term-ref #object-formula}.
<!--zh-->
## 小结

结构给出了所讨论的对象，以及相等和成员关系的解释。无论结构选用什么真值，都可以用命题值谓词限制载体，并继承原来的两种关系；附带的成员关系证明不会区分第一分量相等的依值对。对于命题值结构，传递性是另一项独立条件，要求被选中对象的元素也留在选定范围内。下一章将在选定的结构中解释[词项]{.term-ref #object-term}与[公式]{.term-ref #object-formula}。
<!--ja-->
## まとめ

構造は、考察する対象の台と、等号・所属の解釈を与える。真理値の型によらず、二つの関係を受け継ぎながら、命題値の述語で台を制限できる。添えられた所属の証拠は、第一成分が等しい依存対を区別しない。命題値の構造では、推移性はこれとは独立の条件であり、選ばれた対象に属する要素も選ばれた範囲に残ることを要求する。次章では、選んだ構造の中で[項]{.term-ref #object-term}と[論理式]{.term-ref #object-formula}に意味を与える。
<!--/-->

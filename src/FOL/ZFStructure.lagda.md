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

This chapter specifies only the data needed to begin. It then considers what happens when we keep just the objects satisfying a chosen property. The resulting structure will let later chapters interpret such claims over a smaller range of objects. No set-theoretic axiom is assumed here.
<!--zh-->

上一章规定了关于集合的陈述可以怎样写，却还没有说它们何时成立。要判断这些陈述，先得选定其中的表达式可以指向哪些对象，以及怎样判断两种基本关系：两个对象相等、一个对象属于另一个。提供这些选择的，就是一个**结构**。

本章先确定所需的基本数据，再考察只保留满足某种性质的对象时会怎样。这样得到的新结构，让后文可以在更小的范围内解释这些陈述。这里尚不假设任何集合论公理。
<!--ja-->

前章では集合についてどのような主張を書けるかを定めたが、その主張がいつ成り立つかはまだ決めていない。書かれた主張の意味を定めるには、そこで指す対象の範囲と、二つの基本的な関係、すなわち対象どうしの等しさと所属をどう判定するかを選ぶ必要がある。その選択を与えるのが**構造**である。

本章ではまず必要なデータだけを定め、続いて、ある性質を満たす対象だけに範囲を狭める方法を考える。得られた構造を使えば、後の章でより小さな範囲について主張を解釈できる。ここでは集合論の公理を仮定しない。
<!--/-->

<!--en-->
## Carrier and relations

In the [object language]{.term-ref #object-language}, `t ≐ u`{.Agda} and `t ∈̇ u`{.Agda} are [formulas]{.term-ref #object-formula}, not yet propositions that can be proved. To interpret them, choose a type `S` of objects and two relations on it. We write `𝒮` for the resulting structure and `x`, `y` for elements of its **carrier** `S`. The superscript `ˢ` marks the relations supplied by `𝒮`.

Why supply an equality relation instead of using Agda's path equality `x ≡ y`{.Agda}? The object-language equality sign needs an interpretation of its own. The field `x ≈ˢ y`{.Agda} can assign a truth value even when no path `x ≡ y`{.Agda} is given. At this stage the field is just a binary relation; we have not required the laws of equality or any compatibility with membership.
<!--zh-->
## 载体与关系

在[对象语言]{.term-ref #object-language}中，`t ≐ u`{.Agda} 与 `t ∈̇ u`{.Agda} 是[公式]{.term-ref #object-formula}，还不是可以证明的命题。要解释它们，就选定一个对象类型 `S`，并在上面给出两种关系。所得结构记作 `𝒮`，其**载体** `S` 的元素记作 `x`、`y`。上标 `ˢ` 表示关系由结构 `𝒮` 提供。

为什么相等关系也要单独给出，而不直接采用 Agda 的路径相等 `x ≡ y`{.Agda}？因为[对象语言]{.term-ref #object-language}中的相等记号需要自己的解释。即使没有给出路径 `x ≡ y`{.Agda}，字段 `x ≈ˢ y`{.Agda} 仍可赋予一个真值。此时它只是二元关系；我们尚未要求它满足相等关系的定律，也未要求它与隶属关系相容。
<!--ja-->
## 台と関係

[対象言語]{.term-ref #object-language}の `t ≐ u`{.Agda} と `t ∈̇ u`{.Agda} は[論理式]{.term-ref #object-formula}であり、まだ証明できる命題ではない。その意味を定めるには、対象の型 `S` と、その上の二つの関係を選ぶ。得られる構造を `𝒮`、その**台** `S` の元を `x`、`y` と書く。上付きの `ˢ` は、関係が構造 `𝒮` から与えられることを示す。

等号の関係まで別に与え、Agda のパス等式 `x ≡ y`{.Agda} をそのまま使わないのはなぜか。[対象言語]{.term-ref #object-language}の等号には独自の解釈が必要だからである。パス `x ≡ y`{.Agda} が与えられていなくても、フィールド `x ≈ˢ y`{.Agda} は真理値を与えられる。この段階では単なる二項関係であり、等号の法則も、所属との整合性もまだ要求しない。
<!--/-->

<!--en-->
**Definition** (`ZFStructure`{.Agda}) At level `ℓ`, a structure consists of a carrier `S : Type ℓ`{.Agda}, a proof that `S` is an h-set, and two relations of type `S → S → hProp ℓ`{.Agda} for equality and membership. The first two fields fix the range of objects and ensure that paths between them form propositions. Because a type at level `ℓ` and the type `hProp ℓ`{.Agda} both live one universe higher, the record itself lies in `Type (ℓ-suc ℓ)`{.Agda}.
<!--zh-->
**定义** (`ZFStructure`{.Agda}) 在层级 `ℓ`，一个结构由载体 `S : Type ℓ`{.Agda}、`S` 是 h-集合的证明，以及两个 `S → S → hProp ℓ`{.Agda} 型的关系组成，分别解释相等与隶属。前两个字段确定对象的范围，并保证对象之间的路径类型都是命题。层级 `ℓ` 上的类型与 `hProp ℓ`{.Agda} 的类型都位于高一层宇宙，因此整个 record 属于 `Type (ℓ-suc ℓ)`{.Agda}。
<!--ja-->
**定義** (`ZFStructure`{.Agda}) レベル `ℓ` の構造は、台 `S : Type ℓ`{.Agda}、`S` が h-集合である証明、および等号と所属を解釈する二つの `S → S → hProp ℓ`{.Agda} 型の関係からなる。最初の二つのフィールドが対象の範囲を定め、その間のパスの型が命題であることを保証する。レベル `ℓ` の型と `hProp ℓ`{.Agda} の型はともに一つ上の宇宙に属するため、レコード全体は `Type (ℓ-suc ℓ)`{.Agda} に属する。
<!--/-->

```agda
record ZFStructure (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    S         : Type ℓ
    isSetS    : isSet S
```

<!--en-->
The remaining fields give a proposition for each ordered pair of carrier elements. For instance, `x ∈ˢ y`{.Agda} is the structure's membership proposition, while `t ∈̇ u`{.Agda} from the previous chapter is still a piece of syntax. The record does not yet say how [terms]{.term-ref #object-term} denote elements, nor whether either relation obeys a set-theoretic axiom.
<!--zh-->
余下两个字段为每对载体元素给出一个命题。例如，`x ∈ˢ y`{.Agda} 是结构中的隶属命题，而上一章的 `t ∈̇ u`{.Agda} 仍只是一段语法。这个 record 尚未说明[词项]{.term-ref #object-term}怎样指代载体元素，也没有要求这两种关系满足集合论公理。
<!--ja-->
残る二つのフィールドは、台の元の組ごとに命題を与える。たとえば `x ∈ˢ y`{.Agda} は構造における所属の命題であるが、前章の `t ∈̇ u`{.Agda} はまだ構文にすぎない。このレコードは、[項]{.term-ref #object-term}が台の元をどう指すかも、二つの関係が集合論の公理を満たすかどうかも定めない。
<!--/-->

```agda
    _≈ˢ_ _∈ˢ_ : S → S → hProp ℓ

  infix 20 _≈ˢ_ _∈ˢ_
```

<!--en-->
The name `ZFStructure`{.Agda} identifies the language whose symbols are to be interpreted, not a model already satisfying ZF. One could, for example, use natural numbers as the carrier and interpret the membership field by their usual order. That supplies the required data, but certainly does not prove the ZF axioms. Additional laws come later.

## Reading membership as a type

The field `x ∈ˢ y`{.Agda} returns an `hProp`{.Agda}, a proposition together with its proof-irrelevance. To use a proof of that proposition as an argument, we pass to its underlying type `⟨ x ∈ˢ y ⟩`{.Agda}. The submodule `hPropStructure`{.Agda} keeps a structure `𝒮` fixed and gives this type the notation `x ∈ᵗ y`{.Agda}.
<!--zh-->
`ZFStructure`{.Agda} 这个名字指出它要解释的是集合论语言，并不表示它已经是 ZF 模型。例如，以自然数为载体，把通常的大小关系放进隶属字段，也能提供这里要求的数据，却当然不能据此证明 ZF 公理。进一步的定律要留待后文。

## 把隶属读作类型

字段 `x ∈ˢ y`{.Agda} 返回一个 `hProp`{.Agda}，其中包含命题及其证明无关性。若要把该命题的证明作为函数实参，就取出底层类型 `⟨ x ∈ˢ y ⟩`{.Agda}。子模块 `hPropStructure`{.Agda} 固定一个结构 `𝒮`，并把这个类型记作 `x ∈ᵗ y`{.Agda}。
<!--ja-->
`ZFStructure`{.Agda} という名前は解釈する記号が集合論の言語に属することを示すのであって、すでに ZF のモデルであるという意味ではない。たとえば自然数を台とし、通常の大小関係を所属のフィールドに入れても、ここで必要なデータはそろう。しかしそれだけで ZF の公理が証明されるわけではない。さらに必要な法則は後で加える。

## 所属を型として読む

フィールド `x ∈ˢ y`{.Agda} は `hProp`{.Agda}、すなわち命題とその証明無関係性を返す。その命題の証明を関数の引数として使うには、基礎となる型 `⟨ x ∈ˢ y ⟩`{.Agda} を取り出す。部分モジュール `hPropStructure`{.Agda} は構造 `𝒮` を固定し、この型を `x ∈ᵗ y`{.Agda} と書けるようにする。
<!--/-->

<!--en-->
Opening `ZFStructure 𝒮` inside the submodule makes its fields available as `S`, `∈ˢ`{.Agda}, and so on. The new notation will not change which memberships hold; it only exposes the type of their proofs.
<!--zh-->
在子模块内打开 `ZFStructure 𝒮`，便可直接使用它的字段 `S`、`∈ˢ`{.Agda} 等。新记号不改变哪些隶属关系成立，只是取出这些命题的证明类型。
<!--ja-->
部分モジュール内で `ZFStructure 𝒮` を開くと、`S` や `∈ˢ`{.Agda} などのフィールドをそのまま使える。新しい記法は、どの所属が成り立つかを変えず、命題の証明の型を取り出すだけである。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module hPropStructure {ℓ} (𝒮 : ZFStructure ℓ) where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
**Definition** (`_∈ᵗ_`{.Agda}) For carrier elements `x` and `y`, let `x ∈ᵗ y`{.Agda} be the underlying type of `x ∈ˢ y`{.Agda}.
<!--zh-->
**定义** (`_∈ᵗ_`{.Agda}) 对载体元素 `x`、`y`，定义 `x ∈ᵗ y`{.Agda} 为 `x ∈ˢ y`{.Agda} 的底层类型。
<!--ja-->
**定義** (`_∈ᵗ_`{.Agda}) 台の元 `x`、`y` に対し、`x ∈ᵗ y`{.Agda} を `x ∈ˢ y`{.Agda} の基礎型と定める。
<!--/-->

```agda
  open ZFStructure 𝒮 public

  _∈ᵗ_ : S → S → Type ℓ
  x ∈ᵗ y = ⟨ x ∈ˢ y ⟩
```

<!--en-->
An inhabitant of `y ∈ᵗ x`{.Agda} is therefore a proof that `y` belongs to `x` in this structure. The left argument is the member, just as for `∈ˢ`{.Agda}; we give the two notations the same binding strength.
<!--zh-->
因此，`y ∈ᵗ x`{.Agda} 的元素就是「`y` 在该结构中属于 `x`」的证明。与 `∈ˢ`{.Agda} 一样，左侧实参是成员；两个记号也采用相同的结合强度。
<!--ja-->
したがって `y ∈ᵗ x`{.Agda} の元は、この構造で `y` が `x` に属することの証明である。`∈ˢ`{.Agda} と同じく左側が所属する元であり、二つの記法の結び付きの強さも同じにする。
<!--/-->

```agda
  infix 20 _∈ᵗ_
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
这几个相近的隶属记号各有用途。尤其是，[类]{.term-ref #class}是谓词 `M : S → hProp ℓ`{.Agda}，所以 `x ∈ᶜ M`{.Agda} 问的是元素是否满足这个谓词，而不是比较两个载体元素。

| 记号 | 两侧的对象 | 得到的结果 |
| --- | --- | --- |
| `t ∈̇ u`{.Agda} | 两个[词项]{.term-ref #object-term} | 尚未赋予真值的[公式]{.term-ref #object-formula} |
| `x ∈ˢ y`{.Agda} | 两个载体元素 | `hProp ℓ`{.Agda} 中的命题 |
| `x ∈ᵗ y`{.Agda} | 同样的两个元素 | `x ∈ˢ y`{.Agda} 的底层证明类型 |
| `x ∈ᶜ M`{.Agda} | 一个元素与一个类 | `M x`{.Agda} 的底层证明类型 |
: 四种隶属记号各自的用途
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
## Transitive classes

Suppose a class `M` selects some elements of the carrier. If `x` is selected and `y` belongs to `x` according to the structure, must `y` also be selected? A **transitive class** is one for which the answer is yes. This is closure under *members*, not under subsets.
<!--zh-->
## 传递类

设类 `M` 选出了载体中的一部分元素。若 `x` 已被选中，而按结构的隶属关系 `y` 属于 `x`，那么 `y` 也会被选中吗？答案总为「是」时，`M` 就是**传递类**。这是对*成员*的闭合，不是对子集的闭合。
<!--ja-->
## 推移的クラス

クラス `M` が台の元をいくつか選ぶとする。選ばれた `x` に、構造の所属関係によって `y` が属するなら、`y` も選ばれるだろうか。常にそうなるクラスを**推移的クラス**という。これは*要素*についての閉性であり、部分集合についての閉性ではない。
<!--/-->

<!--en-->
**Definition** (`Transitive`{.Agda}) For a structure `𝒮` and a class `M`, transitivity assigns, to any carrier elements `x` and `y`, a proof of `y ∈ᶜ M`{.Agda} from proofs of `y ∈ᵗ x`{.Agda} and `x ∈ᶜ M`{.Agda}. The quantification over `x` and `y` is implicit in the code.
<!--zh-->
**定义** (`Transitive`{.Agda}) 对结构 `𝒮` 与类 `M`，传递性要求：任取载体元素 `x`、`y`，从 `y ∈ᵗ x`{.Agda} 和 `x ∈ᶜ M`{.Agda} 的证明得到 `y ∈ᶜ M`{.Agda} 的证明。代码中的 `x`、`y` 采用隐式量化。
<!--ja-->
**定義** (`Transitive`{.Agda}) 構造 `𝒮` とクラス `M` に対し、推移性とは、任意の台の元 `x`、`y` について、`y ∈ᵗ x`{.Agda} と `x ∈ᶜ M`{.Agda} の証明から `y ∈ᶜ M`{.Agda} の証明を与えることである。コードでは `x`、`y` を暗黙に量化する。
<!--/-->

```agda
Transitive : ∀ {ℓ} (𝒮 : ZFStructure ℓ)
           → (ZFStructure.S 𝒮 → hProp ℓ) → Type ℓ
Transitive 𝒮 M = ∀ {x y} → y ∈ᵗ x → x ∈ᶜ M → y ∈ᶜ M
  where open hPropStructure 𝒮
```

<!--en-->
This is a condition on a class, not an extra field of every structure. The restriction constructed next works for any class; transitivity becomes relevant when we need a member of a selected object to remain inside the selected range.
<!--zh-->
这是对类的额外条件，不是每个结构都必须具备的字段。下一节可以把结构限制到任意类；只有当我们需要保证「被选中对象的成员仍在选定范围内」时，才须假设传递性。
<!--ja-->
これはクラスに課す追加の条件であり、すべての構造に備わるフィールドではない。次節の制限は任意のクラスについて作れる。選ばれた対象の要素も選ばれた範囲に残す必要があるとき、初めて推移性を仮定する。
<!--/-->

<!--en-->
## Substructures

To make the variables range over only the elements selected by `M`, we need a new carrier. It is not enough to keep the old type `S` and merely remember `M` alongside it: a variable of type `S` could still denote an unselected element. Instead, each element of the new carrier includes both an `x : S`{.Agda} and evidence that `x ∈ᶜ M`{.Agda}. The notation `𝒮 ↾ M`{.Agda} means the structure `𝒮` restricted to this class.
<!--zh-->
## 子结构

若想让变元只在 `M` 选中的元素中取值，就需要换一个载体。仅保留原类型 `S`，再把 `M` 放在旁边，还不够：`S` 型的变元仍能指向未被选中的元素。因此，新载体的每个元素既包含 `x : S`{.Agda}，也包含 `x ∈ᶜ M`{.Agda} 的证据。`𝒮 ↾ M`{.Agda} 表示把结构 `𝒮` 限制到这个类上。
<!--ja-->
## 部分構造

変数が `M` に選ばれた元だけを動くようにするには、台を作り直す必要がある。元の型 `S` を残して横に `M` を添えるだけでは、`S` 型の変数は選ばれなかった元も指せてしまう。そこで新しい台の各元を、`x : S`{.Agda} と `x ∈ᶜ M`{.Agda} の証拠の組にする。`𝒮 ↾ M`{.Agda} は、構造 `𝒮` をこのクラスへ制限したものを表す。
<!--/-->

<!--en-->
**Definition** (`_↾_`{.Agda}) For any class `M : S → hProp ℓ`{.Agda}, the restricted structure has carrier `Σ[ x ∶ S ] (x ∈ᶜ M)`{.Agda}. This is a type of dependent pairs, not a set within the structure representing the class. The previously introduced `isSetClass`{.Agda} supplies its h-set proof from `isSetS`{.Agda} and the propositionhood of each membership type.
<!--zh-->
**定义** (`_↾_`{.Agda}) 对任意类 `M : S → hProp ℓ`{.Agda}，限制结构的载体是 `Σ[ x ∶ S ] (x ∈ᶜ M)`{.Agda}。这是依值对的类型，不是结构内部表示该类的某个集合。前文引入的 `isSetClass`{.Agda} 利用 `isSetS`{.Agda} 及逐点的成员类型为命题这一事实，给出新载体的 h-集合性证明。
<!--ja-->
**定義** (`_↾_`{.Agda}) 任意のクラス `M : S → hProp ℓ`{.Agda} に対し、制限された構造の台を `Σ[ x ∶ S ] (x ∈ᶜ M)`{.Agda} とする。これは依存対の型であり、構造の内部でそのクラスを表す集合ではない。先に導入した `isSetClass`{.Agda} を `isSetS`{.Agda} と各点で所属の型が命題であることに適用し、新しい台の h-集合性を得る。
<!--/-->

```agda
_↾_ : ∀ {ℓ} (𝒮 : ZFStructure ℓ)
    → (ZFStructure.S 𝒮 → hProp ℓ) → ZFStructure ℓ
_↾_ {ℓ} 𝒮 M = record
  { S      = Σ[ x ∶ S ] (x ∈ᶜ M)
  ; isSetS = isSetClass isSetS (λ x → ⟨ M x ⟩isProp)
```

<!--en-->
How should the two relations act on these pairs? For restricted elements `a` and `b`, apply the old relations to their first projections: `fst a ≈ˢ fst b`{.Agda} and `fst a ∈ˢ fst b`{.Agda}. The proofs stored in the second components certify that the elements lie in `M`; they do not alter the truth values of equality or membership. Thus the relation fields are pulled back from `𝒮` along `fst`{.Agda}.
<!--zh-->
新载体上的两个关系该怎样定义？对限制元素 `a`、`b`，在各自的第一投影上应用原关系，得到 `fst a ≈ˢ fst b`{.Agda} 与 `fst a ∈ˢ fst b`{.Agda}。第二分量的证明只保证这两个元素属于 `M`，不改变相等或隶属的真值。这样，两个关系字段就沿 `fst`{.Agda} 从 `𝒮` 拉回。
<!--ja-->
新しい台の上で二つの関係をどう定めるか。制限された元 `a`、`b` の第一射影に元の関係を適用し、`fst a ≈ˢ fst b`{.Agda} と `fst a ∈ˢ fst b`{.Agda} を得る。第二成分の証拠は元が `M` に属することを保証するだけで、等号や所属の真理値を変えない。つまり二つの関係を `fst`{.Agda} に沿って `𝒮` から引き戻す。
<!--/-->

```agda
  ; _≈ˢ_   = λ a b → fst a ≈ˢ fst b
  ; _∈ˢ_   = λ a b → fst a ∈ˢ fst b }
  where open ZFStructure 𝒮

infixl 21 _↾_
```

<!--en-->
The relations ignore the certificates, but what about equality of the pairs themselves? A certificate cannot distinguish two pairs with the same first component: after transporting one certificate along a path between the first components, both certificates inhabit the same proposition and hence agree. This concerns Agda's path equality of pairs, not the freely chosen structure relation `≈ˢ`{.Agda}.
<!--zh-->
两个关系都不看证据，但这些对本身的相等又如何？证据不会把第一分量相同的对区分开：沿第一分量之间的路径传输一份证据后，两份证据就处于同一个命题中，因而相等。这里讨论的是 Agda 中对的路径相等，不是任意指定的结构关系 `≈ˢ`{.Agda}。
<!--ja-->
二つの関係は証拠を見ないが、対そのものの等しさはどうなるか。証拠によって第一成分が等しい対を区別することはできない。第一成分の間のパスに沿って一方の証拠を移せば、二つの証拠は同じ命題に属し、したがって等しい。ここで扱うのは Agda における対のパス等式であり、自由に与えた構造の関係 `≈ˢ`{.Agda} ではない。
<!--/-->

<!--en-->
**Lemma** (`↾-reflects`{.Agda}) For `a` and `b` in the restricted carrier, a path `fst a ≡ fst b`{.Agda} determines a path `a ≡ b`{.Agda}.
<!--zh-->
**引理** (`↾-reflects`{.Agda}) 对限制载体中的 `a`、`b`，路径 `fst a ≡ fst b`{.Agda} 决定路径 `a ≡ b`{.Agda}。
<!--ja-->
**補題** (`↾-reflects`{.Agda}) 制限された台の `a`、`b` について、パス `fst a ≡ fst b`{.Agda} からパス `a ≡ b`{.Agda} が定まる。
<!--/-->

```agda
↾-reflects : ∀ {ℓ} {𝒮 : ZFStructure ℓ} {M : ZFStructure.S 𝒮 → hProp ℓ}
             {a b : ZFStructure.S (𝒮 ↾ M)}
           → fst a ≡ fst b → a ≡ b
↾-reflects {M = M} = Σ≡Prop (λ x → ⟨ M x ⟩isProp)
```

<!--en-->
The library lemma `Σ≡Prop`{.Agda} performs precisely this step, using `⟨ M x ⟩isProp`{.Agda} for each fibre of certificates. The converse needs no special lemma: a path `a ≡ b`{.Agda} always gives `fst a ≡ fst b`{.Agda} by applying `fst`{.Agda}. Only the less immediate direction is named here.
<!--zh-->
库引理 `Σ≡Prop`{.Agda} 正是利用每处的 `⟨ M x ⟩isProp`{.Agda} 完成这一步。反向不需另设引理：对路径 `a ≡ b`{.Agda} 应用 `fst`{.Agda}，自然得到 `fst a ≡ fst b`{.Agda}。这里命名的只是较不显然的方向。
<!--ja-->
ライブラリの補題 `Σ≡Prop`{.Agda} は、各点の `⟨ M x ⟩isProp`{.Agda} を使って、まさにこの操作を行う。逆向きに特別な補題は要らない。パス `a ≡ b`{.Agda} に `fst`{.Agda} を作用させれば `fst a ≡ fst b`{.Agda} が得られる。ここでは自明でない向きだけに名前を付ける。
<!--/-->

<!--en-->
## Recap

The syntax of the preceding chapter now has a possible place to be read: a carrier and two proposition-valued relations. Restricting that carrier to a class changes the range of future [quantifiers]{.term-ref #object-quantifier} while inheriting both relations; it requires no transitivity assumption. In the next chapter we will finally assign meanings to [terms]{.term-ref #object-term} and [formulas]{.term-ref #object-formula} in a chosen structure.
<!--zh-->
## 小结

上一章的语法现在有了可以接受解释的场所：一个载体和两种命题值关系。把载体限制到一个类，会改变后续[量词]{.term-ref #object-quantifier}的取值范围，同时继承原来的关系；这个构造不要求类具有传递性。下一章才会在选定的结构中，真正解释[词项]{.term-ref #object-term}与[公式]{.term-ref #object-formula}。
<!--ja-->
## まとめ

前章の構文を読み取るための場が、台と二つの命題値の関係によって用意された。台をクラスに制限すると、後で[量化子]{.term-ref #object-quantifier}が動く範囲は変わるが、二つの関係は元のまま受け継ぐ。この構成に推移性は要らない。次章では、選んだ構造の中で[項]{.term-ref #object-term}と[論理式]{.term-ref #object-formula}に実際の意味を与える。
<!--/-->

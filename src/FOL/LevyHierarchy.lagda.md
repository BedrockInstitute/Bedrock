<!--en-->
# The Lévy hierarchy

A first-order formula can quantify in two ways: boundedly, as in "for all $x$ in $t$", or unboundedly, over the whole universe. The Lévy hierarchy measures a formula's syntactic complexity by its unbounded quantifiers: **Δ₀** formulas use only bounded quantifiers, Σ₁ formulas prefix a block of unbounded existentials to a Δ₀ core, and Π₁ formulas prefix a block of unbounded universals. Membership in these classes matters because later chapters prove Δ₀-absoluteness and run definability arguments over the constructible universe by structural induction on quantifier shape. Rather than inspect formulas over and over, this chapter turns the classification itself into data: a **witness** is an inductive datum indexed by a formula, available for any constant domain `K`, so a formula can carry proof of its own complexity class alongside its syntax. The chapter builds the Δ₀ witness, a Boolean checker that recognizes bounded formulas, and the extension to every finite level Σₙ/Πₙ.
<!--zh-->
# Lévy 层级

一阶公式有两种量化方式：有界的，如「对所有 $x$ 属于 $t$」；以及在整个宇宙上取量的无界量化。Lévy 层级按无界量词衡量公式的语法复杂度：**Δ₀** 公式只用有界量词，Σ₁ 公式在 Δ₀ 核心之前加一段无界存在量词，Π₁ 公式则加一段无界全称量词。这些类的归属之所以重要，是因为后面的章节要证明 Δ₀ 绝对性，并在可构造宇宙上按量词形状做结构归纳的可定义性论证。与其反复去检查公式，本章干脆把分类本身做成数据：**见证**是以公式为下标的归纳数据，对任意常元域 `K` 都可用，于是一个公式可以在语法之外同时携带其复杂度类的证明。本章构造 Δ₀ 见证、一个识别有界公式的布尔检查器，以及推广到每个有限层级 Σₙ/Πₙ 的分类。
<!--ja-->
# Lévy 階層

一階論理式には二つの量化の仕方があります。「$t$ に属するすべての $x$ について」という有界な量化と、宇宙全体にわたる非有界な量化です。Lévy 階層は、論理式の構文的な複雑さを非有界量化子で測ります。**Δ₀** 論理式は有界量化子しか使わず、Σ₁ 論理式は Δ₀ の核の前に非有界な存在量化子の列を、Π₁ 論理式は非有界な全称量化子の列を前置します。これらのクラスへの所属が重要なのは、後の章で Δ₀ 絶対性を証明し、構成可能宇宙上で量化子の形に関する構造的帰納による定義可能性の議論を進めるからです。論理式をそのたびに調べる代わりに、本章では分類そのものをデータにします。**証拠**とは論理式で添字付けられた帰納的なデータであり、任意の定数域 `K` に対して使えるので、論理式は自分の構文とともに複雑さのクラスの証明を帯同できます。本章は Δ₀ の証拠、有界論理式を認識するブール判定器、そしてすべての有限レベル Σₙ/Πₙ への拡張を構成します。
<!--/-->

<!--en-->
The chapter relies on one bridge between computation and proof. The type `Bool` has the two values `true` and `false`, and `_and_` conjoins two Boolean results. The operation `Bool→Type` sends a Boolean to a type: `true` goes to a one-point type and `false` to the empty type. Hence an element of `Bool→Type b` exists exactly when `b` is `true`. This is what lets a computed answer later serve as a proof obligation: a program can first decide a Boolean question about syntax, and the assertion that the answer came out `true` is itself a type one can inhabit.
<!--zh-->
本章依赖一条从计算到证明的桥梁。类型 `Bool` 有 `true` 与 `false` 两个值，`_and_` 合取两个布尔结果。运算 `Bool→Type` 把布尔值送到一个类型：`true` 对应单点类型，`false` 对应空类型。于是 `Bool→Type b` 有元素当且仅当 `b` 为 `true`。这正是让计算结果日后能兼作证明义务的机制：程序可以先对语法作出布尔判定，而「答案为 `true`」这个断言本身就是一个可以有元素的类型。
<!--ja-->
本章は計算から証明への一本の橋に依拠します。型 `Bool` は `true` と `false` の二つの値を持ち、`_and_` は二つのブール値の結果を連言します。演算 `Bool→Type` はブール値を型へ送ります。`true` は一点型に、`false` は空な型に対応します。したがって `Bool→Type b` に元が存在するのは `b` が `true` のときちょうどです。この仕組みにより、計算の結果が後で証明義務を兼ねられます。プログラムはまず構文についてのブール的な問いを判定し、「答えが `true` になった」という主張はそれ自体が元を持てる型になるのです。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.LevyHierarchy where

open import Base.Prelude
open import Base.Truth
open import Cubical.Data.Bool using ( Bool; true; false; _and_; Bool→Type )
```

<!--en-->
The formulas being classified come from the object language of `FOL.Syntax`: terms, the atomic relations `_∈̇_` and `_≐_`, the connectives, and two distinct pairs of quantifier forms. The bounded quantifiers `∀̇∈` and `∃̇∈` name their bound as a term of the language, while `∀̇_` and `∃̇_` quantify without one. Keeping the two kinds syntactically separate is what makes the whole classification possible: every family defined below is indexed by a `Formula K n`, so the Lévy hierarchy here is a predicate on syntax itself, never on semantic values.
<!--zh-->
被分类的公式来自 `FOL.Syntax` 的对象语言：词项、原子关系 `_∈̇_` 与 `_≐_`、联结词，以及两对不同的量词形式。有界量词 `∀̇∈` 与 `∃̇∈` 把界限写成语言中的词项，而 `∀̇_` 与 `∃̇_` 则不带界限地量化。两种量词在语法上分离，正是整个分类得以进行的前提：下面定义的每个族都以 `Formula K n` 为下标，所以这里的Lévy 层级是语法本身的谓词，而不是语义值的谓词。
<!--ja-->
分類の対象となる論理式は、`FOL.Syntax` の対象言語に由来します。項、原子関係 `_∈̇_` と `_≐_`、結合子、そして二組の異なる量化子の形式です。有界量化子 `∀̇∈` と `∃̇∈` は界限を言語内の項として名指ししますが、`∀̇_` と `∃̇_` は界限なしに量化します。二種の量化子が構文上区別されていることこそ、この分類全体を可能にする前提です。以下で定義される各族はいずれも `Formula K n` で添字付けられるため、ここでのLévy 階層は意味論的な値ではなく構文そのもの上の述語です。
<!--/-->

```agda
open import Cubical.Data.Unit using ( tt )
open import FOL.Syntax using
  ( Term; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
```

<!--en-->
## The Δ₀ witness

`Δ₀` is an inductive family indexed by formulas: an inhabitant of `Δ₀ φ` is a witness, as explicit data, that every quantifier occurring in `φ` is bounded. The definition admits one constructor for each permitted formula shape and none for `∃̇` or `∀̇`; this absence is the classification. The family is parameterized by the constant domain `K` at some universe level `ℓc` but otherwise only by syntax, so the same witness type is available over any domain.
<!--zh-->
## Δ₀ 见证

`Δ₀` 是以公式为下标的归纳族：`Δ₀ φ` 的一个元素就是一份显式数据的见证，证明 `φ` 中出现的每个量词都有界。定义对每个获准的公式形状给一个构造子，而不给 `∃̇` 与 `∀̇` 任何构造子；**缺席即分类**。该族除在某个宇宙层级 `ℓc` 上以常元域 `K` 为参数外，只由语法决定，所以同一见证类型对任意常元域都可用。
<!--ja-->
## Δ₀ の証拠

`Δ₀` は論理式で添字付けられた帰納的族です。`Δ₀ φ` の元は、`φ` に現れる量化子がすべて有界であることの、明示的なデータとしての証拠です。定義は許容される論理式の形ごとに一つの構成子を持ち、非有界な `∃̇` と `∀̇` には構成子を与えません。この不在こそが分類です。この族は、ある宇宙レベル `ℓc` の定数域 `K` をパラメータとするほかは構文だけで決まるため、同じ証拠の型が任意の定数域で使えます。
<!--/-->

<!--en-->
The guiding invariant of the Δ₀ family is: bounded quantifiers preserve boundedness, and unbounded quantifiers break it. The declaration realizes this as an inductive family `Δ₀` indexed by formulas of every arity `n`, living at the same universe level as `K`, so a witness is small data. An atomic formula such as `t ∈̇ u` is accepted outright: it contains no quantifier at all, so `δ-∈` (and its equality companion `δ-≐`) takes no argument. The class is then closed under the binary connectives, with `δ-∧` and `δ-∨` each demanding a witness for both components of the compound.
<!--zh-->
Δ₀ 族的指引性不变量是：有界量词保持有界性，无界量词破坏它。声明把它实现为以每个元数 `n` 的公式为下标的归纳族 `Δ₀`，与 `K` 同处一个宇宙层级，故见证是小数据。像 `t ∈̇ u` 这样的原子公式被直接接受：它根本不含量词，所以 `δ-∈` (以及等式的同伴 `δ-≐`) 不带参数。该类随后对二元联结词封闭，`δ-∧` 与 `δ-∨` 各自要求复合公式两个成分都有见证。
<!--ja-->
Δ₀ の族を導く不変量は次のとおりです。有界量化子は有界性を保ち、非有界量化子はこれを壊す。宣言はこれを、任意のアリティ `n` の論理式で添字付けられた帰納的族 `Δ₀` として実現します。`K` と同じ宇宙レベルに住むので、証拠は小さなデータです。`t ∈̇ u` のような原子論理式はそのまま受け入れられます。量化子をまったく含まないため、`δ-∈` (および等式版の `δ-≐`) は引数を取りません。次にこのクラスは二項結合子の下で閉じ、`δ-∧` と `δ-∨` はそれぞれ複合論理式の両成分に対する証拠を要求します。
<!--/-->

```agda
data Δ₀ {ℓc} {K : Type ℓc} : ∀ {n} → Formula K n → Type ℓc where
  δ-∈  : ∀ {n} {t u : Term K n} → Δ₀ (t ∈̇ u)
  δ-≐  : ∀ {n} {t u : Term K n} → Δ₀ (t ≐ u)
  δ-∧  : ∀ {n} {φ ψ : Formula K n} → Δ₀ φ → Δ₀ ψ → Δ₀ (φ ∧̇ ψ)
  δ-∨  : ∀ {n} {φ ψ : Formula K n} → Δ₀ φ → Δ₀ ψ → Δ₀ (φ ∨̇ ψ)
```

<!--en-->
Implication `δ-⇒` and falsity `δ-⊥`, which carries no quantifier, complete the quantifier-free shapes. The decisive rows are the bounded quantifiers: `δ-∀∈` and `δ-∃∈` take a witness for a body `φ` of arity `suc n` and return one for `∀̇∈ t φ` or `∃̇∈ t φ`, where the bound is the term `t`. Boundedness thus travels through a bounded quantifier unchanged. Equally decisive is what the list omits: no constructor mentions the unbounded `∃̇` or `∀̇`. A formula with an unbounded quantifier, such as `∃̇ (x₀ ∈̇ x₁)`, falls under no constructor, so no inhabitant of `Δ₀` at that index can ever be assembled. This refusal is the classification, not a theorem about it.
<!--zh-->
蕴涵 `δ-⇒` 与不带量词的伪式 `δ-⊥` 补齐了无量词的形状。决定性的行是有界量词：`δ-∀∈` 与 `δ-∃∈` 取元数 `suc n` 的体 `φ` 的见证，返回 `∀̇∈ t φ` 或 `∃̇∈ t φ` 的见证，其界限是词项 `t`。于是有界性原封不动地穿过有界量词。同样决定性的是清单所省略者：没有任何构造子提到无界的 `∃̇` 或 `∀̇`。像 `∃̇ (x₀ ∈̇ x₁)` 这样含无界量词的公式不落入任何构造子，所以在该下标处根本拼不出 `Δ₀` 的元素。这种拒绝本身就是分类，而不是关于分类的定理。
<!--ja-->
含意 `δ-⇒` と、量化子を持たない偽 `δ-⊥` が、量化子を含まない形を完成させます。決定的な行は有界量化子です。`δ-∀∈` と `δ-∃∈` はアリティ `suc n` の本体 `φ` に対する証拠を受け取り、`∀̇∈ t φ` あるいは `∃̇∈ t φ` の証拠を返します。界限は項 `t` です。こうして有界性は有界量化子をそのまま通過します。同じくらい決定的なのは、この一覧に欠けているものです。非有界な `∃̇` や `∀̇` に触れる構成子は一つもありません。`∃̇ (x₀ ∈̇ x₁)` のように非有界量化子を含む論理式はどの構成子にも当てはまらず、その添字での `Δ₀` の元は決して組み立てられません。この拒否こそが分類であり、分類についての定理ではありません。
<!--/-->

```agda
  δ-⇒  : ∀ {n} {φ ψ : Formula K n} → Δ₀ φ → Δ₀ ψ → Δ₀ (φ ⇒̇ ψ)
  δ-⊥  : ∀ {n} → Δ₀ {n = n} ⊥̇
  δ-∀∈ : ∀ {n} {t : Term K n} {φ : Formula K (suc n)} → Δ₀ φ → Δ₀ (∀̇∈ t φ)
  δ-∃∈ : ∀ {n} {t : Term K n} {φ : Formula K (suc n)} → Δ₀ φ → Δ₀ (∃̇∈ t φ)

δ-¬ : ∀ {ℓc} {K : Type ℓc} {n} {φ : Formula K n} → Δ₀ φ → Δ₀ (¬̇ φ)
```

<!--en-->
Negation and truth need no special treatment because they are not primitive: in this syntax `¬̇ φ` is defined as `φ ⇒̇ ⊥̇` and `⊤̇` as `⊥̇ ⇒̇ ⊥̇`. Since implication and falsity already carry witnesses, boundedness of the defined formulas follows by the `δ-⇒` constructor. The derived witness `δ-¬ d` packages the witness `d` with `δ-⊥`, and `δ-⊤` places `δ-⊥` on both sides of an implication. These are lemmas about the existing family, not new constructors, and they let later code certify negated and trivial formulas without new case analysis.
<!--zh-->
否定与真无需特殊处理，因为它们不是原始的：在这套语法中，`¬̇ φ` 定义为 `φ ⇒̇ ⊥̇`，`⊤̇` 定义为 `⊥̇ ⇒̇ ⊥̇`。既然蕴涵与伪式已有见证，被定义公式的有界性便由 `δ-⇒` 构造子推出。派生见证 `δ-¬ d` 把见证 `d` 与 `δ-⊥` 打包，`δ-⊤` 则把 `δ-⊥` 放在蕴涵两端。它们是关于既有族的引理而非新构造子，使后面的代码无需新的分情形即可证明否定式与平凡式。
<!--ja-->
否定と真理に特別な扱いは要りません。それらは原始的ではないからです。この構文では `¬̇ φ` は `φ ⇒̇ ⊥̇` として、`⊤̇` は `⊥̇ ⇒̇ ⊥̇` として定義されています。含意と偽がすでに証拠を持つため、定義された論理式の有界性は `δ-⇒` 構成子から従います。派生証拠 `δ-¬ d` は証拠 `d` を `δ-⊥` とまとめ、`δ-⊤` は含意の両辺に `δ-⊥` を置きます。これらは既存の族についての補題であって新しい構成子ではなく、後のコードが新たな場合分けなしに否定された論理式や自明な論理式を証明できるようにします。
<!--/-->

```agda
δ-¬ d = δ-⇒ d δ-⊥

δ-⊤ : ∀ {ℓc} {K : Type ℓc} {n} → Δ₀ {K = K} {n = n} ⊤̇
δ-⊤ = δ-⇒ δ-⊥ δ-⊥
```

<!--en-->
## Checking concrete formulas

Reading a formula against the constructor list by hand is unnecessary: the function `bounded` traverses the syntax and returns `true` exactly when no unbounded quantifier is met, and `checkΔ₀` converts the assertion that this Boolean came out `true` into an actual `Δ₀` witness. The proved direction is one-way: Boolean success yields a witness. The definition is not claimed to be a decision procedure in the opposite direction, and no completeness result is proved here.
<!--zh-->
## 检查具体公式

逐条对照构造子清单去读一个公式并无必要：函数 `bounded` 遍历语法，恰在未遇到无界量词时返回 `true`；`checkΔ₀` 再把「这个布尔值为 `true`」这一断言转成真正的 `Δ₀` 见证。已证明的方向是单向的：布尔成功给出见证。这里并未声称该定义是反方向的判定过程，也没有证明任何完备性结果。
<!--ja-->
## 具体的な論理式を判定する

論理式を一つずつ構成子のリストと突き合わせて読む必要はありません。関数 `bounded` は構文を走査し、非有界な量化子に出会わないときにちょうど `true` を返し、`checkΔ₀` はこのブール値が `true` になったという主張を実際の `Δ₀` の証拠へ変換します。証明された方向は一方向です。ブール値の成功が証拠を与えます。この定義が逆方向の判定手続きであるとは主張せず、完全性の結果もここでは証明しません。
<!--/-->

<!--en-->
Building Δ₀ witnesses by hand is unnecessary once the invariant can be checked mechanically. The function `bounded` walks through a formula and reports a `Bool`: atomic formulas and falsity report `true` outright, while each binary connective conjoins the results of its two subformulas with `_and_`. At this stage the check simply mirrors the shapes that Δ₀ accepts, one recursion per formula constructor.
<!--zh-->
一旦不变量可以机械地检查，手工构造 Δ₀ 见证就不必要了。函数 `bounded` 遍历公式并报告一个 `Bool`：原子公式与伪式直接报告 `true`，每个二元联结词则用 `_and_` 合取两个子公式的结果。此阶段的检查只是逐个公式构造子地镜像 Δ₀ 所接受的形状。
<!--ja-->
不変量が機械的に検査できるなら、Δ₀ の証拠を手で組み立てる必要はありません。関数 `bounded` は論理式をたどって `Bool` を報告します。原子論理式と偽はそのまま `true` を返し、各二項結合子は `_and_` で二つの部分論理式の結果を連言します。この段階の検査は、Δ₀ が受け入れる形を論理式の構成子ごとに一つの再帰で写しているにすぎません。
<!--/-->

```agda
bounded : ∀ {ℓc} {K : Type ℓc} {n} → Formula K n → Bool
bounded (t ∈̇ u) = true
bounded (t ≐ u) = true
bounded (φ ∧̇ ψ) = bounded φ and bounded ψ
bounded (φ ∨̇ ψ) = bounded φ and bounded ψ
```

<!--en-->
Here the invariant does real work. Both unbounded quantifiers return `false`, so a single unbounded occurrence anywhere in a formula spoils the whole check, whatever its subformulas look like. The bounded quantifiers behave oppositely: the recursion just continues into the body, because the bound `t` is a term of the syntax and cannot conceal a quantifier. The rule `bounded (∀̇∈ t φ) = bounded φ` is the computational counterpart of the Δ₀ constructor that let boundedness pass through.
<!--zh-->
不变量在这里真正发挥作用。两个无界量词都返回 `false`，所以公式中任何一处出现无界量词，无论子公式如何，整个检查即告失败。有界量词则相反：递归直接进入体公式，因为界限 `t` 是语法中的词项，藏不住量词。规则 `bounded (∀̇∈ t φ) = bounded φ` 正是那条允许有界性穿过的 Δ₀ 构造子的计算对应物。
<!--ja-->
ここで不変量が本領を発揮します。二つの非有界量化子はどちらも `false` を返すため、論理式のどこかに非有界量化子が一度現れれば、部分論理式がどうであれ検査全体が失敗します。有界量化子は逆で、再帰はそのまま本体へ進みます。界限 `t` は構文の項であり、量化子を隠せないからです。規則 `bounded (∀̇∈ t φ) = bounded φ` は、有界性を通過させた Δ₀ の構成子の計算上の対応物です。
<!--/-->

```agda
bounded (φ ⇒̇ ψ) = bounded φ and bounded ψ
bounded ⊥̇ = true
bounded (∃̇ φ) = false
bounded (∀̇ φ) = false
bounded (∀̇∈ t φ) = bounded φ
```

<!--en-->
A Boolean `true` at a conjunction means two things at once, and the private helper `and-out` takes it apart. Given `a b : Bool` and an inhabitant of `Bool→Type (a and b)`, it returns a pair of inhabitants, one for `Bool→Type a` and one for `Bool→Type b`. When `a` is `false`, the input would have to inhabit `Bool→Type false`, an empty type, so the case is discharged by the absurd pattern `()`. When `a` is `true`, the unit element `tt` proves the first conjunct and the given `h` already is the second.
<!--zh-->
合取处的布尔值 `true` 意味着两件事，私有辅助函数 `and-out` 把它拆开。给定 `a b : Bool` 与 `Bool→Type (a and b)` 的一个元素，它返回一对元素，分别属于 `Bool→Type a` 与 `Bool→Type b`。当 `a` 为 `false` 时，输入将不得不落入空类型 `Bool→Type false`，所以该情形由荒谬模式 `()` 直接打发。当 `a` 为 `true` 时，单位元 `tt` 证明第一个合取支，而给定的 `h` 本身就是第二个。
<!--ja-->
連言におけるブール値 `true` は一度に二つのことを意味するので、プライベートな補助関数 `and-out` がそれを分解します。`a b : Bool` と `Bool→Type (a and b)` の元が与えられると、`Bool→Type a` と `Bool→Type b` それぞれの元の組を返します。`a` が `false` のとき、入力は空な型 `Bool→Type false` に属さねばならず、この場合は荒謬パターン `()` で片付きます。`a` が `true` のときは、単位元 `tt` が第一の連言肢を証明し、与えられた `h` がそのまま第二の連言肢になります。
<!--/-->

```agda
bounded (∃̇∈ t φ) = bounded φ

private
  and-out : (a b : Bool) → Bool→Type (a and b) → Bool→Type a × Bool→Type b
  and-out false b ()
  and-out true b h = tt , h
```

<!--en-->
The function `checkΔ₀` is where the Boolean decision becomes evidence. It takes a formula `φ` and an inhabitant of `Bool→Type (bounded φ)`, which can exist only if the traversal computed `true`, and produces an actual `Δ₀ φ` witness. The atomic cases return the corresponding constructors directly, with the hypothesis `h` unused. For a conjunction, `bounded (φ ∧̇ ψ)` computes to `bounded φ and bounded ψ`, so `and-out` splits `h` into the two per-conjunct proofs `p .fst` and `p .snd`, and the recursive calls supply the sub-witnesses that `δ-∧` reassembles.
<!--zh-->
函数 `checkΔ₀` 正是布尔判定变成证据之处。它取公式 `φ` 与 `Bool→Type (bounded φ)` 的一个元素，后者只有在遍历算出 `true` 时才可能存在，并产出真正的 `Δ₀ φ` 见证。原子情形直接返回相应构造子，前提 `h` 用不上。合取情形中，`bounded (φ ∧̇ ψ)` 计算为 `bounded φ and bounded ψ`，于是 `and-out` 把 `h` 拆成两个逐支证明 `p .fst` 与 `p .snd`，递归调用给出子见证，再由 `δ-∧` 重组。
<!--ja-->
ブール的な判定が証拠に変わるのが関数 `checkΔ₀` です。この関数は論理式 `φ` と `Bool→Type (bounded φ)` の元を受け取ります。後者が存在するのは走査が `true` と計算したときに限られ、関数は実際の `Δ₀ φ` の証拠を返します。原子論理式の場合は対応する構成子を直接返し、仮定 `h` は使われません。連言の場合、`bounded (φ ∧̇ ψ)` は `bounded φ and bounded ψ` と計算されるので、`and-out` が `h` を連言肢ごとの二つの証明 `p .fst` と `p .snd` に分解し、再帰呼び出しが下位の証拠を供給して `δ-∧` が組み立て直します。
<!--/-->

```agda

checkΔ₀ : ∀ {ℓc} {K : Type ℓc} {n} (φ : Formula K n) → Bool→Type (bounded φ) → Δ₀ φ
checkΔ₀ (t ∈̇ u) h = δ-∈
checkΔ₀ (t ≐ u) h = δ-≐
checkΔ₀ (φ ∧̇ ψ) h = δ-∧ (checkΔ₀ φ (p .fst)) (checkΔ₀ ψ (p .snd))
  where p = and-out (bounded φ) (bounded ψ) h
```

<!--en-->
Disjunction and implication repeat the same move: each splits `h` with `and-out`, runs the two recursive calls, and recombines with `δ-∨` or `δ-⇒`. Falsity needs only `δ-⊥`. With these clauses, every quantifier-free shape that Δ₀ accepts has a route from the Boolean result to a witness.
<!--zh-->
析取与蕴涵重复同一动作：各自用 `and-out` 拆开 `h`，运行两次递归调用，再以 `δ-∨` 或 `δ-⇒` 重组。伪式只需 `δ-⊥`。有了这些子句，Δ₀ 接受的每个无量词形状都有了从布尔结果到见证的路径。
<!--ja-->
選言と含意は同じ動きを繰り返します。それぞれ `and-out` で `h` を分解し、二つの再帰呼び出しを実行して、`δ-∨` か `δ-⇒` で組み立て直します。偽は `δ-⊥` だけで足ります。これらの節により、Δ₀ が受け入れる量子化を含まないすべての形について、ブール値の結果から証拠への道が用意されました。
<!--/-->

```agda
checkΔ₀ (φ ∨̇ ψ) h = δ-∨ (checkΔ₀ φ (p .fst)) (checkΔ₀ ψ (p .snd))
  where p = and-out (bounded φ) (bounded ψ) h
checkΔ₀ (φ ⇒̇ ψ) h = δ-⇒ (checkΔ₀ φ (p .fst)) (checkΔ₀ ψ (p .snd))
  where p = and-out (bounded φ) (bounded ψ) h
checkΔ₀ ⊥̇ h = δ-⊥
```

<!--en-->
The remaining clauses close the argument. For the unbounded quantifiers, `bounded (∃̇ φ)` and `bounded (∀̇ φ)` both compute to `false`, so the hypothesis `h` would have to inhabit `Bool→Type false`, an empty type; the absurd pattern `()` accepts the case precisely because no such inhabitant exists. For the bounded quantifiers, `bounded (∀̇∈ t φ)` computes to `bounded φ`, so `h` passes unchanged to the body and the recursive result is wrapped with `δ-∀∈` or `δ-∃∈`. In total the clauses establish `bounded φ ≡ true → Δ₀ φ` for every formula: computational success yields evidence. The terms `t` and `u` never influence the outcome, and the converse direction is not claimed anywhere here.
<!--zh-->
余下的子句收束论证。对无界量词，`bounded (∃̇ φ)` 与 `bounded (∀̇ φ)` 都计算为 `false`，于是前提 `h` 将不得不落入空类型 `Bool→Type false`；荒谬模式 `()` 之所以能接受该情形，正因为这样的元素不存在。对有界量词，`bounded (∀̇∈ t φ)` 计算为 `bounded φ`，于是 `h` 原样传给体公式，递归结果用 `δ-∀∈` 或 `δ-∃∈` 包住。合起来，这些子句对每个公式确立 `bounded φ ≡ true → Δ₀ φ`：计算上的成功给出证据。词项 `t` 与 `u` 从不影响结果，而相反方向在这里任何地方都未被声称。
<!--ja-->
残りの節が議論を閉じます。非有界量化子については、`bounded (∃̇ φ)` と `bounded (∀̇ φ)` はどちらも `false` と計算されるため、仮定 `h` は空な型 `Bool→Type false` に属さねばなりません。そのような元は存在しないからこそ、荒謬パターン `()` がこの場合を受け止められます。有界量化子については、`bounded (∀̇∈ t φ)` は `bounded φ` と計算されるので、`h` はそのまま本体に渡され、再帰の結果を `δ-∀∈` か `δ-∃∈` で包みます。全体として、これらの節はすべての論理式に対して `bounded φ ≡ true → Δ₀ φ` を確立します。計算上の成功が証拠を与えるのです。項 `t` と `u` は結果に影響せず、逆向きの主張はここではどこにも行われません。
<!--/-->

```agda
checkΔ₀ (∃̇ φ) ()
checkΔ₀ (∀̇ φ) ()
checkΔ₀ (∀̇∈ t φ) h = δ-∀∈ (checkΔ₀ φ h)
checkΔ₀ (∃̇∈ t φ) h = δ-∃∈ (checkΔ₀ φ h)
```

<!--en-->
## Σ₁ and Π₁

Once formulas can be unboundedly quantified, the natural next question is how many unbounded quantifiers, and of which kind, a formula may contain. Σ₁ and Π₁ answer for exactly one block: a Σ₁ witness is either a Δ₀ witness, or one more unbounded existential applied to a Σ₁ witness for the body. So Σ₁-witnesses form a type nested over itself, recording any finite run of existentials over a Δ₀ core, and Π₁ is the same construction with the polarity flipped. Neither class allows the two quantifier kinds to alternate, and each binder consumes a body of arity `suc n` while producing a formula of arity `n`. The two families here stand alone; the next section reorganizes the same idea into a uniform hierarchy indexed by a level.
<!--zh-->
## Σ₁ 与 Π₁

公式既然可以无界量化，下一个自然的问题是：公式可以含多少个无界量词、是哪种。Σ₁ 与 Π₁ 恰好对一段量词作出回答：Σ₁ 见证要么是 Δ₀ 见证，要么是对某个 Σ₁ 见证 (其体公式) 再多施加一个无界存在量词。因此 Σ₁ 见证构成一个套在自己之上的类型，记录 Δ₀ 核心之上任意有限段存在量词；Π₁ 则是同一构造、极性翻转。两类都不允许两种量词交替，且每个约束词消耗元数 `suc n` 的体、产出元数 `n` 的公式。这里的两族是独立定义的；下一节把同一想法重组成按层级下标的统一层级。
<!--ja-->
## Σ₁ と Π₁

論理式が非有界に量化できるなら、次の自然な問いは、いくつの、どの種の非有界量化子を含んでよいかです。Σ₁ と Π₁ はちょうど一つの列について答えます。Σ₁ の証拠は、Δ₀ の証拠であるか、本体に対する Σ₁ の証拠に非有界な存在量化子をもう一つ施したものです。つまり Σ₁ の証拠は自分自身の上に重なる型をなし、Δ₀ の核の上の任意に有限な存在量化子の列を記録します。Π₁ は同じ構成で極性を逆にしたものです。どちらのクラスも二種の量化子の交替を許さず、各束縛子はアリティ `suc n` の本体を消費してアリティ `n` の論理式を生みます。ここでの二つの族は独立に定義されており、次の節が同じ考えをレベルで添字付けられた一様な階層へ組み替えます。
<!--/-->

<!--en-->
The nesting is visible in the two constructors of `Σ₁`. The base `σ-Δ₀` embeds any Δ₀ witness unchanged, so every bounded formula counts as Σ₁ with no extra quantifiers. The step `σ-∃` prepends one unbounded existential: from a Σ₁ witness for a body of arity `suc n` it builds one for `∃̇ φ`. Applying `σ-∃` repeatedly builds a finite block of existentials, and the block must end in a `σ-Δ₀` core; there is no way to introduce a universal quantifier along the way.
<!--zh-->
这种嵌套在 `Σ₁` 的两个构造子中清晰可见。基座 `σ-Δ₀` 原样嵌入任何 Δ₀ 见证，于是每个有界公式都算 Σ₁，不带额外量词。台阶 `σ-∃` 前置一个无界存在量词：从元数 `suc n` 的体的 Σ₁ 见证构造出 `∃̇ φ` 的见证。反复使用 `σ-∃` 便得到有限段存在量词，而这一段必须终于 `σ-Δ₀` 核心；途中没有办法引入全称量词。
<!--ja-->
この重なりは `Σ₁` の二つの構成子にはっきり現れます。基底 `σ-Δ₀` は任意の Δ₀ の証拠をそのまま埋め込むので、すべての有界論理式は追加の量化子なしで Σ₁ に数えられます。ステップ `σ-∃` は非有界な存在量化子を一つ前置きし、アリティ `suc n` の本体に対する Σ₁ の証拠から `∃̇ φ` の証拠を作ります。`σ-∃` を繰り返せば有限個の存在量化子の列ができ、その列は `σ-Δ₀` の核で終わらねばならず、途中で全称量化子を入れる道はありません。
<!--/-->

```agda
data Σ₁ {ℓc} {K : Type ℓc} : ∀ {n} → Formula K n → Type ℓc where
  σ-Δ₀ : ∀ {n} {φ : Formula K n} → Δ₀ φ → Σ₁ φ
  σ-∃  : ∀ {n} {φ : Formula K (suc n)} → Σ₁ φ → Σ₁ (∃̇ φ)

```

<!--en-->
`Π₁` is the mirror image: `π-Δ₀` shares the same Δ₀ base, and `π-∀` prepends one unbounded universal, again from a body of arity `suc n`. The two families are built by the same nesting pattern with the quantifier polarity reversed, and this difference in polarity is exactly what later absoluteness arguments will read off the witnesses.
<!--zh-->
`Π₁` 是其镜像：`π-Δ₀` 共享同一个 Δ₀ 基座，`π-∀` 前置一个无界全称量词，同样取自元数 `suc n` 的体。两族由同一嵌套模式构成，只是量词极性相反，而这一极性之差正是后面绝对性论证要从见证中读出的东西。
<!--ja-->
`Π₁` はその鏡像です。`π-Δ₀` は同じ Δ₀ の基底を共有し、`π-∀` は非有界な全称量化子を一つ前置きします。ここでも本体のアリティは `suc n` です。二つの族は量化子の極性を逆にした同じ重ね方で作られており、この極性の違いこそ、後に絶対性の議論が証拠から読み取るものです。
<!--/-->

```agda
data Π₁ {ℓc} {K : Type ℓc} : ∀ {n} → Formula K n → Type ℓc where
  π-Δ₀ : ∀ {n} {φ : Formula K n} → Δ₀ φ → Π₁ φ
  π-∀  : ∀ {n} {φ : Formula K (suc n)} → Π₁ φ → Π₁ (∀̇ φ)
```

<!--en-->
## The general hierarchy

One fixed block of unbounded quantifiers is only the first rung. The general Lévy hierarchy grades formulas by how often the polarity of their unbounded quantifiers alternates, and this chapter encodes the grading with two mutually defined inductive families, `Σₙ` and `Πₙ`, each carrying a natural number level `k`. The index `k` is a bound supplied by the witness itself: a witness at level `k` may use up to `k` alternations, but need not use exactly `k`, because Δ₀ formulas embed at every level. The implicit `n` remains the formula's arity, a separate bookkeeping that must not be confused with `k`. Each family closes under its own unbounded quantifier at a fixed level, while `σ-Π` and `π-Σ` are the two alternation steps that raise the index by crossing between the families.
<!--zh-->
## 一般层级

一段固定的无界量词只是第一级。一般Lévy 层级按无界量词极性交替的次数为公式分级，本章用两个互定义的归纳族 `Σₙ` 与 `Πₙ` 来编码这种分级，各带自然数层级 `k`。下标 `k` 是由见证自身提供的一个界：层级 `k` 的见证至多可用 `k` 次交替，但不必恰好用 `k` 次，因为 Δ₀ 公式在每个层级都有嵌入。隐含的 `n` 仍是公式的元数，是另一回事，不可与 `k` 混淆。每个族在固定层级上对自己那种无界量词封闭，而 `σ-Π` 与 `π-Σ` 则是跨越两族、抬升下标的两个交替步骤。
<!--ja-->
## 一般の Lévy 階層

非有界量化子の固定された一つの列は、最初の段にすぎません。一般のLévy 階層は、非有界量化子の極性が何回交替するかで論理式を分级し、本章はこの分级を相互に定義された二つの帰納的族 `Σₙ` と `Πₙ` で符号化します。それぞれ自然数のレベル `k` を帯びます。添字 `k` は証拠そのものが供給する上界です。レベル `k` の証拠は最大 `k` 回の交替を使えますが、ちょうど `k` 回使う必要はありません。Δ₀ 論理式がすべてのレベルで埋め込まれるからです。暗黙の `n` は依然として論理式のアリティであり、`k` と混同してはならない別の管理項目です。各族は固定レベルで自分の極性の非有界量化子の下で閉じ、`σ-Π` と `π-Σ` が族をまたいで添字を上げる二つの交互ステップです。
<!--/-->

<!--en-->
The two families must refer to each other, since an alternation is precisely a change of family, so they are declared in one `mutual` block. `Σₙ` carries the level index `k` before the formula index. The base `σ-Δ₀` lets a Δ₀ formula sit at any level `k`, which is why the level records an upper bound rather than an exact count. The alternation step `σ-Π` promotes a `Πₙ k` witness to `Σₙ (suc k)`, paying one increment of level for crossing polarity. Finally `σ-∃` extends a witness at level `suc k` by one more existential at that same level, the body's arity `suc n` shrinking back to `n`.
<!--zh-->
两族必须互相引用，因为交替恰恰就是换族，所以它们在一个 `mutual` 块中声明。`Σₙ` 在公式下标之前带上层级下标 `k`。基座 `σ-Δ₀` 允许 Δ₀ 公式处于任何层级 `k`，这正是层级记录上界而非确切次数的原因。交替台阶 `σ-Π` 把 `Πₙ k` 的见证提升为 `Σₙ (suc k)`，为跨越极性付出一级层。最后，`σ-∃` 在同一层级 `suc k` 上用多一个存在量词扩展见证，体的元数 `suc n` 缩回到 `n`。
<!--ja-->
交替とはまさに族の乗り換えですから、二つの族は互いを参照せねばならず、一つの `mutual` ブロックで宣言されます。`Σₙ` は論理式の添字の前にレベルの添字 `k` を帯びます。基底 `σ-Δ₀` は Δ₀ 論理式をどのレベル `k` にも置けるので、レベルが正確な回数ではなく上界を記録する理由がここにあります。交互ステップ `σ-Π` は `Πₙ k` の証拠を `Σₙ (suc k)` へ引き上げ、極性を越える代償としてレベルを一段支払います。最後に `σ-∃` はレベル `suc k` の証拠に同じレベルで存在量化子をもう一つ施して延ばし、本体のアリティ `suc n` は `n` に縮みます。
<!--/-->

```agda
mutual
  data Σₙ {ℓc} {K : Type ℓc} : ℕ → ∀ {n} → Formula K n → Type ℓc where
    σ-Δ₀ : ∀ {k n} {φ : Formula K n} → Δ₀ φ → Σₙ k φ
    σ-Π  : ∀ {k n} {φ : Formula K n} → Πₙ k φ → Σₙ (suc k) φ
    σ-∃  : ∀ {k n} {φ : Formula K (suc n)} → Σₙ (suc k) φ → Σₙ (suc k) (∃̇ φ)
```

<!--en-->
`Πₙ` is declared in the same mutual block with the dual shape: `π-Δ₀` embeds Δ₀ at every level, `π-Σ` lifts a `Σₙ k` witness to `Πₙ (suc k)`, and `π-∀` closes level `suc k` under unbounded universals. Together the two families record finite quantifier blocks whose cores alternate as often as the level permits. The separately defined Σ₁/Π₁ families of the previous section correspond in shape to `Σₙ 1` and `Πₙ 1`, that is `suc zero`: at level zero only the Δ₀ constructor is available, while the quantifier constructors require `suc k`.
<!--zh-->
`Πₙ` 在同一互定义块中以对偶形状声明：`π-Δ₀` 在每个层级嵌入 Δ₀，`π-Σ` 把 `Σₙ k` 的见证提升为 `Πₙ (suc k)`，`π-∀` 使层级 `suc k` 对无界全称量词封闭。两族合起来记录了核心按层级所允许的次数交替的有限量词段。上一节独立定义的 Σ₁/Π₁ 两族在形状上对应 `Σₙ 1` 与 `Πₙ 1`，即 `suc zero`：零层级只有 Δ₀ 构造子可用，而量词构造子都要求 `suc k`。
<!--ja-->
`Πₙ` は同じ相互定義ブロックで双対の形で宣言されます。`π-Δ₀` はすべてのレベルで Δ₀ を埋め込み、`π-Σ` は `Σₙ k` の証拠を `Πₙ (suc k)` へ引き上げ、`π-∀` はレベル `suc k` を非有界な全称量化子の下で閉じます。二つの族を合わせると、核がレベルの許す回数だけ交替する有限個の量化子の列が記録されます。前節で独立に定義された Σ₁/Π₁ の族は、形の上で `Σₙ 1` と `Πₙ 1`、すなわち `suc zero` に対応します。レベル 0 では Δ₀ の構成子しか使えず、量化子の構成子はいずれも `suc k` を要求するからです。
<!--/-->

```agda

  data Πₙ {ℓc} {K : Type ℓc} : ℕ → ∀ {n} → Formula K n → Type ℓc where
    π-Δ₀ : ∀ {k n} {φ : Formula K n} → Δ₀ φ → Πₙ k φ
    π-Σ  : ∀ {k n} {φ : Formula K n} → Σₙ k φ → Πₙ (suc k) φ
    π-∀  : ∀ {k n} {φ : Formula K (suc n)} → Πₙ (suc k) φ → Πₙ (suc k) (∀̇ φ)
```

<!--en-->
## Recap

The Lévy hierarchy is now represented by inductive witnesses. A Δ₀ witness excludes unbounded quantifiers by construction; Σ₁ and Π₁ add a finite block of one polarity; and the mutually defined Σₙ and Πₙ families bound further alternation independently of formula arity. Because each witness exposes the permitted outer shape, later induction arguments can treat bounded, existential, and universal cases separately.
<!--zh-->
## 小结

Lévy 层级现在由归纳见证表示。Δ₀ 见证从构造上排除无界量词；Σ₁ 与 Π₁ 各加入一段有限的单一极性量词；互定义的 Σₙ 与 Πₙ 族则把更高的交替层级同公式元数分开控制。每个见证都显露获准的外层形状，因此后续归纳论证可以分别处理有界、存在与全称情形。
<!--ja-->
## まとめ

Lévy 階層は帰納的な証拠として表されました。Δ₀ の証拠は構成上、非有界量化子を排除し、Σ₁ と Π₁ は一方の極性からなる有限列を加え、相互定義された Σₙ と Πₙ の族は、さらに高い交替レベルを論理式のアリティとは別に制限します。各証拠は許される外側の形を明らかにするので、後の帰納法では有界、存在、全称の場合を分けて扱えます。
<!--/-->

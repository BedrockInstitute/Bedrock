<!--en-->
# Definable subsets of a set

For a set `A`, the operator `Def A`{.Agda} collects exactly the subsets of `A` defined by a first-order formula over the restricted structure on `A`, with finitely many parameters from `A`. Its membership theorem exposes the formula, environment, and satisfaction relation used by later constructibility arguments.

Two design points carry the chapter. The formulas take `A`'s small member type `⟪ A ⟫` as their constant domain, so "parameters from `A`" is enforced by the type. And satisfaction is the **inner** semantics, on the restricted structure `𝒮ᵥ ↾ (∈ A)`: quantifiers range over members of `A` only, which is what "definable *in* `(A, ∈)`" means in the textbook, and which lets the essential smallness of the previous chapters apply here: every formula evaluates small, so `Def A` is a set, with no resizing needed at all.
<!--zh-->
# 集合的可定义子集

对集合 `A`，算子 `Def A`{.Agda} 恰好收集由 `A` 上限制结构中的一阶公式，并使用 `A` 中有限多个参数所定义的 `A` 的子集。其隶属定理给出后续可构造性论证所需的公式、环境与满足关系。

本章依赖两个设计点。公式以 `A` 的小成员类型 `⟪ A ⟫` 为常元域，因此类型本身保证参数来自 `A`。满足采用限制结构 `𝒮ᵥ ↾ (∈ A)` 上的**内层**语义，量词的范围只包括 `A` 的成员。这正是教科书中「在 `(A, ∈)` **中**可定义」的含义，也使前几章的本质小性在此适用：任何公式的求值都是小类型，因此 `Def A` 是集合，降层无需额外代价。
<!--ja-->
# 集合の定義可能な部分集合

集合 `A` に対して、演算子 `Def A`{.Agda} は、`A` 上の制限構造における一階論理式と `A` の有限個のパラメータで定義される `A` の部分集合をちょうど集めます。その所属定理は、後の構成可能性の議論で使う論理式、環境、充足関係を取り出します。

本章を支える設計上の要点が二つあります。第一に、論理式は `A` の小さな要素型 `⟪ A ⟫` を定数域として取るので、「`A` からのパラメータ」が型そのものによって強制されます。第二に、充足は制限構造 `𝒮ᵥ ↾ (∈ A)` 上の**内側**の意味論で読まれ、量化子の範囲は `A` の要素だけに限られます。これが教科書で「`(A, ∈)` **の中で**定義可能」と言う意味であり、前の章々の本質的小ささがここで効きます。すべての論理式の評価は小さな型になるので、`Def A` は集合であり、レベルの引き下げは一切不要です。
<!--/-->

<!--en-->
The question of this chapter: for a set `A`, which subsets of `A` can be singled out by a first-order formula interpreted inside `(A, ∈)`? The answer will be collected into a single operator `Def A`{.Agda}, itself a set of the ambient hierarchy. Everything takes place at one fixed universe level ℓ, so that `Def A` is small enough to exist as a set at the same level as `A`.
<!--zh-->
本章的问题是：对一个集合 `A`，哪些子集能被一阶公式在 `(A, ∈)` 内部解释时挑选出来？答案将被收集进一个算子 `Def A`{.Agda}，它本身是外围层级中的一个集合。一切都在一个固定的宇宙层级 ℓ 上进行，使 `Def A` 足够小，能与 `A` 在同一层级上作为集合存在。
<!--ja-->
この章の問いは次のものです。集合 `A` に対して、一階の論理式を `(A, ∈)` の中で解釈したとき、どの部分集合が取り出せるでしょうか。答えは一つの演算子 `Def A`{.Agda} に集められ、それ自体が周囲の階層の集合になります。すべては一つの宇宙レベル ℓ を固定して行われ、これにより `Def A` は `A` と同じレベルの集合として存在できる大きさを保ちます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Definability {ℓ : Level} where

open import FOL.ZFStructure using ( ZFStructure; Transitive )
```

<!--en-->
The formulas come from an inductive object language: `Formula K n` has constants indexed by a type `K` and `n` slots indexing free variables, with atoms built from a structure's membership and equality relations. Choosing `K = ⟪ A ⟫`, the small member type of `A`, makes "parameters from `A`" true by construction: every constant names a member of `A`. The bounded fragment `Δ₀` will matter later, when the inner and outer readings of satisfaction are compared; constant mapping and relabelling are the operations that move a formula between constant domains and transport satisfaction along such a move.
<!--zh-->
公式来自归纳的对象语言：`Formula K n` 的常元由类型 `K` 索引，`n` 个槽位索引自由变量，原子公式由结构的隶属与相等关系构成。取 `K = ⟪ A ⟫`，即 `A` 的小成员类型，「参数来自 `A`」便由构造自动成立：每个常元指称 `A` 的一个成员。有界片段 `Δ₀` 稍后比较满足的内层与外层读法时才会用到；常元映射与改名则是把公式在常元域之间移动并沿此移动搬运满足关系的操作。
<!--ja-->
論理式は帰納的な対象言語から来ます。`Formula K n` は、定数が型 `K` で添字づけられ、自由変数の `n` 個のスロットを持ち、原子論理式は構造の所属と等号の関係から組み立てられます。`K = ⟪ A ⟫`、つまり `A` の小さな要素型を選べば、「`A` からのパラメータ」は構成そのものによって成り立ちます。すべての定数は `A` の要素を名指すからです。有界断片 `Δ₀` は、充足の内側と外側の読みを比べる際に後で効きます。定数の対応付けと改名は、論理式を定数域の間で移し、その移動に沿って充足を輸送する操作です。
<!--/-->

```agda
open import FOL.Syntax using ( Formula; var; con; _∈̇_; ⊤̇ )
open import FOL.LevyHierarchy using ( Δ₀ )
open import FOL.Manipulation.ConstantMapping using ( mapFo )
open import FOL.Manipulation.Relabelling using ( mapΔ₀; ⊨-map )
import FOL.Absoluteness
```

<!--en-->
"Definable *in* `(A, ∈)`" means quantifiers may only range over members of `A`. So satisfaction must be taken in the structure restricted to the class `x ↦ x ∈ˢ A`, not in the ambient hierarchy. The chapter works over the ambient structure `𝒮ᵥ` carried by the level-ℓ hierarchy, with carrier `S` and membership `∈ₛ`; the restriction to `A` and the smallness of the restricted world come from the smallness chapter: given a class, a small type with an equivalence to the restricted carrier, and a constant interpretation, it rebuilds the restricted structure and proves every formula evaluates to a small proposition there. The restriction class here is simply membership in `A`.
<!--zh-->
「在 `(A, ∈)` **中**可定义」意味着量词只能在 `A` 的成员上取值。因此满足关系必须取在限制到类 `x ↦ x ∈ˢ A` 的结构上，而不是外围层级上。本章在层级 ℓ 上的外围结构 `𝒮ᵥ` 中工作，其载体为 `S`、隶属为 `∈ₛ`；向 `A` 的限制以及限制世界的小性来自小性章：给定一个类、一个与限制载体等价的小类型、以及常元解释，它重建限制结构并证明其中每个公式都求值为小命题。本章的限制类就是「属于 `A`」。
<!--ja-->
「`(A, ∈)` **の中で**定義可能」とは、量化子が `A` の要素の上だけで動くことを意味します。したがって充足は、クラス `x ↦ x ∈ˢ A` に制限した構造で取られなければならず、周囲の階層で取るのではありません。この章はレベル ℓ の階層が担う周囲の構造 `𝒮ᵥ` の上で作業します。台は `S`、所属は `∈ₛ` です。`A` への制限と制限された世界の小ささは小ささの章から来ます。クラス、制限された台と同値な小さな型、定数の解釈を与えると、制限された構造を組み立て直し、そこではすべての論理式が小さな命題に評価されることを証明します。ここでの制限のクラスは「`A` への所属」そのものです。
<!--/-->

```agda
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Smallness {ℓ} using ( module InnerSmall )

open import Cubical.Foundations.Equiv
  using ( _≃_; equivFun; invEq; invEquiv; compEquiv; propBiimpl→Equiv )
open import Cubical.Functions.Embedding using ( isEmbedding→Inj )
```

<!--en-->
Essential smallness is what lets satisfaction become an index for a set. Since each formula evaluates to a *small* proposition inside `(A, ∈)`, the members of `A` satisfying a formula can be indexed by a small type, and the hierarchy constructor `sett` turns a small index type and an indexing map into a set. Both the subset defined by one formula and `Def` itself will be built this way. Membership in a `sett` is then only a truncated existence statement, and propositions-valued targets force truncation to be eliminated into propositions rather than yielding chosen witnesses. The shape of the constructions produces the chapter's path-based specifications.
<!--zh-->
本质小性正是让满足关系能够为集合充当索引的关键。既然每个公式在 `(A, ∈)` 内都求值为**小**命题，满足公式的 `A` 的成员便可由一个小类型索引，而层级构造子 `sett` 把小索引类型和索引映射变成一个集合。一个公式定义出的子集与 `Def` 本身都将以这种方式构造。`sett` 的隶属于是只是截断的存在性陈述，而以命题为目标时截断只能消入命题，不会给出被选取的见证。这些构造的形状产生了本章基于路径的规格。
<!--ja-->
本質的小ささこそが、充足を集合の添字にできる根拠です。各論理式は `(A, ∈)` の中で**小さな**命題に評価されるので、式を満たす `A` の要素は小さな型で添字づけられ、階層の構成子 `sett` が小さな索引型と索引写像から集合を作ります。一つの論理式が定義する部分集合も `Def` 自身も、この方法で構成されます。すると `sett` の所属は切断された存在の命題にすぎず、命題値の目標に向かうとき切断は命題へ消去されるだけで、選ばれた証人は得られません。構成のこの形が、本章の経路に基づく仕様を生みます。
<!--/-->

```agda
open import Cubical.Data.Sigma using ( Σ-cong-equiv-snd )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
```

<!--en-->
Finally, the vocabulary of truth values. The truth algebra over `hProp (ℓ-suc ℓ)` interprets connectives and quantifiers as operations on propositions, so satisfaction takes values in `hProp (ℓ-suc ℓ)`, with `⟨ p ⟩` projecting the underlying proposition of an `hProp`. Equality of such propositions is a path, so specifications about membership will be stated as paths of propositions and proved by chains of them. With this setup, the next section fixes one set `A` and defines its definable subsets.
<!--zh-->
最后是真值的词汇。以 `hProp (ℓ-suc ℓ)` 为载的真值代数把联结词与量词解释为命题上的操作，因此满足关系取值于 `hProp (ℓ-suc ℓ)`，其中 `⟨ p ⟩` 取出 `hProp` 的底层命题。这类命题的相等是路径，因此关于隶属的规格将陈述为命题之间的路径，并用路径链来证明。就位之后，下一节固定一个集合 `A` 并定义其可定义子集。
<!--ja-->
最後に、真理値の語彙です。`hProp (ℓ-suc ℓ)` の上の真理値代数は結合子と量化子を命題に対する操作として解釈するので、充足は `hProp (ℓ-suc ℓ)` に値を取ります。`⟨ p ⟩` は `hProp` の根底にある命題を取り出します。この種の命題の相等は経路なので、所属についての仕様は命題としての経路で述べられ、経路の連結によって証明されます。これが整えば、次の節は一つの集合 `A` を固定し、その定義可能部分集合を定義します。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber; presentation
        ; isEmb⟪_⟫↪; _⊆_; extensionality )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open ZFStructure 𝒮ᵥ
```

<!--en-->
## The operator

Everything below is relative to one set `A`, so the section works in a module `DefOf A`. The restriction class is membership in `A`, and the essential smallness witness `e` is the library's `presentation`{.Agda}: the small member type `⟪ A ⟫` *is* the restricted carrier, up to equivalence (with the small membership converted pointwise to the large one). The constant interpretation `ι` sends a constant, an index in `⟪ A ⟫`, to the corresponding member of the restricted carrier; its first component is the member itself, definitionally.
<!--zh-->
## 算子

以下一切都相对于一个集合 `A`，故本节在模块 `DefOf A` 中工作。限制类取「属于 `A`」，而本质小见证 `e` 就是库的 `presentation`{.Agda}：小成员类型 `⟪ A ⟫` 与限制载体等价 (小成员关系逐点换成大的即可)。常元解释 `ι` 把常元，即 `⟪ A ⟫` 的索引，送到限制载体的对应成员；其第一分量按定义就是该成员本身。
<!--ja-->
## 演算子

以下のすべては一つの集合 `A` に相対的 so、本節はモジュール `DefOf A` の中で進みます。制限のクラスは「`A` への所属」であり、本質的小ささの証人 `e` はライブラリの `presentation`{.Agda} です。小さな要素型 `⟪ A ⟫` は、同値の違いを除いて、制限された台そのものです (小さい方の所属を点ごとに大きい方へ置き換えるだけです)。定数の解釈 `ι` は、定数つまり `⟪ A ⟫` の添字を、制限された台の対応する要素へ送ります。その第一成分は定義上、その要素そのものです。
<!--/-->

<!--en-->
The class `M` assigns to each set `x` the proposition `x ∈ˢ A`, so the restricted carrier `Σ[ x ∈ S ] (x ∈ᶜ M)` is, elementwise, a member of `A` together with the proof that it is one. The equivalence `e` exhibits this carrier as essentially small. Its first factor is the inverse of `presentation A`, which identifies a member of `A` merely lying in the fiber of the indexing map with an index in `⟪ A ⟫`; its second factor converts, for each `v`, the small membership statement `v ∈ₛ A` into the large one `v ∈ˢ A` and back. These are propositions, so the pointwise conversion is legitimate.
<!--zh-->
类 `M` 给每个集合 `x` 指派命题 `x ∈ˢ A`，因此限制载体 `Σ[ x ∈ S ] (x ∈ᶜ M)` 逐元素地就是 `A` 的一个成员连同「它是成员」的证明。等价 `e` 把这个载体表现为本质小。它的第一个因子是 `presentation A` 的逆，把仅仅落在索引映射纤维中的 `A` 的成员等同于 `⟪ A ⟫` 中的索引；第二个因子对每个 `v` 把小隶属陈述 `v ∈ₛ A` 双向换成大隶属陈述 `v ∈ˢ A`。由于这些是命题，逐点转换是合法的。
<!--ja-->
クラス `M` は各集合 `x` に命題 `x ∈ˢ A` を割り当てるので、制限された台 `Σ[ x ∈ S ] (x ∈ᶜ M)` は要素ごとに、`A` の要素と「それが要素である証拠」の対です。同値 `e` はこの台が本質的に小さいことを示します。第一因子は `presentation A` の逆で、索引写像のファイバーに「だけ」落ちている `A` の要素を `⟪ A ⟫` の添字と同一視します。第二因子は各 `v` について、小さい方の所属 `v ∈ₛ A` と大きい方の所属 `v ∈ˢ A` を両方向に変換します。これらは命題なので、点ごとの変換は正当です。
<!--/-->

```agda
module DefOf (A : S) where

  M : S → hProp (ℓ-suc ℓ)
  M x = x ∈ˢ A

  e : ⟪ A ⟫ ≃ (Σ[ x ∈ S ] (x ∈ᶜ M))
  e = compEquiv (invEquiv (presentation A))
```

<!--en-->
The constant interpretation `ι` is then just the equivalence `e` read as a function. Because the domain type of formulas will be `⟪ A ⟫` itself, a constant of the language is an index for a member of `A`, and `ι` decodes it into the restricted carrier. The first projection of `ι m` is definitionally the underlying set `⟪ A ⟫↪ m`, a fact the membership proofs will use without ceremony.
<!--zh-->
于是常元解释 `ι` 就是把等价 `e` 当作函数来读。由于公式的常元域将取 `⟪ A ⟫` 本身，语言中的一个常元就是 `A` 的某个成员的索引，`ι` 把它解码到限制载体中。`ι m` 的第一投影按定义就是底层集合 `⟪ A ⟫↪ m`，隶属证明会不加修饰地使用这一事实。
<!--ja-->
定数の解釈 `ι` は、同値 `e` を関数として読んだものにすぎません。論理式の定数域は `⟪ A ⟫` 自身になるので、言語の定数とは `A` の要素への添字であり、`ι` はそれを制限された台へ復号します。`ι m` の第一射影は定義上、基礎となる集合 `⟪ A ⟫↪ m` であり、所属の証明はこの事実をそのまま使います。
<!--/-->

```agda
        (Σ-cong-equiv-snd (λ v →
          propBiimpl→Equiv (snd (v ∈ₛ A)) (snd (v ∈ˢ A))
            (∈∈ₛ {a = v} {b = A} .snd) (∈∈ₛ {a = v} {b = A} .fst)))

  ι : ⟪ A ⟫ → Σ[ x ∈ S ] (x ∈ᶜ M)
  ι = equivFun e
```

<!--en-->
Opening `InnerSmall` at this data rebuilds the world: the structure `𝒮M` restricted to membership in `A`, its satisfaction relation `⊨ᵐ`, and the theorem `⊨ᵐ-small` that every formula over `⟪ A ⟫` evaluates to a small proposition. Making the opening public means later chapters read inner satisfaction under exactly these names. From here on, "satisfies" always means this inner relation, with quantifiers confined to members of `A`.
<!--zh-->
在这些数据上开启 `InnerSmall` 便重建了世界：限制到「属于 `A`」的结构 `𝒮M`、其满足关系 `⊨ᵐ`，以及定理 `⊨ᵐ-small`，即 `⟪ A ⟫` 上的每个公式都求值为小命题。以 public 开启意味着后续章节恰在这些名字下读取内层满足。从这里起，「满足」一律指这个内层关系，量词只限于 `A` 的成员。
<!--ja-->
このデータに対して `InnerSmall` を開くと、世界が組み立て直されます。「`A` への所属」に制限した構造 `𝒮M`、その充足関係 `⊨ᵐ`、そして `⟪ A ⟫` 上のすべての論理式が小さな命題に評価されるという定理 `⊨ᵐ-small` です。public に開くことで、後の章は内側の充足をまさにこれらの名前で読みます。以降、「充足する」とは常にこの内側の関係を指し、量化子は `A` の要素に限られます。
<!--/-->

```agda

  open InnerSmall M ⟪ A ⟫ e {K = ⟪ A ⟫} ι public
```

<!--en-->
With the inner satisfaction `⊨ᵐ` and its smallness in scope, the operator can be defined directly. `smallSat φ m` is the truth value of `φ` at the member `m`, living one universe down; `defSet φ` is the subset `φ` defines out of `A`, a `sett` over the members `φ` selects; and `Def A` is the collection of all of them, indexed by the formulas themselves. A formula is a piece of inductive data in `Type ℓ`, hence a legitimate small index: this is precisely **syntax as index set**.
<!--zh-->
内层满足 `⊨ᵐ` 与其小性就位后，算子可直接定义。`smallSat φ m` 是 `φ` 在成员 `m` 处的真值，位于低一层宇宙；`defSet φ` 是 `φ` 从 `A` 中定出的子集，在 `φ` 选中的成员上应用 `sett`；`Def A` 则是这些子集的全体，以公式自身为索引。公式是 `Type ℓ` 中的归纳数据，恰好构成合法的小索引；这里使用的正是**语法当索引集**。
<!--ja-->
内側の充足 `⊨ᵐ` とその小ささが手に入れば、演算子は直接定義できます。`smallSat φ m` はメンバー `m` における `φ` の真理値で、一つ下の宇宙に住みます。`defSet φ` は `φ` が `A` から定義する部分集合で、`φ` が選ぶ要素たちの上の `sett` です。そして `Def A` はそれら全体の集まりで、論理式そのものを添字とします。論理式は `Type ℓ` の帰納的データなので、正当な小さな添字です。これこそ**構文を索引集合として使う**という発想です。
<!--/-->

<!--en-->
The compression `smallSat` packages the two-step evaluation: `⊨ᵐ-small φ (ι m ∷ [])` is a pair whose first component is a small proposition equivalent to the inner satisfaction statement, and whose second component is that equivalence. The environment `ι m ∷ []` has a single entry because `φ` has one free-variable slot, filled by the member `m` through `ι`. Independently of this, any constants occurring in `φ` are interpreted through the constant interpretation `ι`, so they may name arbitrary members of `A`: parameters enter through constants, and the variable entry only fixes where the single free slot is evaluated. The underlying proposition `⟨ smallSat φ m ⟩` says that `φ` holds at `m` inside `(A, ∈)`, in the small form suitable for indexing a `sett`.
<!--zh-->
压缩 `smallSat` 打包了两步求值：`⊨ᵐ-small φ (ι m ∷ [])` 是一个对子，第一分量是与内层满足陈述等价的小命题，第二分量是那个等价本身。环境 `ι m ∷ []` 只有一项，因为 `φ` 只有一个自由变量槽位，由成员 `m` 经 `ι` 填入。与此独立地，`φ` 中出现的任何常元都经常元解释 `ι` 解释，因此可以指称 `A` 的任意成员：参数经由常元进入，而变量那一项只是固定单个自由槽位的求值位置。底层命题 `⟨ smallSat φ m ⟩` 表示 `φ` 在 `(A, ∈)` 内于 `m` 处成立，且已是适合为 `sett` 充当索引的小形式。
<!--ja-->
圧縮 `smallSat` は二段階の評価をまとめます。`⊨ᵐ-small φ (ι m ∷ [])` は対で、第一成分は内側の充足の命題と同値な小さな命題、第二成分がその同値です。環境 `ι m ∷ []` の項目が一つなのは、`φ` の自由変数のスロットが一つで、それを要素 `m` が `ι` を通じて埋めるからです。それとは独立に、`φ` に現れる任意の定数は定数の解釈 `ι` を通して解釈されるので、`A` のどんな要素でも名指せます。パラメータは定数を通じて入り、変数の項は単一の自由スロットをどこで評価するかを固定するだけです。根底の命題 `⟨ smallSat φ m ⟩` は、`φ` が `(A, ∈)` の中で `m` において成り立つことを、`sett` の添字に適した小さな形で言います。
<!--/-->

```agda
  smallSat : Formula ⟪ A ⟫ 1 → ⟪ A ⟫ → hProp ℓ
  smallSat φ m = ⊨ᵐ-small φ (ι m ∷ []) .fst

  defSet : Formula ⟪ A ⟫ 1 → S
  defSet φ = sett (Σ[ m ∈ ⟪ A ⟫ ] ⟨ smallSat φ m ⟩) (λ p → ⟪ A ⟫↪ (p .fst))

  Def : S
```

<!--en-->
The definable subset `defSet φ` is presented by the index type `Σ[ m ∈ ⟪ A ⟫ ] ⟨ smallSat φ m ⟩`: an index is a member `m` together with a proof that `φ` holds at it, and the indexing map sends such a pair to the set `⟪ A ⟫↪ m`. Note the truncation discipline: the proof component is a proof, not chosen data, and membership in `defSet φ` only asks for a proof to *merely* exist. Finally `Def` applies the same construction one level up, with the formulas themselves as the index family: each formula merely hits some `defSet φ`. Because formulas live in `Type ℓ`, the index type is small and the result is again a set of the hierarchy.
<!--zh-->
可定义子集 `defSet φ` 由索引类型 `Σ[ m ∈ ⟪ A ⟫ ] ⟨ smallSat φ m ⟩` 呈现：一个索引是成员 `m` 连同「`φ` 在 `m` 处成立」的证明，索引映射把这个对子送到集合 `⟪ A ⟫↪ m`。注意截断纪律：证明分量是证明而非被选取的数据，`defSet φ` 的成员只要求这样的证明**仅仅**存在。最后，`Def` 在上一层重复同一构造，以公式本身为索引族：每个索引仅仅命中某个 `defSet φ`。由于公式住在 `Type ℓ` 中，索引类型是小的，结果仍是层级中的集合。
<!--ja-->
定義可能部分集合 `defSet φ` は、索引型 `Σ[ m ∈ ⟪ A ⟫ ] ⟨ smallSat φ m ⟩` で提示されます。索引とはメンバー `m` と「`φ` が `m` で成り立つ」ことの証明の対であり、索引写像はその対を集合 `⟪ A ⟫↪ m` へ送ります。切断の規律に注意してください。証明の成分は証明であって選ばれたデータではなく、`defSet φ` の所属はそのような証明が「だけ」存在することを要求します。最後に `Def` は同じ構成を一段上で繰り返し、論理式そのものを索引族とします。各索引はある `defSet φ` に「だけ」ヒットします。論理式は `Type ℓ` に住むので索引型は小さく、結果は再び階層の集合になります。
<!--/-->

```agda
  Def = sett (Formula ⟪ A ⟫ 1) defSet
```

<!--en-->
## Membership, specified

Both `Def` and each `defSet φ` are `sett`s, so their membership is *definitionally* "merely hit by the index family". For `Def` this needs no proof at all: a member of `Def` is merely a `defSet φ`. For the definable subsets there are two specifications: their members stay inside `A`, and a member `⟪ A ⟫↪ m` belongs to `defSet φ` **exactly when the inner world satisfies `φ` at `m`**; this is literally what "definable subset" means (the compression `smallSat` was only an encoding, and the equivalence preserves it).
<!--zh-->
## 隶属，给出规格

`Def` 与每个 `defSet φ` 都由 `sett` 构造，因此其隶属关系**按定义**表示相应索引的仅仅存在性。对 `Def` 无须另作证明：`Def` 的成员仅仅就是某个 `defSet φ`。可定义子集有两条规格：它的成员都属于 `A`；成员 `⟪ A ⟫↪ m` 属于 `defSet φ`，**当且仅当内层世界在 `m` 处满足 `φ`**。这两条规格直接给出「可定义子集」的含义；`smallSat` 的压缩只是编码，并不改变这个等价关系。
<!--ja-->
## 所属の特徴付け

`Def` も各 `defSet φ` も `sett` で構成されるので、その所属は**定義上**「索引族にだけヒットすること」を意味します。`Def` については証明はまったく不要です。`Def` の要素はある `defSet φ` である「だけ」だからです。定義可能部分集合には二つの仕様があります。その要素は `A` の中にとどまること、そして要素 `⟪ A ⟫↪ m` が `defSet φ` に属するのは**内側の世界が `m` で `φ` を充足するときちょうどそのときに限る**ことです。これが文字どおり「定義可能部分集合」の意味であり、圧縮 `smallSat` は符号化にすぎず、同値がそれを保ちます。
<!--/-->

<!--en-->
The first specification says each `defSet φ` is contained in `A`. A member of `defSet φ` merely comes from an index `(m , _)` with some proof, together with a path `q` identifying the indexed set with `y`. Since membership in `A` is a proposition, truncation can be eliminated into it: the proof transports the known fact `⟪ A ⟫↪ m ∈ˢ A` along `q` to obtain `y ∈ˢ A`. The known fact itself is exactly the small membership `⟪ A ⟫↪ m ∈ₛ A`, converted through `∈∈ₛ`.
<!--zh-->
第一条规格说每个 `defSet φ` 都包含于 `A`。`defSet φ` 的成员仅仅来自带某个证明的索引 `(m , _)`，连同把索引集合等同于 `y` 的路径 `q`。由于 `A` 中的隶属是命题，截断可消入命题：该证明沿 `q` 把已知事实 `⟪ A ⟫↪ m ∈ˢ A` 搬运过去，得到 `y ∈ˢ A`。这个已知事实正是小隶属 `⟪ A ⟫↪ m ∈ₛ A` 经 `∈∈ₛ` 转换而来。
<!--ja-->
第一の仕様は、各 `defSet φ` が `A` に含まれると言います。`defSet φ` の要素は、ある証明付きの索引 `(m , _)` から「だけ」来ており、索引付けされた集合を `y` と同一視する経路 `q` を伴います。`A` への所属は命題なので、切断は命題へ消去できます。その証明が既知の事実 `⟪ A ⟫↪ m ∈ˢ A` を `q` に沿って輸送し、`y ∈ˢ A` を得ます。既知の事実そのものは、小さい方の所属 `⟪ A ⟫↪ m ∈ₛ A` を `∈∈ₛ` を通して変換したものです。
<!--/-->

```agda
  defSet⊆A : (φ : Formula ⟪ A ⟫ 1) (y : S) → ⟨ y ∈ˢ defSet φ ⟩ → ⟨ y ∈ˢ A ⟩
  defSet⊆A φ y = PT.rec (snd (y ∈ˢ A)) λ { ((m , _) , q) →
    subst (λ v → ⟨ v ∈ˢ A ⟩) q
          (∈∈ₛ {a = ⟪ A ⟫↪ m} {b = A} .snd (∈ₛ⟪ A ⟫↪ m)) }

  private
```

<!--en-->
The second specification is the heart of the chapter, and it is stated as a path of propositions, not a pair of implications: membership of `⟪ A ⟫↪ m` in `defSet φ` equals the inner satisfaction statement `(ι m ∷ []) ⊨ᵐ φ`. The auxiliary `decode` re-expands `smallSat` into the full pair, so the equivalence in its second component is available to both directions. Note also the private injectivity lemma: `⟪ A ⟫↪` is an embedding of `⟪ A ⟫` into the carrier, so paths between its values come from paths between indices; this will recover `m' ≡ m` from a path of sets.
<!--zh-->
第二条规格是本章的核心，它被陈述为命题之间的路径，而不是一对蕴含：`⟪ A ⟫↪ m` 属于 `defSet φ` 这一命题等于内层满足陈述 `(ι m ∷ []) ⊨ᵐ φ`。辅助定义 `decode` 把 `smallSat` 重新展开成完整的对子，于是其第二分量中的等价对两个方向都可用。另请注意私有的单射性引理：`⟪ A ⟫↪` 是从 `⟪ A ⟫` 到载体的嵌入，其值之间的路径来自索引之间的路径；这将从集合的路径恢复出 `m' ≡ m`。
<!--ja-->
第二の仕様は本章の核心で、含意の対ではなく命題としての経路で述べられます。`⟪ A ⟫↪ m` が `defSet φ` に属するという命題は、内側の充足の命題 `(ι m ∷ []) ⊨ᵐ φ` と等しいのです。補助定義 `decode` は `smallSat` を完全な対に展開し直し、第二成分の同値を両方向から使えるようにします。また private の単射性補題に注意してください。`⟪ A ⟫↪` は `⟪ A ⟫` から台への埋め込みなので、その値の間の経路は添字の間の経路から来ます。これにより集合の経路から `m' ≡ m` を復元します。
<!--/-->

```agda
    ⟪⟫↪-inj : {m' m : ⟪ A ⟫} → ⟪ A ⟫↪ m' ≡ ⟪ A ⟫↪ m → m' ≡ m
    ⟪⟫↪-inj {m'} {m} = isEmbedding→Inj isEmb⟪ A ⟫↪ m' m

  defSet-mem : (φ : Formula ⟪ A ⟫ 1) (m : ⟪ A ⟫)
             → (⟪ A ⟫↪ m ∈ˢ defSet φ) ≡ ((ι m ∷ []) ⊨ᵐ φ)
  defSet-mem φ m = ⇔toPath fwd bwd
```

<!--en-->
The forward direction unpacks what membership merely gives: an index `(m' , h)`, where `h` proves `smallSat φ m'`, and a path `q` with `⟪ A ⟫↪ m' ≡ ⟪ A ⟫↪ m`. Injectivity turns `q` into `m' ≡ m`, and transporting `h` along it yields a proof of `smallSat φ m`. The second component of `decode`, the equivalence between the small proposition and inner satisfaction, then converts this proof into the target statement. Every ingredient is used: truncation gives the index, embedding gives the path between indices, transport moves the proof, equivalence decodes it.
<!--zh-->
正向展开隶属仅仅给出的内容：索引 `(m' , h)`，其中 `h` 证明 `smallSat φ m'`，以及满足 `⟪ A ⟫↪ m' ≡ ⟪ A ⟫↪ m` 的路径 `q`。单射性把 `q` 变成 `m' ≡ m`，沿它搬运 `h` 得到 `smallSat φ m` 的证明。然后 `decode` 的第二分量，即小命题与内层满足之间的等价，把这个证明转换为目标陈述。每个部件都派上用场：截断给出索引，嵌入给出索引间的路径，移送搬运证明，等价将其解码。
<!--ja-->
順方向は、所属が「だけ」与えるものを展開します。証明 `h` が `smallSat φ m'` を示す索引 `(m' , h)` と、`⟪ A ⟫↪ m' ≡ ⟪ A ⟫↪ m` となる経路 `q` です。単射性が `q` を `m' ≡ m` に変え、それに沿って `h` を輸送すれば `smallSat φ m` の証明が得られます。次に `decode` の第二成分、つまり小さな命題と内側の充足との同値が、この証明を目標の命題へ変換します。部品はすべて使われます。切断が索引を、埋め込みが添字の間の経路を、輸送が証明の移動を、同値が復号を担います。
<!--/-->

```agda
    where
    decode = ⊨ᵐ-small φ (ι m ∷ [])
    fwd : ⟨ ⟪ A ⟫↪ m ∈ˢ defSet φ ⟩ → ⟨ (ι m ∷ []) ⊨ᵐ φ ⟩
    fwd = PT.rec (snd ((ι m ∷ []) ⊨ᵐ φ)) λ { ((m' , h) , q) →
      invEq (decode .snd) (subst (λ k → ⟨ smallSat φ k ⟩) (⟪⟫↪-inj q) h) }
```

<!--en-->
The reverse direction is short because the equivalence also runs that way: given `hφ : (ι m ∷ []) ⊨ᵐ φ`, apply the equivalence to get a proof of `smallSat φ m`, and take the index `(m , proof)` with the trivial path `refl`. The result is truncated with `∣_∣₁`, which is all that membership demands. Together the two directions give the promised exact correspondence between inner satisfaction and membership in the definable subset.
<!--zh-->
反向很短，因为等价同样可以反向运行：给定 `hφ : (ι m ∷ []) ⊨ᵐ φ`，应用该等价得到 `smallSat φ m` 的证明，取索引 `(m , 证明)` 与平凡路径 `refl`。结果用 `∣_∣₁` 截断，这正是隶属所要求的。两个方向合起来给出内层满足与可定义子集隶属之间的精确对应。
<!--ja-->
逆方向は短くて済みます。同値は逆にも走るからです。`hφ : (ι m ∷ []) ⊨ᵐ φ` が与えられれば、同値を適用して `smallSat φ m` の証明を得て、自明な経路 `refl` とともに索引 `(m , 証明)` を取ります。結果は `∣_∣₁` で切断されますが、所属が要求するのはそれだけです。両方向を合わせて、内側の充足と定義可能部分集合への所属との、約束された正確な対応が得られます。
<!--/-->

```agda
    bwd : ⟨ (ι m ∷ []) ⊨ᵐ φ ⟩ → ⟨ ⟪ A ⟫↪ m ∈ˢ defSet φ ⟩
    bwd hφ = ∣ (m , equivFun (decode .snd) hφ) , refl ∣₁
```

<!--en-->
## Def refines, never shrinks

Two facts locate `Def A` before any transitivity assumption is made. The always-true formula defines all of `A`, so `A` itself is an element of `Def A`; and every element of `Def A` is a subset of `A`. This does not yet assert `A ⊆ Def A`. That stronger inclusion is proved in the next section from transitivity, by defining each member of `A` separately.
<!--zh-->
## Def 只精化，不缩水

在不假设传递性时，两条事实已经确定 `Def A` 的位置。恒真公式定义出整个 `A`，所以 `A` 本身是 `Def A` 的一个成员；而 `Def A` 的每个成员都是 `A` 的子集。这里尚未断言 `A ⊆ Def A`。下一节将在传递性前提下逐一可定义 `A` 的成员，从而证明这条更强的包含。
<!--ja-->
## Def は細分するが要素を失わない

推移性を仮定する前でも、二つの事実が `Def A` の位置を定めます。恒真論理式は `A` 全体を定義するので、`A` 自身が `Def A` の要素です。また、`Def A` の各要素は `A` の部分集合です。この段階ではまだ `A ⊆ Def A` を主張していません。次節では推移性のもとで `A` の各要素を個別に定義し、このより強い包含を証明します。
<!--/-->

<!--en-->
The private helper `A-mem` converts a large membership proof into its fiber form: a member `y` of `A` merely comes from some index `m` with `⟪ A ⟫↪ m ≡ y`, and since `∈-asFiber` returns the fiber as data (the truncation lives inside the membership proof it consumes), the pair can be taken apart with `let`. Equality of the two sets is then proved by `extensionality`, so it suffices to establish inclusion in both directions.
<!--zh-->
私有辅助 `A-mem` 把大的隶属证明转成纤维形式：`A` 的成员 `y` 仅仅来自某个索引 `m`，满足 `⟪ A ⟫↪ m ≡ y`；由于 `∈-asFiber` 以数据形式返回纤维 (截断位于它消费的隶属证明之内)，可以用 `let` 把对子拆开。两个集合的相等由 `extensionality` 证明，因此只需给出两个方向的包含。
<!--ja-->
private の補助 `A-mem` は大きい方の所属の証明をファイバーの形に変換します。`A` の要素 `y` は、`⟪ A ⟫↪ m ≡ y` を満たすある添字 `m` から「だけ」来ており、`∈-asFiber` がファイバーをデータとして返す (切断はそれが消費する所属の証明の中にある) ので、`let` で対を分解できます。二つの集合の等しさは `extensionality` で示すので、両方向の包含を確立すれば十分です。
<!--/-->

```agda
  private
    A-mem : (y : S) → ⟨ y ∈ˢ A ⟩ → Σ[ m ∈ ⟪ A ⟫ ] (⟪ A ⟫↪ m ≡ y)
    A-mem y y∈ = ∈-asFiber {a = y} {b = A} y∈

  defSet⊤≡A : defSet ⊤̇ ≡ A
  defSet⊤≡A = extensionality (defSet ⊤̇) A (sub₁ , sub₂)
```

<!--en-->
The easy direction reuses the containment just proved. A set-theoretic member `y` of `defSet ⊤̇` gives, via the definition of `sett` membership, a truncated index; `defSet⊆A` then places `y` inside `A`, and the conversion `∈∈ₛ` repackages the statement in the form the inclusion `⊆` expects. Nothing here uses what `⊤̇` means: this half holds for every `defSet φ`.
<!--zh-->
容易的方向复用刚证得的包含。`defSet ⊤̇` 的集合论成员 `y` 经 `sett` 隶属的定义给出截断的索引；`defSet⊆A` 随即把 `y` 放进 `A`，转换 `∈∈ₛ` 再把陈述包装成包含 `⊆` 所期望的形式。这一半完全不用 `⊤̇` 的含义：它对每个 `defSet φ` 都成立。
<!--ja-->
容易な方向は、今証明した包含を再利用します。`defSet ⊤̇` の集合論的な要素 `y` は、`sett` の所属の定義を通して切断された索引を与え、`defSet⊆A` が `y` を `A` の中に置き、変換 `∈∈ₛ` が命題を包含 `⊆` が期待する形に整えます。ここでは `⊤̇` の意味は一切使わず、この半分はすべての `defSet φ` で成り立ちます。
<!--/-->

```agda
    where
    sub₁ : ⟨ defSet ⊤̇ ⊆ A ⟩
    sub₁ y y∈ₛ = ∈∈ₛ {a = y} {b = A} .fst
      (defSet⊆A ⊤̇ y (∈∈ₛ {a = y} {b = defSet ⊤̇} .snd y∈ₛ))
    sub₂ : ⟨ A ⊆ defSet ⊤̇ ⟩
```

<!--en-->
The converse uses what "true" means: since `⊤̇` holds at every member, `defSet-mem ⊤̇ m` identifies `⟪ A ⟫↪ m ∈ˢ defSet ⊤̇` with a proposition that any inhabitant proves, here supplied as the identity function. So each member `y` of `A`, being merely `⟪ A ⟫↪ m`, is transported along the fiber path into `defSet ⊤̇`. Note the use of `sym (defSet-mem ⊤̇ m)` inside `subst ⟨_⟩`: the theorem is a path of propositions, so it transports proofs in whichever direction the goal needs.
<!--zh-->
反向用到「真」的含义：由于 `⊤̇` 在每个成员处成立，`defSet-mem ⊤̇ m` 把 `⟪ A ⟫↪ m ∈ˢ defSet ⊤̇` 等同于一个任何元素都能证明的命题，这里以恒等函数给出。于是 `A` 的每个成员 `y`，既然仅仅是 `⟪ A ⟫↪ m`，就沿纤维路径被搬运进 `defSet ⊤̇`。注意 `subst ⟨_⟩` 中 `sym (defSet-mem ⊤̇ m)` 的用法：该定理是命题之间的路径，因此可以按目标需要的方向搬运证明。
<!--ja-->
逆方向は「真」の意味を使います。`⊤̇` はすべてのメンバーで成り立つので、`defSet-mem ⊤̇ m` は `⟪ A ⟫↪ m ∈ˢ defSet ⊤̇` を、どんな要素でも証明できる命題と同一視します。ここではそれを恒等関数として与えます。したがって `A` の各要素 `y` は、`⟪ A ⟫↪ m` である「だけ」なので、ファイバーの経路に沿って `defSet ⊤̇` の中へ輸送されます。`subst ⟨_⟩` の中の `sym (defSet-mem ⊤̇ m)` に注意してください。この定理は命題としての経路なので、目標が必要とするどちらの方向にも証明を輸送できます。
<!--/-->

```agda
    sub₂ y y∈ₛ =
      let (m , q) = A-mem y (∈∈ₛ {a = y} {b = A} .snd y∈ₛ)
      in subst (λ v → ⟨ v ∈ₛ defSet ⊤̇ ⟩) q
           (∈∈ₛ {a = ⟪ A ⟫↪ m} {b = defSet ⊤̇} .fst
             (subst ⟨_⟩ (sym (defSet-mem ⊤̇ m)) (λ z → z)))
```

<!--en-->
The dual containment `Def∋⊆A` says every element of `Def A` is a subset of `A`. Its hypothesis is itself a truncation: `x` merely is some `defSet φ`. The target is a proposition, being built from propositions by products, so `PT.rec` may eliminate the truncation; the case then transports `y ∈ˢ x` backwards along the path identifying `x` with `defSet φ` and applies the containment of `defSet φ`. Combined with `defSet⊤≡A`, which yields `A ∈ Def`, the picture is complete: `Def` contains `A` as an element and contains only subsets of `A`.
<!--zh-->
对偶的包含 `Def∋⊆A` 说 `Def A` 的每个元素都是 `A` 的子集。它的前提本身就是截断：`x` 仅仅是某个 `defSet φ`。目标是由命题经乘积构成的命题，因此 `PT.rec` 可以消去截断；随后沿把 `x` 等同于 `defSet φ` 的路径反向搬运 `y ∈ˢ x`，并应用 `defSet φ` 的包含。与给出 `A ∈ Def` 的 `defSet⊤≡A` 合观，图景完整：`Def` 把 `A` 作为元素包含在内，且只包含 `A` 的子集。
<!--ja-->
双対の包含 `Def∋⊆A` は、`Def A` の各要素が `A` の部分集合であると言います。その前提はそれ自体が切断です。`x` はある `defSet φ` である「だけ」です。目標は命題から積を作った命題なので、`PT.rec` が切断を消去できます。そして、`x` を `defSet φ` と同一視する経路に沿って `y ∈ˢ x` を逆方向に輸送し、`defSet φ` の包含を適用します。`A ∈ Def` を与える `defSet⊤≡A` と合わせて状況は完結します。`Def` は `A` を要素として含み、含むのは `A` の部分集合だけです。
<!--/-->

```agda

  Def∋⊆A : (x : S) → ⟨ x ∈ˢ Def ⟩ → (y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ y ∈ˢ A ⟩
  Def∋⊆A x = PT.rec (isPropΠ λ y → isPropΠ λ _ → snd (y ∈ˢ A))
    (λ { (φ , q) y y∈x → defSet⊆A φ y (subst (λ s → ⟨ y ∈ˢ s ⟩) (sym q) y∈x) })
```

<!--en-->
## Under transitivity, A ⊆ Def A

When `A` is transitive, each **member** `a` of `A` is itself definable, by the same two-symbol construction that built intersection in the model chapter: the atomic formula "the variable is a member of `a`". Separation's implicit "∈ A" clause is what transitivity discharges: members of `a` are already members of `A`, so the atom carves out exactly `a`. Hence `A ⊆ Def A`: no element is omitted. Combined with the previous section, iterating `Def` can only accumulate, which is exactly what the constructible tower requires.
<!--zh-->
## 传递性之下，A ⊆ Def A

当 `A` 传递时，`A` 的每个**成员** `a` 自身也可定义：仍用模型章构造交集的那条两符号途径，即原子公式「该变量属于 `a`」。分离暗含的「∈ A」条件恰好由传递性保证：`a` 的成员已是 `A` 的成员，于是原子公式刻出的正是 `a`。故 `A ⊆ Def A`：没有任何元素被遗漏。与上一节合观，迭代 `Def` 只增不减，正合可构造塔的需要。
<!--ja-->
## 推移性の下で A ⊆ Def A

`A` が推移的なら、`A` の各**要素** `a` 自身も定義可能です。モデルの章で交わりを作ったのと同じ二つの記号による構成、すなわち原子論理式「その変数は `a` の要素である」を使います。分離が暗黙に課す「∈ A」の条件を埋めるのがまさに推移性です。`a` の要素はすでに `A` の要素なので、原子式が切り出すのはちょうど `a` です。よって `A ⊆ Def A` であり、落とされる要素はありません。前節と合わせると、`Def` の反復は蓄積するだけであり、これは構成可能階層がまさに要求する性質です。
<!--/-->

<!--en-->
The submodule takes transitivity of `A` as an explicit hypothesis. The atomic formula `atom mₐ` is `var zero ∈̇ con mₐ`: one free-variable slot, and a single constant naming the element `mₐ`. This is where the design choice of using `⟪ A ⟫` as the constant domain pays off again: every member of `A` is available as a constant, with `ι` decoding it into the restricted carrier.
<!--zh-->
子模块以 `A` 的传递性为显式前提。原子公式 `atom mₐ` 是 `var zero ∈̇ con mₐ`：一个自由变量槽位，加上命名元素 `mₐ` 的单个常元。这里再次体现了以 `⟪ A ⟫` 为常元域这一设计选择的好处：`A` 的每个成员都可充作常元，由 `ι` 解码到限制载体。
<!--ja-->
この議論は `A` の推移性を明示的な仮定として取ります。原子論理式 `atom mₐ` は `var zero ∈̇ con mₐ` で、自由変数のスロットが一つと、要素 `mₐ` を名指す単一の定数からなります。`⟪ A ⟫` を定数域として使うという設計判断がここでも効きます。`A` のすべての要素が定数として使え、`ι` がそれを制限された台へ復号するからです。
<!--/-->

```agda
  module Refine (Atrans : Transitive 𝒮ᵥ M) where

    atom : ⟪ A ⟫ → Formula ⟪ A ⟫ 1
    atom mₐ = var zero ∈̇ con mₐ

    atom-mem : (mₐ m : ⟪ A ⟫)
             → (⟪ A ⟫↪ m ∈ˢ defSet (atom mₐ)) ≡ (⟪ A ⟫↪ m ∈ˢ ⟪ A ⟫↪ mₐ)
```

<!--en-->
The specialization of the membership theorem to this atom is immediate, because the environment is fixed to the single parameter `m` and the inner truth of `var zero ∈̇ con mₐ` is, by the semantics of atoms, precisely membership `⟪ A ⟫↪ m ∈ˢ ⟪ A ⟫↪ mₐ` inside the restricted world. Since restricted membership is defined by the ambient membership of the underlying sets, the atom really selects the elements of `⟪ A ⟫↪ mₐ`; the remaining work is only to show the presented set `defSet (atom mₐ)` equals that element.
<!--zh-->
把隶属定理特化到这个原子是直接的：环境固定为单个参数 `m`，而由原子公式的语义，`var zero ∈̇ con mₐ` 的内层真值恰是限制世界内的隶属 `⟪ A ⟫↪ m ∈ˢ ⟪ A ⟫↪ mₐ`。由于限制隶属由底层集合的外围隶属定义，这个原子确实选中 `⟪ A ⟫↪ mₐ` 的元素；剩下的工作只是证明呈现出的集合 `defSet (atom mₐ)` 等于那个元素。
<!--ja-->
この原子式への所属定理の特殊化は直接です。環境は単一のパラメータ `m` に固定されており、原子式の意味論により `var zero ∈̇ con mₐ` の内側の真理値は、制限された世界の中の所属 `⟪ A ⟫↪ m ∈ˢ ⟪ A ⟫↪ mₐ` にほかなりません。制限された所属は基礎となる集合の周囲の所属で定義されるので、この原子式は実際に `⟪ A ⟫↪ mₐ` の要素を選びます。残る仕事は、提示された集合 `defSet (atom mₐ)` がその要素と等しいことを示すことだけです。
<!--/-->

```agda
    atom-mem mₐ m = defSet-mem (atom mₐ) m

    defSet-atom≡ : (mₐ : ⟪ A ⟫) → defSet (atom mₐ) ≡ ⟪ A ⟫↪ mₐ
    defSet-atom≡ mₐ = extensionality (defSet (atom mₐ)) (⟪ A ⟫↪ mₐ) (sub₁ , sub₂)
      where
      sub₁ : ⟨ defSet (atom mₐ) ⊆ ⟪ A ⟫↪ mₐ ⟩
```

<!--en-->
The forward inclusion eliminates the truncated index of `y ∈ˢ defSet (atom mₐ)`: an index is a pair `(m , h)` of a member and a proof that the atom holds at it, plus the path `q` from the indexing map. By `atom-mem`, the proof `h` becomes membership `⟪ A ⟫↪ m ∈ˢ ⟪ A ⟫↪ mₐ` in the ambient sense, and `∈∈ₛ` converts it to a set-theoretic member of `⟪ A ⟫↪ mₐ`; transporting along `q` finishes. This mirrors the proof of `defSet⊆A` with the atom's meaning in place of the trivial containment in `A`.
<!--zh-->
正向包含消去 `y ∈ˢ defSet (atom mₐ)` 的截断索引：索引是一个对子 `(m , h)`，其中 `h` 证明原子在 `m` 处成立，再加上来自索引映射的路径 `q`。经 `atom-mem`，证明 `h` 变成环境意义下的隶属 `⟪ A ⟫↪ m ∈ˢ ⟪ A ⟫↪ mₐ`，`∈∈ₛ` 把它转换为 `⟪ A ⟫↪ mₐ` 的集合论成员；沿 `q` 搬运即完成。这与 `defSet⊆A` 的证明互为镜像，只是用原子的含义替代了平凡的「属于 `A`」。
<!--ja-->
順方向の包含は、`y ∈ˢ defSet (atom mₐ)` の切断された索引を消去します。索引は、メンバーと「原子式がそこで成り立つ」ことの証明 `h` の対 `(m , h)` であり、さらに索引写像からの経路 `q` を伴います。`atom-mem` により証明 `h` は周囲の意味での所属 `⟪ A ⟫↪ m ∈ˢ ⟪ A ⟫↪ mₐ` に変わり、`∈∈ₛ` がそれを `⟪ A ⟫↪ mₐ` の集合論的な要素へ変換します。`q` に沿った輸送で完成です。これは、平凡な「`A` への所属」の代わりに原子式の意味を置いた、`defSet⊆A` の証明の鏡像です。
<!--/-->

```agda
      sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ ⟪ A ⟫↪ mₐ))
        (λ { ((m , h) , q) →
          subst (λ v → ⟨ v ∈ₛ ⟪ A ⟫↪ mₐ ⟩) q
            (∈∈ₛ {a = ⟪ A ⟫↪ m} {b = ⟪ A ⟫↪ mₐ} .fst
              (subst ⟨_⟩ (atom-mem mₐ m) ∣ (m , h) , refl ∣₁)) })
```

<!--en-->
The reverse inclusion is where transitivity enters. Given `y ∈ˢ ⟪ A ⟫↪ mₐ`, unfold it to the ambient membership `y∈a`; transitivity of `A` states that a member of a member of `A` is again a member of `A`, applied here with the witness `mₐ-as` that `⟪ A ⟫↪ mₐ ∈ˢ A`. So `y ∈ˢ A`, and the fiber decomposition hands over an index `m` with `⟪ A ⟫↪ m ≡ y`, ready to be presented as an inhabitant of `defSet (atom mₐ)`.
<!--zh-->
反向包含是传递性登场之处。给定 `y ∈ˢ ⟪ A ⟫↪ mₐ`，展开为外围隶属 `y∈a`；`A` 的传递性说「`A` 的成员的成员仍是 `A` 的成员」，这里以见证 `mₐ-as` (即 `⟪ A ⟫↪ mₐ ∈ˢ A`) 施用。于是 `y ∈ˢ A`，纤维分解交出一个索引 `m`，满足 `⟪ A ⟫↪ m ≡ y`，随时可呈现为 `defSet (atom mₐ)` 的元素。
<!--ja-->
逆方向の包含は、推移性が登場する場所です。`y ∈ˢ ⟪ A ⟫↪ mₐ` が与えられれば、それを周囲の所属 `y∈a` に展開します。`A` の推移性は「`A` の要素の要素は再び `A` の要素」と言うもので、ここでは `⟪ A ⟫↪ mₐ ∈ˢ A` という証人 `mₐ-as` とともに適用されます。よって `y ∈ˢ A` となり、ファイバー分解は `⟪ A ⟫↪ m ≡ y` を満たす添字 `m` を渡し、`defSet (atom mₐ)` の要素として提示できます。
<!--/-->

```agda
        (∈∈ₛ {a = y} {b = defSet (atom mₐ)} .snd y∈ₛ)
      sub₂ : ⟨ ⟪ A ⟫↪ mₐ ⊆ defSet (atom mₐ) ⟩
      sub₂ y y∈ₛ =
        let y∈a     = ∈∈ₛ {a = y} {b = ⟪ A ⟫↪ mₐ} .snd y∈ₛ
            y∈A     = Atrans {x = ⟪ A ⟫↪ mₐ} {y = y} y∈a mₐ-as
```

<!--en-->
To conclude, the index `m` just obtained must actually satisfy the atom at itself. Transporting `y∈a` backwards along the fiber path puts membership inside `⟪ A ⟫↪ mₐ`, and `atom-mem`, read in the reverse direction via `sym`, converts that into a proof of `smallSat (atom mₐ) m`. The final transport along `q` lands in `defSet (atom mₐ)`. Both inclusions together give the equality of sets. Note how every transport here moves a *proof* along a path of sets or of propositions, never building new data.
<!--zh-->
收尾时，刚得到的索引 `m` 必须确实在自身处满足该原子。沿纤维路径反向搬运 `y∈a` 把隶属放进 `⟪ A ⟫↪ mₐ` 之内，`atom-mem` 经 `sym` 反向读出，把它转换为 `smallSat (atom mₐ) m` 的证明。最后沿 `q` 的搬运落在 `defSet (atom mₐ)` 中。两个包含合起来给出集合的相等。注意这里的每个移送都在沿集合或命题的路径搬运**证明**，从不制造新数据。
<!--ja-->
締めくくりに、得られた添字 `m` が実際に自身で原子式を満たすことを示します。ファイバーの経路に沿って `y∈a` を逆向きに輸送すると所属が `⟪ A ⟫↪ mₐ` の内側に入り、`atom-mem` を `sym` で逆向きに読んで、それが `smallSat (atom mₐ) m` の証明に変わります。最後の `q` に沿った輸送が `defSet (atom mₐ)` に着地します。両方の包含で、集合の等しさが得られます。ここでの輸送はどれも、集合や命題の経路に沿って**証明**を運ぶもので、新しいデータを作ることはありません。
<!--/-->

```agda
            (m , q) = ∈-asFiber {a = y} {b = A} y∈A
        in subst (λ v → ⟨ v ∈ₛ defSet (atom mₐ) ⟩) q
             (∈∈ₛ {a = ⟪ A ⟫↪ m} {b = defSet (atom mₐ)} .fst
               (subst ⟨_⟩ (sym (atom-mem mₐ m))
                 (subst (λ v → ⟨ v ∈ˢ ⟪ A ⟫↪ mₐ ⟩) (sym q) y∈a)))
```

<!--en-->
With the equality in hand, membership in `Def` is one truncation away. Given `a ∈ˢ A`, the fiber decomposition of that membership provides an index `mₐ` with `⟪ A ⟫↪ mₐ ≡ a`; since the fiber is data here, the pair can be opened with `let` and `mₐ` named.
<!--zh-->
有了这个等式，距 `Def` 的隶属只剩一次截断。给定 `a ∈ˢ A`，该隶属的纤维分解提供索引 `mₐ`，满足 `⟪ A ⟫↪ mₐ ≡ a`；由于此处纤维是数据，可以用 `let` 打开对子并命名 `mₐ`。
<!--ja-->
この等式が手に入れば、`Def` への所属まであと切断一つです。`a ∈ˢ A` が与えられれば、その所属のファイバー分解は `⟪ A ⟫↪ mₐ ≡ a` を満たす添字 `mₐ` を与えます。ここではファイバーがデータなので、`let` で対を開き `mₐ` に名前を付けられます。
<!--/-->

```agda
        where
        mₐ-as : ⟨ ⟪ A ⟫↪ mₐ ∈ˢ A ⟩
        mₐ-as = ∈∈ₛ {a = ⟪ A ⟫↪ mₐ} {b = A} .snd (∈ₛ⟪ A ⟫↪ mₐ)

    A⊆Def : (a : S) → ⟨ a ∈ˢ A ⟩ → ⟨ a ∈ˢ Def ⟩
    A⊆Def a a∈ =
```

<!--en-->
The element `defSet (atom mₐ)` of `Def` equals `⟪ A ⟫↪ mₐ`, and composing that equality with the fiber path `q` gives `defSet (atom mₐ) ≡ a`. Wrapping the pair of a formula and this equality in the truncation `∣_∣₁` produces exactly what membership in `Def` demands: a formula whose defined subset is `a`, merely. Thus every element of `A` survives into `Def`, and with the previous section the operator only refines.
<!--zh-->
`Def` 的元素 `defSet (atom mₐ)` 等于 `⟪ A ⟫↪ mₐ`，与纤维路径 `q` 复合得 `defSet (atom mₐ) ≡ a`。把「一个公式加上这条等式」用截断 `∣_∣₁` 包装，恰好给出 `Def` 的隶属所要求的：一个其定义出的子集为 `a` 的公式，仅仅存在。于是 `A` 的每个元素都进入 `Def`，结合上一节，该算子只作精化。
<!--ja-->
`Def` の要素 `defSet (atom mₐ)` は `⟪ A ⟫↪ mₐ` と等しく、その等しさとファイバーの経路 `q` を合成すれば `defSet (atom mₐ) ≡ a` が得られます。論理式とこの等式の対を切断 `∣_∣₁` で包むと、`Def` への所属が要求するもの、つまり定義した部分集合が `a` であるような論理式が「だけ」存在することが、ちょうど得られます。こうして `A` のすべての要素は `Def` に残り、前節と合わせて、この演算子は精化だけを行います。
<!--/-->

```agda
      let (mₐ , q) = ∈-asFiber {a = a} {b = A} a∈
      in ∣ atom mₐ , defSet-atom≡ mₐ ∙ q ∣₁
```

<!--en-->
### Definability read from outside

One consequence deserves its own name, because the constructible-stage proofs lean on it repeatedly. Membership in `defSet φ` is a statement of the *inner* world `(A, ∈)`, and the arguments to come are conducted in the ambient hierarchy. For a Δ₀ formula the two readings agree, which is the absoluteness theorem; what remains is bookkeeping, since absoluteness is stated over the members of the class while `defSet` is stated over the small index type. Relabelling closes that gap, and the whole proof is a three-step path: the specification of `defSet`, then the relabelling of the formula, then absoluteness.

`A` must be transitive for this, which is why the lemma lives in this submodule; every stage of the tower is.
<!--zh-->
### 从外部读可定义性

有一条推论值得单独命名，因为可构造层的证明要反复倚重它。属于 `defSet φ` 是**内层**世界 `(A, ∈)` 中的陈述，而接下来的论证都在外围层级进行。对 Δ₀ 公式，两种读法一致，这就是绝对性定理；其余的只是层级核对，因为绝对性对类的成员陈述，而 `defSet` 对小索引类型陈述。重标正是为了消除这道层级差异，整个证明分三步：`defSet` 的规格、公式的重标、然后绝对性。

这需要 `A` 传递，故本引理归入这个子模块；塔的每层都传递。
<!--ja-->
### 外部から読む定義可能性

名前を与える価値のある帰結が一つあります。構成可能性の段階の証明はこれに繰り返し依拠するからです。`defSet φ` への所属は**内側**の世界 `(A, ∈)` での命題ですが、これからの議論は周囲の階層で行われます。Δ₀ 論理式については二つの読みが一致します。これが絶対性定理です。絶対性はクラスの要素について述べられる一方、`defSet` は小さな索引型について述べられるので、残るのはそのずれの処理だけです。定数の改名がこのずれを埋め、証明全体は三段階の経路になります。`defSet` の仕様、論理式の改名、そして絶対性です。

このためには `A` が推移的でなければならず、だからこそこの補題はこのこの議論に置かれています。階層のどの段階も推移的です。
<!--/-->

<!--en-->
The absoluteness module is instantiated at the ambient structure, the class `M`, and the transitivity hypothesis, yielding the restricted structure `Abs.𝒮M`, the outer satisfaction `Abs.⊨ᵛ`, and the Δ₀ absoluteness `Abs.abs₀`. The statement takes a witness `d` certifying that `φ` is Δ₀, and asserts a path of propositions: membership of `⟪ A ⟫↪ m` in `defSet φ` equals the satisfaction of `mapFo ι φ` in the *ambient* structure at the environment `⟪ A ⟫↪ m ∷ []`. The formula on the right has its constants mapped through `ι`, so it is a formula over the ambient carrier naming members of `A`.
<!--zh-->
绝对性模块在外围结构、类 `M` 与传递性前提上实例化，得到限制结构 `Abs.𝒮M`、外层满足 `Abs.⊨ᵛ` 与 Δ₀ 绝对性 `Abs.abs₀`。该陈述取一条证明 `φ` 是 Δ₀ 的见证 `d`，并断言命题之间的路径：`⟪ A ⟫↪ m` 属于 `defSet φ` 这一命题，等于公式 `mapFo ι φ` 在**外围**结构中于环境 `⟪ A ⟫↪ m ∷ []` 处的满足。右边的公式把常元经 `ι` 映射，因而是外围载体上的、指称 `A` 成员的公式。
<!--ja-->
絶対性のモジュールは、周囲の構造、クラス `M`、推移性の仮定の上で具体化され、制限された構造 `Abs.𝒮M`、外側の充足 `Abs.⊨ᵛ`、そして Δ₀ 絶対性 `Abs.abs₀` を与えます。この命題は、`φ` が Δ₀ であることを証明する証拠 `d` を取り、命題としての経路を主張します。`⟪ A ⟫↪ m` が `defSet φ` に属するという命題は、論理式 `mapFo ι φ` が**周囲**の構造で環境 `⟪ A ⟫↪ m ∷ []` のもとで充足されることと等しいのです。右辺の論理式は定数を `ι` を通して写すので、`A` の要素を名指す、周囲の台の上の論理式になります。
<!--/-->

```agda
    module Abs = FOL.Absoluteness.Single 𝒮ᵥ M Atrans

    abs-defSet : (φ : Formula ⟪ A ⟫ 1) → Δ₀ φ → (m : ⟪ A ⟫)
               → (⟪ A ⟫↪ m ∈ˢ defSet φ)
                 ≡ ((⟪ A ⟫↪ m ∷ []) Abs.⊨ᵛ (mapFo ι φ))
    abs-defSet φ d m =
```

<!--en-->
The proof concatenates three paths. First, `defSet-mem` reads membership in the definable subset as inner satisfaction of `φ` at `ι m`. Second, `⊨-map` (in the symmetric direction, hence `sym`) says that relabelling the constants through `ι` does not change the truth value, because `ι` is precisely the constant interpretation of the inner world; what remains is inner satisfaction of the relabelled formula `mapFo ι φ`. Third, `abs₀` transports inner satisfaction of that Δ₀ formula to outer satisfaction in the ambient structure, this being the only step that uses transitivity. The result lets later chapters treat membership in a definable subset as an ambient, not merely inner, statement.
<!--zh-->
证明复合三条路径。第一，`defSet-mem` 把可定义子集中的隶属读作 `φ` 在 `ι m` 处的内层满足。第二，`⊨-map` (取对称方向，故有 `sym`) 说经 `ι` 改名常元不改变真值，因为 `ι` 恰是内层世界的常元解释；剩下的是改名后公式 `mapFo ι φ` 的内层满足。第三，`abs₀` 把这条 Δ₀ 公式的内层满足搬运为外围结构中的外层满足，这也是唯一用到传递性的一步。此结果让后续章节可以把可定义子集中的隶属当作环境层面的陈述，而不只是内层陈述。
<!--ja-->
証明は三つの経路を連結します。第一に、`defSet-mem` は定義可能部分集合への所属を、`ι m` における `φ` の内側の充足として読みます。第二に、`⊨-map` (対称の方向なので `sym`) は、定数を `ι` を通して改名しても真理値が変わらないと言います。`ι` が内側の世界の定数の解釈にほかならないからです。残るのは、改名された論理式 `mapFo ι φ` の内側の充足です。第三に、`abs₀` がその Δ₀ 論理式の内側の充足を、周囲の構造での外側の充足へ輸送します。推移性を使うのはこの一段階だけです。この結果により、後の章は定義可能部分集合への所属を、内側だけではなく周囲の命題として扱えます。
<!--/-->

```agda
        defSet-mem φ m
      ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) Abs.𝒮M ι id φ (ι m ∷ []))
      ∙ Abs.abs₀ (mapΔ₀ ι d) (ι m ∷ [])
```

<!--en-->
## Recap

`Def A` is the set of subsets of `A` definable in the inner world `(A, ∈)` with parameters from `A`: syntax as index set, inner satisfaction for meaning, and essential smallness supplying the required universe level. The specification `defSet-mem`{.Agda} states directly what "definable" means, and the operator only refines: `A ⊆ Def A` under transitivity (`A⊆Def`{.Agda}), and members of `Def A` are subsets of `A` (`Def∋⊆A`{.Agda}). The next chapter iterates this step into a universe.
<!--zh-->
## 小结

`Def A` 是内层世界 `(A, ∈)` 中由带 `A` 中参数的公式定义出的 `A` 的子集之集：语法充作索引集，内层满足给出含义，本质小性保证所需的宇宙层级。规格 `defSet-mem`{.Agda} 直接陈述「可定义」的含义，而算子只作精化：传递性下 `A ⊆ Def A` (`A⊆Def`{.Agda})，且 `Def A` 的成员都是 `A` 的子集 (`Def∋⊆A`{.Agda})。下一章把这一步迭代成一个宇宙。
<!--ja-->
## まとめ

`Def A` は、内側の世界 `(A, ∈)` で `A` からのパラメータ付きの論理式によって定義される `A` の部分集合の集合です。構文が索引集合として働き、内側の充足が意味を与え、本質的小ささが必要な宇宙レベルを賄います。仕様 `defSet-mem`{.Agda} は「定義可能」の意味を直接述べ、この演算子は精化だけを行います。推移性の下では `A ⊆ Def A` (`A⊆Def`{.Agda}) であり、`Def A` の要素は `A` の部分集合です (`Def∋⊆A`{.Agda})。次の章はこの一歩を宇宙へと反復します。
<!--/-->

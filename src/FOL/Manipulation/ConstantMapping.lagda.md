<!--en-->
# Mapping constants

A function between constant domains acts on first-order syntax by replacing every constant symbol and leaving every variable untouched. This chapter defines that action on terms and formulas, proves that it respects composition, and specializes the formula map to carry parameter-free formulas, whose constant domain is the empty type, into formulas over any constant domain.
<!--zh-->
# 映射常元

常元域之间的函数作用于一阶语法的方式是：替换每个常元符号，而保持每个变量不变。本章在词项与公式上定义这个作用，证明它与复合相容，并把公式映射特殊化：以空类型为常元域的无参公式可由此进入任意常元域上的公式。
<!--ja-->
# 定数の写像

定数域の間の関数は、各定数記号を置き換え、変数をそのままにすることで一階の構文に作用します。本章では項と論理式に対するこの作用を定義して合成との両立を証明し、さらに論理式の写像を特殊化して、定数域が空型である無パラメータ論理式を任意の定数域上の論理式へ移します。
<!--/-->

<!--en-->
A formula such as `var 0 ∈̇ con k` names two things in two different ways: `var 0` refers through the free variables, while `con k` refers through the constant domain, some type `K`. Now suppose we are given a function `f : K → K'`. What should the relabelled formula look like? The natural answer is that only the constant moves: `con k` becomes `con (f k)`, while the variable, the membership relation, and the overall shape of the formula stay exactly as they were. This chapter defines that relabelling on terms and then on formulas, working with the types `Term` and `Formula` from the syntax chapter and their full stock of constructors: the atomic relations `_∈̇_` and `_≐_`, the connectives, and the quantifiers including the bounded forms `∀̇∈` and `∃̇∈`.
<!--zh-->
取公式 `var 0 ∈̇ con k` 这样的例子，它用两种方式指称两个对象：`var 0` 经自由变量指称，`con k` 则经常元域指称，这个常元域是某个类型 `K`。现在给定函数 `f : K → K'`，改名后的公式应当是什么样？自然的回答是：只有常元移动。`con k` 变为 `con (f k)`，而变量、属于关系与公式的整体形状保持原样。本章先在词项上、再在公式上定义这种改名，所用的类型 `Term` 与 `Formula` 及其全部构造子来自语法章：原子关系 `_∈̇_` 与 `_≐_`，联结词，以及包括有界形式 `∀̇∈`、`∃̇∈` 在内的量词。
<!--ja-->
`var 0 ∈̇ con k` という論理式は、二つの対象を二つの仕方で指しています。`var 0` は自由変数を経由し、`con k` は定数域、つまりある型 `K` を経由して指すのです。ここで関数 `f : K → K'` が与えられたとき、改名後の論理式はどんな形になるべきでしょうか。自然な答えは、動くのは定数だけ、というものです。`con k` は `con (f k)` になり、変数・所属関係・論理式全体の形はそのまま保たれます。本章ではまず項の上で、次に論理式の上でこの改名を定義します。使うのは構文の章の型 `Term` と `Formula` とそのすべての構成子、すなわち原子関係 `_∈̇_` と `_≐_`、論理結合子、そして束縛形式 `∀̇∈` と `∃̇∈` を含む量化子です。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.Manipulation.ConstantMapping where

open import Base.Prelude
open import FOL.Syntax using
  ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
```

<!--en-->
One special choice of domain will deserve its own attention: the empty type `⊥*`. A formula whose constant domain is `⊥*` contains no constants at all, and the end of this chapter studies how such formulas map into formulas over any `K`. Until then, everything takes place for an arbitrary function between constant domains.
<!--zh-->
有一种特殊的常元域值得单独注意：空类型 `⊥*`。常元域为 `⊥*` 的公式根本不含常元，本章末尾将研究这类公式如何映入任意 `K` 上的公式。在此之前，一切讨论都针对常元域之间的任意函数。
<!--ja-->
特別な定数域が一つ、後で独自に扱うことになります。空型 `⊥*` です。定数域が `⊥*` である論理式には定数がまったく現れず、本章の末尾では、そのような論理式が任意の `K` 上の論理式へどう写るかを扱います。それまでの議論は、定数域の間の任意の関数に対して行われます。
<!--/-->

```agda
import Cubical.Data.Empty as Empty
```

<!--en-->
## Syntax level

The syntax is functorial in its constant domain: a map `K → K'` pushes through a term or formula, relabelling constants while preserving de Bruijn variables and logical structure. This section defines that action; the composition law is proved in the next section.
<!--zh-->
## 语法层

语法对其常元域是函子式的：映射 `K → K'` 逐点穿过词项或公式，对常元改名，同时保持 de Bruijn 变量与逻辑结构不变。本节定义这个作用；复合法则在下一节证明。
<!--ja-->
## 構文への作用

構文は定数域に関して関手的です。写像 `K → K'` は項や論理式を通り抜けて定数だけを改名し、de Bruijn 変数と論理構造は保存します。本節ではこの作用を定義し、合成に関する法則は次節で証明します。
<!--/-->

<!--en-->
On terms the action leaves no room for choice. `mapTm` takes the relabelling function `f : K → K'` and a term of free-variable arity `n`, and returns a term of the same arity `n`: the constant `con k` becomes `con (f k)` and the variable `var i` is returned unchanged. This is a relabelling of constant symbols only; it is not substitution and has no effect on variables.
<!--zh-->
在词项上，这个作用没有别的选择。`mapTm` 取改名函数 `f : K → K'` 和自由变量个数为 `n` 的词项，返回的词项仍有同样的个数 `n`：常元 `con k` 变为 `con (f k)`，变量 `var i` 原样返回。这只是对常元符号的改名，不是代入，对变量也没有任何作用。
<!--ja-->
項に対する作用には選びようがありません。`mapTm` は改名関数 `f : K → K'` と自由変数の個数 `n` の項を受け取り、同じ個数 `n` の項を返します。定数 `con k` は `con (f k)` になり、変数 `var i` はそのまま返ります。これは定数記号の改名だけであり、代入ではなく、変数にはいかなる作用も持ちません。
<!--/-->

```agda
mapTm : ∀ {ℓ ℓ'} {K : Type ℓ} {K' : Type ℓ'} {n}
      → (K → K') → Term K n → Term K' n
mapTm f (con k) = con (f k)
mapTm f (var i) = var i

mapFo : ∀ {ℓ ℓ'} {K : Type ℓ} {K' : Type ℓ'} {n}
```

<!--en-->
An atomic formula shows how the action extends to formulas. The image of `t ∈̇ u` under `mapFo` is `mapTm f t ∈̇ mapTm f u`: the same relation applied to the two mapped terms, over the same arity `n`. So the running example `var 0 ∈̇ con k` maps to `var 0 ∈̇ con (f k)`, in which only the constant has moved.
<!--zh-->
原子公式显示了这一作用如何扩展到公式。`t ∈̇ u` 在 `mapFo` 下的像是 `mapTm f t ∈̇ mapTm f u`：同一关系施加于映射后的两个词项，自由变量个数仍是 `n`。于是我们的例子 `var 0 ∈̇ con k` 映为 `var 0 ∈̇ con (f k)`，其中只有常元移动了。
<!--ja-->
原子論理式が、この作用の論理式への拡張のされ方を示します。`t ∈̇ u` の `mapFo` による像は `mapTm f t ∈̇ mapTm f u` です。同じ関係が、写像後の二つの項に、同じ個数 `n` の上で施されます。したがって先の例 `var 0 ∈̇ con k` は `var 0 ∈̇ con (f k)` に写り、動くのは定数だけです。
<!--/-->

```agda
      → (K → K') → Formula K n → Formula K' n
mapFo f (t ∈̇ u)  = mapTm f t ∈̇ mapTm f u
mapFo f (t ≐ u)  = mapTm f t ≐ mapTm f u
mapFo f (φ ∧̇ ψ)  = mapFo f φ ∧̇ mapFo f ψ
mapFo f (φ ∨̇ ψ)  = mapFo f φ ∨̇ mapFo f ψ
```

<!--en-->
A quantified formula shows that logical structure is untouched. Under `mapFo`, a quantifier prefix is kept and its body, of arity `suc n`, is mapped recursively and returned with the same arity; each connective is rebuilt on the mapped subformulas. The operation neither adds nor removes a binder, and no constructor ever changes shape; falsity `⊥̇`, which carries no constant, maps to itself.
<!--zh-->
量化公式表明逻辑结构不受影响。在 `mapFo` 下，量词前缀保持不变，其自由变量个数为 `suc n` 的主体被递归映射，个数仍是 `suc n`；每个联结词在映射后的子公式上重建。该操作既不增加也不删除约束词，任何构造子的形状都不会改变；不含常元的假 `⊥̇` 映到自身。
<!--ja-->
量化された論理式は、論理構造が損なわれないことを示します。`mapFo` の下で、量化子の前置きはそのまま保たれ、自由変数の個数 `suc n` の本体は再帰的に写像されて同じ個数で返ります。各論理結合子は写像後の部分式の上で再構成されます。この操作は束縛子を増やしも減らしもせず、どの構成子も形を変えません。定数を含まない偽 `⊥̇` はそのまま写ります。
<!--/-->

```agda
mapFo f (φ ⇒̇ ψ)  = mapFo f φ ⇒̇ mapFo f ψ
mapFo f ⊥̇        = ⊥̇
mapFo f (∃̇ φ)    = ∃̇ mapFo f φ
mapFo f (∀̇ φ)    = ∀̇ mapFo f φ
mapFo f (∀̇∈ t φ) = ∀̇∈ (mapTm f t) (mapFo f φ)
```

<!--en-->
The bounded quantifiers `∀̇∈` and `∃̇∈` are the case where both operations meet, since they combine a term with a formula: the bounding term `t` is relabelled by `mapTm` and the body by `mapFo`. With this, `mapFo` transforms syntax only; it never interprets a formula or touches an environment.
<!--zh-->
有界量词 `∀̇∈` 与 `∃̇∈` 是两种操作相遇的情形，因为它们同时结合词项与公式：约束词项 `t` 用 `mapTm` 改名，主体用 `mapFo` 映射。至此，`mapFo` 只变换语法，从不解释公式，也不触及环境。
<!--ja-->
有界量化子 `∀̇∈` と `∃̇∈` は、項と論理式を併せ持つため、両方の操作が一度に現れる場合です。束縛する項 `t` は `mapTm` で改名され、本体は `mapFo` で写像されます。これにより `mapFo` は構文だけを変換し、論理式を解釈したり環境に触れたりすることは決してありません。
<!--/-->

```agda
mapFo f (∃̇∈ t φ) = ∃̇∈ (mapTm f t) (mapFo f φ)
```

<!--en-->
Two such maps in a row are one map: mapping by `f` and then by `g` agrees, as a path, with mapping once by `λ k → g (f k)`. This functoriality of the constant-domain action is what later chapters use to collapse an intermediate constant domain, and it belongs to the syntax level rather than to any one application.
<!--zh-->
连着两次这样的映射就是一次映射：先按 `f` 再按 `g` 映射，与按 `λ k → g (f k)` 一次映射，作为路径相等。常元域作用的这条函子性正是后续各章用来消去中间常元域的依据，它属于语法层，而不专属于任何一个应用。
<!--ja-->
二つの写像を続けて施すことは一つの写像と同じです。`f` で写してから `g` で写すことは、`λ k → g (f k)` による一度の写像とパスとして一致します。定数域への作用のこの関手性は、後の章が中間の定数域を消去するのに使うものであり、構文の水準に属する法則です。
<!--/-->

<!--en-->
The composition law is a commuting square. If a term is mapped first along `f : K → K'` and then along `g : K' → K''`, the result should agree with mapping it once along the composite `λ k → g (f k)`. `mapTm-comp` states exactly this, as a path in `Term K'' n`. On a constant, both sides compute to `con (g (f k))`, so the agreement already holds as definitional equality and `refl` proves the case; on a variable no constant occurs, so the two sides are again the same term.
<!--zh-->
复合法则是一个交换方阵。若一个词项先沿 `f : K → K'` 映射，再沿 `g : K' → K''` 映射，结果应当与沿复合函数 `λ k → g (f k)` 一次映射相一致。`mapTm-comp` 正是把这一点陈述为 `Term K'' n` 中的路径。在常元上，两边都计算为 `con (g (f k))`，一致已是定义等式，故该情形由 `refl` 证明；在变量上不出现常元，两边又是同一个词项。
<!--ja-->
合成法則は可換な正方形として述べられます。項をまず `f : K → K'` で写し、次に `g : K' → K''` で写すなら、その結果は合成 `λ k → g (f k)` による一度の写像と一致するはずです。`mapTm-comp` はまさにこれを `Term K'' n` のパスとして述べます。定数の場合、両辺はともに `con (g (f k))` まで計算され、一致はすでに定義的等式として成り立つので、この場合は `refl` で証明できます。変数の場合は定数が現れないため、両辺は再び同じ項です。
<!--/-->

```agda
mapTm-comp : ∀ {ℓ ℓ' ℓ''} {K : Type ℓ} {K' : Type ℓ'} {K'' : Type ℓ''} {n}
             (f : K → K') (g : K' → K'') (t : Term K n)
           → mapTm g (mapTm f t) ≡ mapTm (λ k → g (f k)) t
mapTm-comp f g (con k) = refl
mapTm-comp f g (var i) = refl
```

<!--en-->
For formulas the same square is stated by `mapFo-comp`: the two routes around the square, `mapFo g (mapFo f φ)` and `mapFo (λ k → g (f k)) φ`, are paths of the same type `Formula K'' n`. Since the square is already proved for terms, the atomic cases need no new argument on terms: congruence `cong₂` lifts the two term paths into a path between the rebuilt atoms.
<!--zh-->
对公式，同一个方阵由 `mapFo-comp` 陈述：沿方阵两条路线的结果 `mapFo g (mapFo f φ)` 与 `mapFo (λ k → g (f k)) φ`，是同一类型 `Formula K'' n` 中的路径。由于方阵在词项上已证，原子情形无需对词项另作论证：同余 `cong₂` 把两条词项路径提升为重建的原子之间的路径。
<!--ja-->
論理式に対しては、同じ正方形が `mapFo-comp` によって述べられます。正方形の二つの経路、すなわち `mapFo g (mapFo f φ)` と `mapFo (λ k → g (f k)) φ` は、同じ型 `Formula K'' n` のパスです。正方形は項に対してすでに証明されているので、原子論理式の場合に項について新たな議論は要りません。合同 `cong₂` が二つの項のパスを、再構成された原子の間のパスへ持ち上げます。
<!--/-->

```agda

mapFo-comp : ∀ {ℓ ℓ' ℓ''} {K : Type ℓ} {K' : Type ℓ'} {K'' : Type ℓ''} {n}
             (f : K → K') (g : K' → K'') (φ : Formula K n)
           → mapFo g (mapFo f φ) ≡ mapFo (λ k → g (f k)) φ
mapFo-comp f g (t ∈̇ u)  = cong₂ _∈̇_ (mapTm-comp f g t) (mapTm-comp f g u)
mapFo-comp f g (t ≐ u)  = cong₂ _≐_ (mapTm-comp f g t) (mapTm-comp f g u)
```

<!--en-->
Structural recursion propagates the square through the connectives: each subformula carries its own instance, and congruence rebuilds the connective on the two subformula paths. Falsity `⊥̇` contains neither constants nor subformulas, so both routes compute to the same formula and the case is `refl`.
<!--zh-->
结构递归使方阵穿过联结词：每个子公式各携带方阵的一个实例，同余在两条子公式路径上重建联结词。假 `⊥̇` 既不含常元也不含子公式，两条路线都计算为同一公式，该情形就是 `refl`。
<!--ja-->
構造的な再帰によって正方形は論理結合子を通り抜けます。各部分式が正方形の自らのインスタンスを持ち、合同が二つの部分式のパスの上で結合子を再構成します。偽 `⊥̇` は定数も部分式も含まないため、両経路は同じ論理式まで計算され、この場合は `refl` です。
<!--/-->

```agda
mapFo-comp f g (φ ∧̇ ψ)  = cong₂ _∧̇_ (mapFo-comp f g φ) (mapFo-comp f g ψ)
mapFo-comp f g (φ ∨̇ ψ)  = cong₂ _∨̇_ (mapFo-comp f g φ) (mapFo-comp f g ψ)
mapFo-comp f g (φ ⇒̇ ψ)  = cong₂ _⇒̇_ (mapFo-comp f g φ) (mapFo-comp f g ψ)
mapFo-comp f g ⊥̇        = refl
mapFo-comp f g (∃̇ φ)    = cong ∃̇_ (mapFo-comp f g φ)
```

<!--en-->
The quantifier cases close the induction: a prefix quantifier applies to one subformula, while the bounded forms `∀̇∈` and `∃̇∈` pair a term with a body and use both the term path and the body path. Since every constructor of `Formula` is covered, the composition square commutes for every formula. This functoriality is a purely syntactic fact, available wherever later chapters need to collapse an intermediate constant domain.
<!--zh-->
量词情形结束归纳：前缀量词只作用于一个子公式，而有界形式 `∀̇∈` 与 `∃̇∈` 把词项与主体配对，同时用到词项路径与主体路径。由于 `Formula` 的每个构造子都已覆盖，复合法则方阵对每个公式成立。这条函子性是纯语法的事实，后续各章凡需消去中间常元域，皆可取用。
<!--ja-->
量化子の場合で帰納が閉じます。前置量化子は一つの部分式に作用し、有界形式 `∀̇∈` と `∃̇∈` は項と本体を対にするので、項のパスと本体のパスの両方が使われます。`Formula` のすべての構成子が扱われたため、合成の正方形はすべての論理式で可換になります。この関手性は純粋に構文的な事実であり、後の章が中間の定数域を消去する必要が生じたときはいつでも利用できます。
<!--/-->

```agda
mapFo-comp f g (∀̇ φ)    = cong ∀̇_ (mapFo-comp f g φ)
mapFo-comp f g (∀̇∈ t φ) = cong₂ ∀̇∈ (mapTm-comp f g t) (mapFo-comp f g φ)
mapFo-comp f g (∃̇∈ t φ) = cong₂ ∃̇∈ (mapTm-comp f g t) (mapFo-comp f g φ)
```

<!--en-->
The most frequently used instance of the map enters a constant domain from **no** constants. The syntax chapter introduced the **parameter-free formulas**, whose constant domain is the empty type; like sentences they have no separate name, and the type `Formula (⊥* {ℓ}) n` expresses the full definition: a formula of this type contains no constant nodes at all, but may still use any of its `n` available free-variable slots. Relabelling into a type `K` requires a function `⊥* → K`, and the empty type is exactly the type for which such a function exists uniquely, with no case to define: there is no constant to send anywhere. This is what the eliminator `Empty.rec*` provides, and relabelling along it maps parameter-free formulas into formulas over any domain.
<!--zh-->
这个映射最常用的实例从**没有**常元的域进入常元域。语法章介绍过**无参公式**，其常元域是空类型；类型 `Formula (⊥* {ℓ}) n` 已把定义说尽：这种类型的公式根本不含常元节点，但仍可使用其 `n` 个自由变量槽位中的任意一些。要改名进入类型 `K`，需要一个函数 `⊥* → K`，而空型正是这种函数唯一存在、且无需定义任何分支的类型：没有任何常元需要送往别处。这正是消去子 `Empty.rec*` 所提供的；沿它改名，就把无参公式映入任意常元域上的公式。
<!--ja-->
この写像のよく使われる例は、定数を**一切持たない**定数域から任意の定数域への移行です。**無パラメータ論理式**の定数域は空型であり、型 `Formula (⊥* {ℓ}) n` がその条件を表します。この型の論理式には定数の節がまったく現れませんが、`n` 個の自由変数のスロットはどれでも使えます。型 `K` への改名には関数 `⊥* → K` が必要ですが、空型はまさにそのような関数が唯一つ、定義すべき場合分けもなく存在する型です。どこにも送るべき定数がないからです。これを提供するのが消去子 `Empty.rec*` であり、これに沿って定数を改名すると、無パラメータ論理式を任意の定数域上の論理式へ写せます。
<!--/-->

<!--en-->
`embed` is exactly `mapFo Empty.rec*`: the unique function `⊥* → K` from the empty constant alphabet is used as the relabelling, so every constant position, of which there are none, is sent somewhere. What changes is the constant domain alone: the free-variable context of length `n` and the binders are untouched, so `embed` neither closes the formula nor supplies an environment for its variables.
<!--zh-->
`embed` 正是 `mapFo Empty.rec*`：从空常元字母表出发的函数 `⊥* → K` 是唯一的，直接取它作改名，于是所有常元位置 (其实一个也没有) 都被送往某处。改变的只是常元域：长度为 `n` 的自由变量上下文与约束词都不变，因此 `embed` 既不封闭公式，也不为其中的变量提供环境。
<!--ja-->
`embed` はまさに `mapFo Empty.rec*` です。空の定数アルファベットからの関数 `⊥* → K` は唯一なので、それをそのまま改名に用います。するとすべての定数の位置 (実際には一つもありません) がどこかに送られます。変わるのは定数域だけです。長さ `n` の自由変数の文脈と束縛子はそのままなので、`embed` は論理式を閉じたり変数への環境を与えたりするものではありません。
<!--/-->

```agda
embed : ∀ {ℓ ℓ'} {K : Type ℓ'} {n} → Formula (⊥* {ℓ}) n → Formula K n
embed = mapFo Empty.rec*
```

<!--en-->
## Recap

`mapTm` and `mapFo` express the syntax-level action of a map of constant domains: constants are relabelled, variables, binders and arities are untouched. `mapFo-comp` proves this action is functorial under composition, and `embed` is the parameter-free instance, the basis for later constant relabelling and parameter abstraction.
<!--zh-->
## 小结

`mapTm` 与 `mapFo` 表达常元域映射在语法层的作用：常元被改名，变量、约束词与个数均不变。`mapFo-comp` 证明该作用对复合是函子性的；`embed` 是无参实例，是后续常元改名与参数抽象的基础。
<!--ja-->
## まとめ

`mapTm` と `mapFo` は、定数域の写像が構文の水準で行う作用を表します。定数は改名され、変数・束縛子・個数はそのままです。`mapFo-comp` はこの作用が合成に関して関手的であることを証明し、`embed` は無パラメータの場合の例で、後の定数の改名とパラメータ抽象化の基礎になります。
<!--/-->

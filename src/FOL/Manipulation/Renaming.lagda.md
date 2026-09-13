<!--en-->
# Variable renaming

A map between finite variable contexts acts on terms and formulas by renaming free variables while leaving constants fixed. The accompanying agreement relation on environments gives one semantic theorem that covers weakening, exchange, and contraction.

The syntax chapter pointed out an absence: no substitution, no weakening. The quantifier clauses take bodies in an extended context directly, so the classical apparatus for moving variables around is unnecessary. What little variable motion the book does need is covered by one device: **renaming**, a map `ρ : Fin n → Fin m` pushed through a formula, with a single correctness theorem that handles weakening, exchange, and contraction in one stroke.
<!--zh-->
# 变量改名

有限变量语境之间的映射通过改名自由变量作用于词项与公式，同时保持常元不变。环境上的相符关系给出一条语义定理，统一涵盖弱化、交换与收缩。

语法章提过一处缺席：没有替换，也没有弱化。量词子句直接取扩展语境中的公式体，因此经典的整套变量替换机制并无必要。本书确实需要的那一点变量调整，由一个操作完成：**改名**，即沿公式推送一个映射 `ρ : Fin n → Fin m`，并配一条正确性定理，弱化、交换、收缩都由此得出。
<!--ja-->
# 変数の改名

有限な変数文脈の間の写像は、定数を固定したまま自由変数を改名して項と論理式へ作用します。環境の一致関係を用いる一つの意味論的定理が、弱化、交換、縮約をまとめて扱います。

構文の章が指摘した欠落、つまり代入も弱化もないことには理由があります。量詞の節が拡張された文脈の本体を直接受け取るため、変数を動かすための古典的な仕組みは不要でした。本書が実際に必要とする変数の移動は一つの装置で賄えます。それが**改名**です。写像 `ρ : Fin n → Fin m` を論理式へ押し通し、弱化、交換、縮約を一つの正しさの定理で同時に扱います。
<!--/-->

<!--en-->
Suppose a formula has its free variables indexed by `n` slots, and we want to view it in a context of `m` slots. A map `ρ : Fin n → Fin m` tells us where each variable goes, and renaming applies it to every free variable of the formula. The only complication is the quantifiers: their bodies live in a context with one extra slot, so `ρ` must be extended beneath each binder in a way that leaves the bound variable alone.
<!--zh-->
设想一个公式，其自由变量由 `n` 个槽位索引，而我们想在 `m` 个槽位的语境中看待它。映射 `ρ : Fin n → Fin m` 告诉我们每个变量去向何处，改名就是把这一映射作用到公式的每个自由变量上。唯一的复杂之处在量词：量词体活在多出一个槽位的语境中，因此 `ρ` 必须在每个约束子之下以不惊动被约束变量的方式扩展。
<!--ja-->
公式の自由変数が `n` 個のスロットで索引づけられているとき、それを `m` 個のスロットの文脈で捉えたい場面を考えます。写像 `ρ : Fin n → Fin m` が各変数の行き先を決め、改名とはこの写像を公式のすべての自由変数に作用させることです。難所は量詞です。量詞の本体はスロットを一つ余分に持つ文脈で生きるので、`ρ` を束縛変数を乱さないように各束縛子の下で拡張する必要があります。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.Manipulation.Renaming where

open import Base.Prelude
open import FOL.ZFStructure using ( ZFStructure )
```

<!--en-->
One correctness theorem then measures renaming: under a suitable relation between the old and new environments, the renamed formula denotes the same proposition as the original. Since the proposition is computed in an arbitrary proposition-valued set-theoretic structure, the theorem has exactly the generality of satisfaction itself, and the usual structural rules of sequent practice, weakening, exchange, and contraction, all fall out as particular choices of `ρ`.
<!--zh-->
随后由一条正确性定理来衡量改名：在旧环境与新环境之间一个合适的关系之下，改名后的公式与原公式指称相同的命题。由于该命题是在任意命题值集合论结构中计算的，定理与满足关系本身具有完全相同的普遍性；而序列演算惯用的结构规则，弱化、交换、收缩，都作为 `ρ` 的特定选取由此得出。
<!--ja-->
そして改名は一つの正しさの定理で測られます。旧環境と新環境の間の適切な関係のもとで、改名された公式は元の公式と同じ命題を表します。命題は任意の命題値をとる任意の集合論的構造の上で計算されるので、定理は充足関係そのものとまったく同じ一般性を持ち、シーケント計算で慣用される構造規則、すなわち弱化、交換、縮約は、すべて `ρ` の特定の選択として得られます。
<!--/-->

```agda
open import FOL.Syntax using
  ( Term; con; var
  ; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Semantics
```

<!--en-->
## The syntactic layer

`renameTm`{.Agda} and `renameFo`{.Agda} push a map `Fin n → Fin m` through the syntax. Beneath a binder, `liftρ`{.Agda} fixes the newly bound variable and shifts the old variables through the given map.
<!--zh-->
## 语法层

`renameTm`{.Agda} 与 `renameFo`{.Agda} 将映射 `Fin n → Fin m` 贯穿语法。在约束子之下，`liftρ`{.Agda} 固定新约束的变量，并通过给定映射移动原有变量。
<!--ja-->
## 構文の水準

`renameTm`{.Agda} と `renameFo`{.Agda} は写像 `Fin n → Fin m` を構文へ通します。束縛子の下では、`liftρ`{.Agda} が新しく束縛された変数を固定し、元の変数を与えられた写像で移します。
<!--/-->

<!--en-->
Take a formula with a free variable under a bounded quantifier, say `∀̇∈ x₀ (var 1 ∈̇ var 0)` in a context of two slots: the bound variable is slot 0 of the body, and slot 1 of the body is the free variable 0 of the outside. A renaming `ρ : Fin n → Fin m` moves the outside variables; under the binder we need a map on `Fin (suc n) → Fin (suc m)` that sends the bound slot 0 to slot 0 and sends each old slot `suc i` to `suc (ρ i)`. That extension is `liftρ ρ`, and it guarantees the bound variable is never disturbed.
<!--zh-->
取一个在有界量词之下含自由变量的公式，例如双槽位语境中的 `∀̇∈ x₀ (var 1 ∈̇ var 0)`：被约束变量是公式体的第零槽位，而公式体的第 1 槽位正是外层的自由变量 0。改名 `ρ : Fin n → Fin m` 移动外层变量；在约束子之下，我们需要 `Fin (suc n) → Fin (suc m)` 上的一个映射，把被约束的第零槽位送到第零槽位，并把每个旧槽位 `suc i` 送到 `suc (ρ i)`。这一扩展就是 `liftρ ρ`，它保证被约束变量从不被扰动。
<!--ja-->
有界量詞の下に自由変数を持つ公式を取りましょう。たとえば二つのスロットの文脈における `∀̇∈ x₀ (var 1 ∈̇ var 0)` です。束縛変数は本体のスロット 0 であり、本体のスロット 1 は外側の自由変数 0 にあたります。改名 `ρ : Fin n → Fin m` は外側の変数を動かしますが、束縛子の下では `Fin (suc n) → Fin (suc m)` 上の写像、つまり束縛されたスロット 0 をスロット 0 へ送り、各旧スロット `suc i` を `suc (ρ i)` へ送るものが必要になります。この拡張が `liftρ ρ` であり、束縛変数が決して乱されないことを保証します。
<!--/-->

```agda
liftρ : ∀ {n m} → (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
liftρ ρ zero    = zero
liftρ ρ (suc i) = suc (ρ i)
```

<!--en-->
With the lifting in hand, renaming extends to terms and then to formulas by structural recursion. The type of `renameTm` states the whole idea: a term with `n` free-variable slots becomes a term with `m` slots. A constant `con k` names no free variable at all, so it passes through unchanged; constants belong to the alphabet, not to the context, and their interpretation is a separate matter. The only other term form is a variable, where `ρ` finally acts.
<!--zh-->
有了提升，改名便可对词项、再对公式做结构递归地扩展。`renameTm` 的类型已经说出全部想法：含 `n` 个自由变量槽位的词项变为含 `m` 个槽位的词项。常元 `con k` 完全不指名任何自由变量，因此原样通过；常元属于字母表而非语境，其解释是另一回事。词项仅剩的另一种形式是变量，`ρ` 在此才真正起作用。
<!--ja-->
持ち上げが手に入れば、改名は項へ、さらに公式へと構造的再帰で拡張できます。`renameTm` の型が考えのすべてを述べています。`n` 個の自由変数スロットを持つ項が `m` 個のスロットを持つ項になるのです。定数 `con k` は自由変数をまったく名指さないのでそのまま通ります。定数は文脈ではなくアルファベットに属し、その解釈は別の問題です。項のもう一つの形式である変数において、初めて `ρ` が実際に働きます。
<!--/-->

```agda

renameTm : ∀ {ℓc} {K : Type ℓc} {n m} → (Fin n → Fin m) → Term K n → Term K m
renameTm ρ (con k) = con k
```

<!--en-->
For formulas the pattern continues: `renameFo` has the same shape, turning a formula over `n` slots into one over `m`. The atomic clauses rename their term arguments, so in our example `var 1 ∈̇ var 0` under the outer map becomes `var (ρ 1) ∈̇ var (ρ 0)` as far as the outside slots are concerned. The propositional connectives and falsity carry no variables of their own and are rebuilt recursively from the renamed subformulas.
<!--zh-->
公式的模式相同：`renameFo` 形状一致，把 `n` 个槽位上的公式变为 `m` 个槽位上的公式。两条原子子句对其词项参数改名，因此在我们的例子中，就外层槽位而言 `var 1 ∈̇ var 0` 变为 `var (ρ 1) ∈̇ var (ρ 0)`。命题联结词与假值自身不带变量，由改名后的子公式递归重建。
<!--ja-->
公式でも同じ流れです。`renameFo` は同じ形をし、`n` 個のスロット上の公式を `m` 個のスロット上の公式へ変えます。原子の節は項の引数を改名するので、例の公式では、外側のスロットにかぎれば `var 1 ∈̇ var 0` は `var (ρ 1) ∈̇ var (ρ 0)` になります。命題結合子と偽はそれ自身は変数を持たず、改名された部分公式から再帰的に組み立て直されます。
<!--/-->

```agda
renameTm ρ (var i) = var (ρ i)

renameFo : ∀ {ℓc} {K : Type ℓc} {n m} → (Fin n → Fin m) → Formula K n → Formula K m
renameFo ρ (t ∈̇ u)  = renameTm ρ t ∈̇ renameTm ρ u
renameFo ρ (t ≐ u)  = renameTm ρ t ≐ renameTm ρ u
renameFo ρ (φ ∧̇ ψ)  = renameFo ρ φ ∧̇ renameFo ρ ψ
```

<!--en-->
The plain quantifiers are the first place where the recursive call changes: since the body lives in the extended context, the call passes `liftρ ρ` rather than `ρ`. This is exactly the discipline we described for the example: the bound slot stays at zero, and the outside renaming reaches the body only in shifted form.
<!--zh-->
普通量词是递归调用首次改变的地方：公式体活在扩展语境中，因此递归调用传入的是 `liftρ ρ` 而非 `ρ`。这正是我们为例子描述的规则：被约束的槽位保持在第零位，外层改名只以移位后的形式到达公式体。
<!--ja-->
通常の量詞は、再帰呼び出しが初めて変わる場所です。本体は拡張された文脈に住むので、呼び出しには `ρ` ではなく `liftρ ρ` が渡されます。これは例で述べた規則そのものです。束縛スロットはゼロに留まり、外側の改名は移された形でのみ本体に届きます。
<!--/-->

```agda
renameFo ρ (φ ∨̇ ψ)  = renameFo ρ φ ∨̇ renameFo ρ ψ
renameFo ρ (φ ⇒̇ ψ)  = renameFo ρ φ ⇒̇ renameFo ρ ψ
renameFo ρ ⊥̇        = ⊥̇
renameFo ρ (∃̇ φ)    = ∃̇ renameFo (liftρ ρ) φ
renameFo ρ (∀̇ φ)    = ∀̇ renameFo (liftρ ρ) φ
```

<!--en-->
The bounded quantifiers use both maps at once, and our example sits exactly here. For `∀̇∈ t φ`, the bound `t` lives in the outer context and is renamed with `ρ`, while the body `φ` is renamed with `liftρ ρ`. So `∀̇∈ x₀ (var 1 ∈̇ var 0)` under `ρ` becomes `∀̇∈ (renamed bound) (var (suc (ρ 0)) ∈̇ var 0)`: the reference to free variable 0 follows the renaming through its shift, and the bound occurrence of slot 0 is untouched. The syntactic layer is now complete; the next section asks whether the result means the same as what we started with.
<!--zh-->
有界量词同时使用两个映射，我们的例子恰好落在这里。对 `∀̇∈ t φ`，界限 `t` 住在外层语境，用 `ρ` 改名；公式体 `φ` 用 `liftρ ρ` 改名。于是 `∀̇∈ x₀ (var 1 ∈̇ var 0)` 在 `ρ` 之下变为 `∀̇∈ (改名后的界限) (var (suc (ρ 0)) ∈̇ var 0)`：对自由变量 0 的引用随移位跟随改名，而槽位 0 的被约束出现原封不动。语法层至此完成；下一节追问结果是否与我们出发的公式含义相同。
<!--ja-->
有界量詞は二つの写像を同時に使います。例の公式はまさにここにあります。`∀̇∈ t φ` では、限界 `t` は外側の文脈に住むので `ρ` で改名され、本体 `φ` は `liftρ ρ` で改名されます。したがって `ρ` の下で `∀̇∈ x₀ (var 1 ∈̇ var 0)` は `∀̇∈ (改名された限界) (var (suc (ρ 0)) ∈̇ var 0)` になります。自由変数 0 への言及は移動に従って改名を追い、スロット 0 の束縛された出現はそのままです。これで構文の水準は完成です。次の節は、結果が最初の公式と同じ意味を持つかを問います。
<!--/-->

```agda
renameFo ρ (∀̇∈ t φ) = ∀̇∈ (renameTm ρ t) (renameFo (liftρ ρ) φ)
renameFo ρ (∃̇∈ t φ) = ∃̇∈ (renameTm ρ t) (renameFo (liftρ ρ) φ)
```

<!--en-->
## The semantic layer

`Agrees ρ γ δ`{.Agda} says that the two environments assign equal values to variables related by `ρ`. This condition survives extension beneath a binder, and structural induction then proves equal term denotations and equal satisfaction for renamed formulas.
<!--zh-->
## 语义层

`Agrees ρ γ δ`{.Agda} 表示两个环境给经 `ρ` 对应的变量指派相等的取值。该条件在约束子下扩展环境时仍保持，结构归纳遂证明改名后词项释义与公式满足关系相等。
<!--ja-->
## 意味論の水準

`Agrees ρ γ δ`{.Agda} は、`ρ` で対応する変数に二つの環境が等しい値を割り当てることを表します。この条件は束縛子の下で環境を拡張しても保たれ、構造帰納法によって改名後の項の表示と論理式の充足関係が等しいと分かります。
<!--/-->

<!--en-->
Syntax alone cannot say whether a renaming preserves meaning; we need to compare environments. An environment is a vector of elements of the structure's carrier, of length matching the context: `γ : S ^ m` for the big context, `δ : S ^ n` for the small one. The question becomes: when do `γ` and `δ` count as the same assignment from the point of view of `ρ`?
<!--zh-->
仅靠语法无法判断改名是否保持含义；我们需要比较环境。环境是结构载体的元素构成的向量，长度与语境匹配：大语境用 `γ : S ^ m`，小语境用 `δ : S ^ n`。问题于是变成：从 `ρ` 的角度看，`γ` 与 `δ` 何时算是同一个指派？
<!--ja-->
構文だけでは改名が意味を保つかを言えず、環境を比較する必要があります。環境は構造の台の要素からなるベクトルで、長さは文脈と一致します。大きい文脈には `γ : S ^ m`、小さい文脈には `δ : S ^ n` です。問いはこう変わります。`ρ` の視点から、`γ` と `δ` はいつ同じ割り当てとみなせるのか。
<!--/-->

```agda
module Sat {ℓ} (𝒮 : ZFStructure ℓ)
           {ℓc} {K : Type ℓc} (ι : K → ZFStructure.S 𝒮) where

  open ZFStructure 𝒮

  private module Sem = FOL.Semantics 𝒮
```

<!--en-->
The answer is the relation `Agrees ρ γ δ`: for every index `i` of the small context, `δ` at `i` and `γ` at `ρ i` must be equal elements, the equality being a path in the carrier. Note the direction of the lookup: `ρ` goes from the small context to the big one, so `δ` assigns to `i` exactly what `γ` assigns to `ρ i`. In our running example with `n = 2`, agreement on the variable `1` of the body reads `lookup (ρ 0) γ ≡ lookup 1 δ`, that is, the big environment must match the small one at the image position.
<!--zh-->
答案就是关系 `Agrees ρ γ δ`：对小语境的每个索引 `i`，`δ` 在 `i` 处与 `γ` 在 `ρ i` 处必须取相等的元素，该相等是载体中的路径。注意查找的方向：`ρ` 从小语境走向大语境，因此 `δ` 在 `i` 处指派的正是 `γ` 在 `ρ i` 处指派的。在我们 `n = 2` 的运行例子中，公式体变量 `1` 上的相符读作 `lookup (ρ 0) γ ≡ lookup 1 δ`，即大环境必须在像的位置与小环境匹配。
<!--ja-->
答えが関係 `Agrees ρ γ δ` です。小さい文脈の各索引 `i` について、`δ` の `i` での値と `γ` の `ρ i` での値が台におけるパスとして等しくなければなりません。参照の向きに注意してください。`ρ` は小さい文脈から大きい文脈へ向かうので、`δ` が `i` に割り当てるのは `γ` が `ρ i` に割り当てる値とちょうど同じです。`n = 2` の例では、本体の変数 `1` での一致は `lookup (ρ 0) γ ≡ lookup 1 δ` と読めます。つまり大きい環境は像の位置で小さい環境と一致しなければなりません。
<!--/-->

```agda
  open Sem using ( _^_ )
  open Sem.At K ι using ( _⊨_; ⟦_⟧ )

  Agrees : ∀ {n m} → (Fin n → Fin m) → S ^ m → S ^ n → Type ℓ
  Agrees ρ γ δ = ∀ i → lookup (ρ i) γ ≡ lookup i δ
```

<!--en-->
The correctness theorem: a renamed formula in the big environment means the same as the original in the small one. Terms first, then the usual induction, every case a congruence, the binder cases stepping through `agrees∷`{.Agda}. Weakening (inserting an unused variable), exchange, and contraction are all instances, obtained by choosing `ρ`.
<!--zh-->
正确性定理：变换后的公式在大环境中的含义，与原公式在小环境中的相同。先处理词项，然后照例归纳，每个情形是一条同余，约束子情形依赖 `agrees∷`{.Agda}。弱化 (插入未用的变量)、交换、收缩都是特例，取相应的 `ρ` 即得。
<!--ja-->
正しさの定理：改名された論理式の大きい環境における意味は、元の論理式の小さい環境における意味と同じです。まず項から始め、いつもの帰納法に進みます。各場合は同余性であり、束縛子の場合は `agrees∷`{.Agda} を経由します。弱化 (使われない変数の挿入)、交換、縮約はすべて特殊例で、`ρ` を選ぶことによって得られます。
<!--/-->

<!--en-->
The theorem will go by induction on the formula, so agreement must survive the step under a quantifier. It does: if both environments are extended with the same element `x` at position zero, then `x ∷ γ` and `x ∷ δ` agree under `liftρ ρ`. At index zero both sides read `x` by computation, and at index `suc i` the demand reduces to the old `ag i`. This lemma `agrees∷` is the semantic counterpart of the syntactic lifting.
<!--zh-->
定理将对公式做归纳，因此相符关系必须在量词之下这一步仍然成立。事实如此：若两个环境都在第零位添加同一元素 `x`，则 `x ∷ γ` 与 `x ∷ δ` 在 `liftρ ρ` 之下相符。索引零处两边经计算都读出 `x`；索引 `suc i` 处的要求归约为原有的 `ag i`。引理 `agrees∷` 是语法提升在语义上的对应物。
<!--ja-->
定理は公式の帰納法で進むので、一致関係は量詞の下の一歩を生き延びなければなりません。実際に生き延びます。両方の環境に位置ゼロで同じ要素 `x` を加えると、`x ∷ γ` と `x ∷ δ` は `liftρ ρ` の下で一致します。索引ゼロでは計算から両辺とも `x` を読み、索引 `suc i` での要求は既存の `ag i` に帰着します。この補題 `agrees∷` は、構文の持ち上げに対応する意味論上の対応物です。
<!--/-->

```agda
  agrees∷ : ∀ {n m} {ρ : Fin n → Fin m} {γ : S ^ m} {δ : S ^ n}
            (x : S) → Agrees ρ γ δ → Agrees (liftρ ρ) (x ∷ γ) (x ∷ δ)
  agrees∷ x ag zero    = refl
  agrees∷ x ag (suc i) = ag i
```

<!--en-->
Everything now rests on the two theorems. For terms: evaluating `renameTm ρ t` in the big environment `γ` gives a path to evaluating `t` in the small environment `δ`, provided `γ` and `δ` agree under `ρ`. For formulas the analogous statement compares propositions of satisfaction. The hypothesis `Agrees ρ γ δ` is what makes the claim substantive: without any relation between the environments, no equality of denotations could hold.
<!--zh-->
一切都落在两条定理上。对词项：在环境 `γ` 与 `δ` 于 `ρ` 之下相符的前提下，在大环境中求值 `renameTm ρ t` 得到一条到在小环境中求值 `t` 的路径。对公式，类似的陈述比较满足关系的命题。前提 `Agrees ρ γ δ` 正是使断言有实质内容的条件：环境之间没有任何关系时，指称的相等无从谈起。
<!--ja-->
すべては二つの定理にかかっています。項については、`γ` と `δ` が `ρ` の下で一致するという仮定のもとで、大きい環境 `γ` で `renameTm ρ t` を評価したものは、小さい環境 `δ` で `t` を評価したものへのパスになります。公式では同様の主張が充足の命題を比較します。仮定 `Agrees ρ γ δ` が主張に実質を与えます。環境の間に何の関係もなければ、表示の等しいことは成り立ちようがありません。
<!--/-->

```agda

  ⟦⟧-rename : ∀ {n m} (ρ : Fin n → Fin m) (t : Term K n)
```

<!--en-->
The term proof is short because there is so little to a term. A constant denotes `ι k` independently of the environment, so the two evaluations are the same by `refl`. A variable `var i` denotes `lookup i δ` on the small side and `lookup (ρ i) γ` on the big side, and agreement at index `i` is exactly the path between them, so `ag i` closes the case. The real content is one level up, in the formula theorem.
<!--zh-->
词项的证明很短，因为词项本身内容很少。常元的释义 `ι k` 与环境无关，两次求值经 `refl` 相同。变量 `var i` 在小侧释义为 `lookup i δ`，在大侧释义为 `lookup (ρ i) γ`，而索引 `i` 处的相符恰是二者之间的路径，故 `ag i` 了结此情形。真正的内容在上一层的公式定理中。
<!--ja-->
項の証明は短い。項の中身が少ないからです。定数は環境に依存せず `ι k` を表すので、二つの評価は `refl` で同じです。変数 `var i` は小さい側では `lookup i δ`、大きい側では `lookup (ρ i) γ` を表し、索引 `i` での一致がまさに両者をつなぐパスなので、`ag i` がこの場合を閉じます。本質は一つ上の公式の定理にあります。
<!--/-->

```agda
              (γ : S ^ m) (δ : S ^ n) → Agrees ρ γ δ
            → ⟦ renameTm ρ t ⟧ γ ≡ ⟦ t ⟧ δ
  ⟦⟧-rename ρ (con k) γ δ ag = refl
  ⟦⟧-rename ρ (var i) γ δ ag = ag i

  ⊨-rename : ∀ {n m} (ρ : Fin n → Fin m) (φ : Formula K n)
```

<!--en-->
The formula theorem states a path between two propositions: `γ ⊨ renameFo ρ φ` on the big side, `δ ⊨ φ` on the small side. Consider first the bounded quantifier of our example, whose body contains no further binder; the other cases follow the same two patterns, congruence or recursion, which we describe here. For an atomic formula, the term theorem gives paths between the denotations of the renamed and original terms, and `cong₂` transports those paths through membership or equality of sets. Likewise each connective case applies `cong₂` to the corresponding logical operation, and falsity needs only `refl`.
<!--zh-->
公式定理陈述两个命题之间的路径：大侧的 `γ ⊨ renameFo ρ φ`，小侧的 `δ ⊨ φ`。先看我们例子中的有界量词，其公式体不含更深的约束子；其余情形遵循同样的两种模式，同余或递归，在此一并描述。对原子公式，词项定理给出改名词项与原词项释义之间的路径，`cong₂` 把这些路径经过集合的属于或相等传输过去。联结词情形同样对相应的逻辑运算用 `cong₂`，假值只需 `refl`。
<!--ja-->
公式の定理は二つの命題の間のパスを述べます。大きい側の `γ ⊨ renameFo ρ φ` と、小さい側の `δ ⊨ φ` です。まず例の有界量詞を考えます。その本体にはさらに束縛子がありません。残りの場合はここで述べる同余と再帰という二つの型のどちらかに従います。原子公式では、項の定理が改名された項と元の項の表示の間のパスを与え、`cong₂` がそのパスを集合の所属関係や等号を通して運びます。結合子の場合も対応する論理演算に `cong₂` を使い、偽は `refl` で足ります。
<!--/-->

```agda
             (γ : S ^ m) (δ : S ^ n) → Agrees ρ γ δ
           → (γ ⊨ renameFo ρ φ) ≡ (δ ⊨ φ)
  ⊨-rename ρ (t ∈̇ u)  γ δ ag = cong₂ _∈ˢ_ (⟦⟧-rename ρ t γ δ ag) (⟦⟧-rename ρ u γ δ ag)
  ⊨-rename ρ (t ≐ u)  γ δ ag = cong₂ _≈ˢ_ (⟦⟧-rename ρ t γ δ ag) (⟦⟧-rename ρ u γ δ ag)
  ⊨-rename ρ (φ ∧̇ ψ)  γ δ ag = cong₂ _⊓_ (⊨-rename ρ φ γ δ ag) (⊨-rename ρ ψ γ δ ag)
```

<!--en-->
Under the unbounded existential `∃̇ φ`, satisfaction quantifies over all candidate elements `x` of the carrier, so the proof must show that the functions of `x` on the two sides are pointwise equal, which is where `funExt` enters. At each `x` the two environments are the extensions `x ∷ γ` and `x ∷ δ`, and by `agrees∷ x ag` they agree under `liftρ ρ`, which is precisely the induction hypothesis at the smaller formula. This is the point of the whole design: agreement was built to survive extension, so the recursive call goes through unchanged.
<!--zh-->
在无界存在量词 `∃̇ φ` 之下，满足关系遍历载体的所有候选元素 `x`，因此证明须说明两侧关于 `x` 的函数逐点相等，`funExt` 正在此处登场。在每个 `x` 处，两侧环境是扩展 `x ∷ γ` 与 `x ∷ δ`，由 `agrees∷ x ag` 它们在 `liftρ ρ` 之下相符，而这恰是较小公式处的归纳假设。这正是整体设计的关键：相符关系本就为在扩展下存活而构造，递归调用因此畅通无阻。
<!--ja-->
無制限の存在量詞 `∃̇ φ` の下では、充足は台のすべての候補要素 `x` を渡るので、証明は両側の `x` の関数が各点で等しいことを示さねばならず、ここで `funExt` が登場します。各 `x` で両側の環境は拡張 `x ∷ γ` と `x ∷ δ` であり、`agrees∷ x ag` により `liftρ ρ` の下で一致します。これは小さい公式での帰納法の仮定にほかなりません。ここが設計全体の要点です。一致関係は拡張の下で保たれるように作られているので、再帰呼び出しがそのまま通ります。
<!--/-->

```agda
  ⊨-rename ρ (φ ∨̇ ψ)  γ δ ag = cong₂ _⊔_ (⊨-rename ρ φ γ δ ag) (⊨-rename ρ ψ γ δ ag)
  ⊨-rename ρ (φ ⇒̇ ψ)  γ δ ag = cong₂ _⇒_ (⊨-rename ρ φ γ δ ag) (⊨-rename ρ ψ γ δ ag)
  ⊨-rename ρ ⊥̇        γ δ ag = refl
  ⊨-rename ρ (∃̇ φ)    γ δ ag = cong (⋁ S) (funExt (λ x →
    ⊨-rename (liftρ ρ) φ (x ∷ γ) (x ∷ δ) (agrees∷ x ag)))
```

<!--en-->
The unbounded universal `∀̇ φ` is the dual, using `⋀` in place of `⋁` with the same `funExt` and `agrees∷` steps. The bounded universal `∀̇∈ t φ` combines the two ingredients: satisfaction is `⋀` over `x` of the implication from `x ∈ˢ ⟦ t ⟧ γ` to the body's satisfaction. The bound contributes a `cong` through `x ∈ˢ_` fed by the term theorem, and the body contributes the recursive call at `liftρ ρ`; `cong₂ _⇒_` welds them into the required path between implications.
<!--zh-->
无界全称量词 `∀̇ φ` 是对偶情形，用 `⋀` 替代 `⋁`，`funExt` 与 `agrees∷` 的步骤相同。有界全称量词 `∀̇∈ t φ` 把两种成分结合起来：其满足是对 `x` 的 `⋀`，从 `x ∈ˢ ⟦ t ⟧ γ` 到公式体满足的蕴涵。界限贡献一个经 `x ∈ˢ_` 的 `cong`，由词项定理提供；公式体贡献在 `liftρ ρ` 处的递归调用；`cong₂ _⇒_` 把二者焊成蕴涵之间所需的路径。
<!--ja-->
非有界な全称量化子 `∀̇ φ` は双対で、`⋁` の代わりに `⋀` を使い、`funExt` と `agrees∷` の手順は同じです。有界全称量詞 `∀̇∈ t φ` は二つの材料を組み合わせます。その充足は、`x ∈ˢ ⟦ t ⟧ γ` から本体の充足への含意についての `x` に対する `⋀` です。限界は項の定理が供給する `x ∈ˢ_` を通る `cong` を寄与し、本体は `liftρ ρ` での再帰呼び出しを寄与し、`cong₂ _⇒_` が両者を含意の間の求めるパスへ接合します。
<!--/-->

```agda
  ⊨-rename ρ (∀̇ φ)    γ δ ag = cong (⋀ S) (funExt (λ x →
    ⊨-rename (liftρ ρ) φ (x ∷ γ) (x ∷ δ) (agrees∷ x ag)))
  ⊨-rename ρ (∀̇∈ t φ) γ δ ag = cong (⋀ S) (funExt (λ x →
    cong₂ _⇒_ (cong (x ∈ˢ_) (⟦⟧-rename ρ t γ δ ag))
              (⊨-rename (liftρ ρ) φ (x ∷ γ) (x ∷ δ) (agrees∷ x ag))))
```

<!--en-->
The bounded existential `∃̇∈ t φ` closes the induction in the mirror image: `⋁ S` over `x`, the renamed bound `x ∈ˢ ⟦ t ⟧ γ` joined to the body satisfaction by `⊓`, and the same recursive call through `agrees∷`. Notice what was never used: injectivity of `ρ`. The theorem is stated for an arbitrary map `Fin n → Fin m`, so collapsing two variables onto one, as in contraction, is as admissible as spacing them out, as in weakening, or reordering them, as in exchange.
<!--zh-->
有界存在量词 `∃̇∈ t φ` 以镜像结束归纳：对 `x` 的 `⋁ S`，改名后的界限 `x ∈ˢ ⟦ t ⟧ γ` 经 `⊓` 与公式体满足相接，以及经 `agrees∷` 的同一递归调用。注意什么从未被用到：`ρ` 的单射性。定理对任意映射 `Fin n → Fin m` 陈述，因此把两个变量收缩到一处，如收缩；把变量拉开间距，如弱化；或调换次序，如交换；都是同样可采纳的。
<!--ja-->
有界存在量詞 `∃̇∈ t φ` が鏡像の形で帰納を閉じます。`x` に対する `⋁ S`、改名された限界 `x ∈ˢ ⟦ t ⟧ γ` を `⊓` で本体の充足に結び、`agrees∷` を経る同じ再帰呼び出しです。決して使われなかったものに注目してください。`ρ` の単射性です。定理は任意の写像 `Fin n → Fin m` に対して述べられているので、二つの変数を一つへ畳み込むこと (縮約) も、変数を間隔を空けて並べること (弱化) も、順序を入れ替えること (交換) も、同じく許されます。
<!--/-->

```agda
  ⊨-rename ρ (∃̇∈ t φ) γ δ ag = cong (⋁ S) (funExt (λ x →
    cong₂ _⊓_ (cong (x ∈ˢ_) (⟦⟧-rename ρ t γ δ ag))
              (⊨-rename (liftρ ρ) φ (x ∷ γ) (x ∷ δ) (agrees∷ x ag))))
```

<!--en-->
## Recap

Variable renaming consists of the syntactic maps, environment agreement, and the theorem `⊨-rename`{.Agda}. Choosing the context map specializes this single interface to weakening, exchange, or contraction.
<!--zh-->
## 小结

变量改名由语法映射、环境相符关系与定理 `⊨-rename`{.Agda} 组成。选择不同语境映射，即可将这一统一接口特化为弱化、交换或收缩。
<!--ja-->
## まとめ

変数の改名は、構文写像、環境の一致、定理 `⊨-rename`{.Agda} からなります。文脈の写像を選ぶことで、この一つのインターフェースを弱化、交換、縮約へ特殊化できます。
<!--/-->

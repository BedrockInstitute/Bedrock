<!--en-->
# Constant relabelling

A first-order formula carries constant symbols from some domain `K`, but the symbols themselves are inert: only the interpretation function decides what they denote. This chapter studies what happens when a function `f : K → K'` renames every constant symbol, an action written `mapFo f`. Two questions are answered. First, does the meaning survive the renaming, in the precise sense that satisfaction under `ι` after renaming coincides with satisfaction under the composite interpretation `ι ∘ f` before renaming? Second, does the syntactic classification of a formula in the Lévy hierarchy survive, so that the Δ₀ witness, and more generally the Σₙ/Πₙ witness, can be transported along `f`? Both answers are yes, and both proofs are structural, mirroring the constructors of the syntax.
<!--zh-->
# 常元改名

一阶公式携带着来自某个常元域 `K` 的常元符号，但符号本身是惰性的：决定它们所指的只有解释函数。本章研究当一个函数 `f : K → K'` 改写每个常元符号时会发生什么，这一作用记作 `mapFo f`。这里回答两个问题。其一，含义是否在改名后幸存，精确地说：改名后在 `ι` 下的满足，是否等同于改名前在复合解释 `ι ∘ f` 下的满足？其二，公式在 Lévy 层级中的语法分类是否幸存，即 Δ₀ 见证以及更一般的 Σₙ/Πₙ 见证能否沿 `f` 搬运？两个答案都是肯定的，而且两个证明都是结构性的，与语法的构造子一一对应。
<!--ja-->
# 定数の改名

一階の論理式はある定数域 `K` からの定数記号を運びますが、記号そのものは不活性です。記号が何を指すかを決めるのは解釈関数だけです。この章では、関数 `f : K → K'` がすべての定数記号を改名するとき何が起こるかを調べます。この作用は `mapFo f` と書かれます。ここで答える問いは二つです。第一に、改名後の `ι` の下での充足が、改名前の合成解釈 `ι ∘ f` の下での充足と一致するという精密な意味で、意味は改名を生き延びるのか。第二に、Lévy 階層における論理式の構文的分類は生き延びるのか、すなわち Δ₀ の証人、より一般に Σₙ/Πₙ の証人は `f` に沿って運べるのか。答えはいずれも「はい」であり、両方の証明は構文の構成子に対応する構成的なものです。
<!--/-->

<!--en-->
Take a formula over a constant domain `K` and rename its constants along a function `f : K → K'`. What the formula says then depends on which interpretation reads it: the target interpretation `ι : K' → S`, applied to the renamed formula, or the composite `ι ∘ f`, applied to the original. The semantic half of this chapter asks whether these two readings always agree, and the syntactic half asks whether a formula's classification in the Lévy hierarchy survives the renaming. Both are proved by structural induction, mirroring the constructors of the syntax.
<!--zh-->
取一个定义在常元域 `K` 上的公式，沿函数 `f : K → K'` 改名它的常元。这个公式说什么，取决于哪个解释来读它：是目标解释 `ι : K' → S` 作用于改名后的公式，还是复合解释 `ι ∘ f` 作用于原公式。本章的语义一半问这两种读法是否总是一致，语法一半问公式在 Lévy 层级中的分类是否在改名下幸存。两个答案都由结构归纳给出，与语法的构造子一一对应。
<!--ja-->
定数域 `K` 上の論理式を取り、その定数を関数 `f : K → K'` に沿って改名してみます。論理式が何を述べるかは、どの解釈がそれを読むかで決まります。目標の解釈 `ι : K' → S` を改名後の論理式に適用するか、合成 `ι ∘ f` を元の論理式に適用するかです。本章の意味論的な半分は、この二つの読み方が常に一致するかを問い、構文論的な半分は、Lévy 階層における論理式の分類が改名を生き延びるかを問います。いずれも構文の構成子に対応する構造帰納法で示されます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.Manipulation.Relabelling where

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
```

<!--en-->
The action under study is written `mapTm f` on terms and `mapFo f` on formulas: a function `f : K → K'` relabels each constant `con k` to `con (f k)` and leaves every variable untouched. Because it acts on constants only, every connective and every quantifier, bounded or unbounded, keeps its exact position, which is the reason the Lévy classification should survive. The classification itself is given by inductive witnesses: an inhabitant of `Δ₀ φ` is explicit data certifying that every quantifier in `φ` is bounded, one constructor per permitted shape, and `Σₙ k φ` and `Πₙ k φ` record the alternating unbounded blocks.
<!--zh-->
被研究的作用在词项上记作 `mapTm f`，在公式上记作 `mapFo f`：函数 `f : K → K'` 把每个常元 `con k` 改名为 `con (f k)`，并让每个变量原样不动。由于它只作用于常元，每个联结词与每个量词 (无论有界与否) 都保持原位，这正是 Lévy 分类应当幸存的原因。分类本身以归纳见证给出：`Δ₀ φ` 的一个元素是显式数据，证明 `φ` 中每个量词都有界，每个获准的形状对应一个构造子；`Σₙ k φ` 与 `Πₙ k φ` 则记录交替的无界块。
<!--ja-->
問題の作用は、項には `mapTm f`、論理式には `mapFo f` と書かれます。関数 `f : K → K'` は各定数 `con k` を `con (f k)` へ改名し、変数はそのまま残します。定数にだけ作用するため、すべての結合子とすべての量化子 (有界かどうかにかかわらず) は元の位置を保ち、これが Lévy 分類が生き延びるはずだと期待できる理由です。分類そのものは帰納的な証人で与えられます。`Δ₀ φ` の元は `φ` のすべての量化子が有界であることを証明する明示的なデータであり、許容される形ごとに一つの構成子を持ち、`Σₙ k φ` と `Πₙ k φ` は交互に現れる非有界の列を記録します。
<!--/-->

```agda
open import FOL.Syntax using
  ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.ConstantMapping using ( mapTm; mapFo; embed )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-⊥; δ-∀∈; δ-∃∈
```

<!--en-->
On the semantic side, a structure `𝒮` with carrier `S` reads a formula over `K` through an interpretation `ι : K → S`, yielding a satisfaction relation `_⊨_` and term evaluation `⟦_⟧`. The two readings to be compared therefore share the same syntax but differ in interpretation, and the proofs below keep them apart by carrying both side by side.
<!--zh-->
在语义一侧，带载体 `S` 的结构 `𝒮` 经解释 `ι : K → S` 来读 `K` 上的公式，得到满足关系 `_⊨_` 与词项求值 `⟦_⟧`。因此待比较的两种读法共享同一语法，差别只在解释；下面的证明让二者并排出现，以保持区分。
<!--ja-->
意味論の側では、台 `S` を持つ構造 `𝒮` が解釈 `ι : K → S` を通して `K` 上の論理式を読み、充足関係 `_⊨_` と項の評価 `⟦_⟧` を与えます。したがって比較すべき二つの読み方は同じ構文を共有し、解釈だけが異なります。以下の証明では、両者を並行して扱いながら区別を保ちます。
<!--/-->

```agda
  ; Σₙ; σ-Δ₀; σ-Π; σ-∃; Πₙ; π-Δ₀; π-Σ; π-∀ )
import FOL.Semantics
import Cubical.Data.Empty as Empty
```

<!--en-->
## Meaning level

Renaming constants is a purely syntactic operation, so one must check that it does not disturb meaning. The precise statement is a commutation: for any map of constant domains `f : K → K'` and any interpretation `ι : K' → S` of the target domain, evaluating a relabelled formula under `ι` gives the same truth value as evaluating the original formula under the composite interpretation `ι ∘ f`. The proof runs by structural induction, with the base case supplied by term evaluation and the congruence lemmas of the truth algebra doing the rest.
<!--zh-->
## 含义层

常元改名是纯语法操作，因此必须检查它不扰动含义。精确的陈述是一条交换律：对任意常元域映射 `f : K → K'` 与目标域的任意解释 `ι : K' → S`，改名后的公式在 `ι` 下的求值，与原公式在复合解释 `ι ∘ f` 下的求值给出相同的真值。证明按结构归纳进行：基底情形由词项求值提供，其余由真值代数的同余引理完成。
<!--ja-->
## 意味の水準

定数の改名は純粋に構文的な操作なので、意味を乱さないことを確認しなければなりません。正確な主張は可換性です。任意の定数域の写像 `f : K → K'` と対象域の任意の解釈 `ι : K' → S` に対し、改名後の論理式を `ι` の下で評価した真理値は、元の論理式を合成解釈 `ι ∘ f` の下で評価した真理値と一致します。証明は構造帰納法で進み、基底の場合は項の評価が担い、残りは真理値代数の合同補題が担います。
<!--/-->

<!--en-->
Fix a truth algebra `𝕋`, a ZF structure `𝒮` over it with carrier `S`, a relabelling `f : K → K'`, and an interpretation `ι : K' → S` of the target domain. The composite `ι ∘ f` is an equally good interpretation of the source domain, so we have two readings of the same formulas: the renamed formula under `ι`, and the original under `ι ∘ f`. The commutation problem is whether these readings give equal truth values.
<!--zh-->
固定一个真值代数 `𝕋`、其上带载体 `S` 的 ZF 结构 `𝒮`、一个改名 `f : K → K'`，以及目标域的解释 `ι : K' → S`。复合 `ι ∘ f` 同样是源域的一个合格解释，于是同一批公式有了两种读法：改名后的公式在 `ι` 下，原公式在 `ι ∘ f` 下。交换问题就是问这两种读法是否给出相等的真值。
<!--ja-->
真理値代数 `𝕋`、その上の台 `S` を持つ ZF 構造 `𝒮`、改名 `f : K → K'`、そして対象域の解釈 `ι : K' → S` を固定します。合成 `ι ∘ f` は源の域の正当な解釈でもあるので、同じ論理式に二つの読み方が得られます。改名後の論理式を `ι` の下で読むか、元の論理式を `ι ∘ f` の下で読むかです。可換の問題とは、この二つの読み方が等しい真理値を与えるかを問うことです。
<!--/-->

```agda
module _ {ℓ ℓ'} (𝕋 : TruthAlgebra ℓ ℓ') (𝒮 : ZFStructure 𝕋) where

  open TruthAlgebra 𝕋
  open ZFStructure 𝒮
  open FOL.Semantics 𝕋 𝒮 using ( module At; _^_ )

  module _ {ℓc ℓd} {K : Type ℓc} {K' : Type ℓd} (f : K → K') (ι : K' → S) where
```

<!--en-->
The atomic case already shows why the two readings must agree. Consider the formula `t ∈̇ u`: the first reading evaluates it as `⟦ mapTm f t ⟧ γ ∈ˢ ⟦ mapTm f u ⟧ γ`, the second as `⟦ t ⟧∘ γ ∈ˢ ⟦ u ⟧∘ γ`. The term lemma `⟦⟧-map` gives `⟦ mapTm f t ⟧ γ ≡ ⟦ t ⟧∘ γ` for every term, and both of its cases hold by `refl`: a relabelled constant `con (f k)` evaluates to `ι (f k)`, which is exactly what the composite reading computes, and a variable ignores constants altogether.
<!--zh-->
原子情形已经显示了两种读法为何必须一致。考虑公式 `t ∈̇ u`：第一种读法把它求值为 `⟦ mapTm f t ⟧ γ ∈ˢ ⟦ mapTm f u ⟧ γ`，第二种读法求值为 `⟦ t ⟧∘ γ ∈ˢ ⟦ u ⟧∘ γ`。词项引理 `⟦⟧-map` 对每个词项给出 `⟦ mapTm f t ⟧ γ ≡ ⟦ t ⟧∘ γ`，其两种情形都由 `refl` 成立：改名后的常元 `con (f k)` 求值为 `ι (f k)`，这正是复合读法所计算的；而变量完全不涉及常元。
<!--ja-->
原子論理式の場合が、二つの読み方がなぜ一致しなければならないかをすでに示しています。論理式 `t ∈̇ u` を考えると、第一の読み方はこれを `⟦ mapTm f t ⟧ γ ∈ˢ ⟦ mapTm f u ⟧ γ` と評価し、第二の読み方は `⟦ t ⟧∘ γ ∈ˢ ⟦ u ⟧∘ γ` と評価します。項の補題 `⟦⟧-map` はすべての項に対して `⟦ mapTm f t ⟧ γ ≡ ⟦ t ⟧∘ γ` を与え、その二つの場合はどちらも `refl` で成立します。改名された定数 `con (f k)` の評価値は `ι (f k)` であり、これは合成の読み方が計算するものそのものだからです。変数は定数にまったく関与しません。
<!--/-->

```agda

    open At K' ι using ( _⊨_; ⟦_⟧ )
    open At K (λ k → ι (f k)) using () renaming ( _⊨_ to _⊨∘_ ; ⟦_⟧ to ⟦_⟧∘ )

    ⟦⟧-map : ∀ {n} (t : Term K n) (γ : S ^ n)
           → ⟦ mapTm f t ⟧ γ ≡ ⟦ t ⟧∘ γ
    ⟦⟧-map (con k) γ = refl
```

<!--en-->
The satisfaction lemma `⊨-map` lifts this agreement from terms to formulas, as paths in the truth algebra: `(γ ⊨ mapFo f φ) ≡ (γ ⊨∘ φ)`. For the atomic case `t ∈̇ u`, the two term paths from `⟦⟧-map` are fed into the membership relation by `cong₂ _∈ˢ_`, producing the path between the two readings of the statement. Equality atoms work identically through `≈ˢ`.
<!--zh-->
满足引理 `⊨-map` 把这一一致从词项提升到公式，得到真值代数中的路径：`(γ ⊨ mapFo f φ) ≡ (γ ⊨∘ φ)`。对原子情形 `t ∈̇ u`，来自 `⟦⟧-map` 的两条词项路径经 `cong₂ _∈ˢ_` 送入属于关系，产生该命题两种读法之间的路径。等号原子经 `≈ˢ` 完全同样地处理。
<!--ja-->
充足の補題 `⊨-map` はこの一致を項から論理式へ持ち上げ、真理値代数における経路 `(γ ⊨ mapFo f φ) ≡ (γ ⊨∘ φ)` を与えます。原子論理式 `t ∈̇ u` の場合は、`⟦⟧-map` からの二つの項の経路を `cong₂ _∈ˢ_` によって所属関係に入れ、この主張の二つの読み方の間の経路を作ります。等号の原子も `≈ˢ` を通じてまったく同様に扱われます。
<!--/-->

```agda
    ⟦⟧-map (var i) γ = refl

    ⊨-map : ∀ {n} (φ : Formula K n) (γ : S ^ n)
          → (γ ⊨ mapFo f φ) ≡ (γ ⊨∘ φ)
    ⊨-map (t ∈̇ u)  γ = cong₂ _∈ˢ_ (⟦⟧-map t γ) (⟦⟧-map u γ)
    ⊨-map (t ≐ u)  γ = cong₂ _≈ˢ_ (⟦⟧-map t γ) (⟦⟧-map u γ)
```

<!--en-->
The propositional connectives are handled by congruence as well, because the structure interprets them by the truth algebra's own operations: a path between the two readings of `φ` and one between the readings of `ψ` combine into a path for `φ ∧̇ ψ` through `⊓`, and similarly for disjunction and implication. Falsity `⊥̇` contains no constants at all, so its two readings are the same value and the path is `refl`.
<!--zh-->
命题联结词同样由同余处理，因为结构用真值代数自身的运算来解释它们：`φ` 的两种读法之间的一条路径与 `ψ` 的两条读法之间的一条路径，经 `⊓` 合成 `φ ∧̇ ψ` 的一条路径；析取与蕴涵同理。假 `⊥̇` 完全不含常元，其两种读法是同一个值，路径即 `refl`。
<!--ja-->
命題結合子も同様に合同で処理されます。構造はこれらを真理値代数自身の演算で解釈するからです。`φ` の二つの読み方の間の経路と `ψ` のそれとが、`⊓` を通して `φ ∧̇ ψ` の経路に合成され、選言や含意も同様です。偽 `⊥̇` は定数をまったく含まないので、二つの読み方は同じ値となり、経路は `refl` です。
<!--/-->

```agda
    ⊨-map (φ ∧̇ ψ)  γ = cong₂ _⊓_ (⊨-map φ γ) (⊨-map ψ γ)
    ⊨-map (φ ∨̇ ψ)  γ = cong₂ _⊔_ (⊨-map φ γ) (⊨-map ψ γ)
    ⊨-map (φ ⇒̇ ψ)  γ = cong₂ _⇒_ (⊨-map φ γ) (⊨-map ψ γ)
    ⊨-map ⊥̇        γ = refl
    ⊨-map (∃̇ φ)    γ = cong (⋁ S) (funExt (λ x → ⊨-map φ (x ∷ γ)))
```

<!--en-->
The quantifier cases are the only places where the environment changes, and it changes identically on both sides. Reading `∃̇ φ` under either interpretation joins over the carrier: for each element `x`, the bound variable is given the value `x` by extending the same environment to `x ∷ γ`. Since the environment extension is the same in both readings, the induction hypothesis `⊨-map φ (x ∷ γ)` applies unchanged, and `funExt` assembles these into a path between the joins. The bounded quantifiers combine this with the atomic pattern: each also produces a path in `x ∈ˢ ⟦ t ⟧ γ` from `⟦⟧-map`, fed through `⇒` or `⊓` by congruence. With these cases the commutation holds for every formula constructor, and the induction is complete.
<!--zh-->
量词情形是唯一环境发生变化的地方，而且两侧的变化完全相同。无论在哪个解释下读 `∃̇ φ`，都是在载体上取并：对每个元素 `x`，被约束变量通过把同一个环境扩张为 `x ∷ γ` 而取值 `x`。由于两种读法中的环境扩张一致，归纳假设 `⊨-map φ (x ∷ γ)` 原样适用，`funExt` 再把这些拼成并运算之间的路径。有界量词把这一点与原子模式结合：它们还要从 `⟦⟧-map` 产生 `x ∈ˢ ⟦ t ⟧ γ` 中的一条路径，经同余送入 `⇒` 或 `⊓`。补齐这些情形后，交换律对每个公式构造子都成立，归纳完成。
<!--ja-->
量化子の場合だけが環境が変わる箇所であり、しかも両側でまったく同じように変わります。どちらの解釈で `∃̇ φ` を読んでも、台の上の結びを取ることになります。各元 `x` に対し、束縛変数は同じ環境を `x ∷ γ` へ拡張することで値 `x` を得ます。環境の拡張が両読み方で一致するため、帰納法の仮定 `⊨-map φ (x ∷ γ)` がそのまま適用でき、`funExt` がこれらを結びの間の経路へ組み立てます。有界量化子はこれを原子論理式の型と結び付けます。`⟦⟧-map` から `x ∈ˢ ⟦ t ⟧ γ` 内の経路も作り、合同を通して `⇒` か `⊓` に入れます。これらの場合で、可換性はすべての論理式の構成子について成り立ち、帰納法は完了です。
<!--/-->

```agda
    ⊨-map (∀̇ φ)    γ = cong (⋀ S) (funExt (λ x → ⊨-map φ (x ∷ γ)))
    ⊨-map (∀̇∈ t φ) γ = cong (⋀ S) (funExt (λ x →
      cong₂ _⇒_ (cong (x ∈ˢ_) (⟦⟧-map t γ)) (⊨-map φ (x ∷ γ))))
    ⊨-map (∃̇∈ t φ) γ = cong (⋁ S) (funExt (λ x →
      cong₂ _⊓_ (cong (x ∈ˢ_) (⟦⟧-map t γ)) (⊨-map φ (x ∷ γ))))
```

<!--en-->
The commutation lemma already contains the parameter-free case, and the corollary below merely reads it off. A parameter-free formula is one whose constant domain is the empty type `⊥*`; there are no constant symbols to interpret, so it can be embedded into formulas over any domain `K` by `embed`, and the two readings of its meaning must agree whatever `K` and `ι` are.
<!--zh-->
交换引理本身已经包含无参情形，下面的推论只是把它读出来。无参公式是常元域为空类型 `⊥*` 的公式：没有需要解释的常元符号，因此经 `embed` 可以嵌入为任意域 `K` 上的公式，而其含义的两种读法无论 `K` 与 `ι` 如何都必须一致。
<!--ja-->
可換の補題はすでに無パラメータの場合を含んでおり、下の系はそれを読み出すだけです。無パラメータ論理式とは定数域が空型 `⊥*` である論理式のことです。解釈すべき定数記号がないため、`embed` によって任意の域 `K` 上の論理式へ埋め込め、その意味の二つの読み方は `K` と `ι` が何であれ一致しなければなりません。
<!--/-->

<!--en-->
The inner module fixes an arbitrary target domain `K` and interpretation `ι : K → S`, then opens the satisfaction relation twice: once normally for formulas over `K`, and once under the name `_⊨∅_` for formulas over the empty constant domain, where the interpretation is the function `λ b → ι (Empty.rec* b)`. That function is legitimate because `Empty.rec*` is the eliminator of the empty type: an element of `⊥*` would let one produce an element of any type, including `S`, so the interpretation never actually needs a value.
<!--zh-->
内层模块固定任意目标域 `K` 与解释 `ι : K → S`，然后打开两次满足关系：一次通常地用于 `K` 上的公式，一次以名字 `_⊨∅_` 用于空常元域上的公式，其解释为函数 `λ b → ι (Empty.rec* b)`。这个函数是合法的，因为 `Empty.rec*` 是空类型的消去子：`⊥*` 的一个元素本可产生任何类型 (包括 `S`) 的元素，所以该解释实际上永远不需要具体的值。
<!--ja-->
内側のモジュールは任意の対象域 `K` と解釈 `ι : K → S` を固定し、充足関係を二度開きます。一度は通常どおり `K` 上の論理式に対して、もう一度は名前 `_⊨∅_` で空の定数域上の論理式に対してです。後者の解釈は関数 `λ b → ι (Empty.rec* b)` です。これが正当なのは、`Empty.rec*` が空型の消去子だからです。`⊥*` の元があれば任意の型 (`S` を含む) の元を作れるので、この解釈が実際に値を必要とすることは決してありません。
<!--/-->

```agda
  module _ {ℓe ℓc} {K : Type ℓc} (ι : K → S) where

    open At K ι using ( _⊨_ )
    open At (⊥* {ℓe}) (λ b → ι (Empty.rec* b)) using () renaming ( _⊨_ to _⊨∅_ )

    embed-⊨ : ∀ {n} (φ : Formula (⊥* {ℓe}) n) (γ : S ^ n)
            → (γ ⊨ embed φ) ≡ (γ ⊨∅ φ)
```

<!--en-->
The corollary `embed-⊨` is then a direct instance of `⊨-map`, with `f` taken to be the empty eliminator `Empty.rec*` viewed as a function `⊥* → K`: for every parameter-free formula `φ` and environment `γ`, satisfaction of `embed φ` under `ι` is a path to satisfaction of `φ` in the `∅`-marked reading. In words, embedding a parameter-free formula into a richer constant domain cannot change what it says.
<!--zh-->
于是推论 `embed-⊨` 就是 `⊨-map` 的直接实例，其中 `f` 取为视为函数 `⊥* → K` 的空消去子 `Empty.rec*`：对每个无参公式 `φ` 与环境 `γ`，`embed φ` 在 `ι` 下的满足与 `φ` 在带 `∅` 标记读法下的满足之间有一条路径。换言之，把无参公式嵌入更丰富的常元域不会改变它所说的话。
<!--ja-->
系 `embed-⊨` は、`f` を関数 `⊥* → K` と見なした空の消去子 `Empty.rec*` として `⊨-map` の直接の実例です。すべての無パラメータ論理式 `φ` と環境 `γ` に対し、`embed φ` を `ι` の下で充足することと、`∅` 標識の読み方で `φ` を充足することとの間に経路があります。つまり、無パラメータ論理式をより豊かな定数域へ埋め込んでも、その述べる内容は変わりません。
<!--/-->

```agda
    embed-⊨ = ⊨-map Empty.rec* ι
```

<!--en-->
## Levy witness level

Meaning is only half of the story. The Lévy hierarchy classifies formulas by quantifier structure, and this classification is represented by inductive witnesses: `Δ₀ φ` is explicit data certifying that every quantifier in `φ` is bounded, and `Σₙ k φ` / `Πₙ k φ` record the alternating unbounded blocks. Since relabelling replaces constant symbols but leaves every connective and quantifier, bounded or not, exactly where it was, the witnesses should survive, and `mapΔ₀` shows this at the Δ₀ level before the mutual induction extends it upward.
<!--zh-->
## Lévy 见证层

含义只是故事的一半。Lévy 层级按量词结构给公式分类，这一分类用归纳见证表示：`Δ₀ φ` 是显式数据，证明 `φ` 中每个量词都有界；`Σₙ k φ` 与 `Πₙ k φ` 记录交替的无界块。由于常元改名只替换常元符号，而让每个联结词与量词 (无论有界与否) 原位不动，见证理应幸存。`mapΔ₀` 先在 Δ₀ 层面展示这一点，随后互归纳把它向上扩展。
<!--ja-->
## Lévy 証人の水準

意味は物語の半分にすぎません。Lévy 階層は量化子の構造によって論理式を分類し、その分類は帰納的な証人で表されます。`Δ₀ φ` は `φ` のすべての量化子が有界であることを証明する明示的なデータであり、`Σₙ k φ` と `Πₙ k φ` は交互に現れる非有界の列を記録します。定数の改名は定数記号を置き換えるだけで、結合子と量化子 (有界かどうかにかかわらず) をすべて元の位置に保つため、証人は生き延びるはずです。`mapΔ₀` はまず Δ₀ の水準でこれを示し、その後の相互帰納法が上方へ拡張します。
<!--/-->

<!--en-->
Relabelling replaces each constant symbol but leaves every quantifier, bounded or not, exactly where it was, so a formula's quantifier shape is invariant under `mapFo f`. A Lévy witness records exactly that shape, so it should transport along any `f`. The type of `mapΔ₀` states this at the base level: from a Δ₀ witness for `φ` it produces a Δ₀ witness for `mapFo f φ`. The atomic cases are immediate: a witness `δ-∈` for `t ∈̇ u` carries no arguments, because an atomic formula has no quantifiers to bound, and `mapFo f` sends the formula to another atomic formula of the same shape, so `δ-∈` again certifies it; the same holds for `≐`.
<!--zh-->
常元改名只替换常元符号，而让每个量词 (无论有界与否) 原位不动，因此公式的量词形状在 `mapFo f` 下不变。Lévy 见证记录的正是这一形状，所以它应当能沿任意 `f` 搬运。`mapΔ₀` 的类型在基底层面陈述了这一点：从 `φ` 的一个 Δ₀ 见证产生 `mapFo f φ` 的一个 Δ₀ 见证。原子情形是直接的：`t ∈̇ u` 的见证 `δ-∈` 不带参数，因为原子公式没有需要约束的量词，而 `mapFo f` 把该公式变为同一形状的另一个原子公式，所以 `δ-∈` 再次证明它；`≐` 同理。
<!--ja-->
定数の改名は定数記号を置き換えるだけで、すべての量化子 (有界かどうかにかかわらず) を元の位置に保つため、論理式の量化子の形は `mapFo f` の下で不変です。Lévy の証人が記録するのはまさにその形なので、任意の `f` に沿って輸送できるはずです。`mapΔ₀` の型は基底の水準でこれを述べます。`φ` に対する Δ₀ の証人から `mapFo f φ` に対する Δ₀ の証人を作るのです。原子論理式の場合は直ちに得られます。`t ∈̇ u` の証人 `δ-∈` は引数を取りません。原子論理式には束縛すべき量化子がないからです。`mapFo f` はこの論理式を同じ形の別の原子論理式へ送るため、再び `δ-∈` がそれを証明します。`≐` も同様です。
<!--/-->

```agda
mapΔ₀ : ∀ {ℓc ℓd} {K : Type ℓc} {K' : Type ℓd} (f : K → K')
        {n} {φ : Formula K n} → Δ₀ φ → Δ₀ (mapFo f φ)
mapΔ₀ f δ-∈ = δ-∈
mapΔ₀ f δ-≐ = δ-≐
mapΔ₀ f (δ-∧ c d) = δ-∧ (mapΔ₀ f c) (mapΔ₀ f d)
```

<!--en-->
The remaining constructors of `Δ₀` are the connectives, falsity, and the bounded quantifiers. Each packages witnesses for its subformulas, and each recursive call transports a structurally smaller witness, with the constructor rebuilding the package over the renamed formula. Crucially, `Δ₀` has no constructor for the unbounded quantifiers `∃̇` and `∀̇`, only for the bounded `∀̇∈` and `∃̇∈`, and those two cases recurse exactly like the connectives. Since `mapFo f` never turns a bounded quantifier into an unbounded one, every witness input has a case, which is what makes the definition total.
<!--zh-->
`Δ₀` 的其余构造子是联结词、假与有界量词。每一个都打包其子公式的见证，每次递归调用搬运一个结构上更小的见证，再由该构造子在改名后的公式上重建打包。关键在于，`Δ₀` 对无界量词 `∃̇` 与 `∀̇` 没有构造子，只有对有界的 `∀̇∈` 与 `∃̇∈` 的构造子，而这两个情形的递归与联结词完全一样。由于 `mapFo f` 从不把有界量词变成无界量词，每个见证输入都有对应的情形，这正是定义成为全函数的原因。
<!--ja-->
`Δ₀` の残りの構成子は、結合子、偽、そして有界量化子です。それぞれが部分論理式の証人を束ねており、各再帰呼び出しは構造的に小さい証人を輸送し、その構成子が改名後の論理式の上で束を組み立て直します。決定的なのは、`Δ₀` には非有界な量化子 `∃̇` と `∀̇` の構成子がなく、有界な `∀̇∈` と `∃̇∈` の構成子だけがあることで、この二つの場合の再帰は結合子とまったく同じです。`mapFo f` が有界量化子を非有界量化子に変えることはないので、証人の入力には必ず場合が対応し、これが定義を全域的にする理由です。
<!--/-->

```agda
mapΔ₀ f (δ-∨ c d) = δ-∨ (mapΔ₀ f c) (mapΔ₀ f d)
mapΔ₀ f (δ-⇒ c d) = δ-⇒ (mapΔ₀ f c) (mapΔ₀ f d)
mapΔ₀ f δ-⊥ = δ-⊥
mapΔ₀ f (δ-∀∈ c) = δ-∀∈ (mapΔ₀ f c)
mapΔ₀ f (δ-∃∈ c) = δ-∃∈ (mapΔ₀ f c)
```

<!--en-->
The Δ₀ level is the base of an inductively defined hierarchy: a Σₙ witness is either a Δ₀ witness, or a Π witness one level down, or a witness for an unbounded existential block, and dually for Πₙ. Because Σₙ and Πₙ are defined in terms of each other, the relabelling lemma for both must be proved at once, in a `mutual` block.
<!--zh-->
Δ₀ 层是一个归纳定义的层级的基底：Σₙ 见证要么是 Δ₀ 见证，要么是低一层的 Π 见证，要么是一段无界存在量词的见证；Πₙ 对偶。由于 Σₙ 与 Πₙ 相互定义，二者的改名引理必须在同一个 `mutual` 块中同时证明。
<!--ja-->
Δ₀ の水準は、帰納的に定義された階層の基底です。Σₙ の証人は、Δ₀ の証人か、一段下の Π の証人か、非有界な存在量化の列の証人のいずれかであり、Πₙ はその双対です。Σₙ と Πₙ は互いに定義し合うため、両者に対する改名の補題は `mutual` ブロックで一度に証明しなければなりません。
<!--/-->

<!--en-->
Above Δ₀, a Σₙ witness is either a Δ₀ witness, a Π witness one level down, or a witness for a block of unbounded existentials, and dually for Πₙ. The two forms are defined in terms of each other, so their transport lemmas are proved at once in a `mutual` block, with the same shape as `mapΔ₀`: from a Σₙ (respectively Πₙ) witness for `φ`, produce one for `mapFo f φ` at the same level `k`. A witness `σ-Δ₀ d` wraps a Δ₀ witness, and `mapΔ₀ f d` transports it at the leaves. A witness `σ-Π p` records a turn of the alternation, and is handled by calling the Π lemma, which is exactly why the two proofs must be mutually recursive.
<!--zh-->
在 Δ₀ 之上，Σₙ 见证要么是 Δ₀ 见证，要么是低一层的 Π 见证，要么是一段无界存在量词的见证；Πₙ 对偶。两种形式相互定义，因此二者的搬运引理在同一个 `mutual` 块中同时证明，其形状与 `mapΔ₀` 相同：从 `φ` 的一个 Σₙ (相应地 Πₙ) 见证，产生同一层级 `k` 上 `mapFo f φ` 的一个见证。见证 `σ-Δ₀ d` 包装一个 Δ₀ 见证，由 `mapΔ₀ f d` 在叶端搬运；见证 `σ-Π p` 记录层级交替中的一次转向，由调用 Π 引理来处理，这正是两个证明必须互递归的原因。
<!--ja-->
Δ₀ の上では、Σₙ の証人は Δ₀ の証人か、一段下の Π の証人か、非有界な存在量化の列の証人のいずれかであり、Πₙ はその双対です。二つの形式は互いに定義し合うため、輸送の補題は `mutual` ブロックで一度に証明されます。その形は `mapΔ₀` と同じで、`φ` の Σₙ (それぞれ Πₙ) の証人から、同じ水準 `k` の `mapFo f φ` の証人を作ります。証人 `σ-Δ₀ d` は Δ₀ の証人を包み、`mapΔ₀ f d` が葉でそれを輸送します。証人 `σ-Π p` は交互の一段回を記録するもので、Π の補題を呼び出して処理します。両方の証明が相互再帰でなければならないのはまさにこのためです。
<!--/-->

```agda
mutual
  mapΣₙ : ∀ {ℓc ℓd} {K : Type ℓc} {K' : Type ℓd} (f : K → K')
          {k n} {φ : Formula K n} → Σₙ k φ → Σₙ k (mapFo f φ)
  mapΣₙ f (σ-Δ₀ d) = σ-Δ₀ (mapΔ₀ f d)
  mapΣₙ f (σ-Π p)  = σ-Π (mapΠₙ f p)
```

<!--en-->
The remaining Σ case `σ-∃ s` handles a block of unbounded existentials: the block stays a block under `mapFo f`, so the sub-witness `s` is transported by a recursive call to `mapΣₙ` itself. The Π side is the exact dual, with `π-Δ₀` delegating to `mapΔ₀` and `π-Σ` calling `mapΣₙ` for the alternation.
<!--zh-->
Σ 的其余情形 `σ-∃ s` 处理一段无界存在量词：该块在 `mapFo f` 下仍是块，因此子见证 `s` 由对 `mapΣₙ` 自身的递归调用搬运。Π 一侧是完全的对偶，`π-Δ₀` 委托给 `mapΔ₀`，`π-Σ` 为层级交替调用 `mapΣₙ`。
<!--ja-->
Σ の残りの場合 `σ-∃ s` は非有界な存在量化の列を扱います。`mapFo f` の下でも列は列のままだから、下位の証人 `s` は `mapΣₙ` 自身への再帰呼び出しで輸送されます。Π の側は正確な双対で、`π-Δ₀` は `mapΔ₀` に委ね、`π-Σ` は交互の回に対して `mapΣₙ` を呼びます。
<!--/-->

```agda
  mapΣₙ f (σ-∃ s)  = σ-∃ (mapΣₙ f s)

  mapΠₙ : ∀ {ℓc ℓd} {K : Type ℓc} {K' : Type ℓd} (f : K → K')
          {k n} {φ : Formula K n} → Πₙ k φ → Πₙ k (mapFo f φ)
  mapΠₙ f (π-Δ₀ d) = π-Δ₀ (mapΔ₀ f d)
  mapΠₙ f (π-Σ s)  = π-Σ (mapΣₙ f s)
```

<!--en-->
The final case `π-∀ p` mirrors `σ-Π`, transporting the alternation within the Π side. Termination is not an additional argument here but a structural fact: each recursive call is applied to a structurally smaller component of the witness, with `mapΔ₀` at the leaves of both recursions. The result is a single transport principle for the whole finite Lévy hierarchy: a formula's grade, as recorded by its inductive witness, is invariant under relabelling of constants.
<!--zh-->
最后的情形 `π-∀ p` 与 `σ-Π` 成镜像，在 Π 一侧搬运层级交替。终止性在这里不是额外的论证而是结构性事实：每次递归调用都作用于见证的结构上更小的分支，而 `mapΔ₀` 位于两个递归的叶端。其结果是对整个有限 Lévy 层级的单一搬运原理：由归纳见证记录的公式级别在常元改名下不变。
<!--ja-->
最後の場合 `π-∀ p` は `σ-Π` と鏡像をなし、Π の側で交互の回を輸送します。停止性はここでは追加の議論ではなく構造的事実です。各再帰呼び出しは証人の構造的に小さい成分に適用され、`mapΔ₀` が両方の再帰の葉にあります。得られるのは、有限の Lévy 階層全体に対する一つの輸送原理です。帰納的な証人によって記録された論理式の等級は、定数の改名の下で不変です。
<!--/-->

```agda
  mapΠₙ f (π-∀ p)  = π-∀ (mapΠₙ f p)
```

<!--en-->
## Recap

This chapter established two invariance properties of the relabelling action `mapFo f`. Semantically, `⊨-map` says that renaming constants commutes with satisfaction, in the precise sense that evaluating under `ι` after renaming equals evaluating under `ι ∘ f` before; the parameter-free embedding `embed-⊨` follows as the special case where the source domain is empty. Syntactically, `mapΔ₀`, `mapΣₙ` and `mapΠₙ` say that the Lévy witnesses, which certify a formula's quantifier structure, can be transported along any relabelling. Together these mean that a formula can be moved between constant domains while both its meaning and its complexity witness move with it, which is what later chapters rely on when shifting between the empty domain and the domains of the constructible hierarchy.
<!--zh-->
## 小结

本章确立了常元改名作用 `mapFo f` 的两条不变性。语义上，`⊨-map` 断言常元改名与满足关系可交换，精确地说：改名后在 `ι` 下求值等于改名前在 `ι ∘ f` 下求值；无参嵌入 `embed-⊨` 作为源域为空的特例随之而来。语法上，`mapΔ₀`、`mapΣₙ` 与 `mapΠₙ` 断言证明公式量词结构的 Lévy 见证可沿任意改名搬运。合起来，公式可以在常元域之间移动，其含义与复杂度见证一同移动；这正是后面章节在空域与可构造层级的各域之间转换时所依赖的事实。
<!--ja-->
## まとめ

この章では、定数の改名の作用 `mapFo f` に関する二つの不変性を確立しました。意味論的には、`⊨-map` が定数の改名と充足関係の可換性を主張します。正確には、改名後の `ι` の下での評価は、改名前の `ι ∘ f` の下での評価と等しいということです。無パラメータの埋め込み `embed-⊨` は、源の定数域が空である特別な場合として従います。構文的には、`mapΔ₀`、`mapΣₙ`、`mapΠₙ` が、論理式の量化子構造を証明する Lévy の証人が任意の改名に沿って輸送できることを主張します。合わせて、論理式はその意味と複雑さの証人を伴ったまま定数域の間を移動でき、これは後の章が空の定数域と構成可能階層の諸域との間を移るときに依拠する事実です。
<!--/-->

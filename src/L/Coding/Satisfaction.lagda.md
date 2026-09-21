<!--en-->
# Satisfaction by recursion on formulas

Given a set `B` in `L` and a formula, we construct the set of environments over `B` that satisfy that formula. The construction proceeds by recursion on the formula: for a compound formula the set is determined by the sets of its immediate subformulas, while the atoms and falsity are handled directly. In every case the set is obtained by separation, from the set of all length-`n` environments over `B`, of those whose entries meet a describing condition. The membership equations of the resulting sets describe the ten formula constructors.

The recursion being on a meta-language formula shapes every step. Agda can inspect the formula, so each step may name the sets produced at the subformulas as constants of the describing condition, and the object language never has to quantify over a code. The atoms are correspondingly short: a meta-language term is visibly a variable or a constant, so reading its value has one case rather than the two that a coded clause must distinguish.
<!--zh-->
# 沿公式递归构造满足关系

给定 `L` 中的集合 `B` 和一条公式，我们构造 `B` 上满足该公式的环境所组成的集合。构造沿公式递归进行：复合公式的集合由其直接子公式的集合确定，而原子与假则被直接处理。无论哪种情形，集合都由分离得到：从「`B` 上长度 `n` 的全部环境」这个集合中，保留条目满足描述条件的那些。所得集合的隶属等式逐一描述十个公式构造子。

递归沿元语言的公式进行，这一点决定了每个步骤的形状。Agda 可以检查这条公式，因此每一步都能把子公式处已产出的集合作为描述条件的常元点名，而对象语言始终不必对码作量化；于是每一步都只是一次分离。原子情形也相应简短：元语言的词项一眼可辨是变元还是常元，读取其取值只需一种情形，而非码化子句必须区分的两种。
<!--ja-->
# 論理式上の再帰による充足関係

`L` の集合 `B` と論理式を与え、その論理式を充足する `B` 上の環境の集合を構成する。構成は論理式の上の再帰として進む。複合の論理式の集合は直接の部分式の集合によって定まり、原子と偽はそれぞれ直接に扱われる。いずれの場合も、集合は分出によって得られる。すなわち、「`B` 上の長さ `n` のすべての環境」という集合から、記述の条件を満たすものを残すのである。得られる集合の所属の等式は十の論理式構成子を記述する。

再帰がメタ言語の論理式の上にあることが、すべての段階の形を決める。Agda は論理式を検査できるので、各段階は部分式で作られた集合を記述の条件の定数として名指せる。対象言語が符号を量化する必要は一度も生じない。したがって各段階は一度の分出であり、原子の場合が短いのも同じ理由からである。メタ言語の項は変数か定数かが目に見えているため、値の読み取りは場合を一つしか持たない。符号化された節が区別しなければならない二場合と比べてのことである。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module L.Coding.Satisfaction {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

<!--en-->
The construction is carried out under excluded middle at the successor of the model level. Its formulas belong to the language of set theory, with equality, membership, the three binary connectives, falsity, and bounded and unbounded quantifiers.
<!--zh-->
构造假设模型层级的后继处成立排中律。所处理的是集合论语言的公式，包含相等、隶属、三个二元联结词、假，以及有界与无界量词。
<!--ja-->
構成は、モデルのレベルの後続での排中律を仮定する。扱うのは集合論の言語の論理式で、相等、所属、三つの二項結合子、偽、有界および非有界の量化子を含む。
<!--/-->

```agda

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Term; con; var; Formula
        ; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Absoluteness
```

<!--en-->
Satisfaction will be read in the constructible substructure of the cumulative hierarchy. Formula absoluteness supplies that restricted reading, while ordered pairs encode the graphs used as environments.
<!--zh-->
满足关系将在累积层级的可构造子结构中读取。公式绝对性提供这种限制结构中的读法，有序对则编码充当环境的图。
<!--ja-->
充足は、累積階層の構成可能部分構造で読み取る。論理式の絶対性がその制限された読み方を与え、順序対が環境として用いるグラフを符号化する。
<!--/-->

```agda
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
```

<!--en-->
For each formula, separation cuts its satisfaction set out of the set of coded environments. The formulas `appAt`{.Agda} and `consAtL`{.Agda} describe lookup in an environment graph and extension by one value; `envSet`{.Agda} supplies all environments of the required length.
<!--zh-->
对每条公式，分离从编码环境集里截出其满足集合。公式 `appAt`{.Agda} 与 `consAtL`{.Agda} 分别描述环境图中的查找和添入一个值后的扩展；`envSet`{.Agda} 给出所需长度的全部环境。
<!--ja-->
各論理式について、分出によって符号化環境の集合から充足集合を切り出す。`appAt`{.Agda} と `consAtL`{.Agda} は、環境グラフでの参照と一つの値による拡張を記述し、`envSet`{.Agda} は必要な長さのすべての環境を与える。
<!--/-->

```agda
open import L.Coding.Model {ℓ} using ( appAt; appAt-adequate )
open import L.Coding.Expressions {ℓ} using ( consAtL; numL )
open import L.Coding.EnvironmentSet {ℓ} lem using ( envSet )
```

<!--en-->
Existential clauses produce propositionally truncated witnesses. Finite indices are converted to natural numbers and then represented by von Neumann numerals inside the hierarchy.
<!--zh-->
存在子句给出命题截断下的见证。有限指标先化为自然数，再由层级内部的冯·诺伊曼数码表示。
<!--ja-->
存在の節は、命題的に切り詰められた証人を与える。有限添字は自然数へ変換され、階層内部のフォン・ノイマン数項で表される。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
```

<!--en-->
The hierarchy's numeral construction names those indices as sets. Opening the constructible truth-valued structure fixes the meaning of membership and satisfaction throughout the chapter.
<!--zh-->
层级的数码构造把这些指标命名为集合。打开可构造的真值结构后，本章中的隶属与满足便有了固定含义。
<!--ja-->
階層の数項構成は、それらの添字を集合として名指す。構成可能な真理値構造を開くことで、本章を通じた所属と充足の意味が定まる。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_ )
```

<!--en-->
The notation `_⊨_`{.Agda} below is satisfaction in the restricted constructible structure, evaluated under a finite environment vector.
<!--zh-->
下文的 `_⊨_`{.Agda} 表示限制可构造结构中的满足关系，并在有限环境向量下求值。
<!--ja-->
以下の `_⊨_`{.Agda} は、有限環境ベクトルのもとで評価される、制限された構成可能構造の充足関係である。
<!--/-->

```agda

open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## Evaluating variables and constants

A variable obtains its value from the environment at its index; a constant already names its value. Both facts are said inside the object language, because the describing conditions are formulas. The term reader `tmIs` says, of a value slot and an environment slot, that the environment assigns to the term the value at the value slot. For a constant this is the bare equation between the value slot and the constant. For a variable it is an existence statement: some carrier element equals the numeral of the index, and the application clause says that the pair of that index and the recorded value belongs to the graph of the environment recorded at the environment slot. Satisfaction judgments throughout are read in `L`.
<!--zh-->
## 变元与常元的求值

变元从环境中取得其索引处的值；常元则直接指称自己的值。这两件事实必须在对象语言内部说出，因为描述条件本身是公式。词项读式 `tmIs` 说的是：在取值槽位与环境槽位之间，环境把该词项对应到取值槽位中的那个值。对常元，这就是取值槽位与常元之间的等式本身。对变元，这是一条存在陈述：载体的某个元素等于该索引的数码，而应用子句说，这个索引与所记录取值组成的对属于环境槽位处所记录环境的图。全章的满足判断都在 `L` 中读出。
<!--ja-->
## 変数と定数の評価

変数の値はその添字に対応する環境の成分であり、定数は自らの値を指定している。この二つの事実は対象言語の内部で言われなければならない。記述の条件そのものが論理式だからである。項の読み `tmIs` は、値のスロットと環境のスロットについて、環境がその項を値のスロットの値に対応させることを述べる。定数なら、それは値のスロットと定数の間の等式そのものである。変数の場合は存在の主張になる。台のある要素が添字の数項に等しく、適用の節は、その添字と記録された値の対が、環境のスロットに記録された環境のグラフに属することを言う。充足の判断はすべて `L` の中で読まれる。
<!--/-->

```agda
private
  nn : ℕ → S
  nn k = # k , numL k
```

<!--en-->
The internal numerals pair the ambient von Neumann numerals with their constructibility proofs, so an index can be named inside `L` wherever it is needed.
<!--zh-->
内部数码把外围的冯·诺伊曼数码连同其可构造性证明配成对，于是索引在需要之处总能在 `L` 内部被点名。
<!--ja-->
内部の数項は、周囲のフォン・ノイマン数項にその構成可能性の証明を対にしたもので、添字は必要な場所でいつでも `L` の内部で名指せる。
<!--/-->

```agda

tmIs : ∀ {n m} → Term S n → Fin m → Fin m → Formula S m
```

<!--en-->
The reader takes a term, the slot holding the value of the term, and the slot holding the environment in which the term is read, and it returns a formula over environments of that length.
<!--zh-->
读式取一个词项、持有该词项取值的槽位、以及读取词项时所处环境的槽位，返回该长度环境上的一条公式。
<!--ja-->
読みは、項と、その項の値を収めるスロットと、項を読む環境を収めるスロットを受け取り、その長さの環境の上の論理式を返す。
<!--/-->

```agda
tmIs (var i) v e =
  ∃̇ ((var zero ≐ con (nn (toℕ i))) ∧̇ appAt (suc e) zero (suc v))
```

<!--en-->
For a variable, the clause says that some carrier element `x` equals the numeral of the index, and that the pair of that index and the value at the value slot belongs to the graph of the environment recorded at the environment slot. The equation only pins the index witness; the application clause carries the content.
<!--zh-->
对变元，子句说：载体的某个元素 `x` 等于该索引的数码，且「这个索引与取值槽位处的取值组成的对属于环境槽位处所记录环境的图」。等式只是钉住索引见证；携带内容的是应用子句。
<!--ja-->
変数の場合、この節は次のように述べる。台のある要素 `x` が添字の数項に等しく、その添字と値のスロットの値の対が、環境のスロットに記録された環境のグラフに属する、と。等式は添字の証人を釘付けにするだけで、内容を運ぶのは適用の節である。
<!--/-->

```agda
tmIs (con c) v e = var v ≐ con c
```

<!--en-->
For a constant, no environment is consulted: the value slot is simply identified with the constant.
<!--zh-->
对常元，无须考察环境：取值槽位就等同于该常元。
<!--ja-->
定数の場合、環境を調べる必要はない。値のスロットはその定数と同一視されるだけである。
<!--/-->

```agda

tmIs-var-in : ∀ {n m} (i : Fin n) (γ : S ^ m) (v e : Fin m)
            → ⟨ pr (# (toℕ i)) (fst (lookup v γ)) ∈ fst (lookup e γ) ⟩
            → ⟨ γ ⊨ tmIs {n} (var i) v e ⟩
```

<!--en-->
The adequacy lemmas connect the formula with the ambient membership it encodes. Inward: if the environment at slot `e` contains the pair of the numeral `i` and the value at slot `v`, then `γ` satisfies the reader.
<!--zh-->
充分性的两条引理把公式与它所编码的外围隶属连接起来。向内：若槽位 `e` 处的环境包含数码 `i` 与槽位 `v` 处取值组成的对，则 `γ` 满足这条读式。
<!--ja-->
妥当性の二つの補題が、論理式とそれが符号化する周囲の所属とを結ぶ。内向きには、スロット `e` の環境が、数項 `i` とスロット `v` の値の対を含むなら、`γ` はこの読みを満たす。
<!--/-->

```agda
tmIs-var-in i γ v e h = ∣ nn (toℕ i)
  , ( refl
    , subst ⟨_⟩ (sym (appAt-adequate (suc e) zero (suc v) (nn (toℕ i) ∷ γ))) h ) ∣₁
```

<!--en-->
The witness is the numeral itself; its defining equation is definitional, and the membership travels along the adequacy path, read in reverse, from the ambient statement to the internal clause over the extended environment.
<!--zh-->
见证就是数码本身；其定义等式是定义性的，而那份隶属沿充分性路径反方向传输，从外围陈述变为扩展环境上的内部子句。
<!--ja-->
証人は数項そのものであり、その定義の等式は定義的である。所属は妥当性のパスに沿って逆向きに輸送され、周囲の主張から拡張された環境の上の内部の節へ変わる。
<!--/-->

```agda

tmIs-var-out : ∀ {n m} (i : Fin n) (γ : S ^ m) (v e : Fin m)
             → ⟨ γ ⊨ tmIs {n} (var i) v e ⟩
             → ⟨ pr (# (toℕ i)) (fst (lookup v γ)) ∈ fst (lookup e γ) ⟩
```

<!--en-->
Outward, satisfaction of the reader yields the ambient membership. Here a general principle of the chapter appears for the first time: a truncated witness may be consumed whenever the goal is a proposition or a truncation, and nothing below violates this.
<!--zh-->
向外，读式的满足给出外围隶属。这里首次出现本章的一条一般原则：只要目标是命题或截断，截断见证即可消耗；下文任何地方都不违反这一点。
<!--ja-->
外向きには、読みの充足から周囲の所属が得られる。ここで本章の一般原則が初めて現れる。目標が命題か切り詰めである限り、切り詰められた証人は消費できる。以下のどこでもこの原則は破られない。
<!--/-->

```agda
tmIs-var-out i γ v e = rec₁
  (snd (pr (# (toℕ i)) (fst (lookup v γ)) ∈ fst (lookup e γ)))
```

<!--en-->
The truncated witness pairs an entry `x` with the proof that `x` is the numeral of the index and that the clause over the extended environment holds.
<!--zh-->
截断的见证由条目 `x` 与两份证明组成：`x` 是该索引的数码，且扩展环境上的子句成立。
<!--ja-->
切り詰められた証人は、項目 `x` と、`x` が添字の数項であること、そして拡張された環境の上で節が成り立つことの証明の組である。
<!--/-->

```agda
  (λ { (x , (qx , m)) →
    subst (λ w → ⟨ pr w (fst (lookup v γ)) ∈ fst (lookup e γ) ⟩) qx
      (subst ⟨_⟩ (appAt-adequate (suc e) zero (suc v) (x ∷ γ)) m) })
```

<!--en-->
The adequacy path identifies the clause with the membership of the pair of `x` and the value; rewriting `x` back to the numeral along its equation leaves exactly the membership that the outward direction owes.
<!--zh-->
充分性路径把该子句等同于 `x` 与取值组成的对的隶属；沿其等式把 `x` 改写回数码，剩下的恰是向外方向所应交付的那份隶属。
<!--ja-->
妥当性のパスは、この節を `x` と値の対の所属と同一視する。`x` をその等式に沿って数項へ書き戻せば、外向きの方向が負う所属がちょうど残る。
<!--/-->

<!--en-->
## The set of satisfying environments

For each constructor, a formula describes which environments to retain by separation, and every describing condition is a one-variable formula over environments of the formula's own arity. The connectives refer to the sets already built for the subformulas, naming them as constants. An unbounded quantifier conses a member of the carrier onto the environment and asks whether the extension belongs to the set one arity up; the bounded quantifiers add the second guard that the new entry lies in the bounding term's value. Every step of the construction is thus one separation.
<!--zh-->
## 满足公式的环境集

对每个构造子，一条公式描述分离时应保留哪些环境，而每条描述条件都是定义在该公式自身元数的环境上的一条单变元公式。联结词引用为子公式已构造的集合，把它们作为常元点名。无界量词把载体的一个成员添加到环境之前，再检验扩展是否属于元数多一的那个集合；有界量词再加一道约束：新条目须落在界项的取值之中。于是构造的每一步都只是一次分离。
<!--ja-->
## 論理式を充足する環境の集合

各構成子について、分出で残す環境を論理式が指定し、どの記述の条件も、その論理式自身のアリティの環境の上の一変数の論理式である。結合子は部分式のためにすでに作られた集合を定数として名指して参照する。非有界の量化子は、台の要素を環境の先頭に加え、その拡張が一つアリティの大きい集合に属するかを調べる。有界の量化子はさらに、新しい項目が界の項の値に属するという守りを加える。こうして構成の各段階はすべて一度の分出である。
<!--/-->

```agda
private
  opaque
    sep : (a : S) → Formula S 1 → S
    sep a φ = hasSeparationL a φ .fst .fst
```

<!--en-->
Separation is recorded once, in its opaque wrapper: from a set and a one-variable formula it produces the subset.
<!--zh-->
分离被一次性记录在不透明的包装之中：从一个集合与一条单变元公式产出子集。
<!--ja-->
分出は不透明な包装の中に一度記録される。集合と一変数の論理式から部分集合を作る。
<!--/-->

```agda

    sep-mem : (a : S) (φ : Formula S 1) (x : S)
            → (x ∈ˢ sep a φ) ≡ ((x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ))
    sep-mem a φ = hasSeparationL a φ .fst .snd
```

<!--en-->
The membership specification is the whole content of separation: membership in the subset is membership in the ambient set together with satisfaction of the condition.
<!--zh-->
隶属规格就是分离的全部内容：属于子集，等于属于外围集合并且满足条件。
<!--ja-->
所属の仕様が分出の内容のすべてである。部分集合への所属は、周囲の集合への所属と条件の充足を合わせたものである。
<!--/-->

```agda

module _ (B : S) where
  cond : ∀ {n} → Formula S n → Formula S 1
```

<!--en-->
Fix a base set `B`. Every formula will determine a unary condition on a coded environment over `B`; separating the environments that satisfy this condition produces its satisfaction set.
<!--zh-->
固定基集合 `B`。每条公式都确定一个关于 `B` 上编码环境的一元条件；从全部环境中分离出满足该条件者，便得到这条公式的满足集合。
<!--ja-->
基礎集合 `B` を固定する。各論理式は、`B` 上の符号化された環境について一項の条件を定める。その条件を満たす環境を分出すると、その論理式の充足集合が得られる。
<!--/-->

```agda

  Sat : ∀ {n} → Formula S n → S
  Sat {n} φ = sep (envSet B n) (cond φ)
```

<!--en-->
The set of satisfying environments is the separation, from the full environment set at the formula's arity, of the environments meeting the condition.
<!--zh-->
满足公式的环境集，就是从该公式元数的完整环境集中分离出满足条件的环境所得。
<!--ja-->
論理式を充足する環境の集合は、その論理式のアリティの環境の集合全体から、条件を満たす環境を分出したものである。
<!--/-->

```agda

  Sat-mem : ∀ {n} (φ : Formula S n) (x : S)
          → (x ∈ˢ Sat φ) ≡ ((x ∈ˢ envSet B n) ⊓ ((x ∷ []) ⊨ cond φ))
  Sat-mem {n} φ = sep-mem (envSet B n) (cond φ)
```

<!--en-->
Its membership equation records exactly the two requirements: the environment has the right arity and values, and it meets the condition specific to the formula.
<!--zh-->
它的隶属等式恰记录了两项要求：该环境有正确的元数与取值，并且满足这条公式特有的条件。
<!--ja-->
その所属の等式が記録するのは二つの要件である。環境が正しいアリティと値をもち、かつその論理式固有の条件を満たすことである。
<!--/-->

```agda

  cond (t ∈̇ u) =
    (∃̇ (∃̇ ( tmIs t (suc zero) (suc (suc zero))
          ∧̇ ( tmIs u zero (suc (suc zero))
          ∧̇ (var (suc zero) ∈̇ var zero) ))))
```

<!--en-->
The membership atom binds two entries and asserts the object-language membership of the value of `t`, read at slot `suc zero`, in the value of `u`, read at slot `zero`. Both values are read against the environment slot.
<!--zh-->
隶属原子绑定两个条目，并断言对象语言的隶属：在槽位 `suc zero` 处读取的 `t` 的取值，属于在槽位 `zero` 处读取的 `u` 的取值。两个取值都对照环境槽位读取。
<!--ja-->
所属の原子式は二つの項目を束縛し、対象言語の所属を主張する。スロット `suc zero` で読まれる `t` の値が、スロット `zero` で読まれる `u` の値に属するというものである。どちらの値も環境のスロットに対して読まれる。
<!--/-->

```agda
  cond (t ≐ u) =
    (∃̇ (∃̇ ( tmIs t (suc zero) (suc (suc zero))
          ∧̇ ( tmIs u zero (suc (suc zero))
          ∧̇ (var (suc zero) ≐ var zero) ))))
```

<!--en-->
The equality atom has the same shape with equality in place of membership.
<!--zh-->
相等原子形状相同，只是把隶属换成了相等。
<!--ja-->
相等の原子式は同じ形をし、所属の代わりに相等が置かれる。
<!--/-->

```agda
  cond (a ∧̇ b) =
    ((var zero ∈̇ con (Sat a)) ∧̇ (var zero ∈̇ con (Sat b)))
```

<!--en-->
A conjunction's condition asks of the environment that it belong to both subformula sets, each named as a constant.
<!--zh-->
合取的条件要求该环境同时属于两个子公式集合，二者都以常元点名。
<!--ja-->
連言の条件は、その環境が二つの部分式の集合のどちらにも属すことを求める。どちらの集合も定数として名指される。
<!--/-->

```agda
  cond (a ∨̇ b) =
    ((var zero ∈̇ con (Sat a)) ∨̇ (var zero ∈̇ con (Sat b)))
```

<!--en-->
A disjunction's condition asks for membership in at least one of the two.
<!--zh-->
析取的条件要求至少属于二者之一。
<!--ja-->
選言の条件は、二つのうち少なくとも一方への所属を求める。
<!--/-->

```agda
  cond (a ⇒̇ b) =
    ((var zero ∈̇ con (Sat a)) ⇒̇ (var zero ∈̇ con (Sat b)))
```

<!--en-->
An implication's condition says that membership in the antecedent's set implies membership in the consequent's set.
<!--zh-->
蕴涵的条件说：属于前件集合蕴含属于后件集合。
<!--ja-->
含意の条件は、前件の集合への所属が後件の集合への所属を導くと言う。
<!--/-->

```agda
  cond ⊥̇ = ⊥̇
```

<!--en-->
Falsity is its own condition: no environment satisfies it.
<!--zh-->
假的条件就是假本身：没有环境满足它。
<!--ja-->
偽の条件は偽そのものである。これを満たす環境はない。
<!--/-->

```agda
  cond (∃̇ a) =
    (∃̇∈ (con B) (∃̇ ( consAtL zero (suc zero) (suc (suc zero))
                  ∧̇ (var zero ∈̇ con (Sat a)) )))
```

<!--en-->
An unbounded existential ranges over the carrier: some member `x` of `B` extends the environment, the extension clause certifies that the new list is an environment, and the extended environment belongs to the subformula's set.
<!--zh-->
无界存在量词在载体上取值：`B` 的某个成员 `x` 扩展环境，扩展子句证明新的列表确是环境，而扩展后的环境属于子公式的集合。
<!--ja-->
非有界の存在量化子は台の上を動く。`B` のある要素 `x` が環境を拡張し、拡張の節が新しい列が環境であることを証明し、拡張された環境が部分式の集合に属する。
<!--/-->

```agda
  cond (∀̇ a) =
    (∀̇∈ (con B) (∀̇ ( consAtL zero (suc zero) (suc (suc zero))
                  ⇒̇ (var zero ∈̇ con (Sat a)) )))
```

<!--en-->
The unbounded universal is its dual: every member of the carrier, once consed, lands the extended environment in the subformula's set.
<!--zh-->
无界全称是它的对偶：载体的每个成员一经添加，扩展后的环境就落入子公式的集合。
<!--ja-->
非有界の全称はその双対である。台の各要素は、加えられさえすれば、拡張された環境を部分式の集合の中へ落とし入れる。
<!--/-->

```agda
  cond (∀̇∈ t a) =
    (∀̇ ( tmIs t zero (suc zero)
      ⇒̇ ∀̇∈ (con B) ( (var zero ∈̇ var (suc zero))
                   ⇒̇ ∀̇ ( consAtL zero (suc zero) (suc (suc (suc zero)))
                       ⇒̇ (var zero ∈̇ con (Sat a)) ) ) ))
```

<!--en-->
A bounded universal runs in three quantified layers. The outermost reads the value `w` of the bounding term from its slot; over each such `w`, the carrier member `x` is quantified with the two guards `x ∈ B` and `x ∈ w`; and for each `x`, the extension `e'` of the environment by `x`, certified by the extension clause, is required to belong to the subformula's set. Here `w` is only the auxiliary slot of the bound; the environment of the subformula `a` is `e'`, which adds exactly one entry to the environment.
<!--zh-->
有界全称分三层量化。最外层从自己的槽位读出界项的取值 `w`；对每个这样的 `w`，量化载体成员 `x`，并加上 `x ∈ B` 与 `x ∈ w` 两道约束；再对每个 `x`，要求由 `x` 扩展环境所得的 `e'` 经扩展子句认证后属于子公式的集合。这里 `w` 只是界的辅助槽位；子公式 `a` 的环境是 `e'`，它恰好给环境增加一个条目。
<!--ja-->
有界の全称は三層にわたって量化する。最も外側で、界の項の値 `w` をみずからのスロットから読み、そのような各 `w` の上で、台の要素 `x` が `x ∈ B` と `x ∈ w` の二つの守りつきで量化され、さらに各 `x` について、`x` で環境を拡張した `e'` が拡張の節の証明のもとで部分式の集合に属すことが要求される。ここで `w` は境界の補助のスロットにすぎず、部分式 `a` の環境は `e'` であり、環境にちょうど一つの項目を加えたものである。
<!--/-->

```agda
  cond (∃̇∈ t a) =
    (∃̇ ( tmIs t zero (suc zero)
      ∧̇ ∃̇∈ (con B) ( (var zero ∈̇ var (suc zero))
                   ∧̇ ∃̇ ( consAtL zero (suc zero) (suc (suc (suc zero)))
                       ∧̇ (var zero ∈̇ con (Sat a)) ) ) ))
```

<!--en-->
The bounded existential composes the same three layers as an existence statement: the bounding term's value is read first, and the witness is a member of the carrier lying in that value, whose extension belongs to the subformula's set. Both guards, the base and the bound, are kept.
<!--zh-->
有界存在把同样的三层写成存在陈述：先读出界项的取值，见证是载体中落在该取值之内的成员，且其扩展环境属于子公式的集合。基与界两道约束都得到保留。
<!--ja-->
有界の存在量化は、同じ三層を存在の主張として組み合わせる。まず界の項の値が読まれ、証人は台のうちその値に属する要素であり、その拡張された環境が部分式の集合に属することまで要求される。基礎と境界の二つの守りがともに保たれる。
<!--/-->

<!--en-->
## Reading the conditions

The general equation `Sat-mem` separates membership in the environment set from satisfaction of the condition. Conjunction, disjunction, implication, and falsity reduce directly by the definition of `cond`{.Agda}; no auxiliary equivalence is needed for them. The remaining helpers expose the witnesses hidden by the two atomic existentials and by the existential quantifiers, or read the functions supplied by universal quantifiers. They concern only satisfaction of `cond φ`{.Agda}; the environment-set conjunct remains in `Sat-mem`{.Agda}.
<!--zh-->
## 条件的读取

一般等式 `Sat-mem` 把「属于环境集」与「满足条件」分开。合取、析取、蕴涵与假可直接按 `cond`{.Agda} 的定义归约，无须辅助等价。下面的引理只处理其余情形：展开两个原子存在式与存在量词所隐藏的见证，或读出全称量词提供的函数。它们只讨论 `cond φ`{.Agda} 的满足；环境集合取项仍留在 `Sat-mem`{.Agda} 中。
<!--ja-->
## 条件の読み取り

一般の等式 `Sat-mem` は、環境集合への所属と条件の充足を分ける。連言、選言、含意、偽は `cond`{.Agda} の定義によって直接簡約され、補助的な同値は要らない。以下の補題が扱うのは残りの場合である。二つの原子の存在式と存在量化子に隠れた証人を展開し、あるいは全称量化子が与える関数を読み取る。これらは `cond φ`{.Agda} の充足だけを扱い、環境集合の連言は `Sat-mem`{.Agda} に残る。
<!--/-->

```agda
  CondAtom : ∀ {n} → Term S n → Term S n
           → (S → S → Type (ℓ-suc ℓ)) → S → Type (ℓ-suc ℓ)
  CondAtom t u R z = Σ[ v ∈ S ] (Σ[ w ∈ S ]
    (⟨ (w ∷ v ∷ z ∷ []) ⊨ tmIs t (suc zero) (suc (suc zero)) ⟩
     × (⟨ (w ∷ v ∷ z ∷ []) ⊨ tmIs u zero (suc (suc zero)) ⟩ × R v w)))
```

<!--en-->
For the two atoms, the condition is an existence statement, and its unpacked shape is the Σ-type `CondAtom`: a value `v` for `t` and a value `w` for `u`, each read through the term reader against the environment at `z`, together with the relation `R` between the two underlying sets. The type itself carries no truncation; the truncated form appears at the helpers below.
<!--zh-->
对两条原子，条件是一条存在陈述，其展开形状就是 Σ 类型 `CondAtom`：`t` 的取值 `v`、`u` 的取值 `w`，二者都经词项读式对照 `z` 处的环境读取，外加两个底层集合之间的关系 `R`。该类型本身不带截断；截断的形式出现在下面的各条辅助引理处。
<!--ja-->
二つの原子式では、条件は存在の主張であり、その展開された形が Σ 型の `CondAtom` である。`t` の値 `v` と `u` の値 `w` が、それぞれ項の読みを通して `z` の環境に対して読まれ、さらに二つの基底集合の間の関係 `R` が伴う。この型そのものは切り詰めを帯びず、切り詰められた形は後の補題に現れる。
<!--/-->

```agda

  cond∈-in : ∀ {n} (t u : Term S n) (z : S)
           → ∥ CondAtom t u (λ v w → ⟨ fst v ∈ fst w ⟩) z ∥₁
           → ⟨ (z ∷ []) ⊨ cond (t ∈̇ u) ⟩
  cond∈-in t u z = map₁ (λ { (v , (w , r)) → v , ∣ w , r ∣₁ })
```

<!--en-->
The inward mapping for membership repackages the truncated triple as the nested witnesses the two quantifiers expect. The elimination is legitimate because the goal, an outer truncation, is itself a proposition, not because of any property of the relation inside.
<!--zh-->
隶属的向内映射把截断的三元组重新包装成两个量词所期待的嵌套见证。消去之所以合法，是因为目标本身作为外层截断就是命题，而与内部关系具有何种性质无关。
<!--ja-->
所属の内向きの写しは、切り詰められた三つ組を、二つの量化子が期待する入れ子の証人の形に組み直す。消去が正当なのは、目標である外側の切り詰めそれ自体が命題だからで、内側の関係の性質のためではない。
<!--/-->

```agda

  cond∈-out : ∀ {n} (t u : Term S n) (z : S)
            → ⟨ (z ∷ []) ⊨ cond (t ∈̇ u) ⟩
            → ∥ CondAtom t u (λ v w → ⟨ fst v ∈ fst w ⟩) z ∥₁
  cond∈-out t u z = rec₁ squash₁
    (λ { (v , hv) → map₁ (λ { (w , r) → v , (w , r) }) hv })
```

<!--en-->
The outward mapping flattens the nested witnesses back into the triple, the whole argument remaining inside truncation.
<!--zh-->
向外映射把嵌套的见证摊平回三元组，整个论证都留在截断之内。
<!--ja-->
外向きの写しは、入れ子の証人を三つ組へと平らに戻す。議論の全体が切り詰めの内側にとどまる。
<!--/-->

```agda

  cond≐-in : ∀ {n} (t u : Term S n) (z : S)
           → ∥ CondAtom t u (λ v w → fst v ≡ fst w) z ∥₁
           → ⟨ (z ∷ []) ⊨ cond (t ≐ u) ⟩
  cond≐-in t u z = map₁ (λ { (v , (w , r)) → v , ∣ w , r ∣₁ })
```

<!--en-->
The equality atom carries the relation `fst v ≡ fst w`, equality of underlying sets, and its inward mapping is word for word the membership one.
<!--zh-->
相等原子携带的关系是 `fst v ≡ fst w`，即底层集合的相等；其向内映射与隶属情形逐字相同。
<!--ja-->
相等の原子式が運ぶ関係は `fst v ≡ fst w`、すなわち基底集合の相等であり、その内向きの写しは所属の場合と一言一句変わらない。
<!--/-->

```agda

  cond≐-out : ∀ {n} (t u : Term S n) (z : S)
            → ⟨ (z ∷ []) ⊨ cond (t ≐ u) ⟩
            → ∥ CondAtom t u (λ v w → fst v ≡ fst w) z ∥₁
  cond≐-out t u z = rec₁ squash₁
    (λ { (v , hv) → map₁ (λ { (w , r) → v , (w , r) }) hv })
```

<!--en-->
Its outward mapping is likewise the membership one with the relation exchanged.
<!--zh-->
其向外映射也与隶属情形相同，只是交换了关系。
<!--ja-->
その外向きの写しも所属の場合と同じで、関係を取り替えただけである。
<!--/-->

```agda

  CondQuant : ∀ {n} → Formula S (suc n) → S → Type (ℓ-suc ℓ)
  CondQuant a z = Σ[ x ∈ S ] (⟨ fst x ∈ fst B ⟩
    × (Σ[ e' ∈ S ] (⟨ (e' ∷ x ∷ z ∷ []) ⊨ consAtL zero (suc zero) (suc (suc zero)) ⟩
                    × ⟨ fst e' ∈ fst (Sat a) ⟩)))
```

<!--en-->
For the unbounded existential, the unpacked condition is the Σ-type `CondQuant`: a member `x` of the base, an entry `e'` certified by the extension clause to be the environment `z` extended by `x`, and membership of `e'` in the subformula's set. Again the type is untruncated, and the truncation is added at the helpers.
<!--zh-->
对无界存在量词，展开后的条件是 Σ 类型 `CondQuant`：基的一个成员 `x`、经扩展子句认证为「环境 `z` 添加 `x` 后的扩展」的条目 `e'`、以及 `e'` 属于子公式集合的隶属。该类型同样不带截断，截断在辅助引理处添加。
<!--ja-->
非有界の存在量化子では、展開された条件は Σ 型の `CondQuant` である。基礎の要素 `x`、拡張の節によって環境 `z` に `x` を加えた拡張であると証明される項目 `e'`、そして `e'` の部分式の集合への所属である。ここでも型は切り詰めを帯びず、切り詰めは補題で加えられる。
<!--/-->

```agda

  cond∃-in : ∀ {n} (a : Formula S (suc n)) (z : S)
           → ∥ CondQuant a z ∥₁ → ⟨ (z ∷ []) ⊨ cond (∃̇ a) ⟩
  cond∃-in a z = map₁ (λ { (x , (x∈ , (e' , r))) → x , (x∈ , ∣ e' , r ∣₁) })
```

<!--en-->
Inward folds the extension data into the single truncated witness that the existential's own quantifier provides.
<!--zh-->
向内映射把扩展数据折进存在量词自身提供的那一个截断见证之中。
<!--ja-->
内向きの写しは、拡張のデータを、存在量化子自身が与える一つの切り詰められた証人へ折りたたむ。
<!--/-->

```agda

  cond∃-out : ∀ {n} (a : Formula S (suc n)) (z : S)
            → ⟨ (z ∷ []) ⊨ cond (∃̇ a) ⟩ → ∥ CondQuant a z ∥₁
  cond∃-out a z = rec₁ squash₁
    (λ { (x , (x∈ , hv)) → map₁ (λ { (e' , r) → x , (x∈ , (e' , r)) }) hv })
```

<!--en-->
Outward unfolds the two nested truncated witnesses in turn; both goals are truncations and therefore propositions, so the unfolding is legitimate.
<!--zh-->
向外依次展开两层嵌套的截断见证；两个目标都是截断、因而是命题，展开因此合法。
<!--ja-->
外向きには、入れ子になった二つの切り詰められた証人を順に展開する。どちらの目標も切り詰め、したがって命題なので、展開は正当である。
<!--/-->

```agda

  cond∀-in : ∀ {n} (a : Formula S (suc n)) (z : S)
           → ((x e' : S) → ⟨ fst x ∈ fst B ⟩
              → ⟨ (e' ∷ x ∷ z ∷ []) ⊨ consAtL zero (suc zero) (suc (suc zero)) ⟩
```

<!--en-->
For every permitted value and its certified extension, the premise supplies membership in the subformula's satisfaction set.
<!--zh-->
对每个允许的取值及其经过认证的扩展，前提给出该扩展属于子公式的满足集合。
<!--ja-->
許された各値と証明された拡張について、前提はその拡張が部分式の充足集合に属すことを与える。
<!--/-->

```agda
              → ⟨ fst e' ∈ fst (Sat a) ⟩)
           → ⟨ (z ∷ []) ⊨ cond (∀̇ a) ⟩
  cond∀-in a z k x x∈ e' hc = k x e' x∈ hc
```

<!--en-->
For the unbounded universal, the unpacked condition is a function assigning to every base member and its extension the subformula's truth at that extension. Inward and outward are that one function read in the two directions of the quantifier.
<!--zh-->
对无界全称，展开后的条件是一个函数：给基的每个成员连同其扩展，指派子公式在该扩展处的真值。向内与向外是同一个函数沿量词两个方向的读法。
<!--ja-->
非有界の全称では、展開された条件は関数である。基礎の各要素とその拡張に対して、その拡張での部分式の真理値を割り当てる。内向きと外向きは、量化子の二つの向きで読んだ同じ関数である。
<!--/-->

```agda

  cond∀-out : ∀ {n} (a : Formula S (suc n)) (z : S)
            → ⟨ (z ∷ []) ⊨ cond (∀̇ a) ⟩
            → ((x e' : S) → ⟨ fst x ∈ fst B ⟩
```

<!--en-->
Reading the condition outward retains the value from `B` and the environment obtained by adjoining it.
<!--zh-->
向外读取条件时，保留取自 `B` 的值，以及把该值添入后得到的环境。
<!--ja-->
条件を外向きに読むとき、`B` から取った値と、それを付け加えて得た環境を保つ。
<!--/-->

```agda
               → ⟨ (e' ∷ x ∷ z ∷ []) ⊨ consAtL zero (suc zero) (suc (suc zero)) ⟩
               → ⟨ fst e' ∈ fst (Sat a) ⟩)
  cond∀-out a z h x e' x∈ hc = h x x∈ e' hc
```

<!--en-->
No truncation appears, because satisfaction of a universal is verified by supplying its verifier, which is exactly what both directions do.
<!--zh-->
这里不出现截断，因为全称的满足靠给出验证者来完成，而两个方向做的恰是这件事。
<!--ja-->
ここに切り詰めは現れない。全称の充足は検証者を与えることで確かめられ、二つの方向はともにまさにそれを行うからである。
<!--/-->

```agda

  CondBnd : ∀ {n} → Formula S (suc n) → S → S → Type (ℓ-suc ℓ)
  CondBnd a z w = Σ[ x ∈ S ] ((⟨ fst x ∈ fst B ⟩ × ⟨ fst x ∈ fst w ⟩)
    × (Σ[ e' ∈ S ]
        (⟨ (e' ∷ x ∷ w ∷ z ∷ []) ⊨ consAtL zero (suc zero) (suc (suc (suc zero))) ⟩
         × ⟨ fst e' ∈ fst (Sat a) ⟩)))
```

<!--en-->
The bounded quantifiers add one layer. The condition quantifies, in order, the value `w` of the bounding term, a member `x` of the base lying in `w`, and the extension `e'` of the environment `z` by `x`, certified by the extension clause and required to belong to the subformula's set. The role of `w` is auxiliary: it carries the bound's value, while the environment of the subformula is `e'`, which adds exactly one entry, the member `x`, to the environment `z`.
<!--zh-->
有界量词多出一层。条件依次量化：界项的取值 `w`、落在 `w` 中的基成员 `x`、以及环境 `z` 添加 `x` 后的扩展 `e'`，后者由扩展子句认证，并要求属于子公式的集合。`w` 的角色是辅助性的：它承载界的取值，而子公式 `a` 的环境是 `e'`，后者恰给环境 `z` 增加一个条目，即成员 `x`。
<!--ja-->
有界の量化子は一層加わる。条件が順に量化するのは、界の項の値 `w`、`w` の内側にある基礎の要素 `x`、そして環境 `z` に `x` を加えた拡張 `e'` である。`e'` は拡張の節が証明し、部分式の集合に属することが要求される。`w` の役割は補助である。境界の値を運ぶのは `w` であり、部分式の環境は `e'`、すなわち環境 `z` に要素 `x` をちょうど一つ加えたものである。
<!--/-->

```agda

  cond∃∈-in : ∀ {n} (t : Term S n) (a : Formula S (suc n)) (z : S)
            → ∥ (Σ[ w ∈ S ] (⟨ (w ∷ z ∷ []) ⊨ tmIs t zero (suc zero) ⟩
                             × ∥ CondBnd a z w ∥₁)) ∥₁
            → ⟨ (z ∷ []) ⊨ cond (∃̇∈ t a) ⟩
```

<!--en-->
The bounded existential stacks its witnesses: the outer truncation is over the value `w` of the bounding term, and inside it sits the inner truncation of `CondBnd a z w`, holding the carrier member and its extension.
<!--zh-->
有界存在把见证叠放起来：外层截断针对界项的取值 `w`，其内是 `CondBnd a z w` 的内层截断，装着载体成员及其扩展。
<!--ja-->
有界の存在量化は証人を重ねる。外側の切り詰めは界の項の値 `w` の上にあり、その内側に `CondBnd a z w` の内側の切り詰め、すなわち台の要素とその拡張が収まる。
<!--/-->

```agda
  cond∃∈-in t a z = map₁
    (λ { (w , (hw , hx)) → w , (hw , map₁
      (λ { (x , ((x∈B , x∈w) , (e' , r))) → x , (x∈B , (x∈w , ∣ e' , r ∣₁)) })
      hx) })
```

<!--en-->
The first `map₁` eliminates the outer truncation over `w`, and the nested `map₁` eliminates the inner truncation of `CondBnd`, folding the member and the extension into the existential's own quantifier. Both goals are truncations and hence propositions, so the two eliminations are legitimate for the same reason.
<!--zh-->
第一个 `map₁` 消去 `w` 上的外层截断，嵌套的 `map₁` 消去 `CondBnd` 的内层截断，把成员与扩展折进存在量词自身的量词之中。两个目标都是截断、因而都是命题，两次消去的合法性同出一源。
<!--ja-->
最初の `map₁` が `w` の上の外側の切り詰めを消去し、入れ子の `map₁` が `CondBnd` の内側の切り詰めを消去して、要素と拡張を存在量化子自身の量化の中へ折りたたむ。どちらの目標も切り詰め、したがって命題なので、二つの消去が正当な理由は同じである。
<!--/-->

```agda

  cond∃∈-out : ∀ {n} (t : Term S n) (a : Formula S (suc n)) (z : S)
             → ⟨ (z ∷ []) ⊨ cond (∃̇∈ t a) ⟩
             → ∥ (Σ[ w ∈ S ] (⟨ (w ∷ z ∷ []) ⊨ tmIs t zero (suc zero) ⟩
                              × ∥ CondBnd a z w ∥₁)) ∥₁
```

<!--en-->
The outward statement exposes the same two-layer shape: the value of the bound on the outside, and within it the truncated record of the carrier member and its extension.
<!--zh-->
向外陈述暴露出同样的两层形状：外层是界项的取值，其内是截断的「载体成员及其扩展」之记录。
<!--ja-->
外向きの主張は、同じ二層の形をそのまま見せる。外側に境界の値、その内側に切り詰められた、台の要素とその拡張の記録である。
<!--/-->

```agda
  cond∃∈-out t a z = map₁
    (λ { (w , (hw , hx)) → w , (hw , rec₁ squash₁
      (λ { (x , (x∈B , (x∈w , hv))) → map₁
        (λ { (e' , r) → x , ((x∈B , x∈w) , (e' , r)) }) hv })
      hx) })
```

<!--en-->
Its proof unfolds the two layers in turn, the whole journey remaining inside truncation.
<!--zh-->
其证明依次展开这两层，整个过程都留在截断之内。
<!--ja-->
その証明はこの二層を順に展開する。行程のすべてが切り詰めの内側にとどまる。
<!--/-->

```agda

  cond∀∈-in : ∀ {n} (t : Term S n) (a : Formula S (suc n)) (z : S)
            → ((w : S) → ⟨ (w ∷ z ∷ []) ⊨ tmIs t zero (suc zero) ⟩
               → (x e' : S) → ⟨ fst x ∈ fst B ⟩ → ⟨ fst x ∈ fst w ⟩
```

<!--en-->
The two guards require `x` to belong both to the base `B` and to the value `w` of the bounding term.
<!--zh-->
两道约束要求 `x` 同时属于基集合 `B` 与界项的取值 `w`。
<!--ja-->
二つの条件は、`x` が基礎集合 `B` と境界項の値 `w` の両方に属すことを要求する。
<!--/-->

```agda
               → ⟨ (e' ∷ x ∷ w ∷ z ∷ [])
                    ⊨ consAtL zero (suc zero) (suc (suc (suc zero))) ⟩
               → ⟨ fst e' ∈ fst (Sat a) ⟩)
            → ⟨ (z ∷ []) ⊨ cond (∀̇∈ t a) ⟩
  cond∀∈-in t a z k w hw x x∈B x∈w e' hc = k w hw x e' x∈B x∈w hc
```

<!--en-->
The bounded universal's condition is a function over the three quantified layers: to every value `w` of the bounding term it assigns, for every base member `x` inside `w` and every extension `e'` certified as the environment `z` extended by `x`, the subformula's truth at `e'`. The inward mapping is that function, applied.
<!--zh-->
有界全称的条件是量化三层的函数：对界项的每个取值 `w`，对 `w` 内的每个基成员 `x` 与每份认证为「环境 `z` 添加 `x` 后的扩展」的 `e'`，指派子公式在 `e'` 处的真值。向内映射就是这个函数被应用的样子。
<!--ja-->
有界の全称の条件は、三層に量化された関数である。界の項の値 `w` のそれぞれに対して、`w` の内側の基礎の各要素 `x` と、環境 `z` に `x` を加えた拡張であると証明された各 `e'` について、`e'` での部分式の真理値を割り当てる。内向きの写しは、その関数を適用した姿である。
<!--/-->

```agda

  cond∀∈-out : ∀ {n} (t : Term S n) (a : Formula S (suc n)) (z : S)
             → ⟨ (z ∷ []) ⊨ cond (∀̇∈ t a) ⟩
             → ((w : S) → ⟨ (w ∷ z ∷ []) ⊨ tmIs t zero (suc zero) ⟩
```

<!--en-->
The result ranges over the same bound value, base member, and certified one-entry extension.
<!--zh-->
结论量化同一个界值、基集合成员，以及经过认证的单条目扩展。
<!--ja-->
結論は、同じ境界の値、基礎集合の要素、証明された一項の拡張にわたって量化する。
<!--/-->

```agda
                → (x e' : S) → ⟨ fst x ∈ fst B ⟩ → ⟨ fst x ∈ fst w ⟩
                → ⟨ (e' ∷ x ∷ w ∷ z ∷ [])
                     ⊨ consAtL zero (suc zero) (suc (suc (suc zero))) ⟩
                → ⟨ fst e' ∈ fst (Sat a) ⟩)
  cond∀∈-out t a z h w hw x e' x∈B x∈w hc = h w hw x x∈B x∈w e' hc


```

<!--en-->
The outward mapping is the same function, read back through the three quantifiers. No truncation appears in either direction, since a universal is verified by supplying its verifier, and here the verifier is supplied layer by layer, for the value, for the member, and for the extension.
<!--zh-->
向外映射是同一个函数，沿三个量词反向读出。两个方向都不出现截断：全称的验证靠供给其验证者完成，而这里验证者是一层一层供给的，为取值、为成员、也为扩展。
<!--ja-->
外向きの写しは同じ関数を、三つの量化子を通して逆向きに読んだものである。どちらの方向にも切り詰めは現れない。全称の検証は検証者を与えることで完了し、ここでは値に対して、要素に対して、そして拡張に対して、層ごとに検証者が与えられるのである。
<!--/-->
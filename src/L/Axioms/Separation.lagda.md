```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
# Separation and replacement, bounded
<!--zh-->
# 有界分离与替换
<!--ja-->
# 有界な分出公理と置換公理
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )
```

<!--en-->
We therefore fix a universe level `ℓ` and a host-level hypothesis
`lem : LEM (ℓ-suc ℓ)`. This parameter remains explicit in the type of every resulting theorem. The fixed-stage argument itself will use
definability, transitivity, and Δ₀ absoluteness constructively; the classical
dependency appears when arbitrary constants, the source set, or selected image
values are assigned canonical least stage indices.
<!--zh-->
因此固定宇宙层级 `ℓ`，并取宿主层假设 `lem : LEM (ℓ-suc ℓ)`。由此得到的每条定理都在类型中显式保留这一参数。固定层上的论证只以构造方式使用可定义性、传递性与 Δ₀ 绝对性；当任意常元、源集合或选定的像值被指派典范的最早层索引时，经典依赖才实际出现。
<!--ja-->
そこで宇宙レベル `ℓ` とホスト側の仮定 `lem : LEM (ℓ-suc ℓ)` を固定する。ここから得られる各定理は、その型にこの仮定を明示的に保つ。固定した段階での議論は、定義可能性、推移性、Δ₀ 絶対性だけを構成的に使う。古典的な依存が実際に現れるのは、任意の定数、始集合、または選ばれた像の値に、正準な最小段階の添字を割り当てるときである。
<!--/-->

```agda
module L.Axioms.Separation {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

```agda
open import FOL.ZFStructure using ( Transitive; module hPropStructure )
open import FOL.Syntax
  using ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∈; δ-∧; δ-∃∈ )
open import FOL.Manipulation.ConstantBounding
  using ( BoundedTm; BoundedFo; BoundedTm-mono; BoundedFo-mono; module Relabel )
open import FOL.Manipulation.ConstantMapping using ( mapFo )
open import FOL.Manipulation.Relabelling using ( ⊨-map )
import FOL.Semantics
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-layer; layer-trans; Lset-mono
        ; 𝒟ₒ; 𝒟ₒ-intro; Lset→isL )
open import L.Ordinal {ℓ} using ( ∅-ord; boundingOrd; bound2 )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Axioms.Basic {ℓ} using ( LsetS; 𝒟ₒ→isL; uniqueL )
```

<!--en-->
Bounded separation asks for more than a host-level subtype of a constructible
set `a`. It asks for an element of the constructible model whose members are
exactly those `x ∈ a` satisfying a given Δ₀ formula. Bounded replacement asks
for the corresponding set of values of a functional Δ₀ relation. The proof of
both statements will move the relevant data into one ordinal stage, form a
definable subset there, and compare that stage calculation with satisfaction
in the whole constructible model.
<!--zh-->
有界分离所求的不只是可构造集 `a` 的一个宿主层子类型，而是可构造模型中的一个元素，其成员恰为 `a` 中满足给定 Δ₀ 公式的 `x`。有界替换所求的则是函数性 Δ₀ 关系的取值所成之集。两项证明都会先把有关数据放入同一个序数层，在层内形成可定义子集，再把这项层内计算与整个可构造模型中的满足关系比较。
<!--ja-->
有界な分出公理が求めるのは、構成可能集合 `a` のホスト側の部分型だけではない。`a` に属し、与えられた Δ₀ 論理式を満たす `x` だけを要素とする、構成可能モデルの要素を求める。有界な置換公理は、関数的な Δ₀ 関係の値からなる集合を求める。どちらの証明でも、関係するデータを一つの順序数段階へ入れ、その段階で定義可能部分集合を作り、この段階内の計算を構成可能モデル全体での充足関係と比較する。
<!--/-->

<!--en-->
Two kinds of logic must remain separate from the outset. Formulas and their
quantifiers belong to the object language interpreted by the model. The
statement that a truth value is decidable belongs to the host theory. We assume excluded middle at the successor universe level; it enters through the operation that assigns a constructible set its least containing stage. This assumption is neither an axiom asserted inside `L` nor a choice principle.
<!--zh-->
从一开始就须区分两层逻辑。公式及其量词属于由模型解释的对象语言；真值可判定这一陈述则属于宿主理论。我们假设后继宇宙层级上的排中律；这项假设经由「为可构造集指派包含它的最早层」这一运算进入证明。它既不是 `L` 内部断言的公理，也不是选择原则。
<!--ja-->
初めから二つの論理の層を区別する必要がある。論理式とその量化子は、モデルが解釈する対象言語に属する。真理値が決定可能であるという主張はホスト理論に属する。後続宇宙レベルの排中律を仮定する。この仮定は、構成可能集合を含む最小の層を割り当てる操作を通して証明に入る。これは `L` の内部で主張される公理でも、選択原理でもない。
<!--/-->



<!--en-->
The object language makes the first notion of boundedness precise. A formula
`φ : Formula S n` may contain constants from the model carrier `S` and has `n`
free-variable slots. A certificate `Δ₀ φ` says that every quantifier occurring
in `φ` is bounded by a term. Membership atoms are Δ₀, conjunction preserves
the property, and bounded existential quantification preserves it. These three
closure facts make the separation and image formulas Δ₀.
<!--zh-->
对象语言使第一种有界性得到精确定义。公式 `φ : Formula S n` 可以含有来自模型载体 `S` 的常元，并有 `n` 个自由变元槽位。证书 `Δ₀ φ` 表示 `φ` 中出现的每个量词都由一个词项界定。隶属原子是 Δ₀ 的，合取保持这一性质，有界存在量化也保持这一性质。这三项封闭性保证分离公式与像公式仍是 Δ₀ 的。
<!--ja-->
対象言語によって、第一の有界性が正確に定まる。論理式 `φ : Formula S n` はモデルの台 `S` の要素を定数として含むことができ、`n` 個の自由変数の位置をもつ。証明 `Δ₀ φ` は、`φ` に現れるすべての量化子が項によって有界であることを表す。所属の原子論理式は Δ₀ であり、連言と有界存在量化はこの性質を保つ。この三つの閉性によって、分出の論理式と像の論理式も Δ₀ になる。
<!--/-->

<!--en-->
A different notion of boundedness controls constants. `BoundedTm P t` and
`BoundedFo P φ` say that every constant occurring in a term or formula satisfies
the host-level predicate `P`. They say nothing about whether the formula's
quantifiers are bounded, so `mkBoundedFo` applies even to formulas that
are not Δ₀. Relabelling uses such a certificate to replace each constant by an
index in a chosen stage, and the mapping lemmas compare satisfaction before and
after that syntactic change.
<!--zh-->
另一种有界性约束常元。`BoundedTm P t` 与 `BoundedFo P φ` 表示词项或公式中出现的每个常元都满足宿主层谓词 `P`。它们并不说明公式中的量词是否有界，所以 `mkBoundedFo` 也适用于非 Δ₀ 公式。给定这种证书，改名会把每个常元换成所选层中的一个索引；映射引理则比较这项语法变换前后的满足关系。
<!--ja-->
もう一つの有界性は定数を制約する。`BoundedTm P t` と `BoundedFo P φ` は、項または論理式に現れるすべての定数がホスト側の述語 `P` を満たすことを表す。論理式の量化子が有界かどうかについては何も述べないので、`mkBoundedFo` は Δ₀ でない論理式にも適用できる。この証明を使うと、改名によって各定数を選んだ段階の添字に置き換えられ、写像に関する補題によって、その構文上の変更の前後で充足関係を比較できる。
<!--/-->

<!--en-->
Why move constants into one stage? A stage `Lset σ` has a small presentation,
so formulas defining its subsets use indices from that presentation as their
constants. The original formula instead uses arbitrary elements of `S` as
constants. Once those constants have been relabelled, `DefOf (Lset σ)` can form
the subset selected by the formula inside the ambient cumulative hierarchy;
the constructibility results can then package that subset as an element of the
model. The remaining task is to prove that this stage-defined subset has the
same members as the original formula specifies in `L`.
<!--zh-->
为何要把常元移入同一个层？层 `Lset σ` 有一个小呈现，所以定义其子集的公式以该呈现中的索引为常元；原公式却以 `S` 的任意元素为常元。完成改名之后，`DefOf (Lset σ)` 可以在外围累积层级中形成该公式选出的子集，再由可构造性结果把这个子集包装成模型元素。余下的问题是证明：这个在层内定义的子集，与原公式在 `L` 中指定的成员完全相同。
<!--ja-->
なぜ定数を一つの段階へ移すのであろうか。段階 `Lset σ` には小さな提示があるため、その部分集合を定義する論理式は、この提示の添字を定数として使う。これに対して元の論理式は、`S` の任意の要素を定数として使う。改名した後では、`DefOf (Lset σ)` が、その論理式で選ばれる部分集合を周囲の累積階層の中で作り、構成可能性に関する結果がそれをモデルの要素として組み立てる。残る課題は、この段階で定義した部分集合の要素が、元の論理式が `L` で指定する要素と正確に一致することを証明することである。
<!--/-->

<!--en-->
The hierarchy supplies two scales of ordinal bounds. `bound2` puts two stage
indices inside a common ordinal, while `boundingOrd` does the same for a family
indexed by a small type. Monotonicity then moves stage membership to the common
bound. The operation `stage` assigns each constructible set the least stage
index whose layer contains it; only this least-stage operation in this
construction uses `lem`. At the other end, `uniqueL` uses the model's set
extensionality to prove uniqueness from a pointwise
membership specification.
<!--zh-->
层级工具提供两种规模的序数上界。`bound2` 把两个层索引置于一个共同序数之内，`boundingOrd` 则对由小类型索引的一族层索引作同样处理；层的单调性随后把成员关系提升到共同上界。运算 `stage` 为每个可构造集指派一个最早层索引，使相应的层包含该集合；在这项构造中，只有这个最早层运算使用 `lem`。另一端的 `uniqueL` 使用模型的集合外延性，从逐点成员规格证明唯一性。
<!--ja-->
階層に関する道具は、二つの規模の順序数上界を与える。`bound2` は二つの段階の添字を一つの共通の順序数の中へ置き、`boundingOrd` は小さな型で添字づけられた族について同じことを行う。その後、段階の単調性によって所属を共通上界まで持ち上げる。操作 `stage` は、各構成可能集合に、それを含む最小の段階の添字を割り当てる。この構成では、この最小段階の操作だけが `lem` を使う。もう一方の端では、`uniqueL` がモデルの集合外延性を使い、各点での所属の仕様から一意性を証明する。
<!--/-->

<!--en-->
Several kinds of equality have different roles here. `⇔toPath` applies
proposition extensionality to turn two implications into a path between
proposition-valued truth values. `Σ≡Prop` lifts equality of underlying sets to
equality of model elements because constructibility certificates form a
proposition. Set extensionality enters separately through `uniqueL`. Finally,
propositional truncation records that a witness exists without retaining a
chosen witness; its eliminator is used only when the target is again a
proposition.
<!--zh-->
这里的几种相等各有不同作用。`⇔toPath` 使用命题外延性，把两个方向的蕴含化为命题值真值之间的路径。由于可构造性证书构成命题，`Σ≡Prop` 把底层集合的相等提升为模型元素的相等。集合外延性则另经 `uniqueL` 进入。最后，命题截断只记录见证存在而不保留一个选定见证；仅在目标仍是命题时使用其消去子。
<!--ja-->
ここで使ういくつかの等しさは、役割が異なる。`⇔toPath` は命題外延性を使い、二方向の含意を命題値の真理値の間のパスへ変える。構成可能性の証明が命題をなすため、`Σ≡Prop` は基礎にある集合の等しさをモデル要素の等しさへ持ち上げる。集合外延性は、これとは別に `uniqueL` を通して使われる。最後に、命題的切り詰めは、選ばれた証人を保持せずに証人の存在だけを記録する。その除去子は、行き先が再び命題である場合にだけ使う。
<!--/-->

<!--en-->
Small presentations connect model membership with the small index types needed
by ordinal bounding and stage definability. For a cumulative-hierarchy set `A`,
the type `⟪ A ⟫` indexes its represented members and `⟪ A ⟫↪` returns the set
named by an index. Conversely, `∈-asFiber` turns a membership proof `x ∈ A`
into an index together with a path from its represented set to `x`. The
construction uses that untruncated fibre data locally; no representative is
extracted from propositional truncation.
<!--zh-->
小呈现把模型成员关系与序数界定及层内可定义性所需的小索引类型连接起来。对累积层级中的集合 `A`，类型 `⟪ A ⟫` 为其呈现的成员编索引，`⟪ A ⟫↪` 返回某索引所指名的集合。反过来，`∈-asFiber` 把成员证明 `x ∈ A` 化为一个索引，以及从其呈现值到 `x` 的路径。构造在局部直接使用这份未经截断的纤维数据；这里没有从命题截断中抽取代表。
<!--ja-->
小さな提示は、モデルの所属を、順序数による上界と段階での定義可能性に必要な小さな添字型へ結びつける。累積階層の集合 `A` に対して、型 `⟪ A ⟫` は提示された要素を添字づけ、`⟪ A ⟫↪` は添字が名指す集合を返す。逆に、`∈-asFiber` は所属の証明 `x ∈ A` を、添字と、その提示された集合から `x` へのパスへ変える。この構成は、切り詰められていないファイバーのデータを局所的に使う。命題的切り詰めから代表を取り出すことはない。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ∈-asFiber; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
```

<!--en-->
The proposition-valued structure on `L` has carrier `S`. An
element `x : S` is a dependent pair consisting of an ambient set `fst x` and a
proof `snd x` that this set is constructible. Thus `S` is the carrier type of
the model, not a set called `L`; its equality and membership are read from the
underlying sets and take values in `hProp`.
<!--zh-->
`L` 上的命题值结构以 `S` 为模型载体。元素 `x : S` 是一个依值对，由外围集合 `fst x` 与证明该集合可构造的 `snd x` 组成。因此，`S` 是模型的载体类型，并不是一个名为 `L` 的集合；其相等与成员关系从底层集合读取，并取值于 `hProp`。
<!--ja-->
`L` 上の命題値構造の台を `S` とする。要素 `x : S` は、周囲の集合 `fst x` と、その集合が構成可能であることの証明 `snd x` からなる依存対である。したがって `S` はモデルの台の型であり、`L` という名の集合ではない。その等しさと所属は基礎にある集合から読み取られ、`hProp` に値を取る。
<!--/-->

```agda
open hPropStructure 𝒮ʟ
```

<!--en-->
The axioms ultimately ask this carrier to realize a host-level class
`Q : S → hProp (ℓ-suc ℓ)`. The type `SetOf Q` pairs a model element `b` with,
for every `x : S`, a path `(x ∈ˢ b) ≡ Q x`. In separation, `Q x` will combine
membership in the source with an object-language satisfaction judgment. For
example, if the formula says that `x` belongs to a constant `c`, the desired
extension is the intersection of `a` and `c`. The proof realizes this class by
a set in `L`; it does not identify the class itself with an object-language
formula or assume that the host theory's subtype already belongs to `L`.
<!--zh-->
这些公理最终要求该载体实现一个宿主层类 `Q : S → hProp (ℓ-suc ℓ)`。类型 `SetOf Q` 把模型元素 `b` 与如下规格配成一对：对每个 `x : S`，都有路径 `(x ∈ˢ b) ≡ Q x`。在分离中，`Q x` 会把属于源集合这一条件与一项对象语言满足判断合取起来。例如，若公式表示 `x` 属于常元 `c`，所求外延就是 `a` 与 `c` 的交。证明要用 `L` 中的一个集合实现这个类；它既不把类本身认作对象语言公式，也不假定宿主理论中的子类型已经属于 `L`。
<!--ja-->
これらの公理が最終的に要求するのは、この台がホスト側のクラス `Q : S → hProp (ℓ-suc ℓ)` を実現することである。型 `SetOf Q` は、モデル要素 `b` と、各 `x : S` に対するパス `(x ∈ˢ b) ≡ Q x` を組にする。分出公理では、`Q x` は始集合への所属と対象言語の充足判断を連言で結ぶ。たとえば論理式が `x` は定数 `c` に属すと述べるなら、求める外延は `a` と `c` の共通部分である。証明はこのクラスを `L` の集合によって実現する。クラスそのものを対象言語の論理式と同一視することも、ホスト理論の部分型がすでに `L` に属すと仮定することもない。
<!--/-->

```agda
module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )
```

<!--en-->
The same object-language formula can now be read in two structures. The notation
`γ ⊨v φ` denotes satisfaction in the ambient cumulative hierarchy at an
environment of raw sets, while `γ ⊨ φ` denotes satisfaction in the structure
whose carrier is `S`. Keeping these judgments distinct is
essential: the fixed-stage construction first proves a statement about an
ambiently defined subset, then uses absoluteness to recover the intended
satisfaction judgment in the constructible model.
<!--zh-->
现在，同一条对象语言公式可以在两个结构中读取。记号 `γ ⊨v φ` 表示公式在外围累积层级中、以裸集合环境解释时的满足关系；`γ ⊨ φ` 则表示公式在以 `S` 为载体的结构中的满足关系。这两种判断必须保持区分：固定层构造先证明一个关于外围可定义子集的陈述，再用绝对性恢复可构造模型中所需的满足判断。
<!--ja-->
同じ対象言語の論理式を、二つの構造で読めるようになった。記法 `γ ⊨v φ` は、生の集合からなる割り当てのもとで、周囲の累積階層における充足関係を表す。一方、`γ ⊨ φ` は台が `S` である構造における充足関係を表す。この二つの判断を区別しておくことが必要である。固定した段階での構成は、まず周囲で定義された部分集合についての主張を証明し、その後、絶対性によって構成可能モデルで意図した充足判断を回復する。
<!--/-->

```agda
module SemV = FOL.Semantics 𝒮ᵥ
open SemV.At (V ℓ) id using () renaming ( _⊨_ to _⊨v_ )
```

<!--en-->
The constructible class is transitive: a member of a constructible set is
constructible. This is exactly enough for bounded quantifiers. An ambient
witness lying in the interpretation of a constructible bounding term can be
repackaged as an element of `S`, and an inner witness can be projected back to
its underlying set. Induction on a Δ₀ formula therefore gives `abs₀`, a path
between its ambient and inner truth values. This is Δ₀ absoluteness, not a claim
that `L` or any stage is elementary for arbitrary formulas.
<!--zh-->
可构造类是传递的：可构造集的成员仍可构造。这恰好足以处理有界量词。若一个外围见证属于某个可构造界定词项的解释，就能把它重新包装为 `S` 的元素；反向则可把内层见证投影回其底层集合。于是对 Δ₀ 公式作归纳便得到 `abs₀`，即外围真值与内层真值之间的路径。这是 Δ₀ 绝对性，并不声称 `L` 或任何层对任意公式都是初等的。
<!--ja-->
構成可能クラスは推移的である。構成可能集合の要素は再び構成可能である。これは有界量化子を扱うのにちょうど十分である。構成可能な境界項の解釈に属する周囲の証人は `S` の要素として組み直せ、内側の証人は基礎にある集合へ射影できる。したがって Δ₀ 論理式についての帰納から、その周囲での真理値と内側での真理値の間のパス `abs₀` が得られる。これは Δ₀ 絶対性であり、`L` やいずれかの段階が任意の論理式について初等的であるという主張ではない。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( abs₀ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## The replacement image
<!--zh-->
## 替换的像
<!--ja-->
## 置換による像
<!--/-->

<!--en-->
For replacement, first state the image as a host-level predicate. The truth
value `ReplImage a φ z` says that there merely exists an `x : S` such that
`x ∈ˢ a` and the object-language formula `φ` is satisfied at the environment
`x ∷ z ∷ []`. Here the source occupies slot zero and the candidate value slot
one. The indexed host-level existential uses propositional truncation, so it
forgets which source produced `z`; it is distinct from the object-language
bounded existential `∃̇∈` that defines the same image by a unary formula.
Nothing in this definition requires `φ` to be Δ₀ or the relation to be
functional.
<!--zh-->
对替换，先把像写成宿主层谓词。真值 `ReplImage a φ z` 表示仅仅存在某个 `x : S`，使 `x ∈ˢ a`，并且对象语言公式 `φ` 在环境 `x ∷ z ∷ []` 下成立；此处源占零号槽，候选值占一号槽。这个宿主层索引存在采用命题截断，因此忘去究竟由哪个源产生 `z`；它不同于用一元公式定义同一像时采用的对象语言有界存在 `∃̇∈`。该定义本身既不要求 `φ` 为 Δ₀，也不要求关系具有函数性。
<!--ja-->
置換公理については、まず像をホスト側の述語として述べる。真理値 `ReplImage a φ z` は、ある `x : S` が存在して、`x ∈ˢ a` であり、対象言語の論理式 `φ` が割り当て `x ∷ z ∷ []` で充足されるという事実だけを表す。ここでは始域の要素が第零の位置、値の候補が第一の位置を占める。このホスト側の添字付き存在は命題的切り詰めを使うため、どの始域の要素が `z` を生じたかを忘れる。これは、同じ像を一変数論理式によって定義するときに使う対象言語の有界存在 `∃̇∈` とは別のものである。この定義自体は、`φ` が Δ₀ であることも、関係が関数的であることも要求しない。
<!--/-->

```agda
ReplImage : (a : S) (φ : Formula S 2) → S → hProp (ℓ-suc ℓ)
ReplImage a φ z = ∃[ x ∶ S ] (x ∈ˢ a) ⊓ ((x ∷ z ∷ []) ⊨ φ)
```

<!--en-->
## Bounding a functional image
<!--zh-->
## 界住函数像
<!--ja-->
## 関数的な像を抑える
<!--/-->

<!--en-->
The extra problem in replacement is to find one stage containing every possible
value. `FunctionalImage` treats an arbitrary host-level relation `R` and assumes
that for each `x ∈ˢ a` the fibre `Σ[ y ∶ S ] ⟨ R x y ⟩` is contractible. Thus
the fibre contains a specified centre and every other related pair is equal to
it. This hypothesis supplies existence and uniqueness as data at each source;
projecting its centres is ordinary dependent-function application and uses no
host-level or object-theoretic choice axiom.
<!--zh-->
替换多出的困难，是找到一个容纳所有可能取值的层。`FunctionalImage` 处理任意宿主层关系 `R`，并假设对每个 `x ∈ˢ a`，纤维 `Σ[ y ∶ S ] ⟨ R x y ⟩` 都可缩。因此，该纤维带有一个指定中心，任何其他相关对都与中心相等。这项假设在每个源处以数据形式给出存在性与唯一性；从这些中心作投影只是依值函数应用，不使用宿主层或对象理论的选择公理。
<!--ja-->
置換公理で新たに生じる問題は、可能な値をすべて含む一つの段階を見つけることである。`FunctionalImage` は任意のホスト側の関係 `R` を扱い、各 `x ∈ˢ a` についてファイバー `Σ[ y ∶ S ] ⟨ R x y ⟩` が可縮であると仮定する。したがって、このファイバーには指定された中心があり、ほかのすべての関係する対はその中心に等しくなる。この仮定は、各始域の要素について存在と一意性をデータとして与える。中心を射影することは通常の依存関数の適用であり、ホスト側の選択公理も対象理論の選択公理も使わない。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module FunctionalImage (a : S) (R : S → S → hProp (ℓ-suc ℓ))
                       (fc : (x : S) → ⟨ x ∈ˢ a ⟩
                           → isContr (Σ[ y ∶ S ] ⟨ R x y ⟩)) where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
The type `Mem` packages a source element together with evidence that it belongs
to `a`. This evidence is part of the input expected by the contractible-fibre
hypothesis, so a bare `x : S` would not suffice. Since `S` already lives at the
successor universe level, `Mem` is too large to serve directly as the small
index type required by `boundingOrd`. The canonical small presentation of the
underlying set `fst a` provides a small way to enumerate the source members
needed for the bound.
<!--zh-->
类型 `Mem` 把一个源元素与它属于 `a` 的证据包装在一起。可缩纤维假设要求这份证据作为输入，所以只有一个裸的 `x : S` 并不足够。由于 `S` 已经位于后继宇宙层级，`Mem` 太大，不能直接充当 `boundingOrd` 所需的小索引类型。底层集合 `fst a` 的典范小呈现提供一种小规模的枚举方式，列出构造上界所需的源成员。
<!--ja-->
型 `Mem` は、始域の要素と、それが `a` に属するという証拠を組にする。可縮なファイバーについての仮定はこの証拠を入力として要求するので、単なる `x : S` だけでは足りない。`S` はすでに後続宇宙レベルにあるため、`Mem` は `boundingOrd` が要求する小さな添字型として直接使うには大きすぎる。基礎にある集合 `fst a` の正準な小さな提示は、上界の構成に必要な始域の要素を小さな型で列挙する。
<!--/-->

```agda
  Mem : Type (ℓ-suc ℓ)
  Mem = Σ[ x ∶ S ] ⟨ x ∈ˢ a ⟩
```

<!--en-->
For `p : Mem`, the contractible fibre `fc (p .fst) (p .snd)` already contains
its centre. The function `img` projects the value component of that centre,
giving a definite model element for each certified source member. Although this
looks like choosing values pointwise, no truncated existence is being
eliminated: the centres are explicit components of the supplied dependent
function `fc`.
<!--zh-->
对 `p : Mem`，可缩纤维 `fc (p .fst) (p .snd)` 已经包含其中心。函数 `img` 投影出该中心的值分量，从而为每个带证书的源成员给出一个确定的模型元素。这看似逐点选取取值，却没有消去任何经过截断的存在：这些中心本来就是所给依值函数 `fc` 的显式分量。
<!--ja-->
`p : Mem` に対して、可縮なファイバー `fc (p .fst) (p .snd)` はすでにその中心を含んでいる。関数 `img` は中心の値の成分を射影し、証明付きの各始域の要素に対して一つの確定したモデル要素を与える。これは各点で値を選んでいるように見えるが、切り詰められた存在を除去してはいない。中心は、与えられた依存関数 `fc` の明示的な成分だからである。
<!--/-->

```agda
  img : Mem → S
  img p = fc (p .fst) (p .snd) .fst .fst
```

<!--en-->
The centre contains more than the chosen value. Its second component proves
that `R (p .fst) (img p)` holds, and `img-sat` names this fact.
The distinction matters: `img` supplies an element whose stage can be bounded,
whereas `img-sat` certifies that this selected element is genuinely a value of
the relation at the given source.
<!--zh-->
中心所含的不只是选定值。其第二分量证明 `R (p .fst) (img p)` 成立，`img-sat` 单独命名这项事实。二者的区别很重要：`img` 给出一个可以界定其所在层的元素，`img-sat` 则证明这个选定元素确实是该关系在给定源处的取值。
<!--ja-->
中心が含むのは選ばれた値だけではない。その第二成分は `R (p .fst) (img p)` が成り立つことを証明し、`img-sat` はこの事実に名前を与える。この区別には意味がある。`img` はその段階を抑えられる要素を与え、`img-sat` は、その選ばれた要素が与えられた始域の要素における関係の値であることを証明する。
<!--/-->

```agda
  img-sat : (p : Mem) → ⟨ R (p .fst) (img p) ⟩
  img-sat p = fc (p .fst) (p .snd) .fst .snd
```

<!--en-->
Contractibility also identifies the chosen centre with every competing related
pair `(y , h)`. Applying congruence to the first projection yields
`img p ≡ y`, an equality of complete model elements, including their
constructibility certificates. Placing `img p` in the common stage and
transporting that membership along this equality then covers an
arbitrary `y` satisfying `R (p .fst) y`. Functionality is used source by source;
it does not say that values arising from different sources are distinct.
<!--zh-->
可缩性还把选定中心与每个其他相关对 `(y , h)` 认同起来。对第一投影取合同，便得到 `img p ≡ y`，这是完整模型元素的相等，连同其可构造性证书也包括在内。把 `img p` 放入共同层，再沿这项相等运输成员证明，便可覆盖任意满足 `R (p .fst) y` 的 `y`。函数性逐个源使用；它并不表示不同源产生的值彼此不同。
<!--ja-->
可縮性はまた、選ばれた中心を、ほかのすべての関係する対 `(y , h)` と同一視する。第一射影に合同性を適用すると `img p ≡ y` が得られる。これは構成可能性の証明も含む、モデル要素全体の等しさである。`img p` を共通の段階へ入れ、この等しさに沿って所属の証明を輸送すれば、`R (p .fst) y` を満たす任意の `y` を扱える。関数性は始域の要素ごとに使われる。異なる始域の要素から生じる値が互いに異なるという主張ではない。
<!--/-->

```agda
  img-uniq : (p : Mem) (y : S) → ⟨ R (p .fst) y ⟩ → img p ≡ y
  img-uniq p y h = cong fst (fc (p .fst) (p .snd) .snd (y , h))
```

<!--en-->
To obtain a small indexing family, `memS` starts with an index
`m : ⟪ fst a ⟫`. Its represented set is known to belong to `fst a`. Since `a`
is constructible and the constructible class is transitive, that represented
set is constructible as well, so it can be paired with its certificate to form
an element of `S`. Together with the original membership proof this gives an
element of `Mem`, to which `img` and the fibre hypothesis may be applied.
<!--zh-->
为得到小索引族，`memS` 从索引 `m : ⟪ fst a ⟫` 出发。该索引所呈现的集合已知属于 `fst a`。由于 `a` 可构造且可构造类传递，这个呈现值也可构造，因而能与其证书配成 `S` 的元素；再加上原有的成员证明，就得到 `Mem` 的元素，可以对它应用 `img` 与纤维假设。
<!--ja-->
小さな添字の族を得るために、`memS` は添字 `m : ⟪ fst a ⟫` から始める。この添字が提示する集合は `fst a` に属する。`a` は構成可能であり、構成可能クラスは推移的なので、この提示された集合も構成可能である。したがって、その集合と証明を組にして `S` の要素を作れる。さらに元の所属の証明を加えると `Mem` の要素となり、`img` とファイバーについての仮定を適用できる。
<!--/-->

```agda
  private
    memS : ⟪ fst a ⟫ → Mem
    memS m = (⟪ fst a ⟫↪ m
             , isL-trans fm∈fa (a .snd)) , fm∈fa
      where
```

<!--en-->
The local proof `fm∈fa` supplies the membership component of `memS`. The
canonical presentation states membership first in its small relation, and
`∈∈ₛ` converts that fact to the proposition-valued membership of the cumulative
hierarchy. Applying transitivity to `fm∈fa` and the certificate `a .snd` gives
the constructibility component of `memS`. Thus the same
membership fact both locates the represented set inside the source and permits
it to be packaged as a constructible model element.
<!--zh-->
局部证明 `fm∈fa` 给出 `memS` 的成员分量。典范呈现先在其小成员关系中陈述成员事实，`∈∈ₛ` 再把该事实转换为累积层级中的命题值成员关系。把传递性施于 `fm∈fa` 与证书 `a .snd`，便得到 `memS` 的可构造性分量。因此，同一项成员事实既把呈现值定位在源集合内，也使它能够被包装成可构造模型元素。
<!--ja-->
局所的な証明 `fm∈fa` は、`memS` の所属の成分を与える。正準な提示は、まず小さな所属関係によって所属を述べ、`∈∈ₛ` がその事実を累積階層の命題値の所属へ変換する。`fm∈fa` と証明 `a .snd` に推移性を適用すると、`memS` の構成可能性の成分が得られる。したがって同じ所属の事実が、提示された集合を始集合の中に位置づけると同時に、それを構成可能なモデル要素として組み立てることを可能にする。
<!--/-->

```agda
      fm∈fa : ⟨ ⟪ fst a ⟫↪ m ∈ fst a ⟩
      fm∈fa = ∈∈ₛ {a = ⟪ fst a ⟫↪ m} {b = fst a} .snd (∈ₛ⟪ fst a ⟫↪ m)
```

<!--en-->
The source can now be traversed through the small type `⟪ fst a ⟫`. For each
index `m`, take the least stage index containing the selected value
`img (memS m)` and supply its ordinality by `stage-ord`. The constructive
operation `boundingOrd` returns one ordinal strictly above all these indices.
The common-bound argument uses `stage-ord` and `stage-mem`; minimality is not
needed for the common-bound argument, although it is also provided by the canonical `stage` assignment. If `a` is empty, the index family is empty and
`boundingOrd` still returns an ordinal bound, without asserting that the image
is inhabited.
<!--zh-->
现在可以沿小类型 `⟪ fst a ⟫` 遍历源集合。对每个索引 `m`，取包含选定值 `img (memS m)` 的最早层索引，并以 `stage-ord` 给出其序数性。构造性的运算 `boundingOrd` 返回一个严格高于所有这些索引的序数。共同上界论证使用 `stage-ord` 与 `stage-mem` 所给的事实，而不需要最小性，尽管典范的 `stage` 指派也提供了最小性。若 `a` 为空，索引族也为空，`boundingOrd` 仍返回一个序数上界，却不因此断言像非空。
<!--ja-->
これで、小さな型 `⟪ fst a ⟫` を通して始集合を走査できる。各添字 `m` について、選ばれた値 `img (memS m)` を含む最小の段階の添字を取り、その順序数性を `stage-ord` で与える。構成的な操作 `boundingOrd` は、これらすべての添字より真に上にある一つの順序数を返す。共通上界の議論が使うのは `stage-ord` と `stage-mem` が与える事実であり、最小性は必要ない。ただし、標準的な `stage` の割り当てから最小性も得られる。`a` が空なら添字の族も空であるが、`boundingOrd` はそれでも順序数上界を返し、像に要素があるとは主張しない。
<!--/-->

```agda
    bImg = boundingOrd ⟪ fst a ⟫
      (λ m → stage (fst (img (memS m))) (img (memS m) .snd))
      (λ m → stage-ord (fst (img (memS m))) (img (memS m) .snd))
```

<!--en-->
The first projection of this bounding result is named `βimg`. It is an ordinal
stage index, not the stage itself. The corresponding stage is the cumulative
hierarchy set `Lset βimg`; `range∈βimg` states that the underlying set
of every related value belongs to this stage. Packaging `Lset βimg` as a model
element is a separate operation and requires an ordinality certificate.
<!--zh-->
这一界定结果的第一投影被命名为 `βimg`。它是序数层索引，并非层本身；相应的层是累积层级中的集合 `Lset βimg`。`range∈βimg` 断言每个相关值的底层集合都属于这个层。把 `Lset βimg` 包装成模型元素是另一项独立运算，并且需要序数性证书。
<!--ja-->
この上界の結果の第一射影を `βimg` と名づける。これは順序数である段階の添字であり、段階そのものではない。対応する段階は、累積階層の集合 `Lset βimg` である。`range∈βimg` は、関係するすべての値の基礎にある集合がこの段階に属すことを述べる。`Lset βimg` をモデル要素として組み立てるのは別の操作であり、順序数性の証明を必要とする。
<!--/-->

```agda
  βimg : V ℓ
  βimg = bImg .fst
```

<!--en-->
The second projection of `bImg` certifies both parts of the bound. Its first
part, exposed here as `βimg-ord`, proves that `βimg` is an ordinal; this permits
`Lset βimg` to be packaged as a model element. The remaining part gives, for
every small source index `m`, membership of the selected value's stage index in
`βimg`. Combining that comparison with `stage-mem` places each selected image
in `Lset βimg`. Transport from the represented source to an arbitrary source
member, followed by `img-uniq`, extends the conclusion to every value related
to that member. Ordinality and range containment are therefore distinct claims
extracted from the same bounding construction.
<!--zh-->
`bImg` 的第二投影证明上界的两个部分。其中第一部分在此命名为 `βimg-ord`，证明 `βimg` 是序数；这使 `Lset βimg` 能够被包装成模型元素。余下部分则对每个小源索引 `m`，给出所选值的层索引属于 `βimg` 的证明。把后一项比较与 `stage-mem` 合用，就能把每个选定像放入 `Lset βimg`；再从呈现的源运输到任意源成员，并应用 `img-uniq`，结论便扩展到与该成员相关的每个值。因此，序数性与值域包含是从同一界定构造中取得的两项不同结论。
<!--ja-->
`bImg` の第二射影は、上界の二つの部分を証明する。その第一の部分をここで `βimg-ord` として取り出し、`βimg` が順序数であることを示す。この証明によって、`Lset βimg` をモデル要素として組み立てられる。残る部分は、小さな始域の添字 `m` ごとに、選ばれた値の段階の添字が `βimg` に属することを与える。この比較を `stage-mem` と組み合わせると、選ばれた各像が `Lset βimg` に入る。さらに、提示された始域の要素から任意の始域の要素へ輸送し、`img-uniq` を使うことで、その要素と関係するすべての値へ結論を広げる。したがって、順序数性と値域の包含は、同じ上界の構成から取り出される別々の主張である。
<!--/-->

```agda
  βimg-ord : IsOrd βimg
  βimg-ord = bImg .snd .fst
```

<!--en-->
To bound every value of the relation, fix `x ∈ˢ a`, a candidate `y`, and a proof
of `R x y`. The source membership identifies `x` with a member from the canonical
small presentation of `a`. Functionality then identifies `y` with the chosen value
at that presented member. That chosen value belongs to its canonical stage, whose
index lies strictly below `βimg`; `Lset-mono` therefore places it in `Lset βimg`.
Transport along the value equality gives the required membership for `y`. Thus the
single stage `Lset βimg` contains every value related to a member of `a`. The
canonical stages used earlier depend on `lem`; this final comparison and upward
transport introduce no further classical principle.
<!--zh-->
为界住关系的每个取值，固定 `x ∈ˢ a`、候选值 `y` 以及 `R x y` 的证明。源集成员关系把 `x` 认同为 `a` 的规范小表现中的一个成员；函数性继而把 `y` 认同为该被呈现成员处选定的值。这个选定值属于自己的典范层，而该层的索引严格位于 `βimg` 之下，所以 `Lset-mono` 把它抬入 `Lset βimg`。最后沿取值等式运输，即可得到 `y` 的层成员证明。因此，同一个层 `Lset βimg` 容纳关系作用于 `a` 的成员所得的一切值。前面选取典范层依赖 `lem`；这里的最终比较与向上运输没有引入更多经典原则。
<!--ja-->
関係のすべての値を抑えるため、`x ∈ˢ a`、候補 `y`、および `R x y` の証明を固定する。始集合への所属により、`x` は `a` の標準的な小さい表示から得られる要素と同一視される。関数性はさらに、`y` をその表示された要素で選ばれた値と同一視する。その値は自身の標準的な段階に属し、その添字は `βimg` より真に小さいので、`Lset-mono` によって `Lset βimg` へ持ち上がる。最後に値の等式に沿って輸送すれば `y` の所属が得られる。したがって一つの段階 `Lset βimg` が、`a` の要素から関係によって得られるすべての値を含む。先に標準的な段階を選ぶ部分は `lem` に依存するが、ここでの最後の比較と上方への輸送は新たな古典原理を導入しない。
<!--/-->

```agda
  range∈βimg : (x : S) → ⟨ x ∈ˢ a ⟩ → (y : S) → ⟨ R x y ⟩
              → ⟨ fst y ∈ Lset βimg ⟩
  range∈βimg x x∈a y h = subst (λ w → ⟨ fst w ∈ Lset βimg ⟩) image≡y
    (Lset-mono {α = βimg} {β = stage (fst (img (memS m))) (img (memS m) .snd)}
      (bImg .snd .snd m) (stage-mem (fst (img (memS m))) (img (memS m) .snd)))
```

<!--en-->
The membership fibre supplies both data needed to compare the arbitrary source
with the small presentation. Its first projection is an index `m` of the
presentation of `fst a`; this is data already contained in membership, rather
than a choice from a merely inhabited collection. Its second projection is an
equality between the set presented by `m` and `fst x`. The lemma `Σ≡Prop` lifts
that equality to `memS m .fst ≡ x`, because the second component `isL` of a
model element is proposition-valued and hence cannot distinguish two packages
with the same underlying set.
<!--zh-->
隶属纤维同时给出比较任意源元素与小表现所需的两项数据。第一投影是 `fst a` 的表现中的索引 `m`；它本来就包含在这份成员证明中，并非从一个仅知非空的集合中作选择。第二投影给出 `m` 所呈现的集合与 `fst x` 之间的等式。由于模型元素的第二分量 `isL` 是命题值的，不能区分底层集合相同的两个包裹，`Σ≡Prop` 把这条底层等式提升为 `memS m .fst ≡ x`。
<!--ja-->
所属のファイバーは、任意の始点と小さい表示を比較するための二つのデータを同時に与える。第一射影は `fst a` の表示の添字 `m` である。これは単に要素が存在する集まりから選んだものではなく、所属の証明そのものに含まれるデータである。第二射影は、`m` が表示する集合と `fst x` との等式を与える。モデル要素の第二成分 `isL` は命題値であり、同じ基礎集合をもつ二つの組を区別しないため、`Σ≡Prop`はこの基礎集合の等式を `memS m .fst ≡ x` へ持ち上げる。
<!--/-->

```agda
    where
    m = ∈-asFiber {a = fst x} {b = fst a} x∈a .fst
    q : memS m .fst ≡ x
    q = Σ≡Prop (λ z → snd (isL z))
      (∈-asFiber {a = fst x} {b = fst a} x∈a .snd)
```

<!--en-->
The relation proof originally has source `x`. Transporting it along the inverse
of `q` makes it a proof of `R (memS m .fst) y`, so it lies in the same value
fibre as the centre selected by `fc` at `memS m`. Since that fibre is
contractible, `img-uniq` equates its centre `img (memS m)` with `y`. This is the
precise use of functionality: it compares two values for one fixed source. It
does not assert that different source members have different values.
<!--zh-->
原来的关系证明以 `x` 为源。沿 `q` 的逆路径运输后，它成为`R (memS m .fst) y` 的证明，因而与 `fc` 在 `memS m` 处选定的中心落在同一个取值纤维中。该纤维可缩，所以 `img-uniq` 把中心 `img (memS m)` 与 `y` 等同。这正是函数性的用途：比较同一个固定源的两个取值；它并不断言不同源成员的取值彼此不同。
<!--ja-->
もとの関係の証明は `x` を始点とする。これを `q` の逆向きに沿って輸送すると、`R (memS m .fst) y` の証明になり、`memS m` において `fc` が選んだ中心と同じ値のファイバーに入る。そのファイバーは可縮なので、`img-uniq` は中心`img (memS m)` と `y` を同一視する。関数性が使われるのは、固定した一つの始点に対する二つの値を比較するためである。異なる始点の値が異なるとは主張しない。
<!--/-->

```agda
    image≡y : img (memS m) ≡ y
    image≡y = img-uniq (memS m) y (subst (λ z → ⟨ R z y ⟩) (sym q) h)
```
</div>
</details>

<!--en-->
## At a fixed stage
<!--zh-->
## 在固定的层上
<!--ja-->
## 固定した段階での構成
<!--/-->

<!--en-->
The fixed-stage argument begins with an ordinal index `σ` and its certificate
`oσ`. The construction `DefC = DefOf (Lset σ)` treats the members of `Lset σ`
through their canonical small presentation. It supplies formulas whose constants
are such presentation indices and the subset `defSet` cut out by each unary
formula. The remaining task is to compare that stage-based definition with
satisfaction in the constructible model.
<!--zh-->
固定层论证从序数索引 `σ` 及其证书 `oσ` 开始。构造 `DefC = DefOf (Lset σ)` 通过 `Lset σ` 的规范小表现处理其成员，并提供以表现索引为常元的公式，以及每条一元公式刻出的子集 `defSet`。余下任务是把这种层内定义与可构造模型中的满足关系作精确比较。
<!--ja-->
固定した段階での議論は、順序数の添字 `σ` とその証明 `oσ` から始まる。構成 `DefC = DefOf (Lset σ)` は、`Lset σ` の要素をその標準的な小さい表示を通して扱う。そして、表示の添字を定数とする論理式と、各一変数論理式が切り出す部分集合 `defSet` を与える。残る課題は、この段階に基づく定義を構成可能モデルでの充足と正確に比較することである。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module AtStage (σ : V ℓ) (oσ : IsOrd σ) where
```
</summary>
<div class="submodule-fold-content">

```agda
  module DefC = DefOf (Lset σ)
```

<!--en-->
Bounded-formula absoluteness requires the class under consideration to be
transitive. Here `DefC.M` is the class of members of `Lset σ`, and
`layer-trans (Lset-layer σ)` proves exactly that a member of one of its members
is again in the stage. Notice that this proof does not use the ordinality
certificate `oσ`: transitivity follows from `Lset-layer σ` itself. This closure
is what keeps witnesses of bounded quantifiers inside the restricted world.
<!--zh-->
有界公式的绝对性要求所考虑的类具有传递性。这里 `DefC.M` 是 `Lset σ` 的成员类，而 `layer-trans (Lset-layer σ)` 恰好证明：其成员的成员仍在该层中。注意，这份证明不使用序数性证书 `oσ`；传递性直接来自 `Lset-layer σ`。正是这种封闭性保证有界量词的见证留在受限世界内。
<!--ja-->
有界論理式の絶対性には、対象となるクラスの推移性が必要である。ここで `DefC.M` は`Lset σ` の要素のクラスであり、`layer-trans (Lset-layer σ)` は、その要素の要素も再び段階内にあることをちょうど証明する。この証明は順序数性の証明 `oσ` を使わない。推移性は `Lset-layer σ` 自体から従う。この閉性によって、有界量化子の証人は制限された世界の内部に留まる。
<!--/-->

```agda
  Atrans : Transitive 𝒮ᵥ DefC.M
  Atrans = layer-trans (Lset-layer σ)
```

<!--en-->
Supplying `Atrans` to `DefC.Refine` makes the bounded-formula comparison available.
The renamed notation `_⊨σ_` denotes the refinement's ambient `V`-valued reading:
stage indices are interpreted by the members they present, and the resulting
formula is evaluated in the surrounding hierarchy. In particular,
`RefC.abs-defSet` will identify membership in a definable subset with this ambient
reading for a `Δ₀` formula. That fact provides the first half of the semantic
bridge below.
<!--zh-->
把 `Atrans` 交给 `DefC.Refine` 后，就可使用有界公式的比较结果。改名后的记号`_⊨σ_` 表示精炼模块给出的外围 `V` 值读法：层索引按其所呈现的成员解释，所得公式在周遭层级中求值。特别地，对 `Δ₀` 公式，`RefC.abs-defSet` 将把属于可定义子集与这种外围读法等同；这构成下述语义桥的前半段。
<!--ja-->
`Atrans` を `DefC.Refine` に与えると、有界論理式を比較する結果が使えるようになる。改名された記法 `_⊨σ_` は、精緻化モジュールが与える周囲の `V` 値の読みを表す。段階の添字を、それが表示する要素として解釈し、得られた論理式を周囲の階層で評価する。特に `Δ₀` 論理式について、`RefC.abs-defSet` は定義可能部分集合への所属をこの周囲の読みと同一視する。これが後の意味論的な橋の前半である。
<!--/-->

```agda
  module RefC = DefC.Refine Atrans
  open RefC.Abs using () renaming ( _⊨ᵛ_ to _⊨σ_ )
```

<!--en-->
The predicate `Below c` says only that the underlying set `fst c` belongs to
`Lset σ`. Its role is to certify the constants occurring in a term or formula:
`BoundedFo Below φ` contains one such certificate for every constant of `φ`.
It says nothing about free-variable assignments or quantified witnesses. The
separate `cover` hypothesis of `carveAt` will later control which satisfying
values lie in the stage.
<!--zh-->
谓词 `Below c` 只表示底层集合 `fst c` 属于 `Lset σ`。它用于证明词项或公式中出现的常元有界：`BoundedFo Below φ` 为 `φ` 的每个常元保存这样一份证书。它不约束自由变元的赋值，也不约束量词见证；稍后 `carveAt` 的另一个假设 `cover`才负责保证满足者落在该层中。
<!--ja-->
述語 `Below c` は、基礎集合 `fst c` が `Lset σ` に属することだけを表す。その役割は項や論理式に現れる定数を証明することであり、`BoundedFo Below φ` は`φ` の各定数についてこの証明を保持する。自由変数への付値や量化された証人を制約するものではない。充足する値が段階内にあることは、後で `carveAt` の別の仮定 `cover` が保証する。
<!--/-->

```agda
  Below : S → Type (ℓ-suc ℓ)
  Below c = ⟨ fst c ∈ Lset σ ⟩
```

<!--en-->
The relabelling `RL` turns each model constant satisfying `Below` into an index
of the small presentation `⟪ Lset σ ⟫`. Its semantic maps are `fst`, from model
elements to underlying sets, and `⟪ Lset σ ⟫↪`, from presentation indices to
the sets they name. For a proof that `fst c ∈ Lset σ`, `∈-asFiber` returns
both the required index and the equality saying that this index names `fst c`.
These two projections establish the commuting triangle needed for correct
relabelling.
<!--zh-->
重标 `RL` 把每个满足 `Below` 的模型常元变成小表现 `⟪ Lset σ ⟫` 的一个索引。它的两条语义映射分别是从模型元素取底层集合的 `fst`，以及从表现索引取其所指集合的 `⟪ Lset σ ⟫↪`。给定 `fst c ∈ Lset σ` 的证明，`∈-asFiber` 同时返回所需索引和「该索引确实指名 `fst c`」的等式。这两个投影建立正确重标所需的交换三角形。
<!--ja-->
付け替え `RL` は、`Below` を満たす各モデル定数を、小さい表示 `⟪ Lset σ ⟫` の添字へ変える。意味論側の二つの写像は、モデル要素から基礎集合を取る `fst` と、表示の添字からそれが指す集合を取る `⟪ Lset σ ⟫↪` である。`fst c ∈ Lset σ` の証明に対して、`∈-asFiber` は必要な添字と、その添字が実際に `fst c` を指すという等式を同時に返す。この二つの射影が、正しい付け替えに必要な可換三角形を与える。
<!--/-->

```agda
  module RL = Relabel {K = S} {K' = ⟪ Lset σ ⟫} {W = V ℓ}
                fst ⟪ Lset σ ⟫↪ Below
                (λ c p → ∈-asFiber {a = fst c} {b = Lset σ} p .fst)
                (λ c p → ∈-asFiber {a = fst c} {b = Lset σ} p .snd)
```

<!--en-->
The bridge compares two satisfaction propositions for the same mathematical
assignment. On the left, every constant of `φ` has first been relabelled to a
presentation index by `RL.liftFo`; `mapFo DefC.ι` then interprets that index as
the member it presents, and `_⊨σ_` evaluates the result in the ambient
hierarchy at `⟪ Lset σ ⟫↪ m`. On the right, the original formula is evaluated
inside the constructible model at the packaged element
`(⟪ Lset σ ⟫↪ m , xL)`. The constant bound `h`, the `Δ₀` proof `dφ`, and the
constructibility proof `xL` justify the three changes of viewpoint.
<!--zh-->
这座桥比较同一数学赋值的两条满足命题。左侧先由 `RL.liftFo` 把 `φ` 的每个常元重标为表现索引，再由 `mapFo DefC.ι` 把索引解释为其所呈现的成员，最后在周遭层级中于 `⟪ Lset σ ⟫↪ m` 求值。右侧则在可构造模型内，于打包后的元素`(⟪ Lset σ ⟫↪ m , xL)` 处求原公式的值。常元界 `h`、`Δ₀` 证明 `dφ` 与可构造性证明 `xL` 分别保证这几次视角转换合法。
<!--ja-->
この橋は、同じ数学的な付値に対する二つの充足命題を比較する。左辺では、まず`RL.liftFo` が `φ` の各定数を表示の添字へ付け替え、`mapFo DefC.ι` がその添字を表示される要素として解釈し、`_⊨σ_` が周囲の階層で `⟪ Lset σ ⟫↪ m` において評価する。右辺では、もとの論理式を構成可能モデルの内部で、組にした要素`(⟪ Lset σ ⟫↪ m , xL)` において評価する。定数の境界 `h`、`Δ₀` の証明 `dφ`、構成可能性の証明 `xL` が、これらの視点の移動を正当化する。
<!--/-->

```agda
  satBridge : (φ : Formula S 1) (h : BoundedFo Below φ) (dφ : Δ₀ φ)
              (m : ⟪ Lset σ ⟫) (xL : ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩)
            → ((⟪ Lset σ ⟫↪ m ∷ []) ⊨σ (mapFo DefC.ι (RL.liftFo φ h)))
              ≡ (((⟪ Lset σ ⟫↪ m , xL) ∷ []) ⊨ φ)
  satBridge φ h dφ m xL =
```

<!--en-->
The first three paths normalize the two successive constant interpretations.
The first `⊨-map` expands the interpretation `DefC.ι` of the stage constants.
The symmetric second application expresses the same reading through the
presentation map `⟪ Lset σ ⟫↪`. The path `RL.liftFo-correct`, placed under
satisfaction by `cong`, then replaces "relabel to an index and name it again"
with direct interpretation by `fst`. This last step is a syntactic formula
equality derived from the commuting triangle in `RL`.
<!--zh-->
前三条路径整理两次相继的常元解释。第一条 `⊨-map` 展开层常元的解释`DefC.ι`；第二条取对称方向，把同一读法改写为经表现映射 `⟪ Lset σ ⟫↪` 的解释。随后把 `RL.liftFo-correct` 置于满足关系下作同余，以直接经 `fst` 解释取代「先重标为索引、再把索引指名回来」。最后这一步是由 `RL` 的交换三角形导出的语法公式等式。
<!--ja-->
最初の三つのパスは、連続する二つの定数解釈を整理する。最初の `⊨-map` は段階の定数解釈 `DefC.ι` を展開する。二番目の適用を逆向きに使うと、同じ読みが表示写像 `⟪ Lset σ ⟫↪` を通す形になる。次に `RL.liftFo-correct` を `cong` によって充足の下へ移し、「添字へ付け替えてから再び指す」解釈を、`fst` による直接の解釈へ置き換える。この最後の段階は `RL` の可換三角形から得られる構文上の論理式の等式である。
<!--/-->

```agda
      ⊨-map 𝒮ᵥ DefC.ι fst (RL.liftFo φ h)
        (⟪ Lset σ ⟫↪ m ∷ [])
    ∙ sym (⊨-map 𝒮ᵥ ⟪ Lset σ ⟫↪ id (RL.liftFo φ h)
             (⟪ Lset σ ⟫↪ m ∷ []))
    ∙ cong (λ ψ → (⟪ Lset σ ⟫↪ m ∷ []) ⊨v ψ) (RL.liftFo-correct φ h)
```

<!--en-->
The fourth path, another `⊨-map`, moves from ambient satisfaction with the
constants and environment read through `fst` to the corresponding formula over
model elements. At that point both the original formula and the packaged
one-element environment are in place. The final path uses `abs₀` in the symmetric
direction: `Δ₀` absoluteness carries ambient truth at the underlying sets back to
truth inside the constructible model. Since the result is an equality of hProps,
later arguments may transport evidence in either direction.
<!--zh-->
第四条路径再次使用 `⊨-map`，把常元与环境都经 `fst` 读取的外围满足改写为模型元素上的相应公式。至此，原公式与打包后的单元素环境都已就位。最后一条路径取`abs₀` 的对称方向：`Δ₀` 绝对性把底层集合处的外围真值带回可构造模型内部的真值。所得结果是两个 hProp 之间的等式，故后续论证可沿任一方向运输证明。
<!--ja-->
第四のパスは再び `⊨-map` を使い、定数と環境をともに `fst` を通して読む周囲での充足を、モデル要素上の対応する論理式へ移す。この時点で、もとの論理式と、組にされた一要素環境がそろう。最後のパスは `abs₀` を逆向きに使う。`Δ₀` 絶対性により、基礎集合における周囲での真理が構成可能モデル内部での真理へ戻る。結果は hProp 間の等式なので、後の議論は証明をどちら向きにも輸送できる。
<!--/-->

```agda
    ∙ ⊨-map 𝒮ᵥ fst id φ (⟪ Lset σ ⟫↪ m ∷ [])
    ∙ sym (abs₀ dφ ((⟪ Lset σ ⟫↪ m , xL) ∷ []))
```

<!--en-->
The desired membership specification can now be stated directly. For a
presented stage member `m`, together with a proof `xL` that its represented set
is constructible, membership in the definable subset cut out by the lifted
formula equals satisfaction of the original formula in `L`. The left side uses
the small presentation of `Lset σ`; the right side packages the same represented
set as a model element. The equality therefore connects the stage construction
to the predicate that separation must realize.
<!--zh-->
现在可以直接陈述所需的成员规格。对层表现中的索引 `m`，并给定其所呈现集合可构造的证明 `xL`，属于提升公式刻出的可定义子集，等同于原公式在 `L` 中得到满足。左侧使用 `Lset σ` 的小表现，右侧则把同一被呈现集合包装为模型元素。这条等式因而把层内构造与分离所要实现的谓词连接起来。
<!--ja-->
必要な所属の仕様をここで直接述べられる。段階の表示の添字 `m` と、それが表す集合が構成可能であるという証明 `xL` に対し、持ち上げた論理式が切り出す定義可能部分集合への所属は、もとの論理式が `L` で充足されることに等しくなる。左辺は`Lset σ` の小さい表示を使い、右辺は同じ表示された集合をモデル要素として組にする。この等式が、段階内の構成を分出が実現すべき述語へ結ぶ。
<!--/-->

```agda
  carveSat : (φ : Formula S 1) (h : BoundedFo Below φ) (dφ : Δ₀ φ)
             (m : ⟪ Lset σ ⟫) (xL : ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩)
           → (⟪ Lset σ ⟫↪ m ∈ DefC.defSet (RL.liftFo φ h))
             ≡ (((⟪ Lset σ ⟫↪ m , xL) ∷ []) ⊨ φ)
  carveSat φ h dφ m xL =
```

<!--en-->
The proof is the composite of two semantic equalities. First,
`RefC.abs-defSet` uses transitivity and the lifted `Δ₀` certificate to identify
membership in `DefC.defSet (RL.liftFo φ h)` with ambient satisfaction of
`mapFo DefC.ι (RL.liftFo φ h)` at the presented member. Then `satBridge`
identifies that ambient proposition with satisfaction of the original formula
inside the constructible model. The order matters: definability reaches the
ambient hierarchy first, and model absoluteness supplies the final link.
<!--zh-->
证明复合两条语义等式。首先，`RefC.abs-defSet` 使用传递性与提升后的 `Δ₀` 证书，把属于 `DefC.defSet (RL.liftFo φ h)` 等同于公式`mapFo DefC.ι (RL.liftFo φ h)` 在被呈现成员处的外围满足。随后 `satBridge` 把这条外围命题等同于原公式在可构造模型内的满足。次序在这里不可颠倒：可定义性先抵达周遭层级，模型绝对性再给出最后一环。
<!--ja-->
証明は二つの意味論的な等式の合成である。まず `RefC.abs-defSet` が、推移性と持ち上げられた `Δ₀` の証明を用いて、`DefC.defSet (RL.liftFo φ h)` への所属を、表示された要素における `mapFo DefC.ι (RL.liftFo φ h)` の周囲での充足と同一視する。次に `satBridge` が、その周囲の命題を、もとの論理式の構成可能モデル内部での充足と同一視する。定義可能性によってまず周囲の階層へ到達し、モデルの絶対性が最後のつながりを与える、という順序が要点である。
<!--/-->

```agda
    RefC.abs-defSet (RL.liftFo φ h) (RL.Δ₀-liftFo h dφ) m ∙ satBridge φ h dφ m xL
```

<!--en-->
The operation `carve` is exactly `DefC.defSet`, now given a stable name for the
rest of the construction. Declaring it opaque changes no set and adds no
existence principle; it only prevents automatic unfolding. Mathematically,
`carve ψ` remains the subset of `Lset σ` selected by the unary formula `ψ` over
the stage's presentation. The following lemmas expose the membership and
constructibility facts needed to use that subset.
<!--zh-->
运算 `carve` 就是 `DefC.defSet`，这里只为后续构造给它一个稳定名称。将其声明为不透明既不改变所得集合，也不加入新的存在原则；它只阻止自动展开。在数学上，`carve ψ` 仍是由层表现上的一元公式 `ψ` 从 `Lset σ` 中选出的子集。以下引理给出使用这个子集所需的成员关系与可构造性事实。
<!--ja-->
演算 `carve` は `DefC.defSet` そのものであり、残りの構成で使うために安定した名前を与えたものである。不透明に指定しても集合は変わらず、新しい存在原理も加わらない。自動的な展開を止めるだけである。数学的には `carve ψ` は引き続き、段階の表示上の一変数論理式 `ψ` が `Lset σ` から選び出す部分集合である。続く補題が、この部分集合を使うために必要な所属と構成可能性の事実を与える。
<!--/-->

```agda
  opaque
    carve : Formula ⟪ Lset σ ⟫ 1 → V ℓ
    carve ψ = DefC.defSet ψ
```

<!--en-->
The formula `ψ` itself witnesses that `carve ψ` is a definable subset of
`Lset σ`. The constructor `𝒟ₒ-intro` expects merely the existence of such a
formula and an extensional equality with its `defSet`, so the explicit pair
`(ψ , refl)` is inserted into propositional truncation as `∣ ψ , refl ∣₁`.
Consequently the particular defining formula is not retained by the membership
proposition `carve ψ ∈ 𝒟ₒ (Lset σ)`. This lemma supplies the premise from
which `𝒟ₒ→isL` will later derive constructibility. This line introduces the
truncation; it does not eliminate it or recover a formula from it.
<!--zh-->
公式 `ψ` 本身见证 `carve ψ` 是 `Lset σ` 的可定义子集。构造子 `𝒟ₒ-intro` 只要求「存在某条公式及其 `defSet` 与目标集合之间的外延等式」，所以显式数据`(ψ , refl)` 以 `∣ ψ , refl ∣₁` 放入命题截断。因此，成员命题`carve ψ ∈ 𝒟ₒ (Lset σ)` 不保留具体是哪条定义公式。这条引理给出前提，稍后`𝒟ₒ→isL` 将由此前提推出可构造性。此行只引入命题截断，并未从中消去或恢复一条公式。
<!--ja-->
論理式 `ψ` 自身が、`carve ψ` が `Lset σ` の定義可能部分集合であることを証言する。構成子 `𝒟ₒ-intro` が要求するのは、そのような論理式と、その `defSet` と対象集合との外延的な等式が単に存在することである。そこで明示的な組 `(ψ , refl)` を`∣ ψ , refl ∣₁` として命題的切り詰めに入れる。その結果、所属命題`carve ψ ∈ 𝒟ₒ (Lset σ)` は、どの論理式が定義したかを保持しない。この補題は、後で `𝒟ₒ→isL` が構成可能性を導くための前提を与える。この行は命題的切り詰めを導入するだけで、そこから論理式を除去して取り出すことはしない。
<!--/-->

```agda
  opaque
    unfolding carve
    carve∈𝒟ₒ : (ψ : Formula ⟪ Lset σ ⟫ 1) → ⟨ carve ψ ∈ 𝒟ₒ (Lset σ) ⟩
    carve∈𝒟ₒ ψ = 𝒟ₒ-intro (Lset σ) (DefC.defSet ψ) ∣ ψ , refl ∣₁
```

<!--en-->
Every definable subset produced by `DefC.defSet` is contained in its ambient
set `Lset σ`. The lemma `carve⊆` records this inclusion for the opaque name:
from `y ∈ carve ψ` it obtains `y ∈ Lset σ` by `DefC.defSet⊆A`. This
containment is independent of whether `y` satisfies any formula in the
constructible model; it follows from the way `defSet` ranges only over the
stage's presented members.
<!--zh-->
`DefC.defSet` 产生的每个可定义子集都包含于其环境集合 `Lset σ`。引理 `carve⊆`为不透明名称记录这条包含：它用 `DefC.defSet⊆A` 从 `y ∈ carve ψ` 得到`y ∈ Lset σ`。这条包含不依赖 `y` 是否在可构造模型中满足某条公式；它来自`defSet` 只遍历该层所呈现成员的定义方式。
<!--ja-->
`DefC.defSet` が作る定義可能部分集合は、すべて周囲の集合 `Lset σ` に含まれる。補題 `carve⊆` は、この包含を不透明な名前について記録する。`DefC.defSet⊆A` によって `y ∈ carve ψ` から `y ∈ Lset σ` を得る。この包含は、`y` が構成可能モデルで何らかの論理式を満たすかどうかには依存しない。`defSet` が段階の表示された要素だけを走るという定義から従う。
<!--/-->

```agda
    carve⊆ : (ψ : Formula ⟪ Lset σ ⟫ 1) (y : V ℓ) → ⟨ y ∈ carve ψ ⟩
           → ⟨ y ∈ Lset σ ⟩
    carve⊆ ψ y mem = DefC.defSet⊆A ψ y mem
```

<!--en-->
The forward reading of `carveSat` turns carved membership into model
satisfaction. Given a presented member in
`carve (RL.liftFo φ h)`, substitution along the hProp equality `carveSat`
produces a proof that the corresponding model element satisfies `φ`. No new
logical implication is proved here: `subst` simply transports an inhabitant
from the left endpoint of the established equality to the right endpoint.
<!--zh-->
`carveSat` 的正向读法把刻出集合的成员证明变成模型中的满足证明。给定一个被呈现成员属于 `carve (RL.liftFo φ h)`，沿 hProp 等式 `carveSat` 作替换，就得到相应模型元素满足 `φ` 的证明。这里没有另证一条逻辑蕴含；`subst` 只是把等式左端的元素运输到右端。
<!--ja-->
`carveSat` の順向きの読みは、切り出された集合への所属をモデルでの充足へ変える。表示された要素が `carve (RL.liftFo φ h)` に属するなら、hProp の等式 `carveSat` に沿う置換によって、対応するモデル要素が `φ` を満たす証明が得られる。ここで新しい論理的含意を証明しているのではない。`subst` は、すでに得た等式の左端の要素を右端へ輸送するだけである。
<!--/-->

```agda
    imageOut : (φ : Formula S 1) (h : BoundedFo Below φ) (dφ : Δ₀ φ)
               (m : ⟪ Lset σ ⟫) (xL : ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩)
             → ⟨ ⟪ Lset σ ⟫↪ m ∈ carve (RL.liftFo φ h) ⟩
             → ⟨ ((⟪ Lset σ ⟫↪ m , xL) ∷ []) ⊨ φ ⟩
    imageOut φ h dφ m xL mem = subst ⟨_⟩ (carveSat φ h dφ m xL) mem
```

<!--en-->
The reverse reading follows the same equality in the opposite direction.
Satisfaction of `φ` by the packaged presented member transports along
`sym (carveSat ...)` to membership in the carved set. Together `imageOut` and
`imageIn` give both directions of the pointwise correspondence, but only for
members represented in the fixed stage. The later `cover` argument is what
allows an arbitrary satisfying model element to be represented there.
<!--zh-->
反向读法沿同一条等式的相反方向进行。打包后的被呈现成员满足 `φ`，沿`sym (carveSat ...)` 运输后便成为刻出集合的成员证明。`imageOut` 与 `imageIn`合起来给出逐点对应的两个方向，但此时只适用于固定层中已被呈现的成员；稍后的`cover` 论证才保证任意满足的模型元素也能在该层中得到表现。
<!--ja-->
逆向きの読みは、同じ等式を反対向きにたどる。組にされた表示要素による `φ` の充足を `sym (carveSat ...)` に沿って輸送すると、切り出された集合への所属が得られる。`imageOut` と `imageIn` は合わせて点ごとの対応の両方向を与えるが、この時点では固定した段階に表示される要素だけが対象である。任意の充足するモデル要素をそこで表示できることは、後の `cover` の議論が保証する。
<!--/-->

```agda
    imageIn : (φ : Formula S 1) (h : BoundedFo Below φ) (dφ : Δ₀ φ)
              (m : ⟪ Lset σ ⟫) (xL : ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩)
            → ⟨ ((⟪ Lset σ ⟫↪ m , xL) ∷ []) ⊨ φ ⟩
            → ⟨ ⟪ Lset σ ⟫↪ m ∈ carve (RL.liftFo φ h) ⟩
    imageIn φ h dφ m xL sat = subst ⟨_⟩ (sym (carveSat φ h dφ m xL)) sat
```

<!--en-->
Satisfaction is insensitive to the proof component carried by a model element.
An equality `fst u ≡ fst v` of underlying sets lifts through `Σ≡Prop` to an
equality `u ≡ v`, because `isL x` is a proposition for every `x`; satisfaction
then transports along the resulting equality of one-element environments. The
argument does not inspect `dφ`, so this transport is mathematically valid for an
arbitrary formula. The `Δ₀` parameter remains in the statement although the proof does not use it, and no use of excluded middle occurs in the proof.
<!--zh-->
满足关系不受模型元素所携证明分量的影响。由于每个 `isL x` 都是命题，底层集合的等式 `fst u ≡ fst v` 经 `Σ≡Prop` 提升为 `u ≡ v`，随后满足证明沿所得单元素环境等式运输。证明体并不查看 `dφ`，所以这条运输在数学上对任意公式都成立；`Δ₀` 参数仍保留在陈述中，尽管证明并未使用它；证明也没有使用排中律。
<!--ja-->
充足は、モデル要素が携える証明成分には依存しない。各 `isL x` は命題なので、基礎集合の等式 `fst u ≡ fst v` は `Σ≡Prop` により `u ≡ v` へ持ち上がり、充足の証明は得られた一要素環境の等式に沿って輸送される。証明本体は `dφ` を参照しないため、この輸送は数学的には任意の論理式について成り立つ。`Δ₀` の引数は証明で使われないまま文に残っており、証明は排中律も使わない。
<!--/-->

```agda
  opaque
    ⊨-transport : (φ : Formula S 1) (dφ : Δ₀ φ) (u v : S) → fst u ≡ fst v
                → ⟨ (u ∷ []) ⊨ φ ⟩ → ⟨ (v ∷ []) ⊨ φ ⟩
    ⊨-transport φ dφ u v p =
      subst (λ z → ⟨ (z ∷ []) ⊨ φ ⟩) (Σ≡Prop (λ x → snd (isL x)) p)
```

<!--en-->
## Separation at a stage
<!--zh-->
## 在一层上分离
<!--ja-->
## 一つの段階で分出する
<!--/-->

<!--en-->
Every index `m : ⟪ Lset σ ⟫` presents an actual member of the stage.
The canonical small-membership proof `∈ₛ⟪ Lset σ ⟫↪ m` is converted by the
second direction of `∈∈ₛ` into the ambient proposition
`⟪ Lset σ ⟫↪ m ∈ Lset σ`. Since `σ` is ordinal, `Lset→isL σ oσ` turns this
stage membership into the constructibility certificate needed to package the
presented set as an element of `S`. This is the point in the fixed-stage
construction where `oσ` is used.
<!--zh-->
每个索引 `m : ⟪ Lset σ ⟫` 都呈现该层的一个实际成员。规范的小成员证明`∈ₛ⟪ Lset σ ⟫↪ m` 经 `∈∈ₛ` 的第二个方向转换成外围命题`⟪ Lset σ ⟫↪ m ∈ Lset σ`。由于 `σ` 是序数，`Lset→isL σ oσ` 再把这份层成员证明转成可构造性证书，从而能把被呈现集合包装为 `S` 的元素。固定层构造正是在这里使用 `oσ`。
<!--ja-->
各添字 `m : ⟪ Lset σ ⟫` は、段階の実際の要素を表示する。標準的な小さい所属の証明 `∈ₛ⟪ Lset σ ⟫↪ m` は、`∈∈ₛ` の第二の向きによって周囲の命題`⟪ Lset σ ⟫↪ m ∈ Lset σ` へ変換される。`σ` は順序数なので、`Lset→isL σ oσ` はこの段階への所属を構成可能性の証明へ変え、表示された集合を `S` の要素として組にできるようにする。固定した段階の構成で `oσ` が使われるのはこの箇所である。
<!--/-->

```agda
  private
    memberIsL : (m : ⟪ Lset σ ⟫) → ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩
    memberIsL m = Lset→isL σ oσ (⟪ Lset σ ⟫↪ m)
      (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m} {b = Lset σ} .snd (∈ₛ⟪ Lset σ ⟫↪ m))
```

<!--en-->
The general fixed-stage construction accepts a unary formula `χ`, a proof that
all its constants satisfy `Below`, a `Δ₀` certificate, and a cover saying that
every model element satisfying `χ` has its underlying set in `Lset σ`. It must
produce a contractible type of realizers for the satisfaction predicate.
`uniqueL` reduces this goal to one explicit model element with a pointwise
membership specification: propositional extensionality turns the two implications
at each `z` into a path of truth values, and set extensionality then gives
uniqueness of the realizing set.
<!--zh-->
固定层的通用构造接收一元公式 `χ`、其全部常元满足 `Below` 的证明、`Δ₀` 证书，以及一条覆盖条件：每个满足 `χ` 的模型元素，其底层集合都属于 `Lset σ`。目标是给出实现该满足谓词的可缩类型。`uniqueL` 把目标化为一个带逐点成员规格的显式模型元素：命题外延性先把每个 `z` 处的双向蕴含变成真值路径，集合外延性再给出实现集合的唯一性。
<!--ja-->
固定した段階での一般構成は、一変数論理式 `χ`、そのすべての定数が `Below` を満たす証明、`Δ₀` の証明、および `χ` を満たす各モデル要素の基礎集合が `Lset σ` に属するという被覆条件を受け取る。目標は、充足述語を実現するものの可縮な型を与えることである。`uniqueL` はこの目標を、点ごとの所属仕様をもつ一つの明示的なモデル要素へ帰着する。命題外延性が各 `z` での二方向の含意を真理値のパスにし、集合外延性が実現する集合の一意性を与える。
<!--/-->

```agda
  carveAt : (χ : Formula S 1) (hχ : BoundedFo Below χ) (dχ : Δ₀ χ)
            (cover : (z : S) → ⟨ (z ∷ []) ⊨ χ ⟩ → ⟨ fst z ∈ Lset σ ⟩)
          → isContr (SetOf (λ z → (z ∷ []) ⊨ χ))
  carveAt χ hχ dχ cover = uniqueL (λ z → (z ∷ []) ⊨ χ) (replElt , spec)
    where
```

<!--en-->
The chosen realizer has underlying set `carve (RL.liftFo χ hχ)`. The bound
`hχ` makes the relabelling of every constant into the stage legitimate, while
`carve∈𝒟ₒ` proves that the resulting `defSet` belongs to the definable powerset
of `Lset σ`. Applying `𝒟ₒ→isL σ oσ` to that membership supplies the second
component of the model element. Thus definability gives existence of a
constructible realizer; its exact extension is established separately by `spec`.
<!--zh-->
选定实现者的底层集合是 `carve (RL.liftFo χ hχ)`。常元界 `hχ` 使每个常元重标入该层成为合法操作，而 `carve∈𝒟ₒ` 证明所得 `defSet` 属于 `Lset σ` 的可定义幂集。把 `𝒟ₒ→isL σ oσ` 施于这份成员证明，就得到模型元素的第二分量。因此，可定义性给出一个可构造实现者的存在；它的精确外延则由另行证明的 `spec` 确定。
<!--ja-->
選ばれた実現要素の基礎集合は `carve (RL.liftFo χ hχ)` である。定数の境界 `hχ` により、各定数を段階へ付け替えることが正当化される。`carve∈𝒟ₒ` は、得られた `defSet` が`Lset σ` の定義可能冪集合に属することを証明する。この所属に `𝒟ₒ→isL σ oσ` を適用すると、モデル要素の第二成分が得られる。したがって定義可能性が構成可能な実現要素の存在を与え、その正確な外延は別に `spec` が証明する。
<!--/-->

```agda
    replElt : S
    replElt = carve (RL.liftFo χ hχ)
            , 𝒟ₒ→isL σ oσ (carve (RL.liftFo χ hχ)) (carve∈𝒟ₒ (RL.liftFo χ hχ))
```

<!--en-->
The specification is a path between membership in `replElt` and satisfaction
of `χ`, for every model element `z`. The forward implication starts with
`z ∈ˢ replElt`. Since the underlying set of `replElt` is the carved set,
`carve⊆` places `fst z` in `Lset σ`; the canonical presentation then supplies
an index `m` naming that set. After transporting carved membership to the
presented representative, `imageOut` yields satisfaction there, and
`⊨-transport` moves it along the underlying-set equality back to `z`.
The cover hypothesis is unnecessary in this direction because carved membership
already provides the required stage bound.
<!--zh-->
规格对每个模型元素 `z` 给出「`z` 属于 `replElt`」与「`z` 满足 `χ`」之间的路径。正向蕴含从 `z ∈ˢ replElt` 开始。由于 `replElt` 的底层集合就是刻出集合，`carve⊆`把 `fst z` 放入 `Lset σ`，规范表现于是给出指名该集合的索引 `m`。将刻出集合的成员证明运输到被呈现代表后，`imageOut` 给出该处的满足证明，`⊨-transport` 再沿底层集合等式把它搬回 `z`。这个方向无需覆盖假设，因为刻出集合的成员关系已经给出所需的层界。
<!--ja-->
仕様は各モデル要素 `z` について、`z` が `replElt` に属することと、`z` が `χ` を満たすこととの間のパスを与える。順向きの含意は `z ∈ˢ replElt` から始まる。`replElt` の基礎集合は切り出された集合なので、`carve⊆` が `fst z` を `Lset σ` に入れ、標準的な表示がその集合を指す添字 `m` を与える。切り出された集合への所属を表示された代表へ輸送すると、`imageOut` がそこでの充足を与え、`⊨-transport` が基礎集合の等式に沿ってそれを `z` へ戻す。この向きでは所属自体から必要な段階の境界が得られるため、被覆仮定は使わない。
<!--/-->

```agda
    spec : (z : S) → (z ∈ˢ replElt) ≡ ((z ∷ []) ⊨ χ)
    spec z = ⇔toPath fwd bwd
      where
      fwd : ⟨ z ∈ˢ replElt ⟩ → ⟨ ((z ∷ []) ⊨ χ) ⟩
      fwd z∈ = ⊨-transport χ dχ (⟪ Lset σ ⟫↪ m , xL) z q (imageOut χ hχ dχ m xL m∈)
```

<!--en-->
The local data make the passage to the canonical presentation explicit.
First `fz∈Lσ` follows from containment of the carved set. Applying `∈-asFiber`
to this membership gives an index `m : ⟪ Lset σ ⟫` and a path
`q : ⟪ Lset σ ⟫↪ m ≡ fst z`. These are the two projections of one membership
fibre, so no choice principle is involved. The path `q` will be used in opposite
directions: first to move carved membership to the presented set, and then to
move satisfaction from the packaged representative back to `z`.
<!--zh-->
这些局部数据把通往规范表现的步骤明确写出。首先，`fz∈Lσ` 来自刻出集合对该层的包含。把 `∈-asFiber` 施于这份成员证明，得到索引 `m : ⟪ Lset σ ⟫` 与路径`q : ⟪ Lset σ ⟫↪ m ≡ fst z`。二者是同一个隶属纤维的两个投影，所以这里不涉及任何选择原则。路径 `q` 将沿相反方向使用两次：先把刻出集合的成员证明移到被呈现集合，再把打包代表处的满足证明搬回 `z`。
<!--ja-->
これらの局所データは、標準的な表示へ移る過程を明示する。まず `fz∈Lσ` は、切り出された集合が段階に含まれることから従う。この所属に `∈-asFiber` を適用すると、添字 `m : ⟪ Lset σ ⟫` とパス `q : ⟪ Lset σ ⟫↪ m ≡ fst z` が得られる。両者は一つの所属ファイバーの二つの射影なので、選択原理は使われない。パス `q`は互いに逆の向きに使われる。まず切り出された集合への所属を表示された集合へ移し、次に組にした代表での充足を `z` へ戻す。
<!--/-->

```agda
        where
        fz∈Lσ = carve⊆ (RL.liftFo χ hχ) (fst z) z∈
        m = ∈-asFiber {a = fst z} {b = Lset σ} fz∈Lσ .fst
        q : ⟪ Lset σ ⟫↪ m ≡ fst z
        q = ∈-asFiber {a = fst z} {b = Lset σ} fz∈Lσ .snd
```

<!--en-->
The forward direction of the specification ends with two steps. The represented
member of the layer is packaged into a model element, its constructibility
coming from the stage itself; and the membership in the carved set, proved for
that represented member, is carried along the naming equation to the original
element. The direction is complete: a member of the carved set satisfies the
formula, in the model, at itself.
<!--zh-->
规格的正向方向以两步收尾。层中被表示的成员被打包成模型元素，其可构造性来自层本身；而对那个被表示成员证得的、对刻出集合的隶属，沿命名等式被搬到原元素身上。该方向完成：刻出集合的成员在模型中、于自身处满足公式。
<!--ja-->
仕様の順方向は、二つの段階で締めくくられる。層の中で表されたメンバーが、モデルの元として梱包され、その構成可能性は段階そのものから来る。そして、その表されたメンバーに対して証明された、刻まれた集合への所属が、名指しの等式に沿って、もとの元へ運ばれる。これで順方向は完成である。刻まれた集合の元は、モデルの中で、自分自身のもとで論理式を満たすのである。
<!--/-->

```agda
        xL = memberIsL m
        m∈ : ⟨ ⟪ Lset σ ⟫↪ m ∈ carve (RL.liftFo χ hχ) ⟩
        m∈ = subst (λ w → ⟨ w ∈ carve (RL.liftFo χ hχ) ⟩) (sym q) z∈
```

<!--en-->
The backward direction begins with the covering hypothesis, and this is the one
place where the covering hypothesis is used: every element satisfying the formula is assumed to lie in the stage. Applying this hypothesis to the given satisfaction proof. The fibre of
the stage membership then recovers the index of a canonical representative.
<!--zh-->
反向方向从覆盖假设开始，此处使用覆盖假设：每个满足公式的元素都位于该层。把这个假设施于给定的满足证明。层隶属的纤维随即恢复出规范代表的索引。
<!--ja-->
逆方向は、覆いの仮定から始まる。ここで覆いの仮定を使う。論理式を満たす各要素はこの段階に属すと仮定されているので、与えられた充足の証明を適用すると。すると、段階への所属の繊維が、標準的な代表の添字を取り戻す。
<!--/-->

```agda
      bwd : ⟨ ((z ∷ []) ⊨ χ) ⟩ → ⟨ z ∈ˢ replElt ⟩
      bwd qz = subst (λ w → ⟨ w ∈ carve (RL.liftFo χ hχ) ⟩) q m∈
        where
        fz∈Lσ = cover z qz
        m = ∈-asFiber {a = fst z} {b = Lset σ} fz∈Lσ .fst
```

<!--en-->
The representative is named by an equation, and the satisfaction is moved to it.
Since satisfaction depends only on the underlying set, the equation between
underlying sets suffices; the representative is packaged as a model element with
its own constructibility, and the formula now holds of the representative
instead of the original.
<!--zh-->
代表由一条等式指名，而满足被搬到它身上。既然满足只依赖底层集合，底层集合之间的等式便已足够；代表被打包成带自身可构造性的模型元素，公式现在对代表成立，而非对原来的元素。
<!--ja-->
代表は一つの等式によって名指され、充足はその代表のところへ移される。充足が底の集合のみに依存するのであるから、底の集合のあいだの等式で十分である。代表は、それ自身の構成可能性を添えて、モデルの元として梱包され、論理式は、もとの元の代わりに、代表について成り立つ。
<!--/-->

```agda
        q : ⟪ Lset σ ⟫↪ m ≡ fst z
        q = ∈-asFiber {a = fst z} {b = Lset σ} fz∈Lσ .snd
        xL = memberIsL m
        satz : ⟨ ((⟪ Lset σ ⟫↪ m , xL) ∷ []) ⊨ χ ⟩
        satz = ⊨-transport χ dχ z (⟪ Lset σ ⟫↪ m , xL) (sym q) qz
```

<!--en-->
The definability implication now applies: the representative satisfies the formula, so
the representative belongs to the carved set; and the naming equation carries
the membership back to the original element. Both directions are complete, and
the specification is, at every element, an equality of two propositions:
belonging to the carved realization, and satisfying the formula in the model.
<!--zh-->
现在使用可定义性的正向蕴含：代表满足公式，于是代表属于刻出的集合；命名等式再把这份隶属搬回原元素。两个方向均已完备，而规格在每个元素处都是两条命题的相等：属于刻出的实现，与在模型中满足公式。
<!--ja-->
ここで定義可能性の順方向を使う。代表は論理式を満たすので、代表は刻まれた集合に属する。そして名指しの等式が、この所属をもとの元へ運び戻す。両方向がそろい、仕様は、すべての元において、二つの命題の相等となる。刻まれた実現への所属と、モデルの中で論理式を満たすこととの相等である。
<!--/-->

```agda
        m∈ : ⟨ ⟪ Lset σ ⟫↪ m ∈ carve (RL.liftFo χ hχ) ⟩
        m∈ = imageIn χ hχ dχ m xL satz
```

<!--en-->
Separation at a stage specializes the preceding construction to subsets. Its hypothesis is
that the source set already lies in the stage; its formula is the conjunction of
membership in the source with the given formula, which is bounded because a
membership atom is bounded and conjunctions preserve boundedness, and its
constants are bounded because the source was supplied below the stage and the
formula's constants came certified. The fixed-stage theorem then returns exactly the
contractible realization that the model field's separation asks for.
<!--zh-->
层上分离把前面的构造专用于子集。其假设为：源集合已在层内；其公式是「属于源」与给定公式的合取，因隶属原子有界、合取保持有界而成为有界公式；其常元有界，因为源被供在层下、公式的常元带着证书。于是固定层定理返回的恰是模型字段的分离所要的那份可缩实现。
<!--ja-->
段階での分出は、先の構成を部分集合に特化したものである。仮定は、始集合がすでに段階の中にあるということ。その論理式は、「始集合への所属」と与えられた論理式との連言であり、所属の原子が有界であり、連言が有界性を保つので、有界な論理式である。定数も有界である。始集合が段階の下に供給され、論理式の定数には証明書が付いていたからである。こうして固定段階の定理は、モデルの欄の分出が求める、ちょうどあの可縮な実現を返す。
<!--/-->

```agda
  separateAt : (a : S) (fa∈σ : ⟨ fst a ∈ Lset σ ⟩)
               (φ : Formula S 1) (h : BoundedFo Below φ) (dφ : Δ₀ φ)
             → isContr (SetOf (λ x → (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)))
  separateAt a fa∈σ φ h dφ =
    carveAt ((var zero ∈̇ con a) ∧̇ φ) ((tt* , fa∈σ) , h) (δ-∧ δ-∈ dφ)
```

<!--en-->
The covering hypothesis of the fixed-stage theorem is discharged by the first conjunct
alone. An element satisfying the conjunction satisfies membership in the source,
the source lies in the stage, and the stage is transitive, so the element lies
in the stage as well. This is the mathematical reason the membership conjunct of
the separation predicate is not decoration: it is what brings every candidate
under the stage within which the subset is being carved.
<!--zh-->
固定层定理的覆盖假设只由第一个合取项即可解除。满足该合取的元素满足「属于源」，而源落在层中、层又传递，于是元素也落在层中。这正是分离谓词中隶属合取项并非装饰的数学缘由：是它把每个候选带进了正在刻出子集的那一层之内。
<!--ja-->
固定段階の定理の覆いの仮定は、最初の連言だけによって解除される。連言を満たす元は「始集合への所属」を満たし、始集合は段階の中にあり、段階は推移的である。ゆえにその元も段階の中にある。分出の述語における所属の連言が飾りではない数学的理由は、これである。切り出そうとしている層の内側へ、すべての候補を運び込むのが、この連言なのである。
<!--/-->

```agda
      (λ z q → layer-trans (Lset-layer σ) {x = fst a} {y = fst z} (q .fst) fa∈σ)
```
</div>
</details>

<!--en-->
## Finding the stage
<!--zh-->
## 找到那一层
<!--ja-->
## 論理式を収める段階を求める
<!--/-->

<!--en-->
To compare bounds chosen independently, the stage condition is parameterized by its ordinal index. The predicate has the same mathematical content as before: an element's underlying set belongs to the layer named by the index. A single chosen stage therefore becomes a variable stage over which the subsequent search may quantify.
<!--zh-->
为了比较彼此独立选出的界，层条件改为以序数指标为参数。这个谓词的数学内容与前面相同：元素的底集属于该索引所指名的层。这样，原先选定的单个层便成为变量，随后的搜索可以在各层之间量化。
<!--ja-->
独立に選ばれた上界を比較するため、層の条件を順序数の添字でパラメータ化する。その数学的内容は先ほどと同じで、元の底の集合が添字の指す層に属するということである。こうして、先に選んだ一つの層を変数として扱い、後の探索で層について量化できるようになる。
<!--/-->

```agda
Below′ : V ℓ → S → Type (ℓ-suc ℓ)
Below′ σ c = ⟨ fst c ∈ Lset σ ⟩
```

<!--en-->
The first lifting lemma moves a term's boundedness along the indices. If one
stage index precedes another, then every constant lying under the first lies
under the second, by the strict growth of the tower; and the boundedness
certificate of a term is carried to the larger index by applying this
pointwise at each constant. The term itself is unchanged; only the proof of boundedness is transported.
<!--zh-->
第一条提升引理沿指标搬运词项的有界性。若一个层指标先于另一个，则凡落在第一层之下的常元也落在第二层之下，这由塔的严格增长保证；而词项的有界性证书通过在每个常元处逐点施加这条单调性，被搬到更大的指标上。词项本身保持不变；被搬运的只有其有界性证明。
<!--ja-->
最初の持ち上げの補題は、項の有界性を指標に沿って運ぶ。ある段階の指標が別の指標に先行すれば、第一の層の下にある定数はすべて、第二の層の下にもある。塔の狭い増大によるものである。そして項の有界性の証明書は、各定数ごとにこの点ごとの単調性を施すことで、より大きな指標へ運ばれる。項そのものは変わらず、有界性の証明だけが輸送される。
<!--/-->

```agda
liftTmTo : {σ β : V ℓ} → ⟨ σ ∈ β ⟩ → ∀ {n} (t : Term S n)
         → BoundedTm (Below′ σ) t → BoundedTm (Below′ β) t
liftTmTo {σ} {β} σ∈β t h =
  BoundedTm-mono {P = Below′ σ} {Q = Below′ β}
    (λ (c : S) h' → Lset-mono {α = β} {β = σ} σ∈β {x = fst c} h') t h
```

<!--en-->
The second lifting lemma does the same for formulas: a formula whose constants
all lie under one stage index keeps that property under any later index. The
proof applies the term lemma at every constant position of the formula. With the
two lifting lemmas, a boundedness proof obtained at one stage can be transported to any later stage chosen for the remaining data.
<!--zh-->
第二条提升引理对公式做同样的事：一条所有常元都落在某层指标之下的公式，在任何更晚的指标之下仍保持该性质。证明在公式的每个常元位置施加词项引理。有了这两条提升引理，在一个层上得到的有界性证明，可以搬运到为其余数据选定的任何更后层。
<!--ja-->
第二の持ち上げの補題は、論理式について同じことをする。すべての定数がある段階の指標の下にある論理式は、それより後のどんな指標の下でも、その性質を保つ。証明は、論理式のすべての定数の位置で、項の補題を施すものである。この二つの持ち上げの補題があれば、ある段階で得た有界性の証明を、残りのデータのために選んだ任意の後の段階へ輸送できる。
<!--/-->

```agda
liftFoTo : {σ β : V ℓ} → ⟨ σ ∈ β ⟩ → ∀ {n} (φ : Formula S n)
         → BoundedFo (Below′ σ) φ → BoundedFo (Below′ β) φ
liftFoTo {σ} {β} σ∈β φ h =
  BoundedFo-mono {P = Below′ σ} {Q = Below′ β}
    (λ (c : S) h' → Lset-mono {α = β} {β = σ} σ∈β {x = fst c} h') φ h
```

<!--en-->
The search for a constant bound starts at terms, and the two cases could hardly
be more different. A constant is bounded by its own earliest stage, with the
ordinality of that index and the membership of the constant in its layer. A variable contains no constants, so the empty stage is returned with a vacuous proof; there is no constant to bound, and the result makes no claim that a variable's value belongs to the empty set.
<!--zh-->
常元之界的搜索从词项开始，而两种情形迥异。常元以自己的最早层为界，连同该指标的序数性以及该常元在其层中的隶属。变元不含常元，于是返回空层与平凡成立的证明；这里没有需要定界的常元，也不声称变元的取值属于空集。
<!--ja-->
定数の上界の探索は項から始まり、二つの場合は明確に異なる。定数には、それ自身が初めて属する層を上界として、その添字の順序数性と定数の所属証明を添える。変数は定数を含まないため、空の層と自明な証明を返す。ここには上界を求めるべき定数がなく、変数の値が空集合に属すとは主張しない。
<!--/-->

```agda
mkBoundedTm : ∀ {n} (t : Term S n) → Σ[ σ ∶ V ℓ ] (IsOrd σ × BoundedTm (Below′ σ) t)
mkBoundedTm (con c) = stage (fst c) (c .snd)
                    , (stage-ord (fst c) (c .snd) , stage-mem (fst c) (c .snd))
mkBoundedTm (var i) = ∅ , (∅-ord , _)
```

<!--en-->
The merger of two search results is stated once, generically, for any two kinds
of certificates that can be lifted along the indices. Its input is a pair of
results, each an ordinal index with its ordinality and a certificate; its output
is one result at a common index, with both certificates carried there. The two
lifting operations are parameters, so the same construction applies to two terms, two formulas, or a term and a formula.
<!--zh-->
两份搜索结果的合并被一次性、一般地陈述，适用于任何可沿指标提升的两种证书。其输入是一对结果，各自是一个序数指标带其序数性与一份证书；其输出是公共指标处的一个结果，两份证书都被搬运到位。两个提升操作作为参数传入，故同一构造可用于两个词项、两个公式，或一个词项与一个公式。
<!--ja-->
二つの探索結果をまとめる操作は、一度だけ、一般的に述べられる。指標に沿って持ち上げられるどんな二種類の証明書にも対応する。入力は、結果の対である。おのおの、順序数の指標とその順序数性と、証明書。出力は、共通の指標における一つの結果で、二つの証明書がともにそこへ運ばれる。持ち上げの二つの操作がパラメータなので、同じ構成を、二つの項、二つの論理式、または項と論理式に適用できる。
<!--/-->

```agda
private
  mkBounded : ∀ {ℓc ℓd} {C : V ℓ → Type ℓc} {D : V ℓ → Type ℓd}
            → (liftC : {σ β : V ℓ} → ⟨ σ ∈ β ⟩ → C σ → C β)
            → (liftD : {σ β : V ℓ} → ⟨ σ ∈ β ⟩ → D σ → D β)
            → (r₁ : Σ[ σ ∶ V ℓ ] (IsOrd σ × C σ))
```

<!--en-->
The common-bound construction has three steps. It takes the bound of the two
indices, which is an ordinal above both; it records that the first index
precedes the bound and the second does too; and it applies the two lifting
operations along these inclusions, so both certificates describe the common
index. No property of the certificates is used beyond their liftable shape.
<!--zh-->
公共界的构造分为三步。取两个指标的界，即高于两者的一个序数；记录第一指标先于该界、第二指标亦然；沿这两条包含关系施加两个提升操作，使两份证书都描述公共指标。除「可提升的形状」之外，没有使用证书的任何性质。
<!--ja-->
共通上界の構成は三段階からなる。二つの指標の限界を取る。それは両方の上にある順序数である。第一の指標がその限界に先行し、第二もそうであることを記録する。そして、この二つの包含関係に沿って、持ち上げの操作を施し、二つの証明書がともに共通の指標を述べるようにする。証明書について使われるのは、持ち上げられるという形だけであり、それ以外の性質は何も使わない。
<!--/-->

```agda
            → (r₂ : Σ[ σ ∶ V ℓ ] (IsOrd σ × D σ))
            → Σ[ σ ∶ V ℓ ] (IsOrd σ × (C σ × D σ))
  mkBounded liftC liftD r₁ r₂ = b .fst , (b .snd .fst ,
      ( liftC (b .snd .snd .fst) (r₁ .snd .snd)
      , liftD (b .snd .snd .snd) (r₂ .snd .snd) ))
```

<!--en-->
The bound itself is the ordinal chapter's merge of two ordinals: an ordinal that
each of the two precedes. This is the only ordinal-theoretic fact needed by this recursion, and it is constructive; the classical parameter does not enter
here, but only earlier, where each constant's earliest stage was named.
<!--zh-->
界本身是序数一章对两个序数的合并：一个被两者皆先于的序数。这是这项递归所需的唯一序数论事实，而且它是构造性的；经典参数不在此处进入，而是更早，在每个常元的最早层被指名之处。
<!--ja-->
限界そのものは、順序数の章による、二つの順序数の合併である。どちらの順序数もそれに先行するような順序数である。これが、この再帰に必要な唯一の順序数論的事実であり、構成的なものである。古典的なパラメータが入り込むのはここではなく、もっと早く、各定数の最も早い段階が名指されたところなのである。
<!--/-->

```agda
    where
    b  = bound2 (r₁ .fst) (r₂ .fst) (r₁ .snd .fst) (r₂ .snd .fst)
```

<!--en-->
The search over formulas recurses on the syntax. The two atomic forms merge the
bounds of their two terms. Each propositional connective merges the bounds of
its two subformulas. In every case the merger just described does the work, and
the boundedness proofs are transported to the common index.
<!--zh-->
公式之上的搜索沿语法递归。两种原子形式合并其两个词项的界。每个命题联结词合并其两个子公式的界。每种情形都由刚才描述的合并器完成工作，而有界性证明被搬运到公共指标。
<!--ja-->
論理式の上の探索は、構文を再帰する。二つの原子的な形は、それぞれの二つの項の限界をまとめる。命題の結合子は、その二つの部分論理式の限界をまとめる。いずれの場合も、仕事をするのは、先ほどのまとめ役であり、有界性の証明は共通の添字へ輸送される。
<!--/-->

```agda
mkBoundedFo : ∀ {n} (φ : Formula S n) → Σ[ σ ∶ V ℓ ] (IsOrd σ × BoundedFo (Below′ σ) φ)
mkBoundedFo (t ∈̇ u) = mkBounded (λ σ∈β → liftTmTo σ∈β t) (λ σ∈β → liftTmTo σ∈β u) (mkBoundedTm t) (mkBoundedTm u)
mkBoundedFo (t ≐ u) = mkBounded (λ σ∈β → liftTmTo σ∈β t) (λ σ∈β → liftTmTo σ∈β u) (mkBoundedTm t) (mkBoundedTm u)
mkBoundedFo (φ ∧̇ ψ) = mkBounded (λ σ∈β → liftFoTo σ∈β φ) (λ σ∈β → liftFoTo σ∈β ψ) (mkBoundedFo φ) (mkBoundedFo ψ)
mkBoundedFo (φ ∨̇ ψ) = mkBounded (λ σ∈β → liftFoTo σ∈β φ) (λ σ∈β → liftFoTo σ∈β ψ) (mkBoundedFo φ) (mkBoundedFo ψ)
```

<!--en-->
The remaining cases are instructive in their asymmetry. The false formula has no constants, so the empty stage is a bound. An unbounded quantifier has the same constant bound as its body: the quantifier itself
introduces no constant, so the recursion passes underneath it untouched. A bounded quantifier also contains its bounding term: its bounding term names a constant, so the
term's bound and the body's bound are merged.
<!--zh-->
余下的情形因其不对称而富有教益。假公式没有常元，所以空层就是一个界。无界量词与其公式体有相同的常元界：量词自身不引入常元，递归从其下方原样通过。有界量词还含有界定词项：其界定词项指名一个常元，故词项的界与公式体的界要合并。
<!--ja-->
残りの場合は、その非対称が教訓的である。偽の論理式は定数を含まないので、空の段階が上界になる。非有界量化子の定数の上界は、本体の上界と同じである。量化子そのものは定数をひとつも導入しないので、再帰は、その下を何も触れずに通過する。有界量化子は、さらにその限定項を含む。その範囲を定める項が一つの定数を名指すので、項の限界と本体の限界とをまとめるのである。
<!--/-->

```agda
mkBoundedFo (φ ⇒̇ ψ) = mkBounded (λ σ∈β → liftFoTo σ∈β φ) (λ σ∈β → liftFoTo σ∈β ψ) (mkBoundedFo φ) (mkBoundedFo ψ)
mkBoundedFo ⊥̇        = ∅ , (∅-ord , _)
mkBoundedFo (∃̇ φ)    = mkBoundedFo φ
mkBoundedFo (∀̇ φ)    = mkBoundedFo φ
mkBoundedFo (∀̇∈ t φ) = mkBounded (λ σ∈β → liftTmTo σ∈β t) (λ σ∈β → liftFoTo σ∈β φ) (mkBoundedTm t) (mkBoundedFo φ)
```

<!--en-->
The bounded existential behaves like the bounded universal: the bound of the
bounding term is merged with the bound of the body. One property of the whole
search deserves emphasis, because it separates two independent notions: the recursion
inspects only constants, so it succeeds on formulas with unbounded quantifiers
as well. A certificate produced here therefore says nothing about whether a
formula is bounded; the two notions, constants-under-a-stage and
bounded-quantifiers, remain separate throughout.
<!--zh-->
有界存在与有界全称量词行为一致：界定词项的界与公式体的界合并。整个搜索的一条性质值得强调，因为它区分了两个彼此独立的概念：这场递归只检查常元，所以对含无界量词的公式同样成功。因此这里产出的证书对「公式是否有界」不置一词；「常元落在某层之下」与「量词皆有界」这两个概念全程各自独立。
<!--ja-->
有界存在は、有界全称量化子と同じふるまいをする。範囲を定める項の限界と、本体の限界とがまとめられる。この探索全体の性質のうち、二つの独立した概念を分けるものを強調しておく。この再帰が調べるのは定数だけである。だから、非有界な量化子を含む論理式に対しても、うまく行く。したがって、ここで産み出される証明書は、論理式が有界かどうかについて何も語らない。定数がある段階の下にあることと、量化子が有界であることは、終始、別々の概念なのである。
<!--/-->

```agda
mkBoundedFo (∃̇∈ t φ) = mkBounded (λ σ∈β → liftTmTo σ∈β t) (λ σ∈β → liftFoTo σ∈β φ) (mkBoundedTm t) (mkBoundedFo φ)
```

<!--en-->
## Δ₀ separation
<!--zh-->
## Δ₀ 分离
<!--ja-->
## Δ₀ 分出公理
<!--/-->

<!--en-->
Bounded separation is now stated in full. For a source set and any unary formula
all of whose quantifiers are bounded, the predicate "member of the source and
satisfying the formula" has a contractible realization by a model element. The
proof is one application of the fixed-stage separation theorem, after the stage has been computed.
<!--zh-->
有界分离至此完整陈述。对一个源集合与任何一元公式，只要其量词皆有界，「是源的成员且满足公式」这条谓词就有模型元素给出的可缩实现。证明只需应用一次固定层分离定理，在层算好之后。
<!--ja-->
有界な分出が、いま、完全な形で述べられる。始集合と、量化子がすべて有界であるような一変数論理式に対して、「始集合の要素であり論理式を満たす」という述語は、モデルの元による可縮な実現をもつ。段階を定めた後、固定段階での分出定理を一度適用する。
<!--/-->

```agda
separateΔ₀ : (a : S) (φ : Formula S 1) → Δ₀ φ
           → isContr (SetOf (λ x → (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)))
separateΔ₀ a φ dφ = AtStage.separateAt σ oσ a fa∈σ φ h dφ
  where
  rφ = mkBoundedFo φ
```

<!--en-->
The stage is computed from two bounds. The search just constructed bounds the constants of the formula, while the established stage assignment gives the earliest stage containing the source set. The two indices are merged, and the formula's certificate is lifted to the merge. At the resulting common stage, both the formula's constants and the source lie below the chosen bound.
<!--zh-->
这个层由两个界共同确定。刚构造的搜索为公式中的常元给出一界，而既有的层指派给出容纳源集合的最早层。合并两个指标后，再把公式的证书提升到合并所得的层；于是公式的常元与源集合都落在同一个界之下。
<!--ja-->
この層は二つの上界から定まる。先に構成した探索が論理式の定数を抑える上界を与え、既に得られている層の割り当てが始集合を含む最初の層を与える。二つの添字を併合し、論理式の証明書をその層まで持ち上げる。これにより、論理式の定数と始集合は同じ上界の下に置かれる。
<!--/-->

```agda
  sa = stage (fst a) (a .snd)
  bb = bound2 (rφ .fst) sa (rφ .snd .fst) (stage-ord (fst a) (a .snd))
  σ  = bb .fst
  oσ = bb .snd .fst
  h  = liftFoTo {σ = rφ .fst} {β = σ} (bb .snd .snd .fst) φ (rφ .snd .snd)
```

<!--en-->
The source's own placement is recorded separately: it lies in its earliest
layer, and the merge's recorded inclusion lifts that membership to the common
stage. This supplies the covering hypothesis of the fixed-stage theorem. It follows directly from the monotonicity of the tower and the certificate supplied by the stage assignment.
<!--zh-->
源自身的位置单独处理：它属于自己的最早层，而合并所得的包含关系把这份隶属提升到公共层。这便给出固定层定理所需的覆盖假设，只用到塔的单调性与层指派所附的证书。
<!--ja-->
始集合自身の位置は別に扱う。始集合はそれが初めて現れる層に属し、併合から得られる包含関係によって、この所属を共通の層まで持ち上げる。これが固定層の定理に必要な被覆の仮定であり、塔の単調性と層の割り当てに伴う証明書から直接得られる。
<!--/-->

```agda
  fa∈σ : ⟨ fst a ∈ Lset σ ⟩
  fa∈σ = Lset-mono {α = σ} {β = sa} (bb .snd .snd .snd) (stage-mem (fst a) (a .snd))
```

<!--en-->
## Δ₀ replacement
<!--zh-->
## Δ₀ 替换
<!--ja-->
## Δ₀ 置換公理
<!--/-->

<!--en-->
Bounded replacement is stated with its functionality hypothesis explicit. For a
source, a binary formula all of whose quantifiers are bounded, and the
assumption that each member's fibre of related values is contractible, the image
predicate has a contractible realization by a model element. The proof transports realizability along an equality of predicates. Functionality is used to bound the related values; once that bound is known, ordinary separation collects the image.
<!--zh-->
有界替换连同其函数性假设一并陈述。给定源集合、一条量词皆有界的二元公式，并假设每个源成员所对应的值构成可缩纤维，像谓词便有模型元素给出的可缩实现。证明沿谓词的相等搬运可实现性：函数性用来为相关值取得共同的界，得到这个界后，再由普通的分离收集其像。
<!--ja-->
有界な置換は、その関数性の仮定とともに述べられる。始集合と、量化子がすべて有界な二変数論理式を取り、各要素に対応する値の繊維が可縮であると仮定する。このとき、像の述語はモデルの元による可縮な実現をもつ。証明は述語の相等に沿って実現可能性を輸送する。関数性によって関連する値に共通の上界を与え、その上界を得た後は通常の分出によって像を集める。
<!--/-->

```agda
replaceΔ₀ : (a : S) (φ : Formula S 2) → Δ₀ φ
          → ((x : S) → ⟨ x ∈ˢ a ⟩ → isContr (Σ[ y ∶ S ] ⟨ (x ∷ y ∷ []) ⊨ φ ⟩))
          → isContr (SetOf (ReplImage a φ))
replaceΔ₀ a φ dφ fc =
  subst (λ Q → isContr (SetOf Q)) (sym Q≡)
```

<!--en-->
The functional-image bound is applied with the source in the first slot of the relation. It gives the common image stage with its ordinality and its covering fact. Full
bounded separation is then applied at that stage, packaged as a model element,
to the unary image formula; the formula's boundedness evidence is the bounded
existential case, since the only quantifier added is bounded by the source.
<!--zh-->
函数像定界定理按关系的第一槽为源的次序应用，给出公共像层连同其序数性与覆盖事实。随后，在该层打包成模型元素之处，对一元像公式施用完整的有界分离；该公式的有界性证据是有界存在的情形，因为唯一添入的量词被源所界。
<!--ja-->
関数像の上界に関する定理を、関係の第一の位置を始域とする順序で適用すると、共通の像の段階、その順序数性、覆いの事実が得られる。そして、その段階をモデルの元として梱包したところで、一変数の像の論理式に対して、完全な有界分出が施される。この論理式の有界性の証拠は、有界存在の場合のものである。加わった量化子は一つだけで、それが源によって有界にされているからである。
<!--/-->

```agda
    (separateΔ₀ (LsetS βimg βimg-ord) imageFo (δ-∃∈ dφ))
  where
  module I = FunctionalImage a (λ x y → (x ∷ y ∷ []) ⊨ φ) fc
  open I using ( βimg; βimg-ord; range∈βimg )
```

<!--en-->
The unary image formula has the following semantics. It says, in the object
language, that some member of the source relates to the outer candidate, and the
bounded existential pushes that member into the first environment slot. The
bounded existential here is the object language's own quantifier; the outer
existence of the image predicate is the host level's truncated existence. The
two agree in meaning through the semantics, but they are not the same syntactic
object, and distinguishing them makes the next equality precise.
<!--zh-->
一元像公式具有如下语义。它以对象语言说：源的某个成员与外侧候选相关，而有界存在把那个成员推进环境的第一个槽。此处的有界存在是对象语言自己的量词；像谓词的外层存在则是宿主层面的截断存在。两者经语义而意义相符，却不是同一个句法对象；区分二者，才能精确陈述下一条相等。
<!--ja-->
一変数の像の論理式の意味は次のとおりである。それは、対象言語でこう言う。始集合のどこかのメンバーが、外側の候補と関係づけられる、と。そして有界存在が、そのメンバーを環境の最初の枠へ押し込む。ここでの有界存在は、対象言語自身の量化子である。一方、像の述語の外側の存在は、ホストレベルの切り詰められた存在である。二者は意味においては意味論を通して一致するが、同じ統語的な対象ではない。両者を区別することで、次の等式を正確に述べられる。
<!--/-->

```agda
  imageFo : Formula S 1
  imageFo = ∃̇∈ (con a) φ
```

<!--en-->
The guarded predicate collects what the construction can verify: the candidate
lies in the packaged common image stage, and it satisfies the unary image
formula. The stage-membership conjunct provides a bound for Separation. The other conjunct describes the actual image, so the stage condition can later be removed using the covering theorem.
<!--zh-->
带守卫的谓词收集构造所能核验的东西：候选者落在打包好的公共像层中，并且满足那条一元像公式。层成员这一合取项为分离提供一个界，另一个合取项描述真正的像；因此，随后可借覆盖定理去掉层条件。
<!--ja-->
守衛つきの述語は、構成が検証できるものを集める。候補が、梱包された共通の像の段階の中にあり、一変数の像の論理式を満たす、ということ。段階への所属を表す連言は分出の上界を与え、もう一方の連言は実際の像を記述する。したがって、後で覆いの定理を用いて段階の条件を取り除ける。
<!--/-->

```agda
  BoundedImage : S → hProp (ℓ-suc ℓ)
  BoundedImage y = (y ∈ˢ LsetS βimg βimg-ord) ⊓ ((y ∷ []) ⊨ imageFo)
```

<!--en-->
The equality of the two predicates is pointwise, and its two directions differ
in effort. Forward: from the truncated source witness into the guarded
predicate. The elimination is legitimate because the guarded predicate is a
proposition, the covering fact supplies the stage membership, and the same source is placed back inside the truncation with its satisfaction in the slot
order the formula expects. Backward: nothing is needed, for the satisfaction of
the image formula at a candidate is, by its semantics, exactly the image
predicate at that candidate; the stage conjunct is dropped and the second
conjunct stands as the claim. Because the source occupies the first slot: no transposition of variables is needed
anywhere.
<!--zh-->
两条谓词的相等逐点成立，而其两个方向用力不同。正向：从被截断的源见证走向带守卫的谓词。消去是合法的，因为带守卫的谓词是命题；覆盖事实供给层隶属；同一个源及其满足证明按公式要求的槽位次序重新放入截断。反向：什么都不需要，因为像公式在候选处的满足，按其语义恰是候选处的像谓词；层合取被丢弃，第二个合取项本身即为所求。由于源占据第一个槽位：全程无须任何变元换位。
<!--ja-->
二つの述語の相等は点ごとに成り立ち、その二方向は手間が違う。順方向。切り詰められた源の証人から、守衛つきの述語へ。消去が正当なのは、守衛つきの述語が命題だからである。覆いの事実が段階への所属を供給し、同じ始域の要素と充足の証明を、論理式が要求する位置の順序で切り詰めの中へ戻す。逆方向には、何も要らない。候補における像の論理式の充足は、その意味論により、ちょうどその候補における像の述語だからである。段階の連言は捨てられ、第二の連言がそのまま主張となる。始域が第一の位置を占めるため。変数の入れ替えは、どこにも要らないのである。
<!--/-->

```agda
  Q≡ : ReplImage a φ ≡ BoundedImage
  Q≡ = funExt (λ y → ⇔toPath (into y) (λ p → p .snd))
    where
    into : (y : S) → ⟨ ReplImage a φ y ⟩ → ⟨ BoundedImage y ⟩
    into y = rec₁ (snd (BoundedImage y)) λ { (x , (x∈a , h)) →
```

<!--en-->
For a candidate `y` in `ReplImage a φ`, the source `x`, its membership proof
`x∈a`, and the satisfaction proof `h` are available under propositional
truncation. Since `BoundedImage y` is a proposition, `rec₁` may use these
data while constructing its two conjuncts. The first component follows from
`range∈βimg`: functionality implies that every value related to a member of
`a` lies in `Lset βimg`. For the second component, the same `x`, `x∈a`, and
`h` are placed back under propositional truncation. By the semantics of
`imageFo = ∃̇∈ (con a) φ`, this is exactly the proof that `y` satisfies
`imageFo`. Thus no source is returned as untruncated data.

This completes the implication from `ReplImage a φ y` to `BoundedImage y`.
Together with the reverse implication, which discards the stage-membership
component, it yields `Q≡`; transport along `sym Q≡` then proves
`replaceΔ₀`. Precisely, under the assumption `lem : LEM (ℓ-suc ℓ)`, a
Δ₀ witness for `φ`, and contractibility of the value fibre for every
`x ∈ˢ a`, the result is `isContr (SetOf (ReplImage a φ))`. This is the stated
Δ₀ replacement theorem. The branch introduces no additional classical
principle, although the construction of the common stage used by
`range∈βimg` depends on `lem`.
<!--zh-->
对 `ReplImage a φ` 中的候选者 `y`，源 `x`、成员证明 `x∈a` 与满足证明 `h` 只在命题截断下给出。由于 `BoundedImage y` 是命题，`rec₁` 可以在构造它的两个合取项时使用这些数据。第一项来自 `range∈βimg`：函数性蕴涵，与 `a` 的成员相关的每个值都属于 `Lset βimg`。对于第二项，把同一个 `x`、`x∈a` 与 `h` 重新放入命题截断。按照 `imageFo = ∃̇∈ (con a) φ` 的语义，这恰是 `y` 满足 `imageFo` 的证明。因此，没有源作为未经截断的数据返回。

由此完成从 `ReplImage a φ y` 到 `BoundedImage y` 的蕴涵。再结合舍弃层成员关系分量所得的反向蕴涵，便得到 `Q≡`；沿 `sym Q≡` 运输则证明 `replaceΔ₀`。准确地说，在假设 `lem : LEM (ℓ-suc ℓ)`、`φ` 的 Δ₀ 见证，以及每个 `x ∈ˢ a` 对应的值纤维均可缩这些条件下，结论是 `isContr (SetOf (ReplImage a φ))`。这是所陈述的 Δ₀ 替换定理。本分支没有引入额外的经典原理，但 `range∈βimg` 所使用的公共层之构造依赖 `lem`。
<!--ja-->
`ReplImage a φ` に属する候補 `y` について、始域の要素 `x`、所属の証明 `x∈a`、充足の証明 `h` は、命題的切り詰めのもとでのみ与えられる。`BoundedImage y` は命題なので、`rec₁` は、その二つの連言を構成する間にこれらのデータを使える。第一の成分は `range∈βimg` から得られる。関数性により、`a` の要素と関係するすべての値は `Lset βimg` に属する。第二の成分では、同じ `x`、`x∈a`、`h` を命題的切り詰めの中へ戻す。`imageFo = ∃̇∈ (con a) φ` の意味論により、これはちょうど `y` が `imageFo` を満たすことの証明である。したがって、始域の要素が切り詰められていないデータとして返されることはない。

これで `ReplImage a φ y` から `BoundedImage y` への含意が完成する。段階への所属の成分を捨てる逆向きの含意と合わせて `Q≡` が得られ、`sym Q≡` に沿う輸送によって `replaceΔ₀` が証明される。正確には、仮定 `lem : LEM (ℓ-suc ℓ)`、`φ` の Δ₀ 証人、および各 `x ∈ˢ a` における値のファイバーの可縮性のもとで、結論は `isContr (SetOf (ReplImage a φ))` である。これはここで述べた Δ₀ 置換定理である。この枝は新たな古典的原理を導入しないが、`range∈βimg` が用いる共通の段階の構成は `lem` に依存する。
<!--/-->

```agda
      range∈βimg x x∈a y h , ∣ x , (x∈a , h) ∣₁ }
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
Bounded separation and bounded replacement follow the same pattern. First place the source, the formula's constants, and, for replacement, all related values below one ordinal stage. Definability forms the required subset inside that stage, while relabelling and Δ₀ absoluteness identify its membership relation with satisfaction in the constructible model. Thus `separateΔ₀`{.Agda} and `replaceΔ₀`{.Agda} are obtained under the single host-level assumption `lem : LEM (ℓ-suc ℓ)`{.Agda}.
<!--zh-->
有界分离与有界替换遵循同一思路。先把源集合、公式中的常元，以及替换所涉及的全部取值置于同一个序数层之下；随后在该层内借助可定义性形成所需子集，再由重标与 Δ₀ 绝对性把其成员关系认同为可构造模型中的满足关系。由此，在唯一的宿主层假设 `lem : LEM (ℓ-suc ℓ)`{.Agda} 下得到 `separateΔ₀`{.Agda} 与 `replaceΔ₀`{.Agda}。
<!--ja-->
有界な分出と有界な置換は、同じ方針に従う。まず始集合と論理式の定数を一つの順序数層の下に置き、置換ではさらに関係するすべての値も同じ層の下に収める。次に定義可能性によってその層の内部で必要な部分集合を作り、変名と Δ₀ 絶対性によって、その所属関係を構成可能モデルにおける充足と同一視する。こうして、唯一のホスト側の仮定 `lem : LEM (ℓ-suc ℓ)`{.Agda} のもとで `separateΔ₀`{.Agda} と `replaceΔ₀`{.Agda} が得られる。
<!--/-->

<!--en-->
# Separation and replacement, in full
<!--zh-->
# 完整的分离与替换
<!--ja-->
# 完全な分出公理と置換公理
<!--/-->

<!--en-->
Bounded separation can form the subset of a constructible set defined by a
Δ₀ formula, but the separation scheme permits an arbitrary first-order
formula. This chapter closes that gap by reflecting one formula at a stage
containing the set to be separated. It then proves full replacement by placing
all values of a functional relation on the source set in one stage and
collecting them with the full separation result. These are the two
formula-scheme fields proved here;
the complete ZF and ZFC records are assembled later.
<!--zh-->
有界分离能够形成由 Δ₀ 公式定义的可构造子集，但分离模式允许任意一阶公式。本章先在一个包含待分离集合的层上反射一条指定公式，以此弥合两者之间的差距；随后把函数性关系在源集合上的所有值置于同一层，再用刚得到的完整分离收集它们，从而证明完整替换。本章证明的正是这两个公式模式字段；完整的 ZF 与 ZFC record 留待后文装配。
<!--ja-->
有界な分出公理は、Δ₀ 論理式で定義される構成可能な部分集合を作れるが、分出公理図式は任意の一階論理式を許す。本章では、分出する集合を含む段階で一つの論理式を反映することにより、この隔たりを埋める。次に、始集合上の関数的関係のすべての値を一つの段階へ入れ、得られた完全な分出公理で集めることにより、完全な置換公理を証明する。本章で証明するのは、この二つの公理図式の欄である。ZF と ZFC のレコード全体は後の章で組み立てる。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

```

<!--en-->
The sole classical parameter is the host principle `LEM`. At the stated
universe level it decides each proposition by returning either a proof or a
refutation. This is not a host-level axiom of choice and gives no operation
that selects witnesses from an arbitrary family of propositionally truncated
existences. It is also distinct from the choice axiom later interpreted inside
the set-theoretic model.
<!--zh-->
唯一的经典参数是宿主层原理 `LEM`。在指定的宇宙层级上，它对每个命题返回证明或反驳。它不是宿主层选择公理，也不给出从任意一族命题截断存在中选取见证的操作；它还不同于后文在集合论模型内部解释的选择公理。
<!--ja-->
古典的なパラメータは、ホスト側の原理 `LEM` だけである。指定された宇宙レベルで、各命題について証明か反駁のいずれかを返す。これはホスト側の選択公理ではなく、命題的切り詰めを受けた存在の任意の族から証人を選ぶ操作も与えない。また、後に集合論のモデル内で解釈される選択公理とも異なる。
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )

```

<!--en-->
Fix `lem : LEM (ℓ-suc ℓ)`. All constructions in this module are relative to
this one host assumption. The mathematical conclusions are the separation and
replacement schemes for arbitrary first-order formulas in the constructible
model; the object-theoretic axiom of choice is neither assumed nor proved here.
The dependence on excluded middle enters through the least-stage and formula
reflection results used below: the former decides whether a smaller qualifying
stage merely exists, and the latter decides the matrix in the reverse direction
of the unbounded universal case.
<!--zh-->
固定 `lem : LEM (ℓ-suc ℓ)`。本模块的一切构造都相对于这一条宿主层假设。数学结论是可构造模型中适用于任意一阶公式的分离模式与替换模式；此处既不假设也不证明对象理论的选择公理。对排中律的依赖来自下文所用的最早层与公式反射定理：前者判定是否仅仅存在更小的合格层，后者在无界全称量词的反向判定矩阵是否成立。
<!--ja-->
`lem : LEM (ℓ-suc ℓ)` を固定する。このモジュールのすべての構成は、この一つのホスト側の仮定に相対的である。数学的な結論は、構成可能モデルにおける任意の一階論理式に対する分出公理図式と置換公理図式である。対象理論の選択公理は、ここでは仮定も証明もされない。排中律への依存は、後で使う最小段階と論理式の反映の定理を通して入る。前者では条件を満たすより小さな段階が単に存在するかを判定し、後者では非有界全称量化子の逆向きで行列が成り立つかを判定する。
<!--/-->

```agda
module L.Axioms.Full {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

```

<!--en-->
The argument moves between syntax and semantics. A value of `Formula S n` is
an object-language formula with `n` variable positions and constants drawn from
`S`; `con` inserts such a constant. Renaming changes which environment position
a variable reads and comes with a satisfaction theorem. Relativization replaces
each unbounded quantifier by one bounded by a chosen constant, and
`Δ₀-relativize` proves structurally that the resulting formula is bounded. The
agreement of the original and relativized formulas will come from reflection,
not from the syntactic transformation alone.
<!--zh-->
论证需要在句法与语义之间往返。`Formula S n` 的元素是有 `n` 个变元位置、常元取自 `S` 的对象语言公式，`con` 把这样的常元放入公式。改名改变变元读取的环境位置，并带有相应的满足关系定理。相对化把每个无界量词改为由选定常元约束的量词，`Δ₀-relativize` 则从公式结构证明结果是有界公式。原公式与相对化公式的一致来自反射，而不是单凭这次句法变换。
<!--ja-->
議論では構文と意味論の間を行き来する。`Formula S n` の要素は、`n` 個の変数位置をもち、`S` の要素を定数とする対象言語の論理式である。`con` はそのような定数を論理式へ入れる。改名は変数が読む環境の位置を変え、それに対応する充足関係の定理を伴う。相対化は各非有界量化子を、選んだ定数で有界な量化子に置き換え、`Δ₀-relativize` は得られた論理式が有界であることを構造的に証明する。元の論理式と相対化された論理式の一致は反映から得られるのであり、構文変換だけからは得られない。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( con; Formula; ∃̇∈ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import FOL.Manipulation.Relativization using ( relativize; Δ₀-relativize )
import FOL.Absoluteness
```

<!--en-->
Two structures interpret this language. The ambient cumulative hierarchy
`𝒮ᵥ` interprets all sets in `V ℓ`, while `𝒮ʟ` has as elements the sets equipped
with proofs of constructibility. For an index `β`, `Lset β` is the corresponding
constructible stage; its layer proof yields transitivity, and strict membership
between ordinal indices lets membership be raised by `Lset-mono`. For every
constructible set, `stage` gives the least ordinal index whose stage contains it,
together with ordinality and membership proofs. Only the latter two facts, not
minimality itself, are used in this chapter.
<!--zh-->
这套语言有两种结构解释。外围的累积层级结构 `𝒮ᵥ` 解释 `V ℓ` 中的所有集合；`𝒮ʟ` 的元素则是配有可构造性证明的集合。对指标 `β`，`Lset β` 是相应的可构造层；它的层证明给出传递性，而序数指标之间的严格隶属关系使 `Lset-mono` 可以把成员关系提升到更高层。对每个可构造集，`stage` 给出包含它的最小序数层指标，以及序数性与成员关系的证明。本章只使用后两项事实，不使用极小性本身。
<!--ja-->
この言語には二つの構造による解釈がある。周囲の累積階層の構造 `𝒮ᵥ` は `V ℓ` のすべての集合を解釈し、`𝒮ʟ` の要素は構成可能性の証明を備えた集合である。添字 `β` に対し、`Lset β` は対応する構成可能段階である。その段階であることの証明から推移性が得られ、順序数添字どうしの厳密な所属に沿って `Lset-mono` が所属を上の段階へ移す。構成可能集合ごとに、`stage` はその集合を含む最小の順序数段階の添字を、順序数性と所属の証明とともに与える。本章で使うのは後の二つの事実であり、最小性そのものではない。
<!--/-->

```agda
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset; Lset-layer; layer-trans; Lset-mono )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
```

<!--en-->
Bounded separation and reflection provide the bridge to arbitrary formulas.
For a bounded unary formula, `separateΔ₀` constructs the unique constructible
set with the required members. For one arbitrary formula `φ` and one ordinal
`δ`, `mkReflect` produces an ordinal `β` with `δ ∈ β` and identifies `φ` with
its relativization on environments lying in `Lset β`. This is reflection for
the specified formula and parameters, not an elementary-submodel assertion
about `Lset β`. For replacement, `FunctionalImage` gives one ordinal stage
containing every `y` related to some `x ∈ˢ a`, and `LsetS` presents that stage
as an object-language constant.
<!--zh-->
有界分离与反射共同搭起通往任意公式的桥梁。对有界的一元公式，`separateΔ₀` 构造具有所需成员的唯一可构造集。对一条任意公式 `φ` 和一个序数 `δ`，`mkReflect` 产生满足 `δ ∈ β` 的序数 `β`，并在条目落于 `Lset β` 的环境上认同 `φ` 与其相对化。这只是针对指定公式与参数的反射，并不声称 `Lset β` 是初等子模型。对于替换，`FunctionalImage` 给出一个序数层，容纳每个与某个 `x ∈ˢ a` 相关的 `y`；`LsetS` 则把该层表示成对象语言常元。
<!--ja-->
有界な分出公理と反映が、任意の論理式への橋渡しをする。有界な一変数論理式に対し、`separateΔ₀` は必要な要素をもつ一意な構成可能集合を作る。一つの任意の論理式 `φ` と一つの順序数 `δ` に対し、`mkReflect` は `δ ∈ β` を満たす順序数 `β` を作り、成分が `Lset β` に属する環境上で `φ` とその相対化を同一視する。これは指定された論理式とパラメータについての反映であり、`Lset β` が初等部分モデルであるという主張ではない。置換公理のためには、`FunctionalImage` が、ある `x ∈ˢ a` と関係するすべての `y` を含む一つの順序数段階を与え、`LsetS` がその段階を対象言語の定数として表す。
<!--/-->

```agda
open import L.Axioms.Separation {ℓ} lem
  using ( module FunctionalImage; separateΔ₀ )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.FormulaReflection {ℓ} lem using ( mkReflect )

```

<!--en-->
Several host constructions make the semantic equalities precise. `⇔toPath`
turns implications in both directions between proposition-valued truths into a
path, after which function extensionality can identify predicates pointwise.
The indexed existential used in `hProp` is propositionally truncated. In the
replacement proof, `rec₁` eliminates such an existence only into another
proposition, while `map₁` transforms witnesses without taking them outside the
truncation. Neither operation chooses a source globally.
<!--zh-->
若干宿主层构造使语义等同成为精确的路径。`⇔toPath` 把命题值真值之间的双向蕴含变成路径，随后函数外延性便可从逐点路径认同两个谓词。`hProp` 中的索引存在经过命题截断。在替换证明中，`rec₁` 只把这种存在消去到另一个命题，`map₁` 则在不把见证带出命题截断的前提下变换见证。这两种操作都不会全局选定一个源。
<!--ja-->
いくつかのホスト側の構成により、意味論上の一致が正確なパスになる。`⇔toPath` は命題値の真理の間の双方向の含意をパスに変え、関数外延性は各点でのパスから述語を同一視する。`hProp` の添字付き存在は命題的切り詰めを受けている。置換公理の証明では、`rec₁` はそのような存在を別の命題へだけ除去し、`map₁` は証人を切り詰めの外へ出さずに変換する。どちらの操作も、始域の要素を大域的に選ばない。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
```

<!--en-->
The carrier `S` of `𝒮ʟ` consists of an underlying set in `V ℓ` together with
a proof of its constructibility. Its equality and membership relations inspect
the underlying sets, so `x ∈ˢ a` supplies the ambient membership used later by
stage transitivity. Object-language formulas range over this carrier; their
constants and environment entries therefore retain the constructibility
certificates needed to remain inside the model.
<!--zh-->
`𝒮ʟ` 的载体 `S` 由 `V ℓ` 中的底层集合及其可构造性证明组成。其相等与隶属关系只考察底层集合，因此 `x ∈ˢ a` 给出后文配合层传递性使用的外围隶属。对象语言公式以这一载体为论域，所以它们的常元与环境条目都保留了留在模型内部所需的可构造性证书。
<!--ja-->
`𝒮ʟ` の台 `S` は、`V ℓ` の集合と、その構成可能性の証明からなる。その等しさと所属関係は基礎にある集合だけを見るので、`x ∈ˢ a` は、後で段階の推移性と組み合わせる外側の所属を与える。対象言語の論理式はこの台にわたって量化するため、その定数と環境の各成分は、モデル内にとどまるために必要な構成可能性の証明を保っている。
<!--/-->

```agda

open hPropStructure 𝒮ʟ

```

<!--en-->
For a host predicate `Q : S → hProp (ℓ-suc ℓ)`, `SetOf Q` is the type of pairs
consisting of a model element `b` and a pointwise path `(x ∈ˢ b) ≡ Q x`.
Thus `isContr (SetOf Q)` expresses strong unique existence: its centre supplies
an actual realizing set, and its contraction identifies every other realizer
with that centre. The predicate `Q` is a host-level function, even when it is
built from satisfaction of an object-language formula. Projecting the centre is
ordinary data extraction and uses no description principle.
<!--zh-->
对宿主层谓词 `Q : S → hProp (ℓ-suc ℓ)`，`SetOf Q` 是如下配对的类型：一个模型元素 `b`，以及逐点路径 `(x ∈ˢ b) ≡ Q x`。因此，`isContr (SetOf Q)` 表达强的唯一存在：其中心给出一个实际的实现集合，其收缩则把每个其他实现者与该中心认同。即使 `Q` 由对象语言公式的满足关系构成，它仍是宿主层函数。从中心作投影只是取出已有数据，不使用摹状原理。
<!--ja-->
ホスト側の述語 `Q : S → hProp (ℓ-suc ℓ)` に対し、`SetOf Q` は、モデルの要素 `b` と、各点でのパス `(x ∈ˢ b) ≡ Q x` の組からなる型である。したがって `isContr (SetOf Q)` は強い一意存在を表す。その中心が実際の実現集合を与え、収縮が他のすべての実現者を中心と同一視する。`Q` は、対象言語の論理式の充足関係から作られる場合でも、ホスト側の関数である。中心からの射影は、すでにあるデータを取り出すだけで、記述原理を使わない。
<!--/-->

```agda
module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )

```

<!--en-->
The absoluteness construction gives the same syntax an ambient reading in
`𝒮ᵥ` and an inner reading in `𝒮ʟ`. Here the inner relation `_⊨ᵐ_` is renamed
`_⊨_`. Consequently `γ ⊨ φ` is itself a host-level proposition asserting that
the object-language formula `φ` is true in the constructible structure under
the finite environment `γ`; it should not be confused with substituting an
arbitrary host predicate into the syntax.
<!--zh-->
绝对性构造为同一套句法给出 `𝒮ᵥ` 中的外围读法与 `𝒮ʟ` 中的内层读法；这里把内层关系 `_⊨ᵐ_` 政名为 `_⊨_`。因此，`γ ⊨ φ` 本身是一个宿主层命题，断言对象语言公式 `φ` 在有限环境 `γ` 下于可构造结构中为真；不能把它混同于把任意宿主层谓词代入句法。
<!--ja-->
絶対性の構成は、同じ構文に対して `𝒮ᵥ` での外側の読みと `𝒮ʟ` での内側の読みを与える。ここでは内側の関係 `_⊨ᵐ_` を `_⊨_` と改名する。したがって `γ ⊨ φ` は、それ自体がホスト側の命題であり、有限環境 `γ` のもとで対象言語の論理式 `φ` が構成可能構造において真であることを述べる。任意のホスト側の述語を構文へ代入することとは異なる。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

```

<!--en-->
To compare the two variable orders used later, instantiate the renaming
semantics for `𝒮ʟ`, with constants interpreted by the identity function.
`Ren.Agrees` states pointwise that a renamed variable position reads the same
entry as the corresponding position in another environment. Whenever this
agreement is given, `Ren.⊨-rename` identifies satisfaction of the renamed
formula with satisfaction of the original formula in the rearranged
environment.
<!--zh-->
为了比较后文使用的两种变元次序，这里在 `𝒮ʟ` 上实例化改名语义，并以恒等函数解释常元。`Ren.Agrees` 逐点断言：经改名的变元位置与另一环境中的对应位置读出同一条目。一旦给出这种一致，`Ren.⊨-rename` 就把改名公式的满足关系与原公式在重排环境中的满足关系认同起来。
<!--ja-->
後で使う二つの変数順序を比較するため、定数を恒等関数で解釈して、`𝒮ʟ` における改名の意味論を具体化する。`Ren.Agrees` は各点で、改名された変数位置と別の環境の対応する位置が同じ成分を読むことを述べる。この一致が与えられると、`Ren.⊨-rename` は、改名後の論理式の充足関係を、並べ替えた環境における元の論理式の充足関係と同一視する。
<!--/-->

```agda
module Ren = Sat 𝒮ʟ id
```

<!--en-->
## Two small tools
<!--zh-->
## 两件小工具
<!--ja-->
## 二つの補助道具
<!--/-->

<!--en-->
The first local lemma records transitivity on underlying sets. If `x ∈ y` and
`y ∈ Lset β`, then `x ∈ Lset β`, because every constructible stage is a
transitive set. The variables here lie in `V ℓ`; the lemma does not manufacture
a proof that `x` is constructible. At its later use, `x : S` already carries
that proof, while `transIn` supplies only the stage-membership fact required by
reflection.
<!--zh-->
第一条局部引理记录底层集合上的传递性。若 `x ∈ y` 且 `y ∈ Lset β`，则 `x ∈ Lset β`，因为每个可构造层都是传递集。这里的变元属于 `V ℓ`；该引理并不构造 `x` 的可构造性证明。后文使用它时，`x : S` 已经自带这份证明，而 `transIn` 只补出反射所需的层成员关系。
<!--ja-->
最初の局所補題は、基礎にある集合についての推移性を記録する。`x ∈ y` かつ `y ∈ Lset β` ならば、各構成可能段階は推移的集合なので `x ∈ Lset β` である。ここで変数は `V ℓ` の要素であり、この補題は `x` の構成可能性の証明を作らない。後で使うときには `x : S` がすでにその証明をもち、`transIn` は反映に必要な段階への所属だけを与える。
<!--/-->

```agda
private
  transIn : (β : V ℓ) {x y : V ℓ} → ⟨ x ∈ y ⟩ → ⟨ y ∈ Lset β ⟩ → ⟨ x ∈ Lset β ⟩
  transIn β = layer-trans (Lset-layer β)

```

<!--en-->
Replacement uses a binary formula in two environment orders. In the model
statement, `(y ∷ x ∷ []) ⊨ φ` places the image `y` in slot zero and the source
`x` in slot one. After an existential quantifier binds the source, however, its
body is evaluated in `(x ∷ y ∷ [])`, with the newly bound source in slot zero.
The function `swap` exchanges precisely these two positions of `Fin 2`; it does
not reverse the mathematical relation.
<!--zh-->
替换对同一条二元公式使用两种环境次序。在模型的陈述中，`(y ∷ x ∷ []) ⊨ φ` 把像 `y` 放在零号槽，把源 `x` 放在一号槽。存在量词绑定源之后，其主体却在 `(x ∷ y ∷ [])` 中求值，新绑定的源位于零号槽。函数 `swap` 恰好交换 `Fin 2` 的这两个位置，并不反转数学关系。
<!--ja-->
置換公理では、一つの二変数論理式を二通りの環境順序で使う。モデルでの主張 `(y ∷ x ∷ []) ⊨ φ` では、像 `y` がスロット零、始域の要素 `x` がスロット一に置かれる。しかし、存在量化子が始域の要素を束縛した後、その本体は `(x ∷ y ∷ [])` で評価され、新たに束縛された `x` がスロット零に置かれる。関数 `swap` は `Fin 2` のこの二つの位置だけを交換し、数学的関係の向きを逆にするものではない。
<!--/-->

```agda
  swap : Fin 2 → Fin 2
  swap zero    = suc zero
  swap (suc _) = zero

```

<!--en-->
Applying formula renaming to `swap` gives `swapFo`. If `φ` expects the image in
position zero and the source in position one, then `swapFo φ` can be evaluated
with the source first. This is a syntactic rearrangement of the free positions;
its semantic justification is supplied separately by renaming correctness.
<!--zh-->
把公式改名用于 `swap`，便得到 `swapFo`。若 `φ` 预期像在零号位置、源在一号位置，那么 `swapFo φ` 就可以在源居首的环境中求值。这只是自由位置的句法重排；其语义依据另由改名正确性给出。
<!--ja-->
論理式の改名を `swap` に適用して `swapFo` を得る。`φ` が像を位置零、始域の要素を位置一で読むなら、`swapFo φ` は始域の要素を先に置いた環境で評価できる。これは自由変数位置の構文的な並べ替えであり、その意味論上の根拠は改名の正しさから別に得られる。
<!--/-->

```agda
  swapFo : Formula S 2 → Formula S 2
  swapFo = renameFo swap

```

<!--en-->
For concrete elements `x` and `z`, the two environments agree under this
transposition. At position zero, `swap` reads the second entry of
`x ∷ z ∷ []`, namely `z`; at position one it reads `x`. Both required paths
therefore compute to `refl`, giving the complete proof of `Ren.Agrees` for a
two-entry environment.
<!--zh-->
对具体元素 `x` 与 `z`，两个环境在这次换位下逐点一致。在零号位置，`swap` 从 `x ∷ z ∷ []` 读出第二项 `z`；在一号位置则读出 `x`。因此，两条所需路径都直接计算为 `refl`，这就完整证明了二元环境所需的 `Ren.Agrees`。
<!--ja-->
具体的な要素 `x` と `z` に対し、二つの環境はこの転置のもとで各点ごとに一致する。位置零では、`swap` は `x ∷ z ∷ []` の第二成分 `z` を読み、位置一では `x` を読む。したがって必要な二つのパスはいずれも `refl` に計算され、二成分の環境に対する `Ren.Agrees` の証明が完成する。
<!--/-->

```agda
  swapAgrees : (x z : S) → Ren.Agrees swap (x ∷ z ∷ []) (z ∷ x ∷ [])
  swapAgrees x z zero       = refl
  swapAgrees x z (suc zero) = refl

```

<!--en-->
Renaming correctness now gives the exact semantic conversion used in
replacement:
`(x ∷ z ∷ []) ⊨ swapFo φ` is the same proposition as
`(z ∷ x ∷ []) ⊨ φ`. Reading `x` as the source and `z` as the image, the left
side is the order created by the bounded existential and the right side is the
image-first order required by the model. The path works in both directions by
ordinary transport.
<!--zh-->
改名正确性现在给出替换所需的精确语义转换：`(x ∷ z ∷ []) ⊨ swapFo φ` 与 `(z ∷ x ∷ []) ⊨ φ` 是同一个命题。把 `x` 读作源、`z` 读作像时，左边是有界存在量词产生的次序，右边是模型要求的像在前次序。这条路径可借通常的运输双向使用。
<!--ja-->
改名の正しさから、置換公理で使う正確な意味論的変換が得られる。`(x ∷ z ∷ []) ⊨ swapFo φ` は `(z ∷ x ∷ []) ⊨ φ` と同じ命題である。`x` を始域の要素、`z` を像と読むと、左辺は有界存在量化子が作る順序であり、右辺はモデルが要求する像を先に置く順序である。このパスは通常の輸送により両方向に使える。
<!--/-->

```agda
  ⊨-swap : (φ : Formula S 2) (x z : S)
         → ((x ∷ z ∷ []) ⊨ swapFo φ) ≡ ((z ∷ x ∷ []) ⊨ φ)
  ⊨-swap φ x z = Ren.⊨-rename swap φ (x ∷ z ∷ []) (z ∷ x ∷ []) (swapAgrees x z)
```

<!--en-->
## Separation
<!--zh-->
## 分离
<!--ja-->
## 分出公理
<!--/-->

<!--en-->
Full separation quantifies over every unary object-language formula
`φ : Formula S 1`, with no boundedness hypothesis. Its target says that there
is a unique model set whose members are exactly those `x` that both belong to
`a` and satisfy `φ`. The proof applies bounded separation to the relativized
formula and then transports the entire contractible type of realizers along
`sym Q≡`. Thus uniqueness comes from `separateΔ₀`; it is not reconstructed after
reflection.
<!--zh-->
完整分离量化每条一元对象语言公式 `φ : Formula S 1`，不带有界性假设。其目标说：存在唯一的模型集合，其成员恰是既属于 `a` 又满足 `φ` 的元素 `x`。证明先把有界分离用于相对化后的公式，再沿 `sym Q≡` 运输实现者的整个可缩类型。因此，唯一性来自 `separateΔ₀`，无需在反射之后重新证明。
<!--ja-->
完全な分出公理は、有界性の仮定を置かず、すべての一変数対象言語論理式 `φ : Formula S 1` を量化する。その目標は、`a` に属し、かつ `φ` を満たす `x` だけを要素とするモデル内の集合が一意に存在することである。証明は相対化された論理式に有界な分出公理を適用し、実現者全体の可縮な型を `sym Q≡` に沿って輸送する。したがって一意性は `separateΔ₀` から得られ、反映の後で証明し直す必要はない。
<!--/-->

```agda
hasSeparationL : (a : S) (φ : Formula S 1)
               → isContr (SetOf (λ x → (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)))
hasSeparationL a φ =
  subst (λ Q → isContr (SetOf Q)) (sym Q≡)
    (separateΔ₀ a (relativize c φ) (Δ₀-relativize c φ))
```

<!--en-->
Begin by placing the parameter `a` below the stage where reflection will be
used. Its underlying set has the least-stage index `sa`, and `stage-ord` proves
that this index is an ordinal. Applying `mkReflect φ` with `sa` produces an
ordinal `β`, a strict membership `sa ∈ β`, and a path between the satisfaction
propositions of `φ` and its relativization for every environment lying in
`Lset β`. Supplying `sa` at this
point matters: the reflection theorem is built to contain that index and is not
being enlarged afterwards.
<!--zh-->
先把参数 `a` 放到将要使用反射的层之下。其底层集合的最早层指标是 `sa`，`stage-ord` 证明该指标为序数。以 `sa` 为输入对 `φ` 应用 `mkReflect`，得到序数 `β`、严格隶属关系 `sa ∈ β`，以及对每个落在 `Lset β` 中的环境，`φ` 与其相对化的满足命题之间的路径。此时把 `sa` 传入构造十分关键：反射层从一开始就被构造成包含该指标，而不是事后再扩张。
<!--ja-->
まず、反映を使う段階の中にパラメータ `a` が入るよう準備する。その基礎にある集合の最小段階添字を `sa` とし、`stage-ord` がこの添字の順序数性を証明する。`sa` を与えて `mkReflect φ` を適用すると、順序数 `β`、厳密な所属 `sa ∈ β`、および `Lset β` に入るすべての環境について `φ` とその相対化の充足命題を結ぶパスが得られる。ここで `sa` を渡すことには意味がある。反映段階は初めからこの添字を含むように作られるのであり、後から拡大されるのではない。
<!--/-->

```agda
  where
  sa  = stage (fst a) (a .snd)
  R   = mkReflect φ sa (stage-ord (fst a) (a .snd))
  β   = R .fst
  oβ  = R .snd .fst
```

<!--en-->
The index `β`, the underlying set `Lset β`, and the model element `c` are three
different objects. Using `oβ : IsOrd β`, the term `LsetS β oβ` forms an element
`c : S` from the stage and its constructibility proof. This is
exactly the form required by `relativize`: its new quantifier bounds are
object-language constants, so the stage must be represented inside the model
rather than used only as an ambient set.
<!--zh-->
指标 `β`、底层集合 `Lset β` 与模型元素 `c` 是三个不同的对象。利用证明 `oβ : IsOrd β`，项 `LsetS β oβ` 由该层及其可构造性证明构成元素 `c : S`。这恰是 `relativize` 所需的形式：新量词的界是对象语言常元，因此该层必须在模型内部表示，不能只作为外围集合使用。
<!--ja-->
添字 `β`、基礎にある集合 `Lset β`、モデルの要素 `c` は、それぞれ異なる対象である。証明 `oβ : IsOrd β` により、`LsetS β oβ` はその段階を構成可能性の証明と組にして、要素 `c : S` にする。これは `relativize` が必要とする形である。新しい量化子の境界は対象言語の定数なので、段階は周囲の集合として使うだけでなく、モデルの内部で表されなければならない。
<!--/-->

```agda
  c   = LsetS β oβ

```

<!--en-->
The parameter now lies in the reflection stage. `stage-mem` gives
`fst a ∈ Lset sa`, while the reflection data give the strict ordinal membership
`sa ∈ β`. Monotonicity of the constructible hierarchy combines them to obtain
`fa∈β : fst a ∈ Lset β`. This does not identify `a` with an ordinal: `sa` and
`β` are indices, whereas `fst a` is the set being placed in the higher stage.
<!--zh-->
现在可把参数放入反射层。`stage-mem` 给出 `fst a ∈ Lset sa`，而反射数据给出严格的序数隶属 `sa ∈ β`。可构造层级的单调性把二者合成，得到 `fa∈β : fst a ∈ Lset β`。这并未把 `a` 与序数认同：`sa` 和 `β` 是指标，`fst a` 才是被放入更高层的集合。
<!--ja-->
これでパラメータを反映段階へ入れられる。`stage-mem` は `fst a ∈ Lset sa` を与え、反映のデータは順序数の厳密な所属 `sa ∈ β` を与える。構成可能階層の単調性により、この二つから `fa∈β : fst a ∈ Lset β` が得られる。ここで `a` を順序数と同一視してはいない。`sa` と `β` は添字であり、`fst a` は上の段階へ入れられる集合である。
<!--/-->

```agda
  fa∈β : ⟨ fst a ∈ Lset β ⟩
  fa∈β = Lset-mono {α = β} {β = sa} (R .snd .snd .fst)
           (stage-mem (fst a) (a .snd))

```

<!--en-->
Reflection is available only for environments whose entries lie in
`Lset β`, so the membership conjunct in separation does essential work. Given
`x ∈ˢ a`, transitivity combines this fact with `fa∈β` to put `fst x` in
`Lset β`; `_` supplies the vacuous condition for the empty tail of the
one-entry environment. The reflection component of `R` then gives `bridge`, a
path from satisfaction of `φ` at `x` to satisfaction of its relativization.
No comparison is asserted for arbitrary `x : S` outside `a`.
<!--zh-->
反射只适用于条目落在 `Lset β` 中的环境，因此分离谓词中的成员合取项不可缺少。给定 `x ∈ˢ a`，传递性把该事实与 `fa∈β` 合起来，得到 `fst x ∈ Lset β`；`_` 则给出单元素环境空尾部的平凡条件。于是，`R` 的反射分量给出 `bridge`，即 `φ` 在 `x` 处的满足关系与其相对化的满足关系之间的路径。对于 `a` 外的任意 `x : S`，这里不作比较。
<!--ja-->
反映を適用できるのは、成分が `Lset β` に属する環境だけなので、分出公理の述語にある所属の連言が本質的な役割を果たす。`x ∈ˢ a` が与えられると、推移性によりこの事実と `fa∈β` から `fst x ∈ Lset β` が得られ、`_` が一成分環境の空の末尾に対する自明な条件を与える。そこで `R` の反映成分を使うと、`x` における `φ` の充足関係から、その相対化の充足関係へのパス `bridge` が得られる。`a` の外にある任意の `x : S` については、比較を主張しない。
<!--/-->

```agda
  bridge : (x : S) → ⟨ x ∈ˢ a ⟩
         → ((x ∷ []) ⊨ φ) ≡ ((x ∷ []) ⊨ relativize c φ)
  bridge x x∈a = R .snd .snd .snd (x ∷ []) (transIn β x∈a fa∈β , tt*)

```

<!--en-->
It remains to compare the two host predicates. In each direction, a proof of
the common membership conjunct `x ∈ˢ a` is retained, and only the satisfaction
proof is transported along `bridge` or its inverse. `⇔toPath` turns these two
maps into a path between the proposition values at `x`, and `funExt` assembles
the pointwise paths into `Q≡`. This is equality of predicates; no existential
truncation is eliminated and no extensionality argument about candidate sets is
performed here.
<!--zh-->
最后要比较两个宿主层谓词。在每个方向上，共同的成员证明 `x ∈ˢ a` 都被原样保留，只有满足关系的证明沿 `bridge` 或其逆向运输。`⇔toPath` 把这两个映射变成 `x` 处两个命题值之间的路径，`funExt` 再把逐点路径合成为 `Q≡`。这只是谓词的相等；此处既不消去存在的命题截断，也不对候选集合作外延性论证。
<!--ja-->
残る仕事は、二つのホスト側の述語を比較することである。どちらの方向でも、共通の所属証明 `x ∈ˢ a` はそのまま保ち、充足関係の証明だけを `bridge` またはその逆向きに沿って輸送する。`⇔toPath` はこの二つの写像を `x` における命題値の間のパスに変え、`funExt` が各点でのパスを `Q≡` へまとめる。これは述語の等しさである。ここでは存在の命題的切り詰めを除去せず、候補集合について外延性を使う議論も行わない。
<!--/-->

```agda
  Q≡ : (λ x → (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ))
     ≡ (λ x → (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ relativize c φ))
  Q≡ = funExt (λ x → ⇔toPath
    (λ { (x∈a , h) → x∈a , subst ⟨_⟩ (bridge x x∈a) h })
    (λ { (x∈a , h) → x∈a , subst ⟨_⟩ (sym (bridge x x∈a)) h }))
```

<!--en-->
## Where the images live
<!--zh-->
## 诸像所在的层
<!--ja-->
## 像を収める段階
<!--/-->

<!--en-->
For every `x ∈ˢ a`, the hypothesis makes the dependent sum of related values
`Σ y , (y ∷ x ∷ []) ⊨ φ` contractible. Its centre supplies a value and its
contraction identifies every related value with that centre, so this step uses
no host-level axiom of choice. `FunctionalImage` ranges over the small
presentation `⟪ fst a ⟫`; for each small index it takes the least stage of the
corresponding centre, and `boundingOrd` bounds all those stages by one ordinal
`βimg`. Given an arbitrary member `x ∈ˢ a`, `∈-asFiber` returns a small index
whose represented value is equal to the underlying set of `x`. That path moves
the relation to the source represented by that index; contractibility then
identifies its chosen centre with every related `y` and transports the common
stage bound along that equality. The least-stage operation in this construction
still depends on `lem`, although no choice axiom is used.
<!--zh-->
对每个 `x ∈ˢ a`，假设都使相关值的依值和 `Σ y , (y ∷ x ∷ []) ⊨ φ` 可缩。其中心给出一个值，收缩则把每个相关值与该中心认同，所以这一步不使用宿主层选择公理。`FunctionalImage` 遍历小表示 `⟪ fst a ⟫`；它为每个小指标所表示成员的中心取最早层，再由 `boundingOrd` 用一个序数 `βimg` 界住所有这些层。给定任意成员 `x ∈ˢ a`，`∈-asFiber` 返回一个小指标，以及该指标的表示值与 `x` 的底层集合相等的路径。沿此路径可把关系搬到该指标所表示的源，再由可缩性把所选中心与每个相关的 `y` 认同，并沿这一相等搬运公共层界。这一构造中的最早层操作仍依赖 `lem`，但不使用选择公理。
<!--ja-->
各 `x ∈ˢ a` に対し、仮定は関係する値の依存和 `Σ y , (y ∷ x ∷ []) ⊨ φ` を可縮にする。その中心が一つの値を与え、収縮が関係するすべての値を中心と同一視するので、この段階ではホスト側の選択公理を使わない。`FunctionalImage` は小さな表示 `⟪ fst a ⟫` にわたる。各小さな添字が表す要素について中心の最小段階を取り、`boundingOrd` がそれらすべてを一つの順序数 `βimg` で上から抑える。任意の `x ∈ˢ a` が与えられると、`∈-asFiber` は小さな添字と、その表示値が `x` の基礎にある集合に等しいというパスを返す。そのパスに沿って関係を添字が表す始域の要素へ移し、可縮性によって選ばれた中心を関係する各 `y` と同一視し、その等しさに沿って共通の段階上界を移す。この構成の最小段階を求める操作は依然として `lem` に依存するが、選択公理は使わない。
<!--/-->

```agda
module Images (a : S) (φ : Formula S 2)
              (fc : (x : S) → ⟨ x ∈ˢ a ⟩
                  → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ φ ⟩)) where
  open FunctionalImage a (λ x y → (y ∷ x ∷ []) ⊨ φ) fc public
```

<!--en-->
## Replacement
<!--zh-->
## 替换
<!--ja-->
## 置換公理
<!--/-->

<!--en-->
The hypothesis of `hasReplacementL` makes each value fibre over a member of
`a` contractible, while its conclusion makes the type of model sets realizing
the image predicate contractible. These are different uniqueness statements:
the first supplies one value for each source, and the second supplies one set
containing exactly all such values. The source existential in the image
predicate is propositionally truncated, so it records existence without
exposing a chosen source. The `opaque` boundary changes only Agda's
definitional reduction; it changes neither this statement nor its assumptions.
<!--zh-->
`hasReplacementL` 的假设使 `a` 的每个成员之上的值纤维可缩，而其结论使实现像谓词的模型集合所成之类型可缩。这是两种不同的唯一性：前者为每个源给出唯一的值，后者给出恰好收集所有这些值的唯一集合。像谓词中的源存在经过命题截断，只记录源的存在而不暴露一个选定的源。`opaque` 边界只改变 Agda 的定义性化归，既不改变这个陈述，也不增添假设。
<!--ja-->
`hasReplacementL` の仮定は、`a` の各要素上の値のファイバーを可縮にし、その結論は像の述語を実現するモデル内の集合の型を可縮にする。これは異なる二つの一意性である。前者は各始域の要素に一つの値を与え、後者はそれらすべてをちょうど集める一つの集合を与える。像の述語にある始域の要素の存在は命題的切り詰めを受けているため、存在するという事実だけを記録し、選ばれた要素を外へ出さない。`opaque` の境界が変えるのは Agda の定義上の簡約だけであり、この主張も仮定も変えない。
<!--/-->

```agda
opaque
  hasReplacementL : (a : S) (φ : Formula S 2)
                → ((x : S) → ⟨ x ∈ˢ a ⟩
                     → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ φ ⟩))
                → isContr (SetOf (λ y → ∃[ x ∶ S ] (x ∈ˢ a) ⊓ ((y ∷ x ∷ []) ⊨ φ)))
```

<!--en-->
The replacement proof now has exactly the two ingredients it needs. From the
pointwise contractible fibres, `Images` provides an ordinal stage containing
every value related to a member of `a`. Full separation on that stage, with the
unary formula `imageFo`, gives a contractible type of sets realizing
`BoundedImage`. The path `Q≡` proved below identifies that predicate with the
image predicate `Image`, which has no stage condition; transport along
`sym Q≡` therefore gives
the required contractible type `SetOf Image`. This is full replacement for the
arbitrary formula `φ`, rather than an application of the earlier bounded
replacement theorem.

Later, `L.Model` uses `hasSeparationL` and `hasReplacementL` as two of the
twelve fields of `L⊨ZF`. Only after that ZF record has been assembled does
`hasChoiceL L⊨ZF` supply the object-theoretic choice field used to form
`L⊨ZFC`. Here `lem : LEM (ℓ-suc ℓ)` is the classical host assumption, while
`fc` is the stated pointwise total-and-unique-value hypothesis. Projecting the centres
already contained in `fc` requires no host-level axiom of choice, and the later
choice field is a conclusion, not a premise of this proof.
<!--zh-->
替换证明现在已有恰好两项所需材料。由逐点可缩纤维，`Images` 给出一个序数层，容纳与 `a` 的成员相关的每个值。在该层上把完整分离用于一元公式 `imageFo`，便得到实现 `BoundedImage` 的集合所成的可缩类型。下文证明的路径 `Q≡` 将这一谓词认同于不带层条件的像谓词 `Image`；因此沿 `sym Q≡` 运输，就得到所要求的可缩类型 `SetOf Image`。这正是任意公式 `φ` 的完整替换，而不是对前一章有界替换定理的调用。

稍后，`L.Model` 把 `hasSeparationL` 与 `hasReplacementL` 用作 `L⊨ZF` 十二个字段中的两个。只有在这份 ZF record 装配完成之后，`hasChoiceL L⊨ZF` 才给出组成 `L⊨ZFC` 所需的对象理论选择字段。此处 `lem : LEM (ℓ-suc ℓ)` 是经典的宿主层假设，`fc` 则是定理明列的逐点唯一存在假设。从 `fc` 已经携带的中心作投影不需要宿主层选择公理；后文的选择字段是所得结论，并非本证明的前提。
<!--ja-->
置換公理の証明に必要な二つの材料が、これでそろった。各点での可縮なファイバーから、`Images` は `a` の要素と関係するすべての値を含む一つの順序数段階を与える。その段階において一変数論理式 `imageFo` に完全な分出公理を適用すると、`BoundedImage` を実現する集合からなる可縮型が得られる。以下で証明するパス `Q≡` は、この述語を段階条件のない像の述語 `Image` と同一視する。したがって `sym Q≡` に沿って輸送すれば、必要な可縮型 `SetOf Image` が得られる。これは任意の論理式 `φ` に対する完全な置換公理であり、前章の有界な置換公理の定理を適用したものではない。

後に `L.Model` は、`hasSeparationL` と `hasReplacementL` を `L⊨ZF` の十二の欄のうち二つとして用いる。その ZF レコードを組み立てた後で初めて、`hasChoiceL L⊨ZF` が `L⊨ZFC` を作るための対象理論の選択の欄を与える。ここで `lem : LEM (ℓ-suc ℓ)` は古典的なホスト側の仮定であり、`fc` は定理に明記された各点での一意存在の仮定である。`fc` がすでに含む中心を射影するのにホスト側の選択公理は必要ない。後で得られる選択の欄は結論であって、この証明の前提ではない。
<!--/-->

```agda
  hasReplacementL a φ fc =
    subst (λ Q → isContr (SetOf Q)) (sym Q≡)
      (hasSeparationL (LsetS βimg βimg-ord) imageFo)
    where
    open Images a φ fc
```

<!--en-->
The predicate required by replacement is stated directly in the variable order
of the model axiom. A candidate `y` belongs to `Image` precisely when some
`x ∈ˢ a` satisfies `φ` in the environment `y ∷ x ∷ []`, with the image first
and the source second. The indexed existential in `hProp` uses propositional
truncation: it retains the fact that a suitable source exists while forgetting
which source was used. Thus contractibility of `SetOf Image` will say that
there is a unique model set with exactly these image members; it does not say
that the image itself has only one member.
<!--zh-->
替换所要求的谓词直接采用模型公理中的变元次序。候选者 `y` 属于 `Image`，当且仅当存在某个 `x ∈ˢ a`，使 `φ` 在环境 `y ∷ x ∷ []` 中成立，其中像在前，源在后。`hProp` 中的索引存在采用命题截断：它保留适当的源存在这一事实，却忘去具体使用了哪个源。因此，`SetOf Image` 的可缩性表示恰有一个模型集合以这些像为成员，并不表示像集本身只有一个成员。
<!--ja-->
置換公理が要求する述語を、モデルの公理と同じ変数順序で直接述べる。候補 `y` が `Image` に属すのは、ある `x ∈ˢ a` について、像を先、始域の要素を後に置いた環境 `y ∷ x ∷ []` で `φ` が成り立つとき、またそのときに限る。`hProp` の添字付き存在は命題的切り詰めを用いる。適切な始域の要素が存在するという事実は保つが、それがどの要素かは忘れる。したがって `SetOf Image` の可縮性が述べるのは、ちょうどこれらの像を要素とするモデル内の集合が一意に存在することであり、像集合そのものの要素が一つしかないということではない。
<!--/-->

```agda

    Image : S → hProp (ℓ-suc ℓ)
    Image y = ∃[ x ∶ S ] (x ∈ˢ a) ⊓ ((y ∷ x ∷ []) ⊨ φ)

```

<!--en-->
To obtain the same condition by separation, it must be expressed as a unary
object-language formula. In `imageFo`, the bounded existential ranges over
members of the constant `a`; when its source witness `x` is introduced, the
body is evaluated in the environment `x ∷ y ∷ []`. Since `φ` expects
`y ∷ x ∷ []`, the body is `swapFo φ`, and `⊨-swap` proves that this change of
positions preserves the intended relation. Only this newly added existential
is bounded by `a`. The formula `φ` may still contain unbounded quantifiers, so
`imageFo` need not be a Δ₀ formula and must be handled by full separation.
<!--zh-->
要用分离得到同一条件，须先把它表达成一元对象语言公式。在 `imageFo` 中，有界存在量词遍历常元 `a` 的成员；引入源见证 `x` 后，公式体在环境 `x ∷ y ∷ []` 中求值。由于 `φ` 预期的是 `y ∷ x ∷ []`，公式体取为 `swapFo φ`，而 `⊨-swap` 证明这次位置交换保持原来要表达的关系。只有新添的这一个存在量词受 `a` 约束；`φ` 仍可含无界量词，所以 `imageFo` 未必是 Δ₀ 公式，必须由完整分离处理。
<!--ja-->
同じ条件を分出公理によって得るには、それを一変数の対象言語論理式として表す必要がある。`imageFo` の有界存在量化子は定数 `a` の要素にわたる。始域の証人 `x` を導入すると、本体は環境 `x ∷ y ∷ []` で評価される。`φ` が想定する環境は `y ∷ x ∷ []` なので、本体には `swapFo φ` を置き、`⊨-swap` が、この位置交換によって意図した関係が保たれることを証明する。`a` によって有界なのは、新たに加えたこの存在量化子だけである。`φ` は非有界な量化子を含み得るので、`imageFo` は Δ₀ 論理式とは限らず、完全な分出公理によって扱う必要がある。
<!--/-->

```agda
    imageFo : Formula S 1
    imageFo = ∃̇∈ (con a) (swapFo φ)

```

<!--en-->
Full separation is applied inside the model set representing the common stage,
so the predicate it realizes contains two conditions. The first places `y` in
`Lset βimg`; the second says that `y` satisfies `imageFo`. This first conjunct
is the domain condition contributed by separation, rather than a bound on every
quantifier of the formula. It is redundant for genuine image values because
`range∈βimg` already places all of them in the common stage. The remaining proof
shows that adding or removing this stage condition does not change the
extension of the image predicate.
<!--zh-->
完整分离施于表示公共层的模型集合之内，所以它实现的谓词含有两个条件。第一项把 `y` 放入 `Lset βimg`，第二项断言 `y` 满足 `imageFo`。第一个合取项是分离所带来的论域条件，并不表示公式的每个量词都有界。对真正的像值而言，这一条件是多余的，因为 `range∈βimg` 已把所有像值放进公共层。余下的证明说明，添加或去掉这项层条件都不改变像谓词的外延。
<!--ja-->
完全な分出公理は共通の段階を表すモデル内の集合に適用されるので、それが実現する述語は二つの条件を含む。第一の条件は `y` を `Lset βimg` に置き、第二の条件は `y` が `imageFo` を満たすと述べる。第一の連言は分出公理が加える領域の条件であり、論理式のすべての量化子を有界にするものではない。真に像となる値については、`range∈βimg` がすでにすべてを共通の段階へ入れているため、この条件は余分である。残る証明は、この段階条件を加えても除いても、像の述語の外延が変わらないことを示す。
<!--/-->

```agda
    BoundedImage : S → hProp (ℓ-suc ℓ)
    BoundedImage y = (y ∈ˢ LsetS βimg βimg-ord) ⊓ ((y ∷ []) ⊨ imageFo)

```

<!--en-->
The equality `Q≡` is obtained pointwise. For each candidate `y`, `into y` and
`out y` prove the two implications between `Image y` and `BoundedImage y`;
`⇔toPath` turns them into a path of proposition values, and `funExt` combines
these paths into equality of predicates. The forward implication begins with a
propositionally truncated source. `rec₁` may inspect such a witness here
because its target is the proposition underlying `BoundedImage y`, as certified
by `snd (BoundedImage y)`. The witness is used only within that propositional
target and cannot be returned as untruncated data.
<!--zh-->
相等 `Q≡` 由逐点论证得到。对每个候选者 `y`，`into y` 与 `out y` 给出 `Image y` 和 `BoundedImage y` 之间的两个方向；`⇔toPath` 把它们化为命题值之间的路径，`funExt` 再把这些逐点路径合成谓词的相等。正向从经过命题截断的源开始。此处 `rec₁` 可以考察这样的见证，因为它的目标是 `BoundedImage y` 的底层命题，`snd (BoundedImage y)` 正是对此的证明。见证只在这个命题目标内部使用，不能作为未截断的数据返回。
<!--ja-->
等式 `Q≡` は各点での議論から得られる。候補 `y` ごとに、`into y` と `out y` が `Image y` と `BoundedImage y` の間の二つの含意を与える。`⇔toPath` はそれらを命題値の間のパスにし、`funExt` は各点のパスを述語の等式へまとめる。順方向は、命題的切り詰めを受けた始域の要素から始まる。ここで `rec₁` がその証人を調べられるのは、行き先が `BoundedImage y` の基礎にある命題だからであり、`snd (BoundedImage y)` がまさにそのことを証明する。証人はこの命題の中でだけ使われ、切り詰められていないデータとして返されることはない。
<!--/-->

```agda
    Q≡ : Image ≡ BoundedImage
    Q≡ = funExt (λ y → ⇔toPath (into y) (out y))
      where
      into : (y : S) → ⟨ Image y ⟩ → ⟨ BoundedImage y ⟩
      into y = rec₁ (snd (BoundedImage y)) λ { (x , (x∈a , h)) →
```

<!--en-->
Inside this permitted propositional elimination, suppose the source is `x`,
with proofs `x ∈ˢ a` and `(y ∷ x ∷ []) ⊨ φ`. The range theorem
`range∈βimg` supplies the first conjunct by placing `y` in the common stage. For
the second conjunct, the same `x` is repackaged under propositional truncation.
The reverse of the path `⊨-swap φ x y` transports satisfaction of `φ` at
`y ∷ x ∷ []` to satisfaction of `swapFo φ` at `x ∷ y ∷ []`, which is exactly
the body of `imageFo`. Thus the branch constructs both parts of
`BoundedImage y` without extracting a source from the truncation.
<!--zh-->
在这次合法的命题消去内部，设源为 `x`，并有证明 `x ∈ˢ a` 与 `(y ∷ x ∷ []) ⊨ φ`。值域定理 `range∈βimg` 把 `y` 放入公共层，从而给出第一个合取项。对于第二个合取项，同一个 `x` 被重新包入命题截断。沿路径 `⊨-swap φ x y` 的反向运输，把 `φ` 在 `y ∷ x ∷ []` 中的满足变为 `swapFo φ` 在 `x ∷ y ∷ []` 中的满足，后者恰是 `imageFo` 的公式体。因此，这个分支构造出 `BoundedImage y` 的两个部分，却没有从命题截断中取出一个源作为结果。
<!--ja-->
この許された命題への除去の内部で、始域の要素を `x` とし、`x ∈ˢ a` と `(y ∷ x ∷ []) ⊨ φ` の証明があるとする。値域についての定理 `range∈βimg` は `y` を共通の段階へ入れ、第一の連言を与える。第二の連言では、同じ `x` を命題的切り詰めの中へ再び包む。パス `⊨-swap φ x y` の逆向きに沿う輸送は、`y ∷ x ∷ []` における `φ` の充足を、`x ∷ y ∷ []` における `swapFo φ` の充足へ移す。後者はちょうど `imageFo` の本体である。このように、この枝は始域の要素を切り詰めから結果として取り出すことなく、`BoundedImage y` の二つの部分を構成する。
<!--/-->

```agda
        range∈βimg x x∈a y h
        , ∣ x , (x∈a , subst ⟨_⟩ (sym (⊨-swap φ x y)) h) ∣₁ }

```

<!--en-->
For the reverse implication, the stage-membership component is simply
discarded. Satisfaction of `imageFo` already contains, under propositional
truncation, a source `x`, its membership in `a`, and satisfaction of
`swapFo φ` at `x ∷ y ∷ []`. The map `map₁` keeps the same source and
membership proof inside the truncation while transport along `⊨-swap φ x y`
changes the last component to satisfaction of `φ` at `y ∷ x ∷ []`. The result
is `Image y`. Together with the forward implication this proves `Q≡`, and the
transport in the defining equation above converts the set obtained by full
separation into the unique set required by full replacement. No witness is
selected during this comparison.
<!--zh-->
反向蕴含直接丢弃层成员关系这一分量。`imageFo` 的满足已经在命题截断之下包含一个源 `x`、它属于 `a` 的证明，以及 `swapFo φ` 在 `x ∷ y ∷ []` 中成立的证明。`map₁` 把同一个源及其成员证明保留在命题截断内部，同时沿 `⊨-swap φ x y` 运输，把最后一项变为 `φ` 在 `y ∷ x ∷ []` 中的满足；所得正是 `Image y`。它与正向蕴含共同证明 `Q≡`，而定义等式开头的运输则把完整分离得到的集合变为完整替换所要求的唯一集合。这次比较没有选出任何见证。
<!--ja-->
逆向きの含意では、段階への所属の成分をそのまま捨てる。`imageFo` の充足はすでに、命題的切り詰めの下に、始域の要素 `x`、それが `a` に属すことの証明、そして `x ∷ y ∷ []` における `swapFo φ` の充足を含んでいる。`map₁` は同じ始域の要素と所属の証明を命題的切り詰めの内側に保ったまま、`⊨-swap φ x y` に沿う輸送によって最後の成分を `y ∷ x ∷ []` における `φ` の充足へ変える。得られるのは `Image y` である。これと順方向の含意から `Q≡` が証明され、上の定義式の冒頭にある輸送が、完全な分出公理で得た集合を、完全な置換公理が要求する一意な集合へ変える。この比較では証人を一つも選び出していない。
<!--/-->

```agda
      out : (y : S) → ⟨ BoundedImage y ⟩ → ⟨ Image y ⟩
      out y (_ , h) = map₁ (λ { (x , (x∈a , h')) →
        x , (x∈a , subst ⟨_⟩ (⊨-swap φ x y) h') }) h
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
Full separation and full replacement arise from two reductions. Reflection for
the chosen formula, on environments inside a stage containing the source set,
turns its truth into that of a Δ₀ relativization; bounded separation then gives
full separation. A pointwise contractible value fibre, the source set's small
presentation, and ordinal bounding place every related value in one stage;
full separation then collects the image and gives full replacement. Both
results retain the single classical parameter `LEM (ℓ-suc ℓ)` and use no
host-level axiom of choice. They later fill the separation and replacement
fields of `L⊨ZF`; this chapter does not assemble the full ZF or ZFC record.
<!--zh-->
完整分离与完整替换来自两次归约。先在包含源集合的层内环境上反射指定公式，把它的真假化为其 Δ₀ 相对化公式的真假；有界分离随即给出完整分离。逐点可缩的值纤维、源集合的小表示与序数定界再把每个相关值置于同一层，完整分离于是能够收集像并给出完整替换。两项结果都保留唯一的经典参数 `LEM (ℓ-suc ℓ)`，且不使用宿主层选择公理。后文会用它们填入 `L⊨ZF` 的分离与替换字段；本章本身不装配完整的 ZF 或 ZFC record。
<!--ja-->
完全な分出公理と完全な置換公理は、二つの還元から得られる。まず、始集合を含む段階内の環境上で指定された論理式を反映し、その真理値を Δ₀ 相対化の真理値へ移す。すると、有界な分出公理から完全な分出公理が得られる。次に、各点で可縮な値のファイバー、始集合の小さな表示、順序数による上界を用いて、関係するすべての値を一つの段階へ入れる。完全な分出公理がその像を集め、完全な置換公理を与える。二つの結果は、古典的なパラメータ `LEM (ℓ-suc ℓ)` だけを保ち、ホスト側の選択公理を使わない。これらは後に `L⊨ZF` の分出と置換の欄を満たす。本章自体は ZF や ZFC のレコード全体を組み立てない。
<!--/-->

<!--en-->
# The index of the least constructible stage

Every constructible set x belongs to `Lset α` for at least one ordinal α. This chapter turns that mere existence into a canonical bound: the least ordinal whose stage contains x. The construction first solves a more general problem. For any hProp-valued property P of ordinals, a well-founded descent finds its least witness, while ordinal trichotomy proves that the resulting witness is unique.

The descent begins at any ordinal satisfying P. At α it asks whether some smaller ordinal β ∈ α also satisfies P. A positive answer invokes the induction result at β; a negative answer proves α minimal. Membership induction makes this definition well founded. Both the assertion of a smaller witness and the initial witness are propositionally truncated, but `LeastOrd P` is itself a proposition, so each truncation may be eliminated into that complete package.

Specializing P σ to x ∈ Lset σ gives `stage x hx`. Its accompanying theorems state that this index is an ordinal, that its stage contains x, and that no smaller ordinal stage contains x. The proof uses excluded middle only to decide the existence of a smaller witness and to compare two candidate ordinals.
<!--zh-->
# 最小可构造层的索引

每个可构造集合 x 至少属于一个序数 α 所索引的 `Lset α`。本章把这种仅仅存在化为一个典范界：包含 x 的最小层之序数索引。证明先解决更一般的问题。对序数上的任意 hProp 值性质 P，良基下降找出其最小见证，序数三歧则证明所得见证唯一。

下降从任意满足 P 的序数开始。在 α 处，询问是否有更小的 β ∈ α 也满足 P；肯定答案调用 β 处的归纳结果，否定答案则证明 α 最小。成员关系归纳使这一定义保持良基。「存在更小见证」的断言与初始见证都经过命题截断，但 `LeastOrd P` 本身是命题，因此每处截断都可以消去到这个完整包。

把 P σ 特化为 x ∈ Lset σ，便得到 `stage x hx`。配套定理说明该索引是序数、其层包含 x，且没有更小的序数层包含 x。证明使用排中律的地方只有判定更小见证是否存在，以及比较两个候选序数。
<!--ja-->
# 最小の構成可能段階の添字

各構成可能集合 x は、少なくとも一つの順序数 α に対する `Lset α` に属します。本章は、この単なる存在から標準的な上界、すなわち x を含む最小段階の順序数添字を得ます。まず、より一般的な問題を解きます。順序数上の任意の hProp 値の性質 P について、整礎的な降下が最小の証人を見つけ、順序数の三分法がその一意性を示します。

降下は P を満たす任意の順序数から始まります。α において、より小さい β ∈ α も P を満たすかを問います。肯定なら β における帰納法の結果を使い、否定なら α の最小性が得られます。所属に関する帰納法により、この定義は整礎的です。「より小さい証人が存在する」という主張と最初の証人はいずれも命題的に切り捨てられていますが、`LeastOrd P` 自身が命題なので、それぞれの切り捨てをこの完全なパッケージへ消去できます。

P σ を x ∈ Lset σ に特殊化すると `stage x hx` が得られます。付随する定理は、この添字が順序数で、その段階が x を含み、より小さい順序数の段階は x を含まないことを述べます。排中律を使うのは、より小さい証人の存在を判定するときと、二つの候補順序数を比較するときだけです。
<!--/-->

<!--en-->
Work at a fixed universe level ℓ and assume excluded middle at level ℓ-suc ℓ. The assumption will be used in two mathematically distinct ways: `ord-tri` compares ordinal candidates, while the descent decides the hProp asserting that a smaller candidate exists.
<!--zh-->
固定宇宙层级 ℓ，并假设层级 ℓ-suc ℓ 上的排中律。这个假设有两种不同的数学用途：`ord-tri` 比较候选序数，而下降过程判定「存在更小候选」这一 hProp。
<!--ja-->
宇宙レベル ℓ を固定し、レベル ℓ-suc ℓ における排中律を仮定します。この仮定には二つの異なる数学的用途があります。`ord-tri` は候補の順序数を比較し、降下は「より小さい候補が存在する」という hProp を判定します。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module L.Stage {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

<!--en-->
Membership supplies both the strict order on ordinals and its well-founded induction principle. Constructibility supplies the predicate IsOrd, the stage family Lset and the assertion isL x that x occurs in some ordinal-indexed stage. Thus the same membership relation controls descent among candidate indices and, after specialization, membership of x in a stage.
<!--zh-->
隶属关系既给出序数上的严格序，也给出其良基归纳原理。可构造性一侧提供谓词 IsOrd、层族 Lset，以及断言 x 出现在某个序数索引层中的 isL x。因此，同一个隶属关系既控制候选索引之间的下降，也在特化后表达 x 属于某一层。
<!--ja-->
所属関係は、順序数上の狭義順序と、その整礎帰納の原理の両方を与えます。構成可能性からは、述語 IsOrd、段階族 Lset、そして x がある順序数添字の段階に現れるという主張 isL x を得ます。したがって同じ所属関係が候補添字の間の降下を制御し、特殊化後には x の段階への所属を表します。
<!--/-->

```agda

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import L.Constructible {ℓ} using ( IsOrd; isPropIsOrd; Lset; isL )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
```

<!--en-->
The assertion that a smaller witness exists is represented by a propositionally truncated existential. It records existence without exposing a chosen β. The eliminator `PT.rec` can use such evidence only when the target is a proposition; the uniqueness proof below supplies exactly this fact for `LeastOrd P`. Products and dependent function spaces preserve propositionhood, which will also show that the evidence attached to a fixed ordinal index is unique.
<!--zh-->
「存在更小见证」用命题截断的存在式表示，只记录存在而不暴露选定的 β。消去子 `PT.rec` 只能在目标是命题时使用这份证据；下面的唯一性证明恰好说明 `LeastOrd P` 是命题。积与依赖函数空间保持命题性，这也将说明固定序数索引所附的证据唯一。
<!--ja-->
「より小さい証人が存在する」という主張は、命題的に切り捨てられた存在で表します。これは存在だけを記録し、選ばれた β を取り出しません。消去子 `PT.rec` がこの証拠を使えるのは対象が命題の場合だけであり、下の一意性の証明が `LeastOrd P` についてまさにそれを示します。積と依存関数型は命題性を保つので、固定した順序数添字に付随する証拠も一意になります。
<!--/-->

```agda
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
open import Cubical.Data.Sigma using ( Σ≡Prop )
```

<!--en-->
A property P is a map into Ω, the type of hProps. Hence `⟨ P α ⟩` is its underlying proposition at α, and `snd (P α)` proves that any two of its witnesses agree. This propositionhood is needed when equality of ordinal indices is lifted to equality of complete least-witness packages.
<!--zh-->
性质 P 是到 Ω，即 hProp 类型的映射。因此，`⟨ P α ⟩` 是 P 在 α 处的底层命题，而 `snd (P α)` 证明其任意两个见证相等。当序数索引的相等被提升为完整最小见证包的相等时，正需要这一命题性。
<!--ja-->
性質 P は Ω、すなわち hProp の型への写像です。したがって `⟨ P α ⟩` は α における基礎の命題であり、`snd (P α)` はその任意の二つの証人が一致することを示します。順序数添字の等号を最小証人のパッケージ全体の等号へ持ち上げるとき、この命題性を使います。
<!--/-->

```agda
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ )

open hPropStructure 𝒮ᵥ
```

<!--en-->
## The least ordinal satisfying a property

For a property `P` of ordinals, `LeastOrd P`{.Agda} packages an ordinal α satisfying `P` together with the proof that no smaller ordinal satisfies it. This definition concerns the ordinal index itself; only the later specialization `P σ = (x ∈ Lset σ)` turns such an index into the index of a constructible stage.

Uniqueness uses the fact that the property takes values in an `hProp`{.Agda}: the two candidates are compared by trichotomy, each strict direction is refuted by the other's minimality, and the remaining components are propositions, so the equality of the ordinals is the equality of the packages.
<!--zh-->
## 满足性质的最小序数

对于序数性质 `P`，`LeastOrd P`{.Agda} 由满足 `P` 的序数 α 和「没有更小序数满足 `P`」的证明组成。这个定义谈的是序数索引本身；直到稍后取 `P σ = (x ∈ Lset σ)`，这样的索引才成为某个可构造层的索引。

唯一性正用到该性质取值于 `hProp`{.Agda} 这一事实：两个候选经三歧比较，每个严格方向都被对方的极小性反驳，而其余分量都是命题，故序数相等即是二者作为整体相等。
<!--ja-->
## 性質を満たす最小の順序数

順序数の性質 `P` に対して、`LeastOrd P`{.Agda} は `P` を満たす順序数 α と、それより小さい順序数は `P` を満たさないという証明とを組にします。この定義が扱うのは順序数の添字そのものであり、後で `P σ = (x ∈ Lset σ)` と特殊化して初めて、その添字は構成可能段階の添字になります。

一意性は、性質が `hProp`{.Agda} の値を取るという事実を用います。二人の候補は三分性で比較され、どちらの厳密な向きも相手の最小性によって反駁され、残りの成分はすべて命題です。したがって順序数として等しければ、パッケージ全体としても等しいのです。
<!--/-->

<!--en-->
Leastness is stated as a refutation: `isLeastOrd α` is the assertion, for every set γ, that γ cannot be an ordinal satisfying P with γ ∈ α. Minimality by contradiction is the right shape here because the strict order on ordinals is read off membership; there is no smaller-ordinal value to return, only an impossible situation to derive. The full package `LeastOrd` then bundles an ordinal, its ordinalhood, a proof of P at it, and this minimality clause.
<!--zh-->
极小性被表述为一个反驳：`isLeastOrd α` 断言，对任意集合 γ，γ 不可能是满足 P 的序数且有 γ ∈ α。这里用反证表述极小性是合适的形状，因为序数上的严格序正是经由成员关系读出的；没有「更小序数」这样的值可供返回，只有要导出的不可能局面。整体包 `LeastOrd` 则把序数、其序数性、在该处 P 的证明，以及这条极小性条款捆在一起。
<!--ja-->
最小性は反駁として述べられます。`isLeastOrd α` とは、任意の集合 γ について、γ が P を満たす順序数でかつ γ ∈ α であるような状況は起こりえない、という主張です。ここで背理的な形の最小性が適切なのは、順序数の厳密な順序が所属を通して読み取られるからです。返すべき「より小さい順序数」の値はなく、導出すべきは不可能な状況だけです。パッケージ全体 `LeastOrd` は、順序数、その順序数性、そこでの P の証明、そしてこの最小性の条項をひとまとめにします。
<!--/-->

```agda
module _ (P : S → hProp (ℓ-suc ℓ)) where

  isLeastOrd : S → Type (ℓ-suc ℓ)
  isLeastOrd α = (γ : S) → IsOrd γ → ⟨ P γ ⟩ → ⟨ γ ∈ˢ α ⟩ → Empty.⊥

  LeastOrd : Type (ℓ-suc ℓ)
  LeastOrd = Σ[ α ∈ S ] (IsOrd α × ⟨ P α ⟩ × isLeastOrd α)
```

<!--en-->
To prove two such packages equal, compare their ordinal indices first. Trichotomy delivers one of three cases: α ∈ α′, α = α′, or α′ ∈ α. The plan is to eliminate both strict cases by contradiction and keep the equality case; `decide` is the function turning that trichotomy result into a path α ≡ α′. Crucially, this argument shows the indices equal; the packages are dependent pairs over the index, so an equality of packages is not yet obtained from an equality of indices alone.
<!--zh-->
要证两个这样的包相等，先比较它们的序数索引。三歧给出三种情形：α ∈ α′、α = α′ 或 α′ ∈ α。计划是：用反证消去两个严格情形，保留相等情形；`decide` 就是把这份三歧结果变成路径 α ≡ α′ 的函数。关键在于，这一步只证得索引相等；而包是在索引上的依赖对，故仅有索引相等还得不到包的相等。
<!--ja-->
このようなパッケージが等しいことを示すには、まず順序数の添字を比較します。三分性は α ∈ α′、α = α′、α′ ∈ α の三つの場合を届けます。方針は、厳密な二つの場合を背理的に消去し、等しい場合を残すことです。`decide` はこの三分法の結果をパス α ≡ α′ に変える関数です。重要なのは、この議論が示すのは添字の等しさだけだということです。パッケージは添字上の依存対なので、添字の等しさだけからパッケージの等しさは得られません。
<!--/-->

```agda

  isPropLeastOrd : isProp LeastOrd
  isPropLeastOrd (α , ordα , pα , leastα) (α' , ordα' , pα' , leastα') =
    Σ≡Prop propRest α≡α'
    where
    decide : (⟨ α ∈ˢ α' ⟩ ⊎ ((α ≡ α') ⊎ ⟨ α' ∈ˢ α ⟩)) → α ≡ α'
```

<!--en-->
Each strict case contradicts minimality, but minimality of the *other* candidate. If α were a member of α′, then α is an ordinal satisfying P that lies strictly below α′, and `leastα'` refutes exactly that; the case α′ ∈ α is symmetric, using `leastα`. The middle case is the path itself. Feeding `ord-tri`'s verdict into `decide` thus yields the path `α≡α'`, and note that no assumption about P beyond its values being propositions was used so far.
<!--zh-->
每个严格情形都与极小性矛盾，但那是与**另一个**候选的极小性矛盾。若 α ∈ α′，则 α 是严格低于 α′ 且满足 P 的序数，`leastα'` 反驳的恰是这一点；α′ ∈ α 的情形对称，用 `leastα`。中间情形就是路径本身。把 `ord-tri` 的裁决送入 `decide`，即得路径 `α≡α'`。注意，到目前为止，除「P 的取值是命题」外，未对 P 使用任何假设。
<!--ja-->
それぞれの厳密な場合は最小性と矛盾しますが、それは**相手側**の候補の最小性との矛盾です。α ∈ α′ なら、α は α′ より厳密に下にあり P を満たす順序数であり、`leastα'` が反駁するのはまさにこれです。α′ ∈ α の場合は `leastα` を用いて対称です。真ん中の場合がパスそのものです。`ord-tri` の判定を `decide` に流し込めばパス `α≡α'` が得られます。ここまでに P について使った仮定は、その値が命題であること以外にありません。
<!--/-->

```agda
    decide (inl α∈α')       = Empty.rec (leastα' α ordα pα α∈α')
    decide (inr (inl e))    = e
    decide (inr (inr α'∈α)) = Empty.rec (leastα α' ordα' pα' α'∈α)
    α≡α' : α ≡ α'
    α≡α' = decide (ord-tri α ordα α' ordα')
```

<!--en-->
It remains to lift the path of indices to a path of packages, and this uses propositionhood of the dependent remainder. The component that varies with the index is `IsOrd β × ⟨ P β ⟩ × isLeastOrd β`; `IsOrd β` is a proposition by the constructible chapter, `⟨ P β ⟩` is a proposition because P is hProp-valued, and `isLeastOrd β` is a function type into the empty type, hence a proposition by `isPropΠ` iterated. So `propRest β` certifies propositionhood of the whole remainder, and `Σ≡Prop` turns the base path into the required equality of packages: once the index agrees, the dependent remainder cannot disagree.
<!--zh-->
剩下要把索引的路径提升为包的路径，这里要用到依赖剩余分量的命题性。随索引变化的分量是 `IsOrd β × ⟨ P β ⟩ × isLeastOrd β`：`IsOrd β` 由可构造章知是命题；因 P 取值于 hProp，`⟨ P β ⟩` 是命题；`isLeastOrd β` 是到空类型的函数类型，经 `isPropΠ` 迭代即知是命题。于是 `propRest β` 证明了整个剩余分量的命题性，`Σ≡Prop` 把基础路径变成所需的包的相等：索引一旦一致，依赖的剩余分量便不可能不一致。
<!--ja-->
残るは、添字のパスをパッケージのパスへ引き上げることであり、ここでは依存する残りの命題性を使います。添字とともに変わる成分は `IsOrd β × ⟨ P β ⟩ × isLeastOrd β` です。`IsOrd β` は構成可能の章により命題であり、`⟨ P β ⟩` は P が hProp 値であることから命題であり、`isLeastOrd β` は空型への関数型なので `isPropΠ` の繰り返しで命題です。よって `propRest β` が残りの全体の命題性を証明し、`Σ≡Prop` が基礎のパスを、求めるパッケージの相等へと変えます。添字が一致すれば、依存する残りは一致しないようがないのです。
<!--/-->

```agda
    propRest : (β : S) → isProp (IsOrd β × ⟨ P β ⟩ × isLeastOrd β)
    propRest β = isProp× (isPropIsOrd β)
      (isProp× (snd (P β))
        (isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → Empty.isProp⊥))
```

<!--en-->
## Descent to the least ordinal

Starting from any ordinal satisfying `P`, `leastOrdBelow`{.Agda} asks whether a strictly smaller ordinal also satisfies `P` and recurses when one does. Membership induction defines the result from the results at strictly smaller ordinals, yielding the least ordinal satisfying `P`, before the construction is specialized to constructible stages.

The result being a proposition, the starting ordinal may be given truncated, and that is the form the callers have: they know a suitable ordinal exists without having chosen one.
<!--zh-->
## 下降到最小序数

从任一满足 `P` 的序数出发，`leastOrdBelow`{.Agda} 询问是否有严格更小的序数也满足 `P`，若有便递归下降。成员关系归纳由严格更小序数处的结果定义当前结果，从而得到满足 `P` 的最小序数；此时构造尚未特化到可构造层。

结果既是命题，起始序数便可以截断的形式给出，而这正是各调用方实际具有的形式：它们知道合用的序数存在，却未曾选定一个。
<!--ja-->
## 最小の順序数への降下

`P` を満たす任意の順序数から始め、`leastOrdBelow`{.Agda} は、それより小さく `P` を満たす順序数があれば再帰的にそこへ降ります。所属に関する帰納法は、真に小さい順序数での結果から現在の結果を定め、`P` を満たす最小の順序数を与えます。この時点ではまだ構成可能段階への特殊化は行いません。

結果が命題であるため、出発点の順序数は切り詰められた形で与えてよく、それこそが呼び出し側の実際の形です。呼び出し側は、適切な順序数が存在することを知っているだけで、ひとつを選んではいません。
<!--/-->

<!--en-->
The descent is organized as well-founded induction on membership, the principle `∈-induction` from the hierarchy chapter. Its step receives an ordinal α, its ordinalhood, a proof of P at α, and an induction hypothesis valid for every strictly smaller member β: provided β is again an ordinal satisfying P, the globally least P-witness obtained by starting the induction at β is already available. The step's only job is to decide, at α, whether the descent must continue or has arrived.
<!--zh-->
下降按成员关系上的良基归纳来组织，即层级章的原理 `∈-induction`。其步进收到的参数有：序数 α、其序数性、在 α 处的 P 的证明，以及对每个严格更小成员 β 可用的归纳假说：只要 β 又是满足 P 的序数，从 β 开始归纳所得的全局最小 P 见证便已在手。步进唯一的任务，就是在 α 处判定下降该继续还是已经抵达。
<!--ja-->
降下は所属に関する整礎帰納として構成されます。これが階層の章の原理 `∈-induction` です。そのステップは、順序数 α、その順序数性、α での P の証明、そしてすべての厳密に小さい要素 β に対して有効な帰納法の仮定を受け取ります。β が再び P を満たす順序数であれば、β から帰納を始めて得られる大域的に最小の P の証人がすでに手にある、というものです。ステップの仕事はただひとつ、α において降下を続けるか、到着したかを判定することです。
<!--/-->

```agda
  leastOrdBelow : (α : S) → IsOrd α → ⟨ P α ⟩ → LeastOrd
  leastOrdBelow = ∈-induction step
    where
    step : (α : S) → (∀ β → ⟨ β ∈ˢ α ⟩ → IsOrd β → ⟨ P β ⟩ → LeastOrd)
         → IsOrd α → ⟨ P α ⟩ → LeastOrd
```

<!--en-->
The question to decide is `Smaller`: merely whether there exists a β with β ∈ α, ordinal, and satisfying P, all packaged with conjunctions into a single hProp. Two features matter. First, the existential is truncated: `Smaller` carries no chosen β, only the assertion that one exists. Second, excluded middle at level ℓ-suc ℓ, applied via `lem`, decides this question outright, delivering either an inhabitant of the truncation or a refutation. This is precisely where the classical assumption enters the descent.
<!--zh-->
要判定的问题是 `Smaller`：是否仅仅存在某个 β，使 β ∈ α、β 是序数且满足 P；诸条件用合取打包成一个 hProp。有两点要紧。其一，这个存在式是截断的：`Smaller` 不携带选定的 β，只声称存在一个。其二，层级 ℓ-suc ℓ 上的排中律经 `lem` 直接判定这个问题，交付截断的一个元素或一个反驳。这正是经典假设进入下降之所在。
<!--ja-->
判定すべき問いは `Smaller` です。すなわち、β ∈ α であり、順序数であり、P を満たすような β が単に存在するかどうかで、各条件は論理積でひとつの hProp にまとめられます。ここで重要な点が二つあります。第一に、この存在文は切り詰められていることです。`Smaller` は選ばれた β を持たず、存在することの主張だけを運びます。第二に、レベル ℓ-suc ℓ における排中律が `lem` を通してこの問いを丸ごと判定し、切り詰めの要素か、反駁かのどちらかを届けることです。これこそ古典的な仮定が降下に入り込む場所です。
<!--/-->

```agda
    step α IH ordα pα = decide (lem Smaller)
      where
      Smaller : hProp (ℓ-suc ℓ)
      Smaller = ∃[ β ∶ S ] ((β ∈ˢ α) ⊓ ((IsOrd β , isPropIsOrd β) ⊓ P β))
      decide : (⟨ Smaller ⟩ ⊎ (⟨ Smaller ⟩ → Empty.⊥)) → LeastOrd
```

<!--en-->
The two branches of the decision build the answer directly. In the positive branch, the truncated witness cannot be taken apart into data, but `PT.rec` may eliminate it into any proposition, and `LeastOrd` is one: so the witness is converted, without being chosen, into the globally least package supplied by the induction hypothesis at β. In the negative branch there is no smaller witness at all, so α itself is least. Recursion happens only through `∈-induction`'s controlled induction hypothesis.
<!--zh-->
判定的两个分支都直接构造答案。在肯定分支里，截断的见证不能拆成数据，但 `PT.rec` 可以把它消去到任何命题，而 `LeastOrd` 恰是命题：于是这个见证在被消去而非被选定的意义上，转化为归纳假说在 β 处给出的全局最小包。在否定分支里根本不存在更小的见证，故 α 自身就是最小的。递归只经由 `∈-induction` 受控的归纳假说发生。
<!--ja-->
判定の二つの分岐は、どちらも答えを直接組み立てます。肯定的な分岐では、切り詰められた証人をデータとして分解することはできませんが、`PT.rec` はそれを任意の命題へ消去でき、`LeastOrd` はまさに命題です。そこで証人は、選ばれることなく、β における帰納法の仮定が与える大域的に最小のパッケージへと変換されます。否定的な分岐では、より小さい証人はそもそも存在しないので、α 自身が最小です。再帰は `∈-induction` の管理された帰納法の仮定を通してのみ起こります。。
<!--/-->

```agda
      decide (inl ∃β) = PT.rec isPropLeastOrd
        (λ { (β , (β∈α , (ordβ , pβ))) → IH β β∈α ordβ pβ }) ∃β
      decide (inr ¬∃β) = α , ordα , pα , leastProof
        where
        leastProof : isLeastOrd α
```

<!--en-->
The negative branch's minimality clause is where the refutation earns its keep: given any γ below α that is an ordinal satisfying P, the witness `(γ , γ∈α , ordγ , pγ)` is packaged into the very truncation `Smaller` that was denied, and applying `¬∃β` to it yields the required contradiction. Finally, `leastOrd` handles the form callers actually have: an ordinal satisfying P merely exists. Again the elimination into `LeastOrd` is licensed by its propositionhood, proved in the previous section, so a truncated existence is refined into the canonical least index without eliminating the truncation into an arbitrary data type.
<!--zh-->
否定分支的极小性条款正是反驳发挥作用之处：给定 α 之下任何满足 P 的序数 γ，把见证 `(γ , γ∈α , ordγ , pγ)` 打包进恰好被否认的那个截断 `Smaller`，再对它施加 `¬∃β` 即得所需矛盾。最后，`leastOrd` 处理调用方实际具有的形式：满足 P 的序数仅仅存在。再次地，向 `LeastOrd` 的消去由上一节证明的命题性所许可，于是截断的存在被精炼成典范的最小索引，且没有把截断消去到任意数据类型。
<!--ja-->
否定的な分岐の最小性の条項で、反駁が働きます。α より下で P を満たす順序数 γ が与えられれば、証人 `(γ , γ∈α , ordγ , pγ)` は、まさに否定されたはずの切り詰め `Smaller` に梱包され、それに `¬∃β` を適用して求める矛盾が得られます。最後に `leastOrd` が、呼び出し側が実際に持つ形を扱います。P を満たす順序数が単に存在する、という形です。ここでも `LeastOrd` への消去は、前節で証明された命題性によって許されます。こうして切り詰められた存在は、切り捨てを任意のデータ型へ消去することなく、正準な最小の添字へと洗練されるのです。
<!--/-->

```agda
        leastProof γ ordγ pγ γ∈α = ¬∃β ∣ γ , (γ∈α , (ordγ , pγ)) ∣₁

  leastOrd : ∥ (Σ[ α ∈ S ] (IsOrd α × ⟨ P α ⟩)) ∥₁ → LeastOrd
  leastOrd = PT.rec isPropLeastOrd
    (λ { (α , (ordα , pα)) → leastOrdBelow α ordα pα })
```

<!--en-->
## The stage-index function

For `P σ = (x ∈ Lset σ)`, the descent returns the least ordinal index α whose stage `Lset α`{.Agda} contains `x`. The function `stage`{.Agda} selects α, `stage-ord`{.Agda} proves that it is an ordinal, and `stage-mem`{.Agda} and `stage-earliest`{.Agda} relate that index to its stage.

The index is exposed through three stable facts rather than its recursive construction: it is an ordinal, its stage contains x, and it is minimal among ordinal indices with that property. Declaring `stage` opaque preserves this abstraction boundary.
<!--zh-->
## 层索引函数

取 `P σ = (x ∈ Lset σ)` 后，下降得到最小序数索引 α，使层 `Lset α`{.Agda} 包含 `x`。函数 `stage`{.Agda} 选出 α，`stage-ord`{.Agda} 证明它是序数，`stage-mem`{.Agda} 与 `stage-earliest`{.Agda} 则把这个索引与相应层联系起来。

这个索引通过三条稳定事实给出，而不依赖递归构造本身：它是序数、其层包含 x，并且在具有该性质的序数索引中最小。把 `stage` 声明为 opaque 保持了这一抽象边界。
<!--ja-->
## 段階の添字を返す関数

`P σ = (x ∈ Lset σ)` とすると、降下は `x` を含む段階 `Lset α`{.Agda} の最小の順序数添字 α を返します。関数 `stage`{.Agda} が α を選び、`stage-ord`{.Agda} はそれが順序数であることを、`stage-mem`{.Agda} と `stage-earliest`{.Agda} はその添字と対応する段階との関係を示します。

この添字は再帰的な構成そのものではなく、三つの安定した事実を通して与えられます。すなわち、順序数であり、その段階が x を含み、その性質をもつ順序数添字の中で最小です。`stage` を opaque とすることで、この抽象化の境界を保ちます。
<!--/-->

<!--en-->
A constructibility certificate `⟨ isL x ⟩` is exactly the input form `leastOrd` expects: by the class's definition in the constructible chapter, an element of `isL x` is merely a pair of an ordinal σ, its ordinalhood, and a membership `x ∈ˢ Lset σ`. So the property `λ σ → x ∈ˢ Lset σ` satisfies the hypotheses of the descent, and `theEarliest` applies `leastOrd` to this property. Thus constructibility supplies exactly the truncated existence premise needed to obtain a least stage index.
<!--zh-->
可构造性证书 `⟨ isL x ⟩` 恰是 `leastOrd` 所期望的输入形式：按可构造章中类的定义，`isL x` 的一个元素仅仅是序数 σ、其序数性、以及隶属 `x ∈ˢ Lset σ` 的一个对。于是性质 `λ σ → x ∈ˢ Lset σ` 满足下降的假设，而 `theEarliest` 把 `leastOrd` 应用于这条性质。因此，可构造性恰好提供了取得最小层索引所需的截断存在前提。
<!--ja-->
構成可能性の証明書 `⟨ isL x ⟩` は、`leastOrd` が期待する入力の形そのものです。構成可能の章でのクラスの定義により、`isL x` の要素とは、順序数 σ とその順序数性と所属 `x ∈ˢ Lset σ` の対を単に切り詰めたものです。したがって性質 `λ σ → x ∈ˢ Lset σ` は降下の仮定を満たし、`theEarliest` はこの性質に `leastOrd` を適用します。したがって構成可能性は、最小段階の添字を得るために必要な切り捨てられた存在の前提をちょうど与えます。
<!--/-->

```agda
theEarliest : (x : S) → ⟨ isL x ⟩ → LeastOrd (λ σ → x ∈ˢ Lset σ)
theEarliest x = leastOrd (λ σ → x ∈ˢ Lset σ)

opaque
  stage : (x : S) → ⟨ isL x ⟩ → S
  stage x p = theEarliest x p .fst
```

<!--en-->
The package `theEarliest x p` contains the least index together with its three proofs. The function `stage` projects the index and keeps its recursive construction opaque, so later arguments use its ordinalhood, membership and minimality. It is an ordinal-valued function of a constructible set and its witness; it is neither a universe level nor the rank function.
<!--zh-->
包 `theEarliest x p` 含有最小索引及其三项证明。函数 `stage` 投影出该索引，并保持其递归构造不透明，使后续论证使用序数性、层隶属与极小性。它以可构造集合及其见证为输入并返回序数；它既不是宇宙层级，也不是秩函数。
<!--ja-->
パッケージ `theEarliest x p` は、最小の添字と三つの証明を含みます。関数 `stage` は添字を射影し、その再帰的構成を不透明に保つので、後の議論は順序数性、段階への所属、最小性を使います。これは構成可能集合とその証人から順序数を返す関数であり、宇宙レベルでも階数関数でもありません。
<!--/-->

```agda

opaque
  unfolding stage
  stage-ord : (x : S) (p : ⟨ isL x ⟩) → IsOrd (stage x p)
  stage-ord x p = theEarliest x p .snd .fst

  stage-mem : (x : S) (p : ⟨ isL x ⟩) → ⟨ x ∈ˢ Lset (stage x p) ⟩
```

<!--en-->
The three theorems are the interface, each a projection of the package. `stage-ord` states that the chosen index is an ordinal, so it can later be compared with other indices. `stage-mem` places `x` in the stage `Lset (stage x p)`{.Agda}, the membership fact established by the descent. `stage-earliest` recovers the minimality clause itself: no smaller ordinal σ has `x ∈ˢ Lset σ`. Together they say that `stage x p`{.Agda} is precisely the least index promised at the head of the chapter, reached by projection rather than by reopening the recursion.
<!--zh-->
这三条定理就是接口，每条都是该包的一个投影。`stage-ord` 说所选索引是序数，因而日后可以与其他索引比较。`stage-mem` 把 `x` 放进层 `Lset (stage x p)`{.Agda}，这正是下降所建立的隶属事实。`stage-earliest` 则取回极小性条款本身：没有更小的序数 σ 使 `x ∈ˢ Lset σ`。合起来，它们说 `stage x p`{.Agda} 恰是章首承诺的那个最小索引，只是经由投影、而非重新打开递归而得到。
<!--ja-->
三つの定理がインターフェースであり、どれもパッケージの射影です。`stage-ord` は選ばれた添字が順序数であることを述べ、したがって後に他の添字と比較できます。`stage-mem` は `x` を段階 `Lset (stage x p)`{.Agda} に属させます。これが降下によって示される所属の事実です。`stage-earliest` は最小性の条項そのものを取り戻します。より小さい順序数 σ で `x ∈ˢ Lset σ` となるものはありません。合わせて、これらは `stage x p`{.Agda} が章の冒頭で約束された最小の添字にちょうど等しいことを、再帰を開き直すのではなく射影を通して述べています。
<!--/-->

```agda
  stage-mem x p = theEarliest x p .snd .snd .fst

  stage-earliest : (x : S) (p : ⟨ isL x ⟩)
                 → isLeastOrd (λ σ → x ∈ˢ Lset σ) (stage x p)
  stage-earliest x p = theEarliest x p .snd .snd .snd
```

<!--en-->
## Recap

`leastOrd`{.Agda} extracts the least ordinal satisfying a property from a truncated existence witness. Its specialization `stage x hx`{.Agda} returns the ordinal index α of the least `Lset α`{.Agda} containing `x`; `stage-ord`{.Agda}, `stage-mem`{.Agda}, and `stage-earliest`{.Agda} state exactly those facts. Later arguments can therefore compare or bound these ordinal indices and then use the corresponding constructible stages.
<!--zh-->
## 小结

`leastOrd`{.Agda} 从截断的存在见证中提取满足某条性质的最小序数。其特例 `stage x hx`{.Agda} 返回包含 `x` 的最小 `Lset α`{.Agda} 的序数索引 α；`stage-ord`{.Agda}、`stage-mem`{.Agda} 与 `stage-earliest`{.Agda} 精确陈述这些事实。后续论证因而可以比较或约束这些序数索引，再使用对应的可构造层。
<!--ja-->
## まとめ

`leastOrd`{.Agda} は、ある性質を満たす順序数が存在するという切り詰められた証人から、その最小の順序数を取り出します。その特殊化 `stage x hx`{.Agda} は `x` を含む最小の `Lset α`{.Agda} の順序数添字 α を返し、`stage-ord`{.Agda}、`stage-mem`{.Agda}、`stage-earliest`{.Agda} がその事実を正確に述べます。後の議論では、これらの順序数添字を比較または上から抑えてから、対応する構成可能段階を使えます。
<!--/-->

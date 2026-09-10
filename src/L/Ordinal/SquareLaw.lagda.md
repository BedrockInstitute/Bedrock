<!--en-->
# Ordinal indices, the Gödel pair order, and finite indices

This chapter supplies three concrete orders and conversions used by later counting arguments: the membership well-order on an ordinal's index, the Gödel order on pairs of indices, and the correspondence between members of a finite ordinal and `Fin`.

The first construction compares two indices of an ordinal by membership of the ordinal elements they name; ordinal trichotomy and regularity turn that comparison into a strict well-order on the index type. The second grades a pair of indices by the maximum of its coordinates under that order and orders pairs sharing a maximum coordinate lexicographically; trichotomy, irreflexivity and transitivity are proved directly, and well-foundedness comes from nesting the descent inside two levels of the lexicographic product. The third reads each member of the infinite ordinal ω as a numeral and converts indices of the finite ordinal # n to and from `Fin n`. It then reduces a precise obstruction to the finite pigeonhole principle: a type that contains injective images of finite types of every size cannot itself inject into the square of a fixed finite type.
<!--zh-->
# 序数指标、Gödel 对序与有穷指标

本章为后续计数论证提供三项具体工具：序数指标上的隶属良序、指标对上的 Gödel 序，以及有穷序数成员与 `Fin` 之间的对应。

第一个构造通过指标所指名的序数元素之间的隶属关系来比较两个指标；序数的三歧性与正则性把这个比较变成指标类型上的严格良序。第二个构造用该序下坐标的最大值为指标对分级，并对共享最大坐标的对按字典序排列；三歧性、非自反性与传递性直接证明，而良基性则通过把下降嵌入两层字典序乘积得到。第三个构造把无穷序数 ω 的每个成员读作数码，并在有穷序数 # n 的指标与 `Fin n` 之间作双向转换。随后它把一个准确的不可能性归约为有穷鸽笼原理：若一个类型容纳任意大小的有穷类型的单射像，它就不能单射到某个固定有穷类型的平方中。
<!--ja-->
# 順序数の添字、Gödel 対順序、有限添字

本章では後の計数に使う三つの具体的な道具を与える。順序数の添字上の所属整列順序、添字の対上の Gödel 順序、有限順序数の要素と `Fin` の対応である。

第一の構成は、添字が指す順序数要素どうしの所属によって二つの添字を比較し、順序数の三分性と正則性によってその比較を添字型上の狭義整列順序にします。第二の構成は、その順序での座標の最大値によって添字の対を階級づけし、最大値を共有する対は辞書式に並べます。三分性・非反射性・推移性は直接に証明され、整礎性は降下を辞書式積の二段階に入れ子にすることで得られます。第三の構成は、無限順序数 ω の各要素を数項として読み、有限順序数 # n の添字と `Fin n` の間を双方向に変換します。次に、正確な不可能性を有限鳩の巣原理へ帰着します。任意の大きさの有限型の単射像を含む型は、ある固定された有限型の平方へ単射できません。
<!--/-->

<!--en-->
The chapter works at a fixed universe level ℓ, and it takes one classical assumption as a module parameter: a decision of every proposition at level ℓ-suc ℓ. The comparisons established later need this, because ordinal trichotomy and least-element search each settle a mere-existence question by excluded middle. Keeping the assumption as an explicit parameter records exactly which classical input each construction consumes.
<!--zh-->
本章在固定的宇宙层级 ℓ 上工作，并取一个经典假设作为模块参数：层级 ℓ-suc ℓ 上每个命题的判定。后文建立的比较需要它，因为序数三歧与最小元搜索各自要用排中律裁决一个单纯存在性问题。把这个假设保留为显式参数，恰好记录了每个构造消耗的是哪一份经典输入。
<!--ja-->
本章は固定された宇宙レベル ℓ で働き、一つの古典的仮定をモジュールパラメータとして取ります。それはレベル ℓ-suc ℓ のすべての命題に対する判定です。後に確立される比較にはこれが必要です。順序数の三分法も最小要素の探索も、単なる存在の問いを排中律で決着させるからです。この仮定を明示的なパラメータとして残すことで、各構成がどの古典的入力を消費するかが正確に記録されます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Ordinal.SquareLaw {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

<!--en-->
The mathematical setting is the cumulative hierarchy V, whose sets form a type S and whose membership is truncated existence of an index. Each set a carries a chosen small presentation: an index type ⟪ a ⟫ and an embedding ⟪ a ⟫↪ whose image is a. Reasoning about members of a thus becomes reasoning about indices, and the injectivity of the embedding identifies indices naming the same element. The constructions below treat an arbitrary ordinal α with the certificate IsOrd α: a transitive set all of whose members are transitive, in the von Neumann sense.
<!--zh-->
数学背景是累积层级 V：其集合构成一个类型 S，隶属是「存在某个指标」的截断陈述。每个集合 a 自带一份选定的小呈现：指标类型 ⟪ a ⟫ 与嵌入 ⟪ a ⟫↪，后者的像正是 a。于是讨论 a 的成员就变成讨论指标，而嵌入的单射性把指名同一元素的指标等同起来。下面的构造处理带证书 IsOrd α 的任意序数 α：von Neumann 意义下传递集且成员皆传递的集合。
<!--ja-->
数学的な舞台は累積階層 V です。そこでは集合が型 S をなし、所属は「ある添字の存在」という切り詰められた言明として表されます。各集合 a には選ばれた小さな提示が伴います。添字型 ⟪ a ⟫ と埋め込み ⟪ a ⟫↪ であり、その像こそが a です。したがって a の要素について論じることは添字について論じることになり、埋め込みの単射性が同じ要素を指す添字を同一視します。以下の構成は、IsOrd α の証明書をもつ任意の順序数 α を扱います。これは von Neumann の意味で、推移的であり、その要素もすべて推移的である集合のことです。
<!--/-->

```agda

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; regularityV; ∈-irrefl )
open import V.Model {ℓ} using ( ω-specV; numeralV; numeralV≡# )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ} using ( IsOrd )
```

<!--en-->
A strict well-order combines four properties of one relation: any two points are trichotomically comparable, no point lies strictly below itself, strict comparison is transitive, and every descending chain is well founded. Natural numbers provide the model example. The operation leastOf uses this structure and excluded middle to select a least witness from a merely inhabited proposition-valued family; later, ordinal trichotomy supplies the same three-way comparison for members of an ordinal.
<!--zh-->
严格良序把同一关系的四项性质结合起来：任意两点可作三歧比较，没有点严格小于自身，严格比较具有传递性，并且每条递降链都是良基的。自然数给出典型例子。leastOf 利用这一结构与排中律，从仅仅有元素的命题值族中选出最小见证；稍后，序数三歧为序数成员提供同样的三向比较。
<!--ja-->
狭義整列順序は、一つの関係について四つの性質をまとめます。任意の二点が三分法で比較でき、どの点も自分自身より真に小さくなく、狭義比較が推移的で、すべての降下が整礎です。自然数がその基本例です。leastOf はこの構造と排中律を使い、単に要素が存在する命題値族から最小の証人を選びます。後では、順序数の三分法が順序数の要素に同じ三方向の比較を与えます。
<!--/-->

```agda
open import L.Ordinal {ℓ} using ( mem-ord; ∈#-elim )
open import V.Coding {ℓ} using ( #-inj′; #mono )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; Tri; lt; eq; gt; leastOf; natOrder; module SWO )
```

<!--en-->
The logical vocabulary matches the shape of the statements to be proved. Refutations are functions into the empty type; membership proofs are inhabitants of truncated propositions; a three-way comparison is a sum of its cases, rendered by inl and inr. Paths between pairs and between records are handled by the standard lemmas Σ≡Prop and ΣPathP, which build a path into a dependent pair from paths of the components when the relevant component types are propositions.
<!--zh-->
逻辑词汇与待证陈述的形状相配。反驳是映到空类型的函数；隶属证明是截断命题的居民；三路比较是其各情形的和，由 inl 与 inr 标注。序对之间与记录之间的路径由标准引理 Σ≡Prop 与 ΣPathP 处理：当相关分支类型是命题时，它们从分量的路径构造出进入依赖对的路径。
<!--ja-->
論理の語彙は、証明すべき言明の形に合わせて選ばれています。反証は空型への関数であり、所属の証明は切り詰められた命題の住人であり、三路の比較はその場合の直和で、inl と inr で印づけられます。対やレコードの間のパスは標準補題 Σ≡Prop と ΣPathP で扱います。関係する成分の型が命題であるとき、成分のパスから依存対へのパスを組み立てるものです。
<!--/-->

```agda

import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sigma using ( Σ≡Prop; ΣPathP )
```

<!--en-->
The finite counting part needs arithmetic and the standard finite types. Multiplication _·_ on natural numbers sizes the square of a finite type, and the library equivalence factorEquiv identifies `Fin n × Fin n` with `Fin (n · n)`. The pigeonhole theorem supplies the impossibility that anchors the chapter's last argument: no injection from `Fin (suc n)` to `Fin n` exists. Order on the natural numbers comes with the fact that ≤ is a proposition, which makes comparisons into `Fin` respect the proof-irrelevance of their bound.
<!--zh-->
有穷计数部分需要算术与标准有穷类型。自然数乘法 _·_ 度量有穷类型的平方，库中的等价 factorEquiv 把 `Fin n × Fin n` 与 `Fin (n · n)` 等同起来。鸽笼定理给出本章末尾论证的锚点：从 `Fin (suc n)` 到 `Fin n` 不存在单射。自然数上的序还附带「≤ 是命题」这一事实，这使得到 `Fin` 的比较与其界的证明无关性相容。
<!--ja-->
有限計数の部分には算術と標準的な有限型が必要です。自然数の乗法 _·_ は有限型の平方の大きさを定め、ライブラリの等価 factorEquiv は `Fin n × Fin n` を `Fin (n · n)` と同一視します。鳩の巣定理は、本章の最後の議論の要となる不可能性を供給します。`Fin (suc n)` から `Fin n` への単射は存在しない、というものです。自然数上の順序には「≤ が命題である」という事実が伴い、これにより `Fin` への比較がその上限の証明非依存性と調和します。
<!--/-->

```agda
open import Cubical.Data.Nat using ( _·_ )
import Cubical.Data.Fin.Base as FB
open import Cubical.Data.Fin.Properties using ( factorEquiv; pigeonhole )
open import Cubical.Data.Nat.Order using ( _<_; isProp≤; ≤-refl )
open import Cubical.Foundations.Equiv using ( equivFun; invEq; retEq )
```

<!--en-->
For each set a, the presentation map ⟪ a ⟫↪ turns an index into the member it names. Its fiber over # k therefore contains exactly the indices naming that numeral. When k < n, numeral monotonicity places # k inside # n, and choosing the corresponding fiber point defines the conversion from Fin n into the index type of the finite ordinal. The reverse conversion will use least search, because an arbitrary index does not arrive with its numeral label.
<!--zh-->
对每个集合 a，呈现映射 ⟪ a ⟫↪ 把指标送到它所指名的成员，因此它在 # k 上的原像恰由指名该数码的指标组成。当 k < n 时，数码的单调性把 # k 置于 # n 内，选取相应原像中的点便定义了从 Fin n 到有穷序数指标类型的转换。反向转换将使用最小元搜索，因为任意指标并不自带其数码标号。
<!--ja-->
各集合 a について、提示写像 ⟪ a ⟫↪ は添字を、それが指す要素へ送ります。したがって # k 上の繊維は、まさにその数項を指す添字からなります。k < n なら数項の単調性により # k は # n の中に入り、対応する繊維の点を選ぶことで Fin n から有限順序数の添字型への変換が定まります。逆向きには最小要素の探索を使います。任意の添字には数項のラベルが初めから付いていないからです。
<!--/-->

```agda
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
```

<!--en-->
Well-foundedness is carried by the accessibility predicate: Acc R x holds when every R-predecessor of x is again accessible, acc packages this data, and WellFounded R asks for accessibility of every element. Accessibility certificates are handed downward in the descent arguments of this chapter. Finally, the truth algebra of hProps at level ℓ-suc ℓ is opened, making conjunction and the other logical operations on propositions available to the structure machinery used in the ordinal section.
<!--zh-->
良基性由可及性谓词承载：当 x 的每个 R-前驱都可及时，Acc R x 成立；acc 打包这一数据；WellFounded R 要求每个元素都可及。本章的下降论证正是逐层向下传递这些可及性证书。最后打开层级 ℓ-suc ℓ 上 hProp 的真值代数，使命题上的合取等逻辑运算可供序数一节使用的结构机制调用。
<!--ja-->
整礎性は到達可能性の述語によって運ばれます。x のすべての R-先行者が再び到達可能なとき Acc R x が成り立ち、acc がこのデータを包み、WellFounded R はすべての要素の到達可能性を要求します。本章の降下の議論は、この到達可能性の証明書を下へ下へと受け渡してゆきます。最後に、レベル ℓ-suc ℓ の hProp の真理値代数を開き、命題上の連言などの論理演算を、順序数の節で使う構造の仕組みから利用できるようにします。
<!--/-->

```agda
open InfinitySet using ( #_; ω )
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
Later in this chapter, well-foundedness of the Gödel pair order is obtained by embedding its descent into nested lexicographic descents. The ingredient needed for that is a general construction: given a strict well-order on X and any well-founded relation on Y, the product X × Y carries a natural strict order, and that order is well founded. This section builds exactly that, and nothing more.

Two small points shape the construction. First, the product order compares the first coordinates with the well-order, and only when neither direction of strict comparison holds, that is, when the first coordinates are equal, does it consult the second relation; recovering the equality from the two failed comparisons is what the connexity lemma does. Second, the proof carries an accessibility certificate for the first coordinate and one for the second coordinate simultaneously, mirroring the two-level priority of the order.
<!--zh-->
本章稍后，Gödel 对序的良基性将通过把其下降嵌入嵌套的字典序下降而得到。所需的一般构造是：给定 X 上的严格良序与 Y 上任意良基关系，乘积 X × Y 带有自然的严格序，且该序良基。本节恰好构造这一点，此外无他。

两点塑造了这个构造。其一，乘积序先用良序比较第一坐标，只有当两个方向的严格比较都不成立，即第一坐标相等时，才查阅第二个关系；从两次失败的比较中恢复相等，正是联结性引理所做的。其二，证明同时携带第一坐标与第二坐标的可及性证书，与这个序的两级优先次序相对应。
<!--ja-->
本章の後半では、Gödel 対順序の整礎性を、その降下を入れ子になった辞書式降下に埋め込むことで得ます。そのために必要な材料は一般的な構成です。X 上の狭義整列順序と Y 上の任意の整礎な関係が与えられれば、積 X × Y には自然な狭義順序が伴い、その順序は整礎です。この節はまさにそれだけを組み立てます。

二つの小さな点がこの構成を形づくります。第一に、積の順序はまず整列順序で第一座標を比較し、両方向の狭義比較がともに成り立たないとき、すなわち第一座標が等しいときにのみ第二の関係を参照します。二つの失敗した比較から等式を復元するのが、connex (連結性) の補題の働きです。第二に、証明は第一座標と第二座標のそれぞれに対する到達可能性の証明書を同時に運び、この順序の二段階の優先順位に対応します。
<!--/-->

<!--en-->
A strict well-order trichotomizes any two elements: the comparison data Tri returns either a proof that a is below b, a path a ≡ b, or a proof that b is below a. So if both strict directions have been refuted, only the middle case can remain, and it carries exactly the equality we want. This connexity lemma packages that case analysis; it is not a new order law but a reading of trichotomy data under two refutations.
<!--zh-->
严格良序使任意两个元素三歧：比较数据 Tri 返回「a 低于 b」的证明、路径 a ≡ b，或「b 低于 a」的证明。因此若两个严格方向都被反驳，只剩下中间情形，而它恰好携带我们要的相等。这个联结性引理把这一情形分析打包；它不是新的序定律，而是在两个反驳下对三歧数据的解读。
<!--ja-->
狭義整列順序は任意の二要素を三分します。比較データ Tri は「a が b より下」の証明、パス a ≡ b、あるいは「b が a より下」の証明のいずれかを返します。したがって両方向の狭義比較がともに反証されていれば、残るのは中間の場合だけであり、それがまさに求める等式を運んでいます。この connex の補題はその場合分けをまとめたもので、新しい順序の法則ではなく、二つの反証のもとでの三分法データの読み方です。
<!--/-->

```agda
connex : {ℓc : Level} {A : Type ℓc} (w : SWO A) (a b : A)
       → (SWO._<∙_ w a b → Empty.⊥) → (SWO._<∙_ w b a → Empty.⊥) → a ≡ b
connex w a b ¬ab ¬ba with SWO.tri∙ w a b
... | lt h = Empty.rec (¬ab h)
... | eq p = p
```

<!--en-->
The product is set up generically. The first factor carries a strict well-order u on X, giving access to its relation, its trichotomy and its well-foundedness. The second factor carries any relation _<ᵥ_ on Y that is well founded; no trichotomy or transitivity is demanded of it, since the product will only ever need to descend along it. Both relations are valued at level ℓ-suc ℓ, the level at which the later ordinal comparisons live.
<!--zh-->
乘积以一般方式建立。第一因子带 X 上的严格良序 u，从而可使用其关系、三歧性与良基性。第二因子带 Y 上任意良基的关系 _<ᵥ_；不要求它有三歧性或传递性，因为乘积只需沿它下降。两个关系都取值于层级 ℓ-suc ℓ，即后文序数比较所处的层级。
<!--ja-->
積は一般的に設定されます。第一因子には X 上の狭義整列順序 u が伴い、その関係・三分法・整礎性が使えます。第二因子には Y 上の任意の整礎な関係 _<ᵥ_ が伴います。三分割法や推移性は要求されません。積がこの関係に求めるのは降下だけだからです。両方の関係はレベル ℓ-suc ℓ で値をとります。これは後の順序数の比較が住むレベルです。
<!--/-->

```agda
... | gt h = Empty.rec (¬ba h)


module _ {ℓx ℓy : Level} {X : Type ℓx} {Y : Type ℓy} (u : SWO X)
         (_<ᵥ_ : Y → Y → Type (ℓ-suc ℓ)) (wfv : WellFounded _<ᵥ_) where

  private
    module U = SWO u
```

<!--en-->
The product order _≺×_ has two ways to compare (a , x) below (b , y). Either a is strictly below b in the well-order, or the first coordinates are equal, witnessed by the pair of refutations of both strict directions, and x is below y in the second relation. This is the lexicographic priority stated as a sum: the well-order is consulted first, the second relation only at ties. Alongside the order, the proof plans its data: accProd will build an accessibility certificate for a pair from one for each coordinate.
<!--zh-->
乘积序 _≺×_ 比较两个方式把 (a , x) 排在 (b , y) 之下：或者 a 在良序下严格低于 b；或者第一坐标相等，以对两个严格方向的反驳为证，且 x 在第二个关系下低于 y。这就是以和类型陈述的字典序优先级：先查良序，仅在平局时查第二个关系。与序并列，证明也计划好了其数据：accProd 将从每个坐标的可及性证书造出序对的可及性证书。
<!--ja-->
積の順序 _≺×_ が (a , x) を (b , y) より下に置く道は二つあります。整列順序で a が b より真に下にあるか、あるいは第一座標が等しいこと (両方向の狭義比較への反証の組がそれを証明する) と、第二の関係で x が y より下にあることです。これは辞書式の優先順位を直和として述べたものです。整列順序をまず参照し、引き分けのときのみ第二の関係を見ます。順序と並んで、証明はそのデータを計画します。accProd は各座標の到達可能性の証明書から対の証明書を組み立てます。
<!--/-->

```agda

  _≺×_ : X × Y → X × Y → Type (ℓ-suc ℓ)
  (a , x) ≺× (b , y) =
    (a U.<∙ b) ⊎ (((a U.<∙ b) → Empty.⊥) × ((b U.<∙ a) → Empty.⊥) × (x <ᵥ y))

  private
    accProd : (a : X) → Acc U._<∙_ a → (x : Y) → Acc _<ᵥ_ x → Acc _≺×_ (a , x)
```

<!--en-->
The descent follows the two-tier priority. Given that a is accessible in the well-order and x is accessible in the second relation, any ≺×-predecessor (b , y) falls into one of the two summands. If the first coordinate strictly dropped, then b is a well-order predecessor of a, so its accessibility certificate ru b h applies, and y contributes its own certificate wfv y; recursion on these two strictly smaller certificates builds the certificate for (b , y).
<!--zh-->
下降遵循两级优先次序。已知 a 在良序中可及且 x 在第二个关系中可及，任何 ≺×-前驱 (b , y) 落入和的两个分支之一。若第一坐标严格下降，则 b 是 a 在良序中的前驱，其可及性证书 ru b h 适用，而 y 贡献自己的证书 wfv y；对这两个严格更小的证书递归，就造出 (b , y) 的证书。
<!--ja-->
降下は二段階の優先順位に従います。a が整列順序で到達可能であり x が第二の関係で到達可能だとすると、任意の ≺×-先行者 (b , y) は直和の二つの枝のどちらかに落ちます。第一座標が真に下がっていた場合は、b は整列順序における a の先行者なので、その到達可能性の証明書 ru b h が使え、y は自前の証明書 wfv y を提供します。これらの真に小さい二つの証明書への再帰が (b , y) の証明書を組み立てます。
<!--/-->

```agda
    accProd a (acc ru) = inner
      where
      inner : (x : Y) → Acc _<ᵥ_ x → Acc _≺×_ (a , x)
      inner x (acc rv) = acc λ where
        (b , y) (inl h) → accProd b (ru b h) y (wfv y)
```

<!--en-->
The tie case is where connex earns its place: the second summand asserts both strict comparisons fail, so connex produces a path b ≡ a and the pair may be transported to one with equal first coordinates, reducing descent to the second relation alone, where the certificate rv y h applies. Stacking these two clauses, every pair is accessible, since the well-order makes each first coordinate accessible and the hypothesis makes each second coordinate accessible; this is prodWF, the only statement about the product that the rest of the chapter consumes.
<!--zh-->
平局情形正是联结性引理的用武之地：第二个分支断言两个严格比较都失败，于是 connex 产生路径 b ≡ a，可把该对沿此路径搬运到第一坐标相等的对上，把下降约化为只在第二个关系上进行，那里的证书 rv y h 适用。把这两个子句叠起来，每个序对都可及：良序使每个第一坐标可及，假设使每个第二坐标可及。这就是 prodWF，本章其余部分消耗的关于乘积的唯一陈述。
<!--ja-->
引き分けの場合こそ connex の出番です。第二の枝は両方向の狭義比較が失敗したと主張するので、connex がパス b ≡ a を生み出し、その対はこのパスに沿って第一座標の等しい対へ輸送できます。降下は第二の関係だけの問題に帰着し、そこでは証明書 rv y h が適用されます。この二つの節を重ねれば、すべての対が到達可能です。整列順序が各第一座標を到達可能にし、仮定が各第二座標を到達可能にするからです。これが prodWF であり、本章の残りの部分がこの積について消費する唯一の主張です。
<!--/-->

```agda
        (b , y) (inr (¬ba , ¬ab , h)) →
          subst (λ z → Acc _≺×_ (z , y)) (sym (connex u b a ¬ba ¬ab))
            (inner y (rv y h))

  prodWF : WellFounded _≺×_
  prodWF (a , x) = accProd a (U.wf∙ a) x (wfv x)

```

<!--en-->
## The membership order on an ordinal's index

An ordinal α is a transitive set whose members are all transitive, and its members are linearly ordered by membership; the classical input `ord-tri` makes that order trichotomic. But the counting arguments of later chapters need the order on the indices rather than on the members themselves of the fixed presentation of α: the small type ⟪ α ⟫ whose embedding ⟪ α ⟫↪ has image α. This section transports the membership order from members to indices.

Two distinctions make the transport honest. First, an index m is not itself a set of the hierarchy; the element it names is ⟪ α ⟫↪ m, and all comparisons happen at the level of these named elements, with injectivity of the embedding recovering index equality from element equality. Second, each named element is itself an ordinal, a consequence of transitivity of α, and this is what licenses transitivity and the classical trichotomy at every index. The result is the strict well-order ordSWO on ⟪ α ⟫, the base instance on which the Gödel pair order of the next section is graded.
<!--zh-->
## 序数指标上的隶属序

序数 α 是传递集且成员皆传递，其成员按隶属线性有序；经典输入 `ord-tri` 使这个序三歧。但后续章节的计数论证需要的不是成员本身上的序，而是 α 的固定呈现的指标上的序：小类型 ⟪ α ⟫，其嵌入 ⟪ α ⟫↪ 的像正是 α。本节把隶属序从成员搬运到指标上。

两个区分使这个搬运忠实。其一，指标 m 本身不是层级中的集合；它所指名的元素是 ⟪ α ⟫↪ m，一切比较都发生在这些被指名的元素层面，而嵌入的单射性从元素相等恢复指标相等。其二，每个被指名的元素本身也是序数，这是 α 的传递性的推论，正是它允许在每个指标处使用传递性与经典三歧。结果是 ⟪ α ⟫ 上的严格良序 ordSWO，即下一节 Gödel 对序据以分级的基底实例。
<!--ja-->
## 順序数の添字上の所属順序

順序数 α は推移的であり、その要素もすべて推移的で、要素は所属によって線形に順序づけられます。古典的な入力 `ord-tri` がこの順序を三分的にします。しかし後の章の計数の議論に必要なのは、要素そのもの上の順序ではなく、α の固定された提示の添字上の順序です。小さな型 ⟪ α ⟫ と、その像が α である埋め込み ⟪ α ⟫↪ です。この節は所属順序を要素から添字へと運びます。

二つの区別がこの移し替えを忠実にします。第一に、添字 m それ自体は階層の集合ではありません。それが指す要素は ⟪ α ⟫↪ m であり、比較はすべてこの指名された要素のレベルで行われ、埋め込みの単射性が要素の等式から添字の等式を復元します。第二に、指名された各要素もまた順序数です。これは α の推移性からの帰結であり、各添字で推移性と古典的な三分法を使うことを許すものです。結果として得られるのは ⟪ α ⟫ 上の狭義整列順序 ordSWO で、次の節の Gödel 対順序が階級づけの基礎とする実例です。
<!--/-->

<!--en-->
The relation ≺₁ on indices is defined by membership of the named elements: m ≺₁ n holds exactly when ⟪ α ⟫↪ m is a member of ⟪ α ⟫↪ n in the structure's membership proposition. Everything else in the section reads this definition. The first supporting fact is that each named element is itself an ordinal: since α is transitive and the index m names a member of α, the certificate mem-ord applied to the membership proof member α m yields IsOrd of the named element. This certificate ord-inord is used three more times below.
<!--zh-->
指标上的关系 ≺₁ 由被指名元素间的隶属定义：m ≺₁ n 成立，当且仅当 ⟪ α ⟫↪ m 按结构的隶属命题是 ⟪ α ⟫↪ n 的成员。本节其余内容都围绕这个定义展开。第一个支撑事实是：每个被指名元素本身也是序数。由于 α 传递而指标 m 指名 α 的一个成员，把证书 mem-ord 应用于隶属证明 member α m 便得到被指名元素的 IsOrd。这个证书 ord-inord 在下文还要再用三次。
<!--ja-->
添字上の関係 ≺₁ は、指名された要素どうしの所属によって定義されます。m ≺₁ n が成り立つのは、構造の所属命題において ⟪ α ⟫↪ m が ⟪ α ⟫↪ n の要素であるとき、そのときに限ります。この節の残りはすべてこの定義を読みます。最初の支えとなる事実は、指名された各要素もまた順序数であることです。α が推移的で添字 m が α の要素を指すので、所属の証明 member α m に証明書 mem-ord を適用すれば、指名された要素の IsOrd が得られます。この証明書 ord-inord はこの後さらに三回使われます。
<!--/-->

```agda
module _ (α : S) (oα : IsOrd α) where

  _≺₁_ : ⟪ α ⟫ → ⟪ α ⟫ → Type (ℓ-suc ℓ)
  m ≺₁ n = ⟪ α ⟫↪ m ∈ᵗ ⟪ α ⟫↪ n

  ord-inord : (m : ⟪ α ⟫) → IsOrd (⟪ α ⟫↪ m)
  ord-inord m = mem-ord {A = α} oα (⟪ α ⟫↪ m) (member α m)
```

<!--en-->
Trichotomy on indices comes from trichotomy of the named elements. The classical theorem ord-tri compares two ordinal members, returning either a proof that the first is a member of the second, a path of element equality, or a proof in the other direction, packed as a sum. The auxiliary go matches these three cases: the two membership branches become lt and gt directly, since ≺₁ was defined as membership of named elements.
<!--zh-->
指标的三歧来自被指名元素的三歧。经典定理 ord-tri 比较两个序数成员，返回和类型：第一个是第二个的成员的证明、元素相等的路径，或相反方向的证明。辅助函数 go 匹配这三种情形：两个隶属分支直接成为 lt 与 gt，因为 ≺₁ 正是定义为被指名元素间的隶属。
<!--ja-->
添字の三分法は、指名された要素の三分法から来ます。古典的な定理 ord-tri は二つの順序数要素を比較し、直和を返します。第一が第二の要素であることの証明、要素の等式のパス、あるいは逆方向の証明です。補助の go はこの三つの場合を対応づけます。所属の二つの枝はそのまま lt と gt になります。≺₁ は指名された要素どうしの所属として定義されているからです。
<!--/-->

```agda

  tri₁ : (m n : ⟪ α ⟫) → Tri (m ≺₁ n) (m ≡ n) (n ≺₁ m)
  tri₁ m n = go (ord-tri (⟪ α ⟫↪ m) (ord-inord m) (⟪ α ⟫↪ n) (ord-inord n))
    where
    go : (⟨ ⟪ α ⟫↪ m ∈ˢ ⟪ α ⟫↪ n ⟩
          ⊎ ((⟪ α ⟫↪ m ≡ ⟪ α ⟫↪ n) ⊎ ⟨ ⟪ α ⟫↪ n ∈ˢ ⟪ α ⟫↪ m ⟩))
```

<!--en-->
The equality branch is the only place the presentation is used essentially. Ordinal trichotomy returns equality of the named elements, but the goal is equality of indices, and these are different types. Injectivity of the embedding, recorded as ↪-inj, reflects the element path to a path between indices. With that branch handled, tri₁ is the three-case comparison data Tri on ⟪ α ⟫.
<!--zh-->
相等的分支是唯一实质性使用呈现之处。序数三歧返回的是被指名元素的相等，而目标是指标的相等，两者是不同的类型。嵌入的单射性 ↪-inj 把元素路径反映为指标间的路径。处理好这个分支后，tri₁ 就是 ⟪ α ⟫ 上的三情形比较数据 Tri。
<!--ja-->
等号の枝だけが、提示を本質的に使う箇所です。順序数の三分法が返すのは指名された要素の等式ですが、目標は添字の等式であり、両者は異なる型です。埋め込みの単射性 ↪-inj が要素のパスを添字の間のパスへと反映します。この枝を処理すれば、tri₁ は ⟪ α ⟫ 上の三場合の比較データ Tri になります。
<!--/-->

```agda
       → Tri (m ≺₁ n) (m ≡ n) (n ≺₁ m)
    go (inl h)       = lt h
    go (inr (inl p)) = eq (↪-inj {a = α} p)
    go (inr (inr h)) = gt h

  irr₁ : (m : ⟪ α ⟫) → (m ≺₁ m → Empty.⊥)
```

<!--en-->
Irreflexivity and transitivity are inherited from the named elements. No set is a member of itself, so m ≺₁ m refutes itself. For transitivity, m ≺₁ n and n ≺₁ k are both membership facts about ⟪ α ⟫↪ k, an ordinal by ord-inord, and the first component of the IsOrd certificate asserts transitivity of membership among the members of an ordinal, so it chains the two facts directly. Accessibility transfers the same way: if every member of the named element ⟪ α ⟫↪ m is accessible under membership, then every ≺₁-predecessor n of m names a member, so its certificate can be fed the membership fact for the index n, and acc₁ returns the accessibility of m under ≺₁.
<!--zh-->
非自反性与传递性从被指名元素继承。没有集合属于自身，故 m ≺₁ m 自我反驳。对传递性，m ≺₁ n 与 n ≺₁ k 都是关于 ⟪ α ⟫↪ k 的隶属事实，而由 ord-inord 它是序数；IsOrd 证书的第一个分量断言序数成员间隶属的传递性，因此直接把两个事实串联。可及性同样搬运：若被指名元素 ⟪ α ⟫↪ m 的每个成员在隶属下可及，则 m 的每个 ≺₁-前驱 n 指名一个成员，把指标 n 的隶属事实喂给其证书，acc₁ 便返回 m 在 ≺₁ 下的可及性。
<!--ja-->
非反射性と推移性は、指名された要素から引き継がれます。自分自身に属する集合はないので、m ≺₁ m は自己反証します。推移性については、m ≺₁ n と n ≺₁ k はどちらも ⟪ α ⟫↪ k についての所属の事実であり、ord-inord によりこれは順序数です。IsOrd の証明書の最初の成分は、順序数の要素どうしの所属の推移性を主張するので、二つの事実を直接つなぎます。到達可能性も同じように運ばれます。指名された要素 ⟪ α ⟫↪ m の各要素が所属のもとで到達可能なら、m の各 ≺×-ではなく ≺₁-先行者 n はある要素を指すので、添字 n に対する所属の事実をその証明書に渡せば、acc₁ が ≺₁ のもとでの m の到達可能性を返します。
<!--/-->

```agda
  irr₁ m h = ∈-irrefl (⟪ α ⟫↪ m) h

  trans₁ : (m n k : ⟪ α ⟫) → m ≺₁ n → n ≺₁ k → m ≺₁ k
  trans₁ m n k h h' = ord-inord k .fst h h'

  acc₁ : (m : ⟪ α ⟫) → Acc _∈ᵗ_ (⟪ α ⟫↪ m) → Acc _≺₁_ m
  acc₁ m (acc r) = acc (λ n n≺m → acc₁ n (r (⟪ α ⟫↪ n) n≺m))
```

<!--en-->
Well-foundedness of ≺₁ is now one step away: regularity on the ambient hierarchy hands an accessibility certificate for membership to every set, so every named element ⟪ α ⟫↪ m is accessible, and acc₁ lifts that to accessibility of the index m. This is wf₁, the well-foundedness the search in the finite section will reuse. The record ordSWO then packages the relation with its four laws into the interface SWO, the same five fields the natural-number instance of the strict well-order chapter supplies.
<!--zh-->
≺₁ 的良基性只差一步：环境层级上的正则性把隶属下的可及性证书交给每个集合，故每个被指名元素 ⟪ α ⟫↪ m 可及，而 acc₁ 把它提升为指标 m 的可及性。这就是 wf₁，有穷一节的搜索将复用的良基性。随后记录 ordSWO 把关系与其四条定律打包进接口 SWO，与严格良序一章的自然数实例供给的是同样的五个字段。
<!--ja-->
≺₁ の整礎性まであと一歩です。周囲の階層での正則性が、所属のもとでの到達可能性の証明書をすべての集合に渡すので、指名された要素 ⟪ α ⟫↪ m はそれぞれ到達可能であり、acc₁ がそれを添字 m の到達可能性へと持ち上げます。これが wf₁ であり、有限の節の探索が再利用する整礎性です。そしてレコード ordSWO が関係とその四つの法則をインターフェース SWO にまとめます。狭義整列順序の章の自然数の実例が供給するのと同じ五つのフィールドです。
<!--/-->

```agda

  wf₁ : WellFounded _≺₁_
  wf₁ m = acc₁ m (regularityV (⟪ α ⟫↪ m))

  ordSWO : SWO ⟪ α ⟫
  ordSWO = record
    { _<∙_   = _≺₁_
```

<!--en-->
Assembling ordSWO is the point of the section: an instance, not new mathematics. Every later construction that takes a SWO can now run on the index of any ordinal, and the pair order of the next section consumes exactly this instance. Nothing about ω or finite ordinals is special here; the argument used only transitivity of α, the embedding, classical trichotomy and regularity.
<!--zh-->
组装 ordSWO 正是本节的要点：这是一个实例，而非新的数学。此后任何以 SWO 为输入的构造都能运行在任意序数的指标上，下一节的对序消耗的正是这个实例。这里对 ω 或有穷序数没有任何特殊处理；论证只用到了 α 的传递性、嵌入、经典三歧与正则性。
<!--ja-->
ordSWO の組み立てこそがこの節の要点です。これは実例であって新しい数学ではありません。SWO を入力とする以後の構成はどれも、任意の順序数の添字の上で動くようになり、次の節の対順序が消費するのはまさにこの実例です。ここで ω や有限順序数が特別扱いされることはありません。議論に使ったのは α の推移性、埋め込み、古典的な三分法、そして正則性だけです。
<!--/-->

```agda
    ; tri∙   = tri₁
    ; irr∙   = irr₁
    ; trans∙ = trans₁
    ; wf∙    = wf₁ }


```

<!--en-->
The classical Gödel pairing idea orders pairs of indices so that descent on pairs can be analyzed coordinate by coordinate. The order used here is not the plain lexicographic order: it is graded first by the ≺₁-maximum of the two coordinates, so that pairs of small coordinates sink below pairs with a large coordinate regardless of arrangement, and only pairs sharing a maximum grade are compared by first coordinate and then by second coordinate. This section defines that order and proves trichotomy, irreflexivity and transitivity directly from the corresponding laws of ≺₁; its well-foundedness, which needs the lexicographic product of the earlier section, follows in the next block of code.

The maximum requires one preliminary: a reflexive companion ≤₁ of ≺₁, defined as a sum of the strict relation and equality. Since trichotomy data is explicit three-case data, the maximum of two indices is computed by inspecting the comparison and returning one of the two inputs, and the certificate max-spec records the two ≤₁-facts that make the returned value a genuine maximum.
<!--zh-->
经典的 Gödel 配对想法是给指标对排一个序，使对上的下降能按坐标逐层分析。这里用的序不是普通的字典序：它先用两坐标的 ≺₁-最大值分级，使坐标都小的对无论怎样排列都沉到有大坐标的对之下，只有共享最大等级的对才按第一坐标、再按第二坐标比较。本节定义这个序，并从 ≺₁ 的相应定律直接证明三歧、非自反与传递；其良基性需要前文的字典序乘积，在下一段代码中给出。

最大值需要一个预备：≺₁ 的自反伴随 ≤₁，定义为严格关系与相等之和。由于三歧数据是显式的三情形数据，两个指标的最大值通过检查比较、返回两个输入之一来计算，而证书 max-spec 记录使返回值成为真正最大值的两个 ≤₁-事实。
<!--ja-->
古典的な Gödel の対の考え方は、指字の対に順序を与え、対の上の降下を座標ごとに分析できるようにするものです。ここで使う順序は普通の辞書式順序ではありません。まず二つの座標の ≺₁-最大値で階級づけを行うので、座標がどちらも小さい対は、並び方にかかわらず大きい座標をもつ対の下に沈み、最大の階級を共有する対だけが第一座標、次に第二座標で比較されます。この節はその順序を定義し、≺₁ の対応する法則から三分法・非反射性・推移性を直接証明します。整礎性には前の節の辞書式積が必要で、次のコードのまとまりで与えられます。

最大値には一つの準備が要ります。≺₁ の反射的な伴い手 ≤₁ で、狭義の関係と等式の直和として定義します。三分法データは明示的な三場合のデータなので、二つの添字の最大値は比較を検査して二つの入力のどちらかを返すことで計算され、証明書 max-spec は返された値が真の最大値であることを支える二つの ≤₁ の事実を記録します。
<!--/-->

<!--en-->
The non-strict companion ≤₁ collects the two ways one index can fail to be strictly above another: m ≤₁ n holds either because m ≺₁ n or because m equals n. With it, the maximum is defined from comparison data: maxGo takes the three-case comparison of m and n as an argument and returns the larger one, n when m is strictly below, and m in the two remaining cases.
<!--zh-->
非严格伴随 ≤₁ 收集了「一个指标不严格高于另一个」的两种方式：m ≤₁ n 成立，或者因为 m ≺₁ n，或者因为 m 与 n 相等。借助它，最大值由比较数据定义：maxGo 以 m 与 n 的三情形比较为参数，返回较大者，m 严格低于时返回 n，其余两种情形返回 m。
<!--ja-->
非狭義の伴い手 ≤₁ は、ある添字が別の添字より真には上にない二つの場合を集めます。m ≤₁ n が成り立つのは、m ≺₁ n のときか、m が n と等しいときです。これを使って最大値は比較データから定義されます。maxGo は m と n の三場合の比較を引数に取り、大きい方を返します。m が真に下のときは n を、残る二つの場合は m を返します。
<!--/-->

```agda
  _≤₁_ : ⟪ α ⟫ → ⟪ α ⟫ → Type (ℓ-suc ℓ)
  m ≤₁ n = (m ≺₁ n) ⊎ (m ≡ n)

  maxGo : (m n : ⟪ α ⟫) → Tri (m ≺₁ n) (m ≡ n) (n ≺₁ m) → ⟪ α ⟫
  maxGo m n (lt _) = n
  maxGo m n (eq _) = m
```

<!--en-->
The function maxOrd is the maximum made total: it first computes the comparison tri₁ m n and then applies maxGo to that data. Because tri₁ is classical input, maxOrd is a defined function whose values depend on that data, not on an independently proved totality claim. The specification max-spec states what makes the result a maximum: each input is ≤₁ the output, and it is proved by the same case analysis, which the following where block carries out.
<!--zh-->
函数 maxOrd 是完全化的最大值：先计算比较 tri₁ m n，再把 maxGo 应用于该数据。由于 tri₁ 是经典输入，maxOrd 是一个取值依赖该数据的定义函数，而非单独证明的完全性断言。规格 max-spec 陈述使结果成为最大值的内容：每个输入都 ≤₁ 输出，其证明也走同一情形分析，接下来的 where 块执行之。
<!--ja-->
関数 maxOrd は最大値を全域化したものです。まず比較 tri₁ m n を計算し、そのデータに maxGo を適用します。tri₁ が古典的な入力であるため、maxOrd は値がそのデータに依存する定義された関数であり、独立に証明された全域性の主張ではありません。仕様 max-spec は、結果を最大値たらしめるものを述べます。各入力が出力に対して ≤₁ であることであり、その証明も同じ場合分けによります。次の where ブロックがそれを実行します。
<!--/-->

```agda
  maxGo m n (gt _) = m

  maxOrd : ⟪ α ⟫ → ⟪ α ⟫ → ⟪ α ⟫
  maxOrd m n = maxGo m n (tri₁ m n)

  max-spec : (m n : ⟪ α ⟫) → (m ≤₁ maxOrd m n) × (n ≤₁ maxOrd m n)
  max-spec m n = go (tri₁ m n)
```

<!--en-->
The first two comparison cases certify both ≤₁-facts directly. If m ≺₁ n, then m ≤₁ n uses the strict branch and n ≤₁ n uses the equality branch; when m and n agree, symmetry of the path supplies the second equality.
<!--zh-->
前两个比较情形直接认证两条 ≤₁ 事实。若 m ≺₁ n，则 m ≤₁ n 使用严格分支，而 n ≤₁ n 使用相等分支；当 m 与 n 相等时，路径的对称性给出第二条等式。
<!--ja-->
最初の二つの比較の場合は、二つの ≤₁ の事実を直接に証明します。m ≺₁ n なら m ≤₁ n は狭義の枝を、n ≤₁ n は等号の枝を使います。m と n が一致する場合は、パスの対称性が二つ目の等式を与えます。
<!--/-->

```agda
    where
    go : (t : Tri (m ≺₁ n) (m ≡ n) (n ≺₁ m))
       → (m ≤₁ maxGo m n t) × (n ≤₁ maxGo m n t)
    go (lt h) = inl h , inr refl
    go (eq p) = inr refl , inr (sym p)
```

<!--en-->
The remaining case is symmetric: when n ≺₁ m, the chosen maximum is m. Thus max-spec says precisely that both inputs lie below the computed maximum in the reflexive order ≤₁.
<!--zh-->
余下情形与之对称：若 n ≺₁ m，则选出的最大值是 m。因此 max-spec 恰好断言两个输入在自反序 ≤₁ 中都不超过计算所得的最大值。
<!--ja-->
残る場合は対称です。n ≺₁ m なら、選ばれる最大値は m です。したがって max-spec は、二つの入力がともに反射的な順序 ≤₁ で計算された最大値以下にあることを述べています。
<!--/-->

```agda
    go (gt h) = inr refl , inl h
```

<!--en-->
The type Pair collects the square of the index: an element is a pair (a , b) of indices of α. The order ≺ on Pair is defined by its three-tier priority as a nested sum. The first summand compares grades: maxOrd a b is strictly below maxOrd c d. If the grades tie, the second summand requires the grade equality and then compares coordinates: a strictly below c, or, if a equals c, b strictly below d.
<!--zh-->
类型 Pair 收集指标的平方：一个元素是 α 的指标对 (a , b)。Pair 上的序 ≺ 以嵌套和定义出它的三级优先次序。第一个分支比较等级：maxOrd a b 严格低于 maxOrd c d。若等级持平，第二个分支要求等级相等，再比较坐标：a 严格低于 c，或在 a 等于 c 时 b 严格低于 d。
<!--ja-->
型 Pair は添字の平方を集めます。要素は α の添字の対 (a , b) です。Pair 上の順序 ≺ は、その三段階の優先順位を入れ子の直和として定義します。第一の枝は階級を比較します。maxOrd a b が maxOrd c d より真に下にあることです。階級が並んだときは、第二の枝が階級の等式を要求したうえで座標を比較します。a が c より真に下にあるか、a が c に等しければ b が d より真に下にあることです。
<!--/-->

```agda

  Pair : Type ℓ
  Pair = ⟪ α ⟫ × ⟪ α ⟫

  _≺_ : Pair → Pair → Type (ℓ-suc ℓ)
  (a , b) ≺ (c , d) =
```

<!--en-->
The proof of trichotomy mirrors the definition's nesting from the outside in. The outer analysis M-case compares the two grades with tri₁; when the grades are strictly ordered, the whole pairs are strictly ordered by the first summand, in either direction. Only the tie case needs the inner tiers, and tri≺ is assembled as one function returning the three-case data for any two pairs.
<!--zh-->
三歧性的证明由外向内镜像定义的嵌套。外层分析 M-case 用 tri₁ 比较两个等级；当等级严格有序时，整对就在任一方向上被第一个分支严格排序。只有平局情形才需要内层，tri≺ 作为单个函数组装而成，对任意两对返回三情形数据。
<!--ja-->
三分法の証明は、定義の入れ子を外から内へと写します。外側の分析 M-case は tri₁ で二つの階級を比較します。階級が真に順序づけられていれば、対全体がどちらの方向でも第一の枝により真に順序づけられます。引き分けの場合だけが内側の段を必要とし、tri≺ は任意の二つの対について三場合のデータを返す一つの関数として組み立てられます。
<!--/-->

```agda
    (maxOrd a b ≺₁ maxOrd c d)
      ⊎ ((maxOrd a b ≡ maxOrd c d) × ((a ≺₁ c) ⊎ ((a ≡ c) × (b ≺₁ d))))

  tri≺ : (p q : Pair) → Tri (p ≺ q) (p ≡ q) (q ≺ p)
  tri≺ (a , b) (c , d) = M-case (tri₁ (maxOrd a b) (maxOrd c d))
    where
```

<!--en-->
The deepest case Y-case handles pairs whose grades and first coordinates both agree, comparing the second coordinates. A strict comparison of b and d puts the pairs strictly in order in the matching direction, with the two equalities carried along as witnesses that the outer tiers really tie; the reverse direction is symmetric.
<!--zh-->
最深的情形 Y-case 处理等级与第一坐标都一致的对，比较第二坐标。b 与 d 的严格比较按相应方向使两对严格有序，两个等式作为「外层确实持平」的见证一并携带；反方向对称。
<!--ja-->
最も深い場合 Y-case は、階級と第一座標がともに一致する対を扱い、第二座標を比較します。b と d の狭義比較があれば、対応する方向で対は真に順序づけられ、二つの等式は外の段が本当に並んでいることの証人として一緒に運ばれます。逆方向は対称です。
<!--/-->

```agda
    Y-case : (e : maxOrd a b ≡ maxOrd c d) (f : a ≡ c)
           → Tri (b ≺₁ d) (b ≡ d) (d ≺₁ b)
           → Tri ((a , b) ≺ (c , d)) ((a , b) ≡ (c , d)) ((c , d) ≺ (a , b))
    Y-case e f (lt h) = lt (inr (e , inr (f , h)))
    Y-case e f (gt h) = gt (inr (sym e , inr (sym f , h)))
```

<!--en-->
When the second coordinates also agree, the two pairs are equal, and cong₂ on the pairing constructor turns the two coordinate paths into a path between pairs; this is why the equality branch of the comparison data carries actual paths rather than bare tags. One tier up, X-case compares the first coordinates: a strict comparison settles the order at that tier, and the tie case descends to Y-case with the comparison of b and d.
<!--zh-->
当第二坐标也一致时，两对相等，pairing 构造子上的 cong₂ 把两个坐标路径变成对之间的路径；这正是比较数据的相等分支携带实际路径而非裸标签的原因。向上一层，X-case 比较第一坐标：严格比较在该层决定次序，平局情形带着 b 与 d 的比较下降到 Y-case。
<!--ja-->
第二座標まで一致するときは、二つの対は等しく、対の構成子への cong₂ が二つの座標のパスを対の間のパスに変えます。比較データの等号の枝が裸のタグではなく実際のパスを運ぶのはこのためです。一段上では、X-case が第一座標を比較します。狭義の比較がその段で順序を決め、引き分けの場合は b と d の比較を連れて Y-case へ降ります。
<!--/-->

```agda
    Y-case e f (eq g) = eq (cong₂ _,_ f g)

    X-case : (e : maxOrd a b ≡ maxOrd c d)
           → Tri (a ≺₁ c) (a ≡ c) (c ≺₁ a)
           → Tri ((a , b) ≺ (c , d)) ((a , b) ≡ (c , d)) ((c , d) ≺ (a , b))
    X-case e (lt h) = lt (inr (e , inl h))
```

<!--en-->
Finally the top tier: M-case compares the grades themselves. The two strict cases are the first summand of ≺ applied directly. The signature of M-case spells out that its input is exactly the trichotomy data for the two grades, so the reader can see the whole proof of tri≺ as one three-fold case analysis, tier by tier, each tier consuming the comparison data of the one below.
<!--zh-->
最后是顶层：M-case 比较等级本身。两个严格情形直接应用 ≺ 的第一个分支。M-case 的签名明确其输入正是两个等级的三歧数据，于是 tri≺ 的整个证明可以读作逐层进行的一次三重情形分析，每一层消耗下一层的比较数据。
<!--ja-->
最後に最上段です。M-case が階級そのものを比較します。二つの狭義の場合は ≺ の第一の枝をそのまま適用します。M-case のシグネチャは、入力がまさに二つの階級に対する三分法データであることを明示するので、tri≺ の証明全体を、一つ下の段の比較データを消費しながら段ごとに進む一つの三重の場合分けとして読めます。
<!--/-->

```agda
    X-case e (gt h) = gt (inr (sym e , inl h))
    X-case e (eq f) = Y-case e f (tri₁ b d)

    M-case : Tri (maxOrd a b ≺₁ maxOrd c d)
                 (maxOrd a b ≡ maxOrd c d)
                 (maxOrd c d ≺₁ maxOrd a b)
```

<!--en-->
The three cases of M-case close the analysis: strict in the grades, or a tie descending through the first and then the second coordinate. With tri≺ in hand, the order ≺ is trichotomic as data, which is what later uniqueness arguments will consume.
<!--zh-->
M-case 的三个情形结束分析：等级严格，或平局经第一坐标再到第二坐标下降。有了 tri≺，序 ≺ 作为数据是三歧的，这正是后续唯一性论证要消耗的性质。
<!--ja-->
M-case の三つの場合が分析を閉じます。階級で狭義に、あるいは引き分けから第一座標を経て第二座標へと降りる場合です。tri≺ が手に入れば、順序 ≺ はデータとして三分的であり、これが後の一意性の議論が消費する性質です。
<!--/-->

```agda
           → Tri ((a , b) ≺ (c , d)) ((a , b) ≡ (c , d)) ((c , d) ≺ (a , b))
    M-case (lt h) = lt (inl h)
    M-case (gt h) = gt (inl h)
    M-case (eq e) = X-case e (tri₁ a c)

  irr≺ : (p : Pair) → (p ≺ p → Empty.⊥)
```

<!--en-->
Irreflexivity of the pair order is short because each tier already knows how to refute its own strict comparison. If (a , b) ≺ (a , b), the witness falls into one of the three summands of the nested definition; each is a strict ≺₁-fact about a coordinate or a grade, and the corresponding irr₁ turns it into a contradiction. The grade case uses irr₁ at maxOrd a b, the first-coordinate case at a, the second-coordinate case at b.
<!--zh-->
对序的非自反性很简短，因为每一层已知道如何反驳自己的严格比较。若 (a , b) ≺ (a , b)，其见证落入嵌套定义的三个分支之一；每个都是关于某坐标或某等级的严格 ≺₁-事实，相应的 irr₁ 把它变成矛盾。等级情形在 maxOrd a b 处用 irr₁，第一坐标情形在 a 处，第二坐标情形在 b 处。
<!--ja-->
対の順序の非反射性は短く済みます。それぞれの段がすでに自分の狭義比較の反証の仕方を知っているからです。(a , b) ≺ (a , b) なら、その証明は入れ子の定義の三つの枝のどれかに落ちます。いずれも座標か階級についての狭義の ≺₁ の事実であり、対応する irr₁ が矛盾に導きます。階級の場合は maxOrd a b で、第一座標の場合は a で、第二座標の場合は b で irr₁ を使います。
<!--/-->

```agda
  irr≺ (a , b) (inl h)              = irr₁ (maxOrd a b) h
  irr≺ (a , b) (inr (e , inl h))    = irr₁ a h
  irr≺ (a , b) (inr (e , inr (f , h))) = irr₁ b h

  trans≺ : (p q r : Pair) → p ≺ q → q ≺ r → p ≺ r
  trans≺ (a , b) (c , d) (e , f) = goM
```

<!--en-->
Transitivity is the substantial law, and its proof is organized around the three grades: M₁ the grade of (a , b), M₂ of (c , d), M₃ of (e , f). The lemmas goY and goX handle the inner tiers first. goY is nothing but transitivity of ≺₁ applied to the second coordinates; it is the composite argument of the innermost case below.
<!--zh-->
传递性是实质的定律，其证明围绕三个等级组织：M₁ 是 (a , b) 的等级，M₂ 是 (c , d) 的，M₃ 是 (e , f) 的。引理 goY 与 goX 先处理内层。goY 不过是把 ≺₁ 的传递性应用于第二坐标；它是下文最内层情形的复合论证。
<!--ja-->
推移性が本質的な法則で、その証明は三つの階級を軸に組織されます。M₁ は (a , b) の階級、M₂ は (c , d) の、M₃ は (e , f) の階級です。補題 goY と goX がまず内側の段を扱います。goY は第二座標に ≺₁ の推移性を適用したにすぎず、後の最も内側の場合の合成の議論になります。
<!--/-->

```agda
    where
    M₁ = maxOrd a b
    M₂ = maxOrd c d
    M₃ = maxOrd e f

    goY : (b ≺₁ d) → (d ≺₁ f) → (b ≺₁ f)
```

<!--en-->
The lemma goX composes the coordinate-level verdicts of the two strict steps. When both steps are strict in the first coordinate, transitivity of ≺₁ composes them. When one step is strict and the other is a first-coordinate equality, the strict fact is transported along that path, since a ≺₁ c and c ≡ e give a ≺₁ e by substitution. Both equalities is the remaining case, deferred to the pair of second coordinates.
<!--zh-->
引理 goX 复合两个严格步骤在坐标层面的裁决。当两步都在第一坐标严格时，≺₁ 的传递性复合它们。当一步严格而另一步是第一坐标相等时，严格事实沿该路径搬运，因为 a ≺₁ c 与 c ≡ e 经代入给出 a ≺₁ e。两者皆相等是剩余情形，交给第二坐标处理。
<!--ja-->
補題 goX は、二つの狭義のステップの座標レベルでの判定を合成します。両ステップが第一座標で狭義のときは、≺₁ の推移性がそれらを合成します。片方が狭義でもう片方が第一座標の等式のときは、そのパスに沿って狭義の事実が輸送されます。a ≺₁ c と c ≡ e から代入により a ≺₁ e が得られるからです。両方とも等式の場合が残り、第二座標の組に委ねられます。
<!--/-->

```agda
    goY = trans₁ b d f

    goX : ((a ≺₁ c) ⊎ ((a ≡ c) × (b ≺₁ d)))
        → ((c ≺₁ e) ⊎ ((c ≡ e) × (d ≺₁ f)))
        → ((a ≺₁ e) ⊎ ((a ≡ e) × (b ≺₁ f)))
    goX (inl h) (inl h') = inl (trans₁ a c e h h')
```

<!--en-->
The remaining case passes from goX to the pair of second coordinates, and their equality paths are concatenated to witness that the grades of the endpoints coincide. With these two lemmas prepared, the signature of goM states the composition problem at the top tier: from a strict step or tie between M₁ and M₂, and one between M₂ and M₃, produce the corresponding verdict between M₁ and M₃. The structure exactly mirrors goX, one level up.
<!--zh-->
剩余情形从 goX 交给第二坐标的对，其相等路径拼接起来见证两端点的等级重合。这两个引理备好后，goM 的签名在顶层陈述复合问题：从 M₁ 与 M₂ 之间的严格步骤或平局，以及 M₂ 与 M₃ 之间的相应裁决，产出 M₁ 与 M₃ 之间的相应裁决。其结构恰好是 goX 向上一层的镜像。
<!--ja-->
残った場合は goX から第二座標の組へ渡され、それらの等式のパスは連結されて、両端の階級が一致することの証人となります。この二つの補題をそろえて、goM のシグネチャは最上段での合成の問題を述べます。M₁ と M₂ の間の狭義のステップか引き分け、および M₂ と M₃ の間の対応する判定から、M₁ と M₃ の間の対応する判定を作ることです。その構造はちょうど一段上の goX の写しです。
<!--/-->

```agda
    goX (inl h) (inr (e₂ , _)) = inl (subst (λ w → a ≺₁ w) e₂ h)
    goX (inr (e₁ , _)) (inl h') = inl (subst (λ w → w ≺₁ e) (sym e₁) h')
    goX (inr (e₁ , s₁)) (inr (e₂ , s₂)) = inr (e₁ ∙ e₂ , goY s₁ s₂)

    goM : ((M₁ ≺₁ M₂) ⊎ ((M₁ ≡ M₂) × ((a ≺₁ c) ⊎ ((a ≡ c) × (b ≺₁ d)))))
        → ((M₂ ≺₁ M₃) ⊎ ((M₂ ≡ M₃) × ((c ≺₁ e) ⊎ ((c ≡ e) × (d ≺₁ f)))))
```

<!--en-->
The four clauses of `goM` are `goX` shifted one tier up. If both steps are strict between the maxima, transitivity of ≺₁ composes `M₁ ≺₁ M₂` and `M₂ ≺₁ M₃`. If one step is strict and the other is a tie at the maximum, the strict fact is transported along the equality path: `M₁ ≺₁ M₂` together with `M₂ ≡ M₃` yields `M₁ ≺₁ M₃` by substitution, and symmetrically with `sym e₁` when the tie comes first. Only when both steps are ties at the maximum do we remain there, recording `e₁ ∙ e₂` as the concatenated path of grades and delegating the second coordinates to `goX`.
<!--zh-->
goM 的四个分支正是 goX 上移一层之后的模样。若两个极大值之间的两步都是严格步骤，就用 ≺₁ 的传递性把 `M₁ ≺₁ M₂` 与 `M₂ ≺₁ M₃` 复合起来。若其中一步严格而另一步在极大值处是等值，则严格事实沿等值路径搬运：由 `M₁ ≺₁ M₂` 和 `M₂ ≡ M₃` 经替换得到 `M₁ ≺₁ M₃`；等值在前时对称地使用 `sym e₁`。只有当两步都是极大值处的等值时才留在本层：记 `e₁ ∙ e₂` 为级差等值的拼接路径，并把第二坐标交给 goX 处理。
<!--ja-->
goM の 4 つの節は、goX を一段上に移した形をしている。両方のステップが最大値の間で真に狭いなら、≺₁ の推移性で `M₁ ≺₁ M₂` と `M₂ ≺₁ M₃` を合成する。片方だけが狭く、他方が最大値での一致であるときは、等しいことを示す経路に沿って狭い事実を輸送する。すなわち `M₁ ≺₁ M₂` と `M₂ ≡ M₃` から置換により `M₁ ≺₁ M₃` が出て、一致が先に来る場合は対称に `sym e₁` を使う。両方とも最大値での一致のときだけ同じ段に留まり、級の一致を連結した経路 `e₁ ∙ e₂` を記録し、第二座標を goX に委ねる。
<!--/-->

```agda
        → ((M₁ ≺₁ M₃) ⊎ ((M₁ ≡ M₃) × ((a ≺₁ e) ⊎ ((a ≡ e) × (b ≺₁ f)))))
    goM (inl h) (inl h') = inl (trans₁ M₁ M₂ M₃ h h')
    goM (inl h) (inr (e₂ , _)) = inl (subst (λ w → M₁ ≺₁ w) e₂ h)
    goM (inr (e₁ , _)) (inl h') = inl (subst (λ w → w ≺₁ M₃) (sym e₁) h')
    goM (inr (e₁ , s₁)) (inr (e₂ , s₂)) = inr (e₁ ∙ e₂ , goX s₁ s₂)
```

<!--en-->
To borrow the well-foundedness of the lexicographic product, each pair is re-exposed as a triple: `f` stores the grade `maxOrd a b` in front of the pair `(a , b)`. This map is injective for a trivial reason: a path between the triples can be projected onto the pair stored in the second component, and that projection `cong snd` recovers the pair equality outright.
<!--zh-->
为了借用字典序乘积的良基性，把每个序对重新呈现为三元组：f 把级差 `maxOrd a b` 记在序对 `(a , b)` 之前。这个映射的单射性几乎是显然的：三元组之间的路径可以投影到存放在第二分量中的序对上，投影 `cong snd` 直接还原出序对的相等。
<!--ja-->
辞書式積の整礎性を借りるために、各対を三つ組として改めて提示する。f は級である `maxOrd a b` を対 `(a , b)` の手前に記録する。この射の単射性はほとんど自明で、三つ組の間の経路を第二成分に格納された対へ射影すればよく、その射影 `cong snd` が対の一致をそのまま回復する。
<!--/-->

```agda

  f : Pair → ⟪ α ⟫ × (⟪ α ⟫ × ⟪ α ⟫)
  f (a , b) = maxOrd a b , (a , b)

  f-inj : {p q : Pair} → f p ≡ f q → p ≡ q
  f-inj {a , b} {c , d} e = cong snd e

  _≺²_ : (⟪ α ⟫ × ⟪ α ⟫) → (⟪ α ⟫ × ⟪ α ⟫) → Type (ℓ-suc ℓ)
```

<!--en-->
Two lexicographic products are now instantiated with the ordinal order as the outer component. The relation `_≺²_` compares pairs of indices: first by ≺₁ on the left coordinate, and, when neither direction holds there, by ≺₁ on the right coordinate; `prodWF` supplied well-foundedness for exactly this shape. Stacking once more, `_≺³_` compares the graded triples on which `f` lands, so descent under `_≺³_` is a three-tier lexicographic descent: grade, first coordinate, second coordinate.
<!--zh-->
现在以序数序为外层分量实例化两个字典序乘积。关系 `_≺²_` 比较指标的序对：先比较左坐标上的 ≺₁，当两个方向都不成立时再比较右坐标上的 ≺₁；prodWF 恰好为这种形状给出良基性。再堆叠一次得到 `_≺³_`，它比较 f 所落入的带级三元组，于是 `_≺³_` 下的递降是三级字典序递降：级差、第一坐标、第二坐标。
<!--ja-->
ここで順序数順序を外側の成分として、辞書式積を二度具体化する。関係 `_≺²_` は添字の対を比較する。まず左座標の ≺₁ で比べ、どちらの向きも成り立たないときに右座標の ≺₁ で比べる。この形に対しては prodWF がちょうど整礎性を与える。もう一段重ねた `_≺³_` は f の着地点である級付き三つ組を比較するから、`_≺³_` の下での下降は級、第一座標、第二座標という三段の辞書式下降になる。
<!--/-->

```agda
  _≺²_ = _≺×_ ordSWO _≺₁_ wf₁

  wf² : WellFounded _≺²_
  wf² = prodWF ordSWO _≺₁_ wf₁

  _≺³_ : (⟪ α ⟫ × (⟪ α ⟫ × ⟪ α ⟫)) → (⟪ α ⟫ × (⟪ α ⟫ × ⟪ α ⟫)) → Type (ℓ-suc ℓ)
  _≺³_ = _≺×_ ordSWO _≺²_ wf²
```

<!--en-->
`wf³` is just the second application of `prodWF`, so `_≺³_` is well-founded without further work. The helper `¬<₁` records a small consequence of irreflexivity: if `m` and `n` are equal indices, no step `m ≺₁ n` can exist, since transporting the step backwards along the equality gives `m ≺₁ m`. This is exactly the bookkeeping the product relation needs, because `_≺×_` descends to its second tier only when neither outer direction holds. With that in place, `subrel` is typed to convert every step `p ≺ q` of the pair order into a step `f p ≺³ f q` between the graded triples.
<!--zh-->
wf³ 只是 prodWF 的第二次应用，因此 `_≺³_` 无需进一步工作便是良基的。辅助事实 ¬<₁ 记录了反自反性的一个小推论：若指标 m 与 n 相等，则步骤 `m ≺₁ n` 不可能存在，因为把该步骤沿等式向后搬运就得到 `m ≺₁ m`。这正是乘积关系所需的簿记，因为 `_≺×_` 只有在外层两个方向都不成立时才降到第二层。有了这一点，subrel 的类型便是把序对序的每个步骤 `p ≺ q` 转换成带级三元组之间的步骤 `f p ≺³ f q`。
<!--ja-->
wf³ は prodWF の二度目の適用にすぎず、`_≺³_` は追加の作業なしに整礎である。補助事実 ¬<₁ は反反射性の小さな帰結を記録する。添字 m と n が等しければ、ステップ `m ≺₁ n` は存在しえない。そのステップを等式に沿って後ろへ輸送すれば `m ≺₁ m` が得られるからである。これは積の関係が求めるまさにその準備である。`_≺×_` は外側のどちらの向きも成り立たないときに限って次の段へ降りるからだ。これを踏まえると、subrel は対の順序の各ステップ `p ≺ q` を級付き三つ組の間のステップ `f p ≺³ f q` へ変換するものとして型が与えられている。
<!--/-->

```agda

  wf³ : WellFounded _≺³_
  wf³ = prodWF ordSWO _≺²_ wf²

  ¬<₁ : (m : ⟪ α ⟫) {n : ⟪ α ⟫} → m ≡ n → (m ≺₁ n → Empty.⊥)
  ¬<₁ m {n} q h = irr₁ m (subst (λ w → m ≺₁ w) (sym q) h)

  subrel : {p q : Pair} → p ≺ q → f p ≺³ f q
```

<!--en-->
The first two cases of `subrel` are direct. When the grades are already strictly ordered, the step `inl h` is itself a top-tier step of `_≺³_`, since both relations share the outer component ≺₁. When the grades tie and the first coordinates are strictly ordered, the target relation requires proof that neither grade direction holds before descending a tier; `¬<₁` on each side, applied to the tie path and its symmetry, supplies exactly those two refutations, after which `inl h` places the strict first-coordinate step on the second tier.
<!--zh-->
subrel 的前两种情形是直接的。当级差已经严格有序时，步骤 `inl h` 本身就是 `_≺³_` 的顶层步骤，因为两个关系共用外层分量 ≺₁。当级差相等而第一坐标严格有序时，目标关系要求在降层之前证明级差的两个方向都不成立；对等值路径及其对称各用一次 ¬<₁ 恰好给出这两个反驳，随后 `inl h` 把严格的第一坐标步骤放到第二层。
<!--ja-->
subrel の最初の二つの場合は直接的である。級がすでに真に順序づけられているなら、ステップ `inl h` はそれ自体が `_≺³_` の最上段のステップである。両関係が外側の成分 ≺₁ を共有するからだ。級が一致し第一座標が真に狭い場合、目標の関係は一段降りる前に級のどちらの向きも成り立たないことの証明を要求する。一致の経路とその対称にそれぞれ ¬<₁ を適用すれば、まさにその二つの反駁が得られ、その後に `inl h` が第一座標の狭いステップを第二段に置く。
<!--/-->

```agda
  subrel {a , b} {c , d} (inl h) =
    inl h
  subrel {a , b} {c , d} (inr (e , inl h)) =
    inr (¬<₁ (maxOrd a b) e , ¬<₁ (maxOrd c d) (sym e) , inl h)
  subrel {a , b} {c , d} (inr (e , inr (f , h))) =
```

<!--en-->
The fully tied case nests one level deeper: the grades tie, the first coordinates tie, and the second coordinates are strictly ordered, so `subrel` must refute both grade directions and then both first-coordinate directions before placing `h` on the innermost tier. Well-foundedness of the pair order then follows by pulling accessibility back along `f`: `wf≺ p` starts from accessibility of `f p` in `_≺³_`, which `wf³` provides. The private helper `go` is stated so that the index of the accessibility proof determines the pair it is about, letting the recursion below reenter itself.
<!--zh-->
完全相等的情形更深一层嵌套：级差相等、第一坐标相等、第二坐标严格有序，因此 subrel 必须先反驳级差的两个方向、再反驳第一坐标的两个方向，才能把 h 放到最内层。序对序的良基性随后由沿 f 拉回可达性得到：wf≺ p 从 `f p` 在 `_≺³_` 中的可达性出发，而这正是 wf³ 所提供的。私有辅助函数 go 的陈述方式使得可达性证明的指标就确定了它所关心的序对，从而下方的递归得以重新进入自身。
<!--ja-->
完全に一致する場合はさらに一段深く入れ子になる。級が一致し、第一座標も一致し、第二座標が真に狭い。そこで subrel は、h を最内段に置く前に、級の二つの向きと第一座標の二つの向きを反駁しなければならない。対の順序の整礎性は、f に沿って到達可能性を引き戻すことで従う。wf≺ p は `f p` の `_≺³_` における到達可能性から出発するが、それを wf³ が与える。非公開の補助関数 go は、到達可能性の証明の添字がその証明が対象とする対を定めるように述べられており、下の再帰が自分自身に再び入れるようになっている。
<!--/-->

```agda
    inr (¬<₁ (maxOrd a b) e , ¬<₁ (maxOrd c d) (sym e)
       , inr (¬<₁ a f , ¬<₁ c (sym f) , h))

  wf≺ : WellFounded _≺_
  wf≺ p = go (wf³ (f p))
    where
```

<!--en-->
The computation rule of `go` unpacks the accessibility data: from `acc r`, where `r` maps every `_≺³_`-predecessor of `f q` to accessibility, it produces `acc` on the pair side. Given a predecessor `q'` with `q' ≺ q`, the step is pushed forward through `subrel` to a step `f q' ≺³ f q`, fed to `r`, and `go` is applied again. Hence every descending chain of pairs maps to a descending chain of graded triples, which well-foundedness of `_≺³_` forbids, so the pair order admits no infinite descent.
<!--zh-->
go 的计算规则展开可达性数据：由 `acc r` (其中 r 把 `f q` 的每个 `_≺³_` 前驱映到可达性) 在序对一侧产生 acc。给定带 `q' ≺ q` 的前驱 `q'`，先经 subrel 把该步骤推前为 `f q' ≺³ f q`，交给 r，再对结果应用 go。于是序对的每个递降链都映为带级三元组的递降链，而 `_≺³_` 的良基性禁止后者，故序对序不存在无穷递降。
<!--ja-->
go の計算規則は到達可能性のデータを展開する。`acc r` から出発する。ここで r は `f q` の各 `_≺³_` 前駆を到達可能性へ写す。これにより対の側で acc が作られる。`q' ≺ q` を満たす前駆 `q'` が与えられると、ステップは subrel によって `f q' ≺³ f q` へと押し出され、r に渡され、そこへ再び go が適用される。したがって対の任意の降下列は級付き三つ組の降下列へ写されるが、`_≺³_` の整礎性は後者を禁じるから、対の順序に無限降下はない。
<!--/-->

```agda
    go : {q : Pair} → Acc _≺³_ (f q) → Acc _≺_ q
    go {q} (acc r) = acc (λ q' q'≺q → go (r (f q') (subrel {q'} {q} q'≺q)))

```

<!--en-->
## Moving between finite ordinals and `Fin`

Every member of `ω` is a numeral, but membership in `ω` is a truncated statement and yields only a mere existence of a numeral label. Inside the finite ordinal `# n` the situation is better: the proposition "this index represents `# k` with `k < n`" is an `hProp`, so excluded middle applies and least-element search returns a chosen least label. That label is the conversion `toFin : ⟪ # n ⟫ → Fin n`, and the fiber supplied by `#mono` gives the way back.
<!--zh-->
## 在有穷序数与 `Fin` 之间转换

`ω` 的每个成员都是数码，但 `ω` 的成员资格是截断命题，只能给出数码标号「仅仅存在」。而在有穷序数 `# n` 内部情况更好：命题「该指标表示 `# k` 且 `k < n`」是一个 `hProp`，排中律因此适用，最小元搜索会返回一个被选出的最小标号。这个标号就是转换 `toFin : ⟪ # n ⟫ → Fin n`，而 `#mono` 提供的纤维给出返回之路。
<!--ja-->
## 有限順序数と `Fin` の間を移る

`ω` の各要素は数項ですが、`ω` の要素であることは切り捨てられた命題であり、数項のラベルが「単に存在する」ことしか与えません。有限順序数 `# n` の内部では事情が良くなります。「この添字が `k < n` なる `# k` を表す」という命題は `hProp` なので排中律が適用でき、最小要素の探索は選ばれた最小ラベルを返します。このラベルが変換 `toFin : ⟪ # n ⟫ → Fin n` であり、`#mono` の与える繊維が逆方向の道を与えます。
<!--/-->

<!--en-->
The search proposition `P` packages, for each index `m` of `# n` and each natural number `k`, the conjunction of `k < n` and the assertion that `m` represents the numeral `# k`. Its propositionhood is assembled from two facts: the order `k < n` is a proposition, and the equality of represented elements lives in a set, so its equality type is a proposition as well. Wrapping the conjunction into an `hProp` is what later licenses an application of excluded middle to it.
<!--zh-->
搜索命题 P 对 `# n` 的每个指标 m 和每个自然数 k，打包了 `k < n` 与「m 表示数码 `# k`」这两者的合取。它的命题性由两个事实组装而成：序关系 `k < n` 是命题，而所表示元素之间的等式生活在集合中，其等式类型因此也是命题。把这个合取包成 `hProp`，正是后面得以对它应用排中律的原因。
<!--ja-->
探索の命題 P は、`# n` の各添字 m と各自然数 k に対して、`k < n` と「m が数項 `# k` を表す」という主張の連言をまとめたものです。その命題性は二つの事実から組み立てられます。順序 `k < n` が命題であることと、表された要素の等式が集合の中に住んでおり、その等式型も命題であることです。この連言を `hProp` に包むことが、後で排中律を適用できる根拠になります。
<!--/-->

```agda
module FiniteBase where

  P : (n : ℕ) (m : ⟪ # n ⟫) → ℕ → hProp (ℓ-suc ℓ)
  P n m k = ((k < n) × (⟪ # n ⟫↪ m ≡ # k))
          , isProp× isProp≤ (isSetS (⟪ # n ⟫↪ m) (# k))

  ω-mem→numeral : (β : S) → ⟨ β ∈ˢ ω ⟩ → ∥ Σ[ n ∈ ℕ ] (β ≡ # n) ∥₁
```

<!--en-->
Membership of `β` in `ω` itself only says that β is a numeral in the truncated sense: the specification of `ω` delivers a truncated pair of a lifted natural number and an approximation certificate. The helper `hit` refines this data into a path: the approximation `β ≈ˢ numeralV n` composed with `numeralV≡# n` yields `β ≡ # n`. The result stays inside `∥_∥₁`, so this theorem gives a mere existence of a numeral label and not a chosen one; a witness would require eliminating the truncation into a non-propositional target.
<!--zh-->
β 属于 `ω` 本身只以截断的方式说 β 是一个数码：`ω` 的刻画给出一个提升自然数与近似证书的截断序对。辅助函数 hit 把这份数据精化为一条路径：近似 `β ≈ˢ numeralV n` 与 `numeralV≡# n` 复合得到 `β ≡ # n`。结果保持在 `∥_∥₁` 之内，所以该定理给出数码标号的仅仅存在而非被选出的标号；要得到见证就需要把截断消入非命题性目标。
<!--ja-->
β が `ω` に属することそのものは、β が数項であることを切り捨てられた形でしか言いません。`ω` の仕様は、持ち上げられた自然数と近似の証明書の切り捨てられた対を与えます。補助関数 hit はこのデータを経路へと精製し、近似 `β ≈ˢ numeralV n` と `numeralV≡# n` の合成から `β ≡ # n` を得ます。結果は `∥_∥₁` の中に留まるので、この定理が与えるのは数項ラベルの単なる存在であり、選ばれたラベルではありません。証人を得るには切り捨てを非命題的な対象へ消去する必要があります。
<!--/-->

```agda
  ω-mem→numeral β β∈ω = PT.map hit (subst ⟨_⟩ (ω-specV β) β∈ω)
    where
    hit : Σ[ n ∈ Lift {ℓ-zero} {ℓ-suc ℓ} ℕ ] ⟨ β ≈ˢ numeralV (lower n) ⟩
        → Σ[ n ∈ ℕ ] (β ≡ # n)
    hit (n , p) = lower n , p ∙ numeralV≡# (lower n)
```

<!--en-->
For an index of the finite ordinal `# n` there is a concrete inhabitant to start from: the membership of the represented element in `⟪ # n ⟫` implies, via `∈#-elim`, that some `k < n` satisfies `P`. Feeding this truncated witness to `leastOf natOrder lem` uses excluded middle at the natural-number order to turn mere existence into a chosen least pair `s`. Its first component is the label `k` and the first component of its certificate is the bound `k < n`, which is exactly the data `Fin n` packages.
<!--zh-->
对有穷序数 `# n` 的指标，存在具体的出发点：所表示元素属于 `⟪ # n ⟫` 这一事实经 `∈#-elim` 蕴含某个 `k < n` 满足 P。把这个截断见证交给 `leastOf natOrder lem`，在自然数序上使用排中律，把仅仅存在转化为被选出的最小序对 s。其第一分量是标号 k，其证书的第一分量是界 `k < n`，而这正是 `Fin n` 打包的数据。
<!--ja-->
有限順序数 `# n` の添字には具体的な出発点があります。表された要素が `⟪ # n ⟫` に属するという事実は、`∈#-elim` を通じて、`k < n` なる k が P を満たすことを含意します。この切り捨てられた証人を `leastOf natOrder lem` に渡すと、自然数の順序について排中律を用いて、単なる存在が選ばれた最小の対 s に変わります。その第一成分がラベル k であり、証明書の第一成分が上界 `k < n` で、これこそ `Fin n` がまとめたデータです。
<!--/-->

```agda

  toFin : (n : ℕ) → ⟪ # n ⟫ → FB.Fin n
  toFin n m = k , k<n
    where
    s = leastOf natOrder lem (P n m) (∈#-elim n (⟪ # n ⟫↪ m) (member (# n) m))
    k : ℕ
```

<!--en-->
The specification of `toFin` says more than the type bound: the least label `k` satisfies the full second conjunct of `P`, namely that the index `m` represents `# k`. This is the second component of the certificate returned by the least-element search, and it is the path that the injectivity proof below will consume.
<!--zh-->
toFin 的刻画比类型上的界说得更多：最小标号 k 满足 P 的完整的第二个合取支，即指标 m 表示 `# k`。这是最小元搜索返回证书的第二个分量，也是下面单射性证明要消费的那条路径。
<!--ja-->
toFin の仕様は型の上界よりも多くを言います。最小ラベル k は P の第二の連言支、すなわち添字 m が `# k` を表すという部分を満たすのです。これは最小要素の探索が返す証明書の第二成分であり、下の単射性の証明が消費する経路そのものです。
<!--/-->

```agda
    k = fst s
    k<n : k < n
    k<n = fst (fst (snd s))

  toFin-spec : (n : ℕ) (m : ⟪ # n ⟫) → ⟪ # n ⟫↪ m ≡ # (fst (toFin n m))
  toFin-spec n m = snd (fst (snd s))
```

<!--en-->
Injectivity of `toFin` follows by transporting the two specification paths along the assumed equality of labels. If `toFin n m₁` and `toFin n m₂` agree, their first components agree, so `# (fst (toFin n m₁))` and `# (fst (toFin n m₂))` are connected by a path; concatenating with the two specifications gives a path between the represented elements, and `↪-inj` reflects equality of represented elements back to equality of indices, as it did for the ordinal order.
<!--zh-->
toFin 的单射性沿标号相等的假设搬运两条刻画路径而得。若 `toFin n m₁` 与 `toFin n m₂` 相等，则其第一分量相等，于是 `# (fst (toFin n m₁))` 与 `# (fst (toFin n m₂))` 之间有路径；与两条刻画拼接便得到所表示元素之间的路径，而 `↪-inj` 把所表示元素的相等反射回指标的相等，正如序数序处那样。
<!--ja-->
toFin の単射性は、ラベルの一致という仮定に沿って二つの仕様の経路を輸送することで従います。`toFin n m₁` と `toFin n m₂` が一致すればその第一成分は一致し、したがって `# (fst (toFin n m₁))` と `# (fst (toFin n m₂))` の間に経路があります。二つの仕様と連結すれば表された要素の間の経路が得られ、`↪-inj` が順序数の順序のときと同様に、表された要素の一致を添字の一致へと反映します。
<!--/-->

```agda
    where
    s = leastOf natOrder lem (P n m) (∈#-elim n (⟪ # n ⟫↪ m) (member (# n) m))

  toFin-inj : (n : ℕ) (m₁ m₂ : ⟪ # n ⟫) → toFin n m₁ ≡ toFin n m₂ → m₁ ≡ m₂
  toFin-inj n m₁ m₂ e = ↪-inj {a = # n}
    (toFin-spec n m₁ ∙ cong (λ k → # k) (cong fst e) ∙ sym (toFin-spec n m₂))
```

<!--en-->
The reverse direction starts from `#mono`, which witnesses that `# k` is a member of `# n` whenever `k < n`. Since the index type `⟪ # n ⟫` presents the members of `# n`, that membership comes with a fiber: an index whose represented element is `# k`, together with a certificate of exactly the shape that `fromFin-spec` records. So `fromFin n (k , k<n)` is the first component of this fiber, chosen by the presentation rather than by least search.
<!--zh-->
反方向从 `#mono` 出发：只要 `k < n`，它就见证 `# k` 是 `# n` 的成员。由于指标类型 `⟪ # n ⟫` 呈现 `# n` 的成员，这个成员资格附带一个纤维：一个所表示元素为 `# k` 的指标，连同恰为 fromFin-spec 所记录形状的证书。于是 `fromFin n (k , k<n)` 就是这个纤维的第一分量，由呈现方式选定，而非由最小元搜索选定。
<!--ja-->
逆方向は `#mono` から始まります。`k < n` ならば `# k` が `# n` の要素であることを `#mono` が証明します。添字型 `⟪ # n ⟫` は `# n` の要素を提示するので、この所属には繊維が付随します。すなわち、表された要素が `# k` である添字と、fromFin-spec が記録するのとまったく同じ形の証明書です。したがって `fromFin n (k , k<n)` はこの繊維の第一成分であり、最小探索ではなく提示の仕方によって選ばれます。
<!--/-->

```agda

  fromFin : (n : ℕ) → FB.Fin n → ⟪ # n ⟫
  fromFin n (k , k<n) = fiber (# n) (#mono k n k<n) .fst

  fromFin-spec : (n : ℕ) (i : FB.Fin n) → ⟪ # n ⟫↪ (fromFin n i) ≡ # (fst i)
  fromFin-spec n (k , k<n) = fiber (# n) (#mono k n k<n) .snd

  fromFin-inj : (n : ℕ) (i₁ i₂ : FB.Fin n) → fromFin n i₁ ≡ fromFin n i₂ → i₁ ≡ i₂
```

<!--en-->
Injectivity of `fromFin` uses that `Fin n` is a subtype: its second components are bounded naturals, a proposition-valued family, so an equality of pairs reduces to an equality of first components. The path between represented elements obtained from the two specifications and `e` is converted by `#-inj′` into a path of natural numbers, and `Σ≡Prop` lifts that to a path in `Fin n`. The section then introduces `factor`, defined as the forward direction of the standard equivalence `factorEquiv : Fin n × Fin n ≃ Fin (n · n)`, which enumerates pairs of positions by a single position.
<!--zh-->
fromFin 的单射性利用了 `Fin n` 是子类型这一事实：其第二分量是有界自然数，一个取命题值的族，于是序对的相等可归约为第一分量的相等。由两条刻画与 e 得到的所表示元素之间的路径经 `#-inj′` 转换为自然数之间的路径，`Σ≡Prop` 再把它提升为 `Fin n` 中的路径。本节随后引入 factor，定义为标准等价 `factorEquiv : Fin n × Fin n ≃ Fin (n · n)` 的正向部分，它用单个位置枚举位置对。
<!--ja-->
fromFin の単射性は、`Fin n` が部分型であることを用います。その第二成分は有界な自然数、つまり命題値の族なので、対の一致は第一成分の一致に帰着します。二つの仕様と e から得た、表された要素の間の経路は `#-inj′` によって自然数の間の経路に変換され、`Σ≡Prop` がそれを `Fin n` の経路へ持ち上げます。続いてこの節は factor を導入します。これは標準的な同値 `factorEquiv : Fin n × Fin n ≃ Fin (n · n)` の順方向であり、位置の対を一つの位置で数え上げます。
<!--/-->

```agda
  fromFin-inj n i₁ i₂ e = Σ≡Prop (λ _ → isProp≤)
    (#-inj′ (sym (fromFin-spec n i₁) ∙ cong (⟪ # n ⟫↪) e ∙ fromFin-spec n i₂))

  factor : (n : ℕ) → FB.Fin n × FB.Fin n → FB.Fin (n · n)
  factor n = equivFun (factorEquiv {n = n} {m = n})

  factor-inj : (n : ℕ) (x y : FB.Fin n × FB.Fin n)
```

<!--en-->
Because `factor` is an equivalence and not merely a function, its injectivity needs no new case analysis: if `factor n x` and `factor n y` agree, applying the inverse and using the round-trip law `retEq` on each side returns `x` and `y` themselves. The proof is the concatenation of `sym (retEq ...) x`, the transported equality, and `retEq ... y`. This is the pattern noted earlier: a map shaped like an inverse is not an inverse until the inverse laws are supplied, and here the library's equivalence supplies them.
<!--zh-->
由于 factor 是等价而不只是函数，其单射性无需新的情形分析：若 `factor n x` 与 `factor n y` 相等，对两侧应用逆映射并使用往返定律 retEq，便回到 x 与 y 自身。证明就是 `sym (retEq ...) x`、被搬运的等式与 `retEq ... y` 的拼接。这正是前面指出的模式：形如逆映射的映射在逆定律补齐之前还不是逆映射，而这里由库中的等价提供了逆定律。
<!--ja-->
factor は単なる関数ではなく同値であるため、その単射性に新しい場合分けは不要です。`factor n x` と `factor n y` が一致すれば、両側に逆写像を適用し往復則 retEq を使えば、x と y そのものに戻ります。証明は `sym (retEq ...) x`、輸送された等式、`retEq ... y` の連結です。これは先に指摘したパターン、つまり逆の形をした写像は逆法則が供給されるまでは逆ではない、ということの実例で、ここではライブラリの同値が逆法則を供給します。
<!--/-->

```agda
             → factor n x ≡ factor n y → x ≡ y
  factor-inj n x y e =
    sym (retEq (factorEquiv {n = n} {m = n}) x)
      ∙ cong (invEq (factorEquiv {n = n} {m = n})) e
      ∙ retEq (factorEquiv {n = n} {m = n}) y
```

<!--en-->
The pigeonhole statement is the finite core of the later contradiction: no function `Fin (suc n) → Fin n` can be injective. The library result `pigeonhole`, applied with the reflexivity witness `≤-refl {m = suc n}`, produces two positions `i` and `j` together with a certificate that they are distinct yet `f i ≡ f j`; composing the injectivity hypothesis with that equality yields an element of the empty type.
<!--zh-->
鸽笼命题是后面矛盾的有限内核：不存在单射的函数 `Fin (suc n) → Fin n`。库中的结果 pigeonhole 以自反性见证 `≤-refl {m = suc n}` 应用于 f，产出两个位置 i 与 j，连同「它们不同而 `f i ≡ f j`」的证书；把单射性假设与该等式复合，便得到空类型的元素。
<!--ja-->
鳩の巣の命題は、後の矛盾の有限の中核です。関数 `Fin (suc n) → Fin n` は単射になりえません。ライブラリの結果 pigeonhole を反射性の証明 `≤-refl {m = suc n}` とともに f に適用すると、相異なるのに `f i ≡ f j` を満たす二つの位置 i と j とその証明書が得られ、単射性の仮定をその等式と合成すれば空の型の要素が得られます。
<!--/-->

```agda

  no-inj-Fin : (n : ℕ) → (f : FB.Fin (suc n) → FB.Fin n)
             → ((x y : FB.Fin (suc n)) → f x ≡ f y → x ≡ y) → Empty.⊥
  no-inj-Fin n f finj = i#j (finj i j feq)
    where
    i = fst (pigeonhole (≤-refl {m = suc n}) f)
```

<!--en-->
The unpacking separates the pigeonhole certificate into the parts the final line needs: `i` and `j` are the two colliding positions, `i#j` is their distinctness, and `feq` is the equality of their images. The computation `i#j (finj i j feq)` then applies the injectivity hypothesis to obtain `i ≡ j` and feeds it to the distinctness, producing the contradiction.
<!--zh-->
这里的拆解把鸽笼证书分成末行所需的各部分：i 与 j 是两个碰撞位置，i#j 是它们的相异性，feq 是其像的等式。于是计算 `i#j (finj i j feq)` 把单射性假设应用于得到 `i ≡ j`，再交给相异性，产生矛盾。
<!--ja-->
この展開は、鳩の巣の証明書を最終行で必要な部分に分けます。i と j は衝突する二つの位置、i#j はその相異性、feq は像の一致です。計算 `i#j (finj i j feq)` は単射性の仮定から `i ≡ j` を得て、それを相異性に渡して矛盾を生み出します。
<!--/-->

```agda
    j = fst (snd (pigeonhole (≤-refl {m = suc n}) f))
    prf = snd (snd (pigeonhole (≤-refl {m = suc n}) f))
    i#j = fst prf
    feq : f i ≡ f j
    feq = snd prf
```

<!--en-->
The final block abstracts away from omega. It is parameterized by a family `E : ℕ → Type ℓ` together with an injective encoder `toFinE : E n → Fin n` and an injective decoder `fromFinE : Fin n → E n`. Note what is and is not assumed: each direction comes with its own injectivity proof, but the two are not required to be mutually inverse, and no equivalence between `E n` and `Fin n` is claimed. Only the two injectivities enter the argument.
<!--zh-->
最后的模块从 ω 中抽象出来。它由族 `E : ℕ → Type ℓ` 参数化，并带有单射的编码器 `toFinE : E n → Fin n` 与单射的解码器 `fromFinE : Fin n → E n`。注意假设了什么、没有假设什么：每个方向各自带有自己的单射性证明，但不要求两者互逆，也不声称 `E n` 与 `Fin n` 之间存在等价。进入论证的只有这两个单射性。
<!--ja-->
最後のブロックは ω から抽象化します。これは族 `E : ℕ → Type ℓ` でパラメータ化され、単射な符号器 `toFinE : E n → Fin n` と単射な復号器 `fromFinE : Fin n → E n` を伴います。何が仮定され、何が仮定されないかに注意してください。各方向はそれぞれ自身の単射性の証明を伴いますが、両者が互いに逆であることは要求されず、`E n` と `Fin n` の間の同値も主張されません。議論に入るのはこの二つの単射性だけです。
<!--/-->

```agda

  module AbstractChase (E : ℕ → Type ℓ)
                       (toFinE : (n : ℕ) → E n → FB.Fin n)
                       (toFinE-inj : (n : ℕ) (m₁ m₂ : E n) → toFinE n m₁ ≡ toFinE n m₂ → m₁ ≡ m₂)
                       (fromFinE : (n : ℕ) → FB.Fin n → E n)
                       (fromFinE-inj : (n : ℕ) (i₁ i₂ : FB.Fin n) → fromFinE n i₁ ≡ fromFinE n i₂ → i₁ ≡ i₂) where
```

<!--en-->
Inside this setup, the inner module `NoInj` fixes a type `A` that receives an injection `into m` from every `E m`, itself injective at each level. Its theorem `no-inj` says that no injection `A → E n × E n` can exist for any `n`: the reduction is immediate, because the displayed proof simply hands the constructed finite function `g` to `no-inj-Fin (n · n)` together with its injectivity. All the work lies in defining `g` and proving `g-inj`.
<!--zh-->
在此设定内，内层模块 NoInj 固定一个类型 A，它从每个 `E m` 接收单射 `into m`，且该单射在每个层级上都是单的。其定理 no-inj 说：对任意 n，不存在单射 `A → E n × E n`。归约是直接的，因为所展示的证明只是把构造出的有限函数 g 连同其单射性交给 `no-inj-Fin (n · n)`。全部工作在于定义 g 并证明 g-inj。
<!--ja-->
この設定のもとで、内側のモジュール NoInj は型 A を固定します。A はすべての `E m` から単射 `into m` を受け入れ、その単射は各レベルで単射です。その定理 no-inj は、任意の n に対して単射 `A → E n × E n` は存在しないと言います。帰結は直接的で、示された証明は構成した有限関数 g とその単射性を `no-inj-Fin (n · n)` に渡すだけだからです。すべての仕事は g の定義と g-inj の証明にあります。
<!--/-->

```agda

    module NoInj (A : Type ℓ) (into : (m : ℕ) → E m → A)
                 (into-inj : (m : ℕ) (i₁ i₂ : E m) → into m i₁ ≡ into m i₂ → i₁ ≡ i₂) where

      no-inj : (n : ℕ) → (f : A → E n × E n)
             → ((x y : A) → f x ≡ f y → x ≡ y) → Empty.⊥
      no-inj n f finj = no-inj-Fin (n · n) g g-inj
```

<!--en-->
The map `g` is the forbidden injection `Fin (suc (n · n)) → Fin (n · n)`, built as a composition. Starting from a position `i` of a set one larger than `n · n`, the decoder `fromFinE` produces an element of `E (suc (n · n))`, the injection `into` lifts it into `A`, the assumed map `f` sends it to a pair of elements of `E n`, and the encoder `toFinE` turns each component into a position of `Fin n`. The pair of positions is finally compressed by `factor` into a single position of `Fin (n · n)`.
<!--zh-->
映射 g 就是被禁止的单射 `Fin (suc (n · n)) → Fin (n · n)`，由复合构造而成。从比 `n · n` 大一的位置 i 出发，解码器 fromFinE 产生 `E (suc (n · n))` 的元素，单射 into 把它送入 A，假设的映射 f 把它送到 `E n` 的一对元素，编码器 toFinE 再把每个分量变成 `Fin n` 中的位置。最后由 factor 把这对位置压缩为 `Fin (n · n)` 中的单个位置。
<!--ja-->
写像 g は、禁じられている単射 `Fin (suc (n · n)) → Fin (n · n)` であり、合成として構成されます。`n · n` より 1 大きい集合の位置 i から出発し、復号器 fromFinE が `E (suc (n · n))` の要素を作り、単射 into がそれを A へ持ち上げ、仮定された写像 f がそれを `E n` の要素の対へ送り、符号器 toFinE が各成分を `Fin n` の位置へ変えます。最後に factor がこの位置の対を `Fin (n · n)` の一つの位置へ圧縮します。
<!--/-->

```agda
        where
        g : FB.Fin (suc (n · n)) → FB.Fin (n · n)
        g i = factor n ( toFinE n (fst (f (into (suc (n · n)) (fromFinE (suc (n · n)) i))))
                       , toFinE n (snd (f (into (suc (n · n)) (fromFinE (suc (n · n)) i)))))
        g-inj : (x y : FB.Fin (suc (n · n))) → g x ≡ g y → x ≡ y
```

<!--en-->
Injectivity of `g` propagates the contradiction backwards through each layer of its construction. Assume `g x ≡ g y`. Since `factor` is injective, the pair of encoded positions is equal; since `toFinE` is injective, the two components of the pair are equal as elements of `E n`; since `f` is injective, the two elements of `A` are equal; since `into` is injective, the two elements of `E (suc (n · n))` are equal; and since `fromFinE` is injective, `x ≡ y`. The displayed term reads inside out exactly along this chain.
<!--zh-->
g 的单射性把矛盾沿其构造的每一层向后传播。设 `g x ≡ g y`。由于 factor 是单射，编码位置的序对相等；由于 toFinE 是单射，该序对的两个分量作为 `E n` 的元素相等；由于 f 是单射，A 中的两个元素相等；由于 into 是单射，`E (suc (n · n))` 中的两个元素相等；最后由于 fromFinE 是单射，得到 `x ≡ y`。所展示的项恰好沿这条链从内向外读。
<!--ja-->
g の単射性は、矛盾をその構成の各層を通って後ろへ伝播させます。`g x ≡ g y` と仮定します。factor が単射なので、符号化された位置の対は一致し、toFinE が単射なのでその対の二つの成分は `E n` の要素として一致し、f が単射なので A の二つの要素は一致し、into が単射なので `E (suc (n · n))` の二つの要素は一致し、最後に fromFinE が単射なので `x ≡ y` が得られます。示された項はまさにこの連鎖に沿って内側から外側へ読めます。
<!--/-->

```agda
        g-inj x y e = fromFinE-inj (suc (n · n)) x y
          (into-inj (suc (n · n))
            (fromFinE (suc (n · n)) x) (fromFinE (suc (n · n)) y)
            (finj Xx Xy pair-eq))
          where
```

<!--en-->
The `where` block names the intermediate values to keep the chain readable. `Xx` and `Xy` are the two elements of `A` obtained by decoding the positions `x` and `y` and then injecting them; they are the inputs whose images under `f` must be shown equal. The statement `p-eq` records the intermediate goal: the pairs of encoded positions agree.
<!--zh-->
where 块为中间值命名以保持链条可读。Xx 与 Xy 是把位置 x 与 y 解码再注入而得的 A 的两个元素；它们正是需要证明其 f 之下像相等的输入。命题 p-eq 记录了中间目标：两组编码位置一致。
<!--ja-->
where ブロックは中間値に名前を付け、連鎖を読みやすくします。Xx と Xy は、位置 x と y を復号してから注入して得られる A の二つの要素であり、f による像の一致を示すべき入力そのものです。命題 p-eq は中間目標、すなわち符号化された位置の対が一致することを記録します。
<!--/-->

```agda
          Xx : A
          Xx = into (suc (n · n)) (fromFinE (suc (n · n)) x)
          Xy : A
          Xy = into (suc (n · n)) (fromFinE (suc (n · n)) y)
          p-eq : (toFinE n (fst (f Xx)) , toFinE n (snd (f Xx)))
```

<!--en-->
The intermediate goal `p-eq` is exactly what the injectivity of `factor` delivers: applying `factor-inj` to the assumed equality `e` between the compressed positions converts it back to an equality of the pairs of positions in `Fin n`, here the pairs of `toFinE`-images of the two components of `f Xx` and `f Xy`.
<!--zh-->
中间目标 p-eq 恰好由 factor 的单射性给出：对压缩位置之间的假设等式 e 应用 factor-inj，便把它转换回 `Fin n` 中位置对的相等，这里是 `f Xx` 与 `f Xy` 的两个分量的 toFinE 像所成的位置对。
<!--ja-->
中間目標 p-eq はまさに factor の単射性が与えるものです。圧縮された位置の間の仮定の等式 e に factor-inj を適用すれば、それを `Fin n` の位置の対の一致へと戻せます。ここでの対は、`f Xx` と `f Xy` の二つの成分の toFinE 像からなる対です。
<!--/-->

```agda
               ≡ (toFinE n (fst (f Xy)) , toFinE n (snd (f Xy)))
          p-eq = factor-inj n
                   (toFinE n (fst (f Xx)) , toFinE n (snd (f Xx)))
                   (toFinE n (fst (f Xy)) , toFinE n (snd (f Xy))) e
          fst-eq : toFinE n (fst (f Xx)) ≡ toFinE n (fst (f Xy))
```

<!--en-->
Projecting the pair equality with `cong fst` and `cong snd` splits it into equalities of the first and second encoded positions. Each is then converted back into an equality of the corresponding components of `f Xx` and `f Xy` by the encoder's injectivity `toFinE-inj`, giving `fst-eq′` and, one line later, its second-coordinate counterpart.
<!--zh-->
用 `cong fst` 与 `cong snd` 投影序对的相等，把它拆成第一与第二编码位置各自的相等。随后由编码器的单射性 toFinE-inj 把每一个转换回 `f Xx` 与 `f Xy` 相应分量的相等，得到 fst-eq′，以及一行之后的第二坐标对应版本。
<!--ja-->
対の一致を `cong fst` と `cong snd` で射影すると、第一と第二の符号化位置のそれぞれの一致に分解されます。その後、符号器の単射性 toFinE-inj によって、それぞれが `f Xx` と `f Xy` の対応する成分の一致へと変換され、fst-eq′ が、そして一行後に第二座標の対応物が得られます。
<!--/-->

```agda
          fst-eq = cong fst p-eq
          snd-eq : toFinE n (snd (f Xx)) ≡ toFinE n (snd (f Xy))
          snd-eq = cong snd p-eq
          fst-eq′ : fst (f Xx) ≡ fst (f Xy)
          fst-eq′ = toFinE-inj n (fst (f Xx)) (fst (f Xy)) fst-eq
```

<!--en-->
The two component equalities are reassembled into an equality of pairs by `ΣPathP`, which packages a path of first components and a path of second components into a path between dependent pairs. This `pair-eq` is precisely what the outermost injectivity hypothesis `finj` consumes, completing the backward chain begun at `g-inj`.
<!--zh-->
两条分量相等由 ΣPathP 重新组装为序对的相等：它把第一分量的路径与第二分量的路径打包成依赖序对之间的路径。这个 pair-eq 恰好是最外层的单射性假设 finj 所消费的，从而完成了从 g-inj 开始的向后链条。
<!--ja-->
二つの成分の一致は ΣPathP によって対の一致へと再構成されます。これは第一成分の経路と第二成分の経路を依存対の間の経路へとまとめるものです。この pair-eq こそ、最も外側の単射性の仮定 finj が消費するものであり、g-inj から始まった後ろ向きの連鎖を完了します。
<!--/-->

```agda
          snd-eq′ : snd (f Xx) ≡ snd (f Xy)
          snd-eq′ = toFinE-inj n (snd (f Xx)) (snd (f Xy)) snd-eq
          pair-eq : f Xx ≡ f Xy
          pair-eq = ΣPathP (fst-eq′ , snd-eq′)
```

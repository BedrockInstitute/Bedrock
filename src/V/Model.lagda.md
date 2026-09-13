<!--en-->
# The cumulative hierarchy models ZF and ZFC

This chapter realizes each axiom of ZF inside the cumulative hierarchy at one fixed universe level `ℓ`. For each axiom asserting the existence of a set, the task is to exhibit that set together with a proof that its membership relation is, as a path of truth values, exactly the required description. The assumptions involved are worth separating at the outset. The stock constructions, namely the empty set, pairing, and union, cost nothing beyond the hierarchy's own set former, and the same is true of replacement, which is read directly off the membership rule of that former. Full separation needs propositional resizing, so that each satisfaction proposition gets a representative one universe down. Power set needs a small classifier for propositions, `HPropSmallness`{.Agda}. Resizing and the classifier are packaged together as `Impredicativity`{.Agda}, and the assembled ZF theorem `V⊨ZF`{.Agda} assumes exactly `LEM (ℓ-suc ℓ)`{.Agda}, from which the package follows. For its ZFC part, the theorem `V⊨ZFC`{.Agda} separately assumes set-level choice at `ℓ-suc ℓ`{.Agda}; by Diaconescu's theorem it implies the excluded middle used for the ZF part, and, lowered one universe, it supplies the choice-set axiom. The chapter builds up to these two theorems by converting, one axiom at a time, the constructions the hierarchy already provides into the exact shape the axioms demand.
<!--zh-->
# 累积层级是 ZF 与 ZFC 的模型

本章在固定的一个宇宙层级 `ℓ` 上，于累积层级内部逐条实现 ZF 的公理。对于要求集合存在的公理，任务是构造这样的集合，并证明其成员关系作为真值的路径恰是该公理所要求的描述。所涉假设值得先分开陈述。层级中已有的构造，即空集、配对与并，只花层级自身集合构造子的代价；替换同样如此，它直接从该构造子的成员规则读出。全分离需要命题降层，使每个满足命题获得低一层宇宙的代表。幂集需要一个命题的小分类器，即 `HPropSmallness`{.Agda}。降层与分类器打包为 `Impredicativity`{.Agda}，装配出的 ZF 定理 `V⊨ZF`{.Agda} 恰假设 `LEM (ℓ-suc ℓ)`{.Agda}，打包由它导出。ZFC 部分另以 `ℓ-suc ℓ`{.Agda} 层的集合层选择为假设；由 Diaconescu 定理，它蕴含 ZF 部分所用的排中律，而降低一层宇宙后又供给选择集公理。本章的工作就是把层级已有的构造逐一转换成公理所要求的精确形状，直至得出这两个定理。
<!--ja-->
# 累積階層は ZF と ZFC のモデル

本章は、固定した一つの宇宙レベル `ℓ` の上で、累積階層の内側に ZF の各公理を実現します。集合の存在を要求する各公理については、その集合を構成し、所属関係が真理値のパスとして要求された記述にちょうど等しいことを証明します。関係する仮定は初めに区別しておく価値があります。基本的な構成、すなわち空集合、対、和集合は、階層自身の集合構成子の代償しか要らず、置換も同様で、その構成子の所属規則から直接読み取れます。完全な分出には命題リサイズが必要で、各充足命題に一段低い宇宙の代表を与えます。冪集合には命題の小分類子 `HPropSmallness`{.Agda} が必要です。リサイズと分類子は `Impredicativity`{.Agda} としてひとまとめにされ、組み立てられた ZF の定理 `V⊨ZF`{.Agda} はちょうど `LEM (ℓ-suc ℓ)`{.Agda} を仮定し、パッキングはそこから従います。ZFC の部分では、定理 `V⊨ZFC`{.Agda} がレベル `ℓ-suc ℓ`{.Agda} の集合レベルの選択を別に仮定します。ディアコネスクの定理により、これは ZF の部分に使う排中律を含意し、一段下げれば選択集合の公理を供給します。本章は、階層がすでに持つ構成を公理の要求する正確な形へ一公理ずつ変換し、この二つの定理へ至ります。
<!--/-->

<!--en-->
The universe accounting is exact and should be read once. The carrier of the model is the hierarchy `S` at level `ℓ`, itself an inhabitant of `Type (ℓ-suc ℓ)`. The truth values serving as the model's equality and membership live in `hProp (ℓ-suc ℓ)`. The package `Impredicativity ℓ` couples the two smallness principles used below: `resizing` at that truth level, and the small classifier `HPropSmallness ℓ`, a small type equivalent to all of `hProp ℓ`. The choice lemma consumes set-level choice at level `ℓ`, and the final corollaries assume `LEM (ℓ-suc ℓ)` and `SetChoice (ℓ-suc ℓ)` respectively. So no single uniform level governs every assumption; each principle is taken exactly where its statement makes sense.
<!--zh-->
宇宙层级的账目是精确的，值得读一遍。模型的载体是层级 `ℓ` 上的 `S`，它本身居于 `Type (ℓ-suc ℓ)`。充当模型等词与成员关系的真值住在 `hProp (ℓ-suc ℓ)`。打包 `Impredicativity ℓ` 联结下文用到的两个小性原理：该真值层上的 `resizing`，以及小分类器 `HPropSmallness ℓ`，即与整个 `hProp ℓ` 等价的一个小类型。选择引理消耗层级 `ℓ` 上的集合层选择，而最终两条推论分别假设 `LEM (ℓ-suc ℓ)` 与 `SetChoice (ℓ-suc ℓ)`。因此没有哪一层统一层级支配所有假设；每条原理都恰在其陈述有意义之处取用。
<!--ja-->
宇宙レベルの計算は正確で、一度読んでおくべきものです。モデルの台はレベル `ℓ` の階層 `S` であり、それ自身 `Type (ℓ-suc ℓ)` の要素です。モデルの等号と所属を担う真理値は `hProp (ℓ-suc ℓ)` に住みます。パッキング `Impredicativity ℓ` は、以下で使う二つの小ささの原理、すなわちこの真理値レベルでの `resizing` と、`hProp ℓ` 全体と同値な小さな型である小分類子 `HPropSmallness ℓ` を結び付けます。選択の補題はレベル `ℓ` の集合レベルの選択を消費し、最後の二つの帰結はそれぞれ `LEM (ℓ-suc ℓ)` と `SetChoice (ℓ-suc ℓ)` を仮定します。したがってすべての仮定を支配する単一の一律のレベルはなく、各原理はその主張が意味を持つちょうどその場所で取られます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module V.Model {ℓ : Level} where

open import Base.Impredicativity using ( HPropSmallness; Impredicativity )
```

<!--en-->
Formally, what does it mean for the hierarchy to satisfy an axiom? The first-order logic chapters supply the vocabulary. A structure is a carrier that is an h-set, whose equality and membership take truth values, not booleans of a fixed two-element type. A formula is an element of the object language's syntax, and the axiom schemas quantify over its free-variable slots. Satisfaction is a relation that reads a formula at an environment of carrier elements and returns a truth value. The ZF axioms are re-derived one by one in exactly these terms below.
<!--zh-->
「层级满足一条公理」在形式上是什么意思？一阶逻辑诸章供给了术语。一个结构是作为 h-集合的载体，其等词与成员关系取真值，而非某个固定二元类型中的布尔值。公式是对象语言语法的元素，公理模式对它的自由变元槽量化。满足关系在载体元素的环境下读出公式，返回一个真值。下面将逐一按这些术语重新导出 ZF 的公理。
<!--ja-->
「階層が公理を満たす」とは形式的にはどういう意味でしょうか。一階論理の諸章が語彙を供給します。構造とは h-集合である台のことであり、その等号と所属は、固定された二元型のブール値ではなく真理値を取ります。論理式は対象言語の構文の要素であり、公理のスキーマはその自由変数の枠を量化します。充足は、台の要素からなる環境のもとで論理式を読み、真理値を返す関係です。以下では ZF の公理を、まさにこの言葉で一つずつ導き直します。
<!--/-->

```agda
open import Base.Classical using ( LEM; lem→impredicativity )
open import Base.Choice using ( SetChoice; choice→lem; lowerSetChoice )
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using ( Formula )
import FOL.Semantics
```

<!--en-->
The hierarchy contributes the structure `𝒮ᵥ`{.Agda}: its equality is the path type of the higher inductive type `V ℓ`{.Agda}, and its membership is the hierarchy's native `∈`. Extensionality and regularity for this structure were proved in the chapter on the hierarchy itself and are quoted here rather than reproved. One further tool is carried over from the smallness chapter: the adapter that builds a set from a predicate each of whose values is small. It becomes full separation as soon as resizing supplies the smallness. Throughout, a bi-implication of propositions is converted into the path between their truth values by the standard rewriting `⇔toPath`{.Agda}; almost every specification below ends with that step.
<!--zh-->
层级给出结构 `𝒮ᵥ`{.Agda}：其等词是高阶归纳类型 `V ℓ`{.Agda} 的路径类型，其成员关系是层级原生的 `∈`。该结构的外延性与正则性已在层级一章证明，此处引用而非重证。另有一个从小性一章带来的工具：从「每个取值都小」的谓词构造集合的适配器；一旦降层供给小性，它就成为全分离。全文中，命题之间的双向蕴含经标准改写 `⇔toPath`{.Agda} 变成真值之间的路径；下文几乎每条规格都以这一步收尾。
<!--ja-->
階層が提供するのは構造 `𝒮ᵥ`{.Agda} です。その等号は高次帰納型 `V ℓ`{.Agda} のパス型であり、所属は階層本来の `∈` です。この構造の外延性と正則性は階層そのものの章で証明済みで、ここでは再証明せずに引用します。さらに小ささの章から一つの道具を持ち越します。各値が小さい述語から集合を作る適合装置で、リサイズが小ささを供給しだい完全な分出になります。全体を通じて、命題の間の双条件は標準の書き換え `⇔toPath`{.Agda} で真理値の間のパスに変えられます。以下の仕様のほとんどすべてがこの一手で終わります。
<!--/-->

```agda
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; regularityV )
open import V.Smallness {ℓ} using ( separateFromSmall )

open import Cubical.Foundations.Equiv using ( equivFun; invEq; secEq )
open import Cubical.Functions.Logic using ( ⇔toPath )
```

<!--en-->
Three general cubical facts shape the proofs to come. An embedding into a type whose equality types are propositions is injective, which matters whenever a recovered index must be shown to be the only possible one. A path between dependent pairs whose second components are propositions is fixed by the paths between first projections. And membership statements about image sets are typically truncated existentials: they are introduced by `∣_∣₁`{.Agda} and eliminated with `PT.rec`{.Agda} into proposition-valued targets, while contradictions are handled by the empty type.
<!--zh-->
三条 cubical 一般事实塑造了后面的证明。到相等类型为命题的类型的嵌入是单射，当需要说明回收到的索引是唯一可能时这一点就要用上。第二分量为命题的依值对之间的路径由第一投影之间的路径决定。此外，像集的成员陈述通常是截断的存在式：用 `∣_∣₁`{.Agda} 引入，用 `PT.rec`{.Agda} 消入取命题值的目标；矛盾则交给空类型处理。
<!--ja-->
cubical の三つの一般的な事実が後の証明を形作ります。等号の型が命題である型への埋め込みは単射であり、復元した添字が唯一の可能性であることを示す場面で効きます。第二成分が命題である依存対の間のパスは、第一射影の間のパスで決まります。さらに、像の集合への所属の主張はたいてい切り詰められた存在の形をしており、`∣_∣₁`{.Agda} で導入し、`PT.rec`{.Agda} で命題値の目標へ消去します。矛盾は空の型で扱います。
<!--/-->

```agda
open import Cubical.Functions.Embedding
  using ( Embedding-into-isSet→isSet; isEmbedding→Inj )
open import Cubical.Data.Sigma using ( Σ≡Prop )
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
```

<!--en-->
The central construction is the set former `sett`{.Agda}: from a small index type `X` and a family `X → S` it forms the image set, and `y ∈ sett X ix` holds exactly when some index presents `y`, merely. Replacement is read directly off this membership rule. That the hierarchy is an h-set, recorded by `setIsSet`{.Agda}, is what makes the path type `x ≡ y` a proposition and hence a legitimate truth value for the structure's equality.
<!--zh-->
核心构造是集合构造子 `sett`{.Agda}：从小索引类型 `X` 与族 `X → S` 造出像集，而 `y ∈ sett X ix` 恰在纯粹地存在某个索引呈现 `y` 时成立。替换直接从这条成员规则读出。层级是 h-集合这一点 (由 `setIsSet`{.Agda} 记录) 使路径类型 `x ≡ y` 成为命题，从而成为结构等词的合法真值。
<!--ja-->
中心となる構成は集合の構成子 `sett`{.Agda} です。小さな添字の型 `X` と族 `X → S` から像の集合を作り、所属 `y ∈ sett X ix` は、ある添字が `y` を呈示することが純粋に存在するとき、そのときに限り成ります。置換はこの所属の規則から直接読み取ります。階層が h-集合であること (`setIsSet`{.Agda} が記録します) により、パス型 `x ≡ y` は命題となり、構造の等号の正当な真理値になります。
<!--/-->

```agda
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base
  using ( sett; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
```

<!--en-->
Membership comes in two shapes, and the whole chapter moves between them. Every set `a` has a small type of indices `⟪ a ⟫`{.Agda} with an embedding `⟪ a ⟫↪`{.Agda} whose image is `a`; the small membership `x ∈ₛ a` says that some index presents `x`. The equivalence `∈∈ₛ` converts between small and ordinary membership pointwise in both directions, and `∈-asFiber` does more: from a proof of `x ∈ a` it returns an actual, untruncated pair of an index and a presenting path. That untruncatedness is what lets index recovery be a function rather than a choice. The stock sets are also ready-made: the empty set with its refutation `∅-empty`, the pair `⁅ a , b ⁆`{.Agda} with `pairing-ax`, the union `⋃ a`{.Agda} with `union-ax`, the singleton `⁅ a ⁆s`{.Agda} with its classification, and the binary union `_∪_`{.Agda}.
<!--zh-->
成员关系有两种形态，全章都在二者之间移动。每个集合 `a` 都有小索引类型 `⟪ a ⟫`{.Agda}，配一个像恰为 `a` 的嵌入 `⟪ a ⟫↪`{.Agda}；小隶属 `x ∈ₛ a` 说某个索引呈现 `x`。等价 `∈∈ₛ` 在两个方向上逐点互换小隶属与普通隶属；`∈-asFiber` 则更进一步：从 `x ∈ a` 的证明返回实际的不加截断的对 (一个索引加一条呈现路径)。正是这种不加截断性使索引回收成为函数而非选择。所需的基本集合也已备好：带反驳 `∅-empty` 的空集、配对 `⁅ a , b ⁆`{.Agda} 与 `pairing-ax`、并 `⋃ a`{.Agda} 与 `union-ax`、带分类的单点集 `⁅ a ⁆s`{.Agda}，以及二元并 `_∪_`{.Agda}。
<!--ja-->
所属には二つの形があり、章全体がこの間を行き来します。すべての集合 `a` は小さな添字の型 `⟪ a ⟫`{.Agda} と、像がちょうど `a` である埋め込み `⟪ a ⟫↪`{.Agda} を持ち、小さな所属 `x ∈ₛ a` はある添字が `x` を呈示することを言います。同値 `∈∈ₛ` が小さな所属と通常の所属を双方向に各点で取り替え、`∈-asFiber` はさらに進んで、`x ∈ a` の証明から添字と呈示するパスの対を切り詰めずに実際に返します。この切り詰められていないことが、添字の復元を選択ではなく関数にします。基本的な集合も用意済みです。反駁 `∅-empty` を持つ空集合、対 `⁅ a , b ⁆`{.Agda} と `pairing-ax`、和 `⋃ a`{.Agda} と `union-ax`、分類を持つ一元集合 `⁅ a ⁆s`{.Agda}、そして二項和 `_∪_`{.Agda} です。
<!--/-->

```agda
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber
        ; identityPrinciple; _⊆_; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; pairing-ax; ⋃_; union-ax; ⁅_⁆s; _∪_
        ; SingletonPackage; module InfinitySet )
```

<!--en-->
A worked conversion shows the method that every specification proof uses. For the pair, the library's `pairing-ax` states a bi-implication between `x ∈ₛ ⁅ a , b ⁆` and the disjunction `x ≡ₕ a ⊔ x ≡ₕ b`; for this structure `≡ₕ u v` is the path type `u ≡ v`, which is definitionally what the structure's `≈ˢ u v` is. So the pairing specification, proved in the next section, is just `⇔toPath` applied to `pairing-ax` with one layer of `∈∈ₛ` threaded through each direction: forward turns the ordinary membership into the small one the classification consumes, backward turns the resulting disjunction back into an ordinary membership. The same three moves convert the empty set, the union, and, with one more truncation layer, membership in the union of an indexed family.
<!--zh-->
一个具体的转换展示了所有规格证明都用的方法。对配对，库的 `pairing-ax` 陈述 `x ∈ₛ ⁅ a , b ⁆` 与析取 `x ≡ₕ a ⊔ x ≡ₕ b` 之间的双向蕴含；对当前结构，`≡ₕ u v` 就是路径类型 `u ≡ v`，与结构的 `≈ˢ u v` 按定义相同。于是下一节证明的配对规格只是把 `⇔toPath` 应用于 `pairing-ax`，并在每个方向穿过一层 `∈∈ₛ`：正向把普通隶属转成分类所消耗的小隶属，反向把所得析取转回普通隶属。同样的三步转换空集、并，以及 (多一层截断) 索引族之并的成员关系。
<!--ja-->
一つの具体的な変換が、これからのすべての仕様の証明が使う方法を示します。対について、ライブラリの `pairing-ax` は `x ∈ₛ ⁅ a , b ⁆` と選言 `x ≡ₕ a ⊔ x ≡ₕ b` の双条件を述べます。この構造にとって `≡ₕ u v` はパス型 `u ≡ v` であり、構造の `≈ˢ u v` と定義により同じです。したがって次の節で証明される対の仕様は、`pairing-ax` に `⇔toPath` を適用し、両方向で `∈∈ₛ` を一層だけ通すだけです。順方向は通常の所属を分類が消費する小さな所属へ、逆方向は得られた選言を通常の所属へ戻します。同じ三手順が空集合、和、そして (切り詰めをもう一段加えて) 添字付きの族の和への所属を変換します。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( SetPackage )  -- lint-agda: keep (used qualified: SetPackage.classification)
open InfinitySet using ( sucV; #_; ω )

open ZFStructure 𝒮ᵥ
```

<!--en-->
The target of all these conversions is the record `isZFModel`{.Agda}, whose fields are the ZF axioms: extensionality, regularity, empty set, pairing, union, separation, replacement, power set, and strong infinity through a numeral chain with two pinning equations. Each existence field asks for an `isContr (SetOf Q)`{.Agda}: a set realizing the class `Q` together with uniqueness data, which extensionality supplies; `isZFCModel`{.Agda} adds the choice-set field. Satisfaction for the deep-embedded formulas is instantiated at this structure: `(y ∷ x ∷ []) ⊨ φ`{.Agda} reads a formula `φ` of arity two at the environment that assigns `y` to the first free-variable slot and `x` to the second. The axiom schemas are each supplied as functions of their parameters, so every instance, for every formula, holds at once.
<!--zh-->
所有这些转换的目标是 record `isZFModel`{.Agda}，其字段即 ZF 公理：外延性、正则性、空集、配对、并、分离、替换、幂集，以及经数码链及其两条固定方程表述的强无穷。每个存在性字段要求 `isContr (SetOf Q)`{.Agda}：实现类 `Q` 的集合加上唯一性数据，唯一性由外延性提供；`isZFCModel`{.Agda} 再加选择集字段。深嵌入公式的满足关系在此结构上实例化：`(y ∷ x ∷ []) ⊨ φ`{.Agda} 表示在把 `y` 赋给第一个自由变元槽、`x` 赋给第二个的环境下读出元数为 2 的公式 `φ`。各公理模式都作为其参数的函数给出，因此对每个公式的每个实例都一次成立。
<!--ja-->
これらの変換の目標は record `isZFModel`{.Agda} で、その欄は ZF の公理そのものです。外延性、正則性、空集合、対、和、分出、置換、冪集合、そして数項の列と二つの固定方程式で表される強い無限です。各存在の欄は `isContr (SetOf Q)`{.Agda}、すなわちクラス `Q` を実現する集合と一意性のデータを要求し、一意性は外延性が供給します。`isZFCModel`{.Agda} は選択集合の欄を加えます。深く埋め込まれた論理式の充足はこの構造上で具体化されます。`(y ∷ x ∷ []) ⊨ φ`{.Agda} は、アリティ 2 の論理式 `φ` を、最初の自由変数の枠に `y` を、次の枠に `x` を割り当てる環境のもとで読むことを意味します。各公理のスキーマはパラメータの関数として与えられるので、すべての論理式に対するすべての実例が一度に成ります。
<!--/-->

```agda

module Model = FOL.ZFModel 𝒮ᵥ
open Model using ( SetOf; _⊆ˢ_; setOf-unique; isZFModel; isZFCModel )

module SemanticsV = FOL.Semantics 𝒮ᵥ
open SemanticsV.At S id using ( _⊨_ )
```

<!--en-->
## The basic sets

The empty set, pairing, and union are the easiest fields to discharge, because the constructions and their classifications already exist in the hierarchy library. What remains is to change the shape of the statements. A specification for the model record is an equality of truth values, and indeed a path: for every carrier element `x`, the truth value `x ∈ˢ b` must be equal, as a path, to the class description `Q x`. The library states its axioms through the small membership `∈ₛ`, so each conversion applies the same three moves: `∈∈ₛ`{.Agda} trades small membership for ordinary membership pointwise, the library's classification supplies the corresponding bi-implication, and `⇔toPath`{.Agda} rewrites that bi-implication into the required path. For pairing the correspondence is closest: the library's "equal to `a` or to `b`" is definitionally the field's `(x ≈ˢ a) ⊔ (x ≈ˢ b)`, so only the layer of `∈∈ₛ` is genuinely work.
<!--zh-->
## 基本集合

空集、配对与并是最容易兑现的字段，因为这些构造及其分类在层级库中已经存在。剩下的只是改变陈述的形状。模型 record 的规格是真值的相等，而且是一条路径：对载体的每个元素 `x`，真值 `x ∈ˢ b` 必须作为路径等于类描述 `Q x`。库通过小隶属 `∈ₛ` 陈述其公理，于是每次转换都用同样三步：`∈∈ₛ`{.Agda} 逐点互换小隶属与普通隶属，库的分类给出相应的双向蕴含，`⇔toPath`{.Agda} 把该双向蕴含改写成所需的路径。配对最贴近：库的「等于 `a` 或等于 `b`」与字段的 `(x ≈ˢ a) ⊔ (x ≈ˢ b)` 按定义相同，真正的工作只剩一层 `∈∈ₛ`。
<!--ja-->
## 基本的な集合

空集合、対、和集合は最も簡単に満たせる欄です。構成とその分類が階層のライブラリにすでにあるからです。残るのは主張の形を整えることだけです。モデルのレコードに対する仕様とは真理値の等式、それもパスであり、台の各要素 `x` について真理値 `x ∈ˢ b` がクラスの記述 `Q x` とパスとして等しくなければなりません。ライブラリは公理を小さな所属 `∈ₛ` を通して述べるので、変換は毎回同じ三手順です。`∈∈ₛ`{.Agda} が小さな所属と通常の所属を各点で取り替え、ライブラリの分類が対応する双条件を供給し、`⇔toPath`{.Agda} がその双条件を要求されるパスに書き換えます。最も対応が直接的なのは対で、ライブラリの「`a` と等しいか `b` と等しい」は欄の `(x ≈ˢ a) ⊔ (x ≈ˢ b)` と定義により同じなので、真の仕事は `∈∈ₛ` の一層だけです。
<!--/-->

<!--en-->
The empty-set specification asks that, for every carrier element `x`, the truth value of `x ∈ˢ ∅` be the path-equal image of the falsity `⊥`. This is the chapter's basic conversion in miniature. What the library proves is that `∅` has no members in the small membership `∈ₛ`, so the two membership notions must be exchanged pointwise first. Forward, `∈∈ₛ` turns a proof of `x ∈ˢ ∅` into the small membership that `∅-empty` refutes, and from the contradiction the empty type is inhabited, which is exactly what the implication demands. Backward there is nothing to build, since no element of `⊥` can be supplied. `⇔toPath` then converts the resulting bi-implication of propositions into the path of truth values the specification requires.
<!--zh-->
空集的规格要求：对载体的每个元素 `x`，真值 `x ∈ˢ ∅` 作为路径恰等于假值 `⊥` 的像。这是本章基本转换的缩影。库所证明的是 `∅` 在小隶属 `∈ₛ` 意义下没有成员，所以先要逐点交换两种隶属。正向，`∈∈ₛ` 把 `x ∈ˢ ∅` 的证明变成被 `∅-empty` 驳斥的小隶属；由这一矛盾，空类型有元素，这正蕴含所需的结论。反向则无需构造任何东西，因为 `⊥` 没有元素可给。`⇔toPath` 最后把所得的命题间双向蕴含转换成规格要求的真值路径。
<!--ja-->
空集合の仕様は、台の各要素 `x` について、真理値 `x ∈ˢ ∅` がパスとして偽 `⊥` とちょうど一致することを求めます。これは本章の基本変換の縮図です。ライブラリが示すのは、`∅` が小さな所属 `∈ₛ` の意味で元を持たないことなので、まず二つの所属を各点で交換します。順方向では、`∈∈ₛ` が `x ∈ˢ ∅` の証明を `∅-empty` が反駁する小さな所属へ変え、この矛盾から空の型の要素が得られ、まさに含意の要求を満たします。逆方向は構成すべきものがありません。`⊥` には要素がないからです。`⇔toPath` が最後に、得られた命題間の双条件を仕様の要求する真理値のパスへ変換します。
<!--/-->

```agda
empty-spec : (x : S) → (x ∈ˢ ∅) ≡ ⊥
empty-spec x = ⇔toPath
  (λ x∈ → Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst x∈)))
  (λ ())

pair-spec : (a b x : S) → (x ∈ˢ ⁅ a , b ⁆) ≡ ((x ≈ˢ a) ⊔ (x ≈ˢ b))
```

<!--en-->
Pairing asks that membership in `⁅ a , b ⁆` equal the disjunction of being equal to `a` and being equal to `b`, where the equalities are read as the structure's `≈ˢ`. The library's `pairing-ax` states a bi-implication between the small membership `x ∈ₛ ⁅ a , b ⁆` and the corresponding disjunction of small equality with `a` or `b`, and the propositional part of the statement already matches the target. Forward, one application of `∈∈ₛ` converts the ordinary membership `x ∈ˢ ⁅ a , b ⁆` into the small form that `pairing-ax` consumes, and its first direction returns the disjunction. Backward, the second direction of `pairing-ax` produces the small membership, and the other half of `∈∈ₛ` lifts it back to ordinary membership. Each direction is a single application of the library result wrapped in one exchange of membership notation.
<!--zh-->
配对要求：`⁅ a , b ⁆` 中的成员关系等于「与 `a` 相等或与 `b` 相等」的析取，其中相等按结构的 `≈ˢ` 读出。库的 `pairing-ax` 给出小隶属 `x ∈ₛ ⁅ a , b ⁆` 与「与 `a` 或 `b` 小相等」的析取之间的双向蕴含，其命题部分已与目标形状一致。正向，`∈∈ₛ` 的一次应用把普通成员资格 `x ∈ˢ ⁅ a , b ⁆` 转成 `pairing-ax` 所消耗的小形式，其第一方向返回该析取。反向，`pairing-ax` 的第二方向给出小隶属，`∈∈ₛ` 的另一半再把它提升回普通成员资格。每个方向都是一次库结果的应用，外面只包一层隶属记号的交换。
<!--ja-->
対は、`⁅ a , b ⁆` への所属が「`a` と等しいか `b` と等しいか」の選言に等しいことを求めます。等しさは構造の `≈ˢ` として読みます。ライブラリの `pairing-ax` は、小さな所属 `x ∈ₛ ⁅ a , b ⁆` と「`a` または `b` との小さな等しさ」の選言との双条件を述べ、その命題の部分はすでに目標の形と一致しています。順方向では、`∈∈ₛ` の一度の適用が通常の所属 `x ∈ˢ ⁅ a , b ⁆` を `pairing-ax` の消費する小形式へ変え、その第一方向が選言を返します。逆方向では、`pairing-ax` の第二方向が小さな所属を与え、`∈∈ₛ` のもう半分がそれを通常の所属へ引き上げます。各方向は、ライブラリの結果の一度の適用に所属記法の交換を一層かぶせただけです。
<!--/-->

```agda
pair-spec a b x = ⇔toPath
  (λ x∈ → pairing-ax a b x .fst (∈∈ₛ {a = x} {b = ⁅ a , b ⁆} .fst x∈))
  (λ h → ∈∈ₛ {a = x} {b = ⁅ a , b ⁆} .snd (pairing-ax a b x .snd h))

union-spec : (a x : S) → (x ∈ˢ (⋃ a)) ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ (x ∈ˢ y))
union-spec a x = ⇔toPath
```

<!--en-->
Union is the first specification with an existential shape: membership in `⋃ a` should equal the truncated statement that some `y` lies in `a` with `x` in `y`. Forward, `union-ax` yields such a truncated triple `(v , v in a , x in v)`, but with both memberships in small form. The rewriting happens inside a propositional truncation with a propositional target, so `PT.map` transforms the witness in place: `∈∈ₛ` turns `v ∈ₛ a` into an ordinary member of `a`, and `x ∈ₛ v` into an ordinary member of `v`. The outcome is a witness of the indexed disjunction `⋁ S`, the direct `hProp` mere-existence statement over the carrier, and no member is chosen.
<!--zh-->
并是第一个带存在形状的规格：`⋃ a` 中的成员关系应等于「某个 `y` 属于 `a` 且 `x` 属于 `y`」的截断陈述。正向，`union-ax` 给出的正是这样的截断三元组 `(v , v ∈ a , x ∈ v)`，只是两个成员资格都是小形式。改写发生在命题截断内部，而目标仍是命题，所以 `PT.map` 就地改写见证：`∈∈ₛ` 把 `v ∈ₛ a` 变成 `a` 的普通成员，把 `x ∈ₛ v` 变成 `v` 的普通成员。结果是带索引析取 `⋁ S` 的一个见证，即`hProp` 上对载体的纯粹存在陈述，并且不选出任何成员。
<!--ja-->
和は存在の形をもつ最初の仕様です。`⋃ a` への所属は、「ある `y` が `a` に属し `x` が `y` に属する」という切り詰められた主張に等しいはずです。順方向では、`union-ax` がまさにそのような切り詰められた三つ組 `(v , v ∈ a , x ∈ v)` を与えますが、二つの所属がともに小形式です。書き換えは命題の截断の内部で行われ、目標も命題なので、`PT.map` が証人をその場で変えます。`∈∈ₛ` が `v ∈ₛ a` を `a` の通常の要素へ、`x ∈ₛ v` を `v` の通常の要素へ変えます。結果は添字付き選言 `⋁ S` の証人、すなわち`hProp` 上で台を量化する単なる存在の主張であり、どの元も選ばれません。
<!--/-->

```agda
  (λ x∈ → PT.map
    (λ { (v , va , xv) → v , ∈∈ₛ {a = v} {b = a} .snd va
                           , ∈∈ₛ {a = x} {b = v} .snd xv })
    (union-ax a x .fst (∈∈ₛ {a = x} {b = ⋃ a} .fst x∈)))
  (λ h → ∈∈ₛ {a = x} {b = ⋃ a} .snd (union-ax a x .snd (PT.map
```

<!--en-->
Backward runs the same exchange in reverse. From a truncated witness of the indexed disjunction, `PT.map` takes each case `(v , v in a , x in v)` and, using the other direction of `∈∈ₛ`, rebuilds the small-form triple that `union-ax` consumes; its second direction then returns small membership in `⋃ a`, which the remaining half of `∈∈ₛ` lifts to ordinary membership. Together the two directions give the path of truth values the specification requires, both derived from the one library classification plus the pointwise exchange of membership notation.
<!--zh-->
反向把同一交换倒过来做。从带索引析取的截断见证出发，`PT.map` 对每个情形 `(v , v ∈ a , x ∈ v)` 用 `∈∈ₛ` 的另一方向重建 `union-ax` 所消耗的小形式三元组；其第二方向给出 `⋃ a` 中的小隶属，再由 `∈∈ₛ` 的另一半提升为普通成员资格。两个方向合起来给出规格所需的真值路径，都来自同一个库分类加上逐点的隶属记号交换。
<!--ja-->
逆方向は同じ交換を逆向きに行います。添字付き選言の切り詰められた証人から出発し、`PT.map` が各場合 `(v , v ∈ a , x ∈ v)` に対して `∈∈ₛ` の逆向きで `union-ax` の消費する小形式の三つ組を組み立てます。その第二方向が `⋃ a` への小さな所属を返し、`∈∈ₛ` のもう半分がそれを通常の所属へ引き上げます。二つの方向を合わせると仕様の要求する真理値のパスが得られ、いずれも一つのライブラリの分類と各点の所属記法の交換から来ます。
<!--/-->

```agda
    (λ { (v , va , xv) → v , ∈∈ₛ {a = v} {b = a} .fst va
                           , ∈∈ₛ {a = x} {b = v} .fst xv })
    h)))
```

<!--en-->
The goal of this chapter is to realize each axiom of ZF inside the cumulative hierarchy, at one fixed universe level `ℓ`: the structure `𝒮ᵥ`{.Agda} has a carrier `S` with truth-valued equality and membership, and a model record demands, for each axiom, a set whose membership is path-equal to the prescribed description. The assumptions are uneven, and it pays to separate them. The stock constructions, namely the empty set, pair, union, and infinity, and the whole replacement argument need no extra assumption at all. Full separation needs propositional resizing, so that the satisfaction of each formula becomes a small proposition pointwise. Power set needs a small classifier `HPropSmallness`, a small type equivalent to all of `hProp ℓ`. The packaged corollaries record the combined cost: `V⊨ZF` assumes exactly `LEM (ℓ-suc ℓ)`, and `V⊨ZFC` assumes exactly `SetChoice (ℓ-suc ℓ)`. This section stays on the assumption-free side. It develops the basic membership specifications for the union of a set and then for the union of an indexed family `f : X → S`. The set `⋃ (sett X f)` collects the values of the family through an intermediate set, and it is worth reading membership in that union directly as membership in some family member. Unfolding `union-spec` gives a truncated existential over members `v` of the union, and since each such `v` is itself presented by an index of the `sett`, a second truncated layer sits on top. The two lemmas below compose the layers into one, in each direction.
<!--zh-->
本章的目标是在累积层级内部实现 ZF 的每条公理，全程固定在同一个宇宙层级 `ℓ` 上：结构 `𝒮ᵥ`{.Agda} 带有取真值的等词与成员关系的载体 `S`，模型 record 对每条公理都要求一个集合，其成员关系按路径等于所规定的描述。各部分所需假设并不均匀，值得分开列出。层级中已有的构造，即空集、配对、并与无穷，以及整个替换论证，完全不需要额外假设。全分离需要命题降层，使每条公式的满足逐点成为小命题。幂集需要小分类器 `HPropSmallness`，一个与整个 `hProp ℓ` 等价的小类型。打包的推论记录合并后的代价：`V⊨ZF` 恰假设 `LEM (ℓ-suc ℓ)`，`V⊨ZFC` 恰假设 `SetChoice (ℓ-suc ℓ)`。本节停留在无需假设的一侧，先为一个集合的并、再为索引族 `f : X → S` 的并展开基本成员规格。集合 `⋃ (sett X f)` 经由一个中间集合收拢族的取值，值得把属于这个并直接读作属于某个族元。展开 `union-spec` 得到对并的成员 `v` 的截断存在式，而每个这样的 `v` 又由 `sett` 的一个索引呈现，于是上面还叠着第二层截断。下面两条引理在两个方向上把各层合而为一。
<!--ja-->
本章の目標は、一つの固定した宇宙レベル `ℓ` の上で、累積階層の内側に ZF の各公理を実現することです。構造 `𝒮ᵥ`{.Agda} は真理値を返す等号と所属を備えた台 `S` を持ち、モデルの record は各公理について、その所属がパスとして定められた記述に等しい集合を要求します。仮定は部分によって異なるので、分けて述べる価値があります。基本的な構成、すなわち空集合、対、和、無限と、置換の議論全体には、追加の仮定はまったく要りません。完全な分出には命題リサイズが必要で、各論理式の充足が点ごとに小さな命題になります。冪集合には小分類子 `HPropSmallness`、つまり `hProp ℓ` 全体と同値な小さな型が必要です。まとめられた帰結は合算のコストを記録します。`V⊨ZF` はちょうど `LEM (ℓ-suc ℓ)` を仮定し、`V⊨ZFC` はちょうど `SetChoice (ℓ-suc ℓ)` を仮定します。この節は仮定の不要な側にとどまり、まず一つの集合の和、次に添字付きの族 `f : X → S` の和について、基本的な所属の仕様を展開します。集合 `⋃ (sett X f)` は中間の集合を通して族の値を集めますが、この和への所属をある族の元への所属として直接読めることは有益です。`union-spec` を展開すると和の元 `v` にわたる切り詰められた存在式が得られ、そのような `v` はそれぞれ `sett` の添字で呈示されるため、その上に第二の切り詰めの層が乗ります。以下の二つの補題は、各方向でこの層を一つへまとめます。
<!--/-->

<!--en-->
The inward lemma turns one concrete membership `x ∈ f i` into membership in the whole union. The witness is written down rather than searched for: the intermediate element is `f i` itself, presented by the index `i` through the reflexive path, with `h` certifying that `x` lies in it. Since `union-spec` is an equality of truth values, `subst ⟨_⟩` transports this witness across the reversed specification, so the truncated triple is consumed exactly in the shape the union characterization expects. Nothing enters beyond `union-spec` itself.
<!--zh-->
内向引理把一个具体的成员资格 `x ∈ f i` 变成整个并的成员资格。见证是直接写出而非寻找的：中间元素就是 `f i` 本身，由索引 `i` 经自反路径呈现，`h` 证明 `x` 在其中。由于 `union-spec` 是真值的相等，`subst ⟨_⟩` 沿反向的规格搬运该见证，使这个截断三元组恰以并的特征化所期望的形状被消耗。除 `union-spec` 本身外不进入任何东西。
<!--ja-->
内向きの補題は、一つの具体的な所属 `x ∈ f i` を和全体への所属へ変えます。証人は探し出すのではなく書き下されます。中間の要素は `f i` そのものであり、添字 `i` が自反なパスで呈示し、`h` が `x` がそこに属することを証明します。`union-spec` は真理値の等式なので、`subst ⟨_⟩` が逆向きの仕様に沿ってこの証人を運び、切り詰められた三つ組が和の特徴付けの期待するちょうどその形で消費されます。`union-spec` 自身のほかには何も入りません。
<!--/-->

```agda
union-family-in : (X : Type ℓ) (f : X → S) (i : X) (x : S)
                → ⟨ x ∈ˢ f i ⟩ → ⟨ x ∈ˢ (⋃ (sett X f)) ⟩
union-family-in X f i x h = subst ⟨_⟩ (sym (union-spec (sett X f) x))
  ∣ f i , ∣ i , refl ∣₁ , h ∣₁

union-family-out : (X : Type ℓ) (f : X → S) (x : S)
```

<!--en-->
The outward lemma recovers, from membership in the union, merely some family member containing `x`. Unfolding `union-spec` gives a truncated triple `(v , v in the union , x in v)`; the second component says `v` is presented by an index, so a further `PT.map` inside the truncation extracts a pair `(i , q)` with `f i ≡ v`. The membership of `x` in `v` is then transported along the reverse of `q` to land in `f i`. The target keeps its truncation, so the eliminator is `PT.rec` into `∥ Σ[ i ] ⟨ x ∈ˢ f i ⟩ ∥₁` with `squash₁` as the propositionhood evidence. The conclusion stays a mere existence: some family member contains `x`, and no member is chosen.
<!--zh-->
外向引理从「属于并」恢复出：纯粹地存在某个含 `x` 的族元。展开 `union-spec` 得到截断的三元组 `(v , v 在并中 , x 在 v 中)`；第二分量说 `v` 由某个索引呈现，于是在截断内部再作一次 `PT.map`，抽出 `(i , q)` 使 `f i ≡ v`。然后把 `x` 在 `v` 中的成员资格沿 `q` 的反向搬运，落进 `f i`。目标保持截断，因此消去用 `PT.rec` 进入 `∥ Σ[ i ] ⟨ x ∈ˢ f i ⟩ ∥₁`，以 `squash₁` 为命题性证据；结论仍是纯粹存在：某个族元含 `x`，而不选出任何族元。
<!--ja-->
外向きの補題は、和への所属から「`x` を含む族の元が純粋に存在する」ことを取り出します。`union-spec` を展開すると、切り詰められた三つ組 `(v , v は和に属する , x は v に属する)` が得られます。第二成分は `v` が添字で呈示されると言うので、截断の内部でさらに `PT.map` を行い、`f i ≡ v` なる対 `(i , q)` を取り出します。そして `v` における `x` の所属を `q` の逆向きに沿って運び、`f i` に着地させます。目標は截断を保つので、消去には `squash₁` を命題性の証拠として `PT.rec` で `∥ Σ[ i ] ⟨ x ∈ˢ f i ⟩ ∥₁` に入ります。結論は純粋な存在のままです。ある族の元が `x` を含むのであり、どの元も選ばれません。
<!--/-->

```agda
                 → ⟨ x ∈ˢ (⋃ (sett X f)) ⟩ → ∥ Σ[ i ∈ X ] ⟨ x ∈ˢ f i ⟩ ∥₁
union-family-out X f x h = PT.rec PT.squash₁
  (λ { (v , hv , hx) → PT.map
    (λ { (i , q) → i , subst (λ w → ⟨ x ∈ˢ w ⟩) (sym q) hx }) hv })
  (subst ⟨_⟩ (union-spec (sett X f) x) h)
```

<!--en-->
## Replacement without an additional axiom

Replacement is a schema, and in ordinary set theory it is a genuine axiom: for each set `a` and each formula `φ` functional on `a`, the existence of the image must be postulated. Here the hierarchy itself supplies a construction, and no choice principle is invoked. The functionality hypothesis is stated as contractibility: for every member `x` of `a`, the type of values `y` with `(y ∷ x ∷ []) ⊨ φ` is contractible, so a center value comes with proofs that every other value is identified with it. Because contractibility provides actual data, that center value can be read off and used to build the image. The members of `a`, however, are given only through their small presentation: each member appears as `⟪ a ⟫↪ m` for some index `m` of the type `⟪ a ⟫`. The construction therefore indexes the image by `⟪ a ⟫` itself, and the potentially delicate step, recovering an index from a membership fact, is a function rather than a choice, because the presentation fibers of `∈-asFiber` are untruncated. What must be checked is that membership in the resulting set has exactly the truth value the schema demands. The forward direction only reads off the data the image provides; the backward direction recovers an index from an external membership and then uses the contraction of the functionality hypothesis once, to identify the externally given value with the value the construction chose at the recovered index.
<!--zh-->
## 无需新增公理的替换

替换是一条模式公理：在通常集合论中，对每个集合 `a` 与在 `a` 上函数性的公式 `φ`，像的存在性必须被公理化地断言。这里由层级自身给出构造，并且不调用任何选择原理。函数性假设以紧缩性陈述：对 `a` 的每个成员 `x`，满足 `(y ∷ x ∷ []) ⊨ φ` 的 `y` 构成的类型是紧缩的，于是中心值带有「其他任何值都与它等同」的证明。由于紧缩性提供实际数据，这个中心值可以被读出并用于构造像。但 `a` 的成员只通过小呈现给出：每个成员都以 `⟪ a ⟫↪ m` 的形式出现，`m` 是类型 `⟪ a ⟫` 的某个索引。因此构造以 `⟪ a ⟫` 本身为像编索引；可能精细的一步，即从成员资格回收索引，是函数而非选择，因为 `∈-asFiber` 的呈现纤维不加截断。需要核对的是：所得集合的成员关系恰有模式所要求的真值。正向只是读出像自身提供的资料；反向从外部成员资格回收一个索引，然后用一次函数性假设的紧缩，把外部给定的值与构造在回收索引处选定的值等同起来。
<!--ja-->
## 追加の公理を要しない置換

置換は図式形式の公理で、通常の集合論では、各集合 `a` と `a` 上で関数的な論理式 `φ` に対して像の存在を公理として要請します。ここでは階層そのものが構成を与え、選択原理は一切呼びません。関数性の仮定は緊縮性として述べられます。`a` の各元 `x` に対し、`(y ∷ x ∷ []) ⊨ φ` を満たす `y` の型が緊縮的であり、中心の値には、他のすべての値がそれと同一視されることの証明が伴います。緊縮性が実際のデータを与えるため、この中心の値を読み出して像の構成に使えます。ただし `a` の元は小さな提示を通してしか与えられず、各元は型 `⟪ a ⟫` のある添字 `m` に対して `⟪ a ⟫↪ m` として現れます。そこで構成は像に `⟪ a ⟫` 自身で添字を付けます。繊細になりうる段階、すなわち所属の事実から添字を復元する作業は、`∈-asFiber` の提示のファイバーが切り詰められていないため、選択ではなく関数です。確かめるべきは、出来上がった集合への所属が図式の要求する真理値をちょうど持つことです。順方向は像が提供するデータを読み出すだけです。逆方向は外部の所属から添字を復元し、その後、関数性の仮定の緊縮を一度だけ使い、外部から与えられた値を、復元した添字で構成が選んだ値と同一視します。
<!--/-->

<!--en-->
One preliminary fact runs through everything below: if `m` is an index of the presentation of `a`, then the element `⟪ a ⟫↪ m` it presents really is a member of `a`. The small membership `⟪ a ⟫↪ m ∈ₛ a` holds by definition of the presentation, and `∈∈ₛ` lifts it to the structural membership. The section then takes its data: a set `a`, a formula `φ` with two free-variable slots, and the functionality hypothesis `fc`, which asserts for each `x ∈ a` that the type of values `y` satisfying `(y ∷ x ∷ []) ⊨ φ` is contractible. Contractibility is data, a center together with a contraction, so the center value for each member of `a` is available for computation without any choice principle.
<!--zh-->
一个预备事实贯穿下文：若 `m` 是 `a` 的呈现中的一个索引，则它呈现的元素 `⟪ a ⟫↪ m` 确实是 `a` 的成员。小成员资格 `⟪ a ⟫↪ m ∈ₛ a` 按呈现的定义成立，`∈∈ₛ` 把它提升为结构性成员资格。本节随后取定数据：集合 `a`、有两个自由变元槽的公式 `φ`，以及函数性假设 `fc`，它对每个 `x ∈ a` 断言满足 `(y ∷ x ∷ []) ⊨ φ` 的 `y` 构成的类型是紧缩的。紧缩性是数据，即一个中心加上一个收缩，因此 `a` 的每个成员的中心值可供计算使用，无需任何选择原理。
<!--ja-->
一つの準備的事実が以下のすべてを貫きます。`m` が `a` の提示における添字なら、それが呈示する要素 `⟪ a ⟫↪ m` は実際に `a` の要素である、というものです。小さな所属 `⟪ a ⟫↪ m ∈ₛ a` は提示の定義により成り立ち、`∈∈ₛ` がそれを構造的な所属へ引き上げます。続いてこの節のデータを取ります。集合 `a`、自由変数の枠を二つ持つ論理式 `φ`、そして関数性の仮定 `fc` です。`fc` は各 `x ∈ a` に対し、`(y ∷ x ∷ []) ⊨ φ` を満たす `y` の型が緊縮的であると主張します。緊縮性はデータ、つまり中心と緊縮の対なので、`a` の各元に対する中心の値は、いかなる選択原理もなしに計算に使えます。
<!--/-->

```agda
private
  memb : (a : S) (m : ⟪ a ⟫) → ⟨ ⟪ a ⟫↪ m ∈ˢ a ⟩
  memb a m = ∈∈ₛ {a = ⟪ a ⟫↪ m} {b = a} .snd (∈ₛ⟪ a ⟫↪ m)

module _ (a : S) (φ : Formula S 2)
         (fc : (x : S) → ⟨ x ∈ˢ a ⟩ → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ φ ⟩)) where
```

<!--en-->
The image is then a direct assembly: `replaceImage` is `sett` over the index type `⟪ a ⟫`, sending each index `m` to the center value that `fc` provides for the member `⟪ a ⟫↪ m`. Its specification says that membership in `replaceImage` equals the truth value obtained by disjoining `(x ∈ a) ⊓ φ(y, x)` over all `x`, which is the replacement schema in semantic form: `y` belongs to the image exactly when it arises as the value of `φ` at some member of `a`. As elsewhere in the chapter, `⇔toPath` converts the two implications into the path of truth values the specification asks for.
<!--zh-->
像集于是是直接的组装：`replaceImage` 是索引类型 `⟪ a ⟫` 上的 `sett`，把每个索引 `m` 映到 `fc` 为成员 `⟪ a ⟫↪ m` 提供的中心值。其规格说：属于 `replaceImage` 等于对所有 `x` 析取 `(x ∈ a) ⊓ φ(y, x)` 得到的真值。这正是语义形式的替换模式：`y` 属于像，当且仅当它是 `φ` 在 `a` 的某个成员处取的值。与本章其他地方一样，`⇔toPath` 把两个蕴含转换成规格要求的真值路径。
<!--ja-->
像はこうして直接的な組み立てになります。`replaceImage` は添字型 `⟪ a ⟫` 上の `sett` で、各添字 `m` を、`fc` が要素 `⟪ a ⟫↪ m` のために提供する中心の値へ写します。その仕様は、`replaceImage` への所属が、すべての `x` にわたって `(x ∈ a) ⊓ φ(y, x)` を選言した真理値と等しいことを述べます。これは意味論の形での置換図式です。`y` が像に属するのは、`a` のある元で `φ` の値として生じるときちょうどそのときです。本章の他の場所と同様に、`⇔toPath` が二つの含意を仕様の要求する真理値のパスへ変換します。
<!--/-->

```agda

  replaceImage : S
  replaceImage = sett ⟪ a ⟫ (λ m → fc (⟪ a ⟫↪ m) (memb a m) .fst .fst)

  replaceImage-spec : ∀ y → (y ∈ˢ replaceImage)
                    ≡ ⋁ S (λ x → (x ∈ˢ a) ⊓ ((y ∷ x ∷ []) ⊨ φ))
  replaceImage-spec y = ⇔toPath fwd bwd
```

<!--en-->
The forward direction of the specification starts from a membership in the image. Because `replaceImage` is a `sett` indexed by the presentation type of `a`, such a membership carries an index `m` of `⟪ a ⟫` together with a path `q` from the presented element `⟪ a ⟫↪ m` to `y`. The witness for the right-hand side is then assembled from this one index. First, the presented element is a member of `a`, by the preliminary fact `memb`. Second, `fc` provides the value at that member together with the proof that `φ` holds of it and that member; transporting that proof along `q` moves the second free-variable slot from the presented element to `y`. This direction uses none of the uniqueness content of `fc`: however the image presents `y`, some member of `a` is produced at which `φ(y, x)` holds.
<!--zh-->
规格的正向方向从像中的成员资格出发。由于 `replaceImage` 是以 `a` 的呈现类型为索引的 `sett`，这样的成员资格带有 `⟪ a ⟫` 的一个索引 `m`，以及一条从被呈现元素 `⟪ a ⟫↪ m` 到 `y` 的路径 `q`。右侧的见证就由这一个索引组装而成。第一，由预备事实 `memb`，被呈现元素是 `a` 的成员。第二，`fc` 在该成员处给出值以及 `φ` 对该值与该成员成立的证明；沿 `q` 传递该证明，就把公式的第二个自由变元槽从被呈现元素移到 `y`。这一方向不使用 `fc` 的任何唯一性内容：无论像以何种方式呈现 `y`，都得到 `a` 中使 `φ(y, x)` 成立的某个成员。
<!--ja-->
仕様の順方向は像への所属から始まります。`replaceImage` は `a` の提示型を添字とする `sett` なので、その所属には `⟪ a ⟫` の添字 `m` と、呈示された要素 `⟪ a ⟫↪ m` から `y` へのパス `q` が伴います。右辺の証拠はこの一つの添字から組み立てられます。第一に、準備的事実 `memb` により、呈示された要素は `a` の元です。第二に、`fc` がその元に対して値と、`φ` がその値とその元について成り立つことの証明を与えるので、その証明を `q` に沿って輸送すれば、論理式の第二の自由変数の枠は呈示された要素から `y` へ移ります。この方向は `fc` の一意性の内容をまったく使いません。像が `y` をどのように呈示しようとも、`φ(y, x)` が成り立つ `a` のある元が得られます。
<!--/-->

```agda
    where
    fwd : ⟨ y ∈ˢ replaceImage ⟩ → ⟨ ⋁ S (λ x → (x ∈ˢ a) ⊓ ((y ∷ x ∷ []) ⊨ φ)) ⟩
    fwd = PT.map λ { (m , q) →
        ⟪ a ⟫↪ m , memb a m
      , subst (λ v → ⟨ (v ∷ ⟪ a ⟫↪ m ∷ []) ⊨ φ ⟩) q
```

<!--en-->
The backward direction is where a choice principle would seem unavoidable. It receives a truncated witness `(x , x∈a , hφ)` and must produce an index into the image, an index that presents the very member `x` of `a` at which `φ(y, x)` holds. So the fact that `x` is a member must be turned into an index presenting it. The smallness chapter supplies exactly this: `∈-asFiber` returns, as ordinary untruncated data, an actual pair `mf` of an index and a path from the presented element back to `x`. No choice among possible indices is made, because the recovery is a function. The satisfaction proof `hφ` is then transported along the reverse of the path `mf .snd`, moving the second free-variable slot from `x` to the presented element, which is the shape in which the hypothesis `fc` was stated.
<!--zh-->
后向方向正是表面上离不开选择原理之处。它收到截断的见证 `(x , x∈a , hφ)`，必须给出像的一个索引，而且该索引要呈现 `a` 中使 `φ(y, x)` 成立的那个成员 `x` 本身。于是必须把「`x` 是成员」这一事实转化为呈现它的索引。小性一章给出的恰是这个：`∈-asFiber` 以普通的不加截断的数据返回实际的对 `mf`，由一个索引加一条从被呈现元素回到 `x` 的路径组成。回收是函数，因此并没有在可能的索引之间作任何选取。随后把满足证明 `hφ` 沿路径 `mf .snd` 的逆传递，把第二个自由变元槽从 `x` 移到被呈现元素，与前提 `fc` 被陈述的形状一致。
<!--ja-->
逆方向は、一見して選択原理が避けられないように思われる箇所です。切り詰められた証拠 `(x , x∈a , hφ)` を受け取り、像への添字を提示しなければなりません。しかもその添字は、`φ(y, x)` が成り立つ `a` の元 `x` そのものを呈示するものでなければなりません。そこで「`x` が元である」という事実を、それを呈示する添字へ変える必要があります。小ささの章がまさにこれを供給します。`∈-asFiber` は、添字と、呈示された要素から `x` へ戻るパスからなる実際の対 `mf` を、切り詰められていない通常のデータとして返します。復元は関数なので、可能な添字の間で選択を行うことはありません。その後、充足の証明 `hφ` をパス `mf .snd` の逆に沿って輸送し、第二の自由変数の枠を `x` から呈示された要素へ移します。これは前提 `fc` が述べられている形と一致します。
<!--/-->

```agda
              (fc (⟪ a ⟫↪ m) (memb a m) .fst .snd) }
    bwd : ⟨ ⋁ S (λ x → (x ∈ˢ a) ⊓ ((y ∷ x ∷ []) ⊨ φ)) ⟩ → ⟨ y ∈ˢ replaceImage ⟩
    bwd = PT.map λ { (x , x∈a , hφ) →
      let mf = ∈-asFiber {a = x} {b = a} x∈a
          hφ' = subst (λ v → ⟨ (y ∷ v ∷ []) ⊨ φ ⟩) (sym (mf .snd)) hφ
```

<!--en-->
The recovered index still has to become membership in the image, and this is the one place where uniqueness enters. At the index `mf .fst`, the functionality hypothesis says the type of suitable values is contractible, so the externally supplied pair `(y , hφ')` is compared with the chosen center: the contraction yields the center together with a path to it, and the first projection of that path identifies `y` with the value the construction assigned to the presented member, which is an index into `replaceImage`. Uniqueness is thus used exactly once, to recognize the externally given value `y` as one of the internally chosen image values. Combined with the presenting index `mf .fst`, this gives membership of `y` in the image.
<!--zh-->
回收的索引还须变成像中的成员资格，这正是唯一性唯一进入之处。在索引 `mf .fst` 处，函数性假设说合适值构成的类型是紧缩的，于是把外部给定的对 `(y , hφ')` 与选定中心比较：紧缩给出中心及一条到它的路径，该路径的第一投影把 `y` 与构造赋给被呈现成员的值等同起来，而后者就是 `replaceImage` 的一个索引。因此唯一性恰好用了一次，用来把外部给定的值 `y` 认作内部选出的像值之一。与呈现索引 `mf .fst` 合起来，就得到 `y` 在像中的成员资格。
<!--ja-->
復元した添字はなお像への所属へ変えねばならず、一意性が入るのはここだけです。添字 `mf .fst` において関数性の仮定は、適切な値の型が緊縮的であることを言うので、外部から与えられた対 `(y , hφ')` を選ばれた中心と比べます。緊縮は中心とそれへのパスを与え、そのパスの第一射影により、`y` は構成がその呈示された元に割り当てた値、すなわち `replaceImage` への添字と同一視されます。したがって一意性はちょうど一度使われ、外部の値 `y` を内部で選ばれた像の値の一つとして認める役割を果たします。これと呈示する添字 `mf .fst` を合わせれば、`y` の像への所属が得られます。
<!--/-->

```agda
      in mf .fst
       , cong fst (fc (⟪ a ⟫↪ (mf .fst)) (memb a (mf .fst)) .snd (y , hφ')) }
```

<!--en-->
## The numeral chain and ω

Strong infinity is the field the library supplies nearly complete. Its `ω` is a `sett` over `Lift ℕ` with the numerals `#` as the family, so membership in `ω` holds precisely when `x` is merely hit by some `#`. What the record demands, however, is phrased through the model's own numeral chain: zero must be empty, and each successor's members must be exactly the members of the predecessor together with the predecessor itself. The work is therefore to align two chains that step differently. The model's chain takes `a ∪ ⁅ a , a ⁆` as its successor, the library's takes `sucV a = a ∪ ⁅ a ⁆s`. The pair `⁅ a , a ⁆` with a repeated entry and the singleton `⁅ a ⁆s` have the same elements, and extensionality turns that into a path; with this one identification the two chains agree stage by stage, and `ω`'s membership characterization becomes the record's strong infinity.
<!--zh-->
## 数码链与 ω

强无穷是库几乎完整供给的字段。库的 `ω` 是在 `Lift ℕ` 上、以数码 `#` 为族的 `sett`，所以 `x` 属于 `ω` 恰当它仅仅被某个 `#` 命中。但 record 的要求是通过模型自身的数码链表述的：零必须是空的，每个后继的成员必须恰为前驱的成员再加上前驱本身。因此工作在于对齐两条取后继方式不同的链：模型链取 `a ∪ ⁅ a , a ⁆`，库链取 `sucV a = a ∪ ⁅ a ⁆s`。两个元素相同的对集 `⁅ a , a ⁆` 与单点集 `⁅ a ⁆s` 有相同的元素，外延性把它变成一条路径；有了这一次等同，两条链便逐级一致，`ω` 的成员特征化就成为 record 的强无穷。
<!--ja-->
## 数項の列と ω

強い無限は、ライブラリがほぼそのまま供給する欄です。ライブラリの `ω` は `Lift ℕ` の上、数項 `#` を族とする `sett` なので、`x` が `ω` に属するのは、ある `#` が `x` に命中することが単に成り立つときであり、そのときに限ります。しかし record の要求はモデル自身の数項の列を通して述べられます。第 0 項は空でなければならず、各後続項の元は前者の元に前者自身を加えたものにちょうど等しくなければなりません。したがって仕事は、後続の取り方が異なる二つの列を整列させることです。モデルの列は `a ∪ ⁅ a , a ⁆` を、ライブラリの列は `sucV a = a ∪ ⁅ a ⁆s` を取ります。同じ項を二度入れた対 `⁅ a , a ⁆` と一元集合 `⁅ a ⁆s` は同じ元を持ち、外延性がそれをパスに変えます。この一度の同一視により二つの列は段階ごとに一致し、`ω` の所属の特徴付けが record の強い無限になります。
<!--/-->

<!--en-->
The identification `⁅ a , a ⁆ ≡ ⁅ a ⁆s` is a path between sets, so extensionality reduces it to the two membership inclusions. The first inclusion says every element of the pair with a repeated entry is an element of the singleton. Its input is a membership in `⁅ a , a ⁆`, and the pairing axiom unfolds such a membership into a truncated disjunction: the element equals `a` through the left entry of the pair or through the right one.
<!--zh-->
等同 `⁅ a , a ⁆ ≡ ⁅ a ⁆s` 是集合之间的路径，所以外延性把它化归为两个成员收纳。第一个收纳说两个元素相同的对集的每个元素都是单点集的元素。其输入是 `⁅ a , a ⁆` 中的成员资格，配对公理把这样的成员资格展开为截断的析取：该元素经由配对的左分支或右分支等于 `a`。
<!--ja-->
同定 `⁅ a , a ⁆ ≡ ⁅ a ⁆s` は集合の間のパスなので、外延性により二つの所属の包含へ帰着します。第一の包含は、同じ項を二度入れた対のすべての元が一元集合の元であることを言います。その入力は `⁅ a , a ⁆` への所属であり、対の公理はそのような所属を切り詰められた選言へ展開します。すなわち、その元は対の左の項を通じて、または右の項を通じて `a` と等しい、というものです。
<!--/-->

```agda
pair-singleton : (a : S) → ⁅ a , a ⁆ ≡ ⁅ a ⁆s
pair-singleton a = extensionality ⁅ a , a ⁆ ⁅ a ⁆s (s1 , s2)
  where
  singl-cls = SetPackage.classification (SingletonPackage a)
  s1 : ⟨ ⁅ a , a ⁆ ⊆ ⁅ a ⁆s ⟩
```

<!--en-->
Both disjuncts ask for the same thing, membership in `⁅ a ⁆s`, so after the truncated disjunction is eliminated into the proposition `x ≡ a`, whose propositionhood follows from the hierarchy being an h-set, each branch supplies its path and the results agree by that very propositionhood. What is consumed here is the backward direction of the singleton's classification, running from the path `x ≡ a` to the small membership `x ∈ₛ ⁅ a ⁆s`; note that it is the opposite direction from the one the reverse inclusion will use.
<!--zh-->
两个析取支要求的是同一件事：属于 `⁅ a ⁆s`。于是先把截断的析取消入命题 `x ≡ a` (其命题性来自层级是 h-集合)，每个分支给出自己的路径，而两个结果恰由该命题性等同。这里消耗的是单点集分类的反向：从路径 `x ≡ a` 走到小隶属 `x ∈ₛ ⁅ a ⁆s`；注意它与反向包含将要使用的方向恰好相反。
<!--ja-->
どちらの選言支も同じこと、`⁅ a ⁆s` への所属を要求します。そこでまず切り詰められた選言を命題 `x ≡ a` (その命題性は階層が h-集合であることから従います) へ消去し、各分岐が自らのパスを与えれば、二つの結果はまさにその命題性によって同一視されます。ここで使うのは一元集合の分類の逆向きで、パス `x ≡ a` から小さな所属 `x ∈ₛ ⁅ a ⁆s` へ進む方向です。これが後の逆包含で使う向きと逆であることに注意してください。
<!--/-->

```agda
  s1 x x∈ₛ = singl-cls x .snd
    (PT.rec (setIsSet x a)
            (λ { (Sum.inl e) → e ; (Sum.inr e) → e })
            (pairing-ax a a x .fst x∈ₛ))
  s2 : ⟨ ⁅ a ⁆s ⊆ ⁅ a , a ⁆ ⟩
```

<!--en-->
The reverse inclusion runs in the other direction: the classification's forward component turns the membership `x ∈ₛ ⁅ a ⁆s` into the path `x ≡ a`, and this path, injected as the left disjunct, is converted by the pairing axiom into membership in `⁅ a , a ⁆`. With the two sets identified, the model's numeral chain is defined by recursion on `ℕ`: `numeralV zero` is the empty set, and `numeralV (suc n)` unions onto stage `n` a pair whose two entries are both that stage. After the identification this is exactly the von Neumann successor step `n ∪ ⁅ n ⁆s`, since a pair with equal entries and a singleton have the same members.
<!--zh-->
反向包含则朝另一方向进行：分类的正向分量把成员资格 `x ∈ₛ ⁅ a ⁆s` 变成路径 `x ≡ a`，把该路径作为左析取支注入后，配对公理把它转成 `⁅ a , a ⁆` 中的成员资格。两个集合等同之后，模型的数码链按 `ℕ` 递归定义：`numeralV zero` 是空集，`numeralV (suc n)` 在第 `n` 阶段上并上一个两个元素都是该阶段的对集。经等同，由于两个元素相同的对集与单点集成员相同，这正是冯·诺伊曼后继步骤 `n ∪ ⁅ n ⁆s`。
<!--ja-->
逆の包含は逆向きに進みます。分類の順方向の成分が所属 `x ∈ₛ ⁅ a ⁆s` をパス `x ≡ a` に変え、このパスを左の選言支として注入すると、対の公理が `⁅ a , a ⁆` への所属へ変換します。二つの集合の同定が済むと、モデルの数項の列は `ℕ` 上の再帰で定義されます。`numeralV zero` は空集合、`numeralV (suc n)` は段階 `n` に、両方の項がともにその段階である対を併合します。同定の後、等しい項を持つ対と一元集合は同じ元を持つため、これはまさにフォン・ノイマンの後続の一段階 `n ∪ ⁅ n ⁆s` です。
<!--/-->

```agda
  s2 x x∈ₛ = pairing-ax a a x .snd ∣ Sum.inl (singl-cls x .fst x∈ₛ) ∣₁

numeralV : ℕ → S
numeralV zero    = ∅
numeralV (suc n) = numeralV n ∪ ⁅ numeralV n , numeralV n ⁆

numeralV≡# : (n : ℕ) → numeralV n ≡ # n
```

<!--en-->
That the two chains agree is proved by induction on `ℕ`. At zero both sides reduce to the empty set, so the path is `refl`. At the successor step, congruence under the same union-of-pair shape rewrites both sides, and inside the pair the identification `pair-singleton` is applied, which is the step where the extensionality result is consumed. With the chains aligned, the remaining task is to read `ω`'s membership in the model's vocabulary. The statement `ω-specV` says that membership in `ω` equals the indexed disjunction "`x` is equal to some `numeralV`", the index ranging over `Lift ℕ`, whose elements are lifted natural numbers. The equality on the right is `≈ˢ`, the extensional equality of sets of the structure, so the statement is about the set `x`, not about a chosen presentation.
<!--zh-->
两条链的一致按 `ℕ` 归纳证明。在零处两边都化归为空集，路径是 `refl`。后继步在同一个「配对再取并」的形状下用共质性改写两边，并在配对内部应用等同 `pair-singleton`，这正是消耗外延性结果之处。链对齐后，剩下的任务是用模型的语言读 `ω` 的成员关系。陈述 `ω-specV` 说：`ω` 中的成员关系等于带索引的析取「`x` 等于某个 `numeralV`」，索引取遍 `Lift ℕ`，其元素是提升的自然数。右边的相等是 `≈ˢ`，即结构的集合外延相等，因此该陈述是关于集合 `x` 的，而非关于某个被选呈现。
<!--ja-->
二つの列の一致は `ℕ` 上の帰納法で示します。零では両辺とも空集合に簡約されるので、パスは `refl` です。後続の段階では、同じ「対の併合」の形の下で共點性によって両辺を書き換え、対の内部で同定 `pair-singleton` を適用します。外延性の結果が使われるのはこの一歩です。列が整列すると、残りの仕事は `ω` の所属をモデルの語彙で読むことです。`ω-specV` は、`ω` への所属が添字付き選言「`x` はある `numeralV` と等しい」と等しいことを述べます。添字は `Lift ℕ`、つまり持ち上げられた自然数の型を渡ります。右辺の等しさは `≈ˢ`、すなわち構造の集合の外延的等しさなので、この主張は選ばれた提示ではなく集合 `x` そのものについてのものです。
<!--/-->

```agda
numeralV≡# zero    = refl
numeralV≡# (suc n) = cong₂ (λ u v → ⋃ ⁅ u , v ⁆) (numeralV≡# n)
  (cong (λ u → ⁅ u , u ⁆) (numeralV≡# n) ∙ pair-singleton (# n))

ω-specV : (x : S)
        → (x ∈ˢ ω) ≡ ⋁ (Lift {ℓ-zero} {ℓ-suc ℓ} ℕ) (λ n → x ≈ˢ numeralV (lower n))
```

<!--en-->
The proof converts the two descriptions of membership into a path with `⇔toPath`. Forward, a witness `(i , p)` is a lifted index together with a path `p` from `x` to the library numeral `# (lower i)`; composing `p` with the reverses of the alignment paths turns it into a path from `x` to `numeralV (lower i)`. Backward, the same path algebra runs in the opposite direction: a path from `x` to `numeralV` is rewritten, via the alignment, into a path to the matching `#`. The `lift` and `lower` conversions only move the natural number across the `Lift`; the mathematical content of both directions is the alignment `numeralV≡#` and the path algebra around it.
<!--zh-->
证明用 `⇔toPath` 把成员关系的两种描述转成路径。前向：见证 `(i , p)` 是一个提升的索引，加一条从 `x` 到库数码 `# (lower i)` 的路径 `p`；把 `p` 与对齐路径的逆逐段复合，就得到从 `x` 到 `numeralV (lower i)` 的路径。后向：同一套路径代数沿反方向进行，从 `x` 到 `numeralV` 的路径经对齐改写为到相应 `#` 的路径。`lift` 与 `lower` 的转换只是把自然数跨过 `Lift` 移动；两个方向的数学内容都是对齐 `numeralV≡#` 及其周围的路径代数。
<!--ja-->
証明は `⇔toPath` によって所属の二つの記述をパスに変換します。順方向では、証拠 `(i , p)` は持ち上げられた添字と、`x` からライブラリの数項 `# (lower i)` へのパス `p` です。`p` を整列のパスの逆々と合わせて合成すれば、`x` から `numeralV (lower i)` へのパスが得られます。逆方向では同じパスの代数を逆向きに行い、`x` から `numeralV` へのパスを整列を通して対応する `#` へのパスに書き換えます。`lift` と `lower` の変換は自然数を `Lift` の越しに移すだけです。両方向の数学的内容は整列 `numeralV≡#` とその周囲のパスの代数にあります。
<!--/-->

```agda
ω-specV x = ⇔toPath
  (PT.map (λ { (i , p) → lift (lower i)
             , sym p ∙ sym (numeralV≡# (lower i)) }))
  (PT.map (λ { (n , q) → lift (lower n)
             , sym (q ∙ numeralV≡# (lower n)) }))
```

<!--en-->
The record's two pinning equations speak of membership in a successor stage, so the chapter needs the case analysis for `sucV` itself: a member of `sucV A` is, merely, a member of `A` or equal to `A`, and both inclusions hold. This is what lets any numeral chain aligned with the library inherit the pinning equations, since the library numerals step by `sucV`. The analysis unfolds `sucV A` once through the union and pairing axioms; the second disjunct, membership in the singleton `⁅ A ⁆s`, is closed by the singleton's classification.
<!--zh-->
record 的两条固定方程描述的是后继阶段的成员关系，因此本章需要对 `sucV` 本身的分情形分析：`sucV A` 的成员，纯粹地，要么是 `A` 的成员、要么等于 `A`，且两个方向的收纳都成立。由于库数码按 `sucV` 取后继，这使得任何与库对齐的数码链都能继承固定方程。该分析把 `sucV A` 沿并与配对公理展开一次；第二个析取支，即属于单点集 `⁅ A ⁆s` 的成员资格，由单点集的分类收尾。
<!--ja-->
record の二つの固定方程式は後続の段階への所属について語るため、本章では `sucV` 自身の場合分けが必要です。`sucV A` の元は、切り詰められた意味で、`A` の元であるか `A` と等しいかのいずれかであり、両方向の包含が成り立ちます。ライブラリの数項は `sucV` で後続を取るため、この場合分けによってライブラリと整列した任意の数項列が固定方程式を引き継げます。解析は `sucV A` を和と対の公理で一度展開し、第二の選言支、すなわち一元集合 `⁅ A ⁆s` への所属は、その分類で閉じます。
<!--/-->

<!--en-->
The analysis starts from a piece of the previous section that is worth extracting: membership of `x` in the singleton `⁅ A ⁆s` forces the path `x ≡ A`. This is the first half of the singleton's classification, recorded here as `singl≡`. The elimination principle `∈sucV-elim` then turns the case analysis into a usable form: given a proposition `P`, a proof of `P` from membership in `A`, a proof of `P` from equality with `A`, and a member of `sucV A`, it produces a proof of `P`. That `P` is required to be a proposition is exactly what licenses eliminating the truncated case analysis into it.
<!--zh-->
分析从上一节的一条事实出发，值得把它单独抽出：`x` 属于单点集 `⁅ A ⁆s` 强制路径 `x ≡ A`。这是单点集分类的前半，此处记为 `singl≡`。消去原则 `∈sucV-elim` 随后把分情形分析变成可用的形式：给定命题 `P`、由「`x` 属于 `A`」得 `P` 的证明、由「`x` 等于 `A`」得 `P` 的证明，以及 `sucV A` 的一个成员，它就给出 `P` 的证明。要求 `P` 是命题，恰好是把截断的分情形消入它的依据。
<!--ja-->
分析は前節の事実一つから始めます。これを取り出しておく価値があります。`x` が一元集合 `⁅ A ⁆s` に属すればパス `x ≡ A` が強制される、というものです。これは一元集合の分類の前半であり、ここでは `singl≡` として記録します。消去原理 `∈sucV-elim` はこの場合分けを使える形にします。命題 `P`、`x` が `A` の元である場合に `P` を与える証明、`x` が `A` と等しい場合に `P` を与える証明、そして `sucV A` の一つの元が与えられれば、`P` の証明を作る、というものです。`P` が命題であるという要求こそ、切り詰められた場合分けをそこへ消去する根拠です。
<!--/-->

```agda
private
  singl≡ : (A x : S) → ⟨ x ∈ₛ ⁅ A ⁆s ⟩ → x ≡ A
  singl≡ A x = SetPackage.classification (SingletonPackage A) x .fst

∈sucV-elim : {A x : S} {P : Type (ℓ-suc ℓ)} → isProp P → ⟨ x ∈ˢ sucV A ⟩
           → (⟨ x ∈ˢ A ⟩ → P) → (x ≡ A → P) → P
```

<!--en-->
Mathematically, `sucV A` is the union of the pair `⁅ A , ⁅ A ⁆s ⁆`, so a member of it is a member of one of the two components. The analysis therefore runs in two steps. The union axiom first produces, merely, a component `v` of the pair with `x` a member of `v`; the pairing axiom then splits membership of `v` in the pair into the truncated disjunction `v ≡ A` or `v ≡ ⁅ A ⁆s`. In the left branch, transporting `x ∈ v` along `v ≡ A` gives ordinary membership in `A`, exactly what the first premise expects.
<!--zh-->
数学上，`sucV A` 是配对 `⁅ A , ⁅ A ⁆s ⁆` 的并，所以它的成员是该对某个分量的成员。分析因此分两步。并公理先纯粹地给出配对的一个分量 `v`，且 `x` 是 `v` 的成员；配对公理再把「`v` 属于这对」分裂为截断的析取 `v ≡ A` 或 `v ≡ ⁅ A ⁆s`。左支中，沿 `v ≡ A` 传递 `x ∈ v` 即得 `A` 中的普通成员资格，恰是第一个前提所期望的。
<!--ja-->
数学的には、`sucV A` は対 `⁅ A , ⁅ A ⁆s ⁆` の和なので、その元はいずれかの成分の元です。分析は二段階で進みます。まず和の公理が、対のある成分 `v` と `x` が `v` の元であることを純粋に与えます。次に対の公理が、`v` のこの対への所属を、切り詰められた選言 `v ≡ A` か `v ≡ ⁅ A ⁆s` かへ分裂させます。左の分岐では、`v ≡ A` に沿って `x ∈ v` を輸送すれば `A` への通常の所属が得られ、これは第一の前提の期待するものです。
<!--/-->

```agda
∈sucV-elim {A} {x} pP x∈ kA k≡ =
  PT.rec pP
    (λ { (v , (v∈₂ , x∈v)) → PT.rec pP
      (λ { (Sum.inl v≡A) →
             kA (∈∈ₛ {a = x} {b = A} .snd (subst (λ w → ⟨ x ∈ₛ w ⟩) v≡A x∈v))
```

<!--en-->
In the right branch, transporting along `v ≡ ⁅ A ⁆s` yields membership in the singleton, and `singl≡` converts that into the path `x ≡ A`, which is what the second premise expects. Both truncated eliminations land in the proposition `P`, so they are legitimate, and the two cases together discharge the analysis. The first inclusion is also recorded on its own: `∈sucV-inl` states that a member of `A` is a member of `sucV A`.
<!--zh-->
右支中，沿 `v ≡ ⁅ A ⁆s` 传递得到单点集中的成员资格，`singl≡` 把它变成路径 `x ≡ A`，正是第二个前提所期望的。两次截断消去都落入命题 `P`，因而合法，两个情形合起来完成分析。第一个收纳也单独记录：`∈sucV-inl` 陈述 `A` 的成员是 `sucV A` 的成员。
<!--ja-->
右の分岐では、`v ≡ ⁅ A ⁆s` に沿った輸送で一元集合への所属が得られ、`singl≡` がそれをパス `x ≡ A` へ変えます。これは第二の前提の期待するものです。二度の切り詰めの消去はいずれも命題 `P` に着地するため正当であり、二つの場合が合わさって分析を完結させます。最初の包含も独立に記録されます。`∈sucV-inl` は、`A` の元が `sucV A` の元であることを述べます。
<!--/-->

```agda
         ; (Sum.inr v≡s) →
             k≡ (singl≡ A x (subst (λ w → ⟨ x ∈ₛ w ⟩) v≡s x∈v)) })
      (pairing-ax A ⁅ A ⁆s v .fst v∈₂) })
    (union-ax ⁅ A , ⁅ A ⁆s ⁆ x .fst (∈∈ₛ {a = x} {b = sucV A} .fst x∈))

∈sucV-inl : {A x : S} → ⟨ x ∈ˢ A ⟩ → ⟨ x ∈ˢ sucV A ⟩
```

<!--en-->
The proof of `∈sucV-inl` builds rather than analyzes: from the assumed membership of `x` in `A`, it assembles a witness for membership in the union. Inside the truncation, the component `A` of the pair is presented through the pairing axiom via the left disjunct with the reflexive path, and the membership of `x` in `A` is converted into the small form the union axiom consumes. The outer exchange then lifts the whole small-form witness to membership in `sucV A`.
<!--zh-->
`∈sucV-inl` 的证明是构造而非分析：从假设的「`x` 属于 `A`」出发，组装出属于并的见证。在截断内部，配对的分量 `A` 经配对公理以带自反路径的左析取支呈现；`x` 属于 `A` 的成员资格则转成并公理所消耗的小形式。外层交换再把整个小形式见证提升为 `sucV A` 中的成员资格。
<!--ja-->
`∈sucV-inl` の証明は構成であり、解析ではありません。仮定された `x` の `A` への所属から、和への所属の証人を組み立てます。切り詰めの内部では、対の成分 `A` が、対の公理を通して自反パス付きの左の選言支として提示され、`x` の `A` への所属は、和の公理が消費する小形式へ変換されます。外側の交換が、この小形式の証拠全体を `sucV A` への所属へ引き上げます。
<!--/-->

```agda
∈sucV-inl {A} {x} x∈A = ∈∈ₛ {a = x} {b = sucV A} .snd
  (union-ax ⁅ A , ⁅ A ⁆s ⁆ x .snd
    ∣ A , (pairing-ax A ⁅ A ⁆s A .snd ∣ Sum.inl refl ∣₁
         , ∈∈ₛ {a = x} {b = A} .fst x∈A) ∣₁)

self∈sucV : (a : S) → ⟨ a ∈ˢ sucV a ⟩
```

<!--en-->
The companion `self∈sucV` proves the second inclusion: every set `a` is a member of its own successor. The witness is now the other component `⁅ a ⁆s` of the pair, presented via the right disjunct; the fact that it contains `a` is the second half of the singleton classification applied to the reflexive path. Together the two lemmas give the content the pinning equations need: the members of `sucV A` are, merely, the members of `A` together with `A` itself.
<!--zh-->
伴随的 `self∈sucV` 证明第二个收纳：每个集合 `a` 属于它自己的后继。这次的见证是配对的另一分量 `⁅ a ⁆s`，经右析取支呈现；它包含 `a` 这一事实是单点集分类的后半应用于自反路径。两条引理合起来给出固定方程所需的内容：`sucV A` 的成员，仅仅是 `A` 的成员再加上 `A` 本身。
<!--ja-->
対応する `self∈sucV` は第二の包含、すなわち任意の集合 `a` が自分自身の後続に属することを示します。今度の証拠は対のもう一方の成分 `⁅ a ⁆s` を右の選言支として提示するもので、それが `a` を含むという事実は、一元集合の分類の後半を自反パスに適用したものです。二つの補題を合わせると、固定方程式に必要な内容が得られます。`sucV A` の元とは、切り詰められた意味で、`A` の元と `A` 自身にほかなりません。
<!--/-->

```agda
self∈sucV a = ∈∈ₛ {a = a} {b = sucV a} .snd
  (union-ax ⁅ a , ⁅ a ⁆s ⁆ a .snd
    ∣ ⁅ a ⁆s , (pairing-ax a ⁅ a ⁆s ⁅ a ⁆s .snd ∣ Sum.inr refl ∣₁
              , SetPackage.classification (SingletonPackage a) a .snd refl) ∣₁)
```

<!--en-->
The two pinning equations, for any chain aligned with the library's. The record asks that the zeroth numeral have no members and that the members of each successor numeral be exactly the members of the predecessor together with the predecessor itself. Both statements are about membership in the given chain, while the case analysis of the previous section speaks of membership in `sucV`; the alignment `q : a n ≡ # n` is the bridge, and every statement about membership in the chain transports along `q` to the corresponding statement about the library numerals. The module takes the chain and the alignment as parameters, so the same lemmas serve the model's chain and any other.
<!--zh-->
任意与库对齐的链的两条固定方程。record 要求：第零个数码没有成员；每个后继数码的成员恰为其前驱的成员加上前驱本身。这两条陈述都关乎给定链中的成员资格，而上一节的分情形分析谈的是 `sucV` 中的成员资格；对齐 `q : a n ≡ # n` 是桥梁，关于链中成员资格的陈述都可沿 `q` 搬运为关于库数码的相应陈述。该模块把链与对齐作为参数，因此同样的引理既服务模型的链，也服务任何其他链。
<!--ja-->
ライブラリと整列する任意の列に対する、二つの固定方程式です。レコードは、第 0 の数項が元を持たないこと、また各後続数項の元が前者の元に前者自身を加えたものにちょうど等しいことを要求します。どちらの主張も与えられた列への所属についてですが、前節の場合分けは `sucV` への所属について語ります。整列 `q : a n ≡ # n` がその橋渡しであり、列への所属についての主張は `q` に沿ってライブラリの数項についての対応する主張へ運べます。モジュールは列と整列をパラメータとして受け取るので、同じ補題がモデルの列にも他の列にも使えます。
<!--/-->

<!--en-->
The zero equation is the easier one. If `z` were a member of the chain's zeroth stage, transporting along `q zero` makes it a member of the library's empty set; after the exchange by `∈∈ₛ`, `∅-empty` refutes that membership in its small form, and the result is an inhabitant of the empty type. Note what is not claimed: no freestanding emptiness of the model's numeral is proved, only that membership in it implies a contradiction, which is all the pinning equation demands.
<!--zh-->
第零条方程较简单。若 `z` 是链的第零处的成员，沿 `q zero` 搬运便使它成为库空集的成员；经 `∈∈ₛ` 交换后，`∅-empty` 以小隶属形式驳斥它，结果是空类型的元素。注意并未主张什么：这里没有证明模型数码单独意义上的空性，只证明「属于它蕴含矛盾」，而固定方程要求的恰是这些。
<!--ja-->
第 0 の方程式のほうが簡単です。もし `z` が列の第 0 段階の元なら、`q zero` に沿って輸送すればライブラリの空集合の元になります。`∈∈ₛ` による交換を経て、`∅-empty` が小さな所属の形でそれを反駁し、結果は空の型の要素です。主張されない点にも注意してください。モデルの数項そのものの空性を証明するのではなく、そこへの所属が矛盾を導くことだけを示します。固定方程式が要求するのはまさにそれです。
<!--/-->

```agda
module NumPin (a : ℕ → S) (q : (n : ℕ) → a n ≡ # n) where
  pinZero : (z : S) → ⟨ z ∈ˢ a zero ⟩ → Empty.⊥
  pinZero z z∈ = ∅-empty z
    (∈∈ₛ {a = z} {b = ∅} .fst (subst (λ w → ⟨ z ∈ˢ w ⟩) (q zero) z∈))

  pinSuc : (n : ℕ) (z : S)
```

<!--en-->
The successor equation is a pair of conversions between membership in `a (suc n)` and the truncated disjunction of membership in `a n` with equality to it, which is the shape the record's field prescribes. The equality in the second disjunct is `≈ˢ`, the structure's equality, so the alignment paths apply to it directly. The propositionhood of the disjunction is supplied explicitly in the proof, since the eliminator of a truncated statement needs it.
<!--zh-->
后继方程是「属于 `a (suc n)`」与「属于 `a n` 或等于 `a n` 的截断析取」之间的一对转换，正是 record 字段规定的形状。第二个析取支中的相等是 `≈ˢ`，即结构的等词，所以对齐路径可直接作用于它。析取的命题性在证明中显式给出，因为截断陈述的消去器需要它。
<!--ja-->
後続の方程式は、`a (suc n)` への所属と、「`a n` への所属または `a n` と等しいこと」の切り詰められた選言との間の変換の対であり、これはレコードのフィールドが定める形です。第二の選言支での等しさは `≈ˢ`、つまり構造の等号なので、整列のパスを直接適用できます。選言の命題性は証明の中で明示的に供給されます。切り詰められた主張の消去子がそれを必要とするからです。
<!--/-->

```agda
         → (⟨ z ∈ˢ a (suc n) ⟩ → ⟨ (z ∈ˢ a n) ⊔ (z ≈ˢ a n) ⟩)
         × (⟨ (z ∈ˢ a n) ⊔ (z ≈ˢ a n) ⟩ → ⟨ z ∈ˢ a (suc n) ⟩)
  pinSuc n z = fwd , bwd
    where
    fwd : ⟨ z ∈ˢ a (suc n) ⟩ → ⟨ (z ∈ˢ a n) ⊔ (z ≈ˢ a n) ⟩
```

<!--en-->
Forward, the membership in the chain is first transported to membership in `# (suc n)`, and from there the `sucV` analysis applies, eliminating into the disjunction of the conclusion. In the first branch, membership in `# n` is transported back along the alignment at stage `n` to membership in `a n`, and the truncated disjunction is introduced with the left injection. In the second branch, the path from `z` to `# n` is composed with the reverse alignment to give a path from `z` to `a n`, taking the right injection. Both branches produce truncated witnesses, so the result remains a mere disjunction, never a decided case.
<!--zh-->
正向，先把链中的成员资格搬到 `# (suc n)` 的成员资格，从那里适用 `sucV` 分析，消入结论的析取。第一分支中，`# n` 中的成员资格沿第 `n` 处的对齐搬回 `a n` 中的成员资格，用左注入引入截断析取。第二分支中，`z` 到 `# n` 的路径与反向对齐复合，得到 `z` 到 `a n` 的路径，取右注入。两个分支都产生截断见证，因此结果仍是纯粹的析取，绝不是已判定的情形。
<!--ja-->
順方向では、まず列での所属を `# (suc n)` への所属へ輸送し、そこで `sucV` の分析が適用され、結論の選言へ消去されます。第一の枝では、`# n` での所属が段階 `n` での整列に沿って `a n` での所属へ運び戻され、左の注入で切り詰められた選言が導入されます。第二の枝では、`z` から `# n` へのパスが逆向きの整列と合成され、`z` から `a n` へのパスが得られ、右の注入を取ります。両枝とも切り詰められた証人を生むので、結果はあくまで純粋な選言であり、判定された場合ではありません。
<!--/-->

```agda
    fwd z∈ = ∈sucV-elim {A = # n} {x = z}
      (snd ((z ∈ˢ a n) ⊔ (z ≈ˢ a n)))
      (subst (λ w → ⟨ z ∈ˢ w ⟩) (q (suc n)) z∈)
      (λ z∈#n → ∣ Sum.inl (subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (q n)) z∈#n) ∣₁)
      (λ z≡#n → ∣ Sum.inr (z≡#n ∙ sym (q n)) ∣₁)
```

<!--en-->
Backward has two truncated cases to handle, so the eliminator runs into the membership proposition of `a (suc n)`. In the first case, the member of `a n` is transported to `# n`, the lemma `∈sucV-inl` puts it into the library successor, and the result is transported back along the alignment at the successor stage. The alignment is used in both directions at every step, which is why it was taken as a hypothesis for all `n` at once.
<!--zh-->
反向要处理两个截断情形，因此消去器进入 `a (suc n)` 的成员命题。第一情形中，`a n` 的成员被搬到 `# n`，引理 `∈sucV-inl` 把它放进库后继，再沿后继处的对齐搬回。对齐在每一步都被双向使用，这正是把它作为对所有 `n` 一并给出的假设的原因。
<!--ja-->
逆方向では二つの切り詰められた場合を扱うので、消去子は `a (suc n)` の所属の命題へ入ります。第一の場合、`a n` の元は `# n` へ運ばれ、補題 `∈sucV-inl` がそれをライブラリの後続に入れ、結果は後続の段階での整列に沿って運び戻されます。整列は各段階で両方向に使われます。これが、すべての `n` に対して一度に仮定として取られた理由です。
<!--/-->

```agda
    bwd : ⟨ (z ∈ˢ a n) ⊔ (z ≈ˢ a n) ⟩ → ⟨ z ∈ˢ a (suc n) ⟩
    bwd = PT.rec (snd (z ∈ˢ a (suc n)))
      (λ { (Sum.inl z∈n) → subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (q (suc n)))
             (∈sucV-inl {A = # n} (subst (λ w → ⟨ z ∈ˢ w ⟩) (q n) z∈n))
         ; (Sum.inr z≡n) → subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (q (suc n)))
```

<!--en-->
The second case handles the right disjunct, and this is where the fact that a successor contains itself enters. The hypothesis is a path `z ≡ a n` from `z` to the model's predecessor; composing it with the alignment `q n` yields a path `z ≡ # n`. That path transports the stored fact `self∈sucV (# n)`, that `# n` lies in its own library successor, into the statement that `z` lies in `sucV (# n)`, and the final transport along the alignment at the successor stage returns to the chain. Together the two branches deliver the full backward conversion, completing the successor pinning equation for every aligned chain.
<!--zh-->
第二情形处理右析取支，这里正是「后继包含自身」这条事实的用武之地。假设是从 `z` 到模型前驱的路径 `z ≡ a n`；把它与对齐 `q n` 复合，得到路径 `z ≡ # n`。该路径把已存的事实 `self∈sucV (# n)`，即 `# n` 属于自己的库后继，搬运为「`z` 属于 `sucV (# n)`」的陈述，最后沿后继处的对齐搬运回到链上。两个分支合起来给出完整的反向转换，为每条对齐的链完成后继固定方程。
<!--ja-->
第二の場合は右の選言支を扱い、ここで「後続は自分自身を含む」という事実が働きます。仮定は `z` からモデルの前者へのパス `z ≡ a n` であり、整列 `q n` との合成によりパス `z ≡ # n` になります。このパスが、保持しておいた事実 `self∈sucV (# n)`、すなわち `# n` が自分自身のライブラリの後続に属することを、「`z` は `sucV (# n)` に属する」という主張へ輸送し、最後は後続の段階での整列に沿う輸送で列に戻ります。二つの枝を合わせて逆方向の変換が完成し、整列した任意の列に対して後続の固定方程式が果たされます。
<!--/-->

```agda
             (subst (λ w → ⟨ w ∈ˢ sucV (# n) ⟩) (sym (z≡n ∙ q n))
               (self∈sucV (# n))) })
```

<!--en-->
## Assumptions for the remaining axioms

Two fields remain, full separation and power set, and they pose two different smallness problems. Full separation must turn an arbitrary satisfaction proposition `(y ∷ []) ⊨ φ`, which lives in `Type (ℓ-suc ℓ)`, into a small one, and no Δ₀ witness is available to do this by hand; what is needed is the `resizing` component of impredicativity, which produces a small representative for each such proposition pointwise, so that the smallness adapter `separateFromSmall` applies. Power set poses the other problem: a candidate subset of `a` is a family of membership propositions indexed by `⟪ a ⟫`, and to form a set from it, each proposition must be encoded in one fixed small type. The `hPropSmallness` component supplies exactly this: a small type `Ω'` equivalent to all of `hProp ℓ`, serving as a classifier for propositions. Neither construction uses the whole `Impredicativity` packing; each consumes one of its two components, and the later assembly takes the packing as a parameter, deriving it in the classical case through `lem→impredicativity`.

## Power set

The power set is the one construction the library's own header disclaims, and the small classifier is what builds it. A candidate subset of `a` is described by a characteristic function `⟪ a ⟫ → Ω'` into the classifier's small carrier; decoding each value `χ m` yields a proposition on the index `m`, and the elements presented by indices where that proposition holds are gathered into a set by `sett`. The proof establishes two inclusions: everything the function selects lies in the given subset, and every member of the subset is selected, the second direction using the round trip decode after encode on propositions, together with extensionality.
<!--zh-->
## 其余公理所需的假设

还剩两个字段，全分离与幂集，它们提出的是两个不同的小性问题。全分离要把任意的满足命题 `(y ∷ []) ⊨ φ` (住在 `Type (ℓ-suc ℓ)`) 变小，而没有 Δ₀ 见证可以徒手完成；所需的是非直谓性中的 `resizing` 分量，它逐点地为每个这样的命题给出小代表，从而使小性适配器 `separateFromSmall` 得以应用。幂集提出的是另一类问题：`a` 的候选子集是以 `⟪ a ⟫` 为索引的成员命题族，要从它造出集合，每条命题必须编码进一个固定的小类型。`hPropSmallness` 分量恰好供给这一点：一个与整个 `hProp ℓ` 等价的小类型 `Ω'`，充当命题的分类器。两个构造都不使用整个 `Impredicativity` 打包；各自只消耗它的一个分量，后面的装配把该打包作为参数，经典情形经 `lem→impredicativity` 得到。

## 幂集

幂集是库文件头明确声明不提供的那一件构造，而小分类器正是构造它的材料。`a` 的候选子集由进入分类器小载体的特征函数 `⟪ a ⟫ → Ω'` 描述；解码每个值 `χ m` 便得到索引 `m` 上的命题，凡该命题成立的索引所呈现的元素由 `sett` 收集成集合。证明建立两个收纳：函数选中的都落在给定子集内，子集的每个成员都被选中；第二个方向使用命题上「先编码再解码」的往返，再由外延性收尾。
<!--ja-->
## 残る公理に必要な仮定

残る欄は完全な分出と冪集合の二つですが、両者は異なる小ささの問題を提示します。完全な分出は、`Type (ℓ-suc ℓ)` に住む任意の充足命題 `(y ∷ []) ⊨ φ` を小さくしなければなりませんが、手作業でこれを行う Δ₀ の証人はありません。必要なのは非可述性の `resizing` の成分で、そのような各命題に点ごとに小さな代表を与え、小ささの適合装置 `separateFromSmall` を適用できるようにします。冪集合が提示するのは別の問題です。`a` の候補となる部分集合は `⟪ a ⟫` で添字付けられた所属の命題の族であり、そこから集合を作るには、各命題を一つの固定された小さな型へ符号化しなければなりません。`hPropSmallness` の成分はまさにこれを供給します。すなわち `hProp ℓ` 全体と同値な小さな型 `Ω'` で、命題の分類子として働きます。どちらの構成も `Impredicativity` のパッキング全体を使うのではなく、その二つの成分の一方だけを消費します。後の組み立てはパッキングをパラメータとして受け取り、古典的な場合は `lem→impredicativity` から導かれます。

## 冪集合

冪集合は、ライブラリのヘッダ自身が提供しないと明言する唯一の構成であり、小分類子こそがそれを作る材料です。`a` の候補となる部分集合は、分類子の小さな台への特性関数 `⟪ a ⟫ → Ω'` で記述します。各値 `χ m` を復号すれば添字 `m` 上の命題が得られ、その命題が成り立つ添字が呈示する要素は `sett` で一つの集合に集められます。証明は二つの包含を確立します。関数が選んだものはすべて与えられた部分集合に含まれ、部分集合のすべての元が選ばれる、というものです。第二の方向は、命題に対する復号してから符号化する往復と、外延性を用います。
<!--/-->

<!--en-->
The power-set construction assumes exactly one component of the packing: a witness `sΩ` of `HPropSmallness ℓ`, that is, a small type `Ω'` in `Type ℓ` together with an equivalence onto `hProp ℓ`. Nothing else is assumed. From the equivalence two readings are extracted. The forward map `decode` turns a small truth value into an ordinary proposition packaged in `hProp ℓ`; this is the direction that lets a characteristic function be read as a predicate on indices.
<!--zh-->
幂集构造恰以该打包的一个成分为前提：`HPropSmallness ℓ` 的见证 `sΩ`，即 `Type ℓ` 中的小类型 `Ω'` 连同到 `hProp ℓ` 的等价。此外不假设任何东西。由该等价提取两个读法。正向映射 `decode` 把小真值变成打包在 `hProp ℓ` 中的普通命题；正是这个方向使特征函数可被读作索引上的谓词。
<!--ja-->
冪集合の構成は、パッキングの成分のうちちょうど一つを前提とします。すなわち `HPropSmallness ℓ` の証人 `sΩ`、つまり `Type ℓ` の小さな型 `Ω'` と `hProp ℓ` 全体への同値です。それ以外は何も仮定しません。この同値から二つの読み方を取り出します。順方向の写像 `decode` は小さな真理値を、`hProp ℓ` に包装された通常の命題へ変えます。特性関数を添字上の述語として読めるのはこの方向です。
<!--/-->

```agda
module Power (sΩ : HPropSmallness ℓ) where

  private
    decode : sΩ .fst → hProp ℓ
    decode = equivFun (sΩ .snd)

    encode : hProp ℓ → sΩ .fst
```

<!--en-->
The backward map `encode` sends an `hProp ℓ` proposition into the small carrier, and the round trip `decode∘encode` is the `secEq` leg of the equivalence: decoding the encoding of a proposition returns a path to exactly that proposition. With the classifier in place, the realizing family `F` is direct. For a characteristic function `χ`, take the pairs of an index `m` with a proof that `decode (χ m)` holds, and form the `sett` of the elements they present. The selected members are exactly those whose encoded truth value decodes to a proposition with a proof.
<!--zh-->
反向映射 `encode` 把 `hProp ℓ` 的命题送入小载体，而往返 `decode∘encode` 是等价的 `secEq` 一侧：把命题的编码再解码，得到指向恰该命题的路径。分类器就位后，实现族 `F` 是直接的：对特征函数 `χ`，取「索引 `m` 加上 `decode (χ m)` 成立的证明」的对，把所呈现的元素作成 `sett`。被选中的成员恰是其编码真值解码出带证明命题的那些。
<!--ja-->
逆方向の写像 `encode` は `hProp ℓ` の命題を小さな台へ送り、往復 `decode∘encode` は同値の `secEq` の側です。命題の符号を復号すれば、もとの命題そのものへのパスが返ります。分類子が揃うと、実現する族 `F` は直接的です。特性関数 `χ` に対し、添字 `m` と「`decode (χ m)` が成り立つ」ことの証明の対を集め、それが呈示する要素の `sett` を作ります。選ばれる元は、符号化された真理値を復号すると証明付きの命題になるものにちょうど一致します。
<!--/-->

```agda
    encode = invEq (sΩ .snd)

    decode∘encode : (P : hProp ℓ) → decode (encode P) ≡ P
    decode∘encode = secEq (sΩ .snd)

    F : (a : S) → (⟪ a ⟫ → sΩ .fst) → S
    F a χ = sett (Σ[ m ∈ ⟪ a ⟫ ] ⟨ decode (χ m) ⟩) (λ p → ⟪ a ⟫↪ (p .fst))
```

<!--en-->
The power set operation is itself a `sett`: the index type is the function type from `⟪ a ⟫` into the small carrier `Ω'`, and the family realizes each characteristic function as the set selected above. Membership in `𝒫V a` is therefore, merely, membership in one of the realized sets: a member arrives as a truncated pair of a characteristic function and a path from the set it selects to `x`. The forward direction of the specification shows that such an `x` is a subset of `a` in the ambient sense, the inclusion `⊆` of the hierarchy library rather than the structure's relation `⊆ˢ`; the passage between the two is kept separate and handled at the end.
<!--zh-->
幂集运算本身就是一次 `sett`：索引类型是从 `⟪ a ⟫` 到小载体 `Ω'` 的函数类型，族把每个特征函数实现为上文选出的集合。于是属于 `𝒫V a` 仅仅是属于某个实现的集合：成员以「特征函数加一条从它所选集合到 `x` 的路径」的截断对出现。规格的正向表明这样的 `x` 在环境意义下是 `a` 的子集，即层级库的包含 `⊆`，而非结构的关系 `⊆ˢ`；两者的换算被分开处理，留到最后。
<!--ja-->
冪集合の操作そのものも `sett` です。添字型は `⟪ a ⟫` から小さな台 `Ω'` への関数型であり、族が各特性関数を上で選ばれた集合として実現します。したがって `𝒫V a` への所属とは、切り詰められた意味で、実現された集合のどれかへの所属です。すなわち、特性関数と、それが選ぶ集合から `x` へのパスの切り詰められた対として元が現れます。仕様の順方向は、そのような `x` が周辺の意味で `a` の部分集合であること、つまり階層のライブラリの包含 `⊆` であって構造の関係 `⊆ˢ` ではないことを示します。両者の仲立ちには別の段階を設け、最後に扱います。
<!--/-->

```agda

  𝒫V : S → S
  𝒫V a = sett (⟪ a ⟫ → sΩ .fst) (F a)

  private
    fwd : (a x : S) → ⟨ x ∈ˢ 𝒫V a ⟩ → ⟨ x ⊆ a ⟩
    fwd a x = PT.rec ((x ⊆ a) .snd) λ { (χ , p) y y∈ₛx →
```

<!--en-->
The proof of `x ⊆ a` proceeds member by member, first eliminating the truncated membership in the power set. After transporting the membership of `y` in `x` back along the presenting path, it becomes small membership in the selected set `F a χ`; converting that through `∈∈ₛ` yields a presenting fiber, an index `m` together with a proof that `decode (χ m)` holds and a path identifying `y` with the presented element `⟪ a ⟫↪ m`.
<!--zh-->
`x ⊆ a` 的证明逐成员进行，先消去属于幂集的截断成员资格。沿呈现路径把 `y` 在 `x` 中的成员资格搬回后，它变成在所选集合 `F a χ` 中的小隶属；经 `∈∈ₛ` 转换后得到呈现纤维：索引 `m` 加上 `decode (χ m)` 成立的证明，以及一条把 `y` 与被呈现元素 `⟪ a ⟫↪ m` 等同的路径。
<!--ja-->
`x ⊆ a` の証明は元ごとに進み、まず冪集合への切り詰められた所属を消去します。`y` の `x` への所属を呈示するパスに沿って運び戻すと、それは選ばれた集合 `F a χ` への小さな所属になり、`∈∈ₛ` で変換すると呈示するファイバーが得られます。すなわち添字 `m` と、`decode (χ m)` が成り立つことの証明、さらに `y` を呈示された要素 `⟪ a ⟫↪ m` と同一視するパスです。
<!--/-->

```agda
      PT.rec ((y ∈ₛ a) .snd)
             (λ { ((m , _) , q) → subst (λ v → ⟨ v ∈ₛ a ⟩) q (∈ₛ⟪ a ⟫↪ m) })
             (∈∈ₛ {a = y} {b = F a χ} .snd
               (subst (λ v → ⟨ y ∈ₛ v ⟩) (sym p) y∈ₛx)) }

    bwd : (a x : S) → ⟨ x ⊆ a ⟩ → ⟨ x ∈ˢ 𝒫V a ⟩
```

<!--en-->
The remaining work is to turn that fiber into membership of `y` in `a`, which the transport along the path accomplishes, since the presented elements of `a` are members of `a` by construction. The target stays proposition-valued throughout, so both truncation eliminations are legitimate. Thus any member of the power set, however it is presented, collects only members of `a`.

Backward builds the witness for membership in the power set, and it needs no choice. The characteristic function `χₓ` is recovered explicitly: the index `m` is sent to the encoding `encode` of the small membership of the presented element `⟪ a ⟫↪ m` in `x`, a function because the small membership fiber of the embedding is untruncated. The truncated pair then packages `χₓ` with the assertion, proved by extensionality from the two inclusions `s1` and `s2`, that the set `χₓ` selects equals `x`.
<!--zh-->
剩下的工作是把该纤维变成 `y` 在 `a` 中的成员资格，沿路径的搬运正好完成这一点，因为 `a` 的被呈现元素按构造就是 `a` 的成员。目标始终取命题值，所以两次截断消去都是合法的。于是幂集的任何成员，无论怎样呈现，都只收集 `a` 的成员。

反向为属于幂集构造见证，且无需选择。特征函数 `χₓ` 被显式回收：索引 `m` 被送到被呈现元素 `⟪ a ⟫↪ m` 在 `x` 中的小隶属的编码 `encode`。这是函数操作而非选择，因为嵌入的小隶属纤维不加截断。截断的对随后把 `χₓ` 与「`χₓ` 所选的集合等于 `x`」的断言打包，该断言由两个收纳 `s1`、`s2` 经外延性建立。
<!--ja-->
残りの作業は、そのファイバーを `y` の `a` への所属に変えることで、パスに沿う輸送がこれを果たします。`a` の呈示された要素は構成によって `a` の元だからです。目標は終始命題値のままなので、二つの切り詰めの消去はいずれも正当です。こうして冪集合の元は、どのように呈示されようと、`a` の元だけを集めます。

逆方向は冪集合への所属の証人を組み立てますが、選択は要りません。特性関数 `χₓ` は明示的に取り戻されます。添字 `m` は、呈示された要素 `⟪ a ⟫↪ m` の `x` における小さな所属の符号 `encode` へ送られます。これは関数であって選択ではありません。埋め込みの小さな所属のファイバーが切り詰められていないからです。切り詰められた対は、`χₓ` と「`χₓ` が選ぶ集合が `x` に等しい」という主張をまとめます。その主張は二つの包含 `s1`、`s2` から外延性によって確立されます。
<!--/-->

```agda
    bwd a x sub = ∣ χₓ , extensionality (F a χₓ) x (s1 , s2) ∣₁
      where
      χₓ : ⟪ a ⟫ → sΩ .fst
      χₓ m = encode (⟪ a ⟫↪ m ∈ₛ x)
      s1 : ⟨ F a χₓ ⊆ x ⟩
```

<!--en-->
The first inclusion shows that the set selected by `χₓ` adds nothing beyond `x`. A small member of `F a χₓ` carries an index `m`, a proof that `decode (χₓ m)` holds, and a presenting path. Since `χₓ m` was defined as the encoding of the membership `⟪ a ⟫↪ m ∈ₛ x`, the round trip `decode∘encode` rewrites the decoded proof back into exactly that membership, and the presenting path transports it onto `y`. So every member of the selected set is a member of `x`.
<!--zh-->
第一个收纳表明 `χₓ` 所选的集合没有超出 `x` 的东西。`F a χₓ` 的小成员带有索引 `m`、`decode (χₓ m)` 成立的证明，以及一条呈现路径。由于 `χₓ m` 本就定义为成员资格 `⟪ a ⟫↪ m ∈ₛ x` 的编码，往返 `decode∘encode` 把解码后的证明改写回恰是该成员资格，呈现路径再把它搬运到 `y` 上。于是所选集合的每个成员都是 `x` 的成员。
<!--ja-->
第一の包含は、`χₓ` が選ぶ集合が `x` を超えるものを何も加えないことを示します。`F a χₓ` の小さな元は、添字 `m`、`decode (χₓ m)` が成り立つことの証明、そして呈示するパスを伴います。`χₓ m` はもともと所属 `⟪ a ⟫↪ m ∈ₛ x` の符号として定義されているので、往復 `decode∘encode` が復号された証明をまさにその所属へ書き戻し、呈示するパスがそれを `y` の上へ運びます。したがって選ばれた集合のすべての元は `x` の元です。
<!--/-->

```agda
      s1 y y∈ₛF = PT.rec ((y ∈ₛ x) .snd)
        (λ { ((m , h) , q) →
          subst (λ v → ⟨ v ∈ₛ x ⟩) q
            (subst ⟨_⟩ (decode∘encode (⟪ a ⟫↪ m ∈ₛ x)) h) })
        (∈∈ₛ {a = y} {b = F a χₓ} .snd y∈ₛF)
```

<!--en-->
The second inclusion must go the other way: from an arbitrary member `y` of `x`, produce a small member of `F a χₓ`. The inclusion hypothesis `sub` first gives a presenting fiber for `y` in `a`, and its second component certifies that the presented element and `y` have the same members. The embedding's presentation is used in both directions here, so nothing needs to be chosen: the fiber is untruncated data, and the path `q` extracting `⟪ a ⟫↪ m₀ ≡ y` will be available as an ordinary term.
<!--zh-->
第二个收纳要反向进行：从 `x` 的任意成员 `y`，造出 `F a χₓ` 的一个小成员。收纳前提 `sub` 先给出 `y` 在 `a` 中的呈现纤维，其第二分量证明被呈现元素与 `y` 有相同的成员。这里双向使用嵌入的呈现，因此无需选取任何东西：纤维是不加截断的数据，抽出 `⟪ a ⟫↪ m₀ ≡ y` 的路径 `q` 将作为普通项可用。
<!--ja-->
第二の包含は逆向きに進めます。`x` の任意の元 `y` から、`F a χₓ` の小さな元を作るのです。包含の仮定 `sub` はまず `a` における `y` の呈示するファイバーを与え、その第二成分は、呈示された要素と `y` が同じ元を持つことを証明します。ここでは埋め込みの提示を両方向で使うので、何も選ぶ必要はありません。ファイバーは切り詰められていないデータであり、`⟪ a ⟫↪ m₀ ≡ y` を取り出すパス `q` は普通の項として利用できます。
<!--/-->

```agda
      s2 : ⟨ x ⊆ F a χₓ ⟩
      s2 y y∈ₛx = ∈∈ₛ {a = y} {b = F a χₓ} .fst ∣ (m₀ , h) , q ∣₁
        where
        m₀ = sub y y∈ₛx .fst
        q : ⟪ a ⟫↪ m₀ ≡ y
```

<!--en-->
The path `q` is obtained by applying `identityPrinciple` to the equal-members data of the inclusion hypothesis, so the presented element `⟪ a ⟫↪ m₀` equals `y`. Transporting the membership of `y` in `x` backwards along `q` lands it at the presented element, and that is precisely the proposition that `decode (χₓ m₀)` decodes to, by the round trip again: `χₓ m₀` was defined as the encoding of exactly this membership. So the pair `(m₀ , h)` of the index with the transported proof inhabits the type defining `F a χₓ`, and it witnesses `y` in the selected set. With both inclusions in place, `power-spec` composes this equivalence with the pointwise exchange between the ambient inclusion `⊆` and the structure's subset relation `⊆ˢ`, giving the field `hasPower` a set whose membership is, as truth values, the subset relation the record states.
<!--zh-->
路径 `q` 由对收纳前提的等成员数据应用 `identityPrinciple` 得到，于是被呈现元素 `⟪ a ⟫↪ m₀` 等于 `y`。把 `y` 在 `x` 中的成员资格沿 `q` 反向搬运，落到被呈现元素上；由往返，这恰是 `decode (χₓ m₀)` 解码出的命题：`χₓ m₀` 本就定义为恰好这个成员资格的编码。于是索引与搬运后证明构成的对 `(m₀ , h)` 居于定义 `F a χₓ` 的类型中，见证 `y` 在所选集合里。两个收纳就位后，`power-spec` 把这条等价与「环境包含 `⊆` 与结构的子集关系 `⊆ˢ` 之间逐点交换」复合，为字段 `hasPower` 给出一个集合，其隶属作为真值等于 record 所陈述的子集关系。
<!--ja-->
パス `q` は、包含の仮定の「元が同じ」というデータに `identityPrinciple` を適用して得られ、呈示された要素 `⟪ a ⟫↪ m₀` が `y` に等しいことが分かります。`x` での `y` の所属を `q` の逆向きに沿って運ぶと呈示された要素に着地し、これが往復によって、まさに `decode (χₓ m₀)` が復号する命題です。`χₓ m₀` はもともとこの所属の符号として定義されていたからです。よって添字と運ばれた証明の対 `(m₀ , h)` は `F a χₓ` を定める型の要素となり、選ばれた集合への `y` の所属の証人になります。両包含が揃うと、`power-spec` はこの同値を、周辺の包含 `⊆` と構造の部分集合の関係 `⊆ˢ` との各点の交換と合成し、欄 `hasPower` に、その所属が真理値としてレコードの述べる部分集合の関係に等しい集合を与えます。
<!--/-->

```agda
        q = equivFun identityPrinciple (sub y y∈ₛx .snd)
        h : ⟨ decode (χₓ m₀) ⟩
        h = subst ⟨_⟩ (sym (decode∘encode (⟪ a ⟫↪ m₀ ∈ₛ x)))
                  (subst (λ v → ⟨ v ∈ₛ x ⟩) (sym q) y∈ₛx)

  power-spec : (a x : S) → (x ∈ˢ 𝒫V a) ≡ (x ⊆ˢ a)
```

<!--en-->
The specification `power-spec` composes two equalities of truth values. The first is the equivalence just proved: membership in `𝒫V a` equals the ambient inclusion `x ⊆ a`, which quantifies over actual members and is not truncated. The second converts the ambient inclusion into the structure's own subset relation `x ⊆ˢ a`, stated through the structure's membership `∈ˢ`: given a function sending each ordinary member of `x` to an ordinary member of `a`, the two directions of `∈∈ₛ` exchange the membership notations pointwise in both directions. The composite is the power-set field's data: a set `𝒫V a` whose membership, as a truth value, is exactly the subset relation the record states. Note where each smallness input entered: separation consumed `resizing` pointwise, while the power set was built from `hPropSmallness` alone.
<!--zh-->
规格 `power-spec` 复合两个真值等式。第一个是刚证的主等价：属于 `𝒫V a` 等于环境意义下的包含 `x ⊆ a`，后者量化于实际成员之上，不加截断。第二个把环境包含转换成结构自己的子集关系 `x ⊆ˢ a`，它经由结构的成员关系 `∈ˢ` 陈述：给定把 `x` 的每个普通成员送到 `a` 的普通成员的函数，`∈∈ₛ` 的两个方向逐点互换两种隶属记号。复合所得正是幂集字段收到的数据：集合 `𝒫V a` 的隶属作为真值恰是 record 所述的子集关系。也请注意各小性输入进入之处：分离逐点消耗 `resizing`，而幂集仅由 `hPropSmallness` 构成。
<!--ja-->
仕様 `power-spec` は二つの真理値の等式を合成します。一つ目は今示した本質的な同値、すなわち `𝒫V a` への所属と、実際の元の上で量化され切り詰められていない包含 `x ⊆ a` との一致です。二つ目は、その包含を構造自身の部分集合の関係 `x ⊆ˢ a`、つまり構造の所属 `∈ˢ` を通して述べた形へ変換します。`x` の各通常の元を `a` の通常の元へ送る関数が与えられれば、`∈∈ₛ` の両方向が二つの所属の記法を各点で取り替えます。その合成こそ、冪集合のフィールドが受け取るデータです。集合 `𝒫V a` の所属が、真理値として、record の述べる部分集合の関係にちょうど等しいということです。それぞれの小ささの入力が入った場所にも注意してください。分出は点ごとに `resizing` を消費し、冪集合は `hPropSmallness` だけで組み立てられました。
<!--/-->

```agda
  power-spec a x =
    ⇔toPath {P = x ∈ˢ 𝒫V a} {Q = x ⊆ a} (fwd a x) (bwd a x)
    ∙ ⇔toPath {P = x ⊆ a} {Q = x ⊆ˢ a}
      (λ s y y∈x → ∈∈ₛ {a = y} {b = a} .snd (s y (∈∈ₛ {a = y} {b = x} .fst y∈x)))
      (λ f y y∈ₛx → ∈∈ₛ {a = y} {b = a} .fst (f y (∈∈ₛ {a = y} {b = x} .snd y∈ₛx)))
```

<!--en-->
## Establishing V ⊨ ZF

Every field of the model record now has its witness, and this section assembles them into a single mathematical theorem: the cumulative hierarchy satisfies ZF. The axioms group by how they were obtained. Empty set, pairing, and union are the stock sets converted at the start of the chapter. Full separation and power set are the two smallness results, each consuming one component of the impredicativity packing: separation uses `resizing` to make each satisfaction proposition small so that `separateFromSmall` applies, and power set uses the small classifier alone. Replacement is the image built from untruncated fibers, and infinity is the library's `ω` together with the numeral alignment. What remains is a packaging step with one genuine mathematical input. A field of `isZFModel` asks for `isContr (SetOf Q)`: a realizing set together with a contraction of all realizers to it, and extensionality supplies exactly that contraction, via `setOf-unique`. The theorem `V⊨ZF-impredicative` assumes the packing `Impredicativity ℓ`; the theorem `V⊨ZF` assumes instead `LEM (ℓ-suc ℓ)` and derives the packing through `lem→impredicativity`.
<!--zh-->
## 证明 V ⊨ ZF

模型 record 的每个字段如今都有了见证；本节把它们组装成单个数学定理：累积层级满足 ZF。公理按其来源分组。空集、配对与并是章首转换过的所需的基本集合。全分离与幂集是两个小性结果，各自消耗非直谓性打包的一个分量：分离用 `resizing` 使每个满足命题变小，从而 `separateFromSmall` 得以应用；幂集只用小分类器。替换是由不加截断的纤维造出的像；无穷是库中的 `ω` 连同数码对齐。剩下的是一步打包，但其中有一个真正的数学输入：`isZFModel` 的每个字段要求 `isContr (SetOf Q)`，即实现集合连同把一切实现者收缩到它的紧缩，而外延性经 `setOf-unique` 恰好给出这个紧缩。定理 `V⊨ZF-impredicative` 假设打包 `Impredicativity ℓ`；定理 `V⊨ZF` 改为假设 `LEM (ℓ-suc ℓ)`，并经 `lem→impredicativity` 导出该打包。
<!--ja-->
## V ⊨ ZF の証明

モデルの record の各フィールドにはすでに証拠が揃っており、この節はそれらを一つの数学的定理へ組み立てます。累積階層は ZF を満たす、という定理です。公理はその導出の仕方ごとに分類できます。空集合、対、和集合は章の冒頭で変換した基本的な集合です。完全な分出と冪集合は二つの小ささの結果で、それぞれ非可述性のパッキングの成分を一つずつ消費します。分出は `resizing` で各充足命題を小さくして `separateFromSmall` を適用できようにし、冪集合は小分類子だけを使います。置換は切り詰められていないファイバーから作った像であり、無限はライブラリの `ω` と数項の整列です。残るのは梱包の一段階ですが、そこには本物の数学的入力が一つあります。`isZFModel` の各フィールドは `isContr (SetOf Q)`、すなわち実現する集合と、すべての実現者をそこへ収縮させるデータを要求します。外延性がまさにその収縮を `setOf-unique` を通して与えます。定理 `V⊨ZF-impredicative` はパッキング `Impredicativity ℓ` を仮定し、定理 `V⊨ZF` は代わりに `LEM (ℓ-suc ℓ)` を仮定して、`lem→impredicativity` によりパッキングを導きます。
<!--/-->

<!--en-->
The assembly takes the packing `Impredicativity ℓ` as a parameter, and its two fields feed the two smallness constructions separately: `hPropSmallness` goes to the power-set construction of the previous section, which uses the classifier alone, and `resizing` is what separation uses. Full separation is stated directly: given a set `a` and a formula `φ` with one free-variable slot, produce a set `s` such that, for every `y`, the truth value `y ∈ˢ s` is the path equal to the conjunction of `y ∈ˢ a` and the satisfaction of `φ` at the one-point environment `y ∷ []`. This is precisely the shape of the separation specification the model record demands.
<!--zh-->
组装以打包 `Impredicativity ℓ` 为参数，其两个字段分别供给两个小性构造：`hPropSmallness` 交给上一节的幂集构造，那里只用分类器；`resizing` 则是分离所用的。全分离直接陈述：给定集合 `a` 与带一个自由变元槽的公式 `φ`，给出集合 `s`，使得对每个 `y`，真值 `y ∈ˢ s` 按路径等于「`y ∈ˢ a`」与「`φ` 在单元环境 `y ∷ []` 下满足」的合取。这正是模型 record 所要求分离规格的形状。
<!--ja-->
組み立てはパッキング `Impredicativity ℓ` をパラメータとして受け、その二つのフィールドは二つの小ささの構成に別々に供給されます。`hPropSmallness` は前節の冪集合の構成に渡され、そこでは分類子だけが使われます。`resizing` は分出で使うものです。完全な分出は直接に述べられます。集合 `a` と自由変数の枠を一つ持つ論理式 `φ` が与えられたとき、各 `y` について真理値 `y ∈ˢ s` が「`y ∈ˢ a`」と「一点環境 `y ∷ []` での `φ` の充足」の連言にパスとして等しい集合 `s` を作ります。これはモデルの record が要求する分出の仕様の形そのものです。
<!--/-->

```agda
module VModel (imp : Impredicativity ℓ) where
  open Impredicativity imp
  open Power hPropSmallness public

  separateFull : (a : S) (φ : Formula S 1)
               → Σ[ s ∈ S ] (∀ y → (y ∈ˢ s) ≡ ((y ∈ˢ a) ⊓ ((y ∷ []) ⊨ φ)))
```

<!--en-->
Separation is one application of the adapter from the smallness chapter. `separateFromSmall` takes a predicate `P : S → hProp (ℓ-suc ℓ)` on `a`, a smallness witness for each value, and returns a set `s` with the path specification `y ∈ˢ s ≡ (y ∈ˢ a) ⊓ P y`. Here the predicate is `λ y → (y ∷ []) ⊨ φ`, the satisfaction of `φ` at each one-point environment, and its smallness at each point is `resizing` applied there. No hypothesis on the shape of `φ` is needed: resizing assigns a small representative to every satisfaction proposition, whatever formula produces it. With `separateFull` in hand, the theorem `V⊨ZF-impredicative` of type `isZFModel` can be assembled from the witnesses already proved.
<!--zh-->
分离是小性一章的适配器的一次应用。`separateFromSmall` 取 `a` 上的谓词 `P : S → hProp (ℓ-suc ℓ)` 与每个取值的小性见证，返回带路径规格 `y ∈ˢ s ≡ (y ∈ˢ a) ⊓ P y` 的集合 `s`。这里的谓词是 `λ y → (y ∷ []) ⊨ φ`，即 `φ` 在每个单元环境下的满足；其在各点的小性就是在该点应用的 `resizing`。对 `φ` 的形状无需任何前提：无论公式是什么，降层都为每个满足命题指派一个小代表。有了 `separateFull`，便可从已证的见证组装出类型为 `isZFModel` 的定理 `V⊨ZF-impredicative`。
<!--ja-->
分出は、小ささの章の適合装置の一度の適用です。`separateFromSmall` は、`a` の上の述語 `P : S → hProp (ℓ-suc ℓ)` と各値への小ささの証明を受け取り、パスの仕様 `y ∈ˢ s ≡ (y ∈ˢ a) ⊓ P y` をもつ集合 `s` を返します。ここでの述語は `λ y → (y ∷ []) ⊨ φ`、つまり各一点環境での `φ` の充足であり、各点での小ささはそこで適用される `resizing` です。`φ` の形状についての前提は一切要りません。どのような論理式から生じたものであれ、リサイズは各充足命題に小さな代表を割り当てます。`separateFull` が揃えば、すでに示した証拠から型 `isZFModel` の定理 `V⊨ZF-impredicative` を組み立てられます。
<!--/-->

```agda
  separateFull a φ =
    separateFromSmall a (λ y → (y ∷ []) ⊨ φ) (λ y → resizing ((y ∷ []) ⊨ φ))

  V⊨ZF-impredicative : isZFModel
  V⊨ZF-impredicative = record
    { extensional    = extensionalV
```

<!--en-->
The first group of entries reuses the chapter's opening conversions. For the empty set, the pair, and the union, the explicit realizer is the library set `∅`, `⁅ a , b ⁆`, or `⋃ a`, together with the specification proved there; the entries `extensional` and `regularity` quote the witnesses proved in the hierarchy chapter. Separation's realizer is `separateFull a φ`, the pair of the separated set and its specification, already in the shape the field asks for. Each field is a function of its parameters, so every instance of the schema, for every formula, is supplied at once.
<!--zh-->
第一组条目复用章首的转换。空集、配对与并的显式实现者分别是库集合 `∅`、`⁅ a , b ⁆`、`⋃ a`，连同在那里证明的规格；`extensional` 与 `regularity` 两项引用层级一章所证的见证。分离的实现者是 `separateFull a φ`，即分离集与规格组成的对，已恰为字段要求的形状。每个字段都是其参数的函数，所以模式的每个实例、对每个公式都一次给出。
<!--ja-->
最初のグループの項目は章の冒頭の変換を再利用します。空集合、対、和集合の明示的な実現者は、それぞれライブラリの集合 `∅`、`⁅ a , b ⁆`、`⋃ a` と、そこで示した仕様です。`extensional` と `regularity` の項目は、階層の章で証明された証拠を引用します。分出の実現者は `separateFull a φ`、すなわち分出された集合とその仕様の対で、すでにフィールドの要求する形をしています。各フィールドはパラメータの関数なので、図式のすべての実例が、すべての論理式に対して一度に供給されます。
<!--/-->

```agda
    ; regularity     = regularityV
    ; hasEmpty       = one _ (∅ , empty-spec)
    ; hasPair        = λ a b → one _ (⁅ a , b ⁆ , pair-spec a b)
    ; hasUnion       = λ a → one _ (⋃ a , union-spec a)
    ; hasSeparation  = λ a φ → one _ (separateFull a φ)
```

<!--en-->
The next two entries consume the middle constructions. The replacement field receives the functionality hypothesis `fc` and takes as realizer the image `replaceImage` with its specification; the power-set field takes `𝒫V a` with `power-spec`, the construction built from the small classifier alone. The numeral chain then occupies three entries: the operation `numeralV` itself, and the two pinning equations, `numeral-zero` saying that nothing inhabits `numeralV zero`, and `numeral-suc` giving the member-or-predecessor dichotomy for `numeralV (suc n)`. Both equations come from the `NumPin` lemmas applied to the alignment `numeralV≡#`, so they carry exactly the content of that alignment plus the `sucV` case analysis.
<!--zh-->
接下来两个条目消费中段的构造。替换字段接收函数性前提 `fc`，以像 `replaceImage` 及其规格为实现者；幂集字段取 `𝒫V a` 及 `power-spec`，即仅由小分类器造出的构造。数码链占据三项：运算 `numeralV` 本身，以及两条固定方程，`numeral-zero` 说没有元素居于 `numeralV zero`，`numeral-suc` 给出 `numeralV (suc n)` 的「成员或前驱」二分。两条方程都来自把 `NumPin` 引理应用于对齐 `numeralV≡#`，因此其内容恰是该对齐加上 `sucV` 分情形分析。
<!--ja-->
続く二つの項目は、中盤の構成を使います。置換のフィールドは関数性の仮定 `fc` を受け取り、像 `replaceImage` とその仕様を実現者とします。冪集合のフィールドは `𝒫V a` と `power-spec`、つまり小分類子だけから作った構成を取ります。数項の列は三つの項目を占めます。演算 `numeralV` 自身と、二つの固定方程式です。`numeral-zero` は `numeralV zero` には元が住まないことを、`numeral-suc` は `numeralV (suc n)` の元が前者の元か前者と等しいかの二分であることを述べます。どちらの方程式も、整列 `numeralV≡#` に対する `NumPin` の補題の適用から来るため、その内容はちょうどこの整列と `sucV` の場合分けです。
<!--/-->

```agda
    ; hasReplacement = λ a φ fc → one _ (replaceImage a φ fc , replaceImage-spec a φ fc)
    ; hasPower       = λ a → one _ (𝒫V a , power-spec a)
    ; numeral        = numeralV
    ; numeral-zero   = NumPin.pinZero numeralV numeralV≡#
    ; numeral-suc    = NumPin.pinSuc numeralV numeralV≡#
```

<!--en-->
The last field is strong infinity, realized by `ω` with its specification: every member of `ω` is merely a model numeral, which is what the record demands. The auxiliary `one` records the general principle that closes every existence field. For any class `Q : S → hProp (ℓ-suc ℓ)`, an element of `SetOf Q`, that is a realizing set with its specification, already determines an element of `isContr (SetOf Q)`, because `setOf-unique` applied to extensionality contracts all realizers to the given one. So every explicit realizer above becomes the contractibility data its field requires, and extensionality is quoted once in `one` rather than repeated in each entry.
<!--zh-->
最后一个字段是强无穷，由 `ω` 及其规格实现：`ω` 的每个成员都仅仅是某个模型数码，这正是 record 的要求。辅助定义 `one` 用一行记录收尾所有存在性字段的一般原则。对任何类 `Q : S → hProp (ℓ-suc ℓ)`，`SetOf Q` 的一个元素，即实现集合连同其规格，已足以确定 `isContr (SetOf Q)` 的元素，因为把 `setOf-unique` 应用于外延性，就能把一切实现者收缩到给定者。于是上面每个显式实现者都变成其字段所需的紧缩数据，外延性在 `one` 中引用一次，而不必在每个条目里重复。
<!--ja-->
最後のフィールドは強い無限で、`ω` とその仕様が実現します。`ω` の各元は単にどこかのモデル数項と等しい、というのが record の要求です。補助の `one` は、すべての存在のフィールドを締めくくる一般原則を一行で記録します。任意のクラス `Q : S → hProp (ℓ-suc ℓ)` に対し、`SetOf Q` の元、すなわち実現する集合とその仕様は、`setOf-unique` を外延性に適用すればすべての実現者が与えられたものへ収縮するため、`isContr (SetOf Q)` の元をすでに定めます。したがって上の各明示的な実現者は、そのフィールドの要求する可縮データになり、外延性は各項目で繰り返されず `one` で一度引用されます。
<!--/-->

```agda
    ; hasInfinity    = one _ (ω , ω-specV) }
    where
    one : (Q : S → hProp (ℓ-suc ℓ)) → SetOf Q → isContr (SetOf Q)
    one = setOf-unique extensionalV
```

<!--en-->
The theorem `V⊨ZF-impredicative` states that the cumulative hierarchy satisfies ZF under the single hypothesis `Impredicativity ℓ`. Both schema fields are functions that accept every formula, so separation and replacement hold for all formulas at once, through the deep embedding of the object language in the first-order logic chapters. The second theorem replaces the packing with the standard classical assumption: `V⊨ZF` takes `LEM (ℓ-suc ℓ)` and derives the packing from it. What is proved is a model construction under the stated hypothesis, not an unconditional consistency claim.
<!--zh-->
定理 `V⊨ZF-impredicative` 陈述：在单一假设 `Impredicativity ℓ` 下，累积层级满足 ZF。两个模式字段都是接受一切公式的函数，因此分离与替换对所有公式一次成立，其中用到一阶逻辑诸章对对象语言的深嵌入。第二个定理把打包换成标准经典假设：`V⊨ZF` 取 `LEM (ℓ-suc ℓ)`，并从中导出该打包。所证的是在所述假设下的模型构造，而非无条件的无矛盾性断言。
<!--ja-->
定理 `V⊨ZF-impredicative` は、単一の仮定 `Impredicativity ℓ` の下で累積階層が ZF を満たすことを述べます。二つの図式のフィールドはどちらもすべての論理式を受け取る関数なので、分出と置換はすべての論理式に対して一度に成り立ちます。そこでは一階論理の諸章による対象言語の深い埋め込みが働きます。第二の定理は、このパッキングを標準的な古典的仮定に置き換えます。`V⊨ZF` は `LEM (ℓ-suc ℓ)` を受け取り、そこからパッキングを導きます。証明されるのは、明示された仮定の下でのモデルの構成であり、無条件の無矛盾性の主張ではありません。
<!--/-->

<!--en-->
The definition of `V⊨ZF` is one composition: the excluded middle instance is converted into the packing by `lem→impredicativity`, and the result is fed to `VModel.V⊨ZF-impredicative`. In that conversion, from the classical chapter, the resizing field uses `lem` at its own level, while the classifier field first lowers the instance one successor step with `lowerLEM` and then builds the equivalence presenting `hProp ℓ` by `Lift Bool`. One assumption at the successor level therefore reaches both fields the model consumes: separation through resizing, power set through the classifier.
<!--zh-->
`V⊨ZF` 的定义是一次复合：排中律实例经 `lem→impredicativity` 转为打包，其结果交给 `VModel.V⊨ZF-impredicative`。在该转换 (来自经典一章) 中，降层字段在其自身层级使用 `lem`，而分类器字段先用 `lowerLEM` 把实例下降一个后继步，再构造以 `Lift Bool` 呈现 `hProp ℓ` 的等价。于是后继层上的一条假设同时到达模型消耗的两个字段：分离经由降层，幂集经由分类器。
<!--ja-->
`V⊨ZF` の定義は一度の合成です。排中律の実例を `lem→impredicativity` がパッキングへ変換し、その結果が `VModel.V⊨ZF-impredicative` に渡されます。この変換、古典の章で示されたものでは、リサイズのフィールドは `lem` をそのレベルでそのまま使い、分類子のフィールドはまず `lowerLEM` で実例を後続一段下げてから、`hProp ℓ` を `Lift Bool` で提示する同値を構成します。したがって後続レベルでの一つの仮定が、モデルが消費する両方のフィールドに届きます。分出はリサイズを通して、冪集合は分類子を通してです。
<!--/-->

```agda
V⊨ZF : LEM (ℓ-suc ℓ) → isZFModel
V⊨ZF lem = VModel.V⊨ZF-impredicative (lem→impredicativity lem)
```

<!--en-->
## Choice as a separate assumption

Excluded middle does not yield choice, so the last axiom of ZFC is taken as a separate assumption and the choice-set axiom is proved from it. The interface is `SetChoice`{.Agda}: for an h-set `X : Type ℓ` and a family `B : X → Type ℓ` each of whose fibers is merely inhabited, there is a choice function on the whole of `X`, given as a truncated inhabitant. The lemma below assumes a level-`ℓ` instance of this interface together with an `isZFModel` for the fixed hierarchy structure `𝒮ᵥ`, from which it uses the intersection `∩` and its specification. The family whose choice is taken is a small presentation: the index type is `⟪ a ⟫`, an h-set, and the fiber over an index `m` is the set `⟪ ⟪ a ⟫↪ m ⟫` presented by `m`. So choice selects presentation indices, not elements of sets. From the chosen indices a set `c` is formed by one application of `sett`; the pairwise disjointness hypothesis `disj` then shows, through the model's intersection, that `c` meets each member of `a` in a contractible, hence unique, set of points. The truncation is asymmetric by design: the choice set itself is merely existential, while each intersection carries explicit `isContr` data. The final theorem consumes one instance of `SetChoice (ℓ-suc ℓ)` twice: `choice→lem` converts it into `LEM (ℓ-suc ℓ)` for the ZF part, and `lowerSetChoice` lowers it to `SetChoice ℓ` for the choice lemma. So `V⊨ZFC` is proved from choice alone; excluded middle is recovered from choice by Diaconescu's theorem, not the other way round.
<!--zh-->
## 另行假设选择公理

排中律推不出选择，因此 ZFC 的最后一条公理被另立为假设，选择集公理由它证明。接口是 `SetChoice`{.Agda}：对 h-集合 `X : Type ℓ` 与族 `B : X → Type ℓ`，若每个纤维仅仅居有，则整个 `X` 上存在选择函数，以截断的形式给出。下面的引理假设该接口在层级 `ℓ` 的一个实例，连同固定层级结构 `𝒮ᵥ` 上的一个 `isZFModel`，并从中使用交 `∩` 及其规格。被施加选择的族是一个小呈现：索引类型是 `⟪ a ⟫`，它是一个 h-集合；索引 `m` 上的纤维是 `m` 所呈现的集合 `⟪ ⟪ a ⟫↪ m ⟫`。因此选择选出的是呈现索引，而非集合的元素。由被选索引经一次 `sett` 造出集合 `c`；再由两两不交前提 `disj`，经由模型的交证明 `c` 与 `a` 的每个成员的交是可缩从而唯一的点集。截断在设计上是不对称的：选择集本身仅仅是存在，而每个交都携带显式的 `isContr` 数据。最终定理把一个 `SetChoice (ℓ-suc ℓ)` 实例用两次：`choice→lem` 把它转为 `LEM (ℓ-suc ℓ)` 供 ZF 部分使用，`lowerSetChoice` 把它降到 `SetChoice ℓ` 供选择引理使用。所以 `V⊨ZFC` 单凭选择而证；排中律由选择经 Diaconescu 定理回收，而非相反。
<!--ja-->
## 選択公理を別に仮定する

排中律から選択は導けないため、ZFC の最後の公理は独立な仮定として受け、選択集合の公理はそこから証明します。インターフェースは `SetChoice`{.Agda} です。h-集合 `X : Type ℓ` と族 `B : X → Type ℓ` に対し、各ファイバーが単に居住するなら、`X` 全体の上の選択関数が、切り詰められた形で存在します。以下の補題は、このインターフェースのレベル `ℓ` の実例と、固定された階層構造 `𝒮ᵥ` 上の `isZFModel` を仮定し、そこから交 `∩` とその仕様を使います。選択を施す族は小さな提示です。添字の型は h-集合 `⟪ a ⟫` であり、添字 `m` 上のファイバーは `m` が提示する集合 `⟪ ⟪ a ⟫↪ m ⟫` です。したがって選択が選ぶのは集合の要素ではなく提示の添字です。選ばれた添字から、`sett` を一度適用して集合 `c` を作ります。そして互いに素であることの仮定 `disj` により、モデルの交を通して、`c` が `a` の各元と交わる点の集合が可縮、したがって一意であることが示されます。切り詰めは設計上非対称です。選択集合そのものは単なる存在ですが、各交わりは明示的な `isContr` のデータを持ちます。最終定理は一つの `SetChoice (ℓ-suc ℓ)` の実例を二度使います。`choice→lem` がそれを ZF の部分のための `LEM (ℓ-suc ℓ)` へ変換し、`lowerSetChoice` がそれを選択の補題のための `SetChoice ℓ` へ下げます。つまり `V⊨ZFC` は選択だけから証明されます。排中律はディアコネスクの定理により選択から回収されるのであって、逆ではありません。
<!--/-->

<!--en-->
Two preliminary facts feed the choice-set construction. The first concerns the index type at which choice will be applied. Each presentation type `⟪ a ⟫` is an h-set: it embeds into the hierarchy through `⟪ a ⟫↪`, whose embedding property `isEmb⟪ a ⟫↪` was recorded when the presentation was introduced, and the hierarchy itself is an h-set by `setIsSet`. A general cubical result, `Embedding-into-isSet→isSet`, transfers the h-set condition back along an embedding, so `isSet⟪ a ⟫` holds for every set `a`. Equality types between indices are therefore propositions, which is precisely the condition `SetChoice` places on the type it chooses from.
<!--zh-->
选择集构造要用到两条预备事实。第一条关乎施加选择的索引类型。每个呈现类型 `⟪ a ⟫` 都是 h-集合：它经 `⟪ a ⟫↪` 嵌入层级，而嵌入性质 `isEmb⟪ a ⟫↪` 在引入该呈现时已记录；层级本身由 `setIsSet` 是 h-集合。cubical 的一般结果 `Embedding-into-isSet→isSet` 沿嵌入把 h-集合性传回，于是对每个集合 `a` 都有 `isSet⟪ a ⟫`。索引之间的相等类型因此都是命题，这正是 `SetChoice` 对其选择对象类型所要求的条件。
<!--ja-->
選択集合の構成には二つの準備的事実が使われます。第一は、選択を適用する添字の型に関するものです。各提示の型 `⟪ a ⟫` は h-集合です。`⟪ a ⟫↪` を通して階層へ埋め込まれ、その埋め込みの性質 `isEmb⟪ a ⟫↪` は提示の導入時に記録済みであり、階層自身は `setIsSet` により h-集合だからです。cubical の一般結果 `Embedding-into-isSet→isSet` が埋め込みに沿って h-集合性を引き戻すので、任意の集合 `a` に対して `isSet⟪ a ⟫` が成ります。したがって添字の間の等号の型はすべて命題であり、これがまさに `SetChoice` が選択の対象とする型に課す条件です。
<!--/-->

```agda
private
  isSet⟪_⟫ : (a : S) → isSet ⟪ a ⟫
  isSet⟪ a ⟫ = Embedding-into-isSet→isSet (⟪ a ⟫↪ , isEmb⟪ a ⟫↪) setIsSet

  isContrΣ-fromCenter : {P : S → hProp (ℓ-suc ℓ)} (z₀ : S) (p₀ : z₀ ∈ᶜ P)
                      → ((z : S) → z ∈ᶜ P → z₀ ≡ z)
```

<!--en-->
The second fact turns a uniqueness argument into contractibility data. For a class `P` on the carrier, suppose a centre `z₀` with a realization `p₀`, together with a contraction sending every realizing `z` to a path `z₀ ≡ z`. Then the type of pairs of a set and a realization of `P` is contractible, with centre `(z₀ , p₀)`. The contraction between pairs is built with `Σ≡Prop`: it suffices to give the path between first components, because each `P v` is a proposition and so fixes the second component. The choice-set conclusion has exactly this shape: one meeting point, unique in the `isContr` sense. The lemma then takes its hypotheses. It assumes an arbitrary `isZFModel` for the fixed structure `𝒮ᵥ`, from which it uses only the model's intersection `∩` and its specification `∩-spec`, together with an instance of `SetChoice ℓ`.
<!--zh-->
第二条事实把唯一性论证打包成紧缩性数据。对载体上的类 `P`，假设有中心 `z₀` 及其实现 `p₀`，并有紧缩把每个实现 `z` 送到路径 `z₀ ≡ z`。那么「集合加 `P` 的实现」的序对类型是紧缩的，中心为 `(z₀ , p₀)`。序对之间的紧缩用 `Σ≡Prop` 构造：只需给出第一分量间的路径，因为每个 `P v` 是命题，第二分量随之确定。选择集结论恰是这种形状：一个交点，在 `isContr` 意义下唯一。引理的前提随之取定：它假设固定结构 `𝒮ᵥ` 上任意一个 `isZFModel`，只从中使用模型的交 `∩` 及其规格 `∩-spec`，再加上 `SetChoice ℓ` 的一个实例。
<!--ja-->
第二の事実は、一意性の議論を緊縮性のデータへ包装します。台の上のクラス `P` に対し、中心 `z₀` とその実現 `p₀`、そして `P` を実現する各 `z` をパス `z₀ ≡ z` に送る緊縮があれば、「集合と `P` の実現」の組の型は緊縮的で、その中心は `(z₀ , p₀)` です。組の間の緊縮は `Σ≡Prop` で組み立てます。第一成分の間のパスを与えれば十分で、各 `P v` が命題であるため第二成分はそれで決まるからです。選択集合の結論はちょうどこの形、`isContr` の意味で一意な一点です。補題の仮定は続いて取られます。固定された構造 `𝒮ᵥ` 上の任意の `isZFModel` を仮定し、そこからはモデルの交 `∩` とその仕様 `∩-spec` だけを使い、これに `SetChoice ℓ` の一実例を添えます。
<!--/-->

```agda
                      → isContr (Σ[ z ∈ S ] (z ∈ᶜ P))
  isContrΣ-fromCenter {P} z₀ p₀ u =
    (z₀ , p₀) , λ w → Σ≡Prop (λ v → snd (P v)) (u (w .fst) (w .snd))

module ChoiceLemma (zf : isZFModel) (ac : SetChoice ℓ) where
  open Model.isZFModel zf using ( _∩_; ∩-spec )
```

<!--en-->
The lemma `choice` states the classical choice-set situation. Its hypotheses: `inh` says each member `x` of `a` is merely inhabited, so the family consists of nonempty sets; `disj` says that two members of `a` sharing any element, even merely, are already equal, so the family is pairwise disjoint. The conclusion is a **merely existing** set `c` such that for each member `x` of `a` the type of points meeting `c ∩ x` is contractible. The truncation is asymmetric: the choice set itself is not given as data, only its truncation is inhabited, while the uniqueness of each meeting point is explicit `isContr` data.
<!--zh-->
引理 `choice` 陈述经典的选择集情形。前提是：`inh` 说 `a` 的每个成员 `x` 仅仅居有，故族由非空集组成；`disj` 说 `a` 的两个成员哪怕仅仅共享一个元素就已相等，故族两两不交。结论是一个**仅仅存在**的集合 `c`，使得对 `a` 的每个成员 `x`，与 `c ∩ x` 相交的点的类型是紧缩的。截断是不对称的：选择集本身不作为数据给出，只有其截断居有；而每个交点的唯一性却是显式的 `isContr` 数据。
<!--ja-->
補題 `choice` は古典的な選択集合の状況を述べます。仮定は次のとおりです。`inh` は `a` の各元 `x` が単に居住することを言い、族は空でない集合からなります。`disj` は、`a` の二つの元が単に共通の元を共有するだけですでに等しいことを言い、族は互いに素です。結論は、**単に存在する**集合 `c` で、`a` の各元 `x` に対して交 `c ∩ x` の点の型が緊縮的であるというものです。切り詰めは非対称です。選択集合そのものはデータとして与えられず、その切り詰めが居住するだけです。一方、各交点の一意性は明示的な `isContr` のデータです。
<!--/-->

```agda

  choice : (a : S)
         → ((x : S) → ⟨ x ∈ˢ a ⟩ → ∥ Σ[ y ∈ S ] ⟨ y ∈ˢ x ⟩ ∥₁)
         → ((x y : S) → ⟨ x ∈ˢ a ⟩ → ⟨ y ∈ˢ a ⟩
              → ∥ Σ[ z ∈ S ] (⟨ z ∈ˢ x ⟩ × ⟨ z ∈ˢ y ⟩) ∥₁ → x ≡ y)
         → ∥ Σ[ c ∈ S ] ((x : S) → ⟨ x ∈ˢ a ⟩
```

<!--en-->
The proof applies the choice instance at the small presentation of the family, not at the family itself. The index type is `⟪ a ⟫`, an h-set by the first preliminary fact; the family is `λ m → ⟪ ⟪ a ⟫↪ m ⟫`, the set presented by each index. What remains is to show each fiber merely inhabited, which is the role of `pick`: for each index `m`, a member of the presented set `⟪ a ⟫↪ m` merely exists by `inh` at the member that `memb a m` certifies, and `∈-asFiber` extracts from that membership an actual index into the presentation of `⟪ a ⟫↪ m`. The truncation on the input is preserved throughout, so `pick` never claims to choose a point inside a member of `a`; it only re-indexes the mere existence.
<!--zh-->
证明把选择实例施加在族的小呈现上，而非族本身。索引类型是 `⟪ a ⟫`，由第一条预备事实它是 h-集合；族是 `λ m → ⟪ ⟪ a ⟫↪ m ⟫`，即每个索引所呈现的集合。剩下的只需让每个纤维仅仅居有，这正是 `pick` 的作用：对每个索引 `m`，由 `inh` 在 `memb a m` 所证明的成员处得到所呈现集合 `⟪ a ⟫↪ m` 的成员仅仅存在，`∈-asFiber` 再从该成员资格提取指向 `⟪ a ⟫↪ m` 之呈现的实际索引。输入上的截断全程保持，所以 `pick` 从不宣称在 `a` 的成员内部选了点；它只是给单纯的存在重新编号。
<!--ja-->
証明は、族そのものではなく族の小さな提示の上で選択の実例を適用します。添字の型は `⟪ a ⟫` で、第一の準備事実により h-集合です。族は `λ m → ⟪ ⟪ a ⟫↪ m ⟫`、つまり各添字が提示する集合です。残るのは各ファイバーを単に居住させることで、それが `pick` の役目です。各添字 `m` に対し、`memb a m` が確かめる要素のところで `inh` が、提示された集合 `⟪ a ⟫↪ m` の要素の単なる存在を与え、`∈-asFiber` がその所属から `⟪ a ⟫↪ m` の提示への実際の添字を取り出します。入力の切り詰めは終始保存されるので、`pick` が `a` の要素の内部で点を選ぶと主張することはなく、単なる存在に添字を付け直すだけです。
<!--/-->

```agda
              → isContr (Σ[ z ∈ S ] ⟨ z ∈ˢ (c ∩ x) ⟩)) ∥₁
  choice a inh disj = PT.map mk (ac ⟪ a ⟫ isSet⟪ a ⟫ (λ m → ⟪ ⟪ a ⟫↪ m ⟫) pick)
      where
      pick : (m : ⟪ a ⟫) → ∥ ⟪ ⟪ a ⟫↪ m ⟫ ∥₁
      pick m = PT.map
```

<!--en-->
The choice function then returns, for each index `m`, an actual element `g m` of the presented set: choice on the h-set of indices yields untruncated data, an element of the presentation of `⟪ a ⟫↪ m`. The remainder `mk` packages this into the conclusion: a set `c` together with, for each member `x` of `a`, contractibility data for the type of points meeting `c ∩ x`. Because the choice function already produced untruncated data at the index level, `mk` is an ordinary function; the truncation reappears only when the whole package is wrapped by `PT.map`. This is exactly why the choice set itself is merely existential while each intersection carries explicit `isContr` data.
<!--zh-->
选择函数随后对每个索引 `m` 返回所呈现集合的一个实际元素 `g m`：对索引之 h-集合的选择给出不加截断的数据，即 `⟪ a ⟫↪ m` 之呈现的一个元素。其余部分 `mk` 把它打包成结论：集合 `c`，加上对 `a` 的每个成员 `x`，与 `c ∩ x` 相交的点类型的紧缩数据。由于选择函数在索引层产生的已是不加截断的数据，`mk` 是普通函数；截断只在整体被 `PT.map` 包装时重新出现。这正是选择集本身只是纯粹存在、而每个交都携带显式 `isContr` 数据的原因。
<!--ja-->
選択関数はその後、各添字 `m` に対して提示された集合の実際の要素 `g m` を返します。添字の h-集合上の選択は切り詰められていないデータ、すなわち `⟪ a ⟫↪ m` の提示の要素を与えます。残りの `mk` はこれを結論へ包装します。集合 `c` と、`a` の各元 `x` に対する、交 `c ∩ x` の点の型の緊縮データです。選択関数が添字の水準で既に切り詰められていないデータを生んでいるため、`mk` は普通の関数であり、切り詰めが再び現れるのは全体が `PT.map` で包まれるときだけです。選択集合そのものが単なる存在でありながら、各交わりが明示的な `isContr` のデータを持つのはまさにこのためです。
<!--/-->

```agda
        (λ { (y , y∈) → ∈-asFiber {a = y} {b = ⟪ a ⟫↪ m} y∈ .fst })
        (inh (⟪ a ⟫↪ m) (memb a m))
      mk : ((m : ⟪ a ⟫) → ⟪ ⟪ a ⟫↪ m ⟫)
         → Σ[ c ∈ S ] ((x : S) → ⟨ x ∈ˢ a ⟩
              → isContr (Σ[ z ∈ S ] ⟨ z ∈ˢ (c ∩ x) ⟩))
```

<!--en-->
Inside `mk`, the chosen data is interpreted. The function `g m` returns an index into the presentation of `⟪ a ⟫↪ m`, so composing with that presentation yields an actual set `chosen m`, a member of the member indexed by `m`. The choice set is then `c = sett ⟪ a ⟫ chosen`: the sets picked for each index, gathered by one application of the hierarchy's set former.
<!--zh-->
在 `mk` 内部，把选出的数据加以解释。`g m` 返回的是指向 `⟪ a ⟫↪ m` 之呈现的索引，与该呈现复合后得到实际的集合 `chosen m`，即索引 `m` 所指成员的一个成员。选择集就是 `c = sett ⟪ a ⟫ chosen`：为每个索引选出的集合，经层级集合构造器的一次应用收集起来。
<!--ja-->
`mk` の内部で、選ばれたデータを解釈します。`g m` が返すのは `⟪ a ⟫↪ m` の提示への添字なので、その提示と合成すると実際の集合 `chosen m`、すなわち添字 `m` の指す要素の要素の一つが得られます。選択集合は `c = sett ⟪ a ⟫ chosen`、つまり各添字のために選ばれた集合を階層の集合構成子の一度の適用で集めたものです。
<!--/-->

```agda
      mk g = c , uniq
        where
        chosen : ⟪ a ⟫ → S
        chosen m = ⟪ ⟪ a ⟫↪ m ⟫↪ (g m)
        c : S
```

<!--en-->
One fact about `c` is recorded before uniqueness: each chosen set really is a member of the member it came from. This follows from the presentation: an index `g m` into the presentation of a set is, by `∈ₛ⟪ ⟫↪`, a small membership, and `∈∈ₛ` lifts it to the structural membership `⟨ chosen m ∈ˢ ⟪ a ⟫↪ m ⟩`. With the uniqueness helper of the second preliminary fact available, `uniq` becomes a three-part argument: a centre, a proof that the centre lies in the intersection, and a contraction of every other meeting point to the centre.
<!--zh-->
在唯一性之前先记录关于 `c` 的一条事实：每个被选集合确实是它来源成员的成员。这由呈现得出：指向集合呈现的索引 `g m` 经 `∈ₛ⟪ ⟫↪` 是小成员资格，`∈∈ₛ` 把它提升为结构性成员资格 `⟨ chosen m ∈ˢ ⟪ a ⟫↪ m ⟩`。有了第二条预备事实的唯一性辅助，`uniq` 成为三段论证：中心、中心居于交中的证明、以及把其他交点紧缩到中心的紧缩。
<!--ja-->
一意性の前に、`c` についての一つの事実を記録します。選ばれた各集合は、その出身の要素の要素に確かになっています。これは提示から従います。集合の提示への添字 `g m` は `∈ₛ⟪ ⟫↪` により小さな所属であり、`∈∈ₛ` がそれを構造的な所属 `⟨ chosen m ∈ˢ ⟪ a ⟫↪ m ⟩` へ引き上げます。第二の準備事実の一意性の補助が揃うと、`uniq` は三段の議論になります。中心、中心が交に属することの証明、そして他の交点を中心へ緊縮する緊縮です。
<!--/-->

```agda
        c = sett ⟪ a ⟫ chosen
        chosen∈ : (m : ⟪ a ⟫) → ⟨ chosen m ∈ˢ ⟪ a ⟫↪ m ⟩
        chosen∈ m = ∈∈ₛ {a = chosen m} {b = ⟪ a ⟫↪ m} .snd (∈ₛ⟪ ⟪ a ⟫↪ m ⟫↪ (g m))
        uniq : (x : S) → ⟨ x ∈ˢ a ⟩ → isContr (Σ[ z ∈ S ] ⟨ z ∈ˢ (c ∩ x) ⟩)
        uniq x x∈a = isContrΣ-fromCenter {P = λ z → z ∈ˢ (c ∩ x)} z₀ pf₀ uniqz
```

<!--en-->
The centre is computed as follows. The member `x` of `a` has an untruncated presenting fiber: `∈-asFiber` gives an index `m₀` together with a path `mf .snd` presenting `x`. The meeting point is the set chosen at that index, `z₀ = chosen m₀`. This is where the untruncated fibers pay off again: recovering the index from membership is a function, not a choice, so the centre is well defined without any appeal to the choice instance.
<!--zh-->
中心这样计算。`a` 的成员 `x` 有不加截断的呈现纤维：`∈-asFiber` 给出索引 `m₀` 及呈现 `x` 的路径 `mf .snd`。交点取该索引处的被选集合 `z₀ = chosen m₀`。这正是不加截断的纤维再次发挥作用之处：从成员资格回收索引是函数而非选择，因此中心的定义无需调用选择实例。
<!--ja-->
中心は次のように計算されます。`a` の要素 `x` は切り詰められていない提示のファイバーを持ち、`∈-asFiber` が添字 `m₀` と `x` を提示するパス `mf .snd` を与えます。交点はその添字で選ばれた集合 `z₀ = chosen m₀` です。ここで再び切り詰められていないファイバーが利きます。所属から添字を復元するのは関数であって選択ではないため、中心の定義に選択の実例を呼ぶ必要はありません。
<!--/-->

```agda
          where
          mf = ∈-asFiber {a = x} {b = a} x∈a
          m₀ = mf .fst
          z₀ = chosen m₀
          pf₀ : ⟨ z₀ ∈ˢ (c ∩ x) ⟩
```

<!--en-->
The centre must lie in the intersection `c ∩ x`. By the model's `∩-spec`, membership in an intersection is a truth value equal to the conjunction of membership in `c` and in `x`, and the proof transports along the symmetrized specification. Membership in `c` merely witnesses that `z₀` was chosen at index `m₀`, with the reflexive path, and `m₀` presents `x`; membership in `x` follows by transporting `chosen∈ m₀` along that presenting path. The two halves are conjoined as a truncated pair. The remaining duty is the contraction `uniqz`, which must send every `z` meeting `c ∩ x` to a path `z₀ ≡ z`.
<!--zh-->
中心必须居于交 `c ∩ x` 中。由模型的 `∩-spec`，交中的成员资格作为真值等于「属于 `c`」与「属于 `x`」的合取，证明沿对称化后的规格进行搬运。属于 `c` 的部分以自反路径仅仅见证 `z₀` 在索引 `m₀` 处被选，而 `m₀` 呈现 `x`；属于 `x` 的部分由把 `chosen∈ m₀` 沿该呈现路径搬运得到。两部分作为截断的序对合取。剩下的任务是紧缩 `uniqz`：它须把交 `c ∩ x` 中的每个 `z` 送到路径 `z₀ ≡ z`。
<!--ja-->
中心は交 `c ∩ x` に属さねばなりません。モデルの `∩-spec` により、交への所属は真理値として「`c` への所属」と「`x` への所属」の連言に等しく、証明は対称化した仕様に沿って輸送します。`c` への所属は、自反パスとともに、`z₀` が添字 `m₀` で選ばれたことの単なる証明であり、`m₀` は `x` を提示します。`x` への所属は、`chosen∈ m₀` をその提示のパスに沿って輸送することで従います。二つの半分は切り詰められた組として連言されます。残る仕事は緊縮 `uniqz` です。交 `c ∩ x` に属する各 `z` をパス `z₀ ≡ z` に送らねばなりません。
<!--/-->

```agda
          pf₀ = subst ⟨_⟩ (sym (∩-spec c x z₀))
                  ( ∣ m₀ , refl ∣₁
                  , subst (λ w → ⟨ z₀ ∈ˢ w ⟩) (mf .snd) (chosen∈ m₀) )
          uniqz : (z : S) → ⟨ z ∈ˢ (c ∩ x) ⟩ → z₀ ≡ z
          uniqz z pf = PT.rec (setIsSet z₀ z)
```

<!--en-->
The contraction is the delicate half. Take any `z` meeting `c ∩ x`; membership in the intersection transports through `∩-spec` into the truncated conjunction `zcx`. The first component says, merely, that `z` lies in some chosen set: an index `m` together with a path `q` from `z` to `chosen m` as members of `c`. Since `chosen m` is a member of `⟪ a ⟫↪ m` by `chosen∈`, transporting along `q` shows `z` is a member of that member too. So `z` is a shared element of the members `x` and `⟪ a ⟫↪ m` of `a`, and disjointness applies: `disj` yields the path `x ≡ ⟪ a ⟫↪ m`. The two members present the same set, so their presenting indices agree: the presentation is an embedding, hence injective on indices, and `isEmbedding→Inj` applied to the composed paths gives `m ≡ m₀`. Therefore `chosen m ≡ chosen m₀ = z₀`, and composing with `q` yields the contraction path `z₀ ≡ z`. The target is a path between elements of an h-set, hence a proposition, which licenses eliminating the truncation here.

The accounting of the chapter's final theorem is exact. One instance of `SetChoice (ℓ-suc ℓ)` is used twice: `choice→lem` converts it into `LEM (ℓ-suc ℓ)`, which drives the ZF part through `V⊨ZF`, and `lowerSetChoice` lowers the same instance to `SetChoice ℓ`, which feeds `ChoiceLemma` for the choice-set part. The choice set exists merely, while each intersection is uniquely determined by explicit contractibility data.
<!--zh-->
紧缩是较精巧的一半。取交 `c ∩ x` 中的任意 `z`；交中的成员资格经 `∩-spec` 搬运为截断的合取 `zcx`。第一分量仅仅说 `z` 居于某个被选集合：即索引 `m` 加上从 `z` 到 `chosen m` 的作为 `c` 成员的路径 `q`。由 `chosen∈`，`chosen m` 是 `⟪ a ⟫↪ m` 的成员，沿 `q` 搬运便知 `z` 也是该成员的成员。于是 `z` 是 `a` 的成员 `x` 与 `⟪ a ⟫↪ m` 的公共元素，不交性随即适用：`disj` 给出路径 `x ≡ ⟪ a ⟫↪ m`。两个成员呈现同一集合，所以它们的呈现索引一致：呈现是嵌入，从而在索引上单射，把复合后的路径交给 `isEmbedding→Inj` 即得 `m ≡ m₀`。因此 `chosen m ≡ chosen m₀ = z₀`，与 `q` 复合即得紧缩路径 `z₀ ≡ z`。目标是 h-集合的元素之间的路径，因而是命题，这正允许在此消去截断。

本章最终定理的记账是精确的。`SetChoice (ℓ-suc ℓ)` 的一个实例被使用两次：`choice→lem` 把它转为 `LEM (ℓ-suc ℓ)`，经 `V⊨ZF` 驱动 ZF 部分；`lowerSetChoice` 把同一实例降到 `SetChoice ℓ`，供给 `ChoiceLemma` 作选择集部分。选择集只是纯粹地存在，而每个交由显式的紧缩数据唯一确定。
<!--ja-->
緊縮が繊細な半分です。交 `c ∩ x` に属する任意の `z` を取ると、交への所属が `∩-spec` を通して切り詰められた連言 `zcx` へ輸送されます。第一成分は、`z` がある選ばれた集合に属することの単なる証明です。すなわち添字 `m` と、`c` の要素としての `z` から `chosen m` へのパス `q` です。`chosen∈` により `chosen m` は `⟪ a ⟫↪ m` の要素なので、`q` に沿って輸送すれば `z` がその要素の要素でもあることが分かります。したがって `z` は `a` の要素 `x` と `⟪ a ⟫↪ m` の共通の要素であり、非交性が適用されます。`disj` はパス `x ≡ ⟪ a ⟫↪ m` を与えます。二つの要素は同じ集合を提示するので、提示する添字は一致します。提示は埋め込みで添字の上で単射だから、合成したパスに `isEmbedding→Inj` を適用すれば `m ≡ m₀` が従います。よって `chosen m ≡ chosen m₀ = z₀` であり、`q` と合成すれば緊縮のパス `z₀ ≡ z` が得られます。目標は h-集合の要素の間のパス、つまり命題であり、これがここで切り詰めを消去することを正当化します。

本章の最終定理の計算は正確です。`SetChoice (ℓ-suc ℓ)` の一つの実例が二度使われます。`choice→lem` がそれを `LEM (ℓ-suc ℓ)` へ変換し、`V⊨ZF` を通して ZF の部分を駆動します。また `lowerSetChoice` が同じ実例を `SetChoice ℓ` に下げ、選択集合の部分のために `ChoiceLemma` に渡します。選択集合は単に存在するだけですが、各交わりは明示的な緊縮のデータによって一意に定まります。
<!--/-->

```agda
              (λ { (m , q) →
                let z∈m : ⟨ z ∈ˢ ⟪ a ⟫↪ m ⟩
                    z∈m = subst (λ w → ⟨ w ∈ˢ ⟪ a ⟫↪ m ⟩) q (chosen∈ m)
                    x≡m : x ≡ ⟪ a ⟫↪ m
                    x≡m = disj x (⟪ a ⟫↪ m) x∈a (memb a m)
```

<!--en-->
Disjointness is applied to the two members `x` and `⟪ a ⟫↪ m` of `a`, with the shared element `z` as the witness of their overlap; the hypothesis `disj` returns the path `x ≡ ⟪ a ⟫↪ m`. The two indices therefore present the same member, and the presentation `⟪ a ⟫↪` is an embedding, hence injective on indices: `isEmbedding→Inj`, applied to the composition `sym x≡m ∙ sym (mf .snd)`, yields `m ≡ m₀`. Applying `chosen` to that path and composing with `q` produces `z₀ ≡ z`, the path the contraction requires. The target `z₀ ≡ z` is a path between elements of the h-set V, hence a proposition, which licenses eliminating the truncation of the case analysis here.
<!--zh-->
把不交性用于 `a` 的两个成员 `x` 与 `⟪ a ⟫↪ m`，以公共元素 `z` 为重叠的见证；前提 `disj` 返回路径 `x ≡ ⟪ a ⟫↪ m`。于是两个索引呈现同一成员，而呈现 `⟪ a ⟫↪` 是嵌入，从而在索引上单射：把复合 `sym x≡m ∙ sym (mf .snd)` 交给 `isEmbedding→Inj`，便得 `m ≡ m₀`。对该路径施加 `chosen` 并与 `q` 复合，即产生紧缩所需的路径 `z₀ ≡ z`。目标 `z₀ ≡ z` 是 h-集合 V 的元素之间的路径，因而是命题，这正允许在此消去分情形的截断。
<!--ja-->
非交性を `a` の二つの要素 `x` と `⟪ a ⟫↪ m` に適用し、重なりの証人として共通の要素 `z` を渡すと、仮定 `disj` はパス `x ≡ ⟪ a ⟫↪ m` を返します。したがって二つの添字は同じ要素を提示します。提示 `⟪ a ⟫↪` は埋め込みであり、添字の上で単射なので、合成 `sym x≡m ∙ sym (mf .snd)` に `isEmbedding→Inj` を適用すれば `m ≡ m₀` が得られます。このパスに `chosen` を施し `q` と合成すれば、緊縮の要求するパス `z₀ ≡ z` が生まれます。目標 `z₀ ≡ z` は h-集合 V の要素の間のパス、つまり命題であり、これがここで場合分けの切り詰めを消去することを正当化します。
<!--/-->

```agda
                            ∣ z , zcx .snd , z∈m ∣₁
                    m≡m₀ : m ≡ m₀
                    m≡m₀ = isEmbedding→Inj isEmb⟪ a ⟫↪ m m₀
                             (sym x≡m ∙ sym (mf .snd))
                in sym (cong chosen m≡m₀) ∙ q })
```

<!--en-->
The conjunction `zcx` is produced by transporting `pf` along the path `∩-spec c x z`, which rewrites membership in `c ∩ x` as a plain pair of the two membership propositions. Its components are then used separately: the first feeds the disjointness witness of the previous step, and the second enters the transport `z∈m` of the membership of `z`. With the centre and the contraction in place, `uniq` supplies the `isContr` data for each member `x` of `a`, and `mk` returns the set `c` together with those data. The choice set itself exists only merely, as an inhabitant of a propositional truncation; the uniqueness of each intersection, by contrast, is explicit, untruncated `isContr` data.
<!--zh-->
合取 `zcx` 由把 `pf` 沿路径 `∩-spec c x z` 搬运得到，它把 `c ∩ x` 中的成员资格改写成两个成员命题的普通序对。两个分量随后分开使用：第一个进入上一步的不交性见证，第二个进入 `z` 的成员资格搬运 `z∈m`。中心与紧缩就位后，`uniq` 为 `a` 的每个成员供给 `isContr` 数据，`mk` 返回集合 `c` 连同这些数据。选择集本身只是作为命题截断的一个元素纯粹存在；相比之下，每个交的唯一性是不加截断的显式 `isContr` 数据。
<!--ja-->
連言 `zcx` は、`pf` をパス `∩-spec c x z` に沿って輸送して得られ、`c ∩ x` への所属が二つの所属命題の普通の組として書き直されます。二つの成分はその後別々に使われます。第一成分は前段の非交性の証人に入り、第二成分は `z` の所属の輸送 `z∈m` に入ります。中心と緊縮が揃うと、`uniq` が `a` の各要素に対する `isContr` のデータを供給し、`mk` は集合 `c` とそれらのデータを返します。選択集合そのものは、命題の切り詰めの要素として単に存在するだけです。それに対して、各交の一意性は切り詰められていない明示的な `isContr` のデータです。
<!--/-->

```agda
              (zcx .fst)
            where
            zcx : ⟨ z ∈ˢ c ⟩ × ⟨ z ∈ˢ x ⟩
            zcx = subst ⟨_⟩ (∩-spec c x z) pf

```

<!--en-->
## V ⊨ ZFC, on choice alone

The lemma of the previous section and the ZF theorem meet here. The construction `ChoiceLemma.choice` is proved for the fixed hierarchy structure under two stated hypotheses: an arbitrary `isZFModel` for that structure, and an instance of `SetChoice ℓ`. Its index type is the small presentation `⟪ a ⟫`, an h-set, so choice selects presentation indices of the family; disjointness then proves each intersection contractible. The choice set therefore exists merely, while each meeting point is unique as explicit `isContr` data. The theorem `V⊨ZFC` states the exact combined cost: `SetChoice (ℓ-suc ℓ)` yields `LEM (ℓ-suc ℓ)` for the ZF part via `choice→lem`, and the same instance, lowered by `lowerSetChoice` to `SetChoice ℓ`, drives the choice-set lemma. What is proved is a model construction under the stated hypothesis, not an unconditional proof.
<!--zh-->
## V ⊨ ZFC：单凭选择

上一节的引理与 ZF 定理在此会合。构造 `ChoiceLemma.choice` 是对固定层级结构、在两条明示前提下证明的：该结构上任意一个 `isZFModel`，以及 `SetChoice ℓ` 的一个实例。其索引类型是小呈现 `⟪ a ⟫`，是一个 h-集合，因此选择选出的是族的呈现索引；随后不交性证明每个交可缩。于是选择集仅仅存在，而每个交点作为显式 `isContr` 数据唯一。定理 `V⊨ZFC` 陈述的正是合并后的精确代价：`SetChoice (ℓ-suc ℓ)` 经 `choice→lem` 为 ZF 部分给出 `LEM (ℓ-suc ℓ)`，同一实例经 `lowerSetChoice` 降为 `SetChoice ℓ`，驱动选择集引理。所证的是所述假设下的模型构造，而非无条件的证明。
<!--ja-->
## 選択だけから V ⊨ ZFC

前節の補題と ZF の定理がここで合流します。構成 `ChoiceLemma.choice` は、固定された階層構造に対して、二つの明示された仮定の下で証明されています。その構造上の任意の `isZFModel` と、`SetChoice ℓ` の一実例です。その添字の型は小さな提示 `⟪ a ⟫` であり h-集合なので、選択が選ぶのは族の提示の添字です。その後、非交性が各交の可縮性を示します。したがって選択集合は単に存在するだけであり、各交点は明示的な `isContr` のデータとして一意です。定理 `V⊨ZFC` が述べるのは結合後の正確なコストです。`SetChoice (ℓ-suc ℓ)` は `choice→lem` を通して ZF の部分に `LEM (ℓ-suc ℓ)` を与え、同じ実例を `lowerSetChoice` で `SetChoice ℓ` に下げたものが選択集合の補題を駆動します。証明されるのは明示された仮定の下でのモデルの構成であり、無条件の証明ではありません。
<!--/-->

<!--en-->
The theorem's hypothesis is a single instance, `SetChoice (ℓ-suc ℓ)`: set-level choice at the successor of the model's truth level. The conclusion `isZFCModel` packages a ZF model together with an internal choice-set witness, so the proof supplies both components. The ZF part is named `base`, since the choice-set lemma takes a ZF model as an input.
<!--zh-->
定理的前提是单个实例：`SetChoice (ℓ-suc ℓ)`，即模型真值层的后继上的集合层选择。结论 `isZFCModel` 把一个 ZF 模型与内部的选择集见证打包在一起，因此证明同时给出两个分量。ZF 部分被命名为 `base`，因为选择集引理要以 ZF 模型为输入。
<!--ja-->
定理の仮定は一つの実例です。すなわち `SetChoice (ℓ-suc ℓ)`、モデルの真理値の水準の後続における集合レベルの選択です。結論 `isZFCModel` は ZF モデルと内部の選択集合の証明をひとまとめにするので、証明は両方の成分を与えます。ZF の部分には `base` と名前が付きます。選択集合の補題が入力として ZF モデルを受け取るからです。
<!--/-->

```agda
V⊨ZFC : SetChoice (ℓ-suc ℓ) → isZFCModel
V⊨ZFC ac = record
  { zf = base ; hasChoice = ChoiceLemma.choice base (lowerSetChoice ac) }
  where
  base : isZFModel
```

<!--en-->
The single instance is used for two conclusions. `choice→lem` converts it into excluded middle at level `ℓ-suc ℓ`, which is exactly the hypothesis `V⊨ZF` expects; this gives `base`. For the choice-set part, `lowerSetChoice` lowers the same instance to `SetChoice ℓ`, which is what `ChoiceLemma.choice` requires, and the lemma is applied to `base`. Thus one instance of choice at the successor level yields the ZF model through excluded middle, and its one-level lowering yields the choice-set axiom.
<!--zh-->
单个实例被用于两个结论。`choice→lem` 把它转为层 `ℓ-suc ℓ` 的排中律，恰是 `V⊨ZF` 所期望的前提，由此得到 `base`。选择集部分则由 `lowerSetChoice` 把同一实例降到 `SetChoice ℓ`，这正是 `ChoiceLemma.choice` 所需要的，引理随即应用于 `base`。于是，后继层上的一例选择经排中律给出 ZF 模型，其低一层的形式给出选择集公理。
<!--ja-->
一つの実例が二つの結論に使われます。`choice→lem` はそれをレベル `ℓ-suc ℓ` の排中律へ変換し、これは `V⊨ZF` が期待する仮定にちょうど一致するので、`base` が得られます。選択集合の部分では、`lowerSetChoice` が同じ実例を `SetChoice ℓ` に下げます。これが `ChoiceLemma.choice` の要求するものであり、補題は `base` に適用されます。こうして、後続レベルでの一つの選択の実例が排中律を通して ZF モデルを与え、一段下げたそれが選択集合の公理を与えます。
<!--/-->

```agda
  base = V⊨ZF (choice→lem ac)
```

<!--en-->
## Recap

The chapter's accounting is now complete. Empty set, pair, and union were converted from existing constructions by `∈∈ₛ` and `⇔toPath`{.Agda}; replacement follows directly through `sett` over untruncated fibers; strong infinity is `ω`'s definition plus one chain alignment (`numeralV≡#`{.Agda}). The two remaining fields, full separation and power set, need exactly the `Impredicativity`{.Agda} packing of `Base.Impredicativity`: assembly gives `V⊨ZF-impredicative`{.Agda} at that exact cost, and excluded middle upgrades it to the headline `V⊨ZF`{.Agda}. One further, independent instance of set-level choice supplies the final theorem: `SetChoice (ℓ-suc ℓ)` yields `LEM (ℓ-suc ℓ)` for the ZF part and, lowered one level to `SetChoice ℓ`, drives the choice-set lemma, giving `V⊨ZFC`{.Agda}. The universe that the constructible-universe chapters will examine from within now exists.
<!--zh-->
## 小结

本章的记账至此完成。空集、配对与并经由 `∈∈ₛ` 和 `⇔toPath`{.Agda} 从既有构造转换而来；替换沿未加截断的纤维经 `sett` 直接得到；强无穷是 `ω` 的定义再加一次链对齐 (`numeralV≡#`{.Agda})。剩下两条，全分离与幂集，所需的恰是 `Base.Impredicativity` 打包的 `Impredicativity`{.Agda}：合龙以此精确代价给出 `V⊨ZF-impredicative`{.Agda}，排中律把它提升为主要的 `V⊨ZF`{.Agda}。最后一个条件是一个独立的、再另加的集合层选择实例：`SetChoice (ℓ-suc ℓ)` 为 ZF 部分给出 `LEM (ℓ-suc ℓ)`，同一实例降到 `SetChoice ℓ` 后驱动选择集引理，于是得到 `V⊨ZFC`{.Agda}。可构造宇宙诸章将要向内考察的那个宇宙，至此已经构造完成。
<!--ja-->
## まとめ

本章の勘定はこれで完結します。空集合、対、和集合は既存の構成を `∈∈ₛ` と `⇔toPath`{.Agda} で変換したものです。置換は切り詰められていないファイバーの上の `sett` を通して直接従い、強い無限は `ω` の定義に一つの列の整列 (`numeralV≡#`{.Agda}) を加えたものです。残る二つの欄、完全な分出と冪集合に必要なのは、`Base.Impredicativity` がまとめた `Impredicativity`{.Agda} のパッキングそのものです。組み立てはその正確なコストで `V⊨ZF-impredicative`{.Agda} を与え、排中律がそれを主たる `V⊨ZF`{.Agda} へ引き上げます。最後の定理には、さらに独立な集合レベルの選択の実例が一つ要ります。`SetChoice (ℓ-suc ℓ)` は ZF の部分に `LEM (ℓ-suc ℓ)` を与え、同じ実例を一段下げた `SetChoice ℓ` が選択集合の補題を駆動し、`V⊨ZFC`{.Agda} が得られます。構成可能宇宙の諸章が内側から調べることになる宇宙が、ここに存在するようになりました。
<!--/-->

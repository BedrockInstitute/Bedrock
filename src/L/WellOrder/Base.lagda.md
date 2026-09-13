<!--en-->
# Strict well-orders and least-element search

Suppose a property of natural numbers is known to hold of at least one number. Then it holds of a least number: among the witnesses there is a smallest one. For a general strict well-order, this chapter uses a descent from a known witness. If some strictly smaller element is still a witness, move down to it and repeat. If not, the current element is least. Well-foundedness of the order guarantees this descent cannot continue forever, so the process stops at a least witness.

This chapter turns that argument into a theorem for any strict well-order, not just the natural numbers. Two pieces of order data carry the proof. First, a comparison of two elements has three possible outcomes, strictly below, equal, or strictly above, and representing these outcomes as explicit data lets a proof reason by cases on them; this is what shows a least witness, once found, is unique, since two least witnesses cannot be strictly below each other. Second, well-foundedness is presented as an accessibility certificate for every element, and it is these certificates, handed down step by step, that let the descent be carried out inside type theory. One genuinely classical ingredient remains in this proof: at each step the search decides whether some smaller witness still exists, and that mere-existence question is settled by excluded middle at the level where it is asked. Everything else, including the uniqueness of the result, is constructive.

The chapter first defines comparison data, then states the order laws together, then proves that being least is a proposition and that least witnesses exist. It closes by assembling the strict order on the natural numbers into an instance, so the search applies there concretely.
<!--zh-->
# 严格良序与最小元搜索

设自然数的一个性质至少对一个数成立。那么它对一个最小的数成立：见证之中必有最小者。对于一般的严格良序，本章采用从已知见证出发的下降论证：若仍有严格更小的元素满足该性质，就移到那里重复；若没有，当前元素即为最小。序的良基性保证这样的下降不可能永远继续，因此过程会停在某个最小见证处。

本章把这个论证推广成对任意严格良序成立的定理，而不只对自然数。两块序数据承担证明。其一，两个元素的比较有三种结果：严格小于、相等、严格大于；把这三种结果表示为显式数据，证明便可按情形推理，这正说明极小见证一旦找到便唯一，因为两个极小见证不可能彼此严格更小。其二，良基性表述为每个元素的可及性证书，正是这些证书逐层下传，使下降得以在类型论中执行。本章的这个证明还使用一个经典成分：每一步都判定是否仍存在更小的见证，这个单纯存在性问题由所问层级上的排中律裁决。其余部分，包括结果的唯一性，都是构造性的。

本章先定义比较数据，再把序定律一并陈述，然后证明「是极小元」是命题且极小见证存在，最后把自然数上的严格序组装成实例，使搜索在那里具体可用。
<!--ja-->
# 狭義整列順序と最小要素の探索

自然数のある性質が少なくとも一つの数で成り立つとします。すると、その性質は最小の数で成り立ちます。証人のうちには最小のものがあるからです。一般の狭義整列順序に対して、本章は既知の証人からの降下を用います。まだ真に小さい要素が性質を満たすならそこへ移って繰り返し、満たさなければ現在の要素が最小です。順序の整礎性がこの降下は永遠に続かないことを保証し、探索は最小証人で止まります。

本章は、この議論を自然数だけでなく任意の狭義整列順序に対する定理にします。証明を支えるのは二つの順序のデータです。第一に、二つの要素の比較には真に小さい・等しい・真に大きいという三つの結果があり、これらを明示的なデータとして表せば証明は場合分けで推論できます。これが最小証人の一意性を示すもので、二つの最小証人は互いに真に小さいことはあり得ません。第二に、整礎性は各要素への到達可能性の証明書として表され、この証明書を一歩ごとに受け渡すことで、降下を型理論の中で実行できます。本章のこの証明には古典的な成分が一つあります。各段階で、より小さい証人がまだ存在するかどうかを判定し、この単なる存在の問いを、それが問われるレベルでの排中律によって決着します。結果の一意性を含め、それ以外はすべて構成的です。

本章はまず比較データを定義し、次に順序の法則をまとめて述べ、さらに「最小であること」が命題であることと最小証人の存在を示し、最後に自然数上の狭義順序を実例として組み立てて、探索がそこで具体的に使えるようにします。
<!--/-->

<!--en-->
The carrier of the order and the order relation itself need not sit at the same universe level: a relation may be valued at a fixed level `ℓₚ` while its carrier lives at any level. This separation is a matter of generality, not of the mathematics of the search; the least-element argument below never compares levels.

Two mathematical notions then do the work. Well-foundedness is phrased through the accessibility predicate `Acc`{.Agda}: an element is accessible when every strictly smaller element is accessible in turn, and a relation is well founded when every element is accessible. These accessibility certificates are what license the recursive descent of the search. Trichotomy, in turn, is the comparison data that makes least witnesses unique. The natural-number order supplies both notions already, so its instance requires assembly rather than a fresh proof.
<!--zh-->
序的载体与序关系本身不必处在同一宇宙层级：关系可以取值于固定层级 `ℓₚ`，而载体住在任意层级。这种区分只关乎一般性，与搜索的数学无关；下文的最小元论证从不比较层级。

随后真正工作的是两个数学概念。良基性通过可及性谓词 `Acc`{.Agda} 表述：一个元素可及，意思是每个严格更小的元素也依次可及；每个元素都可及时，关系是良基的。正是这些可及性证书为搜索的递归下降提供许可。三歧性则是使极小见证唯一的比较数据。自然数上的序已经同时具备这两个概念，因此它的实例只需组装而无需另证。
<!--ja-->
順序の台と順序関係そのものは、同じ宇宙レベルに住む必要はありません。関係は固定レベル `ℓₚ` で値をとり、台は任意のレベルに住んでいてよい。この区別は一般性の問題であって探索の数学とは無関係であり、以下の最小要素の議論がレベルを比較することはありません。

そのうえで、実際に働くのは二つの数学的概念です。整礎性は到達可能性の述語 `Acc`{.Agda} で表します。ある要素が到達可能とは、真に小さい各要素がさらに到達可能であることであり、すべての要素が到達可能なとき関係は整礎です。この到達可能性の証明書こそが、探索の再帰的降下を許すものです。三分性はその一方で、最小証人の一意性を支える比較データです。自然数上の順序はこの二つをすでに備えているため、その実例は組み立てだけで新たな証明を要しません。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module L.WellOrder.Base {ℓₚ : Level} where
```

<!--en-->
The search must also live with incomplete information. The hypothesis says only that the set of witnesses is merely inhabited, an inhabitant of `∥_∥₁`{.Agda}, and at each descent step the question whether some strictly smaller witness remains is again a mere existence statement. Neither assumption hands over a chosen witness, and neither needs to: propositional truncation may be eliminated because the goal, being a least element, is a proposition, and that propositionhood is proved in this chapter. Excluded middle enters precisely to turn each such existence question into a two-way decision, a proof or a refutation.
<!--zh-->
搜索还必须与不完整的信息共处。假设只说见证的集合「仅仅非空」，即 `∥_∥₁`{.Agda} 的一个居民；而每一步下降所问的「是否仍有严格更小的见证」同样是单纯存在陈述。这两处都不交出被选定的见证，也不需要交出：命题截断之所以能消去，是因为目标「作为极小元」是命题，而这一点将在本章证明。排中律恰好用来把每个这样的存在问题变成证明或反驳的两路判定。
<!--ja-->
探索はさらに、不完全な情報のもとで行われなければなりません。仮定が言うのは、証人の集合が「単に非空」であること、つまり `∥_∥₁`{.Agda} の住人が存在することだけです。また各降下段階で問われる「真に小さい証人がまだ残っているか」も、やはり単なる存在文です。どちらも選ばれた証人を手渡すわけではなく、手渡す必要もありません。命題的な切り捨ての除去が許されるのは、目標である「最小要素であること」が命題だからであり、これは本章で示します。排中律が入るのはまさに、そのような存在の問いを証明か反証かへの二路判定に変える箇所です。
<!--/-->

```agda

open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Nat.Order using ( _<_; <-trans; ¬m<m; <-wellfounded; _≟_ )
import Cubical.Data.Nat.Order as NatOrder
import Cubical.HITs.PropositionalTruncation as PT
```

<!--en-->
This logical situation fixes the order of the proof. Before eliminating either truncation, we first show that leastness at a point is a proposition and that the total type of least witnesses is also a proposition. Trichotomy supplies the path between any two candidates, while impossible strict comparisons are discharged by their minimality. Only after that uniqueness argument is the descent allowed to consume the merely inhabited hypothesis.
<!--zh-->
这个逻辑情形决定了证明的次序。在消去任一截断之前，先证明固定一点上的极小性是命题，并证明极小见证的总类型也是命题。三歧性给出任意两个候选之间的路径，而与极小性冲突的严格比较则被排除。只有完成这段唯一性论证之后，下降过程才能消耗仅仅非空的假设。
<!--ja-->
この論理的状況が証明の順序を定めます。いずれかの切り捨てを除去する前に、まず固定した点での最小性が命題であり、最小証人の全体型も命題であることを示します。三分性が任意の二候補の間のパスを与え、最小性と両立しない狭義比較は排除されます。この一意性の議論を終えて初めて、降下は単に非空であるという仮定を消費できます。
<!--/-->

```agda
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ )
open import Cubical.Relation.Nullary using ( isProp¬ ) renaming ( ¬_ to ¬ᵗ_ )
import Cubical.Data.Empty as Empty
```

<!--en-->
A decision, when it exists, returns either a proof or a refutation. The two-way sum with its constructors provides exactly this shape of verdict, and it will carry the choice that excluded middle hands to the descent.
<!--zh-->
判定 (若存在) 返回证明或反驳之一。带两个构造子的二元和恰好给出这种裁决的形状，它将承载排中律递交给下降过程的那个选择。
<!--ja-->
判定 (存在するならば) は証明か反証のどちらかを返します。二つの構成子をもつ直和型はまさにこの形の判定を与え、排中律が降下に渡す選択を担うことになります。
<!--/-->

```agda
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
```

<!--en-->
## Trichotomy, as data

Comparing two elements of a strict well-order has three possible outcomes, and later proofs need to reason by cases on which outcome occurred. We therefore represent the comparison as an inductive type with three constructors, each carrying its own evidence: a proof of the strict relation in one direction, an equality, or a proof in the other direction. Because the three alternatives are constructor tags rather than a nested sum of types, a proof can inspect the comparison directly and name the case it is in. Each of the three types may live at its own universe level, and the comparison type lands at the maximum of the three.
<!--zh-->
## 作为数据的三歧

比较严格良序的两个元素有三种可能结果，后续证明需要按出现的结果分情形推理。因此我们把比较表示为带三个构造子的归纳类型，各构造子携带自己的证据：一个方向严格关系的证明、一个相等，或另一方向的证明。由于三个选项是构造子标签而非嵌套的和类型，证明可以直接检查比较并指出自己所在的情形。三个类型各自可处于自己的宇宙层级，比较类型落在三者的最大层级。
<!--ja-->
## データとしての三分性

狭義整列順序の二つの要素の比較には三つの可能的な結果があり、後の証明はどの結果が起きたかで場合分けして推論する必要があります。そこで比較を、三つの構成子をもつ帰納型として表します。各構成子はそれぞれの証拠、すなわち一方方向の狭義関係の証明、等式、あるいは他方方向の証明をデータとしてもたせます。三つの選択肢は入れ子の直和ではなく構成子のタグとして表されるため、証明は比較を直接検査し、自分がどの場合にいるかを名指せます。三つの型はそれぞれ独自の宇宙レベルに住んでよく、比較型は三つの最大値に住みます。
<!--/-->

<!--en-->
The three constructors `lt`, `eq` and `gt` correspond to the three outcomes. The equality branch carries a proof of the path `a ≡ b`{.Agda} between the carrier elements, rather than returning a bare tag that merely reports equality. For the natural-number example this type will be filled by translating the library's three-way decision on `a ≟ b`{.Agda}, constructor by constructor.
<!--zh-->
三个构造子 `lt`、`eq`、`gt` 对应三种结果。相等分支携带载体元素之间路径 `a ≡ b`{.Agda} 的证明，而不是只返回一个报告相等的标签。对自然数例子，这个类型将通过把库中对 `a ≟ b`{.Agda} 的三路判定逐构造子翻译来填充。
<!--ja-->
三つの構成子 `lt`、`eq`、`gt` が三つの結果に対応します。等号の分岐は、等しいと報告するだけのタグではなく、台の要素間のパス `a ≡ b`{.Agda} の証明を運びます。自然数の例では、この型はライブラリの `a ≟ b`{.Agda} に対する三路判定を構成子ごとに翻訳して埋められます。
<!--/-->

```agda
data Tri {ℓ₁ ℓ₂ ℓ₃ : Level} (A : Type ℓ₁) (B : Type ℓ₂) (C : Type ℓ₃)
       : Type (ℓ-max ℓ₁ (ℓ-max ℓ₂ ℓ₃)) where
  lt : A → Tri A B C
  eq : B → Tri A B C
  gt : C → Tri A B C
```

<!--en-->
## The bundle

A strict well-order is not just a relation: it is a relation together with the laws that make least-element search work. We gather the relation, trichotomy, irreflexivity, transitivity and well-foundedness into a single record `SWO`{.Agda} over a carrier `A`. Naming this interface keeps all later constructions independent of how any particular order happens to be built; the natural-number order given later in this chapter and any other instance supply the same five fields. The carrier and the relation may sit at different universe levels: `A` lives at level `ℓc`, while the relation takes values in `Type ℓₚ`{.Agda}. Since the type of such relation values itself lies one universe higher, the record lives at `ℓ-max ℓc (ℓ-suc ℓₚ)`{.Agda}.
<!--zh-->
## 束

严格良序不只是一个关系：它是一个关系连同使最小元搜索得以运作的定律。我们把关系、三歧性、非自反性、传递性与良基性收进载体 `A` 上的单一记录 `SWO`{.Agda}。为这个接口命名，使后续构造不依赖任何具体序的构造方式；本章稍后给出的自然数序与其他实例都提供同样的五个字段。载体与关系可处于不同宇宙层级：`A` 住在层级 `ℓc`，关系取值于 `Type ℓₚ`{.Agda}。由于这种关系值的类型本身位于高一层宇宙，记录位于 `ℓ-max ℓc (ℓ-suc ℓₚ)`{.Agda}。
<!--ja-->
## 狭義整列順序の構造

狭義整列順序は単なる関係ではありません。最小要素探索を機能させる法則を伴った関係です。関係、三分性、非反射性、推移性、整礎性を、台 `A` の上の単一のレコード `SWO`{.Agda} にまとめます。このインターフェースに名前を与えることで、以後の構成は特定の順序の作られ方に依存しなくなります。本章の後半で与える自然数の順序も他の実例も、同じ五つのフィールドを供給します。台と関係は異なる宇宙レベルに住んでよく、`A` はレベル `ℓc` に住み、関係は `Type ℓₚ`{.Agda} に値をとります。このような関係値の型そのものは一つ上の宇宙に住むため、レコードは `ℓ-max ℓc (ℓ-suc ℓₚ)`{.Agda} に住みます。
<!--/-->

<!--en-->
The first two fields are the relation and its trichotomy. For any two elements `a` and `b`, `tri∙`{.Agda} returns comparison data: either `a <∙ b`{.Agda}, a path `a ≡ b`{.Agda}, or `b <∙ a`{.Agda}. Trichotomy is what makes least elements unique later, since two candidates cannot be strictly below each other.
<!--zh-->
前两个字段是关系及其三歧性。对任意两个元素 `a` 与 `b`，`tri∙`{.Agda} 返回比较数据：`a <∙ b`{.Agda}、路径 `a ≡ b`{.Agda}、或 `b <∙ a`{.Agda}。三歧性正是稍后极小元唯一性的来源，因为两个候选不可能彼此严格更小。
<!--ja-->
最初の二つのフィールドは関係とその三分性です。任意の二要素 `a` と `b` に対し、`tri∙`{.Agda} は比較データを返します。`a <∙ b`{.Agda}、パス `a ≡ b`{.Agda}、または `b <∙ a`{.Agda} のいずれかです。三分性は後で最小要素の一意性を支えるもので、二人の候補が互いに真に小さいことはあり得ません。
<!--/-->

```agda
record SWO {ℓc : Level} (A : Type ℓc) : Type (ℓ-max ℓc (ℓ-suc ℓₚ)) where
  field
    _<∙_   : A → A → Type ℓₚ
    tri∙   : (a b : A) → Tri (a <∙ b) (a ≡ b) (b <∙ a)
    irr∙   : (a : A) → ¬ᵗ a <∙ a
```

<!--en-->
The remaining three fields are the order laws. `irr∙`{.Agda} says no element is below itself, `trans∙`{.Agda} is transitivity, and `wf∙`{.Agda} asserts that every element of `A` is accessible for the relation. Accessibility is the inductive principle behind well-founded recursion: given `acc rs`{.Agda} at `a`, the function `rs`{.Agda} produces accessibility data for every smaller element. It is precisely this supply, handed down step by step, that makes the descent in the search terminate.
<!--zh-->
其余三个字段是序定律。`irr∙`{.Agda} 说没有元素小于自身，`trans∙`{.Agda} 是传递性，而 `wf∙`{.Agda} 断言 `A` 的每个元素对该关系都是可及的。可及性是良基递归背后的归纳原理：给定 `a` 处的 `acc rs`{.Agda}，函数 `rs`{.Agda} 对每个更小的元素给出可及性数据。正是这份逐层下传的供给使搜索中的下降得以终止。
<!--ja-->
残りの三つのフィールドは順序の法則です。`irr∙`{.Agda} はどの要素も自分自身より小さくないことを言い、`trans∙`{.Agda} は推移性、そして `wf∙`{.Agda} は `A` のすべての要素がこの関係について到達可能であると主張します。到達可能性は整礎再帰の背後にある帰納原理です。`a` における `acc rs`{.Agda} が与えられると、関数 `rs` はより小さい各要素に対して到達可能性のデータを生み出します。段階ごとに受け渡されるこの供給こそが、探索の降下を停止させるものです。
<!--/-->

```agda
    trans∙ : (a b c : A) → a <∙ b → b <∙ c → a <∙ c
    wf∙    : WellFounded _<∙_
```

<!--en-->
## Least elements

Fix a strict well-order `w` on `A`. For a predicate `P` valued in propositions, an element `a` is least for `P` when it satisfies `P` and no element satisfying `P` is strictly below it. Being least is a proposition, and so is the type of least elements as a whole: given two, trichotomy excludes both strict cases and forces equality. These two propositionhood facts are the hinge of the chapter, because a proposition-valued goal may absorb propositional truncation. That is what will let the search below turn a merely inhabited subset into an actual least element.
<!--zh-->
## 极小元

固定 `A` 上的一个严格良序 `w`。对取值于命题的谓词 `P`，元素 `a` 是 `P` 的极小元，当它满足 `P` 且没有满足 `P` 的元素严格位于其下。「是极小元」是命题，「极小元」这个类型整体也是：给定两个，三歧排除两个严格情形并强制相等。这两条命题性事实是本章的关键，因为命题值的目标可以吸收命题截断。正是这一点将让下文的搜索把仅仅非空的子集变成真正的极小元。
<!--ja-->
## 最小要素

`A` 上の狭義整列順序 `w` を固定します。命題値をとる述語 `P` に対し、要素 `a` が `P` の最小要素であるとは、`P` を満たし、かつ `P` を満たす要素で真に `a` より小さいものが存在しないことです。最小であることは命題であり、「最小要素」の型全体もそうです。二つ与えられれば、三分性が両方の真のケースを排除し、等しさを強制します。この二つの命題性の事実が本章の要です。命題値の目標は命題的な切り捨てを吸収できるからです。これにより後の探索が、単に非空なだけの部分集合から実際の最小要素を取り出せるようになります。
<!--/-->

<!--en-->
The definition takes `P` as a family of `hProp`{.Agda}: each fiber is packaged with a certificate that it is a proposition. `⟨ P a ⟩`{.Agda} projects the underlying type, so `IsLeast P a`{.Agda} is the pair of a witness that `a` satisfies `P` and a function sending every other witness `b`, together with its certificate `⟨ P b ⟩`{.Agda}, to a refutation of `b <∙ a`{.Agda}. Note that the leastness bound is required only of elements that actually satisfy the predicate; elements outside the subset may lie anywhere.
<!--zh-->
定义把 `P` 取为 `hProp`{.Agda} 值的族：每根纤维连同「它是命题」的证书一起打包。`⟨ P a ⟩`{.Agda} 投影出底层类型，于是 `IsLeast P a`{.Agda} 是一个二元组：`a` 满足 `P` 的见证，加上一个函数，它把每个其他见证 `b` 连同其证书 `⟨ P b ⟩`{.Agda} 送到对 `b <∙ a`{.Agda} 的反驳。注意最小性约束只要求在实际满足谓词的元素上成立；子集之外的元素可以位于任何位置。
<!--ja-->
定義では `P` を `hProp`{.Agda} 値の族として取ります。各ファイバーは「それが命題である」という証明書とともに梱包されています。`⟨ P a ⟩`{.Agda} が基礎型を射影するので、`IsLeast P a`{.Agda} は、`a` が `P` を満たすことの証人と、他の各証人 `b` をその証明書 `⟨ P b ⟩`{.Agda} とともに `b <∙ a`{.Agda} の反証へ送る関数との対です。最小性の条件が要求されるのは実際に述語を満たす要素についてだけであり、部分集合の外の要素はどこにあってもよいことに注意してください。
<!--/-->

```agda
module _ {ℓc : Level} {A : Type ℓc} (w : SWO {ℓc} A) where
  open SWO w

  IsLeast : {ℓ'' : Level} → (A → hProp ℓ'') → A → Type (ℓ-max ℓc (ℓ-max ℓₚ ℓ''))
  IsLeast P a = ⟨ P a ⟩ × ((b : A) → ⟨ P b ⟩ → ¬ᵗ b <∙ a)

  isPropIsLeast : {ℓ'' : Level} (P : A → hProp ℓ'') (a : A) → isProp (IsLeast P a)
```

<!--en-->
Both components of `IsLeast P a`{.Agda} are propositions: the first by the certificate packed into `P a`, the second because a negation-valued function into propositions is propositional. Hence `IsLeast P a`{.Agda} is a proposition, by closing the pair under products of propositions. For the total type of least elements, `Σ≡Prop`{.Agda} identifies two pairs as soon as their first components agree, provided the second is propositional; that reduction is exactly what the auxiliary `decide` carries out.
<!--zh-->
`IsLeast P a`{.Agda} 的两个分量都是命题：第一个由打包进 `P a` 的证书保证，第二个是因为取值于命题的否定值函数是命题。于是借助「命题的二元组仍是命题」把配对闭合，`IsLeast P a`{.Agda} 是命题。对极小元的整体类型，`Σ≡Prop`{.Agda} 在第二分量是命题时，只要两个二元组的第一分量相等就识别它们；这一化归正是辅助函数 `decide` 所执行的。
<!--ja-->
`IsLeast P a`{.Agda} の両成分は命題です。第一は `P a` に梱包された証明書により、第二は命題値を返す否定値関数が命題であることによります。したがって「命題の対は命題」という閉じ方により、`IsLeast P a`{.Agda} は命題です。最小要素全体の型については、`Σ≡Prop`{.Agda} は第二成分が命題であるとき、第一成分が一致すれば二つの対を同一視します。この帰着をまさに行うのが補助関数 `decide` です。
<!--/-->

```agda
  isPropIsLeast P a = isProp× (snd (P a)) (isPropΠ λ b → isPropΠ λ _ → isProp¬ _)

  isPropLeastOf : {ℓ'' : Level} (P : A → hProp ℓ'')
                → isProp (Σ[ a ∈ A ] IsLeast P a)
  isPropLeastOf P (m , pm , minm) (m' , pm' , minm') =
    Σ≡Prop (isPropIsLeast P) (decide (tri∙ m m'))
```

<!--en-->
To compare two least elements `m` and `m'`, `decide` inspects `tri∙ m m'`{.Agda}. If `m <∙ m'`{.Agda}, then `m'` is least and `m` satisfies the predicate, so `m` should not be strictly below `m'`: contradiction, via `Empty.rec`{.Agda}, which discharges any goal from an impossible case. The symmetric case is analogous. In the remaining case the comparison itself hands over the path `e : m ≡ m'`{.Agda}, which is returned directly. Together with `Σ≡Prop`{.Agda}, this proves `isPropLeastOf`{.Agda}: the type of least witnesses for `P` is a proposition, so leastness, once it exists, is unique.
<!--zh-->
为比较两个极小元 `m` 与 `m'`，`decide` 检查 `tri∙ m m'`{.Agda}。若 `m <∙ m'`{.Agda}，则 `m'` 是极小元而 `m` 满足谓词，于是 `m` 不应严格小于 `m'`：矛盾，经由 `Empty.rec`{.Agda}，它从不可能情形导出任何目标。对称情形类似。剩下的情形中比较本身交出路径 `e : m ≡ m'`{.Agda}，直接返回即可。结合 `Σ≡Prop`{.Agda}，这证明了 `isPropLeastOf`{.Agda}：`P` 的极小见证类型是命题，故极小性一旦存在便唯一。
<!--ja-->
二つの最小要素 `m` と `m'` を比較するために、`decide` は `tri∙ m m'`{.Agda} を検査します。`m <∙ m'`{.Agda} なら、`m'` は最小であり `m` は述語を満たすので、`m` が真に `m'` より小さいはずがありません。矛盾です。これは不可能な場合から任意の目標を導く `Empty.rec`{.Agda} によります。対称な場合も同様です。残る場合では、比較そのものがパス `e : m ≡ m'`{.Agda} を渡してくるので、それを直接返します。`Σ≡Prop`{.Agda} と合わせて、これが `isPropLeastOf`{.Agda} を証明します。`P` の最小証人の型は命題であり、したがって最小性は存在すれば一意です。
<!--/-->

```agda
    where
    decide : Tri (m <∙ m') (m ≡ m') (m' <∙ m) → m ≡ m'
    decide (lt m<m') = Empty.rec (minm' m pm m<m')
    decide (eq e)    = e
    decide (gt m'<m) = Empty.rec (minm m' pm' m'<m)
```

<!--en-->
Here is the search itself. It takes excluded middle at the level where the questions are asked, a predicate `P`, and a mere inhabitant of the subset of witnesses, and returns an actual pair of a least witness with its leastness data. The argument descends along the well-order: from any starting witness, ask whether some strictly smaller element still satisfies `P`. If yes, recurse there, which terminates because each recursion moves strictly down and accessibility is handed along. If no, the current element is least by definition. Each step needs a classical decision of a proposition built from the arbitrary predicate, and that is the only place excluded middle enters; the statement and the order laws themselves remain constructive.
<!--zh-->
现在给出搜索本身。它取所问层级上的排中律、谓词 `P`，以及见证子集的单纯居民，返回真正的二元组：极小见证连同其最小性数据。论证沿良序下降：从任一初始见证出发，问是否有严格更小的元素仍满足 `P`。若有，就在那里递归；由于每次递归严格向下移动且可及性逐层下传，这会终止。若无，则当前元素按定义即为极小。每一步都需要对由任意谓词构造的命题作经典判定，这正是排中律进入的唯一位置；陈述本身与序定律仍是构造性的。
<!--ja-->
これが探索そのものです。問いが発せられるレベルでの排中律、述語 `P`、そして証人の部分集合の単なる住人を受け取り、最小性のデータを伴った実際の最小証人の対を返します。議論は整列順序に沿って降下します。任意の出発点の証人から、「より真に小さく `P` を満たす要素があるか」を問い、あればそこで再帰します。再帰のたびに真に下へ移動し、到達可能性が受け渡されるため、これは停止します。なければ、現在の要素が定義により最小です。各段階では任意の述語から構成される命題の古典的判定が必要であり、これが排中律が入る唯一の場所です。主張自体と順序の法則は構成的なままです。
<!--/-->

<!--en-->
The elimination of the truncation in the hypothesis is legitimate because the target `Σ[ a ∈ A ] IsLeast P a`{.Agda} was shown to be a proposition by `isPropLeastOf`{.Agda}. So from the merely inhabited subset we may extract some starting witness `a₀` with its certificate, and then begin the descent `go a₀ (wf∙ a₀) pa₀`{.Agda}: the accessibility data `wf∙ a₀`{.Agda}, part of the bundle, is the fuel for the recursion. Note that the starting witness is arbitrary; the descent, not the choice of starting point, produces the least element.
<!--zh-->
假设中截断的消去是合法的，因为目标 `Σ[ a ∈ A ] IsLeast P a`{.Agda} 已被 `isPropLeastOf`{.Agda} 证明为命题。于是可从仅仅非空的子集中提取某个初始见证 `a₀` 及其证书，然后开始下降 `go a₀ (wf∙ a₀) pa₀`{.Agda}：作为束一部分的可及性数据 `wf∙ a₀`{.Agda} 正是递归的燃料。注意初始见证是任意的；产出极小元的是下降过程，而非起点的选取。
<!--ja-->
仮定の切り捨ての除去が正当なのは、目標 `Σ[ a ∈ A ] IsLeast P a`{.Agda} が `isPropLeastOf`{.Agda} によって命題と示されているからです。したがって、単に非空な部分集合から出発点の証人 `a₀` とその証明書を取り出し、降下 `go a₀ (wf∙ a₀) pa₀`{.Agda} を始められます。束の一部である到達可能性のデータ `wf∙ a₀`{.Agda} が再帰の燃料です。出発点の証人は任意であることに注意してください。最小要素を生み出すのは出発点の選択ではなく降下のほうです。
<!--/-->

```agda
  leastOf : {ℓ'' : Level} → LEM (ℓ-max ℓc (ℓ-max ℓₚ ℓ''))
          → (P : A → hProp ℓ'')
          → ∥ Σ[ a ∈ A ] ⟨ P a ⟩ ∥₁ → Σ[ a ∈ A ] IsLeast P a
  leastOf {ℓ''} lem P =
    PT.rec (isPropLeastOf P) (λ { (a₀ , pa₀) → go a₀ (wf∙ a₀) pa₀ })
```

<!--en-->
The auxiliary `go` receives an element `a`, its accessibility data, and a certificate that `a` satisfies `P`; it returns a least witness. At each step it forms the proposition `Smaller`: whether there merely exists an element strictly below `a` that still satisfies `P`. This is an `hProp`{.Agda} because its underlying type is a propositional truncation, so excluded middle applies to it; the level bookkeeping ensures the decision is taken at exactly the level of the data involved.
<!--zh-->
辅助函数 `go` 接收元素 `a`、其可及性数据、以及 `a` 满足 `P` 的证书，返回一个极小见证。每一步它构造命题 `Smaller`：是否「仅仅存在」一个严格位于 `a` 之下且仍满足 `P` 的元素。由于它的底层类型是命题截断，它是一个 `hProp`{.Agda}，排中律因此适用；层级簿记保证判定恰好在所涉数据所在的层级作出。
<!--ja-->
補助関数 `go` は要素 `a`、その到達可能性のデータ、そして `a` が `P` を満たすことの証明書を受け取り、最小証人を返します。各段階で命題 `Smaller` を構成します。すなわち、真に `a` より小さく `P` を満たす要素が「単に存在する」かどうかです。その基礎型は命題的な切り捨てなのでこれは `hProp`{.Agda} であり、排中律が適用できます。レベルの帳簿づけにより、判定はまさに関係するデータのレベルで行われます。
<!--/-->

```agda
    where
    go : (a : A) → Acc _<∙_ a → ⟨ P a ⟩ → Σ[ m ∈ A ] IsLeast P m
    go a (acc rs) pa = decide (lem (Smaller , squash₁))
      where
      Smaller : Type (ℓ-max ℓc (ℓ-max ℓₚ ℓ''))
```

<!--en-->
Applying `lem` to `Smaller` yields either a proof or a refutation, and `decide` turns either verdict into a least witness. In the positive case the truncated statement is again eliminated into the proposition-valued goal, handing a genuine element `b` strictly below `a` with `P b`; the recursion continues at `b` using the accessibility function `rs`, which is defined precisely on the elements below `a`. This is the descent step, and the accessibility data is what guarantees it cannot go on forever.
<!--zh-->
把 `lem` 用于 `Smaller` 得到证明或反驳，`decide` 把两种裁决都变成极小见证。肯定情形中，截断陈述再次消去到命题值的目标，交出真正的元素 `b`，严格小于 `a` 且满足 `P b`；递归借助可及性函数 `rs` 在 `b` 处继续，而 `rs` 恰好在 `a` 之下的元素上有定义。这就是下降步，正是可及性数据保证它不会无限继续。
<!--ja-->
`lem` を `Smaller` に適用すると証明か反証が得られ、`decide` はどちらの判定も最小証人に変えます。肯定の場合、切り捨てられた主張は再び命題値の目標へと除去され、真に `a` より小さく `P b` を満たす実際の要素 `b` が渡されます。再帰は到達可能性関数 `rs` を用いて `b` で続きます。`rs` はまさに `a` より下の要素の上で定義されています。これが降下の一段であり、これが無限に続かないことを保証するのは到達可能性のデータです。
<!--/-->

```agda
      Smaller = ∥ Σ[ b ∈ A ] ((b <∙ a) × ⟨ P b ⟩) ∥₁
      decide : Smaller ⊎ (Smaller → Empty.⊥) → Σ[ m ∈ A ] IsLeast P m
      decide (inl q) = PT.rec (isPropLeastOf P)
        (λ { (b , (b<a , pb)) → go b (rs b b<a) pb }) q
      decide (inr ¬q) = a , (pa , λ b pb b<a → ¬q ∣ b , (b<a , pb) ∣₁)
```

<!--en-->
## The natural numbers, well-ordered

The usual strict order on the natural numbers satisfies all four laws of the bundle, and its well-foundedness follows by induction on the upper number. This section assembles `natOrder : SWO {ℓ-zero} ℕ`{.Agda}; a concrete consumer, `L.Choice.FiniteStageOrders`{.Agda}, calls `leastOf natOrder`{.Agda} to pick the earliest natural-numbered finite stage witnessing a property. The library already supplies every ingredient about the usual order, so the bundle is assembled rather than proved: the relation, irreflexivity, transitivity and well-foundedness are the library's own, and the trichotomy is the library's three-way decision procedure with its answer renamed into the chapter's constructors.

One genuine step remains. The order on the natural numbers lives at the bottom universe level, while the relation of a bundle is valued at the fixed level `ℓₚ`; each comparison is therefore wrapped in `Lift`{.Agda}, which changes only where the type lives and nothing about its inhabitants.
<!--zh-->
## 自然数，良序化

自然数上的通常严格序满足束的全部四条定律，其良基性对上侧自然数作归纳即得。本节组装 `natOrder : SWO {ℓ-zero} ℕ`{.Agda}；一个具体使用处 `L.Choice.FiniteStageOrders`{.Agda} 调用 `leastOf natOrder`{.Agda}，从以自然数编号的有限层中挑出见证某性质的最早层。关于通常的序，库中已有全部所需材料，因此这个束只需组装而无需另行证明：关系、非自反性、传递性与良基性直接取自库，三歧性则是库的三路判定程序、其答案按本章构造子重新命名。

剩下的一步是真正的调整。自然数上的序处在最底宇宙层级，而束的关系取值于固定层级 `ℓₚ`；因此每次比较都要用 `Lift`{.Agda} 包一层，它只改变类型所在的层级，不改变其居民。
<!--ja-->
## 自然数の整列順序

自然数上の通常の狭義順序は束の四つの法則をすべて満たし、その整礎性は上側の自然数についての帰納で従います。この節では `natOrder : SWO {ℓ-zero} ℕ`{.Agda} を組み立てます。具体的な利用箇所である `L.Choice.FiniteStageOrders`{.Agda} は `leastOf natOrder`{.Agda} を呼び、自然数で番号づけられた有限段階のうち、性質を証明する最も早いものを選び出します。通常の順序について必要な材料はすべてライブラリが供給するため、この束は証明するのではなく組み立てるだけです。関係・非反射性・推移性・整礎性はライブラリのものをそのまま使い、三分性はライブラリの三路判定の手続きの答えを本章の構成子に名前を変えたものです。

残る真の調整が一つあります。自然数の順序は最下層の宇宙レベルに住む一方、束の関係は固定レベル `ℓₚ` で値をとります。そこで各比較を `Lift`{.Agda} で包みます。これは型の住むレベルを変えるだけで、住人については何も変えません。
<!--/-->

<!--en-->
`liftAcc` transports accessibility data from the plain order to its lifted copy. Given `acc r`{.Agda} at `n`, it returns `acc`{.Agda} of a function that, from `m` below `n` in the lifted order, first unwraps the lifted proof with `lower`{.Agda} and recurses at `m`. This is structural recursion on the accessibility argument, the same pattern that will drive `leastOf`. Note the two universe arguments of `Lift`{.Agda}: the source stays at zero and only the target is `ℓₚ`.
<!--zh-->
`liftAcc` 把可及性数据从原本的序搬运到其抬升副本。给定 `n` 处的 `acc r`{.Agda}，它返回某个函数的 `acc`{.Agda}：该函数从抬升序中位于 `n` 之下的 `m` 出发，先用 `lower`{.Agda} 拆开抬升的证明，再在 `m` 处递归。这是对可及性参数的结构递归，与稍后驱动 `leastOf` 的模式相同。注意 `Lift`{.Agda} 的两个宇宙参数：源层级保持为零，只有目标层级是 `ℓₚ`。
<!--ja-->
`liftAcc` は到達可能性のデータを元の順序からその持ち上げられたコピーへ運びます。`n` における `acc r`{.Agda} が与えられると、持ち上げられた順序で `n` より下の `m` に対し、まず `lower`{.Agda} で持ち上げられた証明をほどいてから `m` で再帰する関数の `acc`{.Agda} を返します。これは到達可能性の引数に対する構造的再帰であり、後に `leastOf` を駆動するのと同じパターンです。`Lift`{.Agda} が二つの宇宙引数をもつことに注意してください。ソースはゼロのままで、ターゲットだけが `ℓₚ` です。
<!--/-->

```agda
liftAcc : (n : ℕ) → Acc _<_ n → Acc (λ a b → Lift {ℓ-zero} {ℓₚ} (a < b)) n
liftAcc n (acc r) = acc (λ m h → liftAcc m (r m (lower h)))

natOrder : SWO {ℓ-zero} ℕ
natOrder = record
  { _<∙_   = λ a b → Lift (a < b)
```

<!--en-->
With the lifted accessibility in hand, `natOrder` is filled in field by field. The relation sends `a` and `b` to `Lift (a < b)`{.Agda}; irreflexivity unwraps its hypothesis and applies the library's `¬m<m`{.Agda}; transitivity unwraps both proofs, composes them with the library's `<-trans`{.Agda}, and re-lifts the result; well-foundedness produces `liftAcc n (<-wellfounded n)`{.Agda} at each `n`. No new mathematics about the natural-number order is proved here, only the level adjustment and the renaming into the bundle's field names.
<!--zh-->
有了抬升后的可及性，`natOrder` 逐字段填入。关系把 `a` 与 `b` 送到 `Lift (a < b)`{.Agda}；非自反性拆开假设并应用库的 `¬m<m`{.Agda}；传递性拆开两个证明，用库的 `<-trans`{.Agda} 复合，再把结果重新抬升；良基性对每个 `n` 给出 `liftAcc n (<-wellfounded n)`{.Agda}。这里没有为自然数序证明任何新数学，只做了层级调整和向束字段名的改写。
<!--ja-->
持ち上げられた到達可能性が手に入れば、`natOrder` はフィールドごとに埋められます。関係は `a` と `b` を `Lift (a < b)`{.Agda} に送り、非反射性は仮定をほどいてライブラリの `¬m<m`{.Agda} を適用し、推移性は二つの証明をほどいてライブラリの `<-trans`{.Agda} で合成してから結果を再度持ち上げ、整礎性は各 `n` に対し `liftAcc n (<-wellfounded n)`{.Agda} を与えます。ここで自然数の順序について新しい数学が証明されるわけではなく、行われるのはレベルの調整と束のフィールド名への名前の付け替えだけです。
<!--/-->

```agda
  ; tri∙   = triOf
  ; irr∙   = λ a h → ¬m<m (lower h)
  ; trans∙ = λ a b c h k → lift (<-trans (lower h) (lower k))
  ; wf∙    = λ n → liftAcc n (<-wellfounded n) }
  where
```

<!--en-->
The trichotomy field is `triOf`, defined in the `where` block. The library's decision procedure `a ≟ b`{.Agda} returns a value of the library's own three-way type `NatOrder.Trichotomy a b`{.Agda}, whose constructors `lt`, `eq` and `gt` carry the same three kinds of evidence as the chapter's `Tri`. So `fromNat` maps constructor to constructor: a strictness proof in either direction is lifted, and an equality is passed through unchanged, since equality of natural numbers needs no level adjustment.
<!--zh-->
三歧字段是 `where` 块中的 `triOf`。库的判定程序 `a ≟ b`{.Agda} 返回库自己的三路类型 `NatOrder.Trichotomy a b`{.Agda} 的值，其构造子 `lt`、`eq`、`gt` 携带与本章 `Tri` 相同的三种证据。于是 `fromNat` 逐构造子映射：任一方向的严格性证明被抬升，而相等性原样通过，因为自然数的相等无需层级调整。
<!--ja-->
三分性のフィールドは `where` ブロックの `triOf` です。ライブラリの判定手続き `a ≟ b`{.Agda} は、ライブラリ自身の三路型 `NatOrder.Trichotomy a b`{.Agda} の値を返します。その構成子 `lt`、`eq`、`gt` は本章の `Tri` と同じ三種類の証拠を運びます。そこで `fromNat` は構成子ごとに写します。どちらの方向の真に小さいことの証明も持ち上げられ、等式はそのまま通ります。自然数の等しさにはレベルの調整が要らないからです。
<!--/-->

```agda
  triOf : (a b : ℕ) → Tri (Lift (a < b)) (a ≡ b) (Lift (b < a))
  triOf a b = fromNat (a ≟ b)
    where
    fromNat : NatOrder.Trichotomy a b → Tri (Lift (a < b)) (a ≡ b) (Lift (b < a))
    fromNat (NatOrder.lt h) = lt (lift h)
```

<!--en-->
The three clauses of `fromNat` complete the translation. Reading them together shows why renaming suffices: the library's comparison data and the chapter's are the same shape, differing only in where the two strictness types live. With this field filled, `natOrder` is a fully assembled bundle, and everything from the previous sections applies to it: given excluded middle, every inhabited proposition-valued predicate on `ℕ` has a unique least witness.
<!--zh-->
`fromNat` 的三个子句完成翻译。合起来读可见为何改名就足够：库的比较数据与本章的形状相同，差别只在两个严格性类型所在的层级。填上这个字段后，`natOrder` 便是完整组装的束，前面各节的结论对它适用：给定排中律，`ℕ` 上每个非空的命题值谓词都有唯一的最小见证。
<!--ja-->
`fromNat` の三つの節が翻訳を完成させます。合わせて読めば、名前の付け替えだけで足りる理由が分かります。ライブラリの比較データと本章のものは同じ形をしており、違いは二つの真に小さいことを表す型の住むレベルだけです。このフィールドが埋まれば、`natOrder` は完全に組み立てられた束となり、前節までの結果が適用されます。排中律が与えられれば、`ℕ` 上の証人をもつ命題値述語には一意な最小の証人が存在します。
<!--/-->

```agda
    fromNat (NatOrder.eq h) = eq h
    fromNat (NatOrder.gt h) = gt (lift h)
```

<!--en-->
## Recap

Strict well-orders can now be passed around as a single structure, compared by trichotomy, and searched for least witnesses. `SWO`{.Agda} gathers the relation with its four laws, and `leastOf`{.Agda} extracts, from any merely inhabited subset, a least witness that is unique up to the path supplied by `isPropLeastOf`{.Agda}. The natural-number instance `natOrder`{.Agda} supports searches over natural-number indices, for instance when a later chapter picks the earliest finite stage of L witnessing a property. Excluded middle enters only as the decision asked at each descent step of the search; the bundle definition, its laws and the natural-number order remain constructive.
<!--zh-->
## 小结

现在，严格良序可以作为一个结构整体传递、以三歧作比较，并搜索最小见证。`SWO`{.Agda} 把关系连同四条定律收在一起，`leastOf`{.Agda} 从任何仅仅非空的子集中取出极小见证，且由 `isPropLeastOf`{.Agda} 提供的路径保证唯一。自然数实例 `natOrder`{.Agda} 支持在自然数索引上搜索，例如后续章节从 L 的有限层中挑选见证某性质的最早层。排中律只在搜索每一步下降所问的判定处进入；束的定义、其定律与自然数序本身仍是构造性的。
<!--ja-->
## まとめ

これで狭義整列順序を一つの構造として受け渡し、三分性で比較し、最小の証人を探索できるようになりました。`SWO`{.Agda} は関係と四つの法則をまとめ、`leastOf`{.Agda} は単に非空なだけの任意の部分集合から最小の証人を取り出します。その一意性は `isPropLeastOf`{.Agda} の供給するパスによって理解されます。自然数の実例 `natOrder`{.Agda} は自然数による添字上の探索を可能にします。例えば後の章では、性質を証明する L の最も早い有限段階を選ぶために使われます。排中律が入るのは探索の各降下段階で問われる判定のところだけです。束の定義、その法則、そして自然数の順序は構成的なままです。
<!--/-->

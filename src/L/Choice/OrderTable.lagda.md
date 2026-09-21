<!--en-->
# An internal table of stage orders

At a constructible ordinal index `α`, the preceding construction already gives a host-level strict well-order on the members of `Lset α`. The purpose of this chapter is to represent its binary comparison by a set inside `L`, so that formulas interpreted in the model can quantify over that relation. The result is conditional on an adequate object-language description of one recursive step and applies when `α` is both an ordinal and constructible. It represents the relation underlying the existing order; it does not yet assert in the object language that this relation is a well-order.
<!--zh-->
# 层序的内部表

在可构造序数层索引 `α` 处，先前的构造已经给出 `Lset α` 的成员上的宿主层严格良序。本章要把它的二元比较表示为 `L` 内部的一个集合，使模型中解释的公式能够量化这条关系。所得结果以单步递归已有充分的对象语言描述为条件，并且只适用于既是序数又可构造的 `α`。它表示已有序的底层关系，而尚未在对象语言中断言这条关系是良序。
<!--ja-->
# 段階順序の内部の表

構成可能な順序数の段階添字 `α` では、先の構成によって `Lset α` の要素上のホスト側の狭義整列順序がすでに得られている。本章の目的は、その二項比較を `L` の内部の集合として表現し、モデルで解釈される論理式がその関係を量化できるようにすることである。結果は、一段階の再帰について妥当な対象言語の記述が与えられることを前提とし、`α` が順序数かつ構成可能である場合に適用される。ここで表現するのは既存の順序の基礎となる関係であり、この関係が整列順序であるという対象言語の主張はまだ与えない。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

```

<!--en-->
The single classical assumption is excluded middle at the universe level used throughout the construction. It is already needed by the stage orders and supplies the replacement and separation principles used later; the local arguments about truncation, transport, and extensional uniqueness add no second classical hypothesis.
<!--zh-->
全章唯一的经典假设，是构造所处宇宙层级上的排中律。先前的层序已经需要它，后文使用的替换与分离也由它供给；关于截断、搬运与外延唯一性的局部论证不再加入第二项经典假设。
<!--ja-->
この章で用いる古典的仮定は、構成が置かれる宇宙レベルでの排中律だけである。先に得た段階順序がすでにこれを必要とし、後で用いる置換と分出もこれから得られる。切り詰め、輸送、外延的な一意性についての局所的な議論が、別の古典的仮定を加えることはない。
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )

```

<!--en-->
Fixing `lem : LEM (ℓ-suc ℓ)` at the module boundary makes that dependence uniform. In particular, every construction below inherits the same level-indexed assumption rather than silently appealing to excluded middle at an unrestricted size.
<!--zh-->
在模块边界固定 `lem : LEM (ℓ-suc ℓ)`，使这项依赖始终一致。特别地，下文所有构造都继承同一个带层级索引的假设，而不会暗中诉诸任意大小上的排中律。
<!--ja-->
モジュールの境界で `lem : LEM (ℓ-suc ℓ)` を固定することで、この依存は一貫したものになる。したがって以下の構成はすべて、同じレベルつきの仮定を受け継ぎ、任意の大きさでの排中律を暗黙に用いることはない。
<!--/-->

```agda
module L.Choice.OrderTable {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

```

<!--en-->
Two levels of discourse must be kept separate. The relation to be represented is defined in the host type theory, while its recursive description is a first-order formula interpreted in `L`. Membership induction connects the stages: its motive may take values in any dependent type family, so the later simultaneous package of a table and a relation does not have to be a proposition for the recursion to be legitimate.
<!--zh-->
这里必须区分两个论述层次。待表示的关系定义在宿主类型论中，而它的递归描述是一条在 `L` 中解释的一阶公式。成员归纳连接各层：它的动机可以取值于任意依值类型族，因此后文同时包含表与关系的资料包无须先被证明为命题，递归本身便已合法。
<!--ja-->
ここでは二つの議論の水準を区別する必要がある。表現される関係はホストの型理論で定義され、その再帰的な記述は `L` で解釈される一階論理式である。所属に沿う帰納が各段階を結ぶ。その動機は任意の依存型族に値を取れるので、後で表と関係を同時に運ぶ組が命題であることは、再帰の正当性の前提ではない。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
```

<!--en-->
The final relation lives in the constructible model, but its endpoints begin as members of the host set `Lset α`. Once ordinalness `oα` is fixed, `Lset→isL` packages each such endpoint as an element of the model; this conversion uses the ordinalness of `α`, not a separate proof that `α` itself is constructible. The constructibility witness for `α` has a different later role: it packages the index itself as the model element `A`, which serves as the domain for replacement and as a parameter of separation. Ordinal membership supplies ordinalness at smaller indices, while pair injectivity and extensionality recover endpoints and identify sets from their members.
<!--zh-->
最终关系位于可构造模型中，但它的端点起初是宿主集合 `Lset α` 的成员。固定序数性证明 `oα` 后，`Lset→isL` 把每个端点打包为模型元素；这一步使用 `α` 的序数性，而不使用 `α` 本身可构造的另一份证明。`α` 的可构造性见证在后文承担不同作用：它把层索引本身打包为模型元素 `A`，供替换作为定义域、供分离作为参数。序数成员法则给出较小索引的序数性，而对编码的单射性与外延性分别恢复端点、按成员认同集合。
<!--ja-->
最終的な関係は構成可能モデルの中にあるが、その端点はまずホスト集合 `Lset α` の要素として現れる。順序数性 `oα` を固定すると、`Lset→isL` によって各端点をモデル要素としてまとめられる。この変換が使うのは `α` の順序数性であり、`α` 自身が構成可能であるという別の証明ではない。`α` の構成可能性の証人は、後で異なる役割を果たす。段階の添字自身をモデル要素 `A` としてまとめ、置換公理の定義域と分出公理のパラメータにするためである。順序数の要素に関する法則が小さい添字の順序数性を与え、対の符号化の単射性と外延性が、それぞれ端点の復元と要素による集合の同一視を与える。
<!--/-->

```agda
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset; Lset→isL; IsOrd; isPropIsOrd )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Axioms.Basic {ℓ} using ( extensionalL )
```

<!--en-->
The construction will use the two set-existence principles for different purposes. Replacement collects the relation values at all lower indices into one table, after truncated existence and extensional uniqueness have made each graph fiber contractible. Separation then cuts the current relation out of one common containing set. Thus the table and the relation at its bound are produced together, but by distinct arguments.
<!--zh-->
构造将把两条集合存在原理用于不同目的。命题截断下的存在与外延唯一性先使每个图纤维可缩，替换随后把所有较小索引处的关系取值收集成一张表。分离则从一个公共包含集中切出当前关系。因此，界下的表与界处的关系虽被同时产生，却来自两种不同的论证。
<!--ja-->
この構成では、二つの集合存在原理を異なる目的に用いる。命題的切り詰めのもとの存在と外延的な一意性によって各グラフの繊維を可縮にした後、置換がすべての小さい添字での関係の値を一つの表に集める。分出は一つの共通の包含集合から現在の関係を切り出す。したがって、上界より下の表と上界での関係は同時に作られるが、その存在を与える議論は別々である。
<!--/-->

```agda
open import L.Axioms.Full {ℓ} lem using ( hasReplacementL; hasSeparationL )
open import L.Recursion {ℓ} lem using ( mereFunct; smallDom )
open import L.Coding.Model {ℓ} using ( domAt-intro; prʟ; prʟ-fst )
open import L.Coding.Expressions {ℓ} using ( extAt; extAt-in; extAt-out; extAt-in-both )
open import L.Coding.HierarchySequence {ℓ} lem using ( module RecShape )
```

<!--en-->
The order itself is already available as `orderAt α oα`, a strict well-order on `Mem (Lset α)`. This chapter uses its underlying comparison, trichotomy, irreflexivity, and transitivity, and later transports the same order to a small presentation of the stage. No new comparison rule or well-foundedness proof is introduced here.
<!--zh-->
序本身已经由 `orderAt α oα` 给出，它是 `Mem (Lset α)` 上的严格良序。本章使用其底层比较、三岐性、非自反性与传递性，后面还把同一个序搬运到该层的小呈现上。这里不引入新的比较规则，也不重新证明良基性。
<!--ja-->
順序そのものは、`Mem (Lset α)` 上の狭義整列順序 `orderAt α oα` としてすでに得られている。本章ではその基礎となる比較、三分性、非反射性、推移性を用い、後には同じ順序を段階の小さな提示へ運ぶ。新しい比較規則や整礎性の証明をここで導入することはない。
<!--/-->

```agda
open import L.Choice.StageOrders {ℓ} lem using ( Mem; relOf; orderAt; memOf; carry )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; Tri; lt; eq; gt )

```

<!--en-->
Many later equalities compare dependent pairs whose second components are membership proofs. Since membership and ordinalness are propositions, equality of the underlying sets determines equality of the packaged members, and changing a certificate does not create a different mathematical endpoint. Transport along pair-component equalities can therefore align comparisons without turning proofs into extra choices.
<!--zh-->
后文许多等式比较的是依值对，其第二分量是成员证明。由于成员关系与序数性都是命题，底层集的相等便决定打包成员的相等，而更换证书不会产生不同的数学端点。因此，可以沿对分量的等式搬运比较，而不会把证明变成额外的选择。
<!--ja-->
後で現れる多くの等式は、第二成分が所属の証明である依存対を比較する。所属と順序数性は命題なので、底の集合の等しさからまとめられた要素の等しさが定まり、証明書を取り替えても別の数学的端点は生じない。そのため、対の成分の等式に沿って比較を輸送しても、証明を余分な選択に変えることはない。
<!--/-->

```agda
```

<!--en-->
Propositional truncation will mark every place where existence is needed without a selected witness. Small presentations serve a different role: they replace a possibly large membership fiber by a small index type whose embedding returns the represented member. Keeping these devices distinct is essential, since one hides a choice while the other controls size.
<!--zh-->
命题截断将标出每个只需存在而不选定见证之处。小呈现承担另一种任务：它用一个小索引类型呈现可能较大的成员纤维，再由嵌入返回所表示的成员。二者必须分清，因为前者隐藏选择，后者控制大小。
<!--ja-->
命題的切り詰めは、証人を選ばず存在だけを必要とするすべての箇所を示す。小さな提示の役割は別である。大きいかもしれない所属の繊維を小さな添字型で提示し、その埋め込みから表される要素を返す。一方は選択を隠し、他方は大きさを制御するので、この二つを区別することが大切である。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈-asFiber )
```

<!--en-->
From this point, propositions and quantifiers are read in the membership structure of `L`. A statement that a model element realizes a class is therefore expressed as a proposition about its members, not as an external collection assembled by metatheoretic comprehension.
<!--zh-->
从这里起，命题与量词都在 `L` 的成员结构中读取。因此，说一个模型元素实现某个类，是对其成员作出的命题，而不是借元理论的概括另行组装一个外部集合。
<!--ja-->
ここから先、命題と量化は `L` の所属構造で読む。したがって、モデルの要素があるクラスを実現するという主張は、その要素の所属についての命題として表され、メタ理論の内包によって別の外部集合を作ることではない。
<!--/-->

```agda

open hPropStructure 𝒮ʟ

```

<!--en-->
The internal set-builder interface will later state that a candidate has exactly the members satisfying a formula. This is an extensional specification of a set; existence still has to come from replacement or separation at the appropriate point of the recursion.
<!--zh-->
后面使用的内部集合构造接口，将陈述某个候选集合恰以满足一条公式的对象为成员。这只是集合的外延规格；集合的存在仍须在递归的相应位置由替换或分离给出。
<!--ja-->
後で用いる内部の集合記法は、候補の集合が、ある論理式を満たす対象をちょうど要素にもつことを述べる。これは集合の外延的な仕様であり、集合の存在そのものは、再帰の適切な箇所で置換または分出から得なければならない。
<!--/-->

```agda
module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )

```

<!--en-->
Formula satisfaction is compared with host-level predicates through absoluteness. The formulas do not themselves contain `orderAt`; instead, adequacy equations will identify their interpreted truth values with the host class of coded comparison pairs.
<!--zh-->
公式的满足关系通过绝对性与宿主层谓词相比较。公式本身并不含有 `orderAt`；充分性等式将在语义上把公式的真值与编码比较对所成的宿主层类认同起来。
<!--ja-->
論理式の充足は、絶対性を通してホスト側の述語と比較される。論理式そのものが `orderAt` を含むのではない。妥当性の等式が、その解釈された真理値を、符号化された比較対からなるホスト側のクラスと同一視する。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

```

<!--en-->
The formulas used below introduce two fresh binders around an existing environment. The private shift preserves the meanings of the older variables by moving each of their indices past those binders, a small syntactic device that lets the mathematical roles of value, index, and table remain fixed.
<!--zh-->
后文公式会在既有环境外再引入两个绑定。这个私有移位把每个旧变元的索引越过两个新绑定，从而保留原有含义；借此，取值、索引与表的数学角色在扩展环境中仍保持不变。
<!--ja-->
以下の論理式は、既存の環境の外側に二つの新しい束縛を導入する。この非公開のずらしは、古い各変数の添字を二つの束縛の先へ移して意味を保つ。これにより、値、添字、表という数学的な役割が、拡張された環境でも変わらない。
<!--/-->

```agda
private
  sh2 : ∀ {n} → Fin n → Fin (suc (suc n))
  sh2 i = suc (suc i)
```

<!--en-->
## The comparison, read back whole
<!--zh-->
## 把比较整个读回来
<!--ja-->
## 比較を切り詰めから取り戻す
<!--/-->

<!--en-->
A class in the model must be proposition-valued, whereas no proof has been given that a witness of `relOf (orderAt α oα) a b` is unique. `Ordering` therefore retains only the propositional truncation of that witness. This changes the logical form needed for class membership while preserving whether the comparison is inhabited.
<!--zh-->
模型中的类必须取命题值，但尚未证明 `relOf (orderAt α oα) a b` 的见证具有唯一性。因此，`Ordering` 只保留该见证的命题截断。这把比较化为适合类成员关系的逻辑形式，同时保留比较是否有见证这一事实。
<!--ja-->
モデルのクラスは命題に値を取る必要があるが、`relOf (orderAt α oα) a b` の証人が一意であるとは証明されていない。そこで `Ordering` は、その証人の命題的切り詰めだけを保つ。これにより比較はクラスの所属に適した論理的な形になり、比較が証人をもつかどうかは保たれる。
<!--/-->

```agda
Ordering : (α : V ℓ) → IsOrd α → Mem (Lset α) → Mem (Lset α) → hProp (ℓ-suc ℓ)
Ordering α oα a b = ∥ relOf (orderAt α oα) a b ∥₁ , squash₁

```

<!--en-->
For this particular comparison, the truncation can later be removed. The reason is the trichotomy of the already constructed strict order: once `a` and `b` have been classified as forward-related, equal, or reverse-related, the latter two alternatives contradict the truncated forward comparison. This is a special property of a strict total comparison, not a general way to extract witnesses from propositional truncation.
<!--zh-->
对于这一特定比较，稍后可以消去截断。理由是已有严格序的三岐性：一旦把 `a` 与 `b` 分成正向相关、相等或反向相关三种情形，后两种就会与截断后的正向比较矛盾。这是严格全序比较的特殊性质，并非从任意命题截断中提取见证的一般方法。
<!--ja-->
この特定の比較については、後で切り詰めを除去できる。その理由は、すでに構成された狭義順序の三分性である。`a` と `b` が順方向に関係する場合、等しい場合、逆方向に関係する場合に分けると、後の二つは切り詰められた順方向の比較と矛盾する。これは狭義全順序の比較に固有の性質であり、命題的切り詰め一般から証人を取り出す方法ではない。
<!--/-->

```agda
strict : (α : V ℓ) (oα : IsOrd α) (a b : Mem (Lset α))
       → ⟨ Ordering α oα a b ⟩ → relOf (orderAt α oα) a b
strict α oα a b h = decide (SWO.tri∙ W a b)
  where
  W = orderAt α oα
```

<!--en-->
In the forward branch, trichotomy already supplies the required untruncated witness, so the truncated hypothesis is not opened. In the equality branch, the witness may be eliminated only into the empty type: transporting it along `a ≡ b` would make `a` precede itself, contrary to irreflexivity. The final result follows from that contradiction.
<!--zh-->
在正向分支中，三岐性已经给出所需的未截断见证，因而无须打开截断假设。在相等分支中，只把该见证消去到空类型：沿 `a ≡ b` 搬运后，它将使 `a` 先于自身，与非自反性矛盾。所需结果再由该矛盾消去得到。
<!--ja-->
順方向の分岐では、三分性が必要な切り詰められていない証人をすでに与えるので、切り詰められた仮定を開く必要はない。等しい分岐では、その証人を空の型へだけ除去する。`a ≡ b` に沿って輸送すれば `a` が自分自身に先行することになり、非反射性に反するからである。必要な結果は、この矛盾から得られる。
<!--/-->

```agda
  decide : Tri (relOf W a b) (a ≡ b) (relOf W b a) → relOf W a b
  decide (lt k) = k
  decide (eq q) = ⊥₀-rec (rec₁ isProp⊥
    (λ k → SWO.irr∙ W a (subst (relOf W a) (sym q) k)) h)
  decide (gt k) = ⊥₀-rec (rec₁ isProp⊥
```

<!--en-->
In the reverse branch, combining a hypothetical forward witness with the reverse comparison by transitivity would again make `a` precede itself. The truncation is opened only to prove this contradiction. Thus `strict` returns a comparison witness without proving that comparison witnesses themselves form a proposition or selecting a preferred proof.
<!--zh-->
在反向分支中，若有正向见证，把它与反向比较按传递性复合，也会使 `a` 先于自身。此处打开截断只为证明这个矛盾。因此，`strict` 虽返回一项比较见证，却没有证明比较见证本身构成命题，也没有选出某个优先证明。
<!--ja-->
逆方向の分岐では、仮に順方向の証人があれば、それを逆方向の比較と推移性で合成することで、やはり `a` が自分自身に先行してしまう。ここでも切り詰めを開くのは、この矛盾を示すためだけである。したがって `strict` は比較の証人を返すが、比較の証人の型が命題であることや、優先される証明を選ぶことは示さない。
<!--/-->

```agda
    (λ j → SWO.irr∙ W a (SWO.trans∙ W a b a j k)) h)
```

<!--en-->
## What the relation at a stage is
<!--zh-->
## 层处的关系是什么
<!--ja-->
## 段階における関係
<!--/-->

<!--en-->
For an index `α`, `Related α z` says, under propositional truncation, that `z` is the Kuratowski pair of two members of `Lset α` related by the stage order. The ordinalness certificate is quantified inside the class, so the class does not depend on a chosen proof that `α` is an ordinal. The endpoint decomposition and comparison witness remain within their truncation boundaries.
<!--zh-->
对索引 `α`，`Related α z` 在命题截断意义下断言：`z` 是 `Lset α` 的两个成员所成的 Kuratowski 对，且这两个成员由层序关联。序数性证书在类的内部量化，因此该类不依赖于一份选定的 `α` 为序数的证明。端点分解与比较见证都留在各自的截断边界内。
<!--ja-->
添字 `α` に対して `Related α z` は、命題的切り詰めのもとで、`z` が `Lset α` の二つの要素の Kuratowski 対であり、その二要素が段階順序で関係づけられていることを述べる。順序数性の証明書はクラスの内側で量化されるので、このクラスは `α` が順序数であるという選ばれた証明に依存しない。端点の分解と比較の証人は、それぞれの切り詰めの境界内にとどまる。
<!--/-->

```agda
Related : V ℓ → V ℓ → hProp (ℓ-suc ℓ)
Related α z = ∃[ oα ∶ IsOrd α ] (∃[ a ∶ Mem (Lset α) ] (∃[ b ∶ Mem (Lset α) ]
  ((z ≡ pr (fst a) (fst b)) , setIsSet z (pr (fst a) (fst b))) ⊓ Ordering α oα a b))

```

<!--en-->
A model set `r` realizes this class when its membership agrees with `Related α` in both directions at every model element `z`. The outward implication excludes unrelated or malformed members, and the inward implication includes every related pair. Quantifying over model elements is sufficient here because constructibility is transitive, so every member of a constructible set can itself be packaged as an element of the model.
<!--zh-->
模型集合 `r` 实现这个类，是指对每个模型元素 `z`，`r` 的成员关系与 `Related α` 双向一致。向外蕴含排除无关或形状错误的成员，向内蕴含纳入每个被关联的对。这里只量化模型元素已经足够，因为可构造性具有传递性，可构造集的每个成员都能再次打包为模型元素。
<!--ja-->
モデルの集合 `r` がこのクラスを実現するとは、すべてのモデル要素 `z` について、`r` への所属と `Related α` が双方向に一致することである。外向きの含意は無関係な要素や形の違う要素を排除し、内向きの含意は関係するすべての対を含める。構成可能性は推移的であり、構成可能な集合の各要素もモデルの要素としてまとめられるので、ここではモデル要素だけを量化すれば十分である。
<!--/-->

```agda
Realizes : V ℓ → S → hProp (ℓ-suc ℓ)
Realizes α r = ∀[ z ∶ S ] ((fst z ∈ fst r) ⇒ Related α (fst z))
                        ⊓ (Related α (fst z) ⇒ (fst z ∈ fst r))

```

<!--en-->
`IsRel α r` is the type of evidence for that exact membership specification. It asserts that `r` realizes the host-defined class; it does not add a strict-order structure to `r`, nor does it claim that the relation satisfies an object-language well-order formula.
<!--zh-->
`IsRel α r` 是上述精确成员规格的证据类型。它断言 `r` 实现宿主层定义的类；它既不为 `r` 添加严格序结构，也不声称该关系满足某条对象语言良序公式。
<!--ja-->
`IsRel α r` は、この正確な所属仕様の証拠の型である。これは `r` がホスト側で定義されたクラスを実現することを述べるだけで、`r` に狭義順序の構造を加えず、関係が対象言語の整列順序の論理式を満たすとも主張しない。
<!--/-->

```agda
IsRel : V ℓ → S → Type (ℓ-suc ℓ)
IsRel α r = ⟨ Realizes α r ⟩

```

<!--en-->
The two implications in a realization proof determine a path between the proposition that `z` belongs to `r` and the proposition that `z` is related at `α`. This pointwise path is the rewriting principle used later whenever membership in an arbitrary realizer must be exchanged for the semantic class.
<!--zh-->
实现证明中的两条蕴含，在「`z` 属于 `r`」与「`z` 在 `α` 处被关联」这两个命题之间确定一条路径。后文每当需要在任意实现者的成员关系与语义类之间转换时，就使用这条逐点路径改写。
<!--ja-->
実現の証明に含まれる二つの含意は、「`z` が `r` に属する」という命題と「`z` が `α` で関係する」という命題の間のパスを定める。この点ごとのパスが、任意の実現集合への所属と意味論的なクラスを交換するときの書き換え原理になる。
<!--/-->

```agda
rel-path : (α : V ℓ) (r : S) → IsRel α r
         → (z : S) → (fst z ∈ fst r) ≡ Related α (fst z)
rel-path α r p z =
  ⇔toPath {P = fst z ∈ fst r} {Q = Related α (fst z)} (p z .fst) (p z .snd)

```

<!--en-->
If `r` and `r'` both realize the class, their membership propositions agree pointwise, and extensionality in `L` identifies the two sets. The uniqueness proved here is uniqueness of the realizing set. It does not make the truncated ordinal certificate, endpoint decomposition, or comparison witness in `Related` uniquely chosen.
<!--zh-->
若 `r` 与 `r'` 都实现该类，则两者的成员命题逐点一致，`L` 中的外延性遂认同这两个集合。这里证明的是实现集合的唯一性；它并不把 `Related` 中经过截断的序数证书、端点分解或比较见证变成唯一选定的资料。
<!--ja-->
`r` と `r'` がともにこのクラスを実現するなら、両者の所属命題は点ごとに一致し、`L` の外延性が二つの集合を同一視する。ここで示す一意性は実現集合の一意性である。`Related` の中で切り詰められた順序数性の証明書、端点の分解、比較の証人が一意に選ばれることを意味しない。
<!--/-->

```agda
rel-unique : (α : V ℓ) (r r' : S) → IsRel α r → IsRel α r' → r ≡ r'
rel-unique α r r' p q = extensionalL
  (λ z → rel-path α r p z ∙ sym (rel-path α r' q z))

```

<!--en-->
The forward reading starts with specified members `a,b` and an actual stage-order comparison. Their underlying sets form the coded pair, while the ordinal certificate, the two packaged members, and the truncated comparison give a witness of `Related`. Since the witness is constructed inside the truncations, no choice is being extracted.
<!--zh-->
正向读式从指定的成员 `a,b` 与一项实际的层序比较出发。其底层集组成编码对，而序数证书、两个打包成员与截断后的比较共同给出 `Related` 的见证。见证是在各层截断内部构造的，因此这里没有从截断信息中提取选择。
<!--ja-->
順方向の読みは、指定された要素 `a,b` と実際の段階順序の比較から始まる。二つの底の集合が符号化された対を作り、順序数性の証明書、まとめられた二要素、切り詰められた比較が `Related` の証人を与える。証人は切り詰めの内側で構成されるので、切り詰められた情報から選択を取り出してはいない。
<!--/-->

```agda
module _ (α : V ℓ) (oα : IsOrd α) (a b : Mem (Lset α)) where
  related-in : relOf (orderAt α oα) a b → ⟨ Related α (pr (fst a) (fst b)) ⟩
  related-in h = ∣ oα , ∣ a , ∣ b , (refl , ∣ h ∣₁) ∣₁ ∣₁ ∣₁

```

<!--en-->
The reverse reading has a deliberately narrower shape. Its input object is already the coded pair of the fixed endpoints `a,b`; only under that presentation can the proof compare an existentially represented pair with those endpoints and recover their stage-order comparison. It does not decompose an arbitrary related object into a selected pair.
<!--zh-->
反向读式刻意采用更窄的形状。输入对象已经被呈现为固定端点 `a,b` 的编码对；只有在这种呈现下，证明才能把存在性表示中的对与这两个端点比较，并恢复它们的层序比较。它不会把任意被关联对象分解成一对选定端点。
<!--ja-->
逆方向の読みは、意図的に狭い形をしている。入力の対象はすでに固定された端点 `a,b` の符号化された対として提示されている。この提示があるからこそ、存在的に表された対を二つの端点と比較し、その段階順序の比較を復元できる。任意の関係する対象を、選ばれた端点の対へ分解するものではない。
<!--/-->

```agda
  related-out : ⟨ Related α (pr (fst a) (fst b)) ⟩ → relOf (orderAt α oα) a b
  related-out h = strict α oα a b (rec₁ squash₁ atOrd h)
    where
    atPair : (o : IsOrd α) (a' b' : Mem (Lset α))
           → (pr (fst a) (fst b) ≡ pr (fst a') (fst b'))
```

<!--en-->
Suppose the truncated record presents endpoints `a',b'` and an ordinalness proof `o`. Equality of the two coded pairs identifies `a` with `a'` and `b` with `b'`; propositionhood of ordinalness identifies `o` with the fixed proof `oα`. Transporting the recorded comparison along these three identifications yields a truncated comparison at the fixed endpoints.
<!--zh-->
设截断记录给出端点 `a',b'` 与序数性证明 `o`。两条编码对的相等分别认同 `a` 与 `a'`、`b` 与 `b'`；序数性的命题性则认同 `o` 与固定证明 `oα`。沿这三项认同搬运被记录的比较，便得到固定端点处的截断比较。
<!--ja-->
切り詰められた記録が端点 `a',b'` と順序数性の証明 `o` を与えるとする。二つの符号化された対の等しさから `a` と `a'`、`b` と `b'` がそれぞれ同一視され、順序数性が命題であることから `o` と固定された証明 `oα` が同一視される。この三つの同一視に沿って記録された比較を輸送すると、固定された端点での切り詰められた比較が得られる。
<!--/-->

```agda
           → ⟨ Ordering α o a' b' ⟩ → ⟨ Ordering α oα a b ⟩
    atPair o a' b' q = map₁
      (λ k → subst2 (relOf (orderAt α oα)) (sym ea) (sym eb)
        (subst (λ o' → relOf (orderAt α o') a' b') (isPropIsOrd α o oα) k))
      where
```

<!--en-->
Pair-code injectivity first recovers equality of the underlying endpoint sets. Each endpoint is a dependent pair of a set and its membership proof in `Lset α`; because that proof is propositional, equality of the first components lifts to equality of the complete members. The comparison can therefore be transported at its correct dependent type.
<!--zh-->
对编码的单射性先恢复底层端点集的相等。每个端点都是由集合及其属于 `Lset α` 的证明组成的依值对；由于该证明是命题，第一分量的相等可以提升为完整成员的相等。比较因而能在正确的依值类型中搬运。
<!--ja-->
対の符号化の単射性は、まず底にある端点の集合の等しさを復元する。各端点は、集合とそれが `Lset α` に属する証明からなる依存対である。その証明は命題なので、第一成分の等しさは要素全体の等しさへ持ち上がる。これにより、比較を正しい依存型の中で輸送できる。
<!--/-->

```agda
      ea : a ≡ a'
      ea = Σ≡Prop (λ x → snd (x ∈ Lset α)) (pr-inj q .fst)
      eb : b ≡ b'
      eb = Σ≡Prop (λ x → snd (x ∈ Lset α)) (pr-inj q .snd)

```

<!--en-->
The outer ordinal certificate is explicit, while each endpoint exists only under propositional truncation. The elimination therefore proceeds one truncation at a time into the proposition `Ordering α oα a b`. This target permits temporary representatives to be used without allowing either endpoint to escape as selected data.
<!--zh-->
外层序数证书是显式的，而两个端点都只在命题截断下存在。因此，消去逐层进入命题 `Ordering α oα a b`。这个目标允许证明临时使用代表，却不会让任一端点作为选定资料逸出。
<!--ja-->
外側の順序数性の証明書は明示されているが、各端点は命題的切り詰めのもとでしか存在しない。そこで切り詰めを一層ずつ、命題 `Ordering α oα a b` へ除去する。この目標の中では一時的な代表を使えるが、どちらの端点も選ばれたデータとして外へ出ることはない。
<!--/-->

```agda
    atOrd : Σ[ o ∈ IsOrd α ] ⟨ ∃[ a' ∶ Mem (Lset α) ] (∃[ b' ∶ Mem (Lset α) ] ((pr (fst a) (fst b) ≡ pr (fst a') (fst b'))
                 , setIsSet _ (pr (fst a') (fst b'))) ⊓ Ordering α o a' b') ⟩
          → ⟨ Ordering α oα a b ⟩
    atOrd (o , h₁) = rec₁ squash₁
      (λ { (a' , h₂) → rec₁ squash₁
```

<!--en-->
After both temporary endpoints have been exposed, the pair-alignment argument supplies the truncated comparison at `a,b`; `strict` then turns that specific truncated comparison into the required witness. The composite proves the reverse reading while preserving all existential truncation boundaries except for the comparison witness justified by trichotomy.
<!--zh-->
两个临时端点都被打开后，对齐有序对的论证给出 `a,b` 处的截断比较；随后 `strict` 把这一特定截断比较化为所需见证。复合后的证明完成反向读式，同时保留所有存在量词的截断边界，只有经三岐性论证的比较见证被恢复出来。
<!--ja-->
二つの一時的な端点を開いた後、対を整列する議論が `a,b` での切り詰められた比較を与え、`strict` がその特定の比較から必要な証人を復元する。この合成によって逆方向の読みが得られるが、三分性で正当化された比較の証人を除き、存在に関する切り詰めの境界はすべて保たれる。
<!--/-->

```agda
        (λ { (b' , (q , hr)) → atPair o a' b' q hr }) h₂ }) h₁
```

<!--en-->
## Whatever realizes the class, read at both shapes
<!--zh-->
## 凡实现那个类者，读在两种形状上
<!--ja-->
## クラスを実現する任意の集合を二つの形で読む
<!--/-->

<!--en-->
The useful representation lemmas are stated for any `r` realizing `Related α`, not only for the relation eventually constructed by the recursion. This allows a relation value already recorded in a lower table to be read immediately. For fixed ordinalness `oα`, each member of `Lset α` is constructible and can therefore be packaged as an element of the model.
<!--zh-->
真正有用的表示引理针对任意实现 `Related α` 的 `r`，而不限于递归最终构造的关系。这样，较低层表中已经记录的关系取值便能立即被读取。固定序数性证明 `oα` 后，`Lset α` 的每个成员都是可构造的，因而可以打包成模型元素。
<!--ja-->
有用な表現補題は、再帰が最後に構成する関係だけでなく、`Related α` を実現する任意の `r` について述べられる。これにより、小さい段階の表にすでに記録された関係の値を直ちに読める。順序数性の証明 `oα` を固定すると、`Lset α` の各要素は構成可能であり、モデルの要素としてまとめられる。
<!--/-->

```agda
module _ (α : V ℓ) (oα : IsOrd α) (r : S) (hr : IsRel α r) where
  private
    memL : Mem (Lset α) → S
    memL c = fst c , Lset→isL α oα (fst c) (snd c)

```

<!--en-->
The model's internal ordered pair of the packaged endpoints and the host Kuratowski pair of their underlying sets are propositionally equal, though they are not treated as definitionally identical. Applying membership in `r` to this equality gives the first transport bridge.
<!--zh-->
模型中由打包端点组成的内部有序对，与其底层集在宿主层组成的 Kuratowski 对在命题上相等，但二者不被当作定义性相同。把「属于 `r`」施于这条等式，便得到第一条搬运桥。
<!--ja-->
まとめられた端点からモデル内部で作る順序対と、その底の集合からホスト側で作る Kuratowski 対は命題的に等しいが、定義的に同じものとは扱わない。この等しさに「`r` に属する」を作用させると、最初の輸送の橋が得られる。
<!--/-->

```agda
    atRel : (a b : Mem (Lset α))
          → (fst (prʟ (memL a) (memL b)) ∈ fst r)
          ≡ (pr (fst a) (fst b) ∈ fst r)
    atRel a b = cong (λ x → x ∈ fst r) (prʟ-fst (memL a) (memL b))

```

<!--en-->
Applying `Related α` to the same pair equality gives the companion bridge on the semantic side. Together, the two bridges let a realization proof be used at an internal pair and then restated at the plain pair of underlying sets, or conversely.
<!--zh-->
把 `Related α` 施于同一条有序对等式，得到语义一侧的配套桥。两条桥结合起来，便可先在内部有序对处使用实现证明，再把结论改述为底层集的朴素有序对，反向亦然。
<!--ja-->
同じ対の等しさに `Related α` を作用させると、意味論の側のもう一つの橋が得られる。二つの橋を合わせることで、内部の順序対に実現の証明を使い、その結果を底の集合の素の対について述べ直せる。逆向きにも同様である。
<!--/-->

```agda
    atRelated : (a b : Mem (Lset α))
              → ⟨ Related α (fst (prʟ (memL a) (memL b))) ⟩
              ≡ ⟨ Related α (pr (fst a) (fst b)) ⟩
    atRelated a b = cong (λ x → ⟨ Related α x ⟩) (prʟ-fst (memL a) (memL b))

```

<!--en-->
The filling direction begins with a host-level comparison of two members. The forward `Related` reading turns it into relatedness of their coded pair, the realization proof turns relatedness into membership in `r`, and the pair bridge returns the statement to the host pair. Hence every pair compared by `orderAt` occurs in any realizing set.
<!--zh-->
填充方向从两个成员的一项宿主层比较出发。`Related` 的正向读式把它化为编码对的关联性，实现证明再把关联性化为属于 `r`，最后由有序对桥把陈述搬回宿主对。因此，`orderAt` 所比较的每一对都属于任意实现集合。
<!--ja-->
埋める向きは、二つの要素のホスト側の比較から始まる。`Related` の順方向の読みがそれを符号化された対の関係へ変え、実現の証明が関係を `r` への所属へ変え、対の橋が主張をホスト側の対へ戻す。したがって、`orderAt` で比較されるすべての対は、任意の実現集合に属する。
<!--/-->

```agda
  rel-fill : (a b : Mem (Lset α)) → relOf (orderAt α oα) a b
           → ⟨ pr (fst a) (fst b) ∈ fst r ⟩
  rel-fill a b h = subst ⟨_⟩ (atRel a b)
    (hr (prʟ (memL a) (memL b)) .snd
      (transport (sym (atRelated a b)) (related-in α oα a b h)))
```

<!--en-->
The reading direction reverses the route. Membership of the host pair is transported to membership of the internal pair, read outward through the realization proof as a `Related` fact, transported back to the fixed host pair, and finally converted by `related-out` into the untruncated stage-order comparison.
<!--zh-->
读取方向反向走过同一条路径。宿主对的成员关系先搬到内部对处，经实现证明向外读成 `Related` 事实，再搬回固定的宿主对，最终由 `related-out` 化为未截断的层序比较。
<!--ja-->
読む向きは同じ経路を逆にたどる。ホスト側の対の所属を内部の対の所属へ輸送し、実現の証明を外向きに読んで `Related` の事実を得て、固定されたホスト側の対へ戻す。最後に `related-out` が、切り詰められていない段階順序の比較を返す。
<!--/-->

```agda

  rel-rep : (a b : Mem (Lset α))
          → ⟨ pr (fst a) (fst b) ∈ fst r ⟩ → relOf (orderAt α oα) a b
  rel-rep a b h = related-out α oα a b
    (transport (atRelated a b)
      (hr (prʟ (memL a) (memL b)) .fst (subst ⟨_⟩ (sym (atRel a b)) h)))
```

<!--en-->
Some later arguments work with the small presentation `⟪ Lset α ⟫` rather than with dependent member pairs. An index in that presentation embeds into the underlying set and carries precisely the membership proof needed to form an element of `Mem (Lset α)`.
<!--zh-->
后续有些论证使用小呈现 `⟪ Lset α ⟫`，而不直接使用依值成员对。呈现中的索引嵌入底层集合，并携带恰好足以组成 `Mem (Lset α)` 元素的成员证明。
<!--ja-->
後の議論には、依存的な要素の対ではなく、小さな提示 `⟪ Lset α ⟫` を用いるものがある。その提示の添字は底の集合へ埋め込まれ、`Mem (Lset α)` の要素を作るために必要な所属の証明を備えている。
<!--/-->

```agda

  private
    atIx : ⟪ Lset α ⟫ → Mem (Lset α)
    atIx m = ⟪ Lset α ⟫↪ m , memOf (Lset α) m

```

<!--en-->
Carrying `orderAt` along that presentation gives a strict order on the small index type. This is the same comparison viewed through the embedding, so the representation theorems need no new order-theoretic argument.
<!--zh-->
沿这个呈现搬运 `orderAt`，得到小索引类型上的严格序。这只是同一比较经嵌入后的读法，因此相应的表示定理无须新的序论论证。
<!--ja-->
この提示に沿って `orderAt` を運ぶと、小さな添字型上の狭義順序が得られる。これは埋め込みを通して見た同じ比較なので、対応する表現定理に新たな順序論の議論は必要ない。
<!--/-->

```agda
  open SWO (carry (Lset α) (orderAt α oα)) using () renaming ( _<∙_ to _≺ᶜ_ )

```

<!--en-->
For presentation indices `u,v`, a carried comparison is first read as the comparison of their associated stage members. The earlier filling theorem then places the Kuratowski pair of the embedded endpoints in `r`. This is the small-index form of comparison-to-membership.
<!--zh-->
对呈现索引 `u,v`，搬运后的比较先被读成相应层成员之间的比较。先前的填充定理随后把嵌入端点所成的 Kuratowski 对放入 `r`。这就是从比较到成员关系的小索引形式。
<!--ja-->
提示の添字 `u,v` について、運ばれた比較は、まず対応する段階要素の比較として読まれる。先の埋める定理が、埋め込まれた端点の Kuratowski 対を `r` に入れる。これが、比較から所属へ向かう小さい添字での形である。
<!--/-->

```agda
  ixRel-fill : (u v : ⟪ Lset α ⟫) → u ≺ᶜ v
             → ⟨ pr (⟪ Lset α ⟫↪ u) (⟪ Lset α ⟫↪ v) ∈ fst r ⟩
  ixRel-fill u v = rel-fill (atIx u) (atIx v)

```

<!--en-->
Conversely, membership of the pair of embedded endpoints is read by the earlier theorem as a comparison of the associated stage members. By the definition of the carried order, this is exactly the strict comparison of `u` and `v` in the small presentation.
<!--zh-->
反过来，嵌入端点所成的对属于 `r`，经先前定理读成相应层成员的比较。按照搬运序的定义，这恰是小呈现中 `u` 与 `v` 的严格比较。
<!--ja-->
逆に、埋め込まれた端点の対が `r` に属するなら、先の定理によって対応する段階要素の比較として読める。運ばれた順序の定義から、これは小さな提示における `u` と `v` の狭義比較そのものである。
<!--/-->

```agda
  ixRel-rep : (u v : ⟪ Lset α ⟫)
            → ⟨ pr (⟪ Lset α ⟫↪ u) (⟪ Lset α ⟫↪ v) ∈ fst r ⟩ → u ≺ᶜ v
  ixRel-rep u v = rel-rep (atIx u) (atIx v)
```

<!--en-->
## What a table records
<!--zh-->
## 一张表记录了什么
<!--ja-->
## 表が記録するもの
<!--/-->

<!--en-->
The first table condition is soundness of recorded values. If an index `c` lies below `B` and the coded entry `(c,r)` occurs in `h`, then `r` must realize `Related c`. This condition says nothing about entries whose first component lies outside `B`, so it cannot by itself characterize the table's domain.
<!--zh-->
第一项表条件是已记录取值的可靠性。若索引 `c` 位于 `B` 以下，且编码条目 `(c,r)` 属于 `h`，则 `r` 必须实现 `Related c`。这项条件不约束第一分量位于 `B` 之外的条目，因而不能单独刻画表的定义域。
<!--ja-->
最初の表の条件は、記録された値の健全性である。添字 `c` が `B` より下にあり、符号化された項目 `(c,r)` が `h` に属するなら、`r` は `Related c` を実現しなければならない。この条件は第一成分が `B` の外にある項目について何も述べないので、それだけでは表の定義域を特徴づけられない。
<!--/-->

```agda
Values : S → V ℓ → Type (ℓ-suc ℓ)
Values h B = (c r : S) → ⟨ fst c ∈ B ⟩
           → ⟨ pr (fst c) (fst r) ∈ fst h ⟩ → IsRel (fst c) r

```

<!--en-->
The second condition is totality below the bound. Every `c ∈ B` has some recorded value `r`, but the existence is propositionally truncated. Thus `Entries` supplies exactly what a propositional step argument may use, while withholding a global function that chooses one value at every index.
<!--zh-->
第二项条件是界下的全定义性。每个 `c ∈ B` 都有某个被记录取值 `r`，但这项存在经过命题截断。因此，`Entries` 恰好供给命题性步进论证所需的信息，却不提供在每个索引处选取一个取值的全局函数。
<!--ja-->
第二の条件は、上界より下で全域であることである。各 `c ∈ B` には記録された値 `r` が何か存在するが、その存在には命題的切り詰めが施されている。したがって `Entries` は命題的なステップの議論に必要な情報だけを与え、各添字で一つの値を選ぶ大域的な関数は与えない。
<!--/-->

```agda
Entries : S → V ℓ → Type (ℓ-suc ℓ)
Entries h B = (c : S) → ⟨ fst c ∈ B ⟩
            → ∥ (Σ[ r ∈ S ] ⟨ pr (fst c) (fst r) ∈ fst h ⟩) ∥₁

```

<!--en-->
The third condition excludes entries beyond the bound: every coded pair in `h` has its first component in `B`. Together with `Entries`, it yields the exact domain needed when a completed table is turned back into an approximation. The forward proof that recorded values are sound needs only the first two conditions and therefore keeps `Domain` separate.
<!--zh-->
第三项条件排除界外条目：`h` 中每个编码对的第一分量都属于 `B`。它与 `Entries` 合用，给出把一张完成的表反建为逼近时所需的精确定义域。正向证明已记录取值正确时只需前两项条件，所以 `Domain` 被单独保留。
<!--ja-->
第三の条件は上界の外の項目を排除する。`h` に属するすべての符号化された対の第一成分が `B` に属する。これを `Entries` と合わせると、完成した表から近似を組み立て直すために必要な正確な定義域が得られる。記録された値の健全性を順方向に示す証明には最初の二条件だけが必要なので、`Domain` は分けておく。
<!--/-->

```agda
Domain : S → V ℓ → Type (ℓ-suc ℓ)
Domain h B = (c r : S) → ⟨ pr (fst c) (fst r) ∈ fst h ⟩ → ⟨ fst c ∈ B ⟩
```

<!--en-->
## The step, as a parameter
<!--zh-->
## 那一步，取作参数
<!--ja-->
## ステップをパラメータとする
<!--/-->

<!--en-->
The recursive construction now assumes two formulas with one semantic meaning. `Cond b f` is the variable-slot form used when an approximation table is bound inside a graph; `Cond₀ B F` is the constant form used when a fixed ordinal and completed table serve as parameters to separation. The first adequacy equation assumes ordinalness together with `Values` and `Entries`, then identifies satisfaction of the variable form with `Related` at every tested object.
<!--zh-->
递归构造现在假设两条具有同一语义的公式。`Cond b f` 是变元槽形式，用于逼近表在图中被绑定时；`Cond₀ B F` 是常元形式，用于固定序数与完成的表作为分离的参数时。第一条充分性等式假设序数性以及 `Values` 与 `Entries`，随后对每个被检验对象，把变元形式的满足关系与相应的 `Related` 认同起来。
<!--ja-->
再帰的な構成はここで、同じ意味をもつ二つの論理式を仮定する。`Cond b f` は、近似の表がグラフの内部で束縛されるときに用いる変数スロットの形である。`Cond₀ B F` は、固定された順序数と完成した表を分出のパラメータにするときに用いる定数の形である。最初の妥当性の等式は、順序数性と `Values`、`Entries` を仮定し、調べる各対象について変数形式の充足を対応する `Related` と同一視する。
<!--/-->

```agda
module Described
  (Cond : ∀ {n} → Fin n → Fin n → Formula S (suc n))
  (Cond₀ : S → S → Formula S 1)
  (cond-spec : ∀ {n} (b f : Fin n) (γ : S ^ n) → IsOrd (fst (lookup b γ))
             → Values (lookup f γ) (fst (lookup b γ))
```

<!--en-->
The variable-form hypothesis is pointwise and genuinely bidirectional: it both reads a satisfying coded object as a related pair and constructs satisfaction from relatedness. Only correctness and truncated existence of entries below the ordinal are required. No exact-domain claim is assumed here, so possible entries outside the bound play no part in the semantic identification.
<!--zh-->
变元形式的假设是逐点且真正双向的：它既把满足公式的编码对象读成被关联的对，也从关联性构造公式的满足。这里仅要求序数以下条目的正确性与命题截断下的存在性，并不假设精确定义域，因此可能的界外条目不参与这项语义认同。
<!--ja-->
変数形式の仮定は点ごとであり、実際に双方向である。論理式を満たす符号化対象を関係する対として読む向きと、関係することから充足を構成する向きの両方を含む。必要なのは、順序数より下の項目の正しさと、命題的切り詰めのもとの存在だけである。ここでは正確な定義域を仮定しないので、上界の外にありうる項目はこの意味論的な同一視に関与しない。
<!--/-->

```agda
             → Entries (lookup f γ) (fst (lookup b γ))
             → (z : S)
             → ((z ∷ γ) ⊨ Cond b f) ≡ Related (fst (lookup b γ)) (fst z))
  (cond₀-spec : (b f : S) → IsOrd (fst b)
              → Values f (fst b) → Entries f (fst b)
```

<!--en-->
The constant-form equation gives the same pointwise equivalence after the ordinal and table have become fixed model elements. This second presentation is required by separation, whose defining formula has one free slot for the possible relation member. The equation identifies the meanings of the two contexts; it does not claim that `Cond` and `Cond₀` are syntactically equal.
<!--zh-->
当序数与表已成为固定模型元素后，常元形式的等式给出同样的逐点等价。分离所用的定义公式只为可能的关系成员保留一个自由槽，因此需要这种第二种呈现。该等式认同两种语境的含义，而不声称 `Cond` 与 `Cond₀` 在语法上相等。
<!--ja-->
順序数と表が固定されたモデル要素になった後、定数形式の等式が同じ点ごとの同値を与える。分出で用いる定義論理式は、関係の要素の候補のために一つだけ自由スロットを残すので、この第二の提示が必要である。この等式は二つの文脈の意味を同一視するが、`Cond` と `Cond₀` が構文的に等しいとは主張しない。
<!--/-->

```agda
              → (z : S) → ((z ∷ []) ⊨ Cond₀ b f) ≡ Related (fst b) (fst z))
  where

```

<!--en-->
Given the variable condition, `StepAt v b f` specifies a candidate value extensionally: an object belongs to the value in slot `v` exactly when it satisfies `Cond b f`. This is a two-way membership specification, not an existence theorem. The actual set realizing the specification will be produced later by the recursive use of replacement and separation.
<!--zh-->
给定变元条件后，`StepAt v b f` 外延地刻画候选取值：一个对象属于槽位 `v` 中的取值，当且仅当它满足 `Cond b f`。这是一项双向成员规格，而不是存在定理。实现该规格的实际集合将在后面的递归中由替换与分离产生。
<!--ja-->
変数形式の条件を与えると、`StepAt v b f` は候補の値を外延的に指定する。ある対象がスロット `v` の値に属することと、`Cond b f` を満たすことがちょうど一致する。これは双方向の所属仕様であり、存在定理ではない。この仕様を実現する実際の集合は、後の再帰で置換と分出を用いて作られる。
<!--/-->

```agda
  StepAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  StepAt v b f = extAt v (Cond b f)

```

<!--en-->
Fix slots for the candidate value, ordinal index, and lower table, together with an environment satisfying ordinalness, value soundness, and truncated entry existence. Under these hypotheses, the adequacy equation supplies one common pointwise meaning for the condition. The following two readings will use it in opposite directions: an extensional step specification yields an `IsRel` proof for the candidate value, while an existing `IsRel` proof fills that specification. The whole construction remains relative to the assumed step description until a later chapter supplies a concrete instance.
<!--zh-->
固定候选取值、序数索引与较低层表的三个槽位，并给定一个满足序数性、取值可靠性与命题截断下表项存在性的环境。在这些假设下，充分性等式为条件给出统一的逐点含义。随后的两条读式将从相反方向使用它：外延步进规格产生候选取值的 `IsRel` 证明，而已有的 `IsRel` 证明填充该规格。在后续章节给出具体实例以前，整个构造始终以这条假设的步进描述为参数。
<!--ja-->
候補の値、順序数の添字、小さい段階の表の三つのスロットを固定し、順序数性、値の健全性、命題的切り詰めのもとの項目の存在を満たす環境を与える。これらの仮定のもとで、妥当性の等式は条件に共通の点ごとの意味を与える。続く二つの読みはこれを逆向きに用いる。外延的なステップ仕様から候補の値についての `IsRel` の証明を得る向きと、すでにある `IsRel` の証明からその仕様を満たす向きである。後の章で具体的な実例が与えられるまでは、構成全体がこの仮定されたステップ記述に相対したままである。
<!--/-->

```agda
  module _ {n : ℕ} (v b f : Fin n) (γ : S ^ n)
           (ob : IsOrd (fst (lookup b γ)))
           (vals : Values (lookup f γ) (fst (lookup b γ)))
           (ents : Entries (lookup f γ) (fst (lookup b γ))) where
    private
```

<!--en-->
Once an ordinal bound, a sound table, and entries at every smaller argument have been fixed, the variable form of the condition has an exact mathematical meaning. A set satisfies it precisely when it is one of the ordered pairs related by the stage order. This equivalence is the semantic bridge between the object-language step and the host-level relation.
<!--zh-->
固定序数界、健全的表以及每个较小实参处的条目后，条件的变元形式便有了精确的数学含义：一个集合满足它，当且仅当它是该层序所关联的有序对之一。这条等价是对象语言步进与宿主层关系之间的语义桥梁。
<!--ja-->
順序数の上界、正しい表、各小さい引数での要素を固定すると、条件の変数形式には正確な数学的意味が与えられる。ある集合がこの条件を満たすことと、その段階の順序が関係づける順序対の一つであることは同値である。この同値が、対象言語の一段階とホスト側の関係を結ぶ意味論的な橋になる。
<!--/-->

```agda
      same : (z : S) → ((z ∷ γ) ⊨ Cond b f) ≡ Related (fst (lookup b γ)) (fst z)
      same = cond-spec b f γ ob vals ents

```

<!--en-->
Suppose a candidate value satisfies the extensional step. Membership in that value then implies the condition, hence relatedness, while relatedness implies the condition and therefore membership. These two implications say exactly that the candidate realizes the relation at the chosen ordinal.
<!--zh-->
设一个候选取值满足此外延步进。对该取值的隶属先推出条件成立，再由语义桥得到关联性；反过来，关联性推出条件成立，继而推出隶属。两条蕴含合在一起，恰好说明候选取值实现所选序数处的关系。
<!--ja-->
候補の値が外延的な一段階を満たすとする。その値への所属から条件が従い、さらに関係づけられていることが従う。逆に、関係づけられていることから条件が従い、そこから所属が従う。この二つの含意を合わせると、候補が選んだ順序数での関係を実現することになる。
<!--/-->

```agda
    step-rel : ⟨ γ ⊨ StepAt v b f ⟩ → IsRel (fst (lookup b γ)) (lookup v γ)
    step-rel h z =
        (λ hz → subst ⟨_⟩ (same z) (extAt-out v (Cond b f) γ h z hz))
      , (λ hz → extAt-in v (Cond b f) γ h z (subst ⟨_⟩ (sym (same z)) hz))

```

<!--en-->
The same argument reverses. If a set already realizes the stage relation, its two membership implications can be transported across the semantic equivalence to prove the extensional step. Thus the step formula and realization carry the same information once the ordinal and the table hypotheses are available.
<!--zh-->
同一论证也可反向使用。若一个集合已经实现该层关系，就能把它的两条隶属蕴含沿语义等价搬运，得到此外延步进。因此，在序数与表的假设齐备时，步进公式的满足与关系的实现携带相同的信息。
<!--ja-->
同じ議論は逆向きにも使える。ある集合がすでに段階の関係を実現していれば、その二つの所属に関する含意を意味論的同値に沿って運び、外延的な一段階を証明できる。したがって、順序数と表についての仮定がそろえば、一段階の論理式と関係の実現は同じ情報を表す。
<!--/-->

```agda
    step-table : IsRel (fst (lookup b γ)) (lookup v γ) → ⟨ γ ⊨ StepAt v b f ⟩
    step-table sp = extAt-in-both v (Cond b f) γ
      (λ z hz → subst ⟨_⟩ (sym (same z)) (sp z .fst hz))
      (λ z h → sp z .snd (subst ⟨_⟩ (same z) h))
```

<!--en-->
## Approximations and the graph
<!--zh-->
## 诸逼近，与那个图
<!--ja-->
## 近似とグラフ
<!--/-->

<!--en-->
The generic recursion shape is now specialized to this step. An approximation is a set-coded table with the prescribed domain and a valid step at every recorded entry; a graph says that some such approximation supports the value at the current argument; and the paired graph records the argument together with that value. The available introduction and elimination principles let the rest of the construction reason through these meanings without choosing witnesses from truncated existences.
<!--zh-->
现在把通用递归形状专用于这条步进。逼近是集合编码的表，它具有指定定义域，并使每个已记录条目满足相应步进；图断言存在这样的逼近来支撑当前实参处的取值；成对图则把实参与该取值一起记录。相应的引入和消去原则使后文能按这些含义推理，而不必从命题截断的存在中选出见证。
<!--ja-->
ここで一般の再帰の形をこの一段階に特殊化する。近似とは、指定された定義域をもち、記録した各要素で一段階の条件を満たす集合符号化された表である。グラフは、そのような近似が現在の引数での値を支えることを述べ、順序対を値とするグラフは引数とその値を一緒に記録する。導入規則と除去規則を使えば、命題的切り詰めの存在から証人を選ぶことなく、以後はこの意味に沿って議論できる。
<!--/-->

```agda
  module A = RecShape StepAt
  open A using ( ApproxAt; GraphAt; ApproxAt-dom; ApproxAt-value; ApproxAt-step
               ; ApproxAt-in; GraphOf; Graph-in; Graph-out
               ; PairGraphAt; PairOf; PairGraph-in; PairGraph-out )
```

<!--en-->
## Every value an approximation records
<!--zh-->
## 逼近所记录的每个取值
<!--ja-->
## 近似が記録するすべての値
<!--/-->

<!--en-->
To prove that an approximation records only correct values, fix its table and domain and consider one possible argument `u`. The induction property says that if `u` is constructible and ordinal, then every recorded pair `(u,r)` has a value `r` realizing the relation at `u`. It deliberately quantifies over every recorded value, so functionality is not assumed.
<!--zh-->
为了证明逼近只记录正确取值，先固定其表与定义域，再考察一个可能的实参 `u`。归纳性质说：若 `u` 可构造且为序数，则每个已记录对 `(u,r)` 的取值 `r` 都实现 `u` 处的关系。这里有意对所有已记录取值量化，因此没有预先假设单值性。
<!--ja-->
近似が正しい値だけを記録することを示すため、その表と定義域を固定し、引数の候補 `u` を考える。帰納に用いる性質は、`u` が構成可能な順序数なら、記録された各対 `(u,r)` の値 `r` が `u` での関係を実現する、というものである。記録されたすべての値を対象にするため、単値性を仮定していない。
<!--/-->

```agda
  module _ {n : ℕ} (f a : Fin n) (γ : S ^ n) where
    private
      Value : V ℓ → Type (ℓ-suc ℓ)
      Value u = ⟨ isL u ⟩ → IsOrd u → (r : S)
              → ⟨ pr u (fst r) ∈ fst (lookup f γ) ⟩ → IsRel u r
```

<!--en-->
Membership induction is applied to the underlying set of the recorded argument `c`. This is legitimate for the Type-valued property just described: membership induction is a recursion principle for arbitrary dependent type families, not only for propositions. The approximation's domain is assumed ordinal so that membership below one recorded argument remains inside that domain.
<!--zh-->
证明对已记录实参 `c` 的底层集合作沿成员关系的归纳。上述性质取值于一般的类型，仍可使用这条原则，因为沿成员关系的归纳允许任意依值类型族，并不只允许命题。逼近的定义域另有序数性假设，以保证一个已记录实参以下的成员仍落在该定义域内。
<!--ja-->
記録された引数 `c` の基礎の集合について、所属に沿う帰納を行う。この原理は命題だけでなく任意の依存型族に対する再帰原理なので、先ほどの Type 値の性質にも適用できる。近似の定義域には別に順序数性を仮定し、記録された一つの引数より下の要素が同じ定義域にとどまることを保証する。
<!--/-->

```agda

    approx-val : ⟨ γ ⊨ ApproxAt f a ⟩ → IsOrd (fst (lookup a γ))
               → (c : S) → IsOrd (fst c) → (r : S)
               → ⟨ pr (fst c) (fst r) ∈ fst (lookup f γ) ⟩ → IsRel (fst c) r
    approx-val h oa c = ∈-induction {P = Value} go (fst c) (snd c)
      where
```

<!--en-->
At the induction step, let `r` be a value recorded at `u`. The approximation itself says that this entry satisfies the recursive step computed from the same table. To read that step as realization at `u`, it remains to supply a sound and complete restriction of the table below `u`; these are exactly the two obligations discharged by the induction hypothesis and the domain information.
<!--zh-->
在归纳步中，设 `r` 是记录在 `u` 处的取值。逼近本身断言这个条目满足由同一张表计算出的递归步进。要把该步进读成 `u` 处关系的实现，还需给出表在 `u` 以下的健全性与完备性；这两项义务分别由归纳假设和定义域信息解决。
<!--ja-->
帰納の一段階で、`r` を `u` に記録された値とする。近似自身が、この要素は同じ表から計算される再帰の一段階を満たすと述べている。この一段階を `u` での関係の実現として読むには、`u` より下に制限した表の正しさと完全性が必要である。この二つを、帰納仮定と定義域の情報がそれぞれ与える。
<!--/-->

```agda
      go : (u : V ℓ) → ((t : V ℓ) → ⟨ t ∈ u ⟩ → Value t) → Value u
      go u IH hu ou r p = step-rel zero (suc zero) (sh2 f) (r ∷ d ∷ γ) ou vals ents
        (ApproxAt-step f a γ h d r p)
        where
        d : S
```

<!--en-->
The argument `u` is paired with its constructibility proof so that it can be used as an element of the model. Because `(u,r)` is recorded, the exact-domain clause of the approximation places `u` in the approximation's ordinal domain. This is the point at which a fact about a table entry becomes the bound needed for all smaller recursive calls.
<!--zh-->
实参 `u` 与其可构造性证明打包后，便可作为模型中的元素使用。由于 `(u,r)` 已被记录，逼近的精确定义域子句推出 `u` 属于逼近的序数定义域。正是在这里，关于一个表条目的事实转化成了所有更小递归调用所需的界。
<!--ja-->
引数 `u` をその構成可能性の証明と組にすると、モデルの要素として扱える。`(u,r)` が記録されているので、近似の正確な定義域の節から、`u` が近似の順序数領域に属することが分かる。ここで、一つの表要素についての事実が、より小さい再帰呼出しすべてに必要な上界へ変わる。
<!--/-->

```agda
        d = u , hu
        u∈a : ⟨ u ∈ fst (lookup a γ) ⟩
        u∈a = ApproxAt-dom f a γ h d r p
        vals : Values (lookup f γ) u
        vals e t e∈ q =
```

<!--en-->
For an entry `(e,t)` with `e∈u`, the induction hypothesis proves that `t` realizes the relation at `e`; membership in an ordinal also makes `e` ordinal. Completeness is obtained differently: transitivity of the approximation's ordinal domain turns `e∈u` and `u` in the domain into `e` in the domain, and the approximation supplies some value there under propositional truncation. The recursive step at `u` is therefore fully justified. In particular, two values recorded at one argument can later be identified because both realize the same class, although no separately named uniqueness lemma is introduced here.
<!--zh-->
对于满足 `e∈u` 的条目 `(e,t)`，归纳假设证明 `t` 实现 `e` 处的关系；序数的成员法则同时给出 `e` 的序数性。完备性的来源不同：逼近定义域的传递性把 `e∈u` 与 `u` 属于定义域合成为 `e` 属于定义域，随后逼近以命题截断形式给出那里存在某个取值。因此，`u` 处的递归步进得到了全部所需前提。特别地，同一实参处的两个已记录取值都实现同一个类，故以后可由外延唯一性认同它们；此处并未引入另一个具名的唯一性引理。
<!--ja-->
`e∈u` を満たす要素 `(e,t)` については、帰納仮定が `t` は `e` での関係を実現すると示す。また、順序数の要素であることから `e` も順序数である。完全性は別の仕方で得られる。近似の順序数領域の推移性により、`e∈u` と `u` が領域に属することから `e` も領域に属し、近似がそこで何らかの値の存在を命題的切り詰めのもとで与える。これで `u` での再帰の一段階に必要な前提がすべてそろう。同じ引数に二つの値が記録されていれば、どちらも同じクラスを実現するので後に外延的一意性から同一視できるが、ここでは別の名前をもつ一意性補題は導入しない。
<!--/-->

```agda
          IH (fst e) e∈ (snd e) (mem-ord {A = u} ou (fst e) e∈) t q
        ents : Entries (lookup f γ) u
        ents e e∈ = ApproxAt-value f a γ h e (oa .fst {x = u} {y = fst e} e∈ u∈a)

```

<!--en-->
## The graph holds of nothing else
<!--zh-->
## 图对别的什么都不成立
<!--ja-->
## グラフが決定する値
<!--/-->

<!--en-->
A graph assertion contains only a propositionally truncated witness for the supporting approximation. Nevertheless, its desired conclusion, that the displayed value realizes the relation at the ordinal argument, is itself a proposition. The truncation may therefore be eliminated into that conclusion. This establishes correctness of a graph value; uniqueness still requires comparing two realizing sets by extensionality.
<!--zh-->
图的断言只以命题截断形式包含支撑它的逼近见证。不过，所需结论「图中取值实现序数实参处的关系」本身是命题，因此可以把该命题截断消去到此结论中。这一步确立图取值的正确性；若要得到唯一性，仍须再用外延性比较两个实现集合。
<!--ja-->
グラフの主張が含む、それを支える近似の証人は命題的切り詰めの中にある。しかし、求める結論である「表示された値が順序数の引数での関係を実現する」は命題である。したがって、その結論へ切り詰めを除去できる。ここで得られるのはグラフの値の正しさであり、一意性にはさらに二つの実現集合を外延性で比較する必要がある。
<!--/-->

```agda
  module _ {n : ℕ} (w b : Fin n) (γ : S ^ n) where
    graph-only : ⟨ γ ⊨ GraphAt w b ⟩ → IsOrd (fst (lookup b γ))
               → IsRel (fst (lookup b γ)) (lookup w γ)
    graph-only h ob = rec₁ (snd (Realizes (fst (lookup b γ)) (lookup w γ)))
      read (Graph-out w b γ h)
```

<!--en-->
After a graph witness is opened inside this propositional target, it provides an approximation `f` together with the outer step at the bound. The step can be read as realization once `f` is known to have correct values and entries at every argument below the bound. Those two facts are recovered from the approximation rather than assumed afresh.
<!--zh-->
在这个命题目标内打开图见证后，可以得到逼近 `f` 以及界处的外层步进。只要知道 `f` 在界下每个实参处都有正确取值与条目，就能把该步进读成关系实现。这两项事实从逼近本身恢复，无须重新假设。
<!--ja-->
この命題の目標の中でグラフの証人を開くと、近似 `f` と上界での外側の一段階が得られる。`f` が上界より下の各引数で正しい値と要素をもつと分かれば、その一段階を関係の実現として読める。この二つの事実は新たに仮定するのではなく、近似から取り出す。
<!--/-->

```agda
      where
      read : GraphOf w b γ → IsRel (fst (lookup b γ)) (lookup w γ)
      read (f , (ha , hs)) = step-rel (suc w) (suc b) zero (f ∷ γ) ob vals ents hs
        where
        vals : Values f (fst (lookup b γ))
```

<!--en-->
Correctness of every value recorded by `f` is the preceding membership-induction result, applied to each member of the ordinal bound; the member is ordinal by `mem-ord`. Completeness below the bound is already the value-existence half of the approximation's exact-domain specification. Hence the outer step yields the promised realization.
<!--zh-->
`f` 所记录每个取值的正确性来自前面的沿成员关系归纳结论，并逐一应用于序数界的成员；`mem-ord` 保证这些成员仍是序数。界下的完备性则正是逼近精确定义域规格中「存在取值」的方向。因此，外层步进给出所需的关系实现。
<!--ja-->
`f` が記録する各値の正しさは、直前の所属に沿う帰納の結果を順序数の上界の各要素に適用して得る。その要素が順序数であることは `mem-ord` が保証する。上界より下での完全性は、近似の正確な定義域の仕様にある値の存在の向きである。したがって、外側の一段階から求める実現が得られる。
<!--/-->

```agda
        vals c r c∈ p = approx-val zero (suc b) (f ∷ γ) ha ob c
          (mem-ord {A = fst (lookup b γ)} ob (fst c) c∈) r p
        ents : Entries f (fst (lookup b γ))
        ents = ApproxAt-value zero (suc b) (f ∷ γ) ha

```

<!--en-->
For the converse direction, begin with a table `h` that is sound on an ordinal bound, has an entry at every point below it, and has no recorded pair whose first component lies outside it. If the proposed current value realizes the relation at the bound, these data are sufficient to exhibit `h` as the approximation hidden by the graph and to verify the graph's outer step.
<!--zh-->
反方向从一张表 `h` 开始：它在某个序数界上健全，在界下每点都有条目，而且没有第一分量落在界外的已记录对。若所提议的当前取值实现界处关系，这些资料便足以把 `h` 展示为图所隐藏的逼近，并验证图的外层步进。
<!--ja-->
逆向きには、順序数の上界上で正しく、その下の各点に要素をもち、第一成分が上界の外にある対を記録しない表 `h` から始める。候補となる現在の値が上界での関係を実現するなら、これらの資料で `h` をグラフが隠している近似として示し、グラフの外側の一段階も検証できる。
<!--/-->

```agda
    graph-table : (h : S) → IsOrd (fst (lookup b γ))
                → Values h (fst (lookup b γ)) → Entries h (fst (lookup b γ))
                → Domain h (fst (lookup b γ))
                → IsRel (fst (lookup b γ)) (lookup w γ) → ⟨ γ ⊨ GraphAt w b ⟩
    graph-table h ob vals ents dom sp = Graph-in w b γ h approx
```

<!--en-->
The outer step follows immediately from the realization hypothesis by the reverse semantic bridge. What remains is the approximation. Its domain must be exact: a first component occurs in some table entry precisely when it lies below the bound. The two directions use different table assumptions, which prevents soundness, completeness, and boundedness from being conflated.
<!--zh-->
外层步进由关系实现假设经反向语义桥直接得到，余下任务是构造逼近。逼近的定义域必须精确：某个第一分量出现在表的某条记录中，当且仅当它属于该界。两个方向分别使用不同的表假设，从而不把健全性、完备性与有界性混为一谈。
<!--ja-->
外側の一段階は、実現の仮定を逆向きの意味論的な橋に通せば直ちに得られる。残るのは近似である。その定義域は正確でなければならず、ある第一成分が表の何らかの要素に現れることと、その第一成分が上界より下にあることが同値である必要がある。二つの向きは異なる表の仮定を使うため、正しさ、完全性、有界性は混同されない。
<!--/-->

```agda
      (step-table (suc w) (suc b) zero (h ∷ γ) ob vals ents sp)
      where
      onDom : (c : S)
            → (⟨ ∃[ r ∶ S ] pr (fst c) (fst r) ∈ fst h ⟩
               → ⟨ fst c ∈ fst (lookup b γ) ⟩)
```

<!--en-->
If some value is recorded at `c`, the witness for that value is propositionally truncated. It may be eliminated because the conclusion `c` belongs to the bound is a proposition, and boundedness then proves that conclusion. Conversely, completeness supplies a merely existing recorded value for every `c` in the bound. Together these directions give the exact domain required of an approximation.
<!--zh-->
若某个取值记录在 `c` 处，该取值的见证位于命题截断中。由于结论「`c` 属于该界」是命题，可以把命题截断消去到这个结论，再由有界性完成证明。反过来，完备性为界中的每个 `c` 给出仅存在意义下的已记录取值。两方向合起来，得到逼近所需的精确定义域。
<!--ja-->
何らかの値が `c` に記録されているとき、その値の証人は命題的切り詰めの中にある。結論である「`c` が上界に属する」は命題なので、そこへ切り詰めを除去し、有界性から結論を得られる。逆に、完全性は上界内の各 `c` に、単に存在する記録値を与える。二つの向きを合わせると、近似が必要とする正確な定義域になる。
<!--/-->

```agda
            × (⟨ fst c ∈ fst (lookup b γ) ⟩
               → ⟨ ∃[ r ∶ S ] pr (fst c) (fst r) ∈ fst h ⟩)
      onDom c = (λ hr → rec₁ (snd (fst c ∈ fst (lookup b γ)))
                          (λ { (r , p) → dom c r p }) hr)
              , ents c
```

<!--en-->
The second approximation clause checks the recursive step at each recorded pair `(c,r)`. It uses the same table `h`, but only through the information relevant below `c`. Thus every existing entry must be viewed locally: `c` must be an ordinal, all recorded values below it must be correct, and every smaller argument must have an entry.
<!--zh-->
逼近的第二个子句在每个已记录对 `(c,r)` 处检查递归步进。它仍使用同一张表 `h`，但只使用与 `c` 以下部分有关的资料。因此，每个现有条目都要局部考察：`c` 必须是序数，其下所有已记录取值都必须正确，并且每个更小实参都必须有条目。
<!--ja-->
近似の第二の節は、記録された各対 `(c,r)` で再帰の一段階を検査する。同じ表 `h` を使うが、`c` より下に関係する情報だけを使う。したがって、既存の各要素を局所的に見て、`c` が順序数であること、その下の記録値がすべて正しいこと、さらに各小さい引数に要素があることを示す。
<!--/-->

```agda

      onStep : (c r : S) → ⟨ pr (fst c) (fst r) ∈ fst h ⟩
             → ⟨ (r ∷ c ∷ h ∷ γ) ⊨ StepAt zero (suc zero) (suc (suc zero)) ⟩
      onStep c r p = step-table zero (suc zero) (suc (suc zero)) (r ∷ c ∷ h ∷ γ)
        oc vals' ents' (vals c r c∈ p)
        where
```

<!--en-->
Boundedness first turns the recorded pair into `c` below the ambient bound. Since that bound is ordinal, `c` is ordinal as well. The soundness hypothesis can now be restricted to `c`: whenever an entry `(e,t)` is actually recorded, boundedness places `e` in the ambient bound and the original soundness statement applies.
<!--zh-->
有界性先把已记录对转化为 `c` 属于外围界。由于该界是序数，`c` 也为序数。此时可以把健全性限制到 `c` 以下：只要条目 `(e,t)` 确实被记录，有界性便把 `e` 放回外围界，原来的健全性陈述因而适用。
<!--ja-->
まず有界性から、記録された対の第一成分 `c` が周囲の上界より下にあることが分かる。その上界は順序数なので、`c` も順序数である。これで正しさの仮定を `c` より下に制限できる。要素 `(e,t)` が実際に記録されていれば、有界性が `e` を周囲の上界に置くため、もとの正しさを適用できる。
<!--/-->

```agda
        c∈ : ⟨ fst c ∈ fst (lookup b γ) ⟩
        c∈ = dom c r p
        oc : IsOrd (fst c)
        oc = mem-ord {A = fst (lookup b γ)} ob (fst c) c∈
        vals' : Values h (fst c)
```

<!--en-->
Notice the asymmetry between local soundness and local completeness. Soundness needs only the fact that an entry is recorded, because boundedness recovers its ambient-domain membership. Completeness starts from `e∈c`; transitivity of the ambient ordinal combines this with `c` below the bound, after which the original completeness hypothesis supplies an entry at `e`.
<!--zh-->
局部健全性与局部完备性的来源并不对称。健全性只需知道某条目已被记录，因为有界性可恢复其对外围定义域的隶属。完备性则从 `e∈c` 出发，利用外围序数的传递性和 `c` 属于该界得到 `e` 属于该界，随后原来的完备性假设在 `e` 处给出条目。
<!--ja-->
局所的な正しさと局所的な完全性の由来は対称ではない。正しさには要素が記録されているという事実だけで十分であり、有界性から周囲の領域への所属を回収できる。完全性は `e∈c` から始まり、周囲の順序数の推移性と `c` が上界より下にあることから `e` も上界より下にあると示し、もとの完全性から `e` での要素を得る。
<!--/-->

```agda
        vals' e t _ q = vals e t (dom e t q) q
        ents' : Entries h (fst c)
        ents' e e∈ = ents e (ob .fst {x = fst c} {y = fst e} e∈ c∈)

```

<!--en-->
The exact-domain equivalence and the local step proof are precisely the two conjuncts of an approximation. Packaging them makes `h` a witness for the approximation hidden in the graph. Together with the already verified outer step, this completes the passage from a sound, complete, bounded table to the graph assertion.
<!--zh-->
精确定义域等价与逐条目的局部步进恰是逼近的两个合取项。把它们合在一起，`h` 就成为图中所隐藏逼近的见证。再结合已经验证的外层步进，便完成从健全、完备且有界的表到图断言的方向。
<!--ja-->
正確な定義域の同値と各要素での局所的な一段階は、近似をなす二つの連言である。これらをまとめると、`h` はグラフに隠された近似の証人になる。すでに確かめた外側の一段階と合わせて、正しく完全で有界な表からグラフの主張への向きが完成する。
<!--/-->

```agda
      approx : ⟨ (h ∷ γ) ⊨ ApproxAt zero (suc b) ⟩
      approx = ApproxAt-in zero (suc b) (h ∷ γ)
        (domAt-intro zero (suc b) (h ∷ γ) onDom) onStep
```

<!--en-->
## The pair graph

Replacement acts on a graph whose value is a complete table entry. `PairGraphAt` therefore says that the displayed value is the Kuratowski pair of the current index and some relation set, and that this relation set satisfies `GraphAt` at that index. Its two readings keep the relation-set witness under propositional truncation. This is the bridge from the relation-valued recursion to a replacement image containing indexed entries.
<!--zh-->
## 成对的那个图

替换作用于一张以完整表项为取值的图。因而，`PairGraphAt` 断言所显示的取值是当前索引与某个关系集组成的 Kuratowski 对，并且该关系集在此索引处满足 `GraphAt`。它的两条读式都把关系集见证保留在命题截断之内。这就把取值为关系集的递归连接到由带索引条目组成的替换图像。
<!--ja-->
## 順序対を値とするグラフ

置換公理は、完全な表の項目を値とするグラフに作用する。そこで `PairGraphAt` は、表示された値が現在の添字とある関係集合との Kuratowski 対であり、その関係集合がその添字で `GraphAt` を満たすことを述べる。二つの読みは、関係集合の証人を命題的切り詰めの内側に保つ。これが、関係集合を値とする再帰と、添字つきの項目からなる置換の像との橋になる。
<!--/-->

<!--en-->
## The table, and the relation at the bound
<!--zh-->
## 那张表，与界上的那个关系
<!--ja-->
## 表と上界における関係
<!--/-->

<!--en-->
The class `Recorded B` describes the intended members of a table below `B`. An object belongs to it merely when there are a model element `c` in `B` and a model element `r` realizing the relation at `c`, such that the object is the ordered pair of their underlying sets. The existential data are propositionally truncated. The definition itself does not require `B` to be ordinal; ordinality will matter when this class is used for an ordinal bound.
<!--zh-->
类 `Recorded B` 描述界 `B` 以下一张表应有的成员。一个对象属于该类，是指以命题截断形式存在模型元素 `c` 与 `r`，其中 `c` 属于 `B`，`r` 实现 `c` 处的关系，而且该对象等于二者底层集合组成的有序对。定义本身不要求 `B` 为序数；在序数界上使用这个类时，序数性才发挥作用。
<!--ja-->
クラス `Recorded B` は、`B` より下の表がもつべき要素を記述する。ある対象がこのクラスに属するとは、モデル要素 `c` と `r` が命題的切り詰めのもとで存在し、`c` が `B` に属し、`r` が `c` での関係を実現し、その対象が二つの基礎の集合の順序対に等しいことである。定義そのものは `B` が順序数であることを要求せず、このクラスを順序数の上界で使うときに順序数性が働く。
<!--/-->

```agda
  Recorded : V ℓ → V ℓ → hProp (ℓ-suc ℓ)
  Recorded B z = ∃[ c ∶ S ] (fst c ∈ B) ⊓ (∃[ r ∶ S ]
    ((z ≡ pr (fst c) (fst r)) , setIsSet z (pr (fst c) (fst r)))
    ⊓ Realizes (fst c) r)

```

<!--en-->
A model set is a table for `B` when membership in it is pointwise equivalent to belonging to `Recorded B`. Both directions matter. One excludes every unrelated or out-of-domain object, while the other includes every pair `(c,r)` with `c∈B` and `r` realizing the relation at `c`. Thus `IsTable` expresses exact representation, not only closure under correct entries.
<!--zh-->
模型中的集合若要成为 `B` 的表，它的隶属必须逐点等价于属于 `Recorded B`。两个方向都不可缺少：一个排除不相关对象和定义域外对象，另一个纳入每个满足 `c∈B` 且 `r` 实现 `c` 处关系的对 `(c,r)`。因此，`IsTable` 表达的是精确表示，而不只是对正确条目的封闭性。
<!--ja-->
モデルの集合が `B` の表であるとは、その集合への所属が各点で `Recorded B` への所属と同値であることである。二つの向きがともに必要である。一方は無関係な対象や領域外の対象を排除し、他方は `c∈B` かつ `r` が `c` での関係を実現する各対 `(c,r)` を含める。したがって `IsTable` は、正しい要素についての閉性だけでなく正確な表現を述べる。
<!--/-->

```agda
  IsTable : V ℓ → S → Type (ℓ-suc (ℓ-suc ℓ))
  IsTable B h = (z : S) → (fst z ∈ fst h) ≡ Recorded B (fst z)

```

<!--en-->
The recursive datum at `α` contains two model sets: a table representing all correct entries below `α`, and a set realizing the relation at `α` itself. At the next larger argument, the first component supplies the earlier table needed to check an approximation, while the second supplies the relation value to be entered into a later table. This bundle is data returned by membership recursion. No proof that its type is a proposition is given or needed, because membership induction accepts arbitrary Type-valued families.
<!--zh-->
`α` 处的递归资料包含模型中的两个集合：一张精确表示 `α` 以下所有正确条目的表，以及一个实现 `α` 本身之关系的集合。处理更大实参时，第一个分量提供验证逼近所需的既有表，第二个分量提供要写入后续表的关系取值。这个包是沿成员关系递归返回的数据。这里没有证明其类型是命题，也不需要这样的证明，因为沿成员关系的归纳接受任意 Type 值类型族。
<!--ja-->
`α` での再帰データは、モデル内の二つの集合を含む。一つは `α` より下の正しい要素すべてを正確に表す表であり、もう一つは `α` 自身での関係を実現する集合である。より大きい引数を扱うとき、第一成分は近似を検査するための既存の表を与え、第二成分は後の表に記録する関係の値を与える。この束は所属に沿う再帰が返すデータである。その型が命題であるという証明はなく、また必要でもない。所属に沿う帰納は任意の Type 値の族を受け取るからである。
<!--/-->

```agda
  Bundle : V ℓ → Type (ℓ-suc (ℓ-suc ℓ))
  Bundle α = Σ[ h ∈ S ] Σ[ r ∈ S ] (IsTable α h × IsRel α r)

```

<!--en-->
Fix an exact table `h` for a bound `B`. To use its specification at a concrete entry, one must align two versions of ordered pairing: the internal pair of model elements and the host-level Kuratowski pair of their underlying sets. The projection law for internal pairing transports the table equivalence to the underlying pair `(c,r)`.
<!--zh-->
固定界 `B` 的一张精确表 `h`。要在具体条目处使用其规格，必须对齐两种有序对：模型元素构成的内部对，以及其底层集合构成的宿主层 Kuratowski 对。内部配对的投影律把表的隶属等价搬运到 `(c,r)` 的底层有序对处。
<!--ja-->
上界 `B` に対する正確な表 `h` を固定する。その仕様を具体的な要素に使うには、モデル要素の内部の順序対と、それらの基礎の集合からなるホスト側の Kuratowski 対をそろえる必要がある。内部対の射影則に沿って表の所属同値を運ぶと、基礎の順序対 `(c,r)` で使える形になる。
<!--/-->

```agda
  module _ (B : V ℓ) (oB : IsOrd B) (h : S) (sp : IsTable B h) where
    private
      atPair : (c r : S)
             → (pr (fst c) (fst r) ∈ fst h) ≡ Recorded B (pr (fst c) (fst r))
      atPair c r = subst (λ x → (x ∈ fst h) ≡ Recorded B x) (prʟ-fst c r)
```

<!--en-->
The exact table specification is applied to the internal pair and then viewed through that projection law. Although the surrounding reading fixes `B` as an ordinal, this alignment itself uses only the table specification and the representation of ordered pairs; it contains no additional ordinal argument.
<!--zh-->
先把精确表规格应用于内部有序对，再经上述投影律阅读所得等价。外围读式虽把 `B` 固定为序数，这一步对齐本身却只使用表规格与有序对的表示，并没有额外的序数论论证。
<!--ja-->
正確な表の仕様を内部の順序対に適用し、その同値を先ほどの射影則を通して読む。周囲の読みでは `B` を順序数として固定しているが、この同定そのものが使うのは表の仕様と順序対の表現だけであり、追加の順序数論的議論はない。
<!--/-->

```agda
        (sp (prʟ c r))

```

<!--en-->
An actual table entry `(c,r)` can now be read in two ways at once. Exactness yields a recorded decomposition, from which one recovers both `c∈B`, the domain fact, and that `r` realizes the relation at `c`, the value-soundness fact. Applying this reading to every entry gives `Domain h B` and `Values h B`.
<!--zh-->
现在可以同时从两个方面读取一个实际表条目 `(c,r)`。精确性给出它的已记录分解，由此恢复定义域事实 `c∈B`，以及取值健全性事实「`r` 实现 `c` 处关系」。把这个读式应用于每个条目，就得到 `Domain h B` 与 `Values h B`。
<!--ja-->
これで実際の表要素 `(c,r)` を二つの面から同時に読める。正確性から記録された形への分解が得られ、そこから定義域の事実 `c∈B` と、値の正しさである「`r` が `c` での関係を実現する」を回収する。この読みを各要素に適用すると、`Domain h B` と `Values h B` が得られる。
<!--/-->

```agda
    table-out : Domain h B × Values h B
    table-out = (λ c r p → read c r p .fst) , (λ c r _ p → read c r p .snd)
      where
      read : (c r : S) → ⟨ pr (fst c) (fst r) ∈ fst h ⟩
           → ⟨ fst c ∈ B ⟩ × IsRel (fst c) r
```

<!--en-->
The decomposition supplied by `Recorded` is propositionally truncated, so its elimination needs a proposition-valued target. Here the target is the product of membership in `B` and realization of the relation. Membership is a proposition, realization is a proposition, and their product is again a proposition. This, rather than any property of the whole bundle, is what licenses the elimination.
<!--zh-->
`Recorded` 给出的分解位于命题截断中，所以消去它时目标必须为命题。这里的目标是「属于 `B`」与「实现该关系」的积；隶属是命题，关系实现也是命题，二者的积仍是命题。消去的合法性来自这个局部目标，而不是整个包的任何性质。
<!--ja-->
`Recorded` が与える分解は命題的切り詰めの中にあるため、その除去先は命題でなければならない。ここでの目標は、`B` への所属と関係の実現との積である。所属も実現も命題であり、その積も命題である。除去を正当化するのはこの局所的な目標であって、束全体についての性質ではない。
<!--/-->

```agda
      read c r p = rec₁ isPropBoth outer (subst ⟨_⟩ (atPair c r) p)
        where
        isPropBoth : isProp (⟨ fst c ∈ B ⟩ × IsRel (fst c) r)
        isPropBoth = isProp× (snd (fst c ∈ B)) (snd (Realizes (fst c) r))

```

<!--en-->
Inside the propositional elimination, suppose the recorded decomposition uses another pair `(d,t)`. Equality of the Kuratowski pairs `(c,r)` and `(d,t)` forces equality of their first underlying components and equality of their second underlying components. The first equality will transfer domain membership, while the second aligns the proposed value with the realizing value from the decomposition.
<!--zh-->
在命题消去的内部，设已记录分解使用的是另一对 `(d,t)`。Kuratowski 对 `(c,r)` 与 `(d,t)` 相等，便迫使它们的第一底层分量相等，也迫使第二底层分量相等。第一条等式用于搬运定义域隶属，第二条等式用于把待读取值与分解中的实现取值对齐。
<!--ja-->
命題への除去の内側で、記録された分解が別の対 `(d,t)` を使うとする。Kuratowski 対 `(c,r)` と `(d,t)` の等しさから、第一の基礎成分どうしと第二の基礎成分どうしがそれぞれ等しいと分かる。第一の等しさは定義域への所属を運び、第二の等しさは読みたい値と分解に現れた実現値をそろえる。
<!--/-->

```agda
        inner : (d t : S) → ⟨ fst d ∈ B ⟩
              → (pr (fst c) (fst r) ≡ pr (fst d) (fst t)) → IsRel (fst d) t
              → ⟨ fst c ∈ B ⟩ × IsRel (fst c) r
        inner d t d∈ q hr =
            subst (λ x → ⟨ x ∈ B ⟩) (sym (pr-inj q .fst)) d∈
```

<!--en-->
The first-component equality transports `d∈B` to `c∈B`. Equality of the second underlying sets lifts to equality of the model elements `r` and `t`, because their constructibility certificates are propositions and carry no extra choice. Realization can then be transported simultaneously along the index equality and this value equality, yielding realization at exactly `(c,r)`.
<!--zh-->
沿第一分量等式可把 `d∈B` 搬运为 `c∈B`。第二底层集合的等式还能提升为模型元素 `r` 与 `t` 的等式，因为二者的可构造性证明都是命题，不携带额外选择。随后同时沿索引等式与取值等式搬运关系实现，便得到恰在 `(c,r)` 处的实现事实。
<!--ja-->
第一成分の等しさに沿って `d∈B` を `c∈B` へ運べる。第二の基礎の集合の等しさはモデル要素 `r` と `t` の等しさへ持ち上がる。構成可能性の証明は命題であり、追加の選択を含まないからである。添字の等しさと値の等しさに同時に沿って実現を運べば、ちょうど `(c,r)` での実現が得られる。
<!--/-->

```agda
          , subst2 IsRel (sym (pr-inj q .fst)) (sym rt) hr
          where
          rt : r ≡ t
          rt = Σ≡Prop (λ x → snd (isL x)) (pr-inj q .snd)

```

<!--en-->
The outer recorded witness first provides an index `d` in `B` and a further truncated witness for its realizing value. Since the final pair of facts is propositional, both truncation layers may be eliminated in turn. The endpoint-equality argument just established handles the innermost decomposition.
<!--zh-->
最外层的已记录见证先给出 `B` 中的指数 `d`，以及关于其实现取值的另一层命题截断见证。最终所求的两项事实构成命题，所以可以依次消去这两层命题截断；刚才建立的端点等式论证负责处理最内层分解。
<!--ja-->
記録された外側の証人は、まず `B` に属する添字 `d` と、その実現値についてのさらに切り詰められた証人を与える。最終的に求める二つの事実は命題なので、二層の命題的切り詰めを順に除去できる。先ほどの端点の等しさに関する議論が、最も内側の分解を処理する。
<!--/-->

```agda
        outer : Σ[ d ∈ S ] ( ⟨ fst d ∈ B ⟩
                  × ⟨ ∃[ t ∶ S ] ((pr (fst c) (fst r) ≡ pr (fst d) (fst t))
                        , setIsSet _ (pr (fst d) (fst t))) ⊓ Realizes (fst d) t ⟩ )
              → ⟨ fst c ∈ B ⟩ × IsRel (fst c) r
        outer (d , (d∈ , hs)) = rec₁ isPropBoth
```

<!--en-->
For each possible realizing value `t`, the equality of pairs reduces the witness to the desired facts about `c` and `r`. Because the result does not retain `t`, this use of truncation does not choose a value from the table; it proves only the proposition that the given entry has the required domain and realization properties.
<!--zh-->
对每个可能的实现取值 `t`，有序对等式都把该见证化为关于 `c` 与 `r` 的所需事实。由于结果不保留 `t`，这里对命题截断的使用并未从表中选择取值；它只证明给定条目具有所需定义域性质与关系实现性质这一命题。
<!--ja-->
実現値の候補 `t` ごとに、順序対の等しさから証人を `c` と `r` について求める事実へ変換できる。結果には `t` が残らないため、この切り詰めの使用は表から値を選んでいない。与えられた要素が必要な定義域と実現の性質をもつ、という命題だけを証明している。
<!--/-->

```agda
          (λ { (t , (q , hr)) → inner d t d∈ q hr }) hs

```

<!--en-->
The converse table reading is direct. Given `c∈B` and a model element `r` realizing the relation at `c`, the pair `(c,r)` has the required truncated `Recorded` witness. Exactness of the table then turns that class membership into membership in `h`, with the internal-pair projection supplying the necessary alignment of representations.
<!--zh-->
表读式的反方向较为直接。给定 `c∈B` 以及实现 `c` 处关系的模型元素 `r`，有序对 `(c,r)` 便具有 `Recorded` 所需的命题截断见证。表的精确性再把这项类隶属转成对 `h` 的隶属，而内部有序对的投影律负责对齐两种表示。
<!--ja-->
表を読む逆向きは直接的である。`c∈B` と、`c` での関係を実現するモデル要素 `r` が与えられれば、対 `(c,r)` は `Recorded` が要求する命題的切り詰められた証人をもつ。表の正確性により、そのクラスへの所属を `h` への所属へ変え、内部対の射影則が二つの表現をそろえる。
<!--/-->

```agda
    table-in : (c r : S) → ⟨ fst c ∈ B ⟩ → IsRel (fst c) r
             → ⟨ pr (fst c) (fst r) ∈ fst h ⟩
    table-in c r c∈ hr = subst ⟨_⟩ (sym (atPair c r))
      ∣ c , (c∈ , ∣ r , (refl , hr) ∣₁) ∣₁

```

<!--en-->
Before the relation at an ordinal `α` can be obtained by separation, all possible related pairs need one containing set in `L`. The required bound returns a model set `D` containing every object in `Related α`. It is only a common container and may have unrelated members; exactness is not claimed at this stage.
<!--zh-->
在通过分离得到序数 `α` 处的关系之前，需要先在 `L` 中找到一个集合，容纳所有可能的相关有序对。所需的界返回模型集合 `D`，使 `Related α` 中的每个对象都属于 `D`。它只是共同容器，可能含有无关成员；此时并不声称精确性。
<!--ja-->
順序数 `α` での関係を分出によって得る前に、関係しうるすべての順序対を含む一つの `L` の集合が必要である。求める上界は、`Related α` の各対象を含むモデル集合 `D` を返す。これは共通の容器にすぎず、無関係な要素を含んでもよいため、この時点では正確性を主張しない。
<!--/-->

```agda
  bound : (α : V ℓ) (oα : IsOrd α)
        → Σ[ D ∈ S ] ((z : S) → ⟨ Related α (fst z) ⟩ → ⟨ fst z ∈ fst D ⟩)
  bound α oα = d .fst , confine
    where
    ixL : ⟪ Lset α ⟫ → S
```

<!--en-->
The small presentation of `Lset α` supplies indices for all of its members. Each index is turned into a model element by pairing the presented underlying set with its constructibility proof, obtained from membership in the constructible stage. This makes internal ordered pairing available for every presented endpoint.
<!--zh-->
`Lset α` 的小呈现为其所有成员提供索引。每个索引所呈现的底层集合与其可构造性证明打包，成为模型元素；该证明来自它对可构造层的隶属。于是，每个被呈现端点都可用于内部有序配对。
<!--ja-->
`Lset α` の小さい提示は、その全要素に添字を与える。各添字が提示する基礎の集合を、構成可能な段階への所属から得た構成可能性の証明と組にして、モデル要素にする。これにより、提示された各端点について内部の順序対を作れる。
<!--/-->

```agda
    ixL m = ⟪ Lset α ⟫↪ m , Lset→isL α oα (⟪ Lset α ⟫↪ m) (memOf (Lset α) m)

```

<!--en-->
Pairs of presentation indices form a small indexing type. Applying the common-domain principle to the family of their internal ordered pairs gives a model set `D` containing every member of that family. The principle supplies containment only; it neither computes the exact image nor filters pairs according to the stage order.
<!--zh-->
呈现索引的有序对形成一个小索引类型。把共同定义域原则应用于这些索引所对应的内部有序对族，便得到模型集合 `D`，其中包含该族的每个成员。这条原则只给出包含关系，既不计算精确像，也不按照层序筛选有序对。
<!--ja-->
提示の添字の対は小さい添字型をなす。それらに対応する内部順序対の族へ共通領域の原理を適用すると、その族の各要素を含むモデル集合 `D` が得られる。この原理が与えるのは包含だけであり、正確な像を計算せず、段階の順序に従って対を選別することもない。
<!--/-->

```agda
    d : Σ[ D ∈ S ] ((p : ⟪ Lset α ⟫ × ⟪ Lset α ⟫)
                    → ⟨ prʟ (ixL (fst p)) (ixL (snd p)) ∈ˢ D ⟩)
    d = smallDom (⟪ Lset α ⟫ × ⟪ Lset α ⟫) (λ p → prʟ (ixL (fst p)) (ixL (snd p)))

```

<!--en-->
The common bound must also be usable for ordinary members `a,b` of `Lset α`, not just for presentation indices. Represent each member by its fiber index, use the bound for the corresponding internal pair, and transport membership along the equality between the presented pair and the host-level pair `pr(fst a,fst b)`. Thus every pair of stage members lies in `D`.
<!--zh-->
共同界不仅要适用于呈现索引，还要适用于 `Lset α` 的普通成员 `a,b`。先用各自的纤维索引表示这两个成员，再对相应内部有序对使用共同界，并沿「被呈现有序对等于宿主层有序对 `pr(fst a,fst b)`」的等式搬运隶属。因此，该层任意两个成员组成的有序对都属于 `D`。
<!--ja-->
共通の上界は提示の添字だけでなく、`Lset α` の通常の要素 `a,b` にも使えなければならない。各要素をそのファイバー添字で表し、対応する内部順序対について上界を使い、提示された対とホスト側の対 `pr(fst a,fst b)` との等しさに沿って所属を運ぶ。したがって、段階の任意の二要素からなる順序対は `D` に属する。
<!--/-->

```agda
    onPair : (a b : Mem (Lset α)) → ⟨ pr (fst a) (fst b) ∈ fst (d .fst) ⟩
    onPair a b = subst (λ x → ⟨ x ∈ fst (d .fst) ⟩)
      (prʟ-fst (ixL (fa .fst)) (ixL (fb .fst))
        ∙ cong₂ pr (fa .snd) (fb .snd))
      (d .snd (fa .fst , fb .fst))
```

<!--en-->
Membership proofs for `a` and `b` identify them with elements of the small presentation. The resulting fiber equalities identify both endpoints, and congruence of ordered pairing identifies the two host-level pairs. Combined with the projection law for internal pairing, this is the equality used in the preceding transport.
<!--zh-->
`a` 与 `b` 的隶属证明把它们分别认同为小呈现中的元素，所得纤维等式对齐两个端点；有序配对的合同性进而对齐两个宿主层有序对。再结合内部配对的投影律，就得到上一段搬运所需的等式。
<!--ja-->
`a` と `b` の所属証明は、それぞれを小さい提示の要素と同定する。得られるファイバーの等しさが二つの端点をそろえ、順序対を作る操作の合同性がホスト側の二つの対を同定する。内部対の射影則と合わせると、直前の所属の輸送に必要な等しさになる。
<!--/-->

```agda
      where
      fa = ∈-asFiber {a = fst a} {b = Lset α} (snd a)
      fb = ∈-asFiber {a = fst b} {b = Lset α} (snd b)

```

<!--en-->
Now take an arbitrary object in `Related α`. Its definition gives, through three nested propositionally truncated existentials, an ordinal certificate and two members `a,b` of `Lset α`, together with an equality identifying the object with their pair and the propositionally truncated comparison fact. The target, membership in `D`, is a proposition, so the three existential truncations may be eliminated one after another. Containment depends only on the endpoints and their pair equality; even the truncated comparison is unnecessary for this coarse bound.
<!--zh-->
现取 `Related α` 中的任意对象。它的定义通过三层嵌套且经过命题截断的存在量词，给出序数性证明、`Lset α` 的两个成员 `a,b`，以及把该对象认同为二者有序对的等式；层序比较本身还保留在命题截断之内。目标「属于 `D`」是命题，因此可以逐层消去三层存在量词的命题截断。这个粗略界只依赖两个端点及有序对等式，连截断后的比较事实也无须使用。
<!--ja-->
`Related α` の任意の対象を取る。その定義は、命題的に切り詰められた三重の存在量化を通して、順序数性の証明、`Lset α` の二要素 `a,b`、および対象をその順序対と同定する等しさを与える。段階順序の比較そのものも、さらに命題的切り詰めの内側にある。目標である `D` への所属は命題なので、三つの存在量化の切り詰めを順に除去できる。この粗い上界に必要なのは二つの端点と対の等しさだけであり、切り詰められた比較の事実さえ使わない。
<!--/-->

```agda
    confine : (z : S) → ⟨ Related α (fst z) ⟩ → ⟨ fst z ∈ fst (d .fst) ⟩
    confine z = rec₁ (snd (fst z ∈ fst (d .fst)))
      (λ { (_ , h₁) → rec₁ (snd (fst z ∈ fst (d .fst)))
        (λ { (a , h₂) → rec₁ (snd (fst z ∈ fst (d .fst)))
          (λ { (b , (q , _)) →
```

<!--en-->
The pair of recovered endpoints already belongs to `D` by the previous result. Transporting this membership along the reverse of the recovered pair equality places the original object in `D`. The witnesses remain confined to the propositional proof, so the bound does not choose endpoints for each related object.
<!--zh-->
由前面的结论，恢复出的两个端点所成有序对已经属于 `D`。沿所恢复有序对等式的反向搬运这项隶属，就得到原对象属于 `D`。这些见证只留在命题证明内部，所以该界并没有为每个相关对象选择端点。
<!--ja-->
回収した二つの端点からなる順序対は、先の結果によりすでに `D` に属する。回収した対の等しさの逆向きにこの所属を運ぶと、もとの対象が `D` に属すると分かる。証人は命題の証明の内部にとどまるため、この上界は各対象の端点を選んでいない。
<!--/-->

```agda
            subst (λ x → ⟨ x ∈ fst (d .fst) ⟩) (sym q) (onPair a b) }) h₂ }) h₁ })

```

<!--en-->
The table and current relation are constructed together by membership recursion. Its actual input range is a constructible ordinal: `α` is accompanied by both a proof that it belongs to `L` and a proof that it is ordinal. The recursive value is the bundle just described, and the definition is sealed so later arguments use its specifications. This recursion is valid for a Type-valued family; it does not rely on `Bundle α` being a proposition.
<!--zh-->
表与当前关系通过沿成员关系的递归同时构造。它的实际输入范围是配有可构造性证明的序数：`α` 同时带有属于 `L` 的证明和序数性证明。递归取值是前述包，而定义被封装，使后文通过规格使用它。该递归允许 Type 值类型族，并不依赖 `Bundle α` 是命题。
<!--ja-->
表と現在の関係を、所属に沿う再帰で同時に構成する。実際の入力範囲は構成可能な順序数であり、`α` には `L` に属することの証明と順序数性の証明の両方が伴う。再帰の値は先ほどの束であり、後ではその仕様を通して使うよう定義を閉じている。この再帰は Type 値の族に適用でき、`Bundle α` が命題であることには依存しない。
<!--/-->

```agda
  opaque
    tableAt : (α : V ℓ) → ⟨ isL α ⟩ → IsOrd α → Bundle α
    tableAt = ∈-induction {P = λ α → ⟨ isL α ⟩ → IsOrd α → Bundle α}
      (build (PairGraphAt zero (suc zero)) refl)
      where
```

<!--en-->
At the induction step for `α`, assume recursively that every member `δ` of `α` has a bundle whenever its constructibility and ordinality are supplied. The task is to produce the corresponding table below `α` and the relation at `α`. The paired graph formula is kept as an explicit parameter together with an equality to the intended formula; this changes no mathematical hypothesis and lets the replacement argument use exactly that graph.
<!--zh-->
在 `α` 处的归纳步中，递归假设说：对 `α` 的每个成员 `δ`，只要给出其可构造性与序数性，就有相应的包。当前任务是产生 `α` 以下的表以及 `α` 处的关系。成对图公式作为显式参数保留，并带有它等于预期公式的证明；这不增加数学假设，只保证替换论证使用的正是那张图。
<!--ja-->
`α` での帰納の一段階では、`α` の各要素 `δ` について、その構成可能性と順序数性が与えられれば対応する束がある、と再帰的に仮定する。ここでの課題は、`α` より下の表と `α` での関係を作ることである。順序対を値とするグラフの論理式を、意図した論理式との等しさとともに明示的な引数として保つ。これは数学的仮定を増やさず、置換の議論がまさにそのグラフを使うことを保証する。
<!--/-->

```agda
      build : (φ : Formula S 2) → φ ≡ PairGraphAt zero (suc zero)
            → (α : V ℓ)
            → ((δ : V ℓ) → ⟨ δ ∈ α ⟩ → ⟨ isL δ ⟩ → IsOrd δ → Bundle δ)
            → ⟨ isL α ⟩ → IsOrd α → Bundle α
      build φ qφ α IH hα oα = rep .fst .fst , (sep .fst .fst , (spec , rspec))
```

<!--en-->
The ordinal `α` and its constructibility proof form a model element `A`. This is the internal domain over which the paired graph will be considered: its members are precisely the smaller sets that the membership-recursive hypothesis can address once their ordinalness has been established.
<!--zh-->
序数 `α` 与其可构造性证明组成模型元素 `A`。它将作为考察成对图的内部定义域；其中的成员正是那些更小集合，只要建立其序数性，沿成员关系的递归假设便可处理它们。
<!--ja-->
順序数 `α` とその構成可能性の証明を組にして、モデル要素 `A` を作る。これは順序対を値とするグラフを考える内部の定義域である。その要素は、順序数性を示せば所属に沿う再帰仮定を適用できる、より小さい集合にちょうど当たる。
<!--/-->

```agda
        where
        A : S
        A = α , hα

```

<!--en-->
Every member `c` of an ordinal `α` is itself an ordinal. This inherited ordinalness is essential because the recursive construction is defined only on constructible ordinals, not on arbitrary constructible members. No truncation is involved in obtaining this certificate.
<!--zh-->
序数 `α` 的每个成员 `c` 本身仍是序数。这项继承的序数性不可缺少，因为递归构造只定义在可构造序数上，而不是任意可构造成员上。取得这份序数性证明不涉及命题截断。
<!--ja-->
順序数 `α` の各要素 `c` はそれ自身も順序数である。この継承された順序数性は不可欠である。再帰的構成の定義域は任意の構成可能な要素ではなく、構成可能な順序数だからである。この順序数性の証明を得る際に命題的切り詰めは使わない。
<!--/-->

```agda
        ordOf : (c : S) → ⟨ fst c ∈ α ⟩ → IsOrd (fst c)
        ordOf c c∈ = mem-ord {A = α} oα (fst c) c∈

```

<!--en-->
For `c∈α`, the model element `c` already carries its constructibility proof, and ordinal membership supplies its ordinalness. These are exactly the inputs needed to apply the induction hypothesis. The result is the full bundle at `c`: both the exact table below `c` and a realizing relation at `c`.
<!--zh-->
对于 `c∈α`，模型元素 `c` 已携带其可构造性证明，而序数成员法则给出其序数性。这些正是应用归纳假设所需的输入。所得结果是 `c` 处的完整包，其中同时含有 `c` 以下的精确表和 `c` 处的关系实现集合。
<!--ja-->
`c∈α` のとき、モデル要素 `c` はすでに構成可能性の証明をもち、順序数の要素であることから順序数性も得られる。これは帰納仮定を適用するために必要な入力そのものである。結果として、`c` より下の正確な表と `c` での関係の実現集合をともに含む、`c` での完全な束が得られる。
<!--/-->

```agda
        bun : (c : S) → ⟨ fst c ∈ α ⟩ → Bundle (fst c)
        bun c c∈ = IH (fst c) c∈ (snd c) (ordOf c c∈)

```

<!--en-->
From the recursive bundle at `c`, select its current-relation component and call it the value at `c`. This is a concrete model element, not a witness extracted from the truncated `Entries` field of a table. Its availability is why the recursion carries the relation at each constructible ordinal in its domain together with the table below it.
<!--zh-->
从 `c` 处的递归包中取出当前关系分量，并把它作为 `c` 处的取值。它是一个具体的模型元素，并非从表的命题截断 `Entries` 字段中抽出的见证。递归之所以把定义域内每个可构造序数处的关系与其下的表一同携带，正是为了得到这样的具体取值。
<!--ja-->
`c` での再帰的な束から、現在の関係の成分を取り出し、`c` での値とする。これは具体的なモデル要素であり、表の命題的切り詰められた `Entries` から取り出した証人ではない。定義域内の各構成可能な順序数での関係をその下の表と一緒に再帰が運ぶのは、この具体的な値を利用するためである。
<!--/-->

```agda
        value : (c : S) → ⟨ fst c ∈ α ⟩ → S
        value c c∈ = bun c c∈ .snd .fst

```

<!--en-->
The specification stored with that component states that the chosen value realizes `Related c`. This is exactly the semantic correctness supplied by the induction hypothesis. By itself it asserts neither that the value satisfies the paired graph nor that its pair with `c` belongs to a completed table.
<!--zh-->
与该分量一同存储的规格断言：所选取值实现 `Related c`。这恰是归纳假设所提供的语义正确性。仅凭这项事实，既不能断言该取值满足成对图，也不能断言它与 `c` 组成的有序对已属于一张完成的表。
<!--ja-->
その成分とともに保存された仕様は、選んだ値が `Related c` を実現すると述べる。これは帰納仮定が与える意味論的な正しさそのものである。この事実だけでは、その値が順序対を値とするグラフを満たすことも、`c` との対が完成した表に属することも主張できない。
<!--/-->

```agda
        relOK : (c : S) (c∈ : ⟨ fst c ∈ α ⟩) → IsRel (fst c) (value c c∈)
        relOK c c∈ = bun c c∈ .snd .snd .snd

```

<!--en-->
For each `c` whose underlying ordinal lies below `α`, the induction hypothesis already supplies the relation set at `c`. Replacement must remember which index produced that relation, so its candidate value is the internal ordered pair of `c` with this relation set, rather than the relation set alone.
<!--zh-->
对每个底层序数属于 `α` 的 `c`，归纳假设已经给出 `c` 处的关系集。替换必须保留产生该关系的索引，因此它的候选取值是 `c` 与这个关系集组成的内部有序对，而不是裸关系集。
<!--ja-->
底の順序数が `α` に属する各 `c` について、帰納法の仮定はすでに `c` における関係集合を与えている。置換公理では、どの添字がその関係を生んだかを残す必要があるため、候補となる値は関係集合だけではなく、`c` とその関係集合との内部順序対である。
<!--/-->

```agda
        entry : (c : S) → ⟨ fst c ∈ α ⟩ → S
        entry c c∈ = prʟ c (value c c∈)

```

<!--en-->
It remains to show that this candidate lies on the graph used by replacement. Before forming the pair, the chosen relation set must satisfy the recursive graph at `c`. The bundle at `c` provides both its lower table and its realized relation, while membership of `c` in the ordinal `α` makes `c` an ordinal and permits the general table-to-graph argument to be applied.
<!--zh-->
还须证明这个候选取值落在替换所用的图上。在组成有序对之前，选定的关系集必须满足 `c` 处的递归图。`c` 处的包同时给出其下方的表与该处已实现的关系，而 `c` 属于序数 `α` 又保证 `c` 本身是序数，因而可以应用从表到图的一般论证。
<!--ja-->
次に、この候補が置換公理で用いるグラフ上にあることを示す。順序対を作る前に、選んだ関係集合が `c` における再帰グラフを満たさなければならない。`c` における束は、その下の表とそこで実現された関係をともに与える。また、順序数 `α` に `c` が属することから `c` 自身も順序数なので、表からグラフを得る一般の議論を適用できる。
<!--/-->

```agda
        below : (c : S) (c∈ : ⟨ fst c ∈ α ⟩) (k : S)
              → ⟨ (value c c∈ ∷ k ∷ c ∷ []) ⊨ GraphAt zero (suc (suc zero)) ⟩
        below c c∈ k = graph-table zero (suc (suc zero))
          (value c c∈ ∷ k ∷ c ∷ []) (bun c c∈ .fst) (ordOf c c∈)
          (reads .snd) ents (reads .fst) (relOK c c∈)
```

<!--en-->
The exact specification of the lower table yields two of the three facts required by that argument: every recorded value below `c` realizes the appropriate relation, and no recorded pair has an index outside `c`. The remaining fact is completeness, namely that each member of `c` has some recorded value.
<!--zh-->
下方那张表的精确规格给出该论证所需三项事实中的两项：`c` 以下每个被记录的取值都实现相应关系，并且没有索引在 `c` 之外的有序对被记录。余下的是完备性，即 `c` 的每个成员处都有某个被记录的取值。
<!--ja-->
下方の表の正確な仕様から、この議論に必要な三つの事実のうち二つが得られる。`c` より下で記録された各値は対応する関係を実現し、添字が `c` の外にある順序対は記録されない。残るのは完全性、すなわち `c` の各要素に何らかの記録値があることである。
<!--/-->

```agda
          where
          reads : Domain (bun c c∈ .fst) (fst c) × Values (bun c c∈ .fst) (fst c)
          reads = table-out (fst c) (ordOf c c∈) (bun c c∈ .fst)
                    (bun c c∈ .snd .snd .fst)
          ents : Entries (bun c c∈ .fst) (fst c)
```

<!--en-->
For a member `e` of `c`, transitivity of the ambient ordinal carries `e ∈ c ∈ α` to `e ∈ α`. The induction hypothesis therefore supplies the realized relation at `e`, and the exact table specification at `c` places the pair of `e` with that relation into the lower table. The witness is returned under propositional truncation, exactly as table completeness requires.
<!--zh-->
若 `e` 是 `c` 的成员，环境序数的传递性便把 `e ∈ c ∈ α` 推成 `e ∈ α`。于是归纳假设给出 `e` 处已实现的关系，而 `c` 处表的精确规格把 `e` 与该关系组成的有序对放入下方表中。这个见证置于命题截断之下返回，恰好符合表完备性的要求。
<!--ja-->
`e` が `c` の要素なら、周囲の順序数の推移性により `e ∈ c ∈ α` から `e ∈ α` が従う。したがって帰納法の仮定は `e` における実現関係を与え、`c` における表の正確な仕様は、`e` とその関係との順序対を下方の表へ入れる。この証人は、表の完全性が要求するとおり、命題的切り詰めの中で返される。
<!--/-->

```agda
          ents e e∈ = ∣ value e e∈' , table-in (fst c) (ordOf c c∈) (bun c c∈ .fst)
                         (bun c c∈ .snd .snd .fst) e (value e e∈') e∈ (relOK e e∈') ∣₁
            where
            e∈' : ⟨ fst e ∈ α ⟩
            e∈' = oα .fst {x = fst c} {y = fst e} e∈ c∈
```

<!--en-->
The recursive graph proof for the relation value can now be combined with the canonical identification of the internal ordered pair. Thus the candidate entry satisfies the paired graph formula at `c`, establishing the existence half of functionality for every index below `α`.
<!--zh-->
现在可以把关系取值的递归图证明与内部有序对的标准同一视合并。由此，候选条目在 `c` 处满足成对图公式，也就对 `α` 以下每个索引建立了函数性所需的存在方向。
<!--ja-->
これで、関係値についての再帰グラフの証明と、内部順序対の標準的な同一視とを組み合わせられる。その結果、候補の項目は `c` において順序対グラフの論理式を満たし、`α` より下の各添字について関数性の存在側が得られる。
<!--/-->

```agda

        holds : (c : S) (c∈ : ⟨ fst c ∈ α ⟩) → ⟨ (entry c c∈ ∷ c ∷ []) ⊨ φ ⟩
        holds c c∈ = PairGraph-in zero (suc zero) (entry c c∈ ∷ c ∷ []) φ qφ
          (value c c∈) (prʟ-fst c (value c c∈)) (below c c∈ (entry c c∈))

```

<!--en-->
Functionality also requires uniqueness of the whole paired value. If another `k` satisfies the paired graph at `c`, reading that formula gives, under propositional truncation, a relation set `r`, an identification of the underlying set of `k` with the pair `(c,r)`, and a graph proof for `r`. Since equality in the constructible carrier is a proposition, this truncated information may be eliminated into the desired equality.
<!--zh-->
函数性还要求整个成对取值的唯一性。若另一个 `k` 在 `c` 处满足成对图，读出该公式便会在命题截断之下给出关系集 `r`、`k` 的底层集合与有序对 `(c,r)` 的同一视，以及 `r` 的图证明。可构造论域中的相等是命题，因此可以把这些截断资料消去到所需的相等中。
<!--ja-->
関数性には、順序対全体としての値の一意性も必要である。別の `k` が `c` において順序対グラフを満たすなら、その論理式を読むことで、命題的切り詰めの中に、関係集合 `r`、`k` の底の集合と順序対 `(c,r)` との同一視、そして `r` のグラフの証明が得られる。構成可能な台における等しさは命題なので、この切り詰められた情報を求める等しさへ消去できる。
<!--/-->

```agda
        only : (c : S) (c∈ : ⟨ fst c ∈ α ⟩) (k : S)
             → ⟨ (k ∷ c ∷ []) ⊨ φ ⟩ → k ≡ entry c c∈
        only c c∈ k h = rec₁ (isSetS k (entry c c∈)) read
          (PairGraph-out zero (suc zero) (k ∷ c ∷ []) φ qφ h)
          where
```

<!--en-->
The graph proof says that `r` realizes the relation class at `c`; independently, the induction hypothesis says the chosen value at `c` realizes that same class. Extensional uniqueness of realizing relation sets therefore identifies `r` with the chosen value. This is where uniqueness enters, after graph correctness has been established, rather than as an assumption about the lower table.
<!--zh-->
图证明说明 `r` 实现 `c` 处的关系类；另一方面，归纳假设说明在 `c` 处选定的取值也实现同一个类。因此，实现关系类的集合之外延唯一性把 `r` 与选定取值认同。唯一性是在图的正确性已经建立之后才进入论证的，并不是对下方表所作的假设。
<!--ja-->
グラフの証明は、`r` が `c` における関係クラスを実現することを述べる。一方、帰納法の仮定は、`c` で選ばれた値も同じクラスを実現することを述べる。したがって、実現関係集合の外延的な一意性により、`r` は選ばれた値と同一視される。一意性を用いるのはグラフの正しさを確立した後であり、下方の表に単値性を仮定しているのではない。
<!--/-->

```agda
          read : PairOf zero (suc zero) (k ∷ c ∷ []) φ qφ → k ≡ entry c c∈
          read (r , (q , hg)) = Σ≡Prop (λ x → snd (isL x))
            ( q
            ∙ cong (pr (fst c)) (cong fst (rel-unique (fst c) r (value c c∈)
                (graph-only zero (suc (suc zero)) (r ∷ k ∷ c ∷ []) hg (ordOf c c∈))
```

<!--en-->
Composing the given identification of `k` with `(c,r)`, the equality of the two relation sets, and the canonical projection path for the constructible ordered pair identifies the underlying sets of `k` and the candidate entry. Constructibility is a proposition, so this underlying equality lifts to an equality in the carrier and completes the uniqueness proof.
<!--zh-->
把已知的 `k` 与 `(c,r)` 的同一视、两个关系集的相等，以及可构造有序对的标准投影路径依次复合，便认同了 `k` 与候选条目的底层集合。可构造性是命题，所以这条底层相等可提升为论域中的相等，唯一性证明至此完成。
<!--ja-->
与えられた `k` と `(c,r)` との同一視、二つの関係集合の等しさ、そして構成可能な順序対の標準的な射影パスを順に合成すると、`k` と候補項目の底の集合が同一視される。構成可能性は命題なので、この底での等しさは台における等しさへ持ち上がり、一意性の証明が完了する。
<!--/-->

```agda
                (relOK c c∈)))
            ∙ sym (prʟ-fst c (value c c∈)) )

```

<!--en-->
For each `c ∈ α`, existence and uniqueness now describe a single point of the fiber consisting of a graph value together with its satisfaction proof. The unique-existence witness is propositionally truncated, but contractibility is itself a proposition; hence `mereFunct` converts that witness into the contractible fiber required by replacement without making any additional choice.
<!--zh-->
对每个 `c ∈ α`，刚才的存在性与唯一性在「图取值连同其满足证明」所成的纤维中确定唯一一点。这份唯一存在见证处在命题截断之下，但可缩性本身是命题；因此 `mereFunct` 无须作任何额外选择，就能把该见证转换成替换所要求的可缩纤维。
<!--ja-->
各 `c ∈ α` について、ここまでの存在性と一意性は、グラフの値とその充足証明からなるファイバーの一点を一意に定める。この一意存在の証人は命題的に切り詰められているが、可縮性そのものは命題である。したがって `mereFunct` は新たな選択を行わずに、この証人を置換公理が要求する可縮なファイバーへ変換する。
<!--/-->

```agda
        fc : (c : S) → ⟨ c ∈ˢ A ⟩
           → isContr (Σ[ k ∈ S ] ⟨ (k ∷ c ∷ []) ⊨ φ ⟩)
        fc c c∈ = mereFunct φ c ∣ entry c c∈ , (holds c c∈ , only c c∈) ∣₁

```

<!--en-->
Replacement may therefore collect the paired graph values over the internal domain `α`. Its conclusion is a contractible type of a constructible set equipped with the exact membership specification for that image. In particular, it gives a uniquely specified image set; it does not assert that the members of that set form a contractible type.
<!--zh-->
于是替换可以在内部定义域 `α` 上收集成对图的取值。其结论是一个可缩类型，其中的元素由一个可构造集合及该图像的精确成员关系规格组成。因此得到的是具有唯一规格的图像集，并不是说这个集合的成员构成可缩类型。
<!--ja-->
したがって置換公理は、内部の定義域 `α` 上で順序対グラフの値を集められる。その結論は、構成可能な集合と、その像についての正確な所属仕様とからなる可縮型である。つまり一意に指定された像集合が得られるのであって、その集合の要素が可縮型をなすという主張ではない。
<!--/-->

```agda
        rep : isContr (SetOf (λ z → ∃[ c ∶ S ] (c ∈ˢ A) ⊓ ((z ∷ c ∷ []) ⊨ φ)))
        rep = hasReplacementL A φ fc

```

<!--en-->
The table `H` is the constructible set at the center of this contractible replacement result. Its accompanying membership specification remains available and will now be used to prove that `H` records exactly the intended index-relation pairs.
<!--zh-->
表 `H` 取为这项可缩替换结果之中心所给出的可构造集合。与它同行的成员关系规格仍然可用，下面将据此证明 `H` 恰好记录预期的「索引与关系」有序对。
<!--ja-->
表 `H` は、この可縮な置換結果の中心が与える構成可能な集合である。それに伴う所属仕様も引き続き利用でき、`H` が意図した添字と関係との順序対だけを正確に記録することを次に証明する。
<!--/-->

```agda
        H : S
        H = rep .fst .fst

```

<!--en-->
The required table specification is an equality between two propositions: membership in `H` and being an index below `α` paired with a set realizing the relation there. It is obtained from two implications. The forward implication reads replacement membership, and the backward implication turns any such recorded pair back into a value of the replacement graph.
<!--zh-->
所需的表规格是两个命题之间的相等：一边是属于 `H`，另一边是「某个 `α` 以下的索引与一个实现该处关系的集合组成有序对」。这条相等由两个蕴含得到。正向读出替换的成员关系，反向则把任何这样的被记录有序对变回替换图的取值。
<!--ja-->
必要な表の仕様は二つの命題の等しさである。一方は `H` への所属であり、他方は、`α` より下の添字と、そこでの関係を実現する集合との順序対であることである。この等しさは二つの含意から得る。順方向では置換による所属を読み、逆方向ではそのような記録順序対を置換グラフの値へ戻す。
<!--/-->

```agda
        spec : IsTable α H
        spec z = ⇔toPath toRec fromRec
          where
          toRec : ⟨ fst z ∈ fst H ⟩ → ⟨ Recorded α (fst z) ⟩
          toRec hz = rec₁ squash₁
```

<!--en-->
In the forward direction, replacement membership merely supplies an index `c` below `α` and a proof that `z` satisfies the paired graph there. The uniqueness result identifies `z` with the canonical entry at `c`; its relation component is already known to realize the class at `c`. These facts produce the required recorded-pair witness, still under propositional truncation.
<!--zh-->
在正向中，替换的成员关系只在命题截断之下给出 `α` 以下的索引 `c`，以及 `z` 在该处满足成对图的证明。先前的唯一性结果把 `z` 与 `c` 处的标准条目认同，而该条目的关系分量已知实现 `c` 处的类。这些事实给出所需的被记录有序对见证，并继续保留命题截断边界。
<!--ja-->
順方向では、置換による所属から、`α` より下の添字 `c` と、`z` がそこで順序対グラフを満たすという証明が、命題的切り詰めの中で得られる。先ほどの一意性により `z` は `c` における標準的な項目と同一視され、その関係成分はすでに `c` でのクラスを実現すると分かっている。これらから必要な記録順序対の証人が得られ、命題的切り詰めの境界も保たれる。
<!--/-->

```agda
            (λ { (c , (c∈ , hp)) → ∣ c , (c∈ , ∣ value c c∈
               , ( cong fst (only c c∈ z hp) ∙ prʟ-fst c (value c c∈)
                 , relOK c c∈ ) ∣₁) ∣₁ })
            (subst ⟨_⟩ (rep .fst .snd z) hz)

```

<!--en-->
For the reverse implication, a recorded-pair witness may contain any relation set `r` realizing the class at `c`, not necessarily the recursive value chosen above. To reuse the paired graph proof already established for the canonical entry, the argument first eliminates the truncated witness into the propositional satisfaction goal and then transports that proof along an equality between the two entries.
<!--zh-->
在反向蕴含中，被记录有序对的见证可以包含任意实现 `c` 处关系类的集合 `r`，未必是上文递归选定的取值。为了复用已经为标准条目建立的成对图证明，论证先把截断见证消去到命题性的满足目标中，再沿两个条目之间的相等搬运该证明。
<!--ja-->
逆向きの含意では、記録順序対の証人に含まれる関係集合 `r` は、`c` における関係クラスを実現する任意の集合でよく、先に再帰的に選んだ値とは限らない。標準的な項目についてすでに得た順序対グラフの証明を再利用するため、まず切り詰められた証人を命題である充足の目標へ消去し、次に二つの項目の等しさに沿ってその証明を移す。
<!--/-->

```agda
          fromRec : ⟨ Recorded α (fst z) ⟩ → ⟨ fst z ∈ fst H ⟩
          fromRec hz = subst ⟨_⟩ (sym (rep .fst .snd z)) (map₁
            (λ { (c , (c∈ , hr)) → c , (c∈ , rec₁ (snd ((z ∷ c ∷ []) ⊨ φ))
              (λ { (r , (q , hs)) → subst (λ t → ⟨ (t ∷ c ∷ []) ⊨ φ ⟩)
                (sym (Σ≡Prop (λ x → snd (isL x))
```

<!--en-->
That transport path starts with the recorded equality for `z`, replaces `r` by the canonical relation value using extensional uniqueness, and ends with the canonical projection path for the internal ordered pair. Because constructibility proofs are propositional, equality of the underlying sets determines equality in the carrier. The transported graph proof then places `z` in the replacement image and closes the reverse implication.
<!--zh-->
这条搬运路径始于 `z` 随被记录见证给出的相等，经由外延唯一性把 `r` 换成标准关系取值，最后接上内部有序对的标准投影路径。由于可构造性证明是命题，底层集合的相等即可确定论域中的相等。沿此路径搬运后的图证明把 `z` 放入替换图像，从而完成反向蕴含。
<!--ja-->
この移送パスは、記録された証人に伴う `z` の等しさから始まり、外延的な一意性によって `r` を標準的な関係値に置き換え、内部順序対の標準的な射影パスで終わる。構成可能性の証明は命題なので、底の集合の等しさから台における等しさが定まる。このパスに沿って移されたグラフの証明により `z` は置換の像に入り、逆向きの含意が完了する。
<!--/-->

```agda
                  (q ∙ cong (pr (fst c)) (cong fst
                     (rel-unique (fst c) r (value c c∈) hs (relOK c c∈)))
                     ∙ sym (prʟ-fst c (value c c∈)))))
                (holds c c∈) }) hr) }) hz)

```

<!--en-->
The exact table specification now yields correctness of all values recorded by `H` below `α`. If the pair `(c,r)` belongs to `H` with `c ∈ α`, reading the specification shows that `r` realizes the relation class at `c`. No new induction or uniqueness argument is needed at this point.
<!--zh-->
现在，表的精确规格给出 `H` 在 `α` 以下所记录全部取值的正确性。若 `(c,r)` 属于 `H` 且 `c ∈ α`，读出该规格便知 `r` 实现 `c` 处的关系类。此处无须再作归纳或唯一性论证。
<!--ja-->
ここで表の正確な仕様から、`H` が `α` より下で記録するすべての値の正しさが得られる。`c ∈ α` で順序対 `(c,r)` が `H` に属するなら、その仕様を読むことで `r` が `c` における関係クラスを実現すると分かる。この段階では新たな帰納法や一意性の議論は不要である。
<!--/-->

```agda
        tvals : Values H α
        tvals = table-out α oα H spec .snd

```

<!--en-->
Completeness is obtained pointwise. For each `c ∈ α`, the recursive value at `c` is known to realize the required class, so the table specification inserts its pair into `H`. The resulting existential statement is propositionally truncated: it certifies that an entry exists at every index without making a distinguished entry part of the completeness statement.
<!--zh-->
完备性逐点取得。对每个 `c ∈ α`，`c` 处的递归取值已知实现所需的类，因此表规格把它与 `c` 组成的有序对放入 `H`。所得存在陈述经过命题截断：它证明每个索引处都有条目，却不把某个指定条目纳入完备性陈述。
<!--ja-->
完全性は各点ごとに得られる。各 `c ∈ α` について、`c` における再帰値が必要なクラスを実現すると分かっているので、表の仕様は `c` とその値との順序対を `H` に入れる。得られる存在命題は命題的に切り詰められており、各添字に項目があることを保証するが、特定の項目を完全性の主張に含めるものではない。
<!--/-->

```agda
        tents : Entries H α
        tents c c∈ = ∣ value c c∈
                    , table-in α oα H spec c (value c c∈) c∈ (relOK c c∈) ∣₁

```

<!--en-->
The table has now supplied the value correctness and completeness needed to read the constant form of the step condition at `α`. Separation applies that condition inside the previously constructed common bound. It returns the uniquely specified constructible subset whose members are exactly the bounded elements satisfying the condition; this subset, rather than the bound itself, is the candidate relation at `α`.
<!--zh-->
这张表现已给出在 `α` 处读取常元形式步进条件所需的取值正确性与完备性。分离公理在先前构造的共同界内应用该条件，得到具有唯一规格的可构造子集，其成员恰为界中满足该条件的元素。作为 `α` 处候选关系的是这个子集，而不是共同界本身。
<!--ja-->
この表から、`α` におけるステップ条件の定数形を読むために必要な、値の正しさと完全性が得られた。分出公理は、先に構成した共通の上界の中でその条件を適用する。その結果、上界に属して条件を満たす要素だけを正確にもつ、仕様によって一意な構成可能部分集合が得られる。`α` における関係の候補は共通の上界そのものではなく、この部分集合である。
<!--/-->

```agda
        sep : isContr (SetOf (λ x → (x ∈ˢ bound α oα .fst)
                                  ⊓ ((x ∷ []) ⊨ Cond₀ A H)))
        sep = hasSeparationL (bound α oα .fst) (Cond₀ A H)

```

<!--en-->
To prove that the separated set realizes the intended class, first take one of its members. The separation specification yields both membership in the common bound and satisfaction of the constant condition; only the second component is needed in this direction. Adequacy of the condition converts that satisfaction into `Related α`, giving the membership-to-relation implication.
<!--zh-->
为证明分离所得集合实现预期的类，先取它的一个成员。分离规格同时给出该元素属于共同界并满足常元条件；这个方向只需第二分量。条件的充分性把该满足证明转换成 `Related α`，从而得到从成员关系到关系类的蕴含。
<!--ja-->
分出された集合が意図したクラスを実現することを示すため、まずその要素を一つ取る。分出の仕様から、共通の上界への所属と定数条件の充足がともに得られるが、この向きで必要なのは後者だけである。条件の妥当性により、その充足は `Related α` へ変換され、所属から関係クラスへの含意が得られる。
<!--/-->

```agda
        rspec : IsRel α (sep .fst .fst)
        rspec z =
            (λ hz → subst ⟨_⟩ (cond₀-spec A H oα tvals tents z)
                      (subst ⟨_⟩ (sep .fst .snd z) hz .snd))
          , (λ hz → subst ⟨_⟩ (sym (sep .fst .snd z))
```

<!--en-->
Conversely, an element satisfying `Related α` lies in the common bound by its defining confinement property. Adequacy in the reverse direction turns the same relation fact into satisfaction of the constant condition. These two components meet the separation specification and place the element in the separated set, completing the exact realization in both directions.
<!--zh-->
反过来，满足 `Related α` 的元素由共同界的限制性质可知属于该界。充分性的反向又把同一关系事实转换为对常元条件的满足。这两个分量共同符合分离规格，因而把该元素放入分离所得集合，完成双向的精确实现。
<!--ja-->
逆に、`Related α` を満たす要素は、共通の上界がもつ閉じ込めの性質により、その上界に属する。また、妥当性の逆方向は同じ関係の事実を定数条件の充足へ変換する。この二成分が分出の仕様を満たすので、その要素は分出された集合に入り、両方向の正確な実現が完成する。
<!--/-->

```agda
                      ( bound α oα .snd z hz
                      , subst ⟨_⟩ (sym (cond₀-spec A H oα tvals tents z)) hz ))

```

<!--en-->
For a layer index `α` equipped with both constructibility and ordinalness, the recursive bundle contains the lower table and the relation set just obtained by separation. The relation `relL` selects the latter. Its scope is therefore the constructible ordinal indices used in `L`, not arbitrary ordinals without a constructibility witness.
<!--zh-->
对同时配有可构造性与序数性证明的层索引 `α`，递归包包含下方的表以及刚由分离得到的关系集。关系 `relL` 选取后者。因此，它的适用范围是 `L` 中所用的可构造序数层索引，而不是没有可构造性见证的任意序数。
<!--ja-->
構成可能性と順序数性の証明をともに備えた段階添字 `α` について、再帰的な束は下方の表と、いま分出によって得た関係集合とを含む。関係 `relL` は後者を選ぶ。したがって、その適用範囲は `L` で用いる構成可能な順序数段階の添字であり、構成可能性の証人を伴わない任意の順序数ではない。
<!--/-->

```agda
  relL : (α : V ℓ) → ⟨ isL α ⟩ → IsOrd α → S
  relL α hα oα = tableAt α hα oα .snd .fst

```

<!--en-->
The accompanying specification comes from the same bundle. It says exactly that membership in `relL` agrees with the class `Related α`: every member represents a related pair, and every related pair belongs. Later arguments can therefore reason from this equivalence without reopening the replacement and separation construction.
<!--zh-->
同行的规格来自同一个包。它精确断言：属于 `relL` 与满足类 `Related α` 相一致；每个成员都表示一个被关联的有序对，而每个被关联的有序对都属于其中。因此，后续论证可以直接使用这条等价，无须重新展开替换与分离的构造。
<!--ja-->
それに伴う仕様も同じ束から得られる。この仕様は、`relL` への所属がクラス `Related α` と正確に一致すること、すなわち各要素が関係づけられた順序対を表し、関係づけられた各順序対がそこに属することを述べる。したがって後の議論では、置換と分出の構成を開き直さず、この同値を直接用いられる。
<!--/-->

```agda
  relL-spec : (α : V ℓ) (hα : ⟨ isL α ⟩) (oα : IsOrd α) → IsRel α (relL α hα oα)
  relL-spec α hα oα = tableAt α hα oα .snd .snd .snd
```

<!--en-->
## The members are the pairs the order relates
<!--zh-->
## 成员就是那个序所关联的诸对
<!--ja-->
## 要素は順序が関係づける順序対である
<!--/-->

<!--en-->
For two members `a` and `b` of `Lset α`, the filling direction specializes the general realization lemma to `relL`. A host-level comparison by the already constructed strict well-order `orderAt α` therefore places the encoded ordered pair of their underlying sets in `relL`.
<!--zh-->
对 `Lset α` 的两个成员 `a` 与 `b`，填充方向把一般的实现引理专用于 `relL`。因此，已经构造好的严格良序 `orderAt α` 中的一条宿主层比较，会把二者底层集合组成的编码有序对放入 `relL`。
<!--ja-->
`Lset α` の二要素 `a` と `b` について、埋める向きは一般の実現補題を `relL` に特殊化する。したがって、すでに構成されている狭義整列順序 `orderAt α` によるホスト側の比較から、二つの底の集合を符号化した順序対が `relL` に属することが従う。
<!--/-->

```agda
  module _ (α : V ℓ) (hα : ⟨ isL α ⟩) (oα : IsOrd α) where
    relL-fill : (a b : Mem (Lset α)) → relOf (orderAt α oα) a b
              → ⟨ pr (fst a) (fst b) ∈ fst (relL α hα oα) ⟩
    relL-fill = rel-fill α oα (relL α hα oα) (relL-spec α hα oα)

```

<!--en-->
The reading direction gives the converse for the same two layer members: membership of their encoded pair in `relL` recovers the host-level comparison in `orderAt α`. Together the two directions give a pointwise representation of the relation graph used by later minimality arguments. They neither construct a new comparison of names nor assert in the object language that this graph is a well-order.
<!--zh-->
读取方向对同一对层成员给出逆命题：二者编码有序对属于 `relL`，便可恢复 `orderAt α` 中的宿主层比较。两个方向合起来逐点表示这张关系图，供后续的最小性论证使用。它们既不构造新的名字比较，也不在对象语言中断言这张图是良序。
<!--ja-->
読む向きは、同じ二つの段階要素について逆を与える。二要素の符号化順序対が `relL` に属することから、`orderAt α` におけるホスト側の比較が復元される。二方向を合わせると、後の最小性の議論で用いる関係グラフが各要素対ごとに表現される。ここでは新たな名前の比較を構成せず、このグラフが整列順序であるという対象言語の主張も行わない。
<!--/-->

```agda
    relL-rep : (a b : Mem (Lset α))
             → ⟨ pr (fst a) (fst b) ∈ fst (relL α hα oα) ⟩
             → relOf (orderAt α oα) a b
    relL-rep = rel-rep α oα (relL α hα oα) (relL-spec α hα oα)
```

<!--en-->
## Recap

At a constructible ordinal index `α`, the host type theory already has the strict well-order `orderAt α oα` on the members of `Lset α`. `Ordering` turns its comparison into a proposition-valued predicate by propositional truncation, and `Related` packages the related endpoint pairs as a host-defined class. Trichotomy allows `strict` to recover the comparison only at specified endpoints; `IsRel`, `relL-fill`, and `relL-rep` then express the exact pointwise correspondence between that comparison and membership in a realizing set.

The realizing set is obtained indirectly. An approximation records merely existing values below its domain, and membership induction proves that every recorded value realizes the class for its own argument without assuming functionality. Extensional uniqueness identifies competing realizers when the paired graph fiber is compared. `mereFunct` converts the resulting truncated unique existence into contractibility, replacement collects the indexed entries below `α`, and separation cuts the relation at `α` from a common containing set. The recursive bundle carries the completed lower table and the current relation together; the recursion does not require this bundle to be a proposition.

The construction remains relative to the two adequate forms of the object-language step supplied to `Described`. Later chapters provide the concrete description and discharge that parameter. Here `relL` is available only when `α` comes with both `isL` and `IsOrd` evidence. It represents the graph of the already constructed order; it neither completes a new comparison of names nor proves in the object language that the graph is a well-order.
<!--zh-->
## 小结

在可构造序数层索引 `α` 处，宿主类型论已经给出 `Lset α` 的成员上的严格良序 `orderAt α oα`。`Ordering` 通过命题截断把它的比较化为命题值谓词，`Related` 再把被关联端点的有序对组织成宿主层定义的类。三岐性只允许 `strict` 在端点已经指定时恢复比较；`IsRel`、`relL-fill` 与 `relL-rep` 随后逐点给出这项比较与实现集合之成员关系的精确对应。

实现集合通过间接方式得到。逼近只在其定义域以下记录命题截断意义下存在的取值，而沿成员关系的归纳在不假设单值性的情况下，证明每个已记录取值都实现其自身实参处的类。比较成对图的纤维时，实现集合的外延唯一性才认同相互竞争的取值。`mereFunct` 把所得命题截断下的唯一存在转成可缩性，替换收集 `α` 以下的带索引条目，分离再从共同包含集中切出 `α` 处的关系。递归包同时携带完成的下方表与当前关系，而递归并不要求这个包是命题。

整个构造仍以交给 `Described` 的两种充分对象语言步进形式为参数，后续章节才给出具体描述并解除这个参数。这里的 `relL` 只适用于同时配有 `isL` 与 `IsOrd` 证据的 `α`。它表示已有序的关系图；它既不完成新的名字比较，也不在对象语言中证明这张图是良序。
<!--ja-->
## まとめ

構成可能な順序数の段階の添字 `α` では、ホスト型理論がすでに `Lset α` の要素上の狭義整列順序 `orderAt α oα` を与えている。`Ordering` はその比較に命題的切り詰めを施して命題値の述語にし、`Related` は関係する端点の順序対をホスト側で定義されたクラスとしてまとめる。三分性によって `strict` が比較を復元できるのは、端点が指定されている場合だけである。その後、`IsRel`、`relL-fill`、`relL-rep` が、この比較と実現集合への所属との正確な点ごとの対応を与える。

実現集合は間接的に得られる。近似はその定義域より下の値が単に存在することだけを記録し、所属に沿う帰納は単値性を仮定せず、記録された各値が自身の引数でのクラスを実現することを示す。順序対グラフの繊維を比較するときに初めて、実現集合の外延的な一意性が競合する値を同一視する。`mereFunct` は得られた命題的切り詰めのもとの一意存在を可縮性へ変え、置換公理が `α` より下の添字つき項目を集め、分出公理が共通の包含集合から `α` での関係を切り出す。再帰的な束は完成した下方の表と現在の関係をともに運ぶが、再帰はこの束が命題であることを要求しない。

構成全体は、`Described` に与えられる二つの妥当な対象言語のステップ形式に相対したままである。後の章が具体的な記述を与え、このパラメータを解消する。ここで `relL` を利用できるのは、`α` に `isL` と `IsOrd` の証拠がともに備わる場合だけである。これは既存の順序の関係グラフを表現するものであり、新たな名前の比較を完成させることも、そのグラフが整列順序であると対象言語で証明することもない。
<!--/-->

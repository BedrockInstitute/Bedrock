<!--en-->
# Coded injections

Later cardinal arguments repeatedly move between two representations of an injection: a graph that a formula can quantify over, and an actual function between the small member types of sets. The gap between them is filled in three layers. The object language first needs a formula saying that the graph is injective, the mirror of the single-valuedness clause already available. Then, assuming single-valuedness and an exact domain, the graph can be read as a genuine function whose values remain elements of the constructible model. Finally that function transfers to the canonical small presentations of a stated domain and range. This chapter adds the injectivity formula and carries out both readback layers used by the Cantor-Bernstein and GCH constructions.
<!--zh-->
# 编码单射

后续的基数论证反复在单射的两种表示之间往返：一种是公式可以量化的图，另一种是集合的小成员类型之间的实际函数。两者之间的缝隙分三层填补。对象语言首先需要一条表达图是单射的公式，它是已有单值性条款的对偶。其次，在单值性与恰当定义域的假设下，图可以读成一个真正的函数，取值仍是可构造模型的元素。最后，该函数可转移到指定定义域与值域的典范小呈现上。本章补上单射性公式，并完成 Cantor-Bernstein 与 GCH 构造所用的两层读回。
<!--ja-->
# 符号化された単射

後の基数論では、対象言語が量化できるグラフと、集合の小さな要素型の間の実際の単射という二つの表現を往復する。この溝は三層で埋める。まず対象言語には、グラフが単射であることを言う論理式、すでにある一価性の条項の鏡像が必要になる。次に、一価性とちょうどの定義域を仮定すれば、グラフは値が構成可能モデルの要素にとどまる本物の関数として読める。最後にその関数は、指定された定義域と値域の標準的な小さな提示へ移る。本章は単射性の論理式を加え、Cantor-Bernstein と GCH の構成が使う二段階の読み戻しを実行する。
<!--/-->

<!--en-->
The construction is valid constructively. Although the ambient development carries `LEM (ℓ-suc ℓ)`, the proofs below never invoke it: existence of a graph value is truncated, but single-valuedness makes the entire image fiber a proposition, so truncation elimination recovers its unique inhabitant without a choice principle.
<!--zh-->
这一构造本身是构造性的。周遭论证虽带有 `LEM (ℓ-suc ℓ)`，下面的证明却不调用它：图的取值只以截断存在给出，但单值性使整个像原像成为命题，因此可以消去截断并取得其唯一元素，而无须选择原理。
<!--ja-->
この構成自体は構成的です。周囲の議論は `LEM (ℓ-suc ℓ)` を仮定していますが、以下の証明はそれを使いません。グラフの値の存在は切り詰められていますが、一価性により像のファイバー全体が命題になるため、選択原理なしに切り詰めを消去してその一意な要素を得られます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.Injection {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

<!--en-->
Let `S` be the carrier of the constructible model. An element of `S` consists of an ambient set in `V ℓ` together with evidence that it is constructible. Consequently graph assertions are statements about the first projections. The formulas for application, single-valuedness, and exact domain connect internal satisfaction with precisely these projected graph facts.
<!--zh-->
设 `S` 为可构造模型的载体。`S` 的元素由 `V ℓ` 中的周遭集合及其可构造性证明组成，因此图的断言都针对第一投影陈述。表示图取值、单值性与恰当定义域的公式，恰好把内部满足关系与这些投影后的图事实联系起来。
<!--ja-->
`S` を構成可能モデルの台とします。`S` の要素は `V ℓ` の周囲の集合と、その構成可能性の証明からなるため、グラフについての主張は第一射影について述べられます。適用、一価性、正確な定義域を表す論理式は、内部の充足をこれらの射影されたグラフの事実と結び付けます。
<!--/-->

```agda

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _≐_; _⇒̇_; ∀̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
```

<!--en-->
The second readback layer needs the canonical presentation machinery: a set presented by an index type and an indexing map, with `member` turning an index into an explicit membership proof and `fiber` doing the converse by returning an actual index, not a truncated one. `Σ≡Prop` will reduce equality of dependent pairs to equality of first components when the second components are propositions, which is exactly how the fiber of images and the pairs of the model carrier are handled.
<!--zh-->
第二层读回需要典范呈现的工具：集合由索引类型与索引映射呈现，`member` 把索引变成显式的隶属证明，`fiber` 做相反的事，返回一个实际的索引而非截断的存在。`Σ≡Prop` 会在第二分量是命题时把依赖对的相等化归为第一分量的相等，像的原像与模型载体的对正是这样处理的。
<!--ja-->
第二の読み戻しには標準的な提示の道具が必要です。集合はインデックス型とインデックス付けの写しで提示され、`member` はインデックスを明示的な所属証明に変え、`fiber` は逆に実際のインデックスを返します。切り詰められた存在ではなくです。`Σ≡Prop` は第二成分が命題のとき、依存対の等しさを第一成分の等しさへ帰着させます。像のファイバーも模型の台の対もこの仕方で扱われます。
<!--/-->

```agda
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( appAt; appAt-adequate; svAt; svAt-out; domAt; domAt-in )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
```

<!--en-->
Truth values here are propositions with their proofs of propositionhood, and the truth algebra packages the logical connectives the satisfaction relation uses. The satisfaction judgment `_⊨_` is then stated for the constructible structure `𝒮ʟ`, so a judgment such as `γ ⊨ svAt zero` is a claim about the projected sets via the adequacy identifications, not about bare satisfaction in an ambient structure.
<!--zh-->
这里的真值是带着「其为命题」证明的命题，真值代数把满足关系用到的逻辑连接词打包起来。满足判断 `_⊨_` 是对可构造结构 `𝒮ʟ` 陈述的，因此像 `γ ⊨ svAt zero` 这样的判断经充分性等同化后谈的是投影后的集合，而非对某个周遭结构的裸满足。
<!--ja-->
ここでの真理値は、命題であることの証明を添えた命題であり、真理値代数が充足関係の使う論理結合子をまとめます。充足の判断 `_⊨_` は構成可能な構造 `𝒮ʟ` に対して述べられるので、`γ ⊨ svAt zero` のような判断は、妥当性の同一視を通して射影された集合についての主張になります。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )
```

<!--en-->
Bounded absoluteness relates satisfaction in the constructible model to satisfaction after projecting an assignment with `fst`. This bridge is used only where an adequacy theorem is applied. It does not turn `Extract.toFun` into an injection by itself: injectivity enters later as the separate hypothesis `ij`.
<!--zh-->
有界绝对性把可构造模型中的满足与赋值经 `fst` 投影后的满足联系起来。这座桥只在应用充分性定理时使用，并不会自行使 `Extract.toFun` 成为单射；单射性稍后以独立假设 `ij` 加入。
<!--ja-->
有界絶対性は、構成可能モデルでの充足を、割り当てを `fst` で射影した後の充足と結び付けます。この橋は妥当性定理を適用する箇所で用いられますが、それだけで `Extract.toFun` が単射になるわけではありません。単射性は後で独立な仮定 `ij` として加わります。
<!--/-->

```agda

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## Injectivity in the object language

A single-valued graph fixes one input and compares outputs: if two entries share the same first component, their second components agree. Injectivity is the mirror image: it fixes one output and compares inputs. Concretely, if both `(x, y)` and `(x', y)` belong to the graph, then the first components of `x` and `x'` must be equal. Stating this as a formula of the object language is what lets a cardinal argument quantify over injective graphs inside the model, so this section defines `injAt` and proves that, under the adequacy identifications for application, the formula holds exactly when the projected graph has the injectivity property.
<!--zh-->
## 对象语言中的单射性

单值性的图固定一个输入、比较输出：若两条目有相同的第一分量，其第二分量一致。单射性是它的镜像：固定一个输出、比较输入。具体地，若 `(x, y)` 与 `(x', y)` 都属于图，则 `x` 与 `x'` 的第一分量必须相等。把它写成对象语言的公式，基数论证才能在模型内部对单射图作量化。本节定义 `injAt`，并证明：在应用的充分性等同下，该公式成立当且仅当投影后的图具有单射性质。
<!--ja-->
## 対象言語における単射性

妥当性の観点では、## 対象言語における単射性

一価的なグラフは引数を固定して値を比較します。同じ第一成分を持つ二つの項目の第二成分は一致する、というものです。単射性はその鏡像で、値を固定して引数を比較します。具体的には、`(x, y)` と `(x', y)` がともにグラフに属するなら、`x` と `x'` の第一成分は等しくなければなりません。これを対象言語の論理式として述べることで、基数論はモデルの内部で単射なグラフを量化できるようになります。
<!--/-->

<!--en-->
The formula binds the assignment `x′ ∷ x ∷ y ∷ γ`: slot 0 is `x′`, slot 1 is `x`, and slot 2 is `y`, while the old graph slot `f` becomes `f + 3`. Its two premises say that `(x,y)` and `(x′,y)` belong to that graph, and its conclusion equates `x` and `x′`. Thus it fixes the output and compares the inputs, exactly the mirror of single-valuedness.
<!--zh-->
公式绑定赋值 `x′ ∷ x ∷ y ∷ γ`：槽位 0 是 `x′`，槽位 1 是 `x`，槽位 2 是 `y`，原来的图槽位 `f` 则变为 `f + 3`。两个前提分别说 `(x,y)` 与 `(x′,y)` 属于该图，结论把 `x` 与 `x′` 等同。因此它固定输出并比较输入，恰是单值性的对偶。
<!--ja-->
論理式は割り当て `x′ ∷ x ∷ y ∷ γ` を束縛します。スロット 0 は `x′`、1 は `x`、2 は `y` で、もとのグラフのスロット `f` は `f + 3` になります。二つの前提は `(x,y)` と `(x′,y)` がそのグラフに属すことを述べ、結論は `x` と `x′` を等置します。したがって出力を固定して入力を比較し、一価性とちょうど対をなします。
<!--/-->

```agda
injAt : ∀ {n} → Fin n → Formula S n
injAt f = ∀̇ (∀̇ (∀̇ (
      appAt (suc (suc (suc f))) (suc zero) (suc (suc zero))
  ⇒̇ (appAt (suc (suc (suc f))) zero (suc (suc zero))
  ⇒̇ (var (suc zero) ≐ var zero)))))
```

<!--en-->
For the readback, fix a variable index `f` and an environment `γ` of model elements. `Holds₀ x y` is the projected fact that the ordered pair of the underlying sets of `x` and `y` belongs to the underlying graph, the graph being the entry that variable `f` selects from `γ`. Both directions below compare a satisfaction judgment of an application clause with this `Holds₀`, so the adequacy paths are the pivot of the whole argument.
<!--zh-->
读回时固定变元索引 `f` 与模型元素组成的赋值 `γ`。`Holds₀ x y` 是投影后的事实：`x` 与 `y` 的底层集合组成的有序对属于底层图，即变元 `f` 在 `γ` 中选出的那一项。下面的两个方向都是把某条应用条款的满足判断与这个 `Holds₀` 相比较，充分性路径是整个论证的枢纽。
<!--ja-->
読み戻しでは変数の添字 `f` と模型要素からなる割り当て `γ` を固定します。`Holds₀ x y` は射影された事実で、`x` と `y` の底の集合の順序対が底のグラフ、すなわち変数 `f` が `γ` から選ぶ項目に属すということです。以下の両方向は、適用の条項の充足の判断をこの `Holds₀` と比べるもので、妥当性のパスが議論の要になります。
<!--/-->

```agda

module _ {n : ℕ} (f : Fin n) (γ : S ^ n) where
  private
    Holds₀ : S → S → Type (ℓ-suc ℓ)
    Holds₀ x y = ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩

    at₁ : (y x x' : S)
```

<!--en-->
The path `at₁` records the adequacy of the first application clause in the extended environment `x' ∷ x ∷ y ∷ γ`: satisfaction there is identified with the projected membership of the pair `(x, y)` in the graph. The identification is an equality of propositions, given by `appAt-adequate` at the stated variable indices, so it can be transported along in either direction.
<!--zh-->
路径 `at₁` 记录第一条应用条款在扩张赋值 `x' ∷ x ∷ y ∷ γ` 处的充分性：那里的满足被等同于对 `(x, y)` 属于图的投影事实。这一等同是命题之间的相等，由 `appAt-adequate` 在所给变元索引处给出，因此可以向两个方向运输。
<!--ja-->
パス `at₁` は、拡張された割り当て `x' ∷ x ∷ y ∷ γ` での最初の適用条項の妥当性を記録します。そこでの充足は、対 `(x, y)` のグラフへの所属という射影された事実と同一視されます。この同一視は命題どうしの等しさであり、所定の変数の添字での `appAt-adequate` によって与えられるので、どちらの方向へも輸送できます。
<!--/-->

```agda
        → ((x' ∷ x ∷ y ∷ γ) ⊨ appAt (suc (suc (suc f))) (suc zero) (suc (suc zero)))
        ≡ (pr (fst x) (fst y) ∈ fst (lookup f γ))
    at₁ y x x' = appAt-adequate (suc (suc (suc f))) (suc zero) (suc (suc zero))
                   (x' ∷ x ∷ y ∷ γ)

    at₂ : (y x x' : S)
```

<!--en-->
The path `at₂` is the same statement for the other clause: satisfaction of the application at variables `0` and `2` equals the projected membership of `(x', y)`. The two paths differ only in which first component is fed into the pair code, which is precisely the asymmetry that injectivity exploits.
<!--zh-->
路径 `at₂` 是另一条条款的同样陈述：变元 `0` 与 `2` 处的应用的满足等同于 `(x', y)` 属于图的投影事实。两条路径只在对码中输入哪个第一分量上不同，而这正是单射性所利用的不对称。
<!--ja-->
パス `at₂` はもう一つの条項についての同じ主張です。変数 `0` と `2` での適用の充足は、対 `(x', y)` のグラフへの所属という射影された事実と等しくなります。二つのパスの違いは、対の符号にどちらの第一成分を入れるかだけで、これこそ単射性が利用する非対称です。
<!--/-->

```agda
        → ((x' ∷ x ∷ y ∷ γ) ⊨ appAt (suc (suc (suc f))) zero (suc (suc zero)))
        ≡ (pr (fst x') (fst y) ∈ fst (lookup f γ))
    at₂ y x x' = appAt-adequate (suc (suc (suc f))) zero (suc (suc zero))
                   (x' ∷ x ∷ y ∷ γ)

  injAt-out : ⟨ γ ⊨ injAt f ⟩
```

<!--en-->
The outward direction `injAt-out` starts from a proof that the formula holds at `γ` and two membership facts `Holds₀ x y` and `Holds₀ x' y`. Instantiating the three quantifiers yields a satisfaction proof of the implication body at the extended environment; the membership facts are then transported along the reverses of `at₁` and `at₂`, turning them into satisfaction proofs of the two antecedent clauses. The final `fst x ≡ fst x'` is read off inside the model's equality.
<!--zh-->
向外的方向 `injAt-out` 从公式在 `γ` 处成立的证明与两个隶属事实 `Holds₀ x y`、`Holds₀ x' y` 出发。把三个量词实例化，得到含取式体在扩张赋值处的满足证明；再把隶属事实沿 `at₁`、`at₂` 的反向运输，变成两条前件条款的满足证明。最后的 `fst x ≡ fst x'` 在模型的相等中读出。
<!--ja-->
外向きの `injAt-out` は、論理式が `γ` で成り立つ証明と二つの所属の事実 `Holds₀ x y`、`Holds₀ x' y` から出発します。三つの量化子を具体化すると、拡張された割り当てでの含意の本体の充足証明が得られ、所属の事実を `at₁` と `at₂` の逆向きに輸送して、二つの前件の条項の充足証明に変えます。最後の `fst x ≡ fst x'` はモデルの等しさの中で読み取ります。
<!--/-->

```agda
            → (y x x' : S) → Holds₀ x y → Holds₀ x' y → fst x ≡ fst x'
  injAt-out h y x x' p q = h y x x'
    (subst ⟨_⟩ (sym (at₁ y x x')) p) (subst ⟨_⟩ (sym (at₂ y x x')) q)

  injAt-in : ((y x x' : S) → Holds₀ x y → Holds₀ x' y → fst x ≡ fst x')
           → ⟨ γ ⊨ injAt f ⟩
```

<!--en-->
The inward direction `injAt-in` runs the same transports forward: given the projected injectivity property as a hypothesis on `Holds₀`, it transports the two membership facts along `at₁` and `at₂` themselves to obtain satisfaction of the two antecedents, and the hypothesis then produces the equality the formula's conclusion asks for. Together the two directions say the formula is adequate for injectivity, not stronger and not weaker.
<!--zh-->
向内的方向 `injAt-in` 沿同样的路径正向运输：把投影的单射性质作为关于 `Holds₀` 的假设，沿 `at₁`、`at₂` 本身运输两个隶属事实，得到两条前件的满足，假设随后给出公式结论所需的等式。两个方向合起来说明：该公式对单射性是充分的，既不强也不弱。
<!--ja-->
内向きの `injAt-in` は同じ輸送を順方向に行います。`Holds₀` についての射影された単射性を仮定として与えると、二つの所属の事実を `at₁` と `at₂` そのものに沿って輸送して二つの前件の充足を得、仮定が論理式の結論の求める等しさを出します。二つの方向を合わせて、この論理式が単射性に対して過不足なく妥当であることが分かります。
<!--/-->

```agda
  injAt-in h y x x' p q = h y x x'
    (subst ⟨_⟩ (at₁ y x x') p) (subst ⟨_⟩ (at₂ y x x') q)
```

<!--en-->
## Extracting an injection into the model

Assuming a graph is single-valued and has an exact domain, every element of the domain has some image in the graph, but only a merely existing one: domain membership yields a propositional truncation, not a chosen witness. Single-valuedness upgrades the situation. It shows that for a fixed input, the type of pairs consisting of an output and a proof that the pair belongs to the graph is a proposition, and a truncated value can always be eliminated into a proposition. Thus the graph yields a genuine function into the model. Only after the additional injectivity hypothesis is supplied does `toFun-inj` show that this function is injective. This first readback layer keeps values as elements of the carrier, the form used when later proofs still reason about the coded graph.
<!--zh-->
## 提取一个取值于模型的单射

假设图是单值的且有恰当定义域，定义域的每个元素在图中都有某个像，但那只是仅仅存在的像：定义域隶属给出的是命题截断，而非选定的见证。单值性改变了局面。它表明对一个固定的输入，「一个输出连同该对属于图的证明」构成的类型是命题，而截断的值总能消去到命题中。于是图给出一个真正的、取值在模型中的函数；再假设单射性，便得到真正的单射。这第一层读回把取值保留为载体的元素，是后续证明仍需对编码图作推理时使用的形式。
<!--ja-->
## モデルに値を取る単射を取り出す

グラフが一価でちょうどの定義域を持つと仮定すると、定義域の各要素はグラフの中に何らかの像を持ちますが、それはもっぱら存在するだけの像です。定義域への所属が与えるのは命題の切り詰めであって、選ばれた証人ではありません。一価性がこの状況を変えます。入力を固定すると、「出力と、その対がグラフに属する証明」の組の型が命題であることが示され、切り詰められた値はいつでも命題へ消去できます。したがってグラフはモデルに値を取る本物の関数を与え、単射性まで仮定すれば本物の単射になります。この第一の読み戻しは値を台の要素のまま保つ形で、後の証明がコード化されたグラフを参照し続けるときに使われます。
<!--/-->

<!--en-->
The section takes the graph `F` and the domain `D` as model elements, together with the two satisfaction hypotheses: single-valuedness of the graph at variable zero, and the exact-domain clause saying that every element of `D` has a value under `F`. The environment `γ` packages them in the fixed order the satisfaction judgments expect.
<!--zh-->
本节把图 `F` 与定义域 `D` 作为模型元素，连同两个满足假设：变元零处图的单值性，以及断言 `D` 的每个元素在 `F` 下有取值的恰当定义域条款。环境 `γ` 按满足判断所期望的固定顺序把它们打包。
<!--ja-->
この節は、グラフ `F` と定義域 `D` を模型の要素として、二つの充足の仮定とともに取ります。変数ゼロでのグラフの一価性と、`D` のすべての要素が `F` の下で値を持つと言うちょうどの定義域の条項です。環境 `γ` はそれらを、充足の判断が期待する固定の順序でまとめます。
<!--/-->

```agda
module Extract (F D : S)
               (sv : ⟨ (F ∷ D ∷ []) ⊨ svAt zero ⟩)
               (dm : ⟨ (F ∷ D ∷ []) ⊨ domAt zero (suc zero) ⟩) where

  γ : S ^ 2
  γ = F ∷ D ∷ []
```

<!--en-->
`Holds x y` is the projected membership of the pair of underlying sets in the underlying graph. The fiber `Fib x` pairs an output `y` with such a proof; it is the type whose elements are candidate values of the graph at `x`, each carrying its own certificate that it really is a value.
<!--zh-->
`Holds x y` 是底层对属于底层图的投影隶属。原像 `Fib x` 把一个输出 `y` 与这样的证明配成一对；它的元素就是图在 `x` 处的候选值，每个候选都带着「它确实是取值」的证书。
<!--ja-->
`Holds x y` は、底の対が底のグラフに属すという射影された所属です。ファイバー `Fib x` は出力 `y` にこの証明を添えた組で、その要素はグラフが `x` で取る候補の値であり、それぞれが本当に値であることの証明書を伴います。
<!--/-->

```agda

  Holds : S → S → Type (ℓ-suc ℓ)
  Holds x y = ⟨ pr (fst x) (fst y) ∈ fst F ⟩

  Fib : S → Type (ℓ-suc ℓ)
  Fib x = Σ[ y ∈ S ] Holds x y

  isPropFib : (x : S) → isProp (Fib x)
```

<!--en-->
To prove `Fib x` proposition-valued, compare `(y,p)` and `(y′,q)`. Single-valuedness supplies the path `fst y ≡ fst y′`. The inner `Σ≡Prop` lifts this path to `y ≡ y′` because the second component of an element of `S`, its `isL` certificate, is a proposition. The outer `Σ≡Prop` then lifts that equality to the two elements of `Fib x` because graph-membership proofs are propositions. These are two distinct proof-irrelevance steps; neither says that equality of ambient sets follows merely from constructibility.
<!--zh-->
要证明 `Fib x` 是命题，比较 `(y,p)` 与 `(y′,q)`。单值性先给出路径 `fst y ≡ fst y′`。内层 `Σ≡Prop` 利用 `S` 元素的第二分量即 `isL` 证书为命题，把该路径提升为 `y ≡ y′`；外层 `Σ≡Prop` 再利用图隶属证明为命题，把这一相等提升为 `Fib x` 的两个元素相等。这是两个不同的证明无关性步骤，并不是说周遭集合的相等仅由可构造性推出。
<!--ja-->
`Fib x` が命題であることを示すには、`(y,p)` と `(y′,q)` を比較します。一価性からまずパス `fst y ≡ fst y′` が得られます。内側の `Σ≡Prop` は、`S` の要素の第二成分である `isL` の証明が命題であることを使い、このパスを `y ≡ y′` へ持ち上げます。外側の `Σ≡Prop` は、グラフ所属の証明が命題であることを使い、その等しさを `Fib x` の二要素の等しさへ持ち上げます。これは別々の二つの証明無関係性の段階であり、周囲の集合の等しさが構成可能性だけから従うという意味ではありません。
<!--/-->

```agda
  isPropFib x (y , p) (y' , q) =
    Σ≡Prop (λ w → snd (pr (fst x) (fst w) ∈ fst F))
      (Σ≡Prop (λ z → snd (isL z)) (svAt-out zero γ sv x y y' p q))

  toVal : (x : S) → ∥ Fib x ∥₁ → Fib x
  toVal x = PT.rec (isPropFib x) (λ z → z)
```

<!--en-->
Because `Fib x` is a proposition, `toVal` can eliminate the truncated existence of a value, `∥ Fib x ∥₁`, into an actual fiber. This is the one place where a choice could seem to be hiding, and it is not: propositional truncation eliminates into any proposition-valued target, so no law of excluded middle and no selection of a canonical representative is needed. The domain `Dom` then packages an input with the projected proof that it belongs to `D`, and `fib` feeds each input's truncated image, obtained from `domAt-in`, through `toVal`.
<!--zh-->
由于 `Fib x` 是命题，`toVal` 能把取值的截断存在 `∥ Fib x ∥₁` 消去为实际的原像。选择似乎藏在这里，其实没有：命题截断可以消去到任何命题值的目标，既不需要排中律也不需要选典范代表。定义域 `Dom` 把输入与其属于 `D` 的投影证明打包，`fib` 把由 `domAt-in` 得到的每个输入的截断像送入 `toVal`。
<!--ja-->
`Fib x` が命題なので、`toVal` は値の切り詰められた存在 `∥ Fib x ∥₁` を実際のファイバーへ消去できます。選択がここに隠れていそうで、そうではありません。命題の切り詰めは命題値の任意の対象へ消去できるので、排中律も代表的な元の選出も要りません。定義域 `Dom` は入力に `D` への所属の射影された証明を添えてまとめ、`fib` は `domAt-in` から得た各入力の切り詰められた像を `toVal` に通します。
<!--/-->

```agda

  Dom : Type (ℓ-suc ℓ)
  Dom = Σ[ x ∈ S ] ⟨ fst x ∈ fst D ⟩

  fib : (u : Dom) → Fib (fst u)
  fib (x , m) = toVal x (domAt-in zero (suc zero) γ dm x m)

  toFun : Dom → S
```

<!--en-->
The function `toFun` sends a domain entry to the output `y : S` in its unique fiber. It discards only the accompanying graph-membership proof; the output remains a model element and therefore retains its constructibility certificate. The theorem `toFun-graph` recovers exactly that discarded membership evidence as the second component of the fiber.
<!--zh-->
函数 `toFun` 把定义域元素送到其唯一原像中的输出 `y : S`。它只舍去随附的图隶属证明；输出仍是模型元素，因此保留其可构造性证书。定理 `toFun-graph` 恰把这份被舍去的隶属证据作为原像的第二分量取回。
<!--ja-->
関数 `toFun` は定義域の要素を、その一意なファイバーに含まれる出力 `y : S` へ送ります。捨てるのは付随するグラフ所属の証明だけで、出力はモデルの要素のままなので構成可能性の証明書を保持します。定理 `toFun-graph` は、捨てた所属の証拠をファイバーの第二成分として取り出します。
<!--/-->

```agda
  toFun u = fst (fib u)

  toFun-graph : (u : Dom) → Holds (fst u) (toFun u)
  toFun-graph u = snd (fib u)

  module _ (ij : ⟨ γ ⊨ injAt zero ⟩) where

    toFun-inj : (u v : Dom) → fst (toFun u) ≡ fst (toFun v)
```

<!--en-->
With injectivity of the graph also assumed, `toFun-inj` turns equality of outputs into equality of inputs. If the underlying sets of `toFun u` and `toFun v` agree, the graph equation of `u` is transported along that path so that both entries speak about the same output, namely `toFun v`; `injAt-out` then compares the two inputs and returns the equality of the first components of `fst u` and `fst v`. The result is stated on projected first components, the form in which downstream cardinal arguments compare elements of `Dom`.
<!--zh-->
再假设图的单射性，`toFun-inj` 把输出的相等变成输入的相等。若 `toFun u` 与 `toFun v` 的底层集合相等，就把 `u` 的图等式沿该路径运输，使两条目都谈及同一个输出即 `toFun v`；`injAt-out` 随后比较两个输入，给出 `fst u` 与 `fst v` 的第一分量之相等。结论是对投影后的第一分量陈述的，下游基数论证比较 `Dom` 的元素时用的正是这一形式。
<!--ja-->
グラフの単射性まで仮定すると、`toFun-inj` は値の等しさを引数の等しさに変えます。`toFun u` と `toFun v` の底の集合が等しければ、`u` のグラフの等式をそのパスに沿って輸送して、両方の項目が同じ値、すなわち `toFun v` について語るようにし、`injAt-out` が二つの引数を比較して `fst u` と `fst v` の第一成分の等しさを返します。結果は射影された第一成分について述べられ、後続の基数論が `Dom` の要素を比較するときの形です。
<!--/-->

```agda
              → fst (fst u) ≡ fst (fst v)
    toFun-inj u v e = injAt-out zero γ ij (toFun v) (fst u) (fst v)
      (subst (λ w → ⟨ pr (fst (fst u)) w ∈ fst F ⟩) e (toFun-graph u))
      (toFun-graph v)
```

<!--en-->
## Restricting to the small carriers

The injection `toFun` acts on pairs of a model element and a membership proof, a carrier that cardinal arguments cannot count. The final step replaces both endpoints by the canonical small presentations: the domain becomes the index type of `D`, and the range becomes the index type of a set `C` supplied by the caller, which need only prove that every value of the graph lies in `C`. The graph clauses, single-valuedness, exact domain and injectivity, are all assumed here at once. What the presentation layer contributes is explicitness: membership in `D` and in `C` can be read off from indices and back, because the canonical embedding has proposition-valued fibers.
<!--zh-->
## 限制到小载体

函数 `toFun` 作用在「模型元素连同隶属证明」的对上，这样的载体无法用于基数计数。最后一步把两端都换成典范的小呈现：定义域换成 `D` 的索引类型，值域换成调用方提供的集合 `C` 的索引类型，调用方只需证明图的每个取值都落在 `C` 中。图的三个条款，单值性、恰当定义域与单射性，在此一并假设。呈现层的贡献在于显式性：因为典范嵌入有命题值的原像，属于 `D` 或 `C` 都能从索引读出，也能读回索引。
<!--ja-->
## 小さな台に制限する

関数 `toFun` は「模型の要素と所属の証明」の対に作用しますが、この台は基数の議論で数えることができません。最後の段階では両端を標準的な小さな提示に置き換えます。定義域は `D` のインデックス型に、値域は呼び出し側が指定する集合 `C` のインデックス型になり、呼び出し側はグラフのどの値も `C` に属すことを証明するだけで済みます。グラフの三つの条項、一価性、ちょうどの定義域、単射性は、ここでまとめて仮定します。提示の層がもたらすのは明示性です。標準的な埋め込みのファイバーが命題値であるため、`D` や `C` への所属はインデックスから読み出せ、インデックスへ読み戻せます。
<!--/-->

<!--en-->
The parameters name the three constructible sets at play: the graph `F`, the domain `D`, and the range `C`. The first three hypotheses are exactly the satisfaction statements that Extract and toFun-inj consumed. The last, `ran`, is new: for any input `x` and value `y` with the pair `(x, y)` in the graph, it certifies that the underlying set of `y` belongs to the underlying set of `C`. This is a range restriction stated as a hypothesis on the caller's side, so the section itself never assumes that the graph was built with a particular range.
<!--zh-->
参数点名了起作用的三个可构造集合：图 `F`、定义域 `D` 与值域 `C`。前三个假设正是 Extract 与 toFun-inj 所用的满足陈述。最后一条 `ran` 是新的：对任意输入 `x` 与使 `(x, y)` 属于图的取值 `y`，它证书化 `y` 的底层集合属于 `C` 的底层集合。这是作为调用方假设陈述的取值限制，因此本节本身从不假设图是以某个特定值域造出的。
<!--ja-->
パラメータは、ここで働く三つの構成可能集合、グラフ `F`、定義域 `D`、値域 `C` を名指します。最初の三つの仮定は、Extract と toFun-inj が使った充足の主張そのものです。最後の `ran` が新しいもので、入力 `x` と、対 `(x, y)` がグラフに属すような値 `y` に対して、`y` の底の集合が `C` の底の集合に属すことを証明書として与えます。これは値域の制限を呼び出し側の仮定として述べたもので、この節自身はグラフが特定の値域を持って作られたと仮定しません。
<!--/-->

```agda
module Small (F D C : S)
             (sv : ⟨ (F ∷ D ∷ []) ⊨ svAt zero ⟩)
             (dm : ⟨ (F ∷ D ∷ []) ⊨ domAt zero (suc zero) ⟩)
             (ij : ⟨ (F ∷ D ∷ []) ⊨ injAt zero ⟩)
             (ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩
```

<!--en-->
Under the single-valuedness and exact-domain hypotheses, `Extract` supplies the unique graph value for each domain member. To compare this construction with the small presentation, `toS` turns an index `m` of the canonical presentation of `D` into a model element. The first component is the presented set itself; the second is its constructibility certificate, obtained by `isL-trans` from the explicit membership `member (fst D) m` and the certificate that `D` itself is constructible. Transitivity is exactly the principle needed: a member of a constructible set is constructible.
<!--zh-->
内层模块以 `F`、`D` 与前两个满足证明重新打开 Extract，于是上一节的所有构造都以带前缀的名字可用。接着 `toS` 把 `D` 的典范呈现的一个索引 `m` 变成模型元素。第一分量就是被呈现的集合本身；第二分量是其可构造性证书，由 `isL-trans` 从显式隶属 `member (fst D) m` 与 `D` 自身可构造的证书得出。传递性正是所需的原理：可构造集合的成员是可构造的。
<!--ja-->
内側のモジュールは、`F` と `D` と先の二つの充足の証明で Extract を改めて開くので、前節の構成はすべて接頭辞付きの名前で使えます。そして `toS` は `D` の標準的な提示のインデックス `m` を模型の要素に変えます。第一成分は提示された集合そのものであり、第二成分はその構成可能性の証明書で、`isL-trans` により、明示的な所属 `member (fst D) m` と `D` 自身が構成可能である証明書から得られます。推移性はまさに必要な原理です。構成可能集合の要素は構成可能です。
<!--/-->

```agda
                  → ⟨ fst y ∈ fst C ⟩) where

  module E = Extract F D sv dm

  toS : ⟪ fst D ⟫ → S
  toS m = ⟪ fst D ⟫↪ m
        , isL-trans {x = fst D} {y = ⟪ fst D ⟫↪ m} (member (fst D) m) (snd D)
```

<!--en-->
Each small index must also be seen as a member of the domain in Extract's sense, and `at` supplies that pair: the model element `toS m` together with the explicit membership proof `member (fst D) m`. Feeding `at m` to the graph through `E.toFun` produces a value, and the range hypothesis certifies that this value belongs to `C`. Because the membership `⟪ fst C ⟫↪ k ≡ fst (E.toFun (at m))` in the canonical presentation is a fiber of an embedding with proposition-valued fibers, `fiber` returns an actual index `k` together with a path, not merely the truncated existence of one.
<!--zh-->
每个小索引还须被看作 Extract 意义下定义域的成员，`at` 提供这一对：模型元素 `toS m` 连同显式隶属证明 `member (fst D) m`。把 `at m` 经 `E.toFun` 喂给图得到一个取值，取值假设证书化该值属于 `C`。由于典范呈现中的隶属 `⟪ fst C ⟫↪ k ≡ fst (E.toFun (at m))` 是具有命题值原像的嵌入的原像，`fiber` 返回的是实际的索引 `k` 连同一条路径，而非仅仅是截断的存在。
<!--ja-->
各小さなインデックスは、Extract の意味でも定義域の要素と見なされねばならず、`at` がその組を与えます。模型の要素 `toS m` と明示的な所属の証明 `member (fst D) m` です。`at m` を `E.toFun` でグラフに通すと値が得られ、値域の仮定がこの値が `C` に属すことを証明します。標準的な提示での所属 `⟪ fst C ⟫↪ k ≡ fst (E.toFun (at m))` は、命題値のファイバーを持つ埋め込みのファイバーなので、`fiber` は切り詰められた存在ではなく、実際のインデックス `k` とパスの組を返します。
<!--/-->

```agda

  at : ⟪ fst D ⟫ → E.Dom
  at m = toS m , member (fst D) m

  fib : (m : ⟪ fst D ⟫)
      → Σ[ k ∈ ⟪ fst C ⟫ ] (⟪ fst C ⟫↪ k ≡ fst (E.toFun (at m)))
  fib m = fiber (fst C)
```

<!--en-->
Discarding the path leaves `small`, a function from the index type of `D` to the index type of `C`. Each domain index is sent to the index naming its image under the graph. At this point the two representations meet: `small` is a map between types at the fixed universe level, exactly the shape a counting argument requires, and its behavior is tied to the graph through the retained paths.
<!--zh-->
舍去路径便得到 `small`：从 `D` 的索引类型到 `C` 的索引类型的函数。每个定义域索引被送到「在图下的像」所对应的索引。至此两种表示会合：`small` 是固定宇宙层级上类型之间的映射，正是计数论证所需的形状，而它经由保留的路径与图联系在一起。
<!--ja-->
パスを捨てると `small` が得られます。`D` のインデックス型から `C` のインデックス型への関数で、各定義域のインデックスは、グラフの下での像に対応するインデックスへ送られます。ここで二つの表現が合流します。`small` は固定された宇宙レベルの型の間の写しであり、数え上げの議論が求める形そのものであり、保持されたパスを通してグラフと結び付いています。
<!--/-->

```agda
    (ran (toS m) (E.toFun (at m)) (E.toFun-graph (at m)))

  small : ⟪ fst D ⟫ → ⟪ fst C ⟫
  small m = fst (fib m)

  small-inj : (m n : ⟪ fst D ⟫) → small m ≡ small n → m ≡ n
  small-inj m n e = ↪-inj {a = fst D} {m = m} {n = n}
```

<!--en-->
Injectivity of `small` is proved by routing an equality of indices back through the presentations. From `small m ≡ small n`, the path `snd (fib m)` is reversed to see the presented value at `m`, congruence under the embedding carries the equality across, and `snd (fib n)` lands at the presented value at `n`; the concatenation of the three paths, taken in exactly this direction, equates the underlying sets of the two outputs. Extract's injectivity then equates the underlying sets of the two inputs, and `↪-inj`, the injectivity of the domain presentation embedding on indices, concludes `m ≡ n`. Two distinct injectivity facts are at work, one for the graph and one for the canonical embedding, and neither substitutes for the other.
<!--zh-->
`small` 的单射性由索引的相等沿呈现往返证得。由 `small m ≡ small n`，反向取 `snd (fib m)` 得到 `m` 处的呈现值，嵌入下的同余把相等传过去，`snd (fib n)` 落到 `n` 处的呈现值；三条路径按这个确切方向拼接，使两个输出的底层集合相等。Extract 的单射性随之给出两个输入的底层集合相等，而 `↪-inj`，即定义域呈现嵌入在索引上的单射性，最终给出 `m ≡ n`。这里有两个不同的单射性事实在起作用，一个关于图，一个关于典范嵌入，二者不可互相替代。
<!--ja-->
`small` の単射性は、インデックスの等しさを提示の中を通して辿ることで証明されます。`small m ≡ small n` から、`snd (fib m)` を逆向きにたどって `m` での提示された値を得、埋め込みの下での合同が等しさを運び、`snd (fib n)` が `n` での提示された値に着きます。三つのパスを正にこの方向でつなぐことで、二つの値の底の集合が等しくなります。続いて Extract の単射性が二つの入力の底の集合の等しさを与え、`↪-inj`、すなわち定義域の提示の埋め込みのインデックス上の単射性が `m ≡ n` を結論します。ここでは二つの異なる単射性の事実が働いており、一つはグラフについて、もう一つは標準的な埋め込みについてで、どちらも他方で代用できません。
<!--/-->

```agda
    (E.toFun-inj ij (at m) (at n)
      (sym (snd (fib m)) ∙ cong ⟪ fst C ⟫↪ e ∙ snd (fib n)))
```

<!--en-->
## Recap

`injAt` expresses injectivity of a coded graph inside the model. Single-valuedness and an exact domain let `Extract.toFun` read the graph as a function into `L`; the separate hypothesis `ij` makes `Extract.toFun-inj` available. With the stated range condition, `Small.small` transfers that injection to the canonical small member types of the domain and range. The truncation step uses uniqueness of the image fiber, and the presentation step uses proposition-valued embedding fibers.
<!--zh-->
## 小结

`injAt` 在模型内部表达编码图的单射性。单值性与恰当定义域使 `Extract.toFun` 能把图读成取值于 `L` 的函数；独立假设 `ij` 才给出 `Extract.toFun-inj`。加上指定的值域条件后，`Small.small` 把该单射转移到定义域和值域的典范小成员类型上。截断步骤使用像原像的唯一性，呈现步骤则使用嵌入原像为命题这一性质。
<!--ja-->
## まとめ

`injAt` は符号化グラフの単射性をモデル内部で表します。一価性と正確な定義域から `Extract.toFun` はグラフを `L` に値を取る関数として読み、独立な仮定 `ij` を加えて初めて `Extract.toFun-inj` が得られます。指定された値域条件の下で、`Small.small` はこの単射を定義域と値域の標準的な小さな要素型へ移します。切り詰めの段階では像のファイバーの一意性を、提示の段階では埋め込みのファイバーが命題であることを使います。
<!--/-->

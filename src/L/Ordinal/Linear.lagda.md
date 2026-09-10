<!--en-->
# Ordinals are linearly ordered by membership

Of any two ordinals, one belongs to the other or the two are equal. This chapter isolates the classical step needed for that comparison and explains why it requires an explicit hypothesis.

Everything about ordinals up to now has been closure: zero is one, successors are, unions are, bounds exist. Closure statements build; they never have to *decide* anything. Trichotomy decides. Given two ordinals with no relation assumed between them, it returns one of the three comparison cases, and this chapter obtains that decision from its explicit excluded-middle parameter. So the chapter takes the excluded middle as a module parameter, using the level-indexed packaging fixed in the foundations, and modules that use `ord-tri` receive that parameter explicitly.

Two ingredients from the ambient hierarchy make the proof shorter than the textbook version. Regularity gives a well-founded induction, used twice over, once in each argument. Extensionality means that mutual inclusion *is* equality, so the equal case needs no separate work. Excluded middle decides the two inclusions and the membership propositions used to turn a failed inclusion into a truncated counterexample.
<!--zh-->
# 序数由隶属关系线性排序

任两个序数，或一者属于另一者，或二者相等。本章把这种比较所需的经典步骤单独列出，并说明为何需要显式假设。

迄今关于序数的一切都是闭包：零是序数，后继是，并也是，上界存在。闭包陈述关乎建造；它们从不需要**判定**任何东西。三歧要判定。给定两个彼此之间不假设任何关系的序数，它要回答三种互斥情形中的哪一种成立，本章从显式的排中律参数取得这一判定。所以本章把排中律取作模块参数，采用基础阶段定下的逐层级打包形式，使用 `ord-tri` 的模块都显式接收这个参数。

来自环境层级的两样材料使证明比教科书版本更短。正则性给出良基归纳，而且要用两次，两个自变量各一次。外延性意味着互相包含**就是**相等，故相等那一情形无须另行处理。排中律既判定两个方向的包含，也判定把包含失败转成截断反例时所需的成员关系命题。
<!--ja-->
# 順序数は所属によって線形に順序付けられる

任意の二つの順序数は、一方が他方に属するか、両者が等しいかのどちらかです。本章では、この比較に必要な古典的段階を切り分け、なぜ明示的な仮定が必要かを説明します。

これまでの順序数に関する命題はすべて閉包性でした。零は順序数であり、後続も和も順序数であり、上限も存在する。閉包の主張は構築に関わるもので、何かを**判定**する必要はありません。三分性は判定を要求します。互いに何の関係も仮定されていない二つの順序数を与えられ、三つの場合のどれが成り立つかを答えなければならず、本章では、この判定を明示的な排中律のパラメータから得ます。そこで本章は排中律をモジュールパラメータとして取り、基礎の段階で固定されたレベルごとのパッケージングを用います。`ord-tri` を使うモジュールは、このパラメータを明示的に受け取ります。

周囲の階層からの二つの材料が、証明を教科書の版より短くします。正則性公理は整礎帰納を与え、二つの引数に対して一度ずつ、計二回使われます。外延性により、相互包含**は**等号そのものなので、等しい場合を別途扱う必要はありません。排中律は二方向の包含を判定し、さらに包含の失敗を切り詰められた反例へ変える際に必要な所属命題も判定します。
<!--/-->

<!--en-->
The chapter runs under a single classical hypothesis, stated once as a module parameter: an instance of `LEM (ℓ-suc ℓ)`. Recall its shape from the foundations: for each proposition `P : hProp (ℓ-suc ℓ)`, it returns either a proof of `⟨ P ⟩` or a refutation, a map from `⟨ P ⟩` into the empty type. This level matches `⊆ᵇ-prop A B : hProp (ℓ-suc ℓ)` and the membership propositions decided inside the counterexample argument. Keeping the assumption as an explicit module parameter records the classical input at each use of this module.
<!--zh-->
全章只在模块参数的形式下使用一条经典假设：`LEM (ℓ-suc ℓ)` 的一个实例。回顾基础阶段的形状：对每个命题 `P : hProp (ℓ-suc ℓ)`，它返回 `⟨ P ⟩` 的证明，或一个反驳，即从 `⟨ P ⟩` 映入空类型的映射。这个层级恰好匹配 `⊆ᵇ-prop A B : hProp (ℓ-suc ℓ)` 以及反例论证中被判定的成员关系命题。把假设保留为显式模块参数，会在每次使用本模块时记录经典输入。
<!--ja-->
本章はただ一つの古典的仮定の下で進みます。それはモジュールパラメータとして一度だけ宣言される `LEM (ℓ-suc ℓ)` の実例です。基礎の章で確めた形を思い出してください。各命題 `P : hProp (ℓ-suc ℓ)` に対し、`⟨ P ⟩` の証明か、あるいは `⟨ P ⟩` を空型へ写す反証を返します。このレベルは `⊆ᵇ-prop A B : hProp (ℓ-suc ℓ)` と、反例の議論で判定する所属命題に一致します。仮定を明示的なモジュールパラメータとして保つことで、このモジュールを使うたびに古典的入力が記録されます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Ordinal.Linear {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

<!--en-->
The proof works directly in the ambient hierarchy V rather than through the object language. The carrier and the structure membership `∈ˢ` come from the ZF structure packaged over `𝒮ᵥ`, so `⟨ x ∈ˢ A ⟩` is the underlying proposition of a truth value in the hProp truth algebra. Two principles of V carry the mathematical weight: `extensionalV`, which converts a family of membership biconditionals into a path of equality, and `regularityV`, which makes membership well-founded and thus supports induction on it. The remaining import from the L-side, `mem-ord`, matters at every recursive call: it shows that any member of an ordinal is itself an ordinal, which is what lets the induction hypothesis apply below.
<!--zh-->
证明直接在环境层级 V 中进行，而不经由对象语言。载体与结构隶属 `∈ˢ` 来自打包在 `𝒮ᵥ` 上的 ZF 结构，因此 `⟨ x ∈ˢ A ⟩` 是 hProp 真值代数中一个真值的底层命题。V 的两条原理承担数学重任：`extensionalV` 把一族成员关系的双向蕴含转换为相等的路径；`regularityV` 使隶属关系良基，从而支持其上的归纳。L 侧其余的导入 `mem-ord` 在每次递归调用处起作用：它表明序数的任何成员自身也是序数，这正是归纳假设能在下层使用的原因。
<!--ja-->
証明は対象言語を経由せず、周囲の階層 V の中で直接行われます。台と構造の所属 `∈ˢ` は `𝒮ᵥ` の上にパッケージされた ZF 構造から来るので、`⟨ x ∈ˢ A ⟩` は hProp 真理値代数における真理値の基底命題です。V の二つの原理が数学的な重みを担います。`extensionalV` は所属関係の双条件の族を等号のパスへ変え、`regularityV` は所属関係を整礎にしてその上の帰納を可能にします。L 側のもう一つの輸入 `mem-ord` は再帰呼び出しのたびに効きます。順序数の任意の要素がそれ自身順序数であることを示すもので、これが帰納仮説を下の層で使えるようにする理由です。
<!--/-->

```agda

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; regularityV )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( mem-ord )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
```

<!--en-->
The decision procedure returns which of three cases holds, so the return type is built from a three-way sum: membership on the left, equality in the middle, membership on the right. Also needed is the conversion from an iff to a path, which the extensionality argument will apply to each point of the carrier. The empty type plays the role of refutation throughout: to refute a proposition is to map it into something with no inhabitants.
<!--zh-->
判定程序要回答三种情形中哪一种成立，因此返回类型由三向和构造：左边是隶属关系，中间是相等，右边是隶属关系。还需要从双向蕴含到路径的转换，外延性论证将对载体的每一点使用它。空类型全程扮演反驳的角色：反驳一个命题，就是把它映入一个没有元素的类型。
<!--ja-->
判定手続きは三つの場合のどれが成り立つかを返すので、返り値の型は三分岐の直和で組み立てます。左に所属、中央に等号、右に所属です。さらに必要なのは双条件からパスへの変換で、外延性の議論が台の各点に適用します。空型は全体を通して反証の役割を果たします。命題を反証するとは、それを元を持たない型へ写すことです。
<!--/-->

```agda
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
import Cubical.Induction.WellFounded as WF
```

<!--en-->
Two final conventions are opened for the whole file. The truth algebra interface supplies the propositional connectives used inside membership statements, and the structure vocabulary fixes `S` as the carrier and `∈ˢ` as its membership, so the code reads as set theory rather than as logic plumbing. These conventions let the proof track membership, equality, and well-founded recursion for ordinal elements directly.
<!--zh-->
最后为整个文件打开两项约定。真值代数接口提供成员关系陈述内部使用的命题联结词，结构词汇把 `S` 固定为载体、`∈ˢ` 固定为其隶属关系，于是代码读起来是集合论而非逻辑管道。这些约定让后面的论证能直接追踪序数元素的隶属、相等与良基递归。
<!--ja-->
最後に、ファイル全体に対して二つの約束を開きます。真理値代数のインターフェースは所属の記述の中で使われる命題結合子を供給し、構造の語彙は `S` を台、`∈ˢ` をその所属として固定します。これでコードは論理の配管ではなく集合論として読めます。この設定に新しい数学はありません。前の章々の順序数が階層 V と出会うインターフェースです。
<!--/-->

```agda

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## Inclusion, and what fails it

The proof pivots on one relation: pointwise inclusion. If it holds both ways, extensionality makes the two ordinals equal; if it fails in one direction, excluded middle supplies a truncated member witnessing the failure; well-founded induction and transitivity then turn that counterexample into a strict comparison. This subsection fixes the relation and its packaging. Note what the level arithmetic already says: inclusion lives at `Type (ℓ-suc ℓ)`, which is precisely where the supplied instance of excluded middle can decide it.
<!--zh-->
## 包含，及其失败的见证

证明围绕一个关系展开：逐点包含。若它双向成立，外延性使两个序数相等；若它在某一方向失败，排中律给出一个截断的反例成员；良基归纳与传递性再把这个反例转成严格比较。本小节固定这个关系及其打包方式。注意层级运算已经说明的事：包含住在 `Type (ℓ-suc ℓ)`，这正是所给排中律实例能判定它的那一层。
<!--ja-->
## 包含と、その失敗を示す証人

証明は一つの関係を軸に回ります。点ごとの包含です。これが両方向に成り立てば外延性により二つの順序数は等しく、一方向で失敗すれば排中律が切り詰められた反例の要素を与え、整礎帰納と推移性がその反例を狭義の比較へ変えます。この節ではその関係とそのパッケージングを固定します。レベルの計算がすでに語っていることに注意してください。包含は `Type (ℓ-suc ℓ)` に住み、これは与えられた排中律の実例がまさに判定できる場所です。
<!--/-->

<!--en-->
Inclusion of `A` in `B` is not a primitive here but a defined notion: every member `x` of `A`, in the structure sense, must be a member of `B`. Each membership `x ∈ˢ A` is a proposition in the hProp truth algebra, so the definition quantifies over the carrier `S` and over propositions at level `ℓ`, which places the whole relation in `Type (ℓ-suc ℓ)`. The matching hProp packaging attaches the propositionhood proof: a dependent function into a proposition is again a proposition, applied twice to the two nested function types. This matters because the excluded middle is decided per hProp, and it is exactly this packaged statement that the proof will hand to `lem`.
<!--zh-->
`A` 包含于 `B` 在这里不是初始概念而是定义出来的：`A` 的每个成员 `x`，在结构意义下，必须是 `B` 的成员。每个成员关系 `x ∈ˢ A` 是 hProp 真值代数中的命题，因此定义量化了载体 `S` 与 `ℓ` 层的命题，把整个关系放进 `Type (ℓ-suc ℓ)`。配套的 hProp 打包附上命题性的证明：到命题的依赖函数仍是命题，把这一点对两层嵌套的函数类型各用一次。这很重要，因为排中律是逐 hProp 判定的，而证明交给 `lem` 的正是这个打包后的陈述。
<!--ja-->
`A` が `B` に含まれることはここでは原始概念ではなく定義された概念です。`A` の各要素 `x` は、構造の意味で、`B` の要素でなければならない。各所属 `x ∈ˢ A` は hProp 真理値代数の命題なので、この定義は台 `S` とレベル `ℓ` の命題を量化し、関係全体を `Type (ℓ-suc ℓ)` に置きます。対応する hProp のパッケージングは命題性の証明を添えます。命題への依存関数は再び命題であり、これを入れ子になった二つの関数型にそれぞれ適用します。これが重要なのは、排中律が hProp ごとに判定されるからであり、証明が `lem` に渡すのはまさにこのパッケージされた命題です。
<!--/-->

```agda
_⊆ᵇ_ : S → S → Type (ℓ-suc ℓ)
A ⊆ᵇ B = (x : S) → ⟨ x ∈ˢ A ⟩ → ⟨ x ∈ˢ B ⟩

⊆ᵇ-prop : (A B : S) → hProp (ℓ-suc ℓ)
⊆ᵇ-prop A B = (A ⊆ᵇ B) , isPropΠ (λ x → isPropΠ (λ _ → snd (x ∈ˢ B)))

ext-⊆ᵇ : {A B : S} → A ⊆ᵇ B → B ⊆ᵇ A → A ≡ B
```

<!--en-->
The equal case of trichotomy comes for free from extensionality of the hierarchy. Given inclusions both ways, each point `x` of the carrier yields an iff between `⟨ x ∈ˢ A ⟩` and `⟨ x ∈ˢ B ⟩`; `⇔toPath` turns that iff into a path, and `extensionalV` assembles the family of paths into the equality `A ≡ B`. No classical input is used here at all: extensionality is a theorem of V itself.
<!--zh-->
三歧中的相等情形由层级的外延性免费给出。给定双向包含，载体的每一点 `x` 都给出 `⟨ x ∈ˢ A ⟩` 与 `⟨ x ∈ˢ B ⟩` 之间的双向蕴含；`⇔toPath` 把它变成路径，`extensionalV` 再把路径族组装成相等 `A ≡ B`。这里完全没有用到经典输入：外延性本身就是 V 的定理。
<!--ja-->
三分性の等号の場合は、階層の外延性からただで手に入ります。両方向の包含が与えられれば、台の各点 `x` は `⟨ x ∈ˢ A ⟩` と `⟨ x ∈ˢ B ⟩` の間の双条件を与え、`⇔toPath` がそれをパスに変え、`extensionalV` がパスの族を等式 `A ≡ B` に組み立てます。ここには古典的な入力はまったく使われません。外延性は V 自身の定理だからです。
<!--/-->

```agda
ext-⊆ᵇ {A} {B} s₁ s₂ = extensionalV (λ x → ⇔toPath (s₁ x) (s₂ x))
```

<!--en-->
Here is the one genuinely classical step. From a *failure* of inclusion the proof needs a member witnessing it, and passing from "not every member of `B` lies in `A`" to "some member does not" is not constructive. Excluded middle decides the existence statement directly: were there no such witness, then each member of `B` could be shown to lie in `A`, one decided membership at a time, contradicting the assumed failure. The witness that comes out remains propositionally truncated, and that is enough, because the only thing the trichotomy proof will do with it is eliminate it into a membership proposition.
<!--zh-->
这里是真正经典的那一步。从包含**失败**出发，证明需要一个见证它的成员，而从「`B` 的成员并非都含于 `A`」过渡到「某个成员不含于 `A`」不是构造性的。排中律直接判定那个存在陈述：若没有这样的见证，则可以逐个判定成员关系，证明 `B` 的每个成员终究含于 `A`，与假设的失败矛盾。得出的见证仍是命题截断的，而这已经足够，因为三歧证明对它唯一要做的事就是把它消去成一个成员关系命题。
<!--ja-->
ここが本当に古典的な一段です。包含の**失敗**から出発して、証明はそれを証人する要素を必要としますが、「`B` の要素がすべて `A` に含まれるわけではない」から「ある要素は含まれない」への移行は構成的ではありません。排中律がこの存在文を直接判定します。そのような証人が存在しないなら、所属を一つずつ判定しながら `B` の各要素がやはり `A` に含まれることを示せ、これは仮定された失敗に矛盾します。得られる証人は命題切り詰めされたままですが、それで十分です。三分性の証明がこれにすることは、メンバーシップ命題への消去だけだからです。
<!--/-->

<!--en-->
The statement is a conditional: if inclusion `A ⊆ᵇ B` is refutable, then a truncated witness exists, a member `a` of `A` with `a ∉ B`. The conclusion is deliberately an existence claim under `∥ ∥₁` rather than a chosen pair. The first classical move decides the truncated existence statement `Witness` itself. Note the level bookkeeping: the witness statement is an hProp at `ℓ-suc ℓ`, exactly where the module's `lem` applies, so no lifting is needed. In the positive branch the witness is already in hand; the interesting branch is the negative one.
<!--zh-->
陈述是条件式的：若包含 `A ⊆ᵇ B` 可被反驳，则存在一个截断的见证，即 `A` 的一个成员 `a` 使 `a ∉ B`。结论刻意写成 `∥ ∥₁` 下的存在陈述，而非选定的对。第一步经典动作是判定截断的存在陈述 `Witness` 本身。注意层级的记账：见证陈述是 `ℓ-suc ℓ` 处的 hProp，恰好是模块的 `lem` 适用的地方，因此无须抬升。正分支中见证已在手；有趣的是负分支。
<!--ja-->
この主張は条件文です。包含 `A ⊆ᵇ B` が反証可能なら、切り詰められた証人、すなわち `a ∉ B` を満たす `A` の要素 `a` が存在する。結論は選ばれた対ではなく、意図的に `∥ ∥₁` の下の存在主張になっています。最初の古典的な動作は、切り詰められた存在文 `Witness` 自体を判定することです。レベルの計算に注意してください。証人の文は `ℓ-suc ℓ` の hProp であり、モジュールの `lem` が適用できるちょうどその場所にあるので、持ち上げは不要です。肯定的な分岐では証人はすでに手にあり、興味があるのは否定的な分岐です。
<!--/-->

```agda
¬⊆ᵇ→witness : (A B : S) → (A ⊆ᵇ B → Empty.⊥)
            → ∥ Σ[ a ∈ S ] (⟨ a ∈ˢ A ⟩ × (⟨ a ∈ˢ B ⟩ → Empty.⊥)) ∥₁
¬⊆ᵇ→witness A B ¬sub = decide (lem Witness)
  where
  Witness : hProp (ℓ-suc ℓ)
```

<!--en-->
Suppose `Witness` is refutable. Then the refutation of inclusion can itself be refuted: for arbitrary `x`, we decide the membership `x ∈ˢ B` separately, and on the negative branch assemble the witness `x` with `x ∈ˢ A` and the refutation of `x ∈ˢ B` into an inhabitant of `Witness`, contradicting the given refutation. So inclusion holds after all, and feeding it to the assumed refutation of inclusion yields the empty type. This is exactly the pattern announced above: the single global decision on `Witness` plus a pointwise decision on each `x ∈ˢ B` together convert "no witness exists" into "inclusion holds".
<!--zh-->
设 `Witness` 可被反驳。那么对包含的反驳本身也可被反驳：对任意的 `x`，单独判定成员关系 `x ∈ˢ B`；在负分支中，把成员 `x` 连同 `x ∈ˢ A` 与对 `x ∈ˢ B` 的反驳组装成 `Witness` 的一个元素，与所给反驳矛盾。于是包含终究成立，把它交给假设的对包含的反驳就得到空类型。这正是上面宣布的模式：对 `Witness` 的一次全局判定，加上对每个 `x ∈ˢ B` 的逐点判定，共同把「不存在见证」转化为「包含成立」。
<!--ja-->
`Witness` が反証可能だとします。すると包含の反証自身も反証できます。任意の `x` に対して所属 `x ∈ˢ B` を独立に判定し、否定的な分岐では要素 `x` を `x ∈ˢ A` と `x ∈ˢ B` の反証とともに `Witness` の元へ組み立てます。これは与えられた反証に矛盾します。したがって包含は結局成り立ち、それを仮定された包含の反証に渡せば空型が得られます。これはまさに上で述べたパターンです。`Witness` への一度の大域判定と、各 `x ∈ˢ B` への点ごとの判定が、「証人は存在しない」を「包含は成り立つ」へ変えます。
<!--/-->

```agda
  Witness = ∥ Σ[ a ∈ S ] (⟨ a ∈ˢ A ⟩ × (⟨ a ∈ˢ B ⟩ → Empty.⊥)) ∥₁
          , PT.isPropPropTrunc
  decide : ⟨ Witness ⟩ ⊎ (⟨ Witness ⟩ → Empty.⊥) → ⟨ Witness ⟩
  decide (inl wit)  = wit
  decide (inr ¬wit) = Empty.rec (¬sub sub)
```

<!--en-->
The pointwise decision is worth pausing on, because it shows how a truncated conclusion tolerates a truncated input. To prove `x ∈ˢ B` from `x ∈ˢ A`, decide that single membership with `lem`. If it holds, done. If it fails, the refutation of `x ∈ˢ B`, together with `x ∈ˢ A` and `x`, is exactly the data of a witness, and its truncation `∣ x , (x∈A , ¬x∈B) ∣₁` is an inhabitant of `Witness`, contradicting the negative branch's hypothesis.
<!--zh-->
逐点判定值得停一停，因为它显示了截断的结论如何容纳截断的输入。要从 `x ∈ˢ A` 证明 `x ∈ˢ B`，用 `lem` 判定这一个成员关系。若成立则完成。若失败，对 `x ∈ˢ B` 的反驳连同 `x ∈ˢ A` 与 `x` 恰好是见证的数据，其截断 `∣ x , (x∈A , ¬x∈B) ∣₁` 是 `Witness` 的一个元素，与负分支的假设矛盾。
<!--ja-->
点ごとの判定に少し立ち止まる価値があります。切り詰められた結論が切り詰められた入力をどう受け入れるかを示しているからです。`x ∈ˢ A` から `x ∈ˢ B` を証明するには、その一つの所属を `lem` で判定します。成り立てば終わりです。失敗するなら、`x ∈ˢ B` の反証は `x ∈ˢ A` と `x` とともにまさに証人のデータであり、その切り詰め `∣ x , (x∈A , ¬x∈B) ∣₁` は `Witness` の元となり、否定分岐の仮定に矛盾します。
<!--/-->

```agda
    where
    sub : A ⊆ᵇ B
    sub x x∈A = at (lem (x ∈ˢ B))
      where
      at : ⟨ x ∈ˢ B ⟩ ⊎ (⟨ x ∈ˢ B ⟩ → Empty.⊥) → ⟨ x ∈ˢ B ⟩
```

<!--en-->
Assembling the pieces: the outer decision on `Witness` returns the truncated witness directly in the positive case, and in the negative case derives a contradiction from the assumed failure of inclusion. The helper `¬⊆ᵇ→witness` is now available for both directions of the trichotomy argument, and it never promises more than a truncated witness. Keeping the truncation explicit is what makes the later elimination legal: propositional truncation may be eliminated only into propositions, and the membership statements the next subsection eliminates into are exactly that.
<!--zh-->
把各部分组装起来：对 `Witness` 的外层判定在正情形直接返回截断见证；在负情形，从假设的包含失败导出矛盾。辅助引理 `¬⊆ᵇ→witness` 现在可供三歧论证的两个方向使用，而且它承诺的从来不超过一个截断见证。保持截断显式正是使后面的消去合法的原因：命题截断只能消去到命题，而下一小节消去进入的成员关系陈述恰好是命题。
<!--ja-->
部品を組み立てます。`Witness` に対する外側の判定は、肯定的な場合は切り詰められた証人を直接返し、否定的な場合は仮定された包含の失敗から矛盾を導きます。補題 `¬⊆ᵇ→witness` はこれで三分性の議論の両方向で使えますが、切り詰められた証人以上のことは決して約束しません。切り詰めを明示的に保つことが後の消去を正当化する理由です。命題切り詰めは命題へしか消去できず、次の節で消去される所属の文はまさに命題だからです。
<!--/-->

```agda
      at (inl x∈B)  = x∈B
      at (inr ¬x∈B) = Empty.rec (¬wit ∣ x , (x∈A , ¬x∈B) ∣₁)
```

<!--en-->
## Trichotomy

Everything is now in place for the main theorem. The comparison is stated as a three-way sum: either `A` is a member of `B`, or the two are equal by a path, or `B` is a member of `A`. The proof runs well-founded induction twice, once on each argument, so that at a leaf it may recurse into members of either ordinal. The two inclusions `A ⊆ᵇ B` and `B ⊆ᵇ A` are decided in each induction step by excluded middle; the previous subsection then does the rest. Note the direction bookkeeping that the reader should carry through the case analysis: failure of `B ⊆ᵇ A` produces a member of `B` outside `A` and concludes `A ∈ˢ B`, while failure of `A ⊆ᵇ B` produces a member of `A` outside `B` and concludes `B ∈ˢ A`.
<!--zh-->
## 三歧

主要定理的准备工作已经齐备。比较写成三向和：或者 `A` 是 `B` 的成员，或者二者由一条路径相等，或者 `B` 是 `A` 的成员。证明对两个自变量各作一次良基归纳，使得在叶子处可以递归到任一序数的成员内部。两个包含 `A ⊆ᵇ B` 与 `B ⊆ᵇ A` 在每个叶子处由排中律判定；上一小节完成了其余工作。读者在情形分析中应当带上的方向记账是：`B ⊆ᵇ A` 失败产生一个属于 `B` 而不属于 `A` 的成员，结论是 `A ∈ˢ B`；`A ⊆ᵇ B` 失败产生一个属于 `A` 而不属于 `B` 的成员，结论是 `B ∈ˢ A`。
<!--ja-->
## 順序数の三分性

主定理のための準備はすべて整いました。比較は三分岐の直和として述べられます。`A` が `B` の要素であるか、両者がパスによって等しいか、`B` が `A` の要素であるか。証明は整礎帰納を引数ごとに一度ずつ、計二回実行し、葉のところでどちらの順序数の要素にも再帰できるようにします。二つの包含 `A ⊆ᵇ B` と `B ⊆ᵇ A` は各葉で排中律によって判定され、残りは前節が担いました。場合分けを通して読者が手にしておくべき向きの対応は次のとおりです。`B ⊆ᵇ A` の失敗は `B` に属し `A` に属さない要素を生み、結論は `A ∈ˢ B` です。`A ⊆ᵇ B` の失敗は `A` に属し `B` に属さない要素を生み、結論は `B ∈ˢ A` です。
<!--/-->

<!--en-->
The statement `Tri A B` packages the three possible answers in one type, built from nested sums. Its two outer cases are membership in the structure sense; the middle case is a path of equality. The type sits at `Type (ℓ-suc ℓ)`, which is the level forced by the membership propositions inside it.
<!--zh-->
陈述 `Tri A B` 把三种可能的答案打包进一个类型，由嵌套的和构造。外侧两种情形是结构意义的成员关系；中间情形是相等的路径。类型位于 `Type (ℓ-suc ℓ)`，这是其内部的成员关系命题所要求的层级。
<!--ja-->
主張 `Tri A B` は三つの答えを一つの型にまとめ、入れ子になった直和で組み立てます。外側の二つの場合は構造の意味での所属であり、中央の場合は等号のパスです。この型は `Type (ℓ-suc ℓ)` に住み、これは内部の所属命題が要求するレベルです。
<!--/-->

```agda
Tri : S → S → Type (ℓ-suc ℓ)
Tri A B = ⟨ A ∈ˢ B ⟩ ⊎ ((A ≡ B) ⊎ ⟨ B ∈ˢ A ⟩)

ord-tri : (A : S) → IsOrd A → (B : S) → IsOrd B → Tri A B
ord-tri = WF.WFI.induction regularityV {P = P} stepA
  where
```

<!--en-->
The theorem's shape is a well-founded induction supplied by regularity. The predicate being proven, `P A`, says that `A` behaves correctly for every ordinal `B` it is compared with, taking the two ordinality certificates as hypotheses. Regularity thus provides induction on the first argument: to prove `P A`, it suffices to prove `P A'` for every member `A'` of `A`. This is the first of the two nested inductions; the second, on `B`, will appear inside the step.
<!--zh-->
定理的形状是正则性供给的良基归纳。被证的谓词 `P A` 说的是：`A` 与任何与之比较的序数 `B` 都表现正确，并把两个序数性证明当作假设。于是正则性给出对第一个自变量的归纳：要证 `P A`，只需对 `A` 的每个成员 `A'` 证 `P A'`。这是两层嵌套归纳中的第一层；第二层对 `B`，将出现在步内。
<!--ja-->
定理の形は、正則性公理が供給する整礎帰納です。証明される述語 `P A` は、比較される任意の順序数 `B` に対して `A` が正しく振る舞うこと、二つの順序数性の証明を仮定として取ることを述べます。これにより正則性は第一引数上の帰納を与えます。`P A` を証明するには、`A` の各要素 `A'` について `P A'` を証明すれば十分です。これは入れ子になった二つの帰納の第一で、第二の `B` 上の帰納はステップの中に現れます。
<!--/-->

```agda
  P : S → Type (ℓ-suc ℓ)
  P A = IsOrd A → (B : S) → IsOrd B → Tri A B

  stepA : (A : S) → (∀ A' → ⟨ A' ∈ˢ A ⟩ → P A') → P A
  stepA A IHA ordA =
    WF.WFI.induction regularityV {P = λ B → IsOrd B → Tri A B} stepB
```

<!--en-->
The outer step receives the induction hypothesis for every member of `A` and immediately runs a second well-founded induction, this time on `B`, with its own predicate `λ B → IsOrd B → Tri A B`. At the inner leaf the two inclusions are decided by `lem` applied to the packaged propositions `⊆ᵇ-prop A B` and `⊆ᵇ-prop B A`. These two decisions begin the classical case analysis; the earlier helper also uses excluded middle to obtain a truncated counterexample from each failed inclusion.
<!--zh-->
外层步拿到 `A` 每个成员的归纳假设，随即运行第二个良基归纳，这次对 `B`，谓词是 `λ B → IsOrd B → Tri A B`。在内层归纳步中，两个包含由 `lem` 应用于打包命题 `⊆ᵇ-prop A B` 与 `⊆ᵇ-prop B A` 来判定。这两个判定开启经典的分情形；前面的辅助引理也使用排中律，把每个包含失败转成截断的反例。
<!--ja-->
外側のステップは `A` の各要素に対する帰納仮説を受け取り、すぐに第二の整礎帰納を実行します。今度は `B` 上で、述語は `λ B → IsOrd B → Tri A B` です。内側の帰納ステップでは、二つの包含がパッケージされた命題 `⊆ᵇ-prop A B` と `⊆ᵇ-prop B A` に `lem` を適用して判定されます。この二つの判定が古典的な場合分けを開始します。前の補題も排中律を使い、それぞれの包含の失敗から切り詰められた反例を得ます。
<!--/-->

```agda
    where
    stepB : (B : S) → (∀ B' → ⟨ B' ∈ˢ B ⟩ → IsOrd B' → Tri A B')
          → IsOrd B → Tri A B
    stepB B IHB ordB = decide (lem (⊆ᵇ-prop A B)) (lem (⊆ᵇ-prop B A))
      where
```

<!--en-->
The first failure case supposes `B ⊆ᵇ A` fails, so a member `b` of `B` outside `A` is merely known to exist. The helper `fromB` shows what one such explicit pair would give: since `b` is a member of the ordinal `B`, `mem-ord` certifies that `b` is itself an ordinal, and the inner induction hypothesis `IHB` may compare `A` with `b`. Its first outcome is `A ∈ˢ b`; ordinal transitivity, the first component of `IsOrd B`, then lifts this through `b ∈ˢ B` to `A ∈ˢ B`.
<!--zh-->
第一个失败情形假设 `B ⊆ᵇ A` 失败，于是仅仅存在 `B` 的一个不属于 `A` 的成员 `b`。辅助引理 `fromB` 表明这样一个显式的对能给出什么：由于 `b` 是序数 `B` 的成员，`mem-ord` 证明 `b` 自身是序数，内层归纳假设 `IHB` 便可比较 `A` 与 `b`。其第一种结果是 `A ∈ˢ b`；序数的传递性，即 `IsOrd B` 的第一个分量，再把它经由 `b ∈ˢ B` 提升为 `A ∈ˢ B`。
<!--ja-->
最初の失敗の場合は `B ⊆ᵇ A` が失敗すると仮定し、`B` のうち `A` に属さない要素 `b` が単に存在するとしか分かりません。補題 `fromB` は、そのような明示的な対が一つあれば何が得られるかを示します。`b` は順序数 `B` の要素なので、`mem-ord` が `b` 自身も順序数であることを証明し、内側の帰納仮説 `IHB` が `A` と `b` を比較できます。その第一の結果は `A ∈ˢ b` です。順序数の推移性、すなわち `IsOrd B` の第一成分が、これを `b ∈ˢ B` を経て `A ∈ˢ B` まで持ち上げます。
<!--/-->

```agda
      fromB : Σ[ b ∈ S ] (⟨ b ∈ˢ B ⟩ × (⟨ b ∈ˢ A ⟩ → Empty.⊥)) → ⟨ A ∈ˢ B ⟩
      fromB (b , (b∈B , ¬b∈A)) = at (IHB b b∈B (mem-ord {A = B} ordB b b∈B))
        where
        at : Tri A b → ⟨ A ∈ˢ B ⟩
        at (inl A∈b)       = ordB .fst A∈b b∈B
```

<!--en-->
The other two outcomes of comparing `A` with `b` are handled in turn. If `A ≡ b` by a path, then transporting `b ∈ˢ B` backward along that path, which is what `subst` with `sym` does, yields `A ∈ˢ B`. And if `b ∈ˢ A`, the choice of `b` as outside `A` is contradicted directly. All three branches land in the same proposition `⟨ A ∈ˢ B ⟩`, which is exactly why a merely existing witness suffices here: the truncated pair is eliminated into a proposition, never into data.
<!--zh-->
比较 `A` 与 `b` 的另外两种结果依次处理。若 `A ≡ b` 是一条路径，则沿该路径把 `b ∈ˢ B` 反向搬运，即用 `subst` 配 `sym` 所做的，得到 `A ∈ˢ B`。若 `b ∈ˢ A`，则与 `b` 被选为 `A` 之外直接矛盾。三个分支都落入同一命题 `⟨ A ∈ˢ B ⟩`，这正是仅仅存在的见证在此够用的原因：截断的对被消去进命题，从不消去进数据。
<!--ja-->
`A` と `b` の比較の残り二つの結果を順に処理します。`A ≡ b` がパスで与えられれば、そのパスに沿って `b ∈ˢ B` を逆方向へ輸送する、すなわち `subst` に `sym` を組み合わせる操作により `A ∈ˢ B` が得られます。また `b ∈ˢ A` なら、`b` を `A` の外として選んだことに直接矛盾します。三つの分岐はすべて同じ命題 `⟨ A ∈ˢ B ⟩` に着地します。これこそ、切り詰められた存在証人でここでは十分な理由です。切り詰められた対は命題へ消去されるのであって、データへ消去されることはありません。
<!--/-->

```agda
        at (inr (inl A≡b)) = subst (λ w → ⟨ w ∈ˢ B ⟩) (sym A≡b) b∈B
        at (inr (inr b∈A)) = Empty.rec (¬b∈A b∈A)

      fromA : Σ[ a ∈ S ] (⟨ a ∈ˢ A ⟩ × (⟨ a ∈ˢ B ⟩ → Empty.⊥)) → ⟨ B ∈ˢ A ⟩
      fromA (a , (a∈A , ¬a∈B)) =
        at (IHA a a∈A (mem-ord {A = A} ordA a a∈A) B ordB)
```

<!--en-->
The mirrored helper `fromA` covers the other failure: `A ⊆ᵇ B` fails, so some member `a` of `A` lies outside `B`. Now the outer induction hypothesis does the work, since it compares `A`'s members and is applied at `a`. If `a` turns out to be in `B`, the choice of `a` is contradicted; if `a ≡ B`, transport gives `B ∈ˢ A`; and if `B ∈ˢ a`, transitivity of `A` lifts it through `a ∈ˢ A`. Note the asymmetry the mirror introduces: the equality branch transports `a ∈ˢ A` along the path rather than reversing it, because this time the compared pair sits the other way round.
<!--zh-->
镜像的辅助引理 `fromA` 覆盖另一个失败：`A ⊆ᵇ B` 失败，于是 `A` 的某个成员 `a` 不在 `B` 内。此时由外层归纳假设承担工作，因为它比较 `A` 的成员，并在 `a` 处应用。若 `a` 结果属于 `B`，则与 `a` 的选取矛盾；若 `a ≡ B`，搬运给出 `B ∈ˢ A`；若 `B ∈ˢ a`，则 `A` 的传递性把它经由 `a ∈ˢ A` 提升。注意镜像引入的不对称：相等分支沿路径搬运 `a ∈ˢ A` 而非反向搬运，因为这次被比较的一对方向相反。
<!--ja-->
鏡像の補題 `fromA` はもう一つの失敗を扱います。`A ⊆ᵇ B` が失敗すれば、`A` のある要素 `a` が `B` の外にあります。今度は外側の帰納仮説が仕事をします。`A` の要素を比較するもので、`a` で適用されます。`a` が結局 `B` に属するなら `a` の選択に矛盾し、`a ≡ B` なら輸送により `B ∈ˢ A` が得られ、`B ∈ˢ a` なら `A` の推移性がこれを `a ∈ˢ A` を経て持ち上げます。鏡像が持ち込む非対称に注意してください。等号の分岐はパスに沿って `a ∈ˢ A` を輸送するのであって逆向きにはしない、今回は比較される組の向きが逆だからです。
<!--/-->

```agda
        where
        at : Tri a B → ⟨ B ∈ˢ A ⟩
        at (inl a∈B)       = Empty.rec (¬a∈B a∈B)
        at (inr (inl a≡B)) = subst (λ w → ⟨ w ∈ˢ A ⟩) a≡B a∈A
        at (inr (inr B∈a)) = ordA .fst B∈a a∈A
```

<!--en-->
With the two converters in hand, the four verdict combinations sort into the three answers. If both inclusions hold, mutual inclusion is equality by the previous subsection, and the middle answer is returned. If `A ⊆ᵇ B` holds but `B ⊆ᵇ A` fails, the truncated witness for the failure is eliminated with `PT.rec`, which is legal precisely because the target `⟨ A ∈ˢ B ⟩` is a proposition, its propositionhood supplied by the second component of the membership hProp. The result is the left answer `A ∈ˢ B`: this is the branch where failure of `B ⊆ᵇ A` concludes that `A` belongs to `B`.
<!--zh-->
两个转换器在手后，四种裁决组合归入三种答案。若两个包含都成立，由上一小节可知互相包含就是相等，返回中间答案。若 `A ⊆ᵇ B` 成立而 `B ⊆ᵇ A` 失败，则用 `PT.rec` 消去该失败的截断见证，这之所以合法，恰恰因为目标 `⟨ A ∈ˢ B ⟩` 是命题，其命题性由成员 hProp 的第二个分量提供。结果是左侧答案 `A ∈ˢ B`：这正是 `B ⊆ᵇ A` 失败而结论为 `A` 属于 `B` 的分支。
<!--ja-->
二つの変換器が手にあれば、四つの判定の組み合わせは三つの答えに整理されます。両方の包含が成り立てば、相互包含は等号であり、中央の答えが返ります。`A ⊆ᵇ B` が成り立ち `B ⊆ᵇ A` が失敗する場合は、その失敗の切り詰められた証人を `PT.rec` で消去します。これが正当なのは、目標 `⟨ A ∈ˢ B ⟩` が命題であり、その命題性が所属 hProp の第二成分から供給されるからです。結果は左の答え `A ∈ˢ B` です。`B ⊆ᵇ A` の失敗から `A` が `B` に属すると結論するのがこの分岐です。
<!--/-->

```agda

      decide : (A ⊆ᵇ B) ⊎ ((A ⊆ᵇ B) → Empty.⊥)
             → (B ⊆ᵇ A) ⊎ ((B ⊆ᵇ A) → Empty.⊥) → Tri A B
      decide (inl A⊆B) (inl B⊆A) = inr (inl (ext-⊆ᵇ A⊆B B⊆A))
      decide (inl A⊆B) (inr ¬B⊆A) =
        inl (PT.rec (snd (A ∈ˢ B)) fromB (¬⊆ᵇ→witness B A ¬B⊆A))
```

<!--en-->
The last combination covers failure of `A ⊆ᵇ B`, whatever the second verdict is, and the mirrored converter delivers `B ∈ˢ A`. Together with the two cases above, every leaf now returns an inhabitant of `Tri A B`, so the double induction closes and `ord-tri` stands as a theorem about arbitrary ordinals `A` and `B`. Later chapters on stage orders and on cardinals, for example `L.GCH.CardinalSquareLaw`, take it as their comparison primitive.
<!--zh-->
最后一种组合覆盖 `A ⊆ᵇ B` 的失败，无论第二个裁决如何，镜像转换器交付 `B ∈ˢ A`。与上面两种情形合并，每个叶子现在都返回 `Tri A B` 的一个元素，于是双层归纳闭合，`ord-tri` 成为关于任意序数 `A` 与 `B` 的定理。后续关于阶段序与基数的章节，例如 `L.GCH.CardinalSquareLaw`，把它当作自己的比较原语。
<!--ja-->
最後の組み合わせは、二番目の判定がどうであれ `A ⊆ᵇ B` の失敗を扱い、鏡像の変換器が `B ∈ˢ A` を届けます。上の二つの場合と合わせて、各葉は今や `Tri A B` の元を返し、二重の帰納は閉じて、`ord-tri` は任意の順序数 `A` と `B` についての定理として立ちます。段階順序や基数に関する後の章、たとえば `L.GCH.CardinalSquareLaw` は、これを比較の原始部品として使います。
<!--/-->

```agda
      decide (inr ¬A⊆B) _ =
        inr (inr (PT.rec (snd (B ∈ˢ A)) fromA (¬⊆ᵇ→witness A B ¬A⊆B)))
```

<!--en-->
## Recap

Together with the previously available irreflexivity of hierarchy membership and the transitivity contained in `IsOrd`, `ord-tri` now supplies comparison of any two ordinals. These comparison laws are the order-theoretic foundation for the stage monotonicity and cardinal arguments later in the book.

`ord-tri` compares any two ordinals, and the book supplies one instance of the excluded middle for it, taken as a module parameter. This is the boundary the groundwork was built to make auditable: nothing is postulated, and uses of `ord-tri` must supply the module’s excluded-middle parameter. The chapters that follow put the comparison to the question it was needed for: which ordinals appear at which stage of the constructible hierarchy.
<!--zh-->
## 小结

结合层级成员关系已有的非自反性和 `IsOrd` 所含的传递性，`ord-tri` 现在给出任意两个序数的比较。这些比较定律构成后续阶段单调性与基数论证的序论基础。

`ord-tri` 比较任意两个序数，而本书为它提供一份排中律实例，并把它取作模块参数。这正是奠基部分为使其可审计而搭建的那道边界：无一处 postulate，使用 `ord-tri` 时必须提供本模块的排中律参数。随后的章节把这个比较用在它被需要的那个问题上：哪些序数出现在可构造层级的哪个阶段。
<!--ja-->
## まとめ

階層の所属について既に得られた非反射性と `IsOrd` に含まれる推移性に加えて、`ord-tri` が任意の二つの順序数の比較を与えます。これらの比較法則は、後の段階の単調性と基数の議論に必要な順序論的基礎となります。

`ord-tri` は任意の二つの順序数を比較し、本書はそのために排中律の実例を一つ供給します。これはモジュールパラメータとして与えられます。これこそ基盤の部分が監査可能にするために築いた境界です。何一つ postulate されず、`ord-tri` を使うには、このモジュールの排中律パラメータを与える必要があります。続く章々は、この比較をそれが必要とされた問い、すなわちどの順序数が構成可能階層のどの段階に現れるか、に用います。
<!--/-->

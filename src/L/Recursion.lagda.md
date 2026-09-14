<!--en-->
# Internalizing recursive definitions in L

A recursive definition may first be given in the metatheory, while its values are later needed as a set of `L`. The replacement theorem supplies this passage. Given a domain in `L` and an object-language formula that has exactly one value at every point of the domain, it forms the set of all those values. The graph formula retains the dependence on the index; the set obtained by replacement is the value range, so equal values arising at different indices occur only once.
<!--zh-->
# L 中递归定义的内部化

递归定义可以先在元理论中给出，而它的取值随后需要组成 `L` 中的集合。替换定理实现这一转换。给定 `L` 中的定义域，以及一条在定义域每一点恰有一个取值的对象语言公式，替换便形成所有这些取值构成的集合。图公式保留取值对索引的依赖；替换所得集合只是值域，因此不同索引产生的相同取值只出现一次。
<!--ja-->
# L における再帰的定義の内部化

再帰的定義をまずメタ理論で与え、その値を後に `L` の集合として必要とすることがあります。この移行を与えるのが置換定理です。`L` の定義域と、その各点で値をただ一つもつ対象言語の論理式から、置換はすべての値からなる集合を作ります。添字への依存はグラフの論理式が保持します。置換で得られる集合は値域なので、異なる添字から同じ値が生じても一度だけ現れます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module L.Recursion {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

```

<!--en-->
The relation defining the values is written as an object-language formula with two free variables, read in the order value then index. Its satisfaction is evaluated in the constructible structure. This lets replacement speak about a relation internal to `L` while the proof of uniqueness remains available in the metatheory.
<!--zh-->
定义取值的关系写成带两个自由变元的对象语言公式，读取次序为值在前、索引在后。公式的满足关系在可构造结构中解释。这样，替换谈论的是 `L` 内部的关系，而唯一性的证明仍可在元理论中使用。
<!--ja-->
値を定める関係は、二つの自由変数をもつ対象言語の論理式で書き、値、添字の順に読みます。その充足関係は構成可能構造で解釈されます。これにより、置換は `L` の内部の関係を扱いながら、一意性の証明はメタ理論で利用できます。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
```

<!--en-->
The construction also uses the stage structure of `L`. Every constructible set appears at some stage, and the stages containing a family indexed by a type in `Type ℓ` can be bounded by one ordinal. This produces a single set containing the whole family when a convenient domain bound is needed.
<!--zh-->
构造还要使用 `L` 的层结构。每个可构造集合都出现在某一层，而由 `Type ℓ` 中的类型索引的一族集合，其所在层可以由同一个序数界定。需要统一的定义域上界时，这便给出一个包含整族元素的集合。
<!--ja-->
構成には `L` の段階構造も用います。各構成可能集合はある段階に現れ、`Type ℓ` の型で添字づけられた族の各段階は一つの順序数で抑えられます。共通の定義域の上界が必要なとき、これにより族全体を含む一つの集合が得られます。
<!--/-->

```agda
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset-mono )
open import L.Ordinal {ℓ} using ( boundingOrd )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
```

<!--en-->
Replacement in `L` applies to an arbitrary formula of the required arity. At this point no additional proof that the formula is Δ₀, or that all of its constants lie in a chosen stage, is required from the caller; those issues were handled in the proof of the general replacement theorem. Paths between dependent pairs with propositional second components will express the uniqueness of values.
<!--zh-->
`L` 中的替换适用于具有所需元数的任意公式。在这里调用它时，无需另外证明公式是 Δ₀，也无需证明其全部常元位于某个预先选定的层；这些问题已经在一般替换定理的证明中处理。第二分量为命题的依值对之间的路径，将用来表达取值的唯一性。
<!--ja-->
`L` の置換は、必要な項数をもつ任意の論理式に適用できます。ここでそれを用いる側は、論理式が Δ₀ であることや、すべての定数が選んだ段階に属することを別に証明する必要はありません。それらは一般の置換定理の証明で処理されています。第二成分が命題である依存対の間のパスを用いて、値の一意性を表します。
<!--/-->

```agda
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Full {ℓ} lem using ( hasReplacementL )

open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.Prelude using ( isPropIsContr )
import Cubical.HITs.PropositionalTruncation as PT
```

<!--en-->
For a predicate on the constructible carrier, `SetOf` is the type of a set together with a membership specification realizing that predicate. This is the form in which replacement returns the value range. Propositional truncation records an originating index without choosing one.
<!--zh-->
对可构造论域上的谓词，`SetOf` 表示一个集合连同一条成员关系规格，说明该集合实现这个谓词。替换以这种形式返回值域。命题截断记录某个来源索引的存在，而不选定其中一个。
<!--ja-->
構成可能な領域上の述語に対して、`SetOf` は、その述語を実現する集合と所属の仕様からなる型です。置換はこの形で値域を返します。命題的切り詰めは、元となる添字の存在を、特定の一つを選ばずに記録します。
<!--/-->

```agda
open PT using ( ∣_∣₁; ∥_∥₁ )

open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )

```

<!--en-->
The satisfaction notation below is the semantics of formulas in `𝒮ʟ`. The general replacement theorem already connects this semantics with the stagewise argument used to prove replacement; this chapter uses the resulting theorem and does not assume that arbitrary formulas are absolute between `L` and the ambient hierarchy.
<!--zh-->
下文的满足记号表示公式在 `𝒮ʟ` 中的语义。一般替换定理已经把这一语义与证明替换时采用的逐层论证联系起来；本章使用所得定理，并不假定任意公式在 `L` 与外围层级之间绝对。
<!--ja-->
以下の充足記号は、`𝒮ʟ` における論理式の意味論を表します。一般の置換定理は、この意味論と置換の証明で用いた段階ごとの議論をすでに結びつけています。本章はその定理を用いるのであり、任意の論理式が `L` と周囲の階層の間で絶対的だと仮定するものではありません。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## What a recursion has to supply

Three things. The **domain** is the index set, itself an element of the model, so the indices are sets of `L` and the whole index is one set. The **graph** is a formula in two variables, value first and index second, in the order the model's replacement field states. Its constants may be any elements of `L`, so a recursion that reads an already-internalized table names that table here; there is no complexity bound and no bound on where its constants live.
<!--zh-->
## 递归须提供什么

三样东西。**定义域**是索引集，它自己是模型中的元素；因此各个索引都是 `L` 的集合，整个索引集也是一个集合。**图**是二元公式，值在前、索引在后，与模型替换字段所用的次序一致。公式的常元可以是 `L` 的任意元素，读取已内化表的递归就在此处指名那张表；既无复杂度上界，也不限制常元所属的层。
<!--ja-->
## 再帰が与えるべきもの

三つです。**定義域**は添字の集合であり、それ自身モデルの要素です。したがって各添字は `L` の集合であり、添字全体も一つの集合です。**グラフ**は二変数の論理式で、値が先、添字が後という、モデルの置換のフィールドと同じ順です。その定数は `L` の任意の要素でよく、すでに内部化された表を読む再帰は、ここでその表を名指します。複雑さの上限も、定数の属する段階の制限もありません。
<!--/-->

```agda
record Recursion : Type (ℓ-suc (ℓ-suc ℓ)) where
  field
    dom   : S
    graph : Formula S 2
```

<!--en-->
**Functionality** here includes both existence and uniqueness. At every index in the domain, the type of a value paired with a proof that it satisfies the graph must be contractible. Its centre supplies a value, while the contraction proves that every other satisfying value agrees with it.
<!--zh-->
这里的**函数性**同时包含存在性与唯一性。对定义域中的每个索引，一个取值连同其满足图的证明所成的类型必须是可缩的。其中心给出取值，而收缩则证明其他任何满足图的取值都与它相同。
<!--ja-->
ここでの**関数性**は、存在と一意性の両方を含みます。定義域の各添字で、値と、それがグラフを満たす証明との対からなる型が可縮でなければなりません。その中心が値を与え、収縮が、グラフを満たす他の値はすべてそれと一致することを証明します。
<!--/-->

```agda
    funct : (x : S) → ⟨ x ∈ˢ dom ⟩
          → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ graph ⟩)
```

<!--en-->
The lemma `smallDom` gives a common containing set for a family `f : X → S` indexed by `X : Type ℓ`. It does not assert that this containing set is the exact image of `f`, nor does it by itself supply the domain of every recursion. When a larger stage is used as a domain, totality and uniqueness must still be proved at all of its members.
<!--zh-->
引理 `smallDom` 为一族 `f : X → S` 给出共同的包含集合，其中 `X : Type ℓ`。它并不声称该集合恰好是 `f` 的像，也不会自动给出每项递归的定义域。若采用更大的层作为定义域，仍须对其中所有成员证明取值存在且唯一。
<!--ja-->
補題 `smallDom` は、`X : Type ℓ` で添字づけられた族 `f : X → S` を共通に含む集合を与えます。その集合が `f` の像と一致するとは主張せず、すべての再帰の定義域を自動的に与えるものでもありません。より大きな段階を定義域に用いるなら、そのすべての要素で値の存在と一意性をなお証明する必要があります。
<!--/-->

```agda
smallDom : (X : Type ℓ) (f : X → S) → Σ[ d ∈ S ] ((x : X) → ⟨ f x ∈ˢ d ⟩)
smallDom X f = LsetS β oβ , mem
  where
```

<!--en-->
The bounding principle is applied to the stages of the values: each `f x` is constructible, so it appears at some stage, and the stages of all the `f x` lie below a single ordinal `β`. That ordinal, certified to be an ordinal, names the stage set used as the domain.
<!--zh-->
界定原理施加于取值的诸层：每个 `f x` 都可构造，故出现在某一层，而所有 `f x` 的层都低于单一序数 `β`。这个被证明为序数的序数，即指名用作定义域的层集。
<!--ja-->
界定の原理は値の段階に施します。各 `f x` は構成可能なのである段階に現れ、すべての `f x` の段階はただ一つの順序数 `β` の下にあります。順序数であることが証明されたこの順序数が、定義域として使う段階の集合を名指します。
<!--/-->

```agda
  b = boundingOrd X (λ x → stage (fst (f x)) (f x .snd))
        (λ x → stage-ord (fst (f x)) (f x .snd))
  β = b .fst
  oβ : IsOrd β
  oβ = b .snd .fst
```

<!--en-->
Membership then follows in two steps: each value appears at its own stage, and stages are monotone, so a value below `β` in the stage order is a member of the stage at `β`. Every `f x` is thus an element of the domain set.
<!--zh-->
隶属随后分两步得到：每个取值出现在自己的层，而层是单调的，故在层序中低于 `β` 的取值是 `β` 处那个层的成员。于是每个 `f x` 都是该定义域集合的元素。
<!--ja-->
所属は二段階で従います。各値は自分の段階に現れ、段階は単調なので、段階の順序で `β` より下にある値は `β` における段階の要素です。こうしてすべての `f x` が定義域の集合の要素になります。
<!--/-->

```agda
  mem : (x : X) → ⟨ f x ∈ˢ LsetS β oβ ⟩
  mem x = Lset-mono {α = β} {β = stage (fst (f x)) (f x .snd)} (b .snd .snd x)
            (stage-mem (fst (f x)) (f x .snd))
```

<!--en-->
## The value range

For a recursion `R`, let `Image y` mean that some index `x` belongs to the domain and the graph relates `x` to `y`. The existential is propositionally truncated, so it records only that `y` occurs as a value. Replacement realizes this predicate as a set; it does not construct a set of index-value pairs.
<!--zh-->
## 值域

对递归 `R`，令 `Image y` 表示存在定义域中的索引 `x`，使图把 `x` 与 `y` 联系起来。这个存在被命题截断，因此只记录 `y` 作为取值出现。替换把这一谓词实现为集合，并不构造索引与取值的有序对集合。
<!--ja-->
## 値域

再帰 `R` に対して、`Image y` を、定義域に属する添字 `x` が存在してグラフが `x` と `y` を関係づけること、とします。この存在は命題的に切り詰められるので、`y` が値として現れることだけを記録します。置換はこの述語を集合として実現し、添字と値の対の集合を作るわけではありません。
<!--/-->

```agda
module Of (R : Recursion) where
  open Recursion R public

  private
    Image : S → hProp (ℓ-suc ℓ)
    Image y = ∃[ x ∶ S ] (x ∈ˢ dom) ⊓ ((y ∷ x ∷ []) ⊨ graph)

```

<!--en-->
Applying replacement to the domain, graph, and functionality proof yields a set realizing `Image`. The result contains both the value-range set and the exact proposition describing membership in it.
<!--zh-->
把替换应用于定义域、图和函数性证明，便得到实现 `Image` 的集合。结果同时包含值域集合，以及准确描述其成员关系的命题。
<!--ja-->
定義域、グラフ、関数性の証明に置換を適用すると、`Image` を実現する集合が得られます。その結果は、値域の集合と、そこへの所属を正確に記述する命題の両方を含みます。
<!--/-->

```agda
    r : SetOf Image
    r = hasReplacementL dom graph funct .fst

```

<!--en-->
The value range is the first component of this result. Its membership specification states that `y` belongs to it exactly when there merely exists an index in the domain at which the graph has value `y`.
<!--zh-->
值域是这一结果的第一分量。其成员关系规格说明：`y` 属于值域，当且仅当仅仅存在定义域中的某个索引，使图在该处取值 `y`。
<!--ja-->
値域はこの結果の第一成分です。その所属の仕様は、定義域のある添字でグラフが値 `y` をとることが単に存在するとき、かつそのときに限り `y` が値域に属する、と述べます。
<!--/-->

```agda
  table : S
  table = r .fst

  table-mem : (y : S) → (y ∈ˢ table) ≡ Image y
  table-mem = r .snd

```

<!--en-->
The two directions of the specification are useful separately. A concrete graph witness places its value in the range. Conversely, membership in the range yields only the truncated existence of an originating index and graph witness; it does not choose that index.
<!--zh-->
这条规格的两个方向可以分别使用。具体的图见证把相应取值放入值域；反过来，值域中的成员只给出来源索引及图见证的截断存在性，并不选定该索引。
<!--ja-->
仕様の二つの向きは別々に利用できます。具体的なグラフの証人から、その値が値域に属することが従います。逆に、値域への所属から得られるのは、元となる添字とグラフの証人の切り詰められた存在だけであり、その添字を選ぶことはできません。
<!--/-->

```agda
  table-in : (x y : S) → ⟨ x ∈ˢ dom ⟩ → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩
           → ⟨ y ∈ˢ table ⟩
  table-in x y x∈ h = subst ⟨_⟩ (sym (table-mem y)) ∣ x , (x∈ , h) ∣₁

  table-out : (y : S) → ⟨ y ∈ˢ table ⟩ → ⟨ Image y ⟩
  table-out y h = subst ⟨_⟩ (table-mem y) h

```

<!--en-->
Functionality also determines a metatheoretic value at every member of the domain: it is the first component of the contraction centre. Any other `y` satisfying the graph at the same index is equal to this value, by the contraction supplied in the recursion data.
<!--zh-->
存在唯一性还为定义域的每个成员确定一个元理论取值，即可缩类型中心的第一分量。若另一个 `y` 在同一索引处满足图，则递归数据给出的收缩证明它等于该取值。
<!--ja-->
関数性は、定義域の各要素におけるメタ理論上の値も定めます。それは可縮な型の中心の第一成分です。同じ添字で別の `y` がグラフを満たすなら、再帰データが与える収縮によってこの値と等しくなります。
<!--/-->

```agda
  val : (x : S) → ⟨ x ∈ˢ dom ⟩ → S
  val x x∈ = funct x x∈ .fst .fst

  val-uniq : (x : S) (x∈ : ⟨ x ∈ˢ dom ⟩) (y : S)
           → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩ → val x x∈ ≡ y
  val-uniq x x∈ y h = cong fst (funct x x∈ .snd (y , h))

```

<!--en-->
## From unique existence to functionality

Some constructions naturally prove only that a unique graph value merely exists. The lemma `mereFunct` converts this propositionally truncated unique-existence statement into the contractibility required by `Recursion`. It makes no decidability assumption and does not choose a value independently of its uniqueness proof.
<!--zh-->
## 从唯一存在到函数性

有些构造自然得到的只是：满足图的唯一取值仅仅存在。引理 `mereFunct` 把这一命题截断的唯一存在陈述转换成 `Recursion` 所需的可缩性。它不假定可判定性，也不会脱离唯一性证明另行选择取值。
<!--ja-->
## 一意存在から関数性へ

構成によっては、グラフを満たす一意な値が単に存在することだけが自然に得られます。補題 `mereFunct` は、この命題的に切り詰められた一意存在を、`Recursion` が要求する可縮性へ変換します。決定可能性を仮定せず、一意性の証明とは独立に値を選ぶこともありません。
<!--/-->

```agda
mereFunct : (graph : Formula S 2) (x : S)
          → ∥ (Σ[ y ∈ S ] (⟨ (y ∷ x ∷ []) ⊨ graph ⟩
                          × ((y' : S) → ⟨ (y' ∷ x ∷ []) ⊨ graph ⟩ → y' ≡ y))) ∥₁
          → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ graph ⟩)
```

<!--en-->
Because contractibility is a proposition, the truncation may be eliminated into this goal. A representative unique value supplies the contraction centre, and its uniqueness clause identifies every other pair with that centre; the propositional graph component then determines the full dependent-pair equality.
<!--zh-->
由于可缩性是命题，可以把截断消去到这一目标。一个代表性的唯一取值给出收缩中心，其唯一性条款把其他每个对子与中心等同；图的证明分量是命题，因而取值的等式即可确定整个依值对的等式。
<!--ja-->
可縮性は命題なので、切り詰めをこの目標へ消去できます。一つの一意な値が収縮の中心を与え、その一意性の条項が他の各対を中心と同一視します。グラフの証明成分は命題なので、値の等式から依存対全体の等式が定まります。
<!--/-->

```agda
mereFunct graph x = PT.rec isPropIsContr
  (λ { (y , (hy , uniq)) → (y , hy)
     , (λ { (y' , hy') → Σ≡Prop (λ w → snd ((w ∷ x ∷ []) ⊨ graph))
                           (sym (uniq y' hy')) }) })
```

<!--en-->
## Starting from a metatheoretic function

The `Definition` form is convenient when a total function `fn : S → S` is already available in the metatheory. Besides a domain and a graph formula, it asks for proofs that the formula holds of `fn x` on the domain and that every value admitted by the formula equals `fn x`.
<!--zh-->
## 从元理论函数出发

若元理论中已经有全函数 `fn : S → S`，采用 `Definition` 形式较为方便。除定义域与图公式外，它还要求证明：在定义域上，公式对 `fn x` 成立，并且公式允许的每个取值都等于 `fn x`。
<!--ja-->
## メタ理論の関数から始める

メタ理論に全域関数 `fn : S → S` がすでにある場合には、`Definition` の形が便利です。定義域とグラフの論理式に加え、定義域上で論理式が `fn x` について成り立つこと、また論理式が許す各値が `fn x` に等しいことを証明します。
<!--/-->

```agda
record Definition : Type (ℓ-suc (ℓ-suc ℓ)) where
  field
    dom     : S
    fn      : S → S
    graph   : Formula S 2
```

<!--en-->
Saying that the formula defines the function is two implications. One says the formula holds of the function's own value at each index. The other says nothing else satisfies it: any value the graph admits at an index equals the function's value there. Together they are the two directions of graph adequacy.
<!--zh-->
说「公式定义了函数」，就是两条蕴含。一条说该公式在函数自身的取值处、对每个索引成立。另一条说别无他物满足它：图在某索引处允许的任何取值都等于函数在该处的值。二者合起来就是图公式充分性的两个方向。
<!--ja-->
論理式が関数を定義する、と言うのは二つの含意です。一つは、各添字でその論理式が関数自身の値について成り立つこと。もう一つは、他に満たすものがないこと、すなわちグラフがある添字で許すどんな値も、そこでの関数の値と等しいこと。両者合わせて、グラフの妥当性の二方向です。
<!--/-->

```agda
    defines : (x : S) → ⟨ x ∈ˢ dom ⟩ → ⟨ (fn x ∷ x ∷ []) ⊨ graph ⟩
    only    : (x : S) → ⟨ x ∈ˢ dom ⟩ → (y : S)
            → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩ → y ≡ fn x

```

<!--en-->
These two implications determine a recursion structure. Its domain and graph are inherited unchanged; the remaining task is to prove that the graph-value fiber is contractible at every point of the domain.
<!--zh-->
这两条蕴含确定一个递归结构。定义域与图原样保留，余下只需证明：对定义域的每一点，满足图的取值所成的纤维都是可缩的。
<!--ja-->
この二つの含意から再帰構造が定まります。定義域とグラフはそのまま受け継がれ、残るのは、定義域の各点でグラフを満たす値のファイバーが可縮であることの証明です。
<!--/-->

```agda
asRecursion : Definition → Recursion
asRecursion D = record
  { dom   = D.dom
  ; graph = D.graph
```

<!--en-->
Functionality is derived, not assumed. The centre is the pair of the function's value and the proof that the graph holds of it. Any competing pair is identified with the centre through the second implication, which forces its value to equal the function's; the identification is transported across the pair, whose satisfaction component is a proposition. Thus the graph-value fiber is contractible on the stated domain.
<!--zh-->
函数性是导出的，不是假设的。中心是「函数的取值连同图对它成立的证明」这一对子。任何竞争的对子都经第二条蕴含被等同于中心，因为那条蕴含迫使它的取值等于函数的取值；该同一视沿对子搬运，而其满足分量是命题。因此，在指定定义域上，图的取值纤维是可缩的。
<!--ja-->
関数性は仮定されるのではなく、導かれます。中心は、関数の値と、グラフがそれについて成り立つことの証明の対です。競合する対は、第二の含意を通して中心と同一視されます。その含意が、対の値を関数の値に等しく強めるからです。同一視は対に沿って輸送され、その充足の成分は命題です。したがって、指定した定義域上でグラフの値のファイバーは可縮です。
<!--/-->

```agda
  ; funct = λ x x∈ → (D.fn x , D.defines x x∈)
          , λ { (y , h) → Σ≡Prop (λ w → snd ((w ∷ x ∷ []) ⊨ D.graph))
                            (sym (D.only x x∈ y h)) } }
  where module D = Definition D
```

<!--en-->
## The image of a definable function

Applying the preceding conversion to a `Definition` produces its value range as a set of `L`. The function remains a metatheoretic description, while the graph formula and replacement certify that all of its values over the stated domain form an internal set.
<!--zh-->
## 可定义函数的像

把前述转换应用于一个 `Definition`，便得到其值域作为 `L` 中的集合。函数仍是元理论中的描述，而图公式与替换共同证明：它在指定定义域上的全部取值组成内部集合。
<!--ja-->
## 定義可能な関数の像

先の変換を `Definition` に適用すると、その値域が `L` の集合として得られます。関数はメタ理論上の記述のままですが、グラフの論理式と置換により、指定した定義域上のすべての値が内部集合をなすことが証明されます。
<!--/-->

```agda
module Image (D : Definition) where
  open Definition D public
  private
    module R = Of (asRecursion D)

```

<!--en-->
The module exposes this range under the name `table`. No separate membership lemmas are re-exported here; when their full specification is needed, it remains the one proved for the underlying `Recursion`.
<!--zh-->
该模块以 `table` 为名给出这个值域。这里没有另外导出成员关系引理；需要完整规格时，仍使用底层 `Recursion` 已经证明的那一份。
<!--ja-->
このモジュールは、この値域を `table` という名で与えます。ここでは所属に関する補題を別に公開しません。完全な仕様が必要なら、基礎となる `Recursion` について証明されたものを用います。
<!--/-->

```agda
  table : S
  table = R.table

```

<!--en-->
## Scope of the construction

The result applies when three obligations are met: the domain is a set of `L`; the relation is expressed by a two-variable formula over the constructible structure; and it has a unique value at every point of that domain. The `Definition` form proves the last condition from a total metatheoretic function and two adequacy implications. The helper `smallDom` can supply a common containing stage for a `Type ℓ`-indexed family, but using that stage as the domain still requires functionality on every additional member.

No complexity bound on the graph formula or stage-locality certificate for its constants is required at this point. This convenience comes from the already proved general replacement theorem; it does not assert that arbitrary formulas are absolute, and each application must still provide the formula and its adequacy proof.
<!--zh-->
## 构造的适用范围

这项结果要求满足三项条件：定义域是 `L` 中的集合；关系由可构造结构上的二元公式表达；它在定义域的每一点具有唯一取值。`Definition` 形式从一个元理论全函数及两条充分性证明导出最后一项。辅助引理 `smallDom` 可以为由 `Type ℓ` 中类型索引的一族元素给出共同的包含层，但若把该层用作定义域，仍须对其中新增的每个成员证明存在唯一性。

在此处调用替换时，无须限制图公式的复杂度，也无须另交常元位于同一层的证书。这一便利来自已经证明的一般替换定理；它并不声称任意公式都是绝对的，而且每次应用仍须给出公式及其充分性证明。
<!--ja-->
## 構成の適用範囲

この結果には三つの条件があります。定義域が `L` の集合であること、関係が構成可能構造上の二変数の論理式で表されること、そして定義域の各点で値が一意に存在することです。`Definition` の形では、メタ理論上の全域関数と二つの妥当性の証明から最後の条件を導きます。補題 `smallDom` は、`Type ℓ` の型で添字づけられた族に共通の包含段階を与えますが、その段階を定義域にするなら、余分な各要素についても関数性を証明しなければなりません。

ここで置換を用いる際には、グラフの論理式の複雑さを制限したり、定数が同じ段階に属することを別に証明したりする必要はありません。この利便性は、すでに証明された一般の置換定理によるものです。任意の論理式が絶対的だと主張するものではなく、各適用ではなお論理式とその妥当性の証明を与える必要があります。
<!--/-->

<!--en-->
## Recap

Replacement turns a functional formula on an internal domain into its value range in `L`. A `Recursion` states functionality directly as contractibility; `mereFunct` derives it from truncated unique existence; and `Definition` derives it from a total metatheoretic function together with the two directions of graph adequacy. The resulting set records which values occur, while the graph formula continues to record which index produces which value.
<!--zh-->
## 小结

替换把内部定义域上的函数性公式转换成 `L` 中的值域。`Recursion` 直接以可缩性陈述存在唯一性；`mereFunct` 从截断的唯一存在导出可缩性；`Definition` 则从元理论全函数以及图公式充分性的两个方向导出它。所得集合记录哪些取值出现，而哪个索引产生哪个取值仍由图公式记录。
<!--ja-->
## まとめ

置換は、内部の定義域上の関数的な論理式を `L` の値域へ変えます。`Recursion` は関数性を可縮性として直接述べ、`mereFunct` は切り詰められた一意存在からそれを導き、`Definition` はメタ理論上の全域関数とグラフの妥当性の二方向からそれを導きます。得られる集合はどの値が現れるかを記録し、どの添字がどの値を生むかは引き続きグラフの論理式が記録します。
<!--/-->

<!--en-->
# ω-recursion inside the constructible universe

A definable step on constructible sets and a starting point determine, by recursion on the host natural numbers, a sequence of finite iterates. This chapter represents each iterate inside `L`: finite correct tables establish existence and uniqueness at the internal numerals, replacement gathers their values and their indexed graph, and union forms the set containing every member reached at a finite stage.
<!--zh-->
# 可构造宇宙中的 ω 递归

可构造集合上的可定义步骤与一个起点，通过宿主自然数上的递归确定一列有限次迭代。本章在 `L` 内表示每次迭代：有限的正确表证明内部数码处取值的存在性与唯一性，替换收集这些值及其带索引的图，并集则组成包含每个有限阶段所得成员的集合。
<!--ja-->
# 構成可能宇宙における ω 再帰

構成可能集合上の定義可能な操作と始点から、ホスト側の自然数に関する再帰によって有限反復の列が定まります。本章では各反復を `L` の内部で表します。有限な正しい表によって内部の数項における値の存在と一意性を示し、置換によって値と添字付きグラフを集め、和集合によって有限段階で得られるすべての要素を含む集合を作ります。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

```

<!--en-->
The base library is opened, and excluded middle is received as an explicit hypothesis, in the standing form of the book.
<!--zh-->
打开基础库，并以全书一贯形式将排中律作为显式假设引入。
<!--ja-->
基礎ライブラリを開き、本書の常の形式に従って、排中律を明示的な仮定として受け取ります。
<!--/-->

```agda
open import Base.Prelude
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
open import Base.Classical using ( LEM )

```

<!--en-->
The module fixes the universe level and names the classical hypothesis: every theorem below records exactly which level instance of excluded middle it consumes.
<!--zh-->
模块固定宇宙层级并命名经典假设：下文每条定理都准确记录它消耗哪个层级的排中律实例。
<!--ja-->
モジュールは宇宙レベルを固定し、古典的な仮定に名前を与えます。以下の各定理は、どのレベルの排中律の実例を消費するかを正確に記録します。
<!--/-->

```agda
module L.GCH.OmegaRecursion {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

```

<!--en-->
The description of the iteration is written in the object language, whose formulas use equality, conjunction, implication, and the unbounded existential and universal quantifiers; formula renaming and absoluteness support reading the same formula under different environments.
<!--zh-->
迭代的描述用对象语言书写：公式由相等、合取、蕴涵以及无界存在与全称量词构成；公式改名与绝对性支持同一公式在不同环境下的读取。
<!--ja-->
反復の記述は対象言語で書かれます。論理式は等号・連言・含意、そして非有界の存在と全称の量化子から作られ、論理式の改名と絶対性が、同じ論理式を異なる環境のもとで読むことを支えます。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _⇒̇_; ∃̇_; ∀̇_ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
import FOL.Absoluteness
```

<!--en-->
The ambient hierarchy supplies membership and the numerals, ordered pairs have injective components, and the constructible structure carries the stage machinery with its transitivity and monotonicity.
<!--zh-->
外围层级供给隶属与数码，有序对的分量可单射恢复，可构造结构承载层机制及其传递性与单调性。
<!--ja-->
周囲の階層が所属と数項を供給し、順序対の成分は単射に復元でき、構成可能な構造が段階の仕組みとその推移性・単調性を運びます。
<!--/-->

```agda
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj )
open import V.Model {ℓ} using ( pair-spec; union-spec; self∈sucV )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( #∈ω; ∈#-elim; boundingOrd )
```

<!--en-->
To turn a host sequence into sets of `L`, we need four internal constructions: stages that bound constructibility, finite sets that hold approximating tables, coded ordered pairs and unions, and the set `ωʟ` of internal natural numbers. Together they let the later argument pass from one finite table for each host index to a single range and graph indexed inside the model.
<!--zh-->
要把宿主序列化为 `L` 中的集合，需要四类内部构造：为可构造性提供界的层、容纳近似表的有限集、码化有序对与并，以及内部自然数集 `ωʟ`。借助这些构造，后文可从每个宿主指标各自的一张有限表，过渡到模型内部带索引的单一值域与图。
<!--ja-->
ホスト側の列を `L` の集合として表すには、構成可能性に上界を与える段階、近似表を収める有限集合、符号化された順序対と和集合、そして内部自然数集合 `ωʟ` が必要です。これらにより、各ホスト添字に対する有限表から、モデル内部で添字付けられた一つの値域とグラフへ移ることができます。
<!--/-->

```agda
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Axioms.Basic {ℓ} using ( finSet; finSet-in; finSet-out; module FinOf )
open import L.Axioms.Numerals {ℓ}
  using ( pairʟ; pairʟ-fst; unionʟ; unionʟ-fst )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
```

<!--en-->
The recursion interface packages an internally definable, uniquely valued relation on an internal domain. Its graph construction and the coding formulas for application, ordered pairs, and set-theoretic successor will later turn the semantic finite-table argument into a first-order relation over `L` and then into actual sets of `L`.
<!--zh-->
递归接口把内部定义域上可在内部定义且取值唯一的关系打包起来。相应的图构造，以及表示应用、有序对和集合论后继的编码公式，稍后会把有限表的语义论证化为 `L` 上的一阶关系，再化为 `L` 中的实际集合。
<!--ja-->
再帰のインターフェースは、内部の定義域上で内部的に定義でき、値が一意である関係をまとめます。そのグラフ構成と、適用・順序対・集合論的後続を表す符号化論理式によって、後で有限表の意味論的な議論を `L` 上の一階の関係へ、さらに `L` の実際の集合へ移します。
<!--/-->

```agda
open import L.Recursion {ℓ} lem using ( Recursion; module Of; mereFunct )
open import L.Recursion.Graph {ℓ} lem using () renaming ( module Graph to RecursionGraph )
open import L.Coding.Model {ℓ} using ( appAt; appAt-adequate; prʟ; prʟ-fst )
open import L.Coding.Expressions {ℓ} using ( sucAtL; sucAtL-adequate; numL )

```

<!--en-->
The arithmetic of natural numbers, their bounded indices, and the conversions between bounded indices and numerals support the finite bookkeeping of the chapter.
<!--zh-->
自然数序、有界索引，以及有界索引与数码之间的转换，支撑本章的有限簿记。
<!--ja-->
自然数の順序、有界の索引、そして有界の索引と数項の間の変換が、この章の有限の簿記を支えます。
<!--/-->

```agda
open import Cubical.Data.Nat.Order
  using ( _≤_; ≤-refl; ≤-trans; <-weaken; pred-≤-pred; suc-≤-suc )
open import Cubical.Data.FinData.Properties using ( toℕ<n; fromℕ'; toFromId' )
```

<!--en-->
Several identifications below live in dependent pairs: an underlying set is accompanied by a propositional proof of constructibility. The h-set structure of the cumulative hierarchy makes equalities between underlying sets propositions, while sums and two-variable transport handle the alternatives and simultaneous substitutions arising when coded pairs are decoded.
<!--zh-->
下文若干同一视发生在依值对中：底层集合附带一个证明其可构造的命题。累积层级的 h-集合结构保证底层集合之间的等式是命题；和类型与二元搬运则处理解码有序对时出现的分支及同步代换。
<!--ja-->
以下のいくつかの同一視は依存対の中で行われます。台となる集合には、その構成可能性を示す命題が伴います。累積階層の h-集合構造により台集合の間の等式は命題となり、直和と二変数の輸送が、符号化された対を読み解く際の分岐と同時代入を扱います。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
```

<!--en-->
The successor operation of the hierarchy and the truncation machinery complete the constructions.
<!--zh-->
层级的后继运算与截断机制补全各构造。
<!--ja-->
階層の後続の演算と切り詰めの仕組みが、構成を完成させます。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV; #_ )

```

<!--en-->
The constructible carrier is opened with its membership, since every iterate is an element of `L`.
<!--zh-->
可构造载体连同其隶属被打开，因为每次迭代都是 `L` 的元素。
<!--ja-->
構成可能な台がその所属とともに開かれます。それぞれの反復は `L` の要素だからです。
<!--/-->

```agda
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

```

<!--en-->
The absoluteness reading is imported under two names, for formulas read inside `L` at environments.
<!--zh-->
绝对性读法以两个名字引入，用于在 `L` 内部于环境处读取公式。
<!--ja-->
絶対性の読みは二つの名前で導入され、`L` の内部で環境のもとで論理式を読むために使われます。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
The renaming semantics is instantiated under the identity of constant alphabets, so a renamed formula is read in an environment with its slots rearranged.
<!--zh-->
改名语义在恒等常元字母表下实例化，于是被改名的公式可在槽位重排后的环境中读取。
<!--ja-->
改名の意味論は、定数のアルファベットをそのままにして具体化されます。これにより、名前を替えた論理式を、枠を並べ替えた環境のもとで読めます。
<!--/-->

```agda
module Ren = Sat 𝒮ʟ id

```

<!--en-->
The carrier is an h-set, since the hierarchy is an h-set and constructibility is propositional; equalities of constructible sets are therefore propositions.
<!--zh-->
载体是 h-集合，因为层级是 h-集合且可构造性是命题；因此可构造集合之间的相等是命题。
<!--ja-->
台は h-集合です。階層が h-集合であり、構成可能性が命題だからです。したがって構成可能な集合の間の等式は命題になります。
<!--/-->

```agda
isSetS : isSet S
isSetS = isSetΣSndProp setIsSet (λ v → snd (isL v))

```

<!--en-->
Equal underlying sets make equal constructible sets, by the propositionhood of the constructibility proof. This conversion is used whenever an equality has first been obtained at the level of underlying sets.
<!--zh-->
底层集合相等即可构造集合相等，依据是可构造性证明的命题性。每当等式先在底层集合层面获得时，就使用这一转换。
<!--ja-->
底の集合が等しければ構成可能な集合も等しくなります。構成可能性の証明が命題だからです。等式がまず底の集合の水準で得られたとき、いつでもこの変換を使います。
<!--/-->

```agda
S≡ : {x y : S} → fst x ≡ fst y → x ≡ y
S≡ = Σ≡Prop (λ v → snd (isL v))
```

<!--en-->
A coded graph records the input first and the value second: `Holds F x y` means that the ordered pair `(x,y)` belongs to `F`, at the level of underlying sets. Formula environments use the opposite list order, so the step relation at input `x` and output `y` is read under `(y ∷ x ∷ [])`.
<!--zh-->
编码图先记录输入、再记录值：`Holds F x y` 表示有序对 `(x,y)` 在底层集合层面属于 `F`。公式环境中的列表次序相反，因此输入为 `x`、输出为 `y` 的步进关系在 `(y ∷ x ∷ [])` 环境下读取。
<!--ja-->
符号化されたグラフは入力を先、値を後に記録します。`Holds F x y` は、台集合の水準で順序対 `(x,y)` が `F` に属することを意味します。論理式の環境ではリストの順序が逆になるため、入力 `x`、出力 `y` のステップ関係は `(y ∷ x ∷ [])` のもとで読みます。
<!--/-->

```agda
Holds : S → S → S → Type (ℓ-suc ℓ)
Holds F x y = ⟨ pr (fst x) (fst y) ∈ fst F ⟩
```

<!--en-->
The constructible numeral of `k` packages the ambient numeral with its constructibility; numerals are the indices at which the iterates will be recorded.
<!--zh-->
自然数 `k` 的可构造数码把外围数码连同其可构造性打包；数码正是各次迭代将被记录的位置。
<!--ja-->
自然数 `k` の構成可能な数項は、周囲の数項にその構成可能性を対にしたものです。数項こそ、反復が記録される位置です。
<!--/-->

```agda
nn : ℕ → S
nn k = # k , numL k
```

<!--en-->
An element enters the internal unordered pair `pairʟ a b` once its underlying set is identified with the underlying set of either `a` or `b`. The proof transports this alternative through the equation identifying the underlying set of `pairʟ a b` with the ambient unordered pair.
<!--zh-->
若一个元素的底层集合与 `a` 或 `b` 的底层集合相等，它便属于内部无序对 `pairʟ a b`。证明沿一条等式搬运这一二择分支；该等式把 `pairʟ a b` 的底层集合与外围无序对认同起来。
<!--ja-->
ある要素の台集合が `a` または `b` の台集合と等しければ、その要素は内部の非順序対 `pairʟ a b` に属します。証明では、`pairʟ a b` の台集合を周囲の非順序対と同一視する等式に沿って、この二つの場合を輸送します。
<!--/-->

```agda
pairʟ-in : (a b y : S) → (fst y ≡ fst a) ⊎ (fst y ≡ fst b) → ⟨ y ∈ˢ pairʟ a b ⟩
pairʟ-in a b y k = subst (λ w → ⟨ fst y ∈ w ⟩) (sym (pairʟ-fst a b))
  (subst ⟨_⟩ (sym (pair-spec (fst a) (fst b) (fst y))) ∣ k ∣₁)

```

<!--en-->
To place `y` in the internal union of `A`, it suffices to exhibit a particular constructible set `B` with `B ∈ A` and `y ∈ B`. The two memberships form the usual witness for membership in a union and are transported through the underlying-set equation for `unionʟ A`.
<!--zh-->
要把 `y` 放入 `A` 的内部并，只需给出一个明确的可构造集合 `B`，满足 `B ∈ A` 且 `y ∈ B`。这两条隶属构成并集隶属的通常见证，再沿 `unionʟ A` 的底层集合等式搬运。
<!--ja-->
`y` を `A` の内部和集合に入れるには、`B ∈ A` かつ `y ∈ B` を満たす具体的な構成可能集合 `B` を示せば十分です。この二つの所属が和集合への所属の通常の証人となり、`unionʟ A` の台集合に関する等式に沿って輸送されます。
<!--/-->

```agda
unionʟ-in : (A y B : S) → ⟨ fst B ∈ fst A ⟩ → ⟨ fst y ∈ fst B ⟩ → ⟨ y ∈ˢ unionʟ A ⟩
unionʟ-in A y B hB hy = subst (λ w → ⟨ fst y ∈ w ⟩) (sym (unionʟ-fst A))
  (subst ⟨_⟩ (sym (union-spec (fst A) (fst y))) ∣ fst B , (hB , hy) ∣₁)

```

<!--en-->
Membership in a union yields, merely, an intermediate set containing the element; the intermediate set is an ambient element, without a constructibility proof of its own.
<!--zh-->
并中的隶属仅仅给出包含该元素的某个中间集合；中间集合是外围元素，自身不带可构造性证明。
<!--ja-->
和の中の所属からは、その要素を含む中間の集合が単に得られます。中間の集合は周囲の要素であり、それ自身の構成可能性の証明は持ちません。
<!--/-->

```agda
unionʟ-out : (A y : S) → ⟨ y ∈ˢ unionʟ A ⟩
           → ∥ Σ[ B ∈ V ℓ ] (⟨ B ∈ fst A ⟩ × ⟨ fst y ∈ B ⟩) ∥₁
unionʟ-out A y h = subst ⟨_⟩ (union-spec (fst A) (fst y))
  (subst (λ w → ⟨ fst y ∈ w ⟩) (unionʟ-fst A) h)
```

<!--en-->
## Finite iterates of a definable step
<!--zh-->
## 可定义步骤的有限次迭代
<!--ja-->
## 定義可能な操作の有限反復
<!--/-->

<!--en-->
The iteration module receives the five ingredients of the whole chapter: a starting point, a step formula in the output-first input-second order, the actual step function, a proof that the formula defines the function everywhere, and a proof that only that value satisfies it. Totality over the whole carrier is part of the data.
<!--zh-->
迭代模块收取全章的五份材料：起点、按「输出在前输入在后」次序的步进公式、实际的步进函数、「公式处处定义该函数」的证明，以及「只有该值满足公式」的证明。在整个载体上的全域性是数据的一部分。
<!--ja-->
反復のモジュールは、この章の五つの材料を受け取ります。始点、出力が先で入力が後という順のステップの論理式、実際のステップ関数、その論理式がすべての点で関数を定義することの証明、そしてその値だけが充足することの証明です。台全体での全域性がデータの一部です。
<!--/-->

```agda
module Iterate (a : S) (stepFo : Formula S 2) (step : S → S)
               (defines : (x : S) → ⟨ (step x ∷ x ∷ []) ⊨ stepFo ⟩)
               (only : (x y : S) → ⟨ (y ∷ x ∷ []) ⊨ stepFo ⟩ → y ≡ step x) where

```

<!--en-->
The iteration sequence is a host-level recursion on the natural numbers: it starts at `a` and applies the step function to the previous value. At this stage it is only an Agda sequence; its internal representation is the work of the chapter.
<!--zh-->
迭代序列是宿主层面关于自然数的递归：从 `a` 出发，把步进函数作用于前值。此处它只是 Agda 序列；其内部表示才是本章的工作。
<!--ja-->
反復列は、自然数の上のホスト側の再帰です。`a` から始まり、前の値にステップ関数を適用します。この段階ではまだ Agda の列にすぎず、その内部での表現がこの章の仕事です。
<!--/-->

```agda
  it : ℕ → S
  it zero    = a
  it (suc n) = step (it n)
```

<!--en-->
The zero clause says that every value recorded at the zeroth numeral has the same underlying set as the starting point. It does not say that a value is recorded there.
<!--zh-->
零点子句说：在数码零处记录的每个值，其底层集都与起点相同。它并不声称零点处有值被记录。
<!--ja-->
ゼロの節は、数項ゼロのもとで記録されたすべての値の底の集合が、始点の底の集合と同じであることを言います。そこに値が記録されるとは言っていません。
<!--/-->

```agda
  Zero : S → Type (ℓ-suc ℓ)
  Zero F = (v : S) → Holds F (nn 0) v → fst v ≡ fst a

```

<!--en-->
The successor clause says that whenever the table records both `(x, v)` and `(x', v')` with the underlying set of `x'` the successor of that of `x`, the step relation holds between the two values.
<!--zh-->
后继子句说：只要表同时记录 `(x, v)` 与 `(x', v')`，且 `x'` 的底层集是 `x` 的后继，步进关系就在两个值之间成立。
<!--ja-->
後続の節は、表が `(x, v)` と `(x', v')` の両方を記録し、`x'` の底の集合が `x` のそれの後続であるなら、二つの値の間にステップの関係が成り立つ、と言います。
<!--/-->

```agda
  Step : S → Type (ℓ-suc ℓ)
  Step F = (x v x' v' : S) → Holds F x v → Holds F x' v'
         → fst x' ≡ sucV (fst x) → ⟨ (v' ∷ v ∷ []) ⊨ stepFo ⟩

```

<!--en-->
The downward clause says that below every recorded entry, a recorded value exists, merely. It is the domain-completion clause, and its conclusion is truncated because a witness is not chosen.
<!--zh-->
向下子句说：在每个被记录条目之下，仅仅地存在某个被记录的值。它是定义域的完备条款，其结论因未选定见证而是截断的。
<!--ja-->
下向きの節は、記録された項目の下では、記録された値が単に存在することを言います。これは定義域を完成させる条項であり、証人が選ばれないため、結論は切り詰められています。
<!--/-->

```agda
  Down : S → Type (ℓ-suc ℓ)
  Down F = (x' v' x : S) → Holds F x' v' → ⟨ fst x ∈ fst x' ⟩
         → ∥ Σ[ v ∈ S ] Holds F x v ∥₁

```

<!--en-->
A correct approximation is the conjunction of the three clauses. It is deliberately weaker than being a function graph: it fixes no exact domain and imposes no uniqueness.
<!--zh-->
正确近似是三条子句的合取。它刻意弱于「函数图的正确性」：既不固定精确定义域，也不施加唯一性。
<!--ja-->
正しい近似とは、三つの節の連言です。それは関数のグラフとしての正しさよりも意図的に弱く、正確な定義域も一意性も定めません。
<!--/-->

```agda
  Correct : S → Type (ℓ-suc ℓ)
  Correct F = Zero F × (Step F × Down F)
```

<!--en-->
The zero clause is written in the object language. It says that for every `z` equal to the zeroth numeral, and every value recorded there, that value equals the starting point.
<!--zh-->
零点子句写成对象语言公式：对每个等于数码零的 `z`，以及在 `z` 处记录的每个值，该值都等于起点。
<!--ja-->
ゼロの節は、対象言語で書かれます。数項ゼロと等しいすべての `z` と、そこに記録されたすべての値について、その値は始点と等しい、と言うのです。
<!--/-->

```agda
  opaque
    zeroAt : ∀ {n} → Fin n → Formula S n
    zeroAt f = ∀̇ ( (var zero ≐ con (nn 0))
                 ⇒̇ ∀̇ ( appAt (suc (suc f)) (suc zero) zero ⇒̇ (var zero ≐ con a) ) )

```

<!--en-->
Reading the zero clause applies it at the numeral zero and transports the application atom through its adequacy, producing the underlying-set equation of `Zero`.
<!--zh-->
读取零点子句即在数码零处应用它，并把应用原子经充分性搬运，得到 `Zero` 的底层集等式。
<!--ja-->
ゼロの節の読みは、数項ゼロのもとでそれを適用し、適用のアトムを妥当性に沿って運んで、`Zero` の底の集合の等式を産み出します。
<!--/-->

```agda
    zero-out : ∀ {n} (f : Fin n) (γ : S ^ n) → ⟨ γ ⊨ zeroAt f ⟩ → Zero (lookup f γ)
    zero-out f γ h v hv = h (nn 0) refl v
      (subst ⟨_⟩ (sym (appAt-adequate (suc (suc f)) (suc zero) zero (v ∷ nn 0 ∷ γ))) hv)

```

<!--en-->
Conversely, a host-level proof of the zero clause fills the object-language formula. The quantified set `z` is rewritten along the premise `z = nn 0`, and the graph membership at zero is transported into the application atom before the clause identifies its value with `a`.
<!--zh-->
反过来，宿主层的零点子句可填入对象语言公式。先沿前提 `z = nn 0` 改写被量化集合 `z`，再把零点处的图隶属搬入应用原子，最后由该子句把其值认同为 `a`。
<!--ja-->
逆に、ホスト側のゼロの節から対象言語の論理式を満たせます。量化された集合 `z` を前提 `z = nn 0` に沿って書き換え、ゼロにおけるグラフへの所属を適用のアトムへ輸送してから、その値を `a` と同一視します。
<!--/-->

```agda
    zero-in : ∀ {n} (f : Fin n) (γ : S ^ n) → Zero (lookup f γ) → ⟨ γ ⊨ zeroAt f ⟩
    zero-in f γ h z ez v hv = h v
      (subst (λ t → ⟨ pr t (fst v) ∈ fst (lookup f γ) ⟩) ez
        (subst ⟨_⟩ (appAt-adequate (suc (suc f)) (suc zero) zero (v ∷ z ∷ γ)) hv))
```

<!--en-->
The renaming of the step formula uses two slots: the first variable stays at position zero, and the second moves to position two, so that four quantified slots can surround the renamed body.
<!--zh-->
步进公式的改名使用两个槽位：第一个变元留在位置零，第二个移到位置二，从而四个被量化槽位可以环绕改名后的主体。
<!--ja-->
ステップの論理式の改名は、二つの枠を使います。最初の変数は位置ゼロにとどまり、二つ目は位置二へ動き、こうして四つの量化された枠が、名前を替えた本体を囲みます。
<!--/-->

```agda
  private
    ρ : ∀ {n} → Fin 2 → Fin (suc (suc (suc (suc n))))
    ρ zero       = zero
    ρ (suc zero) = suc (suc zero)

```

<!--en-->
The renaming agreement checks that the two environments agree on the renamed slots, which are the only positions the renamed formula reads.
<!--zh-->
改名一致检查两个环境在被改名槽位上一致，而这些正是改名公式读取的位置。
<!--ja-->
改名の一致は、二つの環境が、名前を替えられた枠のもとで一致することを確かめます。改名された論理式が読むのは、この位置だけです。
<!--/-->

```agda
    ag : ∀ {n} (γ : S ^ n) (x v x' v' : S)
       → Ren.Agrees ρ (v' ∷ x' ∷ v ∷ x ∷ γ) (v' ∷ v ∷ [])
    ag γ x v x' v' zero       = refl
    ag γ x v x' v' (suc zero) = refl

```

<!--en-->
The successor clause universally quantifies two table entries `(x,v)` and `(x',v')`. Its nested implications first assume that both entries occur in the table and then assume that the underlying index `x'` is the set-theoretic successor of `x`.
<!--zh-->
后继子句全称量化表中的两个条目 `(x,v)` 与 `(x',v')`。层层嵌套的蕴涵先假设两个条目都出现在表中，再假设指标 `x'` 的底层集合是 `x` 的集合论后继。
<!--ja-->
後続の節は、表の二つの項目 `(x,v)` と `(x',v')` を全称量化します。入れ子になった含意は、まず両方の項目が表に現れることを仮定し、次に添字 `x'` の台集合が `x` の集合論的後続であることを仮定します。
<!--/-->

```agda
  opaque
    stepAt : ∀ {n} → Fin n → Formula S n
    stepAt f = ∀̇ (∀̇ (∀̇ (∀̇ (
        appAt (suc (suc (suc (suc f)))) (suc (suc (suc zero))) (suc (suc zero))
      ⇒̇ ( appAt (suc (suc (suc (suc f)))) (suc zero) zero
```

<!--en-->
Under these three premises, the conclusion is the renamed step formula relating `v'` to `v`. Renaming selects the output and input slots from the four quantified variables, thereby connecting the finite table's adjacent rows to the original two-variable definition of `step`.
<!--zh-->
在这三项前提下，结论是把 `v'` 与 `v` 联系起来的改名步进公式。改名从四个被量化变元中选出输出槽与输入槽，从而把有限表的相邻两行连接到原来的二元 `step` 定义。
<!--ja-->
この三つの前提のもとで、結論は `v'` と `v` を関係づける改名済みのステップ論理式です。改名は四つの量化変数から出力と入力の位置を選び、有限表の隣り合う行を、元の二変数による `step` の定義へ結びます。
<!--/-->

```agda
      ⇒̇ ( sucAtL (suc (suc (suc zero))) (suc zero)
      ⇒̇ renameFo ρ stepFo ) ) ))))

```

<!--en-->
The renaming path is proved by the renaming semantics: satisfaction of the renamed formula at the long environment equals satisfaction of the original at the short one, because the two environments agree on the renamed slots.
<!--zh-->
改名路径由改名语义证明：改名公式在长环境处的满足等于原公式在短环境处的满足，因为两个环境在被改名槽位上一致。
<!--ja-->
改名のパスは、改名の意味論で証明されます。名前を替えた論理式の長い環境での充足は、もとの論理式の短い環境での充足と等しくなります。二つの環境が、替えられた枠のもとで一致しているからです。
<!--/-->

```agda
    private
      gr : ∀ {n} (γ : S ^ n) (x v x' v' : S)
         → ⟨ (v' ∷ x' ∷ v ∷ x ∷ γ) ⊨ renameFo ρ stepFo ⟩ ≡ ⟨ (v' ∷ v ∷ []) ⊨ stepFo ⟩
      gr γ x v x' v' = cong ⟨_⟩
        (Ren.⊨-rename ρ stepFo (v' ∷ x' ∷ v ∷ x ∷ γ) (v' ∷ v ∷ []) (ag γ x v x' v'))
```

<!--en-->
Reading the successor clause transports the two application atoms against their adequacy, applies the four quantifiers, and uses the renaming path.
<!--zh-->
读取后继子句逆着充分性搬运两个应用原子，应用四个全称量词，并使用改名路径。
<!--ja-->
後続の節の読みは、二つの適用のアトムを妥当性に逆らって運び、四つの全称量化子を適用し、改名のパスを使います。
<!--/-->

```agda

    step-out : ∀ {n} (f : Fin n) (γ : S ^ n) → ⟨ γ ⊨ stepAt f ⟩ → Step (lookup f γ)
    step-out f γ h x v x' v' p q s = transport (gr γ x v x' v')
      (h x v x' v'
        (subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc (suc f)))) (suc (suc (suc zero))) (suc (suc zero)) (v' ∷ x' ∷ v ∷ x ∷ γ))) p)
        (subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc (suc f)))) (suc zero) zero (v' ∷ x' ∷ v ∷ x ∷ γ))) q)
```

<!--en-->
The last premise recognizes `x'` as the set-theoretic successor of `x`. Together with the two table memberships, it is exactly the hypothesis needed to compare adjacent rows, so the semantic reading yields the step relation between their values.
<!--zh-->
最后一项前提将 `x'` 认作 `x` 的集合论后继。它与两条表隶属关系合在一起，恰好构成比较相邻两行所需的假设，因此语义读法给出两行取值之间的步进关系。
<!--ja-->
最後の前提は、`x'` が `x` の集合論的な後者であることを表す。二つの表所属と合わせると、これは隣接する行を比較するためにちょうど必要な仮定となり、意味論的な読みから二つの値の間のステップ関係が得られる。
<!--/-->

```agda
        (subst ⟨_⟩ (sym (sucAtL-adequate (suc (suc (suc zero))) (suc zero) (v' ∷ x' ∷ v ∷ x ∷ γ))) s))

```

<!--en-->
Filling the successor clause runs the same transports in reverse, starting from the host-level step instance.
<!--zh-->
填充后继子句从宿主层的步进实例出发，反向运行同样的搬运。
<!--ja-->
後続の節の埋めは、ホスト側のステップの実例から出発して、同じ輸送を逆向きに実行します。
<!--/-->

```agda
    step-in : ∀ {n} (f : Fin n) (γ : S ^ n) → Step (lookup f γ) → ⟨ γ ⊨ stepAt f ⟩
    step-in f γ h x v x' v' p q s = transport (sym (gr γ x v x' v'))
      (h x v x' v'
        (subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc f)))) (suc (suc (suc zero))) (suc (suc zero)) (v' ∷ x' ∷ v ∷ x ∷ γ)) p)
        (subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc f)))) (suc zero) zero (v' ∷ x' ∷ v ∷ x ∷ γ)) q)
```

<!--en-->
Conversely, a host-level proof of the adjacent-row condition satisfies the object-language clause: the adequacy equations identify its three premises with the two encoded entries and the successor relation, while renaming restores the original two-variable step formula.
<!--zh-->
反过来，宿主层关于相邻两行的证明可满足对象语言子句：充分性等式将三项前提分别认同为两个编码条目与后继关系，而改名语义则恢复原来的二元步进公式。
<!--ja-->
逆に、隣接する行についてのホスト側の証明から対象言語の節を満たせる。妥当性の等式によって三つの前提は二つの符号化された項目と後者関係に対応し、改名の意味論によって元の二変数のステップ論理式が復元される。
<!--/-->

```agda
        (subst ⟨_⟩ (sucAtL-adequate (suc (suc (suc zero))) (suc zero) (v' ∷ x' ∷ v ∷ x ∷ γ)) s))
```

<!--en-->
The downward clause has three universal quantifiers and one existential. If the table contains `(x',v')` and `x` is a member of the underlying set of `x'`, the formula asserts that some value is recorded at `x`; the existential semantics retains only the proposition that such a value exists.
<!--zh-->
向下子句含有三个全称量词与一个存在量词。若表含有 `(x',v')`，且 `x` 属于 `x'` 的底层集合，公式便断言在 `x` 处记录了某个值；存在量词的语义只保留「这种值存在」这一命题。
<!--ja-->
下向きの節は三つの全称量化子と一つの存在量化子をもちます。表が `(x',v')` を含み、`x` が `x'` の台集合の要素なら、`x` に何らかの値が記録されていると主張します。存在量化子の意味論が保持するのは、そのような値が存在するという命題だけです。
<!--/-->

```agda
  opaque
    downAt : ∀ {n} → Fin n → Formula S n
    downAt f = ∀̇ (∀̇ (∀̇ (
        appAt (suc (suc (suc f))) (suc (suc zero)) (suc zero)
      ⇒̇ ( (var zero ∈̇ var (suc (suc zero)))
```

<!--en-->
The existential conclusion is exactly a truncated existence of a recorded value.
<!--zh-->
该存在结论恰是一个被记录值的截断存在。
<!--ja-->
その存在の結論は、記録された値の切り詰められた存在そのものです。
<!--/-->

```agda
      ⇒̇ ∃̇ (appAt (suc (suc (suc (suc f)))) (suc zero) zero) ) )))

```

<!--en-->
Reading the downward formula preserves the existential as a propositional truncation. It maps each hidden witness value and its application atom to the corresponding host-level graph membership, without selecting a witness outside the truncation.
<!--zh-->
读取向下公式时，存在量词仍保留为命题截断。证明把截断中的每个见证值及其应用原子映到相应的宿主层图隶属，而不从截断外部选取见证。
<!--ja-->
下向きの論理式を読むとき、存在量化子は命題的切り詰めのまま保たれます。切り詰めの内部にある各証人の値と適用のアトムを、対応するホスト側のグラフ所属へ写し、切り詰めの外で証人を選ぶことはしません。
<!--/-->

```agda
    down-out : ∀ {n} (f : Fin n) (γ : S ^ n) → ⟨ γ ⊨ downAt f ⟩ → Down (lookup f γ)
    down-out f γ h x' v' x p m = map₁
      (λ { (v , q) → v , subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc f)))) (suc zero) zero (v ∷ x ∷ v' ∷ x' ∷ γ)) q })
      (h x' v' x (subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc f))) (suc (suc zero)) (suc zero) (x ∷ v' ∷ x' ∷ γ))) p) m)

```

<!--en-->
Filling runs the transport the other way, from the host-level truncated entry to the satisfaction of the existential.
<!--zh-->
填充把搬运反向运行：从宿主层的截断条目到存在式的满足。
<!--ja-->
埋めは、この輸送を逆向きに実行します。ホスト側の切り詰められた項目から、存在の充足へです。
<!--/-->

```agda
    down-in : ∀ {n} (f : Fin n) (γ : S ^ n) → Down (lookup f γ) → ⟨ γ ⊨ downAt f ⟩
    down-in f γ h x' v' x p m = map₁
      (λ { (v , q) → v , subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc (suc f)))) (suc zero) zero (v ∷ x ∷ v' ∷ x' ∷ γ))) q })
      (h x' v' x (subst ⟨_⟩ (appAt-adequate (suc (suc (suc f))) (suc (suc zero)) (suc zero) (x ∷ v' ∷ x' ∷ γ)) p) m)

```

<!--en-->
Correctness in the object language is the conjunction of the three clauses.
<!--zh-->
对象语言中的正确性即三条子句的合取。
<!--ja-->
対象言語での正しさは、三つの節の連言です。
<!--/-->

```agda
  opaque
    corrAt : ∀ {n} → Fin n → Formula S n
    corrAt f = zeroAt f ∧̇ (stepAt f ∧̇ downAt f)

```

<!--en-->
The three conjuncts recover exactly the semantic conditions already isolated as `Zero`, `Step`, and `Down`. In particular, translating the formula back to mathematics introduces neither a domain equation nor a single-valuedness assumption.
<!--zh-->
三个合取分量恰好恢复先前分别提出的 `Zero`、`Step` 与 `Down` 语义条件。尤其是，把公式读回数学陈述时，既不会引入定义域等式，也不会增加单值性假设。
<!--ja-->
三つの連言成分から、先に分けて定めた `Zero`、`Step`、`Down` の意味論的条件がそのまま復元される。特に、論理式を数学的な主張へ読み戻しても、定義域の等式や一価性の仮定が新たに加わることはない。
<!--/-->

```agda
    corr-out : ∀ {n} (f : Fin n) (γ : S ^ n) → ⟨ γ ⊨ corrAt f ⟩ → Correct (lookup f γ)
    corr-out f γ (z , (s , d)) = zero-out f γ z , (step-out f γ s , down-out f γ d)

```

<!--en-->
The converse direction shows that these three semantic conditions suffice to satisfy the conjunction. Hence `corrAt` is an exact first-order presentation of the deliberately weak notion `Correct`, rather than a stronger assertion that the approximation is already a total function graph.
<!--zh-->
反向证明表明，这三个语义条件足以满足该合取。因此，`corrAt` 精确地一阶呈现了刻意较弱的 `Correct` 概念，而没有加强为「该近似已经是全函数图」的断言。
<!--ja-->
逆方向は、この三つの意味論的条件だけで連言を満たすことを示す。したがって `corrAt` は、意図的に弱く定めた `Correct` を一階の論理式として正確に表しており、近似がすでに全域関数のグラフであるという強い主張にはなっていない。
<!--/-->

```agda
    corr-in : ∀ {n} (f : Fin n) (γ : S ^ n) → Correct (lookup f γ) → ⟨ γ ⊨ corrAt f ⟩
    corr-in f γ (z , (s , d)) = zero-in f γ z , (step-in f γ s , down-in f γ d)
```

<!--en-->
The formula `itFo` says that some correct approximation records value `y` at index `q`: internally, the graph entry is the ordered pair `(q,y)`, while the formula environment is `(y ∷ q ∷ [])`. Thus `itFo` does not state a recursion equation; it internalizes the relation witnessed by a finite correct approximation.
<!--zh-->
公式 `itFo` 表示某个正确近似在指标 `q` 处记录值 `y`：在图的内部编码中，条目是有序对 `(q,y)`，而公式环境为 `(y ∷ q ∷ [])`。因此 `itFo` 并不陈述递归方程；它把由有限正确近似见证的关系内化。
<!--ja-->
論理式 `itFo` は、ある正しい近似が添字 `q` に値 `y` を記録することを表します。グラフ内部の符号では項目は順序対 `(q,y)` であり、論理式の環境は `(y ∷ q ∷ [])` です。したがって `itFo` は再帰方程式を述べるものではなく、有限な正しい近似によって証される関係を内部化します。
<!--/-->

```agda
  opaque
    itFo : Formula S 2
    itFo = ∃̇ ( corrAt zero ∧̇ appAt zero (suc (suc zero)) (suc zero) )

```

<!--en-->
From a satisfaction of `itFo` one recovers only the propositional truncation of a witness table `F`, together with `Correct F` and the entry `(q,y)`. The formula therefore certifies that a suitable finite approximation exists, while deliberately hiding which approximation was used.
<!--zh-->
从 `itFo` 的满足只能恢复一个见证表 `F` 的命题截断，并在截断内得到 `Correct F` 及条目 `(q,y)`。因此，该公式证明合适的有限近似存在，同时刻意隐藏所用的是哪张近似表。
<!--ja-->
`itFo` の充足から復元できるのは、証人となる表 `F` の命題的切り詰めと、その内側にある `Correct F` および項目 `(q,y)` だけである。したがってこの論理式は、適切な有限近似の存在を保証する一方、どの近似を用いたかは意図的に忘れている。
<!--/-->

```agda
    itFo-out : (y q : S) → ⟨ (y ∷ q ∷ []) ⊨ itFo ⟩
             → ∥ Σ[ F ∈ S ] (Correct F × Holds F q y) ∥₁
    itFo-out y q = map₁ (λ { (F , (hc , ha)) → F
      , ( corr-out zero (F ∷ y ∷ q ∷ []) hc
        , subst ⟨_⟩ (appAt-adequate zero (suc (suc zero)) (suc zero) (F ∷ y ∷ q ∷ [])) ha ) })
```

<!--en-->
In the other direction, any particular correct approximation containing `(q,y)` witnesses `itFo(y,q)`. Its identity is immediately placed under propositional truncation, which is why later arguments may use existence and uniqueness but may not extract a preferred table.
<!--zh-->
反方向上，任何包含 `(q,y)` 的特定正确近似都可见证 `itFo(y,q)`。该近似的身份立即被置于命题截断之下，所以后续论证可以使用存在性与唯一性，却不能抽取一张优先选定的表。
<!--ja-->
逆方向では、`(q,y)` を含む具体的な正しい近似がどれでも `itFo(y,q)` の証人になる。その近似がどれであるかは直ちに命題的切り詰めの内側へ置かれるため、後の議論では存在と一意性を利用できるが、特定の表を選び出すことはできない。
<!--/-->

```agda

    itFo-in : (y q F : S) → Correct F → Holds F q y → ⟨ (y ∷ q ∷ []) ⊨ itFo ⟩
    itFo-in y q F hc hq = ∣ F
      , ( corr-in zero (F ∷ y ∷ q ∷ []) hc
        , subst ⟨_⟩ (sym (appAt-adequate zero (suc (suc zero)) (suc zero) (F ∷ y ∷ q ∷ []))) hq ) ∣₁
```

<!--en-->
The satisfaction of `itFo` is transported along an equality of the numeral slot alone; the value slot stays fixed.
<!--zh-->
`itFo` 的满足沿「数码槽的等式」搬运；值槽保持不动。
<!--ja-->
`itFo` の充足は、数項の枠の等式に沿って運ばれます。値の枠は固定されたままです。
<!--/-->

```agda
  itFo-at : (v : S) {x y : S} → x ≡ y
          → ⟨ (v ∷ x ∷ []) ⊨ itFo ⟩ → ⟨ (v ∷ y ∷ []) ⊨ itFo ⟩
  itFo-at v e = subst (λ t → ⟨ (v ∷ t ∷ []) ⊨ itFo ⟩) e
```

<!--en-->
The uniqueness lemma begins by cases on the iterate index: at zero, the zero clause gives the equation directly; at a successor, the truncated downward witness must first be eliminated. That elimination is legitimate because the target is an equality in an h-set.
<!--zh-->
唯一性引理按迭代指标分情形开始：在零点，零点子句直接给出等式；在后继，须先消去向下的截断见证。由于目标在 h-集合中是等式，消去合法。
<!--ja-->
一意性の補題は、反復の索引による場合分けで始まります。ゼロでは、ゼロの節が直接等式を与えます。後続では、下向きの切り詰められた証人をまず消去しなければなりません。目標が h-集合の中の等式であるため、この消去は正当です。
<!--/-->

```agda
  corr-val : (F : S) → Correct F → (k : ℕ) (v : S)
           → Holds F (nn k) v → fst v ≡ fst (it k)
  corr-val F (z , (s , d)) zero    v h = z v h
  corr-val F (z , (s , d)) (suc k) v h =
    rec₁ (setIsSet (fst v) (fst (it (suc k)))) read
```

<!--en-->
At a successor index, `Down` supplies, under propositional truncation, a value recorded at the predecessor numeral. The induction hypothesis identifies this predecessor value with `it k`; then `Step` shows that the current and predecessor values satisfy `stepFo`, and `only` determines the current value uniquely.
<!--zh-->
在后继指标处，`Down` 在命题截断下给出前驱数码处记录的某个值。归纳假设将此前驱值认同为 `it k`；随后 `Step` 表明当前值与前驱值满足 `stepFo`，而 `only` 唯一确定当前值。
<!--ja-->
後者の添字では、`Down` により、前の数項に記録された値が命題的切り詰めの内側で得られる。帰納法の仮定がこの値を `it k` と同一視し、続いて `Step` が現在の値と前の値による `stepFo` の充足を与え、`only` が現在の値を一意に定める。
<!--/-->

```agda
      (d (nn (suc k)) v (nn k) h (self∈sucV (# k)))
    where
    read : Σ[ u ∈ S ] Holds F (nn k) u → fst v ≡ fst (it (suc k))
    read (u , hu) = cong fst (only (it k) v
      (subst (λ t → ⟨ (v ∷ t ∷ []) ⊨ stepFo ⟩)
```

<!--en-->
The induction hypothesis gives equality of the underlying sets of `u` and `it k`. Since constructibility is a proposition, `S≡` lifts this to an equality in `S`, allowing the input of `stepFo` to be replaced by `it k`. The clause `only` then identifies `v` with `step (it k) = it (suc k)`.
<!--zh-->
归纳假设给出 `u` 与 `it k` 的底层集合相等。由于可构造性是命题，`S≡` 将它提升为 `S` 中的等式，因此可把 `stepFo` 的输入替换为 `it k`。随后，子句 `only` 将 `v` 认同为 `step (it k) = it (suc k)`。
<!--ja-->
帰納法の仮定から、`u` と `it k` の基礎となる集合が等しいことが分かる。構成可能性は命題なので、`S≡` はこの等しさを `S` における等式へ持ち上げる。そこで `stepFo` の入力を `it k` に置き換えられ、最後に `only` が `v` を `step (it k) = it (suc k)` と同一視する。
<!--/-->

```agda
        (S≡ (corr-val F (z , (s , d)) k u hu))
        (s (nn k) u (nn (suc k)) v hu h refl)))

```

<!--en-->
The value at a canonical numeral is unique: any satisfaction of the iteration formula at `nn k` records a value whose underlying set equals that of `it k`. The proof eliminates the truncated correct table and applies the uniqueness lemma within that table.
<!--zh-->
正準数码处的取值唯一：迭代公式在 `nn k` 处的任何满足，其所记录取值的底层集合都等于 `it k` 的底层集合。证明消去截断的正确表，并在该表内应用唯一性引理。
<!--ja-->
正準な数項での値は一意です。反復の論理式が `nn k` で成立するなら、記録された値の基礎の集合は `it k` の基礎の集合と等しくなります。証明は、切り詰められた正しい表を消去して、その表の中で一意性の補題を適用します。
<!--/-->

```agda
  itFo-val : (k : ℕ) (v : S) → ⟨ (v ∷ nn k ∷ []) ⊨ itFo ⟩ → fst v ≡ fst (it k)
  itFo-val k v h = rec₁ (setIsSet (fst v) (fst (it k)))
    (λ { (F , (hc , hv)) → corr-val F hc k v hv }) (itFo-out v (nn k) h)
```

<!--en-->
Each iterate is presented as a model element: the ordered pair of its numeral with the iterate itself, both constructible.
<!--zh-->
每次迭代被呈现为模型元素：其数码与迭代自身组成的有序对，二者皆可构造。
<!--ja-->
それぞれの反復は、モデルの要素として提示されます。その数項と反復自身の順序対で、どちらも構成可能です。
<!--/-->

```agda
  private
    e : ℕ → S
    e k = prʟ (nn k) (it k)

```

<!--en-->
The bounding ordinal for all entry stages is assembled by the bounding lemma applied to the family of stage indices of the entry pairs.
<!--zh-->
所有条目层索引的公共上界序数由界引理施于条目对的层索引族而得。
<!--ja-->
すべての項目の段階の添字に対する上界の順序数は、項目の対の段階の添字の族に、上界の補題を適用して得られます。
<!--/-->

```agda
  private
    entryStages = boundingOrd (Lift {ℓ-zero} {ℓ} ℕ)
      (λ k → stage (fst (e (lower k))) (e (lower k) .snd))
      (λ k → stage-ord (fst (e (lower k))) (e (lower k) .snd))

```

<!--en-->
Write `entryBound` for this common ordinal bound. The point of naming it is that every finite table can be constructed inside the same level `Lset entryBound`, even though the table length will later vary with `n`.
<!--zh-->
将这个公共序数上界记为 `entryBound`。命名它的意义在于，即使后续有限表的长度随 `n` 变化，每张表仍可在同一个层 `Lset entryBound` 中构造。
<!--ja-->
この共通の順序数上界を `entryBound` と書く。後で有限表の長さが `n` とともに変わっても、すべての表を同じ段階 `Lset entryBound` の中で構成できることが、この上界を取り出す目的である。
<!--/-->

```agda
    entryBound : V ℓ
    entryBound = entryStages .fst

```

<!--en-->
The bound is itself an ordinal, as required for it to index a constructible level. No leastness claim is needed: any ordinal lying above all the entry stages is enough for the finite-set construction.
<!--zh-->
该上界本身是序数，因而可以索引一个可构造层。这里不需要任何最小性结论：只要某个序数高于所有条目的层索引，就足以进行有限集构造。
<!--ja-->
この上界自身は順序数なので、構成可能階層の段階を添字付けられる。最小性は必要ない。すべての項目の段階の添字より上にある順序数なら、有限集合を構成するには十分である。
<!--/-->

```agda
    entryBound-ord : IsOrd entryBound
    entryBound-ord = entryStages .snd .fst

```

<!--en-->
Each entry belongs to the constructible level indexed by the common bound. Indeed, its own stage contains it, and monotonicity of `Lset` carries that membership along the comparison supplied by `boundingOrd`.
<!--zh-->
每个条目都属于公共上界所索引的可构造层。具体而言，条目属于其自身的层，而 `Lset` 的单调性沿 `boundingOrd` 给出的序数比较将该隶属关系送入公共层。
<!--ja-->
各項目は、共通の上界を添字とする構成可能階層に属する。実際、項目はまずそれ自身の段階に属し、`Lset` の単調性によって、`boundingOrd` が与える順序数の比較に沿って共通の段階へ移される。
<!--/-->

```agda
    entry-in-bound : (k : ℕ) → ⟨ fst (e k) ∈ Lset entryBound ⟩
    entry-in-bound k = Lset-mono (entryStages .snd .snd (lift k))
      (stage-mem (fst (e k)) (e k .snd))

```

<!--en-->
For a fixed `n`, the table `Fn n` is the finite set of entry pairs with indices `0` through `n`. The common bound proves that every such pair lies in one constructible level, so the finite-set construction packages the whole table as an element of `L`.
<!--zh-->
固定 `n` 后，表 `Fn n` 是由指标从 `0` 到 `n` 的条目对组成的有限集。公共上界证明所有这些有序对都属于同一个可构造层，因此有限集构造可将整张表打包为 `L` 的元素。
<!--ja-->
`n` を固定すると、表 `Fn n` は添字 `0` から `n` までの項目の対からなる有限集合である。共通の上界により、それらの対がすべて一つの構成可能階層に属することが分かるので、有限集合の構成によって表全体を `L` の要素としてまとめられる。
<!--/-->

```agda
  Fn : ℕ → S
  Fn n = finSet (suc n) (λ i → fst (e (toℕ i))) ,
    FinOf.finSetL entryBound entryBound-ord
      (suc n) (λ i → fst (e (toℕ i))) (λ i → entry-in-bound (toℕ i))

```

<!--en-->
If `k ≤ n`, the canonical entry `(nn k, it k)` occurs in `Fn n`. Thus the table contains exactly the initial segment needed to witness the iteration formula at its final index `n`.
<!--zh-->
若 `k ≤ n`，正準条目 `(nn k, it k)` 就出现在 `Fn n` 中。因此，这张表包含在末指标 `n` 处见证迭代公式所需的整个初始段。
<!--ja-->
`k ≤ n` なら、標準的な項目 `(nn k, it k)` は `Fn n` に現れる。したがってこの表は、末尾の添字 `n` で反復の論理式を証言するために必要な初切片をすべて含む。
<!--/-->

```agda
  Fn-in : (n k : ℕ) → k ≤ n → Holds (Fn n) (nn k) (it k)
  Fn-in n k p = subst (λ w → ⟨ w ∈ fst (Fn n) ⟩) (prʟ-fst (nn k) (it k))
    (finSet-in (suc n) (λ i → fst (e (toℕ i))) (fst (e k))
      ∣ fromℕ' (suc n) k (suc-≤-suc p)
      , cong (λ j → fst (e j)) (toFromId' (suc n) k (suc-≤-suc p)) ∣₁)
```

<!--en-->
The outward reading decomposes any member into a bounded index and its iterate value, both recovered under truncation.
<!--zh-->
向外读法把任何成员分解为有界索引及其迭代取值，均在截断下恢复。
<!--ja-->
外向きの読み出しは、すべての要素を、有界な添字とその反復の値へ分解します。どちらも切り詰めの下で復元されます。
<!--/-->

```agda

  Fn-out : (n : ℕ) (y : S) → ⟨ y ∈ˢ Fn n ⟩
         → ∥ Σ[ k ∈ ℕ ] ((k ≤ n) × (fst y ≡ pr (# k) (fst (it k)))) ∥₁
  Fn-out n y h = map₁ (λ { (i , q) → toℕ i
    , (pred-≤-pred (toℕ<n i) , sym q ∙ prʟ-fst (nn (toℕ i)) (it (toℕ i))) })
    (finSet-out (suc n) (λ i → fst (e (toℕ i))) (fst y) h)
```

<!--en-->
The pair reading decomposes any entry of the finite table into a bounded index and its iterate value, using the injectivity of the Kuratowski pair.
<!--zh-->
对的读法用 Kuratowski 对的单射性把有限表的任何条目分解为有界索引及其迭代取值。
<!--ja-->
対の読み出しは、Kuratowski の対の単射性を使って、有限の表のどの項目も、有界な添字とその反復の値へ分解します。
<!--/-->

```agda
  Fn-pair : (n : ℕ) (x v : S) → Holds (Fn n) x v
          → ∥ Σ[ k ∈ ℕ ] ((k ≤ n) × ((fst x ≡ # k) × (fst v ≡ fst (it k)))) ∥₁
  Fn-pair n x v h = map₁ (λ { (k , (p , q)) → k , (p , pr-inj (sym (prʟ-fst x v) ∙ q)) })
    (Fn-out n (prʟ x v) (subst (λ w → ⟨ w ∈ fst (Fn n) ⟩) (sym (prʟ-fst x v)) h))

```

<!--en-->
The finite table is correct: the three clauses are assembled from the pair readings of the table entries.
<!--zh-->
有限表是正确的：三条子句由表条目的对读取装配。
<!--ja-->
有限の表は正しいです。三つの条項は、表の項目の対の読み出しから組み立てられます。
<!--/-->

```agda
  Fn-correct : (n : ℕ) → Correct (Fn n)
  Fn-correct n = zeroC , (stepC , downC)
    where
    zeroC : Zero (Fn n)
    zeroC v h = rec₁ (setIsSet (fst v) (fst a))
```

<!--en-->
For the zero clause, reading an entry at `nn 0` yields some index `k` whose numeral is `# 0`. Injectivity of the numeral encoding forces `k = 0`, and the accompanying value equation then identifies the recorded value with `it 0 = a`.
<!--zh-->
为证明零点子句，从 `nn 0` 处的条目可读出某个数码等于 `# 0` 的指标 `k`。数码编码的单射性迫使 `k = 0`，随附的取值等式遂将记录值认同为 `it 0 = a`。
<!--ja-->
零点の条項では、`nn 0` にある項目を読むと、数項が `# 0` に等しい添字 `k` が得られる。数項の符号化の単射性から `k = 0` となり、同時に得られた値の等式によって、記録された値は `it 0 = a` と同一視される。
<!--/-->

```agda
      (λ { (k , (_ , (ex , ev))) → ev ∙ cong (λ j → fst (it j)) (sym (#-inj 0 k ex)) })
      (Fn-pair n (nn 0) v h)

```

<!--en-->
For the step clause, read the two table entries under propositional truncation. Since satisfaction of `stepFo` is a proposition, both truncations may be eliminated there; the remaining task is to identify their indices as consecutive and their values as the corresponding iterates.
<!--zh-->
为证明步进子句，先在命题截断下读取两个表条目。由于 `stepFo` 的满足是命题，两层截断都可消去到这一目标中；余下只须证明两个指标相邻，并将两个值分别认同为相应的迭代。
<!--ja-->
ステップの節では、二つの表項目を命題的切り詰めの内側で読み出す。`stepFo` の充足は命題なので、二つの切り詰めをこの目標へ消去できる。残るのは、二つの添字が連続していることと、それぞれの値が対応する反復であることを示す作業である。
<!--/-->

```agda
    stepC : Step (Fn n)
    stepC x v x' v' hxv hx'v' s = rec₁ (snd ((v' ∷ v ∷ []) ⊨ stepFo)) outer (Fn-pair n x v hxv)
      where
      outer : Σ[ k ∈ ℕ ] ((k ≤ n) × ((fst x ≡ # k) × (fst v ≡ fst (it k))))
            → ⟨ (v' ∷ v ∷ []) ⊨ stepFo ⟩
```

<!--en-->
After the first reading has exposed `k`, the second exposes an index `k'` for the adjacent row. Keeping both witnesses inside eliminations into the propositional satisfaction judgment respects the truncation boundary while making their index and value equations simultaneously available.
<!--zh-->
第一次读取给出 `k` 后，第二次读取给出相邻行的指标 `k'`。两个见证始终位于以命题性满足判断为目标的消去之内；这样既守住截断边界，又能同时使用它们的指标等式与取值等式。
<!--ja-->
最初の読み出しで `k` が現れた後、二つ目の読み出しから隣接する行の添字 `k'` が得られる。二つの証人を、命題である充足判断への消去の内側に保つことで、切り詰めの境界を守りながら、添字と値の等式を同時に利用できる。
<!--/-->

```agda
      outer (k , (_ , (ex , ev))) = rec₁ (snd ((v' ∷ v ∷ []) ⊨ stepFo)) inner (Fn-pair n x' v' hx'v')
        where
        inner : Σ[ k' ∈ ℕ ] ((k' ≤ n) × ((fst x' ≡ # k') × (fst v' ≡ fst (it k'))))
              → ⟨ (v' ∷ v ∷ []) ⊨ stepFo ⟩
        inner (k' , (_ , (ex' , ev'))) =
```

<!--en-->
The two table readings identify `v` with `it k` and `v'` with `it k'`. The successor equation between their positions forces `k' = suc k`; after these identifications, the required satisfaction is precisely `defines (it k)`. Equalities in the model carrier are obtained with `S≡`, using that the constructibility proof component is propositional.
<!--zh-->
两次表读取分别将 `v` 认同为 `it k`、将 `v'` 认同为 `it k'`。两个位置之间的后继等式迫使 `k' = suc k`；完成这些认同后，所需的满足恰由 `defines (it k)` 给出。模型载体中的等式由 `S≡` 获得，其中用到了可构造性证明分量是命题这一事实。
<!--ja-->
二つの表の読み出しにより、`v` は `it k` と、`v'` は `it k'` とそれぞれ同一視される。二つの位置を結ぶ後者の等式から `k' = suc k` が従うので、これらを置き換えた後に必要な充足はちょうど `defines (it k)` である。モデルの台における等式には、構成可能性の証明成分が命題であることを用いて `S≡` を適用する。
<!--/-->

```agda
          subst2 (λ p q → ⟨ (p ∷ q ∷ []) ⊨ stepFo ⟩)
            (S≡ (sym (ev' ∙ cong (λ j → fst (it j)) k'≡)))
            (S≡ (sym ev))
            (defines (it k))
          where
```

<!--en-->
To obtain `k' = suc k`, compare the equation saying that the second position is the successor of the first with the two equations identifying those positions as `# k'` and `# k`. Injectivity of the numeral encoding then turns equality of the encoded finite ordinals into equality of their natural-number indices.
<!--zh-->
为得到 `k' = suc k`，将「第二个位置是第一个位置的后继」这一等式，与分别把两个位置认同为 `# k'` 和 `# k` 的等式合成。数码编码的单射性便把编码后有限序数的相等化为自然数指标的相等。
<!--ja-->
`k' = suc k` を得るには、第二の位置が第一の位置の後者であるという等式を、それぞれの位置を `# k'` と `# k` に同一視する等式と合成する。すると数項の符号化の単射性により、符号化された有限順序数の等しさが自然数の添字の等しさへ変わる。
<!--/-->

```agda
          k'≡ : k' ≡ suc k
          k'≡ = #-inj k' (suc k) (sym ex' ∙ s ∙ cong sucV ex)

```

<!--en-->
The downward clause is proved by eliminating the truncated pair reading and finding a smaller index whose canonical entry is already present.
<!--zh-->
向下子句的证明由消去截断的对读取并找到已有正準条目的更小索引完成。
<!--ja-->
下向きの条項は、切り詰められた対の読み出しを消去して、すでに正準な項目のあるより小さい添字を見つけることで証明されます。
<!--/-->

```agda
    downC : Down (Fn n)
    downC x' v' x h m = rec₁ squash₁ outer (Fn-pair n x' v' h)
      where
      outer : Σ[ k' ∈ ℕ ] ((k' ≤ n) × ((fst x' ≡ # k') × (fst v' ≡ fst (it k'))))
            → ∥ Σ[ v ∈ S ] Holds (Fn n) x v ∥₁
```

<!--en-->
The smaller index's entry is produced by the inward reading of the finite table, transported along the numeral equation.
<!--zh-->
更小索引的条目由有限表的向内读式产出，沿数码等式运输。
<!--ja-->
より小さい添字の項目は、有限の表の内向きの読み出しによって作られ、数項の等式に沿って運ばれます。
<!--/-->

```agda
      outer (k' , (p' , (ex' , _))) = map₁
        (λ { (j , (j< , ej)) → it j
           , subst (λ t → ⟨ pr t (fst (it j)) ∈ fst (Fn n) ⟩) (sym ej)
               (Fn-in n j (≤-trans (<-weaken j<) p')) })
        (∈#-elim k' (fst x) (subst (λ w → ⟨ fst x ∈ w ⟩) ex' m))
```

<!--en-->
Each canonical pair satisfies the iteration formula, using its own finite table as the witness. Every target numeral thus has its own table; no single table is claimed to serve all positions.
<!--zh-->
每条正準对都满足迭代公式，以各自的有限表为见证。每个目标数码都有自己的表；不主张任何单表同时服务所有位置。
<!--ja-->
それぞれの正準な対が反復の論理式を満たします。自分自身の有限の表を証人として使います。すべての目標の数項が、それぞれ自分の表をもちます。一つの表がすべての位置に仕えるとは主張していません。
<!--/-->

```agda
  it-graph : (k : ℕ) → ⟨ (it k ∷ nn k ∷ []) ⊨ itFo ⟩
  it-graph k = itFo-in (it k) (nn k) (Fn k) (Fn-correct k) (Fn-in k k ≤-refl)
```

<!--en-->
A numeral representation is an explicit pair of a natural number with the equation identifying it with the carrier element.
<!--zh-->
数码表示是自然数与「认同其为载体元素」的等式的显式对。
<!--ja-->
数項の表示とは、自然数と、それを台の要素と同一視する等式の、明示的な対です。
<!--/-->

```agda
  Num : S → Type (ℓ-suc ℓ)
  Num q = Σ[ k ∈ ℕ ] (nn k ≡ q)

```

<!--en-->
Membership in the model's natural-number set `ωʟ` recovers such a numeral representation only under propositional truncation. This is enough for later uniqueness arguments, whose conclusions are propositions, but it does not expose a natural number for unrestricted computation.
<!--zh-->
从模型内部自然数集 `ωʟ` 的成员关系，只能在命题截断下恢复这种数码表示。这足以用于后续结论为命题的唯一性论证，却不会给出一个可供任意计算使用的自然数。
<!--ja-->
モデル内部の自然数集合 `ωʟ` に属することから得られる数項表示は、命題的切り詰めの内側にとどまる。後で結論が命題となる一意性の議論にはこれで十分だが、任意の計算に使える自然数が取り出されるわけではない。
<!--/-->

```agda
  ω-num : (q : S) → ⟨ q ∈ˢ ωʟ ⟩ → ∥ Num q ∥₁
  ω-num q = map₁ (λ { (i , p) → lower i , S≡ p })

```

<!--en-->
We can now regard `itFo` as a total, single-valued relation on the internal set `ωʟ`. The record `valR` packages this domain and graph together with the remaining functionality proof; applying Replacement to this record will collect their values in `L`.
<!--zh-->
现在可以把 `itFo` 看作内部集合 `ωʟ` 上的全且单值的关系。记录 `valR` 将定义域、图关系与尚待给出的函数性证明打包；随后对该记录应用替换，即可在 `L` 中收集这些取值。
<!--ja-->
ここまでで `itFo` を、内部集合 `ωʟ` 上の全域かつ一価な関係とみなせる。レコード `valR` はこの定義域とグラフを、残る関数性の証明とともにまとめる。このレコードに置換を適用することで、それらの値を `L` の中に集められる。
<!--/-->

```agda
  private
    valR : Recursion
    valR = record
      { dom   = ωʟ
      ; graph = itFo
```

<!--en-->
Functionality is assembled from a merely-existing numeral representation: the decode produces the iterate value, and the uniqueness is proved at the decoded numeral.
<!--zh-->
函数性由「仅存在的数码表示」装配：解码产出迭代取值，唯一性在解码出的数码处证明。
<!--ja-->
関数性は、単に存在するだけの数項の表示から組み立てられます。復号が反復の値を産出し、一意性は、復号された数項で証明されます。
<!--/-->

```agda
      ; funct = λ q q∈ → mereFunct itFo q (map₁ (wit q) (ω-num q q∈)) }
      where
      wit : (q : S) → Num q
          → Σ[ y ∈ S ] (⟨ (y ∷ q ∷ []) ⊨ itFo ⟩
                       × ((y' : S) → ⟨ (y' ∷ q ∷ []) ⊨ itFo ⟩ → y' ≡ y))
```

<!--en-->
For a displayed representation `nn k ≡ q`, take `it k` as the centre of the fibre. The graph proof is transported forward to `q`, while any competing value is transported back to `nn k` and identified by `itFo-val`. The surrounding `mereFunct` turns the truncated existence of such a centre with uniqueness into contractibility of the fibre.
<!--zh-->
给定一个明确的表示 `nn k ≡ q`，取 `it k` 为纤维中心。先将图证明向前搬运到 `q`；对任何竞争取值，则将其证明反向搬运到 `nn k`，再由 `itFo-val` 认同。外围的 `mereFunct` 把这种带唯一性的中心之截断存在化为纤维的可缩性。
<!--ja-->
具体的な表示 `nn k ≡ q` が与えられたら、`it k` をファイバーの中心とする。グラフの証明は `q` へ順向きに移し、競合する値の証明は `nn k` へ戻して `itFo-val` により同一視する。外側の `mereFunct` は、このような一意な中心の切り詰められた存在を、ファイバーの可縮性へ変える。
<!--/-->

```agda
      wit q (k , eq) = it k
        , ( itFo-at (it k) eq (it-graph k)
          , λ y' h → S≡ (itFo-val k y' (itFo-at y' (sym eq) h)) )

```

<!--en-->
The general Replacement construction associated with `valR` now provides a set containing its values, together with exact membership rules. These rules will connect the internally collected set with the host-defined sequence `it`.
<!--zh-->
与 `valR` 关联的一般替换构造现在给出一个收集其取值的集合，并附带精确的隶属规则。这些规则将内部收集所得的集合与宿主侧定义的序列 `it` 联系起来。
<!--ja-->
`valR` に付随する一般の置換構成から、その値を集めた集合と、正確な所属規則が得られる。これらの規則によって、内部で集めた集合と、ホスト側で定義した列 `it` とが結び付く。
<!--/-->

```agda
    module VR = Of valR

```

<!--en-->
The set `values` is the Replacement image of `ωʟ` under the relation `itFo`: it contains the finite iterate values, with repetitions automatically collapsed by sethood. It is a set of values, rather than the indexed function graph constructed below.
<!--zh-->
集合 `values` 是 `ωʟ` 经关系 `itFo` 所得的替换像：它包含各次有限迭代的取值，而重复取值因集合性自然合并。它是取值集合，并非下文构造的带索引函数图。
<!--ja-->
集合 `values` は、関係 `itFo` による `ωʟ` の置換像である。有限反復の値を含み、重複する値は集合として自動的に一つにまとまる。これは値の集合であって、後で構成する添字付きの関数グラフではない。
<!--/-->

```agda
  values : S
  values = VR.table

```

<!--en-->
Every host-defined iterate belongs to this value set. At the internal numeral `nn n`, membership follows from `nn n ∈ ωʟ` together with the finite-table witness `it-graph n`.
<!--zh-->
每个宿主侧定义的迭代都属于这个取值集合。在内部数码 `nn n` 处，`nn n ∈ ωʟ` 与有限表见证 `it-graph n` 共同给出该隶属关系。
<!--ja-->
ホスト側で定義した各反復は、この値の集合に属する。内部の数項 `nn n` について、`nn n ∈ ωʟ` と有限表による証明 `it-graph n` を合わせることで、この所属が得られる。
<!--/-->

```agda
  values-in : (n : ℕ) → ⟨ fst (it n) ∈ fst values ⟩
  values-in n = VR.table-in (nn n) (it n) (#∈ω n) (it-graph n)

```

<!--en-->
Every member of the value domain is, merely, some iterate value: the outward reading recovers the numeral representation and the iteration formula satisfaction, and the uniqueness lemma identifies the value.
<!--zh-->
值域的每个成员仅是某次迭代的取值：向外读法恢复数码表示与迭代公式满足，唯一性引理认同取值。
<!--ja-->
値の領域のすべての要素は、単に、なんらかの反復の値です。外向きの読み出しが数項の表示と反復の論理式の充足を復元し、一意性の補題が値を同定します。
<!--/-->

```agda
  values-out : (y : S) → ⟨ y ∈ˢ values ⟩ → ∥ Σ[ n ∈ ℕ ] (fst y ≡ fst (it n)) ∥₁
  values-out y hy = rec₁ squash₁
    (λ { (q , (q∈ , h)) → map₁
      (λ { (k , eq) → k , itFo-val k y (itFo-at y (sym eq) h) }) (ω-num q q∈) })
    (VR.table-out y hy)
```

<!--en-->
The union of the value domain is a set of `L`, formed by the model's union operation.
<!--zh-->
值域的并由模型的并运算形成，是 `L` 的集合。
<!--ja-->
値の領域の合併は、モデルの合併の操作によって作られ、`L` の集合です。
<!--/-->

```agda

  iterUnion : S
  iterUnion = unionʟ values

```

<!--en-->
Every member of a finite iterate belongs to `iterUnion`: first `values-in` places that iterate itself in `values`, and then the defining membership rule for union places each of its members in the union. Notice that this proves `it n ⊆ iterUnion`, rather than that `it n` itself is a member of `iterUnion`.
<!--zh-->
每次有限迭代的所有成员都属于 `iterUnion`：先由 `values-in` 将该迭代本身放入 `values`，再由并的隶属规则将它的每个成员放入并中。这里证明的是 `it n ⊆ iterUnion`，并非 `it n` 本身属于 `iterUnion`。
<!--ja-->
各有限反復のすべての要素は `iterUnion` に属する。まず `values-in` により反復そのものが `values` に入り、次に和集合の所属規則により、その各要素が和集合に入る。ここで示されるのは `it n ⊆ iterUnion` であり、`it n` 自身が `iterUnion` の要素だということではない。
<!--/-->

```agda
  iterUnion-in : (n : ℕ) (z : S) → ⟨ fst z ∈ fst (it n) ⟩ → ⟨ z ∈ˢ iterUnion ⟩
  iterUnion-in n z hz = unionʟ-in values z (it n) (values-in n) hz

```

<!--en-->
Every member of the union merely lies in some finite iterate. The proof eliminates the union membership to find the intermediate set, packages it as constructible, and reads it through the value domain's outward reading.
<!--zh-->
并的每个成员仅属于某次有限迭代。证明消去并的隶属以找到中间集合，将其打包为可构造，再经值域向外读法读取。
<!--ja-->
合併のすべての要素は、単に、ある有限の反復の中にあります。証明は、合併の所属を消去して中間の集合を見つけ、それを構成可能として包み、値の領域の外向きの読み出しで読みます。
<!--/-->

```agda
  iterUnion-out : (z : S) → ⟨ z ∈ˢ iterUnion ⟩ → ∥ Σ[ n ∈ ℕ ] ⟨ fst z ∈ fst (it n) ⟩ ∥₁
  iterUnion-out z h = rec₁ squash₁
    (λ { (B , (hB , hz)) → map₁
      (λ { (n , eB) → n , subst (λ w → ⟨ fst z ∈ w ⟩) eB hz })
      (values-out (B , isL-trans {x = fst values} {y = B} hB (snd values)) hB) })
```

<!--en-->
The outer union rule yields an intermediate set `B` with `B ∈ values` and `z ∈ B`, still under propositional truncation. Transitivity of `L` supplies the constructibility witness needed to regard `B` as an element of `S`; `values-out` then identifies it with some `it n`, again without selecting an index outside the truncation.
<!--zh-->
并的向外规则在命题截断下给出一个中间集合 `B`，满足 `B ∈ values` 且 `z ∈ B`。`L` 的传递性补出把 `B` 视为 `S` 元素所需的可构造性见证；随后 `values-out` 将它认同为某个 `it n`，而指标仍不被选出命题截断之外。
<!--ja-->
和集合の外向きの規則から、`B ∈ values` かつ `z ∈ B` を満たす中間集合 `B` が、命題的切り詰めの内側で得られる。`L` の推移性により `B` を `S` の要素とみなすための構成可能性の証人が補われ、続いて `values-out` が `B` をある `it n` と同一視する。この添字も切り詰めの外へ選び出されることはない。
<!--/-->

```agda
    (unionʟ-out values z h)
```

<!--en-->
## The indexed graph and finite growth
<!--zh-->
## 带索引的图与有限增长
<!--ja-->
## 添字付きグラフと有限段階の成長
<!--/-->

<!--en-->
Besides the value set and its union, the same recursion record determines an internal function graph. Its elements retain both the numeral input and the corresponding iterate value, which is needed when later arguments must refer to a particular finite stage rather than merely to the set of all values.
<!--zh-->
除取值集合及其并之外，同一递归记录还确定一个内部函数图。图中的元素同时保留输入数码及相应的迭代取值，因而后续论证若须指称某个特定有限层，而不只是所有取值的集合，便可使用此图。
<!--ja-->
値の集合とその和集合に加えて、同じ再帰レコードから内部の関数グラフも定まる。その要素は入力の数項と対応する反復値の両方を保持するので、後の議論で値全体の集合だけでなく特定の有限段階を参照する必要があるときに利用できる。
<!--/-->

```agda
  private
    module TR = RecursionGraph valR using ( F; F-in; F-out )

```

<!--en-->
The function graph collects the ordered pairs of numerals and iterate values.
<!--zh-->
函数图收集数码与迭代取值组成的有序对。
<!--ja-->
関数のグラフは、数項と反復の値の順序対を集めます。
<!--/-->

```agda
  iter : S
  iter = TR.F

```

<!--en-->
Every canonical pair is a member of the graph, transported along the uniqueness of the replacement value.
<!--zh-->
每条正準对都是图的成员，沿替换取值的唯一性运输。
<!--ja-->
それぞれの正準な対は、グラフの要素です。置換の値の一意性に沿って運ばれます。
<!--/-->

```agda
  iter-in : (n : ℕ) → ⟨ pr (# n) (fst (it n)) ∈ fst iter ⟩
  iter-in n = subst (λ v → ⟨ pr (# n) (fst v) ∈ fst iter ⟩)
    (VR.val-uniq (nn n) (#∈ω n) (it n) (it-graph n)) (TR.F-in (nn n) (#∈ω n))

```

<!--en-->
Conversely, every graph member is merely equal to a canonical pair `(# n, it n)` for some natural number `n`. The source supplied by the general graph rule and its numeral representation both remain under propositional truncation, and value uniqueness identifies the second component without exposing `n` outside that truncation.
<!--zh-->
反过来，图的每个成员都仅仅等于某个自然数 `n` 对应的正準有序对 `(# n, it n)`。一般图规则给出的源及其数码表示始终留在命题截断之下，而取值唯一性认同第二分量，却不会把 `n` 暴露到截断之外。
<!--ja-->
逆に、グラフの各要素は、ある自然数 `n` に対する標準的な対 `(# n, it n)` に単に等しい。一般のグラフ規則から得られる始域の要素とその数項表示は、どちらも命題的切り詰めの内側に保たれる。値の一意性により第二成分を同一視できるが、`n` が切り詰めの外へ取り出されることはない。
<!--/-->

```agda
  iter-out : (y : S) → ⟨ y ∈ˢ iter ⟩ → ∥ Σ[ n ∈ ℕ ] (fst y ≡ pr (# n) (fst (it n))) ∥₁
  iter-out y hy = rec₁ squash₁
    (λ { (q , q∈ , e) → map₁ (λ { (k , eq) → k
      , e ∙ cong₂ pr (cong fst (sym eq))
        (cong fst (VR.val-uniq q q∈ (it k) (itFo-at (it k) eq (it-graph k)))) }) (ω-num q q∈) })
```

<!--en-->
The outward membership rule for the general graph first supplies a source `q ∈ ωʟ` and the encoded pair involving its unique value. Decoding `q` as a numeral and using value uniqueness turns this into the stated canonical pair, while the natural-number index remains under propositional truncation.
<!--zh-->
一般函数图的向外隶属规则先给出一个源 `q ∈ ωʟ`，以及由它的唯一取值组成的编码有序对。将 `q` 解码为数码并使用取值唯一性，便得到所述正準有序对；自然数指标始终留在命题截断之下。
<!--ja-->
一般の関数グラフの外向き所属規則から、まず始域の要素 `q ∈ ωʟ` と、その一意な値を含む符号化された対が得られる。`q` を数項として復号し、値の一意性を使えば、主張された標準的な対になる。自然数の添字は最後まで命題的切り詰めの内側に保たれる。
<!--/-->

```agda
    (TR.F-out (fst y) hy)
```

<!--en-->
The growth module is parameterized by the hypothesis that each set is contained in its own step.
<!--zh-->
增长模块以「每个集合包含于自身步进」的假设为参数。
<!--ja-->
成長のモジュールは、「すべての集合が自分自身のステップの中に含まれる」という仮定によってパラメータづけられます。
<!--/-->

```agda
  module Closure (grows : (x z : S) → ⟨ fst z ∈ fst x ⟩ → ⟨ fst z ∈ fst (step x) ⟩) where

```

<!--en-->
The growth hypothesis gives one-way containment between adjacent iterates: every member of `it n` also belongs to `it (suc n)`. No reverse containment, fixed-point property, or closure of `iterUnion` under `step` follows from this statement.
<!--zh-->
增长假设给出相邻迭代之间的单向包含：`it n` 的每个成员也属于 `it (suc n)`。该结论不蕴含反向包含、不动点性质，也不蕴含 `iterUnion` 对 `step` 封闭。
<!--ja-->
成長の仮定から、隣り合う反復の間の一方向の包含が得られる。すなわち `it n` の各要素は `it (suc n)` にも属する。この主張から逆向きの包含、不動点性、あるいは `iterUnion` の `step` による閉性は導かれない。
<!--/-->

```agda
    it-mono : (n : ℕ) (z : S) → ⟨ fst z ∈ fst (it n) ⟩ → ⟨ fst z ∈ fst (it (suc n)) ⟩
    it-mono n z = grows (it n) z

```

<!--en-->
Iterating the adjacent containment `k` times proves `it n ⊆ it (k + n)`. The induction measures the number of additional steps, so the result compares two explicitly separated finite stages; it asserts neither monotonicity of `step` with respect to arbitrary inclusions nor any closure property of their union.
<!--zh-->
将相邻包含重复 `k` 次可得 `it n ⊆ it (k + n)`。归纳变量是额外步数，因此结论比较的是两个以明确步数分隔的有限层；它既不主张 `step` 对任意包含关系单调，也不主张这些层的并具有任何封闭性。
<!--ja-->
隣接する段階の包含を `k` 回繰り返すと、`it n ⊆ it (k + n)` が得られる。帰納するのは追加するステップ数なので、この結果は明示された有限個のステップだけ離れた二つの段階を比較する。`step` が任意の包含に関して単調であることも、それらの和集合が何らかの閉性をもつことも主張していない。
<!--/-->

```agda
    it-up : (n k : ℕ) (z : S) → ⟨ fst z ∈ fst (it n) ⟩ → ⟨ fst z ∈ fst (it (k + n)) ⟩
    it-up n zero    z h = h
    it-up n (suc k) z h = it-mono (k + n) z (it-up n k z h)
```

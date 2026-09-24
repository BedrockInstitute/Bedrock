```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
# The environment tower
<!--zh-->
# 环境塔
<!--ja-->
# 環境の塔
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )
```

<!--en-->
Fix a universe level `ℓ` and an instance `lem : LEM (ℓ-suc ℓ)`. Every construction below is relative to this one hypothesis; no stronger classical principle is added.
<!--zh-->
固定宇宙层级 `ℓ` 与实例 `lem : LEM (ℓ-suc ℓ)`。下文所有构造都相对于这一项假设，不再加入更强的经典原理。
<!--ja-->
宇宙レベル `ℓ` と実例 `lem : LEM (ℓ-suc ℓ)` を固定する。以下の構成はすべてこの一つの仮定に相対的であり、これより強い古典的原理は加えない。
<!--/-->

```agda
module L.Coding.EnvironmentTower {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; ⊥̇; ∃̇_; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using ( checkΔ₀; Δ₀ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction; extensionalV )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Environment {ℓ} using ( env; cons )
open import L.Coding.Model {ℓ} using ( prAtL; prʟ; prʟ-fst; container )
open import L.Coding.Expressions {ℓ} using
  ( envSetAt; sucAtL; consAtL; consAtL-adequate; numL )
open import L.Coding.Quantification {ℓ} using
  ( i0; i1; i2; i3; sh; pr-out; pr-in; down; suc-out; suc-in
  ; i4; i5
  ; sndEx; bothEx; bothAll
  ; sndEx-out; bothEx-out; bothAll-in
  ; fillSnd; fillBoth; useBoth )
open import L.Coding.EnvironmentSet {ℓ} lem using ( envSet; envSet-in; envSet-out; envS; Ix )
open import L.Coding.EnvironmentAgreement {ℓ} lem using ( module Ambient; module AmbientHolds )
open import L.Recursion {ℓ} lem using ( smallDom )
open import L.Axioms.Basic {ℓ} using ( extensionalL )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ; ω-specL )
```

<!--en-->
This chapter builds the environment tower inside `L`. For each natural number `n`, the tower records the coded ordered pair `(# n, envSet W n)`, where `envSet W n` is the set of all length-`n` environments taking values in `W`. The construction first produces the actual set and then gives a bounded first-order description through which later chapters can read its coded entries.
<!--zh-->
本章在 `L` 内构造环境塔。对每个自然数 `n`，该塔记录码化有序对 `(# n, envSet W n)`，其中 `envSet W n` 是全体取值于 `W` 的 `n` 元环境之集。我们先构造这个实际集合，再给出一份有界一阶描述，供后续章节读取其中的码化条目。
<!--ja-->
本章では、`L` の内部に環境の塔を構成する。各自然数 `n` に対して、塔は符号化された順序対 `(# n, envSet W n)` を記録する。ここで `envSet W n` は、`W` に値を取る長さ `n` のすべての環境からなる集合である。まず実際の集合を構成し、次に、後の章がその符号化された項目を読み取るための有界な一階記述を与える。
<!--/-->

<!--en-->
The construction is carried out in cubical type theory and uses excluded middle at the stated universe level. This classical hypothesis enters through the constructions of fixed-length environment sets, common bounds, separation, and the internal natural numbers.
<!--zh-->
这一构造在立方类型论中进行，并使用所标宇宙层级上的排中律。该经典假设经由定长环境集、公共界、分离以及内部自然数集的构造进入本章。
<!--ja-->
この構成は立方型理論の中で行われ、明記された宇宙レベルでの排中律を用いる。この古典的仮定は、固定長の環境集合、共通の上界、分出、および内部自然数集合の構成を通して本章に入る。
<!--/-->



<!--en-->
Two descriptions of the tower will coexist. The first is an external construction of a set in `L`; the second is a formula in the object language of set theory. Membership, equality, conjunction, disjunction, and bounded quantification form that formula, while the Lévy-hierarchy checker will certify that it is Δ₀.
<!--zh-->
本章会同时使用环境塔的两种描述。第一种是在外围构造 `L` 中的一个集合，第二种是集合论对象语言中的公式。该公式由隶属、相等、合取、析取与有界量化组成，Lévy 层级检查器则会认证它属于 Δ₀。
<!--ja-->
本章では、環境の塔について二つの記述を併用する。一つは `L` の集合を外側から構成する記述であり、もう一つは集合論の対象言語における論理式である。後者は所属、等号、連言、選言、有界量化から組み立てられ、Lévy 階層の検査器によって Δ₀ であることが認証される。
<!--/-->

<!--en-->
The proof later reads a tower entry downward to a predecessor. Membership induction in the cumulative hierarchy justifies this descent, and extensionality identifies environment sets once their members agree. Injectivity of the coded ordered pair then recovers the numeral and environment-set components separately.
<!--zh-->
稍后的证明会把环境塔条目向下读到前驱。累积层级中的隶属归纳保证这种下降良基，而外延性在成员相同时识别两个环境集。码化有序对的单射性继而分别恢复数码分量与环境集分量。
<!--ja-->
後の証明では、塔の項目を先行項目へ向かって下向きに読む。累積階層の所属帰納がこの降下の整礎性を保証し、外延性が、同じ要素をもつ環境集合を同定する。さらに符号化順序対の単射性によって、数項成分と環境集合成分を別々に復元できる。
<!--/-->

<!--en-->
The bridge between the two descriptions consists of formulas recognizing coded pairs, von Neumann successors, environment sets, and cons extensions. Containers keep the component quantifiers bounded, and adequacy lemmas identify satisfaction of these formulas with the corresponding constructions in the cumulative hierarchy.
<!--zh-->
连接两种描述的桥梁，是识别码化有序对、冯·诺伊曼后继、环境集与 cons 扩展的公式。容器使分量量词保持有界，而充分性引理把这些公式的满足与累积层级中的相应构造联系起来。
<!--ja-->
二つの記述を結ぶのは、符号化順序対、フォン・ノイマン後続、環境集合、cons 拡張を認識する論理式である。容器によって成分をめぐる量化を有界に保ち、妥当性の補題によって、これらの論理式の充足を累積階層の対応する構成と結ぶ。
<!--/-->

<!--en-->
Reading and constructing a coded pair repeatedly requires access to both components. The two-component quantifiers provide this access inside bounded formulas, and their introduction and elimination lemmas preserve the propositional nature of satisfaction. The family `envSet W n` supplies the semantic sets to which those components will be compared.
<!--zh-->
读取或构造码化有序对时，需要反复访问其两个分量。双分量量词在有界公式内部提供这种访问，其引入与消去引理保持满足关系的命题性。族 `envSet W n` 则提供与这些分量比较的语义集合。
<!--ja-->
符号化順序対を読んだり構成したりするには、その二成分へ繰り返しアクセスする必要がある。二成分の量化は有界論理式の内部でこのアクセスを与え、その導入・除去補題は充足が命題であることを保つ。族 `envSet W n` は、それらの成分と比較する意味論的な集合を与える。
<!--/-->

<!--en-->
An environment-set formula determines a set only extensionally. Its agreement theorem compares that description with the constructed `envSet W n`. A common bound and full separation will then collect all arities into one constructible set, while constructible numerals provide its first components.
<!--zh-->
环境集公式只能按外延确定一个集合，其一致定理把这份描述与已构造的 `envSet W n` 比较。随后，公共界与完整分离把所有元数收进一个可构造集合，而可构造数码提供各条目的第一分量。
<!--ja-->
環境集合の論理式が集合を定めるのは外延的にだけである。その一致定理が、この記述を構成済みの `envSet W n` と比較する。続いて、共通の上界と完全な分出がすべてのアリティを一つの構成可能集合へ集め、構成可能な数項が各項目の第一成分を与える。
<!--/-->

<!--en-->
The internal set `ωʟ` connects an object-language arity with an external natural number. Reading one of its members yields, under propositional truncation, a natural number and an identification with the corresponding constructible numeral. It therefore establishes that some arity exists without choosing one globally for every member.
<!--zh-->
内部集合 `ωʟ` 把对象语言中的元数与外围自然数联系起来。读取其成员时，会在命题截断下得到一个自然数，以及该成员与相应可构造数码的同一视。因此，这一读法只确定某个元数存在，并不为每个成员全局选出一个元数。
<!--ja-->
内部集合 `ωʟ` は、対象言語のアリティを外側の自然数と結ぶ。その要素を読むと、命題的切り詰めのもとで、自然数と対応する構成可能な数項との同一視が得られる。したがって、何らかのアリティが存在することは分かるが、各要素に対するアリティを大域的に選ぶことはできない。
<!--/-->

<!--en-->
Finite vectors represent the environments in which formulas are interpreted, while dependent pairs and coproducts express the witnesses and case distinctions returned by their semantics. Natural-number addition accounts for the extra slots introduced by bounded pair readers.
<!--zh-->
有限向量表示解释公式所用的环境，依值对与余积则表达其语义返回的见证和情形分裂。自然数加法记录有界有序对读取器引入的额外槽位。
<!--ja-->
有限ベクトルは論理式を解釈する環境を表し、依存対と直和は、その意味論が返す証人と場合分けを表す。自然数の加法は、有界な順序対の読み取りによって追加されるスロットを数える。
<!--/-->

<!--en-->
Many semantic witnesses in this chapter live under propositional truncation. Such a witness may be used when the target is itself a proposition, as happens for membership, satisfaction, and equality between hierarchy sets, but it cannot be projected into a globally chosen arity or environment. Propositional extensionality and the empty type support the corresponding equality and impossibility arguments.
<!--zh-->
本章许多语义见证都位于命题截断之下。若目标本身是命题，例如隶属、满足关系或层级集合之间的相等，便可以使用这种见证；但不能从中投影出全局选定的元数或环境。命题外延性与空类型分别支持相应的相等和不可能性论证。
<!--ja-->
本章の意味論的な証人の多くは、命題的切り詰めのもとにある。所属、充足、階層の集合どうしの等しさのように、目標自身が命題である場合にはその証人を使えるが、そこから大域的に選ばれたアリティや環境を射影することはできない。命題外延性と空型は、それぞれ対応する等式と不可能性の議論を支える。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
```

<!--en-->
A set in the cumulative hierarchy comes with a small presentation of its members. Passing between membership and the corresponding fibre lets the proof turn an arbitrary member of `W` into a presentation index. The same hierarchy supplies the von Neumann numerals `# n` and their successor operation `sucV`.
<!--zh-->
累积层级中的集合带有其成员的小呈现。在隶属与相应纤维之间转换，使证明能够把 `W` 的任意成员变成一个呈现索引。同一层级还提供冯·诺伊曼数码 `# n` 及其后继运算 `sucV`。
<!--ja-->
累積階層の集合には、その要素の小さな表示が伴う。所属と対応するファイバーの間を移ることで、`W` の任意の要素を表示の添字へ変換できる。同じ階層は、フォン・ノイマン数項 `# n` とその後続演算 `sucV` も与える。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Properties using
  ( ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈-asFiber; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_; sucV )
```

<!--en-->
Write `S` for the type of constructible sets. An element of `S` consists of an underlying hierarchy set together with evidence that it lies in `L`; the proofs below compare underlying sets through the first projection while preserving this evidence when constructing witnesses.
<!--zh-->
以 `S` 表示可构造集合的类型。`S` 的元素由一个底层层级集合及其属于 `L` 的证据组成；下文证明通过第一投影比较底层集合，并在构造见证时保留可构造性证据。
<!--ja-->
構成可能集合の型を `S` と書く。`S` の要素は、基礎となる階層の集合と、それが `L` に属することの証拠からなる。以下の証明では第一射影を通して基礎の集合を比較し、証人を構成するときには構成可能性の証拠を保つ。
<!--/-->

```agda
open hPropStructure 𝒮ʟ using ( S )
```

<!--en-->
Formula satisfaction is interpreted over vectors of constructible sets. Transitivity of `L` connects this internal interpretation with the ambient cumulative hierarchy, so the same underlying membership facts can support both the object-language formulas and the external construction.
<!--zh-->
公式的满足关系在可构造集合向量上解释。`L` 的传递性把这种内部解释与外围累积层级联系起来，因此，同一批底层隶属事实既能支撑对象语言公式，也能支撑外围构造。
<!--ja-->
論理式の充足は、構成可能集合のベクトルの上で解釈される。`L` の推移性がこの内部解釈を周囲の累積階層と結ぶため、同じ基礎的な所属の事実を、対象言語の論理式と外側の構成の両方に用いることができる。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## Constructing the tower set
<!--zh-->
## 构造环境塔集合
<!--ja-->
## 環境の塔を集合として構成する
<!--/-->

<!--en-->
With that interpretation fixed, the first task is to collect all arity-indexed environment sets into one set.
<!--zh-->
固定这一解释后，首要任务便是把按元数索引的所有环境集收进一个集合。
<!--ja-->
この解釈を固定した上で、まずアリティで添字づけられたすべての環境集合を一つの集合に集める。
<!--/-->

<!--en-->
The tower module fixes the carrier `W` whose members are the values environments may take. Its `n`-th entry is the coded ordered pair of the constructible numeral `n` and the set of all environments of length `n`: the first component records the length, the second collects all environments of exactly that length.
<!--zh-->
塔模块固定载体 `W`，环境的取值即其成员。其第 `n` 个条目是「可构造数码 `n` 与长度为 `n` 的全体环境之集」的编码有序对：第一分量记录长度，第二分量收集恰该长度的所有环境。
<!--ja-->
塔のモジュールは、環境が値を取る台 `W` を固定する。その第 `n` 項目は、構成可能な数項 `n` と、長さ `n` のすべての環境の集合との、符号化された順序対である。第一成分が長さを記録し、第二成分がちょうどその長さのすべての環境を集める。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module Tower (W : S) where
```
</summary>
<div class="submodule-fold-content">

```agda
  entry : ℕ → S
  entry n = prʟ (numeralL n) (envSet W n)
```

<!--en-->
The entries are first gathered into a common container by the small-domain principle. The container is only a shared upper bound; the precise collection is carved out by separation next.
<!--zh-->
诸条目先由小定义域原理收进一个公共容器。容器只是公共上界；精确的集合由下一步的分离刻出。
<!--ja-->
項目はまず、小さな定義域の原理によって共通の容器に集められる。容器は共有の上界にすぎず、正確な集合は次の分出で刻まれる。
<!--/-->

```agda
  private
    dom : Σ[ d ∈ S ] ((k : Lift {ℓ-zero} {ℓ} ℕ) → ⟨ fst (entry (lower k)) ∈ fst d ⟩)
    dom = smallDom (Lift {ℓ-zero} {ℓ} ℕ) (λ k → entry (lower k))
```

<!--en-->
The separating formula decomposes a candidate into an arity and an environment set and imposes four conditions: the base-set witness equals `W`; the candidate is the coded ordered pair of the arity and that set; the arity belongs to the internal `ω`; and the set satisfies the first-order, extensional description `envSetAt` at that arity over `W`. Its three leading existential quantifiers are unbounded, so this formula is used with full separation rather than the later Δ₀ argument.
<!--zh-->
分离公式把候选分解为元数与环境集，并施加四个条件：基集见证等于 `W`；候选是该元数与环境集的码化有序对；元数属于内部 `ω`；该集合满足「它是 `W` 上这一元数的环境集」这一一阶外延描述 `envSetAt`。开头三个存在量词无界，因此这里使用完整分离，而非下文的 Δ₀ 论证。
<!--ja-->
分出に用いる論理式は、候補をアリティと環境集合に分解し、四つの条件を課す。基礎集合の証人が `W` と等しいこと、候補がそのアリティと環境集合の符号化された順序対であること、アリティが内部の `ω` に属すること、そしてその集合が `W` 上の当該アリティの環境集合を表す一階の外延的記述 `envSetAt` を満たすことである。冒頭の三つの存在量化子は非有界なので、ここでは後の Δ₀ の議論ではなく完全な分出を用いる。
<!--/-->

```agda
    towerFo : Formula S 1
    towerFo = ∃̇ (∃̇ (∃̇ ( (var i2 ≐ con W)
                      ∧̇ ( prAtL i3 i1 i0
                      ∧̇ ( (var i1 ∈̇ con ωʟ)
                      ∧̇ envSetAt i0 i1 i2 )))))
```

<!--en-->
The tower is carved by separation out of the container and kept opaque, so later arguments use it only through its membership specification.
<!--zh-->
塔由容器上的分离刻出并保持不透明，后文论证只通过其隶属规格使用它。
<!--ja-->
塔は、容器の上の分出によって刻まれ、不透明に保たれる。後の議論は、所属の仕様を通してだけそれを使うのである。
<!--/-->

```agda
  opaque
    tower : S
    tower = hasSeparationL (dom .fst) towerFo .fst .fst
```

<!--en-->
The membership specification is exported: membership in the tower is membership in the container conjoined with satisfaction of the separating formula.
<!--zh-->
隶属规格被导出：塔中的隶属即容器中的隶属且满足分离公式。
<!--ja-->
所属の仕様が輸出される。塔の中の所属とは、容器の中の所属と、分出の論理式の充足の連言である。
<!--/-->

```agda
    tower-mem : (x : S)
              → (fst x ∈ fst tower) ≡ ((fst x ∈ fst (dom .fst)) ⊓ ((x ∷ []) ⊨ towerFo))
    tower-mem = hasSeparationL (dom .fst) towerFo .fst .snd
```

<!--en-->
The key ingredient is that each environment set satisfies its own external description at its own entry: the environment set, its numeral, the carrier, and the entry are placed in a four-slot environment, and the description is satisfied there by construction.
<!--zh-->
关键材料是：每个环境集在其自身条目处满足其外延描述。环境集、其数码、载体与条目被置入四槽环境，而描述在该处按构造成立。
<!--ja-->
重要な材料は、各環境集合がその自身の項目のもとで外延的な記述を満たすことである。環境集合・その数項・台・項目が四つの枠の環境に置かれ、記述は構成によってそこで成立する。
<!--/-->

```agda
  private
    holdsAt : (n : ℕ) → ⟨ (envSet W n ∷ numeralL n ∷ W ∷ entry n ∷ []) ⊨ envSetAt i0 i1 i2 ⟩
    holdsAt n = AmbientHolds.holds W (envSet W n ∷ numeralL n ∷ W ∷ entry n ∷ [])
                  i0 i1 i2 n refl (numeralL-fst n) refl
```

<!--en-->
Every standard entry therefore belongs to the tower: the container membership is supplied by the bounding record, and the separating formula is satisfied by the truncated witness built from the carrier, the numeral, and the environment set.
<!--zh-->
于是每个标准条目都属于塔：容器隶属由界定记录供给，分离公式由载体、数码与环境集构成的截断见证满足。
<!--ja-->
したがって、すべての正準な項目は塔の中にある。容器への所属は界定の記録から供給され、分出の論理式は、台・数項・環境集合から作られた切り詰められた証人によって充足される。
<!--/-->

```agda
    tower-in : (n : ℕ) → ⟨ fst (entry n) ∈ fst tower ⟩
    tower-in n = subst ⟨_⟩ (sym (tower-mem (entry n)))
      ( dom .snd (lift n)
      , ∣ W , ∣ numeralL n , ∣ envSet W n
        , ( refl
```

<!--en-->
The witness tree nests the carrier, the constructible numeral, and the environment set, and each level transports its own component: the ordered pair is recognized through the pairing projection law, the numeral membership through the internal `ω` reading, and the description by the ingredient above.
<!--zh-->
见证树嵌套载体、可构造数码与环境集，每一层各自搬运其分量：有序对经配对投影法则被识别，数码隶属经内部 `ω` 读法识别，而描述由上述材料满足。
<!--ja-->
証人の木は、台・構成可能な数項・環境集合を入れ子にし、それぞれの層が自分の成分を運ぶ。順序対は対の射影の法則で認められ、数項の所属は内部の `ω` の読みで、記述は上の材料によって充足される。
<!--/-->

```agda
          , ( pr-in i3 i1 i0 (envSet W n ∷ numeralL n ∷ W ∷ entry n ∷ [])
                (prʟ-fst (numeralL n) (envSet W n))
            , ( subst ⟨_⟩ (sym (ω-specL (numeralL n))) ∣ lift n , refl ∣₁
              , holdsAt n ))) ∣₁ ∣₁ ∣₁ )
```

<!--en-->
The standard entry is then restated in ambient normal form: the coded pair of the constructible numeral and the environment set has the same underlying ordered pair as the plain pair of the numerals and the underlying stage, by the two projection laws.
<!--zh-->
标准条目随后以外围标准形重述：由两条投影法则，可构造数码与环境集的编码对的底层有序对，等于数码与底层层的朴素对。
<!--ja-->
正準な項目は、周囲の標準形で言い直される。構成可能な数項と環境集合の符号化された対の底の順序対は、二つの射影の法則によって、数項と底の段階の対に等しくなる。
<!--/-->

```agda
  tower-in′ : (n : ℕ) → ⟨ pr (# n) (fst (envSet W n)) ∈ fst tower ⟩
  tower-in′ n = subst (λ u → ⟨ u ∈ fst tower ⟩)
    (prʟ-fst (numeralL n) (envSet W n) ∙ cong (λ u → pr u (fst (envSet W n))) (numeralL-fst n))
    (tower-in n)
```

<!--en-->
Conversely, membership in the constructed tower can be read out: every member is merely the coded pair of a numeral and the environment set of that length. The natural number and the equality are returned under propositional truncation, so this result records existence without defining a choice of arity for every member. The proof first unfolds the membership specification and retains its separating-formula component.
<!--zh-->
反之，可以读出所构造环境塔的成员：每个成员仅仅是某个数码与相应长度环境集的码化有序对。自然数及其等式位于命题截断之下，因此该结论只记录存在性，并未为每个成员定义一个元数选择。证明先展开隶属规格，再取出其中满足分离公式的分量。
<!--ja-->
逆に、構成した環境の塔の所属を読み出せる。各要素は、ある数項とその長さの環境集合との符号化された順序対であることが命題的切り詰めのもとで得られる。自然数と等式は命題的切り詰めの内側にあるため、この結果は存在を記録するだけで、各要素のアリティを選ぶ関数を定めない。証明はまず所属の仕様を展開し、分出論理式を満たす成分を取り出す。
<!--/-->

```agda
  tower-out : (x : S) → ⟨ fst x ∈ fst tower ⟩
            → ∥ Σ[ n ∈ ℕ ] (fst x ≡ pr (# n) (fst (envSet W n))) ∥₁
  tower-out x hx = rec₁ squash₁ byB (subst ⟨_⟩ (tower-mem x) hx .snd)
    where
    Goal : Type (ℓ-suc ℓ)
```

<!--en-->
The target type makes that boundary explicit: it is the propositional truncation of a natural number `n` together with an equality from the member’s underlying set to the standard pair `pr (# n) (fst (envSet W n))`.
<!--zh-->
目标类型明确表达这一边界：它是命题截断，其中仅仅存在自然数 `n`，并有从该成员的底层集合到标准有序对 `pr (# n) (fst (envSet W n))` 的等式。
<!--ja-->
目標の型はこの境界を明示する。自然数 `n` と、要素の台集合から標準的な順序対 `pr (# n) (fst (envSet W n))` への等式との組を命題的に切り詰めた型である。
<!--/-->

```agda
    Goal = ∥ Σ[ n ∈ ℕ ] (fst x ≡ pr (# n) (fst (envSet W n))) ∥₁
```

<!--en-->
The separating formula binds three witnesses. The first elimination names the base-set witness `b`; the remaining formula will identify it with `W` while also exposing the arity and environment-set witnesses.
<!--zh-->
分离公式绑定三个见证。第一次消去命名基集见证 `b`；余下的公式随后把它与 `W` 认同，并继续暴露元数见证和环境集见证。
<!--ja-->
分出論理式は三つの証人を束縛する。最初の除去で基礎集合の証人 `b` に名前を付ける。残る論理式はこれを `W` と同定し、さらにアリティと環境集合の証人を取り出す。
<!--/-->

```agda
    byB : Σ[ b ∈ S ] ⟨ (b ∷ x ∷ []) ⊨ ∃̇ (∃̇ ( (var i2 ≐ con W)
                    ∧̇ ( prAtL i3 i1 i0
                    ∧̇ ( (var i1 ∈̇ con ωʟ)
                    ∧̇ envSetAt i0 i1 i2 )))) ⟩ → Goal
    byB (b , hb) = rec₁ squash₁ byN hb
```

<!--en-->
The second elimination names the arity as a constructible set.
<!--zh-->
第二次消去把元数命名为可构造集合。
<!--ja-->
二つ目の消去は、アリティを構成可能な集合として名指す。
<!--/-->

```agda
      where
      byN : Σ[ n ∈ S ] ⟨ (n ∷ b ∷ x ∷ []) ⊨ ∃̇ ( (var i2 ≐ con W)
                    ∧̇ ( prAtL i3 i1 i0
                    ∧̇ ( (var i1 ∈̇ con ωʟ)
                    ∧̇ envSetAt i0 i1 i2 ))) ⟩ → Goal
```

<!--en-->
The third elimination names the environment set and exposes the four conjuncts: the base set is `W`, the ordered pair is recognized, the arity is in the internal `ω`, and the external description of the environment set holds.
<!--zh-->
第三次消去命名环境集并暴露四个合取支：基集是 `W`、有序对被识别、元数属于内部 `ω`，且环境集的外延描述成立。
<!--ja-->
三つ目の消去は環境集合を名指し、四つの連言支を露わにする。基の集合が `W` であること、順序対が認められること、アリティが内部の `ω` に属すること、そして環境集合の外延的な記述が成り立つことである。
<!--/-->

```agda
      byN (n , hn) = rec₁ squash₁ byE hn
        where
        byE : Σ[ F ∈ S ] ⟨ (F ∷ n ∷ b ∷ x ∷ []) ⊨ ( (var i2 ≐ con W)
                    ∧̇ ( prAtL i3 i1 i0
                    ∧̇ ( (var i1 ∈̇ con ωʟ)
```

<!--en-->
The ordered-pair reader recovers the equality from the member to the coded pair of the arity and the described set. Membership of the arity in the internal `ω` then yields, under propositional truncation, an ordinary natural number whose constructible numeral has the same underlying set.
<!--zh-->
有序对读取器恢复从该成员到「元数与所描述集合的码化有序对」的等式。随后，元数属于内部 `ω` 这一事实在命题截断之下给出一个普通自然数，其可构造数码具有相同的底层集合。
<!--ja-->
順序対の読み取りにより、要素からアリティと記述された集合との符号化された順序対への等式が得られる。次に、アリティが内部の `ω` に属することから、同じ台集合をもつ構成可能な数項に対応する通常の自然数が、命題的切り詰めのもとで得られる。
<!--/-->

```agda
                    ∧̇ envSetAt i0 i1 i2 ))) ⟩ → Goal
        byE (F , (qb , (hp , (hω , hE)))) = rec₁ squash₁ byK (subst ⟨_⟩ (ω-specL n) hω)
          where
          xq : fst x ≡ pr (fst n) (fst F)
          xq = pr-out i3 i1 i0 (F ∷ n ∷ b ∷ x ∷ []) hp
```

<!--en-->
The numeral identification aligns the recorded arity with the constructible numeral of the natural number, and the environment-agreement module is opened at the four-slot environment, prepared to compare the described set with the constructed one.
<!--zh-->
数码同一视把被记录的元数与该自然数的可构造数码对齐；环境一致模块在四槽环境处打开，准备比较被描述的集合与实际构造的集合。
<!--ja-->
数項の同一視が、記録されたアリティをその自然数の構成可能な数項と整列させ、環境の一致のモジュールが、四つの枠の環境のもとで開かれ、記述された集合と実際に構成された集合を比較する準備をする。
<!--/-->

```agda
          byK : Σ[ k ∈ Lift {ℓ-zero} {ℓ-suc ℓ} ℕ ] (fst n ≡ fst (numeralL (lower k))) → Goal
          byK (k , qn) = ∣ lower k , xq ∙ cong₂ pr (qn ∙ numeralL-fst (lower k)) Eq ∣₁
            where
            module Am = Ambient W (F ∷ n ∷ b ∷ x ∷ []) i0 i1 i2 (lower k)
                          (qn ∙ numeralL-fst (lower k)) qb hE using (into; outof)
```

<!--en-->
The agreement module supplies both directions of membership between the described set and the constructed environment set, and extensionality inside `L` converts these two directions into an equality of underlying sets.
<!--zh-->
一致模块供给被描述集与实际环境集之间隶属的两个方向；`L` 内的外延性把这两个方向转换为底层集合的等式。
<!--ja-->
一致のモジュールは、記述された集合と実際に構成された環境集合の間の所属の両方向を供給する。そして `L` の内部の外延性が、この二つの方向を、底の集合の等式に変える。
<!--/-->

```agda
            Eq : fst F ≡ fst (envSet W (lower k))
            Eq = cong fst (extensionalL {a = F} {b = envSet W (lower k)}
              (λ z → ⇔toPath (Am.into z) (Am.outof z)))
```
</div>
</details>

<!--en-->
## A bounded specification of the tower
<!--zh-->
## 环境塔的有界规格
<!--ja-->
## 環境の塔の有界な仕様
<!--/-->

<!--en-->
The emptiness predicate says that a set has no members at all, by a bounded universal over its members.
<!--zh-->
空性谓词说一个集合全无成员，由对其成员的有界全称表达。
<!--ja-->
空性の述語は、集合がまったく要素をもたないことを、その要素の上の有界の全称で言う。
<!--/-->

```agda
emptyAll : ∀ {m} → Fin m → Formula S m
emptyAll x = ∀̇∈ (var x) ⊥̇
```

<!--en-->
The singleton-of-empty clause has two conjuncts: the set contains an empty member, and every member of it is empty. Both are needed: the first is an existence clause, and without it the predicate would also hold of the empty set itself.
<!--zh-->
空集单点子句有两个合取支：该集合含有一个空成员，且其每个成员都是空的。两者都需要：第一个是存在子句，没有它该谓词也会对空集自身成立。
<!--ja-->
空集合の単元の節には二つの連言支がある。その集合が空の要素を一つ含むことと、そのすべての要素が空であることである。両方が要る。最初のものは存在の条項であり、これがなければ、この述語は空集合自身についても成り立ってしまう。
<!--/-->

```agda
sglEmpty : ∀ {m} → Fin m → Formula S m
sglEmpty F = ∃̇∈ (var F) (emptyAll i0) ∧̇ ∀̇∈ (var F) (emptyAll i0)
```

<!--en-->
The cons-image clause gives both inclusions needed for equality. Every member of the proposed successor set must merely be a cons of some carrier element onto some member of the predecessor set. Conversely, for every predecessor environment and every carrier element, a corresponding cons extension must merely occur in the successor set. Together these conditions say that the successor set has exactly the cons extensions and no additional members.
<!--zh-->
cons 像子句给出集合相等所需的两个包含方向。所提议后继集的每个成员都必须仅仅是某个载体元素接到某个前驱集成员之前所得的 cons；反过来，对每个前驱环境与每个载体元素，相应的 cons 扩展都必须仅仅出现于后继集中。两项合起来说明后继集恰含这些 cons 扩展而无额外成员。
<!--ja-->
cons 像の節は、集合の等しさに必要な二方向の包含を与える。候補となる後続集合の各要素は、ある台の要素をある前段の環境に cons して得られるものでなければならない。逆に、各前段の環境と各台の要素に対して、対応する cons 拡張が後続集合に存在しなければならない。両条件を合わせると、後続集合はそれらの cons 拡張だけをちょうど含む。
<!--/-->

```agda
consImage : ∀ {m} → Fin m → Fin m → Fin m → Formula S m
consImage F' F w =
    ∀̇∈ (var F') (∃̇∈ (var (sh 1 w)) (∃̇∈ (var (sh 2 F)) (consAtL i2 i1 i0)))
  ∧̇ ∀̇∈ (var F) (∀̇∈ (var (sh 1 w)) (∃̇∈ (var (sh 2 F')) (consAtL i0 i1 i2)))
```

<!--en-->
The two bodies describe one adjacent step after the current entry has been decomposed into an arity and an environment set. `upBody` says that the new arity is the successor of the current arity and that the new environment set is its cons image. `downBody` reverses these roles: the current arity is the successor of the predecessor arity, and the current environment set is the cons image of the predecessor set.
<!--zh-->
当前条目被分解为元数与环境集后，这两个主体描述相邻的一步。`upBody` 说新元数是当前元数的后继，且新环境集是当前环境集的 cons 像。`downBody` 反转这些角色：当前元数是前驱元数的后继，且当前环境集是前驱环境集的 cons 像。
<!--ja-->
現在の項目をアリティと環境集合に分解した後、この二つの本体が隣接する一段を記述する。`upBody` は、新しいアリティが現在のアリティの後続であり、新しい環境集合が現在の環境集合の cons 像であることを述べる。`downBody` は役割を逆にし、現在のアリティが前段のアリティの後続であり、現在の環境集合が前段の環境集合の cons 像であることを述べる。
<!--/-->

```agda
private
  upBody downBody : ∀ {m} → Fin m → Formula S (8 + m)
  upBody w = sucAtL i5 i1 ∧̇ consImage i0 i4 (sh 8 w)
  downBody w = sucAtL i1 i5 ∧̇ consImage i4 i0 (sh 8 w)
```

<!--en-->
The upward clause exists over the tower: some entry of the tower satisfies the upward body.
<!--zh-->
向上子句在塔上作存在量化：塔中某条目满足向上主体。
<!--ja-->
上向きの節は、塔の上で存在量化される。塔のある項目が上向きの本体を満たすのである。
<!--/-->

```agda
  towerUp : ∀ {m} → Fin m → Fin m → Formula S (4 + m)
  towerUp E w = ∃̇∈ (var (sh 4 E)) (bothEx i0 (upBody w))
```

<!--en-->
The downward clause is a disjunction: the entry equals the base entry with an empty environment set, or some tower entry is a predecessor whose cons image is the current one. This is what supports the membership-induction reading below.
<!--zh-->
向下子句是一个析取：条目等于带空环境集的基条目，或塔中某条目是其 cons 像为当前条目的前驱。这正是下文隶属归纳读法所依赖的。
<!--ja-->
下向きの節は選言である。その項目が、空の環境集合をもつ基底の項目と等しいか、あるいは、塔のある項目が、その cons の像が現在の項目である先行者であるかのどちらかである。これが、後の所属帰納の読みを支える。
<!--/-->

```agda
  towerDown : ∀ {m} → Fin m → Fin m → Fin m → Formula S (4 + m)
  towerDown E w N0 =
      ((var i1 ≐ var (sh 4 N0)) ∧̇ sglEmpty i0)
    ∨̇ ∃̇∈ (var (sh 4 E)) (bothEx i0 (downBody w))
```

<!--en-->
The full formula conjoins three bounded conditions on coded ordered-pair entries: a base pair occurs in `E`; every member of `E` that is read through the pair interface has an upward successor; and every such pair is either a base pair or has a predecessor. Thus `towerAt` controls the coded ordered-pair entries used by the later readers. It does not by itself exclude arbitrary non-pair members of `E`, nor does this chapter derive equality of an arbitrary satisfying `E` with the constructed `Tower.tower W`.
<!--zh-->
完整公式合取了关于码化有序对条目的三个有界条件：`E` 中出现一个基准对；`E` 中每个经有序对接口读出的成员都有向上的后继；每个这样的对要么是基准对，要么具有前驱。因此，`towerAt` 控制的是后文读取器所使用的码化有序对条目。它本身不排除 `E` 中任意的非有序对成员，本章也没有由任意 `E` 满足该公式推出它等于所构造的 `Tower.tower W`。
<!--ja-->
完全な論理式は、符号化された順序対の項目について三つの有界な条件を連言する。基底の対が `E` に存在すること、`E` のうち順序対のインターフェースを通して読まれる各要素に上向きの後続があること、そしてそのような各対が基底の対であるか前段をもつことである。したがって、`towerAt` が制御するのは、後の読み取りで用いる符号化された順序対の項目である。それだけでは `E` の任意の非順序対要素を排除せず、本章は、この論理式を満たす任意の `E` が構成した `Tower.tower W` と等しいことも導かない。
<!--/-->

```agda
towerAt : ∀ {m} → Fin m → Fin m → Fin m → Formula S m
towerAt E w N0 =
    ∃̇∈ (var E) (sndEx i0 (sh 1 N0) (sglEmpty i0))
  ∧̇ ( ∀̇∈ (var E) (bothAll i0 (towerUp E w))
    ∧̇ ∀̇∈ (var E) (bothAll i0 (towerDown E w N0)) )
```

<!--en-->
The Δ₀ certificate is produced by the checker. It certifies only that every quantifier is bounded; the semantic correctness of the formula is established by the reading lemmas below, not by this certificate.
<!--zh-->
Δ₀ 证书由检查器产出。它只证明每个量词都有界；公式的语义正确性由下文读取引理另行建立，而非由该证书证明。
<!--ja-->
Δ₀ の証拠は検査によって産み出される。それは、すべての量化子が有界であることだけを証明する。論理式の意味論的な正しさは、後の読みの補題が別に確立するのであって、この証拠によるものではない。
<!--/-->

```agda
Δ₀-towerAt : ∀ {m} (E w N0 : Fin m) → Δ₀ (towerAt E w N0)
Δ₀-towerAt E w N0 = checkΔ₀ (towerAt E w N0) tt
```

<!--en-->
## The zero and successor environment sets
<!--zh-->
## 零元与后继元数的环境集
<!--ja-->
## 零アリティと後続アリティの環境集合
<!--/-->

<!--en-->
The facts module fixes the carrier `W` and collects the concrete recursion facts about zero-length and successor-length environments.
<!--zh-->
事实模块固定载体 `W`，并收集关于零长与后继长环境的实际递推事实。
<!--ja-->
事実のモジュールは台 `W` を固定し、長さゼロと後続の長さの環境についての実際の再帰の事実を集める。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module EnvFacts (W : S) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
    ι : ⟪ fst W ⟫ → V ℓ
    ι = ⟪ fst W ⟫↪
```

<!--en-->
Every presented index names a member of `W`: the small membership bridge runs from the presentation into the underlying set.
<!--zh-->
每个被呈现索引指名 `W` 的一个成员：小隶属桥从呈现通入底层集合。
<!--ja-->
提示された索引はどれも `W` の要素を名指す。小さな所属の橋が、提示から底の集合の中へ続くのである。
<!--/-->

```agda
    ι∈ : (q : ⟪ fst W ⟫) → ⟨ ι q ∈ fst W ⟩
    ι∈ q = ∈∈ₛ {a = ι q} {b = fst W} .snd (∈ₛ⟪ fst W ⟫↪ q)
```

<!--en-->
There is exactly one index of length zero, and it is recognized because a function out of an empty type is defined by its impossible cases.
<!--zh-->
长度为零的索引恰有一个，其识别源于「从空类型出发的函数由不可能情形定义」。
<!--ja-->
長さゼロの索引はちょうど一つであり、それは、空の型からの関数がその不可能な場合によって定義されることから認められる。
<!--/-->

```agda
    g0 : Ix W 0
    g0 ()
```

<!--en-->
A set with no members equals the zero-length environment graph, by extensionality: neither side has a member, since the zero-length index has no cases.
<!--zh-->
无成员的集合等于零长环境图，由外延性：两侧都没有成员，因为零长索引没有情形。
<!--ja-->
要素をもたない集合は、長さゼロの環境のグラフと等しくなる。外延性による。長さゼロの索引には場合がないので、どちらの側にも要素はないのである。
<!--/-->

```agda
  noMembers→env0 : (z : V ℓ) → ((y : V ℓ) → ⟨ y ∈ z ⟩ → ⊥₀) → z ≡ fst (envS W g0)
  noMembers→env0 z k = extensionalV (λ y → ⇔toPath
    (λ hy → ⊥₀-rec (k y hy))
    (rec₁ (snd (y ∈ z)) (λ { (lift () , _) })))
```

<!--en-->
Conversely, every environment graph of length zero has no members: the index has no cases, so the pair that would encode a member cannot be formed.
<!--zh-->
反过来，长度为零的每个环境图都没有成员：索引没有情形，故编码成员所需的对无法形成。
<!--ja-->
逆に、長さゼロのどの環境のグラフも要素をもたない。索引に場合がないので、要素を符号化する対が作れないのである。
<!--/-->

```agda
  envAny0-noMembers : (g : Ix W 0) (y : V ℓ) → ⟨ y ∈ fst (envS W g) ⟩ → ⊥₀
  envAny0-noMembers g y = rec₁ isProp⊥ (λ { (lift () , _) })
```

<!--en-->
Reading the zero-length environment set out: every member is a set with no members. The proof eliminates the truncated presentation and applies the previous fact.
<!--zh-->
读出零长环境集：其每个成员都是无成员的集合。证明消去截断的呈现并应用前述事实。
<!--ja-->
長さゼロの環境集合を読み出すと、そのすべての要素は要素をもたない集合である。証明は、切り詰められた提示を消去して、前の事実を適用する。
<!--/-->

```agda
  envSet0-out : (z : V ℓ) → ⟨ z ∈ fst (envSet W 0) ⟩
              → (y : V ℓ) → ⟨ y ∈ z ⟩ → ⊥₀
  envSet0-out z hz y hy = rec₁ isProp⊥
    (λ { (g , e) → envAny0-noMembers g y (subst (λ u → ⟨ y ∈ u ⟩) e hy) })
    (envSet-out W 0 (down (envSet W 0) z hz) hz)
```

<!--en-->
Filling the zero-length environment set uses the empty set: it is transported into the presentation, and the empty graph is recognized from its no-members proof.
<!--zh-->
填充零长环境集使用空集：它被搬运进呈现，而空图由其无成员证明被识别。
<!--ja-->
長さゼロの環境集合の埋めは空集合を使う。それは提示の中へ運ばれ、空のグラフはその要素がないことの証明によって認められる。
<!--/-->

```agda
  envSet0-in : (z : V ℓ) → ((y : V ℓ) → ⟨ y ∈ z ⟩ → ⊥₀) → ⟨ z ∈ fst (envSet W 0) ⟩
  envSet0-in z k = subst (λ u → ⟨ u ∈ fst (envSet W 0) ⟩) (sym (noMembers→env0 z k)) (envSet-in W g0)
```

<!--en-->
The environment coding agrees with cons at the function level: prepending a carrier element and shifting the indices codes exactly the cons of the coded functions, entry by entry.
<!--zh-->
环境编码在函数层与 cons 一致：前置一个载体元素并移动索引，逐条目地恰好编码了编码函数的 cons。
<!--ja-->
環境の符号化は、関数の水準で cons と一致する。台の要素を先頭に加え、索引をずらすと、符号化された関数の cons を項目ごとにちょうど符号化するのである。
<!--/-->

```agda
  cons-env : (q : ⟪ fst W ⟫) {k : ℕ} (g : Ix W k)
           → env (cons (ι q) (λ i → ι (g i))) ≡ fst (envS W (cons q g))
  cons-env q g = cong env (funExt (λ { zero → refl ; (suc i) → refl }))
```

<!--en-->
Every carrier element extends every environment of length `k` to an environment of length `suc k`: the new member of `W` is presented by an index, and the extended function is inserted into the successor environment set.
<!--zh-->
`W` 的每个成员把每个长度为 `k` 的环境延拓为长度 `suc k` 的环境：`W` 的新成员由一个索引呈现，延拓后的函数被插入后继环境集。
<!--ja-->
台 `W` のすべての要素は、長さ `k` のどの環境も、長さ `suc k` の環境へ延長する。`W` の新しい要素は索引で提示され、延長された関数が、後続の環境集合の中に挿入される。
<!--/-->

```agda
  envCons∈ : {k : ℕ} (x : V ℓ) → ⟨ x ∈ fst W ⟩ → (g : Ix W k)
           → ⟨ env (cons x (λ i → ι (g i))) ∈ fst (envSet W (suc k)) ⟩
  envCons∈ {k} x x∈ g =
    subst (λ u → ⟨ u ∈ fst (envSet W (suc k)) ⟩)
      (sym (cong (λ v → env (cons v (λ i → ι (g i)))) (sym (fib .snd)) ∙ cons-env (fib .fst) g))
```

<!--en-->
The presenting index is recovered from the membership through the fiber of the presentation, so the coding uses the actual presenting index of `x`.
<!--zh-->
呈现索引经呈现在该成员处的纤维恢复，因此编码使用的是 `x` 的实际呈现索引。
<!--ja-->
提示の索引は、その要素における提示の繊維を通して復元されるので、符号化は `x` の実際の提示の索引を使う。
<!--/-->

```agda
      (envSet-in W (cons (fib .fst) g))
    where
    fib : Σ[ q ∈ ⟪ fst W ⟫ ] (ι q ≡ x)
    fib = ∈-asFiber {a = x} {b = fst W} x∈
```

<!--en-->
The insertion is restated for a constructible element with an identification of its underlying set: membership in the successor environment set follows by transporting along that identification.
<!--zh-->
该插入对「带底层集同一视的可构造元素」重述：沿该同一视搬运，即得属于后继环境集。
<!--ja-->
この挿入は、底の集合の同一視をもつ構成可能な要素に対して言い直される。その同一視に沿って運ぶことで、後続の環境集合への所属が従う。
<!--/-->

```agda
  envSuc-in : {k : ℕ} (x e' : S) → ⟨ fst x ∈ fst W ⟩ → (g : Ix W k)
            → fst e' ≡ env (cons (fst x) (λ i → ι (g i)))
            → ⟨ fst e' ∈ fst (envSet W (suc k)) ⟩
  envSuc-in {k} x e' x∈ g qe' =
    subst (λ u → ⟨ u ∈ fst (envSet W (suc k)) ⟩) (sym qe') (envCons∈ (fst x) x∈ g)
```

<!--en-->
A successor environment splits at the function level into a head and a tail. If `g'` indexes a successor environment, then its underlying set equals the coded graph of the function whose zero-th entry is the head value `ι (g' zero)` and whose `i+1`-st entry is `ι (g' (suc i))`. The proof is the functoriality of the environment constructor under the function extensionality that says the two index functions agree at every slot.
<!--zh-->
后继环境在函数层拆为头部与尾部。若 `g'` 索引一个后继环境，则其底层集合等于以 `ι (g' zero)` 为零号条目、以 `ι (g' (suc i))` 为第 `i+1` 条目的编码图。证明依赖于环境构造子在函数外延性下的函数性，后者说两个索引函数在每个槽位处取值相同。
<!--ja-->
後続の環境は、関数のレベルで先頭と尾部に分かれる。`g'` が後続の環境に添字づけられているなら、その基礎の集合は、零番目の項目が `ι (g' zero)`、第 `i+1` 項目が `ι (g' (suc i))` であるような符号化されたグラフと等しくなる。証明は、二つの添字の関数がすべての枠で同じ値をもつという関数外延性のもとでの、環境の構成子の関数性による。
<!--/-->

```agda
  env-split : {k : ℕ} (g' : Ix W (suc k))
            → fst (envS W g') ≡ env (cons (ι (g' zero)) (λ i → ι (g' (suc i))))
  env-split g' = cong env (funExt (λ { zero → refl ; (suc i) → refl }))
```

<!--en-->
The outward reading of a successor environment recovers its head and tail only under propositional truncation. For each member `e'` of `envSet W (suc k)`, there merely exist a presentation index `q` naming a member `ι q` of `W`, a tail index `g : Ix W k`, and an equality identifying the underlying set of `e'` with the coded graph of their cons function.
<!--zh-->
后继环境的向外读法只在命题截断下恢复其头部与尾部。对 `envSet W (suc k)` 的每个成员 `e'`，仅仅存在一个呈现索引 `q`、一个尾部索引 `g : Ix W k` 及一条等式，其中 `q` 指名 `W` 的成员 `ι q`，而该等式把 `e'` 的底层集合识别为二者 cons 函数的码化图。
<!--ja-->
後続環境の外向きの読み出しが先頭と尾部を復元するのは、命題的切り詰めのもとでだけである。`envSet W (suc k)` の各要素 `e'` に対して、`W` の要素 `ι q` を名指す表示添字 `q`、尾部の添字 `g : Ix W k`、および `e'` の基礎の集合を両者の cons 関数の符号化グラフと同定する等式が単に存在する。
<!--/-->

```agda
  envSuc-out : {k : ℕ} (e' : S) → ⟨ fst e' ∈ fst (envSet W (suc k)) ⟩
             → ∥ Σ[ q ∈ ⟪ fst W ⟫ ] Σ[ g ∈ Ix W k ]
                  (fst e' ≡ env (cons (ι q) (λ i → ι (g i)))) ∥₁
  envSuc-out {k} e' h = map₁
    (λ { (g' , e) → g' zero , (λ i → g' (suc i)) , (e ∙ env-split g') })
```

<!--en-->
The membership proof is consumed by the outward reading of the environment set, which supplies the truncated index; the equation of the graph then composes with the splitting lemma to produce the cons equation.
<!--zh-->
隶属证明被环境集的向外读法消耗，后者供给截断的索引；图的等式再与拆分引理复合，产出 cons 等式。
<!--ja-->
所属の証明は、環境の集合の外向きの読み出しに消費され、切り詰められた添字を供給する。グラフの等式は、分かちの補題と合成されて、cons の等式を作る。
<!--/-->

```agda
    (envSet-out W (suc k) e' h)
```
</div>
</details>

<!--en-->
## Reading the successor construction
<!--zh-->
## 读取后继环境的构造
<!--ja-->
## 後続環境の構成を読む
<!--/-->

<!--en-->
The cons-image reader is parameterized by the candidate successor set `F'`, the candidate base set `F`, the alphabet slot `w`, and the environment, together with the equation aligning the alphabet slot with the working set.
<!--zh-->
cons 像读取器以候选后继集 `F'`、候选基集 `F`、字母表槽 `w` 与环境为参数，连同把字母表槽与工作集对齐的等式。
<!--ja-->
cons の像の読み手は、候補の後続の集合 `F'`、候補の基底の集合 `F`、アルファベットの枠 `w`、そして環境をパラメータとし、アルファベットの枠を作業集合と揃える等式を伴う。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module ConsImageRead {m : ℕ} (F' F w : Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) where
```
</summary>
<div class="submodule-fold-content">

```agda
  open EnvFacts W
  private
    ι : ⟪ fst W ⟫ → V ℓ
```

<!--en-->
The embedding of the carrier into the hierarchy is named once, so that every carrier element can be presented as a hierarchy element when needed by the coding.
<!--zh-->
载体到层级的嵌入只命名一次，使每个载体元素可在编码需要时呈现为层级元素。
<!--ja-->
台から階層への埋め込みは一度だけ名づけられ、符号化が必要とするときに、台のすべての要素を階層の要素として提示できるようにする。
<!--/-->

```agda
    ι = ⟪ fst W ⟫↪
```

<!--en-->
For each `q` in the carrier of `W`, the presentation map places `ι q` in the underlying set of `W`. The proof reads membership from the fibre supplied by the canonical presentation of that set.
<!--zh-->
对 `W` 载体中的每个 `q`，呈现映射都把 `ι q` 放入 `W` 的底层集合。证明从该集合的典范呈现所给出的 fibre 中读出隶属。
<!--ja-->
`W` の台の各 `q` に対して、提示写像は `ι q` を `W` の基礎の集合に入れる。証明は、その集合の標準的な提示が与えるファイバーから所属を読み取る。
<!--/-->

```agda
    ι∈' : (q : ⟪ fst W ⟫) → ⟨ ι q ∈ fst W ⟩
    ι∈' q = ∈∈ₛ {a = ι q} {b = fst W} .snd (∈ₛ⟪ fst W ⟫↪ q)
```

<!--en-->
The outward reading of the cons-image clause says: if the base set equals the stage environment set at `k`, then a set satisfying the cons-image clause equals the successor stage environment set. The proof is by extensionality, comparing members in two directions.

The forward direction reads a member `z` of the candidate successor set through the cons-image clause.
<!--zh-->
cons 像子句的向外读法说：若基集等于 `k` 处的层环境集，则满足 cons 像子句的集合等于后继层环境集。证明以外延性比较成员于两个方向。

向前方向经 cons 像子句读取候选后继集的成员 `z`。
<!--ja-->
cons の像の条項の外向きの読み出しはこう言う。基底の集合が `k` での段階の環境の集合に等しいなら、cons の像の条項を満たす集合は、後続の段階の環境の集合に等しい、と。証明は、二方向で要素を比較する外延性である。

前向きの方向は、cons の像の条項を通して、候補の後続の集合の要素 `z` を読む。
<!--/-->

```agda
  consImage-out : (k : ℕ) → fst (lookup F γ) ≡ fst (envSet W k)
                → ⟨ γ ⊨ consImage F' F w ⟩ → fst (lookup F' γ) ≡ fst (envSet W (suc k))
  consImage-out k qF (h1 , h2) = extensionalV (λ z → ⇔toPath (fwd z) (bwd z))
    where
    fwd : (z : V ℓ) → ⟨ z ∈ fst (lookup F' γ) ⟩ → ⟨ z ∈ fst (envSet W (suc k)) ⟩
```

<!--en-->
The clause supplies a carrier element `x` and a coded environment entry `e` and the cons equation; the environment-set outward reading at the base set supplies a truncated index `g`. Each truncated witness is eliminated into the next proposition.
<!--zh-->
子句供给载体元素 `x`、编码环境条目 `e` 与 cons 等式；基集的环境集向外读法供给截断索引 `g`。每个截断见证都被消去到下一条命题。
<!--ja-->
条項は、台の要素 `x` と、符号化された環境の項目 `e` と、cons の等式を供給する。基底の集合の環境の集合の外向きの読み出しが、切り詰められた添字 `g` を供給する。それぞれの切り詰められた証人は、つぎの命題へ消去される。
<!--/-->

```agda
    fwd z hz = rec₁ (snd (z ∈ fst (envSet W (suc k))))
      (λ { (x , (x∈ , hx)) → rec₁ (snd (z ∈ fst (envSet W (suc k))))
        (λ { (e , (e∈ , hc)) → rec₁ (snd (z ∈ fst (envSet W (suc k))))
          (λ { (g , qe) →
            envSuc-in x zS (subst (λ u → ⟨ fst x ∈ u ⟩) qw x∈) g
```

<!--en-->
In the forward inclusion, the first half of the cons-image clause supplies a head `x`, a tail environment `e`, and satisfaction of the coded cons relation. Reading `e` in the actual base environment set yields a tail index under propositional truncation. Adequacy of `consAtL` then identifies `z` with the semantic cons graph, and `envSuc-in` places that graph in `envSet W (suc k)`. Every truncation is eliminated into this membership proposition.
<!--zh-->
在向前包含中，cons 像子句的前半部给出头部 `x`、尾环境 `e`，以及码化 cons 关系的满足。把 `e` 作为真实基环境集的成员读取，会在命题截断下得到一个尾部索引。随后，`consAtL` 的充分性把 `z` 与语义上的 cons 图识别，`envSuc-in` 再把该图放入 `envSet W (suc k)`。每个截断都只消去到这个隶属命题中。
<!--ja-->
前向きの包含では、cons 像の条項の前半が、先頭 `x`、尾部の環境 `e`、および符号化された cons 関係の充足を与える。`e` を実際の基底環境集合の要素として読むと、命題的切り詰めのもとで尾部の添字が得られる。次に `consAtL` の妥当性が `z` を意味論的な cons グラフと同定し、`envSuc-in` がそのグラフを `envSet W (suc k)` に入れる。どの切り詰めも、この所属命題にだけ除去される。
<!--/-->

```agda
              (subst ⟨_⟩ (consAtL-adequate i2 i1 i0 (e ∷ x ∷ zS ∷ γ) (λ i → ι (g i)) qe) hc) })
          (envSet-out W k e (subst (λ u → ⟨ fst e ∈ u ⟩) qF e∈)) })
        hx })
      (h1 zS hz)
      where
```

<!--en-->
The membership proof for `z` in the candidate successor set supplies a constructible representative `zS : S` with underlying set `z`. This representative is the value passed to the bounded cons-image reader.
<!--zh-->
`z` 属于候选后继集的证明给出一个可构造代表 `zS : S`，其底层集合就是 `z`。这个代表随后被传给有界 cons 像读取器。
<!--ja-->
`z` が候補の後続集合に属するという証明から、基礎の集合が `z` である構成可能な代表 `zS : S` が得られる。この代表を有界な cons 像の読み手に渡す。
<!--/-->

```agda
      zS : S
      zS = down (lookup F' γ) z hz
```

<!--en-->
For the reverse inclusion, take a member `z` of the actual successor environment set. Its successor decomposition merely supplies a head `q`, a tail index `g`, and an equation identifying `z` with their cons environment. The second half of the cons-image clause then merely supplies a corresponding member `e'` of the candidate successor set.
<!--zh-->
为证明反向包含，取真实后继环境集的成员 `z`。其后继分解仅仅给出头部 `q`、尾部索引 `g`，以及把 `z` 认同为二者 cons 环境的等式。cons 像子句的后半部随后仅仅给出候选后继集中的相应成员 `e'`。
<!--ja-->
逆向きの包含を示すため、実際の後続環境集合の要素 `z` を取る。その後続分解は、先頭 `q`、尾部の添字 `g`、および `z` を両者の cons 環境と同定する等式が単に存在することを与える。次に cons の像の条項の後半から、候補の後続集合の対応する要素 `e'` が単に存在することを得る。
<!--/-->

```agda
    bwd : (z : V ℓ) → ⟨ z ∈ fst (envSet W (suc k)) ⟩ → ⟨ z ∈ fst (lookup F' γ) ⟩
    bwd z hz = rec₁ (snd (z ∈ fst (lookup F' γ)))
      (λ { (q , g , qz) → rec₁ (snd (z ∈ fst (lookup F' γ)))
        (λ { (e' , (e'∈ , hc)) →
          subst (λ u → ⟨ u ∈ fst (lookup F' γ) ⟩)
```

<!--en-->
The adequacy of `consAtL` identifies the object-language cons relation supplied by the clause with the same coded cons graph used in the semantic decomposition. Composing this equation with the decomposition equation identifies `e'` with `z`, so membership of `e'` transports to membership of `z`.
<!--zh-->
`consAtL` 的充分性把子句所给出的对象语言 cons 关系认同为语义分解中使用的同一码化 cons 图。将该等式与分解等式复合，便认同 `e'` 与 `z`，从而可把 `e'` 的隶属运输为 `z` 的隶属。
<!--ja-->
`consAtL` の妥当性により、条項が与える対象言語の cons 関係は、意味論的な分解で使われたものと同じ符号化 cons グラフに同定される。この等式を分解の等式と合成すると `e'` と `z` が同定されるので、`e'` の所属を `z` の所属へ移せる。
<!--/-->

```agda
            (subst ⟨_⟩ (consAtL-adequate i0 i1 i2 (e' ∷ xS q ∷ envS W g ∷ γ) (λ i → ι (g i)) refl) hc
             ∙ sym qz)
            e'∈ })
        (h2 (envS W g) (subst (λ u → ⟨ fst (envS W g) ∈ u ⟩) (sym qF) (envSet-in W g))
            (xS q) (subst (λ u → ⟨ ι q ∈ u ⟩) (sym qw) (ι∈' q))) })
```

<!--en-->
The two propositional truncations are eliminated only into the membership proposition being proved. The element `zS` presents `z` inside the constructible carrier, while `xS` will similarly present the recovered head.
<!--zh-->
两个命题截断都只被消去到正在证明的隶属命题中。`zS` 在可构造载体内呈现 `z`，而 `xS` 将以同样方式呈现恢复出的头部。
<!--ja-->
二つの命題截断はいずれも、証明中の所属命題にだけ消去される。`zS` は `z` を構成可能な台の中で提示し、`xS` は復元された先頭を同様に提示する。
<!--/-->

```agda
      (envSuc-out zS hz)
      where
      zS : S
      zS = down (envSet W (suc k)) z hz
      xS : ⟪ fst W ⟫ → S
```

<!--en-->
For a recovered head `q`, its image `ι q` lies in `W`; transitivity of constructibility therefore equips it with the certificate needed to form the carrier element `xS q`.
<!--zh-->
对恢复出的头部 `q`，其像 `ι q` 属于 `W`；因此，可构造性的传递性为它配备构成载体元素 `xS q` 所需的证书。
<!--ja-->
復元された先頭 `q` について、その像 `ι q` は `W` に属する。したがって構成可能性の推移性から、台の要素 `xS q` を作るために必要な証明が得られる。
<!--/-->

```agda
      xS q = ι q , isL-trans {x = fst W} {y = ι q} (ι∈' q) (snd W)
```

<!--en-->
The inward direction of the cons-image clause is proved from the two identifications with the actual stage environment sets. Both directions of the cons-image clause are now available.
<!--zh-->
cons 像子句的向内方向由与真实层环境集的两个认同证明。cons 像子句的两个方向至此可用。
<!--ja-->
cons の像の条項の内向きの方向は、実際の段階の環境の集合との二つの同定から証明される。これで、cons の像の条項の両方向が使える。
<!--/-->

```agda
  consImage-in : (k : ℕ) → fst (lookup F γ) ≡ fst (envSet W k)
               → fst (lookup F' γ) ≡ fst (envSet W (suc k))
               → ⟨ γ ⊨ consImage F' F w ⟩
  consImage-in k qF qF' = h1 , h2
    where
```

<!--en-->
The first direction of the inward reading says that every member of the candidate successor set satisfies the bounded existential: there exists a head element and an environment from the base set whose cons extension is the member.

The truncated decomposition of the member is consumed to name the head and the tail.
<!--zh-->
向内读法的第一方向说，候选后继集的每个成员都满足一个有界存在式：存在头部元素与来自基集的环境，其 cons 扩展即该成员。

成员的截断分解被消耗以名指头部与尾部。
<!--ja-->
内向きの読み出しの最初の方向は、候補の後続の集合のすべての要素が有界の存在量化子を満たすと言う。先頭の要素と、基底の集合からの環境が存在し、その cons の拡張がその要素になる、というものである。要素の切り詰められた分解を消費して、先頭と尾部を名指す。
<!--/-->

```agda
    h1 : (e' : S) → ⟨ fst e' ∈ fst (lookup F' γ) ⟩
       → ⟨ (e' ∷ γ) ⊨ ∃̇∈ (var (sh 1 w)) (∃̇∈ (var (sh 2 F)) (consAtL i2 i1 i0)) ⟩
    h1 e' he' = map₁
      (λ { (q , g , qe') →
        let xS : S
```

<!--en-->
The head is carried into the carrier, the tail is presented as an element of the base set by the base-set membership identification, and the cons adequacy transports the cons equation into the object language.
<!--zh-->
头部被载入载体，尾部经基集隶属认同呈现为基集元素，而 cons 充分性把 cons 等式运入对象语言。
<!--ja-->
先頭は台の中へ載せられ、尾部は基底の集合への所属の同定によって基底の集合の要素として提示され、cons の妥当性が cons の等式を対象言語の中へ運ぶ。
<!--/-->

```agda
            xS = ι q , isL-trans {x = fst W} {y = ι q} (ι∈' q) (snd W)
        in xS , ( subst (λ u → ⟨ ι q ∈ u ⟩) (sym qw) (ι∈' q)
              , ∣ envS W g , ( subst (λ u → ⟨ fst (envS W g) ∈ u ⟩) (sym qF) (envSet-in W g)
                             , subst ⟨_⟩ (sym (consAtL-adequate i2 i1 i0 (envS W g ∷ xS ∷ e' ∷ γ) (λ i → ι (g i)) refl)) qe' ) ∣₁ ) })
      (envSuc-out e' (subst (λ u → ⟨ fst e' ∈ u ⟩) qF' he'))
```

<!--en-->
The second clause starts with a member `e` of the base set and a member `x` of the alphabet set. It must merely exhibit a member of the candidate successor set whose coded graph is obtained by adjoining `x` to the environment represented by `e`.

The outward reading of the base environment set merely supplies the tail index `g`; the semantic cons introduction then places the resulting graph in the actual successor environment set.
<!--zh-->
第二个子句从基集成员 `e` 与字母表集成员 `x` 出发。它只需给出候选后继集中的一个成员，使其码化图由把 `x` 接到 `e` 所表示的环境之前得到。

基环境集的向外读法仅仅给出尾部索引 `g`；语义上的 cons 引入随后把所得图放入真实后继环境集。
<!--ja-->
第二の条項は、基底集合の要素 `e` とアルファベット集合の要素 `x` から始まる。ここで必要なのは、`e` が表す環境の先頭に `x` を付けて得られる符号化グラフをもつ、候補の後続集合の要素が単に存在することである。

基底環境集合の外向きの読み出しから尾部の添字 `g` が単に存在することを得て、意味論的な cons の導入によって、得られたグラフを実際の後続環境集合に入れる。
<!--/-->

```agda
    h2 : (e : S) → ⟨ fst e ∈ fst (lookup F γ) ⟩ → (x : S) → ⟨ fst x ∈ fst (lookup w γ) ⟩
       → ⟨ (x ∷ e ∷ γ) ⊨ ∃̇∈ (var (sh 2 F')) (consAtL i0 i1 i2) ⟩
    h2 e he x hx = map₁
      (λ { (g , qe) →
        let m : ⟨ env (cons (fst x) (λ i → ι (g i))) ∈ fst (envSet W (suc k)) ⟩
```

<!--en-->
The constructed environment is presented as an element of the successor stage environment set by descending along the membership supplied by the cons introduction. The cons adequacy transports the satisfaction of the cons clause into the object language.
<!--zh-->
构造出的环境沿 cons 引理供给的隶属下降而呈现为后继层环境集的元素。cons 充分性把 cons 子句的满足运入对象语言。
<!--ja-->
作られた環境は、cons の導入が供給する所属を下降して、後続の段階の環境の集合の要素として提示される。cons の妥当性が、cons の条項の充足を対象言語の中へ運ぶ。
<!--/-->

```agda
            m = envCons∈ (fst x) (subst (λ u → ⟨ fst x ∈ u ⟩) qw hx) g
            e' : S
            e' = down (envSet W (suc k)) (env (cons (fst x) (λ i → ι (g i)))) m
        in e' , ( subst (λ u → ⟨ fst e' ∈ u ⟩) (sym qF') m
                , subst ⟨_⟩ (sym (consAtL-adequate i0 i1 i2 (e' ∷ x ∷ e ∷ γ) (λ i → ι (g i)) qe)) refl ) })
```

<!--en-->
The base-set outward reading supplies the truncated index `g` whose environment is the entry `e`.
<!--zh-->
基集向外读法供给截断索引 `g`，其环境即条目 `e`。
<!--ja-->
基底の集合の外向きの読み出しが、切り詰められた添字 `g` を供給する。その環境が項目 `e` である。
<!--/-->

```agda
      (envSet-out W k e (subst (λ u → ⟨ fst e ∈ u ⟩) qF he))
```
</div>
</details>

<!--en-->
Numerals are presented as constructible elements: the finite ordinal together with its constructibility certificate.
<!--zh-->
数码被呈现为可构造元素：有限序数连同其可构造性证书。
<!--ja-->
数項は構成可能な要素として提示される。有限の順序数と、その構成可能性の証明である。
<!--/-->

```agda
nn : ℕ → S
nn k = # k , numL k
```

<!--en-->
## Reading the tower specification
<!--zh-->
## 读取环境塔规格
<!--ja-->
## 環境の塔の仕様を読む
<!--/-->

<!--en-->
The single-empty-set module is parameterized by the candidate set slot and the environment.
<!--zh-->
单点空集模块以候选集槽位与环境为参数。
<!--ja-->
一つの空集合のモジュールは、候補の集合の枠と環境をパラメータとする。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module SglEmpty (W : S) {m : ℕ} (F : Fin m) (γ : S ^ m) where
```
</summary>
<div class="submodule-fold-content">

```agda
  open EnvFacts W
```

<!--en-->
The outward reading says that a set satisfying the single-empty-set clause has the same underlying set as the zero-stage environment set. The proof is by extensionality, comparing members in two directions.

The first named object is the underlying set of the candidate, and the `none` helper extracts a refutation from the bounded clause.
<!--zh-->
单点空集子句的向外读法说：满足该子句的集合与零层环境集具有相同底层集合。证明以外延性在两个方向比较成员。

第一个被命名的对象是候选的底层集合，而 `none` 辅助式从有界子句提取反驳。
<!--ja-->
一つの空集合の条項の外向きの読み出しは、その条項を満たす集合が、零の段階の環境の集合と同じ基礎の集合をもつと言う。証明は、二方向で要素を比較する外延性である。

最初に名づけられた対象は、候補の基礎の集合であり、`none` の補助が、有界の条項から反駁を取り出す。
<!--/-->

```agda
  sglEmpty-out : ⟨ γ ⊨ sglEmpty F ⟩ → fst (lookup F γ) ≡ fst (envSet W 0)
  sglEmpty-out (hex , hall) = extensionalV (λ z → ⇔toPath (fwd z) (bwd z))
    where
    Fv = fst (lookup F γ)
    none : (z : S) → ⟨ (z ∷ γ) ⊨ emptyAll i0 ⟩ → (y : V ℓ) → ⟨ y ∈ fst z ⟩ → ⊥₀
```

<!--en-->
The `none` helper feeds a carrier presentation of a member into the bounded clause, which returns the empty type, confirming that the presented set has no members.
<!--zh-->
`none` 辅助式把成员的载体呈现喂给有界子句，后者返回空类型，确认所呈现集合无成员。
<!--ja-->
`none` の補助は、要素の台の提示を有界の条項に渡す。条項は空型を返し、提示された集合に要素がないことを確かめる。
<!--/-->

```agda
    none z k y hy = ⊥*-rec (k (down z y hy) hy)
```

<!--en-->
Forward: a member of the candidate set is presented, the bounded clause refutes every member of it, so it has no members; the zero-stage introduction then admits it as a member of the zero-stage environment set.
<!--zh-->
向前：候选集的成员被呈现，有界子句反驳其每个成员，故它无成员；零层引入随后接纳它为零层环境集的成员。
<!--ja-->
前向き：候補の集合の要素が提示され、有界の条項がそのすべての要素を反駁するので、要素をもたない。零の段階の導入が、それを零の段階の環境の集合の要素として受け入れる。
<!--/-->

```agda
    fwd : (z : V ℓ) → ⟨ z ∈ Fv ⟩ → ⟨ z ∈ fst (envSet W 0) ⟩
    fwd z hz = envSet0-in z (none (down (lookup F γ) z hz) (hall (down (lookup F γ) z hz) hz))
```

<!--en-->
Backward: a member of the zero-stage environment set is presented, and its truncated index is consumed. Both the indexed environment and the member itself are shown to have no members, so they are equal by extensionality of the hierarchy.
<!--zh-->
向后：零层环境集的成员被呈现，其截断索引被消耗。被索引的环境与该成员本身均被证明无成员，故由层级外延性二者相等。
<!--ja-->
後ろ向き：零の段階の環境の集合の要素が提示され、その切り詰められた添字が消費される。添字づけられた環境とその要素の両方が要素をもたないことが示されるので、階層の外延性によって両者は等しくなる。
<!--/-->

```agda
    bwd : (z : V ℓ) → ⟨ z ∈ fst (envSet W 0) ⟩ → ⟨ z ∈ Fv ⟩
    bwd z hz = rec₁ (snd (z ∈ Fv))
      (λ { (e , (e∈ , he)) →
        subst (λ u → ⟨ u ∈ Fv ⟩)
          (noMembers→env0 (fst e) (none e he) ∙ sym (noMembers→env0 z (envSet0-out z hz)))
```

<!--en-->
The transported membership closes the backward direction, and the existence clause completes the proof by confirming the candidate is nonempty.
<!--zh-->
被运输的隶属闭合向后方向，而存在子句确认候选集非空，证明完成。
<!--ja-->
運ばれた所属が後ろ向きの方向を閉じ、存在の条項が、候補が空でないことを確かめて、証明を完成させる。
<!--/-->

```agda
          e∈ })
      hex
```

<!--en-->
For the inward reading, choose the empty environment `e0`. The existential half is satisfied because `e0` belongs to the zero-stage environment set and has no members. The universal half follows because every member of that environment set has no members. Transport along the assumed equality replaces the actual zero-stage set by the candidate set in both halves.
<!--zh-->
为证明向内读式，选择空环境 `e0`。存在项成立，因为 `e0` 属于零层环境集且没有成员。全称项成立，因为该环境集的每个成员都没有成员。沿假设的等式运输，便在两项中都以候选集替代真实零层集。
<!--ja-->
内向きの読み出しでは、空の環境 `e0` を選ぶ。`e0` は零段階の環境集合に属し、要素をもたないので、存在の側が成り立つ。また、その環境集合のどの要素も要素をもたないので、全称の側も成り立つ。仮定された等式に沿って移送することで、両方に現れる実際の零段階集合を候補集合に置き換える。
<!--/-->

```agda
  sglEmpty-in : fst (lookup F γ) ≡ fst (envSet W 0) → ⟨ γ ⊨ sglEmpty F ⟩
  sglEmpty-in q =
      ∣ e0 , ( subst (λ u → ⟨ fst e0 ∈ u ⟩) (sym q) (envSet-in W (λ ()))
             , (λ y hy → lift (envAny0-noMembers (λ ()) (fst y) hy)) ) ∣₁
    , (λ z hz y hy → lift (envSet0-out (fst z) (subst (λ u → ⟨ fst z ∈ u ⟩) q hz) (fst y) hy))
```

<!--en-->
The empty environment is the coded graph of the function from the empty type, which has no entries.
<!--zh-->
空环境是从空类型出发的函数的编码图，它没有条目。
<!--ja-->
空の環境は、空型からの関数の符号化されたグラフであり、項目をもたない。
<!--/-->

```agda
    where
    e0 : S
    e0 = envS W (λ ())
```
</div>
</details>

<!--en-->
The tower reader fixes a candidate tower slot `E`, a parameter-set slot `w`, a zero-numeral slot `N0`, and an interpreting environment. Its hypotheses identify `w` with the working set `W`, identify `N0` with `# 0`, and assert satisfaction of `towerAt E w N0`. The two readings below are relative to exactly these identifications.
<!--zh-->
环境塔读取器固定候选塔槽 `E`、参数集槽 `w`、零数码槽 `N0` 与解释环境。其假设把 `w` 与工作集 `W` 识别，把 `N0` 与 `# 0` 识别，并断言 `towerAt E w N0` 得到满足。下文两种读法恰好相对于这些同一视成立。
<!--ja-->
環境の塔の読み手は、候補の塔のスロット `E`、パラメータ集合のスロット `w`、ゼロの数項のスロット `N0`、および解釈環境を固定する。その仮定は、`w` を作業集合 `W` と同定し、`N0` を `# 0` と同定し、`towerAt E w N0` の充足を与える。以下の二つの読みは、ちょうどこれらの同一視に相対的である。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module TowerRead {m : ℕ} (E w N0 : Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) (qN0 : fst (lookup N0 γ) ≡ # 0)
  (h : ⟨ γ ⊨ towerAt E w N0 ⟩) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
    Ev = fst (lookup E γ)
```

<!--en-->
The three conjuncts of the tower formula are named: the base clause, the upward-closure clause, and the downward-decomposition clause.
<!--zh-->
塔公式的三个合取项被命名：基项子句、向上闭合子句与向下分解子句。
<!--ja-->
塔の論理式の三つの連言項に名前がつけられる。基底の条項、上向きの閉じの条項、そして下向きの分解の条項である。
<!--/-->

```agda
    hbase = h .fst
    hup = h .snd .fst
    hdown = h .snd .snd
```

<!--en-->
An entry is a truncated record of a natural number arity and an environment set whose underlying set is presented by that arity. It is the reading goal for the tower's outward direction.
<!--zh-->
条目是「自然数元数连同以该元数呈现的环境集」的截断记录。它是塔的向外方向的读取目标。
<!--ja-->
項目とは、自然数のアリティと、そのアリティで提示される環境の集合の、切り詰められた記録である。塔の外向きの方向の読みの目標である。
<!--/-->

```agda
  Entry : V ℓ → V ℓ → Type (ℓ-suc ℓ)
  Entry n F = ∥ Σ[ k ∈ ℕ ] ((n ≡ # k) × (F ≡ fst (envSet W k))) ∥₁
```

<!--en-->
The outward reading of tower entries is proved by membership induction on the first component of the encoded pair. The motive says: for every hierarchy element `nv`, whenever the first component of an entry equals `nv` and the entry belongs to the candidate tower, the entry decomposes as a natural-number arity with its environment set. This is a well-founded induction on the membership relation of the hierarchy, not an ordinary induction on natural numbers.

The step function splits on the downward-decomposition clause of the tower formula.
<!--zh-->
塔条目的向外读法由编码对第一分量的集合隶属归纳证明。动机说：对层级中每个元素 `nv`，若某条目的第一分量等于 `nv` 且该条目属于候选塔，则该条目分解为自然数元数连同其环境集。这是对层级隶属关系的良基归纳，而非对自然数的普通归纳。

步进函数按塔公式的向下分解子句分裂。
<!--ja-->
塔の項目の外向きの読み出しは、符号化された対の第一成分の集合についての所属の帰納で証明される。動機はこう言う。階層のすべての要素 `nv` について、ある項目の第一成分が `nv` に等しく、その項目が候補の塔に属するなら、その項目は自然数のアリティとその環境の集合に分解される、と。これは、階層の所属関係についての整礎帰納であり、自然数についての通常の帰納ではない。

ステップの関数は、塔の論理式の下向きの分解の条項で場合分けする。
<!--/-->

```agda
  entry-out : (n F : S) → ⟨ pr (fst n) (fst F) ∈ Ev ⟩ → Entry (fst n) (fst F)
  entry-out n F = ∈-induction {P = P} step (fst n) n F refl
    where
    P : V ℓ → Type (ℓ-suc ℓ)
    P nv = (n F : S) → fst n ≡ nv → ⟨ pr (fst n) (fst F) ∈ Ev ⟩ → Entry (fst n) (fst F)
```

<!--en-->
The step of the membership induction splits on the downward-decomposition clause of the tower formula, which says that the pair either is the base entry or has a predecessor entry.
<!--zh-->
隶属归纳的步进按塔公式的向下分解子句分裂：该对或是基项，或有一前驱条目。
<!--ja-->
所属の帰納のステップは、塔の論理式の下向きの分解の条項で場合分けする。その対が基底の項目であるか、前の項目をもつかである。
<!--/-->

```agda
    step : (nv : V ℓ) → ((y : V ℓ) → ⟨ y ∈ nv ⟩ → P y) → P nv
    step nv IH n F qn p∈ = rec₁ squash₁ cases
      (useBoth i0 (pS ∷ γ) n F refl (towerDown E w N0) (hdown pS p∈))
      where
      pS : S
```

<!--en-->
The membership proof for the candidate pair supplies a constructible representative `pS : S`. Its container exposes the numeral and environment-set components through bounded quantification, and the four-slot environment places those components beside the pair and the surrounding chapter environment.
<!--zh-->
候选有序对的隶属证明给出一个可构造代表 `pS : S`。其容器通过有界量化暴露数码分量与环境集分量，四槽环境则把这些分量连同该有序对放在本章外围环境之前。
<!--ja-->
候補の順序対の所属証明から、構成可能な代表 `pS : S` が得られる。その容器は、有界量化を通して数項成分と環境集合成分を公開し、四つのスロットからなる環境は、それらの成分と順序対を本章の外側の環境の前に置く。
<!--/-->

```agda
      pS = down (lookup E γ) (pr (fst n) (fst F)) p∈
      c = container pS n F refl
      δ : S ^ (4 + m)
      δ = F ∷ n ∷ c .fst ∷ pS ∷ γ
```

<!--en-->
The case split consumes the downward-decomposition satisfaction. The base case reads the zero-numeral equation together with the single-empty-set outward reading, producing the arity zero and the zero-stage environment set. The successor case passes to the recursive step.
<!--zh-->
情形分裂消耗向下分解的满足。基例读取零数码等式连同单点空集向外读法，产出元数零与零层环境集。后继情形传入递归步。
<!--ja-->
場合分けは、下向きの分解の充足を消費する。基底の場合は、零の数項の等式と、一つの空集合の条項の外向きの読み出しを読み、アリティ零と零の段階の環境の集合を作る。後続の場合は、再帰のステップに渡される。
<!--/-->

```agda
      cases : ((fst n ≡ fst (lookup N0 γ)) × ⟨ δ ⊨ sglEmpty i0 ⟩)
            ⊎ ⟨ δ ⊨ ∃̇∈ (var (sh 4 E)) (bothEx i0 (downBody w)) ⟩
            → Entry (fst n) (fst F)
      cases (inl (qn0 , hF)) = ∣ 0 , (qn0 ∙ qN0 , SglEmpty.sglEmpty-out W i0 δ hF) ∣₁
      cases (inr hs) = rec₁ squash₁
```

<!--en-->
The successor case unpacks the bounded existentials: a predecessor entry `p'` and a successor equation, followed by a predecessor numeral `n'`, a predecessor environment set `F'`, a cons container, and the cons equation. The four-slot extension prepares the induction.

The ordinality comparison says the candidate numeral is the von Neumann successor of the predecessor numeral.
<!--zh-->
后继情形拆开有界存在：前驱条目 `p'` 与后继等式，随后是前驱数码 `n'`、前驱环境集 `F'`、cons 容器与 cons 等式。四槽扩展为归纳做准备。

序数比较说：候选数码是前驱数码的冯·诺伊曼后继。
<!--ja-->
後続の場合は、有界の存在量化をほどく。前の項目 `p'` と後続の等式、そして前の数項 `n'`、前の環境の集合 `F'`、cons のコンテナと cons の等式である。四つの枠の拡張が帰納を準備する。

順序数の比較は、候補の数項が、前の数項のフォン・ノイマンの後続であると言う。
<!--/-->

```agda
        (λ { (p' , (p'∈ , hb)) → rec₁ squash₁
          (λ { (n' , F' , s' , (qp' , (hsuc , hci))) →
            let δ' = F' ∷ n' ∷ s' ∷ p' ∷ δ
                qsuc : fst n ≡ sucV (fst n')
                qsuc = suc-out i1 i5 δ' hsuc
```

<!--en-->
The predecessor numeral lies in the candidate numeral because every set lies in its von Neumann successor; transport along the successor equation makes this the strict descent required by membership induction. Applying the induction hypothesis recovers an arity `k` and the stage `envSet W k`.
<!--zh-->
前驱数码属于候选数码，因为每个集合都属于其冯·诺伊曼后继；沿后继等式运输后，这正是隶属归纳所需的严格下降。应用归纳假设即可恢复元数 `k` 与层 `envSet W k`。
<!--ja-->
前の数項は、そのフォン・ノイマン後続に属し、後続の等式に沿って移送すると、所属に関する帰納法に必要な真の下降が得られる。帰納仮定を適用すれば、アリティ `k` と段階 `envSet W k` が復元される。
<!--/-->

```agda
                n'∈ : ⟨ fst n' ∈ nv ⟩
                n'∈ = subst (λ u → ⟨ fst n' ∈ u ⟩) (sym qsuc ∙ qn) (self∈sucV (fst n'))
            in map₁
              (λ { (k , (qk , qF')) →
                suc k , ( qsuc ∙ cong sucV qk
```

<!--en-->
The recovered arity is mapped to its successor, and the cons-image outward reading transports the base environment set to the successor environment set. The induction hypothesis is applied at the predecessor, whose membership is transported along the tower equation.
<!--zh-->
恢复的元数被映到其后继，cons 像向外读法把基层环境集运到后继层环境集。归纳假设施于前驱，其隶属沿塔等式运输。
<!--ja-->
復元されたアリティはその後続へ写され、cons の像の外向きの読み出しが、基底の環境の集合を後続のものへ運ぶ。帰納の仮定は、塔の等式に沿って所属が運ばれる前の要素で適用される。
<!--/-->

```agda
                        , ConsImageRead.consImage-out i4 i0 (sh 8 w) δ' W qw k qF' hci ) })
              (IH (fst n') n'∈ n' F' refl
                (subst (λ u → ⟨ u ∈ Ev ⟩) qp' p'∈)) })
          (bothEx-out i0 (downBody w) (p' ∷ δ) hb) })
        hs
```

<!--en-->
The inward reading is proved by ordinary induction on the external natural number `k`. At zero, the base clause merely supplies a tower member together with its second component. Reading `sglEmpty` identifies that component with `envSet W 0`, while the alignment `N0 = # 0` identifies the first component; transport along the resulting pair equation yields the standard zero entry.
<!--zh-->
向内读式对外围自然数 `k` 作普通归纳。在零步，基项子句仅仅给出一个塔成员及其第二分量。读取 `sglEmpty` 将该分量认同为 `envSet W 0`，而对齐式 `N0 = # 0` 认同其第一分量；沿所得有序对等式运输，即得标准零条目。
<!--ja-->
内向きの読み出しは、外部の自然数 `k` に関する通常の帰納法で証明する。零の場合、基底の条項から塔の要素とその第二成分が単に存在することを得る。`sglEmpty` を読むと第二成分が `envSet W 0` に同定され、整合条件 `N0 = # 0` によって第一成分も同定される。得られた順序対の等式に沿って移送すれば、標準的な零番目の項目が得られる。
<!--/-->

```agda
  entry-in : (k : ℕ) → ⟨ pr (# k) (fst (envSet W k)) ∈ Ev ⟩
  entry-in zero = rec₁ (snd (pr (# 0) (fst (envSet W 0)) ∈ Ev))
    (λ { (p , (p∈ , hs)) → rec₁ (snd (pr (# 0) (fst (envSet W 0)) ∈ Ev))
      (λ { (F , s , (qp , hF)) →
        subst (λ u → ⟨ u ∈ Ev ⟩)
```

<!--en-->
After the zero case closes, the successor step applies the upward-closure clause to the already constructed standard entry at `k`. That clause merely supplies a new tower member together with a numeral satisfying the successor formula and an environment set satisfying the cons-image formula.
<!--zh-->
零步闭合后，后继步骤把向上闭合子句应用于已经构造出的第 `k` 个标准条目。该子句仅仅给出一个新的塔成员，以及满足后继公式的数码和满足 cons 像公式的环境集。
<!--ja-->
零の場合を終えると、後続の場合では、すでに構成した第 `k` 標準項目に上向き閉包の条項を適用する。この条項から、新しい塔の要素と、後続の論理式を満たす数項、および cons の像の論理式を満たす環境集合が単に存在することを得る。
<!--/-->

```agda
          (qp ∙ cong₂ pr qN0 (SglEmpty.sglEmpty-out W i0 (F ∷ s ∷ p ∷ γ) hF))
          p∈ })
      (sndEx-out i0 (sh 1 N0) (sglEmpty i0) (p ∷ γ) hs) })
    hbase
  entry-in (suc k) = rec₁ (snd (pr (# (suc k)) (fst (envSet W (suc k))) ∈ Ev))
```

<!--en-->
The successor formula determines the new first component from the old numeral, and the outward reading of the cons-image formula determines the new second component from `envSet W k`. Applying the coded-pair equation to these two identifications yields the standard successor entry `(# (suc k), envSet W (suc k))`.
<!--zh-->
后继公式由旧数码确定新的第一分量，cons 像公式的向外读法则由 `envSet W k` 确定新的第二分量。把码化有序对等式应用于这两条同一视，便得到标准后继条目 `(# (suc k), envSet W (suc k))`。
<!--ja-->
後続の論理式は、もとの数項から新しい第一成分を定め、cons 像の論理式の外向きの読みは、`envSet W k` から新しい第二成分を定める。符号化順序対の等式にこれら二つの同一視を適用すると、標準的な後続項目 `(# (suc k), envSet W (suc k))` が得られる。
<!--/-->

```agda
    (λ { (p' , (p'∈ , hb)) → rec₁ (snd (pr (# (suc k)) (fst (envSet W (suc k))) ∈ Ev))
      (λ { (n' , F' , s' , (qp' , (hsuc , hci))) →
        let δ' = F' ∷ n' ∷ s' ∷ p' ∷ δ
        in subst (λ u → ⟨ u ∈ Ev ⟩)
             (qp' ∙ cong₂ pr (suc-out i5 i1 δ' hsuc)
```

<!--en-->
The induction hypothesis first supplies membership of the standard entry at `k`. Applying upward closure to that entry merely produces a successor entry together with its two component formulas. Their outward readings identify the components with `# (suc k)` and `envSet W (suc k)`, so transport along the resulting coded-pair equality proves membership of the standard successor entry.
<!--zh-->
归纳假设先给出第 `k` 个标准条目的隶属证明。把向上闭合应用于该条目，仅仅得到一个后继条目及其两个分量公式。向外读取这两个公式，会把相应分量识别为 `# (suc k)` 与 `envSet W (suc k)`；沿所得码化有序对等式运输，便证明标准后继条目属于塔。
<!--ja-->
帰納仮定はまず、第 `k` 標準項目の所属を与える。その項目に上向き閉包を適用すると、後続項目とその二つの成分を記述する論理式が、命題的切り詰めのもとで得られる。それらを外向きに読むと、各成分が `# (suc k)` と `envSet W (suc k)` に同定されるので、得られた符号化順序対の等式に沿って移送すれば、標準的な後続項目の所属が証明される。
<!--/-->

```agda
                             (ConsImageRead.consImage-out i0 i4 (sh 8 w) δ' W qw k refl hci))
             p'∈ })
      (bothEx-out i0 (upBody w) (p' ∷ δ) hb) })
    (useBoth i0 (pS ∷ γ) (nn k) (envSet W k) refl (towerUp E w) (hup pS (entry-in k)))
    where
```

<!--en-->
To invoke upward closure, the standard entry at `k` is first presented as the carrier element `pS`. Its container exposes the two components to bounded quantification, and the four-slot environment records the current environment set, numeral, container, and tower entry.
<!--zh-->
为调用向上闭合，先把第 `k` 个标准条目呈现为载体元素 `pS`。其容器向有界量词暴露两个分量，四槽环境则依次记录当前环境集、数码、容器与塔条目。
<!--ja-->
上向き閉包を使うため、まず第 `k` 標準項目を台の要素 `pS` として提示する。そのコンテナが二つの成分を有界量化に公開し、四つの枠からなる環境が、現在の環境集合、数項、コンテナ、塔の項目を順に記録する。
<!--/-->

```agda
    pS : S
    pS = down (lookup E γ) (pr (# k) (fst (envSet W k))) (entry-in k)
    c = container pS (nn k) (envSet W k) refl
    δ : S ^ (4 + m)
    δ = envSet W k ∷ nn k ∷ c .fst ∷ pS ∷ γ
```
</div>
</details>

<!--en-->
The tower-holding module assumes that the candidate tower has been identified with the real tower by an equation of underlying sets, in addition to the carrier and numeral equations. All conclusions are relative to these identifications.
<!--zh-->
塔持有模块假定候选塔已通过底层集合等式与真实塔等同，此外还有载体与数码等式。所有结论都相对于这些等同。
<!--ja-->
塔を保持するモジュールは、候補の塔が、基礎の集合の等式によって実際の塔と同一視されていると仮定する。台と数項の等式に加えてである。すべての結論は、これらの同定に相対的である。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module TowerHolds {m : ℕ} (E w N0 : Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) (qE : fst (lookup E γ) ≡ fst (Tower.tower W))
  (qN0 : fst (lookup N0 γ) ≡ # 0) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
    Ev = fst (lookup E γ)
```

<!--en-->
Every standard entry belongs to the candidate tower, by transporting the real tower's inward reading along the identification equation.
<!--zh-->
每条标准条目属于候选塔，方法是把真实塔的向内读式沿等同等式运输。
<!--ja-->
すべての正準な項目は、候補の塔に属する。実際の塔の内向きの読み出しを、同定の等式に沿って運ぶことによるものである。
<!--/-->

```agda
    entry∈ : (k : ℕ) → ⟨ pr (# k) (fst (envSet W k)) ∈ Ev ⟩
    entry∈ k = subst (λ u → ⟨ pr (# k) (fst (envSet W k)) ∈ u ⟩) (sym qE) (Tower.tower-in′ W k)
```

<!--en-->
Each standard entry is presented as a carrier element by descending along its membership in the candidate tower.
<!--zh-->
每条标准条目沿其在候选塔中的隶属下降而呈现为载体元素。
<!--ja-->
それぞれの正準な項目は、候補の塔の中での所属を下降して、台の要素として提示される。
<!--/-->

```agda
    entryS : (k : ℕ) → S
    entryS k = down (lookup E γ) (pr (# k) (fst (envSet W k))) (entry∈ k)
```

<!--en-->
Every member of the candidate tower is read as a standard entry, by transporting the membership into the real tower and applying the tower's outward reading.
<!--zh-->
候选塔的每个成员都被读作标准条目，方法是把隶属运入真实塔并应用塔的向外读法。
<!--ja-->
候補の塔のすべての要素は、正準な項目として読まれる。所属を実際の塔の中へ運び、塔の外向きの読み出しを適用することによるものである。
<!--/-->

```agda
    read : (p : S) → ⟨ fst p ∈ Ev ⟩ → ∥ Σ[ k ∈ ℕ ] (fst p ≡ pr (# k) (fst (envSet W k))) ∥₁
    read p p∈ = Tower.tower-out W p (subst (λ u → ⟨ fst p ∈ u ⟩) qE p∈)
```

<!--en-->
The tower-holding conclusion is the triple of clauses: the base clause, the upward-closure clause, and the downward-decomposition clause. The base clause is proved by presenting the zero-th standard entry and its membership.
<!--zh-->
塔持有结论是三个子句的三元组：基项子句、向上闭合子句与向下分解子句。基项子句的证明：呈现第零条标准条目及其隶属。
<!--ja-->
塔を保持する結論は、三つの条項の組である。基底の条項、上向きの閉じの条項、そして下向きの分解の条項である。基底の条項は、零番目の正準な項目とその所属を提示することで証明される。
<!--/-->

```agda
  holds : ⟨ γ ⊨ towerAt E w N0 ⟩
  holds = hbase , (hup , hdown)
    where
    hbase : ⟨ γ ⊨ ∃̇∈ (var E) (sndEx i0 (sh 1 N0) (sglEmpty i0)) ⟩
    hbase = ∣ entryS 0 , ( entry∈ 0
```

<!--en-->
The zero-th entry is filled with its numeral equation, its membership, and the single-empty-set inward reading applied to the presented environment. The numeral equation is transported from the candidate zero-numeral slot.
<!--zh-->
第零条目以其数码等式、其隶属以及施于所呈现环境的单点空集向内读式填充。数码等式从候选零数码槽运输而来。
<!--ja-->
零番目の項目は、その数項の等式と所属と、提示された環境に適用した一つの空集合の条項の内向きの読み出しで満たされる。数項の等式は、候補の零の数項の枠から運ばれる。
<!--/-->

```agda
      , fillSnd i0 (entryS 0 ∷ γ) (lookup N0 γ) (envSet W 0)
          (cong (λ a → pr a (fst (envSet W 0))) (sym qN0))
          (sglEmpty i0)
          (SglEmpty.sglEmpty-in W i0
            (envSet W 0 ∷ container (lookup i0 (entryS 0 ∷ γ)) (lookup N0 γ) (envSet W 0)
```

<!--en-->
The base clause is now complete. Its witness is the canonical entry `entryS 0`, whose membership in `E` comes from the alignment with the constructed tower. The equation `qN0` aligns the first component with the designated zero slot, while `SglEmpty.sglEmpty-in` identifies the second component with the singleton containing the empty environment. Hence the required base entry exists, still under propositional truncation.
<!--zh-->
基条目子句至此完成。其见证是典范条目 `entryS 0`，该条目属于 `E` 是由 `E` 与已构造环境塔的对齐得到的。等式 `qN0` 把第一分量与指定的零数码槽位对齐，而 `SglEmpty.sglEmpty-in` 把第二分量识别为只含空环境的单点集。因此，所需的基条目在命题截断下存在。
<!--ja-->
基底の節はこれで完成する。その証人は正準な項目 `entryS 0` であり、これが `E` に属することは、`E` と構成済みの塔との同一視から得られる。等式 `qN0` は第一成分を指定されたゼロの数項のスロットに揃え、`SglEmpty.sglEmpty-in` は第二成分を空環境だけからなる一元集合と同定する。したがって、必要な基底の項目が命題的切り詰めのもとで存在する。
<!--/-->

```agda
               (cong (λ a → pr a (fst (envSet W 0))) (sym qN0)) .fst ∷ entryS 0 ∷ γ) refl)
          (sh 1 N0) refl ) ∣₁
```

<!--en-->
For upward closure, fix an entry `p` of `E` and any coded-pair presentation `p = (n,F)` supplied to `bothAll-in`. The reader `read p p∈` says, under propositional truncation, that `p` is the canonical entry `(# k, envSet W k)` for some `k`. Injectivity of the ordered-pair code then identifies `n` with `# k` and `F` with `envSet W k`. Thus the argument uses precisely the coded ordered-pair interface controlled by `towerAt`.
<!--zh-->
为证明向上闭合，固定 `E` 的一个条目 `p`，并考虑传给 `bothAll-in` 的任意码化有序对表示 `p = (n,F)`。读式 `read p p∈` 在命题截断下断言：对某个 `k`，`p` 是典范条目 `(# k, envSet W k)`。码化有序对的单射性随即把 `n` 与 `# k`、`F` 与 `envSet W k` 分别识别。因而，该论证恰好使用 `towerAt` 所控制的码化有序对接口。
<!--ja-->
上向き閉包を示すため、`E` の項目 `p` と、`bothAll-in` に渡される任意の符号化順序対表示 `p = (n,F)` を固定する。読み補題 `read p p∈` は、ある `k` について `p` が正準な項目 `(# k, envSet W k)` であることを、命題的切り詰めのもとで述べる。そこで符号化順序対の単射性を使うと、`n` は `# k` と、`F` は `envSet W k` とそれぞれ同定される。したがって、この議論が使うのは、`towerAt` が制御する符号化順序対のインターフェースに限られる。
<!--/-->

```agda
    hup : (p : S) → ⟨ fst p ∈ Ev ⟩ → ⟨ (p ∷ γ) ⊨ bothAll i0 (towerUp E w) ⟩
    hup p p∈ = bothAll-in i0 (towerUp E w) (p ∷ γ) (λ n F s s∈ n∈ F∈ e →
      rec₁ (snd ((F ∷ n ∷ s ∷ p ∷ γ) ⊨ towerUp E w))
        (λ { (k , qp) →
          let q = pr-inj (sym e ∙ qp)
```

<!--en-->
The next canonical entry is obtained from the membership proof for `entryS (suc k)` in `E`. The environment `δ1` records this entry together with the components `F` and `n` of the current entry; `container` then supplies the bounded container needed to expose the numeral and environment-set components of the new ordered pair. Extending once more to `δ2` places the canonical successor numeral and `envSet W (suc k)` in the slots required by `upBody`.
<!--zh-->
下一个典范条目由 `entryS (suc k)` 属于 `E` 的证明取得。环境 `δ1` 同时记录该条目以及当前条目的分量 `F` 与 `n`；随后，`container` 提供有界容器，使新有序对的数码分量与环境集分量可由公式访问。再延拓一次得到 `δ2`，便把典范后继数码与 `envSet W (suc k)` 放入 `upBody` 所需的槽位。
<!--ja-->
次の正準な項目は、`entryS (suc k)` が `E` に属するという証明から得られる。環境 `δ1` は、この項目と現在の項目の成分 `F`、`n` をまとめて記録する。続いて `container` が、新しい順序対の数項成分と環境集合成分を論理式から参照するための有界な容器を与える。さらに `δ2` へ拡張すると、正準な後続数項と `envSet W (suc k)` が `upBody` の要求するスロットに置かれる。
<!--/-->

```agda
              δ1 = entryS (suc k) ∷ F ∷ n ∷ s ∷ p ∷ γ
              c' = container (lookup i0 δ1) (nn (suc k)) (envSet W (suc k)) refl
              δ2 = envSet W (suc k) ∷ nn (suc k) ∷ c' .fst ∷ δ1
          in ∣ entryS (suc k) , ( entry∈ (suc k)
             , fillBoth i0 δ1 (nn (suc k)) (envSet W (suc k)) refl (upBody w)
```

<!--en-->
The two conjuncts of `upBody` now express the two successor steps. The introduction lemma for `sucAtL` uses the first-component equality, transported through `sucV`, to relate `# (suc k)` to the new numeral slot. Independently, `ConsImageRead.consImage-in` uses the second-component equality, the alignment `w = W`, and the adequacy of `consAtL` to show that `envSet W (suc k)` is exactly the cons image of `envSet W k`. These proofs produce a truncated successor-entry witness; eliminating the truncated result of `read` into that satisfaction proposition establishes upward closure for every entry.
<!--zh-->
此时，`upBody` 的两个合取支分别表达两种后继步骤。`sucAtL` 的引入引理把第一分量的等式经 `sucV` 搬运，从而将 `# (suc k)` 与新的数码槽位联系起来。另一方面，`ConsImageRead.consImage-in` 使用第二分量的等式、对齐 `w = W` 以及 `consAtL` 的充分性，证明 `envSet W (suc k)` 恰是 `envSet W k` 的 cons 像。这些证明产出一个截断的后继条目见证；再把 `read` 的截断结果消去到这个满足命题中，便对每个条目建立了向上闭合。
<!--ja-->
ここで `upBody` の二つの連言は、それぞれ二つの後続段階を表す。`sucAtL` の導入補題は第一成分の等式を `sucV` によって運び、`# (suc k)` と新しい数項のスロットを結ぶ。一方、`ConsImageRead.consImage-in` は第二成分の等式、同一視 `w = W`、および `consAtL` の妥当性を用いて、`envSet W (suc k)` が `envSet W k` の cons 像にほかならないことを示す。これらの証明から後続項目の切り詰められた証人が得られ、`read` の切り詰められた結果をこの充足命題へ除去することで、すべての項目について上向き閉包が成立する。
<!--/-->

```agda
                 ( suc-in i5 i1 δ2 (cong sucV (sym (q .fst)))
                 , ConsImageRead.consImage-in i0 i4 (sh 8 w) δ2 W qw k (q .snd) refl ) ) ∣₁ })
        (read p p∈))
```

<!--en-->
Downward decomposition begins in the same way: fix an entry `p`, choose any coded-pair presentation `p = (n,F)`, and use `read` only through propositional truncation. A resulting witness supplies some natural number `k` for which `p = (# k, envSet W k)`. Pattern matching on this witness separates `k = 0` from `k = suc j`, exactly the two disjuncts of `towerDown`.
<!--zh-->
向下分解以同样的方式开始：固定条目 `p`，取其任意码化有序对表示 `p = (n,F)`，并且只在命题截断允许的范围内使用 `read`。所得见证给出某个自然数 `k`，使 `p = (# k, envSet W k)`。对该见证中的 `k` 作模式匹配，便分成 `k = 0` 与 `k = suc j` 两种情形，它们恰好对应 `towerDown` 的两个析取支。
<!--ja-->
下向き分解も同じように始まる。項目 `p` とその任意の符号化順序対表示 `p = (n,F)` を固定し、`read` は命題的切り詰めが許す範囲でだけ使う。得られる証人は、`p = (# k, envSet W k)` を満たすある自然数 `k` を与える。この証人の `k` をパターン照合すると、`k = 0` と `k = suc j` に分かれる。これらがちょうど `towerDown` の二つの選言である。
<!--/-->

```agda
    hdown : (p : S) → ⟨ fst p ∈ Ev ⟩ → ⟨ (p ∷ γ) ⊨ bothAll i0 (towerDown E w N0) ⟩
    hdown p p∈ = bothAll-in i0 (towerDown E w N0) (p ∷ γ) (λ n F s s∈ n∈ F∈ e →
      rec₁ (snd ((F ∷ n ∷ s ∷ p ∷ γ) ⊨ towerDown E w N0))
        (λ { (zero , qp) →
          let q = pr-inj (sym e ∙ qp)
```

<!--en-->
If `k` is zero, injectivity of the ordered-pair code identifies `n` with `# 0` and `F` with `envSet W 0`. The first equality, combined with `qN0`, proves that the recorded numeral is the designated zero, while `SglEmpty.sglEmpty-in` turns the second equality into the singleton-of-empty condition. This establishes the left disjunct. If `k = suc j`, the same injectivity instead recovers the predecessor index and its environment set; the next environments prepare a witness for the right disjunct.
<!--zh-->
若 `k` 为零，码化有序对的单射性便把 `n` 与 `# 0`、`F` 与 `envSet W 0` 分别识别。第一条等式与 `qN0` 合成，证明所记录的数码就是指定的零数码；`SglEmpty.sglEmpty-in` 则把第二条等式转成只含空环境的单点集条件。这就建立了左析取支。若 `k = suc j`，同一单射性转而恢复前驱索引及其环境集；接下来的环境为右析取支准备见证。
<!--ja-->
`k` がゼロなら、符号化順序対の単射性によって `n` は `# 0` と、`F` は `envSet W 0` とそれぞれ同定される。第一の等式を `qN0` と合成すると、記録された数項が指定されたゼロの数項であることが分かり、`SglEmpty.sglEmpty-in` は第二の等式を空環境だけからなる一元集合という条件に変える。これで左の選言が得られる。`k = suc j` なら、同じ単射性から先行する添字とその環境集合が得られ、続く環境が右の選言の証人を用意する。
<!--/-->

```agda
          in ∣ inl (q .fst ∙ sym qN0 , SglEmpty.sglEmpty-in W i0 (F ∷ n ∷ s ∷ p ∷ γ) (q .snd)) ∣₁
           ; (suc j , qp) →
          let q = pr-inj (sym e ∙ qp)
              δ1 = entryS j ∷ F ∷ n ∷ s ∷ p ∷ γ
              c' = container (lookup i0 δ1) (nn j) (envSet W j) refl
```

<!--en-->
For the successor case, `entryS j` supplies the canonical predecessor entry in `E`. The introduction lemma for `sucAtL` uses the first-component equality to show that the current numeral is the successor of the predecessor numeral. Then `ConsImageRead.consImage-in`, using `w = W` and the second-component equality, proves that the current environment set is the cons image of the predecessor environment set. Packaging the predecessor and these two facts gives the truncated witness required by the right disjunct.
<!--zh-->
在后继情形中，`entryS j` 给出 `E` 内的典范前驱条目。`sucAtL` 的引入引理使用第一分量的等式，证明当前数码是前驱数码的后继。随后，`ConsImageRead.consImage-in` 使用 `w = W` 与第二分量的等式，证明当前环境集是前驱环境集的 cons 像。把该前驱条目与这两个事实打包，便得到右析取支所需的截断见证。
<!--ja-->
後続の場合、`entryS j` が `E` に属する正準な先行項目を与える。`sucAtL` の導入補題は第一成分の等式を用いて、現在の数項が先行する数項の後続であることを示す。次に `ConsImageRead.consImage-in` が、`w = W` と第二成分の等式を用いて、現在の環境集合が先行する環境集合の cons 像であることを示す。この先行項目と二つの事実をまとめると、右の選言が要求する切り詰められた証人が得られる。
<!--/-->

```agda
              δ2 = envSet W j ∷ nn j ∷ c' .fst ∷ δ1
          in ∣ inr ∣ entryS j , ( entry∈ j
             , fillBoth i0 δ1 (nn j) (envSet W j) refl (downBody w)
                 ( suc-in i1 i5 δ2 (q .fst)
                 , ConsImageRead.consImage-in i4 i0 (sh 8 w) δ2 W qw j refl (q .snd) ) ) ∣₁ ∣₁ })
```

<!--en-->
Eliminating the truncated result of `read` into the satisfaction proposition completes downward decomposition for every member of the real tower. Together with the base and upward clauses, this proves `towerAt E w N0` whenever `E`, `w`, and `N0` are aligned with `Tower.tower W`, `W`, and `# 0`. The conclusion establishes the bounded description for the real tower while retaining the coded ordered-pair boundary of the formula.
<!--zh-->
把 `read` 的截断结果消去到满足命题中，便对真实环境塔的每个成员完成向下分解。结合基项与向上闭合子句可知：只要 `E`、`w`、`N0` 分别与 `Tower.tower W`、`W`、`# 0` 对齐，`towerAt E w N0` 就得到满足。该结论证明真实环境塔满足其有界描述，同时保留公式只控制码化有序对接口这一边界。
<!--ja-->
`read` の切り詰められた結果を充足命題へ除去すると、実際の塔のすべての要素について下向き分解が完成する。基底と上向き閉包の条項を合わせれば、`E`、`w`、`N0` がそれぞれ `Tower.tower W`、`W`、`# 0` と同定されるとき、`towerAt E w N0` が充足される。この結論は、論理式が符号化順序対のインターフェースだけを制御するという境界を保ったまま、実際の塔が有界記述を満たすことを示す。
<!--/-->

```agda
        (read p p∈))
```
</div>
</details>

<!--en-->
## Recap

The environment tower now has both forms needed later: an actual constructible set whose members are exactly the standard pairs `(# n, envSet W n)`, and a Δ₀ formula that reads and produces its coded ordered-pair entries one adjacent arity at a time. The two directions use different inductions: membership induction rules out endless descent when reading an entry, while ordinary induction on natural numbers constructs every standard entry. All recovered arities and decompositions remain under propositional truncation, and the formula makes no claim about possible non-pair members of an arbitrary candidate set.
<!--zh-->
## 回顾

环境塔现在具备后文所需的两种形式：一方面，它是一个实际的可构造集合，其成员恰为标准有序对 `(# n, envSet W n)`；另一方面，它有一条 Δ₀ 公式，可逐个相邻元数读取和生成这些码化有序对条目。两个方向使用不同的归纳：读取条目时以隶属归纳排除无穷下降，生成全部标准条目时则对自然数作普通归纳。恢复出的元数与分解始终留在命题截断之下，而该公式不对任意候选集合中可能存在的非有序对成员作出断言。
<!--ja-->
## まとめ

環境の塔には、後で必要となる二つの形がそろった。一つは、要素がちょうど標準的な順序対 `(# n, envSet W n)` である実際の構成可能集合である。もう一つは、隣り合うアリティごとに、その符号化順序対の項目を読み取り、生成する Δ₀ 論理式である。二つの向きでは異なる帰納法を使う。項目を読むときは所属帰納によって無限降下を排除し、標準項目をすべて生成するときは自然数に関する通常の帰納法を使う。復元されたアリティと分解はつねに命題的切り詰めのもとにあり、この論理式は、任意の候補集合に含まれうる非順序対の要素について何も主張しない。
<!--/-->

<!--en-->
# Finite environments as set-coded graphs
<!--zh-->
# 作为集合编码图的有穷环境
<!--ja-->
# 集合で符号化した有限環境
<!--/-->

<!--en-->
This chapter represents a finite variable assignment by a set of numeral-value pairs, proves exact lookup in that graph, and defines the set-level operations used when satisfaction passes under a quantifier.
<!--zh-->
本章用数码与值的有序对之集表示有穷变元赋值，证明该图中的精确查值，并定义满足关系进入量词之下时使用的集合层运算。
<!--ja-->
本章では有限な変数割当てを数項と値の対の集合で表し、そのグラフでの正確な参照を証明し、充足関係が量化子の内側へ進むときに使う集合上の操作を定義します。
<!--/-->

<!--en-->
A certificate that talks about satisfaction has to talk about environments, and
an environment is a function from variable indices to sets. Functions are not
sets of the hierarchy, so this chapter encodes them: an environment becomes its
graph, the set of pairs of an index with the value there.

The encoding pays off immediately, because the index side is a numeral and the
previous chapter already made numerals injective. So the graph really is a
function graph: at the key for `i` there sits exactly the value at `i`, and
nothing else. That lemma is the whole point of the chapter, and the atomic clause
of a satisfaction certificate is where it gets spent.

Two more readers follow, for the two things a certificate does with an
environment: look a value up, and extend the environment when it goes under a
quantifier. Extension is von Neumann successor at the index side, so the second
reader characterizes the successor. The chapter closes with the set of *all*
finite sequences over a given set, which is the canonical place an environment
lives when a certificate has to quantify over environments rather than exhibit
one.
<!--zh-->
谈论满足关系的证书必须谈论环境，而环境是从变元序号到集合的函数。函数不是层级中的集合，故本章把它们编码：环境成为它的图，即序号与该处取值配成的对的集合。

编码立刻有回报，因为序号那一侧是数码，而上一章已经使数码单射。于是这个图确实是函数图：在 `i` 的键处恰好坐着 `i` 处的值，别无他物。那条引理就是本章的全部要点，而满足证书的原子子句正是花掉它的地方。

随后还有两条读式，对应证书对环境所做的两件事：查出一个值，以及在下降到量词之下时扩张环境。扩张在序号一侧就是 von Neumann 后继，故第二条读式刻画后继。本章以「给定集合上全体有穷序列」的集合收尾，那是证书需要对环境作量化 (而非拿出某一个) 时，环境的典范居所。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Coding.Environment {ℓ : Level} where

open import FOL.Syntax using ( var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; ∀̇∈; ∃̇∈; ⊥̇ )
open import FOL.LevyHierarchy using ( checkΔ₀; Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-∀∈ )
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-inl; ∈sucV-elim )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′ )
open import L.Coding.PairFormulas {ℓ}
  using ( prAt; prAt-adequate; prChar-fwd; prChar-bwd
        ; ∈pair-introL; ∈pair-introR )

open import Cubical.Data.Unit using ( tt )
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as E hiding ( elim )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.FinData using ( toℕ; inj-toℕ )
open import Cubical.HITs.CumulativeHierarchy.Base
  using ( V; sett; setIsSet; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; _⊆_; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( sucV; #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module Sem = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open Sem using ( _^_ )
open Sem.At (V ℓ) id using ( _⊨_; ⟦_⟧ )
```

<!--en-->
## The graph of an environment
<!--zh-->
## 环境的图
<!--ja-->
## 環境のグラフと参照
<!--/-->

<!--en-->
`env g` collects the pairs `⟨# i , g i⟩`, while `lookup-spec` proves that the value paired with the key for `i` is exactly `g i`.
<!--zh-->
`env g` 汇集有序对 `⟨# i , g i⟩`，而 `lookup-spec` 证明与 `i` 的键配对的值恰为 `g i`。
<!--ja-->
`env g` は対 `⟨# i , g i⟩` を集め、`lookup-spec` は `i` の鍵と対になる値がちょうど `g i` であることを示します。
<!--/-->

<!--en-->
An environment of length `n` becomes the set of pairs of the numeral for an index
with the value there. The index type is finite, hence small, so the gathering is
legitimate; membership is definitional.
<!--zh-->
长度为 `n` 的环境成为「序号的数码与该处取值」之对的集合。索引类型有穷，故小，这次汇集合法；隶属关系按定义成立。
<!--/-->

```agda
env : ∀ {n} → (Fin n → V ℓ) → V ℓ
env {n} g = sett (Lift {ℓ-zero} {ℓ} (Fin n))
                 (λ li → pr (# (toℕ (lower li))) (g (lower li)))

```

<!--en-->
And the lemma the chapter exists for: the graph is *functional*. A pair sits in
it at key `i` exactly when its second component is the value at `i`. Forwards,
the Kuratowski pair is injective, so the key of the witnessing entry equals the
key asked about; numerals are injective, so the indices agree; and the index type
embeds in the naturals, so the two indices are the same. Backwards is the entry
itself.
<!--zh-->
然后是本章为之存在的那条引理：这个图是**函数性的**。一个对在键 `i` 处属于它，恰当其第二分量是 `i` 处的值。正向：Kuratowski 对单射，故作证条目的键等于所问的键；数码单射，故序号相符；而索引类型嵌入自然数，故两个序号相同。反向就是那个条目本身。
<!--/-->

```agda
lookup-spec : ∀ {n} (g : Fin n → V ℓ) (i : Fin n) (v : V ℓ)
  → (pr (# (toℕ i)) v ∈ env g) ≡ ((v ≡ g i) , setIsSet v (g i))
lookup-spec {n} g i v = ⇔toPath fwd bwd
  where
  step : (lj : Lift {ℓ-zero} {ℓ} (Fin n))
       → pr (# (toℕ (lower lj))) (g (lower lj)) ≡ pr (# (toℕ i)) v
       → v ≡ g i
  step lj e = sym (ps .snd) ∙ cong g (inj-toℕ (#-inj′ (ps .fst)))
    where
    ps : (# (toℕ (lower lj)) ≡ # (toℕ i)) × (g (lower lj) ≡ v)
    ps = pr-inj e
  fwd : ⟨ pr (# (toℕ i)) v ∈ env g ⟩ → v ≡ g i
  fwd = PT.rec (setIsSet v (g i)) (λ { (lj , e) → step lj e })
  bwd : v ≡ g i → ⟨ pr (# (toℕ i)) v ∈ env g ⟩
  bwd e = ∣ lift i , cong (pr (# (toℕ i))) (sym e) ∣₁
```

<!--en-->
## Recognizing successor indices
<!--zh-->
## 识别后继索引
<!--ja-->
## 後者となる添字を認識する
<!--/-->

<!--en-->
`sucAt i j` is a bounded formula saying that the value at `j` is the von Neumann successor of the value at `i`; `sucAt-adequate` proves this semantic characterization.
<!--zh-->
有界公式 `sucAt i j` 表示 `j` 处的值是 `i` 处的值的 von Neumann 后继；`sucAt-adequate` 证明这一语义刻画。
<!--ja-->
有界式 `sucAt i j` は `j` での値が `i` での値の von Neumann 後者であることを表し、`sucAt-adequate` がこの意味論的特徴づけを証明します。
<!--/-->

<!--en-->
Extending an environment shifts every index up by one, and on numerals that is
the von Neumann successor. So a certificate that descends under a binder needs to
say "this index is the successor of that one", which is three clauses: the
smaller belongs to the larger, everything below the smaller is below the larger,
and everything below the larger is below the smaller or equal to it.
<!--zh-->
扩张环境把每个序号上移一位，而在数码上那就是 von Neumann 后继。故下降到约束之下的证书需要说「这个序号是那个的后继」，即三条子句：小者属于大者；小者之下的一切都在大者之下；而大者之下的一切，或在小者之下，或与小者相等。
<!--/-->

```agda
sucAt : ∀ {n} → Fin n → Fin n → Formula (V ℓ) n
sucAt i j = (var i ∈̇ var j)
         ∧̇ ((∀̇∈ (var i) (var zero ∈̇ var (suc j)))
         ∧̇ (∀̇∈ (var j) ((var zero ∈̇ var (suc i)) ∨̇ (var zero ≐ var (suc i)))))

Δ₀-sucAt : ∀ {n} (i j : Fin n) → Δ₀ (sucAt i j)
Δ₀-sucAt i j = δ-∧ δ-∈ (δ-∧ (δ-∀∈ δ-∈) (δ-∀∈ (δ-∨ δ-∈ δ-≐)))

private
  suc-char : (I J : V ℓ)
    → ⟨ I ∈ J ⟩
    → ((z : V ℓ) → ⟨ z ∈ I ⟩ → ⟨ z ∈ J ⟩)
    → ((z : V ℓ) → ⟨ z ∈ J ⟩ → ∥ ⟨ z ∈ I ⟩ ⊎ (z ≡ I) ∥₁)
    → J ≡ sucV I
  suc-char I J hIJ mono cover = extensionality J (sucV I) (sub₁ , sub₂)
    where
    sub₁ : ⟨ J ⊆ sucV I ⟩
    sub₁ z z∈ₛJ = PT.rec ((z ∈ₛ sucV I) .snd)
      (Sum.rec
        (λ h → ∈∈ₛ {a = z} {b = sucV I} .fst (∈sucV-inl {A = I} {x = z} h))
        (λ e → subst (λ w → ⟨ w ∈ₛ sucV I ⟩) (sym e)
                 (∈∈ₛ {a = I} {b = sucV I} .fst (self∈sucV I))))
      (cover z (∈∈ₛ {a = z} {b = J} .snd z∈ₛJ))
    sub₂ : ⟨ sucV I ⊆ J ⟩
    sub₂ z z∈ₛs = ∈∈ₛ {a = z} {b = J} .fst
      (∈sucV-elim {A = I} {x = z} {P = ⟨ z ∈ J ⟩} ((z ∈ J) .snd)
        (∈∈ₛ {a = z} {b = sucV I} .snd z∈ₛs)
        (λ h → mono z h)
        (λ e → subst (λ w → ⟨ w ∈ J ⟩) (sym e) hIJ))

  suc-intro : (I J : V ℓ) → J ≡ sucV I
    → ⟨ I ∈ J ⟩
    × (((z : V ℓ) → ⟨ z ∈ I ⟩ → ⟨ z ∈ J ⟩)
    × ((z : V ℓ) → ⟨ z ∈ J ⟩ → ∥ ⟨ z ∈ I ⟩ ⊎ (z ≡ I) ∥₁))
  suc-intro I J e =
      subst (λ w → ⟨ I ∈ w ⟩) (sym e) (self∈sucV I)
    , (λ z h → subst (λ w → ⟨ z ∈ w ⟩) (sym e) (∈sucV-inl {A = I} {x = z} h))
    , (λ z z∈J → ∈sucV-elim {A = I} {x = z} {P = ∥ ⟨ z ∈ I ⟩ ⊎ (z ≡ I) ∥₁} squash₁
        (subst (λ w → ⟨ z ∈ w ⟩) e z∈J)
        (λ h → ∣ inl h ∣₁)
        (λ q → ∣ inr q ∣₁))

sucAt-adequate : ∀ {n} (i j : Fin n) (γ : (V ℓ) ^ n)
  → (γ ⊨ sucAt i j) ≡ ((⟦ var j ⟧ γ ≡ sucV (⟦ var i ⟧ γ)) , setIsSet _ _)
sucAt-adequate i j γ = ⇔toPath
  (λ { (h₁ , h₂ , h₃) → suc-char (⟦ var i ⟧ γ) (⟦ var j ⟧ γ) h₁ h₂ h₃ })
  (suc-intro (⟦ var i ⟧ γ) (⟦ var j ⟧ γ))
```

<!--en-->
## Shifting an entry
<!--zh-->
## 移位一个条目
<!--ja-->
## 一つの項目をずらす
<!--/-->

<!--en-->
`shiftPairAt p' p` recognizes when the pair at `p'` is obtained from the pair at `p` by replacing its numeral key with its successor and leaving the value unchanged.
<!--zh-->
`shiftPairAt p' p` 识别如下情形：把 `p` 处有序对的数码键换成其后继并保持值不变，便得到 `p'` 处的有序对。
<!--ja-->
`shiftPairAt p' p` は、`p` にある対の数項の鍵をその後者に置き換え、値を変えずに得られる対が `p'` にあることを認識します。
<!--/-->

<!--en-->
Extending an environment does not only add an entry, it renumbers the ones
already there: what was at index `i` is now at index `i + 1`. The formula below
recognizes one such renumbering, relating an entry to its shifted counterpart.

Five nested bounded quantifiers, which is what it costs to reach the components
of two pairs at once: the entry, its index, its value, the shifted entry and its
index. The body is then two Kuratowski readers and the successor reader from
above, saying that the two entries share a value and that the indices are one
apart. Everything the reader chapters built is spent here at once, which is why
this is the last formula the coding stack needs.
<!--zh-->
扩张环境不只是添一个条目，它还给已有的条目重新编号：原本在索引 `i` 处的，如今在 `i + 1` 处。下面这条公式认出一次这样的重编号，把一个条目与它移位后的对应物联系起来。

五层嵌套的有界量词，那是一举抵达两个对的各个分量所需的代价：条目、它的索引、它的值、移位后的条目、以及后者的索引。主体随后是两条 Kuratowski 读式与上文那条后继读式，说这两个条目共享一个值，且两个索引相差一位。读式诸章造出的一切在此一次花光，这也是编码这一层所需的最后一条公式。
<!--/-->

```agda
shiftPairAt : ∀ {n} → Fin n → Fin n → Formula (V ℓ) n
shiftPairAt p' p =
  ∃̇∈ (var p)
    (∃̇∈ (var zero)
      (∃̇∈ (var (suc zero))
        (∃̇∈ (var (suc (suc (suc p'))))
          (∃̇∈ (var zero)
            ( prAt (suc (suc (suc (suc (suc p)))))
                   (suc (suc (suc zero))) (suc (suc zero))
            ∧̇ ( prAt (suc (suc (suc (suc (suc p'))))) zero (suc (suc zero))
            ∧̇ sucAt (suc (suc (suc zero))) zero ))))))

shiftPairAt-adequate : ∀ {n} (p' p : Fin n) (γ : (V ℓ) ^ n)
  → (γ ⊨ shiftPairAt p' p)
  ≡ (∥ Σ[ i ∈ V ℓ ] Σ[ v ∈ V ℓ ]
       ((⟦ var p ⟧ γ ≡ pr i v) × (⟦ var p' ⟧ γ ≡ pr (sucV i) v)) ∥₁ , squash₁)
shiftPairAt-adequate p' p γ = ⇔toPath fwd bwd
  where
  P = ⟦ var p ⟧ γ
  P' = ⟦ var p' ⟧ γ
  Tgt : Type (ℓ-suc ℓ)
  Tgt = ∥ Σ[ i ∈ V ℓ ] Σ[ v ∈ V ℓ ] ((P ≡ pr i v) × (P' ≡ pr (sucV i) v)) ∥₁

  conclude : (c i v c' j : V ℓ)
    → ⟨ (j ∷ c' ∷ v ∷ i ∷ c ∷ γ)
        ⊨ prAt (suc (suc (suc (suc (suc p))))) (suc (suc (suc zero))) (suc (suc zero)) ⟩
    → ⟨ (j ∷ c' ∷ v ∷ i ∷ c ∷ γ)
        ⊨ prAt (suc (suc (suc (suc (suc p'))))) zero (suc (suc zero)) ⟩
    → ⟨ (j ∷ c' ∷ v ∷ i ∷ c ∷ γ) ⊨ sucAt (suc (suc (suc zero))) zero ⟩
    → Tgt
  conclude c i v c' j sat₁ sat₂ sat₃ =
    ∣ i , v
    , subst ⟨_⟩
        (prAt-adequate (suc (suc (suc (suc (suc p)))))
          (suc (suc (suc zero))) (suc (suc zero)) (j ∷ c' ∷ v ∷ i ∷ c ∷ γ))
        sat₁
    , (subst ⟨_⟩
        (prAt-adequate (suc (suc (suc (suc (suc p'))))) zero (suc (suc zero))
          (j ∷ c' ∷ v ∷ i ∷ c ∷ γ))
        sat₂
       ∙ cong (λ z → pr z v)
          (subst ⟨_⟩
            (sucAt-adequate (suc (suc (suc zero))) zero (j ∷ c' ∷ v ∷ i ∷ c ∷ γ))
            sat₃))
    ∣₁

  fwd : ⟨ γ ⊨ shiftPairAt p' p ⟩ → Tgt
  fwd = PT.rec squash₁ (λ { (c , _ , h₁) → PT.rec squash₁
    (λ { (i , _ , h₂) → PT.rec squash₁
      (λ { (v , _ , h₃) → PT.rec squash₁
        (λ { (c' , _ , h₄) → PT.rec squash₁
          (λ { (j , _ , sat₁ , sat₂ , sat₃) → conclude c i v c' j sat₁ sat₂ sat₃ })
          h₄ })
        h₃ })
      h₂ })
    h₁ })

  build : (i v : V ℓ) → P ≡ pr i v → P' ≡ pr (sucV i) v → ⟨ γ ⊨ shiftPairAt p' p ⟩
  build i v eP eP' =
    ∣ ⁅ i , v ⁆
    , subst (λ z → ⟨ ⁅ i , v ⁆ ∈ z ⟩) (sym eP)
        (∈pair-introR {u = ⁅ i ⁆s} {v = ⁅ i , v ⁆} {y = ⁅ i , v ⁆} refl)
    , ∣ i , ∈pair-introL {u = i} {v = v} {y = i} refl
      , ∣ v , ∈pair-introR {u = i} {v = v} {y = v} refl
        , ∣ ⁅ sucV i , v ⁆
          , subst (λ z → ⟨ ⁅ sucV i , v ⁆ ∈ z ⟩) (sym eP')
              (∈pair-introR {u = ⁅ sucV i ⁆s} {v = ⁅ sucV i , v ⁆}
                            {y = ⁅ sucV i , v ⁆} refl)
          , ∣ sucV i
            , ∈pair-introL {u = sucV i} {v = v} {y = sucV i} refl
            , subst ⟨_⟩
                (sym (prAt-adequate (suc (suc (suc (suc (suc p)))))
                  (suc (suc (suc zero))) (suc (suc zero))
                  (sucV i ∷ ⁅ sucV i , v ⁆ ∷ v ∷ i ∷ ⁅ i , v ⁆ ∷ γ)))
                eP
            , subst ⟨_⟩
                (sym (prAt-adequate (suc (suc (suc (suc (suc p'))))) zero (suc (suc zero))
                  (sucV i ∷ ⁅ sucV i , v ⁆ ∷ v ∷ i ∷ ⁅ i , v ⁆ ∷ γ)))
                eP'
            , subst ⟨_⟩
                (sym (sucAt-adequate (suc (suc (suc zero))) zero
                  (sucV i ∷ ⁅ sucV i , v ⁆ ∷ v ∷ i ∷ ⁅ i , v ⁆ ∷ γ)))
                refl
            ∣₁
          ∣₁
        ∣₁
      ∣₁
    ∣₁

  bwd : Tgt → ⟨ γ ⊨ shiftPairAt p' p ⟩
  bwd = PT.rec ((γ ⊨ shiftPairAt p' p) .snd)
    (λ { (i , v , eP , eP') → build i v eP eP' })
```

<!--en-->
## Coding the empty entry
<!--zh-->
## 编码空条目
<!--ja-->
## 空の項目を符号化する
<!--/-->

<!--en-->
The formulas `sgl0At`, `pair0At`, and `tag0At` recognize the singleton, Kuratowski pair, and tagged pair used for the new zeroth environment entry; their semantic lemmas recover each encoded component.
<!--zh-->
公式 `sgl0At`、`pair0At` 与 `tag0At` 识别新添的第零个环境条目所用的单点集、Kuratowski 对与带标签对；相应的充分阶段条件引理恢复各编码分量。
<!--ja-->
式 `sgl0At`、`pair0At`、`tag0At` は、新しい第 0 環境項目に使う一元集合、Kuratowski 対、タグ付き対を認識し、対応する十分な段階の条件を示す補題が各符号化成分を復元します。
<!--/-->

<!--en-->
The tag this chapter's extension reader uses is `# 0`, and `# 0` is the empty
set by definition. So the tag is said without a constant: a member is empty. The
readers below are the empty versions of the tagged ones. The meta machinery
proves that a set satisfying the empty tag is the Kuratowski pair with the empty
set as first component. The singleton and unordered pair share the same
empty-member witness. Mapping their two predicates together carries the whole
pair characterization in either direction.
<!--zh-->
本章扩展读式所用的标签是 `# 0`，而 `# 0` 按定义就是空集。于是标签可以不借常元说出：一个成员是空的。下面几条读式就是空版的带标签版本。元层机制证明：满足空标签读式的集合，恰是以空集为第一分量的 Kuratowski 对。单点集与无序对共享同一个空成员见证。一起映射这两个谓词，就能在两个方向搬运整条有序对刻画。
<!--/-->

```agda
sgl0At : ∀ {n} → Fin n → Formula (V ℓ) n
sgl0At k = (∃̇∈ (var k) (∀̇∈ (var zero) ⊥̇))
        ∧̇ (∀̇∈ (var k) (∀̇∈ (var zero) ⊥̇))

pair0At : ∀ {n} → Fin n → Fin n → Formula (V ℓ) n
pair0At k j = (∃̇∈ (var k) (∀̇∈ (var zero) ⊥̇))
           ∧̇ ((var j ∈̇ var k)
           ∧̇ (∀̇∈ (var k) ((∀̇∈ (var zero) ⊥̇) ∨̇ (var zero ≐ var (suc j)))))

tag0At : ∀ {n} → Fin n → Fin n → Formula (V ℓ) n
tag0At s x = (∃̇∈ (var s) (sgl0At zero))
          ∧̇ ((∃̇∈ (var s) (pair0At zero (suc x)))
          ∧̇ (∀̇∈ (var s) (sgl0At zero ∨̇ pair0At zero (suc x))))

private
  Empty' : V ℓ → Type (ℓ-suc ℓ)
  Empty' z = (y : V ℓ) → ⟨ y ∈ z ⟩ → E.⊥* {ℓ-suc ℓ}

  empty'→∅ : (z : V ℓ) → Empty' z → z ≡ ∅
  empty'→∅ z hz = extensionalV (λ y → ⇔toPath
    (λ h → E.rec (lower (hz y h)))
    (λ h → E.rec (∅-empty y (∈∈ₛ {a = y} {b = ∅} .fst h))))

  ∅→empty' : (z : V ℓ) → z ≡ ∅ → Empty' z
  ∅→empty' z e y y∈z = lift (∅-empty y (∈∈ₛ {a = y} {b = ∅} .fst (subst (λ w → ⟨ y ∈ w ⟩) e y∈z)))

  EmptySgl : V ℓ → Type (ℓ-suc ℓ)
  EmptySgl w = ∥ Σ[ z ∈ V ℓ ] (⟨ z ∈ w ⟩ × Empty' z) ∥₁
            × ((z : V ℓ) → ⟨ z ∈ w ⟩ → Empty' z)

  EmptyPair : V ℓ → V ℓ → Type (ℓ-suc ℓ)
  EmptyPair W w = ∥ Σ[ z ∈ V ℓ ] (⟨ z ∈ w ⟩ × Empty' z) ∥₁
               × (⟨ W ∈ w ⟩ × ((z : V ℓ) → ⟨ z ∈ w ⟩ → ∥ Empty' z ⊎ (z ≡ W) ∥₁))

  SglOf∅ : V ℓ → Type (ℓ-suc ℓ)
  SglOf∅ w = ⟨ ∅ ∈ w ⟩ × ((z : V ℓ) → ⟨ z ∈ w ⟩ → z ≡ ∅)

  PairOf∅ : V ℓ → V ℓ → Type (ℓ-suc ℓ)
  PairOf∅ W w = ⟨ ∅ ∈ w ⟩ × (⟨ W ∈ w ⟩ × ((z : V ℓ) → ⟨ z ∈ w ⟩ → ∥ (z ≡ ∅) ⊎ (z ≡ W) ∥₁))

  empty-member : (w : V ℓ) → ∥ Σ[ z ∈ V ℓ ] (⟨ z ∈ w ⟩ × Empty' z) ∥₁ → ⟨ ∅ ∈ w ⟩
  empty-member w = PT.rec ((∅ ∈ w) .snd)
    (λ { (z , hz , ez) → subst (λ u → ⟨ u ∈ w ⟩) (empty'→∅ z ez) hz })

  EmptySgl→SglOf∅ : (w : V ℓ) → EmptySgl w → SglOf∅ w
  EmptySgl→SglOf∅ w (h₁ , hall) = empty-member w h₁ , (λ z hz → empty'→∅ z (hall z hz))

  EmptyPair→PairOf∅ : (W w : V ℓ) → EmptyPair W w → PairOf∅ W w
  EmptyPair→PairOf∅ W w (h₁ , hW , hall) = empty-member w h₁ , hW
    , (λ z hz → PT.map (Sum.map (empty'→∅ z) (λ e → e)) (hall z hz))

  SglOf∅→EmptySgl : (w : V ℓ) → SglOf∅ w → EmptySgl w
  SglOf∅→EmptySgl w (h∅ , hall) =
      (∣ ∅ , (h∅ , ∅→empty' ∅ refl) ∣₁)
    , (λ z z∈w → ∅→empty' z (hall z z∈w))

  PairOf∅→EmptyPair : (W w : V ℓ) → PairOf∅ W w → EmptyPair W w
  PairOf∅→EmptyPair W w (h∅ , hW , hall) =
      (∣ ∅ , (h∅ , ∅→empty' ∅ refl) ∣₁)
    , (hW , λ z z∈w → PT.map (Sum.rec (λ e → inl (∅→empty' z e)) (λ e → inr e))
        (hall z z∈w))

  PairWitness : (V ℓ → Type (ℓ-suc ℓ)) → (V ℓ → Type (ℓ-suc ℓ)) → V ℓ → Type (ℓ-suc ℓ)
  PairWitness P R Q = ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × P w) ∥₁
    × (∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × R w) ∥₁
    × ((y : V ℓ) → ⟨ y ∈ Q ⟩ → ∥ P y ⊎ R y ∥₁))

  map-witness : {P R P' R' : V ℓ → Type (ℓ-suc ℓ)} (Q : V ℓ)
    → ((w : V ℓ) → P w → P' w) → ((w : V ℓ) → R w → R' w)
    → PairWitness P R Q → PairWitness P' R' Q
  map-witness Q f g (h₁ , h₂ , h₃) =
      PT.map (λ { (w , hw , h) → w , hw , f w h }) h₁
    , PT.map (λ { (w , hw , h) → w , hw , g w h }) h₂
    , (λ y hy → PT.map (Sum.map (f y) (g y)) (h₃ y hy))

prChar∅-fwd : (Q W : V ℓ)
  → ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × EmptySgl w) ∥₁
  → ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × EmptyPair W w) ∥₁
  → ((y : V ℓ) → ⟨ y ∈ Q ⟩ → ∥ EmptySgl y ⊎ EmptyPair W y ∥₁)
  → Q ≡ pr ∅ W
prChar∅-fwd Q W h₁ h₂ h₃ = prChar-fwd Q ∅ W (fst h) (fst (snd h)) (snd (snd h))
  where
  h : PairWitness SglOf∅ (PairOf∅ W) Q
  h = map-witness Q EmptySgl→SglOf∅ (EmptyPair→PairOf∅ W) (h₁ , h₂ , h₃)

prChar∅-bwd : (Q W : V ℓ) → Q ≡ pr ∅ W
  → ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × EmptySgl w) ∥₁
  × (∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × EmptyPair W w) ∥₁
  × ((y : V ℓ) → ⟨ y ∈ Q ⟩ → ∥ EmptySgl y ⊎ EmptyPair W y ∥₁))
prChar∅-bwd Q W e = map-witness Q SglOf∅→EmptySgl (PairOf∅→EmptyPair W) (prChar-bwd Q ∅ W e)

tag0At-adequate : ∀ {n} (s x : Fin n) (γ : (V ℓ) ^ n)
                → (γ ⊨ tag0At s x) ≡ ((⟦ var s ⟧ γ ≡ pr ∅ (⟦ var x ⟧ γ)) , setIsSet _ _)
tag0At-adequate s x γ = ⇔toPath
  (λ { (h₁ , h₂ , h₃) → prChar∅-fwd _ _ h₁ h₂ h₃ })
  (λ e → prChar∅-bwd _ _ e)
```

<!--en-->
## Extending an environment
<!--zh-->
## 扩张环境
<!--ja-->
## 環境を拡張する
<!--/-->

<!--en-->
`cons a g` puts `a` at index zero and shifts every old entry by one; `consAt` expresses exactly this graph transformation and `consAt-adequate` proves the equivalence.
<!--zh-->
`cons a g` 把 `a` 放在索引零处，并把每个旧条目上移一位；`consAt` 恰好表达这一图变换，`consAt-adequate` 证明相应等价。
<!--ja-->
`cons a g` は `a` を添字 0 に置き、すべての旧項目を一つずつずらします。`consAt` はこのグラフ変換を正確に表し、`consAt-adequate` がその同値性を証明します。
<!--/-->

<!--en-->
And the formula the quantifier clauses need: the extended environment is the old
one with a new value at index zero. Three clauses. The entry at key zero holds the
new value; every entry of the old environment appears shifted in the new one; and
every entry of the new one is either that first entry or a shift of an old one.

The semantic characterization is stated against an *encoded* environment, because that is the form the
certificates hold. Given that the old environment is the graph of `g`, satisfaction
of the formula says exactly that the new one is the graph of `g` with the value
consed on. The two sides match key by key, and the match is definitional at the
index: the numeral for `suc k` is the successor of the numeral for `k`, and
consing shifts indices by exactly that.
<!--zh-->
然后是量词子句所需的那条公式：扩张后的环境就是旧环境在索引零处添上一个新值。三条子句。键零处的条目持有新值；旧环境的每个条目在新环境中移位出现；而新环境的每个条目，或是那第一个条目，或是某个旧条目的移位。

充分性是对**编码后的**环境陈述的，因为那是诸证书所持有的形式。给定旧环境是 `g` 的图，该公式的满足恰好说新环境是 `g` 前置一个值之后的图。两侧逐键相符，而在索引上这个相符是定义性的：`suc k` 的数码就是 `k` 的数码的后继，而前置恰好把索引移那么多。
<!--/-->

```agda
cons : ∀ {ℓ'} {X : Type ℓ'} {n : ℕ} → X → (Fin n → X) → Fin (suc n) → X
cons m g zero    = m
cons m g (suc i) = g i

consAt : ∀ {n} → Fin n → Fin n → Fin n → Formula (V ℓ) n
consAt e' m e =
  (∃̇∈ (var e') (tag0At zero (suc m)))
  ∧̇ ((∀̇∈ (var e) (∃̇∈ (var (suc e')) (shiftPairAt zero (suc zero))))
  ∧̇ (∀̇∈ (var e') ((tag0At zero (suc m))
                   ∨̇ (∃̇∈ (var (suc e)) (shiftPairAt (suc zero) zero)))))

Δ₀-consAt : ∀ {n} (e' m e : Fin n) → Δ₀ (consAt e' m e)
Δ₀-consAt e' m e = checkΔ₀ (consAt e' m e) tt

consAt-adequate : ∀ {n} (e' m e : Fin n) (γ : (V ℓ) ^ n)
  {k : ℕ} (g : Fin k → V ℓ)
  → ⟦ var e ⟧ γ ≡ env g
  → (γ ⊨ consAt e' m e)
  ≡ ((⟦ var e' ⟧ γ ≡ env (cons (⟦ var m ⟧ γ) g)) , setIsSet _ _)
consAt-adequate e' m e γ {k} g hE = ⇔toPath fwd bwd
  where
  M = ⟦ var m ⟧ γ
  E = ⟦ var e ⟧ γ
  E' = ⟦ var e' ⟧ γ
  G' : Fin (suc k) → V ℓ
  G' = cons M g

  shift-path : {a b x y : V ℓ} → pr a x ≡ pr b y → pr (sucV a) x ≡ pr (sucV b) y
  shift-path {a} {b} {x} {y} e = cong₂ (λ a b → pr (sucV a) b) (fst p) (snd p)
    where
    p : (a ≡ b) × (x ≡ y)
    p = pr-inj e

  classify : ((y : V ℓ) → ⟨ y ∈ E' ⟩
               → ∥ ⟨ (y ∷ γ) ⊨ tag0At zero (suc m) ⟩
                 ⊎ ⟨ (y ∷ γ) ⊨ ∃̇∈ (var (suc e)) (shiftPairAt (suc zero) zero) ⟩ ∥₁)
           → (y : V ℓ) → ⟨ y ∈ E' ⟩ → ⟨ y ∈ env G' ⟩
  classify h₃ y y∈E' = PT.rec ((y ∈ env G') .snd)
    (Sum.rec
      (λ tsat →
        ∣ lift zero
        , sym (subst ⟨_⟩ (tag0At-adequate zero (suc m) (y ∷ γ)) tsat) ∣₁)
      (λ ssat → PT.rec ((y ∈ env G') .snd)
        (λ { (p , p∈E , sh) → PT.rec ((y ∈ env G') .snd)
          (λ { (li , peq) → PT.rec ((y ∈ env G') .snd)
            (λ { (i , v , epv , eyv) →
                ∣ lift (suc (lower li))
                , sym (shift-path (sym epv ∙ sym peq))
                ∙ sym eyv ∣₁ })
            (subst ⟨_⟩ (shiftPairAt-adequate (suc zero) zero (p ∷ y ∷ γ)) sh) })
          (subst (λ z → ⟨ p ∈ z ⟩) hE p∈E) })
        ssat))
    (h₃ y y∈E')

  covered : ⟨ γ ⊨ ∃̇∈ (var e') (tag0At zero (suc m)) ⟩
          → ((p : V ℓ) → ⟨ p ∈ E ⟩
              → ⟨ (p ∷ γ) ⊨ ∃̇∈ (var (suc e')) (shiftPairAt zero (suc zero)) ⟩)
          → (y : V ℓ) → ⟨ y ∈ env G' ⟩ → ⟨ y ∈ E' ⟩
  covered h₁ h₂ y y∈G' = PT.rec ((y ∈ E') .snd)
    (λ { (lj , eq) → byKey (lower lj) eq })
    y∈G'
    where
    byKey : (j : Fin (suc k)) → pr (# (toℕ j)) (G' j) ≡ y → ⟨ y ∈ E' ⟩
    byKey zero eq = PT.rec ((y ∈ E') .snd)
      (λ { (q , q∈E' , tsat) →
        subst (λ z → ⟨ z ∈ E' ⟩)
          (subst ⟨_⟩ (tag0At-adequate zero (suc m) (q ∷ γ)) tsat ∙ eq)
          q∈E' })
      h₁
    byKey (suc i₀) eq = PT.rec ((y ∈ E') .snd)
      (λ { (p' , p'∈E' , sh) → PT.rec ((y ∈ E') .snd)
        (λ { (i , v , epv , ep'v) →
          subst (λ z → ⟨ z ∈ E' ⟩)
            (ep'v
             ∙ shift-path (sym epv)
             ∙ eq)
            p'∈E' })
        (subst ⟨_⟩
          (shiftPairAt-adequate zero (suc zero) (p' ∷ pr (# (toℕ i₀)) (g i₀) ∷ γ)) sh) })
      (h₂ (pr (# (toℕ i₀)) (g i₀))
          (subst (λ z → ⟨ pr (# (toℕ i₀)) (g i₀) ∈ z ⟩) (sym hE) ∣ lift i₀ , refl ∣₁))

  fwd : ⟨ γ ⊨ consAt e' m e ⟩ → E' ≡ env G'
  fwd (h₁ , h₂ , h₃) = extensionalV
    (λ y → ⇔toPath (classify h₃ y) (covered h₁ h₂ y))

  bwd : E' ≡ env G' → ⟨ γ ⊨ consAt e' m e ⟩
  bwd e'eq =
      ∣ pr (# 0) M
      , subst (λ z → ⟨ pr (# 0) M ∈ z ⟩) (sym e'eq) ∣ lift zero , refl ∣₁
      , subst ⟨_⟩ (sym (tag0At-adequate zero (suc m) (pr (# 0) M ∷ γ))) refl ∣₁
    , (λ p p∈E → PT.rec
        (((p ∷ γ) ⊨ ∃̇∈ (var (suc e')) (shiftPairAt zero (suc zero))) .snd)
        (λ { (li , peq) →
          ∣ pr (# (suc (toℕ (lower li)))) (g (lower li))
          , subst (λ z → ⟨ pr (# (suc (toℕ (lower li)))) (g (lower li)) ∈ z ⟩)
              (sym e'eq) ∣ lift (suc (lower li)) , refl ∣₁
          , subst ⟨_⟩
              (sym (shiftPairAt-adequate zero (suc zero)
                (pr (# (suc (toℕ (lower li)))) (g (lower li)) ∷ p ∷ γ)))
              ∣ # (toℕ (lower li)) , g (lower li) , sym peq , refl ∣₁ ∣₁ })
        (subst (λ z → ⟨ p ∈ z ⟩) hE p∈E))
    , (λ p' p'∈E' → PT.rec squash₁
        (λ { (lj , eq) → byKey' p' (lower lj) eq })
        (subst (λ z → ⟨ p' ∈ z ⟩) e'eq p'∈E'))
    where
    byKey' : (p' : V ℓ) (j : Fin (suc k))
           → pr (# (toℕ j)) (G' j) ≡ p'
           → ∥ ⟨ (p' ∷ γ) ⊨ tag0At zero (suc m) ⟩
             ⊎ ⟨ (p' ∷ γ) ⊨ ∃̇∈ (var (suc e)) (shiftPairAt (suc zero) zero) ⟩ ∥₁
    byKey' p' zero eq =
      ∣ inl (subst ⟨_⟩ (sym (tag0At-adequate zero (suc m) (p' ∷ γ))) (sym eq)) ∣₁
    byKey' p' (suc i₀) eq =
      ∣ inr ∣ pr (# (toℕ i₀)) (g i₀)
            , subst (λ z → ⟨ pr (# (toℕ i₀)) (g i₀) ∈ z ⟩) (sym hE)
                ∣ lift i₀ , refl ∣₁
            , subst ⟨_⟩
                (sym (shiftPairAt-adequate (suc zero) zero
                  (pr (# (toℕ i₀)) (g i₀) ∷ p' ∷ γ)))
                ∣ # (toℕ i₀) , g i₀ , refl , sym eq ∣₁ ∣₁ ∣₁
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
The chapter provides a set-coded environment with exact lookup and a bounded, semantically correct description of extension, which are the two environment operations needed by satisfaction clauses.
<!--zh-->
本章得到具有精确查值的集合编码环境，以及对环境扩张的有界且语义正确的描述；这正是满足关系子句所需的两种环境操作。
<!--ja-->
本章により、正確に参照できる集合符号化環境と、環境拡張の有界で意味論的に正しい記述が得られます。これらが充足関係の各条件に必要な二つの環境操作です。
<!--/-->

<!--en-->
An environment is its graph (`env`{.Agda}), and the graph is functional
(`lookup-spec`{.Agda}), which is what makes the encoding usable rather than
merely definable. `sucAt`{.Agda} recognizes the index shift that going under a
quantifier performs. `shiftPairAt`{.Agda} recognizes the renumbering that
extension performs, and `consAt`{.Agda} puts it to work: the extended
environment is the old one with a value consed on, stated against the encoded
form the certificates actually hold. That is the last formula the coding stack
owes the certificates.
<!--zh-->
环境就是它的图 (`env`{.Agda})，而图是函数性的 (`lookup-spec`{.Agda})，正是这一点使这套编码可用而不只是可定义。`sucAt`{.Agda} 认出下降到量词之下时所作的序号移位。`shiftPairAt`{.Agda} 认出扩张所作的重编号，而 `consAt`{.Agda} 把它用起来：扩张后的环境就是旧环境前置一个值，且是对诸证书实际持有的编码形式陈述的。那是编码这一层欠诸证书的最后一条公式。
<!--/-->

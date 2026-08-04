# The level formula

<!--en-->
The initial-segment chapter wrote the face once, generic in the carrier: the
story of the constructible tower told inside a carrier is one sentence, some
initial segment `f` of the tower lies in the carrier's binding set,
approximates the tower, applies the definable step at each stage, and ranges
over the member being read, and the face's adequacy makes the sentence and its
external reading interchangeable. This chapter supplies the first
instantiation, the wing's own `W2`, at the real tower: the carrier is a level
`Lset α`, and the approximation entry, which the face deliberately left as a
telescope slot, is now filled with the tower story itself. The result is the
level formula, the object-language sentence saying that a member of the level
is one of the constructible levels, with its two-way adequacy.

The tower story has three clauses here. The witness is a function, which
means a set of Kuratowski pairs with at most one value at each argument; it
maps the empty set to itself; and at every stage it applies the definable
step, the clause the initial-segment chapter read as its own Def-step entry
and which collapses at a level by the theorem that every member of a stage is
definable at a member of that stage. The chapter writes each clause twice,
once at the meta level over the graph and once as an object-language formula,
and proves the two-way decodes that make the object-language sentence mean the
story. The two remaining clauses of the classical story, the limit clause and
the ordinal domain bound, are measured here as the omitted pieces and reported
as such; each needs machinery the delivered cone has not yet stocked, and this
chapter stops at its line budget rather than pushing their decodes past it.
<!--zh-->
初始段章把面孔一次写成、以载体为参数：在某个载体内部讲述的可构造塔故事是一条句子，某条 L 塔初始段 `f` 落在载体的绑定集里、近似整座塔、在每个阶段施以可定义步、并以被读成员为像，而面孔的充分性使这条句子与它的外部读式可以互换。本章交付第一个实例化，即翼自己的 `W2`，落在真实塔上：载体是层 `Lset α`，而面孔刻意留作望远镜槽位的近似条目，现在由塔故事本身填满。成果就是层公式，那条说「载体的某个成员是可构造层之一」的对象语言句子，连同它的双向充分性。

塔故事在此有三条子句。见证是函数，即一个库拉托夫斯基对之集，且在每一自变量处至多一个值；它把空集映到自身；而在每个阶段它施以可定义步，这一条正是初始段章读作自己的 Def 步条目、并经「层的每个成员都在该层的某成员处可定义」这条定理在层处坍缩。本章把每条子句写两遍，一遍在元层跑在图关系上，一遍是对象语言公式，并证明使对象语言句子意指这个故事的双向解码。经典故事所余的两条子句，极限子句与序数定义域界，在此作为缺项被测度并照实报告；每条都需要已交付锥体尚未备好的机器，本章在行数预算处停下，而不把它们的解码推过界线。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.LevelFormula {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; _∈̇_; _≐_; _∧̇_; _⇒̇_; ¬̇_; ⊤̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using
  ( Lset; Lset-layer; layer-trans; Lset-in; Lset-out
  ; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ-inv; isTransV )
open import L.Definability {ℓ} using ( module DefOf )
open import L.PairAtoms {ℓ} using ( isPair; module PairMem; module PairKit )
open import L.InitialSegment {ℓ} using ( _⟷_; _∈ran_; DefStep; module Face )

import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit using ( tt* )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The tower story at the meta level
<!--zh-->
## 元层的塔故事
<!--/-->

<!--en-->
Everything below is relative to one level `u = Lset α` and its binding set
`K`, a member of that level. The level's transitivity, the kit's second
parameter, is the delivered stage theorem, and the pair atoms open at the
carrier. The story itself is a conjunction of three clauses, each stated at
the level of the graph: the pairs `pr a b` lying in the witness `f`.

Functionhood splits in two. `pairhood` says every member of `f` is a
Kuratowski pair, the delivered predicate of the pair-atom chapter; it is the
spine of the story. `singleValued` says the function's value is unique: two
pairs with the same first component agree on the second.

The zero clause says the witness maps the empty set to itself. The empty set
is the set with no members, so the clause names a memberless `a` with
`pr a a` lying in `f`, avoiding any constant in the object language.
<!--zh-->
以下一切都相对于某一层 `u = Lset α` 及其绑定集 `K`，即该层的一个成员。层的传递性，套件的第二个参数，就是已交付的阶段定理，而对原子在载体处打开。故事本身是三条子句的合取，每条都跑在图关系上：落在见证 `f` 里的对 `pr a b`。

函数性一分为二。`pairhood` 说 `f` 的每个成员都是库拉托夫斯基对，这是对原子章已交付的谓词，也是故事的脊梁；`singleValued` 说函数的值唯一：首分量相同的两个对，第二分量一致。

零子句说见证把空集映到自身。空集就是没有成员的集合，于是子句点名某个无成员的 `a`，使 `pr a a` 落在 `f` 里，对象语言不必引入常量。
<!--/-->

```agda
-- The tower story at the real tower, at the level of the graph.
module LevelAt (α : S) (K : ⟪ Lset α ⟫) where

  u : S
  u = Lset α

  utr : isTransV u
  utr = layer-trans (Lset-layer α)

  module U = DefOf u
  open U using ( SM; ι; _⊨ᵐ_; defSet )
  module PK = PairKit u utr
  module PM = PairMem u utr

  pairhood : S → Type (ℓ-suc ℓ)
  pairhood f = (z : S) → ⟨ z ∈ˢ f ⟩ → isPair z

  singleValued : S → Type (ℓ-suc ℓ)
  singleValued f = (a b c : S) → ⟨ pr a b ∈ˢ f ⟩ → ⟨ pr a c ∈ˢ f ⟩ → b ≡ c

  -- The zero clause: some memberless a has pr a a in f.
  zeroClause : S → Type (ℓ-suc ℓ)
  zeroClause f = ∥ Σ[ a ∈ S ]
    ( ((z : S) → ⟨ z ∈ˢ a ⟩ → Empty.⊥) × ⟨ pr a a ∈ˢ f ⟩ ) ∥₁

  -- The approximation entry: the whole tower story.
  Approx : V ℓ → V ℓ → Type (ℓ-suc ℓ)
  Approx _ f = pairhood f × singleValued f × zeroClause f
```

<!--en-->
## The object-language half
<!--zh-->
## 对象语言半边
<!--/-->

<!--en-->
Each clause gets an object-language formula, in de Bruijn shape with the
bounded quantifiers binding variable zero, so that a formula of arity two
speaks with the witness `f` at variable zero and the read member `x` at
variable one. The pair memberships `pr a b ∈ f` are written with the kit's
pair atom under a bounded existential, exactly the shape the shared decode
below reads.
<!--zh-->
每条子句都配一条对象语言公式，采用 de Bruijn 形状，有界量词绑定变量零，于是二元公式以见证 `f` 在变量零、被读成员 `x` 在变量一处说话。对隶属 `pr a b ∈ f` 用套件的对原子配一个有界存在写出，正是下面共享解码所读的形状。
<!--/-->

```agda
  private
    f0 : {n : ℕ} → Fin (suc n)
    f0 = zero

  pairForm : Formula ⟪ u ⟫ 2
  pairForm = ∀̇∈ (var zero)
              (∃̇ (∃̇ (PK.prAt (suc (suc zero)) (suc zero) zero)))

  singleForm : Formula ⟪ u ⟫ 2
  singleForm = ∀̇ (∀̇ (∀̇ (
      ∃̇∈ (var (suc (suc (suc zero))))
        (PK.prAt zero (suc (suc (suc zero))) (suc (suc zero)))
      ∧̇ ∃̇∈ (var (suc (suc (suc zero))))
        (PK.prAt zero (suc (suc (suc zero))) (suc zero))
      ⇒̇ var (suc zero) ≐ var zero
    )))

  zeroForm : Formula ⟪ u ⟫ 2
  zeroForm = ∃̇ ( (∀̇ (¬̇ (var zero ∈̇ var (suc zero))))
              ∧̇ (∃̇∈ (var (suc zero))
                   (PK.prAt zero (suc zero) (suc zero))) )

  -- The approximation, the Def-step (collapsed at a level) and the range
  -- read, at the object level.
  Ap : Formula ⟪ u ⟫ 2
  Ap = pairForm ∧̇ singleForm ∧̇ zeroForm

  Cl : Formula ⟪ u ⟫ 2
  Cl = ⊤̇

  Rg : Formula ⟪ u ⟫ 2
  Rg = ∃̇ ( ∃̇∈ (var (suc zero))
            (PK.prAt zero (suc zero) (suc (suc (suc zero)))) )
```

<!--en-->
## The decodes
<!--zh-->
## 解码
<!--/-->

<!--en-->
The approximation entry's adequacy is one two-way decode: a satisfied object
clause is the corresponding meta-level read, and conversely. The innermost
shape appears in every clause, so it is decoded once: `pair∈` says the
satisfaction of "the pair of the sets at `a` and `b` lies in the set at `k`"
is exactly the meta-level membership `pr a b ∈ k`, with the pair-atom decode
reading the satisfaction back to the equality and the carrier's transitivity
supplying the membership certificate on the way in.

Each clause then decodes by walking its quantifiers. The pattern is the
chapter's standing discipline: every truncated branch is a named `where`
function with a written type, so the inner satisfaction machinery elaborates
once per branch.
<!--zh-->
近似条目的充分性是一条双向解码：被满足的对象子句就是对应的元层读式，反之亦然。最内层的形状出现在每条子句里，于是只解码一次：`pair∈` 说「`a`、`b` 处的集合之对落在 `k` 处的集合里」这条公式的满足，恰是元层的隶属 `pr a b ∈ k`，进入方向由对原子解码读回等式，载体传递性供给隶属证书。

然后每条子句沿量词走一遍解码。模式是本章的一贯纪律：每个截断分支都是带书面类型的具名 `where` 函数，于是内层满足机器每个分支只展开一次。
<!--/-->

```agda
  pair∈ : {n : ℕ} (k a b : Fin n) (δ : Vec SM n)
        → ⟨ δ ⊨ᵐ (∃̇∈ (var k) (PK.prAt zero (suc a) (suc b))) ⟩
        ⟷ ⟨ pr (fst (lookup a δ)) (fst (lookup b δ)) ∈ˢ fst (lookup k δ) ⟩
  pair∈ k a b δ = pair∈-out , pair∈-in
    where
    pair∈-out : ⟨ δ ⊨ᵐ (∃̇∈ (var k) (PK.prAt zero (suc a) (suc b))) ⟩
              → ⟨ pr (fst (lookup a δ)) (fst (lookup b δ)) ∈ˢ fst (lookup k δ) ⟩
    pair∈-out = PT.rec (snd (pr (fst (lookup a δ)) (fst (lookup b δ))
                             ∈ˢ fst (lookup k δ))) go
      where
      go : Σ[ z ∈ SM ] (⟨ fst z ∈ˢ fst (lookup k δ) ⟩
                      × ⟨ (z ∷ δ) ⊨ᵐ PK.prAt zero (suc a) (suc b) ⟩)
         → ⟨ pr (fst (lookup a δ)) (fst (lookup b δ)) ∈ˢ fst (lookup k δ) ⟩
      go (z , (z∈k , p)) =
        subst (λ w → ⟨ w ∈ˢ fst (lookup k δ) ⟩)
          (PK.prAt-out zero (suc a) (suc b) (z ∷ δ) p) z∈k

    pair∈-in : ⟨ pr (fst (lookup a δ)) (fst (lookup b δ)) ∈ˢ fst (lookup k δ) ⟩
             → ⟨ δ ⊨ᵐ (∃̇∈ (var k) (PK.prAt zero (suc a) (suc b))) ⟩
    pair∈-in h = ∣ z , (h , PK.prAt-in zero (suc a) (suc b) (z ∷ δ) refl) ∣₁
      where
      z : SM
      z = PK.pt (pr (fst (lookup a δ)) (fst (lookup b δ)))
          (utr {x = fst (lookup k δ)}
               {y = pr (fst (lookup a δ)) (fst (lookup b δ))} h (snd (lookup k δ)))

  -- Pairhood: every member of f is a pair.
  pairhood-out : (f : SM) (x : ⟪ u ⟫)
               → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ pairForm ⟩ → pairhood (fst f)
  pairhood-out f x h z z∈f = PT.rec squash₁ step (h zm z∈f)
    where
    zm : SM
    zm = PK.pt z (utr {x = fst f} {y = z} z∈f (snd f))
    step : Σ[ a ∈ SM ]
             ⟨ (a ∷ zm ∷ f ∷ ι x ∷ [])
               ⊨ᵐ (∃̇ (PK.prAt (suc (suc zero)) (suc zero) zero)) ⟩
         → isPair z
    step (a , sa) = PT.rec squash₁ step₂ sa
      where
      step₂ : Σ[ b ∈ SM ]
                ⟨ (b ∷ a ∷ zm ∷ f ∷ ι x ∷ [])
                  ⊨ᵐ PK.prAt (suc (suc zero)) (suc zero) zero ⟩ → isPair z
      step₂ (b , p) = ∣ fst a , (fst b ,
        PK.prAt-out (suc (suc zero)) (suc zero) zero (b ∷ a ∷ zm ∷ f ∷ ι x ∷ []) p) ∣₁

  pairhood-in : (f : SM) (x : ⟪ u ⟫)
              → pairhood (fst f) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ pairForm ⟩
  pairhood-in f x ph ym y∈f = PT.rec squash₁ step (ph (fst ym) y∈f)
    where
    step : Σ[ a ∈ S ] Σ[ b ∈ S ] (fst ym ≡ pr a b)
         → ⟨ (ym ∷ f ∷ ι x ∷ [])
              ⊨ᵐ (∃̇ (∃̇ (PK.prAt (suc (suc zero)) (suc zero) zero))) ⟩
    step (a , (b , e)) = ∣ a-pt , (∣ b-pt , prAt-sat ∣₁) ∣₁
      where
      pr∈u : ⟨ pr a b ∈ˢ u ⟩
      pr∈u = utr {x = fst f} {y = pr a b}
        (subst (λ w → ⟨ w ∈ˢ fst f ⟩) e y∈f) (snd f)
      a∈u : ⟨ a ∈ˢ u ⟩
      a∈u = PM.pair-left {a = a} {b = b} pr∈u
      b∈u : ⟨ b ∈ˢ u ⟩
      b∈u = PM.pair-right {a = a} {b = b} pr∈u
      a-pt : SM
      a-pt = PK.pt a a∈u
      b-pt : SM
      b-pt = PK.pt b b∈u
      prAt-sat : ⟨ (b-pt ∷ a-pt ∷ ym ∷ f ∷ ι x ∷ [])
                   ⊨ᵐ PK.prAt (suc (suc zero)) (suc zero) zero ⟩
      prAt-sat = PK.prAt-in (suc (suc zero)) (suc zero) zero
                   (b-pt ∷ a-pt ∷ ym ∷ f ∷ ι x ∷ []) e

  -- Single-valuedness: equal first components force equal seconds.
  single-out : (f : SM) (x : ⟪ u ⟫)
             → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ singleForm ⟩ → singleValued (fst f)
  single-out f x h a b c ab∈f ac∈f =
    h (PK.pt a a∈u) (PK.pt b b∈u) (PK.pt c c∈u) (ab-sat , ac-sat)
    where
    a∈u : ⟨ a ∈ˢ u ⟩
    a∈u = PM.pair-left {a = a} {b = b}
      (utr {x = fst f} {y = pr a b} ab∈f (snd f))
    b∈u : ⟨ b ∈ˢ u ⟩
    b∈u = PM.pair-right {a = a} {b = b}
      (utr {x = fst f} {y = pr a b} ab∈f (snd f))
    c∈u : ⟨ c ∈ˢ u ⟩
    c∈u = PM.pair-right {a = a} {b = c}
      (utr {x = fst f} {y = pr a c} ac∈f (snd f))
    δ : Vec SM 5
    δ = PK.pt c c∈u ∷ PK.pt b b∈u ∷ PK.pt a a∈u ∷ f ∷ ι x ∷ []
    ab-sat : ⟨ δ ⊨ᵐ (∃̇∈ (var (suc (suc (suc zero))))
                      (PK.prAt zero (suc (suc (suc zero))) (suc (suc zero)))) ⟩
    ab-sat = pair∈ (suc (suc (suc zero))) (suc (suc zero)) (suc zero) δ .snd ab∈f
    ac-sat : ⟨ δ ⊨ᵐ (∃̇∈ (var (suc (suc (suc zero))))
                      (PK.prAt zero (suc (suc (suc zero))) (suc zero))) ⟩
    ac-sat = pair∈ (suc (suc (suc zero))) (suc (suc zero)) zero δ .snd ac∈f

  single-in : (f : SM) (x : ⟪ u ⟫)
            → singleValued (fst f) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ singleForm ⟩
  single-in f x sv am bm cm hₚ =
    sv (fst am) (fst bm) (fst cm)
      (pair∈ (suc (suc (suc zero))) (suc (suc zero)) (suc zero)
        (cm ∷ bm ∷ am ∷ f ∷ ι x ∷ []) .fst
        (hₚ .fst))
      (pair∈ (suc (suc (suc zero))) (suc (suc zero)) zero
        (cm ∷ bm ∷ am ∷ f ∷ ι x ∷ []) .fst
        (hₚ .snd))

  -- The zero clause: the witness maps the empty set to itself.
  zero-out : (f : SM) (x : ⟪ u ⟫)
           → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ zeroForm ⟩ → zeroClause (fst f)
  zero-out f x h = PT.rec squash₁ step h
    where
    step : Σ[ a ∈ SM ]
             ( ⟨ (a ∷ f ∷ ι x ∷ []) ⊨ᵐ (∀̇ (¬̇ (var zero ∈̇ var (suc zero)))) ⟩
             × ⟨ (a ∷ f ∷ ι x ∷ []) ⊨ᵐ (∃̇∈ (var (suc zero))
                                          (PK.prAt zero (suc zero) (suc zero))) ⟩ )
         → zeroClause (fst f)
    step (a , (emp , pr)) = ∣ fst a , (empt ,
      pair∈ (suc zero) zero zero (a ∷ f ∷ ι x ∷ []) .fst pr) ∣₁
      where
      empt : (z : S) → ⟨ z ∈ˢ fst a ⟩ → Empty.⊥
      empt z z∈a = emp (PK.pt z (utr {x = fst a} {y = z} z∈a (snd a))) z∈a

  zero-in : (f : SM) (x : ⟪ u ⟫)
          → zeroClause (fst f) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ zeroForm ⟩
  zero-in f x = PT.rec squash₁ step
    where
    step : Σ[ a ∈ S ]
             ( ((z : S) → ⟨ z ∈ˢ a ⟩ → Empty.⊥) × ⟨ pr a a ∈ˢ fst f ⟩ )
         → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ zeroForm ⟩
    step (a , (emp , aa∈f)) = ∣ a-pt , (∀-sat ,
      pair∈ (suc zero) zero zero (a-pt ∷ f ∷ ι x ∷ []) .snd aa∈f) ∣₁
      where
      a∈u : ⟨ a ∈ˢ u ⟩
      a∈u = PM.pair-left {a = a} {b = a}
        (utr {x = fst f} {y = pr a a} aa∈f (snd f))
      a-pt : SM
      a-pt = PK.pt a a∈u
      ∀-sat : ⟨ (a-pt ∷ f ∷ ι x ∷ []) ⊨ᵐ (∀̇ (¬̇ (var zero ∈̇ var (suc zero)))) ⟩
      ∀-sat zm z∈a = emp (fst zm) z∈a
```

<!--en-->
With the three decodes in hand, the approximation adequacy assembles them:
the satisfaction of `Ap` is the tower story, and the tower story builds the
satisfaction, conjunct by conjunct.
<!--zh-->
三条解码在手，近似充分性随即装配：`Ap` 的满足就是塔故事，塔故事也逐合取项建回满足。
<!--/-->

```agda
  -- The approximation adequacy, both directions, walking the three conjuncts.
  ap-out : (f : SM) (x : ⟪ u ⟫) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Ap ⟩
         → Approx u (fst f)
  ap-out f x (h₁ , (h₂ , h₃)) =
    ( pairhood-out f x h₁
    , ( single-out f x h₂ , zero-out f x h₃ ) )

  ap-in : (f : SM) (x : ⟪ u ⟫) → Approx u (fst f)
        → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Ap ⟩
  ap-in f x (h₁ , (h₂ , h₃)) =
    ( pairhood-in f x h₁
    , ( single-in f x h₂ , zero-in f x h₃ ) )

  a-ok : (f : SM) (x : ⟪ u ⟫)
       → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Ap ⟩ ⟷ Approx u (fst f)
  a-ok f x = ap-out f x , ap-in f x
```

<!--en-->
## The Def-step and the range
<!--zh-->
## Def 步与像
<!--/-->

<!--en-->
The Def-step clause is the successor clause of the tower story, and at a level
it collapses. The collapse theorem, that every member of a stage is definable
at a member of that stage, unfolds the union at the carrier once: a member of
`Lset α` sits in `𝒟ₒ (Lset δ)` for some `δ ∈ α`, the definable-power inverse
names a formula, and `Lset δ` itself belongs to the carrier by the tower's
entry lemma applied to the fact that every set is definable in itself. So the
clause `Cl = ⊤̇` decodes to the delivered Def-step read in the forward
direction, and the reverse direction is the truth clause itself.

The range read is the graph's second-component projection: `x` lies in the
range of `f` when some `a` has `pr a x` in `f`. The object clause is a bounded
existential over the members of `f` naming a pair whose second component is
`x`, and the decode is the pair membership lemma twice, once for the witness
in, once for the pairhood out.
<!--zh-->
Def 步子句就是塔故事的后继子句，而在层处它坍缩。坍缩定理，「层的每个成员都在该层的某成员处可定义」，把载体处的并展开一次：`Lset α` 的成员对某 `δ ∈ α` 落在 `𝒟ₒ (Lset δ)` 里，可定义幂的逆点名一条公式，而 `Lset δ` 自身经塔的进入引理施于「每个集合都在自身中可定义」而属于载体。于是子句 `Cl = ⊤̇` 在前进方向解码到已交付的 Def 步读式，反向就是真子句本身。

像的读式是图关系的第二分量投影：当某 `a` 使 `pr a x` 落在 `f` 里，`x` 就落在 `f` 的像中。对象子句是对 `f` 成员的有界存在，点名一个以 `x` 为第二分量的对，解码就是对隶属引理用两次，见证进入一次、成对性读出一次。
<!--/-->

```agda
  collapse : (g : S) → ⟨ g ∈ˢ u ⟩ → DefStep u g
  collapse g g∈u = PT.rec squash₁ step (Lset-out α g g∈u)
    where
    step : Σ[ δ ∈ S ] (⟨ δ ∈ˢ α ⟩ × ⟨ g ∈ˢ 𝒟ₒ (Lset δ) ⟩) → DefStep u g
    step (δ , (δ∈α , g∈𝒟ₒ)) = PT.rec squash₁ go (𝒟ₒ-inv (Lset δ) g g∈𝒟ₒ)
      where
      go : Σ[ φ ∈ Formula ⟪ Lset δ ⟫ 1 ] (DefOf.defSet (Lset δ) φ ≡ g)
         → DefStep u g
      go (φ , e) = ∣ Lset δ , (φ , (w∈u , e)) ∣₁
        where
        w∈u : ⟨ Lset δ ∈ˢ u ⟩
        w∈u = Lset-in α δ (Lset δ) δ∈α
          (𝒟ₒ-intro (Lset δ) (Lset δ)
            ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset δ) ∣₁)

  c-ok : (f : SM) (x : ⟪ u ⟫)
       → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Cl ⟩ ⟷ DefStep u (fst f)
  c-ok f x = (λ _ → collapse (fst f) (snd f)) , (λ _ → tt*)

  r-out : (f : SM) (x : ⟪ u ⟫) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Rg ⟩
        → (⟪ u ⟫↪ x) ∈ran fst f
  r-out f x h = PT.rec squash₁ step h
    where
    step : Σ[ a ∈ SM ]
             ⟨ (a ∷ f ∷ ι x ∷ []) ⊨ᵐ
               (∃̇∈ (var (suc zero))
                    (PK.prAt zero (suc zero) (suc (suc (suc zero))))) ⟩
         → (⟪ u ⟫↪ x) ∈ran fst f
    step (a , sa) = ∣ fst a ,
      pair∈ (suc zero) zero (suc (suc zero)) (a ∷ f ∷ ι x ∷ []) .fst sa ∣₁

  r-in : (f : SM) (x : ⟪ u ⟫) → (⟪ u ⟫↪ x) ∈ran fst f
       → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Rg ⟩
  r-in f x = PT.rec squash₁ step
    where
    step : Σ[ a ∈ S ] ⟨ pr a (⟪ u ⟫↪ x) ∈ˢ fst f ⟩
         → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Rg ⟩
    step (a , ax∈f) = ∣ am , pa-sat ∣₁
      where
      a∈u : ⟨ a ∈ˢ u ⟩
      a∈u = PM.pair-left {a = a} {b = ⟪ u ⟫↪ x}
        (utr {x = fst f} {y = pr a (⟪ u ⟫↪ x)} ax∈f (snd f))
      am : SM
      am = PK.pt a a∈u
      pa-sat : ⟨ (am ∷ f ∷ ι x ∷ []) ⊨ᵐ
                  (∃̇∈ (var (suc zero))
                       (PK.prAt zero (suc zero) (suc (suc (suc zero))))) ⟩
      pa-sat = pair∈ (suc zero) zero (suc (suc zero))
                 (am ∷ f ∷ ι x ∷ []) .snd ax∈f

  r-ok : (f : SM) (x : ⟪ u ⟫)
       → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Rg ⟩ ⟷ (⟪ u ⟫↪ x) ∈ran fst f
  r-ok f x = r-out f x , r-in f x
```

<!--en-->
## The read-off
<!--zh-->
## 读出
<!--/-->

<!--en-->
The four telescope entries are now filled at the real tower, and the face's
adequacy module assembles them into the level formula's two-way adequacy: a
member `m` of the level lies in the definable set carved by the formula exactly
when some initial segment of the tower, a member of the binding set, lies in
the carrier, approximates the tower, applies the definable step, and ranges
over `m`. `read-off` is the delivered object, the consumer's take-away, with
the carrier `u`, the binding set `K` and the level index `α` as parameters.
<!--zh-->
望远镜的四项如今在真实塔处填满，面孔的充分性模块把它们装配成层公式的双向充分性：层的成员 `m` 落在公式刻出的可定义集里，当且仅当某条塔的初始段，绑定集的成员，落在载体内、近似整座塔、施以可定义步并以 `m` 为像。`read-off` 就是交付对象，消费方的所得，以载体 `u`、绑定集 `K` 与层索引 `α` 为参数。
<!--/-->

```agda
  module F = Face u K Ap Cl Rg
  module A = F.Adequacy Approx a-ok c-ok r-ok

  -- The two-way adequacy at the real tower.
  read-off : (m : ⟪ u ⟫) → ⟨ ⟪ u ⟫↪ m ∈ˢ defSet F.σ ⟩ ⟷ A.Elem m
  read-off = A.face-iff
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The chapter delivers the wing's level formula at the real tower: the
approximation entry of the initial-segment face is now the tower story itself,
functionhood (pairhood and single-valuedness) and the zero clause, with the
Def-step collapse and the range read completing the four entries, and the
two-way adequacy `read-off` against the delivered `defSet` face. The shared
pair kit is consumed, not re-derived. What remains of the classical tower
story are the limit clause, the union condition at limit ordinals, and the
ordinal domain bound, measured here as the chapter's omitted pieces and priced
in the report; each needs machinery the cone has not yet stocked. The other
two consumers of the face, the bridge's `L-sigma` at a rud carrier and the
condensation crossing, reuse the shared kit and the instantiation recipe: the
carrier, the clause formulas, and the decode discipline, each at its own
tower. The orchestrator wires this chapter into `Everything`.
<!--zh-->
本章在真实塔处交付翼的层公式：初始段面孔的近似条目如今就是塔故事本身，函数性 (成对性与单值性) 与零子句，连同 Def 步坍缩与像的读式补全四项，以及对照已交付 `defSet` 面孔的双向充分性 `read-off`。共享的对套件被消费，而非重推。经典塔故事所余的两条子句，极限子句与序数定义域界，在此作为缺项被测度并在报告中定价；它们各需要锥体尚未备好的机器。面孔的另两个消费方，rud 载体上的桥 `L-sigma` 与凝聚跨越，复用共享套件与实例化配方：载体、子句公式与解码纪律，各在自己的塔处。编排者把本章接入 `Everything`。
<!--/-->

# The level sigma at a rud carrier

<!--en-->
The initial-segment chapter wrote the face once, generic in the carrier; the
level-formula chapter supplied the first instantiation, the wing's own `W2`,
at the real tower, and left the recipe: the carrier, the clause formulas, and
the decode discipline, each at its own tower. This chapter supplies the
second instantiation, the bridge's sigma at a rud carrier. The carrier is a
limit level `Jset α` of the rud tower, transitive by the rud tower's stage
theorem and closed under the sixteen rudimentary operations; the tower story
is the same three-clause sentence the level-formula chapter delivered,
functionhood (pairhood and single-valuedness) and the zero clause, written at
the meta level and again as object-language formulas. The clause that changes
is the Def-step: at a level it collapsed by the theorem that every member of a
stage is definable at a member of that stage, while at the rud carrier it
collapses by the definability chapter's Refine lemma, that under transitivity
every member of a set is definable there by the atom naming it, with the rud
tower's membership chain, every member of a limit level lies in a carrier
member, supplying the descent. The result is the level sigma, the
initial-segment formula at a rud carrier, with its two-way adequacy.

The two remaining clauses of the classical story, the limit clause and the
ordinal domain bound, are measured here as the omitted pieces and reported as
such, exactly as at the tower: each is about the tower story, not about the
carrier, so the tower chapter's measured prices carry over, and this chapter
stops at its line budget rather than pushing their decodes past it.
<!--zh-->
初始段章把面孔一次写成、以载体为参数；层公式章交付第一个实例化，即翼自己的 `W2`，落在真实塔上，并留下配方：载体、子句公式与解码纪律，各在自己的塔处。本章交付第二个实例化，即 rud 载体上的桥 sigma。载体是 rud 塔的极限层 `Jset α`，由 rud 塔的阶段定理保证传递、并对十六个初步函数运算封闭；塔故事就是层公式章交付的同一条三子句句子，函数性 (成对性与单值性) 与零子句，在元层写一遍，再写成对象语言公式。变了的那条子句是 Def 步：在层处它经「层的每个成员都在该层的某成员处可定义」这条定理坍缩；在 rud 载体处它经可定义性章的 Refine 引理坍缩，即传递性之下集合的每个成员都由点名它的原子公式在其上可定义，rud 塔的成员链，「极限层的每个成员都落在某个载体成员里」，供给这段下行。成果就是层 sigma，即 rud 载体处的初始段公式，连同它的双向充分性。

经典故事所余的两条子句，极限子句与序数定义域界，在此作为缺项被测度并照实报告，与塔处完全一致：它们各自关于塔故事本身，与载体无关，故塔章的实测价直接平移，而本章在行数预算处停下，不把它们的解码推过界线。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module L.Rud.LevelSigma {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; _∈̇_; _≐_; _∧̇_; _⇒̇_; ¬̇_; ⊤̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import V.Presentation {ℓ} using ( fiber )
open import L.Constructible {ℓ} using ( isTransV )
open import L.Definability {ℓ} using ( module DefOf )
open import L.PairAtoms {ℓ} using ( isPair; module PairMem; module PairKit )
open import L.InitialSegment {ℓ} using ( _⟷_; _∈ran_; DefStep; module Face )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit )
open import L.Rud.Step {ℓ} lem A using
  ( Sset; Sset-trans; Sset-out; Sset-suc; Sset-in; Jset; limit-succ-mem; step
  ; step-∈ )

import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit using ( tt* )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )
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
Everything below is relative to one rud carrier `u = Jset α` at a limit
`α`, with the carrier's transitivity, the rud tower's stage theorem, and its
binding set `K`, a member of the carrier. The story is the same conjunction
of three clauses the tower chapter read, each stated at the level of the
graph: the pairs `pr a b` lying in the witness `f`.

Functionhood splits in two. `pairhood` says every member of `f` is a
Kuratowski pair, the delivered predicate of the pair-atom chapter; it is the
spine of the story. `singleValued` says the function's value is unique: two
pairs with the same first component agree on the second.

The zero clause says the witness maps the empty set to itself. The empty set
is the set with no members, so the clause names a memberless `a` with
`pr a a` lying in `f`, avoiding any constant in the object language.
<!--zh-->
以下一切都相对于一个 rud 载体 `u = Jset α`，其中 `α` 是极限，载体的传递性就是 rud 塔的阶段定理，绑定集 `K` 是载体的一个成员。故事与塔章读到的同一条三子句合取，每条都跑在图关系上：落在见证 `f` 里的对 `pr a b`。

函数性一分为二。`pairhood` 说 `f` 的每个成员都是库拉托夫斯基对，这是对原子章已交付的谓词，也是故事的脊梁；`singleValued` 说函数的值唯一：首分量相同的两个对，第二分量一致。

零子句说见证把空集映到自身。空集就是没有成员的集合，于是子句点名某个无成员的 `a`，使 `pr a a` 落在 `f` 里，对象语言不必引入常量。
<!--/-->

```agda
-- The tower story at a rud carrier, at the level of the graph.
module LevelAt (α : S) (lim : ⟨ isLimit α ⟩) (K : ⟪ Jset α lim ⟫) where

  u : S
  u = Jset α lim

  utr : isTransV u
  utr = Sset-trans α

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

  -- The approximation, the Def-step (collapsed at a rud carrier) and the
  -- range read, at the object level.
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
  pairhood-out f x h z z∈f = PT.rec squash₁ uStep (h zm z∈f)
    where
    zm : SM
    zm = PK.pt z (utr {x = fst f} {y = z} z∈f (snd f))
    uStep : Σ[ a ∈ SM ]
             ⟨ (a ∷ zm ∷ f ∷ ι x ∷ [])
               ⊨ᵐ (∃̇ (PK.prAt (suc (suc zero)) (suc zero) zero)) ⟩
         → isPair z
    uStep (a , sa) = PT.rec squash₁ uStep₂ sa
      where
      uStep₂ : Σ[ b ∈ SM ]
                ⟨ (b ∷ a ∷ zm ∷ f ∷ ι x ∷ [])
                  ⊨ᵐ PK.prAt (suc (suc zero)) (suc zero) zero ⟩ → isPair z
      uStep₂ (b , p) = ∣ fst a , (fst b ,
        PK.prAt-out (suc (suc zero)) (suc zero) zero (b ∷ a ∷ zm ∷ f ∷ ι x ∷ []) p) ∣₁

  pairhood-in : (f : SM) (x : ⟪ u ⟫)
              → pairhood (fst f) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ pairForm ⟩
  pairhood-in f x ph ym y∈f = PT.rec squash₁ uStep (ph (fst ym) y∈f)
    where
    uStep : Σ[ a ∈ S ] Σ[ b ∈ S ] (fst ym ≡ pr a b)
         → ⟨ (ym ∷ f ∷ ι x ∷ [])
              ⊨ᵐ (∃̇ (∃̇ (PK.prAt (suc (suc zero)) (suc zero) zero))) ⟩
    uStep (a , (b , e)) = ∣ a-pt , (∣ b-pt , prAt-sat ∣₁) ∣₁
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
  zero-out f x h = PT.rec squash₁ uStep h
    where
    uStep : Σ[ a ∈ SM ]
             ( ⟨ (a ∷ f ∷ ι x ∷ []) ⊨ᵐ (∀̇ (¬̇ (var zero ∈̇ var (suc zero)))) ⟩
             × ⟨ (a ∷ f ∷ ι x ∷ []) ⊨ᵐ (∃̇∈ (var (suc zero))
                                          (PK.prAt zero (suc zero) (suc zero))) ⟩ )
         → zeroClause (fst f)
    uStep (a , (emp , pr)) = ∣ fst a , (empt ,
      pair∈ (suc zero) zero zero (a ∷ f ∷ ι x ∷ []) .fst pr) ∣₁
      where
      empt : (z : S) → ⟨ z ∈ˢ fst a ⟩ → Empty.⊥
      empt z z∈a = emp (PK.pt z (utr {x = fst a} {y = z} z∈a (snd a))) z∈a

  zero-in : (f : SM) (x : ⟪ u ⟫)
          → zeroClause (fst f) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ zeroForm ⟩
  zero-in f x = PT.rec squash₁ uStep
    where
    uStep : Σ[ a ∈ S ]
             ( ((z : S) → ⟨ z ∈ˢ a ⟩ → Empty.⊥) × ⟨ pr a a ∈ˢ fst f ⟩ )
         → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ zeroForm ⟩
    uStep (a , (emp , aa∈f)) = ∣ a-pt , (∀-sat ,
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
The Def-step clause is the successor clause of the tower story, and at a rud
carrier it collapses too. The collapse reads the union at the carrier once: a
member `g` of `Jset α` sits in `step (Sset δ)` for some `δ ∈ α`, hence in the
next level `w = Sset (sucV δ)`, and that next level still belongs to the
carrier because `α` is a limit. The definability chapter's Refine lemma then
names `g` at `w` by the atom "the variable is a member of `g`", and the
carrier's transitivity makes the atom carve out exactly `g`. So the clause
`Cl = ⊤̇` decodes to the delivered Def-step read in the forward direction, and
the reverse direction is the truth clause itself.

The range read is the graph's second-component projection: `x` lies in the
range of `f` when some `a` has `pr a x` in `f`. The object clause is a bounded
existential over the members of `f` naming a pair whose second component is
`x`, and the decode is the pair membership lemma twice, once for the witness
in, once for the pairhood out.
<!--zh-->
Def 步子句就是塔故事的后继子句，而在 rud 载体处它也坍缩。坍缩在载体处把并展开一次：`Jset α` 的成员 `g` 对某 `δ ∈ α` 落在 `step (Sset δ)` 里，从而落在下一层 `w = Sset (sucV δ)` 里，而这一层因 `α` 是极限仍属于载体。可定义性章的 Refine 引理随即在 `w` 处用原子公式「该变量属于 `g`」点名 `g`，载体的传递性使原子公式刻出的恰好是 `g`。于是子句 `Cl = ⊤̇` 在前进方向解码到已交付的 Def 步读式，反向就是真子句本身。

像的读式是图关系的第二分量投影：当某 `a` 使 `pr a x` 落在 `f` 里，`x` 就落在 `f` 的像中。对象子句是对 `f` 成员的有界存在，点名一个以 `x` 为第二分量的对，解码就是对隶属引理用两次，见证进入一次、成对性读出一次。
<!--/-->

```agda
  -- The Def-step collapses at the rud carrier: every member of a rud
  -- level is definable at a member of it.
  collapse : (g : S) → ⟨ g ∈ˢ u ⟩ → DefStep u g
  collapse g g∈u = PT.rec squash₁ uStep (Sset-out α g g∈u)
    where
    uStep : Σ[ δ ∈ S ] (⟨ δ ∈ˢ α ⟩ × ⟨ g ∈ˢ step (Sset δ) ⟩) → DefStep u g
    uStep (δ , δ∈α , g∈stepSδ) = ∣ w , (φ , (w∈u , defSet≡)) ∣₁
      where
      w : S
      w = Sset (sucV δ)
      w∈u : ⟨ w ∈ˢ u ⟩
      w∈u = Sset-in α (sucV δ) w (limit-succ-mem α δ lim δ∈α) (step-∈ w)
      g∈w : ⟨ g ∈ˢ w ⟩
      g∈w = subst (λ t → ⟨ g ∈ˢ t ⟩) (sym (Sset-suc δ)) g∈stepSδ
      wf : Σ[ m ∈ ⟪ w ⟫ ] (⟪ w ⟫↪ m ≡ g)
      wf = fiber w g∈w
      module R = DefOf.Refine w (Sset-trans (sucV δ))
      φ : Formula ⟪ w ⟫ 1
      φ = R.atom (wf .fst)
      defSet≡ : DefOf.defSet w φ ≡ g
      defSet≡ = R.defSet-atom≡ (wf .fst) ∙ wf .snd

  c-ok : (f : SM) (x : ⟪ u ⟫)
       → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Cl ⟩ ⟷ DefStep u (fst f)
  c-ok f x = (λ _ → collapse (fst f) (snd f)) , (λ _ → tt*)

  r-out : (f : SM) (x : ⟪ u ⟫) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Rg ⟩
        → (⟪ u ⟫↪ x) ∈ran fst f
  r-out f x h = PT.rec squash₁ uStep h
    where
    uStep : Σ[ a ∈ SM ]
             ⟨ (a ∷ f ∷ ι x ∷ []) ⊨ᵐ
               (∃̇∈ (var (suc zero))
                    (PK.prAt zero (suc zero) (suc (suc (suc zero))))) ⟩
         → (⟪ u ⟫↪ x) ∈ran fst f
    uStep (a , sa) = ∣ fst a ,
      pair∈ (suc zero) zero (suc (suc zero)) (a ∷ f ∷ ι x ∷ []) .fst sa ∣₁

  r-in : (f : SM) (x : ⟪ u ⟫) → (⟪ u ⟫↪ x) ∈ran fst f
       → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Rg ⟩
  r-in f x = PT.rec squash₁ uStep
    where
    uStep : Σ[ a ∈ S ] ⟨ pr a (⟪ u ⟫↪ x) ∈ˢ fst f ⟩
         → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Rg ⟩
    uStep (a , ax∈f) = ∣ am , pa-sat ∣₁
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
The four telescope entries are now filled at the rud carrier, and the face's
adequacy module assembles them into the level sigma's two-way adequacy: a
member `m` of the carrier lies in the definable set carved by the formula
exactly when some initial segment of the tower, a member of the binding set,
lies in the carrier, approximates the tower, applies the definable step, and
ranges over `m`. `read-off` is the delivered object, the consumer's take-away,
with the carrier `u`, the binding set `K` and the limit index `α` as
parameters.
<!--zh-->
望远镜的四项如今在 rud 载体处填满，面孔的充分性模块把它们装配成层 sigma 的双向充分性：载体的成员 `m` 落在公式刻出的可定义集里，当且仅当某条塔的初始段，绑定集的成员，落在载体内、近似整座塔、施以可定义步并以 `m` 为像。`read-off` 就是交付对象，消费方的所得，以载体 `u`、绑定集 `K` 与极限索引 `α` 为参数。
<!--/-->

```agda
  module F = Face u K Ap Cl Rg
  module A = F.Adequacy Approx a-ok c-ok r-ok

  -- The two-way adequacy at a rud carrier.
  read-off : (m : ⟪ u ⟫) → ⟨ ⟪ u ⟫↪ m ∈ˢ defSet F.σ ⟩ ⟷ A.Elem m
  read-off = A.face-iff
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The chapter delivers the bridge's sigma at a rud carrier: the approximation
entry of the initial-segment face is the tower story itself, functionhood
(pairhood and single-valuedness) and the zero clause, with the Def-step
collapse and the range read completing the four entries, and the two-way
adequacy `read-off` against the delivered `defSet` face. The shared pair kit
is consumed, not re-derived, and the Def-step collapse leans on the
definability chapter's Refine lemma rather than the tower's definable-power
descent. What remains of the classical tower story are the limit clause and
the ordinal domain bound, measured here as the chapter's omitted pieces and
priced in the report; each is about the tower story, not the carrier, so the
tower chapter's prices carry over. The face's third consumer, the
condensation crossing, reuses the same shared kit and the same recipe at its
own carrier. The orchestrator wires this chapter into `Everything`.
<!--zh-->
本章在 rud 载体处交付桥的 sigma：初始段面孔的近似条目如今就是塔故事本身，函数性 (成对性与单值性) 与零子句，连同 Def 步坍缩与像的读式补全四项，以及对照已交付 `defSet` 面孔的双向充分性 `read-off`。共享的对套件被消费，而非重推，Def 步坍缩倚靠可定义性章的 Refine 引理，而非塔的可定义幂下行。经典塔故事所余的两条子句，极限子句与序数定义域界，在此作为缺项被测度并在报告中定价；它们各关于塔故事本身，与载体无关，故塔章的价格直接平移。面孔的第三个消费方，凝聚跨越，在自己的载体处复用同一套共享套件与同一条配方。编排者把本章接入 `Everything`。
<!--/-->

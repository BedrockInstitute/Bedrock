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
  ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Coding {ℓ} using ( pr )
open import V.Presentation {ℓ} using ( fiber )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-elim; ∈sucV-inl )
open import L.Constructible {ℓ} using ( isTransV; IsOrd; isPropIsOrd )
open import L.Definability {ℓ} using ( module DefOf )
open import L.PairAtoms {ℓ} using ( isPair; module PairMem; module PairKit )
open import L.InitialSegment {ℓ} using ( _⟷_; _∈ran_; DefStep; module Face )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit )
open import L.Rud.Step {ℓ} lem A using
  ( Sset; Sset-trans; Sset-out; Sset-suc; Sset-in; Jset; limit-succ-mem; step
  ; step-∈ )

import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.Functions.Logic using ( ⇔toPath )
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

<!--en-->
## The strengthened story: the successor value and the domain bound
<!--zh-->
## 加锐的塔故事：后继值与定义域界
<!--/-->

<!--en-->
The three-clause story pins the graph's functionhood and its start, but not
its continuation: an honest-ish witness may map a successor numeral to an
arbitrary carrier member, so the range carve overshoots. The classical story
closes the gap with two more clauses. The successor-value clause says the
value at a successor is the set of definable subsets of the value at the
predecessor; at a rud carrier this reads as the carrier-internal powerset
relation, `b` lying in the graph at the successor exactly when `b` is the
carrier's own set of subsets of the predecessor's value, written with bounded
quantifiers. The strengthened domain bound says every first component lies
in the bound itself (at the first limit, in `ω`), not merely in the carrier.
Both are built here as meta-level clauses, object-language formulas and
two-way decodes. The domain bound is read per component: the totality
direction of the classical exactness is redundant for the family carve,
because the successor-value clause's own two-way shape forces the value
chain, so a segment's range is a set of stages regardless. The limit clause
stays omitted, since below the first limit there is no limit ordinal for it
to speak about. The strengthened bound's object-language form is a
consumer's choice: the bound is a member of the carrier only above the first
limit (the bound-nameability fact), so the chapter records the bound as a
parameter of the meta clause and discharges it wherever the carrier names it.
The re-assembly of the approximation entry (the five-clause `Ap` with its
adequacy) is the face-instantiation seam: every clause now has its formula
and its two-way decode, so the adequacy walks the delivered conjuncts
verbatim.
<!--zh-->
三子句故事钉死了图的函数性与起点，却没有钉死续行：一个近似诚实的见证可以把后继数码映到任意的载体成员，于是像的刻划会越界。经典故事用两条子句补上缺口。后继值子句说后继处的值是前驱值的可定义子集之集；在 rud 载体处这读作载体内幂集关系，`b` 恰好是载体自身的前驱值子集之集时，后继处的图才含有 `b`，用有界量词写出。加锐的定义域界说每个首分量都落在界本身里 (在第一个极限处即落在 `ω` 里)，而不只是落在载体里。两条都作为元层子句、对象语言公式与双向解码在此建造。定义域界按分量读出：经典精确性的完全方向对族刻划是多余的，因为后继值子句自身的双向形状已经逼出值链，故一段的范围无论如何都是若干阶段的集合。极限子句仍然缺位，因为第一个极限之下没有极限序数供它谈论。加锐界在对象语言里的形式由消费方选择：界只在第一个极限之上才是载体的成员 (界可命名事实)，故本章把界记为元层子句的参数，并在载体能命名它的地方兑付。近似条目的重新装配 (五合取 `Ap` 连同其充分性) 是面孔实例化的接缝：每条子句如今都有自己的公式与双向解码，故充分性逐字走过已交付的合取项。
<!--/-->

```agda
  _⊆_ : S → S → Type (ℓ-suc ℓ)
  u ⊆ v = (x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩

  ext-⊆ : {u v : S} → u ⊆ v → v ⊆ u → u ≡ v
  ext-⊆ sub sup = extensionalV (λ x → ⇔toPath (sub x) (sup x))

  -- b is exactly the carrier's set of subsets of c.
  powRel : S → S → Type (ℓ-suc ℓ)
  powRel c b = ( ⟨ b ∈ˢ u ⟩
               × ((z : S) → ⟨ z ∈ˢ b ⟩ → z ⊆ c)
               × ((z : S) → ⟨ z ∈ˢ u ⟩ → z ⊆ c → ⟨ z ∈ˢ b ⟩) )

  -- The successor-value clause: the graph's value at suc a is powRel of
  -- the value at a.
  succValClause : S → Type (ℓ-suc ℓ)
  succValClause f = (a c b : S) → ⟨ pr a c ∈ˢ f ⟩
    → (⟨ pr (sucV a) b ∈ˢ f ⟩ ⟷ powRel c b)

  -- The domain bound (per-component read): every first component of f is
  -- an ordinal of the carrier.
  ordDom : S → Type (ℓ-suc ℓ)
  ordDom f = (a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁ → (IsOrd a × ⟨ a ∈ˢ u ⟩)

  -- The strengthened bound: every first component lies in the bound β.
  strongDomOrd : S → S → Type (ℓ-suc ℓ)
  strongDomOrd β f = (a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁ → (IsOrd a × ⟨ a ∈ˢ β ⟩)

  -- The discharge: wherever every ordinal of the carrier lies in the bound.
  strong-discharge : (β : S) (f : S)
    → ((a : S) → IsOrd a → ⟨ a ∈ˢ u ⟩ → ⟨ a ∈ˢ β ⟩)
    → ordDom f → strongDomOrd β f
  strong-discharge β f dis ord a h =
    PT.rec (isProp× (isPropIsOrd a) (snd (a ∈ˢ β))) go h
    where
    go : Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ → IsOrd a × ⟨ a ∈ˢ β ⟩
    go (b , ab∈f) = ( ord-a .fst , dis a (ord-a .fst) (ord-a .snd) )
      where
      ord-a : IsOrd a × ⟨ a ∈ˢ u ⟩
      ord-a = ord a (∣ b , ab∈f ∣₁)

```

<!--en-->
Each new clause gets an object-language formula in the chapter's standing de
Bruijn shape. The successor of a set is not a term of the object language, so
the successor pair `pr (suc a) b` is read through a bounded atom `sucAt`: the
set at `k` is the successor of the set at `a` exactly when `a` lies in `k`,
`a` is a subset of `k`, and every member of `k` is a member of `a` or `a`
itself, all bounded. The internal powerset atom `powAt` reads "the set at `b`
is the carrier-internal powerset of the set at `c`": every member of `b` is a
subset of `c`, and every subset of `c` in the carrier lies in `b`. The
ordinal predicate `isOrdAt` and the domain formula `domForm` are the tower
chapter's pieces ported by carrier substitution, and the successor-value
clause `succValForm` assembles its three quantifiers around the two new atoms.
<!--zh-->
每条新子句都配一条对象语言公式，沿用本章一贯的 de Bruijn 形状。集合的后继不是对象语言的词项，故后继对 `pr (suc a) b` 经有界原子 `sucAt` 读出：`k` 处的集合是 `a` 处集合的后继，当且仅当 `a` 落在 `k` 里、`a` 是 `k` 的子集、且 `k` 的每个成员都是 `a` 的成员或 `a` 本身，全部有界。载体内幂集原子 `powAt` 读作「`b` 处的集合是 `c` 处集合的载体内幂集」：`b` 的每个成员都是 `c` 的子集，而载体中 `c` 的每个子集都落在 `b` 里。序数谓词 `isOrdAt` 与定义域公式 `domForm` 是塔章按载体替换搬来的件，后继值子句 `succValForm` 把三个量词绕两条新原子装配起来。
<!--/-->

```agda
  -- The successor atom's coverage body: a member of k is a member of a
  sucKcov : {n : ℕ} → Fin n → Fin n → Formula ⟪ u ⟫ (suc n)
  sucKcov k a = (var zero ∈̇ var (suc a)) ∨̇ (var zero ≐ var (suc a))

  -- The bounded successor atom: k = suc a.
  sucAt : {n : ℕ} → Fin n → Fin n → Formula ⟪ u ⟫ n
  sucAt k a =
    (var a ∈̇ var k)
    ∧̇ (∀̇∈ (var a) (var zero ∈̇ var (suc k)))
    ∧̇ (∀̇∈ (var k) (sucKcov k a))

  isOrdAt : {n : ℕ} → Fin n → Formula ⟪ u ⟫ n
  isOrdAt k = (∀̇∈ (var k) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc k)))))
           ∧̇ (∀̇∈ (var k) (∀̇∈ (var zero) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero))))))

  powAt : {n : ℕ} → Fin n → Fin n → Formula ⟪ u ⟫ n
  powAt b c = (∀̇∈ (var b) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc c)))))
           ∧̇ (∀̇ ( (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc c))))
                 ⇒̇ (var zero ∈̇ var (suc b)) ))

  domForm : Formula ⟪ u ⟫ 2
  domForm = ∀̇ ( (∃̇ (∃̇∈ (var (suc (suc zero)))
                      (PK.prAt zero (suc (suc zero)) (suc zero))))
             ⇒̇ isOrdAt zero )

  succPairAt : Formula ⟪ u ⟫ 6
  succPairAt = (sucAt zero (suc (suc (suc zero))))
             ∧̇ (∃̇∈ (var (suc (suc (suc (suc zero)))))
                    (PK.prAt zero (suc zero) (suc (suc zero))))

  succConc : Formula ⟪ u ⟫ 5
  succConc = (∃̇ succPairAt ⇒̇ (powAt zero (suc zero)))
          ∧̇ ((powAt zero (suc zero)) ⇒̇ ∃̇ succPairAt)

  succAnt : Formula ⟪ u ⟫ 5
  succAnt = ∃̇∈ (var (suc (suc (suc zero))))
               (PK.prAt zero (suc (suc (suc zero))) (suc (suc zero)))

  succBody : Formula ⟪ u ⟫ 5
  succBody = succAnt ⇒̇ succConc

  succValForm : Formula ⟪ u ⟫ 2
  succValForm = ∀̇ (∀̇ (∀̇ succBody))

```

<!--en-->
The two new atoms decode first, and everything else consumes them. `sucAt-ok`
reads the bounded successor atom back to successor equality: the forward
direction splits a member of `k` through the successor's case analysis, and
the reverse direction rebuilds the three conjuncts from the equality. `powAt-ok`
reads the internal-powerset atom back to `powRel`: the two bounded quantifiers
are exactly the relation's two inclusions, with the carrier's transitivity
supplying the certificates the inner quantifiers ask for. The successor-value
clause's decode then walks its three quantifiers: the pair memberships are the
shared `pair∈` read, the successor pair is read through `sucAt-ok`, and the
two directions of the clause's bi-implication are the two directions of
`powAt-ok`. The ordinal decode `isOrd-out`/`isOrd-in` is the tower chapter's
shared piece ported verbatim, and the domain decode `dom-out`/`dom-in` reads
the per-component bound, each truncated branch a named `where` function with a
written type. The successor-value clause's two-way decode is one lemma
`succVal-ok`, and the successor pair at the graph is decoded once by
`succPair-ok`, consumed by both directions.
<!--zh-->
两条新原子先解码，其余全部消费它们。`sucAt-ok` 把有界后继原子读回后继等式：前进方向沿后继的分情形装置拆开 `k` 的成员，反向从等式重建三条合取项。`powAt-ok` 把载体内幂集原子读回 `powRel`：两条有界量词恰是关系的两条包含，载体传递性供给内层量词索要的证书。后继值子句的解码随之走过它的三个量词：对隶属用共享的 `pair∈` 读式，后继对经 `sucAt-ok` 读出，子句双向蕴含的两头正是 `powAt-ok` 的两个方向。序数解码 `isOrd-out`/`isOrd-in` 是塔章的共享件逐字搬来，定义域解码 `dom-out`/`dom-in` 读出按分量的界，每条截断分支都是带书面类型的具名 `where` 函数。后继值子句的双向解码是一条引理 `succVal-ok`，图处的后继对由 `succPair-ok` 解码一次，两个方向都消费它。
<!--/-->

```agda
  -- The successor atom decodes to successor equality.
  sucAt-ok : {n : ℕ} (k a : Fin n) (δ : Vec SM n)
           → ⟨ δ ⊨ᵐ sucAt k a ⟩ ⟷ (fst (lookup k δ) ≡ sucV (fst (lookup a δ)))
  sucAt-ok k a δ = (out , bwd)
    where
    valK valA : S
    valK = fst (lookup k δ)
    valA = fst (lookup a δ)
    out : ⟨ δ ⊨ᵐ sucAt k a ⟩ → valK ≡ sucV valA
    out (k∈ , (A⊆K , Kcov)) = ext-⊆ K⊆suc suc⊆K
      where
      K⊆suc : valK ⊆ sucV valA
      K⊆suc z z∈K = PT.rec (snd (z ∈ˢ sucV valA)) go (Kcov zm z∈K)
        where
        zm : SM
        zm = PK.pt z (utr {x = valK} {y = z} z∈K (snd (lookup k δ)))
        go : (⟨ z ∈ˢ valA ⟩ ⊎ (z ≡ valA))
           → ⟨ z ∈ˢ sucV valA ⟩
        go (inl z∈A) = ∈sucV-inl {A = valA} {x = z} z∈A
        go (inr z≡A) = subst (λ w → ⟨ w ∈ˢ sucV valA ⟩) (sym z≡A) (self∈sucV valA)
      suc⊆K : sucV valA ⊆ valK
      suc⊆K z z∈suc = ∈sucV-elim (snd (z ∈ˢ valK)) z∈suc
        (λ z∈A → A⊆K (PK.pt z (utr {x = valA} {y = z} z∈A (snd (lookup a δ)))) z∈A)
        (λ z≡A → subst (λ w → ⟨ w ∈ˢ valK ⟩) (sym z≡A) k∈)
    bwd : valK ≡ sucV valA → ⟨ δ ⊨ᵐ sucAt k a ⟩
    bwd q = ( k∈q , (A⊆Kq , Kcovq) )
      where
      k∈q : ⟨ valA ∈ˢ valK ⟩
      k∈q = subst (λ w → ⟨ valA ∈ˢ w ⟩) (sym q) (self∈sucV valA)
      A⊆Kq : ⟨ δ ⊨ᵐ ∀̇∈ (var a) (var zero ∈̇ var (suc k)) ⟩
      A⊆Kq zm z∈A = subst (λ w → ⟨ fst zm ∈ˢ w ⟩) (sym q) (∈sucV-inl {A = valA} {x = fst zm} z∈A)
      Kcovq : ⟨ δ ⊨ᵐ ∀̇∈ (var k) (sucKcov k a) ⟩
      Kcovq zm z∈K = ∈sucV-elim (snd sat) z∈suc inA eqA
        where
        sat = (zm ∷ δ) ⊨ᵐ sucKcov k a
        z∈suc : ⟨ fst zm ∈ˢ sucV valA ⟩
        z∈suc = subst (λ w → ⟨ fst zm ∈ˢ w ⟩) q z∈K
        inA : ⟨ fst zm ∈ˢ valA ⟩ → ⟨ (zm ∷ δ) ⊨ᵐ sucKcov k a ⟩
        inA h = ∣ inl h ∣₁
        eqA : fst zm ≡ valA → ⟨ (zm ∷ δ) ⊨ᵐ sucKcov k a ⟩
        eqA e = ∣ inr e ∣₁

  -- The internal-powerset atom decodes to the powerset relation.
  powAt-ok : {n : ℕ} (b c : Fin n) (δ : Vec SM n)
           → ⟨ δ ⊨ᵐ powAt b c ⟩ ⟷ powRel (fst (lookup c δ)) (fst (lookup b δ))
  powAt-ok b c δ = (out , bwd)
    where
    B C : S
    B = fst (lookup b δ)
    C = fst (lookup c δ)
    out : ⟨ δ ⊨ᵐ powAt b c ⟩ → powRel C B
    out (subs , closed) = ( snd (lookup b δ)
                          , (λ z z∈B → z⊆C z z∈B)
                          , (λ z z∈u z⊆C → closed (PK.pt z z∈u) (λ w w∈z → z⊆C (fst w) w∈z)) )
      where
      z⊆C : (z : S) → ⟨ z ∈ˢ B ⟩ → z ⊆ C
      z⊆C z z∈B w w∈z = subs zm z∈B wm w∈z
        where
        zm : SM
        zm = PK.pt z (utr {x = B} {y = z} z∈B (snd (lookup b δ)))
        wm : SM
        wm = PK.pt w (utr {x = z} {y = w} w∈z (snd zm))
    bwd : powRel C B → ⟨ δ ⊨ᵐ powAt b c ⟩
    bwd (B∈u , memb , closed) = ( subs , closedSat )
      where
      subs : ⟨ δ ⊨ᵐ ∀̇∈ (var b) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc c)))) ⟩
      subs zm z∈B w w∈z = memb (fst zm) z∈B (fst w) w∈z
      closedSat : ⟨ δ ⊨ᵐ ∀̇ ( (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc c))))
                           ⇒̇ (var zero ∈̇ var (suc b)) ) ⟩
      closedSat zm z⊆C = closed (fst zm) (snd zm)
        (λ w w∈z → z⊆C (PK.pt w (utr {x = fst zm} {y = w} w∈z (snd zm))) w∈z)

  -- The successor pair at the graph decodes to the meta pair membership.
  succPair-ok : (f : SM) (x : ⟪ u ⟫) (am cm bm : SM)
    → ⟨ (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ ∃̇ succPairAt ⟩
    ⟷ ⟨ pr (sucV (fst am)) (fst bm) ∈ˢ fst f ⟩
  succPair-ok f x am cm bm = (out , bwd)
    where
    out : ⟨ (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ ∃̇ succPairAt ⟩
        → ⟨ pr (sucV (fst am)) (fst bm) ∈ˢ fst f ⟩
    out = PT.rec (snd (pr (sucV (fst am)) (fst bm) ∈ˢ fst f)) go
      where
      go : Σ[ xm ∈ SM ] ⟨ (xm ∷ bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ succPairAt ⟩
         → ⟨ pr (sucV (fst am)) (fst bm) ∈ˢ fst f ⟩
      go (xm , (suc-sat , p-sat)) =
        subst (λ w → ⟨ pr w (fst bm) ∈ˢ fst f ⟩)
          (sucAt-ok zero (suc (suc (suc zero)))
            (xm ∷ bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) .fst suc-sat)
          (pair∈ (suc (suc (suc (suc zero)))) zero (suc zero)
            (xm ∷ bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) .fst p-sat)
    bwd : ⟨ pr (sucV (fst am)) (fst bm) ∈ˢ fst f ⟩
        → ⟨ (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ ∃̇ succPairAt ⟩
    bwd ab∈f = ∣ xm , ( suc-sat , p-sat ) ∣₁
      where
      x∈u : ⟨ sucV (fst am) ∈ˢ u ⟩
      x∈u = PM.pair-left {a = sucV (fst am)} {b = fst bm}
        (utr {x = fst f} {y = pr (sucV (fst am)) (fst bm)} ab∈f (snd f))
      xm : SM
      xm = PK.pt (sucV (fst am)) x∈u
      suc-sat : ⟨ (xm ∷ bm ∷ cm ∷ am ∷ f ∷ ι x ∷ [])
                  ⊨ᵐ sucAt zero (suc (suc (suc zero))) ⟩
      suc-sat = sucAt-ok zero (suc (suc (suc zero)))
        (xm ∷ bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) .snd refl
      p-sat : ⟨ (xm ∷ bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ
                (∃̇∈ (var (suc (suc (suc (suc zero)))))
                     (PK.prAt zero (suc zero) (suc (suc zero)))) ⟩
      p-sat = pair∈ (suc (suc (suc (suc zero)))) zero (suc zero)
        (xm ∷ bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) .snd ab∈f

  -- The successor-value clause decodes both ways: a satisfied clause is
  -- the meta story, and the meta story builds the satisfaction.
  succVal-ok : (f : SM) (x : ⟪ u ⟫)
             → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ succValForm ⟩ ⟷ succValClause (fst f)
  succVal-ok f x = (out , bwd)
    where
    out : ⟨ (f ∷ ι x ∷ []) ⊨ᵐ succValForm ⟩ → succValClause (fst f)
    out h a c b ac∈f = (o1 , o2)
      where
      pr∈u : ⟨ pr a c ∈ˢ u ⟩
      pr∈u = utr {x = fst f} {y = pr a c} ac∈f (snd f)
      am cm : SM
      am = PK.pt a (PM.pair-left {a = a} {b = c} pr∈u)
      cm = PK.pt c (PM.pair-right {a = a} {b = c} pr∈u)
      ant : (bm : SM) → ⟨ (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ succAnt ⟩
      ant bm = pair∈ (suc (suc (suc zero))) (suc (suc zero)) (suc zero)
        (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) .snd ac∈f
      o1 : ⟨ pr (sucV a) b ∈ˢ fst f ⟩ → powRel c b
      o1 ab∈f = powAt-ok zero (suc zero)
          (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) .fst
        ((h am cm bm (ant bm)) .fst (succPair-ok f x am cm bm .snd ab∈f))
        where
        b∈u : ⟨ b ∈ˢ u ⟩
        b∈u = PM.pair-right {a = sucV a} {b = b}
          (utr {x = fst f} {y = pr (sucV a) b} ab∈f (snd f))
        bm : SM
        bm = PK.pt b b∈u
      o2 : powRel c b → ⟨ pr (sucV a) b ∈ˢ fst f ⟩
      o2 pb = succPair-ok f x am cm bm .fst pr-sat
        where
        bm : SM
        bm = PK.pt b (pb .fst)
        powAt-sat : ⟨ (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ powAt zero (suc zero) ⟩
        powAt-sat = powAt-ok zero (suc zero)
          (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) .snd pb
        pr-sat : ⟨ (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ ∃̇ succPairAt ⟩
        pr-sat = (h am cm bm (ant bm)) .snd powAt-sat
    bwd : succValClause (fst f) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ succValForm ⟩
    bwd sc am cm bm ant-sat = (d1 , d2)
      where
      ac∈f : ⟨ pr (fst am) (fst cm) ∈ˢ fst f ⟩
      ac∈f = pair∈ (suc (suc (suc zero))) (suc (suc zero)) (suc zero)
        (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) .fst ant-sat
      d1 : ⟨ (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ
             (∃̇ succPairAt ⇒̇ (powAt zero (suc zero))) ⟩
      d1 = PT.rec (snd ((bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ powAt zero (suc zero))) go
        where
        go : Σ[ xm ∈ SM ]
               ⟨ (xm ∷ bm ∷ cm ∷ am ∷ f ∷ ι x ∷ [])
                 ⊨ᵐ succPairAt ⟩
           → ⟨ (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ powAt zero (suc zero) ⟩
        go (xm , sat) =
          powAt-ok zero (suc zero) (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) .snd
            (sc (fst am) (fst cm) (fst bm) ac∈f .fst
              (succPair-ok f x am cm bm .fst (∣ xm , sat ∣₁)))
      d2 : ⟨ (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ
             ((powAt zero (suc zero)) ⇒̇ ∃̇ succPairAt) ⟩
      d2 powAt-sat = succPair-ok f x am cm bm .snd ab∈f
        where
        ab∈f : ⟨ pr (sucV (fst am)) (fst bm) ∈ˢ fst f ⟩
        ab∈f = sc (fst am) (fst cm) (fst bm) ac∈f .snd
          (powAt-ok zero (suc zero) (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) .fst powAt-sat)

  -- The ordinal predicate decodes to being an ordinal (the tower
  -- chapter's shared decode, ported by carrier substitution).
  isOrd-out : {n : ℕ} (k : Fin n) (δ : Vec SM n)
            → ⟨ δ ⊨ᵐ isOrdAt k ⟩ → IsOrd (fst (lookup k δ))
  isOrd-out k δ (h₁ , h₂) = (trans , memTr)
    where
    valA = fst (lookup k δ)
    trans : isTransV valA
    trans {x} {y} y∈x x∈A = h₁ xm x∈A ym y∈x
      where
      x∈u : ⟨ x ∈ˢ u ⟩
      x∈u = utr {x = valA} {y = x} x∈A (snd (lookup k δ))
      xm : SM
      xm = PK.pt x x∈u
      ym : SM
      ym = PK.pt y (utr {x = x} {y = y} y∈x x∈u)
    memTr : (x : S) → ⟨ x ∈ˢ valA ⟩ → isTransV x
    memTr x x∈A {y} {z} z∈y y∈x = h₂ xm x∈A ym y∈x zm z∈y
      where
      x∈u : ⟨ x ∈ˢ u ⟩
      x∈u = utr {x = valA} {y = x} x∈A (snd (lookup k δ))
      xm : SM
      xm = PK.pt x x∈u
      y∈u : ⟨ y ∈ˢ u ⟩
      y∈u = utr {x = x} {y = y} y∈x x∈u
      ym : SM
      ym = PK.pt y (utr {x = x} {y = y} y∈x x∈u)
      zm : SM
      zm = PK.pt z (utr {x = y} {y = z} z∈y y∈u)

  isOrd-in : {n : ℕ} (k : Fin n) (δ : Vec SM n) → IsOrd (fst (lookup k δ))
           → ⟨ δ ⊨ᵐ isOrdAt k ⟩
  isOrd-in k δ (Atr , Amem) = (c1 , c2)
    where
    c1 : ⟨ δ ⊨ᵐ ∀̇∈ (var k) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc k)))) ⟩
    c1 xm x∈A ym y∈x = Atr {x = fst xm} {y = fst ym} y∈x x∈A
    c2 : ⟨ δ ⊨ᵐ
           ∀̇∈ (var k) (∀̇∈ (var zero) (∀̇∈ (var zero)
             (var zero ∈̇ var (suc (suc zero))))) ⟩
    c2 xm x∈A ym y∈x zm z∈y =
      Amem (fst xm) x∈A {x = fst ym} {y = fst zm} z∈y y∈x

  -- The domain bound decodes to the per-component read.
  dom-out : (f : SM) (x : ⟪ u ⟫) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ domForm ⟩ → ordDom (fst f)
  dom-out f x h a = PT.rec (isProp× (isPropIsOrd a) (snd (a ∈ˢ u))) go
    where
    go : Σ[ b ∈ S ] ⟨ pr a b ∈ˢ fst f ⟩ → IsOrd a × ⟨ a ∈ˢ u ⟩
    go (b , ab∈f) = ( isOrd-out zero (am ∷ f ∷ ι x ∷ []) sat-ord , a∈u )
      where
      pr∈u : ⟨ pr a b ∈ˢ u ⟩
      pr∈u = utr {x = fst f} {y = pr a b} ab∈f (snd f)
      a∈u : ⟨ a ∈ˢ u ⟩
      a∈u = PM.pair-left {a = a} {b = b} pr∈u
      b∈u : ⟨ b ∈ˢ u ⟩
      b∈u = PM.pair-right {a = a} {b = b} pr∈u
      am bm : SM
      am = PK.pt a a∈u
      bm = PK.pt b b∈u
      sat : ⟨ (bm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ
              (∃̇∈ (var (suc (suc zero)))
                   (PK.prAt zero (suc (suc zero)) (suc zero))) ⟩
      sat = pair∈ (suc (suc zero)) (suc zero) zero
        (bm ∷ am ∷ f ∷ ι x ∷ []) .snd ab∈f
      sat-ord : ⟨ (am ∷ f ∷ ι x ∷ []) ⊨ᵐ isOrdAt zero ⟩
      sat-ord = h am (∣ bm , sat ∣₁)

  dom-in : (f : SM) (x : ⟪ u ⟫) → ordDom (fst f) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ domForm ⟩
  dom-in f x ord am = PT.rec (snd ((am ∷ f ∷ ι x ∷ []) ⊨ᵐ isOrdAt zero)) go
    where
    go : Σ[ bm ∈ SM ]
           ⟨ (bm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ
             (∃̇∈ (var (suc (suc zero)))
                  (PK.prAt zero (suc (suc zero)) (suc zero))) ⟩
       → ⟨ (am ∷ f ∷ ι x ∷ []) ⊨ᵐ isOrdAt zero ⟩
    go (bm , sat) = isOrd-in zero (am ∷ f ∷ ι x ∷ [])
      (ord (fst am) (∣ fst bm ,
        pair∈ (suc (suc zero)) (suc zero) zero
          (bm ∷ am ∷ f ∷ ι x ∷ []) .fst sat ∣₁) .fst)

```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The strengthened story at a rud carrier now carries the successor-value
clause and the strengthened domain bound: the two new atoms `sucAt` and
`powAt` are decoded once each, the successor-value clause is decoded both
ways by `succVal-ok` with the successor pair read by `succPair-ok`, and the
domain bound is read per component, with the strengthened bound stated on it
and discharged wherever the carrier names the bound. The limit clause stays
omitted, vacuous below the first limit. The face's approximation entry
re-assembles over the delivered clause decodes; the carve's remaining steps
are the over-HF identification of the carrier-internal powerset with the
definable power and the family equality itself.
<!--zh-->
rud 载体处的加锐故事如今带有后继值子句与加锐的定义域界：两条新原子 `sucAt` 与 `powAt` 各解码一次，后继值子句由 `succVal-ok` 双向解码、后继对由 `succPair-ok` 读出，定义域界按分量读出，加锐界立在它上面，并在载体能命名界的地方兑付。极限子句仍然缺位，第一个极限之下它是空的。面孔的近似条目在已交付的子句解码之上重新装配；族刻划所余的步骤是「载体内幂集与可定义幂在 HF 上相合」的认同，以及族等式本身。
<!--/-->

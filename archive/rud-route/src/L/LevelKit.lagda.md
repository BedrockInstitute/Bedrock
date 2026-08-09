# The level-story clause kit

<!--en-->
The tower story is the conjunction of clauses a witness `f` must satisfy to be
an initial segment of the constructible tower, and it is written the same way
at every carrier: functionhood (pairhood and single-valuedness), the zero
clause, the ordinal domain bound and the range read all speak only about the
pairs `pr a b` lying in the graph, the carrier's transitivity and the inner
semantics, so none of them mentions which tower the carrier belongs to. This
chapter hosts that shared content once, at a generic transitive carrier. The
carrier `u` and its transitivity `utr` are the kit's two parameters, the pair
atoms open at the carrier exactly as in the pair-atom chapter, and every
clause is written twice, once at the meta level over the graph and once as an
object-language formula, with the two-way decodes that make the object
sentence mean the story. The bounded successor atom joins the kit as
carrier-generic ordinal content, the one-way successor clause is delivered
once, parameterized by its conclusion atom, and the story assembly builds the
tower story's conjunction once over a consumer's clause list. The consumers,
the level-formula chapter at the real tower, the level-sigma chapter at a rud
carrier, the S-story chapter at the step equality and the below-lim chapter,
each keep only their carrier-specific clauses and collapses, and instantiate
the kit at their carriers.
<!--zh-->
塔故事是见证 `f` 为可构造塔初始段所须满足的子句合取，而在每个载体处都以同一方式写出：函数性 (成对性与单值性)、零子句、序数定义域界与像的读式都只谈论落在图关系里的对 `pr a b`、载体的传递性与内层语义，于是没有一条提及载体属于哪座塔。本章把这些共享内容一次写成，落在通用的传递载体处。载体 `u` 与其传递性 `utr` 是套件的两个参数，对原子在载体处打开，与对原子章完全一致；每条子句写两遍，一遍在元层跑在图关系上，一遍是对象语言公式，并配使对象句子意指这个故事的双向解码。有界后继原子作为载体泛型的序数内容加入套件，单向后继值子句以结论原子为参数一次交付，故事装配在消费方的子句表上把塔故事的合取一次建成。消费方，真实塔上的层公式章、rud 载体上的层 sigma 章、步等式处的 S-故事章与 below-lim 章，各自只保留载体专属的子句与坍缩，并在自己的载体处实例化本套件。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.LevelKit {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( isTransV; IsOrd )
open import L.Definability {ℓ} using ( module DefOf )
open import L.PairAtoms {ℓ} using ( isPair; module PairMem; module PairKit )
open import L.InitialSegment {ℓ} using ( _⟷_; _∈ran_ )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-elim; ∈sucV-inl )

import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )
import Cubical.Data.List as List
import Cubical.Data.Unit as Unit
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The meta-level clauses
<!--zh-->
## 元层子句
<!--/-->

<!--en-->
Everything below is relative to one transitive carrier `u` and its witness
`f`, a member of the carrier's inner world. Functionhood splits in two.
`pairhood` says every member of `f` is a Kuratowski pair, the delivered
predicate of the pair-atom chapter; it is the spine of the story.
`singleValued` says the function's value is unique: two pairs with the same
first component agree on the second.

The zero clause says the witness maps the empty set to itself. The empty set
is the set with no members, so the clause names a memberless `a` with
`pr a a` lying in `f`, avoiding any constant in the object language.

The exact domain bound says the first components of `f` are exactly the
members of some ordinal `δ` in the carrier: some `δ` in `u` is an ordinal,
and `a` lies in `δ` exactly when some pair `pr a b` lies in `f`, the graph's
first-component projection read both ways. This is the exactness shape the
classical story reads as the domain of the function.
<!--zh-->
以下一切都相对于一个传递载体 `u` 及其见证 `f`，即载体内层世界的一个成员。函数性一分为二。`pairhood` 说 `f` 的每个成员都是库拉托夫斯基对，这是对原子章已交付的谓词，也是故事的脊梁；`singleValued` 说函数的值唯一：首分量相同的两个对，第二分量一致。

零子句说见证把空集映到自身。空集就是没有成员的集合，于是子句点名某个无成员的 `a`，使 `pr a a` 落在 `f` 里，对象语言不必引入常量。

精确定义域界说 `f` 的首分量恰是载体中某个序数 `δ` 的成员：`u` 中的某个 `δ` 是序数，且 `a` 落在 `δ` 里当且仅当某个对 `pr a b` 落在 `f` 里，即图的第一分量投影两头都读。这正是经典故事读作函数定义域的精确性形状。
<!--/-->

```agda
-- The clause kit at a transitive carrier: the shared tower-story clauses
-- and their two-way decodes, written once.
module LevelKit (u : V ℓ) (utr : isTransV u) where

  module U = DefOf u
  open U using ( SM; ι; _⊨ᵐ_; defSet ) public
  module PK = PairKit u utr
  module PM = PairMem u utr

  -- Pairhood: every member of f is a Kuratowski pair.
  pairhood : S → Type (ℓ-suc ℓ)
  pairhood f = (z : S) → ⟨ z ∈ˢ f ⟩ → isPair z

  -- Single-valuedness: equal first components force equal seconds.
  singleValued : S → Type (ℓ-suc ℓ)
  singleValued f = (a b c : S) → ⟨ pr a b ∈ˢ f ⟩ → ⟨ pr a c ∈ˢ f ⟩ → b ≡ c

  -- The zero clause: some memberless a has pr a a in f.
  zeroClause : S → Type (ℓ-suc ℓ)
  zeroClause f = ∥ Σ[ a ∈ S ]
    ( ((z : S) → ⟨ z ∈ˢ a ⟩ → Empty.⊥) × ⟨ pr a a ∈ˢ f ⟩ ) ∥₁

  -- The exact domain bound: the first components of f are exactly the
  -- members of some ordinal δ in the carrier.
  exactDom : S → Type (ℓ-suc ℓ)
  exactDom f = ∥ Σ[ δ ∈ S ] ( ⟨ δ ∈ˢ u ⟩ × IsOrd δ
    × ((a : S) → ⟨ a ∈ˢ δ ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁)
    × ((a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁ → ⟨ a ∈ˢ δ ⟩) ) ∥₁
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
below reads. The ordinal predicate `isOrdAt k` is the delivered bounded
formula, transitive with transitive members, parameterized by the index of
the candidate. The exact domain formula `exactDomForm` exists an ordinal `δ`
and reads the exactness both ways through the two named inclusions: a member
of `δ` has a pair in `f`, and a pair in `f` forces its first component into
`δ`. The Def-step clause `Cl` is the truth clause, collapsed at every
carrier, and the range read `Rg` is the graph's second-component projection.
<!--zh-->
每条子句都配一条对象语言公式，采用 de Bruijn 形状，有界量词绑定变量零，于是二元公式以见证 `f` 在变量零、被读成员 `x` 在变量一处说话。对隶属 `pr a b ∈ f` 用套件的对原子配一个有界存在写出，正是下面共享解码所读的形状。序数谓词 `isOrdAt k` 就是已交付的有界公式，传递且成员皆传递，以候选的下标为参数。精确定义域公式 `exactDomForm` 存在一个序数 `δ`，并经两条具名包含把精确性两头读出：`δ` 的成员在 `f` 里有对，而 `f` 里的对逼其首分量进入 `δ`。Def 步子句 `Cl` 是真子句，在每个载体处坍缩；像的读式 `Rg` 是图的第二分量投影。
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

  -- The ordinal predicate at a variable: transitive, with transitive
  -- members, bounded throughout.
  isOrdAt : {n : ℕ} → Fin n → Formula ⟪ u ⟫ n
  isOrdAt k =
    (∀̇∈ (var k) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc k)))))
    ∧̇
    (∀̇∈ (var k) (∀̇∈ (var zero) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero))))))

  -- The pair membership inside the exactness inclusions, at the arity-5
  -- environment (b, a, δ, f, x): the pair pr a b lies in the bound member.
  prInForm : Formula ⟪ u ⟫ 5
  prInForm = ∃̇∈ (var (suc (suc (suc zero))))
              (PK.prAt zero (suc (suc zero)) (suc zero))

  -- The totality inclusion: a ∈ δ ⇒ some pair pr a b lies in f.
  domInForm : Formula ⟪ u ⟫ 3
  domInForm = ∀̇ ((var zero ∈̇ var (suc zero)) ⇒̇ ∃̇ prInForm)

  -- The converse inclusion: a pair pr a b in f forces a ∈ δ.
  domOutForm : Formula ⟪ u ⟫ 3
  domOutForm = ∀̇ (∃̇ prInForm ⇒̇ (var zero ∈̇ var (suc zero)))

  -- The exact domain formula: some ordinal δ has exactly the first
  -- components of f as its members, both directions.
  exactDomForm : Formula ⟪ u ⟫ 2
  exactDomForm = ∃̇ (isOrdAt zero ∧̇ domInForm ∧̇ domOutForm)

  -- The Def-step clause (collapsed at a carrier) and the range read.
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
Each clause's adequacy is a two-way decode: a satisfied object clause is the
corresponding meta-level read, and conversely. The innermost shape appears in
every clause, so it is decoded once: `pair∈` says the satisfaction of "the
pair of the sets at `a` and `b` lies in the set at `k`" is exactly the
meta-level membership `pr a b ∈ k`, with the pair-atom decode reading the
satisfaction back to the equality and the carrier's transitivity supplying
the membership certificate on the way in.

Each clause then decodes by walking its quantifiers. The pattern is the
chapter's standing discipline: every truncated branch is a named `where`
function with a written type, so the inner satisfaction machinery elaborates
once per branch. The ordinal decode `isOrd-out`/`isOrd-in` reads the bounded
transitivity clauses back to `IsOrd`, and the carrier's transitivity supplies
the certificates the inner quantifiers ask for; it is the shared piece,
consumed both by the exact domain bound and by the limit premise of the
tower chapter's limit clause. The exactness decode `exactDom-out`/`exactDom-in`
walks the two bounded quantifiers of the domain clause, and the range decode
`r-out`/`r-in` is the pair membership lemma twice, once for the witness in,
once for the pairhood out.
<!--zh-->
每条子句的充分性都是一条双向解码：被满足的对象子句就是对应的元层读式，反之亦然。最内层的形状出现在每条子句里，于是只解码一次：`pair∈` 说「`a`、`b` 处的集合之对落在 `k` 处的集合里」这条公式的满足，恰是元层的隶属 `pr a b ∈ k`，进入方向由对原子解码读回等式，载体传递性供给隶属证书。

然后每条子句沿量词走一遍解码。模式是本章的一贯纪律：每个截断分支都是带书面类型的具名 `where` 函数，于是内层满足机器每个分支只展开一次。序数解码 `isOrd-out`/`isOrd-in` 把两条有界传递子句读回 `IsOrd`，载体传递性供给内层量词索要的证书；它是共享件，精确定义域界与塔章极限子句的极限前提各用一次。精确性解码 `exactDom-out`/`exactDom-in` 走过定义域子句的两个有界量词，像的解码 `r-out`/`r-in` 是对隶属引理用两次，见证进入一次、成对性读出一次。
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

  -- The ordinal predicate: satisfaction is being an ordinal.
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

  -- The exact domain bound: satisfaction is the exactness decode.
  exactDom-out : (f : SM) (x : ⟪ u ⟫)
               → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ exactDomForm ⟩ → exactDom (fst f)
  exactDom-out f x h = PT.rec squash₁ step h
    where
    step : Σ[ δm ∈ SM ]
             ⟨ (δm ∷ f ∷ ι x ∷ []) ⊨ᵐ (isOrdAt zero ∧̇ domInForm ∧̇ domOutForm) ⟩
         → exactDom (fst f)
    step (δm , (ord , (in-sat , out-sat))) =
      ∣ fst δm , (snd δm , isOrd-out zero (δm ∷ f ∷ ι x ∷ []) ord
        , in-part , out-part) ∣₁
      where
      in-part : (a : S) → ⟨ a ∈ˢ fst δm ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ fst f ⟩ ∥₁
      in-part a a∈δ = PT.rec squash₁ go (in-sat am a∈δ)
        where
        am : SM
        am = PK.pt a (utr {x = fst δm} {y = a} a∈δ (snd δm))
        go : Σ[ bm ∈ SM ] ⟨ (bm ∷ am ∷ δm ∷ f ∷ ι x ∷ []) ⊨ᵐ prInForm ⟩
           → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ fst f ⟩ ∥₁
        go (bm , sat) = ∣ fst bm ,
          pair∈ (suc (suc (suc zero))) (suc zero) zero
            (bm ∷ am ∷ δm ∷ f ∷ ι x ∷ []) .fst sat ∣₁
      out-part : (a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ fst f ⟩ ∥₁ → ⟨ a ∈ˢ fst δm ⟩
      out-part a = PT.rec (snd (a ∈ˢ fst δm)) go
        where
        go : Σ[ b ∈ S ] ⟨ pr a b ∈ˢ fst f ⟩ → ⟨ a ∈ˢ fst δm ⟩
        go (b , ab∈f) = out-sat am (∣ bm , sat ∣₁)
          where
          pr∈u : ⟨ pr a b ∈ˢ u ⟩
          pr∈u = utr {x = fst f} {y = pr a b} ab∈f (snd f)
          am : SM
          am = PK.pt a (PM.pair-left {a = a} {b = b} pr∈u)
          bm : SM
          bm = PK.pt b (PM.pair-right {a = a} {b = b} pr∈u)
          sat : ⟨ (bm ∷ am ∷ δm ∷ f ∷ ι x ∷ []) ⊨ᵐ prInForm ⟩
          sat = pair∈ (suc (suc (suc zero))) (suc zero) zero
                  (bm ∷ am ∷ δm ∷ f ∷ ι x ∷ []) .snd ab∈f

  exactDom-in : (f : SM) (x : ⟪ u ⟫) → exactDom (fst f)
              → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ exactDomForm ⟩
  exactDom-in f x = PT.rec squash₁ step
    where
    step : Σ[ δ ∈ S ] ( ⟨ δ ∈ˢ u ⟩ × IsOrd δ
             × ((a : S) → ⟨ a ∈ˢ δ ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ fst f ⟩ ∥₁)
             × ((a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ fst f ⟩ ∥₁ → ⟨ a ∈ˢ δ ⟩) )
         → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ exactDomForm ⟩
    step (δ , (δ∈u , ordδ , inM , outM)) =
      ∣ δm , (isOrd-in zero (δm ∷ f ∷ ι x ∷ []) ordδ , (in-sat , out-sat)) ∣₁
      where
      δm : SM
      δm = PK.pt δ δ∈u
      in-sat : ⟨ (δm ∷ f ∷ ι x ∷ []) ⊨ᵐ domInForm ⟩
      in-sat am a∈δ = PT.rec squash₁ go (inM (fst am) a∈δ)
        where
        go : Σ[ b ∈ S ] ⟨ pr (fst am) b ∈ˢ fst f ⟩
           → ⟨ (am ∷ δm ∷ f ∷ ι x ∷ []) ⊨ᵐ ∃̇ prInForm ⟩
        go (b , ab∈f) = ∣ bm , sat ∣₁
          where
          pr∈u : ⟨ pr (fst am) b ∈ˢ u ⟩
          pr∈u = utr {x = fst f} {y = pr (fst am) b} ab∈f (snd f)
          bm : SM
          bm = PK.pt b (PM.pair-right {a = fst am} {b = b} pr∈u)
          sat : ⟨ (bm ∷ am ∷ δm ∷ f ∷ ι x ∷ []) ⊨ᵐ prInForm ⟩
          sat = pair∈ (suc (suc (suc zero))) (suc zero) zero
                  (bm ∷ am ∷ δm ∷ f ∷ ι x ∷ []) .snd ab∈f
      out-sat : ⟨ (δm ∷ f ∷ ι x ∷ []) ⊨ᵐ domOutForm ⟩
      out-sat am = PT.rec (snd (fst am ∈ˢ fst δm)) go
        where
        go : Σ[ bm ∈ SM ] ⟨ (bm ∷ am ∷ δm ∷ f ∷ ι x ∷ []) ⊨ᵐ prInForm ⟩
           → ⟨ fst am ∈ˢ fst δm ⟩
        go (bm , sat) = outM (fst am)
          ∣ fst bm ,
            pair∈ (suc (suc (suc zero))) (suc zero) zero
              (bm ∷ am ∷ δm ∷ f ∷ ι x ∷ []) .fst sat ∣₁

  -- The range read: satisfaction of Rg is the second-component projection.
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
## The bounded successor atom and the one-way successor clause
<!--zh-->
## 有界后继原子与单向后继值子句
<!--/-->

<!--en-->
The successor of a set is not a term of the object language. The successor
pair `pr (sucV a) b` is read through the bounded successor atom `sucAt`: the
set at `k` is the successor of the set at `a` exactly when `a` lies in `k`,
`a` is a subset of `k`, and every member of `k` is a member of `a` or `a`
itself, all bounded. Its decode `sucAt-ok` reads the atom back to successor
equality. The successor pair at the graph is decoded once by `succPair-ok`,
consumed by every clause that reads the pair.

The one-way successor clause says: `pr a c` lies in `f`, and `pr (sucV a) b`
lies in `f`, so the conclusion `concl b c` holds. The clause is the same at
every carrier; only the conclusion atom differs. The module `OneWaySucc`
takes the conclusion relation, its object formula and its two-way decode,
and delivers the clause, its formula and its decode once. The level-sigma
chapter instantiates it at the powerset atom; the S-story chapter
instantiates it at the step equality.
<!--zh-->
集合的后继不是对象语言的词项。后继对 `pr (sucV a) b` 经有界后继原子 `sucAt` 读出：`k` 处的集合是 `a` 处集合的后继，当且仅当 `a` 落在 `k` 里、`a` 是 `k` 的子集、且 `k` 的每个成员都是 `a` 的成员或 `a` 本身，全部有界。解码 `sucAt-ok` 把原子读回后继等式。图处的后继对由 `succPair-ok` 解码一次，读该对的每条子句都消费它。

单向后继值子句说：`pr a c` 落在 `f` 里，且 `pr (sucV a) b` 落在 `f` 里，则结论 `concl b c` 成立。子句在每个载体处相同；只有结论原子不同。模块 `OneWaySucc` 取结论关系、其对象公式及其双向解码，一次交付子句、公式与解码。层 sigma 章在幂集原子处实例化它；S-故事章在步等式处实例化它。
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

  private
    _⊆_ : S → S → Type (ℓ-suc ℓ)
    u ⊆ v = (x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩

    ext-⊆ : {u v : S} → u ⊆ v → v ⊆ u → u ≡ v
    ext-⊆ sub sup = extensionalV (λ x → ⇔toPath (sub x) (sup x))

  -- The bounded successor atom decodes to successor equality.
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
        go : (⟨ z ∈ˢ valA ⟩ ⊎ (z ≡ valA)) → ⟨ z ∈ˢ sucV valA ⟩
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

  -- The successor pair at the graph: pr (sucV a) b lies in f.
  succPairAt : Formula ⟪ u ⟫ 6
  succPairAt = (sucAt zero (suc (suc (suc zero))))
             ∧̇ (∃̇∈ (var (suc (suc (suc (suc zero)))))
                    (PK.prAt zero (suc zero) (suc (suc zero))))

  succPair-ok : (f : SM) (x : ⟪ u ⟫) (am cm bm : SM)
    → ⟨ (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ ∃̇ succPairAt ⟩
    ⟷ ⟨ pr (sucV (fst am)) (fst bm) ∈ˢ fst f ⟩
  succPair-ok f x am cm bm = (out , bwd)
    where
    out : ⟨ (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ ∃̇ succPairAt ⟩ → ⟨ pr (sucV (fst am)) (fst bm) ∈ˢ fst f ⟩
    out = PT.rec (snd (pr (sucV (fst am)) (fst bm) ∈ˢ fst f)) go
      where
      go : Σ[ xm ∈ SM ] ⟨ (xm ∷ bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ succPairAt ⟩ → ⟨ pr (sucV (fst am)) (fst bm) ∈ˢ fst f ⟩
      go (xm , (suc-sat , p-sat)) =
        subst (λ w → ⟨ pr w (fst bm) ∈ˢ fst f ⟩)
          (sucAt-ok zero (suc (suc (suc zero)))
            (xm ∷ bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) .fst suc-sat)
          (pair∈ (suc (suc (suc (suc zero)))) zero (suc zero)
            (xm ∷ bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) .fst p-sat)
    bwd : ⟨ pr (sucV (fst am)) (fst bm) ∈ˢ fst f ⟩ → ⟨ (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ ∃̇ succPairAt ⟩
    bwd ab∈f = ∣ xm , (suc-sat , p-sat) ∣₁
      where
      x∈u : ⟨ sucV (fst am) ∈ˢ u ⟩
      x∈u = PM.pair-left {a = sucV (fst am)} {b = fst bm}
        (utr {x = fst f} {y = pr (sucV (fst am)) (fst bm)} ab∈f (snd f))
      xm : SM
      xm = PK.pt (sucV (fst am)) x∈u
      suc-sat : ⟨ (xm ∷ bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ sucAt zero (suc (suc (suc zero))) ⟩
      suc-sat = sucAt-ok zero (suc (suc (suc zero))) (xm ∷ bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) .snd refl
      p-sat : ⟨ (xm ∷ bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ
                (∃̇∈ (var (suc (suc (suc (suc zero))))) (PK.prAt zero (suc zero) (suc (suc zero)))) ⟩
      p-sat = pair∈ (suc (suc (suc (suc zero)))) zero (suc zero) (xm ∷ bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) .snd ab∈f

  -- The antecedent: pr a c lies in f.
  succAnt : Formula ⟪ u ⟫ 5
  succAnt = ∃̇∈ (var (suc (suc (suc zero))))
               (PK.prAt zero (suc (suc (suc zero))) (suc (suc zero)))

  -- The one-way successor clause, parameterized by its conclusion atom.
  module OneWaySucc
    (concl : S → S → Type (ℓ-suc ℓ))
    (Concl : {n : ℕ} → Fin n → Fin n → Formula ⟪ u ⟫ n)
    (Concl-ok : {n : ℕ} (k c : Fin n) (δ : Vec SM n)
              → ⟨ δ ⊨ᵐ Concl k c ⟩ ⟷ concl (fst (lookup k δ)) (fst (lookup c δ)))
    where

    -- Values for present pairs only: pr a c and pr (sucV a) b lie in f,
    -- so the conclusion holds for b and c.
    succClause : S → Type (ℓ-suc ℓ)
    succClause f = (a c b : S) → ⟨ pr a c ∈ˢ f ⟩ → ⟨ pr (sucV a) b ∈ˢ f ⟩
                 → concl b c

    succConc : Formula ⟪ u ⟫ 5
    succConc = ∃̇ succPairAt ⇒̇ (Concl zero (suc zero))

    succBody : Formula ⟪ u ⟫ 5
    succBody = succAnt ⇒̇ succConc

    succForm : Formula ⟪ u ⟫ 2
    succForm = ∀̇ (∀̇ (∀̇ succBody))

    -- The one-way clause decodes both ways, walking the three quantifiers.
    succ-ok : (f : SM) (x : ⟪ u ⟫)
            → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ succForm ⟩ ⟷ succClause (fst f)
    succ-ok f x = (out , bwd)
      where
      out : ⟨ (f ∷ ι x ∷ []) ⊨ᵐ succForm ⟩ → succClause (fst f)
      out h a c b ac∈f ab∈f = Concl-ok zero (suc zero) (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) .fst
        ((h am cm bm (ant bm)) (succPair-ok f x am cm bm .snd ab∈f))
        where
        pr∈u : ⟨ pr a c ∈ˢ u ⟩
        pr∈u = utr {x = fst f} {y = pr a c} ac∈f (snd f)
        am cm : SM
        am = PK.pt a (PM.pair-left {a = a} {b = c} pr∈u)
        cm = PK.pt c (PM.pair-right {a = a} {b = c} pr∈u)
        ant : (bm : SM) → ⟨ (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ succAnt ⟩
        ant bm = pair∈ (suc (suc (suc zero))) (suc (suc zero)) (suc zero)
          (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) .snd ac∈f
        b∈u : ⟨ b ∈ˢ u ⟩
        b∈u = PM.pair-right {a = sucV a} {b = b}
          (utr {x = fst f} {y = pr (sucV a) b} ab∈f (snd f))
        bm : SM
        bm = PK.pt b b∈u
      bwd : succClause (fst f) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ succForm ⟩
      bwd sc am cm bm ant-sat = PT.rec
        (snd ((bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ Concl zero (suc zero))) go
        where
        ac∈f : ⟨ pr (fst am) (fst cm) ∈ˢ fst f ⟩
        ac∈f = pair∈ (suc (suc (suc zero))) (suc (suc zero)) (suc zero)
          (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) .fst ant-sat
        go : Σ[ xm ∈ SM ] ⟨ (xm ∷ bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ succPairAt ⟩
           → ⟨ (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ Concl zero (suc zero) ⟩
        go (xm , sat) = Concl-ok zero (suc zero) (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) .snd
          (sc (fst am) (fst cm) (fst bm) ac∈f
            (succPair-ok f x am cm bm .fst (∣ xm , sat ∣₁)))
```

<!--en-->
## The story assembly
<!--zh-->
## 故事装配
<!--/-->

<!--en-->
Every consumer assembles the same story: the meta-level conjunction, the
right-nested product of the clause predicates, the object conjunction, the
right-nested chain of the clause formulas, and the two-way decode that walks
the clause decodes in each direction. The assembly is the same at every
carrier, so the kit hosts it once, parameterized by the clause list. A story
clause record `StoryClause` carries the predicate, the object formula and the
two-way decode; `mkClause` builds one from the two directions, and `clauseOk`
builds one from a delivered `-ok` lemma. The clause list `StoryClauses` is a
`List` of the records, with the local operators `_∷₊_` and `end` for the
consumer's list. The fold `Conj` assembles the meta-level conjunction over a
predicate list, `ConjForm` assembles the object conjunction over the clause
list, and `conj-out` and `conj-in` walk the decodes in each direction. The
five names `storyCl`, `storyForm`, `story-out`, `story-in` and `story-ok`
deliver the assembled story at a consumer's clause list. A consumer supplies
clauses, not proofs.
<!--zh-->
每个消费方都装配同一条故事：元层合取，即子句谓词的右嵌套积；对象合取，即子句公式的右嵌套链；以及双向解码，沿每条子句解码各走一个方向。装配在每个载体处相同，于是套件把它一次写成，以子句表为参数。故事子句记录 `StoryClause` 携带谓词、对象公式与双向解码；`mkClause` 由两个方向构造一条，`clauseOk` 由一条已交付的 `-ok` 引理构造一条。子句表 `StoryClauses` 就是这些记录的 `List`，消费方的表用本地算子 `_∷₊_` 与 `end` 书写。折叠 `Conj` 在谓词表上装配元层合取，`ConjForm` 在子句表上装配对象合取，`conj-out` 与 `conj-in` 各沿一个方向走解码。五个名字 `storyCl`、`storyForm`、`story-out`、`story-in` 与 `story-ok` 在消费方的子句表处交付装配好的故事。消费方只供子句，不供证明。
<!--/-->

```agda
  -- One story clause: the predicate, the object formula and the two-way
  -- decode at the witness environment, as a right-nested pair.
  StoryClause : Type (ℓ-suc (ℓ-suc ℓ))
  StoryClause =
    Σ[ cl ∈ (S → Type (ℓ-suc ℓ)) ]
    Σ[ form ∈ Formula ⟪ u ⟫ 2 ]
    Σ[ out ∈ ((f : SM) (x : ⟪ u ⟫) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ form ⟩ → cl (fst f)) ]
    ((f : SM) (x : ⟪ u ⟫) → cl (fst f) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ form ⟩)

  -- One clause, from the two decode directions.
  mkClause : (cl : S → Type (ℓ-suc ℓ)) (form : Formula ⟪ u ⟫ 2)
           → ((f : SM) (x : ⟪ u ⟫) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ form ⟩ → cl (fst f))
           → ((f : SM) (x : ⟪ u ⟫) → cl (fst f) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ form ⟩)
           → StoryClause
  mkClause cl form out bwd = cl , (form , (out , bwd))

  -- A clause from a delivered two-way `-ok` lemma.
  clauseOk : (cl : S → Type (ℓ-suc ℓ)) (form : Formula ⟪ u ⟫ 2)
           → ((f : SM) (x : ⟪ u ⟫) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ form ⟩ ⟷ cl (fst f))
           → StoryClause
  clauseOk cl form ok = mkClause cl form (λ f x → ok f x .fst) (λ f x → ok f x .snd)

  -- The clause list at a consumer.
  StoryClauses : Type (ℓ-suc (ℓ-suc ℓ))
  StoryClauses = List.List StoryClause

  infixr 5 _∷₊_

  _∷₊_ : StoryClause → StoryClauses → StoryClauses
  c ∷₊ cs = c List.∷ cs

  end : StoryClauses
  end = List.[]

  -- The meta-level conjunction over a predicate list.
  Conj : List.List (S → Type (ℓ-suc ℓ)) → S → Type (ℓ-suc ℓ)
  Conj List.[] f = Unit.Unit*
  Conj (c List.∷ List.[]) f = c f
  Conj (c List.∷ cs) f = c f × Conj cs f

  -- The clause predicates of a clause list.
  clProject : StoryClauses → List.List (S → Type (ℓ-suc ℓ))
  clProject List.[] = List.[]
  clProject ((cl , _) List.∷ cs) = cl List.∷ clProject cs

  -- The object conjunction over the clause list.
  ConjForm : StoryClauses → Formula ⟪ u ⟫ 2
  ConjForm List.[] = ⊤̇
  ConjForm ((_ , (form , _)) List.∷ List.[]) = form
  ConjForm ((_ , (form , _)) List.∷ cs) = form ∧̇ ConjForm cs

  -- The decode walk, both directions.
  conj-out : (cs : StoryClauses) (f : SM) (x : ⟪ u ⟫)
           → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ ConjForm cs ⟩
           → Conj (clProject cs) (fst f)
  conj-out List.[] f x h = Unit.tt*
  conj-out ((_ , (_ , (out , _))) List.∷ List.[]) f x h = out f x h
  conj-out ((_ , (_ , (out , _))) List.∷ c' List.∷ cs) f x (h₁ , h₂) =
    out f x h₁ , conj-out (c' List.∷ cs) f x h₂

  conj-in : (cs : StoryClauses) (f : SM) (x : ⟪ u ⟫)
          → Conj (clProject cs) (fst f)
          → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ ConjForm cs ⟩
  conj-in List.[] f x h = Unit.tt*
  conj-in ((_ , (_ , (_ , bwd))) List.∷ List.[]) f x h = bwd f x h
  conj-in ((_ , (_ , (_ , bwd))) List.∷ c' List.∷ cs) f x (h₁ , h₂) =
    bwd f x h₁ , conj-in (c' List.∷ cs) f x h₂

  -- The assembled story at a consumer's clause list.
  storyCl : StoryClauses → S → Type (ℓ-suc ℓ)
  storyCl cs = Conj (clProject cs)

  storyForm : StoryClauses → Formula ⟪ u ⟫ 2
  storyForm = ConjForm

  story-out : (cs : StoryClauses) (f : SM) (x : ⟪ u ⟫)
            → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ storyForm cs ⟩ → storyCl cs (fst f)
  story-out cs = conj-out cs

  story-in : (cs : StoryClauses) (f : SM) (x : ⟪ u ⟫)
           → storyCl cs (fst f) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ storyForm cs ⟩
  story-in cs = conj-in cs

  story-ok : (cs : StoryClauses) (f : SM) (x : ⟪ u ⟫)
           → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ storyForm cs ⟩ ⟷ storyCl cs (fst f)
  story-ok cs f x = conj-out cs f x , conj-in cs f x
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The chapter delivers the shared clause kit at a generic transitive carrier:
the meta-level reads (pairhood, single-valuedness, the zero clause, the exact
domain bound), their object-language formulas, and the two-way decodes
(the innermost pair membership, the four clause decodes, the ordinal decode,
the exactness decode and the range read). Nothing here mentions which tower
the carrier belongs to: the kit consumes only the carrier's transitivity, the
pair-atom kit and the inner semantics. The bounded successor atom joins the
kit as carrier-generic ordinal content, and the one-way successor clause is
delivered once, parameterized by its conclusion atom; the level-sigma chapter
instantiates the clause at the powerset atom, and the S-story chapter at the
step equality. The consumers instantiate the kit at their own carrier and
keep their carrier-specific clauses and collapses: the level formula's limit
clause at the real tower, the level sigma's strengthened successor story and
per-component bound at a rud carrier, and each consumer's own Def-step
collapse and adequacy assembly.
<!--zh-->
本章在通用传递载体处交付共享的子句套件：元层读式 (成对性、单值性、零子句、精确定义域界)、它们的对象语言公式，以及双向解码 (最内层的对隶属、四条子句解码、序数解码、精确性解码与像的读式)。此处没有任何内容提及载体属于哪座塔：套件只消费载体的传递性、对原子套件与内层语义。有界后继原子作为载体泛型的序数内容加入套件，单向后继值子句以结论原子为参数一次交付；层 sigma 章在幂集原子处实例化该子句，S-故事章在步等式处实例化它。消费方在自己的载体处实例化套件，各自保留载体专属的子句与坍缩：真实塔上层公式的极限子句，rud 载体上层 sigma 的加锐后继故事与按分量界，以及各自的 Def 步坍缩与充分性装配。
<!--/-->

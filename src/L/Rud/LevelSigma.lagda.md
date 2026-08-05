# The level sigma at a rud carrier

<!--en-->
The initial-segment chapter wrote the face once, generic in the carrier, and
the level-story clause kit wrote the shared tower-story clauses once, generic
in a transitive carrier. The level-formula chapter supplied the first
instantiation, the wing's own `W2`, at the real tower, and left the recipe:
the carrier, the clause formulas, and the decode discipline, each at its own
tower. This chapter supplies the second instantiation, the bridge's sigma at
a rud carrier. The carrier is a limit level `Jset α` of the rud tower,
transitive by the rud tower's stage theorem and closed under the sixteen
rudimentary operations; the tower story is the same sentence the kit hosts,
functionhood (pairhood and single-valuedness), the zero clause and the exact
domain bound, written at the meta level and again as object-language
formulas. The clause that changes is the Def-step: at a level it collapsed by
the theorem that every member of a stage is definable at a member of that
stage, while at the rud carrier it collapses by the definability chapter's
Refine lemma, that under transitivity every member of a set is definable
there by the atom naming it, with the rud tower's membership chain, every
member of a limit level lies in a carrier member, supplying the descent. The
result is the level sigma, the initial-segment formula at a rud carrier, with
its two-way adequacy.

The limit clause is measured here as the omitted piece and reported as such:
it is about the tower story, not about the carrier, and the tower chapter
keeps it. The strengthened story that follows supplies what the first-limit
carve actually consumes, the successor-value clause and the domain bounds,
on top of the same kit.
<!--zh-->
初始段章把面孔一次写成、以载体为参数，层故事子句套件把共享的塔故事子句一次写成、以传递载体为参数。层公式章交付第一个实例化，即翼自己的 `W2`，落在真实塔上，并留下配方：载体、子句公式与解码纪律，各在自己的塔处。本章交付第二个实例化，即 rud 载体上的桥 sigma。载体是 rud 塔的极限层 `Jset α`，由 rud 塔的阶段定理保证传递、并对十六个初步函数运算封闭；塔故事就是套件托管的同一条句子，函数性 (成对性与单值性)、零子句与精确定义域界，在元层写一遍，再写成对象语言公式。变了的那条子句是 Def 步：在层处它经「层的每个成员都在该层的某成员处可定义」这条定理坍缩；在 rud 载体处它经可定义性章的 Refine 引理坍缩，即传递性之下集合的每个成员都由点名它的原子公式在其上可定义，rud 塔的成员链，「极限层的每个成员都落在某个载体成员里」，供给这段下行。成果就是层 sigma，即 rud 载体处的初始段公式，连同它的双向充分性。

极限子句在此作为缺项被测度并照实报告：它关于塔故事本身，与载体无关，由塔章保留。其后的加锐故事供给第一个极限刻划实际消费的内容，后继值子句与定义域界，立在同一个套件之上。
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
  ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Coding {ℓ} using ( pr )
open import V.Presentation {ℓ} using ( fiber )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-elim; ∈sucV-inl )
open import L.Constructible {ℓ} using ( isTransV; IsOrd; isPropIsOrd )
open import L.Definability {ℓ} using ( module DefOf )
open import L.InitialSegment {ℓ} using ( _⟷_; DefStep; module Face )
open import L.LevelKit {ℓ} using ( module LevelKit )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit )
open import L.Rud.Step {ℓ} lem A using
  ( Sset; Sset-trans; Sset-out; Sset-suc; Sset-in; Jset; limit-succ-mem; step
  ; step-∈ )

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
## The kit at the rud carrier
<!--zh-->
## rud 载体处的套件
<!--/-->

<!--en-->
Everything below is relative to one rud carrier `u = Jset α` at a limit
`α`, with the carrier's transitivity, the rud tower's stage theorem, and its
binding set `K`, a member of the carrier. The kit opens at the carrier: the
shared clauses, functionhood, the zero clause and the exact domain bound,
come with their formulas and their two-way decodes. The approximation entry
is the conjunction of the kit's three clauses, the three-clause story the
carve reads.

The Def-step clause is the successor clause of the tower story, and at a rud
carrier it collapses too. The collapse reads the union at the carrier once: a
member `g` of `Jset α` sits in `step (Sset δ)` for some `δ ∈ α`, hence in the
next level `w = Sset (sucV δ)`, and that next level still belongs to the
carrier because `α` is a limit. The definability chapter's Refine lemma then
names `g` at `w` by the atom "the variable is a member of `g`", and the
carrier's transitivity makes the atom carve out exactly `g`. So the clause
`Cl = ⊤̇`, the kit's truth clause, decodes to the delivered Def-step read in
the forward direction, and the reverse direction is the truth clause itself.

The range read is the graph's second-component projection, and the kit hosts
the object clause `Rg` with its two-way decode `r-ok`. The four telescope
entries are then filled at the rud carrier, and the face's adequacy module
assembles them into the level sigma's two-way adequacy, `read-off`.
<!--zh-->
以下一切都相对于一个 rud 载体 `u = Jset α`，其中 `α` 是极限，载体的传递性就是 rud 塔的阶段定理，绑定集 `K` 是载体的一个成员。套件在载体处打开：共享子句，函数性、零子句与精确定义域界，连同各自的公式与双向解码。近似条目是套件三条子句的合取，即刻划所读的三子句故事。

Def 步子句就是塔故事的后继子句，而在 rud 载体处它也坍缩。坍缩在载体处把并展开一次：`Jset α` 的成员 `g` 对某 `δ ∈ α` 落在 `step (Sset δ)` 里，从而落在下一层 `w = Sset (sucV δ)` 里，而这一层因 `α` 是极限仍属于载体。可定义性章的 Refine 引理随即在 `w` 处用原子公式「该变量属于 `g`」点名 `g`，载体的传递性使原子公式刻出的恰好是 `g`。于是子句 `Cl = ⊤̇`，即套件的真子句，在前进方向解码到已交付的 Def 步读式，反向就是真子句本身。

像的读式是图关系的第二分量投影，套件托管对象子句 `Rg` 连同它的双向解码 `r-ok`。望远镜的四项如今在 rud 载体处填满，面孔的充分性模块把它们装配成层 sigma 的双向充分性，即 `read-off`。
<!--/-->

```agda
-- The tower story at a rud carrier, at the level of the graph.
module LevelAt (α : S) (lim : ⟨ isLimit α ⟩) (K : ⟪ Jset α lim ⟫) where

  u : S
  u = Jset α lim

  utr : isTransV u
  utr = Sset-trans α

  module Kit = LevelKit u utr
  open Kit public

  -- The approximation entry: the three-clause story.
  Approx : V ℓ → V ℓ → Type (ℓ-suc ℓ)
  Approx _ f = pairhood f × singleValued f × zeroClause f

  -- The three-clause object story, at the standing arity.
  Ap : Formula ⟪ u ⟫ 2
  Ap = pairForm ∧̇ singleForm ∧̇ zeroForm

  -- The approximation adequacy, both directions, walking the three
  -- delivered clause decodes.
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

  module F = Face u K Ap Cl Rg
  module A = F.Adequacy Approx a-ok c-ok r-ok

  -- The two-way adequacy at a rud carrier.
  read-off : (m : ⟪ u ⟫) → ⟨ ⟪ u ⟫↪ m ∈ˢ defSet F.σ ⟩ ⟷ A.Elem m
  read-off = A.face-iff
```

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
<!--zh-->
三子句故事钉死了图的函数性与起点，却没有钉死续行：一个近似诚实的见证可以把后继数码映到任意的载体成员，于是像的刻划会越界。经典故事用两条子句补上缺口。后继值子句说后继处的值是前驱值的可定义子集之集；在 rud 载体处这读作载体内幂集关系，`b` 恰好是载体自身的前驱值子集之集时，后继处的图才含有 `b`，用有界量词写出。加锐的定义域界说每个首分量都落在界本身里 (在第一个极限处即落在 `ω` 里)，而不只是落在载体里。两条都作为元层子句、对象语言公式与双向解码在此建造。定义域界按分量读出：经典精确性的完全方向对族刻划是多余的，因为后继值子句自身的双向形状已经逼出值链，故一段的范围无论如何都是若干阶段的集合。极限子句仍然缺位，因为第一个极限之下没有极限序数供它谈论。加锐界在对象语言里的形式由消费方选择：界只在第一个极限之上才是载体的成员 (界可命名事实)，故本章把界记为元层子句的参数，并在载体能命名它的地方兑付。
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
ordinal predicate `isOrdAt` and the exact domain formula `exactDomForm` are
the kit's pieces, and the per-component domain formula `domForm` is this
chapter's own weakening of the exactness, reading each first component as an
ordinal. The successor-value clause `succValForm` assembles its three
quantifiers around the two new atoms.
<!--zh-->
每条新子句都配一条对象语言公式，沿用本章一贯的 de Bruijn 形状。集合的后继不是对象语言的词项，故后继对 `pr (suc a) b` 经有界原子 `sucAt` 读出：`k` 处的集合是 `a` 处集合的后继，当且仅当 `a` 落在 `k` 里、`a` 是 `k` 的子集、且 `k` 的每个成员都是 `a` 的成员或 `a` 本身，全部有界。载体内幂集原子 `powAt` 读作「`b` 处的集合是 `c` 处集合的载体内幂集」：`b` 的每个成员都是 `c` 的子集，而载体中 `c` 的每个子集都落在 `b` 里。序数谓词 `isOrdAt` 与精确定义域公式 `exactDomForm` 是套件的件，按分量定义域公式 `domForm` 是本章对精确性自己的弱化，把每个首分量读作序数。后继值子句 `succValForm` 把三个量词绕两条新原子装配起来。
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

  powAt : {n : ℕ} → Fin n → Fin n → Formula ⟪ u ⟫ n
  powAt b c = (∀̇∈ (var b) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc c)))))
           ∧̇ (∀̇ ( (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc c))))
                 ⇒̇ (var zero ∈̇ var (suc b)) ))

  -- The per-component domain bound: every first component of f is an
  -- ordinal of the carrier.
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
kit's `pair∈` read, the successor pair is read through `sucAt-ok`, and the
two directions of the clause's bi-implication are the two directions of
`powAt-ok`. The ordinal decode `isOrd-out`/`isOrd-in` is the kit's shared
piece, and the per-component domain decode `dom-out`/`dom-in` reads the bound,
each truncated branch a named `where` function with a written type. The
successor-value clause's two-way decode is one lemma `succVal-ok`, and the
successor pair at the graph is decoded once by `succPair-ok`, consumed by both
directions.
<!--zh-->
两条新原子先解码，其余全部消费它们。`sucAt-ok` 把有界后继原子读回后继等式：前进方向沿后继的分情形装置拆开 `k` 的成员，反向从等式重建三条合取项。`powAt-ok` 把载体内幂集原子读回 `powRel`：两条有界量词恰是关系的两条包含，载体传递性供给内层量词索要的证书。后继值子句的解码随之走过它的三个量词：对隶属用套件的 `pair∈` 读式，后继对经 `sucAt-ok` 读出，子句双向蕴含的两头正是 `powAt-ok` 的两个方向。序数解码 `isOrd-out`/`isOrd-in` 是套件的共享件，按分量定义域解码 `dom-out`/`dom-in` 读出界，每条截断分支都是带书面类型的具名 `where` 函数。后继值子句的双向解码是一条引理 `succVal-ok`，图处的后继对由 `succPair-ok` 解码一次，两个方向都消费它。
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
## The strengthened approximation reassembled
<!--zh-->
## 加锐近似条目重新装配
<!--/-->

<!--en-->
Every clause of the strengthened story now has its object formula and its
two-way decode, so the approximation entry reassembles over the delivered
conjuncts verbatim: the five-clause formula `aStForm` is the conjunction of
the three kit clauses, the per-component domain bound and the successor-value
clause, and the two-way adequacy `aSt-ok` walks the five delivered decodes in
each direction. This is the seam the strengthened section recorded: the
reassembly itself, nothing new to prove, and it is what a consumer of the
strengthened story at a carrier instantiates.
<!--zh-->
加锐故事的每条子句如今都有自己的对象公式与双向解码，故近似条目逐合取项在已交付件上重新装配：五合取公式 `aStForm` 是三条套件子句、按分量定义域界与后继值子句的合取，双向充分性 `aSt-ok` 在每一方向上走过五条已交付解码。这正是加锐节所记录的接缝：装配本身，无可新证，也是载体处加锐故事的消费方所要实例化的对象。
<!--/-->

```agda
  -- The strengthened approximation entry: the five-clause story.
  aSt : S → Type (ℓ-suc ℓ)
  aSt f = pairhood f × singleValued f × zeroClause f × ordDom f × succValClause f

  -- The five-clause object story, at the standing arity.
  aStForm : Formula ⟪ u ⟫ 2
  aStForm = pairForm ∧̇ singleForm ∧̇ zeroForm ∧̇ domForm ∧̇ succValForm

  -- The strengthened adequacy, both directions, walking the delivered
  -- clause decodes.
  aSt-out : (f : SM) (x : ⟪ u ⟫) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ aStForm ⟩ → aSt (fst f)
  aSt-out f x (h₁ , (h₂ , (h₃ , (h₄ , h₅)))) =
    ( pairhood-out f x h₁
    , ( single-out f x h₂
      , ( zero-out f x h₃ , ( dom-out f x h₄ , succVal-ok f x .fst h₅ ) ) ) )

  aSt-in : (f : SM) (x : ⟪ u ⟫) → aSt (fst f) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ aStForm ⟩
  aSt-in f x (h₁ , (h₂ , (h₃ , (h₄ , h₅)))) =
    ( pairhood-in f x h₁
    , ( single-in f x h₂
      , ( zero-in f x h₃ , ( dom-in f x h₄ , succVal-ok f x .snd h₅ ) ) ) )

  -- The seam, closed: the five-clause reassembly with its two-way decode.
  aSt-ok : (f : SM) (x : ⟪ u ⟫)
         → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ aStForm ⟩ ⟷ aSt (fst f)
  aSt-ok f x = aSt-out f x , aSt-in f x
```

<!--en-->
## The one-way successor clause and the exact domain bound
<!--zh-->
## 单向后继值子句与精确定义域界
<!--/-->

<!--en-->
The strengthened story is stronger than its consumer can use: over a
powerset-closed carrier the two-way successor clause forces the successor
pair's presence from its powerset reading, and over the hereditarily finite
carrier that forcing is infinite, so the recorded five-clause story has no
finite witness. The classical carve needs only the forward direction, values
for present pairs only, and the exact domain bound, the kit's `exactDom`
shape: some ordinal `δ` of the carrier has exactly the first components of
the witness as its members, read both ways. Both pieces are delivered here.
The one-way clause is the forward half of the delivered `succValClause`, so
its formula and decode machinery survive: the new formula `succValForm1` keeps
the antecedent and drops the reverse implication of the clause's conclusion,
and `succVal1-ok` decodes it through the delivered atoms exactly as
`succVal-ok` decodes its two-way parent. The exact domain bound is the kit's
`exactDomForm` with its two-way decode; the per-component bound of the
strengthened section is a different object, it names no domain and reads no
totality direction. The approximation entry re-assembles once more over the
delivered conjuncts, with the exact bound and the one-way clause in place of
the per-component bound and the two-way clause.
<!--zh-->
加锐故事比消费方所能用的更强：在幂集封闭的载体上，双向后继值子句从幂集读法逼出后继对的存在，而在遗传有穷载体上那种逼迫是无穷的，故所记五合取故事没有有穷见证。经典刻划只需要前进方向，即只为已现之对给值，以及精确定义域界，即套件的 `exactDom` 形状：载体中的某个序数 `δ` 恰好以见证的首分量全体为成员，两头都读。两件都在此交付。单向子句是已交付 `succValClause` 的前进半边，故其公式与解码机器幸存：新公式 `succValForm1` 保留前件、删去子句结论中的反向蕴含，而 `succVal1-ok` 经已交付原子把它解码，恰如 `succVal-ok` 解码其双向母本。精确定义域界是套件的 `exactDomForm` 连同它的双向解码；加锐节的按分量界是另一件东西，它不点名任何定义域、也不读完全方向。近似条目再次在已交付合取项上装配，以精确界与单向子句替下按分量界与双向子句。
<!--/-->

```agda
  -- The one-way successor-value clause: values for present pairs only.
  succValClause1 : S → Type (ℓ-suc ℓ)
  succValClause1 f = (a c b : S) → ⟨ pr a c ∈ˢ f ⟩ → ⟨ pr (sucV a) b ∈ˢ f ⟩ → powRel c b

  -- The delivered two-way clause gives the one-way clause.
  succVal1-of : (f : S) → succValClause f → succValClause1 f
  succVal1-of f sc a c b ac∈f = sc a c b ac∈f .fst
```

<!--en-->
The one-way successor clause's formula is the delivered clause's body with
the conclusion's reverse implication deleted, everything else untouched, so
the delivered atoms `succPairAt`, `succAnt` and `powAt` still carry the
reading.
<!--zh-->
单向子句的公式就是已交付子句的体、删去结论中的反向蕴含，其余原封不动，故已交付原子 `succPairAt`、`succAnt` 与 `powAt` 仍承载读数。
<!--/-->

```agda
  -- The one-way clause's conclusion: a successor pair present gives the
  -- powerset reading (no converse).
  succConc1 : Formula ⟪ u ⟫ 5
  succConc1 = ∃̇ succPairAt ⇒̇ (powAt zero (suc zero))

  succBody1 : Formula ⟪ u ⟫ 5
  succBody1 = succAnt ⇒̇ succConc1

  succValForm1 : Formula ⟪ u ⟫ 2
  succValForm1 = ∀̇ (∀̇ (∀̇ succBody1))
```

<!--en-->
The one-way clause decodes by the same three quantifiers as its parent: the
forward direction applies the satisfied clause to the successor pair's
membership and reads `powAt` back through `powAt-ok`, and the reverse
direction rebuilds the satisfaction from the meta one-way clause, the
delivered `succPair-ok` supplying the successor pair's membership in both
directions.
<!--zh-->
单向子句沿与其母本相同的三个量词解码：前进方向把被满足的子句施于后继对的隶属、再经 `powAt-ok` 把 `powAt` 读回，反向从元层单向子句重建满足，已交付的 `succPair-ok` 双向供给后继对的隶属。
<!--/-->

```agda
  -- The one-way successor-value clause decodes both ways.
  succVal1-ok : (f : SM) (x : ⟪ u ⟫)
              → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ succValForm1 ⟩ ⟷ succValClause1 (fst f)
  succVal1-ok f x = (out , bwd)
    where
    out : ⟨ (f ∷ ι x ∷ []) ⊨ᵐ succValForm1 ⟩ → succValClause1 (fst f)
    out h a c b ac∈f ab∈f = powAt-ok zero (suc zero)
        (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) .fst
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
    bwd : succValClause1 (fst f) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ succValForm1 ⟩
    bwd sc1 am cm bm ant-sat =
      PT.rec (snd ((bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ powAt zero (suc zero))) go
      where
      ac∈f : ⟨ pr (fst am) (fst cm) ∈ˢ fst f ⟩
      ac∈f = pair∈ (suc (suc (suc zero))) (suc (suc zero)) (suc zero)
        (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) .fst ant-sat
      go : Σ[ xm ∈ SM ]
             ⟨ (xm ∷ bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ succPairAt ⟩
         → ⟨ (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ powAt zero (suc zero) ⟩
      go (xm , sat) = powAt-ok zero (suc zero)
        (bm ∷ cm ∷ am ∷ f ∷ ι x ∷ []) .snd
        (sc1 (fst am) (fst cm) (fst bm) ac∈f
          (succPair-ok f x am cm bm .fst (∣ xm , sat ∣₁)))
```

<!--en-->
The approximation entry reassembles once more, verbatim over the delivered
conjuncts: the five-clause formula `aStForm1` and its two-way adequacy
`aSt1-ok` walk the three kit decodes, the kit's exact domain decode and the
one-way successor decode. This is the story the first-limit carve
instantiates.
<!--zh-->
近似条目再次装配，逐合取项走过已交付件：五合取公式 `aStForm1` 及其双向充分性 `aSt1-ok` 走过三条套件解码、套件的精确界解码与单向后继解码。这正是第一个极限刻划所要实例化的故事。
<!--/-->

```agda
  -- The one-way approximation entry: the five-clause story with the exact
  -- domain bound and the one-way successor clause.
  aSt1 : S → Type (ℓ-suc ℓ)
  aSt1 f = pairhood f × singleValued f × zeroClause f × exactDom f × succValClause1 f

  -- The one-way object story, at the standing arity.
  aStForm1 : Formula ⟪ u ⟫ 2
  aStForm1 = pairForm ∧̇ singleForm ∧̇ zeroForm ∧̇ exactDomForm ∧̇ succValForm1

  -- The one-way adequacy, both directions, walking the clause decodes.
  aSt1-out : (f : SM) (x : ⟪ u ⟫) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ aStForm1 ⟩ → aSt1 (fst f)
  aSt1-out f x (h₁ , (h₂ , (h₃ , (h₄ , h₅)))) =
    ( pairhood-out f x h₁
    , ( single-out f x h₂
      , ( zero-out f x h₃ , ( exactDom-out f x h₄ , succVal1-ok f x .fst h₅ ) ) ) )

  aSt1-in : (f : SM) (x : ⟪ u ⟫) → aSt1 (fst f) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ aStForm1 ⟩
  aSt1-in f x (h₁ , (h₂ , (h₃ , (h₄ , h₅)))) =
    ( pairhood-in f x h₁
    , ( single-in f x h₂
      , ( zero-in f x h₃ , ( exactDom-in f x h₄ , succVal1-ok f x .snd h₅ ) ) ) )

  -- The one-way seam, closed.
  aSt1-ok : (f : SM) (x : ⟪ u ⟫)
          → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ aStForm1 ⟩ ⟷ aSt1 (fst f)
  aSt1-ok f x = aSt1-out f x , aSt1-in f x
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The chapter delivers the bridge's sigma at a rud carrier: the approximation
entry of the initial-segment face is the tower story itself, the kit's three
clauses with their shared decodes, with the Def-step collapse and the range
read completing the four entries, and the two-way adequacy `read-off` against
the delivered `defSet` face. The shared kit is consumed, not re-derived, and
the Def-step collapse leans on the definability chapter's Refine lemma rather
than the tower's definable-power descent. What remains of the classical tower
story is the limit clause, measured here as the chapter's omitted piece and
priced in the report; it is about the tower story, not the carrier, and the
tower chapter keeps it. On top of the same kit, the strengthened story
carries the successor-value clause and the domain bounds, and the one-way
form with the exact domain bound is the story the first-limit carve
instantiates. The face's third consumer, the condensation crossing, reuses
the same shared kit and the same recipe at its own carrier. The orchestrator
wires this chapter into `Everything`.
<!--zh-->
本章在 rud 载体处交付桥的 sigma：初始段面孔的近似条目如今就是塔故事本身，套件的三条子句连同它们的共享解码，而 Def 步坍缩与像的读式补全四项，以及对照已交付 `defSet` 面孔的双向充分性 `read-off`。共享套件被消费，而非重推，Def 步坍缩倚靠可定义性章的 Refine 引理，而非塔的可定义幂下行。经典塔故事所余的极限子句，在此作为缺项被测度并在报告中定价；它关于塔故事本身，与载体无关，由塔章保留。在同一个套件之上，加锐故事携带后继值子句与定义域界，而带精确定义域界的单向形式正是第一个极限刻划所要实例化的故事。面孔的第三个消费方，凝聚跨越，在自己的载体处复用同一套共享套件与同一条配方。编排者把本章接入 `Everything`。
<!--/-->

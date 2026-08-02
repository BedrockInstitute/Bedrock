# Graphs of composites

<!--en-->
The switch theorem left one named residue: the closure side asks that a closed
level absorb the image of a composite family, and no single basis function
gives it. The classical route strengthens the induction to the graph
`H(p) = {⟨y, F(y)⟩ : y ∈ p}` and reads the image off `H` with the collection
`F8`. This chapter builds the graph calculus that route needs: the ambient
set, the existential projection, the identity graph, the converse of a
relation, and the join of two graphs. Everything is a chain of the sixteen
basis functions, so everything lands in any level closed under them.
<!--zh-->
切换定理留下一项具名存留：闭包一侧要求封闭层吸收复合族之像，而没有任何单个基函数给出它。经典路线把归纳加强到图 `H(p) = {⟨y, F(y)⟩ : y ∈ p}`，再用收集 `F8` 从 `H` 读出像。本章建造该路线所需的图演算：环境集、存在投影、恒等图、关系之逆、以及两个图的接合。一切都是十六个基函数之链，故一切都落在任何对它们封闭的层里。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett; setIsSet )

module L.Rud.Graphs {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Rud.Ops {ℓ}
  using ( F0; F0-spec; F1; F1-spec; F2; F2-read; F2-write
        ; F3; F3-read; F3-write; F4; F4-read; F4-write
        ; F5; F5-spec; F6; F6-read; F6-write; F7; F7-read; F7-write )
open import L.Rud.Images {ℓ}
  using ( F8; F8-spec; F10; F10-spec; left; right; left-spec; right-spec )
open import L.Rud.Step {ℓ} lem A
  using ( Op16; f3; f4; f8; Fof; Fof-f3; Fof-f4; Fof-f8 )
open import L.Rud.Switch {ℓ} lem A
  using ( dne; ∈s; ∈S; evalC; imgOpC; ConIn; AllIn
        ; interOp; interSpec; unionOp; unionSpec; colOp; colSpec
        ; chSepOp; chSepSpec; eqSepOp; eqSepSpec; module Bs; module Closure )
open Bs using ( Comp; conC; varC; interC; diffC; unionC; pairC; colC
              ; chSepC; eqSepC; imgC )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit using ( Unit*; tt* )
open import Cubical.Foundations.Equiv using ( equivFun; invEquiv )
import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; _≡ₕ_; _∼_; _⊆_; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber; extensionality
        ; identityPrinciple )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The small kit

Three derived operations carry the whole chapter: the binary union, the binary
intersection, and the range of a relation. Each is a chain of basis functions,
each is sealed at its birth site with its specification inside the seal
(lesson R-38), and each specification is stated at the structure's membership
with every set written out.
<!--zh-->
## 小器材

三个派生运算承载全章：二元并、二元交、以及关系的值域。每个都是基函数之链，每个都在其诞生处连同规格一并封印 (法则 R-38)，每条规格都以结构的隶属陈述，且每个集合都写明。
<!--/-->

```agda
opaque
  cup : V ℓ → V ℓ → V ℓ
  cup a b = F5 (F0 a b) (F0 a b)

  cup-in : (a b x : V ℓ) → ⟨ (x ∈ˢ a) ⊔ (x ∈ˢ b) ⟩ → ⟨ x ∈ˢ cup a b ⟩
  cup-in a b x = PT.rec (snd (x ∈ˢ cup a b)) go
    where
    go : (⟨ x ∈ˢ a ⟩ ⊎ ⟨ x ∈ˢ b ⟩) → ⟨ x ∈ˢ cup a b ⟩
    go (inl h) = F5-spec (F0 a b) (F0 a b) x .snd
      ∣ a , (F0-spec a b a .snd ∣ inl refl ∣₁ , h) ∣₁
    go (inr h) = F5-spec (F0 a b) (F0 a b) x .snd
      ∣ b , (F0-spec a b b .snd ∣ inr refl ∣₁ , h) ∣₁

  cup-out : (a b x : V ℓ) → ⟨ x ∈ˢ cup a b ⟩ → ⟨ (x ∈ˢ a) ⊔ (x ∈ˢ b) ⟩
  cup-out a b x h = PT.rec (snd ((x ∈ˢ a) ⊔ (x ∈ˢ b))) go
    (F5-spec (F0 a b) (F0 a b) x .fst h)
    where
    go : Σ[ v ∈ V ℓ ] ⟨ (v ∈ˢ F0 a b) ⊓ (x ∈ˢ v) ⟩ → ⟨ (x ∈ˢ a) ⊔ (x ∈ˢ b) ⟩
    go (v , v∈ , x∈v) = PT.rec (snd ((x ∈ˢ a) ⊔ (x ∈ˢ b))) sides
      (F0-spec a b v .fst v∈)
      where
      sides : (⟨ v ≡ₕ a ⟩ ⊎ ⟨ v ≡ₕ b ⟩) → ⟨ (x ∈ˢ a) ⊔ (x ∈ˢ b) ⟩
      sides (inl e) = ∣ inl (subst (λ t → ⟨ x ∈ˢ t ⟩) e x∈v) ∣₁
      sides (inr e) = ∣ inr (subst (λ t → ⟨ x ∈ˢ t ⟩) e x∈v) ∣₁

opaque
  cap : V ℓ → V ℓ → V ℓ
  cap a b = F1 a (F1 a b)

  cap-in : (a b x : V ℓ) → ⟨ x ∈ˢ a ⟩ → ⟨ x ∈ˢ b ⟩ → ⟨ x ∈ˢ cap a b ⟩
  cap-in a b x x∈a x∈b = F1-spec a (F1 a b) x .snd
    (x∈a , λ h → F1-spec a b x .fst h .snd x∈b)

  cap-outl : (a b x : V ℓ) → ⟨ x ∈ˢ cap a b ⟩ → ⟨ x ∈ˢ a ⟩
  cap-outl a b x h = F1-spec a (F1 a b) x .fst h .fst

  cap-outr : (a b x : V ℓ) → ⟨ x ∈ˢ cap a b ⟩ → ⟨ x ∈ˢ b ⟩
  cap-outr a b x h = ∈S x b (dne (x ∈ₛ b)
    (λ x∉b → F1-spec a (F1 a b) x .fst h .snd
      (F1-spec a b x .snd
        ( F1-spec a (F1 a b) x .fst h .fst
        , λ k → x∉b (∈s x b k) ))))
```

<!--en-->
## The range, which is the existential projection

The range of a relation is the one construction that eliminates an existential:
`v ∈ ran R` exactly when some `u` has `⟨u,v⟩ ∈ R`. It is the union of the
slices of `R` taken at the members of its domain, so it is `F5`, `F8`, `F6` and
`F10` in one chain. Every later construction uses it to discharge a bound
quantifier, and it is the reason the leading coordinate of a tuple is always
the one being quantified away.
<!--zh-->
## 值域，即存在投影

关系的值域是唯一消去存在量词的构造：`v ∈ ran R` 恰当某个 `u` 使 `⟨u,v⟩ ∈ R`。它是 `R` 在其定义域各成员处切片之并，故是 `F5`、`F8`、`F6`、`F10` 的一条链。此后每个构造都用它兑付一个有界量词，这也是元组的首坐标总是被量掉的那个坐标的原因。
<!--/-->

```agda
opaque
  ranOp : V ℓ → V ℓ
  ranOp R = F5 (F8 R (F6 R R)) (F8 R (F6 R R))

  ran-in : (R u v : V ℓ) → ⟨ pr u v ∈ˢ R ⟩ → ⟨ v ∈ˢ ranOp R ⟩
  ran-in R u v h = F5-spec (F8 R (F6 R R)) (F8 R (F6 R R)) v .snd
    ∣ F10 R u , (slice∈ , v∈slice) ∣₁
    where
    u∈dom : ⟨ u ∈ˢ F6 R R ⟩
    u∈dom = F6-write R R u ∣ u , v , (h , refl) ∣₁
    fib : Σ[ m ∈ ⟪ F6 R R ⟫ ] (⟪ F6 R R ⟫↪ m ≡ u)
    fib = ∈-asFiber {a = u} {b = F6 R R} u∈dom
    slice∈ : ⟨ F10 R u ∈ˢ F8 R (F6 R R) ⟩
    slice∈ = subst ⟨_⟩ (sym (F8-spec R (F6 R R) (F10 R u)))
      ∣ fib .fst , cong (F10 R) (fib .snd) ∣₁
    v∈slice : ⟨ v ∈ˢ F10 R u ⟩
    v∈slice = subst ⟨_⟩ (sym (F10-spec R u v)) h

  ran-out : (R v : V ℓ) → ⟨ v ∈ˢ ranOp R ⟩
          → ∥ Σ[ u ∈ V ℓ ] ⟨ pr u v ∈ˢ R ⟩ ∥₁
  ran-out R v h = PT.rec squash₁ outer
    (F5-spec (F8 R (F6 R R)) (F8 R (F6 R R)) v .fst h)
    where
    outer : Σ[ W ∈ V ℓ ] ⟨ (W ∈ˢ F8 R (F6 R R)) ⊓ (v ∈ˢ W) ⟩
          → ∥ Σ[ u ∈ V ℓ ] ⟨ pr u v ∈ˢ R ⟩ ∥₁
    outer (W , W∈ , v∈W) = PT.rec squash₁ inner
      (subst ⟨_⟩ (F8-spec R (F6 R R) W) W∈)
      where
      inner : Σ[ m ∈ ⟪ F6 R R ⟫ ] ⟨ F10 R (⟪ F6 R R ⟫↪ m) ≡ₕ W ⟩
            → ∥ Σ[ u ∈ V ℓ ] ⟨ pr u v ∈ˢ R ⟩ ∥₁
      inner (m , e) = ∣ ⟪ F6 R R ⟫↪ m
        , subst ⟨_⟩ (F10-spec R (⟪ F6 R R ⟫↪ m) v)
            (subst (λ t → ⟨ v ∈ˢ t ⟩) (sym e) v∈W) ∣₁
```

<!--en-->
## The ambient set

Extensionality has to be tested somewhere, and the test set is `p` together
with the members of its members. Nothing below quantifies outside it: two
members of `p` that agree on the ambient set agree outright.
<!--zh-->
## 环境集

外延性总要在某处检验，检验集就是 `p` 连同其成员的成员。下文没有任何量词跑到它之外：`p` 的两个成员若在环境集上一致，就径直一致。
<!--/-->

```agda
opaque
  amb : V ℓ → V ℓ
  amb p = cup p (F5 p p)

  amb-self : (p y : V ℓ) → ⟨ y ∈ˢ p ⟩ → ⟨ y ∈ˢ amb p ⟩
  amb-self p y h = cup-in p (F5 p p) y ∣ inl h ∣₁

  amb-mem : (p y c : V ℓ) → ⟨ y ∈ˢ p ⟩ → ⟨ c ∈ˢ y ⟩ → ⟨ c ∈ˢ amb p ⟩
  amb-mem p y c y∈p c∈y = cup-in p (F5 p p) c
    ∣ inr (F5-spec p p c .snd ∣ y , (y∈p , c∈y) ∣₁) ∣₁
```

<!--en-->
## The triple space and the two membership tests

The tuple calculus of the basis is narrow: `F3` inserts a coordinate after the
first, `F4` appends one at the end of a pair, and the range strips the leading
coordinate. That is exactly enough to write the two padded membership
relations on triples `⟨c, a, b⟩`: one says `c ∈ a`, the other says `c ∈ b`,
and both live in the same triple space, so their difference is meaningful.
<!--zh-->
## 三元组空间与两个隶属检验

基的元组演算很窄：`F3` 在首坐标之后插入一个坐标，`F4` 在一个对的末端追加一个坐标，值域则剥去首坐标。这恰好够写出三元组 `⟨c, a, b⟩` 上两个加衬的隶属关系：一个说 `c ∈ a`，另一个说 `c ∈ b`，两者住在同一个三元组空间里，故其差有意义。
<!--/-->

```agda
opaque
  mrel : V ℓ → V ℓ
  mrel q = F7 q q

  mrel-in : (q c a : V ℓ) → ⟨ c ∈ˢ q ⟩ → ⟨ a ∈ˢ q ⟩ → ⟨ c ∈ˢ a ⟩
          → ⟨ pr c a ∈ˢ mrel q ⟩
  mrel-in q c a c∈ a∈ c∈a = F7-write q q (pr c a)
    ∣ c , a , (c∈ , a∈ , c∈a , refl) ∣₁

  mrel-out : (q c a : V ℓ) → ⟨ pr c a ∈ˢ mrel q ⟩ → ⟨ c ∈ˢ a ⟩
  mrel-out q c a h = PT.rec (snd (c ∈ˢ a)) go (F7-read q q (pr c a) h)
    where
    go : Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ]
           (⟨ u ∈ˢ q ⟩ × ⟨ v ∈ˢ q ⟩ × ⟨ u ∈ˢ v ⟩ × ⟨ pr c a ≡ₕ pr u v ⟩)
       → ⟨ c ∈ˢ a ⟩
    go (u , v , _ , _ , u∈v , e) =
      subst (λ t → ⟨ t ∈ˢ a ⟩) (sym (pr-inj {a = c} {b = a} {c = u} {d = v} e .fst))
        (subst (λ t → ⟨ u ∈ˢ t ⟩)
          (sym (pr-inj {a = c} {b = a} {c = u} {d = v} e .snd)) u∈v)

opaque
  tsp : V ℓ → V ℓ
  tsp p = F2 (amb p) (F2 p p)

  tsp-in : (p c a b : V ℓ) → ⟨ c ∈ˢ amb p ⟩ → ⟨ a ∈ˢ p ⟩ → ⟨ b ∈ˢ p ⟩
         → ⟨ pr c (pr a b) ∈ˢ tsp p ⟩
  tsp-in p c a b c∈ a∈ b∈ = F2-write (amb p) (F2 p p) (pr c (pr a b))
    ∣ c , pr a b
    , ( c∈ , F2-write p p (pr a b) ∣ a , b , (a∈ , b∈ , refl) ∣₁ , refl ) ∣₁

opaque
  lft : V ℓ → V ℓ
  lft p = cap (F4 p (mrel (amb p))) (tsp p)

  rgt : V ℓ → V ℓ
  rgt p = cap (F3 p (mrel (amb p))) (tsp p)

  lft-in : (p c a b : V ℓ) → ⟨ c ∈ˢ amb p ⟩ → ⟨ a ∈ˢ p ⟩ → ⟨ b ∈ˢ p ⟩ → ⟨ c ∈ˢ a ⟩
         → ⟨ pr c (pr a b) ∈ˢ lft p ⟩
  lft-in p c a b c∈ a∈ b∈ c∈a =
    cap-in (F4 p (mrel (amb p))) (tsp p) (pr c (pr a b))
      (F4-write p (mrel (amb p)) (pr c (pr a b))
        ∣ c , a , b
        , (b∈ , mrel-in (amb p) c a c∈ (amb-self p a a∈) c∈a , refl) ∣₁)
      (tsp-in p c a b c∈ a∈ b∈)

  rgt-in : (p c a b : V ℓ) → ⟨ c ∈ˢ amb p ⟩ → ⟨ a ∈ˢ p ⟩ → ⟨ b ∈ˢ p ⟩ → ⟨ c ∈ˢ b ⟩
         → ⟨ pr c (pr a b) ∈ˢ rgt p ⟩
  rgt-in p c a b c∈ a∈ b∈ c∈b =
    cap-in (F3 p (mrel (amb p))) (tsp p) (pr c (pr a b))
      (F3-write p (mrel (amb p)) (pr c (pr a b))
        ∣ c , a , b
        , (a∈ , mrel-in (amb p) c b c∈ (amb-self p b b∈) c∈b , refl) ∣₁)
      (tsp-in p c a b c∈ a∈ b∈)

  lft-out : (p c a b : V ℓ) → ⟨ pr c (pr a b) ∈ˢ lft p ⟩ → ⟨ c ∈ˢ a ⟩
  lft-out p c a b h = PT.rec (snd (c ∈ˢ a)) go
    (F4-read p (mrel (amb p)) (pr c (pr a b))
      (cap-outl (F4 p (mrel (amb p))) (tsp p) (pr c (pr a b)) h))
    where
    go : Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ] Σ[ z ∈ V ℓ ]
           (⟨ z ∈ˢ p ⟩ × ⟨ pr u v ∈ˢ mrel (amb p) ⟩
            × ⟨ pr c (pr a b) ≡ₕ pr u (pr v z) ⟩)
       → ⟨ c ∈ˢ a ⟩
    go (u , v , z , _ , uv∈ , e) =
      subst (λ t → ⟨ t ∈ˢ a ⟩) (sym c≡u)
        (subst (λ t → ⟨ u ∈ˢ t ⟩) (sym a≡v) (mrel-out (amb p) u v uv∈))
      where
      c≡u : c ≡ u
      c≡u = pr-inj {a = c} {b = pr a b} {c = u} {d = pr v z} e .fst
      a≡v : a ≡ v
      a≡v = pr-inj {a = a} {b = b} {c = v} {d = z}
        (pr-inj {a = c} {b = pr a b} {c = u} {d = pr v z} e .snd) .fst

  rgt-out : (p c a b : V ℓ) → ⟨ pr c (pr a b) ∈ˢ rgt p ⟩ → ⟨ c ∈ˢ b ⟩
  rgt-out p c a b h = PT.rec (snd (c ∈ˢ b)) go
    (F3-read p (mrel (amb p)) (pr c (pr a b))
      (cap-outl (F3 p (mrel (amb p))) (tsp p) (pr c (pr a b)) h))
    where
    go : Σ[ u ∈ V ℓ ] Σ[ z ∈ V ℓ ] Σ[ v ∈ V ℓ ]
           (⟨ z ∈ˢ p ⟩ × ⟨ pr u v ∈ˢ mrel (amb p) ⟩
            × ⟨ pr c (pr a b) ≡ₕ pr u (pr z v) ⟩)
       → ⟨ c ∈ˢ b ⟩
    go (u , z , v , _ , uv∈ , e) =
      subst (λ t → ⟨ t ∈ˢ b ⟩) (sym c≡u)
        (subst (λ t → ⟨ u ∈ˢ t ⟩) (sym b≡v) (mrel-out (amb p) u v uv∈))
      where
      c≡u : c ≡ u
      c≡u = pr-inj {a = c} {b = pr a b} {c = u} {d = pr z v} e .fst
      b≡v : b ≡ v
      b≡v = pr-inj {a = a} {b = b} {c = z} {d = v}
        (pr-inj {a = c} {b = pr a b} {c = u} {d = pr z v} e .snd) .snd
```

<!--en-->
## The identity graph

The identity graph `{⟨y, y⟩ : y ∈ p}` is the base case of the whole induction,
and the two obvious routes to it are circular in the image operation being
built. This one is not: it cuts the square `p × p` by the pairs that a witness
separates. A witness for `⟨a, b⟩` is a member of the ambient set lying in one
of the two and not the other; the pairs with no witness are exactly the
diagonal, by extensionality. The forward reading spends excluded middle once,
through double negation, which is where a constructive reading of "no witness"
falls short of equality.
<!--zh-->
## 恒等图

恒等图 `{⟨y, y⟩ : y ∈ p}` 是整个归纳的基础情形，而通向它的两条显然路线在所建之像运算上循环。这一条不循环：它把方 `p × p` 按有见证分离的对切开。`⟨a, b⟩` 的见证是环境集的一个成员，落在两者之一而不落在另一个；无见证的对恰是对角线，由外延性所致。正向读取花掉一次排中律，经双重否定，这正是「无见证」的构造性读法够不到相等之处。
<!--/-->

```agda
opaque
  wit : V ℓ → V ℓ
  wit p = cup (F1 (lft p) (rgt p)) (F1 (rgt p) (lft p))

  neq : V ℓ → V ℓ
  neq p = ranOp (wit p)

  neq-inl : (p c a b : V ℓ) → ⟨ pr c (pr a b) ∈ˢ lft p ⟩
          → (⟨ pr c (pr a b) ∈ˢ rgt p ⟩ → Empty.⊥) → ⟨ pr a b ∈ˢ neq p ⟩
  neq-inl p c a b h₁ h₂ = ran-in (wit p) c (pr a b)
    (cup-in (F1 (lft p) (rgt p)) (F1 (rgt p) (lft p)) (pr c (pr a b))
      ∣ inl (F1-spec (lft p) (rgt p) (pr c (pr a b)) .snd (h₁ , h₂)) ∣₁)

  neq-inr : (p c a b : V ℓ) → ⟨ pr c (pr a b) ∈ˢ rgt p ⟩
          → (⟨ pr c (pr a b) ∈ˢ lft p ⟩ → Empty.⊥) → ⟨ pr a b ∈ˢ neq p ⟩
  neq-inr p c a b h₁ h₂ = ran-in (wit p) c (pr a b)
    (cup-in (F1 (lft p) (rgt p)) (F1 (rgt p) (lft p)) (pr c (pr a b))
      ∣ inr (F1-spec (rgt p) (lft p) (pr c (pr a b)) .snd (h₁ , h₂)) ∣₁)

  neq-out : (p t : V ℓ) → ⟨ t ∈ˢ neq p ⟩
          → ∥ Σ[ c ∈ V ℓ ]
               ( (⟨ pr c t ∈ˢ lft p ⟩ × (⟨ pr c t ∈ˢ rgt p ⟩ → Empty.⊥))
               ⊎ (⟨ pr c t ∈ˢ rgt p ⟩ × (⟨ pr c t ∈ˢ lft p ⟩ → Empty.⊥)) ) ∥₁
  neq-out p t h = PT.rec squash₁ outer (ran-out (wit p) t h)
    where
    D : Type (ℓ-suc ℓ)
    D = Σ[ c ∈ V ℓ ]
          ( (⟨ pr c t ∈ˢ lft p ⟩ × (⟨ pr c t ∈ˢ rgt p ⟩ → Empty.⊥))
          ⊎ (⟨ pr c t ∈ˢ rgt p ⟩ × (⟨ pr c t ∈ˢ lft p ⟩ → Empty.⊥)) )
    outer : Σ[ c ∈ V ℓ ] ⟨ pr c t ∈ˢ wit p ⟩ → ∥ D ∥₁
    outer (c , h') = PT.rec squash₁ sides
      (cup-out (F1 (lft p) (rgt p)) (F1 (rgt p) (lft p)) (pr c t) h')
      where
      sides : (⟨ pr c t ∈ˢ F1 (lft p) (rgt p) ⟩ ⊎ ⟨ pr c t ∈ˢ F1 (rgt p) (lft p) ⟩)
            → ∥ D ∥₁
      sides (inl k) = ∣ c , inl (F1-spec (lft p) (rgt p) (pr c t) .fst k) ∣₁
      sides (inr k) = ∣ c , inr (F1-spec (rgt p) (lft p) (pr c t) .fst k) ∣₁

opaque
  idG : V ℓ → V ℓ
  idG p = F1 (F2 p p) (neq p)

  idG-in : (p a : V ℓ) → ⟨ a ∈ˢ p ⟩ → ⟨ pr a a ∈ˢ idG p ⟩
  idG-in p a a∈ = F1-spec (F2 p p) (neq p) (pr a a) .snd
    ( F2-write p p (pr a a) ∣ a , a , (a∈ , a∈ , refl) ∣₁ , noWit )
    where
    noWit : ⟨ pr a a ∈ˢ neq p ⟩ → Empty.⊥
    noWit h = PT.rec Empty.isProp⊥ go (neq-out p (pr a a) h)
      where
      go : Σ[ c ∈ V ℓ ]
             ( (⟨ pr c (pr a a) ∈ˢ lft p ⟩ × (⟨ pr c (pr a a) ∈ˢ rgt p ⟩ → Empty.⊥))
             ⊎ (⟨ pr c (pr a a) ∈ˢ rgt p ⟩ × (⟨ pr c (pr a a) ∈ˢ lft p ⟩ → Empty.⊥)) )
         → Empty.⊥
      go (c , inl (k , nk)) = nk (rgt-in p c a a
        (amb-mem p a c a∈ (lft-out p c a a k)) a∈ a∈ (lft-out p c a a k))
      go (c , inr (k , nk)) = nk (lft-in p c a a
        (amb-mem p a c a∈ (rgt-out p c a a k)) a∈ a∈ (rgt-out p c a a k))

  idG-out : (p t : V ℓ) → ⟨ t ∈ˢ idG p ⟩
          → ∥ Σ[ a ∈ V ℓ ] (⟨ a ∈ˢ p ⟩ × ⟨ t ≡ₕ pr a a ⟩) ∥₁
  idG-out p t h = PT.rec squash₁ go
    (F2-read p p t (F1-spec (F2 p p) (neq p) t .fst h .fst))
    where
    nonq : ⟨ t ∈ˢ neq p ⟩ → Empty.⊥
    nonq = F1-spec (F2 p p) (neq p) t .fst h .snd
    go : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] (⟨ a ∈ˢ p ⟩ × ⟨ b ∈ˢ p ⟩ × ⟨ t ≡ₕ pr a b ⟩)
       → ∥ Σ[ a ∈ V ℓ ] (⟨ a ∈ˢ p ⟩ × ⟨ t ≡ₕ pr a a ⟩) ∥₁
    go (a , b , a∈ , b∈ , e) = ∣ a , (a∈ , e ∙ cong (pr a) (sym a≡b)) ∣₁
      where
      nonq' : ⟨ pr a b ∈ˢ neq p ⟩ → Empty.⊥
      nonq' k = nonq (subst (λ w → ⟨ w ∈ˢ neq p ⟩) (sym e) k)
      sub₁ : ⟨ a ⊆ b ⟩
      sub₁ c c∈ₛa = ∈s c b (∈S c b (dne (c ∈ₛ b) notnot))
        where
        c∈a : ⟨ c ∈ˢ a ⟩
        c∈a = ∈S c a c∈ₛa
        notnot : (⟨ c ∈ₛ b ⟩ → Empty.⊥) → Empty.⊥
        notnot nc = nonq' (neq-inl p c a b
          (lft-in p c a b (amb-mem p a c a∈ c∈a) a∈ b∈ c∈a)
          (λ k → nc (∈s c b (rgt-out p c a b k))))
      sub₂ : ⟨ b ⊆ a ⟩
      sub₂ c c∈ₛb = ∈s c a (∈S c a (dne (c ∈ₛ a) notnot))
        where
        c∈b : ⟨ c ∈ˢ b ⟩
        c∈b = ∈S c b c∈ₛb
        notnot : (⟨ c ∈ₛ a ⟩ → Empty.⊥) → Empty.⊥
        notnot nc = nonq' (neq-inr p c a b
          (rgt-in p c a b (amb-mem p b c b∈ c∈b) a∈ b∈ c∈b)
          (λ k → nc (∈s c a (lft-out p c a b k))))
      a≡b : a ≡ b
      a≡b = extensionality a b (sub₁ , sub₂)
```

<!--en-->
## The join of two graphs

The second construction the scoping named is the join: two relations on a
common first coordinate are merged into one relation whose value is the pair
of the two values. `F4` appends a coordinate at the end of a pair and `F3`
inserts one after the first, so each relation can be padded into the same
triple space with the other's slot left free, and the join is the
intersection of the two paddings. This is what the two shuffling functions of
the basis are for.
<!--zh-->
## 两个图的接合

摸底具名的第二个构造是接合：共享首坐标的两个关系合并为一个关系，其值是两个值之对。`F4` 在一个对的末端追加坐标，`F3` 在首坐标之后插入坐标，故每个关系都能加衬进同一个三元组空间、把对方的槽留空，接合即两次加衬之交。基的两个搬运函数正为此而设。
<!--/-->

```agda
opaque
  joinOp : V ℓ → V ℓ → V ℓ → V ℓ → V ℓ
  joinOp R S Wr Ws = cap (F4 Ws R) (F3 Wr S)

  join-in : (R S Wr Ws d u v : V ℓ)
          → ⟨ pr d u ∈ˢ R ⟩ → ⟨ pr d v ∈ˢ S ⟩ → ⟨ u ∈ˢ Wr ⟩ → ⟨ v ∈ˢ Ws ⟩
          → ⟨ pr d (pr u v) ∈ˢ joinOp R S Wr Ws ⟩
  join-in R S Wr Ws d u v du∈ dv∈ u∈ v∈ =
    cap-in (F4 Ws R) (F3 Wr S) (pr d (pr u v))
      (F4-write Ws R (pr d (pr u v)) ∣ d , u , v , (v∈ , du∈ , refl) ∣₁)
      (F3-write Wr S (pr d (pr u v)) ∣ d , u , v , (u∈ , dv∈ , refl) ∣₁)

  join-outl : (R S Wr Ws d u v : V ℓ)
            → ⟨ pr d (pr u v) ∈ˢ joinOp R S Wr Ws ⟩ → ⟨ pr d u ∈ˢ R ⟩
  join-outl R S Wr Ws d u v h = PT.rec (snd (pr d u ∈ˢ R)) go
    (F4-read Ws R (pr d (pr u v)) (cap-outl (F4 Ws R) (F3 Wr S) (pr d (pr u v)) h))
    where
    go : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] Σ[ z ∈ V ℓ ]
           (⟨ z ∈ˢ Ws ⟩ × ⟨ pr a b ∈ˢ R ⟩ × ⟨ pr d (pr u v) ≡ₕ pr a (pr b z) ⟩)
       → ⟨ pr d u ∈ˢ R ⟩
    go (a , b , z , _ , ab∈ , e) = subst (λ t → ⟨ t ∈ˢ R ⟩)
      (sym (cong₂ pr (pr-inj {a = d} {b = pr u v} {c = a} {d = pr b z} e .fst)
        (pr-inj {a = u} {b = v} {c = b} {d = z}
          (pr-inj {a = d} {b = pr u v} {c = a} {d = pr b z} e .snd) .fst))) ab∈

  join-outr : (R S Wr Ws d u v : V ℓ)
            → ⟨ pr d (pr u v) ∈ˢ joinOp R S Wr Ws ⟩ → ⟨ pr d v ∈ˢ S ⟩
  join-outr R S Wr Ws d u v h = PT.rec (snd (pr d v ∈ˢ S)) go
    (F3-read Wr S (pr d (pr u v)) (cap-outr (F4 Ws R) (F3 Wr S) (pr d (pr u v)) h))
    where
    go : Σ[ a ∈ V ℓ ] Σ[ z ∈ V ℓ ] Σ[ b ∈ V ℓ ]
           (⟨ z ∈ˢ Wr ⟩ × ⟨ pr a b ∈ˢ S ⟩ × ⟨ pr d (pr u v) ≡ₕ pr a (pr z b) ⟩)
       → ⟨ pr d v ∈ˢ S ⟩
    go (a , z , b , _ , ab∈ , e) = subst (λ t → ⟨ t ∈ˢ S ⟩)
      (sym (cong₂ pr (pr-inj {a = d} {b = pr u v} {c = a} {d = pr z b} e .fst)
        (pr-inj {a = u} {b = v} {c = z} {d = b}
          (pr-inj {a = d} {b = pr u v} {c = a} {d = pr z b} e .snd) .snd))) ab∈
```

<!--en-->
## The image, read off an element relation

The point of the whole calculus is this equation. Call a relation `R` an
element relation for a family `val` over `p` when `⟨y, w⟩ ∈ R` says exactly
that `w` is a member of `val y`, for `y` in `p`. Then the collection `F8 R p`
is the image of the family: `F8` takes the slice of `R` at each member of `p`,
and each slice is a value. No union is needed, because the element relation
already carries the members rather than the values.
<!--zh-->
## 从元素关系读出像

整套演算的要点就是这条方程。若关系 `R` 满足：对 `p` 中的 `y`，`⟨y, w⟩ ∈ R` 恰好说 `w` 是 `val y` 的成员，则称 `R` 是族 `val` 在 `p` 上的元素关系。此时收集 `F8 R p` 就是该族之像：`F8` 在 `p` 的每个成员处取 `R` 的切片，而每个切片就是一个值。不需要再取并，因为元素关系携带的本就是成员而非值。
<!--/-->

```agda
slice-eq : (R y val : V ℓ)
         → ((w : V ℓ) → ⟨ pr y w ∈ˢ R ⟩ → ⟨ w ∈ˢ val ⟩)
         → ((w : V ℓ) → ⟨ w ∈ˢ val ⟩ → ⟨ pr y w ∈ˢ R ⟩)
         → F10 R y ≡ val
slice-eq R y val fwd bwd = extensionality (F10 R y) val (sub₁ , sub₂)
  where
  sub₁ : ⟨ F10 R y ⊆ val ⟩
  sub₁ w h = ∈s w val (fwd w (subst ⟨_⟩ (F10-spec R y w) (∈S w (F10 R y) h)))
  sub₂ : ⟨ val ⊆ F10 R y ⟩
  sub₂ w h = ∈s w (F10 R y) (subst ⟨_⟩ (sym (F10-spec R y w)) (bwd w (∈S w val h)))

img-of-rel : (R p : V ℓ) (val : V ℓ → V ℓ)
           → ((y w : V ℓ) → ⟨ y ∈ˢ p ⟩ → ⟨ pr y w ∈ˢ R ⟩ → ⟨ w ∈ˢ val y ⟩)
           → ((y w : V ℓ) → ⟨ y ∈ˢ p ⟩ → ⟨ w ∈ˢ val y ⟩ → ⟨ pr y w ∈ˢ R ⟩)
           → sett ⟪ p ⟫ (λ m → val (⟪ p ⟫↪ m)) ≡ F8 R p
img-of-rel R p val fwd bwd = cong (sett ⟪ p ⟫) (funExt fam)
  where
  fam : (m : ⟪ p ⟫) → val (⟪ p ⟫↪ m) ≡ F10 R (⟪ p ⟫↪ m)
  fam m = sym (slice-eq R (⟪ p ⟫↪ m) (val (⟪ p ⟫↪ m))
    (λ w → fwd (⟪ p ⟫↪ m) w (∈S (⟪ p ⟫↪ m) p (∈ₛ⟪ p ⟫↪ m)))
    (λ w → bwd (⟪ p ⟫↪ m) w (∈S (⟪ p ⟫↪ m) p (∈ₛ⟪ p ⟫↪ m))))
```

<!--en-->
## The converse of a relation

Slices are taken at the first coordinate and the range strips the first
coordinate, so a relation can only be read in the direction it was written.
Turning it around is the one move the tuple calculus cannot make by padding
alone, and the identity graph is exactly what pays for it: the triple
`⟨u, v, u⟩` whose first and last coordinates agree is the intersection of one
padding of the relation with one padding of the identity graph, and stripping
its leading coordinate leaves `⟨v, u⟩`.
<!--zh-->
## 关系之逆

切片在首坐标处取，值域也剥去首坐标，故关系只能按写下的方向读。把它翻转过来是元组演算单靠加衬做不到的一步，而恒等图恰好为此买单：首尾坐标相同的三元组 `⟨u, v, u⟩` 是关系的一次加衬与恒等图的一次加衬之交，剥去其首坐标便剩下 `⟨v, u⟩`。
<!--/-->

```agda
opaque
  swp : V ℓ → V ℓ → V ℓ
  swp R q = ranOp (cap (F4 q R) (F3 q (idG q)))

  swp-in : (R q u v : V ℓ) → ⟨ pr u v ∈ˢ R ⟩ → ⟨ u ∈ˢ q ⟩ → ⟨ v ∈ˢ q ⟩
         → ⟨ pr v u ∈ˢ swp R q ⟩
  swp-in R q u v uv∈ u∈ v∈ = ran-in (cap (F4 q R) (F3 q (idG q))) u (pr v u)
    (cap-in (F4 q R) (F3 q (idG q)) (pr u (pr v u))
      (F4-write q R (pr u (pr v u)) ∣ u , v , u , (u∈ , uv∈ , refl) ∣₁)
      (F3-write q (idG q) (pr u (pr v u))
        ∣ u , v , u , (v∈ , idG-in q u u∈ , refl) ∣₁))

  swp-out : (R q t : V ℓ) → ⟨ t ∈ˢ swp R q ⟩
          → ∥ Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ] (⟨ pr u v ∈ˢ R ⟩ × ⟨ t ≡ₕ pr v u ⟩) ∥₁
  swp-out R q t h = PT.rec squash₁ outer
    (ran-out (cap (F4 q R) (F3 q (idG q))) t h)
    where
    D : Type (ℓ-suc ℓ)
    D = Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ] (⟨ pr u v ∈ˢ R ⟩ × ⟨ t ≡ₕ pr v u ⟩)
    outer : Σ[ w ∈ V ℓ ] ⟨ pr w t ∈ˢ cap (F4 q R) (F3 q (idG q)) ⟩ → ∥ D ∥₁
    outer (w , h') = PT.rec squash₁ fromR
      (F4-read q R (pr w t) (cap-outl (F4 q R) (F3 q (idG q)) (pr w t) h'))
      where
      fromR : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] Σ[ z ∈ V ℓ ]
                (⟨ z ∈ˢ q ⟩ × ⟨ pr a b ∈ˢ R ⟩ × ⟨ pr w t ≡ₕ pr a (pr b z) ⟩)
            → ∥ D ∥₁
      fromR (a , b , z , _ , ab∈ , e₁) = PT.rec squash₁ fromId
        (F3-read q (idG q) (pr w t)
          (cap-outr (F4 q R) (F3 q (idG q)) (pr w t) h'))
        where
        w≡a : w ≡ a
        w≡a = pr-inj {a = w} {b = t} {c = a} {d = pr b z} e₁ .fst
        t≡bz : t ≡ pr b z
        t≡bz = pr-inj {a = w} {b = t} {c = a} {d = pr b z} e₁ .snd
        fromId : Σ[ a₂ ∈ V ℓ ] Σ[ z₂ ∈ V ℓ ] Σ[ b₂ ∈ V ℓ ]
                   (⟨ z₂ ∈ˢ q ⟩ × ⟨ pr a₂ b₂ ∈ˢ idG q ⟩
                    × ⟨ pr w t ≡ₕ pr a₂ (pr z₂ b₂) ⟩)
               → ∥ D ∥₁
        fromId (a₂ , z₂ , b₂ , _ , id∈ , e₂) = PT.rec squash₁ same id-shape
          where
          w≡a₂ : w ≡ a₂
          w≡a₂ = pr-inj {a = w} {b = t} {c = a₂} {d = pr z₂ b₂} e₂ .fst
          t≡zb : t ≡ pr z₂ b₂
          t≡zb = pr-inj {a = w} {b = t} {c = a₂} {d = pr z₂ b₂} e₂ .snd
          id-shape : ∥ Σ[ x ∈ V ℓ ] (⟨ x ∈ˢ q ⟩ × ⟨ pr a₂ b₂ ≡ₕ pr x x ⟩) ∥₁
          id-shape = idG-out q (pr a₂ b₂) id∈
          same : Σ[ x ∈ V ℓ ] (⟨ x ∈ˢ q ⟩ × ⟨ pr a₂ b₂ ≡ₕ pr x x ⟩) → ∥ D ∥₁
          same (x , _ , e₃) = ∣ a , b , (ab∈ , t≡bw) ∣₁
            where
            a₂≡b₂ : a₂ ≡ b₂
            a₂≡b₂ = pr-inj {a = a₂} {b = b₂} {c = x} {d = x} e₃ .fst
                  ∙ sym (pr-inj {a = a₂} {b = b₂} {c = x} {d = x} e₃ .snd)
            z≡a : z ≡ a
            z≡a = pr-inj {a = b} {b = z} {c = z₂} {d = b₂}
                    (sym t≡bz ∙ t≡zb) .snd
                ∙ sym a₂≡b₂ ∙ sym w≡a₂ ∙ w≡a
            t≡bw : t ≡ pr b a
            t≡bw = t≡bz ∙ cong (pr b) z≡a
```

<!--en-->
## Flattening a relation

A graph carries values and an element relation carries members, and the step
from one to the other is the flattening: `⟨d, w⟩` lies in the flattening of
`R` when some `v` has `⟨d, v⟩ ∈ R` and `w ∈ v`. Both conditions are read off
the leading coordinate `v`, so both need the converse: the relation turned
around, and the membership relation turned around. The field of `R` is the
one ambient set both live in.
<!--zh-->
## 关系的摊平

图携带值，元素关系携带成员，从一者到另一者的一步就是摊平：`⟨d, w⟩` 属于 `R` 的摊平，意即存在 `v` 使 `⟨d, v⟩ ∈ R` 且 `w ∈ v`。两个条件都从首坐标 `v` 读出，故都需要逆：关系翻转过来，以及隶属关系翻转过来。`R` 的域是两者共同的那个环境集。
<!--/-->

```agda
opaque
  fld : V ℓ → V ℓ
  fld R = amb (cup (F6 R R) (ranOp R))

  fld-dom : (R d v : V ℓ) → ⟨ pr d v ∈ˢ R ⟩ → ⟨ d ∈ˢ fld R ⟩
  fld-dom R d v h = amb-self (cup (F6 R R) (ranOp R)) d
    (cup-in (F6 R R) (ranOp R) d
      ∣ inl (F6-write R R d ∣ d , v , (h , refl) ∣₁) ∣₁)

  fld-ran : (R d v : V ℓ) → ⟨ pr d v ∈ˢ R ⟩ → ⟨ v ∈ˢ fld R ⟩
  fld-ran R d v h = amb-self (cup (F6 R R) (ranOp R)) v
    (cup-in (F6 R R) (ranOp R) v ∣ inr (ran-in R d v h) ∣₁)

  fld-mem : (R d v w : V ℓ) → ⟨ pr d v ∈ˢ R ⟩ → ⟨ w ∈ˢ v ⟩ → ⟨ w ∈ˢ fld R ⟩
  fld-mem R d v w h w∈ = amb-mem (cup (F6 R R) (ranOp R)) v w
    (cup-in (F6 R R) (ranOp R) v ∣ inr (ran-in R d v h) ∣₁) w∈

opaque
  flat : V ℓ → V ℓ
  flat R = ranOp (cap (F4 (fld R) (swp R (fld R)))
                      (F3 (fld R) (swp (mrel (fld R)) (fld R))))

  flat-in : (R d v w : V ℓ) → ⟨ pr d v ∈ˢ R ⟩ → ⟨ w ∈ˢ v ⟩ → ⟨ pr d w ∈ˢ flat R ⟩
  flat-in R d v w h w∈ = ran-in
    (cap (F4 (fld R) (swp R (fld R))) (F3 (fld R) (swp (mrel (fld R)) (fld R))))
    v (pr d w)
    (cap-in (F4 (fld R) (swp R (fld R)))
            (F3 (fld R) (swp (mrel (fld R)) (fld R))) (pr v (pr d w)) c₁ c₂)
    where
    d∈ : ⟨ d ∈ˢ fld R ⟩
    d∈ = fld-dom R d v h
    v∈ : ⟨ v ∈ˢ fld R ⟩
    v∈ = fld-ran R d v h
    w∈f : ⟨ w ∈ˢ fld R ⟩
    w∈f = fld-mem R d v w h w∈
    c₁ : ⟨ pr v (pr d w) ∈ˢ F4 (fld R) (swp R (fld R)) ⟩
    c₁ = F4-write (fld R) (swp R (fld R)) (pr v (pr d w))
      ∣ v , d , w , (w∈f , swp-in R (fld R) d v h d∈ v∈ , refl) ∣₁
    c₂ : ⟨ pr v (pr d w) ∈ˢ F3 (fld R) (swp (mrel (fld R)) (fld R)) ⟩
    c₂ = F3-write (fld R) (swp (mrel (fld R)) (fld R)) (pr v (pr d w))
      ∣ v , d , w
      , ( d∈
        , swp-in (mrel (fld R)) (fld R) w v
            (mrel-in (fld R) w v w∈f v∈ w∈) w∈f v∈
        , refl ) ∣₁

  flat-out : (R t : V ℓ) → ⟨ t ∈ˢ flat R ⟩
           → ∥ Σ[ d ∈ V ℓ ] Σ[ v ∈ V ℓ ] Σ[ w ∈ V ℓ ]
                (⟨ pr d v ∈ˢ R ⟩ × ⟨ w ∈ˢ v ⟩ × ⟨ t ≡ₕ pr d w ⟩) ∥₁
  flat-out R t h = PT.rec squash₁ outer
    (ran-out (cap (F4 (fld R) (swp R (fld R)))
                  (F3 (fld R) (swp (mrel (fld R)) (fld R)))) t h)
    where
    D : Type (ℓ-suc ℓ)
    D = Σ[ d ∈ V ℓ ] Σ[ v ∈ V ℓ ] Σ[ w ∈ V ℓ ]
          (⟨ pr d v ∈ˢ R ⟩ × ⟨ w ∈ˢ v ⟩ × ⟨ t ≡ₕ pr d w ⟩)
    outer : Σ[ v₀ ∈ V ℓ ]
              ⟨ pr v₀ t ∈ˢ cap (F4 (fld R) (swp R (fld R)))
                               (F3 (fld R) (swp (mrel (fld R)) (fld R))) ⟩
          → ∥ D ∥₁
    outer (v₀ , h') = PT.rec squash₁ step₁
      (F4-read (fld R) (swp R (fld R)) (pr v₀ t)
        (cap-outl (F4 (fld R) (swp R (fld R)))
                  (F3 (fld R) (swp (mrel (fld R)) (fld R))) (pr v₀ t) h'))
      where
      step₁ : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] Σ[ z ∈ V ℓ ]
                (⟨ z ∈ˢ fld R ⟩ × ⟨ pr a b ∈ˢ swp R (fld R) ⟩
                 × ⟨ pr v₀ t ≡ₕ pr a (pr b z) ⟩)
            → ∥ D ∥₁
      step₁ (a , b , z , _ , ab∈ , e₁) = PT.rec squash₁ step₂
        (swp-out R (fld R) (pr a b) ab∈)
        where
        v₀≡a : v₀ ≡ a
        v₀≡a = pr-inj {a = v₀} {b = t} {c = a} {d = pr b z} e₁ .fst
        t≡bz : t ≡ pr b z
        t≡bz = pr-inj {a = v₀} {b = t} {c = a} {d = pr b z} e₁ .snd
        step₂ : Σ[ u' ∈ V ℓ ] Σ[ v' ∈ V ℓ ]
                  (⟨ pr u' v' ∈ˢ R ⟩ × ⟨ pr a b ≡ₕ pr v' u' ⟩)
              → ∥ D ∥₁
        step₂ (u' , v' , uv∈ , e₂) = PT.rec squash₁ step₃
          (F3-read (fld R) (swp (mrel (fld R)) (fld R)) (pr v₀ t)
            (cap-outr (F4 (fld R) (swp R (fld R)))
                      (F3 (fld R) (swp (mrel (fld R)) (fld R))) (pr v₀ t) h'))
          where
          ba∈R : ⟨ pr b a ∈ˢ R ⟩
          ba∈R = subst (λ s → ⟨ s ∈ˢ R ⟩)
            (cong₂ pr (sym (pr-inj {a = a} {b = b} {c = v'} {d = u'} e₂ .snd))
                      (sym (pr-inj {a = a} {b = b} {c = v'} {d = u'} e₂ .fst)))
            uv∈
          step₃ : Σ[ a₂ ∈ V ℓ ] Σ[ z₂ ∈ V ℓ ] Σ[ b₂ ∈ V ℓ ]
                    (⟨ z₂ ∈ˢ fld R ⟩
                     × ⟨ pr a₂ b₂ ∈ˢ swp (mrel (fld R)) (fld R) ⟩
                     × ⟨ pr v₀ t ≡ₕ pr a₂ (pr z₂ b₂) ⟩)
                → ∥ D ∥₁
          step₃ (a₂ , z₂ , b₂ , _ , mem∈ , e₃) = PT.rec squash₁ step₄
            (swp-out (mrel (fld R)) (fld R) (pr a₂ b₂) mem∈)
            where
            v₀≡a₂ : v₀ ≡ a₂
            v₀≡a₂ = pr-inj {a = v₀} {b = t} {c = a₂} {d = pr z₂ b₂} e₃ .fst
            t≡zb : t ≡ pr z₂ b₂
            t≡zb = pr-inj {a = v₀} {b = t} {c = a₂} {d = pr z₂ b₂} e₃ .snd
            z≡b₂ : z ≡ b₂
            z≡b₂ = pr-inj {a = b} {b = z} {c = z₂} {d = b₂}
              (sym t≡bz ∙ t≡zb) .snd
            step₄ : Σ[ u₃ ∈ V ℓ ] Σ[ v₃ ∈ V ℓ ]
                      (⟨ pr u₃ v₃ ∈ˢ mrel (fld R) ⟩ × ⟨ pr a₂ b₂ ≡ₕ pr v₃ u₃ ⟩)
                  → ∥ D ∥₁
            step₄ (u₃ , v₃ , m∈ , e₄) = ∣ b , a , z , (ba∈R , z∈a , t≡bz) ∣₁
              where
              b₂∈a₂ : ⟨ b₂ ∈ˢ a₂ ⟩
              b₂∈a₂ = subst (λ s → ⟨ s ∈ˢ a₂ ⟩)
                (sym (pr-inj {a = a₂} {b = b₂} {c = v₃} {d = u₃} e₄ .snd))
                (subst (λ s → ⟨ u₃ ∈ˢ s ⟩)
                  (sym (pr-inj {a = a₂} {b = b₂} {c = v₃} {d = u₃} e₄ .fst))
                  (mrel-out (fld R) u₃ v₃ m∈))
              z∈a : ⟨ z ∈ˢ a ⟩
              z∈a = subst (λ s → ⟨ z ∈ˢ s ⟩) (sym v₀≡a₂ ∙ v₀≡a)
                (subst (λ s → ⟨ s ∈ˢ a₂ ⟩) (sym z≡b₂) b₂∈a₂)
```

<!--en-->
## Composition, and the general read of a join

Two relations keyed on a common first coordinate compose to a relation between
their values: the join pairs the two values under the key, and the range
strips the key away. The general read of a join comes with it, since the
composition has to decompose an arbitrary member rather than one of a known
shape.
<!--zh-->
## 复合，以及接合的通用读取

共享首坐标的两个关系复合为它们的值之间的关系：接合把两个值配在键之下，值域再把键剥去。接合的通用读取随之而来，因为复合要拆解任意成员，而非某个已知形状的成员。
<!--/-->

```agda
opaque
  unfolding joinOp
  join-out : (R S Wr Ws t : V ℓ) → ⟨ t ∈ˢ joinOp R S Wr Ws ⟩
           → ∥ Σ[ d ∈ V ℓ ] Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ]
                (⟨ pr d u ∈ˢ R ⟩ × ⟨ pr d v ∈ˢ S ⟩ × ⟨ t ≡ₕ pr d (pr u v) ⟩) ∥₁
  join-out R S Wr Ws t h = PT.rec squash₁ go
    (F4-read Ws R t (cap-outl (F4 Ws R) (F3 Wr S) t h))
    where
    D : Type (ℓ-suc ℓ)
    D = Σ[ d ∈ V ℓ ] Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ]
          (⟨ pr d u ∈ˢ R ⟩ × ⟨ pr d v ∈ˢ S ⟩ × ⟨ t ≡ₕ pr d (pr u v) ⟩)
    go : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] Σ[ z ∈ V ℓ ]
           (⟨ z ∈ˢ Ws ⟩ × ⟨ pr a b ∈ˢ R ⟩ × ⟨ t ≡ₕ pr a (pr b z) ⟩)
       → ∥ D ∥₁
    go (a , b , z , _ , ab∈ , e) = ∣ a , b , z
      , ( ab∈
        , join-outr R S Wr Ws a b z
            (subst (λ x → ⟨ x ∈ˢ joinOp R S Wr Ws ⟩) e h)
        , e ) ∣₁

opaque
  comp : V ℓ → V ℓ → V ℓ → V ℓ → V ℓ
  comp R S Wr Ws = ranOp (joinOp R S Wr Ws)

  comp-in : (R S Wr Ws m u v : V ℓ) → ⟨ pr m u ∈ˢ R ⟩ → ⟨ pr m v ∈ˢ S ⟩
          → ⟨ u ∈ˢ Wr ⟩ → ⟨ v ∈ˢ Ws ⟩ → ⟨ pr u v ∈ˢ comp R S Wr Ws ⟩
  comp-in R S Wr Ws m u v hu hv u∈ v∈ = ran-in (joinOp R S Wr Ws) m (pr u v)
    (join-in R S Wr Ws m u v hu hv u∈ v∈)

  comp-out : (R S Wr Ws t : V ℓ) → ⟨ t ∈ˢ comp R S Wr Ws ⟩
           → ∥ Σ[ m ∈ V ℓ ] Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ]
                (⟨ pr m u ∈ˢ R ⟩ × ⟨ pr m v ∈ˢ S ⟩ × ⟨ t ≡ₕ pr u v ⟩) ∥₁
  comp-out R S Wr Ws t h = PT.rec squash₁ outer (ran-out (joinOp R S Wr Ws) t h)
    where
    D : Type (ℓ-suc ℓ)
    D = Σ[ m ∈ V ℓ ] Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ]
          (⟨ pr m u ∈ˢ R ⟩ × ⟨ pr m v ∈ˢ S ⟩ × ⟨ t ≡ₕ pr u v ⟩)
    outer : Σ[ m ∈ V ℓ ] ⟨ pr m t ∈ˢ joinOp R S Wr Ws ⟩ → ∥ D ∥₁
    outer (m , h') = PT.rec squash₁ inner (join-out R S Wr Ws (pr m t) h')
      where
      inner : Σ[ d ∈ V ℓ ] Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ]
                (⟨ pr d u ∈ˢ R ⟩ × ⟨ pr d v ∈ˢ S ⟩
                 × ⟨ pr m t ≡ₕ pr d (pr u v) ⟩)
            → ∥ D ∥₁
      inner (d , u , v , du , dv , e) = ∣ d , u , v
        , ( du , dv , pr-inj {a = m} {b = t} {c = d} {d = pr u v} e .snd ) ∣₁
```

<!--en-->
## The values of a relation

The slices of a relation over an index set are its values, and `F8` collects
them. Three readings are needed downstream: a slice at a member of the index
set is a value, a related member lies in the union of the values, and so does
a member of a value.
<!--zh-->
## 关系的值

关系在索引集上的各个切片就是它的值，`F8` 把它们收拢起来。下游需要三条读取：索引集成员处的切片是一个值，被关联的成员落在诸值之并中，值的成员亦然。
<!--/-->

```agda
opaque
  vals : V ℓ → V ℓ → V ℓ
  vals R D = F8 R D

  vals-slice : (R D d : V ℓ) → ⟨ d ∈ˢ D ⟩ → ⟨ F10 R d ∈ˢ vals R D ⟩
  vals-slice R D d d∈ = subst ⟨_⟩ (sym (F8-spec R D (F10 R d)))
    ∣ fib .fst , cong (F10 R) (fib .snd) ∣₁
    where
    fib : Σ[ m ∈ ⟪ D ⟫ ] (⟪ D ⟫↪ m ≡ d)
    fib = ∈-asFiber {a = d} {b = D} d∈

  vals-union : (R D d w : V ℓ) → ⟨ d ∈ˢ D ⟩ → ⟨ pr d w ∈ˢ R ⟩
             → ⟨ w ∈ˢ F5 (vals R D) (vals R D) ⟩
  vals-union R D d w d∈ h = F5-spec (vals R D) (vals R D) w .snd
    ∣ F10 R d , (vals-slice R D d d∈ , subst ⟨_⟩ (sym (F10-spec R d w)) h) ∣₁

  vals-mem : (R D v w : V ℓ) → ⟨ v ∈ˢ vals R D ⟩ → ⟨ w ∈ˢ v ⟩
           → ⟨ w ∈ˢ F5 (vals R D) (vals R D) ⟩
  vals-mem R D v w v∈ w∈ = F5-spec (vals R D) (vals R D) w .snd
    ∣ v , (v∈ , w∈) ∣₁
```

<!--en-->
## The slice graph

This is the step from an element relation back to a graph, and it is the
identity graph's proof shape at one coordinate more. A pair `⟨d, v⟩` is kept
when no member separates `v` from the slice of `R` at `d`: the two padded
relations on triples `⟨w, d, v⟩` say `w ∈ v` and `⟨d, w⟩ ∈ R`, their symmetric
difference is the separator set, and the graph is `D × vals` minus its range.
Both readings spend excluded middle once, exactly where the identity graph
does.
<!--zh-->
## 切片图

这是从元素关系回到图的一步，也就是恒等图的证明形状多加一个坐标。当没有成员把 `v` 与 `R` 在 `d` 处的切片分开时，对 `⟨d, v⟩` 被保留：三元组 `⟨w, d, v⟩` 上的两个加衬关系分别说 `w ∈ v` 与 `⟨d, w⟩ ∈ R`，其对称差是分离集，图即 `D × vals` 减去它的值域。两条读取各花掉一次排中律，恰在恒等图花掉的同一处。
<!--/-->

```agda
opaque
  sgQ : V ℓ → V ℓ → V ℓ
  sgQ R D = cup (cup D (F5 (vals R D) (vals R D))) (vals R D)

  q-D : (R D d : V ℓ) → ⟨ d ∈ˢ D ⟩ → ⟨ d ∈ˢ sgQ R D ⟩
  q-D R D d h = cup-in (cup D (F5 (vals R D) (vals R D))) (vals R D) d
    ∣ inl (cup-in D (F5 (vals R D) (vals R D)) d ∣ inl h ∣₁) ∣₁

  q-W : (R D w : V ℓ) → ⟨ w ∈ˢ F5 (vals R D) (vals R D) ⟩ → ⟨ w ∈ˢ sgQ R D ⟩
  q-W R D w h = cup-in (cup D (F5 (vals R D) (vals R D))) (vals R D) w
    ∣ inl (cup-in D (F5 (vals R D) (vals R D)) w ∣ inr h ∣₁) ∣₁

  q-B : (R D v : V ℓ) → ⟨ v ∈ˢ vals R D ⟩ → ⟨ v ∈ˢ sgQ R D ⟩
  q-B R D v h = cup-in (cup D (F5 (vals R D) (vals R D))) (vals R D) v
    ∣ inr h ∣₁

opaque
  sgT : V ℓ → V ℓ → V ℓ
  sgT R D = F2 (F5 (vals R D) (vals R D)) (F2 D (vals R D))

  sgT-in : (R D w d v : V ℓ) → ⟨ w ∈ˢ F5 (vals R D) (vals R D) ⟩
         → ⟨ d ∈ˢ D ⟩ → ⟨ v ∈ˢ vals R D ⟩ → ⟨ pr w (pr d v) ∈ˢ sgT R D ⟩
  sgT-in R D w d v hw hd hv =
    F2-write (F5 (vals R D) (vals R D)) (F2 D (vals R D)) (pr w (pr d v))
      ∣ w , pr d v
      , ( hw , F2-write D (vals R D) (pr d v) ∣ d , v , (hd , hv , refl) ∣₁
        , refl ) ∣₁

opaque
  sgL : V ℓ → V ℓ → V ℓ
  sgL R D = cap (F3 D (mrel (sgQ R D))) (sgT R D)

  sgR : V ℓ → V ℓ → V ℓ
  sgR R D = cap (F4 (vals R D) (swp R (sgQ R D))) (sgT R D)

  sgL-in : (R D w d v : V ℓ) → ⟨ w ∈ˢ v ⟩ → ⟨ d ∈ˢ D ⟩ → ⟨ v ∈ˢ vals R D ⟩
         → ⟨ pr w (pr d v) ∈ˢ sgL R D ⟩
  sgL-in R D w d v w∈v hd hv =
    cap-in (F3 D (mrel (sgQ R D))) (sgT R D) (pr w (pr d v))
      (F3-write D (mrel (sgQ R D)) (pr w (pr d v))
        ∣ w , d , v
        , ( hd
          , mrel-in (sgQ R D) w v (q-W R D w hw) (q-B R D v hv) w∈v
          , refl ) ∣₁)
      (sgT-in R D w d v hw hd hv)
    where
    hw : ⟨ w ∈ˢ F5 (vals R D) (vals R D) ⟩
    hw = vals-mem R D v w hv w∈v

  sgR-in : (R D w d v : V ℓ) → ⟨ pr d w ∈ˢ R ⟩ → ⟨ d ∈ˢ D ⟩ → ⟨ v ∈ˢ vals R D ⟩
         → ⟨ pr w (pr d v) ∈ˢ sgR R D ⟩
  sgR-in R D w d v dw∈ hd hv =
    cap-in (F4 (vals R D) (swp R (sgQ R D))) (sgT R D) (pr w (pr d v))
      (F4-write (vals R D) (swp R (sgQ R D)) (pr w (pr d v))
        ∣ w , d , v
        , ( hv
          , swp-in R (sgQ R D) d w dw∈ (q-D R D d hd) (q-W R D w hw)
          , refl ) ∣₁)
      (sgT-in R D w d v hw hd hv)
    where
    hw : ⟨ w ∈ˢ F5 (vals R D) (vals R D) ⟩
    hw = vals-union R D d w hd dw∈

  sgL-out : (R D w d v : V ℓ) → ⟨ pr w (pr d v) ∈ˢ sgL R D ⟩ → ⟨ w ∈ˢ v ⟩
  sgL-out R D w d v h = PT.rec (snd (w ∈ˢ v)) go
    (F3-read D (mrel (sgQ R D)) (pr w (pr d v))
      (cap-outl (F3 D (mrel (sgQ R D))) (sgT R D) (pr w (pr d v)) h))
    where
    go : Σ[ u ∈ V ℓ ] Σ[ z ∈ V ℓ ] Σ[ y ∈ V ℓ ]
           (⟨ z ∈ˢ D ⟩ × ⟨ pr u y ∈ˢ mrel (sgQ R D) ⟩
            × ⟨ pr w (pr d v) ≡ₕ pr u (pr z y) ⟩)
       → ⟨ w ∈ˢ v ⟩
    go (u , z , y , _ , m∈ , e) =
      subst (λ x → ⟨ x ∈ˢ v ⟩) (sym w≡u)
        (subst (λ x → ⟨ u ∈ˢ x ⟩) (sym v≡y) (mrel-out (sgQ R D) u y m∈))
      where
      w≡u : w ≡ u
      w≡u = pr-inj {a = w} {b = pr d v} {c = u} {d = pr z y} e .fst
      v≡y : v ≡ y
      v≡y = pr-inj {a = d} {b = v} {c = z} {d = y}
        (pr-inj {a = w} {b = pr d v} {c = u} {d = pr z y} e .snd) .snd

  sgR-out : (R D w d v : V ℓ) → ⟨ pr w (pr d v) ∈ˢ sgR R D ⟩ → ⟨ pr d w ∈ˢ R ⟩
  sgR-out R D w d v h = PT.rec (snd (pr d w ∈ˢ R)) go
    (F4-read (vals R D) (swp R (sgQ R D)) (pr w (pr d v))
      (cap-outl (F4 (vals R D) (swp R (sgQ R D))) (sgT R D) (pr w (pr d v)) h))
    where
    go : Σ[ u ∈ V ℓ ] Σ[ y ∈ V ℓ ] Σ[ z ∈ V ℓ ]
           (⟨ z ∈ˢ vals R D ⟩ × ⟨ pr u y ∈ˢ swp R (sgQ R D) ⟩
            × ⟨ pr w (pr d v) ≡ₕ pr u (pr y z) ⟩)
       → ⟨ pr d w ∈ˢ R ⟩
    go (u , y , z , _ , sw∈ , e) = PT.rec (snd (pr d w ∈ˢ R)) inner
      (swp-out R (sgQ R D) (pr u y) sw∈)
      where
      w≡u : w ≡ u
      w≡u = pr-inj {a = w} {b = pr d v} {c = u} {d = pr y z} e .fst
      d≡y : d ≡ y
      d≡y = pr-inj {a = d} {b = v} {c = y} {d = z}
        (pr-inj {a = w} {b = pr d v} {c = u} {d = pr y z} e .snd) .fst
      inner : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
                (⟨ pr a b ∈ˢ R ⟩ × ⟨ pr u y ≡ₕ pr b a ⟩) → ⟨ pr d w ∈ˢ R ⟩
      inner (a , b , ab∈ , e₂) = subst (λ x → ⟨ x ∈ˢ R ⟩)
        (cong₂ pr (sym (d≡y ∙ pr-inj {a = u} {b = y} {c = b} {d = a} e₂ .snd))
                  (sym (w≡u ∙ pr-inj {a = u} {b = y} {c = b} {d = a} e₂ .fst)))
        ab∈

opaque
  sgBad : V ℓ → V ℓ → V ℓ
  sgBad R D = cup (ranOp (F1 (sgL R D) (sgR R D)))
                  (ranOp (F1 (sgR R D) (sgL R D)))

  sgBad-inl : (R D w t : V ℓ) → ⟨ pr w t ∈ˢ sgL R D ⟩
            → (⟨ pr w t ∈ˢ sgR R D ⟩ → Empty.⊥) → ⟨ t ∈ˢ sgBad R D ⟩
  sgBad-inl R D w t h₁ h₂ =
    cup-in (ranOp (F1 (sgL R D) (sgR R D))) (ranOp (F1 (sgR R D) (sgL R D))) t
      ∣ inl (ran-in (F1 (sgL R D) (sgR R D)) w t
        (F1-spec (sgL R D) (sgR R D) (pr w t) .snd (h₁ , h₂))) ∣₁

  sgBad-inr : (R D w t : V ℓ) → ⟨ pr w t ∈ˢ sgR R D ⟩
            → (⟨ pr w t ∈ˢ sgL R D ⟩ → Empty.⊥) → ⟨ t ∈ˢ sgBad R D ⟩
  sgBad-inr R D w t h₁ h₂ =
    cup-in (ranOp (F1 (sgL R D) (sgR R D))) (ranOp (F1 (sgR R D) (sgL R D))) t
      ∣ inr (ran-in (F1 (sgR R D) (sgL R D)) w t
        (F1-spec (sgR R D) (sgL R D) (pr w t) .snd (h₁ , h₂))) ∣₁

  sgBad-out : (R D t : V ℓ) → ⟨ t ∈ˢ sgBad R D ⟩
            → ∥ Σ[ w ∈ V ℓ ]
                 ( (⟨ pr w t ∈ˢ sgL R D ⟩ × (⟨ pr w t ∈ˢ sgR R D ⟩ → Empty.⊥))
                 ⊎ (⟨ pr w t ∈ˢ sgR R D ⟩ × (⟨ pr w t ∈ˢ sgL R D ⟩ → Empty.⊥)) )
               ∥₁
  sgBad-out R D t h = PT.rec squash₁ sides
    (cup-out (ranOp (F1 (sgL R D) (sgR R D)))
             (ranOp (F1 (sgR R D) (sgL R D))) t h)
    where
    E : Type (ℓ-suc ℓ)
    E = Σ[ w ∈ V ℓ ]
          ( (⟨ pr w t ∈ˢ sgL R D ⟩ × (⟨ pr w t ∈ˢ sgR R D ⟩ → Empty.⊥))
          ⊎ (⟨ pr w t ∈ˢ sgR R D ⟩ × (⟨ pr w t ∈ˢ sgL R D ⟩ → Empty.⊥)) )
    sides : (⟨ t ∈ˢ ranOp (F1 (sgL R D) (sgR R D)) ⟩
             ⊎ ⟨ t ∈ˢ ranOp (F1 (sgR R D) (sgL R D)) ⟩) → ∥ E ∥₁
    sides (inl k) = PT.rec squash₁
      (λ { (w , k') → ∣ w , inl (F1-spec (sgL R D) (sgR R D) (pr w t) .fst k') ∣₁ })
      (ran-out (F1 (sgL R D) (sgR R D)) t k)
    sides (inr k) = PT.rec squash₁
      (λ { (w , k') → ∣ w , inr (F1-spec (sgR R D) (sgL R D) (pr w t) .fst k') ∣₁ })
      (ran-out (F1 (sgR R D) (sgL R D)) t k)

opaque
  sgraph : V ℓ → V ℓ → V ℓ
  sgraph R D = F1 (F2 D (vals R D)) (sgBad R D)

  sgraph-in : (R D d v : V ℓ) → ⟨ d ∈ˢ D ⟩ → ⟨ v ∈ˢ vals R D ⟩
            → ((w : V ℓ) → ⟨ w ∈ˢ v ⟩ → ⟨ pr d w ∈ˢ R ⟩)
            → ((w : V ℓ) → ⟨ pr d w ∈ˢ R ⟩ → ⟨ w ∈ˢ v ⟩)
            → ⟨ pr d v ∈ˢ sgraph R D ⟩
  sgraph-in R D d v hd hv h₁ h₂ =
    F1-spec (F2 D (vals R D)) (sgBad R D) (pr d v) .snd
      ( F2-write D (vals R D) (pr d v) ∣ d , v , (hd , hv , refl) ∣₁ , noBad )
    where
    noBad : ⟨ pr d v ∈ˢ sgBad R D ⟩ → Empty.⊥
    noBad bad = PT.rec Empty.isProp⊥ go (sgBad-out R D (pr d v) bad)
      where
      go : Σ[ w ∈ V ℓ ]
             ( (⟨ pr w (pr d v) ∈ˢ sgL R D ⟩
                × (⟨ pr w (pr d v) ∈ˢ sgR R D ⟩ → Empty.⊥))
             ⊎ (⟨ pr w (pr d v) ∈ˢ sgR R D ⟩
                × (⟨ pr w (pr d v) ∈ˢ sgL R D ⟩ → Empty.⊥)) )
         → Empty.⊥
      go (w , inl (k , nk)) = nk
        (sgR-in R D w d v (h₁ w (sgL-out R D w d v k)) hd hv)
      go (w , inr (k , nk)) = nk
        (sgL-in R D w d v (h₂ w (sgR-out R D w d v k)) hd hv)

  sgraph-outl : (R D d v : V ℓ) → ⟨ d ∈ˢ D ⟩ → ⟨ v ∈ˢ vals R D ⟩
              → ⟨ pr d v ∈ˢ sgraph R D ⟩
              → (w : V ℓ) → ⟨ w ∈ˢ v ⟩ → ⟨ pr d w ∈ˢ R ⟩
  sgraph-outl R D d v hd hv h w w∈v = ∈S (pr d w) R
    (dne (pr d w ∈ₛ R) (λ n →
      F1-spec (F2 D (vals R D)) (sgBad R D) (pr d v) .fst h .snd
        (sgBad-inl R D w (pr d v) (sgL-in R D w d v w∈v hd hv)
          (λ k → n (∈s (pr d w) R (sgR-out R D w d v k))))))

  sgraph-outr : (R D d v : V ℓ) → ⟨ d ∈ˢ D ⟩ → ⟨ v ∈ˢ vals R D ⟩
              → ⟨ pr d v ∈ˢ sgraph R D ⟩
              → (w : V ℓ) → ⟨ pr d w ∈ˢ R ⟩ → ⟨ w ∈ˢ v ⟩
  sgraph-outr R D d v hd hv h w dw∈ = ∈S w v
    (dne (w ∈ₛ v) (λ n →
      F1-spec (F2 D (vals R D)) (sgBad R D) (pr d v) .fst h .snd
        (sgBad-inr R D w (pr d v) (sgR-in R D w d v dw∈ hd hv)
          (λ k → n (∈s w v (sgL-out R D w d v k))))))

  sgraph-shape : (R D t : V ℓ) → ⟨ t ∈ˢ sgraph R D ⟩
               → ∥ Σ[ d ∈ V ℓ ] Σ[ v ∈ V ℓ ]
                    (⟨ d ∈ˢ D ⟩ × ⟨ v ∈ˢ vals R D ⟩ × ⟨ t ≡ₕ pr d v ⟩) ∥₁
  sgraph-shape R D t h = F2-read D (vals R D) t
    (F1-spec (F2 D (vals R D)) (sgBad R D) t .fst h .fst)
```

<!--en-->
## The projection graphs

A set of pairs carries two projections, and the nested image needs both as
relations. Neither is a padding, but both are one intersection away: the
triple `⟨d, d, t⟩` whose first two coordinates agree is a padding of the set
of pairs met with a padding of the identity graph, and read as a pair it is
`⟨d, ⟨d, t⟩⟩`, the converse of the left projection. The right projection is
the same construction over the converse of the set. The identity graph pays
for both, and the converse turns them the right way round.
<!--zh-->
## 投影图

一个对集带有两个投影，嵌套的像两个都要，且要它们作为关系。二者都不是加衬，但都只差一次取交：前两个坐标相同的三元组 `⟨d, d, t⟩` 是该对集的一次加衬与恒等图的一次加衬之交，读作对便是 `⟨d, ⟨d, t⟩⟩`，即左投影之逆。右投影是同一构造施于该集之逆。恒等图为二者买单，取逆再把它们转到正确的方向。
<!--/-->

```agda
opaque
  lpg : V ℓ → V ℓ → V ℓ
  lpg P X = cap (F3 X P) (F4 X (idG X))

  rpg : V ℓ → V ℓ → V ℓ
  rpg P X = cap (F4 X (swp P X)) (F3 X (idG X))

  lpg-in : (P X d t : V ℓ) → ⟨ pr d t ∈ˢ P ⟩ → ⟨ d ∈ˢ X ⟩ → ⟨ t ∈ˢ X ⟩
         → ⟨ pr d (pr d t) ∈ˢ lpg P X ⟩
  lpg-in P X d t dt∈ d∈ t∈ = cap-in (F3 X P) (F4 X (idG X)) (pr d (pr d t))
    (F3-write X P (pr d (pr d t)) ∣ d , d , t , (d∈ , dt∈ , refl) ∣₁)
    (F4-write X (idG X) (pr d (pr d t))
      ∣ d , d , t , (t∈ , idG-in X d d∈ , refl) ∣₁)

  rpg-in : (P X d t : V ℓ) → ⟨ pr d t ∈ˢ P ⟩ → ⟨ d ∈ˢ X ⟩ → ⟨ t ∈ˢ X ⟩
         → ⟨ pr t (pr d t) ∈ˢ rpg P X ⟩
  rpg-in P X d t dt∈ d∈ t∈ =
    cap-in (F4 X (swp P X)) (F3 X (idG X)) (pr t (pr d t))
      (F4-write X (swp P X) (pr t (pr d t))
        ∣ t , d , t , (t∈ , swp-in P X d t dt∈ d∈ t∈ , refl) ∣₁)
      (F3-write X (idG X) (pr t (pr d t))
        ∣ t , d , t , (d∈ , idG-in X t t∈ , refl) ∣₁)

  lpg-out : (P X a b : V ℓ) → ⟨ pr a b ∈ˢ lpg P X ⟩
          → ∥ Σ[ t ∈ V ℓ ] (⟨ pr a t ∈ˢ P ⟩ × ⟨ b ≡ₕ pr a t ⟩) ∥₁
  lpg-out P X a b h = PT.rec squash₁ fromP
    (F3-read X P (pr a b) (cap-outl (F3 X P) (F4 X (idG X)) (pr a b) h))
    where
    E : Type (ℓ-suc ℓ)
    E = Σ[ t ∈ V ℓ ] (⟨ pr a t ∈ˢ P ⟩ × ⟨ b ≡ₕ pr a t ⟩)
    fromP : Σ[ u ∈ V ℓ ] Σ[ z ∈ V ℓ ] Σ[ v ∈ V ℓ ]
              (⟨ z ∈ˢ X ⟩ × ⟨ pr u v ∈ˢ P ⟩ × ⟨ pr a b ≡ₕ pr u (pr z v) ⟩)
          → ∥ E ∥₁
    fromP (u , z , v , _ , uv∈ , e₁) = PT.rec squash₁ fromId
      (F4-read X (idG X) (pr a b)
        (cap-outr (F3 X P) (F4 X (idG X)) (pr a b) h))
      where
      a≡u : a ≡ u
      a≡u = pr-inj {a = a} {b = b} {c = u} {d = pr z v} e₁ .fst
      b≡zv : b ≡ pr z v
      b≡zv = pr-inj {a = a} {b = b} {c = u} {d = pr z v} e₁ .snd
      fromId : Σ[ u' ∈ V ℓ ] Σ[ v' ∈ V ℓ ] Σ[ z' ∈ V ℓ ]
                 (⟨ z' ∈ˢ X ⟩ × ⟨ pr u' v' ∈ˢ idG X ⟩
                  × ⟨ pr a b ≡ₕ pr u' (pr v' z') ⟩)
             → ∥ E ∥₁
      fromId (u' , v' , z' , _ , id∈ , e₂) = PT.rec squash₁ same
        (idG-out X (pr u' v') id∈)
        where
        a≡u' : a ≡ u'
        a≡u' = pr-inj {a = a} {b = b} {c = u'} {d = pr v' z'} e₂ .fst
        b≡vz : b ≡ pr v' z'
        b≡vz = pr-inj {a = a} {b = b} {c = u'} {d = pr v' z'} e₂ .snd
        same : Σ[ x ∈ V ℓ ] (⟨ x ∈ˢ X ⟩ × ⟨ pr u' v' ≡ₕ pr x x ⟩) → ∥ E ∥₁
        same (x , _ , e₃) = ∣ v , (subst (λ y → ⟨ y ∈ˢ P ⟩) (sym pa) uv∈
                                 , b≡zv ∙ cong (λ y → pr y v) z≡a) ∣₁
          where
          u'≡v' : u' ≡ v'
          u'≡v' = pr-inj {a = u'} {b = v'} {c = x} {d = x} e₃ .fst
                ∙ sym (pr-inj {a = u'} {b = v'} {c = x} {d = x} e₃ .snd)
          z≡a : z ≡ a
          z≡a = pr-inj {a = z} {b = v} {c = v'} {d = z'} (sym b≡zv ∙ b≡vz) .fst
              ∙ sym u'≡v' ∙ sym a≡u'
          pa : pr a v ≡ pr u v
          pa = cong (λ y → pr y v) a≡u

  rpg-out : (P X a b : V ℓ) → ⟨ pr a b ∈ˢ rpg P X ⟩
          → ∥ Σ[ d ∈ V ℓ ] (⟨ pr d a ∈ˢ P ⟩ × ⟨ b ≡ₕ pr d a ⟩) ∥₁
  rpg-out P X a b h = PT.rec squash₁ fromP
    (F4-read X (swp P X) (pr a b)
      (cap-outl (F4 X (swp P X)) (F3 X (idG X)) (pr a b) h))
    where
    E : Type (ℓ-suc ℓ)
    E = Σ[ d ∈ V ℓ ] (⟨ pr d a ∈ˢ P ⟩ × ⟨ b ≡ₕ pr d a ⟩)
    fromP : Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ] Σ[ z ∈ V ℓ ]
              (⟨ z ∈ˢ X ⟩ × ⟨ pr u v ∈ˢ swp P X ⟩ × ⟨ pr a b ≡ₕ pr u (pr v z) ⟩)
          → ∥ E ∥₁
    fromP (u , v , z , _ , sw∈ , e₁) = PT.rec squash₁ fromSwp
      (swp-out P X (pr u v) sw∈)
      where
      a≡u : a ≡ u
      a≡u = pr-inj {a = a} {b = b} {c = u} {d = pr v z} e₁ .fst
      b≡vz : b ≡ pr v z
      b≡vz = pr-inj {a = a} {b = b} {c = u} {d = pr v z} e₁ .snd
      fromSwp : Σ[ d' ∈ V ℓ ] Σ[ t' ∈ V ℓ ]
                  (⟨ pr d' t' ∈ˢ P ⟩ × ⟨ pr u v ≡ₕ pr t' d' ⟩) → ∥ E ∥₁
      fromSwp (d' , t' , dt∈ , e₂) = PT.rec squash₁ fromId
        (F3-read X (idG X) (pr a b)
          (cap-outr (F4 X (swp P X)) (F3 X (idG X)) (pr a b) h))
        where
        u≡t' : u ≡ t'
        u≡t' = pr-inj {a = u} {b = v} {c = t'} {d = d'} e₂ .fst
        v≡d' : v ≡ d'
        v≡d' = pr-inj {a = u} {b = v} {c = t'} {d = d'} e₂ .snd
        fromId : Σ[ u' ∈ V ℓ ] Σ[ z' ∈ V ℓ ] Σ[ v' ∈ V ℓ ]
                   (⟨ z' ∈ˢ X ⟩ × ⟨ pr u' v' ∈ˢ idG X ⟩
                    × ⟨ pr a b ≡ₕ pr u' (pr z' v') ⟩)
               → ∥ E ∥₁
        fromId (u' , z' , v' , _ , id∈ , e₃) = PT.rec squash₁ same
          (idG-out X (pr u' v') id∈)
          where
          a≡u' : a ≡ u'
          a≡u' = pr-inj {a = a} {b = b} {c = u'} {d = pr z' v'} e₃ .fst
          b≡zv : b ≡ pr z' v'
          b≡zv = pr-inj {a = a} {b = b} {c = u'} {d = pr z' v'} e₃ .snd
          same : Σ[ x ∈ V ℓ ] (⟨ x ∈ˢ X ⟩ × ⟨ pr u' v' ≡ₕ pr x x ⟩) → ∥ E ∥₁
          same (x , _ , e₄) = ∣ d' , (dt∈' , b≡da) ∣₁
            where
            u'≡v' : u' ≡ v'
            u'≡v' = pr-inj {a = u'} {b = v'} {c = x} {d = x} e₄ .fst
                  ∙ sym (pr-inj {a = u'} {b = v'} {c = x} {d = x} e₄ .snd)
            z≡a : z ≡ a
            z≡a = pr-inj {a = v} {b = z} {c = z'} {d = v'}
                    (sym b≡vz ∙ b≡zv) .snd
                ∙ sym u'≡v' ∙ sym a≡u'
            dt∈' : ⟨ pr d' a ∈ˢ P ⟩
            dt∈' = subst (λ y → ⟨ pr d' y ∈ˢ P ⟩) (sym u≡t' ∙ sym a≡u) dt∈
            b≡da : b ≡ pr d' a
            b≡da = b≡vz ∙ cong₂ pr v≡d' z≡a

opaque
  lproj : V ℓ → V ℓ → V ℓ
  lproj P X = swp (lpg P X) (cup X P)

  rproj : V ℓ → V ℓ → V ℓ
  rproj P X = swp (rpg P X) (cup X P)

  lproj-in : (P X d t : V ℓ) → ⟨ pr d t ∈ˢ P ⟩ → ⟨ d ∈ˢ X ⟩ → ⟨ t ∈ˢ X ⟩
           → ⟨ pr (pr d t) d ∈ˢ lproj P X ⟩
  lproj-in P X d t dt∈ d∈ t∈ = swp-in (lpg P X) (cup X P) d (pr d t)
    (lpg-in P X d t dt∈ d∈ t∈)
    (cup-in X P d ∣ inl d∈ ∣₁) (cup-in X P (pr d t) ∣ inr dt∈ ∣₁)

  rproj-in : (P X d t : V ℓ) → ⟨ pr d t ∈ˢ P ⟩ → ⟨ d ∈ˢ X ⟩ → ⟨ t ∈ˢ X ⟩
           → ⟨ pr (pr d t) t ∈ˢ rproj P X ⟩
  rproj-in P X d t dt∈ d∈ t∈ = swp-in (rpg P X) (cup X P) t (pr d t)
    (rpg-in P X d t dt∈ d∈ t∈)
    (cup-in X P t ∣ inl t∈ ∣₁) (cup-in X P (pr d t) ∣ inr dt∈ ∣₁)

  lproj-out : (P X e d : V ℓ) → ⟨ pr e d ∈ˢ lproj P X ⟩
            → ∥ Σ[ t ∈ V ℓ ] (⟨ pr d t ∈ˢ P ⟩ × ⟨ e ≡ₕ pr d t ⟩) ∥₁
  lproj-out P X e d h = PT.rec squash₁ go (swp-out (lpg P X) (cup X P) (pr e d) h)
    where
    E : Type (ℓ-suc ℓ)
    E = Σ[ t ∈ V ℓ ] (⟨ pr d t ∈ˢ P ⟩ × ⟨ e ≡ₕ pr d t ⟩)
    go : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
           (⟨ pr a b ∈ˢ lpg P X ⟩ × ⟨ pr e d ≡ₕ pr b a ⟩) → ∥ E ∥₁
    go (a , b , ab∈ , e₁) = PT.rec squash₁ inner (lpg-out P X a b ab∈)
      where
      e≡b : e ≡ b
      e≡b = pr-inj {a = e} {b = d} {c = b} {d = a} e₁ .fst
      d≡a : d ≡ a
      d≡a = pr-inj {a = e} {b = d} {c = b} {d = a} e₁ .snd
      inner : Σ[ t ∈ V ℓ ] (⟨ pr a t ∈ˢ P ⟩ × ⟨ b ≡ₕ pr a t ⟩) → ∥ E ∥₁
      inner (t , at∈ , e₂) = ∣ t
        , ( subst (λ y → ⟨ pr y t ∈ˢ P ⟩) (sym d≡a) at∈
          , e≡b ∙ e₂ ∙ cong (λ y → pr y t) (sym d≡a) ) ∣₁

  rproj-out : (P X e t : V ℓ) → ⟨ pr e t ∈ˢ rproj P X ⟩
            → ∥ Σ[ d ∈ V ℓ ] (⟨ pr d t ∈ˢ P ⟩ × ⟨ e ≡ₕ pr d t ⟩) ∥₁
  rproj-out P X e t h = PT.rec squash₁ go (swp-out (rpg P X) (cup X P) (pr e t) h)
    where
    E : Type (ℓ-suc ℓ)
    E = Σ[ d ∈ V ℓ ] (⟨ pr d t ∈ˢ P ⟩ × ⟨ e ≡ₕ pr d t ⟩)
    go : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
           (⟨ pr a b ∈ˢ rpg P X ⟩ × ⟨ pr e t ≡ₕ pr b a ⟩) → ∥ E ∥₁
    go (a , b , ab∈ , e₁) = PT.rec squash₁ inner (rpg-out P X a b ab∈)
      where
      e≡b : e ≡ b
      e≡b = pr-inj {a = e} {b = t} {c = b} {d = a} e₁ .fst
      t≡a : t ≡ a
      t≡a = pr-inj {a = e} {b = t} {c = b} {d = a} e₁ .snd
      inner : Σ[ d ∈ V ℓ ] (⟨ pr d a ∈ˢ P ⟩ × ⟨ b ≡ₕ pr d a ⟩) → ∥ E ∥₁
      inner (d , da∈ , e₂) = ∣ d
        , ( subst (λ y → ⟨ pr d y ∈ˢ P ⟩) (sym t≡a) da∈
          , e≡b ∙ e₂ ∙ cong (pr d) (sym t≡a) ) ∣₁
```

<!--en-->
## Everything lands in a closed level

The constructions above are chains of basis functions and nothing else, so a
set closed under the sixteen functions contains every one of them. The
closure lemmas below are one per construction, each in its own unfolding
block, each reading the chain off the definition the seal hides. The eight
wrappers the switch chapter already carries are reused; the three the graph
calculus adds are `F3`, `F4` and the collection `F8`.
<!--zh-->
## 一切都落在封闭层内

上面的构造无非是基函数之链，故对十六个函数封闭的集合含有其中每一个。下面的封闭引理每个构造一条，各在自己的解封块中，各自从封印所藏的定义读出那条链。切换章已携带的八个包装器在此复用；图演算新增的三个是 `F3`、`F4` 与收集 `F8`。
<!--/-->

```agda
module Kit (J : V ℓ)
  (Jrud : (i : Op16) (a b : V ℓ) → ⟨ a ∈ˢ J ⟩ → ⟨ b ∈ˢ J ⟩ → ⟨ Fof i a b ∈ˢ J ⟩)
  where

  open Closure J Jrud public

  J-F3 : (a b : V ℓ) → InJ a → InJ b → InJ (F3 a b)
  J-F3 a b ha hb = subst InJ (Fof-f3 a b) (Jrud f3 a b ha hb)

  J-F4 : (a b : V ℓ) → InJ a → InJ b → InJ (F4 a b)
  J-F4 a b ha hb = subst InJ (Fof-f4 a b) (Jrud f4 a b ha hb)

  J-F8 : (a b : V ℓ) → InJ a → InJ b → InJ (F8 a b)
  J-F8 a b ha hb = subst InJ (Fof-f8 a b) (Jrud f8 a b ha hb)

  opaque
    unfolding cup
    J-cup : (a b : V ℓ) → InJ a → InJ b → InJ (cup a b)
    J-cup a b ha hb = J-F5 (F0 a b) (F0 a b) h₀ h₀
      where
      h₀ : InJ (F0 a b)
      h₀ = J-F0 a b ha hb

  opaque
    unfolding cap
    J-cap : (a b : V ℓ) → InJ a → InJ b → InJ (cap a b)
    J-cap a b ha hb = J-F1 a (F1 a b) ha (J-F1 a b ha hb)

  opaque
    unfolding ranOp
    J-ran : (R : V ℓ) → InJ R → InJ (ranOp R)
    J-ran R hR = J-F5 (F8 R (F6 R R)) (F8 R (F6 R R)) h₈ h₈
      where
      h₈ : InJ (F8 R (F6 R R))
      h₈ = J-F8 R (F6 R R) hR (J-F6 R R hR hR)

  opaque
    unfolding amb
    J-amb : (p : V ℓ) → InJ p → InJ (amb p)
    J-amb p hp = J-cup p (F5 p p) hp (J-F5 p p hp hp)

  opaque
    unfolding mrel
    J-mrel : (q : V ℓ) → InJ q → InJ (mrel q)
    J-mrel q hq = J-F7 q q hq hq

  opaque
    unfolding tsp
    J-tsp : (p : V ℓ) → InJ p → InJ (tsp p)
    J-tsp p hp = J-F2 (amb p) (F2 p p) (J-amb p hp) (J-F2 p p hp hp)

  opaque
    unfolding lft rgt
    J-lft : (p : V ℓ) → InJ p → InJ (lft p)
    J-lft p hp = J-cap (F4 p (mrel (amb p))) (tsp p)
      (J-F4 p (mrel (amb p)) hp (J-mrel (amb p) (J-amb p hp))) (J-tsp p hp)

    J-rgt : (p : V ℓ) → InJ p → InJ (rgt p)
    J-rgt p hp = J-cap (F3 p (mrel (amb p))) (tsp p)
      (J-F3 p (mrel (amb p)) hp (J-mrel (amb p) (J-amb p hp))) (J-tsp p hp)

  opaque
    unfolding wit neq
    J-neq : (p : V ℓ) → InJ p → InJ (neq p)
    J-neq p hp = J-ran (cup (F1 (lft p) (rgt p)) (F1 (rgt p) (lft p)))
      (J-cup (F1 (lft p) (rgt p)) (F1 (rgt p) (lft p))
        (J-F1 (lft p) (rgt p) (J-lft p hp) (J-rgt p hp))
        (J-F1 (rgt p) (lft p) (J-rgt p hp) (J-lft p hp)))

  opaque
    unfolding idG
    J-idG : (p : V ℓ) → InJ p → InJ (idG p)
    J-idG p hp = J-F1 (F2 p p) (neq p) (J-F2 p p hp hp) (J-neq p hp)

  opaque
    unfolding joinOp
    J-join : (R S Wr Ws : V ℓ) → InJ R → InJ S → InJ Wr → InJ Ws
           → InJ (joinOp R S Wr Ws)
    J-join R S Wr Ws hR hS hr hs = J-cap (F4 Ws R) (F3 Wr S)
      (J-F4 Ws R hs hR) (J-F3 Wr S hr hS)

  opaque
    unfolding swp
    J-swp : (R q : V ℓ) → InJ R → InJ q → InJ (swp R q)
    J-swp R q hR hq = J-ran (cap (F4 q R) (F3 q (idG q)))
      (J-cap (F4 q R) (F3 q (idG q))
        (J-F4 q R hq hR) (J-F3 q (idG q) hq (J-idG q hq)))

  opaque
    unfolding comp
    J-comp : (R S Wr Ws : V ℓ) → InJ R → InJ S → InJ Wr → InJ Ws
           → InJ (comp R S Wr Ws)
    J-comp R S Wr Ws hR hS hr hs = J-ran (joinOp R S Wr Ws)
      (J-join R S Wr Ws hR hS hr hs)

  opaque
    unfolding vals
    J-vals : (R D : V ℓ) → InJ R → InJ D → InJ (vals R D)
    J-vals R D hR hD = J-F8 R D hR hD

  opaque
    unfolding sgQ
    J-sgQ : (R D : V ℓ) → InJ R → InJ D → InJ (sgQ R D)
    J-sgQ R D hR hD = J-cup (cup D (F5 (vals R D) (vals R D))) (vals R D)
      (J-cup D (F5 (vals R D) (vals R D)) hD (J-F5 (vals R D) (vals R D) hB hB))
      hB
      where
      hB : InJ (vals R D)
      hB = J-vals R D hR hD

  opaque
    unfolding sgT
    J-sgT : (R D : V ℓ) → InJ R → InJ D → InJ (sgT R D)
    J-sgT R D hR hD = J-F2 (F5 (vals R D) (vals R D)) (F2 D (vals R D))
      (J-F5 (vals R D) (vals R D) hB hB) (J-F2 D (vals R D) hD hB)
      where
      hB : InJ (vals R D)
      hB = J-vals R D hR hD

  opaque
    unfolding sgL sgR
    J-sgL : (R D : V ℓ) → InJ R → InJ D → InJ (sgL R D)
    J-sgL R D hR hD = J-cap (F3 D (mrel (sgQ R D))) (sgT R D)
      (J-F3 D (mrel (sgQ R D)) hD (J-mrel (sgQ R D) (J-sgQ R D hR hD)))
      (J-sgT R D hR hD)

    J-sgR : (R D : V ℓ) → InJ R → InJ D → InJ (sgR R D)
    J-sgR R D hR hD = J-cap (F4 (vals R D) (swp R (sgQ R D))) (sgT R D)
      (J-F4 (vals R D) (swp R (sgQ R D)) (J-vals R D hR hD)
        (J-swp R (sgQ R D) hR (J-sgQ R D hR hD)))
      (J-sgT R D hR hD)

  opaque
    unfolding sgBad
    J-sgBad : (R D : V ℓ) → InJ R → InJ D → InJ (sgBad R D)
    J-sgBad R D hR hD =
      J-cup (ranOp (F1 (sgL R D) (sgR R D))) (ranOp (F1 (sgR R D) (sgL R D)))
        (J-ran (F1 (sgL R D) (sgR R D)) (J-F1 (sgL R D) (sgR R D) hL hRr))
        (J-ran (F1 (sgR R D) (sgL R D)) (J-F1 (sgR R D) (sgL R D) hRr hL))
      where
      hL : InJ (sgL R D)
      hL = J-sgL R D hR hD
      hRr : InJ (sgR R D)
      hRr = J-sgR R D hR hD

  opaque
    unfolding sgraph
    J-sgraph : (R D : V ℓ) → InJ R → InJ D → InJ (sgraph R D)
    J-sgraph R D hR hD = J-F1 (F2 D (vals R D)) (sgBad R D)
      (J-F2 D (vals R D) hD (J-vals R D hR hD)) (J-sgBad R D hR hD)

  opaque
    unfolding lpg rpg
    J-lpg : (P X : V ℓ) → InJ P → InJ X → InJ (lpg P X)
    J-lpg P X hP hX = J-cap (F3 X P) (F4 X (idG X))
      (J-F3 X P hX hP) (J-F4 X (idG X) hX (J-idG X hX))

    J-rpg : (P X : V ℓ) → InJ P → InJ X → InJ (rpg P X)
    J-rpg P X hP hX = J-cap (F4 X (swp P X)) (F3 X (idG X))
      (J-F4 X (swp P X) hX (J-swp P X hP hX))
      (J-F3 X (idG X) hX (J-idG X hX))

  opaque
    unfolding lproj rproj
    J-lproj : (P X : V ℓ) → InJ P → InJ X → InJ (lproj P X)
    J-lproj P X hP hX = J-swp (lpg P X) (cup X P) (J-lpg P X hP hX)
      (J-cup X P hX hP)

    J-rproj : (P X : V ℓ) → InJ P → InJ X → InJ (rproj P X)
    J-rproj P X hP hX = J-swp (rpg P X) (cup X P) (J-rpg P X hP hX)
      (J-cup X P hX hP)

  opaque
    unfolding fld
    J-fld : (R : V ℓ) → InJ R → InJ (fld R)
    J-fld R hR = J-amb (cup (F6 R R) (ranOp R))
      (J-cup (F6 R R) (ranOp R) (J-F6 R R hR hR) (J-ran R hR))

  opaque
    unfolding flat
    J-flat : (R : V ℓ) → InJ R → InJ (flat R)
    J-flat R hR = J-ran
      (cap (F4 (fld R) (swp R (fld R)))
           (F3 (fld R) (swp (mrel (fld R)) (fld R))))
      (J-cap (F4 (fld R) (swp R (fld R)))
             (F3 (fld R) (swp (mrel (fld R)) (fld R)))
        (J-F4 (fld R) (swp R (fld R)) hf (J-swp R (fld R) hR hf))
        (J-F3 (fld R) (swp (mrel (fld R)) (fld R)) hf
          (J-swp (mrel (fld R)) (fld R) (J-mrel (fld R) hf) hf)))
      where
      hf : InJ (fld R)
      hf = J-fld R hR
```


<!--en-->
## Argument records

A composite of arity `k` is evaluated at `k` arguments, and in the induction
every one of them varies with the index. An argument family is a function of
the index, and it enters the induction through its graph. The three
operations below read a family vector at an index, shift one along a left
projection, and read a constant vector; the shift is what the nested image
needs, since there the index is a pair whose two components feed different
slots.
<!--zh-->
## 自变量记录

元数为 `k` 的复合在 `k` 个自变量处求值，而在归纳中每个自变量都随索引变动。自变量族是索引的函数，它经由自己的图进入归纳。下面三个运算分别是：在索引处读出族向量、沿左投影平移一个族向量、以及读出常值向量；平移正是嵌套的像所需，因为那里索引是一个对，其两个分量喂给不同的槽。
<!--/-->

```agda
opaque
  -- perf: R-38: the Images projections are transparent by delivery and their
  -- bodies are union towers over setts, so a path endpoint mentioning one
  -- normalizes the tower; both are sealed here with their pair equations
  -- inside, and every consumer reads only the sealed equations. Invoking the
  -- imported right-spec costs 25 s even at variable arguments, and it is paid
  -- exactly once, here. The cheaper-looking replacement (the slice of the
  -- singleton at the left projection) is worse: proving its pair equation
  -- puts its own tower inside extensionality, which walls past 600 s (P-i [A]).
  prL : V ℓ → V ℓ
  prL x = left x

  prL-pair : (a b : V ℓ) → prL (pr a b) ≡ a
  prL-pair a b = left-spec a b

  prR : V ℓ → V ℓ
  prR x = right x

  prR-pair : (a b : V ℓ) → prR (pr a b) ≡ b
  prR-pair a b = right-spec a b

appAt : {k : ℕ} → Vec (V ℓ → V ℓ) k → V ℓ → Vec (V ℓ) k
appAt [] d = []
appAt (g ∷ gs) d = g d ∷ appAt gs d

appAt-lookup : {k : ℕ} (i : Fin k) (gs : Vec (V ℓ → V ℓ) k) (d : V ℓ)
             → lookup i (appAt gs d) ≡ lookup i gs d
appAt-lookup zero (g ∷ gs) d = refl
appAt-lookup (suc i) (g ∷ gs) d = appAt-lookup i gs d

shiftAt : {k : ℕ} → Vec (V ℓ → V ℓ) k → Vec (V ℓ → V ℓ) k
shiftAt [] = []
shiftAt (g ∷ gs) = (λ e → g (prL e)) ∷ shiftAt gs

appAt-shift : {k : ℕ} (gs : Vec (V ℓ → V ℓ) k) (e : V ℓ)
            → appAt (shiftAt gs) e ≡ appAt gs (prL e)
appAt-shift [] e = refl
appAt-shift (g ∷ gs) e = cong (g (prL e) ∷_) (appAt-shift gs e)

appAt-pair : {k : ℕ} (gs : Vec (V ℓ → V ℓ) k) (d t : V ℓ)
           → appAt (prR ∷ shiftAt gs) (pr d t) ≡ (t ∷ appAt gs d)
appAt-pair gs d t = cong₂ _∷_ (prR-pair d t)
  (appAt-shift gs (pr d t) ∙ cong (appAt gs) (prL-pair d t))

constFams : {k : ℕ} → Vec (V ℓ) k → Vec (V ℓ → V ℓ) k
constFams [] = []
constFams (v ∷ vs) = (λ _ → v) ∷ constFams vs

appAt-const : {k : ℕ} (vs : Vec (V ℓ) k) (d : V ℓ) → appAt (constFams vs) d ≡ vs
appAt-const [] d = refl
appAt-const (v ∷ vs) d = cong (v ∷_) (appAt-const vs d)

constGraphs : {k : ℕ} → V ℓ → Vec (V ℓ) k → Vec (V ℓ) k
constGraphs p [] = []
constGraphs p (v ∷ vs) = F2 p (F0 v v) ∷ constGraphs p vs

constRel : (p x y w : V ℓ) → ⟨ y ∈ˢ p ⟩
         → (⟨ pr y w ∈ˢ F2 p x ⟩ → ⟨ w ∈ˢ x ⟩)
         × (⟨ w ∈ˢ x ⟩ → ⟨ pr y w ∈ˢ F2 p x ⟩)
constRel p x y w y∈ = fwd , bwd
  where
  fwd : ⟨ pr y w ∈ˢ F2 p x ⟩ → ⟨ w ∈ˢ x ⟩
  fwd h = PT.rec (snd (w ∈ˢ x)) go (F2-read p x (pr y w) h)
    where
    go : Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ]
           (⟨ u ∈ˢ p ⟩ × ⟨ v ∈ˢ x ⟩ × ⟨ pr y w ≡ₕ pr u v ⟩)
       → ⟨ w ∈ˢ x ⟩
    go (u , v , _ , v∈ , e) = subst (λ t → ⟨ t ∈ˢ x ⟩)
      (sym (pr-inj {a = y} {b = w} {c = u} {d = v} e .snd)) v∈
  bwd : ⟨ w ∈ˢ x ⟩ → ⟨ pr y w ∈ˢ F2 p x ⟩
  bwd h = F2-write p x (pr y w) ∣ y , w , (y∈ , h , refl) ∣₁
```

<!--en-->
## The element-relation principle, restated

The principle indexes by a set `D` of records and a vector of argument
families given by their graphs. Its instance at a one-slot stack recovers the
form the switch chapter's hypothesis asks for, but the induction cannot be
run in that form: the nested image evaluates its inner composite at a stack
whose head varies with the index, so the hypothesis has to be uniform in the
record. Six clauses are pointwise in the record and port from the fixed-stack
form unchanged; the four that were open are proved below with the slice
graph; the nested image is proved with the projection graphs.
<!--zh-->
## 元素关系原理的重述

该原理以记录集 `D` 与一列由各自的图给出的自变量族为索引。它在单槽栈处的实例复现切换章假设所要的形状，但归纳不能在那个形状下运行：嵌套的像在栈首随索引变动的栈上求值其内层复合，故假设必须对记录一致。六条子句对记录是逐点的，从定栈形状原样移植；此前悬置的四条在下面用切片图证出；嵌套的像用投影图证出。
<!--/-->

```agda
module Cases (J : V ℓ)
  (Jrud : (i : Op16) (a b : V ℓ) → ⟨ a ∈ˢ J ⟩ → ⟨ b ∈ˢ J ⟩ → ⟨ Fof i a b ∈ˢ J ⟩)
  where

  open Kit J Jrud public

  IsGraph : (V ℓ → V ℓ) → V ℓ → V ℓ → Type (ℓ-suc ℓ)
  IsGraph g Γ D = (d w : V ℓ) → ⟨ d ∈ˢ D ⟩
                → (⟨ pr d w ∈ˢ Γ ⟩ → w ≡ g d) × (w ≡ g d → ⟨ pr d w ∈ˢ Γ ⟩)

  Args : {k : ℕ} → Vec (V ℓ → V ℓ) k → Vec (V ℓ) k → V ℓ → Type (ℓ-suc ℓ)
  Args [] [] D = Unit*
  Args (g ∷ gs) (Γ ∷ Γs) D = (InJ Γ × IsGraph g Γ D) × Args gs Γs D

  argAt : {k : ℕ} (i : Fin k) (gs : Vec (V ℓ → V ℓ) k) (Γs : Vec (V ℓ) k)
          (D : V ℓ) → Args gs Γs D
        → InJ (lookup i Γs) × IsGraph (lookup i gs) (lookup i Γs) D
  argAt zero (g ∷ gs) (Γ ∷ Γs) D (a , _) = a
  argAt (suc i) (g ∷ gs) (Γ ∷ Γs) D (_ , as) = argAt i gs Γs D as

  IsElemRel : {k : ℕ} → Comp k → Vec (V ℓ → V ℓ) k → V ℓ → V ℓ
            → Type (ℓ-suc ℓ)
  IsElemRel f gs D R = (d w : V ℓ) → ⟨ d ∈ˢ D ⟩
    → (⟨ pr d w ∈ˢ R ⟩ → ⟨ w ∈ˢ evalC f (appAt gs d) ⟩)
    × (⟨ w ∈ˢ evalC f (appAt gs d) ⟩ → ⟨ pr d w ∈ˢ R ⟩)

  ElemRel : {k : ℕ} → Comp k → Vec (V ℓ → V ℓ) k → V ℓ → Type (ℓ-suc ℓ)
  ElemRel f gs D = Σ[ R ∈ V ℓ ] (InJ R × IsElemRel f gs D R)
```

<!--en-->
The graph of a composite is the slice graph of its element relation. This is
the conversion the four waiting clauses were waiting for, and it is where the
slice graph is spent.
<!--zh-->
复合之图就是其元素关系的切片图。这正是四条待决子句所等的那次转换，也是切片图花掉之处。
<!--/-->

```agda
  graphOf : {k : ℕ} (f : Comp k) (gs : Vec (V ℓ → V ℓ) k) (D : V ℓ) → InJ D
          → ElemRel f gs D
          → Σ[ Γ ∈ V ℓ ] (InJ Γ × IsGraph (λ d → evalC f (appAt gs d)) Γ D)
  graphOf f gs D hD (R , hR , sp) =
    sgraph R D , (J-sgraph R D hR hD , spec)
    where
    spec : IsGraph (λ d → evalC f (appAt gs d)) (sgraph R D) D
    spec d w d∈ = fwd , bwd
      where
      val : V ℓ
      val = evalC f (appAt gs d)
      val≡ : F10 R d ≡ val
      val≡ = slice-eq R d val (λ x h → sp d x d∈ .fst h) (λ x h → sp d x d∈ .snd h)
      val∈ : ⟨ val ∈ˢ vals R D ⟩
      val∈ = subst (λ y → ⟨ y ∈ˢ vals R D ⟩) val≡ (vals-slice R D d d∈)
      fwd : ⟨ pr d w ∈ˢ sgraph R D ⟩ → w ≡ val
      fwd h = PT.rec (setIsSet w val) go (sgraph-shape R D (pr d w) h)
        where
        go : Σ[ d' ∈ V ℓ ] Σ[ v' ∈ V ℓ ]
               (⟨ d' ∈ˢ D ⟩ × ⟨ v' ∈ˢ vals R D ⟩ × ⟨ pr d w ≡ₕ pr d' v' ⟩)
           → w ≡ val
        go (d' , v' , _ , v'∈ , e) = extensionality w val (s₁ , s₂)
          where
          w∈vals : ⟨ w ∈ˢ vals R D ⟩
          w∈vals = subst (λ y → ⟨ y ∈ˢ vals R D ⟩)
            (sym (pr-inj {a = d} {b = w} {c = d'} {d = v'} e .snd)) v'∈
          s₁ : ⟨ w ⊆ val ⟩
          s₁ x x∈ = ∈s x val (sp d x d∈ .fst
            (sgraph-outl R D d w d∈ w∈vals h x (∈S x w x∈)))
          s₂ : ⟨ val ⊆ w ⟩
          s₂ x x∈ = ∈s x w (sgraph-outr R D d w d∈ w∈vals h x
            (sp d x d∈ .snd (∈S x val x∈)))
      bwd : w ≡ val → ⟨ pr d w ∈ˢ sgraph R D ⟩
      bwd e = subst (λ y → ⟨ pr d y ∈ˢ sgraph R D ⟩) (sym e)
        (sgraph-in R D d val d∈ val∈
          (λ x h → sp d x d∈ .snd h) (λ x h → sp d x d∈ .fst h))
```

<!--en-->
The six pointwise clauses. A constant and an argument slot are read off a
product and a flattened graph; intersection, difference and union are the
same operations on relations.
<!--zh-->
六条逐点子句。常量与自变量槽分别从积与摊平的图读出；交、差、并则是关系上的同名运算。
<!--/-->

```agda
  elem-conC : {k : ℕ} (x : V ℓ) (gs : Vec (V ℓ → V ℓ) k) (D : V ℓ)
            → InJ x → InJ D → ElemRel (conC x) gs D
  elem-conC x gs D hx hD =
    F2 D x , (J-F2 D x hD hx , λ d w d∈ → constRel D x d w d∈)

  elem-varC : {k : ℕ} (i : Fin k) (gs : Vec (V ℓ → V ℓ) k) (Γs : Vec (V ℓ) k)
              (D : V ℓ) → Args gs Γs D → InJ D → ElemRel (varC i) gs D
  elem-varC i gs Γs D args hD = flat Γᵢ , (J-flat Γᵢ hΓ , spec)
    where
    Γᵢ : V ℓ
    Γᵢ = lookup i Γs
    hΓ : InJ Γᵢ
    hΓ = argAt i gs Γs D args .fst
    gr : IsGraph (lookup i gs) Γᵢ D
    gr = argAt i gs Γs D args .snd
    spec : IsElemRel (varC i) gs D (flat Γᵢ)
    spec d w d∈ = fwd , bwd
      where
      eq : lookup i (appAt gs d) ≡ lookup i gs d
      eq = appAt-lookup i gs d
      fwd : ⟨ pr d w ∈ˢ flat Γᵢ ⟩ → ⟨ w ∈ˢ lookup i (appAt gs d) ⟩
      fwd h = PT.rec (snd (w ∈ˢ lookup i (appAt gs d))) go (flat-out Γᵢ (pr d w) h)
        where
        go : Σ[ d' ∈ V ℓ ] Σ[ v ∈ V ℓ ] Σ[ w' ∈ V ℓ ]
               (⟨ pr d' v ∈ˢ Γᵢ ⟩ × ⟨ w' ∈ˢ v ⟩ × ⟨ pr d w ≡ₕ pr d' w' ⟩)
           → ⟨ w ∈ˢ lookup i (appAt gs d) ⟩
        go (d' , v , w' , dv∈ , w'∈ , e) = subst (λ y → ⟨ w ∈ˢ y ⟩) (sym eq)
          (subst (λ y → ⟨ w ∈ˢ y ⟩) v≡
            (subst (λ y → ⟨ y ∈ˢ v ⟩) (sym w≡w') w'∈))
          where
          d≡d' : d ≡ d'
          d≡d' = pr-inj {a = d} {b = w} {c = d'} {d = w'} e .fst
          w≡w' : w ≡ w'
          w≡w' = pr-inj {a = d} {b = w} {c = d'} {d = w'} e .snd
          v≡ : v ≡ lookup i gs d
          v≡ = gr d v d∈ .fst
            (subst (λ y → ⟨ pr y v ∈ˢ Γᵢ ⟩) (sym d≡d') dv∈)
      bwd : ⟨ w ∈ˢ lookup i (appAt gs d) ⟩ → ⟨ pr d w ∈ˢ flat Γᵢ ⟩
      bwd h = flat-in Γᵢ d (lookup i gs d) w (gr d (lookup i gs d) d∈ .snd refl)
        (subst (λ y → ⟨ w ∈ˢ y ⟩) eq h)

  elem-interC : {k : ℕ} (a b : Comp k) (gs : Vec (V ℓ → V ℓ) k) (D : V ℓ)
              → ElemRel a gs D → ElemRel b gs D → ElemRel (interC a b) gs D
  elem-interC a b gs D (Ra , hRa , sa) (Rb , hRb , sb) =
    cap Ra Rb , (J-cap Ra Rb hRa hRb , spec)
    where
    spec : IsElemRel (interC a b) gs D (cap Ra Rb)
    spec d w d∈ = fwd , bwd
      where
      X : V ℓ
      X = evalC a (appAt gs d)
      Y : V ℓ
      Y = evalC b (appAt gs d)
      fwd : ⟨ pr d w ∈ˢ cap Ra Rb ⟩ → ⟨ w ∈ˢ interOp X Y ⟩
      fwd h = ∈S w (interOp X Y) (interSpec X Y w .snd
        ( ∈s w X (sa d w d∈ .fst (cap-outl Ra Rb (pr d w) h))
        , ∈s w Y (sb d w d∈ .fst (cap-outr Ra Rb (pr d w) h)) ))
      bwd : ⟨ w ∈ˢ interOp X Y ⟩ → ⟨ pr d w ∈ˢ cap Ra Rb ⟩
      bwd h = cap-in Ra Rb (pr d w)
        (sa d w d∈ .snd (∈S w X (interSpec X Y w .fst (∈s w (interOp X Y) h) .fst)))
        (sb d w d∈ .snd (∈S w Y (interSpec X Y w .fst (∈s w (interOp X Y) h) .snd)))

  elem-diffC : {k : ℕ} (a b : Comp k) (gs : Vec (V ℓ → V ℓ) k) (D : V ℓ)
             → ElemRel a gs D → ElemRel b gs D → ElemRel (diffC a b) gs D
  elem-diffC a b gs D (Ra , hRa , sa) (Rb , hRb , sb) =
    F1 Ra Rb , (J-F1 Ra Rb hRa hRb , spec)
    where
    spec : IsElemRel (diffC a b) gs D (F1 Ra Rb)
    spec d w d∈ = fwd , bwd
      where
      X : V ℓ
      X = evalC a (appAt gs d)
      Y : V ℓ
      Y = evalC b (appAt gs d)
      fwd : ⟨ pr d w ∈ˢ F1 Ra Rb ⟩ → ⟨ w ∈ˢ F1 X Y ⟩
      fwd h = F1-spec X Y w .snd
        ( sa d w d∈ .fst (F1-spec Ra Rb (pr d w) .fst h .fst)
        , λ k → F1-spec Ra Rb (pr d w) .fst h .snd (sb d w d∈ .snd k) )
      bwd : ⟨ w ∈ˢ F1 X Y ⟩ → ⟨ pr d w ∈ˢ F1 Ra Rb ⟩
      bwd h = F1-spec Ra Rb (pr d w) .snd
        ( sa d w d∈ .snd (F1-spec X Y w .fst h .fst)
        , λ k → F1-spec X Y w .fst h .snd (sb d w d∈ .fst k) )

  elem-unionC : {k : ℕ} (a : Comp k) (gs : Vec (V ℓ → V ℓ) k) (D : V ℓ)
              → ElemRel a gs D → ElemRel (unionC a) gs D
  elem-unionC a gs D (Ra , hRa , sa) = flat Ra , (J-flat Ra hRa , spec)
    where
    spec : IsElemRel (unionC a) gs D (flat Ra)
    spec d w d∈ = fwd , bwd
      where
      X : V ℓ
      X = evalC a (appAt gs d)
      fwd : ⟨ pr d w ∈ˢ flat Ra ⟩ → ⟨ w ∈ˢ unionOp X ⟩
      fwd h = PT.rec (snd (w ∈ˢ unionOp X)) go (flat-out Ra (pr d w) h)
        where
        go : Σ[ d' ∈ V ℓ ] Σ[ v ∈ V ℓ ] Σ[ w' ∈ V ℓ ]
               (⟨ pr d' v ∈ˢ Ra ⟩ × ⟨ w' ∈ˢ v ⟩ × ⟨ pr d w ≡ₕ pr d' w' ⟩)
           → ⟨ w ∈ˢ unionOp X ⟩
        go (d' , v , w' , dv∈ , w'∈ , e) = ∈S w (unionOp X)
          (unionSpec X w .snd ∣ v , (∈s v X v∈X , ∈s w v w∈v) ∣₁)
          where
          v∈X : ⟨ v ∈ˢ X ⟩
          v∈X = sa d v d∈ .fst (subst (λ y → ⟨ pr y v ∈ˢ Ra ⟩)
            (sym (pr-inj {a = d} {b = w} {c = d'} {d = w'} e .fst)) dv∈)
          w∈v : ⟨ w ∈ˢ v ⟩
          w∈v = subst (λ y → ⟨ y ∈ˢ v ⟩)
            (sym (pr-inj {a = d} {b = w} {c = d'} {d = w'} e .snd)) w'∈
      bwd : ⟨ w ∈ˢ unionOp X ⟩ → ⟨ pr d w ∈ˢ flat Ra ⟩
      bwd h = PT.rec (snd (pr d w ∈ˢ flat Ra)) go
        (unionSpec X w .fst (∈s w (unionOp X) h))
        where
        go : Σ[ v ∈ V ℓ ] (⟨ v ∈ₛ X ⟩ × ⟨ w ∈ₛ v ⟩) → ⟨ pr d w ∈ˢ flat Ra ⟩
        go (v , v∈ , w∈) = flat-in Ra d v w
          (sa d v d∈ .snd (∈S v X v∈)) (∈S w v w∈)
```

<!--en-->
The four clauses the slice graph unblocks. Pairing is the union of the two
graphs; collection cuts the second element relation by a membership test read
off the first graph; the two separations restrict the third element relation
to the records where the test holds, and the test is the join of the two
graphs met with a product of the membership relation, or of the identity
graph.
<!--zh-->
切片图解开的四条子句。配对是两个图之并；收集用从第一个图读出的隶属检验切割第二个元素关系；两种分离把第三个元素关系限制到检验成立的那些记录上，而检验是两个图的接合与隶属关系之积、或与恒等图之积，二者取交。
<!--/-->

```agda
  elem-pairC : {k : ℕ} (a b : Comp k) (gs : Vec (V ℓ → V ℓ) k) (D : V ℓ)
             → InJ D → ElemRel a gs D → ElemRel b gs D → ElemRel (pairC a b) gs D
  elem-pairC a b gs D hD Ea Eb = cup Γa Γb , (J-cup Γa Γb hΓa hΓb , spec)
    where
    GA : Σ[ Γ ∈ V ℓ ] (InJ Γ × IsGraph (λ d → evalC a (appAt gs d)) Γ D)
    GA = graphOf a gs D hD Ea
    GB : Σ[ Γ ∈ V ℓ ] (InJ Γ × IsGraph (λ d → evalC b (appAt gs d)) Γ D)
    GB = graphOf b gs D hD Eb
    Γa : V ℓ
    Γa = GA .fst
    Γb : V ℓ
    Γb = GB .fst
    hΓa : InJ Γa
    hΓa = GA .snd .fst
    hΓb : InJ Γb
    hΓb = GB .snd .fst
    spec : IsElemRel (pairC a b) gs D (cup Γa Γb)
    spec d w d∈ = fwd , bwd
      where
      X : V ℓ
      X = evalC a (appAt gs d)
      Y : V ℓ
      Y = evalC b (appAt gs d)
      fwd : ⟨ pr d w ∈ˢ cup Γa Γb ⟩ → ⟨ w ∈ˢ F0 X Y ⟩
      fwd h = PT.rec (snd (w ∈ˢ F0 X Y)) sides (cup-out Γa Γb (pr d w) h)
        where
        sides : (⟨ pr d w ∈ˢ Γa ⟩ ⊎ ⟨ pr d w ∈ˢ Γb ⟩) → ⟨ w ∈ˢ F0 X Y ⟩
        sides (inl k) = F0-spec X Y w .snd ∣ inl (GA .snd .snd d w d∈ .fst k) ∣₁
        sides (inr k) = F0-spec X Y w .snd ∣ inr (GB .snd .snd d w d∈ .fst k) ∣₁
      bwd : ⟨ w ∈ˢ F0 X Y ⟩ → ⟨ pr d w ∈ˢ cup Γa Γb ⟩
      bwd h = PT.rec (snd (pr d w ∈ˢ cup Γa Γb)) sides (F0-spec X Y w .fst h)
        where
        sides : (⟨ w ≡ₕ X ⟩ ⊎ ⟨ w ≡ₕ Y ⟩) → ⟨ pr d w ∈ˢ cup Γa Γb ⟩
        sides (inl e) = cup-in Γa Γb (pr d w) ∣ inl (GA .snd .snd d w d∈ .snd e) ∣₁
        sides (inr e) = cup-in Γa Γb (pr d w) ∣ inr (GB .snd .snd d w d∈ .snd e) ∣₁

  elem-colC : {k : ℕ} (a b : Comp k) (gs : Vec (V ℓ → V ℓ) k) (D : V ℓ)
            → InJ D → ElemRel a gs D → ElemRel b gs D → ElemRel (colC a b) gs D
  elem-colC a b gs D hD Ea (Rb , hRb , sb) = cap Rb M , (J-cap Rb M hRb hM , spec)
    where
    GA : Σ[ Γ ∈ V ℓ ] (InJ Γ × IsGraph (λ d → evalC a (appAt gs d)) Γ D)
    GA = graphOf a gs D hD Ea
    Γa : V ℓ
    Γa = GA .fst
    Wt : V ℓ
    Wt = F5 (vals Rb D) (vals Rb D)
    WA : V ℓ
    WA = F5 (vals Γa D) (vals Γa D)
    Q : V ℓ
    Q = cup (cup D Wt) WA
    M : V ℓ
    M = comp (swp Γa Q) (mrel Q) D Wt
    hWt : InJ Wt
    hWt = J-F5 (vals Rb D) (vals Rb D) hv hv
      where
      hv : InJ (vals Rb D)
      hv = J-vals Rb D hRb hD
    hQ : InJ Q
    hQ = J-cup (cup D Wt) WA (J-cup D Wt hD hWt)
      (J-F5 (vals Γa D) (vals Γa D) hv hv)
      where
      hv : InJ (vals Γa D)
      hv = J-vals Γa D (GA .snd .fst) hD
    hM : InJ M
    hM = J-comp (swp Γa Q) (mrel Q) D Wt
      (J-swp Γa Q (GA .snd .fst) hQ) (J-mrel Q hQ) hD hWt
    spec : IsElemRel (colC a b) gs D (cap Rb M)
    spec d t d∈ = fwd , bwd
      where
      X : V ℓ
      X = evalC a (appAt gs d)
      Y : V ℓ
      Y = evalC b (appAt gs d)
      dX∈ : ⟨ pr d X ∈ˢ Γa ⟩
      dX∈ = GA .snd .snd d X d∈ .snd refl
      X∈Q : ⟨ X ∈ˢ Q ⟩
      X∈Q = cup-in (cup D Wt) WA X ∣ inr (vals-union Γa D d X d∈ dX∈) ∣₁
      d∈Q : ⟨ d ∈ˢ Q ⟩
      d∈Q = cup-in (cup D Wt) WA d ∣ inl (cup-in D Wt d ∣ inl d∈ ∣₁) ∣₁
      fwd : ⟨ pr d t ∈ˢ cap Rb M ⟩ → ⟨ t ∈ˢ colOp X Y ⟩
      fwd h = ∈S t (colOp X Y)
        (colSpec X Y t .snd (∈s t Y t∈Y , ∈s X t X∈t))
        where
        t∈Y : ⟨ t ∈ˢ Y ⟩
        t∈Y = sb d t d∈ .fst (cap-outl Rb M (pr d t) h)
        X∈t : ⟨ X ∈ˢ t ⟩
        X∈t = PT.rec (snd (X ∈ˢ t)) go
          (comp-out (swp Γa Q) (mrel Q) D Wt (pr d t) (cap-outr Rb M (pr d t) h))
          where
          go : Σ[ m ∈ V ℓ ] Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ]
                 (⟨ pr m u ∈ˢ swp Γa Q ⟩ × ⟨ pr m v ∈ˢ mrel Q ⟩
                  × ⟨ pr d t ≡ₕ pr u v ⟩)
             → ⟨ X ∈ˢ t ⟩
          go (m , u , v , su∈ , mv∈ , e) = PT.rec (snd (X ∈ˢ t)) inner
            (swp-out Γa Q (pr m u) su∈)
            where
            d≡u : d ≡ u
            d≡u = pr-inj {a = d} {b = t} {c = u} {d = v} e .fst
            t≡v : t ≡ v
            t≡v = pr-inj {a = d} {b = t} {c = u} {d = v} e .snd
            inner : Σ[ x ∈ V ℓ ] Σ[ y ∈ V ℓ ]
                      (⟨ pr x y ∈ˢ Γa ⟩ × ⟨ pr m u ≡ₕ pr y x ⟩) → ⟨ X ∈ˢ t ⟩
            inner (x , y , xy∈ , e₂) = subst (λ z → ⟨ z ∈ˢ t ⟩) m≡X
              (subst (λ z → ⟨ m ∈ˢ z ⟩) (sym t≡v) (mrel-out Q m v mv∈))
              where
              m≡y : m ≡ y
              m≡y = pr-inj {a = m} {b = u} {c = y} {d = x} e₂ .fst
              u≡x : u ≡ x
              u≡x = pr-inj {a = m} {b = u} {c = y} {d = x} e₂ .snd
              m≡X : m ≡ X
              m≡X = GA .snd .snd d m d∈ .fst
                (subst (λ z → ⟨ pr z m ∈ˢ Γa ⟩) (sym (d≡u ∙ u≡x))
                  (subst (λ z → ⟨ pr x z ∈ˢ Γa ⟩) (sym m≡y) xy∈))
      bwd : ⟨ t ∈ˢ colOp X Y ⟩ → ⟨ pr d t ∈ˢ cap Rb M ⟩
      bwd h = cap-in Rb M (pr d t) inRb
        (comp-in (swp Γa Q) (mrel Q) D Wt X d t
          (swp-in Γa Q d X dX∈ d∈Q X∈Q)
          (mrel-in Q X t X∈Q t∈Q (∈S X t (colSpec X Y t .fst
            (∈s t (colOp X Y) h) .snd)))
          d∈ t∈Wt)
        where
        t∈Y : ⟨ t ∈ˢ Y ⟩
        t∈Y = ∈S t Y (colSpec X Y t .fst (∈s t (colOp X Y) h) .fst)
        inRb : ⟨ pr d t ∈ˢ Rb ⟩
        inRb = sb d t d∈ .snd t∈Y
        t∈Wt : ⟨ t ∈ˢ Wt ⟩
        t∈Wt = vals-union Rb D d t d∈ inRb
        t∈Q : ⟨ t ∈ˢ Q ⟩
        t∈Q = cup-in (cup D Wt) WA t ∣ inl (cup-in D Wt t ∣ inr t∈Wt ∣₁) ∣₁
```

```agda
  testSet : V ℓ → V ℓ → V ℓ → V ℓ → V ℓ → V ℓ → V ℓ
  testSet Γa Γb T D WA WB =
    F6 (cap (joinOp Γa Γb WA WB) (F2 D T)) (cap (joinOp Γa Γb WA WB) (F2 D T))

  J-test : (Γa Γb T D WA WB : V ℓ) → InJ Γa → InJ Γb → InJ T → InJ D
         → InJ WA → InJ WB → InJ (testSet Γa Γb T D WA WB)
  J-test Γa Γb T D WA WB ha hb hT hD hA hB = J-F6 C C hC hC
    where
    C : V ℓ
    C = cap (joinOp Γa Γb WA WB) (F2 D T)
    hC : InJ C
    hC = J-cap (joinOp Γa Γb WA WB) (F2 D T)
      (J-join Γa Γb WA WB ha hb hA hB) (J-F2 D T hD hT)

  test-in : (Γa Γb T D WA WB d A B : V ℓ) → ⟨ d ∈ˢ D ⟩
          → ⟨ pr d A ∈ˢ Γa ⟩ → ⟨ pr d B ∈ˢ Γb ⟩ → ⟨ A ∈ˢ WA ⟩ → ⟨ B ∈ˢ WB ⟩
          → ⟨ pr A B ∈ˢ T ⟩ → ⟨ d ∈ˢ testSet Γa Γb T D WA WB ⟩
  test-in Γa Γb T D WA WB d A B d∈ dA∈ dB∈ A∈ B∈ AB∈ =
    F6-write C C d ∣ d , pr A B , (inC , refl) ∣₁
    where
    C : V ℓ
    C = cap (joinOp Γa Γb WA WB) (F2 D T)
    inC : ⟨ pr d (pr A B) ∈ˢ C ⟩
    inC = cap-in (joinOp Γa Γb WA WB) (F2 D T) (pr d (pr A B))
      (join-in Γa Γb WA WB d A B dA∈ dB∈ A∈ B∈)
      (F2-write D T (pr d (pr A B)) ∣ d , pr A B , (d∈ , AB∈ , refl) ∣₁)

  test-out : (Γa Γb T D WA WB d : V ℓ) → ⟨ d ∈ˢ testSet Γa Γb T D WA WB ⟩
           → ∥ Σ[ A ∈ V ℓ ] Σ[ B ∈ V ℓ ]
                (⟨ pr d A ∈ˢ Γa ⟩ × ⟨ pr d B ∈ˢ Γb ⟩ × ⟨ pr A B ∈ˢ T ⟩) ∥₁
  test-out Γa Γb T D WA WB d h = PT.rec squash₁ outer (F6-read C C d h)
    where
    C : V ℓ
    C = cap (joinOp Γa Γb WA WB) (F2 D T)
    E : Type (ℓ-suc ℓ)
    E = Σ[ A ∈ V ℓ ] Σ[ B ∈ V ℓ ]
          (⟨ pr d A ∈ˢ Γa ⟩ × ⟨ pr d B ∈ˢ Γb ⟩ × ⟨ pr A B ∈ˢ T ⟩)
    outer : Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ] (⟨ pr u v ∈ˢ C ⟩ × ⟨ d ≡ₕ u ⟩) → ∥ E ∥₁
    outer (u , v , uv∈ , d≡u) = PT.rec squash₁ fromJoin
      (join-out Γa Γb WA WB (pr d v)
        (cap-outl (joinOp Γa Γb WA WB) (F2 D T) (pr d v) dv∈))
      where
      dv∈ : ⟨ pr d v ∈ˢ C ⟩
      dv∈ = subst (λ y → ⟨ pr y v ∈ˢ C ⟩) (sym d≡u) uv∈
      fromJoin : Σ[ d₀ ∈ V ℓ ] Σ[ x ∈ V ℓ ] Σ[ y ∈ V ℓ ]
                   (⟨ pr d₀ x ∈ˢ Γa ⟩ × ⟨ pr d₀ y ∈ˢ Γb ⟩
                    × ⟨ pr d v ≡ₕ pr d₀ (pr x y) ⟩)
               → ∥ E ∥₁
      fromJoin (d₀ , x , y , dx∈ , dy∈ , e) = PT.rec squash₁ fromProd
        (F2-read D T (pr d v)
          (cap-outr (joinOp Γa Γb WA WB) (F2 D T) (pr d v) dv∈))
        where
        d≡d₀ : d ≡ d₀
        d≡d₀ = pr-inj {a = d} {b = v} {c = d₀} {d = pr x y} e .fst
        v≡xy : v ≡ pr x y
        v≡xy = pr-inj {a = d} {b = v} {c = d₀} {d = pr x y} e .snd
        fromProd : Σ[ d₁ ∈ V ℓ ] Σ[ v₁ ∈ V ℓ ]
                     (⟨ d₁ ∈ˢ D ⟩ × ⟨ v₁ ∈ˢ T ⟩ × ⟨ pr d v ≡ₕ pr d₁ v₁ ⟩)
                 → ∥ E ∥₁
        fromProd (d₁ , v₁ , _ , v₁∈ , e₁) = ∣ x , y
          , ( subst (λ z → ⟨ pr z x ∈ˢ Γa ⟩) (sym d≡d₀) dx∈
            , subst (λ z → ⟨ pr z y ∈ˢ Γb ⟩) (sym d≡d₀) dy∈
            , subst (λ z → ⟨ z ∈ˢ T ⟩)
                (sym (pr-inj {a = d} {b = v} {c = d₁} {d = v₁} e₁ .snd ) ∙ v≡xy)
                v₁∈ ) ∣₁

  elem-chSepC : {k : ℕ} (a b c : Comp k) (gs : Vec (V ℓ → V ℓ) k) (D : V ℓ)
              → InJ D → ElemRel a gs D → ElemRel b gs D → ElemRel c gs D
              → ElemRel (chSepC a b c) gs D
  elem-chSepC a b c gs D hD Ea Eb (Rc , hRc , sc) =
    cap Rc (F2 P Wc) , (J-cap Rc (F2 P Wc) hRc (J-F2 P Wc hP hWc) , spec)
    where
    GA : Σ[ Γ ∈ V ℓ ] (InJ Γ × IsGraph (λ d → evalC a (appAt gs d)) Γ D)
    GA = graphOf a gs D hD Ea
    GB : Σ[ Γ ∈ V ℓ ] (InJ Γ × IsGraph (λ d → evalC b (appAt gs d)) Γ D)
    GB = graphOf b gs D hD Eb
    WA : V ℓ
    WA = F5 (vals (GA .fst) D) (vals (GA .fst) D)
    WB : V ℓ
    WB = F5 (vals (GB .fst) D) (vals (GB .fst) D)
    Q : V ℓ
    Q = cup WA WB
    Wc : V ℓ
    Wc = F5 (vals Rc D) (vals Rc D)
    P : V ℓ
    P = testSet (GA .fst) (GB .fst) (mrel Q) D WA WB
    hWA : InJ WA
    hWA = J-F5 (vals (GA .fst) D) (vals (GA .fst) D) hv hv
      where
      hv : InJ (vals (GA .fst) D)
      hv = J-vals (GA .fst) D (GA .snd .fst) hD
    hWB : InJ WB
    hWB = J-F5 (vals (GB .fst) D) (vals (GB .fst) D) hv hv
      where
      hv : InJ (vals (GB .fst) D)
      hv = J-vals (GB .fst) D (GB .snd .fst) hD
    hWc : InJ Wc
    hWc = J-F5 (vals Rc D) (vals Rc D) hv hv
      where
      hv : InJ (vals Rc D)
      hv = J-vals Rc D hRc hD
    hP : InJ P
    hP = J-test (GA .fst) (GB .fst) (mrel Q) D WA WB (GA .snd .fst) (GB .snd .fst)
      (J-mrel Q (J-cup WA WB hWA hWB)) hD hWA hWB
    spec : IsElemRel (chSepC a b c) gs D (cap Rc (F2 P Wc))
    spec d w d∈ = fwd , bwd
      where
      X : V ℓ
      X = evalC a (appAt gs d)
      Y : V ℓ
      Y = evalC b (appAt gs d)
      Z : V ℓ
      Z = evalC c (appAt gs d)
      dX∈ : ⟨ pr d X ∈ˢ GA .fst ⟩
      dX∈ = GA .snd .snd d X d∈ .snd refl
      dY∈ : ⟨ pr d Y ∈ˢ GB .fst ⟩
      dY∈ = GB .snd .snd d Y d∈ .snd refl
      X∈WA : ⟨ X ∈ˢ WA ⟩
      X∈WA = vals-union (GA .fst) D d X d∈ dX∈
      Y∈WB : ⟨ Y ∈ˢ WB ⟩
      Y∈WB = vals-union (GB .fst) D d Y d∈ dY∈
      fwd : ⟨ pr d w ∈ˢ cap Rc (F2 P Wc) ⟩ → ⟨ w ∈ˢ chSepOp X Y Z ⟩
      fwd h = ∈S w (chSepOp X Y Z)
        (chSepSpec X Y Z w .snd (∈s w Z w∈Z , ∈s X Y X∈Y))
        where
        w∈Z : ⟨ w ∈ˢ Z ⟩
        w∈Z = sc d w d∈ .fst (cap-outl Rc (F2 P Wc) (pr d w) h)
        d∈P : ⟨ d ∈ˢ P ⟩
        d∈P = PT.rec (snd (d ∈ˢ P)) go
          (F2-read P Wc (pr d w) (cap-outr Rc (F2 P Wc) (pr d w) h))
          where
          go : Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ]
                 (⟨ u ∈ˢ P ⟩ × ⟨ v ∈ˢ Wc ⟩ × ⟨ pr d w ≡ₕ pr u v ⟩) → ⟨ d ∈ˢ P ⟩
          go (u , v , u∈ , _ , e) = subst (λ z → ⟨ z ∈ˢ P ⟩)
            (sym (pr-inj {a = d} {b = w} {c = u} {d = v} e .fst)) u∈
        X∈Y : ⟨ X ∈ˢ Y ⟩
        X∈Y = PT.rec (snd (X ∈ˢ Y)) go
          (test-out (GA .fst) (GB .fst) (mrel Q) D WA WB d d∈P)
          where
          go : Σ[ A ∈ V ℓ ] Σ[ B ∈ V ℓ ]
                 (⟨ pr d A ∈ˢ GA .fst ⟩ × ⟨ pr d B ∈ˢ GB .fst ⟩
                  × ⟨ pr A B ∈ˢ mrel Q ⟩)
             → ⟨ X ∈ˢ Y ⟩
          go (A , B , dA∈ , dB∈ , AB∈) =
            subst (λ z → ⟨ z ∈ˢ Y ⟩) (GA .snd .snd d A d∈ .fst dA∈)
              (subst (λ z → ⟨ A ∈ˢ z ⟩) (GB .snd .snd d B d∈ .fst dB∈)
                (mrel-out Q A B AB∈))
      bwd : ⟨ w ∈ˢ chSepOp X Y Z ⟩ → ⟨ pr d w ∈ˢ cap Rc (F2 P Wc) ⟩
      bwd h = cap-in Rc (F2 P Wc) (pr d w) inRc
        (F2-write P Wc (pr d w) ∣ d , w , (d∈P , w∈Wc , refl) ∣₁)
        where
        parts : ⟨ w ∈ₛ Z ⟩ × ⟨ X ∈ₛ Y ⟩
        parts = chSepSpec X Y Z w .fst (∈s w (chSepOp X Y Z) h)
        inRc : ⟨ pr d w ∈ˢ Rc ⟩
        inRc = sc d w d∈ .snd (∈S w Z (parts .fst))
        w∈Wc : ⟨ w ∈ˢ Wc ⟩
        w∈Wc = vals-union Rc D d w d∈ inRc
        d∈P : ⟨ d ∈ˢ P ⟩
        d∈P = test-in (GA .fst) (GB .fst) (mrel Q) D WA WB d X Y d∈ dX∈ dY∈
          X∈WA Y∈WB
          (mrel-in Q X Y (cup-in WA WB X ∣ inl X∈WA ∣₁)
            (cup-in WA WB Y ∣ inr Y∈WB ∣₁) (∈S X Y (parts .snd)))
```

```agda
  elem-eqSepC : {k : ℕ} (a b c : Comp k) (gs : Vec (V ℓ → V ℓ) k) (D : V ℓ)
              → InJ D → ElemRel a gs D → ElemRel b gs D → ElemRel c gs D
              → ElemRel (eqSepC a b c) gs D
  elem-eqSepC a b c gs D hD Ea Eb (Rc , hRc , sc) =
    cap Rc (F2 P Wc) , (J-cap Rc (F2 P Wc) hRc (J-F2 P Wc hP hWc) , spec)
    where
    GA : Σ[ Γ ∈ V ℓ ] (InJ Γ × IsGraph (λ d → evalC a (appAt gs d)) Γ D)
    GA = graphOf a gs D hD Ea
    GB : Σ[ Γ ∈ V ℓ ] (InJ Γ × IsGraph (λ d → evalC b (appAt gs d)) Γ D)
    GB = graphOf b gs D hD Eb
    WA : V ℓ
    WA = F5 (vals (GA .fst) D) (vals (GA .fst) D)
    WB : V ℓ
    WB = F5 (vals (GB .fst) D) (vals (GB .fst) D)
    Q : V ℓ
    Q = cup WA WB
    Wc : V ℓ
    Wc = F5 (vals Rc D) (vals Rc D)
    P : V ℓ
    P = testSet (GA .fst) (GB .fst) (idG Q) D WA WB
    hWA : InJ WA
    hWA = J-F5 (vals (GA .fst) D) (vals (GA .fst) D) hv hv
      where
      hv : InJ (vals (GA .fst) D)
      hv = J-vals (GA .fst) D (GA .snd .fst) hD
    hWB : InJ WB
    hWB = J-F5 (vals (GB .fst) D) (vals (GB .fst) D) hv hv
      where
      hv : InJ (vals (GB .fst) D)
      hv = J-vals (GB .fst) D (GB .snd .fst) hD
    hWc : InJ Wc
    hWc = J-F5 (vals Rc D) (vals Rc D) hv hv
      where
      hv : InJ (vals Rc D)
      hv = J-vals Rc D hRc hD
    hP : InJ P
    hP = J-test (GA .fst) (GB .fst) (idG Q) D WA WB (GA .snd .fst) (GB .snd .fst)
      (J-idG Q (J-cup WA WB hWA hWB)) hD hWA hWB
    spec : IsElemRel (eqSepC a b c) gs D (cap Rc (F2 P Wc))
    spec d w d∈ = fwd , bwd
      where
      X : V ℓ
      X = evalC a (appAt gs d)
      Y : V ℓ
      Y = evalC b (appAt gs d)
      Z : V ℓ
      Z = evalC c (appAt gs d)
      dX∈ : ⟨ pr d X ∈ˢ GA .fst ⟩
      dX∈ = GA .snd .snd d X d∈ .snd refl
      dY∈ : ⟨ pr d Y ∈ˢ GB .fst ⟩
      dY∈ = GB .snd .snd d Y d∈ .snd refl
      X∈WA : ⟨ X ∈ˢ WA ⟩
      X∈WA = vals-union (GA .fst) D d X d∈ dX∈
      Y∈WB : ⟨ Y ∈ˢ WB ⟩
      Y∈WB = vals-union (GB .fst) D d Y d∈ dY∈
      fwd : ⟨ pr d w ∈ˢ cap Rc (F2 P Wc) ⟩ → ⟨ w ∈ˢ eqSepOp X Y Z ⟩
      fwd h = ∈S w (eqSepOp X Y Z)
        (eqSepSpec X Y Z w .snd (∈s w Z w∈Z , X∼Y))
        where
        w∈Z : ⟨ w ∈ˢ Z ⟩
        w∈Z = sc d w d∈ .fst (cap-outl Rc (F2 P Wc) (pr d w) h)
        d∈P : ⟨ d ∈ˢ P ⟩
        d∈P = PT.rec (snd (d ∈ˢ P)) go
          (F2-read P Wc (pr d w) (cap-outr Rc (F2 P Wc) (pr d w) h))
          where
          go : Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ]
                 (⟨ u ∈ˢ P ⟩ × ⟨ v ∈ˢ Wc ⟩ × ⟨ pr d w ≡ₕ pr u v ⟩) → ⟨ d ∈ˢ P ⟩
          go (u , v , u∈ , _ , e) = subst (λ z → ⟨ z ∈ˢ P ⟩)
            (sym (pr-inj {a = d} {b = w} {c = u} {d = v} e .fst)) u∈
        X∼Y : ⟨ X ∼ Y ⟩
        X∼Y = PT.rec (snd (X ∼ Y)) go
          (test-out (GA .fst) (GB .fst) (idG Q) D WA WB d d∈P)
          where
          go : Σ[ A ∈ V ℓ ] Σ[ B ∈ V ℓ ]
                 (⟨ pr d A ∈ˢ GA .fst ⟩ × ⟨ pr d B ∈ˢ GB .fst ⟩
                  × ⟨ pr A B ∈ˢ idG Q ⟩)
             → ⟨ X ∼ Y ⟩
          go (A , B , dA∈ , dB∈ , AB∈) = PT.rec (snd (X ∼ Y)) inner
            (idG-out Q (pr A B) AB∈)
            where
            A≡X : A ≡ X
            A≡X = GA .snd .snd d A d∈ .fst dA∈
            B≡Y : B ≡ Y
            B≡Y = GB .snd .snd d B d∈ .fst dB∈
            inner : Σ[ z ∈ V ℓ ] (⟨ z ∈ˢ Q ⟩ × ⟨ pr A B ≡ₕ pr z z ⟩)
                  → ⟨ X ∼ Y ⟩
            inner (z , _ , e) = equivFun (invEquiv (identityPrinciple {a = X} {b = Y}))
              (sym A≡X ∙ pr-inj {a = A} {b = B} {c = z} {d = z} e .fst
                ∙ sym (pr-inj {a = A} {b = B} {c = z} {d = z} e .snd) ∙ B≡Y)
      bwd : ⟨ w ∈ˢ eqSepOp X Y Z ⟩ → ⟨ pr d w ∈ˢ cap Rc (F2 P Wc) ⟩
      bwd h = cap-in Rc (F2 P Wc) (pr d w) inRc
        (F2-write P Wc (pr d w) ∣ d , w , (d∈P , w∈Wc , refl) ∣₁)
        where
        parts : ⟨ w ∈ₛ Z ⟩ × ⟨ X ∼ Y ⟩
        parts = eqSepSpec X Y Z w .fst (∈s w (eqSepOp X Y Z) h)
        inRc : ⟨ pr d w ∈ˢ Rc ⟩
        inRc = sc d w d∈ .snd (∈S w Z (parts .fst))
        w∈Wc : ⟨ w ∈ˢ Wc ⟩
        w∈Wc = vals-union Rc D d w d∈ inRc
        X≡Y : X ≡ Y
        X≡Y = equivFun (identityPrinciple {a = X} {b = Y}) (parts .snd)
        d∈P : ⟨ d ∈ˢ P ⟩
        d∈P = test-in (GA .fst) (GB .fst) (idG Q) D WA WB d X Y d∈ dX∈ dY∈
          X∈WA Y∈WB
          (subst (λ z → ⟨ pr X z ∈ˢ idG Q ⟩) X≡Y
            (idG-in Q X (cup-in WA WB X ∣ inl X∈WA ∣₁)))
```

<!--en-->
The nested image is the clause the restatement exists for. Its inner composite
is evaluated at a stack whose head is the inner argument and whose tail is the
outer record's, so the induction hypothesis is taken at a new record set: the
pairs of an outer record with an inner argument. The two projection graphs
supply the new argument families, and the outer relation is the composition of
the left projection with the inner graph.
<!--zh-->
嵌套的像正是重述为之存在的那条子句。其内层复合在这样的栈上求值：栈首是内层自变量，栈尾是外层记录的那些自变量，故归纳假设取在一个新的记录集上，即外层记录与内层自变量所成的对。两个投影图供应新的自变量族，外层关系则是左投影与内层图之复合。
<!--/-->

```agda
  liftGraphs : {k : ℕ} → Vec (V ℓ) k → V ℓ → V ℓ → V ℓ → Vec (V ℓ) k
  liftGraphs [] L D' D = []
  liftGraphs (Γ ∷ Γs) L D' D =
    comp L Γ D' (F5 (vals Γ D) (vals Γ D)) ∷ liftGraphs Γs L D' D

  liftArgs : {k : ℕ} (gs : Vec (V ℓ → V ℓ) k) (Γs : Vec (V ℓ) k) (D D' L : V ℓ)
           → InJ D → InJ D' → InJ L
           → ((e : V ℓ) → ⟨ e ∈ˢ D' ⟩
              → ⟨ pr (prL e) e ∈ˢ L ⟩ × ⟨ prL e ∈ˢ D ⟩)
           → ((e u t : V ℓ) → ⟨ e ∈ˢ D' ⟩ → ⟨ pr u t ∈ˢ L ⟩ → ⟨ t ≡ₕ e ⟩
              → u ≡ prL e)
           → Args gs Γs D → Args (shiftAt gs) (liftGraphs Γs L D' D) D'
  liftArgs [] [] D D' L hD hD' hL lin lout args = tt*
  liftArgs (g ∷ gs) (Γ ∷ Γs) D D' L hD hD' hL lin lout ((hΓ , gr) , rest) =
    ( J-comp L Γ D' Wv hL hΓ hD' hWv , spec )
    , liftArgs gs Γs D D' L hD hD' hL lin lout rest
    where
    Wv : V ℓ
    Wv = F5 (vals Γ D) (vals Γ D)
    hWv : InJ Wv
    hWv = J-F5 (vals Γ D) (vals Γ D) hv hv
      where
      hv : InJ (vals Γ D)
      hv = J-vals Γ D hΓ hD
    spec : IsGraph (λ e → g (prL e)) (comp L Γ D' Wv) D'
    spec e w e∈ = fwd , bwd
      where
      fwd : ⟨ pr e w ∈ˢ comp L Γ D' Wv ⟩ → w ≡ g (prL e)
      fwd h = PT.rec (setIsSet w (g (prL e))) go (comp-out L Γ D' Wv (pr e w) h)
        where
        go : Σ[ m ∈ V ℓ ] Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ]
               (⟨ pr m u ∈ˢ L ⟩ × ⟨ pr m v ∈ˢ Γ ⟩ × ⟨ pr e w ≡ₕ pr u v ⟩)
           → w ≡ g (prL e)
        go (m , u , v , mu∈ , mv∈ , eq) =
          w≡v ∙ gr m v m∈D .fst mv∈ ∙ cong g m≡
          where
          e≡u : e ≡ u
          e≡u = pr-inj {a = e} {b = w} {c = u} {d = v} eq .fst
          w≡v : w ≡ v
          w≡v = pr-inj {a = e} {b = w} {c = u} {d = v} eq .snd
          m≡ : m ≡ prL e
          m≡ = lout e m u e∈ mu∈ (sym e≡u)
          m∈D : ⟨ m ∈ˢ D ⟩
          m∈D = subst (λ y → ⟨ y ∈ˢ D ⟩) (sym m≡) (lin e e∈ .snd)
      bwd : w ≡ g (prL e) → ⟨ pr e w ∈ˢ comp L Γ D' Wv ⟩
      bwd eq = comp-in L Γ D' Wv (prL e) e w (lin e e∈ .fst) inΓ e∈
        (vals-union Γ D (prL e) w (lin e e∈ .snd) inΓ)
        where
        inΓ : ⟨ pr (prL e) w ∈ˢ Γ ⟩
        inΓ = gr (prL e) w (lin e e∈ .snd) .snd eq

  elem-imgC : {k : ℕ} (g : Comp (suc k)) (a : Comp k) (gs : Vec (V ℓ → V ℓ) k)
              (Γs : Vec (V ℓ) k) (D : V ℓ) → Args gs Γs D → InJ D
            → ElemRel a gs D
            → ((D' : V ℓ) (gs' : Vec (V ℓ → V ℓ) (suc k))
               (Γs' : Vec (V ℓ) (suc k))
               → Args gs' Γs' D' → InJ D' → ElemRel g gs' D')
            → ElemRel (imgC g a) gs D
  elem-imgC {k} g a gs Γs D args hD (Ra , hRa , sa) IHg =
    comp (lproj D' X) Γ' D Ww , (hR , spec)
    where
    Wt : V ℓ
    Wt = F5 (vals Ra D) (vals Ra D)
    hWt : InJ Wt
    hWt = J-F5 (vals Ra D) (vals Ra D) hv hv
      where
      hv : InJ (vals Ra D)
      hv = J-vals Ra D hRa hD
    D' : V ℓ
    D' = cap Ra (F2 D Wt)
    hD' : InJ D'
    hD' = J-cap Ra (F2 D Wt) hRa (J-F2 D Wt hD hWt)
    X : V ℓ
    X = cup D Wt
    hX : InJ X
    hX = J-cup D Wt hD hWt
    D'-in : (d t : V ℓ) → ⟨ d ∈ˢ D ⟩ → ⟨ pr d t ∈ˢ Ra ⟩ → ⟨ pr d t ∈ˢ D' ⟩
    D'-in d t d∈ h = cap-in Ra (F2 D Wt) (pr d t) h
      (F2-write D Wt (pr d t)
        ∣ d , t , (d∈ , vals-union Ra D d t d∈ h , refl) ∣₁)
    D'-out : (e : V ℓ) → ⟨ e ∈ˢ D' ⟩
           → ∥ Σ[ d ∈ V ℓ ] Σ[ t ∈ V ℓ ]
                (⟨ d ∈ˢ D ⟩ × ⟨ t ∈ˢ Wt ⟩ × ⟨ pr d t ∈ˢ Ra ⟩ × ⟨ e ≡ₕ pr d t ⟩)
              ∥₁
    D'-out e h = PT.rec squash₁ go (F2-read D Wt e (cap-outr Ra (F2 D Wt) e h))
      where
      go : Σ[ d ∈ V ℓ ] Σ[ t ∈ V ℓ ]
             (⟨ d ∈ˢ D ⟩ × ⟨ t ∈ˢ Wt ⟩ × ⟨ e ≡ₕ pr d t ⟩)
         → ∥ Σ[ d ∈ V ℓ ] Σ[ t ∈ V ℓ ]
              (⟨ d ∈ˢ D ⟩ × ⟨ t ∈ˢ Wt ⟩ × ⟨ pr d t ∈ˢ Ra ⟩ × ⟨ e ≡ₕ pr d t ⟩)
            ∥₁
      go (d , t , d∈ , t∈ , e≡) = ∣ d , t
        , ( d∈ , t∈
          , subst (λ y → ⟨ y ∈ˢ Ra ⟩) e≡ (cap-outl Ra (F2 D Wt) e h)
          , e≡ ) ∣₁
    inX-l : (d t : V ℓ) → ⟨ d ∈ˢ D ⟩ → ⟨ d ∈ˢ X ⟩
    inX-l d t d∈ = cup-in D Wt d ∣ inl d∈ ∣₁
    inX-r : (t : V ℓ) → ⟨ t ∈ˢ Wt ⟩ → ⟨ t ∈ˢ X ⟩
    inX-r t t∈ = cup-in D Wt t ∣ inr t∈ ∣₁
    lin1 : (e : V ℓ) → ⟨ e ∈ˢ D' ⟩ → ⟨ pr (prL e) e ∈ˢ lpg D' X ⟩
    lin1 e e∈ = PT.rec (snd (pr (prL e) e ∈ˢ lpg D' X)) go (D'-out e e∈)
      where
      go : Σ[ d ∈ V ℓ ] Σ[ t ∈ V ℓ ]
             (⟨ d ∈ˢ D ⟩ × ⟨ t ∈ˢ Wt ⟩ × ⟨ pr d t ∈ˢ Ra ⟩ × ⟨ e ≡ₕ pr d t ⟩)
         → ⟨ pr (prL e) e ∈ˢ lpg D' X ⟩
      go (d , t , d∈ , t∈ , dt∈ , e≡) =
        subst (λ y → ⟨ pr (prL y) y ∈ˢ lpg D' X ⟩) (sym e≡)
          (subst (λ y → ⟨ pr y (pr d t) ∈ˢ lpg D' X ⟩) (sym (prL-pair d t))
            (lpg-in D' X d t (D'-in d t d∈ dt∈) (inX-l d t d∈) (inX-r t t∈)))

    lin2 : (e : V ℓ) → ⟨ e ∈ˢ D' ⟩ → ⟨ prL e ∈ˢ D ⟩
    lin2 e e∈ = PT.rec (snd (prL e ∈ˢ D)) go (D'-out e e∈)
      where
      go : Σ[ d ∈ V ℓ ] Σ[ t ∈ V ℓ ]
             (⟨ d ∈ˢ D ⟩ × ⟨ t ∈ˢ Wt ⟩ × ⟨ pr d t ∈ˢ Ra ⟩ × ⟨ e ≡ₕ pr d t ⟩)
         → ⟨ prL e ∈ˢ D ⟩
      go (d , t , d∈ , t∈ , dt∈ , e≡) = subst (λ y → ⟨ y ∈ˢ D ⟩)
        (sym (cong prL e≡ ∙ prL-pair d t)) d∈

    lin : (e : V ℓ) → ⟨ e ∈ˢ D' ⟩
        → ⟨ pr (prL e) e ∈ˢ lpg D' X ⟩ × ⟨ prL e ∈ˢ D ⟩
    lin e e∈ = lin1 e e∈ , lin2 e e∈
    lout : (e u t : V ℓ) → ⟨ e ∈ˢ D' ⟩ → ⟨ pr u t ∈ˢ lpg D' X ⟩ → ⟨ t ≡ₕ e ⟩
         → u ≡ prL e
    lout e u t e∈ ut∈ t≡e = PT.rec (setIsSet u (prL e)) go (lpg-out D' X u t ut∈)
      where
      go : Σ[ s ∈ V ℓ ] (⟨ pr u s ∈ˢ D' ⟩ × ⟨ t ≡ₕ pr u s ⟩) → u ≡ prL e
      go (s , us∈ , t≡) = sym (cong prL (sym t≡e ∙ t≡) ∙ prL-pair u s)
    gs' : Vec (V ℓ → V ℓ) (suc k)
    gs' = prR ∷ shiftAt gs
    Γs' : Vec (V ℓ) (suc k)
    Γs' = rproj D' X ∷ liftGraphs Γs (lpg D' X) D' D
    args' : Args gs' Γs' D'
    args' = ( J-rproj D' X hD' hX , rspec )
          , liftArgs gs Γs D D' (lpg D' X) hD hD' (J-lpg D' X hD' hX) lin lout args
      where
      rspec : IsGraph prR (rproj D' X) D'
      rspec e w e∈ = fwd , bwd
        where
        fwd : ⟨ pr e w ∈ˢ rproj D' X ⟩ → w ≡ prR e
        fwd h = PT.rec (setIsSet w (prR e)) go (rproj-out D' X e w h)
          where
          go : Σ[ d ∈ V ℓ ] (⟨ pr d w ∈ˢ D' ⟩ × ⟨ e ≡ₕ pr d w ⟩) → w ≡ prR e
          go (d , dw∈ , e≡) = sym (cong prR e≡ ∙ prR-pair d w)
        bwd : w ≡ prR e → ⟨ pr e w ∈ˢ rproj D' X ⟩
        bwd eq = PT.rec (snd (pr e w ∈ˢ rproj D' X)) go (D'-out e e∈)
          where
          go : Σ[ d ∈ V ℓ ] Σ[ t ∈ V ℓ ]
                 (⟨ d ∈ˢ D ⟩ × ⟨ t ∈ˢ Wt ⟩ × ⟨ pr d t ∈ˢ Ra ⟩ × ⟨ e ≡ₕ pr d t ⟩)
             → ⟨ pr e w ∈ˢ rproj D' X ⟩
          go (d , t , d∈ , t∈ , dt∈ , e≡) =
            subst (λ y → ⟨ pr y w ∈ˢ rproj D' X ⟩) (sym e≡)
              (subst (λ y → ⟨ pr (pr d t) y ∈ˢ rproj D' X ⟩) (sym w≡t)
                (rproj-in D' X d t (D'-in d t d∈ dt∈) (inX-l d t d∈) (inX-r t t∈)))
            where
            w≡t : w ≡ t
            w≡t = eq ∙ cong prR e≡ ∙ prR-pair d t
    EL' : ElemRel g gs' D'
    EL' = IHg D' gs' Γs' args' hD'
    GG : Σ[ Γ ∈ V ℓ ] (InJ Γ × IsGraph (λ e → evalC g (appAt gs' e)) Γ D')
    GG = graphOf g gs' D' hD' EL'
    Γ' : V ℓ
    Γ' = GG .fst
    Ww : V ℓ
    Ww = F5 (vals Γ' D') (vals Γ' D')
    hWw : InJ Ww
    hWw = J-F5 (vals Γ' D') (vals Γ' D') hv hv
      where
      hv : InJ (vals Γ' D')
      hv = J-vals Γ' D' (GG .snd .fst) hD'
    hR : InJ (comp (lproj D' X) Γ' D Ww)
    hR = J-comp (lproj D' X) Γ' D Ww (J-lproj D' X hD' hX) (GG .snd .fst) hD hWw
    spec : IsElemRel (imgC g a) gs D (comp (lproj D' X) Γ' D Ww)
    spec d w d∈ = fwd , bwd
      where
      Av : V ℓ
      Av = evalC a (appAt gs d)
      Goal : Type (ℓ-suc ℓ)
      Goal = ⟨ w ∈ˢ evalC (imgC g a) (appAt gs d) ⟩
      fwd : ⟨ pr d w ∈ˢ comp (lproj D' X) Γ' D Ww ⟩ → Goal
      fwd h = PT.rec (snd (w ∈ˢ evalC (imgC g a) (appAt gs d))) outer
        (comp-out (lproj D' X) Γ' D Ww (pr d w) h)
        where
        outer : Σ[ m ∈ V ℓ ] Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ]
                  (⟨ pr m u ∈ˢ lproj D' X ⟩ × ⟨ pr m v ∈ˢ Γ' ⟩
                   × ⟨ pr d w ≡ₕ pr u v ⟩)
              → Goal
        outer (m , u , v , mu∈ , mv∈ , eq) = PT.rec
          (snd (w ∈ˢ evalC (imgC g a) (appAt gs d))) inner
          (lproj-out D' X m u mu∈)
          where
          d≡u : d ≡ u
          d≡u = pr-inj {a = d} {b = w} {c = u} {d = v} eq .fst
          w≡v : w ≡ v
          w≡v = pr-inj {a = d} {b = w} {c = u} {d = v} eq .snd
          inner : Σ[ t ∈ V ℓ ] (⟨ pr u t ∈ˢ D' ⟩ × ⟨ m ≡ₕ pr u t ⟩) → Goal
          inner (t , ut∈ , m≡) = ∣ fib .fst , path ∣₁
            where
            dt∈D' : ⟨ pr d t ∈ˢ D' ⟩
            dt∈D' = subst (λ y → ⟨ pr y t ∈ˢ D' ⟩) (sym d≡u) ut∈
            t∈A : ⟨ t ∈ˢ Av ⟩
            t∈A = sa d t d∈ .fst (cap-outl Ra (F2 D Wt) (pr d t) dt∈D')
            fib : Σ[ n ∈ ⟪ Av ⟫ ] (⟪ Av ⟫↪ n ≡ t)
            fib = ∈-asFiber {a = t} {b = Av} t∈A
            v≡ : v ≡ evalC g (t ∷ appAt gs d)
            v≡ = GG .snd .snd m v (subst (λ y → ⟨ y ∈ˢ D' ⟩) (sym m≡) ut∈) .fst mv∈
               ∙ cong (λ y → evalC g (appAt gs' y)) m≡
               ∙ cong (evalC g) (appAt-pair gs u t)
               ∙ cong (λ y → evalC g (t ∷ appAt gs y)) (sym d≡u)
            path : evalC g (⟪ Av ⟫↪ (fib .fst) ∷ appAt gs d) ≡ w
            path = cong (λ y → evalC g (y ∷ appAt gs d)) (fib .snd)
                 ∙ sym v≡ ∙ sym w≡v
      bwd : Goal → ⟨ pr d w ∈ˢ comp (lproj D' X) Γ' D Ww ⟩
      bwd h = PT.rec (snd (pr d w ∈ˢ comp (lproj D' X) Γ' D Ww)) go h
        where
        go : Σ[ n ∈ ⟪ Av ⟫ ] (evalC g (⟪ Av ⟫↪ n ∷ appAt gs d) ≡ w)
           → ⟨ pr d w ∈ˢ comp (lproj D' X) Γ' D Ww ⟩
        go (n , path) = comp-in (lproj D' X) Γ' D Ww (pr d t) d w
          (lproj-in D' X d t dt∈D' (inX-l d t d∈) (inX-r t t∈Wt))
          inΓ' d∈ (vals-union Γ' D' (pr d t) w dt∈D' inΓ')
          where
          t : V ℓ
          t = ⟪ Av ⟫↪ n
          t∈A : ⟨ t ∈ˢ Av ⟩
          t∈A = ∈S t Av (∈ₛ⟪ Av ⟫↪ n)
          dt∈Ra : ⟨ pr d t ∈ˢ Ra ⟩
          dt∈Ra = sa d t d∈ .snd t∈A
          t∈Wt : ⟨ t ∈ˢ Wt ⟩
          t∈Wt = vals-union Ra D d t d∈ dt∈Ra
          dt∈D' : ⟨ pr d t ∈ˢ D' ⟩
          dt∈D' = D'-in d t d∈ dt∈Ra
          inΓ' : ⟨ pr (pr d t) w ∈ˢ Γ' ⟩
          inΓ' = GG .snd .snd (pr d t) w dt∈D' .snd
            (sym path ∙ sym (cong (evalC g) (appAt-pair gs d t)))
```

<!--en-->
## The induction, and the discharge

The ten clauses assemble into one structural recursion on the composite. Its
instance at the one-slot stack is the image principle the switch chapter's
closure side asks for: take the record set to be the set being ranged over
itself, the identity graph for the separated variable, and a product for each
witness-stack constant. With it the switch chapter's conditional module is
instantiated with nothing left over, so the closure direction of the switch
theorem is unconditional.
<!--zh-->
## 归纳与兑付

十条子句合为复合上的一次结构递归。它在单槽栈处的实例正是切换章闭包一侧所要的像原理：取记录集为被遍历的那个集合自身、被分离变量取恒等图、见证栈的每个常量取一个积。有了它，切换章的条件模块被兑付得一无所剩，于是切换定理的闭包方向是无条件的。
<!--/-->

```agda
  elemRel : {k : ℕ} (f : Comp k) (gs : Vec (V ℓ → V ℓ) k) (Γs : Vec (V ℓ) k)
            (D : V ℓ) → ConIn InJ f → Args gs Γs D → InJ D → ElemRel f gs D
  elemRel (conC x) gs Γs D hc args hD = elem-conC x gs D hc hD
  elemRel (varC i) gs Γs D hc args hD = elem-varC i gs Γs D args hD
  elemRel (interC a b) gs Γs D (ha , hb) args hD = elem-interC a b gs D
    (elemRel a gs Γs D ha args hD) (elemRel b gs Γs D hb args hD)
  elemRel (diffC a b) gs Γs D (ha , hb) args hD = elem-diffC a b gs D
    (elemRel a gs Γs D ha args hD) (elemRel b gs Γs D hb args hD)
  elemRel (unionC a) gs Γs D ha args hD = elem-unionC a gs D
    (elemRel a gs Γs D ha args hD)
  elemRel (pairC a b) gs Γs D (ha , hb) args hD = elem-pairC a b gs D hD
    (elemRel a gs Γs D ha args hD) (elemRel b gs Γs D hb args hD)
  elemRel (colC a b) gs Γs D (ha , hb) args hD = elem-colC a b gs D hD
    (elemRel a gs Γs D ha args hD) (elemRel b gs Γs D hb args hD)
  elemRel (chSepC a b c) gs Γs D (ha , hb , hc) args hD = elem-chSepC a b c gs D hD
    (elemRel a gs Γs D ha args hD) (elemRel b gs Γs D hb args hD)
    (elemRel c gs Γs D hc args hD)
  elemRel (eqSepC a b c) gs Γs D (ha , hb , hc) args hD = elem-eqSepC a b c gs D hD
    (elemRel a gs Γs D ha args hD) (elemRel b gs Γs D hb args hD)
    (elemRel c gs Γs D hc args hD)
  elemRel (imgC g a) gs Γs D (hg , ha) args hD = elem-imgC g a gs Γs D args hD
    (elemRel a gs Γs D ha args hD)
    (λ D' gs' Γs' args' hD' → elemRel g gs' Γs' D' hg args' hD')

  constArgs : {k : ℕ} (vs : Vec (V ℓ) k) (p : V ℓ) → InJ p → AllIn InJ vs
            → Args (constFams vs) (constGraphs p vs) p
  constArgs [] p hp hvs = tt*
  constArgs (v ∷ vs) p hp (hv , hvs) =
    ( J-F2 p (F0 v v) hp (J-F0 v v hv hv) , spec ) , constArgs vs p hp hvs
    where
    spec : IsGraph (λ _ → v) (F2 p (F0 v v)) p
    spec d w d∈ = fwd , bwd
      where
      fwd : ⟨ pr d w ∈ˢ F2 p (F0 v v) ⟩ → w ≡ v
      fwd h = PT.rec (setIsSet w v) (Sum.rec (λ e → e) (λ e → e))
        (F0-spec v v w .fst (constRel p (F0 v v) d w d∈ .fst h))
      bwd : w ≡ v → ⟨ pr d w ∈ˢ F2 p (F0 v v) ⟩
      bwd e = constRel p (F0 v v) d w d∈ .snd (F0-spec v v w .snd ∣ inl e ∣₁)

  topArgs : {k : ℕ} (p : V ℓ) (vs : Vec (V ℓ) k) → InJ p → AllIn InJ vs
          → Args ((λ y → y) ∷ constFams vs) (idG p ∷ constGraphs p vs) p
  topArgs p vs hp hvs = ( J-idG p hp , idSpec ) , constArgs vs p hp hvs
    where
    idSpec : IsGraph (λ y → y) (idG p) p
    idSpec d w d∈ = fwd , bwd
      where
      fwd : ⟨ pr d w ∈ˢ idG p ⟩ → w ≡ d
      fwd h = PT.rec (setIsSet w d) go (idG-out p (pr d w) h)
        where
        go : Σ[ z ∈ V ℓ ] (⟨ z ∈ˢ p ⟩ × ⟨ pr d w ≡ₕ pr z z ⟩) → w ≡ d
        go (z , _ , e) = pr-inj {a = d} {b = w} {c = z} {d = z} e .snd
                       ∙ sym (pr-inj {a = d} {b = w} {c = z} {d = z} e .fst)
      bwd : w ≡ d → ⟨ pr d w ∈ˢ idG p ⟩
      bwd e = subst (λ y → ⟨ pr d y ∈ˢ idG p ⟩) (sym e) (idG-in p d d∈)

  Jimg : {k : ℕ} (f : Comp (suc k)) (vs : Vec (V ℓ) k) (p : V ℓ)
       → ConIn InJ f → AllIn InJ vs → InJ p → InJ (imgOpC f vs p)
  Jimg f vs p hf hvs hp = subst InJ (sym eq) (J-F8 R p hR hp)
    where
    E : ElemRel f ((λ y → y) ∷ constFams vs) p
    E = elemRel f ((λ y → y) ∷ constFams vs) (idG p ∷ constGraphs p vs) p hf
          (topArgs p vs hp hvs) hp
    R : V ℓ
    R = E .fst
    hR : InJ R
    hR = E .snd .fst
    ev : (y : V ℓ) → appAt ((λ y → y) ∷ constFams vs) y ≡ (y ∷ vs)
    ev y = cong (y ∷_) (appAt-const vs y)
    eq : imgOpC f vs p ≡ F8 R p
    eq = img-of-rel R p (λ y → evalC f (y ∷ vs))
      (λ y w y∈ h → subst (λ z → ⟨ w ∈ˢ evalC f z ⟩) (ev y)
        (E .snd .snd y w y∈ .fst h))
      (λ y w y∈ h → E .snd .snd y w y∈ .snd
        (subst (λ z → ⟨ w ∈ˢ evalC f z ⟩) (sym (ev y)) h))

  module Discharge where
    open Eval-J Jimg public
```

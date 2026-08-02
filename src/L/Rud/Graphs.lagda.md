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
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett )

module L.Rud.Graphs {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Rud.Ops {ℓ}
  using ( F0; F0-spec; F1; F1-spec; F2; F2-read; F2-write
        ; F3; F3-read; F3-write; F4; F4-read; F4-write
        ; F5; F5-spec; F6; F6-write; F7; F7-read; F7-write )
open import L.Rud.Images {ℓ} using ( F8; F8-spec; F10; F10-spec )
open import L.Rud.Step {ℓ} lem A
  using ( Op16; f3; f4; f8; Fof; Fof-f3; Fof-f4; Fof-f8 )
open import L.Rud.Switch {ℓ} lem A
  using ( dne; ∈s; ∈S; evalC; imgOpC; ConIn; AllIn; lookupIn
        ; interOp; interSpec; unionOp; unionSpec; module Bs; module Closure )
open Bs using ( Comp; conC; varC; interC; diffC; unionC )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; _≡ₕ_; _⊆_; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber; extensionality )
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
## What the image residue reduces to

The switch chapter's one standing hypothesis asks that a closed level absorb
the image of a composite family. With the extraction equation above, that
hypothesis reduces to a single principle about element relations: if every
composite family over a closed level has an element relation inside the
level, the image is inside the level too, in the hypothesis's own type. The
reduction is stated first as a lemma at one family, then as the implication
that discharges the hypothesis verbatim, and finally by instantiating the
switch chapter's own conditional module with it, which is what checks that
the two types agree on the nose.
<!--zh-->
## 像的存留归约为什么

切换章唯一悬置的假设要求封闭层吸收复合族之像。有了上面的提取方程，该假设归约为关于元素关系的一条原理：若封闭层上的每个复合族都有一个落在层内的元素关系，则像也落在层内，且落在该假设自身的类型中。归约先以单个族上的引理陈述，再以逐字兑付该假设的蕴含式陈述，最后用它实例化切换章自己的条件模块，这一步正是对两个类型严丝合缝的检验。
<!--/-->

```agda
  IsElemRel : {k : ℕ} → Comp (suc k) → Vec (V ℓ) k → V ℓ → V ℓ
            → Type (ℓ-suc ℓ)
  IsElemRel f vs p R = (y w : V ℓ) → ⟨ y ∈ˢ p ⟩
    → (⟨ pr y w ∈ˢ R ⟩ → ⟨ w ∈ˢ evalC f (y ∷ vs) ⟩)
    × (⟨ w ∈ˢ evalC f (y ∷ vs) ⟩ → ⟨ pr y w ∈ˢ R ⟩)

  ElemRel : {k : ℕ} → Comp (suc k) → Vec (V ℓ) k → V ℓ → Type (ℓ-suc ℓ)
  ElemRel f vs p = Σ[ R ∈ V ℓ ] (InJ R × IsElemRel f vs p R)

  img-from-rel : {k : ℕ} (f : Comp (suc k)) (vs : Vec (V ℓ) k) (p R : V ℓ)
               → InJ R → InJ p → IsElemRel f vs p R → InJ (imgOpC f vs p)
  img-from-rel f vs p R hR hp spec =
    subst InJ (sym (img-of-rel R p (λ y → evalC f (y ∷ vs))
      (λ y w y∈ → spec y w y∈ .fst) (λ y w y∈ → spec y w y∈ .snd)))
      (J-F8 R p hR hp)

  ElemRelPrinciple : Type (ℓ-suc ℓ)
  ElemRelPrinciple = {k : ℕ} (f : Comp (suc k)) (vs : Vec (V ℓ) k) (p : V ℓ)
                   → ConIn InJ f → AllIn InJ vs → InJ p → ElemRel f vs p

  elemRel→Jimg : ElemRelPrinciple
               → {k : ℕ} (f : Comp (suc k)) (vs : Vec (V ℓ) k) (p : V ℓ)
               → ConIn InJ f → AllIn InJ vs → InJ p → InJ (imgOpC f vs p)
  elemRel→Jimg principle f vs p hf hvs hp =
    img-from-rel f vs p (E .fst) (E .snd .fst) hp (E .snd .snd)
    where
    E : ElemRel f vs p
    E = principle f vs p hf hvs hp

  module Discharge (principle : ElemRelPrinciple) where
    open Eval-J (elemRel→Jimg principle) public
```

<!--en-->
## The cases that close

The element-relation principle is an induction over the composite syntax, and
the calculus above closes five of its ten clauses outright. A constant and a
witness-stack slot are products, because the value does not depend on the
argument; the separated variable itself is the converse membership relation,
which is where the identity graph is spent; and intersection and difference
are the same operations one level up, because an element relation carries
members rather than values. The clauses that remain need the graph form and
are recorded in the batch report.
<!--zh-->
## 就此封口的情形

元素关系原理是复合语法上的一个归纳，上面的演算径直封住其十条子句中的五条。常量与见证栈的一格是积，因为值不依赖于自变量；被分离的变量自身是逆隶属关系，恒等图正花在此处；交与差则是高一层的同名运算，因为元素关系携带的是成员而非值。其余子句需要图形式，记录在本批次报告中。
<!--/-->

```agda
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

selfRel : (p y w : V ℓ) → ⟨ y ∈ˢ p ⟩
        → (⟨ pr y w ∈ˢ swp (mrel (amb p)) (amb p) ⟩ → ⟨ w ∈ˢ y ⟩)
        × (⟨ w ∈ˢ y ⟩ → ⟨ pr y w ∈ˢ swp (mrel (amb p)) (amb p) ⟩)
selfRel p y w y∈ = fwd , bwd
  where
  fwd : ⟨ pr y w ∈ˢ swp (mrel (amb p)) (amb p) ⟩ → ⟨ w ∈ˢ y ⟩
  fwd h = PT.rec (snd (w ∈ˢ y)) go
    (swp-out (mrel (amb p)) (amb p) (pr y w) h)
    where
    go : Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ]
           (⟨ pr u v ∈ˢ mrel (amb p) ⟩ × ⟨ pr y w ≡ₕ pr v u ⟩)
       → ⟨ w ∈ˢ y ⟩
    go (u , v , uv∈ , e) = subst (λ t → ⟨ t ∈ˢ y ⟩)
      (sym (pr-inj {a = y} {b = w} {c = v} {d = u} e .snd))
      (subst (λ t → ⟨ u ∈ˢ t ⟩)
        (sym (pr-inj {a = y} {b = w} {c = v} {d = u} e .fst))
        (mrel-out (amb p) u v uv∈))
  bwd : ⟨ w ∈ˢ y ⟩ → ⟨ pr y w ∈ˢ swp (mrel (amb p)) (amb p) ⟩
  bwd h = swp-in (mrel (amb p)) (amb p) w y
    (mrel-in (amb p) w y (amb-mem p y w y∈ h) (amb-self p y y∈) h)
    (amb-mem p y w y∈ h) (amb-self p y y∈)
```

```agda
module Cases (J : V ℓ)
  (Jrud : (i : Op16) (a b : V ℓ) → ⟨ a ∈ˢ J ⟩ → ⟨ b ∈ˢ J ⟩ → ⟨ Fof i a b ∈ˢ J ⟩)
  where

  open Kit J Jrud public

  elem-conC : {k : ℕ} (x : V ℓ) (vs : Vec (V ℓ) k) (p : V ℓ) → InJ x → InJ p
            → ElemRel (conC x) vs p
  elem-conC x vs p hx hp = F2 p x , (J-F2 p x hp hx , λ y w y∈ → constRel p x y w y∈)

  elem-varZ : {k : ℕ} (vs : Vec (V ℓ) k) (p : V ℓ) → InJ p
            → ElemRel (varC zero) vs p
  elem-varZ vs p hp = swp (mrel (amb p)) (amb p)
    , ( J-swp (mrel (amb p)) (amb p) (J-mrel (amb p) (J-amb p hp)) (J-amb p hp)
      , λ y w y∈ → selfRel p y w y∈ )

  elem-varS : {k : ℕ} (i : Fin k) (vs : Vec (V ℓ) k) (p : V ℓ)
            → AllIn InJ vs → InJ p → ElemRel (varC (suc i)) vs p
  elem-varS i vs p hvs hp = F2 p (lookup i vs)
    , ( J-F2 p (lookup i vs) hp (lookupIn InJ i vs hvs)
      , λ y w y∈ → constRel p (lookup i vs) y w y∈ )

  elem-diffC : {k : ℕ} (a b : Comp (suc k)) (vs : Vec (V ℓ) k) (p : V ℓ)
             → ElemRel a vs p → ElemRel b vs p → ElemRel (diffC a b) vs p
  elem-diffC a b vs p (Ra , hRa , sa) (Rb , hRb , sb) =
    F1 Ra Rb , (J-F1 Ra Rb hRa hRb , spec)
    where
    spec : IsElemRel (diffC a b) vs p (F1 Ra Rb)
    spec y w y∈ = fwd , bwd
      where
      X : V ℓ
      X = evalC a (y ∷ vs)
      Y : V ℓ
      Y = evalC b (y ∷ vs)
      fwd : ⟨ pr y w ∈ˢ F1 Ra Rb ⟩ → ⟨ w ∈ˢ F1 X Y ⟩
      fwd h = F1-spec X Y w .snd
        ( sa y w y∈ .fst (F1-spec Ra Rb (pr y w) .fst h .fst)
        , λ k → F1-spec Ra Rb (pr y w) .fst h .snd (sb y w y∈ .snd k) )
      bwd : ⟨ w ∈ˢ F1 X Y ⟩ → ⟨ pr y w ∈ˢ F1 Ra Rb ⟩
      bwd h = F1-spec Ra Rb (pr y w) .snd
        ( sa y w y∈ .snd (F1-spec X Y w .fst h .fst)
        , λ k → F1-spec X Y w .fst h .snd (sb y w y∈ .fst k) )

  elem-interC : {k : ℕ} (a b : Comp (suc k)) (vs : Vec (V ℓ) k) (p : V ℓ)
              → ElemRel a vs p → ElemRel b vs p → ElemRel (interC a b) vs p
  elem-interC a b vs p (Ra , hRa , sa) (Rb , hRb , sb) =
    cap Ra Rb , (J-cap Ra Rb hRa hRb , spec)
    where
    spec : IsElemRel (interC a b) vs p (cap Ra Rb)
    spec y w y∈ = fwd , bwd
      where
      X : V ℓ
      X = evalC a (y ∷ vs)
      Y : V ℓ
      Y = evalC b (y ∷ vs)
      fwd : ⟨ pr y w ∈ˢ cap Ra Rb ⟩ → ⟨ w ∈ˢ interOp X Y ⟩
      fwd h = ∈S w (interOp X Y) (interSpec X Y w .snd
        ( ∈s w X (sa y w y∈ .fst (cap-outl Ra Rb (pr y w) h))
        , ∈s w Y (sb y w y∈ .fst (cap-outr Ra Rb (pr y w) h)) ))
      bwd : ⟨ w ∈ˢ interOp X Y ⟩ → ⟨ pr y w ∈ˢ cap Ra Rb ⟩
      bwd h = cap-in Ra Rb (pr y w)
        (sa y w y∈ .snd (∈S w X (interSpec X Y w .fst (∈s w (interOp X Y) h) .fst)))
        (sb y w y∈ .snd (∈S w Y (interSpec X Y w .fst (∈s w (interOp X Y) h) .snd)))
```

```agda
  elem-unionC : {k : ℕ} (a : Comp (suc k)) (vs : Vec (V ℓ) k) (p : V ℓ)
              → ElemRel a vs p → ElemRel (unionC a) vs p
  elem-unionC a vs p (Ra , hRa , sa) = flat Ra , (J-flat Ra hRa , spec)
    where
    spec : IsElemRel (unionC a) vs p (flat Ra)
    spec y w y∈ = fwd , bwd
      where
      X : V ℓ
      X = evalC a (y ∷ vs)
      fwd : ⟨ pr y w ∈ˢ flat Ra ⟩ → ⟨ w ∈ˢ unionOp X ⟩
      fwd h = PT.rec (snd (w ∈ˢ unionOp X)) go (flat-out Ra (pr y w) h)
        where
        go : Σ[ d ∈ V ℓ ] Σ[ v ∈ V ℓ ] Σ[ w' ∈ V ℓ ]
               (⟨ pr d v ∈ˢ Ra ⟩ × ⟨ w' ∈ˢ v ⟩ × ⟨ pr y w ≡ₕ pr d w' ⟩)
           → ⟨ w ∈ˢ unionOp X ⟩
        go (d , v , w' , dv∈ , w'∈ , e) = ∈S w (unionOp X)
          (unionSpec X w .snd ∣ v , (∈s v X v∈X , ∈s w v w∈v) ∣₁)
          where
          v∈X : ⟨ v ∈ˢ X ⟩
          v∈X = sa y v y∈ .fst (subst (λ s → ⟨ pr s v ∈ˢ Ra ⟩)
            (sym (pr-inj {a = y} {b = w} {c = d} {d = w'} e .fst)) dv∈)
          w∈v : ⟨ w ∈ˢ v ⟩
          w∈v = subst (λ s → ⟨ s ∈ˢ v ⟩)
            (sym (pr-inj {a = y} {b = w} {c = d} {d = w'} e .snd)) w'∈
      bwd : ⟨ w ∈ˢ unionOp X ⟩ → ⟨ pr y w ∈ˢ flat Ra ⟩
      bwd h = PT.rec (snd (pr y w ∈ˢ flat Ra)) go
        (unionSpec X w .fst (∈s w (unionOp X) h))
        where
        go : Σ[ v ∈ V ℓ ] (⟨ v ∈ₛ X ⟩ × ⟨ w ∈ₛ v ⟩) → ⟨ pr y w ∈ˢ flat Ra ⟩
        go (v , v∈ , w∈) = flat-in Ra y v w
          (sa y v y∈ .snd (∈S v X v∈)) (∈S w v w∈)
```

<!--en-->
# Describing the closed domain of formula codes

This chapter defines the bounded formula `codesAt` that describes a closed
domain of formula codes. Its shape half recognizes the ten constructors at a
recorded arity, while its closure half requires the immediate term and formula
subkeys of every constructor to remain in the same domain; the alphabet of
constants is supplied separately by `CodeAlphabet`.
<!--zh-->
# 描述封闭的公式码定义域

本章定义有界公式 `codesAt`，用它描述封闭的公式码定义域。形状部分在记录的元数上识别十种构造子，封闭部分则要求每种构造子的直接词项子键与公式子键仍留在同一定义域；常元的字母表由 `CodeAlphabet` 另行提供。
<!--ja-->
# 閉じた論理式符号の定義域を記述する

本章では、閉じた論理式符号の定義域を記述する有界論理式 `codesAt` を定義する。形の部分は記録されたアリティで十個の構成子を識別し、閉性の部分は各構成子の直下にある項と論理式の部分キーが同じ定義域に残ることを要求する。定数のアルファベットは `CodeAlphabet` が別に与える。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module L.Coding.CodeDomain {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using
  ( checkΔ₀; Δ₀ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( prAtL; appAt )
open import L.Coding.Expressions {ℓ} using ( sucAtL )
import L.Coding.Expressions {ℓ} as CodingExpressions
module E = CodingExpressions.PairExpression
open import L.Coding.Quantification {ℓ} using
  ( i0; i1; i2; i3; i4; i5; i6; i7; i8; sh
  ; f0; f1; f2; f3; f4; f5; f6; f7; f8; f9
  ; sndEx; sndAll; bothEx; bothAll; bigOr )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.Unit using ( tt )
open import Cubical.Data.Vec using ( lookup )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_ )

open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ )
```

<!--en-->
This chapter describes the shapes of formula codes and the closure conditions that make structural induction available.
<!--zh-->
本章描述公式码的形状，以及使结构归纳可用的封闭条件。
<!--/-->
<!--en-->
## Describing shape and closure

The description of a code domain has two parts. Every member must have one of the ten constructor shapes at a recorded arity, and every constructor key must bring its immediate term and formula subkeys back into the same domain.
<!--zh-->
## 描述形状与封闭性

码定义域的描述分为两部分：每个成员都必须在某个记录的元数上具有十种构造子形状之一，而每个构造子键的直接词项子键与公式子键都必须回到同一定义域中。
<!--ja-->
## 形と閉性の記述

符号の定義域の記述は二つの部分からなります。各要素は記録されたアリティで十個の構成子の形のいずれかを持ち、各構成子キーの直下にある項と論理式の部分キーは同じ定義域へ戻らなければなりません。
<!--/-->

The code set. `C` is the set of keys `(n, code)` of the formulas over `w` at
every arity. Two clauses in Devlin polarity: every member is a key of one of the
ten shapes, at an arity the tower holds, with its subkeys in `C` and its term
parts over `w` or the arity (soundness reads this by `∈`-induction); and `C` is
closed under the ten code-forming operations (completeness reads this by
induction on the formula).

A term code over the arity `ar` and the carrier `w`: `(N0, x)` with `x` in `w`,
or `(N1, i)` with `i` in `ar`.

```agda
isTm : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Fin m → Formula S m
isTm t ar w N0 N1 =
    sndEx t N0 (var i0 ∈̇ var (sh 2 w))
  ∨̇ sndEx t N1 (var i0 ∈̇ var (sh 2 ar))
```

`(suc ar, r)` is in `C`: some member of `C` is the pair of a successor of `ar`
with `r`.

```agda
keyUp : ∀ {m} → Fin m → Fin m → Fin m → Formula S m
keyUp C ar r =
  ∃̇∈ (var C) (∃̇∈ (var i0) (∃̇∈ (var i0)
    (prAtL i2 i0 (sh 3 r) ∧̇ sucAtL (sh 3 ar) i0)))
```

A key expression records the arity, tag and payload. Its bounded membership
reader and both semantic directions use the structural pair-expression proof.

```agda
keyExpr : ∀ {m} → Fin m → Fin m → E.Expr m → E.Expr m
keyExpr ar N p = E.pair (E.slot ar) (E.pair (E.slot N) p)

atomKeyExpr : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → E.Expr m
atomKeyExpr ar N Nx x Ny y = keyExpr ar N
  (E.pair (E.pair (E.slot Nx) (E.slot x))
    (E.pair (E.slot Ny) (E.slot y)))

bndKeyExpr : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Fin m → E.Expr m
bndKeyExpr ar N Nx x a = keyExpr ar N
  (E.pair (E.pair (E.slot Nx) (E.slot x)) (E.slot a))
```

The unary key `(ar, (N, a))` exists in `C`.

```agda
unKey : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Formula S m
unKey C ar N a = E.member (keyExpr ar N (E.slot a)) (var C)
```

The binary key `(ar, (N, (a, b)))`.

```agda
binKey : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Fin m → Formula S m
binKey C ar N a b = E.member (keyExpr ar N (E.pair (E.slot a) (E.slot b))) (var C)
```

The atom key `(ar, (N, ((Nx, x), (Ny, y))))`.

```agda
atomKey : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → Formula S m
atomKey C ar N Nx x Ny y = E.member (atomKeyExpr ar N Nx x Ny y) (var C)
```

The bounded-quantifier key `(ar, (N, ((Nx, x), a)))`.

```agda
bndKey : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → Formula S m
bndKey C ar N Nx x a = E.member (bndKeyExpr ar N Nx x a) (var C)
```

The tag slots, as one function from the ten positions named in
`L.Coding.Quantification`; `Tags γ N` says those slots hold the corresponding
numerals.

```agda
Tags : ∀ {m} (γ : S ^ m) (N : Fin 10 → Fin m) → Type (ℓ-suc ℓ)
Tags γ N = (k : Fin 10) → fst (lookup (N k) γ) ≡ # (toℕ k)

shN : ∀ {m} (j : ℕ) → (Fin 10 → Fin m) → Fin 10 → Fin (j + m)
shN j N k = sh j (N k)
```

The shape clause. At `r ∷ s'' ∷ p ∷ s' ∷ F ∷ ar ∷ s ∷ q ∷ c ∷ γ` (9 + m): the
payload `r` of the tag `N`, with `ar` at `i5` and `c` at `i8`.

```agda
module Shape {m : ℕ} (C w : Fin m) (N : Fin 10 → Fin m) where
  private
    C9 w9 : Fin (9 + m)
    C9 = sh 9 C
    w9 = sh 9 w

  atomPay binPay conPay quPay bqPay : Formula S (9 + m)
  atomPay = bothEx i0 (isTm i1 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) ∧̇ isTm i0 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)))
  binPay  = bothEx i0 (appAt (sh 12 C) i8 i1 ∧̇ appAt (sh 12 C) i8 i0)
  conPay  = var i0 ≐ var (sh 9 (N f0))
  quPay   = keyUp C9 i5 i0
  bqPay   = bothEx i0 (isTm i1 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) ∧̇ keyUp (sh 12 C) i8 i0)
```

The payload formula of each tag, by the tag's number.

```agda
  payN : ℕ → Formula S (9 + m)
  payN 0 = atomPay
  payN 1 = atomPay
  payN 2 = binPay
  payN 3 = binPay
  payN 4 = binPay
  payN 5 = conPay
  payN 6 = quPay
  payN 7 = quPay
  payN 8 = bqPay
  payN 9 = bqPay
  payN (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) = ⊥̇

  pay : Fin 10 → Formula S (9 + m)
  pay k = payN (toℕ k)
```

At `p ∷ s' ∷ F ∷ ar ∷ s ∷ q ∷ c ∷ γ` (7 + m): `p` is `(N k, r)` for one of the
ten tags, with `r`'s payload condition.

```agda
  at : Fin 10 → Formula S (7 + m)
  at k = sndEx i0 (sh 7 (N k)) (pay k)

  ten : Formula S (7 + m)
  ten = bigOr 9 at
```

Every member of `C` is a key: `∀ c ∈ C`, `∃ (ar, F) ∈ E`, `c = (ar, p)`, `p` one
of the ten.

```agda
shapeAt : ∀ {m} → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
shapeAt C w E N =
  ∀̇∈ (var C) (∃̇∈ (var (sh 1 E)) (bothEx i0 (sndEx i4 i1 (Shape.ten C w N))))
```

The closure clauses, each under `∀ (ar, F) ∈ E`, at `F ∷ ar ∷ s ∷ q ∷ γ`
(4 + m): `ar` at `i1`, `C` at `sh 4 C`, `w` at `sh 4 w`.

```agda
module Close {m : ℕ} (C w : Fin m) (N : Fin 10 → Fin m) where
  private
    C4 w4 : Fin (4 + m)
    C4 = sh 4 C
    w4 = sh 4 w
```

`X` and `Y` are bounds at 4 + m and 5 + m: the carrier or the arity.

```agda
  atomClose : (k Nx Ny : Fin 10) (X : Fin (4 + m)) (Y : Fin (5 + m)) → Formula S (4 + m)
  atomClose k Nx Ny X Y =
    ∀̇∈ (var X) (∀̇∈ (var Y) (atomKey (sh 6 C) i3 (sh 6 (N k)) (sh 6 (N Nx)) i1 (sh 6 (N Ny)) i0))

  binClose : (k : Fin 10) → Formula S (4 + m)
  binClose k =
    ∀̇∈ (var C4) (sndAll i0 i2 (∀̇∈ (var (sh 7 C)) (sndAll i0 i5 (binKey (sh 10 C) i7 (sh 10 (N k)) i3 i0))))

  conClose : (k : Fin 10) → Formula S (4 + m)
  conClose k = unKey C4 i1 (sh 4 (N k)) (sh 4 (N f0))
```

At `a ∷ ar' ∷ s ∷ c₁ ∷ F ∷ ar ∷ s ∷ q ∷ γ` (8 + m): `ar` at `i5`, `ar'` at
`i1`.

```agda
  quClose : (k : Fin 10) → Formula S (4 + m)
  quClose k = ∀̇∈ (var C4) (bothAll i0 (sucAtL i5 i1 ⇒̇ unKey (sh 8 C) i5 (sh 8 (N k)) i0))

  bqClose : (k Nx : Fin 10) (X : Fin (8 + m)) → Formula S (4 + m)
  bqClose k Nx X =
    ∀̇∈ (var C4) (bothAll i0 (sucAtL i5 i1 ⇒̇ ∀̇∈ (var X) (bndKey (sh 9 C) i6 (sh 9 (N k)) (sh 9 (N Nx)) i0 i1)))
```

The eighteen instances: four term combinations for each atom, two for each
bounded quantifier.

```agda
  all : Formula S (4 + m)
  all =
      atomClose f0 f0 f0 w4 (sh 1 w4) ∧̇ (atomClose f0 f0 f1 w4 i2
    ∧̇ (atomClose f0 f1 f0 i1 (sh 1 w4) ∧̇ (atomClose f0 f1 f1 i1 i2
    ∧̇ (atomClose f1 f0 f0 w4 (sh 1 w4) ∧̇ (atomClose f1 f0 f1 w4 i2
    ∧̇ (atomClose f1 f1 f0 i1 (sh 1 w4) ∧̇ (atomClose f1 f1 f1 i1 i2
    ∧̇ (binClose f2 ∧̇ (binClose f3 ∧̇ (binClose f4
    ∧̇ (conClose f5 ∧̇ (quClose f6 ∧̇ (quClose f7
    ∧̇ (bqClose f8 f0 (sh 8 w) ∧̇ (bqClose f8 f1 i5
    ∧̇ (bqClose f9 f0 (sh 8 w) ∧̇ bqClose f9 f1 i5))))))))))))))))

closeAt : ∀ {m} → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
closeAt C w E N = ∀̇∈ (var E) (bothAll i0 (Close.all C w N))

codesAt : ∀ {m} → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
codesAt C w E N = shapeAt C w E N ∧̇ closeAt C w E N

Δ₀-codesAt : ∀ {m} (C w E : Fin m) (N : Fin 10 → Fin m) → Δ₀ (codesAt C w E N)
Δ₀-codesAt C w E N = checkΔ₀ (codesAt C w E N) tt
```

<!--en-->
## Recap

`codesAt` combines a shape condition with closure under immediate subkeys. The
shape condition recognizes one of ten constructors at a recorded arity, while
the closure condition keeps every term and formula part needed for structural
induction inside the same domain.
<!--zh-->
## 小结

`codesAt` 把形状条件与对直接子键的封闭性合在一起。形状条件在记录的元数上识别十种构造子，封闭条件则把结构归纳所需的每个词项部分与公式部分留在同一定义域内。
<!--ja-->
## まとめ

`codesAt` は、形の条件と直下の部分キーに対する閉性を組み合わせる。形の条件は記録されたアリティで十個の構成子の一つを識別し、閉性の条件は構造帰納法に必要な各項部分と論理式部分を同じ定義域の中に保つ。
<!--/-->

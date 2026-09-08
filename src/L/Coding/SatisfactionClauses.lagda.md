<!--en-->
# Describing the satisfaction table
<!--zh-->
# 描述满足关系表
<!--ja-->
# 充足関係表を記述する
<!--/-->

<!--en-->
This chapter specifies a satisfaction table by one bounded formula over a common frame. Ten constructor relations describe the value assigned to each formula code, and `Δ₀-tableAt`{.Agda} proves that their conjunction is a bounded formula.
<!--zh-->
本章用同一个框架上的一条有界公式描述满足关系表。十条构造子关系分别规定每种公式码的取值，而 `Δ₀-tableAt`{.Agda} 证明它们的合取仍是有界公式。
<!--ja-->
本章では、共通の枠組み上の一つの有界論理式によって充足関係表を記述します。十個の構成子関係が各論理式符号の値を定め、`Δ₀-tableAt`{.Agda} はその連言が有界論理式であることを示します。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
module L.Coding.SatisfactionClauses {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; Term; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊤̇; ⊥̇; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using ( checkΔ₀; Δ₀ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ} using ( prAtL )
open import L.Coding.Expressions {ℓ} using ( sucAtL; consAtL )
open import L.Coding.Quantification {ℓ} using
  ( f0; f1; i0; i1; i2; i3; i4; i5; i6; i8; i9; i11; i12; i14; i16; i17; i19; sh
  ; sndEx; sndAll; bothEx; bothAll; bigAnd )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.Unit using ( tt )

open hPropStructure 𝒮ʟ using ( S )
```

<!--en-->
## The table frame and its ten clauses
<!--zh-->
## 表框架及其十条子句
<!--ja-->
## 表の枠組みと十個の節
<!--/-->

<!--en-->
The formulas `extB`, `subAt`, `subSucAt`, and `tmIs` express the common semantic
pieces of a table entry; the ten constructor relations are assembled by `relN`,
and `clause` and `tableAt` require those relations at every code key.
<!--zh-->
公式 `extB`、`subAt`、`subSucAt` 与 `tmIs` 表达表条目的共同语义部件；十种构造子的关系由 `relN` 汇集，而 `clause` 与 `tableAt` 要求这些关系在每个公式码键上成立。
<!--ja-->
論理式 `extB`、`subAt`、`subSucAt`、`tmIs` は表の要素に共通する意味論的な部分を表す。十個の構成子の関係を `relN` がまとめ、`clause` と `tableAt` が各論理式符号の鍵でそれらの関係を要求する。
<!--/-->

The table. `T` is the satisfaction table: a set of pairs `(c, yc)`, `c` a key in
`C`, one at every key, whose values obey the ten clauses. Each clause is
stated at the frame
`yc ∷ s''' ∷ e ∷ r ∷ s'' ∷ p ∷ s' ∷ c ∷ F ∷ ar ∷ s ∷ q ∷ γ` (12 + m), read off
`(ar, F) ∈ E`, `c = (ar, p) ∈ C`, `p = (N k, r)` and `(c, yc) ∈ T`, and says
what `yc` is: the members of `F` with the property the constructor gives, in the
value polarity of `extB`.

`y` is exactly the set of members of `F` satisfying `φ`.

```agda
extB : ∀ {j} → Fin j → Fin j → Formula S (1 + j) → Formula S j
extB y F φ = ∀̇∈ (var y) ((var i0 ∈̇ var (sh 1 F)) ∧̇ φ)
           ∧̇ ∀̇∈ (var F) (φ ⇒̇ (var i0 ∈̇ var (sh 1 y)))
```

The first component, universally.

```agda
fstAll : ∀ {j} → Fin j → Fin j → Formula S (2 + j) → Formula S j
fstAll x v body = ∀̇∈ (var x) (∀̇∈ (var i0) (prAtL (sh 2 x) i0 (sh 2 v) ⇒̇ body))
```

The value at the subkey `(ar, a)`: every entry `(c₁, ya)` of `T` with
`c₁ = (ar, a)`, body at `ya ∷ c₁ ∷ s ∷ e' ∷ γ`.

```agda
subAt : ∀ {j} → Fin j → Fin j → Fin j → Formula S (4 + j) → Formula S j
subAt T ar a body = ∀̇∈ (var T) (bothAll i0 (prAtL i1 (sh 4 ar) (sh 4 a) ⇒̇ body))
```

The value at the subkey `(suc ar, a)`: body at
`ar' ∷ s' ∷ ya ∷ c₁ ∷ s ∷ e' ∷ γ`.

```agda
subSucAt : ∀ {j} → Fin j → Fin j → Fin j → Formula S (6 + j) → Formula S j
subSucAt T ar a body =
  ∀̇∈ (var T) (bothAll i0 (fstAll i1 (sh 4 a) (sucAtL (sh 6 ar) i0 ⇒̇ body)))
```

`v` is the value of the term code `t` in the environment `z`: `t` is the
constant `v`, or `t` is the variable `i` and `(i, v)` is an entry of `z`.

```agda
tmIs : ∀ {j} → Fin j → Fin j → Fin j → Fin j → Fin j → Formula S j
tmIs t z v N0 N1 =
  prAtL t N0 v ∨̇ sndEx t N1 (∃̇∈ (var (sh 2 z)) (prAtL i0 i1 (sh 3 v)))
```

The ten relations, at the frame (12 + m): `yc` at `i0`, `r` at `i3`, `F` at
`i8`, `ar` at `i9`. Each relation binds its subvalues and ends in an extension
fact whose body is named, so that a reader can hand the body back at the frame
it was read in.

```agda
module Rel {m : ℕ} (T w : Fin m) (N : Fin 10 → Fin m) where
  private
    N0 N1 : ∀ {j} → Fin (j + m)
    N0 {j} = sh j (N f0)
    N1 {j} = sh j (N f1)
```

At `z ∷ yb ∷ c₂ ∷ s₂ ∷ e₂ ∷ ya ∷ c₁ ∷ s₁ ∷ e₁ ∷ b ∷ a ∷ s ∷ frame`: `ya` at
`i5`, `yb` at `i1`.

```agda
  binBody : (∀ {j} → Formula S j → Formula S j → Formula S j) → Formula S (24 + m)
  binBody op = op (var i0 ∈̇ var i5) (var i0 ∈̇ var i1)
```

At `z ∷ ar' ∷ s' ∷ ya ∷ c₁ ∷ s ∷ e' ∷ frame`: `ya` at `i3`, `w` at `sh 19 w`.

```agda
  quBody : (∀ {j} → Term S j → Formula S (suc j) → Formula S j) → Formula S (19 + m)
  quBody q = q (var (sh 19 w)) (∃̇∈ (var i4) (consAtL i0 i1 i2))
```

At `z ∷ ar' ∷ s' ∷ ya ∷ c₁ ∷ s₁ ∷ e' ∷ a ∷ t ∷ s ∷ frame`: `ya` at `i3`, `t` at
`i8`, `w` at `sh 22 w`.

```agda
  bqBody : (∀ {j} → Term S j → Formula S (suc j) → Formula S j)
         → (∀ {j} → Formula S j → Formula S j → Formula S j) → Formula S (22 + m)
  bqBody q c =
    q (var (sh 22 w)) (c (tmIs i9 i1 i0 N0 N1)
      (q (var (sh 23 w)) (c (var i0 ∈̇ var i1) (∃̇∈ (var i5) (consAtL i0 i1 i3)))))
```

At `z ∷ u ∷ t ∷ s ∷ frame`: `u` at `i1`, `t` at `i2`, `w` at `sh 16 w`; `rel` at
`x ∷ v ∷ z ∷ u ∷ t ∷ s ∷ frame`, `v` at `i1`, `x` at `i0`.

```agda
  atomBody : Formula S (18 + m) → Formula S (16 + m)
  atomBody rel =
    ∃̇∈ (var (sh 16 w)) (∃̇∈ (var (sh 17 w))
      (tmIs i4 i2 i1 N0 N1 ∧̇ (tmIs i3 i2 i0 N0 N1 ∧̇ rel)))

  botRel : Formula S (12 + m)
  botRel = extB i0 i8 ⊥̇

  binRel : (∀ {j} → Formula S j → Formula S j → Formula S j) → Formula S (12 + m)
  binRel op =
    bothAll i3 (subAt (sh 15 T) i12 i1 (subAt (sh 19 T) i16 i4 (extB i11 i19 (binBody op))))

  quRel : (∀ {j} → Term S j → Formula S (suc j) → Formula S j) → Formula S (12 + m)
  quRel q = subSucAt (sh 12 T) i9 i3 (extB i6 i14 (quBody q))

  bqRel : (∀ {j} → Term S j → Formula S (suc j) → Formula S j)
        → (∀ {j} → Formula S j → Formula S j → Formula S j) → Formula S (12 + m)
  bqRel q c = bothAll i3 (subSucAt (sh 15 T) i12 i0 (extB i9 i17 (bqBody q c)))

  atomRel : Formula S (18 + m) → Formula S (12 + m)
  atomRel rel = bothAll i3 (extB i3 i11 (atomBody rel))

  relN : ℕ → Formula S (12 + m)
  relN 0 = atomRel (var i1 ∈̇ var i0)
  relN 1 = atomRel (var i1 ≐ var i0)
  relN 2 = binRel _∧̇_
  relN 3 = binRel _∨̇_
  relN 4 = binRel _⇒̇_
  relN 5 = botRel
  relN 6 = quRel ∃̇∈
  relN 7 = quRel ∀̇∈
  relN 8 = bqRel ∀̇∈ _⇒̇_
  relN 9 = bqRel ∃̇∈ _∧̇_
  relN (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) = ⊤̇
```

The frame, and the clauses.

```agda
module Clause {m : ℕ} (T w C E : Fin m) (N : Fin 10 → Fin m) where
  private
    module R = Rel T w N

  clause : Fin 10 → Formula S m
  clause k =
    ∀̇∈ (var E) (bothAll i0 (∀̇∈ (var (sh 4 C)) (sndAll i0 i2 (sndAll i0 (sh 7 (N k))
      (∀̇∈ (var (sh 9 T)) (sndAll i0 i5 (R.relN (toℕ k))))))))
```

Every key has an entry, and every entry is at a key.

```agda
  total onC : Formula S m
  total = ∀̇∈ (var C) (∃̇∈ (var (sh 1 T)) (sndEx i0 i1 ⊤̇))
  onC = ∀̇∈ (var T) (bothEx i0 (var i1 ∈̇ var (sh 4 C)))

  ten : Formula S m
  ten = bigAnd 9 clause

tableAt : ∀ {m} → Fin m → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
tableAt T w C E N = Clause.total T w C E N ∧̇ (Clause.onC T w C E N ∧̇ Clause.ten T w C E N)

Δ₀-tableAt : ∀ {m} (T w C E : Fin m) (N : Fin 10 → Fin m) → Δ₀ (tableAt T w C E N)
Δ₀-tableAt T w C E N = checkΔ₀ (tableAt T w C E N) tt
```

<!--en-->
## Recap

The formula `tableAt` combines ten constructor clauses over a shared table frame. Each clause is built from the bounded formula combinators above, and `Δ₀-tableAt` proves that the complete specification remains in the Lévy hierarchy's bounded fragment.
<!--zh-->
## 小结

公式 `tableAt` 在同一个表框架上合并十条构造子子句。每条子句都由上述有界公式组合子构成，而 `Δ₀-tableAt` 证明完整规格仍属于莱维层级的有界片段。
<!--ja-->
## まとめ

論理式 `tableAt` は共通の表の枠組み上で十個の構成子の節をまとめます。各節は上の有界論理式の組合せからなり、`Δ₀-tableAt` は仕様全体がレヴィ階層の有界部分に属することを示します。
<!--/-->

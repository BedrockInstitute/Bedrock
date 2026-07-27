# Satisfaction, one formula at a time

<!--en-->
The value the table will record. For a formula of the meta-language and a set of
`L` the environments range over, this is the set of those environments that
satisfy it, built by recursion on the formula.

Nothing here is internal. The recursion is on a formula Agda can see, so each
step may name the sets the previous steps produced as constants, and the object
language never has to quantify over a code. That is what makes every step a
single separation off the ambient set, and what makes the twelve clauses of the
internal recursion, when they come, into identities rather than definitions.

The atoms are shorter here than in the internal clauses for the same reason. A
term of the meta-language is a variable or a constant and the recursion knows
which, so the reader for its value is one case rather than two.
<!--zh-->
表将要记录的那个取值。给定元语言的一条公式，以及诸环境所落之上的 `L` 的一个集合，这就是满足它的那些环境构成的集合，沿公式递归造出。

此处没有任何内部的东西。递归沿一条 Agda 看得见的公式进行，故每一步都可以把前几步产出的集合以常元点名，而对象语言从不必对码作量化。正是这一点使每一步只是「在周遭集合上作一次分离」，也正是这一点使内部递归那十二条子句到来时成为**等式**而非定义。

出于同样理由，此处的原子比内部子句短。元语言的一个词项要么是变元、要么是常元，而递归知道是哪个，故读它取值的读式只有一种情形，不是两种。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.Sat {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Term; con; var; Formula
        ; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Coding.Model {ℓ} using ( appAt; consAtL; numL )
open import L.Coding.EnvSet {ℓ} lem using ( envSet )

open import Cubical.Data.FinData using ( toℕ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## Reading a term the recursion can see
<!--zh-->
## 读一个递归看得见的词项
<!--/-->

<!--en-->
Two clauses, and which one applies is decided in the meta-language rather than
by the object language matching a tag. A variable's value is what the environment
records at its index; a constant's value is itself.
<!--zh-->
两条子句，而适用哪一条由元语言决定，不由对象语言去匹配标签。变元的取值是环境在它序号处记录的东西；常元的取值就是它自己。
<!--/-->

```agda
private
  nn : ℕ → S
  nn k = # k , numL k

tmIs : ∀ {n m} → Term S n → Fin m → Fin m → Formula S m
tmIs (var i) v e =
  ∃̇ ((var zero ≐ con (nn (toℕ i))) ∧̇ appAt (suc e) zero (suc v))
tmIs (con c) v e = var v ≐ con c
```

<!--en-->
## The value
<!--zh-->
## 那个取值
<!--/-->

<!--en-->
Twelve clauses, each one separation off the ambient set. The propositional ones
name the values below them and combine them with the object language's own
connective, which is why the clause for implication is the Heyting arrow rather
than a complement of a union: the chapter that wrote the internal clauses made
the same choice for the same reason, and the two have to agree.

The quantifiers cons a member of the carrier onto the environment and ask whether
the result is in the value below, which is one arity up. The two bounded ones do
the same with the member drawn from the value of their bounding term rather than
from the carrier.
<!--zh-->
十二条子句，每条都是在周遭集合上作一次分离。命题的那几条把它们下面的诸取值点名，再用对象语言自己的联结词把它们合起来；蕴含那一条因此是 Heyting 箭头，而非「并的补」：写内部诸子句的那一章出于同样理由作了同样的选择，而两者必须一致。

两个量词把载体的一个成员接到环境头上，再问结果是否落在下面那个取值之中，而后者高一个元数。两个有界量词做同样的事，只是那个成员取自其界项的取值，而非取自载体。
<!--/-->

```agda
private
  sep : (a : S) → Formula S 1 → S
  sep a φ = hasSeparationL a φ .fst .fst

  sep-mem : (a : S) (φ : Formula S 1) (x : S)
          → (x ∈ˢ sep a φ) ≡ ((x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ))
  sep-mem a φ = hasSeparationL a φ .fst .snd

module _ (B : S) where
  cond : ∀ {n} → Formula S n → Formula S 1

  Sat : ∀ {n} → Formula S n → S
  Sat {n} φ = sep (envSet B n) (cond φ)

  cond (t ∈̇ u) =
    (∃̇ (∃̇ ( tmIs t (suc zero) (suc (suc zero))
          ∧̇ ( tmIs u zero (suc (suc zero))
          ∧̇ (var (suc zero) ∈̇ var zero) ))))
  cond (t ≐ u) =
    (∃̇ (∃̇ ( tmIs t (suc zero) (suc (suc zero))
          ∧̇ ( tmIs u zero (suc (suc zero))
          ∧̇ (var (suc zero) ≐ var zero) ))))
  cond (a ∧̇ b) =
    ((var zero ∈̇ con (Sat a)) ∧̇ (var zero ∈̇ con (Sat b)))
  cond (a ∨̇ b) =
    ((var zero ∈̇ con (Sat a)) ∨̇ (var zero ∈̇ con (Sat b)))
  cond (a ⇒̇ b) =
    ((var zero ∈̇ con (Sat a)) ⇒̇ (var zero ∈̇ con (Sat b)))
  cond (¬̇ a) = ¬̇ (var zero ∈̇ con (Sat a))
  cond ⊤̇ = ⊤̇
  cond ⊥̇ = ⊥̇
  cond (∃̇ a) =
    (∃̇∈ (con B) (∃̇ ( consAtL zero (suc zero) (suc (suc zero))
                  ∧̇ (var zero ∈̇ con (Sat a)) )))
  cond (∀̇ a) =
    (∀̇∈ (con B) (∀̇ ( consAtL zero (suc zero) (suc (suc zero))
                  ⇒̇ (var zero ∈̇ con (Sat a)) )))
  cond (∀̇∈ t a) =
    (∀̇ ( tmIs t zero (suc zero)
      ⇒̇ ∀̇∈ (var zero) (∀̇ ( consAtL zero (suc zero) (suc (suc (suc zero)))
                        ⇒̇ (var zero ∈̇ con (Sat a)) )) ))
  cond (∃̇∈ t a) =
    (∃̇ ( tmIs t zero (suc zero)
      ∧̇ ∃̇∈ (var zero) (∃̇ ( consAtL zero (suc zero) (suc (suc (suc zero)))
                        ∧̇ (var zero ∈̇ con (Sat a)) )) ))
```

<!--en-->
## What each clause says
<!--zh-->
## 每条子句说了什么
<!--/-->

<!--en-->
The membership equations, one per constructor, and the only thing this chapter
exports besides the value itself. They are what the internal clauses will be
checked against: an internal clause says the recorded value stands in some
relation to the recorded subvalues, and these say the same of the values built
here, so verifying a clause is transporting one along the other.

Each is the separation's own specification with the constructor's condition
already substituted, which is why they are one line apiece.
<!--zh-->
诸成员等式，每个构造子一条，也是本章除那个取值本身之外唯一导出的东西。它们是内部诸子句将被对照的对象：一条内部子句说「被记录的取值与被记录的诸子取值处于某种关系」，而这些说的是同一件事、只不过对象是此处造出的诸取值；故验证一条子句就是沿其中之一把另一条搬过去。

每一条都是那次分离自己的规格，且构造子的条件已代入，这就是它们一条一行的原因。
<!--/-->

```agda
  Sat-mem : ∀ {n} (φ : Formula S n) (x : S)
          → (x ∈ˢ Sat φ) ≡ ((x ∈ˢ envSet B n) ⊓ ((x ∷ []) ⊨ cond φ))
  Sat-mem {n} φ = sep-mem (envSet B n) (cond φ)
```

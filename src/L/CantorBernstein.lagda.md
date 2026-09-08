<!--en-->
# Cantor–Schröder–Bernstein inside L

Coded injections in both directions between two sets of `L` yield a bijection between their small presentations. Each injection code is first read as an ordinary injection, after which the type-level Cantor–Schröder–Bernstein theorem supplies the truncated bijection.
<!--zh-->
# L 内部的 Cantor–Schröder–Bernstein 定理

`L` 中两个集合之间若有双向的编码单射，便可得到其小呈现之间的双射。每个注入码先被读成普通注入，再由类型层的 Cantor–Schröder–Bernstein 定理给出截断的双射。
<!--ja-->
# L の内部における Cantor–Schröder–Bernstein の定理

`L` の二つの集合の間に双方向の符号化された単射があれば、それらの小さな提示の間の全単射が得られます。各単射の符号を通常の単射として読み出し、型の Cantor–Schröder–Bernstein の定理から命題的に切り詰められた全単射を得ます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM; lowerLEM )

module L.CantorBernstein {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.CantorBernstein {ℓ} (lowerLEM lem)
  using ( small-set; module MutualInj )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Cardinal {ℓ} lem using ( InjCode; InjL )
open import L.Coding.Injection {ℓ} lem using ( module Small )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open hPropStructure 𝒮ʟ using ( S )
```

Set-ness of the small member type, delegated: `small-set` is stated
at `V ℓ`, and `fst a` is a `V ℓ` for every `a : S`.

```agda
setPL : (a : S) → isSet (⟪ fst a ⟫)
setPL a = small-set (fst a)
```

The readback at the code notion: an `InjCode` witness is four
satisfaction facts, and `Small` consumes exactly those four.

```agda
readL : (a b : S) → Σ[ F ∈ S ] InjCode F a b
      → Σ[ f ∈ (⟪ fst a ⟫ → ⟪ fst b ⟫) ]
          ((x y : ⟪ fst a ⟫) → f x ≡ f y → x ≡ y)
readL a b (F , sv , dm , ij , ran) = SM.small , SM.small-inj
  where
  module SM = Small F a b sv dm ij ran

module MutualInjL = MutualInj S (λ a → ⟪ fst a ⟫)
  (λ a b → Σ[ F ∈ S ] InjCode F a b) setPL readL
```

`InjL` is definitionally the truncation of the witness relation the
application above was made at, so `∃bijection` reads off with no
conversion.  The surjectivity stays truncated: the hypotheses are
truncated existentials, so the conclusion is the same grade of
object they speak in.  A consumer holding a witness as data reads
`MutualInjL.mutual→bijection` off the same application.

```agda
mutual-inj→bijection : (a b : S) → InjL a b → InjL b a
  → ∥ Σ[ h ∈ (⟪ fst a ⟫ → ⟪ fst b ⟫) ]
       (((x y : ⟪ fst a ⟫) → h x ≡ h y → x ≡ y)
     × ((y : ⟪ fst b ⟫) → ∥ Σ[ x ∈ ⟪ fst a ⟫ ] (h x ≡ y) ∥₁)) ∥₁
mutual-inj→bijection = MutualInjL.∃bijection
```

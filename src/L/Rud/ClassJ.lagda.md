# The rud constructible class

<!--en-->
The rud side of the bridge names its universe. A set is in the class `J` when
some limit level of the `S`-tower contains it, and the witness carries the
limit certificate, which subsumes the ordinality of the level: the bridge's
endpoints line up with the constructible side, where the ordinal certificate
rides in the witness the same way. The class is a proposition by
construction, it is transitive because every level is, and the tower's own
placement lemma reads the defining direction. The structure `𝒮ⱼ`, the
restriction of the ambient structure to the class, packages the rud side as a
world of its own.
<!--zh-->
rud 一侧的桥为它的宇宙命名。一个集合属于初步函数类 `J`，指 `S`-塔的某个极限层包含它，见证随身携带极限证书，证书已涵盖该层的序数性，于是桥的两端与可构造一侧对齐，彼处的见证同样携序数而行。类按构造是命题，因每层传递而传递，塔自身的安放引理读出定义方向。结构 `𝒮ⱼ`，即把周遭结构限制到类上的结果，把 rud 一侧打包成自己的世界。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module L.Rud.ClassJ {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure
  using ( ZFStructure; _↾_; module hPropStructure; Transitive )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit )
open import L.Rud.Step {ℓ} lem A using ( Jset; Sset-trans )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.Data.Sigma.Properties using ( Σ≡Prop )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The class
<!--zh-->
## 类
<!--/-->

<!--en-->
Membership in `J` is truncated existence of a limit level containing `x`, read
level by level exactly as `isL` reads stage by stage. The family is
propositional because the limit predicate is and membership is, so the join
lands in the truth values.
<!--zh-->
`J` 的隶属是「存在极限层包含 `x`」的截断，逐层读出，正如 `isL` 逐阶段读出。族是命题的，因为极限谓词与隶属皆是命题，故并落在真值里。
<!--/-->

```agda
isJ : S → Ω
isJ x = ⋁ S (λ α → (Σ[ lim ∈ ⟨ isLimit α ⟩ ] ⟨ x ∈ˢ Jset α lim ⟩) , isPropΣ x α)
  where
  isPropΣ : (x α : S) → isProp (Σ[ lim ∈ ⟨ isLimit α ⟩ ] ⟨ x ∈ˢ Jset α lim ⟩)
  isPropΣ x α u v = Σ≡Prop (λ lim → snd (x ∈ˢ Jset α lim)) (snd (isLimit α) (u .fst) (v .fst))

isPropIsJ : (x : S) → isProp (⟨ isJ x ⟩)
isPropIsJ x = snd (isJ x)
```

<!--en-->
Sitting in a limit level *is* the definition, so the bridge in that direction is
the constructor itself, mirroring `Lset→isL`: every closure proof on the rud
side ends by exhibiting a limit level, and the certificate comes along.
<!--zh-->
落在某个极限层中**就是**定义，故这个方向的桥就是构造子本身，与 `Lset→isL` 遥相呼应：rud 一侧的每个闭包证明都以拿出一个极限层收尾，证书随行而至。
<!--/-->

```agda
Jset→isJ : (α : S) → (lim : ⟨ isLimit α ⟩) → (x : S) → ⟨ x ∈ˢ Jset α lim ⟩ → ⟨ isJ x ⟩
Jset→isJ α lim x x∈J = ∣ α , lim , x∈J ∣₁
```

<!--en-->
## Transitivity
<!--zh-->
## 传递性
<!--/-->

<!--en-->
The class is closed downwards: a member of a `J`-set sits in the same level,
and the levels of the tower are transitive. The witness does not move, only the
element does, exactly as in the constructible class.
<!--zh-->
类向下封闭：`J` 之集的成员落在同一层，而塔的各层传递。见证不动，只有元素移动，与可构造类如出一辙。
<!--/-->

```agda
isJ-trans : Transitive 𝒮ᵥ isJ
isJ-trans {x} {y} y∈x x∈J = PT.rec (snd (isJ y))
  (λ { (α , lim , x∈Jα) → ∣ α , lim , Sset-trans α y∈x x∈Jα ∣₁ })
  x∈J
```

<!--en-->
## The structure
<!--zh-->
## 结构
<!--/-->

<!--en-->
The chapter's deliverable on the rud side: the class packaged as a structure,
the restriction `𝒮ᵥ ↾ isJ` in the shape `𝒮ʟ` carved out of the same ambient
structure. Its carrier is the `J`-sets, its relations are inherited, and the
whole framework applies to it verbatim; the fine-structure route reads this as
its own universe.
<!--zh-->
rud 一侧本章的交付物：把类打包成结构，即按 `𝒮ʟ` 的形状从同一周遭结构中裁出的 `𝒮ᵥ ↾ isJ`。载体是 `J` 之集，关系原样继承，整套框架逐字适用于它；细结构路线把它读作自己的宇宙。
<!--/-->

```agda
𝒮ⱼ : ZFStructure (hPropAlgebra (ℓ-suc ℓ))
𝒮ⱼ = 𝒮ᵥ ↾ isJ
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The class `J` is defined as membership in a limit level of the `S`-tower, with
the certificate in the witness; it is propositional, transitive, and read one
way by the tower itself. The restricted structure `𝒮ⱼ` is the carrier the
fine-structure route studies, standing beside `𝒮ʟ` at the same price.
<!--zh-->
类 `J` 定义为 `S`-塔某个极限层的隶属，证书随见证同行；它命题、传递，且被塔本身按一个方向读出。限制结构 `𝒮ⱼ` 是细结构路线研究的载体，以同样的代价立在 `𝒮ʟ` 身旁。
<!--/-->

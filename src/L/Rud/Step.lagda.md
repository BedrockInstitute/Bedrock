# The concrete one-step operator

<!--en-->
The hierarchy engine of the rud route is abstract: it takes a one-step
operator together with four properties and builds the S-tower from nothing
else. This chapter supplies the concrete operator: for each of the sixteen
operations of the Schindler-Zeman basis (SZ p. 10, equation I.1) it forms
the image set of values over the square of `u ∪ {u}`, built as a
`sett`{.Agda} over the small representation of that square, and the step is
the union of those sixteen images, one step of the rud closure. The
membership characterization the consumers read is stated by the step-in and
step-out lemmas, and the construction itself is sealed so nothing downstream
unfolds it.

The chapter also discharges what the telescope's four properties need from
the concrete operator. Membership of `u` and of its members in the step is
the definitional floor of the cumulative form: the step contains `u ∪ {u}`,
as the step-shape ruling pins (SZ's verb "adds images to `U ∪ {U}`" and
Mathias's `T(u) = u ∪ {u} ∪ ...`, WS 2.73). The transitivity of the step
for transitive inputs is then analysed operation by operation, sharing the
frame that the tuple operations catch the intermediate objects of pair
formation. Monotonicity of the step in its argument is examined and its
outcome recorded in the batch report.
<!--zh-->
初步函数路线的层级引擎是抽象的：它只拿一个单步算子连同四条性质，就别无其他地建起 S-塔。本章供给具体算子：对 Schindler-Zeman 基的十六个运算各取 `u ∪ {u}` 之平方上的像值集 (SZ p. 10，方程 I.1)，作为该平方的小表示上的 `sett`{.Agda} 造出，step 则是这十六个像之并，即初步函数闭包的一步。消费者读取的隶属刻画由 step-in 与 step-out 引理陈述，构造本身被封起，下游无从展开。

本章还清偿望远镜四条性质需要从具体算子得到的那部分。`u` 及其成员在 step 中的隶属是累积形式的定义性地板：step 含有 `u ∪ {u}`，正如 step 形状裁定所定 (SZ 的动词「把像加到 `U ∪ {U}`」，以及 Mathias 的 `T(u) = u ∪ {u} ∪ ...`，WS 2.73)。接着逐运算分析 step 对传递输入的传递性，共享「三元组运算捕捉对形成的中间对象」这一框架。step 对其自变量的单调性经过考查，其结果记入批次报告。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; sett )

module L.Rud.Step {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr )
open import L.Rud.Ops {ℓ}
  using ( F0; F1; F2; F3; F4; F5; F6; F7; F9
        ; F0-spec; F1-spec; F5-spec
        ; F2-read; F3-read; F4-read; F6-read; F7-read )
open import L.Rud.Images {ℓ}
  using ( F8; F10; F11; F12; F13; F14; left; right; left-spec; right-spec
        ; F8-spec; F10-spec; F11-spec; F12-spec )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sum.Properties using ( isProp⊎ )
import Cubical.Data.Empty as Empty
open import Cubical.Functions.Logic using ( ∃[]-syntax )
open import Cubical.Foundations.Equiv using ( fiber )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber; _≡ₕ_; _⊆_; extensionality )
-- lint-agda: keep (used qualified: SetPackage.classification)
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_∶_⁆; separation-ax; pairing-ax; ⋃_; union-ax; ⁅_⁆s
        ; SingletonPackage; SetPackage )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The argument set and its membership
<!--zh-->
## 参数集及其隶属
<!--/-->

<!--en-->
The step applies its images to the members of `u ∪ {u}`, and membership in
the argument set decides constructively between "a member of `u`" and "equal
to `u`". That split is the case analysis every transitivity case performs.
The argument set is almost transitive: a member of a member of the argument
set is again in it whenever `u` is transitive, and this one-step closure is
the workhorse of the per-operation cases below.
<!--zh-->
step 把像施于 `u ∪ {u}` 的成员，参数集的隶属在「`u` 的成员」与「等于 `u`」之间构造性地分情形，这正是每个传递性情形要做的切分。参数集近乎传递：只要 `u` 传递，参数集成员的成员仍在其内，这条单步闭包是下方逐运算情形的支柱。
<!--/-->

```agda
u' : V ℓ → V ℓ
u' u = ⋃ ⁅ u , ⁅ u ⁆s ⁆

u'-in : (u x : V ℓ) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ u' u ⟩
u'-in u x x∈u = ∈∈ₛ {a = x} {b = u' u} .snd
  (union-ax ⁅ u , ⁅ u ⁆s ⁆ x .snd
    ∣ u , ( pairing-ax u (⁅ u ⁆s) u .snd ∣ inl refl ∣₁
         , ∈∈ₛ {a = x} {b = u} .fst x∈u ) ∣₁)

u-self-in : (u : V ℓ) → ⟨ u ∈ˢ u' u ⟩
u-self-in u = ∈∈ₛ {a = u} {b = u' u} .snd
  (union-ax ⁅ u , ⁅ u ⁆s ⁆ u .snd
    ∣ ⁅ u ⁆s , ( pairing-ax u (⁅ u ⁆s) (⁅ u ⁆s) .snd ∣ inr refl ∣₁
              , SetPackage.classification (SingletonPackage u) u .snd refl ) ∣₁)

u'-cases : (u a : V ℓ) → ⟨ a ∈ˢ u' u ⟩ → (⟨ a ∈ˢ u ⟩ ⊎ (a ≡ u))
u'-cases u a h = PT.rec (isProp⊎ (snd (a ∈ˢ u)) (isSetS a u) disj) go
    (union-ax ⁅ u , ⁅ u ⁆s ⁆ a .fst (∈∈ₛ {a = a} {b = u' u} .fst h))
  where
  disj : ⟨ a ∈ˢ u ⟩ → a ≡ u → Empty.⊥
  disj a∈u a≡u = ∈-irrefl a (subst (λ t → ⟨ a ∈ˢ t ⟩) (sym a≡u) a∈u)
  go : Σ[ v ∈ V ℓ ] (⟨ v ∈ₛ ⁅ u , ⁅ u ⁆s ⁆ ⟩ × ⟨ a ∈ₛ v ⟩)
     → (⟨ a ∈ˢ u ⟩ ⊎ (a ≡ u))
  go (v , v∈ₛpair , a∈ₛv) = PT.rec
    (isProp⊎ (snd (a ∈ˢ u)) (isSetS a u) disj) go'
    (pairing-ax u (⁅ u ⁆s) v .fst v∈ₛpair)
    where
    go' : (⟨ v ≡ₕ u ⟩ ⊎ ⟨ v ≡ₕ ⁅ u ⁆s ⟩) → (⟨ a ∈ˢ u ⟩ ⊎ (a ≡ u))
    go' (inl v≡u) = inl (subst (λ t → ⟨ a ∈ˢ t ⟩) v≡u (∈∈ₛ {a = a} {b = v} .snd a∈ₛv))
    go' (inr v≡s) = inr (SetPackage.classification (SingletonPackage u) a .fst
      (subst (λ t → ⟨ a ∈ₛ t ⟩) v≡s a∈ₛv))

u'-trans : (u : V ℓ) (tr : {x y : V ℓ} → ⟨ y ∈ˢ x ⟩ → ⟨ x ∈ˢ u ⟩ → ⟨ y ∈ˢ u ⟩)
         → (a x : V ℓ) → ⟨ x ∈ˢ a ⟩ → ⟨ a ∈ˢ u' u ⟩ → ⟨ x ∈ˢ u' u ⟩
u'-trans u tr a x x∈a a∈u' = go (u'-cases u a a∈u')
  where
  go : (⟨ a ∈ˢ u ⟩ ⊎ (a ≡ u)) → ⟨ x ∈ˢ u' u ⟩
  go (inl a∈u) = u'-in u x (tr x∈a a∈u)
  go (inr a≡u) = u'-in u x (subst (λ t → ⟨ x ∈ˢ t ⟩) a≡u x∈a)

doubleUnion : V ℓ → V ℓ
doubleUnion b = ⋃ (⋃ b)

in-⋃⋃ : (b x : V ℓ) → ⟨ x ∈ˢ doubleUnion b ⟩
       → ∥ Σ[ e ∈ V ℓ ] Σ[ f ∈ V ℓ ]
            (⟨ f ∈ˢ b ⟩ × ⟨ e ∈ˢ f ⟩ × ⟨ x ∈ˢ e ⟩) ∥₁
in-⋃⋃ b x h = PT.rec squash₁ go
    (union-ax (⋃ b) x .fst (∈∈ₛ {a = x} {b = doubleUnion b} .fst h))
  where
  go : Σ[ e ∈ V ℓ ] (⟨ e ∈ₛ ⋃ b ⟩ × ⟨ x ∈ₛ e ⟩)
     → ∥ Σ[ e' ∈ V ℓ ] Σ[ f ∈ V ℓ ]
          (⟨ f ∈ˢ b ⟩ × ⟨ e' ∈ˢ f ⟩ × ⟨ x ∈ˢ e' ⟩) ∥₁
  go (e , e∈ₛ⋃b , x∈ₛe) = PT.map go' (union-ax b e .fst e∈ₛ⋃b)
    where
    go' : Σ[ f ∈ V ℓ ] (⟨ f ∈ₛ b ⟩ × ⟨ e ∈ₛ f ⟩)
        → Σ[ e' ∈ V ℓ ] Σ[ f' ∈ V ℓ ]
             (⟨ f' ∈ˢ b ⟩ × ⟨ e' ∈ˢ f' ⟩ × ⟨ x ∈ˢ e' ⟩)
    go' (f , f∈ₛb , e∈ₛf) = e , f
      , ( ∈∈ₛ {a = f} {b = b} .snd f∈ₛb
        , ∈∈ₛ {a = e} {b = f} .snd e∈ₛf
        , ∈∈ₛ {a = x} {b = e} .snd x∈ₛe )

⋃⋃→u' : (u : V ℓ) (tr : {x y : V ℓ} → ⟨ y ∈ˢ x ⟩ → ⟨ x ∈ˢ u ⟩ → ⟨ y ∈ˢ u ⟩)
       → (b x : V ℓ) → ⟨ b ∈ˢ u' u ⟩ → ⟨ x ∈ˢ doubleUnion b ⟩ → ⟨ x ∈ˢ u' u ⟩
⋃⋃→u' u tr b x b∈u' h = PT.rec (snd (x ∈ˢ u' u)) go (in-⋃⋃ b x h)
  where
  go : Σ[ e ∈ V ℓ ] Σ[ f ∈ V ℓ ]
         (⟨ f ∈ˢ b ⟩ × ⟨ e ∈ˢ f ⟩ × ⟨ x ∈ˢ e ⟩) → ⟨ x ∈ˢ u' u ⟩
  go (e , f , f∈b , e∈f , x∈e) = u'-trans u tr e x x∈e
    (u'-trans u tr f e e∈f (u'-trans u tr b f f∈b b∈u'))
```

<!--en-->
## The operation index and the images
<!--zh-->
## 运算索引与像
<!--/-->

<!--en-->
The sixteen operations are packed into one family indexed by a dedicated
sixteen-constructor type `Op16`{.Agda}, so the step and its membership
lemmas quantify over one index
rather than sixteen names. `F15` is the relativization slot, applied to the
module parameter `A`; the plain trunk instantiates `A` as the empty set at
assembly. Each operation contributes one image set, the `sett`{.Agda} of
its values over the argument square.
<!--zh-->
十六个运算被收进以专用十六构造子类型 `Op16`{.Agda} 为索引的单一族 `Fof`{.Agda}，step 与其隶属引理于是只对一个索引量化，而非十六个名字。`F15` 是相对化槽，施于模块参数 `A`；非相对化主干在合龙处把 `A` 实例化为空集。每个运算贡献一个像集，即其值在参数平方上的 `sett`{.Agda}。
<!--/-->

```agda
data Op16 : Type ℓ where
  op0 : Op16
  op1 : Op16
  op2 : Op16
  op3 : Op16
  op4 : Op16
  op5 : Op16
  op6 : Op16
  op7 : Op16
  op8 : Op16
  op9 : Op16
  op10 : Op16
  op11 : Op16
  op12 : Op16
  op13 : Op16
  op14 : Op16
  op15 : Op16

f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : Op16
f0 = op0
f1 = op1
f2 = op2
f3 = op3
f4 = op4
f5 = op5
f6 = op6
f7 = op7
f8 = op8
f9 = op9
f10 = op10
f11 = op11
f12 = op12
f13 = op13
f14 = op14
f15 = op15

-- the relativization slot, defined here because the images chapter keeps
-- its own F15 private; the plain trunk instantiates A as the empty set
F15A : V ℓ → V ℓ
F15A x = ⁅ x ∶ (λ u → u ∈ₛ A) ⁆

F15A-spec : (x u : V ℓ) → ⟨ u ∈ˢ F15A x ⟩ → ⟨ u ∈ˢ x ⟩
F15A-spec x u h = ∈∈ₛ {a = u} {b = x} .snd
  (separation-ax x (λ u → u ∈ₛ A) u .fst (∈∈ₛ {a = u} {b = F15A x} .fst h) .fst)

opaque
  Fof : Op16 → V ℓ → V ℓ → V ℓ
  Fof op0 a b = F0 a b
  Fof op1 a b = F1 a b
  Fof op2 a b = F2 a b
  Fof op3 a b = F3 a b
  Fof op4 a b = F4 a b
  Fof op5 a b = F5 a b
  Fof op6 a b = F6 a b
  Fof op7 a b = F7 a b
  Fof op8 a b = F8 a b
  Fof op9 a b = F9 a b
  Fof op10 a b = F10 a b
  Fof op11 a b = F11 a b
  Fof op12 a b = F12 a b
  Fof op13 a b = F13 a b
  Fof op14 a b = F14 a b
  Fof op15 a b = F15A a

opaque
  unfolding Fof
  Fof-f0 : (a b : V ℓ) → Fof f0 a b ≡ F0 a b
  Fof-f0 a b = refl

  Fof-f9 : (a b : V ℓ) → Fof f9 a b ≡ F9 a b
  Fof-f9 a b = refl

  Fof-f10 : (a b : V ℓ) → Fof f10 a b ≡ F10 a b
  Fof-f10 a b = refl

  Fof-f11 : (a b : V ℓ) → Fof f11 a b ≡ F11 a b
  Fof-f11 a b = refl

  Fof-f12 : (a b : V ℓ) → Fof f12 a b ≡ F12 a b
  Fof-f12 a b = refl

im : Op16 → V ℓ → V ℓ
im i u = sett (⟪ u' u ⟫ × ⟪ u' u ⟫)
         (λ p → Fof i (⟪ u' u ⟫↪ (p .fst)) (⟪ u' u ⟫↪ (p .snd)))
```

<!--en-->
## The step and its membership characterization
<!--zh-->
## step 及其隶属刻画
<!--/-->

<!--en-->
The step is cumulative: it contains the members of `u`, the set `u` itself,
and every value `F_i(a,b)` with `a, b ∈ u ∪ {u}`. This is the form the
step-shape ruling pins (SZ's prose verb "adds images to `U ∪ {U}`", and
Mathias's verbatim cumulative one-step operator `T(u) = u ∪ {u} ∪ ...`,
WS 2.73). The construction is sealed `opaque`{.Agda}, and the membership
characterization is exported as the three-armed `step-in` directions
(a member of `u`, `u` itself, or an image value) and the `step-out`
direction, which are the only surface the rest of the route reads.
<!--zh-->
step 是累积的：它含有 `u` 的成员、集合 `u` 本身，以及每个值 `F_i(a,b)`，其中 `a, b ∈ u ∪ {u}`。这正是 step 形状裁定所定的形式 (SZ 行文的动词「把像加到 `U ∪ {U}`」，以及 Mathias 逐字累积的单步算子 `T(u) = u ∪ {u} ∪ ...`，WS 2.73)。构造以 `opaque`{.Agda} 封印，隶属刻画以三臂 `step-in` 方向 (u 的成员、u 本身、或一个像值) 与 `step-out` 方向导出，这是路线其余部分唯一读取的表面。
<!--/-->

```agda
values : V ℓ → V ℓ
values u = ⋃ (sett Op16 (λ i → im i u))

data StepArm (u x : V ℓ) : Type (ℓ-suc ℓ) where
  arm-member : ⟨ x ∈ˢ u ⟩ → StepArm u x
  arm-self   : x ≡ u → StepArm u x
  arm-image  : (i : Op16) (a b : V ℓ)
             → (⟨ a ∈ˢ u ⟩ ⊎ (a ≡ u)) → (⟨ b ∈ˢ u ⟩ ⊎ (b ≡ u)) → ⟨ x ≡ₕ Fof i a b ⟩
             → StepArm u x

image-wit : (u x : V ℓ) → Type (ℓ-suc ℓ)
image-wit u x = Σ[ i ∈ Op16 ] Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
                  ((⟨ a ∈ˢ u ⟩ ⊎ (a ≡ u)) × (⟨ b ∈ˢ u ⟩ ⊎ (b ≡ u)) × ⟨ x ≡ₕ Fof i a b ⟩)

opaque
  step : V ℓ → V ℓ
  step u = ⋃ ⁅ u' u , values u ⁆

opaque
  unfolding step
  step-out : (u x : V ℓ) → ⟨ x ∈ˢ step u ⟩
           → ∥ StepArm u x ∥₁
  step-out u x h = PT.rec squash₁ go₁
    (union-ax ⁅ u' u , values u ⁆ x .fst
      (∈∈ₛ {a = x} {b = step u} .fst h))
    where
    go₁ : Σ[ v ∈ V ℓ ] (⟨ v ∈ₛ ⁅ u' u , values u ⁆ ⟩ × ⟨ x ∈ₛ v ⟩)
        → ∥ StepArm u x ∥₁
    go₁ (v , v∈ₛpair , x∈ₛv) = PT.rec squash₁ go₂
      (pairing-ax (u' u) (values u) v .fst v∈ₛpair)
      where
      go₂ : (⟨ v ≡ₕ u' u ⟩ ⊎ ⟨ v ≡ₕ values u ⟩)
          → ∥ StepArm u x ∥₁
      go₂ (inl v≡u') = go' (u'-cases u x
        (subst (λ t → ⟨ x ∈ˢ t ⟩) v≡u' (∈∈ₛ {a = x} {b = v} .snd x∈ₛv)))
        where
        go' : (⟨ x ∈ˢ u ⟩ ⊎ (x ≡ u)) → ∥ StepArm u x ∥₁
        go' (inl x∈u) = ∣ arm-member x∈u ∣₁
        go' (inr x≡u) = ∣ arm-self x≡u ∣₁
      go₂ (inr v≡val) = PT.rec squash₁
          (λ ((i , a , b , a∈u , b∈u , x≡) : image-wit u x) →
             ∣ arm-image i a b a∈u b∈u x≡ ∣₁)
          (go₃ (subst (λ t → ⟨ x ∈ₛ t ⟩) v≡val x∈ₛv))
        where
        go₃ : ⟨ x ∈ₛ values u ⟩ → ∥ image-wit u x ∥₁
        go₃ h' = PT.rec squash₁
            go₄ (union-ax (sett Op16 (λ i → im i u)) x .fst h')
          where
          go₄ : Σ[ w ∈ V ℓ ] (⟨ w ∈ₛ sett Op16 (λ i → im i u) ⟩ × ⟨ x ∈ₛ w ⟩)
              → ∥ image-wit u x ∥₁
          go₄ (w , w∈ₛS , x∈ₛw) = PT.rec squash₁
            go₅ (∈∈ₛ {a = w} {b = sett Op16 (λ i → im i u)} .snd w∈ₛS)
            where
            go₅ : Σ[ j ∈ Op16 ] (im j u ≡ w) → ∥ image-wit u x ∥₁
            go₅ (j , q) = PT.rec squash₁
              go₆ (subst (λ t → ⟨ x ∈ˢ t ⟩) (sym q) (∈∈ₛ {a = x} {b = w} .snd x∈ₛw))
              where
              go₆ : Σ[ p ∈ ⟪ u' u ⟫ × ⟪ u' u ⟫ ]
                      ⟨ Fof j (⟪ u' u ⟫↪ (p .fst)) (⟪ u' u ⟫↪ (p .snd)) ≡ₕ x ⟩
                  → ∥ image-wit u x ∥₁
              go₆ (p , r) = ∣ j
                , ⟪ u' u ⟫↪ (p .fst) , ⟪ u' u ⟫↪ (p .snd)
                , ( u'-cases u (⟪ u' u ⟫↪ (p .fst))
                      (∈∈ₛ {a = ⟪ u' u ⟫↪ (p .fst)} {b = u' u} .snd (∈ₛ⟪ u' u ⟫↪ (p .fst)))
                  , u'-cases u (⟪ u' u ⟫↪ (p .snd))
                      (∈∈ₛ {a = ⟪ u' u ⟫↪ (p .snd)} {b = u' u} .snd (∈ₛ⟪ u' u ⟫↪ (p .snd)))
                  , sym r ) ∣₁

  step-in : (u x : V ℓ) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ step u ⟩
  step-in u x x∈u = ∈∈ₛ {a = x} {b = step u} .snd
    (union-ax ⁅ u' u , values u ⁆ x .snd
      ∣ u' u , ( pairing-ax (u' u) (values u) (u' u) .snd ∣ inl refl ∣₁
               , ∈∈ₛ {a = x} {b = u' u} .fst (u'-in u x x∈u) ) ∣₁)

  step-in-self : (u : V ℓ) → ⟨ u ∈ˢ step u ⟩
  step-in-self u = ∈∈ₛ {a = u} {b = step u} .snd
    (union-ax ⁅ u' u , values u ⁆ u .snd
      ∣ u' u , ( pairing-ax (u' u) (values u) (u' u) .snd ∣ inl refl ∣₁
               , ∈∈ₛ {a = u} {b = u' u} .fst (u-self-in u) ) ∣₁)

  step-in-img : (u x : V ℓ) (i : Op16) (a b : V ℓ)
              → ⟨ a ∈ˢ u' u ⟩ → ⟨ b ∈ˢ u' u ⟩ → ⟨ x ≡ₕ Fof i a b ⟩
              → ⟨ x ∈ˢ step u ⟩
  step-in-img u x i a b a∈u' b∈u' x≡ =
    ∈∈ₛ {a = x} {b = step u} .snd
      (union-ax ⁅ u' u , values u ⁆ x .snd
        ∣ values u , ( pairing-ax (u' u) (values u) (values u) .snd ∣ inr refl ∣₁
                     , x∈ₛvalues ) ∣₁)
    where
    fa : fiber (⟪ u' u ⟫↪) a
    fa = ∈-asFiber {a = a} {b = u' u} a∈u'
    fb : fiber (⟪ u' u ⟫↪) b
    fb = ∈-asFiber {a = b} {b = u' u} b∈u'
    a' : V ℓ
    a' = ⟪ u' u ⟫↪ (fa .fst)
    b' : V ℓ
    b' = ⟪ u' u ⟫↪ (fb .fst)
    x≡ₕab' : ⟨ x ≡ₕ Fof i a' b' ⟩
    x≡ₕab' = subst (λ t → ⟨ x ≡ₕ t ⟩) (sym (cong₂ (Fof i) (fa .snd) (fb .snd))) x≡
    x∈ₛim : ⟨ x ∈ₛ im i u ⟩
    x∈ₛim = ∈∈ₛ {a = x} {b = im i u} .fst
      ∣ (fa .fst , fb .fst)
      , (cong₂ (Fof i) (fa .snd) (fb .snd) ∙ sym x≡) ∣₁
    x∈ₛvalues : ⟨ x ∈ₛ values u ⟩
    x∈ₛvalues = union-ax (sett Op16 (λ i → im i u)) x .snd
      ∣ im i u , ( ∈∈ₛ {a = im i u} {b = sett Op16 (λ i → im i u)} .fst ∣ i , refl ∣₁
                 , x∈ₛim ) ∣₁
```

<!--en-->
The two growth properties are the definitional floor of the cumulative
step: `u` and its members are in `u ∪ {u}`, which the step contains. The
membership-conditioned monotonicity transfers the floor through the subset
and membership hypotheses and re-enters each image value through its
original arguments.
<!--zh-->
两条增长性质是累积 step 的定义性地板：`u` 及其成员都在 `u ∪ {u}` 中，而 step 含有它。带成员条件的单调性把地板经子集与成员假设传输，再让每个像值经其原自变量重新进入。
<!--/-->

```agda
step-⊆ : (u x : V ℓ) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ step u ⟩
step-⊆ = step-in

step-∈ : (u : V ℓ) → ⟨ u ∈ˢ step u ⟩
step-∈ = step-in-self

step-mono∈ : {u v : V ℓ} → ((x : V ℓ) → ⟨ x ∈ u ⟩ → ⟨ x ∈ v ⟩)
           → ⟨ u ∈ v ⟩ → ((x : V ℓ) → ⟨ x ∈ step u ⟩ → ⟨ x ∈ step v ⟩)
step-mono∈ {u} {v} sub u∈v x x∈stepu = PT.rec (snd (x ∈ˢ step v)) go
  (step-out u x x∈stepu)
  where
  go : StepArm u x → ⟨ x ∈ˢ step v ⟩
  go (arm-member x∈u) = step-in v x (sub x x∈u)
  go (arm-self x≡u) = step-in v x (subst (λ t → ⟨ t ∈ˢ v ⟩) (sym x≡u) u∈v)
  go (arm-image i a b a∈u b≡u x≡) =
    step-in-img v x i a b (a-split a∈u) (b-split b≡u) x≡
    where
    a-split : (⟨ a ∈ˢ u ⟩ ⊎ (a ≡ u)) → ⟨ a ∈ˢ u' v ⟩
    a-split (inl a∈u) = u'-in v a (sub a a∈u)
    a-split (inr a≡u) = u'-in v a (subst (λ t → ⟨ t ∈ˢ v ⟩) (sym a≡u) u∈v)
    b-split : (⟨ b ∈ˢ u ⟩ ⊎ (b ≡ u)) → ⟨ b ∈ˢ u' v ⟩
    b-split (inl b∈u) = u'-in v b (sub b b∈u)
    b-split (inr b≡u) = u'-in v b (subst (λ t → ⟨ t ∈ˢ v ⟩) (sym b≡u) u∈v)

u'-member→step : (u x : V ℓ) → ⟨ x ∈ˢ u' u ⟩ → ⟨ x ∈ˢ step u ⟩
u'-member→step u x h = go (u'-cases u x h)
  where
  go : (⟨ x ∈ˢ u ⟩ ⊎ (x ≡ u)) → ⟨ x ∈ˢ step u ⟩
  go (inl x∈u) = step-⊆ u x x∈u
  go (inr x≡u) = subst (λ t → ⟨ t ∈ˢ step u ⟩) (sym x≡u) (step-∈ u)
```

<!--en-->
## The shared frames of the transitivity cases
<!--zh-->
## 传递性情形的共享框架
<!--/-->

<!--en-->
The transitivity analysis of the step for a transitive `u` is a case split
over the sixteen operations. Two frames recur. The first reads the members
of a Kuratowski pair: a member of `pr u v` is the singleton of `u` or the
unordered pair of `u` and `v`, and each is itself an image value over the
argument square: `{u} = F0 u u` and `{u, v} = F0 u v`, so any pair of
members of the argument set lands in the step. The second reads the members
of a singleton: a member of `{a}` is `a` itself, a member of the argument
set.
<!--zh-->
对传递的 `u` 分析 step 的传递性，就是对十六个运算分情形。两个框架反复出现。其一是读 Kuratowski 对的成员：`pr u v` 的成员是 `u` 的单点或 `u`、`v` 的无序对，而两者各自就是参数平方上的像值：`{u} = F0 u u`，`{u, v} = F0 u v`，故参数集成员之对总落进 step。其二是读单点的成员：`{a}` 的成员就是 `a` 本身，即参数集的成员。
<!--/-->

```agda
pr-member : (u v y : V ℓ) → ⟨ y ∈ˢ pr u v ⟩
          → ⟨ (y ≡ₕ ⁅ u ⁆s) ⊔ (y ≡ₕ ⁅ u , v ⁆) ⟩
pr-member u v y h = pairing-ax (⁅ u ⁆s) (⁅ u , v ⁆) y .fst
  (∈∈ₛ {a = y} {b = pr u v} .fst h)

singl-member : (a y : V ℓ) → ⟨ y ∈ˢ ⁅ a ⁆s ⟩ → y ≡ a
singl-member a y h = SetPackage.classification (SingletonPackage a) y .fst
  (∈∈ₛ {a = y} {b = ⁅ a ⁆s} .fst h)

singl≡pair : (a : V ℓ) → ⁅ a ⁆s ≡ ⁅ a , a ⁆
singl≡pair a = extensionality (⁅ a ⁆s) (⁅ a , a ⁆) (sub₁ , sub₂)
  where
  sub₁ : ⟨ ⁅ a ⁆s ⊆ ⁅ a , a ⁆ ⟩
  sub₁ x x∈s = pairing-ax a a x .snd
    ∣ inl (singl-member a x (∈∈ₛ {a = x} {b = ⁅ a ⁆s} .snd x∈s)) ∣₁
  sub₂ : ⟨ ⁅ a , a ⁆ ⊆ ⁅ a ⁆s ⟩
  sub₂ x x∈p = SetPackage.classification (SingletonPackage a) x .snd
    (PT.rec (isSetS x a) (λ { (inl e) → e ; (inr e) → e })
      (pairing-ax a a x .fst x∈p))

pair→step : (u : V ℓ) → (a b y : V ℓ)
          → ⟨ a ∈ˢ u' u ⟩ → ⟨ b ∈ˢ u' u ⟩ → ⟨ y ∈ˢ pr a b ⟩
          → ⟨ y ∈ˢ step u ⟩
pair→step u a b y a∈u' b∈u' h = PT.rec (snd (y ∈ˢ step u)) go (pr-member a b y h)
  where
  go : (⟨ y ≡ₕ ⁅ a ⁆s ⟩ ⊎ ⟨ y ≡ₕ ⁅ a , b ⁆ ⟩) → ⟨ y ∈ˢ step u ⟩
  go (inl y≡s) = step-in-img u y f0 a a a∈u' a∈u'
    (subst (λ t → ⟨ y ≡ₕ t ⟩) (singl≡pair a ∙ sym (Fof-f0 a a)) y≡s)
  go (inr y≡p) = step-in-img u y f0 a b a∈u' b∈u'
    (subst (λ t → ⟨ y ≡ₕ t ⟩) (sym (Fof-f0 a b)) y≡p)

prL-in-doubleUnion : (b u v : V ℓ) → ⟨ pr u v ∈ˢ b ⟩ → ⟨ u ∈ˢ doubleUnion b ⟩
prL-in-doubleUnion b u v h = ∈∈ₛ {a = u} {b = doubleUnion b} .snd
  (union-ax (⋃ b) u .snd
    ∣ ⁅ u ⁆s , ( union-ax b (⁅ u ⁆s) .snd
                  ∣ pr u v , ( ∈∈ₛ {a = pr u v} {b = b} .fst h
                             , pairing-ax (⁅ u ⁆s) (⁅ u , v ⁆) (⁅ u ⁆s) .snd ∣ inl refl ∣₁ ) ∣₁
              , SetPackage.classification (SingletonPackage u) u .snd refl ) ∣₁)

prR-in-doubleUnion : (b u v : V ℓ) → ⟨ pr u v ∈ˢ b ⟩ → ⟨ v ∈ˢ doubleUnion b ⟩
prR-in-doubleUnion b u v h = ∈∈ₛ {a = v} {b = doubleUnion b} .snd
  (union-ax (⋃ b) v .snd
    ∣ ⁅ u , v ⁆ , ( union-ax b (⁅ u , v ⁆) .snd
                     ∣ pr u v , ( ∈∈ₛ {a = pr u v} {b = b} .fst h
                                , pairing-ax (⁅ u ⁆s) (⁅ u , v ⁆) (⁅ u , v ⁆) .snd ∣ inr refl ∣₁ ) ∣₁
                 , pairing-ax u v v .snd ∣ inr refl ∣₁ ) ∣₁)
```

<!--en-->
## The per-operation transitivity cases
<!--zh-->
## 逐运算的传递性情形
<!--/-->

<!--en-->
The step is transitive for transitive inputs, operation by operation. Each
case reads a member `x` of the value `F_i(a,b)` with `a, b ∈ u ∪ {u}`, opens
`y ∈ x` through the operation's specification, and reassembles `y` as a
member of the step: members of the argument set land directly, and the
intermediate objects of pair formation are caught by the pair and tuple
images. Twelve cases close cleanly: `F0`, `F1`, `F2`, `F3`, `F4`, `F5`,
`F6`, `F7`, `F8`, `F9`, `F10`, and `F15`, the five sealed ones through the
read lemmas appended to the operations chapter. The `F3` and `F4` cases are
the ones the tuple operations were engineered for: a member of their triple
values is itself a tuple value, `F11 z (pr u v)` and `F12 z (pr u v)`, at
the existing pair `pr u v ∈ b`, so it lands in the step as a value over the
argument square. The `F11` to `F14` cases close on the pair branch through
the excluded middle (`left b` and `right b` are the components, in the
argument set by transitivity), and their non-pair branches need the images
chapter's private junk facts: the left and right projections of a non-pair
are defined through private `⋂`- and `rightSlice`-internals that neither
reduce nor name from outside this module. That read is recorded as the
batch's remaining blocker; all trails are in the batch report.
<!--zh-->
对传递输入，step 逐运算地传递。每个情形读值 `F_i(a,b)` 的成员 `x`，其中 `a, b ∈ u ∪ {u}`，经该运算的规格拆开 `y ∈ x`，再把 `y` 重组成 step 的成员：参数集的成员直接落下，对形成的中间对象则由对与三元组像捕捉。此处十二个情形干净闭合：`F0`、`F1`、`F2`、`F3`、`F4`、`F5`、`F6`、`F7`、`F8`、`F9`、`F10` 与 `F15`，其中五个被封运算经运算章附录的读引理。`F3` 与 `F4` 的情形正是三元组运算为之而设者：其三元组值的成员本身就是三元组值，即现有对 `pr u v ∈ b` 处的 `F11 z (pr u v)` 与 `F12 z (pr u v)`，于是它作为参数平方上的值落进 step。`F11` 至 `F14` 的情形在对支经排中律闭合 (`left b` 与 `right b` 即两分量，经传递性在参数集中)，其非对支需要像章的私有垃圾事实：非对的左右投影经私有的 `⋂` 与 `rightSlice` 内部定义，在本模块之外既不归约也无从点名。这条缺失的读取记为批次余下的阻碍；全部轨迹都在批次报告中。
<!--/-->

```agda
Trans : V ℓ → Type (ℓ-suc ℓ)
Trans u = {x y : V ℓ} → ⟨ y ∈ˢ x ⟩ → ⟨ x ∈ˢ u ⟩ → ⟨ y ∈ˢ u ⟩

trans-F0 : (u : V ℓ) (tr : Trans u) → (a b x y : V ℓ)
         → ⟨ a ∈ˢ u' u ⟩ → ⟨ b ∈ˢ u' u ⟩ → ⟨ x ≡ₕ F0 a b ⟩ → ⟨ y ∈ˢ x ⟩
         → ⟨ y ∈ˢ step u ⟩
trans-F0 u tr a b x y a∈u' b∈u' x≡ y∈x = PT.rec (snd (y ∈ˢ step u)) go
  (F0-spec a b y .fst
    (subst (λ t → ⟨ y ∈ˢ t ⟩) x≡ y∈x))
  where
  go : (⟨ y ≡ₕ a ⟩ ⊎ ⟨ y ≡ₕ b ⟩) → ⟨ y ∈ˢ step u ⟩
  go (inl y≡a) = u'-member→step u y (subst (λ t → ⟨ t ∈ˢ u' u ⟩) (sym y≡a) a∈u')
  go (inr y≡b) = u'-member→step u y (subst (λ t → ⟨ t ∈ˢ u' u ⟩) (sym y≡b) b∈u')

trans-F1 : (u : V ℓ) (tr : Trans u) → (a b x y : V ℓ)
         → ⟨ a ∈ˢ u' u ⟩ → ⟨ b ∈ˢ u' u ⟩ → ⟨ x ≡ₕ F1 a b ⟩ → ⟨ y ∈ˢ x ⟩
         → ⟨ y ∈ˢ step u ⟩
trans-F1 u tr a b x y a∈u' b∈u' x≡ y∈x = u'-member→step u y
  (u'-trans u tr a y (F1-spec a b y .fst
    (subst (λ t → ⟨ y ∈ˢ t ⟩) (x≡) y∈x) .fst) a∈u')

trans-F2 : (u : V ℓ) (tr : Trans u) → (a b x y : V ℓ)
         → ⟨ a ∈ˢ u' u ⟩ → ⟨ b ∈ˢ u' u ⟩ → ⟨ x ≡ₕ F2 a b ⟩ → ⟨ y ∈ˢ x ⟩
         → ⟨ y ∈ˢ step u ⟩
trans-F2 u tr a b x y a∈u' b∈u' x≡ y∈x = PT.rec (snd (y ∈ˢ step u)) go
  (F2-read a b y (subst (λ t → ⟨ y ∈ˢ t ⟩) (x≡) y∈x))
  where
  go : Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ]
         (⟨ p ∈ˢ a ⟩ × ⟨ q ∈ˢ b ⟩ × ⟨ y ≡ₕ pr p q ⟩) → ⟨ y ∈ˢ step u ⟩
  go (p , q , p∈a , q∈b , y≡) = step-in-img u y f9 p q
    (u'-trans u tr a p p∈a a∈u') (u'-trans u tr b q q∈b b∈u')
    (subst (λ t → ⟨ y ≡ₕ t ⟩) (sym (Fof-f9 p q)) y≡)

trans-F3 : (u : V ℓ) (tr : Trans u) → (a b x y : V ℓ)
         → ⟨ a ∈ˢ u' u ⟩ → ⟨ b ∈ˢ u' u ⟩ → ⟨ x ≡ₕ F3 a b ⟩ → ⟨ y ∈ˢ x ⟩
         → ⟨ y ∈ˢ step u ⟩
trans-F3 u tr a b x y a∈u' b∈u' x≡ y∈x = PT.rec (snd (y ∈ˢ step u)) go
  (F3-read a b y (subst (λ t → ⟨ y ∈ˢ t ⟩) (x≡) y∈x))
  where
  go : Σ[ p ∈ V ℓ ] Σ[ z ∈ V ℓ ] Σ[ q ∈ V ℓ ]
         (⟨ z ∈ˢ a ⟩ × ⟨ pr p q ∈ˢ b ⟩ × ⟨ y ≡ₕ pr p (pr z q) ⟩)
     → ⟨ y ∈ˢ step u ⟩
  go (p , z , q , z∈a , pruv∈b , y≡) =
    step-in-img u y f11 z (pr p q)
      (u'-trans u tr a z z∈a a∈u')
      (u'-trans u tr b (pr p q) pruv∈b b∈u')
      (subst (λ t → ⟨ y ≡ₕ t ⟩)
        (sym (F11-spec z (pr p q) p q refl) ∙ sym (Fof-f11 z (pr p q))) y≡)

trans-F4 : (u : V ℓ) (tr : Trans u) → (a b x y : V ℓ)
         → ⟨ a ∈ˢ u' u ⟩ → ⟨ b ∈ˢ u' u ⟩ → ⟨ x ≡ₕ F4 a b ⟩ → ⟨ y ∈ˢ x ⟩
         → ⟨ y ∈ˢ step u ⟩
trans-F4 u tr a b x y a∈u' b∈u' x≡ y∈x = PT.rec (snd (y ∈ˢ step u)) go
  (F4-read a b y (subst (λ t → ⟨ y ∈ˢ t ⟩) (x≡) y∈x))
  where
  go : Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ] Σ[ z ∈ V ℓ ]
         (⟨ z ∈ˢ a ⟩ × ⟨ pr p q ∈ˢ b ⟩ × ⟨ y ≡ₕ pr p (pr q z) ⟩)
     → ⟨ y ∈ˢ step u ⟩
  go (p , q , z , z∈a , pruv∈b , y≡) =
    step-in-img u y f12 z (pr p q)
      (u'-trans u tr a z z∈a a∈u')
      (u'-trans u tr b (pr p q) pruv∈b b∈u')
      (subst (λ t → ⟨ y ≡ₕ t ⟩)
        (sym (F12-spec z (pr p q) p q refl) ∙ sym (Fof-f12 z (pr p q))) y≡)

trans-F5 : (u : V ℓ) (tr : Trans u) → (a b x y : V ℓ)
         → ⟨ a ∈ˢ u' u ⟩ → ⟨ b ∈ˢ u' u ⟩ → ⟨ x ≡ₕ F5 a b ⟩ → ⟨ y ∈ˢ x ⟩
         → ⟨ y ∈ˢ step u ⟩
trans-F5 u tr a b x y a∈u' b∈u' x≡ y∈x = PT.rec (snd (y ∈ˢ step u)) go
  (F5-spec a b y .fst (subst (λ t → ⟨ y ∈ˢ t ⟩) (x≡) y∈x))
  where
  go : Σ[ v ∈ V ℓ ] ⟨ (v ∈ˢ a) ⊓ (y ∈ˢ v) ⟩ → ⟨ y ∈ˢ step u ⟩
  go (v , v∈a , y∈v) = u'-member→step u y
    (u'-trans u tr v y y∈v (u'-trans u tr a v v∈a a∈u'))

trans-F6 : (u : V ℓ) (tr : Trans u) → (a b x y : V ℓ)
         → ⟨ a ∈ˢ u' u ⟩ → ⟨ b ∈ˢ u' u ⟩ → ⟨ x ≡ₕ F6 a b ⟩ → ⟨ y ∈ˢ x ⟩
         → ⟨ y ∈ˢ step u ⟩
trans-F6 u tr a b x y a∈u' b∈u' x≡ y∈x = PT.rec (snd (y ∈ˢ step u)) go
  (F6-read a b y (subst (λ t → ⟨ y ∈ˢ t ⟩) (x≡) y∈x))
  where
  go : Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ]
         (⟨ pr p q ∈ˢ a ⟩ × ⟨ y ≡ₕ p ⟩) → ⟨ y ∈ˢ step u ⟩
  go (p , q , pruv∈a , y≡p) = u'-member→step u y
    (subst (λ t → ⟨ t ∈ˢ u' u ⟩) (sym y≡p)
      (⋃⋃→u' u tr a p a∈u' (prL-in-doubleUnion a p q pruv∈a)))

trans-F7 : (u : V ℓ) (tr : Trans u) → (a b x y : V ℓ)
         → ⟨ a ∈ˢ u' u ⟩ → ⟨ b ∈ˢ u' u ⟩ → ⟨ x ≡ₕ F7 a b ⟩ → ⟨ y ∈ˢ x ⟩
         → ⟨ y ∈ˢ step u ⟩
trans-F7 u tr a b x y a∈u' b∈u' x≡ y∈x = PT.rec (snd (y ∈ˢ step u)) go
  (F7-read a b y (subst (λ t → ⟨ y ∈ˢ t ⟩) (x≡) y∈x))
  where
  go : Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ]
         (⟨ p ∈ˢ a ⟩ × ⟨ q ∈ˢ a ⟩ × ⟨ p ∈ˢ q ⟩ × ⟨ y ≡ₕ pr p q ⟩)
     → ⟨ y ∈ˢ step u ⟩
  go (p , q , p∈a , q∈a , p∈q , y≡) = step-in-img u y f9 p q
    (u'-trans u tr a p p∈a a∈u') (u'-trans u tr a q q∈a a∈u')
    (subst (λ t → ⟨ y ≡ₕ t ⟩) (sym (Fof-f9 p q)) y≡)

trans-F8 : (u : V ℓ) (tr : Trans u) → (a b x y : V ℓ)
         → ⟨ a ∈ˢ u' u ⟩ → ⟨ b ∈ˢ u' u ⟩ → ⟨ x ≡ₕ F8 a b ⟩ → ⟨ y ∈ˢ x ⟩
         → ⟨ y ∈ˢ step u ⟩
trans-F8 u tr a b x y a∈u' b∈u' x≡ y∈x = PT.rec (snd (y ∈ˢ step u)) go
  (subst ⟨_⟩ (F8-spec a b y) (subst (λ t → ⟨ y ∈ˢ t ⟩) (x≡) y∈x))
  where
  go : Σ[ m ∈ ⟪ b ⟫ ] ⟨ F10 a (⟪ b ⟫↪ m) ≡ₕ y ⟩ → ⟨ y ∈ˢ step u ⟩
  go (m , y≡) = step-in-img u y f10 a (⟪ b ⟫↪ m) a∈u'
    (u'-trans u tr b (⟪ b ⟫↪ m)
      (∈∈ₛ {a = ⟪ b ⟫↪ m} {b = b} .snd (∈ₛ⟪ b ⟫↪ m)) b∈u')
    (subst (λ t → ⟨ y ≡ₕ t ⟩) (sym y≡ ∙ sym (Fof-f10 a (⟪ b ⟫↪ m))) refl)

trans-F9 : (u : V ℓ) (tr : Trans u) → (a b x y : V ℓ)
         → ⟨ a ∈ˢ u' u ⟩ → ⟨ b ∈ˢ u' u ⟩ → ⟨ x ≡ₕ F9 a b ⟩ → ⟨ y ∈ˢ x ⟩
         → ⟨ y ∈ˢ step u ⟩
trans-F9 u tr a b x y a∈u' b∈u' x≡ y∈x = pair→step u a b y a∈u' b∈u'
  (subst (λ t → ⟨ y ∈ˢ t ⟩) (x≡) y∈x)

trans-F10 : (u : V ℓ) (tr : Trans u) → (a b x y : V ℓ)
          → ⟨ a ∈ˢ u' u ⟩ → ⟨ b ∈ˢ u' u ⟩ → ⟨ x ≡ₕ F10 a b ⟩ → ⟨ y ∈ˢ x ⟩
          → ⟨ y ∈ˢ step u ⟩
trans-F10 u tr a b x y a∈u' b∈u' x≡ y∈x = u'-member→step u y
  (u'-trans u tr ⁅ b , y ⁆ y (y-in-pair b y)
    (u'-trans u tr (pr b y) ⁅ b , y ⁆ (pair-in-pr b y)
      (u'-trans u tr a (pr b y)
        (subst ⟨_⟩ (F10-spec a b y) (subst (λ t → ⟨ y ∈ˢ t ⟩) (x≡) y∈x))
        a∈u')))
  where
  y-in-pair : (b y : V ℓ) → ⟨ y ∈ˢ ⁅ b , y ⁆ ⟩
  y-in-pair b y = ∈∈ₛ {a = y} {b = ⁅ b , y ⁆} .snd
    (pairing-ax b y y .snd ∣ inr refl ∣₁)
  pair-in-pr : (b y : V ℓ) → ⟨ ⁅ b , y ⁆ ∈ˢ pr b y ⟩
  pair-in-pr b y = ∈∈ₛ {a = ⁅ b , y ⁆} {b = pr b y} .snd
    (pairing-ax (⁅ b ⁆s) (⁅ b , y ⁆) (⁅ b , y ⁆) .snd ∣ inr refl ∣₁)

isPair : V ℓ → hProp (ℓ-suc ℓ)
isPair b = ( ∥ Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ] ⟨ b ≡ₕ pr p q ⟩ ∥₁ , squash₁ )

singl-in : (a : V ℓ) → ⟨ a ∈ₛ ⁅ a ⁆s ⟩
singl-in a = SetPackage.classification (SingletonPackage a) a .snd refl

left-in-u'-pair : (u : V ℓ) (tr : Trans u) → (b : V ℓ)
                → ⟨ b ∈ˢ u' u ⟩ → ⟨ isPair b ⟩ → ⟨ left b ∈ˢ u' u ⟩
left-in-u'-pair u tr b b∈u' h = PT.rec (snd (left b ∈ˢ u' u)) go h
  where
  go : Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ] ⟨ b ≡ₕ pr p q ⟩ → ⟨ left b ∈ˢ u' u ⟩
  go (p , q , b≡) = subst (λ t → ⟨ t ∈ˢ u' u ⟩) (sym left≡p) p∈u'
    where
    left≡p : left b ≡ p
    left≡p = subst (λ t → left t ≡ p) (sym b≡) (left-spec p q)
    p∈⁅p⁆s : ⟨ p ∈ˢ ⁅ p ⁆s ⟩
    p∈⁅p⁆s = ∈∈ₛ {a = p} {b = ⁅ p ⁆s} .snd (singl-in p)
    ⁅p⁆s∈b : ⟨ ⁅ p ⁆s ∈ˢ b ⟩
    ⁅p⁆s∈b = subst (λ t → ⟨ ⁅ p ⁆s ∈ˢ t ⟩) (sym b≡)
      (∈∈ₛ {a = ⁅ p ⁆s} {b = pr p q} .snd
        (pairing-ax (⁅ p ⁆s) (⁅ p , q ⁆) (⁅ p ⁆s) .snd ∣ inl refl ∣₁))
    p∈u' : ⟨ p ∈ˢ u' u ⟩
    p∈u' = u'-trans u tr ⁅ p ⁆s p p∈⁅p⁆s
      (u'-trans u tr b ⁅ p ⁆s ⁅p⁆s∈b b∈u')

right-in-u'-pair : (u : V ℓ) (tr : Trans u) → (b : V ℓ)
                 → ⟨ b ∈ˢ u' u ⟩ → ⟨ isPair b ⟩ → ⟨ right b ∈ˢ u' u ⟩
right-in-u'-pair u tr b b∈u' h = PT.rec (snd (right b ∈ˢ u' u)) go h
  where
  go : Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ] ⟨ b ≡ₕ pr p q ⟩ → ⟨ right b ∈ˢ u' u ⟩
  go (p , q , b≡) = subst (λ t → ⟨ t ∈ˢ u' u ⟩) (sym right≡q) q∈u'
    where
    right≡q : right b ≡ q
    right≡q = subst (λ t → right t ≡ q) (sym b≡) (right-spec p q)
    q∈⁅p,q⁆ : ⟨ q ∈ˢ ⁅ p , q ⁆ ⟩
    q∈⁅p,q⁆ = ∈∈ₛ {a = q} {b = ⁅ p , q ⁆} .snd
      (pairing-ax p q q .snd ∣ inr refl ∣₁)
    ⁅p,q⁆∈b : ⟨ ⁅ p , q ⁆ ∈ˢ b ⟩
    ⁅p,q⁆∈b = subst (λ t → ⟨ ⁅ p , q ⁆ ∈ˢ t ⟩) (sym b≡)
      (∈∈ₛ {a = ⁅ p , q ⁆} {b = pr p q} .snd
        (pairing-ax (⁅ p ⁆s) (⁅ p , q ⁆) (⁅ p , q ⁆) .snd ∣ inr refl ∣₁))
    q∈u' : ⟨ q ∈ˢ u' u ⟩
    q∈u' = u'-trans u tr ⁅ p , q ⁆ q q∈⁅p,q⁆
      (u'-trans u tr b ⁅ p , q ⁆ ⁅p,q⁆∈b b∈u')

trans-F15 : (u : V ℓ) (tr : Trans u) → (a b x y : V ℓ)
          → ⟨ a ∈ˢ u' u ⟩ → ⟨ b ∈ˢ u' u ⟩ → ⟨ x ≡ₕ F15A a ⟩ → ⟨ y ∈ˢ x ⟩
          → ⟨ y ∈ˢ step u ⟩
trans-F15 u tr a b x y a∈u' b∈u' x≡ y∈x = u'-member→step u y
  (u'-trans u tr a y (F15A-spec a y (subst (λ t → ⟨ y ∈ˢ t ⟩) (x≡) y∈x)) a∈u')
```

## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The concrete operator is in place and sealed: the sixteen per-operation
image sets over the argument square, the step as their union, and the
membership characterization as the only surface. The growth properties
discharge from the pairing image alone, and the membership-conditioned
monotonicity discharges from the subset plus membership hypotheses.
Twelve per-operation transitivity cases close cleanly through the shared
pair and argument frames, the `F3`/`F4` cases through the tuple values
`F11`/`F12` at the existing pair; the `F11` to `F14` non-pair branches need
the images chapter's private junk facts, recorded in the batch report. The
instantiation of the hierarchy engine and the limit-level closure facts
await the transitivity question's resolution.
<!--zh-->
具体算子就位并已封印：参数平方上的十六个逐运算像集、作为其并的 step，以及作为唯一表面的隶属刻画。增长性质单从配对像清偿，带成员条件的新单调性从子集加成员假设清偿。十二个逐运算传递性情形经共享的对与参数框架干净闭合，`F3`/`F4` 的情形经现有对处的三元组值 `F11`/`F12` 闭合；`F11` 至 `F14` 的非对支需要像章的私有垃圾事实，记入批次报告。层级引擎的实例化与极限层闭包事实等待传递性问题的解决。
<!--/-->

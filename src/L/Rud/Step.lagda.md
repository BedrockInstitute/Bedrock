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
the concrete operator. Membership of `u` and of its members in the step
comes from the pairing image, the classical singleton route: `u` is a member
of `F0 u u = {u}`, and a member `x` of `u` is a member of `F0 x u = {x,u}`,
both of which are images over the argument square. The transitivity of the
step for transitive inputs is then analysed operation by operation, sharing
the frame that the tuple operations catch the intermediate objects of pair
formation. Monotonicity of the step in its argument is examined and its
outcome recorded in the batch report.
<!--zh-->
初步函数路线的层级引擎是抽象的：它只拿一个单步算子连同四条性质，就别无其他地建起 S-塔。本章供给具体算子：对 Schindler-Zeman 基的十六个运算各取 `u ∪ {u}` 之平方上的像值集 (SZ p. 10，方程 I.1)，作为该平方的小表示上的 `sett`{.Agda} 造出，step 则是这十六个像之并，即初步函数闭包的一步。消费者读取的隶属刻画由 step-in 与 step-out 引理陈述，构造本身被封起，下游无从展开。

本章还清偿望远镜四条性质需要从具体算子得到的那部分。`u` 及其成员在 step 中的隶属来自配对像，即经典的单点路线：`u` 是 `F0 u u = {u}` 的成员，`u` 的成员 `x` 是 `F0 x u = {x,u}` 的成员，两者都是参数平方上的像。接着逐运算分析 step 对传递输入的传递性，共享「三元组运算捕捉对形成的中间对象」这一框架。step 对其自变量的单调性经过考查，其结果记入批次报告。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; sett )

module L.Rud.Step {ℓ : Level} (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr )
open import L.Rud.Ops {ℓ}
  using ( F0; F1; F2; F3; F4; F5; F6; F7; F9
        ; F0-spec; F1-spec; F5-spec; F9-spec )
open import L.Rud.Images {ℓ}
  using ( F8; F10; F11; F12; F13; F14; left; right; F8-spec; F10-spec )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sum.Properties using ( isProp⊎ )
import Cubical.Data.Empty as Empty
open import Cubical.Functions.Logic using ( ∃[]-syntax )
open import Cubical.Foundations.Equiv using ( fiber )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber; _≡ₕ_ )
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
The step is the union, over the sixteen indices, of the unions of the image
sets: a member of the step is a member of some value `F_i(a,b)` with
`a, b ∈ u ∪ {u}`. The construction is sealed `opaque`{.Agda}, and the
characterization is exported as the two directions `step-in` and
`step-out`{.Agda}, which are the only surface the rest of the route reads.
<!--zh-->
step 是十六个索引上的并，每个索引再取其像集之并：step 的成员是某个值 `F_i(a,b)` 的成员，其中 `a, b ∈ u ∪ {u}`。构造以 `opaque`{.Agda} 封印，刻画以 `step-in` 与 `step-out`{.Agda} 两个方向导出，这是路线其余部分唯一读取的表面。
<!--/-->

```agda
opaque
  step : V ℓ → V ℓ
  step u = ⋃ (sett Op16 (λ i → ⋃ (im i u)))

opaque
  unfolding step
  step-out : (u x : V ℓ) → ⟨ x ∈ˢ step u ⟩
           → ∥ Σ[ i ∈ Op16 ] Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
                (⟨ a ∈ˢ u' u ⟩ × ⟨ b ∈ˢ u' u ⟩ × ⟨ x ∈ˢ Fof i a b ⟩) ∥₁
  step-out u x h = PT.rec squash₁ go₁
    (union-ax (sett Op16 (λ i → ⋃ (im i u))) x .fst
      (∈∈ₛ {a = x} {b = step u} .fst h))
    where
    go₁ : Σ[ v ∈ V ℓ ]
            (⟨ v ∈ₛ sett Op16 (λ i → ⋃ (im i u)) ⟩ × ⟨ x ∈ₛ v ⟩)
        → ∥ Σ[ i ∈ Op16 ] Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
             (⟨ a ∈ˢ u' u ⟩ × ⟨ b ∈ˢ u' u ⟩ × ⟨ x ∈ˢ Fof i a b ⟩) ∥₁
    go₁ (v , v∈ₛS , x∈ₛv) = PT.rec squash₁ go₂
      (∈∈ₛ {a = v} {b = sett Op16 (λ i → ⋃ (im i u))} .snd v∈ₛS)
      where
      go₂ : Σ[ j ∈ Op16 ] (⋃ (im j u) ≡ v)
          → ∥ Σ[ i ∈ Op16 ] Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
               (⟨ a ∈ˢ u' u ⟩ × ⟨ b ∈ˢ u' u ⟩ × ⟨ x ∈ˢ Fof i a b ⟩) ∥₁
      go₂ (j , q) = PT.rec squash₁ go₃
        (union-ax (im j u) x .fst
          (subst (λ t → ⟨ x ∈ₛ t ⟩) (sym q) x∈ₛv))
        where
        go₃ : Σ[ w ∈ V ℓ ] (⟨ w ∈ₛ im j u ⟩ × ⟨ x ∈ₛ w ⟩)
            → ∥ Σ[ i ∈ Op16 ] Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
                 (⟨ a ∈ˢ u' u ⟩ × ⟨ b ∈ˢ u' u ⟩ × ⟨ x ∈ˢ Fof i a b ⟩) ∥₁
        go₃ (w , w∈ₛim , x∈ₛw) = PT.rec squash₁ go₄
          (∈∈ₛ {a = w} {b = im j u} .snd w∈ₛim)
          where
          go₄ : Σ[ p ∈ ⟪ u' u ⟫ × ⟪ u' u ⟫ ]
                  (Fof j (⟪ u' u ⟫↪ (p .fst)) (⟪ u' u ⟫↪ (p .snd)) ≡ w)
              → ∥ Σ[ i ∈ Op16 ] Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
                   (⟨ a ∈ˢ u' u ⟩ × ⟨ b ∈ˢ u' u ⟩ × ⟨ x ∈ˢ Fof i a b ⟩) ∥₁
          go₄ (p , r) = ∣ j
            , ⟪ u' u ⟫↪ (p .fst) , ⟪ u' u ⟫↪ (p .snd)
            , ( ∈∈ₛ {a = ⟪ u' u ⟫↪ (p .fst)} {b = u' u} .snd (∈ₛ⟪ u' u ⟫↪ (p .fst))
              , ∈∈ₛ {a = ⟪ u' u ⟫↪ (p .snd)} {b = u' u} .snd (∈ₛ⟪ u' u ⟫↪ (p .snd))
              , subst (λ t → ⟨ x ∈ˢ t ⟩) (sym r)
                  (∈∈ₛ {a = x} {b = w} .snd x∈ₛw) ) ∣₁

  step-in : (u x : V ℓ) (i : Op16) (a b : V ℓ)
          → ⟨ a ∈ˢ u' u ⟩ → ⟨ b ∈ˢ u' u ⟩ → ⟨ x ∈ˢ Fof i a b ⟩
          → ⟨ x ∈ˢ step u ⟩
  step-in u x i a b a∈u' b∈u' x∈Fab =
    ∈∈ₛ {a = x} {b = step u} .snd
      (union-ax (sett Op16 (λ i → ⋃ (im i u))) x .snd
        ∣ ⋃ (im i u) , ( im∈ₛS , x∈ₛ⋃im ) ∣₁)
    where
    fa : fiber (⟪ u' u ⟫↪) a
    fa = ∈-asFiber {a = a} {b = u' u} a∈u'
    fb : fiber (⟪ u' u ⟫↪) b
    fb = ∈-asFiber {a = b} {b = u' u} b∈u'
    a' : V ℓ
    a' = ⟪ u' u ⟫↪ (fa .fst)
    b' : V ℓ
    b' = ⟪ u' u ⟫↪ (fb .fst)
    x∈ₛFab' : ⟨ x ∈ₛ Fof i a' b' ⟩
    x∈ₛFab' = subst (λ t → ⟨ x ∈ₛ t ⟩)
      (sym (cong₂ (Fof i) (fa .snd) (fb .snd))) (∈∈ₛ {a = x} {b = Fof i a b} .fst x∈Fab)
    x∈ₛ⋃im : ⟨ x ∈ₛ ⋃ (im i u) ⟩
    x∈ₛ⋃im = union-ax (im i u) x .snd
      ∣ Fof i a' b'
        , ( ∈∈ₛ {a = Fof i a' b'} {b = im i u} .fst
            ∣ (fa .fst , fb .fst) , refl ∣₁
        , x∈ₛFab' ) ∣₁
    im∈ₛS : ⟨ ⋃ (im i u) ∈ₛ sett Op16 (λ i → ⋃ (im i u)) ⟩
    im∈ₛS = ∈∈ₛ {a = ⋃ (im i u)}
      {b = sett Op16 (λ i → ⋃ (im i u))} .fst
      ∣ i , refl ∣₁
```

<!--en-->
The two growth properties follow from the pairing image alone. A member `x`
of `u` lies in `F0 x u = {x,u}`, and `u` itself lies in `F0 u u = {u}`;
both images take their arguments from the argument square, so the step-in
direction places them in the step.
<!--zh-->
两条增长性质单独从配对像得出。`u` 的成员 `x` 落在 `F0 x u = {x,u}` 中，`u` 本身落在 `F0 u u = {u}` 中；两个像都从参数平方取自变量，于是 step-in 方向把它们放进 step。
<!--/-->

```agda
step-⊆ : (u x : V ℓ) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ step u ⟩
step-⊆ u x x∈u = step-in u x f0 x u (u'-in u x x∈u) (u-self-in u)
  (F0-spec x u x .snd ∣ inl refl ∣₁)

step-∈ : (u : V ℓ) → ⟨ u ∈ˢ step u ⟩
step-∈ u = step-in u u f0 u u (u-self-in u) (u-self-in u)
  (F0-spec u u u .snd ∣ inl refl ∣₁)

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
unordered pair of `u` and `v`, and both are members of the pair images
`F9 u u` and `F9 u v`, so any pair of members of the argument set lands in
the step. The second reads the members of a singleton: a member of `{a}` is
`a` itself, a member of the argument set.
<!--zh-->
对传递的 `u` 分析 step 的传递性，就是对十六个运算分情形。两个框架反复出现。其一是读 Kuratowski 对的成员：`pr u v` 的成员是 `u` 的单点或 `u`、`v` 的无序对，两者都是对像 `F9 u u` 与 `F9 u v` 的成员，故参数集成员之对总落进 step。其二是读单点的成员：`{a}` 的成员就是 `a` 本身，即参数集的成员。
<!--/-->

```agda
pr-member : (u v y : V ℓ) → ⟨ y ∈ˢ pr u v ⟩
          → ⟨ (y ≡ₕ ⁅ u ⁆s) ⊔ (y ≡ₕ ⁅ u , v ⁆) ⟩
pr-member u v y h = pairing-ax (⁅ u ⁆s) (⁅ u , v ⁆) y .fst
  (∈∈ₛ {a = y} {b = pr u v} .fst h)

singl-member : (a y : V ℓ) → ⟨ y ∈ˢ ⁅ a ⁆s ⟩ → y ≡ a
singl-member a y h = SetPackage.classification (SingletonPackage a) y .fst
  (∈∈ₛ {a = y} {b = ⁅ a ⁆s} .fst h)

pair→step : (u : V ℓ) (tr : {x y : V ℓ} → ⟨ y ∈ˢ x ⟩ → ⟨ x ∈ˢ u ⟩ → ⟨ y ∈ˢ u ⟩)
          → (a b y : V ℓ)
          → ⟨ a ∈ˢ u' u ⟩ → ⟨ b ∈ˢ u' u ⟩ → ⟨ y ∈ˢ pr a b ⟩
          → ⟨ y ∈ˢ step u ⟩
pair→step u tr a b y a∈u' b∈u' h = PT.rec (snd (y ∈ˢ step u)) go (pr-member a b y h)
  where
  go : (⟨ y ≡ₕ ⁅ a ⁆s ⟩ ⊎ ⟨ y ≡ₕ ⁅ a , b ⁆ ⟩) → ⟨ y ∈ˢ step u ⟩
  go (inl y≡s) = step-in u y f9 a a a∈u' a∈u' (F9-spec a a y .snd ∣ inl y≡s ∣₁)
  go (inr y≡p) = step-in u y f9 a b a∈u' b∈u' (F9-spec a b y .snd ∣ inr y≡p ∣₁)

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
images. Nine cases close cleanly here: `F0`, `F1`, `F5`, `F8`, `F9`, `F10`,
`F11`, `F12`, and `F15`. The cases for `F2`-`F4`, `F6`, and `F7` are held
back because the operations chapter seals their specifications' right-hand
sides `opaque`{.Agda}, so the membership decompositions are not reachable
from outside; the cases for `F13` and `F14` carry an open sub-obligation on
the junk behaviour of the right projection. All three trails are recorded in
the batch report.
<!--zh-->
对传递输入，step 逐运算地传递。每个情形读值 `F_i(a,b)` 的成员 `x`，其中 `a, b ∈ u ∪ {u}`，经该运算的规格拆开 `y ∈ x`，再把 `y` 重组成 step 的成员：参数集的成员直接落下，对形成的中间对象则由对与三元组像捕捉。此处九个情形干净闭合：`F0`、`F1`、`F5`、`F8`、`F9`、`F10`、`F11`、`F12` 与 `F15`。`F2`-`F4`、`F6`、`F7` 的情形因运算章把规格右侧封以 `opaque`{.Agda}、隶属拆解从外部不可达而搁置；`F13` 与 `F14` 的情形带着右投影垃圾行为的开放子义务。三条轨迹都记入批次报告。
<!--/-->

```agda
Trans : V ℓ → Type (ℓ-suc ℓ)
Trans u = {x y : V ℓ} → ⟨ y ∈ˢ x ⟩ → ⟨ x ∈ˢ u ⟩ → ⟨ y ∈ˢ u ⟩

trans-F0 : (u : V ℓ) (tr : Trans u) → (a b x y : V ℓ)
         → ⟨ a ∈ˢ u' u ⟩ → ⟨ b ∈ˢ u' u ⟩ → ⟨ x ∈ˢ F0 a b ⟩ → ⟨ y ∈ˢ x ⟩
         → ⟨ y ∈ˢ step u ⟩
trans-F0 u tr a b x y a∈u' b∈u' x∈F0ab y∈x = PT.rec (snd (y ∈ˢ step u)) go
  (F0-spec a b x .fst x∈F0ab)
  where
  go : (⟨ x ≡ₕ a ⟩ ⊎ ⟨ x ≡ₕ b ⟩) → ⟨ y ∈ˢ step u ⟩
  go (inl x≡a) = u'-member→step u y
    (u'-trans u tr a y (subst (λ t → ⟨ y ∈ˢ t ⟩) x≡a y∈x) a∈u')
  go (inr x≡b) = u'-member→step u y
    (u'-trans u tr b y (subst (λ t → ⟨ y ∈ˢ t ⟩) x≡b y∈x) b∈u')

trans-F1 : (u : V ℓ) (tr : Trans u) → (a b x y : V ℓ)
         → ⟨ a ∈ˢ u' u ⟩ → ⟨ b ∈ˢ u' u ⟩ → ⟨ x ∈ˢ F1 a b ⟩ → ⟨ y ∈ˢ x ⟩
         → ⟨ y ∈ˢ step u ⟩
trans-F1 u tr a b x y a∈u' b∈u' x∈F1ab y∈x = u'-member→step u y
  (u'-trans u tr x y y∈x
    (u'-trans u tr a x (F1-spec a b x .fst x∈F1ab .fst) a∈u'))

trans-F5 : (u : V ℓ) (tr : Trans u) → (a b x y : V ℓ)
         → ⟨ a ∈ˢ u' u ⟩ → ⟨ b ∈ˢ u' u ⟩ → ⟨ x ∈ˢ F5 a b ⟩ → ⟨ y ∈ˢ x ⟩
         → ⟨ y ∈ˢ step u ⟩
trans-F5 u tr a b x y a∈u' b∈u' x∈F5ab y∈x = PT.rec (snd (y ∈ˢ step u)) go
  (F5-spec a b x .fst x∈F5ab)
  where
  go : Σ[ v ∈ V ℓ ] ⟨ (v ∈ˢ a) ⊓ (x ∈ˢ v) ⟩ → ⟨ y ∈ˢ step u ⟩
  go (v , v∈a , x∈v) = u'-member→step u y
    (u'-trans u tr x y y∈x
      (u'-trans u tr v x x∈v (u'-trans u tr a v v∈a a∈u')))

trans-F8 : (u : V ℓ) (tr : Trans u) → (a b x y : V ℓ)
         → ⟨ a ∈ˢ u' u ⟩ → ⟨ b ∈ˢ u' u ⟩ → ⟨ x ∈ˢ F8 a b ⟩ → ⟨ y ∈ˢ x ⟩
         → ⟨ y ∈ˢ step u ⟩
trans-F8 u tr a b x y a∈u' b∈u' x∈F8ab y∈x = PT.rec (snd (y ∈ˢ step u)) go
  (subst ⟨_⟩ (F8-spec a b x) x∈F8ab)
  where
  go : Σ[ m ∈ ⟪ b ⟫ ] ⟨ F10 a (⟪ b ⟫↪ m) ≡ₕ x ⟩ → ⟨ y ∈ˢ step u ⟩
  go (m , x≡F10az) = let z = ⟪ b ⟫↪ m in
    u'-member→step u y
      (u'-trans u tr ⁅ z , y ⁆ y (y-in-pair z y)
        (u'-trans u tr (pr z y) ⁅ z , y ⁆ (pair-in-pr z y)
          (u'-trans u tr a (pr z y)
            (subst ⟨_⟩ (F10-spec a z y)
              (subst (λ t → ⟨ y ∈ˢ t ⟩) (sym x≡F10az) y∈x))
            a∈u')))
    where
    y-in-pair : (z y : V ℓ) → ⟨ y ∈ˢ ⁅ z , y ⁆ ⟩
    y-in-pair z y = ∈∈ₛ {a = y} {b = ⁅ z , y ⁆} .snd
      (pairing-ax z y y .snd ∣ inr refl ∣₁)
    pair-in-pr : (z y : V ℓ) → ⟨ ⁅ z , y ⁆ ∈ˢ pr z y ⟩
    pair-in-pr z y = ∈∈ₛ {a = ⁅ z , y ⁆} {b = pr z y} .snd
      (pairing-ax (⁅ z ⁆s) (⁅ z , y ⁆) (⁅ z , y ⁆) .snd ∣ inr refl ∣₁)

trans-F9 : (u : V ℓ) (tr : Trans u) → (a b x y : V ℓ)
         → ⟨ a ∈ˢ u' u ⟩ → ⟨ b ∈ˢ u' u ⟩ → ⟨ x ∈ˢ F9 a b ⟩ → ⟨ y ∈ˢ x ⟩
         → ⟨ y ∈ˢ step u ⟩
trans-F9 u tr a b x y a∈u' b∈u' x∈F9ab y∈x = PT.rec (snd (y ∈ˢ step u)) go
  (F9-spec a b x .fst x∈F9ab)
  where
  go : (⟨ x ≡ₕ ⁅ a ⁆s ⟩ ⊎ ⟨ x ≡ₕ ⁅ a , b ⁆ ⟩) → ⟨ y ∈ˢ step u ⟩
  go (inl x≡s) = u'-member→step u y
    (subst (λ t → ⟨ t ∈ˢ u' u ⟩) (sym (singl-member a y
      (subst (λ t → ⟨ y ∈ˢ t ⟩) x≡s y∈x))) a∈u')
  go (inr x≡p) = PT.rec (snd (y ∈ˢ step u)) go'
    (pairing-ax a b y .fst (∈∈ₛ {a = y} {b = ⁅ a , b ⁆} .fst
      (subst (λ t → ⟨ y ∈ˢ t ⟩) x≡p y∈x)))
    where
    go' : (⟨ y ≡ₕ a ⟩ ⊎ ⟨ y ≡ₕ b ⟩) → ⟨ y ∈ˢ step u ⟩
    go' (inl y≡a) = u'-member→step u y (subst (λ t → ⟨ t ∈ˢ u' u ⟩) (sym y≡a) a∈u')
    go' (inr y≡b) = u'-member→step u y (subst (λ t → ⟨ t ∈ˢ u' u ⟩) (sym y≡b) b∈u')

trans-F10 : (u : V ℓ) (tr : Trans u) → (a b x y : V ℓ)
          → ⟨ a ∈ˢ u' u ⟩ → ⟨ b ∈ˢ u' u ⟩ → ⟨ x ∈ˢ F10 a b ⟩ → ⟨ y ∈ˢ x ⟩
          → ⟨ y ∈ˢ step u ⟩
trans-F10 u tr a b x y a∈u' b∈u' x∈F10ab y∈x = u'-member→step u y
  (u'-trans u tr x y y∈x
    (u'-trans u tr ⁅ b , x ⁆ x (x-in-pair b x)
      (u'-trans u tr (pr b x) ⁅ b , x ⁆ (pair-in-pr b x)
        (u'-trans u tr a (pr b x) (subst ⟨_⟩ (F10-spec a b x) x∈F10ab) a∈u'))))
  where
  x-in-pair : (b x : V ℓ) → ⟨ x ∈ˢ ⁅ b , x ⁆ ⟩
  x-in-pair b x = ∈∈ₛ {a = x} {b = ⁅ b , x ⁆} .snd
    (pairing-ax b x x .snd ∣ inr refl ∣₁)
  pair-in-pr : (b x : V ℓ) → ⟨ ⁅ b , x ⁆ ∈ˢ pr b x ⟩
  pair-in-pr b x = ∈∈ₛ {a = ⁅ b , x ⁆} {b = pr b x} .snd
    (pairing-ax (⁅ b ⁆s) (⁅ b , x ⁆) (⁅ b , x ⁆) .snd ∣ inr refl ∣₁)

trans-F11 : (u : V ℓ) (tr : Trans u) → (a b x y : V ℓ)
          → ⟨ a ∈ˢ u' u ⟩ → ⟨ b ∈ˢ u' u ⟩ → ⟨ x ∈ˢ F11 a b ⟩ → ⟨ y ∈ˢ x ⟩
          → ⟨ y ∈ˢ step u ⟩
trans-F11 u tr a b x y a∈u' b∈u' x∈F11ab y∈x = PT.rec (snd (y ∈ˢ step u)) go
  (pairing-ax (⁅ left b ⁆s) (⁅ left b , pr a (right b) ⁆) x .fst
    (∈∈ₛ {a = x} {b = F11 a b} .fst x∈F11ab))
  where
  left∈step : ⟨ left b ∈ˢ step u ⟩
  left∈step = step-in u (left b) f13 b b b∈u' b∈u'
    (∈∈ₛ {a = left b} {b = F13 b b} .snd
      (pairing-ax (left b) (pr (right b) b) (left b) .snd ∣ inl refl ∣₁))
  go : (⟨ x ≡ₕ ⁅ left b ⁆s ⟩ ⊎ ⟨ x ≡ₕ ⁅ left b , pr a (right b) ⁆ ⟩)
     → ⟨ y ∈ˢ step u ⟩
  go (inl x≡s) = subst (λ t → ⟨ t ∈ˢ step u ⟩)
    (sym (singl-member (left b) y
      (subst (λ t → ⟨ y ∈ˢ t ⟩) x≡s y∈x))) left∈step
  go (inr x≡p) = PT.rec (snd (y ∈ˢ step u)) go'
    (pairing-ax (left b) (pr a (right b)) y .fst
      (∈∈ₛ {a = y} {b = ⁅ left b , pr a (right b) ⁆} .fst
        (subst (λ t → ⟨ y ∈ˢ t ⟩) x≡p y∈x)))
    where
    go' : (⟨ y ≡ₕ left b ⟩ ⊎ ⟨ y ≡ₕ pr a (right b) ⟩) → ⟨ y ∈ˢ step u ⟩
    go' (inl y≡l) = subst (λ t → ⟨ t ∈ˢ step u ⟩) (sym y≡l) left∈step
    go' (inr y≡p) = subst (λ t → ⟨ t ∈ˢ step u ⟩) (sym y≡p)
      (step-in u (pr a (right b)) f14 a b a∈u' b∈u'
        (∈∈ₛ {a = pr a (right b)} {b = F14 a b} .snd
          (pairing-ax (left b) (pr a (right b)) (pr a (right b)) .snd ∣ inr refl ∣₁)))

trans-F12 : (u : V ℓ) (tr : Trans u) → (a b x y : V ℓ)
          → ⟨ a ∈ˢ u' u ⟩ → ⟨ b ∈ˢ u' u ⟩ → ⟨ x ∈ˢ F12 a b ⟩ → ⟨ y ∈ˢ x ⟩
          → ⟨ y ∈ˢ step u ⟩
trans-F12 u tr a b x y a∈u' b∈u' x∈F12ab y∈x = PT.rec (snd (y ∈ˢ step u)) go
  (pairing-ax (⁅ left b ⁆s) (⁅ left b , pr (right b) a ⁆) x .fst
    (∈∈ₛ {a = x} {b = F12 a b} .fst x∈F12ab))
  where
  left∈step : ⟨ left b ∈ˢ step u ⟩
  left∈step = step-in u (left b) f13 b b b∈u' b∈u'
    (∈∈ₛ {a = left b} {b = F13 b b} .snd
      (pairing-ax (left b) (pr (right b) b) (left b) .snd ∣ inl refl ∣₁))
  go : (⟨ x ≡ₕ ⁅ left b ⁆s ⟩ ⊎ ⟨ x ≡ₕ ⁅ left b , pr (right b) a ⁆ ⟩)
     → ⟨ y ∈ˢ step u ⟩
  go (inl x≡s) = subst (λ t → ⟨ t ∈ˢ step u ⟩)
    (sym (singl-member (left b) y
      (subst (λ t → ⟨ y ∈ˢ t ⟩) x≡s y∈x))) left∈step
  go (inr x≡p) = PT.rec (snd (y ∈ˢ step u)) go'
    (pairing-ax (left b) (pr (right b) a) y .fst
      (∈∈ₛ {a = y} {b = ⁅ left b , pr (right b) a ⁆} .fst
        (subst (λ t → ⟨ y ∈ˢ t ⟩) x≡p y∈x)))
    where
    go' : (⟨ y ≡ₕ left b ⟩ ⊎ ⟨ y ≡ₕ pr (right b) a ⟩) → ⟨ y ∈ˢ step u ⟩
    go' (inl y≡l) = subst (λ t → ⟨ t ∈ˢ step u ⟩) (sym y≡l) left∈step
    go' (inr y≡p) = subst (λ t → ⟨ t ∈ˢ step u ⟩) (sym y≡p)
      (step-in u (pr (right b) a) f13 a b a∈u' b∈u'
        (∈∈ₛ {a = pr (right b) a} {b = F13 a b} .snd
          (pairing-ax (left b) (pr (right b) a) (pr (right b) a) .snd ∣ inr refl ∣₁)))

trans-F15 : (u : V ℓ) (tr : Trans u) → (a b x y : V ℓ)
          → ⟨ a ∈ˢ u' u ⟩ → ⟨ b ∈ˢ u' u ⟩ → ⟨ x ∈ˢ F15A a ⟩ → ⟨ y ∈ˢ x ⟩
          → ⟨ y ∈ˢ step u ⟩
trans-F15 u tr a b x y a∈u' b∈u' x∈F15ab y∈x = u'-member→step u y
  (u'-trans u tr x y y∈x (u'-trans u tr a x (F15A-spec a x x∈F15ab) a∈u'))
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The concrete operator is in place and sealed: the sixteen per-operation
image sets over the argument square, the step as their union, and the
membership characterization as the only surface. The growth properties
discharge from the pairing image alone. Nine per-operation transitivity
cases close cleanly through the shared pair and argument frames; the
remaining seven are recorded as trails, as is the monotonicity obligation,
whose universal form no sixteen-image step can satisfy. The instantiation
of the hierarchy engine and the limit-level closure facts await the
telescope's reshaping, all trails documented in the batch report.
<!--zh-->
具体算子就位并已封印：参数平方上的十六个逐运算像集、作为其并的 step，以及作为唯一表面的隶属刻画。增长性质单从配对像清偿。九个逐运算传递性情形经共享的对与参数框架干净闭合；其余七个连同单调性义务一并记入轨迹，而单调性的全称形式是任何十六像 step 都无法满足的。层级引擎的实例化与极限层闭包事实等待望远镜重塑，全部轨迹记录在批次报告中。
<!--/-->

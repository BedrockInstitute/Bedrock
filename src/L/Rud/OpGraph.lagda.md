# The operation graphs in variables

<!--en-->
The description chapter turned each operation's specification into a formula
over a carrier whose satisfaction characterizes membership in the image
`v ∈ Fof i a b`, with the arguments as constants. This chapter trades the
constants for variables: for each operation a formula `graphᵢ` in the three
variables `(x, u, v)` whose satisfaction at the carrier says `x = Fof i u v`,
with the two-way adequacy as a direction pair. The trade is the parameter
chapter's: each constant-form description is abstracted by `placeFo`, its
adequacy travels through `⊨-place`, and the extensional closure of the
variable shape is one generic frame instantiated per operation.
<!--zh-->
描述章把每个运算的规格译成载体上的一条公式，其满足刻画像中的隶属`v ∈ Fof i a b`，实参以常量的身份入场。本章把常量换成变量：对每个运算给出一条三变量 `(x, u, v)` 的公式 `graphᵢ`，其在载体处的满足说 `x = Fof i u v`，双向适足以方向对陈述。这笔交易就是参数章的：每条常量形描述经 `placeFo` 抽象，其适足经`⊨-place` 旅行，变量形的外延闭包是一个泛型框架，逐运算实例化。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module L.Rud.OpGraph {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure; Transitive )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import FOL.Syntax using
  ( Formula; Term; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ∀̇_; ∃̇_; ∀̇∈; ∃̇∈ )
import FOL.Semantics
open import FOL.Manipulation.Parameters
  using ( countFo; constantsFo; placeFo )
import FOL.Manipulation.Parameters
import FOL.Manipulation.Relabelling
open import FOL.Manipulation.Relabelling using ( embed )
open import L.Rud.Describe {ℓ}
  using ( module F0Desc; module F1Desc; module F5Desc; module F10Desc; module F2Desc )
open import L.Rud.Step {ℓ} lem A
  using ( f0; f1; f2; f5; f10; Fof
        ; Fof-f0; Fof-f1; Fof-f2; Fof-f5; Fof-f10 )
open import L.Rud.Switch {ℓ} lem A using ( module Hops )
import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈-asFiber; extensionality )
open import Cubical.Data.Vec using ( lookup; _++_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module SemA = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemA.At (⟪ A ⟫) (⟪ A ⟫↪) using ( _⊨_ )
open SemA using ( _^_ )
```

<!--en-->
## The empty-domain irrelevance
<!--zh-->
## 空域无关性
<!--/-->

<!--en-->
The abstraction's output sits over the empty constant domain, and the
parameter chapter evaluates it with the empty-type eliminator as the
interpretation, while the relabelling kit evaluates it with the carrier's
interpretation composed after the eliminator. A formula over the empty domain
carries no constant, so the two evaluations agree; the little induction below
is the one mechanical price of entering the carrier's syntax at all.
<!--zh-->
抽象的产物坐在空常量域上，参数章以空型消去子为解释求值它，而重标工具组以载体的解释接在消去子之后求值它。空域上的公式不携带常量，故两次求值一致；下面这趟小归纳就是进入载体语法的全部机械代价。
<!--/-->

```agda
private
  module Sem⊥ = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  module At∅₁ = Sem⊥.At (⊥* {ℓ-zero}) Empty.rec*
  module At∅₂ = Sem⊥.At (⊥* {ℓ-zero}) (λ b → ⟪ A ⟫↪ (Empty.rec* b))

  open At∅₁ renaming ( _⊨_ to _⊨₁_ ; ⟦_⟧ to ⟦_⟧₁ )
  open At∅₂ renaming ( _⊨_ to _⊨₂_ ; ⟦_⟧ to ⟦_⟧₂ )

  tm⊥-irrel : {n : ℕ} (t : Term (⊥* {ℓ-zero}) n) (γ : S ^ n)
            → ⟦ t ⟧₁ γ ≡ ⟦ t ⟧₂ γ
  tm⊥-irrel (con k) γ = Empty.rec* k
  tm⊥-irrel (var i) γ = refl

  sat⊥-irrel : {n : ℕ} (ψ : Formula (⊥* {ℓ-zero}) n) (γ : S ^ n)
             → (γ ⊨₁ ψ) ≡ (γ ⊨₂ ψ)
  sat⊥-irrel (t ∈̇ u) γ = cong₂ _∈ˢ_ (tm⊥-irrel t γ) (tm⊥-irrel u γ)
  sat⊥-irrel (t ≐ u) γ = cong₂ _≈ˢ_ (tm⊥-irrel t γ) (tm⊥-irrel u γ)
  sat⊥-irrel (φ ∧̇ ψ) γ = cong₂ _⊓_ (sat⊥-irrel φ γ) (sat⊥-irrel ψ γ)
  sat⊥-irrel (φ ∨̇ ψ) γ = cong₂ _⊔_ (sat⊥-irrel φ γ) (sat⊥-irrel ψ γ)
  sat⊥-irrel (φ ⇒̇ ψ) γ = cong₂ _⇒_ (sat⊥-irrel φ γ) (sat⊥-irrel ψ γ)
  sat⊥-irrel (¬̇ φ)   γ = cong ¬_ (sat⊥-irrel φ γ)
  sat⊥-irrel Formula.⊤̇ γ = refl
  sat⊥-irrel Formula.⊥̇ γ = refl
  sat⊥-irrel (∃̇ φ)   γ = cong (⋁ S) (funExt (λ x → sat⊥-irrel φ (x ∷ γ)))
  sat⊥-irrel (∀̇ φ)   γ = cong (⋀ S) (funExt (λ x → sat⊥-irrel φ (x ∷ γ)))
  sat⊥-irrel (∀̇∈ t φ) γ = cong (⋀ S) (funExt (λ x →
    cong₂ _⇒_ (cong (x ∈ˢ_) (tm⊥-irrel t γ)) (sat⊥-irrel φ (x ∷ γ))))
  sat⊥-irrel (∃̇∈ t φ) γ = cong (⋁ S) (funExt (λ x →
    cong₂ _⊓_ (cong (x ∈ˢ_) (tm⊥-irrel t γ)) (sat⊥-irrel φ (x ∷ γ))))

module At₀ = SemA.At (⊥* {ℓ-zero}) Empty.rec*

-- the parameter chapter's transfer, instantiated at the carrier's syntax
⊨-place₀ : (φ : Formula ⟪ A ⟫ 1) (θ : Fin (countFo φ) → Fin 4)
         → (γ : S ^ 1) (σ : S ^ 3)
         → ((j : Fin (countFo φ)) → lookup (θ j) (γ ++ σ)
              ≡ ⟪ A ⟫↪ (lookup j (constantsFo φ)))
         → (γ ⊨ φ) ≡ ((γ ++ σ) At₀.⊨ placeFo {ℓz = ℓ-zero} φ θ)
⊨-place₀ = FOL.Manipulation.Parameters.⊨-place
  (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ {ℓz = ℓ-zero} {ℓc = ℓ} {K = ⟪ A ⟫} (⟪ A ⟫↪)

-- the relabelling kit's embedding, at the same instantiation
embed-⊨₀ : (ψ : Formula (⊥* {ℓ-zero}) 4) (γ : S ^ 4)
         → (γ ⊨ embed ψ) ≡ (γ At∅₂.⊨ ψ)
embed-⊨₀ = FOL.Manipulation.Relabelling.embed-⊨
  (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ {ℓe = ℓ-zero} {ℓc = ℓ} {K = ⟪ A ⟫} (⟪ A ⟫↪)

private
  i1 : {n : ℕ} → Fin (suc (suc n))
  i1 = suc zero
  i2 : {n : ℕ} → Fin (suc (suc (suc n)))
  i2 = suc i1
  i3 : {n : ℕ} → Fin (suc (suc (suc (suc n))))
  i3 = suc i2
```

<!--en-->
## The argument fibres
<!--zh-->
## 实参纤维
<!--/-->

<!--en-->
Each operation's graph is stated at a pair of argument values `u, v` of the
carrier. The constant-form description speaks through their small-index
fibres, so every per-operation module starts by naming them once: the fibre
index `m` and the path back to the value.
<!--zh-->
每个运算的图在载体的一对实参值 `u, v` 处陈述。常量形描述经由它们的小索引纤维说话，故每个逐运算模块先一次点名它们：纤维索引 `m` 与回到该值的道路。
<!--/-->

```agda
module Args (u v : S) (uu : ⟨ u ∈ˢ A ⟩) (vu : ⟨ v ∈ˢ A ⟩) where
  mᵤ : ⟪ A ⟫
  mᵤ = ∈-asFiber {a = u} {b = A} uu .fst
  qᵤ : ⟪ A ⟫↪ mᵤ ≡ u
  qᵤ = ∈-asFiber {a = u} {b = A} uu .snd
  mᵥ : ⟪ A ⟫
  mᵥ = ∈-asFiber {a = v} {b = A} vu .fst
  qᵥ : ⟪ A ⟫↪ mᵥ ≡ v
  qᵥ = ∈-asFiber {a = v} {b = A} vu .snd
```

<!--en-->
## The constants-to-variables face
<!--zh-->
## 常量到变量的那一面
<!--/-->

<!--en-->
The variable shape of an operation is its constant-form description formula
with the argument constants abstracted to the `u` and `v` slots of a
four-variable context, the candidate sitting at index zero. The adequacy of
the abstraction is the parameter chapter's `⊨-place`, read through the
relabelling kit and the empty-domain irrelevance: satisfaction of the shape at
`(z, x, u, v)` is satisfaction of the description at the constant fibres,
which is exactly what the description's own two directions speak.
<!--zh-->
一个运算的变量形，就是它的常量形描述公式把实参常量抽象到四变量语境的 `u`、`v`槽位，候选坐在序号零。抽象的充分性是参数章的 `⊨-place`，经重标工具组与空域无关性读出：形状在 `(z, x, u, v)` 处的满足，就是描述在常量纤维处的满足，而这正是描述自身两个方向所说的话。
<!--/-->

```agda
module VarSat (φ : Formula ⟪ A ⟫ 1) (θ : Fin (countFo φ) → Fin 4)
  (mᵤ mᵥ : ⟪ A ⟫)
  (hyp : (z x : S) (j : Fin (countFo φ))
       → lookup (θ j) (z ∷ x ∷ ⟪ A ⟫↪ mᵤ ∷ ⟪ A ⟫↪ mᵥ ∷ [])
         ≡ ⟪ A ⟫↪ (lookup j (constantsFo φ)))
  where
  ψ : Formula (⊥* {ℓ-zero}) 4
  ψ = placeFo {ℓz = ℓ-zero} φ θ

  body : Formula ⟪ A ⟫ 4
  body = embed ψ

  satPath : (z x : S)
          → ((z ∷ x ∷ ⟪ A ⟫↪ mᵤ ∷ ⟪ A ⟫↪ mᵥ ∷ []) ⊨ body) ≡ ((z ∷ []) ⊨ φ)
  satPath z x = embed-⊨₀ ψ env ∙ sym (sat⊥-irrel ψ env)
             ∙ sym (⊨-place₀ φ θ (z ∷ []) (x ∷ ⟪ A ⟫↪ mᵤ ∷ ⟪ A ⟫↪ mᵥ ∷ []) (hyp z x))
    where
    env : S ^ 4
    env = z ∷ x ∷ ⟪ A ⟫↪ mᵤ ∷ ⟪ A ⟫↪ mᵥ ∷ []

  var-out : (z x : S) → ⟨ (z ∷ x ∷ ⟪ A ⟫↪ mᵤ ∷ ⟪ A ⟫↪ mᵥ ∷ []) ⊨ body ⟩ → ⟨ (z ∷ []) ⊨ φ ⟩
  var-out z x h = subst ⟨_⟩ (satPath z x) h

  var-in : (z x : S) → ⟨ (z ∷ []) ⊨ φ ⟩ → ⟨ (z ∷ x ∷ ⟪ A ⟫↪ mᵤ ∷ ⟪ A ⟫↪ mᵥ ∷ []) ⊨ body ⟩
  var-in z x h = subst ⟨_⟩ (sym (satPath z x)) h
```

<!--en-->
## The fibre environment
<!--zh-->
## 纤维环境
<!--/-->

<!--en-->
The graph's adequacy is stated at the argument values `u, v` themselves,
while the transfer above lives at the fibres; the two are connected by the
paths back to the values, transported through the satisfaction.
<!--zh-->
图的适足在实参值 `u, v` 自身处陈述，而上文的迁移住在纤维处；两者经回到值的道路、穿过满足关系相连。
<!--/-->

```agda
module FibEnv (body : Formula ⟪ A ⟫ 4) (u v : S)
  (uu : ⟨ u ∈ˢ A ⟩) (vu : ⟨ v ∈ˢ A ⟩) where
  module AR = Args u v uu vu

  toFib : (z x : S) → ⟨ (z ∷ x ∷ u ∷ v ∷ []) ⊨ body ⟩
                   → ⟨ (z ∷ x ∷ ⟪ A ⟫↪ AR.mᵤ ∷ ⟪ A ⟫↪ AR.mᵥ ∷ []) ⊨ body ⟩
  toFib z x h = subst (λ w → ⟨ (z ∷ x ∷ w ∷ ⟪ A ⟫↪ AR.mᵥ ∷ []) ⊨ body ⟩) (sym AR.qᵤ)
    (subst (λ w → ⟨ (z ∷ x ∷ u ∷ w ∷ []) ⊨ body ⟩) (sym AR.qᵥ) h)

  fromFib : (z x : S) → ⟨ (z ∷ x ∷ ⟪ A ⟫↪ AR.mᵤ ∷ ⟪ A ⟫↪ AR.mᵥ ∷ []) ⊨ body ⟩
                      → ⟨ (z ∷ x ∷ u ∷ v ∷ []) ⊨ body ⟩
  fromFib z x h = subst (λ w → ⟨ (z ∷ x ∷ w ∷ v ∷ []) ⊨ body ⟩) AR.qᵤ
    (subst (λ w → ⟨ (z ∷ x ∷ ⟪ A ⟫↪ AR.mᵤ ∷ w ∷ []) ⊨ body ⟩) AR.qᵥ h)
```

<!--en-->
## The graph frame
<!--zh-->
## 图框架
<!--/-->

<!--en-->
The graph of an operation is the extensional closure of its variable shape:
every member of `x` satisfies the shape, and every set satisfying the shape is
a member of `x`. The frame is generic in the set-valued operation and in the
shape's two adequacy directions, and proves the two-way characterization of
`x = Op u v` once. The second conjunct is an unbounded universal, so the
graph is the honest Π₁ reading of set equality, not a Δ₀ formula; the
sequence-witness formula's uniform Σ₁ face pays that price at its own level.
<!--zh-->
一个运算的图是它的变量形的外延闭包：`x` 的每个成员都满足形状，每个满足形状的集合都是 `x` 的成员。框架对集合值运算与形状的两个适足方向泛型，一次证出 `x = Op u v`的双向刻画。第二合取项是一条无界全称，故图是集合等词的诚实 Π₁ 读法，而非 Δ₀ 公式；序列见证公式的均匀 Σ₁ 面孔在自己的层级上付这笔账。
<!--/-->

```agda
module GraphFrame (Op : S → S → S) (body : Formula ⟪ A ⟫ 4) (u v : S)
  (body-out : (z x : S) → ⟨ (z ∷ x ∷ u ∷ v ∷ []) ⊨ body ⟩ → ⟨ z ∈ˢ Op u v ⟩)
  (body-in : (z x : S) → ⟨ z ∈ˢ Op u v ⟩ → ⟨ (z ∷ x ∷ u ∷ v ∷ []) ⊨ body ⟩)
  where
  graph : Formula ⟪ A ⟫ 3
  graph = (∀̇∈ (var zero) body) ∧̇ (∀̇ (body ⇒̇ (var zero ∈̇ var i1)))

  graph-out : (x : S) → ⟨ (x ∷ u ∷ v ∷ []) ⊨ graph ⟩ → x ≡ Op u v
  graph-out x h = extensionality x (Op u v) (sub , sup)
    where
    sub : (z : S) → ⟨ z ∈ₛ x ⟩ → ⟨ z ∈ₛ Op u v ⟩
    sub z hz = ∈∈ₛ {a = z} {b = Op u v} .fst
      (body-out z x (h .fst z (∈∈ₛ {a = z} {b = x} .snd hz)))
    sup : (z : S) → ⟨ z ∈ₛ Op u v ⟩ → ⟨ z ∈ₛ x ⟩
    sup z hz = ∈∈ₛ {a = z} {b = x} .fst
      (h .snd z (body-in z x (∈∈ₛ {a = z} {b = Op u v} .snd hz)))

  graph-in : (x : S) → x ≡ Op u v → ⟨ (x ∷ u ∷ v ∷ []) ⊨ graph ⟩
  graph-in x e = (∀₁ , ∀₂)
    where
    ∀₁ : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ (z ∷ x ∷ u ∷ v ∷ []) ⊨ body ⟩
    ∀₁ z hz = body-in z x (subst (λ t → ⟨ z ∈ˢ t ⟩) e hz)
    ∀₂ : (z : S) → ⟨ (z ∷ x ∷ u ∷ v ∷ []) ⊨ body ⟩ → ⟨ z ∈ˢ x ⟩
    ∀₂ z hb = subst (λ t → ⟨ z ∈ˢ t ⟩) (sym e) (body-out z x hb)
```

<!--en-->
## F0, the unordered pair
<!--zh-->
## F0，无序对
<!--/-->

<!--en-->
F0 is the frame's first instantiation and the representative operation of the
batch: the description is transparent, its two constants are exactly the two
arguments, and the shape abstracts to the disjunction of the two equalities.
The module names the graph formula and its two adequacy directions.
<!--zh-->
F0 是框架的第一个实例，也是本批的代表运算：描述透明，两个常量恰是两个实参，形状抽象为两条等词之析取。模块点名图公式与其两个适足方向。
<!--/-->

```agda
module F0Graph (u v : S) (uu : ⟨ u ∈ˢ A ⟩) (vu : ⟨ v ∈ˢ A ⟩)
  (Atr : Transitive 𝒮ᵥ (λ x → x ∈ˢ A)) where
  module AR = Args u v uu vu
  module D = F0Desc A u v uu vu Atr

  θ₀ : Fin (countFo D.Φ₀) → Fin 4
  θ₀ zero = i2
  θ₀ (suc zero) = i3

  hyp₀ : (z x : S) (j : Fin (countFo D.Φ₀))
       → lookup (θ₀ j) (z ∷ x ∷ ⟪ A ⟫↪ AR.mᵤ ∷ ⟪ A ⟫↪ AR.mᵥ ∷ [])
         ≡ ⟪ A ⟫↪ (lookup j (constantsFo D.Φ₀))
  hyp₀ z x zero = refl
  hyp₀ z x (suc zero) = refl

  module VS = VarSat D.Φ₀ θ₀ AR.mᵤ AR.mᵥ hyp₀
  module FE = FibEnv VS.body u v uu vu

  body₀ : Formula ⟪ A ⟫ 4
  body₀ = VS.body

  body-out₀ : (z x : S) → ⟨ (z ∷ x ∷ u ∷ v ∷ []) ⊨ body₀ ⟩ → ⟨ z ∈ˢ Fof f0 u v ⟩
  body-out₀ z x h = subst (λ t → ⟨ z ∈ˢ t ⟩) (sym (Fof-f0 u v))
    (D.F0-desc-out z (VS.var-out z x (FE.toFib z x h)))

  body-in₀ : (z x : S) → ⟨ z ∈ˢ Fof f0 u v ⟩ → ⟨ (z ∷ x ∷ u ∷ v ∷ []) ⊨ body₀ ⟩
  body-in₀ z x h = FE.fromFib z x
    (VS.var-in z x (D.F0-desc-in z (subst (λ t → ⟨ z ∈ˢ t ⟩) (Fof-f0 u v) h)))

  module GF = GraphFrame (Fof f0) body₀ u v body-out₀ body-in₀

  graph₀ : Formula ⟪ A ⟫ 3
  graph₀ = GF.graph

  F0-graph-out : (x : S) → ⟨ (x ∷ u ∷ v ∷ []) ⊨ graph₀ ⟩ → x ≡ Fof f0 u v
  F0-graph-out = GF.graph-out

  F0-graph-in : (x : S) → x ≡ Fof f0 u v → ⟨ (x ∷ u ∷ v ∷ []) ⊨ graph₀ ⟩
  F0-graph-in = GF.graph-in
```

<!--en-->
## F1, set difference
<!--zh-->
## F1，差
<!--/-->

<!--en-->
F1 differs from F0 in one structural point only: the second conjunct is a
negation, and the placement and the transfer are unchanged.
<!--zh-->
F1 与 F0 只差一处结构：第二合取项是否定，安置与迁移原样。
<!--/-->

```agda
module F1Graph (u v : S) (uu : ⟨ u ∈ˢ A ⟩) (vu : ⟨ v ∈ˢ A ⟩)
  (Atr : Transitive 𝒮ᵥ (λ x → x ∈ˢ A)) where
  module AR = Args u v uu vu
  module D = F1Desc A u v uu vu Atr

  θ₁ : Fin (countFo D.Φ₁) → Fin 4
  θ₁ zero = i2
  θ₁ (suc zero) = i3

  hyp₁ : (z x : S) (j : Fin (countFo D.Φ₁))
       → lookup (θ₁ j) (z ∷ x ∷ ⟪ A ⟫↪ AR.mᵤ ∷ ⟪ A ⟫↪ AR.mᵥ ∷ [])
         ≡ ⟪ A ⟫↪ (lookup j (constantsFo D.Φ₁))
  hyp₁ z x zero = refl
  hyp₁ z x (suc zero) = refl

  module VS = VarSat D.Φ₁ θ₁ AR.mᵤ AR.mᵥ hyp₁
  module FE = FibEnv VS.body u v uu vu

  body₁ : Formula ⟪ A ⟫ 4
  body₁ = VS.body

  body-out₁ : (z x : S) → ⟨ (z ∷ x ∷ u ∷ v ∷ []) ⊨ body₁ ⟩ → ⟨ z ∈ˢ Fof f1 u v ⟩
  body-out₁ z x h = subst (λ t → ⟨ z ∈ˢ t ⟩) (sym (Fof-f1 u v))
    (D.F1-desc-out z (VS.var-out z x (FE.toFib z x h)))

  body-in₁ : (z x : S) → ⟨ z ∈ˢ Fof f1 u v ⟩ → ⟨ (z ∷ x ∷ u ∷ v ∷ []) ⊨ body₁ ⟩
  body-in₁ z x h = FE.fromFib z x
    (VS.var-in z x (D.F1-desc-in z (subst (λ t → ⟨ z ∈ˢ t ⟩) (Fof-f1 u v) h)))

  module GF = GraphFrame (Fof f1) body₁ u v body-out₁ body-in₁

  graph₁ : Formula ⟪ A ⟫ 3
  graph₁ = GF.graph

  F1-graph-out : (x : S) → ⟨ (x ∷ u ∷ v ∷ []) ⊨ graph₁ ⟩ → x ≡ Fof f1 u v
  F1-graph-out = GF.graph-out

  F1-graph-in : (x : S) → x ≡ Fof f1 u v → ⟨ (x ∷ u ∷ v ∷ []) ⊨ graph₁ ⟩
  F1-graph-in = GF.graph-in
```

<!--en-->
## F5, the union
<!--zh-->
## F5，并
<!--/-->

<!--en-->
The union's value ignores its second argument, and the description formula
mentions only the first; the placement has one case, mapping that occurrence
to the `u` slot, and the shape is the single bounded existential.
<!--zh-->
并的值忽略第二实参，描述公式只提及第一个；安置只有一个情形，把那次出现映射到 `u`槽，形状是那条有界存在。
<!--/-->

```agda
module F5Graph (u v : S) (uu : ⟨ u ∈ˢ A ⟩) (vu : ⟨ v ∈ˢ A ⟩)
  (Atr : Transitive 𝒮ᵥ (λ x → x ∈ˢ A)) where
  module AR = Args u v uu vu
  module D = F5Desc A u v uu Atr

  θ₅ : Fin (countFo D.Φ₅) → Fin 4
  θ₅ zero = i2

  hyp₅ : (z x : S) (j : Fin (countFo D.Φ₅))
       → lookup (θ₅ j) (z ∷ x ∷ ⟪ A ⟫↪ AR.mᵤ ∷ ⟪ A ⟫↪ AR.mᵥ ∷ [])
         ≡ ⟪ A ⟫↪ (lookup j (constantsFo D.Φ₅))
  hyp₅ z x zero = refl

  module VS = VarSat D.Φ₅ θ₅ AR.mᵤ AR.mᵥ hyp₅
  module FE = FibEnv VS.body u v uu vu

  body₅ : Formula ⟪ A ⟫ 4
  body₅ = VS.body

  body-out₅ : (z x : S) → ⟨ (z ∷ x ∷ u ∷ v ∷ []) ⊨ body₅ ⟩ → ⟨ z ∈ˢ Fof f5 u v ⟩
  body-out₅ z x h = subst (λ t → ⟨ z ∈ˢ t ⟩) (sym (Fof-f5 u v))
    (D.F5-desc-out z (VS.var-out z x (FE.toFib z x h)))

  body-in₅ : (z x : S) → ⟨ z ∈ˢ Fof f5 u v ⟩ → ⟨ (z ∷ x ∷ u ∷ v ∷ []) ⊨ body₅ ⟩
  body-in₅ z x h = FE.fromFib z x
    (VS.var-in z x (D.F5-desc-in z (subst (λ t → ⟨ z ∈ˢ t ⟩) (Fof-f5 u v) h)))

  module GF = GraphFrame (Fof f5) body₅ u v body-out₅ body-in₅

  graph₅ : Formula ⟪ A ⟫ 3
  graph₅ = GF.graph

  F5-graph-out : (x : S) → ⟨ (x ∷ u ∷ v ∷ []) ⊨ graph₅ ⟩ → x ≡ Fof f5 u v
  F5-graph-out = GF.graph-out

  F5-graph-in : (x : S) → x ≡ Fof f5 u v → ⟨ (x ∷ u ∷ v ∷ []) ⊨ graph₅ ⟩
  F5-graph-in = GF.graph-in
```

<!--en-->
## F2, the product
<!--zh-->
## F2，积
<!--/-->

<!--en-->
The product's specification is sealed, and the description chapter's reverse
direction is closed in the switch chapter's hops; the frame consumes both
directions exactly as it consumes the transparent ones. This is the sealed
specimen of the batch.
<!--zh-->
积的规格是封存的，描述章的反向在切换章的反向跳处封口；框架消费两个方向与消费透明方向完全一样。这是本批的封存标本。
<!--/-->

```agda
module F2Graph (u v : S) (uu : ⟨ u ∈ˢ A ⟩) (vu : ⟨ v ∈ˢ A ⟩)
  (Atr : Transitive 𝒮ᵥ (λ x → x ∈ˢ A)) where
  module AR = Args u v uu vu
  module D = F2Desc A u v uu vu
  module H = Hops A u v uu vu Atr

  θ₂ : Fin (countFo D.Φ₂) → Fin 4
  θ₂ zero = i2
  θ₂ (suc zero) = i3

  hyp₂ : (z x : S) (j : Fin (countFo D.Φ₂))
       → lookup (θ₂ j) (z ∷ x ∷ ⟪ A ⟫↪ AR.mᵤ ∷ ⟪ A ⟫↪ AR.mᵥ ∷ [])
         ≡ ⟪ A ⟫↪ (lookup j (constantsFo D.Φ₂))
  hyp₂ z x zero = refl
  hyp₂ z x (suc zero) = refl

  module VS = VarSat D.Φ₂ θ₂ AR.mᵤ AR.mᵥ hyp₂
  module FE = FibEnv VS.body u v uu vu

  body₂ : Formula ⟪ A ⟫ 4
  body₂ = VS.body

  body-out₂ : (z x : S) → ⟨ (z ∷ x ∷ u ∷ v ∷ []) ⊨ body₂ ⟩ → ⟨ z ∈ˢ Fof f2 u v ⟩
  body-out₂ z x h = subst (λ t → ⟨ z ∈ˢ t ⟩) (sym (Fof-f2 u v))
    (H.F2-desc-out z (VS.var-out z x (FE.toFib z x h)))

  body-in₂ : (z x : S) → ⟨ z ∈ˢ Fof f2 u v ⟩ → ⟨ (z ∷ x ∷ u ∷ v ∷ []) ⊨ body₂ ⟩
  body-in₂ z x h = FE.fromFib z x
    (VS.var-in z x (D.F2-desc-in z (subst (λ t → ⟨ z ∈ˢ t ⟩) (Fof-f2 u v) h)))

  module GF = GraphFrame (Fof f2) body₂ u v body-out₂ body-in₂

  graph₂ : Formula ⟪ A ⟫ 3
  graph₂ = GF.graph

  F2-graph-out : (x : S) → ⟨ (x ∷ u ∷ v ∷ []) ⊨ graph₂ ⟩ → x ≡ Fof f2 u v
  F2-graph-out = GF.graph-out

  F2-graph-in : (x : S) → x ≡ Fof f2 u v → ⟨ (x ∷ u ∷ v ∷ []) ⊨ graph₂ ⟩
  F2-graph-in = GF.graph-in
```

<!--en-->
## F10, one image set
<!--zh-->
## F10，单个像集
<!--/-->

<!--en-->
The slice operation is the image half's first instance: the description's two
constants are the two arguments again, and the frame closes it with the same
two-line instantiation as F0 and F1.
<!--zh-->
切片运算是像半的第一个实例：描述的两个常量再次就是两个实参，框架以与 F0、F1 相同的两行实例化收束它。
<!--/-->

```agda
module F10Graph (u v : S) (uu : ⟨ u ∈ˢ A ⟩) (vu : ⟨ v ∈ˢ A ⟩)
  (Atr : Transitive 𝒮ᵥ (λ x → x ∈ˢ A)) where
  module AR = Args u v uu vu
  module D = F10Desc A u v uu vu Atr

  θ₁₀ : Fin (countFo D.Φ₁₀) → Fin 4
  θ₁₀ zero = i2
  θ₁₀ (suc zero) = i3

  hyp₁₀ : (z x : S) (j : Fin (countFo D.Φ₁₀))
        → lookup (θ₁₀ j) (z ∷ x ∷ ⟪ A ⟫↪ AR.mᵤ ∷ ⟪ A ⟫↪ AR.mᵥ ∷ [])
          ≡ ⟪ A ⟫↪ (lookup j (constantsFo D.Φ₁₀))
  hyp₁₀ z x zero = refl
  hyp₁₀ z x (suc zero) = refl

  module VS = VarSat D.Φ₁₀ θ₁₀ AR.mᵤ AR.mᵥ hyp₁₀
  module FE = FibEnv VS.body u v uu vu

  body₁₀ : Formula ⟪ A ⟫ 4
  body₁₀ = VS.body

  body-out₁₀ : (z x : S) → ⟨ (z ∷ x ∷ u ∷ v ∷ []) ⊨ body₁₀ ⟩ → ⟨ z ∈ˢ Fof f10 u v ⟩
  body-out₁₀ z x h = subst (λ t → ⟨ z ∈ˢ t ⟩) (sym (Fof-f10 u v))
    (D.F10-desc-out z (VS.var-out z x (FE.toFib z x h)))

  body-in₁₀ : (z x : S) → ⟨ z ∈ˢ Fof f10 u v ⟩ → ⟨ (z ∷ x ∷ u ∷ v ∷ []) ⊨ body₁₀ ⟩
  body-in₁₀ z x h = FE.fromFib z x
    (VS.var-in z x (D.F10-desc-in z (subst (λ t → ⟨ z ∈ˢ t ⟩) (Fof-f10 u v) h)))

  module GF = GraphFrame (Fof f10) body₁₀ u v body-out₁₀ body-in₁₀

  graph₁₀ : Formula ⟪ A ⟫ 3
  graph₁₀ = GF.graph

  F10-graph-out : (x : S) → ⟨ (x ∷ u ∷ v ∷ []) ⊨ graph₁₀ ⟩ → x ≡ Fof f10 u v
  F10-graph-out = GF.graph-out

  F10-graph-in : (x : S) → x ≡ Fof f10 u v → ⟨ (x ∷ u ∷ v ∷ []) ⊨ graph₁₀ ⟩
  F10-graph-in = GF.graph-in
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The frame is in place: a variable shape abstracted from the constant-form
description, an extensional graph closure, and the two adequacy directions
assembled from the description's own directions and the parameter chapter's
transfer. The representative operation F0 instantiates it green, and F1, F5,
F2 and F10 follow with unchanged instantiations, covering the transparent,
single-argument, sealed-specification and image-half shapes. The batch report
records the remaining operations and the obstruction the D-10 check found:
the four tuple operations F11 to F14, whose total definitions route through
the left and right projections.
<!--zh-->
框架就位：从常量形描述抽象出的变量形状、外延图闭包，以及由描述自身方向与参数章迁移装配的两个适足方向。代表运算 F0 绿色实例化它，F1、F5、F2 与 F10 以原样的实例化跟进，覆盖透明、单实参、封存规格与像半诸形。批次报告记录其余运算与 D-10 检查找到的受阻：四个三元组运算 F11 至 F14，其全函数定义取道左、右投影。
<!--/-->

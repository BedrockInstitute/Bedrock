# The S-hierarchy, abstractly

<!--en-->
The rud route builds its universe from a tower `S₀ = ∅`, `S_{α+1} = step(S_α)`,
unions at limits, over a one-step operator that the operations chapter will
instantiate with the sixteen functions. This chapter proves the engine
abstractly: the step enters as a module parameter together with the four
properties the proofs actually spend, and the ordinal-indexed family, its
cumulativity and transitivity, the three derived case equations, and the
limit-indexed subfamily `J` are all built on nothing else. Nothing concrete
unfolds anywhere, because nothing concrete is in scope; that is the point.
Every property assumed here is an obligation the instantiation batch must
discharge, so the telescope stays exactly as small as the proofs force it to
be.
<!--zh-->
rud 路线从一座塔 `S₀ = ∅`、`S_{α+1} = step(S_α)`、极限处取并出发建造宇宙，其上的一步算子将在运算章由十六个函数实例化。本章抽象地证明引擎：step 连同证明真正花费的四条性质一起作为模块参数进入，而以序数为索引的族、它的累积性与传递性、三条派生的分情形方程，以及限制在极限索引上的子族 `J`，全部只建在这套东西之上。此处不展开任何具体对象，因为具体对象本就不在作用域内，这正是要点。这里假设的每条性质都是实例化批次必须清偿的义务，故望远镜被压得与证明所需恰好一样小。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; sett )

module L.Rud.Hierarchy
  {ℓ : Level}
  (lem : LEM (ℓ-suc ℓ))
  (step : V ℓ → V ℓ)
  (step-⊆ : (u x : V ℓ) → ⟨ x ∈ u ⟩ → ⟨ x ∈ step u ⟩)
  (step-∈ : (u : V ℓ) → ⟨ u ∈ step u ⟩)
  (step-mono : {u v : V ℓ} → ((x : V ℓ) → ⟨ x ∈ u ⟩ → ⟨ x ∈ v ⟩)
            → ((x : V ℓ) → ⟨ x ∈ step u ⟩ → ⟨ x ∈ step v ⟩))
  (step-trans : (u : V ℓ)
              → ({x y : V ℓ} → ⟨ y ∈ x ⟩ → ⟨ x ∈ u ⟩ → ⟨ y ∈ u ⟩)
              → ({x y : V ℓ} → ⟨ y ∈ x ⟩ → ⟨ x ∈ step u ⟩ → ⟨ y ∈ step u ⟩))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ}
  using ( 𝒮ᵥ; extensionalV; ∈-induction; ∈-induction-compute; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim; self∈sucV )
open import L.Constructible {ℓ}
  using ( isTransV; ∅-trans; ⋃-trans; setUnion-trans; IsOrd )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri; Tri )
open import L.Rud.OrdArith {ℓ} lem
  using ( isLimit; isLimit-ord; isLimit-not-succ; limit-mem-ord )

open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ∈-asFiber; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⋃_; union-ax; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## Inclusion
<!--zh-->
## 包含
<!--/-->

<!--en-->
Inclusion is written pointwise, and mutual inclusion is equality by the
hierarchy's extensionality, `_⊆_` reads "is a subset of". This is the only
equality engine the derived equations use, and it costs nothing beyond the two
membership functions it is handed.
<!--zh-->
包含逐点写出，互相包含按层级的外延性即相等，`_⊆_` 读作「是……的子集」。这是派生方程唯一用到的相等引擎，除接过两条成员函数外不费分文。
<!--/-->

```agda
_⊆_ : S → S → Type (ℓ-suc ℓ)
u ⊆ v = (x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩

ext-⊆ : {u v : S} → u ⊆ v → v ⊆ u → u ≡ v
ext-⊆ {u} {v} sub sup = extensionalV (λ x → ⇔toPath (sub x) (sup x))
```

<!--en-->
## The closure principles
<!--zh-->
## 闭包原则
<!--/-->

<!--en-->
As in the constructible tower, the levels admit an inductive predicate naming
the closure principles: the empty set is a level, levels close under the step,
and unions of levels are levels, whether the union is taken over the members
of a set or over a small family. Every level is transitive: each case is the
corresponding closure lemma for transitive sets, and the step case is exactly
the abstract parameter `step-trans`{.Agda}. The binary-union form of the
constructible tower is left out, since no level of this development is ever
formed as a binary union, and a constructor nothing uses would only add a
clause to every induction on the predicate.
<!--zh-->
与可构造塔一样，诸层容许一条归纳谓词点名闭包原则：空集是层，层对 step 封闭，层的并仍是层，无论是沿某集合的成员取并，还是沿小族取并。每个层都传递：每种情形对应传递集的相应闭包引理，step 情形恰是抽象参数 `step-trans`{.Agda}。可构造塔的二元并形式此处略去，因为本开发的任何层都不会以二元并成形，而一个无人使用的构造子只会给谓词上的每次归纳多添一条子句。
<!--/-->

```agda
data isLevel : S → Type (ℓ-suc ℓ) where
  ∅-level        : isLevel ∅
  step-level     : {A : S} → isLevel A → isLevel (step A)
  union-level    : (x : S) → ((y : S) → ⟨ y ∈ˢ x ⟩ → isLevel y) → isLevel (⋃ x)
  setUnion-level : (X : Type ℓ) (f : X → S)
                 → ((x : X) → isLevel (f x)) → isLevel (⋃ (sett X f))

level-trans : {A : S} → isLevel A → isTransV A
level-trans ∅-level = ∅-trans
level-trans (step-level {A} lA) = step-trans A (level-trans lA)
level-trans (union-level x mem) = ⋃-trans x (λ y y∈x → level-trans (mem y y∈x))
level-trans (setUnion-level X f hf) = setUnion-trans X f (λ x → level-trans (hf x))
```

<!--en-->
## The tower
<!--zh-->
## 塔
<!--/-->

<!--en-->
The family itself is one equation over the tower's membership recursion, not a
case analysis. `Sset`{.Agda} is the code's spelling of the family the prose
writes as `S`, and `S α` reads "the `α`-th level": it is the union, over the
members `β` of `α`, of `step` applied to the recursive value at `β`. On the
von Neumann ordinals this is exactly `S₀ = ∅`, `S_{α+1} = step(S_α)`, unions
at limits, and the single equation is the clause that proves all three at once.
The tower is sealed `opaque`{.Agda} with `Sset-compute`{.Agda} as its official
unfolding, so the recursion machinery is not dragged into later conversions.
<!--zh-->
族本身是对塔的成员递归的一条方程，而非分情形。`Sset`{.Agda} 是代码里对该族的拼写，行文写作 `S`，而 `S α` 读作「第 `α` 层」：它是沿 `α` 的成员 `β`、对 `β` 处递归值施以 step 所得的并。在冯·诺伊曼序数上这正是 `S₀ = ∅`、`S_{α+1} = step(S_α)`、极限取并，而这一条方程就是同时证出三种情形的那个子句。塔以 `opaque`{.Agda} 封印，`Sset-compute`{.Agda} 是它的官方展开，递归机器不会被拖进日后的转换。
<!--/-->

```agda
Sset-step : (α : S) → (∀ β → β ∈ᵗ α → S) → S
Sset-step α rec = ⋃ (sett ⟪ α ⟫ (λ m → step (rec (⟪ α ⟫↪ m) (mem m))))
  where
  mem : (m : ⟪ α ⟫) → ⟪ α ⟫↪ m ∈ᵗ α
  mem m = ∈∈ₛ {a = ⟪ α ⟫↪ m} {b = α} .snd (∈ₛ⟪ α ⟫↪ m)

opaque
  Sset : S → S
  Sset = ∈-induction Sset-step

Sset-stepFam : (α : S) → ⟪ α ⟫ → S
Sset-stepFam α m = step (Sset (⟪ α ⟫↪ m))

opaque
  unfolding Sset
  Sset-compute : (α : S) → Sset α ≡ ⋃ (sett ⟪ α ⟫ (Sset-stepFam α))
  Sset-compute = ∈-induction-compute Sset-step
```

<!--en-->
Every value of the tower is a level, by the same induction as the constructible
tower: unfold once with `Sset-compute`{.Agda}, use the hypothesis at each
member, raise by `step-level`{.Agda}, and close the family union. Transitivity
of every level follows immediately, and at a limit index this is literally a
union of transitive sets.
<!--zh-->
塔的每个值都是层，归纳与可构造塔相同：用 `Sset-compute`{.Agda} 展开一次，在每个成员处用归纳假设，经 `step-level`{.Agda} 抬升，再把族并收拢。每个层传递随即得出，而在极限索引处这正是对传递集取并。
<!--/-->

```agda
Sset-level : (α : S) → isLevel (Sset α)
Sset-level = ∈-induction lvlStep
  where
  lvlStep : (α : S) → (∀ β → β ∈ᵗ α → isLevel (Sset β)) → isLevel (Sset α)
  lvlStep α IH = subst isLevel (sym (Sset-compute α))
    (setUnion-level ⟪ α ⟫ (Sset-stepFam α)
      (λ m → step-level (IH (⟪ α ⟫↪ m) (mem m))))
    where
    mem : (m : ⟪ α ⟫) → ⟪ α ⟫↪ m ∈ᵗ α
    mem m = ∈∈ₛ {a = ⟪ α ⟫↪ m} {b = α} .snd (∈ₛ⟪ α ⟫↪ m)

Sset-trans : (α : S) → isTransV (Sset α)
Sset-trans α = level-trans (Sset-level α)
```

<!--en-->
## Membership and cumulativity
<!--zh-->
## 成员与累积性
<!--/-->

<!--en-->
Belonging to a level reads the union in both directions, exactly as in the
constructible tower: going in names a member `δ` of the index together with a
membership in `step (Sset δ)`, and coming out names the fibre. The two
directions are named lemmas because every later closure argument reaches for
one of them.
<!--zh-->
属于一个层把那个并两头各读一遍，与可构造塔完全一致：进去点名索引的一个成员 `δ`，连同一条 `step (Sset δ)` 中的成员资格，出来点名纤维。两个方向各成命名引理，因为此后每个闭包论证都要取其中之一。
<!--/-->

```agda
Sset-in : (α δ x : S) → ⟨ δ ∈ˢ α ⟩ → ⟨ x ∈ˢ step (Sset δ) ⟩ → ⟨ x ∈ˢ Sset α ⟩
Sset-in α δ x δ∈α x∈stepSδ =
  subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (Sset-compute α))
    (∈∈ₛ {a = x} {b = ⋃ (sett ⟪ α ⟫ (Sset-stepFam α))} .snd
      (union-ax (sett ⟪ α ⟫ (Sset-stepFam α)) x .snd
        ∣ step (Sset δ) , (stepSδ∈ₛsett , x∈ₛstepSδ) ∣₁))
  where
  fib = ∈-asFiber {a = δ} {b = α} δ∈α
  m = fib .fst
  p : ⟪ α ⟫↪ m ≡ δ
  p = fib .snd
  stepSδ∈ₛsett : ⟨ step (Sset δ) ∈ₛ sett ⟪ α ⟫ (Sset-stepFam α) ⟩
  stepSδ∈ₛsett = ∈∈ₛ {a = step (Sset δ)} {b = sett ⟪ α ⟫ (Sset-stepFam α)} .fst
    ∣ m , cong (λ b → step (Sset b)) p ∣₁
  x∈ₛstepSδ : ⟨ x ∈ₛ step (Sset δ) ⟩
  x∈ₛstepSδ = ∈∈ₛ {a = x} {b = step (Sset δ)} .fst x∈stepSδ

Sset-out : (α x : S) → ⟨ x ∈ˢ Sset α ⟩
         → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ α ⟩ × ⟨ x ∈ˢ step (Sset δ) ⟩) ∥₁
Sset-out α x x∈Sα = PT.rec squash₁ uStep
  (union-ax (sett ⟪ α ⟫ (Sset-stepFam α)) x .fst
    (∈∈ₛ {a = x} {b = ⋃ (sett ⟪ α ⟫ (Sset-stepFam α))} .fst
      (subst (λ w → ⟨ x ∈ˢ w ⟩) (Sset-compute α) x∈Sα)))
  where
  G : Type (ℓ-suc ℓ)
  G = Σ[ δ ∈ S ] (⟨ δ ∈ˢ α ⟩ × ⟨ x ∈ˢ step (Sset δ) ⟩)
  atFib : (v : S) → ⟨ x ∈ₛ v ⟩ → (m : ⟪ α ⟫) → Sset-stepFam α m ≡ v → G
  atFib v x∈ₛv m sm≡v = ⟪ α ⟫↪ m
    , ( ∈∈ₛ {a = ⟪ α ⟫↪ m} {b = α} .snd (∈ₛ⟪ α ⟫↪ m)
      , ∈∈ₛ {a = x} {b = Sset-stepFam α m} .snd
          (subst (λ w → ⟨ x ∈ₛ w ⟩) (sym sm≡v) x∈ₛv) )
  uStep : Σ[ v ∈ S ] (⟨ v ∈ₛ sett ⟪ α ⟫ (Sset-stepFam α) ⟩ × ⟨ x ∈ₛ v ⟩) → ∥ G ∥₁
  uStep (v , v∈ₛsett , x∈ₛv) = PT.map
    (λ { (m , sm≡v) → atFib v x∈ₛv m sm≡v })
    (∈∈ₛ {a = v} {b = sett ⟪ α ⟫ (Sset-stepFam α)} .snd v∈ₛsett)
```

<!--en-->
Cumulativity is then a corollary, not a construction: a lower level sits inside
`step` of itself by `step-⊆`{.Agda}, and going in carries it up. Monotonicity
in the index is even cheaper, since it needs only the single equation and no
property of `step` at all.
<!--zh-->
累积性于是是推论，而非构造：较低的层经 `step-⊆`{.Agda} 落进自身的像，再由「进去」抬升。索引上的单调性更便宜，它只用那条单方程，完全不需要 step 的任何性质。
<!--/-->

```agda
Sset-mono : {α β : S} → ⟨ β ∈ˢ α ⟩ → Sset β ⊆ Sset α
Sset-mono {α} {β} β∈α x x∈Sβ = Sset-in α β x β∈α (step-⊆ (Sset β) x x∈Sβ)

Sset-index-mono : {α β : S} → α ⊆ β → Sset α ⊆ Sset β
Sset-index-mono {α} {β} α⊆β x x∈Sα = PT.rec (snd (x ∈ˢ Sset β)) uStep
  (Sset-out α x x∈Sα)
  where
  uStep : Σ[ δ ∈ S ] (⟨ δ ∈ˢ α ⟩ × ⟨ x ∈ˢ step (Sset δ) ⟩) → ⟨ x ∈ˢ Sset β ⟩
  uStep (δ , δ∈α , x∈stepSδ) = Sset-in β δ x (α⊆β δ δ∈α) x∈stepSδ
```

<!--en-->
## The derived case equations
<!--zh-->
## 派生的分情形方程
<!--/-->

<!--en-->
The three case equations are the exports the rest of the route quotes. Zero is
the union over an empty index, so membership in `Sset ∅` is impossible and the
set is empty. The successor equation is where cumulativity and
`step-mono`{.Agda} pay: every member of `sucV β` is `β` itself or a member of
`β`, and the images of the lower levels sit inside the image of `Sset β`, while
the reverse inclusion is `β` itself, a member of its own successor. Neither
direction needs an ordinal hypothesis on `β`, so the equation holds for every
set, not only ordinals.
<!--zh-->
三条分情形方程是路线其余部分引用的出口。零是沿空索引的并，故属于 `Sset ∅` 不可能，这个集合就是空集。后继方程是累积性与 `step-mono`{.Agda} 兑现之处：`sucV β` 的每个成员是 `β` 本身或 `β` 的成员，较低诸层的像都落在 `Sset β` 的像内，而反向包含只是 `β` 自身，它是自己后继的成员。两个方向都不需要 `β` 的序数假设，故方程对一切集合成立，不限于序数。
<!--/-->

```agda
Sset-zero : Sset ∅ ≡ ∅
Sset-zero = ext-⊆ S∅⊆∅ ∅⊆S∅
  where
  S∅⊆∅ : Sset ∅ ⊆ ∅
  S∅⊆∅ x x∈S∅ = PT.rec (snd (x ∈ˢ ∅)) uStep (Sset-out ∅ x x∈S∅)
    where
    uStep : Σ[ δ ∈ S ] (⟨ δ ∈ˢ ∅ ⟩ × ⟨ x ∈ˢ step (Sset δ) ⟩) → ⟨ x ∈ˢ ∅ ⟩
    uStep (δ , δ∈∅ , _) = Empty.rec (∅-empty δ (∈∈ₛ {a = δ} {b = ∅} .fst δ∈∅))
  ∅⊆S∅ : ∅ ⊆ Sset ∅
  ∅⊆S∅ x x∈∅ = Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst x∈∅))

Sset-suc : (β : S) → Sset (sucV β) ≡ step (Sset β)
Sset-suc β = ext-⊆ sub sup
  where
  sub : Sset (sucV β) ⊆ step (Sset β)
  sub x x∈Sβ' = PT.rec (snd (x ∈ˢ step (Sset β))) uStep
    (Sset-out (sucV β) x x∈Sβ')
    where
    uStep : Σ[ γ ∈ S ] (⟨ γ ∈ˢ sucV β ⟩ × ⟨ x ∈ˢ step (Sset γ) ⟩)
          → ⟨ x ∈ˢ step (Sset β) ⟩
    uStep (γ , γ∈suc , x∈stepSγ) = ∈sucV-elim (snd (x ∈ˢ step (Sset β))) γ∈suc
      (λ γ∈β → step-mono (Sset-mono {α = β} {β = γ} γ∈β) x x∈stepSγ)
      (λ γ≡β → subst (λ w → ⟨ x ∈ˢ step (Sset w) ⟩) γ≡β x∈stepSγ)
  sup : step (Sset β) ⊆ Sset (sucV β)
  sup x x∈stepSβ = Sset-in (sucV β) β x (self∈sucV β) x∈stepSβ
```

<!--en-->
The membership reading of cumulativity follows once the successor equation is
in hand: `step-∈`{.Agda} places `Sset β` inside `step (Sset β)`, the equation
identifies that set with `Sset (sucV β)`, and cumulativity carries the level up
to any index above `sucV β`. This is the one place `step-∈`{.Agda} is spent.
<!--zh-->
累积性的成员读式在后继方程到手后随之而来：`step-∈`{.Agda} 把 `Sset β` 放进 `step (Sset β)`，方程把它等同于 `Sset (sucV β)`，累积性再把该层抬到 `sucV β` 之上的任何索引。这是 `step-∈`{.Agda} 唯一被花掉的地方。
<!--/-->

```agda
Sset-level-mem : {α β : S} → ⟨ sucV β ∈ˢ α ⟩ → ⟨ Sset β ∈ˢ Sset α ⟩
Sset-level-mem {α} {β} sucβ∈α =
  Sset-mono {α = α} {β = sucV β} sucβ∈α (Sset β)
    (subst (λ w → ⟨ Sset β ∈ˢ w ⟩) (sym (Sset-suc β)) (step-∈ (Sset β)))
```

<!--en-->
A limit ordinal is closed under successor: comparing `sucV β` with `α` by the
ordinal trichotomy leaves only membership, since equality would make `α` a
successor and the strict direction `α ∈ sucV β` would close into self-membership
through transitivity. This is the one classical step of the chapter, and it is
why `lem` is in the telescope.
<!--zh-->
极限序数对后继封闭：用序数三歧比较 `sucV β` 与 `α`，唯一幸存的情形是隶属，因为相等会使 `α` 成为后继，而严格方向 `α ∈ sucV β` 会经传递性闭成自属。这是本章唯一经典的一步，也是 `lem` 进入望远镜的原因。
<!--/-->

```agda
limit-succ-mem : (α β : S) → ⟨ isLimit α ⟩ → ⟨ β ∈ˢ α ⟩ → ⟨ sucV β ∈ˢ α ⟩
limit-succ-mem α β lim β∈α = go (ord-tri (sucV β) (suc-ord ordβ) α (isLimit-ord α lim))
  where
  ordβ : IsOrd β
  ordβ = limit-mem-ord α lim β β∈α
  go : Tri (sucV β) α → ⟨ sucV β ∈ˢ α ⟩
  go (inl sucβ∈α) = sucβ∈α
  go (inr (inl eq)) = Empty.rec (isLimit-not-succ α lim (β , (ordβ , eq)))
  go (inr (inr α∈sucβ)) = Empty.rec* {A = ⟨ sucV β ∈ˢ α ⟩}
    (∈sucV-elim (isProp⊥* {ℓ-suc ℓ}) α∈sucβ
      (λ α∈β → lift (∈-irrefl α (isLimit-ord α lim .fst {x = β} {y = α} α∈β β∈α)))
      (λ α≡β → lift (∈-irrefl β (subst (λ w → ⟨ β ∈ˢ w ⟩) α≡β β∈α))))
```

<!--en-->
The limit equation then states that a limit level is the union of the earlier
levels. One direction raises each earlier level through `step` into the union
that defines `Sset α`; the other rewrites each `step (Sset β)` by the successor
equation and closes the successor `sucV β` back inside `α` by the closure fact
just proved.
<!--zh-->
极限方程于是陈述：极限层是更早诸层之并。一个方向把每个更早的层经 step 抬进定义 `Sset α` 的那个并；另一个方向用后继方程改写每个 `step (Sset β)`，再凭刚证的封闭事实把后继 `sucV β` 关回 `α` 之内。
<!--/-->

```agda
Sset-levelFam : (α : S) → ⟪ α ⟫ → S
Sset-levelFam α m = Sset (⟪ α ⟫↪ m)

Sset-limit : (α : S) → ⟨ isLimit α ⟩ → Sset α ≡ ⋃ (sett ⟪ α ⟫ (Sset-levelFam α))
Sset-limit α lim = ext-⊆ S⊆levels levels⊆S
  where
  U : S
  U = ⋃ (sett ⟪ α ⟫ (Sset-levelFam α))
  levels⊆S : U ⊆ Sset α
  levels⊆S x x∈⋃ = PT.rec (snd (x ∈ˢ Sset α)) uStep
    (union-ax (sett ⟪ α ⟫ (Sset-levelFam α)) x .fst
      (∈∈ₛ {a = x} {b = U} .fst x∈⋃))
    where
    uStep : Σ[ v ∈ S ] (⟨ v ∈ₛ sett ⟪ α ⟫ (Sset-levelFam α) ⟩ × ⟨ x ∈ₛ v ⟩)
          → ⟨ x ∈ˢ Sset α ⟩
    uStep (v , v∈ₛsett , x∈ₛv) = PT.rec (snd (x ∈ˢ Sset α)) atFib
      (∈∈ₛ {a = v} {b = sett ⟪ α ⟫ (Sset-levelFam α)} .snd v∈ₛsett)
      where
      atFib : Σ[ m ∈ ⟪ α ⟫ ] (Sset-levelFam α m ≡ v) → ⟨ x ∈ˢ Sset α ⟩
      atFib (m , sm≡v) =
        Sset-in α (⟪ α ⟫↪ m) x
          (∈∈ₛ {a = ⟪ α ⟫↪ m} {b = α} .snd (∈ₛ⟪ α ⟫↪ m))
          (step-⊆ (Sset (⟪ α ⟫↪ m)) x
            (∈∈ₛ {a = x} {b = Sset (⟪ α ⟫↪ m)} .snd
              (subst (λ w → ⟨ x ∈ₛ w ⟩) (sym sm≡v) x∈ₛv)))
  S⊆levels : Sset α ⊆ U
  S⊆levels x x∈Sα = PT.rec (snd (x ∈ˢ U)) uStep (Sset-out α x x∈Sα)
    where
    uStep : Σ[ δ ∈ S ] (⟨ δ ∈ˢ α ⟩ × ⟨ x ∈ˢ step (Sset δ) ⟩)
          → ⟨ x ∈ˢ U ⟩
    uStep (δ , δ∈α , x∈stepSδ) = go (limit-succ-mem α δ lim δ∈α)
      where
      x∈Sδ' : ⟨ x ∈ˢ Sset (sucV δ) ⟩
      x∈Sδ' = subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (Sset-suc δ)) x∈stepSδ
      go : ⟨ sucV δ ∈ˢ α ⟩ → ⟨ x ∈ˢ U ⟩
      go sucδ∈α = ∈∈ₛ {a = x} {b = U} .snd
        (union-ax (sett ⟪ α ⟫ (Sset-levelFam α)) x .snd
          ∣ Sset (sucV δ) , (memₛ , x∈ₛSδ') ∣₁)
        where
        fib = ∈-asFiber {a = sucV δ} {b = α} sucδ∈α
        p : ⟪ α ⟫↪ (fib .fst) ≡ sucV δ
        p = fib .snd
        memₛ : ⟨ Sset (sucV δ) ∈ₛ sett ⟪ α ⟫ (Sset-levelFam α) ⟩
        memₛ = ∈∈ₛ {a = Sset (sucV δ)} {b = sett ⟪ α ⟫ (Sset-levelFam α)} .fst
          ∣ fib .fst , cong Sset p ∣₁
        x∈ₛSδ' : ⟨ x ∈ₛ Sset (sucV δ) ⟩
        x∈ₛSδ' = ∈∈ₛ {a = x} {b = Sset (sucV δ)} .fst x∈Sδ'
```

<!--en-->
## J at limits
<!--zh-->
## 极限处的 J
<!--/-->

<!--en-->
Restricting the family to limit indices gives the subfamily the fine-structure
route reads as `J`, spelled `Jset`{.Agda} in code; `J α` reads "the `α`-th
level at the limit `α`". Its levels are transitive, it is monotone, and at a
limit index it is the union of the earlier levels, all inherited from `Sset`
definitionally. Whether `J α` is closed under the sixteen operations is a
different question: the abstract step carries no operations to close over, so
that fact belongs to the instantiation batch, not to this chapter.
<!--zh-->
把族限制在极限索引上，得到细结构路线读作 `J` 的子族，代码里拼作 `Jset`{.Agda}；`J α` 读作「极限 `α` 处的第 `α` 层」。它的诸层传递、它单调，且在极限索引处是更早诸层之并，这些都从 `Sset` 定义性地继承。`J α` 是否对十六个运算封闭是另一个问题：抽象 step 身上没有任何可供封闭的运算，故那个事实属于实例化批次，不属于本章。
<!--/-->

```agda
Jset : (α : S) → ⟨ isLimit α ⟩ → S
Jset α _ = Sset α

Jset-trans : (α : S) → (lim : ⟨ isLimit α ⟩) → isTransV (Jset α lim)
Jset-trans α lim = Sset-trans α

Jset-mono : {α β : S} → (limα : ⟨ isLimit α ⟩) → (limβ : ⟨ isLimit β ⟩)
          → ⟨ β ∈ˢ α ⟩ → Jset β limβ ⊆ Jset α limα
Jset-mono {α} {β} limα limβ β∈α = Sset-mono {α = α} {β = β} β∈α

Jset-limit : (α : S) → (lim : ⟨ isLimit α ⟩)
           → Jset α lim ≡ ⋃ (sett ⟪ α ⟫ (Sset-levelFam α))
Jset-limit α lim = Sset-limit α lim
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The engine is complete: the single-equation family, cumulativity in both
readings, monotonicity, transitivity of every level, the three derived
equations, and `J` with its reads. The telescope records the whole debt: four
properties of `step` and one instance of the excluded middle, the latter spent
only on the limit equation through the ordinal trichotomy. The instantiation
batch pays the debt with the sixteen operations and reads the hierarchy off;
nothing here unfolds because nothing here is concrete.
<!--zh-->
引擎完整：单方程族、两种读法的累积性、单调性、每层的传递性、三条派生方程，以及 `J` 及其读法。望远镜记下全部债务：step 的四条性质与一份排中律实例，后者仅经序数三歧花在极限方程上。实例化批次用十六个运算清偿债务并读出层级；此处不展开任何东西，因为此处没有任何具体之物。
<!--/-->

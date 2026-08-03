# The ordinal block map

<!--en-->
The bridge between the two towers runs over ordinals: one constructible step
costs `ω` rud steps, and one rud step's junk costs constructible steps, so the
two towers can only be interleaved at indices spaced `ω` apart. This chapter
delivers the index map, the block function `b` that writes `b α = ω · α`: zero
goes to zero, a successor adds one block of `ω` successors, and a limit
collects the earlier blocks. The bridge then reads the rud tower at the
`b`-indices, and what it spends is exactly the four laws proved here: the
blocks are ordinals, they are monotone, every nonzero block is a limit, and
the finite successor iterations of a block stay inside the next block.
<!--zh-->
两座塔之间的桥要跑在序数上：一步可构造要花掉 `ω` 步初步函数，一步初步函数的垃圾又要花掉可构造步，故两塔只能在间隔 `ω` 的索引处交错。本章交付索引映射，即把 `b α = ω · α` 写出来的块函数 `b`：零映到零，后继加一个由 `ω` 个后继组成的块，极限收拢更早的诸块。桥随后在 `b` 索引处读初步函数塔，而它所花费的正是此处证明的四条律：诸块是序数、单调、每个非零块是极限，且一个块的有限后继迭代都落在下一块之内。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Rud.OrdBlocks {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ}
  using ( 𝒮ᵥ; extensionalV; ∈-induction; ∈-induction-compute; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim; ∈sucV-inl; self∈sucV )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( suc-ord; mem-ord; setUnion-ord )
open import L.Rud.OrdArith {ℓ} lem
  using ( isLimit; isLimit-ord; isLimit-not-zero; isLimit-not-succ; limit-mem-ord
        ; ord-case; isSucc )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri; Tri )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Functions.Logic using ( ⇔toPath; ∃[]-syntax )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber )
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
hierarchy's extensionality, exactly as in the tower chapter; this is the only
equality engine the case equations use.
<!--zh-->
包含逐点写出，互相包含按层级的外延性即相等，与塔章完全一致；这是分情形方程唯一用到的相等引擎。
<!--/-->

```agda
_⊆_ : S → S → Type (ℓ-suc ℓ)
u ⊆ v = (x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩

ext-⊆ : {u v : S} → u ⊆ v → v ⊆ u → u ≡ v
ext-⊆ {u} {v} sub sup = extensionalV (λ x → ⇔toPath (sub x) (sup x))
```

<!--en-->
## The ω-extension
<!--zh-->
## ω 延拓
<!--/-->

<!--en-->
The block added at a successor is `u` plus `ω` further successors: the union of
the finitely iterated successors of `u`, indexed by the naturals. This is the
formulation the laws spend least on: the level `u` itself and every finite
iterate sit in `+ω u` by one membership step, ordinality comes from the
ordinal chapter's union closure in one line, and the successor-absorption law
below reads off the same family. The two membership directions are named
first, since every later argument reaches for one of them.
<!--zh-->
后继处所加的块是 `u` 再添 `ω` 个后继：以自然数为索引、对 `u` 有限迭代后继所得之并。这是诸律花费最少的表述：`u` 自身与每个有限迭代落在 `+ω u` 里只花一步隶属，序数性由序数章的并闭包一行到手，下方的后继吸收律也读同一个族。两条隶属方向先具名，因为此后每个论证都要取其中之一。
<!--/-->

```agda
sucIter : ℕ → S → S
sucIter zero u = u
sucIter (suc n) u = sucV (sucIter n u)

+ω : S → S
+ω u = ⋃ (sett (Lift {ℓ-zero} {ℓ} ℕ) (λ m → sucIter (suc (lower m)) u))

+ω-in : (u x : S) → (n : ℕ) → ⟨ x ∈ˢ sucIter (suc n) u ⟩ → ⟨ x ∈ˢ +ω u ⟩
+ω-in u x n x∈ = ∈∈ₛ {a = x} {b = +ω u} .snd
  (union-ax (sett (Lift {ℓ-zero} {ℓ} ℕ) F) x .snd
    ∣ sucIter (suc n) u , (memb , x∈ₛ) ∣₁)
  where
  F : Lift {ℓ-zero} {ℓ} ℕ → S
  F m = sucIter (suc (lower m)) u
  memb : ⟨ sucIter (suc n) u ∈ₛ sett (Lift {ℓ-zero} {ℓ} ℕ) F ⟩
  memb = ∈∈ₛ {a = sucIter (suc n) u} {b = sett (Lift {ℓ-zero} {ℓ} ℕ) F} .fst
    ∣ lift n , refl ∣₁
  x∈ₛ : ⟨ x ∈ₛ sucIter (suc n) u ⟩
  x∈ₛ = ∈∈ₛ {a = x} {b = sucIter (suc n) u} .fst x∈

+ω-out : (u x : S) → ⟨ x ∈ˢ +ω u ⟩
        → ∥ Σ[ n ∈ ℕ ] ⟨ x ∈ˢ sucIter (suc n) u ⟩ ∥₁
+ω-out u x x∈ = PT.rec squash₁ uStep
  (union-ax (sett (Lift {ℓ-zero} {ℓ} ℕ) F) x .fst
    (∈∈ₛ {a = x} {b = +ω u} .fst x∈))
  where
  F : Lift {ℓ-zero} {ℓ} ℕ → S
  F m = sucIter (suc (lower m)) u
  uStep : Σ[ v ∈ S ] (⟨ v ∈ₛ sett (Lift {ℓ-zero} {ℓ} ℕ) F ⟩ × ⟨ x ∈ₛ v ⟩)
        → ∥ Σ[ n ∈ ℕ ] ⟨ x ∈ˢ sucIter (suc n) u ⟩ ∥₁
  uStep (v , v∈ₛsett , x∈ₛv) = PT.rec squash₁ atFib
    (∈∈ₛ {a = v} {b = sett (Lift {ℓ-zero} {ℓ} ℕ) F} .snd v∈ₛsett)
    where
    atFib : Σ[ m ∈ Lift {ℓ-zero} {ℓ} ℕ ] (F m ≡ v)
          → ∥ Σ[ n ∈ ℕ ] ⟨ x ∈ˢ sucIter (suc n) u ⟩ ∥₁
    atFib (m , Fm≡v) =
      ∣ lower m , subst (λ w → ⟨ x ∈ˢ w ⟩) (sym Fm≡v)
          (∈∈ₛ {a = x} {b = v} .snd x∈ₛv) ∣₁

+ω-mem : (u : S) → ⟨ u ∈ˢ +ω u ⟩
+ω-mem u = +ω-in u u 0 (self∈sucV u)

+ω-sup : (u : S) → u ⊆ +ω u
+ω-sup u x x∈u = +ω-in u x 0 (∈sucV-inl x∈u)

+ω-iter : (n : ℕ) → (u : S) → ⟨ sucIter n u ∈ˢ +ω u ⟩
+ω-iter n u = +ω-in u (sucIter n u) n (self∈sucV (sucIter n u))
```

<!--en-->
Ordinality of the extension is the ordinal chapter's union closure applied to
the family of iterated successors; each iterate is an ordinal by one step of
the successor-ordinal lemma. This is the fact the bridge's limit certificates
will lean on inside the blocks.
<!--zh-->
延拓的序数性是序数章并闭包施于迭代后继之族的结果；每个迭代由后继序数引理一步成为序数。这是桥的极限证书在块内将要倚靠的事实。
<!--/-->

```agda
sucIter-ord : {u : S} → (n : ℕ) → IsOrd u → IsOrd (sucIter n u)
sucIter-ord zero ou = ou
sucIter-ord (suc n) ou = suc-ord (sucIter-ord n ou)

+ω-ord : (u : S) → IsOrd u → IsOrd (+ω u)
+ω-ord u ou = setUnion-ord (Lift {ℓ-zero} {ℓ} ℕ) (λ m → sucIter (suc (lower m)) u)
  (λ m → sucIter-ord (suc (lower m)) ou)
```

<!--en-->
## The block map
<!--zh-->
## 块映射
<!--/-->

<!--en-->
The block map is a transfinite recursion over membership, in the same single
equation style as the tower itself: the block at `α` is the union, over the
members `δ` of `α`, of the ω-extension of the block at `δ`. On the von
Neumann ordinals this single clause is exactly the three textbook clauses, and
the case equations below are consequences, not further cases: `b ∅ = ∅` by
emptiness, `b (sucV α) = +ω (b α)` by the successor split, and at a limit the
union of the earlier blocks. The recursion is sealed `opaque`{.Agda} with
`b-compute`{.Agda} as its official unfolding, as the tower's is.
<!--zh-->
块映射是与塔同款单方程的沿成员超穷递归：`α` 处的块是沿 `α` 的成员 `δ`、对 `δ` 处块的 ω 延拓所取之并。在冯·诺伊曼序数上，这一条子句恰是教科书的三条子句，而下方诸分情形方程是推论，并非另设情形：`b ∅ = ∅` 出于空性，`b (sucV α) = +ω (b α)` 出于后继切分，极限处取更早诸块之并。递归以 `opaque`{.Agda} 封印，`b-compute`{.Agda} 是官方展开，与塔一致。
<!--/-->

```agda
private
  ix∈ : (α : S) (m : ⟪ α ⟫) → ⟪ α ⟫↪ m ∈ᵗ α
  ix∈ α m = ∈∈ₛ {a = ⟪ α ⟫↪ m} {b = α} .snd (∈ₛ⟪ α ⟫↪ m)

b-step : (α : S) → (∀ β → β ∈ᵗ α → S) → S
b-step α rec = ⋃ (sett ⟪ α ⟫ (λ m → +ω (rec (⟪ α ⟫↪ m) (ix∈ α m))))

opaque
  b : S → S
  b = ∈-induction b-step

b-stepFam : (α : S) → ⟪ α ⟫ → S
b-stepFam α m = +ω (b (⟪ α ⟫↪ m))

opaque
  unfolding b
  b-compute : (α : S) → b α ≡ ⋃ (sett ⟪ α ⟫ (b-stepFam α))
  b-compute = ∈-induction-compute b-step
```

<!--en-->
Membership in a block reads the defining union in both directions, exactly as
in the tower: going in names a member `δ` of the index together with a
membership in `+ω (b δ)`, and coming out names the fibre. The zero equation
then says the block at zero is empty, since the empty set has no members.
<!--zh-->
块的隶属把定义那个并两头各读一遍，与塔完全一致：进去点名索引的一个成员 `δ`，连同一条 `+ω (b δ)` 中的成员资格，出来点名纤维。零方程于是说零处的块为空，因为空集没有成员。
<!--/-->

```agda
b-in : (α δ x : S) → ⟨ δ ∈ˢ α ⟩ → ⟨ x ∈ˢ +ω (b δ) ⟩ → ⟨ x ∈ˢ b α ⟩
b-in α δ x δ∈α x∈ =
  subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (b-compute α))
    (∈∈ₛ {a = x} {b = ⋃ (sett ⟪ α ⟫ (b-stepFam α))} .snd
      (union-ax (sett ⟪ α ⟫ (b-stepFam α)) x .snd
        ∣ +ω (b δ) , (memb , x∈ₛ) ∣₁))
  where
  fib = ∈-asFiber {a = δ} {b = α} δ∈α
  memb : ⟨ +ω (b δ) ∈ₛ sett ⟪ α ⟫ (b-stepFam α) ⟩
  memb = ∈∈ₛ {a = +ω (b δ)} {b = sett ⟪ α ⟫ (b-stepFam α)} .fst
    ∣ fib .fst , cong (λ w → +ω (b w)) (fib .snd) ∣₁
  x∈ₛ : ⟨ x ∈ₛ +ω (b δ) ⟩
  x∈ₛ = ∈∈ₛ {a = x} {b = +ω (b δ)} .fst x∈

b-out : (α x : S) → ⟨ x ∈ˢ b α ⟩
      → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ α ⟩ × ⟨ x ∈ˢ +ω (b δ) ⟩) ∥₁
b-out α x x∈bα = PT.rec squash₁ uStep
  (union-ax (sett ⟪ α ⟫ (b-stepFam α)) x .fst
    (∈∈ₛ {a = x} {b = ⋃ (sett ⟪ α ⟫ (b-stepFam α))} .fst
      (subst (λ w → ⟨ x ∈ˢ w ⟩) (b-compute α) x∈bα)))
  where
  G : Type (ℓ-suc ℓ)
  G = Σ[ δ ∈ S ] (⟨ δ ∈ˢ α ⟩ × ⟨ x ∈ˢ +ω (b δ) ⟩)
  atFib : (v : S) → ⟨ x ∈ₛ v ⟩ → Σ[ m ∈ ⟪ α ⟫ ] (b-stepFam α m ≡ v) → G
  atFib v x∈ₛv (m , sm≡v) = ⟪ α ⟫↪ m
    , ( ix∈ α m
      , ∈∈ₛ {a = x} {b = b-stepFam α m} .snd
          (subst (λ w → ⟨ x ∈ₛ w ⟩) (sym sm≡v) x∈ₛv) )
  uStep : Σ[ v ∈ S ] (⟨ v ∈ₛ sett ⟪ α ⟫ (b-stepFam α) ⟩ × ⟨ x ∈ₛ v ⟩) → ∥ G ∥₁
  uStep (v , v∈ₛsett , x∈ₛv) = PT.map (atFib v x∈ₛv)
    (∈∈ₛ {a = v} {b = sett ⟪ α ⟫ (b-stepFam α)} .snd v∈ₛsett)

b-zero : b ∅ ≡ ∅
b-zero = ext-⊆ b∅⊆∅ ∅⊆b∅
  where
  b∅⊆∅ : b ∅ ⊆ ∅
  b∅⊆∅ x x∈b∅ = PT.rec (snd (x ∈ˢ ∅)) uStep (b-out ∅ x x∈b∅)
    where
    uStep : Σ[ δ ∈ S ] (⟨ δ ∈ˢ ∅ ⟩ × ⟨ x ∈ˢ +ω (b δ) ⟩) → ⟨ x ∈ˢ ∅ ⟩
    uStep (δ , δ∈∅ , _) = Empty.rec (∅-empty δ (∈∈ₛ {a = δ} {b = ∅} .fst δ∈∅))
  ∅⊆b∅ : ∅ ⊆ b ∅
  ∅⊆b∅ x x∈∅ = Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst x∈∅))
```

<!--en-->
## Monotonicity
<!--zh-->
## 单调性
<!--/-->

<!--en-->
The block map is monotone in the strong, membership sense, and it costs no
induction: the block at `β` sits in its own ω-extension, which is one member of
the family the block at `α` unions over. Inclusion of the blocks themselves
comes at the same price, and both hold for arbitrary indices, no ordinality
needed.
<!--zh-->
块映射在强意义、即隶属意义下单调，而且不花归纳：`β` 处的块落在自身的 ω 延拓里，而后者正是 `α` 处块所并之族的一员。诸块自身的包含同价而来，两者都对任意索引成立，无须序数性。
<!--/-->

```agda
b-mono : {α β : S} → ⟨ β ∈ˢ α ⟩ → ⟨ b β ∈ˢ b α ⟩
b-mono {α} {β} β∈α = b-in α β (b β) β∈α (+ω-mem (b β))

b-incl : {α β : S} → ⟨ β ∈ˢ α ⟩ → b β ⊆ b α
b-incl {α} {β} β∈α x x∈bβ = b-in α β x β∈α (+ω-sup (b β) x x∈bβ)
```

<!--en-->
## Ordinality of the blocks
<!--zh-->
## 诸块的序数性
<!--/-->

<!--en-->
Every block is an ordinal, by the same induction the tower used: unfold once,
use the hypothesis at each member, and close with the union-of-ordinals lemma.
The members of an ordinal index are ordinals by downward closure, so the
induction hypothesis is always applied at ordinals.
<!--zh-->
每个块都是序数，归纳与塔所用相同：展开一次，在每个成员处用假设，再以序数之并引理收拢。序数索引的成员由向下封闭而为序数，故归纳假设总在序数处施放。
<!--/-->

```agda
b-ord : (α : S) → IsOrd α → IsOrd (b α)
b-ord = ∈-induction b-ord-step
  where
  b-ord-step : (α : S) → ((β : S) → β ∈ᵗ α → IsOrd β → IsOrd (b β))
             → IsOrd α → IsOrd (b α)
  b-ord-step α IH ordα = subst IsOrd (sym (b-compute α))
    (setUnion-ord ⟪ α ⟫ (b-stepFam α)
      (λ m → +ω-ord (b (⟪ α ⟫↪ m))
        (IH (⟪ α ⟫↪ m) (ix∈ α m) (mem-ord {A = α} ordα (⟪ α ⟫↪ m) (ix∈ α m)))))
```

<!--en-->
## Limits close under successors
<!--zh-->
## 极限对后继封闭
<!--/-->

<!--en-->
The limit case of the equations needs one fact about limits themselves: a limit
ordinal contains the successor of each of its members. This is the ordinal
chapter's trichotomy applied to `sucV β` against `α`: equality would make `α`
a successor, and the strict direction would close into self-membership through
transitivity. The hierarchy chapter exports the same fact; it is re-derived
here, at the same price, because this chapter stands on the ordinal kit alone.
<!--zh-->
方程的极限情形需要一个关于极限自身的事实：极限序数包含其每个成员的后继。这是序数章的三歧施于 `sucV β` 与 `α`：相等会使 `α` 成为后继，严格方向则经传递性闭成自属。层级章导出同一事实；本章只立于序数工具箱之上，故以同样的代价在此重证。
<!--/-->

```agda
private
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
## The case equations
<!--zh-->
## 分情形方程
<!--/-->

<!--en-->
The three clauses are now consequences of the single recursion clause. Zero is
done above. At a limit, the block is the union of the earlier blocks: one
direction raises each earlier block through its ω-extension into the defining
union, the other rewrites each `+ω (b δ)` as the block at `sucV δ` and closes
the successor back inside the limit. At a successor, the defining union over
`sucV α` is exactly the block at `α` plus its ω-extension: every member of
`sucV α` is `α` or below, the below-members collapse into `b α` by
monotonicity, and the collapse is where the ordinal comparison enters.
<!--zh-->
三条子句于是都是单递归子句的推论。零已在上文。极限处，块是更早诸块之并：一个方向把每个更早块经其 ω 延拓抬进定义那个并，另一个方向把每个 `+ω (b δ)` 改写为 `sucV δ` 处的块，再把后继闭回极限之内。后继处，`sucV α` 上的定义并恰是 `α` 处的块加其 ω 延拓：`sucV α` 的每个成员是 `α` 或更下，更下的成员经单调性塌进 `b α`，而塌缩之处正是序数比较进场的地方。
<!--/-->

```agda
-- D-10 sanity check, small cases:
--   b ∅ = ∅
--   b 1 = b (sucV ∅) = +ω (b ∅) = +ω ∅ = ω, a limit
--   b 2 = +ω ω = ω·2, a limit
--   b ω = ⋃ { b n | n < ω } = ⋃ { ω·n | n } = ω², a limit
-- Honest side conditions:
--   b-suc needs IsOrd α: b is total (b α = ∅ off the ordinals), but the
--   successor clause is an ordinal statement.
--   b-limit needs isLimit α: at a successor the right-hand union would omit
--   the fresh block +ω (b α); at zero both sides are empty but no limit
--   certificate exists to state the equation under; at limits of limits the
--   equation survives, since sucV δ ∈ α and the block at sucV δ is a genuine
--   extension of the block at δ.
--   b-limit-nonzero needs α ≢ ∅: b ∅ = ∅ is not a limit.

b-limit : (α : S) → ⟨ isLimit α ⟩ → b α ≡ ⋃ (sett ⟪ α ⟫ (λ m → b (⟪ α ⟫↪ m)))
b-limit α lim = ext-⊆ b⊆levels levels⊆b
  where
  U : S
  U = ⋃ (sett ⟪ α ⟫ (λ m → b (⟪ α ⟫↪ m)))
  levels⊆b : U ⊆ b α
  levels⊆b x x∈U = PT.rec (snd (x ∈ˢ b α)) uStep
    (union-ax (sett ⟪ α ⟫ (λ m → b (⟪ α ⟫↪ m))) x .fst
      (∈∈ₛ {a = x} {b = U} .fst x∈U))
    where
    uStep : Σ[ v ∈ S ] (⟨ v ∈ₛ sett ⟪ α ⟫ (λ m → b (⟪ α ⟫↪ m)) ⟩ × ⟨ x ∈ₛ v ⟩)
          → ⟨ x ∈ˢ b α ⟩
    uStep (v , v∈ₛsett , x∈ₛv) = PT.rec (snd (x ∈ˢ b α)) atFib
      (∈∈ₛ {a = v} {b = sett ⟪ α ⟫ (λ m → b (⟪ α ⟫↪ m))} .snd v∈ₛsett)
      where
      atFib : Σ[ m ∈ ⟪ α ⟫ ] (b (⟪ α ⟫↪ m) ≡ v) → ⟨ x ∈ˢ b α ⟩
      atFib (m , bm≡v) = b-in α (⟪ α ⟫↪ m) x (ix∈ α m)
        (+ω-sup (b (⟪ α ⟫↪ m)) x
          (∈∈ₛ {a = x} {b = b (⟪ α ⟫↪ m)} .snd (subst (λ w → ⟨ x ∈ₛ w ⟩) (sym bm≡v) x∈ₛv)))
  b⊆levels : b α ⊆ U
  b⊆levels x x∈bα = PT.rec (snd (x ∈ˢ U)) uStep (b-out α x x∈bα)
    where
    uStep : Σ[ δ ∈ S ] (⟨ δ ∈ˢ α ⟩ × ⟨ x ∈ˢ +ω (b δ) ⟩) → ⟨ x ∈ˢ U ⟩
    uStep (δ , δ∈α , x∈+ωbδ) = go (limit-succ-mem α δ lim δ∈α)
      where
      x∈bδ' : ⟨ x ∈ˢ b (sucV δ) ⟩
      x∈bδ' = b-in (sucV δ) δ x (self∈sucV δ) x∈+ωbδ
      go : ⟨ sucV δ ∈ˢ α ⟩ → ⟨ x ∈ˢ U ⟩
      go sucδ∈α = ∈∈ₛ {a = x} {b = U} .snd
        (union-ax (sett ⟪ α ⟫ (λ m → b (⟪ α ⟫↪ m))) x .snd
          ∣ b (sucV δ) , (memb , x∈ₛbδ') ∣₁)
        where
        fib = ∈-asFiber {a = sucV δ} {b = α} sucδ∈α
        memb : ⟨ b (sucV δ) ∈ₛ sett ⟪ α ⟫ (λ m → b (⟪ α ⟫↪ m)) ⟩
        memb = ∈∈ₛ {a = b (sucV δ)} {b = sett ⟪ α ⟫ (λ m → b (⟪ α ⟫↪ m))} .fst
          ∣ fib .fst , cong b (fib .snd) ∣₁
        x∈ₛbδ' : ⟨ x ∈ₛ b (sucV δ) ⟩
        x∈ₛbδ' = ∈∈ₛ {a = x} {b = b (sucV δ)} .fst x∈bδ'
```

<!--en-->
The successor clause collapses by inclusion in both directions. The forward
direction is the one place the successor split of `sucV α` spends the ordinal
comparison: the members below `α` collapse because `+ω` is monotone in the
subset order on ordinals, and that monotonicity is the successor operator's
one classical step, the ordinal trichotomy applied to the two ordinals
compared by inclusion.
<!--zh-->
后继子句按双向包含塌缩。正向是 `sucV α` 的后继切分花掉序数比较的唯一位点：`α` 以下的成员因 `+ω` 在序数的子集序上单调而塌缩，而该单调性正是后继算子唯一经典的一步，即把序数三歧施于按包含比较的两个序数。
<!--/-->

```agda
sucV-mono-ord : {u v : S} → IsOrd u → IsOrd v → u ⊆ v → sucV u ⊆ sucV v
sucV-mono-ord {u} {v} ou ov sub x x∈ = ∈sucV-elim (snd (x ∈ˢ sucV v)) x∈
  (λ x∈u → ∈sucV-inl (sub x x∈u))
  (λ x≡u → subst (λ w → ⟨ w ∈ˢ sucV v ⟩) (sym x≡u) (go (ord-tri u ou v ov)))
  where
  go : Tri u v → ⟨ u ∈ˢ sucV v ⟩
  go (inl u∈v) = ∈sucV-inl u∈v
  go (inr (inl u≡v)) = subst (λ w → ⟨ u ∈ˢ w ⟩) (cong sucV u≡v) (self∈sucV u)
  go (inr (inr v∈u)) = Empty.rec (∈-irrefl v (sub v v∈u))

sucIter-incl : (n : ℕ) → {u v : S} → IsOrd u → IsOrd v → u ⊆ v → sucIter n u ⊆ sucIter n v
sucIter-incl zero ou ov sub = sub
sucIter-incl (suc n) ou ov sub = sucV-mono-ord (sucIter-ord n ou) (sucIter-ord n ov)
  (sucIter-incl n ou ov sub)

+ω-mono : {u v : S} → IsOrd u → IsOrd v → u ⊆ v → +ω u ⊆ +ω v
+ω-mono {u} {v} ou ov sub x x∈ = PT.rec (snd (x ∈ˢ +ω v)) uStep (+ω-out u x x∈)
  where
  uStep : Σ[ n ∈ ℕ ] ⟨ x ∈ˢ sucIter (suc n) u ⟩ → ⟨ x ∈ˢ +ω v ⟩
  uStep (n , x∈) = +ω-in v x n (sucIter-incl (suc n) ou ov sub x x∈)

b-suc : (α : S) → IsOrd α → b (sucV α) ≡ +ω (b α)
b-suc α ordα = ext-⊆ sub sup
  where
  sup : +ω (b α) ⊆ b (sucV α)
  sup x x∈ = b-in (sucV α) α x (self∈sucV α) x∈
  sub : b (sucV α) ⊆ +ω (b α)
  sub x x∈ = PT.rec (snd (x ∈ˢ +ω (b α))) uStep (b-out (sucV α) x x∈)
    where
    uStep : Σ[ δ ∈ S ] (⟨ δ ∈ˢ sucV α ⟩ × ⟨ x ∈ˢ +ω (b δ) ⟩) → ⟨ x ∈ˢ +ω (b α) ⟩
    uStep (δ , δ∈suc , x∈) = ∈sucV-elim (snd (x ∈ˢ +ω (b α))) δ∈suc
      (λ δ∈α → +ω-mono (b-ord δ (mem-ord {A = α} ordα δ δ∈α)) (b-ord α ordα)
        (b-incl {α = α} {β = δ} δ∈α) x x∈)
      (λ δ≡α → subst (λ w → ⟨ x ∈ˢ +ω (b w) ⟩) δ≡α x∈)
```

<!--en-->
## The successor-absorption fact
<!--zh-->
## 后继吸收事实
<!--/-->

<!--en-->
The bridge reads the rud tower at the block indices, and what it needs between
`b β` and `b (sucV β)` is that every finite successor iteration of the lower
block stays inside the next block. One membership step places the `n`-th
iterate in `+ω (b β)`, and the ω-extension is a member of the family the next
block unions over, so the fact costs no induction. Together with the limit law
below, this is exactly what the tower's successor equation and limit-closure
fact consume at the block indices.
<!--zh-->
桥在块索引处读初步函数塔，而它在 `b β` 与 `b (sucV β)` 之间需要的，是较低块的每个有限后继迭代都落在下一块之内。一步隶属把第 `n` 个迭代放进 `+ω (b β)`，而 ω 延拓正是下一块所并之族的一员，故该事实不花归纳。连同下方的极限律，这恰是塔的后继方程与极限封闭事实在块索引处所要消费的东西。
<!--/-->

```agda
b-absorbs : (α : S) → (n : ℕ) → ⟨ sucIter n (b α) ∈ˢ b (sucV α) ⟩
b-absorbs α n = b-in (sucV α) α (sucIter n (b α)) (self∈sucV α) (+ω-iter n (b α))
```

<!--en-->
## The limit law
<!--zh-->
## 极限律
<!--/-->

<!--en-->
The load-bearing law: every nonzero block is a limit ordinal, so the bridge can
read `Jset` at every `b`-index it ever forms. At a successor the block is an
ω-extension, and the extension is a limit: it is an ordinal, it contains its
own base, and it is not a successor, because a successor of `γ` inside the
extension would force `γ` into one of the finite iterates and close into
self-membership through transitivity. At a limit the same argument runs one
member down: the successor `γ` of the union lies in some earlier block, its
successor collapses to the block one step up, and the block one step up is
itself a member of the union. The nonemptiness at a limit is the one
classical step of the chapter, the excluded middle applied to whether the
limit index has a member.
<!--zh-->
承重的律：每个非零块都是极限序数，故桥可以在它造出的每个 `b` 索引处读 `Jset`。后继处，块是 ω 延拓，而延拓是极限：它是序数、含自己的底，且不是后继，因为延拓中 `γ` 的后继会迫使 `γ` 落入某个有限迭代，再经传递性闭成自属。极限处同一论证下行一个成员：并的后继 `γ` 落在某个更早块里，它的后继塌缩到上一层的块，而上一层的块本身就是并的一员。极限处的非空性是本章唯一经典的一步，即把排中律施于「极限索引是否有成员」。
<!--/-->

```agda
suc-⊆ : {A x : S} → IsOrd A → ⟨ x ∈ˢ A ⟩ → sucV x ⊆ A
suc-⊆ {A} {x} ordA x∈A z z∈sucx = ∈sucV-elim (snd (z ∈ˢ A)) z∈sucx
  (λ z∈x → ordA .fst {x = x} {y = z} z∈x x∈A)
  (λ z≡x → subst (λ w → ⟨ w ∈ˢ A ⟩) (sym z≡x) x∈A)

+ω-limit : (u : S) → IsOrd u → ⟨ isLimit (+ω u) ⟩
+ω-limit u ou = ( +ω-ord u ou
                , nz
                , ns )
  where
  nz : (+ω u ≡ ∅) → Empty.⊥
  nz e = ∅-empty u (∈∈ₛ {a = u} {b = ∅} .fst (subst (λ w → ⟨ u ∈ˢ w ⟩) e (+ω-mem u)))
  ns : ⟨ isSucc (+ω u) ⟩ → Empty.⊥
  ns (γ , ordγ , sucγ≡) = PT.rec Empty.isProp⊥ uStep (+ω-out u γ γ∈)
    where
    γ∈ : ⟨ γ ∈ˢ +ω u ⟩
    γ∈ = subst (λ w → ⟨ γ ∈ˢ w ⟩) sucγ≡ (self∈sucV γ)
    uStep : Σ[ n ∈ ℕ ] ⟨ γ ∈ˢ sucIter (suc n) u ⟩ → Empty.⊥
    uStep (n , γ∈sucn) = Empty.rec* {A = Empty.⊥}
      (∈sucV-elim {P = Empty.⊥* {ℓ-suc ℓ}} (Empty.isProp⊥* {ℓ-suc ℓ})
        γ∈sucn (λ γ∈n → lift (in1 γ∈n)) (λ γ≡n → lift (in2 γ≡n)))
      where
      t∈sucγ : ⟨ sucIter (suc n) u ∈ˢ sucV γ ⟩
      t∈sucγ = subst (λ w → ⟨ sucIter (suc n) u ∈ˢ w ⟩) (sym sucγ≡) (+ω-iter (suc n) u)
      in2 : γ ≡ sucIter n u → Empty.⊥
      in2 γ≡n = ∈-irrefl (sucV γ) t∈sucγ'
        where
        t∈sucγ' : ⟨ sucV γ ∈ˢ sucV γ ⟩
        t∈sucγ' = subst (λ w → ⟨ w ∈ˢ sucV γ ⟩) (sym (cong sucV γ≡n)) t∈sucγ
      in1 : ⟨ γ ∈ˢ sucIter n u ⟩ → Empty.⊥
      in1 γ∈n = Empty.rec* {A = Empty.⊥}
        (∈sucV-elim {P = Empty.⊥* {ℓ-suc ℓ}} (Empty.isProp⊥* {ℓ-suc ℓ}) t∈sucγ
          (λ t∈γ → lift (∈-irrefl (sucIter n u)
            (sucIter-ord n ou .fst {x = γ} {y = sucIter n u}
              (ordγ .fst {x = sucIter (suc n) u} {y = sucIter n u}
                (self∈sucV (sucIter n u)) t∈γ) γ∈n)))
          (λ t≡γ → lift (∈-irrefl (sucIter n u)
            (sucIter-ord n ou .fst {x = γ} {y = sucIter n u}
              (subst (λ w → ⟨ sucIter n u ∈ˢ w ⟩) t≡γ (self∈sucV (sucIter n u))) γ∈n))))
```

<!--en-->
At a limit index the same not-a-successor argument runs against the union of
the earlier blocks, and nonemptiness follows once some member exists, which the
excluded middle supplies. The two halves assemble the limit certificate.
<!--zh-->
极限索引处，同一个「非后继」论证对着更早诸块之并运行，而一旦某个成员存在，非空随之而来，排中律供应这个成员。两半装配出极限证书。
<!--/-->

```agda
private
  limit-block-limit : (α : S) → ⟨ isLimit α ⟩ → ⟨ isLimit (b α) ⟩
  limit-block-limit α lim = ( b-ord α (isLimit-ord α lim)
                            , nz
                            , ns )
    where
    nz : (b α ≡ ∅) → Empty.⊥
    nz e = go (lem (∃[ δ ] (δ ∈ˢ α)))
      where
      go : ⟨ ∃[ δ ] (δ ∈ˢ α) ⟩ ⊎ (⟨ ∃[ δ ] (δ ∈ˢ α) ⟩ → Empty.⊥) → Empty.⊥
      go (inl eδ) = PT.rec Empty.isProp⊥ (λ { (δ , δ∈α) →
        ∅-empty (b δ) (∈∈ₛ {a = b δ} {b = ∅} .fst
          (subst (λ w → ⟨ b δ ∈ˢ w ⟩) e (b-mono {α = α} {β = δ} δ∈α))) })
        eδ
      go (inr noδ) = Empty.rec (isLimit-not-zero α lim (ext-⊆ α⊆∅ ∅⊆α))
        where
        α⊆∅ : α ⊆ ∅
        α⊆∅ x x∈α = Empty.rec (noδ ∣ x , x∈α ∣₁)
        ∅⊆α : ∅ ⊆ α
        ∅⊆α x x∈∅ = Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst x∈∅))
    ns : ⟨ isSucc (b α) ⟩ → Empty.⊥
    ns (γ , _ , sucγ≡) = PT.rec Empty.isProp⊥ uStep (b-out α γ γ∈bα)
      where
      γ∈bα : ⟨ γ ∈ˢ b α ⟩
      γ∈bα = subst (λ w → ⟨ γ ∈ˢ w ⟩) sucγ≡ (self∈sucV γ)
      uStep : Σ[ δ ∈ S ] (⟨ δ ∈ˢ α ⟩ × ⟨ γ ∈ˢ +ω (b δ) ⟩) → Empty.⊥
      uStep (δ , δ∈α , γ∈+ωbδ) = ∈-irrefl (b α) bα∈bα
        where
        ordδ : IsOrd δ
        ordδ = limit-mem-ord α lim δ δ∈α
        sucδ∈α : ⟨ sucV δ ∈ˢ α ⟩
        sucδ∈α = limit-succ-mem α δ lim δ∈α
        bδ'⊆bα : b (sucV δ) ⊆ b α
        bδ'⊆bα x x∈bδ' = b-in α (sucV δ) x sucδ∈α (+ω-sup (b (sucV δ)) x x∈bδ')
        γ∈bδ' : ⟨ γ ∈ˢ b (sucV δ) ⟩
        γ∈bδ' = b-in (sucV δ) δ γ (self∈sucV δ) γ∈+ωbδ
        bα⊆bδ' : b α ⊆ b (sucV δ)
        bα⊆bδ' x x∈bα = suc-⊆ {A = b (sucV δ)} {x = γ}
          (b-ord (sucV δ) (suc-ord ordδ)) γ∈bδ' x
          (subst (λ w → ⟨ x ∈ˢ w ⟩) (sym sucγ≡) x∈bα)
        bδ'≡bα : b (sucV δ) ≡ b α
        bδ'≡bα = ext-⊆ bδ'⊆bα bα⊆bδ'
        bα∈bα : ⟨ b α ∈ˢ b α ⟩
        bα∈bα = subst (λ w → ⟨ w ∈ˢ b α ⟩) bδ'≡bα
          (b-mono {α = α} {β = sucV δ} sucδ∈α)

b-limit-nonzero : (α : S) → IsOrd α → ((α ≡ ∅) → Empty.⊥) → ⟨ isLimit (b α) ⟩
b-limit-nonzero α ordα nz = go (ord-case α ordα)
  where
  go : (α ≡ ∅) ⊎ (⟨ isSucc α ⟩ ⊎ ⟨ isLimit α ⟩) → ⟨ isLimit (b α) ⟩
  go (inl z) = Empty.rec (nz z)
  go (inr (inl (β , ordβ , eq))) =
    subst (λ w → ⟨ isLimit w ⟩) (sym (cong b (sym eq) ∙ b-suc β ordβ))
      (+ω-limit (b β) (b-ord β ordβ))
  go (inr (inr lim)) = limit-block-limit α lim
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The block map is a single-equation membership recursion whose three textbook
clauses are theorems: zero, successor (`b (sucV α) = +ω (b α)`), and limit
(the union of the earlier blocks). The bridge spends the four laws: the blocks
are ordinals, monotone in membership, every nonzero block is a limit, and the
finite successor iterations stay inside the next block. The classical content
is one comparison per ordinal-inclusion step, the successor-closure fact, and
one excluded middle for the nonemptiness of a limit block; everything else is
constructive.
<!--zh-->
块映射是单方程成员递归，其教科书三子句皆为定理：零、后继 (`b (sucV α) = +ω (b α)`)、极限 (更早诸块之并)。桥花费四条律：诸块是序数、隶属意义下单调、每个非零块是极限、有限后继迭代落在下一块之内。经典内容仅是每次序数包含一步一次比较、后继封闭事实，以及极限块非空时的一次排中律；其余皆构造。
<!--/-->

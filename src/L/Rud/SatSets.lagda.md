# Satisfaction sets

<!--en-->
The switch's missing direction is the one for **arbitrary** formulas. The
delivered limit switch carries a Δ₀ formula's definable set into the closure by
realizing the formula as a composite of rudimentary functions, and an unbounded
quantifier has no such composite. This chapter builds the classical replacement: for every formula
`φ` over the carrier of a transitive rudimentary-closed set `U`, the **satisfaction
set** `T φ`, the set of tuples from `U` at which `φ` holds, as a member of the
closure. Satisfaction stays external and only certifies; the sets themselves are
built from the sixteen basis operations alone.

The tuple convention is the delivered one: tuples nest to the right,
`⟨v₀, v₁, …⟩ = pr v₀ ⟨v₁, …⟩`, matching `F3`'s and `F4`'s insertion and append,
and matching de Bruijn binding, where the newly bound variable is the head of the
environment. Under that convention the existential is not `F6`'s domain but its
converse, the **range**, and the range is the one derived operation this chapter
adds: `F5 (F8 x (F6 x x))`, sealed at birth with its specification inside.
<!--zh-->
切换定理所缺的方向，是对**任意**公式的那一半。已交付的极限切换把 Δ₀ 公式的可定义集送进闭包，办法是把公式领悟为一个初步函数的复合；无界量词没有这样的复合。本章造出经典的替代品：对传递且对初步函数封闭的集合 `U`，其载体上的每个公式 `φ`，造出**满足集** `T φ`，即 `φ` 在其上成立的 `U` 元组之集，作为闭包的成员。满足关系留在外部，只作认证；集合本身仅由十六个基运算造出。

元组约定沿用已交付者：元组向右嵌套，`⟨v₀, v₁, …⟩ = pr v₀ ⟨v₁, …⟩`，与 `F3` 的插入、`F4` 的接续对齐，也与 de Bruijn 约束对齐，新约束的变量恰是环境的头。在该约定下，存在量词对应的不是 `F6` 的定义域而是它的逆，即**值域**，而值域正是本章新增的唯一派生运算：`F5 (F8 x (F6 x x))`，出生即封印，规格封在印内。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )

module L.Rud.SatSets {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; Term; con; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
  ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Rud.Ops {ℓ} using
  ( F0; F0-spec; F1; F1-spec; F2; F2-read; F2-write
  ; F3; F3-read; F3-write; F4; F4-read; F4-write; F5; F5-spec
  ; F6; F6-write; F7; F7-read; F7-write )
open import L.Rud.Images {ℓ} using ( F8; F8-spec; F10; F10-spec )
open import L.Rud.Step {ℓ} lem A using
  ( Op16; f0; f1; f2; f3; f4; f5; f6; f7; f8; f10; Fof
  ; Fof-f0; Fof-f1; Fof-f2; Fof-f3; Fof-f4; Fof-f5; Fof-f6; Fof-f7
  ; Fof-f8; Fof-f10; Jset; Jset-rud; Sset-trans; Sset-mem )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Data.Sigma using ( Σ≡Prop )
import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; _≡ₕ_; ∈-asFiber; extensionality; _⊆_; ∈∈ₛ; ∈ₛ⟪_⟫↪_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## Three derived operations

Three operations the basis does not name are used by every clause below, and each
is sealed at birth with its specification inside the seal, because each is a
consumer's composite of operations the trunk delivered transparent. `capOp`{.Agda}
is intersection as the double difference, the one spot where the algebra spends
excluded middle (the standing D-7 ruling). `cupOp`{.Agda} is binary union.
`ranOp`{.Agda} is the **range**, the converse of the domain: the classical
`ran x = ⋃ { x"{u} ∣ u ∈ dom x }`, which is `F5`, `F8`, `F6` and `F10` in one
line. The range is what the right-nested tuple convention costs, and it is the
whole cost.
<!--zh-->
## 三个派生运算

有三个基未曾命名的运算被下方每条子句使用，各自出生即封印、规格封在印内，因为各自都是消费者对主干以透明方式交付之运算的复合。`capOp`{.Agda} 是作为二重差的交，也是本代数花掉排中律的唯一一处 (D-7 裁定照旧)。`cupOp`{.Agda} 是二元并。`ranOp`{.Agda} 是**值域**，即定义域之逆：经典的 `ran x = ⋃ { x"{u} ∣ u ∈ dom x }`，一行之内用上 `F5`、`F8`、`F6` 与 `F10`。值域正是右嵌套元组约定的代价，而且是全部代价。
<!--/-->

```agda
dneV : (P : hProp (ℓ-suc ℓ)) → ((⟨ P ⟩ → Empty.⊥) → Empty.⊥) → ⟨ P ⟩
dneV P nn = go (lem P)
  where
  go : ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥) → ⟨ P ⟩
  go (inl p) = p
  go (inr np) = Empty.rec (nn np)

dif-in : (a b x : V ℓ) → ⟨ x ∈ˢ F1 a b ⟩
       → ⟨ x ∈ˢ a ⟩ × (⟨ x ∈ˢ b ⟩ → Empty.⊥)
dif-in a b x h = F1-spec a b x .fst h

dif-out : (a b x : V ℓ) → ⟨ x ∈ˢ a ⟩ → (⟨ x ∈ˢ b ⟩ → Empty.⊥)
        → ⟨ x ∈ˢ F1 a b ⟩
dif-out a b x p q = F1-spec a b x .snd (p , q)

prod-out : (a b u v : V ℓ) → ⟨ u ∈ˢ a ⟩ → ⟨ v ∈ˢ b ⟩ → ⟨ pr u v ∈ˢ F2 a b ⟩
prod-out a b u v hu hv = F2-write a b (pr u v) ∣ u , v , (hu , hv , refl) ∣₁

opaque
  -- perf: R-38: a consumer's composite of the delivered difference; sealed with its spec inside
  capOp : V ℓ → V ℓ → V ℓ
  capOp a b = F1 a (F1 a b)

  capOp-in : (a b x : V ℓ) → ⟨ x ∈ˢ capOp a b ⟩ → ⟨ x ∈ˢ a ⟩ × ⟨ x ∈ˢ b ⟩
  capOp-in a b x h = x∈a , dneV (x ∈ˢ b) nn
    where
    parts : ⟨ x ∈ˢ a ⟩ × (⟨ x ∈ˢ F1 a b ⟩ → Empty.⊥)
    parts = dif-in a (F1 a b) x h
    x∈a : ⟨ x ∈ˢ a ⟩
    x∈a = parts .fst
    nn : (⟨ x ∈ˢ b ⟩ → Empty.⊥) → Empty.⊥
    nn x∉b = parts .snd (dif-out a b x x∈a x∉b)

  capOp-out : (a b x : V ℓ) → ⟨ x ∈ˢ a ⟩ → ⟨ x ∈ˢ b ⟩ → ⟨ x ∈ˢ capOp a b ⟩
  capOp-out a b x x∈a x∈b = dif-out a (F1 a b) x x∈a no
    where
    no : ⟨ x ∈ˢ F1 a b ⟩ → Empty.⊥
    no k = dif-in a b x k .snd x∈b

opaque
  -- perf: R-38: F5 and F0 are delivered transparent; the alias is a birth site
  cupOp : V ℓ → V ℓ → V ℓ
  cupOp a b = F5 (F0 a b) (F0 a b)

  cupOp-in : (a b x : V ℓ) → ⟨ x ∈ˢ cupOp a b ⟩
           → ∥ ⟨ x ∈ˢ a ⟩ ⊎ ⟨ x ∈ˢ b ⟩ ∥₁
  cupOp-in a b x h = PT.rec squash₁ go (F5-spec (F0 a b) (F0 a b) x .fst h)
    where
    go : Σ[ v ∈ V ℓ ] (⟨ v ∈ˢ F0 a b ⟩ × ⟨ x ∈ˢ v ⟩)
       → ∥ ⟨ x ∈ˢ a ⟩ ⊎ ⟨ x ∈ˢ b ⟩ ∥₁
    go (v , v∈ , x∈v) = PT.rec squash₁ go' (F0-spec a b v .fst v∈)
      where
      go' : ⟨ v ≡ₕ a ⟩ ⊎ ⟨ v ≡ₕ b ⟩ → ∥ ⟨ x ∈ˢ a ⟩ ⊎ ⟨ x ∈ˢ b ⟩ ∥₁
      go' (inl q) = ∣ inl (subst (λ w → ⟨ x ∈ˢ w ⟩) q x∈v) ∣₁
      go' (inr q) = ∣ inr (subst (λ w → ⟨ x ∈ˢ w ⟩) q x∈v) ∣₁

  cupOp-outl : (a b x : V ℓ) → ⟨ x ∈ˢ a ⟩ → ⟨ x ∈ˢ cupOp a b ⟩
  cupOp-outl a b x h = F5-spec (F0 a b) (F0 a b) x .snd
    ∣ a , (F0-spec a b a .snd ∣ inl refl ∣₁ , h) ∣₁

  cupOp-outr : (a b x : V ℓ) → ⟨ x ∈ˢ b ⟩ → ⟨ x ∈ˢ cupOp a b ⟩
  cupOp-outr a b x h = F5-spec (F0 a b) (F0 a b) x .snd
    ∣ b , (F0-spec a b b .snd ∣ inr refl ∣₁ , h) ∣₁

opaque
  -- perf: R-38: F8 and F10 are delivered transparent; the range alias is a birth site
  ranOp : V ℓ → V ℓ
  ranOp x = F5 (F8 x (F6 x x)) (F8 x (F6 x x))

  ranOp-in : (x m : V ℓ) → ⟨ m ∈ˢ ranOp x ⟩
           → ∥ Σ[ u ∈ V ℓ ] ⟨ pr u m ∈ˢ x ⟩ ∥₁
  ranOp-in x m h =
    PT.rec squash₁ go (F5-spec (F8 x (F6 x x)) (F8 x (F6 x x)) m .fst h)
    where
    go : Σ[ v ∈ V ℓ ] (⟨ v ∈ˢ F8 x (F6 x x) ⟩ × ⟨ m ∈ˢ v ⟩)
       → ∥ Σ[ u ∈ V ℓ ] ⟨ pr u m ∈ˢ x ⟩ ∥₁
    go (v , v∈ , m∈v) = PT.rec squash₁ go' (subst ⟨_⟩ (F8-spec x (F6 x x) v) v∈)
      where
      go' : Σ[ k ∈ ⟪ F6 x x ⟫ ] ⟨ F10 x (⟪ F6 x x ⟫↪ k) ≡ₕ v ⟩
          → ∥ Σ[ u ∈ V ℓ ] ⟨ pr u m ∈ˢ x ⟩ ∥₁
      go' (k , q) = ∣ ⟪ F6 x x ⟫↪ k , inx ∣₁
        where
        m∈slice : ⟨ m ∈ˢ F10 x (⟪ F6 x x ⟫↪ k) ⟩
        m∈slice = subst (λ w → ⟨ m ∈ˢ w ⟩) (sym q) m∈v
        inx : ⟨ pr (⟪ F6 x x ⟫↪ k) m ∈ˢ x ⟩
        inx = subst ⟨_⟩ (F10-spec x (⟪ F6 x x ⟫↪ k) m) m∈slice

  ranOp-out : (x u m : V ℓ) → ⟨ pr u m ∈ˢ x ⟩ → ⟨ m ∈ˢ ranOp x ⟩
  ranOp-out x u m h = F5-spec (F8 x (F6 x x)) (F8 x (F6 x x)) m .snd
    ∣ F10 x (⟪ F6 x x ⟫↪ (fk .fst)) , (slice∈ , m∈slice) ∣₁
    where
    u∈dom : ⟨ u ∈ˢ F6 x x ⟩
    u∈dom = F6-write x x u ∣ u , m , (h , refl) ∣₁
    fk : Σ[ k ∈ ⟪ F6 x x ⟫ ] (⟪ F6 x x ⟫↪ k ≡ u)
    fk = ∈-asFiber {a = u} {b = F6 x x} u∈dom
    m∈slice : ⟨ m ∈ˢ F10 x (⟪ F6 x x ⟫↪ (fk .fst)) ⟩
    m∈slice = subst ⟨_⟩ (sym (F10-spec x (⟪ F6 x x ⟫↪ (fk .fst)) m))
      (subst (λ w → ⟨ pr w m ∈ˢ x ⟩) (sym (fk .snd)) h)
    slice∈ : ⟨ F10 x (⟪ F6 x x ⟫↪ (fk .fst)) ∈ˢ F8 x (F6 x x) ⟩
    slice∈ = subst ⟨_⟩ (sym (F8-spec x (F6 x x) (F10 x (⟪ F6 x x ⟫↪ (fk .fst)))))
      ∣ fk .fst , refl ∣₁
```

<!--en-->
## The closure interface

The whole construction runs over an abstract closure, in the shape the limit
switch's `Closure`{.Agda} module has: a predicate `InJ`, the sixteen-operation
closure fact, the transitivity of the closed set, and the level `U` itself as a
member. Nothing concrete is in scope, so nothing concrete unfolds.
<!--zh-->
## 闭包接口

整个构造在一个抽象闭包上运行，形状与极限切换的 `Closure`{.Agda} 模块相同：一个谓词 `InJ`、十六运算的封闭事实、闭集的传递性，以及层 `U` 自身作为成员。作用域内没有任何具体之物，故无一具体之物展开。
<!--/-->

```agda
module Sat (U : V ℓ)
           (Utrans : (x y : V ℓ) → ⟨ x ∈ˢ y ⟩ → ⟨ y ∈ˢ U ⟩ → ⟨ x ∈ˢ U ⟩)
           (InJ : V ℓ → Type (ℓ-suc ℓ))
           (Jtrans : (a b : V ℓ) → InJ b → ⟨ a ∈ˢ b ⟩ → InJ a)
           (Jrud : (i : Op16) (a b : V ℓ) → InJ a → InJ b → InJ (Fof i a b))
           (JU : InJ U)
           where

  open DefOf U using ( SM; _⊨ᵐ_; ⟦_⟧ᵐ; ι; defSet; defSet-mem; defSet⊆A )

  JF0 : (a b : V ℓ) → InJ a → InJ b → InJ (F0 a b)
  JF0 a b ha hb = subst InJ (Fof-f0 a b) (Jrud f0 a b ha hb)

  JF1 : (a b : V ℓ) → InJ a → InJ b → InJ (F1 a b)
  JF1 a b ha hb = subst InJ (Fof-f1 a b) (Jrud f1 a b ha hb)

  JF2 : (a b : V ℓ) → InJ a → InJ b → InJ (F2 a b)
  JF2 a b ha hb = subst InJ (Fof-f2 a b) (Jrud f2 a b ha hb)

  JF3 : (a b : V ℓ) → InJ a → InJ b → InJ (F3 a b)
  JF3 a b ha hb = subst InJ (Fof-f3 a b) (Jrud f3 a b ha hb)

  JF4 : (a b : V ℓ) → InJ a → InJ b → InJ (F4 a b)
  JF4 a b ha hb = subst InJ (Fof-f4 a b) (Jrud f4 a b ha hb)

  JF5 : (a b : V ℓ) → InJ a → InJ b → InJ (F5 a b)
  JF5 a b ha hb = subst InJ (Fof-f5 a b) (Jrud f5 a b ha hb)

  JF6 : (a b : V ℓ) → InJ a → InJ b → InJ (F6 a b)
  JF6 a b ha hb = subst InJ (Fof-f6 a b) (Jrud f6 a b ha hb)

  JF7 : (a b : V ℓ) → InJ a → InJ b → InJ (F7 a b)
  JF7 a b ha hb = subst InJ (Fof-f7 a b) (Jrud f7 a b ha hb)

  JF8 : (a b : V ℓ) → InJ a → InJ b → InJ (F8 a b)
  JF8 a b ha hb = subst InJ (Fof-f8 a b) (Jrud f8 a b ha hb)

  JF10 : (a b : V ℓ) → InJ a → InJ b → InJ (F10 a b)
  JF10 a b ha hb = subst InJ (Fof-f10 a b) (Jrud f10 a b ha hb)

  UmemInJ : (a : V ℓ) → ⟨ a ∈ˢ U ⟩ → InJ a
  UmemInJ a a∈U = Jtrans a U JU a∈U
```

<!--en-->
## Tuple spaces and the decode

An environment for a formula with `n + 1` free variables is a vector of `n + 1`
members of `U`; `Tup`{.Agda} codes it as a right-nested tuple, and `Us`{.Agda} is
the set of all such codes. The membership characterization of `Us`{.Agda} is
stated once, in both directions, and every clause below consumes it.

The **decode-uniqueness** lemma comes before any clause work: a tuple determines
its environment, so two decodes of one member are the same environment. Stated
once per arity by an induction on the arity, it removes the injectivity chase
from every clause that has to compare two decodes.
<!--zh-->
## 元组空间与解码

带 `n + 1` 个自由变量的公式，其环境是 `U` 的 `n + 1` 个成员组成的向量；`Tup`{.Agda} 把它编码为右嵌套元组，`Us`{.Agda} 则是全体此类编码之集。`Us`{.Agda} 的隶属刻画双向各陈述一次，下方每条子句都消费它。

**解码唯一性**引理排在一切子句工作之前：元组决定其环境，故一个成员的两次解码给出同一环境。它按元数归纳、每个元数只陈述一次，从此把单射性追踪从每条需要比较两次解码的子句中移除。
<!--/-->

```agda
  Us : ℕ → V ℓ
  Us zero = U
  Us (suc n) = F2 U (Us n)

  hUs : (n : ℕ) → InJ (Us n)
  hUs zero = JU
  hUs (suc n) = JF2 U (Us n) JU (hUs n)

  Tup : (n : ℕ) → Vec SM (suc n) → V ℓ
  Tup zero (v ∷ []) = v .fst
  Tup (suc n) (v ∷ δ) = pr (v .fst) (Tup n δ)

  Us-out : (n : ℕ) (δ : Vec SM (suc n)) → ⟨ Tup n δ ∈ˢ Us n ⟩
  Us-out zero (v ∷ []) = v .snd
  Us-out (suc n) (v ∷ δ) = F2-write U (Us n) (pr (v .fst) (Tup n δ))
    ∣ v .fst , Tup n δ , (v .snd , Us-out n δ , refl) ∣₁

  DecTup : (n : ℕ) → V ℓ → Type (ℓ-suc ℓ)
  DecTup n m = ∥ Σ[ δ ∈ Vec SM (suc n) ] (m ≡ Tup n δ) ∥₁

  Us-in : (n : ℕ) (m : V ℓ) → ⟨ m ∈ˢ Us n ⟩ → DecTup n m
  Us-in zero m h = ∣ ((m , h) ∷ []) , refl ∣₁
  Us-in (suc n) m h = PT.rec squash₁ go (F2-read U (Us n) m h)
    where
    go : Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ]
           (⟨ p ∈ˢ U ⟩ × ⟨ q ∈ˢ Us n ⟩ × ⟨ m ≡ₕ pr p q ⟩)
       → DecTup (suc n) m
    go (p , q , p∈ , q∈ , m≡) = PT.rec squash₁ go' (Us-in n q q∈)
      where
      go' : Σ[ δ ∈ Vec SM (suc n) ] (q ≡ Tup n δ) → DecTup (suc n) m
      go' (δ , q≡) = ∣ ((p , p∈) ∷ δ) , (m≡ ∙ cong (pr p) q≡) ∣₁

  Tup-inj : (n : ℕ) (δ ε : Vec SM (suc n)) → Tup n δ ≡ Tup n ε → δ ≡ ε
  Tup-inj zero (v ∷ []) (w ∷ []) p =
    cong (_∷ []) (Σ≡Prop (λ x → snd (x ∈ˢ U)) p)
  Tup-inj (suc n) (v ∷ δ) (w ∷ ε) p =
    cong₂ _∷_ (Σ≡Prop (λ x → snd (x ∈ˢ U)) (pr-inj p .fst))
              (Tup-inj n δ ε (pr-inj p .snd))

  Sat-cong : (n : ℕ) (φ : Formula ⟪ U ⟫ (suc n)) (δ ε : Vec SM (suc n))
           → Tup n δ ≡ Tup n ε → ⟨ ε ⊨ᵐ φ ⟩ → ⟨ δ ⊨ᵐ φ ⟩
  Sat-cong n φ δ ε p = subst (λ γ → ⟨ γ ⊨ᵐ φ ⟩) (sym (Tup-inj n δ ε p))
```

<!--en-->
## The three base relations on the level

Every atom of the object language is read off one of three relations on `U`:
membership `Mem`{.Agda}, its converse `Memᶜ`{.Agda}, and the diagonal
`Diag`{.Agda}. Membership is `F7` outright. The diagonal is where extensionality
enters: two members of `U` are equal exactly when neither has a member the other
lacks, and "has a member the other lacks" is a range of a triple set, hence
`ranOp`{.Agda}. The converse of membership then follows from the diagonal by the
same range step, and so does the self-membership slice the equal-index atom
needs.
<!--zh-->
## 层上的三个基关系

对象语言的每个原子都从 `U` 上的三个关系之一读出：隶属 `Mem`{.Agda}、其逆 `Memᶜ`{.Agda}，以及对角 `Diag`{.Agda}。隶属径直就是 `F7`。对角是外延性入场之处：`U` 的两个成员相等，恰当彼此都没有对方所缺的成员，而「有一个对方所缺的成员」是某个三元组集的值域，故用 `ranOp`{.Agda}。隶属之逆随后经同一步值域从对角得出，同下标原子所需的自隶属切片亦然。
<!--/-->

```agda
  opaque
    unfolding capOp
    J-cap : (a b : V ℓ) → InJ a → InJ b → InJ (capOp a b)
    J-cap a b ha hb = JF1 a (F1 a b) ha (JF1 a b ha hb)

  opaque
    unfolding cupOp
    J-cup : (a b : V ℓ) → InJ a → InJ b → InJ (cupOp a b)
    J-cup a b ha hb = JF5 (F0 a b) (F0 a b) h₀ h₀
      where
      h₀ : InJ (F0 a b)
      h₀ = JF0 a b ha hb

  opaque
    unfolding ranOp
    J-ran : (a : V ℓ) → InJ a → InJ (ranOp a)
    J-ran a ha = JF5 (F8 a (F6 a a)) (F8 a (F6 a a)) h₈ h₈
      where
      h₆ : InJ (F6 a a)
      h₆ = JF6 a a ha ha
      h₈ : InJ (F8 a (F6 a a))
      h₈ = JF8 a (F6 a a) ha h₆

  Emp : (n : ℕ) → V ℓ
  Emp n = F1 (Us n) (Us n)

  hEmp : (n : ℕ) → InJ (Emp n)
  hEmp n = JF1 (Us n) (Us n) (hUs n) (hUs n)

  Emp-elim : (n : ℕ) (m : V ℓ) → ⟨ m ∈ˢ Emp n ⟩ → Empty.⊥
  Emp-elim n m h = dif-in (Us n) (Us n) m h .snd (dif-in (Us n) (Us n) m h .fst)

  Us1 : V ℓ
  Us1 = Us 1

  Us2 : V ℓ
  Us2 = Us 2

  Mem : V ℓ
  Mem = F7 U U

  hMem : InJ Mem
  hMem = JF7 U U JU JU

  Mem-out : (a b : V ℓ) → ⟨ a ∈ˢ U ⟩ → ⟨ b ∈ˢ U ⟩ → ⟨ a ∈ˢ b ⟩
          → ⟨ pr a b ∈ˢ Mem ⟩
  Mem-out a b ha hb hab = F7-write U U (pr a b) ∣ a , b , (ha , hb , hab , refl) ∣₁

  Mem-read : (a b : V ℓ) → ⟨ pr a b ∈ˢ Mem ⟩
           → ⟨ (a ∈ˢ U) ⊓ (b ∈ˢ U) ⊓ (a ∈ˢ b) ⟩
  Mem-read a b h = PT.rec (snd ((a ∈ˢ U) ⊓ (b ∈ˢ U) ⊓ (a ∈ˢ b))) go
    (F7-read U U (pr a b) h)
    where
    go : Σ[ s ∈ V ℓ ] Σ[ t ∈ V ℓ ]
           (⟨ s ∈ˢ U ⟩ × ⟨ t ∈ˢ U ⟩ × ⟨ s ∈ˢ t ⟩ × ⟨ pr a b ≡ₕ pr s t ⟩)
       → ⟨ (a ∈ˢ U) ⊓ (b ∈ˢ U) ⊓ (a ∈ˢ b) ⟩
    go (s , t , hs , ht , s∈t , eq) = a∈U , b∈U , a∈b
      where
      a≡s : a ≡ s
      a≡s = pr-inj eq .fst
      b≡t : b ≡ t
      b≡t = pr-inj eq .snd
      a∈U : ⟨ a ∈ˢ U ⟩
      a∈U = subst (λ w → ⟨ w ∈ˢ U ⟩) (sym a≡s) hs
      b∈U : ⟨ b ∈ˢ U ⟩
      b∈U = subst (λ w → ⟨ w ∈ˢ U ⟩) (sym b≡t) ht
      a∈b : ⟨ a ∈ˢ b ⟩
      a∈b = subst (λ w → ⟨ a ∈ˢ w ⟩) (sym b≡t)
              (subst (λ w → ⟨ w ∈ˢ t ⟩) (sym a≡s) s∈t)

  In3L : V ℓ
  In3L = F4 U Mem

  In3R : V ℓ
  In3R = F3 U Mem

  hIn3L : InJ In3L
  hIn3L = JF4 U Mem JU hMem

  hIn3R : InJ In3R
  hIn3R = JF3 U Mem JU hMem

  In3L-out : (a b c : V ℓ) → ⟨ a ∈ˢ U ⟩ → ⟨ b ∈ˢ U ⟩ → ⟨ c ∈ˢ U ⟩ → ⟨ a ∈ˢ b ⟩
           → ⟨ pr a (pr b c) ∈ˢ In3L ⟩
  In3L-out a b c ha hb hc a∈b = F4-write U Mem (pr a (pr b c))
    ∣ a , b , c , (hc , Mem-out a b ha hb a∈b , refl) ∣₁

  In3R-out : (a b c : V ℓ) → ⟨ a ∈ˢ U ⟩ → ⟨ b ∈ˢ U ⟩ → ⟨ c ∈ˢ U ⟩ → ⟨ a ∈ˢ c ⟩
           → ⟨ pr a (pr b c) ∈ˢ In3R ⟩
  In3R-out a b c ha hb hc a∈c = F3-write U Mem (pr a (pr b c))
    ∣ a , b , c , (hb , Mem-out a c ha hc a∈c , refl) ∣₁

  In3L-read : (a b c : V ℓ) → ⟨ pr a (pr b c) ∈ˢ In3L ⟩
            → ⟨ (a ∈ˢ U) ⊓ (b ∈ˢ U) ⊓ (c ∈ˢ U) ⊓ (a ∈ˢ b) ⟩
  In3L-read a b c h =
    PT.rec (snd ((a ∈ˢ U) ⊓ (b ∈ˢ U) ⊓ (c ∈ˢ U) ⊓ (a ∈ˢ b))) go
      (F4-read U Mem (pr a (pr b c)) h)
    where
    go : Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ] Σ[ z ∈ V ℓ ]
           (⟨ z ∈ˢ U ⟩ × ⟨ pr u v ∈ˢ Mem ⟩
          × ⟨ pr a (pr b c) ≡ₕ pr u (pr v z) ⟩)
       → ⟨ (a ∈ˢ U) ⊓ (b ∈ˢ U) ⊓ (c ∈ˢ U) ⊓ (a ∈ˢ b) ⟩
    go (u , v , z , hz , huv , eq) =
      parts .fst , parts .snd .fst , c∈U , parts .snd .snd
      where
      a≡u : a ≡ u
      a≡u = pr-inj eq .fst
      b≡v : b ≡ v
      b≡v = pr-inj (pr-inj eq .snd) .fst
      c≡z : c ≡ z
      c≡z = pr-inj (pr-inj eq .snd) .snd
      huv' : ⟨ pr a b ∈ˢ Mem ⟩
      huv' = subst (λ w → ⟨ w ∈ˢ Mem ⟩) (sym (cong₂ pr a≡u b≡v)) huv
      parts : ⟨ (a ∈ˢ U) ⊓ (b ∈ˢ U) ⊓ (a ∈ˢ b) ⟩
      parts = Mem-read a b huv'
      c∈U : ⟨ c ∈ˢ U ⟩
      c∈U = subst (λ w → ⟨ w ∈ˢ U ⟩) (sym c≡z) hz

  In3R-read : (a b c : V ℓ) → ⟨ pr a (pr b c) ∈ˢ In3R ⟩
            → ⟨ (a ∈ˢ U) ⊓ (b ∈ˢ U) ⊓ (c ∈ˢ U) ⊓ (a ∈ˢ c) ⟩
  In3R-read a b c h =
    PT.rec (snd ((a ∈ˢ U) ⊓ (b ∈ˢ U) ⊓ (c ∈ˢ U) ⊓ (a ∈ˢ c))) go
      (F3-read U Mem (pr a (pr b c)) h)
    where
    go : Σ[ u ∈ V ℓ ] Σ[ z ∈ V ℓ ] Σ[ v ∈ V ℓ ]
           (⟨ z ∈ˢ U ⟩ × ⟨ pr u v ∈ˢ Mem ⟩
          × ⟨ pr a (pr b c) ≡ₕ pr u (pr z v) ⟩)
       → ⟨ (a ∈ˢ U) ⊓ (b ∈ˢ U) ⊓ (c ∈ˢ U) ⊓ (a ∈ˢ c) ⟩
    go (u , z , v , hz , huv , eq) =
      parts .fst , b∈U , parts .snd .fst , parts .snd .snd
      where
      a≡u : a ≡ u
      a≡u = pr-inj eq .fst
      b≡z : b ≡ z
      b≡z = pr-inj (pr-inj eq .snd) .fst
      c≡v : c ≡ v
      c≡v = pr-inj (pr-inj eq .snd) .snd
      huv' : ⟨ pr a c ∈ˢ Mem ⟩
      huv' = subst (λ w → ⟨ w ∈ˢ Mem ⟩) (sym (cong₂ pr a≡u c≡v)) huv
      parts : ⟨ (a ∈ˢ U) ⊓ (c ∈ˢ U) ⊓ (a ∈ˢ c) ⟩
      parts = Mem-read a c huv'
      b∈U : ⟨ b ∈ˢ U ⟩
      b∈U = subst (λ w → ⟨ w ∈ˢ U ⟩) (sym b≡z) hz
```

```agda
  Us1-read : (a b : V ℓ) → ⟨ pr a b ∈ˢ Us1 ⟩ → ⟨ (a ∈ˢ U) ⊓ (b ∈ˢ U) ⟩
  Us1-read a b h = PT.rec (snd ((a ∈ˢ U) ⊓ (b ∈ˢ U))) go (F2-read U U (pr a b) h)
    where
    go : Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ]
           (⟨ p ∈ˢ U ⟩ × ⟨ q ∈ˢ U ⟩ × ⟨ pr a b ≡ₕ pr p q ⟩)
       → ⟨ (a ∈ˢ U) ⊓ (b ∈ˢ U) ⟩
    go (p , q , hp , hq , eq) =
        subst (λ w → ⟨ w ∈ˢ U ⟩) (sym (pr-inj eq .fst)) hp
      , subst (λ w → ⟨ w ∈ˢ U ⟩) (sym (pr-inj eq .snd)) hq

  Dif3 : V ℓ
  Dif3 = capOp In3L (F1 Us2 In3R)

  Dif3' : V ℓ
  Dif3' = capOp In3R (F1 Us2 In3L)

  Dif2 : V ℓ
  Dif2 = ranOp Dif3

  Dif2' : V ℓ
  Dif2' = ranOp Dif3'

  hDif2 : InJ Dif2
  hDif2 = J-ran Dif3
    (J-cap In3L (F1 Us2 In3R) hIn3L (JF1 Us2 In3R (hUs 2) hIn3R))

  hDif2' : InJ Dif2'
  hDif2' = J-ran Dif3'
    (J-cap In3R (F1 Us2 In3L) hIn3R (JF1 Us2 In3L (hUs 2) hIn3L))

  Dif2-out : (w b c : V ℓ) → ⟨ w ∈ˢ U ⟩ → ⟨ b ∈ˢ U ⟩ → ⟨ c ∈ˢ U ⟩
           → ⟨ w ∈ˢ b ⟩ → (⟨ w ∈ˢ c ⟩ → Empty.⊥) → ⟨ pr b c ∈ˢ Dif2 ⟩
  Dif2-out w b c hw hb hc w∈b w∉c =
    ranOp-out Dif3 w (pr b c)
      (capOp-out In3L (F1 Us2 In3R) (pr w (pr b c))
        (In3L-out w b c hw hb hc w∈b)
        (dif-out Us2 In3R (pr w (pr b c))
          (Us-out 2 ((w , hw) ∷ (b , hb) ∷ (c , hc) ∷ []))
          (λ k → w∉c (In3R-read w b c k .snd .snd .snd))))

  Dif2'-out : (w b c : V ℓ) → ⟨ w ∈ˢ U ⟩ → ⟨ b ∈ˢ U ⟩ → ⟨ c ∈ˢ U ⟩
            → ⟨ w ∈ˢ c ⟩ → (⟨ w ∈ˢ b ⟩ → Empty.⊥) → ⟨ pr b c ∈ˢ Dif2' ⟩
  Dif2'-out w b c hw hb hc w∈c w∉b =
    ranOp-out Dif3' w (pr b c)
      (capOp-out In3R (F1 Us2 In3L) (pr w (pr b c))
        (In3R-out w b c hw hb hc w∈c)
        (dif-out Us2 In3L (pr w (pr b c))
          (Us-out 2 ((w , hw) ∷ (b , hb) ∷ (c , hc) ∷ []))
          (λ k → w∉b (In3L-read w b c k .snd .snd .snd))))

  Dif2-in : (b c : V ℓ) → ⟨ pr b c ∈ˢ Dif2 ⟩
          → ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ˢ b ⟩ × (⟨ w ∈ˢ c ⟩ → Empty.⊥)) ∥₁
  Dif2-in b c h = PT.rec squash₁ go (ranOp-in Dif3 (pr b c) h)
    where
    go : Σ[ u ∈ V ℓ ] ⟨ pr u (pr b c) ∈ˢ Dif3 ⟩
       → ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ˢ b ⟩ × (⟨ w ∈ˢ c ⟩ → Empty.⊥)) ∥₁
    go (u , hu) = ∣ u , (rd .snd .snd .snd , notin) ∣₁
      where
      parts : ⟨ pr u (pr b c) ∈ˢ In3L ⟩
            × (⟨ pr u (pr b c) ∈ˢ In3R ⟩ → Empty.⊥)
      parts = capOp-in In3L (F1 Us2 In3R) (pr u (pr b c)) hu .fst
            , λ k → dif-in Us2 In3R (pr u (pr b c))
                      (capOp-in In3L (F1 Us2 In3R) (pr u (pr b c)) hu .snd) .snd k
      rd : ⟨ (u ∈ˢ U) ⊓ (b ∈ˢ U) ⊓ (c ∈ˢ U) ⊓ (u ∈ˢ b) ⟩
      rd = In3L-read u b c (parts .fst)
      notin : ⟨ u ∈ˢ c ⟩ → Empty.⊥
      notin k = parts .snd
        (In3R-out u b c (rd .fst) (rd .snd .fst) (rd .snd .snd .fst) k)

  Dif2'-in : (b c : V ℓ) → ⟨ pr b c ∈ˢ Dif2' ⟩
           → ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ˢ c ⟩ × (⟨ w ∈ˢ b ⟩ → Empty.⊥)) ∥₁
  Dif2'-in b c h = PT.rec squash₁ go (ranOp-in Dif3' (pr b c) h)
    where
    go : Σ[ u ∈ V ℓ ] ⟨ pr u (pr b c) ∈ˢ Dif3' ⟩
       → ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ˢ c ⟩ × (⟨ w ∈ˢ b ⟩ → Empty.⊥)) ∥₁
    go (u , hu) = ∣ u , (rd .snd .snd .snd , notin) ∣₁
      where
      parts : ⟨ pr u (pr b c) ∈ˢ In3R ⟩
            × (⟨ pr u (pr b c) ∈ˢ In3L ⟩ → Empty.⊥)
      parts = capOp-in In3R (F1 Us2 In3L) (pr u (pr b c)) hu .fst
            , λ k → dif-in Us2 In3L (pr u (pr b c))
                      (capOp-in In3R (F1 Us2 In3L) (pr u (pr b c)) hu .snd) .snd k
      rd : ⟨ (u ∈ˢ U) ⊓ (b ∈ˢ U) ⊓ (c ∈ˢ U) ⊓ (u ∈ˢ c) ⟩
      rd = In3R-read u b c (parts .fst)
      notin : ⟨ u ∈ˢ b ⟩ → Empty.⊥
      notin k = parts .snd
        (In3L-out u b c (rd .fst) (rd .snd .fst) (rd .snd .snd .fst) k)

  Diag : V ℓ
  Diag = F1 Us1 (cupOp Dif2 Dif2')

  hDiag : InJ Diag
  hDiag = JF1 Us1 (cupOp Dif2 Dif2') (hUs 1) (J-cup Dif2 Dif2' hDif2 hDif2')

  Diag-out : (a b : V ℓ) → ⟨ a ∈ˢ U ⟩ → ⟨ b ∈ˢ U ⟩ → a ≡ b → ⟨ pr a b ∈ˢ Diag ⟩
  Diag-out a b ha hb a≡b = dif-out Us1 (cupOp Dif2 Dif2') (pr a b)
    (Us-out 1 ((a , ha) ∷ (b , hb) ∷ [])) no
    where
    no : ⟨ pr a b ∈ˢ cupOp Dif2 Dif2' ⟩ → Empty.⊥
    no k = PT.rec Empty.isProp⊥ br (cupOp-in Dif2 Dif2' (pr a b) k)
      where
      br : ⟨ pr a b ∈ˢ Dif2 ⟩ ⊎ ⟨ pr a b ∈ˢ Dif2' ⟩ → Empty.⊥
      br (inl h) = PT.rec Empty.isProp⊥ gl (Dif2-in a b h)
        where
        gl : Σ[ w ∈ V ℓ ] (⟨ w ∈ˢ a ⟩ × (⟨ w ∈ˢ b ⟩ → Empty.⊥)) → Empty.⊥
        gl (w , w∈a , w∉b) = w∉b (subst (λ t → ⟨ w ∈ˢ t ⟩) a≡b w∈a)
      br (inr h) = PT.rec Empty.isProp⊥ gr (Dif2'-in a b h)
        where
        gr : Σ[ w ∈ V ℓ ] (⟨ w ∈ˢ b ⟩ × (⟨ w ∈ˢ a ⟩ → Empty.⊥)) → Empty.⊥
        gr (w , w∈b , w∉a) = w∉a (subst (λ t → ⟨ w ∈ˢ t ⟩) (sym a≡b) w∈b)

  Diag-read : (a b : V ℓ) → ⟨ pr a b ∈ˢ Diag ⟩
            → ⟨ (a ∈ˢ U) ⊓ (b ∈ˢ U) ⊓ (a ≡ₕ b) ⟩
  Diag-read a b h = a∈U , b∈U , extensionality a b (sub₁ , sub₂)
    where
    parts : ⟨ pr a b ∈ˢ Us1 ⟩ × (⟨ pr a b ∈ˢ cupOp Dif2 Dif2' ⟩ → Empty.⊥)
    parts = dif-in Us1 (cupOp Dif2 Dif2') (pr a b) h
    ab : ⟨ (a ∈ˢ U) ⊓ (b ∈ˢ U) ⟩
    ab = Us1-read a b (parts .fst)
    a∈U : ⟨ a ∈ˢ U ⟩
    a∈U = ab .fst
    b∈U : ⟨ b ∈ˢ U ⟩
    b∈U = ab .snd
    sub₁ : ⟨ a ⊆ b ⟩
    sub₁ w w∈ₛa = ∈∈ₛ {a = w} {b = b} .fst (dneV (w ∈ˢ b) nn)
      where
      w∈a : ⟨ w ∈ˢ a ⟩
      w∈a = ∈∈ₛ {a = w} {b = a} .snd w∈ₛa
      nn : (⟨ w ∈ˢ b ⟩ → Empty.⊥) → Empty.⊥
      nn w∉b = parts .snd (cupOp-outl Dif2 Dif2' (pr a b)
        (Dif2-out w a b (Utrans w a w∈a a∈U) a∈U b∈U w∈a w∉b))
    sub₂ : ⟨ b ⊆ a ⟩
    sub₂ w w∈ₛb = ∈∈ₛ {a = w} {b = a} .fst (dneV (w ∈ˢ a) nn)
      where
      w∈b : ⟨ w ∈ˢ b ⟩
      w∈b = ∈∈ₛ {a = w} {b = b} .snd w∈ₛb
      nn : (⟨ w ∈ˢ a ⟩ → Empty.⊥) → Empty.⊥
      nn w∉a = parts .snd (cupOp-outr Dif2 Dif2' (pr a b)
        (Dif2'-out w a b (Utrans w b w∈b b∈U) a∈U b∈U w∈b w∉a))
```

```agda
  Eq3R : V ℓ
  Eq3R = F3 U Diag

  hEq3R : InJ Eq3R
  hEq3R = JF3 U Diag JU hDiag

  Eq3R-out : (a b c : V ℓ) → ⟨ a ∈ˢ U ⟩ → ⟨ b ∈ˢ U ⟩ → ⟨ c ∈ˢ U ⟩ → a ≡ c
           → ⟨ pr a (pr b c) ∈ˢ Eq3R ⟩
  Eq3R-out a b c ha hb hc a≡c = F3-write U Diag (pr a (pr b c))
    ∣ a , b , c , (hb , Diag-out a c ha hc a≡c , refl) ∣₁

  Eq3R-read : (a b c : V ℓ) → ⟨ pr a (pr b c) ∈ˢ Eq3R ⟩
            → ⟨ (a ∈ˢ U) ⊓ (b ∈ˢ U) ⊓ (c ∈ˢ U) ⊓ (a ≡ₕ c) ⟩
  Eq3R-read a b c h =
    PT.rec (snd ((a ∈ˢ U) ⊓ (b ∈ˢ U) ⊓ (c ∈ˢ U) ⊓ (a ≡ₕ c))) go
      (F3-read U Diag (pr a (pr b c)) h)
    where
    go : Σ[ u ∈ V ℓ ] Σ[ z ∈ V ℓ ] Σ[ v ∈ V ℓ ]
           (⟨ z ∈ˢ U ⟩ × ⟨ pr u v ∈ˢ Diag ⟩
          × ⟨ pr a (pr b c) ≡ₕ pr u (pr z v) ⟩)
       → ⟨ (a ∈ˢ U) ⊓ (b ∈ˢ U) ⊓ (c ∈ˢ U) ⊓ (a ≡ₕ c) ⟩
    go (u , z , v , hz , huv , eq) =
      parts .fst , b∈U , parts .snd .fst , parts .snd .snd
      where
      a≡u : a ≡ u
      a≡u = pr-inj eq .fst
      b≡z : b ≡ z
      b≡z = pr-inj (pr-inj eq .snd) .fst
      c≡v : c ≡ v
      c≡v = pr-inj (pr-inj eq .snd) .snd
      huv' : ⟨ pr a c ∈ˢ Diag ⟩
      huv' = subst (λ w → ⟨ w ∈ˢ Diag ⟩) (sym (cong₂ pr a≡u c≡v)) huv
      parts : ⟨ (a ∈ˢ U) ⊓ (c ∈ˢ U) ⊓ (a ≡ₕ c) ⟩
      parts = Diag-read a c huv'
      b∈U : ⟨ b ∈ˢ U ⟩
      b∈U = subst (λ w → ⟨ w ∈ˢ U ⟩) (sym b≡z) hz

  Memᶜ : V ℓ
  Memᶜ = ranOp (capOp In3L Eq3R)

  hMemᶜ : InJ Memᶜ
  hMemᶜ = J-ran (capOp In3L Eq3R) (J-cap In3L Eq3R hIn3L hEq3R)

  Memᶜ-out : (a b : V ℓ) → ⟨ a ∈ˢ U ⟩ → ⟨ b ∈ˢ U ⟩ → ⟨ b ∈ˢ a ⟩
           → ⟨ pr a b ∈ˢ Memᶜ ⟩
  Memᶜ-out a b ha hb b∈a = ranOp-out (capOp In3L Eq3R) b (pr a b)
    (capOp-out In3L Eq3R (pr b (pr a b))
      (In3L-out b a b hb ha hb b∈a)
      (Eq3R-out b a b hb ha hb refl))

  Memᶜ-read : (a b : V ℓ) → ⟨ pr a b ∈ˢ Memᶜ ⟩
            → ⟨ (a ∈ˢ U) ⊓ (b ∈ˢ U) ⊓ (b ∈ˢ a) ⟩
  Memᶜ-read a b h =
    PT.rec (snd ((a ∈ˢ U) ⊓ (b ∈ˢ U) ⊓ (b ∈ˢ a))) go
      (ranOp-in (capOp In3L Eq3R) (pr a b) h)
    where
    go : Σ[ u ∈ V ℓ ] ⟨ pr u (pr a b) ∈ˢ capOp In3L Eq3R ⟩
       → ⟨ (a ∈ˢ U) ⊓ (b ∈ˢ U) ⊓ (b ∈ˢ a) ⟩
    go (u , hu) = rdL .snd .fst , rdL .snd .snd .fst , b∈a
      where
      parts : ⟨ pr u (pr a b) ∈ˢ In3L ⟩ × ⟨ pr u (pr a b) ∈ˢ Eq3R ⟩
      parts = capOp-in In3L Eq3R (pr u (pr a b)) hu
      rdL : ⟨ (u ∈ˢ U) ⊓ (a ∈ˢ U) ⊓ (b ∈ˢ U) ⊓ (u ∈ˢ a) ⟩
      rdL = In3L-read u a b (parts .fst)
      rdR : ⟨ (u ∈ˢ U) ⊓ (a ∈ˢ U) ⊓ (b ∈ˢ U) ⊓ (u ≡ₕ b) ⟩
      rdR = Eq3R-read u a b (parts .snd)
      b∈a : ⟨ b ∈ˢ a ⟩
      b∈a = subst (λ w → ⟨ w ∈ˢ a ⟩) (rdR .snd .snd .snd) (rdL .snd .snd .snd)

  Slf : V ℓ
  Slf = ranOp (capOp Mem Diag)

  hSlf : InJ Slf
  hSlf = J-ran (capOp Mem Diag) (J-cap Mem Diag hMem hDiag)

  Slf-out : (a : V ℓ) → ⟨ a ∈ˢ U ⟩ → ⟨ a ∈ˢ a ⟩ → ⟨ a ∈ˢ Slf ⟩
  Slf-out a ha a∈a = ranOp-out (capOp Mem Diag) a a
    (capOp-out Mem Diag (pr a a) (Mem-out a a ha ha a∈a) (Diag-out a a ha ha refl))

  Slf-read : (a : V ℓ) → ⟨ a ∈ˢ Slf ⟩ → ⟨ (a ∈ˢ U) ⊓ (a ∈ˢ a) ⟩
  Slf-read a h = PT.rec (snd ((a ∈ˢ U) ⊓ (a ∈ˢ a))) go
    (ranOp-in (capOp Mem Diag) a h)
    where
    go : Σ[ u ∈ V ℓ ] ⟨ pr u a ∈ˢ capOp Mem Diag ⟩ → ⟨ (a ∈ˢ U) ⊓ (a ∈ˢ a) ⟩
    go (u , hu) = rdM .snd .fst , a∈a
      where
      parts : ⟨ pr u a ∈ˢ Mem ⟩ × ⟨ pr u a ∈ˢ Diag ⟩
      parts = capOp-in Mem Diag (pr u a) hu
      rdM : ⟨ (u ∈ˢ U) ⊓ (a ∈ˢ U) ⊓ (u ∈ˢ a) ⟩
      rdM = Mem-read u a (parts .fst)
      rdD : ⟨ (u ∈ˢ U) ⊓ (a ∈ˢ U) ⊓ (u ≡ₕ a) ⟩
      rdD = Diag-read u a (parts .snd)
      a∈a : ⟨ a ∈ˢ a ⟩
      a∈a = subst (λ w → ⟨ w ∈ˢ a ⟩) (rdD .snd .snd) (rdM .snd .snd)

  opaque
    -- perf: R-38: F10 is delivered transparent; the slice alias is a birth site
    Up : V ℓ → V ℓ
    Up c = F10 Mem c

    Up-read : (c x : V ℓ) → ⟨ x ∈ˢ Up c ⟩ → ⟨ (c ∈ˢ U) ⊓ (x ∈ˢ U) ⊓ (c ∈ˢ x) ⟩
    Up-read c x h = Mem-read c x (subst ⟨_⟩ (F10-spec Mem c x) h)

    Up-out : (c x : V ℓ) → ⟨ c ∈ˢ U ⟩ → ⟨ x ∈ˢ U ⟩ → ⟨ c ∈ˢ x ⟩ → ⟨ x ∈ˢ Up c ⟩
    Up-out c x hc hx h = subst ⟨_⟩ (sym (F10-spec Mem c x)) (Mem-out c x hc hx h)

    J-Up : (c : V ℓ) → InJ c → InJ (Up c)
    J-Up c hc = JF10 Mem c hMem hc
```

<!--en-->
## The coordinate families

An atom of the object language relates two coordinates of the tuple. Rather than
permute coordinates, the construction recurses on the arity: the head of a tuple
is its de Bruijn variable zero, so an atom whose two variables both look past the
head is a cylinder `F2 U _` over the same atom one arity down, an atom relating
the head to a later coordinate is an `F3`-insertion over the same atom one arity
down, and the base cases sit at the three relations above. `F4` is the append
that starts the family, and `F3` is the insertion that walks it up.
<!--zh-->
## 坐标族

对象语言的原子关联元组的两个坐标。构造不去置换坐标，而是对元数递归：元组的头就是它的 de Bruijn 零号变量，于是两个变量都越过头的原子，是同一原子降一元数后的柱 `F2 U _`；把头与后面某坐标关联的原子，是同一原子降一元数后的 `F3` 插入；基情形则落在上面那三个关系上。`F4` 是启动该族的接续，`F3` 是把它逐级抬升的插入。
<!--/-->

```agda
  module Coord (R : V ℓ) (hR : InJ R)
               (Rel : V ℓ → V ℓ → hProp (ℓ-suc ℓ))
               (R-in : (m : V ℓ) → ⟨ m ∈ˢ R ⟩
                     → ∥ Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
                          (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × ⟨ Rel a b ⟩
                         × ⟨ m ≡ₕ pr a b ⟩) ∥₁)
               (R-out : (a b : V ℓ) → ⟨ a ∈ˢ U ⟩ → ⟨ b ∈ˢ U ⟩ → ⟨ Rel a b ⟩
                      → ⟨ pr a b ∈ˢ R ⟩)
               where

    R-read : (a b : V ℓ) → ⟨ pr a b ∈ˢ R ⟩
           → ⟨ (a ∈ˢ U) ⊓ (b ∈ˢ U) ⊓ Rel a b ⟩
    R-read a b h = PT.rec (snd ((a ∈ˢ U) ⊓ (b ∈ˢ U) ⊓ Rel a b)) go (R-in (pr a b) h)
      where
      go : Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ]
             (⟨ p ∈ˢ U ⟩ × ⟨ q ∈ˢ U ⟩ × ⟨ Rel p q ⟩ × ⟨ pr a b ≡ₕ pr p q ⟩)
         → ⟨ (a ∈ˢ U) ⊓ (b ∈ˢ U) ⊓ Rel a b ⟩
      go (p , q , hp , hq , rel , eq) =
          subst (λ w → ⟨ w ∈ˢ U ⟩) (sym a≡p) hp
        , subst (λ w → ⟨ w ∈ˢ U ⟩) (sym b≡q) hq
        , subst (λ w → ⟨ Rel a w ⟩) (sym b≡q) (subst (λ w → ⟨ Rel w q ⟩) (sym a≡p) rel)
        where
        a≡p : a ≡ p
        a≡p = pr-inj eq .fst
        b≡q : b ≡ q
        b≡q = pr-inj eq .snd

    LR : (n : ℕ) (j : Fin (suc n)) → V ℓ
    LR zero zero = R
    LR (suc n) zero = F4 (Us n) R
    LR (suc n) (suc j) = F3 U (LR n j)

    hLR : (n : ℕ) (j : Fin (suc n)) → InJ (LR n j)
    hLR zero zero = hR
    hLR (suc n) zero = JF4 (Us n) R (hUs n) hR
    hLR (suc n) (suc j) = JF3 U (LR n j) JU (hLR n j)

    LR-out : (n : ℕ) (j : Fin (suc n)) (v : SM) (δ : Vec SM (suc n))
           → ⟨ Rel (v .fst) (lookup j δ .fst) ⟩
           → ⟨ pr (v .fst) (Tup n δ) ∈ˢ LR n j ⟩
    LR-out zero zero v (w ∷ []) rel = R-out (v .fst) (w .fst) (v .snd) (w .snd) rel
    LR-out (suc n) zero v (w ∷ δ) rel =
      F4-write (Us n) R (pr (v .fst) (pr (w .fst) (Tup n δ)))
        ∣ v .fst , w .fst , Tup n δ
        , (Us-out n δ , R-out (v .fst) (w .fst) (v .snd) (w .snd) rel , refl) ∣₁
    LR-out (suc n) (suc j) v (w ∷ δ) rel =
      F3-write U (LR n j) (pr (v .fst) (pr (w .fst) (Tup n δ)))
        ∣ v .fst , w .fst , Tup n δ
        , (w .snd , LR-out n j v δ rel , refl) ∣₁

    LRDec : (n : ℕ) (j : Fin (suc n)) → V ℓ → Type (ℓ-suc ℓ)
    LRDec n j m = ∥ Σ[ v ∈ SM ] Σ[ δ ∈ Vec SM (suc n) ]
                     (⟨ Rel (v .fst) (lookup j δ .fst) ⟩
                    × (m ≡ pr (v .fst) (Tup n δ))) ∥₁

    LR-in : (n : ℕ) (j : Fin (suc n)) (m : V ℓ) → ⟨ m ∈ˢ LR n j ⟩ → LRDec n j m
    LR-in zero zero m h = PT.rec squash₁ go (R-in m h)
      where
      go : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
             (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × ⟨ Rel a b ⟩ × ⟨ m ≡ₕ pr a b ⟩)
         → LRDec zero zero m
      go (a , b , ha , hb , rel , m≡) = ∣ (a , ha) , ((b , hb) ∷ []) , (rel , m≡) ∣₁
    LR-in (suc n) zero m h = PT.rec squash₁ go (F4-read (Us n) R m h)
      where
      go : Σ[ u ∈ V ℓ ] Σ[ w ∈ V ℓ ] Σ[ z ∈ V ℓ ]
             (⟨ z ∈ˢ Us n ⟩ × ⟨ pr u w ∈ˢ R ⟩ × ⟨ m ≡ₕ pr u (pr w z) ⟩)
         → LRDec (suc n) zero m
      go (u , w , z , hz , huw , m≡) = PT.rec squash₁ go' (Us-in n z hz)
        where
        rd : ⟨ (u ∈ˢ U) ⊓ (w ∈ˢ U) ⊓ Rel u w ⟩
        rd = R-read u w huw
        go' : Σ[ δ ∈ Vec SM (suc n) ] (z ≡ Tup n δ) → LRDec (suc n) zero m
        go' (δ , z≡) = ∣ (u , rd .fst) , ((w , rd .snd .fst) ∷ δ)
                       , (rd .snd .snd , m≡ ∙ cong (λ t → pr u (pr w t)) z≡) ∣₁
    LR-in (suc n) (suc j) m h = PT.rec squash₁ go (F3-read U (LR n j) m h)
      where
      go : Σ[ u ∈ V ℓ ] Σ[ z ∈ V ℓ ] Σ[ w ∈ V ℓ ]
             (⟨ z ∈ˢ U ⟩ × ⟨ pr u w ∈ˢ LR n j ⟩ × ⟨ m ≡ₕ pr u (pr z w) ⟩)
         → LRDec (suc n) (suc j) m
      go (u , z , w , hz , huw , m≡) = PT.rec squash₁ go' (LR-in n j (pr u w) huw)
        where
        go' : Σ[ v ∈ SM ] Σ[ δ ∈ Vec SM (suc n) ]
                (⟨ Rel (v .fst) (lookup j δ .fst) ⟩
               × (pr u w ≡ pr (v .fst) (Tup n δ)))
            → LRDec (suc n) (suc j) m
        go' (v , δ , rel , eq) = ∣ v , ((z , hz) ∷ δ) , (rel , path) ∣₁
          where
          path : m ≡ pr (v .fst) (pr z (Tup n δ))
          path = m≡ ∙ cong₂ (λ s t → pr s (pr z t)) (pr-inj eq .fst) (pr-inj eq .snd)
```

```agda
  Diag-in : (m : V ℓ) → ⟨ m ∈ˢ Diag ⟩
          → ∥ Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
               (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × ⟨ a ≡ₕ b ⟩ × ⟨ m ≡ₕ pr a b ⟩) ∥₁
  Diag-in m h = PT.rec squash₁ go
    (F2-read U U m (dif-in Us1 (cupOp Dif2 Dif2') m h .fst))
    where
    go : Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ]
           (⟨ p ∈ˢ U ⟩ × ⟨ q ∈ˢ U ⟩ × ⟨ m ≡ₕ pr p q ⟩)
       → ∥ Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
            (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × ⟨ a ≡ₕ b ⟩ × ⟨ m ≡ₕ pr a b ⟩) ∥₁
    go (p , q , hp , hq , m≡) =
      ∣ p , q , (hp , hq , Diag-read p q pq∈ .snd .snd , m≡) ∣₁
      where
      pq∈ : ⟨ pr p q ∈ˢ Diag ⟩
      pq∈ = subst (λ w → ⟨ w ∈ˢ Diag ⟩) m≡ h

  Diagᶜ-in : (m : V ℓ) → ⟨ m ∈ˢ Diag ⟩
           → ∥ Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
                (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × ⟨ b ≡ₕ a ⟩ × ⟨ m ≡ₕ pr a b ⟩) ∥₁
  Diagᶜ-in m h = PT.map
    (λ { (a , b , ha , hb , eq , m≡) → a , b , (ha , hb , sym eq , m≡) })
    (Diag-in m h)

  Diagᶜ-out : (a b : V ℓ) → ⟨ a ∈ˢ U ⟩ → ⟨ b ∈ˢ U ⟩ → b ≡ a → ⟨ pr a b ∈ˢ Diag ⟩
  Diagᶜ-out a b ha hb eq = Diag-out a b ha hb (sym eq)

  Memᶜ-in : (m : V ℓ) → ⟨ m ∈ˢ Memᶜ ⟩
          → ∥ Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
               (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × ⟨ b ∈ˢ a ⟩ × ⟨ m ≡ₕ pr a b ⟩) ∥₁
  Memᶜ-in m h = PT.rec squash₁ go (ranOp-in (capOp In3L Eq3R) m h)
    where
    go : Σ[ u ∈ V ℓ ] ⟨ pr u m ∈ˢ capOp In3L Eq3R ⟩
       → ∥ Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
            (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × ⟨ b ∈ˢ a ⟩ × ⟨ m ≡ₕ pr a b ⟩) ∥₁
    go (u , hu) = PT.rec squash₁ go'
      (F4-read U Mem (pr u m) (capOp-in In3L Eq3R (pr u m) hu .fst))
      where
      go' : Σ[ p ∈ V ℓ ] Σ[ w ∈ V ℓ ] Σ[ z ∈ V ℓ ]
              (⟨ z ∈ˢ U ⟩ × ⟨ pr p w ∈ˢ Mem ⟩ × ⟨ pr u m ≡ₕ pr p (pr w z) ⟩)
          → ∥ Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
               (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × ⟨ b ∈ˢ a ⟩ × ⟨ m ≡ₕ pr a b ⟩) ∥₁
      go' (p , w , z , hz , hpw , eq) =
        ∣ w , z , (rd .fst , rd .snd .fst , rd .snd .snd , m≡) ∣₁
        where
        m≡ : m ≡ pr w z
        m≡ = pr-inj eq .snd
        rd : ⟨ (w ∈ˢ U) ⊓ (z ∈ˢ U) ⊓ (z ∈ˢ w) ⟩
        rd = Memᶜ-read w z (subst (λ t → ⟨ t ∈ˢ Memᶜ ⟩) m≡ h)

  module Atoms (Rel : V ℓ → V ℓ → hProp (ℓ-suc ℓ))
               (R Rc D : V ℓ) (hR : InJ R) (hRc : InJ Rc) (hD : InJ D)
               (R-in : (m : V ℓ) → ⟨ m ∈ˢ R ⟩
                     → ∥ Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
                          (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × ⟨ Rel a b ⟩
                         × ⟨ m ≡ₕ pr a b ⟩) ∥₁)
               (R-out : (a b : V ℓ) → ⟨ a ∈ˢ U ⟩ → ⟨ b ∈ˢ U ⟩ → ⟨ Rel a b ⟩
                      → ⟨ pr a b ∈ˢ R ⟩)
               (Rc-in : (m : V ℓ) → ⟨ m ∈ˢ Rc ⟩
                      → ∥ Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
                           (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × ⟨ Rel b a ⟩
                          × ⟨ m ≡ₕ pr a b ⟩) ∥₁)
               (Rc-out : (a b : V ℓ) → ⟨ a ∈ˢ U ⟩ → ⟨ b ∈ˢ U ⟩ → ⟨ Rel b a ⟩
                       → ⟨ pr a b ∈ˢ Rc ⟩)
               (D-read : (v : V ℓ) → ⟨ v ∈ˢ D ⟩ → ⟨ (v ∈ˢ U) ⊓ Rel v v ⟩)
               (D-out : (v : V ℓ) → ⟨ v ∈ˢ U ⟩ → ⟨ Rel v v ⟩ → ⟨ v ∈ˢ D ⟩)
               where

    module CR = Coord R hR Rel R-in R-out
    module CC = Coord Rc hRc (λ a b → Rel b a) Rc-in Rc-out

    Bin : (n : ℕ) (i j : Fin (suc n)) → V ℓ
    Bin zero zero zero = D
    Bin (suc n) zero zero = F2 D (Us n)
    Bin (suc n) zero (suc j) = CR.LR n j
    Bin (suc n) (suc i) zero = CC.LR n i
    Bin (suc n) (suc i) (suc j) = F2 U (Bin n i j)

    hBin : (n : ℕ) (i j : Fin (suc n)) → InJ (Bin n i j)
    hBin zero zero zero = hD
    hBin (suc n) zero zero = JF2 D (Us n) hD (hUs n)
    hBin (suc n) zero (suc j) = CR.hLR n j
    hBin (suc n) (suc i) zero = CC.hLR n i
    hBin (suc n) (suc i) (suc j) = JF2 U (Bin n i j) JU (hBin n i j)

    Bin-out : (n : ℕ) (i j : Fin (suc n)) (δ : Vec SM (suc n))
            → ⟨ Rel (lookup i δ .fst) (lookup j δ .fst) ⟩
            → ⟨ Tup n δ ∈ˢ Bin n i j ⟩
    Bin-out zero zero zero (v ∷ []) rel = D-out (v .fst) (v .snd) rel
    Bin-out (suc n) zero zero (v ∷ δ) rel =
      prod-out D (Us n) (v .fst) (Tup n δ) (D-out (v .fst) (v .snd) rel) (Us-out n δ)
    Bin-out (suc n) zero (suc j) (v ∷ δ) rel = CR.LR-out n j v δ rel
    Bin-out (suc n) (suc i) zero (v ∷ δ) rel = CC.LR-out n i v δ rel
    Bin-out (suc n) (suc i) (suc j) (v ∷ δ) rel =
      prod-out U (Bin n i j) (v .fst) (Tup n δ) (v .snd) (Bin-out n i j δ rel)

    BinDec : (n : ℕ) (i j : Fin (suc n)) → V ℓ → Type (ℓ-suc ℓ)
    BinDec n i j m = ∥ Σ[ δ ∈ Vec SM (suc n) ]
                        (⟨ Rel (lookup i δ .fst) (lookup j δ .fst) ⟩
                       × (m ≡ Tup n δ)) ∥₁

    Bin-in : (n : ℕ) (i j : Fin (suc n)) (m : V ℓ) → ⟨ m ∈ˢ Bin n i j ⟩
           → BinDec n i j m
    Bin-in zero zero zero m h = ∣ ((m , rd .fst) ∷ []) , (rd .snd , refl) ∣₁
      where
      rd : ⟨ (m ∈ˢ U) ⊓ Rel m m ⟩
      rd = D-read m h
    Bin-in (suc n) zero zero m h = PT.rec squash₁ go (F2-read D (Us n) m h)
      where
      go : Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ]
             (⟨ p ∈ˢ D ⟩ × ⟨ q ∈ˢ Us n ⟩ × ⟨ m ≡ₕ pr p q ⟩)
         → BinDec (suc n) zero zero m
      go (p , q , hp , hq , m≡) = PT.rec squash₁ go' (Us-in n q hq)
        where
        rd : ⟨ (p ∈ˢ U) ⊓ Rel p p ⟩
        rd = D-read p hp
        go' : Σ[ δ ∈ Vec SM (suc n) ] (q ≡ Tup n δ) → BinDec (suc n) zero zero m
        go' (δ , q≡) = ∣ ((p , rd .fst) ∷ δ) , (rd .snd , m≡ ∙ cong (pr p) q≡) ∣₁
    Bin-in (suc n) zero (suc j) m h = PT.rec squash₁ go (CR.LR-in n j m h)
      where
      go : Σ[ v ∈ SM ] Σ[ δ ∈ Vec SM (suc n) ]
             (⟨ Rel (v .fst) (lookup j δ .fst) ⟩ × (m ≡ pr (v .fst) (Tup n δ)))
         → BinDec (suc n) zero (suc j) m
      go (v , δ , rel , m≡) = ∣ (v ∷ δ) , (rel , m≡) ∣₁
    Bin-in (suc n) (suc i) zero m h = PT.rec squash₁ go (CC.LR-in n i m h)
      where
      go : Σ[ v ∈ SM ] Σ[ δ ∈ Vec SM (suc n) ]
             (⟨ Rel (lookup i δ .fst) (v .fst) ⟩ × (m ≡ pr (v .fst) (Tup n δ)))
         → BinDec (suc n) (suc i) zero m
      go (v , δ , rel , m≡) = ∣ (v ∷ δ) , (rel , m≡) ∣₁
    Bin-in (suc n) (suc i) (suc j) m h =
      PT.rec squash₁ go (F2-read U (Bin n i j) m h)
      where
      go : Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ]
             (⟨ p ∈ˢ U ⟩ × ⟨ q ∈ˢ Bin n i j ⟩ × ⟨ m ≡ₕ pr p q ⟩)
         → BinDec (suc n) (suc i) (suc j) m
      go (p , q , hp , hq , m≡) = PT.rec squash₁ go' (Bin-in n i j q hq)
        where
        go' : Σ[ δ ∈ Vec SM (suc n) ]
                (⟨ Rel (lookup i δ .fst) (lookup j δ .fst) ⟩ × (q ≡ Tup n δ))
            → BinDec (suc n) (suc i) (suc j) m
        go' (δ , rel , q≡) = ∣ ((p , hp) ∷ δ) , (rel , m≡ ∙ cong (pr p) q≡) ∣₁

  Sel : (P : V ℓ) (n : ℕ) (i : Fin (suc n)) → V ℓ
  Sel P zero zero = P
  Sel P (suc n) zero = F2 P (Us n)
  Sel P (suc n) (suc i) = F2 U (Sel P n i)

  hSel : (P : V ℓ) → InJ P → (n : ℕ) (i : Fin (suc n)) → InJ (Sel P n i)
  hSel P hP zero zero = hP
  hSel P hP (suc n) zero = JF2 P (Us n) hP (hUs n)
  hSel P hP (suc n) (suc i) = JF2 U (Sel P n i) JU (hSel P hP n i)

  Sel-out : (P : V ℓ) (n : ℕ) (i : Fin (suc n)) (δ : Vec SM (suc n))
          → ⟨ lookup i δ .fst ∈ˢ P ⟩ → ⟨ Tup n δ ∈ˢ Sel P n i ⟩
  Sel-out P zero zero (v ∷ []) h = h
  Sel-out P (suc n) zero (v ∷ δ) h =
    prod-out P (Us n) (v .fst) (Tup n δ) h (Us-out n δ)
  Sel-out P (suc n) (suc i) (v ∷ δ) h =
    prod-out U (Sel P n i) (v .fst) (Tup n δ) (v .snd) (Sel-out P n i δ h)

  SelDec : (P : V ℓ) (n : ℕ) (i : Fin (suc n)) → V ℓ → Type (ℓ-suc ℓ)
  SelDec P n i m = ∥ Σ[ δ ∈ Vec SM (suc n) ]
                      (⟨ lookup i δ .fst ∈ˢ P ⟩ × (m ≡ Tup n δ)) ∥₁

  Sel-in : (P : V ℓ) (Psub : (x : V ℓ) → ⟨ x ∈ˢ P ⟩ → ⟨ x ∈ˢ U ⟩)
           (n : ℕ) (i : Fin (suc n)) (m : V ℓ)
         → ⟨ m ∈ˢ Sel P n i ⟩ → SelDec P n i m
  Sel-in P Psub zero zero m h = ∣ ((m , Psub m h) ∷ []) , (h , refl) ∣₁
  Sel-in P Psub (suc n) zero m h = PT.rec squash₁ go (F2-read P (Us n) m h)
    where
    go : Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ]
           (⟨ p ∈ˢ P ⟩ × ⟨ q ∈ˢ Us n ⟩ × ⟨ m ≡ₕ pr p q ⟩)
       → SelDec P (suc n) zero m
    go (p , q , hp , hq , m≡) = PT.rec squash₁ go' (Us-in n q hq)
      where
      go' : Σ[ δ ∈ Vec SM (suc n) ] (q ≡ Tup n δ) → SelDec P (suc n) zero m
      go' (δ , q≡) = ∣ ((p , Psub p hp) ∷ δ) , (hp , m≡ ∙ cong (pr p) q≡) ∣₁
  Sel-in P Psub (suc n) (suc i) m h = PT.rec squash₁ go (F2-read U (Sel P n i) m h)
    where
    go : Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ]
           (⟨ p ∈ˢ U ⟩ × ⟨ q ∈ˢ Sel P n i ⟩ × ⟨ m ≡ₕ pr p q ⟩)
       → SelDec P (suc n) (suc i) m
    go (p , q , hp , hq , m≡) = PT.rec squash₁ go' (Sel-in P Psub n i q hq)
      where
      go' : Σ[ δ ∈ Vec SM (suc n) ]
              (⟨ lookup i δ .fst ∈ˢ P ⟩ × (q ≡ Tup n δ))
          → SelDec P (suc n) (suc i) m
      go' (δ , hd , q≡) = ∣ ((p , hp) ∷ δ) , (hd , m≡ ∙ cong (pr p) q≡) ∣₁
```

<!--en-->
## The atoms and the engine

Instantiating the coordinate families at membership and at equality gives every
atom whose two terms are variables. An atom with a constant is a slice: a
constant on the right cuts by membership in that constant, a constant on the left
cuts by the `F10` slice "the sets that contain it", and an equality with a
constant cuts by its singleton. Two constants decide by excluded middle, and the
answer is the whole tuple space or the empty one.

Then `T`{.Agda} itself, one clause per constructor of the object language, and
the engine `hT`{.Agda}: every satisfaction set is a member of the closure.
<!--zh-->
## 原子与引擎

把坐标族分别实例化于隶属与等词，就得到两个词项都是变量的一切原子。带常量的原子是切片：常量在右，按属于该常量切；常量在左，按 `F10` 切片「含它的那些集合」切；与常量的等式，则按其单点集切。两个常量由排中律裁决，答案或是整个元组空间，或是空的那个。

随后是 `T`{.Agda} 本身，对象语言每个构造子一条子句，以及引擎 `hT`{.Agda}：每个满足集都是闭包的成员。
<!--/-->

```agda
  memU : (c : ⟪ U ⟫) → ⟨ ⟪ U ⟫↪ c ∈ˢ U ⟩
  memU c = ∈∈ₛ {a = ⟪ U ⟫↪ c} {b = U} .snd (∈ₛ⟪ U ⟫↪ c)

  Uself-read : (v : V ℓ) → ⟨ v ∈ˢ U ⟩ → ⟨ (v ∈ˢ U) ⊓ (v ≡ₕ v) ⟩
  Uself-read v h = h , refl

  Uself-out : (v : V ℓ) → ⟨ v ∈ˢ U ⟩ → ⟨ v ≡ₕ v ⟩ → ⟨ v ∈ˢ U ⟩
  Uself-out v h _ = h

  module A∈ = Atoms (λ a b → a ∈ˢ b) Mem Memᶜ Slf hMem hMemᶜ hSlf
                    (F7-read U U) Mem-out Memᶜ-in Memᶜ-out Slf-read Slf-out

  module A≐ = Atoms (λ a b → a ≡ₕ b) Diag Diag U hDiag hDiag JU
                    Diag-in Diag-out Diagᶜ-in Diagᶜ-out Uself-read Uself-out

  singl : (c : ⟪ U ⟫) → V ℓ
  singl c = F0 (⟪ U ⟫↪ c) (⟪ U ⟫↪ c)

  hSingl : (c : ⟪ U ⟫) → InJ (singl c)
  hSingl c = JF0 (⟪ U ⟫↪ c) (⟪ U ⟫↪ c)
    (UmemInJ (⟪ U ⟫↪ c) (memU c)) (UmemInJ (⟪ U ⟫↪ c) (memU c))

  singl-in : (c : ⟪ U ⟫) (x : V ℓ) → ⟨ x ∈ˢ singl c ⟩ → x ≡ ⟪ U ⟫↪ c
  singl-in c x h = PT.rec (setIsSet x (⟪ U ⟫↪ c))
    (λ { (inl p) → p ; (inr p) → p })
    (F0-spec (⟪ U ⟫↪ c) (⟪ U ⟫↪ c) x .fst h)

  singl-out : (c : ⟪ U ⟫) (x : V ℓ) → x ≡ ⟪ U ⟫↪ c → ⟨ x ∈ˢ singl c ⟩
  singl-out c x p = F0-spec (⟪ U ⟫↪ c) (⟪ U ⟫↪ c) x .snd ∣ inl p ∣₁

  singl-sub : (c : ⟪ U ⟫) (x : V ℓ) → ⟨ x ∈ˢ singl c ⟩ → ⟨ x ∈ˢ U ⟩
  singl-sub c x h = subst (λ w → ⟨ w ∈ˢ U ⟩) (sym (singl-in c x h)) (memU c)

  condSet : (n : ℕ) (P : hProp (ℓ-suc ℓ)) → (⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥)) → V ℓ
  condSet n P (inl _) = Us n
  condSet n P (inr _) = Emp n

  hCond : (n : ℕ) (P : hProp (ℓ-suc ℓ)) (d : ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥))
        → InJ (condSet n P d)
  hCond n P (inl _) = hUs n
  hCond n P (inr _) = hEmp n

  cond-out : (n : ℕ) (P : hProp (ℓ-suc ℓ)) (d : ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥))
             (m : V ℓ) → ⟨ m ∈ˢ Us n ⟩ → ⟨ P ⟩ → ⟨ m ∈ˢ condSet n P d ⟩
  cond-out n P (inl _) m h p = h
  cond-out n P (inr np) m h p = Empty.rec (np p)

  cond-in : (n : ℕ) (P : hProp (ℓ-suc ℓ)) (d : ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥))
            (m : V ℓ) → ⟨ m ∈ˢ condSet n P d ⟩ → ⟨ (m ∈ˢ Us n) ⊓ P ⟩
  cond-in n P (inl p) m h = h , p
  cond-in n P (inr np) m h = Empty.rec (Emp-elim n m h)

  atomIn : (n : ℕ) → Term ⟪ U ⟫ (suc n) → Term ⟪ U ⟫ (suc n) → V ℓ
  atomIn n (var i) (var j) = A∈.Bin n i j
  atomIn n (var i) (con d) = Sel (⟪ U ⟫↪ d) n i
  atomIn n (con c) (var j) = Sel (Up (⟪ U ⟫↪ c)) n j
  atomIn n (con c) (con d) =
    condSet n (⟪ U ⟫↪ c ∈ˢ ⟪ U ⟫↪ d) (lem (⟪ U ⟫↪ c ∈ˢ ⟪ U ⟫↪ d))

  atomEq : (n : ℕ) → Term ⟪ U ⟫ (suc n) → Term ⟪ U ⟫ (suc n) → V ℓ
  atomEq n (var i) (var j) = A≐.Bin n i j
  atomEq n (var i) (con d) = Sel (singl d) n i
  atomEq n (con c) (var j) = Sel (singl c) n j
  atomEq n (con c) (con d) =
    condSet n (⟪ U ⟫↪ c ≡ₕ ⟪ U ⟫↪ d) (lem (⟪ U ⟫↪ c ≡ₕ ⟪ U ⟫↪ d))

  hAtomIn : (n : ℕ) (t s : Term ⟪ U ⟫ (suc n)) → InJ (atomIn n t s)
  hAtomIn n (var i) (var j) = A∈.hBin n i j
  hAtomIn n (var i) (con d) = hSel (⟪ U ⟫↪ d) (UmemInJ (⟪ U ⟫↪ d) (memU d)) n i
  hAtomIn n (con c) (var j) =
    hSel (Up (⟪ U ⟫↪ c)) (J-Up (⟪ U ⟫↪ c) (UmemInJ (⟪ U ⟫↪ c) (memU c))) n j
  hAtomIn n (con c) (con d) =
    hCond n (⟪ U ⟫↪ c ∈ˢ ⟪ U ⟫↪ d) (lem (⟪ U ⟫↪ c ∈ˢ ⟪ U ⟫↪ d))

  hAtomEq : (n : ℕ) (t s : Term ⟪ U ⟫ (suc n)) → InJ (atomEq n t s)
  hAtomEq n (var i) (var j) = A≐.hBin n i j
  hAtomEq n (var i) (con d) = hSel (singl d) (hSingl d) n i
  hAtomEq n (con c) (var j) = hSel (singl c) (hSingl c) n j
  hAtomEq n (con c) (con d) =
    hCond n (⟪ U ⟫↪ c ≡ₕ ⟪ U ⟫↪ d) (lem (⟪ U ⟫↪ c ≡ₕ ⟪ U ⟫↪ d))

  AtomInDec : (n : ℕ) (t s : Term ⟪ U ⟫ (suc n)) → V ℓ → Type (ℓ-suc ℓ)
  AtomInDec n t s m = ∥ Σ[ δ ∈ Vec SM (suc n) ]
                         (⟨ (⟦ t ⟧ᵐ δ) .fst ∈ˢ (⟦ s ⟧ᵐ δ) .fst ⟩
                        × (m ≡ Tup n δ)) ∥₁

  AtomEqDec : (n : ℕ) (t s : Term ⟪ U ⟫ (suc n)) → V ℓ → Type (ℓ-suc ℓ)
  AtomEqDec n t s m = ∥ Σ[ δ ∈ Vec SM (suc n) ]
                         (((⟦ t ⟧ᵐ δ) .fst ≡ (⟦ s ⟧ᵐ δ) .fst)
                        × (m ≡ Tup n δ)) ∥₁

  atomIn-out : (n : ℕ) (t s : Term ⟪ U ⟫ (suc n)) (δ : Vec SM (suc n))
             → ⟨ (⟦ t ⟧ᵐ δ) .fst ∈ˢ (⟦ s ⟧ᵐ δ) .fst ⟩ → ⟨ Tup n δ ∈ˢ atomIn n t s ⟩
  atomIn-out n (var i) (var j) δ h = A∈.Bin-out n i j δ h
  atomIn-out n (var i) (con d) δ h = Sel-out (⟪ U ⟫↪ d) n i δ h
  atomIn-out n (con c) (var j) δ h =
    Sel-out (Up (⟪ U ⟫↪ c)) n j δ
      (Up-out (⟪ U ⟫↪ c) (lookup j δ .fst) (memU c) (lookup j δ .snd) h)
  atomIn-out n (con c) (con d) δ h =
    cond-out n (⟪ U ⟫↪ c ∈ˢ ⟪ U ⟫↪ d) (lem (⟪ U ⟫↪ c ∈ˢ ⟪ U ⟫↪ d))
      (Tup n δ) (Us-out n δ) h

  atomIn-in : (n : ℕ) (t s : Term ⟪ U ⟫ (suc n)) (m : V ℓ)
            → ⟨ m ∈ˢ atomIn n t s ⟩ → AtomInDec n t s m
  atomIn-in n (var i) (var j) m h = A∈.Bin-in n i j m h
  atomIn-in n (var i) (con d) m h = Sel-in (⟪ U ⟫↪ d) sub n i m h
    where
    sub : (x : V ℓ) → ⟨ x ∈ˢ ⟪ U ⟫↪ d ⟩ → ⟨ x ∈ˢ U ⟩
    sub x hx = Utrans x (⟪ U ⟫↪ d) hx (memU d)
  atomIn-in n (con c) (var j) m h =
    PT.map step (Sel-in (Up (⟪ U ⟫↪ c)) sub n j m h)
    where
    sub : (x : V ℓ) → ⟨ x ∈ˢ Up (⟪ U ⟫↪ c) ⟩ → ⟨ x ∈ˢ U ⟩
    sub x hx = Up-read (⟪ U ⟫↪ c) x hx .snd .fst
    step : Σ[ δ ∈ Vec SM (suc n) ]
             (⟨ lookup j δ .fst ∈ˢ Up (⟪ U ⟫↪ c) ⟩ × (m ≡ Tup n δ))
         → Σ[ δ ∈ Vec SM (suc n) ]
              (⟨ ⟪ U ⟫↪ c ∈ˢ lookup j δ .fst ⟩ × (m ≡ Tup n δ))
    step (δ , hd , eq) =
      δ , (Up-read (⟪ U ⟫↪ c) (lookup j δ .fst) hd .snd .snd , eq)
  atomIn-in n (con c) (con d) m h = PT.map step (Us-in n m (rd .fst))
    where
    rd : ⟨ (m ∈ˢ Us n) ⊓ (⟪ U ⟫↪ c ∈ˢ ⟪ U ⟫↪ d) ⟩
    rd = cond-in n (⟪ U ⟫↪ c ∈ˢ ⟪ U ⟫↪ d) (lem (⟪ U ⟫↪ c ∈ˢ ⟪ U ⟫↪ d)) m h
    step : Σ[ δ ∈ Vec SM (suc n) ] (m ≡ Tup n δ)
         → Σ[ δ ∈ Vec SM (suc n) ]
              (⟨ ⟪ U ⟫↪ c ∈ˢ ⟪ U ⟫↪ d ⟩ × (m ≡ Tup n δ))
    step (δ , eq) = δ , (rd .snd , eq)

  atomEq-out : (n : ℕ) (t s : Term ⟪ U ⟫ (suc n)) (δ : Vec SM (suc n))
             → (⟦ t ⟧ᵐ δ) .fst ≡ (⟦ s ⟧ᵐ δ) .fst → ⟨ Tup n δ ∈ˢ atomEq n t s ⟩
  atomEq-out n (var i) (var j) δ h = A≐.Bin-out n i j δ h
  atomEq-out n (var i) (con d) δ h =
    Sel-out (singl d) n i δ (singl-out d (lookup i δ .fst) h)
  atomEq-out n (con c) (var j) δ h =
    Sel-out (singl c) n j δ (singl-out c (lookup j δ .fst) (sym h))
  atomEq-out n (con c) (con d) δ h =
    cond-out n (⟪ U ⟫↪ c ≡ₕ ⟪ U ⟫↪ d) (lem (⟪ U ⟫↪ c ≡ₕ ⟪ U ⟫↪ d))
      (Tup n δ) (Us-out n δ) h

  atomEq-in : (n : ℕ) (t s : Term ⟪ U ⟫ (suc n)) (m : V ℓ)
            → ⟨ m ∈ˢ atomEq n t s ⟩ → AtomEqDec n t s m
  atomEq-in n (var i) (var j) m h = A≐.Bin-in n i j m h
  atomEq-in n (var i) (con d) m h =
    PT.map step (Sel-in (singl d) (singl-sub d) n i m h)
    where
    step : Σ[ δ ∈ Vec SM (suc n) ]
             (⟨ lookup i δ .fst ∈ˢ singl d ⟩ × (m ≡ Tup n δ))
         → Σ[ δ ∈ Vec SM (suc n) ]
              ((lookup i δ .fst ≡ ⟪ U ⟫↪ d) × (m ≡ Tup n δ))
    step (δ , hd , eq) = δ , (singl-in d (lookup i δ .fst) hd , eq)
  atomEq-in n (con c) (var j) m h =
    PT.map step (Sel-in (singl c) (singl-sub c) n j m h)
    where
    step : Σ[ δ ∈ Vec SM (suc n) ]
             (⟨ lookup j δ .fst ∈ˢ singl c ⟩ × (m ≡ Tup n δ))
         → Σ[ δ ∈ Vec SM (suc n) ]
              ((⟪ U ⟫↪ c ≡ lookup j δ .fst) × (m ≡ Tup n δ))
    step (δ , hd , eq) = δ , (sym (singl-in c (lookup j δ .fst) hd) , eq)
  atomEq-in n (con c) (con d) m h = PT.map step (Us-in n m (rd .fst))
    where
    rd : ⟨ (m ∈ˢ Us n) ⊓ (⟪ U ⟫↪ c ≡ₕ ⟪ U ⟫↪ d) ⟩
    rd = cond-in n (⟪ U ⟫↪ c ≡ₕ ⟪ U ⟫↪ d) (lem (⟪ U ⟫↪ c ≡ₕ ⟪ U ⟫↪ d)) m h
    step : Σ[ δ ∈ Vec SM (suc n) ] (m ≡ Tup n δ)
         → Σ[ δ ∈ Vec SM (suc n) ]
              ((⟪ U ⟫↪ c ≡ ⟪ U ⟫↪ d) × (m ≡ Tup n δ))
    step (δ , eq) = δ , (rd .snd , eq)

  Ev : (n : ℕ) → Term ⟪ U ⟫ (suc n) → V ℓ
  Ev n (con c) = F2 (⟪ U ⟫↪ c) (Us n)
  Ev n (var i) = A∈.CR.LR n i

  hEv : (n : ℕ) (t : Term ⟪ U ⟫ (suc n)) → InJ (Ev n t)
  hEv n (con c) = JF2 (⟪ U ⟫↪ c) (Us n) (UmemInJ (⟪ U ⟫↪ c) (memU c)) (hUs n)
  hEv n (var i) = A∈.CR.hLR n i

  Ev-out : (n : ℕ) (t : Term ⟪ U ⟫ (suc n)) (v : SM) (δ : Vec SM (suc n))
         → ⟨ v .fst ∈ˢ (⟦ t ⟧ᵐ δ) .fst ⟩ → ⟨ pr (v .fst) (Tup n δ) ∈ˢ Ev n t ⟩
  Ev-out n (con c) v δ h =
    prod-out (⟪ U ⟫↪ c) (Us n) (v .fst) (Tup n δ) h (Us-out n δ)
  Ev-out n (var i) v δ h = A∈.CR.LR-out n i v δ h

  EvDec : (n : ℕ) (t : Term ⟪ U ⟫ (suc n)) → V ℓ → Type (ℓ-suc ℓ)
  EvDec n t m = ∥ Σ[ v ∈ SM ] Σ[ δ ∈ Vec SM (suc n) ]
                   (⟨ v .fst ∈ˢ (⟦ t ⟧ᵐ δ) .fst ⟩
                  × (m ≡ pr (v .fst) (Tup n δ))) ∥₁

  Ev-in : (n : ℕ) (t : Term ⟪ U ⟫ (suc n)) (m : V ℓ) → ⟨ m ∈ˢ Ev n t ⟩ → EvDec n t m
  Ev-in n (con c) m h = PT.rec squash₁ go (F2-read (⟪ U ⟫↪ c) (Us n) m h)
    where
    go : Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ]
           (⟨ p ∈ˢ ⟪ U ⟫↪ c ⟩ × ⟨ q ∈ˢ Us n ⟩ × ⟨ m ≡ₕ pr p q ⟩)
       → EvDec n (con c) m
    go (p , q , hp , hq , m≡) = PT.map step (Us-in n q hq)
      where
      step : Σ[ δ ∈ Vec SM (suc n) ] (q ≡ Tup n δ)
           → Σ[ v ∈ SM ] Σ[ δ ∈ Vec SM (suc n) ]
                (⟨ v .fst ∈ˢ ⟪ U ⟫↪ c ⟩ × (m ≡ pr (v .fst) (Tup n δ)))
      step (δ , q≡) = (p , Utrans p (⟪ U ⟫↪ c) hp (memU c)) , δ
                    , (hp , m≡ ∙ cong (pr p) q≡)
  Ev-in n (var i) m h = A∈.CR.LR-in n i m h

  T : (n : ℕ) → Formula ⟪ U ⟫ (suc n) → V ℓ
  T n (t ∈̇ s) = atomIn n t s
  T n (t ≐ s) = atomEq n t s
  T n (φ ∧̇ ψ) = capOp (T n φ) (T n ψ)
  T n (φ ∨̇ ψ) = cupOp (T n φ) (T n ψ)
  T n (φ ⇒̇ ψ) = F1 (Us n) (F1 (T n φ) (T n ψ))
  T n (¬̇ φ) = F1 (Us n) (T n φ)
  T n ⊤̇ = Us n
  T n ⊥̇ = Emp n
  T n (∃̇ φ) = ranOp (T (suc n) φ)
  T n (∀̇ φ) = F1 (Us n) (ranOp (F1 (Us (suc n)) (T (suc n) φ)))
  T n (∀̇∈ t φ) =
    F1 (Us n) (ranOp (capOp (Ev n t) (F1 (Us (suc n)) (T (suc n) φ))))
  T n (∃̇∈ t φ) = ranOp (capOp (Ev n t) (T (suc n) φ))

  hT : (n : ℕ) (φ : Formula ⟪ U ⟫ (suc n)) → InJ (T n φ)
  hT n (t ∈̇ s) = hAtomIn n t s
  hT n (t ≐ s) = hAtomEq n t s
  hT n (φ ∧̇ ψ) = J-cap (T n φ) (T n ψ) (hT n φ) (hT n ψ)
  hT n (φ ∨̇ ψ) = J-cup (T n φ) (T n ψ) (hT n φ) (hT n ψ)
  hT n (φ ⇒̇ ψ) = JF1 (Us n) (F1 (T n φ) (T n ψ)) (hUs n)
    (JF1 (T n φ) (T n ψ) (hT n φ) (hT n ψ))
  hT n (¬̇ φ) = JF1 (Us n) (T n φ) (hUs n) (hT n φ)
  hT n ⊤̇ = hUs n
  hT n ⊥̇ = hEmp n
  hT n (∃̇ φ) = J-ran (T (suc n) φ) (hT (suc n) φ)
  hT n (∀̇ φ) = JF1 (Us n) (ranOp (F1 (Us (suc n)) (T (suc n) φ))) (hUs n)
    (J-ran (F1 (Us (suc n)) (T (suc n) φ))
      (JF1 (Us (suc n)) (T (suc n) φ) (hUs (suc n)) (hT (suc n) φ)))
  hT n (∀̇∈ t φ) =
    JF1 (Us n) (ranOp (capOp (Ev n t) (F1 (Us (suc n)) (T (suc n) φ)))) (hUs n)
      (J-ran (capOp (Ev n t) (F1 (Us (suc n)) (T (suc n) φ)))
        (J-cap (Ev n t) (F1 (Us (suc n)) (T (suc n) φ)) (hEv n t)
          (JF1 (Us (suc n)) (T (suc n) φ) (hUs (suc n)) (hT (suc n) φ))))
  hT n (∃̇∈ t φ) = J-ran (capOp (Ev n t) (T (suc n) φ))
    (J-cap (Ev n t) (T (suc n) φ) (hEv n t) (hT (suc n) φ))
```

<!--en-->
## Adequacy

The engine says the sets are members of the closure; adequacy says they are the
right sets. Both directions are proved **at a tuple**, not at an arbitrary
member: `adeq-mem`{.Agda} reads satisfaction off membership at `Tup δ`, and
`adeq-set`{.Agda} writes it back. That is the decode-uniqueness dividend in
force: because `Tup-inj`{.Agda} is proved once, no clause has to compare two
decodes of one member, and the arbitrary-member form follows at the end by one
generic step through `Us-in`{.Agda}.
<!--zh-->
## 适足

引擎说这些集合是闭包的成员；适足说它们是**对**的集合。两个方向都在**元组处**证明，而非在任意成员处：`adeq-mem`{.Agda} 从 `Tup δ` 处的隶属读出满足，`adeq-set`{.Agda} 把它写回去。这正是解码唯一性红利在起作用：`Tup-inj`{.Agda} 只证一次，于是没有任何子句需要比较一个成员的两次解码，而任意成员的形式最后经 `Us-in`{.Agda} 一步通用手续得出。
<!--/-->

```agda
  Us-fst : (n : ℕ) (u m : V ℓ) → ⟨ pr u m ∈ˢ Us (suc n) ⟩ → ⟨ u ∈ˢ U ⟩
  Us-fst n u m h = PT.rec (snd (u ∈ˢ U)) go (F2-read U (Us n) (pr u m) h)
    where
    go : Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ]
           (⟨ p ∈ˢ U ⟩ × ⟨ q ∈ˢ Us n ⟩ × ⟨ pr u m ≡ₕ pr p q ⟩)
       → ⟨ u ∈ˢ U ⟩
    go (p , q , hp , hq , eq) =
      subst (λ w → ⟨ w ∈ˢ U ⟩) (sym (pr-inj eq .fst)) hp

  Us-snd : (n : ℕ) (u m : V ℓ) → ⟨ pr u m ∈ˢ Us (suc n) ⟩ → ⟨ m ∈ˢ Us n ⟩
  Us-snd n u m h = PT.rec (snd (m ∈ˢ Us n)) go (F2-read U (Us n) (pr u m) h)
    where
    go : Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ]
           (⟨ p ∈ˢ U ⟩ × ⟨ q ∈ˢ Us n ⟩ × ⟨ pr u m ≡ₕ pr p q ⟩)
       → ⟨ m ∈ˢ Us n ⟩
    go (p , q , hp , hq , eq) =
      subst (λ w → ⟨ w ∈ˢ Us n ⟩) (sym (pr-inj eq .snd)) hq

  decUs : (n : ℕ) (m : V ℓ) → DecTup n m → ⟨ m ∈ˢ Us n ⟩
  decUs n m = PT.rec (snd (m ∈ˢ Us n))
    (λ { (δ , eq) → subst (λ w → ⟨ w ∈ˢ Us n ⟩) (sym eq) (Us-out n δ) })

  T-sub : (n : ℕ) (φ : Formula ⟪ U ⟫ (suc n)) (m : V ℓ)
        → ⟨ m ∈ˢ T n φ ⟩ → ⟨ m ∈ˢ Us n ⟩
  T-sub n (t ∈̇ s) m h =
    decUs n m (PT.map (λ { (δ , _ , eq) → δ , eq }) (atomIn-in n t s m h))
  T-sub n (t ≐ s) m h =
    decUs n m (PT.map (λ { (δ , _ , eq) → δ , eq }) (atomEq-in n t s m h))
  T-sub n (φ ∧̇ ψ) m h = T-sub n φ m (capOp-in (T n φ) (T n ψ) m h .fst)
  T-sub n (φ ∨̇ ψ) m h = PT.rec (snd (m ∈ˢ Us n)) br
    (cupOp-in (T n φ) (T n ψ) m h)
    where
    br : ⟨ m ∈ˢ T n φ ⟩ ⊎ ⟨ m ∈ˢ T n ψ ⟩ → ⟨ m ∈ˢ Us n ⟩
    br (inl k) = T-sub n φ m k
    br (inr k) = T-sub n ψ m k
  T-sub n (φ ⇒̇ ψ) m h = dif-in (Us n) (F1 (T n φ) (T n ψ)) m h .fst
  T-sub n (¬̇ φ) m h = dif-in (Us n) (T n φ) m h .fst
  T-sub n ⊤̇ m h = h
  T-sub n ⊥̇ m h = Empty.rec (Emp-elim n m h)
  T-sub n (∃̇ φ) m h = PT.rec (snd (m ∈ˢ Us n)) go (ranOp-in (T (suc n) φ) m h)
    where
    go : Σ[ u ∈ V ℓ ] ⟨ pr u m ∈ˢ T (suc n) φ ⟩ → ⟨ m ∈ˢ Us n ⟩
    go (u , hu) = Us-snd n u m (T-sub (suc n) φ (pr u m) hu)
  T-sub n (∀̇ φ) m h =
    dif-in (Us n) (ranOp (F1 (Us (suc n)) (T (suc n) φ))) m h .fst
  T-sub n (∀̇∈ t φ) m h =
    dif-in (Us n) (ranOp (capOp (Ev n t) (F1 (Us (suc n)) (T (suc n) φ)))) m h .fst
  T-sub n (∃̇∈ t φ) m h = PT.rec (snd (m ∈ˢ Us n)) go
    (ranOp-in (capOp (Ev n t) (T (suc n) φ)) m h)
    where
    go : Σ[ u ∈ V ℓ ] ⟨ pr u m ∈ˢ capOp (Ev n t) (T (suc n) φ) ⟩ → ⟨ m ∈ˢ Us n ⟩
    go (u , hu) = Us-snd n u m
      (T-sub (suc n) φ (pr u m) (capOp-in (Ev n t) (T (suc n) φ) (pr u m) hu .snd))

  mutual
    adeq-mem : (n : ℕ) (φ : Formula ⟪ U ⟫ (suc n)) (δ : Vec SM (suc n))
             → ⟨ Tup n δ ∈ˢ T n φ ⟩ → ⟨ δ ⊨ᵐ φ ⟩

    adeq-set : (n : ℕ) (φ : Formula ⟪ U ⟫ (suc n)) (δ : Vec SM (suc n))
             → ⟨ δ ⊨ᵐ φ ⟩ → ⟨ Tup n δ ∈ˢ T n φ ⟩

    adeq-mem n (t ∈̇ s) δ h = PT.rec (snd (δ ⊨ᵐ (t ∈̇ s))) step
      (atomIn-in n t s (Tup n δ) h)
      where
      step : Σ[ ε ∈ Vec SM (suc n) ]
               (⟨ (⟦ t ⟧ᵐ ε) .fst ∈ˢ (⟦ s ⟧ᵐ ε) .fst ⟩ × (Tup n δ ≡ Tup n ε))
           → ⟨ δ ⊨ᵐ (t ∈̇ s) ⟩
      step (ε , sat , eq) = Sat-cong n (t ∈̇ s) δ ε eq sat
    adeq-mem n (t ≐ s) δ h = PT.rec (snd (δ ⊨ᵐ (t ≐ s))) step
      (atomEq-in n t s (Tup n δ) h)
      where
      step : Σ[ ε ∈ Vec SM (suc n) ]
               (((⟦ t ⟧ᵐ ε) .fst ≡ (⟦ s ⟧ᵐ ε) .fst) × (Tup n δ ≡ Tup n ε))
           → ⟨ δ ⊨ᵐ (t ≐ s) ⟩
      step (ε , sat , eq) = Sat-cong n (t ≐ s) δ ε eq sat
    adeq-mem n (φ ∧̇ ψ) δ h =
        adeq-mem n φ δ (parts .fst)
      , adeq-mem n ψ δ (parts .snd)
      where
      parts : ⟨ Tup n δ ∈ˢ T n φ ⟩ × ⟨ Tup n δ ∈ˢ T n ψ ⟩
      parts = capOp-in (T n φ) (T n ψ) (Tup n δ) h
    adeq-mem n (φ ∨̇ ψ) δ h = PT.rec (snd (δ ⊨ᵐ (φ ∨̇ ψ))) br
      (cupOp-in (T n φ) (T n ψ) (Tup n δ) h)
      where
      br : ⟨ Tup n δ ∈ˢ T n φ ⟩ ⊎ ⟨ Tup n δ ∈ˢ T n ψ ⟩ → ⟨ δ ⊨ᵐ (φ ∨̇ ψ) ⟩
      br (inl k) = ∣ inl (adeq-mem n φ δ k) ∣₁
      br (inr k) = ∣ inr (adeq-mem n ψ δ k) ∣₁
    adeq-mem n (φ ⇒̇ ψ) δ h satφ = dneV (δ ⊨ᵐ ψ) nn
      where
      parts : ⟨ Tup n δ ∈ˢ Us n ⟩
            × (⟨ Tup n δ ∈ˢ F1 (T n φ) (T n ψ) ⟩ → Empty.⊥)
      parts = dif-in (Us n) (F1 (T n φ) (T n ψ)) (Tup n δ) h
      nn : (⟨ δ ⊨ᵐ ψ ⟩ → Empty.⊥) → Empty.⊥
      nn nψ = parts .snd (dif-out (T n φ) (T n ψ) (Tup n δ)
        (adeq-set n φ δ satφ) (λ k → nψ (adeq-mem n ψ δ k)))
    adeq-mem n (¬̇ φ) δ h sat =
      dif-in (Us n) (T n φ) (Tup n δ) h .snd (adeq-set n φ δ sat)
    adeq-mem n ⊤̇ δ h = tt*
    adeq-mem n ⊥̇ δ h = Empty.rec (Emp-elim n (Tup n δ) h)
    adeq-mem n (∃̇ φ) δ h = PT.map go (ranOp-in (T (suc n) φ) (Tup n δ) h)
      where
      go : Σ[ u ∈ V ℓ ] ⟨ pr u (Tup n δ) ∈ˢ T (suc n) φ ⟩
         → Σ[ x ∈ SM ] ⟨ (x ∷ δ) ⊨ᵐ φ ⟩
      go (u , hu) = (u , u∈U) , adeq-mem (suc n) φ ((u , u∈U) ∷ δ) hu
        where
        u∈U : ⟨ u ∈ˢ U ⟩
        u∈U = Us-fst n u (Tup n δ) (T-sub (suc n) φ (pr u (Tup n δ)) hu)
    adeq-mem n (∀̇ φ) δ h x = dneV ((x ∷ δ) ⊨ᵐ φ) nn
      where
      parts : ⟨ Tup n δ ∈ˢ Us n ⟩
            × (⟨ Tup n δ ∈ˢ ranOp (F1 (Us (suc n)) (T (suc n) φ)) ⟩ → Empty.⊥)
      parts = dif-in (Us n) (ranOp (F1 (Us (suc n)) (T (suc n) φ))) (Tup n δ) h
      nn : (⟨ (x ∷ δ) ⊨ᵐ φ ⟩ → Empty.⊥) → Empty.⊥
      nn nsat = parts .snd
        (ranOp-out (F1 (Us (suc n)) (T (suc n) φ)) (x .fst) (Tup n δ)
          (dif-out (Us (suc n)) (T (suc n) φ) (Tup (suc n) (x ∷ δ))
            (Us-out (suc n) (x ∷ δ))
            (λ k → nsat (adeq-mem (suc n) φ (x ∷ δ) k))))
    adeq-mem n (∀̇∈ t φ) δ h x hx = dneV ((x ∷ δ) ⊨ᵐ φ) nn
      where
      W : V ℓ
      W = capOp (Ev n t) (F1 (Us (suc n)) (T (suc n) φ))
      parts : ⟨ Tup n δ ∈ˢ Us n ⟩ × (⟨ Tup n δ ∈ˢ ranOp W ⟩ → Empty.⊥)
      parts = dif-in (Us n) (ranOp W) (Tup n δ) h
      nn : (⟨ (x ∷ δ) ⊨ᵐ φ ⟩ → Empty.⊥) → Empty.⊥
      nn nsat = parts .snd (ranOp-out W (x .fst) (Tup n δ)
        (capOp-out (Ev n t) (F1 (Us (suc n)) (T (suc n) φ)) (Tup (suc n) (x ∷ δ))
          (Ev-out n t x δ hx)
          (dif-out (Us (suc n)) (T (suc n) φ) (Tup (suc n) (x ∷ δ))
            (Us-out (suc n) (x ∷ δ))
            (λ k → nsat (adeq-mem (suc n) φ (x ∷ δ) k)))))
    adeq-mem n (∃̇∈ t φ) δ h = PT.rec (snd (δ ⊨ᵐ (∃̇∈ t φ))) go
      (ranOp-in (capOp (Ev n t) (T (suc n) φ)) (Tup n δ) h)
      where
      go : Σ[ u ∈ V ℓ ] ⟨ pr u (Tup n δ) ∈ˢ capOp (Ev n t) (T (suc n) φ) ⟩
         → ⟨ δ ⊨ᵐ (∃̇∈ t φ) ⟩
      go (u , hu) = PT.map step (Ev-in n t (pr u (Tup n δ)) (parts .fst))
        where
        parts : ⟨ pr u (Tup n δ) ∈ˢ Ev n t ⟩
              × ⟨ pr u (Tup n δ) ∈ˢ T (suc n) φ ⟩
        parts = capOp-in (Ev n t) (T (suc n) φ) (pr u (Tup n δ)) hu
        step : Σ[ v ∈ SM ] Σ[ ε ∈ Vec SM (suc n) ]
                 (⟨ v .fst ∈ˢ (⟦ t ⟧ᵐ ε) .fst ⟩
                × (pr u (Tup n δ) ≡ pr (v .fst) (Tup n ε)))
             → Σ[ x ∈ SM ]
                  (⟨ x .fst ∈ˢ (⟦ t ⟧ᵐ δ) .fst ⟩ × ⟨ (x ∷ δ) ⊨ᵐ φ ⟩)
        step (v , ε , bnd , eq) = v , (bnd' , sat)
          where
          δ≡ε : δ ≡ ε
          δ≡ε = Tup-inj n δ ε (pr-inj eq .snd)
          bnd' : ⟨ v .fst ∈ˢ (⟦ t ⟧ᵐ δ) .fst ⟩
          bnd' = subst (λ γ → ⟨ v .fst ∈ˢ (⟦ t ⟧ᵐ γ) .fst ⟩) (sym δ≡ε) bnd
          sat : ⟨ (v ∷ δ) ⊨ᵐ φ ⟩
          sat = adeq-mem (suc n) φ (v ∷ δ)
            (subst (λ w → ⟨ pr w (Tup n δ) ∈ˢ T (suc n) φ ⟩)
              (pr-inj eq .fst) (parts .snd))

    adeq-set n (t ∈̇ s) δ sat = atomIn-out n t s δ sat
    adeq-set n (t ≐ s) δ sat = atomEq-out n t s δ sat
    adeq-set n (φ ∧̇ ψ) δ sat = capOp-out (T n φ) (T n ψ) (Tup n δ)
      (adeq-set n φ δ (sat .fst)) (adeq-set n ψ δ (sat .snd))
    adeq-set n (φ ∨̇ ψ) δ sat =
      PT.rec (snd (Tup n δ ∈ˢ T n (φ ∨̇ ψ))) br sat
      where
      br : ⟨ δ ⊨ᵐ φ ⟩ ⊎ ⟨ δ ⊨ᵐ ψ ⟩ → ⟨ Tup n δ ∈ˢ T n (φ ∨̇ ψ) ⟩
      br (inl s) = cupOp-outl (T n φ) (T n ψ) (Tup n δ) (adeq-set n φ δ s)
      br (inr s) = cupOp-outr (T n φ) (T n ψ) (Tup n δ) (adeq-set n ψ δ s)
    adeq-set n (φ ⇒̇ ψ) δ sat =
      dif-out (Us n) (F1 (T n φ) (T n ψ)) (Tup n δ) (Us-out n δ) no
      where
      no : ⟨ Tup n δ ∈ˢ F1 (T n φ) (T n ψ) ⟩ → Empty.⊥
      no k = dif-in (T n φ) (T n ψ) (Tup n δ) k .snd
        (adeq-set n ψ δ (sat (adeq-mem n φ δ (dif-in (T n φ) (T n ψ) (Tup n δ) k .fst))))
    adeq-set n (¬̇ φ) δ sat = dif-out (Us n) (T n φ) (Tup n δ) (Us-out n δ)
      (λ k → sat (adeq-mem n φ δ k))
    adeq-set n ⊤̇ δ sat = Us-out n δ
    adeq-set n ⊥̇ δ sat = Empty.rec* sat
    adeq-set n (∃̇ φ) δ sat = PT.rec (snd (Tup n δ ∈ˢ T n (∃̇ φ))) go sat
      where
      go : Σ[ x ∈ SM ] ⟨ (x ∷ δ) ⊨ᵐ φ ⟩ → ⟨ Tup n δ ∈ˢ T n (∃̇ φ) ⟩
      go (x , s) = ranOp-out (T (suc n) φ) (x .fst) (Tup n δ)
        (adeq-set (suc n) φ (x ∷ δ) s)
    adeq-set n (∀̇ φ) δ sat =
      dif-out (Us n) (ranOp (F1 (Us (suc n)) (T (suc n) φ))) (Tup n δ)
        (Us-out n δ) no
      where
      no : ⟨ Tup n δ ∈ˢ ranOp (F1 (Us (suc n)) (T (suc n) φ)) ⟩ → Empty.⊥
      no k = PT.rec Empty.isProp⊥ go
        (ranOp-in (F1 (Us (suc n)) (T (suc n) φ)) (Tup n δ) k)
        where
        go : Σ[ u ∈ V ℓ ] ⟨ pr u (Tup n δ) ∈ˢ F1 (Us (suc n)) (T (suc n) φ) ⟩
           → Empty.⊥
        go (u , hu) = parts .snd (adeq-set (suc n) φ ((u , u∈U) ∷ δ) (sat (u , u∈U)))
          where
          parts : ⟨ pr u (Tup n δ) ∈ˢ Us (suc n) ⟩
                × (⟨ pr u (Tup n δ) ∈ˢ T (suc n) φ ⟩ → Empty.⊥)
          parts = dif-in (Us (suc n)) (T (suc n) φ) (pr u (Tup n δ)) hu
          u∈U : ⟨ u ∈ˢ U ⟩
          u∈U = Us-fst n u (Tup n δ) (parts .fst)
    adeq-set n (∀̇∈ t φ) δ sat =
      dif-out (Us n) (ranOp W) (Tup n δ) (Us-out n δ) no
      where
      W : V ℓ
      W = capOp (Ev n t) (F1 (Us (suc n)) (T (suc n) φ))
      no : ⟨ Tup n δ ∈ˢ ranOp W ⟩ → Empty.⊥
      no k = PT.rec Empty.isProp⊥ go (ranOp-in W (Tup n δ) k)
        where
        go : Σ[ u ∈ V ℓ ] ⟨ pr u (Tup n δ) ∈ˢ W ⟩ → Empty.⊥
        go (u , hu) = PT.rec Empty.isProp⊥ step
          (Ev-in n t (pr u (Tup n δ)) (parts .fst))
          where
          parts : ⟨ pr u (Tup n δ) ∈ˢ Ev n t ⟩
                × ⟨ pr u (Tup n δ) ∈ˢ F1 (Us (suc n)) (T (suc n) φ) ⟩
          parts = capOp-in (Ev n t) (F1 (Us (suc n)) (T (suc n) φ))
                    (pr u (Tup n δ)) hu
          step : Σ[ v ∈ SM ] Σ[ ε ∈ Vec SM (suc n) ]
                   (⟨ v .fst ∈ˢ (⟦ t ⟧ᵐ ε) .fst ⟩
                  × (pr u (Tup n δ) ≡ pr (v .fst) (Tup n ε)))
               → Empty.⊥
          step (v , ε , bnd , eq) =
            dif-in (Us (suc n)) (T (suc n) φ) (pr u (Tup n δ)) (parts .snd) .snd
              (subst (λ w → ⟨ pr w (Tup n δ) ∈ˢ T (suc n) φ ⟩)
                (sym (pr-inj eq .fst))
                (adeq-set (suc n) φ (v ∷ δ) (sat v bnd')))
            where
            δ≡ε : δ ≡ ε
            δ≡ε = Tup-inj n δ ε (pr-inj eq .snd)
            bnd' : ⟨ v .fst ∈ˢ (⟦ t ⟧ᵐ δ) .fst ⟩
            bnd' = subst (λ γ → ⟨ v .fst ∈ˢ (⟦ t ⟧ᵐ γ) .fst ⟩) (sym δ≡ε) bnd
    adeq-set n (∃̇∈ t φ) δ sat =
      PT.rec (snd (Tup n δ ∈ˢ T n (∃̇∈ t φ))) go sat
      where
      go : Σ[ x ∈ SM ] (⟨ x .fst ∈ˢ (⟦ t ⟧ᵐ δ) .fst ⟩ × ⟨ (x ∷ δ) ⊨ᵐ φ ⟩)
         → ⟨ Tup n δ ∈ˢ T n (∃̇∈ t φ) ⟩
      go (x , bnd , s) = ranOp-out (capOp (Ev n t) (T (suc n) φ)) (x .fst) (Tup n δ)
        (capOp-out (Ev n t) (T (suc n) φ) (Tup (suc n) (x ∷ δ))
          (Ev-out n t x δ bnd) (adeq-set (suc n) φ (x ∷ δ) s))

  Dec : (n : ℕ) → Formula ⟪ U ⟫ (suc n) → V ℓ → Type (ℓ-suc ℓ)
  Dec n φ m = ∥ Σ[ δ ∈ Vec SM (suc n) ] (⟨ δ ⊨ᵐ φ ⟩ × (m ≡ Tup n δ)) ∥₁

  adeq-in : (n : ℕ) (φ : Formula ⟪ U ⟫ (suc n)) (m : V ℓ)
          → ⟨ m ∈ˢ T n φ ⟩ → Dec n φ m
  adeq-in n φ m h = PT.map step (Us-in n m (T-sub n φ m h))
    where
    step : Σ[ δ ∈ Vec SM (suc n) ] (m ≡ Tup n δ)
         → Σ[ δ ∈ Vec SM (suc n) ] (⟨ δ ⊨ᵐ φ ⟩ × (m ≡ Tup n δ))
    step (δ , eq) =
      δ , (adeq-mem n φ δ (subst (λ w → ⟨ w ∈ˢ T n φ ⟩) eq h) , eq)

```

<!--en-->
## The definable set is the satisfaction set

At one free variable the tuple space is `U` itself and the tuple code is the
member itself, so the satisfaction set at arity one is literally a subset of `U`.
Adequacy at that arity says it is the subset `defSet φ` carves out, and the
engine already put it in the closure.
<!--zh-->
## 可定义集就是满足集

在一个自由变量处，元组空间就是 `U` 自身，元组编码也就是成员自身，故一元处的满足集字面上就是 `U` 的一个子集。该元数处的适足说它就是 `defSet φ` 刻出的那个子集，而引擎早已把它放进闭包。
<!--/-->

```agda
  T≡defSet : (φ : Formula ⟪ U ⟫ 1) → T 0 φ ≡ defSet φ
  T≡defSet φ = extensionality (T 0 φ) (defSet φ) (sub₁ , sub₂)
    where
    sub₁ : ⟨ T 0 φ ⊆ defSet φ ⟩
    sub₁ y y∈ₛ = ∈∈ₛ {a = y} {b = defSet φ} .fst
      (PT.rec (snd (y ∈ˢ defSet φ)) go
        (adeq-in 0 φ y (∈∈ₛ {a = y} {b = T 0 φ} .snd y∈ₛ)))
      where
      go : Σ[ δ ∈ Vec SM 1 ] (⟨ δ ⊨ᵐ φ ⟩ × (y ≡ Tup 0 δ)) → ⟨ y ∈ˢ defSet φ ⟩
      go ((v ∷ []) , sat , eq) =
        subst (λ w → ⟨ w ∈ˢ defSet φ ⟩) (fm .snd ∙ sym eq) mem
        where
        fm : Σ[ m ∈ ⟪ U ⟫ ] (⟪ U ⟫↪ m ≡ v .fst)
        fm = ∈-asFiber {a = v .fst} {b = U} (v .snd)
        ιm≡v : ι (fm .fst) ≡ v
        ιm≡v = Σ≡Prop (λ x → snd (x ∈ˢ U)) (fm .snd)
        sat' : ⟨ (ι (fm .fst) ∷ []) ⊨ᵐ φ ⟩
        sat' = subst (λ x → ⟨ (x ∷ []) ⊨ᵐ φ ⟩) (sym ιm≡v) sat
        mem : ⟨ ⟪ U ⟫↪ (fm .fst) ∈ˢ defSet φ ⟩
        mem = subst ⟨_⟩ (sym (defSet-mem φ (fm .fst))) sat'
    sub₂ : ⟨ defSet φ ⊆ T 0 φ ⟩
    sub₂ y y∈ₛ = ∈∈ₛ {a = y} {b = T 0 φ} .fst
      (subst (λ w → ⟨ w ∈ˢ T 0 φ ⟩) (fm .snd) inT)
      where
      y∈d : ⟨ y ∈ˢ defSet φ ⟩
      y∈d = ∈∈ₛ {a = y} {b = defSet φ} .snd y∈ₛ
      y∈U : ⟨ y ∈ˢ U ⟩
      y∈U = defSet⊆A φ y y∈d
      fm : Σ[ m ∈ ⟪ U ⟫ ] (⟪ U ⟫↪ m ≡ y)
      fm = ∈-asFiber {a = y} {b = U} y∈U
      sat : ⟨ (ι (fm .fst) ∷ []) ⊨ᵐ φ ⟩
      sat = subst ⟨_⟩ (defSet-mem φ (fm .fst))
              (subst (λ w → ⟨ w ∈ˢ defSet φ ⟩) (sym (fm .snd)) y∈d)
      inT : ⟨ ⟪ U ⟫↪ (fm .fst) ∈ˢ T 0 φ ⟩
      inT = adeq-set 0 φ (ι (fm .fst) ∷ []) sat

  defSet-InJ : (φ : Formula ⟪ U ⟫ 1) → InJ (defSet φ)
  defSet-InJ φ = subst InJ (T≡defSet φ) (hT 0 φ)
```

<!--en-->
## The full switch at limit levels

The abstract closure is discharged at the pair of limit levels the trunk cares
about, exactly as the delivered Δ₀ switch discharges it: the smaller level is the
transitive set the formula speaks about, the larger one is the closure it lands
in, and `Jset-rud`{.Agda} is the sixteen-operation fact. The statement is the
delivered `definable→closure`{.Agda} with the Δ₀ hypothesis deleted.
<!--zh-->
## 极限层处的完全切换

抽象闭包在主干所关心的那对极限层处兑付，方式与已交付的 Δ₀ 切换完全相同：较小的层是公式所谈论的传递集，较大的层是它落入的闭包，而 `Jset-rud`{.Agda} 就是十六运算的封闭事实。所得陈述就是已交付的 `definable→closure`{.Agda} 删去 Δ₀ 假设。
<!--/-->

```agda
module LimitFullSwitch (α : V ℓ) (limα : ⟨ isLimit α ⟩)
                       (β : V ℓ) (limβ : ⟨ isLimit β ⟩) (β∈α : ⟨ β ∈ˢ α ⟩) where

  Ju : V ℓ
  Ju = Jset β limβ

  Jα : V ℓ
  Jα = Jset α limα

  Ju∈Jα : ⟨ Ju ∈ˢ Jα ⟩
  Ju∈Jα = Sset-mem {α = α} {β = β} β∈α

  Jutrans : (x y : V ℓ) → ⟨ x ∈ˢ y ⟩ → ⟨ y ∈ˢ Ju ⟩ → ⟨ x ∈ˢ Ju ⟩
  Jutrans x y x∈y y∈U = Sset-trans β {x = y} {y = x} x∈y y∈U

  Jαtrans : (a b : V ℓ) → ⟨ b ∈ˢ Jα ⟩ → ⟨ a ∈ˢ b ⟩ → ⟨ a ∈ˢ Jα ⟩
  Jαtrans a b b∈ a∈b = Sset-trans α {x = b} {y = a} a∈b b∈

  module S = Sat Ju Jutrans (λ x → ⟨ x ∈ˢ Jα ⟩) Jαtrans (Jset-rud α limα) Ju∈Jα

  full-switch-⊇ : (φ : Formula ⟪ Ju ⟫ 1) → ⟨ DefOf.defSet Ju φ ∈ˢ Jα ⟩
  full-switch-⊇ φ = S.defSet-InJ φ
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The satisfaction sets are built and adequate. Three derived operations enter, each
sealed at birth with its specification inside: intersection as the double
difference (the D-7 excluded-middle spend), binary union, and the **range**, which
is the whole price of keeping the delivered right-nested tuple convention. Three
relations on the level carry every atom: membership is `F7`, the diagonal comes
from extensionality through two triple sets and a range, and the converse of
membership and the self-membership slice come from the diagonal by the same range
step. The coordinate families recurse on the arity rather than permuting
coordinates, so `F3` and `F4` do all the tuple plumbing. Adequacy is proved at a
tuple in both directions, which is where the once-proved decode-uniqueness
`Tup-inj`{.Agda} pays: no clause compares two decodes. At one free variable the
satisfaction set **is** `defSet φ`, and discharging the abstract closure at a pair
of limit levels gives the full switch for an arbitrary formula, the delivered Δ₀
switch with its Δ₀ hypothesis deleted.
<!--zh-->
满足集已造出且适足。进场的派生运算有三个，各自出生即封印、规格封在印内：作为二重差的交 (D-7 那笔排中律支出)、二元并，以及**值域**，后者就是保留已交付右嵌套元组约定的全部代价。层上的三个关系承载全部原子：隶属就是 `F7`，对角经两个三元组集与一次值域从外延性得出，隶属之逆与自隶属切片则经同一步值域从对角得出。坐标族按元数递归而非置换坐标，于是全部元组管道由 `F3` 与 `F4` 承担。适足在元组处双向证明，只证一次的解码唯一性 `Tup-inj`{.Agda} 正是在此兑现：没有任何子句需要比较两次解码。在一个自由变量处，满足集**就是** `defSet φ`，而把抽象闭包在一对极限层处兑付，便得到任意公式的完全切换，即已交付的 Δ₀ 切换删去其 Δ₀ 假设。
<!--/-->

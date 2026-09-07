<!--en-->
# Iterating a definable step through ω

Many later constructions close a set by repeating one definable operation finitely many times. This chapter carries out that ω-recursion inside `L` and packages the resulting sequence and union for reuse.
<!--zh-->
# 沿 ω 迭代可定义步骤

后续许多构造通过有限次重复一个可定义运算来闭合一个集合。本章在 `L` 内部执行这场 ω 递归，并封装所得序列及其并集以供复用。
<!--ja-->
# 定義可能な操作を ω に沿って反復する

後の多くの構成では、一つの定義可能な操作を有限回繰り返して集合を閉じる。本章ではその ω 再帰を `L` の内部で行い、得られる列とその合併を再利用できる形にまとめる。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.OmegaRecursion {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _⇒̇_; ∃̇_; ∀̇_ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj )
open import V.Model {ℓ} using ( pair-spec; union-spec; self∈sucV )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( #∈ω; ∈#-elim; boundingOrd )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Axioms.Basic {ℓ} using ( finSet; finSet-in; finSet-out; module FinOf )
open import L.Axioms.Numerals {ℓ}
  using ( pairʟ; pairʟ-fst; unionʟ; unionʟ-fst )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Recursion {ℓ} lem using ( Recursion; module Of; mereFunct ) renaming ( module Graph to RecursionGraph )
open import L.Coding.Model {ℓ} using ( appAt; appAt-adequate; prʟ; prʟ-fst )
open import L.Coding.Expressions {ℓ} using ( sucAtL; sucAtL-adequate; numL )

open import Cubical.Data.Nat.Order
  using ( _≤_; ≤-refl; ≤-trans; <-weaken; pred-≤-pred; suc-≤-suc )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.FinData.Properties using ( toℕ<n; fromℕ'; toFromId' )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_ )
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV; #_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

Renaming, read at the same satisfaction as `_⊨_` (as `OrderType` does).

```agda
module Ren = Sat (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ id

isSetS : isSet S
isSetS = isSetΣSndProp setIsSet (λ v → snd (isL v))

S≡ : {x y : S} → fst x ≡ fst y → x ≡ y
S≡ = Σ≡Prop (λ v → snd (isL v))
```

"The pair `(x, y)` is a member of `F`", the shape every clause below reads.

```agda
Holds : S → S → S → Type (ℓ-suc ℓ)
Holds F x y = ⟨ pr (fst x) (fst y) ∈ fst F ⟩
```

The numeral `k` as an element of L.

```agda
nn : ℕ → S
nn k = # k , numL k
```

Membership injections for the model's pair and union, and the union reader,
follow from the projection equations of src/L/Axioms/Numerals.lagda.md and the
hierarchy's specifications.

```agda
pairʟ-in : (a b y : S) → (fst y ≡ fst a) ⊎ (fst y ≡ fst b) → ⟨ y ∈ˢ pairʟ a b ⟩
pairʟ-in a b y k = subst (λ w → ⟨ fst y ∈ w ⟩) (sym (pairʟ-fst a b))
  (subst ⟨_⟩ (sym (pair-spec (fst a) (fst b) (fst y))) ∣ k ∣₁)

unionʟ-in : (A y B : S) → ⟨ fst B ∈ fst A ⟩ → ⟨ fst y ∈ fst B ⟩ → ⟨ y ∈ˢ unionʟ A ⟩
unionʟ-in A y B hB hy = subst (λ w → ⟨ fst y ∈ w ⟩) (sym (unionʟ-fst A))
  (subst ⟨_⟩ (sym (union-spec (fst A) (fst y))) ∣ fst B , (hB , hy) ∣₁)

unionʟ-out : (A y : S) → ⟨ y ∈ˢ unionʟ A ⟩
           → ∥ Σ[ B ∈ V ℓ ] (⟨ B ∈ fst A ⟩ × ⟨ fst y ∈ B ⟩) ∥₁
unionʟ-out A y h = subst ⟨_⟩ (union-spec (fst A) (fst y))
  (subst (λ w → ⟨ fst y ∈ w ⟩) (unionʟ-fst A) h)
```

The recursion. `a` is the start, `stepFo` defines `step` on the whole model (the
two directions of src/L/Recursion.lagda.md's `Definition`, with no domain
clause), and `it` is the iteration, in the host.

```agda
```

<!--en-->
## Finite iterates of a definable step

Starting at `a`, the value `it n` applies the step exactly `n` times. The graph formula records a finite table whose first row is `a` and whose successive rows satisfy the defining formula for the step.
<!--zh-->
## 可定义步骤的有限次迭代

从 `a` 出发，`it n` 恰好应用步骤 `n` 次。图公式记录一张有限表，其首行是 `a`，而每个后继行都满足步骤的定义公式。
<!--ja-->
## 定義可能な操作の有限反復

`a` から始め、`it n` は操作をちょうど `n` 回適用する。グラフ論理式は、先頭行が `a` で、各後者行が操作を定義する論理式を満たす有限表を記録する。
<!--/-->

```agda
module Iterate (a : S) (stepFo : Formula S 2) (step : S → S)
               (defines : (x : S) → ⟨ (step x ∷ x ∷ []) ⊨ stepFo ⟩)
               (only : (x y : S) → ⟨ (y ∷ x ∷ []) ⊨ stepFo ⟩ → y ≡ step x) where

  it : ℕ → S
  it zero    = a
  it (suc n) = step (it n)
```

Section 1. The approximation formula, and how to read it.

A set `F` of pairs is CORRECT when its entries at 0 are `a`, any two entries at
successive indices are related by the step, and every entry at `x'` has an entry
at each member of `x'`. No domain clause and no single-valuedness: section 2
shows every entry at a numeral is the iterate there, and section 3 builds one
correct set per `n`.

```agda
  Zero : S → Type (ℓ-suc ℓ)
  Zero F = (v : S) → Holds F (nn 0) v → fst v ≡ fst a

  Step : S → Type (ℓ-suc ℓ)
  Step F = (x v x' v' : S) → Holds F x v → Holds F x' v'
         → fst x' ≡ sucV (fst x) → ⟨ (v' ∷ v ∷ []) ⊨ stepFo ⟩

  Down : S → Type (ℓ-suc ℓ)
  Down F = (x' v' x : S) → Holds F x' v' → ⟨ fst x ∈ fst x' ⟩
         → ∥ Σ[ v ∈ S ] Holds F x v ∥₁

  Correct : S → Type (ℓ-suc ℓ)
  Correct F = Zero F × (Step F × Down F)
```

"Every entry of `f` at 0 is `a`." Inside: `z` is 0; then `v` is 0, `z` is 1.

```agda
  opaque
    zeroAt : ∀ {n} → Fin n → Formula S n
    zeroAt f = ∀̇ ( (var zero ≐ con (nn 0))
                 ⇒̇ ∀̇ ( appAt (suc (suc f)) (suc zero) zero ⇒̇ (var zero ≐ con a) ) )

    zero-out : ∀ {n} (f : Fin n) (γ : S ^ n) → ⟨ γ ⊨ zeroAt f ⟩ → Zero (lookup f γ)
    zero-out f γ h v hv = h (nn 0) refl v
      (subst ⟨_⟩ (sym (appAt-adequate (suc (suc f)) (suc zero) zero (v ∷ nn 0 ∷ γ))) hv)

    zero-in : ∀ {n} (f : Fin n) (γ : S ^ n) → Zero (lookup f γ) → ⟨ γ ⊨ zeroAt f ⟩
    zero-in f γ h z ez v hv = h v
      (subst (λ t → ⟨ pr t (fst v) ∈ fst (lookup f γ) ⟩) ez
        (subst ⟨_⟩ (appAt-adequate (suc (suc f)) (suc zero) zero (v ∷ z ∷ γ)) hv))
```

"Entries at `x` and at `x' = suc x` are related by the step." Inside: `x` is 3,
`v` is 2, `x'` is 1, `v'` is 0; the step formula reads `(v' ∷ v ∷ [])`.

```agda
  private
    ρ : ∀ {n} → Fin 2 → Fin (suc (suc (suc (suc n))))
    ρ zero       = zero
    ρ (suc zero) = suc (suc zero)

    ag : ∀ {n} (γ : S ^ n) (x v x' v' : S)
       → Ren.Agrees ρ (v' ∷ x' ∷ v ∷ x ∷ γ) (v' ∷ v ∷ [])
    ag γ x v x' v' zero       = refl
    ag γ x v x' v' (suc zero) = refl

  opaque
    stepAt : ∀ {n} → Fin n → Formula S n
    stepAt f = ∀̇ (∀̇ (∀̇ (∀̇ (
        appAt (suc (suc (suc (suc f)))) (suc (suc (suc zero))) (suc (suc zero))
      ⇒̇ ( appAt (suc (suc (suc (suc f)))) (suc zero) zero
      ⇒̇ ( sucAtL (suc (suc (suc zero))) (suc zero)
      ⇒̇ renameFo ρ stepFo ) ) ))))

    private
      gr : ∀ {n} (γ : S ^ n) (x v x' v' : S)
         → ⟨ (v' ∷ x' ∷ v ∷ x ∷ γ) ⊨ renameFo ρ stepFo ⟩ ≡ ⟨ (v' ∷ v ∷ []) ⊨ stepFo ⟩
      gr γ x v x' v' = cong ⟨_⟩
        (Ren.⊨-rename ρ stepFo (v' ∷ x' ∷ v ∷ x ∷ γ) (v' ∷ v ∷ []) (ag γ x v x' v'))

    step-out : ∀ {n} (f : Fin n) (γ : S ^ n) → ⟨ γ ⊨ stepAt f ⟩ → Step (lookup f γ)
    step-out f γ h x v x' v' p q s = transport (gr γ x v x' v')
      (h x v x' v'
        (subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc (suc f)))) (suc (suc (suc zero))) (suc (suc zero)) (v' ∷ x' ∷ v ∷ x ∷ γ))) p)
        (subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc (suc f)))) (suc zero) zero (v' ∷ x' ∷ v ∷ x ∷ γ))) q)
        (subst ⟨_⟩ (sym (sucAtL-adequate (suc (suc (suc zero))) (suc zero) (v' ∷ x' ∷ v ∷ x ∷ γ))) s))

    step-in : ∀ {n} (f : Fin n) (γ : S ^ n) → Step (lookup f γ) → ⟨ γ ⊨ stepAt f ⟩
    step-in f γ h x v x' v' p q s = transport (sym (gr γ x v x' v'))
      (h x v x' v'
        (subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc f)))) (suc (suc (suc zero))) (suc (suc zero)) (v' ∷ x' ∷ v ∷ x ∷ γ)) p)
        (subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc f)))) (suc zero) zero (v' ∷ x' ∷ v ∷ x ∷ γ)) q)
        (subst ⟨_⟩ (sucAtL-adequate (suc (suc (suc zero))) (suc zero) (v' ∷ x' ∷ v ∷ x ∷ γ)) s))
```

"Every entry at `x'` has an entry at each member `x` of `x'`." Inside: `x'` is
2, `v'` is 1, `x` is 0; then `v` is 0, `x` is 1, `x'` is 3.

```agda
  opaque
    downAt : ∀ {n} → Fin n → Formula S n
    downAt f = ∀̇ (∀̇ (∀̇ (
        appAt (suc (suc (suc f))) (suc (suc zero)) (suc zero)
      ⇒̇ ( (var zero ∈̇ var (suc (suc zero)))
      ⇒̇ ∃̇ (appAt (suc (suc (suc (suc f)))) (suc zero) zero) ) )))

    down-out : ∀ {n} (f : Fin n) (γ : S ^ n) → ⟨ γ ⊨ downAt f ⟩ → Down (lookup f γ)
    down-out f γ h x' v' x p m = PT.map
      (λ { (v , q) → v , subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc f)))) (suc zero) zero (v ∷ x ∷ v' ∷ x' ∷ γ)) q })
      (h x' v' x (subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc f))) (suc (suc zero)) (suc zero) (x ∷ v' ∷ x' ∷ γ))) p) m)

    down-in : ∀ {n} (f : Fin n) (γ : S ^ n) → Down (lookup f γ) → ⟨ γ ⊨ downAt f ⟩
    down-in f γ h x' v' x p m = PT.map
      (λ { (v , q) → v , subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc (suc f)))) (suc zero) zero (v ∷ x ∷ v' ∷ x' ∷ γ))) q })
      (h x' v' x (subst ⟨_⟩ (appAt-adequate (suc (suc (suc f))) (suc (suc zero)) (suc zero) (x ∷ v' ∷ x' ∷ γ)) p) m)

  opaque
    corrAt : ∀ {n} → Fin n → Formula S n
    corrAt f = zeroAt f ∧̇ (stepAt f ∧̇ downAt f)

    corr-out : ∀ {n} (f : Fin n) (γ : S ^ n) → ⟨ γ ⊨ corrAt f ⟩ → Correct (lookup f γ)
    corr-out f γ (z , (s , d)) = zero-out f γ z , (step-out f γ s , down-out f γ d)

    corr-in : ∀ {n} (f : Fin n) (γ : S ^ n) → Correct (lookup f γ) → ⟨ γ ⊨ corrAt f ⟩
    corr-in f γ (z , (s , d)) = zero-in f γ z , (step-in f γ s , down-in f γ d)
```

The graph formula, over `(y ∷ q ∷ [])`: "`y` is recorded at `q` by some correct
set". Inside: `F` is 0, `y` is 1, `q` is 2.

```agda
  opaque
    itFo : Formula S 2
    itFo = ∃̇ ( corrAt zero ∧̇ appAt zero (suc (suc zero)) (suc zero) )

    itFo-out : (y q : S) → ⟨ (y ∷ q ∷ []) ⊨ itFo ⟩
             → ∥ Σ[ F ∈ S ] (Correct F × Holds F q y) ∥₁
    itFo-out y q = PT.map (λ { (F , (hc , ha)) → F
      , ( corr-out zero (F ∷ y ∷ q ∷ []) hc
        , subst ⟨_⟩ (appAt-adequate zero (suc (suc zero)) (suc zero) (F ∷ y ∷ q ∷ [])) ha ) })

    itFo-in : (y q F : S) → Correct F → Holds F q y → ⟨ (y ∷ q ∷ []) ⊨ itFo ⟩
    itFo-in y q F hc hq = ∣ F
      , ( corr-in zero (F ∷ y ∷ q ∷ []) hc
        , subst ⟨_⟩ (sym (appAt-adequate zero (suc (suc zero)) (suc zero) (F ∷ y ∷ q ∷ []))) hq ) ∣₁
```

Transport of the graph formula along an equation of the index.

```agda
  itFo-at : (v : S) {x y : S} → x ≡ y
          → ⟨ (v ∷ x ∷ []) ⊨ itFo ⟩ → ⟨ (v ∷ y ∷ []) ⊨ itFo ⟩
  itFo-at v e = subst (λ t → ⟨ (v ∷ t ∷ []) ⊨ itFo ⟩) e
```

Section 2. Uniqueness: a correct set records the iterate at every numeral. One
induction on the numeral.

```agda
  corr-val : (F : S) → Correct F → (k : ℕ) (v : S)
           → Holds F (nn k) v → fst v ≡ fst (it k)
  corr-val F (z , (s , d)) zero    v h = z v h
  corr-val F (z , (s , d)) (suc k) v h =
    PT.rec (setIsSet (fst v) (fst (it (suc k)))) read
      (d (nn (suc k)) v (nn k) h (self∈sucV (# k)))
    where
    read : Σ[ u ∈ S ] Holds F (nn k) u → fst v ≡ fst (it (suc k))
    read (u , hu) = cong fst (only (it k) v
      (subst (λ t → ⟨ (v ∷ t ∷ []) ⊨ stepFo ⟩)
        (S≡ (corr-val F (z , (s , d)) k u hu))
        (s (nn k) u (nn (suc k)) v hu h refl)))

  itFo-val : (k : ℕ) (v : S) → ⟨ (v ∷ nn k ∷ []) ⊨ itFo ⟩ → fst v ≡ fst (it k)
  itFo-val k v h = PT.rec (setIsSet (fst v) (fst (it k)))
    (λ { (F , (hc , hv)) → corr-val F hc k v hv }) (itFo-out v (nn k) h)
```

Section 3. Existence: the finite table `{ (k, it k) : k ≤ n }` is the image of
`Fin (suc n)` under the entry map. All entries in the infinite family share one
stage bound, so the general finite-family theorem puts every such table in `L`.
The generic finite-set readers give its two membership directions directly.

```agda
  private
    e : ℕ → S
    e k = prʟ (nn k) (it k)

  private
    entryStages = boundingOrd (Lift {ℓ-zero} {ℓ} ℕ)
      (λ k → stage (fst (e (lower k))) (e (lower k) .snd))
      (λ k → stage-ord (fst (e (lower k))) (e (lower k) .snd))

    entryBound : V ℓ
    entryBound = entryStages .fst

    entryBound-ord : IsOrd entryBound
    entryBound-ord = entryStages .snd .fst

    entry-in-bound : (k : ℕ) → ⟨ fst (e k) ∈ Lset entryBound ⟩
    entry-in-bound k = Lset-mono (entryStages .snd .snd (lift k))
      (stage-mem (fst (e k)) (e k .snd))

  Fn : ℕ → S
  Fn n = finSet (suc n) (λ i → fst (e (toℕ i))) ,
    FinOf.finSetL entryBound entryBound-ord
      (suc n) (λ i → fst (e (toℕ i))) (λ i → entry-in-bound (toℕ i))

  Fn-in : (n k : ℕ) → k ≤ n → Holds (Fn n) (nn k) (it k)
  Fn-in n k p = subst (λ w → ⟨ w ∈ fst (Fn n) ⟩) (prʟ-fst (nn k) (it k))
    (finSet-in (suc n) (λ i → fst (e (toℕ i))) (fst (e k))
      ∣ fromℕ' (suc n) k (suc-≤-suc p)
      , cong (λ j → fst (e j)) (toFromId' (suc n) k (suc-≤-suc p)) ∣₁)

  Fn-out : (n : ℕ) (y : S) → ⟨ y ∈ˢ Fn n ⟩
         → ∥ Σ[ k ∈ ℕ ] ((k ≤ n) × (fst y ≡ pr (# k) (fst (it k)))) ∥₁
  Fn-out n y h = PT.map (λ { (i , q) → toℕ i
    , (pred-≤-pred (toℕ<n i) , sym q ∙ prʟ-fst (nn (toℕ i)) (it (toℕ i))) })
    (finSet-out (suc n) (λ i → fst (e (toℕ i))) (fst y) h)
```

A pair in the table, read as an index and a value.

```agda
  Fn-pair : (n : ℕ) (x v : S) → Holds (Fn n) x v
          → ∥ Σ[ k ∈ ℕ ] ((k ≤ n) × ((fst x ≡ # k) × (fst v ≡ fst (it k)))) ∥₁
  Fn-pair n x v h = PT.map (λ { (k , (p , q)) → k , (p , pr-inj (sym (prʟ-fst x v) ∙ q)) })
    (Fn-out n (prʟ x v) (subst (λ w → ⟨ w ∈ fst (Fn n) ⟩) (sym (prʟ-fst x v)) h))

  Fn-correct : (n : ℕ) → Correct (Fn n)
  Fn-correct n = zeroC , (stepC , downC)
    where
    zeroC : Zero (Fn n)
    zeroC v h = PT.rec (setIsSet (fst v) (fst a))
      (λ { (k , (_ , (ex , ev))) → ev ∙ cong (λ j → fst (it j)) (sym (#-inj 0 k ex)) })
      (Fn-pair n (nn 0) v h)

    stepC : Step (Fn n)
    stepC x v x' v' hxv hx'v' s = PT.rec (snd ((v' ∷ v ∷ []) ⊨ stepFo)) outer (Fn-pair n x v hxv)
      where
      outer : Σ[ k ∈ ℕ ] ((k ≤ n) × ((fst x ≡ # k) × (fst v ≡ fst (it k))))
            → ⟨ (v' ∷ v ∷ []) ⊨ stepFo ⟩
      outer (k , (_ , (ex , ev))) = PT.rec (snd ((v' ∷ v ∷ []) ⊨ stepFo)) inner (Fn-pair n x' v' hx'v')
        where
        inner : Σ[ k' ∈ ℕ ] ((k' ≤ n) × ((fst x' ≡ # k') × (fst v' ≡ fst (it k'))))
              → ⟨ (v' ∷ v ∷ []) ⊨ stepFo ⟩
        inner (k' , (_ , (ex' , ev'))) =
          subst2 (λ p q → ⟨ (p ∷ q ∷ []) ⊨ stepFo ⟩)
            (S≡ (sym (ev' ∙ cong (λ j → fst (it j)) k'≡)))
            (S≡ (sym ev))
            (defines (it k))
          where
          k'≡ : k' ≡ suc k
          k'≡ = #-inj k' (suc k) (sym ex' ∙ s ∙ cong sucV ex)

    downC : Down (Fn n)
    downC x' v' x h m = PT.rec squash₁ outer (Fn-pair n x' v' h)
      where
      outer : Σ[ k' ∈ ℕ ] ((k' ≤ n) × ((fst x' ≡ # k') × (fst v' ≡ fst (it k'))))
            → ∥ Σ[ v ∈ S ] Holds (Fn n) x v ∥₁
      outer (k' , (p' , (ex' , _))) = PT.map
        (λ { (j , (j< , ej)) → it j
           , subst (λ t → ⟨ pr t (fst (it j)) ∈ fst (Fn n) ⟩) (sym ej)
               (Fn-in n j (≤-trans (<-weaken j<) p')) })
        (∈#-elim k' (fst x) (subst (λ w → ⟨ fst x ∈ w ⟩) ex' m))
```

The graph formula holds of the iterate, at every numeral.

```agda
  it-graph : (k : ℕ) → ⟨ (it k ∷ nn k ∷ []) ⊨ itFo ⟩
  it-graph k = itFo-in (it k) (nn k) (Fn k) (Fn-correct k) (Fn-in k k ≤-refl)
```

Section 4. The tables: the values, their union, and the graph, in L.

```agda
  Num : S → Type (ℓ-suc ℓ)
  Num q = Σ[ k ∈ ℕ ] (nn k ≡ q)

  ω-num : (q : S) → ⟨ q ∈ˢ ωʟ ⟩ → ∥ Num q ∥₁
  ω-num q = PT.map (λ { (i , p) → lower i , S≡ p })

  private
    valR : Recursion
    valR = record
      { dom   = ωʟ
      ; graph = itFo
      ; funct = λ q q∈ → mereFunct itFo q (PT.map (wit q) (ω-num q q∈)) }
      where
      wit : (q : S) → Num q
          → Σ[ y ∈ S ] (⟨ (y ∷ q ∷ []) ⊨ itFo ⟩
                       × ((y' : S) → ⟨ (y' ∷ q ∷ []) ⊨ itFo ⟩ → y' ≡ y))
      wit q (k , eq) = it k
        , ( itFo-at (it k) eq (it-graph k)
          , λ y' h → S≡ (itFo-val k y' (itFo-at y' (sym eq) h)) )

    module VR = Of valR

  values : S
  values = VR.table

  values-in : (n : ℕ) → ⟨ fst (it n) ∈ fst values ⟩
  values-in n = VR.table-in (nn n) (it n) (#∈ω n) (it-graph n)

  values-out : (y : S) → ⟨ y ∈ˢ values ⟩ → ∥ Σ[ n ∈ ℕ ] (fst y ≡ fst (it n)) ∥₁
  values-out y hy = PT.rec squash₁
    (λ { (q , (q∈ , h)) → PT.map
      (λ { (k , eq) → k , itFo-val k y (itFo-at y (sym eq) h) }) (ω-num q q∈) })
    (VR.table-out y hy)

  iterUnion : S
  iterUnion = unionʟ values

  iterUnion-in : (n : ℕ) (z : S) → ⟨ fst z ∈ fst (it n) ⟩ → ⟨ z ∈ˢ iterUnion ⟩
  iterUnion-in n z hz = unionʟ-in values z (it n) (values-in n) hz

  iterUnion-out : (z : S) → ⟨ z ∈ˢ iterUnion ⟩ → ∥ Σ[ n ∈ ℕ ] ⟨ fst z ∈ fst (it n) ⟩ ∥₁
  iterUnion-out z h = PT.rec squash₁
    (λ { (B , (hB , hz)) → PT.map
      (λ { (n , eB) → n , subst (λ w → ⟨ fst z ∈ w ⟩) eB hz })
      (values-out (B , isL-trans {x = fst values} {y = B} hB (snd values)) hB) })
    (unionʟ-out values z h)
```

<!--en-->
## Collecting the ω-sequence inside L

Replacement gathers all finite iterates into a single graph indexed by `ω`. Its range and union therefore belong to `L`, providing the internal ω-closure used for Skolem hulls.
<!--zh-->
## 在 L 内收集 ω 序列

替换把全部有限次迭代收集成一张以 `ω` 为指标的图。因此其值域与并集都属于 `L`，给出 Skolem 壳所用的内部 ω 闭包。
<!--ja-->
## L の内部で ω 列を集める

置換により、すべての有限反復を `ω` で添字付けた一つのグラフへ集める。その値域と合併は `L` に属し、Skolem 包に用いる内部 ω 閉包を与える。
<!--/-->

The graph `{ (n, it n) : n ∈ ℕ }` is the graph of the same value recursion.
Its uniqueness identifies each recorded value with the corresponding iterate.

```agda
  private
    module TR = RecursionGraph valR using ( F; F-in; F-out )

  iter : S
  iter = TR.F

  iter-in : (n : ℕ) → ⟨ pr (# n) (fst (it n)) ∈ fst iter ⟩
  iter-in n = subst (λ v → ⟨ pr (# n) (fst v) ∈ fst iter ⟩)
    (VR.val-uniq (nn n) (#∈ω n) (it n) (it-graph n)) (TR.F-in (nn n) (#∈ω n))

  iter-out : (y : S) → ⟨ y ∈ˢ iter ⟩ → ∥ Σ[ n ∈ ℕ ] (fst y ≡ pr (# n) (fst (it n))) ∥₁
  iter-out y hy = PT.rec squash₁
    (λ { (q , q∈ , e) → PT.map (λ { (k , eq) → k
      , e ∙ cong₂ pr (cong fst (sym eq))
        (cong fst (VR.val-uniq q q∈ (it k) (itFo-at (it k) eq (it-graph k)))) }) (ω-num q q∈) })
    (TR.F-out (fst y) hy)
```

Section 5. One instance: a step that only grows. The union starts at `a`, every
stage sits below the next, and the step of any set bounded by a stage lands
inside the union.

```agda
  module Closure (grows : (x z : S) → ⟨ fst z ∈ fst x ⟩ → ⟨ fst z ∈ fst (step x) ⟩) where

    it-mono : (n : ℕ) (z : S) → ⟨ fst z ∈ fst (it n) ⟩ → ⟨ fst z ∈ fst (it (suc n)) ⟩
    it-mono n z = grows (it n) z

    it-up : (n k : ℕ) (z : S) → ⟨ fst z ∈ fst (it n) ⟩ → ⟨ fst z ∈ fst (it (k + n)) ⟩
    it-up n zero    z h = h
    it-up n (suc k) z h = it-mono (k + n) z (it-up n k z h)
```

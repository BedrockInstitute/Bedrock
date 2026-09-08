<!--en-->
# Coding finite sequences below an infinite ordinal

For an infinite ordinal, finitely many entries can be folded into one code without leaving the ordinal. This chapter constructs the set of finite sequences, defines the fold from a coded pairing, and proves the resulting internal injection.
<!--zh-->
# 在无穷序数以下编码有限序列

对一个无穷序数，可以把有限多个元素折叠成一个编码而不离开该序数。本章构造有限序列集，从编码配对定义折叠，并证明所得的内部单射。
<!--ja-->
# 無限順序数の下で有限列をコード化する

無限順序数では、有限個の要素を順序数の外へ出ることなく一つのコードへ畳み込める。本章では有限列の集合を構成し、コード化された対関数から畳み込みを定義して、得られる内部単射を示す。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.FiniteSequenceCoding {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _≐_; _∧̇_; ∃̇_; ∀̇∈; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; regularityV )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′; #mono )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Ordinal {ℓ} using ( #∈ω; ∈#-elim )
open import L.Axioms.Basic {ℓ} using ( extensionalL )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Coding.Model {ℓ} using ( prAtL; prAtL-adequate; prʟ; prʟ-fst; svAt; svAt-out; domAt; domAt-in; domAt-out; domAt-intro; appAt; appAt-adequate; envOverAt; envOver-sv; envOver-dom; envOverAt-transport )
open import L.Coding.Expressions {ℓ} using ( numL; sucAtL; sucAtL-adequate )
open import L.Coding.Injection {ℓ} lem using ( injAt; module Extract )
open import L.Coding.Environment {ℓ} using ( lookup-spec )
open import L.Coding.EnvironmentSet {ℓ} lem
  using ( Ix; envS; envOver; envSet; envSet-in; envSet-out; module Recover )
open import L.Recursion {ℓ} lem using ( Recursion; module Of; mereFunct; smallDom )
open import L.Cardinal {ℓ} lem using ( InjL; IsCardinalL )
open import L.InjectionComposition {ℓ} lem using ( injl-trans )
open import L.GCH.CardinalRepresentative {ℓ} lem using ( cardOf )
open import L.DefinableInjection {ℓ} lem using ( DefinableMap; module Inj )
open import L.GCH.CardinalSquareLaw {ℓ} lem
  using ( prodL; prodL-in; Goal; module Step; prod-inj; no-fin; ω⊆ )
open import L.InjectionComposition {ℓ} lem using ( appC; appC-adequate )

open import Cubical.Data.Nat.Order
  using ( _<_; ≤-refl; ≤-suc; suc-≤-suc; pred-≤-pred; ¬-<-zero; <-split; zero-≤ )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.FinData.Properties using ( toℕ<n; fromℕ'; toFromId' )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV; #_ )
import Cubical.Induction.WellFounded as WF
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
```

The V-carrier: the ambient membership lives here.

```agda
module SV = hPropStructure 𝒮ᵥ using ()
```

The L-carrier: `InjL` lives here.

```agda
module SL = hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open SL using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

The numeral `k` as an element of L.

```agda
nn : ℕ → S
nn k = # k , numL k
```

<!--en-->
## Collecting all finite sequences over a set

`seqL A` is the union of the environment sets of every finite length. A bounded description recognizes precisely those environments, so when `A` belongs to `L`, the entire collection is one set of `L`.
<!--zh-->
## 收集一个集合上的全部有限序列

`seqL A` 是所有有限长度环境集的并集。一条有界描述恰好识别这些环境，因此当 `A` 属于 `L` 时，整个集合也是 `L` 中的一个集合。
<!--ja-->
## 集合上のすべての有限列を集める

`seqL A` は、すべての有限長の環境集合の合併である。有界な記述がちょうどそれらの環境を認識するので、`A` が `L` に属すれば、全体も `L` の一つの集合になる。
<!--/-->

`seqL A` is the union over `n` of `envSet A n`: the environments of every finite
length over `A`. It is carved by separation out of a stage that contains every
`envS A g` (`smallDom`), with the one-place description "`x` is an environment
over `A` whose domain is a member of `ω`". Inside the two binders: `b` is 0,
`n` is 1, `x` is 2.

```agda
SeqIx : S → Type ℓ
SeqIx A = Σ[ n ∈ ℕ ] Ix A n

private
  amb : (A : S) → S
  amb A = smallDom (SeqIx A) (λ p → envS A (snd p)) .fst

  amb-in : (A : S) (p : SeqIx A) → ⟨ fst (envS A (snd p)) ∈ˢ fst (amb A) ⟩
  amb-in A = smallDom (SeqIx A) (λ p → envS A (snd p)) .snd

seqFo : S → Formula S 1
seqFo A = ∃̇∈ (con ωʟ) (∃̇ ( (var zero ≐ con A)
                        ∧̇ envOverAt (suc (suc zero)) (suc zero) zero ))

opaque
  seqL : S → S
  seqL A = hasSeparationL (amb A) (seqFo A) .fst .fst

  seqL-spec : (A x : S) → (x SL.∈ˢ seqL A)
            ≡ ((x SL.∈ˢ amb A) ⊓ ((x ∷ []) ⊨ seqFo A))
  seqL-spec A = hasSeparationL (amb A) (seqFo A) .fst .snd

seqL-in : (A : S) (n : ℕ) (x : S)
        → ⟨ fst x ∈ˢ fst (envSet A n) ⟩ → ⟨ fst x ∈ˢ fst (seqL A) ⟩
seqL-in A n x hx = PT.rec (snd (fst x ∈ˢ fst (seqL A))) from (envSet-out A n x hx)
  where
  from : Σ[ g ∈ Ix A n ] (fst x ≡ fst (envS A g)) → ⟨ fst x ∈ˢ fst (seqL A) ⟩
  from (g , e) = subst (λ w → ⟨ w ∈ˢ fst (seqL A) ⟩) (sym e) canonical
    where
    canonical : ⟨ fst (envS A g) ∈ˢ fst (seqL A) ⟩
    canonical = subst ⟨_⟩ (sym (seqL-spec A (envS A g)))
      ( amb-in A (n , g)
      , ∣ nn n , (#∈ω n , ∣ A , (refl , envOver A g) ∣₁) ∣₁ )

seqL-out : (A x : S) → ⟨ fst x ∈ˢ fst (seqL A) ⟩
         → ∥ Σ[ n ∈ ℕ ] ⟨ fst x ∈ˢ fst (envSet A n) ⟩ ∥₁
seqL-out A x hx = PT.rec squash₁ step1 (subst ⟨_⟩ (seqL-spec A x) hx .snd)
  where
  step2 : (d : S) (k : ℕ) → # k ≡ fst d
        → Σ[ b ∈ S ] ((fst b ≡ fst A)
             × ⟨ (b ∷ d ∷ x ∷ []) ⊨ envOverAt (suc (suc zero)) (suc zero) zero ⟩)
        → ∥ Σ[ n ∈ ℕ ] ⟨ fst x ∈ˢ fst (envSet A n) ⟩ ∥₁
  step2 d k q (b , eb , hov) =
    ∣ k , subst (λ w → ⟨ w ∈ˢ fst (envSet A k) ⟩) (sym R.recovers) (envSet-in A R.g) ∣₁
    where
    module R = Recover A k (b ∷ d ∷ x ∷ []) (suc (suc zero)) (suc zero) zero
                 (sym q) eb hov using ( g; recovers )

  step1 : Σ[ d ∈ S ] (⟨ fst d ∈ˢ ω ⟩
            × ∥ Σ[ b ∈ S ] ((fst b ≡ fst A)
                 × ⟨ (b ∷ d ∷ x ∷ []) ⊨ envOverAt (suc (suc zero)) (suc zero) zero ⟩) ∥₁)
        → ∥ Σ[ n ∈ ℕ ] ⟨ fst x ∈ˢ fst (envSet A n) ⟩ ∥₁
  step1 (d , d∈ω , h) = PT.rec squash₁
    (λ { (k , q) → PT.rec squash₁ (step2 d (lower k) q) h }) d∈ω
```

<!--en-->
## Folding a finite sequence into one ordinal code

Given a coded pairing on an infinite ordinal `α`, a sequence is folded from left to right and then paired with its length. The graph formula records the finite chain of intermediate values, which makes the coding function definable inside `L`.
<!--zh-->
## 把有限序列折叠成一个序数码

给定无穷序数 `α` 上的编码配对，先从左到右折叠序列，再把结果与长度配对。图公式记录中间值的有限链，从而使编码函数在 `L` 内部可定义。
<!--ja-->
## 有限列を一つの順序数コードへ畳み込む

無限順序数 `α` 上の符号化された対関数から、列を左から右へ畳み込み、最後に長さと対にする。グラフの論理式が中間値の有限列を記録するので、符号化関数は `L` の内部で定義可能になる。
<!--/-->

A sequence `s` of length `n` is coded by folding `F` along it and then tagging
with the length: `c(s) = F(n, v_n)` where `v_0 = 0` and
`v_{i+1} = F(s(i), v_i)`. The graph of `s ↦ c(s)` is expressible: "there is a
finite chain `C`, an environment over `α` on the domain `n + 1`, with
`C(0) = 0`, `C(i+1) = F(s(i), C(i))` for every `i ∈ n`, and `c = F(n, C(n))`".
The fold is host recursion; the formula is read in both directions, and
`Definable.Inj` codes the injection.

```agda
module Code (α : S) (oα : IsOrd (fst α)) (α∉ω : ⟨ fst α ∈ˢ ω ⟩ → Empty.⊥)
            (F : S)
            (sv : ⟨ (F ∷ prodL α ∷ []) ⊨ svAt zero ⟩)
            (dm : ⟨ (F ∷ prodL α ∷ []) ⊨ domAt zero (suc zero) ⟩)
            (ij : ⟨ (F ∷ prodL α ∷ []) ⊨ injAt zero ⟩)
            (ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩
                 → ⟨ fst y ∈ fst α ⟩) where
```

2.1 Members of `α`, and the pairing read as a function.

```agda
  M : Type (ℓ-suc ℓ)
  M = Σ[ v ∈ S ] ⟨ fst v ∈ˢ fst α ⟩

  num : ℕ → M
  num k = nn k , ω⊆ (fst α) oα α∉ω (# k) (#∈ω k)

  up : ⟪ fst α ⟫ → M
  up m = (⟪ fst α ⟫↪ m , isL-trans (member (fst α) m) (snd α)) , member (fst α) m

  module E = Extract F (prodL α) sv dm using ( toFun; toFun-graph; toFun-inj )
```

Sealed: a proof of a proposition, never to be unfolded in a conversion (measured
at this site: unsealed, `chain n g (suc k)` against `app (ext n g k) (chain n g
k)` exhausts an 8g heap).

```agda
  opaque
    pairMem : (a u : M) → ⟨ fst (prʟ (fst a) (fst u)) ∈ˢ fst (prodL α) ⟩
    pairMem a u = subst (λ w → ⟨ w ∈ˢ fst (prodL α) ⟩) (sym (prʟ-fst (fst a) (fst u)))
                    (prodL-in α (fst a) (fst u) (snd a) (snd u))
```

Sealed with its two readings, as `Pairing.ProdMap.val` is.

```agda
  opaque
    val : (x : S) → ⟨ fst x ∈ˢ fst (prodL α) ⟩ → S
    val x mx = E.toFun (x , mx)

    val-graph : (x : S) (mx : ⟨ fst x ∈ˢ fst (prodL α) ⟩)
              → ⟨ pr (fst x) (fst (val x mx)) ∈ fst F ⟩
    val-graph x mx = E.toFun-graph (x , mx)

    val-inj : (x : S) (mx : ⟨ fst x ∈ˢ fst (prodL α) ⟩)
              (x' : S) (mx' : ⟨ fst x' ∈ˢ fst (prodL α) ⟩)
            → fst (val x mx) ≡ fst (val x' mx') → fst x ≡ fst x'
    val-inj x mx x' mx' = E.toFun-inj ij (x , mx) (x' , mx')
```

Sealed with its three facts, for the same reason.

```agda
  opaque
    app : M → M → M
    app a u = val (prʟ (fst a) (fst u)) (pairMem a u)
            , ran (prʟ (fst a) (fst u)) (val (prʟ (fst a) (fst u)) (pairMem a u))
                (val-graph (prʟ (fst a) (fst u)) (pairMem a u))

    app-graph : (a u : M)
              → ⟨ pr (pr (fst (fst a)) (fst (fst u))) (fst (fst (app a u))) ∈ fst F ⟩
    app-graph a u = subst (λ w → ⟨ pr w (fst (fst (app a u))) ∈ fst F ⟩)
                      (prʟ-fst (fst a) (fst u))
                      (val-graph (prʟ (fst a) (fst u)) (pairMem a u))

    app-inj : (a u a' u' : M) → fst (fst (app a u)) ≡ fst (fst (app a' u'))
            → (fst (fst a) ≡ fst (fst a')) × (fst (fst u) ≡ fst (fst u'))
    app-inj a u a' u' e = pr-inj
      (sym (prʟ-fst (fst a) (fst u))
       ∙ val-inj (prʟ (fst a) (fst u)) (pairMem a u) (prʟ (fst a') (fst u')) (pairMem a' u') e
       ∙ prʟ-fst (fst a') (fst u'))
```

`F` is single-valued: any value recorded at the pair is the value.

```agda
    app-uniq : (a u : M) (w : S)
             → ⟨ pr (pr (fst (fst a)) (fst (fst u))) (fst w) ∈ fst F ⟩
             → fst w ≡ fst (fst (app a u))
    app-uniq a u w h =
      svAt-out zero (F ∷ prodL α ∷ []) sv (prʟ (fst a) (fst u)) w (fst (app a u))
        (subst (λ z → ⟨ pr z (fst w) ∈ fst F ⟩) (sym (prʟ-fst (fst a) (fst u))) h)
        (val-graph (prʟ (fst a) (fst u)) (pairMem a u))
```

2.2 The fold, by host recursion on the length, and its injectivity.

The sequence extended to every natural index, with a junk value past its length.

```agda
  ext : (n : ℕ) → (Fin n → ⟪ fst α ⟫) → ℕ → M
  ext zero    g k       = num zero
  ext (suc n) g zero    = up (g zero)
  ext (suc n) g (suc k) = ext n (λ i → g (suc i)) k

  ext-at : (n : ℕ) (g : Fin n → ⟪ fst α ⟫) (i : Fin n) → ext n g (toℕ i) ≡ up (g i)
  ext-at (suc n) g zero    = refl
  ext-at (suc n) g (suc i) = ext-at n (λ j → g (suc j)) i

  chain : (n : ℕ) → (Fin n → ⟪ fst α ⟫) → ℕ → M
  chain n g zero    = num zero
  chain n g (suc k) = app (ext n g k) (chain n g k)

  code : (n : ℕ) → (Fin n → ⟪ fst α ⟫) → M
  code n g = app (num n) (chain n g n)
```

Injectivity of the fold, by downward induction on the length.

```agda
  chain-inj : (n : ℕ) (g g' : Fin n → ⟪ fst α ⟫) (k : ℕ)
            → fst (fst (chain n g k)) ≡ fst (fst (chain n g' k))
            → (j : ℕ) → j < k → fst (fst (ext n g j)) ≡ fst (fst (ext n g' j))
  chain-inj n g g' zero    e j j<0  = Empty.rec (¬-<-zero j<0)
  chain-inj n g g' (suc k) e j j<sk = go (<-split j<sk)
    where
    q = app-inj (ext n g k) (chain n g k) (ext n g' k) (chain n g' k) e
    go : (j < k) ⊎ (j ≡ k) → fst (fst (ext n g j)) ≡ fst (fst (ext n g' j))
    go (inl j<k) = chain-inj n g g' k (snd q) j j<k
    go (inr j≡k) = subst (λ j → fst (fst (ext n g j)) ≡ fst (fst (ext n g' j))) (sym j≡k) (fst q)

  code-inj : (n : ℕ) (g : Fin n → ⟪ fst α ⟫) (n' : ℕ) (g' : Fin n' → ⟪ fst α ⟫)
           → fst (fst (code n g)) ≡ fst (fst (code n' g'))
           → fst (envS α g) ≡ fst (envS α g')
  code-inj n g n' g' e = subst P (#-inj′ (fst q)) same g' (snd q)
    where
    q = app-inj (num n) (chain n g n) (num n') (chain n' g' n') e
    P : ℕ → Type (ℓ-suc ℓ)
    P m = (h : Fin m → ⟪ fst α ⟫)
        → fst (fst (chain n g n)) ≡ fst (fst (chain m h m))
        → fst (envS α g) ≡ fst (envS α h)
    same : P n
    same h e' = cong (λ (f : Fin n → ⟪ fst α ⟫) → fst (envS α f)) (funExt pt)
      where
      pt : (i : Fin n) → g i ≡ h i
      pt i = ↪-inj {a = fst α}
        ( sym (cong (λ z → fst (fst z)) (ext-at n g i))
        ∙ chain-inj n g h n e' (toℕ i) (toℕ<n i)
        ∙ cong (λ z → fst (fst z)) (ext-at n h i) )
```

2.3 The graph, in the object language, and its host reading.

Over `(y ∷ s ∷ [])`. Outer binders: `n ∈ ω`, then `m`, `C`, `b`, `z`, so that
`z` is 0, `b` is 1, `C` is 2, `m` is 3, `n` is 4, `y` is 5, `s` is 6. The step
clause binds `i ∈ n`, then `j`, then `a`, `u`, `w`, `p`: `p` is 0, `w` is 1, `u`
is 2, `a` is 3, `j` is 4, `i` is 5, and the outer seven shift by 6. The final
clause binds `v` then `q`: `q` is 0, `v` is 1, shift by 2.

```agda
  StepAt : (s C i : S) → Type (ℓ-suc ℓ)
  StepAt s C i = ∥ Σ[ j ∈ S ] Σ[ a ∈ S ] Σ[ u ∈ S ] Σ[ w ∈ S ]
      ( (fst j ≡ sucV (fst i))
      × ⟨ pr (fst i) (fst a) ∈ fst s ⟩
      × ⟨ pr (fst i) (fst u) ∈ fst C ⟩
      × ⟨ pr (fst j) (fst w) ∈ fst C ⟩
      × ⟨ pr (pr (fst a) (fst u)) (fst w) ∈ fst F ⟩ ) ∥₁

  DomIs : (s n : S) → Type (ℓ-suc ℓ)
  DomIs s n = (x : S)
    → (⟨ fst x ∈ fst n ⟩ → ∥ Σ[ y ∈ S ] ⟨ pr (fst x) (fst y) ∈ fst s ⟩ ∥₁)
    × ((y : S) → ⟨ pr (fst x) (fst y) ∈ fst s ⟩ → ⟨ fst x ∈ fst n ⟩)

  EnvC : (m C : S) → Type (ℓ-suc ℓ)
  EnvC m C = ⟨ (α ∷ m ∷ C ∷ []) ⊨ envOverAt (suc (suc zero)) (suc zero) zero ⟩

  Wit : (y s : S) → Type (ℓ-suc ℓ)
  Wit y s = ∥ Σ[ n ∈ S ] Σ[ m ∈ S ] Σ[ C ∈ S ]
      ( ⟨ fst n ∈ ω ⟩
      × (fst m ≡ sucV (fst n))
      × DomIs s n
      × EnvC m C
      × ⟨ pr (# zero) (# zero) ∈ fst C ⟩
      × ((i : S) → ⟨ fst i ∈ fst n ⟩ → StepAt s C i)
      × ∥ Σ[ v ∈ S ] ( ⟨ pr (fst n) (fst v) ∈ fst C ⟩
                     × ⟨ pr (pr (fst n) (fst v)) (fst y) ∈ fst F ⟩ ) ∥₁ ) ∥₁

  private
    i0 : ∀ {k} → Fin (suc k)
    i0 = zero
    i1 : ∀ {k} → Fin (suc (suc k))
    i1 = suc i0
    i2 : ∀ {k} → Fin (suc (suc (suc k)))
    i2 = suc i1
    i3 : ∀ {k} → Fin (suc (suc (suc (suc k))))
    i3 = suc i2
    i4 : ∀ {k} → Fin (suc (suc (suc (suc (suc k)))))
    i4 = suc i3
    i5 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc k))))))
    i5 = suc i4
    i6 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc (suc k)))))))
    i6 = suc i5
    i7 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc (suc (suc k))))))))
    i7 = suc i6
    i8 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc k)))))))))
    i8 = suc i7
    i12 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc k)))))))))))))
    i12 = suc (suc (suc (suc i8)))

  opaque
    private
      stepFo : Formula S 8
      stepFo = ∃̇ (
            sucAtL i1 i0
         ∧̇ (∃̇ (∃̇ (∃̇ (∃̇ (
              appAt i12 i5 i3
           ∧̇ appAt i8 i5 i2
           ∧̇ appAt i8 i4 i1
           ∧̇ prAtL i0 i3 i2
           ∧̇ appC F i0 i1 ))))))

      finFo : Formula S 7
      finFo = ∃̇ (∃̇ (
            appAt i4 i6 i1
         ∧̇ prAtL i0 i6 i1
         ∧̇ appC F i0 i7 ))

      body : Formula S 7
      body =
          (var i1 ≐ con α)
       ∧̇ (var i0 ≐ con (nn zero))
       ∧̇ sucAtL i4 i3
       ∧̇ domAt i6 i4
       ∧̇ envOverAt i2 i3 i1
       ∧̇ appAt i2 i0 i0
       ∧̇ ∀̇∈ (var i4) stepFo
       ∧̇ finFo

    fo : Formula S 2
    fo = ∃̇∈ (con ωʟ) (∃̇ (∃̇ (∃̇ (∃̇ body))))

    private
      e7 : S → S → S → S → S → S → S → S ^ 7
      e7 y s n m C b z = z ∷ b ∷ C ∷ m ∷ n ∷ y ∷ s ∷ []

      stepOut : (y s n m C b z i : S)
              → ⟨ (i ∷ e7 y s n m C b z) ⊨ stepFo ⟩ → StepAt s C i
      stepOut y s n m C b z i = PT.rec squash₁ (λ { (j , (ej , ha)) →
        PT.rec squash₁ (λ { (a , hu) → PT.rec squash₁ (λ { (u , hw) →
        PT.rec squash₁ (λ { (w , hp) → PT.rec squash₁ (λ { (p , (h1 , (h2 , (h3 , (h4 , h5))))) →
          let γ = p ∷ w ∷ u ∷ a ∷ j ∷ i ∷ e7 y s n m C b z in
          ∣ j , a , u , w
          , ( subst ⟨_⟩ (sucAtL-adequate i1 i0 (j ∷ i ∷ e7 y s n m C b z)) ej
            , subst ⟨_⟩ (appAt-adequate i12 i5 i3 γ) h1
            , subst ⟨_⟩ (appAt-adequate i8 i5 i2 γ) h2
            , subst ⟨_⟩ (appAt-adequate i8 i4 i1 γ) h3
            , subst (λ q → ⟨ pr q (fst w) ∈ fst F ⟩)
                (subst ⟨_⟩ (prAtL-adequate i0 i3 i2 γ) h4)
                (subst ⟨_⟩ (appC-adequate F i0 i1 γ) h5) ) ∣₁ }) hp }) hw }) hu }) ha })

      finOut : (y s n m C b z : S) → ⟨ e7 y s n m C b z ⊨ finFo ⟩
             → ∥ Σ[ v ∈ S ] ( ⟨ pr (fst n) (fst v) ∈ fst C ⟩
                            × ⟨ pr (pr (fst n) (fst v)) (fst y) ∈ fst F ⟩ ) ∥₁
      finOut y s n m C b z = PT.rec squash₁ (λ { (v , hq) →
        PT.rec squash₁ (λ { (q , (h1 , (h2 , h3))) →
          let γ = q ∷ v ∷ e7 y s n m C b z in
          ∣ v , ( subst ⟨_⟩ (appAt-adequate i4 i6 i1 γ) h1
                , subst (λ r → ⟨ pr r (fst y) ∈ fst F ⟩)
                    (subst ⟨_⟩ (prAtL-adequate i0 i6 i1 γ) h2)
                    (subst ⟨_⟩ (appC-adequate F i0 i7 γ) h3) ) ∣₁ }) hq })
```

The body is read by a function with a stated type, not by a pattern lambda under
`PT.rec`. Measured at this site: the pattern-lambda form exceeded 40 s and 6 GB;
this form checks in under 7 s.

```agda
      bodyOut : (y s n m C b z : S) → ⟨ fst n ∈ ω ⟩
              → ⟨ e7 y s n m C b z ⊨ body ⟩ → Wit y s
      bodyOut y s n m C b z n∈ω (eb , (ez , (em , (hd , (hE , (h0 , (hS , hF))))))) =
        ∣ n , m , C
        , ( n∈ω
          , subst ⟨_⟩ (sucAtL-adequate i4 i3 (e7 y s n m C b z)) em
          , (λ x → domAt-in i6 i4 (e7 y s n m C b z) hd x
                 , domAt-out i6 i4 (e7 y s n m C b z) hd x)
          , envOverAt-transport (e7 y s n m C b z) (α ∷ m ∷ C ∷ [])
              i2 i3 i1 (suc (suc zero)) (suc zero) zero refl refl eb hE
          , subst (λ w → ⟨ pr w w ∈ fst C ⟩) ez
              (subst ⟨_⟩ (appAt-adequate i2 i0 i0 (e7 y s n m C b z)) h0)
          , (λ i i∈n → stepOut y s n m C b z i (hS i i∈n))
          , finOut y s n m C b z hF ) ∣₁

    fo-out : (y s : S) → ⟨ (y ∷ s ∷ []) ⊨ fo ⟩ → Wit y s
    fo-out y s = PT.rec squash₁ (λ { (n , (n∈ω , hm)) →
      PT.rec squash₁ (λ { (m , hC) → PT.rec squash₁ (λ { (C , hb) →
      PT.rec squash₁ (λ { (b , hz) → PT.rec squash₁ (λ { (z , hbody) →
        bodyOut y s n m C b z n∈ω hbody }) hz }) hb }) hC }) hm })

    private
      stepIn : (y s n m C i : S) → StepAt s C i
             → ⟨ (i ∷ e7 y s n m C α (nn zero)) ⊨ stepFo ⟩
      stepIn y s n m C i = PT.map (λ { (j , a , u , w , (ej , ha , hu , hw , hF)) →
        let γ = prʟ a u ∷ w ∷ u ∷ a ∷ j ∷ i ∷ e7 y s n m C α (nn zero) in
        j , ( subst ⟨_⟩ (sym (sucAtL-adequate i1 i0 (j ∷ i ∷ e7 y s n m C α (nn zero)))) ej
            , ∣ a , ∣ u , ∣ w , ∣ prʟ a u
            , ( subst ⟨_⟩ (sym (appAt-adequate i12 i5 i3 γ)) ha
              , ( subst ⟨_⟩ (sym (appAt-adequate i8 i5 i2 γ)) hu
              , ( subst ⟨_⟩ (sym (appAt-adequate i8 i4 i1 γ)) hw
              , ( subst ⟨_⟩ (sym (prAtL-adequate i0 i3 i2 γ)) (prʟ-fst a u)
                , subst ⟨_⟩ (sym (appC-adequate F i0 i1 γ))
                    (subst (λ q → ⟨ pr q (fst w) ∈ fst F ⟩) (sym (prʟ-fst a u)) hF) )))) ∣₁ ∣₁ ∣₁ ∣₁ ) })

      finIn : (y s n m C : S)
            → ∥ Σ[ v ∈ S ] ( ⟨ pr (fst n) (fst v) ∈ fst C ⟩
                           × ⟨ pr (pr (fst n) (fst v)) (fst y) ∈ fst F ⟩ ) ∥₁
            → ⟨ e7 y s n m C α (nn zero) ⊨ finFo ⟩
      finIn y s n m C = PT.map (λ { (v , (hv , hy)) →
        let γ = prʟ n v ∷ v ∷ e7 y s n m C α (nn zero) in
        v , ∣ prʟ n v
            , ( subst ⟨_⟩ (sym (appAt-adequate i4 i6 i1 γ)) hv
              , ( subst ⟨_⟩ (sym (prAtL-adequate i0 i6 i1 γ)) (prʟ-fst n v)
                , subst ⟨_⟩ (sym (appC-adequate F i0 i7 γ))
                    (subst (λ q → ⟨ pr q (fst y) ∈ fst F ⟩) (sym (prʟ-fst n v)) hy) )) ∣₁ })

      bodyIn : (y s n m C : S) → fst m ≡ sucV (fst n) → DomIs s n → EnvC m C
             → ⟨ pr (# zero) (# zero) ∈ fst C ⟩
             → ((i : S) → ⟨ fst i ∈ fst n ⟩ → StepAt s C i)
             → ∥ Σ[ v ∈ S ] ( ⟨ pr (fst n) (fst v) ∈ fst C ⟩
                            × ⟨ pr (pr (fst n) (fst v)) (fst y) ∈ fst F ⟩ ) ∥₁
             → ⟨ e7 y s n m C α (nn zero) ⊨ body ⟩
      bodyIn y s n m C em hd hE h0 hS hF =
        let γ = e7 y s n m C α (nn zero) in
          refl
        , ( refl
        , ( subst ⟨_⟩ (sym (sucAtL-adequate i4 i3 γ)) em
        , ( domAt-intro i6 i4 γ (λ x →
              PT.rec (snd (fst x ∈ fst n)) (λ { (yy , p) → hd x .snd yy p })
            , hd x .fst)
        , ( envOverAt-transport (α ∷ m ∷ C ∷ []) γ
              (suc (suc zero)) (suc zero) zero i2 i3 i1 refl refl refl hE
        , ( subst ⟨_⟩ (sym (appAt-adequate i2 i0 i0 γ)) h0
        , ( (λ i i∈n → stepIn y s n m C i (hS i i∈n))
        , finIn y s n m C hF ))))))

    fo-in : (y s : S) → Wit y s → ⟨ (y ∷ s ∷ []) ⊨ fo ⟩
    fo-in y s = PT.rec (snd ((y ∷ s ∷ []) ⊨ fo))
      (λ { (n , m , C , (n∈ω , em , hd , hE , h0 , hS , hF)) →
        ∣ n , ( n∈ω
              , ∣ m , ∣ C , ∣ α , ∣ nn zero
              , bodyIn y s n m C em hd hE h0 hS hF ∣₁ ∣₁ ∣₁ ∣₁ ) ∣₁ })
```

2.4 At a sequence `s ≡ envS g` of length `N`: the graph holds of the code
(`wit`), and of nothing else (`only`).

```agda
  module AtSeq (N : ℕ) (g : Fin N → ⟪ fst α ⟫) (s : S) (e : fst s ≡ fst (envS α g)) where

    private
      δ : S ^ 3
      δ = α ∷ nn N ∷ envS α g ∷ []

      dom0 : ⟨ δ ⊨ domAt (suc (suc zero)) (suc zero) ⟩
      dom0 = envOver-dom (suc (suc zero)) (suc zero) zero δ (envOver α g)

      gV : Fin N → V ℓ
      gV i = ⟪ fst α ⟫↪ (g i)
```

The entries of `s`, at a natural index below `N`.

```agda
      extMem : (k : ℕ) (p : k < N)
             → ⟨ pr (# k) (fst (fst (ext N g k))) ∈ fst (envS α g) ⟩
      extMem k p = subst (λ k → ⟨ pr (# k) (fst (fst (ext N g k))) ∈ fst (envS α g) ⟩)
        (toFromId' N k p)
        (subst ⟨_⟩ (sym (lookup-spec gV i (fst (fst (ext N g (toℕ i))))))
          (cong (λ z → fst (fst z)) (ext-at N g i)))
        where
        i : Fin N
        i = fromℕ' N k p
```

An entry of `s` at `k` reads back as the `k`-th term.

```agda
      s-uniq : (k : ℕ) (p : k < N) (a : S)
             → ⟨ pr (# k) (fst a) ∈ fst (envS α g) ⟩
             → fst a ≡ fst (fst (ext N g k))
      s-uniq k p a ha =
          subst ⟨_⟩ (lookup-spec gV i (fst a))
            (subst (λ k → ⟨ pr (# k) (fst a) ∈ fst (envS α g) ⟩) (sym (toFromId' N k p)) ha)
        ∙ sym (cong (λ z → fst (fst z)) (ext-at N g i))
        ∙ cong (λ k → fst (fst (ext N g k))) (toFromId' N k p)
        where
        i : Fin N
        i = fromℕ' N k p
```

The chain, as an environment over `α` of length `N + 1`.

```agda
      h : Fin (suc N) → ⟪ fst α ⟫
      h i = fiber (fst α) (snd (chain N g (toℕ i))) .fst

      hV : Fin (suc N) → V ℓ
      hV i = ⟪ fst α ⟫↪ (h i)

      C : S
      C = envS α h

      chainMem : (k : ℕ) (p : k < suc N)
               → ⟨ pr (# k) (fst (fst (chain N g k))) ∈ fst C ⟩
      chainMem k p = subst (λ k → ⟨ pr (# k) (fst (fst (chain N g k))) ∈ fst C ⟩)
        (toFromId' (suc N) k p)
        (subst ⟨_⟩ (sym (lookup-spec hV i (fst (fst (chain N g (toℕ i))))))
          (sym (fiber (fst α) (snd (chain N g (toℕ i))) .snd)))
        where
        i : Fin (suc N)
        i = fromℕ' (suc N) k p

      inS : (k : ℕ) (a : S) → ⟨ pr (# k) (fst a) ∈ fst (envS α g) ⟩ → ⟨ pr (# k) (fst a) ∈ fst s ⟩
      inS k a = subst (λ w → ⟨ pr (# k) (fst a) ∈ w ⟩) (sym e)

      outS : (k : ℕ) (a : S) → ⟨ pr (# k) (fst a) ∈ fst s ⟩ → ⟨ pr (# k) (fst a) ∈ fst (envS α g) ⟩
      outS k a = subst (λ w → ⟨ pr (# k) (fst a) ∈ w ⟩) e

    wit : Wit (fst (code N g)) s
    wit = ∣ nn N , nn (suc N) , C
          , ( #∈ω N
            , refl
            , domIs
            , envOver α h
            , chainMem zero (suc-≤-suc zero-≤)
            , step
            , ∣ fst (chain N g N)
              , ( chainMem N ≤-refl , app-graph (num N) (chain N g N) ) ∣₁ ) ∣₁
      where
      domIs : DomIs s (nn N)
      domIs x =
          (λ m → PT.map (λ { (yy , p) → yy , subst (λ w → ⟨ pr (fst x) (fst yy) ∈ w ⟩) (sym e) p })
                   (domAt-in (suc (suc zero)) (suc zero) δ dom0 x m))
        , (λ yy p → domAt-out (suc (suc zero)) (suc zero) δ dom0 x yy
                      (subst (λ w → ⟨ pr (fst x) (fst yy) ∈ w ⟩) e p))

      step : (i : S) → ⟨ fst i ∈ # N ⟩ → StepAt s C i
      step i i∈N = PT.rec squash₁ (λ { (k , p , ei) →
        ∣ nn (suc k) , fst (ext N g k) , fst (chain N g k) , fst (chain N g (suc k))
        , ( cong sucV (sym ei)
          , subst (λ w → ⟨ pr w (fst (fst (ext N g k))) ∈ fst s ⟩) (sym ei)
              (inS k (fst (ext N g k)) (extMem k p))
          , subst (λ w → ⟨ pr w (fst (fst (chain N g k))) ∈ fst C ⟩) (sym ei)
              (chainMem k (≤-suc p))
          , chainMem (suc k) (suc-≤-suc p)
          , app-graph (ext N g k) (chain N g k) ) ∣₁ }) (∈#-elim N (fst i) i∈N)

    only : (y : S) → Wit y s → fst y ≡ fst (fst (code N g))
    only y = PT.rec (setIsSet (fst y) (fst (fst (code N g))))
      (λ { (n , m , C' , (n∈ω , em , hd , hE , h0 , hS , hF)) →
        Only.final n m C' n∈ω em hd hE h0 hS hF })
      where
      module Only (n m C' : S) (n∈ω : ⟨ fst n ∈ ω ⟩) (em : fst m ≡ sucV (fst n))
                  (hd : DomIs s n) (hE : EnvC m C')
                  (h0 : ⟨ pr (# zero) (# zero) ∈ fst C' ⟩)
                  (hS : (i : S) → ⟨ fst i ∈ fst n ⟩ → StepAt s C' i)
                  (hF : ∥ Σ[ v ∈ S ] ( ⟨ pr (fst n) (fst v) ∈ fst C' ⟩
                                     × ⟨ pr (pr (fst n) (fst v)) (fst y) ∈ fst F ⟩ ) ∥₁)
                  where
```

The domain of `s` is the numeral `N`, so `n` is `# N`.

```agda
        n≡ : fst n ≡ # N
        n≡ = cong fst (extensionalL {a = n} {b = nn N} (λ x → ⇔toPath (fwd x) (bwd x)))
          where
          fwd : (x : S) → ⟨ fst x ∈ fst n ⟩ → ⟨ fst x ∈ # N ⟩
          fwd x x∈n = PT.rec (snd (fst x ∈ # N))
            (λ { (yy , p) → domAt-out (suc (suc zero)) (suc zero) δ dom0 x yy
                              (subst (λ w → ⟨ pr (fst x) (fst yy) ∈ w ⟩) e p) })
            (hd x .fst x∈n)
          bwd : (x : S) → ⟨ fst x ∈ # N ⟩ → ⟨ fst x ∈ fst n ⟩
          bwd x x∈N = PT.rec (snd (fst x ∈ fst n))
            (λ { (yy , p) → hd x .snd yy (subst (λ w → ⟨ pr (fst x) (fst yy) ∈ w ⟩) (sym e) p) })
            (domAt-in (suc (suc zero)) (suc zero) δ dom0 x x∈N)

```

`C'` is single-valued.

```agda
        svC : (x v v' : S) → ⟨ pr (fst x) (fst v) ∈ fst C' ⟩ → ⟨ pr (fst x) (fst v') ∈ fst C' ⟩
            → fst v ≡ fst v'
        svC = svAt-out (suc (suc zero)) (α ∷ m ∷ C' ∷ [])
                (envOver-sv (suc (suc zero)) (suc zero) zero (α ∷ m ∷ C' ∷ []) hE)
```

Every entry of `C'` below `N + 1` is the fold.

```agda
        entry : (k : ℕ) → k < suc N → (v : S)
              → ⟨ pr (# k) (fst v) ∈ fst C' ⟩ → fst v ≡ fst (fst (chain N g k))
        entry zero    p v hv = svC (nn zero) v (nn zero) hv h0
        entry (suc k) p v hv = PT.rec (setIsSet (fst v) (fst (fst (chain N g (suc k)))))
          (λ { (j , a , u , w , (ej , ha , hu , hw , hFw)) →
            let ea : fst a ≡ fst (fst (ext N g k))
                ea = s-uniq k p' a (outS k a ha)
                eu : fst u ≡ fst (fst (chain N g k))
                eu = entry k (≤-suc p') u hu
                ew : fst w ≡ fst (fst (chain N g (suc k)))
                ew = app-uniq (ext N g k) (chain N g k) w
                       (subst (λ q → ⟨ pr q (fst w) ∈ fst F ⟩) (cong₂ pr ea eu) hFw)
            in svC (nn (suc k)) v w hv
                 (subst (λ z → ⟨ pr z (fst w) ∈ fst C' ⟩) ej hw) ∙ ew })
          (hS (nn k) (subst (λ z → ⟨ # k ∈ z ⟩) (sym n≡) (#mono k N p')))
          where
          p' : k < N
          p' = pred-≤-pred p

        final : fst y ≡ fst (fst (code N g))
        final = PT.rec (setIsSet (fst y) (fst (fst (code N g))))
          (λ { (v , (hv , hy)) →
            let hv' : ⟨ pr (# N) (fst v) ∈ fst C' ⟩
                hv' = subst (λ z → ⟨ pr z (fst v) ∈ fst C' ⟩) n≡ hv
                ev : fst v ≡ fst (fst (chain N g N))
                ev = entry N ≤-refl v hv'
            in app-uniq (num N) (chain N g N) y
                 (subst (λ q → ⟨ pr q (fst y) ∈ fst F ⟩) (cong₂ pr n≡ ev) hy) })
          hF
```

2.5 The recursion, the definable map, and the coded injection.

```agda
  Mem : S → Type (ℓ-suc ℓ)
  Mem s = ⟨ fst s ∈ˢ fst (seqL α) ⟩

  Rep : S → Type (ℓ-suc ℓ)
  Rep s = ∥ Σ[ n ∈ ℕ ] Σ[ g ∈ Ix α n ] (fst s ≡ fst (envS α g)) ∥₁

  rep : (s : S) → Mem s → Rep s
  rep s m = PT.rec squash₁
    (λ { (n , hn) → PT.map (λ { (g , e) → n , g , e }) (envSet-out α n s hn) })
    (seqL-out α s m)

  R : Recursion
  R = record
    { dom   = seqL α
    ; graph = fo
    ; funct = λ s m → mereFunct fo s (PT.map (λ { (n , g , e) →
        fst (code n g)
        , ( fo-in (fst (code n g)) s (AtSeq.wit n g s e)
          , λ y' h → Σ≡Prop (λ v → snd (isL v)) (AtSeq.only n g s e y' (fo-out y' s h)) ) })
        (rep s m)) }

  module T = Of R using ( funct; val; val-uniq )

  fn : (s : S) → Mem s → S
  fn = T.val

  fn-code : (s : S) (m : Mem s) (n : ℕ) (g : Ix α n) → fst s ≡ fst (envS α g)
          → fn s m ≡ fst (code n g)
  fn-code s m n g e = T.val-uniq s m (fst (code n g)) (fo-in (fst (code n g)) s (AtSeq.wit n g s e))

  into : (s : S) (m : Mem s) → ⟨ fst (fn s m) ∈ˢ fst α ⟩
  into s m = PT.rec (snd (fst (fn s m) ∈ˢ fst α))
    (λ { (n , g , e) → subst (λ w → ⟨ fst w ∈ˢ fst α ⟩) (sym (fn-code s m n g e)) (snd (code n g)) })
    (rep s m)

  D : DefinableMap
  D = record
    { dom = seqL α ; cod = α ; fn = fn ; into = into ; graph = fo
    ; defines = λ s m → T.funct s m .fst .snd
    ; only    = λ s m y h → sym (T.val-uniq s m y h) }

  inj : (s : S) (m : Mem s) (s' : S) (m' : Mem s')
      → fst (fn s m) ≡ fst (fn s' m') → fst s ≡ fst s'
  inj s m s' m' e = PT.rec2 (setIsSet (fst s) (fst s'))
    (λ { (n , g , es) (n' , g' , es') →
        es
      ∙ code-inj n g n' g'
          (sym (cong fst (fn-code s m n g es)) ∙ e ∙ cong fst (fn-code s' m' n' g' es'))
      ∙ sym es' })
    (rep s m) (rep s' m')

  injL : InjL (seqL α) α
  injL = Inj.injL D inj
```

<!--en-->
## Finite sequences inject into an infinite ordinal

Passing through the cardinal representative of `α` supplies the required coded pairing. The fold is injective because its final tag recovers the length and each pairing step can then be decoded backwards.
<!--zh-->
## 有限序列单射到无穷序数

经由 `α` 的基数代表即可得到所需的编码配对。折叠是单射，因为最后的标签还原长度，随后每一步配对都能逆向解码。
<!--ja-->
## 有限列を無限順序数へ単射する

`α` の基数代表を経由すると、必要な符号化された対関数が得られる。最後のタグから長さを復元し、各対関数を逆向きに復号できるので、畳み込みは単射である。
<!--/-->

At an infinite ordinal `α`, the finite sequences over `α` inject into `α`,
inside L.

The pairing at `α` is the one src/L/GCH/SuccessorIntoPowerSet.lagda.md builds:
`α ↪ μ` at the internal cardinal `μ` of `α`, so `prodL α ↪ prodL μ`; the square
law of src/L/GCH/CardinalSquareLaw.lagda.md at `μ`, which is infinite because `α` is; and
`μ ↪ α`.

```agda
seq-count :
    (α : SL.S) → IsOrd (fst α) → (⟨ fst α ∈ˢ ω ⟩ → Empty.⊥)
  → InjL (seqL α) α
seq-count α oα α∉ω = PT.rec squash₁
  (λ { (F , sv , dm , ij , ran) → Code.injL α oα α∉ω F sv dm ij ran }) pairing
  where
  pairing : InjL (prodL α) α
  pairing = PT.rec squash₁ build (cardOf α oα)
    where
    build : Σ[ μ ∈ S ]
              ( IsOrd (fst μ) × IsCardinalL μ
              × ((z : V ℓ) → ⟨ z ∈ˢ fst μ ⟩ → ⟨ z ∈ˢ fst α ⟩)
              × InjL α μ × InjL μ α )
          → InjL (prodL α) α
    build (μ , oμ , cardμ , _ , α↪μ , μ↪α) =
      injl-trans (prodL α) (prodL μ) α (prod-inj α μ α↪μ)
        (injl-trans (prodL μ) μ α
          (WF.WFI.induction regularityV {P = Goal} Step.result (fst μ) (snd μ) oμ cardμ μ∉ω)
          μ↪α)
      where
      μ∉ω : ⟨ fst μ ∈ˢ ω ⟩ → Empty.⊥
      μ∉ω h = no-fin α μ oα α∉ω oμ h α↪μ
```

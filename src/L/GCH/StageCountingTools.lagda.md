<!--en-->
# The counting tools for infinite constructible stages

The count of an infinite stage rests on coding finite environments and on the base case `L_ω ↪ ω`. This chapter proves the base injection and the formulas that lift injections through finite environments, preparing the proof that `Lset δ ↪ δ` for every infinite ordinal `δ`.
<!--zh-->
# 计数无穷可构造阶段的工具

无穷阶段的计数依赖有限环境的编码与基础情形 `L_ω ↪ ω`。本章证明这一基础单射，以及把单射逐项提升到有限环境的公式，为证明每个无穷序数 `δ` 都有 `Lset δ ↪ δ` 作准备。
<!--ja-->
# 無限な構成可能段階を数える道具

無限段階の計数は、有限環境の符号化と基底の場合 `L_ω ↪ ω` に基づく。本章ではこの基底単射と、単射を有限環境へ成分ごとに持ち上げる論理式を構成し、各無限順序数 `δ` に対する `Lset δ ↪ δ` の証明を準備する。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.StageCountingTools {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _≐_; _∈̇_; _∧̇_; _⇒̇_; ∃̇_; ∀̇_; ∀̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Model {ℓ} using ( ∈sucV-inl; self∈sucV )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′; #mono )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono; Lset→isL )
open import L.Ordinal {ℓ} using ( ∈#-elim; mem-ord; ω-ord; numeral-ord; #∈ω )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst; svAt; svAt-in; svAt-out; domAt; domAt-in; domAt-out; domAt-intro; appAt; appAt-adequate; envOverAt; envOverAt-transport )
open import L.Coding.Expressions {ℓ} using ( numL )
open import L.Coding.Injection {ℓ} lem
  using ( injAt; injAt-in; injAt-out; module Small )
open import L.Coding.Environment {ℓ} using ( env; lookup-spec )
open import L.Coding.EnvironmentSet {ℓ} lem
  using ( Ix; envS; envSet-in; envSet-out; envOver; module Recover )
open import L.Choice.NameComparison {ℓ} lem using ( domAt-numeral; domAt-fill )
open import L.Choice.StageOrders {ℓ} lem
  using ( carry; memOf; orderAt; orderAt-step; relOf
        ; birth-mem; module Family )
  renaming ( Mem to MemOf )
open import L.Choice.OrderTable {ℓ} lem using ( Related; IsRel; ixRel-rep; ixRel-fill )
open import L.Choice.InternalWellOrder {ℓ} lem using ( relL; relL-spec )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; lt; eq; gt ) renaming ( Tri to TriW )
open import L.Recursion {ℓ} lem using ( Recursion; module Of; mereFunct )
open import L.Cardinal {ℓ} lem using ( InjCode; InjL )
open import L.InjectionComposition {ℓ} lem using ( inclusion-coded; injl-trans )
open import L.DefinableInjection {ℓ} lem using ( DefinableMap; module Inj )
open import L.GCH.CardinalSquareLaw {ℓ} lem using ( isL-ord )
open import L.GCH.FiniteSequenceCoding {ℓ} lem using ( seqL; seqL-in; seqL-out )
open import L.Ordinal.SquareLaw {ℓ} lem using ( module FiniteBase )
open FiniteBase using ( fromFin; fromFin-inj )
open import L.InjectionComposition {ℓ} lem using ( appC; appC-adequate; ω-limit; finite-excl-ω )
open import L.Choice.FiniteStageOrders {ℓ} lem
  using ( Tally; StageOrder; stageOrder; finiteStage )  -- lint-agda: keep (StageOrder used as the projection qualifier)
open import L.GCH.OrderType {ℓ} lem using ( Holds; module Code )

open import Cubical.Data.Nat.Order using ( _<_ )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.FinData.FinSet using ( DecΣ )
open import Cubical.Relation.Nullary using ( decRec; yes; no )
open import Cubical.Data.FinData.Properties using ( toℕ<n; fromℕ'; toFromId'; inj-toℕ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum as Sum
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ2; isPropΠ3 )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_; ω; sucV )
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )
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
module SL = hPropStructure 𝒮ʟ using ( S )
open SL using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

The numeral `k` as an element of L.

```agda
nn : ℕ → S
nn k = # k , numL k

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
  i9 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc k))))))))))
  i9 = suc i8
```

<!--en-->
## Length and extensionality of environments

An environment determines its finite domain, and two environments on that domain are equal when all entries agree. These facts let later graph formulas recover sequence data without ambiguity.
<!--zh-->
## 环境的长度与外延性

一个环境确定其有限定义域，而同一定义域上的两个环境在逐项相等时相等。这些事实使后续图公式能够无歧义地还原序列数据。
<!--ja-->
## 環境の長さと外延性

環境はその有限な定義域を定め、同じ定義域上の二つの環境は各項が一致すれば等しい。これにより、後のグラフ論理式は列のデータを曖昧なく復元できる。
<!--/-->

An environment determines its length (read off `domAt`, through the two readings
src/L/Choice/InternalWellOrder.lagda.md exports), and two environments of one length that
are equal agree entrywise.

```agda
env-len : (E : S) {n n' : ℕ} (h : Fin n → V ℓ) (h' : Fin n' → V ℓ)
        → ((i : Fin n) → ⟨ isL (h i) ⟩) → ((i : Fin n') → ⟨ isL (h' i) ⟩)
        → fst E ≡ env h → fst E ≡ env h' → n ≡ n'
env-len E {n} {n'} h h' cg cg' q q' =
  #-inj′ (domAt-numeral (suc zero) zero (nn n ∷ E ∷ []) n' h' cg' q'
            (domAt-fill (suc zero) zero (nn n ∷ E ∷ []) n h cg q refl))

env-pt : {n : ℕ} (h h' : Fin n → V ℓ) → env h ≡ env h' → (i : Fin n) → h i ≡ h' i
env-pt h h' q i = subst ⟨_⟩ (lookup-spec h' i (h i))
  (subst (λ w → ⟨ pr (# (toℕ i)) (h i) ∈ w ⟩) q
    (subst ⟨_⟩ (sym (lookup-spec h i (h i))) refl))
```

<!--en-->
## Lifting a coded injection to finite sequences

A coded injection from `A` to `B` acts entrywise on every finite environment. A single graph formula records the common length and the image of each entry, producing a coded injection from `seqL A` to `seqL B`.
<!--zh-->
## 把编码单射提升到有限序列

从 `A` 到 `B` 的编码单射逐项作用于每个有限环境。一条图公式记录公共长度及每个表项的像，从而产生从 `seqL A` 到 `seqL B` 的编码单射。
<!--ja-->
## 符号化された単射を有限列へ持ち上げる

`A` から `B` への符号化された単射を、各有限環境の成分ごとに作用させる。一つのグラフ論理式が共通の長さと各項の像を記録し、`seqL A` から `seqL B` への符号化された単射を与える。
<!--/-->

Over `(y ∷ s ∷ [])`: "there is `n` with `dom s = n`, and `y` is an environment
over `B` on `n` whose entry at every `i ∈ n` is the `E`-image of the entry of
`s` at `i`". Binders, outermost first: `n`, then `b` pinned to `B`, then
`i ∈ n`, then `u`, `v`. Inside all of them: `v` is 0, `u` is 1, `i` is 2, `b` is
3, `n` is 4, `y` is 5, `s` is 6.

```agda
module SeqMap (A B E : S)
              (sv : ⟨ (E ∷ A ∷ []) ⊨ svAt zero ⟩)
              (dm : ⟨ (E ∷ A ∷ []) ⊨ domAt zero (suc zero) ⟩)
              (ij : ⟨ (E ∷ A ∷ []) ⊨ injAt zero ⟩)
              (ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst E ⟩
                   → ⟨ fst y ∈ fst B ⟩) where

  module Sm = Small E A B sv dm ij ran using ( at; fib; small; small-inj; module E )
```

The map on the presentations, with its graph and its injectivity. Sealed:
measured at this site, an unsealed `f (g j)` met by the unifier (in
`cong (λ h → fst (envS B h)) (funExt pt)`) unfolds the readback's eliminators
and exhausts an 8g heap in under 2 min.

```agda
  opaque
    f : ⟪ fst A ⟫ → ⟪ fst B ⟫
    f = Sm.small

    f-graph : (m : ⟪ fst A ⟫)
            → ⟨ pr (⟪ fst A ⟫↪ m) (⟪ fst B ⟫↪ (f m)) ∈ fst E ⟩
    f-graph m = subst (λ w → ⟨ pr (⟪ fst A ⟫↪ m) w ∈ fst E ⟩)
      (sym (Sm.fib m .snd)) (Sm.E.toFun-graph (Sm.at m))

    f-inj : (m n : ⟪ fst A ⟫) → f m ≡ f n → m ≡ n
    f-inj = Sm.small-inj

  vA : {n : ℕ} → Ix A n → Fin n → V ℓ
  vA g i = ⟪ fst A ⟫↪ (g i)

  vB : {n : ℕ} → Ix B n → Fin n → V ℓ
  vB h i = ⟪ fst B ⟫↪ (h i)

  fg : {n : ℕ} → Ix A n → Ix B n
  fg g i = f (g i)

  isLA : {n : ℕ} (g : Ix A n) (i : Fin n) → ⟨ isL (vA g i) ⟩
  isLA g i = isL-trans (member (fst A) (g i)) (snd A)

  isLB : {n : ℕ} (h : Ix B n) (i : Fin n) → ⟨ isL (vB h i) ⟩
  isLB h i = isL-trans (member (fst B) (h i)) (snd B)
```

1.1 The graph, and its host reading.

```agda
  Ent : (y s i : S) → Type (ℓ-suc ℓ)
  Ent y s i = ∥ Σ[ u ∈ S ] Σ[ v ∈ S ]
      ( ⟨ pr (fst i) (fst u) ∈ fst s ⟩
      × ⟨ pr (fst i) (fst v) ∈ fst y ⟩
      × ⟨ pr (fst u) (fst v) ∈ fst E ⟩ ) ∥₁

  Wit : (y s : S) → Type (ℓ-suc ℓ)
  Wit y s = ∥ Σ[ n ∈ S ]
      ( ⟨ (n ∷ y ∷ s ∷ []) ⊨ domAt i2 i0 ⟩
      × ⟨ (B ∷ n ∷ y ∷ s ∷ []) ⊨ envOverAt i2 i1 i0 ⟩
      × ((i : S) → ⟨ fst i ∈ fst n ⟩ → Ent y s i) ) ∥₁

  opaque
    private
      entFo : Formula S 5
      entFo = ∃̇ (∃̇ ( appAt i6 i2 i1 ∧̇ appAt i5 i2 i0 ∧̇ appC E i1 i0 ))

    fo : Formula S 2
    fo = ∃̇ ( domAt i2 i0
           ∧̇ ∃̇ ( (var i0 ≐ con B)
                ∧̇ envOverAt i2 i1 i0
                ∧̇ ∀̇∈ (var i1) entFo ) )

    private
      entOut : (y s n b i : S) → ⟨ (i ∷ b ∷ n ∷ y ∷ s ∷ []) ⊨ entFo ⟩ → Ent y s i
      entOut y s n b i = PT.rec squash₁ (λ { (u , hv) →
        PT.rec squash₁ (λ { (v , (h1 , (h2 , h3))) →
          let γ = v ∷ u ∷ i ∷ b ∷ n ∷ y ∷ s ∷ [] in
          ∣ u , v
          , ( subst ⟨_⟩ (appAt-adequate i6 i2 i1 γ) h1
            , subst ⟨_⟩ (appAt-adequate i5 i2 i0 γ) h2
            , subst ⟨_⟩ (appC-adequate E i1 i0 γ) h3 ) ∣₁ }) hv })

      entIn : (y s n i : S) → Ent y s i → ⟨ (i ∷ B ∷ n ∷ y ∷ s ∷ []) ⊨ entFo ⟩
      entIn y s n i = PT.map (λ { (u , v , (h1 , h2 , h3)) →
        let γ = v ∷ u ∷ i ∷ B ∷ n ∷ y ∷ s ∷ [] in
        u , ∣ v , ( subst ⟨_⟩ (sym (appAt-adequate i6 i2 i1 γ)) h1
                  , subst ⟨_⟩ (sym (appAt-adequate i5 i2 i0 γ)) h2
                  , subst ⟨_⟩ (sym (appC-adequate E i1 i0 γ)) h3 ) ∣₁ })

      bodyOut : (y s n b : S)
              → ⟨ (n ∷ y ∷ s ∷ []) ⊨ domAt i2 i0 ⟩
              → fst b ≡ fst B
              → ⟨ (b ∷ n ∷ y ∷ s ∷ []) ⊨ envOverAt i2 i1 i0 ⟩
              → ⟨ (b ∷ n ∷ y ∷ s ∷ []) ⊨ ∀̇∈ (var i1) entFo ⟩
              → Wit y s
      bodyOut y s n b hd eb he hS =
        ∣ n , ( hd
              , envOverAt-transport (b ∷ n ∷ y ∷ s ∷ []) (B ∷ n ∷ y ∷ s ∷ [])
                  i2 i1 i0 i2 i1 i0 refl refl eb he
              , λ i i∈n → entOut y s n b i (hS i i∈n) ) ∣₁

    fo-out : (y s : S) → ⟨ (y ∷ s ∷ []) ⊨ fo ⟩ → Wit y s
    fo-out y s = PT.rec squash₁ (λ { (n , (hd , hb)) →
      PT.rec squash₁ (λ { (b , (eb , (he , hS))) → bodyOut y s n b hd eb he hS }) hb })

    fo-in : (y s : S) → Wit y s → ⟨ (y ∷ s ∷ []) ⊨ fo ⟩
    fo-in y s = PT.rec (snd ((y ∷ s ∷ []) ⊨ fo))
      (λ { (n , (hd , he , hS)) →
        ∣ n , ( hd , ∣ B , ( refl , he , λ i i∈n → entIn y s n i (hS i i∈n) ) ∣₁ ) ∣₁ })
```

1.2 At a sequence `s ≡ envS g` of length `N`: the image sequence satisfies the
graph (`wit`), and nothing else does (`only`).

```agda
  module AtSeq (N : ℕ) (g : Ix A N) (s : S) (e : fst s ≡ fst (envS A g)) where

    y₀ : S
    y₀ = envS B (fg g)

    private
```

The entry of an environment at a natural index.

```agda
      at : {k : ℕ} (h : Fin k → V ℓ) (j : Fin k)
         → ⟨ pr (# (toℕ j)) (h j) ∈ env h ⟩
      at h j = subst ⟨_⟩ (sym (lookup-spec h j (h j))) refl

    wit : Wit y₀ s
    wit = ∣ nn N , ( hd , he , step ) ∣₁
      where
      hd : ⟨ (nn N ∷ y₀ ∷ s ∷ []) ⊨ domAt i2 i0 ⟩
      hd = domAt-fill i2 i0 (nn N ∷ y₀ ∷ s ∷ []) N (vA g) (isLA g) e refl

      he : ⟨ (B ∷ nn N ∷ y₀ ∷ s ∷ []) ⊨ envOverAt i2 i1 i0 ⟩
      he = envOverAt-transport (B ∷ nn N ∷ y₀ ∷ []) (B ∷ nn N ∷ y₀ ∷ s ∷ [])
             i2 i1 i0 i2 i1 i0 refl refl refl (envOver B (fg g))

      step : (i : S) → ⟨ fst i ∈ # N ⟩ → Ent y₀ s i
      step i i∈N = PT.map atIndex (∈#-elim N (fst i) i∈N)
        where
        atIndex : Σ[ k ∈ ℕ ] ((k < N) × (fst i ≡ # k))
                → Σ[ u ∈ S ] Σ[ v ∈ S ]
                    ( ⟨ pr (fst i) (fst u) ∈ fst s ⟩
                    × ⟨ pr (fst i) (fst v) ∈ fst y₀ ⟩
                    × ⟨ pr (fst u) (fst v) ∈ fst E ⟩ )
        atIndex (k , p , ei) =
            (vA g j , isLA g j) , (vB (fg g) j , isLB (fg g) j)
          , ( subst2 (λ a w → ⟨ pr a (vA g j) ∈ w ⟩) (sym qi) (sym e) (at (vA g) j)
            , subst (λ a → ⟨ pr a (vB (fg g) j) ∈ fst y₀ ⟩) (sym qi) (at (vB (fg g)) j)
            , f-graph (g j) )
          where
          j : Fin N
          j = fromℕ' N k p
          qi : fst i ≡ # (toℕ j)
          qi = ei ∙ cong #_ (sym (toFromId' N k p))

    only : (y : S) → Wit y s → fst y ≡ fst y₀
    only y = PT.rec (setIsSet (fst y) (fst y₀))
      (λ { (n , (hd , he , hS)) → Only.final n hd he hS })
      where
      module Only (n : S)
                  (hd : ⟨ (n ∷ y ∷ s ∷ []) ⊨ domAt i2 i0 ⟩)
                  (he : ⟨ (B ∷ n ∷ y ∷ s ∷ []) ⊨ envOverAt i2 i1 i0 ⟩)
                  (hS : (i : S) → ⟨ fst i ∈ fst n ⟩ → Ent y s i) where

        qn : fst n ≡ # N
        qn = domAt-numeral i2 i0 (n ∷ y ∷ s ∷ []) N (vA g) (isLA g) e hd
```

The recovered sequence, sealed: a truncation eliminator, never to meet the
unifier.

```agda
        opaque
          gR : Ix B N
          gR = Recover.g B N (B ∷ n ∷ y ∷ s ∷ []) i2 i1 i0 qn refl he

          gR-eq : fst y ≡ fst (envS B gR)
          gR-eq = Recover.recovers B N (B ∷ n ∷ y ∷ s ∷ []) i2 i1 i0 qn refl he
```

The recovered entry at `j` is the `E`-image of the entry of `s`.

```agda
        pt : (j : Fin N) → gR j ≡ fg g j
        pt j = ↪-inj {a = fst B} (PT.rec (setIsSet _ _) read (hS (nn (toℕ j)) j∈n))
          where
          j∈n : ⟨ # (toℕ j) ∈ fst n ⟩
          j∈n = subst (λ w → ⟨ # (toℕ j) ∈ w ⟩) (sym qn) (#mono (toℕ j) N (toℕ<n j))

          read : Σ[ u ∈ S ] Σ[ v ∈ S ]
                   ( ⟨ pr (# (toℕ j)) (fst u) ∈ fst s ⟩
                   × ⟨ pr (# (toℕ j)) (fst v) ∈ fst y ⟩
                   × ⟨ pr (fst u) (fst v) ∈ fst E ⟩ )
               → vB gR j ≡ vB (fg g) j
          read (u , v , (hu , hv , hE)) = sym qv ∙ qv'
            where
            qu : fst u ≡ vA g j
            qu = subst ⟨_⟩ (lookup-spec (vA g) j (fst u))
                   (subst (λ w → ⟨ pr (# (toℕ j)) (fst u) ∈ w ⟩) e hu)
            qv : fst v ≡ vB gR j
            qv = subst ⟨_⟩ (lookup-spec (vB gR) j (fst v))
                   (subst (λ w → ⟨ pr (# (toℕ j)) (fst v) ∈ w ⟩) gR-eq hv)
            qv' : fst v ≡ vB (fg g) j
            qv' = svAt-out zero (E ∷ A ∷ []) sv u v (vB (fg g) j , isLB (fg g) j) hE
                    (subst (λ w → ⟨ pr w (vB (fg g) j) ∈ fst E ⟩) (sym qu) (f-graph (g j)))

        final : fst y ≡ fst y₀
```

A path lambda, not `cong`: measured at this site, `cong` (or `congS`) at this
function sends the unifier through `envS` and exhausts an 8g heap; the lambda
checks in seconds.

```agda
        final = gR-eq ∙ λ i → fst (envS B (funExt pt i))
```

1.3 The recursion, the definable map, and the coded injection.

```agda
  Mem : S → Type (ℓ-suc ℓ)
  Mem s = ⟨ fst s ∈ˢ fst (seqL A) ⟩

  Rep : S → Type (ℓ-suc ℓ)
  Rep s = ∥ Σ[ n ∈ ℕ ] Σ[ g ∈ Ix A n ] (fst s ≡ fst (envS A g)) ∥₁

  rep : (s : S) → Mem s → Rep s
  rep s m = PT.rec squash₁
    (λ { (n , hn) → PT.map (λ { (g , e) → n , g , e }) (envSet-out A n s hn) })
    (seqL-out A s m)

  R : Recursion
  R = record
    { dom   = seqL A
    ; graph = fo
    ; funct = λ s m → mereFunct fo s (PT.map (λ { (n , g , e) →
        AtSeq.y₀ n g s e
        , ( fo-in (AtSeq.y₀ n g s e) s (AtSeq.wit n g s e)
          , λ y' h → Σ≡Prop (λ v → snd (isL v)) (AtSeq.only n g s e y' (fo-out y' s h)) ) })
        (rep s m)) }

  module T = Of R using ( funct; val; val-uniq )

  fn : (s : S) → Mem s → S
  fn = T.val

  fn-code : (s : S) (m : Mem s) (n : ℕ) (g : Ix A n) (e : fst s ≡ fst (envS A g))
          → fn s m ≡ AtSeq.y₀ n g s e
  fn-code s m n g e =
    T.val-uniq s m (AtSeq.y₀ n g s e) (fo-in (AtSeq.y₀ n g s e) s (AtSeq.wit n g s e))

  into : (s : S) (m : Mem s) → ⟨ fst (fn s m) ∈ˢ fst (seqL B) ⟩
  into s m = PT.rec (snd (fst (fn s m) ∈ˢ fst (seqL B)))
    (λ { (n , g , e) → subst (λ w → ⟨ fst w ∈ˢ fst (seqL B) ⟩) (sym (fn-code s m n g e))
           (seqL-in B n (envS B (fg g)) (envSet-in B (fg g))) })
    (rep s m)

  D : DefinableMap
  D = record
    { dom = seqL A ; cod = seqL B ; fn = fn ; into = into ; graph = fo
    ; defines = λ s m → T.funct s m .fst .snd
    ; only    = λ s m y h → sym (T.val-uniq s m y h) }
```

Injectivity: equal image sequences have one length, and then agree entrywise
through the injectivity of the small map.

```agda
  private
    same : (n : ℕ) (g : Ix A n) (n' : ℕ) (g' : Ix A n')
         → fst (envS B (fg g)) ≡ fst (envS B (fg g'))
         → fst (envS A g) ≡ fst (envS A g')
    same n g n' g' q =
      subst P (env-len (envS B (fg g)) (vB (fg g)) (vB (fg g')) (isLB (fg g)) (isLB (fg g')) refl q)
        base g' q
      where
      P : ℕ → Type (ℓ-suc ℓ)
      P k = (h : Ix A k) → fst (envS B (fg g)) ≡ fst (envS B (fg h))
          → fst (envS A g) ≡ fst (envS A h)
      base : P n
      base h q' = λ i → fst (envS A (funExt (λ j →
        f-inj (g j) (h j) (↪-inj {a = fst B} (env-pt (vB (fg g)) (vB (fg h)) q' j))) i))

  inj : (s : S) (m : Mem s) (s' : S) (m' : Mem s')
      → fst (fn s m) ≡ fst (fn s' m') → fst s ≡ fst s'
  inj s m s' m' q = PT.rec2 (setIsSet (fst s) (fst s'))
    (λ { (n , g , e) (n' , g' , e') →
        e
      ∙ same n g n' g'
          (sym (cong fst (fn-code s m n g e)) ∙ q ∙ cong fst (fn-code s' m' n' g' e'))
      ∙ sym e' })
    (rep s m) (rep s' m')

  injL : InjL (seqL A) (seqL B)
  injL = Inj.injL D inj
```

The lift: a coded injection of `A` into `B` lifts to the finite sequences.

```agda
seq-map : (A B E : S) → InjCode E A B → InjL (seqL A) (seqL B)
seq-map A B E (sv , dm , ij , ran) = SeqMap.injL A B E sv dm ij ran
```

<!--en-->
## Pinning a quantified variable to a constant

The next injection formula needs to quantify over a value while requiring it to equal a fixed constant. This binder pattern is proved once with both its internal and ambient readings.
<!--zh-->
## 把量化变量固定为常元

下一条单射公式需要量化一个值，同时要求它等于固定常元。本节一并证明这种绑定模式的内部读法与外围读法。
<!--ja-->
## 量化変数を定数に固定する

次の単射論理式では、値を量化しながら固定した定数に等しいことを要求する。この束縛の形について、内部と周囲の二つの読み方を一度に示す。
<!--/-->

The consumer is the injection formula of section 3, and through it the hull's
own count (src/L/GCH/HullCounting.lagda.md).

```agda
pinAt : ∀ {n} → S → Formula S (suc n) → Formula S n
pinAt c φ = ∃̇ ((var zero ≐ con c) ∧̇ φ)

pin-in : ∀ {n} (c : S) (φ : Formula S (suc n)) (γ : S ^ n)
       → ⟨ (c ∷ γ) ⊨ φ ⟩ → ⟨ γ ⊨ pinAt c φ ⟩
pin-in c φ γ h = ∣ c , (refl , h) ∣₁

pin-out : ∀ {n} (c : S) (φ : Formula S (suc n)) (γ : S ^ n)
        → ⟨ γ ⊨ pinAt c φ ⟩ → ⟨ (c ∷ γ) ⊨ φ ⟩
pin-out c φ γ = PT.rec (snd ((c ∷ γ) ⊨ φ))
  (λ { (z , (ez , h)) → subst (λ v → ⟨ (v ∷ γ) ⊨ φ ⟩) (Σ≡Prop (λ v → snd (isL v)) ez) h })
```

<!--en-->
## A formula for coded injections into a fixed target

The formula states that a graph is total and single-valued on a chosen domain, lands in a constant target, and is injective there. Its two readings allow the hull-counting chapter to move between syntax and the actual map.
<!--zh-->
## 到固定目标的编码单射公式

该公式断言一个图在给定定义域上全域且单值，像包含于固定目标，并且作为从该定义域到目标的图是单射的。它的两种读法使壳计数章节能够在语法描述与实际映射之间往返。
<!--ja-->
## 固定した終域への符号化された単射の論理式

この論理式は、グラフが指定した定義域上で全域かつ一価であり、固定した終域へ値を取り、単射であることを述べる。二つの読み方により、包の計数で構文と実際の写像を往復できる。
<!--/-->

A coded injection said inside the model at two slots against a constant target,
with the readings src/L/GCH/HullCounting.lagda.md fills and reads at the hull.

An injection code is a proposition, and it respects the index
equations of its graph and its domain.

```agda
isPropInjCode : (F a b : S) → isProp (InjCode F a b)
isPropInjCode F a b =
  isProp× (snd ((F ∷ a ∷ []) ⊨ svAt zero))
    (isProp× (snd ((F ∷ a ∷ []) ⊨ domAt zero (suc zero)))
      (isProp× (snd ((F ∷ a ∷ []) ⊨ injAt zero))
        (isPropΠ3 (λ _ y _ → snd (fst y ∈ fst b)))))

injcode-resp : (F F' a a' b : S) → fst F ≡ fst F' → fst a ≡ fst a'
             → InjCode F a b → InjCode F' a' b
injcode-resp F F' a a' b qF qa = subst2 {x = F} {y = F'} {z = a} {w = a'}
  (λ E A → InjCode E A b)
  (Σ≡Prop (λ v → snd (isL v)) qF) (Σ≡Prop (λ v → snd (isL v)) qa)

```

The injection-code formula at two slots, against the constant `b`:
single-valued, with domain `B`, injective, with values in `b`.

```agda
injFo : ∀ {n} → S → Fin n → Fin n → Formula S n
injFo b f B = svAt f ∧̇ domAt f B ∧̇ injAt f
            ∧̇ ∀̇ (∀̇ (appAt (suc (suc f)) i1 i0 ⇒̇ (var i0 ∈̇ con b)))

module InjFo {n : ℕ} (b : S) (f B : Fin n) (γ : S ^ n) where
  private
    F A : S
    F = lookup f γ
    A = lookup B γ

  read : ⟨ γ ⊨ injFo b f B ⟩ → InjCode F A b
  read (sv , dm , ij , ran) =
      svAt-in zero (F ∷ A ∷ []) (λ x y y' p q → svAt-out f γ sv x y y' p q)
    , domAt-intro zero (suc zero) (F ∷ A ∷ []) (λ x →
          (λ h → PT.rec (snd (fst x ∈ fst A))
                   (λ { (y , p) → domAt-out f B γ dm x y p }) h)
        , (λ hx → domAt-in f B γ dm x hx))
    , injAt-in zero (F ∷ A ∷ []) (λ y x x' p q → injAt-out f γ ij y x x' p q)
    , λ x y p → ran x y (subst ⟨_⟩ (sym (appAt-adequate (suc (suc f)) i1 i0 (y ∷ x ∷ γ))) p)

  fill : InjCode F A b → ⟨ γ ⊨ injFo b f B ⟩
  fill (sv , dm , ij , ran) =
      svAt-in f γ (λ x y y' p q → svAt-out zero (F ∷ A ∷ []) sv x y y' p q)
    , domAt-intro f B γ (λ x →
          (λ h → PT.rec (snd (fst x ∈ fst A))
                   (λ { (y , p) → domAt-out zero (suc zero) (F ∷ A ∷ []) dm x y p }) h)
        , (λ hx → domAt-in zero (suc zero) (F ∷ A ∷ []) dm x hx))
    , injAt-in f γ (λ y x x' p q → injAt-out zero (F ∷ A ∷ []) ij y x x' p q)
    , λ x y p → ran x y (subst ⟨_⟩ (appAt-adequate (suc (suc f)) i1 i0 (y ∷ x ∷ γ)) p)
```

<!--en-->
## Reducing the infinite-stage count to `L_ω`

The general stage count consumes a base injection from `L_ω` into `ω`. This section isolates that premise and records how an injection can be transported when its source carriers are equal.
<!--zh-->
## 把无穷阶段计数归约到 `L_ω`

一般的阶段计数使用从 `L_ω` 到 `ω` 的基础单射。本节提取这一前提，并记录在源载体相等时如何搬运单射。
<!--ja-->
## 無限段階の計数を `L_ω` に帰着する

一般の段階計数は、`L_ω` から `ω` への基底単射を使う。本節ではこの前提を取り出し、始域の台が等しいときに単射を移送する方法を記録する。
<!--/-->

The base of the count is `L_ω ↪ ω`, proved in section 6. The row at an infinite
ordinal is src/L/GCH/StageInjection.lagda.md, which runs the hull at `δ+1` and
takes only this base from here.

```agda
Lω : S
Lω = LsetS ω ω-ord

LimitStageCounted : Type (ℓ-suc ℓ)
LimitStageCounted = InjL Lω ωʟ
```

An internal injection moves along equal carriers, by inclusions.

```agda
move : (a a' b b' : S) → fst a ≡ fst a' → fst b ≡ fst b' → InjL a b → InjL a' b'
move a a' b b' qa qb h =
  injl-trans a' a b' (inclusion-coded a' a (λ z hz → subst (λ w → ⟨ z ∈ˢ w ⟩) (sym qa) hz))
    (injl-trans a b b' h (inclusion-coded b b' (λ z hz → subst (λ w → ⟨ z ∈ˢ w ⟩) qb hz)))
```

<!--en-->
## The base count: `L_ω` injects into `ω`

The canonical order on `L_ω` is collapsed to an ordinal. Every initial segment of that order fits inside a finite stage, so every collapse value is finite and the collapse ordinal lies within `ω`.
<!--zh-->
## 基础计数：`L_ω` 单射到 `ω`

把 `L_ω` 上的典范序塌缩为一个序数。该序的每个初始段都装进某个有穷阶段，因此每个塌缩值都是有穷的，而塌缩序数位于 `ω` 之内。
<!--ja-->
## 基底の計数：`L_ω` を `ω` へ単射する

`L_ω` 上の正準的な順序を順序数へ崩壊する。その各始切片はある有限段階に収まるので、各崩壊値は有限であり、崩壊順序数は `ω` の内部に入る。
<!--/-->

The stage order at `ω` is a set of L (`relL ω`); its collapse
(src/L/GCH/OrderType.lagda.md) is an ordinal every value of which is finite,
because the segment below a member sits in one finite stage and omega does not
inject into a finite stage.

<!--en-->
### No finite stage contains an injection from omega

A finite-stage tally turns any proposed injection from `ω` into that stage into an injection into a finite index type. Finite search then supplies the contradiction.
<!--zh-->
### 不存在从 omega 到有穷阶段的单射

由于该阶段是有穷的，任何从 `ω` 到该阶段的候选单射都可归结为到有穷索引类型的单射；随后的有限搜索给出矛盾。
<!--ja-->
### omega から有限段階への単射は存在しない

有限段階の一覧は、`ω` からその段階への単射候補を有限添字型への単射へ変える。有限探索から矛盾が得られる。
<!--/-->

src/L/Choice/FiniteStageOrders.lagda.md tallies the finite stage `L_n`. Excluded middle
decides equality with each entry, and finite search chooses a tally index for
every member. An injection of omega into `L_n` therefore composes to one into
`# size`, which `finite-excl-ω` refutes.

```agda
private
  module FinNo (n : ℕ) where
    t : Tally (finiteStage n)
    t = StageOrder.tally (stageOrder n)

    open Tally t using ( size; item; onto )
```

Finite search returns the index together with its equation; the tally's
surjectivity rules out the unsuccessful branch.

```agda
    named : (x : V ℓ) → ⟨ x ∈ˢ finiteStage n ⟩ → Σ[ i ∈ Fin size ] (item i ≡ x)
    named x hx = decRec (λ q → q) (λ nq → Empty.rec (PT.rec Empty.isProp⊥ nq (onto x hx)))
      (DecΣ size (λ i → item i ≡ x)
        (λ i → Sum.rec yes no (lem ((item i ≡ x) , setIsSet (item i) x))))

    noinj : (f : ⟪ ω ⟫ → ⟪ Lset (# n) ⟫)
          → ((x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y) → Empty.⊥
    noinj f finj = finite-excl-ω (# size) (numeral-ord size) (#∈ω size)
      (λ x → q x , q x) (λ x y e → finj x y (qq x y (cong fst e)))
      where
      vl : ⟪ ω ⟫ → V ℓ
      vl x = ⟪ Lset (# n) ⟫↪ (f x)
      mm : (x : ⟪ ω ⟫) → ⟨ vl x ∈ˢ finiteStage n ⟩
      mm x = member (Lset (# n)) (f x)
      q : ⟪ ω ⟫ → ⟪ # size ⟫
      q x = fromFin size (toℕ (named (vl x) (mm x) .fst) , toℕ<n (named (vl x) (mm x) .fst))
      qq : (x y : ⟪ ω ⟫) → q x ≡ q y → f x ≡ f y
      qq x y e = ↪-inj {a = Lset (# n)}
        (sym (named (vl x) (mm x) .snd)
          ∙ cong item (inj-toℕ (cong fst (fromFin-inj size _ _ e)))
          ∙ named (vl y) (mm y) .snd)

  NoInto : V ℓ → Type ℓ
  NoInto w = (f : ⟪ ω ⟫ → ⟪ Lset w ⟫)
           → ((x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y) → Empty.⊥

  no-inj-fin : (g : V ℓ) → ⟨ g ∈ˢ ω ⟩ → NoInto g
  no-inj-fin g g∈ω = PT.rec (isPropΠ2 (λ _ _ → Empty.isProp⊥))
    (λ { (k , e) → subst NoInto e (FinNo.noinj (lower k)) }) g∈ω
```

<!--en-->
### The canonical order on `L_ω` as a set of L

The stage order at `ω` already belongs to `L`. Its membership reading identifies its graph with ordered pairs of stage members, providing the domain clause required by the order-type construction.
<!--zh-->
### 作为 L 中集合的 `L_ω` 典范序

`ω` 处的阶段序已经属于 `L`。其成员读法把图识别为阶段成员的有序对，从而给出序型构造所需的定义域条件。
<!--ja-->
### L の集合としての `L_ω` 上の正準的順序

`ω` における段階順序は既に `L` に属する。その所属の読み方は、グラフを段階要素の順序対と同定し、順序型構成に必要な定義域条件を与える。
<!--/-->

`relL ω` is the stage order at omega, realized as an element of L
(src/L/Choice/OrderTable.lagda.md). `Related` says what its members are: pairs of two
members of the stage. That is the domain hypothesis `OrderType.Code` asks for.

```agda
hω : ⟨ isL ω ⟩
hω = isL-ord ω ω-ord

Rω : SL.S
Rω = relL ω hω ω-ord

specω : IsRel ω Rω
specω = relL-spec ω hω ω-ord

Rsub : (y x : SL.S) → Holds Rω y x
     → ⟨ fst y ∈ˢ Lset ω ⟩ × ⟨ fst x ∈ˢ Lset ω ⟩
Rsub y x h = PT.rec isP
  (λ { (_ , h₁) → PT.rec isP
    (λ { (a , h₂) → PT.rec isP
      (λ { (b , (q , _)) →
             subst (λ w → ⟨ w ∈ˢ Lset ω ⟩) (sym (pr-inj q .fst)) (a .snd)
           , subst (λ w → ⟨ w ∈ˢ Lset ω ⟩) (sym (pr-inj q .snd)) (b .snd) })
      h₂ })
    h₁ })
  rel
  where
  isP : isProp (⟨ fst y ∈ˢ Lset ω ⟩ × ⟨ fst x ∈ˢ Lset ω ⟩)
  isP = isProp× (snd (fst y ∈ˢ Lset ω)) (snd (fst x ∈ˢ Lset ω))
  rel : ⟨ Related ω (pr (fst y) (fst x)) ⟩
  rel = subst (λ w → ⟨ Related ω w ⟩) (prʟ-fst y x)
    (specω (prʟ y x) .fst
      (subst (λ w → ⟨ w ∈ˢ fst Rω ⟩) (sym (prʟ-fst y x)) h))

module OT = Code Lω Rω Rsub using ( module Conjuncts; Dom; _≺_; isProp≺; ≺-in; ≺-out )
```

The host order at the same presentation, and the two directions
between it and the sealed relation of the collapse.

```agda
Wω : SWO ⟪ Lset ω ⟫
Wω = carry (Lset ω) (orderAt ω ω-ord)

open SWO Wω using () renaming ( _<∙_ to _<ω_ )

≺→< : (a b : OT.Dom) → a OT.≺ b → a <ω b
≺→< a b k = ixRel-rep ω ω-ord Rω specω a b (OT.≺-out a b k)

<→≺ : (a b : OT.Dom) → a <ω b → a OT.≺ b
<→≺ a b k = OT.≺-in a b (ixRel-fill ω ω-ord Rω specω a b k)

wfω : WellFounded OT._≺_
wfω m = go (SWO.wf∙ Wω m)
  where
  go : {n : OT.Dom} → Acc _<ω_ n → Acc OT._≺_ n
  go {n} (acc r) = acc (λ n' k → go (r n' (≺→< n' n k)))

transω : {a b c : OT.Dom} → a OT.≺ b → b OT.≺ c → a OT.≺ c
transω {a} {b} {c} k k' =
  <→≺ a c (SWO.trans∙ Wω a b c (≺→< a b k) (≺→< b c k'))

triω : (a b : OT.Dom) → (a OT.≺ b) ⊎ ((a ≡ b) ⊎ (b OT.≺ a))
triω a b = go (SWO.tri∙ Wω a b)
  where
  go : TriW (a <ω b) (a ≡ b) (b <ω a)
     → (a OT.≺ b) ⊎ ((a ≡ b) ⊎ (b OT.≺ a))
  go (lt h) = inl (<→≺ a b h)
  go (eq e) = inr (inl e)
  go (gt h) = inr (inr (<→≺ b a h))

module C = OT.Conjuncts wfω transω using ( module Inj; col; col-ord; col-out; colTable; otL; otL-out )
module I = C.Inj triω using ( code; col-inj )
```

<!--en-->
### Every predecessor segment lies in a finite stage

The stage order compares birth stages first. Hence every predecessor of a member of `L_ω` is born no later than that member and belongs to one common finite stage.
<!--zh-->
### 每个前驱段都位于一个有穷阶段

阶段序首先比较诞生阶段。因此，`L_ω` 中一个成员的每个前驱都不晚于该成员诞生，并共同属于某个有穷阶段。
<!--ja-->
### 各前者区間は一つの有限段階に入る

段階順序はまず誕生段階を比較する。したがって、`L_ω` の要素の各前者はその要素より遅く生まれることがなく、一つの共通な有限段階に属する。
<!--/-->

The stage order compares the BIRTH first (src/L/Choice/StageOrders.lagda.md,
`Family._≺_`), so a predecessor of `x` is born at or below the birth of `x`,
hence belongs to the stage one above that birth. At omega that stage is finite.

```agda
private
  module F = Family ω (λ δ _ → orderAt δ) ω-ord using ( _≺_; bornAt )

  unfoldω : (a b : MemOf (Lset ω))
          → relOf (orderAt ω ω-ord) a b ≡ F._≺_ a b
  unfoldω a b = cong (λ z → relOf (z ω-ord) a b) (orderAt-step ω)

  bAt : MemOf (Lset ω) → V ℓ
  bAt a = F.bornAt a .fst

  bAt∈ω : (a : MemOf (Lset ω)) → ⟨ bAt a ∈ˢ ω ⟩
  bAt∈ω a = F.bornAt a .snd

  bAt-ord : (a : MemOf (Lset ω)) → IsOrd (bAt a)
  bAt-ord a = mem-ord {A = ω} ω-ord (bAt a) (bAt∈ω a)

  self-at : (a : MemOf (Lset ω)) → ⟨ a .fst ∈ˢ Lset (sucV (bAt a)) ⟩
  self-at a = birth-mem (a .fst) (Lset→isL ω ω-ord (a .fst) (a .snd))

  step-bound : (a b : MemOf (Lset ω)) → F._≺_ a b
             → ⟨ a .fst ∈ˢ Lset (sucV (bAt b)) ⟩
  step-bound a b (inl h) =
    raise (suc∈or≡ (bAt a) (bAt b) (bAt-ord a) (bAt-ord b) h)
    where
    raise : ⟨ sucV (bAt a) ∈ˢ bAt b ⟩ ⊎ (sucV (bAt a) ≡ bAt b)
          → ⟨ a .fst ∈ˢ Lset (sucV (bAt b)) ⟩
    raise (inl k) = Lset-mono {α = sucV (bAt b)} {β = sucV (bAt a)}
      (∈sucV-inl {A = bAt b} {x = sucV (bAt a)} k) (self-at a)
    raise (inr e) = Lset-mono {α = sucV (bAt b)} {β = sucV (bAt a)}
      (subst (λ w → ⟨ sucV (bAt a) ∈ˢ sucV w ⟩) e (self∈sucV (sucV (bAt a))))
      (self-at a)
  step-bound a b (inr (e , u)) =
    subst (λ w → ⟨ a .fst ∈ˢ Lset (sucV w) ⟩) (sym e) (u .fst)

  atIx : OT.Dom → MemOf (Lset ω)
  atIx m = ⟪ Lset ω ⟫↪ m , memOf (Lset ω) m

  gOf : OT.Dom → V ℓ
  gOf p = sucV (bAt (atIx p))

  gOf∈ω : (p : OT.Dom) → ⟨ gOf p ∈ˢ ω ⟩
  gOf∈ω p = ω-limit (bAt (atIx p)) (bAt∈ω (atIx p))

  seg-bound : (p r : OT.Dom) → r OT.≺ p
            → ⟨ ⟪ Lset ω ⟫↪ r ∈ˢ Lset (gOf p) ⟩
  seg-bound p r k =
    step-bound (atIx r) (atIx p) (transport (unfoldω (atIx r) (atIx p)) (≺→< r p k))
```

<!--en-->
### The collapse order type lies inside omega

A collapse value is the order type of one predecessor segment. Since that segment injects into a finite stage, `ω` cannot inject into it, and ordinal comparison places the value below `ω`.
<!--zh-->
### 塌缩序型位于 omega 之内

一个塌缩值是某个前驱段的序型。由于该段单射到有穷阶段，`ω` 不能单射到其中；序数比较遂把该值置于 `ω` 以下。
<!--ja-->
### 崩壊の順序型は omega の内部にある

崩壊値は一つの前者区間の順序型である。その区間は有限段階へ単射するので、`ω` からそこへの単射は存在せず、順序数の比較によって値は `ω` より下に置かれる。
<!--/-->

The collapse value at `p` is the order type of the segment below `p`. That
segment injects, ambiently, into the finite stage of section 3, so omega does
not inject into it; and an ordinal that omega does not reach is a member of
omega. This is the shape of `Step.col-fin` (src/L/GCH/CardinalSquareLaw.lagda.md:979).

```agda
private
  Seg : OT.Dom → V ℓ → Type (ℓ-suc ℓ)
  Seg p b = Σ[ r ∈ OT.Dom ] ((r OT.≺ p) × (C.col r ≡ b))

  isPropSeg : (p : OT.Dom) (b : V ℓ) → isProp (Seg p b)
  isPropSeg p b (r , _ , e) (r' , _ , e') =
    Σ≡Prop (λ z → isProp× (OT.isProp≺ z p) (setIsSet _ _))
      (I.col-inj r r' (e ∙ sym e'))

  seg : (p : OT.Dom) (b : V ℓ) → ⟨ b ∈ˢ C.col p ⟩ → Seg p b
  seg p b h = PT.rec (isPropSeg p b) (λ z → z) (C.col-out p b h)

col-fin : (p : OT.Dom) → ⟨ C.col p ∈ˢ ω ⟩
col-fin p = go (ord-tri (C.col p) (C.col-ord p) ω ω-ord)
  where
  refute : ((z : V ℓ) → ⟨ z ∈ˢ ω ⟩ → ⟨ z ∈ˢ C.col p ⟩) → Empty.⊥
  refute sub = no-inj-fin (gOf p) (gOf∈ω p) f f-inj
    where
    s : (x : ⟪ ω ⟫) → Seg p (⟪ ω ⟫↪ x)
    s x = seg p (⟪ ω ⟫↪ x) (sub (⟪ ω ⟫↪ x) (member ω x))
    fb : (x : ⟪ ω ⟫)
       → Σ[ m ∈ ⟪ Lset (gOf p) ⟫ ] (⟪ Lset (gOf p) ⟫↪ m ≡ ⟪ Lset ω ⟫↪ (s x .fst))
    fb x = fiber (Lset (gOf p)) (seg-bound p (s x .fst) (s x .snd .fst))
    f : ⟪ ω ⟫ → ⟪ Lset (gOf p) ⟫
    f x = fb x .fst
    f-inj : (x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y
    f-inj x y e = ↪-inj {a = ω}
      (sym (s x .snd .snd) ∙ cong C.col rr ∙ s y .snd .snd)
      where
      rr : s x .fst ≡ s y .fst
      rr = ↪-inj {a = Lset ω}
        (sym (fb x .snd) ∙ cong ⟪ Lset (gOf p) ⟫↪ e ∙ fb y .snd)

  go : ⟨ C.col p ∈ˢ ω ⟩ ⊎ ((C.col p ≡ ω) ⊎ ⟨ ω ∈ˢ C.col p ⟩) → ⟨ C.col p ∈ˢ ω ⟩
  go (inl k) = k
  go (inr (inl e)) =
    Empty.rec (refute (λ z z∈ω → subst (λ w → ⟨ z ∈ˢ w ⟩) (sym e) z∈ω))
  go (inr (inr ω∈c)) =
    Empty.rec (refute (λ z z∈ω → C.col-ord p .fst z∈ω ω∈c))

otL⊆ω : (z : V ℓ) → ⟨ z ∈ˢ fst C.otL ⟩ → ⟨ z ∈ˢ ω ⟩
otL⊆ω z h = PT.rec (snd (z ∈ˢ ω))
  (λ { (b , e) → subst (λ w → ⟨ w ∈ˢ ω ⟩) e (col-fin b) })
  (C.otL-out z h)
```

<!--en-->
### The base injection and the infinite-stage interface

Restricting the collapse to its ordinal image gives the coded injection `L_ω ↪ ω`. This is the base premise consumed by the general theorem that every infinite constructible stage injects into its index.
<!--zh-->
### 基础单射与无穷阶段接口

把塌缩限制到其序数像，即得编码单射 `L_ω ↪ ω`。这正是一般定理所需的基础前提；该定理断言每个无穷可构造阶段都单射到其指标。
<!--ja-->
### 基底単射と無限段階のインターフェース

崩壊をその順序数像へ制限すると、符号化された単射 `L_ω ↪ ω` が得られる。これは、各無限構成可能段階をその添字へ単射する一般定理が使う基底の前提である。
<!--/-->

```agda
limit-stage-counted : LimitStageCounted
limit-stage-counted =
  injl-trans Lω C.otL ωʟ ∣ C.colTable , I.code ∣₁
    (inclusion-coded C.otL ωʟ otL⊆ω)
```

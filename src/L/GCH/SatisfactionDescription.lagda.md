<!--en-->
# A Δ₀ description of the satisfaction table

The uniform satisfaction table is useful only after the model can recognize it. This chapter describes the table by a bounded formula and relates that description to the semantic recursion developed earlier.
<!--zh-->
# 满足表的 Δ₀ 描述

统一满足表只有在模型能够识别它之后才可用于内部论证。本章用有界公式描述该表，并把这一描述与此前建立的语义递归联系起来。
<!--ja-->
# 充足関係表の Δ₀ 記述

一様な充足関係表は、モデル自身がそれを認識できて初めて内部の議論に使える。本章では表を有界論理式で記述し、その記述を先に構成した意味論的再帰と結び付ける。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.SatisfactionDescription {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; _∧̇_ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∧ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.EnvironmentSet {ℓ} lem using ( envSet )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes; AllCodes-out; key∈AllCodes; keyS )
open import L.Coding.UniformSatisfaction {ℓ} lem using ( module Table; val-at )
open import L.Coding.PinnedRecursion {ℓ} lem using ( module Match ) public
open import L.Coding.PinnedRecursion {ℓ} lem using ( module SatSoundC; module SatHoldsC )
open import L.Coding.Quantification {ℓ} using ( f0; down )
open import L.Coding.CodeAlphabet {ℓ} using ( module Alphabet )
open import L.Coding.CodeDomain {ℓ} using ( Tags; codesAt; Δ₀-codesAt )
open import L.Coding.CodeDomainAdequacy {ℓ} lem
  using ( module CodesSound; module CodesComplete; module CodesHolds )
open import L.Coding.EnvironmentTower {ℓ} lem
  using ( towerAt; Δ₀-towerAt; module Tower; module TowerRead; module TowerHolds )
open import L.Coding.SatisfactionClauses {ℓ} using ( tableAt; Δ₀-tableAt )
open import L.Coding.SatisfactionClauseSemantics {ℓ} lem using ( module Frame; module Bridge )
open import L.Coding.SatisfactionGraphSet {ℓ} lem using ( module SatGraph )

open import Cubical.Data.Vec using ( lookup )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Foundations.HLevels using ( isPropΣ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ)) using ()
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

The table is sound. A table satisfying the ten clauses over the code set and
the tower records, at the key of every formula, the value the meta-level
recursion built there: induction on the formula, one clause reader and one
bridge per constructor.

```agda
```

<!--en-->
## Soundness of the bounded description

The description decomposes a satisfaction-table entry into its formula code, environment, and recursively computed truth value. Each clause is shown to imply the corresponding row of the uniform satisfaction relation.
<!--zh-->
## 有界描述的可靠性

该描述把满足关系表的表项分解为公式码、环境与递归计算所得的真值。逐条证明每个子句都会推出统一满足关系中的相应行。
<!--ja-->
## 有界な記述の健全性

この記述は、充足関係表の項目を論理式コード、環境、再帰的に計算した真理値へ分解する。各節から一様な充足関係の対応する行が従うことを示す。
<!--/-->

```agda
module SatSound {m : ℕ} (T w C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) (tg : Tags γ N)
  (hE : ⟨ γ ⊨ towerAt E w (N f0) ⟩) (hC : ⟨ γ ⊨ codesAt C w E N ⟩)
  (hT : ⟨ γ ⊨ tableAt T w C E N ⟩) where
  open Alphabet W
  open Bridge W
  private
    Tv = fst (lookup T γ)
    Cv = fst (lookup C γ)
    Ev = fst (lookup E γ)
    module TR = TowerRead E w (N f0) γ W qw (tg f0) hE
    arity : (n F : S) → ⟨ pr (fst n) (fst F) ∈ Ev ⟩ → ∥ Σ[ k ∈ ℕ ] (fst n ≡ # k) ∥₁
    arity n F q∈ = PT.map (λ { (k , (qk , _)) → k , qk }) (TR.entry-out n F q∈)
    module CS = CodesSound C w E N γ W qw tg arity (hC .fst)
    module CC = CodesComplete C w E N γ W qw tg TR.entry-in (hC .snd)
    module Fr = Frame T w C E N γ tg
    module SC = SatSoundC T w C E N γ W qw tg hE CS.closed hT

    hTot = hT .fst
    hOn = hT .snd .fst
```

The value at a subformula's key, from totality.

```agda
    sub : ∀ {n} (a : Formula Ab n) → ∥ Σ[ ya ∈ S ] ⟨ pr (fst (keyS W a)) (fst ya) ∈ Tv ⟩ ∥₁
    sub a = Fr.total-out hTot (keyS W a) (CC.key-in a)
```

EVERY ENTRY IS PINNED. The recursion is the general one of
src/L/Coding/PinnedRecursion.lagda.md, read at the code set: the shape clause supplies
the closure it asks of the index set, and completeness discharges the membership
its statement carries.

```agda
  Pinned : ∀ {n} (ψ : Formula Ab n) → Type (ℓ-suc ℓ)
  Pinned ψ = (y : S) → ⟨ pr (fst (keyS W ψ)) (fst y) ∈ Tv ⟩ → fst y ≡ fst (SatW ψ)

  pinned : ∀ {n} (ψ : Formula Ab n) → Pinned ψ
  pinned ψ = SC.pinned ψ (CC.key-in ψ)
```

WHAT SOUNDNESS SAYS. `C` is the code set, `E` the tower, and `T` the graph of
the uniform table: every entry is at a key and records the table's value there,
and every key has that entry.

```agda
  C-out : (c : S) → ⟨ fst c ∈ Cv ⟩ → ⟨ fst c ∈ fst (AllCodes W) ⟩
  C-out c c∈ = PT.rec (snd (fst c ∈ fst (AllCodes W)))
    (λ { (k , ψ , e) → subst (λ u → ⟨ u ∈ fst (AllCodes W) ⟩) (sym e) (key∈AllCodes W ψ) })
    (CS.key-out c c∈)

  C-in : (c : S) → ⟨ fst c ∈ fst (AllCodes W) ⟩ → ⟨ fst c ∈ Cv ⟩
  C-in c c∈ = PT.rec (snd (fst c ∈ Cv))
    (λ { (k , ψ , e) → subst (λ u → ⟨ u ∈ Cv ⟩) (sym e) (CC.key-in ψ) })
    (AllCodes-out W c c∈)

  E-out : (n F : S) → ⟨ pr (fst n) (fst F) ∈ Ev ⟩
        → ∥ Σ[ k ∈ ℕ ] ((fst n ≡ # k) × (fst F ≡ fst (envSet W k))) ∥₁
  E-out = TR.entry-out

  E-in : (k : ℕ) → ⟨ pr (# k) (fst (envSet W k)) ∈ Ev ⟩
  E-in = TR.entry-in

  T-out : (x y : S) → ⟨ pr (fst x) (fst y) ∈ Tv ⟩
        → Σ[ mx ∈ ⟨ fst x ∈ fst (AllCodes W) ⟩ ] (fst y ≡ fst (Table.val W W x mx))
  T-out x y h = PT.rec (isPropΣ (snd (fst x ∈ fst (AllCodes W))) (λ mx → setIsSet _ _))
    (λ { (c , yc , (ee , c∈)) → PT.rec (isPropΣ (snd (fst x ∈ fst (AllCodes W))) (λ mx → setIsSet _ _))
      (λ { (k , ψ , e) →
        let q = pr-inj ee
            qx : fst x ≡ fst (keyS W ψ)
            qx = q .fst ∙ e
            mx : ⟨ fst x ∈ fst (AllCodes W) ⟩
            mx = subst (λ u → ⟨ u ∈ fst (AllCodes W) ⟩) (sym qx) (key∈AllCodes W ψ)
        in mx , ( pinned ψ y (subst (λ u → ⟨ u ∈ Tv ⟩) (cong (λ a → pr a (fst y)) qx) h)
                ∙ sym (cong fst (val-at W W ψ x mx qx)) ) })
      (CS.key-out c c∈) })
    (Fr.onC-out hOn (down (lookup T γ) (pr (fst x) (fst y)) h) h)

  T-in : (x : S) (mx : ⟨ fst x ∈ fst (AllCodes W) ⟩) → ⟨ pr (fst x) (fst (Table.val W W x mx)) ∈ Tv ⟩
  T-in x mx = PT.rec (snd (pr (fst x) (fst (Table.val W W x mx)) ∈ Tv))
    (λ { (k , ψ , e) → PT.rec (snd (pr (fst x) (fst (Table.val W W x mx)) ∈ Tv))
      (λ { (y , my) →
        subst (λ u → ⟨ u ∈ Tv ⟩)
          (cong₂ pr (sym e) (pinned ψ y my ∙ sym (cong fst (val-at W W ψ x mx e))))
          my })
      (sub ψ) })
    (AllCodes-out W x mx)
```

The table is complete. The graph of the uniform table, over the code set and the
tower, satisfies the description: each clause is read at its frame, the code is
decoded, the entries are read as the table's values, and the bridge supplies the
body.

A code's constructor and payload, from its tag, are read in
src/L/Coding/PinnedRecursion.lagda.md.

```agda
```

<!--en-->
## Completeness and the two readings

Conversely, every genuine row of the uniform satisfaction table supplies the witnesses required by the bounded description. Soundness and completeness combine into internal and ambient read lemmas for the same formula.
<!--zh-->
## 完备性与两种读法

反过来，统一满足关系表的每个真实表项都会给出有界描述所需的见证。可靠性与完备性合在一起，为同一条公式给出内部读引理与外围读引理。
<!--ja-->
## 完全性と二つの読み方

逆に、一様な充足関係表の各々の実際の項目は、有界な記述に必要な証人を与える。健全性と完全性を合わせると、同じ論理式について内部と周囲の二つの読み補題が得られる。
<!--/-->

```agda
module SatHolds {m : ℕ} (T w C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) (qT : fst (lookup T γ) ≡ fst (SatGraph.pairs W))
  (qC : fst (lookup C γ) ≡ fst (AllCodes W)) (qE : fst (lookup E γ) ≡ fst (Tower.tower W))
  (tg : Tags γ N) where
  open Alphabet W
  open Bridge W
  private
    Tv = fst (lookup T γ)
    Cv = fst (lookup C γ)
```

An entry of `T` is the table's value at a key.

```agda
    val≡ : ∀ {n} (ψ : Formula Ab n) (c yc : S) → fst c ≡ fst (keyS W ψ)
         → ⟨ pr (fst c) (fst yc) ∈ Tv ⟩ → fst yc ≡ fst (SatW ψ)
    val≡ ψ c yc qc h =
      let p = SatGraph.pairs-out W c yc (subst (λ u → ⟨ pr (fst c) (fst yc) ∈ u ⟩) qT h)
      in p .snd ∙ cong fst (SatGraph.valOf≡ W c (p .fst)) ∙ cong fst (val-at W W ψ c (p .fst) qc)
```

A member of `C` at arity `n` decodes.

```agda
    decode : (c : S) → ⟨ fst c ∈ Cv ⟩ → (n : ℕ) (z : V ℓ) → fst c ≡ pr (# n) z
           → ∥ Σ[ ψ ∈ Formula Ab n ] (z ≡ cd ψ) ∥₁
    decode c c∈ = Match.decodeAll W c (subst (λ u → ⟨ fst c ∈ u ⟩) qC c∈)
```

The two halves of the domain.

```agda
    tot : (c : S) → ⟨ fst c ∈ Cv ⟩ → ∥ Σ[ yc ∈ S ] ⟨ pr (fst c) (fst yc) ∈ Tv ⟩ ∥₁
    tot c c∈ =
      let mx = subst (λ u → ⟨ fst c ∈ u ⟩) qC c∈
      in ∣ SatGraph.valOf W c mx , subst (λ u → ⟨ pr (fst c) (fst (SatGraph.valOf W c mx)) ∈ u ⟩) (sym qT) (SatGraph.pairs-in W c mx) ∣₁

    onc : (e : S) → ⟨ fst e ∈ Tv ⟩
        → ∥ Σ[ c ∈ S ] Σ[ yc ∈ S ] ((fst e ≡ pr (fst c) (fst yc)) × ⟨ fst c ∈ Cv ⟩) ∥₁
    onc e e∈ = PT.map
      (λ { (x , mx , ee) → x , SatGraph.valOf W x mx , (ee , subst (λ u → ⟨ fst x ∈ u ⟩) (sym qC) mx) })
      (SatGraph.pairs-shape W e (subst (λ u → ⟨ fst e ∈ u ⟩) qT e∈))
```

THE DESCRIPTION IS SATISFIED. The general theorem of
src/L/Coding/PinnedRecursion.lagda.md, at the four objects the all-codes reading names.

```agda
  holds : ⟨ γ ⊨ tableAt T w C E N ⟩
  holds = SatHoldsC.holds W T w C E N γ qw tg
    (TowerHolds.holds E w (N f0) γ W qw qE (tg f0)) val≡ decode tot onc
```

The description, sealed. "`T` is the satisfaction table of `w` over the code set
`C` and the environment tower `E`." The seal holds the three conjuncts; its
readers are the two projections.

```agda
opaque
  satAt : ∀ {m} → Fin m → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
  satAt T w C E N = towerAt E w (N f0) ∧̇ (codesAt C w E N ∧̇ tableAt T w C E N)

opaque
  unfolding satAt

  Δ₀-satAt : ∀ {m} (T w C E : Fin m) (N : Fin 10 → Fin m) → Δ₀ (satAt T w C E N)
  Δ₀-satAt T w C E N = δ-∧ (Δ₀-towerAt E w (N f0)) (δ-∧ (Δ₀-codesAt C w E N) (Δ₀-tableAt T w C E N))

  satAt-out : ∀ {m} (T w C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m)
            → ⟨ γ ⊨ satAt T w C E N ⟩
            → ⟨ γ ⊨ towerAt E w (N f0) ⟩ × (⟨ γ ⊨ codesAt C w E N ⟩ × ⟨ γ ⊨ tableAt T w C E N ⟩)
  satAt-out T w C E N γ h = h

  satAt-in : ∀ {m} (T w C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m)
           → ⟨ γ ⊨ towerAt E w (N f0) ⟩ → ⟨ γ ⊨ codesAt C w E N ⟩ → ⟨ γ ⊨ tableAt T w C E N ⟩
           → ⟨ γ ⊨ satAt T w C E N ⟩
  satAt-in T w C E N γ hE hC hT = hE , (hC , hT)
```

The two theorems. Soundness: a reading of `satAt` at `(T, w, C, E)` makes `T`
the graph of the uniform table of `w`, `C` the code set and `E` the tower, each
read both ways. Completeness: the graph, the code set and the tower satisfy
`satAt`.

```agda
module SatRead {m : ℕ} (T w C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) (tg : Tags γ N) (h : ⟨ γ ⊨ satAt T w C E N ⟩) where
  private
    module SS = SatSound T w C E N γ W qw tg
      (satAt-out T w C E N γ h .fst) (satAt-out T w C E N γ h .snd .fst) (satAt-out T w C E N γ h .snd .snd)
  open SS public using ( C-out; C-in; E-out; E-in; T-out; T-in )

sat-complete : ∀ {m} (T w C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (W : S)
             → fst (lookup w γ) ≡ fst W
             → fst (lookup T γ) ≡ fst (SatGraph.pairs W)
             → fst (lookup C γ) ≡ fst (AllCodes W)
             → fst (lookup E γ) ≡ fst (Tower.tower W)
             → Tags γ N → ⟨ γ ⊨ satAt T w C E N ⟩
sat-complete T w C E N γ W qw qT qC qE tg =
  satAt-in T w C E N γ
    (TowerHolds.holds E w (N f0) γ W qw qE (tg f0))
    (CodesHolds.holds C w E N γ W qw qC qE tg)
    (SatHolds.holds T w C E N γ W qw qT qC qE tg)
```

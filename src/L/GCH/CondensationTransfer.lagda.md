<!--en-->
# Transferring structure through condensation

At a superadequate stage, an elementary hull collapses to a smaller constructible stage. This chapter identifies the formulas needed for that transfer and carries the hierarchy data across the collapse.
<!--zh-->
# 通过凝聚搬运结构

在超充分阶段，一个初等 Skolem 壳会塌缩到更小的可构造阶段。本章找出搬运所需的公式，并沿塌缩把层级数据带到另一侧。
<!--ja-->
# 凝縮を通して構造を移す

強化された十分な段階では、初等的な Skolem 包はより小さい構成可能段階へ崩壊する。本章では移送に必要な論理式を特定し、階層のデータを崩壊写像に沿って運ぶ。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.CondensationTransfer {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; ∃̇_ )
open import FOL.Manipulation.ConstantMapping using ( mapFo; embed )
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using
  ( IsOrd; isL; Lset; Lset-out; Lset-mono; Lset→isL; 𝒟ₒ )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc; ord∈Lset→∈ )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.GCH.SkolemHull {ℓ} lem using
  ( module HullStage; Δ₀-isOrdAt; module Amb
  ; module Frame; _⊨ₚ_; embed-map; isOrd-at-p )
open import L.GCH.HierarchyDescription {ℓ} lem using ( levelFo; Δ₀-levelFo; level-sound; level-complete )
open import L.GCH.AdequateStages {ℓ} lem using ( Superadequate; Adequate; Lset∈suc )

open import Cubical.Data.Vec using ( _∷_; [] )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Foundations.HLevels using ( isProp× )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module SemVᵃ = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemVᵃ using ( _^_ )
```

<!--en-->
## Formulas that identify the level witnesses

The transfer requires simultaneously a level value, its ordinal index, and the proof that the value is the corresponding constructible stage. Packaging all three in one formula lets elementarity bring the complete witness into the hull.
<!--zh-->
## 识别层见证的公式

搬运需要同时给出一个层值、它的序数指标，以及该值就是相应可构造阶段的证明。三者合并进同一条公式后，初等性便能把完整见证带入 Skolem 壳。
<!--ja-->
## 階層の証人を特定する論理式

移送では、階層の値、その順序数添字、およびその値が対応する構成可能段階であることを同時に要求する。三つを一つの論理式にまとめることで、初等性により完全な証人を Skolem 包へ取り込める。
<!--/-->

Each query binds the level value, ordinal parameter, and level witness together.
Elementarity therefore returns all three as members of the hull in one step.

```agda
isOrd-at-p-out : (a p z : S) → ⟨ (a ∷ p ∷ z ∷ []) ⊨ₚ isOrd-at-p ⟩ → IsOrd p
isOrd-at-p-out a p z h =
    ( λ {x₁} {y} y∈x₁ x₁∈p → h .fst x₁ x₁∈p y y∈x₁ )
  , ( λ b b∈p {x₁} {y} y∈x₁ x₁∈b → h .snd b b∈p x₁ x₁∈b y y∈x₁ )
```

<!--en-->
## Transferring hierarchy information through the collapse

At a strengthened adequate stage, elementarity places the required witnesses in the hull and the collapse sends them into `L`. The two closure hypotheses then identify the collapse image with the appropriate hierarchy levels on its own ordinals.
<!--zh-->
## 沿塌缩搬运层级信息

在超充分阶段，初等性把所需见证放入 Skolem 壳，塌缩则把它们送进 `L`。随后两条闭合假设将塌缩像识别为它自身序数处的相应层级。
<!--ja-->
## 崩壊を通して階層の情報を移す

強化された十分な段階では、初等性が必要な証人を Skolem 包へ入れ、崩壊がそれらを `L` へ送る。二つの閉性の仮定により、崩壊像をその順序数に対応する階層と同定できる。
<!--/-->

One hull stage at `HullStage`'s telescope, elementary (`elem`), superadequate
(`sup`), and with its collapse image inside L (`pixL`). The parameter `pixL`
is supplied by `PiIn.πX-isL` through `Discharge` in `L.GCH.ConstructibleHull`, using
induction on the stage of the argument. That proof precedes the application
of condensation: `level-sound` in `L.GCH.HierarchyDescription` reads its three slots
in L, so it needs the constructibility of the collapse values.

```agda
module Condense (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : Frame.A.Elementary lam ordλ succλ X X⊆L ∅∈λ)
  (sup : Superadequate lam)
  (pixL : (x : S) → ⟨ x ∈ˢ HullStage.C.πX lam ordλ succλ X X⊆L ∅∈λ ⟩
        → ⟨ isL x ⟩)
  where

  module F = Frame lam ordλ succλ X X⊆L ∅∈λ using (module A; module Carry; module HS)
  module A = F.A using (SM; module SemM; inL)
  module Mse = A.SemM.At A.SM id using (_⊨_)
  module HS = F.HS using (module ASt; module C; module Condense; module H; M)
  module Cy = F.Carry elem using (atL; atM; member-push; push; pull)

  open HS.H using ( Hull⊆L )

  M : S
  M = HS.M

  π : S → S
  π = HS.C.π

  isLλ : (x : S) → ⟨ x ∈ˢ Lset lam ⟩ → ⟨ isL x ⟩
  isLλ = Lset→isL lam ordλ

  Lset∈Lλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ Lset d ∈ˢ Lset lam ⟩
  Lset∈Lλ d d∈λ = Lset-mono {α = lam} {β = sucV d} (succλ d d∈λ) (Lset∈suc d)

  ord∈Lλ : (d : S) → IsOrd d → ⟨ d ∈ˢ lam ⟩ → ⟨ d ∈ˢ Lset lam ⟩
  ord∈Lλ d od d∈λ =
    Lset-mono {α = lam} {β = sucV d} (succλ d d∈λ) (ord∈Lset-suc d od)
```

Ordinality crosses the collapse in both directions.

```agda
  ord-push : (d : S) (d∈M : ⟨ d ∈ˢ M ⟩) → IsOrd d → IsOrd (π d)
  ord-push d d∈M od =
    Amb.isOrdAt-out (π d)
      (Cy.push Δ₀-isOrdAt ((d , d∈M) ∷ []) (Amb.isOrdAt-in d od))

  ord-pull : (d : S) (d∈M : ⟨ d ∈ˢ M ⟩) → IsOrd (π d) → IsOrd d
  ord-pull d d∈M oπd =
    Amb.isOrdAt-out d
      (Cy.pull Δ₀-isOrdAt ((d , d∈M) ∷ []) (Amb.isOrdAt-in (π d) oπd))
```

THE STAGE EXISTENTIALS, from `level-complete` at an adequate stage. Each formula
binds all three entries at once, so elementarity returns all three as members of
the hull. Shape A pins the parameter directly to its hull member.

```agda
  findA : A.SM → Formula A.SM 0
  findA dM = ∃̇ (∃̇ (∃̇ (embed levelFo ∧̇ (var (suc zero) ≐ con dM))))

  stageA : (d γ : S) (od : IsOrd d) (adγ : Adequate γ) (d∈γ : ⟨ d ∈ˢ γ ⟩)
         → (dM : A.SM) → fst dM ≡ d
         → ⟨ d ∈ˢ Lset lam ⟩ → ⟨ Lset d ∈ˢ Lset lam ⟩ → ⟨ Lset γ ∈ˢ Lset lam ⟩
         → ⟨ [] HS.ASt.AbsL.⊨ᵐ mapFo A.inL (findA dM) ⟩
  stageA d γ od adγ d∈γ dM ed d∈ Ld∈ Lγ∈ =
    ∣ (Lset γ , Lγ∈) , ∣ (d , d∈) , ∣ (Lset d , Ld∈) , (sat , sym ed) ∣₁ ∣₁ ∣₁
    where
    δ : HS.ASt.SL ^ 3
    δ = (Lset d , Ld∈) ∷ (d , d∈) ∷ (Lset γ , Lγ∈) ∷ []

    amb : ⟨ (Lset d ∷ d ∷ Lset γ ∷ []) ⊨ₚ levelFo ⟩
    amb = level-complete γ adγ d od d∈γ

    sat : ⟨ δ HS.ASt.AbsL.⊨ᵐ mapFo A.inL (embed levelFo) ⟩
    sat = subst (λ ψ → ⟨ δ HS.ASt.AbsL.⊨ᵐ ψ ⟩) (sym (embed-map A.inL levelFo))
            (subst ⟨_⟩ (sym (Cy.atL Δ₀-levelFo δ)) amb)
```

Shape P pins membership of the hull member directly.

```agda
  findP : A.SM → Formula A.SM 0
  findP yM = ∃̇ (∃̇ (∃̇ (embed levelFo ∧̇ (con yM ∈̇ var zero))))

  stageP : (y p γ : S) (op : IsOrd p) (adγ : Adequate γ) (p∈γ : ⟨ p ∈ˢ γ ⟩)
         → (yM : A.SM) → fst yM ≡ y → ⟨ y ∈ˢ Lset p ⟩
         → ⟨ p ∈ˢ Lset lam ⟩ → ⟨ Lset p ∈ˢ Lset lam ⟩ → ⟨ Lset γ ∈ˢ Lset lam ⟩
         → ⟨ [] HS.ASt.AbsL.⊨ᵐ mapFo A.inL (findP yM) ⟩
  stageP y p γ op adγ p∈γ yM ey y∈Lp p∈ Lp∈ Lγ∈ =
    ∣ (Lset γ , Lγ∈) , ∣ (p , p∈) , ∣ (Lset p , Lp∈) , (sat , mem) ∣₁ ∣₁ ∣₁
    where
    δ : HS.ASt.SL ^ 3
    δ = (Lset p , Lp∈) ∷ (p , p∈) ∷ (Lset γ , Lγ∈) ∷ []

    amb : ⟨ (Lset p ∷ p ∷ Lset γ ∷ []) ⊨ₚ levelFo ⟩
    amb = level-complete γ adγ p op p∈γ

    sat : ⟨ δ HS.ASt.AbsL.⊨ᵐ mapFo A.inL (embed levelFo) ⟩
    sat = subst (λ ψ → ⟨ δ HS.ASt.AbsL.⊨ᵐ ψ ⟩) (sym (embed-map A.inL levelFo))
            (subst ⟨_⟩ (sym (Cy.atL Δ₀-levelFo δ)) amb)

    mem : ⟨ fst (A.inL yM) ∈ˢ Lset p ⟩
    mem = subst (λ w → ⟨ w ∈ˢ Lset p ⟩) (sym ey) y∈Lp
```

THE WITNESS. At an ordinal of the hull: its level is in the hull, and a hull
witness reads the level formula at `(Lset d, d, z)`.

```agda
  Witness : S → Type (ℓ-suc ℓ)
  Witness d = ∥ Σ[ z ∈ S ] ( ⟨ z ∈ˢ M ⟩ × ⟨ Lset d ∈ˢ M ⟩
                           × ⟨ (Lset d ∷ d ∷ z ∷ []) ⊨ₚ levelFo ⟩ ) ∥₁

  witness : (d : S) → IsOrd d → ⟨ d ∈ˢ M ⟩ → Witness d
  witness d od d∈M = PT.rec squash₁ step1 (sup d d∈λ)
    where
    d∈Lλ : ⟨ d ∈ˢ Lset lam ⟩
    d∈Lλ = Hull⊆L d d∈M

    d∈λ : ⟨ d ∈ˢ lam ⟩
    d∈λ = ord∈Lset→∈ lam ordλ d od d∈Lλ

    Ld∈Lλ : ⟨ Lset d ∈ˢ Lset lam ⟩
    Ld∈Lλ = Lset∈Lλ d d∈λ

    step1 : Σ[ γ ∈ S ] (⟨ γ ∈ˢ lam ⟩ × ⟨ d ∈ˢ γ ⟩ × Adequate γ) → Witness d
    step1 (γ , γ∈λ , d∈γ , adγ) =
      PT.rec squash₁ takeZ hullSat
      where
      Lγ∈Lλ : ⟨ Lset γ ∈ˢ Lset lam ⟩
      Lγ∈Lλ = Lset∈Lλ γ γ∈λ

      dM : A.SM
      dM = d , d∈M

      hullSat : ⟨ [] Mse.⊨ findA dM ⟩
      hullSat = subst ⟨_⟩ (sym (elem 0 (findA dM) []))
        (stageA d γ od adγ d∈γ dM refl d∈Lλ Ld∈Lλ Lγ∈Lλ)

      finishA : (z d' : A.SM)
              → Σ[ a ∈ A.SM ]
                  ( ⟨ (a ∷ d' ∷ z ∷ []) Mse.⊨ embed levelFo ⟩
                  × (fst d' ≡ d) )
              → Σ[ w ∈ S ] ( ⟨ w ∈ˢ M ⟩ × ⟨ Lset d ∈ˢ M ⟩
                           × ⟨ (Lset d ∷ d ∷ w ∷ []) ⊨ₚ levelFo ⟩ )
      finishA z d' (a , sat , ed) = fst z , snd z , Ld∈M , amb'
        where
        amb : ⟨ (fst a ∷ fst d' ∷ fst z ∷ []) ⊨ₚ levelFo ⟩
        amb = subst ⟨_⟩ (Cy.atM Δ₀-levelFo (a ∷ d' ∷ z ∷ [])) sat

        ea : fst a ≡ Lset d
        ea = level-sound (fst a) (fst d') (fst z)
               (isLλ (fst a) (Hull⊆L (fst a) (snd a)))
               (isLλ (fst d') (Hull⊆L (fst d') (snd d')))
               (isLλ (fst z) (Hull⊆L (fst z) (snd z))) amb
             ∙ cong Lset ed

        Ld∈M : ⟨ Lset d ∈ˢ M ⟩
        Ld∈M = subst (λ w → ⟨ w ∈ˢ M ⟩) ea (snd a)

        amb' : ⟨ (Lset d ∷ d ∷ fst z ∷ []) ⊨ₚ levelFo ⟩
        amb' = subst (λ v → ⟨ (v ∷ d ∷ fst z ∷ []) ⊨ₚ levelFo ⟩) ea
          (subst (λ p → ⟨ (fst a ∷ p ∷ fst z ∷ []) ⊨ₚ levelFo ⟩) ed amb)

      takeD : (z : A.SM)
            → Σ[ d' ∈ A.SM ]
                ⟨ (d' ∷ z ∷ []) Mse.⊨ ∃̇ (embed levelFo ∧̇ (var (suc zero) ≐ con dM)) ⟩
            → Witness d
      takeD z (d' , hd) = PT.map (finishA z d') hd

      takeZ : Σ[ z ∈ A.SM ]
                ⟨ (z ∷ []) Mse.⊨ ∃̇ (∃̇ (embed levelFo ∧̇ (var (suc zero) ≐ con dM))) ⟩
            → Witness d
      takeZ (z , hz) = PT.rec squash₁ (takeD z) hz
```

THE COMMUTATION. The collapse of the level at a hull ordinal is the level at the
collapsed ordinal; `pixL` places the pushed triple in L for `level-sound`.

```agda
  commute : (d : S) → IsOrd d → (d∈M : ⟨ d ∈ˢ M ⟩)
          → ⟨ Lset d ∈ˢ M ⟩ × (π (Lset d) ≡ Lset (π d))
  commute d od d∈M =
    PT.rec (isProp× (snd (Lset d ∈ˢ M)) (isSetS (π (Lset d)) (Lset (π d))))
           go (witness d od d∈M)
    where
    go : Σ[ z ∈ S ] ( ⟨ z ∈ˢ M ⟩ × ⟨ Lset d ∈ˢ M ⟩
                    × ⟨ (Lset d ∷ d ∷ z ∷ []) ⊨ₚ levelFo ⟩ )
       → ⟨ Lset d ∈ˢ M ⟩ × (π (Lset d) ≡ Lset (π d))
    go (z , z∈M , Ld∈M , amb) = Ld∈M , eq
      where
      pushed : ⟨ (π (Lset d) ∷ π d ∷ π z ∷ []) ⊨ₚ levelFo ⟩
      pushed = Cy.push Δ₀-levelFo ((Lset d , Ld∈M) ∷ (d , d∈M) ∷ (z , z∈M) ∷ []) amb

      eq : π (Lset d) ≡ Lset (π d)
      eq = level-sound (π (Lset d)) (π d) (π z)
             (pixL (π (Lset d)) (HS.C.πX-intro (Lset d) Ld∈M))
             (pixL (π d) (HS.C.πX-intro d d∈M))
             (pixL (π z) (HS.C.πX-intro z z∈M))
             pushed
```

THE TWO HYPOTHESES OF `HullStage.Condense`.

```agda
  levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ HS.C.πX ⟩ → ⟨ Lset δ ∈ˢ HS.C.πX ⟩
  levelIn δ oδ δ∈πX =
    PT.rec (snd (Lset δ ∈ˢ HS.C.πX)) go (HS.C.πX-member δ δ∈πX)
    where
    go : Σ[ d ∈ S ] (⟨ d ∈ˢ M ⟩ × (π d ≡ δ)) → ⟨ Lset δ ∈ˢ HS.C.πX ⟩
    go (d , d∈M , e) =
      subst (λ w → ⟨ w ∈ˢ HS.C.πX ⟩) (cm .snd ∙ cong Lset e)
            (HS.C.πX-intro (Lset d) (cm .fst))
      where
      od : IsOrd d
      od = ord-pull d d∈M (subst IsOrd (sym e) oδ)

      cm : ⟨ Lset d ∈ˢ M ⟩ × (π (Lset d) ≡ Lset (π d))
      cm = commute d od d∈M

  cover : (y : S) → ⟨ y ∈ˢ M ⟩
        → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ HS.C.πX ⟩ × ⟨ π y ∈ˢ Lset γ ⟩) ∥₁
  cover y y∈M = PT.rec squash₁ go (Lset-out lam y (Hull⊆L y y∈M))
    where
    Goal : Type (ℓ-suc ℓ)
    Goal = ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ HS.C.πX ⟩ × ⟨ π y ∈ˢ Lset γ ⟩) ∥₁

    go : Σ[ c ∈ S ] (⟨ c ∈ˢ lam ⟩ × ⟨ y ∈ˢ 𝒟ₒ (Lset c) ⟩) → Goal
    go (c , c∈λ , y∈D) = PT.rec squash₁ go₂ (sup p p∈λ)
      where
      p : S
      p = sucV c

      p∈λ : ⟨ p ∈ˢ lam ⟩
      p∈λ = succλ c c∈λ

      op : IsOrd p
      op = suc-ord (mem-ord {A = lam} ordλ c c∈λ)

      y∈Lp : ⟨ y ∈ˢ Lset p ⟩
      y∈Lp = subst (λ w → ⟨ y ∈ˢ w ⟩) (sym (Lset-suc c)) y∈D

      go₂ : Σ[ γ ∈ S ] (⟨ γ ∈ˢ lam ⟩ × ⟨ p ∈ˢ γ ⟩ × Adequate γ) → Goal
      go₂ (γ , γ∈λ , p∈γ , adγ) = PT.rec squash₁ takeZ hullSat
        where
        yM : A.SM
        yM = y , y∈M

        hullSat : ⟨ [] Mse.⊨ findP yM ⟩
        hullSat = subst ⟨_⟩ (sym (elem 0 (findP yM) []))
          (stageP y p γ op adγ p∈γ yM refl y∈Lp
            (ord∈Lλ p op p∈λ) (Lset∈Lλ p p∈λ) (Lset∈Lλ γ γ∈λ))

        finishP : (z a : A.SM)
                → Σ[ u ∈ A.SM ]
                    ( ⟨ (u ∷ a ∷ z ∷ []) Mse.⊨ embed levelFo ⟩
                    × ⟨ y ∈ˢ fst u ⟩ )
                → Σ[ β ∈ S ] (IsOrd β × ⟨ β ∈ˢ HS.C.πX ⟩
                              × ⟨ π y ∈ˢ Lset β ⟩)
        finishP z a (u , sat , y∈u) =
          π p′ , ord-push p′ (snd a) op′ , HS.C.πX-intro p′ (snd a) , πy∈
          where
          amb : ⟨ (fst u ∷ fst a ∷ fst z ∷ []) ⊨ₚ levelFo ⟩
          amb = subst ⟨_⟩ (Cy.atM Δ₀-levelFo (u ∷ a ∷ z ∷ [])) sat

          p′ : S
          p′ = fst a

          op′ : IsOrd p′
          op′ = isOrd-at-p-out (fst u) p′ (fst z) (amb .fst)

          u≡ : fst u ≡ Lset p′
          u≡ = level-sound (fst u) p′ (fst z)
                 (isLλ (fst u) (Hull⊆L (fst u) (snd u)))
                 (isLλ p′ (Hull⊆L p′ (snd a)))
                 (isLλ (fst z) (Hull⊆L (fst z) (snd z))) amb

          y∈Lp′ : ⟨ y ∈ˢ Lset p′ ⟩
          y∈Lp′ = subst (λ v → ⟨ y ∈ˢ v ⟩) u≡ y∈u

          cm : ⟨ Lset p′ ∈ˢ M ⟩ × (π (Lset p′) ≡ Lset (π p′))
          cm = commute p′ op′ (snd a)

          πy∈ : ⟨ π y ∈ˢ Lset (π p′) ⟩
          πy∈ = subst (λ w → ⟨ π y ∈ˢ w ⟩) (cm .snd)
                  (Cy.member-push (Lset p′) y (cm .fst) y∈M y∈Lp′)

        takeA : (z : A.SM)
              → Σ[ a ∈ A.SM ]
                  ⟨ (a ∷ z ∷ []) Mse.⊨ ∃̇ (embed levelFo ∧̇ (con yM ∈̇ var zero)) ⟩
              → Goal
        takeA z (a , ha) = PT.map (finishP z a) ha

        takeZ : Σ[ z ∈ A.SM ]
                  ⟨ (z ∷ []) Mse.⊨ ∃̇ (∃̇ (embed levelFo ∧̇ (con yM ∈̇ var zero))) ⟩
              → Goal
        takeZ (z , hz) = PT.rec squash₁ (takeA z) hz
```

THE THEOREM. The collapse of the hull is a level.

```agda
  module Cn = HS.Condense levelIn cover using (condenses)

  condenses : Σ[ β ∈ S ] (IsOrd β × (HS.C.πX ≡ Lset β))
  condenses = Cn.condenses
```

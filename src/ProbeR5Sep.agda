{-# OPTIONS --cubical --safe --guardedness #-}

-- [L3.31-IF-Rp] D-1 probe: Separation over isJ, plus the ordinal-content
-- family priced by statement.
--
-- ONE representative Separation-class target is re-proven over the J tower:
-- AtStageJ's `separateAtJ`, an arbitrary Δ₀-definable subclass carve at a J
-- level, with the introduction half riding L.Rud.SatSets.LimitFullSwitch
-- .full-switch-⊇ (unconditional, Δ₀-free).  Measures churn-vs-genuine-proof
-- lines and names engine gaps instead of filling them.  P-S3 prices the
-- `Sset γ ∩ Ord = γ` family BY STATEMENT: statements and consumers only,
-- nothing beyond a statement is built.
--
-- Line-count convention: non-blank lines inside the agda region (comments
-- included, blanks excluded), the pinned convention.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )

module ProbeR5Sep {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure; Transitive; ↾-reflects )
import FOL.ZFModel
open import FOL.Syntax using ( Formula; con; var; _∈̇_; _∧̇_ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∈; δ-∧ )
open import FOL.Manipulation.Bounding using ( BoundedFo; BoundedFo-mono; module Relabel )
open import FOL.Manipulation.Relabelling using ( mapFo; ⊨-map )
import FOL.Semantics
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Rank {ℓ} using ( rank )
open import L.Ordinal {ℓ} using ( bound2; ω-ord )
open import L.Ordinal.Stages {ℓ} lem using ( φ-ord )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit; isLimit-ord )
open import L.Rud.OrdBlocks {ℓ} lem using ( +ω; +ω-mem; +ω-sup; +ω-limit )
open import L.Rud.Step {ℓ} lem A using ( Sset; Sset-mono; Sset-trans; Jset )
open import L.Rud.ClassJ {ℓ} lem A using ( isJ; isJ-trans; Jset→isJ; 𝒮ⱼ )
open import L.Rud.SatSets {ℓ} lem A using ( module LimitFullSwitch )
open import L.Stage {ℓ} lem using ( leastOrd )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( sucV; ω )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈-asFiber; ∈ₛ⟪_⟫↪_ )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- ===================================================================
-- P-S0 CONTROL: full-switch-⊇ at the probe's telescope (SatSets:1630-1651),
-- and the 𝒮ⱼ uniqueness face (`extensionalJ` + `uniqueJ`), undelivered in the
-- tree; ProbeR5 (untracked) re-derived it, 10 lines, P7-identical.
-- ===================================================================

full-switch-⊇-control : (α : S) (limα : ⟨ isLimit α ⟩) (β : S) (limβ : ⟨ isLimit β ⟩)
                      → ⟨ β ∈ˢ α ⟩ → (φ : Formula ⟪ Jset β limβ ⟫ 1)
                      → ⟨ DefOf.defSet (Jset β limβ) φ ∈ˢ Jset α limα ⟩
full-switch-⊇-control = LimitFullSwitch.full-switch-⊇

module J = hPropStructure 𝒮ⱼ
module ModelJ = FOL.ZFModel 𝒮ⱼ
open ModelJ using ( SetOf; setOf-unique )
module AbsJ = FOL.Absoluteness.Single 𝒮ᵥ isJ isJ-trans
open AbsJ using ( abs₀ ) renaming ( _⊨ᵐ_ to _⊨_ ; _⊨ᵛ_ to _⊨ᵥ_ )

extensionalJ : {a b : J.S} → ((x : J.S) → (x J.∈ˢ a) ≡ (x J.∈ˢ b)) → a ≡ b
extensionalJ {a} {b} h =
  ↾-reflects {𝒮 = 𝒮ᵥ} {M = isJ} (extensionalV {a = fst a} {b = fst b} vwise)
  where
  vwise : (v : S) → (v ∈ˢ fst a) ≡ (v ∈ˢ fst b)
  vwise v = ⇔toPath fwd bwd
    where
    fwd : ⟨ v ∈ˢ fst a ⟩ → ⟨ v ∈ˢ fst b ⟩
    fwd v∈a = subst ⟨_⟩ (h (v , isJ-trans v∈a (a .snd))) v∈a
    bwd : ⟨ v ∈ˢ fst b ⟩ → ⟨ v ∈ˢ fst a ⟩
    bwd v∈b = subst ⟨_⟩ (sym (h (v , isJ-trans v∈b (b .snd)))) v∈b

uniqueJ : (Q : J.S → Ω) → SetOf Q → isContr (SetOf Q)
uniqueJ = setOf-unique extensionalJ

-- ===================================================================
-- P-S1 THE REPRESENTATIVE TARGET: AtStageJ, the fixed-level carve.  The L
-- side AtStage (Separation:108-299) re-points with four swaps (`Lset σ` →
-- `Jset β limβ`, `isL` → `isJ`, `layer-trans` → `Sset-trans β`, `𝒟ₒ→isL` → `full-switch-⊇` + `Jset→isJ`); satBridge is D-16 generic.
-- ===================================================================

module AtStageJ (β : S) (limβ : ⟨ isLimit β ⟩) where

  ordβ : IsOrd β
  ordβ = isLimit-ord β limβ

  module DefC = DefOf (Jset β limβ)

  Atrans : Transitive 𝒮ᵥ DefC.M
  Atrans = Sset-trans β

  module RefC = DefC.Refine Atrans
  open RefC.Abs using () renaming ( _⊨ᵛ_ to _⊨σ_ )

  module SemV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open SemV.At (V ℓ) id using () renaming ( _⊨_ to _⊨v_ )

  Below : J.S → Type (ℓ-suc ℓ)
  Below c = ⟨ fst c ∈ Jset β limβ ⟩

  module RL = Relabel {K = J.S} {K' = ⟪ Jset β limβ ⟫} {W = V ℓ}
                fst ⟪ Jset β limβ ⟫↪ Below
                (λ c p → ∈-asFiber {a = fst c} {b = Jset β limβ} p .fst)
                (λ c p → ∈-asFiber {a = fst c} {b = Jset β limβ} p .snd)

  -- The five-step path, re-pointed; one composite, rest is churn.
  satBridge : (φ : Formula J.S 1) (h : BoundedFo Below φ) (dφ : Δ₀ φ)
              (m : ⟪ Jset β limβ ⟫) (xL : ⟨ isJ (⟪ Jset β limβ ⟫↪ m) ⟩)
            → ((⟪ Jset β limβ ⟫↪ m ∷ []) ⊨σ (mapFo DefC.ι (RL.liftFo φ h)))
              ≡ (((⟪ Jset β limβ ⟫↪ m , xL) ∷ []) ⊨ φ)
  satBridge φ h dφ m xL =
      ⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ DefC.ι fst (RL.liftFo φ h)
        (⟪ Jset β limβ ⟫↪ m ∷ [])
    ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ ⟪ Jset β limβ ⟫↪ id
             (RL.liftFo φ h) (⟪ Jset β limβ ⟫↪ m ∷ []))
    ∙ cong (λ ψ → (⟪ Jset β limβ ⟫↪ m ∷ []) ⊨v ψ) (RL.liftFo-correct φ h)
    ∙ ⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id φ (⟪ Jset β limβ ⟫↪ m ∷ [])
    ∙ sym (abs₀ dφ ((⟪ Jset β limβ ⟫↪ m , xL) ∷ []))

  carveSat : (φ : Formula J.S 1) (h : BoundedFo Below φ) (dφ : Δ₀ φ)
             (m : ⟪ Jset β limβ ⟫) (xL : ⟨ isJ (⟪ Jset β limβ ⟫↪ m) ⟩)
           → (⟪ Jset β limβ ⟫↪ m ∈ DefC.defSet (RL.liftFo φ h))
             ≡ (((⟪ Jset β limβ ⟫↪ m , xL) ∷ []) ⊨ φ)
  carveSat φ h dφ m xL =
    RefC.abs-defSet (RL.liftFo φ h) (RL.Δ₀-liftFo h dφ) m
      ∙ satBridge φ h dφ m xL

  carveSatAnd : (mₐ : ⟪ Jset β limβ ⟫) (φ : Formula J.S 1)
                (h : BoundedFo Below φ) (dφ : Δ₀ φ) (m : ⟪ Jset β limβ ⟫)
                (xL : ⟨ isJ (⟪ Jset β limβ ⟫↪ m) ⟩)
              → (⟪ Jset β limβ ⟫↪ m
                   ∈ DefC.defSet ((var zero ∈̇ con mₐ) ∧̇ RL.liftFo φ h))
                ≡ ((⟪ Jset β limβ ⟫↪ m ∈ ⟪ Jset β limβ ⟫↪ mₐ)
                   ⊓ (((⟪ Jset β limβ ⟫↪ m , xL) ∷ []) ⊨ φ))
  carveSatAnd mₐ φ h dφ m xL =
      RefC.abs-defSet ((var zero ∈̇ con mₐ) ∧̇ RL.liftFo φ h)
        (δ-∧ δ-∈ (RL.Δ₀-liftFo h dφ)) m
    ∙ cong₂ _⊓_ refl (satBridge φ h dφ m xL)

  opaque
    carve : Formula ⟪ Jset β limβ ⟫ 1 → V ℓ
    carve ψ = DefC.defSet ψ

  opaque
    unfolding carve
    -- THE introduction half, one line: unconditional switch at +ω β.
    carve∈J : (ψ : Formula ⟪ Jset β limβ ⟫ 1)
            → ⟨ carve ψ ∈ˢ Jset (+ω β) (+ω-limit β ordβ) ⟩
    carve∈J ψ =
      LimitFullSwitch.full-switch-⊇ (+ω β) (+ω-limit β ordβ) β limβ
        (+ω-mem β) ψ

    carve⊆ : (ψ : Formula ⟪ Jset β limβ ⟫ 1) (y : V ℓ)
           → ⟨ y ∈ carve ψ ⟩ → ⟨ y ∈ Jset β limβ ⟩
    carve⊆ ψ y mem = DefC.defSet⊆A ψ y mem

    carveOut : (mₐ : ⟪ Jset β limβ ⟫) (φ : Formula J.S 1)
               (h : BoundedFo Below φ) (dφ : Δ₀ φ) (m : ⟪ Jset β limβ ⟫)
               (xL : ⟨ isJ (⟪ Jset β limβ ⟫↪ m) ⟩)
             → ⟨ ⟪ Jset β limβ ⟫↪ m
                  ∈ carve ((var zero ∈̇ con mₐ) ∧̇ RL.liftFo φ h) ⟩
             → ⟨ (⟪ Jset β limβ ⟫↪ m ∈ ⟪ Jset β limβ ⟫↪ mₐ)
                 ⊓ (((⟪ Jset β limβ ⟫↪ m , xL) ∷ []) ⊨ φ) ⟩
    carveOut mₐ φ h dφ m xL mem =
      subst ⟨_⟩ (carveSatAnd mₐ φ h dφ m xL) mem

    carveIn : (mₐ : ⟪ Jset β limβ ⟫) (φ : Formula J.S 1)
              (h : BoundedFo Below φ) (dφ : Δ₀ φ) (m : ⟪ Jset β limβ ⟫)
              (xL : ⟨ isJ (⟪ Jset β limβ ⟫↪ m) ⟩)
            → ⟨ (⟪ Jset β limβ ⟫↪ m ∈ ⟪ Jset β limβ ⟫↪ mₐ)
                ⊓ (((⟪ Jset β limβ ⟫↪ m , xL) ∷ []) ⊨ φ) ⟩
            → ⟨ ⟪ Jset β limβ ⟫↪ m
                 ∈ carve ((var zero ∈̇ con mₐ) ∧̇ RL.liftFo φ h) ⟩
    carveIn mₐ φ h dφ m xL br =
      subst ⟨_⟩ (sym (carveSatAnd mₐ φ h dφ m xL)) br

  private
    memberIsJ : (m : ⟪ Jset β limβ ⟫) → ⟨ isJ (⟪ Jset β limβ ⟫↪ m) ⟩
    memberIsJ m = Jset→isJ β limβ (⟪ Jset β limβ ⟫↪ m)
      (∈∈ₛ {a = ⟪ Jset β limβ ⟫↪ m} {b = Jset β limβ} .snd
        (∈ₛ⟪ Jset β limβ ⟫↪ m))

  -- Satisfaction transport (re-point of Separation:258-266; L's opaque
  -- seal dropped, noted in the report).
  ⊨-transport : (φ : Formula J.S 1) (dφ : Δ₀ φ) (u v : J.S) → fst u ≡ fst v
              → ⟨ (u ∷ []) ⊨ φ ⟩ → ⟨ (v ∷ []) ⊨ φ ⟩
  ⊨-transport φ dφ u v p hyp =
    subst ⟨_⟩ (sym (abs₀ dφ (v ∷ [])))
      (subst (λ w → ⟨ (w ∷ []) ⊨ᵥ φ ⟩) p
        (subst ⟨_⟩ (abs₀ dφ (u ∷ [])) hyp))

  -- `separateAtJ`: re-point of Separation:281-330 (`uniqueL` → `uniqueJ`,
  -- `𝒟ₒ→isL` → `Jset→isJ`, `memberIsL` → `memberIsJ`, `Sset-trans`).
  separateAtJ : (a : J.S) (fa∈β : ⟨ fst a ∈ Jset β limβ ⟩)
                (φ : Formula J.S 1) (h : BoundedFo Below φ) (dφ : Δ₀ φ)
              → isContr (SetOf (λ x → (x J.∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)))
  separateAtJ a fa∈β φ h dφ = uniqueJ Q (sepElt , spec)
    where
    Q : J.S → Ω
    Q x = (x J.∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)
    mₐ = ∈-asFiber {a = fst a} {b = Jset β limβ} fa∈β .fst
    qₐ : ⟪ Jset β limβ ⟫↪ mₐ ≡ fst a
    qₐ = ∈-asFiber {a = fst a} {b = Jset β limβ} fa∈β .snd
    ψ : Formula ⟪ Jset β limβ ⟫ 1
    ψ = (var zero ∈̇ con mₐ) ∧̇ RL.liftFo φ h
    sepElt : J.S
    sepElt = carve ψ
           , Jset→isJ (+ω β) (+ω-limit β ordβ) (carve ψ) (carve∈J ψ)
    spec : (z : J.S) → (z J.∈ˢ sepElt) ≡ Q z
    spec z = ⇔toPath fwd bwd
      where
      fwd : ⟨ z J.∈ˢ sepElt ⟩ → ⟨ Q z ⟩
      fwd z∈ = fz∈fa , zφ
        where
        fz∈Jβ = carve⊆ ψ (fst z) z∈
        m = ∈-asFiber {a = fst z} {b = Jset β limβ} fz∈Jβ .fst
        q : ⟪ Jset β limβ ⟫↪ m ≡ fst z
        q = ∈-asFiber {a = fst z} {b = Jset β limβ} fz∈Jβ .snd
        xL = memberIsJ m
        m∈ : ⟨ ⟪ Jset β limβ ⟫↪ m ∈ carve ψ ⟩
        m∈ = subst (λ w → ⟨ w ∈ carve ψ ⟩) (sym q) z∈
        dk = carveOut mₐ φ h dφ m xL m∈
        fz∈fa = subst (λ w → ⟨ fst z ∈ w ⟩) qₐ
          (subst (λ w → ⟨ w ∈ ⟪ Jset β limβ ⟫↪ mₐ ⟩) q (dk .fst))
        zφ = ⊨-transport φ dφ (⟪ Jset β limβ ⟫↪ m , xL) z q (dk .snd)

      bwd : ⟨ Q z ⟩ → ⟨ z J.∈ˢ sepElt ⟩
      bwd (fz∈fa , zφ) = subst (λ w → ⟨ w ∈ carve ψ ⟩) q m∈
        where
        fz∈Jβ = Sset-trans β {x = fst a} {y = fst z} fz∈fa fa∈β
        m = ∈-asFiber {a = fst z} {b = Jset β limβ} fz∈Jβ .fst
        q : ⟪ Jset β limβ ⟫↪ m ≡ fst z
        q = ∈-asFiber {a = fst z} {b = Jset β limβ} fz∈Jβ .snd
        xL = memberIsJ m
        p₁ : ⟨ ⟪ Jset β limβ ⟫↪ m ∈ ⟪ Jset β limβ ⟫↪ mₐ ⟩
        p₁ = subst (λ w → ⟨ w ∈ ⟪ Jset β limβ ⟫↪ mₐ ⟩) (sym q)
          (subst (λ w → ⟨ fst z ∈ w ⟩) (sym qₐ) fz∈fa)
        p₂ : ⟨ ((⟪ Jset β limβ ⟫↪ m , xL) ∷ []) ⊨ φ ⟩
        p₂ = ⊨-transport φ dφ z (⟪ Jset β limβ ⟫↪ m , xL) (sym q) zφ
        m∈ : ⟨ ⟪ Jset β limβ ⟫↪ m ∈ carve ψ ⟩
        m∈ = carveIn mₐ φ h dφ m xL (p₁ , p₂)

-- ===================================================================
-- P-S2 THE Δ₀ THEOREM FROM A NAMED RESIDUE.  The level recursion
-- Separation:mkBoundedFo (:160-214, 55 lines) is formula-generic churn
-- (`Sset-mono` for `Lset-mono`); named as a residue (P6's DefClosureJ
-- pattern).  The a-level bound reuses the DELIVERED classical `leastOrd`
-- (L.Stage:149-151), so the "stage for J" is NOT a gap.
-- ===================================================================

Below′ : S → J.S → Type (ℓ-suc ℓ)
Below′ σ c = ⟨ fst c ∈ Sset σ ⟩

MkBoundedJ : Type (ℓ-suc ℓ)
MkBoundedJ = (φ : Formula J.S 1)
           → Σ[ σ ∈ S ] (IsOrd σ × BoundedFo (Below′ σ) φ)

separateΔ₀J : MkBoundedJ → (a : J.S) (φ : Formula J.S 1) → Δ₀ φ
            → isContr (SetOf (λ x → (x J.∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)))
separateΔ₀J mkb a φ dφ = AtStageJ.separateAtJ σ limσ a fa∈σ φ h dφ
  where
  jst : ∥ Σ[ σ ∈ S ] (IsOrd σ × ⟨ fst a ∈ Sset σ ⟩) ∥₁
  jst = PT.map (λ { (α , lim , fa∈) →
          α , isLimit-ord α lim , fa∈ }) (a .snd)
  sa-pkg = leastOrd (λ σ → fst a ∈ˢ Sset σ) jst
  sa = sa-pkg .fst
  ord-sa = sa-pkg .snd .fst
  rφ = mkb φ
  bb = bound2 (rφ .fst) sa (rφ .snd .fst) ord-sa
  σ0 = bb .fst
  ordσ0 = bb .snd .fst
  σ = +ω σ0
  limσ = +ω-limit σ0 ordσ0
  h : BoundedFo (AtStageJ.Below σ limσ) φ
  h = BoundedFo-mono {P = Below′ (rφ .fst)} {Q = AtStageJ.Below σ limσ}
        (λ c p → Sset-mono {α = σ} {β = rφ .fst}
                  (+ω-sup σ0 (rφ .fst) (bb .snd .snd .fst)) (fst c) p)
        φ (rφ .snd .snd)
  fa∈σ : ⟨ fst a ∈ Jset σ limσ ⟩
  fa∈σ = Sset-mono {α = σ} {β = sa}
           (+ω-sup σ0 sa (bb .snd .snd .snd)) (fst a) (sa-pkg .snd .snd .fst)

-- ===================================================================
-- P-S3 THE Sset-Ord CONTENT FAMILY, PRICED BY STATEMENT (R-5 / Gap B).
-- Statements only.  Each name is the J twin of a delivered L-side
-- declaration or a consumer's exact need (census in the report).  F6 is
-- deferred: no cardinal apparatus exists to state it.
-- ===================================================================
module OrdContentStatements where

  -- F1a L-calque shape (census's Stages elimination-half assumption; L
  -- anchor ord∈Lset-suc, Stages:434-448).  Not the J-native target.
  ord∈Sset-suc : (α : S) → IsOrd α → Type (ℓ-suc ℓ)
  ord∈Sset-suc α ordα = ⟨ α ∈ˢ Sset (sucV α) ⟩

  -- F1 forward at a limit index (J-native shape): ordinals below a limit
  -- are members of the level.  L anchor: Lset-cumul (Stages:164).  Consumers:
  -- r2probe:160-167 (λ-naming), r5census:180 (Infinity + W7).
  ord∈Jset : (β : S) → (limβ : ⟨ isLimit β ⟩) → Type (ℓ-suc ℓ)
  ord∈Jset β limβ = (α : S) → IsOrd α → ⟨ α ∈ˢ β ⟩ → ⟨ α ∈ˢ Jset β limβ ⟩

  -- F2 backward (hard half, through rank): ordinals in the level are
  -- below the index.  L anchor: ord∈Lset→∈ (Stages:265-267) riding
  -- rank-Lset (Stages:190-197); the J mechanism rank-Sset (F2b) is NOT
  -- delivered: not a pure re-point.
  ord∈Sset→∈ : (β : S) → IsOrd β → Type (ℓ-suc ℓ)
  ord∈Sset→∈ β ordβ = (x : S) → IsOrd x → ⟨ x ∈ˢ Sset β ⟩ → ⟨ x ∈ˢ β ⟩

  -- F2b the rank mechanism of the backward half (absent from the tree).
  rank-Sset : (β : S) → IsOrd β → Type (ℓ-suc ℓ)
  rank-Sset β ordβ = (x : S) → ⟨ x ∈ˢ Sset β ⟩ → ⟨ rank x ∈ˢ β ⟩

  -- F3 content equality (r2probe's `Sset γ ∩ Ord ≡ γ`, :160-167): for
  -- ordinals, level membership ≡ index membership (2 lines from F1+F2).
  Sset-Ord-content : (β : S) → IsOrd β → Type (ℓ-suc (ℓ-suc ℓ))
  Sset-Ord-content β ordβ =
    (x : S) → IsOrd x → ⟨ x ∈ˢ Sset β ⟩ ≡ ⟨ x ∈ˢ β ⟩

  -- F4 the carve form (D-16 re-point of OrdAt, Stages:330-395): φ-ord
  -- carves the index out of the level.  F4 + the limit switch give
  -- `α ∈ Sset (+ω α)`; F1 raises it to any limit index.
  defSet-φ-ordJ : (β : S) → (limβ : ⟨ isLimit β ⟩) → Type (ℓ-suc ℓ)
  defSet-φ-ordJ β limβ =
    ((α : S) → ⟨ α ∈ˢ β ⟩ → ⟨ α ∈ˢ Jset β limβ ⟩)
    → DefOf.defSet (Jset β limβ) (φ-ord {K = ⟪ Jset β limβ ⟫}) ≡ β

  -- F5 the ω instance (Axioms.Infinity D-row, r5census:151,:180): F4 at
  -- β = ω + the limit switch; the class form follows by Jset→isJ (delivered).
  ω∈Jset : (α : S) → ⟨ isLimit α ⟩ → Type (ℓ-suc ℓ)
  ω∈Jset α limα = ⟨ ω ∈ˢ Jset α limα ⟩

  ω∈𝒮ⱼ : Type (ℓ-suc ℓ)
  ω∈𝒮ⱼ = ⟨ isJ ω ⟩

{-# OPTIONS --cubical --safe --guardedness #-}

------------------------------------------------------------------------
-- [L3.32-T161] D22 gate: price W3's elimination slice on today's face.
-- Untracked probe, never committed (D-1). Protocol: GHCRTS=-M8g, one
-- Agda process, stop-line 300 non-blank lines, no postulate, no hole,
-- no TERMINATING. Report: _build/l3.32-t161-report.md (written first).
-- Part A measures the wiring around the slice's core (the order formula
-- at the level and its two-way adequacy are the core, taken as module
-- hypotheses so the rest is measured). Part B states the expressible
-- instance at sucV empty and verifies the delivered chapter imports.
------------------------------------------------------------------------

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module ProbeT161 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _∧̇_; ¬̇_; ∃̇_; ∀̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( ∅-ord; suc-ord )
open import L.Definability {ℓ} using ( module DefOf )
open import L.InitialSegment {ℓ} using ( _⟷_ )
open import L.Rud.Step {ℓ} lem A using
  ( Sset; step; step-in-self; step-in-img; Sset-suc; Sset-zero; Sset-trans
  ; Jset; Op16; Fof; u-self-in )
open import L.Rud.Order {ℓ} lem A using
  ( Member; Sset-below; Jset-order )
open import L.WellOrder.Base {ℓ-suc ℓ} using
  ( SWO; IsLeast )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit; isLimit-ord )
open import L.Rud.OrdBlocks {ℓ} lem using ( +ω; +ω-limit; +ω-mem )
open import L.Rud.SatSets {ℓ} lem A using ( module LimitFullSwitch )
open import Cubical.HITs.CumulativeHierarchy.Properties using
  ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions using
  ( ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( sucV )
open import Cubical.Data.Sigma using ( Σ≡Prop )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

------------------------------------------------------------------------
-- PART A. The slice at a variable limit level gamma. The family sits
-- in Ju = Jset gamma limgamma, the bridge's landing level. The row's
-- core is the precedes atom sigma< over the level with its two-way
-- adequacy sigma<-ok; they are taken as hypotheses so the wiring is
-- measured. The wiring: the description (a formula naming "z lies in
-- some family member and nothing in it precedes z"), the landing in
-- the next limit level, and the two adequacy readings PickIn/PickOut.
------------------------------------------------------------------------
module Slice (γ : S) (limγ : ⟨ isLimit γ ⟩) where

  Ju : S
  Ju = Jset γ limγ

  order : SWO (Member γ)
  order = Jset-order γ limγ

  module U = DefOf Ju
  open U using ( SM; ι; _⊨ᵐ_; defSet; defSet-mem; defSet⊆A ) public

  substH : {P Q : hProp (ℓ-suc ℓ)} → P ≡ Q → ⟨ P ⟩ → ⟨ Q ⟩
  substH = subst (λ (R : hProp (ℓ-suc ℓ)) → ⟨ R ⟩)

  fstι : (m : ⟪ Ju ⟫) → fst (ι m) ≡ ⟪ Ju ⟫↪ m
  fstι m = refl

  module Core
    (σ< : Formula ⟪ Ju ⟫ 3)
    (σ<-ok : (w x z : SM) → ⟨ (w ∷ x ∷ z ∷ []) ⊨ᵐ σ< ⟩
           ⟷ Sset-below γ (isLimit-ord γ limγ) w z)
    (a : S) (a∈J : ⟨ a ∈ˢ Ju ⟩)
    where

    aIdx : ⟪ Ju ⟫
    aIdx = ∈-asFiber {a = a} {b = Ju} a∈J .fst

    aEq : ⟪ Ju ⟫↪ aIdx ≡ a
    aEq = ∈-asFiber {a = a} {b = Ju} a∈J .snd

    -- The description: exists x in a, z in x, and nothing in x
    -- precedes z. The precedes atom is consumed at arity 3 because the
    -- bounded quantifier adds a variable and the syntax has no
    -- weakening (FOL/Syntax.lagda.md:157).
    φbody : Formula ⟪ Ju ⟫ 2
    φbody = (var zero ∈̇ con aIdx)
        ∧̇ ( (var (suc zero) ∈̇ var zero)
          ∧̇ ∀̇∈ (var zero) (¬̇ σ<) )

    φ : Formula ⟪ Ju ⟫ 1
    φ = ∃̇ φbody

    c : S
    c = defSet φ

    module LFS = LimitFullSwitch (+ω γ) (+ω-limit γ (isLimit-ord γ limγ))
                   γ limγ (+ω-mem γ)

    c-in : ⟨ c ∈ˢ Jset (+ω γ) (+ω-limit γ (isLimit-ord γ limγ)) ⟩
    c-in = LFS.full-switch-⊇ φ

    Cell : S → Member γ → hProp (ℓ-suc ℓ)
    Cell x m = (⟨ m .fst ∈ˢ x ⟩ , snd (m .fst ∈ˢ x))

    LeastAt : S → ⟪ Ju ⟫ → Type (ℓ-suc ℓ)
    LeastAt x z = Σ[ h ∈ ⟨ ⟪ Ju ⟫↪ z ∈ˢ Ju ⟩ ]
      IsLeast order (Cell x) (⟪ Ju ⟫↪ z , h)

    OutAt : ⟪ Ju ⟫ → Type (ℓ-suc ℓ)
    OutAt z = ∥ Σ[ x ∈ S ] (⟨ x ∈ˢ a ⟩ × LeastAt x z) ∥₁

    -- The index and the carrier member are prop-equal: the first
    -- component is refl (fstι), the second is a proposition. This is
    -- the only member transport the readings need, and it is cheap.
    idxEq : (z : ⟪ Ju ⟫) (h : ⟨ ⟪ Ju ⟫↪ z ∈ˢ Ju ⟩) → ι z ≡ (⟪ Ju ⟫↪ z , h)
    idxEq z h = Σ≡Prop (λ x → snd (x ∈ˢ Sset γ)) (fstι z)

    PickIn : (x : S) → ⟨ x ∈ˢ a ⟩ → (z : ⟪ Ju ⟫) → LeastAt x z → ⟨ ⟪ Ju ⟫↪ z ∈ˢ c ⟩
    PickIn x x∈a z (hz , (z∈x , mini)) = substH (sym (defSet-mem φ z)) sat
      where
      x∈Ju : ⟨ x ∈ˢ Ju ⟩
      x∈Ju = Sset-trans γ {x = a} {y = x} x∈a a∈J
      x∈aSat : ⟨ ((x , x∈Ju) ∷ ι z ∷ []) ⊨ᵐ (var zero ∈̇ con aIdx) ⟩
      x∈aSat = subst (λ v → ⟨ x ∈ˢ v ⟩) (sym aEq) x∈a
      z∈xSat : ⟨ ((x , x∈Ju) ∷ ι z ∷ []) ⊨ᵐ (var (suc zero) ∈̇ var zero) ⟩
      z∈xSat = subst (λ u → ⟨ u ∈ˢ x ⟩) (sym (fstι z)) z∈x
      minSat : (wm : SM) → ⟨ fst wm ∈ˢ x ⟩
              → ⟨ (wm ∷ (x , x∈Ju) ∷ ι z ∷ []) ⊨ᵐ ¬̇ σ< ⟩
      minSat wm w∈x hσ = mini wm w∈x
        (subst (λ m → Sset-below γ (isLimit-ord γ limγ) wm m)
          (idxEq z hz) (σ<-ok wm (x , x∈Ju) (ι z) .fst hσ))
      sat : ⟨ (ι z ∷ []) ⊨ᵐ φ ⟩
      sat = ∣ (x , x∈Ju) , (x∈aSat , (z∈xSat , minSat)) ∣₁

    PickOut : (z : ⟪ Ju ⟫) → ⟨ ⟪ Ju ⟫↪ z ∈ˢ c ⟩ → OutAt z
    PickOut z z∈c = PT.rec squash₁ atX sat
      where
      sat : ⟨ (ι z ∷ []) ⊨ᵐ φ ⟩
      sat = substH (defSet-mem φ z) z∈c
      atX : Σ[ xm ∈ SM ] ⟨ (xm ∷ ι z ∷ []) ⊨ᵐ φbody ⟩ → OutAt z
      atX (xm , (x∈aSat , (z∈xSat , minSat))) =
        ∣ fst xm , (x∈a , (hz , (z∈x , mini))) ∣₁
        where
        x∈a : ⟨ fst xm ∈ˢ a ⟩
        x∈a = subst (λ v → ⟨ fst xm ∈ˢ v ⟩) aEq x∈aSat
        hz : ⟨ ⟪ Ju ⟫↪ z ∈ˢ Ju ⟩
        hz = defSet⊆A φ (⟪ Ju ⟫↪ z) z∈c
        z∈x : ⟨ ⟪ Ju ⟫↪ z ∈ˢ fst xm ⟩
        z∈x = subst (λ u → ⟨ u ∈ˢ fst xm ⟩) (fstι z) z∈xSat
        mini : (b : Member γ) → ⟨ b .fst ∈ˢ fst xm ⟩
             → Sset-below γ (isLimit-ord γ limγ) b (⟪ Ju ⟫↪ z , hz) → Empty.⊥
        mini b b∈x b<∙z = minSat b b∈x
          (σ<-ok b xm (ι z) .snd
            (subst (λ m → Sset-below γ (isLimit-ord γ limγ) b m)
              (sym (idxEq z hz)) b<∙z))

------------------------------------------------------------------------
-- PART B. The expressible instance: sucV empty, the unique level where
-- the successor clause is the whole order. The full slice here is the
-- value-enumeration formula with its two-way adequacy; the
-- self-below-image arm of the soundness is delivered (reuse measured as
-- a wall; report section 5); the image-image arm (and with it
-- completeness) is the residue whose forcing obligation is the
-- value-order content (report section 2).
------------------------------------------------------------------------
module Concrete where

  β : S
  β = ∅

  ordβ : IsOrd β
  ordβ = ∅-ord

  ordS : IsOrd (sucV β)
  ordS = suc-ord ordβ

  u : S
  u = Sset (sucV β)

  u-step : u ≡ step (Sset β)
  u-step = Sset-suc β

  ∅∈u : ⟨ ∅ ∈ˢ u ⟩
  ∅∈u = subst (λ w → ⟨ ∅ ∈ˢ w ⟩) (sym u-step)
    (subst (λ v → ⟨ v ∈ˢ step (Sset β) ⟩) (Sset-zero) (step-in-self (Sset β)))

  img : Op16 → S
  img i = Fof i (Sset β) (Sset β)

  img∈u : (i : Op16) → ⟨ img i ∈ˢ u ⟩
  img∈u i = subst (λ v → ⟨ img i ∈ˢ v ⟩) (sym u-step)
    (step-in-img (Sset β) (img i) i (Sset β) (Sset β)
      (u-self-in (Sset β)) (u-self-in (Sset β)) refl)

  fresh : (x : S) → ⟨ x ∈ˢ Sset β ⟩ → Empty.⊥
  fresh x h = ∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst
    (subst (λ w → ⟨ x ∈ˢ w ⟩) (Sset-zero) h))

  module U = DefOf u
  open U using ( SM; ι; _⊨ᵐ_ ) public

  toMem : ⟪ u ⟫ → Member (sucV β)
  toMem p = ⟪ u ⟫↪ p , ∈∈ₛ {a = ⟪ u ⟫↪ p} {b = u} .snd (∈ₛ⟪ u ⟫↪ p)

  -- The full slice at the expressible instance, stated as the
  -- obligation: the formula enumerating the level's order, with its
  -- two-way adequacy against the delivered Sset-below.
  module FullSlice
    (σ< : Formula ⟪ u ⟫ 2)
    (σ<-ok : (p q : ⟪ u ⟫) → ⟨ (ι p ∷ ι q ∷ []) ⊨ᵐ σ< ⟩
           ⟷ Sset-below (sucV β) ordS (toMem p) (toMem q)) where
    -- The description and the two readings at this level close exactly
    -- as Part A (the same shape, one level lower); nothing beyond
    -- Part A is measured here.

  -- The delivered self-below-image arm of the soundness lives at
  -- src/L/OrderFormula.lagda.md (module Adeq, sat-out); the import
  -- resolves and the module is usable. Restating its concrete-level
  -- satisfaction type in a consumer re-fires T19's concrete-satisfaction
  -- wall (measured: heap exhaustion at -M8g, ~7 min), so the probe
  -- states the instance's obligation at the statement layer instead.
  open import L.OrderFormula {ℓ} lem A using ( module Adeq )

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.536] CONTROL.  The adjunction at an ABSTRACT stage.
--
-- WHY THIS FILE EXISTS.  runs/full-1 exhausted 8 GB (runs/full-1.time).
-- The walling file carved the sequence at the stage `step 3 γ`, which
-- is `sucV (sucV (sucV γ))`, and `sucV` is TRANSPARENT: so the TYPES of
-- the two constants, of the formula and of every `where` block under
-- them named `⟪ Lset (sucV (sucV (sucV γ))) ⟫`.  That is law P-l
-- (dev/LESSONS.md:2357): a statement may be ABOUT a concrete stage, but
-- naming a transparent presentation in its TYPE re-normalizes the tower
-- at every check.
--
-- P-l ALSO SAYS A CURE DOES NOT TRANSFER BY ANALOGY, so this file
-- MEASURES the abstract form alone before anything consumes it.  `σ` is
-- a module parameter here, so `⟪ Lset σ ⟫` is an atom.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-536.runs.Control536 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _≐_; _∨̇_ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-layer; layer-trans
        ; Lset→isL; 𝒟ₒ; 𝒟ₒ-intro )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ∈-asFiber; extensionality; _⊆_; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ


-- ===================================================================
-- THE ADJUNCTION AT AN ARBITRARY STAGE.
--
-- If a set T is described, member by member, as "a member of h, or the
-- set q", and both h and q lie in a stage, then T lies in the NEXT
-- stage.  Two constants and no quantifier: the cheapest shape the door
-- of `𝒟ₒ-intro` (src/L/Constructible.lagda.md:301-304) admits.
--
-- Nothing here is about the hierarchy, the sequence, or any concrete
-- position.  σ, h, q and T are variables.
-- ===================================================================

module AdjoinAt (σ : V ℓ) (oσ : IsOrd σ)
                (h q : V ℓ) (h∈ : ⟨ h ∈ Lset σ ⟩) (q∈ : ⟨ q ∈ Lset σ ⟩)
                (T : S)
                (out : (x : S) → (⟨ fst x ∈ h ⟩ ⊎ (fst x ≡ q))
                     → ⟨ fst x ∈ fst T ⟩)
                (into : (x : S) → ⟨ fst x ∈ fst T ⟩
                      → ∥ ⟨ fst x ∈ h ⟩ ⊎ (fst x ≡ q) ∥₁)
                where
  private
    module DefA = DefOf (Lset σ)

    mₕ : ⟪ Lset σ ⟫
    mₕ = ∈-asFiber {a = h} {b = Lset σ} h∈ .fst

    qₕ : ⟪ Lset σ ⟫↪ mₕ ≡ h
    qₕ = ∈-asFiber {a = h} {b = Lset σ} h∈ .snd

    mQ : ⟪ Lset σ ⟫
    mQ = ∈-asFiber {a = q} {b = Lset σ} q∈ .fst

    qQ : ⟪ Lset σ ⟫↪ mQ ≡ q
    qQ = ∈-asFiber {a = q} {b = Lset σ} q∈ .snd

    φ : Formula ⟪ Lset σ ⟫ 1
    φ = (var zero ∈̇ con mₕ) ∨̇ (var zero ≐ con mQ)

    Atrans = layer-trans (Lset-layer σ)

    defSet≡ : DefA.defSet φ ≡ fst T
    defSet≡ = extensionality (DefA.defSet φ) (fst T) (sub₁ , sub₂)
      where
      fromSat : (m : ⟪ Lset σ ⟫) → ⟨ (DefA.ι m ∷ []) DefA.⊨ᵐ φ ⟩
              → ⟨ ⟪ Lset σ ⟫↪ m ∈ fst T ⟩
      fromSat m sat = PT.rec (snd (x ∈ fst T)) branch sat
        where
        x : V ℓ
        x = ⟪ Lset σ ⟫↪ m

        xS : S
        xS = x , Lset→isL σ oσ x
                   (∈∈ₛ {a = x} {b = Lset σ} .snd (∈ₛ⟪ Lset σ ⟫↪ m))

        branch : ⟨ x ∈ ⟪ Lset σ ⟫↪ mₕ ⟩ ⊎ (x ≡ ⟪ Lset σ ⟫↪ mQ)
               → ⟨ x ∈ fst T ⟩
        branch (inl x∈h) = out xS (inl (subst (λ w → ⟨ x ∈ w ⟩) qₕ x∈h))
        branch (inr p)   = out xS (inr (p ∙ qQ))

      sub₁ : ⟨ DefA.defSet φ ⊆ fst T ⟩
      sub₁ y y∈ₛ = ∈∈ₛ {a = y} {b = fst T} .fst
        (PT.rec (snd (y ∈ fst T))
          (λ { ((m , hm) , qm) →
            subst (λ w → ⟨ w ∈ fst T ⟩) qm
              (fromSat m
                (subst ⟨_⟩ (DefA.defSet-mem φ m) ∣ (m , hm) , refl ∣₁)) })
          (∈∈ₛ {a = y} {b = DefA.defSet φ} .snd y∈ₛ))

      sub₂ : ⟨ fst T ⊆ DefA.defSet φ ⟩
      sub₂ y y∈ₛ = ∈∈ₛ {a = y} {b = DefA.defSet φ} .fst
        (PT.rec (snd (y ∈ DefA.defSet φ)) fromDisj (into yS y∈))
        where
        y∈ : ⟨ y ∈ fst T ⟩
        y∈ = ∈∈ₛ {a = y} {b = fst T} .snd y∈ₛ

        yS : S
        yS = y , isL-trans {x = fst T} {y = y} y∈ (snd T)

        place : ⟨ y ∈ Lset σ ⟩ → (⟨ y ∈ h ⟩ ⊎ (y ≡ q))
              → ⟨ y ∈ DefA.defSet φ ⟩
        place y∈σ d =
          subst (λ w → ⟨ w ∈ DefA.defSet φ ⟩) q'
            (subst ⟨_⟩ (sym (DefA.defSet-mem φ m')) (sat d))
          where
          m' : ⟪ Lset σ ⟫
          m' = ∈-asFiber {a = y} {b = Lset σ} y∈σ .fst

          q' : ⟪ Lset σ ⟫↪ m' ≡ y
          q' = ∈-asFiber {a = y} {b = Lset σ} y∈σ .snd

          sat : (⟨ y ∈ h ⟩ ⊎ (y ≡ q)) → ⟨ (DefA.ι m' ∷ []) DefA.⊨ᵐ φ ⟩
          sat (inl y∈h) =
            ∣ inl (subst (λ w → ⟨ w ∈ ⟪ Lset σ ⟫↪ mₕ ⟩) (sym q')
                     (subst (λ w → ⟨ y ∈ w ⟩) (sym qₕ) y∈h)) ∣₁
          sat (inr y≡q) = ∣ inr (q' ∙ y≡q ∙ sym qQ) ∣₁

        fromDisj : ⟨ y ∈ h ⟩ ⊎ (y ≡ q) → ⟨ y ∈ DefA.defSet φ ⟩
        fromDisj (inl y∈h) = place (Atrans {x = h} {y = y} y∈h h∈) (inl y∈h)
        fromDisj (inr y≡q) =
          place (subst (λ w → ⟨ w ∈ Lset σ ⟩) (sym y≡q) q∈) (inr y≡q)

  adjoin∈ : ⟨ fst T ∈ Lset (sucV σ) ⟩
  adjoin∈ = subst (λ w → ⟨ fst T ∈ w ⟩) (sym (Lset-suc σ))
    (𝒟ₒ-intro (Lset σ) (fst T) ∣ φ , defSet≡ ∣₁)

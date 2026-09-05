{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.297] probe C.  THE OBLIGATION THE RETURN LEFT INFERRED.
--
-- [LJ-1.293] section 3 names a SECOND obligation beside `q'`: the six
-- readings are delivered at the INNER reading `|=m` while the ambient
-- site spends the AMBIENT reading `|=v`, and it calls the transport
-- "a one-time step no delivered lemma states for non-Delta-0 formulas",
-- INFERRED small and measured by nobody.
--
-- At the CLASS carrier that transport is FALSE in general: a non-Delta-0
-- formula is not absolute for L.  At the AMBIENT carrier the class is
-- EVERYTHING, the projection `fst : SM -> S` is an equivalence, and the
-- transport is TRUE FOR EVERY FORMULA.  This probe builds it.
--
--   absFull : (phi : Formula SM n) (d : SM ^ n)
--           -> (d |=m phi) == ((map fst d) |=v phi)
--
-- Twelve cases, one induction, no hypothesis.  The two unbounded
-- quantifier cases carry the whole content and they re-index along
-- `fst`; `Delta-0` never appears.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth

module LJ-1-297.ProbeLJ1297C {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure; Transitive; _↾_ )
open import FOL.Syntax using
  ( Formula; Term; con; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
  ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.Data.Unit using ( Unit*; tt*; isPropUnit* )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Vec using ( map; _∷_ )
import Cubical.HITs.PropositionalTruncation as PT

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- The AMBIENT class, [LJ-1.184] probe A section 4's `Full`.
Full : V ℓ → hProp (ℓ-suc ℓ)
Full _ = Unit* {ℓ-suc ℓ} , isPropUnit*

Full-tr : Transitive 𝒮ᵥ Full
Full-tr h k = tt*

module Abs = FOL.Absoluteness.Single 𝒮ᵥ Full (λ {x} {y} → Full-tr {x} {y})
open Abs using ( SM; _⊨ᵐ_; _⊨ᵛ_; ⟦_⟧ᵐ; ⟦_⟧ᵛ; _^_ )

-- =====================================================================
-- THE DICTIONARY.  `Single` keeps these two private
-- (src/FOL/Absoluteness.lagda.md:91-99), so they are re-derived here.
-- =====================================================================

lookup-fst : ∀ {n} (i : Fin n) (δ : SM ^ n)
           → lookup i (map fst δ) ≡ fst (lookup i δ)
lookup-fst zero    (m ∷ δ) = refl
lookup-fst (suc i) (m ∷ δ) = lookup-fst i δ

⟦⟧-fst : ∀ {n} (t : Term SM n) (δ : SM ^ n)
       → fst (⟦ t ⟧ᵐ δ) ≡ ⟦ t ⟧ᵛ (map fst δ)
⟦⟧-fst (con m) δ = refl
⟦⟧-fst (var i) δ = sym (lookup-fst i δ)

-- =====================================================================
-- THE TRANSPORT, FOR EVERY FORMULA.
-- =====================================================================

absFull : ∀ {n} (φ : Formula SM n) (δ : SM ^ n)
        → (δ ⊨ᵐ φ) ≡ ((map fst δ) ⊨ᵛ φ)
absFull (t ∈̇ u) δ = cong₂ _∈ˢ_ (⟦⟧-fst t δ) (⟦⟧-fst u δ)
absFull (t ≐ u) δ = cong₂ _≈ˢ_ (⟦⟧-fst t δ) (⟦⟧-fst u δ)
absFull (φ ∧̇ ψ) δ = cong₂ _⊓_ (absFull φ δ) (absFull ψ δ)
absFull (φ ∨̇ ψ) δ = cong₂ _⊔_ (absFull φ δ) (absFull ψ δ)
absFull (φ ⇒̇ ψ) δ = cong₂ _⇒_ (absFull φ δ) (absFull ψ δ)
absFull (¬̇ φ)   δ = cong ¬_ (absFull φ δ)
absFull ⊤̇       δ = refl
absFull ⊥̇       δ = refl

-- THE CONTENT.  The inner quantifier ranges over `SM` and the ambient
-- one over `S`; at the FULL class `fst` is an equivalence, and the two
-- directions below are its two halves.  Nothing here is `Delta-0`.
absFull (∃̇ φ) δ = ⇔toPath
  (PT.map (λ { (x , h) → fst x , subst ⟨_⟩ (absFull φ (x ∷ δ)) h }))
  (PT.map (λ { (y , h) →
    (y , tt*) , subst ⟨_⟩ (sym (absFull φ ((y , tt*) ∷ δ))) h }))
absFull (∀̇ φ) δ = ⇔toPath
  (λ h y → subst ⟨_⟩ (absFull φ ((y , tt*) ∷ δ)) (h (y , tt*)))
  (λ h x → subst ⟨_⟩ (sym (absFull φ (x ∷ δ))) (h (fst x)))

-- The bounded cases carry one extra step, the bound's own value.
absFull (∀̇∈ t φ) δ = ⇔toPath
  (λ h y hy → subst ⟨_⟩ (absFull φ ((y , tt*) ∷ δ))
    (h (y , tt*) (subst (λ u → ⟨ y ∈ˢ u ⟩) (sym (⟦⟧-fst t δ)) hy)))
  (λ h x hx → subst ⟨_⟩ (sym (absFull φ (x ∷ δ)))
    (h (fst x) (subst (λ u → ⟨ fst x ∈ˢ u ⟩) (⟦⟧-fst t δ) hx)))
absFull (∃̇∈ t φ) δ = ⇔toPath
  (PT.map (λ { (x , (hx , h)) →
    fst x , ( subst (λ u → ⟨ fst x ∈ˢ u ⟩) (⟦⟧-fst t δ) hx
            , subst ⟨_⟩ (absFull φ (x ∷ δ)) h ) }))
  (PT.map (λ { (y , (hy , h)) →
    (y , tt*) , ( subst (λ u → ⟨ y ∈ˢ u ⟩) (sym (⟦⟧-fst t δ)) hy
                , subst ⟨_⟩ (sym (absFull φ ((y , tt*) ∷ δ))) h ) }))

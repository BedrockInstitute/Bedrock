{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.471]  Carve Internal's order as a set by ONE separation, at
-- [LJ-1.468]'s delivered orderFo.  Rebuilds the formula.  Does not
-- import a probe.  bnd is a PARAMETER.  Do not inhabit it.
--
-- W3 FIRST  `sep-applied`.  Apply hasSeparationL at bnd and orderFo.
--            Readings and the obligation omitted.
-- TERM       `order-as-set`.  The unique SetOf of that carve.
--
-- orderFo rebuilt from agents/tasks/LJ-1-468/Probe468.agda:78-87.
-- Shape: RelCond (src/L/Choice/Before.lagda.md:220-226).
-- Carve: hasSeparationL (src/L/Axioms/Full.lagda.md:144-145),
--        once, as InclGraph spends it (src/L/InjChain.lagda.md:479-483).
--
-- ONE Agda process per run, GHCRTS as the program set it on this pane.
-- Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-471.Probe471 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _≐_; _∧̇_; ∃̇_; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( prAtL )
open import L.Choice.Internal {ℓ} lem using ( StepAt )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import Cubical.Data.FinData using ( Fin; zero; suc )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- After five pin binders and two member binders the environment is
--   0 = y, 1 = x, 2 = C₀, 3 = C, 4 = B, 5 = P, 6 = R, 7 = z
-- Closed indices, Internal's s6a shape
-- (src/L/Choice/Internal.lagda.md:902-908).
private
  iY iX iC0 iCs iCar iPar iCod iZ
    : ∀ {n} → Fin (suc (suc (suc (suc (suc (suc (suc (suc n))))))))
  iY   = zero
  iX   = suc zero
  iC0  = suc (suc zero)
  iCs  = suc (suc (suc zero))
  iCar = suc (suc (suc (suc zero)))
  iPar = suc (suc (suc (suc (suc zero))))
  iCod = suc (suc (suc (suc (suc (suc zero)))))
  iZ   = suc (suc (suc (suc (suc (suc (suc zero))))))

-- Rebuilt at [LJ-1.468]'s delivered type.  Five constants in Term
-- position.  One free variable.  StepAt at slots as delivered
-- (src/L/Choice/Internal.lagda.md:973-975).
orderFo : (R P B C C₀ : S) → Formula S 1
orderFo R P B C C₀ =
  ∃̇ ( (var zero ≐ con R)
    ∧̇ ∃̇ ( (var zero ≐ con P)
      ∧̇ ∃̇ ( (var zero ≐ con B)
        ∧̇ ∃̇ ( (var zero ≐ con C)
          ∧̇ ∃̇ ( (var zero ≐ con C₀)
            ∧̇ ∃̇∈ (con B) ( ∃̇∈ (con B)
              ( prAtL iZ iX iY
              ∧̇ StepAt iCod iPar iCar iCs iC0 iX iY ) ) ) ) ) ) )

-- =====================================================================
-- W3.  Apply hasSeparationL at the named bound and this formula.
-- Readings and the obligation omitted.
-- =====================================================================

sep-applied : (R P B C C₀ bnd : S) → Σ[ Q ∈ S ] _
sep-applied R P B C C₀ bnd = hasSeparationL bnd (orderFo R P B C C₀) .fst

-- =====================================================================
-- Obligation.  One separation at the named bound.  Both directions of
-- the spec are the unique SetOf field.  Readings unpack that field.
-- bnd stays a parameter.  Rank is not built.  w is not read.
-- =====================================================================

-- The brief wrote ⟨ z ∈ˢ Q ⟩ ≡ ((z ∈ˢ bnd) ⊓ ...).  That does not
-- form: left is Type, right is Ω (runs/brief-type.out, UnequalTerms).
-- hasSeparationL returns SetOf, which is (z ∈ˢ Q) ≡ ((z ∈ˢ bnd) ⊓ ...)
-- at Ω (src/FOL/ZFModel.lagda.md:74-81, src/L/Axioms/Full.lagda.md:144-145).
-- G-spec is the same shape (src/L/InjChain.lagda.md:482-483).
order-as-set :
    (R P B C C₀ bnd : S)
  → Σ[ Q ∈ S ] ((z : S) → (z ∈ˢ Q)
      ≡ ((z ∈ˢ bnd) ⊓ ((z ∷ []) ⊨ orderFo R P B C C₀)))
order-as-set R P B C C₀ bnd = hasSeparationL bnd (orderFo R P B C C₀) .fst

order-as-set-out :
    (R P B C C₀ bnd z : S)
  → ⟨ z ∈ˢ fst (order-as-set R P B C C₀ bnd) ⟩
  → ⟨ z ∈ˢ bnd ⟩ × ⟨ (z ∷ []) ⊨ orderFo R P B C C₀ ⟩
order-as-set-out R P B C C₀ bnd z h =
  subst ⟨_⟩ (snd (order-as-set R P B C C₀ bnd) z) h

order-as-set-in :
    (R P B C C₀ bnd z : S)
  → ⟨ z ∈ˢ bnd ⟩
  → ⟨ (z ∷ []) ⊨ orderFo R P B C C₀ ⟩
  → ⟨ z ∈ˢ fst (order-as-set R P B C C₀ bnd) ⟩
order-as-set-in R P B C C₀ bnd z m sat =
  subst ⟨_⟩ (sym (snd (order-as-set R P B C C₀ bnd) z)) (m , sat)

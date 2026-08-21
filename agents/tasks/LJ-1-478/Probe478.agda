{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.478]  Carve the rank as a set by ONE separation, at
-- [LJ-1.475]'s delivered rank-formula with a pinned as con a.
-- Rebuilds the formula.  Does not import a probe.  bnd is a
-- PARAMETER.  Do not inhabit it.
--
-- W3 FIRST  `rankFo`.  Pin a as con a.  Obligation omitted.
-- TERM       `rank-graph`.  The unique SetOf of that carve.
--
-- rank-formula rebuilt from agents/tasks/LJ-1-475/Probe475.agda:95-103.
-- Pin of a: Term position, same RelCond / con move
--     src/L/Choice/Before.lagda.md:220-226, :1302-1303.
-- Carve: hasSeparationL (src/L/Axioms/Full.lagda.md:144-145),
--        once, as order-as-set spends it
--        (agents/tasks/LJ-1-471/Probe471.agda:90-94).
--
-- ONE Agda process per run, GHCRTS as the program set it on this pane.
-- Nothing lands in src/.  Do not postulate.  Do not claim a code.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-478.Probe478 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _≐_; _∈̇_; _∧̇_; _⇒̇_; ∀̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ}
  using ( prAtL; appAt; svAt; inDomAt; extAt; sucAtL )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import Cubical.Data.FinData using ( Fin; zero; suc )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

private
  s2 : ∀ {n} → Fin n → Fin (suc (suc n))
  s2 i = suc (suc i)
  s3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  s3 i = suc (suc (suc i))
  s4 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc n))))
  s4 i = suc (suc (suc (suc i)))
  s5 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc n)))))
  s5 i = suc (suc (suc (suc (suc i))))

-- Rebuilt at [LJ-1.475]'s delivered constructors.  Generic in slots.
-- Env of the body of ∀̇ is (x ∷ original).
fnAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
fnAt f Q m =
  svAt f
  ∧̇ ∀̇ ( (inDomAt (suc f) zero ⇒̇ appAt (suc Q) zero (suc m))
      ∧̇ (appAt (suc Q) zero (suc m) ⇒̇ inDomAt (suc f) zero) )

assignAt : ∀ {n} → Fin n → Fin n → Formula S n
assignAt f Q =
  ∀̇ ( inDomAt (suc f) zero
    ⇒̇ ∃̇ ( appAt (s2 f) (suc zero) zero
        ∧̇ extAt zero (
            ∃̇ ( appAt (s4 Q) zero (s3 zero)
              ∧̇ ∃̇ ( appAt (s5 f) (suc zero) zero
                  ∧̇ ∃̇ ( sucAtL (suc zero) zero
                      ∧̇ (var (s3 zero) ∈̇ var zero) ) ) ) ) ) )

supAt : ∀ {n} → Fin n → Fin n → Formula S n
supAt f r =
  extAt r (
    ∃̇ ( ∃̇ ( appAt (s3 f) (suc zero) zero
          ∧̇ ∃̇ ( sucAtL (suc zero) zero
              ∧̇ (var (s3 zero) ∈̇ var zero) ) ) ) )

-- =====================================================================
-- W3.  Pin a as con a.  Obligation omitted.
-- After the pin of Q and the three binders the env is
--   0 = f, 1 = r, 2 = m, 3 = Q', 4 = z
-- Membership reads con a in Term position.  No extra binder.
-- =====================================================================

rankFo : (Q a : S) → Formula S 1
rankFo Q a =
  ∃̇ ( (var zero ≐ con Q)
    ∧̇ ∃̇ ( ∃̇ (
        prAtL (s3 zero) (suc zero) zero
        ∧̇ (var (suc zero) ∈̇ con a)
        ∧̇ ∃̇ ( fnAt zero (s3 zero) (s2 zero)
            ∧̇ assignAt zero (s3 zero)
            ∧̇ supAt zero (suc zero) ) ) ) )

-- =====================================================================
-- Obligation.  One separation at the named bound.  Both directions of
-- the spec are the unique SetOf field.  Readings unpack that field.
-- bnd stays a parameter.  InjCode is not claimed.  Rank is not a code.
-- =====================================================================

-- The brief wrote the SetOf shape.  hasSeparationL returns SetOf, which
-- is (z ∈ˢ G) ≡ ((z ∈ˢ bnd) ⊓ ...) at Ω
-- (src/FOL/ZFModel.lagda.md:74-81, src/L/Axioms/Full.lagda.md:144-145).
-- G-spec is the same shape (src/L/InjChain.lagda.md:482-483).
rank-graph :
    (Q a bnd : S)
  → Σ[ G ∈ S ] ((z : S) → (z ∈ˢ G)
      ≡ ((z ∈ˢ bnd) ⊓ ((z ∷ []) ⊨ rankFo Q a)))
rank-graph Q a bnd = hasSeparationL bnd (rankFo Q a) .fst

rank-graph-out :
    (Q a bnd z : S)
  → ⟨ z ∈ˢ fst (rank-graph Q a bnd) ⟩
  → ⟨ z ∈ˢ bnd ⟩ × ⟨ (z ∷ []) ⊨ rankFo Q a ⟩
rank-graph-out Q a bnd z h =
  subst ⟨_⟩ (snd (rank-graph Q a bnd) z) h

rank-graph-in :
    (Q a bnd z : S)
  → ⟨ z ∈ˢ bnd ⟩
  → ⟨ (z ∷ []) ⊨ rankFo Q a ⟩
  → ⟨ z ∈ˢ fst (rank-graph Q a bnd) ⟩
rank-graph-in Q a bnd z m sat =
  subst ⟨_⟩ (sym (snd (rank-graph Q a bnd) z)) (m , sat)

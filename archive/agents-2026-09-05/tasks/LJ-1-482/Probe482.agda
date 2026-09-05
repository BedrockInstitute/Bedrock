{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.482]  W3 FIRST, then the obligation type, unbuilt.
-- Four InjCode conjuncts over [LJ-1.478]'s carved rank graph.
-- Rebuilds the carve.  Does not import a probe.  bnd is a PARAMETER.
--
-- W3 FIRST  `from-out`.  From rank-graph-out at the coded pair.
--             Obligation omitted.  Typechecked ALONE.
--             Supplies PAIR ∈ bnd, not y ∈ b.
--
-- TYPE       `RankCoded`.  The obligation, as a type.  No term
--             named rank-coded.  D-10: no conjunct has a 478
--             supplier.
--
-- ONE Agda process per run, GHCRTS the wide caliber the program set
-- on the pane, untouched here.  Nothing lands in src/.
-- Do not postulate.  Do not add a hypothesis to close a conjunct.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-482.Probe482 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _≐_; _∈̇_; _∧̇_; _⇒̇_; ∀̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ}
  using ( prAtL; appAt; svAt; inDomAt; extAt; sucAtL; prʟ; prʟ-fst )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

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

-- Rebuilt at [LJ-1.478]'s delivered constructors.  Generic in slots.
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

rankFo : (Q a : S) → Formula S 1
rankFo Q a =
  ∃̇ ( (var zero ≐ con Q)
    ∧̇ ∃̇ ( ∃̇ (
        prAtL (s3 zero) (suc zero) zero
        ∧̇ (var (suc zero) ∈̇ con a)
        ∧̇ ∃̇ ( fnAt zero (s3 zero) (s2 zero)
            ∧̇ assignAt zero (s3 zero)
            ∧̇ supAt zero (suc zero) ) ) ) )

-- Delivered type, Probe478.agda:105-109.  bnd stays a parameter.
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

-- =====================================================================
-- W3.  The range clause from rank-graph-out, via the coded pair.
-- Obligation omitted.  InjCode omitted.
--
-- from-out is the reading.  It yields the PAIR in bnd, and sat.
-- RangeClause is the fourth conjunct.  Unbuilt.
-- A false close that returns the pair-in-bnd as y ∈ b is in
-- runs/w3-false-close.out.  It is UnequalTerms.  Removed.
-- =====================================================================

module W3 (Q a bnd : S) where

  G : S
  G = fst (rank-graph Q a bnd)

  from-out :
      (x y : S)
    → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
    → ⟨ prʟ x y ∈ˢ bnd ⟩ × ⟨ (prʟ x y ∷ []) ⊨ rankFo Q a ⟩
  from-out x y h = rank-graph-out Q a bnd (prʟ x y) h'
    where
    h' : ⟨ prʟ x y ∈ˢ G ⟩
    h' = subst (λ w → ⟨ w ∈ fst G ⟩) (sym (prʟ-fst x y)) h

  -- The fourth conjunct, as the brief named it.  No term.
  -- from-out supplies prʟ x y ∈ˢ bnd, not fst y ∈ fst b.
  RangeClause : (b : S) → Type (ℓ-suc ℓ)
  RangeClause b =
      (x y : S)
    → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
    → ⟨ fst y ∈ fst b ⟩

-- =====================================================================
-- THE OBLIGATION, as a type.  No term named rank-coded.
-- Delivered 478 telescope (Q a bnd : S), plus b the fourth conjunct
-- names.  Readings rebuilt above, not taken as hypotheses.
-- Do not add a hypothesis.  Do not postulate.
-- =====================================================================

RankCoded : Type (ℓ-suc ℓ)
RankCoded =
    (Q a bnd b : S)
  → InjCode (fst (rank-graph Q a bnd)) a b

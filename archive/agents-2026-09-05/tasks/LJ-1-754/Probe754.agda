{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.754] PROBE.  The BoundedFo certificate of tagAtL at a closed ω-stage:
--
--   tagAtL-bounded-at-γ :
--       (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
--       → ⟨ ω ∈ˢ γ ⟩
--       → {n : ℕ}
--       → (s : Fin n)
--       → (k : ℕ)
--       → (x : Fin n)
--       → BoundedFo (λ (c : S) → ⟨ fst c ∈ˢ Lset γ ⟩) (tagAtL s k x)
--
-- tagAtL (src/L/Coding/Model.lagda.md:585-586) carries exactly ONE constant,
-- `numeralL k`, inside an unbounded ∃̇; its other factor is the pair reader
-- prAtL (src/L/Coding/Model.lagda.md:122-123), whose tree is all variables
-- (sglAt, pairAt, prAt at src/FOL/Bernstein.lagda.md:79-88), so BoundedTm
-- gives that factor nothing but Lift Units.  The certificate therefore
-- assembles from [LJ-1.747]'s leaf numeralL-in-carrier-lim
-- (agents/tasks/LJ-1-747/Probe747.agda:111, IMPORTED, not transcribed) plus
-- the trivial variable certificates of prAtL.
--
-- Lands nothing in src/.  `table-sat` is NOT inhabited (premise 4) and
-- `mkBoundedFo` (src/L/Axioms/Separation.lagda.md:449) is NOT inhabited:
-- the Separation route is exactly what this probe does not take.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by the
-- program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-754.Probe754 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Manipulation.Bounding using ( BoundedFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒮ʟ )
open import L.Ordinal.StageArith {ℓ} lem using ( closedω )
open import L.Coding.Model {ℓ} using ( tagAtL; prAtL )
open import LJ-1-747.Probe747 {ℓ = ℓ} lem using ( numeralL-in-carrier-lim )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ hiding ( S )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.Data.Unit using ( tt )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω )

-- The carrier of 𝒮ʟ, the world tagAtL speaks in.  L.Coding.Model opens this
-- non-publicly (src/L/Coding/Model.lagda.md:70), so the probe opens it
-- directly: the name binds the same projection application there and here.
open hPropStructure 𝒮ʟ using ( S )

------------------------------------------------------------------------------
-- The empty certificate of prAtL.  prAtL q u v = liftFo (prAt q u v) _
-- (src/L/Coding/Model.lagda.md:122-123), and prAt's tree is all variables
-- (sglAt, pairAt, prAt at src/FOL/Bernstein.lagda.md:79-88), so liftFo
-- touches only var, and BoundedTm P (var i) = Lift Unit for EVERY P.  The
-- certificate therefore normalizes to a closed nest of Lift Units -- one
-- that mentions neither P nor q u v -- and the hole below solves by
-- construction at ANY predicate, as the in-tree precedent of the `_` inside
-- prAtL itself already witnesses.  This is the W3 leg: no constant enters
-- through the pair reader, for any predicate whatsoever.

prAtL-triv : ∀ {ℓp : Level} (P : S → Type ℓp) {n} (q u v : Fin n)
           → BoundedFo P (prAtL q u v)
prAtL-triv P q u v = _

------------------------------------------------------------------------------
-- THE OBLIGATION.  Exported at the file's top level at the meter's name.
-- tagAtL s k x unfolds to ∃̇ ((var zero ≐ con (numeralL k)) ∧̇ prAtL (suc s)
-- zero (suc x)), so BoundedFo computes to
--   (Lift Unit × P (numeralL k)) × BoundedFo P (prAtL (suc s) zero (suc x))
-- at P := λ c → ⟨ fst c ∈ˢ Lset γ ⟩.  The left factor is the 747 leaf at k;
-- the right factor is prAtL-triv above.

tagAtL-bounded-at-γ :
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    → ⟨ ω ∈ˢ γ ⟩
    → {n : ℕ}
    → (s : Fin n)
    → (k : ℕ)
    → (x : Fin n)
    → BoundedFo (λ (c : S) → ⟨ fst c ∈ˢ Lset γ ⟩) (tagAtL s k x)
tagAtL-bounded-at-γ γ oγ clγ ω∈γ s k x =
  ( lift tt , numeralL-in-carrier-lim γ oγ clγ ω∈γ k )
    , prAtL-triv (λ (c : S) → ⟨ fst c ∈ˢ Lset γ ⟩) (suc s) zero (suc x)

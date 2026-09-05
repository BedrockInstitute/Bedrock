{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.736] PROBE.  Sat-in-carrier-lim, the Sat value bound at the
-- closedomega scope.  Lands nothing in src/.
--
--   OBLIGATION  Sat-in-carrier-lim (the type in Section 2).  STATED,
--               NOT INHABITED.  The D-10 truth check (brief premise 4)
--               prices the target FALSE:  the obligation quantifies
--               over Formula S n, whose constants range over ALL L-sets
--               (FOL.Absoluteness.Single's SM), and the atom clause of
--               `cond` transports a constant's global membership into
--               Sat's extension.  Section 1 machine-checks that
--               transport, so the review does not rest on a reading of
--               tmIs.  review-of-Sat-in-carrier-lim.md carries the
--               statement and the corrected-scope candidates.
--   DELIVERED   the semantic kernel (Section 1):  for the atom
--               (var 0 INdot con c), satisfaction of Sat's own `cond`
--               at an environment x is EXACTLY the fact
--               that the #0-tagged entry of x lies in c, for EVERY
--               carrier A, environment x and constant c : S, with no
--               stage hypothesis anywhere.  sat-atom-out lifts it to
--               Sat's own membership spec.
--   ABSENT      the INHABITANT of Sat-in-carrier-lim.  No postulate
--               stands in for it and no weaker form is inhabited under
--               its name.  Sat-in-carrier-stage and
--               envSet-in-carrier-stage are not inhabited either.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-736.Probe736 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_ )
import FOL.Absoluteness
open import Cubical.Data.FinData using ( zero; suc )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_; ω )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset )
open import L.Ordinal.StageArith {ℓ} lem using ( closedω )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Coding.Sat {ℓ} lem
  using ( Sat; cond; Sat-mem; tmIs; tmIs-var-in; tmIs-var-out
        ; cond∈-in; cond∈-out )
open import L.Coding.EnvSet {ℓ} lem using ( envSet )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

-- The satisfaction symbol.  THE SAME instance Sat itself opens
-- (src/L/Coding/Sat.lagda.md:57-58):  Single at 𝒮ᵥ with isL, so
-- `_⊨_` below is literally the satisfaction of Sat-mem's clause.
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using () renaming ( _⊨ᵐ_ to _⊨_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

-- The brief's hypothesis glyph `omega in^s gamma` reads at the V
-- structure (gamma : V), so it is renamed here;  the conclusion's
-- glyph `Sat A phi in^s LsetS gamma ogamma` is the L structure's and
-- stays unrenamed below.  (The 725-SPLIT disambiguation, as in
-- Probe729 and Probe730.)
open hPropStructure 𝒮ᵥ using () renaming ( _∈ˢ_ to _∈ˢᵥ_ )
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

-- =====================================================================
-- SECTION 1.  THE SEMANTIC KERNEL, MACHINE-CHECKED.
--
-- `cond`'s atom clause (src/L/Coding/Sat.lagda.md, `cond (t INdot u)`)
-- escorts the two term slots through two existential witnesses and then
-- states `var 1 INdot var 0`:  the t-slot entry lies in the u-slot
-- entry.  For the atom (var 0 INdot con c) the u-slot is pinned to the
-- constant by tmIs (con c) v e = var v =dot con c, so satisfaction at
-- an environment x says exactly:  the #0-tagged entry of x lies in c.
-- The two directions below are that reading, composed from the
-- chapter's OWN readers (cond∈-in / cond∈-out, then the landed
-- tmIs-var-in / tmIs-var-out).  No stage hypothesis appears:  c is any
-- S, at any rank.
-- =====================================================================

module Kernel (A x c : S) where

  φ₀ : Formula S 1
  φ₀ = var zero ∈̇ con c

  GoalΣ : Type _
  GoalΣ = (Σ[ w ∈ S ] (⟨ pr (# 0) (fst w) ∈ fst x ⟩ × ⟨ fst w ∈ fst c ⟩))

  Goal : Type _
  Goal = ∥ GoalΣ ∥₁

  atom-in : (w : S) → ⟨ pr (# 0) (fst w) ∈ fst x ⟩ → ⟨ fst w ∈ fst c ⟩
          → ⟨ (x ∷ []) ⊨ cond A φ₀ ⟩
  atom-in w pr∈ w∈c =
    cond∈-in A {n = 1} (var zero) (con c) x
      ∣ w , (c , ( tmIs-var-in (zero {n = 0}) (c ∷ w ∷ x ∷ []) (suc zero) (suc (suc zero)) pr∈
                 , ( refl
                   , w∈c ) )) ∣₁

  -- The two decoders, each with its RESULT TYPE stated, so no goal
  -- direction ever has to solve the environment vector backwards.

  step-in : (v w : S)
          → ⟨ (w ∷ v ∷ x ∷ []) ⊨ tmIs {n = 1} (var zero) (suc zero) (suc (suc zero)) ⟩
          → ⟨ pr (# 0) (fst v) ∈ fst x ⟩
  step-in v w p₁ = tmIs-var-out {n = 1} {m = 3} zero (w ∷ v ∷ x ∷ []) (suc zero) (suc (suc zero)) p₁

  step-eq : (v w : S)
          → ⟨ (w ∷ v ∷ x ∷ []) ⊨ tmIs {n = 1} (con c) zero (suc (suc zero)) ⟩
          → fst w ≡ fst c
  step-eq v w p₂ = p₂

  atom-out : ⟨ (x ∷ []) ⊨ cond A φ₀ ⟩ → Goal
  atom-out sat = PT.rec (squash₁ {A = GoalΣ})
    (λ { (v , (w , (p₁ , (p₂ , r)))) →
      ∣ v , ( tmIs-var-out (zero {n = 0}) (w ∷ v ∷ x ∷ []) (suc zero) (suc (suc zero)) p₁
            , subst (λ Z → ⟨ fst v ∈ Z ⟩) p₂ r ) ∣₁ })
    (cond∈-out A {n = 1} (var zero) (con c) x sat)

  -- Lifted to Sat's own membership spec:  every member of Sat A phi0
  -- carries a witness w with pr (# 0) (fst w) inside it and fst w in
  -- c.  The envSet conjunct of Sat-mem is carried, never decoded.
  sat-atom-out : ⟨ x ∈ˢ Sat A φ₀ ⟩ → Goal
  sat-atom-out h =
    let hs : ⟨ (x ∈ˢ envSet A 1) ⊓ ((x ∷ []) ⊨ cond A φ₀) ⟩
        hs = subst ⟨_⟩ (Sat-mem A φ₀ x) h
    in  atom-out (hs .snd)

-- =====================================================================
-- SECTION 2.  THE OBLIGATION'S TYPE.  STATED, NOT INHABITED.
--
-- The brief's type, verbatim up to the two membership glyphs:  the
-- hypothesis reads at the V structure (renamed in Section 0), the
-- conclusion at the L structure.  The name is exported at the file's
-- top level;  no inhabitant stands under it, no postulate supports
-- it, and the file carries --safe.  Section 1 is the machine-checked
-- half of the review's FALSE verdict on this type.
-- =====================================================================

Sat-in-carrier-lim : Type (ℓ-suc ℓ)
Sat-in-carrier-lim =
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    (ω∈γ : ⟨ ω ∈ˢᵥ γ ⟩)
    (A : S) (hA : ⟨ fst A ∈ Lset γ ⟩)
    {n : ℕ} (φ : Formula S n)
  → ⟨ Sat A φ ∈ˢ LsetS γ oγ ⟩

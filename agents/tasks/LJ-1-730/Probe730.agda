{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.730] PROBE.  envSet-in-carrier-stage, priced at the brief's
--                     hypothesis.  Lands nothing in src/.
--
--   THE OBLIGATION (brief LJ-1.730, glyphs kept; the V-level membership
--   is renamed to ∈ˢᵥ because the CS-level one keeps the bare ∈ˢ, the
--   725-SPLIT precedent):
--     (γ : V ℓ) (oγ : IsOrd γ) → ⟨ ω ∈ˢᵥ γ ⟩
--     → (A : S) → ⟨ fst A ∈ Lset γ ⟩
--     → (n : ℕ) → ⟨ envSet A n ∈ˢ LsetS γ oγ ⟩
--
--   THE PRICING (D-10, truth before proof).  The conclusion fails at the
--   successor γ = sucV (sucV ω), which satisfies the hypothesis ω ∈ˢ γ:
--   take A := Lset (sucV ω) and n := 1.  Then ω ∈ˢ fst A
--   (ord∈Lset-suc), so the environment g ↦ ω over A carries the pair
--   pr (# 0) ω, and envSet-in A g puts that environment INSIDE
--   envSet A 1.  Rank climbs four links (rank-mono): rank ω <ˢ
--   rank ⁅#0,ω⁆ <ˢ rank (pr #0 ω) <ˢ rank (fst (envS A g)) <ˢ
--   rank (fst (envSet A 1)), and rank-Lset pins the last term inside
--   sucV (sucV ω).  Peeling the two successors (∈sucV-elim) and
--   descending the four links by the transitivity of the ordinal ω
--   leaves rank ω ∈ˢᵥ ω; rank-fix (IsOrd ω) turns that into ω ∈ˢᵥ ω,
--   and ∈-irrefl closes ⊥.  The witness is the term `membrane` below.
--
--   WHAT IS DELIVERED.  The machine-checked refutation `membrane`, the
--   counterexample objects (γ₂, oγ₂, A, ω∈A, hA), and the obligation's
--   TYPE stated with NO inhabitant under its name (the 725-SPLIT
--   form): the type is refutable, so no term of it can be written
--   without inconsistency.  review-of-envSet-in-carrier-stage.md
--   states the NO-GO and the headroom reading.
--
--   NOTHING IS POSTULATED.  No hole in the delivered file.  ONE Agda
--   process per run, GHCRTS = "-A64m -I0 -M2g", the wide caliber, set
--   on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-730.Probe730 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( ⊤̇ )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.FinData using ( Fin ) renaming ( zero to fzero )
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; sett; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; module InfinitySet )
open InfinitySet using ( ω; sucV; #_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ}
  using ( pair-spec; ∈sucV-elim; ∈sucV-inl; self∈sucV )
open import V.Coding {ℓ} using ( pr )

open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; IsOrd; Lset; 𝒟ₒ; 𝒟ₒ-intro )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Ordinal {ℓ} using ( ω-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( rank-Lset; ord∈Lset-suc )
open import L.Rank {ℓ} using ( rank; rank-mono; rank-fix )
open import L.Axioms.Basic {ℓ} using ( LsetS; isL-Lset; Lset-suc )
open import L.Coding.EnvSet {ℓ} lem using ( Ix; envS; envSet; envSet-in )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

-- The two structures, disambiguated: the V level carries the renamed
-- membership, the constructible level keeps the bare names.
open hPropStructure 𝒮ᵥ using ()
  renaming ( S to Sᵥ; _∈ˢ_ to _∈ˢᵥ_; _∈ᵗ_ to _∈ᵗᵥ_; _≈ˢ_ to _≈ˢᵥ_ )
open hPropStructure 𝒮ʟ

-- =====================================================================
-- THE COUNTEREXAMPLE OBJECTS.  γ = sucV (sucV ω) = ω+2, a successor
-- ABOVE ω, so the brief's hypothesis ω ∈ˢ γ HOLDS there.
-- =====================================================================

γ₂ : Sᵥ
γ₂ = sucV (sucV ω)

oγ₂ : IsOrd γ₂
oγ₂ = suc-ord (suc-ord ω-ord)

ω∈γ₂ : ⟨ ω ∈ˢᵥ γ₂ ⟩
ω∈γ₂ = ∈sucV-inl (self∈sucV ω)

-- The carrier: L's own stage ω+1.  It sits in Lset γ₂ by the sealed
-- zeroth instance (𝒟ₒ-intro at ⊤, renamed by Lset-suc), and it HOLDS
-- ω (ord∈Lset-suc at ω).
A : S
A = Lset (sucV ω) , isL-Lset (sucV ω) (suc-ord ω-ord)

ω∈A : ⟨ ω ∈ˢᵥ fst A ⟩
ω∈A = ord∈Lset-suc ω ω-ord

hA : ⟨ fst A ∈ˢᵥ Lset γ₂ ⟩
hA = subst (λ w → ⟨ Lset (sucV ω) ∈ˢᵥ w ⟩) (sym (Lset-suc (sucV ω)))
      (𝒟ₒ-intro (Lset (sucV ω)) (Lset (sucV ω))
        ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset (sucV ω)) ∣₁)

-- =====================================================================
-- THE OBLIGATION'S TYPE.  STATED, NOT INHABITED.  The name is exported
-- at the file's top level as a TYPE; no term stands under it and no
-- postulate supports it.  `membrane` below shows the type is FALSE at
-- the instance (γ₂, A, 1) above, so an inhabitant would close ⊥.
-- =====================================================================

envSet-in-carrier-stage : Type (ℓ-suc ℓ)
envSet-in-carrier-stage =
    (γ : V ℓ) (oγ : IsOrd γ) → ⟨ ω ∈ˢᵥ γ ⟩
  → (A : S) → ⟨ fst A ∈ Lset γ ⟩
  → (n : ℕ) → ⟨ envSet A n ∈ˢ LsetS γ oγ ⟩

-- =====================================================================
-- THE MEMBRANE.  The obligation's conclusion, instantiated at (γ₂, A,
-- 1) with the hypothesis ω ∈ˢ γ satisfied, closes Empty.⊥.  Rank
-- climbs four links by rank-mono (ω into the unordered pair, the pair
-- into the Kuratowski pair, the Kuratowski pair into the environment,
-- the environment into envSet A 1), rank-Lset pins the last rank
-- inside γ₂, and the two successors peel by ∈sucV-elim.  Each of the
-- four descents consumes one link by the transitivity of the ordinal
-- ω, leaving rank ω ∈ˢᵥ ω; rank-fix (IsOrd ω) reads it as ω ∈ˢᵥ ω,
-- and ∈-irrefl closes ⊥.
-- =====================================================================

module Membrane (h : ⟨ envSet A 1 ∈ˢ LsetS γ₂ oγ₂ ⟩) where

  -- The fibre of ω in the carrier, and the environment of length 1
  -- that maps 0 to it.  ix is private in EnvSet, but envS is public
  -- and transparent: fst (envS A g) is the concrete `env` of the
  -- values ⟪ fst A ⟫↪ (g i).
  pt : ⟪ fst A ⟫
  pt = ∈-asFiber {a = ω} {b = fst A} ω∈A .fst

  pt≡ : ⟪ fst A ⟫↪ pt ≡ ω
  pt≡ = ∈-asFiber {a = ω} {b = fst A} ω∈A .snd

  g : Ix A 1
  g _ = pt

  -- The two pair memberships, read off the spec equalities from the
  -- right disjunct (the second component).
  ω∈pair : ⟨ ω ∈ˢᵥ ⁅ # 0 , ω ⁆ ⟩
  ω∈pair =
    subst (λ Z → ⟨ Z ⟩) (sym (pair-spec (# 0) ω ω)) ∣ inr refl ∣₁

  pair∈pr : ⟨ ⁅ # 0 , ω ⁆ ∈ˢᵥ pr (# 0) ω ⟩
  pair∈pr =
    subst (λ Z → ⟨ Z ⟩)
      (sym (pair-spec (⁅ # 0 ⁆s) (⁅ # 0 , ω ⁆) (⁅ # 0 , ω ⁆)))
      ∣ inr refl ∣₁

  -- The Kuratowski pair sits in the environment: the concrete `env`
  -- carries it as the entry at index 0 (EnvSet's `into` direction,
  -- re-read here because `into` is private).
  pr∈env : ⟨ pr (# 0) ω ∈ˢᵥ fst (envS A g) ⟩
  pr∈env = ∣ lift fzero , cong (pr (# 0)) pt≡ ∣₁

  r1 : ⟨ rank ω ∈ˢᵥ rank ⁅ # 0 , ω ⁆ ⟩
  r1 = rank-mono ω ⁅ # 0 , ω ⁆ ω∈pair

  r2 : ⟨ rank ⁅ # 0 , ω ⁆ ∈ˢᵥ rank (pr (# 0) ω) ⟩
  r2 = rank-mono ⁅ # 0 , ω ⁆ (pr (# 0) ω) pair∈pr

  r3 : ⟨ rank (pr (# 0) ω) ∈ˢᵥ rank (fst (envS A g)) ⟩
  r3 = rank-mono (pr (# 0) ω) (fst (envS A g)) pr∈env

  r4 : ⟨ rank (fst (envS A g)) ∈ˢᵥ rank (fst (envSet A 1)) ⟩
  r4 = rank-mono (fst (envS A g)) (fst (envSet A 1)) (envSet-in A g)

  r5 : ⟨ rank (fst (envSet A 1)) ∈ˢᵥ γ₂ ⟩
  r5 = rank-Lset γ₂ oγ₂ (fst (envSet A 1)) h

  transω : (x y : Sᵥ) → ⟨ x ∈ˢᵥ y ⟩ → ⟨ y ∈ˢᵥ ω ⟩ → ⟨ x ∈ˢᵥ ω ⟩
  transω x y x∈y y∈ω = fst ω-ord x∈y y∈ω

  toω : (x y : Sᵥ) → ⟨ x ∈ˢᵥ y ⟩ → ⟨ y ∈ˢᵥ sucV ω ⟩ → ⟨ x ∈ˢᵥ ω ⟩
  toω x y x∈y y∈ =
    ∈sucV-elim ((x ∈ˢᵥ ω) .snd) y∈
      (λ y∈ω → transω x y x∈y y∈ω)
      (λ y≡ω → subst (λ w → ⟨ x ∈ˢᵥ w ⟩) y≡ω x∈y)

  descend : (x y : Sᵥ) → ⟨ x ∈ˢᵥ y ⟩
          → ⟨ y ∈ˢᵥ sucV (sucV ω) ⟩ → ⟨ x ∈ˢᵥ sucV ω ⟩
  descend x y x∈y y∈ =
    ∈sucV-elim ((x ∈ˢᵥ sucV ω) .snd) y∈
      (λ y∈ω → ∈sucV-inl (toω x y x∈y y∈ω))
      (λ y≡ω → subst (λ w → ⟨ x ∈ˢᵥ w ⟩) y≡ω x∈y)

  chain : ⟨ rank ω ∈ˢᵥ ω ⟩
  chain =
    transω (rank ω) (rank ⁅ # 0 , ω ⁆) r1
      (transω (rank ⁅ # 0 , ω ⁆) (rank (pr (# 0) ω)) r2
        (toω (rank (pr (# 0) ω)) (rank (fst (envS A g))) r3
          (descend (rank (fst (envS A g))) (rank (fst (envSet A 1))) r4 r5)))

  membrane : Empty.⊥
  membrane = ∈-irrefl ω (subst (λ w → ⟨ w ∈ˢᵥ ω ⟩) (rank-fix ω ω-ord) chain)

-- The refutation, at the file's top level under its own name.
envSet-in-carrier-stage-false :
    ⟨ envSet A 1 ∈ˢ LsetS γ₂ oγ₂ ⟩ → Empty.⊥
envSet-in-carrier-stage-false = Membrane.membrane

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.733] PROBE.  defat-fill-in-bound, the bounded DefAt fill:
-- the obligation the [LJ-1.725-SPLIT] membrane blocked.  Lands
-- nothing in src/.
--
--   THE OBLIGATION (brief LJ-1.733; glyphs kept, except that the
--   V-level membership is renamed ∈ˢᵥ because the CS-level one keeps
--   the bare ∈ˢ, the 725-SPLIT disambiguation; and the Powerset-local
--   names toS and DA are resolved at this file's top level):
--     (γ : V ℓ) (oγ : IsOrd γ) → ⟨ ω ∈ˢᵥ γ ⟩
--     → (A : S) → ⟨ fst A ∈ Lset γ ⟩
--     → keyS-in-carrier-stage → envSet-in-carrier-stage
--     → Sat-in-carrier-stage
--     → ∀ {n} (w : Fin n) (env : S ^ n)
--     → fst (lookup w env) ≡ fst A
--     → (z : S) (ψ : Formula ⟪ fst A ⟫ 1)
--     → DefOf.defSet (fst A) ψ ≡ fst z
--     → ⟨ (Sat A (toS A ψ) ∷ keyS A ψ ∷ z ∷ env)
--           ⊨ relativize (LsetS γ oγ) (DefBody w) ⟩
--
--   THE CLAUSE (dev/pod/instructions/coder.md, a module hypothesis
--   taken from a predecessor).  Take the type from the probe that
--   typechecked and the verdict from the report;  if the report is
--   NO-GO or names the statement FALSE, stop and say so with
--   file:line, and DO NOT INHABIT the brief's type.  Measured here:
--     keyS-in-carrier-stage    NO-GO, FALSE.  agents/tasks/LJ-1-729/
--                              review-of-keyS-in-carrier-stage.md, HEAD;
--                              corrected scope keyS-in-carrier-lim
--                              (closedω γ) is INHABITED in Probe729.agda.
--     envSet-in-carrier-stage  NO-GO, FALSE, machine-checked.
--                              agents/tasks/LJ-1-730/review-of-envSet-
--                              in-carrier-stage.md, HEAD;
--                              envSet-in-carrier-stage-false at
--                              Probe730.agda:208.
--     Sat-in-carrier-stage     NO REPORT EXISTS.  LJ-1.731 has no
--                              probe, no report, no review in any
--                              worktree;  its worktree carries only the
--                              brief.  Its type is transcribed from
--                              that brief's obligation block, the only
--                              source.
--
--   WHAT IS DELIVERED.  (1) The three hypothesis types, RESTATED, not
--   imported.  (2) The obligation's TYPE, stated with NO inhabitant
--   under its name (the 725-SPLIT form):  the clause forbids an
--   inhabitant, and the premise set is inconsistent, so the type is
--   vacuous -- an inhabitant would hide the membrane behind a theorem
--   name.  (3) The W3 measurement:  from a hypothesis of type
--   envSet-in-carrier-stage ALONE, Empty.⊥ closes (Section 3), the
--   730 refutation re-measured at this file's own restated type --
--   not imported, per the brief.  Nothing here inhabits stage-read,
--   defat-fill-in-bound, unbounded fill, or any corrected scope;  the
--   corrected scopes for envSet and Sat are UNRULED and UNDELIVERED
--   respectively.
--
-- NOTHING IS POSTULATED.  No hole in the delivered file.  ONE Agda
-- process per run, GHCRTS = "-A64m -I0 -M2g", the wide caliber, set
-- on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-733.Probe733 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ⊤̇ )
open import FOL.Manipulation.Relabelling using ( mapFo )
open import FOL.Manipulation.Relativize using ( relativize )
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
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; 𝒟ₒ; 𝒟ₒ-intro )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Ordinal {ℓ} using ( ω-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( rank-Lset; ord∈Lset-suc )
open import L.Rank {ℓ} using ( rank; rank-mono; rank-fix )
open import L.Axioms.Basic {ℓ} using ( LsetS; isL-Lset; Lset-suc )
open import L.Coding.EnvSet {ℓ} lem using ( Ix; envS; envSet; envSet-in )
open import L.Coding.CodeSet {ℓ} lem using ( keyS )
open import L.Coding.Sat {ℓ} lem using ( Sat )
open import L.Coding.Bridge {ℓ} lem using ( asConst )
open import L.Coding.Powerset {ℓ} lem using ( DefBody )
import FOL.Absoluteness

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

-- The two structures, disambiguated: the V level carries the renamed
-- membership, the constructible level keeps the bare names.
open hPropStructure 𝒮ᵥ using ()
  renaming ( S to Sᵥ; _∈ˢ_ to _∈ˢᵥ_; _∈ᵗ_ to _∈ᵗᵥ_; _≈ˢ_ to _≈ˢᵥ_ )
open hPropStructure 𝒮ʟ

-- The obligation's satisfaction is the INNER (L) reading at the
-- identity constant interpretation, the one Powerset's own fill
-- concludes at (AbsL there, AbsL733 here).
module AbsL733 = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL733 using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- The Powerset-local toS, resolved at this file's top level (the
-- brief's `toS ψ` at A): the carrier's members coded as constants.
toS : (A : S) → Formula ⟪ fst A ⟫ 1 → Formula S 1
toS A ψ = mapFo (asConst A) ψ

-- =====================================================================
-- SECTION 1.  THE THREE HYPOTHESIS TYPES, RESTATED, NOT IMPORTED.
-- =====================================================================

-- Hypothesis 1, verbatim from the probe that typechecked it,
-- agents/tasks/LJ-1-729/Probe729.agda Section 5.  The verdict is that
-- report's HEAD: NO-GO, the type is FALSE at this generality; the
-- corrected scope keyS-in-carrier-lim under closedω γ is INHABITED in
-- that probe.  No inhabitant stands under the name here.

keyS-in-carrier-stage : Type (ℓ-suc ℓ)
keyS-in-carrier-stage =
    (γ : V ℓ) (oγ : IsOrd γ)
    (ω∈γ : ⟨ ω ∈ˢᵥ γ ⟩)
    (A : S) (hA : ⟨ fst A ∈ Lset γ ⟩)
    {n : ℕ} (φ : Formula ⟪ fst A ⟫ n)
  → ⟨ keyS A φ ∈ˢ LsetS γ oγ ⟩

-- Hypothesis 2, verbatim from agents/tasks/LJ-1-730/Probe730.agda
-- (the 725-SPLIT form).  The verdict is that report's HEAD: NO-GO,
-- FALSE, machine-checked by envSet-in-carrier-stage-false
-- (Probe730.agda:208).  No inhabitant stands under the name here.

envSet-in-carrier-stage : Type (ℓ-suc ℓ)
envSet-in-carrier-stage =
    (γ : V ℓ) (oγ : IsOrd γ) → ⟨ ω ∈ˢᵥ γ ⟩
  → (A : S) → ⟨ fst A ∈ Lset γ ⟩
  → (n : ℕ) → ⟨ envSet A n ∈ˢ LsetS γ oγ ⟩

-- Hypothesis 3, transcribed from the LJ-1.731 BRIEF's obligation
-- block -- the only source in any worktree (its task directory
-- carries only agents/tasks/LJ-1-731/LJ-1.731.md).  No probe has
-- ever typechecked this type and no verdict exists for it.

Sat-in-carrier-stage : Type (ℓ-suc ℓ)
Sat-in-carrier-stage =
    (γ : V ℓ) (oγ : IsOrd γ) → ⟨ ω ∈ˢᵥ γ ⟩
  → (A : S) → ⟨ fst A ∈ Lset γ ⟩
  → {n : ℕ} (φ : Formula S n)
  → ⟨ Sat A φ ∈ˢ LsetS γ oγ ⟩

-- =====================================================================
-- SECTION 2.  THE OBLIGATION'S TYPE.  STATED, NOT INHABITED.
--
-- The brief's type, verbatim up to the two resolutions recorded in
-- the header.  The name is exported at the file's top level as a
-- TYPE;  no term stands under it and no postulate supports it.  The
-- clause forbids an inhabitant:  two of the three module hypotheses
-- are FALSE by their predecessors' reports, so the premise set is
-- inconsistent and the type is vacuous -- Section 3 closes Empty.⊥
-- from one hypothesis alone.  review-of-defat-fill-in-bound.md
-- states the NO-GO.
-- =====================================================================

defat-fill-in-bound : Type (ℓ-suc ℓ)
defat-fill-in-bound =
    (γ : V ℓ) (oγ : IsOrd γ)
  → ⟨ ω ∈ˢᵥ γ ⟩
  → (A : S) → ⟨ fst A ∈ Lset γ ⟩
  → keyS-in-carrier-stage
  → envSet-in-carrier-stage
  → Sat-in-carrier-stage
  → ∀ {n} (w : Fin n) (env : S ^ n)
  → fst (lookup w env) ≡ fst A
  → (z : S) (ψ : Formula ⟪ fst A ⟫ 1)
  → DefOf.defSet (fst A) ψ ≡ fst z
  → ⟨ (Sat A (toS A ψ) ∷ keyS A ψ ∷ z ∷ env)
        ⊨ relativize (LsetS γ oγ) (DefBody w) ⟩

-- =====================================================================
-- SECTION 3.  THE W3 MEASUREMENT.  The premise set is INCONSISTENT:
-- from a hypothesis of type envSet-in-carrier-stage ALONE, Empty.⊥
-- closes.  The counterexample is 730's (γ = sucV (sucV ω), A =
-- Lset (sucV ω), n = 1), which SATISFIES the hypothesis ω ∈ˢᵥ γ;  the
-- rank chain is 730's membrane, RE-MEASURED at this file's own
-- restated type -- the Boundary's rule that a measured result is
-- re-measured at its own site, and 730's review names exactly this
-- sweep as owed before any GO price at the sibling sites.  Probe730
-- is NOT imported:  every object below is rebuilt here from landed
-- masters only.
-- =====================================================================

-- The counterexample objects.

gamma₂ : Sᵥ
gamma₂ = sucV (sucV ω)

oγ₂ : IsOrd gamma₂
oγ₂ = suc-ord (suc-ord ω-ord)

ω∈γ₂ : ⟨ ω ∈ˢᵥ gamma₂ ⟩
ω∈γ₂ = ∈sucV-inl (self∈sucV ω)

-- The carrier: L's own stage ω+1.  It sits in Lset gamma₂ by the
-- sealed zeroth instance (𝒟ₒ-intro at ⊤, renamed by Lset-suc), and
-- it HOLDS ω (ord∈Lset-suc at ω).
Ace : S
Ace = Lset (sucV ω) , isL-Lset (sucV ω) (suc-ord ω-ord)

ω∈Ace : ⟨ ω ∈ˢᵥ fst Ace ⟩
ω∈Ace = ord∈Lset-suc ω ω-ord

hA₂ : ⟨ fst Ace ∈ˢᵥ Lset gamma₂ ⟩
hA₂ = subst (λ w → ⟨ Lset (sucV ω) ∈ˢᵥ w ⟩) (sym (Lset-suc (sucV ω)))
        (𝒟ₒ-intro (Lset (sucV ω)) (Lset (sucV ω))
          ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset (sucV ω)) ∣₁)

module Membrane (h : ⟨ envSet Ace 1 ∈ˢ LsetS gamma₂ oγ₂ ⟩) where

  -- The fibre of ω in the carrier, and the environment of length 1
  -- that maps 0 to it.  ix is private in EnvSet, but envS is public
  -- and transparent: fst (envS Ace g) is the concrete `env` of the
  -- values ⟪ fst Ace ⟫↪ (g i).
  pt : ⟪ fst Ace ⟫
  pt = ∈-asFiber {a = ω} {b = fst Ace} ω∈Ace .fst

  pt≡ : ⟪ fst Ace ⟫↪ pt ≡ ω
  pt≡ = ∈-asFiber {a = ω} {b = fst Ace} ω∈Ace .snd

  g : Ix Ace 1
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
  pr∈env : ⟨ pr (# 0) ω ∈ˢᵥ fst (envS Ace g) ⟩
  pr∈env = ∣ lift fzero , cong (pr (# 0)) pt≡ ∣₁

  r1 : ⟨ rank ω ∈ˢᵥ rank ⁅ # 0 , ω ⁆ ⟩
  r1 = rank-mono ω ⁅ # 0 , ω ⁆ ω∈pair

  r2 : ⟨ rank ⁅ # 0 , ω ⁆ ∈ˢᵥ rank (pr (# 0) ω) ⟩
  r2 = rank-mono ⁅ # 0 , ω ⁆ (pr (# 0) ω) pair∈pr

  r3 : ⟨ rank (pr (# 0) ω) ∈ˢᵥ rank (fst (envS Ace g)) ⟩
  r3 = rank-mono (pr (# 0) ω) (fst (envS Ace g)) pr∈env

  r4 : ⟨ rank (fst (envS Ace g)) ∈ˢᵥ rank (fst (envSet Ace 1)) ⟩
  r4 = rank-mono (fst (envS Ace g)) (fst (envSet Ace 1)) (envSet-in Ace g)

  r5 : ⟨ rank (fst (envSet Ace 1)) ∈ˢᵥ gamma₂ ⟩
  r5 = rank-Lset gamma₂ oγ₂ (fst (envSet Ace 1)) h

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
        (toω (rank (pr (# 0) ω)) (rank (fst (envS Ace g))) r3
          (descend (rank (fst (envS Ace g))) (rank (fst (envSet Ace 1))) r4 r5)))

  closes : Empty.⊥
  closes = ∈-irrefl ω (subst (λ w → ⟨ w ∈ˢᵥ ω ⟩) (rank-fix ω ω-ord) chain)

-- The measurement, at the file's top level under its own name: the
-- restated envSet hypothesis, instantiated at the counterexample,
-- closes Empty.⊥.  So the brief's premise set is inconsistent, the
-- obligation's type is vacuous, and no honest GO can be returned at
-- the offered scope.
envSet-hypothesis-closes-bottom :
    envSet-in-carrier-stage → Empty.⊥
envSet-hypothesis-closes-bottom h =
  Membrane.closes (h gamma₂ oγ₂ ω∈γ₂ Ace hA₂ 1)

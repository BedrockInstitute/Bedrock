{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.669] PROBE.  A soundness lemma at ARITY 4 with `K` in the
-- environment, taking the chapter's own `Δ₀-matrix`, whose transfer
-- runs at the Σ₁ statement and NOT through `mapΔ₀`.
-- Lands nothing in src/.
--
-- THE VERDICT IS NO-GO, stated in review-of-sound-at-arity4.md.
-- The obligation `sound-at-arity4` is NOT stated in this file: a
-- qualified reference to an absent name is the witness meter's
-- [NotInScope], and that reading is the NO-GO.  The file instead
-- states, green, every fact the verdict rests on.
--
--   PART 1   The chapter's own shape, from [LJ-1.661] PART 2
--            (agents/tasks/LJ-1-661/Probe661.agda:105-126): the
--            bounded matrix at arity 4, env u ∷ v ∷ γ ∷ K, certified
--            Δ₀, and the two Σ₁ readings that keep `K` free.
--
--   PART 2   W3, the class-carrier half.  `σ₁-up` at `AbsL` consumes
--            `σ-Δ₀ Δ₀-matrix` directly.  The formula already lives on
--            `CS.S = AbsL.SM` (`𝒮ʟ = 𝒮ᵥ ↾ isL`,
--            src/L/Constructible.lagda.md:420-421).  No `mapΔ₀`.
--            Sealed (P-l): a transparent matrix in a satisfaction
--            TYPE unfolds the bounded graph and was measured to wall
--            the wide caliber at [LJ-1.662] (Probe662.agda:102-108).
--
--   PART 3   W3, the two walls that stop a HoodSound-shaped lemma.
--            Stated as types, not as failed terms (those live in
--            Wall669.agda.txt).  (i) `σ₁-up` is inner to ambient and
--            cannot run the last leg of [LJ-1.658]'s chain.  (ii) The
--            collapse image is a different constant domain, so the
--            chapter's `Σ₁-matrix` does not type as a certificate
--            there.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-669.Probe669 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ∃̇_ )
open import FOL.LevyHierarchy using ( Δ₀; Σ₁; σ-Δ₀; σ-∃; Π₁; π-Δ₀ )
open import FOL.Manipulation.Parameters using ( countFo )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.BoundedSubset {ℓ} lem using ( module LevelHood0 )

open import Cubical.Data.Vec using ( map )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

module CS = hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ )

-- =====================================================================
-- PART 1.  THE CHAPTER'S OWN SHAPE.
-- =====================================================================

-- The chapter's instantiation at n = 0, all Fin slots zero, the
-- delivered convention (agents/tasks/LJ-1-661/Probe661.agda:98-100).
module LH0 = LevelHood0
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero

-- SEALED (P-l, dev/LESSONS.md:2367).  The matrix is the chapter's
-- `levelHoodB` (src/L/BoundedSubset.lagda.md:848-852).  Left
-- transparent, a satisfaction type names the whole bounded graph
-- inside the elaborator.  The four facts below are the official
-- readings and no consumer needs `unfolding`.
opaque
  matrix : Formula CS.S 4
  matrix = LH0.matrix

  Δ₀-matrix : Δ₀ matrix
  Δ₀-matrix = LH0.Δ₀-matrix

  -- The matrix is a normal form: its erasure count is `refl`
  -- (re-measured here; first measured at
  -- agents/tasks/LJ-1-651/Probe651.agda:73-74).
  count-matrix : countFo matrix ≡ 0
  count-matrix = refl

  -- W3's statement at arity 4: the Δ₀ matrix itself, graded Σ₁ by
  -- the leaf constructor.  `K` stays in the environment.
  Σ₁-matrix : Σ₁ matrix
  Σ₁-matrix = σ-Δ₀ Δ₀-matrix

  -- The arity-3 reading that still carries `K`: one unbounded `∃̇`
  -- over the unused slot.  The chapter exports this grade as
  -- `Σ₁-levelHood` (src/L/BoundedSubset.lagda.md:142-146).
  step1 : Formula CS.S 3
  step1 = ∃̇ matrix

  Σ₁-step1 : Σ₁ step1
  Σ₁-step1 = σ-∃ Σ₁-matrix

-- =====================================================================
-- PART 2.  W3, CLASS-CARRIER HALF.  Σ₁ transfer, no `mapΔ₀`.
-- =====================================================================

-- W2: the mathematics is the delivered `σ₁-up`
-- (src/FOL/Absoluteness.lagda.md:182-185), instantiated at the one
-- carrier the chapter's matrix already inhabits.  The generic form
-- is not rewritten.  A deadline does not force a fixed-carrier copy.
--
-- `σ₁-up (σ-Δ₀ d) = subst ⟨_⟩ (abs₀ d δ)` at
-- src/FOL/Absoluteness.lagda.md:184.  That is the Σ₁ statement's own
-- transfer, not a `mapΔ₀` of the certificate onto a foreign domain.

transfer-at-arity4 :
  (δ : AbsL.SM ^ 4)
  → ⟨ δ AbsL.⊨ᵐ matrix ⟩
  → ⟨ map fst δ AbsL.⊨ᵛ matrix ⟩
transfer-at-arity4 = AbsL.σ₁-up Σ₁-matrix

-- The same transfer at the arity-3 wrapping, `K` still free.
transfer-at-step1 :
  (δ : AbsL.SM ^ 3)
  → ⟨ δ AbsL.⊨ᵐ step1 ⟩
  → ⟨ map fst δ AbsL.⊨ᵛ step1 ⟩
transfer-at-step1 = AbsL.σ₁-up Σ₁-step1

-- The reverse direction EXISTS at this carrier and also avoids
-- `mapΔ₀`, but it is Π₁-down, not Σ₁-up
-- (src/FOL/Absoluteness.lagda.md:187-190).  Recorded so the next
-- brief does not rediscover it.
reverse-at-arity4 :
  (δ : AbsL.SM ^ 4)
  → ⟨ map fst δ AbsL.⊨ᵛ matrix ⟩
  → ⟨ δ AbsL.⊨ᵐ matrix ⟩
reverse-at-arity4 = AbsL.π₁-down (π-Δ₀ Δ₀-matrix)

-- =====================================================================
-- PART 3.  THE TWO WALLS, AS TYPES.
-- =====================================================================
--
-- Wall (i), direction.  [LJ-1.658]'s last leg
-- (agents/tasks/LJ-1-658/Probe658.agda:269-270) is ambient to inner
-- at L.  `σ₁-up` has the opposite arrow.  `reverse-at-arity4` above
-- is the arrow that works, and it is Π₁.  Wall669.agda.txt ascribes
-- `AbsL.σ₁-up Σ₁-matrix` to the reverse type and is red.
--
-- Wall (ii), constant domain.  A collapse-image carrier
-- `Σ[ x ∈ S ] ⟨ x ∈ˢ P ⟩` is not `CS.S`.  The chapter's `Σ₁-matrix`
-- is a certificate at `CS.S`.  It does not type as the argument of
-- `σ₁-up` at that image.  The only delivered construction that
-- places a class-carrier Σ₁ certificate at an image is
-- [LJ-1.161]'s `mapΣ₁ Empty.rec* (erase-Σ₁ φ p s)`
-- (agents/tasks/LJ-1-161/ProbeLJ1161A.agda:83-86), and `mapΣ₁` is
-- `mapΔ₀` at the leaf (src/FOL/Manipulation/Relabelling.lagda.md:234).
-- Wall669-ii.agda.txt ascribes `Abs∅.σ₁-up Σ₁-matrix` at a dummy
-- image and is red.
--
-- =====================================================================
-- PART 4.  THE ABSENCE.
-- =====================================================================
--
-- The obligation `sound-at-arity4` is a HoodSound-shaped lemma: from
-- a collapse-image reading of the arity-4 matrix, conclude
-- `v ≡ Lset γ`.  That chain has four legs
-- (agents/tasks/LJ-1-658/Probe658.agda:247-270):
--
--   inner πX  --σ₁-up-->  ambient πX  --⊨-map-->  ambient L
--             --π₁-down--> inner L    --reader-->  v ≡ Lset γ
--
-- Leg 1 needs a Σ₁ certificate at the image (wall ii, through
-- `mapΔ₀`).  Leg 3 needs ambient to inner (wall i, not Σ₁).  Either
-- wall stops a transfer that is both at Σ₁ and free of `mapΔ₀`.
-- See review-of-sound-at-arity4.md.

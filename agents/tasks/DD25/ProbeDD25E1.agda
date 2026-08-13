{-# OPTIONS --cubical --safe --guardedness #-}

-- [DD25 review of LJ-1.38] THE VACUITY CLAIM, MACHINE-CHECKED.
--
-- The return `_build/lj-1.38-report.md` refuses the story-to-machine
-- agreement.  Its systematic claim (section 2, row 5) is that every
-- story row frame ends in a bounded universal over the value `yc`,
-- which says nothing when `yc` is empty, while the machine's rows end
-- in `extAt yc body`, which constrains an empty value.
--
-- This probe does not argue.  It states the two endings against the
-- delivered semantics and asks Agda.
--
-- SECTION A.  The two endings, generic in the model.
-- SECTION B.  The delivered atom row, at the point the delivered
--             decode hands it over.
-- SECTION C.  The slot arithmetic of the two atom bodies.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed; thrown away per D-1.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeDD25E1 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ⊤̇; ∀̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-zero )
open import L.Coding.Model {ℓ}
  using ( extAt; extAt-out; extAt-in; atomBody; memRel )
open import L.Condensation {ℓ} lem using ( module Mem )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- SECTION A.  THE TWO ENDINGS.
--
-- The story's frames end in `∀̇∈ (var yc) body`
-- (src/L/Condensation.lagda.md:638, :657, :695, :716).
-- The machine's rows end in `extAt yc body`
-- (src/L/Coding/Model.lagda.md:1612, :1762, :1944).
-- =====================================================================

-- A1.  At an EMPTY value the story's ending is discharged by nothing.
story-vacuous : ∀ {n} (y : Fin n) (φ : Formula S (suc n)) (γ : S ^ n)
              → ((x : S) → ⟨ fst x ∈ fst (lookup y γ) ⟩ → Empty.⊥)
              → ⟨ γ ⊨ ∀̇∈ (var y) φ ⟩
story-vacuous y φ γ emp z z∈ = Empty.rec (emp z z∈)

-- A2.  At an EMPTY value the machine's ending forbids every satisfier.
machine-binds : ∀ {n} (y : Fin n) (φ : Formula S (suc n)) (γ : S ^ n)
              → ((x : S) → ⟨ fst x ∈ fst (lookup y γ) ⟩ → Empty.⊥)
              → ⟨ γ ⊨ extAt y φ ⟩
              → (z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → Empty.⊥
machine-binds y φ γ emp h z hz = emp z (extAt-in y φ γ h z hz)

-- A3.  So the story's ending does NOT imply the machine's.  The
-- countermodel is the empty set of L at the value slot and a body
-- every element satisfies.
γ∅ : S ^ 1
γ∅ = numeralL 0 ∷ []

∅-empty : (x : S) → ⟨ fst x ∈ fst (lookup zero γ∅) ⟩ → Empty.⊥
∅-empty x x∈ = numeralL-zero x x∈

story-holds : ⟨ γ∅ ⊨ ∀̇∈ (var zero) ⊤̇ ⟩
story-holds = story-vacuous zero ⊤̇ γ∅ ∅-empty

machine-fails : ⟨ γ∅ ⊨ extAt zero ⊤̇ ⟩ → Empty.⊥
machine-fails h = machine-binds zero ⊤̇ γ∅ ∅-empty h (numeralL 0) _

no-transfer : (⟨ γ∅ ⊨ ∀̇∈ (var zero) ⊤̇ ⟩ → ⟨ γ∅ ⊨ extAt zero ⊤̇ ⟩) → Empty.⊥
no-transfer f = machine-fails (f story-holds)

-- =====================================================================
-- SECTION B.  THE DELIVERED ATOM ROW.
--
-- `BinEnvDecode.binEnv-out` (src/L/Condensation.lagda.md:883-895)
-- hands the row's body at the environment
-- `e ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ`, for every member `e` of `yc`.
-- The machine's `atomRel` (src/L/Coding/Model.lagda.md:1760-1762)
-- hands `extAt yc (atomBody cmp)` at `E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ`.
-- =====================================================================

module AtomRow {m : ℕ} (C T B N K t0 t1 : Fin m) (γ : S ^ m)
               (c ar a b yc E : S) where

  δ : S → S ^ (7 + m)
  δ e = e ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ

  μ : S ^ (6 + m)
  μ = E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ

  -- B1.  At an EMPTY value, the story's whole row content is
  -- discharged by nothing.
  story-free : ((x : S) → ⟨ fst x ∈ fst yc ⟩ → Empty.⊥)
             → (e : S) → ⟨ fst e ∈ fst yc ⟩
             → ⟨ δ e ⊨ Mem.bodyM C T B N K t0 t1 ⟩
  story-free emp e e∈ = Empty.rec (emp e e∈)

  -- B2.  At a NONEMPTY value the story's row is not weak, it is wrong:
  -- one member of `yc` forces every member of `E` that lies in `K`
  -- into `yc`.  The reason is that the story's atom body reads the two
  -- terms at the FRAME's member, not at the extension candidate, so
  -- the defining condition does not mention the element it defines.
  story-forces-all : (e : S) → ⟨ fst e ∈ fst yc ⟩
    → ⟨ δ e ⊨ Mem.bodyM C T B N K t0 t1 ⟩
    → (z : S) → ⟨ fst z ∈ fst (lookup K γ) ⟩ → ⟨ fst z ∈ fst E ⟩
    → ⟨ fst z ∈ fst yc ⟩
  story-forces-all e e∈ h z z∈K z∈E = h .snd z z∈K (z∈E , h .fst e e∈ .snd)

  -- B3.  So the story's row and the machine's row are INCOMPATIBLE at
  -- every value that is nonempty and misses one member of E in K.
  -- That is the normal case: it is an atom whose extension is a proper
  -- nonempty part of the environment set.
  clash : (e : S) → ⟨ fst e ∈ fst yc ⟩
    → ⟨ δ e ⊨ Mem.bodyM C T B N K t0 t1 ⟩
    → ⟨ μ ⊨ extAt (suc zero) (atomBody memRel) ⟩
    → (z : S) → ⟨ fst z ∈ fst (lookup K γ) ⟩ → ⟨ fst z ∈ fst E ⟩
    → (⟨ (z ∷ μ) ⊨ atomBody memRel ⟩ → Empty.⊥)
    → Empty.⊥
  clash e e∈ h hm z z∈K z∈E ¬at =
    ¬at (extAt-out (suc zero) (atomBody memRel) μ hm z
          (story-forces-all e e∈ h z z∈K z∈E))

-- =====================================================================
-- SECTION C.  THE SLOT ARITHMETIC.
--
-- The story's atom body reads the term environment at
-- `suc (suc (suc zero))` (src/L/Condensation.lagda.md:946, :952); the
-- machine's reads it at `suc (suc zero)`
-- (src/L/Coding/Model.lagda.md:1749, :1755-1758).  The two points
-- differ, and the story's is the frame's extra binder.
-- =====================================================================

story-term-point : ∀ {m} (w v cand e E yc b a ar c : S) (γ : S ^ m)
  → lookup (suc (suc (suc zero)))
      (w ∷ v ∷ cand ∷ e ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ≡ e
story-term-point w v cand e E yc b a ar c γ = refl

machine-term-point : ∀ {m} (w v cand E yc b a ar c : S) (γ : S ^ m)
  → lookup (suc (suc zero))
      (w ∷ v ∷ cand ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ≡ cand
machine-term-point w v cand E yc b a ar c γ = refl

-- The Forall row's extended environment: the story lands on E
-- (src/L/Condensation.lagda.md:1142), the machine on the subvalue ya
-- (src/L/Coding/Model.lagda.md:1573).  Same numeral, different slot,
-- because the story's environment carries the frame's extra member.
story-forall-point : ∀ {m} (e' x cand e E ya yc a ar c : S) (γ : S ^ m)
  → lookup (suc (suc (suc (suc zero))))
      (e' ∷ x ∷ cand ∷ e ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ≡ E
story-forall-point e' x cand e E ya yc a ar c γ = refl

machine-forall-point : ∀ {m} (e' x cand E ya yc a ar c : S) (γ : S ^ m)
  → lookup (suc (suc (suc (suc zero))))
      (e' ∷ x ∷ cand ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ≡ ya
machine-forall-point e' x cand E ya yc a ar c γ = refl

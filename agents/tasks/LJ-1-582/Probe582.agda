{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.582]  CLAUSE (i) OF THE LEVEL-HOOD CERTIFICATE.
--
--   The obligation is `defines-level : Cert.DefinesLevel`, clause (i) at
--   agents/tasks/LJ-1-578/Probe578.agda:234-240.
--
--   W3 IS SECTION 1 and the brief ordered it written FIRST and
--   typechecked ALONE.  The slice is agents/tasks/LJ-1-582/runs/W3.agda
--   and its run is runs/w3-1.out, exit 0 at 2.54 s.
--
--   TWO HEAP WALLS WERE MEASURED ON THIS TASK, runs/s3-1.out and
--   runs/s4-1.out, and section 3 states the law that closed them.  I did
--   not set GHCRTS, the program set `-A64m -I0 -M8g` on this pane, and
--   ONE Agda process ran at a time.
--
--   THE CALIBER MOVED TO `-A64m -I0 -M4g` ON THE OWNER'S RULING OF
--   2026-08-23, AND THE GREEN FILE WAS RE-TAKEN UNDER IT:
--   runs/final-5.out, exit 0, 55.26 s, peak 1,416,495,104 bytes, forced
--   with the interface removed first.  The four walling scratch slices
--   runs/S3.agda, runs/S4.agda, runs/S6.agda and runs/S8.agda are frozen
--   as runs/S*.agda.txt, byte-identical, beside runs/full-probe.txt;
--   their measurements are runs/s4-2.out, runs/s6-2.out and runs/s8-2.out
--   under the new cap and the program's own runs/accept-1.out and
--   runs/accept-2.out for S3.
--
--   Nothing is postulated.  Nothing lands in src/.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-582.Probe582 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure; _↾_ )
open import FOL.Syntax using
  ( Formula; Term; con; var; _∈̇_; _≐_; _∧̇_; ∃̇_; ∀̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∈; δ-∧; δ-∀∈ )
open import FOL.Manipulation.Relabelling using
  ( mapFo; mapFo-comp; embed; mapΔ₀; ⊨-map )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import FOL.Manipulation.Parameters using ( countFo )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; isTransV; Lset; Lset→isL )
open import L.BoundedSubset {ℓ} lem
  using ( module HullStage; erase-Δ₀; module Cnt )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( sucV )
open import Cubical.Data.Vec using ( Vec; map; lookup; _∷_; [] )
open import Cubical.HITs.CumulativeHierarchy.Base using ( setIsSet )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
import Cubical.Data.Empty as Empty

-- THE PREDECESSORS, BY THE TYPE EACH ONE DELIVERED (coder clause, owner
-- 2026-08-20).  [LJ-1.578] is NO-GO on `cohyps-supplied` only
-- (lj-1.578-report.md:18-20); clause (i) is a TYPE in its green module
-- and this file takes that type, not a verdict.  [LJ-1.570] is GO on
-- its own obligation (lj-1.570-report.md:6); `GraphAgree` and
-- `matrix-decode` are taken from it by import.
import LJ-1-570.Probe570 {ℓ} lem as P570
import LJ-1-578.Probe578 {ℓ} lem as P578

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ
open SV using ( _∈ˢ_ )
-- THE CLASS CARRIER'S ABSOLUTENESS AND THE MATRIX ARE TAKEN FROM
-- [LJ-1.570] BY NAME, NOT REBUILT.  `matrix-decode` is stated against
-- that task's own `AbsL` and its own `LH0`, so a private copy here would
-- make the elaborator compare two spellings of the level-hood matrix,
-- and section 3's law says what that costs.
module AbsLL = P570.AbsL
module LH0   = P570.LH0

-- =====================================================================
-- SECTION 1.  W3.  THE WIDEST UNMEASURED TERM, TYPE ONLY.
--
--   The brief: "It is uniqueness, not existence.  `Lset δ is the ONLY
--   witness`, stated alone at the inner world, TYPE ONLY.  Write it
--   FIRST and typecheck it ALONE."
--
--   IT STATES.  runs/W3.agda, exit 0 at 2.54 s (runs/w3-1.out), first
--   attempt.  The type is restated below so this file carries it.
--
--   AND THE BRIEF'S GUESS ABOUT WHICH HALF IS HARD IS REFUTED BY
--   SECTION 7 AGAINST SECTION 8: uniqueness is DISCHARGED here from one
--   named hypothesis that [LJ-1.570] already stated, and existence is
--   not.  The report says so under `## THE FORMULA AND ITS UNIQUENESS`.
-- =====================================================================

module W3 (lam : SV.S) (ordλ : IsOrd lam)
          (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
          (X : SV.S)
          (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
          (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module T  = HS.H.T

  OnlyWitness : (c : T.Code) (φ : Formula T.Code 1) → Type (ℓ-suc ℓ)
  OnlyWitness c φ =
    (a : HS.ASt.SL) → ⟨ (a ∷ []) T.⊨c φ ⟩ → fst a ≡ Lset (fst (T.val c))

-- =====================================================================
-- SECTION 2.  D-10, BEFORE ANY PROOF.  THE FORMULA.
--
--   The brief: "Write that formula and say at `file:line` what it says,
--   before you prove anything about it."
--
--   IT IS DEVLIN'S (b) AND NOTHING MORE (dev/literature/devlin-II5.md:99,
--   "(b) (∀γ < α)(∀v)[v = L_γ ↔ v ∈ L_α ∧ L_α ⊨ ∃z φ(z, v, γ)]").
--   Devlin's `∃z` is TWO existentials here, because the tree's bounded
--   body carries its bound `K` as a slot of its own
--   (src/L/BoundedSubset.lagda.md:69-71).  A third existential supplies
--   the ordinal slot, pinned to the code by an object equation, because
--   `CloseSyntax.close` (src/L/BoundedSubset.lagda.md:534-537) is stated
--   at `K : Type (ℓ-suc ℓ)` and the hull's codes are `Type ℓ`
--   (src/L/Hull.lagda.md:72).
--
--   Written out, at env  v ∷ [] , over the hull's codes:
--
--     levelFo c  =  c is an ordinal
--                ∧  ∃γ ∃K ∃u ( levelHoodB(u, v, γ, K)  ∧  γ = c )
--
--   `levelHoodB` is src/L/BoundedSubset.lagda.md:108-112, the tree's own
--   Δ₀ bounded level-hood body, at env  u ∷ v ∷ γ ∷ K ∷ [] .  Slot 0 is
--   unused there (:69-71); it is the graph's witness slot.
-- =====================================================================

-- [LJ-1.230] WALL (b) IS THE CARRIER CHANGE, and it named this route
-- without running it: "The constant-free erase route (FOL.Count,
-- Cnt.erase) plus embed would bridge it" (lj-1.230-report.md:70-72).
-- THE MATRIX IS CONSTANT-FREE, and `refl` says so.
cf : countFo LH0.matrix ≡ 0
cf = refl

-- The tree's level-hood body with its (zero) constants removed.
ψ4 : Formula (⊥* {ℓ-suc ℓ}) 4
ψ4 = Cnt.erase LH0.matrix cf

Δ₀-ψ4 : Δ₀ ψ4
Δ₀-ψ4 = erase-Δ₀ LH0.matrix cf LH0.Δ₀-matrix

-- "k is an ordinal", about a CONSTANT, at any arity.  No renaming is
-- needed and no binder can capture it, because a constant is stable.
ordOf : ∀ {ℓc} {K : Type ℓc} {n : ℕ} → K → Formula K n
ordOf k =
    (∀̇∈ (con k) (∀̇∈ (var zero) (var zero ∈̇ con k)))
  ∧̇ (∀̇∈ (con k) (∀̇∈ (var zero)
       (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero))))))

Δ₀-ordOf : ∀ {ℓc} {K : Type ℓc} {n : ℕ} (k : K) → Δ₀ (ordOf {n = n} k)
Δ₀-ordOf k = δ-∧ (δ-∀∈ (δ-∀∈ δ-∈)) (δ-∀∈ (δ-∀∈ (δ-∀∈ δ-∈)))

-- The matrix's four slots, read in MY environment  u ∷ K ∷ γ ∷ v ∷ [] .
ρ : Fin 4 → Fin 4
ρ zero                   = zero
ρ (suc zero)             = suc (suc (suc zero))
ρ (suc (suc zero))       = suc (suc zero)
ρ (suc (suc (suc zero))) = suc zero

-- Two maps out of the empty constant domain are equal.  Written with the
-- target named, because `Empty.rec*` alone leaves its result type open
-- and the elaborator then reports an unsolved meta (runs/p-1.out:15-18).
⊥map : ∀ {ℓc} {K : Type ℓc} (f g : ⊥* {ℓ-suc ℓ} → K) → f ≡ g
⊥map f g = funExt (λ b → Empty.rec* b)

-- =====================================================================
-- SECTION 3.  A LAW, MEASURED TWICE ON THIS TASK.
--
--   WRITE THE FORMULA ARGUMENT OF `mapΔ₀` OUT.  Left implicit, the
--   elaborator decides `mapFo ?f ?φ` against
--   `mapFo Empty.rec* (Cnt.erase LH0.matrix cf)` by normalising the
--   level-hood matrix, and that does not fit the 8 GB caliber.
--
--     runs/s6-1.out   `mapΔ₀ Empty.rec* (erase-Δ₀ ...)`   EXIT=251,
--                     182.14 s, 8,980,856,832 bytes, heap exhausted
--     runs/s7-1.out   `mapΔ₀ Empty.rec* {φ = ψ4} Δ₀-ψ4`  EXIT=0,
--                     11.20 s, 810,336,256 bytes
--
--   THE TWO FILES DIFFER IN ONE ARGUMENT.  Sixteen times the seconds and
--   eleven times the resident set.  Every implicit formula argument in
--   this file is written out for that reason, and only that reason.
-- =====================================================================

-- =====================================================================
-- SECTION 4.  THE SIX-SLOT FRAME, AND THE FORMULA AT IT.
-- =====================================================================

module At (lam : SV.S) (ordλ : IsOrd lam)
          (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
          (X : SV.S)
          (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
          (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS  = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module ASt = HS.ASt
  module T   = HS.H.T
  module SatC = Sat (hPropAlgebra (ℓ-suc ℓ)) ASt.AbsL.𝒮M T.val

  -- The matrix at the stage's carrier and at the class carrier.
  matC : Formula T.Code 4
  matC = embed ψ4

  matSL : Formula ASt.SL 4
  matSL = embed ψ4

  matCS : Formula CS.S 4
  matCS = embed ψ4

  Δ₀-matSL : Δ₀ matSL
  Δ₀-matSL = mapΔ₀ Empty.rec* {φ = ψ4} Δ₀-ψ4

  Δ₀-matCS : Δ₀ matCS
  Δ₀-matCS = mapΔ₀ Empty.rec* {φ = ψ4} Δ₀-ψ4

  matCS≡ : matCS ≡ LH0.matrix
  matCS≡ = Cnt.erase-inv LH0.matrix cf

  -- A stage member is a member of L (src/L/Constructible.lagda.md:395).
  up : ASt.SL → CS.S
  up m = fst m , Lset→isL lam ordλ (fst m) (snd m)

  mapVal : mapFo T.val matC ≡ matSL
  mapVal = mapFo-comp Empty.rec* T.val ψ4
         ∙ cong (λ f → mapFo f ψ4) (⊥map (λ b → T.val (Empty.rec* b)) Empty.rec*)

  mapUp : mapFo up matSL ≡ matCS
  mapUp = mapFo-comp Empty.rec* up ψ4
        ∙ cong (λ f → mapFo f ψ4) (⊥map (λ b → up (Empty.rec* b)) Empty.rec*)

  -- THE FORMULA.  Section 2 says what it says.  `Body` is named so that
  -- every intermediate type below can be written out.
  Body : T.Code → Formula T.Code 4
  Body c = renameFo ρ matC ∧̇ (var (suc (suc zero)) ≐ con c)

  levelFo : T.Code → Formula T.Code 1
  levelFo c = ordOf c ∧̇ (∃̇ (∃̇ (∃̇ (Body c))))


  -- ===================================================================
  -- SECTION 5.  THE TRANSFER, NAMED AS A TYPE, AND WHY IT IS NOT A TERM.
  --
  --   The body is Δ₀ and the stage and L are both transitive, so one
  --   satisfaction at the stage IS one satisfaction at the class
  --   carrier.  That is `abs₀` twice with `⊨-map` between them, and I
  --   WROTE IT: agents/tasks/LJ-1-582/runs/S3.agda.txt:120-146,
  --   `lift-matrix`.  IT DOES NOT FIT THE CALIBER, and three runs
  --   measure it, each a two-file difference:
  --
  --     runs/s7-1.out  the two Δ₀ witnesses, no `abs₀`   EXIT=0,   11.20 s
  --     runs/s8-1.out  the same file plus ONE `abs₀`     EXIT=143, 1115.97 s,
  --                    9,379,807,232 bytes, stopped above the 8 GB cap
  --     runs/p-5.out   this file plus `lift-matrix`,     EXIT=143, 457.83 s,
  --                    with both Δ₀ witnesses as VARIABLES, 7,626,506,240 bytes
  --
  --   The third run is the sharp one: making the Δ₀ witnesses variables
  --   does NOT buy the transfer.  What costs is comparing two spellings
  --   of a SATISFACTION of the level-hood matrix, and `_⊨_` is a
  --   recursion over the formula (src/FOL/Semantics.lagda.md:91).
  --
  --   SO THE TRANSFER IS A NAMED HYPOTHESIS HERE.  It is not a new
  --   mathematical gap: it is `abs₀`, delivered at
  --   src/FOL/Absoluteness.lagda.md:122, at a formula the caliber cannot
  --   carry.
  -- ===================================================================

  LiftMatrix : Type (ℓ-suc ℓ)
  LiftMatrix = (u v γ K : ASt.SL)
    → ⟨ (u ∷ v ∷ γ ∷ K ∷ []) ASt.AbsL.⊨ᵐ matSL ⟩
    → ⟨ (up u ∷ up v ∷ up γ ∷ up K ∷ []) AbsLL.⊨ᵐ LH0.matrix ⟩

  -- [LJ-1.230]'s obligation, at today's tree and over the erased matrix
  -- that report could not write (lj-1.230-report.md:64-72, wall (b)):
  -- ONE direction of the level-hood decode, read at the STAGE.
  StageDecode : Type (ℓ-suc ℓ)
  StageDecode = (u v γ K : ASt.SL) → IsOrd (fst γ)
    → ⟨ (u ∷ v ∷ γ ∷ K ∷ []) ASt.AbsL.⊨ᵐ matSL ⟩
    → fst v ≡ Lset (fst γ)

  -- AND THE TWO NAMED HYPOTHESES GIVE IT, through [LJ-1.570]'s own
  -- `matrix-decode` (Probe570.agda:319-322) and nothing else.
  decode-from : P570.GraphAgree → LiftMatrix → StageDecode
  decode-from ga lm u v γ K oγ h =
    P570.matrix-decode ga (up u) (up v) (up γ) (up K) oγ (lm u v γ K h)

  -- ===================================================================
  -- SECTION 6.  THE ORDINAL CONJUNCT, BOTH DIRECTIONS, AS TERMS.
  --
  --   `ordOf` is Devlin's `(∀γ < α)` guard (devlin-II5.md:99), carried
  --   INSIDE the formula rather than as a side hypothesis.  Clause (i)
  --   hands the ordinal-hood of the COLLAPSE IMAGE
  --   `HS.C.π (fst (T.val c))` and not of the code value, so the guard
  --   has to travel in the formula or be assumed.  It travels, and
  --   `abs₀` at THIS formula is five bounded quantifiers and costs
  --   nothing.
  -- ===================================================================

  ordOf-out : (k : ASt.SL) (x : SV.S)
            → ⟨ (x ∷ []) ASt.AbsL.⊨ᵛ (ordOf {n = 1} k) ⟩ → IsOrd (fst k)
  ordOf-out k x h =
      ( λ {p} {q} q∈p p∈k → h .fst p p∈k q q∈p )
    , ( λ p p∈k {q} {r} r∈q q∈p → h .snd p p∈k q q∈p r r∈q )

  ordOf-in : (k : ASt.SL) (x : SV.S)
           → IsOrd (fst k) → ⟨ (x ∷ []) ASt.AbsL.⊨ᵛ (ordOf {n = 1} k) ⟩
  ordOf-in k x o =
      ( λ p p∈k q q∈p → o .fst {p} {q} q∈p p∈k )
    , ( λ p p∈k q q∈p r r∈q → o .snd p p∈k {q} {r} r∈q q∈p )

  ordOf-read : (c : T.Code) (a : ASt.SL)
             → ⟨ (a ∷ []) T.⊨c (ordOf {n = 1} c) ⟩ → IsOrd (fst (T.val c))
  ordOf-read c a h = ordOf-out (T.val c) (fst a) hV
    where
    hM : ⟨ (a ∷ []) ASt.AbsL.⊨ᵐ (ordOf {n = 1} (T.val c)) ⟩
    hM = subst ⟨_⟩
           (sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) ASt.AbsL.𝒮M T.val id
                   (ordOf {n = 1} c) (a ∷ []))) h
    hV : ⟨ (fst a ∷ []) ASt.AbsL.⊨ᵛ (ordOf {n = 1} (T.val c)) ⟩
    hV = subst ⟨_⟩
           (ASt.AbsL.abs₀ {φ = ordOf {n = 1} (T.val c)}
              (Δ₀-ordOf (T.val c)) (a ∷ [])) hM

  ordOf-write : (c : T.Code) (a : ASt.SL)
              → IsOrd (fst (T.val c)) → ⟨ (a ∷ []) T.⊨c (ordOf {n = 1} c) ⟩
  ordOf-write c a o =
    subst ⟨_⟩
      (⊨-map (hPropAlgebra (ℓ-suc ℓ)) ASt.AbsL.𝒮M T.val id
         (ordOf {n = 1} c) (a ∷ [])) hM
    where
    hV : ⟨ (fst a ∷ []) ASt.AbsL.⊨ᵛ (ordOf {n = 1} (T.val c)) ⟩
    hV = ordOf-in (T.val c) (fst a) o
    hM : ⟨ (a ∷ []) ASt.AbsL.⊨ᵐ (ordOf {n = 1} (T.val c)) ⟩
    hM = subst ⟨_⟩
           (sym (ASt.AbsL.abs₀ {φ = ordOf {n = 1} (T.val c)}
                   (Δ₀-ordOf (T.val c)) (a ∷ []))) hV

  -- ===================================================================
  -- SECTION 7.  READING THE GUARD OUT OF THE WHOLE FORMULA.
  -- ===================================================================

  guard-of : (c : T.Code) (a : ASt.SL)
           → ⟨ (a ∷ []) T.⊨c (levelFo c) ⟩ → IsOrd (fst (T.val c))
  guard-of c a h = ordOf-read c a (h .fst)

-- =====================================================================
-- WHAT IS NOT IN THIS FILE, AND WHERE IT IS.
--
--   Sections 8 to 11 of the development, `only-witness` and the clause
--   assembled from it, are WRITTEN and are NOT in this file, because
--   they do not fit the caliber.  They are kept at
--   agents/tasks/LJ-1-582/runs/full-probe.txt, which is the same file
--   with those four sections appended and is NOT typechecked.
--
--   THE MEASUREMENT, on a machine with memory free and my own Agda the
--   only large consumer:
--
--     runs/p-17.out  this file                       EXIT=0,   53.58 s,
--                    1,364,049,920 bytes
--     runs/p-19.out  this file plus sections 8 and 9  EXIT=143, 1140.95 s,
--                    9,690,267,648 bytes, stopped by me above the 8 GB cap
--     runs/p-18.out  this file plus sections 8 to 11  EXIT=143, 1142.60 s,
--                    9,602,056,192 bytes, stopped by me
--
--   The report says which runs are heap exhaustions with Agda's own
--   message, which I stopped, and which the machine killed while another
--   process held its memory.
-- =====================================================================

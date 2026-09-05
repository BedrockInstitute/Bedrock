{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.732] PROBE.  The D-10 probe [LJ-1.727] named: BoundInStage
-- (Probe673.agda:93-95) at the codes of the empty instance.  Lands
-- nothing in src/.
--
--   THE OBLIGATION  bound-in-stage-at-empty.  A green term is GO at
--                   the instance; a machine-checked refutation is
--                   NO-GO (agents/tasks/LJ-1-727/lj-1.727-report.md,
--                   section 7, the named probe).
--   THE TARGET      The recorded prose analysis said the demand fails
--                   at EVERY witness at the empty codes
--                   (review-of-completeness-from-pack.md, the
--                   corrected-target section).  D-10 prices the truth
--                   of a recorded residue before pricing its proof,
--                   so this probe MEASURES that reading instead of
--                   proving on it.
--   THE READING     matrix3 = isOrd-at-p ^ phi3 (Probe667.agda:71-73),
--                   phi3 = twelve exists-in-z wraps around the 520
--                   matrix (runs/W3.agda, `three`).  At the empty
--                   instance the parameter and the value are both
--                   empty, so every extAtB row dies at its first
--                   binder, and the table can be the empty set: the
--                   reading survives at a finite transitive bound
--                   carrying the twelve numerals.  This file checks
--                   that on the machine.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing is postulated.  No hole in the delivered file.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-732.Probe732 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _≐_; _∧̇_; ∃̇_ )
open import FOL.Manipulation.Relabelling using ( mapFo; mapFo-comp; embed )
open import FOL.Manipulation.Parameters using ( countFo )
import FOL.Count
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( IsOrd; Lset )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Vec using ( _∷_; [] )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅ )
open import LJ-1-652.Probe652 {ℓ} lem as P652
open import LJ-1-667.Probe667 {ℓ} lem as P667
import LJ-1-673.Probe673 {ℓ} lem as P673
open import LJ-1-732.runs.Num {ℓ} lem
open import LJ-1-732.runs.Amb1 {ℓ} lem
open import LJ-1-732.runs.Amb2 {ℓ} lem

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- THE FRAME.  [LJ-1.673]'s At telescope (Probe673.agda:57-61), the
-- predecessor's BoundInStage and inBound consumed, not rebuilt (W2).
-- =====================================================================

module At732
  (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : P652.Frame652.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ)
  where

  module A = P673.At lam ordλ succλ X X⊆Lλ ∅∈λ elem
  open A public using ( BoundInStage; inBound )
  open A.F.HS.H.T public
    using ( Code; val; wit; vals; search; Sat )

  lam∈ : (k : ℕ) → ⟨ n k ∈ˢ lam ⟩
  lam∈ zero    = ∅∈λ
  lam∈ (suc k) = succλ (n k) (lam∈ k)

  Z∈Lsetlam : ⟨ n 12 ∈ˢ Lset lam ⟩
  Z∈Lsetlam =
    Lset-cumul (n 12) lam (ordn 12) ordλ (lam∈ 12)
      (ord∈Lset-suc (n 12) (ordn 12))

  -- THE WITNESS BOUND as a stage member.
  wZ : A.F.HS.ASt.SL
  wZ = n 12 , Z∈Lsetlam

  -- -------------------------------------------------------------------
  -- PREMISE 5, MACHINE-CHECKED.  The hull holds such codes.  The junk
  -- code (the Sat search on the falsity row, no witness) values the
  -- empty set on every branch, and the empty set IS Lset ∅ by
  -- extensionality over the no-members fact above.  The implication
  -- is not vacuous.
  -- -------------------------------------------------------------------

  sat⊥ : Sat 0 ⊥̇ (vals []) → Empty.⊥* {ℓ-suc ℓ}
  sat⊥ w = PT.rec Empty.isProp⊥* (λ { (a , ha) → ha }) w

  junk-code : Code
  junk-code = wit 0 ⊥̇ []

  val-junk : fst (val junk-code) ≡ ∅
  val-junk =
    Sum.elim
      {C = λ s' → fst (Sum.rec (search 0 ⊥̇ (vals []))
                          (λ _ → (∅ , A.F.HS.H.∅∈Lsetα)) s') ≡ ∅}
      (λ w → Empty.rec* (sat⊥ w))
      (λ _ → refl)
      (lem (Sat 0 ⊥̇ (vals []) , squash₁))

  codes-exist :
      Σ[ ca ∈ Code ] Σ[ cp ∈ Code ]
        ((fst (val cp) ≡ ∅) × (fst (val ca) ≡ Lset ∅))
  codes-exist =
    junk-code , junk-code , (val-junk , val-junk ∙ ∅≡Lset∅)

  -- -------------------------------------------------------------------
  -- THE BRIDGE.  The AbsL reading of the erased matrix at the coded
  -- triple is the ambient reading at the projected one (AtTrans,
  -- Probe652's Section 1), after the two mapFo compositions that
  -- carry matrix3-Code (mapFo slide matrix3, Probe673) back to the
  -- embedded parameter-free matrix3.
  -- -------------------------------------------------------------------

  conv : mapFo val A.matrix₃-Code ≡ embed P667.matrix₃
  conv =
      mapFo-comp A.slide val P667.matrix₃
    ∙ cong (λ g → mapFo g P667.matrix₃) (funExt (λ b → Empty.rec* b))

  module AT = A.F.AtTrans (Lset lam) A.F.HS.ASt.Ltr

  matrix-conj-from :
      (ca cp : Code) (w : A.F.HS.ASt.SL)
      → ⟨ (fst (val ca) ∷ fst (val cp) ∷ fst w ∷ []) P652.⊨ₚ P667.matrix₃ ⟩
      → ⟨ (val ca ∷ val cp ∷ w ∷ [])
            A.F.HS.ASt.AbsL.⊨ᵐ (mapFo val A.matrix₃-Code) ⟩
  matrix-conj-from ca cp w h = subst ⟨_⟩ (sym step) h
    where
    step :
        (val ca ∷ val cp ∷ w ∷ []) A.F.HS.ASt.AbsL.⊨ᵐ (mapFo val A.matrix₃-Code)
      ≡ ( (fst (val ca) ∷ fst (val cp) ∷ fst w ∷ []) P652.⊨ₚ P667.matrix₃ )
    step =
        cong (λ ψ → (val ca ∷ val cp ∷ w ∷ []) A.F.HS.ASt.AbsL.⊨ᵐ ψ) conv
      ∙ AT.read P667.Δ₀-matrix₃ (val ca ∷ val cp ∷ w ∷ [])

  -- the two equality pins of inBound, read at the coded environment:
  -- the innermost slot is the value, the middle slot the parameter,
  -- the last slot the witness.
  pin-ca : (ca cp : Code) (w : A.F.HS.ASt.SL)
         → ⟨ (val ca ∷ val cp ∷ w ∷ []) A.F.HS.ASt.AbsL.⊨ᵐ
               (var zero ≐ con (val ca)) ⟩
  pin-ca ca cp w = refl

  pin-cp : (ca cp : Code) (w : A.F.HS.ASt.SL)
         → ⟨ (val ca ∷ val cp ∷ w ∷ []) A.F.HS.ASt.AbsL.⊨ᵐ
               (var (suc zero) ≐ con (val cp)) ⟩
  pin-cp ca cp w = refl

  -- -------------------------------------------------------------------
  -- THE OBLIGATION.  GO at the instance: the reading holds, the
  -- witness is Z, and the binder order puts the value innermost, so
  -- the value witness is val ca and the parameter witness val cp.
  -- -------------------------------------------------------------------

  bound-in-stage-at-empty :
      (ca cp : Code)
      → fst (val cp) ≡ ∅
      → fst (val ca) ≡ Lset ∅
      → BoundInStage ca cp
  bound-in-stage-at-empty ca cp e₂ e₁ =
    ∣ wZ ,
      ∣ val cp ,
        ∣ val ca ,
          ( matrix-conj-from ca cp wZ
              ( subst (λ q → ⟨ (q ∷ fst (val cp) ∷ fst wZ ∷ []) P652.⊨ₚ P667.matrix₃ ⟩)
                  (sym e₁)
                  ( subst (λ q → ⟨ (Lset ∅ ∷ q ∷ fst wZ ∷ []) P652.⊨ₚ P667.matrix₃ ⟩)
                      (sym e₂) ambient-matrix ) )
          , pin-ca ca cp wZ
          , pin-cp ca cp wZ ) ∣₁ ∣₁ ∣₁

-- =====================================================================
-- THE EXPORT.  The [LJ-1.727-SPLIT] alias form: the At telescope as
-- leading arguments (Probe727Split.agda:139).
-- =====================================================================

bound-in-stage-at-empty = At732.bound-in-stage-at-empty

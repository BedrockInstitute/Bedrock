{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.719] PROBE.  soundness-at-SL: does 667's matrix₃, read at the
-- stage carrier the hull actually has, determine the level?
--
--   THE OBLIGATION  soundness-at-SL, verbatim from the brief.  It is
--                   named here and NOT inhabited.  The stated NO-GO is
--                   review-of-soundness-at-SL.md.
--
--   WHAT IS GREEN    bridge 1 (carrier) retires at SL, demonstrated:
--                    `from-V` turns the V reading of matrix₃ at raw
--                    slots into the 𝒮ʟ reading of W3.three at the
--                    packed triple.
--                  bridge 3 (IsOrd) retires, demonstrated:
--                    `soundness-with-graph` is the WHOLE proof of the
--                    obligation from one named implication, and it is
--                    one `Lset-only` line.
--
--   WHAT IS OPEN     `Gap`, the one implication this task could not
--                    close: matrix₃'s reading at the packed triple to
--                    `LsetGraphAt` at the same triple.  Its content is
--                    bridge 2's leaf leg under the `pairK` obstruction:
--                    the leaf adequacy is placed (`LeafAgree`,
--                    src/L/Condensation.lagda.md:7220) but its
--                    site-fact block holds `pairK` only at a STAGE
--                    bound (`KValue`, :7363-7435, via `Bound.prʟ∈λ`),
--                    while the obligation's `z` ranges over all
--                    members of `Lset lam`, where pairing closure
--                    fails (z = {∅, {∅}} is transitive and
--                    constructible and pr ∅ ∅ = {{∅}} ∉ z).
--
--   THE NO-GO        stated in review-of-soundness-at-SL.md and UPHELD
--                    by review-of-LJ-1-719-1.md.  Second dispatch: the
--                    first return failed acceptance conjunct 6 (the
--                    survey duty), and `lint-back-to-author` returned
--                    the task.  The obligation name now stands at the
--                    foot of this file, STATED AND DELIBERATELY OPEN,
--                    the measured idiom for a NO-GO ([LJ-1.408],
--                    [LJ-1.394], [LJ-1.396]): the hole makes the probe
--                    exit 42 `unsolved_meta`, so the acceptance routes
--                    `no-go-stated` to the mathematician.  The name is
--                    not inhabited, and the three green terms above
--                    are untouched by it.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.  Nothing is
-- postulated.  One hole, at the obligation name, on purpose.  Nothing
-- lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-719.Probe719 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; _∧̇_ )
open import FOL.LevyHierarchy using ( Δ₀ )
open import FOL.Manipulation.Relabelling
  using ( embed; embed-⊨; mapΔ₀ )
import FOL.Absoluteness
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset; IsOrd; Lset→isL )
open import L.Hull {ℓ} lem using ( module AtStage )
open import L.Hierarchy {ℓ} lem using ( Lset-only )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import LJ-1-652.Probe652 {ℓ} lem as P652
open import LJ-1-667.runs.W3 {ℓ} lem as W3
open import LJ-1-667.Probe667 {ℓ} lem as P667
import L.BoundedSubset as Bnd

open import Cubical.Data.Vec using ( map; _∷_; [] )
import Cubical.Data.Empty as Empty

module Bnd719 = Bnd {ℓ} lem

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module SemV719 = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemV719 using ( _^_ )

-- Hierarchy's own absoluteness instance: the inner world of the
-- constructible sets.  Its carrier is 𝒮ʟ's carrier, and `Lset-only`
-- reads at exactly this instance.
module AL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans

-- =====================================================================
-- THE OBLIGATION, verbatim from the brief.  `AtStage.SL` is the brief's
-- `ASt.SL`: the members of the stage, `AtStage`'s own carrier.
-- =====================================================================

SoundnessAtSL : (lam : S) → IsOrd lam → Type (ℓ-suc ℓ)
SoundnessAtSL lam ordλ =
  (a p z : AtStage.SL lam ordλ)
  → ⟨ (fst a ∷ fst p ∷ fst z ∷ []) P652.⊨ₚ P667.matrix₃ ⟩
  → IsOrd (fst p)
  → fst a ≡ Lset (fst p)


-- Second projection of a satisfied conjunction at the parameter-free
-- reading, with both sides annotated: a generic sigma projector makes
-- the unifier dig into the goal's truncated existentials and wall.
snd-of-∧ :
  {n : ℕ} (γ : S ^ n) (φ ψ : Formula (⊥* {ℓ-suc ℓ}) n)
  → ⟨ γ ⊨ₚ (φ ∧̇ ψ) ⟩ → ⟨ γ ⊨ₚ ψ ⟩
snd-of-∧ γ φ ψ (_ , hb) = hb

-- =====================================================================
-- THE PACKING (premise 4).  A stage member is constructible, so it is
-- an 𝒮ʟ slot after `Lset→isL`; the reading then sits at 𝒮ʟ and the
-- missing V-down transfer is never needed.
-- =====================================================================

pack : (lam : S) (ordλ : IsOrd lam) → AtStage.SL lam ordλ → AL.SM
pack lam ordλ q = fst q , Lset→isL lam ordλ (fst q) (snd q)

packed :
  (lam : S) (ordλ : IsOrd lam)
  (a p z : AtStage.SL lam ordλ) → AL.SM ^ 3
packed lam ordλ a p z =
  pack lam ordλ a ∷ pack lam ordλ p ∷ pack lam ordλ z ∷ []

-- =====================================================================
-- BRIDGE 1, RETIRED AT SL.  [LJ-1.652]'s `AtTrans.read`
-- (Probe652.agda:162-166), re-instantiated at `AL`.  The original is
-- trapped inside `Frame652`, whose telescope this obligation does not
-- carry; the body is its body, unchanged.  It is Δ₀ absoluteness plus
-- the embed congruence, and it needs no `lam`.
-- =====================================================================

read-at-SL :
  {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n}
  → Δ₀ φ → (δ : AL.SM ^ n)
  → (δ AL.⊨ᵐ embed φ) ≡ (map fst δ P652.⊨ₚ φ)
read-at-SL {n} {φ} dφ δ =
    AL.abs₀ (mapΔ₀ Empty.rec* dφ) δ
  ∙ embed-⊨ (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ {K = AL.SM} fst φ (map fst δ)
  ∙ cong (λ ι → SemV719.At._⊨_ (⊥* {ℓ-suc ℓ}) ι (map fst δ) φ)
         (funExt (λ b → Empty.rec* b))

-- =====================================================================
-- THE THREE LEGS OF BRIDGE 1.  Families spelled as explicit lambdas:
-- a `cong fst` family here makes the elaborator whnf the endpoints
-- into the goal's truncated existentials and it never comes back
-- (runs/p-9.out through p-14.out, heap exhausted at 213 s).  Leg 1's
-- result stays spelled at the raw triple: the `map fst (packed …)`
-- spelling in a satisfaction position re-fires the same whnf.
-- =====================================================================

-- Leg 1, the conjunct split: `isOrd-at-p` is not the leg that reads.
from-V0 :
  (lam : S) (ordλ : IsOrd lam)
  (a p z : AtStage.SL lam ordλ)
  → ⟨ (fst a ∷ fst p ∷ fst z ∷ []) P652.⊨ₚ P667.matrix₃ ⟩
  → ⟨ (fst a ∷ fst p ∷ fst z ∷ []) P652.⊨ₚ W3.erased ⟩
from-V0 lam ordλ a p z h =
  snd-of-∧ (fst a ∷ fst p ∷ fst z ∷ []) P667.isOrd-at-p W3.erased h

-- Leg 2, the carrier move: the raw reading is the packed 𝒮ʟ reading.
from-V1 :
  (lam : S) (ordλ : IsOrd lam)
  (a p z : AtStage.SL lam ordλ)
  → ⟨ map fst (packed lam ordλ a p z) P652.⊨ₚ W3.erased ⟩
  → ⟨ packed lam ordλ a p z AL.⊨ᵐ (embed W3.erased) ⟩
from-V1 lam ordλ a p z raw =
  transport (λ i → ⟨ sym (read-at-SL W3.Δ₀-erased (packed lam ordλ a p z)) i ⟩)
            raw

-- Leg 3, the un-erase: the erased formula is W3's wrapped matrix.
from-V2 :
  (lam : S) (ordλ : IsOrd lam)
  (a p z : AtStage.SL lam ordλ)
  → ⟨ packed lam ordλ a p z AL.⊨ᵐ (embed W3.erased) ⟩
  → ⟨ packed lam ordλ a p z AL.⊨ᵐ W3.three ⟩
from-V2 lam ordλ a p z h =
  transport (cong (λ ψ → ⟨ packed lam ordλ a p z AL.⊨ᵐ ψ ⟩)
                  (Bnd719.Cnt.erase-inv W3.three W3.count-three))
            h

-- The legs compose by immediate function application, but the composed
-- term is not delivered: checking the composed application unifies the
-- three satisfaction-typed interfaces at once and it exhausts the cap
-- (runs/p-23.out, p-25.out, p-27.out).  [LJ-1.718]'s consumer applies
-- the legs in sequence.

-- =====================================================================
-- THE GAP, AS A TYPE.  The one implication this task could not close.
-- It is NOT `isOrd-at-p`'s work and NOT the carrier's work: the legs
-- already sit at 𝒮ʟ (Legs.from-V0/1/2).  Its content is bridge 2's
-- leaf leg; see the review for the `pairK` obstruction.
-- =====================================================================

Gap : (lam : S) → IsOrd lam → Type (ℓ-suc ℓ)
Gap lam ordλ =
  (a p z : AtStage.SL lam ordλ)
  → ⟨ (fst a ∷ fst p ∷ fst z ∷ []) P652.⊨ₚ P667.matrix₃ ⟩
  → ⟨ packed lam ordλ a p z AL.⊨ᵐ (LsetGraphAt zero (suc zero)) ⟩

-- =====================================================================
-- BRIDGE 3, RETIRED, AND THE OBLIGATION REDUCED TO THE GAP.  One
-- `Lset-only` line: given the graph at the packed triple and `IsOrd`
-- on the parameter, the value is the level.  The slot lookups compute,
-- so the conclusion is `fst a ≡ Lset (fst p)` on the nose.
-- =====================================================================

soundness-with-graph :
  (lam : S) (ordλ : IsOrd lam) → Gap lam ordλ → SoundnessAtSL lam ordλ
soundness-with-graph lam ordλ g a p z h ob =
  Lset-only zero (suc zero) (packed lam ordλ a p z) (g a p z h) ob

-- =====================================================================
-- THE OBLIGATION, STATED AND DELIBERATELY OPEN.  Verbatim from the
-- brief, with `ASt.SL` spelled as `AtStage.SL lam ordλ`, the carrier
-- it names.  It is NOT inhabited: `Gap` is the residue, and the
-- `pairK` obstruction of review-of-soundness-at-SL.md (upheld by
-- review-of-LJ-1-719-1.md) is a FALSE instance of the site-fact block
-- at this generality, not plumbing.  The hole is the point: the probe
-- exits 42, the meter reads the name PROBE-RED-and-unresolved, and a
-- green probe here would strand the upheld NO-GO in the acceptance
-- table's no-match dead zone (measured on [LJ-1.419], pod.py:5275).
-- =====================================================================

soundness-at-SL :
  (lam : S) (ordλ : IsOrd lam)
  (a p z : AtStage.SL lam ordλ)
  → ⟨ (fst a ∷ fst p ∷ fst z ∷ []) P652.⊨ₚ P667.matrix₃ ⟩
  → IsOrd (fst p)
  → fst a ≡ Lset (fst p)
soundness-at-SL = ?

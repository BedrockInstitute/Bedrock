{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.686] PROBE.  The leftover equation
--   mapFo val (mapFo slide φ) ≡ embed φ
-- by mapFo-comp and uniqueness of maps out of ⊥*.  Lands nothing
-- in src/.
--
--   W3              the induction itself, at matrix₃
--                   (agents/tasks/LJ-1-680/lj-1.680-report.md:146-153).
--   THE OBLIGATION  slide-embed-eq.  Generic lemma instantiated at
--                   the delivered matrix₃.  val and slide are
--                   parameters, not the hull telescope.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing is postulated.  No hole.

open import Base.Prelude
open import Base.Classical using ( LEM )

module LJ-1-686.Probe686 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Relabelling using ( embed; mapFo; mapFo-comp )
import Cubical.Data.Empty as Empty
open import LJ-1-667.Probe667 {ℓ} lem as P667
open P667 using ( matrix₃ )

-- W2: written once at a generic carrier and a generic
-- parameter-free formula.  embed-map (Probe652.agda:56-61) is the
-- same uniqueness after embed.  This file does not import
-- Probe652: that module takes LEM and pulls the hull telescope.

lemma : {ℓc ℓd : Level} {K : Type ℓc} {K' : Type ℓd} {n : ℕ}
        (φ : Formula (⊥* {ℓ-suc ℓ}) n)
        (slide : ⊥* {ℓ-suc ℓ} → K)
        (val : K → K')
      → mapFo val (mapFo slide φ) ≡ embed φ
lemma φ slide val =
    mapFo-comp slide val φ
  ∙ cong (λ h → mapFo h φ) (funExt (λ b → Empty.rec* b))

-- THE OBLIGATION.  Instance at the delivered matrix₃.  val and
-- slide stay parameters, so the hull telescope does not leak into
-- this type.  Lifted off the carrier module so the witness meter
-- reads Target.slide-embed-eq (scripts/pod/witness.py:278).

module At {ℓc ℓd : Level} {K : Type ℓc} {K' : Type ℓd}
  (slide : ⊥* {ℓ-suc ℓ} → K)
  (val : K → K') where

  slide-embed-eq : mapFo val (mapFo slide matrix₃) ≡ embed matrix₃
  slide-embed-eq = lemma matrix₃ slide val

slide-embed-eq = At.slide-embed-eq

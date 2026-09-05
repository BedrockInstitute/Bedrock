{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.161 probe A.  THE TRANSFER HALF OF `CrossOut`, MEASURED.
--
-- [LJ-1.160] named this obligation and fixed its criterion in advance:
--   instantiate `FOL.Absoluteness.Single` at the collapse image `C.πX`
--   and supply `TransferM` for ONE delivered `Σ₁` certificate, namely
--   `Σ₁-cert` (src/L/Condensation.lagda.md:269-270).
--   GO at or below 60 in-fence lines for that ONE transfer.
--
-- `TransferM` is the archive's name for "the inner reading implies the
-- ambient reading of the transported formula", at a transitive set
-- carrier: archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:291-293.
--
-- C-38 GUARD.  Nothing here is abstract.  `Σ₁-cert` is CONSUMED, not
-- restated, and `existCertAt` is the delivered formula, not a stand-in.
--
-- BLOCK 1 is the gated block.  BLOCK 2 shows the moved formula still
-- MEANS the delivered one.  BLOCK 3 is not gated: it shows the same
-- block carries the delivered LEVEL-HOOD certificate, which is what
-- `CrossOut` actually consumes.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-161.ProbeLJ1161A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ∃̇_ )
open import FOL.LevyHierarchy using ( Σ₁; σ-Δ₀; σ-∃ )
open import FOL.Manipulation.Parameters using ( countFo )
open import FOL.Manipulation.Relabelling using ( mapFo; mapΔ₀; embed; ⊨-map )
import FOL.Count
import FOL.Absoluteness
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Collapse {ℓ} using ( isTrans; module Collapse )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Condensation {ℓ} lem using ( existCertAt; Σ₁-cert; module AbsL )
open import L.BoundedSubset {ℓ} lem using ( erase-Δ₀; module LevelHood )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( map )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- the class carrier the delivered certificate lives at, and its erase
module CS = hPropStructure 𝒮ʟ
module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} CS.S
module SemV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemV using ( _^_ )

-- =====================================================================
-- BLOCK 1 BEGINS.  THE GATED BLOCK.
-- =====================================================================

-- `Σ₁` travels with a relabelling.  `mapΔ₀` and `mapΣₙ` are delivered
-- (src/FOL/Manipulation/Relabelling.lagda.md:209, :232); `Σ₁` is its
-- own datatype and the tree gives it no map.
mapΣ₁ : ∀ {ℓc ℓd} {K : Type ℓc} {K' : Type ℓd} (f : K → K')
        {n} {φ : Formula K n} → Σ₁ φ → Σ₁ (mapFo f φ)
mapΣ₁ f (σ-Δ₀ d) = σ-Δ₀ (mapΔ₀ f d)
mapΣ₁ f (σ-∃ s)  = σ-∃ (mapΣ₁ f s)

-- `Σ₁` reaches the parameter-free axis.  `erase-Δ₀` is delivered
-- (src/L/BoundedSubset.lagda.md:825); `Σ₁` recurses to it.
erase-Σ₁ : {m : ℕ} (φ : Formula CS.S m) (p : countFo φ ≡ 0)
         → Σ₁ φ → Σ₁ (Cnt.erase φ p)
erase-Σ₁ φ p (σ-Δ₀ d)    = σ-Δ₀ (erase-Δ₀ φ p d)
erase-Σ₁ (∃̇ φ) p (σ-∃ s) = σ-∃ (erase-Σ₁ φ p s)

module AtImage (P : S) (Ptr : isTrans P) where

  module Abs = FOL.Absoluteness.Single 𝒮ᵥ (λ x → x ∈ˢ P) Ptr

  -- a parameter-free formula of the class carrier, AT the image
  at : {m : ℕ} (φ : Formula CS.S m) (p : countFo φ ≡ 0) → Formula Abs.SM m
  at φ p = embed (Cnt.erase φ p)

  -- TransferM at the image, generic in the certificate (DD4)
  transfer : {m : ℕ} (φ : Formula CS.S m) (p : countFo φ ≡ 0) → Σ₁ φ
           → (γ : Abs.SM Abs.^ m)
           → ⟨ γ Abs.⊨ᵐ at φ p ⟩ → ⟨ map fst γ Abs.⊨ᵛ at φ p ⟩
  transfer φ p s = Abs.σ₁-up (mapΣ₁ Empty.rec* (erase-Σ₁ φ p s))

  -- C-38: the instance at the REAL delivered certificate
  cert-transfer : ∀ {n} (C T B N : Fin n) (γ : Abs.SM Abs.^ n)
                → ⟨ γ Abs.⊨ᵐ at (existCertAt C T B N) refl ⟩
                → ⟨ map fst γ Abs.⊨ᵛ at (existCertAt C T B N) refl ⟩
  cert-transfer C T B N = transfer (existCertAt C T B N) refl (Σ₁-cert C T B N)

-- =====================================================================
-- BLOCK 1 ENDS.
-- =====================================================================

-- The site match: the image is `C.πX`, its transitivity is delivered
-- (src/V/Collapse.lagda.md:89), so block 1 applies at the real site
-- with no hypothesis left open.
module AtSite (M : S) where

  module C = Collapse M

  imageTrans : isTrans C.πX
  imageTrans = C.πX-trans

  module Image = AtImage C.πX imageTrans

-- ---------------------------------------------------------------------
-- BLOCK 2 BEGINS.  The moved formula MEANS the delivered one.  The
-- archive priced this separately, as `Transport.amb-agree`
-- (archive/.../L/Condensation.lagda.md:283-287).  Without it the
-- transfer above could be about a different sentence.
-- ---------------------------------------------------------------------

-- the reading of a parameter-free formula, with the interpretation loose
⊨₀ : (⊥* {ℓ-suc ℓ} → S) → ∀ {n} → S ^ n → Formula (⊥* {ℓ-suc ℓ}) n → Ω
⊨₀ ι = SemV.At._⊨_ (⊥* {ℓ-suc ℓ}) ι

module Agreement (P : S) (Ptr : isTrans P) where

  module I = AtImage P Ptr

  ιP : I.Abs.SM → S
  ιP = fst

  ιL : CS.S → S
  ιL = fst

  ι-eq : (λ (b : ⊥* {ℓ-suc ℓ}) → ιP (Empty.rec* b))
       ≡ (λ (b : ⊥* {ℓ-suc ℓ}) → ιL (Empty.rec* b))
  ι-eq = funExt (λ b → Empty.rec* b)

  ambient-agrees : {m : ℕ} (φ : Formula CS.S m) (p : countFo φ ≡ 0) (γ : S ^ m)
                 → (γ I.Abs.⊨ᵛ I.at φ p) ≡ (γ AbsL.⊨ᵛ φ)
  ambient-agrees φ p γ =
      ⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ Empty.rec* ιP (Cnt.erase φ p) γ
    ∙ cong (λ ι → ⊨₀ ι γ (Cnt.erase φ p)) ι-eq
    ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ Empty.rec* ιL (Cnt.erase φ p) γ)
    ∙ cong (λ ψ → γ AbsL.⊨ᵛ ψ) (Cnt.erase-inv φ p)

-- ---------------------------------------------------------------------
-- BLOCK 2 ENDS.
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- BLOCK 3, NOT GATED.  What `CrossOut` actually consumes is the
-- LEVEL-HOOD certificate, not one satisfaction row.  The tree delivers
-- it: `LevelHood.Σ₁-levelHood` (src/L/BoundedSubset.lagda.md:145-146)
-- is Devlin's "∃v∃z φ(z, v, γ)" (dev/literature/devlin-II5.md:102-106).
-- Block 1 is generic, so it takes that certificate unchanged.
-- ---------------------------------------------------------------------

-- WALL, MEASURED 2026-08-14.  Block 3 ran 20 minutes of wall time under
-- GHCRTS="-A64m -I0 -M8g", one agda process, resident set pinned at
-- 9.03 GB, and it did not finish.  The criterion was fixed at 20 minutes
-- BEFORE the run, in the report's section 1.4.  I terminated it (SIGTERM,
-- exit 143).  There was NO heap exhaustion: the cap held and the cap was
-- never raised.
--
-- WHAT WALLS, exactly: `refl : countFo LH.levelHoodΣ₁ ≡ 0`.  Block 1 is
-- generic and takes any parameter-free Σ₁ certificate, but the proof that
-- THIS formula is parameter-free forces `countFo` over a graph that nests
-- the twelve-row bounded table twice (LevelHood's two DefBodyB arguments,
-- src/L/BoundedSubset.lagda.md:81-105).  The tree already knows this cost
-- and works around it: src/L/Condensation/README.md:1-3 splits the twelve
-- rows across three masters "so no single Agda process elaborates all
-- twelve rows".
--
-- The block is kept, not deleted, so the next agent reproduces it in one
-- step.  Uncomment and run.  Do NOT raise the cap.
--
-- module AtLevelHood (P : S) (Ptr : isTrans P) {n : ℕ}
--   (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
--   (M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1 : Fin (7 + n)) where
--
--   module I = AtImage P Ptr
--   module LH = LevelHood {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
--                              M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1
--
--   levelhood-transfer : (γ : I.Abs.SM I.Abs.^ (suc (suc (suc n))))
--     → ⟨ γ I.Abs.⊨ᵐ I.at LH.levelHoodΣ₁ refl ⟩
--     → ⟨ map fst γ I.Abs.⊨ᵛ I.at LH.levelHoodΣ₁ refl ⟩
--   levelhood-transfer = I.transfer LH.levelHoodΣ₁ refl LH.Σ₁-levelHood

-- ---------------------------------------------------------------------
-- BLOCK 3 ENDS.
-- ---------------------------------------------------------------------

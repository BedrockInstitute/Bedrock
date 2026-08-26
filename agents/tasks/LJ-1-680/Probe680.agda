{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.680] PROBE.  Convert as a GENERIC unpack at a 3-slot Δ₀
-- formula, not as a substitution into one matrix's ambient reading.
-- Lands nothing in src/.
--
--   W3              whether the generic unpack elaborates where
--                   [LJ-1.673]'s substitution into matrix₃ did not
--                   (agents/tasks/LJ-1-673/runs/p-4.out).
--   THE OBLIGATION  convert-generic.  Two ∃̇ and two ≐ unpacked at
--                   a generic transitive carrier, then abs₀ at a
--                   generic 3-slot Δ₀ formula.  φ is a variable.
--                   Nothing here names matrix₃.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing is postulated.  No hole.

open import Base.Prelude
open import Base.Truth

module LJ-1-680.Probe680 {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _≐_; _∧̇_; ∃̇_; ⊤̇ )
open import FOL.LevyHierarchy using ( Δ₀; δ-⊤ )
open import FOL.Manipulation.Relabelling using ( embed; embed-⊨; mapΔ₀; mapFo )
import FOL.Semantics
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Collapse {ℓ} using ( isTrans )
open import Cubical.Data.Vec using ( map; _∷_; [] )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module SemVᵃ = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemVᵃ using ( _^_ )
module AtP = SemVᵃ.At (⊥* {ℓ-suc ℓ}) (λ b → Empty.rec* b)

_⊨ₚ_ : {n : ℕ} → S ^ n → Formula (⊥* {ℓ-suc ℓ}) n → hProp (ℓ-suc ℓ)
_⊨ₚ_ = AtP._⊨_

-- Two ∃̇ bind value then parameter; two ≐ pin those binders to
-- constants; the remaining free slot is the witness.  This is
-- inBound (Probe673.agda:83-87) at a generic formula and a generic
-- constant domain, so mapFo f (pin₃ φ ca cp) is pin₃ (mapFo f φ)
-- (f ca) (f cp) by refl and never inducts on φ.
pin₃ : {ℓc : Level} {K : Type ℓc} → Formula K 3 → K → K → Formula K 1
pin₃ φ ca cp =
  ∃̇ (∃̇ (φ ∧̇ (var zero ≐ con ca) ∧̇ (var (suc zero) ≐ con cp)))

pin₃-map : {ℓc ℓd : Level} {K : Type ℓc} {K' : Type ℓd}
           (f : K → K') (φ : Formula K 3) (ca cp : K)
         → mapFo f (pin₃ φ ca cp) ≡ pin₃ (mapFo f φ) (f ca) (f cp)
pin₃-map f φ ca cp = refl

-- =====================================================================
-- THE UNPACK, AT A GENERIC TRANSITIVE CARRIER.  W2: written once.
-- AtTrans.read (Probe652.agda:118-124) is the Δ₀ half and lives
-- inside Frame652, so a hull telescope would leak into this type.
-- `read` below is that four-line body at the carrier it needs.
-- =====================================================================

module Unpack (U : S) (Utr : isTrans U) where

  module Ab = FOL.Absoluteness.Single 𝒮ᵥ (λ x → x ∈ˢ U) Utr

  -- Inner Δ₀ reading of an embedded parameter-free formula is the
  -- ambient parameter-free reading.  Does not use elem.
  read : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : Ab.SM ^ n)
       → (δ Ab.⊨ᵐ embed φ) ≡ (map fst δ ⊨ₚ φ)
  read {n} {φ} dφ δ =
      Ab.abs₀ (mapΔ₀ Empty.rec* dφ) δ
    ∙ embed-⊨ (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ {K = Ab.SM} fst φ (map fst δ)
    ∙ cong (λ ι → SemVᵃ.At._⊨_ (⊥* {ℓ-suc ℓ}) ι (map fst δ) φ)
           (funExt (λ b → Empty.rec* b))

  -- Unpack of two ∃̇ and two ≐.  Δ₀ is not used.  φ is a variable.
  -- The ≐ conjuncts are path equalities on the first projections, so
  -- `read` fires at the unpacked witnesses and the ambient environment
  -- is adjusted by subst, never by Σ-equality on SM.
  unpack-pin :
      (φ : Formula Ab.SM 3)
    → (ca cp a : Ab.SM)
    → ⟨ (a ∷ []) Ab.⊨ᵐ (pin₃ φ ca cp) ⟩
    → ∥ Σ[ y ∈ Ab.SM ] Σ[ x ∈ Ab.SM ]
         ( ⟨ (y ∷ x ∷ a ∷ []) Ab.⊨ᵐ φ ⟩
         × (fst y ≡ fst ca)
         × (fst x ≡ fst cp) ) ∥₁
  unpack-pin φ ca cp a h =
    PT.rec squash₁ outer h
    where
    outer : Σ[ x ∈ Ab.SM ]
              ⟨ (x ∷ a ∷ []) Ab.⊨ᵐ
                  (∃̇ (φ ∧̇ (var zero ≐ con ca)
                         ∧̇ (var (suc zero) ≐ con cp))) ⟩
          → ∥ Σ[ y ∈ Ab.SM ] Σ[ x ∈ Ab.SM ]
               ( ⟨ (y ∷ x ∷ a ∷ []) Ab.⊨ᵐ φ ⟩
               × (fst y ≡ fst ca)
               × (fst x ≡ fst cp) ) ∥₁
    outer (x , hx) =
      PT.rec squash₁ inner hx
      where
      inner : Σ[ y ∈ Ab.SM ]
                ⟨ (y ∷ x ∷ a ∷ []) Ab.⊨ᵐ
                    (φ ∧̇ (var zero ≐ con ca)
                       ∧̇ (var (suc zero) ≐ con cp)) ⟩
            → ∥ Σ[ y ∈ Ab.SM ] Σ[ x ∈ Ab.SM ]
                 ( ⟨ (y ∷ x ∷ a ∷ []) Ab.⊨ᵐ φ ⟩
                 × (fst y ≡ fst ca)
                 × (fst x ≡ fst cp) ) ∥₁
      inner (y , hy) = ∣ y , x , hy .fst , hy .snd .fst , hy .snd .snd ∣₁

  convert-generic :
      {φ : Formula (⊥* {ℓ-suc ℓ}) 3}
    → Δ₀ φ
    → (ca cp a : Ab.SM)
    → ⟨ (a ∷ []) Ab.⊨ᵐ (pin₃ (embed φ) ca cp) ⟩
    → ⟨ (fst ca ∷ fst cp ∷ fst a ∷ []) ⊨ₚ φ ⟩
  convert-generic {φ} dφ ca cp a h =
    PT.rec (snd ((fst ca ∷ fst cp ∷ fst a ∷ []) ⊨ₚ φ)) go
           (unpack-pin (embed φ) ca cp a h)
    where
    go : Σ[ y ∈ Ab.SM ] Σ[ x ∈ Ab.SM ]
           ( ⟨ (y ∷ x ∷ a ∷ []) Ab.⊨ᵐ embed φ ⟩
           × (fst y ≡ fst ca)
           × (fst x ≡ fst cp) )
       → ⟨ (fst ca ∷ fst cp ∷ fst a ∷ []) ⊨ₚ φ ⟩
    go (y , x , hφ , ey , ex) =
      subst (λ v → ⟨ (v ∷ fst cp ∷ fst a ∷ []) ⊨ₚ φ ⟩) ey
        (subst (λ p → ⟨ (fst y ∷ p ∷ fst a ∷ []) ⊨ₚ φ ⟩) ex
          (subst ⟨_⟩ (read dφ (y ∷ x ∷ a ∷ [])) hφ))

  -- Smallest concrete Δ₀ formula of arity 3.  Forces the unpack at
  -- ⊤̇ and does not name matrix₃.
  convert-at-true = convert-generic {φ = ⊤̇} δ-⊤

-- THE OBLIGATION.  Lifted off the carrier module so the witness
-- meter reads Target.convert-generic (scripts/pod/witness.py:278).
convert-generic = Unpack.convert-generic
convert-at-true = Unpack.convert-at-true

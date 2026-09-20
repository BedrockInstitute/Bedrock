{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track B, seam check against Track A. Ledger clause L10 says a
-- cross-track parameter is typed verbatim from the producing export so that a
-- drift FAILS in the consuming probe instead of passing silently. This file
-- is that probe, and it is the whole of it.
--
-- For each of the nine parameters that K5.Clauses.Core takes from Track A, it
-- declares an alias WHOSE TYPE IS TRACK B'S PARAMETER TYPE, character for
-- character as K5/Clauses.agda writes it, and WHOSE BODY IS TRACK A'S EXPORT.
-- If any type had drifted, the alias would not elaborate. Nothing else is
-- claimed here: the compiler side of Core's telescope (val, eqᴬ, memᴬ and the
-- fourteen laws) is Track I's to supply and is untouched.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import K4.Algebra
import K5.Frame
import K5.Clauses

module K5.ClausesAtFrame
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (carrier order : ZFStructure.S 𝒮)
  (B : ZFStructure.S 𝒮)
  (L : K4.Algebra.Lattice 𝒮 B)
  (Cm : K4.Algebra.Complement 𝒮 B L)
  (Kc : K4.Algebra.CodedComplete 𝒮 B L)
  (fb : K5.Frame.Poset.ForcingBase 𝒮 carrier order B L Cm)
  (IsNameᴮ : ZFStructure.S 𝒮 → hProp ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open K4.Algebra 𝒮 using ( Pt; _≤ᴮ_ )
open K4.Algebra.Lattice L using ( _⊓ᴮ_; ⊥ᴮ )

module FP = K5.Frame.Poset 𝒮 carrier order
module FF = FP.Forcing ext paths B L Cm Kc fb
open K5.Frame.Poset.ForcingBase fb using ( i; ≼-refl; ≼-trans )

module CL = K5.Clauses 𝒮 ext paths B L Cm carrier FP._≼ᶜ_ IsNameᴮ

-- 1. the embedding

seam-i : CL.Cond → Pt B
seam-i = i

-- 2 and 3. the sealed relation and its specification

seam-⊩ᴮ : CL.Cond → Pt B → Ω
seam-⊩ᴮ = FF._⊩ᴮ_

seam-⊩ᴮ-spec : (p : CL.Cond) (b : Pt B) → (seam-⊩ᴮ p b) ≡ (seam-i p ≤ᴮ b)
seam-⊩ᴮ-spec = FF.⊩ᴮ-spec

-- 4 and 5. the two order laws, taken out of the record

seam-≼-refl : (p : S) → ⟨ p ∈ˢ carrier ⟩ → ⟨ FP._≼ᶜ_ p p ⟩
seam-≼-refl = ≼-refl

seam-≼-trans : (r q p : S) → ⟨ r ∈ˢ carrier ⟩ → ⟨ q ∈ˢ carrier ⟩
             → ⟨ p ∈ˢ carrier ⟩
             → ⟨ FP._≼ᶜ_ r q ⟩ → ⟨ FP._≼ᶜ_ q p ⟩ → ⟨ FP._≼ᶜ_ r p ⟩
seam-≼-trans = ≼-trans

-- 6 to 9. the four direct poset lemmas Track B consumes, plus the one
-- classical-free extension lemma. Note that CL.DenseBelow and FF.DenseBelow
-- are two separately written definitions and each alias forces them to agree.

seam-⊩ᴮ-mono : (p q : CL.Cond) (b : Pt B)
             → ⟨ FP._≼ᶜ_ (fst q) (fst p) ⟩ → ⟨ seam-⊩ᴮ p b ⟩ → ⟨ seam-⊩ᴮ q b ⟩
seam-⊩ᴮ-mono = FF.⊩ᴮ-mono

seam-⊩ᴮ-down : (p : CL.Cond) (b : Pt B)
             → ⟨ seam-⊩ᴮ p b ⟩
             → ⟨ CL.DenseBelow p (λ r → seam-⊩ᴮ r b) ⟩
seam-⊩ᴮ-down = FF.⊩ᴮ-down

seam-⊩ᴮ-reg : (p : CL.Cond) (b : Pt B)
            → ⟨ CL.DenseBelow p (λ r → seam-⊩ᴮ r b) ⟩
            → ⟨ seam-⊩ᴮ p b ⟩
seam-⊩ᴮ-reg = FF.⊩ᴮ-reg

seam-⊩ᴮ-⊥ : (p : CL.Cond) → ⟨ seam-⊩ᴮ p ⊥ᴮ ⟩ → ⟨ ⊥ ⟩
seam-⊩ᴮ-⊥ = FF.⊩ᴮ-⊥

seam-⊩ᴮ-extend : (q : CL.Cond) (b : Pt B)
               → (((seam-i q ⊓ᴮ b) ≡ ⊥ᴮ) → ⟨ ⊥ ⟩)
               → ⟨ ⋁ CL.Cond (λ r → (FP._≼ᶜ_ (fst r) (fst q)) ⊓ (seam-⊩ᴮ r b)) ⟩
seam-⊩ᴮ-extend = FF.⊩ᴮ-extend

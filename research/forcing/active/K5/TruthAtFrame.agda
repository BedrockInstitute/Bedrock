{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track G, seam check against Tracks A, B, C and D. Ledger clause L10 says
-- a cross-track parameter is typed verbatim from the producing export so that
-- a drift FAILS in the consuming probe instead of passing silently. This file
-- is that probe, and it does more than declare aliases: it APPLIES K5.Truth's
-- Generic layer with every parameter filled from a landed track.
--
--   Track A  the frame, the sealed relation and the six poset lemmas
--   Track B  _⊩_[_] and ⊩-spec, the two free exports Track G takes
--   Track C  witnessAt with its two readings, its density below a condition,
--            and generic-meets-denseBelow
--   Track D  Uof with its filter laws and its ultrafilter clause
--
-- If any of the parameters had drifted the application would not elaborate.
--
-- WHAT STAYS A PARAMETER HERE, each with its owner:
--
--  * the compiler surface, eqᴬ, memᴬ, val and the fourteen laws: Track I's,
--    typed verbatim from Compile.agda:1318-1357;
--  * cob and boc, which are DECISION D1 and are not theorems about an
--    abstract frame. Track A measured them at the coded completion in
--    K5/ProbeD1.agda, where below := fst makes both the identity;
--  * the generic G with its filter and genericity hypotheses;
--  * the satisfaction surface and the two atomic bridges, which belong to the
--    Sat layer and are not applied here.
--
-- TWO CHECKS THAT ARE NOT TYPE CHECKS. Uof-of and Uof-to are filled by the
-- IDENTITY. That is what pins Track D's Uof G b to
-- ⋁ Cond (λ p → (p ∈ᴾ G) ⊓ (p ⊩ᴮ b)) and not merely to some subset with the
-- same four laws; if Track D had sealed it or defined it otherwise the two
-- identities would not elaborate.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax
import OrdinaryProfile
import K4.Algebra
import K4.Implication
import K5.Frame
import K5.Clauses
import K5.Dense
import K5.Generic
import K5.Truth

module K5.TruthAtFrame
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (sep : OrdinaryProfile.Separation 𝒮)
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
open K4.Implication 𝒮 ext paths B L Cm using ( _⊓ᴮ_; _⊔ᴮ_; _⇒ᴮ_; ⊥ᴮ )

module FP = K5.Frame.Poset 𝒮 carrier order
module FF = FP.Forcing ext paths B L Cm Kc fb
module FB = K5.Frame.Poset.ForcingBase fb

module C  = K5.Dense 𝒮 ext paths sep carrier order B L Cm Kc fb
module GP = K5.Generic.Poset 𝒮 carrier order
module GI = GP.Image ext paths B L Cm Kc fb

Src : ℕ → Type ℓ
Src k = Formula (⊥* {ℓ}) k

Nameᴮ : Type ℓ
Nameᴮ = Σ[ x ∈ S ] ⟨ IsNameᴮ x ⟩

Envᴮ : ℕ → Type ℓ
Envᴮ k = Vec Nameᴮ k

module Seam
  (G : GI.FS.Sub)
  (fil : GI.FS.isFilter G)
  (meets : C.MeetsAll G)
  -- decision D1, the two entailments, Track I's to discharge
  (cob : C.CodeOfBelow)
  (boc : C.BelowOfCode)
  -- Track I's compiler surface, Compile.agda:1318-1357
  (eqᴬ memᴬ : S → S → Pt B)
  (val : ∀ {k} → Src k → Envᴮ k → Pt B)
  (law-∈ : ∀ {k} (a b : Fin k) (ν : Envᴮ k)
         → val (var a ∈̇ var b) ν ≡ memᴬ (fst (lookup a ν)) (fst (lookup b ν)))
  (law-≐ : ∀ {k} (a b : Fin k) (ν : Envᴮ k)
         → val (var a ≐ var b) ν ≡ eqᴬ (fst (lookup a ν)) (fst (lookup b ν)))
  (law-∧ : ∀ {k} (φ ψ : Src k) (ν : Envᴮ k)
         → val (φ ∧̇ ψ) ν ≡ (val φ ν ⊓ᴮ val ψ ν))
  (law-∨ : ∀ {k} (φ ψ : Src k) (ν : Envᴮ k)
         → val (φ ∨̇ ψ) ν ≡ (val φ ν ⊔ᴮ val ψ ν))
  (law-⇒ : ∀ {k} (φ ψ : Src k) (ν : Envᴮ k)
         → val (φ ⇒̇ ψ) ν ≡ (val φ ν ⇒ᴮ val ψ ν))
  (law-⊥ : ∀ {k} (ν : Envᴮ k) → val {k} ⊥̇ ν ≡ ⊥ᴮ)
  (law-∃-ub   : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k) (σ : Nameᴮ)
              → ⟨ val φ (σ ∷ ν) ≤ᴮ val (∃̇ φ) ν ⟩)
  (law-∃-lub  : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k) (c : Pt B)
              → ((σ : Nameᴮ) → ⟨ val φ (σ ∷ ν) ≤ᴮ c ⟩)
              → ⟨ val (∃̇ φ) ν ≤ᴮ c ⟩)
  (law-∀-lb   : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k) (σ : Nameᴮ)
              → ⟨ val (∀̇ φ) ν ≤ᴮ val φ (σ ∷ ν) ⟩)
  (law-∀-glb  : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k) (c : Pt B)
              → ((σ : Nameᴮ) → ⟨ c ≤ᴮ val φ (σ ∷ ν) ⟩)
              → ⟨ c ≤ᴮ val (∀̇ φ) ν ⟩)
  (law-∃∈-ub  : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Envᴮ k) (σ : Nameᴮ)
              → ⟨ (memᴬ (fst σ) (fst (lookup j ν)) ⊓ᴮ val φ (σ ∷ ν))
                  ≤ᴮ val (∃̇∈ (var j) φ) ν ⟩)
  (law-∃∈-lub : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Envᴮ k) (c : Pt B)
              → ((σ : Nameᴮ)
                 → ⟨ (memᴬ (fst σ) (fst (lookup j ν)) ⊓ᴮ val φ (σ ∷ ν)) ≤ᴮ c ⟩)
              → ⟨ val (∃̇∈ (var j) φ) ν ≤ᴮ c ⟩)
  (law-∀∈-lb  : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Envᴮ k) (σ : Nameᴮ)
              → ⟨ val (∀̇∈ (var j) φ) ν
                  ≤ᴮ (memᴬ (fst σ) (fst (lookup j ν)) ⇒ᴮ val φ (σ ∷ ν)) ⟩)
  (law-∀∈-glb : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Envᴮ k) (c : Pt B)
              → ((σ : Nameᴮ) → ⟨ c ≤ᴮ (memᴬ (fst σ) (fst (lookup j ν))
                                       ⇒ᴮ val φ (σ ∷ ν)) ⟩)
              → ⟨ c ≤ᴮ val (∀̇∈ (var j) φ) ν ⟩)
  where

  -- Track C into Track D, which is K5/ProbeC.agda's check repeated as an
  -- application rather than as a pair of refl equations.

  module GM = GI.Meeting C.decideAt    C.decideAt-sub    C.decideAt-spec
                         C.decideAt-dense
                         C.coneOrApart C.coneOrApart-sub C.coneOrApart-spec
                         C.coneOrApart-dense
                         G

  -- Track A into Track B, which is K5/ClausesAtFrame.agda's nine aliases as
  -- one application.

  module CL = K5.Clauses 𝒮 ext paths B L Cm carrier FP._≼ᶜ_ IsNameᴮ
  module CC = CL.Core FB.i FF._⊩ᴮ_ FF.⊩ᴮ-spec FB.≼-refl FB.≼-trans
                      FF.⊩ᴮ-mono FF.⊩ᴮ-down FF.⊩ᴮ-reg FF.⊩ᴮ-⊥ FF.⊩ᴮ-extend
                      eqᴬ memᴬ val
                      law-∈ law-≐ law-∧ law-∨ law-⇒ law-⊥
                      law-∃-ub law-∃-lub law-∀-lb law-∀-glb
                      law-∃∈-ub law-∃∈-lub law-∀∈-lb law-∀∈-glb

  -- THE SEAM. Every parameter of Track G's Generic layer, filled.

  module TV = K5.Truth.Poset.Core.Value
                𝒮 carrier order ext paths B L Cm Kc fb IsNameᴮ
                eqᴬ memᴬ val
                law-∈ law-≐ law-∧ law-∨ law-⇒ law-⊥
                law-∃-ub law-∃-lub law-∀-lb law-∀-glb
                law-∃∈-ub law-∃∈-lub law-∀∈-lb law-∀∈-glb
                CC._⊩_[_] CC.⊩-spec

  module TG = TV.Generic
                (λ p → GI.FS._∈ᴾ_ p G)
                meets
                (GI.Uof G)
                (λ _ h → h) (λ _ h → h)
                GM.Uof-up (GM.Uof-dir fil) GM.Uof-proper GM.Uof-ultra
                cob boc
                C.witnessAt C.witnessAt-sub C.witnessAt-force
                C.witnessAt-denseBelow
                (λ lem m → C.generic-meets-denseBelow lem G m fil)

  -- The truth lemma exists at the seam, at a fixed formula, and this is the
  -- statement the package hands to K6. The satisfaction surface and the two
  -- atomic bridges are still hypotheses of the Sat layer and are not supplied
  -- by any landed track; that is obstruction O1 and it is recorded rather
  -- than papered over.

  module SeamSat
    (_≈ᵁ_ _∈ᵁ_ : Nameᴮ → Nameᴮ → Ω)
    (sat : ∀ {k} → Src k → Envᴮ k → Ω)
    (sat-∈ : ∀ {k} (a b : Fin k) (ν : Envᴮ k)
           → sat (var a ∈̇ var b) ν ≡ (lookup a ν ∈ᵁ lookup b ν))
    (sat-≐ : ∀ {k} (a b : Fin k) (ν : Envᴮ k)
           → sat (var a ≐ var b) ν ≡ (lookup a ν ≈ᵁ lookup b ν))
    (sat-∧ : ∀ {k} (φ ψ : Src k) (ν : Envᴮ k)
           → sat (φ ∧̇ ψ) ν ≡ ((sat φ ν) ⊓ (sat ψ ν)))
    (sat-∨ : ∀ {k} (φ ψ : Src k) (ν : Envᴮ k)
           → sat (φ ∨̇ ψ) ν ≡ ((sat φ ν) ⊔ (sat ψ ν)))
    (sat-⇒ : ∀ {k} (φ ψ : Src k) (ν : Envᴮ k)
           → sat (φ ⇒̇ ψ) ν ≡ ((sat φ ν) ⇒ (sat ψ ν)))
    (sat-⊥ : ∀ {k} (ν : Envᴮ k) → sat {k} ⊥̇ ν ≡ ⊥)
    (sat-∃ : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k)
           → sat (∃̇ φ) ν ≡ ⋁ Nameᴮ (λ σ → sat φ (σ ∷ ν)))
    (sat-∀ : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k)
           → sat (∀̇ φ) ν ≡ ⋀ Nameᴮ (λ σ → sat φ (σ ∷ ν)))
    (sat-∃∈ : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Envᴮ k)
            → sat (∃̇∈ (var j) φ) ν
            ≡ ⋁ Nameᴮ (λ σ → (σ ∈ᵁ lookup j ν) ⊓ sat φ (σ ∷ ν)))
    (sat-∀∈ : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Envᴮ k)
            → sat (∀̇∈ (var j) φ) ν
            ≡ ⋀ Nameᴮ (λ σ → (σ ∈ᵁ lookup j ν) ⇒ sat φ (σ ∷ ν)))
    (atom-∈ : (σ τ : Nameᴮ) → (σ ∈ᵁ τ) ≡ GI.Uof G (memᴬ (fst σ) (fst τ)))
    (atom-≐ : (σ τ : Nameᴮ) → (σ ≈ᵁ τ) ≡ GI.Uof G (eqᴬ (fst σ) (fst τ)))
    where

    module TS = TG.Sat _≈ᵁ_ _∈ᵁ_ sat
                       sat-∈ sat-≐ sat-∧ sat-∨ sat-⇒ sat-⊥
                       sat-∃ sat-∀ sat-∃∈ sat-∀∈
                       atom-∈ atom-≐

    -- The headline, read back at the seam: satisfaction in the extension
    -- structure at a fixed formula is exactly the join over the generic of
    -- the conditions forcing it.

    seam-truth : LEM ℓ → ∀ {k} (φ : Src k) (ν : Envᴮ k) → TV.Supply φ
               → sat φ ν
               ≡ ⋁ FP.Cond (λ p → (GI.FS._∈ᴾ_ p G) ⊓ (CC._⊩_[_] p φ ν))
    seam-truth = TS.truth

    seam-not-both : LEM ℓ → ∀ {k} (φ : Src k) (ν : Envᴮ k) → TV.Supply φ
                  → ⟨ sat φ ν ⟩ → ⟨ sat (¬̇ φ) ν ⟩ → ⟨ ⊥ ⟩
    seam-not-both = TS.sat-not-both

    seam-decided : LEM ℓ → ∀ {k} (φ : Src k) (ν : Envᴮ k) → TV.Supply φ
                 → ⟨ (sat φ ν) ⊔ (sat (¬̇ φ) ν) ⟩
    seam-decided = TS.sat-decided

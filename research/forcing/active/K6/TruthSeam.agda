{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track E, THE GATE. Part 3.8's load bearing gap, closed or measured.
--
-- WHAT IS NEW HERE AND NOWHERE IN K1 TO K5. K5/TruthAtFrame.agda fills every
-- parameter of Track G's Generic layer from a landed track and then stops: its
-- module SeamSat (:182-208) re-opens the twelve slot satisfaction telescope and
-- fills none of it, and grepped over K5, TruthAtFrame is named by no other file
-- and SeamSat has no consumer. This file fills ten of the twelve slots with the
-- REAL satisfaction surface of Track F, K5.Structures.Kernel.BooleanSide at
-- U := Uof G, and leaves exactly two open: atom-∈ and atom-≐, which are O1.
--
-- THE COMPOSITION, in one line. Track F's B side structure carries
-- B'.Ext.Sat._⊨_, a re-export of FOL.Semantics.At at the record whose _∈ˢ_ is
-- the value relation (K5/Structures.agda:285-299). Track G's sat is stated on
-- PARAMETER FREE formulas, Src k = Formula (⊥* {ℓ}) k, so the two are joined by
-- embed (FOL/Manipulation/ConstantMapping, embed = mapFo Empty.rec*) and the
-- ten defining equations are then definitional. That embed is the right joint
-- is not a guess: K5/ExtensionSat.agda:219-220 states ext-⊨ at
-- (ν ⊨ᴾ embed φ) ≡ (envᴮ ν ⊨ᴮ embed φ), the same composite on the B side.
--
-- WHAT STAYS A PARAMETER, with its owner. The compiler surface eqᴬ, memᴬ, val
-- and the fourteen laws are K5 Track I's, typed verbatim from
-- Compile.agda:1318-1357 through K5/TruthAtFrame.agda:96-132. cob and boc are
-- K5 decision D1. G, its filter and its genericity are the instance's. And the
-- two atomic bridges are O1: K4/AtomicGraph.agda:411 declares the record,
-- TableSupply at :616-617 is uninhabited and table→graph at :719-720 is the
-- single route with no supplier.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax
open import FOL.Manipulation.ConstantMapping using ( embed )
open import Cubical.Induction.WellFounded using ( WellFounded )
import OrdinaryProfile
import K4.Algebra
import K4.Implication
import K5.Frame
import K5.Generic
import K5.Structures
import K5.TruthAtFrame

module K6.TruthSeam
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

open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ )
open K4.Implication 𝒮 ext paths B L Cm using ( _⊓ᴮ_ ; _⊔ᴮ_ ; _⇒ᴮ_ ; ⊥ᴮ )

module TAF = K5.TruthAtFrame 𝒮 ext paths sep carrier order B L Cm Kc fb IsNameᴮ

Src : ℕ → Type ℓ
Src k = Formula (⊥* {ℓ}) k

Nameᴮ : Type ℓ
Nameᴮ = Σ[ x ∈ S ] ⟨ IsNameᴮ x ⟩

Envᴮ : ℕ → Type ℓ
Envᴮ k = Vec Nameᴮ k

-- The name kernel, verbatim from K5/Structures.agda:209-217, plus the B side's
-- hereditary clause. These seven are K3's and the eighth is Track F's; no
-- second copy of any of them is declared here.

module Kernel
  (entry       : S → S → S)
  (Child       : S → S → Type ℓ)
  (isPropChild : (x n : S) → isProp (Child x n))
  (child-entry : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)
  (child-wf    : WellFounded Child)
  (∅ᴺ          : S)
  (∅ᴺ-spec     : (z : S) → (z ∈ˢ ∅ᴺ) ≡ ⊥)
  (child-nameᴮ : (n : S) → ⟨ IsNameᴮ n ⟩ → (x : S) → Child x n → ⟨ IsNameᴮ x ⟩)
  where

  module KS = K5.Structures.Kernel 𝒮
                entry Child isPropChild child-entry child-wf ∅ᴺ ∅ᴺ-spec
  module BS = KS.BooleanSide B L IsNameᴮ child-nameᴮ

  -- THE SURFACE, at one subset of the conditions. Uof G is Track D's and needs
  -- nothing but G; the B side structure is Track F's and needs nothing but the
  -- subset of the algebra that Uof G is. So the ten satisfaction slots can be
  -- filled here, before any filter or genericity hypothesis is named, and the
  -- conditionality of the package is not smeared across them.

  module At (G : TAF.GI.FS.Sub) where

    module EU = BS.B'.Ext (TAF.GI.Uof G)

    -- Slots one and two. The two relations are the B side structure's own two
    -- fields read off the names, and not a fresh pair with the same laws.

    _≈ᵁ_ : Nameᴮ → Nameᴮ → Ω
    σ ≈ᵁ τ = EU._≈[G]_ (fst σ) (fst τ)

    _∈ᵁ_ : Nameᴮ → Nameᴮ → Ω
    σ ∈ᵁ τ = EU._∈[G]_ (fst σ) (fst τ)

    -- Slot three. Satisfaction in the B side extension structure, at a
    -- parameter free formula embedded into the name alphabet.

    sat : ∀ {k} → Src k → Envᴮ k → Ω
    sat φ ν = EU._⊨_ ν (embed φ)

    -- Slots four to thirteen, the ten defining equations. Every one of them is
    -- refl, which is the measured content of this file: the B side structure's
    -- satisfaction IS Track G's sat and no translation layer sits between them.

    sat-∈ : ∀ {k} (a b : Fin k) (ν : Envᴮ k)
          → sat (var a ∈̇ var b) ν ≡ (lookup a ν ∈ᵁ lookup b ν)
    sat-∈ a b ν = refl

    sat-≐ : ∀ {k} (a b : Fin k) (ν : Envᴮ k)
          → sat (var a ≐ var b) ν ≡ (lookup a ν ≈ᵁ lookup b ν)
    sat-≐ a b ν = refl

    sat-∧ : ∀ {k} (φ ψ : Src k) (ν : Envᴮ k)
          → sat (φ ∧̇ ψ) ν ≡ ((sat φ ν) ⊓ (sat ψ ν))
    sat-∧ φ ψ ν = refl

    sat-∨ : ∀ {k} (φ ψ : Src k) (ν : Envᴮ k)
          → sat (φ ∨̇ ψ) ν ≡ ((sat φ ν) ⊔ (sat ψ ν))
    sat-∨ φ ψ ν = refl

    sat-⇒ : ∀ {k} (φ ψ : Src k) (ν : Envᴮ k)
          → sat (φ ⇒̇ ψ) ν ≡ ((sat φ ν) ⇒ (sat ψ ν))
    sat-⇒ φ ψ ν = refl

    sat-⊥ : ∀ {k} (ν : Envᴮ k) → sat {k} ⊥̇ ν ≡ ⊥
    sat-⊥ ν = refl

    sat-∃ : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k)
          → sat (∃̇ φ) ν ≡ ⋁ Nameᴮ (λ σ → sat φ (σ ∷ ν))
    sat-∃ φ ν = refl

    sat-∀ : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k)
          → sat (∀̇ φ) ν ≡ ⋀ Nameᴮ (λ σ → sat φ (σ ∷ ν))
    sat-∀ φ ν = refl

    sat-∃∈ : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Envᴮ k)
           → sat (∃̇∈ (var j) φ) ν
           ≡ ⋁ Nameᴮ (λ σ → (σ ∈ᵁ lookup j ν) ⊓ sat φ (σ ∷ ν))
    sat-∃∈ j φ ν = refl

    sat-∀∈ : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Envᴮ k)
           → sat (∀̇∈ (var j) φ) ν
           ≡ ⋀ Nameᴮ (λ σ → (σ ∈ᵁ lookup j ν) ⇒ sat φ (σ ∷ ν))
    sat-∀∈ j φ ν = refl

    -- THE COMPOSITE. Everything below the line is conditional, and every
    -- hypothesis of it is a parameter of this telescope rather than a field of
    -- a record applied out of sight. Ruling D1: the signature is the ledger.

    module Conditional
      (fil : TAF.GI.FS.isFilter G)
      (meets : TAF.C.MeetsAll G)
      (cob : TAF.C.CodeOfBelow)
      (boc : TAF.C.BelowOfCode)
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
      -- THE TWO OPEN SLOTS, AND THEY ARE THE ONLY TWO. O1.
      (atom-∈ : (σ τ : Nameᴮ) → (σ ∈ᵁ τ) ≡ TAF.GI.Uof G (memᴬ (fst σ) (fst τ)))
      (atom-≐ : (σ τ : Nameᴮ) → (σ ≈ᵁ τ) ≡ TAF.GI.Uof G (eqᴬ (fst σ) (fst τ)))
      where

      module TS = TAF.Seam G fil meets cob boc
                    eqᴬ memᴬ val
                    law-∈ law-≐ law-∧ law-∨ law-⇒ law-⊥
                    law-∃-ub law-∃-lub law-∀-lb law-∀-glb
                    law-∃∈-ub law-∃∈-lub law-∀∈-lb law-∀∈-glb

      module SS = TS.SeamSat _≈ᵁ_ _∈ᵁ_ sat
                    sat-∈ sat-≐ sat-∧ sat-∨ sat-⇒ sat-⊥
                    sat-∃ sat-∀ sat-∃∈ sat-∀∈
                    atom-∈ atom-≐

      -- The witness supply, per formula and never global. Named here so that F,
      -- G, H and I can quantify over it without re-opening Track G's Value
      -- layer. It is at Type (ℓ-suc ℓ) and may not index a join.

      Supply : ∀ {k} → Src k → Type (ℓ-suc ℓ)
      Supply = TS.TV.Supply

      -- THE TRUTH LEMMA AT THE SEAM, in the two forms K6 consumes. The first is
      -- the working form, satisfaction equals membership of the value in the
      -- generic; the second is the architecture's printed form, read back
      -- through Track B's sealed forcing relation.

      seam-Uof : LEM ℓ → ∀ {k} (φ : Src k) (ν : Envᴮ k) → Supply φ
               → sat φ ν ≡ TAF.GI.Uof G (val φ ν)
      seam-Uof = SS.TS.truth-Uof

      seam-truth : LEM ℓ → ∀ {k} (φ : Src k) (ν : Envᴮ k) → Supply φ
                 → sat φ ν
                 ≡ ⋁ TAF.FP.Cond (λ p → (TAF.GI.FS._∈ᴾ_ p G) ⊓ (TS.CC._⊩_[_] p φ ν))
      seam-truth = SS.seam-truth

      seam-not-both : LEM ℓ → ∀ {k} (φ : Src k) (ν : Envᴮ k) → Supply φ
                    → ⟨ sat φ ν ⟩ → ⟨ sat (¬̇ φ) ν ⟩ → ⟨ ⊥ ⟩
      seam-not-both = SS.seam-not-both

      seam-decided : LEM ℓ → ∀ {k} (φ : Src k) (ν : Envᴮ k) → Supply φ
                   → ⟨ (sat φ ν) ⊔ (sat (¬̇ φ) ν) ⟩
      seam-decided = SS.seam-decided

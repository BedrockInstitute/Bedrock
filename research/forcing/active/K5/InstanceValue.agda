{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track I, file 2 of 2: THE VALUE AND ITS FOURTEEN LAWS AT THE SEALED
-- CODED ALGEBRA.
--
-- What this file is for. Ledger clause L3 says `val` is a PARAMETER and not a
-- definition: no K5 file applies K4.Compile.Core except this one, and the
-- fourteen laws are typed verbatim from Compile.agda:1320-1357 wherever a K5
-- track consumes them. K5/Clauses.agda honours that (REPORT-B section 5.3:
-- its full import list contains no K4.Compile), and its inner `module Core`
-- is left with seventeen unfilled parameters, `eqᴬ`, `memᴬ`, `val` and the
-- fourteen laws. This file is where they come from at the coded completion.
--
-- THE TWO HEAVY MODULE APPLICATIONS, and the budget they are measured
-- against. K4's own Track J measured a file with two applications
-- (K4.Atomic.Atomic at fifteen arguments and K4.Compile.Core at twenty-one)
-- at 3.30 GB against a 1356-line deliverable's 1.08 GB, and drew rule 10 from
-- exactly that comparison: budget heap by module applications, not by line
-- count (K4 REPORT-J section 2). This file makes the same two-application
-- shape, so its peak is reported in REPORT-I rather than assumed small.
--
-- WHAT IS NOT DISCHARGED, and it is visible in the telescope rather than in a
-- comment. Seventeen of K4.Compile.Core's twenty-two parameters are taken
-- flat here: the name layer (NameSpace.agda:176, :179, :182-184, :868-870),
-- Track C's two atomic values, and Track E's nine-field atomic graph. The
-- last of those is OBSTRUCTION O1: the atomic graph has no discharge at any
-- ground (K4/AtomicGraph.agda:411 for the record, :719-720 for the single
-- route, TableSupply at :616-617 uninhabited). Nothing in this file closes
-- it, nothing in this file pretends to, and every consumer of the value
-- carries it in its own telescope for that reason.
--
-- WHAT THIS FILE MEASURES, beyond shipping the value. Architecture section
-- 6.7's probe 0 item 3 asks whether the forcing relation at a sealed
-- embedding elaborates against `val φ ν` at the sealed algebra. The fourteen
-- laws already answer half of it: `law-∧` is a path whose right-hand side is
-- the SEALED meet of two unsealed recursive value terms, which is the shape
-- `sealed-op (unsealed) (unsealed)` that section 6.7 calls unmeasured. The
-- other half is stated at the end, at an embedding taken as a module
-- parameter, which is preamble rule 2's tightest seal.
--
-- HYPOTHESES. CodedCompletion.Core's telescope verbatim, plus the seventeen
-- above. No excluded middle anywhere in this file: `grep -c "LEM"` over it
-- with comments stripped is 0. The classical cost of the instance lives
-- entirely in K5/InstanceBase.agda's `codedBase`.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax
  using ( Term; Formula; con; var
        ; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import OrdinaryProfile
import CodedCompletion
import K4.Algebra
import K4.InstanceCoded
import K4.Compile

module K5.InstanceValue
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext   : OrdinaryProfile.Extensionality 𝒮)
  (pow   : OrdinaryProfile.PowerSet 𝒮)
  (sep   : OrdinaryProfile.Separation 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (𝔓     : CodedCompletion.Presentation 𝒮)
  (laws  : CodedCompletion.Coded.ForcingLaws 𝒮 𝔓)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

open K4.Algebra 𝒮 using ( Pt; _≤ᴮ_; Lattice; Complement; CodedComplete )

module CD = CodedCompletion.Coded 𝒮 𝔓
open CD using ( carrier; order; Cond; _≼ᴵ_ )

-- Heavy application one. The sealed algebra: K4/InstanceCoded.agda's five
-- seals and the three records built over them.

module IC = K4.InstanceCoded 𝒮 ext pow sep paths 𝔓 laws
module CO = IC.CO

--------------------------------------------------------------------------------
-- The compiler at the sealed coded algebra
--------------------------------------------------------------------------------

-- The seventeen parameters K4.Compile.Core still needs once B, the lattice,
-- the complement and the completion are the coded ones. They are typed
-- character for character from Compile.agda:318-353, which is ledger clause
-- L10, so that a drift upstream fails here instead of passing silently.

module Compiler
  -- The name layer, flat. NameSpace.agda:176, :179, :182-184, :868-870.
  (IsName          : S → Ω)
  (nameAtˢ         : ∀ {n} → Fin n → Fin n → Formula S n)
  (nameΔ           : S → S → Ω)
  (nameAtˢ-reading : ∀ {n} (t w : Fin n) (γ : S ^ n)
                   → (γ ⊨ nameAtˢ t w) ≡ nameΔ (lookup w γ) (lookup t γ))
  (name-adequate   : (t : S)
                   → ((t ∷ CO.B ∷ []) ⊨ nameAtˢ zero (suc zero)) ≡ IsName t)
  -- Track C's AtomicSemantics, the two value fields.
  (eqᴬ  : S → S → Pt CO.B)
  (memᴬ : S → S → Pt CO.B)
  -- Track E's AtomicGraph, flat. THIS IS OBSTRUCTION O1.
  (eqAtˢ  : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n)
  (memAtˢ : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n)
  (eqΔ  : S → S → S → S → Ω)
  (memΔ : S → S → S → S → Ω)
  (eqAtˢ-reading  : ∀ {n} (b m p w : Fin n) (γ : S ^ n)
                  → (γ ⊨ eqAtˢ b m p w)
                  ≡ eqΔ (lookup w γ) (lookup b γ) (lookup m γ) (lookup p γ))
  (memAtˢ-reading : ∀ {n} (b m p w : Fin n) (γ : S ^ n)
                  → (γ ⊨ memAtˢ b m p w)
                  ≡ memΔ (lookup w γ) (lookup b γ) (lookup m γ) (lookup p γ))
  (eq-sound  : (m p b : S) → ⟨ IsName m ⟩ → ⟨ IsName p ⟩
             → ⟨ eqΔ CO.B b m p ⟩ → ⟨ b ≈ˢ fst (eqᴬ m p) ⟩)
  (eq-total  : (m p : S) → ⟨ IsName m ⟩ → ⟨ IsName p ⟩
             → ⟨ eqΔ CO.B (fst (eqᴬ m p)) m p ⟩)
  (mem-sound : (m p b : S) → ⟨ IsName m ⟩ → ⟨ IsName p ⟩
             → ⟨ memΔ CO.B b m p ⟩ → ⟨ b ≈ˢ fst (memᴬ m p) ⟩)
  (mem-total : (m p : S) → ⟨ IsName m ⟩ → ⟨ IsName p ⟩
             → ⟨ memΔ CO.B (fst (memᴬ m p)) m p ⟩)
  where

  -- Heavy application two, and the first application of K4.Compile.Core
  -- anywhere outside K4's own two probes: `grep -rn "Compile.Core"` over this
  -- compile root returns one comment line in K5/Truth.agda and no code.

  module VC = K4.Compile.Core 𝒮 ext paths sep
                CO.B IC.codedLattice IC.codedComplement IC.codedComplete
                IsName nameAtˢ nameΔ nameAtˢ-reading name-adequate
                eqᴬ memᴬ
                eqAtˢ memAtˢ eqΔ memΔ
                eqAtˢ-reading memAtˢ-reading
                eq-sound eq-total mem-sound mem-total

  -- The value, and the environment it reads. Both are K4's own definitions
  -- (Compile.agda:1206, :499-506) at the coded algebra; nothing is redefined,
  -- so preamble rule 9 is not in play.

  Src : ℕ → Type ℓ
  Src = VC.Src

  Nameᴮ : Type ℓ
  Nameᴮ = Σ[ x ∈ S ] ⟨ IsName x ⟩

  Envᴮ : ℕ → Type ℓ
  Envᴮ k = Vec Nameᴮ k

  val : ∀ {k} → Src k → Envᴮ k → Pt CO.B
  val = VC.value

  -- The fourteen laws, as the record K4 ships for exactly this use
  -- (Compile.agda:1319-1358, and its own note that the record is at Type ℓ).
  -- A consumer that wants them flat, which is what K5/Clauses.agda's Core
  -- takes, projects them one by one; the record is the cheaper hand-off and
  -- the projections are definitionally K4's own val-∈, val-≐, val-∧, ... .

  valLaws : VC.InterpLaws
  valLaws = VC.interpLaws

  -- The two atomic values, so that a consumer fills K5/Clauses.agda's `eqᴬ`
  -- and `memᴬ` from this module rather than from two places.

  eqValue memValue : S → S → Pt CO.B
  eqValue  = eqᴬ
  memValue = memᴬ

  ------------------------------------------------------------------------
  -- Probe 0 item 3, at the sealed algebra
  ------------------------------------------------------------------------

  -- The embedding enters as a module PARAMETER, which is preamble rule 2's
  -- tightest seal: a projection out of a module parameter is a variable and a
  -- variable cannot unfold. K5/InstanceBase.agda's `iᴷ` fills it, and so does
  -- anything else of that type.
  --
  -- The two declarations below are the forcing relation at a value. The type
  -- of the second nests the SEALED meet over two applications of the value,
  -- which is the compiler-side instance of the shape architecture section 6.7
  -- calls unmeasured, and the ⊓ᴮ in it is IC.meetᴷ and not K2's transparent
  -- coded meet.

  module AtEmbedding (iᶠ : Cond → Pt CO.B) where

    open Lattice IC.codedLattice using ( _⊓ᴮ_ )

    _⊩ᵛ_[_] : ∀ {k} → Cond → Src k → Envᴮ k → Ω
    p ⊩ᵛ φ [ ν ] = iᶠ p ≤ᴮ val φ ν

    -- The conjunction clause at the instance, which is the whole of item 3's
    -- second half: a statement about the sealed meet of two value terms.

    ⊩ᵛ-∧→ : ∀ {k} (p : Cond) (φ ψ : Src k) (ν : Envᴮ k)
          → ⟨ p ⊩ᵛ (φ ∧̇ ψ) [ ν ] ⟩
          → ⟨ iᶠ p ≤ᴮ (val φ ν ⊓ᴮ val ψ ν) ⟩
    ⊩ᵛ-∧→ p φ ψ ν h =
      subst (λ w → ⟨ iᶠ p ≤ᴮ w ⟩) (VC.InterpLaws.law-∧ valLaws φ ψ ν) h

    ⊩ᵛ-∧← : ∀ {k} (p : Cond) (φ ψ : Src k) (ν : Envᴮ k)
          → ⟨ iᶠ p ≤ᴮ (val φ ν ⊓ᴮ val ψ ν) ⟩
          → ⟨ p ⊩ᵛ (φ ∧̇ ψ) [ ν ] ⟩
    ⊩ᵛ-∧← p φ ψ ν h =
      subst (λ w → ⟨ iᶠ p ≤ᴮ w ⟩) (sym (VC.InterpLaws.law-∧ valLaws φ ψ ν)) h

  ------------------------------------------------------------------------
  -- The same, with K2's UNSEALED embedding, as the control
  ------------------------------------------------------------------------

  -- CO.iᴮ is iSet (fst p) with iSet p = separateOf sep carrier (coneφ p)
  -- (CodedCompletion.agda:559-560, :579-580), an unsealed description-operator
  -- term over GroundDescription.agda:130-131's `the`. If the seal on the
  -- embedding were load bearing HERE, this block would be the one that does
  -- not elaborate. REPORT-I section 2 records that it does.

  module AtRawEmbedding where

    open Lattice IC.codedLattice using ( _⊓ᴮ_ )

    _⊩ᵘ_[_] : ∀ {k} → Cond → Src k → Envᴮ k → Ω
    p ⊩ᵘ φ [ ν ] = CO.iᴮ p ≤ᴮ val φ ν

    ⊩ᵘ-∧→ : ∀ {k} (p : Cond) (φ ψ : Src k) (ν : Envᴮ k)
          → ⟨ p ⊩ᵘ (φ ∧̇ ψ) [ ν ] ⟩
          → ⟨ CO.iᴮ p ≤ᴮ (val φ ν ⊓ᴮ val ψ ν) ⟩
    ⊩ᵘ-∧→ p φ ψ ν h =
      subst (λ w → ⟨ CO.iᴮ p ≤ᴮ w ⟩) (VC.InterpLaws.law-∧ valLaws φ ψ ν) h

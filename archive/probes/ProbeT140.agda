{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

-- [L3.32-T140] The tail probe.
--
-- The question: must a fresh proof of `graphAt-holds` and `graphAt-unique`
-- go through the table, slot, sound and unique machinery?
--
-- This probe states the two readings exactly as `L.TowerGraph.Readings`
-- declares them (src/L/TowerGraph.lagda.md:366-378). It does not open
-- `L.Coding.Table`, `L.Coding.Slot`, `L.Coding.Sound` or `L.Coding.Unique`.
-- The surviving interface (`L.Definability`) is in scope.
--
-- The probe proves the assembly: each reading closes in a few lines once
-- its obligation is given. The obligations are stated as types below. Their
-- delivered inhabitants live in the four forbidden modules, and the
-- surviving interface exports no construction that supplies them. That is
-- the measurement: the fresh tail is the obligations, and neither reading
-- fits the 300-line stop without them.

module ProbeT140 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Coding.Model {ℓ}
  using ( closedAt; domAt; domAt-out )
open import L.Coding.Graph {ℓ} lem
  using ( satGraphAt; GraphWitAt; graphAt-in; graphAt-out; twelveAt )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- The carrier is a module parameter, exactly as in `L.TowerGraph`
-- (`module _ (A : S) where`). `Sat` and `keyʟ` are delivered inputs: the
-- reading types mention them, and the delivered definitions live in
-- `L.Coding.Sat` and `L.Coding.Table`. `keyʟ` lives in the forbidden Table
-- module, so it enters as a parameter, honestly.
module _ (A : S) where
  module Readings (Sat : Formula S 1 → S) (keyʟ : Formula S 1 → S) where

    Ci Ti Bi : ∀ {n} → Fin (suc (suc (suc n)))
    Ci = suc (suc zero)
    Ti = suc zero
    Bi = zero

    -- Target 1, copied from `L.TowerGraph.Readings`:
    -- (φ : Formula S 1) → ∀ {n} (w c v : Fin n) (γ : S ^ n)
    -- → fst (lookup w γ) ≡ fst A
    -- → fst (lookup c γ) ≡ fst (keyʟ φ)
    -- → fst (lookup v γ) ≡ fst (Sat φ)
    -- → ⟨ γ ⊨ satGraphAt w c v ⟩
    --
    -- Target 2, copied from the same telescope:
    -- (φ : Formula S 1) → ∀ {n} (w c v : Fin n) (γ : S ^ n)
    -- → fst (lookup w γ) ≡ fst A
    -- → fst (lookup c γ) ≡ fst (keyʟ φ)
    -- → ⟨ γ ⊨ satGraphAt w c v ⟩
    -- → fst (lookup v γ) ≡ fst (Sat φ)

    -- Obligation 1. `satGraphAt w c v` is `∃̇ (∃̇ (∃̇ (pin ∧̇ closedAt ∧̇
    -- domAt ∧̇ appAt ∧̇ twelveAt)))`. Its satisfaction is a witness triple
    -- (C, T, b): the carrier slot, the table of key-value pairs, and the
    -- pinned value. `GraphWitAt` is exactly that witness shape:
    --
    --   Σ[ C ∈ S ] Σ[ T ∈ S ] Σ[ b ∈ S ]
    --     ( fst b ≡ fst (lookup w γ)
    --     × ⟨ (b ∷ T ∷ C ∷ γ) ⊨ closedAt Ci ⟩
    --     × ⟨ (b ∷ T ∷ C ∷ γ) ⊨ domAt Ti Ci ⟩
    --     × ⟨ pr (fst (lookup c γ)) (fst (lookup v γ)) ∈ fst T ⟩
    --     × ⟨ (b ∷ T ∷ C ∷ γ) ⊨ twelveAt Ci Ti Bi ⟩ )
    --
    -- The delivered proof fills this witness with `slot B φ`, `satTable B φ`,
    -- `slotClosed B φ γ`, `domAt-intro` (via `inSlot`/`total`),
    -- `entry-in B φ` and `soundness B φ γ` (Powerset.lagda.md:354-365;
    -- homes at Table.lagda.md:103-107, :278, :288, :318-321,
    -- Slot.lagda.md:262-263, Sound.lagda.md:1038). All of those live in the
    -- forbidden modules. The surviving interface exports only `smallSat`,
    -- `defSet`, `Def`, `Def-spec`, `defSet⊆A`, `defSet-mem` and `Refine`
    -- (Definability.lagda.md:107-113, :136, :140, :145, :217): it carves
    -- subsets of `⟪ fst A ⟫` by meta-formulas and never constructs a set of
    -- key-value pairs, so it cannot supply `T`.
    TableObligation : Type (ℓ-suc ℓ)
    TableObligation =
      (φ : Formula S 1) → ∀ {n} (w c v : Fin n) (γ : S ^ n)
      → fst (lookup w γ) ≡ fst A
      → fst (lookup c γ) ≡ fst (keyʟ φ)
      → fst (lookup v γ) ≡ fst (Sat φ)
      → GraphWitAt w c v γ

    -- Obligation 2. The witness of `graphAt-out` gives the closed, total
    -- triple and the twelve clauses. The value at the key of `φ` is pinned:
    -- the induction over `φ` (the delivered `Good.pinned`, Unique.lagda.md:
    -- 884-906, whose twelve cases run from :209 to :795) concludes
    -- `fst y ≡ fst (Sat B φ)`. The surviving interface has no such
    -- induction: its exports contain no statement about values at keys.
    PinningObligation : Type (ℓ-suc ℓ)
    PinningObligation =
      ∀ {k} (δ : S ^ k) (Ci' Ti' Bi' : Fin k)
      → ⟨ δ ⊨ closedAt Ci' ⟩
      → ⟨ δ ⊨ domAt Ti' Ci' ⟩
      → ⟨ δ ⊨ twelveAt Ci' Ti' Bi' ⟩
      → (φ : Formula S 1) (c y : S)
      → fst c ≡ fst (keyʟ φ)
      → ⟨ fst c ∈ fst (lookup Ci' δ) ⟩
      → ⟨ pr (fst c) (fst y) ∈ fst (lookup Ti' δ) ⟩
      → fst y ≡ fst (Sat φ)

    -- The assembly, measured. Given Obligation 1, target 1 closes in three
    -- lines: the witness is truncated and fed to the frame's `graphAt-in`.
    graphAt-holds-from-table :
      TableObligation
      → (φ : Formula S 1) → ∀ {n} (w c v : Fin n) (γ : S ^ n)
      → fst (lookup w γ) ≡ fst A
      → fst (lookup c γ) ≡ fst (keyʟ φ)
      → fst (lookup v γ) ≡ fst (Sat φ)
      → ⟨ γ ⊨ satGraphAt w c v ⟩
    graphAt-holds-from-table obl φ w c v γ qw qc qv =
      graphAt-in w c v γ ∣ obl φ w c v γ qw qc qv ∣₁

    -- Given Obligation 2, target 2 closes in eight lines: `graphAt-out`
    -- unwraps the witness, `domAt-out` moves the code into the domain, and
    -- the pinning induction concludes the value.
    graphAt-unique-from-pinning :
      PinningObligation
      → (φ : Formula S 1) → ∀ {n} (w c v : Fin n) (γ : S ^ n)
      → fst (lookup w γ) ≡ fst A
      → fst (lookup c γ) ≡ fst (keyʟ φ)
      → ⟨ γ ⊨ satGraphAt w c v ⟩
      → fst (lookup v γ) ≡ fst (Sat φ)
    graphAt-unique-from-pinning pin φ w c v γ qw qc h =
      PT.rec (setIsSet (fst (lookup v γ)) (fst (Sat φ))) step
        (graphAt-out w c v γ h)
      where
      step : GraphWitAt w c v γ → fst (lookup v γ) ≡ fst (Sat φ)
      step (C , (T , (b , (eb , (hc , (hd , (ha , h12))))))) =
        pin (b ∷ T ∷ C ∷ γ) Ci Ti zero hc hd h12 φ
            (lookup c γ) (lookup v γ) qc
            (domAt-out Ti Ci (b ∷ T ∷ C ∷ γ) hd
               (lookup c γ) (lookup v γ) ha) ha

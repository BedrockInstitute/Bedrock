{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.608]  W3.  THE STATEMENT, TYPE ONLY.
--
-- WRITTEN FIRST AND TYPECHECKED ALONE, per the brief's W3 section:
-- "Write it FIRST, typecheck it ALONE, cap it, and report peak RSS.
-- ESTIMATE: about 12 lines, cap at two minutes."  The index type 0.1
-- below was the file's whole content at runs/w3idx-1.out; the lifts
-- and the statement were added after that run landed, and the whole
-- file was then typechecked alone (runs/w3-*.out) before any probe
-- imported it.  NOTHING is inhabited in this file: the main probe
-- imports it and discharges the statement under this very type, so
-- the stated statement and the discharged one cannot drift.
--
-- The recursion is the assembly's branch
-- (src/L/StageCardinal.lagda.md:534-537), the `ih` of ingredient (iv)
-- in [LJ-1.594]'s table.  At a strictly infinite member stage the
-- branch's value is the composed IH at the member stage embedded
-- (src/L/StageCardinal.lagda.md:555-560), and the statement below
-- takes the member stage's OWN graph as a hypothesis: that is the one
-- choice this file makes, and [LJ-1.601]'s report states the reading
-- (agents/tasks/LJ-1-601/lj-1.601-report.md:1, WHAT IT RETIRES).
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-608.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Presentation {ℓ} using ( member; fiber )
open import FOL.Syntax using ( Formula )
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Absoluteness
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset→isL; Lset )
open import L.Ordinal {ℓ} using ( ω-ord; suc-ord; mem-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( LsetS )
import L.StageCardinal

open import Cubical.Data.Sigma using ( _×_ )
open Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
open InfinitySet {ℓ} using ( ω; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SV using ( _∈ˢ_ )
open SL using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq
open SC using ( _↪_ )

-- 0.1  THE RECURSION'S INDEX AT AN INFINITE MEMBER STAGE, TYPE ONLY.
--      `InfIdx α` is the type of the branch's indices at strictly
--      infinite member stages of α.  STRICT infinitude, and not mere
--      non-finitude, is the choice this type makes: it names the one
--      case of the branch's trichotomy whose value the source states
--      as the composed IH at the member stage
--      (src/L/StageCardinal.lagda.md:555-560).
InfIdx : (α : V ℓ) → Type (ℓ-suc ℓ)
InfIdx α = Σ[ m ∈ ⟪ α ⟫ ] ⟨ ω ∈ˢ (⟪ α ⟫↪ m) ⟩

--   The lifts, [LJ-1.561]'s discipline: one line each, re-typed rather
--   than imported, because importing a probe costs its whole
--   elaboration (agents/tasks/LJ-1-597/Probe597.agda:78-82).
isL-ord : (β : V ℓ) → IsOrd β → ⟨ isL β ⟩
isL-ord β oβ = Lset→isL (sucV β) (suc-ord oβ) β (ord∈Lset-suc β oβ)

up : (b : S) → ⟪ fst b ⟫ → S
up b m = ⟪ fst b ⟫↪ m , isL-trans (member (fst b) m) (snd b)

ixOf : (b x : S) → ⟨ fst x ∈ fst b ⟩ → ⟪ fst b ⟫
ixOf b x k = fiber (fst b) {x = fst x} k .fst

-- 0.2  THE SITE, AND THE OBLIGATION'S TYPE, BOTH DIRECTIONS.
--
--   `Graph` is [LJ-1.597]'s shape
--   (agents/tasks/LJ-1-597/Probe597.agda:269): a `Formula S 2`, value
--   variable first and index second, with BOTH readings
--   (`src/L/Recursion.lagda.md:272-279`), at the branch's value at a
--   STRICTLY INFINITE member stage.  The subject `val` is that value
--   lifted into the INDEX α; the hypothesis `IHGraph` is the same
--   shape at the member stage's own recursion, lifted into δ.  The
--   formula is the SAME formula in both: the object language reads
--   equality and membership on underlying sets, and the embedding
--   changes presentations only.
module Site (α : V ℓ) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
            (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
            (IH : (δ : V ℓ) → ⟨ δ ∈ˢ α ⟩ → SC.Upper.P δ) where

  module At (m : ⟪ α ⟫) (ω∈δ : ⟨ ω ∈ˢ (⟪ α ⟫↪ m) ⟩) where

    δ : V ℓ
    δ = ⟪ α ⟫↪ m

    δ∈α : ⟨ δ ∈ˢ α ⟩
    δ∈α = member α m

    oδ : IsOrd δ
    oδ = mem-ord {A = α} oα δ δ∈α

    δ∈suc : ⟨ δ ∈ˢ sucV α₀ ⟩
    δ∈suc = suc-ord oα₀ .fst {x = α} {y = δ} δ∈α α∈suc

    infδ : ⟨ δ ∈ˢ ω ⟩ → Empty.⊥
    infδ h = ∈-irrefl ω (ω-ord .fst ω∈δ h)

    IHδ : ⟪ Lset δ ⟫ ↪ ⟪ δ ⟫
    IHδ = IH δ δ∈α oδ δ∈suc infδ

    br : ⟪ Lset δ ⟫ ↪ ⟪ α ⟫
    br = SC.Upper.comp-inj IHδ (SC.Upper.Emb.emb α oα δ δ∈α)

    δL : S
    δL = LsetS δ oδ

    αO : S
    αO = α , isL-ord α oα

    δO : S
    δO = δ , isL-ord δ oδ

    val : (x : S) (k : ⟨ fst x ∈ fst δL ⟩) → S
    val x k = up αO (fst br (ixOf δL x k))

    valδ : (x : S) (k : ⟨ fst x ∈ fst δL ⟩) → S
    valδ x k = up δO (fst IHδ (ixOf δL x k))

    IHGraph : Type (ℓ-suc ℓ)
    IHGraph = Σ[ ψ ∈ Formula S 2 ]
      ( ((x y : S) (k : ⟨ fst x ∈ fst δL ⟩)
         → fst y ≡ fst (valδ x k) → ⟨ (y ∷ x ∷ []) ⊨ ψ ⟩)
      × ((x y : S) → ⟨ (y ∷ x ∷ []) ⊨ ψ ⟩ → (k : ⟨ fst x ∈ fst δL ⟩)
         → fst y ≡ fst (valδ x k)) )

    RecGraph∞ : Type (ℓ-suc ℓ)
    RecGraph∞ = IHGraph →
      Σ[ ψ ∈ Formula S 2 ]
        ( ((x y : S) (k : ⟨ fst x ∈ fst δL ⟩)
           → fst y ≡ fst (val x k) → ⟨ (y ∷ x ∷ []) ⊨ ψ ⟩)
        × ((x y : S) → ⟨ (y ∷ x ∷ []) ⊨ ψ ⟩ → (k : ⟨ fst x ∈ fst δL ⟩)
           → fst y ≡ fst (val x k)) )

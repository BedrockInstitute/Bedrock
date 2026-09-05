{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.438] PROBE.  Pay the bare nonempty at the coded predicate.
-- It runs in agents/tasks/LJ-1-438/ and lands nothing in src/.
--
--   W3 FIRST  `code-target-swap`.  Moves InjCode across an equality
--             of fst on the third argument.  Graph, γ and the
--             obligation omitted.  Typechecked ALONE.
--
--   GRAPH     Rebuilt from [LJ-1.429] Probe429.agda:53-95.  Peak RSS
--             recorded before the swap was added back.
--
--   TERM      `coded-nonempty`.  self in sucV (fst a), the identity
--             code of [LJ-1.429] moved onto upα self by W3.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-438.Probe438 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV )
open import V.Presentation {ℓ} using ( member; fiber )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono; Lset→isL )
open import L.Ordinal {ℓ} using ( bound2; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Choice.Step {ℓ} lem using ( Mem )
open import L.Cardinal {ℓ} lem using ( InjCode; module SiteBound )
open import L.InjChain {ℓ} lem using ( module InclGraph )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- Generic in a and in oa.  No band, no numeral, no cardinal.
-- Graph rebuilt from Probe429.agda:53-95.
-- Crossing rebuilt from Probe430.agda:60-66.
-- W3 moves the code from a to upα self.
-- =====================================================================

module _ (a : S) (oa : IsOrd (fst a)) where

  open SiteBound a

  module IG = InclGraph a a (λ _ h → h)

  G : S
  G = IG.G

  stgG : V ℓ
  stgG = stage (fst G) (snd G)

  oStg : IsOrd stgG
  oStg = stage-ord (fst G) (snd G)

  pair : Σ[ γ ∈ V ℓ ] (IsOrd γ × ⟨ β ∈ˢ γ ⟩ × ⟨ sucV stgG ∈ˢ γ ⟩)
  pair = bound2 β (sucV stgG) oβ (suc-ord oStg)

  γ : V ℓ
  γ = pair .fst

  oγ : IsOrd γ
  oγ = pair .snd .fst

  stage-in-gamma : ⟨ stgG ∈ˢ γ ⟩
  stage-in-gamma = oγ .fst (self∈sucV stgG) (pair .snd .snd .snd)

  -- Crossing restated at γ, the same line SiteBound.up writes at β
  -- (src/L/Cardinal.lagda.md:171).  Copied from Probe429.agda:81-82.
  upγ : Mem (Lset γ) → S
  upγ (x , mx) = x , Lset→isL γ oγ x mx

  mG : ⟨ fst G ∈ˢ Lset γ ⟩
  mG = Lset-mono {α = γ} {β = stgG} stage-in-gamma (stage-mem (fst G) (snd G))

  Fg : Mem (Lset γ)
  Fg = fst G , mG

  -- LeastCardInjL's crossing, rebuilt at the call site, not opened.
  -- Copied from Probe430.agda:60-66 / src/L/Cardinal.lagda.md:72-80.
  hSucα : ⟨ isL (sucV (fst a)) ⟩
  hSucα = Lset→isL (sucV (sucV (fst a))) (suc-ord (suc-ord oa)) (sucV (fst a))
            (ord∈Lset-suc (sucV (fst a)) (suc-ord oa))

  upα : ⟪ sucV (fst a) ⟫ → S
  upα m = ⟪ sucV (fst a) ⟫↪ m
        , isL-trans (member (sucV (fst a)) m) hSucα

  -- W3.  The one step.  First three conjuncts of InjCode copy.
  -- The fourth substs on fst of the third argument
  -- (src/L/Cardinal.lagda.md:228).
  code-target-swap :
      (F b b' : S) → fst b ≡ fst b'
    → InjCode F a b → InjCode F a b'
  code-target-swap F b b' e (sv , dm , ij , ran) =
    sv , dm , ij , λ x y p → subst (λ v → ⟨ fst y ∈ v ⟩) e (ran x y p)

  -- The two lines the chapter writes at src/L/Cardinal.lagda.md:103-107.
  self : ⟪ sucV (fst a) ⟫
  self = fiber (sucV (fst a)) (self∈sucV (fst a)) .fst

  self-eq : ⟪ sucV (fst a) ⟫↪ self ≡ fst a
  self-eq = fiber (sucV (fst a)) (self∈sucV (fst a)) .snd

  -- Four conjuncts at G ∷ a ∷ [].  Copied from Probe429.agda:97-98.
  id-code : InjCode (upγ Fg) a a
  id-code = IG.sv , IG.dm , IG.ij , IG.ran

  moved : InjCode (upγ Fg) a (upα self)
  moved = code-target-swap (upγ Fg) a (upα self) (sym self-eq) id-code

  coded-nonempty :
    ∥ Σ[ d ∈ ⟪ sucV (fst a) ⟫ ]
        ∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a (upα d) ∥₁ ∥₁
  coded-nonempty = ∣ self , ∣ Fg , moved ∣₁ ∣₁

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.429] PROBE.  The identity code at a bound built FROM the graph.
-- It runs in agents/tasks/LJ-1-429/ and lands nothing in src/.
--
--   W3 FIRST  `stage-in-gamma`.  The graph is built.  The bound is
--             bound2 of SiteBound.β and sucV (stage G).  The membership
--             ⟨ stage (fst G) (snd G) ∈ˢ γ ⟩ is the whole risk.
--             InjCode conjuncts omitted.
--
--   TERM      `id-code-wide`.  Four conjuncts at G ∷ a ∷ [], truncated
--             membership of G in Lset γ, upγ the SiteBound.up crossing
--             restated at γ.  No Σ≡Prop: InjCode sees only fst.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-429.Probe429 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; Lset; Lset-mono; Lset→isL )
open import L.Ordinal {ℓ} using ( bound2; suc-ord )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Choice.Step {ℓ} lem using ( Mem )
open import L.Cardinal {ℓ} lem using ( InjCode; module SiteBound )
open import L.InjChain {ℓ} lem using ( module InclGraph )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- W3.  Graph built.  Bound taken FROM the graph.  InjCode omitted.
-- Generic in a.  SiteBound a in scope.  No cardinal, no band, no
-- numeral, no ω of this probe's own.
-- =====================================================================

module _ (a : S) where

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
  -- (src/L/Cardinal.lagda.md:171).
  upγ : Mem (Lset γ) → S
  upγ (x , mx) = x , Lset→isL γ oγ x mx

  -- Placement: stage G ∈ γ, so G is a member of Lset γ.
  -- [LJ-1.425] delivered this implication; this task pays the premise.
  mG : ⟨ fst G ∈ˢ Lset γ ⟩
  mG = Lset-mono {α = γ} {β = stgG} stage-in-gamma (stage-mem (fst G) (snd G))

  Fg : Mem (Lset γ)
  Fg = fst G , mG

  -- Four conjuncts at G ∷ a ∷ [].  γI = G ∷ D ∷ [] and D = a
  -- (src/L/InjChain.lagda.md:515-516), so no repackaging.
  -- G and upγ Fg are NOT equal as S (isL proofs differ; see
  -- runs/sigma-refl.out).  InjCode sees only fst, so the raw tuple
  -- inhabits InjCode (upγ Fg) a a with no Σ≡Prop.
  id-code-wide : ∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a a ∥₁
  id-code-wide = ∣ Fg , (IG.sv , IG.dm , IG.ij , IG.ran) ∣₁

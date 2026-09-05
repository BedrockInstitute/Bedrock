{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.426] W3 PROBE, then the obligation.
-- HALF B instantiated at x := a, d := κ.  Four hypotheses bare.
-- DO NOT ATTEMPT HALF A.  Audit F6: joining the halves was killed
-- at 8.5 GB RSS.  The obligation `kappa-coded` stays a hole if the
-- live chapters supply no graph.
--
-- `code-from-graph` is copied from LJ-1-414.Probe414:115-128, because
-- importing that module also checks `amb-to-coded = {!!}`.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.  Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-426.Probe426 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset )
open import L.Choice.Step {ℓ} lem using ( Mem )
open import L.Coding.Model {ℓ}
  using ( svAt; svAt-in
        ; domAt; domAt-intro )
open import L.Coding.Injection {ℓ} lem using ( injAt; injAt-in )
open import L.Cardinal {ℓ} lem
  using ( InjCode; module LeastCardInjL; module SiteBound )

open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- HALF B, copied from Probe414.agda:75-128.  No ambient function.
-- =====================================================================

module CodeFromGraph
  (x d G : S)
  (pair-out : (u v : S) → ⟨ pr (fst u) (fst v) ∈ fst G ⟩
            → ⟨ fst u ∈ fst x ⟩ × ⟨ fst v ∈ fst d ⟩)
  (pair-in : (u : S) → ⟨ fst u ∈ fst x ⟩
           → ∥ Σ[ v ∈ S ] ⟨ pr (fst u) (fst v) ∈ fst G ⟩ ∥₁)
  (uniq : (u v v' : S) → ⟨ pr (fst u) (fst v) ∈ fst G ⟩
        → ⟨ pr (fst u) (fst v') ∈ fst G ⟩ → fst v ≡ fst v')
  (inj-mem : (v u u' : S) → ⟨ pr (fst u) (fst v) ∈ fst G ⟩
           → ⟨ pr (fst u') (fst v) ∈ fst G ⟩ → fst u ≡ fst u')
  where

  private
    γG : S ^ 2
    γG = G ∷ x ∷ []

  sv : ⟨ γG ⊨ svAt zero ⟩
  sv = svAt-in zero γG uniq

  ij : ⟨ γG ⊨ injAt zero ⟩
  ij = injAt-in zero γG inj-mem

  dm : ⟨ γG ⊨ domAt zero (suc zero) ⟩
  dm = domAt-intro zero (suc zero) γG (λ u → fwd u , bwd u)
    where
    fwd : (u : S) → ⟨ ∃[ v ∶ S ] (pr (fst u) (fst v) ∈ fst G) ⟩
        → ⟨ fst u ∈ fst x ⟩
    fwd u = PT.rec (snd (fst u ∈ fst x))
      (λ { (v , p) → fst (pair-out u v p) })

    bwd : (u : S) → ⟨ fst u ∈ fst x ⟩
        → ⟨ ∃[ v ∶ S ] (pr (fst u) (fst v) ∈ fst G) ⟩
    bwd u = pair-in u

  ran : (u v : S) → ⟨ pr (fst u) (fst v) ∈ fst G ⟩ → ⟨ fst v ∈ fst d ⟩
  ran u v p = snd (pair-out u v p)

  coded : InjCode G x d
  coded = sv , (dm , (ij , ran))

code-from-graph :
    (x d G : S)
  → ((u v : S) → ⟨ pr (fst u) (fst v) ∈ fst G ⟩
               → ⟨ fst u ∈ fst x ⟩ × ⟨ fst v ∈ fst d ⟩)
  → ((u : S) → ⟨ fst u ∈ fst x ⟩
            → ∥ Σ[ v ∈ S ] ⟨ pr (fst u) (fst v) ∈ fst G ⟩ ∥₁)
  → ((u v v' : S) → ⟨ pr (fst u) (fst v) ∈ fst G ⟩
                → ⟨ pr (fst u) (fst v') ∈ fst G ⟩ → fst v ≡ fst v')
  → ((v u u' : S) → ⟨ pr (fst u) (fst v) ∈ fst G ⟩
                → ⟨ pr (fst u') (fst v) ∈ fst G ⟩ → fst u ≡ fst u')
  → InjCode G x d
code-from-graph x d G pair-out pair-in uniq inj-mem = coded
  where
  open CodeFromGraph x d G pair-out pair-in uniq inj-mem

-- =====================================================================
-- W3.  Instantiate at x := a, d := κ.  Four hypotheses bare.
-- `a` and `oa` are module parameters.  No band, no numeral.
-- =====================================================================

module _ (a : S) (oa : IsOrd (fst a)) where

  open SiteBound a
  open LeastCardInjL a oa using (κ)

  -- HALF B at this pair.  G and the four readings are module hypotheses.
  -- Which of the four has a producer is a report question, not a term.
  module FromGraph
    (G : S)
    (pair-out : (u v : S) → ⟨ pr (fst u) (fst v) ∈ fst G ⟩
              → ⟨ fst u ∈ fst a ⟩ × ⟨ fst v ∈ fst κ ⟩)
    (pair-in : (u : S) → ⟨ fst u ∈ fst a ⟩
             → ∥ Σ[ v ∈ S ] ⟨ pr (fst u) (fst v) ∈ fst G ⟩ ∥₁)
    (uniq : (u v v' : S) → ⟨ pr (fst u) (fst v) ∈ fst G ⟩
          → ⟨ pr (fst u) (fst v') ∈ fst G ⟩ → fst v ≡ fst v')
    (inj-mem : (v u u' : S) → ⟨ pr (fst u) (fst v) ∈ fst G ⟩
             → ⟨ pr (fst u') (fst v) ∈ fst G ⟩ → fst u ≡ fst u')
    where

    from-graph : InjCode G a κ
    from-graph = code-from-graph a κ G pair-out pair-in uniq inj-mem

  -- THE OBLIGATION.  HALF A at this pair has no producer in the live
  -- chapters (report sections 2 and 3).  Hole by design.  Not a
  -- refutation of the type.
  kappa-coded : ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) a κ ∥₁
  kappa-coded = {!!}

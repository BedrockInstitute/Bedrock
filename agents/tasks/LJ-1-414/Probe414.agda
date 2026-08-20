{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.414] W3 PROBE, then the obligation.  HALF B first:
-- `code-from-graph`.  The membership readings of G, in the shape
-- InclGraph states them (src/L/InjChain.lagda.md:494-547), yield
-- InjCode.  InclGraph's pair-out also gives uniqueness and
-- injectivity, because both coordinates are equal.  At this
-- generality those two laws sit beside the two readings.  No ambient
-- function appears in HALF B.  HALF A is the type `HalfA`.  No
-- producer.  The obligation `amb-to-coded` stays a hole.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber.
-- Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-414.Probe414 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Coding.Model {ℓ}
  using ( svAt; svAt-in
        ; domAt; domAt-intro )
open import L.Coding.Injection {ℓ} lem using ( injAt; injAt-in )
open import L.Cardinal {ℓ} lem using ( InjCode; _↪_ )

open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- HALF A, NAMED.  A graph G of an ambient injection f, as two
-- membership readings.  Shape: InclGraph.pair-out / pair-in
-- (src/L/InjChain.lagda.md:494-511).  No inhabitant at this generality.
-- =====================================================================

GraphOf : (x d : S) → (⟪ fst x ⟫ ↪ ⟪ fst d ⟫) → S → Type (ℓ-suc ℓ)
GraphOf x d f G =
    ((u v : S) → ⟨ pr (fst u) (fst v) ∈ fst G ⟩
               → ∥ Σ[ m ∈ ⟪ fst x ⟫ ]
                    ((fst u ≡ ⟪ fst x ⟫↪ m)
                   × (fst v ≡ ⟪ fst d ⟫↪ (fst f m))) ∥₁)
  × ((m : ⟪ fst x ⟫)
      → ⟨ pr (⟪ fst x ⟫↪ m) (⟪ fst d ⟫↪ (fst f m)) ∈ fst G ⟩)

HalfA : (x d : S) → (⟪ fst x ⟫ ↪ ⟪ fst d ⟫) → Type (ℓ-suc ℓ)
HalfA x d f = Σ[ G ∈ S ] GraphOf x d f G

-- =====================================================================
-- W3, HALF B.  The four conjuncts from the membership readings, with
-- no ambient function.  InclGraph derives uniqueness and injectivity
-- from pair-out (src/L/InjChain.lagda.md:518-530).  Here they are
-- hypotheses, because a general graph is not a diagonal.
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
-- THE OBLIGATION.  HALF A has no producer.  Hole by design.
-- =====================================================================

amb-to-coded :
    (x : S) (ox : IsOrd (fst x)) → ⟨ ω ∈ˢ fst x ⟩
  → (d : S) → ⟨ fst d ∈ˢ fst x ⟩ → (⟨ fst d ∈ˢ ω ⟩ → Empty.⊥)
  → ∥ ⟪ fst x ⟫ ↪ ⟪ fst d ⟫ ∥₁
  → ∥ Σ[ F ∈ S ] InjCode F x d ∥₁
amb-to-coded = {!!}

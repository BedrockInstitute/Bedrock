{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.35] THE BOUND-FACT CONSTRUCTION, PRICED.
--
-- Every probe in this lineage takes the bound facts as hypotheses:
--   LeafBnd, OuterBnd, LeafFacts (src/ProbeDD25D5.agda), Bounds and
--   BoundOK (src/ProbeDD25CD.agda).  This probe CONSTRUCTS them at a
--   sealed carrier and measures the cost.
--
-- The construction has two layers, and this probe separates them.
--
--   LAYER 1, the READING LAYER (measured here).  From the satisfaction
--   of the BUILT leaf body `DefBody (suc zero)` at the leaf environment,
--   extract the code fact (c' is a key over the carrier, via the
--   delivered codeAt-out) and the graph witness (the table over the
--   carrier, via the delivered graphAt-out).  The leaf bound facts then
--   assemble from TWO site facts, stated once: codes-in-K (the code
--   set over A lies in K) and witness-vals-in-K (the values of the
--   graph-certified table over A lie in K).  Those site facts are the
--   substrate's code-set half, survey-priced in [LJ-1.34-R]; they are
--   NOT built here.  A pinned alternative, reading the value as the
--   delivered `Sat A (toS psi)` via graphAt-unique, measures at the
--   SAME cost, so the site fact's spelling does not move the price.
--
--   LAYER 2, the OUTER LAYER (re-measured here).  From the satisfaction
--   of the built `StepBody`, extract c in B1, w a recorded value, and
--   d = D0 w, via the delivered readers exactly as ProbeDD25CD's
--   discharge does.  The site facts are val-in-K and D0-in-K (the
--   recorded values and their definable powersets lie in K).
--
-- SECTION 3 is the Delta-0 question: the bounded restatement of the
-- code leaf, with its certificate.  It shows the certificate is a
-- SEPARATE obligation from the bound facts.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed; thrown away per D-1.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ135 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; ∃̇_; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∧; δ-≐; δ-∃∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; 𝒟ₒ )
open import L.Absoluteness {ℓ} using ( Δ₀-liftFo )
open import L.Coding.Base {ℓ} using ( Δ₀-prAt )
open import L.Coding.Model {ℓ}
  using ( prAtL; appAt-adequate )
open import L.Coding.Powerset {ℓ} lem
  using ( DefBody; DefAt-out; codeAt-out )
open import L.Coding.CodeSet {ℓ} lem
  using ( keyS; AllCodes; key∈AllCodes )
open import L.Coding.Graph {ℓ} lem using ( GraphWitAt; graphAt-out )
open import L.Coding.Sequence {ℓ} lem
  using ( StepBody; Records; PowOK )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

private
  sh3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  sh3 i = suc (suc (suc i))

-- =====================================================================
-- SECTION 1: THE LEAF BOUND FACTS, CONSTRUCTED.
--
-- Slot layout mirrors src/ProbeDD25D5.agda's G module.  The leaf
-- environment is (v' ∷ c' ∷ x ∷ δ) with δ : S ^ (5 + n).  The carrier
-- of the leaf is slot (suc zero) of δ; the K bound is slot
-- (suc (suc (suc (suc zero)))) of δ.
-- =====================================================================
module LeafBound {n : ℕ} (A : S) (δ : S ^ (5 + n)) where
  private
    K-slot : Fin (5 + n)
    K-slot = suc (suc (suc (suc zero)))

    -- The carrier of the leaf is the value w, pinned to the sealed A.
    qcar : Type (ℓ-suc ℓ)
    qcar = fst (lookup (suc zero) δ) ≡ fst A

    -- THE SITE FACTS.  The substrate's code-set half, stated once and
    -- not built here ([LJ-1.34-R] prices it at 0.2-0.5k, SURVEY).
    codes-in-K : Type (ℓ-suc ℓ)
    codes-in-K = (x : S) → ⟨ x ∈ˢ AllCodes A ⟩
               → ⟨ fst x ∈ fst (lookup K-slot δ) ⟩

    -- THE CLOSURE ROUTE (Devlin's K(u) shape): the values of the
    -- graph-certified table over the carrier lie in K.
    witness-vals-in-K : Type (ℓ-suc ℓ)
    witness-vals-in-K = (C T b c' v' : S) → fst b ≡ fst A
                      → ⟨ pr (fst c') (fst v') ∈ fst T ⟩
                      → ⟨ fst v' ∈ fst (lookup K-slot δ) ⟩

  -- THE READING LAYER, out direction: the satisfaction of the built
  -- leaf gives the code fact.  The code is a key over the carrier.
  code-read : qcar → (c' v' x : S)
            → ⟨ (v' ∷ c' ∷ x ∷ δ) ⊨ DefBody {5 + n} (suc zero) ⟩
            → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ]
                  (fst c' ≡ fst (keyS A ψ))) ∥₁
  code-read qc c' v' x h =
    codeAt-out A (suc zero) (sh3 (suc zero)) (v' ∷ c' ∷ x ∷ δ) qc (h .fst)

  -- THE READING LAYER, closure route: the graph witness over the
  -- carrier, via the delivered existence direction.
  graph-read : (c' v' x : S)
             → ⟨ (v' ∷ c' ∷ x ∷ δ) ⊨ DefBody {5 + n} (suc zero) ⟩
             → ∥ GraphWitAt (sh3 (suc zero)) (suc zero) zero
                  (v' ∷ c' ∷ x ∷ δ) ∥₁
  graph-read c' v' x h =
    graphAt-out (sh3 (suc zero)) (suc zero) zero (v' ∷ c' ∷ x ∷ δ) (h .snd .fst)

  -- The closure-route leaf bound facts.
  leaf-bnd : qcar → codes-in-K → witness-vals-in-K
           → (c' v' x : S)
           → ⟨ (v' ∷ c' ∷ x ∷ δ) ⊨ DefBody {5 + n} (suc zero) ⟩
           → ⟨ fst c' ∈ fst (lookup K-slot δ) ⟩
           × ⟨ fst v' ∈ fst (lookup K-slot δ) ⟩
  leaf-bnd qc ck wvk c' v' x h =
    PT.rec (isProp× (snd (fst c' ∈ fst (lookup K-slot δ)))
                    (snd (fst v' ∈ fst (lookup K-slot δ)))) step
      (code-read qc c' v' x h)
    where
    step : Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (fst c' ≡ fst (keyS A ψ))
         → ⟨ fst c' ∈ fst (lookup K-slot δ) ⟩
         × ⟨ fst v' ∈ fst (lookup K-slot δ) ⟩
    step (ψ , qc') =
        subst (λ t → ⟨ t ∈ fst (lookup K-slot δ) ⟩) (sym qc')
          (ck (keyS A ψ) (key∈AllCodes A ψ))
      , PT.rec (snd (fst v' ∈ fst (lookup K-slot δ))) vstep (graph-read c' v' x h)
      where
      vstep : GraphWitAt (sh3 (suc zero)) (suc zero) zero
                (v' ∷ c' ∷ x ∷ δ)
            → ⟨ fst v' ∈ fst (lookup K-slot δ) ⟩
      vstep (C , (T , (b , rest))) =
        wvk C T b c' v' (rest .fst ∙ qc) (rest .snd .snd .snd .fst)

-- =====================================================================
-- SECTION 2: THE OUTER BOUND FACTS, CONSTRUCTED.  The environment is
-- (d ∷ w ∷ c ∷ z ∷ γ); K is slot zero of γ.  The assembly is
-- ProbeDD25CD's discharge, with the K-membership as the site facts.
-- =====================================================================
module StepBound {n : ℕ} (γ : S ^ suc n) (v b f : Fin n) where
  private
    K V₁ B₁ F₁ : Fin (suc n)
    K  = zero
    V₁ = suc v
    B₁ = suc b
    F₁ = suc f

    -- THE SITE FACTS: the recorded values and their definable
    -- powersets lie in K.
    val-in-K : Type (ℓ-suc ℓ)
    val-in-K = (c w : S) → Records B₁ F₁ γ c w
             → ⟨ fst w ∈ fst (lookup K γ) ⟩

    D0-in-K : Type (ℓ-suc ℓ)
    D0-in-K = (x : S) → ⟨ fst x ∈ fst (lookup K γ) ⟩
            → ⟨ 𝒟ₒ (fst x) ∈ fst (lookup K γ) ⟩

  -- The outer bound facts: satisfiers of the built step body lie in
  -- B1 (the argument), K (the value) and K (its definable powerset).
  outer-bnd : PowOK B₁ F₁ γ → val-in-K → D0-in-K
            → (z c w d : S)
            → ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ StepBody B₁ F₁ ⟩
            → ⟨ fst c ∈ fst (lookup B₁ γ) ⟩
            × ( ⟨ fst w ∈ fst (lookup K γ) ⟩
              × ⟨ fst d ∈ fst (lookup K γ) ⟩ )
  outer-bnd ok vk dk z c w d h =
      h .fst
    , ( vk c w rec
      , subst (λ t → ⟨ t ∈ fst (lookup K γ) ⟩) (sym qd) (dk w (vk c w rec)) )
    where
    rec : Records B₁ F₁ γ c w
    rec = h .fst , subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc F₁))))
                                (suc (suc zero)) (suc zero)
                                (d ∷ w ∷ c ∷ z ∷ γ)) (h .snd .fst)

    qd : fst d ≡ 𝒟ₒ (fst w)
    qd = DefAt-out w zero (suc zero) (d ∷ w ∷ c ∷ z ∷ γ)
           (λ x x∈ → isL-trans {x = 𝒟ₒ (fst w)} {y = x} x∈ (ok c w rec))
           refl (h .snd .snd .fst)

-- =====================================================================
-- SECTION 3: THE DELTA-0 QUESTION.  The bounded restatement of the
-- code leaf, with its certificate.  The bound facts (sections 1 and 2)
-- are satisfaction-level; the certificate needs this restatement.
-- =====================================================================
module CodeLeafCert where
  Δ₀-prAtL : ∀ {m} (q u v : Fin m) → Δ₀ (prAtL q u v)
  Δ₀-prAtL q u v = Δ₀-liftFo _ (Δ₀-prAt q u v)

  -- The delivered keyArityAtL c k = ∃̇ (tagAtL (suc c) k zero), an
  -- UNBOUNDED existential.  The bounded restatement binds both the tag
  -- and its payload by K.
  keyArityBnd : ∀ {n} → Fin n → ℕ → Fin n → Formula S n
  keyArityBnd c k K =
    ∃̇∈ (var K)
      (∃̇∈ (var (suc K))
        ((var zero ≐ con (numeralL k))
         ∧̇ prAtL (suc (suc c)) zero (suc zero)))

  Δ₀-keyArityBnd : ∀ {n} (c : Fin n) (k : ℕ) (K : Fin n)
                 → Δ₀ (keyArityBnd c k K)
  Δ₀-keyArityBnd c k K =
    δ-∃∈ (δ-∃∈ (δ-∧ δ-≐ (Δ₀-prAtL (suc (suc c)) zero (suc zero))))

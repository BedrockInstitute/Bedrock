{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.152] Probe C.  THE CONTROL, and it is a verbatim copy.
--
-- The body below is `src/ProbeLJ1136A.agda` character for character.
-- ONLY the module name changed, so the file moves into this task's
-- directory.  [LJ-1.136] measured it at 254.22 s on 2026-08-13 at load
-- 5.83 (agents/tasks/LJ-1-136/lj-1.136-report.md:1057-1060).
--
-- WHY A CONTROL IS NEEDED.  The brief records that the machine moved
-- figures by up to 20 percent on 2026-08-13.  A cure measured against
-- yesterday's control is not measured.  Probe D is the same file with
-- ONE change, so C and D differ by that change and nothing else.
--
-- ABORT CRITERION: none.  This is a control, not a decision.
--
-- The header of the original follows.
--
-- ---------------------------------------------------------------------
-- [LJ-1.136] Probe A.  What does ONE write-direction cost?
--
-- [LJ-1.134] measured the READ direction: an L-element graph read back
-- as an honest function.  Route A' also needs the WRITE direction, at
-- every point where the chain BUILDS an injection rather than refutes
-- one.  agents/reports/lj-1.136-report.md section 3.1 lists six.
--
-- This probe builds the cheapest and most load-bearing of the six: the
-- IDENTITY graph on a set, as an element of L, with every conjunct of
-- Probe B's selection predicate proved.  It is load-bearing because it
-- is what supplies the chain's non-emptiness at delta = alpha: the
-- least-cardinal search starts by knowing that alpha injects into
-- itself, constructibly.
--
-- Tracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed to src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-152.ProbeLJ1152C {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Full {ℓ} lem using ( hasReplacementL )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; prʟ; prʟ-fst
        ; svAt; svAt-in; domAt; domAt-intro )

open import ProbeLJ1134A {ℓ} lem using ( injAt; injAt-in )

open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_; setIsSet )
open import Cubical.Data.Sigma using ( Σ≡Prop; _×_ )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf; ℩ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- ---------------------------------------------------------------------
-- THE WRITE DIRECTION, at the identity graph on an arbitrary L-set.
-- The set is a PARAMETER, so P-l is honoured: no type below names a
-- transparent presentation.
-- ---------------------------------------------------------------------

module IdGraph (a : S) where

  -- The description.  ONE formula, and it is a delivered one: "y is the
  -- ordered pair of x with itself".
  φ : Formula S 2
  φ = prAtL zero (suc zero) (suc zero)

  spec : (y x : S) → ⟨ (y ∷ x ∷ []) ⊨ φ ⟩ ≡ (fst y ≡ pr (fst x) (fst x))
  spec y x = cong ⟨_⟩ (prAtL-adequate zero (suc zero) (suc zero) (y ∷ x ∷ []))

  out : (y x : S) → ⟨ (y ∷ x ∷ []) ⊨ φ ⟩ → fst y ≡ pr (fst x) (fst x)
  out y x h = subst (λ T → T) (spec y x) h

  into : (y x : S) → fst y ≡ pr (fst x) (fst x) → ⟨ (y ∷ x ∷ []) ⊨ φ ⟩
  into y x e = subst (λ T → T) (sym (spec y x)) e

  -- Functionality: for every argument the description has exactly one
  -- solution.  This is what replacement demands and it is the whole
  -- obligation.
  fc : (x : S) → ⟨ x ∈ˢ a ⟩ → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ φ ⟩)
  fc x _ = (prʟ x x , into (prʟ x x) x (prʟ-fst x x)) , uniq
    where
    uniq : (w : Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ φ ⟩)
         → (prʟ x x , into (prʟ x x) x (prʟ-fst x x)) ≡ w
    uniq (y , h) = Σ≡Prop (λ z → snd ((z ∷ x ∷ []) ⊨ φ))
      (Σ≡Prop (λ z → snd (isL z)) (prʟ-fst x x ∙ sym (out y x h)))

  -- THE GRAPH, as an element of L.
  Q : S → Ω
  Q y = ⋁ S (λ x → (x ∈ˢ a) ⊓ ((y ∷ x ∷ []) ⊨ φ))

  G : S
  G = ℩ (hasReplacementL a φ fc)

  G-spec : (z : S) → (z ∈ˢ G) ≡ Q z
  G-spec = snd (fst (hasReplacementL a φ fc))

  -- The two readings of membership in the graph.
  G-out : (z : S) → ⟨ z ∈ˢ G ⟩
        → ∥ Σ[ x ∈ S ] (⟨ x ∈ˢ a ⟩ × (fst z ≡ pr (fst x) (fst x))) ∥₁
  G-out z h = PT.map (λ { (x , (m , p)) → x , (m , out z x p) })
                (subst ⟨_⟩ (G-spec z) h)

  G-in : (z x : S) → ⟨ x ∈ˢ a ⟩ → fst z ≡ pr (fst x) (fst x) → ⟨ z ∈ˢ G ⟩
  G-in z x m e = subst ⟨_⟩ (sym (G-spec z)) ∣ x , (m , into z x e) ∣₁

  -- The pair reading, specialised to the shape the conjuncts consume.
  pair-out : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
           → ∥ (fst x ≡ fst y) × ⟨ x ∈ˢ a ⟩ ∥₁
  pair-out x y h = PT.map step (G-out (prʟ x y) h')
    where
    h' : ⟨ prʟ x y ∈ˢ G ⟩
    h' = subst (λ w → ⟨ w ∈ fst G ⟩) (sym (prʟ-fst x y)) h
    step : Σ[ u ∈ S ] (⟨ u ∈ˢ a ⟩ × (fst (prʟ x y) ≡ pr (fst u) (fst u)))
         → (fst x ≡ fst y) × ⟨ x ∈ˢ a ⟩
    step (u , (m , e)) = (xu ∙ sym yu) , subst (λ w → ⟨ w ∈ fst a ⟩) (sym xu) m
      where
      q : (fst x ≡ fst u) × (fst y ≡ fst u)
      q = pr-inj (sym (prʟ-fst x y) ∙ e)
      xu = fst q
      yu = snd q

  -- =====================================================================
  -- THE FOUR CONJUNCTS of Probe B's selection predicate, PROVED.
  -- =====================================================================

  γ : S ^ 2
  γ = G ∷ a ∷ []

  sv : ⟨ γ ⊨ svAt zero ⟩
  sv = svAt-in zero γ (λ x y y' p q →
    PT.rec (setIsSet (fst y) (fst y'))
      (λ r → PT.rec (setIsSet (fst y) (fst y'))
        (λ r' → sym (fst r) ∙ fst r') (pair-out x y' q))
      (pair-out x y p))

  ij : ⟨ γ ⊨ injAt zero ⟩
  ij = injAt-in zero γ (λ y x x' p q →
    PT.rec (setIsSet (fst x) (fst x'))
      (λ r → PT.rec (setIsSet (fst x) (fst x'))
        (λ r' → fst r ∙ sym (fst r')) (pair-out x' y q))
      (pair-out x y p))

  dm : ⟨ γ ⊨ domAt zero (suc zero) ⟩
  dm = domAt-intro zero (suc zero) γ (λ x → fwd x , bwd x)
    where
    fwd : (x : S) → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst G) ⟩
        → ⟨ fst x ∈ fst a ⟩
    fwd x = PT.rec (snd (fst x ∈ fst a))
      (λ { (y , p) → PT.rec (snd (fst x ∈ fst a)) snd (pair-out x y p) })

    bwd : (x : S) → ⟨ fst x ∈ fst a ⟩
        → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst G) ⟩
    bwd x m = ∣ x , subst (λ w → ⟨ w ∈ fst G ⟩) (prʟ-fst x x)
                      (G-in (prʟ x x) x m (prʟ-fst x x)) ∣₁

  -- The range: every value lands back in a.  This is Probe B's fourth
  -- conjunct, and putting it inside the predicate is what section 16.3
  -- recorded.
  ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩ → ⟨ fst y ∈ fst a ⟩
  ran x y h = PT.rec (snd (fst y ∈ fst a))
    (λ r → subst (λ w → ⟨ w ∈ fst a ⟩) (fst r) (snd r)) (pair-out x y h)

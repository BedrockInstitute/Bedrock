{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.556]  The square law, inside L.
--
-- W3 IS SECTION 1, AND IT WAS WRITTEN FIRST AND TYPECHECKED ALONE.
-- The slice is agents/tasks/LJ-1-556/runs/W3.agda, run runs/w3-3.out
-- and runs/w3-4.out, exit 0 both.  Its two red predecessors are kept
-- as runs/w3-1.out and runs/w3-2.out.
--
-- THE OBLIGATION IS NOT INHABITED.  No term of this file is named
-- `square-inside-L`.  The stop is
-- agents/tasks/LJ-1-556/review-of-square-inside-L.md.  This file
-- carries NO hole and NO postulate, so every reduction in it is a
-- measurement and not a claim ([LJ-1.533]'s discipline, kept by
-- [LJ-1.549] and [LJ-1.552]).  Nothing lands in src/.
--
-- WHAT THIS FILE MEASURES, IN ONE LINE EACH.
--
--   Section 1.  W3 IS GO.  kappa x kappa IS an L-set at this frame,
--               with BOTH projections, and the second one is
--               UNTRUNCATED.  `sqL`, `sqL-in`, `sqL-out`.
--   Section 2.  A CONDITION ON THE TWO COMPONENTS INTERNALIZES AS A
--               FORMULA, and the carve out of Section 1 is then free.
--               Measured at the membership order, `ltFo` and `ltL`,
--               NOT transferred by analogy from Section 1.
--   Section 3.  THE OBLIGATION'S TYPE, WRITTEN OUT AND NOT INHABITED.
--               `InternalSquare` is what "an L-set injection of
--               kappa x kappa into kappa, coded" means here.
--   Section 4.  THE CORRECTED TARGET (D-10).  `SquareStep` carries the
--               induction hypothesis the tree's own ambient proof
--               spends, and the brief's type does not.  Also not
--               inhabited: naming it is the deliverable.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M8g" on this pane.  I
-- did not set it.  One Agda process at a time.  No heap event.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-556.Probe556 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
import FOL.ZFModel
open import FOL.Syntax using ( Formula; var; con; ∃̇∈; _∈̇_; _∧̇_ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Cardinal {ℓ} lem using ( IsCardinalL; InjCode )
open import L.Coding.Model {ℓ} using ( prAtL; prAtL-adequate; prʟ; prʟ-fst )
open import L.InjChain {ℓ} lem using ( module StageBound )

open import Cubical.Data.Sigma using ( _×_; Σ≡Prop; ΣPathP )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Foundations.Prelude using ( subst2 )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- SECTION 1.  W3, AND IT IS GO.
--
--   kappa x kappa IS an L-set at this frame.  The route is the one two
--   chapters already use for exactly this shape: `StageBound`
--   (src/L/InjChain.lagda.md:75) bounds the coded pairs, and
--   `hasSeparationL` (src/L/Axioms/Full.lagda.md:144) carves the
--   product out of the bound.  Neither device is new here, and neither
--   is a transfer by analogy: both were run at THIS site.
--
--   The second reading is UNTRUNCATED, and that matters downstream: a
--   consumer of the product needs the two components as INDICES, not
--   merely their existence.  `pr-inj` (src/V/Coding.lagda.md:178) and
--   `↪-inj` make `Comp` a proposition, so the truncation comes off
--   with no choice and no extra hypothesis.
-- =====================================================================

module Square (κ : S) where

  -- Every member of kappa, as an element of L.
  toκ : ⟪ fst κ ⟫ → S
  toκ m = ⟪ fst κ ⟫↪ m
        , isL-trans {x = fst κ} {y = ⟪ fst κ ⟫↪ m} (member (fst κ) m) (snd κ)

  Ix : Type ℓ
  Ix = ⟪ fst κ ⟫ × ⟪ fst κ ⟫

  pw : Ix → S
  pw (m , n) = prʟ (toκ m) (toκ n)

  private
    module SB = StageBound Ix pw

  -- "z is the ordered pair of some member of kappa and some member of
  -- kappa."  One formula, one free place, one constant named.
  sqFo : Formula S 1
  sqFo = ∃̇∈ (con κ) (∃̇∈ (con κ)
           (prAtL (suc (suc zero)) (suc zero) zero))

  private
    sqFo-read : (z : S) → ⟨ (z ∷ []) ⊨ sqFo ⟩
              → ∥ Σ[ u ∈ S ] Σ[ v ∈ S ]
                    (⟨ fst u ∈ fst κ ⟩ × ⟨ fst v ∈ fst κ ⟩
                     × (fst z ≡ pr (fst u) (fst v))) ∥₁
    sqFo-read z h = PT.rec squash₁ outer h
      where
      outer : (Σ[ u ∈ S ] (⟨ fst u ∈ fst κ ⟩
                × ⟨ (u ∷ z ∷ []) ⊨ ∃̇∈ (con κ) (prAtL (suc (suc zero)) (suc zero) zero) ⟩))
            → ∥ Σ[ u ∈ S ] Σ[ v ∈ S ]
                  (⟨ fst u ∈ fst κ ⟩ × ⟨ fst v ∈ fst κ ⟩
                   × (fst z ≡ pr (fst u) (fst v))) ∥₁
      outer (u , (u∈ , hu)) = PT.rec squash₁ inner hu
        where
        inner : (Σ[ v ∈ S ] (⟨ fst v ∈ fst κ ⟩
                  × ⟨ (v ∷ u ∷ z ∷ []) ⊨ prAtL (suc (suc zero)) (suc zero) zero ⟩))
              → ∥ Σ[ u' ∈ S ] Σ[ v ∈ S ]
                    (⟨ fst u' ∈ fst κ ⟩ × ⟨ fst v ∈ fst κ ⟩
                     × (fst z ≡ pr (fst u') (fst v))) ∥₁
        inner (v , (v∈ , hv)) = ∣ u , (v , (u∈ , (v∈ , eq))) ∣₁
          where
          eq : fst z ≡ pr (fst u) (fst v)
          eq = subst ⟨_⟩
                 (prAtL-adequate (suc (suc zero)) (suc zero) zero
                   (v ∷ u ∷ z ∷ [])) hv

    sqFo-write : (u v : S) → ⟨ fst u ∈ fst κ ⟩ → ⟨ fst v ∈ fst κ ⟩
               → ⟨ (prʟ u v ∷ []) ⊨ sqFo ⟩
    sqFo-write u v u∈ v∈ = ∣ u , (u∈ , ∣ v , (v∈ , at) ∣₁) ∣₁
      where
      at : ⟨ (v ∷ u ∷ prʟ u v ∷ []) ⊨ prAtL (suc (suc zero)) (suc zero) zero ⟩
      at = subst ⟨_⟩
             (sym (prAtL-adequate (suc (suc zero)) (suc zero) zero
                    (v ∷ u ∷ prʟ u v ∷ [])))
             (prʟ-fst u v)

  -- THE SET.  Sealed at the point it is made (P-i): every consumer
  -- wants `fst sqL` as an atom.
  opaque
    sqL : S
    sqL = fst (fst (hasSeparationL SB.bnd sqFo))

    sqL-spec : (z : S) → (z ∈ˢ sqL)
             ≡ ((z ∈ˢ SB.bnd) ⊓ ((z ∷ []) ⊨ sqFo))
    sqL-spec = snd (fst (hasSeparationL SB.bnd sqFo))

  -- READING ONE.  The pair of two members of kappa is a member.
  sqL-in : (m n : ⟪ fst κ ⟫) → ⟨ fst (pw (m , n)) ∈ fst sqL ⟩
  sqL-in m n = subst ⟨_⟩ (sym (sqL-spec (pw (m , n))))
    ( SB.below (m , n)
    , sqFo-write (toκ m) (toκ n)
        (member (fst κ) m) (member (fst κ) n) )

  Comp : S → Type (ℓ-suc ℓ)
  Comp z = Σ[ p ∈ Ix ] (fst z ≡ fst (pw p))

  private
    isPropComp : (z : S) → isProp (Comp z)
    isPropComp z (p , e) (q , e') = path
      where
      raw : pr (⟪ fst κ ⟫↪ (fst p)) (⟪ fst κ ⟫↪ (snd p))
          ≡ pr (⟪ fst κ ⟫↪ (fst q)) (⟪ fst κ ⟫↪ (snd q))
      raw = sym (prʟ-fst (toκ (fst p)) (toκ (snd p)))
          ∙ sym e ∙ e' ∙ prʟ-fst (toκ (fst q)) (toκ (snd q))

      split : (⟪ fst κ ⟫↪ (fst p) ≡ ⟪ fst κ ⟫↪ (fst q))
            × (⟪ fst κ ⟫↪ (snd p) ≡ ⟪ fst κ ⟫↪ (snd q))
      split = pr-inj raw

      pq : p ≡ q
      pq = ΣPathP ( ↪-inj {a = fst κ} (fst split)
                  , ↪-inj {a = fst κ} (snd split) )

      path : (p , e) ≡ (q , e')
      path = Σ≡Prop (λ r → setIsSet (fst z) (fst (pw r))) pq

  -- READING TWO, AND IT IS UNTRUNCATED.
  sqL-out : (z : S) → ⟨ fst z ∈ fst sqL ⟩ → Comp z
  sqL-out z h = PT.rec (isPropComp z) step
    (sqFo-read z (snd (subst ⟨_⟩ (sqL-spec z) h)))
    where
    step : (Σ[ u ∈ S ] Σ[ v ∈ S ]
             (⟨ fst u ∈ fst κ ⟩ × ⟨ fst v ∈ fst κ ⟩
              × (fst z ≡ pr (fst u) (fst v))))
         → Comp z
    step (u , (v , (u∈ , (v∈ , e)))) = (fu .fst , fv .fst) , path
      where
      fu = fiber (fst κ) u∈
      fv = fiber (fst κ) v∈
      path : fst z ≡ fst (pw (fu .fst , fv .fst))
      path = e
           ∙ sym (cong₂ pr (fu .snd) (fv .snd))
           ∙ sym (prʟ-fst (toκ (fu .fst)) (toκ (fv .fst)))

  -- ===================================================================
  -- SECTION 2.  A CONDITION ON THE TWO COMPONENTS IS A FORMULA, AND
  --             THE CARVE IS THEN FREE.
  --
  --   `L.Coding.Sequence.RecShape` (src/L/Coding/Sequence.lagda.md:281)
  --   takes its step as a FORMULA and never as a set, so the order data
  --   the ambient collapse consults does not have to become an L-set at
  --   all: it has to become a formula on the two components.  This
  --   section measures that at ONE condition, the membership order,
  --   rather than asserting it of every condition by analogy (AGENTS.md
  --   Boundary: a measured cure does not transfer by analogy).
  --
  --   The set is built too, because it costs one more separation and it
  --   is the shape a consumer that DOES want a set would ask for.
  -- ===================================================================

  ltFo : Formula S 1
  ltFo = ∃̇∈ (con κ) (∃̇∈ (con κ)
           ( prAtL (suc (suc zero)) (suc zero) zero
           ∧̇ (var (suc zero) ∈̇ var zero) ))

  private
    ltFo-read : (z : S) → ⟨ (z ∷ []) ⊨ ltFo ⟩
              → ∥ Σ[ u ∈ S ] Σ[ v ∈ S ]
                    (⟨ fst u ∈ fst κ ⟩ × ⟨ fst v ∈ fst κ ⟩
                     × (fst z ≡ pr (fst u) (fst v))
                     × ⟨ fst u ∈ fst v ⟩) ∥₁
    ltFo-read z h = PT.rec squash₁ outer h
      where
      outer : (Σ[ u ∈ S ] (⟨ fst u ∈ fst κ ⟩
                × ⟨ (u ∷ z ∷ []) ⊨ ∃̇∈ (con κ)
                      ( prAtL (suc (suc zero)) (suc zero) zero
                      ∧̇ (var (suc zero) ∈̇ var zero) ) ⟩))
            → ∥ Σ[ u ∈ S ] Σ[ v ∈ S ]
                  (⟨ fst u ∈ fst κ ⟩ × ⟨ fst v ∈ fst κ ⟩
                   × (fst z ≡ pr (fst u) (fst v))
                   × ⟨ fst u ∈ fst v ⟩) ∥₁
      outer (u , (u∈ , hu)) = PT.rec squash₁ inner hu
        where
        inner : (Σ[ v ∈ S ] (⟨ fst v ∈ fst κ ⟩
                  × ⟨ (v ∷ u ∷ z ∷ []) ⊨
                        ( prAtL (suc (suc zero)) (suc zero) zero
                        ∧̇ (var (suc zero) ∈̇ var zero) ) ⟩))
              → ∥ Σ[ u' ∈ S ] Σ[ v ∈ S ]
                    (⟨ fst u' ∈ fst κ ⟩ × ⟨ fst v ∈ fst κ ⟩
                     × (fst z ≡ pr (fst u') (fst v))
                     × ⟨ fst u' ∈ fst v ⟩) ∥₁
        inner (v , (v∈ , (hv , hlt))) = ∣ u , (v , (u∈ , (v∈ , (eq , hlt)))) ∣₁
          where
          eq : fst z ≡ pr (fst u) (fst v)
          eq = subst ⟨_⟩
                 (prAtL-adequate (suc (suc zero)) (suc zero) zero
                   (v ∷ u ∷ z ∷ [])) hv

    ltFo-write : (u v : S) → ⟨ fst u ∈ fst κ ⟩ → ⟨ fst v ∈ fst κ ⟩
               → ⟨ fst u ∈ fst v ⟩ → ⟨ (prʟ u v ∷ []) ⊨ ltFo ⟩
    ltFo-write u v u∈ v∈ lt = ∣ u , (u∈ , ∣ v , (v∈ , (at , lt)) ∣₁) ∣₁
      where
      at : ⟨ (v ∷ u ∷ prʟ u v ∷ []) ⊨ prAtL (suc (suc zero)) (suc zero) zero ⟩
      at = subst ⟨_⟩
             (sym (prAtL-adequate (suc (suc zero)) (suc zero) zero
                    (v ∷ u ∷ prʟ u v ∷ [])))
             (prʟ-fst u v)

  -- THE ORDER, AS A SET OF L.  One separation out of Section 1's set.
  opaque
    ltL : S
    ltL = fst (fst (hasSeparationL sqL ltFo))

    ltL-spec : (z : S) → (z ∈ˢ ltL)
             ≡ ((z ∈ˢ sqL) ⊓ ((z ∷ []) ⊨ ltFo))
    ltL-spec = snd (fst (hasSeparationL sqL ltFo))

  ltL-in : (m n : ⟪ fst κ ⟫) → ⟨ ⟪ fst κ ⟫↪ m ∈ ⟪ fst κ ⟫↪ n ⟩
         → ⟨ fst (pw (m , n)) ∈ fst ltL ⟩
  ltL-in m n lt = subst ⟨_⟩ (sym (ltL-spec (pw (m , n))))
    ( sqL-in m n
    , ltFo-write (toκ m) (toκ n)
        (member (fst κ) m) (member (fst κ) n) lt )

  ltL-out : (z : S) → ⟨ fst z ∈ fst ltL ⟩
          → Σ[ p ∈ Ix ] ( (fst z ≡ fst (pw p))
                        × ∥ ⟨ ⟪ fst κ ⟫↪ (fst p) ∈ ⟪ fst κ ⟫↪ (snd p) ⟩ ∥₁ )
  ltL-out z h = c .fst , (c .snd , lt)
    where
    both = subst ⟨_⟩ (ltL-spec z) h
    c : Comp z
    c = sqL-out z (both .fst)

    lt : ∥ ⟨ ⟪ fst κ ⟫↪ (c .fst .fst) ∈ ⟪ fst κ ⟫↪ (c .fst .snd) ⟩ ∥₁
    lt = PT.map step (ltFo-read z (both .snd))
      where
      step : (Σ[ u ∈ S ] Σ[ v ∈ S ]
               (⟨ fst u ∈ fst κ ⟩ × ⟨ fst v ∈ fst κ ⟩
                × (fst z ≡ pr (fst u) (fst v))
                × ⟨ fst u ∈ fst v ⟩))
           → ⟨ ⟪ fst κ ⟫↪ (c .fst .fst) ∈ ⟪ fst κ ⟫↪ (c .fst .snd) ⟩
      step (u , (v , (u∈ , (v∈ , (e , hlt))))) =
        subst2 (λ a b → ⟨ a ∈ b ⟩) (fst q) (snd q) hlt
        where
        q : (fst u ≡ ⟪ fst κ ⟫↪ (c .fst .fst))
          × (fst v ≡ ⟪ fst κ ⟫↪ (c .fst .snd))
        q = pr-inj (sym e ∙ c .snd
                    ∙ prʟ-fst (toκ (c .fst .fst)) (toκ (c .fst .snd)))

-- =====================================================================
-- SECTION 3.  THE OBLIGATION'S TYPE, WRITTEN OUT AND NOT INHABITED.
--
--   `InjCode F a b` (src/L/Cardinal.lagda.md:222) is what a CODED
--   injection means here: four conjuncts, single-valued, domain `a`,
--   injective, values in `b`.  So "an L-set injection of kappa x kappa
--   into kappa, coded" is `InjCode F (sqL kappa) kappa`, with the
--   domain object delivered by Section 1.
--
--   NOTHING BELOW INHABITS IT.  Naming the type is what Section 4 then
--   corrects.
-- =====================================================================

InternalSquare : S → Type (ℓ-suc ℓ)
InternalSquare κ = ∥ Σ[ F ∈ S ] InjCode F (Square.sqL κ) κ ∥₁

-- The brief's type, written out exactly, and NOT inhabited.
BriefTarget : Type (ℓ-suc ℓ)
BriefTarget = (κ : S) → IsOrd (fst κ) → IsCardinalL κ → InternalSquare κ

-- =====================================================================
-- SECTION 4.  THE CORRECTED TARGET (D-10).
--
--   The tree's ambient square law is NOT a per-ordinal theorem.  Its
--   hypothesis is `Init` (src/L/Ordinal/SquareLaw.lagda.md:692), whose
--   fourth conjunct is `noinj²`: no injection of the index into an
--   infinite MEMBER'S SQUARE.  The tree derives that conjunct exactly
--   once, at src/L/SquareLawClosed.lagda.md:96 (`clause4-at-kappa`),
--   and the derivation takes TWO inputs:
--
--     * `κ-min-atL` (src/L/SquareLawClosed.lagda.md:85), the AMBIENT
--       leastness of the ambient least cardinal; and
--     * `ih` (src/L/SquareLawClosed.lagda.md:98), THE SQUARE LAW AT
--       EVERY SMALLER INFINITE ORDINAL.
--
--   `ih` is the induction hypothesis of `sq-trunc-closed`
--   (src/L/SquareLawClosed.lagda.md:329), an ∈-induction over all
--   ordinals with four cases.  `IsCardinalL κ`
--   (src/L/Cardinal.lagda.md:234) supplies NEITHER: it refutes a coded
--   injection of kappa into a SMALLER SET, not an injection of kappa
--   into a smaller set's SQUARE, and the gap between the two IS the
--   square law at that smaller set.
--
--   So the brief's type is under-hypothesized against every route the
--   tree has.  The corrected target carries the induction hypothesis.
--   IT IS NOT INHABITED HERE EITHER: the point of writing it is that
--   the next brief funds the right thing.
-- =====================================================================

SquareStep : Type (ℓ-suc ℓ)
SquareStep =
    (κ : S) → IsOrd (fst κ)
  → IsCardinalL κ
  → ( (β : S) → IsOrd (fst β) → ⟨ fst β ∈ fst κ ⟩ → InternalSquare β )
  → InternalSquare κ

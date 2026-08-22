{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.556] W3.  THE PAIRING THE INTERNAL INJECTION MUST USE.
--
-- WRITTEN FIRST AND TYPECHECKED ALONE, before any other Agda of this
-- task, exactly as the brief orders.  No hole, no postulate.
--
-- The brief names the widest unmeasured term:
--
--     -- kappa x kappa as an L-SET, with its two projections, TYPE ONLY
--
-- "TYPE ONLY" is the floor and not the ceiling.  A type alone cannot
-- answer the question the brief attaches to it, which is "if the
-- product is not an L-set at this frame, the obligation is about a
-- different object".  So this slice INHABITS the type: the set, and
-- both readings of its membership.
--
--   sqL      : the L-set of Kuratowski pairs of two members of kappa.
--   sqL-in   : any two members of kappa give a member of sqL.
--   sqL-out  : any member of sqL IS such a pair, UNTRUNCATED, because
--              `pr-inj` makes the two components unique.
--
-- The route is the one two chapters already use for exactly this
-- shape: `StageBound` for the bound (src/L/InjChain.lagda.md:75) and
-- `hasSeparationL` for the carve (src/L/Axioms/Full.lagda.md:144).
-- Neither is new here.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M8g" on this pane.  I
-- did not set it.  One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-556.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
import FOL.ZFModel
open import FOL.Syntax using ( Formula; var; con; ∃̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Coding.Model {ℓ} using ( prAtL; prAtL-adequate; prʟ; prʟ-fst )
open import L.InjChain {ℓ} lem using ( module StageBound )

open import Cubical.Data.Sigma using ( _×_; Σ≡Prop; ΣPathP )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- W3.  kappa x kappa AS AN L-SET, WITH ITS TWO PROJECTIONS.
-- =====================================================================

module Square (κ : S) where

  -- Every member of kappa, as an element of L.
  toκ : ⟪ fst κ ⟫ → S
  toκ m = ⟪ fst κ ⟫↪ m
        , isL-trans {x = fst κ} {y = ⟪ fst κ ⟫↪ m} (member (fst κ) m) (snd κ)

  private
    Ix : Type ℓ
    Ix = ⟪ fst κ ⟫ × ⟪ fst κ ⟫

    pw : Ix → S
    pw (m , n) = prʟ (toκ m) (toκ n)

    module SB = StageBound Ix pw

  -- "z is the ordered pair of some member of kappa and some member of
  -- kappa."  One formula, one free place, no numeral named.
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

  -- READING TWO, AND IT IS UNTRUNCATED.  The two components of a
  -- Kuratowski pair are unique (`pr-inj`), and a member of kappa is
  -- determined by its underlying set (`fiber`), so the Sigma below is
  -- a proposition and the truncation comes off.
  private
    Comp : S → Type (ℓ-suc ℓ)
    Comp z = Σ[ p ∈ ⟪ fst κ ⟫ × ⟪ fst κ ⟫ ] (fst z ≡ fst (pw p))

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

  -- READING TWO, AND IT IS UNTRUNCATED.  The two components of a
  -- Kuratowski pair are unique (`pr-inj`), and a member index is
  -- determined by its underlying set (`↪-inj`), so `Comp` is a
  -- proposition and the truncation comes off.
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

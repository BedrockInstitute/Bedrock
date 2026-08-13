{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.40] THE ROW AGREEMENT, PROTOTYPED.
--
-- The repaired rows must be consumed in the same dispatch.  This probe
-- builds the row agreement machinery: the bounded leaves against the
-- machine's leaves, under the site facts.  It is ported to the master
-- once green.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed; thrown away per D-1.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ140A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _⇒̇_; ∃̇_; ∃̇∈; ∀̇∈; ⊥̇ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ}
  using ( prAtL; appAt; appAt-adequate; consAtL; sucAtL
        ; extAt; extAt-out; extAt-in; extAt-in-both
        ; unClauseAt; binClauseAt
        ; arityTagAtL; arityTagAtL-adequate; arityTagPairAtL
        ; arityTagPairAtL-adequate; tagAtL-adequate; tagPairAtL-adequate
        ; prAtL-adequate; prʟ; prʟ-fst
        ; emptyAt; sameAt; diffAt; interAt; unionAt; implAt
        ; subValAt; subValSuccAt; envSetAt; tmValAt; envOverAt; svAt; domAt
        ; valuesInAt; pairsInAt; pairsIn-out
        ; domAt-out
        ; botClauseAt; topClauseAt; negClauseAt; forallClauseAt
        ; existClauseAt; andClauseAt; orClauseAt; impClauseAt
        ; memClauseAt; eqClauseAt; allInClauseAt; exInClauseAt )
open import L.Condensation {ℓ} lem
  using ( extAtB; arTagB; arTagPairB; tmValB; subValB; subValSuccB
        ; envHypU; envHypT; envHypB2; envHypB2T
        ; interB; unionB; diffB; sameB; emptyB; implB
        ; atomBodyB; bndBodyAll; bndBodyEx; propBodyB
        ; unBareAt; unEnvAt; unFullAt; binFullAt; binEnvAt
        ; envBndGen
        ; Bot; Top; Neg; Forall; And; Or; Imp; Mem; Eq; AllIn; ExIn
        ; Exist )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import Cubical.Data.Nat using ( _+_ )
import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- SECTION 1: THE EXTENSION-FRAME TRANSFER.  From ProbeDD25E2.
-- =====================================================================
extAtB→extAt : ∀ {n} (y K : Fin n) (φB φ : Formula S (suc n)) (γ : S ^ n)
  → ((z : S) → ⟨ (z ∷ γ) ⊨ φB ⟩ → ⟨ (z ∷ γ) ⊨ φ ⟩)
  → ((z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ (z ∷ γ) ⊨ φB ⟩)
  → ((z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  → ⟨ γ ⊨ extAtB y K φB ⟩ → ⟨ γ ⊨ extAt y φ ⟩
extAtB→extAt y K φB φ γ fwd bwd inK h =
  extAt-in-both y φ γ
    (λ z z∈ → fwd z (h .fst z z∈))
    (λ z hz → h .snd z (inK z hz) (bwd z hz))

extAt→extAtB : ∀ {n} (y K : Fin n) (φB φ : Formula S (suc n)) (γ : S ^ n)
  → ((z : S) → ⟨ (z ∷ γ) ⊨ φB ⟩ → ⟨ (z ∷ γ) ⊨ φ ⟩)
  → ((z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ (z ∷ γ) ⊨ φB ⟩)
  → ⟨ γ ⊨ extAt y φ ⟩ → ⟨ γ ⊨ extAtB y K φB ⟩
extAt→extAtB y K φB φ γ fwd bwd h =
    (λ z z∈ → bwd z (h .fst z z∈))
  , (λ z _ hz → h .snd z (fwd z hz))

-- =====================================================================
-- SECTION 2: THE UNARY SHAPE TRANSFER.  The story's bounded arTagB
-- against the machine's arityTagAtL, at the 4-depth environment
-- yc ∷ a ∷ ar ∷ c ∷ γ.  Site facts: the tag column holds the numeral,
-- and the numeral's inner code lies in K.
-- =====================================================================
module UnaryShape {m : ℕ} (tag K : Fin m) (k : ℕ) (γ : S ^ (4 + m)) where
  -- The tag column (a slot of γ) holds the numeral.
  tagEq : Type (ℓ-suc ℓ)
  tagEq = fst (lookup (suc (suc (suc (suc tag)))) γ) ≡ fst (numeralL k)

  -- The numeral lies in K.
  numK : Type (ℓ-suc ℓ)
  numK = ⟨ fst (numeralL k) ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩

  -- The inner code z = pr #k a lies in K, for every payload a.
  innerK : Type (ℓ-suc ℓ)
  innerK = (a : S) → ⟨ fst (prʟ (numeralL k) a) ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩

  -- OUT: the story's bounded shape gives the machine's shape.
  out : tagEq → ⟨ γ ⊨ arTagB tag K ⟩
      → ⟨ γ ⊨ arityTagAtL (suc (suc (suc zero))) (suc (suc zero)) k (suc zero) ⟩
  out te h = transport (cong fst (sym (arityTagAtL-adequate (suc (suc (suc zero)))
                         (suc (suc zero)) k (suc zero) γ))) target
    where
    target : fst (lookup (suc (suc (suc zero))) γ)
           ≡ pr (fst (lookup (suc (suc zero)) γ))
                (pr (# k) (fst (lookup (suc zero) γ)))
    target = PT.rec (setIsSet _ _)
      (λ { (z , (z∈ , (p , kz))) → PT.rec (setIsSet _ _)
        (λ { (t , (t∈ , (tt , zt))) →
          let a₀ = fst (lookup (suc zero) γ)
              ar₀ = fst (lookup (suc (suc zero)) γ)
              p' : fst (lookup (suc (suc (suc (suc zero)))) (z ∷ γ))
                  ≡ pr (fst (lookup (suc (suc (suc zero))) (z ∷ γ)))
                       (fst (lookup zero (z ∷ γ)))
              p' = transport (cong fst (prAtL-adequate (suc (suc (suc (suc zero))))
                    (suc (suc (suc zero))) zero (z ∷ γ))) p
              zt' : fst (lookup (suc zero) (t ∷ z ∷ γ))
                   ≡ pr (fst (lookup zero (t ∷ z ∷ γ)))
                        (fst (lookup (suc (suc (suc zero))) (t ∷ z ∷ γ)))
              zt' = transport (cong fst (prAtL-adequate (suc zero) zero (suc (suc (suc zero)))
                    (t ∷ z ∷ γ))) zt
              tt' : fst (lookup zero (t ∷ z ∷ γ))
                  ≡ fst (lookup (suc (suc (suc (suc tag)))) γ)
              tt' = tt
          in p' ∙ cong (pr ar₀) zt'
               ∙ cong (λ w → pr ar₀ (pr w a₀))
                      (tt' ∙ te ∙ numeralL-fst k) })
        kz })
      h

  -- IN: the machine's shape gives the story's bounded shape, with the
  -- inner code and the numeral lying in K.
  in' : tagEq → numK → innerK → ⟨ γ ⊨ arityTagAtL (suc (suc (suc zero))) (suc (suc zero)) k (suc zero) ⟩
      → ⟨ γ ⊨ arTagB tag K ⟩
  in' te nk ik h = PT.rec squash₁
    (λ { (z , (p , tz)) →
      let p' : fst (lookup (suc (suc (suc (suc zero)))) (z ∷ γ))
              ≡ pr (fst (lookup (suc (suc (suc zero))) (z ∷ γ)))
                   (fst (lookup zero (z ∷ γ)))
          p' = transport (cong fst (prAtL-adequate (suc (suc (suc (suc zero))))
                (suc (suc (suc zero))) zero (z ∷ γ))) p
          tz' : fst (lookup zero (z ∷ γ))
               ≡ pr (# k) (fst (lookup (suc (suc zero)) (z ∷ γ)))
          tz' = transport (cong fst (tagAtL-adequate zero k (suc (suc zero)) (z ∷ γ))) tz
          a₀ : S
          a₀ = lookup (suc zero) γ
          zK : ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩
          zK = subst (λ w → ⟨ w ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩)
                 (sym tz')
                 (subst (λ w → ⟨ w ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩)
                   (prʟ-fst (numeralL k) a₀ ∙ cong₂ pr (numeralL-fst k) refl)
                   (ik a₀))
      in ∣ z , ( zK
               , ( p
                 , ∣ numeralL k
                   , ( nk
                     , ( sym te
                        , transport (cong fst (sym (prAtL-adequate (suc zero) zero (suc (suc (suc zero)))
                               (numeralL k ∷ z ∷ γ))))
                            (tz' ∙ cong₂ pr (sym (numeralL-fst k)) refl) ) )
                   ∣₁ ) ) ∣₁ })
    h

-- =====================================================================
-- SECTION 2B: THE BINARY SHAPE TRANSFER.  The story's bounded
-- arTagPairB against the machine's arityTagPairAtL, at the 5-depth
-- environment yc ∷ b ∷ a ∷ ar ∷ c ∷ γ.
-- =====================================================================
module BinaryShape {m : ℕ} (tag K : Fin m) (k : ℕ) (γ : S ^ (5 + m)) where
  tagEq : Type (ℓ-suc ℓ)
  tagEq = fst (lookup (suc (suc (suc (suc (suc tag))))) γ) ≡ fst (numeralL k)

  numK : Type (ℓ-suc ℓ)
  numK = ⟨ fst (numeralL k) ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩

  innerK : Type (ℓ-suc ℓ)
  innerK = (a b : S) → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩

  pairK : Type (ℓ-suc ℓ)
  pairK = (a b : S) → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩

  out : tagEq → ⟨ γ ⊨ arTagPairB tag K ⟩
      → ⟨ γ ⊨ arityTagPairAtL (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) k
                               (suc (suc zero)) (suc zero) ⟩
  out te h = transport (cong fst (sym (arityTagPairAtL-adequate (suc (suc (suc (suc zero))))
                         (suc (suc (suc zero))) k (suc (suc zero)) (suc zero) γ))) target
    where
    target : fst (lookup (suc (suc (suc (suc zero)))) γ)
           ≡ pr (fst (lookup (suc (suc (suc zero))) γ))
                (pr (# k) (pr (fst (lookup (suc (suc zero)) γ)) (fst (lookup (suc zero) γ))))
    target = PT.rec (setIsSet _ _)
      (λ { (z , (z∈ , (p , kz))) → PT.rec (setIsSet _ _)
        (λ { (t , (t∈ , (tt , kt))) → PT.rec (setIsSet _ _)
          (λ { (w , (w∈ , (zt , wb))) →
            let a₀ = fst (lookup (suc (suc zero)) γ)
                b₀ = fst (lookup (suc zero) γ)
                ar₀ = fst (lookup (suc (suc (suc zero))) γ)
                p' : fst (lookup (suc (suc (suc (suc (suc zero))))) (z ∷ γ))
                    ≡ pr (fst (lookup (suc (suc (suc (suc zero)))) (z ∷ γ)))
                         (fst (lookup zero (z ∷ γ)))
                p' = transport (cong fst (prAtL-adequate (suc (suc (suc (suc (suc zero)))))
                      (suc (suc (suc (suc zero)))) zero (z ∷ γ))) p
                zt' : fst (lookup (suc (suc zero)) (w ∷ t ∷ z ∷ γ))
                     ≡ pr (fst (lookup (suc zero) (w ∷ t ∷ z ∷ γ)))
                          (fst (lookup zero (w ∷ t ∷ z ∷ γ)))
                zt' = transport (cong fst (prAtL-adequate (suc (suc zero)) (suc zero) zero
                      (w ∷ t ∷ z ∷ γ))) zt
                wb' : fst (lookup zero (w ∷ t ∷ z ∷ γ))
                     ≡ pr (fst (lookup (suc (suc (suc (suc (suc zero))))) (w ∷ t ∷ z ∷ γ)))
                          (fst (lookup (suc (suc (suc (suc zero)))) (w ∷ t ∷ z ∷ γ)))
                wb' = transport (cong fst (prAtL-adequate zero (suc (suc (suc (suc (suc zero)))))
                      (suc (suc (suc (suc zero)))) (w ∷ t ∷ z ∷ γ))) wb
                tt' : fst (lookup (suc zero) (w ∷ t ∷ z ∷ γ))
                    ≡ fst (lookup (suc (suc (suc (suc (suc tag))))) γ)
                tt' = tt
            in p' ∙ cong (pr ar₀) (zt' ∙ cong (pr (fst (lookup (suc zero) (w ∷ t ∷ z ∷ γ)))) wb')
                 ∙ cong (λ v → pr ar₀ (pr v (pr a₀ b₀)))
                        (tt' ∙ te ∙ numeralL-fst k) })
          kt })
        kz })
      h

  in' : tagEq → numK → innerK → pairK
      → ⟨ γ ⊨ arityTagPairAtL (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) k
                               (suc (suc zero)) (suc zero) ⟩
      → ⟨ γ ⊨ arTagPairB tag K ⟩
  in' te nk ik pk h = PT.rec squash₁
    (λ { (z , (p , tz)) →
      let a₀ : S
          a₀ = lookup (suc (suc zero)) γ
          b₀ : S
          b₀ = lookup (suc zero) γ
          tz' : fst (lookup zero (z ∷ γ))
               ≡ pr (# k) (pr (fst (lookup (suc (suc (suc zero))) (z ∷ γ)))
                              (fst (lookup (suc (suc zero)) (z ∷ γ))))
          tz' = transport (cong fst (tagPairAtL-adequate zero k (suc (suc (suc zero))) (suc (suc zero)) (z ∷ γ))) tz
          zK : ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩
          zK = subst (λ w → ⟨ w ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩)
                 (sym tz')
                 (subst (λ w → ⟨ w ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩)
                   (prʟ-fst (numeralL k) (prʟ a₀ b₀)
                    ∙ cong₂ pr (numeralL-fst k) (prʟ-fst a₀ b₀))
                   (ik a₀ b₀))
          zt : ⟨ (prʟ a₀ b₀ ∷ numeralL k ∷ z ∷ γ)
                  ⊨ prAtL (suc (suc zero)) (suc zero) zero ⟩
          zt = transport (cong fst (sym (prAtL-adequate (suc (suc zero)) (suc zero) zero
                 (prʟ a₀ b₀ ∷ numeralL k ∷ z ∷ γ))))
               (tz' ∙ cong₂ pr (sym (numeralL-fst k))
                    (sym (prʟ-fst a₀ b₀)))
          wb : ⟨ (prʟ a₀ b₀ ∷ numeralL k ∷ z ∷ γ)
                  ⊨ prAtL zero (suc (suc (suc (suc (suc zero)))))
                            (suc (suc (suc (suc zero)))) ⟩
          wb = transport (cong fst (sym (prAtL-adequate zero (suc (suc (suc (suc (suc zero)))))
                 (suc (suc (suc (suc zero))))
                 (prʟ a₀ b₀ ∷ numeralL k ∷ z ∷ γ))))
               (prʟ-fst a₀ b₀)
      in ∣ z , ( zK
               , ( p
                 , ∣ numeralL k
                   , ( nk
                     , ( sym te
                       , ∣ prʟ a₀ b₀
                         , ( pk a₀ b₀
                           , ( zt , wb ) )
                         ∣₁ ) )
                   ∣₁ ) ) ∣₁ })
    h

-- =====================================================================
-- SECTION 3: THE EMPTY OPERATION TRANSFER.  emptyB and emptyAt agree
-- with no site facts: the body is ⊥̇, and every satisfier of ⊥̇ lies in
-- K vacuously.
-- =====================================================================
emptyB→emptyAt : ∀ {n} (y K : Fin n) (γ : S ^ n)
  → ⟨ γ ⊨ emptyB y K ⟩ → ⟨ γ ⊨ emptyAt y ⟩
emptyB→emptyAt y K γ h =
  extAtB→extAt y K ⊥̇ ⊥̇ γ (λ z x → x) (λ z x → x) (λ z x → Empty.rec (x .lower)) h

emptyAt→emptyB : ∀ {n} (y K : Fin n) (γ : S ^ n)
  → ⟨ γ ⊨ emptyAt y ⟩ → ⟨ γ ⊨ emptyB y K ⟩
emptyAt→emptyB y K γ h =
  extAt→extAtB y K ⊥̇ ⊥̇ γ (λ z x → x) (λ z x → x) h

-- =====================================================================
-- SECTION 4: THE BOT ROW AGREEMENT, AT THE CLASS CARRIER.
-- =====================================================================
module BotAgree {n : ℕ} (C T B N : Fin n) (γ : S ^ suc n)
  (tagEq : fst (lookup (suc N) γ) ≡ fst (numeralL 7))
  (numK : ⟨ fst (numeralL 7) ∈ fst (lookup zero γ) ⟩)
  (innerK : (a : S) → ⟨ fst (prʟ (numeralL 7) a) ∈ fst (lookup zero γ) ⟩)
  (codesK : (c ar a : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 7) (fst a))
           → ⟨ fst ar ∈ fst (lookup zero γ) ⟩ × ⟨ fst a ∈ fst (lookup zero γ) ⟩)
  (valK : (c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 7) (fst a))
         → ⟨ fst yc ∈ fst (lookup zero γ) ⟩) where

  private
    φB : Formula S (suc n)
    φB = unBareAt {suc n} (suc C) (suc T) zero
           (arTagB (suc N) zero)
           (emptyB zero (suc (suc (suc (suc zero)))))

  -- OUT: the machine's bot row gives the story's bounded bot row.
  bot-out : ⟨ γ ⊨ botClauseAt (suc C) (suc T) ⟩ → ⟨ γ ⊨ φB ⟩
  bot-out h = λ c c∈ ar arK a aK yc ycK shB hc →
    let shD = UnaryShape.out {m = suc n} (suc N) zero 7 (yc ∷ a ∷ ar ∷ c ∷ γ) tagEq shB
        hb = h c c∈ ar a yc shD hc
    in emptyAt→emptyB zero (suc (suc (suc (suc zero)))) (yc ∷ a ∷ ar ∷ c ∷ γ) hb

  -- IN: the story's bounded bot row gives the machine's bot row.
  bot-in : ⟨ γ ⊨ φB ⟩ → ⟨ γ ⊨ botClauseAt (suc C) (suc T) ⟩
  bot-in h = λ c c∈ ar a yc shD hc →
    let shEq : fst c ≡ pr (fst ar) (pr (# 7) (fst a))
        shEq = transport (cong fst (arityTagAtL-adequate (suc (suc (suc zero)))
                 (suc (suc zero)) 7 (suc zero) (yc ∷ a ∷ ar ∷ c ∷ γ))) shD
        (arK , aK) = codesK c ar a c∈ shEq
        ycK = valK c ar a yc c∈ shEq
        shB = UnaryShape.in' {m = suc n} (suc N) zero 7 (yc ∷ a ∷ ar ∷ c ∷ γ) tagEq numK innerK shD
        hb = h c c∈ ar arK a aK yc ycK shB hc
    in emptyB→emptyAt zero (suc (suc (suc (suc zero)))) (yc ∷ a ∷ ar ∷ c ∷ γ) hb

-- =====================================================================
-- SECTION 4B: THE ENVIRONMENT-CONDITION TRANSFER, AT THE B2T LAYOUT.
-- The machine's envOverAt at the atom frame environment gives the
-- story's bounded envBndGen, under the witness-in-K site fact.
-- =====================================================================
module EnvB2T {m : ℕ} (B K : Fin m) (γ : S ^ (6 + m)) where
  -- γ is the frame environment E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ₀.
  domWK : Type (ℓ-suc ℓ)
  domWK = (z w y : S) → ⟨ (y ∷ w ∷ z ∷ γ) ⊨ appAt (suc (suc zero)) (suc zero) zero ⟩
        → ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩

  over→bnd : domWK
    → (z : S) → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc (suc (suc (suc (suc zero)))))
                                    (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
    → ⟨ (z ∷ γ) ⊨ envBndGen zero (suc zero) (suc (suc zero))
                             (suc (suc (suc (suc (suc zero)))))
                             (suc (suc (suc (suc (suc (suc (suc K)))))))
                             (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
  over→bnd dwk z h =
    ( λ x1 x1∈ x2 x2∈ x3 x3∈ → h .fst x1 x2 x3 )
    , ( λ w w∈ →
          ( λ hw →
              PT.rec (snd (fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc zero)))))) (w ∷ z ∷ γ))))
                (λ { (y₀ , (y₀∈ , p)) →
                  domAt-out zero (suc (suc (suc (suc (suc zero))))) (z ∷ γ)
                    (h .snd .fst) w y₀
                    (subst ⟨_⟩ (appAt-adequate (suc (suc zero)) (suc zero) zero
                      (y₀ ∷ w ∷ z ∷ γ)) p) })
                hw )
        , ( λ war →
              PT.rec squash₁
                (λ { (y₀ , p) → ∣ y₀ , ( dwk z w y₀
                     p , p ) ∣₁ })
                (h .snd .fst w .snd war)) )
    , ( λ y1 y1∈ y2 y2∈ p → h .snd .snd .fst y1 y2 p )
    , ( λ s s∈ →
        PT.rec squash₁
          (λ { (u , (v₀ , (u∈ , (v∈ , q)))) →
              ∣ u , (u∈ , ∣ v₀ , (v∈ , subst ⟨_⟩
                    (sym (prAtL-adequate (suc (suc zero)) (suc zero) zero (v₀ ∷ u ∷ s ∷ z ∷ γ))) q) ∣₁) ∣₁ })
          (pairsIn-out zero (suc (suc (suc (suc (suc zero)))))
            (suc (suc (suc (suc (suc (suc (suc B))))))) (z ∷ γ)
            (h .snd .snd .snd) s s∈) )

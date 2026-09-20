{-# OPTIONS --cubical --safe --guardedness #-}

-- K1-b probe B2: the continuum hypothesis, its negation, and the omega
-- instance of the generalized continuum hypothesis, as sentences of the
-- object language, each paired with the truth value a host reader would
-- write down, and each with the agreement theorem between the two.
--
-- The agreement theorems are the point. Roadmap section 1 makes them an
-- acceptance condition of T3: "The semantic CH predicate and its
-- object-language sentence must agree; likewise for the omega-instance of
-- GCH." Without them a proof that the negation has Boolean value top would
-- say nothing about the model actually having many reals.
--
-- The syntax has no function symbols, so neither omega nor the power set can
-- appear as a term. Both sentences universally quantify over a w that is
-- omega and a p that is its power set, and say nothing when no such pair
-- exists. Existence is a separate matter, supplied by the profile's Infinity
-- and Power Set fields, not by these sentences.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module CHSentence {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ∃̇_; ∀̇_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import FOL.Manipulation.Renaming using ( renameFo )
open import CardinalBridge 𝒮

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

open Ren using ( ⊨-rename )

-- Renamings into the two-variable context (p ∷ w ∷ []).

om-w : Fin 1 → Fin 2
om-w zero = suc zero

om-w-agrees : (p w : S) → Ren.Agrees om-w (p ∷ w ∷ []) (w ∷ [])
om-w-agrees p w zero = refl

-- Renamings into the three-variable context (x ∷ p ∷ w ∷ []).

inj-wx : Fin 2 → Fin 3
inj-wx zero       = suc (suc zero)
inj-wx (suc zero) = zero

inj-xw : Fin 2 → Fin 3
inj-xw zero       = zero
inj-xw (suc zero) = suc (suc zero)

inj-px : Fin 2 → Fin 3
inj-px zero       = suc zero
inj-px (suc zero) = zero

inj-wx-agrees : (x p w : S) → Ren.Agrees inj-wx (x ∷ p ∷ w ∷ []) (w ∷ x ∷ [])
inj-wx-agrees x p w zero       = refl
inj-wx-agrees x p w (suc zero) = refl

inj-xw-agrees : (x p w : S) → Ren.Agrees inj-xw (x ∷ p ∷ w ∷ []) (x ∷ w ∷ [])
inj-xw-agrees x p w zero       = refl
inj-xw-agrees x p w (suc zero) = refl

inj-px-agrees : (x p w : S) → Ren.Agrees inj-px (x ∷ p ∷ w ∷ []) (p ∷ x ∷ [])
inj-px-agrees x p w zero       = refl
inj-px-agrees x p w (suc zero) = refl

inj-xp : Fin 2 → Fin 3
inj-xp zero       = zero
inj-xp (suc zero) = suc zero

inj-xp-agrees : (x p w : S) → Ren.Agrees inj-xp (x ∷ p ∷ w ∷ []) (x ∷ p ∷ [])
inj-xp-agrees x p w zero       = refl
inj-xp-agrees x p w (suc zero) = refl

-- The continuum hypothesis. Reading: for every omega w and every power set p
-- of w, a set that omega injects into and that injects into p either injects
-- back into omega or receives an injection from p. In words, nothing sits
-- strictly between omega and its power set in the injectability preorder.

CHsent : Formula S 0
CHsent =
  ∀̇ (∀̇ (((renameFo om-w IsOmegaφ) ∧̇ IsPowerSetφ)
       ⇒̇ (∀̇ (((renameFo inj-wx Injectableφ)
              ∧̇ (renameFo inj-xp Injectableφ))
            ⇒̇ ((renameFo inj-xw Injectableφ)
             ∨̇ (renameFo inj-px Injectableφ))))))

¬CHsent : Formula S 0
¬CHsent = ¬̇ CHsent

chValue : Ω
chValue =
  ⋀ S (λ w → ⋀ S (λ p → ((isOmega w) ⊓ (isPowerSet p w))
    ⇒ (⋀ S (λ x → ((injectable w x) ⊓ (injectable x p))
         ⇒ ((injectable x w) ⊔ (injectable p x))))))

CH-agrees : ([] ⊨ CHsent) ≡ chValue
CH-agrees =
  cong (⋀ S) (funExt (λ w →
    cong (⋀ S) (funExt (λ p →
      cong₂ _⇒_
        (cong₂ _⊓_
          (⊨-rename om-w IsOmegaφ (p ∷ w ∷ []) (w ∷ []) (om-w-agrees p w)
           ∙ IsOmega-bridge w)
          (IsPowerSet-bridge p w))
        (cong (⋀ S) (funExt (λ x →
          cong₂ _⇒_
            (cong₂ _⊓_
              (⊨-rename inj-wx Injectableφ (x ∷ p ∷ w ∷ []) (w ∷ x ∷ [])
                (inj-wx-agrees x p w)
               ∙ Injectable-bridge w x)
              (⊨-rename inj-xp Injectableφ (x ∷ p ∷ w ∷ []) (x ∷ p ∷ [])
                (inj-xp-agrees x p w)
               ∙ Injectable-bridge x p))
            (cong₂ _⊔_
              (⊨-rename inj-xw Injectableφ (x ∷ p ∷ w ∷ []) (x ∷ w ∷ [])
                (inj-xw-agrees x p w)
               ∙ Injectable-bridge x w)
              (⊨-rename inj-px Injectableφ (x ∷ p ∷ w ∷ []) (p ∷ x ∷ [])
                (inj-px-agrees x p w)
               ∙ Injectable-bridge p x)))))))))

-- The negation transports through the same agreement. It needs no excluded
-- middle: the only step is the lifted-bottom lemma of CardinalBridge, which
-- reconciles the evaluator's reading of ¬̇ with the algebra's own ¬.

¬CH-agrees : ([] ⊨ ¬CHsent) ≡ (¬ chValue)
¬CH-agrees = cong (_⇒ ⊥) CH-agrees ∙ sym (¬-as-⇒⊥ chValue)

-- Renamings into the three-variable context (d ∷ p ∷ w ∷ []).

sc-dw : Fin 2 → Fin 3
sc-dw zero       = zero
sc-dw (suc zero) = suc (suc zero)

inj-pd : Fin 2 → Fin 3
inj-pd zero       = suc zero
inj-pd (suc zero) = zero

inj-dp : Fin 2 → Fin 3
inj-dp zero       = zero
inj-dp (suc zero) = suc zero

sc-dw-agrees : (d p w : S) → Ren.Agrees sc-dw (d ∷ p ∷ w ∷ []) (d ∷ w ∷ [])
sc-dw-agrees d p w zero       = refl
sc-dw-agrees d p w (suc zero) = refl

inj-pd-agrees : (d p w : S) → Ren.Agrees inj-pd (d ∷ p ∷ w ∷ []) (p ∷ d ∷ [])
inj-pd-agrees d p w zero       = refl
inj-pd-agrees d p w (suc zero) = refl

inj-dp-agrees : (d p w : S) → Ren.Agrees inj-dp (d ∷ p ∷ w ∷ []) (d ∷ p ∷ [])
inj-dp-agrees d p w zero       = refl
inj-dp-agrees d p w (suc zero) = refl

-- The omega instance of the generalized continuum hypothesis, in the shape
-- the existing L theorem uses: the power set of omega is equinumerous with
-- the successor cardinal of omega, equinumerous meaning a pair of injections
-- rather than a bijection.

GCHωsent : Formula S 0
GCHωsent =
  ∀̇ (∀̇ (((renameFo om-w IsOmegaφ) ∧̇ IsPowerSetφ)
       ⇒̇ (∃̇ ((renameFo sc-dw IsSuccCardinalφ)
            ∧̇ ((renameFo inj-pd Injectableφ)
            ∧̇ (renameFo inj-dp Injectableφ))))))

gchωValue : Ω
gchωValue =
  ⋀ S (λ w → ⋀ S (λ p → ((isOmega w) ⊓ (isPowerSet p w))
    ⇒ (⋁ S (λ d → (isSuccCardinal d w)
         ⊓ ((injectable p d) ⊓ (injectable d p))))))

GCHω-agrees : ([] ⊨ GCHωsent) ≡ gchωValue
GCHω-agrees =
  cong (⋀ S) (funExt (λ w →
    cong (⋀ S) (funExt (λ p →
      cong₂ _⇒_
        (cong₂ _⊓_
          (⊨-rename om-w IsOmegaφ (p ∷ w ∷ []) (w ∷ []) (om-w-agrees p w)
           ∙ IsOmega-bridge w)
          (IsPowerSet-bridge p w))
        (cong (⋁ S) (funExt (λ d →
          cong₂ _⊓_
            (⊨-rename sc-dw IsSuccCardinalφ (d ∷ p ∷ w ∷ []) (d ∷ w ∷ [])
              (sc-dw-agrees d p w)
             ∙ IsSuccCardinal-bridge d w)
            (cong₂ _⊓_
              (⊨-rename inj-pd Injectableφ (d ∷ p ∷ w ∷ []) (p ∷ d ∷ [])
                (inj-pd-agrees d p w)
               ∙ Injectable-bridge p d)
              (⊨-rename inj-dp Injectableφ (d ∷ p ∷ w ∷ []) (d ∷ p ∷ [])
                (inj-dp-agrees d p w)
               ∙ Injectable-bridge d p)))))))))

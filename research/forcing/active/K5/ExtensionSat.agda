{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track F, follow-up: satisfaction transfer between the two extension
-- structures. Architecture section 1.9's `ext-⊨`, which section 3.2 assigns to
-- no track and which exit item X6 nevertheless lists among its minimum
-- evidence.
--
-- WHY IT IS HERE AND NOT IN K5/Structures.agda. This file is deliberately
-- SEPARATE so that a failure here costs nothing already banked there, which is
-- K4's own discipline (K4/SubalgebraAgreement.agda:12-13). It is also the only
-- place in Track F that needs BOTH sides at once.
--
-- WHAT IT SAYS. 𝒮ᴾ[ G ] and 𝒮ᴮ[ U ] are two ZFStructures over the SAME truth
-- algebra, so a formula has a truth value in each, and ext-⊨ says the two
-- values are equal once the environment is carried across by the forward
-- translation. Because both values live in hPropAlgebra ℓ the statement is a
-- PATH of truth values, not a biconditional and not a reflection, and every
-- connective clause is a congruence.
--
-- THE MEASURED CORRECTION, and it is the point of this file. Architecture
-- section 1.9 reads: "Satisfaction transfer needs `ext-onto` and only for the
-- two unbounded quantifier clauses, because those quantify over the carriers."
-- MEASURED FALSE. All FOUR quantifier clauses need it, the two bounded ones
-- included, and the reason is visible in the types rather than in the proofs:
-- on the P side a bounded quantifier is ⋀ Nameᴾ or ⋁ Nameᴾ with a guard, and
-- on the B side it is ⋀ Nameᴮ or ⋁ Nameᴮ with a guard. The guard transfers by
-- ∈-agree, but the INDEX TYPE does not, and nothing but surjectivity of the
-- translation relates a join over Nameᴮ to a join over Nameᴾ. Bounding the
-- quantifier changes which elements are admitted; it does not change what they
-- are drawn from. Every one of the four clauses below names ext-surjective.
--
-- WHAT IS NOT ELIMINATED. ext-surjective returns the preimage as DATA
-- (K5/RoundTrip.agda:504), so no clause below eliminates a truncation into
-- data and ledger clause L1's prohibition is not approached. The truncated
-- form ext-onto would not do: at ∀̇ the witness is needed to build a function,
-- and a truncated sigma cannot be opened into one.
--
-- THE LEDGER, and it is two arguments narrower than the architecture prints.
-- ≈-agree and ∈-agree are taken WITHOUT a name hypothesis on either code, at
-- ARBITRARY ground codes, because that is what Track E's deliverable actually
-- exports: `IsNameᴾ` is used in no proof of it, and its `module Architecture`
-- ships the architecture's named signature by taking and discarding both. That
-- is preamble rule 13 applied to a real export list rather than to a design
-- document, and it is why no clause below projects a name proof out of an
-- environment slot. A consumer holding the wider form discards two arguments.
--
-- They are also taken in their DISCHARGED form, without
-- Track E's `LEM ℓ`, `meets` and `isFilter G` arguments. That is not a hidden
-- weakening: it is forced by clause L2, because `meets` is a field of
-- `CodedCompletion.Core` and typing it verbatim here would apply that module
-- outside Track I. The three hypotheses are visible in Track E's own
-- signature, and this file adds none of its own: `grep -c "LEM"` over it with
-- comments stripped is 0. ext-⊨ is therefore unconditional relative to the two
-- agreements and to ext-surjective, and its conditionality is exactly theirs.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import Valuation
import K4.Algebra
import K5.Structures
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT

module K5.ExtensionSat {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Induction.WellFounded using ( WellFounded )
open import Cubical.Data.Sigma using ( _×_ ; _,_ )
open PT using ( ∥_∥₁ ; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open import FOL.Syntax
  using ( Term ; Formula ; con ; var
        ; _∈̇_ ; _≐_ ; _∧̇_ ; _∨̇_ ; _⇒̇_ ; ⊥̇ ; ∃̇_ ; ∀̇_ ; ∀̇∈ ; ∃̇∈ )
open import FOL.Manipulation.ConstantMapping using ( embed )

open K4.Algebra 𝒮 using ( Pt ; Lattice )

private module VL = Valuation 𝒮
open VL using ( Conditions )

Src : ℕ → Type ℓ
Src k = Formula (⊥* {ℓ}) k

-- Three congruences of the truth algebra, named once so that no reflexivity
-- ever stands for an unchanged endpoint inside one (rule 1).

⊓-cong : {P P' Q Q' : Ω} → P ≡ P' → Q ≡ Q' → (P ⊓ Q) ≡ (P' ⊓ Q')
⊓-cong p q = cong₂ _⊓_ p q

⊔-cong : {P P' Q Q' : Ω} → P ≡ P' → Q ≡ Q' → (P ⊔ Q) ≡ (P' ⊔ Q')
⊔-cong p q = cong₂ _⊔_ p q

⇒-cong : {P P' Q Q' : Ω} → P ≡ P' → Q ≡ Q' → (P ⇒ Q) ≡ (P' ⇒ Q')
⇒-cong p q = cong₂ _⇒_ p q

--------------------------------------------------------------------------------
-- The two sides, from Track F's own file
--------------------------------------------------------------------------------

-- Nothing is re-derived here. K5/Structures.agda's PosetSide and BooleanSide
-- are applied and the two structures, their satisfaction and their
-- substitution lemmas are taken from them.

module Transfer
  (entry       : S → S → S)
  (Child       : S → S → Type ℓ)
  (isPropChild : (x n : S) → isProp (Child x n))
  (child-entry : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)
  (child-wf    : WellFounded Child)
  (∅ᴺ          : S)
  (∅ᴺ-spec     : (z : S) → (z ∈ˢ ∅ᴺ) ≡ ⊥)
  (carrierᶠ    : S)
  (_≼ᶜ_        : Conditions carrierᶠ → Conditions carrierᶠ → Ω)
  (≼ᶜ-refl     : (p : Conditions carrierᶠ) → ⟨ p ≼ᶜ p ⟩)
  (≼ᶜ-trans    : {p q r : Conditions carrierᶠ} → ⟨ p ≼ᶜ q ⟩ → ⟨ q ≼ᶜ r ⟩ → ⟨ p ≼ᶜ r ⟩)
  (inhabitedᶜ  : ∥ Conditions carrierᶠ ∥₁)
  (IsNameᴾ     : S → Ω)
  (child-nameᴾ : (n : S) → ⟨ IsNameᴾ n ⟩ → (x : S) → Child x n → ⟨ IsNameᴾ x ⟩)
  (B           : S)
  (L           : Lattice B)
  (IsNameᴮ     : S → Ω)
  (child-nameᴮ : (n : S) → ⟨ IsNameᴮ n ⟩ → (x : S) → Child x n → ⟨ IsNameᴮ x ⟩)
  where

  private
    module KS = K5.Structures.Kernel 𝒮
                  entry Child isPropChild child-entry child-wf ∅ᴺ ∅ᴺ-spec
    module PS = KS.PosetSide carrierᶠ _≼ᶜ_ ≼ᶜ-refl ≼ᶜ-trans inhabitedᶜ
                  IsNameᴾ child-nameᴾ
    module BS = KS.BooleanSide B L IsNameᴮ child-nameᴮ

  Nameᴾ : Type ℓ
  Nameᴾ = PS.Nameᴾ

  Nameᴮ : Type ℓ
  Nameᴮ = BS.Nameᴮ

  ------------------------------------------------------------------------------
  -- The transfer, at one subset of conditions and one subset of the algebra
  ------------------------------------------------------------------------------

  module At (G : PS.P.Sub) (U : Pt B → Ω) where

    open PS.P.Ext G public
      using ( _≈[G]_ ; _∈[G]_ )
      renaming ( _⊨_ to _⊨ᴾ_ ; sat-cong to sat-congᴾ ; Agree to Agreeᴾ )

    open BS.B'.Ext U public
      using ( )
      renaming ( _≈[G]_ to _≈[U]_ ; _∈[G]_ to _∈[U]_
               ; _⊨_ to _⊨ᴮ_ ; sat-cong to sat-congᴮ ; Agree to Agreeᴮ
               ; ≈-refl to ≈-reflᴮ ; ≈-sym to ≈-symᴮ ; ∈-congˡ to ∈-congˡᴮ )

    -- One helper, used by all four quantifier clauses: replacing the head of a
    -- B-side environment by a value-equal name does not change any truth value.

    consᴮ : ∀ {k} (c d : Nameᴮ) (μ : Vec Nameᴮ k) → ⟨ fst c ≈[U] fst d ⟩
          → Agreeᴮ (c ∷ μ) (d ∷ μ)
    consᴮ c d μ h zero     = h
    consᴮ c d μ h (suc ix) = ≈-reflᴮ (fst (lookup ix μ))

    module Sat
      (trᴮ         : S → S)
      (trᴮ-name    : (n : S) → ⟨ IsNameᴾ n ⟩ → ⟨ IsNameᴮ (trᴮ n) ⟩)
      (≈-agree     : (m n : S) → (m ≈[G] n) ≡ (trᴮ m ≈[U] trᴮ n))
      (∈-agree     : (m n : S) → (m ∈[G] n) ≡ (trᴮ m ∈[U] trᴮ n))
      (ext-surjective : (n : S) → ⟨ IsNameᴮ n ⟩
                      → Σ[ τ ∈ (Σ[ m ∈ S ] ⟨ IsNameᴾ m ⟩) ] ⟨ trᴮ (fst τ) ≈[U] n ⟩)
      where

      -- The extension map, architecture section 1.9's own two lines.

      ext-map : Nameᴾ → Nameᴮ
      ext-map τ = trᴮ (fst τ) , trᴮ-name (fst τ) (snd τ)

      envᴮ : ∀ {k} → Vec Nameᴾ k → Vec Nameᴮ k
      envᴮ []      = []
      envᴮ (σ ∷ ν) = ext-map σ ∷ envᴮ ν

      lookup-ext : ∀ {k} (ix : Fin k) (ν : Vec Nameᴾ k)
                 → fst (lookup ix (envᴮ ν)) ≡ trᴮ (fst (lookup ix ν))
      lookup-ext zero     (σ ∷ ν) = refl
      lookup-ext (suc ix) (σ ∷ ν) = lookup-ext ix ν

      -- The two atomic transfers. Nothing is projected out of an environment
      -- slot but the code: the agreements hold at arbitrary ground codes, so
      -- the environment's name proofs are never read.

      private
        atom-∈ : ∀ {k} (ix jx : Fin k) (ν : Vec Nameᴾ k)
               → (fst (lookup ix ν) ∈[G] fst (lookup jx ν))
               ≡ (fst (lookup ix (envᴮ ν)) ∈[U] fst (lookup jx (envᴮ ν)))
        atom-∈ ix jx ν =
          ∈-agree (fst (lookup ix ν)) (fst (lookup jx ν))
          ∙ sym (cong₂ _∈[U]_ (lookup-ext ix ν) (lookup-ext jx ν))

        atom-≈ : ∀ {k} (ix jx : Fin k) (ν : Vec Nameᴾ k)
               → (fst (lookup ix ν) ≈[G] fst (lookup jx ν))
               ≡ (fst (lookup ix (envᴮ ν)) ≈[U] fst (lookup jx (envᴮ ν)))
        atom-≈ ix jx ν =
          ≈-agree (fst (lookup ix ν)) (fst (lookup jx ν))
          ∙ sym (cong₂ _≈[U]_ (lookup-ext ix ν) (lookup-ext jx ν))

      -- THE INDUCTION. The two atomic cases are Track E's agreements. The four
      -- propositional cases are congruences of one truth algebra. The four
      -- QUANTIFIER cases, bounded and unbounded alike, each name
      -- ext-surjective, which is the correction this file ships.

      ext-⊨ : ∀ {k} (φ : Src k) (ν : Vec Nameᴾ k)
            → (ν ⊨ᴾ embed φ) ≡ (envᴮ ν ⊨ᴮ embed φ)

      ext-⊨ (var ix ∈̇ var jx) ν = atom-∈ ix jx ν
      ext-⊨ (var ix ∈̇ con e)  ν = Empty.rec* e
      ext-⊨ (con e ∈̇ u)       ν = Empty.rec* e

      ext-⊨ (var ix ≐ var jx) ν = atom-≈ ix jx ν
      ext-⊨ (var ix ≐ con e)  ν = Empty.rec* e
      ext-⊨ (con e ≐ u)       ν = Empty.rec* e

      ext-⊨ (φ ∧̇ ψ) ν = ⊓-cong (ext-⊨ φ ν) (ext-⊨ ψ ν)
      ext-⊨ (φ ∨̇ ψ) ν = ⊔-cong (ext-⊨ φ ν) (ext-⊨ ψ ν)
      ext-⊨ (φ ⇒̇ ψ) ν = ⇒-cong (ext-⊨ φ ν) (ext-⊨ ψ ν)
      ext-⊨ ⊥̇ ν = refl

      ext-⊨ (∃̇ φ) ν = ⇔toPath to from
        where
          to : ⟨ ν ⊨ᴾ embed (∃̇ φ) ⟩ → ⟨ envᴮ ν ⊨ᴮ embed (∃̇ φ) ⟩
          to = PT.map (λ { (σ , h) → ext-map σ , subst ⟨_⟩ (ext-⊨ φ (σ ∷ ν)) h })

          from : ⟨ envᴮ ν ⊨ᴮ embed (∃̇ φ) ⟩ → ⟨ ν ⊨ᴾ embed (∃̇ φ) ⟩
          from = PT.map (λ { (ρ , h) →
            let pre = ext-surjective (fst ρ) (snd ρ)
            in fst pre
             , subst ⟨_⟩ (sym (ext-⊨ φ (fst pre ∷ ν)))
                 (subst ⟨_⟩ (sat-congᴮ (embed φ) (ρ ∷ envᴮ ν)
                              (ext-map (fst pre) ∷ envᴮ ν)
                              (consᴮ ρ (ext-map (fst pre)) (envᴮ ν)
                                (≈-symᴮ (snd pre))))
                   h) })

      ext-⊨ (∀̇ φ) ν = ⇔toPath to from
        where
          to : ⟨ ν ⊨ᴾ embed (∀̇ φ) ⟩ → ⟨ envᴮ ν ⊨ᴮ embed (∀̇ φ) ⟩
          to f ρ =
            let pre = ext-surjective (fst ρ) (snd ρ)
            in subst ⟨_⟩ (sat-congᴮ (embed φ) (ext-map (fst pre) ∷ envᴮ ν)
                           (ρ ∷ envᴮ ν)
                           (consᴮ (ext-map (fst pre)) ρ (envᴮ ν) (snd pre)))
                 (subst ⟨_⟩ (ext-⊨ φ (fst pre ∷ ν)) (f (fst pre)))

          from : ⟨ envᴮ ν ⊨ᴮ embed (∀̇ φ) ⟩ → ⟨ ν ⊨ᴾ embed (∀̇ φ) ⟩
          from g σ = subst ⟨_⟩ (sym (ext-⊨ φ (σ ∷ ν))) (g (ext-map σ))

      ext-⊨ (∀̇∈ (var ix) φ) ν = ⇔toPath to from
        where
          to : ⟨ ν ⊨ᴾ embed (∀̇∈ (var ix) φ) ⟩ → ⟨ envᴮ ν ⊨ᴮ embed (∀̇∈ (var ix) φ) ⟩
          to f ρ hρ =
            let pre = ext-surjective (fst ρ) (snd ρ)
                guardᴾ : ⟨ fst (fst pre) ∈[G] fst (lookup ix ν) ⟩
                guardᴾ = subst ⟨_⟩
                  (sym (∈-agree (fst (fst pre)) (fst (lookup ix ν))))
                  (∈-congˡᴮ (≈-symᴮ (snd pre))
                    (subst (λ w → ⟨ fst ρ ∈[U] w ⟩) (lookup-ext ix ν) hρ))
            in subst ⟨_⟩ (sat-congᴮ (embed φ) (ext-map (fst pre) ∷ envᴮ ν)
                           (ρ ∷ envᴮ ν)
                           (consᴮ (ext-map (fst pre)) ρ (envᴮ ν) (snd pre)))
                 (subst ⟨_⟩ (ext-⊨ φ (fst pre ∷ ν)) (f (fst pre) guardᴾ))

          from : ⟨ envᴮ ν ⊨ᴮ embed (∀̇∈ (var ix) φ) ⟩ → ⟨ ν ⊨ᴾ embed (∀̇∈ (var ix) φ) ⟩
          from g σ hσ = subst ⟨_⟩ (sym (ext-⊨ φ (σ ∷ ν)))
            (g (ext-map σ)
               (subst (λ w → ⟨ trᴮ (fst σ) ∈[U] w ⟩) (sym (lookup-ext ix ν))
                 (subst ⟨_⟩ (∈-agree (fst σ) (fst (lookup ix ν))) hσ)))

      ext-⊨ (∀̇∈ (con e) φ) ν = Empty.rec* e

      ext-⊨ (∃̇∈ (var ix) φ) ν = ⇔toPath to from
        where
          to : ⟨ ν ⊨ᴾ embed (∃̇∈ (var ix) φ) ⟩ → ⟨ envᴮ ν ⊨ᴮ embed (∃̇∈ (var ix) φ) ⟩
          to = PT.map (λ { (σ , hσ , h) → ext-map σ
                         , subst (λ w → ⟨ trᴮ (fst σ) ∈[U] w ⟩) (sym (lookup-ext ix ν))
                             (subst ⟨_⟩ (∈-agree (fst σ) (fst (lookup ix ν))) hσ)
                         , subst ⟨_⟩ (ext-⊨ φ (σ ∷ ν)) h })

          from : ⟨ envᴮ ν ⊨ᴮ embed (∃̇∈ (var ix) φ) ⟩ → ⟨ ν ⊨ᴾ embed (∃̇∈ (var ix) φ) ⟩
          from = PT.map (λ { (ρ , hρ , h) →
            let pre = ext-surjective (fst ρ) (snd ρ)
            in fst pre
             , subst ⟨_⟩
                 (sym (∈-agree (fst (fst pre)) (fst (lookup ix ν))))
                 (∈-congˡᴮ (≈-symᴮ (snd pre))
                   (subst (λ w → ⟨ fst ρ ∈[U] w ⟩) (lookup-ext ix ν) hρ))
             , subst ⟨_⟩ (sym (ext-⊨ φ (fst pre ∷ ν)))
                 (subst ⟨_⟩ (sat-congᴮ (embed φ) (ρ ∷ envᴮ ν)
                              (ext-map (fst pre) ∷ envᴮ ν)
                              (consᴮ ρ (ext-map (fst pre)) (envᴮ ν)
                                (≈-symᴮ (snd pre))))
                   h) })

      ext-⊨ (∃̇∈ (con e) φ) ν = Empty.rec* e

      ------------------------------------------------------------------------
      -- The ∈-monomorphism, packaged, and what it is NOT
      ------------------------------------------------------------------------

      -- Architecture section 1.9's `ext-mono`. It is ≈-agree and ∈-agree with
      -- the codes replaced by names, which is the form a consumer reading the
      -- two structures wants; nothing is proved here.

      ext-mono-≈ : (σ τ : Nameᴾ) → (fst σ ≈[G] fst τ) ≡ (fst (ext-map σ) ≈[U] fst (ext-map τ))
      ext-mono-≈ σ τ = ≈-agree (fst σ) (fst τ)

      ext-mono-∈ : (σ τ : Nameᴾ) → (fst σ ∈[G] fst τ) ≡ (fst (ext-map σ) ∈[U] fst (ext-map τ))
      ext-mono-∈ σ τ = ∈-agree (fst σ) (fst τ)

      -- NON-CLAIM, and it is the line Track H and Track J both drew. Nothing
      -- above says the two names are the same CODE. K3 states that the raw code
      -- round trip is false in both directions (TranslateReverse.agda:45-46),
      -- Track J refuted the identification of the two generic names
      -- (K5/RefutedOrder.agda), and Track H broke its own file to show that
      -- replacing the value equality by `trᴮ (trᴾ n) ≡ n` gives exit 42. The
      -- type below is the code-level statement, transcribed and shipped with NO
      -- inhabitant so that no later track writes it by accident.

      CodeRoundTrip : Type ℓ
      CodeRoundTrip = (n : S) (hn : ⟨ IsNameᴮ n ⟩)
                    → trᴮ (fst (fst (ext-surjective n hn))) ≡ n

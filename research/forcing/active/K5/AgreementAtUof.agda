{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track E, seam probe 2, and the named instance exit item X4 asks for.
--
-- WHAT IT CHECKS. X4 requires ≈-agree and ∈-agree "at the two instantiations
-- of one K3 module, with Uof G as the Boolean-side filter". K5/Agreement.agda
-- proves them at an ARBITRARY subset U of the algebra that corresponds to G
-- at the image of the embedding, which is strictly more general and is the
-- measured improvement this track reports. This file closes the gap by
-- supplying Uof G for U and Track D's two correspondence clauses for the two
-- bridges, and it therefore also checks, mechanically, two things that were
-- asserted and not compiled:
--
--   1. that Track D's FS.Sub over its frameNotion and K3's Poset.Sub over the
--      same three order facts are the SAME type, so that one G serves both;
--   2. that Uof G, whose type is Pt B → Ω, is a legal argument for the
--      B-side instantiation's Sub, which is Conditions B → Ω. Pt B and
--      Conditions B are the same Σ-type and this is where that is checked
--      rather than claimed.
--
-- The paid input is isolated exactly where Track D isolated it: LEM ℓ, the
-- flat genericity clause, and isFilter G, all three explicit, all three spent
-- only inside generic-reflect. Track C's three coded sets arrive as module
-- parameters typed character for character from the landed K5/Generic.agda
-- (:339-356), which is ledger clause L10 again.
--
-- Evidence, not a deliverable. The deliverable is K5/Agreement.agda.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import Base.Classical using ( LEM )
open import Cubical.Induction.WellFounded using ( WellFounded )
import OrdinaryProfile
import CodedVocabulary
import K4.Algebra
import K4.Implication
import K5.Frame
import K5.Generic
import K5.Agreement

module K5.AgreementAtUof {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open K4.Algebra 𝒮 using ( Pt; Lattice; Complement; CodedComplete )
open CodedVocabulary 𝒮 using ( denseΔ )

module Probe (carrier order : S) where

  open K5.Frame.Poset 𝒮 carrier order using ( Cond; _≼ᶜ_; compatᶜ; ForcingBase )

  module Seam
    (entry       : S → S → S)
    (entry-inj   : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c))
    (Child       : S → S → Type ℓ)
    (isPropChild : (x n : S) → isProp (Child x n))
    (child-entry : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)
    (child-wf    : WellFounded Child)
    (∅ᴺ          : S)
    (∅ᴺ-spec     : (z : S) → (z ∈ˢ ∅ᴺ) ≡ ⊥)
    (paths       : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
    (ext         : OrdinaryProfile.Extensionality 𝒮)
    (B : S) (L : Lattice B) (Cm : Complement B L) (Kc : CodedComplete B L)
    (fb : ForcingBase B L Cm)
    (trᴮ         : S → S)
    (trᴮ-entries : (n e : S) → (e ∈ˢ trᴮ n)
                 ≡ ⋁ S (λ x → ⋁ S (λ p → ⋁ ⟨ p ∈ˢ carrier ⟩ (λ hp →
                     (entry x p ∈ˢ n)
                     ⊓ (e ≈ˢ entry (trᴮ x)
                              (fst (ForcingBase.i fb (p , hp))))))))
    where

    -- Track E's two instantiations of K3's value module, and the translation
    -- fed to them.

    module KF = K5.Agreement.Poset.Kernel.Frame 𝒮 carrier order
                  entry entry-inj Child isPropChild child-entry child-wf
                  ∅ᴺ ∅ᴺ-spec paths
                  B L Cm fb

    module KT = KF.Translation trᴮ trᴮ-entries

    -- Track D's Boolean-side subset, over the same frame. paths serves as
    -- Track D's path realization too, which is one more drift check: the two
    -- files spell that hypothesis identically.

    module GD = K5.Generic.Poset.Image 𝒮 carrier order ext paths B L Cm Kc fb

    -- Track D opens the forcing relation and the complement without
    -- re-exporting them, so the two names Track C's decide-set specification
    -- speaks are opened here from their owners. They are the SAME names: a
    -- module alias is a definition equal to the original applied to the same
    -- arguments, so the seal on _⊩ᴮ_ is untouched by naming it twice.

    open K5.Frame.Poset.Forcing 𝒮 carrier order ext paths B L Cm Kc fb
      using ( _⊩ᴮ_ )
    open K4.Implication 𝒮 ext paths B L Cm using ( ¬ᴮ_ )

    -- Track C's three coded sets, verbatim from K5/Generic.agda:339-356.
    -- decideAt is not used by this file and is carried because Meeting's
    -- telescope carries it; that is Track D's shape and not this probe's.

    module AtSets
      (decideAt          : Pt B → S)
      (decideAt-sub      : (b : Pt B) → ⟨ decideAt b ⊆ˢ carrier ⟩)
      (decideAt-spec     : (b : Pt B) (q : Cond)
                         → ⟨ fst q ∈ˢ decideAt b ⟩
                         → ⟨ (q ⊩ᴮ b) ⊔ (q ⊩ᴮ (¬ᴮ b)) ⟩)
      (decideAt-dense    : LEM ℓ → (b : Pt B)
                         → ⟨ denseΔ carrier order (decideAt b) ⟩)
      (coneOrApart       : Cond → S)
      (coneOrApart-sub   : (p : Cond) → ⟨ coneOrApart p ⊆ˢ carrier ⟩)
      (coneOrApart-spec  : (p q : Cond)
                         → ⟨ fst q ∈ˢ coneOrApart p ⟩
                         → ⟨ (fst q ≼ᶜ fst p) ⊔ (compatᶜ q p ⇒ ⊥) ⟩)
      (coneOrApart-dense : LEM ℓ → (p : Cond)
                         → ⟨ denseΔ carrier order (coneOrApart p) ⟩)
      (G : GD.FS.Sub)
      where

      module MT = GD.Meeting decideAt decideAt-sub decideAt-spec decideAt-dense
                             coneOrApart coneOrApart-sub coneOrApart-spec
                             coneOrApart-dense G

      -- THE JOIN. G is handed to K3's P-side instantiation and Uof G to its
      -- B-side instantiation, and the two bridges are Track D's two
      -- correspondence clauses. If Sub on either side had drifted from the
      -- other, this application would not elaborate.

      module At
        (lem   : LEM ℓ)
        (meets : (d : S) → ⟨ d ⊆ˢ carrier ⟩ → ⟨ denseΔ carrier order d ⟩
               → ⟨ ⋁ Cond (λ q → (q GD.FS.∈ᴾ G) ⊓ (fst q ∈ˢ d)) ⟩)
        (fil   : GD.FS.isFilter G)
        where

        module AG = KT.Agree G (GD.Uof G)
                      MT.generic-forward
                      (MT.generic-reflect lem meets fil)

        open AG public
          using ( _≈[G]_ ; _∈[G]_ ; _≈[U]_ ; _∈[U]_
                ; ≈-agree ; ∈-agree ; active→ ; active← ; generic-bridge )

      -- The architecture's curried signature (part 1.8), delivered at the
      -- named Boolean-side filter. LEM ℓ, genericity and the filter are
      -- explicit arguments, which is where part 5 requires a conditionality
      -- to be visible.

      ≈-agree-at-Uof :
          (lem : LEM ℓ)
        → (meets : (d : S) → ⟨ d ⊆ˢ carrier ⟩ → ⟨ denseΔ carrier order d ⟩
                 → ⟨ ⋁ Cond (λ q → (q GD.FS.∈ᴾ G) ⊓ (fst q ∈ˢ d)) ⟩)
        → (fil : GD.FS.isFilter G)
        → (m n : S)
        → At._≈[G]_ lem meets fil m n
        ≡ At._≈[U]_ lem meets fil (trᴮ m) (trᴮ n)
      ≈-agree-at-Uof lem meets fil = At.≈-agree lem meets fil

      ∈-agree-at-Uof :
          (lem : LEM ℓ)
        → (meets : (d : S) → ⟨ d ⊆ˢ carrier ⟩ → ⟨ denseΔ carrier order d ⟩
                 → ⟨ ⋁ Cond (λ q → (q GD.FS.∈ᴾ G) ⊓ (fst q ∈ˢ d)) ⟩)
        → (fil : GD.FS.isFilter G)
        → (m n : S)
        → At._∈[G]_ lem meets fil m n
        ≡ At._∈[U]_ lem meets fil (trᴮ m) (trᴮ n)
      ∈-agree-at-Uof lem meets fil = At.∈-agree lem meets fil

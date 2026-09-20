{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track D, EVIDENCE AND NOT A DELIVERABLE.
--
-- Every export of K5/Generic.agda is restated here at the type a consumer
-- will write, and then filled by the export itself. A drift between what the
-- file proves and what this track reports therefore fails here rather than
-- passing silently. The three Track C parameters are taken abstractly, which
-- is exactly how Track E and Track G will take them until Track C lands.
--
-- This file also carries the ONE claim about levels that Track D owes. Every
-- statement of module Laws is at Type ℓ, because G is a module parameter and
-- not a quantified variable; the check is the two declarations at the end,
-- which index a ⋁ by the type of a Laws statement and elaborate only at
-- Type ℓ.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import Base.Classical using ( LEM )
import OrdinaryProfile
import CodedVocabulary
import ForcingNotion as FN
import Cubical.HITs.PropositionalTruncation as PT
import K4.Algebra
import K4.Implication
import K5.Frame
import K5.Generic

module K5.ProbeD {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )

open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open K4.Algebra 𝒮
  using ( Pt; _≤ᴮ_; ≤ᴮ-refl; ⊆ˢ-trans; Lattice; Complement; CodedComplete )

open CodedVocabulary 𝒮 using ( denseΔ )

module Poset (carrier order : S) where

  open K5.Frame.Poset 𝒮 carrier order

  module Check
    (ext   : OrdinaryProfile.Extensionality 𝒮)
    (paths : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
    (B : S) (L : Lattice B) (Cm : Complement B L) (Kc : CodedComplete B L)
    (fb : ForcingBase B L Cm)
    where

    open ForcingBase fb
    open K5.Frame.Poset.Forcing 𝒮 carrier order ext paths B L Cm Kc fb
    open K4.Implication 𝒮 ext paths B L Cm
      using ( ⊥ᴮ ; ¬ᴮ_ ; _⊓ᴮ_ ; ⊓-lb₁ ; ⊓-lb₂ ; ⊓-glb )
    open K5.Generic.Poset.Image 𝒮 carrier order ext paths B L Cm Kc fb

    ----------------------------------------------------------------------
    -- The decoded notion is K2's record, inhabited, and its conditions are
    -- Track A's conditions on the nose.
    ----------------------------------------------------------------------

    check-notion : FN.ForcingNotion {ℓ}
    check-notion = frameNotion

    check-Cond : FS.Cond ≡ Cond
    check-Cond = refl

    check-≼ : (p q : Cond) → FS._≼_ p q ≡ (fst p ≼ᶜ fst q)
    check-≼ p q = refl

    ----------------------------------------------------------------------
    -- The corresponding subset, and the reading of it
    ----------------------------------------------------------------------

    check-Uof : FS.Sub → Pt B → Ω
    check-Uof = Uof

    check-Uof-spec : (G : FS.Sub) (b : Pt B)
                   → Uof G b ≡ ⋁ Cond (λ p → (FS._∈ᴾ_ p G) ⊓ (p ⊩ᴮ b))
    check-Uof-spec G b = refl

    module CheckLaws (G : FS.Sub) where

      open K5.Generic.Poset.Image.Laws
             𝒮 carrier order ext paths B L Cm Kc fb G

      check-forward : (p : Cond) → ⟨ FS._∈ᴾ_ p G ⟩ → ⟨ Uof G (i p) ⟩
      check-forward = generic-forward

      check-inhabited : ⟨ FS.positive G ⟩ → ⟨ ⋁ (Pt B) (Uof G) ⟩
      check-inhabited = Uof-inhabited

      check-up : (b c : Pt B) → ⟨ b ≤ᴮ c ⟩ → ⟨ Uof G b ⟩ → ⟨ Uof G c ⟩
      check-up = Uof-up

      check-dir : FS.isFilter G → (b c : Pt B) → ⟨ Uof G b ⟩ → ⟨ Uof G c ⟩
                → ⟨ ⋁ (Pt B) (λ d → (Uof G d) ⊓ ((d ≤ᴮ b) ⊓ (d ≤ᴮ c))) ⟩
      check-dir = Uof-dir

      check-proper : ⟨ Uof G ⊥ᴮ ⟩ → ⟨ ⊥ ⟩
      check-proper = Uof-proper

      check-reflect-from :
          FS.isFilter G
        → (p : Cond)
        → ⟨ ⋁ Cond (λ s → (FS._∈ᴾ_ s G)
                     ⊓ ((fst s ≼ᶜ fst p) ⊔ (compatᶜ s p ⇒ ⊥))) ⟩
        → ⟨ Uof G (i p) ⟩
        → ⟨ FS._∈ᴾ_ p G ⟩
      check-reflect-from = generic-reflect-from

      check-ultra-from :
          (b : Pt B)
        → ⟨ ⋁ Cond (λ q → (FS._∈ᴾ_ q G) ⊓ ((q ⊩ᴮ b) ⊔ (q ⊩ᴮ (¬ᴮ b)))) ⟩
        → ⟨ (Uof G b) ⊔ (Uof G (¬ᴮ b)) ⟩
      check-ultra-from = Uof-ultra-from

      -- MEASURED CORRECTION TO TRAP T-D1, and it is a negative result rather
      -- than a repair. The trap reads: the directedness witness is the image
      -- of a condition in the generic, never a meet, because "a track
      -- reaching for the meet will need separativity". The CONCLUSION is
      -- sound and K5/Generic.agda obeys it; THE REASON GIVEN FOR IT IS FALSE
      -- AT THIS LEMMA. Taking d := b ⊓ᴮ c discharges Uof-dir with no
      -- separativity, no order reflection, no density of the image and no
      -- excluded middle: the common refinement r that the filter downstairs
      -- already supplies has i r under b and under c, so ⊓-glb puts i r under
      -- the meet, and ⊓-lb₁ and ⊓-lb₂ are the other two components. Three
      -- Lattice fields, nothing else. This declaration is the measurement.
      --
      -- Where separativity IS needed is the PULLBACK, G-of U, which is not
      -- K5's: there one has i p and i q in an ultrafilter of the algebra,
      -- hence i p ⊓ᴮ i q in it, and must produce a CONDITION r refining both
      -- p and q, which reads an order relation back off an inequality between
      -- images (ForcingNotion.agda:175-180, :276-278). The pushforward and the
      -- pullback must not be conflated, and the trap's reason belongs to the
      -- pullback.

      Uof-dir-meet : FS.isFilter G → (b c : Pt B) → ⟨ Uof G b ⟩ → ⟨ Uof G c ⟩
                   → ⟨ ⋁ (Pt B) (λ d → (Uof G d) ⊓ ((d ≤ᴮ b) ⊓ (d ≤ᴮ c))) ⟩
      Uof-dir-meet fil b c hb hc = PT.rec (snd goal) fromB hb
        where
          goal : Ω
          goal = ⋁ (Pt B) (λ d → (Uof G d) ⊓ ((d ≤ᴮ b) ⊓ (d ≤ᴮ c)))

          fromB : Σ[ p ∈ Cond ] (⟨ FS._∈ᴾ_ p G ⟩ × ⟨ p ⊩ᴮ b ⟩) → ⟨ goal ⟩
          fromB (p , hpG , hpb) = PT.rec (snd goal) fromC hc
            where
              fromC : Σ[ q ∈ Cond ] (⟨ FS._∈ᴾ_ q G ⟩ × ⟨ q ⊩ᴮ c ⟩) → ⟨ goal ⟩
              fromC (q , hqG , hqc) =
                PT.map atCommon (FS.isFilter.directed fil p q hpG hqG)
                where
                  atCommon : Σ[ r ∈ Cond ] (⟨ FS._∈ᴾ_ r G ⟩ ×
                               (⟨ fst r ≼ᶜ fst p ⟩ × ⟨ fst r ≼ᶜ fst q ⟩))
                           → Σ[ d ∈ Pt B ] ⟨ (Uof G d) ⊓ ((d ≤ᴮ b) ⊓ (d ≤ᴮ c)) ⟩
                  atCommon (r , hrG , hrp , hrq) =
                    (b ⊓ᴮ c)
                    , ( ∣ r , hrG
                        , ⊩ᴮ-intro r (b ⊓ᴮ c)
                            (⊓-glb b c (i r)
                              (⊆ˢ-trans (i-mono p r hrp) (⊩ᴮ-elim p b hpb))
                              (⊆ˢ-trans (i-mono q r hrq) (⊩ᴮ-elim q c hqc))) ∣₁
                      , ( ⊓-lb₁ b c , ⊓-lb₂ b c ) )

      -- Rule 8 and ledger clause L13, checked by the machine rather than by
      -- inspection. A ⋁ may be indexed only by a Type ℓ, so these elaborate
      -- exactly when the statements of module Laws have landed at Type ℓ. Had
      -- G been an explicit argument instead of a module parameter, the type
      -- of check-up would quantify over FS.Sub : Type (ℓ-suc ℓ) and this
      -- would fail with a level error.

      Laws-indexes-⋁ : Ω
      Laws-indexes-⋁ =
        ⋁ ((b c : Pt B) → ⟨ b ≤ᴮ c ⟩ → ⟨ Uof G b ⟩ → ⟨ Uof G c ⟩) (λ _ → ⊥)

      Dir-indexes-⋁ : Ω
      Dir-indexes-⋁ =
        ⋁ (FS.isFilter G → (b c : Pt B) → ⟨ Uof G b ⟩ → ⟨ Uof G c ⟩
            → ⟨ ⋁ (Pt B) (λ d → (Uof G d) ⊓ ((d ≤ᴮ b) ⊓ (d ≤ᴮ c))) ⟩)
          (λ _ → ⊥)

    ----------------------------------------------------------------------
    -- The paid layer, against Track C taken abstractly
    ----------------------------------------------------------------------

    module CheckMeeting
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
      (G : FS.Sub)
      where

      open K5.Generic.Poset.Image.Meeting
             𝒮 carrier order ext paths B L Cm Kc fb
             decideAt decideAt-sub decideAt-spec decideAt-dense
             coneOrApart coneOrApart-sub coneOrApart-spec coneOrApart-dense
             G

      -- The genericity hypothesis is K2's meets field, flat and verbatim from
      -- CodedCompletion.agda:1073-1074 with subsetOf and denseᴵ expanded.

      Meets : Type ℓ
      Meets = (d : S) → ⟨ d ⊆ˢ carrier ⟩ → ⟨ denseΔ carrier order d ⟩
            → ⟨ ⋁ Cond (λ q → (FS._∈ᴾ_ q G) ⊓ (fst q ∈ˢ d)) ⟩

      check-reflect : LEM ℓ → Meets → FS.isFilter G
                    → (p : Cond) → ⟨ Uof G (i p) ⟩ → ⟨ FS._∈ᴾ_ p G ⟩
      check-reflect = generic-reflect

      check-ultra : LEM ℓ → Meets
                  → (b : Pt B) → ⟨ (Uof G b) ⊔ (Uof G (¬ᴮ b)) ⟩
      check-ultra = Uof-ultra

      check-bridge : LEM ℓ → Meets → FS.isFilter G
                   → (p : Cond) → (FS._∈ᴾ_ p G) ≡ Uof G (i p)
      check-bridge = generic-bridge

      -- The free laws are re-exported by Meeting, so a consumer that opens
      -- Meeting alone has the whole track.

      check-reexport : (b c : Pt B) → ⟨ b ≤ᴮ c ⟩ → ⟨ Uof G b ⟩ → ⟨ Uof G c ⟩
      check-reexport = Uof-up

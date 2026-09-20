{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track E: valuation agreement.
--
-- THE QUESTION. K3 built one value relation and left it bi-instantiable: at a
-- carrier code, an order on its conditions and a subset of them, it gives
-- _≈[G]_ and _∈[G]_ on ground codes (Valuation.agda:201-206, :285, :294).
-- K5 has two carriers, the poset's and the algebra's, and one map between the
-- name layers, K3's forward translation trᴮ. The question this file answers
-- is whether the two readings of a name agree: does a P-name have, at G, the
-- value its translation has at the subset of the algebra that G determines?
--
-- THE ANSWER, and its exact shape. Yes, and the agreement is a PATH IN Ω at
-- every pair of ground codes, not merely an entailment in one direction:
--
--     ≈-agree : (m n : S) → (m ≈[G] n) ≡ (trᴮ m ≈[U] trᴮ n)
--     ∈-agree : (m n : S) → (m ∈[G] n) ≡ (trᴮ m ∈[U] trᴮ n)
--
-- WHERE THE AGREEMENT IS STATED, and this is the point Track J's fourth
-- refutation forces. It is stated at the VALUE RELATION and never at the
-- codes. Track J refuted the identification of trᴮ Γᴾ with the Boolean
-- generic name U̇ AS CODES (K5/RefutedOrder.agda:204-220), and was careful to
-- say what that does not refute: the two names may still have the same VALUE
-- at a filter, because an entry of weight ⊥ᴮ is never active. This file is
-- where that distinction lives. Every statement below is about activity and
-- about the value relation; not one of them says that two codes are equal,
-- and the only paths between codes that occur anywhere in the proofs are the
-- ones entry-inj produces INSIDE a truncation and eliminates into a
-- proposition.
--
-- THE ONE THING THE INDUCTION CONSUMES. The whole of it reduces, at every
-- node, to the correspondence between a condition lying in G and its image
-- lying in U. That is Track D's generic-bridge (K5/Generic.agda:411-418).
-- It arrives here as TWO ENTAILMENTS rather than as one path, so that the
-- cost split is visible in the telescope: bridge→ is Track D's
-- generic-forward (K5/Generic.agda:169) and is FREE, bridge← is Track D's
-- generic-reflect (:370) and is
-- PAID, at LEM ℓ and at genericity, and this file spends nothing further.
--
-- FOUR TRAPS, each answered in the source beside the thing it constrains.
--
-- T-E1. The correspondence is NOT proved entry by entry from injectivity of
-- the embedding. There is none and there never will be
-- (TranslateForward.agda:33-36, non-claim 4). K5/RefutedOrder.agda has now
-- refuted order reflection at K2's non-refined instance and shown that
-- separativity, the strongest hypothesis available at that layer, does not
-- repair it. The comment on active← below records what this file does
-- instead, and the telescope shows that no injectivity enters: what the
-- backward active law uses is injectivity of ENTRY, which is about Kuratowski
-- pairs and not about the embedding.
--
-- T-E2. The value relation already indexes its joins by the subname sigma,
-- Below n = Σ[ x ∈ S ] Child x n (Valuation.agda:269-270). Nothing here
-- re-indexes by the carrier: every join this file writes is over S, which is
-- the shape ≈-unfold hands over (:322), and the only other index that occurs
-- is the one K3's own ≈-fwd / ≈-bwd / ≈-intro already hide.
--
-- T-E3. Active is DATA and not a proposition (Valuation.agda:245-254): a name
-- may carry one subname at many weights, and no theorem anywhere says the
-- entry presentation is unique. Every elimination in this file therefore
-- lands in a proposition. The backward active law, active←, states its
-- conclusion as an Ω-valued join for exactly this reason, and is the one
-- place where the identification of a translated entry with its source could
-- have been smuggled out as data.
--
-- T-E4. One application of Valuation.Names, and it is applied to module
-- PARAMETERS, which is rule 2's tightest seal. The two Poset instantiations
-- sit inside that single application.
--
-- WHAT THIS FILE DOES NOT CLAIM.
--
--   * No reverse agreement. trᴾ is not here, and K3's own report says the
--     asymmetry of trᴾ's support makes an equality in that direction
--     unlikely (REPORT-I.md:313-314). Track H owns ext-onto.
--   * No monotonicity in G, in either direction (Valuation.agda:700-705).
--     The induction never compares two relations at two subsets.
--   * No second value relation. This file declares none; it applies K3's.
--   * No inhabitant of ValueStructure, and no set quotient.
--   * Nothing about host values, host semantics or coded/host agreement.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import Cubical.Induction.WellFounded using ( WellFounded; module WFI )
import K4.Algebra
import K5.Frame
import Valuation

module K5.Agreement {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

-- Only the four algebra names this file speaks. Pt and _≤ᴮ_ give the Boolean
-- side its conditions and its order; Pt≡ is the one place two points are
-- identified, and it identifies them by their CODES, membership being a
-- proposition. Lattice is opened for ⊤ᴮ alone, which is what makes the
-- Boolean side of K3's Poset module inhabited.

open K4.Algebra 𝒮 using ( Pt; Pt≡; _≤ᴮ_; ≤ᴮ-refl; ⊆ˢ-trans
                        ; Lattice; Complement )

--------------------------------------------------------------------------------
-- The poset layer
--------------------------------------------------------------------------------

module Poset (carrier order : S) where

  open K5.Frame.Poset 𝒮 carrier order using ( Cond; _≼ᶜ_; ForcingBase )

--------------------------------------------------------------------------------
-- The name kernel, taken flat, and the ONE application of K3's value module
--------------------------------------------------------------------------------

  -- Seven of these eight parameters are exactly K3's module Names
  -- (Valuation.agda:148-156), character for character. The eighth, paths, is
  -- the path realization: K3 puts it in module Standard because no law of the
  -- value relation needs it, and this file needs it for one reason only,
  -- namely that trᴮ's entry law emits an ≈ˢ and entry-inj consumes a host
  -- path (TranslateForward.agda:436-442, NameKernel.agda:321). entry-inj is
  -- K3's Standard parameter too, for the same reason.
  --
  -- Rule 13, and it is measured rather than asserted: this list is derived
  -- from what the two layers below EXPORT and not from the architecture's
  -- prose. Section 1.8 of the architecture states the agreement with two
  -- IsNameᴾ hypotheses. They are not in this telescope because nothing uses
  -- them; see module Architecture at the foot of the file, where the
  -- architecture's signature is delivered by discarding them.

  module Kernel
    (entry       : S → S → S)                                 -- NameKernel:241
    (entry-inj   : {x b y c : S} → entry x b ≡ entry y c
                 → (x ≡ y) × (b ≡ c))                         -- NameKernel:309
    (Child       : S → S → Type ℓ)                            -- NameKernel:356
    (isPropChild : (x n : S) → isProp (Child x n))            -- NameKernel:359
    (child-entry : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)
    (child-wf    : WellFounded Child)                         -- NameKernel:380
    (∅ᴺ          : S)
    (∅ᴺ-spec     : (z : S) → (z ∈ˢ ∅ᴺ) ≡ ⊥)
    (paths       : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
    where

    -- THE ONE APPLICATION, trap T-E4. Every argument is a variable, so rule
    -- 2's tightest seal holds structurally and rule 2b's third threshold
    -- cannot be reached from here: nothing in this file has a type nesting
    -- two operations of an unsealed coded algebra, because no coded
    -- operation occurs at all.

    module VN = Valuation.Names 𝒮 entry Child isPropChild child-entry
                                  child-wf ∅ᴺ ∅ᴺ-spec

    -- The two crossings between the structure's equality and host paths.
    -- K3 names them in the same way at Valuation.agda:513-517 and the forward
    -- translation at TranslateForward.agda:163-170; both are one subst.

    ≈ˢ→≡ : {x y : S} → ⟨ x ≈ˢ y ⟩ → x ≡ y
    ≈ˢ→≡ {x} {y} = subst ⟨_⟩ (paths x y)

    ≡→≈ˢ : {x y : S} → x ≡ y → ⟨ x ≈ˢ y ⟩
    ≡→≈ˢ {x} {y} = subst ⟨_⟩ (sym (paths x y))

    ≈ˢ-refl : (x : S) → ⟨ x ≈ˢ x ⟩
    ≈ˢ-refl x = ≡→≈ˢ refl

--------------------------------------------------------------------------------
-- The two instantiations of the one value module
--------------------------------------------------------------------------------

    -- The frame layer. B, L, Cm and fb are Track A's, and Track A's record is
    -- the only source of the poset's three order facts and of the embedding.
    -- Note what is NOT here: no ext, no paths of the Forcing telescope, no
    -- CodedComplete, no K4.Implication. This file never mentions _⊩ᴮ_, so the
    -- frame's classical layer is out of scope; Track A measured that Kc is
    -- projected by nothing (REPORT-A.md, correction A-4) and this file
    -- projects it too.

    module Frame
      (B : S) (L : Lattice B) (Cm : Complement B L)
      (fb : ForcingBase B L Cm)
      where

      open ForcingBase fb using ( ≼-refl; ≼-trans; inhabited; i )
      open Lattice L using ( ⊤ᴮ )

      -- K3's module Poset at the CONDITIONS. These five arguments are
      -- Track D's frameNotion field for field (K5/Generic.agda:120-128),
      -- which is itself K2's decode (CodedCompletion.agda:239-249) at a
      -- ForcingBase. So Sub, _∈ᴾ_, positive and isFilter on this side ARE
      -- K2's, reached through K3's assembly of K2's record, and no second
      -- copy of any of them is declared anywhere in K5.

      module VP = VN.Poset carrier
        (λ p q → fst p ≼ᶜ fst q)
        (λ p → ≼-refl (fst p) (snd p))
        (λ {p} {q} {r} h k →
           ≼-trans (fst p) (fst q) (fst r) (snd p) (snd q) (snd r) h k)
        (PT.map (λ { (p , hp) → p , hp }) inhabited)

      -- The SAME module at the ALGEBRA. This is the bi-instantiability the
      -- architecture's section 1.8 asserts, here checked by the machine:
      -- Conditions B is Pt B, the order is the algebra's internal inclusion,
      -- and the inhabitedness the record demands is the lattice's top. The
      -- top is a FIELD of Lattice (K4/Algebra.agda:103), so this costs
      -- nothing and in particular costs no density of the image: the
      -- B-side notion is inhabited whether or not any condition maps onto
      -- anything.

      module VU = VN.Poset B
        (λ u v → u ≤ᴮ v)
        ≤ᴮ-refl
        (λ {u} {v} {w} h k → ⊆ˢ-trans h k)
        ∣ ⊤ᴮ ∣₁

--------------------------------------------------------------------------------
-- The translation, as a parameter with its entry law
--------------------------------------------------------------------------------

      -- Ledger clause L10. These two are typed from the producing export and
      -- not from the architecture's prose: trᴮ is
      -- TranslateForward.agda:387 and the entry law is
      -- TranslateForward.agda:436-442, with EntryClass inlined and with the
      -- one substitution the instantiation makes, iCode := λ q → fst (i q).
      -- The Target layer that produces them takes iCode : Cond → S and
      -- i∈B : (q : Cond) → ⟨ iCode q ∈ˢ B ⟩ separately
      -- (TranslateForward.agda:343-344); at a ForcingBase those two are the
      -- two projections of one field, and Σ has eta, so the pair is the
      -- field. A drift in either spelling fails in the seam probe rather
      -- than passing silently.
      --
      -- Note what the entry law does NOT carry: no name hypothesis. Track F
      -- of K3 records the reason in its own source (TranslateForward.agda:
      -- 432-434): support and weightsAt are total, so the law holds at an
      -- arbitrary ground code. That is what lets the whole of this file
      -- dispense with IsNameᴾ.

      module Translation
        (trᴮ         : S → S)
        (trᴮ-entries : (n e : S) → (e ∈ˢ trᴮ n)
                     ≡ ⋁ S (λ x → ⋁ S (λ p → ⋁ ⟨ p ∈ˢ carrier ⟩ (λ hp →
                         (entry x p ∈ˢ n)
                         ⊓ (e ≈ˢ entry (trᴮ x) (fst (i (p , hp))))))))
        where

--------------------------------------------------------------------------------
-- The agreement
--------------------------------------------------------------------------------

        -- G is a subset of the conditions and U a subset of the algebra, and
        -- the only thing assumed about the pair is the correspondence at
        -- images. In particular U is NOT assumed to be Uof G, and nothing
        -- below reads Uof's definition: the agreement is a theorem about any
        -- U that reflects G at the image of the embedding. Rule 7 in its
        -- deeper form: it means the valuation agreement survives any later
        -- change to how the Boolean-side filter is built.
        --
        -- READ THE SCOPE OF THAT GENERALITY EXACTLY, because it is orthogonal
        -- to Track H's interface and not stronger than it. The bridge
        -- constrains U ONLY ON THE IMAGE OF i. Track H's round trip needs
        -- U-to-below, that every element of U has a condition below it whose
        -- image U also contains, which constrains U EVERYWHERE and says U is
        -- GENERATED by images of members of G. A subset can reflect G on the
        -- image and still carry an element with no condition below it at all,
        -- so the bridge does not give U-to-below and the round trip is a
        -- theorem about the pushforward Uof G rather than about an arbitrary
        -- corresponding U. Track K carries the two rows separately.
        --
        -- The two halves are separated because their costs differ. At
        -- U := Uof G, bridge→ is generic-forward (K5/Generic.agda:169-170),
        -- FREE, and bridge← is generic-reflect (:370-380), PAID at LEM ℓ and
        -- at genericity. K5/AgreementAtUof.agda supplies both from Track D.

        module Agree
          (G : VP.Sub) (U : VU.Sub)
          (bridge→ : (p : Cond) → ⟨ p VP.∈ᴾ G ⟩ → ⟨ U (i p) ⟩)
          (bridge← : (p : Cond) → ⟨ U (i p) ⟩ → ⟨ p VP.∈ᴾ G ⟩)
          where

          module Pv = VP.Value G
          module Uv = VU.Value U

          -- The four relations, named as the architecture names them
          -- (section 1.8). They are two instantiations of one definition and
          -- not four definitions: grep for "PairRec", for "≈Rec" and for
          -- "_≈[" in this file and the count of declarations is zero.

          infix 20 _≈[G]_ _∈[G]_ _≈[U]_ _∈[U]_

          _≈[G]_ : S → S → Ω
          _≈[G]_ = Pv._≈[G]_

          _∈[G]_ : S → S → Ω
          _∈[G]_ = Pv._∈[G]_

          _≈[U]_ : S → S → Ω
          _≈[U]_ = Uv._≈[G]_

          _∈[U]_ : S → S → Ω
          _∈[U]_ = Uv._∈[G]_

--------------------------------------------------------------------------------
-- Activity, forward and backward
--------------------------------------------------------------------------------

          -- FORWARD. An active entry translates to an active entry. The
          -- weight p of the entry becomes the image i p, which is a Boolean
          -- element by the second projection of that same field, and the
          -- membership of the translated entry is read off the entry law.
          -- This half uses bridge→ and nothing else.

          active→ : (n x : S) → ⟨ Pv.‖Active‖ x n ⟩
                  → ⟨ Uv.‖Active‖ (trᴮ x) (trᴮ n) ⟩
          active→ n x = PT.map step
            where
              step : Pv.Active x n → Uv.Active (trᴮ x) (trᴮ n)
              step (p , hp , member , hG) =
                fst (i (p , hp)) , snd (i (p , hp)) , mem , bridge→ (p , hp) hG
                where
                  mem : ⟨ entry (trᴮ x) (fst (i (p , hp))) ∈ˢ trᴮ n ⟩
                  mem = subst ⟨_⟩
                    (sym (trᴮ-entries n (entry (trᴮ x) (fst (i (p , hp))))))
                    ∣ x , ∣ p , ∣ hp , member
                                     , ≈ˢ-refl (entry (trᴮ x)
                                                      (fst (i (p , hp)))) ∣₁ ∣₁ ∣₁

          -- BACKWARD, and this is where every trap of the track meets.
          --
          -- An active entry of trᴮ n arrives as a subname code y and a
          -- Boolean weight b. The entry law decomposes it: some entry
          -- ⟨x, p⟩ of n has entry y b equal, in the structure's equality, to
          -- entry (trᴮ x) (i p). entry-inj then gives y ≡ trᴮ x and
          -- b ≡ fst (i p) as host paths, and Pt≡ turns the second into an
          -- identification of the two POINTS, because membership in B is a
          -- proposition. The Boolean weight is therefore the image of the
          -- source weight, and bridge← carries it back into G.
          --
          -- T-E1 IN ITS SHARPEST FORM. Nothing here reflects an ORDER. What
          -- is reflected is a MEMBERSHIP, U (i p) to p ∈ G, and it is
          -- reflected at the image of a single condition, which is exactly
          -- the shape Track D proved without separativity and without order
          -- reflection. The identification b ≡ fst (i p) is not injectivity
          -- of i either: it is injectivity of ENTRY, which is Track A's
          -- entry-inj and is about Kuratowski pairs, not about the
          -- embedding. Two distinct conditions may perfectly well have the
          -- same image, and if they do, this lemma returns whichever source
          -- entry the entry law offered; the conclusion is truncated and no
          -- choice is made.
          --
          -- T-E3. The conclusion is an Ω-valued join, so the elimination of
          -- the truncated entry decomposition lands in a proposition. Nothing
          -- in this file ever extracts a condition, a point of B or a name
          -- from a truncation.

          active← : (n y : S) → ⟨ Uv.‖Active‖ y (trᴮ n) ⟩
                  → ⟨ ⋁ S (λ x → Pv.‖Active‖ x n
                                 ⊓ ((y ≡ trᴮ x) , isSetS y (trᴮ x))) ⟩
          active← n y hy = PT.rec (snd (goal n y)) atEntry hy
            where
              goal : (n y : S) → Ω
              goal n y = ⋁ S (λ x → Pv.‖Active‖ x n
                                    ⊓ ((y ≡ trᴮ x) , isSetS y (trᴮ x)))

              atEntry : Uv.Active y (trᴮ n) → ⟨ goal n y ⟩
              atEntry (b , hb , member , hU) =
                PT.rec (snd (goal n y)) atSub
                       (subst ⟨_⟩ (trᴮ-entries n (entry y b)) member)
                where
                  atSub : Σ[ x ∈ S ]
                            ⟨ ⋁ S (λ p → ⋁ ⟨ p ∈ˢ carrier ⟩ (λ hp →
                                (entry x p ∈ˢ n)
                                ⊓ (entry y b ≈ˢ entry (trᴮ x)
                                                     (fst (i (p , hp)))))) ⟩
                        → ⟨ goal n y ⟩
                  atSub (x , t₁) = PT.rec (snd (goal n y)) atWeight t₁
                    where
                      atWeight : Σ[ p ∈ S ]
                                   ⟨ ⋁ ⟨ p ∈ˢ carrier ⟩ (λ hp →
                                       (entry x p ∈ˢ n)
                                       ⊓ (entry y b ≈ˢ entry (trᴮ x)
                                                            (fst (i (p , hp))))) ⟩
                               → ⟨ goal n y ⟩
                      atWeight (p , t₂) = PT.rec (snd (goal n y)) close t₂
                        where
                          close : Σ[ hp ∈ ⟨ p ∈ˢ carrier ⟩ ]
                                    (⟨ entry x p ∈ˢ n ⟩
                                     × ⟨ entry y b ≈ˢ entry (trᴮ x)
                                                           (fst (i (p , hp))) ⟩)
                                → ⟨ goal n y ⟩
                          close (hp , hen , heq) =
                            ∣ x , ∣ p , hp , hen , hG ∣₁ , fst dec ∣₁
                            where
                              dec : (y ≡ trᴮ x) × (b ≡ fst (i (p , hp)))
                              dec = entry-inj (≈ˢ→≡ heq)

                              hU' : ⟨ U (i (p , hp)) ⟩
                              hU' = subst (λ w → ⟨ U w ⟩)
                                      (Pt≡ {B} {b , hb} {i (p , hp)} (snd dec)) hU

                              hG : ⟨ (p , hp) VP.∈ᴾ G ⟩
                              hG = bridge← (p , hp) hU'

--------------------------------------------------------------------------------
-- The agreement of values
--------------------------------------------------------------------------------

          -- THE INDUCTION. One well-founded induction on the FIRST coordinate
          -- alone, at the motive "for every second coordinate". K3 proves
          -- reflexivity, symmetry and transitivity by the same single
          -- induction (Valuation.agda:349, :377, :409) and for the same
          -- reason: every witness either clause produces is a child of the
          -- first code, so the pair recursion is needed to DEFINE the
          -- relation and not to reason about it.
          --
          -- The shape of each of the four clauses is the same. An active
          -- entry on one side is transported to the other by active→ or
          -- pulled back by active←; K3's ≈-fwd or ≈-bwd supplies the partner
          -- on the source side; and the induction hypothesis at the source
          -- subname, which is a child by K3's active-child (:257), converts
          -- the value equality of the partners. The path active← returns is
          -- then used to rewrite the B-side code, and that is the only place
          -- a code is rewritten anywhere in this file.
          --
          -- MEASURED, and worth stating because it contradicts the natural
          -- expectation: NEITHER DIRECTION IS FREE. One might expect the
          -- forward implication of the path to need only bridge→, since it
          -- pushes P-side data forward. It does not. Its two clauses both
          -- begin by taking an ARBITRARY active entry of a TRANSLATED name,
          -- and recognizing that entry as the translation of a source entry
          -- is active←, which is the paid half. So generic-reflect is
          -- consumed by both halves of ≈-agree, and the architecture's ledger
          -- row "≈-agree, ∈-agree | LEM ℓ" is correct but for a reason that
          -- is not the obvious one.

          ≈-agree : (m n : S) → (m ≈[G] n) ≡ (trᴮ m ≈[U] trᴮ n)
          ≈-agree = WFI.induction child-wf
            {P = λ m → (n : S) → (m ≈[G] n) ≡ (trᴮ m ≈[U] trᴮ n)} st
            where
              st : (m : S)
                 → ((x : S) → Child x m
                    → (n : S) → (x ≈[G] n) ≡ (trᴮ x ≈[U] trᴮ n))
                 → (n : S) → (m ≈[G] n) ≡ (trᴮ m ≈[U] trᴮ n)
              st m IH n = ⇔toPath to from
                where
                  to : ⟨ m ≈[G] n ⟩ → ⟨ trᴮ m ≈[U] trᴮ n ⟩
                  to h = Uv.≈-intro c₁ c₂
                    where
                      c₁ : (y : S) → ⟨ Uv.‖Active‖ y (trᴮ m) ⟩
                         → ⟨ ⋁ S (λ w → Uv.‖Active‖ w (trᴮ n) ⊓ (y ≈[U] w)) ⟩
                      c₁ y hy = PT.rec PT.squash₁ pull (active← m y hy)
                        where
                          pull : Σ[ x ∈ S ] (⟨ Pv.‖Active‖ x m ⟩ × (y ≡ trᴮ x))
                               → ⟨ ⋁ S (λ w → Uv.‖Active‖ w (trᴮ n)
                                              ⊓ (y ≈[U] w)) ⟩
                          pull (x , hx , py) = PT.map push (Pv.≈-fwd h x hx)
                            where
                              push : Σ[ z ∈ S ] (⟨ Pv.‖Active‖ z n ⟩
                                                 × ⟨ x ≈[G] z ⟩)
                                   → Σ[ w ∈ S ] (⟨ Uv.‖Active‖ w (trᴮ n) ⟩
                                                 × ⟨ y ≈[U] w ⟩)
                              push (z , hz , e) =
                                trᴮ z , active→ n z hz
                                , subst (λ t → ⟨ t ≈[U] trᴮ z ⟩) (sym py)
                                    (subst ⟨_⟩
                                      (IH x (Pv.active-child x m hx) z) e)

                      c₂ : (w : S) → ⟨ Uv.‖Active‖ w (trᴮ n) ⟩
                         → ⟨ ⋁ S (λ y → Uv.‖Active‖ y (trᴮ m) ⊓ (y ≈[U] w)) ⟩
                      c₂ w hw = PT.rec PT.squash₁ pull (active← n w hw)
                        where
                          pull : Σ[ z ∈ S ] (⟨ Pv.‖Active‖ z n ⟩ × (w ≡ trᴮ z))
                               → ⟨ ⋁ S (λ y → Uv.‖Active‖ y (trᴮ m)
                                              ⊓ (y ≈[U] w)) ⟩
                          pull (z , hz , pw) = PT.map push (Pv.≈-bwd h z hz)
                            where
                              push : Σ[ x ∈ S ] (⟨ Pv.‖Active‖ x m ⟩
                                                 × ⟨ x ≈[G] z ⟩)
                                   → Σ[ y ∈ S ] (⟨ Uv.‖Active‖ y (trᴮ m) ⟩
                                                 × ⟨ y ≈[U] w ⟩)
                              push (x , hx , e) =
                                trᴮ x , active→ m x hx
                                , subst (λ t → ⟨ trᴮ x ≈[U] t ⟩) (sym pw)
                                    (subst ⟨_⟩
                                      (IH x (Pv.active-child x m hx) z) e)

                  from : ⟨ trᴮ m ≈[U] trᴮ n ⟩ → ⟨ m ≈[G] n ⟩
                  from h = Pv.≈-intro d₁ d₂
                    where
                      d₁ : (x : S) → ⟨ Pv.‖Active‖ x m ⟩
                         → ⟨ ⋁ S (λ z → Pv.‖Active‖ z n ⊓ (x ≈[G] z)) ⟩
                      d₁ x hx = PT.rec PT.squash₁ atPartner
                                       (Uv.≈-fwd h (trᴮ x) (active→ m x hx))
                        where
                          atPartner : Σ[ w ∈ S ] (⟨ Uv.‖Active‖ w (trᴮ n) ⟩
                                                  × ⟨ trᴮ x ≈[U] w ⟩)
                                    → ⟨ ⋁ S (λ z → Pv.‖Active‖ z n
                                                   ⊓ (x ≈[G] z)) ⟩
                          atPartner (w , hw , e) = PT.map back (active← n w hw)
                            where
                              back : Σ[ z ∈ S ] (⟨ Pv.‖Active‖ z n ⟩
                                                 × (w ≡ trᴮ z))
                                   → Σ[ z ∈ S ] (⟨ Pv.‖Active‖ z n ⟩
                                                 × ⟨ x ≈[G] z ⟩)
                              back (z , hz , pw) =
                                z , hz
                                , subst ⟨_⟩
                                    (sym (IH x (Pv.active-child x m hx) z))
                                    (subst (λ t → ⟨ trᴮ x ≈[U] t ⟩) pw e)

                      d₂ : (z : S) → ⟨ Pv.‖Active‖ z n ⟩
                         → ⟨ ⋁ S (λ x → Pv.‖Active‖ x m ⊓ (x ≈[G] z)) ⟩
                      d₂ z hz = PT.rec PT.squash₁ atPartner
                                       (Uv.≈-bwd h (trᴮ z) (active→ n z hz))
                        where
                          atPartner : Σ[ w ∈ S ] (⟨ Uv.‖Active‖ w (trᴮ m) ⟩
                                                  × ⟨ w ≈[U] trᴮ z ⟩)
                                    → ⟨ ⋁ S (λ x → Pv.‖Active‖ x m
                                                   ⊓ (x ≈[G] z)) ⟩
                          atPartner (w , hw , e) = PT.map back (active← m w hw)
                            where
                              back : Σ[ x ∈ S ] (⟨ Pv.‖Active‖ x m ⟩
                                                 × (w ≡ trᴮ x))
                                   → Σ[ x ∈ S ] (⟨ Pv.‖Active‖ x m ⟩
                                                 × ⟨ x ≈[G] z ⟩)
                              back (x , hx , pw) =
                                x , hx
                                , subst ⟨_⟩
                                    (sym (IH x (Pv.active-child x m hx) z))
                                    (subst (λ t → ⟨ t ≈[U] trᴮ z ⟩) pw e)

          -- Membership agrees, and it is a COROLLARY and not a second
          -- induction. K3 fixed the dependency order: _∈[G]_ is DEFINED from
          -- _≈[G]_ and the two are never mutual (Valuation.agda:290-294), so
          -- an agreement of the equalities transports through the defining
          -- join directly. The architecture's section 1.8 calls for "one
          -- simultaneous induction"; measured, one induction suffices and the
          -- second statement needs no induction at all.

          ∈-agree : (m n : S) → (m ∈[G] n) ≡ (trᴮ m ∈[U] trᴮ n)
          ∈-agree m n = ⇔toPath to from
            where
              to : ⟨ m ∈[G] n ⟩ → ⟨ trᴮ m ∈[U] trᴮ n ⟩
              to = PT.map (λ { (y , hy , e) →
                     trᴮ y , active→ n y hy , subst ⟨_⟩ (≈-agree m y) e })

              from : ⟨ trᴮ m ∈[U] trᴮ n ⟩ → ⟨ m ∈[G] n ⟩
              from = PT.rec PT.squash₁ atPartner
                where
                  atPartner : Σ[ w ∈ S ] (⟨ Uv.‖Active‖ w (trᴮ n) ⟩
                                          × ⟨ trᴮ m ≈[U] w ⟩)
                            → ⟨ m ∈[G] n ⟩
                  atPartner (w , hw , e) = PT.map back (active← n w hw)
                    where
                      back : Σ[ y ∈ S ] (⟨ Pv.‖Active‖ y n ⟩ × (w ≡ trᴮ y))
                           → Σ[ y ∈ S ] (⟨ Pv.‖Active‖ y n ⟩ × ⟨ m ≈[G] y ⟩)
                      back (y , hy , pw) =
                        y , hy
                        , subst ⟨_⟩ (sym (≈-agree m y))
                            (subst (λ t → ⟨ trᴮ m ≈[U] t ⟩) pw e)

--------------------------------------------------------------------------------
-- The two standard names, and the statement Track J left open
--------------------------------------------------------------------------------

          -- K3's two computations at the standard names are the only two of
          -- the roadmap's five exit examples that are runnable in K5 at all
          -- (architecture part 6.4): check-faithful (Valuation.agda:655-657)
          -- and generic-value (:659-661), reached here through the positivity
          -- forms at :611 and :633, both instance free. They are stated
          -- on the P-side only. Composing each with the membership agreement
          -- moves it across the translation, and the second of the two is
          -- exactly the sentence Track J's fourth refutation was careful NOT
          -- to refute.
          --
          -- The seven parameters are K3's module Standard verbatim
          -- (Valuation.agda:493-503). entry-inj and the path realization are
          -- already in this file's telescope, so only ext-path and the two
          -- standard names with their specifications are new, and none of the
          -- three is a new ground axiom for K5: they are Track H's of K3.

          module StandardNames
            (ext-path    : {a b : S} → ((x : S) → (x ∈ˢ a) ≡ (x ∈ˢ b)) → a ≡ b)
            (checkᴾ      : S → S)
            (checkᴾ-spec : (a e : S) → (e ∈ˢ checkᴾ a)
                         ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ ⋁ S (λ p → (p ∈ˢ carrier)
                                ⊓ (e ≈ˢ entry (checkᴾ y) p))))
            (Γᴾ          : S)
            (Γᴾ-spec     : (e : S) → (e ∈ˢ Γᴾ)
                         ≡ ⋁ S (λ p → (p ∈ˢ carrier) ⊓ (e ≈ˢ entry (checkᴾ p) p)))
            where

            module PStd = Pv.Standard entry-inj paths ext-path
                                      checkᴾ checkᴾ-spec Γᴾ Γᴾ-spec

            -- The ground copy survives the translation. Two ground sets stand
            -- in the membership relation exactly when the TRANSLATIONS of
            -- their check names do, at Uof G on the Boolean side.

            -- Stated at POSITIVITY and then at the filter, in that order,
            -- because that is the true cost. K3 proves both computations
            -- inside module WithPositivity (Valuation.agda:522) and names
            -- positivity as the only filter law any of its theorems consumes
            -- (:220-223); its isFilter-shaped wrappers (:651-661) project
            -- inhabited and discard the rest. Rule 13: taking the filter here
            -- would over-charge the statement by two hypotheses, which is the
            -- same correction the architecture makes for the ground copy at
            -- trap T-F2.

            check-faithful-at-positive :
                ⟨ VP.positive G ⟩ → (a b : S)
              → (trᴮ (checkᴾ a) ∈[U] trᴮ (checkᴾ b)) ≡ (a ∈ˢ b)
            check-faithful-at-positive pos a b =
              sym (∈-agree (checkᴾ a) (checkᴾ b))
              ∙ PStd.WithPositivity.check-faithful pos a b

            check-faithful-across :
                VP.isFilter G → (a b : S)
              → (trᴮ (checkᴾ a) ∈[U] trᴮ (checkᴾ b)) ≡ (a ∈ˢ b)
            check-faithful-across fil =
              check-faithful-at-positive (VP.filter-positive fil)

            -- AND THE STATEMENT TRACK J LEFT OPEN. Track J refuted
            -- trᴮ Γᴾ ≡ U̇ AS CODES (K5/RefutedOrder.agda:204-220) and said in
            -- the same breath what that does not refute: the two names may
            -- still have the same VALUE at a filter, because an entry of
            -- weight ⊥ᴮ is never active. Here is the value side of that
            -- distinction, proved rather than left as a hope. The forward
            -- translation of the poset generic name has, at Uof G, exactly
            -- the value the poset generic name has at G: the translated check
            -- name of a condition is a value-member of it precisely when the
            -- condition lies in G.
            --
            -- Note what this does NOT say. It does not say trᴮ Γᴾ and U̇ have
            -- the same value: U̇ is not in this file, K5 states nothing about
            -- it, and Track J's refutation of the code identity stands
            -- untouched. It says that the value of trᴮ Γᴾ is the one a
            -- generic name should have, which is the only thing the truth
            -- lemma and the extension map ever ask of it.

            generic-name-value-at-positive :
                ⟨ VP.positive G ⟩ → (p : Cond)
              → (trᴮ (checkᴾ (fst p)) ∈[U] trᴮ Γᴾ) ≡ (p VP.∈ᴾ G)
            generic-name-value-at-positive pos p =
              sym (∈-agree (checkᴾ (fst p)) Γᴾ)
              ∙ PStd.WithPositivity.generic-value pos p

            generic-name-value-across :
                VP.isFilter G → (p : Cond)
              → (trᴮ (checkᴾ (fst p)) ∈[U] trᴮ Γᴾ) ≡ (p VP.∈ᴾ G)
            generic-name-value-across fil =
              generic-name-value-at-positive (VP.filter-positive fil)

--------------------------------------------------------------------------------
-- The positive control X4 asks for
--------------------------------------------------------------------------------

          -- The correspondence, transcribed under its own name, exactly as
          -- Track D states it (K5/Generic.agda:411-418). It is a path in Ω,
          -- which is legitimate for a theorem; ledger clause L13 forbids a
          -- path in Ω as a record FIELD and this file declares no record.
          --
          -- It is EQUIVALENT to the two entailments this module assumes, and
          -- it is what the induction consumes at every node. Recording it
          -- here makes the exit item's demand checkable: the agreement needs
          -- exactly this and exactly nothing else about the pair (G, U).

          generic-bridge : (p : Cond) → (p VP.∈ᴾ G) ≡ U (i p)
          generic-bridge p = ⇔toPath (bridge→ p) (bridge← p)

        -- The architecture's signature for the two agreements, with the two
        -- name hypotheses it prints (section 1.8). They are taken and
        -- DISCARDED, which is the measured negative of this track: the
        -- agreement holds at arbitrary ground codes. K3 recorded the same
        -- fact about its own relation, that _≈[G]_ is a relation on CODES
        -- and never mentions IsName (REPORT-I.md:130-131), and the forward
        -- translation's entry law carries no name hypothesis either
        -- (TranslateForward.agda:432-434). Keeping this wrapper is ledger
        -- clause L10 applied to a signature rather than to a parameter: if a
        -- later track needs the name hypotheses, it finds them here.

        module Architecture
          (IsNameᴾ : S → Ω)
          (G : VP.Sub) (U : VU.Sub)
          (bridge→ : (p : Cond) → ⟨ p VP.∈ᴾ G ⟩ → ⟨ U (i p) ⟩)
          (bridge← : (p : Cond) → ⟨ U (i p) ⟩ → ⟨ p VP.∈ᴾ G ⟩)
          where

          open Agree G U bridge→ bridge← public

          ≈-agree-at-names : (m n : S) → ⟨ IsNameᴾ m ⟩ → ⟨ IsNameᴾ n ⟩
                           → (m ≈[G] n) ≡ (trᴮ m ≈[U] trᴮ n)
          ≈-agree-at-names m n _ _ = ≈-agree m n

          ∈-agree-at-names : (m n : S) → ⟨ IsNameᴾ m ⟩ → ⟨ IsNameᴾ n ⟩
                           → (m ∈[G] n) ≡ (trᴮ m ∈[U] trᴮ n)
          ∈-agree-at-names m n _ _ = ∈-agree m n

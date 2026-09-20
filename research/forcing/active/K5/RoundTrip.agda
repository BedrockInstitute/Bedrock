{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track H: the surjectivity clause of the extension map.
--
-- THE QUESTION. Track E's ≈-agree and ∈-agree say that the forward
-- translation trᴮ carries the value of a poset name at a filter G to the value
-- of the translated name at the corresponding subset Uof G of the algebra.
-- That makes the extension map ext-map τ = trᴮ (fst τ) an ∈-monomorphism from
-- the poset names into the Boolean names. A monomorphism is not an
-- isomorphism, and the missing half is the one this file proves: is every
-- Boolean name, AT THE CORRESPONDING FILTER, equal in value to the translate
-- of some poset name? The answer is yes, the witness is canonical, and it is
-- K3's reverse translation trᴾ: for every ground code n,
--
--     trᴮ (trᴾ n) ≈[U] n.
--
-- WHAT MAKES THIS TRUE, IN ONE PARAGRAPH. Compose the two entry laws. An
-- entry of trᴾ n is entry (trᴾ x) p for an entry x b of n and a condition p in
-- below b (TranslateReverse.agda:656-659). An entry of trᴮ m is
-- entry (trᴮ y) (iCode (q , hq)) for an entry y q of m (TranslateForward.agda
-- :436-442). So an entry of trᴮ (trᴾ n) is entry (trᴮ (trᴾ x)) (iCode p) for
-- an entry x b of n and a p in below b. The two names therefore have entries
-- at the same subnames up to one application of trᴮ ∘ trᴾ, but at completely
-- different WEIGHTS: n weights x by a Boolean element b, while trᴮ (trᴾ n)
-- weights trᴮ (trᴾ x) by the images of the conditions below b. The value
-- relation does not see a weight, it sees only whether a weight is ACTIVE,
-- that is whether it lies in the subset U. And at U = Uof G the two activity
-- classes coincide:
--
--   * if b is in Uof G then some q in G has i q ≤ᴮ b, so the condition q lies
--     in below b and its image i q is in Uof G, witnessed by q itself;
--   * if p lies in below b and i p is in Uof G then some q in G has
--     i q ≤ᴮ i p ≤ᴮ b, so b is in Uof G.
--
-- Both directions are ⊆ˢ-transitivity and nothing else. That is the whole
-- mathematical content of this file; everything below is the induction that
-- carries it down the name, plus the transports that turn the structure's own
-- equality ≈ˢ into a host path.
--
-- ---------------------------------------------------------------------------
-- THE THREE THINGS THIS THEOREM IS NOT. Each is repeated below beside the
-- signature it constrains, on the model K3 set for its own two translations.
--
--  N1. IT IS NOT K2'S RECOVERY THEOREM. K2's recover (Certificate.agda:434-435)
--      is an equation in the ALGEBRA: supᴮ (iImage (below b)) ≡ b, the
--      statement that every element is the supremum of the image of its own
--      coded extension. It needs iImage, a coded direct image former that no
--      inhabitant of Certificate.Embedding supplies anywhere in the programme,
--      and it needs a host-indexed supremum. Nothing of the kind appears here.
--      The statement below is a proposition about the VALUE OF A NAME AT A
--      SUBSET, at a type (⟨ _ ≈[U] _ ⟩ : Type ℓ) that is not the type of any
--      algebra equation, and it consumes no supremum, no image former and no
--      Collection. Architecture part 6.3 records the correction: K3 wrote that
--      the denotational round trip "consumes K2's recover"
--      (TranslateForward.agda:30-31), and recover is not what it consumes.
--
--  N2. THERE IS NO RAW ROUND TRIP, IN EITHER DIRECTION, AND NONE IS CLAIMED.
--      K3 states it at TranslateReverse.agda:45-46: "Nothing below states
--      trᴾ (trᴮ n) ≡ n or trᴮ (trᴾ n) ≡ n, and neither is true." No line of
--      this file states a path between ground codes. The theorem is a value
--      equality at a named subset and it is nowhere else. In particular trᴮ
--      (trᴾ n) and n do not have the same entries, do not have the same
--      support, and are not equal as codes.
--
--  N3. trᴾ IS NOT INJECTIVE AND THIS DOES NOT MAKE IT SO. K3's reason is
--      concrete (TranslateReverse.agda:51-54): below ⊥ᴮ is EMPTY, so a
--      bottom-weighted child emits no entry at all, and two Boolean names
--      differing only in bottom-weighted entries have the same translation.
--      The theorem below is consistent with that and does not repair it: a
--      bottom-weighted entry is never active, because ⊥ᴮ is never in a filter,
--      so the value relation never sees the entry that trᴾ drops. The
--      surjectivity clause lives on exactly that line. Track J refuted the
--      identification of the forward translation of the poset generic name
--      with the Boolean one AS CODES (K5/RefutedOrder.agda:204-211), and was
--      careful to write down what that does not refute: "the two names may
--      still have the same VALUE at a filter, since an entry of weight ⊥ᴮ is
--      never active" (K5/RefutedOrder.agda:41-44). This file is on the value
--      side of that line and inherits both the freedom and the prohibition:
--      it states one value equality and not one code equality, and the
--      deliberate break recorded in REPORT-H section 6 shows that the proof
--      below does NOT prove the code equality.
--
-- ---------------------------------------------------------------------------
-- WHICH HALF THIS DELIVERS AND WHICH REMAINS. K3 deferred "the denotational
-- round trip" to K4 and K5 by name, twice (TranslateForward.agda:30-31,
-- TranslateReverse.agda:47-49), without saying that the phrase covers two
-- different theorems. They are:
--
--   (H) trᴮ (trᴾ n) ≈[U] n, at the BOOLEAN side, U = Uof G. This file. It is
--       FREE: no excluded middle, no filter law, no genericity, no coded dense
--       set. Its only inputs are the two entry laws and the two activity
--       bullets above.
--
--   (R) trᴾ (trᴮ m) ≈[G] m, at the POSET side. NOT proved here and not needed
--       by the extension map. It is not free either: its forward half asks,
--       from a condition r in G with i r ≤ᴮ i p, that p itself lie in G, which
--       is exactly generic-reflect (K5/Generic.agda:370-375) and therefore
--       costs LEM ℓ, the meets field of genericity, and isFilter G. Its
--       backward half is free, by below-in at i p. So (R) is a PAID theorem
--       about a second value relation, and this file states it as an open item
--       with its price rather than proving it.
--
-- Surjectivity of the extension map needs (H) alone, and ext-surjective below
-- says so with the witness exhibited.
--
-- ---------------------------------------------------------------------------
-- HOW THIS FILE IS BUILT, and why it applies no heavy module.
--
-- Ledger clause L2's reason applied one level further out: every object this
-- theorem speaks about enters as a MODULE PARAMETER, so every one of them is a
-- variable that cannot unfold, which is preamble rule 2's tightest seal and
-- makes rule 2b structurally unreachable. The translations enter as trᴮ, trᴾ
-- and their two entry laws, typed character for character from
-- TranslateForward.agda:436-442 and TranslateReverse.agda:656-659 (ledger
-- clause L10); the value relation enters as _≈[U]_, ‖Active‖ and three of its
-- laws, typed from Valuation.agda:337-343 and :245-251; and the corresponding
-- subset enters as U with the two activity bullets as U-to-below and
-- U-from-below. Not one heavy module is applied: the only import that is a
-- module application at all is K4.Algebra, which REPORT-A measured light for
-- exactly this reason, and it is taken for Pt and Pt≡ alone.
--
-- The seams are proved and not asserted, in three companion files, on the
-- model of Track B's K5/ClausesAtFrame.agda:
--   K5/RoundTripAtUof.agda    fills U from Track D's Uof and proves the two
--                             activity bullets FREE at a ForcingBase;
--   K5/RoundTripAtValue.agda  fills the value surface from K3's Valuation at
--                             (B , ≤ᴮ), the one heavy module application this
--                             track is budgeted;
--   K5/RoundTripTranslate.agda  fills trᴮ, trᴾ and the two entry laws from
--                             K3's own TranslateForward and TranslateReverse.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import K4.Algebra

module K5.RoundTrip {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Induction.WellFounded using ( WellFounded; module WFI )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

-- Pt and Pt≡ only. The scope contract of K4/Implication.agda:64-76 does not
-- bite here because no record type name is taken.

open K4.Algebra 𝒮 using ( Pt; Pt≡ )

--------------------------------------------------------------------------------
-- The name kernel, in the seven-line form both translations and the value
-- relation already agree on
--------------------------------------------------------------------------------

-- entry, Child, child-entry and child-wf are Track A of K3
-- (NameKernel.agda:253, :368, :369, :392) and entry-inj is :321. Every one of
-- the three consumers below takes exactly these, so taking them once here is
-- what makes the three seams line up without an adapter.
--
-- WHAT IS NOT TAKEN, and this is a measured over-declaration in the
-- architecture rather than a defect here. Valuation.Names asks in addition for
-- isPropChild, ∅ᴺ and ∅ᴺ-spec; this file needs none of the three, because it
-- never eliminates a Child into a proposition and never speaks of the empty
-- name. TranslateReverse.Names asks in addition for entry-isKPair and
-- child-elim; this file needs neither. They reappear in the seam files, where
-- the producing modules are actually applied.

module Kernel
  (entry       : S → S → S)                                  -- NameKernel:253
  (entry-inj   : {x b y c : S} → entry x b ≡ entry y c
               → (x ≡ y) × (b ≡ c))                          -- NameKernel:321
  (Child       : S → S → Type ℓ)                             -- NameKernel:368
  (child-entry : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)  -- NameKernel:369
  (child-wf    : WellFounded Child)                          -- NameKernel:392
  (≈ˢ-paths    : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
  where

  -- The structure's own equality is a field into Ω and is not host path
  -- equality by definition. Both entry laws emit an ≈ˢ and entry-inj consumes
  -- a path, so every crossing in this file goes through these three lines.
  -- This is TranslateForward.agda:162-172 verbatim in substance.

  ≈ˢ→≡ : {x y : S} → ⟨ x ≈ˢ y ⟩ → x ≡ y
  ≈ˢ→≡ {x} {y} = subst ⟨_⟩ (≈ˢ-paths x y)

  ≡→≈ˢ : {x y : S} → x ≡ y → ⟨ x ≈ˢ y ⟩
  ≡→≈ˢ {x} {y} = subst ⟨_⟩ (sym (≈ˢ-paths x y))

  ≈ˢ-refl : (x : S) → ⟨ x ≈ˢ x ⟩
  ≈ˢ-refl x = ≡→≈ˢ refl

--------------------------------------------------------------------------------
-- The two translations, as their entry laws and nothing else
--------------------------------------------------------------------------------

  -- Neither trᴮ nor trᴾ is read through its recursion here. Both are host
  -- well-founded recursions whose computation law is propositional, and K3
  -- says in both files that every consumer reads the translated name through
  -- the ENTRY LAW rather than by unfolding. This file obeys that literally:
  -- trᴮ and trᴾ are opaque functions S → S and the two entry laws are the only
  -- facts about them in scope.
  --
  -- WHAT IS NOT TAKEN, measured. below-sub (TranslateReverse.agda:455) is in
  -- the producing telescope and is NOT consumed by anything below: the
  -- conditions this proof needs come already paired with their carrier
  -- membership, out of the forward entry law's ⋁ ⟨ p ∈ˢ carrier ⟩ in one
  -- direction and out of U-to-below's ⋁ Cond in the other. Neither trᴮ-name
  -- nor trᴾ-name nor either support law nor either closure law is consumed
  -- either; trᴾ-name enters module Named below and only to package
  -- surjectivity, never to prove the value equality.

  module Translation
    (carrier B : S)
    (iCode : (Σ[ p ∈ S ] ⟨ p ∈ˢ carrier ⟩) → S)              -- TranslateForward:433
    (i∈B   : (q : Σ[ p ∈ S ] ⟨ p ∈ˢ carrier ⟩) → ⟨ iCode q ∈ˢ B ⟩)
    (below : Pt B → S)                                       -- TranslateReverse:454
    (trᴮ : S → S)                                            -- TranslateForward:387
    (trᴮ-entries : (n e : S) → (e ∈ˢ trᴮ n)
                 ≡ ⋁ S (λ x → ⋁ S (λ p → ⋁ ⟨ p ∈ˢ carrier ⟩ (λ hp →
                     (entry x p ∈ˢ n)
                     ⊓ (e ≈ˢ entry (trᴮ x) (iCode (p , hp)))))))
                                                             -- TranslateForward:436-442
    (trᴾ : S → S)                                            -- TranslateReverse:548
    (trᴾ-entries : (n e : S) → (e ∈ˢ trᴾ n)
                 ≡ ⋁ S (λ x → ⋁ S (λ b → ⋁ ⟨ b ∈ˢ B ⟩ (λ hb → ⋁ S (λ p →
                     (entry x b ∈ˢ n) ⊓ ((p ∈ˢ below (b , hb))
                        ⊓ (e ≈ˢ entry (trᴾ x) p)))))))
                                                             -- TranslateReverse:656-659
    where

    -- CodedCompletion.agda:223-224, and the same Σ shape as Pt. Written out in
    -- the telescope above because iCode's type needs it before this line.

    Cond : Type ℓ
    Cond = Σ[ p ∈ S ] ⟨ p ∈ˢ carrier ⟩

    -- The embedding as a point of the algebra, assembled from the two halves
    -- the forward translation takes separately. Track A's ForcingBase carries
    -- it as one field i : Cond → Pt B (K5/Frame.agda:175); K3's Target carries
    -- iCode and i∈B (TranslateForward.agda:433-434). The seam file checks that
    -- the two agree, and by Σ-eta this definition is the identity on that
    -- agreement.

    iPt : Cond → Pt B
    iPt q = iCode q , i∈B q

--------------------------------------------------------------------------------
-- The value relation and the corresponding subset
--------------------------------------------------------------------------------

    -- U is the subset of the ALGEBRA that a subset of the conditions
    -- determines, and it is a bare predicate here. At the seam it is Track D's
    -- Uof G (K5/Generic.agda:150-151), and the two entailments below are
    -- exactly architecture part 6.3's two bullets, both FREE there.
    --
    -- WHY THESE TWO AND NOT A FILTER. The proof needs nothing else about U. It
    -- does not need U upward closed, does not need U directed, does not need U
    -- proper, does not need U to decide anything, and does not need G to be a
    -- filter or to be generic. Stating the interface as the two bullets rather
    -- than as isFilter is preamble rule 13 applied to this track: the
    -- hypothesis list is derived from what the proof consumes and not from
    -- what the layer below happens to export. The negative controls in
    -- REPORT-H record which direction each bullet is spent on.

    module Value
      (U          : Pt B → Ω)
      (_≈[U]_     : S → S → Ω)                              -- Valuation:288 at (B , Uof G)
      (‖Active‖   : S → S → Ω)                              -- Valuation:250-251
      (≈-intro    : {m n : S}
                  → ((x : S) → ⟨ ‖Active‖ x m ⟩
                     → ⟨ ⋁ S (λ y → ‖Active‖ y n ⊓ (x ≈[U] y)) ⟩)
                  → ((y : S) → ⟨ ‖Active‖ y n ⟩
                     → ⟨ ⋁ S (λ x → ‖Active‖ x m ⊓ (x ≈[U] y)) ⟩)
                  → ⟨ m ≈[U] n ⟩)                           -- Valuation:337-343
      (active-in  : (x n b : S) (hb : ⟨ b ∈ˢ B ⟩)
                  → ⟨ entry x b ∈ˢ n ⟩ → ⟨ U (b , hb) ⟩
                  → ⟨ ‖Active‖ x n ⟩)                       -- Valuation:245-251
      (active-out : (x n : S) (Q : Ω) → ⟨ ‖Active‖ x n ⟩
                  → ((b : S) (hb : ⟨ b ∈ˢ B ⟩) → ⟨ entry x b ∈ˢ n ⟩
                     → ⟨ U (b , hb) ⟩ → ⟨ Q ⟩)
                  → ⟨ Q ⟩)                                  -- Valuation:245-251
      (U-to-below   : (b : Pt B) → ⟨ U b ⟩
                    → ⟨ ⋁ Cond (λ q → (fst q ∈ˢ below b) ⊓ U (iPt q)) ⟩)
      (U-from-below : (b : Pt B) (q : Cond) → ⟨ fst q ∈ˢ below b ⟩
                    → ⟨ U (iPt q) ⟩ → ⟨ U b ⟩)
      where

--------------------------------------------------------------------------------
-- The theorem
--------------------------------------------------------------------------------

      -- The surjectivity clause, in the form that carries no hypothesis it
      -- does not use. n ranges over ALL ground codes: neither entry law has a
      -- name hypothesis, because K3 made support and weightsAt total on both
      -- sides, and the activity of an entry already supplies the membership
      -- ⟨ b ∈ˢ B ⟩ that the reverse entry law asks for. The architecture prints
      -- this statement with ⟨ IsNameᴮ n ⟩ in front (part 1.9); that hypothesis
      -- is not consumed and module Named below records it as a measured
      -- over-declaration while still shipping the architecture's signature.
      --
      -- The induction is on Child, at the motive "trᴮ (trᴾ n) has the value of
      -- n". It is a SINGLE induction and not a pair recursion: the two names
      -- compared are n and a function of n, so only one coordinate descends,
      -- and the value equality at the subnames is the induction hypothesis
      -- itself. Neither symmetry nor transitivity of the value relation is
      -- used, which is why ≈-intro is the only law of the relation in the
      -- telescope besides the two activity readings.

      ext-onto-raw : (n : S) → ⟨ trᴮ (trᴾ n) ≈[U] n ⟩
      ext-onto-raw =
        WFI.induction child-wf {P = λ n → ⟨ trᴮ (trᴾ n) ≈[U] n ⟩} step
        where
        step : (n : S)
             → ((x : S) → Child x n → ⟨ trᴮ (trᴾ x) ≈[U] x ⟩)
             → ⟨ trᴮ (trᴾ n) ≈[U] n ⟩
        step n IH = ≈-intro onto back
          where

          -- FIRST CLAUSE. Every active entry of trᴮ (trᴾ n) is matched by an
          -- active entry of n. Peel the forward entry law, then the reverse
          -- one, then use U-from-below to carry the activity of the image of a
          -- condition back up to the activity of the Boolean weight it refines.

          onto : (y : S) → ⟨ ‖Active‖ y (trᴮ (trᴾ n)) ⟩
               → ⟨ ⋁ S (λ z → ‖Active‖ z n ⊓ (y ≈[U] z)) ⟩
          onto y hy = active-out y (trᴮ (trᴾ n)) goal hy fromB
            where
            goal : Ω
            goal = ⋁ S (λ z → ‖Active‖ z n ⊓ (y ≈[U] z))

            fromB : (w : S) (hw : ⟨ w ∈ˢ B ⟩)
                  → ⟨ entry y w ∈ˢ trᴮ (trᴾ n) ⟩ → ⟨ U (w , hw) ⟩ → ⟨ goal ⟩
            fromB w hw he hu =
              PT.rec (snd goal)
                (λ { (x , t₁) → PT.rec (snd goal)
                  (λ { (p , t₂) → PT.rec (snd goal)
                    (λ { (hp , hen , heq) → viaTrᴾ x p hp hen heq })
                    t₂ })
                  t₁ })
                (subst ⟨_⟩ (trᴮ-entries (trᴾ n) (entry y w)) he)
              where

              -- The forward entry law has fired: the entry of trᴮ (trᴾ n) we
              -- hold is the relabelling of an entry ⟨x , p⟩ of trᴾ n, with p a
              -- condition. Now fire the reverse law on that entry.

              viaTrᴾ : (x p : S) (hp : ⟨ p ∈ˢ carrier ⟩)
                     → ⟨ entry x p ∈ˢ trᴾ n ⟩
                     → ⟨ entry y w ≈ˢ entry (trᴮ x) (iCode (p , hp)) ⟩
                     → ⟨ goal ⟩
              viaTrᴾ x p hp hen heq =
                PT.rec (snd goal)
                  (λ { (x' , s₁) → PT.rec (snd goal)
                    (λ { (b , s₂) → PT.rec (snd goal)
                      (λ { (hb , s₃) → PT.rec (snd goal)
                        (λ { (p' , hen' , hpb , heq') →
                               match x' b hb p' hen' hpb heq' })
                        s₃ })
                      s₂ })
                    s₁ })
                  (subst ⟨_⟩ (trᴾ-entries n (entry x p)) hen)
                where

                -- Both laws have fired. n carries the subname x' at the
                -- Boolean weight b, the condition p refines b, and y is the
                -- double translate of x'. The matching entry of n is x' itself.

                match : (x' b : S) (hb : ⟨ b ∈ˢ B ⟩) (p' : S)
                      → ⟨ entry x' b ∈ˢ n ⟩
                      → ⟨ p' ∈ˢ below (b , hb) ⟩
                      → ⟨ entry x p ≈ˢ entry (trᴾ x') p' ⟩
                      → ⟨ goal ⟩
                match x' b hb p' hen' hpb heq' =
                  ∣ x' , active-in x' n b hb hen' hUb , val ∣₁
                  where
                  -- The Kuratowski pairs are injective on both coordinates, so
                  -- the two ≈ˢ equations above are four path equations.

                  decᴮ : (y ≡ trᴮ x) × (w ≡ iCode (p , hp))
                  decᴮ = entry-inj (≈ˢ→≡ heq)

                  decᴾ : (x ≡ trᴾ x') × (p ≡ p')
                  decᴾ = entry-inj (≈ˢ→≡ heq')

                  -- Membership in B is a proposition, so the weight we hold
                  -- and the image of the condition are the same POINT and not
                  -- merely the same code. This is where Pt≡ is spent, once.

                  atImage : (w , hw) ≡ iPt (p , hp)
                  atImage = Pt≡ {B} (snd decᴮ)

                  hUi : ⟨ U (iPt (p , hp)) ⟩
                  hUi = subst (λ t → ⟨ U t ⟩) atImage hu

                  hpb₀ : ⟨ p ∈ˢ below (b , hb) ⟩
                  hpb₀ = subst (λ t → ⟨ t ∈ˢ below (b , hb) ⟩) (sym (snd decᴾ)) hpb

                  -- THE SECOND ACTIVITY BULLET, and the only place it is spent.
                  -- The condition p lies below b and its image is in U, so b is
                  -- in U. At Uof G this is ⊆ˢ-transitivity and nothing else.

                  hUb : ⟨ U (b , hb) ⟩
                  hUb = U-from-below (b , hb) (p , hp) hpb₀ hUi

                  -- The value equality is the induction hypothesis at x', which
                  -- is a child of n because it carries an entry of n.

                  val : ⟨ y ≈[U] x' ⟩
                  val = subst (λ t → ⟨ t ≈[U] x' ⟩)
                              (sym (fst decᴮ ∙ cong trᴮ (fst decᴾ)))
                              (IH x' (child-entry x' b n hen'))

          -- SECOND CLAUSE. Every active entry of n is matched by an active
          -- entry of trᴮ (trᴾ n). Here U-to-below supplies the condition below
          -- the active Boolean weight, and the two entry laws are used in the
          -- introduction direction to place the relabelled entry.

          back : (z : S) → ⟨ ‖Active‖ z n ⟩
               → ⟨ ⋁ S (λ y → ‖Active‖ y (trᴮ (trᴾ n)) ⊓ (y ≈[U] z)) ⟩
          back z hz = active-out z n goal hz fromEntry
            where
            goal : Ω
            goal = ⋁ S (λ y → ‖Active‖ y (trᴮ (trᴾ n)) ⊓ (y ≈[U] z))

            fromEntry : (b : S) (hb : ⟨ b ∈ˢ B ⟩)
                      → ⟨ entry z b ∈ˢ n ⟩ → ⟨ U (b , hb) ⟩ → ⟨ goal ⟩
            fromEntry b hb he hu =
              PT.rec (snd goal) (λ { (q , hqb , hUq) → build q hqb hUq })
                    (U-to-below (b , hb) hu)
              where

              -- THE FIRST ACTIVITY BULLET, and the only place it is spent. The
              -- active Boolean weight b has a condition q below it whose image
              -- is itself active. At Uof G the witness is a member of G and the
              -- second half is generic-forward.

              build : (q : Cond) → ⟨ fst q ∈ˢ below (b , hb) ⟩
                    → ⟨ U (iPt q) ⟩ → ⟨ goal ⟩
              build q hqb hUq =
                ∣ trᴮ (trᴾ z)
                , active-in (trᴮ (trᴾ z)) (trᴮ (trᴾ n)) (iCode q) (i∈B q)
                            inForward hUq
                , IH z (child-entry z b n he)
                ∣₁
                where
                -- The reverse law places the entry of the translated subname
                -- at the condition q, and the forward law relabels it by the
                -- image of q. Both are used backwards, so both ≈ˢ obligations
                -- are reflexivity; the second one is reflexivity only because
                -- Σ-eta identifies (fst q , snd q) with q.

                inReverse : ⟨ entry (trᴾ z) (fst q) ∈ˢ trᴾ n ⟩
                inReverse =
                  subst ⟨_⟩ (sym (trᴾ-entries n (entry (trᴾ z) (fst q))))
                    ∣ z , ∣ b , ∣ hb , ∣ fst q , he , hqb
                                      , ≈ˢ-refl (entry (trᴾ z) (fst q))
                                      ∣₁ ∣₁ ∣₁ ∣₁

                inForward : ⟨ entry (trᴮ (trᴾ z)) (iCode q) ∈ˢ trᴮ (trᴾ n) ⟩
                inForward =
                  subst ⟨_⟩
                    (sym (trᴮ-entries (trᴾ n) (entry (trᴮ (trᴾ z)) (iCode q))))
                    ∣ trᴾ z , ∣ fst q , ∣ snd q , inReverse
                                        , ≈ˢ-refl (entry (trᴮ (trᴾ z)) (iCode q))
                                        ∣₁ ∣₁ ∣₁

--------------------------------------------------------------------------------
-- The architecture's signature, and surjectivity
--------------------------------------------------------------------------------

      -- The name predicates enter here and only here. Two facts are recorded
      -- by this arrangement rather than asserted in prose.
      --
      -- First, the VALUE statement needs no name hypothesis. ext-onto below
      -- carries the architecture's ⟨ IsNameᴮ n ⟩ (part 1.9) and discards it;
      -- the proof is ext-onto-raw at n. This is the same shape of measured
      -- over-declaration REPORT-B recorded for ⊩-∃→'s unused ub (§5.5) and
      -- TranslateForward recorded for its own grant of i-mono and i-pos
      -- (:314-322).
      --
      -- Second, SURJECTIVITY is where the hypothesis is genuinely spent, and
      -- it is spent on trᴾ-name and not on the value equality: to exhibit a
      -- POSET NAME whose translate has the value of n one must know that
      -- trᴾ n is a poset name, which is TranslateReverse.agda:761-762 and
      -- needs ⟨ IsNameᴮ n ⟩.

      module Named
        (IsNameᴾ IsNameᴮ : S → Ω)
        (trᴾ-name : (n : S) → ⟨ IsNameᴮ n ⟩ → ⟨ IsNameᴾ (trᴾ n) ⟩)
                                                      -- TranslateReverse:761-762
        where

        ext-onto : (n : S) → ⟨ IsNameᴮ n ⟩ → ⟨ trᴮ (trᴾ n) ≈[U] n ⟩
        ext-onto n _ = ext-onto-raw n

        -- The extension map is ext-map τ = trᴮ (fst τ) (architecture part
        -- 1.9). This says it is onto the Boolean names up to value at U, with
        -- the preimage exhibited rather than truncated: no truncation is
        -- eliminated into data anywhere, because none is formed. The Σ is a
        -- construction and not a choice.

        ext-surjective :
            (n : S) → ⟨ IsNameᴮ n ⟩
          → Σ[ τ ∈ (Σ[ m ∈ S ] ⟨ IsNameᴾ m ⟩) ] ⟨ trᴮ (fst τ) ≈[U] n ⟩
        ext-surjective n hn = (trᴾ n , trᴾ-name n hn) , ext-onto-raw n

--------------------------------------------------------------------------------
-- The obstructions this track inherits and does not discharge
--------------------------------------------------------------------------------

-- O1. THE ATOMIC GRAPH HAS NO DISCHARGE AT ANY GROUND. K4/AtomicGraph.agda:411
-- declares the record and :719-720 is the single route to it, with TableSupply
-- at :616-617 uninhabited. Nothing in this file touches a compiled value, so
-- the obstruction does not enter its statements; it enters the instance that
-- would supply Track E's val, and it is named here so that a reader who
-- composes this theorem with the truth lemma knows where the composite stands.
--
-- O2. THE CODED AND HOST SEMANTIC AGREEMENT IS CONDITIONAL AND ITS TWO
-- HYPOTHESES ARE UNPROVED UPSTREAM. ReadsSup and ReadsInf at
-- K4/HostSemantics.agda:895-900 have no supplier
-- (grep -c "reads-sup\|reads-inf" CodedCompletion.agda = 0). This file touches
-- NO host value at all, and it does not quote the refuted ledger sentence at
-- K4/HostSemantics.agda:1205-1213 (architecture part 6.5).
--
-- O3. THE REVERSE TRANSLATION IS CONDITIONAL ON K3'S TIER-4 DATUM. trᴾ lives
-- inside TranslateReverse.Names.Ground.Over, whose Ground telescope carries
-- image and image-spec, K3's MemberImage (TranslateReverse.agda:389-396), and
-- K3 measured tier 4 not dischargeable at L. That conditionality is visible in
-- the TYPE of this module: trᴾ and trᴾ-entries are parameters, so a consumer
-- who cannot supply them cannot apply this module. Architecture part 5.3 lists
-- ext-onto under exactly this obstruction, and part 6.3 is the correction that
-- tier 4 is the ONLY thing it is conditional on: not recover, not order
-- reflection, not density of the image, not LEM.
--
-- O6. THERE IS NO CODED ORDER GRAPH OF B. isGeneric (CodedCompletion.agda
-- :1070-1074) lives inside module Core over a Presentation (:201-208) and B
-- has none, so "Uof G is generic" cannot be written down. This file writes it
-- in no form, not even as a hypothesis: U is a bare predicate with two
-- entailments. Unbuilt interface, not unproved theorem.
--
-- AND ONE THAT IS NOT AN OBSTRUCTION BUT A NON-CLAIM. This file asserts
-- nothing about an arbitrary ultrafilter. Architecture part 6.3 is explicit
-- that the coincidence of the two activity classes is a fact about Uof G and
-- is NOT free at an arbitrary ultrafilter, where recover or its equivalent
-- would be needed; that is K13's problem. The two entailments U-to-below and
-- U-from-below are where any such generalization would have to be paid, and
-- they are in the telescope where they are visible.

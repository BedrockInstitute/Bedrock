{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track D: the corresponding subset of the algebra.
--
-- What this module is for. Track A embedded an abstract coded poset into an
-- abstract Boolean algebra. Given a subset G of the conditions, this file
-- builds the subset Uof G of the algebra that G determines, proves the four
-- laws that make it a filter, and proves the two directions of the
-- correspondence between G and Uof G. It is the file the valuation agreement
-- of Track E and the truth lemma of Track G both consume, and the only thing
-- either of them asks of the Boolean side.
--
-- WHAT THIS FILE DOES NOT CLAIM, and this is the limit the architecture found
-- rather than a gap this track left open. K2's genericity predicate isGeneric
-- (CodedCompletion.agda:1070-1074) is declared INSIDE module Core, which is
-- parameterized by a Presentation (:201-208) carrying a coded order graph.
-- The Boolean algebra has no such presentation: K2 did not deliver the coded
-- order graph of the nonzero part, and building one needs the double power
-- set, a Separation against instantiated prAtˢ and subsetAtˢ, Pairing for the
-- reflexivity and transitivity witnesses, and internal Kuratowski
-- injectivity, of which only the last now exists (entry-inj at
-- NameKernel.agda:321, kpair-unique at NameSpace.agda:388). So the sentence
-- "Uof G is generic" CANNOT BE WRITTEN DOWN in this programme today, and this
-- file does not write it down in any disguise.
--
-- THIS IS AN UNBUILT INTERFACE AND NOT AN UNPROVED THEOREM. The missing thing
-- is a type, not a proof of an existing type. What is delivered instead is a
-- subset of the algebra that (1) is a proper, upward closed, directed,
-- inhabited filter with no hypothesis beyond a filter downstairs, (2)
-- REFLECTS G, so that a condition lies in G exactly when its image lies in
-- Uof G, and (3) is an ULTRAFILTER, deciding every element of the algebra,
-- under LEM ℓ and the genericity of G. Items (2) and (3) are everything the
-- valuation agreement and the truth lemma consume.
--
-- Ledger. The hypotheses of the Image layer are the structure, ordinary
-- Extensionality, the path realization, the carrier code B, a Lattice, a
-- Complement, a CodedComplete and a ForcingBase. Extensionality and the path
-- realization are consumed only through K4.Implication's ≤ᴮ-antisym, which
-- this file reaches only through ≤→⊓ inside generic-reflect-from. No
-- Separation, no PowerSet, no Collection, no Choice of any kind. LEM ℓ is an
-- explicit first argument of exactly generic-reflect, Uof-ultra and
-- generic-bridge, and in all three it is spent by being handed to Track C's
-- density lemma and nowhere else.
--
-- Record ownership (rule 9, ledger clause L12). This file declares NO record.
-- ForcingNotion is K2's (ForcingNotion.agda:63), isFilter is K2's (:175),
-- ForcingBase is Track A's. frameNotion below is an INHABITANT of K2's
-- record, built exactly as K2's own decode builds one
-- (CodedCompletion.agda:239-249), not a second copy of it.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import Base.Classical using ( LEM )
import OrdinaryProfile
import CodedVocabulary
import ForcingNotion as FN
import K4.Algebra
import K4.Implication
import K5.Frame

module K5.Generic {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

-- The scope contract of K4/Implication.agda:64-76, copied from Track A: the
-- three record TYPE names come from K4.Algebra and never from a module that
-- re-exports them, so opening K4.Algebra and K4.Implication together is not
-- an ambiguous module name.

open K4.Algebra 𝒮
  using ( Pt; _≤ᴮ_; ≤ᴮ-refl; ⊆ˢ-trans
        ; Lattice; Complement; CodedComplete )

open CodedVocabulary 𝒮 using ( denseΔ )

--------------------------------------------------------------------------------
-- The poset layer
--------------------------------------------------------------------------------

-- carrier and order are Track A's two codes, passed straight through. Nothing
-- at this level needs the algebra.

module Poset (carrier order : S) where

  open K5.Frame.Poset 𝒮 carrier order

--------------------------------------------------------------------------------
-- The decoded notion, and the subset of the algebra a subset of it determines
--------------------------------------------------------------------------------

  module Image
    (ext   : OrdinaryProfile.Extensionality 𝒮)
    (paths : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
    (B : S) (L : Lattice B) (Cm : Complement B L) (Kc : CodedComplete B L)
    (fb : ForcingBase B L Cm)
    where

    open ForcingBase fb
    open K5.Frame.Poset.Forcing 𝒮 carrier order ext paths B L Cm Kc fb
    open K4.Implication 𝒮 ext paths B L Cm using ( _⊓ᴮ_ ; ⊥ᴮ ; ¬ᴮ_ ; ≤→⊓ )

    -- K2's decode (CodedCompletion.agda:239-249) at a ForcingBase instead of
    -- at a Presentation. The three laws it asks for are exactly the three
    -- poset fields of the record, which is why Track A put them there: a
    -- presentation's order-typed clause says the graph consists of Kuratowski
    -- pairs and is never consumed by a structural theorem, so a ForcingBase
    -- is already enough to decode.

    frameNotion : FN.ForcingNotion {ℓ}
    frameNotion = record
      { Cond     = Cond
      ; isSetC   = isSetΣSndProp isSetS (λ x → snd (x ∈ˢ carrier))
      ; _≼_      = λ p q → fst p ≼ᶜ fst q
      ; ≼-refl   = λ p → ≼-refl (fst p) (snd p)
      ; ≼-trans  = λ {p} {q} {r} h k →
                     ≼-trans (fst p) (fst q) (fst r) (snd p) (snd q) (snd r) h k
      ; nonempty = PT.map (λ { (p , hp) → p , hp }) inhabited }

    -- The structural vocabulary is K2's and is never re-declared. Only the
    -- four names this file actually speaks are opened; Cond, _≼_, ≼-refl and
    -- ≼-trans are deliberately left qualified, because the unqualified
    -- versions in scope are Track A's and the two must not be confused even
    -- though they are definitionally identical.

    module FS = FN.Structure frameNotion
    open FS using ( Sub ; _∈ᴾ_ ; positive )

    -- The subset of the algebra determined by a subset of the conditions: b
    -- belongs to Uof G when some member of G forces b. Bell writes the same
    -- set at Problem 4.34; here it is one join over the conditions and
    -- nothing else.
    --
    -- No seal. Rule 2 is about description-operator terms and rule 2b about
    -- nesting two operations of an unsealed coded algebra in a type; Uof's
    -- body contains neither, and Track E must eliminate the join at every
    -- node of its induction, so sealing it would buy nothing and cost a
    -- transport at every use.

    Uof : Sub → Pt B → Ω
    Uof G b = ⋁ Cond (λ p → (p ∈ᴾ G) ⊓ (p ⊩ᴮ b))

--------------------------------------------------------------------------------
-- The filter laws, all free
--------------------------------------------------------------------------------

    -- G is a module parameter rather than an argument so that every statement
    -- below stays at Type ℓ. Sub is Cond → Ω and therefore lives one level up
    -- (ForcingNotion.agda:88-89), and a theorem quantifying over it would be
    -- large; that level is the type-level tell ledger clause L13 asks to
    -- watch, and it is the same tell that makes hostGeneric refutable
    -- (ForcingNotion.agda:300-302, refuted at :315-317).

    module Laws (G : Sub) where

      -- Forward: a condition in G puts its own image in Uof G, witnessed by
      -- the condition itself. This half needs nothing at all.

      generic-forward : (p : Cond) → ⟨ p ∈ᴾ G ⟩ → ⟨ Uof G (i p) ⟩
      generic-forward p hp = ∣ p , hp , ⊩ᴮ-intro p (i p) (≤ᴮ-refl (i p)) ∣₁

      -- Inhabitedness. Stated at positivity and not at the filter record:
      -- inhabited is the only field it consumes, and the architecture's own
      -- ground-copy clause is stated the same way (part 1.8, trap T-F2).

      Uof-inhabited : ⟨ positive G ⟩ → ⟨ ⋁ (Pt B) (Uof G) ⟩
      Uof-inhabited = PT.map (λ { (p , hp) → i p , generic-forward p hp })

      -- Upward closure is transitivity of inclusion under the seal, and it
      -- needs no filter law downstairs at all.

      Uof-up : (b c : Pt B) → ⟨ b ≤ᴮ c ⟩ → ⟨ Uof G b ⟩ → ⟨ Uof G c ⟩
      Uof-up b c h =
        PT.map (λ { (p , hp , hpb) →
                    p , hp , ⊩ᴮ-intro p c (⊆ˢ-trans (⊩ᴮ-elim p b hpb) h) })

      -- Directedness, and THE TRAP THE ARCHITECTURE NAMES FOR THIS TRACK.
      -- The common lower bound produced below is the IMAGE OF A CONDITION,
      -- namely i r for r the refinement that the filter downstairs supplies.
      -- It is never the meet b ⊓ᴮ c. Taking the meet would oblige this track
      -- to find a condition below it, which is density of the image at the
      -- meet and then an order relation read back off an inequality between
      -- images; that last step is order reflection, it is FALSE, and K2
      -- refutes it at InstancesCompletion.agda:131-134. Separativity would
      -- repair it and separativity is additional data and never a field
      -- (ForcingNotion.agda:276-278). So the witness is i r, and the whole
      -- proof is i-mono twice.

      Uof-dir : FS.isFilter G → (b c : Pt B) → ⟨ Uof G b ⟩ → ⟨ Uof G c ⟩
              → ⟨ ⋁ (Pt B) (λ d → (Uof G d) ⊓ ((d ≤ᴮ b) ⊓ (d ≤ᴮ c))) ⟩
      Uof-dir fil b c hb hc = PT.rec (snd goal) fromB hb
        where
          goal : Ω
          goal = ⋁ (Pt B) (λ d → (Uof G d) ⊓ ((d ≤ᴮ b) ⊓ (d ≤ᴮ c)))

          fromB : Σ[ p ∈ Cond ] (⟨ p ∈ᴾ G ⟩ × ⟨ p ⊩ᴮ b ⟩) → ⟨ goal ⟩
          fromB (p , hpG , hpb) = PT.rec (snd goal) fromC hc
            where
              fromC : Σ[ q ∈ Cond ] (⟨ q ∈ᴾ G ⟩ × ⟨ q ⊩ᴮ c ⟩) → ⟨ goal ⟩
              fromC (q , hqG , hqc) =
                PT.map atCommon (FS.isFilter.directed fil p q hpG hqG)
                where
                  atCommon : Σ[ r ∈ Cond ] (⟨ r ∈ᴾ G ⟩ ×
                               (⟨ fst r ≼ᶜ fst p ⟩ × ⟨ fst r ≼ᶜ fst q ⟩))
                           → Σ[ d ∈ Pt B ] ⟨ (Uof G d) ⊓ ((d ≤ᴮ b) ⊓ (d ≤ᴮ c)) ⟩
                  atCommon (r , hrG , hrp , hrq) =
                    i r
                    , ( generic-forward r hrG
                      , ( ⊆ˢ-trans (i-mono p r hrp) (⊩ᴮ-elim p b hpb)
                        , ⊆ˢ-trans (i-mono q r hrq) (⊩ᴮ-elim q c hqc) ) )

      -- Properness. The bottom of the algebra is never in Uof G, because no
      -- condition forces it. Like ⊩ᴮ-⊥ this is FALSE at a degenerate algebra
      -- and the field that excludes the degenerate algebra is i-nonzero,
      -- inside ⊩ᴮ-⊥; no filter law downstairs is consumed.

      Uof-proper : ⟨ Uof G ⊥ᴮ ⟩ → ⟨ ⊥ ⟩
      Uof-proper = PT.rec (snd ⊥) (λ { (p , _ , h) → ⊩ᴮ-⊥ p h })

--------------------------------------------------------------------------------
-- The two paid clauses, with the paid input isolated
--------------------------------------------------------------------------------

      -- Reflection is the direction the roadmap's binding constraint is
      -- about, and its whole content is this lemma, which is FREE. The only
      -- thing it asks of genericity is the dichotomy in its third argument:
      -- SOME member of G either refines p or is incompatible with p.
      --
      -- The argument. In the first case p is in G by upward closure and
      -- nothing else happens. In the second case the member s is incompatible
      -- with p, and the contradiction is assembled as follows. Uof G (i p)
      -- hands over a q in G whose image refines i p. Directedness of G hands
      -- over an r in G refining both s and q. Monotonicity carries i r under
      -- i q and so under i p, which makes i r ⊓ᴮ i p equal to i r, which is
      -- nonzero, so i-compat← returns compatibility of r with p. Finally r
      -- refines s, so a common refinement of r and p is a common refinement
      -- of s and p, and s was incompatible with p.
      --
      -- NOTE WHAT IS ABSENT. No maximal antichain, no maximum principle, no
      -- separativity, and no injectivity of i. The one step that could have
      -- reached for order reflection, namely turning i r ≤ᴮ i p back into an
      -- order relation, is not taken: the conclusion drawn from i r ≤ᴮ i p is
      -- COMPATIBILITY, through i-compat←, and compatibility is all the
      -- contradiction needs.

      generic-reflect-from :
          FS.isFilter G
        → (p : Cond)
        → ⟨ ⋁ Cond (λ s → (s ∈ᴾ G) ⊓ ((fst s ≼ᶜ fst p) ⊔ (compatᶜ s p ⇒ ⊥))) ⟩
        → ⟨ Uof G (i p) ⟩
        → ⟨ p ∈ᴾ G ⟩
      generic-reflect-from fil p met hu = PT.rec (snd (p ∈ᴾ G)) atMember met
        where
          compat-of : (s : Cond) → ⟨ s ∈ᴾ G ⟩ → ⟨ compatᶜ s p ⟩
          compat-of s hsG = PT.rec (snd (compatᶜ s p)) fromU hu
            where
              fromU : Σ[ q ∈ Cond ] (⟨ q ∈ᴾ G ⟩ × ⟨ q ⊩ᴮ i p ⟩)
                    → ⟨ compatᶜ s p ⟩
              fromU (q , hqG , hq) =
                PT.rec (snd (compatᶜ s p)) fromR
                       (FS.isFilter.directed fil s q hsG hqG)
                where
                  fromR : Σ[ r ∈ Cond ] (⟨ r ∈ᴾ G ⟩ ×
                            (⟨ fst r ≼ᶜ fst s ⟩ × ⟨ fst r ≼ᶜ fst q ⟩))
                        → ⟨ compatᶜ s p ⟩
                  fromR (r , _ , hrs , hrq) = PT.map bump (i-compat← r p nz)
                    where
                      hrp : ⟨ i r ≤ᴮ i p ⟩
                      hrp = ⊆ˢ-trans (i-mono q r hrq) (⊩ᴮ-elim q (i p) hq)

                      nz : ((i r ⊓ᴮ i p) ≡ ⊥ᴮ) → ⟨ ⊥ ⟩
                      nz e = i-nonzero r (sym (≤→⊓ (i r) (i p) hrp) ∙ e)

                      bump : Σ[ z ∈ S ] (⟨ z ∈ˢ carrier ⟩ ×
                               (⟨ z ≼ᶜ fst r ⟩ × ⟨ z ≼ᶜ fst p ⟩))
                           → Σ[ z ∈ S ] (⟨ z ∈ˢ carrier ⟩ ×
                               (⟨ z ≼ᶜ fst s ⟩ × ⟨ z ≼ᶜ fst p ⟩))
                      bump (z , hzc , hzr , hzp) =
                        z , hzc
                          , ≼-trans z (fst r) (fst s) hzc (snd r) (snd s) hzr hrs
                          , hzp

          branch : (s : Cond) → ⟨ s ∈ᴾ G ⟩
                 → (⟨ fst s ≼ᶜ fst p ⟩ ⊎ ⟨ compatᶜ s p ⇒ ⊥ ⟩)
                 → ⟨ p ∈ᴾ G ⟩
          branch s hsG (inl hsp) = FS.isFilter.upward fil s p hsG hsp
          branch s hsG (inr apart) = Empty.rec* (apart (compat-of s hsG))

          atMember : Σ[ s ∈ Cond ] (⟨ s ∈ᴾ G ⟩ ×
                       ⟨ (fst s ≼ᶜ fst p) ⊔ (compatᶜ s p ⇒ ⊥) ⟩)
                   → ⟨ p ∈ᴾ G ⟩
          atMember (s , hsG , alt) = PT.rec (snd (p ∈ᴾ G)) (branch s hsG) alt

      -- The ultrafilter clause, with its paid input isolated in the same way.
      -- Given a member of G that decides b one way or the other, Uof G
      -- decides b. FREE, and it consumes no filter law whatever: the witness
      -- for whichever side holds is the deciding condition itself.

      Uof-ultra-from :
          (b : Pt B)
        → ⟨ ⋁ Cond (λ q → (q ∈ᴾ G) ⊓ ((q ⊩ᴮ b) ⊔ (q ⊩ᴮ (¬ᴮ b)))) ⟩
        → ⟨ (Uof G b) ⊔ (Uof G (¬ᴮ b)) ⟩
      Uof-ultra-from b = PT.rec (snd ((Uof G b) ⊔ (Uof G (¬ᴮ b)))) step
        where
          step : Σ[ q ∈ Cond ] (⟨ q ∈ᴾ G ⟩ × ⟨ (q ⊩ᴮ b) ⊔ (q ⊩ᴮ (¬ᴮ b)) ⟩)
               → ⟨ (Uof G b) ⊔ (Uof G (¬ᴮ b)) ⟩
          step (q , hqG , alt) = PT.map pick alt
            where
              pick : (⟨ q ⊩ᴮ b ⟩ ⊎ ⟨ q ⊩ᴮ (¬ᴮ b) ⟩)
                   → (⟨ Uof G b ⟩ ⊎ ⟨ Uof G (¬ᴮ b) ⟩)
              pick (inl h) = inl ∣ q , hqG , h ∣₁
              pick (inr h) = inr ∣ q , hqG , h ∣₁

--------------------------------------------------------------------------------
-- Meeting the coded dense sets of Track C
--------------------------------------------------------------------------------

    -- Track C's three coded sets arrive as explicit module parameters, typed
    -- from the architecture's part 1.6 rather than from a compiled export,
    -- because Track C is written in parallel with this file. That is ledger
    -- clause L10 in its intended use: a drift between Track C's spelling and
    -- the two compositions below fails in a probe instead of passing
    -- silently. Nothing in this file inspects the Separation that builds
    -- them, and nothing here names separateOf, iSet, starOf or coneΔ.
    --
    -- The genericity input is K2's meets field taken FLAT and verbatim from
    -- CodedCompletion.agda:1073-1074, with the two Core-local abbreviations
    -- expanded in place: subsetOf d is d ⊆ˢ carrier (:995-996) and denseᴵ is
    -- denseΔ carrier order (:1001-1002). isGeneric is NOT re-declared here
    -- and no weakening of it to antichains, maximal antichains or predense
    -- sets is offered (ledger clause L4: at an empty coded d, antichainᴵ d is
    -- vacuously true while denseᴵ d is false, so an antichain-routed clause
    -- would be satisfied by nothing).

    module Meeting
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
      (G : Sub)
      where

      open Laws G public

      -- A condition lies in G as soon as its image lies in Uof G. One coded
      -- dense set is met and it is coneOrApart p; the rest is
      -- generic-reflect-from. LEM ℓ is spent by handing it to Track C's
      -- density lemma and in no other place.

      generic-reflect :
          LEM ℓ
        → ((d : S) → ⟨ d ⊆ˢ carrier ⟩ → ⟨ denseΔ carrier order d ⟩
                   → ⟨ ⋁ Cond (λ q → (q ∈ᴾ G) ⊓ (fst q ∈ˢ d)) ⟩)
        → FS.isFilter G
        → (p : Cond) → ⟨ Uof G (i p) ⟩ → ⟨ p ∈ᴾ G ⟩
      generic-reflect lem meets fil p =
        generic-reflect-from fil p
          (PT.map (λ { (s , hsG , hsd) → s , hsG , coneOrApart-spec p s hsd })
                  (meets (coneOrApart p) (coneOrApart-sub p)
                         (coneOrApart-dense lem p)))

      -- Uof G decides every element of the algebra. One coded dense set is
      -- met and it is decideAt b. No filter law downstairs is consumed;
      -- together with Uof-proper, Uof-up, Uof-dir and Uof-inhabited this is
      -- what the word ULTRAFILTER means here, and it is the strongest thing
      -- about Uof G that the present vocabulary can express.

      Uof-ultra :
          LEM ℓ
        → ((d : S) → ⟨ d ⊆ˢ carrier ⟩ → ⟨ denseΔ carrier order d ⟩
                   → ⟨ ⋁ Cond (λ q → (q ∈ᴾ G) ⊓ (fst q ∈ˢ d)) ⟩)
        → (b : Pt B) → ⟨ (Uof G b) ⊔ (Uof G (¬ᴮ b)) ⟩
      Uof-ultra lem meets b =
        Uof-ultra-from b
          (PT.map (λ { (q , hqG , hqd) → q , hqG , decideAt-spec b q hqd })
                  (meets (decideAt b) (decideAt-sub b) (decideAt-dense lem b)))

      -- The two directions packaged as the single bridge the valuation
      -- agreement reduces to at every node of its induction (architecture
      -- part 1.8). It is a path in Ω, which is legitimate for a THEOREM; what
      -- ledger clause L13 forbids is a path in Ω as a record FIELD, since
      -- that is what would push a record to Type (ℓ-suc ℓ) and stop it
      -- indexing a join. No record here carries it.
      --
      -- Track E may NOT prove its induction by monotonicity in G, which K3
      -- records as failing in both directions (Valuation.agda:700-705), and
      -- may NOT get this bridge entry by entry from injectivity of i, of
      -- which there is none and never will be (TranslateForward.agda:33-36).
      -- This path is the whole of what Track E gets from Track D.

      generic-bridge :
          LEM ℓ
        → ((d : S) → ⟨ d ⊆ˢ carrier ⟩ → ⟨ denseΔ carrier order d ⟩
                   → ⟨ ⋁ Cond (λ q → (q ∈ᴾ G) ⊓ (fst q ∈ˢ d)) ⟩)
        → FS.isFilter G
        → (p : Cond) → (p ∈ᴾ G) ≡ Uof G (i p)
      generic-bridge lem meets fil p =
        ⇔toPath (generic-forward p) (generic-reflect lem meets fil p)

--------------------------------------------------------------------------------
-- The non-claims this track is required to state beside its signatures
--------------------------------------------------------------------------------

-- O6, AND IT IS THIS TRACK'S OWN LIMIT. There is no coded order graph of B,
-- so isGeneric (CodedCompletion.agda:1070-1074) cannot be applied to a subset
-- of the algebra at all: the predicate lives inside module Core, which is
-- parameterized by a Presentation (:201-208), and B has none. `Uof G is
-- generic` is therefore an UNBUILT INTERFACE, not an unproved theorem, and
-- this file states it in no form, not even as a hypothesis. What is proved is
-- exactly the list at the head of this file. The interface is sized in
-- k2/REPORT-G.md:222-239 as a self-contained brief, and it is K8's.
--
-- THE PULLBACK IS NOT THIS TRACK'S AND IS NOT PROVED HERE. G-of U, the map
-- back from a subset of the algebra to a subset of the conditions, has no
-- clause in this file. The obstruction is precise and it is not shyness:
-- directedness of a filter demands a common refinement INSIDE the filter
-- (ForcingNotion.agda:175-180), while the preimage of an ultrafilter yields
-- only separate compatibility of the two conditions, and closing that gap
-- needs separativity, which is additional data and never a field (:276-278).
-- The owner is K6 or K11, under an explicit separative hypothesis. Note that
-- this is a different fact from Uof-dir above, which IS free; the
-- pushforward and the pullback must not be conflated, and the plan lens
-- conflated them.
--
-- ORDER REFLECTION. ⟨ i p ≤ᴮ i q ⟩ → ⟨ fst p ≼ᶜ fst q ⟩ is FALSE and K2
-- refutes it at InstancesCompletion.agda:131-134. It is not assumed, derived
-- or used anywhere above; every step that has an inequality between images
-- and wants a poset fact goes through i-compat← and a common refinement.
--
-- INJECTIVITY OF i is likewise absent. TranslateForward.agda:33-36 records
-- that there is none and that there never will be one.
--
-- O1. The atomic graph has no discharge at any ground (K4/AtomicGraph.agda:411,
-- :719-720, :616-617). Nothing here depends on it and no statement here may be
-- read as discharging it.
--
-- O2. The coded and the host semantic agreement is conditional by design, its
-- two hypotheses ReadsSup and ReadsInf (K4/HostSemantics.agda:895-900) are
-- unproved upstream, and the sentence at K4/HostSemantics.agda:1205-1213 is
-- refuted and is not quoted here. This file touches no host value.

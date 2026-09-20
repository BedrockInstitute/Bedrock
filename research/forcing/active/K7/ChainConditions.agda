{-# OPTIONS --cubical --safe --guardedness #-}

-- K7 Track A. THE THREE COUNTABLE CHAIN CONDITIONS.
--
-- The roadmap's words are the specification: "Define the three countable
-- chain conditions separately and prove their equivalence under internal
-- ZFC." This file owns the three definitions and the two FREE arrows
-- between them. Track C owns the equivalence, which needs MaximalExtension
-- and is the package's one open item; the two reduction TYPES are declared
-- at the end of this file so that neither Track C nor anyone else can
-- smuggle a paid arrow in as a free one.
--
-- WHAT THE PROGRAMME DID NOT HAVE, AND THIS FILE BUILDS.
--
-- CodedVocabulary.agda ships a Formula S n, a Δ₀ certificate and a refl
-- reading for fourteen notions, predensity among them (:411-427), and says
-- at :407-409 that predensity "is the form K7's chain condition is stated
-- through". It ships no antichain. Measured over the whole compile root
-- before this file existed: `antichainAt`, `antichainΔ` and `CCC` returned
-- zero lines outside K7/. So ground Separation, which reads a Formula S 1,
-- could not cut an antichain, and no antichain-stated chain condition was
-- provable by internal ZFC for want of the formula. antichainAtˢ below is
-- that formula.
--
-- CODES, NOT HOST SUBSETS, AND THE TYPE CARRIES THE CHOICE.
--
-- ForcingNotion.Structure.antichain (ForcingNotion.agda:153-155) takes a
-- Sub = Cond → Ω, which is Type (ℓ-suc ℓ) (:88-89). A chain condition over
-- Sub quantifies over HOST subsets of conditions and is a strictly stronger
-- statement than one over the model's own codes: it constrains subsets the
-- model cannot see, and it is not a theorem of M at all. Every quantifier
-- below ranges over d : S, a ground SET. The type enforces it and no grep
-- is needed: ⋀ and ⋁ are indexed by a Type ℓ (Base/Truth.lagda.md:72) and
-- Sub does not fit, so a host-quantified draft does not typecheck. The
-- control is on disk as K7/breaks/CCCOverHostSub.agda-break.
--
-- WHICH COUNTABILITY, AND WHY IT IS THE ONLY ONE ON THE LEDGER'S RIGHT SIDE.
--
-- "Countable" has two forms without choice, an injection into ω and a
-- surjection from ω, and they are not interchangeable: inverting a
-- surjection to get an injection is choice. K1 built only the first.
-- injectable (CardinalBridge.agda:382-383) is a TRUNCATED join over the
-- graph f, so it hands back no selector and no host function. Every
-- condition below is the INJECTION form, uniformly, and countableΔ names
-- it once, because an equivalence proof that changed form halfway would be
-- unsound. Track B landed the surjection form in parallel with this file
-- (K7/CardinalOrder.agda:187, :228); nothing below mentions it.
--
-- WHERE paths IS SPENT. Two places, both named. antichainΔ-is-antichainᴵ
-- takes it as an EXPLICIT argument, which is architecture Q5's design: the
-- realization contract sits in one type instead of in every theorem. And
-- member-cong below spends it once, from the module parameter, because
-- ccc₃→ccc₁ must carry membership along the ≈ˢ that an antichain concludes,
-- and a bare ZFStructure gives ≈ˢ no congruence for ∈ˢ. That second spend
-- is a correction to the architecture's "the ONE named lemma"; it is
-- reported rather than hidden.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K7.ChainConditions
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _≐_; _⇒̇_; ∀̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; checkΔ₀ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
open import Cubical.Data.Unit using ( tt )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT

import CodedVocabulary
import CardinalBridge

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module OP = OrdinaryProfile 𝒮
module CV = CodedVocabulary 𝒮
module CB = CardinalBridge 𝒮

open OP.PathRealization paths using ( subst-member )
open CV using ( compatAtˢ; compatibleΔ; subsetΔ; predenseΔ; predenseΔ-mono )
open CB using ( injectable )
open At S id using ( _⊨_ )

--------------------------------------------------------------------------------
-- PART 1. THE ANTICHAIN, AS AN OBJECT-LANGUAGE FORMULA
--------------------------------------------------------------------------------

-- A subset d of the carrier c is an antichain when any two of its members
-- that are compatible are equal. Written with both quantifiers bounded by
-- the CARRIER and the two memberships in d as antecedents, rather than
-- bounded by d, for one reason that is not presentation: the consumer of
-- this predicate is a transfer argument that has a carrier membership in
-- hand at every use site and must supply one at every introduction site
-- (K7/CompletionTransfer.agda:266-273). Bounding by c and guarding by d
-- makes the reader Δ₀ exactly as bounding by d would, and makes the two
-- directions below literal curryings.
--
-- The shape is predenseAtˢ's (CodedVocabulary.agda:411-415) with the inner
-- ∃̇∈ replaced by a second ∀̇∈ and the body turned into an implication into
-- ≐. Read the indices at the innermost point: var zero is q, var (suc zero)
-- is p, and everything of the ambient environment has moved out by two.

antichainAtˢ : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
antichainAtˢ c o d =
  ∀̇∈ (var c)
     ((var zero ∈̇ var (suc d))
       ⇒̇ (∀̇∈ (var (suc c))
             ((var zero ∈̇ var (suc (suc d)))
               ⇒̇ (compatAtˢ (suc (suc c)) (suc (suc o)) (suc zero) zero
                   ⇒̇ (var (suc zero) ≐ var zero)))))

-- The host predicate, written as the literal unfolding of the formula so
-- that the reading is refl. Every quantifier is ⋀ S: a ground set, never a
-- host predicate on conditions, never a Sub.

antichainΔ : S → S → S → Ω
antichainΔ c o d =
  ⋀ S (λ p → (p ∈ˢ c) ⇒ ((p ∈ˢ d) ⇒
    ⋀ S (λ q → (q ∈ˢ c) ⇒ ((q ∈ˢ d) ⇒
      (compatibleΔ c o p q ⇒ (p ≈ˢ q))))))

Δ₀-antichainAtˢ : ∀ {n} (c o d : Fin n) → Δ₀ (antichainAtˢ c o d)
Δ₀-antichainAtˢ c o d = checkΔ₀ (antichainAtˢ c o d) tt

-- Rule 6 at its sharpest. antichainAtˢ sits at uniform depth: swapping two
-- de Bruijn indices at the innermost point leaves a well formed Formula S n
-- whose Δ₀ certificate still closes by checkΔ₀ … tt, and says something
-- about a different pair of sets. Only this theorem objects. The deliberate
-- break is K7/breaks/AntichainReadingSwap.agda-break and its log records
-- that the Δ₀ half passes while this half fails.

antichainAtˢ-reading : ∀ {n} (c o d : Fin n) (γ : S ^ n)
                     → (γ ⊨ antichainAtˢ c o d)
                       ≡ antichainΔ (lookup c γ) (lookup o γ) (lookup d γ)
antichainAtˢ-reading c o d γ = refl

--------------------------------------------------------------------------------
-- PART 2. THE TWO DIRECTIONS, WHICH ARE THE STABLE INTERFACE
--------------------------------------------------------------------------------

-- Track D consumes the antichain through this pair and never unfolds
-- antichainΔ (K7/CompletionTransfer.agda:266-273), so no later change to
-- the definition above can drift a consumer. Both are curryings: the bodies
-- are the identity on the ⋀ and ⇒ structure, in the consumer's own argument
-- order, and that is the measurement Track D reported as refl-cheap.

antichain-use : (c o d p q : S) → ⟨ antichainΔ c o d ⟩
              → ⟨ p ∈ˢ c ⟩ → ⟨ p ∈ˢ d ⟩ → ⟨ q ∈ˢ c ⟩ → ⟨ q ∈ˢ d ⟩
              → ⟨ compatibleΔ c o p q ⟩ → ⟨ p ≈ˢ q ⟩
antichain-use c o d p q h hpc hpd hqc hqd hcomp =
  h p hpc hpd q hqc hqd hcomp

antichain-intro : (c o d : S)
                → ((p q : S) → ⟨ p ∈ˢ c ⟩ → ⟨ p ∈ˢ d ⟩ → ⟨ q ∈ˢ c ⟩ → ⟨ q ∈ˢ d ⟩
                   → ⟨ compatibleΔ c o p q ⟩ → ⟨ p ≈ˢ q ⟩)
                → ⟨ antichainΔ c o d ⟩
antichain-intro c o d f p hpc hpd q hqc hqd hcomp =
  f p q hpc hpd hqc hqd hcomp

-- Monotonicity runs DOWNWARD, and the reversal against predenseΔ-mono
-- (CodedVocabulary.agda:429-431) is the mathematical content rather than a
-- naming accident: a subset of an antichain is an antichain, a superset of
-- a predense set is predense, and the two pull in opposite directions. That
-- opposition is exactly why maximality below is a conjunction and not a
-- maximum.

antichainΔ-mono : (c o d e : S) → ⟨ subsetΔ e d ⟩
                → ⟨ antichainΔ c o d ⟩ → ⟨ antichainΔ c o e ⟩
antichainΔ-mono c o d e sub h p hpc hpe q hqc hqe hcomp =
  h p hpc (sub p hpe) q hqc (sub q hqe) hcomp

--------------------------------------------------------------------------------
-- PART 3. THE ONE LEMMA THAT SPENDS THE REALIZATION CONTRACT
--------------------------------------------------------------------------------

-- K2's own antichain predicate, CodedCompletion.agda:1012-1017,
-- transcribed. It is not imported: CodedCompletion.Core may not be applied
-- outside a named seam probe, and antichainᴵ lives inside Core. The
-- transcription is checked against the real export by refl in
-- K7/ChainConditionsAtCoded.agda, which is stronger than a citation.
--
-- The difference from antichainΔ is exactly one thing: the conclusion is
-- the HOST path p ≡ q, packaged as a truth value by isSetS, where
-- antichainΔ concludes the structure equality p ≈ˢ q. In a bare
-- ZFStructure those are different truth values, and the price of
-- identifying them is the path realization contract. Putting that price in
-- the type of one lemma, as an explicit argument rather than by reading it
-- off the module parameter, is what keeps it visible: a theorem stated with
-- antichainΔ can later be read at a structure where ≈ˢ is not paths, and
-- this lemma cannot.

antichainᴴ : S → S → S → Ω
antichainᴴ c o d =
  ⋀ S (λ p → ⋀ S (λ q →
    (((p ∈ˢ c) ⊓ (p ∈ˢ d))
      ⊓ (((q ∈ˢ c) ⊓ (q ∈ˢ d)) ⊓ compatibleΔ c o p q))
    ⇒ ((p ≡ q) , isSetS p q)))

antichainΔ-is-antichainᴵ :
    ((x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
  → (c o d : S) → antichainΔ c o d ≡ antichainᴴ c o d
antichainΔ-is-antichainᴵ pa c o d = ⇔toPath to fro
  where
  to : ⟨ antichainΔ c o d ⟩ → ⟨ antichainᴴ c o d ⟩
  to h p q hyp =
    subst ⟨_⟩ (pa p q)
      (h p (hyp .fst .fst) (hyp .fst .snd)
         q (hyp .snd .fst .fst) (hyp .snd .fst .snd) (hyp .snd .snd))

  fro : ⟨ antichainᴴ c o d ⟩ → ⟨ antichainΔ c o d ⟩
  fro h p hpc hpd q hqc hqd hcomp =
    subst ⟨_⟩ (sym (pa p q)) (h p q ((hpc , hpd) , ((hqc , hqd) , hcomp)))

-- Membership travels along ≈ˢ only because of the same contract, and this
-- is the second and last place the module parameter paths is spent. It is
-- needed below: an antichain hands back a ≈ˢ and CCC₃'s countable predense
-- subset must absorb the maximal antichain as a SET inclusion.

member-cong : (x y z : S) → ⟨ x ≈ˢ y ⟩ → ⟨ x ∈ˢ z ⟩ → ⟨ y ∈ˢ z ⟩
member-cong x y z h = subst ⟨_⟩ (subst-member x y z h)

--------------------------------------------------------------------------------
-- PART 4. MAXIMALITY AND COUNTABILITY
--------------------------------------------------------------------------------

-- Maximality spelled as predensity, which is what keeps Zorn out of the
-- DEFINITION. A maximal antichain is classically one no strict superset of
-- which is an antichain; that phrasing quantifies over supersets and its
-- existence half is the Zorn-shaped obligation Track C carries. The
-- equivalent "every condition meets some member", which is predensity, is
-- Δ₀ and already in the tree (CodedVocabulary.agda:411-427). Nothing here
-- asserts that a maximal antichain exists; MaximalExtension in part 7 is
-- that assertion and it is a TYPE, not a theorem.

maximalΔ : S → S → S → Ω
maximalΔ c o d = antichainΔ c o d ⊓ predenseΔ c o d

maximal-intro : (c o d : S) → ⟨ antichainΔ c o d ⟩ → ⟨ predenseΔ c o d ⟩
              → ⟨ maximalΔ c o d ⟩
maximal-intro c o d ac pd = ac , pd

maximal-antichain : (c o d : S) → ⟨ maximalΔ c o d ⟩ → ⟨ antichainΔ c o d ⟩
maximal-antichain c o d h = h .fst

maximal-predense : (c o d : S) → ⟨ maximalΔ c o d ⟩ → ⟨ predenseΔ c o d ⟩
maximal-predense c o d h = h .snd

-- Countability against a supplied ground ω code w. The code is an argument
-- and never a construction: the ground profile's Infinity
-- (OrdinaryProfile.agda:83-86) is Bell's truncated inductive-set form and
-- does not even give ω, which is why K6 took ωᴳ as a bare module parameter
-- (K6/GroundTransfer.agda:502). No theorem below inspects w, so nothing
-- here silently assumes it is ω; a consumer that needs that says so with
-- CardinalBridge's isOmega.

countableΔ : S → S → Ω
countableΔ w d = injectable d w

-- The one order-theoretic fact about injectable that the free arrows need,
-- and it is free for a reason worth recording rather than asserting.
-- isInjection f a b (CardinalBridge.agda:283-293) mentions its domain a in
-- ONE clause, the second, and that clause is a single implication
-- (x ∈ˢ a) ⇒ … and not a biconditional. The file records the asymmetry at
-- :224-232 as a known defect. The defect is what makes this lemma cost
-- nothing: the same graph f that is total on b is total on every a ⊆ b, and
-- the function, range and injectivity clauses do not mention a at all.
-- Track B owns injectable's order theory in general; this single entry is
-- proved here because without it the two free arrows would be conditional
-- on an unlanded parameter and could not be called free.

injectable-mono-dom : (a b w : S) → ⟨ subsetΔ a b ⟩
                    → ⟨ injectable b w ⟩ → ⟨ injectable a w ⟩
injectable-mono-dom a b w sub =
  PT.map (λ { (f , (hfun , (hdom , hrest))) →
              f , (hfun , ((λ x hx → hdom x (sub x hx)) , hrest)) })

--------------------------------------------------------------------------------
-- PART 5. THE THREE CONDITIONS
--------------------------------------------------------------------------------

-- The numbering is fixed by the project's design document,
-- forcing-geology-design-2026-09.md:223, and nowhere else: CCC₁ is the
-- MAXIMAL-antichain form, CCC₂ the plain-antichain form, CCC₃ the predense
-- form. Verified at that line in this session. Two independent
-- corroborations inside the roadmap: :219 says the delta-system argument
-- "proves CCC₂(P)", which is the plain form, and :185 says "Transfer CCC₂
-- from P to RO^M(P)". Reversing one and two is silent, because both are
-- well typed Ω's over the same presentation, and it hands K8 the wrong
-- predicate.
--
-- The ascription is the level control and is written before any body.
-- Every one of the three lands in Ω, the model's own truth values, and a
-- draft that had quantified over host subsets would not have been able to:
-- see the header and the break.

CCC₁ᴵ CCC₂ᴵ CCC₃ᴵ : S → S → S → Ω

-- CCC₁. Every maximal antichain of the notion is countable. Weakest of the
-- three, because its hypothesis is the strongest.

CCC₁ᴵ c o w =
  ⋀ S (λ d → ((subsetΔ d c) ⊓ maximalΔ c o d) ⇒ countableΔ w d)

-- CCC₂. Every antichain is countable. This is the predicate the roadmap
-- transfers (roadmap:185) and the one Track D's certificate carries at both
-- ends, so its two directions below are the load-bearing interface of this
-- file.

CCC₂ᴵ c o w =
  ⋀ S (λ d → ((subsetΔ d c) ⊓ antichainΔ c o d) ⇒ countableΔ w d)

-- CCC₃. Every predense set has a countable predense subset. Strongest
-- hypothesis-free reading of the three, and the variant a consumer should
-- prefer, for a reason the break file measures: the empty coded set
-- satisfies the antichain clause of CCC₁ and CCC₂ vacuously and does not
-- satisfy predensity (K5/Dense.agda:520-527, empty-not-dense and its
-- surrounding note).

CCC₃ᴵ c o w =
  ⋀ S (λ d → ((subsetΔ d c) ⊓ predenseΔ c o d)
        ⇒ ⋁ S (λ e → ((subsetΔ e d) ⊓ predenseΔ c o e) ⊓ countableΔ w e))

-- The six directions, in the shape Track D consumes for CCC₂ and in the
-- matching shape for the other two. Each pair is a currying and unfolds
-- nothing, so a consumer written against them cannot drift.

ccc₁-use : (c o w d : S) → ⟨ CCC₁ᴵ c o w ⟩ → ⟨ subsetΔ d c ⟩
         → ⟨ maximalΔ c o d ⟩ → ⟨ injectable d w ⟩
ccc₁-use c o w d h sub mx = h d (sub , mx)

ccc₁-intro : (c o w : S)
           → ((d : S) → ⟨ subsetΔ d c ⟩ → ⟨ maximalΔ c o d ⟩
              → ⟨ injectable d w ⟩)
           → ⟨ CCC₁ᴵ c o w ⟩
ccc₁-intro c o w f d h = f d (h .fst) (h .snd)

ccc-use : (c o v d : S) → ⟨ CCC₂ᴵ c o v ⟩ → ⟨ subsetΔ d c ⟩
        → ⟨ antichainΔ c o d ⟩ → ⟨ injectable d v ⟩
ccc-use c o v d h sub ac = h d (sub , ac)

ccc-intro : (c o v : S)
          → ((d : S) → ⟨ subsetΔ d c ⟩ → ⟨ antichainΔ c o d ⟩
             → ⟨ injectable d v ⟩)
          → ⟨ CCC₂ᴵ c o v ⟩
ccc-intro c o v f d h = f d (h .fst) (h .snd)

ccc₃-use : (c o w d : S) → ⟨ CCC₃ᴵ c o w ⟩ → ⟨ subsetΔ d c ⟩
         → ⟨ predenseΔ c o d ⟩
         → ⟨ ⋁ S (λ e → ((subsetΔ e d) ⊓ predenseΔ c o e) ⊓ countableΔ w e) ⟩
ccc₃-use c o w d h sub pd = h d (sub , pd)

ccc₃-intro : (c o w : S)
           → ((d : S) → ⟨ subsetΔ d c ⟩ → ⟨ predenseΔ c o d ⟩
              → ⟨ ⋁ S (λ e → ((subsetΔ e d) ⊓ predenseΔ c o e)
                          ⊓ countableΔ w e) ⟩)
           → ⟨ CCC₃ᴵ c o w ⟩
ccc₃-intro c o w f d h = f d (h .fst) (h .snd)

--------------------------------------------------------------------------------
-- PART 6. THE TWO FREE ARROWS
--------------------------------------------------------------------------------

-- Both land in CCC₁, and that asymmetry is the fact a consumer must carry:
-- CCC₁ is the WEAKEST of the three, so a transfer certificate whose Φ is
-- CCC₁ proves less than it looks like it proves. The other two arrows are
-- paid and are part 7's reduction types.

-- CCC₂ implies CCC₁ by weakening the hypothesis: a maximal antichain is an
-- antichain, and the predensity half of maximality is discarded. Nothing is
-- spent.

ccc₂→ccc₁ : (c o w : S) → ⟨ CCC₂ᴵ c o w ⟩ → ⟨ CCC₁ᴵ c o w ⟩
ccc₂→ccc₁ c o w h d hyp =
  h d (hyp .fst , maximal-antichain c o d (hyp .snd))

-- CCC₃ implies CCC₁, and this is the one with mathematical content. Let A
-- be a maximal antichain, so predense; CCC₃ hands back a countable predense
-- e ⊆ A. Now e absorbs A: given a ∈ A, predensity of e at a produces some
-- p ∈ e compatible with a; p lies in A because e ⊆ A, both lie in the
-- carrier because A ⊆ c, and the antichain law at A identifies p with a. So
-- A ⊆ e, and injectable-mono-dom carries countability back down. The step
-- from p ≈ˢ a to a ∈ˢ e is member-cong, the second and last spend of paths
-- in this file.
--
-- Both truncations are eliminated into ⟨ a ∈ˢ e ⟩ and ⟨ injectable d w ⟩,
-- which are Ω carriers, so no PT.rec motive here is anything else.

ccc₃→ccc₁ : (c o w : S) → ⟨ CCC₃ᴵ c o w ⟩ → ⟨ CCC₁ᴵ c o w ⟩
ccc₃→ccc₁ c o w h d hyp =
  PT.rec (snd (injectable d w)) step (h d (dsub , maximal-predense c o d mx))
  where
  dsub : ⟨ subsetΔ d c ⟩
  dsub = hyp .fst

  mx : ⟨ maximalΔ c o d ⟩
  mx = hyp .snd

  ac : ⟨ antichainΔ c o d ⟩
  ac = maximal-antichain c o d mx

  absorb : (e : S) → ⟨ subsetΔ e d ⟩ → ⟨ predenseΔ c o e ⟩ → ⟨ subsetΔ d e ⟩
  absorb e esub epd a ha =
    PT.rec (snd (a ∈ˢ e))
      (λ { (p , hpe , hcomp) →
           member-cong p a e
             (ac p (dsub p (esub p hpe)) (esub p hpe) a (dsub a ha) ha hcomp)
             hpe })
      (epd a (dsub a ha))

  step : Σ[ e ∈ S ] ⟨ ((subsetΔ e d) ⊓ predenseΔ c o e) ⊓ countableΔ w e ⟩
       → ⟨ injectable d w ⟩
  step (e , ((esub , epd) , ecnt)) =
    injectable-mono-dom d e w (absorb e esub epd) ecnt

--------------------------------------------------------------------------------
-- PART 7. THE TWO PAID ARROWS, AS REDUCTION TYPES ONLY
--------------------------------------------------------------------------------

-- One lens priced ccc₂→ccc₃ as free and it is not. Extracting a countable
-- predense subset of a predense set b requires first extracting a maximal
-- antichain INSIDE b, which is the same Zorn-shaped extraction as extending
-- an antichain to a maximal one. The two types below are declared here, in
-- the file that owns the predicates, so that Track C's arrows are reductions
-- to a named obligation rather than proofs with an invisible cost. Neither
-- is inhabited anywhere in this tree, measured.
--
-- Bell's route to the first is on disk at
-- bell-2005-boolean-valued-models.fulltext.md:4978-4983, Lemma 4.3's
-- converse: enumerate A ∪ {(⋁A)*} by an ordinal of M and subtract
-- transfinitely. So the cost is an internal ordinal enumeration plus
-- transfinite recursion, not a bare choice function; and the ordinary
-- profile has neither, which is why this is a type and not a theorem.

MaximalExtension : S → S → Type ℓ
MaximalExtension c o =
  (d : S) → ⟨ subsetΔ d c ⟩ → ⟨ antichainΔ c o d ⟩
  → ⟨ ⋁ S (λ e → ((subsetΔ d e) ⊓ (subsetΔ e c)) ⊓ maximalΔ c o e) ⟩

MaximalExtensionIn : S → S → Type ℓ
MaximalExtensionIn c o =
  (b : S) → ⟨ subsetΔ b c ⟩ → ⟨ predenseΔ c o b ⟩
  → ⟨ ⋁ S (λ e → ((subsetΔ e b) ⊓ antichainΔ c o e) ⊓ predenseΔ c o e) ⟩

-- The consumer's own reading of what remains open, stated as the two arrow
-- types so that Track C can alias them rather than retype them. They are
-- TYPES. Nothing below this line proves anything.

CCC₁to₂ : S → S → S → Type ℓ
CCC₁to₂ c o w = MaximalExtension c o → ⟨ CCC₁ᴵ c o w ⟩ → ⟨ CCC₂ᴵ c o w ⟩

CCC₂to₃ : S → S → S → Type ℓ
CCC₂to₃ c o w = MaximalExtensionIn c o → ⟨ CCC₂ᴵ c o w ⟩ → ⟨ CCC₃ᴵ c o w ⟩

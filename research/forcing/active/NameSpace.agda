{-# OPTIONS --cubical --safe --guardedness #-}

-- K3 Track C: closed families, the recognizer and the name bound.
--
-- Section 1.6 of the K3 architecture. The mathematical question is the one
-- every internalization of a recursive predicate has to answer. Track A
-- defines "n is a name" by descent along Child: a host recursion, sealed
-- opaque, with a computation law that lives in the host and not in the
-- ground. The ground cannot see that definition at all. A Δ₀ formula can
-- quantify over the members of a set it is handed and compare them, and
-- nothing more; it cannot run a recursion. So how does a first-order
-- formula recognize a name?
--
-- The classical answer, and K0's (k0-internal-names-probes-2026-09.md:62-76),
-- is to replace the recursion by a WITNESS. A name is a member of some set C
-- that is closed under taking entries: every member of every member of C is
-- an entry whose first coordinate lies again in C and whose weight lies in
-- the carrier W. That condition on C is flat, bounded, and Δ₀; the
-- recognizer then says "there EXISTS such a C containing t", which is one
-- unbounded existential over an otherwise Δ₀ matrix, and therefore Σ₁. The
-- two halves of its adequacy are the content of this file.
--
-- SOUNDNESS is closed-valid: entry closure alone forces every member of C to
-- be a name. The proof is a host induction along Child, and it needs no
-- ground axiom beyond Tier 1, because the only step that leaves the coded
-- world is "a set the object language reads as the Kuratowski pair of x and
-- b IS the term entry x b", which is extensionality and nothing else. This
-- is why the record ClosedFamily below carries no `valid` field: validity is
-- a theorem about any coded closed family, not a datum one has to supply,
-- and putting it in the record would make the record unreachable by
-- Collection, which can only produce sets, not host proofs.
--
-- COMPLETENESS is hereditary: every name is a member of some coded closed
-- family. Here the recursion runs the other way and the question is where
-- the set C comes from. K0 built it by an omega iteration of a one-step
-- closure operator (NameClosureStep.agda, k0-reference/), which needs the L
-- specific iterator and, at the ordinary profile, Infinity. This file takes
-- the architecture's Collection route instead: by Child-induction each
-- subname already has a closed family, Collection over `support n` gathers
-- one such family for each subname into a single set F, Separation keeps the
-- members of F that really are closed, the union of those is closed and
-- contains every subname, and adjoining n itself closes the induction. No
-- Infinity, no internal recursion, no transitive closure. The truncation in
-- the conclusion costs nothing because Collection's own premise is a
-- truncated existential and every consumer eliminates into a proposition.
--
-- THE BOUND is the separate, non-recursive half. Once every subname of n is
-- known to lie in a set C, the entries of n are Kuratowski pairs drawn from
-- C and W, so n itself lies three power sets above C ∪ W. That is a
-- statement about codes and not about names, it needs PowerSet, and PowerSet
-- appears nowhere else in K3; it is therefore an explicit argument of the
-- two declarations that use it and not a hypothesis of anything.
--
-- WHAT THIS FILE IS NOT. It does not produce a name by recursion. Track D
-- measured that a name-valued recursion needs the tier-0 accessibility datum
-- and the tier-4 member-image datum together, because the internal image of
-- the entry-forming function and the recursion equation are the same
-- statement up to a fixed point (REPORT-D F5, F6, F7). Nothing below builds
-- a set by recursion: the recursions here produce PROPOSITIONS, ⟨ IsName n ⟩
-- and ∥ ClosedFamily n ∥₁, and the sets they mention are produced by
-- Collection, Separation, Union and PowerSet at each single step. So no
-- MemberImage appears in any telescope and none is silently widened in.
--
-- THE LEDGER IS THE NESTING, as on Track B. The coded layer at the top takes
-- no hypothesis at all. `Space` adds the weight carrier and twelve facts of
-- Track A's kernel and still no ground axiom. `Ground` is Tier 1 and holds
-- the description bridge. `Recognize` proves soundness from Tier 1 alone.
-- `Intersect` adds Separation. `Ops` adds a union and a pair operation as
-- OPERATIONS, so neither Union nor Pairing is consumed here at all; they are
-- consumed by Tracks A and B and arrive already built. `Collect` adds
-- Separation and Collection and the support interface. That is the whole
-- cost of section 1.6.
--
-- THE SEAL. Every description term below is opaque together with its
-- specification at the point of definition: Track A measured 761 s at 1.05
-- GB against 1.04 s at 327 MB on exactly this point (REPORT-A A1). Only two
-- such terms are built here, the power set and the two separations, because
-- the pair and the union arrive as parameters and a parameter is already
-- maximally stuck.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import NameSupport
import GroundDescription
import NameImage

module NameSpace {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ∃̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; checkΔ₀ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open import OrdinaryProfile 𝒮 using ( Separation; Collection; PowerSet )
open import CodedVocabulary 𝒮
  using ( isSglΔ; isPairΔ; isKPairΔ; prAtˢ
        ; sepAt; sepAt-reading; Δ₀-sepAt; Δ₀-inst )
open import Cubical.Data.Unit using ( tt )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Induction.WellFounded using ( WellFounded; module WFI )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ) hiding ( ¬_ )
open hPropStructure 𝒮
open At S id using ( _⊨_ )

-- Track A hosts the four ground tiers and the accessibility datum at
-- NameKernel's own top level; the architecture gives them a node, K3.0, and
-- assigns that node to no track (REPORT-A A3, REPORT-D F10). They are taken
-- from there and no second home is opened.

module NK = NameKernel 𝒮
module NS = NameSupport 𝒮
open NK using ( Core; Sets; Families; Accessibility )

-- ---------------------------------------------------------------------
-- The coded layer: two formulas, and no hypothesis whatsoever
-- ---------------------------------------------------------------------

-- A formula and its reading are facts about the evaluator, so nothing here
-- needs a ground axiom, a kernel fact or even the weight carrier as a fixed
-- set: both formulas carry the carrier in a variable slot, which is what
-- lets them sit inside a Separation with a different carrier frozen in.

-- ENTRY CLOSURE. "for every n in C, for every member e of n, there is an x
-- in C and a b in w with e the Kuratowski pair of x and b". All four
-- quantifiers are bounded, by C, by n, by C and by w in that order, and the
-- matrix is K2's prAtˢ, which is itself Δ₀ and all of whose quantifiers are
-- bounded by the pair (CodedVocabulary.agda:112-127). This is the whole
-- reason the recognizer can be assembled at all: trap (1) of this track asks
-- whether closedΔ is genuinely Δ₀, and Δ₀-closedAtˢ answers it by checkΔ₀,
-- not by inspection.
--
-- The de Bruijn shifts are the only fiddly part and the reading theorem is
-- what checks them. Under the two bounded universals the outer slots c and w
-- have moved down by two, and under the existential over C by one more, so
-- the carrier slot is written suc (suc (suc w)) and not suc w. A wrong
-- shift is invisible to the Δ₀ witness, which holds for any slot assignment,
-- and is caught only here.

closedAtˢ : ∀ {k} → Fin k → Fin k → Formula S k
closedAtˢ c w =
  ∀̇∈ (var c)
    (∀̇∈ (var zero)
      (∃̇∈ (var (suc (suc c)))
        (∃̇∈ (var (suc (suc (suc w))))
          (prAtˢ (suc (suc zero)) (suc zero) zero))))

closedΔ : S → S → Ω
closedΔ w C =
  ⋀ S (λ n → (n ∈ˢ C) ⇒
    (⋀ S (λ e → (e ∈ˢ n) ⇒
      (⋁ S (λ x → (x ∈ˢ C) ⊓
        (⋁ S (λ b → (b ∈ˢ w) ⊓ isKPairΔ e x b)))))))

Δ₀-closedAtˢ : ∀ {k} (c w : Fin k) → Δ₀ (closedAtˢ c w)
Δ₀-closedAtˢ c w = checkΔ₀ (closedAtˢ c w) tt

closedAtˢ-reading : ∀ {k} (c w : Fin k) (γ : S ^ k)
                  → (γ ⊨ closedAtˢ c w) ≡ closedΔ (lookup w γ) (lookup c γ)
closedAtˢ-reading c w γ = refl

-- THE RECOGNIZER. One unbounded existential in front of the Δ₀ matrix
-- above, plus the membership of the candidate in the witnessing family.
-- Its complexity is recorded here and nowhere discharged: there is no
-- Δ₀-nameAtˢ in this file and there must be none, because the leading
-- quantifier ranges over all sets and no bound on the witnessing family is
-- available from the ordinary profile. The consequence, stated once so that
-- no later track assumes otherwise, is that IsName is NOT known to be
-- absolute between a model and a submodel or an extension (architecture N5).

nameAtˢ : ∀ {k} → Fin k → Fin k → Formula S k
nameAtˢ t w = ∃̇ ((var (suc t) ∈̇ var zero) ∧̇ closedAtˢ zero (suc w))

nameΔ : S → S → Ω
nameΔ w t = ⋁ S (λ C → (t ∈ˢ C) ⊓ closedΔ w C)

nameAtˢ-reading : ∀ {k} (t w : Fin k) (γ : S ^ k)
                → (γ ⊨ nameAtˢ t w) ≡ nameΔ (lookup w γ) (lookup t γ)
nameAtˢ-reading t w γ = refl

-- ---------------------------------------------------------------------
-- Closure is inherited from a cover by closed subsets
-- ---------------------------------------------------------------------

-- The combinator the completeness proof below uses internally, lifted out
-- because it answers a question that arises the moment a closed family has
-- to be BUILT rather than assumed. Several sets are already known to be
-- entry closed. Is the set they jointly fill up entry closed as well?
--
-- It is, and the reason is that the closure clause is LOCAL. To decompose a
-- member e of a member n of U it is enough to find one closed set C that
-- already holds n: C's own clause decomposes e and hands back a first
-- coordinate inside C, and a first coordinate inside C is a first
-- coordinate inside U as soon as C is a subset of U. Nothing about the rest
-- of the cover is ever consulted, so the cover may be indexed by anything
-- at all and its pieces may overlap however they like.
--
-- Three consequences of that shape are worth stating, because they are what
-- make this lemma cheap. It spends no axiom: not Separation, not Union, not
-- Pairing, not PowerSet. It spends no kernel fact: neither entry-inj nor
-- kpair-unique appears, which is exactly the difference from `common`
-- below, where an intersection forces two decompositions of the same member
-- to be compared and injectivity is the whole content. And it never
-- mentions a union OPERATION: the cover is presented by its membership
-- facts alone, so a consumer that obtained its union some other way, or has
-- no union operation at hand, pays nothing to use this.

closed-cover : (w U : S)
             → ((z : S) → ⟨ z ∈ˢ U ⟩
                → ∥ Σ[ C ∈ S ] (⟨ closedΔ w C ⟩ × ⟨ z ∈ˢ C ⟩ × ⟨ C ⊆ˢ U ⟩) ∥₁)
             → ⟨ closedΔ w U ⟩
closed-cover w U cover n hn e he =
  PT.rec PT.squash₁
    (λ { (C , cl , hnC , sub) →
           PT.map (λ { (x , hxC , wts) → x , sub x hxC , wts })
                  (cl n hnC e he) })
    (cover n hn)

-- THE FAMILY INDEXED UNION, which is the case the completeness proof below
-- actually takes and the case a consumer building a domain by Collection
-- wants. The cover is now a coded set G of closed sets and U is anything
-- its members fill up. Read the three hypotheses as the three membership
-- facts of a union: every member of G is closed, everything in a member of
-- G is in U, and everything in U came from some member of G.

closed-family : (w G U : S)
              → ((C : S) → ⟨ C ∈ˢ G ⟩ → ⟨ closedΔ w C ⟩)
              → ((C z : S) → ⟨ C ∈ˢ G ⟩ → ⟨ z ∈ˢ C ⟩ → ⟨ z ∈ˢ U ⟩)
              → ((z : S) → ⟨ z ∈ˢ U ⟩
                 → ∥ Σ[ C ∈ S ] (⟨ C ∈ˢ G ⟩ × ⟨ z ∈ˢ C ⟩) ∥₁)
              → ⟨ closedΔ w U ⟩
closed-family w G U closed into out = closed-cover w U
  (λ z hz → PT.map (λ { (C , hCG , hzC) →
                         C , closed C hCG , hzC , (λ x hx → into C x hCG hx) })
                  (out z hz))

-- THE TWO SET CASE, which is the same proof with a two element index and is
-- therefore derived rather than reproved. It is stated through membership
-- facts for the same reason the family case is: a consumer whose union came
-- from a pair of coordinate domains rather than from ⋃ᴳ can still use it.

closed-union : (w C D U : S)
             → ((z : S) → ⟨ z ∈ˢ C ⟩ → ⟨ z ∈ˢ U ⟩)
             → ((z : S) → ⟨ z ∈ˢ D ⟩ → ⟨ z ∈ˢ U ⟩)
             → ((z : S) → ⟨ z ∈ˢ U ⟩ → ∥ (⟨ z ∈ˢ C ⟩ ⊎ ⟨ z ∈ˢ D ⟩) ∥₁)
             → ⟨ closedΔ w C ⟩ → ⟨ closedΔ w D ⟩ → ⟨ closedΔ w U ⟩
closed-union w C D U inC inD out cc dd = closed-cover w U
  (λ z hz → PT.map (λ { (inl h) → C , cc , h , inC
                      ; (inr h) → D , dd , h , inD })
                  (out z hz))

-- ---------------------------------------------------------------------
-- Tier 1: the description bridge and the power set
-- ---------------------------------------------------------------------

-- Everything in this module is available from ordinary Extensionality and
-- the realization of ≈ˢ as a host path, which is what Core carries beyond
-- Pairing. It is separated from the name layer below because none of it
-- mentions a name, an entry or the weight carrier.

module Ground (𝔠 : Core) where

  open Core 𝔠 using ( extensional; ≈ˢ-paths )

  -- Track B proves the determinacy chain from this tier alone, and its
  -- version is the one to use: the coordinator's EntryCanonical reaches the
  -- same conclusion but carries an accessibility datum and a weight carrier
  -- that neither of its three lemmas consumes (REPORT-B 4.4).
  open NS.Determinacy 𝔠 public
    using ( separateOf; separateOf-spec; ≈→≡; kpair-det )

  open GroundDescription 𝒮 extensional ≈ˢ-paths using ( powerOf-spec )
    renaming ( powerOf to powerOf′ )

  -- Two free slots and constants, the shape Collection wants. The tree has
  -- no such operation: sepAt freezes every slot but one, and nothing in
  -- CodedVocabulary produces a Formula S 2 from a formula with constants.
  -- Track D built it from the same instFo and ⊨-inst that sepAt uses, so no
  -- new formula manipulation enters K3 (REPORT-D F4), and it is opened from
  -- there rather than reproved.
  open NameImage 𝒮 extensional ≈ˢ-paths public
    using ( colAt; colAt-reading; atCon₂ )

  -- The power set, sealed with its specification. GroundDescription's
  -- powerOf is a description term and is transparent there; the bound below
  -- nests three of them, which is exactly the shape Track A measured at
  -- 761 s. Sealing costs nothing because inPow is the only consumer and it
  -- goes through the specification.
  opaque
    𝒫 : PowerSet → S → S
    𝒫 pow a = powerOf′ pow a

    𝒫-spec : (pow : PowerSet) (a x : S)
           → (x ∈ˢ 𝒫 pow a) ≡ (⋀ S (λ y → (y ∈ˢ x) ⇒ (y ∈ˢ a)))
    𝒫-spec pow a x = powerOf-spec pow a x

  inPow : (pow : PowerSet) (a x : S)
        → ((z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ a ⟩) → ⟨ x ∈ˢ 𝒫 pow a ⟩
  inPow pow a x h = subst ⟨_⟩ (sym (𝒫-spec pow a x)) h

  -- Transport of membership along a path in the left argument. Track B
  -- names it once; it is re-exported here so that this file does not carry a
  -- second copy of a one-line lemma.
  open NS public using ( mem-substˡ )

-- ---------------------------------------------------------------------
-- Section 1.6. Closed families, the recognizer and the name bound
-- ---------------------------------------------------------------------

-- The parameters are the weight carrier and twelve declarations of Track A,
-- taken flat and cited by line. No ground axiom appears here, which is the
-- same measurement Track B reports for its own entry layer: the notion of a
-- closed family is a statement about a ground code and the subname relation,
-- and it needs no axiom to be stated.
--
-- Note what is NOT asked for. There is no accessibility datum. Track B
-- measured that the architecture's permitted list over-states by exactly
-- this one item (REPORT-B 4.3), and the same holds here: what the two
-- inductions below descend along is Child, and child-wf is what Track A
-- derives from WellFounded _∈ᵗ_ through the three membership steps. Asking
-- for the tier-0 datum as well would put a hypothesis in the ledger that no
-- proof in this file consumes.
--
-- name-intro is Track A's introduction rule for the sealed predicate. It is
-- not in the architecture's list of kernel exports, and both inductions here
-- are impossible without it: soundness has to CONSTRUCT ⟨ IsName n ⟩ from
-- the shape clause and the hereditary clause, which is exactly what the seal
-- hides.
--
-- Two further facts were in the first draft of this telescope and are gone,
-- because the compiled file never referred to them. isPropChild is not
-- needed because every elimination of a Child below lands in a membership,
-- in a truncation or in ⟨ IsName x ⟩, all of them propositions already; and
-- child-is-name is not needed because validity here is DERIVED, by
-- closed-valid, rather than inherited from a name that is already known.
-- The audit is mechanical: the two names occur nowhere in the body.

module Space (W : S)
  (entry          : S → S → S)                              -- NameKernel:253
  (entry-inj      : {x b y c : S} → entry x b ≡ entry y c
                  → (x ≡ y) × (b ≡ c))                                -- :321
  (entry-isKPair  : (x b : S) → ⟨ isKPairΔ (entry x b) x b ⟩)         -- :332
  (Child          : S → S → Type ℓ)                                   -- :368
  (child-entry    : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)     -- :369
  (child-weight   : (x n : S) → Child x n
                  → ∥ Σ[ b ∈ S ] ⟨ entry x b ∈ˢ n ⟩ ∥₁)               -- :369
  (child-wf       : WellFounded Child)                                -- :392
  (IsName         : S → Ω)                                            -- :461
  (name-shape     : (n : S) → ⟨ IsName n ⟩ → (e : S) → ⟨ e ∈ˢ n ⟩
                  → ∥ Σ[ x ∈ S ] Σ[ b ∈ S ]
                        (e ≡ entry x b) × ⟨ b ∈ˢ W ⟩ ∥₁)              -- :467
  (name-intro     : (n : S)
                  → ((e : S) → ⟨ e ∈ˢ n ⟩
                     → ∥ Σ[ x ∈ S ] Σ[ b ∈ S ]
                           (e ≡ entry x b) × ⟨ b ∈ˢ W ⟩ ∥₁)
                  → ((x : S) → Child x n → ⟨ IsName x ⟩)
                  → ⟨ IsName n ⟩)                                     -- :473
  where

  -- Closure in the HOST sense: C is closed when every subname of a member is
  -- a member. This is weaker than the coded condition, which also asserts
  -- that every member of a member has the shape of an entry, and the gap is
  -- deliberate. The coded condition is what a formula can say; the host
  -- condition is what a consumer of a closed family wants to use.

  Closed : S → Type ℓ
  Closed C = (n : S) → ⟨ n ∈ˢ C ⟩ → (x : S) → Child x n → ⟨ x ∈ˢ C ⟩

  -- ---------------------------------------------------------------------
  -- Soundness of the recognizer, from Tier 1 alone
  -- ---------------------------------------------------------------------

  module Recognize (𝔠 : Core) where

    open Ground 𝔠 public

    -- The single line where the coded layer and the term layer meet. A set
    -- that the object language reads as the Kuratowski pair of x and b is
    -- the kernel's entry on the nose, because the kernel's entry is such a
    -- set and two of them agree member by member. Extensionality is spent
    -- here and, on this track, essentially nowhere else.

    kpair-unique : (q x b : S) → ⟨ isKPairΔ q x b ⟩ → q ≡ entry x b
    kpair-unique q x b h = kpair-det q (entry x b) x b h (entry-isKPair x b)

    -- Coded closure implies host closure. Reading the proof backwards is the
    -- clearest way to see why the coded condition has to mention W: a child
    -- of n arrives as a truncated entry, the closure clause offers SOME
    -- decomposition of that entry, and injectivity says the decomposition
    -- offered is the one we started from. Without injectivity the two
    -- first coordinates could differ and the child would not be recovered.

    coded→closed : (C : S) → ⟨ closedΔ W C ⟩ → Closed C
    coded→closed C cl n hn x edge = PT.rec (snd (x ∈ˢ C)) fromWeight
      (child-weight x n edge)
      where
        fromWeight : Σ[ b ∈ S ] ⟨ entry x b ∈ˢ n ⟩ → ⟨ x ∈ˢ C ⟩
        fromWeight (b , he) = PT.rec (snd (x ∈ˢ C)) outer (cl n hn (entry x b) he)
          where
            inner : (x' : S) → ⟨ x' ∈ˢ C ⟩
                  → Σ[ b' ∈ S ] (⟨ b' ∈ˢ W ⟩ × ⟨ isKPairΔ (entry x b) x' b' ⟩)
                  → ⟨ x ∈ˢ C ⟩
            inner x' hx' (b' , _ , hk) =
              subst (λ u → ⟨ u ∈ˢ C ⟩)
                (sym (fst (entry-inj (kpair-unique (entry x b) x' b' hk)))) hx'

            outer : Σ[ x' ∈ S ] (⟨ x' ∈ˢ C ⟩
                  × ⟨ ⋁ S (λ b' → (b' ∈ˢ W) ⊓ isKPairΔ (entry x b) x' b') ⟩)
                  → ⟨ x ∈ˢ C ⟩
            outer (x' , hx' , wts) =
              PT.rec (snd (x ∈ˢ C)) (inner x' hx') wts

    -- THE key lemma of section 1.6, and the reason ClosedFamily needs no
    -- `valid` field. Entry closure is a flat, coded condition; being a name
    -- is a recursive, host condition; and the first implies the second by
    -- one induction along Child. This is K0's recognizer soundness
    -- (k0-internal-names-probes-2026-09.md:66) with the omega iterator
    -- removed, and it is proved BEFORE any closed family is built, which is
    -- what keeps the Collection route open: Collection produces sets and
    -- cannot produce host proofs, so a record with a `valid` field could
    -- never be assembled from it.

    closed-valid : (C : S) → ⟨ closedΔ W C ⟩
                 → (n : S) → ⟨ n ∈ˢ C ⟩ → ⟨ IsName n ⟩
    closed-valid C cl =
      WFI.induction child-wf {P = λ n → ⟨ n ∈ˢ C ⟩ → ⟨ IsName n ⟩} step
      where
        step : (n : S) → ((x : S) → Child x n → ⟨ x ∈ˢ C ⟩ → ⟨ IsName x ⟩)
             → ⟨ n ∈ˢ C ⟩ → ⟨ IsName n ⟩
        step n IH hn = name-intro n shape hereditary-clause
          where
            shape : (e : S) → ⟨ e ∈ˢ n ⟩
                  → ∥ Σ[ x ∈ S ] Σ[ b ∈ S ]
                        (e ≡ entry x b) × ⟨ b ∈ˢ W ⟩ ∥₁
            shape e he = PT.rec PT.squash₁
              (λ { (x , hx , wts) → PT.map
                     (λ { (b , hb , hk) → x , b , kpair-unique e x b hk , hb })
                     wts })
              (cl n hn e he)

            hereditary-clause : (x : S) → Child x n → ⟨ IsName x ⟩
            hereditary-clause x edge = IH x edge (coded→closed C cl n hn x edge)

    -- The witness the recognizer quantifies over. Three fields, all of them
    -- data the ground can hand over; `closed` and `valid` are derived, not
    -- supplied, which is exactly the decision recorded above.

    record ClosedFamily (n : S) : Type ℓ where
      constructor closedFamily
      field
        C        : S
        contains : ⟨ n ∈ˢ C ⟩
        coded    : ⟨ closedΔ W C ⟩

      closed : Closed C
      closed = coded→closed C coded

      valid : (x : S) → ⟨ x ∈ˢ C ⟩ → ⟨ IsName x ⟩
      valid = closed-valid C coded

    -- One half of adequacy, and the cheap half. The recognizer's existential
    -- is truncated, and ⟨ IsName t ⟩ is a proposition, so the elimination is
    -- legitimate with nothing to check.

    name-sound : (t : S) → ⟨ nameΔ W t ⟩ → ⟨ IsName t ⟩
    name-sound t = PT.rec (snd (IsName t))
      (λ { (C , hc , cl) → closed-valid C cl t hc })

    -- ---------------------------------------------------------------------
    -- Two closed families have a closed common part
    -- ---------------------------------------------------------------------

    -- Separation and nothing else. The mathematics is one application of
    -- injectivity: a member e of a member m of C ∩ D is decomposed twice,
    -- once by C's closure clause and once by D's, and the two decompositions
    -- have the same first coordinate because both are the canonical entry of
    -- the same set. Without kpair-unique the two witnesses would be
    -- unrelated and the intersection would not be closed.

    module Intersect (sep : Separation) where

      interFo : S → Formula S 1
      interFo D = sepAt (var zero ∈̇ var (suc zero)) (D ∷ [])

      interFo-reading : (D x : S) → ((x ∷ []) ⊨ interFo D) ≡ (x ∈ˢ D)
      interFo-reading D x =
        sepAt-reading (var zero ∈̇ var (suc zero)) (D ∷ []) x

      opaque
        inter : S → S → S
        inter C D = separateOf sep C (interFo D)

        inter-spec : (C D x : S)
                   → (x ∈ˢ inter C D) ≡ ((x ∈ˢ C) ⊓ (x ∈ˢ D))
        inter-spec C D x =
          separateOf-spec sep C (interFo D) x
          ∙ cong ((x ∈ˢ C) ⊓_) (interFo-reading D x)

      common : (C D : S) → ⟨ closedΔ W C ⟩ → ⟨ closedΔ W D ⟩
             → Σ[ E ∈ S ] (⟨ E ⊆ˢ C ⟩ × ⟨ E ⊆ˢ D ⟩ × ⟨ closedΔ W E ⟩)
      common C D hC hD = inter C D , leftIn , rightIn , coded
        where
          leftIn : ⟨ inter C D ⊆ˢ C ⟩
          leftIn x m = fst (subst ⟨_⟩ (inter-spec C D x) m)

          rightIn : ⟨ inter C D ⊆ˢ D ⟩
          rightIn x m = snd (subst ⟨_⟩ (inter-spec C D x) m)

          coded : ⟨ closedΔ W (inter C D) ⟩
          coded m hm e he = PT.rec (snd goal) fromC
            (hC m (leftIn m hm) e he)
            where
              goal : Ω
              goal = ⋁ S (λ x → (x ∈ˢ inter C D) ⊓
                       (⋁ S (λ b → (b ∈ˢ W) ⊓ isKPairΔ e x b)))

              fromC : Σ[ x ∈ S ] (⟨ x ∈ˢ C ⟩
                    × ⟨ ⋁ S (λ b → (b ∈ˢ W) ⊓ isKPairΔ e x b) ⟩)
                    → ⟨ goal ⟩
              fromC (x , hxC , wts) = PT.rec (snd goal)
                (λ { (b , hbW , hk) → PT.rec (snd goal)
                       (λ { (x' , hx'D , wts') → PT.rec (snd goal)
                              (λ { (b' , _ , hk') →
                                     ∣ x
                                     , subst ⟨_⟩ (sym (inter-spec C D x))
                                         ( hxC
                                         , subst (λ u → ⟨ u ∈ˢ D ⟩)
                                             (fst (entry-inj
                                               (sym (kpair-unique e x' b' hk')
                                                ∙ kpair-unique e x b hk)))
                                             hx'D )
                                     , ∣ b , hbW , hk ∣₁ ∣₁ })
                              wts' })
                       (hD m (rightIn m hm) e he) })
                wts

    -- ---------------------------------------------------------------------
    -- Two ground operations, taken as operations
    -- ---------------------------------------------------------------------

    -- The union and the unordered pair are NOT rebuilt here. They arrive as
    -- parameters, from Track B and Track A, which is both the honest ledger
    -- and the cheapest thing for the typechecker: a module parameter is a
    -- neutral variable and cannot unfold at all, so the nesting that cost
    -- Track A 761 s cannot arise for these two. Neither Union nor Pairing is
    -- a hypothesis of anything below.

    module Ops
      (⋃ᴳ          : S → S)                                 -- NameSupport:444
      (⋃ᴳ-spec     : (a x : S)
                   → (x ∈ˢ ⋃ᴳ a) ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ (x ∈ˢ y)))  -- :447
      (pairOf      : S → S → S)                              -- NameKernel:204
      (pairOf-left : (a b : S) → ⟨ a ∈ˢ pairOf a b ⟩)                 -- :225
      (pairOf-right : (a b : S) → ⟨ b ∈ˢ pairOf a b ⟩)                -- :228
      (∈-pairOf    : (a b z : S) → ⟨ z ∈ˢ pairOf a b ⟩
                   → ∥ (z ≡ a) ⊎ (z ≡ b) ∥₁)                          -- :220
      where

      ⋃ᴳ-in : (a y x : S) → ⟨ y ∈ˢ a ⟩ → ⟨ x ∈ˢ y ⟩ → ⟨ x ∈ˢ ⋃ᴳ a ⟩
      ⋃ᴳ-in a y x hy hx = subst ⟨_⟩ (sym (⋃ᴳ-spec a x)) ∣ y , hy , hx ∣₁

      -- The family indexed union closure at the union OPERATION, which is
      -- the form the completeness proof below consumes and the one a
      -- consumer holding Track B's ⋃ᴳ will reach for. All the mathematics
      -- is in closed-family; the two lines here only translate ⋃ᴳ-spec into
      -- the membership presentation.

      closed-⋃ᴳ : (G : S) → ((C : S) → ⟨ C ∈ˢ G ⟩ → ⟨ closedΔ W C ⟩)
                → ⟨ closedΔ W (⋃ᴳ G) ⟩
      closed-⋃ᴳ G closed = closed-family W G (⋃ᴳ G) closed
        (λ C z hCG hzC → ⋃ᴳ-in G C z hCG hzC)
        (λ z hz → subst ⟨_⟩ (⋃ᴳ-spec G z) hz)

      binUnion : S → S → S
      binUnion a b = ⋃ᴳ (pairOf a b)

      binUnion-inl : (a b z : S) → ⟨ z ∈ˢ a ⟩ → ⟨ z ∈ˢ binUnion a b ⟩
      binUnion-inl a b z h = ⋃ᴳ-in (pairOf a b) a z (pairOf-left a b) h

      binUnion-inr : (a b z : S) → ⟨ z ∈ˢ b ⟩ → ⟨ z ∈ˢ binUnion a b ⟩
      binUnion-inr a b z h = ⋃ᴳ-in (pairOf a b) b z (pairOf-right a b) h

      binUnion-out : (a b z : S) → ⟨ z ∈ˢ binUnion a b ⟩
                   → ∥ (⟨ z ∈ˢ a ⟩ ⊎ ⟨ z ∈ˢ b ⟩) ∥₁
      binUnion-out a b z m = PT.rec PT.squash₁
        (λ { (y , hy , hz) → PT.map
               (λ { (inl p) → inl (subst (λ u → ⟨ z ∈ˢ u ⟩) p hz)
                  ; (inr p) → inr (subst (λ u → ⟨ z ∈ˢ u ⟩) p hz) })
               (∈-pairOf a b y hy) })
        (subst ⟨_⟩ (⋃ᴳ-spec (pairOf a b) z) m)

      -- Adjoining one point. The singleton is the diagonal pair, exactly as
      -- Track A spells it (NameKernel.agda:235), so no third operation is
      -- needed and the singleton here is the kernel's singleton on the nose.

      adjoin : S → S → S
      adjoin a t = binUnion a (pairOf t t)

      adjoin-old : (a t z : S) → ⟨ z ∈ˢ a ⟩ → ⟨ z ∈ˢ adjoin a t ⟩
      adjoin-old a t z h = binUnion-inl a (pairOf t t) z h

      adjoin-new : (a t : S) → ⟨ t ∈ˢ adjoin a t ⟩
      adjoin-new a t = binUnion-inr a (pairOf t t) t (pairOf-left t t)

      adjoin-out : (a t z : S) → ⟨ z ∈ˢ adjoin a t ⟩
                 → ∥ (⟨ z ∈ˢ a ⟩ ⊎ (z ≡ t)) ∥₁
      adjoin-out a t z m = PT.rec PT.squash₁
        (λ { (inl h) → ∣ inl h ∣₁
           ; (inr h) → PT.map
               (λ { (inl p) → inr p ; (inr p) → inr p })
               (∈-pairOf t t z h) })
        (binUnion-out a (pairOf t t) z m)

      -- ---------------------------------------------------------------------
      -- The bound on names with a given support
      -- ---------------------------------------------------------------------

      -- The one place PowerSet is used in K3, and it is an ARGUMENT, not a
      -- hypothesis: nothing else in section 1.6 needs it, and a tier record
      -- carrying it would misreport the cost of the recognizer.
      --
      -- The mathematics is the internal Kuratowski product. If every subname
      -- of n lies in C then each member of n is entry x b with x in C and b
      -- in W, so each member of a member of n is a subset of C ∪ W, each
      -- member of n is a subset of the power set of C ∪ W, and n itself is a
      -- subset of the power set of that. Three power sets, no more and no
      -- fewer, and the count is visible in the three nested inPow calls.
      --
      -- Note that the proof never unfolds entry. It reads the entry through
      -- entry-isKPair, whose third clause says every member of the entry is
      -- either the coded singleton of x or the coded pair of x and b, and
      -- both of those say directly what their members are. Track B found the
      -- same: entry-isKPair alone replaces six unfolding lemmas (REPORT-B 4.5).

      nameBound : PowerSet → (C : S) → S
      nameBound pow C = 𝒫 pow (𝒫 pow (𝒫 pow (binUnion C W)))

      nameBound-contains : (pow : PowerSet) (C n : S) → ⟨ IsName n ⟩
                         → ((x : S) → Child x n → ⟨ x ∈ˢ C ⟩)
                         → ⟨ n ∈ˢ nameBound pow C ⟩
      nameBound-contains pow C n hn sub = inPow pow layer₂ n outer
        where
          base layer₁ layer₂ : S
          base   = binUnion C W
          layer₁ = 𝒫 pow base
          layer₂ = 𝒫 pow layer₁

          fromEntry : (e x b : S) → e ≡ entry x b → ⟨ b ∈ˢ W ⟩
                    → ⟨ e ∈ˢ n ⟩ → ⟨ e ∈ˢ layer₂ ⟩
          fromEntry e x b eq hb he = inPow pow layer₁ e mid
            where
              hxC : ⟨ x ∈ˢ C ⟩
              hxC = sub x (child-entry x b n
                            (subst (λ u → ⟨ u ∈ˢ n ⟩) eq he))

              hxBase : ⟨ x ∈ˢ base ⟩
              hxBase = binUnion-inl C W x hxC

              hbBase : ⟨ b ∈ˢ base ⟩
              hbBase = binUnion-inr C W b hb

              mid : (w : S) → ⟨ w ∈ˢ e ⟩ → ⟨ w ∈ˢ layer₁ ⟩
              mid w hw = inPow pow base w inner
                where
                  shapes : ⟨ isSglΔ w x ⊔ isPairΔ w x b ⟩
                  shapes = snd (snd (entry-isKPair x b)) w
                             (subst (λ u → ⟨ w ∈ˢ u ⟩) eq hw)

                  inner : (z : S) → ⟨ z ∈ˢ w ⟩ → ⟨ z ∈ˢ base ⟩
                  inner z hz = PT.rec (snd (z ∈ˢ base)) branch shapes
                    where
                      branch : (⟨ isSglΔ w x ⟩ ⊎ ⟨ isPairΔ w x b ⟩)
                             → ⟨ z ∈ˢ base ⟩
                      branch (inl (_ , all)) =
                        mem-substˡ (sym (≈→≡ (all z hz))) hxBase
                      branch (inr (_ , _ , all)) =
                        PT.rec (snd (z ∈ˢ base))
                          (λ { (inl p) → mem-substˡ (sym (≈→≡ p)) hxBase
                             ; (inr p) → mem-substˡ (sym (≈→≡ p)) hbBase })
                          (all z hz)

          outer : (e : S) → ⟨ e ∈ˢ n ⟩ → ⟨ e ∈ˢ layer₂ ⟩
          outer e he = PT.rec (snd (e ∈ˢ layer₂))
            (λ { (x , b , eq , hb) → fromEntry e x b eq hb he })
            (name-shape n hn e he)

      -- ---------------------------------------------------------------------
      -- Completeness: every name has a coded closed family
      -- ---------------------------------------------------------------------

      -- THE CONTRACT of section 1.6, and the only place Collection is spent.
      --
      -- The shape of the argument. Suppose every subname of n already has a
      -- closed family. Collection over `support n`, with the two-variable
      -- formula "y is entry-closed and x belongs to y", returns a single set
      -- F meeting every one of those families. F may contain junk, because
      -- Collection promises only that a witness for each x is somewhere in
      -- F, so one Separation keeps the members of F that really are closed.
      -- The union of a set of closed sets is closed, and it contains every
      -- subname of n. Adjoining n itself is the last step: the only new
      -- member is n, its own subnames lie in the support, and the support is
      -- already inside the union. Nothing is iterated and nothing is
      -- transfinite; the induction is the host's Child-induction and each
      -- step is one Collection, one Separation and two unions.
      --
      -- Why the truncation costs nothing. The induction hypothesis is
      -- ∥ ClosedFamily x ∥₁ and is used only to feed Collection's premise,
      -- which is itself a truncated existential; the conclusion is again
      -- truncated, and every consumer of a closed family in K3 eliminates
      -- into a proposition. No representative is ever chosen.

      module Collect (sep : Separation) (coll : Collection)
        (support       : S → S)                            -- NameSupport:514
        (support-in    : (n : S) → ⟨ IsName n ⟩ → (x : S) → Child x n
                       → ⟨ x ∈ˢ support n ⟩)                         -- :542
        (support-out   : (n x : S) → ⟨ x ∈ˢ support n ⟩ → Child x n) -- :534
        (support-valid : (n : S) → ⟨ IsName n ⟩ → (x : S)
                       → ⟨ x ∈ˢ support n ⟩ → ⟨ IsName x ⟩)          -- :563
        where

        -- The separation class that keeps the genuinely closed members of
        -- the collected set. One free slot for the candidate family, the
        -- weight carrier frozen as a constant.

        closedFo : Formula S 1
        closedFo = sepAt (closedAtˢ zero (suc zero)) (W ∷ [])

        Δ₀-closedFo : Δ₀ closedFo
        Δ₀-closedFo = Δ₀-sepAt (Δ₀-closedAtˢ zero (suc zero)) (W ∷ [])

        closedFo-reading : (y : S) → ((y ∷ []) ⊨ closedFo) ≡ closedΔ W y
        closedFo-reading y =
          sepAt-reading (closedAtˢ zero (suc zero)) (W ∷ []) y

        opaque
          sift : S → S
          sift F = separateOf sep F closedFo

          sift-spec : (F y : S) → (y ∈ˢ sift F) ≡ ((y ∈ˢ F) ⊓ closedΔ W y)
          sift-spec F y =
            separateOf-spec sep F closedFo y
            ∙ cong ((y ∈ˢ F) ⊓_) (closedFo-reading y)

        -- The Collection class, with two free slots. Slot 0 is the candidate
        -- family, slot 1 the subname it has to contain, and the weight
        -- carrier is again a constant. Collection is the only axiom in the
        -- profile that reads a Formula S 2 (OrdinaryProfile.agda:95-101).

        familyFo : Formula S 3
        familyFo = closedAtˢ zero (suc (suc zero)) ∧̇ (var (suc zero) ∈̇ var zero)

        familyAt : Formula S 2
        familyAt = colAt familyFo (W ∷ [])

        Δ₀-familyAt : Δ₀ familyAt
        Δ₀-familyAt = Δ₀-inst (atCon₂ (W ∷ [])) (checkΔ₀ familyFo tt)

        familyAt-reading : (y x : S)
                         → ((y ∷ x ∷ []) ⊨ familyAt)
                         ≡ (closedΔ W y ⊓ (x ∈ˢ y))
        familyAt-reading y x = colAt-reading familyFo (W ∷ []) y x

        -- The union of the sifted family. Every member of it lies in some
        -- genuinely closed member of F, which is the only fact the closure
        -- proof below uses.

        gather : S → S
        gather F = ⋃ᴳ (sift F)

        gather-in : (F C z : S) → ⟨ C ∈ˢ F ⟩ → ⟨ closedΔ W C ⟩ → ⟨ z ∈ˢ C ⟩
                  → ⟨ z ∈ˢ gather F ⟩
        gather-in F C z hCF cl hz =
          ⋃ᴳ-in (sift F) C z (subst ⟨_⟩ (sym (sift-spec F C)) (hCF , cl)) hz

        -- The membership in the sifted family is kept, not just the closure
        -- clause: a consumer that has to put a NEW point into the union needs
        -- the same witnessing set again, and rebuilding it from the closure
        -- clause alone is impossible.
        gather-out : (F z : S) → ⟨ z ∈ˢ gather F ⟩
                   → ∥ Σ[ C ∈ S ]
                        (⟨ C ∈ˢ sift F ⟩ × ⟨ closedΔ W C ⟩ × ⟨ z ∈ˢ C ⟩) ∥₁
        gather-out F z m = PT.map
          (λ { (C , hC , hz) →
                 C , hC , snd (subst ⟨_⟩ (sift-spec F C) hC) , hz })
          (subst ⟨_⟩ (⋃ᴳ-spec (sift F) z) m)

        hereditary : (n : S) → ⟨ IsName n ⟩ → ∥ ClosedFamily n ∥₁
        hereditary =
          WFI.induction child-wf
            {P = λ n → ⟨ IsName n ⟩ → ∥ ClosedFamily n ∥₁} step
          where
            step : (n : S)
                 → ((x : S) → Child x n → ⟨ IsName x ⟩ → ∥ ClosedFamily x ∥₁)
                 → ⟨ IsName n ⟩ → ∥ ClosedFamily n ∥₁
            step n IH hn = PT.rec PT.squash₁ assemble
              (coll (support n) familyAt premise)
              where
                -- Collection's premise. For each subname of n there IS a
                -- closed family containing it, by the induction hypothesis;
                -- the support gives both the edge and the name proof the
                -- hypothesis needs, and Track B's support-out is
                -- unconditional so no well-formedness has to be rechecked.
                premise : ⟨ ⋀ S (λ x → (x ∈ˢ support n) ⇒
                            (⋁ S (λ y → (y ∷ x ∷ []) ⊨ familyAt))) ⟩
                premise x hx = PT.map
                  (λ cf → ClosedFamily.C cf
                        , subst ⟨_⟩ (sym (familyAt-reading (ClosedFamily.C cf) x))
                            (ClosedFamily.coded cf , ClosedFamily.contains cf))
                  (IH x (support-out n x hx) (support-valid n hn x hx))

                assemble : Σ[ F ∈ S ] ⟨ ⋀ S (λ x → (x ∈ˢ support n) ⇒
                             (⋁ S (λ y → (y ∈ˢ F) ⊓ ((y ∷ x ∷ []) ⊨ familyAt)))) ⟩
                         → ∥ ClosedFamily n ∥₁
                assemble (F , bound) =
                  ∣ closedFamily E (adjoin-new (gather F) n) codedE ∣₁
                  where
                    E : S
                    E = adjoin (gather F) n

                    -- Every subname of n is inside the gathered union. This
                    -- is where Collection's output is spent and the only
                    -- place it is used.
                    inGather : (x : S) → ⟨ x ∈ˢ support n ⟩
                             → ⟨ x ∈ˢ gather F ⟩
                    inGather x hx = PT.rec (snd (x ∈ˢ gather F))
                      (λ { (y , hyF , sat) →
                             gather-in F y x hyF
                               (fst (subst ⟨_⟩ (familyAt-reading y x) sat))
                               (snd (subst ⟨_⟩ (familyAt-reading y x) sat)) })
                      (bound x hx)

                    inE : (x : S) → ⟨ x ∈ˢ support n ⟩ → ⟨ x ∈ˢ E ⟩
                    inE x hx = adjoin-old (gather F) n x (inGather x hx)

                    codedE : ⟨ closedΔ W E ⟩
                    codedE m hm e he =
                      PT.rec (snd goal) branch (adjoin-out (gather F) n m hm)
                      where
                        goal : Ω
                        goal = ⋁ S (λ x → (x ∈ˢ E) ⊓
                                 (⋁ S (λ b → (b ∈ˢ W) ⊓ isKPairΔ e x b)))

                        -- An old member. Its own closed family decomposes e
                        -- and hands back a first coordinate inside that
                        -- family, hence inside the union, hence inside E.
                        fromOld : ⟨ m ∈ˢ gather F ⟩ → ⟨ goal ⟩
                        fromOld hmU = PT.rec (snd goal)
                          (λ { (C , hCsift , cl , hmC) → PT.map
                                 (λ { (x , hxC , wts) →
                                        x
                                      , adjoin-old (gather F) n x
                                          (⋃ᴳ-in (sift F) C x hCsift hxC)
                                      , wts })
                                 (cl m hmC e he) })
                          (gather-out F m hmU)

                        -- The new member. Here the shape clause of the name
                        -- predicate is the whole content: it produces the
                        -- decomposition of e, the decomposition produces the
                        -- edge, the edge lands in the support, and the
                        -- support is inside the union by inGather.
                        fromNew : m ≡ n → ⟨ goal ⟩
                        fromNew p = PT.map decompose
                          (name-shape n hn e (subst (λ u → ⟨ e ∈ˢ u ⟩) p he))
                          where
                            decompose : Σ[ x ∈ S ] Σ[ b ∈ S ]
                                          (e ≡ entry x b) × ⟨ b ∈ˢ W ⟩
                                      → Σ[ x ∈ S ] (⟨ x ∈ˢ E ⟩
                                      × ⟨ ⋁ S (λ b → (b ∈ˢ W)
                                            ⊓ isKPairΔ e x b) ⟩)
                            decompose (x , b , eq , hb) =
                              x
                              , inE x (support-in n hn x
                                  (child-entry x b n
                                    (subst (λ u → ⟨ u ∈ˢ n ⟩) eq
                                      (subst (λ u → ⟨ e ∈ˢ u ⟩) p he))))
                              , ∣ b , hb
                                , subst (λ u → ⟨ isKPairΔ u x b ⟩) (sym eq)
                                    (entry-isKPair x b) ∣₁

                        branch : (⟨ m ∈ˢ gather F ⟩ ⊎ (m ≡ n)) → ⟨ goal ⟩
                        branch (inl h) = fromOld h
                        branch (inr p) = fromNew p

        -- The second half of adequacy, and the reason this track needs
        -- Collection at all.

        name-complete : (t : S) → ⟨ IsName t ⟩ → ⟨ nameΔ W t ⟩
        name-complete t ht = PT.map
          (λ cf → ClosedFamily.C cf
                , ClosedFamily.contains cf , ClosedFamily.coded cf)
          (hereditary t ht)

        -- THE RECOGNIZER IS ADEQUATE. A path in Ω, so the two endpoints are
        -- written out: lesson 1 of the preamble says that leaving them to
        -- unification fixes the carrier half of each and blocks the isProp
        -- half.

        name-adequate : (t : S)
                      → ((t ∷ W ∷ []) ⊨ nameAtˢ zero (suc zero)) ≡ IsName t
        name-adequate t = ⇔toPath {P = nameΔ W t} {Q = IsName t}
          (name-sound t) (name-complete t)

-- ---------------------------------------------------------------------
-- The instantiation against Tracks A and B
-- ---------------------------------------------------------------------

-- A check, not part of the mathematics. Every parameter above is discharged
-- from Track A's kernel and Track B's support, and the application is
-- typechecked, so the correspondence between three files is machine-verified
-- rather than read off by eye. Track B's own Instantiate module is reused
-- wholesale: taking its K and BG rather than rebuilding them guarantees that
-- the entry, the child relation and the name predicate here are the same
-- objects, not merely ones with the same definitions.
--
-- The accessibility datum appears HERE and nowhere above, exactly as on
-- Track B: it is needed to build the kernel, not to build a closed family.

module Instantiate (𝔊 : Families) (acc∈ : Accessibility) (W : S) where

  open Families 𝔊 using ( sets; hasCollect )
  open Sets sets using ( core; hasSeparation )

  module BI = NS.Instantiate sets acc∈ W
  module K  = BI.K
  module BG = BI.BG

  module C = Space W
    K.entry K.entry-inj K.entry-isKPair
    K.Child (λ x b n h → ∣ b , h ∣₁) (λ x n e → e)
    K.child-wf
    K.IsName K.name-shape K.name-intro

  module CR = C.Recognize core
  module CX = CR.Intersect hasSeparation
  module CO = CR.Ops BG.⋃ᴳ BG.⋃ᴳ-spec
                     K.pairOf K.pairOf-left K.pairOf-right K.∈-pairOf
  module CC = CO.Collect hasSeparation hasCollect
                         BG.support BG.support-in BG.support-out BG.support-valid

  -- The four deliverables of section 1.6, at the top of the instance.

  hereditary : (n : S) → ⟨ K.IsName n ⟩ → ∥ CR.ClosedFamily n ∥₁
  hereditary = CC.hereditary

  name-adequate : (t : S)
                → ((t ∷ W ∷ []) ⊨ nameAtˢ zero (suc zero)) ≡ K.IsName t
  name-adequate = CC.name-adequate

  common : (C D : S) → ⟨ closedΔ W C ⟩ → ⟨ closedΔ W D ⟩
         → Σ[ E ∈ S ] (⟨ E ⊆ˢ C ⟩ × ⟨ E ⊆ˢ D ⟩ × ⟨ closedΔ W E ⟩)
  common = CX.common

  nameBound : PowerSet → (C : S) → S
  nameBound = CO.nameBound

  nameBound-contains : (pow : PowerSet) (C n : S) → ⟨ K.IsName n ⟩
                     → ((x : S) → K.Child x n → ⟨ x ∈ˢ C ⟩)
                     → ⟨ n ∈ˢ nameBound pow C ⟩
  nameBound-contains = CO.nameBound-contains

  -- The union closure, added for K4 Tracks E and I. Only the ⋃ᴳ form needs
  -- an instance: closed-cover, closed-family and closed-union are at the
  -- top level of this module and cost no hypothesis at all.

  closed-⋃ᴳ : (G : S) → ((C : S) → ⟨ C ∈ˢ G ⟩ → ⟨ closedΔ W C ⟩)
            → ⟨ closedΔ W (BG.⋃ᴳ G) ⟩
  closed-⋃ᴳ = CO.closed-⋃ᴳ

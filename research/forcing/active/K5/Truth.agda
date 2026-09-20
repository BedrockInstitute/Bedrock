{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track G: GENERIC TRUTH.
--
-- What this module is for. Track A embedded an abstract coded poset into an
-- abstract Boolean algebra and sealed p ⊩ᴮ b = i p ≤ᴮ b. Track B proved the
-- ten clauses and uniqueness. Track D built, out of a subset G of the
-- conditions, the subset Uof G of the algebra that G determines, and proved
-- it a proper, upward closed, directed, inhabited filter which REFLECTS G and
-- which, under LEM ℓ and genericity, DECIDES every element. This file closes
-- the loop: it proves that satisfaction in the Boolean-name structure read at
-- Uof G is exactly membership of the value in Uof G, at every fixed formula
-- and every fixed environment. That is the truth lemma.
--
-- THE ONE SENTENCE THE WHOLE FILE IS ORGANISED AROUND. Under decision D3 the
-- right hand side of the architecture's truth lemma,
-- ⋁ Cond (λ p → (p ∈ᴾ G) ⊓ (p ⊩ φ [ ν ])), is literally Uof G (val φ ν),
-- because p ⊩ φ [ ν ] is p ⊩ᴮ val φ ν and Uof G b is
-- ⋁ Cond (λ p → (p ∈ᴾ G) ⊓ (p ⊩ᴮ b)). So the truth lemma says
--
--     sat φ ν ≡ Uof (val φ ν),
--
-- "φ holds at the generic exactly when its value lies in the generic", and
-- the induction has ten cases, of which six are Boolean algebra at the filter
-- and four are the quantifiers. Both forms are shipped: truth-Uof is the
-- working form and truth is the architecture's printed form.
--
-- NO MAXIMUM-PRINCIPLE WITNESS, AND THE PLACE THAT MATTERS. The existential
-- step never names a name whose value attains the supremum. It takes the
-- coded value set that Admits already carries (K4/ValueSets.agda:291-295),
-- separates out of the carrier the conditions lying inside SOME member of it
-- (Track C's witnessAt), meets that coded dense set at the generic, and then
-- eliminates the resulting membership with attained-elim
-- (K4/ValueSets.agda:314-318), whose target is an Ω. No index is ever
-- extracted from a truncation, so no choice of any kind is spent, and the
-- conclusion ⋁ Nameᴮ (λ σ → Uof (f σ)) is itself an Ω, which is why the
-- elimination is legitimate. That lemma is join-prime below and it is the
-- whole of this track's mathematics; everything else is bookkeeping.
--
-- Fullness, FullnessAt, MaximumPrinciple, MaximumPrincipleContract,
-- Refinement, MixtureSupply, Mixture, WitnessSpec, ValueCover,
-- ElementPrinciple and AdequateDomain appear nowhere in this file, in no
-- position, hypothesis included. K4 proved more than the roadmap asked: not
-- one field of CodedComplete is projected anywhere in K4/Witnesses.agda, so
-- completeness is not merely insufficient for the principle, it is not used
-- by either theorem the principle generalizes (K4/Witnesses.agda:941-949).
--
-- HOW THE OTHER TRACKS ENTER. Flat, as module parameters typed from the
-- producing export, which is ledger clause L10 and preamble rule 2 in its
-- tightest form: a projection out of a module parameter is a variable and a
-- variable cannot unfold, so no coded operation appears at any depth in any
-- type here and preamble rule 2b cannot reach this file. Track A is the one
-- exception: K5.Frame is landed, reported and light (286 MB), so it is
-- IMPORTED rather than transcribed, which removes eleven parameters and any
-- possibility of drift against the record that owns the frame.
--
-- THREE HEAVY MODULE APPLICATIONS, and rule 10's budget is by applications
-- and not by lines: K5.Frame.Poset.Forcing, K4.Implication and
-- K4.ValueSets.Core. Every argument of all three is a variable.
--
-- RECORD OWNERSHIP (rule 9, ledger clause L12). This file declares NO record.
-- ForcingBase is Track A's, ForcingClauses is Track B's, Admits is K4's
-- (K4/ValueSets.agda:291), ForcingNotion and isFilter are K2's. Supply below
-- is a RECURSIVE DEFINITION over formulas and not a record; it names no new
-- structure, it only says which Admits records the induction consumes.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import CodedVocabulary
import K4.Algebra
import K4.Implication
import K4.ValueSets
import K5.Frame

module K5.Truth {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open import FOL.Syntax
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( Unit* ; tt* )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

-- The scope contract of K4/Implication.agda:64-77, as Tracks A, B and D read
-- it: K4.Algebra supplies the point vocabulary and the order, K4.Implication
-- supplies the Boolean theory and re-exports the Lattice and Complement
-- fields, and neither re-exports the other's names.

open K4.Algebra 𝒮
  using ( Pt; isSetPt; Pt≡; _≤ᴮ_; ≤ᴮ-refl; ⊆ˢ-trans
        ; Lattice; Complement; CodedComplete )

open K5.Frame 𝒮 using ( denseBelowΔ )
open CodedVocabulary 𝒮 using ( denseΔ )

-- The compiler reads parameter free formulas, Compile.agda:499-500.

Src : ℕ → Type ℓ
Src k = Formula (⊥* {ℓ}) k

--------------------------------------------------------------------------------
-- The poset layer
--------------------------------------------------------------------------------

module Poset (carrier order : S) where

  open K5.Frame.Poset 𝒮 carrier order

  module Core
    (ext   : OrdinaryProfile.Extensionality 𝒮)
    (paths : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
    (B : S) (L : Lattice B) (Cm : Complement B L) (Kc : CodedComplete B L)
    (fb : ForcingBase B L Cm)
    (IsNameᴮ : S → Ω)
    where

    -- Ledger clause L9 forbids the local names `i` and `below`, so the two
    -- record fields are renamed on the way in, exactly as Track C renames
    -- them (K5/Dense.agda:122). Every other field keeps Track A's name.

    open ForcingBase fb renaming ( i to iᶜ ; below to belowᶜ )
    open K5.Frame.Poset.Forcing 𝒮 carrier order ext paths B L Cm Kc fb
    open K4.Implication 𝒮 ext paths B L Cm
    open K4.ValueSets.Core 𝒮 ext paths B L Kc
      using ( Admits ; attained-mem ; attained-elim )

    -- A name is a code carrying its recognition proof, Compile.agda:502-503
    -- read through Fib P = Σ[ x ∈ S ] ⟨ P x ⟩ (K4/ValueSets.agda:166-167).
    -- Written out rather than imported as Fib, exactly as Track B writes it,
    -- so that a consumer's val at Vec (Fib IsName) k fits unchanged: Fib is a
    -- definition and not a record, so this is not a second copy.

    Nameᴮ : Type ℓ
    Nameᴮ = Σ[ x ∈ S ] ⟨ IsNameᴮ x ⟩

    Envᴮ : ℕ → Type ℓ
    Envᴮ k = Vec Nameᴮ k

    -- One Boolean fact this track needs and K4 does not have: in a Boolean
    -- algebra, a lower bound of a join that misses one joinand is below the
    -- other. It is De Morgan and ≤-both-⊥ and nothing else, and it is the
    -- step that makes the disjunction and implication cases of the truth
    -- lemma free of any density argument at the poset.

    ⊔-cancel : (u v w : Pt B) → ⟨ w ≤ᴮ (u ⊔ᴮ v) ⟩ → ⟨ w ≤ᴮ (¬ᴮ u) ⟩ → ⟨ w ≤ᴮ v ⟩
    ⊔-cancel u v w h₁ h₂ = ⊥-as-≤ w v (≤-both-⊥ z (u ⊔ᴮ v) za zb)
      where
        z : Pt B
        z = w ⊓ᴮ (¬ᴮ v)

        za : ⟨ z ≤ᴮ (u ⊔ᴮ v) ⟩
        za = ⊆ˢ-trans (⊓-lb₁ w (¬ᴮ v)) h₁

        zb : ⟨ z ≤ᴮ (¬ᴮ (u ⊔ᴮ v)) ⟩
        zb = subst (λ t → ⟨ z ≤ᴮ t ⟩) (sym (De-Morgan-⊔ u v))
               (⊓-glb (¬ᴮ u) (¬ᴮ v) z
                 (⊆ˢ-trans (⊓-lb₁ w (¬ᴮ v)) h₂) (⊓-lb₂ w (¬ᴮ v)))

    -- DECISION D1, as the two entailments Track C states and consumes
    -- (K5/Dense.agda:579-584), transcribed here character for character so
    -- that a drift fails in the seam probe. The members of a coded value set
    -- are the CODES of algebra elements, so the witness set's reading speaks
    -- x ∈ˢ fst b while forcing speaks the frame's belowᶜ; at an abstract
    -- ForcingBase neither direction is derivable, because the record relates
    -- belowᶜ to the ORDER and never to the code. At the coded completion both
    -- are the identity under below := fst, verified at exit 0 by Track A in
    -- K5/ProbeD1.agda.
    --
    -- THIS IS WHY D1 IS LOAD BEARING FOR TRACK G AND NOT MERELY ECONOMICAL.
    -- Architecture part 6.2 justifies below := fst by the three K3 hypotheses
    -- it discharges for free. The existential step of the truth lemma needs
    -- it as MATHEMATICS: without it the coded witness set reads nothing about
    -- forcing and there is no dense set to meet.

    CodeOfBelow : Type ℓ
    CodeOfBelow = (b : Pt B) (x : S) → ⟨ x ∈ˢ belowᶜ b ⟩ → ⟨ x ∈ˢ fst b ⟩

    BelowOfCode : Type ℓ
    BelowOfCode = (b : Pt B) (x : S) → ⟨ x ∈ˢ fst b ⟩ → ⟨ x ∈ˢ belowᶜ b ⟩

------------------------------------------------------------------------------
-- The compiler surface, flat
------------------------------------------------------------------------------

    -- val and its fourteen laws enter FLAT, typed verbatim from
    -- Compile.agda:1318-1357 through Track B's transcription of them at
    -- K5/Clauses.agda, never by applying K4.Compile.Core, whose telescope is
    -- twenty two entries (Compile.agda:318-353). Preamble rule 12: a law that
    -- applies a PARAMETER to a formula can have that formula inferred.
    --
    -- Three further parameters are Track B's own exports and are typed
    -- character for character from K5/Clauses.agda: the sealed formula
    -- relation, its spec, and the ONE paid clause this track consumes.
    --
    -- WHAT IS NOT TAKEN, and this is a measured correction to the
    -- architecture's part 1.9. The architecture routes the universal step
    -- through ⊩-dichotomy and ⊩-¬. Neither is needed here and neither is a
    -- parameter: the dichotomy is consumed in the form Track D already
    -- packages it, Uof-ultra, and the negation clause is not consumed at all
    -- because the universal step works with ¬ᴮ in the ALGEBRA and never with
    -- a condition quantifier.
    --
    -- NONE OF TRACK B'S FIVE PAID CLAUSES IS CONSUMED. An earlier draft of
    -- this file took ⊩-∃→ and transported its abstract DenseBelow onto the
    -- coded witness set by hand; Track C then landed witnessAt-denseBelow
    -- (K5/Dense.agda:626-672), which proves the density ON THE CODED SET
    -- directly from ⊩ᴮ-extend and the least-upper-bound half of the join, so
    -- the transport and the paid clause both disappear. ⊩-∨→, ⊩-⇒←, ⊩-∃→,
    -- ⊩-∃∈→ and ⊩-dichotomy are all absent from this file. What is taken from
    -- Track B is the sealed formula relation and its spec, both free, and
    -- they are taken only so that the headline theorem can be printed in the
    -- architecture's own ⊩-shaped form.

    module Value
      (eqᴬ memᴬ : S → S → Pt B)
      (val : ∀ {k} → Src k → Envᴮ k → Pt B)
      (law-∈ : ∀ {k} (a b : Fin k) (ν : Envᴮ k)
             → val (var a ∈̇ var b) ν ≡ memᴬ (fst (lookup a ν)) (fst (lookup b ν)))
      (law-≐ : ∀ {k} (a b : Fin k) (ν : Envᴮ k)
             → val (var a ≐ var b) ν ≡ eqᴬ (fst (lookup a ν)) (fst (lookup b ν)))
      (law-∧ : ∀ {k} (φ ψ : Src k) (ν : Envᴮ k)
             → val (φ ∧̇ ψ) ν ≡ (val φ ν ⊓ᴮ val ψ ν))
      (law-∨ : ∀ {k} (φ ψ : Src k) (ν : Envᴮ k)
             → val (φ ∨̇ ψ) ν ≡ (val φ ν ⊔ᴮ val ψ ν))
      (law-⇒ : ∀ {k} (φ ψ : Src k) (ν : Envᴮ k)
             → val (φ ⇒̇ ψ) ν ≡ (val φ ν ⇒ᴮ val ψ ν))
      (law-⊥ : ∀ {k} (ν : Envᴮ k) → val {k} ⊥̇ ν ≡ ⊥ᴮ)
      (law-∃-ub   : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k) (σ : Nameᴮ)
                  → ⟨ val φ (σ ∷ ν) ≤ᴮ val (∃̇ φ) ν ⟩)
      (law-∃-lub  : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k) (c : Pt B)
                  → ((σ : Nameᴮ) → ⟨ val φ (σ ∷ ν) ≤ᴮ c ⟩)
                  → ⟨ val (∃̇ φ) ν ≤ᴮ c ⟩)
      (law-∀-lb   : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k) (σ : Nameᴮ)
                  → ⟨ val (∀̇ φ) ν ≤ᴮ val φ (σ ∷ ν) ⟩)
      (law-∀-glb  : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k) (c : Pt B)
                  → ((σ : Nameᴮ) → ⟨ c ≤ᴮ val φ (σ ∷ ν) ⟩)
                  → ⟨ c ≤ᴮ val (∀̇ φ) ν ⟩)
      (law-∃∈-ub  : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Envᴮ k) (σ : Nameᴮ)
                  → ⟨ (memᴬ (fst σ) (fst (lookup j ν)) ⊓ᴮ val φ (σ ∷ ν))
                      ≤ᴮ val (∃̇∈ (var j) φ) ν ⟩)
      (law-∃∈-lub : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Envᴮ k) (c : Pt B)
                  → ((σ : Nameᴮ)
                     → ⟨ (memᴬ (fst σ) (fst (lookup j ν)) ⊓ᴮ val φ (σ ∷ ν))
                         ≤ᴮ c ⟩)
                  → ⟨ val (∃̇∈ (var j) φ) ν ≤ᴮ c ⟩)
      (law-∀∈-lb  : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Envᴮ k) (σ : Nameᴮ)
                  → ⟨ val (∀̇∈ (var j) φ) ν
                      ≤ᴮ (memᴬ (fst σ) (fst (lookup j ν)) ⇒ᴮ val φ (σ ∷ ν)) ⟩)
      (law-∀∈-glb : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Envᴮ k) (c : Pt B)
                  → ((σ : Nameᴮ) → ⟨ c ≤ᴮ (memᴬ (fst σ) (fst (lookup j ν))
                                           ⇒ᴮ val φ (σ ∷ ν)) ⟩)
                  → ⟨ c ≤ᴮ val (∀̇∈ (var j) φ) ν ⟩)
      -- Track B, K5/Clauses.agda:571-575 and :461-467.
      (_⊩_[_] : ∀ {k} → Cond → Src k → Envᴮ k → Ω)
      (⊩-spec : ∀ {k} (p : Cond) (φ : Src k) (ν : Envᴮ k)
              → (p ⊩ φ [ ν ]) ≡ (p ⊩ᴮ val φ ν))
      where

      -- Negation is implication into falsum (src/FOL/Syntax.lagda.md:108-109)
      -- and val-⇒ emits the material implication (¬ᴮ u) ⊔ᴮ v
      -- (K4/Implication.agda:309-310), so val (¬̇ φ) ν is ¬ᴮ (val φ ν) ⊔ᴮ ⊥ᴮ
      -- and the ⊔-⊥ step (K4/Implication.agda:133) is what turns it into the
      -- pseudocomplement. A track that skips that step writes a well typed
      -- statement about a different element. This is Track B's val-¬
      -- (K5/Clauses.agda) rederived in three lines rather than taken as a
      -- fifteenth parameter; the two are the same path.

      val-¬ : ∀ {k} (φ : Src k) (ν : Envᴮ k) → val (¬̇ φ) ν ≡ (¬ᴮ (val φ ν))
      val-¬ φ ν = law-⇒ φ ⊥̇ ν
                ∙ cong (λ z → (¬ᴮ (val φ ν)) ⊔ᴮ z) (law-⊥ ν)
                ∙ ⊔-⊥ (¬ᴮ (val φ ν))

--------------------------------------------------------------------------------
-- The witness supply, one Admits per QUANTIFIER node
--------------------------------------------------------------------------------

      -- WHAT THE INDUCTION CONSUMES, and this is a measured correction to
      -- architecture part 1.9, which prints "one per ∃ node of φ" and whose
      -- printed signature does not typecheck (it writes
      -- (σ : Nameᴮ) → Admits (λ τ → val φ (τ ∷ ν)) at φ : Src k, where
      -- val φ (τ ∷ ν) is ill typed and the σ is unused).
      --
      -- The existential nodes need a coded set of the values of the body,
      -- which is exactly Admits of that family. THE UNIVERSAL NODES NEED ONE
      -- TOO, at the COMPLEMENTED family, and this is not a convenience. The
      -- forward direction of the universal case says: if every instance lies
      -- in the generic then so does the meet. Dually that is
      --   ⋀ b σ ∉ U  ⟹  ¬ ⋀ b σ ∈ U  ⟹  ⋁ ¬ b σ ∈ U  ⟹  some ¬ b σ ∈ U,
      -- and the last step is join-primeness at the family σ ↦ ¬ᴮ (b σ). A
      -- generic ultrafilter is join-prime only at a family whose join is
      -- CODED, because the coded set is what witnessAt separates against and
      -- what generic-meets-denseBelow meets. So the meet-closure of the
      -- filter costs exactly one Admits at the complemented family, and no
      -- textbook route avoids it: Bell's own proof of the universal case is
      -- de Morgan followed by the existential case.
      --
      -- It is NOT derivable from the plain family's Admits inside this
      -- telescope: the complemented value set would be the image of the plain
      -- one under ¬ᴮ, which needs Collection or an internal image former, and
      -- Core has neither. At the coded completion it is one Separation over B
      -- against a Δ₀ formula, because neg-mem reads membership in the
      -- complement as the poset clause "no refinement of z lies in u"
      -- (CodedCompletion.agda:300-301, :701-708); that Separation is Track I's
      -- or K8's and is named in REPORT-G, not assumed here.
      --
      -- Supply is stated PER NODE and not as four global families, because
      -- exit item X5 asks for the Admits to be a visible hypothesis of the
      -- theorem and a global family is a strictly stronger assumption. The
      -- environment is quantified inside each node because the induction
      -- generalises ν.

      Supply : ∀ {k} → Src k → Type (ℓ-suc ℓ)
      Supply (t ∈̇ u) = Unit*
      Supply (t ≐ u) = Unit*
      Supply ⊥̇ = Unit*
      Supply (φ ∧̇ ψ) = Supply φ × Supply ψ
      Supply (φ ∨̇ ψ) = Supply φ × Supply ψ
      Supply (φ ⇒̇ ψ) = Supply φ × Supply ψ
      Supply {k} (∃̇ φ) =
        ((ν : Envᴮ k) → Admits (λ σ → val φ (σ ∷ ν))) × Supply φ
      Supply {k} (∀̇ φ) =
        ((ν : Envᴮ k) → Admits (λ σ → ¬ᴮ (val φ (σ ∷ ν)))) × Supply φ
      Supply {k} (∃̇∈ (var j) φ) =
        ((ν : Envᴮ k) → Admits (λ σ → (memᴬ (fst σ) (fst (lookup j ν))
                                       ⊓ᴮ val φ (σ ∷ ν))))
        × Supply φ
      Supply (∃̇∈ (con ()) φ)
      Supply {k} (∀̇∈ (var j) φ) =
        ((ν : Envᴮ k) → Admits (λ σ → ¬ᴮ (memᴬ (fst σ) (fst (lookup j ν))
                                            ⇒ᴮ val φ (σ ∷ ν))))
        × Supply φ
      Supply (∀̇∈ (con ()) φ)

--------------------------------------------------------------------------------
-- The generic, and the coded witness set
--------------------------------------------------------------------------------

      -- Track D's surface and Track C's witnessAt arrive as parameters, typed
      -- from K5/Generic.agda and from architecture part 1.6, because those
      -- tracks are written in parallel with this one. Ledger clause L10 in its
      -- intended use: a drift fails in the seam probe instead of passing
      -- silently.
      --
      -- G∈ is λ p → p ∈ᴾ G for G : FS.Sub at Track D's frameNotion
      -- (_∈ᴾ_ at ForcingNotion.agda:91-92, and p ∈ᴾ D is D p). It is taken as
      -- a Cond → Ω rather than as a Sub because Sub lives at Type (ℓ-suc ℓ)
      -- (ForcingNotion.agda:88-89) and nothing here may be pushed up a level;
      -- that is the type level tell of ledger clause L13.
      --
      -- meets is K2's genericity field taken FLAT and verbatim from
      -- CodedCompletion.agda:1073-1074, with Core's two abbreviations expanded
      -- (subsetOf d is d ⊆ˢ carrier at :995-996, denseᴵ is denseΔ carrier
      -- order at :1001-1002). isGeneric is not re-declared, and no weakening
      -- of it to antichains, maximal antichains or predense sets is offered:
      -- at an empty coded d, antichainᴵ d is vacuously true while denseᴵ d is
      -- false (:1001-1017), so an antichain-routed step would be satisfied by
      -- nothing.
      --
      -- Uof-ultra and meets-below take meets as an explicit argument so that
      -- the genericity dependency is machine visible in this file, and LEM ℓ
      -- as an explicit FIRST argument so that the classical ledger is too.
      --
      -- cob and boc ARE DECISION D1, and Track C states them as the two
      -- entailments rather than as the path belowᶜ b ≡ fst b so that each
      -- lemma carries only the direction it spends (K5/Dense.agda:571-584).
      -- witnessAt-force spends BelowOfCode and witnessAt-denseBelow spends
      -- CodeOfBelow; join-prime below spends both, once each.
      --
      -- meets-below is Track C's generic-meets-denseBelow with its isFilter
      -- argument applied. MEASURED CORRECTION TO ARCHITECTURE PART 1.6, and
      -- it is Track C's: that lemma is NOT built from coneOrApart. Meeting
      -- coneOrApart r at a filter containing r produces a filter member
      -- refining r, below which d is dense, but nothing puts the resulting
      -- member of d back inside the filter. The left disjunct has to BE d,
      -- and the set that works is Bell's own union memOrApart d p; Track C
      -- refuted the architecture's route mechanically at exit 42. Nothing in
      -- this file names either set: the enlargement is entirely inside Track
      -- C's lemma and only its statement crosses the seam.

      module Generic
        (G∈ : Cond → Ω)
        (meets : (d : S) → ⟨ d ⊆ˢ carrier ⟩ → ⟨ denseΔ carrier order d ⟩
               → ⟨ ⋁ Cond (λ q → (G∈ q) ⊓ (fst q ∈ˢ d)) ⟩)
        (Uof : Pt B → Ω)
        (Uof-of : (b : Pt B) → ⟨ ⋁ Cond (λ p → (G∈ p) ⊓ (p ⊩ᴮ b)) ⟩ → ⟨ Uof b ⟩)
        (Uof-to : (b : Pt B) → ⟨ Uof b ⟩ → ⟨ ⋁ Cond (λ p → (G∈ p) ⊓ (p ⊩ᴮ b)) ⟩)
        (Uof-up : (b c : Pt B) → ⟨ b ≤ᴮ c ⟩ → ⟨ Uof b ⟩ → ⟨ Uof c ⟩)
        (Uof-dir : (b c : Pt B) → ⟨ Uof b ⟩ → ⟨ Uof c ⟩
                 → ⟨ ⋁ (Pt B) (λ d → (Uof d) ⊓ ((d ≤ᴮ b) ⊓ (d ≤ᴮ c))) ⟩)
        (Uof-proper : ⟨ Uof ⊥ᴮ ⟩ → ⟨ ⊥ ⟩)
        (Uof-ultra : LEM ℓ
                   → ((d : S) → ⟨ d ⊆ˢ carrier ⟩ → ⟨ denseΔ carrier order d ⟩
                              → ⟨ ⋁ Cond (λ q → (G∈ q) ⊓ (fst q ∈ˢ d)) ⟩)
                   → (b : Pt B) → ⟨ (Uof b) ⊔ (Uof (¬ᴮ b)) ⟩)
        (cob : CodeOfBelow)
        (boc : BelowOfCode)
        (witnessAt : S → S)
        (witnessAt-sub : (V : S) → ⟨ witnessAt V ⊆ˢ carrier ⟩)
        (witnessAt-force : BelowOfCode → (V : S) → ⟨ V ⊆ˢ B ⟩ → (r : Cond)
                         → ⟨ fst r ∈ˢ witnessAt V ⟩
                         → ⟨ ⋁ (Pt B) (λ u → (fst u ∈ˢ V) ⊓ (r ⊩ᴮ u)) ⟩)
        (witnessAt-denseBelow :
            LEM ℓ → CodeOfBelow → (V : S) (b : Pt B)
          → ((v : Pt B) → ((u : Pt B) → ⟨ fst u ∈ˢ V ⟩ → ⟨ u ≤ᴮ v ⟩)
                        → ⟨ b ≤ᴮ v ⟩)
          → (p : Cond) → ⟨ iᶜ p ≤ᴮ b ⟩
          → ⟨ denseBelowΔ carrier order (fst p) (witnessAt V) ⟩)
        (meets-below : LEM ℓ
                     → ((d : S) → ⟨ d ⊆ˢ carrier ⟩ → ⟨ denseΔ carrier order d ⟩
                                → ⟨ ⋁ Cond (λ q → (G∈ q) ⊓ (fst q ∈ˢ d)) ⟩)
                     → (r : Cond) → ⟨ G∈ r ⟩
                     → (d : S) → ⟨ d ⊆ˢ carrier ⟩
                     → ⟨ denseBelowΔ carrier order (fst r) d ⟩
                     → ⟨ ⋁ Cond (λ q → (G∈ q) ⊓ (fst q ∈ˢ d)) ⟩)
        where

        Uof-in : (b : Pt B) (p : Cond) → ⟨ G∈ p ⟩ → ⟨ p ⊩ᴮ b ⟩ → ⟨ Uof b ⟩
        Uof-in b p hp h = Uof-of b ∣ p , hp , h ∣₁

--------------------------------------------------------------------------------
-- The six propositional cases, at the filter
--------------------------------------------------------------------------------

        -- Everything in this block is a fact about a proper directed upward
        -- closed subset of a Boolean algebra that decides every element. No
        -- poset vocabulary enters, no density argument is run, and the
        -- classical cost is exactly the ultrafilter clause, which is Track
        -- D's and is paid by meeting decideAt.

        Uof-⊓-in : (u v : Pt B) → ⟨ Uof u ⟩ → ⟨ Uof v ⟩ → ⟨ Uof (u ⊓ᴮ v) ⟩
        Uof-⊓-in u v hu hv = PT.rec (snd (Uof (u ⊓ᴮ v))) step (Uof-dir u v hu hv)
          where
            step : Σ[ d ∈ Pt B ] ⟨ (Uof d) ⊓ ((d ≤ᴮ u) ⊓ (d ≤ᴮ v)) ⟩
                 → ⟨ Uof (u ⊓ᴮ v) ⟩
            step (d , hd , h₁ , h₂) = Uof-up d (u ⊓ᴮ v) (⊓-glb u v d h₁ h₂) hd

        Uof-⊓-out₁ : (u v : Pt B) → ⟨ Uof (u ⊓ᴮ v) ⟩ → ⟨ Uof u ⟩
        Uof-⊓-out₁ u v = Uof-up (u ⊓ᴮ v) u (⊓-lb₁ u v)

        Uof-⊓-out₂ : (u v : Pt B) → ⟨ Uof (u ⊓ᴮ v) ⟩ → ⟨ Uof v ⟩
        Uof-⊓-out₂ u v = Uof-up (u ⊓ᴮ v) v (⊓-lb₂ u v)

        Uof-⊔-in₁ : (u v : Pt B) → ⟨ Uof u ⟩ → ⟨ Uof (u ⊔ᴮ v) ⟩
        Uof-⊔-in₁ u v = Uof-up u (u ⊔ᴮ v) (⊔-ub₁ u v)

        Uof-⊔-in₂ : (u v : Pt B) → ⟨ Uof v ⟩ → ⟨ Uof (u ⊔ᴮ v) ⟩
        Uof-⊔-in₂ u v = Uof-up v (u ⊔ᴮ v) (⊔-ub₂ u v)

        -- THE PRIME FILTER CLAUSE, AND IT IS NOT THE NAIVE DISJUNCTION
        -- CLAUSE. Track B's decisive negative control weakened at-∨← to the
        -- naive form and found the clause record still provable while
        -- UNIQUENESS FAILS (REPORT-B section 8, break B4); Track J
        -- independently refuted the naive clause at the three element V,
        -- where i t = ⊤ᴮ is below i a ⊔ᴮ i b while neither i a nor i b
        -- dominates it, and showed that separativity does not repair it. What
        -- is proved here is a statement about the FILTER and not about a
        -- condition: a generic ultrafilter containing a join contains one
        -- joinand. That is true at the three element V and it is not the
        -- clause those two refutations killed.

        Uof-⊔-out : LEM ℓ → (u v : Pt B)
                  → ⟨ Uof (u ⊔ᴮ v) ⟩ → ⟨ (Uof u) ⊔ (Uof v) ⟩
        Uof-⊔-out lem u v h =
          PT.rec (snd ((Uof u) ⊔ (Uof v))) pick (Uof-ultra lem meets u)
          where
            pick : (⟨ Uof u ⟩ ⊎ ⟨ Uof (¬ᴮ u) ⟩) → ⟨ (Uof u) ⊔ (Uof v) ⟩
            pick (inl x) = ∣ inl x ∣₁
            pick (inr y) =
              PT.map (λ { (d , hd , hdj , hdn) →
                          inr (Uof-up d v (⊔-cancel u v d hdj hdn) hd) })
                     (Uof-dir (u ⊔ᴮ v) (¬ᴮ u) h y)

        Uof-⇒-out : (u v : Pt B) → ⟨ Uof (u ⇒ᴮ v) ⟩ → ⟨ Uof u ⟩ → ⟨ Uof v ⟩
        Uof-⇒-out u v h hu = PT.rec (snd (Uof v)) step (Uof-dir (u ⇒ᴮ v) u h hu)
          where
            step : Σ[ d ∈ Pt B ] ⟨ (Uof d) ⊓ ((d ≤ᴮ (u ⇒ᴮ v)) ⊓ (d ≤ᴮ u)) ⟩
                 → ⟨ Uof v ⟩
            step (d , hd , h₁ , h₂) =
              Uof-up d v (⊆ˢ-trans (⊓-glb (u ⇒ᴮ v) u d h₁ h₂) (⇒ᴮ-mp u v)) hd

        Uof-⇒-in : LEM ℓ → (u v : Pt B)
                 → (⟨ Uof u ⟩ → ⟨ Uof v ⟩) → ⟨ Uof (u ⇒ᴮ v) ⟩
        Uof-⇒-in lem u v f =
          PT.rec (snd (Uof (u ⇒ᴮ v))) pick (Uof-ultra lem meets u)
          where
            pick : (⟨ Uof u ⟩ ⊎ ⟨ Uof (¬ᴮ u) ⟩) → ⟨ Uof (u ⇒ᴮ v) ⟩
            pick (inl x) = Uof-up v (u ⇒ᴮ v) (⊔-ub₂ (¬ᴮ u) v) (f x)
            pick (inr y) = Uof-up (¬ᴮ u) (u ⇒ᴮ v) (⊔-ub₁ (¬ᴮ u) v) y

        -- Nothing and its complement both lie in the filter. FREE, and the
        -- proof spends i-nonzero, through Uof-proper and Track A's ⊩ᴮ-⊥: at a
        -- DEGENERATE algebra, where ⊤ᴮ ≡ ⊥ᴮ, this is FALSE, and neither K4's
        -- three algebra records (K4/Algebra.agda:101, :132, :157) nor K2's
        -- carry a nontriviality field, so ForcingBase.i-nonzero is where the
        -- degenerate algebra is excluded.

        Uof-not-both : (b : Pt B) → ⟨ Uof b ⟩ → ⟨ Uof (¬ᴮ b) ⟩ → ⟨ ⊥ ⟩
        Uof-not-both b hb hn = PT.rec (snd ⊥) step (Uof-dir b (¬ᴮ b) hb hn)
          where
            step : Σ[ d ∈ Pt B ] ⟨ (Uof d) ⊓ ((d ≤ᴮ b) ⊓ (d ≤ᴮ (¬ᴮ b))) ⟩ → ⟨ ⊥ ⟩
            step (d , hd , h₁ , h₂) =
              Uof-proper (subst (λ z → ⟨ Uof z ⟩) (≤-both-⊥ d b h₁ h₂) hd)

--------------------------------------------------------------------------------
-- JOIN-PRIMENESS, the heart of the track
--------------------------------------------------------------------------------

        -- THE STATEMENT. If a coded family of algebra elements has a
        -- supremum, and the supremum lies in the generic, then SOME member of
        -- the family lies in the generic. The family is given by its
        -- universal property (preamble rule 7: a universal property in an
        -- internal order is internally expressible and a construction is
        -- not), and "coded" means exactly that K4's Admits record carries a
        -- ground set of its values.
        --
        -- THE ROUTE, AND WHERE A TEXTBOOK WOULD REACH FOR A WITNESS.
        --
        --  1. Uof-to hands over a condition p in G forcing E.
        --  2. Track C's witnessAt-denseBelow makes the CODED witness set
        --     dense below p, straight from ⊩ᴮ-extend and the LEAST UPPER
        --     BOUND half of the family's universal property. It is handed the
        --     bound at the value set through blub, which is the only place
        --     the index presentation of the family and its coded value set
        --     meet, and that meeting runs one way only: attained-mem turns an
        --     index into a member. This is the step that a maximum principle
        --     would have replaced. A textbook takes a NAME whose value is E
        --     and reads the witness off it; here no name attains anything and
        --     the coded set is the one Admits already carries.
        --  3. generic-meets-denseBelow meets it, giving q in G inside
        --     witnessAt V. Track C's route through Bell's memOrApart, not the
        --     architecture's refuted route through coneOrApart.
        --  4. witnessAt-force turns that membership into "q forces some
        --     member u of V", a ⋁ over Pt B.
        --  5. attained-elim turns u into an index σ, WITH TARGET AN Ω. The
        --     goal
        --     ⋁ Nameᴮ (λ σ → Uof (f σ)) is an Ω, so the elimination is legal
        --     and no index leaves the truncation. A variant of attained-elim
        --     returning an index would be host Choice and is forbidden by
        --     ledger clause L1; it is not used and it does not exist
        --     (K4/ValueSets.agda:310-313).
        --
        -- Admits is at Type (ℓ-suc ℓ) (K4/ValueSets.agda:291) and MAY NEVER
        -- INDEX A JOIN. It is taken as a hypothesis here and is never placed
        -- inside a ⋁ or a ⋀; every join in the proof is indexed by Nameᴮ,
        -- Cond, Pt B or S, each at Type ℓ. That is trap T-G2 and the check
        -- for it is join-prime-indexes-⋁ below.

        join-prime : LEM ℓ → (f : Nameᴮ → Pt B) (E : Pt B)
                   → ((σ : Nameᴮ) → ⟨ f σ ≤ᴮ E ⟩)
                   → ((c : Pt B) → ((σ : Nameᴮ) → ⟨ f σ ≤ᴮ c ⟩) → ⟨ E ≤ᴮ c ⟩)
                   → Admits f
                   → ⟨ Uof E ⟩ → ⟨ ⋁ Nameᴮ (λ σ → Uof (f σ)) ⟩
        join-prime lem f E ub lub Ad hE = PT.rec (snd goal) atP (Uof-to E hE)
          where
            goal : Ω
            goal = ⋁ Nameᴮ (λ σ → Uof (f σ))

            V : S
            V = Admits.values Ad

            hV : ⟨ V ⊆ˢ B ⟩
            hV = Admits.values-sub Ad

            att : (b : S) → (b ∈ˢ V) ≡ ⋁ Nameᴮ (λ σ → b ≈ˢ fst (f σ))
            att = Admits.attained Ad

            -- The family's universal property, read at the value SET rather
            -- than at the index. This is the only place the two presentations
            -- of the same join meet, and it goes one way only: every member
            -- of V is a value of the family, by attained-mem, and that is all
            -- Track C's bound hypothesis asks. Nothing here asks for an index
            -- given a member, which is the direction that would be choice.

            blub : (v : Pt B)
                 → ((u : Pt B) → ⟨ fst u ∈ˢ V ⟩ → ⟨ u ≤ᴮ v ⟩) → ⟨ E ≤ᴮ v ⟩
            blub v hv = lub v (λ σ → hv (f σ) (attained-mem f V att σ))

            -- Step five. A generic condition inside the witness set forces
            -- some member of V; attained-elim turns that member into an index
            -- of the family, IN AN Ω, and the goal is that Ω.

            atQ : Σ[ q ∈ Cond ] (⟨ G∈ q ⟩ × ⟨ fst q ∈ˢ witnessAt V ⟩) → ⟨ goal ⟩
            atQ (q , hqG , hqW) =
              PT.rec (snd goal) pick (witnessAt-force boc V hV q hqW)
              where
                pick : Σ[ u ∈ Pt B ] (⟨ fst u ∈ˢ V ⟩ × ⟨ q ⊩ᴮ u ⟩) → ⟨ goal ⟩
                pick (u , huV , hqu) =
                  attained-elim f V att (fst u) huV goal
                    (λ σ e → ∣ σ , Uof-in (f σ) q hqG
                                    (subst (λ z → ⟨ q ⊩ᴮ z ⟩) (Pt≡ e) hqu) ∣₁)

            atP : Σ[ p ∈ Cond ] (⟨ G∈ p ⟩ × ⟨ p ⊩ᴮ E ⟩) → ⟨ goal ⟩
            atP (p , hpG , hpE) =
              PT.rec (snd goal) atQ
                (meets-below lem meets p hpG (witnessAt V) (witnessAt-sub V)
                  (witnessAt-denseBelow lem cob V E blub p (⊩ᴮ-elim p E hpE)))

        -- MEASURED, and it is Track B's own finding at the clause level
        -- repeated one layer up (REPORT-B section 5.5): the upper bound ub is
        -- NOT consumed. join-prime uses only the least-upper-bound half of the
        -- family's universal property, through blub. ub is kept so that the
        -- signature still reads as a fact about the join and so that a caller
        -- supplying law-∃-ub and law-∃-lub passes them in the architecture's
        -- order.

        -- THE DUAL, and the universal case of the truth lemma is nothing but
        -- this. If every member of a coded family lies in the generic then so
        -- does the infimum. The proof is the ultrafilter clause followed by
        -- join-primeness at the COMPLEMENTED family: if the meet were out,
        -- its complement would be in, the complement is the join of the
        -- complements by de Morgan for a characterised meet, so some
        -- complement would be in, and that contradicts Uof-not-both.
        --
        -- Nothing here is a condition quantifier and nothing here is ⊩-¬. The
        -- architecture's route through ⊩-dichotomy and ⊩-¬ (part 1.9) is the
        -- route at the CONDITION; at the filter the same mathematics is two
        -- calls, and the dichotomy has already been paid once, inside
        -- Track D's Uof-ultra.

        meet-complete : LEM ℓ → (f : Nameᴮ → Pt B) (A : Pt B)
                      → ((σ : Nameᴮ) → ⟨ A ≤ᴮ f σ ⟩)
                      → ((c : Pt B) → ((σ : Nameᴮ) → ⟨ c ≤ᴮ f σ ⟩) → ⟨ c ≤ᴮ A ⟩)
                      → Admits (λ σ → ¬ᴮ (f σ))
                      → ((σ : Nameᴮ) → ⟨ Uof (f σ) ⟩) → ⟨ Uof A ⟩
        meet-complete lem f A lb glb Ad hall =
          PT.rec (snd (Uof A)) pick (Uof-ultra lem meets A)
          where
            ub' : (σ : Nameᴮ) → ⟨ (¬ᴮ (f σ)) ≤ᴮ (¬ᴮ A) ⟩
            ub' σ = ¬ᴮ-anti A (f σ) (lb σ)

            lub' : (c : Pt B) → ((σ : Nameᴮ) → ⟨ (¬ᴮ (f σ)) ≤ᴮ c ⟩)
                 → ⟨ (¬ᴮ A) ≤ᴮ c ⟩
            lub' c hc =
              subst (λ z → ⟨ (¬ᴮ A) ≤ᴮ z ⟩) (¬ᴮ-invol c) (¬ᴮ-anti (¬ᴮ c) A below-c)
              where
                below-c : ⟨ (¬ᴮ c) ≤ᴮ A ⟩
                below-c = glb (¬ᴮ c)
                  (λ σ → subst (λ z → ⟨ (¬ᴮ c) ≤ᴮ z ⟩) (¬ᴮ-invol (f σ))
                           (¬ᴮ-anti (¬ᴮ (f σ)) c (hc σ)))

            clash : Σ[ σ ∈ Nameᴮ ] ⟨ Uof (¬ᴮ (f σ)) ⟩ → ⟨ ⊥ ⟩
            clash (σ , h) = Uof-not-both (f σ) (hall σ) h

            pick : (⟨ Uof A ⟩ ⊎ ⟨ Uof (¬ᴮ A) ⟩) → ⟨ Uof A ⟩
            pick (inl x) = x
            pick (inr y) =
              Empty.rec* (PT.rec (snd ⊥) clash
                (join-prime lem (λ σ → ¬ᴮ (f σ)) (¬ᴮ A) ub' lub' Ad y))

        -- Trap T-G2, checked by the machine and not by inspection. The
        -- CONCLUSION of join-prime is an element of Ω and its carrier is at
        -- Type ℓ, so it may index a join; this declaration elaborates only
        -- because that is so (⋁ takes a Type ℓ index, Base/Truth.lagda.md:72).
        -- The corresponding declaration with Supply φ or Admits f in the
        -- index slot does not elaborate, and the deliberate break is reported
        -- in REPORT-G.

        join-prime-indexes-⋁ : (f : Nameᴮ → Pt B) → Ω
        join-prime-indexes-⋁ f =
          ⋁ ⟨ ⋁ Nameᴮ (λ σ → Uof (f σ)) ⟩ (λ _ → ⊥)

--------------------------------------------------------------------------------
-- Truth at the generic
--------------------------------------------------------------------------------

        -- The extension structure's two relations and its satisfaction enter
        -- flat, typed from src/FOL/Semantics.lagda.md:113-123 read at
        -- 𝒮ᴮ[ Uof G ], whose carrier is Nameᴮ and whose _≈ˢ_ and _∈ˢ_ are the
        -- two fields Track F fills from K3's value relation at (B, ≤ᴮ, Uof G)
        -- (architecture part 1.8). Taking satisfaction as a parameter with
        -- its ten defining equations is the same device Track B used for val
        -- and its fourteen laws; at Track F's structure every one of the ten
        -- is refl, and the seam probe is what checks that.
        --
        -- THE TWO ATOMIC BRIDGES ARE HYPOTHESES, AND THE ARCHITECTURE'S PART
        -- 1.9 DOES NOT LIST THEM. They say that the extension structure's
        -- membership and equality at a name pair are membership of the
        -- compiler's atomic value in the generic. They are not provable
        -- inside this telescope and this file does not pretend otherwise:
        -- there is no name recursion here, K3's value relation is built by a
        -- pair recursion (Valuation.agda:285-300) and K4's atomic values by a
        -- host recursion over the support, and relating the two is an
        -- induction on names. That induction is exactly join-primeness at the
        -- coded family of entry weights, so the route is the one this file
        -- already contains; the missing input is an Admits for that family,
        -- which is K4's atomic graph obstruction O1 (K4/AtomicGraph.agda:411,
        -- :719-720, TableSupply uninhabited at :616-617). Stated as a
        -- hypothesis, it is visible in the type, which is what part 5's rule
        -- demands: a deliverable whose conditionality is invisible in its
        -- type is a defect.
        --
        -- TRAP T-G3. Every statement below is at a FIXED φ and a FIXED ν.
        -- Nothing here defines an internal Ω-valued function on the ground's
        -- own formulas; truth is a host-level family of theorems indexed
        -- externally by a formula, and the ground cannot form it. Bell p. 24
        -- forbids the global internal truth-value function and the roadmap
        -- repeats it at roadmap:191. No K5 statement quantifies a formula
        -- inside the object language and none is offered here.

        module Sat
          (_≈ᵁ_ _∈ᵁ_ : Nameᴮ → Nameᴮ → Ω)
          (sat : ∀ {k} → Src k → Envᴮ k → Ω)
          (sat-∈ : ∀ {k} (a b : Fin k) (ν : Envᴮ k)
                 → sat (var a ∈̇ var b) ν ≡ (lookup a ν ∈ᵁ lookup b ν))
          (sat-≐ : ∀ {k} (a b : Fin k) (ν : Envᴮ k)
                 → sat (var a ≐ var b) ν ≡ (lookup a ν ≈ᵁ lookup b ν))
          (sat-∧ : ∀ {k} (φ ψ : Src k) (ν : Envᴮ k)
                 → sat (φ ∧̇ ψ) ν ≡ ((sat φ ν) ⊓ (sat ψ ν)))
          (sat-∨ : ∀ {k} (φ ψ : Src k) (ν : Envᴮ k)
                 → sat (φ ∨̇ ψ) ν ≡ ((sat φ ν) ⊔ (sat ψ ν)))
          (sat-⇒ : ∀ {k} (φ ψ : Src k) (ν : Envᴮ k)
                 → sat (φ ⇒̇ ψ) ν ≡ ((sat φ ν) ⇒ (sat ψ ν)))
          (sat-⊥ : ∀ {k} (ν : Envᴮ k) → sat {k} ⊥̇ ν ≡ ⊥)
          (sat-∃ : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k)
                 → sat (∃̇ φ) ν ≡ ⋁ Nameᴮ (λ σ → sat φ (σ ∷ ν)))
          (sat-∀ : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k)
                 → sat (∀̇ φ) ν ≡ ⋀ Nameᴮ (λ σ → sat φ (σ ∷ ν)))
          (sat-∃∈ : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Envᴮ k)
                  → sat (∃̇∈ (var j) φ) ν
                  ≡ ⋁ Nameᴮ (λ σ → (σ ∈ᵁ lookup j ν) ⊓ sat φ (σ ∷ ν)))
          (sat-∀∈ : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Envᴮ k)
                  → sat (∀̇∈ (var j) φ) ν
                  ≡ ⋀ Nameᴮ (λ σ → (σ ∈ᵁ lookup j ν) ⇒ sat φ (σ ∷ ν)))
          (atom-∈ : (σ τ : Nameᴮ) → (σ ∈ᵁ τ) ≡ Uof (memᴬ (fst σ) (fst τ)))
          (atom-≐ : (σ τ : Nameᴮ) → (σ ≈ᵁ τ) ≡ Uof (eqᴬ (fst σ) (fst τ)))
          where

          -- THE TRUTH LEMMA, in its working form. Ten cases. The six
          -- propositional ones are the filter block above; the four
          -- quantifier ones are join-prime and meet-complete. Each case is
          -- built by ⇔toPath out of two entailments and never by a congruence
          -- over a truth-value operation, which is preamble rule 1: a bare
          -- reflexivity inside such a congruence leaves the propositionality
          -- component an unsolved metavariable.

          truth-Uof : LEM ℓ → ∀ {k} (φ : Src k) (ν : Envᴮ k) → Supply φ
                    → sat φ ν ≡ Uof (val φ ν)
          truth-Uof lem = go
            where
              go : ∀ {k} (φ : Src k) (ν : Envᴮ k) → Supply φ
                 → sat φ ν ≡ Uof (val φ ν)

              go (var a ∈̇ var b) ν _ =
                sat-∈ a b ν
                ∙ atom-∈ (lookup a ν) (lookup b ν)
                ∙ cong Uof (sym (law-∈ a b ν))
              go (var a ∈̇ con ()) ν _
              go (con () ∈̇ t) ν _

              go (var a ≐ var b) ν _ =
                sat-≐ a b ν
                ∙ atom-≐ (lookup a ν) (lookup b ν)
                ∙ cong Uof (sym (law-≐ a b ν))
              go (var a ≐ con ()) ν _
              go (con () ≐ t) ν _

              go ⊥̇ ν _ = ⇔toPath fwd bwd
                where
                  fwd : ⟨ sat ⊥̇ ν ⟩ → ⟨ Uof (val ⊥̇ ν) ⟩
                  fwd h = Empty.rec* (subst ⟨_⟩ (sat-⊥ ν) h)
                  bwd : ⟨ Uof (val ⊥̇ ν) ⟩ → ⟨ sat ⊥̇ ν ⟩
                  bwd h =
                    Empty.rec*
                      (Uof-proper (subst (λ z → ⟨ Uof z ⟩) (law-⊥ ν) h))

              go (φ ∧̇ ψ) ν sup = ⇔toPath fwd bwd
                where
                  fwd : ⟨ sat (φ ∧̇ ψ) ν ⟩ → ⟨ Uof (val (φ ∧̇ ψ) ν) ⟩
                  fwd h = subst (λ z → ⟨ Uof z ⟩) (sym (law-∧ φ ψ ν))
                    (Uof-⊓-in (val φ ν) (val ψ ν)
                      (subst ⟨_⟩ (go φ ν (fst sup)) (fst hh))
                      (subst ⟨_⟩ (go ψ ν (snd sup)) (snd hh)))
                    where hh = subst ⟨_⟩ (sat-∧ φ ψ ν) h
                  bwd : ⟨ Uof (val (φ ∧̇ ψ) ν) ⟩ → ⟨ sat (φ ∧̇ ψ) ν ⟩
                  bwd h = subst ⟨_⟩ (sym (sat-∧ φ ψ ν))
                    ( subst ⟨_⟩ (sym (go φ ν (fst sup)))
                        (Uof-⊓-out₁ (val φ ν) (val ψ ν) hh)
                    , subst ⟨_⟩ (sym (go ψ ν (snd sup)))
                        (Uof-⊓-out₂ (val φ ν) (val ψ ν) hh) )
                    where hh = subst (λ z → ⟨ Uof z ⟩) (law-∧ φ ψ ν) h

              go (φ ∨̇ ψ) ν sup = ⇔toPath fwd bwd
                where
                  fwd : ⟨ sat (φ ∨̇ ψ) ν ⟩ → ⟨ Uof (val (φ ∨̇ ψ) ν) ⟩
                  fwd h = subst (λ z → ⟨ Uof z ⟩) (sym (law-∨ φ ψ ν))
                    (PT.rec (snd (Uof (val φ ν ⊔ᴮ val ψ ν)))
                      (λ { (inl x) → Uof-⊔-in₁ (val φ ν) (val ψ ν)
                                       (subst ⟨_⟩ (go φ ν (fst sup)) x)
                         ; (inr y) → Uof-⊔-in₂ (val φ ν) (val ψ ν)
                                       (subst ⟨_⟩ (go ψ ν (snd sup)) y) })
                      (subst ⟨_⟩ (sat-∨ φ ψ ν) h))
                  bwd : ⟨ Uof (val (φ ∨̇ ψ) ν) ⟩ → ⟨ sat (φ ∨̇ ψ) ν ⟩
                  bwd h = subst ⟨_⟩ (sym (sat-∨ φ ψ ν))
                    (PT.map
                      (λ { (inl x) → inl (subst ⟨_⟩ (sym (go φ ν (fst sup))) x)
                         ; (inr y) → inr (subst ⟨_⟩ (sym (go ψ ν (snd sup))) y) })
                      (Uof-⊔-out lem (val φ ν) (val ψ ν)
                        (subst (λ z → ⟨ Uof z ⟩) (law-∨ φ ψ ν) h)))

              go (φ ⇒̇ ψ) ν sup = ⇔toPath fwd bwd
                where
                  fwd : ⟨ sat (φ ⇒̇ ψ) ν ⟩ → ⟨ Uof (val (φ ⇒̇ ψ) ν) ⟩
                  fwd h = subst (λ z → ⟨ Uof z ⟩) (sym (law-⇒ φ ψ ν))
                    (Uof-⇒-in lem (val φ ν) (val ψ ν)
                      (λ hu → subst ⟨_⟩ (go ψ ν (snd sup))
                                (subst ⟨_⟩ (sat-⇒ φ ψ ν) h
                                  (subst ⟨_⟩ (sym (go φ ν (fst sup))) hu))))
                  bwd : ⟨ Uof (val (φ ⇒̇ ψ) ν) ⟩ → ⟨ sat (φ ⇒̇ ψ) ν ⟩
                  bwd h = subst ⟨_⟩ (sym (sat-⇒ φ ψ ν))
                    (λ hs → subst ⟨_⟩ (sym (go ψ ν (snd sup)))
                              (Uof-⇒-out (val φ ν) (val ψ ν)
                                (subst (λ z → ⟨ Uof z ⟩) (law-⇒ φ ψ ν) h)
                                (subst ⟨_⟩ (go φ ν (fst sup)) hs)))

              go (∃̇ φ) ν sup = ⇔toPath fwd bwd
                where
                  fwd : ⟨ sat (∃̇ φ) ν ⟩ → ⟨ Uof (val (∃̇ φ) ν) ⟩
                  fwd h = PT.rec (snd (Uof (val (∃̇ φ) ν)))
                    (λ { (σ , hσ) →
                         Uof-up (val φ (σ ∷ ν)) (val (∃̇ φ) ν) (law-∃-ub φ ν σ)
                           (subst ⟨_⟩ (go φ (σ ∷ ν) (snd sup)) hσ) })
                    (subst ⟨_⟩ (sat-∃ φ ν) h)
                  bwd : ⟨ Uof (val (∃̇ φ) ν) ⟩ → ⟨ sat (∃̇ φ) ν ⟩
                  bwd h = subst ⟨_⟩ (sym (sat-∃ φ ν))
                    (PT.map
                      (λ { (σ , hσ) →
                           σ , subst ⟨_⟩ (sym (go φ (σ ∷ ν) (snd sup))) hσ })
                      (join-prime lem (λ σ → val φ (σ ∷ ν)) (val (∃̇ φ) ν)
                        (law-∃-ub φ ν) (law-∃-lub φ ν) (fst sup ν) h))

              go (∀̇ φ) ν sup = ⇔toPath fwd bwd
                where
                  fwd : ⟨ sat (∀̇ φ) ν ⟩ → ⟨ Uof (val (∀̇ φ) ν) ⟩
                  fwd h =
                    meet-complete lem (λ σ → val φ (σ ∷ ν)) (val (∀̇ φ) ν)
                      (law-∀-lb φ ν) (law-∀-glb φ ν) (fst sup ν)
                      (λ σ → subst ⟨_⟩ (go φ (σ ∷ ν) (snd sup))
                               (subst ⟨_⟩ (sat-∀ φ ν) h σ))
                  bwd : ⟨ Uof (val (∀̇ φ) ν) ⟩ → ⟨ sat (∀̇ φ) ν ⟩
                  bwd h = subst ⟨_⟩ (sym (sat-∀ φ ν))
                    (λ σ → subst ⟨_⟩ (sym (go φ (σ ∷ ν) (snd sup)))
                             (Uof-up (val (∀̇ φ) ν) (val φ (σ ∷ ν))
                               (law-∀-lb φ ν σ) h))

              go (∃̇∈ (var j) φ) ν sup = ⇔toPath fwd bwd
                where
                  fwd : ⟨ sat (∃̇∈ (var j) φ) ν ⟩
                      → ⟨ Uof (val (∃̇∈ (var j) φ) ν) ⟩
                  fwd h = PT.rec (snd (Uof (val (∃̇∈ (var j) φ) ν)))
                    (λ { (σ , hm , hφ) →
                         Uof-up (memᴬ (fst σ) (fst (lookup j ν))
                                 ⊓ᴮ val φ (σ ∷ ν))
                                (val (∃̇∈ (var j) φ) ν) (law-∃∈-ub j φ ν σ)
                           (Uof-⊓-in (memᴬ (fst σ) (fst (lookup j ν)))
                                     (val φ (σ ∷ ν))
                             (subst ⟨_⟩ (atom-∈ σ (lookup j ν)) hm)
                             (subst ⟨_⟩ (go φ (σ ∷ ν) (snd sup)) hφ)) })
                    (subst ⟨_⟩ (sat-∃∈ j φ ν) h)
                  bwd : ⟨ Uof (val (∃̇∈ (var j) φ) ν) ⟩
                      → ⟨ sat (∃̇∈ (var j) φ) ν ⟩
                  bwd h = subst ⟨_⟩ (sym (sat-∃∈ j φ ν))
                    (PT.map
                      (λ { (σ , hσ) →
                           σ
                           , ( subst ⟨_⟩ (sym (atom-∈ σ (lookup j ν)))
                                 (Uof-⊓-out₁ (memᴬ (fst σ) (fst (lookup j ν)))
                                             (val φ (σ ∷ ν)) hσ)
                             , subst ⟨_⟩ (sym (go φ (σ ∷ ν) (snd sup)))
                                 (Uof-⊓-out₂ (memᴬ (fst σ) (fst (lookup j ν)))
                                             (val φ (σ ∷ ν)) hσ) ) })
                      (join-prime lem
                        (λ σ → memᴬ (fst σ) (fst (lookup j ν))
                               ⊓ᴮ val φ (σ ∷ ν))
                        (val (∃̇∈ (var j) φ) ν)
                        (law-∃∈-ub j φ ν) (law-∃∈-lub j φ ν) (fst sup ν) h))
              go (∃̇∈ (con ()) φ) ν _

              go (∀̇∈ (var j) φ) ν sup = ⇔toPath fwd bwd
                where
                  fwd : ⟨ sat (∀̇∈ (var j) φ) ν ⟩
                      → ⟨ Uof (val (∀̇∈ (var j) φ) ν) ⟩
                  fwd h =
                    meet-complete lem
                      (λ σ → memᴬ (fst σ) (fst (lookup j ν))
                             ⇒ᴮ val φ (σ ∷ ν))
                      (val (∀̇∈ (var j) φ) ν)
                      (law-∀∈-lb j φ ν) (law-∀∈-glb j φ ν) (fst sup ν)
                      (λ σ → Uof-⇒-in lem (memᴬ (fst σ) (fst (lookup j ν)))
                                          (val φ (σ ∷ ν))
                               (λ hu → subst ⟨_⟩ (go φ (σ ∷ ν) (snd sup))
                                         (subst ⟨_⟩ (sat-∀∈ j φ ν) h σ
                                           (subst ⟨_⟩
                                             (sym (atom-∈ σ (lookup j ν)))
                                             hu))))
                  bwd : ⟨ Uof (val (∀̇∈ (var j) φ) ν) ⟩
                      → ⟨ sat (∀̇∈ (var j) φ) ν ⟩
                  bwd h = subst ⟨_⟩ (sym (sat-∀∈ j φ ν))
                    (λ σ hm → subst ⟨_⟩ (sym (go φ (σ ∷ ν) (snd sup)))
                      (Uof-⇒-out (memᴬ (fst σ) (fst (lookup j ν)))
                                 (val φ (σ ∷ ν))
                        (Uof-up (val (∀̇∈ (var j) φ) ν)
                                (memᴬ (fst σ) (fst (lookup j ν))
                                 ⇒ᴮ val φ (σ ∷ ν))
                                (law-∀∈-lb j φ ν σ) h)
                        (subst ⟨_⟩ (atom-∈ σ (lookup j ν)) hm)))
              go (∀̇∈ (con ()) φ) ν _

          -- The architecture's printed form (part 1.9), which is the working
          -- form read back through ⊩-spec. It is the same theorem: under
          -- decision D3 the right hand side IS Uof (val φ ν).

          truth : LEM ℓ → ∀ {k} (φ : Src k) (ν : Envᴮ k) → Supply φ
                → sat φ ν ≡ ⋁ Cond (λ p → (G∈ p) ⊓ (p ⊩ φ [ ν ]))
          truth lem φ ν sup =
            truth-Uof lem φ ν sup
            ∙ ⇔toPath
                (λ h → PT.map
                  (λ { (p , hp , hf) →
                       p , hp , subst ⟨_⟩ (sym (⊩-spec p φ ν)) hf })
                  (Uof-to (val φ ν) h))
                (λ h → Uof-of (val φ ν)
                  (PT.map
                    (λ { (p , hp , hf) →
                         p , hp , subst ⟨_⟩ (⊩-spec p φ ν) hf })
                    h))

--------------------------------------------------------------------------------
-- The two corollaries exit item X5 names beside the truth lemma
--------------------------------------------------------------------------------

          -- The generic never satisfies a formula and its negation. FREE of
          -- excluded middle and free of any Admits: it is Uof-not-both read
          -- through val-¬, and the whole of its content is properness of the
          -- filter, which is ForcingBase.i-nonzero. FALSE at a degenerate
          -- algebra, and the file says where the exclusion happens.

          not-both : ∀ {k} (φ : Src k) (ν : Envᴮ k)
                   → ⟨ Uof (val φ ν) ⟩ → ⟨ Uof (val (¬̇ φ) ν) ⟩ → ⟨ ⊥ ⟩
          not-both φ ν h hn =
            Uof-not-both (val φ ν) h
              (subst (λ z → ⟨ Uof z ⟩) (val-¬ φ ν) hn)

          -- The generic decides every fixed formula. PAID, and the payment is
          -- Track D's ultrafilter clause, which meets the coded dense set
          -- decideAt; without genericity this is FALSE, and the dense set is
          -- where genericity is spent.

          decided : LEM ℓ → ∀ {k} (φ : Src k) (ν : Envᴮ k)
                  → ⟨ (Uof (val φ ν)) ⊔ (Uof (val (¬̇ φ) ν)) ⟩
          decided lem φ ν =
            PT.map
              (λ { (inl x) → inl x
                 ; (inr y) → inr (subst (λ z → ⟨ Uof z ⟩) (sym (val-¬ φ ν)) y) })
              (Uof-ultra lem meets (val φ ν))

          -- The same two, read at satisfaction through the truth lemma. These
          -- are the sentences a reader wants: the extension is consistent and
          -- complete for each fixed formula of the ground's language.

          sat-not-both : LEM ℓ → ∀ {k} (φ : Src k) (ν : Envᴮ k) → Supply φ
                       → ⟨ sat φ ν ⟩ → ⟨ sat (¬̇ φ) ν ⟩ → ⟨ ⊥ ⟩
          sat-not-both lem φ ν sup h hn =
            not-both φ ν
              (subst ⟨_⟩ (truth-Uof lem φ ν sup) h)
              (subst ⟨_⟩ (truth-Uof lem (¬̇ φ) ν (sup , tt*)) hn)

          sat-decided : LEM ℓ → ∀ {k} (φ : Src k) (ν : Envᴮ k) → Supply φ
                      → ⟨ (sat φ ν) ⊔ (sat (¬̇ φ) ν) ⟩
          sat-decided lem φ ν sup =
            PT.map
              (λ { (inl x) → inl (subst ⟨_⟩ (sym (truth-Uof lem φ ν sup)) x)
                 ; (inr y) → inr (subst ⟨_⟩
                     (sym (truth-Uof lem (¬̇ φ) ν (sup , tt*))) y) })
              (decided lem φ ν)

--------------------------------------------------------------------------------
-- The non-claims this track states beside the signatures they constrain
--------------------------------------------------------------------------------

-- O1. THE ATOMIC GRAPH HAS NO DISCHARGE AT ANY GROUND. The fourteen compiler
-- laws and the two atomic bridges of module Sat sit in telescopes, where they
-- are visible, and not in comments. K4's own record says the graph's step
-- clause, its membership image clause and the recursion's comparison theorem
-- are contract parameters because each is a thing K0 built at B = P(X) in L
-- and did not build at a general ground (K4/AtomicGraph.agda:411, :719-720,
-- TableSupply uninhabited at :616-617). This file claims no discharge.
--
-- O2. THE CODED AND HOST SEMANTIC AGREEMENT IS CONDITIONAL AND IS NOT
-- TOUCHED. This file names no host value, applies no host semantics and
-- quotes no sentence of K4/HostSemantics.agda:1205-1213, which architecture
-- part 6.5 refutes: eq-agrees and mem-agrees both take ReadsSup and ReadsInf
-- (:1075, :1079) and the atomic cases are among the six the sentence calls
-- unconditional, so the genuinely unconditional fragment is the ⊥̇-generated
-- propositional one and not the quantifier free one.
--
-- O6. isGeneric (Uof G) IS AN UNBUILT INTERFACE AND NOT AN UNPROVED THEOREM.
-- K2's genericity predicate lives inside module Core over a Presentation
-- carrying a coded order graph (CodedCompletion.agda:201-208, :1070-1074) and
-- B has none. Nothing here says that Uof G is generic, in any disguise. What
-- is used is exactly what Track D proved: a proper directed upward closed
-- filter that reflects G and, under LEM ℓ and genericity downstairs, decides
-- every element.
--
-- ORDER REFLECTION AND SEPARATIVITY. Neither is assumed, derived or used.
-- i p ≤ᴮ i q → p ≼ᶜ q is FALSE and K2 refutes it
-- (InstancesCompletion.agda:131-134); separativity is additional data and
-- never a field (ForcingNotion.agda:276-278). The only place this file could
-- have reached for either is the directedness of Uof, and that is Track D's
-- and its witness is the image of a condition.
--
-- NO REVERSE CORRESPONDENCE. The pullback G-of U is not stated, not used and
-- not K5's: directedness of the pullback demands a common refinement inside
-- the filter (ForcingNotion.agda:175-180) and the image of an ultrafilter
-- gives only separate compatibility. It is K6's or K11's, under an explicit
-- separative hypothesis.
--
-- NO WELL-FOUNDEDNESS AND NO QUOTIENT. Nothing here asserts that the value
-- relation is well founded, and no set quotient is formed. Bell's Theorem 4.1
-- at the quotient carrier is K13's and may not reuse this track's hypotheses
-- to claim it.

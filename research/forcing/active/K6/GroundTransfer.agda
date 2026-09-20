{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track C: Infinity at the extension structure, and the identification of
-- the ground naturals.
--
-- WHAT THIS FILE IS ABOUT. K5's Track F proved that the check map is an
-- ∈-monomorphism of the ground into the names, and that a Δ₀ formula of the
-- ground's own language has the SAME truth value read in the extension along
-- that map as it has in the ground (K5/Structures.agda:670-671, groundSat).
-- This file asks what that buys, and the answer is exactly one axiom plus the
-- naturals.
--
-- ---------------------------------------------------------------------
-- WHERE THE Δ₀ BOUNDARY FALLS, WHICH IS THE MATHEMATICAL CONTENT
-- ---------------------------------------------------------------------
--
-- The Infinity SENTENCE is not Δ₀. Its outermost constructor is an UNBOUNDED
-- existential: "there is an inductive set". Written as syntax it is ∃̇ infFo,
-- and Δ₀ (FOL/LevyHierarchy.lagda.md:67-75) has no ∃̇ case at all, so no
-- certificate for it can be written down. That absence is not an oversight of
-- this file: it is the wall. groundSat's two unbounded clauses are discharged
-- by absurd pattern on the Δ₀ witness (K5/Structures.agda:689-690), and the
-- reason they must be is that at ∃̇ the extension's join ranges over ⋁ Nm, the
-- whole name carrier, while the ground's ranges over ⋁ S, and a forcing
-- extension exists precisely so that the first can be inhabited where the
-- second is not.
--
-- The BODY of Infinity is Δ₀, and that is the whole of what is transferred.
-- Every quantifier in it is bounded: the memberless member is sought among the
-- members of u, its non-members among the members of itself, and the successor
-- of a member of u among the members of u. infFo below is that body and
-- infFo-Δ₀ is its certificate.
--
-- The outer existential is therefore crossed by HAND and in ONE direction
-- only. A ground set witnessing Infinity is carried to its check name by
-- PT.map, which is sound because a witness on the left produces a witness on
-- the right. Nothing in this file carries a witness the other way, and nothing
-- in this file claims that an inductive name is value-equal to the copy of an
-- inductive ground set.
--
-- ---------------------------------------------------------------------
-- THE HYPOTHESES, WHICH ARE THE MODULE TELESCOPE
-- ---------------------------------------------------------------------
--
-- On the extension side: ⟨ positiveᴾ ⟩, ONE condition in G, and nothing else.
-- Not isFilter, which K3 already records as an over-charge at exactly this
-- point (Valuation.agda:222-225, :651-657: the filter-level re-exports of
-- check-value and check-faithful are literally the positivity-level proofs
-- applied to filter-positive). isFilter does not appear in this file.
--
-- On the ground side: OrdinaryProfile.Infinity 𝒮, taken as a standalone
-- argument and never as a field of a record (ruling D4). Ground Pairing,
-- Union, Power, Separation, Collection, Choice and Foundation are not named
-- here and are not used.
--
-- Classically: nothing. LEM does not appear in this file. groundSat is
-- constructive for the reason K5 gives (K5/Structures.agda:111-117): both
-- sides of every clause are truth values of the same hPropAlgebra ℓ.
--
-- ---------------------------------------------------------------------
-- RULING D3, TRANSCRIBED. chk IS A PARAMETER
-- ---------------------------------------------------------------------
--
-- chk, chk-spec, chk-name, Γ and Γ-spec are parameters of module Copy below,
-- typed from K5/Structures.agda:565-577, and no line of this file constructs
-- a check name. The reason is recorded in K3's own source at
-- NameImage.agda:400-404: the check name's recursion equation and the
-- internalization contract are the same statement, and no tier of that file's
-- section 1.2 produces a fixed point. Track C's theorems are therefore
-- unconditional in K6's own scope, and the O3b row of the ledger is what
-- carries the cost forward to the instance, where chk is a name-valued
-- recursion.
--
-- MEASURED, AND REPORTED RATHER THAN REPAIRED. Of those five, exactly one is
-- read by a proof below: chk-name, which is what makes groundName land in the
-- carrier. chk appears in every statement. chk-spec, Γ and Γ-spec are read by
-- nothing, and entry and carrierᶠ are present only because the types of
-- chk-spec and Γ-spec mention them. That is K5's own recorded over-charge
-- (K5/Structures.agda:553-563) carried one package forward unchanged, on the
-- architecture's instruction to supply and ledger it rather than move it.
--
-- NOT TAKEN, against the architecture's own longer list, and each absence is
-- a rule 13 measurement rather than a preference: entry-inj, ≈ˢ-paths and
-- ext-path are read by nothing here, because the only place a host path would
-- be needed is the converse half of the check map's injectivity, and K5
-- exports that half already as chk-≈ (K5/Structures.agda:604-607). Taking
-- chk-≈ is what lets this file state the naturals identification in BOTH
-- directions without a realization of ≈ˢ as a path.

-- ---------------------------------------------------------------------
-- THE TELESCOPE AUDIT. WHICH PARAMETERS ARE HYPOTHESES, AND WHERE THEY LIVE
-- ---------------------------------------------------------------------
--
-- A field's type does not discriminate a legitimate proof from a poisoned
-- one, and the telescope is the only protection. So: for each parameter of
-- this file, does an inhabitant exist at a GENUINE forcing extension, and
-- from what?
--
-- DATA, carrying no claim. IsNameᴾ, _≈[G]_, _∈[G]_, Cond, G, entry, carrierᶠ,
-- and ωᴳ. Each is a set, a function or a relation; a predicate parameter
-- asserts nothing, and the degenerate choices for the two relations are
-- excluded not by their own types but by the theorem parameters below, which
-- no degenerate relation can satisfy at a ground with an inhabited set. That
-- exclusion is proved, not asserted: infinity-nonvacuous below.
--
-- THEOREMS OF K5 AND K3, proved and not assumed. groundSat is
-- K5/Structures.agda:670-671; check-value is Valuation.agda:551-552;
-- check-faithful is :611; chk-≈ is K5/Structures.agda:604-607. All four are
-- proved from ⟨ positive G ⟩ alone, at an arbitrary G, with no filter law, no
-- genericity and no excluded middle. The seam probe fills every one of these
-- four slots with the named export and not with a lambda.
--
-- A COMPUTATION, discharged by refl. chkEnv-one. The seam probe proves it.
--
-- A GROUND AXIOM. inf : OrdinaryProfile.Infinity 𝒮, at the GROUND structure
-- and not at the extension. inf-is-ground below pins the index type of its
-- join to S, and Infinityᴾ-read pins the conclusion's to Nm; the two cannot
-- be confused into a circle, because the join indices differ.
--
-- THE ONE OPEN ROW, AND IT IS OPEN RATHER THAN FALSE. chk, chk-spec, chk-name,
-- Γ and Γ-spec, which ruling D3 makes parameters. Measured against source,
-- and the measurement corrects the brief this track was dispatched with:
-- SUPPLIERS EXIST. StandardNames.agda:502-503 defines checkᴾ = Ps.chk, :523
-- checkᴾ-spec, :567 checkᴾ-name, :616 Γᴾ and :619 Γᴾ-spec, and the recursion
-- itself is at :319-320 by host well-founded recursion with its propositional
-- computation law at :322-323. So chk is CONSTRUCTED in this programme, and a
-- track that declined to construct it declined on cost and not on
-- impossibility.
--
-- What that construction costs is the honest row, and StandardNames.agda:44
-- and :52-54 state it: tier 0 is acc∈ : WellFounded _∈ᵗ_, the membership
-- accessibility of the GROUND; tier 4 is image and image-spec, K3's
-- MemberImage, which is O3b; tier 2 is ground Union. Its own words at :52-54:
-- tier 4 "is not derivable from any first-order axiom, it is load bearing
-- jointly with tier 0, and neither alone produces check". The internal route
-- that discharges an image cannot start here for the reason NameImage.agda:
-- 392-400 gives: the check name's recursion equation and the internalization
-- contract are the same statement, and the graph mentions the function being
-- produced, so there is no fixed point at that tier.
--
-- The direction of tier 0 is the whole of why this row is a cost and not a
-- poison. acc∈ is well-foundedness of the GROUND's membership, which is true
-- at any transitive ground and is the hypothesis Bell's 1.21 recursion runs
-- on. It is NOT well-foundedness of the extension's membership, which Bell
-- makes equivalent to genericity and which is false at a genuine forcing
-- extension for an arbitrary G. Nothing in this file's telescope mentions the
-- extension's membership under any well-foundedness, accessibility or
-- induction principle, and F1 and F2's censuses over this file return 0.
--
open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import FOL.Semantics
import Cubical.HITs.PropositionalTruncation as PT

module K6.GroundTransfer {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
open import Cubical.Data.Sigma using ( _×_ ; _,_ )
open PT using ( ∥_∥₁ ; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open import FOL.Syntax
  using ( Term ; Formula ; con ; var
        ; _∈̇_ ; _≐_ ; _∧̇_ ; _∨̇_ ; _⇒̇_ ; ⊥̇ ; ∃̇_ ; ∀̇_ ; ∀̇∈ ; ∃̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀ ; δ-∈ ; δ-≐ ; δ-∧ ; δ-∨ ; δ-⇒ ; δ-⊥ ; δ-∀∈ ; δ-∃∈ )
open import FOL.Manipulation.ConstantMapping using ( mapTm ; mapFo )

-- The ground's own satisfaction, at the canonical constant interpretation.
-- It is the right hand side of the transfer equation and it is named once so
-- that no signature below can confuse it with the extension's.

open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
module Gr = At S id

--------------------------------------------------------------------------------
-- The extension structure at one G, rebuilt from the flat value relation
--------------------------------------------------------------------------------

-- Nothing here is a second construction and rule 9 is not breached: the record
-- ZFStructure is the book's (FOL/ZFStructure.lagda.md:61-66) and this module
-- fills its four fields with the same four terms K5 fills them with
-- (K5/Structures.agda:285-291), taken flat as parameters. The reason the
-- structure is assembled here rather than imported is that the satisfaction
-- relation of the extension has to COMPUTE: the transfer equation below is
-- an equation between two readings of one formula, and a _⊨_ taken as an
-- opaque parameter cannot be reduced to the body of Infinity. That is
-- preamble rule 12 at this track, and it is the one place where the spine's
-- "every entry is a variable" cannot be followed.

module Transfer
  (IsNameᴾ    : S → Ω)
  (_≈[G]_ _∈[G]_ : S → S → Ω)
  (Cond       : Type ℓ)
  (G          : Cond → Ω)
  where

  Nm : Type ℓ
  Nm = Σ[ n ∈ S ] ⟨ IsNameᴾ n ⟩

  isSetNm : isSet Nm
  isSetNm = isSetΣSndProp isSetS (λ n → snd (IsNameᴾ n))

  𝒮ᴾ : ZFStructure (hPropAlgebra ℓ)
  𝒮ᴾ = record
    { S      = Nm
    ; isSetS = isSetNm
    ; _≈ˢ_   = λ σ τ → fst σ ≈[G] fst τ
    ; _∈ˢ_   = λ σ τ → fst σ ∈[G] fst τ }

  private module SemP = FOL.Semantics (hPropAlgebra ℓ) 𝒮ᴾ
  module Sat = SemP.At Nm id
  open Sat public using ( _⊨_ )

  -- The two relations of the structure, spelled so that a statement about
  -- names reads as a statement about names. Both are the structure's own
  -- fields and the two reading theorems say so by refl.

  infix 20 _≈ᴾ_ _∈ᴾ_

  _≈ᴾ_ : Nm → Nm → Ω
  σ ≈ᴾ τ = fst σ ≈[G] fst τ

  _∈ᴾ_ : Nm → Nm → Ω
  σ ∈ᴾ τ = fst σ ∈[G] fst τ

  ≈ᴾ-is-field : (σ τ : Nm) → (σ ≈ᴾ τ) ≡ ZFStructure._≈ˢ_ 𝒮ᴾ σ τ
  ≈ᴾ-is-field σ τ = refl

  ∈ᴾ-is-field : (σ τ : Nm) → (σ ∈ᴾ τ) ≡ ZFStructure._∈ˢ_ 𝒮ᴾ σ τ
  ∈ᴾ-is-field σ τ = refl

  -- Positivity, spelled from the two parameters it is built out of. This is
  -- ForcingNotion.agda:160-161 with the definition of _∈ᴾ_ there unfolded:
  -- positive U = ⋁ Cond (λ q → q ∈ᴾ U) and p ∈ᴾ D = D p.

  positiveᴾ : Ω
  positiveᴾ = ⋁ Cond (λ q → G q)

  ------------------------------------------------------------------------------
  -- Infinity's body, as a formula, and the two readings of it
  ------------------------------------------------------------------------------

  -- Trap T-C1 met by construction: every slot of infFo is a var and the set u
  -- is frozen by the ENVIRONMENT. There is no con anywhere in it, which is
  -- exactly why mapFo groundName infFo reduces definitionally and why no
  -- mapFo computation lemma is owed.

  infFo : Formula S 1
  infFo = (∃̇∈ (var zero) (∀̇∈ (var zero) ⊥̇))
        ∧̇ (∀̇∈ (var zero) (∃̇∈ (var (suc zero)) (var (suc zero) ∈̇ var zero)))

  infFo-Δ₀ : Δ₀ infFo
  infFo-Δ₀ = δ-∧ (δ-∃∈ (δ-∀∈ δ-⊥)) (δ-∀∈ (δ-∃∈ δ-∈))

  -- The ground's reading. This is the body of OrdinaryProfile.Infinity
  -- (OrdinaryProfile.agda:84-86) at the set u, transcribed, and the reading
  -- theorem is what forbids a well formed formula about the wrong set: swap
  -- either bound, or either conjunct, and infFo-readᴳ stops being refl.

  infBodyᴳ : S → Ω
  infBodyᴳ u = (⋁ S (λ e → (e ∈ˢ u) ⊓ (⋀ S (λ z → (z ∈ˢ e) ⇒ ⊥))))
             ⊓ (⋀ S (λ x → (x ∈ˢ u) ⇒ (⋁ S (λ y → (y ∈ˢ u) ⊓ (x ∈ˢ y)))))

  infFo-readᴳ : (u : S) → Gr._⊨_ (u ∷ []) infFo ≡ infBodyᴳ u
  infFo-readᴳ u = refl

  -- The extension's reading, at the same formula relabelled along the copy.
  -- The bounds are the same variables and the interpretation is the extension
  -- structure's own membership, so the body has the same SHAPE with ⋁ Nm and
  -- ⋀ Nm in place of ⋁ S and ⋀ S. That difference of index type is the whole
  -- of what a forcing extension is, and it is why only the bounded fragment
  -- transfers.

  infBodyᴾ : Nm → Ω
  infBodyᴾ υ = (⋁ Nm (λ ε → (ε ∈ᴾ υ) ⊓ (⋀ Nm (λ ζ → (ζ ∈ᴾ ε) ⇒ ⊥))))
             ⊓ (⋀ Nm (λ ξ → (ξ ∈ᴾ υ) ⇒ (⋁ Nm (λ ψ → (ψ ∈ᴾ υ) ⊓ (ξ ∈ᴾ ψ)))))

  Infinityᴾ-read : OrdinaryProfile.Infinity 𝒮ᴾ ≡ ⟨ ⋁ Nm infBodyᴾ ⟩
  Infinityᴾ-read = refl

  -- The same reading on the ground's side. The two together are the wall,
  -- stated as a positive fact rather than as a warning: the conclusion's join
  -- is indexed by Nm and the ground hypothesis's by S, so no proof can move
  -- between them by reflexivity and no ground Infinity can be mistaken for an
  -- extension one in a telescope.

  Infinityᴳ-read : OrdinaryProfile.Infinity 𝒮 ≡ ⟨ ⋁ S infBodyᴳ ⟩
  Infinityᴳ-read = refl

  ------------------------------------------------------------------------------
  -- The ground copy's interface, from K5 Track F
  ------------------------------------------------------------------------------

  -- The five of ruling D3, plus the two the types of two of them force. Typed
  -- from K5/Structures.agda:565-577.

  module Copy
    (entry       : S → S → S)
    (carrierᶠ    : S)
    (chk         : S → S)
    (chk-spec    : (a e : S) → (e ∈ˢ chk a)
                 ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ ⋁ S (λ p → (p ∈ˢ carrierᶠ)
                        ⊓ (e ≈ˢ entry (chk y) p))))
    (Γ           : S)
    (Γ-spec      : (e : S) → (e ∈ˢ Γ)
                 ≡ ⋁ S (λ p → (p ∈ˢ carrierᶠ) ⊓ (e ≈ˢ entry (chk p) p)))
    (chk-name    : (a : S) → ⟨ IsNameᴾ (chk a) ⟩)
    where

    -- K5/Structures.agda:594-595. The only place chk-name is spent.

    groundName : S → Nm
    groundName a = chk a , chk-name a

    groundName-code : (a : S) → fst (groundName a) ≡ chk a
    groundName-code a = refl

    --------------------------------------------------------------------------
    -- At a positive G, and nothing more
    --------------------------------------------------------------------------

    -- Every parameter below is an export of K5/Structures.agda's
    -- module Copy.WithPos, whose single parameter is ⟨ positive G ⟩, taken
    -- here as a function OF that positivity so that the hypothesis is visible
    -- in the type of every theorem that spends it rather than hidden in a
    -- telescope. chkEnv and chkEnv-one are K5's :598 and its one computation
    -- at arity one; the remaining four are :604, :655, :672 and K3's
    -- check-value at Valuation.agda:551-552.

    module Ground
      (chkEnv        : ∀ {k} → Vec S k → Vec Nm k)
      (chkEnv-one    : (u : S) → chkEnv (u ∷ []) ≡ (groundName u ∷ []))
      (groundSat     : ⟨ positiveᴾ ⟩ → ∀ {k} (φ : Formula S k) → Δ₀ φ
                     → (γ : Vec S k)
                     → (chkEnv γ ⊨ mapFo groundName φ) ≡ Gr._⊨_ γ φ)
      (check-value   : ⟨ positiveᴾ ⟩ → (a τ : S) → (τ ∈[G] chk a)
                     ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ (τ ≈[G] chk y)))
      (check-faithful : ⟨ positiveᴾ ⟩ → (a b : S) → (chk a ∈[G] chk b) ≡ (a ∈ˢ b))
      (chk-≈         : ⟨ positiveᴾ ⟩ → (a c : S) → (chk a ≈[G] chk c) ≡ (a ≈ˢ c))
      (inf           : OrdinaryProfile.Infinity 𝒮)
      where

      ------------------------------------------------------------------------
      -- The transfer of the Δ₀ body
      ------------------------------------------------------------------------

      -- One equation, and it is the whole of the mathematics of Infinity here.
      -- Read the two ends: on the left the body of Infinity in the extension
      -- at the check name of u, on the right the body of Infinity in the
      -- ground at u. Neither end mentions a formula; the formula is the route
      -- between them and the two reading theorems above are what pin it.

      transfer-body : ⟨ positiveᴾ ⟩ → (u : S)
                    → infBodyᴾ (groundName u) ≡ infBodyᴳ u
      transfer-body pos u =
        sym (cong (λ ν → ν ⊨ mapFo groundName infFo) (chkEnv-one u))
        ∙ groundSat pos infFo infFo-Δ₀ (u ∷ [])

      -- The copy of an inductive ground set is inductive, at a NAMED witness
      -- and with no truncation anywhere. This is the statement that fails
      -- under a vacuous reinterpretation of the value relation, and it is the
      -- one a later package should consume in place of hasInfinity when it
      -- has a ground ω in hand.

      infinity-at : ⟨ positiveᴾ ⟩ → (u : S) → ⟨ infBodyᴳ u ⟩
                  → ⟨ infBodyᴾ (groundName u) ⟩
      infinity-at pos u = subst ⟨_⟩ (sym (transfer-body pos u))

      infinity-at← : ⟨ positiveᴾ ⟩ → (u : S) → ⟨ infBodyᴾ (groundName u) ⟩
                   → ⟨ infBodyᴳ u ⟩
      infinity-at← pos u = subst ⟨_⟩ (transfer-body pos u)

      ------------------------------------------------------------------------
      -- The field
      ------------------------------------------------------------------------

      -- The unbounded existential, crossed by hand and in one direction. ⋁ is
      -- the truncated join, so the target is a proposition and PT.map is
      -- legitimate; nothing is projected out of the ground's truncation into
      -- data.

      hasInfinity : ⟨ positiveᴾ ⟩ → OrdinaryProfile.Infinity 𝒮ᴾ
      hasInfinity pos =
        PT.map (λ { (u , h) → groundName u , infinity-at pos u h }) inf

      ------------------------------------------------------------------------
      -- The identification of the ground's members, at an arbitrary ground set
      ------------------------------------------------------------------------

      -- Three facts, each in both directions, and none of them about ω in
      -- particular: the copy is an ∈-monomorphism, it is injective for the
      -- value relation, and the members of a copy are exactly the copies of
      -- the members. The last is the only one with content beyond K5's
      -- GroundCopy record, and it is K3's check-value read as a statement
      -- about the extension structure's carrier.

      copy-mem : ⟨ positiveᴾ ⟩ → (a b : S)
               → (groundName a ∈ᴾ groundName b) ≡ (a ∈ˢ b)
      copy-mem pos = check-faithful pos

      copy-mem→ : ⟨ positiveᴾ ⟩ → (a b : S) → ⟨ groundName a ∈ᴾ groundName b ⟩
                → ⟨ a ∈ˢ b ⟩
      copy-mem→ pos a b = subst ⟨_⟩ (copy-mem pos a b)

      copy-mem← : ⟨ positiveᴾ ⟩ → (a b : S) → ⟨ a ∈ˢ b ⟩
                → ⟨ groundName a ∈ᴾ groundName b ⟩
      copy-mem← pos a b = subst ⟨_⟩ (sym (copy-mem pos a b))

      copy-eq : ⟨ positiveᴾ ⟩ → (a c : S)
              → (groundName a ≈ᴾ groundName c) ≡ (a ≈ˢ c)
      copy-eq pos = chk-≈ pos

      copy-eq→ : ⟨ positiveᴾ ⟩ → (a c : S) → ⟨ groundName a ≈ᴾ groundName c ⟩
               → ⟨ a ≈ˢ c ⟩
      copy-eq→ pos a c = subst ⟨_⟩ (copy-eq pos a c)

      copy-eq← : ⟨ positiveᴾ ⟩ → (a c : S) → ⟨ a ≈ˢ c ⟩
               → ⟨ groundName a ≈ᴾ groundName c ⟩
      copy-eq← pos a c = subst ⟨_⟩ (sym (copy-eq pos a c))

      copy-members : ⟨ positiveᴾ ⟩ → (a : S) (τ : Nm) → ⟨ τ ∈ᴾ groundName a ⟩
                   → ⟨ ⋁ S (λ y → (y ∈ˢ a) ⊓ (fst τ ≈[G] chk y)) ⟩
      copy-members pos a τ = subst ⟨_⟩ (check-value pos a (fst τ))

      copy-members← : ⟨ positiveᴾ ⟩ → (a : S) (τ : Nm)
                    → ⟨ ⋁ S (λ y → (y ∈ˢ a) ⊓ (fst τ ≈[G] chk y)) ⟩
                    → ⟨ τ ∈ᴾ groundName a ⟩
      copy-members← pos a τ = subst ⟨_⟩ (sym (check-value pos a (fst τ)))

      ------------------------------------------------------------------------
      -- The low end, member by member, which is what a vacuous proof fails
      ------------------------------------------------------------------------

      -- A well typed vacuous inhabitant of hasInfinity is entirely possible:
      -- reinterpret _∈[G]_ as the constantly false relation and every join in
      -- infBodyᴾ becomes unreachable while the record still typechecks. The
      -- three statements below are the discriminators, and each of them is
      -- FALSE under a degenerate reinterpretation. The first fails if _∈[G]_
      -- is made always false, the second fails if it is made always true, the
      -- third fails if _≈[G]_ is made always true.

      low-in : ⟨ positiveᴾ ⟩ → (e a : S) → ⟨ e ∈ˢ a ⟩
             → ⟨ groundName e ∈ᴾ groundName a ⟩
      low-in pos e a = copy-mem← pos e a

      low-empty : ⟨ positiveᴾ ⟩ → (e : S) → ((z : S) → ⟨ z ∈ˢ e ⟩ → ⟨ ⊥ ⟩)
                → (ζ : Nm) → ⟨ ζ ∈ᴾ groundName e ⟩ → ⟨ ⊥ ⟩
      low-empty pos e hyp ζ hζ = PT.rec (snd ⊥)
        (λ { (y , hy , _) → hyp y hy })
        (copy-members pos e ζ hζ)

      low-distinct : ⟨ positiveᴾ ⟩ → (m n : S) → (⟨ m ≈ˢ n ⟩ → ⟨ ⊥ ⟩)
                   → ⟨ groundName m ≈ᴾ groundName n ⟩ → ⟨ ⊥ ⟩
      low-distinct pos m n hyp h = hyp (copy-eq→ pos m n h)

      -- And the two of them together, at the memberless member Infinity's
      -- first conjunct asserts: the copy of a ground set that is inductive has
      -- a member with no members, named, with the ground's own witness for it.

      low-witness : ⟨ positiveᴾ ⟩ → (u : S) → ⟨ infBodyᴳ u ⟩
                  → ⟨ ⋁ Nm (λ ε → (ε ∈ᴾ groundName u)
                        ⊓ (⋀ Nm (λ ζ → (ζ ∈ᴾ ε) ⇒ ⊥))) ⟩
      low-witness pos u h = fst (infinity-at pos u h)

      -- THE NON-VACUITY CERTIFICATE, and it is a theorem rather than a
      -- comment. Reinterpret _∈[G]_ as the constantly false relation and
      -- every statement of this file that is an EQUATION between truth values
      -- survives, because an equation has two sides; hasInfinity survives too,
      -- because its conclusion is a join and a join of false values is a
      -- perfectly good false value. What does not survive is an INHABITANT of
      -- such a join. The line below produces one, from the ground's Infinity
      -- and nothing else, and it is therefore false under that
      -- reinterpretation. Under the constantly TRUE reinterpretation of
      -- _≈[G]_ it is low-distinct that fails, for the same kind of reason.
      -- Between them the two exclude the two degenerate value relations that
      -- would make this file's conclusions empty, which is what K1's numeral
      -- chain needed and did not have.

      infinity-nonvacuous : ⟨ positiveᴾ ⟩ → ⟨ ⋁ Nm (λ υ → ⋁ Nm (λ ε → ε ∈ᴾ υ)) ⟩
      infinity-nonvacuous pos = PT.rec PT.squash₁
        (λ { (u , h) → PT.map
               (λ { (e , he , _) → groundName u , ∣ groundName e , low-in pos e u he ∣₁ })
               (fst h) })
        inf

      ------------------------------------------------------------------------
      -- The architecture's section 2.4 signatures, at a ground ω
      ------------------------------------------------------------------------

      -- Nothing new is proved here. The three names below are the general
      -- theorems above instantiated at one ground set, kept because they are
      -- the shape a later package asked for and because instantiating them
      -- here rather than at the consumer keeps the hypothesis column honest:
      -- every one of them costs ⟨ positiveᴾ ⟩ and no filter law.

      module AtOmega (ωᴳ : S) where

        nat-faithful : ⟨ positiveᴾ ⟩ → (m n : S) → (chk m ∈[G] chk n) ≡ (m ∈ˢ n)
        nat-faithful = check-faithful

        nat-onto : ⟨ positiveᴾ ⟩ → (τ : S) → ⟨ τ ∈[G] chk ωᴳ ⟩
                 → ⟨ ⋁ S (λ n → (n ∈ˢ ωᴳ) ⊓ (τ ≈[G] chk n)) ⟩
        nat-onto pos τ = subst ⟨_⟩ (check-value pos ωᴳ τ)

        nat-inj : ⟨ positiveᴾ ⟩ → (m n : S) → ⟨ chk m ≈[G] chk n ⟩ → ⟨ m ≈ˢ n ⟩
        nat-inj pos m n = subst ⟨_⟩ (chk-≈ pos m n)

        -- The converse of nat-inj, which the forward half alone does not give
        -- and which a consumer identifying the extension's naturals needs: two
        -- ground naturals that are equal have value-equal check names.

        nat-cong : ⟨ positiveᴾ ⟩ → (m n : S) → ⟨ m ≈ˢ n ⟩ → ⟨ chk m ≈[G] chk n ⟩
        nat-cong pos m n = subst ⟨_⟩ (sym (chk-≈ pos m n))

        -- The same three at the carrier of the extension structure, which is
        -- where a consumer of 𝒮ᴾ reads them.

        nat-onto-Nm : ⟨ positiveᴾ ⟩ → (τ : Nm) → ⟨ τ ∈ᴾ groundName ωᴳ ⟩
                    → ⟨ ⋁ S (λ n → (n ∈ˢ ωᴳ) ⊓ (fst τ ≈[G] chk n)) ⟩
        nat-onto-Nm pos = copy-members pos ωᴳ

        nat-in : ⟨ positiveᴾ ⟩ → (n : S) → ⟨ n ∈ˢ ωᴳ ⟩
               → ⟨ groundName n ∈ᴾ groundName ωᴳ ⟩
        nat-in pos n = low-in pos n ωᴳ

        -- Infinity at this ω, with the witness named rather than truncated.

        nat-inductive : ⟨ positiveᴾ ⟩ → ⟨ infBodyᴳ ωᴳ ⟩
                      → ⟨ infBodyᴾ (groundName ωᴳ) ⟩
        nat-inductive pos = infinity-at pos ωᴳ

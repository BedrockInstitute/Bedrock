{-# OPTIONS --cubical --safe --guardedness #-}

-- K3 Track B: supports, entries and weight families.
--
-- Section 1.5 of the K3 architecture. The question this file answers is the
-- one Bell's Definition 1.4 leaves implicit when it says a name is a set of
-- pairs: given a name n, WHICH sets are its subnames, and is that collection
-- a set of the ground rather than a class of the host?
--
-- Two answers are possible and they are not the same answer. The host knows
-- the subname relation Child, defined by a truncated existential over the
-- weight; the ground knows only what a first-order formula can cut out of a
-- set it already has. The content of this file is that the two agree, and
-- that the ground's version is obtained by ONE Separation, not by
-- Replacement.
--
-- WHY SEPARATION AND NOT REPLACEMENT. K0's support went through the strong
-- record's functional Replacement (k0-internal-names-probes-2026-09.md:44),
-- which forces a proof that the coordinate relation is functional before the
-- support exists at all, and that proof is available only for a genuine name.
-- The cheaper route is the membership chain
--
--     x ∈ {x} ∈ entry x b ∈ n        (k0-material-names-value-sets:28)
--
-- which bounds every subname of n inside the double union ⋃²n. Once the
-- bound is a theorem, the support is a Separation on ⋃²n and three things
-- follow at once: `support` is TOTAL, defined on arbitrary ground codes with
-- no ⟨ IsName n ⟩ premise; Collection leaves the K3 core, so Track B's ledger
-- is Tier 2 `Sets`; and the roadmap's "support bound" becomes the literal
-- theorem support-bound below rather than a slogan.
--
-- NO WEIGHT FUNCTION, ANYWHERE. A name may carry the same subname at many
-- weights, and nothing in the theory chooses one of them. So the weight of a
-- SUBNAME is not a function but a set, weightsAt n x, and the support is the
-- family of subnames whose weight set is inhabited (support-is-join). The
-- only function-valued weight in the file is `weight`, and it is indexed by
-- an ENTRY of n, never by a subname: two entries may carry the same subname
-- and receive different weights. This is K0's ruling
-- (k0-representation-decision-2026-09.md:7; k0-internal-names-probes:47-48)
-- and it is what makes the non-selecting reverse translation expressible at
-- all.
--
-- THE SEAL. Every description-operator term below is opaque together with its
-- specification, in one block: ⋃ᴳ with ⋃ᴳ-spec, support with support-spec,
-- weightsAt with weightsAt-spec. This is Track A's measured finding A1, not a
-- style choice: unsealed, `the Q h` unfolds to a stuck truncation eliminator
-- applied to the axiom field of a record parameter, and Track A's file ran
-- 761 s at 1.05 GB without finishing until its pair term was sealed. This
-- file nests three such terms (support separates a subset of a double union),
-- so the exposure is larger, and nothing here ever needs an unfolding: every
-- consumer goes through the -spec.
--
-- THE THREE MECHANICAL LESSONS. (1) Every equality of Ω-valued expressions
-- below is produced either by the-spec, which hands over a whole path, or by
-- ⇔toPath with both directions written out, or by cong along a path whose
-- endpoints are already fixed. No bare refl sits inside a congruence over ⊓,
-- ⇒, ⊔, ⋀ or ⋁. (2) Both description terms write their class argument out in
-- full, and the two separations go through GroundDescription's separateOf,
-- which spells it once. (3) This file contains no negation at all, so the
-- lifted-bottom trap cannot arise; ⊥ does not occur.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel

module NameSupport {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Term; var; Formula; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; checkΔ₀ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
import GroundDescription
open import CodedVocabulary 𝒮
  using ( isSglΔ; isPairΔ; isKPairΔ; prAtˢ; sepAt; sepAt-reading; Δ₀-sepAt )
open import Cubical.Data.Unit using ( tt )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Induction.WellFounded using ( WellFounded; module WFI )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ) hiding ( ¬_ )
open hPropStructure 𝒮
open At S id using ( _⊨_ )

-- The four ground tiers are Track A's, at NameKernel's own top level. The
-- architecture gives them a node of their own, K3.0, and assigns that node to
-- no track; hosting them once and importing them here is what keeps a single
-- ledger in the package. Track B consumes Tier 2 and no more: Extensionality,
-- Pairing and the path realization through Core, plus Union and Separation.
-- Collection, PowerSet, Infinity, Foundation and LEM appear nowhere below.

module NK = NameKernel 𝒮
open NK using ( Core; Sets; Accessibility )

-- ---------------------------------------------------------------------
-- The two readers
-- ---------------------------------------------------------------------

-- These take no hypothesis at all, not even a ground axiom: a formula and its
-- reading are facts about the evaluator. Both are built from K2's coded
-- vocabulary rather than from new syntax, so the Δ₀ witness is checkΔ₀ on the
-- formula's own shape and the reading is refl.
--
-- The first reader is "x is a child of n against the weight carrier w": some
-- member e of n is the Kuratowski pair of x with some member b of w. Both
-- quantifiers are bounded, the outer by n and the inner by w, which is the
-- whole reason the recognizer stays Δ₀ and can sit inside a Separation. K1's
-- pair vocabulary could not do this: its PairφK leads with an unbounded ∀̇
-- (CardinalBridge.agda:116-117) and carries no Δ₀ witness.

childAtˢ : ∀ {k} → Fin k → Fin k → Fin k → Formula S k
childAtˢ x n w = ∃̇∈ (var n) (∃̇∈ (var (suc w)) (prAtˢ (suc zero) (suc (suc x)) zero))

childΔ : S → S → S → Ω
childΔ w n x =
  ⋁ S (λ e → (e ∈ˢ n) ⊓ (⋁ S (λ b → (b ∈ˢ w) ⊓ isKPairΔ e x b)))

Δ₀-childAtˢ : ∀ {k} (x n w : Fin k) → Δ₀ (childAtˢ x n w)
Δ₀-childAtˢ x n w = checkΔ₀ (childAtˢ x n w) tt

childAtˢ-reading : ∀ {k} (x n w : Fin k) (γ : S ^ k)
                 → (γ ⊨ childAtˢ x n w)
                 ≡ childΔ (lookup w γ) (lookup n γ) (lookup x γ)
childAtˢ-reading x n w γ = refl

-- The second reader is "b is a weight of x in n": some member of n is the
-- Kuratowski pair of x with b. It is the first reader with the inner
-- quantifier removed and b promoted to a free slot, which is exactly the
-- difference between asking whether x occurs and asking at which weight it
-- occurs. The membership b ∈ w is not part of it; the separation that uses it
-- is taken over the weight carrier itself, so the bound supplies that clause.

weightAtˢ : ∀ {k} → Fin k → Fin k → Fin k → Formula S k
weightAtˢ b n x = ∃̇∈ (var n) (prAtˢ zero (suc x) (suc b))

weightΔ : S → S → S → Ω
weightΔ n x b = ⋁ S (λ e → (e ∈ˢ n) ⊓ isKPairΔ e x b)

Δ₀-weightAtˢ : ∀ {k} (b n x : Fin k) → Δ₀ (weightAtˢ b n x)
Δ₀-weightAtˢ b n x = checkΔ₀ (weightAtˢ b n x) tt

weightAtˢ-reading : ∀ {k} (b n x : Fin k) (γ : S ^ k)
                  → (γ ⊨ weightAtˢ b n x)
                  ≡ weightΔ (lookup n γ) (lookup x γ) (lookup b γ)
weightAtˢ-reading b n x γ = refl



-- Transport of membership along a path in the LEFT argument. The kernel
-- names the right-hand version; this file needs the other one, because
-- every determinacy step moves a member between two sets by rewriting the
-- member and not the set.

mem-substˡ : {u v : S} → u ≡ v → {z : S} → ⟨ u ∈ˢ z ⟩ → ⟨ v ∈ˢ z ⟩
mem-substˡ p {z} = subst (λ w → ⟨ w ∈ˢ z ⟩) p

-- ---------------------------------------------------------------------
-- What a coded Kuratowski pair determines
-- ---------------------------------------------------------------------

-- The gap this module closes is the one between the two readings of "entry".
-- The kernel's entry x b is a host TERM, built by two applications of the
-- pairing description. The formula above cannot mention it: a Δ₀ formula
-- quantifies over members and compares them, so all it can say is that some
-- member of n SATISFIES the Kuratowski predicate. Separation therefore cuts
-- out the x for which such a member exists, and to get back a child of n in
-- the kernel's sense one needs: a set satisfying isKPairΔ q x b is the term
-- entry x b on the nose.
--
-- That is a uniqueness statement and its source is Extensionality, nothing
-- else. The proof is in three steps and each step is a determinacy fact: two
-- sets that satisfy the same coded description have the same members, hence
-- are equal. Note what is NOT used: no projection of the pairing axiom, no
-- unfolding of the kernel's pairOf (which is sealed on Track A's side), and
-- no injectivity of the entry. Injectivity is spent elsewhere, on the entry
-- index; here the work is extensional agreement.
--
-- The parameter list is the claim: this module needs Tier 1 and would be
-- unchanged if Union and Separation were never assumed.

module Determinacy (𝔠 : Core) where

  open Core 𝔠 using ( extensional; ≈ˢ-paths )

  module GD = GroundDescription 𝒮 extensional ≈ˢ-paths
  open GD public using ( the; the-spec; separateOf; separateOf-spec; ext-path )

  -- The structure's equality is a field into Ω and is not the host's path
  -- equality by definition. Every crossing below goes through one of these.

  ≈→≡ : {x y : S} → ⟨ x ≈ˢ y ⟩ → x ≡ y
  ≈→≡ {x} {y} = subst ⟨_⟩ (≈ˢ-paths x y)

  -- Step one. A coded singleton is determined: its members are exactly the
  -- things equal to u, so two of them agree member by member.

  sgl-det : (w w' u : S) → ⟨ isSglΔ w u ⟩ → ⟨ isSglΔ w' u ⟩ → w ≡ w'
  sgl-det w w' u (hu , all) (hu' , all') = ext-path step
    where
      step : (z : S) → (z ∈ˢ w) ≡ (z ∈ˢ w')
      step z = ⇔toPath
        (λ m → mem-substˡ (sym (≈→≡ (all z m))) hu')
        (λ m → mem-substˡ (sym (≈→≡ (all' z m))) hu)

  -- Step two. A coded unordered pair is determined, by the same argument with
  -- a truncated disjunction in the middle. The disjunction eliminates into
  -- membership, which is a proposition, so the truncation costs nothing.

  pair-det : (w w' u v : S) → ⟨ isPairΔ w u v ⟩ → ⟨ isPairΔ w' u v ⟩ → w ≡ w'
  pair-det w w' u v (hu , hv , all) (hu' , hv' , all') = ext-path step
    where
      into : (z t : S) → ⟨ u ∈ˢ t ⟩ → ⟨ v ∈ˢ t ⟩
           → ⟨ (z ≈ˢ u) ⊔ (z ≈ˢ v) ⟩ → ⟨ z ∈ˢ t ⟩
      into z t mu mv = PT.rec (snd (z ∈ˢ t))
        (λ { (inl p) → mem-substˡ (sym (≈→≡ p)) mu
           ; (inr p) → mem-substˡ (sym (≈→≡ p)) mv })

      step : (z : S) → (z ∈ˢ w) ≡ (z ∈ˢ w')
      step z = ⇔toPath
        (λ m → into z w' hu' hv' (all z m))
        (λ m → into z w  hu  hv  (all' z m))

  -- Step three. A coded Kuratowski pair is determined. Its third clause says
  -- every member is one of the two coded shapes, and its first two clauses
  -- say the other set has a member of each shape; steps one and two identify
  -- them, so membership transfers in both directions.

  kpair-det : (q r x b : S) → ⟨ isKPairΔ q x b ⟩ → ⟨ isKPairΔ r x b ⟩ → q ≡ r
  kpair-det q r x b (s₁ , p₁ , a₁) (s₂ , p₂ , a₂) = ext-path step
    where
      transfer : (q' r' : S)
               → ⟨ ⋁ S (λ w → (w ∈ˢ r') ⊓ isSglΔ w x) ⟩
               → ⟨ ⋁ S (λ w → (w ∈ˢ r') ⊓ isPairΔ w x b) ⟩
               → ⟨ ⋀ S (λ w → (w ∈ˢ q') ⇒ (isSglΔ w x ⊔ isPairΔ w x b)) ⟩
               → (z : S) → ⟨ z ∈ˢ q' ⟩ → ⟨ z ∈ˢ r' ⟩
      transfer q' r' hs hp all z m = PT.rec (snd (z ∈ˢ r'))
        (λ { (inl h) → PT.rec (snd (z ∈ˢ r'))
               (λ { (w , hw , hw') → mem-substˡ (sym (sgl-det z w x h hw')) hw })
               hs
           ; (inr h) → PT.rec (snd (z ∈ˢ r'))
               (λ { (w , hw , hw') → mem-substˡ (sym (pair-det z w x b h hw')) hw })
               hp })
        (all z m)

      step : (z : S) → (z ∈ˢ q) ≡ (z ∈ˢ r)
      step z = ⇔toPath (transfer q r s₂ p₂ a₁ z) (transfer r q s₁ p₁ a₂ z)

-- ---------------------------------------------------------------------
-- Section 1.5. Supports, entries and weight families
-- ---------------------------------------------------------------------

-- THE LEDGER IS THE NESTING. Two modules, and the boundary between them is a
-- claim that can be checked by reading the telescopes rather than the proofs.
--
-- `Names` takes the weight carrier and NINE facts of Track A's kernel, and no
-- ground axiom whatsoever: not Extensionality, not Pairing, not Union, not
-- Separation, not the realization of the structure equality as a host path.
-- The entry index, the decoded child, the decoded weight and the recursor
-- over a name all live there. This is worth stating because it is easy to
-- assume the opposite: reading the entries of a name looks like an operation
-- on the ground, and it is not. It is a decoding of a truncation that the
-- name predicate already carries, and injectivity of the entry is what makes
-- the decoding possible.
--
-- `WithGround` adds Tier 2 `Sets` and two further kernel facts, and only then
-- does a ground set get built. Union builds the double union that bounds
-- every support; Separation cuts the support out of it; Core supplies the
-- extensionality that the determinacy lemmas above run on. Collection,
-- PowerSet, Infinity, Foundation and LEM are absent, and their absence is the
-- decision recorded at the head of this file.
--
-- Each parameter below is a declaration of NameKernel.agda, cited by line.
-- Note what is NOT asked for: no pairOf, no singleOf, no entry-spec, no
-- name-intro, and no accessibility datum. Accessibility enters only as
-- child-wf, which is what Track A derives from it; asking for
-- WellFounded _∈ᵗ_ as well would over-state what this file consumes, since no
-- proof below descends through the membership relation.
--
-- child-entry and child-weight are the two halves of "Child is the truncated
-- existential over the weight", and they sit on opposite sides of the
-- boundary: the introduction rule is needed to decode an entry into a subname
-- and so belongs to `Names`, while the elimination rule is needed only to
-- prove that a child lands in the support and so belongs to `WithGround`.
-- Track A's Child is a transparent definition and both are identities there;
-- taking them as parameters means this file still works if Track A ever seals
-- it.

module Names (W : S)
  (entry          : S → S → S)                              -- NameKernel:253
  (entry-inj      : {x b y c : S} → entry x b ≡ entry y c
                  → (x ≡ y) × (b ≡ c))                                -- :321
  (Child          : S → S → Type ℓ)                                   -- :368
  (isPropChild    : (x n : S) → isProp (Child x n))                   -- :371
  (child-entry    : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)     -- :369
  (child-wf       : WellFounded Child)                                -- :392
  (IsName         : S → Ω)                                            -- :461
  (name-shape     : (n : S) → ⟨ IsName n ⟩ → (e : S) → ⟨ e ∈ˢ n ⟩
                  → ∥ Σ[ x ∈ S ] Σ[ b ∈ S ]
                        (e ≡ entry x b) × ⟨ b ∈ˢ W ⟩ ∥₁)              -- :467
  (child-is-name  : (n : S) → ⟨ IsName n ⟩ → (x : S) → Child x n
                  → ⟨ IsName x ⟩)                                     -- :470
  where


  -- The carrier, spelled here rather than taken as a parameter. It is Track
  -- A's Name definitionally, because IsName is the same predicate and the
  -- Σ-type is the same Σ-type; the package still contains exactly one name
  -- predicate and exactly one name carrier.

  Name : Type ℓ
  Name = Σ[ n ∈ S ] ⟨ IsName n ⟩

  Childᴾ : S → S → Ω
  Childᴾ x n = Child x n , isPropChild x n

  -- ---------------------------------------------------------------------
  -- The entry index
  -- ---------------------------------------------------------------------

  -- The support is not the index. A name is a set of entries and two distinct
  -- entries may carry the same subname at different weights; the support
  -- collapses them and the index does not. K0 separated the two for exactly
  -- this reason (k0-internal-names-probes-2026-09.md:47-48), and every
  -- statement about weights below is indexed by an entry.
  --
  -- Decoding an entry is where injectivity is spent. The shape clause of
  -- IsName offers a decomposition of each member only under a truncation, and
  -- a truncation eliminates only into a proposition; entry-inj is what makes
  -- the decomposition a proposition, so the truncation can be removed and the
  -- coordinates become terms. Without it there would be no `child` and no
  -- `weight`, only their truncations.

  Entryᴺ : S → Type ℓ
  Entryᴺ e = Σ[ x ∈ S ] Σ[ b ∈ S ] (e ≡ entry x b) × ⟨ b ∈ˢ W ⟩

  isPropEntryᴺ : (e : S) → isProp (Entryᴺ e)
  isPropEntryᴺ e (x , b , q , hb) (x' , b' , q' , hb') =
    Σ≡Prop inner (fst (entry-inj (sym q ∙ q')))
    where
      inner : (y : S) → isProp (Σ[ c ∈ S ] (e ≡ entry y c) × ⟨ c ∈ˢ W ⟩)
      inner y (c , r , hc) (c' , r' , hc') =
        Σ≡Prop (λ d → isProp× (isSetS e (entry y d)) (snd (d ∈ˢ W)))
               (snd (entry-inj (sym r ∙ r')))

  Index : Name → Type ℓ
  Index τ = Σ[ e ∈ S ] ⟨ e ∈ˢ fst τ ⟩

  decodeEntry : (τ : Name) (i : Index τ) → Entryᴺ (fst i)
  decodeEntry τ (e , m) =
    PT.rec (isPropEntryᴺ e) (λ r → r) (name-shape (fst τ) (snd τ) e m)

  raw-child : (τ : Name) (i : Index τ) → Child (fst (decodeEntry τ i)) (fst τ)
  raw-child τ i =
    child-entry (fst d) (fst (snd d)) (fst τ)
      (mem-substˡ (fst (snd (snd d))) (snd i))
    where
      d : Entryᴺ (fst i)
      d = decodeEntry τ i

  child : (τ : Name) → Index τ → Name
  child τ i = fst (decodeEntry τ i) ,
    child-is-name (fst τ) (snd τ) (fst (decodeEntry τ i)) (raw-child τ i)

  -- The weight is a function of the ENTRY and of nothing smaller. There is no
  -- map from a subname to a weight in this file and there must be none in K3:
  -- a name may weight one subname many times, and choosing a representative
  -- would be a choice the theory does not make and the reverse translation
  -- could not undo.

  weight : (τ : Name) → Index τ → Σ[ b ∈ S ] ⟨ b ∈ˢ W ⟩
  weight τ i = fst (snd (decodeEntry τ i)) , snd (snd (snd (decodeEntry τ i)))

  represents : (τ : Name) (i : Index τ)
             → fst i ≡ entry (fst (child τ i)) (fst (weight τ i))
  represents τ i = fst (snd (snd (decodeEntry τ i)))

  decreases : (τ : Name) (i : Index τ) → Child (fst (child τ i)) (fst τ)
  decreases = raw-child

  -- Recursion over a name through its entries. This is Track A's Rec with the
  -- edge relation replaced by the index: the step function is handed one
  -- value for each ENTRY of τ rather than one for each child, which is the
  -- shape every later definition by recursion over a name wants, because the
  -- weight of the entry is available in the same breath.
  --
  -- Nothing here produces a name by recursion; `elim` consumes names and the
  -- only names this file builds, `subname` and `child`, are projections of a
  -- code that already exists. That is why child-wf suffices and why no
  -- member-image datum appears in the ledger.

  module Elim {ℓp} (P : Name → Type ℓp)
    (step : (τ : Name) → ((i : Index τ) → P (child τ i)) → P τ) where

    Motive : S → Type (ℓ-max ℓ ℓp)
    Motive n = (v : ⟨ IsName n ⟩) → P (n , v)

    rawStep : (n : S) → ((x : S) → Child x n → Motive x) → Motive n
    rawStep n below v = step (n , v)
      (λ i → below (fst (child (n , v) i)) (decreases (n , v) i)
                   (snd (child (n , v) i)))

    result : (τ : Name) → P τ
    result τ = WFI.induction child-wf {P = Motive} rawStep (fst τ) (snd τ)

  elim : {ℓp : Level} (P : Name → Type ℓp)
       → ((τ : Name) → ((i : Index τ) → P (child τ i)) → P τ)
       → (τ : Name) → P τ
  elim P step = Elim.result P step


  -- ---------------------------------------------------------------------
  -- The ground enters here
  -- ---------------------------------------------------------------------

  -- Everything above is a decoding. Everything below builds a ground set, and
  -- the two extra kernel facts are exactly the two that a ground set needs:
  -- entry-isKPair to see the kernel's entry through the object language, and
  -- child-weight to get a weight out of a bare edge.

  module WithGround (𝔊 : Sets)
    (entry-isKPair : (x b : S) → ⟨ isKPairΔ (entry x b) x b ⟩)         -- :332
    (child-weight  : (x n : S) → Child x n
                   → ∥ Σ[ b ∈ S ] ⟨ entry x b ∈ˢ n ⟩ ∥₁)              -- :369
    where

    open Sets 𝔊 using ( core; hasUnion; hasSeparation )
    open Determinacy core public

    -- ---------------------------------------------------------------------
    -- The double union and the bound
    -- ---------------------------------------------------------------------

    -- Union is an existence axiom and arrives truncated like every other, so
    -- the union set is a description and is sealed with its specification. The
    -- class argument is written out; leaving it implicit is a measured failure
    -- (GroundDescription.agda:113-121).

    opaque
      ⋃ᴳ : S → S
      ⋃ᴳ a = the (λ x → ⋁ S (λ y → (y ∈ˢ a) ⊓ (x ∈ˢ y))) (hasUnion a)

      ⋃ᴳ-spec : (a x : S) → (x ∈ˢ ⋃ᴳ a) ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ (x ∈ˢ y))
      ⋃ᴳ-spec a = the-spec (λ x → ⋁ S (λ y → (y ∈ˢ a) ⊓ (x ∈ˢ y))) (hasUnion a)

    ⋃ᴳ-in : (a y x : S) → ⟨ y ∈ˢ a ⟩ → ⟨ x ∈ˢ y ⟩ → ⟨ x ∈ˢ ⋃ᴳ a ⟩
    ⋃ᴳ-in a y x hy hx = subst ⟨_⟩ (sym (⋃ᴳ-spec a x)) ∣ y , hy , hx ∣₁

    ⋃² : S → S
    ⋃² a = ⋃ᴳ (⋃ᴳ a)

    -- The roadmap's subname bound, as a literal theorem, and its companion for
    -- the weight. Both are two ∈-steps and both come out of ONE fact: the entry
    -- is an internal Kuratowski pair. The first clause of isKPairΔ hands over a
    -- member of the entry containing x, the second a member containing b, so
    -- neither proof needs to know that those members are the singleton and the
    -- unordered pair, and neither touches the sealed pairing term. This is the
    -- entire use of Track A's extra lemma entry-isKPair, and it is why that
    -- lemma being delivered mattered to this track.

    support-bound : (n x b : S) → ⟨ entry x b ∈ˢ n ⟩ → ⟨ x ∈ˢ ⋃² n ⟩
    support-bound n x b h = PT.rec (snd (x ∈ˢ ⋃² n))
      (λ { (w , hw , hx , _) →
             ⋃ᴳ-in (⋃ᴳ n) w x (⋃ᴳ-in n (entry x b) w h hw) hx })
      (fst (entry-isKPair x b))

    weight-bound : (n x b : S) → ⟨ entry x b ∈ˢ n ⟩ → ⟨ b ∈ˢ ⋃² n ⟩
    weight-bound n x b h = PT.rec (snd (b ∈ˢ ⋃² n))
      (λ { (w , hw , _ , hb , _) →
             ⋃ᴳ-in (⋃ᴳ n) w b (⋃ᴳ-in n (entry x b) w h hw) hb })
      (fst (snd (entry-isKPair x b)))

    -- ---------------------------------------------------------------------
    -- The coded entry, recovered as a term
    -- ---------------------------------------------------------------------

    -- Determinacy plus Track A's entry-isKPair: a set the object language reads
    -- as the Kuratowski pair of x and b IS the kernel's entry. This is the one
    -- line that lets a Separation over childAtˢ produce a Child, and it is
    -- where the coded layer and the term layer meet.

    kpair-unique : (q x b : S) → ⟨ isKPairΔ q x b ⟩ → q ≡ entry x b
    kpair-unique q x b h = kpair-det q (entry x b) x b h (entry-isKPair x b)

    -- ---------------------------------------------------------------------
    -- The support
    -- ---------------------------------------------------------------------

    -- The separation class, as a Formula S 1 with n and W frozen into constant
    -- slots. K2's sepAt is the only way to do this: there is no substitution in
    -- the tree, so a con-parameterized formula cannot be nested under a binder,
    -- and every K3 formula is one variable-indexed Formula S k instantiated at
    -- the end (CodedVocabulary.agda:534-551).

    supportFo : S → Formula S 1
    supportFo n = sepAt (childAtˢ zero (suc zero) (suc (suc zero))) (n ∷ W ∷ [])

    Δ₀-supportFo : (n : S) → Δ₀ (supportFo n)
    Δ₀-supportFo n =
      Δ₀-sepAt (Δ₀-childAtˢ zero (suc zero) (suc (suc zero))) (n ∷ W ∷ [])

    -- The support itself. TOTAL: there is no ⟨ IsName n ⟩ premise anywhere in
    -- the definition or in its specification, so support is defined on every
    -- ground code, well formed or not. On a malformed code it is simply the set
    -- of first coordinates of those members that happen to be Kuratowski pairs
    -- with a weight in W, which is the right answer rather than a defect: the
    -- recognizer of Track C must be free to ask about arbitrary codes.

    opaque
      support : S → S
      support n = separateOf hasSeparation (⋃² n) (supportFo n)

      support-spec : (n x : S)
                   → (x ∈ˢ support n) ≡ ((x ∈ˢ ⋃² n) ⊓ childΔ W n x)
      support-spec n x =
        separateOf-spec hasSeparation (⋃² n) (supportFo n) x
        ∙ cong ((x ∈ˢ ⋃² n) ⊓_)
            (sepAt-reading (childAtˢ zero (suc zero) (suc (suc zero)))
                           (n ∷ W ∷ []) x)

    support-⊆ : (n : S) → ⟨ support n ⊆ˢ ⋃² n ⟩
    support-⊆ n x m = fst (subst ⟨_⟩ (support-spec n x) m)

    -- Out is unconditional and in is not, and the asymmetry is exactly the
    -- clause b ∈ W. A child of n arrives with a weight, but nothing in the bare
    -- relation says the weight lies in the carrier; only the shape half of
    -- IsName does. Out needs no such clause, because the coded side already
    -- carries it.

    support-out : (n x : S) → ⟨ x ∈ˢ support n ⟩ → Child x n
    support-out n x m = PT.rec (isPropChild x n)
      (λ { (e , he , inner) → PT.rec (isPropChild x n)
             (λ { (b , _ , hk) →
                    child-entry x b n (mem-substˡ (kpair-unique e x b hk) he) })
             inner })
      (snd (subst ⟨_⟩ (support-spec n x) m))

    support-in : (n : S) → ⟨ IsName n ⟩ → (x : S) → Child x n
               → ⟨ x ∈ˢ support n ⟩
    support-in n hn x edge = subst ⟨_⟩ (sym (support-spec n x))
      (PT.rec (snd ((x ∈ˢ ⋃² n) ⊓ childΔ W n x)) fromEntry (child-weight x n edge))
      where
        -- The weight of a present entry lies in W. Injectivity of the entry is
        -- spent here and only here on the support side: the shape clause offers
        -- SOME decomposition of the member entry x b, and entry-inj says that
        -- decomposition is the one we started with.
        inCarrier : (b : S) → ⟨ entry x b ∈ˢ n ⟩ → ⟨ b ∈ˢ W ⟩
        inCarrier b h = PT.rec (snd (b ∈ˢ W))
          (λ { (x' , b' , q , hb') →
                 subst (λ z → ⟨ z ∈ˢ W ⟩) (sym (snd (entry-inj q))) hb' })
          (name-shape n hn (entry x b) h)

        fromEntry : Σ[ b ∈ S ] ⟨ entry x b ∈ˢ n ⟩
                  → ⟨ (x ∈ˢ ⋃² n) ⊓ childΔ W n x ⟩
        fromEntry (b , h) =
          support-bound n x b h ,
          ∣ entry x b , h , ∣ b , inCarrier b h , entry-isKPair x b ∣₁ ∣₁

    support-valid : (n : S) → ⟨ IsName n ⟩ → (x : S) → ⟨ x ∈ˢ support n ⟩
                  → ⟨ IsName x ⟩
    support-valid n hn x m = child-is-name n hn x (support-out n x m)

    subname : (τ : Name) → Σ[ x ∈ S ] ⟨ x ∈ˢ support (fst τ) ⟩ → Name
    subname τ (x , m) = x , support-valid (fst τ) (snd τ) x m

    -- ---------------------------------------------------------------------
    -- The adapter between the host index and the coded index
    -- ---------------------------------------------------------------------

    -- Two ways to index the subnames of a name: by the host relation, and by
    -- membership in the ground code. For a name they agree, and the agreement
    -- is a path of TYPES rather than a logical equivalence, because only a type
    -- can be handed to Separation's index or to a family of weights.
    --
    -- The level is the point of the exercise and it is why `fam` is given an
    -- explicit type below. Both sides are at Type ℓ: Child lands in Type ℓ by
    -- Track A's declaration, and ⟨ x ∈ˢ support n ⟩ is the carrier of an
    -- element of Ω, which is Type ℓ as well. A support written as a host
    -- predicate S → Ω would instead land at Type (ℓ-suc ℓ), since Ω = hProp ℓ,
    -- and could not index ⋁ or an admitted family at all. That is the whole
    -- reason the support is a ground CODE and not a host predicate.

    Subᴺ Supᴺ : S → Type ℓ
    Subᴺ n = Σ[ x ∈ S ] Child x n
    Supᴺ n = Σ[ x ∈ S ] ⟨ x ∈ˢ support n ⟩

    support-adapter : (n : S) → ⟨ IsName n ⟩ → Subᴺ n ≡ Supᴺ n
    support-adapter n hn = cong fam (funExt pointwise)
      where
        fam : (S → Type ℓ) → Type ℓ
        fam F = Σ[ x ∈ S ] F x

        pointwise : (x : S) → Child x n ≡ ⟨ x ∈ˢ support n ⟩
        pointwise x = cong ⟨_⟩
          (⇔toPath {P = Childᴾ x n} {Q = x ∈ˢ support n}
            (support-in n hn x) (support-out n x))


    -- ---------------------------------------------------------------------
    -- Bell's u(x) as a set of weights
    -- ---------------------------------------------------------------------

    -- Bell writes a B-valued set as a function u with u(x) the weight of x. In
    -- a material presentation there is no such function, and the honest
    -- replacement is the SET of weights at which x occurs in n. It is a
    -- separation on the weight carrier itself, so the clause b ∈ W is supplied
    -- by the bound and the formula asks only that some member of n is the pair
    -- of x with b.

    weightsFo : S → S → Formula S 1
    weightsFo n x = sepAt (weightAtˢ zero (suc zero) (suc (suc zero))) (n ∷ x ∷ [])

    Δ₀-weightsFo : (n x : S) → Δ₀ (weightsFo n x)
    Δ₀-weightsFo n x =
      Δ₀-sepAt (Δ₀-weightAtˢ zero (suc zero) (suc (suc zero))) (n ∷ x ∷ [])

    opaque
      weightsAt : S → S → S
      weightsAt n x = separateOf hasSeparation W (weightsFo n x)

      weightsAt-spec : (n x b : S)
                     → (b ∈ˢ weightsAt n x) ≡ ((b ∈ˢ W) ⊓ weightΔ n x b)
      weightsAt-spec n x b =
        separateOf-spec hasSeparation W (weightsFo n x) b
        ∙ cong ((b ∈ˢ W) ⊓_)
            (sepAt-reading (weightAtˢ zero (suc zero) (suc (suc zero)))
                           (n ∷ x ∷ []) b)

    weightsAt-sub : (n x : S) → ⟨ weightsAt n x ⊆ˢ W ⟩
    weightsAt-sub n x b m = fst (subst ⟨_⟩ (weightsAt-spec n x b) m)

    -- The support is the join of the weight families, and this is the theorem
    -- that says the two presentations are the same object. Left to right is a
    -- swap of two bounded existentials. Right to left is the swap plus the
    -- bound: a weight of x in n produces an entry of n, the entry is canonical
    -- by kpair-unique, and support-bound then places x inside ⋃²n, which is the
    -- clause the coded support carries and the weight family does not.

    support-is-join : (n x : S)
                    → (x ∈ˢ support n) ≡ ⋁ S (λ b → b ∈ˢ weightsAt n x)
    support-is-join n x = support-spec n x ∙ ⇔toPath fwd bwd
      where
        target : Ω
        target = ⋁ S (λ b → b ∈ˢ weightsAt n x)

        source : Ω
        source = (x ∈ˢ ⋃² n) ⊓ childΔ W n x

        fwd : ⟨ source ⟩ → ⟨ target ⟩
        fwd (_ , ch) = PT.rec (snd target)
          (λ { (e , he , inner) → PT.rec (snd target)
                 (λ { (b , hb , hk) →
                        ∣ b , subst ⟨_⟩ (sym (weightsAt-spec n x b))
                                (hb , ∣ e , he , hk ∣₁) ∣₁ })
                 inner })
          ch

        bwd : ⟨ target ⟩ → ⟨ source ⟩
        bwd = PT.rec (snd source)
          (λ { (b , m) → PT.rec (snd source)
                 (λ { (e , he , hk) →
                        support-bound n x b
                          (mem-substˡ (kpair-unique e x b hk) he)
                      , ∣ e , he , ∣ b , fst (decode b m) , hk ∣₁ ∣₁ })
                 (snd (decode b m)) })
          where
            decode : (b : S) → ⟨ b ∈ˢ weightsAt n x ⟩
                   → ⟨ (b ∈ˢ W) ⊓ weightΔ n x b ⟩
            decode b m = subst ⟨_⟩ (weightsAt-spec n x b) m


-- ---------------------------------------------------------------------
-- The instantiation against Track A
-- ---------------------------------------------------------------------

-- This module is a check and not a part of the mathematics: it discharges
-- every one of Track B's eleven kernel parameters from NameKernel.Kernel and
-- typechecks the result, so the correspondence is machine-verified rather
-- than read off two files by eye. Nine parameters are discharged by a name,
-- and the two Child laws by one constructor each, which is what it means for
-- Child to be the truncated existential over the weight.
--
-- The accessibility datum appears HERE and nowhere above. Track B consumes
-- WellFounded Child, which Track A derives from WellFounded _∈ᵗ_ through the
-- three membership steps; the tier-0 realization datum is needed to build the
-- kernel, not to build the support.

module Instantiate (𝔊 : Sets) (acc∈ : Accessibility) (W : S) where

  open Sets 𝔊 using ( core )

  module K = NK.Kernel core acc∈ W

  module B = Names W
    K.entry K.entry-inj
    K.Child K.isPropChild (λ x b n h → ∣ b , h ∣₁)
    K.child-wf
    K.IsName K.name-shape K.child-is-name

  module BG = B.WithGround 𝔊 K.entry-isKPair (λ x n e → e)

  -- The carrier Track B spells out is Track A's, on the nose.

  name-agrees : B.Name ≡ K.Name
  name-agrees = refl

{-# OPTIONS --cubical --safe --guardedness #-}

-- K4 Track B: admitted families, value sets and bound independence.
--
-- WHAT THIS FILE IS FOR. A Boolean value is produced by a JOIN over a host
-- family of names, and the coded completion has no host-indexed join: supᴮ
-- takes a ground CODE and a proof that the code is a subset of the algebra
-- (Certificate.agda:194-209, CodedCompletion.agda:820). So before any value
-- of a quantified formula can be written down, two questions have to be
-- settled, and this module settles them.
--
--   1. EXISTENCE. Is there a ground set whose members are exactly the values
--      attained by the family? That set is Admits.values below, and its
--      specification Admits.attained is an equation between truth values, not
--      a selection of witnesses.
--   2. INDEPENDENCE. If two different host index types attain the same class
--      of values, do they give the same element? That is join-presented and
--      meet-presented, proved with no comparison of the index types at all.
--
-- K0'S WARNING, AND THE SHAPE THAT HONOURS IT. K0 checked one instance of the
-- attained-value construction and said in its own words what it did NOT do:
-- "A supremum is not asserted to be attained by a name with top truth value"
-- and "The actual L set is obtained from the existing ground Separation
-- operation; it is not extracted by choosing witnesses from the attained-value
-- relation" (k0-atomic-value-set-2026-09.md). Collecting the attained values
-- does not select a witness for each value, and a bounded join alone does not
-- produce a maximum-principle witness.
--
-- That warning is enforced structurally here rather than by a comment. The
-- attainment field is a path into ⋁ I, which is a propositional truncation, so
-- the only eliminator this file exposes for it is attained-elim, whose target
-- is an element of Ω. There is no operation anywhere below that takes a member
-- of a value set to an index, and neither of the two names this package
-- reserves for a witness selection principle occurs anywhere in the file; the
-- grep ledger for that claim is in this track's report. What the file proves
-- is exactly the pair of adequacy halves
-- K0 names: admits-occurs, that every semantic value occurs in the set, and
-- admits-sound, that every collected value merely comes from a family member.
--
-- THE ALGEBRA ENTERS AS TRACK A'S RECORDS, taken as parameters of the inner
-- module Core. Records are GENERATIVE: two structurally identical record
-- declarations are two incompatible types, so K4.Algebra is the single source
-- and this file declares no algebra record of its own. A record parameter is
-- still a variable that cannot unfold, so project rule 2 is served exactly as
-- a flat parameter list would serve it, and every projection out of Kc below
-- is neutral.
--
-- Measured consequence, worth recording, because it is the ledger this track
-- is accountable for: Track B consumes NO lattice field and NO complement at
-- all. The Lattice parameter is present only because K4.Algebra indexes
-- CodedComplete by it so that tracks C, F, I and J can write one uniform
-- telescope; no field of it is ever projected here, and
-- `grep -c "Lattice\." K4/ValueSets.agda` returns 0. Nothing below mentions
-- the meet, the join, the complement, the top or the bottom of the lattice,
-- by any spelling.
--
-- PROJECT RULE 3, discharged structurally. supᴮ and infᴮ appear in the types
-- of admits-ub, admits-lub, admits-lb, admits-glb, join-presented and
-- meet-presented, and in every one of those occurrences they are applied to a
-- projection out of a VARIABLE, never out of a constructed record. Admits has
-- three fields and no derived join field, so no type in this file can name the
-- join of a family built on the spot.
--
-- Hypotheses, and this is the whole list at module level: the structure,
-- ordinary Extensionality and the path realization of the structure equality.
-- These are exactly GroundDescription's and NameImage's. Separation and
-- Collection are arguments of the theorems that consume them and are never
-- module parameters. Nothing is imported from the constructible universe or
-- the von Neumann layers, no ambient model record is taken, no classical
-- hypothesis is taken at any level, and no power set, union, pairing,
-- accessibility or name layer enters. This track's report carries the grep
-- ledger that checks each of those absences and reports its count.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import K4.Algebra

module K4.ValueSets
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

open import OrdinaryProfile 𝒮
  using ( iff; Separation; Collection; ≈ˢ-refl; module PathRealization )
open PathRealization paths using ( ≈ˢ-to-path; path-to-≈ˢ )

open import GroundDescription 𝒮 ext paths
  using ( SetExists; the; the-spec; ext-path
        ; separateOf; separateOf-spec; hasImage′ )

-- Track A's algebra layer, opened WITHOUT public. Re-exporting a record TYPE
-- name makes its record module reachable by two routes and a consumer that
-- opens both fails as ambiguous even though both names denote the same
-- record, so nothing from K4.Algebra is re-exported here. Pt, Pt≡ and _≤ᴮ_
-- come from there and are not re-declared: they are plain definitions and
-- would unfold to the same types, but a second copy in scope is a second name
-- for a consumer to disambiguate, for no gain.

open import K4.Algebra 𝒮
  using ( Pt; Pt≡; _≤ᴮ_; ≤ᴮ-refl; ⊆ˢ-trans
        ; Lattice; CodedComplete )

-- ---------------------------------------------------------------------
-- Antisymmetry
-- ---------------------------------------------------------------------

-- The one algebra fact this file proves rather than receives. It is the same
-- two line term as K4/Implication.agda:102-103, kept here because that file's
-- telescope demands a Lattice AND a Complement, and Track B consumes neither;
-- importing it would put a complement in this track's ledger for a lemma that
-- reads only the order. It is a plain definition and not a record, so no
-- generativity question arises: the two terms are interchangeable.
--
-- This is where the module's two ground hypotheses are spent, and it is spent
-- nowhere else. Every uniqueness statement below routes through it, which is
-- project rule 1 observed: a value equation is proved by squeezing between
-- the same bounds, never by a congruence over an algebra operation.

≤ᴮ-antisym : {a : S} {u v : Pt a} → ⟨ u ≤ᴮ v ⟩ → ⟨ v ≤ᴮ u ⟩ → u ≡ v
≤ᴮ-antisym h k = Pt≡ (ext-path (λ x → ⇔toPath (h x) (k x)))

-- ---------------------------------------------------------------------
-- The crossing helpers
-- ---------------------------------------------------------------------

-- Project rules 1 and 4 meet in these three lemmas, so each is named once
-- with a written out type and every endpoint of every ⇔toPath below is a
-- local with an explicit Ω annotation. Rule 4 first: a join that binds a
-- membership witness is indexed by the membership PROPOSITION, so the inner
-- index of the member class is ⟨ x ∈ˢ a ⟩ and not S. NameKernel.agda:125-135
-- records that the other spelling does not typecheck at all, and
-- NameImage.agda:232-233 carries the corrected form. Rule 1 second: an
-- element of Ω is a pair of a type and a proof that the type is a
-- proposition, so unifying the goal fixes only the carrier half and leaves
-- the isProp half an unsolved metavariable unless the endpoints are named.

-- The unchanged endpoint, named once. This is the preamble's prescribed
-- remedy for rule 1: a bare reflexivity inside a congruence over a truth
-- value operation leaves the propositionality component unsolved, because an
-- element of Ω is a pair and unifying the goal fixes the carrier half only.

same : (P : Ω) → P ≡ P
same P = refl

-- The fibre of a class over the carrier. Every index type this package uses
-- has this shape, and that is why every one of them is at Type ℓ and fills
-- the index slot of ⋀ and ⋁ exactly.

Fib : (S → Ω) → Type ℓ
Fib P = Σ[ x ∈ S ] ⟨ P x ⟩

-- A join over the proofs of a proposition is a meet with that proposition.

guard : (P Q : Ω) → (⋁ ⟨ P ⟩ (λ _ → Q)) ≡ (P ⊓ Q)
guard P Q = ⇔toPath fwd bwd
  where
    lhs rhs : Ω
    lhs = ⋁ ⟨ P ⟩ (λ _ → Q)
    rhs = P ⊓ Q

    fwd : ⟨ lhs ⟩ → ⟨ rhs ⟩
    fwd = PT.rec (snd rhs) (λ { (h , q) → h , q })

    bwd : ⟨ rhs ⟩ → ⟨ lhs ⟩
    bwd = λ { (h , q) → ∣ h , q ∣₁ }

-- The crossing itself, over an arbitrary class and not only over membership
-- in a code. The generality is not decoration. The compiler's existential
-- node crosses at the NAME recogniser, which is a class on the carrier and is
-- not of the form (_∈ˢ a) for any a, so a crossing lemma stated only for
-- membership does not reach it. The membership case is recovered below under
-- the architecture's own name.
--
-- The left side is the shape a ground membership specification arrives in,
-- with the member and its membership proof bound separately; the right side
-- is the shape an admitted family wants, with one index type at Type ℓ.

collapseᴾ : (P : S → Ω) (Q : (x : S) → ⟨ P x ⟩ → Ω)
          → ⋁ S (λ x → ⋁ ⟨ P x ⟩ (λ h → Q x h))
          ≡ ⋁ (Fib P) (λ p → Q (fst p) (snd p))
collapseᴾ P Q = ⇔toPath fwd bwd
  where
    lhs rhs : Ω
    lhs = ⋁ S (λ x → ⋁ ⟨ P x ⟩ (λ h → Q x h))
    rhs = ⋁ (Fib P) (λ p → Q (fst p) (snd p))

    fwd : ⟨ lhs ⟩ → ⟨ rhs ⟩
    fwd = PT.rec (snd rhs)
      (λ { (x , t) → PT.rec (snd rhs) (λ { (h , q) → ∣ (x , h) , q ∣₁ }) t })

    bwd : ⟨ rhs ⟩ → ⟨ lhs ⟩
    bwd = PT.rec (snd lhs) (λ { (p , q) → ∣ fst p , ∣ snd p , q ∣₁ ∣₁ })

-- The crossing a compiled quantifier actually needs, in one step. A formula
-- cut out by Separation reads as a guarded class whose second factor does NOT
-- mention the witness, because a formula has no access to it; the value of a
-- subformula at a name DOES mention the witness, because the name is a code
-- together with its recognition proof. The hypothesis is exactly a reading
-- theorem: at every code that the class accepts, and for every proof that it
-- accepts it, the formula's reading agrees with the value statement.
--
-- Rule 4 is discharged on the right: the join binds the recognition proof and
-- is indexed by the fibre, never by the carrier.

collapse-reading : (P R : S → Ω) (Q : (x : S) → ⟨ P x ⟩ → Ω)
                 → ((x : S) (h : ⟨ P x ⟩) → R x ≡ Q x h)
                 → ⋁ S (λ x → P x ⊓ R x)
                 ≡ ⋁ (Fib P) (λ p → Q (fst p) (snd p))
collapse-reading P R Q rd = ⇔toPath fwd bwd
  where
    lhs rhs : Ω
    lhs = ⋁ S (λ x → P x ⊓ R x)
    rhs = ⋁ (Fib P) (λ p → Q (fst p) (snd p))

    fwd : ⟨ lhs ⟩ → ⟨ rhs ⟩
    fwd = PT.rec (snd rhs)
      (λ { (x , (h , r)) → ∣ (x , h) , subst ⟨_⟩ (rd x h) r ∣₁ })

    bwd : ⟨ rhs ⟩ → ⟨ lhs ⟩
    bwd = PT.rec (snd lhs)
      (λ { (p , q) → ∣ fst p
                     , (snd p , subst ⟨_⟩ (sym (rd (fst p) (snd p))) q) ∣₁ })

-- The case where the value statement does not depend on the witness after
-- all. The unchanged endpoint goes through `same`, which is the whole point
-- of naming it.

collapseᴾ-const : (P R : S → Ω)
                → ⋁ S (λ x → P x ⊓ R x)
                ≡ ⋁ (Fib P) (λ p → R (fst p))
collapseᴾ-const P R =
  collapse-reading P R (λ x _ → R x) (λ x _ → same (R x))

-- The two membership specializations, under the architecture's names. Fib of
-- a membership class is Pt of the code, definitionally, so a consumer may mix
-- the two spellings freely.

collapse : (a : S) (Q : (x : S) → ⟨ x ∈ˢ a ⟩ → Ω)
         → ⋁ S (λ x → ⋁ ⟨ x ∈ˢ a ⟩ (λ h → Q x h))
         ≡ ⋁ (Pt a) (λ p → Q (fst p) (snd p))
collapse a = collapseᴾ (λ x → x ∈ˢ a)

collapse-const : (a : S) (R : S → Ω)
               → ⋁ S (λ x → (x ∈ˢ a) ⊓ R x)
               ≡ ⋁ (Pt a) (λ p → R (fst p))
collapse-const a = collapseᴾ-const (λ x → x ∈ˢ a)

-- ---------------------------------------------------------------------
-- The algebra, flat
-- ---------------------------------------------------------------------

-- The uniform K4 telescope. L is named and never projected; Kc supplies the
-- six operations, opened below so that every occurrence of supᴮ and infᴮ in a
-- type is a projection out of the VARIABLE Kc, which is neutral.

module Core (B : S) (L : Lattice B) (Kc : CodedComplete B L) where

  open CodedComplete Kc

  -- ---------------------------------------------------------------------
  -- Admitted families
  -- ---------------------------------------------------------------------

  -- Three fields and no derived join or meet field. A derived join field is
  -- exactly the declaration K3 could not elaborate (NameWeight.agda:474-499
  -- against the shape at CodedCompletion.agda:951-983), so the join is never
  -- named inside a type; it is characterised, by admits-ub and admits-lub.
  --
  -- The level is forced, not chosen. attained is a path in Ω = hProp ℓ, which
  -- lives at Type (ℓ-suc ℓ), so Admits lands at Type (ℓ-suc ℓ) and can never
  -- index ⋁ or ⋀, whose index slot is Type ℓ. Admits is consumed as a
  -- hypothesis and produced as a result, and is never placed inside a join.

  record Admits {I : Type ℓ} (val : I → Pt B) : Type (ℓ-suc ℓ) where
    field
      values     : S
      values-sub : ⟨ values ⊆ˢ B ⟩
      attained   : (b : S) → (b ∈ˢ values) ≡ ⋁ I (λ k → b ≈ˢ fst (val k))

  -- The first half of adequacy, on a bare attainment specification: every
  -- value of the family really occurs in the set. This is where ordinary
  -- Extensionality is spent, through reflexivity of the structure equality,
  -- and it is the same step as CodedCompletion.agda:932-934.

  attained-mem : {I : Type ℓ} (val : I → Pt B) (v : S)
               → ((b : S) → (b ∈ˢ v) ≡ ⋁ I (λ k → b ≈ˢ fst (val k)))
               → (k : I) → ⟨ fst (val k) ∈ˢ v ⟩
  attained-mem {I} val v att k =
    subst ⟨_⟩ (sym (att (fst (val k)))) ∣ k , ≈ˢ-refl ext (fst (val k)) ∣₁

  -- The second half, and the exact place K0's warning bites. A member of the
  -- value set yields an index only under a truncation, so the ONLY eliminator
  -- offered is this one, whose target is an element of Ω and therefore a
  -- proposition. There is deliberately no variant returning an index, and
  -- adding one would be host Choice on the attained-value relation.

  attained-elim : {I : Type ℓ} (val : I → Pt B) (v : S)
                → ((b : S) → (b ∈ˢ v) ≡ ⋁ I (λ k → b ≈ˢ fst (val k)))
                → (b : S) → ⟨ b ∈ˢ v ⟩ → (T : Ω)
                → ((k : I) → b ≡ fst (val k) → ⟨ T ⟩) → ⟨ T ⟩
  attained-elim {I} val v att b hb T step =
    PT.rec (snd T)
      (λ { (k , e) → step k (≈ˢ-to-path b (fst (val k)) e) })
      (subst ⟨_⟩ (att b) hb)

  -- Every attained value is already a member of the algebra, whatever the
  -- index type was. This is the sentence "the values form a subset of the
  -- algebra even when the names range over the entire external carrier",
  -- proved rather than assumed: the family is Pt B valued, so its codes carry
  -- their membership in B along the structure equality.

  attained-in-B : {I : Type ℓ} (val : I → Pt B) (b : S)
                → ⟨ ⋁ I (λ k → b ≈ˢ fst (val k)) ⟩ → ⟨ b ∈ˢ B ⟩
  attained-in-B {I} val b =
    PT.rec (snd (b ∈ˢ B))
      (λ { (k , e) → subst (λ w → ⟨ w ∈ˢ B ⟩)
                       (sym (≈ˢ-to-path b (fst (val k)) e)) (snd (val k)) })

  -- ---------------------------------------------------------------------
  -- The four universal properties
  -- ---------------------------------------------------------------------

  -- Stated first on a bare set and its attainment law, so that a consumer
  -- that built its own value set, as the compiler's existential node does,
  -- never has to package an Admits record to use them. The record versions
  -- follow by projection.

  attained-ub : {I : Type ℓ} (val : I → Pt B) (v : S) (sub : ⟨ v ⊆ˢ B ⟩)
              → ((b : S) → (b ∈ˢ v) ≡ ⋁ I (λ k → b ≈ˢ fst (val k)))
              → (k : I) → ⟨ val k ≤ᴮ supᴮ v sub ⟩
  attained-ub {I} val v sub att k =
    sup-ub v sub (val k) (attained-mem val v att k)

  attained-lub : {I : Type ℓ} (val : I → Pt B) (v : S) (sub : ⟨ v ⊆ˢ B ⟩)
               → ((b : S) → (b ∈ˢ v) ≡ ⋁ I (λ k → b ≈ˢ fst (val k)))
               → (c : Pt B) → ((k : I) → ⟨ val k ≤ᴮ c ⟩)
               → ⟨ supᴮ v sub ≤ᴮ c ⟩
  attained-lub {I} val v sub att c hc = sup-lub v sub c step
    where
      step : (u : Pt B) → ⟨ fst u ∈ˢ v ⟩ → ⟨ u ≤ᴮ c ⟩
      step u hu = attained-elim val v att (fst u) hu (u ≤ᴮ c)
        (λ k e → subst (λ w → ⟨ w ⊆ˢ fst c ⟩) (sym e) (hc k))

  attained-lb : {I : Type ℓ} (val : I → Pt B) (v : S) (sub : ⟨ v ⊆ˢ B ⟩)
              → ((b : S) → (b ∈ˢ v) ≡ ⋁ I (λ k → b ≈ˢ fst (val k)))
              → (k : I) → ⟨ infᴮ v sub ≤ᴮ val k ⟩
  attained-lb {I} val v sub att k =
    inf-lb v sub (val k) (attained-mem val v att k)

  attained-glb : {I : Type ℓ} (val : I → Pt B) (v : S) (sub : ⟨ v ⊆ˢ B ⟩)
               → ((b : S) → (b ∈ˢ v) ≡ ⋁ I (λ k → b ≈ˢ fst (val k)))
               → (c : Pt B) → ((k : I) → ⟨ c ≤ᴮ val k ⟩)
               → ⟨ c ≤ᴮ infᴮ v sub ⟩
  attained-glb {I} val v sub att c hc = inf-glb v sub c step
    where
      step : (u : Pt B) → ⟨ fst u ∈ˢ v ⟩ → ⟨ c ≤ᴮ u ⟩
      step u hu = attained-elim val v att (fst u) hu (c ≤ᴮ u)
        (λ k e → subst (λ w → ⟨ fst c ⊆ˢ w ⟩) (sym e) (hc k))

  -- The record forms. Every occurrence of supᴮ and infᴮ in these four types
  -- is applied to a projection out of the VARIABLE a, which is neutral, and
  -- never to a constructed set or a constructed record: project rule 3.

  admits-ub : {I : Type ℓ} {val : I → Pt B} (a : Admits val) (k : I)
            → ⟨ val k ≤ᴮ supᴮ (Admits.values a) (Admits.values-sub a) ⟩
  admits-ub {I} {val} a =
    attained-ub val (Admits.values a) (Admits.values-sub a)
      (Admits.attained a)

  admits-lub : {I : Type ℓ} {val : I → Pt B} (a : Admits val) (c : Pt B)
             → ((k : I) → ⟨ val k ≤ᴮ c ⟩)
             → ⟨ supᴮ (Admits.values a) (Admits.values-sub a) ≤ᴮ c ⟩
  admits-lub {I} {val} a =
    attained-lub val (Admits.values a) (Admits.values-sub a)
      (Admits.attained a)

  admits-lb : {I : Type ℓ} {val : I → Pt B} (a : Admits val) (k : I)
            → ⟨ infᴮ (Admits.values a) (Admits.values-sub a) ≤ᴮ val k ⟩
  admits-lb {I} {val} a =
    attained-lb val (Admits.values a) (Admits.values-sub a)
      (Admits.attained a)

  admits-glb : {I : Type ℓ} {val : I → Pt B} (a : Admits val) (c : Pt B)
             → ((k : I) → ⟨ c ≤ᴮ val k ⟩)
             → ⟨ c ≤ᴮ infᴮ (Admits.values a) (Admits.values-sub a) ⟩
  admits-glb {I} {val} a =
    attained-glb val (Admits.values a) (Admits.values-sub a)
      (Admits.attained a)

  -- ---------------------------------------------------------------------
  -- The two halves of adequacy, named
  -- ---------------------------------------------------------------------

  -- K0 states the obligation as two directions and packages them as one
  -- equality of truth values. Both directions are recorded here under their
  -- own names, because a later track that proves only one of them has not
  -- proved adequacy, and the record field alone does not say which half is
  -- which.

  admits-occurs : {I : Type ℓ} {val : I → Pt B} (a : Admits val) (k : I)
                → ⟨ fst (val k) ∈ˢ Admits.values a ⟩
  admits-occurs {I} {val} a =
    attained-mem val (Admits.values a) (Admits.attained a)

  admits-sound : {I : Type ℓ} {val : I → Pt B} (a : Admits val) (b : S)
               → ⟨ b ∈ˢ Admits.values a ⟩
               → ∥ Σ[ k ∈ I ] b ≡ fst (val k) ∥₁
  admits-sound {I} {val} a b hb =
    attained-elim val (Admits.values a) (Admits.attained a) b hb
      (∥ Σ[ k ∈ I ] b ≡ fst (val k) ∥₁ , PT.squash₁)
      (λ k e → ∣ k , e ∣₁)

  admits-in-B : {I : Type ℓ} {val : I → Pt B} (a : Admits val) (b : S)
              → ⟨ b ∈ˢ Admits.values a ⟩ → ⟨ b ∈ˢ B ⟩
  admits-in-B a = Admits.values-sub a

  -- ---------------------------------------------------------------------
  -- Bound independence at the algebra
  -- ---------------------------------------------------------------------

  -- This, and not uniqueness of the join of one fixed family, is what
  -- deserves the name. Two DIFFERENT index types with the same attained class
  -- give the same element, and the proof compares no index with any other: it
  -- squeezes each element between the bounds of the other family.
  -- Generalizes NameWeight.agda:278-302 from one fixed weight set to an
  -- arbitrary pair of admitted families.

  join-presented : {I J : Type ℓ} {f : I → Pt B} {g : J → Pt B}
                 → (a : Admits f) (c : Admits g)
                 → ((b : S) → ⋁ I (λ k → b ≈ˢ fst (f k))
                            ≡ ⋁ J (λ j → b ≈ˢ fst (g j)))
                 → supᴮ (Admits.values a) (Admits.values-sub a)
                 ≡ supᴮ (Admits.values c) (Admits.values-sub c)
  join-presented {I} {J} {f} {g} a c agree = ≤ᴮ-antisym up down
    where
      fIn : (k : I) → ⟨ fst (f k) ∈ˢ Admits.values c ⟩
      fIn k = subst ⟨_⟩ (sym (Admits.attained c (fst (f k))))
                (subst ⟨_⟩ (agree (fst (f k)))
                  ∣ k , ≈ˢ-refl ext (fst (f k)) ∣₁)

      gIn : (j : J) → ⟨ fst (g j) ∈ˢ Admits.values a ⟩
      gIn j = subst ⟨_⟩ (sym (Admits.attained a (fst (g j))))
                (subst ⟨_⟩ (sym (agree (fst (g j))))
                  ∣ j , ≈ˢ-refl ext (fst (g j)) ∣₁)

      up : ⟨ supᴮ (Admits.values a) (Admits.values-sub a)
           ≤ᴮ supᴮ (Admits.values c) (Admits.values-sub c) ⟩
      up = admits-lub a (supᴮ (Admits.values c) (Admits.values-sub c))
             (λ k → sup-ub (Admits.values c) (Admits.values-sub c)
                      (f k) (fIn k))

      down : ⟨ supᴮ (Admits.values c) (Admits.values-sub c)
            ≤ᴮ supᴮ (Admits.values a) (Admits.values-sub a) ⟩
      down = admits-lub c (supᴮ (Admits.values a) (Admits.values-sub a))
               (λ j → sup-ub (Admits.values a) (Admits.values-sub a)
                        (g j) (gIn j))

  meet-presented : {I J : Type ℓ} {f : I → Pt B} {g : J → Pt B}
                 → (a : Admits f) (c : Admits g)
                 → ((b : S) → ⋁ I (λ k → b ≈ˢ fst (f k))
                            ≡ ⋁ J (λ j → b ≈ˢ fst (g j)))
                 → infᴮ (Admits.values a) (Admits.values-sub a)
                 ≡ infᴮ (Admits.values c) (Admits.values-sub c)
  meet-presented {I} {J} {f} {g} a c agree = ≤ᴮ-antisym up down
    where
      fIn : (k : I) → ⟨ fst (f k) ∈ˢ Admits.values c ⟩
      fIn k = subst ⟨_⟩ (sym (Admits.attained c (fst (f k))))
                (subst ⟨_⟩ (agree (fst (f k)))
                  ∣ k , ≈ˢ-refl ext (fst (f k)) ∣₁)

      gIn : (j : J) → ⟨ fst (g j) ∈ˢ Admits.values a ⟩
      gIn j = subst ⟨_⟩ (sym (Admits.attained a (fst (g j))))
                (subst ⟨_⟩ (sym (agree (fst (g j))))
                  ∣ j , ≈ˢ-refl ext (fst (g j)) ∣₁)

      up : ⟨ infᴮ (Admits.values a) (Admits.values-sub a)
           ≤ᴮ infᴮ (Admits.values c) (Admits.values-sub c) ⟩
      up = admits-glb c (infᴮ (Admits.values a) (Admits.values-sub a))
             (λ j → inf-lb (Admits.values a) (Admits.values-sub a)
                      (g j) (gIn j))

      down : ⟨ infᴮ (Admits.values c) (Admits.values-sub c)
            ≤ᴮ infᴮ (Admits.values a) (Admits.values-sub a) ⟩
      down = admits-glb a (infᴮ (Admits.values c) (Admits.values-sub c))
               (λ k → inf-lb (Admits.values c) (Admits.values-sub c)
                        (f k) (fIn k))

  -- ---------------------------------------------------------------------
  -- Admission is PROVED at a separated value set
  -- ---------------------------------------------------------------------

  -- The single most consequential statement in this file, and the one the
  -- architecture's compiler decision rests on. Separation always produces a
  -- GUARDED class: separateOf-spec reads the separated set as
  -- (b ∈ˢ B) ⊓ (the formula at b) (GroundDescription.agda:130-135), never as
  -- the bare class. An admitted family wants the bare class. The guard is
  -- redundant, and this is the proof: the family takes its values in Pt B, so
  -- anything merely equal to one of those values is already in B.
  --
  -- Consequence, stated plainly because four tracks turn on it: at a
  -- quantifier node there is no admission datum to supply and nothing to
  -- assume. Given the subformula's reading theorem, the value set is a
  -- Separation and its attainment law is a theorem.

  guarded→admits : {I : Type ℓ} {val : I → Pt B} (v : S)
                 → ((b : S) → (b ∈ˢ v)
                            ≡ ((b ∈ˢ B) ⊓ ⋁ I (λ k → b ≈ˢ fst (val k))))
                 → Admits val
  guarded→admits {I} {val} v gspec = record
    { values     = v
    ; values-sub = λ b hb → subst ⟨_⟩ (gspec b) hb .fst
    ; attained   = λ b → gspec b ∙ drop b }
    where
      drop : (b : S) → ((b ∈ˢ B) ⊓ ⋁ I (λ k → b ≈ˢ fst (val k)))
                     ≡ ⋁ I (λ k → b ≈ˢ fst (val k))
      drop b = ⇔toPath fwd bwd
        where
          lhs rhs : Ω
          lhs = (b ∈ˢ B) ⊓ ⋁ I (λ k → b ≈ˢ fst (val k))
          rhs = ⋁ I (λ k → b ≈ˢ fst (val k))

          fwd : ⟨ lhs ⟩ → ⟨ rhs ⟩
          fwd = snd

          bwd : ⟨ rhs ⟩ → ⟨ lhs ⟩
          bwd t = attained-in-B val b t , t

  -- The same statement with the set built rather than received. The
  -- description term and its specification are sealed together at the point
  -- of definition, which is project rule 2: an unsealed description term
  -- unfolds into a stuck truncation eliminator on a ground axiom field, and
  -- Track A of K3 measured 761 s at 1.05 GB with no result against 1.04 s
  -- sealed.

  opaque
    sepValues : Separation → Formula S 1 → S
    sepValues sep φ = separateOf sep B φ

    sepValues-spec : (sep : Separation) (φ : Formula S 1) (b : S)
                   → (b ∈ˢ sepValues sep φ) ≡ ((b ∈ˢ B) ⊓ ((b ∷ []) ⊨ φ))
    sepValues-spec sep φ = separateOf-spec sep B φ

  sepAdmits : (sep : Separation) {I : Type ℓ} {val : I → Pt B}
              (φ : Formula S 1)
            → ((b : S) → ((b ∷ []) ⊨ φ) ≡ ⋁ I (λ k → b ≈ˢ fst (val k)))
            → Admits val
  sepAdmits sep {I} {val} φ reading =
    guarded→admits (sepValues sep φ)
      (λ b → sepValues-spec sep φ b
           ∙ cong (λ w → (b ∈ˢ B) ⊓ w) (reading b))

  -- ---------------------------------------------------------------------
  -- The contract the atomic layer consumes
  -- ---------------------------------------------------------------------

  -- The class, written once. Rule 4 again: the inner index is the membership
  -- proposition, so that a value may depend on the proof that its argument is
  -- a member, which is exactly what a recursion over a well founded relation
  -- produces.

  ValueClass : (a : S) (f : Pt a → Pt B) (b : S) → Ω
  ValueClass a f b = ⋁ S (λ x → ⋁ ⟨ x ∈ˢ a ⟩ (λ h → b ≈ˢ fst (f (x , h))))

  -- What the atomic layer receives: an operation and its membership
  -- specification, and no information about how the operation was obtained.
  -- Neither discharge route is a field.

  record ValueSets : Type (ℓ-suc ℓ) where
    field
      attain      : (a : S) (f : Pt a → Pt B) → S
      attain-sub  : (a : S) (f : Pt a → Pt B) → ⟨ attain a f ⊆ˢ B ⟩
      attain-spec : (a : S) (f : Pt a → Pt B) (b : S)
                  → (b ∈ˢ attain a f) ≡ ValueClass a f b

  -- Any value set in the member indexed shape is an admitted family over the
  -- members of the code, and the crossing is the only content.
  --
  -- The subset proof is an ARGUMENT and not something this bridge derives.
  -- Measured, with the exact error in this track's report: deriving it makes
  -- supᴮ (attain V a f) (values-sub (admits V a f)) a different term from
  -- supᴮ (attain V a f) (attain-sub V a f), the two proofs of the same
  -- proposition are not definitionally equal, and every statement about the
  -- join of a contract's value set then fails to typecheck. The derivation is
  -- still available, one definition below, for a caller that has only a
  -- specification.

  valueSet→admits : (a : S) (f : Pt a → Pt B) (T : S) (sub : ⟨ T ⊆ˢ B ⟩)
                  → ((b : S) → (b ∈ˢ T) ≡ ValueClass a f b)
                  → Admits {I = Pt a} f
  valueSet→admits a f T sub spec = record
    { values     = T
    ; values-sub = sub
    ; attained   = att }
    where
      att : (b : S) → (b ∈ˢ T) ≡ ⋁ (Pt a) (λ p → b ≈ˢ fst (f p))
      att b = spec b ∙ collapse a (λ x h → b ≈ˢ fst (f (x , h)))

  -- A value set is inside the algebra whether or not anyone said so, for the
  -- same reason the guard of a separated set is redundant.

  valueSet-sub : (a : S) (f : Pt a → Pt B) (T : S)
               → ((b : S) → (b ∈ˢ T) ≡ ValueClass a f b)
               → ⟨ T ⊆ˢ B ⟩
  valueSet-sub a f T spec b hb =
    attained-in-B f b
      (subst ⟨_⟩ (spec b ∙ collapse a (λ x h → b ≈ˢ fst (f (x , h)))) hb)

  admits : (V : ValueSets) (a : S) (f : Pt a → Pt B) → Admits {I = Pt a} f
  admits V a f =
    valueSet→admits a f (ValueSets.attain V a f) (ValueSets.attain-sub V a f)
      (ValueSets.attain-spec V a f)

  -- The two universal properties directly on the contract, so that a consumer
  -- never has to write a projection out of a constructed Admits record in a
  -- type. Here attain is a projection out of the variable V applied to
  -- variables, which is neutral: project rule 3.

  attain-ub : (V : ValueSets) (a : S) (f : Pt a → Pt B) (p : Pt a)
            → ⟨ f p ≤ᴮ supᴮ (ValueSets.attain V a f)
                            (ValueSets.attain-sub V a f) ⟩
  attain-ub V a f = admits-ub (admits V a f)

  attain-lub : (V : ValueSets) (a : S) (f : Pt a → Pt B) (c : Pt B)
             → ((p : Pt a) → ⟨ f p ≤ᴮ c ⟩)
             → ⟨ supᴮ (ValueSets.attain V a f)
                      (ValueSets.attain-sub V a f) ≤ᴮ c ⟩
  attain-lub V a f = admits-lub (admits V a f)

  attain-lb : (V : ValueSets) (a : S) (f : Pt a → Pt B) (p : Pt a)
            → ⟨ infᴮ (ValueSets.attain V a f)
                     (ValueSets.attain-sub V a f) ≤ᴮ f p ⟩
  attain-lb V a f = admits-lb (admits V a f)

  attain-glb : (V : ValueSets) (a : S) (f : Pt a → Pt B) (c : Pt B)
             → ((p : Pt a) → ⟨ c ≤ᴮ f p ⟩)
             → ⟨ c ≤ᴮ infᴮ (ValueSets.attain V a f)
                           (ValueSets.attain-sub V a f) ⟩
  attain-glb V a f = admits-glb (admits V a f)

  -- Uniqueness of the value set, from Extensionality and nothing else. This
  -- is the second of the architecture's three bound independence theorems,
  -- and it is why the contract may be passed around as data with no coherence
  -- obligation. Proved as NameImage.agda:107-110 proves its own.

  values-unique : (V W : ValueSets) (a : S) (f : Pt a → Pt B)
                → ValueSets.attain V a f ≡ ValueSets.attain W a f
  values-unique V W a f = ext-path (λ b →
    ValueSets.attain-spec V a f b ∙ sym (ValueSets.attain-spec W a f b))

  -- ---------------------------------------------------------------------
  -- Route I: the tier four realization datum, flat, in one signature
  -- ---------------------------------------------------------------------

  -- The two arguments are the two fields of NameKernel.agda:136-142. They are
  -- not a parameter of this module, not a field of any record declared here,
  -- and they occur in this one signature only. The coordinator instantiates
  -- with member→values (MemberImage.image M) (MemberImage.image-spec M).
  --
  -- The datum is NOT derivable from Collection: Collection reads a
  -- Formula S 2 and a host function has none (OrdinaryProfile.agda:95-101,
  -- NameKernel.agda:118-124). Nothing below presents it as derivable.

  member→values :
      (image : (a : S) (g : Pt a → S) → S)
    → (image-spec : (a : S) (g : Pt a → S) (z : S)
                  → (z ∈ˢ image a g)
                  ≡ ⋁ S (λ x → ⋁ ⟨ x ∈ˢ a ⟩ (λ h → z ≈ˢ g (x , h))))
    → ValueSets
  member→values image image-spec = record
    { attain      = λ a f → image a (λ p → fst (f p))
    ; attain-sub  = sub
    ; attain-spec = λ a f b → image-spec a (λ p → fst (f p)) b }
    where
      sub : (a : S) (f : Pt a → Pt B) → ⟨ image a (λ p → fst (f p)) ⊆ˢ B ⟩
      sub a f z hz =
        attained-in-B f z
          (subst ⟨_⟩
            (image-spec a (λ p → fst (f p)) z
              ∙ collapse a (λ x h → z ≈ˢ fst (f (x , h))))
            hz)

  -- ---------------------------------------------------------------------
  -- Route G: a definable graph, one code and one function at a time
  -- ---------------------------------------------------------------------

  -- MEASURED NEGATIVE, recorded in the file it concerns. The architecture's
  -- section 1.3 asks for
  --   graph→values : Collection → Separation
  --                → (γ : (a : S) → Formula S 2) → (reading : …) → ValueSets
  -- and that statement is refuted by the architecture's own trap 1 for this
  -- track. ValueSets.attain quantifies over EVERY host function
  -- f : Pt a → Pt B, while γ is fixed before f is given, so the set built
  -- from γ a cannot vary with f while the class ValueClass a f does. Two
  -- constant functions with different codes at a nonempty a already separate
  -- them. Route G therefore discharges one pair (a , f) at a time, which is
  -- what a recursion actually needs, and it is stated that way here. Route I
  -- remains the only route to the total contract, and that is the content of
  -- tier four.

  record ValueGraph (a : S) (f : Pt a → Pt B) : Type ℓ where
    field
      graph   : Formula S 2
      defines : (p : Pt a) → ⟨ (fst (f p) ∷ fst p ∷ []) ⊨ graph ⟩
      only    : (p : Pt a) (y : S)
              → ⟨ (y ∷ fst p ∷ []) ⊨ graph ⟩ → y ≡ fst (f p)

  opaque
    graph→valueSet : Collection → Separation
                   → (a : S) (f : Pt a → Pt B) → ValueGraph a f
                   → Σ[ T ∈ S ] ((b : S) → (b ∈ˢ T) ≡ ValueClass a f b)
    graph→valueSet coll sep a f G = the Q ex , the-spec Q ex
      where
        module G = ValueGraph G

        Q : S → Ω
        Q = ValueClass a f

        Img : S → Ω
        Img b = ⋁ S (λ x → (x ∈ˢ a) ⊓ ((b ∷ x ∷ []) ⊨ G.graph))

        fc : (x : S) → ⟨ x ∈ˢ a ⟩
           → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ G.graph ⟩)
        fc x h =
          (fst (f (x , h)) , G.defines (x , h))
          , λ { (y , t) → Σ≡Prop (λ w → snd ((w ∷ x ∷ []) ⊨ G.graph))
                            (sym (G.only (x , h) y t)) }

        fwd : (b x : S) (h : ⟨ x ∈ˢ a ⟩)
            → ⟨ (b ∷ x ∷ []) ⊨ G.graph ⟩ → ⟨ b ≈ˢ fst (f (x , h)) ⟩
        fwd b x h t = path-to-≈ˢ b (fst (f (x , h))) (G.only (x , h) b t)

        bwd : (b x : S) (h : ⟨ x ∈ˢ a ⟩)
            → ⟨ b ≈ˢ fst (f (x , h)) ⟩ → ⟨ (b ∷ x ∷ []) ⊨ G.graph ⟩
        bwd b x h e =
          subst (λ w → ⟨ (w ∷ x ∷ []) ⊨ G.graph ⟩)
            (sym (≈ˢ-to-path b (fst (f (x , h))) e)) (G.defines (x , h))

        toQ : (b : S) → ⟨ Img b ⟩ → ⟨ Q b ⟩
        toQ b = PT.rec (snd (Q b))
          (λ { (x , (h , t)) → ∣ x , ∣ h , fwd b x h t ∣₁ ∣₁ })

        fromQ : (b : S) → ⟨ Q b ⟩ → ⟨ Img b ⟩
        fromQ b = PT.rec (snd (Img b))
          (λ { (x , u) → PT.rec (snd (Img b))
                 (λ { (h , e) → ∣ x , (h , bwd b x h e) ∣₁ }) u })

        step : Σ[ T ∈ S ] ⟨ ⋀ S (λ b → iff (b ∈ˢ T) (Img b)) ⟩
             → Σ[ T ∈ S ] ⟨ ⋀ S (λ b → iff (b ∈ˢ T) (Q b)) ⟩
        step (T , spec) =
          T , (λ b → (λ hb → toQ b (spec b .fst hb))
                   , (λ hq → spec b .snd (fromQ b hq)))

        ex : ⟨ SetExists Q ⟩
        ex = PT.map step (hasImage′ sep coll a G.graph fc)

  graph→admits : Collection → Separation
               → (a : S) (f : Pt a → Pt B) → ValueGraph a f
               → Admits {I = Pt a} f
  graph→admits coll sep a f G =
    valueSet→admits a f (fst gv) (valueSet-sub a f (fst gv) (snd gv)) (snd gv)
    where
      gv : Σ[ T ∈ S ] ((b : S) → (b ∈ˢ T) ≡ ValueClass a f b)
      gv = graph→valueSet coll sep a f G

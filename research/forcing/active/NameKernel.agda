{-# OPTIONS --cubical --safe --guardedness #-}

-- K3 Track A: the name kernel.
--
-- Sections 1.2, 1.3 and 1.4 of the K3 architecture, in one file, over one
-- weight carrier code W held as a module parameter. The whole layer is built
-- from three ground facts and nothing else: ordinary Extensionality, ordinary
-- Pairing, and the path realization of the structure equality. Accessibility
-- of the membership relation enters separately, as the realization datum it
-- is, and it is the only hypothesis that is not a first-order axiom reading.
--
-- Why the parameter list is this short, and why that is load-bearing rather
-- than tidy. K0 measured that exposing a full model record to the typechecker
-- exhausts a fixed 8 GB heap, twice, at exit 251
-- (k0-material-names-value-sets-2026-09.md:94), and the version that compiled
-- sealed the ground record and unfolded it only locally. So no K3 module takes
-- isZFModel, isZFCModel or any L import, and IsName below is opaque with a
-- proved unfolding lemma rather than a transparent definition. Opacity here is
-- compile feasibility. It is not a style preference.
--
-- Three mechanical lessons K1 and K2 already paid for are observed throughout.
--
-- 1. A bare refl inside a congruence over a truth-value operation leaves the
--    propositionality component an unsolved metavariable, because _⊓_ and _⇒_
--    build a Σ-pair and matching the goal fixes only the carrier. No proof
--    below is written that way: every Ω-valued equality is produced either by
--    the-spec, which is a path handed over whole, or by ⇔toPath, which names
--    both directions.
--
-- 2. An implicit class argument to the description operator does not
--    elaborate. GroundDescription.agda:113-121 records the exact failure. Both
--    uses of `the` in this file write the class out.
--
-- 3. The algebra's bottom is the lifted empty type and the library's negation
--    is on the unlifted one, so every negation is spelled as an implication
--    into the algebra's own ⊥. TruthAlgebra's ¬_ is hidden on the open below,
--    which makes the prohibition mechanical rather than a promise.
--
-- Two prohibitions from section 1.3 hold by the shape of what is written here:
-- there is no record or W-type whose first field is a Type ℓ index, and there
-- is no name former taking a host index type. The Name carrier is a Σ-type
-- over S, never a set quotient, which is what keeps K0's two measured
-- negatives (k0-probe-evidence-2026-09.md:27,29) without analogue.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module NameKernel {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( ⊥̇ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Empty using ( rec* )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.HLevels using ( isProp×; isSetΣSndProp )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Induction.WellFounded using
  ( Acc; acc; WellFounded; isPropAcc; module WFI )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

import OrdinaryProfile
import GroundDescription
open import CodedVocabulary 𝒮 using ( isKPairΔ; isSglΔ; isPairΔ )

open TruthAlgebra (hPropAlgebra ℓ) hiding ( ¬_ )
open hPropStructure 𝒮

module OP = OrdinaryProfile 𝒮
open OP using ( Extensionality; Pairing; Union; Separation; Collection )

-- ---------------------------------------------------------------------
-- Section 1.2. The ground ledger
-- ---------------------------------------------------------------------

-- The architecture puts these four records in their own node, K3.0
-- NameGround. No track in section 3 owns that node, so they are hosted here,
-- where the kernel that consumes the first of them lives. Splitting them into
-- NameGround.agda later is a move of text and a change of one import line in
-- each consumer; nothing below depends on where they sit.
--
-- Four records rather than one, because K0 measured exactly which fields each
-- layer consumes (k0-material-names-value-sets-2026-09.md:128,360-366) and K1
-- measured that the strong Replacement does not transfer from the ordinary
-- profile. A ledger that over-declares is not conservative here: it is the
-- heap failure quoted at the top of this file.

-- Tier 0. Not a first-order axiom, and the reason it is isolated. The
-- ordinary profile carries only the induction schema FoundationInduction,
-- which returns a truth value and no host Acc, so accessibility of the
-- membership relation is a realization datum that an instance supplies.

Accessibility : Type ℓ
Accessibility = WellFounded _∈ᵗ_

-- Tier 1. Exactly what the kernel consumes. Pairing builds the entry,
-- Extensionality makes the description bridge work, and the path realization
-- turns the structure's own equality into host paths so that injectivity of
-- the entry is a statement about paths at all.

record Core : Type (ℓ-suc ℓ) where
  field
    extensional : Extensionality
    hasPair     : Pairing
    ≈ˢ-paths    : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y)

  ≈ˢ-refl : (x : S) → ⟨ x ≈ˢ x ⟩
  ≈ˢ-refl = OP.≈ˢ-refl extensional

-- Tier 2. Supports, weight families and the bound of section 1.5. Union and
-- Separation, and no Collection.

record Sets : Type (ℓ-suc ℓ) where
  field
    core          : Core
    hasUnion      : Union
    hasSeparation : Separation

-- Tier 3. Hereditary closed families. Collection, and nothing else new.

record Families : Type (ℓ-suc ℓ) where
  field
    sets       : Sets
    hasCollect : Collection

-- Tier 4. The one thing no first-order axiom supplies, isolated so that it
-- cannot be smuggled in. Collection reads a Formula S 2, and a host function
-- has no formula, so no instance of Collection applies to it. Section 1.7
-- names this the largest unpriced item in the package.
--
-- The architecture spells the second existential quantifier as ⋁ S, which does
-- not typecheck: the bound variable is the membership witness and lives in
-- ⟨ x ∈ˢ a ⟩, not in S. The index type is corrected here.

record MemberImage : Type (ℓ-suc ℓ) where
  field
    image      : (a : S) (f : (Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩) → S) → S
    image-spec : (a : S) (f : (Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩) → S) (z : S)
               → (z ∈ˢ image a f)
               ≡ ⋁ S (λ x → ⋁ ⟨ x ∈ˢ a ⟩ (λ h → z ≈ˢ f (x , h)))

-- ---------------------------------------------------------------------
-- Sections 1.3 and 1.4. The kernel
-- ---------------------------------------------------------------------

-- One module, parameterized by the weight carrier code, instantiated twice.
-- This is the roadmap's "use recursion once where both representations
-- genuinely share it", and it is satisfiable for one reason worth stating
-- plainly: the subname relation Child never mentions W. A Boolean-weighted
-- name and a poset-weighted name have the same children, the same descent and
-- the same recursor; only the shape predicate sees the weights.
--
-- The accessibility parameter is named acc∈ rather than acc, because acc is
-- the constructor of Acc and every proof of descent below pattern matches on
-- it. The architecture's spelling would shadow the constructor.

module Kernel (𝔊 : Core) (acc∈ : Accessibility) (W : S) where

  open Core 𝔊 using ( extensional; hasPair; ≈ˢ-paths )

  module GD = GroundDescription 𝒮 extensional ≈ˢ-paths
  open GD using ( the; the-spec; separateOf; separateOf-spec )

  -- Equality, in the two shapes the two layers use. The structure's ≈ˢ is a
  -- field into Ω and is not the host's path equality by definition; the
  -- realization hypothesis is what makes the two interchangeable, and every
  -- crossing below goes through one of these two lines.

  ≈→≡ : {x y : S} → ⟨ x ≈ˢ y ⟩ → x ≡ y
  ≈→≡ {x} {y} = subst ⟨_⟩ (≈ˢ-paths x y)

  ≡→≈ : {x y : S} → x ≡ y → ⟨ x ≈ˢ y ⟩
  ≡→≈ {x} {y} = subst ⟨_⟩ (sym (≈ˢ-paths x y))

  -- Transport of membership along a path in the right argument. Named once
  -- because the injectivity proof uses it nine times.

  mem-subst : {u v : S} → u ≡ v → {z : S} → ⟨ z ∈ˢ u ⟩ → ⟨ z ∈ˢ v ⟩
  mem-subst p {z} = subst (λ w → ⟨ z ∈ˢ w ⟩) p

  -- ---------------------------------------------------------------------
  -- Unordered pairs
  -- ---------------------------------------------------------------------

  -- Pairing arrives as a truncated existential and cannot be projected. The
  -- description bridge turns it into a term: extensionality makes the type of
  -- realizers contractible, contractibility is a proposition, and the
  -- truncation eliminates into it. The class argument is written out, which is
  -- lesson 2 and a measured failure when it is not.

  -- The seal on the pair is a measured requirement, not a preference, and it
  -- is the second instance in this file of the rule K0 paid for. Unsealed,
  -- pairOf a b unfolds through the description operator to a stuck
  -- eliminator applied to the Pairing field, and the entry nests three of
  -- them; every definitional comparison in the injectivity proof and in the
  -- Kuratowski reading then compares those spines. Measured on this machine:
  -- with pairOf transparent the file ran 761 s of user time and 1.0 GB
  -- resident without finishing (chk-A2.log). With the seal it is the figure
  -- reported in REPORT-A.md. Nothing below ever needs the unfolding: every
  -- consumer goes through pairOf-spec, which is why the seal costs no proof.

  opaque
    pairOf : S → S → S
    pairOf a b = the (λ x → (x ≈ˢ a) ⊔ (x ≈ˢ b)) (hasPair a b)

    pairOf-spec : (a b x : S) → (x ∈ˢ pairOf a b) ≡ ((x ≈ˢ a) ⊔ (x ≈ˢ b))
    pairOf-spec a b = the-spec (λ x → (x ≈ˢ a) ⊔ (x ≈ˢ b)) (hasPair a b)

  -- The specification in host form, in both directions. The join of the
  -- algebra is a truncated sum, so membership in a pair is a truncated
  -- disjunction of paths and can be eliminated only into a proposition. Every
  -- consumer below respects that.

  ∈-pairOf : (a b z : S) → ⟨ z ∈ˢ pairOf a b ⟩ → ∥ (z ≡ a) ⊎ (z ≡ b) ∥₁
  ∈-pairOf a b z m =
    PT.map (λ { (inl p) → inl (≈→≡ p) ; (inr p) → inr (≈→≡ p) })
      (subst ⟨_⟩ (pairOf-spec a b z) m)

  pairOf-in : (a b z : S) → ∥ (z ≡ a) ⊎ (z ≡ b) ∥₁ → ⟨ z ∈ˢ pairOf a b ⟩
  pairOf-in a b z h =
    subst ⟨_⟩ (sym (pairOf-spec a b z))
      (PT.map (λ { (inl p) → inl (≡→≈ p) ; (inr p) → inr (≡→≈ p) }) h)

  pairOf-left : (a b : S) → ⟨ a ∈ˢ pairOf a b ⟩
  pairOf-left a b = pairOf-in a b a ∣ inl refl ∣₁

  pairOf-right : (a b : S) → ⟨ b ∈ˢ pairOf a b ⟩
  pairOf-right a b = pairOf-in a b b ∣ inr refl ∣₁

  -- The singleton is the diagonal pair, and its membership statement is
  -- untruncated: both branches of the disjunction give the same path, so the
  -- truncation eliminates into the path itself, S being a set.

  singleOf : S → S
  singleOf a = pairOf a a

  singleOf-spec : (a z : S) → ⟨ z ∈ˢ singleOf a ⟩ → z ≡ a
  singleOf-spec a z m =
    PT.rec (isSetS z a) (λ { (inl p) → p ; (inr p) → p }) (∈-pairOf a a z m)

  singleOf-member : (a : S) → ⟨ a ∈ˢ singleOf a ⟩
  singleOf-member a = pairOf-left a a

  -- ---------------------------------------------------------------------
  -- The weighted entry
  -- ---------------------------------------------------------------------

  -- A name is a set of weighted entries, and an entry is the Kuratowski pair
  -- of a subname code and a weight. Nothing else in the kernel knows what a
  -- weight is: W appears in the shape predicate and nowhere above it.

  entry : S → S → S
  entry x b = pairOf (pairOf x x) (pairOf x b)

  entry-spec : (x b z : S)
             → (z ∈ˢ entry x b) ≡ ((z ≈ˢ pairOf x x) ⊔ (z ≈ˢ pairOf x b))
  entry-spec x b = pairOf-spec (pairOf x x) (pairOf x b)

  entry-left : (x b : S) → ⟨ singleOf x ∈ˢ entry x b ⟩
  entry-left x b = pairOf-left (singleOf x) (pairOf x b)

  entry-right : (x b : S) → ⟨ pairOf x b ∈ˢ entry x b ⟩
  entry-right x b = pairOf-right (singleOf x) (pairOf x b)

  -- Injectivity, in three steps. It is the one genuinely combinatorial proof
  -- in the kernel and everything downstream rests on it: the hereditary clause
  -- of the name predicate recovers a subname from an entry only because the
  -- entry determines its two coordinates.
  --
  -- Step one, the first coordinate. The singleton of x belongs to the entry,
  -- hence to the other entry, hence is one of its two members. In either case
  -- y belongs to the singleton of x, so y is x.

  entry-fst : {x b y c : S} → entry x b ≡ entry y c → x ≡ y
  entry-fst {x} {b} {y} {c} p =
    PT.rec (isSetS x y) alt
      (∈-pairOf (singleOf y) (pairOf y c) (singleOf x)
        (mem-subst p (entry-left x b)))
    where
      alt : (singleOf x ≡ singleOf y) ⊎ (singleOf x ≡ pairOf y c) → x ≡ y
      alt (inl q) = sym (singleOf-spec x y (mem-subst (sym q) (singleOf-member y)))
      alt (inr q) = sym (singleOf-spec x y (mem-subst (sym q) (pairOf-left y c)))

  -- Step two, a one-sided fact about the second coordinate. Once the first
  -- coordinates agree, the pair {x, b} belongs to the entry of x and c, so it
  -- is either the singleton of x, in which case b is x and therefore lies in
  -- {x, c}, or it is {x, c} outright. Either way b lies in {x, c}. The
  -- statement is one-sided on purpose: it is applied twice, once to the path
  -- and once to its inverse.

  entry-tail-mem : {x b c : S} → entry x b ≡ entry x c → ⟨ b ∈ˢ pairOf x c ⟩
  entry-tail-mem {x} {b} {c} p =
    PT.rec (snd (b ∈ˢ pairOf x c)) alt
      (∈-pairOf (singleOf x) (pairOf x c) (pairOf x b)
        (mem-subst p (entry-right x b)))
    where
      alt : (pairOf x b ≡ singleOf x) ⊎ (pairOf x b ≡ pairOf x c)
          → ⟨ b ∈ˢ pairOf x c ⟩
      alt (inl q) =
        subst (λ w → ⟨ w ∈ˢ pairOf x c ⟩)
          (sym (singleOf-spec x b (mem-subst q (pairOf-right x b))))
          (pairOf-left x c)
      alt (inr q) = mem-subst q (pairOf-right x b)

  -- Step three, the symmetric combination. Two memberships, four cases, and
  -- the degenerate case is the one where both b and c collapse onto x.

  tail-lemma : {x b c : S} → ⟨ b ∈ˢ pairOf x c ⟩ → ⟨ c ∈ˢ pairOf x b ⟩ → b ≡ c
  tail-lemma {x} {b} {c} mb mc =
    PT.rec2 (isSetS b c) combine (∈-pairOf x c b mb) (∈-pairOf x b c mc)
    where
      combine : ((b ≡ x) ⊎ (b ≡ c)) → ((c ≡ x) ⊎ (c ≡ b)) → b ≡ c
      combine (inl p) (inl q) = p ∙ sym q
      combine (inl _) (inr q) = sym q
      combine (inr p) _       = p

  entry-snd : {x b c : S} → entry x b ≡ entry x c → b ≡ c
  entry-snd p = tail-lemma (entry-tail-mem p) (entry-tail-mem (sym p))

  entry-inj : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c)
  entry-inj {x} {b} {y} {c} p =
    entry-fst p , entry-snd (p ∙ cong (λ w → entry w c) (sym (entry-fst p)))

  -- The entry is a Kuratowski pair in the sense the object language reads.
  -- This is the bridge to K2's coded vocabulary: isKPairΔ is the host reading
  -- of the Δ₀ formula prAtˢ (CodedVocabulary.agda:106-127), so a Separation
  -- over that formula cuts out exactly the entries of a name. Track B's
  -- support specification is stated in these terms, which is why the fact is
  -- proved here rather than there.

  entry-isKPair : (x b : S) → ⟨ isKPairΔ (entry x b) x b ⟩
  entry-isKPair x b = sglPart , pairPart , allPart
    where
      sglWitness : ⟨ isSglΔ (singleOf x) x ⟩
      sglWitness = singleOf-member x , (λ z m → ≡→≈ (singleOf-spec x z m))

      pairWitness : ⟨ isPairΔ (pairOf x b) x b ⟩
      pairWitness = pairOf-left x b , pairOf-right x b ,
        (λ z m → subst ⟨_⟩ (pairOf-spec x b z) m)

      sglPart : ⟨ ⋁ S (λ w → (w ∈ˢ entry x b) ⊓ isSglΔ w x) ⟩
      sglPart = ∣ singleOf x , entry-left x b , sglWitness ∣₁

      pairPart : ⟨ ⋁ S (λ w → (w ∈ˢ entry x b) ⊓ isPairΔ w x b) ⟩
      pairPart = ∣ pairOf x b , entry-right x b , pairWitness ∣₁

      allPart : ⟨ ⋀ S (λ w → (w ∈ˢ entry x b) ⇒ (isSglΔ w x ⊔ isPairΔ w x b)) ⟩
      allPart w m = PT.map decide (∈-pairOf (singleOf x) (pairOf x b) w m)
        where
          decide : ((w ≡ singleOf x) ⊎ (w ≡ pairOf x b))
                 → ⟨ isSglΔ w x ⟩ ⊎ ⟨ isPairΔ w x b ⟩
          decide (inl q) =
            inl (subst (λ u → ⟨ isSglΔ u x ⟩) (sym q) sglWitness)
          decide (inr q) =
            inr (subst (λ u → ⟨ isPairΔ u x b ⟩) (sym q) pairWitness)

  -- ---------------------------------------------------------------------
  -- The subname relation and its descent
  -- ---------------------------------------------------------------------

  -- x is a child of n when some entry of n has x as its first coordinate. The
  -- weight is existentially quantified and truncated, which is the whole
  -- design decision: a child of a name does not come with a chosen weight,
  -- because a subname may appear in a name many times with many weights and
  -- choosing one of them would be a choice the theory does not make.

  Child : S → S → Type ℓ
  Child x n = ∥ Σ[ b ∈ S ] ⟨ entry x b ∈ˢ n ⟩ ∥₁

  isPropChild : (x n : S) → isProp (Child x n)
  isPropChild x n = PT.squash₁

  -- Descent is three membership steps down, x ∈ {x} ∈ entry x b ∈ n, and it is
  -- the only consumer of the accessibility hypothesis in the file. The
  -- truncated weight is eliminated into Acc Child x, which is legitimate
  -- because accessibility is a proposition; that is the single reason the
  -- truncation in Child costs nothing here.

  mutual
    descend : (n : S) → Acc _∈ᵗ_ n → Acc Child n
    descend n (acc below) = acc (λ x edge → PT.rec (isPropAcc x)
      (λ { (b , member) → throughEntry x b (below (entry x b) member) }) edge)

    throughEntry : (x b : S) → Acc _∈ᵗ_ (entry x b) → Acc Child x
    throughEntry x b (acc below) =
      throughSingle x (below (singleOf x) (entry-left x b))

    throughSingle : (x : S) → Acc _∈ᵗ_ (singleOf x) → Acc Child x
    throughSingle x (acc below) = descend x (below x (singleOf-member x))

  child-wf : WellFounded Child
  child-wf n = descend n (acc∈ n)

  -- Recursion on raw codes. The computation law is propositional and never
  -- definitional, which is a property of well-founded recursion in the host
  -- and not a defect of this presentation: every consumer must rewrite along
  -- it rather than expect the term to compute.

  module RawRec {ℓp} (P : S → Type ℓp)
    (step : (n : S) → ((x : S) → Child x n → P x) → P n) where

    result : (n : S) → P n
    result = WFI.induction child-wf step

    computation : (n : S) → result n ≡ step n (λ x _ → result x)
    computation = WFI.induction-compute child-wf step

  -- Both coordinates descend at once. The value relation of section 1.11 is
  -- the first consumer: membership of one name in another and equality of two
  -- names are defined by a simultaneous recursion in which each side steps to
  -- its own children, and no single-coordinate recursor expresses that.

  module RawPairRec {ℓp} (P : S → S → Type ℓp)
    (step : (x y : S) → ((u v : S) → Child u x → Child v y → P u v) → P x y)
    where

    firstStep : (x : S) → ((u : S) → Child u x → (v : S) → P u v)
              → (y : S) → P x y
    firstStep x below y = step x y (λ u v left right → below u left v)

    module First = RawRec (λ x → (y : S) → P x y) firstStep

    result : (x y : S) → P x y
    result = First.result

    computation : (x y : S) → result x y ≡ step x y (λ u v _ _ → result u v)
    computation x y = cong (λ f → f y) (First.computation x)

  -- ---------------------------------------------------------------------
  -- The name predicate
  -- ---------------------------------------------------------------------

  -- Being a name is hereditary: every member is an entry whose weight lies in
  -- W, and every child is itself a name. The first clause is the shape and is
  -- flat; the second is the recursion, and it is why the predicate is defined
  -- by descent rather than written down.

  Entryᴺ : S → Type ℓ
  Entryᴺ e = Σ[ x ∈ S ] Σ[ b ∈ S ] (e ≡ entry x b) × ⟨ b ∈ˢ W ⟩

  Shape : S → Ω
  Shape n = ((e : S) → ⟨ e ∈ˢ n ⟩ → ∥ Entryᴺ e ∥₁) ,
    isPropΠ (λ e → isPropΠ (λ _ → PT.squash₁))

  nameStep : (n : S) → ((x : S) → Child x n → Ω) → Ω
  nameStep n below =
    (⟨ Shape n ⟩ × ((x : S) (edge : Child x n) → ⟨ below x edge ⟩)) ,
    isProp× (snd (Shape n))
      (isPropΠ (λ x → isPropΠ (λ edge → snd (below x edge))))

  module NameDefinition = RawRec (λ _ → Ω) nameStep

  -- The seal. Everything outside this block sees IsName as an abstract
  -- Ω-valued predicate together with one equation, and that is deliberate:
  -- K0 measured that the unsealed version did not compile
  -- (k0-material-names-value-sets-2026-09.md:94). The three lemmas below the
  -- block are the entire interface, and no later K3 module needs more.

  opaque
    IsName : S → Ω
    IsName = NameDefinition.result

    unfold : (n : S) → IsName n ≡ nameStep n (λ x _ → IsName x)
    unfold = NameDefinition.computation

  name-shape : (n : S) → ⟨ IsName n ⟩ → ⟨ Shape n ⟩
  name-shape n proof = fst (subst ⟨_⟩ (unfold n) proof)

  child-is-name : (n : S) → ⟨ IsName n ⟩ → (x : S) → Child x n → ⟨ IsName x ⟩
  child-is-name n proof = snd (subst ⟨_⟩ (unfold n) proof)

  name-intro : (n : S) → ⟨ Shape n ⟩
             → ((x : S) → Child x n → ⟨ IsName x ⟩) → ⟨ IsName n ⟩
  name-intro n sh her = subst ⟨_⟩ (sym (unfold n)) (sh , her)

  -- The carrier. A Σ-type over the ground carrier, with a proof-irrelevant
  -- second component, so it is an h-set for the same reason S is and two names
  -- are equal as soon as their codes are.

  Name : Type ℓ
  Name = Σ[ n ∈ S ] ⟨ IsName n ⟩

  isSetName : isSet Name
  isSetName = isSetΣSndProp isSetS (λ n → snd (IsName n))

  name-≡ : (τ σ : Name) → fst τ ≡ fst σ → τ ≡ σ
  name-≡ τ σ = Σ≡Prop (λ n → snd (IsName n))

  -- ---------------------------------------------------------------------
  -- Names with one entry
  -- ---------------------------------------------------------------------

  -- The singleton name {(σ, z)}. Its shape clause is immediate and its
  -- hereditary clause is exactly where injectivity of the entry is spent: a
  -- child of this code arrives with some weight d, its entry equals the one
  -- entry, so the child is σ's code and inherits σ's own name proof.

  oneEntryCode : Name → S → S
  oneEntryCode σ z = singleOf (entry (fst σ) z)

  oneEntryName : (σ : Name) (z : S) → ⟨ z ∈ˢ W ⟩ → Name
  oneEntryName σ z h = oneEntryCode σ z , valid
    where
      e₀ : S
      e₀ = entry (fst σ) z

      shape : ⟨ Shape (singleOf e₀) ⟩
      shape e m = ∣ fst σ , z , singleOf-spec e₀ e m , h ∣₁

      hereditary : (x : S) → Child x (singleOf e₀) → ⟨ IsName x ⟩
      hereditary x = PT.rec (snd (IsName x))
        (λ { (d , member) →
               subst (λ u → ⟨ IsName u ⟩)
                 (sym (fst (entry-inj (singleOf-spec e₀ (entry x d) member))))
                 (snd σ) })

      valid : ⟨ IsName (singleOf e₀) ⟩
      valid = name-intro (singleOf e₀) shape hereditary

  -- ---------------------------------------------------------------------
  -- The empty name
  -- ---------------------------------------------------------------------

  -- The empty name is taken as a hypothesis rather than built, and the reason
  -- is a ledger fact rather than a convenience. Tier 1 is Extensionality,
  -- Pairing and the path realization; none of the three produces a memberless
  -- set, and the ordinary profile has no empty-set field at all. Any route to
  -- one costs an axiom the kernel's ledger does not carry, so the two
  -- obligations are stated abstractly here and discharged in the submodule
  -- below, where the extra hypothesis is visible in the parameter list.

  module EmptyName (∅ᴺ : S) (∅ᴺ-spec : (z : S) → (z ∈ˢ ∅ᴺ) ≡ ⊥) where

    empty-absurd : {ℓa : Level} {A : Type ℓa} (z : S) → ⟨ z ∈ˢ ∅ᴺ ⟩ → A
    empty-absurd z m = rec* (subst ⟨_⟩ (∅ᴺ-spec z) m)

    ∅ᴺ-is-name : ⟨ IsName ∅ᴺ ⟩
    ∅ᴺ-is-name = name-intro ∅ᴺ
      (λ e m → empty-absurd e m)
      (λ x → PT.rec (snd (IsName x))
        (λ { (b , m) → empty-absurd (entry x b) m }))

    emptyName : Name
    emptyName = ∅ᴺ , ∅ᴺ-is-name

    -- Raw distinctness at a zero weight. The one-entry name has a member and
    -- the empty name has none, so their codes differ whatever the weight z is.
    -- This is the raw half only. The Boolean half, that a name whose single
    -- entry carries the zero weight nevertheless denotes the empty set, is
    -- K4's and is a statement about the value relation, not about codes; K0's
    -- checked witness for it is on the inductive probe carrier and not on this
    -- material one (k0-probe-evidence-2026-09.md:29), so it is not inherited.

    zero-distinct : (σ : Name) (z : S) (h : ⟨ z ∈ˢ W ⟩)
                  → fst (oneEntryName σ z h) ≡ ∅ᴺ → ⟨ ⊥ ⟩
    zero-distinct σ z h p =
      subst ⟨_⟩ (∅ᴺ-spec (entry (fst σ) z))
        (mem-subst p (singleOf-member (entry (fst σ) z)))

  -- Separation discharges the two obligations, and it is the cheapest route:
  -- the ambient bound W is already a parameter, so no inhabitant has to be
  -- imported and Infinity stays out of the ledger entirely. The class of the
  -- separation is the reading of ⊥̇, which the evaluator sends to the algebra's
  -- own bottom; the meet with it collapses by propositional extensionality,
  -- named in both directions rather than left to a congruence.

  module FromSeparation (sep : Separation) where

    meet-bot : (P : Ω) → (P ⊓ ⊥) ≡ ⊥
    meet-bot P = ⇔toPath snd rec*

    emptyCode : S
    emptyCode = separateOf sep W ⊥̇

    emptyCode-spec : (z : S) → (z ∈ˢ emptyCode) ≡ ⊥
    emptyCode-spec z = separateOf-spec sep W ⊥̇ z ∙ meet-bot (z ∈ˢ W)

    open EmptyName emptyCode emptyCode-spec public

  -- ---------------------------------------------------------------------
  -- Section 1.4. Recursion and induction at the name level
  -- ---------------------------------------------------------------------

  -- The raw recursors run on codes. Lifting them to names is a change of
  -- motive and nothing more: a property of names is a property of codes that
  -- takes the name proof as an extra argument, and the recursive call at a
  -- child comes back as a function of that child's own proof. Eta for Σ is
  -- what makes the two sides of the computation law match on the nose, so
  -- child-is-name is not needed here; a child that reaches the step function
  -- already carries its proof.

  module Rec {ℓp} (P : Name → Type ℓp)
    (step : (τ : Name) → ((σ : Name) → Child (fst σ) (fst τ) → P σ) → P τ)
    where

    Motive : S → Type (ℓ-max ℓ ℓp)
    Motive n = (v : ⟨ IsName n ⟩) → P (n , v)

    rawStep : (n : S) → ((x : S) → Child x n → Motive x) → Motive n
    rawStep n below v = step (n , v) (λ σ edge → below (fst σ) edge (snd σ))

    module Raw = RawRec Motive rawStep

    rec : (τ : Name) → P τ
    rec τ = Raw.result (fst τ) (snd τ)

    compute : (τ : Name) → rec τ ≡ step τ (λ σ _ → rec σ)
    compute τ = cong (λ f → f (snd τ)) (Raw.computation (fst τ))

  -- Bell's Induction Principle 1.7, in the form the host gives it. Bell proves
  -- it by an easy induction on rank; here accessibility of the membership
  -- relation replaces the rank, and no rank is defined anywhere in K3.

  ind : {ℓp : Level} (P : Name → Type ℓp)
      → ((τ : Name) → ((σ : Name) → Child (fst σ) (fst τ) → P σ) → P τ)
      → (τ : Name) → P τ
  ind P step = Rec.rec P step

  module PairRec {ℓp} (P : Name → Name → Type ℓp)
    (step : (τ σ : Name)
          → ((υ ω : Name) → Child (fst υ) (fst τ) → Child (fst ω) (fst σ)
             → P υ ω)
          → P τ σ)
    where

    Motive : S → S → Type (ℓ-max ℓ ℓp)
    Motive m n = (u : ⟨ IsName m ⟩) (v : ⟨ IsName n ⟩) → P (m , u) (n , v)

    rawStep : (x y : S)
            → ((u v : S) → Child u x → Child v y → Motive u v) → Motive x y
    rawStep x y below p q =
      step (x , p) (y , q)
        (λ υ ω e f → below (fst υ) (fst ω) e f (snd υ) (snd ω))

    module Raw = RawPairRec Motive rawStep

    pair-rec : (τ σ : Name) → P τ σ
    pair-rec τ σ = Raw.result (fst τ) (fst σ) (snd τ) (snd σ)

    pair-compute : (τ σ : Name)
                 → pair-rec τ σ ≡ step τ σ (λ υ ω _ _ → pair-rec υ ω)
    pair-compute τ σ =
      cong (λ f → f (snd τ) (snd σ)) (Raw.computation (fst τ) (fst σ))

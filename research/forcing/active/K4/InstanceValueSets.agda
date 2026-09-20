{-# OPTIONS --cubical --safe --guardedness #-}

-- K4 Track K, file 3 of 4. What the ValueSets contract COSTS, measured as a
-- lower bound and stated at an arbitrary ground so that the L instance in
-- file 4 is one application of it.
--
-- THE QUESTION. Track B discharges ValueSets from K3's tier-4 member-image
-- datum (K4/ValueSets.agda:680, member→values) and reports, as a measured
-- negative, that the graph route cannot discharge the TOTAL contract, because
-- attain quantifies over every host function f : Pt a → Pt B while a family
-- of graph formulas is fixed before f is given (REPORT-B section 3). That
-- settles which routes exist. It does not say how strong the contract is,
-- and the instance track cannot report an obligation as open without knowing
-- that.
--
-- THE ANSWER, and it is a lower bound rather than an obstruction argument.
-- ValueSets over a carrier B implies that EVERY ambient truth-valued class,
-- with no formula, no complexity bound and no definability of any kind, cuts
-- a set out of B. The proof is one selection function: send a member of B to
-- itself if the class holds of it and to a fixed seed otherwise, which is a
-- host function Pt B → Pt B because both branches land in B, and read its
-- attained-value class. This is K3's tier-4 reduction (LInstanceImage.agda,
-- module Reduction) carried across to the value-set contract, and the two
-- differ in exactly one place: K3's selection is S-valued and works at every
-- code a, while this one must land in Pt B, so the code it works at is B
-- itself. That restriction is why the conclusion below is about subclasses
-- of B and not about subclasses of an arbitrary set.
--
-- WHY THAT IS THE RIGHT MEASUREMENT TO TAKE. The statement "every ambient
-- subclass of B is a set of the ground" is not a lemma anybody is going to
-- find at a ground that is a proper subclass of the ambient universe: it says
-- the ambient power set of B lies inside the ground. At the cumulative
-- hierarchy it is true and cheap, because a set there IS a small family and
-- smallness separates (V/Smallness.lagda.md, separateFromSmall). At the
-- constructible structure it is a form of V = L for the ambient theory, which
-- is consistent and false in any ambient model with a non-constructible
-- subclass of a constructible set. So the reduction below does not prove
-- ValueSets unavailable anywhere; it proves that discharging it at a ground
-- is at least as hard as deciding that, and it locates the difficulty in the
-- ground rather than in the contract.
--
-- THE SEED IS NOT A BLEMISH. A total function must send the members outside
-- the class somewhere, so the attained class carries one extra point. The
-- unseeded statement is recovered whenever the class holds at one point of B,
-- which is the only case in which the subclass is not already empty, and that
-- is the corollary at the bottom. K3 makes the same remark about the same
-- construction (LInstanceImage.agda:255-262).
--
-- HYPOTHESES. The structure, Extensionality and the path realization, which
-- are K4.ValueSets's own three; the algebra, as Track A's records, in the
-- uniform telescope; and excluded middle, which is an explicit argument of
-- the two theorems that split on the class and is a module parameter of
-- neither this file nor anything in it. LEM ℓ and not LEM (ℓ-suc ℓ): the
-- class is Ω-valued and Ω is hProp ℓ, so the decision is at the level the
-- structure already fixes and the L instance pays the landmarks' own price.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
import OrdinaryProfile
import K4.Algebra
import K4.ValueSets

module K4.InstanceValueSets
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )

open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open import OrdinaryProfile 𝒮 using ( ≈ˢ-refl; module PathRealization )
open PathRealization paths using ( ≈ˢ-to-path )

open import K4.Algebra 𝒮 using ( Pt; Lattice; CodedComplete )
open import K4.ValueSets 𝒮 ext paths using ( module Core )

-- ---------------------------------------------------------------------
-- The statement the contract is measured against
-- ---------------------------------------------------------------------

-- A class is an arbitrary Ω-valued predicate on the carrier. It carries no
-- formula, which is what separates this statement from the Separation axiom,
-- and no complexity bound, which is what separates it from every bounded
-- schema in OrdinaryProfile.

Class : Type (ℓ-suc ℓ)
Class = S → Ω

-- "The ambient power set of B is inside the ground", written out. Compare
-- OrdinaryProfile.Separation (OrdinaryProfile.agda:88-91), whose second
-- argument is a Formula S 1: that is the axiom, and this is the schema with
-- the formula deleted.

Absorbs : S → Type (ℓ-suc ℓ)
Absorbs B = (P : Class) → Σ[ s ∈ S ] ((z : S) → (z ∈ˢ s) ≡ ((z ∈ˢ B) ⊓ P z))

module Reduce (B : S) (L : Lattice B) (Kc : CodedComplete B L) where

  open Core B L Kc using ( ValueSets; ValueClass )

  -- ---------------------------------------------------------------------
  -- The selection function
  -- ---------------------------------------------------------------------

  module Reduction (vs : ValueSets) (lem : LEM ℓ)
                   (x₀ : S) (h₀ : ⟨ x₀ ∈ˢ B ⟩) (P : Class) where

    open ValueSets vs using ( attain; attain-spec )

    Decision : S → Type ℓ
    Decision x = ⟨ P x ⟩ ⊎ (⟨ P x ⟩ → Empty.⊥)

    -- The decision is an explicit argument of `pick` rather than being taken
    -- inside it. That is forced, not stylistic: every lemma below case
    -- splits on the decision, and a split cannot happen under a lambda that
    -- has already consumed it. K3 records the same constraint at the same
    -- construction (LInstanceImage.agda:271-274).

    pick : (x : S) → ⟨ x ∈ˢ B ⟩ → Decision x → Pt B
    pick x h (inl _) = x , h
    pick x h (inr _) = x₀ , h₀

    sel : Pt B → Pt B
    sel p = pick (fst p) (snd p) (lem (P (fst p)))

    Target : S → Ω
    Target z = ((z ∈ˢ B) ⊓ P z) ⊔ (z ≈ˢ x₀)

    -- ---------------------------------------------------------------------
    -- Reading a value backwards, and producing one
    -- ---------------------------------------------------------------------

    -- On the branch where the class holds, the selection is the identity, so
    -- a value equal to the selection at x is equal to x, and the class and
    -- the membership transport along that path. On the other branch the
    -- selection is the seed and the value lands in the right disjunct with
    -- nothing to prove.

    class≡ : (z : S) → ValueClass B sel z ≡ Target z
    class≡ z = ⇔toPath out into
      where
      out : ⟨ ValueClass B sel z ⟩ → ⟨ Target z ⟩
      out = PT.rec (snd (Target z))
        (λ { (x , hs) → PT.rec (snd (Target z))
          (λ { (h , q) → step z x h (lem (P x)) q }) hs })
        where
        step : (z x : S) (h : ⟨ x ∈ˢ B ⟩) (d : Decision x)
             → ⟨ z ≈ˢ fst (pick x h d) ⟩ → ⟨ Target z ⟩
        step z x h (inl px) q =
          ∣ inl ( subst (λ w → ⟨ w ∈ˢ B ⟩) (sym (≈ˢ-to-path z x q)) h
                , subst (λ w → ⟨ P w ⟩) (sym (≈ˢ-to-path z x q)) px ) ∣₁
        step z x h (inr _) q = ∣ inr q ∣₁

      into : ⟨ Target z ⟩ → ⟨ ValueClass B sel z ⟩
      into = PT.rec squash₁
        (λ { (inl (z∈B , pz)) → ∣ z , ∣ z∈B , atSelf z z∈B pz (lem (P z)) ∣₁ ∣₁
           ; (inr q)          → ∣ x₀ , ∣ h₀ , atSeed z q (lem (P x₀)) ∣₁ ∣₁ })
        where
        atSelf : (z : S) (h : ⟨ z ∈ˢ B ⟩) → ⟨ P z ⟩ → (d : Decision z)
               → ⟨ z ≈ˢ fst (pick z h d) ⟩
        atSelf z h pz (inl _)  = ≈ˢ-refl ext z
        atSelf z h pz (inr np) = Empty.rec (np pz)

        -- Both branches of the seed return the seed, so the only content is
        -- composing the given path with the one the case split exposes.

        atSeed : (z : S) → ⟨ z ≈ˢ x₀ ⟩ → (d : Decision x₀)
               → ⟨ z ≈ˢ fst (pick x₀ h₀ d) ⟩
        atSeed z q (inl _) = q
        atSeed z q (inr _) = q

    separated : Σ[ s ∈ S ] ((z : S) → (z ∈ˢ s) ≡ Target z)
    separated = attain B sel , λ z → attain-spec B sel z ∙ class≡ z

  -- ---------------------------------------------------------------------
  -- The two statements
  -- ---------------------------------------------------------------------

  -- The seeded form, unconditional in the class.

  valueSets→seeded :
      ValueSets → LEM ℓ
    → (x₀ : S) → ⟨ x₀ ∈ˢ B ⟩ → (P : Class)
    → Σ[ s ∈ S ] ((z : S) → (z ∈ˢ s) ≡ (((z ∈ˢ B) ⊓ P z) ⊔ (z ≈ˢ x₀)))
  valueSets→seeded vs lem x₀ h₀ P = Reduction.separated vs lem x₀ h₀ P

  -- The pointed corollary, which is the sentence to quote. If the class holds
  -- at one point of B then the subclass is a set of the ground exactly, with
  -- no seed and no residue. Read it as: ValueSets at this algebra makes every
  -- INHABITED ambient subclass of B a ground code, and the empty subclass is
  -- a ground code anyway.

  valueSets→absorbs :
      ValueSets → LEM ℓ
    → (x₀ : S) → ⟨ x₀ ∈ˢ B ⟩ → (P : Class) → ⟨ P x₀ ⟩
    → Σ[ s ∈ S ] ((z : S) → (z ∈ˢ s) ≡ ((z ∈ˢ B) ⊓ P z))
  valueSets→absorbs vs lem x₀ h₀ P px₀ =
    R.separated .fst , λ z → R.separated .snd z ∙ ⇔toPath (drop z) (keep z)
    where
    module R = Reduction vs lem x₀ h₀ P

    drop : (z : S) → ⟨ R.Target z ⟩ → ⟨ (z ∈ˢ B) ⊓ P z ⟩
    drop z = PT.rec (snd ((z ∈ˢ B) ⊓ P z))
      (λ { (inl c) → c
         ; (inr q) → subst (λ w → ⟨ w ∈ˢ B ⟩) (sym (≈ˢ-to-path z x₀ q)) h₀
                   , subst (λ w → ⟨ P w ⟩) (sym (≈ˢ-to-path z x₀ q)) px₀ })

    keep : (z : S) → ⟨ (z ∈ˢ B) ⊓ P z ⟩ → ⟨ R.Target z ⟩
    keep z c = ∣ inl c ∣₁

  -- ---------------------------------------------------------------------
  -- The upper bound, for completeness of the ledger
  -- ---------------------------------------------------------------------

  -- The other side of the measurement. ValueSets gives back exactly K3's
  -- tier-4 datum restricted to functions whose values lie in B, so the
  -- contract and that restricted datum are inter-derivable: Track B's
  -- member→values goes one way and this goes the other. Nothing here is
  -- surprising; it is written down so that a later package reading the
  -- reduction above knows the contract is not strictly stronger than the
  -- tier it was supposed to replace.

  valueSets→imageᴮ :
      ValueSets
    → (a : S) (g : Pt a → S) → ((p : Pt a) → ⟨ g p ∈ˢ B ⟩)
    → Σ[ s ∈ S ] ((z : S) → (z ∈ˢ s)
                ≡ ⋁ S (λ x → ⋁ ⟨ x ∈ˢ a ⟩ (λ h → z ≈ˢ g (x , h))))
  valueSets→imageᴮ vs a g hg =
      ValueSets.attain vs a (λ p → g p , hg p)
    , ValueSets.attain-spec vs a (λ p → g p , hg p)

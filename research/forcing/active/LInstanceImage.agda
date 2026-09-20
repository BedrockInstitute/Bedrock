{-# OPTIONS --cubical --safe --guardedness #-}

-- K3 Track J, file 5 of 7. Tier 4, MemberImage, at 𝒮ᵥ and at 𝒮ʟ.
--
-- THIS FILE IS A MEASURED NEGATIVE, and it is the only one in the track. Tier
-- 4 is discharged at the ambient hierarchy and is NOT discharged at the
-- constructible structure. The obstruction is not a missing lemma and not a
-- gap in the tier records: tier 4 at L is EQUIVALENT to a statement strictly
-- stronger than the whole assumption ledger, and that equivalence is proved
-- below rather than asserted.
--
-- THE QUESTION. Tier 4 says: the image of the members of a ground code under
-- an arbitrary HOST function is again a ground code. Section 1.7 calls it the
-- one thing no first-order axiom supplies, and architecture N2 says why:
-- Collection reads a Formula S 2, and a host function carries no formula, so
-- no instance of Collection applies to it. That argument shows tier 4 is not
-- DERIVABLE from tiers 1 to 3. It leaves open whether a particular ground
-- realizes it anyway, and that is the question this file settles for the two
-- grounds the package cares about.
--
-- AT V THE ANSWER IS YES, and the proof is four lines. Every set of the
-- ambient hierarchy IS an image already: the constructor `sett` takes a SMALL
-- index type and a family, so a set comes with a presentation, and the image
-- of a host function over it is the same index type composed with the
-- function. Nothing is separated, nothing is bounded, no axiom is invoked.
-- This is the sense in which tier 4 is a REALIZATION datum and not an axiom:
-- it is a fact about how the sets of a particular model are built.
--
-- AT L THE ANSWER IS NO, and the shape of the failure is the interesting
-- part. A constructible set still has a small presentation, because it is a
-- set of V. Its members are constructible, because L is transitive. Every
-- value of the function is constructible. So the image EXISTS as a set of V,
-- every one of its members is constructible, and one can even compute, with
-- no choice and no formula, a single constructible set that CONTAINS all the
-- values (that is `imageBound` below, and it is the whole of what L.Recursion's
-- `smallDom` gives). What is missing is the last step, carving the image out
-- of that bound, and carving is Separation, and Separation at L reads a
-- formula. An arbitrary host function has none.
--
-- That is the informal argument. The formal content of this file is that it
-- is not merely an argument about proof strategies. `memberImage→classSeparation`
-- proves: tier 4 at L implies that for EVERY constructible set and EVERY
-- ambient truth-valued predicate whatever, the corresponding subclass is
-- itself a constructible set. `classSeparation→memberImage` proves the
-- converse. So tier 4 at L is exactly the statement that L absorbs every
-- ambient subclass of each of its sets, which is a form of V = L for the
-- ambient theory. It is consistent, since it holds in any model of the
-- ambient theory that itself satisfies V = L, and it FAILS in any model that
-- contains a subset of a constructible set that is not constructible, a
-- Cohen real being the standard example. Neither the repository nor the
-- ledger decides it, and nothing weaker than deciding it will discharge
-- tier 4 here.
--
-- WHAT THE PACKAGE SHOULD DO WITH THIS, in one sentence each, stated as
-- findings and not as instructions. Track D measured that tier 0 and tier 4
-- TOGETHER produce `check` and its recursion equation (REPORT-D F6); at L the
-- tier 4 half of that route is unavailable, so the L instance of `check`, of
-- `Γ`, of `trᴮ` and of `trᴾ` has to be built the way L builds every other
-- recursion, by a definable graph through L.Recursion, which is Track D's
-- route G and which needs each of those four functions to carry a formula.
-- That is a real obligation and it is NOT discharged here; it is named so
-- that no later track assumes the L instance inherits `check` for free.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LInstanceImage {ℓ : Level} where

open import FOL.ZFStructure using ( ZFStructure; ↾-reflects; module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member ) renaming ( fiber to memberFiber )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )

open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; sett )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

import NameKernel

-- ---------------------------------------------------------------------
-- Tier 4 at the ambient hierarchy
-- ---------------------------------------------------------------------

-- Read the construction as the sentence "a set is its own presentation". The
-- index is ⟪ a ⟫, the small type of members of `a`; `member` turns an index
-- into a membership proof and `memberFiber` turns a membership proof back
-- into an index (V/Presentation.lagda.md:34-41). Those two are the ONLY
-- inputs, and they are facts about the concrete hierarchy: file 1 records why
-- importing them here is correct and importing them in Tracks A to I would
-- have been the package's most likely silent failure.
--
-- The membership law is definitional on the left. `z ∈ sett X ix` unfolds to
-- the truncated fibre of `ix` over `z` by the defining clause of the
-- hierarchy's membership, so the whole content of the specification is the
-- passage between an index and a membership proof, in both directions, and
-- the proof that the function does not notice which membership proof it was
-- handed. That last step is `Σ≡Prop`, and it is where propositionality of
-- membership is spent.

module AtV where

  open hPropStructure 𝒮ᵥ
  open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ)) hiding ( ¬_ )

  module NKV = NameKernel 𝒮ᵥ

  imageV : (a : S) (f : (Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩) → S) → S
  imageV a f = sett ⟪ a ⟫ (λ m → f (⟪ a ⟫↪ m , member a m))

  imageV-spec : (a : S) (f : (Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩) → S) (z : S)
              → (z ∈ˢ imageV a f)
              ≡ ⋁ S (λ x → ⋁ ⟨ x ∈ˢ a ⟩ (λ h → z ≈ˢ f (x , h)))
  imageV-spec a f z = ⇔toPath fwd bwd
    where
    fwd : ∥ Σ[ m ∈ ⟪ a ⟫ ] (f (⟪ a ⟫↪ m , member a m) ≡ z) ∥₁
        → ⟨ ⋁ S (λ x → ⋁ ⟨ x ∈ˢ a ⟩ (λ h → z ≈ˢ f (x , h))) ⟩
    fwd = PT.rec squash₁
      (λ { (m , p) → ∣ ⟪ a ⟫↪ m , ∣ member a m , sym p ∣₁ ∣₁ })

    bwd : ⟨ ⋁ S (λ x → ⋁ ⟨ x ∈ˢ a ⟩ (λ h → z ≈ˢ f (x , h))) ⟩
        → ∥ Σ[ m ∈ ⟪ a ⟫ ] (f (⟪ a ⟫↪ m , member a m) ≡ z) ∥₁
    bwd = PT.rec squash₁ (λ { (x , hs) → PT.rec squash₁ (at x) hs })
      where
      at : (x : S) → Σ[ h ∈ ⟨ x ∈ˢ a ⟩ ] (z ≡ f (x , h))
         → ∥ Σ[ m ∈ ⟪ a ⟫ ] (f (⟪ a ⟫↪ m , member a m) ≡ z) ∥₁
      at x (h , q) =
        ∣ memberFiber a h .fst
        , cong f (Σ≡Prop (λ y → snd (y ∈ˢ a)) (memberFiber a h .snd)) ∙ sym q ∣₁

  -- The tier record at the ambient hierarchy. Sealed on the same reasoning as
  -- the other tiers, although this one is cheap: nothing downstream needs the
  -- unfolding, and a transparent `sett` under three nested descriptions is
  -- precisely the shape that cost Track A 761 seconds.

  opaque
    memberImageV : NKV.MemberImage
    memberImageV = record { image = imageV ; image-spec = imageV-spec }

-- ---------------------------------------------------------------------
-- Tier 4 at the constructible structure
-- ---------------------------------------------------------------------

module AtL (lem : LEM (ℓ-suc ℓ)) where

  open hPropStructure 𝒮ʟ
  open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ)) hiding ( ¬_ )
  open import L.Recursion {ℓ} lem using ( smallDom )

  module NKL = NameKernel 𝒮ʟ

  -- The reflection lemma of the restriction, with its two implicit arguments
  -- fixed once. At L a truth ⟨ x ≈ˢ y ⟩ IS a path of underlying sets, and
  -- this is the one line that turns it back into a path of model elements.
  -- It is `Σ≡Prop` at the propositional class isL and nothing more.

  S≡ : {x y : S} → fst x ≡ fst y → x ≡ y
  S≡ = ↾-reflects {𝒮 = 𝒮ᵥ} {M = isL}

  Member : (a : S) → Type (ℓ-suc ℓ)
  Member a = Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩

  -- The two halves of "the members of a constructible set are a small family
  -- of constructible sets". Transitivity of the class isL supplies the
  -- constructibility of each member; the presentation supplies the smallness
  -- of the index. Neither is available at an arbitrary ground.

  asMember : (a : S) (m : ⟪ fst a ⟫) → Member a
  asMember a m =
    ( ⟪ fst a ⟫↪ m , isL-trans (member (fst a) m) (snd a) ) , member (fst a) m

  covers : (a : S) (p : Member a) → Σ[ m ∈ ⟪ fst a ⟫ ] (asMember a m ≡ p)
  covers a (x , h) =
    memberFiber (fst a) h .fst
    , Σ≡Prop (λ y → snd (y ∈ˢ a)) (S≡ (memberFiber (fst a) h .snd))

  -- WHAT IS AVAILABLE AT L, in full. Every value of the function lies in one
  -- constructible set, computed with no choice and no formula: bound the
  -- earliest stages of the small family of values and take that stage. This
  -- is L.Recursion's smallDom (src/L/Recursion.lagda.md:141-152), and it is
  -- the exact half of tier 4 that survives the passage from V to L.
  --
  -- It is worth being precise about what it does not say. The bound contains
  -- the values; it contains other things too, an entire constructible stage
  -- of them, and no statement here distinguishes a value from a non-value.

  imageBound : (a : S) (f : Member a → S)
             → Σ[ d ∈ S ] ((p : Member a) → ⟨ f p ∈ˢ d ⟩)
  imageBound a f = sd .fst , inBound
    where
    sd = smallDom ⟪ fst a ⟫ (λ m → f (asMember a m))

    inBound : (p : Member a) → ⟨ f p ∈ˢ sd .fst ⟩
    inBound p = subst (λ q → ⟨ f q ∈ˢ sd .fst ⟩)
                  (covers a p .snd) (sd .snd (covers a p .fst))

  -- THE HYPOTHESIS THAT WOULD DISCHARGE TIER 4, named so that no later track
  -- has to guess it. A class here is an arbitrary Ω-valued predicate of the
  -- ambient theory: no formula, no complexity bound, no definability of any
  -- kind. Class separation says every such class cuts a set out of a set.
  --
  -- At V this holds, by smallness (V/Smallness.lagda.md:219, separateFromSmall,
  -- once a smallness witness is available). At L it is the statement that the
  -- ambient power set of a constructible set is included in L.

  ClassSeparation : Type (ℓ-suc (ℓ-suc ℓ))
  ClassSeparation = (a : S) (P : S → Ω)
                  → Σ[ s ∈ S ] ((z : S) → (z ∈ˢ s) ≡ ((z ∈ˢ a) ⊓ P z))

  -- Direction one. Class separation discharges tier 4: separate the bound by
  -- the image class, then observe that the bounding conjunct is redundant,
  -- because every member of the image class is a value and every value is in
  -- the bound. The redundancy step is where `imageBound` is used and it is
  -- the only place the ambient structure appears in this implication.

  ImageClass : (a : S) (f : Member a → S) → S → Ω
  ImageClass a f z = ⋁ S (λ x → ⋁ ⟨ x ∈ˢ a ⟩ (λ h → z ≈ˢ f (x , h)))

  classSeparation→memberImage : ClassSeparation → NKL.MemberImage
  classSeparation→memberImage cs = record
    { image      = λ a f → cs (imageBound a f .fst) (ImageClass a f) .fst
    ; image-spec = spec }
    where
    spec : (a : S) (f : Member a → S) (z : S)
         → (z ∈ˢ cs (imageBound a f .fst) (ImageClass a f) .fst)
         ≡ ImageClass a f z
    spec a f z =
      cs (imageBound a f .fst) (ImageClass a f) .snd z ∙ ⇔toPath snd add
      where
      add : ⟨ ImageClass a f z ⟩
          → ⟨ (z ∈ˢ imageBound a f .fst) ⊓ ImageClass a f z ⟩
      add c = inD , c
        where
        inD : ⟨ z ∈ˢ imageBound a f .fst ⟩
        inD = PT.rec (snd (z ∈ˢ imageBound a f .fst))
          (λ { (x , hs) → PT.rec (snd (z ∈ˢ imageBound a f .fst))
            (λ { (h , q) → subst (λ w → ⟨ w ∈ˢ imageBound a f .fst ⟩)
                             (sym (S≡ {x = z} {y = f (x , h)} q))
                             (imageBound a f .snd (x , h)) })
            hs })
          c

  -- Direction two, and the measured negative proper. Tier 4 implies class
  -- separation.
  --
  -- The construction is one line of mathematics: given a class P, an argument
  -- a and a member x₀ of it, send each member x of a to ITSELF if P holds of
  -- x, and to x₀ otherwise. Excluded middle at the level of the truth values
  -- makes that a host function, and it is the only use of lem in this file
  -- that is not inherited from a stage construction. The image of that
  -- function is the members of a satisfying P, together with x₀.
  --
  -- The seed x₀ is not a blemish on the statement and cannot be removed by
  -- being cleverer: a nonempty image is the price of a total function, and
  -- the corollary below shows the seed is free whenever the class holds at
  -- one point, which is the only case in which the subclass is not already
  -- the empty set.

  module Reduction (mi : NKL.MemberImage) (a x₀ : S) (h₀ : ⟨ x₀ ∈ˢ a ⟩)
                   (P : S → Ω) where

    open NKL.MemberImage mi using ( image; image-spec )

    Decision : S → Type (ℓ-suc ℓ)
    Decision x = ⟨ P x ⟩ ⊎ (⟨ P x ⟩ → Empty.⊥)

    pick : (x : S) → Decision x → S
    pick x (inl _) = x
    pick x (inr _) = x₀

    sel : Member a → S
    sel p = pick (fst p) (lem (P (fst p)))

    Target : S → Ω
    Target z = ((z ∈ˢ a) ⊓ P z) ⊔ (z ≈ˢ x₀)

    -- Reading a value backwards. The decision is an explicit argument, which
    -- is what lets the case split happen at all: the type of the hypothesis
    -- mentions the decision, so it cannot be split inside a lambda.

    fromValue : (z x : S) → ⟨ x ∈ˢ a ⟩ → (d : Decision x)
              → ⟨ z ≈ˢ pick x d ⟩ → ⟨ Target z ⟩
    fromValue z x h (inl px) q =
      ∣ inl ( subst (λ w → ⟨ w ∈ˢ a ⟩) (sym (S≡ {x = z} {y = x} q)) h
            , subst (λ w → ⟨ P w ⟩) (sym (S≡ {x = z} {y = x} q)) px ) ∣₁
    fromValue z x h (inr _) q = ∣ inr q ∣₁

    -- Producing a value. Two one-line case splits: at a point the class holds
    -- of, the function is the identity; at the seed, both branches return the
    -- seed.

    atSelf : (z : S) → ⟨ P z ⟩ → (d : Decision z) → ⟨ z ≈ˢ pick z d ⟩
    atSelf z pz (inl _) = refl
    atSelf z pz (inr np) = Empty.rec (np pz)

    atSeed : (d : Decision x₀) → ⟨ x₀ ≈ˢ pick x₀ d ⟩
    atSeed (inl _) = refl
    atSeed (inr _) = refl

    class≡ : (z : S) → ImageClass a sel z ≡ Target z
    class≡ z = ⇔toPath out into
      where
      out : ⟨ ImageClass a sel z ⟩ → ⟨ Target z ⟩
      out = PT.rec (snd (Target z))
        (λ { (x , hs) → PT.rec (snd (Target z))
          (λ { (h , q) → fromValue z x h (lem (P x)) q }) hs })

      into : ⟨ Target z ⟩ → ⟨ ImageClass a sel z ⟩
      into = PT.rec squash₁
        (λ { (inl (z∈a , pz)) → ∣ z , ∣ z∈a , atSelf z pz (lem (P z)) ∣₁ ∣₁
           ; (inr q)          → ∣ x₀ , ∣ h₀ , q ∙ atSeed (lem (P x₀)) ∣₁ ∣₁ })

    separated : Σ[ s ∈ S ] ((z : S) → (z ∈ˢ s) ≡ Target z)
    separated = image a sel , λ z → image-spec a sel z ∙ class≡ z

  memberImage→classSeparation :
      NKL.MemberImage
    → (a x₀ : S) → ⟨ x₀ ∈ˢ a ⟩ → (P : S → Ω)
    → Σ[ s ∈ S ] ((z : S)
        → (z ∈ˢ s) ≡ (((z ∈ˢ a) ⊓ P z) ⊔ (z ≈ˢ x₀)))
  memberImage→classSeparation mi a x₀ h₀ P = Reduction.separated mi a x₀ h₀ P

  -- The corollary, which is the sentence to quote. If the class holds at one
  -- point of the argument, tier 4 at L makes the subclass a constructible set
  -- exactly. No formula, no complexity, no definability: an arbitrary ambient
  -- predicate. That is the ambient power set of a constructible set lying
  -- inside L, and it is why tier 4 at L is not a lemma anyone is going to
  -- find.

  memberImage→subclass :
      NKL.MemberImage
    → (a x₀ : S) → ⟨ x₀ ∈ˢ a ⟩ → (P : S → Ω) → ⟨ P x₀ ⟩
    → Σ[ s ∈ S ] ((z : S) → (z ∈ˢ s) ≡ ((z ∈ˢ a) ⊓ P z))
  memberImage→subclass mi a x₀ h₀ P px₀ =
    R.separated .fst , λ z → R.separated .snd z ∙ ⇔toPath (drop z) (keep z)
    where
    module R = Reduction mi a x₀ h₀ P

    drop : (z : S) → ⟨ R.Target z ⟩ → ⟨ (z ∈ˢ a) ⊓ P z ⟩
    drop z = PT.rec (snd ((z ∈ˢ a) ⊓ P z))
      (λ { (inl c) → c
         ; (inr q) → subst (λ w → ⟨ w ∈ˢ a ⟩) (sym (S≡ {x = z} {y = x₀} q)) h₀
                   , subst (λ w → ⟨ P w ⟩) (sym (S≡ {x = z} {y = x₀} q)) px₀ })

    keep : (z : S) → ⟨ (z ∈ˢ a) ⊓ P z ⟩ → ⟨ R.Target z ⟩
    keep z c = ∣ inl c ∣₁

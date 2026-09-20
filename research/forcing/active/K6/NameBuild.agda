{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track A, first half: the ground-side name calculus, Route G.
--
-- Six later K6 tracks build a name the same way: cut a set of entries out of
-- a ground bound by a formula, then certify the result is a name. This file
-- owns the SET half of that, and K6/NameValid.agda owns the CERTIFICATE half.
--
-- ROUTE G, and the route is the whole content of the file. An entry set is an
-- IMAGE, and K3 has two ways to take one. The tier-4 route (StandardNames'
-- imageOn, built from the MemberImage datum) is obstruction O3b and is
-- forbidden here by the architecture's trap T-A1: Pairing and Union do not
-- otherwise owe O3b, and a `spread` taken from StandardNames.Weighted.Over
-- would import it into both. The route taken instead is graph→image
-- (NameImage.agda:190-193), which costs ground Collection plus ground
-- Separation and nothing else, and which asks in exchange for a FORMULA whose
-- reading is the function's graph. The two formulas below, and their two
-- reading theorems, are that price paid in full.
--
-- WHY THE DESCRIPTION OPERATORS ARE PARAMETERS AND NOT APPLICATIONS. Rule 2
-- says seal every ℩-term opaque with its spec, and the measured reason is that
-- an unsealed description term unfolds to a stuck eliminator applied to an
-- axiom field and every later definitional comparison compares those spines.
-- Every description operator this file spends arrives as a module PARAMETER,
-- so it is already maximally stuck: this is NameSpace.agda:78-81's own stated
-- reason for taking ⋃ᴳ and pairOf as parameters rather than rebuilding them.
-- The four sets built here are nevertheless sealed one block per set, and the
-- unsealed control is measured and reported rather than assumed.
--
-- THE PROPER-CLASS DISCIPLINE, which roadmap:205 forbids breaching. Every
-- operation below returns an element of S, and every one of them is bounded by
-- a set the caller already holds: spread by carrierᶠ, entryBound by its
-- argument D, mk by its `bound` argument. No host Σ over S carrying a name
-- certificate appears in any exported type. The check is mechanical and is
-- written out in this track's report.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module K6.NameBuild {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∧̇_; ∀̇∈; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
open import OrdinaryProfile 𝒮 using ( Separation; Collection )
open import CodedVocabulary 𝒮 using ( isKPairΔ; prAtˢ )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

-- ---------------------------------------------------------------------
-- The telescope, which is the ledger
-- ---------------------------------------------------------------------

-- Ruling D4: no K6 file takes OrdinaryZF as a record. The ground axioms this
-- file spends are Collection and Separation, and each is an ARGUMENT of the
-- declaration that spends it, following GroundDescription.agda:19-22 and
-- NameSpace.agda:47-52. Ground Union is spent through ⋃ᴳ, which arrives as an
-- operation; NameSpace.agda:553-560 takes ⋃ᴳ and ⋃ᴳ-spec as parameters for
-- exactly that reason, and the ledger row says so rather than the type.
--
-- Ground Pairing and ground PowerSet are NOT taken. Rule 13: the provisional
-- list in ruling D4 names five ground axioms, and this file measured that it
-- uses two of them directly, one through an operation, and neither of the
-- remaining two at all. PowerSet reappears in K6/NameValid.agda, where
-- `candidates` genuinely spends it.

module Calculus
  (paths         : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
  (ext-path      : {a b : S} → ((x : S) → (x ∈ˢ a) ≡ (x ∈ˢ b)) → a ≡ b)
  (carrierᶠ      : S)
  (entry         : S → S → S)
  (entry-isKPair : (x b : S) → ⟨ isKPairΔ (entry x b) x b ⟩)
  (kpair-unique  : (q x b : S) → ⟨ isKPairΔ q x b ⟩ → q ≡ entry x b)
  (colAt         : ∀ {k} → Formula S (suc (suc k)) → Vec S k → Formula S 2)
  (colAt-reading : ∀ {k} (φ : Formula S (suc (suc k))) (ps : Vec S k) (y x : S)
                 → ((y ∷ x ∷ []) ⊨ colAt φ ps) ≡ ((y ∷ x ∷ ps) ⊨ φ))
  (separateOf      : Separation → (a : S) → Formula S 1 → S)
  (separateOf-spec : (sep : Separation) (a : S) (φ : Formula S 1) (x : S)
                   → (x ∈ˢ separateOf sep a φ) ≡ ((x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)))
  (graph→image : Collection → Separation → (f : S → S) (a : S)
               → (graph : Formula S 2)
               → ((x : S) → ⟨ x ∈ˢ a ⟩ → ⟨ (f x ∷ x ∷ []) ⊨ graph ⟩)
               → ((x : S) → ⟨ x ∈ˢ a ⟩ → (y : S)
                  → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩ → y ≡ f x)
               → Σ[ T ∈ S ] ((z : S) → (z ∈ˢ T)
                   ≡ ⋁ S (λ x → (x ∈ˢ a) ⊓ (z ≈ˢ f x))))
  (⋃ᴳ      : S → S)
  (⋃ᴳ-spec : (a x : S) → (x ∈ˢ ⋃ᴳ a) ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ (x ∈ˢ y)))
  where

  -- The two crossings between the structure's equality and the host's path.
  -- Named once; every use of `paths` below goes through one of them.

  ≈ˢ→≡ : {x y : S} → ⟨ x ≈ˢ y ⟩ → x ≡ y
  ≈ˢ→≡ {x} {y} = subst ⟨_⟩ (paths x y)

  ≡→≈ˢ : {x y : S} → x ≡ y → ⟨ x ≈ˢ y ⟩
  ≡→≈ˢ {x} {y} = subst ⟨_⟩ (sym (paths x y))

  ≈ˢ-refl : (x : S) → ⟨ x ≈ˢ x ⟩
  ≈ˢ-refl x = ≡→≈ˢ refl

  -- ---------------------------------------------------------------------
  -- The entry graph, frozen at one subname
  -- ---------------------------------------------------------------------

  -- graph→image asks for a Formula S 2 whose reading at (y , p) says
  -- "y is the value of the function at p". For the function p ↦ entry x p the
  -- graph is K2's Kuratowski pair reader with the subname x FROZEN as a
  -- constant, which is what colAt does (NameImage.agda:285-290).
  --
  -- The de Bruijn assignment is the only place a silent error can hide, and
  -- rule 6 is sharp here: this formula sits at uniform depth, so a swapped
  -- slot still elaborates as a well-scoped Formula S 2. The reading theorem
  -- is the only guard, and the break file K6/breaks/KPairSwap.agda-break
  -- swaps u and v to confirm the guard bites.

  kpairFo : S → Formula S 2
  kpairFo x = colAt (prAtˢ zero (suc (suc zero)) (suc zero)) (x ∷ [])

  kpairFo-reading : (x y p : S) → ((y ∷ p ∷ []) ⊨ kpairFo x) ≡ isKPairΔ y x p
  kpairFo-reading x y p =
    colAt-reading (prAtˢ zero (suc (suc zero)) (suc zero)) (x ∷ []) y p

  -- Being the Kuratowski pair of x and p, and being the kernel's entry, are
  -- the same proposition. Forward is K3's kpair-unique, which is where ground
  -- extensionality is spent; backward is the kernel's own entry-isKPair
  -- transported along the path. This is the single lemma that lets a coded
  -- formula describe a term-level entry.

  kpair-is-entry : (x p e : S) → isKPairΔ e x p ≡ (e ≈ˢ entry x p)
  kpair-is-entry x p e = ⇔toPath {P = isKPairΔ e x p} {Q = e ≈ˢ entry x p}
    (λ h → ≡→≈ˢ (kpair-unique e x p h))
    (λ h → subst (λ u → ⟨ isKPairΔ u x p ⟩) (sym (≈ˢ→≡ h)) (entry-isKPair x p))

  -- ---------------------------------------------------------------------
  -- One subname, spread over every condition
  -- ---------------------------------------------------------------------

  -- This is StandardNames.agda:299-304's `spread` with its route replaced.
  -- There the image is imageOn, which is the tier-4 datum; here it is the
  -- definable-graph image, and the specification is character for character
  -- the same. That equality of specifications is the point: a consumer cannot
  -- tell which route produced the set, and the obstruction ledger can.

  private
    spreadImage : Collection → Separation → (x : S)
                → Σ[ T ∈ S ] ((z : S) → (z ∈ˢ T)
                    ≡ ⋁ S (λ p → (p ∈ˢ carrierᶠ) ⊓ (z ≈ˢ entry x p)))
    spreadImage coll sep x =
      graph→image coll sep (entry x) carrierᶠ (kpairFo x) defines only
      where
        defines : (p : S) → ⟨ p ∈ˢ carrierᶠ ⟩
                → ⟨ (entry x p ∷ p ∷ []) ⊨ kpairFo x ⟩
        defines p _ = subst ⟨_⟩ (sym (kpairFo-reading x (entry x p) p))
                        (entry-isKPair x p)

        only : (p : S) → ⟨ p ∈ˢ carrierᶠ ⟩ → (y : S)
             → ⟨ (y ∷ p ∷ []) ⊨ kpairFo x ⟩ → y ≡ entry x p
        only p _ y h = kpair-unique y x p (subst ⟨_⟩ (kpairFo-reading x y p) h)

  -- The seal, one block per set (rule 2, trap T-A2). Every description
  -- operator reaching this term is already a parameter, so nothing can unfold
  -- through it; the seal is kept because the architecture asks for it at the
  -- point of definition, and the unsealed control is measured separately.

  opaque
    spread : Collection → Separation → S → S
    spread coll sep x = fst (spreadImage coll sep x)

    spread-spec : (coll : Collection) (sep : Separation) (x e : S)
                → (e ∈ˢ spread coll sep x)
                ≡ ⋁ S (λ p → (p ∈ˢ carrierᶠ) ⊓ (e ≈ˢ entry x p))
    spread-spec coll sep x = snd (spreadImage coll sep x)

  -- The two directions, packaged. Nothing below reads spread-spec directly.

  spread-in : (coll : Collection) (sep : Separation) (x p : S)
            → ⟨ p ∈ˢ carrierᶠ ⟩ → ⟨ entry x p ∈ˢ spread coll sep x ⟩
  spread-in coll sep x p hp =
    subst ⟨_⟩ (sym (spread-spec coll sep x (entry x p)))
      ∣ p , hp , ≈ˢ-refl (entry x p) ∣₁

  spread-out : (coll : Collection) (sep : Separation) (x e : S)
             → ⟨ e ∈ˢ spread coll sep x ⟩
             → ⟨ ⋁ S (λ p → (p ∈ˢ carrierᶠ) ⊓ (e ≈ˢ entry x p)) ⟩
  spread-out coll sep x e = subst ⟨_⟩ (spread-spec coll sep x e)

  -- ---------------------------------------------------------------------
  -- The graph of `spread` itself
  -- ---------------------------------------------------------------------

  -- The outer image needs a formula for spread, and spread is a description
  -- term, so the formula cannot describe it by unfolding. It describes it
  -- EXTENSIONALLY instead: y is the spread of x when every member of y is an
  -- entry of x at some condition, and every condition carries such an entry
  -- in y. Both clauses are bounded, by y and by carrierᶠ, and the weight
  -- carrier is frozen by colAt exactly as above.
  --
  -- The second clause is the one a transcriber drops, because the first alone
  -- already "says what the members are". It does not: without it every subset
  -- of the spread satisfies the formula, `only` cannot conclude and the image
  -- is not determined. K6/breaks/SpreadHalf.agda-break is that omission.

  spreadFo : Formula S 2
  spreadFo = colAt
    ( ∀̇∈ (var zero)
        (∃̇∈ (var (suc (suc (suc zero))))
          (prAtˢ (suc zero) (suc (suc (suc zero))) zero))
    ∧̇ ∀̇∈ (var (suc (suc zero)))
        (∃̇∈ (var (suc zero))
          (prAtˢ zero (suc (suc (suc zero))) (suc zero))) )
    (carrierᶠ ∷ [])

  spreadFo-reading : (y x : S) → ((y ∷ x ∷ []) ⊨ spreadFo)
    ≡ ( (⋀ S (λ e → (e ∈ˢ y) ⇒ ⋁ S (λ p → (p ∈ˢ carrierᶠ) ⊓ isKPairΔ e x p)))
      ⊓ (⋀ S (λ p → (p ∈ˢ carrierᶠ) ⇒ ⋁ S (λ e → (e ∈ˢ y) ⊓ isKPairΔ e x p))) )
  spreadFo-reading y x =
    colAt-reading
      ( ∀̇∈ (var zero)
          (∃̇∈ (var (suc (suc (suc zero))))
            (prAtˢ (suc zero) (suc (suc (suc zero))) zero))
      ∧̇ ∀̇∈ (var (suc (suc zero)))
          (∃̇∈ (var (suc zero))
            (prAtˢ zero (suc (suc (suc zero))) (suc zero))) )
      (carrierᶠ ∷ []) y x

  -- ---------------------------------------------------------------------
  -- The entry bound
  -- ---------------------------------------------------------------------

  -- { entry x p : x ∈ D , p ∈ carrierᶠ }, the ground set every later K6 name
  -- is cut out of. It is the union of the layers, and the layers are the
  -- image of D under spread; the union is where ground Union is spent and the
  -- two images are where Collection and Separation are.

  private
    spreadLayers : (coll : Collection) (sep : Separation) (D : S)
                 → Σ[ T ∈ S ] ((z : S) → (z ∈ˢ T)
                     ≡ ⋁ S (λ x → (x ∈ˢ D) ⊓ (z ≈ˢ spread coll sep x)))
    spreadLayers coll sep D =
      graph→image coll sep (spread coll sep) D spreadFo defines only
      where
        defines : (x : S) → ⟨ x ∈ˢ D ⟩
                → ⟨ (spread coll sep x ∷ x ∷ []) ⊨ spreadFo ⟩
        defines x _ = subst ⟨_⟩ (sym (spreadFo-reading (spread coll sep x) x))
          ( (λ e he → PT.map
               (λ { (p , hp , eq) →
                    p , hp , subst ⟨_⟩ (sym (kpair-is-entry x p e)) eq })
               (spread-out coll sep x e he))
          , (λ p hp → ∣ entry x p , spread-in coll sep x p hp
                     , entry-isKPair x p ∣₁) )

        only : (x : S) → ⟨ x ∈ˢ D ⟩ → (y : S)
             → ⟨ (y ∷ x ∷ []) ⊨ spreadFo ⟩ → y ≡ spread coll sep x
        only x _ y h = ext-path step
          where
            hy : ⟨ (⋀ S (λ e → (e ∈ˢ y) ⇒
                     ⋁ S (λ p → (p ∈ˢ carrierᶠ) ⊓ isKPairΔ e x p)))
                 ⊓ (⋀ S (λ p → (p ∈ˢ carrierᶠ) ⇒
                     ⋁ S (λ e → (e ∈ˢ y) ⊓ isKPairΔ e x p))) ⟩
            hy = subst ⟨_⟩ (spreadFo-reading y x) h

            to : (e : S) → ⟨ e ∈ˢ y ⟩ → ⟨ e ∈ˢ spread coll sep x ⟩
            to e he = subst ⟨_⟩ (sym (spread-spec coll sep x e))
              (PT.map (λ { (p , hp , hk) →
                           p , hp , subst ⟨_⟩ (kpair-is-entry x p e) hk })
                      (fst hy e he))

            fro : (e : S) → ⟨ e ∈ˢ spread coll sep x ⟩ → ⟨ e ∈ˢ y ⟩
            fro e he = PT.rec (snd (e ∈ˢ y))
              (λ { (p , hp , eq) → PT.rec (snd (e ∈ˢ y))
                     (λ { (e' , he' , hk) →
                          subst (λ u → ⟨ u ∈ˢ y ⟩)
                            (kpair-unique e' x p hk ∙ sym (≈ˢ→≡ eq)) he' })
                     (snd hy p hp) })
              (spread-out coll sep x e he)

            step : (e : S) → (e ∈ˢ y) ≡ (e ∈ˢ spread coll sep x)
            step e = ⇔toPath (to e) (fro e)

  -- The seal, a SEPARATE block from spread's (rule 2b, trap T-A3). K5's
  -- Track I measured that sealing the outer operation suffices and that one
  -- unsealed nested argument under an unsealed outer already hangs; here both
  -- are sealed and the nesting is one description term inside another.

  opaque
    entryBound : Collection → Separation → (D : S) → S
    entryBound coll sep D = ⋃ᴳ (fst (spreadLayers coll sep D))

    entryBound-spec : (coll : Collection) (sep : Separation) (D e : S)
                    → (e ∈ˢ entryBound coll sep D)
                    ≡ ⋁ S (λ x → (x ∈ˢ D) ⊓
                        ⋁ S (λ p → (p ∈ˢ carrierᶠ) ⊓ (e ≈ˢ entry x p)))
    entryBound-spec coll sep D e =
        ⋃ᴳ-spec (fst (spreadLayers coll sep D)) e
      ∙ ⇔toPath to fro
      where
        target : Ω
        target = ⋁ S (λ x → (x ∈ˢ D) ⊓
                   ⋁ S (λ p → (p ∈ˢ carrierᶠ) ⊓ (e ≈ˢ entry x p)))

        to : ⟨ ⋁ S (λ u → (u ∈ˢ fst (spreadLayers coll sep D)) ⊓ (e ∈ˢ u)) ⟩
           → ⟨ target ⟩
        to = PT.rec PT.squash₁ (λ { (u , hu , he) →
          PT.map (λ { (x , hx , eq) →
                      x , hx , spread-out coll sep x e
                                 (subst (λ t → ⟨ e ∈ˢ t ⟩) (≈ˢ→≡ eq) he) })
                 (subst ⟨_⟩ (snd (spreadLayers coll sep D) u) hu) })

        fro : ⟨ target ⟩
            → ⟨ ⋁ S (λ u → (u ∈ˢ fst (spreadLayers coll sep D)) ⊓ (e ∈ˢ u)) ⟩
        fro = PT.map (λ { (x , hx , hp) →
            spread coll sep x
          , subst ⟨_⟩ (sym (snd (spreadLayers coll sep D) (spread coll sep x)))
              ∣ x , hx , ≈ˢ-refl (spread coll sep x) ∣₁
          , subst ⟨_⟩ (sym (spread-spec coll sep x e)) hp })

  entryBound-in : (coll : Collection) (sep : Separation) (D x p : S)
                → ⟨ x ∈ˢ D ⟩ → ⟨ p ∈ˢ carrierᶠ ⟩
                → ⟨ entry x p ∈ˢ entryBound coll sep D ⟩
  entryBound-in coll sep D x p hx hp =
    subst ⟨_⟩ (sym (entryBound-spec coll sep D (entry x p)))
      ∣ x , hx , ∣ p , hp , ≈ˢ-refl (entry x p) ∣₁ ∣₁

  entryBound-out : (coll : Collection) (sep : Separation) (D e : S)
                 → ⟨ e ∈ˢ entryBound coll sep D ⟩
                 → ⟨ ⋁ S (λ x → (x ∈ˢ D) ⊓
                       ⋁ S (λ p → (p ∈ˢ carrierᶠ) ⊓ (e ≈ˢ entry x p))) ⟩
  entryBound-out coll sep D e = subst ⟨_⟩ (entryBound-spec coll sep D e)

  -- ---------------------------------------------------------------------
  -- The name builder
  -- ---------------------------------------------------------------------

  -- One Separation against a bound the caller supplies. Every K6 name is of
  -- this shape, and the bound is always entryBound of something, which is
  -- what keeps the construction inside a set: mk cannot be applied to a class
  -- because its first set argument is an element of S.

  opaque
    mk : Separation → (bound : S) → Formula S 1 → S
    mk sep bound θ = separateOf sep bound θ

    mk-spec : (sep : Separation) (bound : S) (θ : Formula S 1) (e : S)
            → (e ∈ˢ mk sep bound θ) ≡ ((e ∈ˢ bound) ⊓ ((e ∷ []) ⊨ θ))
    mk-spec sep bound θ = separateOf-spec sep bound θ

  mk-in : (sep : Separation) (bound : S) (θ : Formula S 1) (e : S)
        → ⟨ e ∈ˢ bound ⟩ → ⟨ (e ∷ []) ⊨ θ ⟩ → ⟨ e ∈ˢ mk sep bound θ ⟩
  mk-in sep bound θ e hb hθ = subst ⟨_⟩ (sym (mk-spec sep bound θ e)) (hb , hθ)

  mk-bound : (sep : Separation) (bound : S) (θ : Formula S 1) (e : S)
           → ⟨ e ∈ˢ mk sep bound θ ⟩ → ⟨ e ∈ˢ bound ⟩
  mk-bound sep bound θ e h = fst (subst ⟨_⟩ (mk-spec sep bound θ e) h)

  mk-sat : (sep : Separation) (bound : S) (θ : Formula S 1) (e : S)
         → ⟨ e ∈ˢ mk sep bound θ ⟩ → ⟨ (e ∷ []) ⊨ θ ⟩
  mk-sat sep bound θ e h = snd (subst ⟨_⟩ (mk-spec sep bound θ e) h)

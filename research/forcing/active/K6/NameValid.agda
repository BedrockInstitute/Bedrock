{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track A, second half: the name certificate and Bell 1.38's domain.
--
-- K6/NameBuild.agda builds ground SETS. This file answers the two questions a
-- consumer asks next. When is such a set a NAME? And, for the Power Set
-- proof, which names can a given name's power-set candidate possibly be?
--
-- BELL 1.38 IS REFUTED AS WRITTEN, and this file carries the replacement.
-- The roadmap (roadmap:205) tells K6 to "normalize candidates to
-- Boolean-valued functions on the given name's domain in M". There is no such
-- object in this tree. A name is a material set of Kuratowski entries, the
-- same subname may occur at many entries at many weights, and K3 says so in
-- its own words at NameWeight.agda:5-14: "there is no function from a subname
-- to a weight to be had, and the object that does exist is the SET of
-- weights". A census over the compile root for a function-space construction
-- returns only CardinalBridge.agda:185's isFunction, a predicate.
--
-- The replacement is nameBound (NameSpace.agda:640-641), and it is not a
-- weaker substitute: it is the only reason Power Set is reachable at all. If
-- every subname of a name n lies in a set C, then n lies three power sets
-- above C ∪ W, so the names with a prescribed domain form a SET, and one
-- Separation against the coded name recogniser cuts it out. Redundancy, many
-- entry sets reading to the same weight, is harmless, because 1.38 uses only
-- the direction nameBound-contains supplies.
--
-- THE ARITY TRAP IN THAT LINE. The recogniser nameAtˢ is stated at ARITY TWO,
-- its adequacy at (t ∷ W ∷ []) (NameSpace.agda:951-953), while separateOf
-- takes a Formula S 1 (GroundDescription.agda:130-131). The weight carrier
-- must be frozen into the formula, and the frozen formula owes its own
-- reading theorem. nameFo and nameFo-reading below are that, and they are the
-- only reason `candidates` is a set of genuine names rather than a set that
-- merely typechecks.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module K6.NameValid {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
open import OrdinaryProfile 𝒮 using ( Separation; Collection; PowerSet )
open import CodedVocabulary 𝒮 using ( sepAt; sepAt-reading )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

-- ---------------------------------------------------------------------
-- The telescope, which is the ledger
-- ---------------------------------------------------------------------

-- Ground Separation and ground PowerSet are the two axioms spent here, each
-- an argument of the declaration that spends it. PowerSet arrives only
-- through nameBound, and NameSpace.agda:47-52 fixed that discipline first:
-- "PowerSet ... is an explicit argument of the two declarations that use it
-- and not a hypothesis of anything". K6 keeps it exactly.
--
-- IsNameᴾ is the abstract recogniser of K5's PosetSide (K5/Structures.agda:
-- 781), and the weight carrier of the poset side is carrierᶠ, which is why
-- name-adequate below is stated at (t ∷ carrierᶠ ∷ []).

module Valid
  (carrierᶠ      : S)
  (entry         : S → S → S)
  (entry-inj     : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c))
  (Child         : S → S → Type ℓ)
  (child-weight  : (x n : S) → Child x n → ∥ Σ[ b ∈ S ] ⟨ entry x b ∈ˢ n ⟩ ∥₁)
  (IsNameᴾ       : S → Ω)
  (name-introᴾ   : (n : S)
                 → ((e : S) → ⟨ e ∈ˢ n ⟩
                    → ∥ Σ[ x ∈ S ] Σ[ b ∈ S ]
                          ((e ≡ entry x b) × ⟨ b ∈ˢ carrierᶠ ⟩) ∥₁)
                 → ((x : S) → Child x n → ⟨ IsNameᴾ x ⟩)
                 → ⟨ IsNameᴾ n ⟩)
  (separateOf      : Separation → (a : S) → Formula S 1 → S)
  (separateOf-spec : (sep : Separation) (a : S) (φ : Formula S 1) (x : S)
                   → (x ∈ˢ separateOf sep a φ) ≡ ((x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)))
  (paths : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
  (mk : Separation → (bound : S) → Formula S 1 → S)
  (mk-bound : (sep : Separation) (bound : S) (θ : Formula S 1) (e : S)
            → ⟨ e ∈ˢ mk sep bound θ ⟩ → ⟨ e ∈ˢ bound ⟩)
  (entryBound : Collection → Separation → (D : S) → S)
  (entryBound-out : (coll : Collection) (sep : Separation) (D e : S)
                  → ⟨ e ∈ˢ entryBound coll sep D ⟩
                  → ⟨ ⋁ S (λ x → (x ∈ˢ D) ⊓
                        ⋁ S (λ p → (p ∈ˢ carrierᶠ) ⊓ (e ≈ˢ entry x p))) ⟩)
  (support  : S → S)
  (nameBound : PowerSet → (C : S) → S)
  (nameBound-contains : (pow : PowerSet) (C n : S) → ⟨ IsNameᴾ n ⟩
                      → ((x : S) → Child x n → ⟨ x ∈ˢ C ⟩)
                      → ⟨ n ∈ˢ nameBound pow C ⟩)
  (nameAtᶠ       : Formula S 2)
  (name-adequate : (t : S) → ((t ∷ carrierᶠ ∷ []) ⊨ nameAtᶠ) ≡ IsNameᴾ t)
  where

  -- ---------------------------------------------------------------------
  -- The certificate
  -- ---------------------------------------------------------------------

  -- A set all of whose members are entries at a condition, carrying a subname
  -- already known to be a name, is a name. This is K3's name-intro
  -- (NameKernel.agda:473-475) with its two clauses supplied from ONE
  -- hypothesis, which is the form every later K6 track can actually discharge:
  -- a track knows what it put into the set, not what the Child relation says
  -- about it afterwards.
  --
  -- The hereditary clause is the half that does real work. A Child edge is a
  -- truncated entry, so it offers SOME weight b with entry x b in n; the
  -- hypothesis then decomposes that same entry as entry x' p, and injectivity
  -- (entry-inj) says x' is x. Without injectivity the two decompositions could
  -- differ and the subname's certificate would be about a different set.

  name-from-entries : (n : S)
    → ((e : S) → ⟨ e ∈ˢ n ⟩
       → ∥ Σ[ x ∈ S ] Σ[ p ∈ S ]
             ((e ≡ entry x p) × (⟨ p ∈ˢ carrierᶠ ⟩ × ⟨ IsNameᴾ x ⟩)) ∥₁)
    → ⟨ IsNameᴾ n ⟩
  name-from-entries n h = name-introᴾ n shape hereditary
    where
      shape : (e : S) → ⟨ e ∈ˢ n ⟩
            → ∥ Σ[ x ∈ S ] Σ[ b ∈ S ]
                  ((e ≡ entry x b) × ⟨ b ∈ˢ carrierᶠ ⟩) ∥₁
      shape e he = PT.map (λ { (x , p , eq , hp , _) → x , p , eq , hp }) (h e he)

      hereditary : (x : S) → Child x n → ⟨ IsNameᴾ x ⟩
      hereditary x edge = PT.rec (snd (IsNameᴾ x))
        (λ { (b , he) → PT.rec (snd (IsNameᴾ x))
               (λ { (x' , p , eq , _ , hx') →
                    subst (λ u → ⟨ IsNameᴾ u ⟩)
                      (sym (fst (entry-inj eq))) hx' })
               (h (entry x b) he) })
        (child-weight x n edge)

  -- The architecture's shape, which is the one Tracks B, F, G and H paste.
  -- It is name-from-entries at the set mk builds, and mk-spec is not consumed:
  -- a caller proves the entry decomposition from what it cut, not from the
  -- Separation's specification.

  mk-name : (sep : Separation) (bound : S) (θ : Formula S 1)
    → ((e : S) → ⟨ e ∈ˢ mk sep bound θ ⟩
       → ∥ Σ[ x ∈ S ] Σ[ p ∈ S ]
             ((e ≡ entry x p) × (⟨ p ∈ˢ carrierᶠ ⟩ × ⟨ IsNameᴾ x ⟩)) ∥₁)
    → ⟨ IsNameᴾ (mk sep bound θ) ⟩
  mk-name sep bound θ = name-from-entries (mk sep bound θ)

  -- The composition all six consuming tracks want, and the reason Track A is
  -- a track rather than six redrafts. Cut anything out of the entry bound of
  -- a set of names and the result is a name: the Separation keeps the cut
  -- inside the bound, the bound's specification decomposes each member as an
  -- entry at a condition, and the hypothesis certifies its first coordinate.
  -- A consumer supplies one thing, that the members of D are names, and never
  -- touches a truncation.

  cut-name : (coll : Collection) (sep : Separation) (D : S) (θ : Formula S 1)
           → ((x : S) → ⟨ x ∈ˢ D ⟩ → ⟨ IsNameᴾ x ⟩)
           → ⟨ IsNameᴾ (mk sep (entryBound coll sep D) θ) ⟩
  cut-name coll sep D θ hD =
    name-from-entries (mk sep (entryBound coll sep D) θ) decompose
    where
      decompose : (e : S) → ⟨ e ∈ˢ mk sep (entryBound coll sep D) θ ⟩
        → ∥ Σ[ x ∈ S ] Σ[ p ∈ S ]
              ((e ≡ entry x p) × (⟨ p ∈ˢ carrierᶠ ⟩ × ⟨ IsNameᴾ x ⟩)) ∥₁
      decompose e he = PT.rec PT.squash₁
        (λ { (x , hx , inner) → PT.map
               (λ { (p , hp , eq) →
                    x , p , subst ⟨_⟩ (paths e (entry x p)) eq , hp , hD x hx })
               inner })
        (entryBound-out coll sep D e
          (mk-bound sep (entryBound coll sep D) θ e he))

  -- ---------------------------------------------------------------------
  -- The recogniser, frozen to arity one
  -- ---------------------------------------------------------------------

  -- sepAt (CodedVocabulary.agda:541-546) turns a Formula S (suc k) into a
  -- Formula S 1 by freezing every slot but the first into a constant, and
  -- carries the reading across. Composing that with name-adequate is the whole
  -- of nameFo-reading, and it is the theorem that makes `candidates` a set of
  -- names: the formula is at uniform depth, so nothing but the reading
  -- distinguishes it from a formula about the wrong slot.

  nameFo : Formula S 1
  nameFo = sepAt nameAtᶠ (carrierᶠ ∷ [])

  nameFo-reading : (t : S) → ((t ∷ []) ⊨ nameFo) ≡ IsNameᴾ t
  nameFo-reading t = sepAt-reading nameAtᶠ (carrierᶠ ∷ []) t ∙ name-adequate t

  -- ---------------------------------------------------------------------
  -- Bell 1.38's candidate domain
  -- ---------------------------------------------------------------------

  -- One Separation against the frozen recogniser, inside one nameBound of one
  -- support. This is the single place in Track A where ground PowerSet is
  -- spent, and it is the place the proper-class trap would be sprung if the
  -- bound were dropped: the class of names whose subnames all lie in a given
  -- set has no ground code until nameBound supplies one, and no ⋁ S slot of
  -- OrdinaryProfile.PowerSet can be filled by a host Σ.

  opaque
    candidates : Separation → PowerSet → (σ : S) → S
    candidates sep pow σ = separateOf sep (nameBound pow (support σ)) nameFo

    candidates-spec : (sep : Separation) (pow : PowerSet) (σ χ : S)
      → (χ ∈ˢ candidates sep pow σ)
      ≡ ((χ ∈ˢ nameBound pow (support σ)) ⊓ ((χ ∷ []) ⊨ nameFo))
    candidates-spec sep pow σ =
      separateOf-spec sep (nameBound pow (support σ)) nameFo

  -- Every name whose subnames lie in the support is a candidate. This is the
  -- only direction Bell 1.38's proof uses, and it is nameBound-contains plus
  -- the reading theorem, with nothing between them.

  candidates-contains : (sep : Separation) (pow : PowerSet) (σ χ : S)
                      → ⟨ IsNameᴾ χ ⟩
                      → ((x : S) → Child x χ → ⟨ x ∈ˢ support σ ⟩)
                      → ⟨ χ ∈ˢ candidates sep pow σ ⟩
  candidates-contains sep pow σ χ hχ sub =
    subst ⟨_⟩ (sym (candidates-spec sep pow σ χ))
      ( nameBound-contains pow (support σ) χ hχ sub
      , subst ⟨_⟩ (sym (nameFo-reading χ)) hχ )

  -- And every candidate is a name. Track G asks for this under the name
  -- powerCandidates-name; it is the other half of the same reading theorem
  -- and costs nothing, and it is what makes the quantifier of the Power Set
  -- proof range over names rather than over arbitrary codes.

  candidates-name : (sep : Separation) (pow : PowerSet) (σ χ : S)
                  → ⟨ χ ∈ˢ candidates sep pow σ ⟩ → ⟨ IsNameᴾ χ ⟩
  candidates-name sep pow σ χ h =
    subst ⟨_⟩ (nameFo-reading χ)
      (snd (subst ⟨_⟩ (candidates-spec sep pow σ χ) h))

  candidates-bound : (sep : Separation) (pow : PowerSet) (σ χ : S)
                   → ⟨ χ ∈ˢ candidates sep pow σ ⟩
                   → ⟨ χ ∈ˢ nameBound pow (support σ) ⟩
  candidates-bound sep pow σ χ h =
    fst (subst ⟨_⟩ (candidates-spec sep pow σ χ) h)

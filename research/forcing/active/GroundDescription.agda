{-# OPTIONS --cubical --safe --guardedness #-}

-- K2 module M5: the ground description bridge.
--
-- Every existence field of the ordinary first-order profile is a TRUNCATED
-- existential: the algebra's ⋁ is ∃[]-syntax (Base/Truth.lagda.md:130), so
-- "there is a set whose members are exactly the Q" arrives as ∥ Σ ... ∥₁ and
-- cannot be projected. This module turns each such statement into a term, by
-- the route the L development already uses (L/Axioms/Basic.lagda.md:524-529):
-- extensionality makes the type of realizers a proposition in the strong form
-- isContr, isContr is itself a proposition, so the truncation eliminates into
-- it, and the description operator of FOL.ZFModel then reads the set off.
--
-- The hypotheses, and this is the whole list: the structure 𝒮, ordinary
-- Extensionality, and the path realization of ≈ˢ. In particular the module
-- does NOT take OrdinaryZF. That record carries hasInfinity and foundation
-- (OrdinaryProfile.agda:132,135), neither of which any description consumes,
-- and taking it would make the parameter list an inaccurate ledger. The same
-- discipline governs hasImage′ at the end of the file: it takes Separation and
-- Collection as two standalone arguments, where K1's hasImage
-- (OrdinaryProfile.agda:340-351) took the whole eight-field record and used
-- exactly those two fields.
--
-- Nothing here needs LEM, at any level.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module GroundDescription
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import FOL.ZFModel 𝒮 using ( IsSetOf; SetOf; setOf-unique; ℩; ℩-spec )
open import Cubical.Foundations.Prelude using ( isPropIsContr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

-- OrdinaryProfile is opened by an alias rather than wholesale, so that the
-- field projections of its OrdinaryZF record stay behind the OP qualifier and
-- cannot collide with the fields of the fragment records declared below.

module OP = OrdinaryProfile 𝒮

open OP
  using ( iff; spec-to-iff; Extensionality; Pairing; Union; PowerSet
        ; Separation; Collection; OrdinaryZF )
open OP.PathRealization paths using ( ≈ˢ-to-path )
open OP.Swap using ( swapFo; ⊨-swap )

-- The shape every existence field of the profile has, named once. Unfolding
-- is definitional, so a field such as PowerSet a, whose type is written out
-- in full at OrdinaryProfile.agda:73-77, is accepted wherever ⟨ SetExists Q ⟩
-- is demanded, with Q the class that field describes.

SetExists : (S → Ω) → Ω
SetExists Q = ⋁ S (λ b → ⋀ S (λ x → iff (x ∈ˢ b) (Q x)))

-- Host-path extensionality, which is what setOf-unique asks for. Ordinary
-- Extensionality delivers a ≈ˢ b, and the realization hypothesis carries that
-- across to a host path. Note the direction of the two subst arguments inside
-- spec-to-iff: agreement of membership as a path of hProps is exactly the
-- premise the ordinary sentence wants, in both directions.

ext-path : {a b : S} → ((x : S) → (x ∈ˢ a) ≡ (x ∈ˢ b)) → a ≡ b
ext-path {a} {b} h = ≈ˢ-to-path a b (ext a b (spec-to-iff a (λ z → z ∈ˢ b) h))

-- The membership specification, in the two shapes the two layers use. The
-- profile states agreement as the internal biconditional; ZFModel states it
-- as a pointwise path of hProps. Between hProps these are the same thing, by
-- propositional extensionality. K1's iff-to-spec (OrdinaryProfile.agda:49-51)
-- is this lemma for the special case where the class is a membership; a
-- general Q needs the same ⇔toPath and nothing more.

iff-to-isSetOf : (b : S) (Q : S → Ω)
               → ⟨ ⋀ S (λ x → iff (x ∈ˢ b) (Q x)) ⟩ → IsSetOf Q b
iff-to-isSetOf b Q h x = ⇔toPath (h x .fst) (h x .snd)

-- Truncated existence of a realizer becomes unique existence. The eliminator
-- is legitimate because the target isContr (SetOf Q) is a proposition, which
-- is the content of isPropIsContr; extensionality is what makes the target
-- inhabited from a single untruncated witness.

described : (Q : S → Ω) → ⟨ SetExists Q ⟩ → isContr (SetOf Q)
described Q =
  PT.rec isPropIsContr
    (λ { (b , h) → setOf-unique ext-path Q (b , iff-to-isSetOf b Q h) })

-- And unique existence becomes a term, by two projections and no description
-- axiom. Every later coded construction of K2 enters the model through these
-- two lines: the object is the Q, and the-spec is the only way to use it,
-- since at the L instance the paths hypothesis is not refl and the term does
-- not compute.

the : (Q : S → Ω) → ⟨ SetExists Q ⟩ → S
the Q h = ℩ {Q = Q} (described Q h)

the-spec : (Q : S → Ω) (h : ⟨ SetExists Q ⟩) → IsSetOf Q (the Q h)
the-spec Q h = ℩-spec {Q = Q} (described Q h)

-- The class argument of the and the-spec CANNOT be left to unification. A
-- measured negative, with the exact error quoted in this track's report: an
-- element of Ω is a pair of a type and a proof that the type is a
-- proposition, and the class appears in SetExists only under ⟨_⟩ and under
-- the isProp components that _⇒_ and _⊓_ build, so writing the _ (pow a)
-- determines the carrier half of the meta and leaves its isProp half blocked,
-- and the file fails with UnsolvedMetaVariables. The class must be written
-- out. It is spelled once here for each of the only two axiom instances the
-- coded completion takes, so that no call site has to spell it again.

powerOf : PowerSet → (a : S) → S
powerOf pow a = the (λ x → ⋀ S (λ y → (y ∈ˢ x) ⇒ (y ∈ˢ a))) (pow a)

powerOf-spec : (pow : PowerSet) (a : S) (x : S)
             → (x ∈ˢ powerOf pow a) ≡ (⋀ S (λ y → (y ∈ˢ x) ⇒ (y ∈ˢ a)))
powerOf-spec pow a = the-spec (λ x → ⋀ S (λ y → (y ∈ˢ x) ⇒ (y ∈ˢ a))) (pow a)

separateOf : Separation → (a : S) → Formula S 1 → S
separateOf sep a φ = the (λ x → (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)) (sep a φ)

separateOf-spec : (sep : Separation) (a : S) (φ : Formula S 1) (x : S)
                → (x ∈ˢ separateOf sep a φ) ≡ ((x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ))
separateOf-spec sep a φ = the-spec (λ x → (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)) (sep a φ)

-- The fragments. GroundFragment names exactly the four hypotheses the coded
-- completion consumes: extensionality and the path realization for the
-- description bridge above, PowerSet once for the ambient power set, and
-- Separation for every object built inside it. Pairing and Union are split
-- off into ProductFragment because only the ordered-pair constructions need
-- them, and a ledger that mentions them in the core would be wrong.

record GroundFragment : Type (ℓ-suc ℓ) where
  field
    extensional   : Extensionality
    hasPower      : PowerSet
    hasSeparation : Separation
    ≈ˢ-paths      : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y)

record ProductFragment : Type ℓ where
  field
    hasPair  : Pairing
    hasUnion : Union

-- A ground presented as the full ordinary record supplies the fragment; the
-- realization of ≈ˢ is not part of that record and stays an explicit second
-- argument. This is a projection in one direction only: the fragment forgets
-- Infinity, Replacement and Foundation and cannot give them back.

fromOrdinaryZF : OrdinaryZF
               → ((x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
               → GroundFragment
fromOrdinaryZF r p = record
  { extensional   = OP.OrdinaryZF.extensional r
  ; hasPower      = OP.OrdinaryZF.hasPower r
  ; hasSeparation = OP.OrdinaryZF.hasSeparation r
  ; ≈ˢ-paths      = p }

-- Bell's Remark 1 direction that the ordinary profile proves on its own:
-- Collection plus Separation turn a functional relation into an image set.
-- The body is K1's hasImage (OrdinaryProfile.agda:345-398) with its record
-- argument replaced by the two fields the proof actually used, so that
-- Collection appears in a ledger only where it is consumed. K2's core does
-- not consume it at all.
--
-- Functionality is host contractibility, matching the hypothesis shape of the
-- existing strong record. The image class is the one the bound set b and the
-- swapped formula θ cut out of b by a single Separation.

hasImage′ : Separation → Collection
  → (a : S) (φ : Formula S 2)
  → ((x : S) → ⟨ x ∈ˢ a ⟩ → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ φ ⟩))
  → ⟨ ⋁ S (λ b → ⋀ S (λ y → iff (y ∈ˢ b)
       (⋁ S (λ x → (x ∈ˢ a) ⊓ ((y ∷ x ∷ []) ⊨ φ))))) ⟩
hasImage′ sep coll a φ fc =
  PT.rec (snd target)
    (λ { (b , bound) →
         PT.rec (snd target)
           (λ { (img , spec) → ∣ img , assemble b bound img spec ∣₁ })
           (sep b θ) })
    (coll a φ premise)
  where
    image-pred : S → Ω
    image-pred y = ⋁ S (λ x → (x ∈ˢ a) ⊓ ((y ∷ x ∷ []) ⊨ φ))

    target : Ω
    target = ⋁ S (λ b → ⋀ S (λ y → iff (y ∈ˢ b) (image-pred y)))

    θ : Formula S 1
    θ = ∃̇∈ (con a) (swapFo φ)

    θ-reading : (y : S) → ((y ∷ []) ⊨ θ) ≡ (image-pred y)
    θ-reading y =
      cong (⋁ S) (funExt (λ x → cong ((x ∈ˢ a) ⊓_) (⊨-swap φ x y)))

    premise : ⟨ ⋀ S (λ x → (x ∈ˢ a) ⇒ (⋁ S (λ y → (y ∷ x ∷ []) ⊨ φ))) ⟩
    premise x x∈a = ∣ fc x x∈a .fst ∣₁

    assemble : (b : S)
      → ((x : S) → ⟨ x ∈ˢ a ⟩
           → ⟨ ⋁ S (λ y → (y ∈ˢ b) ⊓ ((y ∷ x ∷ []) ⊨ φ)) ⟩)
      → (img : S)
      → ((z : S) → ⟨ iff (z ∈ˢ img) ((z ∈ˢ b) ⊓ ((z ∷ []) ⊨ θ)) ⟩)
      → ⟨ ⋀ S (λ y → iff (y ∈ˢ img) (image-pred y)) ⟩
    assemble b bound img spec = λ y → backward y , forward y
      where
        forward : (y : S) → ⟨ image-pred y ⟩ → ⟨ y ∈ˢ img ⟩
        forward y image =
          PT.rec (snd (y ∈ˢ img))
            (λ { (x , x∈a , sat) →
                 PT.rec (snd (y ∈ˢ img))
                   (λ { (y' , y'∈b , sat') →
                        spec y .snd
                          ( subst (λ w → ⟨ w ∈ˢ b ⟩)
                              (sym (cong fst (sym (fc x x∈a .snd (y , sat))
                                          ∙ fc x x∈a .snd (y' , sat'))))
                              y'∈b
                          , subst ⟨_⟩ (sym (θ-reading y))
                              ∣ x , (x∈a , sat) ∣₁ ) })
                   (bound x x∈a) })
            image

        backward : (y : S) → ⟨ y ∈ˢ img ⟩ → ⟨ image-pred y ⟩
        backward y y∈img =
          subst ⟨_⟩ (θ-reading y) (spec y .fst y∈img .snd)

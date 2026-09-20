{-# OPTIONS --cubical --safe --guardedness #-}

-- K1 probe A and B: the ordinary first-order ZF profile, its Choice extension,
-- the Foundation form equivalences, and the equality coherence facts.
-- Bell 2005, printed pages 17-18, fixes the axiom shapes used here.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module OrdinaryProfile {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import Base.Classical using ( LEM )
open import FOL.ZFStructure
  using ( module hPropStructure; Transitive )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _∧̇_; _⇒̇_; ⊥̇; ¬̇_; ∃̇_; ∀̇_; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

-- The internal biconditional. Spelled from the algebra's implication and meet,
-- exactly the reading of the object-language abbreviation φ ↔ ψ.

iff : Ω → Ω → Ω
iff P Q = (P ⇒ Q) ⊓ (Q ⇒ P)

iff-intro : (P Q : Ω) → (⟨ P ⟩ → ⟨ Q ⟩) → (⟨ Q ⟩ → ⟨ P ⟩) → ⟨ iff P Q ⟩
iff-intro P Q f g = f , g

-- The bridge the later files consume: an hProp-valued membership
-- specification, stated as paths of hProps, becomes the internal biconditional
-- the ordinary sentences read.

spec-to-iff : (b : S) (Q : S → Ω) → ((x : S) → (x ∈ˢ b) ≡ Q x)
            → ⟨ ⋀ S (λ x → iff (x ∈ˢ b) (Q x)) ⟩
spec-to-iff b Q sp =
  λ x → iff-intro (x ∈ˢ b) (Q x)
    (λ h → subst ⟨_⟩ (sp x) h) (λ h → subst ⟨_⟩ (sym (sp x)) h)

iff-to-spec : (a b : S) → ⟨ ⋀ S (λ z → iff (z ∈ˢ a) (z ∈ˢ b)) ⟩
            → (z : S) → (z ∈ˢ a) ≡ (z ∈ˢ b)
iff-to-spec a b h z = ⇔toPath (h z .fst) (h z .snd)

-- The axiom readings. Each is the host reading of an ordinary first-order
-- sentence through FOL.Semantics: existence fields use the truncated
-- existential the hProp algebra interprets, never host contractibility, never
-- a description operator, never a host-chosen witness.

Extensionality : Type ℓ
Extensionality =
  (a b : S) → ⟨ ⋀ S (λ z → iff (z ∈ˢ a) (z ∈ˢ b)) ⟩ → ⟨ a ≈ˢ b ⟩

Pairing : Type ℓ
Pairing =
  (a b : S)
    → ⟨ ⋁ S (λ p → ⋀ S (λ x → iff (x ∈ˢ p) ((x ≈ˢ a) ⊔ (x ≈ˢ b)))) ⟩

Union : Type ℓ
Union =
  (a : S)
    → ⟨ ⋁ S (λ v → ⋀ S (λ x → iff (x ∈ˢ v)
         (⋁ S (λ y → (y ∈ˢ a) ⊓ (x ∈ˢ y))))) ⟩

PowerSet : Type ℓ
PowerSet =
  (a : S)
    → ⟨ ⋁ S (λ v → ⋀ S (λ x → iff (x ∈ˢ v)
         (⋀ S (λ y → (y ∈ˢ x) ⇒ (y ∈ˢ a))))) ⟩

-- Bell (6) with ∅ spelled as "memberless": there is an inductive set, a set
-- with a memberless member in which every member has a member. Not the
-- standard-numeral formulation of the existing strong record.

Infinity : Type ℓ
Infinity =
  ⟨ ⋁ S (λ u → (⋁ S (λ e → (e ∈ˢ u) ⊓ (⋀ S (λ z → (z ∈ˢ e) ⇒ ⊥))))
            ⊓ (⋀ S (λ x → (x ∈ˢ u) ⇒ (⋁ S (λ y → (y ∈ˢ u) ⊓ (x ∈ˢ y)))))) ⟩

Separation : Type ℓ
Separation =
  (a : S) (φ : Formula S 1)
    → ⟨ ⋁ S (λ s → ⋀ S (λ x → iff (x ∈ˢ s) ((x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)))) ⟩

-- Bell (3), Collection form Replacement.

Collection : Type ℓ
Collection =
  (a : S) (φ : Formula S 2)
    → ⟨ ⋀ S (λ x → (x ∈ˢ a) ⇒ (⋁ S (λ y → (y ∷ x ∷ []) ⊨ φ))) ⟩
    → ⟨ ⋁ S (λ b → ⋀ S (λ x → (x ∈ˢ a) ⇒
         (⋁ S (λ y → (y ∈ˢ b) ⊓ ((y ∷ x ∷ []) ⊨ φ))))) ⟩

-- Bell (7), induction form Foundation.

FoundationInduction : Type ℓ
FoundationInduction =
  (φ : Formula S 1)
    → ( (x : S) → ((y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ (y ∷ []) ⊨ φ ⟩)
                  → ⟨ (x ∷ []) ⊨ φ ⟩ )
    → (x : S) → ⟨ (x ∷ []) ⊨ φ ⟩

-- Choice, truncated existence of a choice set, with the hypothesis shape the
-- existing isZFCModel already uses. "Exactly one point" is internal: existence
-- by the truncated existential, uniqueness up to the structure's ≈ˢ.

ChoiceSet : Type ℓ
ChoiceSet =
  (a : S)
    → ((x : S) → ⟨ x ∈ˢ a ⟩ → ∥ Σ[ y ∈ S ] ⟨ y ∈ˢ x ⟩ ∥₁)
    → ((x y : S) → ⟨ x ∈ˢ a ⟩ → ⟨ y ∈ˢ a ⟩
         → ∥ Σ[ z ∈ S ] (⟨ z ∈ˢ x ⟩ × ⟨ z ∈ˢ y ⟩) ∥₁ → x ≡ y)
    → ⟨ ⋁ S (λ c → ⋀ S (λ x → (x ∈ˢ a) ⇒
         ( (⋁ S (λ z → (z ∈ˢ c) ⊓ (z ∈ˢ x)))
         ⊓ (⋀ S (λ z → ⋀ S (λ z' → (((z ∈ˢ c) ⊓ (z ∈ˢ x)) ⊓ ((z' ∈ˢ c) ⊓ (z' ∈ˢ x)))
             ⇒ (z ≈ˢ z'))))))) ⟩

record OrdinaryZF : Type (ℓ-suc ℓ) where
  field
    extensional    : Extensionality
    hasPair        : Pairing
    hasUnion       : Union
    hasPower       : PowerSet
    hasInfinity    : Infinity
    hasSeparation  : Separation
    hasReplacement : Collection
    foundation     : FoundationInduction

record OrdinaryZFC : Type (ℓ-suc ℓ) where
  field
    zf : OrdinaryZF
  open OrdinaryZF zf public
  field
    hasChoice : ChoiceSet

-- Part B: equality coherence.
--
-- What ZFStructure alone supplies: ≈ˢ is a field into Ω, so its truth is a
-- proposition, and host path equality substitutes under both arguments of
-- membership, because membership is a function.

≈ˢ-isProp : (x y : S) → isProp ⟨ x ≈ˢ y ⟩
≈ˢ-isProp x y = snd (x ≈ˢ y)

∈ˢ-cong-subst : (x y z : S) → x ≡ y → (x ∈ˢ z) ≡ (y ∈ˢ z)
∈ˢ-cong-subst x y z p = cong (_∈ˢ z) p

∈ˢ-cong-base : (x y z : S) → y ≡ z → (x ∈ˢ y) ≡ (x ∈ˢ z)
∈ˢ-cong-base x y z p = cong (x ∈ˢ_) p

-- What ordinary Extensionality supplies beyond that: reflexivity, by
-- instantiating the sentence at a = b, where its premise holds trivially; and
-- with reflexivity, every host path reflects into ≈ˢ.

≈ˢ-refl : Extensionality → (x : S) → ⟨ x ≈ˢ x ⟩
≈ˢ-refl ext x = ext x x (λ z → (λ p → p) , (λ p → p))

≈ˢ-of-path : Extensionality → {x y : S} → x ≡ y → ⟨ x ≈ˢ y ⟩
≈ˢ-of-path ext {x} {y} p = subst (λ w → ⟨ x ≈ˢ w ⟩) p (≈ˢ-refl ext x)

-- What is NOT available: from truth of ⟨ x ≈ˢ y ⟩ to equality of the hProps
-- x ∈ˢ z and y ∈ˢ z, in either argument. Neither ZFStructure nor
-- Extensionality gives it; Extensionality runs the other way, from agreement
-- of membership to equality. The facts below hold under the realization
-- contract that identifies ≈ˢ with host paths, which is what the quotient
-- construction of K0 and the concrete V and L instances supply.

module PathRealization
  (≈ˢ-paths : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y)) where

  ≈ˢ-to-path : (x y : S) → ⟨ x ≈ˢ y ⟩ → x ≡ y
  ≈ˢ-to-path x y h = subst ⟨_⟩ (≈ˢ-paths x y) h

  path-to-≈ˢ : (x y : S) → x ≡ y → ⟨ x ≈ˢ y ⟩
  path-to-≈ˢ x y p = subst ⟨_⟩ (sym (≈ˢ-paths x y)) p

  ≈ˢ-sym : (x y : S) → ⟨ x ≈ˢ y ⟩ → ⟨ y ≈ˢ x ⟩
  ≈ˢ-sym x y h = path-to-≈ˢ y x (sym (≈ˢ-to-path x y h))

  subst-member : (x y z : S) → ⟨ x ≈ˢ y ⟩ → (x ∈ˢ z) ≡ (y ∈ˢ z)
  subst-member x y z h = cong (_∈ˢ z) (≈ˢ-to-path x y h)

  subst-base : (x y z : S) → ⟨ y ≈ˢ z ⟩ → (x ∈ˢ y) ≡ (x ∈ˢ z)
  subst-base x y z h = cong (x ∈ˢ_) (≈ˢ-to-path y z h)

-- Part A extra: the relation between induction form Foundation and the
-- ordinary minimal element form, Bell (7) against Bell (7*).

MinimalElement : Type ℓ
MinimalElement =
  (u : S) → ⟨ ⋁ S (λ z → z ∈ˢ u) ⟩
        → ⟨ ⋁ S (λ x → (x ∈ˢ u)
             ⊓ (⋀ S (λ w → ((w ∈ˢ x) ⊓ (w ∈ˢ u)) ⇒ ⊥))) ⟩

TransitiveClosure : Type ℓ
TransitiveClosure =
  (u : S) → ∥ Σ[ t ∈ S ] (⟨ u ∈ˢ t ⟩ × Transitive 𝒮 (λ z → z ∈ˢ t)) ∥₁

module MinimalForm (u : S) where

  noCommon : S → S → Ω
  noCommon x u' = ⋀ S (λ w → ((w ∈ˢ x) ⊓ (w ∈ˢ u')) ⇒ ⊥)

  minimal-sentence : S → Ω
  minimal-sentence x = (x ∈ˢ u) ⊓ noCommon x u

  -- z ∈ u ⇒ ∃ x. x ∈ u ∧ ∀ w. (w ∈ x ∧ w ∈ u) ⇒ ⊥, with u as a constant.

  fo : Formula S 1
  fo = (var zero ∈̇ con u)
    ⇒̇ ∃̇ ((var zero ∈̇ con u)
      ∧̇ (∀̇ (¬̇ ((var zero ∈̇ var (suc zero)) ∧̇ (var zero ∈̇ con u)))))

  fo-reading : (z : S)
    → ((z ∷ []) ⊨ fo) ≡ ((z ∈ˢ u) ⇒ (⋁ S minimal-sentence))
  fo-reading z = refl

-- Induction form gives the minimal element form, given excluded middle at the
-- profile's own level. The classical step is the case split on "x and u have a
-- common member"; with no common member, x itself is minimal.

foundation→minimal : FoundationInduction → LEM ℓ → MinimalElement
foundation→minimal find lem u nonempty =
  PT.rec (snd target) (λ { (z₀ , z₀∈u) → find fo step z₀ z₀∈u }) nonempty
  where
    open MinimalForm u

    target : Ω
    target = ⋁ S minimal-sentence

    step : (x : S) → ((y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ (y ∷ []) ⊨ fo ⟩)
         → ⟨ (x ∷ []) ⊨ fo ⟩
    step x ih x∈u = decide (lem (⋁ S (λ w → (w ∈ˢ x) ⊓ (w ∈ˢ u))))
      where
        decide : ⟨ ⋁ S (λ w → (w ∈ˢ x) ⊓ (w ∈ˢ u)) ⟩
               ⊎ (⟨ ⋁ S (λ w → (w ∈ˢ x) ⊓ (w ∈ˢ u)) ⟩ → Empty.⊥)
               → ⟨ target ⟩
        decide (inl some) = PT.rec (snd target)
          (λ { (w , w∈x , w∈u) → ih w w∈x w∈u }) some
        decide (inr none) =
          ∣ x , (x∈u , λ w common → Empty.rec (none ∣ w , common ∣₁)) ∣₁

-- The converse needs more than excluded middle: the classical proof separates
-- a transitive closure of the starting set by the negated formula and applies
-- the minimal element form there. The profile's truncated operations do not
-- build transitive closures, so the closure is an explicit hypothesis of this
-- lemma, alongside excluded middle and the schema's Separation field.

minimal→foundation : Separation → MinimalElement → LEM ℓ → TransitiveClosure
                   → FoundationInduction
minimal→foundation sep minimal lem tc φ step u₀ =
  decideTop (lem ((u₀ ∷ []) ⊨ φ))
  where
    refute : (t : S) → Transitive 𝒮 (λ z → z ∈ˢ t)
           → (s : S) → ((z : S) → ⟨ iff (z ∈ˢ s)
                ((z ∈ˢ t) ⊓ ((z ∷ []) ⊨ ¬̇ φ)) ⟩)
           → (x : S) → ⟨ x ∈ˢ s ⟩
           → ⟨ ⋀ S (λ w → ((w ∈ˢ x) ⊓ (w ∈ˢ s)) ⇒ ⊥) ⟩
           → ⟨ (u₀ ∷ []) ⊨ φ ⟩
    refute t trans s spec x x∈s disj =
      branch (lem (⋁ S (λ y → (y ∈ˢ x) ⊓ ((y ∷ []) ⊨ ¬̇ φ))))
      where
        x∈t : ⟨ x ∈ˢ t ⟩
        x∈t = spec x .fst x∈s .fst

        nφx : ⟨ (x ∷ []) ⊨ ¬̇ φ ⟩
        nφx = spec x .fst x∈s .snd

        branch : ⟨ ⋁ S (λ y → (y ∈ˢ x) ⊓ ((y ∷ []) ⊨ ¬̇ φ)) ⟩
               ⊎ (⟨ ⋁ S (λ y → (y ∈ˢ x) ⊓ ((y ∷ []) ⊨ ¬̇ φ)) ⟩ → Empty.⊥)
               → ⟨ (u₀ ∷ []) ⊨ φ ⟩
        branch (inl some) = PT.rec (snd ((u₀ ∷ []) ⊨ φ))
          (λ { (y , y∈x , nφy) →
               Empty.rec* (disj y
                 ( y∈x
                 , spec y .snd (trans y∈x x∈t , nφy) )) })
          some
        branch (inr none) = Empty.rec* (nφx (step x all-members))
          where
            all-members : (y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ (y ∷ []) ⊨ φ ⟩
            all-members y y∈x = decideY (lem ((y ∷ []) ⊨ φ))
              where
                decideY : ⟨ (y ∷ []) ⊨ φ ⟩ ⊎ (⟨ (y ∷ []) ⊨ φ ⟩ → Empty.⊥)
                       → ⟨ (y ∷ []) ⊨ φ ⟩
                decideY (inl holds) = holds
                decideY (inr nφy) = Empty.rec
                  (none ∣ y , (y∈x , λ h → Empty.rec (nφy h)) ∣₁)

    decideTop : ⟨ (u₀ ∷ []) ⊨ φ ⟩ ⊎ (⟨ (u₀ ∷ []) ⊨ φ ⟩ → Empty.⊥)
              → ⟨ (u₀ ∷ []) ⊨ φ ⟩
    decideTop (inl holds) = holds
    decideTop (inr fails) =
      PT.rec (snd ((u₀ ∷ []) ⊨ φ))
        (λ { (t , u₀∈t , trans) →
             PT.rec (snd ((u₀ ∷ []) ⊨ φ))
               (λ { (s , spec) →
                    PT.rec (snd ((u₀ ∷ []) ⊨ φ))
                      (λ { (x , x∈s , disj) →
                           refute t trans s spec x x∈s disj })
                      (minimal s
                        ∣ u₀ , spec u₀ .snd (u₀∈t , λ h → Empty.rec (fails h)) ∣₁) })
               (sep t (¬̇ φ)) })
        (tc u₀)

-- The compensation direction for Replacement, the half of Bell's Remark 1
-- equivalence that the ordinary profile proves on its own: Collection plus
-- Separation turns a functional relation into an image set. Functionality is
-- host contractibility here, matching the hypothesis shape of the existing
-- strong record, so this is also the exact statement of what the strong
-- record's Replacement field would need to be re-obtained after transferring.

module Swap where

  swap : Fin 2 → Fin 2
  swap zero    = suc zero
  swap (suc _) = zero

  swapFo : Formula S 2 → Formula S 2
  swapFo = renameFo swap

  module Ren = Sat (hPropAlgebra ℓ) 𝒮 id

  swapAgrees : (x z : S) → Ren.Agrees swap (x ∷ z ∷ []) (z ∷ x ∷ [])
  swapAgrees x z zero       = refl
  swapAgrees x z (suc zero) = refl

  ⊨-swap : (φ : Formula S 2) (x z : S)
         → ((x ∷ z ∷ []) ⊨ swapFo φ) ≡ ((z ∷ x ∷ []) ⊨ φ)
  ⊨-swap φ x z =
    Ren.⊨-rename swap φ (x ∷ z ∷ []) (z ∷ x ∷ []) (swapAgrees x z)

hasImage : OrdinaryZF
  → (a : S) (φ : Formula S 2)
  → ((x : S) → ⟨ x ∈ˢ a ⟩ → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ φ ⟩))
  → ⟨ ⋁ S (λ b → ⋀ S (λ y → iff (y ∈ˢ b)
       (⋁ S (λ x → (x ∈ˢ a) ⊓ ((y ∷ x ∷ []) ⊨ φ))))) ⟩
hasImage r a φ fc =
  PT.rec (snd target)
    (λ { (b , bound) →
         PT.rec (snd target)
           (λ { (img , spec) → ∣ img , assemble b bound img spec ∣₁ })
           (OrdinaryZF.hasSeparation r b θ) })
    (OrdinaryZF.hasReplacement r a φ premise)
  where
    open Swap

    image-pred : S → Ω
    image-pred y = ⋁ S (λ x → (x ∈ˢ a) ⊓ ((y ∷ x ∷ []) ⊨ φ))

    target : Ω
    target = ⋁ S (λ b → ⋀ S (λ y → iff (y ∈ˢ b) (image-pred y)))

    θ : Formula S 1
    θ = ∃̇∈ (con a) (swapFo φ)

    θ-reading : (y : S)
      → ((y ∷ []) ⊨ θ) ≡ (image-pred y)
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

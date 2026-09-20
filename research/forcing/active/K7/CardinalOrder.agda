{-# OPTIONS --cubical --safe --guardedness #-}

-- K7 Track B. THE ORDER THEORY CardinalBridge NEVER HAD.
--
-- G3 of the architecture measured that `injectable` (CardinalBridge.agda:379-388)
-- has ZERO theorems in the whole compile root: no reflexivity, no transitivity,
-- no composition with inclusion, no domain monotonicity. Re-measured here by
-- grep over /tmp/bedrock-k7-probes: the only non-comment occurrences outside
-- CardinalBridge.agda are the CH and GCHω sentences (CHSentence.agda:100-101,
-- :178) and three PARAMETER declarations in K7's own Track D
-- (K7/CompletionTransfer.agda:527, :571, :648), which takes `pull-injectable`
-- as a hypothesis precisely because no lemma exists.
--
-- Ruling Q10 gives this track the ORDER THEORY and not the GCHω-to-CH
-- implication. Architecture 3.8 measured that K10's unrouted third
-- prerequisite reduces to `injectable-trans` composed with `injectable-incl`:
-- instantiate CHSentence.agda:100 at x := chk ω₁, and the hypothesis
-- `injectable (chk ω₁) p` is K9's injection `chk ω₂ ↪ p` composed with the
-- inclusion `chk ω₁ ⊆ chk ω₂`. Both composition steps are in this file.
--
-- WHAT THIS FILE DOES NOT TAKE, AND THE MEASUREMENT BEHIND IT.
--
-- The shared spine (architecture 4.0) gives every K7 file the triple
-- (𝒮 , ext , paths). This file takes 𝒮 ONLY, and takes ordinary
-- Extensionality and the two membership congruences of ≈ˢ as parameters of
-- the one module that spends them. The reason is rule 15's class (iii):
--
--   paths is FALSE at K6's extension structure. K6/Ordinals.agda:141 builds
--   𝒮ᴱ with _≈ˢ_ = λ σ τ → fst σ ≈[G] fst τ, the forcing value equality on
--   NAMES, and Nm = Σ[ n ∈ S ] ⟨ IsNm n ⟩ (K6/Ordinals.agda:127) is not a
--   quotient. Two distinct names with the same value satisfy ≈ˢ and are not
--   equal. A Track B that takes `paths` as a MODULE parameter therefore
--   cannot be instantiated at the extension at all, and the brief's own
--   requirement that ord-compare "serves the ground and the extension"
--   could not be met.
--
-- The two congruences are class (i) at BOTH structures: at the ground they
-- are OrdinaryProfile.PathRealization.subst-member / subst-base
-- (OrdinaryProfile.agda:188-192) applied to `paths`; at the extension they
-- are K5's sat-cong (the shape K6/Ordinals.agda:170-172 takes) at the atomic
-- formula var zero ∈̇ var (suc zero). Nothing else in this file needs paths,
-- so nothing else in this file is ground-only.
--
-- WHAT THIS FILE DOES APPLY. `CardinalBridge 𝒮`, for real, exactly as
-- K6/Ordinals.agda:117 does. A flat telescope of `isOrdinal`, `isKPair`,
-- `isInjection`, `injectable` cannot prove a single semantic deliverable of
-- this track, because every one of them unfolds those predicates to their
-- ⋀ / ⋁ bodies; an opaque parameter plus its defining equation IS the
-- definition. CardinalBridge is not on 1.7's forbidden-application list and
-- is not heavy: K6/Ordinals applies it twice and measures 0.69 s.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module K7.CardinalOrder {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; Term; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ¬̇_
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import FOL.Manipulation.ConstantMapping using ( mapFo )
open import FOL.LevyHierarchy using ( Δ₀; checkΔ₀ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( tt )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

import OrdinaryProfile
import CardinalBridge

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module OP = OrdinaryProfile 𝒮
module CB = CardinalBridge 𝒮

open OP
  using ( iff; Extensionality; Pairing; Separation; Collection
        ; FoundationInduction; MinimalElement; foundation→minimal )
open CB public
  using ( Subsetφ; isSubset; Subset-bridge
        ; IsSingletonφ; isSingleton; IsPairφ; isPair
        ; PairφK; isKPair; PairφK-bridge
        ; IsRelationφ; isRelation; IsFunctionφ; isFunction
        ; IsInjectionφ; isInjection; IsInjection-bridge
        ; InjDomφ; InjRanφ; InjDom-bridge; InjRan-bridge; InjFun-bridge
        ; Injectableφ; injectable; Injectable-bridge
        ; IsTransitiveφ; isTransitiveSet; IsOrdinalφ; isOrdinal
        ; IsOrdinal-bridge; IsCardinalφ; isCardinal
        ; inj-fun; inj-fun-agrees )

module Ren = Sat (hPropAlgebra ℓ) 𝒮 id
open Ren using ( Agrees; ⊨-rename )

--------------------------------------------------------------------------------
-- PART 1. THE TWO SYNTACTIC CERTIFICATES K6/Ordinals ASSERTS IN A COMMENT
--------------------------------------------------------------------------------

-- K6/Ordinals.agda:174-180 takes `chk-ordinal` as a hypothesis and justifies
-- it in prose: "Δ₀ absoluteness of the ordinal predicate along the check map.
-- It is K5's groundSat at IsOrdinalφ, which is Δ₀ because every quantifier in
-- it is bounded ... IsOrdinalφ carries no constants, so mapFo groundName sends
-- it to itself." Neither half was built. Both are built here, and neither
-- costs a hypothesis.
--
-- The first half. IsOrdinalφ (CardinalBridge.agda:522-529, verified at source)
-- is IsTransitiveφ ∧̇ (∀̇∈ (var zero) (∀̇∈ (var (suc zero)) (… ∨̇ (… ∨̇ …)))),
-- and every quantifier in both conjuncts is a bounded ∀̇∈, so the Boolean
-- scanner `bounded` returns true and checkΔ₀ reads the certificate off it.

Δ₀-IsOrdinalφ : Δ₀ IsOrdinalφ
Δ₀-IsOrdinalφ = checkΔ₀ IsOrdinalφ tt

-- The same for the transitivity conjunct on its own, which the extension side
-- of K6 reads separately.

Δ₀-IsTransitiveφ : Δ₀ IsTransitiveφ
Δ₀-IsTransitiveφ = checkΔ₀ IsTransitiveφ tt

-- The contrast that makes the first certificate worth stating. IsCardinalφ is
-- NOT Δ₀: its second conjunct renames Injectableφ = ∃̇ IsInjectionφ, whose
-- existential is unbounded, and IsFunctionφ and InjDomφ carry unbounded
-- quantifiers of their own. The negative is recorded as a break file rather
-- than as an Agda declaration, since `bounded IsCardinalφ` is false and
-- checkΔ₀ has no clause for ∃̇.

-- The second half. mapFo acts on CONSTANTS only (mapTm f (var i) = var i), and
-- IsOrdinalφ contains no `con`, so relabelling the constant domain leaves the
-- syntax tree fixed. The statement needs the target structure, because
-- CardinalBridge's formulas are indexed by their structure's carrier.

module Relabel (𝒯 : ZFStructure (hPropAlgebra ℓ)) where

  private
    module CB𝒯 = CardinalBridge 𝒯

  ordinalφ-mapFo : (h : S → ZFStructure.S 𝒯)
                 → mapFo h IsOrdinalφ ≡ CB𝒯.IsOrdinalφ
  ordinalφ-mapFo h = refl

  transitiveφ-mapFo : (h : S → ZFStructure.S 𝒯)
                    → mapFo h IsTransitiveφ ≡ CB𝒯.IsTransitiveφ
  transitiveφ-mapFo h = refl

--------------------------------------------------------------------------------
-- PART 2. THE MISSING SURJECTION VOCABULARY
--------------------------------------------------------------------------------

-- CardinalBridge has sixteen entries and no surjection. Ruling Q6 gives the
-- missing cardinal vocabulary to this track, "written in CardinalBridge's exact
-- style with a formula, a host reading and a refl-or-proved bridge for each
-- entry, so a later K1 addendum can absorb the file unchanged". That is the
-- shape below: three renamings with their Agrees lemmas, one formula, one host
-- predicate, one bridge assembled from CardinalBridge's own three.
--
-- Env (f ∷ a ∷ b ∷ []), reading "f is a function, total on a, with values in b,
-- whose value set covers b". The first three conjuncts are IsInjectionφ's
-- first three, reused verbatim; only the fourth is new. Surjectivity is the
-- ONTO clause and not injectivity, so IsSurjectionφ is deliberately NOT
-- IsInjectionφ with a clause swapped.

surj-pair : Fin 3 → Fin 6
surj-pair zero              = zero
surj-pair (suc zero)        = suc zero
surj-pair (suc (suc zero))  = suc (suc zero)

SurjOntoφ : Formula S 3
SurjOntoφ =
  ∀̇∈ (var (suc (suc zero)))
       (∃̇ (∃̇ ((var (suc zero) ∈̇ var (suc (suc (suc (suc zero)))))
            ∧̇ ((var zero ∈̇ var (suc (suc (suc zero))))
            ∧̇ (renameFo surj-pair PairφK)))))

IsSurjectionφ : Formula S 3
IsSurjectionφ =
  (renameFo inj-fun IsFunctionφ)
  ∧̇ (InjDomφ
  ∧̇ (InjRanφ
  ∧̇ SurjOntoφ))

isSurjection : S → S → S → Ω
isSurjection f a b =
  (isFunction f)
  ⊓ ((⋀ S (λ x → (x ∈ˢ a) ⇒ (⋁ S (λ y → ⋁ S (λ p →
       (p ∈ˢ f) ⊓ (isKPair p x y))))))
  ⊓ ((⋀ S (λ p → (p ∈ˢ f) ⇒ (⋀ S (λ x → ⋀ S (λ y →
       (isKPair p x y) ⇒ (y ∈ˢ b))))))
  ⊓ (⋀ S (λ v → (v ∈ˢ b) ⇒ (⋁ S (λ x → ⋁ S (λ p →
       (x ∈ˢ a) ⊓ ((p ∈ˢ f) ⊓ (isKPair p x v)))))))))

surj-pair-agrees : (p x v f a b : S)
  → Agrees surj-pair (p ∷ x ∷ v ∷ f ∷ a ∷ b ∷ []) (p ∷ x ∷ v ∷ [])
surj-pair-agrees p x v f a b zero              = refl
surj-pair-agrees p x v f a b (suc zero)        = refl
surj-pair-agrees p x v f a b (suc (suc zero))  = refl

SurjOnto-bridge : (f a b : S)
  → ((f ∷ a ∷ b ∷ []) ⊨ SurjOntoφ)
    ≡ (⋀ S (λ v → (v ∈ˢ b) ⇒ (⋁ S (λ x → ⋁ S (λ p →
         (x ∈ˢ a) ⊓ ((p ∈ˢ f) ⊓ (isKPair p x v)))))))
SurjOnto-bridge f a b =
  cong (⋀ S) (funExt (λ v → cong ((v ∈ˢ b) ⇒_) (cong (⋁ S) (funExt (λ x →
    cong (⋁ S) (funExt (λ p → cong ((x ∈ˢ a) ⊓_) (cong ((p ∈ˢ f) ⊓_)
      (⊨-rename surj-pair PairφK (p ∷ x ∷ v ∷ f ∷ a ∷ b ∷ [])
        (p ∷ x ∷ v ∷ []) (surj-pair-agrees p x v f a b))))))))))

IsSurjection-bridge : (f a b : S)
  → ((f ∷ a ∷ b ∷ []) ⊨ IsSurjectionφ) ≡ (isSurjection f a b)
IsSurjection-bridge f a b =
  cong₂ _⊓_ (InjFun-bridge f a b)
    (cong₂ _⊓_ (InjDom-bridge f a b)
      (cong₂ _⊓_ (InjRan-bridge f a b) (SurjOnto-bridge f a b)))

-- Env (a ∷ b ∷ []), "some surjection carries a onto b", the ∃̇-closure that
-- Injectableφ (CardinalBridge.agda:379-380) is for injections. The bound
-- variable sits at position 0 with a and b at 1 and 2, so IsSurjectionφ
-- applies unrenamed, exactly as Injectableφ applies IsInjectionφ.

Surjectableφ : Formula S 2
Surjectableφ = ∃̇ IsSurjectionφ

surjectable : S → S → Ω
surjectable a b = ⋁ S (λ f → isSurjection f a b)

Surjectable-bridge : (a b : S)
  → ((a ∷ b ∷ []) ⊨ Surjectableφ) ≡ (surjectable a b)
Surjectable-bridge a b =
  cong (⋁ S) (funExt (λ f → IsSurjection-bridge f a b))

--------------------------------------------------------------------------------
-- PART 3. THE ORDER THEORY
--------------------------------------------------------------------------------

-- Extensionality and the two membership congruences of ≈ˢ. OrdinaryProfile
-- states in its own words (OrdinaryProfile.agda:169-174) that the congruences
-- are NOT available from ZFStructure or from Extensionality and must come from
-- a realization contract. At the ground that contract is `paths` and the two
-- lemmas are OrdinaryProfile.PathRealization.subst-member and subst-base
-- (:188-192). At the extension it is K5's sat-cong at an atomic formula. The
-- module takes the two facts rather than either route, which is what keeps the
-- whole of Part 3 usable at both structures.
--
-- Ground axioms are arguments of the declarations that spend them (ruling D4),
-- never parameters of this module and never one record.

module Order
  (ext       : Extensionality)
  (mem-congˡ : (x y z : S) → ⟨ x ≈ˢ y ⟩ → (x ∈ˢ z) ≡ (y ∈ˢ z))
  (mem-congʳ : (x y z : S) → ⟨ y ≈ˢ z ⟩ → (x ∈ˢ y) ≡ (x ∈ˢ z))
  where

  ------------------------------------------------------------------------
  -- 3.1 ≈ˢ is an equivalence, and it transports membership
  ------------------------------------------------------------------------

  -- Reflexivity is Extensionality at a = b (OrdinaryProfile.agda:163-164).
  -- Symmetry and transitivity are NOT: ≈ˢ is an abstract field of the
  -- structure and the ordinary sentence runs only from agreement of
  -- membership to equality. Both directions below go through mem-congʳ and
  -- back through ext, which is the only route the profile has.

  ≈-refl : (x : S) → ⟨ x ≈ˢ x ⟩
  ≈-refl = OP.≈ˢ-refl ext

  ≈-sym : (x y : S) → ⟨ x ≈ˢ y ⟩ → ⟨ y ≈ˢ x ⟩
  ≈-sym x y h = ext y x (λ z →
      (λ m → subst ⟨_⟩ (sym (mem-congʳ z x y h)) m)
    , (λ m → subst ⟨_⟩ (mem-congʳ z x y h) m))

  ≈-trans : (x y z : S) → ⟨ x ≈ˢ y ⟩ → ⟨ y ≈ˢ z ⟩ → ⟨ x ≈ˢ z ⟩
  ≈-trans x y z h g = ext x z (λ w →
      (λ m → subst ⟨_⟩ (mem-congʳ w y z g) (subst ⟨_⟩ (mem-congʳ w x y h) m))
    , (λ m → subst ⟨_⟩ (sym (mem-congʳ w x y h))
               (subst ⟨_⟩ (sym (mem-congʳ w y z g)) m)))

  mem-inˡ : (x y z : S) → ⟨ x ≈ˢ y ⟩ → ⟨ x ∈ˢ z ⟩ → ⟨ y ∈ˢ z ⟩
  mem-inˡ x y z h = subst ⟨_⟩ (mem-congˡ x y z h)

  mem-inʳ : (x y z : S) → ⟨ y ≈ˢ z ⟩ → ⟨ x ∈ˢ y ⟩ → ⟨ x ∈ˢ z ⟩
  mem-inʳ x y z h = subst ⟨_⟩ (mem-congʳ x y z h)

  ------------------------------------------------------------------------
  -- 3.2 Domain monotonicity, codomain monotonicity, congruence
  ------------------------------------------------------------------------

  -- The three free lemmas. None of them builds a set: the SAME graph f that
  -- injects b into w injects every subset of b into w, because the only
  -- clause of isInjection that mentions the domain is the domain clause
  -- (CardinalBridge.agda:286-287) and it is a single implication, not a
  -- biconditional. That weakness is exactly what CardinalBridge.agda:224-232
  -- flags as deliberate, and here it is what makes the lemma free.

  injectable-mono-dom : (a b w : S) → ⟨ isSubset a b ⟩
                      → ⟨ injectable b w ⟩ → ⟨ injectable a w ⟩
  injectable-mono-dom a b w sub =
    PT.map (λ { (f , fn , dom , rest) →
                f , (fn , ((λ x x∈a → dom x (sub x x∈a)) , rest)) })

  -- Codomain monotonicity is the dual and is free for the dual reason: the
  -- range clause is also a single implication.

  injectable-mono-cod : (a w v : S) → ⟨ isSubset w v ⟩
                      → ⟨ injectable a w ⟩ → ⟨ injectable a v ⟩
  injectable-mono-cod a w v sub =
    PT.map (λ { (f , fn , dom , ran , rest) →
                f , (fn , (dom , ((λ p p∈f x y k → sub y (ran p p∈f x y k))
                                 , rest))) })

  injectable-cong : (a b w : S) → ⟨ a ≈ˢ b ⟩
                  → ⟨ injectable a w ⟩ → ⟨ injectable b w ⟩
  injectable-cong a b w e =
    PT.map (λ { (f , fn , dom , rest) →
                f , (fn , ((λ x x∈b → dom x (mem-inʳ x b a (≈-sym a b e) x∈b))
                          , rest)) })

  injectable-cong-cod : (a w v : S) → ⟨ w ≈ˢ v ⟩
                      → ⟨ injectable a w ⟩ → ⟨ injectable a v ⟩
  injectable-cong-cod a w v e =
    PT.map (λ { (f , fn , dom , ran , rest) →
                f , (fn , (dom , ((λ p p∈f x y k → mem-inʳ y w v e (ran p p∈f x y k))
                                 , rest))) })

  ------------------------------------------------------------------------
  -- 3.3 No set is a member of itself
  ------------------------------------------------------------------------

  -- Induction form Foundation at the formula ¬̇ (var zero ∈̇ var zero). The
  -- inductive step is one application: if every member of u avoids itself and
  -- u ∈ u, then u is such a member. Nothing classical is used.

  no-self : FoundationInduction → (x : S) → ⟨ x ∈ˢ x ⟩ → Empty.⊥
  no-self find x h = Empty.rec* (find selfFo selfStep x h)
    where
      selfFo : Formula S 1
      selfFo = ¬̇ (var zero ∈̇ var zero)

      selfStep : (u : S) → ((y : S) → ⟨ y ∈ˢ u ⟩ → ⟨ (y ∷ []) ⊨ selfFo ⟩)
               → ⟨ (u ∷ []) ⊨ selfFo ⟩
      selfStep u ih u∈u = ih u u∈u u∈u

  ------------------------------------------------------------------------
  -- 3.4 The cut lemma
  ------------------------------------------------------------------------

  -- A transitive subset of an ordinal is either the whole ordinal or one of
  -- its members. This is the one place the argument is genuinely classical
  -- and genuinely uses Foundation: the ∈-least member of a \ g is forced to
  -- be g itself, and the two inclusions that prove it run in opposite
  -- directions, one off linearity of a and one off minimality.
  --
  -- The hypotheses on g are stated as host implications rather than as
  -- isSubset g a and isTransitiveSet g, because every call site produces
  -- them that way out of a Separation specification and the unfolding would
  -- be noise.

  cut : Separation → FoundationInduction → LEM ℓ
      → (a g : S) → ⟨ isOrdinal a ⟩
      → ((y : S) → ⟨ y ∈ˢ g ⟩ → ⟨ y ∈ˢ a ⟩)
      → ((y : S) → ⟨ y ∈ˢ g ⟩ → (z : S) → ⟨ z ∈ˢ y ⟩ → ⟨ z ∈ˢ g ⟩)
      → ⟨ (g ≈ˢ a) ⊔ (g ∈ˢ a) ⟩
  cut sep find lem a g aord sub gtr = decide (lem gap)
    where
      atr : (x : S) → ⟨ x ∈ˢ a ⟩ → (y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ y ∈ˢ a ⟩
      atr = aord .fst

      alin : (x : S) → ⟨ x ∈ˢ a ⟩ → (y : S) → ⟨ y ∈ˢ a ⟩
           → ⟨ (x ∈ˢ y) ⊔ ((x ≈ˢ y) ⊔ (y ∈ˢ x)) ⟩
      alin = aord .snd

      gapFo : Formula S 1
      gapFo = ¬̇ (var zero ∈̇ con g)

      gap : Ω
      gap = ⋁ S (λ x → (x ∈ˢ a) ⊓ ((x ∈ˢ g) ⇒ ⊥))

      target : Ω
      target = (g ≈ˢ a) ⊔ (g ∈ˢ a)

      -- The empty-gap branch. Every member of a is a member of g by double
      -- negation, so the two sets agree and Extensionality closes it.

      filled : (⟨ gap ⟩ → Empty.⊥) → (z : S) → ⟨ z ∈ˢ a ⟩ → ⟨ z ∈ˢ g ⟩
      filled none z z∈a = pick (lem (z ∈ˢ g))
        where
          pick : ⟨ z ∈ˢ g ⟩ ⊎ (⟨ z ∈ˢ g ⟩ → Empty.⊥) → ⟨ z ∈ˢ g ⟩
          pick (inl yes) = yes
          pick (inr no)  =
            Empty.rec (none ∣ z , (z∈a , λ m → Empty.rec (no m)) ∣₁)

      -- The inhabited-gap branch, at a minimal member x of a \ g.

      atMin : (d : S)
            → ((z : S) → ⟨ iff (z ∈ˢ d) ((z ∈ˢ a) ⊓ ((z ∈ˢ g) ⇒ ⊥)) ⟩)
            → (x : S) → ⟨ x ∈ˢ d ⟩
            → ((w : S) → ⟨ (w ∈ˢ x) ⊓ (w ∈ˢ d) ⟩ → ⟨ ⊥ ⟩)
            → ⟨ target ⟩
      atMin d dsp x x∈d minimal = ∣ inr (mem-inˡ x g a x≈g x∈a) ∣₁
        where
          x∈a : ⟨ x ∈ˢ a ⟩
          x∈a = dsp x .fst x∈d .fst

          x∉g : ⟨ x ∈ˢ g ⟩ → ⟨ ⊥ ⟩
          x∉g = dsp x .fst x∈d .snd

          -- Downward: every member of x is a member of g, because a member of
          -- x that missed g would be a member of a \ g below the minimum.

          down : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ g ⟩
          down z z∈x = pick (lem (z ∈ˢ g))
            where
              pick : ⟨ z ∈ˢ g ⟩ ⊎ (⟨ z ∈ˢ g ⟩ → Empty.⊥) → ⟨ z ∈ˢ g ⟩
              pick (inl yes) = yes
              pick (inr no)  = Empty.rec*
                (minimal z (z∈x , dsp z .snd
                  (atr x x∈a z z∈x , λ m → Empty.rec (no m))))

          -- Upward: every member of g is a member of x. Linearity of a leaves
          -- three cases and two of them put x inside g.

          up : (z : S) → ⟨ z ∈ˢ g ⟩ → ⟨ z ∈ˢ x ⟩
          up z z∈g = PT.rec (snd (z ∈ˢ x)) three (alin x x∈a z (sub z z∈g))
            where
              three : ⟨ x ∈ˢ z ⟩ ⊎ ⟨ (x ≈ˢ z) ⊔ (z ∈ˢ x) ⟩ → ⟨ z ∈ˢ x ⟩
              three (inl x∈z) = Empty.rec* (x∉g (gtr z z∈g x x∈z))
              three (inr rest) = PT.rec (snd (z ∈ˢ x)) two rest
                where
                  two : ⟨ x ≈ˢ z ⟩ ⊎ ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ x ⟩
                  two (inl e)    =
                    Empty.rec* (x∉g (mem-inˡ z x g (≈-sym x z e) z∈g))
                  two (inr z∈x)  = z∈x

          x≈g : ⟨ x ≈ˢ g ⟩
          x≈g = ext x g (λ z → down z , up z)

      decide : ⟨ gap ⟩ ⊎ (⟨ gap ⟩ → Empty.⊥) → ⟨ target ⟩
      decide (inr none) =
        ∣ inl (ext g a (λ z → sub z , filled none z)) ∣₁
      decide (inl some) =
        PT.rec (snd target)
          (λ { (d , dsp) →
               PT.rec (snd target)
                 (λ { (x , x∈d , minimal) → atMin d dsp x x∈d minimal })
                 (foundation→minimal find lem d
                   (PT.map (λ { (z , z∈a , z∉g) →
                                z , dsp z .snd (z∈a , z∉g) })
                           some)) })
          (sep a gapFo)

  ------------------------------------------------------------------------
  -- 3.5 ord-compare: comparability of ordinals
  ------------------------------------------------------------------------

  -- Route M of architecture 2.7, and the reason this track owns it.
  -- isCardinal's outer quantifier is BOUNDED: CardinalBridge.agda:551 is
  -- ∀̇∈ (var zero) and :556 reads ⋀ S (λ β → (β ∈ˢ κ) ⇒ …), so cardinality
  -- transfers without any comparability of ordinals. isSuccCardinal's
  -- minimality conjunct is NOT: CardinalBridge.agda:587 is a plain ∀̇ and
  -- :596 reads ⋀ S (λ μ → …) over the whole carrier, and its conclusion
  -- (δ ≈ˢ μ) ⊔ (δ ∈ˢ μ) is exactly two thirds of a trichotomy. That is what
  -- ord-compare supplies, and it supplies it at whichever structure it is
  -- instantiated at.
  --
  -- The proof is the classical one, with α ∩ δ cut by a single Separation
  -- and the two halves handed to cut. The fourth case is where Foundation
  -- earns its place: γ ∈ α and γ ∈ δ put γ inside γ.
  --
  -- MEASURED AGAINST THE BRIEF: Pairing is NOT a hypothesis. The brief's
  -- signature lists FoundationInduction → Separation → Pairing → LEM ℓ; no
  -- step below builds a set other than by Separation, and rule 13 says an
  -- unused parameter comes out.

  ord-compare : FoundationInduction → Separation → LEM ℓ
              → (α δ : S) → ⟨ isOrdinal α ⟩ → ⟨ isOrdinal δ ⟩
              → ⟨ (α ∈ˢ δ) ⊔ ((α ≈ˢ δ) ⊔ (δ ∈ˢ α)) ⟩
  ord-compare find sep lem α δ αord δord =
    PT.rec (snd target) (λ { (γ , γsp) → combine γ γsp }) (sep α interFo)
    where
      target : Ω
      target = (α ∈ˢ δ) ⊔ ((α ≈ˢ δ) ⊔ (δ ∈ˢ α))

      interFo : Formula S 1
      interFo = var zero ∈̇ con δ

      Spec : S → Type ℓ
      Spec γ = (x : S) → ⟨ iff (x ∈ˢ γ) ((x ∈ˢ α) ⊓ (x ∈ˢ δ)) ⟩

      -- The intersection is transitive because both ordinals are.

      inter-tr : (γ : S) → Spec γ
               → (y : S) → ⟨ y ∈ˢ γ ⟩ → (z : S) → ⟨ z ∈ˢ y ⟩ → ⟨ z ∈ˢ γ ⟩
      inter-tr γ γsp y y∈γ z z∈y =
        γsp z .snd ( αord .fst y (γsp y .fst y∈γ .fst) z z∈y
                   , δord .fst y (γsp y .fst y∈γ .snd) z z∈y )

      four : (γ : S) → Spec γ
           → ⟨ γ ≈ˢ α ⟩ ⊎ ⟨ γ ∈ˢ α ⟩ → ⟨ γ ≈ˢ δ ⟩ ⊎ ⟨ γ ∈ˢ δ ⟩ → ⟨ target ⟩
      four γ γsp (inl γ≈α) (inl γ≈δ) =
        ∣ inr ∣ inl (≈-trans α γ δ (≈-sym γ α γ≈α) γ≈δ) ∣₁ ∣₁
      four γ γsp (inl γ≈α) (inr γ∈δ) = ∣ inl (mem-inˡ γ α δ γ≈α γ∈δ) ∣₁
      four γ γsp (inr γ∈α) (inl γ≈δ) = ∣ inr ∣ inr (mem-inˡ γ δ α γ≈δ γ∈α) ∣₁ ∣₁
      four γ γsp (inr γ∈α) (inr γ∈δ) =
        Empty.rec (no-self find γ (γsp γ .snd (γ∈α , γ∈δ)))

      combine : (γ : S) → Spec γ → ⟨ target ⟩
      combine γ γsp =
        PT.rec (snd target)
          (λ hα → PT.rec (snd target) (λ hδ → four γ γsp hα hδ)
            (cut sep find lem δ γ δord (λ y m → γsp y .fst m .snd)
                 (inter-tr γ γsp)))
          (cut sep find lem α γ αord (λ y m → γsp y .fst m .fst)
               (inter-tr γ γsp))

  ------------------------------------------------------------------------
  -- 3.6 Singletons, pairs, and the clause decomposition of isInjection
  ------------------------------------------------------------------------

  -- The five projections out of CardinalBridge's singleton and pair readings
  -- (CardinalBridge.agda:86-88, :102-105). They are named because the two
  -- construction lemmas below use them thirty times between them and an
  -- anonymous .snd .snd .snd chain is where a component swap hides.

  sgl-has : (t x : S) → ⟨ isSingleton t x ⟩ → ⟨ x ∈ˢ t ⟩
  sgl-has t x h = h .fst

  sgl-mem : (t x u : S) → ⟨ isSingleton t x ⟩ → ⟨ u ∈ˢ t ⟩ → ⟨ u ≈ˢ x ⟩
  sgl-mem t x u h = h .snd u

  pr-hasˡ : (t x y : S) → ⟨ isPair t x y ⟩ → ⟨ x ∈ˢ t ⟩
  pr-hasˡ t x y h = h .fst

  pr-hasʳ : (t x y : S) → ⟨ isPair t x y ⟩ → ⟨ y ∈ˢ t ⟩
  pr-hasʳ t x y h = h .snd .fst

  pr-mem : (t x y u : S) → ⟨ isPair t x y ⟩ → ⟨ u ∈ˢ t ⟩
         → ⟨ (u ≈ˢ x) ⊔ (u ≈ˢ y) ⟩
  pr-mem t x y u h = h .snd .snd u

  -- The four clauses of isInjection, named, with the decomposition stated as
  -- a reading theorem rather than assumed. The first two are the two halves
  -- of isFunction. The last is injectivity and it is NOT SingleClause with
  -- arguments permuted: single-valuedness pairs p and q at a common FIRST
  -- component and concludes about the second, injectivity pairs them at a
  -- common SECOND component and concludes about the first
  -- (CardinalBridge.agda:188-190 against :290-292).

  SingleClause : S → Ω
  SingleClause f =
    ⋀ S (λ p → (p ∈ˢ f) ⇒ (⋀ S (λ q → (q ∈ˢ f) ⇒
      (⋀ S (λ x → ⋀ S (λ y → ⋀ S (λ z →
        ((isKPair p x y) ⊓ (isKPair q x z)) ⇒ (y ≈ˢ z))))))))

  DomClause : S → S → Ω
  DomClause f a =
    ⋀ S (λ x → (x ∈ˢ a) ⇒ (⋁ S (λ y → ⋁ S (λ p →
      (p ∈ˢ f) ⊓ (isKPair p x y)))))

  RanClause : S → S → Ω
  RanClause f b =
    ⋀ S (λ p → (p ∈ˢ f) ⇒ (⋀ S (λ x → ⋀ S (λ y →
      (isKPair p x y) ⇒ (y ∈ˢ b)))))

  InjClause : S → Ω
  InjClause f =
    ⋀ S (λ p → (p ∈ˢ f) ⇒ (⋀ S (λ q → (q ∈ˢ f) ⇒
      (⋀ S (λ x → ⋀ S (λ y → ⋀ S (λ z →
        ((isKPair p x y) ⊓ (isKPair q z y)) ⇒ (x ≈ˢ z))))))))

  function-clauses : (f : S) → isFunction f ≡ ((isRelation f) ⊓ (SingleClause f))
  function-clauses f = refl

  injection-clauses : (f a b : S)
    → isInjection f a b
      ≡ ((isFunction f) ⊓ ((DomClause f a) ⊓ ((RanClause f b) ⊓ (InjClause f))))
  injection-clauses f a b = refl

  ------------------------------------------------------------------------
  -- 3.7 Pairing builds singletons, pairs and Kuratowski pairs
  ------------------------------------------------------------------------

  sglOf : Pairing → (x : S) → ⟨ ⋁ S (λ t → isSingleton t x) ⟩
  sglOf pair x =
    PT.map (λ { (t , tsp) →
                t , ( tsp x .snd ∣ inl (≈-refl x) ∣₁
                    , λ u u∈t → PT.rec (snd (u ≈ˢ x))
                        (λ { (inl e) → e ; (inr e) → e }) (tsp u .fst u∈t) ) })
      (pair x x)

  prOf : Pairing → (x y : S) → ⟨ ⋁ S (λ t → isPair t x y) ⟩
  prOf pair x y =
    PT.map (λ { (t , tsp) →
                t , ( tsp x .snd ∣ inl (≈-refl x) ∣₁
                    , ( tsp y .snd ∣ inr (≈-refl y) ∣₁
                      , λ u u∈t → tsp u .fst u∈t ) ) })
      (pair x y)

  -- Congruence and substitution. The first pair moves the CARRIER of the
  -- singleton or pair along ≈ˢ, the second moves its COMPONENTS. Both are
  -- needed: a Kuratowski pair is determined by its components and its
  -- components are determined by it, and the two facts run through opposite
  -- lemmas.

  sgl-cong : (w t x : S) → ⟨ w ≈ˢ t ⟩ → ⟨ isSingleton t x ⟩ → ⟨ isSingleton w x ⟩
  sgl-cong w t x e h =
    ( mem-inʳ x t w (≈-sym w t e) (sgl-has t x h)
    , λ u u∈w → sgl-mem t x u h (mem-inʳ u w t e u∈w) )

  pr-cong : (w t x y : S) → ⟨ w ≈ˢ t ⟩ → ⟨ isPair t x y ⟩ → ⟨ isPair w x y ⟩
  pr-cong w t x y e h =
    ( mem-inʳ x t w (≈-sym w t e) (pr-hasˡ t x y h)
    , ( mem-inʳ y t w (≈-sym w t e) (pr-hasʳ t x y h)
      , λ u u∈w → pr-mem t x y u h (mem-inʳ u w t e u∈w) ) )

  sgl-subst : (t x x' : S) → ⟨ x ≈ˢ x' ⟩
            → ⟨ isSingleton t x ⟩ → ⟨ isSingleton t x' ⟩
  sgl-subst t x x' e h =
    ( mem-inˡ x x' t e (sgl-has t x h)
    , λ u u∈t → ≈-trans u x x' (sgl-mem t x u h u∈t) e )

  pr-subst : (t x x' y y' : S) → ⟨ x ≈ˢ x' ⟩ → ⟨ y ≈ˢ y' ⟩
           → ⟨ isPair t x y ⟩ → ⟨ isPair t x' y' ⟩
  pr-subst t x x' y y' ex ey h =
    ( mem-inˡ x x' t ex (pr-hasˡ t x y h)
    , ( mem-inˡ y y' t ey (pr-hasʳ t x y h)
      , λ u u∈t → PT.map (λ { (inl q) → inl (≈-trans u x x' q ex)
                            ; (inr q) → inr (≈-trans u y y' q ey) })
                    (pr-mem t x y u h u∈t) ) )

  kpair-subst : (p x x' y y' : S) → ⟨ x ≈ˢ x' ⟩ → ⟨ y ≈ˢ y' ⟩
              → ⟨ isKPair p x y ⟩ → ⟨ isKPair p x' y' ⟩
  kpair-subst p x x' y y' ex ey h t =
      (λ m → PT.map (λ { (inl s) → inl (sgl-subst t x x' ex s)
                       ; (inr q) → inr (pr-subst t x x' y y' ex ey q) })
               (h t .fst m))
    , (λ m → h t .snd
        (PT.map (λ { (inl s) → inl (sgl-subst t x' x (≈-sym x x' ex) s)
                   ; (inr q) → inr (pr-subst t x' x y' y
                                      (≈-sym x x' ex) (≈-sym y y' ey) q) })
          m))

  sgl-unique : (t t' x : S) → ⟨ isSingleton t x ⟩ → ⟨ isSingleton t' x ⟩
             → ⟨ t ≈ˢ t' ⟩
  sgl-unique t t' x h h' = ext t t' (λ z → into t t' h h' z , into t' t h' h z)
    where
      into : (u u' : S) → ⟨ isSingleton u x ⟩ → ⟨ isSingleton u' x ⟩
           → (z : S) → ⟨ z ∈ˢ u ⟩ → ⟨ z ∈ˢ u' ⟩
      into u u' hu hu' z z∈u =
        mem-inˡ x z u' (≈-sym z x (sgl-mem u x z hu z∈u)) (sgl-has u' x hu')

  pr-unique : (t t' x y : S) → ⟨ isPair t x y ⟩ → ⟨ isPair t' x y ⟩
            → ⟨ t ≈ˢ t' ⟩
  pr-unique t t' x y h h' = ext t t' (λ z → into t t' h h' z , into t' t h' h z)
    where
      into : (u u' : S) → ⟨ isPair u x y ⟩ → ⟨ isPair u' x y ⟩
           → (z : S) → ⟨ z ∈ˢ u ⟩ → ⟨ z ∈ˢ u' ⟩
      into u u' hu hu' z z∈u = PT.rec (snd (z ∈ˢ u'))
        (λ { (inl e) → mem-inˡ x z u' (≈-sym z x e) (pr-hasˡ u' x y hu')
           ; (inr e) → mem-inˡ y z u' (≈-sym z y e) (pr-hasʳ u' x y hu') })
        (pr-mem u x y z hu z∈u)

  -- Existence of the Kuratowski pair, by Pairing twice over. The forward
  -- half of the biconditional moves the two shapes along ≈ˢ, the backward
  -- half identifies them, and those are exactly sgl-cong / pr-cong against
  -- sgl-unique / pr-unique.

  kpairOf : Pairing → (x y : S) → ⟨ ⋁ S (λ p → isKPair p x y) ⟩
  kpairOf pair x y =
    PT.rec (snd tgt)
      (λ { (s , ssp) → PT.rec (snd tgt)
        (λ { (t , tsp) → PT.map
          (λ { (q , qsp) → q , build s ssp t tsp q qsp }) (pair s t) })
        (prOf pair x y) })
      (sglOf pair x)
    where
      tgt : Ω
      tgt = ⋁ S (λ p → isKPair p x y)

      build : (s : S) → ⟨ isSingleton s x ⟩ → (t : S) → ⟨ isPair t x y ⟩
            → (q : S) → ⟨ ⋀ S (λ w → iff (w ∈ˢ q) ((w ≈ˢ s) ⊔ (w ≈ˢ t))) ⟩
            → ⟨ isKPair q x y ⟩
      build s ssp t tsp q qsp w =
          (λ m → PT.map (λ { (inl e) → inl (sgl-cong w s x e ssp)
                           ; (inr e) → inr (pr-cong w t x y e tsp) })
                   (qsp w .fst m))
        , (λ m → qsp w .snd
            (PT.map (λ { (inl sg) → inl (sgl-unique w s x sg ssp)
                       ; (inr pr) → inr (pr-unique w t x y pr tsp) }) m))

  ------------------------------------------------------------------------
  -- 3.8 Component recovery: a Kuratowski pair determines its components
  ------------------------------------------------------------------------

  -- NameSupport.agda:233 proves the OTHER direction, that the components
  -- determine the pair, over the coded predicate isKPairΔ. The direction
  -- needed here is measured absent from the compile root, and it is the
  -- lemma every clause of the two constructions below runs through.
  --
  -- Pairing is unavoidable and this is why. isKPair p x y is a
  -- BICONDITIONAL, "the members of p are exactly the two shapes". With no
  -- set of either shape in existence, both directions are vacuous and p may
  -- be empty, so nothing at all follows about x and y. The singleton of x
  -- is the witness that forces p to be inhabited.

  kpair-fst : Pairing → (p x y x' y' : S)
            → ⟨ isKPair p x y ⟩ → ⟨ isKPair p x' y' ⟩ → ⟨ x ≈ˢ x' ⟩
  kpair-fst pair p x y x' y' h h' =
    PT.rec (snd (x ≈ˢ x')) (λ { (s , ssp) → step s ssp }) (sglOf pair x)
    where
      step : (s : S) → ⟨ isSingleton s x ⟩ → ⟨ x ≈ˢ x' ⟩
      step s ssp = ≈-sym x' x (sgl-mem s x x' ssp x'∈s)
        where
          s∈p : ⟨ s ∈ˢ p ⟩
          s∈p = h s .snd ∣ inl ssp ∣₁

          x'∈s : ⟨ x' ∈ˢ s ⟩
          x'∈s = PT.rec (snd (x' ∈ˢ s))
            (λ { (inl sg) → sgl-has s x' sg
               ; (inr pr) → pr-hasˡ s x' y' pr })
            (h' s .fst s∈p)

  kpair-snd : Pairing → (p x y x' y' : S)
            → ⟨ isKPair p x y ⟩ → ⟨ isKPair p x' y' ⟩ → ⟨ y ≈ˢ y' ⟩
  kpair-snd pair p x y x' y' h h' =
    PT.rec (snd goal) (λ { (t , tsp) → atPair t tsp }) (prOf pair x y)
    where
      goal : Ω
      goal = y ≈ˢ y'

      ex : ⟨ x ≈ˢ x' ⟩
      ex = kpair-fst pair p x y x' y' h h'

      -- The degenerate branch: {x, y} turned out to be a singleton, so y is
      -- x, and y' has to be fetched from the OTHER pair {x', y'}.

      viaOther : ⟨ y ≈ˢ x ⟩ → ⟨ y ≈ˢ y' ⟩
      viaOther yx =
        PT.rec (snd goal) (λ { (t' , t'sp) → atOther t' t'sp })
          (prOf pair x' y')
        where
          atOther : (t' : S) → ⟨ isPair t' x' y' ⟩ → ⟨ y ≈ˢ y' ⟩
          atOther t' t'sp = PT.rec (snd goal) two (h t' .fst t'∈p)
            where
              t'∈p : ⟨ t' ∈ˢ p ⟩
              t'∈p = h' t' .snd ∣ inr t'sp ∣₁

              y'∈t' : ⟨ y' ∈ˢ t' ⟩
              y'∈t' = pr-hasʳ t' x' y' t'sp

              fromX : ⟨ y' ≈ˢ x ⟩ → ⟨ y ≈ˢ y' ⟩
              fromX e = ≈-trans y x y' yx (≈-sym y' x e)

              two : ⟨ isSingleton t' x ⟩ ⊎ ⟨ isPair t' x y ⟩ → ⟨ y ≈ˢ y' ⟩
              two (inl sg) = fromX (sgl-mem t' x y' sg y'∈t')
              two (inr pr) = PT.rec (snd goal)
                (λ { (inl e) → fromX e ; (inr e) → ≈-sym y' y e })
                (pr-mem t' x y y' pr y'∈t')

      atPair : (t : S) → ⟨ isPair t x y ⟩ → ⟨ y ≈ˢ y' ⟩
      atPair t tsp = PT.rec (snd goal) two (h' t .fst t∈p)
        where
          t∈p : ⟨ t ∈ˢ p ⟩
          t∈p = h t .snd ∣ inr tsp ∣₁

          y∈t : ⟨ y ∈ˢ t ⟩
          y∈t = pr-hasʳ t x y tsp

          two : ⟨ isSingleton t x' ⟩ ⊎ ⟨ isPair t x' y' ⟩ → ⟨ y ≈ˢ y' ⟩
          two (inl sg) =
            viaOther (≈-trans y x' x (sgl-mem t x' y sg y∈t) (≈-sym x x' ex))
          two (inr pr) = PT.rec (snd goal) inner (pr-mem t x' y' y pr y∈t)
            where
              y'∈t : ⟨ y' ∈ˢ t ⟩
              y'∈t = pr-hasʳ t x' y' pr

              inner : ⟨ y ≈ˢ x' ⟩ ⊎ ⟨ y ≈ˢ y' ⟩ → ⟨ y ≈ˢ y' ⟩
              inner (inr e) = e
              inner (inl e) = PT.rec (snd goal) final (pr-mem t x y y' tsp y'∈t)
                where
                  yx : ⟨ y ≈ˢ x ⟩
                  yx = ≈-trans y x' x e (≈-sym x x' ex)

                  final : ⟨ y' ≈ˢ x ⟩ ⊎ ⟨ y' ≈ˢ y ⟩ → ⟨ y ≈ˢ y' ⟩
                  final (inl q) = ≈-trans y x y' yx (≈-sym y' x q)
                  final (inr q) = ≈-sym y' y q

  kpair-components : Pairing → (p x y x' y' : S)
                   → ⟨ isKPair p x y ⟩ → ⟨ isKPair p x' y' ⟩
                   → ⟨ (x ≈ˢ x') ⊓ (y ≈ˢ y') ⟩
  kpair-components pair p x y x' y' h h' =
    kpair-fst pair p x y x' y' h h' , kpair-snd pair p x y x' y' h h'

  ------------------------------------------------------------------------
  -- 3.9 The graph builder
  ------------------------------------------------------------------------

  -- Collection cuts a bound out of a, Separation cuts the graph out of the
  -- bound. This is GroundDescription.hasImage′ (:181-185) WITHOUT its
  -- functionality hypothesis: hasImage′ asks for host contractibility of the
  -- value, isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ φ ⟩), and a Kuratowski pair
  -- is unique only up to ≈ˢ, which is not a host path at the extension. The
  -- price of dropping it is that the result is not a biconditional: the
  -- graph is cut out of a bound and the reverse inclusion is not claimed.
  -- Both construction lemmas below need only the two directions stated.

  GraphSpec : (a : S) (ψ : Formula S 2) (h : S) → Ω
  GraphSpec a ψ h =
      (⋀ S (λ w → (w ∈ˢ h) ⇒ (⋁ S (λ x → (x ∈ˢ a) ⊓ ((w ∷ x ∷ []) ⊨ ψ)))))
    ⊓ (⋀ S (λ x → (x ∈ˢ a) ⇒ (⋁ S (λ w → (w ∈ˢ h) ⊓ ((w ∷ x ∷ []) ⊨ ψ)))))

  graphOf : Separation → Collection → (a : S) (ψ : Formula S 2)
          → ⟨ ⋀ S (λ x → (x ∈ˢ a) ⇒ (⋁ S (λ w → (w ∷ x ∷ []) ⊨ ψ))) ⟩
          → ⟨ ⋁ S (λ h → GraphSpec a ψ h) ⟩
  graphOf sep coll a ψ prem =
    PT.rec (snd tgt)
      (λ { (B , bound) → PT.rec (snd tgt)
        (λ { (h , hsp) → ∣ h , (fwd B h hsp , bwd B bound h hsp) ∣₁ })
        (sep B θ) })
      (coll a ψ prem)
    where
      tgt : Ω
      tgt = ⋁ S (λ h → GraphSpec a ψ h)

      θ : Formula S 1
      θ = ∃̇∈ (con a) (OP.Swap.swapFo ψ)

      θ-reading : (w : S)
        → ((w ∷ []) ⊨ θ) ≡ (⋁ S (λ x → (x ∈ˢ a) ⊓ ((w ∷ x ∷ []) ⊨ ψ)))
      θ-reading w =
        cong (⋁ S) (funExt (λ x → cong ((x ∈ˢ a) ⊓_) (OP.Swap.⊨-swap ψ x w)))

      fwd : (B h : S)
          → ((z : S) → ⟨ iff (z ∈ˢ h) ((z ∈ˢ B) ⊓ ((z ∷ []) ⊨ θ)) ⟩)
          → ⟨ ⋀ S (λ w → (w ∈ˢ h) ⇒
                (⋁ S (λ x → (x ∈ˢ a) ⊓ ((w ∷ x ∷ []) ⊨ ψ)))) ⟩
      fwd B h hsp w w∈h = subst ⟨_⟩ (θ-reading w) (hsp w .fst w∈h .snd)

      bwd : (B : S)
          → ⟨ ⋀ S (λ x → (x ∈ˢ a) ⇒
                (⋁ S (λ y → (y ∈ˢ B) ⊓ ((y ∷ x ∷ []) ⊨ ψ)))) ⟩
          → (h : S)
          → ((z : S) → ⟨ iff (z ∈ˢ h) ((z ∈ˢ B) ⊓ ((z ∷ []) ⊨ θ)) ⟩)
          → ⟨ ⋀ S (λ x → (x ∈ˢ a) ⇒
                (⋁ S (λ w → (w ∈ˢ h) ⊓ ((w ∷ x ∷ []) ⊨ ψ)))) ⟩
      bwd B bound h hsp x x∈a =
        PT.map (λ { (w , w∈B , sat) →
                    w , ( hsp w .snd ( w∈B
                                     , subst ⟨_⟩ (sym (θ-reading w))
                                         ∣ x , (x∈a , sat) ∣₁ )
                        , sat ) })
          (bound x x∈a)

  ------------------------------------------------------------------------
  -- 3.10 injectable-incl: an inclusion is an injection
  ------------------------------------------------------------------------

  -- Architecture 3.8 calls this half "free" beside composition. It is not:
  -- an injection is a SET of ordered pairs, and the diagonal has to be
  -- built. What IS free is the verification, because the weak domain clause
  -- of isInjection (one implication, CardinalBridge.agda:224-232) means the
  -- diagonal of a is an injection of a into any superset without any
  -- trimming. The price is one Collection, one Separation and one Pairing.

  diag-emb : Fin 3 → Fin 2
  diag-emb zero              = zero
  diag-emb (suc zero)        = suc zero
  diag-emb (suc (suc zero))  = suc zero

  diagφ : Formula S 2
  diagφ = renameFo diag-emb PairφK

  diag-agrees : (w x : S) → Agrees diag-emb (w ∷ x ∷ []) (w ∷ x ∷ x ∷ [])
  diag-agrees w x zero              = refl
  diag-agrees w x (suc zero)        = refl
  diag-agrees w x (suc (suc zero))  = refl

  diag-reading : (w x : S) → ((w ∷ x ∷ []) ⊨ diagφ) ≡ (isKPair w x x)
  diag-reading w x =
    ⊨-rename diag-emb PairφK (w ∷ x ∷ []) (w ∷ x ∷ x ∷ []) (diag-agrees w x)
    ∙ PairφK-bridge w x x

  injectable-incl : Separation → Collection → Pairing
                  → (a b : S) → ⟨ isSubset a b ⟩ → ⟨ injectable a b ⟩
  injectable-incl sep coll pair a b sub =
    PT.rec (snd (injectable a b))
      (λ { (h , fw , bw) → ∣ h , build h fw bw ∣₁ })
      (graphOf sep coll a diagφ prem)
    where
      prem : ⟨ ⋀ S (λ x → (x ∈ˢ a) ⇒ (⋁ S (λ w → (w ∷ x ∷ []) ⊨ diagφ))) ⟩
      prem x _ =
        PT.map (λ { (w , k) → w , subst ⟨_⟩ (sym (diag-reading w x)) k })
          (kpairOf pair x x)

      build : (h : S)
            → ⟨ ⋀ S (λ w → (w ∈ˢ h) ⇒
                  (⋁ S (λ x → (x ∈ˢ a) ⊓ ((w ∷ x ∷ []) ⊨ diagφ)))) ⟩
            → ⟨ ⋀ S (λ x → (x ∈ˢ a) ⇒
                  (⋁ S (λ w → (w ∈ˢ h) ⊓ ((w ∷ x ∷ []) ⊨ diagφ)))) ⟩
            → ⟨ isInjection h a b ⟩
      build h fw bw = ((rel , single) , (dom , (ran , inj)))
        where
          useMem : (w : S) (P : Ω) → ⟨ w ∈ˢ h ⟩
                 → ((u : S) → ⟨ u ∈ˢ a ⟩ → ⟨ isKPair w u u ⟩ → ⟨ P ⟩)
                 → ⟨ P ⟩
          useMem w P w∈h k = PT.rec (snd P)
            (λ { (u , u∈a , sat) → k u u∈a (subst ⟨_⟩ (diag-reading w u) sat) })
            (fw w w∈h)

          rel : ⟨ isRelation h ⟩
          rel w w∈h = useMem w (⋁ S (λ u → ⋁ S (λ v → isKPair w u v))) w∈h
            (λ u u∈a k → ∣ u , ∣ u , k ∣₁ ∣₁)

          single : ⟨ SingleClause h ⟩
          single p p∈h q q∈h x y z (kp , kq) =
            useMem p (y ≈ˢ z) p∈h (λ u u∈a ku →
              useMem q (y ≈ˢ z) q∈h (λ v v∈a kv →
                let c₁ = kpair-components pair p u u x y ku kp
                    c₂ = kpair-components pair q v v x z kv kq
                in ≈-trans y u z (≈-sym u y (c₁ .snd))
                     (≈-trans u x z (c₁ .fst)
                       (≈-trans x v z (≈-sym v x (c₂ .fst)) (c₂ .snd)))))

          dom : ⟨ DomClause h a ⟩
          dom x x∈a = PT.map
            (λ { (w , w∈h , sat) →
                 x , ∣ w , (w∈h , subst ⟨_⟩ (diag-reading w x) sat) ∣₁ })
            (bw x x∈a)

          ran : ⟨ RanClause h b ⟩
          ran w w∈h x y k = useMem w (y ∈ˢ b) w∈h (λ u u∈a ku →
            mem-inˡ u y b (kpair-components pair w u u x y ku k .snd)
              (sub u u∈a))

          inj : ⟨ InjClause h ⟩
          inj p p∈h q q∈h x y z (kp , kq) =
            useMem p (x ≈ˢ z) p∈h (λ u u∈a ku →
              useMem q (x ≈ˢ z) q∈h (λ v v∈a kv →
                let c₁ = kpair-components pair p u u x y ku kp
                    c₂ = kpair-components pair q v v z y kv kq
                in ≈-trans x u z (≈-sym u x (c₁ .fst))
                     (≈-trans u y z (c₁ .snd)
                       (≈-trans y v z (≈-sym v y (c₂ .snd)) (c₂ .fst)))))

  -- Reflexivity, which G3 lists beside transitivity as absent.

  injectable-refl : Separation → Collection → Pairing
                  → (a : S) → ⟨ injectable a a ⟩
  injectable-refl sep coll pair a =
    injectable-incl sep coll pair a a (λ z m → m)

  ------------------------------------------------------------------------
  -- 3.11 injectable-trans: injections compose
  ------------------------------------------------------------------------

  -- The composite graph, as one object-language formula with four bound
  -- variables and three copies of PairφK. Env (w ∷ x ∷ []), reading "w is
  -- the ordered pair of x and the g-value of the f-value of x". The four
  -- existentials bind y, z, p, q in that order, so at the matrix the
  -- environment is (q ∷ p ∷ z ∷ y ∷ w ∷ x ∷ []) and the three renamings read
  -- off index 0 to 5 as q, p, z, y, w, x.

  module Comp (f g : S) where

    cmp₁ : Fin 3 → Fin 6
    cmp₁ zero              = suc zero
    cmp₁ (suc zero)        = suc (suc (suc (suc (suc zero))))
    cmp₁ (suc (suc zero))  = suc (suc (suc zero))

    cmp₂ : Fin 3 → Fin 6
    cmp₂ zero              = zero
    cmp₂ (suc zero)        = suc (suc (suc zero))
    cmp₂ (suc (suc zero))  = suc (suc zero)

    cmp₃ : Fin 3 → Fin 6
    cmp₃ zero              = suc (suc (suc (suc zero)))
    cmp₃ (suc zero)        = suc (suc (suc (suc (suc zero))))
    cmp₃ (suc (suc zero))  = suc (suc zero)

    compφ : Formula S 2
    compφ =
      ∃̇ (∃̇ (∃̇ (∃̇
        (((var (suc zero) ∈̇ con f) ∧̇ (renameFo cmp₁ PairφK))
        ∧̇ (((var zero ∈̇ con g) ∧̇ (renameFo cmp₂ PairφK))
        ∧̇ (renameFo cmp₃ PairφK))))))

    cmp₁-agrees : (q p z y w x : S)
      → Agrees cmp₁ (q ∷ p ∷ z ∷ y ∷ w ∷ x ∷ []) (p ∷ x ∷ y ∷ [])
    cmp₁-agrees q p z y w x zero              = refl
    cmp₁-agrees q p z y w x (suc zero)        = refl
    cmp₁-agrees q p z y w x (suc (suc zero))  = refl

    cmp₂-agrees : (q p z y w x : S)
      → Agrees cmp₂ (q ∷ p ∷ z ∷ y ∷ w ∷ x ∷ []) (q ∷ y ∷ z ∷ [])
    cmp₂-agrees q p z y w x zero              = refl
    cmp₂-agrees q p z y w x (suc zero)        = refl
    cmp₂-agrees q p z y w x (suc (suc zero))  = refl

    cmp₃-agrees : (q p z y w x : S)
      → Agrees cmp₃ (q ∷ p ∷ z ∷ y ∷ w ∷ x ∷ []) (w ∷ x ∷ z ∷ [])
    cmp₃-agrees q p z y w x zero              = refl
    cmp₃-agrees q p z y w x (suc zero)        = refl
    cmp₃-agrees q p z y w x (suc (suc zero))  = refl

    comp-body : S → S → S → S → S → S → Ω
    comp-body q p z y w x =
        ((p ∈ˢ f) ⊓ (isKPair p x y))
      ⊓ (((q ∈ˢ g) ⊓ (isKPair q y z)) ⊓ (isKPair w x z))

    k₁ : (q p z y w x : S)
       → ((q ∷ p ∷ z ∷ y ∷ w ∷ x ∷ []) ⊨ (renameFo cmp₁ PairφK))
         ≡ (isKPair p x y)
    k₁ q p z y w x =
      ⊨-rename cmp₁ PairφK (q ∷ p ∷ z ∷ y ∷ w ∷ x ∷ []) (p ∷ x ∷ y ∷ [])
        (cmp₁-agrees q p z y w x) ∙ PairφK-bridge p x y

    k₂ : (q p z y w x : S)
       → ((q ∷ p ∷ z ∷ y ∷ w ∷ x ∷ []) ⊨ (renameFo cmp₂ PairφK))
         ≡ (isKPair q y z)
    k₂ q p z y w x =
      ⊨-rename cmp₂ PairφK (q ∷ p ∷ z ∷ y ∷ w ∷ x ∷ []) (q ∷ y ∷ z ∷ [])
        (cmp₂-agrees q p z y w x) ∙ PairφK-bridge q y z

    k₃ : (q p z y w x : S)
       → ((q ∷ p ∷ z ∷ y ∷ w ∷ x ∷ []) ⊨ (renameFo cmp₃ PairφK))
         ≡ (isKPair w x z)
    k₃ q p z y w x =
      ⊨-rename cmp₃ PairφK (q ∷ p ∷ z ∷ y ∷ w ∷ x ∷ []) (w ∷ x ∷ z ∷ [])
        (cmp₃-agrees q p z y w x) ∙ PairφK-bridge w x z

    comp-reading : (w x : S)
      → ((w ∷ x ∷ []) ⊨ compφ)
        ≡ (⋁ S (λ y → ⋁ S (λ z → ⋁ S (λ p → ⋁ S (λ q →
             comp-body q p z y w x)))))
    comp-reading w x =
      cong (⋁ S) (funExt (λ y → cong (⋁ S) (funExt (λ z →
        cong (⋁ S) (funExt (λ p → cong (⋁ S) (funExt (λ q →
          cong₂ _⊓_
            (cong ((p ∈ˢ f) ⊓_) (k₁ q p z y w x))
            (cong₂ _⊓_ (cong ((q ∈ˢ g) ⊓_) (k₂ q p z y w x))
                       (k₃ q p z y w x))))))))))

  injectable-trans : Separation → Collection → Pairing
                   → (a b d : S)
                   → ⟨ injectable a b ⟩ → ⟨ injectable b d ⟩
                   → ⟨ injectable a d ⟩
  injectable-trans sep coll pair a b d ha hb =
    PT.rec (snd (injectable a d))
      (λ { (f , finj) → PT.rec (snd (injectable a d))
        (λ { (g , ginj) → compose f finj g ginj }) hb })
      ha
    where
      compose : (f : S) → ⟨ isInjection f a b ⟩
              → (g : S) → ⟨ isInjection g b d ⟩ → ⟨ injectable a d ⟩
      compose f finj g ginj =
        PT.rec (snd (injectable a d))
          (λ { (h , fw , bw) → ∣ h , build h fw bw ∣₁ })
          (graphOf sep coll a C.compφ prem)
        where
          module C = Comp f g

          f-single : ⟨ SingleClause f ⟩
          f-single = finj .fst .snd

          f-dom : ⟨ DomClause f a ⟩
          f-dom = finj .snd .fst

          f-ran : ⟨ RanClause f b ⟩
          f-ran = finj .snd .snd .fst

          f-inj : ⟨ InjClause f ⟩
          f-inj = finj .snd .snd .snd

          g-single : ⟨ SingleClause g ⟩
          g-single = ginj .fst .snd

          g-dom : ⟨ DomClause g b ⟩
          g-dom = ginj .snd .fst

          g-ran : ⟨ RanClause g d ⟩
          g-ran = ginj .snd .snd .fst

          g-inj : ⟨ InjClause g ⟩
          g-inj = ginj .snd .snd .snd

          tgtP : S → Ω
          tgtP x = ⋁ S (λ w → (w ∷ x ∷ []) ⊨ C.compφ)

          mk : (x y z p q : S) → ⟨ p ∈ˢ f ⟩ → ⟨ isKPair p x y ⟩
             → ⟨ q ∈ˢ g ⟩ → ⟨ isKPair q y z ⟩ → ⟨ tgtP x ⟩
          mk x y z p q p∈f kp q∈g kq =
            PT.map (λ { (w , kw) →
              w , subst ⟨_⟩ (sym (C.comp-reading w x))
                    ∣ y , ∣ z , ∣ p , ∣ q , ((p∈f , kp) , ((q∈g , kq) , kw))
                      ∣₁ ∣₁ ∣₁ ∣₁ })
              (kpairOf pair x z)

          prem : ⟨ ⋀ S (λ x → (x ∈ˢ a) ⇒ (⋁ S (λ w → (w ∷ x ∷ []) ⊨ C.compφ))) ⟩
          prem x x∈a = PT.rec (snd (tgtP x))
            (λ { (y , r₁) → PT.rec (snd (tgtP x))
              (λ { (p , p∈f , kp) → PT.rec (snd (tgtP x))
                (λ { (z , r₂) → PT.rec (snd (tgtP x))
                  (λ { (q , q∈g , kq) → mk x y z p q p∈f kp q∈g kq })
                  r₂ })
                (g-dom y (f-ran p p∈f x y kp)) })
              r₁ })
            (f-dom x x∈a)

          build : (h : S)
                → ⟨ ⋀ S (λ w → (w ∈ˢ h) ⇒
                      (⋁ S (λ x → (x ∈ˢ a) ⊓ ((w ∷ x ∷ []) ⊨ C.compφ)))) ⟩
                → ⟨ ⋀ S (λ x → (x ∈ˢ a) ⇒
                      (⋁ S (λ w → (w ∈ˢ h) ⊓ ((w ∷ x ∷ []) ⊨ C.compφ)))) ⟩
                → ⟨ isInjection h a d ⟩
          build h fw bw = ((rel , single) , (dom , (ran , inj)))
            where
              useMem : (w : S) (P : Ω) → ⟨ w ∈ˢ h ⟩
                     → ((x y z p q : S) → ⟨ x ∈ˢ a ⟩
                        → ⟨ C.comp-body q p z y w x ⟩ → ⟨ P ⟩)
                     → ⟨ P ⟩
              useMem w P w∈h k = PT.rec (snd P)
                (λ { (x , x∈a , sat) → PT.rec (snd P)
                  (λ { (y , r₁) → PT.rec (snd P)
                    (λ { (z , r₂) → PT.rec (snd P)
                      (λ { (p , r₃) → PT.rec (snd P)
                        (λ { (q , body) → k x y z p q x∈a body })
                        r₃ })
                      r₂ })
                    r₁ })
                  (subst ⟨_⟩ (C.comp-reading w x) sat) })
                (fw w w∈h)

              rel : ⟨ isRelation h ⟩
              rel w w∈h = useMem w (⋁ S (λ u → ⋁ S (λ v → isKPair w u v))) w∈h
                (λ x y z p q x∈a body → ∣ x , ∣ z , body .snd .snd ∣₁ ∣₁)

              domGoal : S → Ω
              domGoal x = ⋁ S (λ v → ⋁ S (λ p → (p ∈ˢ h) ⊓ (isKPair p x v)))

              domOne : (x w : S) → ⟨ w ∈ˢ h ⟩ → ⟨ (w ∷ x ∷ []) ⊨ C.compφ ⟩
                     → ⟨ domGoal x ⟩
              domOne x w w∈h sat = PT.rec (snd (domGoal x))
                (λ { (y , r₁) → PT.rec (snd (domGoal x))
                  (λ { (z , r₂) → PT.rec (snd (domGoal x))
                    (λ { (p , r₃) → PT.rec (snd (domGoal x))
                      (λ { (q , body) →
                           ∣ z , ∣ w , (w∈h , body .snd .snd) ∣₁ ∣₁ })
                      r₃ })
                    r₂ })
                  r₁ })
                (subst ⟨_⟩ (C.comp-reading w x) sat)

              dom : ⟨ DomClause h a ⟩
              dom x x∈a = PT.rec (snd (domGoal x))
                (λ { (w , w∈h , sat) → domOne x w w∈h sat }) (bw x x∈a)

              ran : ⟨ RanClause h d ⟩
              ran w w∈h x' z' k = useMem w (z' ∈ˢ d) w∈h
                (λ x y z p q x∈a body →
                  mem-inˡ z z' d
                    (kpair-components pair w x z x' z' (body .snd .snd) k .snd)
                    (g-ran q (body .snd .fst .fst) y z (body .snd .fst .snd)))

              single : ⟨ SingleClause h ⟩
              single w₁ w₁∈h w₂ w₂∈h x y z (k₁' , k₂') =
                useMem w₁ (y ≈ˢ z) w₁∈h (λ x₁ y₁ z₁ p₁ q₁ _ b₁ →
                  useMem w₂ (y ≈ˢ z) w₂∈h (λ x₂ y₂ z₂ p₂ q₂ _ b₂ →
                    let c₁ = kpair-components pair w₁ x₁ z₁ x y (b₁ .snd .snd) k₁'
                        c₂ = kpair-components pair w₂ x₂ z₂ x z (b₂ .snd .snd) k₂'
                        x₁≈x₂ = ≈-trans x₁ x x₂ (c₁ .fst) (≈-sym x₂ x (c₂ .fst))
                        y₁≈y₂ = f-single p₁ (b₁ .fst .fst) p₂ (b₂ .fst .fst)
                                  x₂ y₁ y₂
                                  ( kpair-subst p₁ x₁ x₂ y₁ y₁ x₁≈x₂
                                      (≈-refl y₁) (b₁ .fst .snd)
                                  , b₂ .fst .snd )
                        z₁≈z₂ = g-single q₁ (b₁ .snd .fst .fst)
                                  q₂ (b₂ .snd .fst .fst) y₂ z₁ z₂
                                  ( kpair-subst q₁ y₁ y₂ z₁ z₁ y₁≈y₂
                                      (≈-refl z₁) (b₁ .snd .fst .snd)
                                  , b₂ .snd .fst .snd )
                    in ≈-trans y z₁ z (≈-sym z₁ y (c₁ .snd))
                         (≈-trans z₁ z₂ z z₁≈z₂ (c₂ .snd))))

              inj : ⟨ InjClause h ⟩
              inj w₁ w₁∈h w₂ w₂∈h x y z (k₁' , k₂') =
                useMem w₁ (x ≈ˢ z) w₁∈h (λ x₁ y₁ z₁ p₁ q₁ _ b₁ →
                  useMem w₂ (x ≈ˢ z) w₂∈h (λ x₂ y₂ z₂ p₂ q₂ _ b₂ →
                    let c₁ = kpair-components pair w₁ x₁ z₁ x y (b₁ .snd .snd) k₁'
                        c₂ = kpair-components pair w₂ x₂ z₂ z y (b₂ .snd .snd) k₂'
                        z₁≈z₂ = ≈-trans z₁ y z₂ (c₁ .snd) (≈-sym z₂ y (c₂ .snd))
                        y₁≈y₂ = g-inj q₁ (b₁ .snd .fst .fst)
                                  q₂ (b₂ .snd .fst .fst) y₁ z₂ y₂
                                  ( kpair-subst q₁ y₁ y₁ z₁ z₂ (≈-refl y₁)
                                      z₁≈z₂ (b₁ .snd .fst .snd)
                                  , b₂ .snd .fst .snd )
                        x₁≈x₂ = f-inj p₁ (b₁ .fst .fst) p₂ (b₂ .fst .fst)
                                  x₁ y₂ x₂
                                  ( kpair-subst p₁ x₁ x₁ y₁ y₂ (≈-refl x₁)
                                      y₁≈y₂ (b₁ .fst .snd)
                                  , b₂ .fst .snd )
                    in ≈-trans x x₁ z (≈-sym x₁ x (c₁ .fst))
                         (≈-trans x₁ x₂ z x₁≈x₂ (c₂ .fst))))

  ------------------------------------------------------------------------
  -- 3.12 What ord-compare says where the answer is known
  ------------------------------------------------------------------------

  -- A trichotomy is worth nothing if the three disjuncts can hold together,
  -- and the brief's trap is exactly a well-typed statement that says
  -- nothing. The two exclusions below are the discriminating checks: they
  -- fail for any predicate that has collapsed to its hypothesis, because a
  -- collapsed predicate makes all three disjuncts derivable at once.

  ord-∈-irrefl : FoundationInduction → (α δ : S) → ⟨ isOrdinal α ⟩
               → ⟨ α ∈ˢ δ ⟩ → ⟨ δ ∈ˢ α ⟩ → Empty.⊥
  ord-∈-irrefl find α δ αord α∈δ δ∈α = no-self find α (αord .fst δ δ∈α α α∈δ)

  ord-∈-not-≈ : FoundationInduction → (α δ : S)
              → ⟨ α ≈ˢ δ ⟩ → ⟨ α ∈ˢ δ ⟩ → Empty.⊥
  ord-∈-not-≈ find α δ e α∈δ =
    no-self find α (mem-inʳ α δ α (≈-sym α δ e) α∈δ)

  -- The first known answer. Two ordinals with α ∈ δ: ord-compare must return
  -- the first disjunct, and the run below refutes the other two and gets the
  -- hypothesis back out of the disjunction.

  ord-compare-known : FoundationInduction → Separation → LEM ℓ
                    → (α δ : S) → ⟨ isOrdinal α ⟩ → ⟨ isOrdinal δ ⟩
                    → ⟨ α ∈ˢ δ ⟩ → ⟨ α ∈ˢ δ ⟩
  ord-compare-known find sep lem α δ αord δord α∈δ =
    PT.rec (snd (α ∈ˢ δ)) three (ord-compare find sep lem α δ αord δord)
    where
      three : ⟨ α ∈ˢ δ ⟩ ⊎ ⟨ (α ≈ˢ δ) ⊔ (δ ∈ˢ α) ⟩ → ⟨ α ∈ˢ δ ⟩
      three (inl h) = h
      three (inr r) = PT.rec (snd (α ∈ˢ δ))
        (λ { (inl e) → Empty.rec (ord-∈-not-≈ find α δ e α∈δ)
           ; (inr h) → Empty.rec (ord-∈-irrefl find α δ αord α∈δ h) }) r

  -- The second known answer, and the one a consumer actually wants. It is
  -- CardinalBridge.agda:597's conclusion verbatim: given that μ does not
  -- belong to δ, δ is below or equal to μ. isSuccCardinal's minimality
  -- conjunct ranges over the WHOLE carrier (a plain ∀̇ at :587, ⋀ S at :596),
  -- which is why cardinality alone does not give it and why comparability of
  -- ordinals is the thing that has to be bought.

  ord-le : FoundationInduction → Separation → LEM ℓ
         → (δ μ : S) → ⟨ isOrdinal δ ⟩ → ⟨ isOrdinal μ ⟩
         → (⟨ μ ∈ˢ δ ⟩ → Empty.⊥) → ⟨ (δ ≈ˢ μ) ⊔ (δ ∈ˢ μ) ⟩
  ord-le find sep lem δ μ δord μord notin =
    PT.rec (snd goal) three (ord-compare find sep lem δ μ δord μord)
    where
      goal : Ω
      goal = (δ ≈ˢ μ) ⊔ (δ ∈ˢ μ)

      three : ⟨ δ ∈ˢ μ ⟩ ⊎ ⟨ (δ ≈ˢ μ) ⊔ (μ ∈ˢ δ) ⟩ → ⟨ goal ⟩
      three (inl h) = ∣ inr h ∣₁
      three (inr r) = PT.rec (snd goal)
        (λ { (inl e) → ∣ inl e ∣₁ ; (inr h) → Empty.rec (notin h) }) r

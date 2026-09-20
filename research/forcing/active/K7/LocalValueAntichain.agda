{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K7.LocalValueAntichain {ℓ}
  (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; Term; var; con; _∧̇_; ∃̇_; ∃̇∈ )
open import Base.Classical using ( LEM )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
import CodedVocabulary
import CardinalBridge
import K7.PossibleValues
import K7.ValueAntichains
import K7.ChainConditions

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open PT using ( ∣_∣₁ )
module OP = OrdinaryProfile 𝒮
module CV = CodedVocabulary 𝒮
module CB = CardinalBridge 𝒮
module CA = K7.ChainConditions 𝒮 ext paths
module PV = K7.PossibleValues 𝒮 paths
open PV using ( _⊨ᴳ_; ≈ˢ→≡; ≡→≈ˢ )

module Names (IsNm : S → Ω) where

  module N = PV.Names IsNm
  open N using ( Nm; codesOf; valueFo )

  module AtG
    (c o : S) (Cond : Type ℓ)
    (cnd : Cond → S)
    (cnd-carrier : (r : Cond) → ⟨ cnd r ∈ˢ c ⟩)
    (cndOf : (q : S) → ⟨ q ∈ˢ c ⟩ → Cond)
    (cnd-cndOf : (q : S) (hq : ⟨ q ∈ˢ c ⟩) → cnd (cndOf q hq) ≡ q)
    (G∈ : Cond → Ω)
    (_≈[G]_ _∈[G]_ : S → S → Ω)
    (chk : S → Nm)
    where

    module E = N.AtG c Cond cnd cnd-carrier cndOf cnd-cndOf
      G∈ _≈[G]_ _∈[G]_ chk

    module ExtensionCardinal = CardinalBridge E.𝒮ᴱ

    functionFo : Formula Nm 1
    functionFo = ExtensionCardinal.IsFunctionφ

    order : Cond → Cond → Ω
    order r p = CV.refinesΔ o (cnd r) (cnd p)

    orderFo : Formula S 2
    orderFo = ∃̇∈ (con o) (CV.prAtˢ zero (suc zero) (suc (suc zero)))

    orderFo-reading : (r p : Cond)
      → ((cnd r ∷ cnd p ∷ []) ⊨ᴳ orderFo) ≡ order r p
    orderFo-reading r p = refl

    module Forcing
      (forces : ∀ {k} → Cond → Formula Nm k → Vec Nm k → Ω)
      (truth-at : ∀ {k} (φ : Formula Nm k) (ν : Vec Nm k)
        → (ν E.⊨ φ) ≡ ⋁ Cond (λ r → G∈ r ⊓ forces r φ ν))
      (forces-mono : ∀ {k} (r p : Cond) → ⟨ order r p ⟩
        → (φ : Formula Nm k) (ν : Vec Nm k)
        → ⟨ forces p φ ν ⟩ → ⟨ forces r φ ν ⟩)
      (directed : (p q : Cond) → ⟨ G∈ p ⟩ → ⟨ G∈ q ⟩
        → ⟨ ⋁ Cond (λ r → G∈ r ⊓ (order r p ⊓ order r q)) ⟩)
      (forcesΔ : ∀ {k} → Formula Nm k → Formula S (suc k))
      (forcesΔ-reading : ∀ {k} (φ : Formula Nm k) (ν : Vec Nm k) (r : Cond)
        → ((cnd r ∷ codesOf ν) ⊨ᴳ forcesΔ φ) ≡ forces r φ ν)
      (mk : OP.Separation → S → Formula S 1 → S)
      (mk-in : (sep : OP.Separation) (b : S) (θ : Formula S 1) (a : S)
        → ⟨ a ∈ˢ b ⟩ → ⟨ (a ∷ []) ⊨ᴳ θ ⟩ → ⟨ a ∈ˢ mk sep b θ ⟩)
      (mk-bound : (sep : OP.Separation) (b : S) (θ : Formula S 1) (a : S)
        → ⟨ a ∈ˢ mk sep b θ ⟩ → ⟨ a ∈ˢ b ⟩)
      (mk-sat : (sep : OP.Separation) (b : S) (θ : Formula S 1) (a : S)
        → ⟨ a ∈ˢ mk sep b θ ⟩ → ⟨ (a ∷ []) ⊨ᴳ θ ⟩)
      where

      module V = E.Values forces truth-at order forces-mono directed
        orderFo orderFo-reading forcesΔ forcesΔ-reading mk mk-in mk-bound mk-sat

      module AtBound (β : S) (chkFo : Formula S 2)
        (chkFo-reading : (u a : S) → ⟨ a ∈ˢ β ⟩
          → ((u ∷ a ∷ []) ⊨ᴳ chkFo) ≡ (u ≈ˢ fst (chk a)))
        where

        module B = V.AtBound β chkFo chkFo-reading

        checkSlots : Fin 2 → Term S 3
        checkSlots zero = var zero
        checkSlots (suc zero) = var (suc (suc zero))

        forceSlots : S → Fin 3 → Term S 3
        forceSlots ξ zero = var (suc zero)
        forceSlots ξ (suc zero) = con (fst (chk ξ))
        forceSlots ξ (suc (suc zero)) = var zero

        orderSlots : Cond → Fin 2 → Term S 2
        orderSlots p zero = var zero
        orderSlots p (suc zero) = con (cnd p)

        -- The free slots are a condition code and a candidate ground value.
        -- The only existential recovers the check code of that value.
        decidingFo : Cond → Nm → S → Formula S 2
        decidingFo p f ξ = CV.instFo (orderSlots p) orderFo
          ∧̇ ∃̇ (CV.instFo checkSlots chkFo
            ∧̇ CV.instFo (forceSlots ξ) (forcesΔ (valueFo f)))

        check-fits : (u q a : S)
          → CV.Fits checkSlots (u ∷ q ∷ a ∷ []) (u ∷ a ∷ [])
        check-fits u q a zero = refl
        check-fits u q a (suc zero) = refl

        force-fits : (ξ u q a : S)
          → CV.Fits (forceSlots ξ) (u ∷ q ∷ a ∷ [])
            (q ∷ fst (chk ξ) ∷ u ∷ [])
        force-fits ξ u q a zero = refl
        force-fits ξ u q a (suc zero) = refl
        force-fits ξ u q a (suc (suc zero)) = refl

        order-fits : (p : Cond) (q a : S)
          → CV.Fits (orderSlots p) (q ∷ a ∷ []) (q ∷ cnd p ∷ [])
        order-fits p q a zero = refl
        order-fits p q a (suc zero) = refl

        deciding-reading : (p r : Cond) (f : Nm) (ξ a : S) → ⟨ a ∈ˢ β ⟩
          → ((cnd r ∷ a ∷ []) ⊨ᴳ decidingFo p f ξ)
            ≡ (order r p ⊓ forces r (valueFo f) (chk ξ ∷ chk a ∷ []))
        deciding-reading p r f ξ a ha = cong₂ _⊓_ order-path
          (⇔toPath {P = (cnd r ∷ a ∷ []) ⊨ᴳ ∃̇ inner}
            {Q = forces r (valueFo f) (chk ξ ∷ chk a ∷ [])} to from)
          where
          order-path : ((cnd r ∷ a ∷ []) ⊨ᴳ CV.instFo (orderSlots p) orderFo)
            ≡ order r p
          order-path = CV.⊨-inst (orderSlots p) orderFo
            (cnd r ∷ a ∷ []) (cnd r ∷ cnd p ∷ []) (order-fits p (cnd r) a)

          inner : Formula S 3
          inner = CV.instFo checkSlots chkFo
            ∧̇ CV.instFo (forceSlots ξ) (forcesΔ (valueFo f))

          to : ⟨ (cnd r ∷ a ∷ []) ⊨ᴳ ∃̇ inner ⟩
            → ⟨ forces r (valueFo f) (chk ξ ∷ chk a ∷ []) ⟩
          to = PT.rec (snd (forces r (valueFo f) (chk ξ ∷ chk a ∷ [])))
            (λ { (u , hc , hf) → subst ⟨_⟩
              (forcesΔ-reading (valueFo f) (chk ξ ∷ chk a ∷ []) r)
              (subst (λ x → ⟨ (cnd r ∷ fst (chk ξ) ∷ x ∷ [])
                ⊨ᴳ forcesΔ (valueFo f) ⟩)
                (≈ˢ→≡ (subst ⟨_⟩
                  (CV.⊨-inst checkSlots chkFo (u ∷ cnd r ∷ a ∷ [])
                    (u ∷ a ∷ []) (check-fits u (cnd r) a)
                    ∙ chkFo-reading u a ha) hc))
                (subst ⟨_⟩ (CV.⊨-inst (forceSlots ξ) (forcesΔ (valueFo f))
                  (u ∷ cnd r ∷ a ∷ []) (cnd r ∷ fst (chk ξ) ∷ u ∷ [])
                  (force-fits ξ u (cnd r) a)) hf)) })

          from : ⟨ forces r (valueFo f) (chk ξ ∷ chk a ∷ []) ⟩
            → ⟨ (cnd r ∷ a ∷ []) ⊨ᴳ ∃̇ inner ⟩
          from hf = ∣ fst (chk a)
            , subst ⟨_⟩ (sym (CV.⊨-inst checkSlots chkFo
                (fst (chk a) ∷ cnd r ∷ a ∷ []) (fst (chk a) ∷ a ∷ [])
                (check-fits (fst (chk a)) (cnd r) a)
                ∙ chkFo-reading (fst (chk a)) a ha)) (≡→≈ˢ refl)
            , subst ⟨_⟩ (sym (CV.⊨-inst (forceSlots ξ) (forcesΔ (valueFo f))
                (fst (chk a) ∷ cnd r ∷ a ∷ [])
                (cnd r ∷ fst (chk ξ) ∷ fst (chk a) ∷ [])
                (force-fits ξ (fst (chk a)) (cnd r) a)
                ∙ forcesΔ-reading (valueFo f) (chk ξ ∷ chk a ∷ []) r)) hf ∣₁

        module Consequence
          (checkedEq : Cond → S → S → Ω)
          (function-values : (r : Cond) (f : Nm) (ξ a b : S)
            → ⟨ forces r functionFo (f ∷ []) ⟩
            → ⟨ forces r (valueFo f) (chk ξ ∷ chk a ∷ []) ⟩
            → ⟨ forces r (valueFo f) (chk ξ ∷ chk b ∷ []) ⟩
            → ⟨ checkedEq r a b ⟩)
          (checked-reflect : (r : Cond) (a b : S)
            → ⟨ checkedEq r a b ⟩ → ⟨ a ≈ˢ b ⟩)
          (order-refl : (r : Cond) → ⟨ order r r ⟩)
          (order-trans : (r q p : Cond) → ⟨ order r q ⟩ → ⟨ order q p ⟩
            → ⟨ order r p ⟩)
          where

          module AtFunction (sep : OP.Separation) (p : Cond) (f : Nm)
            (hf : ⟨ forces p functionFo (f ∷ []) ⟩) (ξ : S) where

            values : S
            values = B.valuesOf sep p f ξ

            bounded : (a : S) → ⟨ a ∈ˢ values ⟩ → ⟨ a ∈ˢ β ⟩
            bounded a ha = fst (subst ⟨_⟩ (B.valuesOf-spec sep p f ξ a) ha)

            total : (a : S) → ⟨ a ∈ˢ values ⟩
              → ⟨ ⋁ S (λ q → (q ∈ˢ c) ⊓ ((q ∷ a ∷ []) ⊨ᴳ decidingFo p f ξ)) ⟩
            total a ha = PT.map
              (λ { (r , hrp , hval) → cnd r , cnd-carrier r
                , subst ⟨_⟩ (sym (deciding-reading p r f ξ a (bounded a ha)))
                    (hrp , hval) })
              (snd (subst ⟨_⟩ (B.valuesOf-spec sep p f ξ a) ha))

            decode : (q a : S) (hq : ⟨ q ∈ˢ c ⟩) → ⟨ a ∈ˢ values ⟩
              → ⟨ (q ∷ a ∷ []) ⊨ᴳ decidingFo p f ξ ⟩
              → ⟨ order (cndOf q hq) p
                  ⊓ forces (cndOf q hq) (valueFo f) (chk ξ ∷ chk a ∷ []) ⟩
            decode q a hq ha h = subst ⟨_⟩
              (deciding-reading p (cndOf q hq) f ξ a (bounded a ha))
              (subst (λ x → ⟨ (x ∷ a ∷ []) ⊨ᴳ decidingFo p f ξ ⟩)
                (sym (cnd-cndOf q hq)) h)

            common-values : (r q t : Cond) (a b : S)
              → ⟨ order r p ⟩ → ⟨ order t r ⟩ → ⟨ order t q ⟩
              → ⟨ forces r (valueFo f) (chk ξ ∷ chk a ∷ []) ⟩
              → ⟨ forces q (valueFo f) (chk ξ ∷ chk b ∷ []) ⟩
              → ⟨ a ≈ˢ b ⟩
            common-values r q t a b hrp htr htq ha hb = checked-reflect t a b
              (function-values t f ξ a b
                (forces-mono t p (order-trans t r p htr hrp) functionFo (f ∷ []) hf)
                (forces-mono t r htr (valueFo f) (chk ξ ∷ chk a ∷ []) ha)
                (forces-mono t q htq (valueFo f) (chk ξ ∷ chk b ∷ []) hb))

            determinate : (a b q : S) → ⟨ a ∈ˢ values ⟩ → ⟨ b ∈ˢ values ⟩
              → ⟨ q ∈ˢ c ⟩ → ⟨ (q ∷ a ∷ []) ⊨ᴳ decidingFo p f ξ ⟩
              → ⟨ (q ∷ b ∷ []) ⊨ᴳ decidingFo p f ξ ⟩ → ⟨ a ≈ˢ b ⟩
            determinate a b q ha hb hq h k = common-values r r r a b
              (fst u) (order-refl r) (order-refl r) (snd u) (snd v)
              where
              r : Cond
              r = cndOf q hq
              u : ⟨ order r p ⊓ forces r (valueFo f) (chk ξ ∷ chk a ∷ []) ⟩
              u = decode q a hq ha h
              v : ⟨ order r p ⊓ forces r (valueFo f) (chk ξ ∷ chk b ∷ []) ⟩
              v = decode q b hq hb k

            decode-order : (r q : S) (hr : ⟨ r ∈ˢ c ⟩) (hq : ⟨ q ∈ˢ c ⟩)
              → ⟨ CV.refinesΔ o r q ⟩ → ⟨ order (cndOf r hr) (cndOf q hq) ⟩
            decode-order r q hr hq = subst ⟨_⟩ (sym
              (cong₂ (CV.refinesΔ o) (cnd-cndOf r hr) (cnd-cndOf q hq)))

            incompatible : (a b q r : S)
              → ⟨ a ∈ˢ values ⟩ → ⟨ b ∈ˢ values ⟩ → ⟨ q ∈ˢ c ⟩ → ⟨ r ∈ˢ c ⟩
              → ⟨ (q ∷ a ∷ []) ⊨ᴳ decidingFo p f ξ ⟩
              → ⟨ (r ∷ b ∷ []) ⊨ᴳ decidingFo p f ξ ⟩
              → (⟨ a ≈ˢ b ⟩ → Empty.⊥) → ⟨ CV.compatibleΔ c o q r ⟩ → Empty.⊥
            incompatible a b q r ha hb hq hr h k neq = PT.rec Empty.isProp⊥
              (λ { (t , ht , htq , htr) → neq
                (common-values (cndOf q hq) (cndOf r hr) (cndOf t ht) a b
                  (fst (decode q a hq ha h)) (decode-order t q ht hq htq)
                  (decode-order t r ht hr htr)
                  (snd (decode q a hq ha h)) (snd (decode r b hr hb k))) })

          module GroundChoice
            (pair : OP.Pairing) (un : OP.Union) (pow : OP.PowerSet)
            (coll : OP.Collection) (find : OP.FoundationInduction)
            (seed : S) (lem : LEM ℓ) (choice : OP.ChoiceSet)
            where

            value-antichain : (sep : OP.Separation) (p : Cond) (f : Nm)
              → ⟨ forces p functionFo (f ∷ []) ⟩ → (ξ : S)
              → ⟨ ⋁ S (λ d → (CV.subsetΔ d c ⊓ CA.antichainΔ c o d)
                  ⊓ CB.injectable (B.valuesOf sep p f ξ) d) ⟩
            value-antichain sep p f hf ξ = Selected.selected-antichain
              where
              module Local = AtFunction sep p f hf ξ
              module Antichains = K7.ValueAntichains 𝒮 ext paths
                pair un pow sep coll find seed
              module Selected = Antichains.AtRelation lem choice
                Local.values c o (decidingFo p f ξ)
                Local.total Local.determinate Local.incompatible

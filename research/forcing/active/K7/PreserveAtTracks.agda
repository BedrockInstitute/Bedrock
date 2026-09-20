{-# OPTIONS --cubical --safe --guardedness #-}

-- K7 Track F, THE SEAM PROBE. IT APPLIES TRACKS A, B AND E FOR REAL.
--
-- Architecture 4.0: "A K7 track that builds its own lookalike structure and
-- does not add this probe ships a well typed theorem about nothing." Track F's
-- exposure to that is specific. Its Track A slot is the chain condition, and
-- the whole T3 protection is that the chain condition is a HYPOTHESIS; a
-- hypothesis whose type merely resembles Track A's CCC₂ᴵ would leave the
-- headline theorem about a different predicate, and no grep of either file
-- would see it. Its Track E slot is the possible-value operator, and a
-- lookalike there would leave the covering theorem about a set nobody builds.
--
-- So this file applies K7.ChainConditions, K7.CardinalOrder and
-- K7.PossibleValues for real, fills every slot Track F takes from them with
-- the genuine export, and instantiates the headline theorems. Only the K5/K6
-- engine and the two obligations no track owns arrive as probe parameters,
-- which is the correct shape for a seam probe: a parameter is maximally stuck.
--
-- WHAT THE PROBE MEASURED, and three of the four are corrections under rule 14.
--
-- 1. CCC₂ᴵ is `S → S → S → Ω` (K7/ChainConditions.agda:305), carrier and order
--    explicit. Architecture 2.2 prints `S → Ω`. The architecture is wrong.
-- 2. The CCC₂ use law is `ccc-use` (K7/ChainConditions.agda:346-348), not
--    `ccc₂-use`, and its conclusion is `⟨ injectable d v ⟩`.
-- 3. Track E's possible-value operator is
--    `valuesOf : Separation → (p : Cond) → (f : Nm) (ξ : S) → S`
--    (K7/PossibleValues.agda:452-453) with the BOUND a module parameter
--    (:297-298) and NO Collection spent. Architecture 2.5 prints
--    `Collection → Separation → (f : Nm) (β ξ : S) → S`. The architecture is
--    wrong and Track F follows the source.
-- 4. Possible values use the same coded order as the chain condition. The
--    covering argument refines a truth witness together with its base
--    condition inside the filter. Antichain bounds require that this base
--    condition force the actual function formula.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using ( Formula; con; var; _∈̇_; ∃̇∈ )
open import Base.Classical using ( LEM )
import OrdinaryProfile
import CardinalBridge
import CodedVocabulary
import K7.ChainConditions
import K7.CardinalOrder
import K7.PossibleValues
import K7.NoCollapse
import K7.ValueFamilies
import K7.InverseSurjection
import K7.CountableCover
import K7.UncountableCover
import K7.LocalValueAntichain
import K7.CheckIndexedFamilies
import K8.GroundSets
import NameKernel
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT

module K7.PreserveAtTracks
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module OP  = OrdinaryProfile 𝒮
module CV  = CodedVocabulary 𝒮
module CBᴳ = CardinalBridge 𝒮
module CA  = K7.ChainConditions 𝒮 ext paths
module PV  = K7.PossibleValues 𝒮 paths
module NC  = K7.NoCollapse 𝒮 ext paths

open OP using ( Separation ; Collection )

--------------------------------------------------------------------------------
-- 1. The Track A slots, each an alias whose TYPE is Track F's parameter type
--    and whose BODY is the producer's export
--------------------------------------------------------------------------------

subsetΔ-seam : S → S → Ω
subsetΔ-seam = CV.subsetΔ

antichainΔ-seam : S → S → S → Ω
antichainΔ-seam = CA.antichainΔ

maximalΔ-seam : S → S → S → Ω
maximalΔ-seam = CA.maximalΔ

ccc₁-seam ccc₂-seam : S → S → S → Ω
ccc₁-seam = CA.CCC₁ᴵ
ccc₂-seam = CA.CCC₂ᴵ

ccc-use-seam : (c o w d : S) → ⟨ CA.CCC₂ᴵ c o w ⟩ → ⟨ CV.subsetΔ d c ⟩
             → ⟨ CA.antichainΔ c o d ⟩ → ⟨ CBᴳ.injectable d w ⟩
ccc-use-seam = CA.ccc-use

ccc₁-use-seam : (c o w d : S) → ⟨ CA.CCC₁ᴵ c o w ⟩ → ⟨ CV.subsetΔ d c ⟩
              → ⟨ CA.maximalΔ c o d ⟩ → ⟨ CBᴳ.injectable d w ⟩
ccc₁-use-seam = CA.ccc₁-use

-- And the identification that the probe exists to make: the countability in
-- Track A's chain condition IS CardinalBridge's injectable, so Track F's
-- conclusion and Track A's hypothesis speak of one notion of countable, by
-- refl and not by a bridge lemma.

countable-seam : (w d : S) → CA.countableΔ w d ≡ CBᴳ.injectable d w
countable-seam w d = refl

--------------------------------------------------------------------------------
-- 2. The extension side, with Track B and Track E applied at it
--------------------------------------------------------------------------------

module Names (IsNm : S → Ω) where

  module N  = NC.Names IsNm
  module NE = PV.Names IsNm

  -- Track E takes its name type from O7 (K7/PossibleValues.agda:161) and Track
  -- F writes the Sigma itself. A Sigma is not generative, so the two agree
  -- definitionally; this is the check, and it is what lets Track E's exports
  -- fill Track F's slots at all.

  name-seam : N.Nm ≡ NE.Nm
  name-seam = refl

  module AtG (_≈[G]_ _∈[G]_ : S → S → Ω) where

    module A   = N.AtG _≈[G]_ _∈[G]_
    module COᴱ = K7.CardinalOrder A.𝒮ᴱ

    -- Track B's surjection vocabulary, read at the EXTENSION structure. Q6
    -- assigns it to K7/CardinalOrder.agda and it is structure-polymorphic, so
    -- the same declaration serves both sides; this alias is the check that it
    -- really does.

    isSurjectionᴱ-seam : N.Nm → N.Nm → N.Nm → Ω
    isSurjectionᴱ-seam = COᴱ.isSurjection

    module AtNotion
      -- The notion, and the extra data Track E's AtG needs beyond Track F's.
      (carrierᶠ    : S)
      (Cond        : Type ℓ)
      (cnd         : Cond → S)
      (cnd-carrier : (r : Cond) → ⟨ cnd r ∈ˢ carrierᶠ ⟩)
      (cndOf       : (q : S) → ⟨ q ∈ˢ carrierᶠ ⟩ → Cond)
      (cnd-cndOf   : (q : S) (hq : ⟨ q ∈ˢ carrierᶠ ⟩) → cnd (cndOf q hq) ≡ q)
      (G∈          : Cond → Ω)
      (chk         : S → N.Nm)
      where

      module P  = A.AtNotion Cond G∈
      module EG = NE.AtG carrierᶠ Cond cnd cnd-carrier cndOf cnd-cndOf
                         G∈ _≈[G]_ _∈[G]_ chk

      -- The structures agree on the nose, which is architecture 4.0's
      -- structure-agrees check at this track's pair of producers.

      structure-agrees : A.𝒮ᴱ ≡ EG.𝒮ᴱ
      structure-agrees = refl

      ----------------------------------------------------------------------
      -- 3. The instantiation, with every landed slot filled for real
      ----------------------------------------------------------------------

      module Probe
        (o : S)
        -- Ground composition is supplied at this seam's explicit profile.
        (injectable-trans : Separation → Collection → (a b d : S)
                          → ⟨ CBᴳ.injectable a b ⟩ → ⟨ CBᴳ.injectable b d ⟩
                          → ⟨ CBᴳ.injectable a d ⟩)
        -- The K5/K6 engine, abstract by design (architecture 1.7), plus O7 in
        -- its general form and K6 Track A's cut, all typed as Track E takes
        -- them so that they can be handed straight through.
        (forces   : ∀ {k} → Cond → Formula N.Nm k → Vec N.Nm k → Ω)
        (truth-at : ∀ {k} (φ : Formula N.Nm k) (ν : Vec N.Nm k)
                  → (ν A.⊨ᴱ φ) ≡ ⋁ Cond (λ r → G∈ r ⊓ forces r φ ν))
        (forces-mono : ∀ {k} (r p : Cond)
                     → ⟨ CV.refinesΔ o (cnd r) (cnd p) ⟩
                     → (φ : Formula N.Nm k) (ν : Vec N.Nm k)
                     → ⟨ forces p φ ν ⟩ → ⟨ forces r φ ν ⟩)
        (directed : (p q : Cond) → ⟨ G∈ p ⟩ → ⟨ G∈ q ⟩
                  → ⟨ ⋁ Cond (λ r → G∈ r
                    ⊓ (CV.refinesΔ o (cnd r) (cnd p)
                    ⊓ CV.refinesΔ o (cnd r) (cnd q))) ⟩)
        (forcesΔ         : ∀ {k} → Formula N.Nm k → Formula S (suc k))
        (forcesΔ-reading : ∀ {k} (φ : Formula N.Nm k) (ν : Vec N.Nm k) (r : Cond)
                         → ((cnd r ∷ NE.codesOf ν) PV.⊨ᴳ forcesΔ φ)
                           ≡ forces r φ ν)
        (mk : Separation → (bound : S) → Formula S 1 → S)
        (mk-in : (sep : Separation) (bound : S) (θ : Formula S 1) (e : S)
               → ⟨ e ∈ˢ bound ⟩ → ⟨ (e ∷ []) PV.⊨ᴳ θ ⟩ → ⟨ e ∈ˢ mk sep bound θ ⟩)
        (mk-bound : (sep : Separation) (bound : S) (θ : Formula S 1) (e : S)
                  → ⟨ e ∈ˢ mk sep bound θ ⟩ → ⟨ e ∈ˢ bound ⟩)
        (mk-sat : (sep : Separation) (bound : S) (θ : Formula S 1) (e : S)
                → ⟨ e ∈ˢ mk sep bound θ ⟩ → ⟨ (e ∷ []) PV.⊨ᴳ θ ⟩)
        -- Track E's own second residue, named there and not discharged.
        (κ             : S)
        (chkFo         : Formula S 2)
        (chkFo-reading : (u a : S) → ⟨ a ∈ˢ κ ⟩
                       → ((u ∷ a ∷ []) PV.⊨ᴳ chkFo) ≡ (u ≈ˢ fst (chk a)))
        -- K5 and K6, flat.
        (sat-cong : ∀ {k} (φ : Formula N.Nm k) (ν μ : Vec N.Nm k) → A.Agree ν μ
                  → (ν A.⊨ᴱ φ) ≡ (μ A.⊨ᴱ φ))
        (≈-refl : (m : S) → ⟨ m ≈[G] m ⟩)
        (chk-mem←     : ⟨ P.positiveᴾ ⟩ → (a b : S) → ⟨ a ∈ˢ b ⟩
                      → ⟨ chk a A.∈ᴱ chk b ⟩)
        (copy-members : ⟨ P.positiveᴾ ⟩ → (a : S) (τ : N.Nm) → ⟨ τ A.∈ᴱ chk a ⟩
                      → ⟨ ⋁ S (λ y → (y ∈ˢ a) ⊓ (fst τ ≈[G] fst (chk y))) ⟩)
        (chk-ordinal : (a : S) → ((chk a ∷ []) A.⊨ᴱ A.CBᴱ.IsOrdinalφ)
                               ≡ ((a ∷ []) NC.⊨ᴳ CBᴳ.IsOrdinalφ))
        (onto : (f a b : N.Nm) → ⟨ COᴱ.isSurjection f a b ⟩
              → (y : N.Nm) → ⟨ y A.∈ᴱ b ⟩
              → ⟨ ⋁ N.Nm (λ x → (x A.∈ᴱ a)
                   ⊓ ((x ∷ y ∷ []) A.⊨ᴱ NE.valueFo f)) ⟩)
        where

        c : S
        c = carrierᶠ

        localOrder : Cond → Cond → Ω
        localOrder r p = CV.refinesΔ o (cnd r) (cnd p)

        localOrderFo : Formula S 2
        localOrderFo = ∃̇∈ (con o)
          (CV.prAtˢ zero (suc zero) (suc (suc zero)))

        localOrderFo-reading : (r p : Cond)
          → ((cnd r ∷ cnd p ∷ []) PV.⊨ᴳ localOrderFo) ≡ localOrder r p
        localOrderFo-reading r p = refl

        -- Track E, applied for real down to the bound.

        module EV = EG.Values forces truth-at localOrder forces-mono directed
                              localOrderFo localOrderFo-reading forcesΔ forcesΔ-reading
                              mk mk-in mk-bound mk-sat
        module EB = EV.AtBound κ chkFo chkFo-reading

        -- Track F's Preserve, with Track A's four predicates, Track A's two use
        -- laws, Track B's surjection predicate and Track E's value formula all
        -- filled from the landed modules.

        module Pr = P.Preserve c o
          CV.subsetΔ CA.antichainΔ CA.maximalΔ CA.CCC₁ᴵ CA.CCC₂ᴵ
          (λ w d → CA.ccc-use c o w d) (λ w d → CA.ccc₁-use c o w d)
          injectable-trans
          forces truth-at localOrder forces-mono directed sat-cong ≈-refl
          chk chk-mem← copy-members chk-ordinal
          NE.valueFo
          COᴱ.isSurjection onto (λ f a b hs → fst hs)

        -- And Track F's bound module, with Track E's possible-value operator
        -- and its universal property, at Track E's own bound.

        module PB = Pr.AtBound κ EB.valuesOf EB.valuesOf-spec

        ----------------------------------------------------------------------
        -- 4. THE SEAM CHECKS. Each type below names the producer's export
        --    directly; a telescope that had drifted to a lookalike would not
        --    elaborate.
        ----------------------------------------------------------------------

        no-onto-at-tracks :
            PB.FamilySet → PB.ValueAntichain
          → (coll : Collection) (sep : Separation) → ⟨ P.positiveᴾ ⟩
          → (w β : S) → ⟨ β ∈ˢ κ ⟩
          → ⟨ CA.CCC₂ᴵ c o w ⟩ → ⟨ PB.ProvedRange w ⟩
          → (f : N.Nm) → ⟨ COᴱ.isSurjection f (chk β) (chk κ) ⟩ → ⟨ ⊥ ⟩
        no-onto-at-tracks = PB.no-onto

        no-collapse-at-tracks :
            PB.FamilySet → PB.ValueAntichain → PB.InverseSpread
          → (coll : Collection) (sep : Separation) → ⟨ P.positiveᴾ ⟩
          → (w : S) → ⟨ CBᴳ.isOrdinal κ ⟩
          → ⟨ CA.CCC₂ᴵ c o w ⟩ → ⟨ PB.ProvedRange w ⟩
          → ⟨ A.CBᴱ.isCardinal (chk κ) ⟩
        no-collapse-at-tracks = PB.no-collapse

        no-collapse-at-ccc₁ :
            PB.FamilySet → PB.ValueMaximalAntichain → PB.InverseSpread
          → (coll : Collection) (sep : Separation) → ⟨ P.positiveᴾ ⟩
          → (w : S) → ⟨ CBᴳ.isOrdinal κ ⟩
          → ⟨ CA.CCC₁ᴵ c o w ⟩ → ⟨ PB.ProvedRange w ⟩
          → ⟨ A.CBᴱ.isCardinal (chk κ) ⟩
        no-collapse-at-ccc₁ = PB.no-collapse-via-ccc₁

        -- The covering theorem at Track E's own set, which is the check that
        -- the two tracks agree about which ground set the argument bounds.

        covering-at-values :
            (sep : Separation) (p : Cond) → ⟨ G∈ p ⟩
          → (f : N.Nm) (β : S)
          → ⟨ Pr.spreadΩ f β κ ⟩
          → (a : S) → ⟨ a ∈ˢ κ ⟩
          → ⟨ ⋁ S (λ ξ → (ξ ∈ˢ β) ⊓ (a ∈ˢ EB.valuesOf sep p f ξ)) ⟩
        covering-at-values = PB.covering

        outside-local-values : (sep : Separation) (p : Cond) (f : N.Nm) (ξ a : S)
          → ((r : Cond) → ⟨ localOrder r p ⟩
            → ⟨ forces r (NE.valueFo f) (chk ξ ∷ chk a ∷ []) ⟩ → Empty.⊥)
          → ⟨ a ∈ˢ EB.valuesOf sep p f ξ ⟩ → Empty.⊥
        outside-local-values sep p f ξ a excluded member =
          PT.rec Empty.isProp⊥ (λ { (r , hrp , forced) → excluded r hrp forced })
            (snd (subst ⟨_⟩ (EB.valuesOf-spec sep p f ξ a) member))

        countable-at-forced-function : PB.ValueAntichain → Collection
          → (w : S) → ⟨ CA.CCC₂ᴵ c o w ⟩
          → (sep : Separation) (p : Cond) (f : N.Nm)
          → ⟨ forces p A.CBᴱ.IsFunctionφ (f ∷ []) ⟩
          → (ξ : S) → ⟨ CBᴳ.injectable (EB.valuesOf sep p f ξ) w ⟩
        countable-at-forced-function = PB.countable-from-ccc₂

        module WithImages
          (families : NameKernel.Families 𝒮)
          (images : NameKernel.MemberImage 𝒮)
          (pow : OP.PowerSet) (find : OP.FoundationInduction)
          (choice : OP.ChoiceSet) (seed : S)
          where

          private module Families = K7.ValueFamilies 𝒮 families images pow find choice seed

          family-set : PB.FamilySet
          family-set sep p f β =
            Families.AtFamily.family-witness β (λ ξ → EB.valuesOf sep p f ξ)

        module WithDefinableFamilies
          (pair : OP.Pairing) (un : OP.Union) (pow : OP.PowerSet)
          (coll : OP.Collection) (find : OP.FoundationInduction)
          (choice : OP.ChoiceSet) (seed : S)
          (checks : S → Formula S 2)
          (checks-reading : (β u ξ : S) → ⟨ ξ ∈ˢ β ⟩
            → ((u ∷ ξ ∷ []) PV.⊨ᴳ checks β) ≡ (u ≈ˢ fst (chk ξ)))
          where

          family-set : PB.FamilySet
          family-set sep p f β = Cuts.family-witness
            where
            module Cuts = K7.CheckIndexedFamilies.AtCuts 𝒮 ext paths pair un pow sep
              coll find choice seed β κ c (cnd p) (λ ξ → fst (chk ξ))
              (checks β) (checks-reading β) (EB.valueBody f)
              (mk sep) (mk-in sep) (mk-bound sep) (mk-sat sep)
              using ( family-witness )

        memLᴱ : (x y z : N.Nm) → ⟨ x A.≈ᴱ y ⟩
          → (x A.∈ᴱ z) ≡ (y A.∈ᴱ z)
        memLᴱ x y z e = sat-cong (var zero ∈̇ var (suc zero))
          (x ∷ z ∷ []) (y ∷ z ∷ []) agree
          where
          agree : A.Agree (x ∷ z ∷ []) (y ∷ z ∷ [])
          agree zero = e
          agree (suc zero) = ≈-refl (fst z)

        memRᴱ : (x y z : N.Nm) → ⟨ y A.≈ᴱ z ⟩
          → (x A.∈ᴱ y) ≡ (x A.∈ᴱ z)
        memRᴱ x y z e = sat-cong (var zero ∈̇ var (suc zero))
          (x ∷ y ∷ []) (x ∷ z ∷ []) agree
          where
          agree : A.Agree (x ∷ y ∷ []) (x ∷ z ∷ [])
          agree zero = ≈-refl (fst x)
          agree (suc zero) = e

        module WithInverse
          (extE : OrdinaryProfile.Extensionality A.𝒮ᴱ)
          (pairE : OrdinaryProfile.Pairing A.𝒮ᴱ)
          (sepE : OrdinaryProfile.Separation A.𝒮ᴱ)
          (collE : OrdinaryProfile.Collection A.𝒮ᴱ)
          (lem : LEM ℓ) (u : N.Nm) (hu : ⟨ u A.∈ᴱ chk κ ⟩)
          where

          private module Inverse = K7.InverseSurjection A.𝒮ᴱ extE memLᴱ memRᴱ

          inverse-spread : PB.InverseSpread
          inverse-spread y hy hinj = Inverse.injectable-surjectable
            lem pairE sepE collE (chk κ) (chk y) u hu hinj

        module AtCountableBound
          (pair : OP.Pairing) (un : OP.Union) (pow : OP.PowerSet)
          (sep : OP.Separation) (coll : OP.Collection) (find : OP.FoundationInduction)
          (lem : LEM ℓ) (choice : OP.ChoiceSet)
          (w : S) (hw : ⟨ CBᴳ.isOmega w ⟩)
          (hκ : ⟨ CBᴳ.isCardinal κ ⟩) (hwκ : ⟨ w ∈ˢ κ ⟩)
          (members-countable : (β : S) → ⟨ β ∈ˢ κ ⟩ → ⟨ CBᴳ.injectable β w ⟩)
          where

          private
            module Cover = K7.CountableCover 𝒮 ext paths pair un pow sep coll find
              lem choice w hw κ hκ hwκ members-countable
              using ( proved-range )

          countable-cover : ⟨ PB.ProvedRange w ⟩
          countable-cover = Cover.proved-range

        module AtLargerBound
          (pair : OP.Pairing) (un : OP.Union) (pow : OP.PowerSet)
          (sep : OP.Separation) (coll : OP.Collection) (find : OP.FoundationInduction)
          (choice : OP.ChoiceSet) (w d : S)
          (hκ : ⟨ CBᴳ.isCardinal κ ⟩) (hdκ : ⟨ d ∈ˢ κ ⟩)
          (wd : ⟨ CBᴳ.injectable w d ⟩)
          (below : (β : S) → ⟨ β ∈ˢ κ ⟩ → ⟨ CBᴳ.injectable β d ⟩)
          where

          private
            module Product = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep w
              using ( product )
            module Cover = K7.UncountableCover 𝒮 ext paths pair un pow sep coll find
              choice w using ( proved-range )

          squareBound : Ω
          squareBound = CBᴳ.injectable (Product.product d d) d

          larger-cover : ⟨ squareBound ⟩
            → ⟨ PB.ProvedRange w ⟩
          larger-cover = Cover.proved-range d κ hκ hdκ wd below

        module WithAntichains
          (checkedEq : Cond → S → S → Ω)
          (function-values : (r : Cond) (f : N.Nm) (ξ a b : S)
            → ⟨ forces r A.CBᴱ.IsFunctionφ (f ∷ []) ⟩
            → ⟨ forces r (NE.valueFo f) (chk ξ ∷ chk a ∷ []) ⟩
            → ⟨ forces r (NE.valueFo f) (chk ξ ∷ chk b ∷ []) ⟩
            → ⟨ checkedEq r a b ⟩)
          (checked-reflect : (r : Cond) (a b : S)
            → ⟨ checkedEq r a b ⟩ → ⟨ a ≈ˢ b ⟩)
          (order-refl : (r : Cond) → ⟨ localOrder r r ⟩)
          (order-trans : (r q p : Cond) → ⟨ localOrder r q ⟩
            → ⟨ localOrder q p ⟩ → ⟨ localOrder r p ⟩)
          (pair : OP.Pairing) (un : OP.Union) (pow : OP.PowerSet)
          (coll : OP.Collection) (find : OP.FoundationInduction)
          (seed : S) (lem : LEM ℓ) (choice : OP.ChoiceSet)
          where

          private
            module Local = K7.LocalValueAntichain.Names.AtG 𝒮 ext paths IsNm
              c o Cond cnd cnd-carrier cndOf cnd-cndOf G∈ _≈[G]_ _∈[G]_ chk
            module LocalForcing = Local.Forcing forces truth-at forces-mono directed
              forcesΔ forcesΔ-reading mk mk-in mk-bound mk-sat
            module Bound = LocalForcing.AtBound κ chkFo chkFo-reading
            module Consequence = Bound.Consequence checkedEq function-values
              checked-reflect order-refl order-trans
            module Selection = Consequence.GroundChoice pair un pow coll find seed lem choice

          local-value-antichain : PB.ValueAntichain
          local-value-antichain = Selection.value-antichain

          countable-local-values : (w : S) → ⟨ CA.CCC₂ᴵ c o w ⟩
            → (sep : Separation) (p : Cond) (f : N.Nm)
            → ⟨ forces p A.CBᴱ.IsFunctionφ (f ∷ []) ⟩
            → (ξ : S) → ⟨ CBᴳ.injectable (EB.valuesOf sep p f ξ) w ⟩
          countable-local-values = PB.countable-from-ccc₂ local-value-antichain coll

          module WithFamilySet
            (family-set : PB.FamilySet)
            where

            no-surjection : (sep : Separation) → ⟨ P.positiveᴾ ⟩
              → (w β : S) → ⟨ β ∈ˢ κ ⟩ → ⟨ CA.CCC₂ᴵ c o w ⟩
              → ⟨ PB.ProvedRange w ⟩ → (f : N.Nm)
              → ⟨ COᴱ.isSurjection f (chk β) (chk κ) ⟩ → ⟨ ⊥ ⟩
            no-surjection = PB.no-onto family-set local-value-antichain coll

            module AtCountableCardinal
              (sep : Separation) (w : S) (hw : ⟨ CBᴳ.isOmega w ⟩)
              (hκ : ⟨ CBᴳ.isCardinal κ ⟩) (hwκ : ⟨ w ∈ˢ κ ⟩)
              (members-countable : (β : S) → ⟨ β ∈ˢ κ ⟩
                → ⟨ CBᴳ.injectable β w ⟩)
              (extE : OrdinaryProfile.Extensionality A.𝒮ᴱ)
              (pairE : OrdinaryProfile.Pairing A.𝒮ᴱ)
              (sepE : OrdinaryProfile.Separation A.𝒮ᴱ)
              (collE : OrdinaryProfile.Collection A.𝒮ᴱ)
              (u : N.Nm) (hu : ⟨ u A.∈ᴱ chk κ ⟩)
              where

              private
                module Cover = AtCountableBound pair un pow sep coll find lem choice
                  w hw hκ hwκ members-countable
                  using ( countable-cover )
                module Inverse = WithInverse extE pairE sepE collE lem u hu
                  using ( inverse-spread )

              preserved-cardinal : ⟨ P.positiveᴾ ⟩ → ⟨ CA.CCC₂ᴵ c o w ⟩
                → ⟨ A.CBᴱ.isCardinal (chk κ) ⟩
              preserved-cardinal positive ccc = PB.no-collapse
                family-set local-value-antichain Inverse.inverse-spread
                coll sep positive w (hκ .fst) ccc Cover.countable-cover

            module AtLargerCardinal
              (sep : Separation) (w d : S)
              (hκ : ⟨ CBᴳ.isCardinal κ ⟩) (hdκ : ⟨ d ∈ˢ κ ⟩)
              (wd : ⟨ CBᴳ.injectable w d ⟩)
              (below : (β : S) → ⟨ β ∈ˢ κ ⟩ → ⟨ CBᴳ.injectable β d ⟩)
              (extE : OrdinaryProfile.Extensionality A.𝒮ᴱ)
              (pairE : OrdinaryProfile.Pairing A.𝒮ᴱ)
              (sepE : OrdinaryProfile.Separation A.𝒮ᴱ)
              (collE : OrdinaryProfile.Collection A.𝒮ᴱ)
              (u : N.Nm) (hu : ⟨ u A.∈ᴱ chk κ ⟩)
              where

              private
                module Cover = AtLargerBound pair un pow sep coll find choice w d
                  hκ hdκ wd below using ( squareBound; larger-cover )
                module Inverse = WithInverse extE pairE sepE collE lem u hu
                  using ( inverse-spread )

              squareBound : Ω
              squareBound = Cover.squareBound

              preserved-cardinal :
                ⟨ squareBound ⟩
                → ⟨ P.positiveᴾ ⟩ → ⟨ CA.CCC₂ᴵ c o w ⟩
                → ⟨ A.CBᴱ.isCardinal (chk κ) ⟩
              preserved-cardinal square positive ccc = PB.no-collapse
                family-set local-value-antichain Inverse.inverse-spread
                coll sep positive w (hκ .fst) ccc (Cover.larger-cover square)

          module WithFamilies
            (families : NameKernel.Families 𝒮)
            (images : NameKernel.MemberImage 𝒮)
            where

            private
              module Family = WithImages families images pow find choice seed
                using ( family-set )
            module Preservation = WithFamilySet Family.family-set
              using ( no-surjection; module AtCountableCardinal; module AtLargerCardinal )
            open Preservation public
              using ( no-surjection; module AtCountableCardinal; module AtLargerCardinal )

          module WithDefinedFamilies
            (checks : S → Formula S 2)
            (checks-reading : (β u ξ : S) → ⟨ ξ ∈ˢ β ⟩
              → ((u ∷ ξ ∷ []) PV.⊨ᴳ checks β) ≡ (u ≈ˢ fst (chk ξ)))
            where

            private
              module Family = WithDefinableFamilies pair un pow coll find choice seed
                checks checks-reading
                using ( family-set )
            module Preservation = WithFamilySet Family.family-set
              using ( no-surjection; module AtCountableCardinal; module AtLargerCardinal )
            open Preservation public
              using ( no-surjection; module AtCountableCardinal; module AtLargerCardinal )

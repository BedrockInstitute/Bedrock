{-# OPTIONS --cubical --safe --guardedness #-}

-- K7 TRACK E. THE POSSIBLE VALUES OF A NAME AT ONE COORDINATE, BOUNDED IN THE
-- GROUND.
--
-- WHAT IS PROVED HERE. Fix a condition p, a name f, a ground coordinate ξ,
-- and a ground bound β. The ground objects a for which some refinement of p
-- forces "f at ξ is the check of a" meet β in a GROUND SET. If p belongs to
-- G, that set contains every value the extension actually takes at ξ inside
-- β. The set is one instance of ground Separation applied to a named Formula
-- S 1 and to β, so it is a subset of β by construction. The covering
-- direction uses the truth lemma, directedness of G, and forcing monotonicity.
--
-- WHY THIS IS THE SHAPE THE PRESERVATION THEOREM WANTS. Track F counts. It
-- needs, for each coordinate, a set of GROUND objects among which the value
-- must lie, because the union of those sets over a ground index set is again a
-- ground set and its ground cardinality is what contradicts surjectivity onto
-- κ. A bound consisting of NAMES does not do that work: distinct names need
-- not be forced distinct, and the map from a name to the ground ordinal it
-- evaluates to depends on G and is not ground definable. That asymmetry is
-- what puts the check map inside the Separation formula, and section (D)
-- below is the whole of its price.
--
-- THE FIVE INGREDIENTS THIS FILE STANDS ON, AND NOTHING ELSE IS CONDITIONAL.
--
--   (1) forcesΔ and forcesΔ-reading. O7, THE GENERAL DEFINABILITY LEMMA, in
--       its landed general form: for each FIXED object formula the forcing
--       relation is one ground formula whose slots are the condition code
--       first and the name codes after. O7/Definability.agda:97-99 declares
--       exactly this pair, and O7/Supply.agda module Chain (:209-242) proves
--       that it follows from ONE residue, valΔ, together with K5's below pair
--       and K6's forced set. This file does NOT take a fourth projection: it
--       takes the general datum, and K7/ValuesAtNames.agda applies Chain to it
--       so that the residue on the page is valΔ alone.
--   (2) mk, mk-in, mk-bound, mk-sat. K6 Track A's Separation cut at a caller
--       supplied bound, K6/NameBuild.agda:348, :355, :359 and :363, with the
--       opaque specification they project at :351.
--   (3) forces and truth-at, ABSTRACT, in the shape K6/Separation.agda:276-279
--       takes them, together with forcing monotonicity and directedness of G.
--       No engine, no K6.ForcesTruth, no K5.Truth.
--   (4) A Formula S 2 defining refinement on condition codes, with its
--       reading theorem. This keeps the cut an object-language Separation.
--   (5) The internal graph of the check map ON β. This is a SECOND residue and
--       this file says so rather than hiding it; see the header of module
--       AtBound and the report row beside it.
--
-- WHAT IS NOT HERE. No chain condition, no antichain, no cardinal and no
-- counting: this file supplies the ground set, Track F does the counting. No
-- selection of any kind is made anywhere below, so neither of the two ledger
-- protections of Part 0d is relied on.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax
  using ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; ∃̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import FOL.Manipulation.ConstantMapping using ( embed )
open import FOL.Manipulation.ParameterAbstraction using ( absFo )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
import FOL.Semantics
import OrdinaryProfile
import CodedVocabulary
import CardinalBridge
import O7.Definability
import Cubical.HITs.PropositionalTruncation as PT

open PT using ( ∣_∣₁ )

module K7.PossibleValues
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

-- Ground Separation, as a standalone argument of the declarations that spend
-- it and never as a module parameter and never as the OrdinaryZF record, which
-- is ruling D4. Ground Collection is NOT here: see the report's rule 13 row.

open OrdinaryProfile 𝒮 using ( Separation )

-- Ground satisfaction, the instance Track A's cut reads its formula in:
-- FOL.Semantics at the GROUND structure with the ground sets as their own
-- constants, the same instance CodedVocabulary.agda:57 and
-- K6/Separation.agda:148-149 take.

private module SemG = FOL.Semantics (hPropAlgebra ℓ) 𝒮
module SatG = SemG.At S id
open SatG public using () renaming ( _⊨_ to _⊨ᴳ_ )

open Sat (hPropAlgebra ℓ) 𝒮 {K = S} id using ( Agrees; ⊨-rename )

open CodedVocabulary 𝒮
  using ( isKPairΔ; prAtˢ; sepAt; sepAt-reading; subsetΔ )

-- O7's OWN name type and OWN slot layout, opened rather than re-spelled. A
-- second `codesOf` defined here would be a different stuck function and the
-- O7 reading theorem could not be filled by O7's export at all; rule 9's
-- generativity applies to a recursive definition exactly as it applies to a
-- record. Nothing else of O7/Definability.agda is used: none of the three
-- projections is imported, because this track takes the GENERAL datum.

module O7D = O7.Definability 𝒮
private module Cardinal = CardinalBridge 𝒮

-- The two directions of `paths`, spelled once. Nothing below uses ground
-- Extensionality: the identification of ≈ˢ with a path is the spine's own
-- parameter and is not an axiom of the profile.

≈ˢ→≡ : {x y : S} → ⟨ x ≈ˢ y ⟩ → x ≡ y
≈ˢ→≡ {x} {y} = subst ⟨_⟩ (paths x y)

≡→≈ˢ : {x y : S} → x ≡ y → ⟨ x ≈ˢ y ⟩
≡→≈ˢ {x} {y} = subst ⟨_⟩ (sym (paths x y))

--------------------------------------------------------------------------------
-- (A) The object language pair vocabulary, at an arbitrary constant domain
--------------------------------------------------------------------------------

-- CodedVocabulary's sglAtˢ (:67-68), pairAtˢ (:82-86) and prAtˢ (:112-116) are
-- the ground instances of three formulas that use no constant at all: every
-- argument position is a Fin n. They are nonetheless typed at Formula S n and
-- so cannot be applied at Formula Nm n, which is the language the forcing
-- relation reads. The three below are the same formulas at an arbitrary K, and
-- the ground instance of each is definitionally CodedVocabulary's.

sglFo : ∀ {ℓc} {K : Type ℓc} {n} → Fin n → Fin n → Formula K n
sglFo w u = (var u ∈̇ var w) ∧̇ (∀̇∈ (var w) (var zero ≐ var (suc u)))

pairFo : ∀ {ℓc} {K : Type ℓc} {n} → Fin n → Fin n → Fin n → Formula K n
pairFo w u v =
    (var u ∈̇ var w)
  ∧̇ ((var v ∈̇ var w)
  ∧̇ (∀̇∈ (var w) ((var zero ≐ var (suc u)) ∨̇ (var zero ≐ var (suc v)))))

kprFo : ∀ {ℓc} {K : Type ℓc} {n} → Fin n → Fin n → Fin n → Formula K n
kprFo q u v =
    (∃̇∈ (var q) (sglFo zero (suc u)))
  ∧̇ ((∃̇∈ (var q) (pairFo zero (suc u) (suc v)))
  ∧̇ (∀̇∈ (var q) (sglFo zero (suc u) ∨̇ pairFo zero (suc u) (suc v))))

-- The ground instance really is the vocabulary the rest of the tree reads, so
-- that a reader may check the transcription rather than trust it.

kprFo-isPrAt : ∀ {n} (q u v : Fin n) → kprFo {K = S} q u v ≡ prAtˢ q u v
kprFo-isPrAt q u v = refl

--------------------------------------------------------------------------------
-- (B) The names, and the formula that says "the second slot is f's value at
--     the first"
--------------------------------------------------------------------------------

module Names (IsNm : S → Ω) where

  -- The name type is O7's, which is the Sigma K5/Structures.agda:263-264
  -- writes and K6/Separation.agda:173-174 re-spells; a Sigma is not
  -- generative, so the three agree definitionally, and K7/ValuesAtNames.agda
  -- checks that against the landed K5 one by refl. `codesOf` is the layout O7
  -- reads its slots in, condition code first and name codes after
  -- (O7/Definability.agda:74-76), and it is OPENED and not copied.

  open O7D.Names IsNm public using ( Nm; codesOf )

  isSetNm : isSet Nm
  isSetNm = isSetΣSndProp isSetS (λ n → snd (IsNm n))

  -- THE OBJECT FORMULA. Two free slots, the coordinate and the value, and one
  -- constant, the name f. It says that the Kuratowski pair of the two slots is
  -- a member of f, which for a name forced to be a function is exactly "the
  -- second slot is f's value at the first". It is stated with two free
  -- variables and not as a family of closed formulas on purpose: O7 gives ONE
  -- ground formula per object formula, so a family indexed by the value would
  -- give a family of ground formulas and no Separation could follow it.

  positiveValueFo : Nm → Formula Nm 2
  positiveValueFo f = ∃̇ (kprFo zero (suc zero) (suc (suc zero)) ∧̇ (var zero ∈̇ con f))

  -- Use exactly the pair predicate appearing in IsFunctionφ. The former
  -- positive presentation is retained above; FunctionalValues proves their
  -- agreement under Extensionality and Pairing.
  valueFo : Nm → Formula Nm 2
  valueFo f = ∃̇ (embed (absFo {ℓz = ℓ} Cardinal.PairφK) ∧̇ (var zero ∈̇ con f))

------------------------------------------------------------------------------
-- (C) The extension side, flat, and the reading of valueFo in it
------------------------------------------------------------------------------

  -- The spine of K6/Ordinals.agda:126-141, which is the cheapest in the tree:
  -- the value relation arrives as two variables, the structure is a record
  -- LITERAL with the four fields K5/Structures.agda:285-291 gives it, and
  -- satisfaction at Formula Nm k is FOL.Semantics at that literal. At the
  -- landed instance the literal is definitionally K5's structure, which
  -- K7/ValuesAtNames.agda checks by refl.

  module AtG
    (carrierᶠ      : S)
    (Cond          : Type ℓ)
    (cnd           : Cond → S)
    (cnd-carrier   : (r : Cond) → ⟨ cnd r ∈ˢ carrierᶠ ⟩)
    -- The condition rebuilt from its code, K6/Replacement.agda:249 and the
    -- note at :128-130: at the instance Cond is a plain Σ, cndOf q hq is
    -- (q , hq) and cnd-cndOf is refl by the eta law. This is the direction
    -- O7/Definability.agda:278 takes, and it is the direction a BOUNDED
    -- ground existential over the carrier needs.
    (cndOf         : (q : S) → ⟨ q ∈ˢ carrierᶠ ⟩ → Cond)
    (cnd-cndOf     : (q : S) (hq : ⟨ q ∈ˢ carrierᶠ ⟩) → cnd (cndOf q hq) ≡ q)
    (G∈            : Cond → Ω)
    (_≈[G]_ _∈[G]_ : S → S → Ω)
    -- The check map, K5/Structures.agda:588-589, where it is groundName.
    (chk           : S → Nm)
    where

    𝒮ᴱ : ZFStructure (hPropAlgebra ℓ)
    𝒮ᴱ = record
      { S      = Nm
      ; isSetS = isSetNm
      ; _≈ˢ_   = λ σ τ → fst σ ≈[G] fst τ
      ; _∈ˢ_   = λ σ τ → fst σ ∈[G] fst τ }

    private module SemE = FOL.Semantics (hPropAlgebra ℓ) 𝒮ᴱ
    private module CardinalE = CardinalBridge 𝒮ᴱ
    module SatE = SemE.At Nm id
    open SatE public using ( _⊨_ )

    -- What valueFo means at the extension, so that the formula is checked and
    -- not merely asserted. Rule 6: a uniform depth formula gets its protection
    -- from its reading theorem and from nowhere else.

    isSglᴱ : Nm → Nm → Ω
    isSglᴱ w u =
      (fst u ∈[G] fst w) ⊓ (⋀ Nm (λ x → (fst x ∈[G] fst w) ⇒ (fst x ≈[G] fst u)))

    isPairᴱ : Nm → Nm → Nm → Ω
    isPairᴱ w u v =
        (fst u ∈[G] fst w)
      ⊓ ((fst v ∈[G] fst w)
      ⊓ (⋀ Nm (λ x → (fst x ∈[G] fst w)
             ⇒ ((fst x ≈[G] fst u) ⊔ (fst x ≈[G] fst v)))))

    isKPairᴱ : Nm → Nm → Nm → Ω
    isKPairᴱ q u v =
        (⋁ Nm (λ w → (fst w ∈[G] fst q) ⊓ isSglᴱ w u))
      ⊓ ((⋁ Nm (λ w → (fst w ∈[G] fst q) ⊓ isPairᴱ w u v))
      ⊓ (⋀ Nm (λ w → (fst w ∈[G] fst q) ⇒ (isSglᴱ w u ⊔ isPairᴱ w u v))))

    valueFo-reading : (f σ τ : Nm)
                    → ((σ ∷ τ ∷ []) ⊨ valueFo f)
                      ≡ ⋁ Nm (λ π → CardinalE.isKPair π σ τ ⊓ (fst π ∈[G] fst f))
    valueFo-reading f σ τ = refl

    positiveValueFo-reading : (f σ τ : Nm)
      → ((σ ∷ τ ∷ []) ⊨ positiveValueFo f)
        ≡ ⋁ Nm (λ π → isKPairᴱ π σ τ ⊓ (fst π ∈[G] fst f))
    positiveValueFo-reading f σ τ = refl

------------------------------------------------------------------------------
-- (D) The bound
------------------------------------------------------------------------------

    -- The telescope is the ledger, and it is read top to bottom. The abstract
    -- forcing and filter laws, the ground definition of refinement, the
    -- general O7 datum, and four exports of K6 Track A are each typed from the
    -- landed source. Nothing else.

    module Values
      -- K6/Separation.agda:276-279, verbatim. Never applied here.
      (forces   : ∀ {k} → Cond → Formula Nm k → Vec Nm k → Ω)
      (truth-at : ∀ {k} (φ : Formula Nm k) (ν : Vec Nm k)
                → (ν ⊨ φ) ≡ ⋁ Cond (λ r → G∈ r ⊓ forces r φ ν))
      (order : Cond → Cond → Ω)
      (forces-mono : ∀ {k} (r p : Cond) → ⟨ order r p ⟩
                   → (φ : Formula Nm k) (ν : Vec Nm k)
                   → ⟨ forces p φ ν ⟩ → ⟨ forces r φ ν ⟩)
      (directed : (p q : Cond) → ⟨ G∈ p ⟩ → ⟨ G∈ q ⟩
                → ⟨ ⋁ Cond (λ r → G∈ r ⊓ (order r p ⊓ order r q)) ⟩)
      (orderFo         : Formula S 2)
      (orderFo-reading : (r p : Cond)
                       → ((cnd r ∷ cnd p ∷ []) ⊨ᴳ orderFo) ≡ order r p)
      -- O7 IN ITS GENERAL FORM, and this pair is the WHOLE of the forcing
      -- side. O7/Definability.agda:97-99, and O7/Supply.agda:238-242 builds
      -- it from the one residue valΔ together with K5's CodeOfBelow and
      -- BelowOfCode (K5/Dense.agda:579-584, discharged at
      -- K5/InstanceBase.agda:361 and :364) and K6's forced set
      -- (K6/ForcesTruth.agda:337-348), which is FREE because `below` is a
      -- ForcingBase field (K5/Frame.agda:198) and no Separation is spent on
      -- it. This track adds NO fourth projection.
      (forcesΔ         : ∀ {k} → Formula Nm k → Formula S (suc k))
      (forcesΔ-reading : ∀ {k} (φ : Formula Nm k) (ν : Vec Nm k) (r : Cond)
                       → ((cnd r ∷ codesOf ν) ⊨ᴳ forcesΔ φ) ≡ forces r φ ν)
      -- K6 Track A's cut, K6/NameBuild.agda:348, :355, :359 and :363, sealed at its
      -- point of definition in its own opaque block. Rule 2 has no target in
      -- this file: mk is a variable of this telescope and a parameter is
      -- maximally stuck, which is rule 2b's K6 refinement.
      (mk : Separation → (bound : S) → Formula S 1 → S)
      (mk-in : (sep : Separation) (bound : S) (θ : Formula S 1) (e : S)
             → ⟨ e ∈ˢ bound ⟩ → ⟨ (e ∷ []) ⊨ᴳ θ ⟩ → ⟨ e ∈ˢ mk sep bound θ ⟩)
      (mk-bound : (sep : Separation) (bound : S) (θ : Formula S 1) (e : S)
                → ⟨ e ∈ˢ mk sep bound θ ⟩ → ⟨ e ∈ˢ bound ⟩)
      (mk-sat : (sep : Separation) (bound : S) (θ : Formula S 1) (e : S)
              → ⟨ e ∈ˢ mk sep bound θ ⟩ → ⟨ (e ∷ []) ⊨ᴳ θ ⟩)
      where

      -- THE SECOND RESIDUE, NAMED. The Separation formula must recover, from
      -- the ground variable a, the CODE of the check name of a, because that
      -- is the slot O7's reading exposes. Below β this is one Formula S 2 and
      -- one reading theorem, and module FromTable builds both from a ground
      -- set. It is class (ii): at a genuine forcing extension the check map is
      -- a ∈ recursion and is ground definable, and its restriction to a set is
      -- a set by ground Replacement; the tree has no internal recursion
      -- machine, which is the same gap NameImage.agda:395-400 records for the
      -- check name itself: "no tier of section 1.2 produces a fixed point".
      --
      -- It is NOT discharged by O7. O7 makes the forcing relation definable at
      -- FIXED name codes; the coordinate by coordinate bound needs it at a
      -- code that VARIES with a ground set, and no renaming of forcesΔ reaches
      -- that. The architecture's 4.5 sketch hid this inside a would be fourth
      -- projection whose stated reading is ill formed; see the report.

      module AtBound
        (β             : S)
        (chkFo         : Formula S 2)
        (chkFo-reading : (u a : S) → ⟨ a ∈ˢ β ⟩
                       → ((u ∷ a ∷ []) ⊨ᴳ chkFo) ≡ (u ≈ˢ fst (chk a)))
        where

        -- The three insertions place the check graph, refinement relation and
        -- O7 forcing formula into the six-slot context opened by the two
        -- quantifiers. Every agreement is refl because no slot moves under a
        -- binder.
        --
        -- The six slot context, once, so that all three tables can be read
        -- against it: 0 is the witnessed code u, 1 is the condition code q,
        -- 2 is the candidate value a, 3 is the code of the check name of the
        -- coordinate, 4 is the carrier of the conditions, and 5 is the code
        -- of the fixed condition p.

        ρC : Fin 2 → Fin 6
        ρC zero       = zero
        ρC (suc zero) = suc (suc zero)

        ρC-ag : (u q a c d p : S)
              → Agrees ρC (u ∷ q ∷ a ∷ c ∷ d ∷ p ∷ []) (u ∷ a ∷ [])
        ρC-ag u q a c d p zero       = refl
        ρC-ag u q a c d p (suc zero) = refl

        ρV : Fin 3 → Fin 6
        ρV zero             = suc zero
        ρV (suc zero)       = suc (suc (suc zero))
        ρV (suc (suc zero)) = zero

        ρV-ag : (u q a c d p : S)
              → Agrees ρV (u ∷ q ∷ a ∷ c ∷ d ∷ p ∷ []) (q ∷ c ∷ u ∷ [])
        ρV-ag u q a c d p zero             = refl
        ρV-ag u q a c d p (suc zero)       = refl
        ρV-ag u q a c d p (suc (suc zero)) = refl

        ρO : Fin 2 → Fin 6
        ρO zero       = suc zero
        ρO (suc zero) = suc (suc (suc (suc (suc zero))))

        ρO-ag : (u q a c d p : S)
              → Agrees ρO (u ∷ q ∷ a ∷ c ∷ d ∷ p ∷ []) (q ∷ p ∷ [])
        ρO-ag u q a c d p zero       = refl
        ρO-ag u q a c d p (suc zero) = refl

        -- The formula, with four slots still open so that sepAt can freeze the
        -- three parameters of the call. Reading it: some condition code q in
        -- the carrier, and some u, such that u is the code of the check name
        -- of the candidate a, q refines p, and q forces the value formula at
        -- the coordinate's check code and at u.

        valueBody : (f : Nm) → Formula S 4
        valueBody f =
          ∃̇∈ (var (suc (suc zero)))
            (∃̇ (renameFo ρC chkFo
              ∧̇ (renameFo ρO orderFo ∧̇ renameFo ρV (forcesΔ (valueFo f)))))

        -- THE SEPARATION FORMULA, named, as the reviewer test asks. Every
        -- ground set this file produces is `mk sep β (valuesFo p f ξ)` and
        -- this is the formula it is cut by.

        valuesFo : (p : Cond) (f : Nm) (ξ : S) → Formula S 1
        valuesFo p f ξ =
          sepAt (valueBody f) (fst (chk ξ) ∷ carrierᶠ ∷ cnd p ∷ [])

        -- THE READING, in one path, and it is the theorem the Separation cut
        -- inherits. Both directions need a ∈ β, because the check graph is
        -- only claimed there; the cut conjoins a ∈ β anyway, so nothing is
        -- lost.

        valuesFo-reading
          : (p : Cond) (f : Nm) (ξ a : S) → ⟨ a ∈ˢ β ⟩
          → ((a ∷ []) ⊨ᴳ valuesFo p f ξ)
            ≡ ⋁ Cond (λ r → order r p
                ⊓ forces r (valueFo f) (chk ξ ∷ chk a ∷ []))
        valuesFo-reading p f ξ a ha =
            sepAt-reading (valueBody f)
              (fst (chk ξ) ∷ carrierᶠ ∷ cnd p ∷ []) a
          ∙ ⇔toPath to from
          where
            cξ : S
            cξ = fst (chk ξ)

            Tgt : Ω
            Tgt = ⋁ Cond (λ r → order r p
                ⊓ forces r (valueFo f) (chk ξ ∷ chk a ∷ []))

            -- One witness of the inner existential, unpacked. The check graph
            -- pins u to the code of the check name of a, the condition code is
            -- rebuilt into a condition, and O7's reading turns the ground
            -- satisfaction into the forcing fact.

            inner : (q : S) → ⟨ q ∈ˢ carrierᶠ ⟩
                  → Σ[ u ∈ S ] (⟨ (u ∷ q ∷ a ∷ cξ ∷ carrierᶠ ∷ cnd p ∷ [])
                                    ⊨ᴳ renameFo ρC chkFo ⟩
                                × (⟨ (u ∷ q ∷ a ∷ cξ ∷ carrierᶠ ∷ cnd p ∷ [])
                                    ⊨ᴳ renameFo ρO orderFo ⟩
                                × ⟨ (u ∷ q ∷ a ∷ cξ ∷ carrierᶠ ∷ cnd p ∷ [])
                                    ⊨ᴳ renameFo ρV (forcesΔ (valueFo f)) ⟩))
                  → ⟨ Tgt ⟩
            inner q hq (u , hc , ho , hv) =
              ∣ cndOf q hq , refined , forced ∣₁
              where
                uIs : u ≡ fst (chk a)
                uIs = ≈ˢ→≡ (subst ⟨_⟩
                  (⊨-rename ρC chkFo
                     (u ∷ q ∷ a ∷ cξ ∷ carrierᶠ ∷ cnd p ∷ []) (u ∷ a ∷ [])
                     (ρC-ag u q a cξ carrierᶠ (cnd p))
                   ∙ chkFo-reading u a ha) hc)

                atOrder : ⟨ (q ∷ cnd p ∷ []) ⊨ᴳ orderFo ⟩
                atOrder = subst ⟨_⟩
                  (⊨-rename ρO orderFo
                    (u ∷ q ∷ a ∷ cξ ∷ carrierᶠ ∷ cnd p ∷ [])
                    (q ∷ cnd p ∷ [])
                    (ρO-ag u q a cξ carrierᶠ (cnd p))) ho

                refined : ⟨ order (cndOf q hq) p ⟩
                refined = subst ⟨_⟩ (orderFo-reading (cndOf q hq) p)
                  (subst (λ w → ⟨ (w ∷ cnd p ∷ []) ⊨ᴳ orderFo ⟩)
                    (sym (cnd-cndOf q hq)) atOrder)

                atSlots : ⟨ (q ∷ cξ ∷ u ∷ []) ⊨ᴳ forcesΔ (valueFo f) ⟩
                atSlots = subst ⟨_⟩
                  (⊨-rename ρV (forcesΔ (valueFo f))
                     (u ∷ q ∷ a ∷ cξ ∷ carrierᶠ ∷ cnd p ∷ []) (q ∷ cξ ∷ u ∷ [])
                     (ρV-ag u q a cξ carrierᶠ (cnd p))) hv

                moved : ⟨ (cnd (cndOf q hq) ∷ cξ ∷ fst (chk a) ∷ [])
                            ⊨ᴳ forcesΔ (valueFo f) ⟩
                moved = subst
                  (λ w → ⟨ (w ∷ cξ ∷ fst (chk a) ∷ []) ⊨ᴳ forcesΔ (valueFo f) ⟩)
                  (sym (cnd-cndOf q hq))
                  (subst
                    (λ w → ⟨ (q ∷ cξ ∷ w ∷ []) ⊨ᴳ forcesΔ (valueFo f) ⟩)
                    uIs atSlots)

                forced : ⟨ forces (cndOf q hq) (valueFo f) (chk ξ ∷ chk a ∷ []) ⟩
                forced = subst ⟨_⟩
                  (forcesΔ-reading (valueFo f) (chk ξ ∷ chk a ∷ []) (cndOf q hq))
                  moved

            to : ⟨ (a ∷ cξ ∷ carrierᶠ ∷ cnd p ∷ []) ⊨ᴳ valueBody f ⟩ → ⟨ Tgt ⟩
            to = PT.rec (snd Tgt)
                   (λ { (q , hq , h) → PT.rec (snd Tgt) (inner q hq) h })

            from : ⟨ Tgt ⟩ → ⟨ (a ∷ cξ ∷ carrierᶠ ∷ cnd p ∷ []) ⊨ᴳ valueBody f ⟩
            from = PT.map (λ { (r , hrp , hf) →
                     cnd r , cnd-carrier r
                   , ∣ fst (chk a) , chkPart r , orderPart r hrp , forPart r hf ∣₁ })
              where
                chkPart : (r : Cond)
                        → ⟨ (fst (chk a) ∷ cnd r ∷ a ∷ cξ ∷ carrierᶠ ∷ cnd p ∷ [])
                              ⊨ᴳ renameFo ρC chkFo ⟩
                chkPart r = subst ⟨_⟩
                  (sym (⊨-rename ρC chkFo
                          (fst (chk a) ∷ cnd r ∷ a ∷ cξ ∷ carrierᶠ ∷ cnd p ∷ [])
                          (fst (chk a) ∷ a ∷ [])
                          (ρC-ag (fst (chk a)) (cnd r) a cξ carrierᶠ (cnd p))
                        ∙ chkFo-reading (fst (chk a)) a ha))
                  (≡→≈ˢ refl)

                orderPart : (r : Cond) → ⟨ order r p ⟩
                          → ⟨ (fst (chk a) ∷ cnd r ∷ a ∷ cξ ∷ carrierᶠ ∷ cnd p ∷ [])
                                ⊨ᴳ renameFo ρO orderFo ⟩
                orderPart r hrp = subst ⟨_⟩
                  (sym (⊨-rename ρO orderFo
                          (fst (chk a) ∷ cnd r ∷ a ∷ cξ ∷ carrierᶠ ∷ cnd p ∷ [])
                          (cnd r ∷ cnd p ∷ [])
                          (ρO-ag (fst (chk a)) (cnd r) a cξ carrierᶠ (cnd p))))
                  (subst ⟨_⟩ (sym (orderFo-reading r p)) hrp)

                forPart : (r : Cond)
                        → ⟨ forces r (valueFo f) (chk ξ ∷ chk a ∷ []) ⟩
                        → ⟨ (fst (chk a) ∷ cnd r ∷ a ∷ cξ ∷ carrierᶠ ∷ cnd p ∷ [])
                              ⊨ᴳ renameFo ρV (forcesΔ (valueFo f)) ⟩
                forPart r hf = subst ⟨_⟩
                  (sym (⊨-rename ρV (forcesΔ (valueFo f))
                          (fst (chk a) ∷ cnd r ∷ a ∷ cξ ∷ carrierᶠ ∷ cnd p ∷ [])
                          (cnd r ∷ cξ ∷ fst (chk a) ∷ [])
                          (ρV-ag (fst (chk a)) (cnd r) a cξ carrierᶠ (cnd p))))
                  (subst ⟨_⟩
                    (sym (forcesΔ-reading (valueFo f) (chk ξ ∷ chk a ∷ []) r))
                    hf)

        -- THE GROUND SET. One instance of ground Separation, at the SET β and
        -- at the named formula. Separation's own type
        -- (OrdinaryProfile.agda:88-91) takes `(a : S)` and `(φ : Formula S 1)`,
        -- so no class can be substituted for either: that is the whole of the
        -- proper class protection and K7/breaks/ClassBound.agda-break measures
        -- it at exit 42.

        valuesOf : Separation → (p : Cond) → (f : Nm) (ξ : S) → S
        valuesOf sep p f ξ = mk sep β (valuesFo p f ξ)

        valuesOf-spec
          : (sep : Separation) (p : Cond) (f : Nm) (ξ a : S)
          → (a ∈ˢ valuesOf sep p f ξ)
            ≡ ((a ∈ˢ β)
               ⊓ ⋁ Cond (λ r → order r p
                   ⊓ forces r (valueFo f) (chk ξ ∷ chk a ∷ [])))
        valuesOf-spec sep p f ξ a = ⇔toPath to from
          where
            to : ⟨ a ∈ˢ valuesOf sep p f ξ ⟩
               → ⟨ (a ∈ˢ β)
                   ⊓ ⋁ Cond (λ r → order r p
                       ⊓ forces r (valueFo f) (chk ξ ∷ chk a ∷ [])) ⟩
            to h = ha , subst ⟨_⟩ (valuesFo-reading p f ξ a ha)
                          (mk-sat sep β (valuesFo p f ξ) a h)
              where
                ha : ⟨ a ∈ˢ β ⟩
                ha = mk-bound sep β (valuesFo p f ξ) a h

            from : ⟨ (a ∈ˢ β)
                     ⊓ ⋁ Cond (λ r → order r p
                         ⊓ forces r (valueFo f) (chk ξ ∷ chk a ∷ [])) ⟩
                 → ⟨ a ∈ˢ valuesOf sep p f ξ ⟩
            from (ha , hr) = mk-in sep β (valuesFo p f ξ) a ha
              (subst ⟨_⟩ (sym (valuesFo-reading p f ξ a ha)) hr)

        -- THE BOUND. Trivial from the cut, and that is the point: the theorem
        -- is that the class is SEPARABLE, not that some set happens to contain
        -- it. A bound produced any other way would be host fiat.

        values-bounded : (sep : Separation) (p : Cond) (f : Nm) (ξ : S)
                       → ⟨ subsetΔ (valuesOf sep p f ξ) β ⟩
        values-bounded sep p f ξ x hx =
          mk-bound sep β (valuesFo p f ξ) x hx

        -- THE COVERING DIRECTION, below the fixed condition p. No membership
        -- of G is needed here: a witness r already carries both the refinement
        -- r ≤ p and the forcing fact recorded by the Separation formula.

        values-covers : (sep : Separation) (p : Cond) (f : Nm)
                      → (ξ a : S) (r : Cond)
                      → ⟨ a ∈ˢ β ⟩
                      → ⟨ order r p ⟩
                      → ⟨ forces r (valueFo f) (chk ξ ∷ chk a ∷ []) ⟩
                      → ⟨ a ∈ˢ valuesOf sep p f ξ ⟩
        values-covers sep p f ξ a r ha hrp hf =
          subst ⟨_⟩ (sym (valuesOf-spec sep p f ξ a))
            (ha , ∣ r , hrp , hf ∣₁)

        -- THE COVERING DIRECTION THAT TRACK F ACTUALLY CONSUMES. If the
        -- EXTENSION says that f's value at the coordinate is the check of a,
        -- and a lies in the ground bound, then a is in the ground set. This is
        -- the only place the truth lemma is spent. Satisfaction gives q in G
        -- forcing the value. Directedness gives r in G below both p and q,
        -- and monotonicity moves the forcing fact from q down to r.

        values-covers-sat : (sep : Separation) (p : Cond) (f : Nm) (ξ a : S)
                          → ⟨ G∈ p ⟩
                          → ⟨ a ∈ˢ β ⟩
                          → ⟨ (chk ξ ∷ chk a ∷ []) ⊨ valueFo f ⟩
                          → ⟨ a ∈ˢ valuesOf sep p f ξ ⟩
        values-covers-sat sep p f ξ a hpG ha hsat =
          subst ⟨_⟩ (sym (valuesOf-spec sep p f ξ a))
            (ha , PT.rec (snd local)
              (λ { (q , hqG , hf) → PT.map (below q hf) (directed p q hpG hqG) })
              (subst ⟨_⟩ (truth-at (valueFo f) (chk ξ ∷ chk a ∷ [])) hsat))
          where
            local : Ω
            local = ⋁ Cond (λ r → order r p
                ⊓ forces r (valueFo f) (chk ξ ∷ chk a ∷ []))

            below : (q : Cond)
                  → ⟨ forces q (valueFo f) (chk ξ ∷ chk a ∷ []) ⟩
                  → Σ[ r ∈ Cond ] (⟨ G∈ r ⟩
                      × (⟨ order r p ⟩ × ⟨ order r q ⟩))
                  → Σ[ r ∈ Cond ] (⟨ order r p ⟩
                      × ⟨ forces r (valueFo f) (chk ξ ∷ chk a ∷ []) ⟩)
            below q hf (r , _ , hrp , hrq) =
              r , hrp , forces-mono r q hrq (valueFo f) (chk ξ ∷ chk a ∷ []) hf

------------------------------------------------------------------------------
-- (E) The second residue, discharged from a ground set
------------------------------------------------------------------------------

      -- The check graph is NOT assumed as a formula. It is BUILT from a ground
      -- set that tabulates the check map on β, in the exact shape
      -- NameImage.agda:356-360 already states for the check recursion: a set
      -- that holds the entry of every member of β with its check code, and
      -- that records no other code at a member of β. This is the O7/Supply
      -- pattern, where belowΔ is built from the landed K5 pair rather than
      -- assumed.
      --
      -- WHAT THE TABLE IS AND IS NOT. It is the graph of a map already present
      -- in every K6 telescope, `chk`, which is the canonical check name and is
      -- pinned by chk-spec (K5/Structures.agda:570-572). It is not a choice
      -- function, nothing selects with it, and it is not a class: it is an
      -- element of S. A supplier who has the check graph as a formula instead
      -- may use module AtBound directly.

      module FromTable
        (β             : S)
        -- K3's kernel, two facts. NameKernel.agda:332 for the second.
        (entry         : S → S → S)
        (entry-isKPair : (x b : S) → ⟨ isKPairΔ (entry x b) x b ⟩)
        (tab           : S)
        (tab-in  : (x : S) → ⟨ x ∈ˢ β ⟩ → ⟨ entry x (fst (chk x)) ∈ˢ tab ⟩)
        (tab-out : (e x u : S) → ⟨ x ∈ˢ β ⟩ → ⟨ e ∈ˢ tab ⟩
                 → ⟨ isKPairΔ e x u ⟩ → u ≡ fst (chk x))
        where

        -- "some member of the table is the Kuratowski pair of a and u". Slot
        -- zero is u and slot one is a, which is the layout AtBound reads. The
        -- pair clause is CodedVocabulary's prAtˢ, whose reading is refl.

        chkFo : Formula S 2
        chkFo = ∃̇∈ (con tab) (prAtˢ zero (suc (suc zero)) (suc zero))

        chkFo-reading : (u a : S) → ⟨ a ∈ˢ β ⟩
                      → ((u ∷ a ∷ []) ⊨ᴳ chkFo) ≡ (u ≈ˢ fst (chk a))
        chkFo-reading u a ha = ⇔toPath to from
          where
            to : ⟨ (u ∷ a ∷ []) ⊨ᴳ chkFo ⟩ → ⟨ u ≈ˢ fst (chk a) ⟩
            to = PT.rec (snd (u ≈ˢ fst (chk a)))
                   (λ { (e , he , hk) → ≡→≈ˢ (tab-out e a u ha he hk) })

            from : ⟨ u ≈ˢ fst (chk a) ⟩ → ⟨ (u ∷ a ∷ []) ⊨ᴳ chkFo ⟩
            from hu = ∣ entry a (fst (chk a)) , tab-in a ha , pairAt ∣₁
              where
                pairAt : ⟨ isKPairΔ (entry a (fst (chk a))) a u ⟩
                pairAt = subst (λ w → ⟨ isKPairΔ (entry a (fst (chk a))) a w ⟩)
                           (sym (≈ˢ→≡ hu)) (entry-isKPair a (fst (chk a)))

        open AtBound β chkFo chkFo-reading public

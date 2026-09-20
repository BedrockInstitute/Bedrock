{-# OPTIONS --cubical --safe --guardedness #-}

-- K4 Track I, follow-up: adequate-exists.
--
-- The measured negative of REPORT-I.md section I1 named two missing inputs to
-- the architecture's adequate-exists. Both now exist. K3's NameSpace.agda
-- exports closed-cover, closed-family, closed-union at the top level and
-- closed-⋃ᴳ through Instantiate, which is the family indexed union closure
-- that report asked for; and Track F has landed, so the compiled value has a
-- ground formula. This file spends both and closes the deliverable.
--
-- IT IS A SEPARATE FILE ON PURPOSE. K4/Witnesses.agda is landed at exit 0 and
-- nothing here can put that at risk. Nothing in Witnesses.agda imports this
-- file, and this file adds no field to any record declared there.
--
-- WHAT THE PROOF IS. Bell's hint for Problem 1.29 is "choose a sufficiently
-- large ordinal alpha such that 1 = [∃xφ(x)] is already the join over V(B) at
-- that stage" (fulltext:2612-2617). There are no ordinals here and there is no
-- stage hierarchy, so the domain is built rather than chosen, in four moves
-- and with no choice at any of them:
--
--   1. COLLECTION over the value set, along the graph of the compiled value.
--      Every attained value is the value at some name, so Collection returns a
--      set W0 that holds, for each attained value, at least one code realizing
--      it. Collection promises only that a witness is SOMEWHERE in the set; it
--      promises nothing about which, and that is all this proof uses.
--   2. SEPARATION sifts W0 down to its names. The sift is needed because
--      Collection's witness is chosen by the axiom and not by us: the codes it
--      returns satisfy the graph, and the graph forces them to be names, but
--      the rest of W0 is junk and the next step applies a per name theorem.
--   3. COLLECTION again, over the sifted set, along K3's family class: for
--      each name there merely is a child closed coded set containing it, which
--      is K3's hereditary (NameSpace.agda:709, :865), truncated at both sites.
--      A second Separation sifts the result down to the genuinely closed sets,
--      which is the step the coordinator's brief calls sifting.
--   4. THE UNION of the sifted family is child closed by K3's closed-⋃ᴳ, and
--      that is the lemma this track asked for and did not have. Its reason is
--      worth repeating because it is why the lemma costs nothing: the closure
--      clause is LOCAL, so a set is closed as soon as every member lies in
--      SOME child closed subset of it, and the pieces never have to be
--      compared with each other. The contrast is K3's intersection combinator,
--      whose whole content is comparing two decompositions of one member.
--
-- THE TWO BRIDGES. K3's closure is CODED and this track's AdequateDomain is
-- stated in the HOST support sense with a names condition alongside. Both
-- bridges are K3's and both are taken flat: closed-support is coded→closed
-- composed with support-out, and closed-valid supplies the names condition.
-- Because the UNION is itself closed, both bridges are applied to it once and
-- neither is applied to a member of the family, which is why no fact about the
-- individual pieces survives into the record.
--
-- NO CHOICE, AGAIN, AND THE SHAPE SAYS SO. Every existential in this proof is
-- a propositional truncation and every elimination of one lands either in a
-- truth value, which is a proposition, or in another truncation. The
-- deliverable is therefore truncated, exactly as the architecture prints it,
-- and it is truncated for a reason that has nothing to do with the axiom of
-- choice: Collection produces a set and not a function, and K3's hereditary is
-- truncated at both of its sites.
--
-- WHAT IS STILL A PARAMETER, AND WHY IT IS A SHAPE AND NOT A GAP. Track F is
-- taken as ValueGraph and ValueSetOf, two records with four and three fields,
-- in the same style as the Formulas module of Witnesses.agda: a change on
-- Track F's side cannot invalidate this file. ValueGraph is the two variable
-- graph of the compiled value, which is Track F's Interp.code frozen at the
-- environment by NameImage's colAt and conjoined with the recogniser;
-- ValueSetOf is Track F's admP read in its two useful directions. The three
-- object formulas closedFo, familyAt and nameFo are K3's own, built at
-- NameSpace.agda:727-751 for exactly this proof, and they are taken flat for
-- the same reason.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using ( Formula )
import OrdinaryProfile
import K4.Algebra
import K4.Implication
import K4.Witnesses
import Cubical.HITs.PropositionalTruncation as PT

module K4.AdequateExists {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import OrdinaryProfile 𝒮 using ( Separation; Collection )
open import GroundDescription 𝒮 ext paths using ( separateOf; separateOf-spec )
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ) hiding ( ¬_ )
open hPropStructure 𝒮
open At S id using ( _⊨_ )

open K4.Algebra 𝒮
  using ( Pt; Pt≡; _≤ᴮ_; Lattice; Complement; CodedComplete )

module KW = K4.Witnesses 𝒮 ext paths

-- The path realization, spent on one step: the value set records attainment
-- with the structure's equality and the order transports along a host path.
-- Same two lines as K4/AtomicLaws.agda and K4/Atomic.agda.

≈→≡ : {x y : S} → ⟨ x ≈ˢ y ⟩ → x ≡ y
≈→≡ {x} {y} = subst ⟨_⟩ (paths x y)

--------------------------------------------------------------------------------
-- The telescope, in two halves that match K4/Witnesses.agda line for line
--------------------------------------------------------------------------------

-- The split is the same as the landed file's, so that the coordinator's two
-- application lines are the two application lines it already writes for
-- K4.Witnesses, with nothing reordered and nothing renamed.

module Core
  (B  : S)
  (L  : Lattice B)
  (Cm : Complement B L)
  (Kc : CodedComplete B L)
  (IsName  : S → Ω)
  (support : S → S)
  (weightᴮ : (n x : S) → Pt B)
  where

  open Lattice L
  open K4.Implication 𝒮 ext paths B L Cm using ( _⇒ᴮ_ )

  module KWC = KW.Core B L Cm Kc IsName support weightᴮ
  open KWC using ( Name; name-irr )

  module Atomic
    (_≈ᴮ_ : S → S → Pt B)
    (_∈ᴮ_ : S → S → Pt B)
    (≈ᴮ-glb : (m n : S) (c : Pt B)
            → ((x : S) → ⟨ x ∈ˢ support m ⟩
               → ⟨ c ≤ᴮ ((weightᴮ m x) ⇒ᴮ (x ∈ᴮ n)) ⟩)
            → ((y : S) → ⟨ y ∈ˢ support n ⟩
               → ⟨ c ≤ᴮ ((weightᴮ n y) ⇒ᴮ (y ∈ᴮ m)) ⟩)
            → ⟨ c ≤ᴮ (m ≈ᴮ n) ⟩)
    (≈ᴮ-sym   : (m n : S) → (m ≈ᴮ n) ≡ (n ≈ᴮ m))
    (≈ᴮ-refl  : (n : S) → (n ≈ᴮ n) ≡ ⊤ᴮ)
    (≈ᴮ-trans : (m n p : S) → ⟨ ((m ≈ᴮ n) ⊓ᴮ (n ≈ᴮ p)) ≤ᴮ (m ≈ᴮ p) ⟩)
    (∈ᴮ-congʳ : (m n p : S) → ⟨ ((n ≈ᴮ p) ⊓ᴮ (m ∈ᴮ n)) ≤ᴮ (m ∈ᴮ p) ⟩)
    (weight-≤ : (n x : S) → ⟨ x ∈ˢ support n ⟩
              → ⟨ (weightᴮ n x) ≤ᴮ (x ∈ᴮ n) ⟩)
    where

    module WI = KWC.Witness _≈ᴮ_ _∈ᴮ_ ≈ᴮ-glb ≈ᴮ-sym ≈ᴮ-refl ≈ᴮ-trans
                            ∈ᴮ-congʳ weight-≤
    open WI using ( Lub; AdequateDomain )

    ----------------------------------------------------------------------------
    -- Track F, as two records and not as an import
    ----------------------------------------------------------------------------

    -- THE GRAPH OF THE COMPILED VALUE, as an object formula in two free
    -- variables: slot 0 the name, slot 1 the value, which is the argument
    -- order Collection reads (OrdinaryProfile.agda:95-101, whose class is
    -- evaluated at (y ∷ x ∷ []) with x the member of the domain set and y the
    -- witness). Three facts about it and no more:
    --
    --   g-name  the graph holds only of names, which is what lets the sift
    --           below keep every witness Collection returns;
    --   g-value at a name it pins the value, which is Track F's Interp.reading
    --           read at the environment σ ∷ ν;
    --   g-total every name stands in it to its own value.
    --
    -- The discharge is Track F's Interp.code (K4/Compile.agda:538-552) frozen
    -- at B ∷ codes ν by NameImage's colAt (NameImage.agda:285, reading :288)
    -- and conjoined with K3's recogniser through name-adequate. No field of
    -- this record mentions a formula of Track F, so a change to Interp.code
    -- changes the discharge and not this file.

    record ValueGraph (v : Name → Pt B) : Type ℓ where
      field
        graph   : Formula S 2
        g-name  : (y b : S) → ⟨ (y ∷ b ∷ []) ⊨ graph ⟩ → ⟨ IsName y ⟩
        g-value : (y b : S) (g : ⟨ (y ∷ b ∷ []) ⊨ graph ⟩)
                → ⟨ b ≈ˢ fst (v (y , g-name y b g)) ⟩
        g-total : (σ : Name) → ⟨ (fst σ ∷ fst (v σ) ∷ []) ⊨ graph ⟩

    -- THE VALUE SET, in the two directions this proof uses. Both are Track B's
    -- adequacy halves at the family v, and Track B insists they are named and
    -- proved separately because a track that has one has not got adequacy
    -- (K4/ValueSets.agda:417, :422). occurs is attained-mem, sound is
    -- attained-elim; the discharge is Track F's admP (K4/Compile.agda:982).
    --
    -- Note which direction each is spent on. occurs feeds the CONCLUSION of
    -- the first Collection, at one attained value at a time; sound feeds its
    -- PREMISE, at every member of the set. Neither is a bound on names.

    record ValueSetOf (v : Name → Pt B) : Type ℓ where
      field
        values : S
        occurs : (σ : Name) → ⟨ fst (v σ) ∈ˢ values ⟩
        sound  : (b : S) → ⟨ b ∈ˢ values ⟩
               → ∥ Σ[ σ ∈ Name ] ⟨ b ≈ˢ fst (v σ) ⟩ ∥₁

    ----------------------------------------------------------------------------
    -- K3's closure layer, flat
    ----------------------------------------------------------------------------

    -- Everything here is exported by K3 at the instance, and the weight
    -- carrier is B by architecture section 1.4's W := B. The three object
    -- formulas are K3's own, built for this proof at NameSpace.agda:727-751;
    -- nameFo is sepAt (nameAtˢ zero (suc zero)) (B ∷ []) read back by
    -- name-adequate (NameSpace.agda:868-870).
    --
    -- closed-support is the composite bridge, coded→closed (NameSpace.agda:398)
    -- after support-out (NameSupport.agda:534), so that no signature in this
    -- file mentions Child and the kernel stays out of the ledger entirely.

    module Closure
      (⋃ᴳ      : S → S)
      (⋃ᴳ-spec : (a x : S) → (x ∈ˢ ⋃ᴳ a) ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ (x ∈ˢ y)))
      (closedΔ : S → S → Ω)
      (closed-⋃ᴳ : (G : S) → ((C : S) → ⟨ C ∈ˢ G ⟩ → ⟨ closedΔ B C ⟩)
                 → ⟨ closedΔ B (⋃ᴳ G) ⟩)
      (closed-valid : (C : S) → ⟨ closedΔ B C ⟩
                    → (n : S) → ⟨ n ∈ˢ C ⟩ → ⟨ IsName n ⟩)
      (closed-support : (C : S) → ⟨ closedΔ B C ⟩
                      → (n x : S) → ⟨ n ∈ˢ C ⟩ → ⟨ x ∈ˢ support n ⟩
                      → ⟨ x ∈ˢ C ⟩)
      (hereditary : (n : S) → ⟨ IsName n ⟩
                  → ∥ Σ[ C ∈ S ] (⟨ n ∈ˢ C ⟩ × ⟨ closedΔ B C ⟩) ∥₁)
      (closedFo : Formula S 1)
      (closedFo-reading : (y : S) → ((y ∷ []) ⊨ closedFo) ≡ closedΔ B y)
      (familyAt : Formula S 2)
      (familyAt-reading : (y x : S)
                        → ((y ∷ x ∷ []) ⊨ familyAt)
                        ≡ (closedΔ B y ⊓ (x ∈ˢ y)))
      (nameFo : Formula S 1)
      (nameFo-reading : (y : S) → ((y ∷ []) ⊨ nameFo) ≡ IsName y)
      where

      --------------------------------------------------------------------------
      -- The theorem
      --------------------------------------------------------------------------

      -- Separation and Collection are ARGUMENTS and never module parameters,
      -- which is Track B's convention and the architecture's: a reader of the
      -- signature sees the two axioms this costs and the mixing half of this
      -- track sees neither.

      adequate-exists : Separation → Collection
                      → (v : Name → Pt B) (E : Pt B) → Lub v E
                      → ValueGraph v → ValueSetOf v
                      → ∥ AdequateDomain v E ∥₁
      adequate-exists sep col v E lb VG VS =
        PT.rec PT.squash₁ afterValues (col values graph premise₁)
        where
        open ValueGraph VG
        open ValueSetOf VS

        -- COLLECTION, FIRST PREMISE. Every member of the value set is the
        -- value at some name, and a name stands in the graph to its own
        -- value. The truncation of `sound` passes straight through, because
        -- Collection's premise is itself a truncated existential.

        premise₁ : ⟨ ⋀ S (λ b → (b ∈ˢ values) ⇒
                     (⋁ S (λ y → (y ∷ b ∷ []) ⊨ graph))) ⟩
        premise₁ b hb = PT.map
          (λ { (σ , eq) →
                 fst σ
               , subst (λ z → ⟨ (fst σ ∷ z ∷ []) ⊨ graph ⟩)
                       (sym (≈→≡ eq)) (g-total σ) })
          (sound b hb)

        afterValues :
            Σ[ W₀ ∈ S ] ⟨ ⋀ S (λ b → (b ∈ˢ values) ⇒
              (⋁ S (λ y → (y ∈ˢ W₀) ⊓ ((y ∷ b ∷ []) ⊨ graph)))) ⟩
          → ∥ AdequateDomain v E ∥₁
        afterValues (W₀ , bound₁) =
          PT.rec PT.squash₁ afterNames (col names familyAt premise₂)
          where

          -- THE FIRST SIFT. Collection returns a set that contains a witness
          -- for each value and may contain anything else besides; the next
          -- step applies a per name theorem, so the junk has to go. Every
          -- witness survives the sift, because the graph holds only of names.

          names : S
          names = separateOf sep W₀ nameFo

          names-spec : (y : S) → (y ∈ˢ names) ≡ ((y ∈ˢ W₀) ⊓ IsName y)
          names-spec y = separateOf-spec sep W₀ nameFo y
                       ∙ cong ((y ∈ˢ W₀) ⊓_) (nameFo-reading y)

          -- COLLECTION, SECOND PREMISE. This is K3's hereditary, and it is the
          -- only place completeness of the recogniser is spent.

          premise₂ : ⟨ ⋀ S (λ x → (x ∈ˢ names) ⇒
                       (⋁ S (λ y → (y ∷ x ∷ []) ⊨ familyAt))) ⟩
          premise₂ x hx = PT.map
            (λ { (C , hxC , cl) →
                   C , subst ⟨_⟩ (sym (familyAt-reading C x)) (cl , hxC) })
            (hereditary x (snd (subst ⟨_⟩ (names-spec x) hx)))

          afterNames :
              Σ[ G₀ ∈ S ] ⟨ ⋀ S (λ x → (x ∈ˢ names) ⇒
                (⋁ S (λ y → (y ∈ˢ G₀) ⊓ ((y ∷ x ∷ []) ⊨ familyAt)))) ⟩
            → ∥ AdequateDomain v E ∥₁
          afterNames (G₀ , bound₂) = ∣ built ∣₁
            where

            -- THE SECOND SIFT, which is the one the brief calls sifting.
            -- closed-⋃ᴳ demands that EVERY member of the family be closed,
            -- and Collection's output guarantees only that a closed one is
            -- present for each name. Separation along K3's own closure class
            -- turns the second into the first and loses no witness.

            family : S
            family = separateOf sep G₀ closedFo

            family-spec : (C : S) → (C ∈ˢ family) ≡ ((C ∈ˢ G₀) ⊓ closedΔ B C)
            family-spec C = separateOf-spec sep G₀ closedFo C
                          ∙ cong ((C ∈ˢ G₀) ⊓_) (closedFo-reading C)

            -- THE DOMAIN. This is the line the whole follow-up is about: the
            -- union of a family of child closed sets is child closed, with no
            -- hypothesis and no comparison between the pieces.

            dom : S
            dom = ⋃ᴳ family

            dom-coded : ⟨ closedΔ B dom ⟩
            dom-coded = closed-⋃ᴳ family
              (λ C hC → snd (subst ⟨_⟩ (family-spec C) hC))

            -- THE TWO BRIDGES, applied to the union itself and to nothing
            -- else. Because the union is closed, no fact about an individual
            -- piece is needed twice and none survives into the record.

            dom-names : (x : S) → ⟨ x ∈ˢ dom ⟩ → ⟨ IsName x ⟩
            dom-names = closed-valid dom dom-coded

            dom-closed : (n x : S) → ⟨ n ∈ˢ dom ⟩ → ⟨ x ∈ˢ support n ⟩
                       → ⟨ x ∈ˢ dom ⟩
            dom-closed = closed-support dom dom-coded

            into : (y : S) → ⟨ y ∈ˢ names ⟩ → ⟨ y ∈ˢ dom ⟩
            into y hy = PT.rec (snd (y ∈ˢ dom)) place (bound₂ y hy)
              where
              place : Σ[ C ∈ S ] ⟨ (C ∈ˢ G₀) ⊓ ((C ∷ y ∷ []) ⊨ familyAt) ⟩
                    → ⟨ y ∈ˢ dom ⟩
              place (C , hCG₀ , sat) =
                subst ⟨_⟩ (sym (⋃ᴳ-spec family y))
                  ∣ C
                  , subst ⟨_⟩ (sym (family-spec C)) (hCG₀ , fst read)
                  , snd read ∣₁
                where
                read : ⟨ closedΔ B C ⟩ × ⟨ y ∈ˢ C ⟩
                read = subst ⟨_⟩ (familyAt-reading C y) sat

            -- ADEQUACY. Every value of the family is the value at a name that
            -- landed in the domain, so a bound over the domain is a bound over
            -- every name, and E is least among those by its own specification.
            -- The two truncations eliminate because an order statement is a
            -- proposition, and nothing is chosen.

            adequate : (c : Pt B)
                     → ((p : Pt dom)
                        → ⟨ v (fst p , dom-names (fst p) (snd p)) ≤ᴮ c ⟩)
                     → ⟨ E ≤ᴮ c ⟩
            adequate c bnd = Lub.lub lb c reach
              where
              reach : (σ : Name) → ⟨ v σ ≤ᴮ c ⟩
              reach σ =
                PT.rec (snd (v σ ≤ᴮ c)) transfer
                       (bound₁ (fst (v σ)) (occurs σ))
                where
                transfer :
                    Σ[ y ∈ S ] ⟨ (y ∈ˢ W₀) ⊓ ((y ∷ fst (v σ) ∷ []) ⊨ graph) ⟩
                  → ⟨ v σ ≤ᴮ c ⟩
                transfer (y , hyW₀ , sat) =
                  subst (λ z → ⟨ z ≤ᴮ c ⟩) (sym same) atName
                  where
                  hyName : ⟨ IsName y ⟩
                  hyName = g-name y (fst (v σ)) sat
                  hyNames : ⟨ y ∈ˢ names ⟩
                  hyNames = subst ⟨_⟩ (sym (names-spec y)) (hyW₀ , hyName)
                  hyDom : ⟨ y ∈ˢ dom ⟩
                  hyDom = into y hyNames
                  -- The two certificates of ⟨ IsName y ⟩ in play are the
                  -- graph's and the domain's. They are propositionally but
                  -- not definitionally equal, which is REPORT-B.md's trap T2,
                  -- and name-irr is the transport the landed file names once.
                  atName : ⟨ v (y , hyName) ≤ᴮ c ⟩
                  atName = subst (λ z → ⟨ z ≤ᴮ c ⟩)
                                 (name-irr v y (dom-names y hyDom) hyName)
                                 (bnd (y , hyDom))
                  same : v σ ≡ v (y , hyName)
                  same = Pt≡ (≈→≡ (g-value y (fst (v σ)) sat))

            built : AdequateDomain v E
            built = record
              { dom        = dom
              ; dom-names  = dom-names
              ; dom-closed = dom-closed
              ; adequate   = adequate
              }

      --------------------------------------------------------------------------
      -- The two corollaries the landed file was waiting for
      --------------------------------------------------------------------------

      -- Problem 1.29 with its domain hypothesis discharged. What remains a
      -- hypothesis is the WITNESS NAME, and that is not this track's to build
      -- either: it is the name whose domain is the adequate domain and whose
      -- weight at z is the value of ∃x (φ(x) ∧ z ∈ x), which is a name
      -- construction and belongs with the ground's name builder. The landed
      -- file's WitnessSpec is its specification and nothing here weakens it.

      unique-witness-merely′ :
          Separation → Collection
        → (v : Name → Pt B) (E : Pt B) (lb : Lub v E)
        → WI.BooleanUnique v → WI.Congruent v
        → ValueGraph v → ValueSetOf v
        → ((A : AdequateDomain v E)
           → ∥ Σ[ u ∈ Name ] WI.WitnessSpec v (AdequateDomain.dom A) u ∥₁)
        → ∥ Σ[ τ ∈ Name ] (v τ ≡ E) ∥₁
      unique-witness-merely′ sep col v E lb bu cg VG VS build =
        PT.rec PT.squash₁
          (λ A → PT.map (λ { (u , W) → u , WI.unique-witness v E lb bu cg A u W })
                        (build A))
          (adequate-exists sep col v E lb VG VS)

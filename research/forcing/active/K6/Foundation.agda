{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track D: the `foundation` field of the ordinary profile at the extension
-- structure, by Child induction.
--
-- ---------------------------------------------------------------------
-- WHICH PROPOSITION THIS FILE PROVES, AND WHICH ONE IT DOES NOT
-- ---------------------------------------------------------------------
--
-- There are two different statements in this area and the whole track turns on
-- keeping them apart.
--
--   (A) INDUCTION FORM FOUNDATION, a first order statement INSIDE the
--       structure. It is OrdinaryProfile.FoundationInduction
--       (OrdinaryProfile.agda:104-108): for every object language formula with
--       one free variable, if the formula holds at every element whose members
--       all satisfy it, then it holds at every element. Every arrow in it is a
--       host arrow and every quantifier a host Pi; it contains no ⋀, no ⋁, no
--       ⇒ and no truncation. It is the eighth field of OrdinaryZF
--       (OrdinaryProfile.agda:126-135).
--
--   (B) EXTERNAL WELL FOUNDEDNESS of the extension's membership relation, that
--       is, a host accessibility inhabitant, at every name, for the relation
--       λ ρ τ → ⟨ nm ρ ∈[G] nm τ ⟩, or a transitive collapse of the quotient
--       carrier onto a host well founded structure.
--
-- THIS FILE PROVES (A) AND NOTHING ELSE. It does not prove (B), it does not
-- assume (B), and (B) does not appear in its telescope in any form. Statement
-- (B) is K13's; the extension's membership may be externally ill founded, and
-- the roadmap at :25 requires the two to remain distinct.
--
-- The proof of (A) never inducts on the extension's membership. It inducts on
-- Child, the SUBNAME relation of the ground codes (NameKernel.agda:368-369),
-- whose well foundedness child-wf (NameKernel.agda:392-393) K3 derives from
-- the ground's own regularity and which is blind to the weight carrier, to the
-- forcing conditions and to G. A value member of a name is NOT a Child of its
-- code; it is value equal to one, and the whole content of the argument is the
-- step that crosses that gap, which is the substitution lemma sat-cong
-- (K5/Structures.agda:400-421).
--
-- ---------------------------------------------------------------------
-- K5's NON-CLAIM 3, TRANSCRIBED VERBATIM (K5/Structures.agda:507-517)
-- ---------------------------------------------------------------------
--
--     -- NON-CLAIM 3. Foundation in the extension structure, in the induction
--     -- form the profile uses. Bell makes well-foundedness of the extension's
--     -- membership EQUIVALENT to genericity, and it runs through the transitive
--     -- collapse of the quotient carrier; K5 has neither the quotient nor the
--     -- collapse, so this is K13's and is not claimed here in any form.
--     --
--     -- Trap T-F3 belongs with it. K5 claims exactly ONE field of the ordinary
--     -- profile, `extensional` above; Foundation is the second field a reader
--     -- would expect and it is a non-claim, and the remaining six are K6's.
--     -- The profile record itself is deliberately NOT named in code, because
--     -- exit item X7's negative-evidence table greps every K5 file for it.
--
-- and the type the non-claim ships uninhabited, at K5/Structures.agda:519-520:
--
--     Founded : Type ℓ
--     Founded = OrdinaryProfile.FoundationInduction structure
--
-- K5's stated reason is a true statement ABOUT (B). It is not a statement about
-- (A), and the type Founded that carries the comment is (A). The seam probe
-- K6/FoundationAtStructures.agda inhabits K5's own Founded by name, at an
-- arbitrary G, so that the correction is machine checked and not argued.
--
-- ---------------------------------------------------------------------
-- WHAT IT COSTS
-- ---------------------------------------------------------------------
--
-- No hypothesis on G at all, and the sharper measured form of that claim: G
-- does not occur in the telescope of this file. The value relation and the
-- value membership enter as two abstract relations on S together with the one
-- unfolding law that connects membership to the active entries. No isFilter,
-- no positivity, no genericity, no LEM, no ground axiom, no atomic graph, no
-- image datum, no set quotient and no collapse.
--
-- ONE PARAMETER BEYOND THE SHARED SPINE, and it is a measured correction to the
-- architecture's "Parameters beyond the spine: none". The spine offers Agree as
-- an ABSTRACT type former together with agree-cons and agree-refl, and
-- agree-cons only ever produces an agreement whose two environments have the
-- SAME head. The congruence this proof needs replaces the head by a value equal
-- name, so it needs an agreement with two DIFFERENT heads, which no spine entry
-- constructs. agree-head below is that constructor. It is not a new assumption:
-- at the real instance it is two clauses over K5's concrete Agree
-- (K5/Structures.agda:376-377), exactly the shape K5 itself already wrote for
-- the Boolean side at K5/ExtensionSat.agda:160-162, and the seam probe supplies
-- it that way.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import Cubical.HITs.PropositionalTruncation as PT

module K6.Foundation {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import Cubical.Induction.WellFounded using ( WellFounded ; module WFI )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

-- The carrier of the extension structure, as a function of the name
-- recogniser. This is K5's Nm (K5/Structures.agda:263-264) written as a
-- definition rather than taken as an abstract parameter, for a reason the
-- spine does not state: a proof that produces a name out of a code and a
-- certificate cannot be written against an abstract carrier with only a
-- projection out of it, and the induction below produces exactly that. It is
-- definitionally K3's Name (NameKernel.agda:481-482) and K4's Fib, so the seam
-- probe passes K5's own carrier into it with no coercion.

NameOf : (IsNm : S → Ω) → Type ℓ
NameOf IsNm = Σ[ n ∈ S ] ⟨ IsNm n ⟩

module At
  (Child        : S → S → Type ℓ)
  (child-wf     : WellFounded Child)
  (IsNameᴾ      : S → Ω)
  (child-nameᴾ  : (n : S) → ⟨ IsNameᴾ n ⟩ → (x : S) → Child x n → ⟨ IsNameᴾ x ⟩)
  (_≈[G]_       : S → S → Ω)
  (_∈[G]_       : S → S → Ω)
  (‖Active‖     : S → S → Ω)
  (∈-unfold     : (m n : S) → (m ∈[G] n) ≡ ⋁ S (λ y → ‖Active‖ y n ⊓ (m ≈[G] y)))
  (active-child : (x n : S) → ⟨ ‖Active‖ x n ⟩ → Child x n)
  (≈-sym        : {m n : S} → ⟨ m ≈[G] n ⟩ → ⟨ n ≈[G] m ⟩)
  (_⊨_          : ∀ {k} → Vec (NameOf IsNameᴾ) k → Formula (NameOf IsNameᴾ) k → Ω)
  (Agree        : ∀ {k} → Vec (NameOf IsNameᴾ) k → Vec (NameOf IsNameᴾ) k → Type ℓ)
  (agree-head   : (σ τ : NameOf IsNameᴾ) → ⟨ fst σ ≈[G] fst τ ⟩
                → Agree (σ ∷ []) (τ ∷ []))
  (sat-cong     : ∀ {k} (φ : Formula (NameOf IsNameᴾ) k)
                  (ν μ : Vec (NameOf IsNameᴾ) k)
                → Agree ν μ → (ν ⊨ φ) ≡ (μ ⊨ φ))
  where

  Nm : Type ℓ
  Nm = NameOf IsNameᴾ

  nm : Nm → S
  nm σ = fst σ

  ------------------------------------------------------------------------------
  -- The induction principle
  ------------------------------------------------------------------------------

  -- The one mathematical question of the track. The profile's Foundation
  -- schema wants to recurse along the extension's membership, and there is no
  -- accessibility for that relation and there is not going to be one before
  -- the quotient exists. What IS available is accessibility for Child, one
  -- level down in the codes. So the induction is run on codes and the result is
  -- transported back up to names, and the transport is the whole argument.
  --
  -- Three hypotheses, and each one is doing work that the others cannot.
  --
  -- propP, because the membership witness is truncated: m ∈[G] n is a join
  -- over S (Valuation.agda:294-295), so its inhabitant is an element of a
  -- propositional truncation and the only elimination into a target that is not
  -- itself a truncation is PT.rec at a proposition. Nothing is chosen here, and
  -- nothing may be: a value member of n does not come with a preferred active
  -- entry realising it, because a subname may sit in a name at many weights.
  --
  -- congP, because the recursion hypothesis lands at the ACTIVE ENTRY y, and
  -- the element the step asks about is an arbitrary τ merely value equal to y.
  -- These are different points of Nm; the structure's equality is the value
  -- relation and not a host path, which is the exact design decision
  -- K5/Structures.agda:33-38 records. Without congP the argument stops here and
  -- the break file K6/breaks/NoCongP.agda-break records the goal that stands
  -- open.
  --
  -- step, the schema's own hypothesis, which the caller supplies.

  name-induction : {ℓp : Level} (P : Nm → Type ℓp)
                 → ((σ : Nm) → isProp (P σ))
                 → ((σ τ : Nm) → ⟨ nm σ ≈[G] nm τ ⟩ → P σ → P τ)
                 → ((σ : Nm) → ((τ : Nm) → ⟨ nm τ ∈[G] nm σ ⟩ → P τ) → P σ)
                 → (σ : Nm) → P σ
  name-induction {ℓp} P propP congP step σ =
    WFI.induction child-wf go (nm σ) (snd σ)
    where
      Motive : S → Type (ℓ-max ℓ ℓp)
      Motive n = (hn : ⟨ IsNameᴾ n ⟩) → P (n , hn)

      go : (n : S) → ((y : S) → Child y n → Motive y) → Motive n
      go n ih hn = step (n , hn) members
        where
          members : (τ : Nm) → ⟨ nm τ ∈[G] n ⟩ → P τ
          members τ h = PT.rec (propP τ)
            (λ { (y , hy , e) →
                   congP (y , child-nameᴾ n hn y (active-child y n hy)) τ (≈-sym e)
                     (ih y (active-child y n hy)
                          (child-nameᴾ n hn y (active-child y n hy))) })
            (subst ⟨_⟩ (∈-unfold (nm τ) n) h)

  ------------------------------------------------------------------------------
  -- Foundation, in the induction form the ordinary profile uses
  ------------------------------------------------------------------------------

  -- The flat form of OrdinaryProfile.FoundationInduction 𝒮ᴾ[ G ], written out
  -- rather than obtained by applying K5.Structures, which no K6 file outside a
  -- seam probe does. At the real structure ⟨ y ∈ˢ x ⟩ IS ⟨ nm y ∈[G] nm x ⟩ by
  -- projection out of the record literal at K5/Structures.agda:285-291, and the
  -- _⊨_ of the profile IS the Sat._⊨_ of the extension because OrdinaryProfile
  -- opens At S id and the structure's S is Nm with ι the identity. The seam
  -- probe checks both identifications by asking for the profile's own type.
  --
  -- congP is discharged by the substitution lemma. This is the only place
  -- sat-cong is spent and it is unavoidable: the recursion delivers the truth
  -- of φ at the active entry y and the schema demands it at the value equal
  -- name τ, so a formula has to be moved across the value relation, which is
  -- what a substitution lemma is for. A Child induction that never spends
  -- sat-cong has proved a statement about CODES and not about the structure.

  foundation : (φ : Formula Nm 1)
             → ( (σ : Nm) → ((τ : Nm) → ⟨ nm τ ∈[G] nm σ ⟩ → ⟨ (τ ∷ []) ⊨ φ ⟩)
                          → ⟨ (σ ∷ []) ⊨ φ ⟩ )
             → (σ : Nm) → ⟨ (σ ∷ []) ⊨ φ ⟩
  foundation φ step =
    name-induction (λ σ → ⟨ (σ ∷ []) ⊨ φ ⟩)
      (λ σ → snd ((σ ∷ []) ⊨ φ))
      (λ σ τ e → subst ⟨_⟩ (sat-cong φ (σ ∷ []) (τ ∷ []) (agree-head σ τ e)))
      step

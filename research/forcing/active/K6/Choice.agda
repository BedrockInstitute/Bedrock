{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track I. AC at the extension structure, proved SEPARATELY FROM ZF, and
-- the assembly of the ordinary profile's two records.
--
-- ---------------------------------------------------------------------
-- WHAT THIS FILE DELIVERS, AND IN WHICH ORDER
-- ---------------------------------------------------------------------
--
--   1. The extension structure 𝒮ᴾ, built from the flat spine rather than by
--      applying K5.Structures, which no K6 file outside a seam probe does.
--   2. RULING D11, the transcription. OrdinaryProfile's ChoiceSet premise
--      concludes a HOST PATH while the comment eight lines above it says the
--      structure's ≈ˢ. Both readings are written here as types and the
--      implication that holds between them is proved. Nothing is edited.
--   3. hasChoice, from a ground well ordering CODE and the forcing engine.
--      The whole extension side argument, density, genericity, the truth
--      lemma and the uniqueness, is proved here.
--   4. The assembly. OrdinaryZF 𝒮ᴾ and OrdinaryZFC 𝒮ᴾ as FUNCTIONS of every
--      hypothesis their fields carry, per ruling D1: the conditionality
--      ledger is the signature.
--
-- ---------------------------------------------------------------------
-- THE SEPARATION THE ROADMAP DEMANDS, AND HOW IT IS ENFORCED HERE
-- ---------------------------------------------------------------------
--
-- roadmap:205 asks that the base interfaces stay usable with a weaker ground
-- profile, and AC must not leak into any ZF field's hypotheses. Two mechanisms
-- enforce that and neither is a promise.
--
--   * STRUCTURAL. ChoiceSet is a field of the OUTER record
--     (OrdinaryProfile.agda:137-142), so OrdinaryZF 𝒮ᴾ cannot be inhabited
--     with Choice smuggled inside it.
--   * SCOPE. The ground well ordering enters in module Selection below.
--     module Assemble is a SIBLING of Selection, not a submodule, so the well
--     ordering is not in scope where OrdinaryZF is assembled at all. The
--     negative control "OrdinaryZF 𝒮ᴾ typechecks with the well ordering
--     removed from scope" is therefore discharged by where the modules sit,
--     and not by a grep that a later edit could falsify.
--
-- The ground well ordering is a CODE with a least element principle over
-- ground SETS. It is never a host selector and never a least element principle
-- for an arbitrary host predicate on S: the latter is class Separation, which
-- is O3b, and it is not assumed here.
--
-- ---------------------------------------------------------------------
-- THE MATHEMATICS OF hasChoice, IN ONE PLACE
-- ---------------------------------------------------------------------
--
-- Bell's own route, 1.43, is NOT available: it runs through the core of 1.31,
-- whose proof selects one member of each equivalence class, that is ground AC
-- used as a host selector, and through the Maximum Principle, which is
-- uninhabited (K4/Witnesses.agda:858-861) and is K12a's; roadmap:195 records
-- that the uniform maximum principle IS AC. The route taken here is the
-- generic extension one and it is labelled as such rather than as 1.43: every
-- member of a member of α is value equal to a name in the ground DOMAIN of a
-- name in the ground domain of α, and that domain is a ground SET, so a ground
-- well ordering of it is all the selection the argument ever needs.
--
-- Fix α. For names υ, ζ and a condition r, Sel α υ ζ r says: υ is in the
-- domain of α, ζ is in the domain of υ, r forces υ ∈ α, r forces ζ ∈ υ, and no
-- refinement of r forces any lt-earlier member of the domain of υ into υ. That
-- is the "least name forced in" of the textbook argument, made per condition
-- because no single condition decides the whole picture.
--
--   EXISTENCE. Let x ∈[G] α. Then x is value equal to some υ active in α, and
--   the first premise makes x, hence υ, inhabited. Pick r₁ ∈ G forcing both
--   υ ∈ α and w ∈ υ for one w in the domain of υ. Below any q ≼ r₁ the ground
--   set of names of the domain of υ that some p ≼ q forces into υ is inhabited,
--   so it has an lt-least element z; the condition p witnessing z satisfies
--   Sel, because an earlier name forced in below p would have been in that
--   same ground set. So the coded set of Sel-conditions is dense below r₁, the
--   filter meets it, and the entry it meets it at is active in the choice name.
--
--   UNIQUENESS. Two members of the choice name lying in x read back as
--   Sel α υ₁ ζ₁ r₁ and Sel α υ₂ ζ₂ r₂ with r₁, r₂ ∈ G. Each rᵢ ∈ G turns its
--   forced υᵢ ∈ α and ζᵢ ∈ υᵢ into truths, so x and υᵢ share the member ζᵢ and
--   the DISJOINTNESS PREMISE identifies them. With υ₁ = υ₂ the two minimality
--   clauses are about one and the same domain: if ζ₁ were lt-earlier than ζ₂,
--   directedness produces a condition in G below r₂ forcing ζ₁ ∈ υ₁, which
--   Sel α υ₁ ζ₂ r₂ forbids. Trichotomy leaves the two codes equal.
--
-- WHERE THE DISJOINTNESS PREMISE'S STRENGTH IS SPENT, measured and not
-- assumed: it is used ONCE per side, to identify x with υᵢ. The proof reads it
-- at the SHIPPED strength, a host path, and uses the path to transport a Sel
-- witness along υ₂ ≡ υ₁. A ≈[G]-only premise would need ∈-congʳ in its place
-- and the argument would still run; the discrepancy of 2.2 therefore makes
-- this field easier and not harder, exactly as the architecture predicts, and
-- that direction is machine checked below as documented→shipped.
--
-- ---------------------------------------------------------------------
-- RULE 15, APPLIED TO THIS FILE'S OWN TELESCOPE, AND THE LEDGER ROWS
-- ---------------------------------------------------------------------
--
-- A field's type does not discriminate a legitimate proof from a poisoned one;
-- the telescope does. Every parameter of this file is classified below, in the
-- three classes Track E fixed and Track J corrected.
--
--   (i)   LANDED or PROVABLE at this layer.
--   (ii)  OPEN at this layer and INHABITED at a genuine forcing extension.
--   (iii) FALSE at the intended instance.
--
-- CLASS (iii) IS UNOCCUPIED IN THIS FILE, and that is a result rather than an
-- absence: the question was asked of every parameter. The rule's original
-- example, external well foundedness of the extension's membership, is not a
-- class (iii) hypothesis either; Track J PROVED it at K6/Refuted.agda:551 from
-- child-wf with no hypothesis on G, because 𝒮ᴾ's carrier is the plain Sigma
-- type Nm and not a quotient. Bell's equivalence of ill foundedness with
-- genericity is about the QUOTIENT carrier, which K6 never forms.
--
-- CLASS (i), the spine and the ground side.
--   carrierᶠ IsNameᴾ Child child-nameᴾ entry G _≼ᶜ_ ≼ᶜ-refl ≼ᶜ-trans _≈[G]_
--   _∈[G]_ ‖Active‖ ∈-unfold active-child active-value active-cond entry-value
--   ≈-refl ≈-sym ≈-trans ∈-congˡ ∈-congʳ Dense DenseBelow    K3 and K5 exports.
--   _⊨_ sat-∈ directed denseBelow-intro                       K5 and K1, refl
--                                                             or one line each.
--   dom dom-active                                            K3's support.
--   lt lt-tri wo-least                                        the GROUND well
--     ordering, as a CODE. wo-least quantifies over d : S, a ground SET. The
--     poisoned form quantifies over a host predicate S → Ω, which is ground
--     CLASS Separation and therefore O3b; it is recorded as the break file
--     K6/breaks/ClassLeast.agda-break and it is NOT assumed here.
--   cut cut-sub cut-in cut-out selCand selCand-sub selCand-in selCand-out
--   selName selName-name selName-in selName-out                Track A's mk
--     over an entryBound, cut by a Delta-zero side condition whose forcing
--     conjunct is a membership in Track E1's forcedSet. This is the SAME
--     family of data Track F carries as sepΔ and sepΔ-reading
--     (K6/Separation.agda, module Cut), so it is a published obligation of
--     Tracks A and E and not an invention of this track. See the report.
--
-- CLASS (ii), the engine, and it appears ONLY in the assembly.
--   atom-∈ atom-≐                                              O1.
--   ExtSurjective                                              see the O3b
--     correction immediately below.
--   Supply srcOf supply                                        one Admits per
--     QUANTIFIER node, per formula and never global.
--   LEM ℓ                                                      covered by the
--     programme's single LEM (ℓ-suc ℓ) through lowerLEM
--     (src/Base/Classical.lagda.md:82). Net addition zero.
--
-- THE O3b ROW, CORRECTED (rule 14). ext-surjective is not itself open: it is
-- PROVED at K5/RoundTrip.agda:507 by one induction on child-wf. O3b enters
-- through the TRANSLATION LAYER, TranslateForward.agda:21 and
-- TranslateReverse.agda:73, which take K3's tier-4 MemberImage flat as `image`
-- and `image-spec`, and the row is the FIVE exports of that layer together:
-- trᴮ, trᴮ-name, ≈-agree, ∈-agree and ext-surjective. Charging O3b to
-- ext-surjective alone understates what a supplier must build, and a reader
-- prices K6 off the assembled signature.
--
-- WHAT THE DEGENERATE AUDIT DOES NOT SHOW ABOUT THIS FIELD. Machine checked by
-- Track J: at G = λ _ → ⊥ the fields hasUnion, hasSeparation, hasReplacement,
-- foundation, extensional AND ChoiceSet are all inhabited, so the degenerate
-- audit discriminates only hasPair, hasPower and hasInfinity. A degenerate
-- audit pass is therefore NO evidence for hasChoice, and none is claimed.
--
-- Two ledger rows this file must not carry in their old form. O4 is no longer
-- "no inhabitant of the coded Presentation type": K6/OnePoint.agda:158 ships
-- one, at Extensionality plus paths plus Pairing plus one set constant, so
-- K2Bridge.Bridge has a witnessed hypothesis and the residual obstruction is
-- the strictly smaller "no NONTRIVIAL coded presentation". And check F3, the
-- instantiation audit for Child and child-wf, passes VACUOUSLY in K6: forty
-- comment stripped lines across sixteen files and zero instantiation sites,
-- every one an import, a parameter or a parameter forwarded. The row reads
-- "no sites in K6, forwarded", not "0".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import K4.Algebra
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT

module K6.Choice {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula ; Term ; var ; _∈̇_ )
open import FOL.Manipulation.ConstantOccurrences using ( countFo )
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Sum using ( _⊎_ ; inl ; inr )
open PT using ( ∥_∥₁ ; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

-- One light application, the same scope contract K5/Structures.agda:166-170
-- records: only the point type of the algebra is needed, and only so that the
-- two atomic bridges of the engine can be typed character for character.

open K4.Algebra 𝒮 using ( Pt )

-- K5's own carrier, written as a definition rather than taken as an abstract
-- parameter (K5/Structures.agda:263-264). Track D measured the reason and it
-- applies verbatim here: a proof that produces a name out of a code and a
-- certificate cannot be written against an abstract carrier that offers only a
-- projection, and both halves of the Choice argument produce exactly that.

NameOf : (IsNm : S → Ω) → Type ℓ
NameOf IsNm = Σ[ n ∈ S ] ⟨ IsNm n ⟩

-- K3's Conditions (Valuation.agda:121-122), the same Sigma, written locally so
-- that the order and the filter can appear in a module telescope at all. It is
-- a definition and not a record, so rule 9 is not in play and a seam probe
-- passes K3's own type in with no coercion.

Conditions : S → Type ℓ
Conditions c = Σ[ p ∈ S ] ⟨ p ∈ˢ c ⟩

-- The compiler's parameter free alphabet, K5/Clauses.agda:117-118 and
-- K5/Truth.agda:107-108. Only the engine's Supply family is stated in it.

Src : ℕ → Type ℓ
Src k = Formula (⊥* {ℓ}) k

--------------------------------------------------------------------------------
-- The extension structure at one subset of the conditions, flat
--------------------------------------------------------------------------------

module At
  (carrierᶠ     : S)
  (IsNameᴾ      : S → Ω)
  (Child        : S → S → Type ℓ)
  (child-nameᴾ  : (n : S) → ⟨ IsNameᴾ n ⟩ → (x : S) → Child x n → ⟨ IsNameᴾ x ⟩)
  (entry        : S → S → S)
  (G            : Conditions carrierᶠ → Ω)
  (_≼ᶜ_         : Conditions carrierᶠ → Conditions carrierᶠ → Ω)
  (≼ᶜ-refl      : (p : Conditions carrierᶠ) → ⟨ p ≼ᶜ p ⟩)
  (≼ᶜ-trans     : {p q r : Conditions carrierᶠ}
                → ⟨ p ≼ᶜ q ⟩ → ⟨ q ≼ᶜ r ⟩ → ⟨ p ≼ᶜ r ⟩)
  (_≈[G]_       : S → S → Ω)
  (_∈[G]_       : S → S → Ω)
  (‖Active‖     : S → S → Ω)
  (∈-unfold     : (m n : S) → (m ∈[G] n) ≡ ⋁ S (λ y → ‖Active‖ y n ⊓ (m ≈[G] y)))
  (active-child : (x n : S) → ⟨ ‖Active‖ x n ⟩ → Child x n)
  (active-value : {x n : S} → ⟨ ‖Active‖ x n ⟩ → ⟨ x ∈[G] n ⟩)
  (active-cond  : (x n : S) → ⟨ ‖Active‖ x n ⟩
                → ⟨ ⋁ (Conditions carrierᶠ) (λ p → (G p) ⊓ (entry x (fst p) ∈ˢ n)) ⟩)
  (entry-value  : (n x : S) (p : Conditions carrierᶠ) → ⟨ G p ⟩
                → ⟨ entry x (fst p) ∈ˢ n ⟩ → ⟨ x ∈[G] n ⟩)
  (≈-refl       : (m : S) → ⟨ m ≈[G] m ⟩)
  (≈-sym        : {m n : S} → ⟨ m ≈[G] n ⟩ → ⟨ n ≈[G] m ⟩)
  (≈-trans      : {m n r : S} → ⟨ m ≈[G] n ⟩ → ⟨ n ≈[G] r ⟩ → ⟨ m ≈[G] r ⟩)
  (∈-congˡ      : {m m' n : S} → ⟨ m ≈[G] m' ⟩ → ⟨ m ∈[G] n ⟩ → ⟨ m' ∈[G] n ⟩)
  (∈-congʳ      : {m n n' : S} → ⟨ n ≈[G] n' ⟩ → ⟨ m ∈[G] n ⟩ → ⟨ m ∈[G] n' ⟩)
  (Dense        : S → Ω)
  (DenseBelow   : Conditions carrierᶠ → S → Ω)
  where

  Nm : Type ℓ
  Nm = NameOf IsNameᴾ

  nm : Nm → S
  nm σ = fst σ

  isSetNm : isSet Nm
  isSetNm = isSetΣSndProp isSetS (λ n → snd (IsNameᴾ n))

  Cond : Type ℓ
  Cond = Conditions carrierᶠ

  -- THE STRUCTURE. Four fields, the same four K5 builds at
  -- K5/Structures.agda:285-291, with the equality the VALUE relation and not a
  -- host path. A seam probe checks by refl that this record is K5's
  -- P.Ext.structure G, so nothing here is a second construction of it.

  𝒮ᴾ : ZFStructure (hPropAlgebra ℓ)
  𝒮ᴾ = record
    { S      = Nm
    ; isSetS = isSetNm
    ; _≈ˢ_   = λ σ τ → nm σ ≈[G] nm τ
    ; _∈ˢ_   = λ σ τ → nm σ ∈[G] nm τ }

  private
    module OPᴾ = OrdinaryProfile 𝒮ᴾ

  -- The membership atom of the extension's own language, at two free
  -- variables. It is the only formula this file ever writes, and it is written
  -- rather than taken as a parameter so that the specialisation of Track E2's
  -- forcing relation below is visibly a specialisation and not a second
  -- relation with the same laws.

  memAtom : Formula Nm 2
  memAtom = var zero ∈̇ var (suc zero)

  ------------------------------------------------------------------------------
  -- RULING D11. The ChoiceSet host path premise, transcribed and not repaired
  ------------------------------------------------------------------------------

  -- OrdinaryProfile.agda:111-113 says of ChoiceSet: "Exactly one point is
  -- internal: existence by the truncated existential, uniqueness up to the
  -- structure's ≈ˢ." The CONCLUSION's inner uniqueness clause does use ≈ˢ
  -- (:124). The disjointness PREMISE does not: it reads
  --
  --     ((x y : S) → ⟨ x ∈ˢ a ⟩ → ⟨ y ∈ˢ a ⟩
  --        → ∥ Σ[ z ∈ S ] (⟨ z ∈ˢ x ⟩ × ⟨ z ∈ˢ y ⟩) ∥₁ → x ≡ y)
  --
  -- at :119-120, concluding a host path. At every ground instance in the
  -- programme ≈ˢ IS the host path, so nobody caught it; at 𝒮ᴾ a host path
  -- between names is strictly finer than ≈[G].
  --
  -- ChoiceSetᴰ below is the reading the comment describes, character for
  -- character except for that one conclusion. The direction that holds is
  -- proved: a proof of the DOCUMENTED statement yields the SHIPPED field, so
  -- the shipped field is the weaker of the two and this track is not made
  -- harder by the discrepancy. The converse needs ⟨ x ≈[G] y ⟩ → x ≡ y, which
  -- is false at 𝒮ᴾ as soon as two code distinct value equal names exist, and
  -- it is not proved here. Track J owns the vacuity attempt.
  -- OrdinaryProfile.agda is K1's landed file and is not edited.

  ChoiceSetᴰ : Type ℓ
  ChoiceSetᴰ =
    (a : Nm)
      → ((x : Nm) → ⟨ nm x ∈[G] nm a ⟩ → ∥ Σ[ y ∈ Nm ] ⟨ nm y ∈[G] nm x ⟩ ∥₁)
      → ((x y : Nm) → ⟨ nm x ∈[G] nm a ⟩ → ⟨ nm y ∈[G] nm a ⟩
           → ∥ Σ[ z ∈ Nm ] (⟨ nm z ∈[G] nm x ⟩ × ⟨ nm z ∈[G] nm y ⟩) ∥₁
           → ⟨ nm x ≈[G] nm y ⟩)
      → ⟨ ⋁ Nm (λ c → ⋀ Nm (λ x → (nm x ∈[G] nm a) ⇒
           ( (⋁ Nm (λ z → (nm z ∈[G] nm c) ⊓ (nm z ∈[G] nm x)))
           ⊓ (⋀ Nm (λ z → ⋀ Nm (λ z' →
                (((nm z ∈[G] nm c) ⊓ (nm z ∈[G] nm x))
                 ⊓ ((nm z' ∈[G] nm c) ⊓ (nm z' ∈[G] nm x)))
                ⇒ (nm z ≈[G] nm z'))))))) ⟩

  path→value : (x y : Nm) → x ≡ y → ⟨ nm x ≈[G] nm y ⟩
  path→value x y e = subst (λ u → ⟨ nm x ≈[G] nm u ⟩) e (≈-refl (nm x))

  documented→shipped : ChoiceSetᴰ → OPᴾ.ChoiceSet
  documented→shipped ch a inh disj =
    ch a inh (λ x y hx hy m → path→value x y (disj x y hx hy m))

  ------------------------------------------------------------------------------
  -- The engine, specialised to the membership atom
  ------------------------------------------------------------------------------

  -- Track E2's three exports, at their published types (4.5, E2), plus the one
  -- spine identity that joins them to the structure. At the real instance
  -- sat-∈ is refl, because OrdinaryProfile does `open At S id` and at 𝒮ᴾ the
  -- structure's S is Nm and its ι is id, so the profile's _⊨_ IS the
  -- extension's Sat._⊨_ (4.0's load bearing identity).

  module WithEngine
    (_⊨_         : ∀ {k} → Vec Nm k → Formula Nm k → Ω)
    (sat-∈       : (σ τ : Nm) → ((σ ∷ τ ∷ []) ⊨ memAtom) ≡ (nm σ ∈[G] nm τ))
    (forces      : ∀ {k} → Cond → Formula Nm k → Vec Nm k → Ω)
    (truth-at    : ∀ {k} (φ : Formula Nm k) (ν : Vec Nm k)
                 → (ν ⊨ φ) ≡ ⋁ Cond (λ p → (G p) ⊓ forces p φ ν))
    (forces-mono : ∀ {k} (p q : Cond) (φ : Formula Nm k) (ν : Vec Nm k)
                 → ⟨ q ≼ᶜ p ⟩ → ⟨ forces p φ ν ⟩ → ⟨ forces q φ ν ⟩)
    -- one filter field, and ONLY one; see the ledger note below
    (directed    : (p q : Cond) → ⟨ G p ⟩ → ⟨ G q ⟩
                 → ⟨ ⋁ Cond (λ r → (G r) ⊓ ((r ≼ᶜ p) ⊓ (r ≼ᶜ q))) ⟩)
    -- genericity, in the dense-below form; at the instance this is
    -- generic-meets-denseBelow lem G meets fil (K5/Dense.agda:497-501) and it
    -- is therefore NOT an assumption beyond MeetsAll, LEM ℓ and the filter
    (denseBelow-intro : (r : Cond) (d : S)
                 → ((q : Cond) → ⟨ q ≼ᶜ r ⟩
                    → ⟨ ⋁ Cond (λ p → (fst p ∈ˢ d) ⊓ (p ≼ᶜ q)) ⟩)
                 → ⟨ DenseBelow r d ⟩)
    (meets-below : (r : Cond) → ⟨ G r ⟩ → (d : S)
                 → ⟨ ⋀ S (λ u → (u ∈ˢ d) ⇒ (u ∈ˢ carrierᶠ)) ⟩ → ⟨ DenseBelow r d ⟩
                 → ⟨ ⋁ Cond (λ p → (G p) ⊓ (fst p ∈ˢ d)) ⟩)
    where

    -- MEASURED, and it is a ledger row rather than a remark: the Choice field
    -- spends `directed` and NOTHING ELSE of the filter. Neither `inhabited`
    -- nor `upward` occurs in this module, and the reason is structural. Every
    -- condition the argument uses is produced by the truth lemma out of a
    -- membership that already holds, so it arrives in G rather than being
    -- fetched from G; and the argument never travels back UP the order.
    --
    -- The removal is the measurement and it was run:
    -- K6/breaks/NoDirected.agda-break is this file with the parameter deleted,
    -- and it fails [NotInScope] at the EXISTENCE half's use, line 528 here,
    -- before reaching the uniqueness half's use at line 654. Two uses, not
    -- one. That correction is recorded rather than smoothed over.
    --
    -- Per field, the package now has three different filter costs and they are
    -- all different, so the ledger is per field and never per package.
    -- hasPair: `inhabited` alone (K6/Elementary.agda:455). hasUnion: `upward`
    -- and `directed`, not `inhabited` (:713). hasInfinity and the ground
    -- naturals: ⟨ positive G ⟩ alone, isFilter measured 0 (Track C).
    -- foundation: nothing on G at all (Track D). hasSeparation: no filter law
    -- in Track F's own file. hasChoice: `directed` alone, here.

    frc : Cond → Nm → Nm → Ω
    frc p σ τ = forces p memAtom (σ ∷ τ ∷ [])

    frc-truth : (σ τ : Nm) → (nm σ ∈[G] nm τ) ≡ ⋁ Cond (λ p → (G p) ⊓ frc p σ τ)
    frc-truth σ τ = sym (sat-∈ σ τ) ∙ truth-at memAtom (σ ∷ τ ∷ [])

    frc-mono : (p q : Cond) (σ τ : Nm) → ⟨ q ≼ᶜ p ⟩ → ⟨ frc p σ τ ⟩ → ⟨ frc q σ τ ⟩
    frc-mono p q σ τ = forces-mono p q memAtom (σ ∷ τ ∷ [])

    frc→mem : (σ τ : Nm) (p : Cond) → ⟨ G p ⟩ → ⟨ frc p σ τ ⟩ → ⟨ nm σ ∈[G] nm τ ⟩
    frc→mem σ τ p hp h = subst ⟨_⟩ (sym (frc-truth σ τ)) ∣ p , hp , h ∣₁

    mem→frc : (σ τ : Nm) → ⟨ nm σ ∈[G] nm τ ⟩ → ⟨ ⋁ Cond (λ p → (G p) ⊓ frc p σ τ) ⟩
    mem→frc σ τ h = subst ⟨_⟩ (frc-truth σ τ) h

    ----------------------------------------------------------------------------
    -- The ground well ordering, and the selection predicate
    ----------------------------------------------------------------------------

    -- dom is the ground DOMAIN operator: a ground set holding every subname
    -- that any entry of a name weights. At the instance it is K3's support
    -- (NameSupport.agda:499-563) and dom-active is support-in composed with
    -- the entry of an active pair.
    --
    -- lt, lt-tri and wo-least are the ground well ordering, as a CODE. Note
    -- the quantifier of wo-least: it ranges over d : S, a ground set, not over
    -- a host predicate on S. That distinction is the whole of the ledger row.

    module Selection
      (dom        : S → S)
      (dom-active : (n x : S) → ⟨ ‖Active‖ x n ⟩ → ⟨ x ∈ˢ dom n ⟩)
      (lt         : S → S → Ω)
      (lt-tri     : (z z' : S) → ∥ ⟨ lt z z' ⟩ ⊎ ((z ≡ z') ⊎ ⟨ lt z' z ⟩) ∥₁)
      (wo-least   : (d : S) → ⟨ ⋁ S (λ z → z ∈ˢ d) ⟩
                  → ⟨ ⋁ S (λ z → (z ∈ˢ d)
                        ⊓ ⋀ S (λ z' → (z' ∈ˢ d) ⇒ ((lt z' z) ⇒ ⊥))) ⟩)
      where

      Sel : (α υ ζ : Nm) (r : Cond) → Ω
      Sel α υ ζ r =
          (nm υ ∈ˢ dom (nm α))
        ⊓ (nm ζ ∈ˢ dom (nm υ))
        ⊓ frc r υ α
        ⊓ frc r ζ υ
        ⊓ ⋀ Nm (λ ζ' → (nm ζ' ∈ˢ dom (nm υ)) ⇒ ((lt (nm ζ') (nm ζ)) ⇒
             ⋀ Cond (λ q → (q ≼ᶜ r) ⇒ ((frc q ζ' υ) ⇒ ⊥))))

      sel-domυ : (α υ ζ : Nm) (r : Cond) → ⟨ Sel α υ ζ r ⟩ → ⟨ nm υ ∈ˢ dom (nm α) ⟩
      sel-domυ α υ ζ r s = fst s

      sel-domζ : (α υ ζ : Nm) (r : Cond) → ⟨ Sel α υ ζ r ⟩ → ⟨ nm ζ ∈ˢ dom (nm υ) ⟩
      sel-domζ α υ ζ r s = fst (snd s)

      sel-inα : (α υ ζ : Nm) (r : Cond) → ⟨ Sel α υ ζ r ⟩ → ⟨ frc r υ α ⟩
      sel-inα α υ ζ r s = fst (snd (snd s))

      sel-inυ : (α υ ζ : Nm) (r : Cond) → ⟨ Sel α υ ζ r ⟩ → ⟨ frc r ζ υ ⟩
      sel-inυ α υ ζ r s = fst (snd (snd (snd s)))

      sel-min : (α υ ζ : Nm) (r : Cond) → ⟨ Sel α υ ζ r ⟩
              → (ζ' : Nm) → ⟨ nm ζ' ∈ˢ dom (nm υ) ⟩ → ⟨ lt (nm ζ') (nm ζ) ⟩
              → (q : Cond) → ⟨ q ≼ᶜ r ⟩ → ⟨ frc q ζ' υ ⟩ → ⟨ ⊥ ⟩
      sel-min α υ ζ r s = snd (snd (snd (snd s)))

      --------------------------------------------------------------------------
      -- The two ground constructions, and hasChoice
      --------------------------------------------------------------------------

      -- cut, selCand and selName are Track A's mk over a ground bound cut by a
      -- Delta-zero side condition, and the side conditions are memberships in
      -- Track E1's forcedSet. None of the three carries any extension side
      -- mathematics: each in/out pair is the reading of a mk-spec and nothing
      -- more, and in particular none of them mentions the choice set, the
      -- premises of ChoiceSet, or G.

      module Names
        (cut          : Nm → Nm → Cond → S)
        (cut-sub      : (α υ : Nm) (q : Cond) (z : S) → ⟨ z ∈ˢ cut α υ q ⟩
                      → ⟨ z ∈ˢ dom (nm υ) ⟩)
        (cut-in       : (α υ ζ : Nm) (q p : Cond) → ⟨ nm ζ ∈ˢ dom (nm υ) ⟩
                      → ⟨ p ≼ᶜ q ⟩ → ⟨ frc p ζ υ ⟩ → ⟨ nm ζ ∈ˢ cut α υ q ⟩)
        (cut-out      : (α υ : Nm) (q : Cond) (z : S) → ⟨ z ∈ˢ cut α υ q ⟩
                      → ⟨ ⋁ Cond (λ p → (p ≼ᶜ q) ⊓ ⋁ Nm (λ ζ →
                            ((nm ζ ≡ z) , isSetS (nm ζ) z) ⊓ frc p ζ υ)) ⟩)
        (selCand      : Nm → Nm → S)
        (selCand-sub  : (α υ : Nm)
                      → ⟨ ⋀ S (λ u → (u ∈ˢ selCand α υ) ⇒ (u ∈ˢ carrierᶠ)) ⟩)
        (selCand-in   : (α υ ζ : Nm) (p : Cond) → ⟨ Sel α υ ζ p ⟩
                      → ⟨ fst p ∈ˢ selCand α υ ⟩)
        (selCand-out  : (α υ : Nm) (p : Cond) → ⟨ fst p ∈ˢ selCand α υ ⟩
                      → ⟨ ⋁ Nm (λ ζ → Sel α υ ζ p) ⟩)
        (selName      : Nm → S)
        (selName-name : (α : Nm) → ⟨ IsNameᴾ (selName α) ⟩)
        (selName-in   : (α υ ζ : Nm) (r : Cond) → ⟨ Sel α υ ζ r ⟩
                      → ⟨ entry (nm ζ) (fst r) ∈ˢ selName α ⟩)
        (selName-out  : (α : Nm) (z : S) (p : Cond)
                      → ⟨ entry z (fst p) ∈ˢ selName α ⟩
                      → ⟨ ⋁ Nm (λ υ → ⋁ Nm (λ ζ →
                            ((nm ζ ≡ z) , isSetS (nm ζ) z) ⊓ Sel α υ ζ p)) ⟩)
        where

        choiceName : Nm → Nm
        choiceName α = selName α , selName-name α

        Goal∃ : (α x : Nm) → Ω
        Goal∃ α x = ⋁ Nm (λ z → (nm z ∈[G] selName α) ⊓ (nm z ∈[G] nm x))

        ------------------------------------------------------------------------
        -- The existence half
        ------------------------------------------------------------------------

        meet-exists : (α : Nm)
          → ((x : Nm) → ⟨ nm x ∈[G] nm α ⟩ → ∥ Σ[ y ∈ Nm ] ⟨ nm y ∈[G] nm x ⟩ ∥₁)
          → (x : Nm) → ⟨ nm x ∈[G] nm α ⟩ → ⟨ Goal∃ α x ⟩
        meet-exists α inh x hx =
          PT.rec (snd (Goal∃ α x)) atActive (subst ⟨_⟩ (∈-unfold (nm x) (nm α)) hx)
          where
          Gl : Ω
          Gl = Goal∃ α x

          atActive : Σ[ y ∈ S ] ⟨ ‖Active‖ y (nm α) ⊓ (nm x ≈[G] y) ⟩ → ⟨ Gl ⟩
          atActive (y , hy , exy) = PT.rec (snd Gl) atInner (inh x hx)
            where
            υ : Nm
            υ = y , child-nameᴾ (nm α) (snd α) y (active-child y (nm α) hy)

            hυdom : ⟨ nm υ ∈ˢ dom (nm α) ⟩
            hυdom = dom-active (nm α) y hy

            hυα : ⟨ nm υ ∈[G] nm α ⟩
            hυα = active-value hy

            atInner : Σ[ y' ∈ Nm ] ⟨ nm y' ∈[G] nm x ⟩ → ⟨ Gl ⟩
            atInner (w0 , hw0) =
              PT.rec (snd Gl) atW
                (subst ⟨_⟩ (∈-unfold (nm w0) (nm υ)) (∈-congʳ exy hw0))
              where
              atW : Σ[ w ∈ S ] ⟨ ‖Active‖ w (nm υ) ⊓ (nm w0 ≈[G] w) ⟩ → ⟨ Gl ⟩
              atW (w , hw , _) = PT.rec (snd Gl) atRα (mem→frc υ α hυα)
                where
                ζ0 : Nm
                ζ0 = w , child-nameᴾ (nm υ) (snd υ) w (active-child w (nm υ) hw)

                hζ0dom : ⟨ nm ζ0 ∈ˢ dom (nm υ) ⟩
                hζ0dom = dom-active (nm υ) w hw

                hζ0υ : ⟨ nm ζ0 ∈[G] nm υ ⟩
                hζ0υ = active-value hw

                atRα : Σ[ rα ∈ Cond ] ⟨ (G rα) ⊓ frc rα υ α ⟩ → ⟨ Gl ⟩
                atRα (rα , hrαG , hrαF) = PT.rec (snd Gl) atRζ (mem→frc ζ0 υ hζ0υ)
                  where
                  atRζ : Σ[ rζ ∈ Cond ] ⟨ (G rζ) ⊓ frc rζ ζ0 υ ⟩ → ⟨ Gl ⟩
                  atRζ (rζ , hrζG , hrζF) =
                    PT.rec (snd Gl) atR1 (directed rα rζ hrαG hrζG)
                    where
                    atR1 : Σ[ r ∈ Cond ] ⟨ (G r) ⊓ ((r ≼ᶜ rα) ⊓ (r ≼ᶜ rζ)) ⟩ → ⟨ Gl ⟩
                    atR1 (r1 , hr1G , r1α , r1ζ) =
                      PT.rec (snd Gl) atMet
                        (meets-below r1 hr1G (selCand α υ) (selCand-sub α υ) dense)
                      where
                      Fα : ⟨ frc r1 υ α ⟩
                      Fα = frc-mono rα r1 υ α r1α hrαF

                      Fζ : ⟨ frc r1 ζ0 υ ⟩
                      Fζ = frc-mono rζ r1 ζ0 υ r1ζ hrζF

                      dense : ⟨ DenseBelow r1 (selCand α υ) ⟩
                      dense = denseBelow-intro r1 (selCand α υ) body
                        where
                        body : (Q : Cond) → ⟨ Q ≼ᶜ r1 ⟩
                             → ⟨ ⋁ Cond (λ p → (fst p ∈ˢ selCand α υ) ⊓ (p ≼ᶜ Q)) ⟩
                        body Q hQ = PT.rec (snd goalQ) pick (wo-least (cut α υ Q) inhabQ)
                          where
                          goalQ : Ω
                          goalQ = ⋁ Cond (λ p → (fst p ∈ˢ selCand α υ) ⊓ (p ≼ᶜ Q))

                          inhabQ : ⟨ ⋁ S (λ z → z ∈ˢ cut α υ Q) ⟩
                          inhabQ = ∣ nm ζ0
                                   , cut-in α υ ζ0 Q Q hζ0dom (≼ᶜ-refl Q)
                                       (frc-mono r1 Q ζ0 υ hQ Fζ) ∣₁

                          pick : Σ[ z ∈ S ] ⟨ (z ∈ˢ cut α υ Q)
                                    ⊓ ⋀ S (λ z' → (z' ∈ˢ cut α υ Q) ⇒ ((lt z' z) ⇒ ⊥)) ⟩
                               → ⟨ goalQ ⟩
                          pick (z , hz , hmin) =
                            PT.rec (snd goalQ) atP (cut-out α υ Q z hz)
                            where
                            atP : Σ[ p ∈ Cond ] ⟨ (p ≼ᶜ Q) ⊓ ⋁ Nm (λ ζ →
                                      ((nm ζ ≡ z) , isSetS (nm ζ) z) ⊓ frc p ζ υ) ⟩
                                → ⟨ goalQ ⟩
                            atP (p , hpQ , rest) = PT.rec (snd goalQ) atZeta rest
                              where
                              atZeta : Σ[ ζ ∈ Nm ] ⟨ ((nm ζ ≡ z) , isSetS (nm ζ) z)
                                          ⊓ frc p ζ υ ⟩ → ⟨ goalQ ⟩
                              atZeta (ζ , eζ , hfp) =
                                ∣ p , selCand-in α υ ζ p selζ , hpQ ∣₁
                                where
                                hζdom : ⟨ nm ζ ∈ˢ dom (nm υ) ⟩
                                hζdom = subst (λ u → ⟨ u ∈ˢ dom (nm υ) ⟩) (sym eζ)
                                          (cut-sub α υ Q z hz)

                                minimal : (ζ' : Nm) → ⟨ nm ζ' ∈ˢ dom (nm υ) ⟩
                                        → ⟨ lt (nm ζ') (nm ζ) ⟩
                                        → (q : Cond) → ⟨ q ≼ᶜ p ⟩ → ⟨ frc q ζ' υ ⟩
                                        → ⟨ ⊥ ⟩
                                minimal ζ' hd hlt q hqp hfq =
                                  hmin (nm ζ')
                                    (cut-in α υ ζ' Q q hd (≼ᶜ-trans hqp hpQ) hfq)
                                    (subst (λ u → ⟨ lt (nm ζ') u ⟩) eζ hlt)

                                selζ : ⟨ Sel α υ ζ p ⟩
                                selζ = hυdom , hζdom
                                     , frc-mono r1 p υ α (≼ᶜ-trans hpQ hQ) Fα
                                     , hfp , minimal

                      atMet : Σ[ p ∈ Cond ] ⟨ (G p) ⊓ (fst p ∈ˢ selCand α υ) ⟩ → ⟨ Gl ⟩
                      atMet (p , hpG , hpC) =
                        PT.rec (snd Gl) atSel (selCand-out α υ p hpC)
                        where
                        atSel : Σ[ ζ ∈ Nm ] ⟨ Sel α υ ζ p ⟩ → ⟨ Gl ⟩
                        atSel (ζ , sel) = ∣ ζ , inC , inX ∣₁
                          where
                          inC : ⟨ nm ζ ∈[G] selName α ⟩
                          inC = entry-value (selName α) (nm ζ) p hpG
                                  (selName-in α υ ζ p sel)

                          inX : ⟨ nm ζ ∈[G] nm x ⟩
                          inX = ∈-congʳ (≈-sym exy)
                                  (frc→mem ζ υ p hpG (sel-inυ α υ ζ p sel))

        ------------------------------------------------------------------------
        -- The uniqueness half
        ------------------------------------------------------------------------

        -- Reading a member of the choice name back to the triple that put it
        -- there. Everything is truncated and stays truncated: no Sigma is
        -- eliminated into data anywhere in this module.

        Witness : (α z : Nm) → Type ℓ
        Witness α z = Σ[ υ ∈ Nm ] Σ[ ζ ∈ Nm ] Σ[ r ∈ Cond ]
                        (⟨ G r ⟩ × (⟨ Sel α υ ζ r ⟩ × ⟨ nm z ≈[G] nm ζ ⟩))

        readback : (α z : Nm) → ⟨ nm z ∈[G] selName α ⟩ → ∥ Witness α z ∥₁
        readback α z h =
          PT.rec PT.squash₁ atE (subst ⟨_⟩ (∈-unfold (nm z) (selName α)) h)
          where
          atE : Σ[ e ∈ S ] ⟨ ‖Active‖ e (selName α) ⊓ (nm z ≈[G] e) ⟩ → ∥ Witness α z ∥₁
          atE (e , he , eze) = PT.rec PT.squash₁ atP (active-cond e (selName α) he)
            where
            atP : Σ[ p ∈ Cond ] ⟨ (G p) ⊓ (entry e (fst p) ∈ˢ selName α) ⟩
                → ∥ Witness α z ∥₁
            atP (p , hpG , mem) = PT.rec PT.squash₁ atυ (selName-out α e p mem)
              where
              atυ : Σ[ υ ∈ Nm ] ⟨ ⋁ Nm (λ ζ →
                        ((nm ζ ≡ e) , isSetS (nm ζ) e) ⊓ Sel α υ ζ p) ⟩
                  → ∥ Witness α z ∥₁
              atυ (υ , rest) = PT.map atζ rest
                where
                atζ : Σ[ ζ ∈ Nm ] ⟨ ((nm ζ ≡ e) , isSetS (nm ζ) e) ⊓ Sel α υ ζ p ⟩
                    → Witness α z
                atζ (ζ , eq , sel) =
                  υ , ζ , p , hpG , sel , subst (λ u → ⟨ nm z ≈[G] u ⟩) (sym eq) eze

        -- The one place directedness is spent. Two Sel witnesses over the SAME
        -- υ, both at conditions in G, cannot have their selected names lt
        -- comparable: a common refinement in G below both forces the earlier
        -- name in, which the later witness's minimality clause forbids.

        clash : (α υ ζa ζb : Nm) (ra rb : Cond) → ⟨ G ra ⟩ → ⟨ G rb ⟩
              → ⟨ Sel α υ ζa ra ⟩ → ⟨ Sel α υ ζb rb ⟩
              → ⟨ lt (nm ζa) (nm ζb) ⟩ → ⟨ ⊥ ⟩
        clash α υ ζa ζb ra rb hra hrb sela selb hlt =
          PT.rec isProp⊥ᴸ at3
            (mem→frc ζa υ (frc→mem ζa υ ra hra (sel-inυ α υ ζa ra sela)))
          where
          isProp⊥ᴸ : isProp ⟨ ⊥ ⟩
          isProp⊥ᴸ = snd ⊥

          at3 : Σ[ r3 ∈ Cond ] ⟨ (G r3) ⊓ frc r3 ζa υ ⟩ → ⟨ ⊥ ⟩
          at3 (r3 , hr3 , F3) = PT.rec isProp⊥ᴸ at4 (directed r3 rb hr3 hrb)
            where
            at4 : Σ[ r4 ∈ Cond ] ⟨ (G r4) ⊓ ((r4 ≼ᶜ r3) ⊓ (r4 ≼ᶜ rb)) ⟩ → ⟨ ⊥ ⟩
            at4 (r4 , _ , r43 , r4b) =
              sel-min α υ ζb rb selb ζa (sel-domζ α υ ζa ra sela) hlt
                r4 r4b (frc-mono r3 r4 ζa υ r43 F3)

        meet-unique : (α : Nm)
          → ((x y : Nm) → ⟨ nm x ∈[G] nm α ⟩ → ⟨ nm y ∈[G] nm α ⟩
               → ∥ Σ[ z ∈ Nm ] (⟨ nm z ∈[G] nm x ⟩ × ⟨ nm z ∈[G] nm y ⟩) ∥₁ → x ≡ y)
          → (x : Nm) → ⟨ nm x ∈[G] nm α ⟩
          → (z z' : Nm)
          → ⟨ nm z ∈[G] selName α ⟩ → ⟨ nm z ∈[G] nm x ⟩
          → ⟨ nm z' ∈[G] selName α ⟩ → ⟨ nm z' ∈[G] nm x ⟩
          → ⟨ nm z ≈[G] nm z' ⟩
        meet-unique α disj x hx z z' hzc hzx hz'c hz'x =
          PT.rec (snd (nm z ≈[G] nm z')) go1 (readback α z hzc)
          where
          Tgt : Ω
          Tgt = nm z ≈[G] nm z'

          go1 : Witness α z → ⟨ Tgt ⟩
          go1 (υ1 , ζ1 , r1 , hr1 , sel1 , e1) =
            PT.rec (snd Tgt) go2 (readback α z' hz'c)
            where
            hζ1x : ⟨ nm ζ1 ∈[G] nm x ⟩
            hζ1x = ∈-congˡ e1 hzx

            hζ1υ1 : ⟨ nm ζ1 ∈[G] nm υ1 ⟩
            hζ1υ1 = frc→mem ζ1 υ1 r1 hr1 (sel-inυ α υ1 ζ1 r1 sel1)

            hυ1α : ⟨ nm υ1 ∈[G] nm α ⟩
            hυ1α = frc→mem υ1 α r1 hr1 (sel-inα α υ1 ζ1 r1 sel1)

            ex1 : x ≡ υ1
            ex1 = disj x υ1 hx hυ1α ∣ ζ1 , hζ1x , hζ1υ1 ∣₁

            go2 : Witness α z' → ⟨ Tgt ⟩
            go2 (υ2 , ζ2 , r2 , hr2 , sel2 , e2) =
              PT.rec (snd Tgt) decide (lt-tri (nm ζ1) (nm ζ2))
              where
              hζ2x : ⟨ nm ζ2 ∈[G] nm x ⟩
              hζ2x = ∈-congˡ e2 hz'x

              hζ2υ2 : ⟨ nm ζ2 ∈[G] nm υ2 ⟩
              hζ2υ2 = frc→mem ζ2 υ2 r2 hr2 (sel-inυ α υ2 ζ2 r2 sel2)

              hυ2α : ⟨ nm υ2 ∈[G] nm α ⟩
              hυ2α = frc→mem υ2 α r2 hr2 (sel-inα α υ2 ζ2 r2 sel2)

              ex2 : x ≡ υ2
              ex2 = disj x υ2 hx hυ2α ∣ ζ2 , hζ2x , hζ2υ2 ∣₁

              sel2' : ⟨ Sel α υ1 ζ2 r2 ⟩
              sel2' = subst (λ u → ⟨ Sel α u ζ2 r2 ⟩) (sym ex2 ∙ ex1) sel2

              same : (nm ζ1 ≡ nm ζ2) → ⟨ Tgt ⟩
              same eq = ≈-trans e1
                          (subst (λ u → ⟨ u ≈[G] nm z' ⟩) (sym eq) (≈-sym e2))

              decide : ⟨ lt (nm ζ1) (nm ζ2) ⟩
                     ⊎ ((nm ζ1 ≡ nm ζ2) ⊎ ⟨ lt (nm ζ2) (nm ζ1) ⟩)
                     → ⟨ Tgt ⟩
              decide (inl h) =
                Empty.rec* (clash α υ1 ζ1 ζ2 r1 r2 hr1 hr2 sel1 sel2' h)
              decide (inr (inl eq)) = same eq
              decide (inr (inr h)) =
                Empty.rec* (clash α υ1 ζ2 ζ1 r2 r1 hr2 hr1 sel2' sel1 h)

        ------------------------------------------------------------------------
        -- AC at the extension structure
        ------------------------------------------------------------------------

        -- The field, at OrdinaryProfile.ChoiceSet 𝒮ᴾ exactly as
        -- OrdinaryProfile.agda:115-124 ships it, host path premise included.

        hasChoice : OPᴾ.ChoiceSet
        hasChoice α inh disj = ∣ choiceName α , body ∣₁
          where
          body : (x : Nm) → ⟨ nm x ∈[G] nm α ⟩
               → ⟨ (⋁ Nm (λ z → (nm z ∈[G] selName α) ⊓ (nm z ∈[G] nm x)))
                 ⊓ (⋀ Nm (λ z → ⋀ Nm (λ z' →
                      (((nm z ∈[G] selName α) ⊓ (nm z ∈[G] nm x))
                       ⊓ ((nm z' ∈[G] selName α) ⊓ (nm z' ∈[G] nm x)))
                      ⇒ (nm z ≈[G] nm z')))) ⟩
          body x hx = meet-exists α inh x hx
                    , λ z z' h → meet-unique α disj x hx z z'
                        (fst (fst h)) (snd (fst h)) (fst (snd h)) (snd (snd h))

  ------------------------------------------------------------------------------
  -- The assembly
  ------------------------------------------------------------------------------

  -- RULING D1, mechanised. Every hypothesis any field carries is a parameter
  -- of the assembled term's own type. Nothing is hidden inside a module
  -- applied out of sight: this file applies no K5 module at all.
  --
  -- RULING D4, mechanised. No producer is taken as a record. The eight fields
  -- arrive as eight standalone arguments at the types Part 4's tracks publish,
  -- and the unconditional ones keep their own weaker hypotheses rather than
  -- being levelled up to the conditional ones. The filter is three flat fields
  -- and never the ForcingNotion record, per 4.2.
  --
  -- The ENGINE is written out rather than abbreviated, per 2.1.

  module Assemble
    (B             : S)
    (IsNameᴮ       : S → Ω)
    (_≈ᵁ_ _∈ᵁ_     : NameOf IsNameᴮ → NameOf IsNameᴮ → Ω)
    (Uof           : Pt B → Ω)
    (eqᴬ memᴬ      : S → S → Pt B)
    (trᴮ           : S → S)
    (_≈[U]_        : S → S → Ω)
    (Supply        : ∀ {k} → Src k → Type (ℓ-suc ℓ))
    (srcOf         : ∀ {k} (φ : Formula Nm k) → Src (k + countFo φ))
    -- THE THREE ENGINE ROWS THE ARCHITECTURE'S "Engine" ABBREVIATION OMITS,
    -- measured against K6/ForcesTruth.agda rather than taken from 2.1. They
    -- are opaque here BECAUSE the assembly must not be able to look inside
    -- them; what each is at the instance is written beside it.
    --
    --   CompilerSurface  [OPEN, O1]  eqᴬ, memᴬ, val and the FOURTEEN laws,
    --     K4/Compile.agda:1318-1357 through K5/TruthAtFrame.agda:96-132, the
    --     telescope of K6/ForcesTruth.agda module Engine. This is the same
    --     obstruction as atom-∈ and atom-≐ and it is a SECOND row of it.
    --   FrameData        [OPEN, O4]  L, Cm, Kc, fb, cob, boc at the carrier B
    --     below. The residual obstruction is no longer "no coded Presentation
    --     inhabitant", which K6/OnePoint.agda:158 now supplies, but the
    --     strictly smaller "no NONTRIVIAL coded presentation".
    --   TranslationRest  [OPEN, O3b]  trᴮ-name, ≈-agree and ∈-agree, the
    --     three exports of TranslateForward/TranslateReverse that join trᴮ
    --     and ext-surjective into the O3b five.
    --
    -- Omitting these three from the signature is the defect
    -- K5/Truth.agda:696-699 names, so they are in it.
    (CompilerSurface FrameData TranslationRest : Type (ℓ-suc ℓ))
    where

    open OPᴾ.OrdinaryZF using
      ( extensional ; hasPair ; hasUnion ; hasPower
      ; hasInfinity ; hasSeparation ; hasReplacement ; foundation )
    open OPᴾ.OrdinaryZFC using ( zf ; hasChoice )

    -- The engine's five components, as types. Each ABBREVIATES NOTHING: it is
    -- the type Track E2 publishes, and unfolding these definitions is textual.

    Atom∈ : Type (ℓ-suc ℓ)
    Atom∈ = (σ τ : NameOf IsNameᴮ) → (σ ∈ᵁ τ) ≡ Uof (memᴬ (fst σ) (fst τ))

    Atom≐ : Type (ℓ-suc ℓ)
    Atom≐ = (σ τ : NameOf IsNameᴮ) → (σ ≈ᵁ τ) ≡ Uof (eqᴬ (fst σ) (fst τ))

    -- K5/RoundTrip.agda:504-507. The type is the engine's, and the O3b row is
    -- NOT this line: ext-surjective is proved there, and O3b is the five
    -- translation layer exports trᴮ, trᴮ-name, ≈-agree, ∈-agree and
    -- ext-surjective together, of which trᴮ is also a parameter above. The
    -- untruncated Sigma is a CONSTRUCTION and not a choice, and no proof in
    -- this file projects out of it.

    ExtSurjective : Type ℓ
    ExtSurjective = (n : S) → ⟨ IsNameᴮ n ⟩ → Σ[ τ ∈ Nm ] ⟨ trᴮ (fst τ) ≈[U] n ⟩

    SupplyAll : Type (ℓ-suc ℓ)
    SupplyAll = ∀ {k} (φ : Formula Nm k) → Supply (srcOf φ)

    -- The filter, flat, ForcingNotion.agda:175-181 field for field, and the
    -- genericity obligation, K5/Dense.agda:482-485.

    Positive : Ω
    Positive = ⋁ Cond (λ q → G q)

    Upward : Type ℓ
    Upward = (p q : Cond) → ⟨ G p ⟩ → ⟨ p ≼ᶜ q ⟩ → ⟨ G q ⟩

    Directed : Type ℓ
    Directed = (p q : Cond) → ⟨ G p ⟩ → ⟨ G q ⟩
             → ⟨ ⋁ Cond (λ r → (G r) ⊓ ((r ≼ᶜ p) ⊓ (r ≼ᶜ q))) ⟩

    Meets : Type ℓ
    Meets = (d : S) → ⟨ ⋀ S (λ u → (u ∈ˢ d) ⇒ (u ∈ˢ carrierᶠ)) ⟩ → ⟨ Dense d ⟩
          → ⟨ ⋁ Cond (λ p → (G p) ⊓ (fst p ∈ˢ d)) ⟩

    module Fields
      -- the unconditional four, at their own hypotheses (Part 6.1 and 4.2)
      (ext[G]      : OPᴾ.Extensionality)
      -- MEASURED MATCH, not a guess. Track B reports hasPair at ⟨ positive G ⟩
      -- alone and hasUnion at upward plus directed and NOT inhabited
      -- (K6/Elementary.agda:44-63), with the architecture's isFilter spelling
      -- kept in its seam probe. These two slots are those two types.
      (pair        : ⟨ Positive ⟩ → OPᴾ.Pairing)
      (union       : Upward → Directed → OPᴾ.Union)
      (infinity    : ⟨ Positive ⟩ → OPᴾ.Infinity)
      (found       : OPᴾ.FoundationInduction)
      -- The three conditional ZF fields, each carrying the WHOLE engine and
      -- carrying it uniformly. That uniformity is measured and not assumed:
      -- Tracks F, G and H each report that no filter law and no dense set fact
      -- is named in their own file, because both are spent once inside
      -- K6/ForcesTruth.agda module Engine, which is what produces truth-at.
      -- So the filter and the genericity belong in the engine prefix and not
      -- in a per field tail, and the per field narrowing those tracks measured
      -- is a narrowing BEYOND the engine, of which there is none.
      (separation  : Atom∈ → Atom≐ → CompilerSurface → FrameData
                   → TranslationRest → ExtSurjective → SupplyAll → LEM ℓ
                   → ⟨ Positive ⟩ → Upward → Directed → Meets → OPᴾ.Separation)
      (power       : Atom∈ → Atom≐ → CompilerSurface → FrameData
                   → TranslationRest → ExtSurjective → SupplyAll → LEM ℓ
                   → ⟨ Positive ⟩ → Upward → Directed → Meets → OPᴾ.PowerSet)
      (replacement : Atom∈ → Atom≐ → CompilerSurface → FrameData
                   → TranslationRest → ExtSurjective → SupplyAll → LEM ℓ
                   → ⟨ Positive ⟩ → Upward → Directed → Meets → OPᴾ.Collection)
      where

      module Assembled
        (atom-∈ : Atom∈) (atom-≐ : Atom≐)
        (compiler : CompilerSurface) (frame : FrameData)
        (translation : TranslationRest) (ext-surjective : ExtSurjective)
        (supply : SupplyAll) (lem : LEM ℓ)
        (inhabited : ⟨ Positive ⟩) (upward : Upward) (dir : Directed)
        (meets : Meets)
        where

        ordinaryZF : OPᴾ.OrdinaryZF
        ordinaryZF = record
          { extensional    = ext[G]
          ; hasPair        = pair inhabited
          ; hasUnion       = union upward dir
          ; hasPower       = power atom-∈ atom-≐ compiler frame translation
                                   ext-surjective supply lem
                                   inhabited upward dir meets
          ; hasInfinity    = infinity inhabited
          ; hasSeparation  = separation atom-∈ atom-≐ compiler frame translation
                                   ext-surjective supply lem
                                   inhabited upward dir meets
          ; hasReplacement = replacement atom-∈ atom-≐ compiler frame translation
                                   ext-surjective supply lem
                                   inhabited upward dir meets
          ; foundation     = found }

      -- THE ASSEMBLED SIGNATURE, written out once so that the conditionality
      -- ledger can be read off one declaration. The ground well ordering does
      -- not occur in it and is not in scope here.
      --
      -- READ THE BODY OF Assembled ABOVE FOR THE HEADLINE. Five of the eight
      -- fields are applied to arguments that contain no engine component at
      -- all: extensional, hasPair, hasUnion, hasInfinity and foundation. Three
      -- carry the whole engine. That five-three split is what the signature
      -- exists to make visible, and it is the honest form of 6.3's headline.
      --
      -- TWO EXIT-CHECKLIST ROWS THIS TRACK RECORDS RATHER THAN DISCHARGES.
      -- First, exit item X3 fails today at K6/GroundTransferAtCheck.agda:67
      -- (a host-fiat (f : Σ… → S) → S), :68 image-spec, :90 SK.Weighted, :97
      -- and :101 imageOn; all five survive comment stripping. That is class
      -- (ii) with O3b visible in a seam probe's telescope, so it is a
      -- legitimate recorded exception in ruling D10's sense, and it is
      -- recorded here because X3 reports a violation otherwise. Measured over
      -- every other K6 file, those four spellings are 0. Second, Track J's
      -- choice-premise-forces-code-equality closes ruling D11's vacuity
      -- attempt and ships ChoiceDisjointProposed as a PROPOSAL; the
      -- consequence that belongs to the assembly is that choiceFromStrong
      -- (ProfileFromStrong.agda:162-199) must be re-checked against the
      -- proposed premise, and that is a K6 exit item and not a K1 edit.

      zfᴾ : Atom∈ → Atom≐ → CompilerSurface → FrameData
          → TranslationRest → ExtSurjective → SupplyAll → LEM ℓ
          → ⟨ Positive ⟩ → Upward → Directed → Meets → OPᴾ.OrdinaryZF
      zfᴾ a b c d e f g h i j k l = Assembled.ordinaryZF a b c d e f g h i j k l

      -- AC enters HERE and nowhere above. GroundWellOrder is an opaque type
      -- because the assembly must not be able to look inside it: what it is at
      -- the instance is lt, lt-tri and wo-least of module Selection plus the
      -- coded names of module Names, and none of those may reach a ZF field.

      module WithChoice
        (GroundWellOrder : Type (ℓ-suc ℓ))
        (choice : Atom∈ → Atom≐ → CompilerSurface → FrameData
                → TranslationRest → ExtSurjective → SupplyAll → LEM ℓ
                → ⟨ Positive ⟩ → Upward → Directed → Meets
                → GroundWellOrder → OPᴾ.ChoiceSet)
        where

        module AssembledC
          (atom-∈ : Atom∈) (atom-≐ : Atom≐)
          (compiler : CompilerSurface) (frame : FrameData)
          (translation : TranslationRest) (ext-surjective : ExtSurjective)
          (supply : SupplyAll) (lem : LEM ℓ)
          (inhabited : ⟨ Positive ⟩) (upward : Upward) (dir : Directed)
          (meets : Meets) (wo : GroundWellOrder)
          where

          ordinaryZFC : OPᴾ.OrdinaryZFC
          ordinaryZFC = record
            { zf = zfᴾ atom-∈ atom-≐ compiler frame translation
                       ext-surjective supply lem inhabited upward dir meets
            ; hasChoice = choice atom-∈ atom-≐ compiler frame translation
                       ext-surjective supply lem inhabited upward dir meets wo }

        zfcᴾ : Atom∈ → Atom≐ → CompilerSurface → FrameData
             → TranslationRest → ExtSurjective → SupplyAll → LEM ℓ
             → ⟨ Positive ⟩ → Upward → Directed → Meets
             → GroundWellOrder → OPᴾ.OrdinaryZFC
        zfcᴾ a b c d e f g h i j k l m =
          AssembledC.ordinaryZFC a b c d e f g h i j k l m

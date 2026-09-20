{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track E2. THE CONDITIONAL ENGINE, and the package's conditionality ledger.
--
-- WHAT THIS FILE IS FOR. Four of K6's nine deliverables (Separation, Power Set,
-- Collection, Choice) are conditional, and they are conditional because they
-- pass through here. Ruling D1: no track may hide one of those hypotheses
-- inside a module it applies, so every one of them is a parameter of the
-- telescope below and is visible in the type of truth-at.
--
-- THE FIVE CONDITIONAL INPUTS, with their ledger rows:
--
--   atom-∈, atom-≐   O1. The B side VALUE relation must agree with the COMPILED
--                    atomic value. K4/AtomicGraph.agda:411 declares the record,
--                    TableSupply at :616-617 is uninhabited, and table→graph at
--                    :719-720 is the single route with no supplier. Note that
--                    this is NOT ∈-agree: ∈-agree (K5/Agreement.agda:542)
--                    relates ∈[G] to ∈[U] through trᴮ, a different statement.
--   ext-surjective   O3b. K5/RoundTrip.agda:504-507. Its untruncated Σ is a
--                    CONSTRUCTION and not a choice, and NO proof here or
--                    downstream may project fst of it outside a proposition.
--   supply           One Admits per QUANTIFIER node, universal nodes included,
--                    at the COMPLEMENTED family (K5/Truth.agda:329-330). It is
--                    stated PER FORMULA and never globally, because a family
--                    uniform in φ is strictly stronger and K5's exit item
--                    forbade it. Supply is at Type (ℓ-suc ℓ) and may never
--                    index a join (rule 4).
--   lem              LEM ℓ, which the programme's single LEM (ℓ-suc ℓ) covers
--                    through lowerLEM (src/Base/Classical.lagda.md:82). Net
--                    addition zero. The lowering happens at the instance.
--
-- ------------------------------------------------------------------------
-- RULE 15. THE TELESCOPE, CLASSIFIED, BECAUSE THE TYPE ALONE DOES NOT SAY
-- ------------------------------------------------------------------------
--
-- Track D measured that a field's type cannot tell a legitimate proof from a
-- poisoned one: `foundation` fell out of `ext-wf : WellFounded (…)` on the
-- EXTENSION's membership in three tokens at exit 0, and that hypothesis is
-- FALSE at a genuine forcing extension. Every body-level grep passes; the one
-- `WellFounded` sits in the telescope. So a ledger that says only "conditional
-- on these" is unreadable. Each parameter below carries one of three tags.
--
--   [LANDED]   proved in K1 to K5, or true of any generic filter. Taking it as
--              a parameter is Part 4's engineering rule, not an assumption.
--   [OPEN]     unproved at this layer, and an inhabitant EXISTS at a genuine
--              forcing extension. This is what "conditional" means here.
--   [FALSE]    no genuine extension satisfies it. There is NONE below, and if
--              one ever appears it must be tagged and the conclusion discarded.
--
-- THE ONE SHAPE A READER WILL GREP FOR, answered in advance. `child-wf :
-- WellFounded Child` appears in the Kernel telescope. It is NOT `ext-wf`. It
-- is well-foundedness of K3's GROUND name kernel child relation, an entry of a
-- code inside a code, and it is PROVED at NameKernel.agda:392-393 from ground
-- accessibility. Nothing here assumes the extension's membership is well
-- founded, and nothing here could: that is exactly K5's non-claim 3.
--
-- A MEASURED CORRECTION TO THE ARCHITECTURE'S O3b ROW, and rule 14 governs.
-- The architecture prints `ext-surjective` as THE O3b parameter and prints
-- trᴮ and the two agreements as if they were unconditional. Read at source,
-- that is the wrong cut. `ext-surjective` is PROVED at K5/RoundTrip.agda:507,
-- `ext-surjective n hn = (trᴾ n , trᴾ-name n hn) , ext-onto-raw n`, by one
-- induction on child-wf; it is a landed theorem of the translation layer and
-- not an assumption on top of it. O3b enters through the TRANSLATION itself:
-- TranslateForward.agda:21 and TranslateReverse.agda:73 both take K3's tier-4
-- MemberImage flat, as `image` and `image-spec`, and trᴮ, trᴮ-name, ≈-agree,
-- ∈-agree and ext-surjective are all exports of that one layer. So the O3b row
-- is the FIVE of them together, and charging it to ext-surjective alone
-- understates what a supplier has to build.
--
-- WHAT IS NOT HERE. isGeneric in any position, including as a hypothesis (O6):
-- there is no coded order graph of B, so the Boolean side predicate cannot be
-- applied to a subset of the algebra at all (K5/Generic.agda:424-431). What
-- stands in for it is Track C's meets, taken flat.
--
-- TRAP T-E3, RECORDED SO NOBODY RE-DISCOVERS IT AS A BLOCKER. K4's interp
-- refuses constants outright by an absurd pattern (K4/Compile.agda:1077), so a
-- track that tries to compile a Formula Nm 1 directly concludes, wrongly, that
-- the schema is out of reach. The answer is E1's bridge, applied below.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax
open import FOL.Manipulation.ConstantMapping using ( embed )
open import Cubical.Data.Vec using ( _++_ )
open import Cubical.Induction.WellFounded using ( WellFounded )
open import Cubical.HITs.PropositionalTruncation using ( ∥_∥₁ )
import OrdinaryProfile
import Valuation
import K4.Algebra
import K4.Implication
import K5.Frame
import K5.Structures
import K5.ExtensionSat
import K6.Definability
import K6.TruthSeam

module K6.ForcesTruth
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  -- [LANDED] the ground's own axioms and its coded forcing notion. `paths`
  -- says the GROUND's equality is the host path, true at every ground
  -- instance in the programme; it is emphatically NOT asserted at 𝒮ᴾ[ G ],
  -- where the equality is the value relation (K5/Structures.agda:285-290).
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (sep : OrdinaryProfile.Separation 𝒮)
  (carrier order : ZFStructure.S 𝒮)
  (B : ZFStructure.S 𝒮)
  (L : K4.Algebra.Lattice 𝒮 B)
  (Cm : K4.Algebra.Complement 𝒮 B L)
  (Kc : K4.Algebra.CodedComplete 𝒮 B L)
  -- [OPEN] B, L, Cm, Kc and fb are the coded completion of the notion. O4:
  -- no inhabitant of the coded Presentation exists in the programme yet and
  -- K8 owns building one. A genuine Cohen notion has one.
  (fb : K5.Frame.Poset.ForcingBase 𝒮 carrier order B L Cm)
  -- [LANDED] the two name recognisers, K3's and K4's.
  (IsNameᴾ IsNameᴮ : ZFStructure.S 𝒮 → hProp ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ )
open K4.Implication 𝒮 ext paths B L Cm using ( _⊓ᴮ_ ; _⊔ᴮ_ ; _⇒ᴮ_ ; ⊥ᴮ )
open Valuation 𝒮 using ( Conditions )

module FP = K5.Frame.Poset 𝒮 carrier order
module TSM = K6.TruthSeam 𝒮 ext paths sep carrier order B L Cm Kc fb IsNameᴮ

Src : ℕ → Type ℓ
Src k = Formula (⊥* {ℓ}) k

-- The name kernel and the poset side's order, verbatim from
-- K5/Structures.agda:209-217 and :244-253. The B side's hereditary clause
-- travels with them because the seam needs it.

-- [LANDED] EVERY parameter of this telescope. The seven kernel entries are
-- K3's (Valuation.agda:148-156) with child-wf proved at NameKernel.agda:392;
-- the four order entries are the notion's preorder, projected out of fb at
-- the instance; the two hereditary clauses are NameKernel.agda:470.

module Kernel
  (entry       : S → S → S)
  (Child       : S → S → Type ℓ)
  (isPropChild : (x n : S) → isProp (Child x n))
  (child-entry : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)
  (child-wf    : WellFounded Child)
  (∅ᴺ          : S)
  (∅ᴺ-spec     : (z : S) → (z ∈ˢ ∅ᴺ) ≡ ⊥)
  (_≼ᶜ_        : Conditions carrier → Conditions carrier → Ω)
  (≼ᶜ-refl     : (p : Conditions carrier) → ⟨ p ≼ᶜ p ⟩)
  (≼ᶜ-trans    : {p q r : Conditions carrier} → ⟨ p ≼ᶜ q ⟩ → ⟨ q ≼ᶜ r ⟩ → ⟨ p ≼ᶜ r ⟩)
  (inhabitedᶜ  : ∥ Conditions carrier ∥₁)
  (child-nameᴾ : (n : S) → ⟨ IsNameᴾ n ⟩ → (x : S) → Child x n → ⟨ IsNameᴾ x ⟩)
  (child-nameᴮ : (n : S) → ⟨ IsNameᴮ n ⟩ → (x : S) → Child x n → ⟨ IsNameᴮ x ⟩)
  where

  module TK = TSM.Kernel entry Child isPropChild child-entry child-wf ∅ᴺ ∅ᴺ-spec
                child-nameᴮ
  module KS = K5.Structures.Kernel 𝒮
                entry Child isPropChild child-entry child-wf ∅ᴺ ∅ᴺ-spec
  module PS = KS.PosetSide carrier _≼ᶜ_ ≼ᶜ-refl ≼ᶜ-trans inhabitedᶜ
                IsNameᴾ child-nameᴾ
  module ES = K5.ExtensionSat.Transfer 𝒮
                entry Child isPropChild child-entry child-wf ∅ᴺ ∅ᴺ-spec
                carrier _≼ᶜ_ ≼ᶜ-refl ≼ᶜ-trans inhabitedᶜ IsNameᴾ child-nameᴾ
                B L IsNameᴮ child-nameᴮ

  module At (G : PS.P.Sub) where

    module TA = TK.At G
    module EA = ES.At G (TSM.TAF.GI.Uof G)
    module D  = K6.Definability 𝒮 ext paths carrier order B L Cm Kc fb PS.𝒮ᴾ[ G ]

    -- The carrier of the extension structure, and the satisfaction that
    -- OrdinaryProfile's schemata are literally stated at. Part 4.0's one
    -- load bearing identity: OrdinaryProfile does `open At S id`, so the _⊨_
    -- inside OrdinaryProfile.Separation 𝒮ᴾ[ G ] IS this one.

    Nameᴾ : Type ℓ
    Nameᴾ = D.Nm

    G∈ : FP.Cond → Ω
    G∈ p = TSM.TAF.GI.FS._∈ᴾ_ p G

    -- THE VALUE LAYER. Everything from here down is O1, because val is.

    module Engine
      -- [OPEN] fil and meets are what a GENERIC FILTER is, and K6 never
      -- spells isGeneric (O6, K5/Generic.agda:424-431). A generic filter
      -- over a countable ground exists; building one is K8's and later.
      (fil : TSM.TAF.GI.FS.isFilter G)
      (meets : TSM.TAF.C.MeetsAll G)
      -- [LANDED] decision D1's two entailments. Both are the IDENTITY at the
      -- coded completion under below := fst, checked at exit 0 in
      -- K5/ProbeD1.agda.
      (cob : TSM.TAF.C.CodeOfBelow)
      (boc : TSM.TAF.C.BelowOfCode)
      -- [OPEN] the compiler surface and its fourteen laws, typed verbatim
      -- from Compile.agda:1318-1357. K4 proves the laws, but val itself is
      -- reachable only through the atomic graph (K5/InstanceValue.agda:110,
      -- labelled THIS IS OBSTRUCTION O1), so the whole block is O1 at the
      -- instance. A genuine Boolean valued model has all fifteen.
      (eqᴬ memᴬ : S → S → Pt B)
      (val : ∀ {k} → Src k → Vec TSM.Nameᴮ k → Pt B)
      (law-∈ : ∀ {k} (a b : Fin k) (ν : Vec TSM.Nameᴮ k)
             → val (var a ∈̇ var b) ν ≡ memᴬ (fst (lookup a ν)) (fst (lookup b ν)))
      (law-≐ : ∀ {k} (a b : Fin k) (ν : Vec TSM.Nameᴮ k)
             → val (var a ≐ var b) ν ≡ eqᴬ (fst (lookup a ν)) (fst (lookup b ν)))
      (law-∧ : ∀ {k} (φ ψ : Src k) (ν : Vec TSM.Nameᴮ k)
             → val (φ ∧̇ ψ) ν ≡ (val φ ν ⊓ᴮ val ψ ν))
      (law-∨ : ∀ {k} (φ ψ : Src k) (ν : Vec TSM.Nameᴮ k)
             → val (φ ∨̇ ψ) ν ≡ (val φ ν ⊔ᴮ val ψ ν))
      (law-⇒ : ∀ {k} (φ ψ : Src k) (ν : Vec TSM.Nameᴮ k)
             → val (φ ⇒̇ ψ) ν ≡ (val φ ν ⇒ᴮ val ψ ν))
      (law-⊥ : ∀ {k} (ν : Vec TSM.Nameᴮ k) → val {k} ⊥̇ ν ≡ ⊥ᴮ)
      (law-∃-ub   : ∀ {k} (φ : Src (suc k)) (ν : Vec TSM.Nameᴮ k) (σ : TSM.Nameᴮ)
                  → ⟨ val φ (σ ∷ ν) ≤ᴮ val (∃̇ φ) ν ⟩)
      (law-∃-lub  : ∀ {k} (φ : Src (suc k)) (ν : Vec TSM.Nameᴮ k) (c : Pt B)
                  → ((σ : TSM.Nameᴮ) → ⟨ val φ (σ ∷ ν) ≤ᴮ c ⟩)
                  → ⟨ val (∃̇ φ) ν ≤ᴮ c ⟩)
      (law-∀-lb   : ∀ {k} (φ : Src (suc k)) (ν : Vec TSM.Nameᴮ k) (σ : TSM.Nameᴮ)
                  → ⟨ val (∀̇ φ) ν ≤ᴮ val φ (σ ∷ ν) ⟩)
      (law-∀-glb  : ∀ {k} (φ : Src (suc k)) (ν : Vec TSM.Nameᴮ k) (c : Pt B)
                  → ((σ : TSM.Nameᴮ) → ⟨ c ≤ᴮ val φ (σ ∷ ν) ⟩)
                  → ⟨ c ≤ᴮ val (∀̇ φ) ν ⟩)
      (law-∃∈-ub  : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Vec TSM.Nameᴮ k)
                    (σ : TSM.Nameᴮ)
                  → ⟨ (memᴬ (fst σ) (fst (lookup j ν)) ⊓ᴮ val φ (σ ∷ ν))
                      ≤ᴮ val (∃̇∈ (var j) φ) ν ⟩)
      (law-∃∈-lub : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Vec TSM.Nameᴮ k)
                    (c : Pt B)
                  → ((σ : TSM.Nameᴮ)
                     → ⟨ (memᴬ (fst σ) (fst (lookup j ν)) ⊓ᴮ val φ (σ ∷ ν)) ≤ᴮ c ⟩)
                  → ⟨ val (∃̇∈ (var j) φ) ν ≤ᴮ c ⟩)
      (law-∀∈-lb  : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Vec TSM.Nameᴮ k)
                    (σ : TSM.Nameᴮ)
                  → ⟨ val (∀̇∈ (var j) φ) ν
                      ≤ᴮ (memᴬ (fst σ) (fst (lookup j ν)) ⇒ᴮ val φ (σ ∷ ν)) ⟩)
      (law-∀∈-glb : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Vec TSM.Nameᴮ k)
                    (c : Pt B)
                  → ((σ : TSM.Nameᴮ) → ⟨ c ≤ᴮ (memᴬ (fst σ) (fst (lookup j ν))
                                              ⇒ᴮ val φ (σ ∷ ν)) ⟩)
                  → ⟨ c ≤ᴮ val (∀̇∈ (var j) φ) ν ⟩)
      -- [OPEN] O1, and it is a THEOREM of the classical development, not a
      -- pathology: at a genuine extension the value relation of the Boolean
      -- side does agree with the compiled atomic value. What is missing is
      -- the supplier, TableSupply at K4/AtomicGraph.agda:616-617.
      (atom-∈ : (σ τ : TSM.Nameᴮ) → TA._∈ᵁ_ σ τ ≡ TSM.TAF.GI.Uof G (memᴬ (fst σ) (fst τ)))
      (atom-≐ : (σ τ : TSM.Nameᴮ) → TA._≈ᵁ_ σ τ ≡ TSM.TAF.GI.Uof G (eqᴬ (fst σ) (fst τ)))
      where

      module TC = TA.Conditional fil meets cob boc
                    eqᴬ memᴬ val
                    law-∈ law-≐ law-∧ law-∨ law-⇒ law-⊥
                    law-∃-ub law-∃-lub law-∀-lb law-∀-glb
                    law-∃∈-ub law-∃∈-lub law-∀∈-lb law-∀∈-glb
                    atom-∈ atom-≐

      -- The witness supply, per parameter free formula. Named here so that the
      -- conditional layer below can quantify it over the ABSTRACTED formulas of
      -- the extension's own language, which is the only place K6 meets it.

      Supply : ∀ {k} → Src k → Type (ℓ-suc ℓ)
      Supply = TC.Supply

      -- THE TRANSFER, and O3b. Everything above is about the B side alone; the
      -- obligations of OrdinaryZF live at 𝒮ᴾ[ G ], and ext-⊨ is the only bridge
      -- between the two. All FOUR of its quantifier clauses name
      -- ext-surjective, the two bounded ones included, which is K5's own
      -- measured correction to the architecture (K5/ExtensionSat.agda:20-30).
      -- Every axiom of the profile opens with ⋁ S or ⋀ S, so every axiom
      -- transfer hits that clause.

      module Conditional
        -- [OPEN] the translation layer, and the true shape of the O3b row.
        -- All five are exports of one layer built on K3's tier-4 MemberImage
        -- (TranslateForward.agda:21, TranslateReverse.agda:73), and
        -- ext-surjective is PROVED from the other four at
        -- K5/RoundTrip.agda:507 rather than assumed beside them. A genuine
        -- extension has the translation; K3 proved the datum is not
        -- dischargeable at L, which is a statement about L and not about
        -- forcing extensions in general.
        (trᴮ         : S → S)
        (trᴮ-name    : (n : S) → ⟨ IsNameᴾ n ⟩ → ⟨ IsNameᴮ (trᴮ n) ⟩)
        (≈-agree     : (m n : S) → EA._≈[G]_ m n ≡ EA._≈[U]_ (trᴮ m) (trᴮ n))
        (∈-agree     : (m n : S) → EA._∈[G]_ m n ≡ EA._∈[U]_ (trᴮ m) (trᴮ n))
        (ext-surjective : (n : S) → ⟨ IsNameᴮ n ⟩
                        → Σ[ τ ∈ (Σ[ m ∈ S ] ⟨ IsNameᴾ m ⟩) ]
                            ⟨ EA._≈[U]_ (trᴮ (fst τ)) n ⟩)
        -- [OPEN] one Admits per quantifier node. At the coded completion it
        -- is one Separation over B against a Δ₀ formula; K8 or a K6 follow
        -- up owns it. Stated per formula, never uniformly in φ (trap T-E2).
        (supply : ∀ {k} (φ : Formula Nameᴾ k) → Supply (D.srcOf φ))
        -- [LANDED] covered by the programme's single LEM (ℓ-suc ℓ) through
        -- lowerLEM (src/Base/Classical.lagda.md:82). Net addition zero.
        (lem : LEM ℓ)
        where

        module ESat = EA.Sat trᴮ trᴮ-name ≈-agree ∈-agree ext-surjective

        forces : ∀ {k} → FP.Cond → Formula Nameᴾ k → Vec Nameᴾ k → Ω
        forces p φ ν =
          TC.TS.CC._⊩_[_] p (D.srcOf φ) (ESat.envᴮ (ν ++ D.parsOf φ))

        -- THE TRUTH LEMMA AT THE EXTENSION, which is what the four conditional
        -- fields of OrdinaryZF are proved from. Three steps, and each is a
        -- landed theorem of a different layer: E1's constant bridge, K5 Track
        -- F's satisfaction transfer, and K5 Track G's truth lemma composed
        -- through the seam.

        truth-at : ∀ {k} (φ : Formula Nameᴾ k) (ν : Vec Nameᴾ k)
                 → (ν D.⊨ φ) ≡ ⋁ FP.Cond (λ p → (G∈ p) ⊓ forces p φ ν)
        truth-at φ ν =
          D.sat-abs φ ν
          ∙ ESat.ext-⊨ (D.srcOf φ) (ν ++ D.parsOf φ)
          ∙ TC.seam-truth lem (D.srcOf φ) (ESat.envᴮ (ν ++ D.parsOf φ)) (supply φ)

        -- Monotonicity, K5/Clauses.agda:587-589 read at an abstracted formula.
        -- Note the direction: the hypothesis is that q refines p.

        forces-mono : ∀ {k} (p q : FP.Cond) (φ : Formula Nameᴾ k) (ν : Vec Nameᴾ k)
                    → ⟨ FP._≼ᶜ_ (fst q) (fst p) ⟩
                    → ⟨ forces p φ ν ⟩ → ⟨ forces q φ ν ⟩
        forces-mono p q φ ν =
          TC.TS.CC.⊩-mono p q (D.srcOf φ) (ESat.envᴮ (ν ++ D.parsOf φ))

        -- THE FORCED SET, AND RULE 3.2's SPLIT MADE CONCRETE. Once val is in
        -- scope the set of conditions forcing a formula is FREE: it is E1's
        -- forcedSet at the value, a ForcingBase field, and no Separation is
        -- spent on it. What is conditional is val, not the set.

        forcesSet : ∀ {k} → Formula Nameᴾ k → Vec Nameᴾ k → S
        forcesSet φ ν = D.forcedSet (val (D.srcOf φ) (ESat.envᴮ (ν ++ D.parsOf φ)))

        forcesSet-in : ∀ {k} (φ : Formula Nameᴾ k) (ν : Vec Nameᴾ k) (p : FP.Cond)
                     → ⟨ forces p φ ν ⟩ → ⟨ fst p ∈ˢ forcesSet φ ν ⟩
        forcesSet-in φ ν p =
          D.forcedSet-in (val (D.srcOf φ) (ESat.envᴮ (ν ++ D.parsOf φ))) p

        forcesSet-out : ∀ {k} (φ : Formula Nameᴾ k) (ν : Vec Nameᴾ k) (p : FP.Cond)
                      → ⟨ fst p ∈ˢ forcesSet φ ν ⟩ → ⟨ forces p φ ν ⟩
        forcesSet-out φ ν p =
          D.forcedSet-out (val (D.srcOf φ) (ESat.envᴮ (ν ++ D.parsOf φ))) p

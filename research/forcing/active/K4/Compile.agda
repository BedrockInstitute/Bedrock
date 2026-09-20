{-# OPTIONS --cubical --safe --guardedness #-}

-- K4 Track F: the fixed-formula compiler.
--
-- WHAT THIS MODULE CLAIMS, AND WHAT IT REFUSES TO CLAIM.
--
-- For each FIXED parameter-free formula of the object language this module
-- produces three things at once: a Boolean value in the coded algebra, an
-- internal formula of the ground that describes that value, and a proof that
-- the two agree. The recursion runs in the HOST, over the ten constructors of
-- FOL.Syntax's Formula, and it is total.
--
-- It does NOT produce an internal function from formulas to truth values.
-- Bell 2005 is explicit on page 24: "although the reader will quickly convince
-- himself that for each specific sentence σ of the language of set theory a
-- specific value for [[σ]]B can be written down within that language, the
-- machinery available in ZFC is not (unless ZFC is inconsistent) strong enough
-- to formalize the construction of the map σ ↦ [[σ]]B as a function of σ. More
-- precisely, one can prove in ZFC that the collection of all pairs ⟨σ, [[σ]]B⟩
-- is not a definable class. We must therefore think of this map as being
-- defined metalinguistically." That is exactly the shape below: `interp` is an
-- Agda function on `Src k`, and no code of a formula ever enters a term. There
-- is no `⌜_⌝` here and no import of FOL.Coding; the absence is checkable.
--
-- The three further non-claims, each stated beside the signature it
-- constrains, on K3's model.
--
--  * No Δ₀ witness is claimed for any compiled code. The quantifier nodes
--    quantify over the whole carrier and the name recogniser is Σ₁ with no
--    bound (NameSpace.agda:167-175 records that in its own words), so a
--    `Δ₀-code` field would be false. There is none, and `grep -c "Δ₀"` on this
--    file returns only the occurrences in this comment.
--  * Agreement with a host evaluator is not stated here at all. It is
--    conditional on both sides admitting the relevant families, and the
--    infinitary half of the bridge (`reads-sup`, `reads-inf`) is unproved
--    upstream. Track J owns whatever half is statable.
--  * The value of a bounded quantifier node is the join over ALL names of the
--    guarded body, not the join over the domain of the bound. The two agree by
--    Bell's Corollary 1.18, which is an atomic-layer theorem and belongs to
--    Track D's `bounded-∃`. It is not assumed here and not used here.
--
-- WHAT THE INTERNAL CODE IS BUILT FROM, AND THE CORRECTION THAT FORCED IT.
--
-- The architecture's section 1.7 says the existential node's code is built
-- "from subsetAtˢ and supAtˢ/supΔ (CodedCompletion.agda:172-185)". That cannot
-- be done at this track's abstraction and the reason is measurable.
-- `supAtˢ c o a q` takes a slot for the CONDITION CARRIER and a slot for the
-- ORDER, and `Core.supᴮ` is defined at `CodedCompletion.agda:820-822` as a
-- Separation instance of `supφ a = sepAt (supAtˢ …) (carrier ∷ order ∷ a ∷ [])`.
-- Track F's permitted hypotheses are Tracks A, C, E, Separation,
-- Extensionality, `≈ˢ-paths` and the name layer: they contain no presentation,
-- no carrier and no order, and the preamble bars `carrier` and `Cond` from a
-- signature. So `supΔ` is not available and must not be simulated.
--
-- The architecture's ENGLISH words are the repair. It says the code asserts
-- "slot 0 is the least upper bound of V inside B", and a least upper bound is
-- an ORDER statement. K4's order is internal inclusion of codes,
-- `u ≤ᴮ v = fst u ⊆ˢ fst v` (K4/Algebra.agda:78-79), which IS a formula. Every
-- operation this compiler needs is pinned by a universal property in that
-- order: the lattice by `⊓-lb₁`, `⊓-lb₂`, `⊓-glb`, `⊔-ub₁`, `⊔-ub₂`, `⊔-lub`,
-- `⊥-least`; the completion by `sup-ub`, `sup-lub`, `inf-lb`, `inf-glb`; and
-- the implication by Track A's adjunction `⇒ᴮ-curry`/`⇒ᴮ-uncurry`. So the whole
-- internal vocabulary of this file is built from ONE atomic formula, bounded
-- quantification, and nothing else. That is the payoff of the architecture's
-- decision to state every value fact as a universal property, and it is
-- collected below as the graph kit.
--
-- The atomic values are the exception and are not pinned by any order fact.
-- They enter as Track E's atomic graph, flat, exactly as the architecture
-- designs them, and O1 is untouched: at the regular-open algebra that
-- parameter has no discharge today.
--
-- SCOPE CONTRACT. Records are generative, so this file declares no algebra
-- record and no value-set record. K4.Algebra is opened here for the three
-- record types and the point vocabulary; K4.Infinitary is opened for the whole
-- Boolean theory including `_⇒ᴮ_`; K4.ValueSets supplies admission. None of
-- them is re-exported.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import K4.Algebra
import K4.Implication
import K4.Infinitary
import K4.ValueSets

module K4.Compile
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Term; Formula; con; var
        ; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import FOL.Manipulation.ConstantOccurrences using ( countFo )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( map )
open import FOL.Manipulation.ParameterAbstraction using ( absFo )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_; ⟦_⟧ )
open Sat (hPropAlgebra ℓ) 𝒮 {K = S} id using ( Agrees; ⊨-rename )

open import OrdinaryProfile 𝒮 using ( Separation; module PathRealization )
open PathRealization paths using ( ≈ˢ-to-path; path-to-≈ˢ )

open import CodedVocabulary 𝒮 using ( sepAt; sepAt-reading )

open K4.Algebra 𝒮
  using ( Pt; Pt≡; _≤ᴮ_; ≤ᴮ-refl; ⊆ˢ-trans
        ; Lattice; Complement; CodedComplete )

-- ---------------------------------------------------------------------
-- Two host facts used everywhere
-- ---------------------------------------------------------------------

-- Rule 1's remedy: an unchanged endpoint of a congruence over a truth value
-- operation goes through a named reflexivity, never a bare `refl`, so that the
-- propositionality component of the hProp pair is not left to unification.

same : (P : Ω) → P ≡ P
same P = refl

≈ˢ-refl : (x : S) → ⟨ x ≈ˢ x ⟩
≈ˢ-refl x = path-to-≈ˢ x x refl

-- Definite description at the level of truth values. A join over the carrier
-- whose first factor pins the bound variable to one code collapses to the
-- second factor at that code. This is the single workhorse of the connective
-- nodes: a compiled code says "there is a p which is the value of φ, and …",
-- and this lemma reads that back as "… at the value of φ".

pin-elim : (m : S) (Q : S → Ω) → (⋁ S (λ p → (p ≈ˢ m) ⊓ Q p)) ≡ Q m
pin-elim m Q = ⇔toPath fwd bwd
  where
    lhs : Ω
    lhs = ⋁ S (λ p → (p ≈ˢ m) ⊓ Q p)

    fwd : ⟨ lhs ⟩ → ⟨ Q m ⟩
    fwd = PT.rec (snd (Q m))
      (λ { (p , (e , q)) → subst (λ w → ⟨ Q w ⟩) (≈ˢ-to-path p m e) q })

    bwd : ⟨ Q m ⟩ → ⟨ lhs ⟩
    bwd q = ∣ m , (≈ˢ-refl m , q) ∣₁

-- ---------------------------------------------------------------------
-- The internal graph kit
-- ---------------------------------------------------------------------

-- Everything the compiler says about a Boolean value inside the ground is
-- said in the vocabulary of this section. There is exactly one atomic
-- ingredient, membership, and one bounded quantifier; every reading below is
-- `refl`, which is the standing evidence that no clause of the object language
-- has been quietly reinterpreted.
--
-- Why this is possible at all. K4's order is internal inclusion of codes, so
-- an order statement about elements of the algebra is a first order statement
-- about sets. Every operation the compiler forms is pinned by an order
-- property: the lattice operations by their bounds, the completion by its
-- bounds, and the implication by Track A's adjunction. So the compiler needs
-- no internal description of the algebra's construction, and in particular
-- needs neither the condition carrier nor the refinement order.

infix 18 _⊆̇_

_⊆̇_ : ∀ {n} → Fin n → Fin n → Formula S n
a ⊆̇ b = ∀̇∈ (var a) (var zero ∈̇ var (suc b))

⊆̇-reading : ∀ {n} (a b : Fin n) (γ : S ^ n)
          → (γ ⊨ (a ⊆̇ b)) ≡ (lookup a γ ⊆ˢ lookup b γ)
⊆̇-reading a b γ = refl

-- "every member of the set at slot a is included in the set at slot c", and
-- its dual. These are the two shapes a bound of a whole family takes.

ubAtˢ lbAtˢ : ∀ {n} → Fin n → Fin n → Formula S n
ubAtˢ a c = ∀̇∈ (var a) (zero ⊆̇ suc c)
lbAtˢ a c = ∀̇∈ (var a) (suc c ⊆̇ zero)

ubΔ lbΔ : S → S → Ω
ubΔ A C = ⋀ S (λ u → (u ∈ˢ A) ⇒ (u ⊆ˢ C))
lbΔ A C = ⋀ S (λ u → (u ∈ˢ A) ⇒ (C ⊆ˢ u))

ubAtˢ-reading : ∀ {n} (a c : Fin n) (γ : S ^ n)
              → (γ ⊨ ubAtˢ a c) ≡ ubΔ (lookup a γ) (lookup c γ)
ubAtˢ-reading a c γ = refl

lbAtˢ-reading : ∀ {n} (a c : Fin n) (γ : S ^ n)
              → (γ ⊨ lbAtˢ a c) ≡ lbΔ (lookup a γ) (lookup c γ)
lbAtˢ-reading a c γ = refl

-- The least upper bound of the family at slot a, taken inside the algebra
-- carrier at slot w, and the greatest lower bound. These are the two
-- quantifier nodes' internal content.

lubAtˢ glbAtˢ : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
lubAtˢ w a q = (var q ∈̇ var w) ∧̇ ubAtˢ a q
             ∧̇ ∀̇∈ (var w) (ubAtˢ (suc a) zero ⇒̇ (suc q ⊆̇ zero))
glbAtˢ w a q = (var q ∈̇ var w) ∧̇ lbAtˢ a q
             ∧̇ ∀̇∈ (var w) (lbAtˢ (suc a) zero ⇒̇ (zero ⊆̇ suc q))

lubΔ glbΔ : S → S → S → Ω
lubΔ W A q = (q ∈ˢ W) ⊓ ubΔ A q ⊓ ⋀ S (λ w → (w ∈ˢ W) ⇒ (ubΔ A w ⇒ (q ⊆ˢ w)))
glbΔ W A q = (q ∈ˢ W) ⊓ lbΔ A q ⊓ ⋀ S (λ w → (w ∈ˢ W) ⇒ (lbΔ A w ⇒ (w ⊆ˢ q)))

lubAtˢ-reading : ∀ {n} (w a q : Fin n) (γ : S ^ n)
               → (γ ⊨ lubAtˢ w a q)
                 ≡ lubΔ (lookup w γ) (lookup a γ) (lookup q γ)
lubAtˢ-reading w a q γ = refl

glbAtˢ-reading : ∀ {n} (w a q : Fin n) (γ : S ^ n)
               → (γ ⊨ glbAtˢ w a q)
                 ≡ glbΔ (lookup w γ) (lookup a γ) (lookup q γ)
glbAtˢ-reading w a q γ = refl

-- The binary meet and join, by their bounds.

meetAtˢ joinAtˢ : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
meetAtˢ w u v q = (var q ∈̇ var w) ∧̇ (q ⊆̇ u) ∧̇ (q ⊆̇ v)
                ∧̇ ∀̇∈ (var w) ((zero ⊆̇ suc u) ⇒̇ (zero ⊆̇ suc v) ⇒̇ (zero ⊆̇ suc q))
joinAtˢ w u v q = (var q ∈̇ var w) ∧̇ (u ⊆̇ q) ∧̇ (v ⊆̇ q)
                ∧̇ ∀̇∈ (var w) ((suc u ⊆̇ zero) ⇒̇ (suc v ⊆̇ zero) ⇒̇ (suc q ⊆̇ zero))

meetΔ joinΔ : S → S → S → S → Ω
meetΔ W u v q = (q ∈ˢ W) ⊓ (q ⊆ˢ u) ⊓ (q ⊆ˢ v)
              ⊓ ⋀ S (λ w → (w ∈ˢ W) ⇒ (w ⊆ˢ u) ⇒ (w ⊆ˢ v) ⇒ (w ⊆ˢ q))
joinΔ W u v q = (q ∈ˢ W) ⊓ (u ⊆ˢ q) ⊓ (v ⊆ˢ q)
              ⊓ ⋀ S (λ w → (w ∈ˢ W) ⇒ (u ⊆ˢ w) ⇒ (v ⊆ˢ w) ⇒ (q ⊆ˢ w))

meetAtˢ-reading : ∀ {n} (w u v q : Fin n) (γ : S ^ n)
                → (γ ⊨ meetAtˢ w u v q)
                  ≡ meetΔ (lookup w γ) (lookup u γ) (lookup v γ) (lookup q γ)
meetAtˢ-reading w u v q γ = refl

joinAtˢ-reading : ∀ {n} (w u v q : Fin n) (γ : S ^ n)
                → (γ ⊨ joinAtˢ w u v q)
                  ≡ joinΔ (lookup w γ) (lookup u γ) (lookup v γ) (lookup q γ)
joinAtˢ-reading w u v q γ = refl

-- The bottom of the algebra, which is the whole content of the ⊥̇ node.

botAtˢ : ∀ {n} → Fin n → Fin n → Formula S n
botAtˢ w q = (var q ∈̇ var w) ∧̇ ∀̇∈ (var w) (suc q ⊆̇ zero)

botΔ : S → S → Ω
botΔ W q = (q ∈ˢ W) ⊓ ⋀ S (λ w → (w ∈ˢ W) ⇒ (q ⊆ˢ w))

botAtˢ-reading : ∀ {n} (w q : Fin n) (γ : S ^ n)
               → (γ ⊨ botAtˢ w q) ≡ botΔ (lookup w γ) (lookup q γ)
botAtˢ-reading w q γ = refl

-- The implication, by Track A's adjunction rather than by ¬ᴮ and ⊔ᴮ. The
-- relative pseudocomplement is the largest element whose meet with the
-- antecedent is below the consequent, and that is again an order statement, so
-- the ⇒̇ node needs no internal description of the complement.

resAtˢ : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
resAtˢ w u v a = ∃̇ (meetAtˢ (suc w) (suc a) (suc u) zero ∧̇ (zero ⊆̇ suc v))

resΔ : S → S → S → S → Ω
resΔ W U V a = ⋁ S (λ m → meetΔ W a U m ⊓ (m ⊆ˢ V))

resAtˢ-reading : ∀ {n} (w u v a : Fin n) (γ : S ^ n)
               → (γ ⊨ resAtˢ w u v a)
                 ≡ resΔ (lookup w γ) (lookup u γ) (lookup v γ) (lookup a γ)
resAtˢ-reading w u v a γ = refl

impAtˢ : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
impAtˢ w u v q = (var q ∈̇ var w) ∧̇ resAtˢ w u v q
               ∧̇ ∀̇∈ (var w) (resAtˢ (suc w) (suc u) (suc v) zero ⇒̇ (zero ⊆̇ suc q))

impΔ : S → S → S → S → Ω
impΔ W U V q = (q ∈ˢ W) ⊓ resΔ W U V q
             ⊓ ⋀ S (λ w → (w ∈ˢ W) ⇒ (resΔ W U V w ⇒ (w ⊆ˢ q)))

impAtˢ-reading : ∀ {n} (w u v q : Fin n) (γ : S ^ n)
               → (γ ⊨ impAtˢ w u v q)
                 ≡ impΔ (lookup w γ) (lookup u γ) (lookup v γ) (lookup q γ)
impAtˢ-reading w u v q γ = refl

-- ---------------------------------------------------------------------
-- The compiler's ledger
-- ---------------------------------------------------------------------

-- Reading the telescope top to bottom is reading the whole hypothesis list of
-- this track. Separation, and no other axiom of the ordinary profile: no
-- Collection, no Power Set, no Infinity, no Foundation, no Choice, no LEM. The
-- algebra as Track A's three records. The name layer flat, four items. Track
-- C's two atomic values and Track E's atomic graph, both flat.
--
-- Why the atomic halves are flat rather than records. Track C's
-- `AtomicSemantics` lives inside `K4.Atomic.Atomic`, whose telescope carries
-- the kernel, the support and the weight; naming the record type here would
-- force this module to carry all fifteen of those parameters for the sake of
-- two fields, and the preamble's own reason for flat parameters is that a
-- module application is what put K3's weight join inside a composite signature
-- and hit the 360 second wall. Track E has not landed as this is written, so
-- its record cannot be named at all. Both lists are field for field, so the
-- coordinator passes `AtomicSemantics.eqᴬ as`, `AtomicSemantics.memᴬ as`,
-- `AtomicGraph.eqAtˢ ag` and so on with no adaptation. A flat field list
-- declares no record and so is not the generative hazard.
--
-- The compiler spends exactly two of `AtomicSemantics`'s eight fields. The six
-- universal properties are the atomic laws and belong to Track D; nothing here
-- reads a weight or a support.

module Core
  (sep : Separation)
  (B  : S)
  (L  : Lattice B)
  (Cm : Complement B L)
  (Kc : CodedComplete B L)
  -- The name layer, flat. NameSpace.agda:176, :179, :182-184, :868-870.
  (IsName          : S → Ω)
  (nameAtˢ         : ∀ {n} → Fin n → Fin n → Formula S n)
  (nameΔ           : S → S → Ω)
  (nameAtˢ-reading : ∀ {n} (t w : Fin n) (γ : S ^ n)
                   → (γ ⊨ nameAtˢ t w) ≡ nameΔ (lookup w γ) (lookup t γ))
  (name-adequate   : (t : S)
                   → ((t ∷ B ∷ []) ⊨ nameAtˢ zero (suc zero)) ≡ IsName t)
  -- Track C's AtomicSemantics, the two value fields.
  (eqᴬ  : S → S → Pt B)
  (memᴬ : S → S → Pt B)
  -- Track E's AtomicGraph, flat.
  (eqAtˢ  : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n)
  (memAtˢ : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n)
  (eqΔ  : S → S → S → S → Ω)
  (memΔ : S → S → S → S → Ω)
  (eqAtˢ-reading  : ∀ {n} (b m p w : Fin n) (γ : S ^ n)
                  → (γ ⊨ eqAtˢ b m p w)
                  ≡ eqΔ (lookup w γ) (lookup b γ) (lookup m γ) (lookup p γ))
  (memAtˢ-reading : ∀ {n} (b m p w : Fin n) (γ : S ^ n)
                  → (γ ⊨ memAtˢ b m p w)
                  ≡ memΔ (lookup w γ) (lookup b γ) (lookup m γ) (lookup p γ))
  (eq-sound  : (m p b : S) → ⟨ IsName m ⟩ → ⟨ IsName p ⟩
             → ⟨ eqΔ B b m p ⟩ → ⟨ b ≈ˢ fst (eqᴬ m p) ⟩)
  (eq-total  : (m p : S) → ⟨ IsName m ⟩ → ⟨ IsName p ⟩
             → ⟨ eqΔ B (fst (eqᴬ m p)) m p ⟩)
  (mem-sound : (m p b : S) → ⟨ IsName m ⟩ → ⟨ IsName p ⟩
             → ⟨ memΔ B b m p ⟩ → ⟨ b ≈ˢ fst (memᴬ m p) ⟩)
  (mem-total : (m p : S) → ⟨ IsName m ⟩ → ⟨ IsName p ⟩
             → ⟨ memΔ B (fst (memᴬ m p)) m p ⟩)
  where

  open K4.Infinitary 𝒮 ext paths B L Cm Kc
  module VSet = K4.ValueSets 𝒮 ext paths
  open VSet using ( Fib; collapse-reading )
  module VS = VSet.Core B L Kc
  open VS
    using ( Admits; guarded→admits; sepAdmits
          ; admits-ub; admits-lub; admits-lb; admits-glb
          ; admits-occurs; admits-sound
          ; join-presented; meet-presented )

  -- ---------------------------------------------------------------------
  -- Pinning a ground class to one element of the algebra
  -- ---------------------------------------------------------------------

  -- A ground class PINS an element when it holds of that element's code and of
  -- nothing else. Every internal description this compiler writes is pinning,
  -- and `pins-reading` turns a pinning statement into exactly the equality of
  -- truth values that `Interp.reading` asks for. Note the shape: the element is
  -- a variable of the lemma, so no signature here contains a construction of one
  -- layer applied to a term of another.

  Pins : (S → Ω) → Pt B → Type ℓ
  Pins P m = ⟨ P (fst m) ⟩ × ((q : S) → ⟨ P q ⟩ → ⟨ q ≈ˢ fst m ⟩)

  pins-reading : (P : S → Ω) (m : Pt B) → Pins P m → (q : S) → P q ≡ (q ≈ˢ fst m)
  pins-reading P m (hm , uq) q = ⇔toPath (uq q) bwd
    where
      bwd : ⟨ q ≈ˢ fst m ⟩ → ⟨ P q ⟩
      bwd e = subst (λ w → ⟨ P w ⟩) (sym (≈ˢ-to-path q (fst m) e)) hm

  -- A pinned class determines its element, so two elements pinned by the same
  -- class are equal. This is how the ∃̇ node reconciles the set it builds with
  -- Separation and the set the code quantifies over.

  pins-elem : (P : S → Ω) (m : S) → ⟨ P m ⟩ → (n : Pt B) → Pins P n → m ≡ fst n
  pins-elem P m hm n pn = ≈ˢ-to-path m (fst n) (snd pn m hm)

  -- ---------------------------------------------------------------------
  -- The graph kit is sound: every graph pins its operation
  -- ---------------------------------------------------------------------

  pins-bot : Pins (botΔ B) ⊥ᴮ
  pins-bot = (snd ⊥ᴮ , λ w hw → ⊥-least (w , hw)) , uq
    where
      uq : (q : S) → ⟨ botΔ B q ⟩ → ⟨ q ≈ˢ fst ⊥ᴮ ⟩
      uq q (hq , least) = path-to-≈ˢ q (fst ⊥ᴮ)
        (cong fst (≤ᴮ-antisym {u = q , hq} {v = ⊥ᴮ}
                     (least (fst ⊥ᴮ) (snd ⊥ᴮ)) (⊥-least (q , hq))))

  pins-meet : (u v : Pt B) → Pins (meetΔ B (fst u) (fst v)) (u ⊓ᴮ v)
  pins-meet u v =
    ( snd (u ⊓ᴮ v) , ⊓-lb₁ u v , ⊓-lb₂ u v
    , (λ w hw hu hv → ⊓-glb u v (w , hw) hu hv) ) , uq
    where
      uq : (q : S) → ⟨ meetΔ B (fst u) (fst v) q ⟩ → ⟨ q ≈ˢ fst (u ⊓ᴮ v) ⟩
      uq q (hq , lu , lv , gr) = path-to-≈ˢ q (fst (u ⊓ᴮ v))
        (cong fst (≤ᴮ-antisym {u = q , hq} {v = u ⊓ᴮ v}
                     (⊓-glb u v (q , hq) lu lv)
                     (gr (fst (u ⊓ᴮ v)) (snd (u ⊓ᴮ v)) (⊓-lb₁ u v) (⊓-lb₂ u v))))

  pins-join : (u v : Pt B) → Pins (joinΔ B (fst u) (fst v)) (u ⊔ᴮ v)
  pins-join u v =
    ( snd (u ⊔ᴮ v) , ⊔-ub₁ u v , ⊔-ub₂ u v
    , (λ w hw hu hv → ⊔-lub u v (w , hw) hu hv) ) , uq
    where
      uq : (q : S) → ⟨ joinΔ B (fst u) (fst v) q ⟩ → ⟨ q ≈ˢ fst (u ⊔ᴮ v) ⟩
      uq q (hq , lu , lv , le) = path-to-≈ˢ q (fst (u ⊔ᴮ v))
        (cong fst (≤ᴮ-antisym {u = q , hq} {v = u ⊔ᴮ v}
                     (le (fst (u ⊔ᴮ v)) (snd (u ⊔ᴮ v)) (⊔-ub₁ u v) (⊔-ub₂ u v))
                     (⊔-lub u v (q , hq) lu lv)))

  pins-lub : (X : S) (h : ⟨ X ⊆ˢ B ⟩) → Pins (lubΔ B X) (supᴮ X h)
  pins-lub X h = ( snd (supᴮ X h) , upper , least ) , uq
    where
      upper : ⟨ ubΔ X (fst (supᴮ X h)) ⟩
      upper x hx = sup-ub X h (x , h x hx) hx

      least : (w : S) → ⟨ w ∈ˢ B ⟩ → ⟨ ubΔ X w ⟩ → ⟨ fst (supᴮ X h) ⊆ˢ w ⟩
      least w hw ubw = sup-lub X h (w , hw) (λ p hp → ubw (fst p) hp)

      uq : (q : S) → ⟨ lubΔ B X q ⟩ → ⟨ q ≈ˢ fst (supᴮ X h) ⟩
      uq q (hq , ubq , lq) = path-to-≈ˢ q (fst (supᴮ X h))
        (cong fst (≤ᴮ-antisym {u = q , hq} {v = supᴮ X h}
                     (lq (fst (supᴮ X h)) (snd (supᴮ X h)) upper)
                     (sup-lub X h (q , hq) (λ p hp → ubq (fst p) hp))))

  pins-glb : (X : S) (h : ⟨ X ⊆ˢ B ⟩) → Pins (glbΔ B X) (infᴮ X h)
  pins-glb X h = ( snd (infᴮ X h) , lowerb , great ) , uq
    where
      lowerb : ⟨ lbΔ X (fst (infᴮ X h)) ⟩
      lowerb x hx = inf-lb X h (x , h x hx) hx

      great : (w : S) → ⟨ w ∈ˢ B ⟩ → ⟨ lbΔ X w ⟩ → ⟨ w ⊆ˢ fst (infᴮ X h) ⟩
      great w hw lbw = inf-glb X h (w , hw) (λ p hp → lbw (fst p) hp)

      uq : (q : S) → ⟨ glbΔ B X q ⟩ → ⟨ q ≈ˢ fst (infᴮ X h) ⟩
      uq q (hq , lbq , gq) = path-to-≈ˢ q (fst (infᴮ X h))
        (cong fst (≤ᴮ-antisym {u = q , hq} {v = infᴮ X h}
                     (inf-glb X h (q , hq) (λ p hp → lbq (fst p) hp))
                     (gq (fst (infᴮ X h)) (snd (infᴮ X h)) lowerb)))

  -- The implication. Track A's adjunction says the relative pseudocomplement is
  -- the largest element whose meet with the antecedent lies below the
  -- consequent, and `resΔ` is exactly that side condition read inside the
  -- ground. Neither ¬ᴮ nor its internal description is needed.

  res-of : (u v : Pt B) → ⟨ resΔ B (fst u) (fst v) (fst (u ⇒ᴮ v)) ⟩
  res-of u v =
    ∣ fst ((u ⇒ᴮ v) ⊓ᴮ u) , (fst (pins-meet (u ⇒ᴮ v) u) , ⇒ᴮ-mp u v) ∣₁

  res→≤ : (u v w : Pt B) → ⟨ resΔ B (fst u) (fst v) (fst w) ⟩ → ⟨ w ≤ᴮ (u ⇒ᴮ v) ⟩
  res→≤ u v w = PT.rec (snd (fst w ⊆ˢ fst (u ⇒ᴮ v)))
    (λ { (m , (hm , hmv)) →
           ⇒ᴮ-curry w u v
             (subst (λ z → ⟨ z ⊆ˢ fst v ⟩)
                    (pins-elem (meetΔ B (fst w) (fst u)) m hm (w ⊓ᴮ u)
                               (pins-meet w u))
                    hmv) })

  pins-imp : (u v : Pt B) → Pins (impΔ B (fst u) (fst v)) (u ⇒ᴮ v)
  pins-imp u v =
    ( snd (u ⇒ᴮ v) , res-of u v
    , (λ w hw r → res→≤ u v (w , hw) r) ) , uq
    where
      uq : (q : S) → ⟨ impΔ B (fst u) (fst v) q ⟩ → ⟨ q ≈ˢ fst (u ⇒ᴮ v) ⟩
      uq q (hq , rq , lq) = path-to-≈ˢ q (fst (u ⇒ᴮ v))
        (cong fst (≤ᴮ-antisym {u = q , hq} {v = u ⇒ᴮ v}
                     (res→≤ u v (q , hq) rq)
                     (lq (fst (u ⇒ᴮ v)) (snd (u ⇒ᴮ v)) (res-of u v))))

  -- ---------------------------------------------------------------------
  -- Input, environments, and the one record
  -- ---------------------------------------------------------------------

  -- The compiler reads PARAMETER FREE formulas. The book fixes the convention
  -- and its reason at src/FOL/Syntax.lagda.md:134-160: a syntax whose
  -- constants are all sets is too big to be collected, so whenever formulas
  -- are used as data it is the parameter-free ones that get collected, with
  -- their parameters fed through environments instead. Here the payoff is
  -- immediate and structural. Because the constant domain is empty, every term
  -- of an input formula is a variable, so the bound of a bounded quantifier is
  -- always a slot, and the environment always hands it a NAME.

  Src : ℕ → Type ℓ
  Src k = Formula (⊥* {ℓ}) k

  Name : Type ℓ
  Name = Fib IsName

  Env : ℕ → Type ℓ
  Env k = Vec Name k

  codes : ∀ {k} → Env k → S ^ k
  codes []      = []
  codes (σ ∷ ν) = fst σ ∷ codes ν

  codes-lookup : ∀ {k} (i : Fin k) (ν : Env k)
               → lookup i (codes ν) ≡ fst (lookup i ν)
  codes-lookup zero    (σ ∷ ν) = refl
  codes-lookup (suc i) (σ ∷ ν) = codes-lookup i ν

  -- THE ONE RECORD. Its three fields are the three things a compiled formula
  -- carries: a value in the algebra, an internal formula of the ground, and
  -- the theorem that the second describes the first.
  --
  -- The environment layout, and the one place it departs from architecture
  -- section 1.7. Slot 0 is the value; slot 1 is the algebra carrier B; slots
  -- 2 upward are the codes of the environment's names. The architecture prints
  -- the carrier as a `con` constant and gives `code` the type
  -- `Formula S (suc k)`. That cannot be done here: the name recogniser
  -- `nameAtˢ` and Track E's `eqAtˢ` and `memAtˢ` take a `Fin` for the carrier
  -- argument, not a `Term`, and this module does not build those formulas and
  -- so cannot change their interface. One slot is the whole cost, it is
  -- constant in the formula's size, and `sepAt` freezes it to a constant at
  -- the point of use anyway.
  --
  -- The level is forced. `reading` is a path in Ω, so `Interp` lands at
  -- Type (ℓ-suc ℓ) and can never index a ⋁ or a ⋀. It is consumed as a
  -- hypothesis and produced as a result, never placed inside a join. The index
  -- `φ` is a phantom: it names the formula a value belongs to and no field
  -- mentions it, which is exactly what keeps rule 3 away from this type.

  record Interp {k : ℕ} (φ : Src k) : Type (ℓ-suc ℓ) where
    field
      val     : Env k → Pt B
      code    : Formula S (suc (suc k))
      reading : (ν : Env k) (b : S)
              → ((b ∷ B ∷ codes ν) ⊨ code) ≡ (b ≈ˢ fst (val ν))

  -- ---------------------------------------------------------------------
  -- The renamings, and their environment agreements
  -- ---------------------------------------------------------------------

  -- Rule 8 in force: there is no formula substitution in this tree and none is
  -- built here. Going under a binder is renaming, every slot is a Fin, and
  -- every agreement below is four lines of `refl` because the layouts were
  -- chosen to make it so. Freezing an environment to constants happens exactly
  -- once, at `sepAt`, and only at the point where Separation needs a
  -- `Formula S 1`.

  wk₂ : ∀ {k} → Fin k → Fin (suc (suc k))
  wk₂ i = suc (suc i)

  -- One slot inserted after the value: b ∷ B ∷ cs  ↦  p ∷ b ∷ B ∷ cs.
  ρ₁ : ∀ {k} → Fin (suc (suc k)) → Fin (suc (suc (suc k)))
  ρ₁ zero    = zero
  ρ₁ (suc i) = suc (suc i)

  ag₁ : ∀ {k} (p b : S) (cs : S ^ k) → Agrees ρ₁ (p ∷ b ∷ B ∷ cs) (p ∷ B ∷ cs)
  ag₁ p b cs zero    = refl
  ag₁ p b cs (suc i) = refl

  -- Two slots inserted after the value.
  ρ₂ : ∀ {k} → Fin (suc (suc k)) → Fin (suc (suc (suc (suc k))))
  ρ₂ zero    = zero
  ρ₂ (suc i) = suc (suc (suc i))

  ag₂ : ∀ {k} (q p b : S) (cs : S ^ k)
      → Agrees ρ₂ (q ∷ p ∷ b ∷ B ∷ cs) (q ∷ B ∷ cs)
  ag₂ q p b cs zero    = refl
  ag₂ q p b cs (suc i) = refl

  -- The subformula of a quantifier node is read at the environment
  -- b ∷ B ∷ t ∷ cs, where t is the bound name's code; the node reads it at
  -- t ∷ x ∷ B ∷ cs, where the bound name has moved to the front.
  ρΨ : ∀ {k} → Fin (suc (suc (suc k))) → Fin (suc (suc (suc k)))
  ρΨ zero                = suc zero
  ρΨ (suc zero)          = suc (suc zero)
  ρΨ (suc (suc zero))    = zero
  ρΨ (suc (suc (suc i))) = suc (suc (suc i))

  agΨ : ∀ {k} (t x : S) (cs : S ^ k)
      → Agrees ρΨ (t ∷ x ∷ B ∷ cs) (x ∷ B ∷ t ∷ cs)
  agΨ t x cs zero                = refl
  agΨ t x cs (suc zero)          = refl
  agΨ t x cs (suc (suc zero))    = refl
  agΨ t x cs (suc (suc (suc i))) = refl

  -- The same move for a bounded quantifier node, which carries two more
  -- witnesses: the value of the membership and the value of the body.
  ρ∈ : ∀ {k} → Fin (suc (suc (suc k)))
             → Fin (suc (suc (suc (suc (suc k)))))
  ρ∈ zero                = zero
  ρ∈ (suc zero)          = suc (suc (suc (suc zero)))
  ρ∈ (suc (suc zero))    = suc (suc zero)
  ρ∈ (suc (suc (suc i))) = suc (suc (suc (suc (suc i))))

  ag∈ : ∀ {k} (q p t x : S) (cs : S ^ k)
      → Agrees ρ∈ (q ∷ p ∷ t ∷ x ∷ B ∷ cs) (q ∷ B ∷ t ∷ cs)
  ag∈ q p t x cs zero                = refl
  ag∈ q p t x cs (suc zero)          = refl
  ag∈ q p t x cs (suc (suc zero))    = refl
  ag∈ q p t x cs (suc (suc (suc i))) = refl

  -- ---------------------------------------------------------------------
  -- The name recogniser, read at the carrier
  -- ---------------------------------------------------------------------

  -- The one fact this module takes from the name layer. Note what it is NOT:
  -- it is not absoluteness of `IsName` and it is not a bound on names. K3's
  -- own note at NameSpace.agda:167-175 records that the recogniser carries one
  -- unbounded existential and that no Δ₀ witness exists for it. The compiler
  -- does not need one, because the recogniser appears only inside a Separation
  -- instance in the ground and Separation accepts any Formula S 1.

  name-read : (t : S) → nameΔ B t ≡ IsName t
  name-read t =
    sym (nameAtˢ-reading zero (suc zero) (t ∷ B ∷ [])) ∙ name-adequate t

  -- ---------------------------------------------------------------------
  -- The two-argument node, once
  -- ---------------------------------------------------------------------

  -- The conjunction, disjunction and implication nodes differ only in which
  -- graph formula they close with, so the code shape and its reading are
  -- written once here. Read the code aloud: "there is a p which is the value
  -- of the left subformula, and a q which is the value of the right one, and
  -- the value slot stands to p and q in the graph of the operation".
  --
  -- The reading is where `pin-elim` earns its place. A compiled code cannot
  -- name the value of a subformula, because a formula has no access to a host
  -- term; it can only quantify over a slot and say that the slot is that
  -- value. `pin-elim` reads such a quantification back as the value itself.

  binCode : ∀ {k} → Formula S (suc (suc k)) → Formula S (suc (suc k))
          → Formula S (suc (suc (suc (suc k)))) → Formula S (suc (suc k))
  binCode c d g = ∃̇ (renameFo ρ₁ c ∧̇ ∃̇ (renameFo ρ₂ d ∧̇ g))

  binCode-reading :
    ∀ {k} (c d : Formula S (suc (suc k)))
      (g : Formula S (suc (suc (suc (suc k)))))
      (G : S → S → S → Ω) (cs : S ^ k) (u v : Pt B)
    → ((x : S) → ((x ∷ B ∷ cs) ⊨ c) ≡ (x ≈ˢ fst u))
    → ((x : S) → ((x ∷ B ∷ cs) ⊨ d) ≡ (x ≈ˢ fst v))
    → ((p q x : S) → ((q ∷ p ∷ x ∷ B ∷ cs) ⊨ g) ≡ G p q x)
    → (op : Pt B → Pt B → Pt B)
    → ((y z : Pt B) → Pins (G (fst y) (fst z)) (op y z))
    → (b : S) → ((b ∷ B ∷ cs) ⊨ binCode c d g) ≡ (b ≈ˢ fst (op u v))
  binCode-reading c d g G cs u v rc rd rg op pg b =
      cong (⋁ S) (funExt outer)
    ∙ pin-elim (fst u) (λ p → G p (fst v) b)
    ∙ pins-reading (G (fst u) (fst v)) (op u v) (pg u v) b
    where
      inner : (p : S)
            → (⋁ S (λ q → ((q ∷ p ∷ b ∷ B ∷ cs) ⊨ renameFo ρ₂ d)
                          ⊓ ((q ∷ p ∷ b ∷ B ∷ cs) ⊨ g)))
              ≡ G p (fst v) b
      inner p = cong (⋁ S) (funExt (λ q →
                  cong₂ _⊓_
                    (⊨-rename ρ₂ d (q ∷ p ∷ b ∷ B ∷ cs) (q ∷ B ∷ cs)
                       (ag₂ q p b cs) ∙ rd q)
                    (rg p q b)))
              ∙ pin-elim (fst v) (λ q → G p q b)

      outer : (p : S)
            → (((p ∷ b ∷ B ∷ cs) ⊨ renameFo ρ₁ c)
               ⊓ (⋁ S (λ q → ((q ∷ p ∷ b ∷ B ∷ cs) ⊨ renameFo ρ₂ d)
                             ⊓ ((q ∷ p ∷ b ∷ B ∷ cs) ⊨ g))))
              ≡ ((p ≈ˢ fst u) ⊓ G p (fst v) b)
      outer p = cong₂ _⊓_
                  (⊨-rename ρ₁ c (p ∷ b ∷ B ∷ cs) (p ∷ B ∷ cs)
                     (ag₁ p b cs) ∙ rc p)
                  (inner p)

  -- ---------------------------------------------------------------------
  -- The quantifier node, once
  -- ---------------------------------------------------------------------

  -- The internal code of a quantifier node. Read aloud: "there is a set V
  -- whose members are exactly the members of the carrier satisfying the
  -- matrix, and the value slot is the least upper bound of V inside the
  -- carrier". The existential over V is genuinely needed: the value set is
  -- produced by Separation in the ground, and the code has no term for it.
  --
  -- No Δ₀ witness is claimed or claimable for this code. The matrix contains
  -- the name recogniser, whose leading quantifier is unbounded, and the
  -- quantifier over V is unbounded as well.

  inBˢ : ∀ {k} → Formula S (suc (suc (suc (suc k))))
  inBˢ = var zero ∈̇ var (suc (suc (suc zero)))

  setOfˢ : ∀ {k} → Formula S (suc (suc k)) → Formula S (suc (suc (suc k)))
  setOfˢ Ψ =
    ∀̇ ( ((var zero ∈̇ var (suc zero)) ⇒̇ (inBˢ ∧̇ renameFo ρ₂ Ψ))
      ∧̇ ((inBˢ ∧̇ renameFo ρ₂ Ψ) ⇒̇ (var zero ∈̇ var (suc zero))) )

  supCodeˢ infCodeˢ : ∀ {k} → Formula S (suc (suc k)) → Formula S (suc (suc k))
  supCodeˢ Ψ = ∃̇ (setOfˢ Ψ ∧̇ lubAtˢ (suc (suc zero)) zero (suc zero))
  infCodeˢ Ψ = ∃̇ (setOfˢ Ψ ∧̇ glbAtˢ (suc (suc zero)) zero (suc zero))

  -- The reading of a quantifier node, for the join. Everything the node needs
  -- from the outside is here: the matrix reads as the attained class of the
  -- family, and the family is admitted. Track B's `guarded→admits` is what
  -- makes the forward direction go: the internal set the code quantifies over
  -- arrives with the membership guard that Separation always puts there, and
  -- the guard is redundant because the family takes its values in the algebra.
  -- Track B's `join-presented` is what identifies the code's set with the one
  -- the recursion built, with no comparison of the two constructions.

  sup-code-reading :
    ∀ {k} (Ψ : Formula S (suc (suc k))) (cs : S ^ k)
      {I : Type ℓ} {f : I → Pt B}
    → ((x : S) → ((x ∷ B ∷ cs) ⊨ Ψ) ≡ ⋁ I (λ i → x ≈ˢ fst (f i)))
    → (a : Admits f)
    → (b : S)
    → ((b ∷ B ∷ cs) ⊨ supCodeˢ Ψ)
      ≡ (b ≈ˢ fst (supᴮ (Admits.values a) (Admits.values-sub a)))
  sup-code-reading Ψ cs {I} {f} rΨ a b = ⇔toPath fwd bwd
    where
      tgt : Pt B
      tgt = supᴮ (Admits.values a) (Admits.values-sub a)

      cls : (V x : S) → ((x ∷ V ∷ b ∷ B ∷ cs) ⊨ renameFo ρ₂ Ψ)
                      ≡ ⋁ I (λ i → x ≈ˢ fst (f i))
      cls V x = ⊨-rename ρ₂ Ψ (x ∷ V ∷ b ∷ B ∷ cs) (x ∷ B ∷ cs)
                  (ag₂ x V b cs) ∙ rΨ x

      fwd : ⟨ (b ∷ B ∷ cs) ⊨ supCodeˢ Ψ ⟩ → ⟨ b ≈ˢ fst tgt ⟩
      fwd = PT.rec (snd (b ≈ˢ fst tgt))
        (λ { (V , (setV , lubV)) →
               let gspec : (x : S) → (x ∈ˢ V)
                                   ≡ ((x ∈ˢ B) ⊓ ⋁ I (λ i → x ≈ˢ fst (f i)))
                   gspec x = ⇔toPath
                     (λ hx → setV x .fst hx .fst
                           , subst ⟨_⟩ (cls V x) (setV x .fst hx .snd))
                     (λ r → setV x .snd
                              (r .fst , subst ⟨_⟩ (sym (cls V x)) (r .snd)))
                   aV : Admits f
                   aV = guarded→admits V gspec
                in path-to-≈ˢ b (fst tgt)
                     ( pins-elem (lubΔ B V) b lubV
                         (supᴮ V (Admits.values-sub aV))
                         (pins-lub V (Admits.values-sub aV))
                     ∙ cong fst (join-presented aV a
                         (λ x → same (⋁ I (λ i → x ≈ˢ fst (f i))))) ) })

      bwd : ⟨ b ≈ˢ fst tgt ⟩ → ⟨ (b ∷ B ∷ cs) ⊨ supCodeˢ Ψ ⟩
      bwd e = ∣ Admits.values a , (setV , lubV) ∣₁
        where
          V : S
          V = Admits.values a

          setV : ⟨ (V ∷ b ∷ B ∷ cs) ⊨ setOfˢ Ψ ⟩
          setV x =
              (λ hx → Admits.values-sub a x hx
                    , subst ⟨_⟩ (sym (cls V x))
                        (subst ⟨_⟩ (Admits.attained a x) hx))
            , (λ r → subst ⟨_⟩ (sym (Admits.attained a x))
                       (subst ⟨_⟩ (cls V x) (r .snd)))

          lubV : ⟨ lubΔ B V b ⟩
          lubV = subst (λ w → ⟨ lubΔ B V w ⟩)
                   (sym (≈ˢ-to-path b (fst tgt) e))
                   (fst (pins-lub V (Admits.values-sub a)))

  inf-code-reading :
    ∀ {k} (Ψ : Formula S (suc (suc k))) (cs : S ^ k)
      {I : Type ℓ} {f : I → Pt B}
    → ((x : S) → ((x ∷ B ∷ cs) ⊨ Ψ) ≡ ⋁ I (λ i → x ≈ˢ fst (f i)))
    → (a : Admits f)
    → (b : S)
    → ((b ∷ B ∷ cs) ⊨ infCodeˢ Ψ)
      ≡ (b ≈ˢ fst (infᴮ (Admits.values a) (Admits.values-sub a)))
  inf-code-reading Ψ cs {I} {f} rΨ a b = ⇔toPath fwd bwd
    where
      tgt : Pt B
      tgt = infᴮ (Admits.values a) (Admits.values-sub a)

      cls : (V x : S) → ((x ∷ V ∷ b ∷ B ∷ cs) ⊨ renameFo ρ₂ Ψ)
                      ≡ ⋁ I (λ i → x ≈ˢ fst (f i))
      cls V x = ⊨-rename ρ₂ Ψ (x ∷ V ∷ b ∷ B ∷ cs) (x ∷ B ∷ cs)
                  (ag₂ x V b cs) ∙ rΨ x

      fwd : ⟨ (b ∷ B ∷ cs) ⊨ infCodeˢ Ψ ⟩ → ⟨ b ≈ˢ fst tgt ⟩
      fwd = PT.rec (snd (b ≈ˢ fst tgt))
        (λ { (V , (setV , glbV)) →
               let gspec : (x : S) → (x ∈ˢ V)
                                   ≡ ((x ∈ˢ B) ⊓ ⋁ I (λ i → x ≈ˢ fst (f i)))
                   gspec x = ⇔toPath
                     (λ hx → setV x .fst hx .fst
                           , subst ⟨_⟩ (cls V x) (setV x .fst hx .snd))
                     (λ r → setV x .snd
                              (r .fst , subst ⟨_⟩ (sym (cls V x)) (r .snd)))
                   aV : Admits f
                   aV = guarded→admits V gspec
                in path-to-≈ˢ b (fst tgt)
                     ( pins-elem (glbΔ B V) b glbV
                         (infᴮ V (Admits.values-sub aV))
                         (pins-glb V (Admits.values-sub aV))
                     ∙ cong fst (meet-presented aV a
                         (λ x → same (⋁ I (λ i → x ≈ˢ fst (f i))))) ) })

      bwd : ⟨ b ≈ˢ fst tgt ⟩ → ⟨ (b ∷ B ∷ cs) ⊨ infCodeˢ Ψ ⟩
      bwd e = ∣ Admits.values a , (setV , glbV) ∣₁
        where
          V : S
          V = Admits.values a

          setV : ⟨ (V ∷ b ∷ B ∷ cs) ⊨ setOfˢ Ψ ⟩
          setV x =
              (λ hx → Admits.values-sub a x hx
                    , subst ⟨_⟩ (sym (cls V x))
                        (subst ⟨_⟩ (Admits.attained a x) hx))
            , (λ r → subst ⟨_⟩ (sym (Admits.attained a x))
                       (subst ⟨_⟩ (cls V x) (r .snd)))

          glbV : ⟨ glbΔ B V b ⟩
          glbV = subst (λ w → ⟨ glbΔ B V w ⟩)
                   (sym (≈ˢ-to-path b (fst tgt) e))
                   (fst (pins-glb V (Admits.values-sub a)))

  -- ---------------------------------------------------------------------
  -- The two atomic graphs, as pinning statements
  -- ---------------------------------------------------------------------

  -- Track E's contract ships soundness and totality separately, which is the
  -- right shape: soundness alone would leave the graph possibly empty and
  -- totality alone would leave it possibly too big. Together they say the
  -- graph pins the value, and that is what a reading theorem is. Note that
  -- both halves carry the recognition hypotheses on their face. Nothing here
  -- claims a value for a code that is not a name.

  eq-pins : (σ τ : Name) → Pins (λ b → eqΔ B b (fst σ) (fst τ))
                                (eqᴬ (fst σ) (fst τ))
  eq-pins σ τ = eq-total (fst σ) (fst τ) (snd σ) (snd τ)
              , (λ b h → eq-sound (fst σ) (fst τ) b (snd σ) (snd τ) h)

  mem-pins : (σ τ : Name) → Pins (λ b → memΔ B b (fst σ) (fst τ))
                                 (memᴬ (fst σ) (fst τ))
  mem-pins σ τ = mem-total (fst σ) (fst τ) (snd σ) (snd τ)
               , (λ b h → mem-sound (fst σ) (fst τ) b (snd σ) (snd τ) h)

  -- The environment's names, addressed by their codes. Every slot of a
  -- parameter-free formula is a Fin, so this is the only lookup the compiler
  -- performs, and it carries the recognition proof along with the code.

  nameAt : ∀ {k} (i : Fin k) (ν : Env k) → Name
  nameAt i ν = lookup i (codes ν)
             , subst (λ w → ⟨ IsName w ⟩) (sym (codes-lookup i ν))
                 (snd (lookup i ν))

  -- ---------------------------------------------------------------------
  -- The two matrices of a quantifier node
  -- ---------------------------------------------------------------------

  -- `Ψplain` is the attained class of an unbounded quantifier: the values the
  -- body takes as its bound variable ranges over the names. `Ψbound` is the
  -- attained class of a bounded one: the values of the body combined, by the
  -- node's own operation, with the atomic value of the membership.
  --
  -- Both cross the same gap, and it is the gap Track B measured. A formula
  -- cannot bind a recognition proof, so the matrix reads as a join over the
  -- CARRIER guarded by the recogniser; the body's value at a name does mention
  -- the proof, because a name is a code together with its recognition. The two
  -- are identified in one step by `collapse-reading`, whose hypothesis is
  -- exactly a reading theorem. The architecture's `collapse`, stated only at
  -- membership in a code, does not reach here: `IsName` is a class on the
  -- carrier and is not `(_∈ˢ a)` for any a.

  Ψplain : ∀ {k} → Formula S (suc (suc (suc k))) → Formula S (suc (suc k))
  Ψplain c = ∃̇ (nameAtˢ zero (suc (suc zero)) ∧̇ renameFo ρΨ c)

  Ψplain-reading :
    ∀ {k} (c : Formula S (suc (suc (suc k)))) (cs : S ^ k) (f : Name → Pt B)
    → ((σ : Name) (x : S) → ((x ∷ B ∷ fst σ ∷ cs) ⊨ c) ≡ (x ≈ˢ fst (f σ)))
    → (x : S) → ((x ∷ B ∷ cs) ⊨ Ψplain c) ≡ ⋁ Name (λ σ → x ≈ˢ fst (f σ))
  Ψplain-reading c cs f rc x =
      cong (⋁ S) (funExt (λ t → cong (λ P → P ⊓ R t)
        ( nameAtˢ-reading zero (suc (suc zero)) (t ∷ x ∷ B ∷ cs)
        ∙ name-read t )))
    ∙ collapse-reading IsName R (λ t h → x ≈ˢ fst (f (t , h)))
        (λ t h → ⊨-rename ρΨ c (t ∷ x ∷ B ∷ cs) (x ∷ B ∷ t ∷ cs)
                   (agΨ t x cs) ∙ rc (t , h) x)
    where
      R : S → Ω
      R t = (t ∷ x ∷ B ∷ cs) ⊨ renameFo ρΨ c

  wk₄ : ∀ {k} → Fin k → Fin (suc (suc (suc (suc k))))
  wk₄ i = suc (suc (suc (suc i)))

  Ψbound : ∀ {k} (i : Fin k) (c : Formula S (suc (suc (suc k))))
           (g : Formula S (suc (suc (suc (suc (suc k))))))
         → Formula S (suc (suc k))
  Ψbound i c g =
    ∃̇ ( nameAtˢ zero (suc (suc zero))
      ∧̇ ∃̇ ( memAtˢ zero (suc zero) (wk₄ i) (suc (suc (suc zero)))
         ∧̇ ∃̇ ( renameFo ρ∈ c ∧̇ g ) ) )

  Ψbound-reading :
    ∀ {k} (i : Fin k) (c : Formula S (suc (suc (suc k))))
      (g : Formula S (suc (suc (suc (suc (suc k))))))
      (cs : S ^ k) (f : Name → Pt B) (G : S → S → S → Ω)
      (op : Pt B → Pt B → Pt B) (hn : ⟨ IsName (lookup i cs) ⟩)
    → ((σ : Name) (x : S) → ((x ∷ B ∷ fst σ ∷ cs) ⊨ c) ≡ (x ≈ˢ fst (f σ)))
    → ((p q t x : S) → ((q ∷ p ∷ t ∷ x ∷ B ∷ cs) ⊨ g) ≡ G p q x)
    → ((y z : Pt B) → Pins (G (fst y) (fst z)) (op y z))
    → (x : S) → ((x ∷ B ∷ cs) ⊨ Ψbound i c g)
              ≡ ⋁ Name (λ σ → x ≈ˢ fst (op (memᴬ (fst σ) (lookup i cs)) (f σ)))
  Ψbound-reading i c g cs f G op hn rc rg pg x =
      cong (⋁ S) (funExt (λ t → cong (λ P → P ⊓ R t)
        ( nameAtˢ-reading zero (suc (suc zero)) (t ∷ x ∷ B ∷ cs)
        ∙ name-read t )))
    ∙ collapse-reading IsName R
        (λ t h → x ≈ˢ fst (op (memᴬ t (lookup i cs)) (f (t , h)))) rd
    where
      R : S → Ω
      R t = ⋁ S (λ p →
              ((p ∷ t ∷ x ∷ B ∷ cs)
                 ⊨ memAtˢ zero (suc zero) (wk₄ i) (suc (suc (suc zero))))
              ⊓ (⋁ S (λ q → ((q ∷ p ∷ t ∷ x ∷ B ∷ cs) ⊨ renameFo ρ∈ c)
                            ⊓ ((q ∷ p ∷ t ∷ x ∷ B ∷ cs) ⊨ g))))

      rd : (t : S) (h : ⟨ IsName t ⟩)
         → R t ≡ (x ≈ˢ fst (op (memᴬ t (lookup i cs)) (f (t , h))))
      rd t h =
          cong (⋁ S) (funExt (λ p → cong₂ _⊓_ (memstep p) (innerq p)))
        ∙ pin-elim (fst (memᴬ t (lookup i cs)))
            (λ p → G p (fst (f (t , h))) x)
        ∙ pins-reading (G (fst (memᴬ t (lookup i cs))) (fst (f (t , h))))
            (op (memᴬ t (lookup i cs)) (f (t , h)))
            (pg (memᴬ t (lookup i cs)) (f (t , h))) x
        where
          memstep : (p : S)
                  → ((p ∷ t ∷ x ∷ B ∷ cs)
                       ⊨ memAtˢ zero (suc zero) (wk₄ i) (suc (suc (suc zero))))
                    ≡ (p ≈ˢ fst (memᴬ t (lookup i cs)))
          memstep p =
              memAtˢ-reading zero (suc zero) (wk₄ i) (suc (suc (suc zero)))
                (p ∷ t ∷ x ∷ B ∷ cs)
            ∙ pins-reading (λ w → memΔ B w t (lookup i cs))
                (memᴬ t (lookup i cs))
                (mem-pins (t , h) (lookup i cs , hn)) p

          innerq : (p : S)
                 → (⋁ S (λ q → ((q ∷ p ∷ t ∷ x ∷ B ∷ cs) ⊨ renameFo ρ∈ c)
                               ⊓ ((q ∷ p ∷ t ∷ x ∷ B ∷ cs) ⊨ g)))
                   ≡ G p (fst (f (t , h))) x
          innerq p =
              cong (⋁ S) (funExt (λ q → cong₂ _⊓_
                ( ⊨-rename ρ∈ c (q ∷ p ∷ t ∷ x ∷ B ∷ cs) (q ∷ B ∷ t ∷ cs)
                    (ag∈ q p t x cs) ∙ rc (t , h) q )
                ( rg p q t x )))
            ∙ pin-elim (fst (f (t , h))) (λ q → G p q x)

  -- ---------------------------------------------------------------------
  -- The quantifier node's three ingredients, named
  -- ---------------------------------------------------------------------

  -- The family, its matrix reading and its admission are top level rather than
  -- local to the recursion's clauses, for one reason that is worth stating:
  -- the per-constructor laws below have to NAME the admitted family they are
  -- about, and a `where` bound definition has no name outside its clause. Each
  -- takes an `Interp` value rather than a formula, so none of them is part of
  -- the recursion and none of them mentions `interp`.

  famP : ∀ {k} {φ : Src (suc k)} (iφ : Interp φ) (ν : Env k) → Name → Pt B
  famP iφ ν σ = Interp.val iφ (σ ∷ ν)

  ΨrP : ∀ {k} {φ : Src (suc k)} (iφ : Interp φ) (ν : Env k) (x : S)
      → ((x ∷ B ∷ codes ν) ⊨ Ψplain (Interp.code iφ))
        ≡ ⋁ Name (λ σ → x ≈ˢ fst (famP iφ ν σ))
  ΨrP iφ ν = Ψplain-reading (Interp.code iφ) (codes ν) (famP iφ ν)
               (λ σ x → Interp.reading iφ (σ ∷ ν) x)

  admP : ∀ {k} {φ : Src (suc k)} (iφ : Interp φ) (ν : Env k)
       → Admits (famP iφ ν)
  admP iφ ν = sepAdmits sep (sepAt (Ψplain (Interp.code iφ)) (B ∷ codes ν))
                (λ x → sepAt-reading (Ψplain (Interp.code iφ)) (B ∷ codes ν) x
                     ∙ ΨrP iφ ν x)

  -- The bounded pair. `gMeet` closes the existential node, `gImp` the
  -- universal one; Bell's Corollary 1.18 is what says the first is a join and
  -- the second a meet of the same shape, and this is the only place the two
  -- differ.

  gMeet gImp : ∀ {k} → Formula S (suc (suc (suc (suc (suc k)))))
  gMeet = meetAtˢ (suc (suc (suc (suc zero)))) (suc zero) zero
                  (suc (suc (suc zero)))
  gImp  = impAtˢ (suc (suc (suc (suc zero)))) (suc zero) zero
                 (suc (suc (suc zero)))

  famM famI : ∀ {k} {φ : Src (suc k)} (iφ : Interp φ) (i : Fin k) (ν : Env k)
            → Name → Pt B
  famM iφ i ν σ = memᴬ (fst σ) (lookup i (codes ν)) ⊓ᴮ Interp.val iφ (σ ∷ ν)
  famI iφ i ν σ = memᴬ (fst σ) (lookup i (codes ν)) ⇒ᴮ Interp.val iφ (σ ∷ ν)

  ΨrM : ∀ {k} {φ : Src (suc k)} (iφ : Interp φ) (i : Fin k) (ν : Env k) (x : S)
      → ((x ∷ B ∷ codes ν) ⊨ Ψbound i (Interp.code iφ) gMeet)
        ≡ ⋁ Name (λ σ → x ≈ˢ fst (famM iφ i ν σ))
  ΨrM iφ i ν = Ψbound-reading i (Interp.code iφ) gMeet (codes ν)
                 (λ σ → Interp.val iφ (σ ∷ ν)) (λ p q x → meetΔ B p q x)
                 _⊓ᴮ_ (snd (nameAt i ν))
                 (λ σ x → Interp.reading iφ (σ ∷ ν) x)
                 (λ p q t x → meetAtˢ-reading (suc (suc (suc (suc zero))))
                                (suc zero) zero (suc (suc (suc zero)))
                                (q ∷ p ∷ t ∷ x ∷ B ∷ codes ν))
                 pins-meet

  ΨrI : ∀ {k} {φ : Src (suc k)} (iφ : Interp φ) (i : Fin k) (ν : Env k) (x : S)
      → ((x ∷ B ∷ codes ν) ⊨ Ψbound i (Interp.code iφ) gImp)
        ≡ ⋁ Name (λ σ → x ≈ˢ fst (famI iφ i ν σ))
  ΨrI iφ i ν = Ψbound-reading i (Interp.code iφ) gImp (codes ν)
                 (λ σ → Interp.val iφ (σ ∷ ν)) (λ p q x → impΔ B p q x)
                 _⇒ᴮ_ (snd (nameAt i ν))
                 (λ σ x → Interp.reading iφ (σ ∷ ν) x)
                 (λ p q t x → impAtˢ-reading (suc (suc (suc (suc zero))))
                                (suc zero) zero (suc (suc (suc zero)))
                                (q ∷ p ∷ t ∷ x ∷ B ∷ codes ν))
                 pins-imp

  admM : ∀ {k} {φ : Src (suc k)} (iφ : Interp φ) (i : Fin k) (ν : Env k)
       → Admits (famM iφ i ν)
  admM iφ i ν = sepAdmits sep
                  (sepAt (Ψbound i (Interp.code iφ) gMeet) (B ∷ codes ν))
                  (λ x → sepAt-reading (Ψbound i (Interp.code iφ) gMeet)
                           (B ∷ codes ν) x ∙ ΨrM iφ i ν x)

  admI : ∀ {k} {φ : Src (suc k)} (iφ : Interp φ) (i : Fin k) (ν : Env k)
       → Admits (famI iφ i ν)
  admI iφ i ν = sepAdmits sep
                  (sepAt (Ψbound i (Interp.code iφ) gImp) (B ∷ codes ν))
                  (λ x → sepAt-reading (Ψbound i (Interp.code iφ) gImp)
                           (B ∷ codes ν) x ∙ ΨrI iφ i ν x)

  -- ---------------------------------------------------------------------
  -- The compiler
  -- ---------------------------------------------------------------------

  -- ONE total structural recursion over the ten constructors of FOL.Syntax,
  -- run in the HOST. `¬̇` and `⊤̇` are derived there (Syntax.lagda.md:108,:111),
  -- so there are ten cases and not twelve, and the two derived spellings are
  -- compiled by the `⇒̇` and `⊥̇` clauses with no extra work.
  --
  -- What makes it total, and why there is no admission datum. At a quantifier
  -- node the value set is a Separation instance and its attainment law is a
  -- THEOREM from the subformula's reading, proved by Track B and checked in
  -- Track B's own probe. So no `Data φ` family is carried, no
  -- induction-recursion is needed, and obstruction O3 stays closed: K13 gets a
  -- `Pt B` for every formula with no per-formula side condition.
  --
  -- What it is NOT. It is not an internal function of a coded formula, and
  -- there is no code of a formula anywhere in a term. Bell page 24, quoted at
  -- the head of this file, forbids exactly that, and the absence is
  -- grep-checkable: no `⌜`, no `Codes`, no `import FOL.Coding`.

  interp : ∀ {k} (φ : Src k) → Interp φ

  -- The two atomic nodes. Everything here is Track E's contract read back;
  -- this file proves no atomic law and reads no weight and no support. The
  -- recognition proofs travel with the codes, through `nameAt`, because
  -- Track E's soundness and totality carry them on their face.

  interp (var i ∈̇ var j) = record
    { val     = λ ν → memᴬ (lookup i (codes ν)) (lookup j (codes ν))
    ; code    = memAtˢ zero (wk₂ i) (wk₂ j) (suc zero)
    ; reading = λ ν b →
        memAtˢ-reading zero (wk₂ i) (wk₂ j) (suc zero) (b ∷ B ∷ codes ν)
        ∙ pins-reading
            (λ w → memΔ B w (lookup i (codes ν)) (lookup j (codes ν)))
            (memᴬ (lookup i (codes ν)) (lookup j (codes ν)))
            (mem-pins (nameAt i ν) (nameAt j ν)) b }
  interp (var i ∈̇ con ())
  interp (con () ∈̇ u)

  interp (var i ≐ var j) = record
    { val     = λ ν → eqᴬ (lookup i (codes ν)) (lookup j (codes ν))
    ; code    = eqAtˢ zero (wk₂ i) (wk₂ j) (suc zero)
    ; reading = λ ν b →
        eqAtˢ-reading zero (wk₂ i) (wk₂ j) (suc zero) (b ∷ B ∷ codes ν)
        ∙ pins-reading
            (λ w → eqΔ B w (lookup i (codes ν)) (lookup j (codes ν)))
            (eqᴬ (lookup i (codes ν)) (lookup j (codes ν)))
            (eq-pins (nameAt i ν) (nameAt j ν)) b }
  interp (var i ≐ con ())
  interp (con () ≐ u)

  -- The three binary connectives, Bell (1.8), (1.11) and (1.12). Each is the
  -- shared two-argument node closed with its own graph.

  interp {k} (φ ∧̇ ψ) = record
    { val     = λ ν → Interp.val (interp φ) ν ⊓ᴮ Interp.val (interp ψ) ν
    ; code    = binCode (Interp.code (interp φ)) (Interp.code (interp ψ)) g
    ; reading = λ ν b →
        binCode-reading (Interp.code (interp φ)) (Interp.code (interp ψ)) g
          (λ p q x → meetΔ B p q x) (codes ν)
          (Interp.val (interp φ) ν) (Interp.val (interp ψ) ν)
          (Interp.reading (interp φ) ν) (Interp.reading (interp ψ) ν)
          (λ p q x → meetAtˢ-reading (suc (suc (suc zero))) (suc zero) zero
                       (suc (suc zero)) (q ∷ p ∷ x ∷ B ∷ codes ν))
          _⊓ᴮ_ pins-meet b }
    where
      g : Formula S (suc (suc (suc (suc k))))
      g = meetAtˢ (suc (suc (suc zero))) (suc zero) zero (suc (suc zero))

  interp {k} (φ ∨̇ ψ) = record
    { val     = λ ν → Interp.val (interp φ) ν ⊔ᴮ Interp.val (interp ψ) ν
    ; code    = binCode (Interp.code (interp φ)) (Interp.code (interp ψ)) g
    ; reading = λ ν b →
        binCode-reading (Interp.code (interp φ)) (Interp.code (interp ψ)) g
          (λ p q x → joinΔ B p q x) (codes ν)
          (Interp.val (interp φ) ν) (Interp.val (interp ψ) ν)
          (Interp.reading (interp φ) ν) (Interp.reading (interp ψ) ν)
          (λ p q x → joinAtˢ-reading (suc (suc (suc zero))) (suc zero) zero
                       (suc (suc zero)) (q ∷ p ∷ x ∷ B ∷ codes ν))
          _⊔ᴮ_ pins-join b }
    where
      g : Formula S (suc (suc (suc (suc k))))
      g = joinAtˢ (suc (suc (suc zero))) (suc zero) zero (suc (suc zero))

  interp {k} (φ ⇒̇ ψ) = record
    { val     = λ ν → Interp.val (interp φ) ν ⇒ᴮ Interp.val (interp ψ) ν
    ; code    = binCode (Interp.code (interp φ)) (Interp.code (interp ψ)) g
    ; reading = λ ν b →
        binCode-reading (Interp.code (interp φ)) (Interp.code (interp ψ)) g
          (λ p q x → impΔ B p q x) (codes ν)
          (Interp.val (interp φ) ν) (Interp.val (interp ψ) ν)
          (Interp.reading (interp φ) ν) (Interp.reading (interp ψ) ν)
          (λ p q x → impAtˢ-reading (suc (suc (suc zero))) (suc zero) zero
                       (suc (suc zero)) (q ∷ p ∷ x ∷ B ∷ codes ν))
          _⇒ᴮ_ pins-imp b }
    where
      g : Formula S (suc (suc (suc (suc k))))
      g = impAtˢ (suc (suc (suc zero))) (suc zero) zero (suc (suc zero))

  -- Falsity, Bell (1.9) read through `¬̇ φ = φ ⇒̇ ⊥̇`.

  interp ⊥̇ = record
    { val     = λ ν → ⊥ᴮ
    ; code    = botAtˢ (suc zero) zero
    ; reading = λ ν b →
        botAtˢ-reading (suc zero) zero (b ∷ B ∷ codes ν)
        ∙ pins-reading (botΔ B) ⊥ᴮ pins-bot b }

  -- The two unbounded quantifiers, Bell (1.10) and (1.14). The family is the
  -- body's value as the bound variable ranges over the names; the join and the
  -- meet are taken over one and the same value set, with one Separation
  -- instance between them.

  interp (∃̇ φ) = record
    { val     = λ ν → supᴮ (Admits.values (admP (interp φ) ν))
                           (Admits.values-sub (admP (interp φ) ν))
    ; code    = supCodeˢ (Ψplain (Interp.code (interp φ)))
    ; reading = λ ν b →
        sup-code-reading (Ψplain (Interp.code (interp φ))) (codes ν)
          (ΨrP (interp φ) ν) (admP (interp φ) ν) b }

  interp (∀̇ φ) = record
    { val     = λ ν → infᴮ (Admits.values (admP (interp φ) ν))
                           (Admits.values-sub (admP (interp φ) ν))
    ; code    = infCodeˢ (Ψplain (Interp.code (interp φ)))
    ; reading = λ ν b →
        inf-code-reading (Ψplain (Interp.code (interp φ))) (codes ν)
          (ΨrP (interp φ) ν) (admP (interp φ) ν) b }

  -- The two bounded quantifiers. THE VALUE IS THE JOIN OVER ALL NAMES of the
  -- guarded body, not the join over the domain of the bound. Bell's (1.15)
  -- shape at fulltext:2010 restricts to dom(u), and Corollary 1.18
  -- (fulltext:2183-2196) is the theorem that the two agree. That theorem is an
  -- atomic-layer statement about the weight and the support, and it is Track
  -- D's `bounded-∃` and `bounded-∀`. It is neither assumed nor used here, and
  -- the unrestricted form is the only one available to a compiler whose
  -- hypotheses do not include closure of a support under the recogniser.

  interp (∃̇∈ (var i) φ) = record
    { val     = λ ν → supᴮ (Admits.values (admM (interp φ) i ν))
                           (Admits.values-sub (admM (interp φ) i ν))
    ; code    = supCodeˢ (Ψbound i (Interp.code (interp φ)) gMeet)
    ; reading = λ ν b →
        sup-code-reading (Ψbound i (Interp.code (interp φ)) gMeet) (codes ν)
          (ΨrM (interp φ) i ν) (admM (interp φ) i ν) b }
  interp (∃̇∈ (con ()) φ)

  interp (∀̇∈ (var i) φ) = record
    { val     = λ ν → infᴮ (Admits.values (admI (interp φ) i ν))
                           (Admits.values-sub (admI (interp φ) i ν))
    ; code    = infCodeˢ (Ψbound i (Interp.code (interp φ)) gImp)
    ; reading = λ ν b →
        inf-code-reading (Ψbound i (Interp.code (interp φ)) gImp) (codes ν)
          (ΨrI (interp φ) i ν) (admI (interp φ) i ν) b }
  interp (∀̇∈ (con ()) φ)

  -- ---------------------------------------------------------------------
  -- The compiled value and the compiled code, named
  -- ---------------------------------------------------------------------

  -- Naming the two projections keeps every law below free of a field
  -- projection out of a constructed record, which is the declaration shape
  -- project rule 3 warns about. It also makes the laws readable as
  -- mathematics rather than as record surgery.

  value : ∀ {k} → Src k → Env k → Pt B
  value φ = Interp.val (interp φ)

  codeOf : ∀ {k} → Src k → Formula S (suc (suc k))
  codeOf φ = Interp.code (interp φ)

  describes : ∀ {k} (φ : Src k) (ν : Env k) (b : S)
            → ((b ∷ B ∷ codes ν) ⊨ codeOf φ) ≡ (b ≈ˢ fst (value φ ν))
  describes φ = Interp.reading (interp φ)

  -- ---------------------------------------------------------------------
  -- The per-constructor laws
  -- ---------------------------------------------------------------------

  -- Bell (1.8) to (1.13) are equations, because the finite operations are
  -- operations; the four quantifier clauses are CHARACTERIZATIONS and never
  -- equations, because naming the join a quantifier node forms would put a
  -- construction of one layer inside the statement of another. The universal
  -- properties say everything an equation would and elaborate in bounded time.

  val-∈ : ∀ {k} (i j : Fin k) (ν : Env k)
        → value (var i ∈̇ var j) ν ≡ memᴬ (fst (lookup i ν)) (fst (lookup j ν))
  val-∈ i j ν =
      cong (λ w → memᴬ w (lookup j (codes ν))) (codes-lookup i ν)
    ∙ cong (λ w → memᴬ (fst (lookup i ν)) w) (codes-lookup j ν)

  val-≐ : ∀ {k} (i j : Fin k) (ν : Env k)
        → value (var i ≐ var j) ν ≡ eqᴬ (fst (lookup i ν)) (fst (lookup j ν))
  val-≐ i j ν =
      cong (λ w → eqᴬ w (lookup j (codes ν))) (codes-lookup i ν)
    ∙ cong (λ w → eqᴬ (fst (lookup i ν)) w) (codes-lookup j ν)

  val-∧ : ∀ {k} (φ ψ : Src k) (ν : Env k)
        → value (φ ∧̇ ψ) ν ≡ (value φ ν ⊓ᴮ value ψ ν)
  val-∧ φ ψ ν = refl

  val-∨ : ∀ {k} (φ ψ : Src k) (ν : Env k)
        → value (φ ∨̇ ψ) ν ≡ (value φ ν ⊔ᴮ value ψ ν)
  val-∨ φ ψ ν = refl

  val-⇒ : ∀ {k} (φ ψ : Src k) (ν : Env k)
        → value (φ ⇒̇ ψ) ν ≡ (value φ ν ⇒ᴮ value ψ ν)
  val-⇒ φ ψ ν = refl

  val-⊥ : ∀ {k} (ν : Env k) → value {k} ⊥̇ ν ≡ ⊥ᴮ
  val-⊥ ν = refl

  -- Bell (1.10) and (1.14), as the join and the meet of the body's values over
  -- the names. Neither is stated as an equation naming a constructed join.

  ∃-ub : ∀ {k} (φ : Src (suc k)) (ν : Env k) (σ : Name)
       → ⟨ value φ (σ ∷ ν) ≤ᴮ value (∃̇ φ) ν ⟩
  ∃-ub φ ν σ = admits-ub (admP (interp φ) ν) σ

  ∃-lub : ∀ {k} (φ : Src (suc k)) (ν : Env k) (c : Pt B)
        → ((σ : Name) → ⟨ value φ (σ ∷ ν) ≤ᴮ c ⟩)
        → ⟨ value (∃̇ φ) ν ≤ᴮ c ⟩
  ∃-lub φ ν c h = admits-lub (admP (interp φ) ν) c h

  ∀-lb : ∀ {k} (φ : Src (suc k)) (ν : Env k) (σ : Name)
       → ⟨ value (∀̇ φ) ν ≤ᴮ value φ (σ ∷ ν) ⟩
  ∀-lb φ ν σ = admits-lb (admP (interp φ) ν) σ

  ∀-glb : ∀ {k} (φ : Src (suc k)) (ν : Env k) (c : Pt B)
        → ((σ : Name) → ⟨ c ≤ᴮ value φ (σ ∷ ν) ⟩)
        → ⟨ c ≤ᴮ value (∀̇ φ) ν ⟩
  ∀-glb φ ν c h = admits-glb (admP (interp φ) ν) c h

  -- Corollary 1.18's shape, at the unrestricted family. Read the bound's atomic
  -- membership value where Bell reads the weight: the two agree by 1.18, which
  -- is Track D's theorem and is not used here.

  ∃∈-ub : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Env k) (σ : Name)
        → ⟨ (memᴬ (fst σ) (fst (lookup i ν)) ⊓ᴮ value φ (σ ∷ ν))
            ≤ᴮ value (∃̇∈ (var i) φ) ν ⟩
  ∃∈-ub i φ ν σ =
    subst (λ w → ⟨ (memᴬ (fst σ) w ⊓ᴮ value φ (σ ∷ ν))
                   ≤ᴮ value (∃̇∈ (var i) φ) ν ⟩)
          (codes-lookup i ν) (admits-ub (admM (interp φ) i ν) σ)

  ∃∈-lub : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Env k) (c : Pt B)
         → ((σ : Name) → ⟨ (memᴬ (fst σ) (fst (lookup i ν)) ⊓ᴮ value φ (σ ∷ ν))
                           ≤ᴮ c ⟩)
         → ⟨ value (∃̇∈ (var i) φ) ν ≤ᴮ c ⟩
  ∃∈-lub i φ ν c h = admits-lub (admM (interp φ) i ν) c
    (λ σ → subst (λ w → ⟨ (memᴬ (fst σ) w ⊓ᴮ value φ (σ ∷ ν)) ≤ᴮ c ⟩)
             (sym (codes-lookup i ν)) (h σ))

  ∀∈-lb : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Env k) (σ : Name)
        → ⟨ value (∀̇∈ (var i) φ) ν
            ≤ᴮ (memᴬ (fst σ) (fst (lookup i ν)) ⇒ᴮ value φ (σ ∷ ν)) ⟩
  ∀∈-lb i φ ν σ =
    subst (λ w → ⟨ value (∀̇∈ (var i) φ) ν
                   ≤ᴮ (memᴬ (fst σ) w ⇒ᴮ value φ (σ ∷ ν)) ⟩)
          (codes-lookup i ν) (admits-lb (admI (interp φ) i ν) σ)

  ∀∈-glb : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Env k) (c : Pt B)
         → ((σ : Name) → ⟨ c ≤ᴮ (memᴬ (fst σ) (fst (lookup i ν))
                                  ⇒ᴮ value φ (σ ∷ ν)) ⟩)
         → ⟨ c ≤ᴮ value (∀̇∈ (var i) φ) ν ⟩
  ∀∈-glb i φ ν c h = admits-glb (admI (interp φ) i ν) c
    (λ σ → subst (λ w → ⟨ c ≤ᴮ (memᴬ (fst σ) w ⇒ᴮ value φ (σ ∷ ν)) ⟩)
             (sym (codes-lookup i ν)) (h σ))

  -- The record, so that K4.6 and K4.7 can take the laws without taking the
  -- compiler. Its level is Type ℓ, not Type (ℓ-suc ℓ) as architecture section
  -- 1.7 prints: every field is a path in Pt B or an element of a truth value's
  -- carrier, and no field is a path in Ω. The correction matters for the same
  -- reason Track C's did, since a record at Type ℓ may index a ⋁ and one at
  -- Type (ℓ-suc ℓ) may not. `Interp` itself really is at Type (ℓ-suc ℓ),
  -- because `reading` is a path in Ω.

  record InterpLaws : Type ℓ where
    field
      law-∈ : ∀ {k} (i j : Fin k) (ν : Env k)
            → value (var i ∈̇ var j) ν
            ≡ memᴬ (fst (lookup i ν)) (fst (lookup j ν))
      law-≐ : ∀ {k} (i j : Fin k) (ν : Env k)
            → value (var i ≐ var j) ν
            ≡ eqᴬ (fst (lookup i ν)) (fst (lookup j ν))
      law-∧ : ∀ {k} (φ ψ : Src k) (ν : Env k)
            → value (φ ∧̇ ψ) ν ≡ (value φ ν ⊓ᴮ value ψ ν)
      law-∨ : ∀ {k} (φ ψ : Src k) (ν : Env k)
            → value (φ ∨̇ ψ) ν ≡ (value φ ν ⊔ᴮ value ψ ν)
      law-⇒ : ∀ {k} (φ ψ : Src k) (ν : Env k)
            → value (φ ⇒̇ ψ) ν ≡ (value φ ν ⇒ᴮ value ψ ν)
      law-⊥ : ∀ {k} (ν : Env k) → value {k} ⊥̇ ν ≡ ⊥ᴮ
      law-∃-ub   : ∀ {k} (φ : Src (suc k)) (ν : Env k) (σ : Name)
                 → ⟨ value φ (σ ∷ ν) ≤ᴮ value (∃̇ φ) ν ⟩
      law-∃-lub  : ∀ {k} (φ : Src (suc k)) (ν : Env k) (c : Pt B)
                 → ((σ : Name) → ⟨ value φ (σ ∷ ν) ≤ᴮ c ⟩)
                 → ⟨ value (∃̇ φ) ν ≤ᴮ c ⟩
      law-∀-lb   : ∀ {k} (φ : Src (suc k)) (ν : Env k) (σ : Name)
                 → ⟨ value (∀̇ φ) ν ≤ᴮ value φ (σ ∷ ν) ⟩
      law-∀-glb  : ∀ {k} (φ : Src (suc k)) (ν : Env k) (c : Pt B)
                 → ((σ : Name) → ⟨ c ≤ᴮ value φ (σ ∷ ν) ⟩)
                 → ⟨ c ≤ᴮ value (∀̇ φ) ν ⟩
      law-∃∈-ub  : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Env k) (σ : Name)
                 → ⟨ (memᴬ (fst σ) (fst (lookup i ν)) ⊓ᴮ value φ (σ ∷ ν))
                     ≤ᴮ value (∃̇∈ (var i) φ) ν ⟩
      law-∃∈-lub : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Env k) (c : Pt B)
                 → ((σ : Name)
                    → ⟨ (memᴬ (fst σ) (fst (lookup i ν)) ⊓ᴮ value φ (σ ∷ ν))
                        ≤ᴮ c ⟩)
                 → ⟨ value (∃̇∈ (var i) φ) ν ≤ᴮ c ⟩
      law-∀∈-lb  : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Env k) (σ : Name)
                 → ⟨ value (∀̇∈ (var i) φ) ν
                     ≤ᴮ (memᴬ (fst σ) (fst (lookup i ν)) ⇒ᴮ value φ (σ ∷ ν)) ⟩
      law-∀∈-glb : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Env k) (c : Pt B)
                 → ((σ : Name) → ⟨ c ≤ᴮ (memᴬ (fst σ) (fst (lookup i ν))
                                          ⇒ᴮ value φ (σ ∷ ν)) ⟩)
                 → ⟨ c ≤ᴮ value (∀̇∈ (var i) φ) ν ⟩

  interpLaws : InterpLaws
  interpLaws = record
    { law-∈ = val-∈ ; law-≐ = val-≐
    ; law-∧ = val-∧ ; law-∨ = val-∨ ; law-⇒ = val-⇒ ; law-⊥ = val-⊥
    ; law-∃-ub = ∃-ub ; law-∃-lub = ∃-lub
    ; law-∀-lb = ∀-lb ; law-∀-glb = ∀-glb
    ; law-∃∈-ub = ∃∈-ub ; law-∃∈-lub = ∃∈-lub
    ; law-∀∈-lb = ∀∈-lb ; law-∀∈-glb = ∀∈-glb }

  -- ---------------------------------------------------------------------
  -- Bound behaviour
  -- ---------------------------------------------------------------------

  -- The existential node joins over ALL names, and a name is not a set of the
  -- ground. A reader who wants the join over a coded bound A gets it here, and
  -- gets with it the exact statement of what a bound costs: the inequality is
  -- unconditional, the equality is FALSE without adequacy, and the adequacy
  -- hypothesis is on the face of the statement and not in a comment.
  --
  -- No bound is constructed here and none is claimed to exist. `supᴮ` takes a
  -- ground code (CodedCompletion.agda:820), so an unbounded value already has
  -- exactly one definition and there is no second bound to compare it against:
  -- bound independence below is between two ADEQUATE bounds, not between a
  -- bounded and an unbounded reading.

  nameIn : (A : S) → ((x : S) → ⟨ x ∈ˢ A ⟩ → ⟨ IsName x ⟩) → Pt A → Name
  nameIn A hA p = fst p , hA (fst p) (snd p)

  -- The matrix of a bounded reading. The recogniser is replaced by membership
  -- in the bound, and the bound enters as a `con` constant, which is the one
  -- place in this file where a ground set is frozen into a formula outside
  -- `sepAt`. Note that `Fib (_∈ˢ A)` is `Pt A` definitionally, so the crossing
  -- is the architecture's own `collapse` after all, at the one node where the
  -- class really is a membership.

  Ψover : ∀ {k} → S → Formula S (suc (suc (suc k))) → Formula S (suc (suc k))
  Ψover A c = ∃̇ ((var zero ∈̇ con A) ∧̇ renameFo ρΨ c)

  Ψover-reading :
    ∀ {k} (A : S) (hA : (x : S) → ⟨ x ∈ˢ A ⟩ → ⟨ IsName x ⟩)
      (c : Formula S (suc (suc (suc k)))) (cs : S ^ k) (f : Name → Pt B)
    → ((σ : Name) (x : S) → ((x ∷ B ∷ fst σ ∷ cs) ⊨ c) ≡ (x ≈ˢ fst (f σ)))
    → (x : S) → ((x ∷ B ∷ cs) ⊨ Ψover A c)
              ≡ ⋁ (Pt A) (λ p → x ≈ˢ fst (f (nameIn A hA p)))
  Ψover-reading A hA c cs f rc x =
    collapse-reading (λ t → t ∈ˢ A) R
      (λ t h → x ≈ˢ fst (f (nameIn A hA (t , h))))
      (λ t h → ⊨-rename ρΨ c (t ∷ x ∷ B ∷ cs) (x ∷ B ∷ t ∷ cs) (agΨ t x cs)
             ∙ rc (nameIn A hA (t , h)) x)
    where
      R : S → Ω
      R t = (t ∷ x ∷ B ∷ cs) ⊨ renameFo ρΨ c

  admOver : ∀ {k} {φ : Src (suc k)} (iφ : Interp φ) (A : S)
            (hA : (x : S) → ⟨ x ∈ˢ A ⟩ → ⟨ IsName x ⟩) (ν : Env k)
          → Admits (λ p → Interp.val iφ (nameIn A hA p ∷ ν))
  admOver iφ A hA ν =
    sepAdmits sep (sepAt (Ψover A (Interp.code iφ)) (B ∷ codes ν))
      (λ x → sepAt-reading (Ψover A (Interp.code iφ)) (B ∷ codes ν) x
           ∙ Ψover-reading A hA (Interp.code iφ) (codes ν) (famP iφ ν)
               (λ σ y → Interp.reading iφ (σ ∷ ν) y) x)

  supOver : ∀ {k} (φ : Src (suc k)) (A : S)
            (hA : (x : S) → ⟨ x ∈ˢ A ⟩ → ⟨ IsName x ⟩) (ν : Env k) → Pt B
  supOver φ A hA ν =
    supᴮ (Admits.values (admOver (interp φ) A hA ν))
         (Admits.values-sub (admOver (interp φ) A hA ν))

  -- Unconditional. Every value attained over the bound is attained, so the
  -- bounded join is below the unbounded one.

  ∃-over-coded :
    ∀ {k} (φ : Src (suc k)) (A : S)
      (hA : (x : S) → ⟨ x ∈ˢ A ⟩ → ⟨ IsName x ⟩) (ν : Env k)
    → ⟨ supOver φ A hA ν ≤ᴮ value (∃̇ φ) ν ⟩
  ∃-over-coded φ A hA ν =
    admits-lub (admOver (interp φ) A hA ν) (value (∃̇ φ) ν)
      (λ p → ∃-ub φ ν (nameIn A hA p))

  -- Adequacy: the bound attains every value the whole name class attains. This
  -- is a statement about the two ATTAINED CLASSES and compares no index with
  -- any other, which is why it carries no choice of witnesses. Its level is
  -- Type (ℓ-suc ℓ), not Type ℓ as architecture section 1.7 prints, because it
  -- is a family of paths in Ω; it is a hypothesis and never enters a join.

  Adequate : ∀ {k} (φ : Src (suc k)) (ν : Env k) (A : S)
             (hA : (x : S) → ⟨ x ∈ˢ A ⟩ → ⟨ IsName x ⟩) → Type (ℓ-suc ℓ)
  Adequate φ ν A hA =
    (b : S) → ⋁ (Pt A) (λ p → b ≈ˢ fst (value φ (nameIn A hA p ∷ ν)))
            ≡ ⋁ Name (λ σ → b ≈ˢ fst (value φ (σ ∷ ν)))

  ∃-coded-exact :
    ∀ {k} (φ : Src (suc k)) (A : S)
      (hA : (x : S) → ⟨ x ∈ˢ A ⟩ → ⟨ IsName x ⟩) (ν : Env k)
    → Adequate φ ν A hA
    → supOver φ A hA ν ≡ value (∃̇ φ) ν
  ∃-coded-exact φ A hA ν ad =
    join-presented (admOver (interp φ) A hA ν) (admP (interp φ) ν) ad

  bound-independent :
    ∀ {k} (φ : Src (suc k)) (ν : Env k) (A A' : S)
      (hA  : (x : S) → ⟨ x ∈ˢ A ⟩  → ⟨ IsName x ⟩)
      (hA' : (x : S) → ⟨ x ∈ˢ A' ⟩ → ⟨ IsName x ⟩)
    → Adequate φ ν A hA → Adequate φ ν A' hA'
    → supOver φ A hA ν ≡ supOver φ A' hA' ν
  bound-independent φ ν A A' hA hA' ad ad' =
    ∃-coded-exact φ A hA ν ad ∙ sym (∃-coded-exact φ A' hA' ν ad')

  -- ---------------------------------------------------------------------
  -- Formulas with ground parameters, and environments of check names
  -- ---------------------------------------------------------------------

  -- A formula with ground parameters reaches this compiler through parameter
  -- abstraction, never by widening `Src` to `Formula S k`. The widening would
  -- be fatal rather than merely inconvenient: the bounded quantifier node
  -- needs its bound to be a slot so that the environment can hand it a NAME,
  -- and a `con` bound is a ground set with no recognition proof attached.
  -- `absFo` turns each constant occurrence into one fresh variable
  -- (ParameterAbstraction.lagda.md:103), and the environment then supplies a
  -- name for each.

  fromParametrized : ∀ {k} (φ : Formula S k) → Src (k + countFo φ)
  fromParametrized φ = absFo φ

  -- The environment of check names over a ground tuple. `check` and its
  -- validity are arguments and not module parameters, because the compiler
  -- itself never forms a check name: this is plumbing for K4.7, which owns
  -- Bell 1.23 and the value of a checked atomic formula. Nothing here claims
  -- that `check` is injective, that it commutes with anything, or that the
  -- value of a checked formula is ⊤ᴮ or ⊥ᴮ.

  checkEnv : (chk : S → S) → ((a : S) → ⟨ IsName (chk a) ⟩)
           → ∀ {n} → S ^ n → Env n
  checkEnv chk hchk []      = []
  checkEnv chk hchk (a ∷ γ) = (chk a , hchk a) ∷ checkEnv chk hchk γ

  checkEnv-codes : (chk : S → S) (hchk : (a : S) → ⟨ IsName (chk a) ⟩)
                 → ∀ {n} (γ : S ^ n)
                 → codes (checkEnv chk hchk γ) ≡ map chk γ
  checkEnv-codes chk hchk []      = refl
  checkEnv-codes chk hchk (a ∷ γ) =
    cong (chk a ∷_) (checkEnv-codes chk hchk γ)

  -- ---------------------------------------------------------------------
  -- The non-claims, collected
  -- ---------------------------------------------------------------------

  -- Each of these is stated beside the signature it constrains above. They are
  -- gathered here so that a later track can read the boundary in one place,
  -- and each is paired with the search that checks it.
  --
  --  1. NO INTERNAL TRUTH-VALUE FUNCTION ON FORMULAS. `interp` is a host
  --     function on `Src k`; no code of a formula enters a term; the
  --     collection of pairs of a formula and its value is not claimed to be a
  --     definable class. Bell page 24 forbids exactly that claim, and the
  --     absence is checked by `grep -c "FOL.Coding\|⌜\|Codes\|tagOf\|payOf"`
  --     over this file, which returns the occurrences in this comment only.
  --
  --  2. NO Δ₀ WITNESS for any compiled code. Every quantifier node's code has
  --     an unbounded quantifier over the value set, and the matrix carries the
  --     name recogniser, whose own leading quantifier is unbounded with no
  --     bound available from the ordinary profile (NameSpace.agda:167-175).
  --     There is no `Δ₀` in this file outside this comment.
  --
  --  3. NO AGREEMENT WITH A HOST EVALUATOR. None is stated, because the
  --     infinitary half of the bridge does not exist upstream:
  --     `grep -c "reads-sup\|reads-inf\|reads-⋁\|reads-⋀"` over
  --     CodedCompletion.agda returns 0, re-run for this file. Agreement is in
  --     any case conditional on both sides admitting the relevant families,
  --     which is the roadmap's own wording, and this file admits families only
  --     through Separation.
  --
  --  4. NO ATOMIC LAW AND NO ATOMIC VALUE IS PROVED HERE. Track E's graph is a
  --     hypothesis, and obstruction O1 is untouched: at the regular-open
  --     algebra that hypothesis has no discharge today. The compiler's
  --     correctness is unconditional only RELATIVE to it, and that is the
  --     honest reading of every theorem in this file.
  --
  --  5. NO BOUND ON THE NAMES. The existential node joins over the whole name
  --     class, `supᴮ` takes a ground code, and the value set that reaches it
  --     is a Separation instance inside the carrier, never a set of names. The
  --     bounded reading above is offered as a comparison, with its adequacy
  --     hypothesis on its face, and no bound is claimed to be adequate.
  --
  --  6. NO CLAIM THAT THE BOUNDED CLAUSES AGREE WITH BELL'S DOMAIN-RESTRICTED
  --     ONES. That is Corollary 1.18 and it is Track D's.
  --
  --  7. NO MAXIMUM PRINCIPLE, NO FULLNESS, NO GENERICITY, NO CHOICE, NO LEM.
  --     The whole ledger is the telescope of `Core`, and the only axiom in it
  --     is Separation.

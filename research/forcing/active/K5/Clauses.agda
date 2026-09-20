{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track B: the ten forcing clauses, the clause record, and UNIQUENESS.
--
-- What this module is for. Architecture decision D3 defines the Boolean
-- forcing relation as p ⊩ᴮ b = i p ≤ᴮ b and the formula relation as
-- p ⊩ φ [ ν ] = p ⊩ᴮ val φ ν. Under that definition the roadmap's displayed
-- public equivalence is refl and closes nothing (T-B1). The deliverable with
-- content is ⊩-unique: any relation R satisfying the ten clauses and agreeing
-- with ⊩ at the two atomic nodes IS ⊩, pointwise, at every formula.
--
-- HOW TRACK A ENTERS. Track A owns the record ForcingBase and the sealed
-- _⊩ᴮ_ with its six direct poset lemmas. This file does NOT import K5.Frame:
-- it takes Track A's stated export surface FLAT, as parameters of module
-- Core, typed from architecture sections 1.2 and 1.3. That is ledger clause
-- L10 and it is also preamble rule 2 in its tightest form, since a module
-- parameter is a variable and a variable cannot unfold. The coordinator
-- instantiates Core by `open ForcingBase fb` and passing the projections.
--
-- RENAMINGS FORCED BY LEDGER CLAUSE L9, which forbids the local names
-- `i`, `below`, `value`, `dense`, `carrier`, `order`, `check`, `reflect`:
--
--     architecture   here        architecture   here
--     i              iᶠ          carrier        carrierᶠ
--     value          val         p ≼ᶜ q         p ≼ᶜ q  (a parameter, not
--                                                        refinesΔ order)
--
-- The order is taken as an abstract Ω-valued relation _≼ᶜ_ rather than as
-- `refinesΔ order`. Consequence: this file imports no coded vocabulary at
-- all, every exported signature is readable in Cond, ≼ᶜ, DenseBelow and ⊩
-- (ledger clause L6), and rule 2b cannot reach any statement here.
--
-- HEAVY MODULE APPLICATIONS: ONE, K4.Implication. The architecture budgets
-- Track B two, the second being K4.Infinitary for supᴮ and infᴮ. It is not
-- needed: preamble rule 7 says state every value fact as a universal
-- property, and once the four quantifier clauses are stated at an abstract
-- family with its lb/glb or ub/lub hypotheses, no completeness structure
-- appears in any type. So CodedComplete is not a parameter of this file.
--
-- CLASSICAL LEDGER. `LEM ℓ` is an explicit first argument of exactly the
-- five Boolean clauses the architecture charges: ⊩-∨→, ⊩-∃→, ⊩-∃∈→, ⊩-⇒←
-- and ⊩-dichotomy. Three further declarations carry it and each is named
-- here so no count is a surprise: ⊩-dichotomy-dense, which is ⊩-dichotomy
-- read at every q below p and spends no new principle; and the two package
-- theorems ⊩-clauses and ⊩-unique, which architecture section 5.1 charges
-- LEM ℓ in its own ledger row. Nothing else in the file names LEM.
--
-- Every use of excluded middle in this file is at ONE proposition shape,
-- `x ≡ ⊥ᴮ` for x : Pt B, decided through decide⊥ below. There is no host
-- choice of any kind, no elimination of a truncated sigma into data, and no
-- appeal to an antichain, a maximal antichain, a predense set or
-- separativity.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import K4.Algebra
import K4.Implication

module K5.Clauses
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (B : ZFStructure.S 𝒮)
  (L : K4.Algebra.Lattice 𝒮 B)
  (Cm : K4.Algebra.Complement 𝒮 B L)
  -- the poset side, abstract: the carrier code and the refinement relation
  (carrierᶠ : ZFStructure.S 𝒮)
  (_≼ᶜ_ : ZFStructure.S 𝒮 → ZFStructure.S 𝒮 → hProp ℓ)
  -- the name recogniser, from which the compiler's name type is built
  (IsNameᴮ : ZFStructure.S 𝒮 → hProp ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

-- The scope contract of K4/Implication.agda:64-77. K4.Algebra supplies the
-- point vocabulary and the order; K4.Implication supplies the theory and
-- re-exports the Lattice and Complement fields. Neither re-exports the
-- other's names, so opening both is unambiguous.

open K4.Algebra 𝒮
  using ( Pt; isSetPt; Pt≡; _≤ᴮ_; ≤ᴮ-refl; ⊆ˢ-trans
        ; Lattice; Complement; CodedComplete )

open K4.Implication 𝒮 ext paths B L Cm

--------------------------------------------------------------------------------
-- Conditions, formulas, names, density below
--------------------------------------------------------------------------------

-- A condition is a code together with a proof that it is a member of the
-- carrier, the same shape K2 gives it at CodedCompletion.agda:223-224 and K4
-- gives a point at K4/Algebra.agda:58-59.

Cond : Type ℓ
Cond = Σ[ x ∈ S ] ⟨ x ∈ˢ carrierᶠ ⟩

-- The compiler reads parameter free formulas, Compile.agda:499-500, and a
-- name is a code carrying its recognition proof, Compile.agda:502-503 read
-- through Fib P = Σ[ x ∈ S ] ⟨ P x ⟩ (K4/ValueSets.agda:166-167). Writing
-- the sigma out rather than importing K4.ValueSets for one abbreviation
-- keeps this file at one heavy module application; the two types are the
-- same type, not two copies, because Fib is a definition and not a record.

Src : ℕ → Type ℓ
Src k = Formula (⊥* {ℓ}) k

Nameᴮ : Type ℓ
Nameᴮ = Σ[ x ∈ S ] ⟨ IsNameᴮ x ⟩

Envᴮ : ℕ → Type ℓ
Envᴮ k = Vec Nameᴮ k

-- Density below a condition, architecture section 1.3. Note the index of
-- both quantifiers: Cond, the sigma carrying the membership proof, and never
-- S with the membership as a conjunct. That is preamble rule 4.

DenseBelow : Cond → (Cond → Ω) → Ω
DenseBelow p W =
  ⋀ Cond (λ q → ((fst q) ≼ᶜ (fst p))
                ⇒ ⋁ Cond (λ r → ((fst r) ≼ᶜ (fst q)) ⊓ (W r)))

DenseBelow-map : (p : Cond) (W W' : Cond → Ω)
               → ((r : Cond) → ⟨ W r ⟩ → ⟨ W' r ⟩)
               → ⟨ DenseBelow p W ⟩ → ⟨ DenseBelow p W' ⟩
DenseBelow-map p W W' f h q hq =
  PT.map (λ { (r , hrq , hw) → r , (hrq , f r hw) }) (h q hq)

--------------------------------------------------------------------------------
-- The one shape of excluded middle this file spends
--------------------------------------------------------------------------------

-- Pt B is a set, so `x ≡ ⊥ᴮ` is a proposition at level ℓ and LEM ℓ decides
-- it. Every paid direction below is one or two instances of this and nothing
-- else. The pattern, including the polarity, is K2's at
-- CodedCompletion.agda:1316-1325.

decide⊥ : LEM ℓ → (x : Pt B) → (x ≡ ⊥ᴮ) ⊎ ((x ≡ ⊥ᴮ) → Empty.⊥)
decide⊥ lem x = lem ((x ≡ ⊥ᴮ) , isSetPt B x ⊥ᴮ)

-- The Boolean identity the implication clause reads. ¬ᴮ (u ⇒ᴮ v) is
-- u ⊓ᴮ ¬ᴮ v, by De Morgan at the complemented left argument and involution.

¬-⇒ᴮ : (u v : Pt B) → (¬ᴮ (u ⇒ᴮ v)) ≡ (u ⊓ᴮ (¬ᴮ v))
¬-⇒ᴮ u v = De-Morgan-⊔ (¬ᴮ u) v ∙ cong (_⊓ᴮ (¬ᴮ v)) (¬ᴮ-invol u)

--------------------------------------------------------------------------------
-- Track A's export surface and the compiler's fourteen laws, taken flat
--------------------------------------------------------------------------------

-- Everything below the line is stated over this telescope. The first block
-- is architecture section 1.2 and 1.3, Track A's record read as a flat list;
-- the second is the two atomic values and `val`; the third is
-- Compile.agda:1318-1357, the record InterpLaws field for field, with the
-- bound variable `i` renamed (ledger clause L9) and nothing else changed.

module Core
  (iᶠ        : Cond → Pt B)
  (_⊩ᴮ_      : Cond → Pt B → Ω)
  (⊩ᴮ-spec   : (p : Cond) (b : Pt B) → (p ⊩ᴮ b) ≡ (iᶠ p ≤ᴮ b))
  (≼-refl    : (p : S) → ⟨ p ∈ˢ carrierᶠ ⟩ → ⟨ p ≼ᶜ p ⟩)
  (≼-trans   : (r q p : S) → ⟨ r ∈ˢ carrierᶠ ⟩ → ⟨ q ∈ˢ carrierᶠ ⟩
             → ⟨ p ∈ˢ carrierᶠ ⟩
             → ⟨ r ≼ᶜ q ⟩ → ⟨ q ≼ᶜ p ⟩ → ⟨ r ≼ᶜ p ⟩)
  (⊩ᴮ-mono   : (p q : Cond) (b : Pt B)
             → ⟨ (fst q) ≼ᶜ (fst p) ⟩ → ⟨ p ⊩ᴮ b ⟩ → ⟨ q ⊩ᴮ b ⟩)
  (⊩ᴮ-down   : (p : Cond) (b : Pt B)
             → ⟨ p ⊩ᴮ b ⟩ → ⟨ DenseBelow p (λ r → r ⊩ᴮ b) ⟩)
  (⊩ᴮ-reg    : (p : Cond) (b : Pt B)
             → ⟨ DenseBelow p (λ r → r ⊩ᴮ b) ⟩ → ⟨ p ⊩ᴮ b ⟩)
  (⊩ᴮ-⊥      : (p : Cond) → ⟨ p ⊩ᴮ ⊥ᴮ ⟩ → ⟨ ⊥ ⟩)
  (⊩ᴮ-extend : (q : Cond) (b : Pt B) → (((iᶠ q ⊓ᴮ b) ≡ ⊥ᴮ) → ⟨ ⊥ ⟩)
             → ⟨ ⋁ Cond (λ r → ((fst r) ≼ᶜ (fst q)) ⊓ (r ⊩ᴮ b)) ⟩)
  (eqᴬ memᴬ  : S → S → Pt B)
  (val       : ∀ {k} → Src k → Envᴮ k → Pt B)
  (law-∈ : ∀ {k} (a b : Fin k) (ν : Envᴮ k)
         → val (var a ∈̇ var b) ν ≡ memᴬ (fst (lookup a ν)) (fst (lookup b ν)))
  (law-≐ : ∀ {k} (a b : Fin k) (ν : Envᴮ k)
         → val (var a ≐ var b) ν ≡ eqᴬ (fst (lookup a ν)) (fst (lookup b ν)))
  (law-∧ : ∀ {k} (φ ψ : Src k) (ν : Envᴮ k)
         → val (φ ∧̇ ψ) ν ≡ (val φ ν ⊓ᴮ val ψ ν))
  (law-∨ : ∀ {k} (φ ψ : Src k) (ν : Envᴮ k)
         → val (φ ∨̇ ψ) ν ≡ (val φ ν ⊔ᴮ val ψ ν))
  (law-⇒ : ∀ {k} (φ ψ : Src k) (ν : Envᴮ k)
         → val (φ ⇒̇ ψ) ν ≡ (val φ ν ⇒ᴮ val ψ ν))
  (law-⊥ : ∀ {k} (ν : Envᴮ k) → val {k} ⊥̇ ν ≡ ⊥ᴮ)
  (law-∃-ub   : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k) (σ : Nameᴮ)
              → ⟨ val φ (σ ∷ ν) ≤ᴮ val (∃̇ φ) ν ⟩)
  (law-∃-lub  : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k) (c : Pt B)
              → ((σ : Nameᴮ) → ⟨ val φ (σ ∷ ν) ≤ᴮ c ⟩)
              → ⟨ val (∃̇ φ) ν ≤ᴮ c ⟩)
  (law-∀-lb   : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k) (σ : Nameᴮ)
              → ⟨ val (∀̇ φ) ν ≤ᴮ val φ (σ ∷ ν) ⟩)
  (law-∀-glb  : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k) (c : Pt B)
              → ((σ : Nameᴮ) → ⟨ c ≤ᴮ val φ (σ ∷ ν) ⟩)
              → ⟨ c ≤ᴮ val (∀̇ φ) ν ⟩)
  (law-∃∈-ub  : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Envᴮ k) (σ : Nameᴮ)
              → ⟨ (memᴬ (fst σ) (fst (lookup j ν)) ⊓ᴮ val φ (σ ∷ ν))
                  ≤ᴮ val (∃̇∈ (var j) φ) ν ⟩)
  (law-∃∈-lub : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Envᴮ k) (c : Pt B)
              → ((σ : Nameᴮ)
                 → ⟨ (memᴬ (fst σ) (fst (lookup j ν)) ⊓ᴮ val φ (σ ∷ ν))
                     ≤ᴮ c ⟩)
              → ⟨ val (∃̇∈ (var j) φ) ν ≤ᴮ c ⟩)
  (law-∀∈-lb  : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Envᴮ k) (σ : Nameᴮ)
              → ⟨ val (∀̇∈ (var j) φ) ν
                  ≤ᴮ (memᴬ (fst σ) (fst (lookup j ν)) ⇒ᴮ val φ (σ ∷ ν)) ⟩)
  (law-∀∈-glb : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Envᴮ k) (c : Pt B)
              → ((σ : Nameᴮ) → ⟨ c ≤ᴮ (memᴬ (fst σ) (fst (lookup j ν))
                                       ⇒ᴮ val φ (σ ∷ ν)) ⟩)
              → ⟨ c ≤ᴮ val (∀̇∈ (var j) φ) ν ⟩)
  where

  ------------------------------------------------------------------------
  -- Reading the frame's specification in both directions
  ------------------------------------------------------------------------

  ⊩→≤ : (p : Cond) (b : Pt B) → ⟨ p ⊩ᴮ b ⟩ → ⟨ iᶠ p ≤ᴮ b ⟩
  ⊩→≤ p b = subst ⟨_⟩ (⊩ᴮ-spec p b)

  ≤→⊩ : (p : Cond) (b : Pt B) → ⟨ iᶠ p ≤ᴮ b ⟩ → ⟨ p ⊩ᴮ b ⟩
  ≤→⊩ p b = subst ⟨_⟩ (sym (⊩ᴮ-spec p b))

  -- Forcing is upward closed in the value. This is the one step every finite
  -- clause below takes, and naming it is what keeps a bare reflexivity out of
  -- any congruence over ⊓ or ⊔ (preamble rule 1, trap T-B4).

  ⊩ᴮ-up : (p : Cond) (b c : Pt B) → ⟨ b ≤ᴮ c ⟩ → ⟨ p ⊩ᴮ b ⟩ → ⟨ p ⊩ᴮ c ⟩
  ⊩ᴮ-up p b c h k = ≤→⊩ p c (⊆ˢ-trans (⊩→≤ p b k) h)

  -- A condition whose image is bottom does not exist. This is ⊩ᴮ-⊥ read
  -- through the order, and it is where trap T-A2 is spent: without the
  -- frame's i-nonzero, which is what ⊩ᴮ-⊥ packages, every classical clause
  -- below fails at its degenerate branch.

  ⊩ᴮ-zero : (p : Cond) → (iᶠ p ≡ ⊥ᴮ) → ⟨ ⊥ ⟩
  ⊩ᴮ-zero p e =
    ⊩ᴮ-⊥ p (≤→⊩ p ⊥ᴮ (subst (λ z → ⟨ z ≤ᴮ ⊥ᴮ ⟩) (sym e) (≤ᴮ-refl ⊥ᴮ)))

  ------------------------------------------------------------------------
  -- The conjunction clause, free in both directions
  ------------------------------------------------------------------------

  ⊩-∧ : (p : Cond) (u v : Pt B) → (p ⊩ᴮ (u ⊓ᴮ v)) ≡ ((p ⊩ᴮ u) ⊓ (p ⊩ᴮ v))
  ⊩-∧ p u v = ⇔toPath fwd bwd
    where
      fwd : ⟨ p ⊩ᴮ (u ⊓ᴮ v) ⟩ → ⟨ (p ⊩ᴮ u) ⊓ (p ⊩ᴮ v) ⟩
      fwd h = ⊩ᴮ-up p (u ⊓ᴮ v) u (⊓-lb₁ u v) h
            , ⊩ᴮ-up p (u ⊓ᴮ v) v (⊓-lb₂ u v) h
      bwd : ⟨ (p ⊩ᴮ u) ⊓ (p ⊩ᴮ v) ⟩ → ⟨ p ⊩ᴮ (u ⊓ᴮ v) ⟩
      bwd (hu , hv) =
        ≤→⊩ p (u ⊓ᴮ v) (⊓-glb u v (iᶠ p) (⊩→≤ p u hu) (⊩→≤ p v hv))

  ------------------------------------------------------------------------
  -- The universal clause, free in both directions, with NO condition
  -- quantifier
  ------------------------------------------------------------------------

  -- TRAP T-B2, named and avoided. The textbook clause for ∀ is a dense-below
  -- statement and costs a density argument and an excluded middle. It is not
  -- owed here, because K4 states the quantifier laws as CHARACTERIZATIONS and
  -- never as equations (Compile.agda:1216-1220). The greatest lower bound law
  -- instantiated at c := iᶠ p gives the whole backward direction on one line,
  -- with no quantifier over conditions anywhere in the proof or the statement.

  ⊩-∀→ : (p : Cond) (A : Pt B) (f : Nameᴮ → Pt B)
       → ((σ : Nameᴮ) → ⟨ A ≤ᴮ f σ ⟩)
       → ⟨ p ⊩ᴮ A ⟩ → (σ : Nameᴮ) → ⟨ p ⊩ᴮ f σ ⟩
  ⊩-∀→ p A f lb h σ = ⊩ᴮ-up p A (f σ) (lb σ) h

  ⊩-∀← : (p : Cond) (A : Pt B) (f : Nameᴮ → Pt B)
       → ((c : Pt B) → ((σ : Nameᴮ) → ⟨ c ≤ᴮ f σ ⟩) → ⟨ c ≤ᴮ A ⟩)
       → ((σ : Nameᴮ) → ⟨ p ⊩ᴮ f σ ⟩) → ⟨ p ⊩ᴮ A ⟩
  ⊩-∀← p A f glb h = ≤→⊩ p A (glb (iᶠ p) (λ σ → ⊩→≤ p (f σ) (h σ)))

  -- The bounded universal is the same pair at the guarded family
  -- g σ = memᴬ σ w ⇒ᴮ f σ, which is exactly what law-∀∈-lb and law-∀∈-glb
  -- hand over. No second proof and no second principle.

  ⊩-∀∈→ : (p : Cond) (A : Pt B) (g : Nameᴮ → Pt B)
        → ((σ : Nameᴮ) → ⟨ A ≤ᴮ g σ ⟩)
        → ⟨ p ⊩ᴮ A ⟩ → (σ : Nameᴮ) → ⟨ p ⊩ᴮ g σ ⟩
  ⊩-∀∈→ = ⊩-∀→

  ⊩-∀∈← : (p : Cond) (A : Pt B) (g : Nameᴮ → Pt B)
        → ((c : Pt B) → ((σ : Nameᴮ) → ⟨ c ≤ᴮ g σ ⟩) → ⟨ c ≤ᴮ A ⟩)
        → ((σ : Nameᴮ) → ⟨ p ⊩ᴮ g σ ⟩) → ⟨ p ⊩ᴮ A ⟩
  ⊩-∀∈← = ⊩-∀←

  ------------------------------------------------------------------------
  -- The implication clause
  ------------------------------------------------------------------------

  -- Forward is the adjunction and is free.

  ⊩-⇒→ : (p : Cond) (u v : Pt B) → ⟨ p ⊩ᴮ (u ⇒ᴮ v) ⟩
       → (q : Cond) → ⟨ (fst q) ≼ᶜ (fst p) ⟩ → ⟨ q ⊩ᴮ u ⟩ → ⟨ q ⊩ᴮ v ⟩
  ⊩-⇒→ p u v h q hqp hu =
    ≤→⊩ q v
      (⊆ˢ-trans (⊓-glb (iᶠ q) u (iᶠ q) (≤ᴮ-refl (iᶠ q)) (⊩→≤ q u hu))
                (⇒ᴮ-uncurry (iᶠ q) u v
                  (⊩→≤ q (u ⇒ᴮ v) (⊩ᴮ-mono p q (u ⇒ᴮ v) hqp h))))

  -- Backward is the first of the five paid directions. The shape is the one
  -- every paid direction below repeats: regularity reduces the goal to a
  -- density statement; at each q below p, either the meet of iᶠ q with the
  -- target is nonzero, and ⊩ᴮ-extend produces the refinement outright, or it
  -- is zero, and then q itself forces the antecedent, so the hypothesis makes
  -- q force the consequent as well, and q is below both a value and its
  -- complement, which ⊩ᴮ-zero forbids.

  ⊩-⇒← : LEM ℓ → (p : Cond) (u v : Pt B)
       → ((q : Cond) → ⟨ (fst q) ≼ᶜ (fst p) ⟩ → ⟨ q ⊩ᴮ u ⟩ → ⟨ q ⊩ᴮ v ⟩)
       → ⟨ p ⊩ᴮ (u ⇒ᴮ v) ⟩
  ⊩-⇒← lem p u v h = ⊩ᴮ-reg p (u ⇒ᴮ v) step
    where
      go : (q : Cond) → ⟨ (fst q) ≼ᶜ (fst p) ⟩
         → ((iᶠ q ⊓ᴮ (u ⇒ᴮ v)) ≡ ⊥ᴮ) ⊎ (((iᶠ q ⊓ᴮ (u ⇒ᴮ v)) ≡ ⊥ᴮ) → Empty.⊥)
         → ⟨ ⋁ Cond (λ r → ((fst r) ≼ᶜ (fst q)) ⊓ (r ⊩ᴮ (u ⇒ᴮ v))) ⟩
      go q hqp (inr nz) = ⊩ᴮ-extend q (u ⇒ᴮ v) (λ e → Empty.rec (nz e))
      go q hqp (inl e) = Empty.rec* (⊩ᴮ-zero q zero-q)
        where
          neg : ⟨ iᶠ q ≤ᴮ (u ⊓ᴮ (¬ᴮ v)) ⟩
          neg = subst (λ z → ⟨ iᶠ q ≤ᴮ z ⟩) (¬-⇒ᴮ u v)
                  (⊓⊥→≤¬ (iᶠ q) (u ⇒ᴮ v) e)
          qu : ⟨ q ⊩ᴮ u ⟩
          qu = ≤→⊩ q u (⊆ˢ-trans neg (⊓-lb₁ u (¬ᴮ v)))
          zero-q : iᶠ q ≡ ⊥ᴮ
          zero-q = ≤-both-⊥ (iᶠ q) v (⊩→≤ q v (h q hqp qu))
                     (⊆ˢ-trans neg (⊓-lb₂ u (¬ᴮ v)))
      step : ⟨ DenseBelow p (λ r → r ⊩ᴮ (u ⇒ᴮ v)) ⟩
      step q hqp = go q hqp (decide⊥ lem (iᶠ q ⊓ᴮ (u ⇒ᴮ v)))

  ------------------------------------------------------------------------
  -- The negation clause, free in BOTH directions
  ------------------------------------------------------------------------

  -- The backward direction looks as though it should need excluded middle,
  -- since it reads a universally quantified refutation as a refinement. It
  -- does not, and the reason is ⊥-as-≤ (K4/Implication.agda:182): "the meet
  -- of iᶠ q with ¬ᴮ u is zero" IS "iᶠ q refines u", in a Boolean algebra, by
  -- the distributive law alone. So the contrapositive that ⊩ᴮ-extend wants
  -- is exactly the hypothesis, with no double negation to eliminate.
  --
  -- TRAP T-B3 lives one level up, at the formula layer: ¬̇ φ is φ ⇒̇ ⊥̇, so
  -- val (¬̇ φ) ν is ¬ᴮ (val φ ν) ⊔ᴮ ⊥ᴮ and not ¬ᴮ (val φ ν). ⊩f-¬ below
  -- discharges that with ⊔-⊥ before it ever reaches this clause.

  ⊩-¬ : (p : Cond) (u : Pt B)
      → (p ⊩ᴮ (¬ᴮ u))
      ≡ ⋀ Cond (λ q → ((fst q) ≼ᶜ (fst p)) ⇒ ((q ⊩ᴮ u) ⇒ ⊥))
  ⊩-¬ p u = ⇔toPath fwd bwd
    where
      fwd : ⟨ p ⊩ᴮ (¬ᴮ u) ⟩
          → ⟨ ⋀ Cond (λ q → ((fst q) ≼ᶜ (fst p)) ⇒ ((q ⊩ᴮ u) ⇒ ⊥)) ⟩
      fwd h q hqp hqu =
        ⊩ᴮ-zero q (≤-both-⊥ (iᶠ q) u (⊩→≤ q u hqu)
                     (⊩→≤ q (¬ᴮ u) (⊩ᴮ-mono p q (¬ᴮ u) hqp h)))
      bwd : ⟨ ⋀ Cond (λ q → ((fst q) ≼ᶜ (fst p)) ⇒ ((q ⊩ᴮ u) ⇒ ⊥)) ⟩
          → ⟨ p ⊩ᴮ (¬ᴮ u) ⟩
      bwd h = ⊩ᴮ-reg p (¬ᴮ u) step
        where
          step : ⟨ DenseBelow p (λ r → r ⊩ᴮ (¬ᴮ u)) ⟩
          step q hqp =
            ⊩ᴮ-extend q (¬ᴮ u)
              (λ e → h q hqp (≤→⊩ q u (⊥-as-≤ (iᶠ q) u e)))

  ------------------------------------------------------------------------
  -- The disjunction clause
  ------------------------------------------------------------------------

  ⊩-∨← : (p : Cond) (u v : Pt B)
       → ⟨ DenseBelow p (λ r → (r ⊩ᴮ u) ⊔ (r ⊩ᴮ v)) ⟩ → ⟨ p ⊩ᴮ (u ⊔ᴮ v) ⟩
  ⊩-∨← p u v h =
    ⊩ᴮ-reg p (u ⊔ᴮ v)
      (DenseBelow-map p (λ r → (r ⊩ᴮ u) ⊔ (r ⊩ᴮ v)) (λ r → r ⊩ᴮ (u ⊔ᴮ v))
        step h)
    where
      step : (r : Cond) → ⟨ (r ⊩ᴮ u) ⊔ (r ⊩ᴮ v) ⟩ → ⟨ r ⊩ᴮ (u ⊔ᴮ v) ⟩
      step r = PT.rec (snd (r ⊩ᴮ (u ⊔ᴮ v)))
        (λ { (inl hu) → ⊩ᴮ-up r u (u ⊔ᴮ v) (⊔-ub₁ u v) hu
           ; (inr hv) → ⊩ᴮ-up r v (u ⊔ᴮ v) (⊔-ub₂ u v) hv })

  -- The second paid direction. Two decisions, no double negation: if either
  -- meet is nonzero, ⊩ᴮ-extend supplies the refinement and the disjunct;
  -- if both are zero, De Morgan puts iᶠ q below the complement of the join
  -- while the hypothesis puts it below the join, and ⊩ᴮ-zero closes.

  ⊩-∨→ : LEM ℓ → (p : Cond) (u v : Pt B)
       → ⟨ p ⊩ᴮ (u ⊔ᴮ v) ⟩
       → ⟨ DenseBelow p (λ r → (r ⊩ᴮ u) ⊔ (r ⊩ᴮ v)) ⟩
  ⊩-∨→ lem p u v h q hqp = caseU (decide⊥ lem (iᶠ q ⊓ᴮ u))
    where
      hq : ⟨ q ⊩ᴮ (u ⊔ᴮ v) ⟩
      hq = ⊩ᴮ-mono p q (u ⊔ᴮ v) hqp h

      T : Ω
      T = ⋁ Cond (λ r → ((fst r) ≼ᶜ (fst q)) ⊓ ((r ⊩ᴮ u) ⊔ (r ⊩ᴮ v)))

      fromLeft : ⟨ ⋁ Cond (λ r → ((fst r) ≼ᶜ (fst q)) ⊓ (r ⊩ᴮ u)) ⟩ → ⟨ T ⟩
      fromLeft = PT.map (λ { (r , hrq , hru) → r , (hrq , ∣ inl hru ∣₁) })

      fromRight : ⟨ ⋁ Cond (λ r → ((fst r) ≼ᶜ (fst q)) ⊓ (r ⊩ᴮ v)) ⟩ → ⟨ T ⟩
      fromRight = PT.map (λ { (r , hrq , hrv) → r , (hrq , ∣ inr hrv ∣₁) })

      caseV : (iᶠ q ⊓ᴮ u) ≡ ⊥ᴮ
            → ((iᶠ q ⊓ᴮ v) ≡ ⊥ᴮ) ⊎ (((iᶠ q ⊓ᴮ v) ≡ ⊥ᴮ) → Empty.⊥) → ⟨ T ⟩
      caseV eu (inr nzv) =
        fromRight (⊩ᴮ-extend q v (λ e → Empty.rec (nzv e)))
      caseV eu (inl ev) = Empty.rec* (⊩ᴮ-zero q zero-q)
        where
          both : ⟨ iᶠ q ≤ᴮ (¬ᴮ (u ⊔ᴮ v)) ⟩
          both = subst (λ z → ⟨ iᶠ q ≤ᴮ z ⟩) (sym (De-Morgan-⊔ u v))
                   (⊓-glb (¬ᴮ u) (¬ᴮ v) (iᶠ q)
                     (⊓⊥→≤¬ (iᶠ q) u eu) (⊓⊥→≤¬ (iᶠ q) v ev))
          zero-q : iᶠ q ≡ ⊥ᴮ
          zero-q = ≤-both-⊥ (iᶠ q) (u ⊔ᴮ v) (⊩→≤ q (u ⊔ᴮ v) hq) both

      caseU : ((iᶠ q ⊓ᴮ u) ≡ ⊥ᴮ) ⊎ (((iᶠ q ⊓ᴮ u) ≡ ⊥ᴮ) → Empty.⊥) → ⟨ T ⟩
      caseU (inr nzu) = fromLeft (⊩ᴮ-extend q u (λ e → Empty.rec (nzu e)))
      caseU (inl eu) = caseV eu (decide⊥ lem (iᶠ q ⊓ᴮ v))

  ------------------------------------------------------------------------
  -- The existential clause
  ------------------------------------------------------------------------

  -- Free direction. Note what does NOT appear: no name attains the supremum,
  -- no maximum principle, no fullness. The upper bound law is the whole
  -- content.

  ⊩-∃← : (p : Cond) (f : Nameᴮ → Pt B) (E : Pt B)
       → ((σ : Nameᴮ) → ⟨ f σ ≤ᴮ E ⟩)
       → ⟨ DenseBelow p (λ r → ⋁ Nameᴮ (λ σ → r ⊩ᴮ f σ)) ⟩ → ⟨ p ⊩ᴮ E ⟩
  ⊩-∃← p f E ub h =
    ⊩ᴮ-reg p E
      (DenseBelow-map p (λ r → ⋁ Nameᴮ (λ σ → r ⊩ᴮ f σ)) (λ r → r ⊩ᴮ E)
        step h)
    where
      step : (r : Cond) → ⟨ ⋁ Nameᴮ (λ σ → r ⊩ᴮ f σ) ⟩ → ⟨ r ⊩ᴮ E ⟩
      step r = PT.rec (snd (r ⊩ᴮ E))
        (λ { (σ , hσ) → ⊩ᴮ-up r (f σ) E (ub σ) hσ })

  -- The third paid direction, and the one that genuinely eliminates a double
  -- negation at a ⋁ Cond. Decide the goal itself: if it fails, then no
  -- refinement of q forces any instance, so every meet iᶠ q ⊓ᴮ f σ is zero,
  -- so the least upper bound law puts E below the complement of iᶠ q while
  -- the hypothesis puts iᶠ q below E, and ⊩ᴮ-zero closes.

  ⊩-∃→ : LEM ℓ → (p : Cond) (f : Nameᴮ → Pt B) (E : Pt B)
       → ((σ : Nameᴮ) → ⟨ f σ ≤ᴮ E ⟩)
       → ((c : Pt B) → ((σ : Nameᴮ) → ⟨ f σ ≤ᴮ c ⟩) → ⟨ E ≤ᴮ c ⟩)
       → ⟨ p ⊩ᴮ E ⟩
       → ⟨ DenseBelow p (λ r → ⋁ Nameᴮ (λ σ → r ⊩ᴮ f σ)) ⟩
  ⊩-∃→ lem p f E ub lub h q hqp = decideT (lem T)
    where
      T : Ω
      T = ⋁ Cond (λ r → ((fst r) ≼ᶜ (fst q)) ⊓ (⋁ Nameᴮ (λ σ → r ⊩ᴮ f σ)))

      hq : ⟨ q ⊩ᴮ E ⟩
      hq = ⊩ᴮ-mono p q E hqp h

      decideT : ⟨ T ⟩ ⊎ (⟨ T ⟩ → Empty.⊥) → ⟨ T ⟩
      decideT (inl t) = t
      decideT (inr no) = Empty.rec* (⊩ᴮ-zero q zero-q)
        where
          pick : (σ : Nameᴮ)
               → ((iᶠ q ⊓ᴮ f σ) ≡ ⊥ᴮ) ⊎ (((iᶠ q ⊓ᴮ f σ) ≡ ⊥ᴮ) → Empty.⊥)
               → (iᶠ q ⊓ᴮ f σ) ≡ ⊥ᴮ
          pick σ (inl e) = e
          pick σ (inr nz) = Empty.rec
            (no (PT.map (λ { (r , hrq , hrf) → r , (hrq , ∣ σ , hrf ∣₁) })
                        (⊩ᴮ-extend q (f σ) (λ e → Empty.rec (nz e)))))
          zeroes : (σ : Nameᴮ) → (iᶠ q ⊓ᴮ f σ) ≡ ⊥ᴮ
          zeroes σ = pick σ (decide⊥ lem (iᶠ q ⊓ᴮ f σ))
          above : ⟨ E ≤ᴮ (¬ᴮ (iᶠ q)) ⟩
          above = lub (¬ᴮ (iᶠ q))
                    (λ σ → ⊓⊥→≤¬ (f σ) (iᶠ q)
                             (⊓-comm (f σ) (iᶠ q) ∙ zeroes σ))
          zero-q : iᶠ q ≡ ⊥ᴮ
          zero-q = ≤-both-⊥ (iᶠ q) (iᶠ q) (≤ᴮ-refl (iᶠ q))
                     (⊆ˢ-trans (⊩→≤ q E hq) above)

  ------------------------------------------------------------------------
  -- The bounded existential clause, at the guarded family memᴬ σ w ⊓ᴮ f σ
  ------------------------------------------------------------------------

  ⊩-∃∈← : (p : Cond) (m f : Nameᴮ → Pt B) (E : Pt B)
        → ((σ : Nameᴮ) → ⟨ (m σ ⊓ᴮ f σ) ≤ᴮ E ⟩)
        → ⟨ DenseBelow p (λ r → ⋁ Nameᴮ (λ σ → (r ⊩ᴮ m σ) ⊓ (r ⊩ᴮ f σ))) ⟩
        → ⟨ p ⊩ᴮ E ⟩
  ⊩-∃∈← p m f E ub h =
    ⊩-∃← p (λ σ → m σ ⊓ᴮ f σ) E ub
      (DenseBelow-map p
        (λ r → ⋁ Nameᴮ (λ σ → (r ⊩ᴮ m σ) ⊓ (r ⊩ᴮ f σ)))
        (λ r → ⋁ Nameᴮ (λ σ → r ⊩ᴮ (m σ ⊓ᴮ f σ))) step h)
    where
      step : (r : Cond) → ⟨ ⋁ Nameᴮ (λ σ → (r ⊩ᴮ m σ) ⊓ (r ⊩ᴮ f σ)) ⟩
           → ⟨ ⋁ Nameᴮ (λ σ → r ⊩ᴮ (m σ ⊓ᴮ f σ)) ⟩
      step r = PT.map
        (λ { (σ , hσ) → σ , subst ⟨_⟩ (sym (⊩-∧ r (m σ) (f σ))) hσ })

  ⊩-∃∈→ : LEM ℓ → (p : Cond) (m f : Nameᴮ → Pt B) (E : Pt B)
        → ((σ : Nameᴮ) → ⟨ (m σ ⊓ᴮ f σ) ≤ᴮ E ⟩)
        → ((c : Pt B) → ((σ : Nameᴮ) → ⟨ (m σ ⊓ᴮ f σ) ≤ᴮ c ⟩) → ⟨ E ≤ᴮ c ⟩)
        → ⟨ p ⊩ᴮ E ⟩
        → ⟨ DenseBelow p (λ r → ⋁ Nameᴮ (λ σ → (r ⊩ᴮ m σ) ⊓ (r ⊩ᴮ f σ))) ⟩
  ⊩-∃∈→ lem p m f E ub lub h =
    DenseBelow-map p
      (λ r → ⋁ Nameᴮ (λ σ → r ⊩ᴮ (m σ ⊓ᴮ f σ)))
      (λ r → ⋁ Nameᴮ (λ σ → (r ⊩ᴮ m σ) ⊓ (r ⊩ᴮ f σ))) step
      (⊩-∃→ lem p (λ σ → m σ ⊓ᴮ f σ) E ub lub h)
    where
      step : (r : Cond) → ⟨ ⋁ Nameᴮ (λ σ → r ⊩ᴮ (m σ ⊓ᴮ f σ)) ⟩
           → ⟨ ⋁ Nameᴮ (λ σ → (r ⊩ᴮ m σ) ⊓ (r ⊩ᴮ f σ)) ⟩
      step r = PT.map
        (λ { (σ , hσ) → σ , subst ⟨_⟩ (⊩-∧ r (m σ) (f σ)) hσ })

  ------------------------------------------------------------------------
  -- Dichotomy, Bell 2.5(xi), the fifth and last paid site
  ------------------------------------------------------------------------

  ⊩-dichotomy : LEM ℓ → (p : Cond) (u : Pt B)
    → ⟨ ⋁ Cond (λ q → ((fst q) ≼ᶜ (fst p))
                      ⊓ ((q ⊩ᴮ u) ⊔ (q ⊩ᴮ (¬ᴮ u)))) ⟩
  ⊩-dichotomy lem p u = go (decide⊥ lem (iᶠ p ⊓ᴮ u))
    where
      go : ((iᶠ p ⊓ᴮ u) ≡ ⊥ᴮ) ⊎ (((iᶠ p ⊓ᴮ u) ≡ ⊥ᴮ) → Empty.⊥)
         → ⟨ ⋁ Cond (λ q → ((fst q) ≼ᶜ (fst p))
                           ⊓ ((q ⊩ᴮ u) ⊔ (q ⊩ᴮ (¬ᴮ u)))) ⟩
      go (inr nz) =
        PT.map (λ { (r , hrp , hru) → r , (hrp , ∣ inl hru ∣₁) })
               (⊩ᴮ-extend p u (λ e → Empty.rec (nz e)))
      go (inl e) =
        ∣ p , (≼-refl (fst p) (snd p)
             , ∣ inr (≤→⊩ p (¬ᴮ u) (⊓⊥→≤¬ (iᶠ p) u e)) ∣₁) ∣₁

  -- The corollary the truth lemma consumes. It is ⊩-dichotomy read at every
  -- q below p and spends no principle beyond it; it is listed in REPORT-B as
  -- a sixth LEM site so that the count of five for the clauses stays exact.

  ⊩-dichotomy-dense : LEM ℓ → (p : Cond) (u : Pt B)
                    → ⟨ DenseBelow p (λ r → (r ⊩ᴮ u) ⊔ (r ⊩ᴮ (¬ᴮ u))) ⟩
  ⊩-dichotomy-dense lem p u q hqp = ⊩-dichotomy lem q u

  ------------------------------------------------------------------------
  -- The forcing relation at a formula
  ------------------------------------------------------------------------

  -- Architecture section 1.4. The seal the architecture asks for here is an
  -- `opaque` block; the seal this file uses is STRUCTURAL and is strictly
  -- tighter: both _⊩ᴮ_ and val are module parameters, hence variables, hence
  -- cannot unfold at all, which is the form of preamble rule 2 that
  -- decisions D2 and L2 name as the tightest available. Nothing in any type
  -- below is at depth one in a coded operation, let alone depth two, so rule
  -- 2b cannot reach this layer.

  infix 5 _⊩_[_]

  _⊩_[_] : ∀ {k} → Cond → Src k → Envᴮ k → Ω
  p ⊩ φ [ ν ] = p ⊩ᴮ val φ ν

  ⊩-spec : ∀ {k} (p : Cond) (φ : Src k) (ν : Envᴮ k)
         → (p ⊩ φ [ ν ]) ≡ (p ⊩ᴮ val φ ν)
  ⊩-spec p φ ν = refl

  -- THE ROADMAP'S DISPLAYED PUBLIC EQUIVALENCE. Under decision D3 it is refl
  -- and it closes NOTHING. It is printed for readers, exit item X2 says so in
  -- its own words, and the theorem with content is ⊩-unique at the foot of
  -- this file.

  forcing-value : ∀ {k} (p : Cond) (φ : Src k) (ν : Envᴮ k)
                → (p ⊩ φ [ ν ]) ≡ (iᶠ p ≤ᴮ val φ ν)
  forcing-value p φ ν = ⊩ᴮ-spec p (val φ ν)

  ⊩-mono : ∀ {k} (p q : Cond) (φ : Src k) (ν : Envᴮ k)
         → ⟨ (fst q) ≼ᶜ (fst p) ⟩ → ⟨ p ⊩ φ [ ν ] ⟩ → ⟨ q ⊩ φ [ ν ] ⟩
  ⊩-mono p q φ ν = ⊩ᴮ-mono p q (val φ ν)

  ⊩-down : ∀ {k} (p : Cond) (φ : Src k) (ν : Envᴮ k)
         → ⟨ p ⊩ φ [ ν ] ⟩ → ⟨ DenseBelow p (λ r → r ⊩ φ [ ν ]) ⟩
  ⊩-down p φ ν = ⊩ᴮ-down p (val φ ν)

  ⊩-reg : ∀ {k} (p : Cond) (φ : Src k) (ν : Envᴮ k)
        → ⟨ DenseBelow p (λ r → r ⊩ φ [ ν ]) ⟩ → ⟨ p ⊩ φ [ ν ] ⟩
  ⊩-reg p φ ν = ⊩ᴮ-reg p (val φ ν)

  -- TRAP T-B3 discharged, once, here. `¬̇ φ` is `φ ⇒̇ ⊥̇`, and the compiler's
  -- implication law emits the material implication, so val (¬̇ φ) ν is
  -- ¬ᴮ (val φ ν) ⊔ᴮ ⊥ᴮ and NOT ¬ᴮ (val φ ν). ⊔-⊥ (K4/Implication.agda:133)
  -- is what closes the gap, and a clause written without it would be a well
  -- typed statement about the wrong element of the algebra.

  val-¬ : ∀ {k} (φ : Src k) (ν : Envᴮ k) → val (¬̇ φ) ν ≡ (¬ᴮ (val φ ν))
  val-¬ φ ν =
      law-⇒ φ ⊥̇ ν
    ∙ cong (λ z → (val φ ν) ⇒ᴮ z) (law-⊥ ν)
    ∙ ⊔-⊥ (¬ᴮ (val φ ν))

  ⊩f-¬ : ∀ {k} (p : Cond) (φ : Src k) (ν : Envᴮ k)
       → (p ⊩ (¬̇ φ) [ ν ])
       ≡ ⋀ Cond (λ q → ((fst q) ≼ᶜ (fst p)) ⇒ ((q ⊩ φ [ ν ]) ⇒ ⊥))
  ⊩f-¬ p φ ν = cong (λ z → p ⊩ᴮ z) (val-¬ φ ν) ∙ ⊩-¬ p (val φ ν)

  ------------------------------------------------------------------------
  -- The clause record
  ------------------------------------------------------------------------

  -- EVERY FIELD IS A PAIR OF ENTAILMENTS AND NO FIELD IS A PATH IN Ω. That
  -- is preamble rule 8 and ledger clause L13, and it is what puts the record
  -- at Type ℓ so that it may index a ⋁, checked by clauses-level-check
  -- below. Architecture section 1.5 prints at-∈, at-≐ and at-⊥ as PATHS,
  -- which contradicts its own sentence two lines later that the record has no
  -- field that is a path in Ω; the entailment form is the one that keeps the
  -- stated level, so it is the one used.
  --
  -- at-⊥ is a single entailment on purpose: the converse, ⟨ ⊥ ⟩ → ⟨ R p ⊥̇ ν ⟩,
  -- is free from falsity and would be a field nobody could fail to supply.
  --
  -- The architecture also lists a field at-mono. It is NOT a field here,
  -- because it is a THEOREM: clauses-mono below derives it from the fields
  -- that are here. Carrying it would make ForcingClauses harder to inhabit
  -- and would therefore make ⊩-unique weaker, which exit item X2 counts as a
  -- failure of the item rather than a variant of it.
  --
  -- The two bounded quantifier clauses are the only ones that mention ⊩ᴮ
  -- beside R. They must: the guard `σ ∈ x` of a bounded quantifier is not a
  -- subformula of the node, so no clause phrased purely in R can say what the
  -- guard forces. The guard is read at memᴬ, which is exactly the atomic
  -- datum the two atomic clauses already pin.

  record ForcingClauses
    (R : ∀ {k} → Cond → Src k → Envᴮ k → Ω) : Type ℓ where
    field
      at-∈→ : ∀ {k} (p : Cond) (a b : Fin k) (ν : Envᴮ k)
            → ⟨ R p (var a ∈̇ var b) ν ⟩
            → ⟨ p ⊩ᴮ memᴬ (fst (lookup a ν)) (fst (lookup b ν)) ⟩
      at-∈← : ∀ {k} (p : Cond) (a b : Fin k) (ν : Envᴮ k)
            → ⟨ p ⊩ᴮ memᴬ (fst (lookup a ν)) (fst (lookup b ν)) ⟩
            → ⟨ R p (var a ∈̇ var b) ν ⟩
      at-≐→ : ∀ {k} (p : Cond) (a b : Fin k) (ν : Envᴮ k)
            → ⟨ R p (var a ≐ var b) ν ⟩
            → ⟨ p ⊩ᴮ eqᴬ (fst (lookup a ν)) (fst (lookup b ν)) ⟩
      at-≐← : ∀ {k} (p : Cond) (a b : Fin k) (ν : Envᴮ k)
            → ⟨ p ⊩ᴮ eqᴬ (fst (lookup a ν)) (fst (lookup b ν)) ⟩
            → ⟨ R p (var a ≐ var b) ν ⟩
      at-⊥  : ∀ {k} (p : Cond) (ν : Envᴮ k) → ⟨ R {k} p ⊥̇ ν ⟩ → ⟨ ⊥ ⟩
      at-∧→ : ∀ {k} (p : Cond) (φ ψ : Src k) (ν : Envᴮ k)
            → ⟨ R p (φ ∧̇ ψ) ν ⟩ → ⟨ (R p φ ν) ⊓ (R p ψ ν) ⟩
      at-∧← : ∀ {k} (p : Cond) (φ ψ : Src k) (ν : Envᴮ k)
            → ⟨ R p φ ν ⟩ → ⟨ R p ψ ν ⟩ → ⟨ R p (φ ∧̇ ψ) ν ⟩
      at-∨→ : ∀ {k} (p : Cond) (φ ψ : Src k) (ν : Envᴮ k)
            → ⟨ R p (φ ∨̇ ψ) ν ⟩
            → ⟨ DenseBelow p (λ r → (R r φ ν) ⊔ (R r ψ ν)) ⟩
      at-∨← : ∀ {k} (p : Cond) (φ ψ : Src k) (ν : Envᴮ k)
            → ⟨ DenseBelow p (λ r → (R r φ ν) ⊔ (R r ψ ν)) ⟩
            → ⟨ R p (φ ∨̇ ψ) ν ⟩
      at-⇒→ : ∀ {k} (p : Cond) (φ ψ : Src k) (ν : Envᴮ k)
            → ⟨ R p (φ ⇒̇ ψ) ν ⟩
            → (q : Cond) → ⟨ (fst q) ≼ᶜ (fst p) ⟩
            → ⟨ R q φ ν ⟩ → ⟨ R q ψ ν ⟩
      at-⇒← : ∀ {k} (p : Cond) (φ ψ : Src k) (ν : Envᴮ k)
            → ((q : Cond) → ⟨ (fst q) ≼ᶜ (fst p) ⟩
               → ⟨ R q φ ν ⟩ → ⟨ R q ψ ν ⟩)
            → ⟨ R p (φ ⇒̇ ψ) ν ⟩
      at-∀→ : ∀ {k} (p : Cond) (φ : Src (suc k)) (ν : Envᴮ k)
            → ⟨ R p (∀̇ φ) ν ⟩ → (σ : Nameᴮ) → ⟨ R p φ (σ ∷ ν) ⟩
      at-∀← : ∀ {k} (p : Cond) (φ : Src (suc k)) (ν : Envᴮ k)
            → ((σ : Nameᴮ) → ⟨ R p φ (σ ∷ ν) ⟩) → ⟨ R p (∀̇ φ) ν ⟩
      at-∃→ : ∀ {k} (p : Cond) (φ : Src (suc k)) (ν : Envᴮ k)
            → ⟨ R p (∃̇ φ) ν ⟩
            → ⟨ DenseBelow p (λ r → ⋁ Nameᴮ (λ σ → R r φ (σ ∷ ν))) ⟩
      at-∃← : ∀ {k} (p : Cond) (φ : Src (suc k)) (ν : Envᴮ k)
            → ⟨ DenseBelow p (λ r → ⋁ Nameᴮ (λ σ → R r φ (σ ∷ ν))) ⟩
            → ⟨ R p (∃̇ φ) ν ⟩
      at-∀∈→ : ∀ {k} (p : Cond) (j : Fin k) (φ : Src (suc k)) (ν : Envᴮ k)
             → ⟨ R p (∀̇∈ (var j) φ) ν ⟩
             → (q : Cond) → ⟨ (fst q) ≼ᶜ (fst p) ⟩ → (σ : Nameᴮ)
             → ⟨ q ⊩ᴮ memᴬ (fst σ) (fst (lookup j ν)) ⟩
             → ⟨ R q φ (σ ∷ ν) ⟩
      at-∀∈← : ∀ {k} (p : Cond) (j : Fin k) (φ : Src (suc k)) (ν : Envᴮ k)
             → ((q : Cond) → ⟨ (fst q) ≼ᶜ (fst p) ⟩ → (σ : Nameᴮ)
                → ⟨ q ⊩ᴮ memᴬ (fst σ) (fst (lookup j ν)) ⟩
                → ⟨ R q φ (σ ∷ ν) ⟩)
             → ⟨ R p (∀̇∈ (var j) φ) ν ⟩
      at-∃∈→ : ∀ {k} (p : Cond) (j : Fin k) (φ : Src (suc k)) (ν : Envᴮ k)
             → ⟨ R p (∃̇∈ (var j) φ) ν ⟩
             → ⟨ DenseBelow p (λ r → ⋁ Nameᴮ (λ σ →
                 (r ⊩ᴮ memᴬ (fst σ) (fst (lookup j ν))) ⊓ (R r φ (σ ∷ ν)))) ⟩
      at-∃∈← : ∀ {k} (p : Cond) (j : Fin k) (φ : Src (suc k)) (ν : Envᴮ k)
             → ⟨ DenseBelow p (λ r → ⋁ Nameᴮ (λ σ →
                 (r ⊩ᴮ memᴬ (fst σ) (fst (lookup j ν))) ⊓ (R r φ (σ ∷ ν)))) ⟩
             → ⟨ R p (∃̇∈ (var j) φ) ν ⟩

  -- EXIT ITEM X2's LEVEL CHECK, mechanised. This declaration elaborates only
  -- if ForcingClauses R is at Type ℓ, since ⋁ takes a Type ℓ index
  -- (Base/Truth.lagda.md:72). If any field were written as a path in Ω the
  -- record would rise to Type (ℓ-suc ℓ) and this line would fail.

  clauses-level-check : (R : ∀ {k} → Cond → Src k → Envᴮ k → Ω)
                      → (ForcingClauses R → Ω) → Ω
  clauses-level-check R P = ⋁ (ForcingClauses R) P

  ------------------------------------------------------------------------
  -- The forcing relation satisfies the clauses
  ------------------------------------------------------------------------

  -- Each field is one of the ten Boolean clauses above, conjugated by the
  -- compiler law for that node. The laws enter by subst, at variables, which
  -- is preamble rule 3's remedy in K2's own i-compat→-at shape
  -- (CodedCompletion.agda:1171-1178): no clause is ever stated at a term that
  -- names a construction of the compiler.

  ⊩-clauses : LEM ℓ → ForcingClauses (λ {k} p φ ν → p ⊩ φ [ ν ])
  ⊩-clauses lem = record
    { at-∈→ = λ p a b ν h → subst (λ z → ⟨ p ⊩ᴮ z ⟩) (law-∈ a b ν) h
    ; at-∈← = λ p a b ν h → subst (λ z → ⟨ p ⊩ᴮ z ⟩) (sym (law-∈ a b ν)) h
    ; at-≐→ = λ p a b ν h → subst (λ z → ⟨ p ⊩ᴮ z ⟩) (law-≐ a b ν) h
    ; at-≐← = λ p a b ν h → subst (λ z → ⟨ p ⊩ᴮ z ⟩) (sym (law-≐ a b ν)) h
    ; at-⊥  = λ p ν h → ⊩ᴮ-⊥ p (subst (λ z → ⟨ p ⊩ᴮ z ⟩) (law-⊥ ν) h)
    ; at-∧→ = λ p φ ψ ν h →
        subst ⟨_⟩ (⊩-∧ p (val φ ν) (val ψ ν))
          (subst (λ z → ⟨ p ⊩ᴮ z ⟩) (law-∧ φ ψ ν) h)
    ; at-∧← = λ p φ ψ ν hφ hψ →
        subst (λ z → ⟨ p ⊩ᴮ z ⟩) (sym (law-∧ φ ψ ν))
          (subst ⟨_⟩ (sym (⊩-∧ p (val φ ν) (val ψ ν))) (hφ , hψ))
    ; at-∨→ = λ p φ ψ ν h →
        ⊩-∨→ lem p (val φ ν) (val ψ ν)
          (subst (λ z → ⟨ p ⊩ᴮ z ⟩) (law-∨ φ ψ ν) h)
    ; at-∨← = λ p φ ψ ν h →
        subst (λ z → ⟨ p ⊩ᴮ z ⟩) (sym (law-∨ φ ψ ν))
          (⊩-∨← p (val φ ν) (val ψ ν) h)
    ; at-⇒→ = λ p φ ψ ν h →
        ⊩-⇒→ p (val φ ν) (val ψ ν)
          (subst (λ z → ⟨ p ⊩ᴮ z ⟩) (law-⇒ φ ψ ν) h)
    ; at-⇒← = λ p φ ψ ν h →
        subst (λ z → ⟨ p ⊩ᴮ z ⟩) (sym (law-⇒ φ ψ ν))
          (⊩-⇒← lem p (val φ ν) (val ψ ν) h)
    ; at-∀→ = λ p φ ν h →
        ⊩-∀→ p (val (∀̇ φ) ν) (λ τ → val φ (τ ∷ ν)) (law-∀-lb φ ν) h
    ; at-∀← = λ p φ ν h →
        ⊩-∀← p (val (∀̇ φ) ν) (λ τ → val φ (τ ∷ ν)) (law-∀-glb φ ν) h
    ; at-∃→ = λ p φ ν h →
        ⊩-∃→ lem p (λ τ → val φ (τ ∷ ν)) (val (∃̇ φ) ν)
          (law-∃-ub φ ν) (law-∃-lub φ ν) h
    ; at-∃← = λ p φ ν h →
        ⊩-∃← p (λ τ → val φ (τ ∷ ν)) (val (∃̇ φ) ν) (law-∃-ub φ ν) h
    ; at-∀∈→ = λ p j φ ν h q hqp σ hm →
        ⊩-⇒→ p (memᴬ (fst σ) (fst (lookup j ν))) (val φ (σ ∷ ν))
          (⊩-∀∈→ p (val (∀̇∈ (var j) φ) ν)
            (λ τ → memᴬ (fst τ) (fst (lookup j ν)) ⇒ᴮ val φ (τ ∷ ν))
            (law-∀∈-lb j φ ν) h σ)
          q hqp hm
    ; at-∀∈← = λ p j φ ν h →
        ⊩-∀∈← p (val (∀̇∈ (var j) φ) ν)
          (λ τ → memᴬ (fst τ) (fst (lookup j ν)) ⇒ᴮ val φ (τ ∷ ν))
          (law-∀∈-glb j φ ν)
          (λ σ → ⊩-⇒← lem p (memᴬ (fst σ) (fst (lookup j ν)))
                   (val φ (σ ∷ ν)) (λ q hqp hm → h q hqp σ hm))
    ; at-∃∈→ = λ p j φ ν h →
        ⊩-∃∈→ lem p (λ τ → memᴬ (fst τ) (fst (lookup j ν)))
          (λ τ → val φ (τ ∷ ν)) (val (∃̇∈ (var j) φ) ν)
          (law-∃∈-ub j φ ν) (law-∃∈-lub j φ ν) h
    ; at-∃∈← = λ p j φ ν h →
        ⊩-∃∈← p (λ τ → memᴬ (fst τ) (fst (lookup j ν)))
          (λ τ → val φ (τ ∷ ν)) (val (∃̇∈ (var j) φ) ν)
          (law-∃∈-ub j φ ν) h
    }

  ------------------------------------------------------------------------
  -- UNIQUENESS. This is the theorem exit item X2 closes on.
  ------------------------------------------------------------------------

  -- What it says. Let R be ANY Ω valued relation between conditions,
  -- formulas and environments. If R satisfies the clause record, then R is
  -- the forcing relation, pointwise, at every formula, every condition and
  -- every environment. Nothing about R is assumed beyond the record: it is
  -- not assumed monotone, not assumed to be of the form iᶠ p ≤ᴮ _, not
  -- assumed to factor through a value at all.
  --
  -- Why this and not `forcing-value`. Under decision D3 the displayed public
  -- equivalence is refl (see forcing-value above) and therefore has no
  -- content: it could not fail whatever the clauses said. Preamble rule 6
  -- says a reflexivity theorem is worthless unless a deliberate break is
  -- shown to fail. ⊩-unique is where the clauses are load bearing, and
  -- REPORT-B records the deliberate break that falsifies one clause and the
  -- error this proof then produces.
  --
  -- How it is proved. Induction on the formula, with the condition and the
  -- environment generalized, because the disjunction, implication, existential
  -- and bounded clauses all quantify over conditions below p and the two
  -- unbounded quantifier clauses all extend the environment. Every case is
  -- the same two lines: take R's clause forward, transport pointwise along
  -- the induction hypothesis, and put ⊩'s clause back. The clauses for ⊩ are
  -- not re-derived here: they are ⊩-clauses, read as a second inhabitant of
  -- the very same record, which is what makes the proof symmetric in R and ⊩.

  ⊩-unique : LEM ℓ → (R : ∀ {k} → Cond → Src k → Envᴮ k → Ω)
           → ForcingClauses R
           → ∀ {k} (p : Cond) (φ : Src k) (ν : Envᴮ k)
           → R p φ ν ≡ (p ⊩ φ [ ν ])
  ⊩-unique lem R fc p φ ν = go φ ν p
    where
      module A = ForcingClauses fc
      module C = ForcingClauses (⊩-clauses lem)

      go : ∀ {k} (φ : Src k) (ν : Envᴮ k) (p : Cond)
         → R p φ ν ≡ (p ⊩ φ [ ν ])

      go (var a ∈̇ var b) ν p =
        ⇔toPath (λ h → C.at-∈← p a b ν (A.at-∈→ p a b ν h))
                (λ h → A.at-∈← p a b ν (C.at-∈→ p a b ν h))
      go (var a ∈̇ con ()) ν p
      go (con () ∈̇ t) ν p

      go (var a ≐ var b) ν p =
        ⇔toPath (λ h → C.at-≐← p a b ν (A.at-≐→ p a b ν h))
                (λ h → A.at-≐← p a b ν (C.at-≐→ p a b ν h))
      go (var a ≐ con ()) ν p
      go (con () ≐ t) ν p

      go ⊥̇ ν p =
        ⇔toPath (λ h → Empty.rec* (A.at-⊥ p ν h))
                (λ h → Empty.rec* (C.at-⊥ p ν h))

      go (φ ∧̇ ψ) ν p = ⇔toPath fwd bwd
        where
          fwd : ⟨ R p (φ ∧̇ ψ) ν ⟩ → ⟨ p ⊩ (φ ∧̇ ψ) [ ν ] ⟩
          fwd h = C.at-∧← p φ ψ ν
                    (subst ⟨_⟩ (go φ ν p) (fst (A.at-∧→ p φ ψ ν h)))
                    (subst ⟨_⟩ (go ψ ν p) (snd (A.at-∧→ p φ ψ ν h)))
          bwd : ⟨ p ⊩ (φ ∧̇ ψ) [ ν ] ⟩ → ⟨ R p (φ ∧̇ ψ) ν ⟩
          bwd h = A.at-∧← p φ ψ ν
                    (subst ⟨_⟩ (sym (go φ ν p)) (fst (C.at-∧→ p φ ψ ν h)))
                    (subst ⟨_⟩ (sym (go ψ ν p)) (snd (C.at-∧→ p φ ψ ν h)))

      go (φ ∨̇ ψ) ν p = ⇔toPath fwd bwd
        where
          fwd : ⟨ R p (φ ∨̇ ψ) ν ⟩ → ⟨ p ⊩ (φ ∨̇ ψ) [ ν ] ⟩
          fwd h = C.at-∨← p φ ψ ν
            (DenseBelow-map p (λ r → (R r φ ν) ⊔ (R r ψ ν))
                              (λ r → (r ⊩ φ [ ν ]) ⊔ (r ⊩ ψ [ ν ]))
              (λ r → PT.map
                (λ { (inl x) → inl (subst ⟨_⟩ (go φ ν r) x)
                   ; (inr y) → inr (subst ⟨_⟩ (go ψ ν r) y) }))
              (A.at-∨→ p φ ψ ν h))
          bwd : ⟨ p ⊩ (φ ∨̇ ψ) [ ν ] ⟩ → ⟨ R p (φ ∨̇ ψ) ν ⟩
          bwd h = A.at-∨← p φ ψ ν
            (DenseBelow-map p (λ r → (r ⊩ φ [ ν ]) ⊔ (r ⊩ ψ [ ν ]))
                              (λ r → (R r φ ν) ⊔ (R r ψ ν))
              (λ r → PT.map
                (λ { (inl x) → inl (subst ⟨_⟩ (sym (go φ ν r)) x)
                   ; (inr y) → inr (subst ⟨_⟩ (sym (go ψ ν r)) y) }))
              (C.at-∨→ p φ ψ ν h))

      go (φ ⇒̇ ψ) ν p = ⇔toPath fwd bwd
        where
          fwd : ⟨ R p (φ ⇒̇ ψ) ν ⟩ → ⟨ p ⊩ (φ ⇒̇ ψ) [ ν ] ⟩
          fwd h = C.at-⇒← p φ ψ ν
            (λ q hqp hu → subst ⟨_⟩ (go ψ ν q)
              (A.at-⇒→ p φ ψ ν h q hqp (subst ⟨_⟩ (sym (go φ ν q)) hu)))
          bwd : ⟨ p ⊩ (φ ⇒̇ ψ) [ ν ] ⟩ → ⟨ R p (φ ⇒̇ ψ) ν ⟩
          bwd h = A.at-⇒← p φ ψ ν
            (λ q hqp hu → subst ⟨_⟩ (sym (go ψ ν q))
              (C.at-⇒→ p φ ψ ν h q hqp (subst ⟨_⟩ (go φ ν q) hu)))

      go (∀̇ φ) ν p = ⇔toPath fwd bwd
        where
          fwd : ⟨ R p (∀̇ φ) ν ⟩ → ⟨ p ⊩ (∀̇ φ) [ ν ] ⟩
          fwd h = C.at-∀← p φ ν
            (λ σ → subst ⟨_⟩ (go φ (σ ∷ ν) p) (A.at-∀→ p φ ν h σ))
          bwd : ⟨ p ⊩ (∀̇ φ) [ ν ] ⟩ → ⟨ R p (∀̇ φ) ν ⟩
          bwd h = A.at-∀← p φ ν
            (λ σ → subst ⟨_⟩ (sym (go φ (σ ∷ ν) p)) (C.at-∀→ p φ ν h σ))

      go (∃̇ φ) ν p = ⇔toPath fwd bwd
        where
          fwd : ⟨ R p (∃̇ φ) ν ⟩ → ⟨ p ⊩ (∃̇ φ) [ ν ] ⟩
          fwd h = C.at-∃← p φ ν
            (DenseBelow-map p (λ r → ⋁ Nameᴮ (λ σ → R r φ (σ ∷ ν)))
                              (λ r → ⋁ Nameᴮ (λ σ → r ⊩ φ [ σ ∷ ν ]))
              (λ r → PT.map
                (λ { (σ , hσ) → σ , subst ⟨_⟩ (go φ (σ ∷ ν) r) hσ }))
              (A.at-∃→ p φ ν h))
          bwd : ⟨ p ⊩ (∃̇ φ) [ ν ] ⟩ → ⟨ R p (∃̇ φ) ν ⟩
          bwd h = A.at-∃← p φ ν
            (DenseBelow-map p (λ r → ⋁ Nameᴮ (λ σ → r ⊩ φ [ σ ∷ ν ]))
                              (λ r → ⋁ Nameᴮ (λ σ → R r φ (σ ∷ ν)))
              (λ r → PT.map
                (λ { (σ , hσ) → σ , subst ⟨_⟩ (sym (go φ (σ ∷ ν) r)) hσ }))
              (C.at-∃→ p φ ν h))

      go (∀̇∈ (var j) φ) ν p = ⇔toPath fwd bwd
        where
          fwd : ⟨ R p (∀̇∈ (var j) φ) ν ⟩ → ⟨ p ⊩ (∀̇∈ (var j) φ) [ ν ] ⟩
          fwd h = C.at-∀∈← p j φ ν
            (λ q hqp σ hm → subst ⟨_⟩ (go φ (σ ∷ ν) q)
              (A.at-∀∈→ p j φ ν h q hqp σ hm))
          bwd : ⟨ p ⊩ (∀̇∈ (var j) φ) [ ν ] ⟩ → ⟨ R p (∀̇∈ (var j) φ) ν ⟩
          bwd h = A.at-∀∈← p j φ ν
            (λ q hqp σ hm → subst ⟨_⟩ (sym (go φ (σ ∷ ν) q))
              (C.at-∀∈→ p j φ ν h q hqp σ hm))
      go (∀̇∈ (con ()) φ) ν p

      go (∃̇∈ (var j) φ) ν p = ⇔toPath fwd bwd
        where
          fwd : ⟨ R p (∃̇∈ (var j) φ) ν ⟩ → ⟨ p ⊩ (∃̇∈ (var j) φ) [ ν ] ⟩
          fwd h = C.at-∃∈← p j φ ν
            (DenseBelow-map p
              (λ r → ⋁ Nameᴮ (λ σ →
                 (r ⊩ᴮ memᴬ (fst σ) (fst (lookup j ν))) ⊓ (R r φ (σ ∷ ν))))
              (λ r → ⋁ Nameᴮ (λ σ →
                 (r ⊩ᴮ memᴬ (fst σ) (fst (lookup j ν))) ⊓ (r ⊩ φ [ σ ∷ ν ])))
              (λ r → PT.map
                (λ { (σ , hm , hφ) →
                     σ , (hm , subst ⟨_⟩ (go φ (σ ∷ ν) r) hφ) }))
              (A.at-∃∈→ p j φ ν h))
          bwd : ⟨ p ⊩ (∃̇∈ (var j) φ) [ ν ] ⟩ → ⟨ R p (∃̇∈ (var j) φ) ν ⟩
          bwd h = A.at-∃∈← p j φ ν
            (DenseBelow-map p
              (λ r → ⋁ Nameᴮ (λ σ →
                 (r ⊩ᴮ memᴬ (fst σ) (fst (lookup j ν))) ⊓ (r ⊩ φ [ σ ∷ ν ])))
              (λ r → ⋁ Nameᴮ (λ σ →
                 (r ⊩ᴮ memᴬ (fst σ) (fst (lookup j ν))) ⊓ (R r φ (σ ∷ ν))))
              (λ r → PT.map
                (λ { (σ , hm , hφ) →
                     σ , (hm , subst ⟨_⟩ (sym (go φ (σ ∷ ν) r)) hφ) }))
              (C.at-∃∈→ p j φ ν h))
      go (∃̇∈ (con ()) φ) ν p

  -- The architecture's at-mono, as a THEOREM rather than a field. Any
  -- relation satisfying the clauses is monotone, because by uniqueness it IS
  -- the forcing relation and the forcing relation is monotone. Carrying this
  -- as a field would have added a hypothesis to ⊩-unique that ⊩-unique does
  -- not use.

  clauses-mono : LEM ℓ → (R : ∀ {k} → Cond → Src k → Envᴮ k → Ω)
               → ForcingClauses R
               → ∀ {k} (p q : Cond) (φ : Src k) (ν : Envᴮ k)
               → ⟨ (fst q) ≼ᶜ (fst p) ⟩ → ⟨ R p φ ν ⟩ → ⟨ R q φ ν ⟩
  clauses-mono lem R fc p q φ ν hqp h =
    subst ⟨_⟩ (sym (⊩-unique lem R fc q φ ν))
      (⊩-mono p q φ ν hqp (subst ⟨_⟩ (⊩-unique lem R fc p φ ν) h))

  -- And the packaged reading a consumer wants: two relations satisfying the
  -- clauses are equal. This is the sense in which the ten clauses DEFINE
  -- forcing, which is the content the displayed equivalence does not carry.

  clauses-determine : LEM ℓ
    → (R R' : ∀ {k} → Cond → Src k → Envᴮ k → Ω)
    → ForcingClauses R → ForcingClauses R'
    → ∀ {k} (p : Cond) (φ : Src k) (ν : Envᴮ k) → R p φ ν ≡ R' p φ ν
  clauses-determine lem R R' fc fc' p φ ν =
    ⊩-unique lem R fc p φ ν ∙ sym (⊩-unique lem R' fc' p φ ν)

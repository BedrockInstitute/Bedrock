{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.549]  SuccIntoSubsets, and the formula it turns on.
--
-- W3 IS SECTION 3, AND IT WAS WRITTEN FIRST AND TYPECHECKED ALONE.
-- The slice is agents/tasks/LJ-1-549/runs/W3.agda, runs w3-1.out to
-- w3-3.out, exit 0.
--
-- THE OBLIGATION IS NOT INHABITED.  The stop is
-- agents/tasks/LJ-1-549/review-of-succ-into-subsets.md.  This file
-- carries NO hole and NO postulate: every reduction in it is a
-- measurement rather than a claim, which is the [LJ-1.533] discipline.
-- Nothing lands in src/.
--
-- WHAT THIS FILE MEASURES, IN ONE LINE EACH.
--
--   Section 1.  D-10, the choice of b.  The largest admissible b is
--               FREE: `hasPowerL` (src/L/Axioms/Power.lagda.md:187) is
--               unconditional, so the power set of κ inside L is a term
--               with no `zf` in scope, and its membership IS `⊆ˢ κ`.
--   Section 2.  THE FREEDOM IN b IS WORTH NOTHING.  `SuccIntoSubsets`
--               and a code at the pair (δ , powL κ) are EQUIVALENT,
--               both directions, unconditionally.  So this task is B10
--               itself and not a weakening of it.
--   Section 3.  W3.  The table formula, four conjuncts.  Three are
--               written from delivered vocabulary.  The fourth has no
--               producer and enters as a parameter.
--   Section 4.  THE CARVE, GENERIC IN THE LINK.  Given the assignment
--               and the link, the code follows.  So the whole residue
--               is the pair (assignment , link) and nothing else.
--   Section 5.  THE ONE DELIVERED CODE PRODUCER IS REFUTED AT THIS
--               SOURCE.  δ is not an ordinal successor.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M8g" on this pane.  I
-- did not set it.  One Agda process at a time.  No heap event.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-549.Probe549 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_; ∃̇_ )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-elim )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Recursion {ℓ} lem using ( smallDom )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Power {ℓ} lem using ( hasPowerL )
open import L.Axioms.Numerals {ℓ} using ( sucʟ; sucʟ-fst )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Cardinal {ℓ} lem using ( InjCode; IsCardinalL; _↪_ )
open import L.CodedShift {ℓ} lem using ( shift-coded )
open import L.GCH {ℓ} lem using ( SuccCardL; InjL )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; svAt; svAt-in; domAt; domAt-intro
        ; prʟ; prʟ-fst )
open import L.Coding.Injection {ℓ} lem using ( injAt; injAt-in )

open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.Foundations.Prelude using ( isPropIsContr )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
open import Cubical.HITs.CumulativeHierarchy.Base
  using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_; sucV )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

-- [LJ-1.546] IS GO AND ITS PROBE CARRIES NO HOLE, so the statement is
-- taken from the file that typechecked and cannot have drifted.
import LJ-1-546.Probe546 {ℓ} lem as P546

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( ℩; ℩-spec; _⊆ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

private
  s2 : ∀ {n} → Fin n → Fin (suc (suc n))
  s2 i = suc (suc i)

-- =====================================================================
-- SECTION 1.  D-10, BEFORE ANY FORMULA, AND IT IS THE CHOICE OF `b`.
--
--   THE SET I TAKE IS THE POWER SET OF κ INSIDE L, and it costs
--   nothing.  `hasPowerL` (src/L/Axioms/Power.lagda.md:187) is an
--   unconditional term of the tree: it separates the bounding stage
--   `Bound.β κ` by `subFo κ` (:98-99, :187-190).  So `powL κ` is a term
--   with NO `zf : isZFModel` anywhere in its type, and `℩-spec` reads
--   its membership as inclusion in κ ON THE NOSE.
--
--   WHY EVERY MEMBER OF IT IS A SUBSET OF κ: because that is what it
--   was separated by.  `powL-sub` is one `subst`.
--
--   THE OTHER TWO CANDIDATES THE BRIEF NAMED.  A STAGE is refuted at
--   the second conjunct: a member of `Lset β` is an arbitrary L-set and
--   not a subset of κ.  A BOUNDED COLLECTION is `powL κ` restricted,
--   and section 2 shows a restriction can only cost more, never less.
-- =====================================================================

powL : S → S
powL κ = ℩ (hasPowerL κ)

powL-sub : (κ y : S) → ⟨ fst y ∈ fst (powL κ) ⟩ → ⟨ y ⊆ˢ κ ⟩
powL-sub κ y m = subst ⟨_⟩ (℩-spec (hasPowerL κ) y) m

powL-in : (κ y : S) → ⟨ y ⊆ˢ κ ⟩ → ⟨ fst y ∈ fst (powL κ) ⟩
powL-in κ y h = subst ⟨_⟩ (sym (℩-spec (hasPowerL κ) y)) h

-- AND IT IS THE MODEL'S OWN POWER SET, so nothing is dodged by
-- dropping `zf`.  Both are `℩` of a proof of the SAME `isContr`, and
-- `isContr` is a proposition.
powL-is-𝒫 : (zf : ModelL.isZFModel) (κ : S)
          → powL κ ≡ ModelL.isZFModel.𝒫 zf κ
powL-is-𝒫 zf κ =
  cong ℩ (isPropIsContr (hasPowerL κ) (ModelL.isZFModel.hasPower zf κ))

-- =====================================================================
-- SECTION 2.  THE FREEDOM IN `b` IS WORTH NOTHING, AND THIS IS THE
--             TASK'S FIRST FINDING.
--
--   The brief says "The freedom in `b` is the whole point of the
--   reduction, and it is yours to use."  IT CANNOT BE USED, because
--   the largest admissible `b` is already free.
--
--   `SubsetsAt` is `[LJ-1.546]`'s conclusion at one pair.  `PowerAt` is
--   B10's conclusion at the same pair, stated with `powL` instead of
--   the model's `𝒫`.  The two implications below are each three lines,
--   and together they say the two statements are the SAME PROBLEM.
--
--   SO THIS TASK IS B10 AND NOT A WEAKENING OF B10.  `[LJ-1.546]`'s
--   reduction removes the `zf` record from the statement, which is
--   real, and it removes nothing else.
-- =====================================================================

SubsetsAt : (κ δ : S) → Type (ℓ-suc ℓ)
SubsetsAt κ δ =
  ∥ Σ[ b ∈ S ] Σ[ F ∈ S ]
     ( InjCode F δ b
     × ((y : S) → ⟨ fst y ∈ fst b ⟩ → ⟨ y ⊆ˢ κ ⟩) ) ∥₁

PowerAt : (κ δ : S) → Type (ℓ-suc ℓ)
PowerAt κ δ = ∥ Σ[ F ∈ S ] InjCode F δ (powL κ) ∥₁

-- THE PIN.  `SuccIntoSubsets` is `SubsetsAt` under `SuccCardL`, on the
-- nose.  If the two had drifted, the identity function below would not
-- typecheck.  This is the `[LJ-1.537]` pinning device
-- (agents/tasks/LJ-1-537/runs/Pin.agda:46-62), at one line.
statement-is-pointwise :
  P546.SuccIntoSubsets → (κ δ : S) → SuccCardL δ κ → SubsetsAt κ δ
statement-is-pointwise t = t

pointwise-is-statement :
  ((κ δ : S) → SuccCardL δ κ → SubsetsAt κ δ) → P546.SuccIntoSubsets
pointwise-is-statement t = t

-- ONE DIRECTION.  Take `b := powL κ`.  The second conjunct is `℩-spec`
-- and nothing else: no hypothesis, no model record, no ordinal fact.
power→subsets : (κ δ : S) → PowerAt κ δ → SubsetsAt κ δ
power→subsets κ δ =
  PT.map (λ { (F , code) → powL κ , F , code , powL-sub κ })

-- THE OTHER DIRECTION.  `[LJ-1.546]`'s `code-target-mono` is IMPORTED
-- and not rebuilt: enlarging the target costs one composition, and
-- `powL κ` is the largest target the second conjunct allows.
subsets→power : (κ δ : S) → SubsetsAt κ δ → PowerAt κ δ
subsets→power κ δ =
  PT.map (λ { (b , F , code , sub) →
    F , P546.code-target-mono F δ b (powL κ) code
          (λ y m → powL-in κ y (sub y m)) })

-- AND `PowerAt` IS B10's CONCLUSION, at any model record at all.
power→B10 : (zf : ModelL.isZFModel) (κ δ : S)
          → PowerAt κ δ → InjL δ (ModelL.isZFModel.𝒫 zf κ)
power→B10 zf κ δ = subst (InjL δ) (powL-is-𝒫 zf κ)

B10→power : (zf : ModelL.isZFModel) (κ δ : S)
          → InjL δ (ModelL.isZFModel.𝒫 zf κ) → PowerAt κ δ
B10→power zf κ δ = subst (InjL δ) (sym (powL-is-𝒫 zf κ))

-- =====================================================================
-- SECTION 3.  W3.  THE FORMULA THAT CARVES THE TABLE.
--
--   WRITTEN FIRST AND TYPECHECKED ALONE, at
--   agents/tasks/LJ-1-549/runs/W3.agda (runs w3-1.out to w3-3.out,
--   exit 0).  This is that slice, verbatim but for the body being
--   named apart so section 4 can read it back.
--
--   ARITY 1.  Its one free variable is the separation variable `z`,
--   the candidate member of the bound.  Under the two binders:
--
--       var 2  =  z, the candidate pair       (the separation slot)
--       var 1  =  x, the argument             (bound, outer ∃)
--       var 0  =  y, the value                (bound, inner ∃)
--
--   FOUR CONJUNCTS.  THREE ARE WRITTEN HERE.
--
--     1.  z is the ordered pair of x and y.          `prAtL`
--     2.  x is a member of δ.                        `∈̇ con δ`
--     3.  y is a member of the power set of κ, which
--         by `℩-spec` IS `y ⊆ˢ κ`.                   `∈̇ con (powL κ)`
--     4.  y is THE value at x.                       `Link`
--
--   CONJUNCT 4 HAS NO PRODUCER IN THIS TREE, so it enters as a
--   PARAMETER.  Section 4 measures exactly what a producer would buy.
-- =====================================================================

TableBody : (δ κ : S) → Formula S 3 → Formula S 3
TableBody δ κ Link =
  prAtL (s2 zero) (suc zero) zero
  ∧̇ ( (var (suc zero) ∈̇ con δ)
    ∧̇ ( (var zero ∈̇ con (powL κ)) ∧̇ Link ) )

TableFo : (δ κ : S) → Formula S 3 → Formula S 1
TableFo δ κ Link = ∃̇ (∃̇ (TableBody δ κ Link))

-- =====================================================================
-- SECTION 4.  THE CARVE, GENERIC IN THE LINK.
--
--   THIS IS THE MEASUREMENT THE BRIEF ASKED FOR.  `approx-carve`'s
--   method (agents/tasks/LJ-1-537/Probe537.agda:119-212) is: a bound
--   from `smallDom` over the members of the domain, a `Formula S 1`,
--   `hasSeparationL`, and the two membership readings.  Below, that
--   method is run at THIS table, with every input supplied except two.
--
--   THE TWO IT CANNOT SUPPLY, and they are the module's parameters:
--
--     `s`     the ambient assignment of a subset of κ to each member
--             of δ, injective.  This is exactly `[LJ-1.414]`'s HALF A
--             at this site (agents/tasks/LJ-1-414/Probe414.agda:65-66).
--     `Link`  the object-language description of that assignment, with
--             its two readings.
--
--   EVERYTHING ELSE IS BUILT HERE.  So the residue of the whole leg is
--   the pair (s , Link) and nothing else.
--
--   `SuccCardL` IS NOT A PARAMETER OF THIS MODULE, and no term in this
--   file takes it.  The leastness clause is therefore spent nowhere in
--   the reduction; it can only be spent inside `s`.
-- =====================================================================

ixOf : (δ x : S) → ⟨ fst x ∈ fst δ ⟩ → ⟪ fst δ ⟫
ixOf δ x m = fiber (fst δ) m .fst

ixOf-val : (δ x : S) (m : ⟨ fst x ∈ fst δ ⟩) → ⟪ fst δ ⟫↪ (ixOf δ x m) ≡ fst x
ixOf-val δ x m = fiber (fst δ) m .snd

module Table (δ κ : S)
  (s : ⟪ fst δ ⟫ → S)
  (s-sub : (k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
  (s-inj : (k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k')
  (Link : Formula S 3)
  (link-in : (x y z : S) (m : ⟨ fst x ∈ fst δ ⟩)
           → fst y ≡ fst (s (ixOf δ x m))
           → ⟨ (y ∷ x ∷ z ∷ []) ⊨ Link ⟩)
  (link-out : (x y z : S) → ⟨ (y ∷ x ∷ z ∷ []) ⊨ Link ⟩
            → (m : ⟨ fst x ∈ fst δ ⟩) → fst y ≡ fst (s (ixOf δ x m)))
  where

  -- a member of δ, as an element of the model
  memD : ⟪ fst δ ⟫ → S
  memD k = ⟪ fst δ ⟫↪ k
         , isL-trans {x = fst δ} {y = ⟪ fst δ ⟫↪ k} (member (fst δ) k) (snd δ)

  -- THE BOUND.  `smallDom` (src/L/Recursion.lagda.md:133) confines a
  -- SMALL family of L-elements in one stage, and the pairs of the
  -- table are indexed by `⟪ fst δ ⟫`, which is small.  This input the
  -- method DOES supply, and it supplies it from `s` alone.
  bnd : Σ[ d ∈ S ] ((k : ⟪ fst δ ⟫) → ⟨ prʟ (memD k) (s k) ∈ˢ d ⟩)
  bnd = smallDom ⟪ fst δ ⟫ (λ k → prʟ (memD k) (s k))

  D : S
  D = bnd .fst

  Cond : Formula S 1
  Cond = TableFo δ κ Link

  Body : Formula S 3
  Body = TableBody δ κ Link

  opaque
    G : S
    G = hasSeparationL D Cond .fst .fst

    G-mem : (z : S) → (z ∈ˢ G) ≡ ((z ∈ˢ D) ⊓ ((z ∷ []) ⊨ Cond))
    G-mem = hasSeparationL D Cond .fst .snd

  private
    inD : (x : S) (m : ⟨ fst x ∈ fst δ ⟩)
        → ⟨ pr (fst x) (fst (s (ixOf δ x m))) ∈ fst D ⟩
    inD x m =
      subst (λ t → ⟨ t ∈ fst D ⟩)
        (prʟ-fst (memD k) (s k) ∙ cong₂ pr (ixOf-val δ x m) refl)
        (bnd .snd k)
      where
      k : ⟪ fst δ ⟫
      k = ixOf δ x m

  graph-in : (x : S) (m : ⟨ fst x ∈ fst δ ⟩)
           → ⟨ pr (fst x) (fst (s (ixOf δ x m))) ∈ fst G ⟩
  graph-in x m =
    subst (λ t → ⟨ t ∈ fst G ⟩) qz
      (subst ⟨_⟩ (sym (G-mem (prʟ x y)))
        ( subst (λ t → ⟨ t ∈ fst D ⟩) (sym qz) (inD x m)
        , ∣ x , ∣ y , (hpr , (m , (hy , link-in x y (prʟ x y) m refl))) ∣₁ ∣₁ ))
    where
    y : S
    y = s (ixOf δ x m)

    qz : fst (prʟ x y) ≡ pr (fst x) (fst y)
    qz = prʟ-fst x y

    hpr : ⟨ (y ∷ x ∷ prʟ x y ∷ []) ⊨ prAtL (s2 zero) (suc zero) zero ⟩
    hpr = subst ⟨_⟩
      (sym (prAtL-adequate (s2 zero) (suc zero) zero (y ∷ x ∷ prʟ x y ∷ []))) qz

    hy : ⟨ fst y ∈ fst (powL κ) ⟩
    hy = powL-in κ y (s-sub (ixOf δ x m))

  private
    -- the two binders, unpacked at a proposition-valued goal
    rec2 : (x y : S) {P : Type (ℓ-suc ℓ)} → isProp P
         → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
         → ((u v : S) → ⟨ (v ∷ u ∷ prʟ x y ∷ []) ⊨ Body ⟩ → P) → P
    rec2 x y pP h g =
      PT.rec pP (λ { (u , hu) → PT.rec pP (λ { (v , hv) → g u v hv }) hu }) cnd
      where
      cnd : ⟨ (prʟ x y ∷ []) ⊨ Cond ⟩
      cnd = subst ⟨_⟩ (G-mem (prʟ x y))
              (subst (λ t → ⟨ t ∈ fst G ⟩) (sym (prʟ-fst x y)) h) .snd

    split : (x y u v : S) → ⟨ (v ∷ u ∷ prʟ x y ∷ []) ⊨ Body ⟩
          → (fst x ≡ fst u) × (fst y ≡ fst v)
    split x y u v (hpr , _) = pr-inj
      ( sym (prʟ-fst x y)
      ∙ subst ⟨_⟩
          (prAtL-adequate (s2 zero) (suc zero) zero (v ∷ u ∷ prʟ x y ∷ [])) hpr )

  graph-mem : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
            → ⟨ fst x ∈ fst δ ⟩ × ⟨ fst y ∈ fst (powL κ) ⟩
  graph-mem x y h = rec2 x y
    (isProp× (snd (fst x ∈ fst δ)) (snd (fst y ∈ fst (powL κ)))) h go
    where
    go : (u v : S) → ⟨ (v ∷ u ∷ prʟ x y ∷ []) ⊨ Body ⟩
       → ⟨ fst x ∈ fst δ ⟩ × ⟨ fst y ∈ fst (powL κ) ⟩
    go u v hv@(_ , (hu∈δ , (hv∈pow , _))) =
        subst (λ t → ⟨ t ∈ fst δ ⟩) (sym (split x y u v hv .fst)) hu∈δ
      , subst (λ t → ⟨ t ∈ fst (powL κ) ⟩) (sym (split x y u v hv .snd)) hv∈pow

  graph-val : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
            → (m : ⟨ fst x ∈ fst δ ⟩) → fst y ≡ fst (s (ixOf δ x m))
  graph-val x y h m = rec2 x y (setIsSet (fst y) (fst (s (ixOf δ x m)))) h go
    where
    go : (u v : S) → ⟨ (v ∷ u ∷ prʟ x y ∷ []) ⊨ Body ⟩
       → fst y ≡ fst (s (ixOf δ x m))
    go u v hv@(_ , (hu∈δ , (_ , hlink))) =
        split x y u v hv .snd
      ∙ link-out u v (prʟ x y) hlink hu∈δ
      ∙ cong (λ t → fst (s t)) (sym ik)
      where
      ik : ixOf δ x m ≡ ixOf δ u hu∈δ
      ik = ↪-inj {a = fst δ}
        ( ixOf-val δ x m ∙ split x y u v hv .fst ∙ sym (ixOf-val δ u hu∈δ) )

  -- ==================================================================
  -- THE FOUR CONJUNCTS.  `[LJ-1.414]`'s HALF B, rebuilt here rather
  -- than imported, because `agents/tasks/LJ-1-414/Probe414.agda:139`
  -- carries a hole by design and a file with a hole cannot be a
  -- dependency of a green probe.
  -- ==================================================================

  private
    γG : S ^ 2
    γG = G ∷ δ ∷ []

  sv : ⟨ γG ⊨ svAt zero ⟩
  sv = svAt-in zero γG go
    where
    go : (x y y' : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
       → ⟨ pr (fst x) (fst y') ∈ fst G ⟩ → fst y ≡ fst y'
    go x y y' p q = graph-val x y p m ∙ sym (graph-val x y' q m)
      where
      m : ⟨ fst x ∈ fst δ ⟩
      m = fst (graph-mem x y p)

  ij : ⟨ γG ⊨ injAt zero ⟩
  ij = injAt-in zero γG go
    where
    go : (y x x' : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
       → ⟨ pr (fst x') (fst y) ∈ fst G ⟩ → fst x ≡ fst x'
    go y x x' p q =
        sym (ixOf-val δ x m)
      ∙ cong ⟪ fst δ ⟫↪ (s-inj (ixOf δ x m) (ixOf δ x' m')
          (sym (graph-val x y p m) ∙ graph-val x' y q m'))
      ∙ ixOf-val δ x' m'
      where
      m : ⟨ fst x ∈ fst δ ⟩
      m = fst (graph-mem x y p)
      m' : ⟨ fst x' ∈ fst δ ⟩
      m' = fst (graph-mem x' y q)

  dm : ⟨ γG ⊨ domAt zero (suc zero) ⟩
  dm = domAt-intro zero (suc zero) γG (λ x → fwd x , bwd x)
    where
    fwd : (x : S) → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst G) ⟩
        → ⟨ fst x ∈ fst δ ⟩
    fwd x = PT.rec (snd (fst x ∈ fst δ))
      (λ { (y , p) → fst (graph-mem x y p) })

    bwd : (x : S) → ⟨ fst x ∈ fst δ ⟩
        → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst G) ⟩
    bwd x m = ∣ s (ixOf δ x m) , graph-in x m ∣₁

  ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩ → ⟨ fst y ∈ fst (powL κ) ⟩
  ran x y h = snd (graph-mem x y h)

  coded : InjCode G δ (powL κ)
  coded = sv , (dm , (ij , ran))

-- THE REDUCTION, AT THE TOP LEVEL.  The assignment and its link buy
-- the whole statement at that pair, with `SuccCardL` never mentioned.
link-suffices :
    (δ κ : S)
    (s : ⟪ fst δ ⟫ → S)
  → ((k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
  → ((k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k')
  → (Link : Formula S 3)
  → ((x y z : S) (m : ⟨ fst x ∈ fst δ ⟩) → fst y ≡ fst (s (ixOf δ x m))
     → ⟨ (y ∷ x ∷ z ∷ []) ⊨ Link ⟩)
  → ((x y z : S) → ⟨ (y ∷ x ∷ z ∷ []) ⊨ Link ⟩
     → (m : ⟨ fst x ∈ fst δ ⟩) → fst y ≡ fst (s (ixOf δ x m)))
  → SubsetsAt κ δ
link-suffices δ κ s s-sub s-inj Link link-in link-out =
  power→subsets κ δ ∣ T.G , T.coded ∣₁
  where
  module T = Table δ κ s s-sub s-inj Link link-in link-out

-- =====================================================================
-- SECTION 5.  THE ONE DELIVERED CODE PRODUCER IS REFUTED AT THIS
--             SOURCE, AND SO IS THE CHEAPEST `b`.
--
--   `[LJ-1.546]`'s sweep counted the sites in `src/` that DELIVER an
--   inhabited `InjCode`: two, both `shift-coded`, both at the pair
--   (sucʟ γ , γ) (agents/tasks/LJ-1-546/lj-1.546-report.md, section
--   `## THE SWEEP`).  `[LJ-1.546]`'s `code-source-determined`
--   (Probe546.agda:127-133) says a table has ONE source.  So the only
--   way the delivered producer could reach this obligation is for δ to
--   BE an ordinal successor.
--
--   IT IS NOT, and the refutation is the producer itself: if δ were
--   `sucʟ γ`, `shift-coded` would code δ into a member of δ, which
--   `IsCardinalL δ` forbids.
-- =====================================================================

-- A cardinal admits no code into any of its own members, so no target
-- below δ is admissible, whatever its members are.
target-not-below :
    (δ b F : S) → IsCardinalL δ → ⟨ fst b ∈ fst δ ⟩ → InjCode F δ b → Empty.⊥
target-not-below δ b F cd m code = cd b m ∣ F , code ∣₁

-- δ IS NOT AN ORDINAL SUCCESSOR.
no-ordinal-successor :
    (δ γ : S) → IsCardinalL δ
  → IsOrd (fst γ) → (⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
  → ((k : ℕ) → ⟨ # k ∈ fst γ ⟩)
  → fst δ ≡ fst (sucʟ γ) → Empty.⊥
no-ordinal-successor δ γ cd oγ γ∉ω num e =
  PT.rec Empty.isProp⊥
    (λ { (F , code) →
          cd γ γ∈δ ∣ F , subst (λ a → InjCode F a γ) (sym eS) code ∣₁ })
    (shift-coded γ oγ γ∉ω num)
  where
  eS : δ ≡ sucʟ γ
  eS = Σ≡Prop (λ x → snd (isL x)) e

  γ∈δ : ⟨ fst γ ∈ fst δ ⟩
  γ∈δ = subst (λ t → ⟨ fst γ ∈ t ⟩) (sym (e ∙ sucʟ-fst γ)) (self∈sucV (fst γ))

-- THE CHEAPEST CANDIDATE `b` PASSES THE SECOND CONJUNCT.  Every member
-- of κ⁺¹ is a subset of κ: a member of κ by ordinal transitivity, and
-- κ itself trivially.  So `sucʟ κ` is a real candidate and not a
-- category error.
succ-kappa-subsets :
    (κ : S) → IsOrd (fst κ)
  → (y : S) → ⟨ fst y ∈ fst (sucʟ κ) ⟩ → ⟨ y ⊆ˢ κ ⟩
succ-kappa-subsets κ oκ y m =
  ∈sucV-elim {A = fst κ} {x = fst y} (snd (y ⊆ˢ κ))
    (subst (λ t → ⟨ fst y ∈ t ⟩) (sucʟ-fst κ) m)
    (λ y∈κ x xm → fst oκ xm y∈κ)
    (λ y≡κ x xm → subst (λ t → ⟨ fst x ∈ t ⟩) y≡κ xm)

-- AND IT IS A MEMBER OF δ.  Trichotomy, with the successor case shut
-- by `no-ordinal-successor` and the descending case by irreflexivity.
succ-kappa-in :
    (δ κ : S) → IsOrd (fst δ) → IsOrd (fst κ) → IsCardinalL δ
  → ⟨ fst κ ∈ fst δ ⟩
  → (⟨ fst κ ∈ fst ωʟ ⟩ → Empty.⊥) → ((k : ℕ) → ⟨ # k ∈ fst κ ⟩)
  → ⟨ fst (sucʟ κ) ∈ fst δ ⟩
succ-kappa-in δ κ oδ oκ cd κ∈δ κ∉ω num =
  go (ord-tri (sucV (fst κ)) (suc-ord oκ) (fst δ) oδ)
  where
  back : ⟨ sucV (fst κ) ∈ fst δ ⟩ → ⟨ fst (sucʟ κ) ∈ fst δ ⟩
  back h = subst (λ t → ⟨ t ∈ fst δ ⟩) (sym (sucʟ-fst κ)) h

  down : ⟨ fst δ ∈ sucV (fst κ) ⟩ → ⟨ fst (sucʟ κ) ∈ fst δ ⟩
  down h = ∈sucV-elim {A = fst κ} {x = fst δ} (snd (fst (sucʟ κ) ∈ fst δ)) h
    (λ δ∈κ → Empty.rec (∈-irrefl (fst κ) (fst oκ κ∈δ δ∈κ)))
    (λ δ≡κ → Empty.rec (∈-irrefl (fst κ) (subst (λ t → ⟨ fst κ ∈ t ⟩) δ≡κ κ∈δ)))

  go : (⟨ sucV (fst κ) ∈ fst δ ⟩
       ⊎ ((sucV (fst κ) ≡ fst δ) ⊎ ⟨ fst δ ∈ sucV (fst κ) ⟩))
     → ⟨ fst (sucʟ κ) ∈ fst δ ⟩
  go (inl h) = back h
  go (inr (inl e)) =
    Empty.rec (no-ordinal-successor δ κ cd oκ κ∉ω num (sym e ∙ sym (sucʟ-fst κ)))
  go (inr (inr h)) = down h

-- SO THE CHEAPEST `b` IS REFUTED OUTRIGHT, at a cardinal successor of
-- an infinite κ.  It is not that nobody found a code into κ⁺¹: there
-- is none.
succ-kappa-excluded :
    (δ κ F : S) → IsOrd (fst δ) → IsOrd (fst κ) → IsCardinalL δ
  → ⟨ fst κ ∈ fst δ ⟩
  → (⟨ fst κ ∈ fst ωʟ ⟩ → Empty.⊥) → ((k : ℕ) → ⟨ # k ∈ fst κ ⟩)
  → InjCode F δ (sucʟ κ) → Empty.⊥
succ-kappa-excluded δ κ F oδ oκ cd κ∈δ κ∉ω num code =
  target-not-below δ (sucʟ κ) F cd
    (succ-kappa-in δ κ oδ oκ cd κ∈δ κ∉ω num) code

-- =====================================================================
-- SECTION 6.  HALF A, READ AT ITS OWN SIZE.
--
--   Section 4 takes the assignment `s` as three hypotheses.  This
--   section measures what those three hypotheses ARE, and the answer
--   is: an ambient injection of δ into the power set of κ, no more and
--   no less.  Both directions, so the reading is exact.
--
--   SO HALF A AT THIS SITE IS THE AMBIENT STATEMENT `κ⁺ ≤ 2^κ`.  It is
--   not a coding fact, it is not a formula question, and no chapter of
--   `src/` delivers it: `[LJ-1.535]` closed the counting-site route
--   (agents/tasks/LJ-1-535/lj-1.535-report.md:1) and the bounded-subset
--   theorem (src/L/BoundedSubset.lagda.md:1621) is the OTHER leg.
-- =====================================================================

assignment→ambient :
    (δ κ : S) (s : ⟪ fst δ ⟫ → S)
  → ((k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
  → ((k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k')
  → ⟪ fst δ ⟫ ↪ ⟪ fst (powL κ) ⟫
assignment→ambient δ κ s s-sub s-inj = f , finj
  where
  f : ⟪ fst δ ⟫ → ⟪ fst (powL κ) ⟫
  f k = fiber (fst (powL κ)) (powL-in κ (s k) (s-sub k)) .fst

  fval : (k : ⟪ fst δ ⟫) → ⟪ fst (powL κ) ⟫↪ (f k) ≡ fst (s k)
  fval k = fiber (fst (powL κ)) (powL-in κ (s k) (s-sub k)) .snd

  finj : (k k' : ⟪ fst δ ⟫) → f k ≡ f k' → k ≡ k'
  finj k k' e =
    s-inj k k' (sym (fval k) ∙ cong (⟪ fst (powL κ) ⟫↪) e ∙ fval k')

ambient→assignment :
    (δ κ : S) → ⟪ fst δ ⟫ ↪ ⟪ fst (powL κ) ⟫
  → Σ[ s ∈ (⟪ fst δ ⟫ → S) ]
      ( ((k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
      × ((k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k') )
ambient→assignment δ κ (f , finj) = s , (sub , inj)
  where
  P : V ℓ
  P = fst (powL κ)

  s : ⟪ fst δ ⟫ → S
  s k = ⟪ P ⟫↪ (f k)
      , isL-trans {x = P} {y = ⟪ P ⟫↪ (f k)} (member P (f k)) (snd (powL κ))

  sub : (k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩
  sub k = powL-sub κ (s k) (member P (f k))

  inj : (k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k'
  inj k k' e = finj k k' (↪-inj {a = P} e)

-- =====================================================================
-- SECTION 7.  THE SWEEP (C-42), MY OWN, AND IT CORRECTS A COUNT.
--
--   `[LJ-1.546]` counted the producers of an inhabited `InjCode` in
--   `src/` by the NAME `InjCode` and found two, both `shift-coded`.
--   THE COUNT BY NAME MISSES TWO MORE, because `L.InjChain` delivers
--   the FOUR CONJUNCTS without ever writing the type's name:
--
--     `L.InjChain.Carve`      src/L/InjChain.lagda.md:468.
--       sv :518, ij :525, dm :532, ran :544.  Opened publicly by
--       `InclGraph` (:575-598) and `OrdIncl` (:604-607).
--       THE PAIR: (D , C) for any D whose members are members of C.
--     `L.InjChain.Comp`       src/L/InjChain.lagda.md:314.
--       svK :380, ijK :391, dmK :402, ranK :420.
--       THE PAIR: (D , C), from two codes at (D , E) and (E , C).
--
--   SO THERE ARE THREE PRODUCER SHAPES AND NOT ONE: the shift, the
--   INCLUSION, and COMPOSITION.  The correction matters because a
--   sweep by name reads as "one shape, refuted" when in fact two more
--   shapes have to be refuted, and one of them is not obviously wrong
--   at this pair: an inclusion needs no ambient function at all.
--
--   BOTH ARE REFUTED HERE.
--
--     THE SHIFT: section 5.  δ is not an ordinal successor.
--     THE INCLUSION: below.  δ is NOT a subset of the power set of κ,
--       and the witness is `sucʟ κ`, which is a member of δ and is not
--       a subset of κ.
--     COMPOSITION: it produces nothing on its own.  It takes TWO codes
--       and no delivered code has δ as its source, which is
--       `[LJ-1.546]`'s `code-source-determined` (Probe546.agda:127-133).
-- =====================================================================

inclusion-fails :
    (δ κ : S) → IsOrd (fst δ) → IsOrd (fst κ) → IsCardinalL δ
  → ⟨ fst κ ∈ fst δ ⟩
  → (⟨ fst κ ∈ fst ωʟ ⟩ → Empty.⊥) → ((k : ℕ) → ⟨ # k ∈ fst κ ⟩)
  → ((z : V ℓ) → ⟨ z ∈ fst δ ⟩ → ⟨ z ∈ fst (powL κ) ⟩) → Empty.⊥
inclusion-fails δ κ oδ oκ cd κ∈δ κ∉ω num sub =
  ∈-irrefl (fst κ) (sucκ⊆κ κ κ∈sucκ)
  where
  κ∈sucκ : ⟨ fst κ ∈ fst (sucʟ κ) ⟩
  κ∈sucκ = subst (λ t → ⟨ fst κ ∈ t ⟩) (sym (sucʟ-fst κ)) (self∈sucV (fst κ))

  sucκ⊆κ : ⟨ sucʟ κ ⊆ˢ κ ⟩
  sucκ⊆κ = powL-sub κ (sucʟ κ)
    (sub (fst (sucʟ κ)) (succ-kappa-in δ κ oδ oκ cd κ∈δ κ∉ω num))

-- =====================================================================
-- SECTION 8.  THE RESIDUE, IN ONE TYPE.
--
--   Everything above collapses to this.  `SuccIntoSubsets` at (κ , δ)
--   is bought by `Residue δ κ` and by nothing weaker that this task
--   found: section 4 spends it and section 6 says its first component
--   is the ambient statement `κ⁺ ≤ 2^κ`.
--
--   NOTHING IN THIS FILE INHABITS `Residue`.  NOTHING IN `src/` DOES.
--   That is the stop, and `review-of-succ-into-subsets.md` states it.
--
--   `SuccCardL` IS ABSENT FROM `Residue`, and from every term of this
--   file.  The leastness clause is therefore not consumed anywhere in
--   the reduction: it can only be spent proving `Residue` itself, and
--   the place it is needed is the first component, where each member
--   of δ must be shown to inject into κ.
-- =====================================================================

Residue : (δ κ : S) → Type (ℓ-suc ℓ)
Residue δ κ =
  Σ[ s ∈ (⟪ fst δ ⟫ → S) ]
    ( ((k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
    × ( ((k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k')
      × (Σ[ Link ∈ Formula S 3 ]
           ( ((x y z : S) (m : ⟨ fst x ∈ fst δ ⟩) → fst y ≡ fst (s (ixOf δ x m))
              → ⟨ (y ∷ x ∷ z ∷ []) ⊨ Link ⟩)
           × ((x y z : S) → ⟨ (y ∷ x ∷ z ∷ []) ⊨ Link ⟩
              → (m : ⟨ fst x ∈ fst δ ⟩) → fst y ≡ fst (s (ixOf δ x m))) )) ) )

residue-suffices : (δ κ : S) → Residue δ κ → SubsetsAt κ δ
residue-suffices δ κ (s , (s-sub , (s-inj , (Link , (lin , lout))))) =
  link-suffices δ κ s s-sub s-inj Link lin lout

-- AND IT SUFFICES FOR B10 OUTRIGHT, which is what `[LJ-1.546]` proved
-- the named fact would do.  Two dispatches meet in this one line.
residue-pays-B10 :
    (zf : ModelL.isZFModel) (δ κ : S)
  → Residue δ κ → InjL δ (ModelL.isZFModel.𝒫 zf κ)
residue-pays-B10 zf δ κ r =
  power→B10 zf κ δ (subsets→power κ δ (residue-suffices δ κ r))

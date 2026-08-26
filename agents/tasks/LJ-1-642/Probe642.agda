{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.642]  CLAUSE (i) OF THE LEVEL-HOOD CERTIFICATE, AT THE ORDINAL
-- INDEX.  The mathematician's ruling (the brief's premise 2) restates
-- the clause so its index carries `IsOrd (fst (T.val c))` and not
-- `IsOrd (HS.C.π (fst (T.val c)))`, and the ruling removes the
-- `PreimageOrd` supplier outright.
--
-- W3 IS SECTION 1 and it was written FIRST and typechecked ALONE.  The
-- slice is agents/tasks/LJ-1-642/runs/W3.agda; its run is
-- runs/w3-1.out (exit 0, 2.50 s, peak 740,294,656 bytes).
--
-- THE FLOOR WAS MEASURED BEFORE ANY PROOF, as the standing coder clause
-- orders on a heavy object.  runs/FLOOR.agda states the obligation with
-- a HOLE in the trimmed frame: runs/floor-1.out, exit 42 at 2.40 s,
-- peak 693,862,400 bytes, `[UnsolvedInteractionMetas]` at the one
-- designed hole.  NO WALL was met anywhere in this task.
--
-- THE IMPORT SET IS src/ AND NOTHING ELSE.  Clause (i) is taken by
-- RESTATEMENT, text for text from agents/tasks/LJ-1-578/Probe578.agda
-- :234-240 with the index corrected, for the reason the brief gives as
-- premise 4 and [LJ-1.598] measured: the certificate's own statement
-- file walls under the wide cap with every dependency warm
-- (agents/tasks/LJ-1-598/runs/chain-578.out, exit 251 at 15.92 s).
-- [LJ-1.598]'s own probe is NOT imported either: its five names that
-- reappear here (`Det`, `Wit`, `inF`, the equation route and the body
-- identity) are restated at the corrected index and each cites the line
-- it comes from.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M4g" on this pane, the
-- HEAVY tier.  I did not set it.  One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-642.Probe642 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; var; _≐_; _∧̇_; ∃̇_; ⊥̇; ⊤̇ )
open import FOL.Manipulation.Parameters
  using ( countFo; constantsFo; absFo; ⊨-abs )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒟ₒ; 𝒟ₒ-intro; Lset-in )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Ordinal.Stages {ℓ} lem using ( rank-Lset )
open import L.Rank {ℓ} using ( rank-fix )
open import L.BoundedSubset {ℓ} lem using ( module HullStage )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( leastOf )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Vec using ( Vec; _∷_; [] )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

-- =====================================================================
-- THE FRAME.  One hull stage, [LJ-1.578] section 3's own six slots, as
-- [LJ-1.598] instantiated them (Probe598.agda:67-74).  Nothing from any
-- probe enters.
-- =====================================================================

module Frame (lam : SV.S) (ordλ : IsOrd lam)
             (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (X : SV.S)
             (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module T = HS.H.T

  -- ===================================================================
  -- SECTION 1.  W3.  THE TWO SUPPLIERS, TYPES ONLY.
  --
  --   The brief names the widest unmeasured term: `Det` and `Wit` at a
  --   general `ψ`.  Both are [LJ-1.598]'s types (Probe598.agda:209 and
  --   :213) at the index this brief RULES.  `Det` is unchanged there,
  --   because [LJ-1.598] already stated it at the index's own
  --   ordinal-hood; `Wit` likewise.  What the ruling changes is the
  --   CLAUSE they feed, in section 2.
  -- ===================================================================

  Det : Formula T.Code 2 → Type (ℓ-suc ℓ)
  Det ψ = (b a : HS.ASt.SL) → IsOrd (fst b)
        → ⟨ (b ∷ a ∷ []) T.⊨c ψ ⟩ → fst a ≡ Lset (fst b)

  Wit : Formula T.Code 2 → Type (ℓ-suc ℓ)
  Wit ψ = (b : HS.ASt.SL) → IsOrd (fst b)
        → ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (b ∷ a ∷ []) T.⊨c ψ ⟩ ∥₁

  -- AND `Det` ALONE IS FREE BY VACUITY, SO THE ANSWER TO "WHICH OF THE
  -- TWO DOES NOT FALL OUT" IS MACHINE-CHECKED RATHER THAN ARGUED.  An
  -- UNSATISFIABLE formula determines vacuously: satisfaction of `⊥̇` is
  -- the algebra's `⊥` (src/FOL/Semantics.lagda.md:99) and `⟨ ⊥ ⟩` is
  -- `⊥*` (src/Base/Truth.lagda.md:121).  This is the `Det` twin of
  -- [LJ-1.598]'s `only-level-vacuous` (Probe598.agda:104), and it says
  -- the same thing about the same site: NEITHER conjunct alone is the
  -- content.  So no brief may fund `Det` alone, and the residue this
  -- task reports is `Wit` UNDER a `Det`, which is the pair.
  det-vacuous : Det ⊥̇
  det-vacuous b a ob h = Empty.rec* h

  -- ===================================================================
  -- SECTION 2.  CLAUSE (i), RESTATED AT THE INDEX THE BRIEF RULES.
  --
  --   The text is [LJ-1.578]'s own (Probe578.agda:234-240) as
  --   [LJ-1.598] restated it (Probe598.agda:118-124), with ONE change
  --   and only one: the hypothesis is `IsOrd (fst (T.val c))`, the
  --   code's VALUE, where [LJ-1.598] had `IsOrd (HS.C.π (fst
  --   (T.val c)))`, the collapse of that value.  That is the brief's
  --   premise 2, and [LJ-1.598]'s D-10 section is why: at a NON-ordinal
  --   value the tree's own graph formula answers with a set that is not
  --   the level (lj-1.598-report.md, the `δ = {{∅}}` reading), so the
  --   old hypothesis admitted codes at which the clause is false.
  -- ===================================================================

  ClauseIAtOrd : Type (ℓ-suc ℓ)
  ClauseIAtOrd =
    (c : T.Code) → IsOrd (fst (T.val c))
    → Σ[ φ ∈ Formula T.Code 1 ]
        ( ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (a ∷ []) T.⊨c φ ⟩ ∥₁
        × ((a : HS.ASt.SL) → ⟨ (a ∷ []) T.⊨c φ ⟩
           → fst a ≡ Lset (fst (T.val c))) )

  BodyAtOrd : T.Code → Type (ℓ-suc ℓ)
  BodyAtOrd c =
    Σ[ φ ∈ Formula T.Code 1 ]
      ( ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (a ∷ []) T.⊨c φ ⟩ ∥₁
      × ((a : HS.ASt.SL) → ⟨ (a ∷ []) T.⊨c φ ⟩
         → fst a ≡ Lset (fst (T.val c))) )

  clause-i-from-body : ((c : T.Code) → IsOrd (fst (T.val c)) → BodyAtOrd c)
                     → ClauseIAtOrd
  clause-i-from-body f = f

  -- ===================================================================
  -- SECTION 3.  THE GRAPH ROUTE, AND WHAT THE RULING BUYS.
  --
  --   [LJ-1.598]'s `graph-gives-level` (Probe598.agda:220-239) already
  --   concluded at `IsOrd (fst (T.val c))`, the index's own
  --   ordinal-hood, and could not reach its own `ClauseI` from there:
  --   the composition needed `PreimageOrd` (Probe598.agda:257), the
  --   bridge from the collapse's ordinal-hood to the value's, which is
  --   built nowhere.  THE RULING DELETES THAT STEP.  Below, the graph
  --   route reaches the clause with NO third supplier, and the term
  --   that does it is the composition `clause-i-from-body ∘ ·`, one
  --   line.  That is exactly what the brief bought with premise 2.
  -- ===================================================================

  inF : (ψ : Formula T.Code 2) → T.Code → Formula T.Code 1
  inF ψ c = ∃̇ (ψ ∧̇ (var zero ≐ con c))

  graph-gives-body : (ψ : Formula T.Code 2) → Det ψ → Wit ψ
                   → (c : T.Code) → IsOrd (fst (T.val c)) → BodyAtOrd c
  graph-gives-body ψ det wit c oc = inF ψ c , sat , uniq
    where
    vc : SV.S
    vc = fst (T.val c)
    sat : ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (a ∷ []) T.⊨c inF ψ c ⟩ ∥₁
    sat = PT.map (λ { (a , hψ) → a , ∣ T.val c , (hψ , refl) ∣₁ })
            (wit (T.val c) oc)
    uniq : (a : HS.ASt.SL) → ⟨ (a ∷ []) T.⊨c inF ψ c ⟩
         → fst a ≡ Lset vc
    uniq a h = PT.rec (SV.isSetS (fst a) (Lset vc)) go h
      where
      go : Σ[ x ∈ HS.ASt.SL ]
             ⟨ (x ∷ a ∷ []) T.⊨c (ψ ∧̇ (var zero ≐ con c)) ⟩
           → fst a ≡ Lset vc
      go (x , hx) = det x a ox (hx .fst) ∙ cong Lset (hx .snd)
        where
        ox : IsOrd (fst x)
        ox = subst IsOrd (sym (hx .snd)) oc

  graph-gives-clause-i : (ψ : Formula T.Code 2) → Det ψ → Wit ψ → ClauseIAtOrd
  graph-gives-clause-i ψ det wit =
    clause-i-from-body (graph-gives-body ψ det wit)

  -- ===================================================================
  -- SECTION 4.  THE EQUATION ROUTE, AT THE SAME INDEX.
  --
  --   [LJ-1.598] section 3, restated at the ruled index
  --   (Probe598.agda:157-177).  If the hull NAMES the level at a code
  --   then an EQUATION is the formula clause (i) asks for and
  --   uniqueness is free, because equality at the restricted structure
  --   IS path equality on the projections
  --   (src/FOL/ZFStructure.lagda.md:148 against :82).
  -- ===================================================================

  eqF : (d : T.Code) → Formula T.Code 1
  eqF d = var zero ≐ con d

  eq-sat : (d : T.Code) → ⟨ (T.val d ∷ []) T.⊨c eqF d ⟩
  eq-sat d = refl

  eq-uniq : (d : T.Code) (a : HS.ASt.SL)
          → ⟨ (a ∷ []) T.⊨c eqF d ⟩ → fst a ≡ fst (T.val d)
  eq-uniq d a h = h

  CodedLevelsAtOrd : Type (ℓ-suc ℓ)
  CodedLevelsAtOrd = (c : T.Code) → IsOrd (fst (T.val c))
                   → Σ[ d ∈ T.Code ] (fst (T.val d) ≡ Lset (fst (T.val c)))

  coded-gives-clause-i : CodedLevelsAtOrd → ClauseIAtOrd
  coded-gives-clause-i cl = clause-i-from-body (λ c oc → go c (cl c oc))
    where
    go : (c : T.Code)
       → Σ[ d ∈ T.Code ] (fst (T.val d) ≡ Lset (fst (T.val c)))
       → BodyAtOrd c
    go c (d , e) = eqF d , ∣ T.val d , eq-sat d ∣₁ , λ a h → eq-uniq d a h ∙ e

  -- ===================================================================
  -- SECTION 5.  THE CONVERSE, WHICH IS NEW HERE.
  --
  --   [LJ-1.598] called the equation route CIRCULAR for the
  --   certificate and stopped there (Probe598.agda:148-154).  The
  --   circle is an EQUIVALENCE, and this section proves the half
  --   nobody had written: clause (i) at the ordinal index GIVES a code
  --   for the level, with no extra hypothesis at all.
  --
  --   The mechanism is the hull's own Skolem closure and nothing else.
  --   A formula over the hull's codes that is satisfied at the stage's
  --   inner world has its LEAST satisfier named by a code outright:
  --   `wit k (absFo φ) (constantsFo φ)` (src/L/Hull.lagda.md:72-76 for
  --   the constructor, :101-104 for `val-wit`), which is the
  --   construction inside `closed` (src/L/Hull.lagda.md:120-138) with
  --   the CODE kept instead of discarded.  No truncation survives,
  --   because the equation it must satisfy is a path in a set.
  --
  --   SO THE CERTIFICATE'S REMAINDER AT THE ORDINAL INDEX IS ONE
  --   STATEMENT AND NOT THREE.  `CodedLevelsAtOrd` and `ClauseIAtOrd`
  --   imply each other; `Det ψ × Wit ψ` implies both; and `Det` alone
  --   is vacuous (section 1).  What is owed is a `Wit` under a `Det`,
  --   equivalently a code for each level, and nothing else.
  -- ===================================================================

  skolem : (φ : Formula T.Code 1)
         → ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (a ∷ []) T.⊨c φ ⟩ ∥₁
         → (t : SV.S)
         → ((a : HS.ASt.SL) → ⟨ (a ∷ []) T.⊨c φ ⟩ → fst a ≡ t)
         → Σ[ d ∈ T.Code ] (fst (T.val d) ≡ t)
  skolem φ sat t u = T.wit k χ cs , cong fst (T.val-wit k χ cs w) ∙ u a sa
    where
    k : ℕ
    k = countFo φ
    χ : Formula (⊥* {ℓ}) (suc k)
    χ = absFo φ
    cs : Vec T.Code k
    cs = constantsFo φ
    w : T.Sat k χ (T.vals cs)
    w = PT.map
      (λ { (b , hb) →
             b , subst ⟨_⟩ (cong (λ vs → (b ∷ vs) T.⊨₀ χ) (sym (T.vals≡map cs)))
                   (subst ⟨_⟩ (⊨-abs (hPropAlgebra (ℓ-suc ℓ)) HS.ASt.AbsL.𝒮M
                                 T.val φ (b ∷ [])) hb) })
      sat
    a : HS.ASt.SL
    a = T.search k χ (T.vals cs) w
    pa : ⟨ (a ∷ T.vals cs) T.⊨₀ χ ⟩
    pa = leastOf HS.ASt.wL {ℓ'' = ℓ-suc ℓ} lem
           (λ z → (z ∷ T.vals cs) T.⊨₀ χ) w .snd .fst
    sa : ⟨ (a ∷ []) T.⊨c φ ⟩
    sa = subst ⟨_⟩ (sym (⊨-abs (hPropAlgebra (ℓ-suc ℓ)) HS.ASt.AbsL.𝒮M
                           T.val φ (a ∷ [])))
           (subst ⟨_⟩ (cong (λ vs → (a ∷ vs) T.⊨₀ χ) (T.vals≡map cs)) pa)

  clause-i-gives-coded : ClauseIAtOrd → CodedLevelsAtOrd
  clause-i-gives-coded cl c oc =
    skolem (cl c oc .fst) (cl c oc .snd .fst)
           (Lset (fst (T.val c))) (cl c oc .snd .snd)

  -- AND ONE COROLLARY THAT COSTS A LINE AND IS WORTH NAMING: clause (i)
  -- at the ordinal index proves, on its own, that the stage CONTAINS
  -- the levels it is about.  The existence conjunct hands a stage
  -- member and the uniqueness conjunct says which set that member is.
  -- This is `levelIn` (src/L/BoundedSubset.lagda.md:917) read at the
  -- STAGE instead of at the collapse, and it is a consequence here
  -- rather than a hypothesis.
  clause-i-gives-levelIn : ClauseIAtOrd → (c : T.Code)
                         → IsOrd (fst (T.val c))
                         → ⟨ Lset (fst (T.val c)) ∈ˢ Lset lam ⟩
  clause-i-gives-levelIn cl c oc =
    PT.rec (snd (Lset (fst (T.val c)) ∈ˢ Lset lam))
      (λ { (a , ha) → subst (λ z → ⟨ z ∈ˢ Lset lam ⟩)
                        (cl c oc .snd .snd a ha) (snd a) })
      (cl c oc .snd .fst)

  -- ===================================================================
  -- SECTION 6.  WHAT THE STAGE ALREADY HAS, AND WHAT IS LEFT.
  --
  --   `level-in-stage` is the half of the residue that the ruling makes
  --   PROVABLE, and it was a hypothesis before.  At an ORDINAL index of
  --   the stage the level is a MEMBER of the stage, outright, from the
  --   frame's own data and three delivered facts: an ordinal of a level
  --   is a member of that level's index (`rank-Lset` composed with
  --   `rank-fix`, src/L/Ordinal/Stages.lagda.md and src/L/Rank.lagda.md,
  --   the same composition `β-succ` uses at
  --   src/L/BoundedSubset.lagda.md:983-985), a set is a definable subset
  --   of itself (`defSet⊤≡A`, src/L/Definability.lagda.md:192-206), and
  --   a member of the step at an index below is a member of the stage
  --   (`Lset-in`, src/L/Constructible.lagda.md:329).
  --
  --   THIS IS `levelIn` READ AT THE STAGE.  `Condense` takes exactly
  --   this shape as a HYPOTHESIS at the COLLAPSE
  --   (src/L/BoundedSubset.lagda.md:917).  At the stage it is a
  --   theorem, and the ruling is what makes it one: the old hypothesis
  --   `IsOrd (HS.C.π ...)` gives no ordinal to feed `rank-fix`.
  --
  --   SO THE REMAINDER IS NOT ABOUT THE STAGE.  The level is in the
  --   stage; what is open is whether the HULL names it, and the hull
  --   names exactly what is definable in the stage from hull
  --   parameters.  That is `Wit` under a `Det`, equivalently
  --   `CodedLevelsAtOrd`, equivalently [LJ-1.610]'s `WitStage`
  --   (agents/tasks/LJ-1-610/Probe610.agda:235-238).
  -- ===================================================================

  self∈𝒟ₒ : (A : SV.S) → ⟨ A ∈ˢ 𝒟ₒ A ⟩
  self∈𝒟ₒ A = 𝒟ₒ-intro A A ∣ ⊤̇ , DefOf.defSet⊤≡A A ∣₁

  level-in-stage : (δ : SV.S) → IsOrd δ → ⟨ δ ∈ˢ Lset lam ⟩
                 → ⟨ Lset δ ∈ˢ Lset lam ⟩
  level-in-stage δ oδ δ∈Lλ =
    Lset-in lam δ (Lset δ) δ∈lam (self∈𝒟ₒ (Lset δ))
    where
    δ∈lam : ⟨ δ ∈ˢ lam ⟩
    δ∈lam = subst (λ w → ⟨ w ∈ˢ lam ⟩) (rank-fix δ oδ)
              (rank-Lset lam ordλ δ δ∈Lλ)

  level-of-code-in-stage : (c : T.Code) → IsOrd (fst (T.val c))
                         → ⟨ Lset (fst (T.val c)) ∈ˢ Lset lam ⟩
  level-of-code-in-stage c oc = level-in-stage (fst (T.val c)) oc (snd (T.val c))

  -- AND `Wit`'s OWN EXISTENTIAL IS FREE, WHICH SHARPENS WHERE THE WALL
  -- IS.  [LJ-1.610] WALL 1 says a witness read at the stage's inner
  -- world must be a MEMBER of the stage
  -- (agents/tasks/LJ-1-610/review-of-graph-stage.md).  For THIS `Wit`
  -- the witness is the tower's VALUE, and section 6 puts that value in
  -- the stage outright.  So `Wit` costs no witness at all: it costs a
  -- formula that HOLDS at the tower's own value, and nothing more.  The
  -- approximation [LJ-1.610] could not build enters only through the
  -- formula's OWN existential, when the formula chosen is the graph.
  Holds : Formula T.Code 2 → Type (ℓ-suc ℓ)
  Holds ψ = (b : HS.ASt.SL) (ob : IsOrd (fst b))
          → ⟨ (b ∷ (Lset (fst b) , level-in-stage (fst b) ob (snd b)) ∷ [])
              T.⊨c ψ ⟩

  wit-from-holds : (ψ : Formula T.Code 2) → Holds ψ → Wit ψ
  wit-from-holds ψ h b ob =
    ∣ (Lset (fst b) , level-in-stage (fst b) ob (snd b)) , h b ob ∣₁

  -- ===================================================================
  -- SECTION 7.  THE EQUIVALENCE, IN ONE NAME.  This is what the task
  -- earns: the certificate's clause (i) at the ruled index is not three
  -- open statements but ONE.
  -- ===================================================================

  clause-i-iff-coded : (ClauseIAtOrd → CodedLevelsAtOrd)
                     × (CodedLevelsAtOrd → ClauseIAtOrd)
  clause-i-iff-coded = clause-i-gives-coded , coded-gives-clause-i

  -- AND THE SAME ROUTE BUYS FACT A AT THE RULED INDEX.
  -- `Facts.HasLevels` (agents/tasks/LJ-1-578/Probe578.agda:120-122) is
  -- "the hull contains the level", and `cert-gives-A` (:254-273) is the
  -- certificate's own derivation of it, which needed the collapse
  -- index.  At the ruled index it is four lines and needs no bridge:
  -- the code's value IS a hull member (src/L/Hull.lagda.md:341-342).
  hull-has-levels : CodedLevelsAtOrd
                  → (c : T.Code) → IsOrd (fst (T.val c))
                  → ⟨ Lset (fst (T.val c)) ∈ˢ HS.M ⟩
  hull-has-levels cl c oc =
    subst (λ z → ⟨ z ∈ˢ HS.M ⟩) (cl c oc .snd)
      (HS.H.val-in-Hull (cl c oc .fst))

  clause-i-gives-hull-levels : ClauseIAtOrd
                             → (c : T.Code) → IsOrd (fst (T.val c))
                             → ⟨ Lset (fst (T.val c)) ∈ˢ HS.M ⟩
  clause-i-gives-hull-levels cl = hull-has-levels (clause-i-gives-coded cl)

  -- THE TRIANGLE CLOSES.  The graph route's two suppliers give a code
  -- for every level, through clause (i) and the hull's Skolem closure.
  graph-gives-coded : (ψ : Formula T.Code 2) → Det ψ → Wit ψ
                    → CodedLevelsAtOrd
  graph-gives-coded ψ det wit =
    clause-i-gives-coded (graph-gives-clause-i ψ det wit)

-- =====================================================================
-- THE OBLIGATION.  Clause (i) at the ordinal index, discharged from the
-- graph route and its two suppliers, exactly as the brief names it.
-- =====================================================================

clause-i-at-ord : (lam : SV.S) (ordλ : IsOrd lam)
  (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : SV.S)
  (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (ψ : Formula (Frame.T.Code lam ordλ succλ X X⊆Lλ ∅∈λ) 2)
  → Frame.Det lam ordλ succλ X X⊆Lλ ∅∈λ ψ
  → Frame.Wit lam ordλ succλ X X⊆Lλ ∅∈λ ψ
  → Frame.ClauseIAtOrd lam ordλ succλ X X⊆Lλ ∅∈λ
clause-i-at-ord lam ordλ succλ X X⊆Lλ ∅∈λ ψ det wit =
  Frame.graph-gives-clause-i lam ordλ succλ X X⊆Lλ ∅∈λ ψ det wit

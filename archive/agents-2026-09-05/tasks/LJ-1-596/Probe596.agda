{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.596]  B9 THROUGH THE INTERNALIZATION MACHINE, WHICH THE TREE
-- ALREADY HAS.
--
-- VERDICT: NO-GO.  The obligation `b9-inf` is NOT in this file, and
-- `agents/tasks/LJ-1-596/review-of-b9-inf.md` states why.  Everything
-- below is TRUE and GREEN: the machine's interface, re-ascribed; the
-- three mismatches between `step` and the machine's slot; and ONE
-- CONDITIONAL TERM that says exactly what the machine would pay if its
-- two missing inputs existed.  No hole, no postulate, `--safe` is on.
--
-- W3 IS `agents/tasks/LJ-1-596/runs/W3.agda`, written first and
-- typechecked alone (`runs/w3-11.out`, EXIT=0), and IMPORTED below so
-- the slice cannot drift.
--
-- CALIBER.  The program sets GHCRTS on this pane.  I do not set it.
-- One Agda process at a time.
--
--   Section 0.  D-10.  The chapter's interface: what it takes, what it
--                gives, at file:line.
--   Section 1.  THE CONDITION RE-ASCRIPTED.  The prose sentence tested
--                against the record's own fields.
--   Section 2.  DOES `step` FIT.  Three mismatches, each a row.
--   Section 3.  THE CONDITIONAL.  What the machine pays, at a GENERIC
--                carrier (clause W2), given its two missing inputs.
--   Section 4.  THE OBLIGATION, STATED AND NOT INHABITED.
--
-- IMPORTS ARE TRIMMED to the rows this file's own sections use
-- (dev/LESSONS.md, the floor law): nothing below reaches
-- `L.StageCardinal` except through W3, and nothing reaches the
-- `[LJ-1.56x]` probe chains at all.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import L.Constructible using ( IsOrd )

module LJ-1-596.Probe596 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst; svAt; svAt-in; domAt; domAt-intro )
open import L.Coding.Injection {ℓ} lem using ( injAt; injAt-in )
open import L.Cardinal {ℓ} lem using ( InjCode; _↪_; IsCardinalL )
open import L.StageBound {ℓ} lem using ( SqFam )
open import L.GCH {ℓ} lem using ( InjL )
import L.Recursion
import LJ-1-596.runs.W3

open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module Rec = L.Recursion {ℓ} lem
module W3 = LJ-1-596.runs.W3 {ℓ} lem α₀ oα₀

-- =====================================================================
-- SECTION 0.  D-10, BEFORE ANY AGDA, AND IT IS THE CHAPTER'S INTERFACE.
--
--   src/L/Recursion.lagda.md TAKES, in the `Recursion` record
--   (:103-108): a domain `dom : S` (:105), a two-variable formula
--   `graph : Formula S 2` (:106), and single-valuedness `funct`
--   (:107-108).  The `Definition` record (:272-279) takes instead a
--   TOTAL function `fn : S → S` (:275) plus the formula (:276) plus
--   the two adequacy fields `defines` (:277) and `only` (:278-279).
--   It GIVES `Of.table : S` (:179-180), the replacement image, with
--   its two membership directions `table-in` (:185-187) and
--   `table-out` (:189-190) and the value function `val`/`val-uniq`
--   (:192-197).  `smallDom` (:133-134) discharges the domain for any
--   small family of elements of L.  THE ENGINE IS `hasReplacementL`
--   (:361), and that is the whole chapter.
-- =====================================================================

-- WHAT IT TAKES, as one type.  The three fields of `Recursion`
-- (src/L/Recursion.lagda.md:105-108), unpacked.
Takes : Type (ℓ-suc ℓ)
Takes =
  Σ[ dom ∈ S ] Σ[ graph ∈ Formula S 2 ]
    ((x : S) → ⟨ fst x ∈ˢ fst dom ⟩
      → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ graph ⟩))

takes-is-the-record : Takes → Rec.Recursion
takes-is-the-record (dom , graph , funct) =
  record { dom = dom ; graph = graph ; funct = funct }

-- WHAT IT GIVES, from that input alone: the table and its membership
-- directions (src/L/Recursion.lagda.md:179-190).
gives-table : Takes → S
gives-table t = Rec.Of.table (takes-is-the-record t)

gives-in : (t : Takes) (x y : S) → ⟨ fst x ∈ˢ fst (t .fst) ⟩
         → ⟨ (y ∷ x ∷ []) ⊨ (t .snd .fst) ⟩
         → ⟨ fst y ∈ˢ fst (gives-table t) ⟩
gives-in t = Rec.Of.table-in (takes-is-the-record t)

-- =====================================================================
-- SECTION 1.  THE CONDITION RE-ASCRIPTED, AND THE PROSE TESTED.
--
--   The chapter's sentence (src/L/Recursion.lagda.md:259-262):
--   "A recursive definition is internalizable when its graph is
--   expressible, and nothing about the recursion's shape, its depth,
--   its order of descent, or the complexity of its clauses appears in
--   the condition."
--
--   THE TYPE SAYS LESS AND DEMANDS MORE.  "Expressible" is not a
--   syntactic property the type checks; the record demands a formula
--   AND the two adequacy implications `defines` and `only`
--   (src/L/Recursion.lagda.md:277-279), each of which is mathematics:
--   `defines` says the formula holds of the function's own value,
--   `only` says nothing else satisfies it.  The sentence is TRUE of
--   the type only if "the graph is expressible" is READ as "a formula
--   adequate in both directions exists".  The second half of the
--   sentence is TRUE as stated: no field of either record mentions the
--   recursion's shape, depth, order of descent or clause complexity.
-- =====================================================================

-- The condition the machine actually demands, as one type: the
-- `Definition` record's five fields (src/L/Recursion.lagda.md:272-279).
Condition : Type (ℓ-suc ℓ)
Condition =
  Σ[ dom ∈ S ] Σ[ fn ∈ (S → S) ] Σ[ graph ∈ Formula S 2 ]
    ( ((x : S) → ⟨ fst x ∈ˢ fst dom ⟩ → ⟨ (fn x ∷ x ∷ []) ⊨ graph ⟩)
    × ((x : S) → ⟨ fst x ∈ˢ fst dom ⟩ → (y : S)
        → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩ → y ≡ fn x) )

condition-is-the-record : Condition → Rec.Definition
condition-is-the-record (dom , fn , graph , (defines , only)) =
  record { dom = dom ; fn = fn ; graph = graph
         ; defines = defines ; only = only }

-- AND THE ENGINE IS REPLACEMENT, NOT A NEW INDUCTION PRINCIPLE.  The
-- chapter's own words (src/L/Recursion.lagda.md:361): "The chapter is
-- a wrapper around `hasReplacementL`".  `takes-is-the-record` and
-- `gives-table` above are the wrapper applied.
engine : (a : S) (φ : Formula S 2)
       → ((x : S) → ⟨ fst x ∈ˢ fst a ⟩
             → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ φ ⟩))
       → S
engine a φ funct = Rec.Of.table (record { dom = a ; graph = φ ; funct = funct })

-- =====================================================================
-- SECTION 2.  DOES `step` FIT.  Three mismatches, each a row.
-- =====================================================================

-- 2.1  THE VALUE IS FUNCTION-VALUED.  W3's `Tower` row, restated here
--      through the import so the probe and the slice cannot drift:
--      `P` (src/L/StageCardinal.lagda.md:530-532) concludes at an
--      injection between fibers, and the machine consumes S-valued
--      functions (`Definition.fn : S → S`,
--      src/L/Recursion.lagda.md:275).  The `refl` is W3's own row
--      (agents/tasks/LJ-1-596/runs/W3.agda, `P-is-function-valued`).
module AtSq (sqf : SqFam α₀) where

  open W3.Tower sqf public

-- 2.2  THE GRAPH'S TWO UNNAMABLE INGREDIENTS.  W3's `Ingredients`
--      (agents/tasks/LJ-1-596/runs/W3.agda, section 3): the class
--      predicate's existential ranges over a META syntax type
--      (src/L/StageCardinal.lagda.md:281-282), and the count `cnt`
--      (:288-289) is defined through `ih` (:283), which is the
--      recursion's own value at a member.  Both rows are imported.
  F-at : (α : V ℓ) (m : ⟪ α ⟫) → Type ℓ
  F-at α = W3.Ingredients.F-at α

  CntShape : (α : V ℓ) → Type ℓ
  CntShape α = W3.Ingredients.CntShape α

  ClassPredShape : (α : V ℓ) → Type (ℓ-suc (ℓ-suc ℓ))
  ClassPredShape α = W3.Ingredients.ClassPredShape α

-- 2.3  THE TREE'S STOCK OF TWO-VARIABLE GRAPHS, as terms.  `satGraph`
--      (src/L/Coding/Graph.lagda.md:238) is the satisfaction
--      recursion's graph, adequate by `L.Coding.Uniform`'s `exists` and
--      `unique`.  `LsetGraph` (src/L/Coding/Sequence.lagda.md:353) is
--      the tower's graph, adequate by `L.Hierarchy`'s `Lset-defines`
--      and `Lset-only`.  THESE ARE THE TREE'S TWO INTERNALIZED
--      RECURSIONS, and neither is the graph of an injection recursion:
--      each is the graph of a construction whose step reads its
--      argument through the satisfaction machinery alone.
--      THE ROWS ARE CITATIONS AND NOT IMPORTS: importing the two
--      chapters into this file's frame was measured at a 4 GB heap
--      wall (runs/p11.out), and an identity function adds nothing the
--      file:line citation does not already give.

-- =====================================================================
-- SECTION 3.  THE CONDITIONAL.  WHAT THE MACHINE PAYS, GIVEN ITS TWO
--   MISSING INPUTS, AT A GENERIC CARRIER (clause W2).
--
--   Input 1: an ambient injection `g` between the member types of two
--   L-elements.  Input 2: a total function that pair-codes `g` on the
--   domain, and a formula adequate to it in both directions.
--   Output: a CODE, the four conjuncts of `InjCode`
--   (src/L/Cardinal.lagda.md:223-228), from the machine's table.
--   THE MATHEMATICS IS WRITTEN ONCE HERE, at the generic pair, and the
--   instantiation at the bill's own pair is one substitution (3.4).
-- =====================================================================

module Machine (a b : S) (g : ⟪ fst a ⟫ ↪ ⟪ fst b ⟫) where

  gf : ⟪ fst a ⟫ → ⟪ fst b ⟫
  gf = fst g

  upb : ⟪ fst b ⟫ → S
  upb m = ⟪ fst b ⟫↪ m , isL-trans {x = fst b} (member (fst b) m) (snd b)

  -- THE TWO MISSING INPUTS, as one type.  A total S-valued function
  -- that pair-codes `g` on the domain (the record's `fn : S → S`,
  -- src/L/Recursion.lagda.md:275, total on the whole model because the
  -- record demands it), and a formula adequate to it in both
  -- directions (`defines` and `only`,
  -- src/L/Recursion.lagda.md:277-279).  [LJ-1.596]'s W3 slice shows
  -- the function half is constructible from LEM alone
  -- (agents/tasks/LJ-1-596/runs/W3.agda, `Elem.fn`); the formula half
  -- is the missing chapter.
  AdequateAt : (S → S) → Formula S 2 → Type (ℓ-suc ℓ)
  AdequateAt fn ψ =
      ((x : S) → ⟨ fst x ∈ˢ fst a ⟩ → ⟨ (fn x ∷ x ∷ []) ⊨ ψ ⟩)
    × ((x : S) → ⟨ fst x ∈ˢ fst a ⟩ → (y : S)
        → ⟨ (y ∷ x ∷ []) ⊨ ψ ⟩ → y ≡ fn x)

  Input : Type (ℓ-suc ℓ)
  Input =
    Σ[ fn ∈ (S → S) ] Σ[ ψ ∈ Formula S 2 ]
      ( ((x : S) → (x∈ : ⟨ fst x ∈ˢ fst a ⟩)
          → fn x ≡ prʟ x (upb (gf (fiber (fst a) x∈ .fst))))
      × AdequateAt fn ψ )

  -- THE FOUR CONJUNCTS, FACTORED OUT OF THE RECORD-CARRYING FRAME.
  --   A heap wall at 4 GB (runs/p11.out) measured the first shape;
  --   the split below holds nothing the conjuncts do not need.
  module Code (fn : S → S)
              (feq : (x : S) → (x∈ : ⟨ fst x ∈ˢ fst a ⟩)
                    → fn x ≡ prʟ x (upb (gf (fiber (fst a) x∈ .fst))))
              (F : S)
              (fin : (x : S) → (x∈ : ⟨ fst x ∈ˢ fst a ⟩)
                    → ⟨ fst (fn x) ∈ˢ fst F ⟩)
              (fout : (z : S) → ⟨ fst z ∈ˢ fst F ⟩
                    → ∥ (Σ[ x ∈ S ] (⟨ fst x ∈ˢ fst a ⟩
                          × (z ≡ fn x))) ∥₁) where

    out : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩
        → ∥ (Σ[ x₀ ∈ S ] (⟨ fst x₀ ∈ˢ fst a ⟩ × (prʟ x y ≡ fn x₀))) ∥₁
    out x y p = fout (prʟ x y)
      (subst (λ w → ⟨ w ∈ˢ fst F ⟩) (sym (prʟ-fst x y)) p)

    eq : (x y : S) (x₀ : S) (x₀∈ : ⟨ fst x₀ ∈ˢ fst a ⟩)
       → prʟ x y ≡ fn x₀
       → pr (fst x) (fst y) ≡ pr (fst x₀) (fst (upb (gf (fiber (fst a) x₀∈ .fst))))
    eq x y x₀ x₀∈ e =
      sym (prʟ-fst x y)
        ∙ cong fst (e ∙ feq x₀ x₀∈)
        ∙ prʟ-fst x₀ (upb (gf (fiber (fst a) x₀∈ .fst)))

    sv : ⟨ (F ∷ a ∷ []) ⊨ svAt zero ⟩
    sv = svAt-in zero (F ∷ a ∷ []) h
      where
      h : (x y y' : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩
        → ⟨ pr (fst x) (fst y') ∈ fst F ⟩ → fst y ≡ fst y'
      h x y y' p q =
        PT.rec2 (setIsSet (fst y) (fst y')) go (out x y p) (out x y' q)
        where
        go : (Σ[ x₀ ∈ S ] (⟨ fst x₀ ∈ˢ fst a ⟩ × (prʟ x y ≡ fn x₀)))
           → (Σ[ x₁ ∈ S ] (⟨ fst x₁ ∈ˢ fst a ⟩ × (prʟ x y' ≡ fn x₁)))
           → fst y ≡ fst y'
        go (x₀ , (x₀∈ , e₀)) (x₁ , (x₁∈ , e₁)) =
          let
            fj  = pr-inj (eq x y x₀ x₀∈ e₀)
            fj' = pr-inj (eq x y' x₁ x₁∈ e₁)
            -- the two fibers present the same member of a
            fib≡ : fiber (fst a) x₀∈ .fst ≡ fiber (fst a) x₁∈ .fst
            fib≡ = ↪-inj {a = fst a}
              (fiber (fst a) x₀∈ .snd
                ∙ (sym (fj .fst) ∙ fj' .fst)
                ∙ sym (fiber (fst a) x₁∈ .snd))
          in fj .snd ∙ cong (λ m → fst (upb m)) (cong gf fib≡) ∙ sym (fj' .snd)

    dm : ⟨ (F ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩
    dm = domAt-intro zero (suc zero) (F ∷ a ∷ []) h
      where
      h : (x : S)
        → (⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst F) ⟩ → ⟨ fst x ∈ fst a ⟩)
        × (⟨ fst x ∈ fst a ⟩ → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst F) ⟩)
      h x = fwd , bwd
        where
        fwd : ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst F) ⟩ → ⟨ fst x ∈ fst a ⟩
        fwd ex = PT.rec (snd (fst x ∈ fst a)) (λ { (y , p) →
          PT.rec (snd (fst x ∈ fst a)) (λ { (x₀ , (x₀∈ , e)) →
            subst (λ w → ⟨ w ∈ˢ fst a ⟩)
              (sym (pr-inj (eq x y x₀ x₀∈ e) .fst)) x₀∈ })
            (out x y p) }) ex
        bwd : ⟨ fst x ∈ fst a ⟩ → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst F) ⟩
        bwd x∈ =
          let
            v = gf (fiber (fst a) x∈ .fst)
          in ∣ upb v
               , subst (λ w → ⟨ w ∈ fst F ⟩)
                   (cong fst (feq x x∈) ∙ prʟ-fst x (upb v))
                   (fin x x∈) ∣₁

    ij : ⟨ (F ∷ a ∷ []) ⊨ injAt zero ⟩
    ij = injAt-in zero (F ∷ a ∷ []) h
      where
      h : (y x x' : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩
        → ⟨ pr (fst x') (fst y) ∈ fst F ⟩ → fst x ≡ fst x'
      h y x x' p q =
        PT.rec2 (setIsSet (fst x) (fst x')) go (out x y p) (out x' y q)
        where
        go : (Σ[ x₀ ∈ S ] (⟨ fst x₀ ∈ˢ fst a ⟩ × (prʟ x y ≡ fn x₀)))
           → (Σ[ x₁ ∈ S ] (⟨ fst x₁ ∈ˢ fst a ⟩ × (prʟ x' y ≡ fn x₁)))
           → fst x ≡ fst x'
        go (x₀ , (x₀∈ , e₀)) (x₁ , (x₁∈ , e₁)) =
          let
            fj  = pr-inj (eq x y x₀ x₀∈ e₀)
            fj' = pr-inj (eq x' y x₁ x₁∈ e₁)
            -- g is injective, so the two fibers agree, so the members do
            v≡ : gf (fiber (fst a) x₀∈ .fst) ≡ gf (fiber (fst a) x₁∈ .fst)
            v≡ = ↪-inj {a = fst b} (sym (fj .snd) ∙ fj' .snd)
            fib≡ : fiber (fst a) x₀∈ .fst ≡ fiber (fst a) x₁∈ .fst
            fib≡ = g .snd _ _ v≡
            mem≡ : fst x₀ ≡ fst x₁
            mem≡ = sym (fiber (fst a) x₀∈ .snd)
                     ∙ cong (⟪ fst a ⟫↪) fib≡
                     ∙ fiber (fst a) x₁∈ .snd
          in fj .fst ∙ mem≡ ∙ sym (fj' .fst)

    ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst b ⟩
    ran x y p =
      PT.rec (snd (fst y ∈ fst b)) (λ { (x₀ , (x₀∈ , e)) →
        subst (λ w → ⟨ w ∈ˢ fst b ⟩) (sym (pr-inj (eq x y x₀ x₀∈ e) .snd))
          (member (fst b) (gf (fiber (fst a) x₀∈ .fst))) })
        (out x y p)

    code : InjCode F a b
    code = sv , (dm , (ij , ran))

  -- WHAT THE MACHINE PAYS FROM ITS INPUT: the table is the code.
  pays-input : Input → InjL a b
  pays-input (fn , ψ , (feq , ad)) = ∣ F , Code.code fn feq F fin fout ∣₁
    where
      D : Rec.Definition
      D = record
        { dom     = a
        ; fn      = fn
        ; graph   = ψ
        ; defines = ad .fst
        ; only    = ad .snd }

      R : Rec.Recursion
      R = Rec.asRecursion D

      -- THE MACHINE'S ANSWER, `Of.table`
      -- (src/L/Recursion.lagda.md:179-180)
      F : S
      F = Rec.Of.table R

      fin : (x : S) → (x∈ : ⟨ fst x ∈ˢ fst a ⟩) → ⟨ fst (fn x) ∈ˢ fst F ⟩
      fin x x∈ = Rec.Of.table-in R x (fn x) x∈ (ad .fst x x∈)

      fout : (z : S) → ⟨ fst z ∈ˢ fst F ⟩
           → ∥ (Σ[ x ∈ S ] (⟨ fst x ∈ˢ fst a ⟩ × (z ≡ fn x))) ∥₁
      fout z z∈ =
        PT.map (λ { (x , (x∈ , h)) → x , (x∈ , ad .snd x x∈ z h) })
          (Rec.Of.table-out R z z∈)

-- 3.4  THE INSTANTIATION AT THE BILL'S OWN PAIR.
--   `ClauseTrophy` is copied letter for letter from
--   agents/tasks/LJ-1-593/Probe593.agda:68-69, which copies it from
--   src/L/GCH.lagda.md:64.
ClauseTrophy : S → Type (ℓ-suc ℓ)
ClauseTrophy κ = ⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥

-- b9inf-given-graph : THE CONDITIONAL AT THE BILL'S OWN PAIR.  One
--   substitution: the domain carrier is the stage, the codomain is
--   the cardinal itself, the ambient injection and the adequate
--   graph are the two missing inputs, and the three hypotheses of
--   `B9Inf` that the machine does not spend are carried unused, as
--   the obligation's own type carries them.
b9inf-given-graph :
    (δ Lδ : S) (ordδ : IsOrd (fst δ)) (cardδ : IsCardinalL δ)
    (δ∉ω : ClauseTrophy δ)
  → (fst Lδ ≡ Lset (fst δ))
  → (g : ⟪ Lset (fst δ) ⟫ ↪ ⟪ fst δ ⟫)
  → Machine.Input (LsetS (fst δ) ordδ) δ g
  → InjL Lδ δ
b9inf-given-graph δ Lδ ordδ cardδ δ∉ω e g inp =
  subst (λ w → InjL w δ) (sym Lδ≡stage)
    (Machine.pays-input (LsetS (fst δ) ordδ) δ g inp)
  where
  Lδ≡stage : Lδ ≡ LsetS (fst δ) ordδ
  Lδ≡stage = Σ≡Prop (λ (x : V ℓ) → snd (isL x)) e

-- =====================================================================
-- SECTION 4.  THE OBLIGATION, STATED AND NOT INHABITED.
--
--   `B9Inf` is copied letter for letter from
--   agents/tasks/LJ-1-593/Probe593.agda:511-514, at this file's own
--   bindings; `ClauseTrophy` above is its third hypothesis, already
--   copied.  NO TERM NAMED `b9-inf` IS IN THIS FILE.
--   `agents/tasks/LJ-1-596/review-of-b9-inf.md` states the NO-GO, and
--   section 3 above is what its reopener would have to supply.
-- =====================================================================

B9 : Type (ℓ-suc ℓ)
B9 = (δ Lδ : S) → IsOrd (fst δ) → (fst Lδ ≡ Lset (fst δ)) → InjL Lδ δ

B9Inf : Type (ℓ-suc ℓ)
B9Inf =
    (δ Lδ : S) → IsOrd (fst δ) → IsCardinalL δ → ClauseTrophy δ
  → (fst Lδ ≡ Lset (fst δ)) → InjL Lδ δ

-- The narrowing is a weakening ([LJ-1.593]'s `b9-pays-b9inf`,
-- agents/tasks/LJ-1-593/Probe593.agda:517-518), restated so the
-- relation between the two rows is a term of this file.
b9-pays-b9inf : B9 → B9Inf
b9-pays-b9inf b9 δ Lδ ordδ _ _ e = b9 δ Lδ ordδ e

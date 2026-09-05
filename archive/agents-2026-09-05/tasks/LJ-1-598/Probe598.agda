{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.598]  Clause (i) of the level-hood certificate, at a frame that
-- fits under the cap.
--
-- W3 IS SECTION 1 and the brief ordered it written FIRST and typechecked
-- ALONE.  The slice is agents/tasks/LJ-1-598/runs/W3.agda; its runs are
-- runs/w3-1.out (exit 42, a dropped conjunct in my own telescope) and
-- runs/w3-2.out (exit 0, 2.82 s).
--
-- THE FLOOR WAS MEASURED BEFORE ANY PROOF (D-10).  The first floor
-- slice, runs/FLOOR.agda, took [LJ-1.578]'s clause by IMPORT and
-- exhausted the 2 GiB wide cap while the IMPORT CHAIN was still
-- elaborating (runs/floor-1.out, exit 251 at 57.90 s, inside
-- LJ-1-570.Probe570).  The chain was then built module by module, one
-- Agda process per module (runs/chain-*.out), and [LJ-1.578]'s OWN FILE
-- exhausted the cap on its own account with every dependency warm
-- (runs/chain-578.out, exit 251 at 15.92 s).  SO THE IMPORT IS OFF and
-- clause (i) is TAKEN BY RESTATEMENT below, text for text from
-- agents/tasks/LJ-1-578/Probe578.agda:234-240.  That is the
-- restructure the heap-wall clause orders, tested under the same cap:
-- this file imports src/ and nothing else.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M2g" on this pane.  I did
-- not set it.  One Agda process at a time.
--
-- THE OBLIGATION IS NOT INHABITED AND NO NAME `defines-level` IS
-- DECLARED HERE.  The stop is stated at
-- agents/tasks/LJ-1-598/review-of-defines-level.md.  What this probe
-- lands instead are the two reductions the report prices: clause (i)
-- from a NAMED level (section 3) and clause (i) from a graph formula
-- read over codes at an ORDINAL index (section 4), plus the missing
-- bridge between the type's own hypothesis and the index those
-- reductions need (section 5).

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-598.Probe598 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; var; _≐_; _∧̇_; ∃̇_; ⊥̇ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.BoundedSubset {ℓ} lem using ( module HullStage )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

-- =====================================================================
-- THE FRAME.  One hull stage, as [LJ-1.578] section 3 instantiated it:
-- the ordinal of the stage, its successor closure, the parameter set,
-- and the empty set below the stage.  Nothing from any probe enters.
-- =====================================================================

module Frame (lam : SV.S) (ordλ : IsOrd lam)
             (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (X : SV.S)
             (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module T = HS.H.T

  -- ===================================================================
  -- SECTION 1.  W3.  THE WIDEST UNMEASURED TERM, TYPE ONLY.
  --
  --   The brief names it: uniqueness, not existence.  "Lset δ is the
  --   ONLY witness", stated alone at the stage's inner world.  The type
  --   below is runs/W3.agda:52-56 letter for letter, and runs/w3-2.out
  --   is its green run.  It is clause (i)'s own second conjunct
  --   (Probe578.agda:239-240) with the existence conjunct removed, at
  --   every code, with no side condition.
  -- ===================================================================

  OnlyLevel : Type (ℓ-suc ℓ)
  OnlyLevel =
    (c : T.Code)
    → Σ[ φ ∈ Formula T.Code 1 ]
        ((a : HS.ASt.SL) → ⟨ (a ∷ []) T.⊨c φ ⟩
         → fst a ≡ Lset (fst (T.val c)))

  -- AND THE W3 QUESTION IS ANSWERED BY A VACUITY, SO THE ANSWER IS
  -- MACHINE-CHECKED RATHER THAN ARGUED.  The uniqueness conjunct
  -- ALONE is free: an UNSATISFIABLE formula is vacuously unique.
  -- Satisfaction of `⊥̇` is the algebra's `⊥`
  -- (src/FOL/Semantics.lagda.md:99), and `⟨ ⊥ ⟩` is `⊥*`
  -- (src/Base/Truth.lagda.md:121), so the equation holds of every
  -- code at the empty formula.  WHAT THE BRIEF CALLED "the widest
  -- unmeasured term" IS THEREFORE NOT THIS TYPE: the content of
  -- clause (i) is uniqueness UNDER A SATISFIABLE formula, which is
  -- the conjunction and not the conjunct.
  only-level-vacuous : OnlyLevel
  only-level-vacuous c = ⊥̇ , λ a h → Empty.rec* h

  -- ===================================================================
  -- SECTION 2.  CLAUSE (i), TAKEN BY RESTATEMENT AND NOT BY IMPORT.
  --
  --   The text is [LJ-1.578]'s own (Probe578.agda:234-240), with the
  --   module openings of its `Cert` frame made explicit here.  The
  --   import walls under the standing cap (runs/chain-578.out), so the
  --   identity row a shared import would give is not available; every
  --   name in the restatement resolves against the same `src/`
  --   definitions that probe instantiates, `HullStage` included.
  -- ===================================================================

  ClauseI : Type (ℓ-suc ℓ)
  ClauseI =
    (c : T.Code) → IsOrd (HS.C.π (fst (T.val c)))
    → Σ[ φ ∈ Formula T.Code 1 ]
        ( ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (a ∷ []) T.⊨c φ ⟩ ∥₁
        × ((a : HS.ASt.SL) → ⟨ (a ∷ []) T.⊨c φ ⟩
           → fst a ≡ Lset (fst (T.val c))) )

  -- the body at one code, and the identity that says it is clause (i)
  Body : T.Code → Type (ℓ-suc ℓ)
  Body c =
    Σ[ φ ∈ Formula T.Code 1 ]
      ( ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (a ∷ []) T.⊨c φ ⟩ ∥₁
      × ((a : HS.ASt.SL) → ⟨ (a ∷ []) T.⊨c φ ⟩
         → fst a ≡ Lset (fst (T.val c))) )

  clause-i-from-body : ((c : T.Code) → IsOrd (HS.C.π (fst (T.val c))) → Body c)
                     → ClauseI
  clause-i-from-body f = f

  -- ===================================================================
  -- SECTION 3.  THE EQUATION ROUTE, PAID IN FULL.
  --
  --   If the hull NAMES the level at a code, then an EQUATION at that
  --   code is the formula clause (i) asks for, and uniqueness is free:
  --   equality at the restricted structure IS path equality
  --   (src/FOL/ZFStructure.lagda.md:148 against :82), so a satisfied
  --   equation is already the wanted path.  This is the whole content
  --   of the section and it typechecks as such.
  --
  --   THE ROUTE IS CIRCULAR FOR THE CERTIFICATE and I do not hide that:
  --   a code naming `Lset δ` is `Facts.HasLevels`'s own conclusion
  --   (Probe578.agda:120-122), which clause (i) exists to buy
  --   (`cert-gives-A`, Probe578.agda:254-273).  What the section
  --   measures is that NOTHING ELSE is owed on this route: the price of
  --   clause (i) is exactly a code for the level, and not one line of
  --   syntax beyond it.
  -- ===================================================================

  eqF : (d : T.Code) → Formula T.Code 1
  eqF d = var zero ≐ con d

  eq-sat : (d : T.Code) → ⟨ (T.val d ∷ []) T.⊨c eqF d ⟩
  eq-sat d = refl

  eq-uniq : (d : T.Code) (a : HS.ASt.SL)
          → ⟨ (a ∷ []) T.⊨c eqF d ⟩ → fst a ≡ fst (T.val d)
  eq-uniq d a h = h

  CodedLevels : Type (ℓ-suc ℓ)
  CodedLevels = (c : T.Code) → IsOrd (HS.C.π (fst (T.val c)))
              → Σ[ d ∈ T.Code ] (fst (T.val d) ≡ Lset (fst (T.val c)))

  coded-gives-level : CodedLevels → ClauseI
  coded-gives-level cl = clause-i-from-body (λ c oc → go c (cl c oc))
    where
    go : (c : T.Code)
       → Σ[ d ∈ T.Code ] (fst (T.val d) ≡ Lset (fst (T.val c)))
       → Body c
    go c (d , e) = eqF d , ∣ T.val d , eq-sat d ∣₁ , λ a h → eq-uniq d a h ∙ e

  -- ===================================================================
  -- SECTION 4.  THE GRAPH ROUTE, PRICED AS ITS TWO HYPOTHESES.
  --
  --   [LJ-1.595] left ONE open question: whether clause (i) falls out
  --   of a matrix the way clause (ii) does, at the price of the index
  --   substituted by a constant (review-of-defines-cover.md, "THE TWO
  --   THINGS THE NEXT BRIEF SHOULD DECIDE", item 2).  The substitution
  --   is avoidable: bind the index with an existential and EQUATE it
  --   with the code, the same shape `Shared` used for clause (ii)
  --   (Probe595.agda:495).  So the matrix route below needs no
  --   renaming and no substitution, and what it does need is exactly
  --   two statements, both left as hypotheses because neither is built
  --   anywhere in the tree:
  --
  --   `Det`: DETERMINATION.  A two-slot formula over codes, index in
  --   slot 0 and value in slot 1, whose every satisfaction at an
  --   ORDINAL index pins the value to the tower there.  This is the
  --   inner-world reading of what `Lset-only` proves at the class `L`
  --   (src/L/Hierarchy.lagda.md:334-337) and what `GraphAgree` would
  --   have to carry to the stage ([LJ-1.570], Probe570.agda:285-292,
  --   marked "parts are terms in five probes, none in src/" at
  --   lj-1.570-report.md:96-100).
  --
  --   `Wit`: EXISTENCE.  The formula is satisfied at every ordinal of
  --   the inner world, at the level there.
  --
  --   Given the two, clause (i) follows at every ORDINAL-VALUED code,
  --   and the term below is that implication in full.
  -- ===================================================================

  Det : Formula T.Code 2 → Type (ℓ-suc ℓ)
  Det ψ = (b a : HS.ASt.SL) → IsOrd (fst b)
        → ⟨ (b ∷ a ∷ []) T.⊨c ψ ⟩ → fst a ≡ Lset (fst b)

  Wit : Formula T.Code 2 → Type (ℓ-suc ℓ)
  Wit ψ = (b : HS.ASt.SL) → IsOrd (fst b)
        → ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (b ∷ a ∷ []) T.⊨c ψ ⟩ ∥₁

  inF : (ψ : Formula T.Code 2) → T.Code → Formula T.Code 1
  inF ψ c = ∃̇ (ψ ∧̇ (var zero ≐ con c))

  graph-gives-level : (ψ : Formula T.Code 2) → Det ψ → Wit ψ
                    → (c : T.Code) → IsOrd (fst (T.val c)) → Body c
  graph-gives-level ψ det wit c oc = inF ψ c , sat , uniq
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

  -- ===================================================================
  -- SECTION 5.  THE INDEX GAP, STATED AS THE MISSING BRIDGE.
  --
  --   Clause (i)'s hypothesis is about the COLLAPSE of the code's
  --   value: `IsOrd (HS.C.π (fst (T.val c)))`.  Section 4's reduction
  --   needs the value ITSELF ordinal, and so does every determination
  --   the tree delivers: `Lset-only` demands `IsOrd` of its argument
  --   (src/L/Hierarchy.lagda.md:335-336) and `ride-only` the same
  --   (src/L/Condensation.lagda.md:422).  The bridge between the two,
  --   if it exists, is not built anywhere, and the report's D-10
  --   section says why it should not be expected: at a NON-ordinal
  --   index the tree's own graph formula is satisfied by a set that is
  --   not the level there.  It is written here as a TYPE so the next
  --   brief can price it or refute it.
  -- ===================================================================

  PreimageOrd : Type (ℓ-suc ℓ)
  PreimageOrd = (c : T.Code) → IsOrd (HS.C.π (fst (T.val c)))
              → IsOrd (fst (T.val c))

  preimage-gives-level : (ψ : Formula T.Code 2) → Det ψ → Wit ψ → PreimageOrd
                       → ClauseI
  preimage-gives-level ψ det wit po =
    clause-i-from-body (λ c oc → graph-gives-level ψ det wit c (po c oc))

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.552]  The assignment at the heart of GCH.
--
-- W3 IS SECTION 1, AND IT WAS WRITTEN FIRST AND TYPECHECKED ALONE.
-- The slice is agents/tasks/LJ-1-552/runs/W3.agda, runs w3-1.out to
-- w3-3.out, exit 0.  Its two red predecessors are kept as
-- runs/w3-red-1.out and runs/w3-red-2.out.
--
-- THE OBLIGATION IS NOT INHABITED.  No term of this file is named
-- `succ-assignment`.  The stop is
-- agents/tasks/LJ-1-552/review-of-succ-assignment.md.  This file
-- carries NO hole and NO postulate, so every reduction in it is a
-- measurement and not a claim ([LJ-1.533]'s discipline, kept by
-- [LJ-1.549]).  Nothing lands in src/.
--
-- WHAT THIS FILE MEASURES, IN ONE LINE EACH.
--
--   Section 1.  W3, BOTH HALVES, AND BOTH ARE GO.
--               (a) `member-into-kappa`: every member of δ injects
--                   into κ, AMBIENTLY.  This is where `SuccCardL`'s
--                   leastness clause is spent, the clause [LJ-1.549]
--                   reported unused.
--               (b) `memSWO`: the picking well-order exists at the
--                   members of ANY set of L, not only at a stage.
--   Section 2.  THE OBLIGATION IS AN AMBIENT INJECTION of δ into the
--               power set of κ inside L, both directions, by
--               [LJ-1.549]'s own two terms, IMPORTED.
--   Section 3.  IT IS FREE BELOW κ AND ONLY BELOW κ.  The identity is
--               an assignment on `sucʟ κ`, and `sucʟ κ` is a MEMBER of
--               δ, so the free part never reaches δ.
--   Section 4.  THE RESIDUE OF THIS TASK.  A separating family of
--               codes with POINTWISE existence buys the obligation,
--               and the obligation buys it back.  So the choosing is
--               free and the whole cost is the pointwise existence.
--   Section 5.  WHAT THE POINTWISE EXISTENCE WOULD NEED, stated with
--               the two generators of an L-set and their arity.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M8g" on this pane.  I
-- did not set it.  One Agda process at a time.  No heap event.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-552.Probe552 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Cardinal {ℓ} lem
  using ( IsCardinalL; InjCode; module LeastCardInjL )
open import L.CantorBernstein {ℓ} lem using ( readL )
open import L.BoundedSubset {ℓ} lem
  using ( IsCardinal; _↪_; module Devlin55 )
open import L.GCH {ℓ} lem using ( SuccCardL )
open import L.Choice.Stage {ℓ} lem using ( stageBound; stage-below )
open import L.Choice.Step {ℓ} lem using ( pullOrder; stageOrder )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( SWO; IsLeast; leastOf )
open import L.Axioms.Numerals {ℓ} using ( sucʟ )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )

open Devlin55 using ( comp-inj; ord-emb )

open import Cubical.HITs.CumulativeHierarchy.Base
  using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪ )
open import Cubical.Functions.Embedding using ( Embedding-into-isSet→isSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

-- [LJ-1.549] IS A STATED NO-GO AND ITS PROBE CARRIES NO HOLE
-- (agents/tasks/LJ-1-549/lj-1.549-report.md, `## VERDICT`).  The
-- residue this task takes three components of is IMPORTED from the
-- file that typechecked, so it cannot have drifted.
import LJ-1-549.Probe549 {ℓ} lem as P549

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SV using ( _∈ˢ_ )
open SL using ( S )

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( _⊆ˢ_ )

open P549 using ( powL; powL-sub; powL-in )

-- =====================================================================
-- SECTION 0.  THE OBLIGATION, AND THE PIN.
--
--   The brief's type, transcribed once.  NOTHING IN THIS FILE
--   INHABITS IT, and no term of this file is named `succ-assignment`.
-- =====================================================================

Assignment : (δ κ : S) → Type (ℓ-suc ℓ)
Assignment δ κ =
  ∥ Σ[ s ∈ (⟪ fst δ ⟫ → S) ]
      ( ((k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
      × ((k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k') ) ∥₁

-- THE PIN.  The brief says the obligation is the FIRST THREE components
-- of [LJ-1.549]'s `Residue` (agents/tasks/LJ-1-549/Probe549.agda:668).
-- This term takes that residue apart and rebuilds nothing: if the
-- transcription above had drifted in any detail, it would not
-- typecheck.
residue-first-three : (δ κ : S) → P549.Residue δ κ → Assignment δ κ
residue-first-three δ κ (s , (sub , (inj , _))) = ∣ s , (sub , inj) ∣₁

-- =====================================================================
-- SECTION 1.  W3.  WRITTEN FIRST, TYPECHECKED ALONE, AND BOTH HALVES
-- ARE GO.  The slice is runs/W3.agda; this section is that slice.
-- =====================================================================

-- 1a.  THE LEASTNESS CLAUSE, SPENT.

-- The ambient cardinality of an L-element ordinal is an ambient
-- cardinal.  `LeastCardInjL` (src/L/Cardinal.lagda.md:61) selects the
-- least ordinal the index injects into; nothing below that can be
-- injected into, or the composite would beat the selection.
card-of : (a : S) (oa : IsOrd (fst a))
        → IsCardinal (fst (LeastCardInjL.κ a oa))
card-of a oa d d∈c f =
  M.κ-min-at (d , isL-trans {x = fst M.κ} {y = d} d∈c (snd M.κ)) d∈c
             (PT.map (λ g → comp-inj g f) M.κ-inj)
  where
  module M = LeastCardInjL a oa

-- The bridge, three lines ([LJ-1.528]'s section 2, re-typed:
-- agents/tasks/LJ-1-528/Probe528.agda:105-107).
ambient→internal : (a : S) → IsCardinal (fst a) → IsCardinalL a
ambient→internal a c d d∈a h =
  PT.rec Empty.isProp⊥ (λ w → c (fst d) d∈a (readL a d w)) h

-- THE HALF.  Every member of δ injects into κ, ambiently.
--
-- `SuccCardL`'s FOURTH COMPONENT (src/L/GCH.lagda.md:51-52) is what
-- pays.  IT IS NOT THE FIRST SPEND OF THAT COMPONENT AND I WILL NOT
-- REPORT IT AS ONE: [LJ-1.550]'s `site-forced`
-- (agents/tasks/LJ-1-550/Probe550.agda:385-390) applies it to a
-- HYPOTHESISED ambient cardinal μ and concludes `δ ⊆ μ`.  The
-- difference is that here the cardinal is PRODUCED, by
-- `LeastCardInjL` at the member itself, so the conclusion is an
-- injection and not an inclusion.
member-into-kappa :
    (δ κ : S) → SuccCardL δ κ
  → (a : S) → ⟨ fst a ∈ˢ fst δ ⟩
  → ∥ ⟪ fst a ⟫ ↪ ⟪ fst κ ⟫ ∥₁
member-into-kappa δ κ (oδ , _ , κ∈δ , least) a a∈δ =
  go (ord-tri (fst M.κ) M.oκ (fst κ) oκ)
  where
  oa : IsOrd (fst a)
  oa = mem-ord {A = fst δ} oδ (fst a) a∈δ
  oκ : IsOrd (fst κ)
  oκ = mem-ord {A = fst δ} oδ (fst κ) κ∈δ
  module M = LeastCardInjL a oa

  cardL : IsCardinalL M.κ
  cardL = ambient→internal M.κ (card-of a oa)

  -- If κ were BELOW the cardinality of `a`, then δ would be below it
  -- too, by leastness; and the cardinality of `a` never leaves `a`.
  -- `∈sucV-elim`'s motive lives in `Type (ℓ-suc ℓ)` and `Empty.⊥` does
  -- not, so the conclusion is the lifted empty type.
  absurd : ⟨ fst κ ∈ˢ fst M.κ ⟩ → Empty.⊥* {ℓ-suc ℓ}
  absurd κ∈c = ∈sucV-elim {A = fst a} {x = fst M.κ}
                 Empty.isProp⊥* M.κ∈sα below same
    where
    a∈c : ⟨ fst a ∈ˢ fst M.κ ⟩
    a∈c = least M.κ M.oκ cardL κ∈c a a∈δ
    below : ⟨ fst M.κ ∈ˢ fst a ⟩ → Empty.⊥* {ℓ-suc ℓ}
    below c∈a = Empty.rec (∈-irrefl (fst a) (oa .fst a∈c c∈a))
    same : fst M.κ ≡ fst a → Empty.⊥* {ℓ-suc ℓ}
    same e = Empty.rec (∈-irrefl (fst a)
               (subst (λ v → ⟨ fst a ∈ˢ v ⟩) e a∈c))

  go : Tri (fst M.κ) (fst κ) → ∥ ⟪ fst a ⟫ ↪ ⟪ fst κ ⟫ ∥₁
  go (inl c∈κ) =
    PT.map (λ f → comp-inj f (ord-emb (fst M.κ) (fst κ) oκ c∈κ)) M.κ-inj
  go (inr (inl e)) = subst (λ v → ∥ ⟪ fst a ⟫ ↪ ⟪ v ⟫ ∥₁) e M.κ-inj
  go (inr (inr κ∈c)) = Empty.rec* (absurd κ∈c)

-- 1b.  THE PICKING WELL-ORDER, AT THE MEMBERS OF ANY SET OF L.

module MemOrder (b : S) where

  β : V ℓ
  β = stageBound (fst b) (snd b) .fst

  oβ : IsOrd β
  oβ = stageBound (fst b) (snd b) .snd .fst

  below : (x : V ℓ) → ⟨ x ∈ˢ fst b ⟩ → ⟨ x ∈ˢ Lset β ⟩
  below x x∈b =
    Lset-mono (stageBound (fst b) (snd b) .snd .snd .snd)
      (stage-below (fst b) (snd b) x x∈b)

  into : ⟪ fst b ⟫ → ⟪ Lset β ⟫
  into m = fiber (Lset β) (below (⟪ fst b ⟫↪ m) (member (fst b) m)) .fst

  into-inj : (m n : ⟪ fst b ⟫) → into m ≡ into n → m ≡ n
  into-inj m n e = ↪-inj {a = fst b}
    (sym (fiber (Lset β) (below (⟪ fst b ⟫↪ m) (member (fst b) m)) .snd)
      ∙ cong (⟪ Lset β ⟫↪) e
      ∙ fiber (Lset β) (below (⟪ fst b ⟫↪ n) (member (fst b) n)) .snd)

-- THE HALF.  A strict well-order on the members of any set of L.
memSWO : (b : S) → SWO ⟪ fst b ⟫
memSWO b = pullOrder ⟪ fst b ⟫ ⟪ Lset M.β ⟫ (stageOrder M.β M.oβ)
             M.into M.into-inj
  where
  module M = MemOrder b

-- =====================================================================
-- SECTION 2.  THE OBLIGATION IS AN AMBIENT INJECTION INTO `powL κ`.
--
--   Both directions, and NEITHER IS REBUILT: they are [LJ-1.549]'s
--   section 6 (agents/tasks/LJ-1-549/Probe549.agda:565-600), imported.
-- =====================================================================

AmbInto : (δ κ : S) → Type ℓ
AmbInto δ κ = ⟪ fst δ ⟫ ↪ ⟪ fst (powL κ) ⟫

obligation-is-ambient : (δ κ : S) → Assignment δ κ → ∥ AmbInto δ κ ∥₁
obligation-is-ambient δ κ =
  PT.map (λ { (s , (sub , inj)) → P549.assignment→ambient δ κ s sub inj })

ambient-is-obligation : (δ κ : S) → ∥ AmbInto δ κ ∥₁ → Assignment δ κ
ambient-is-obligation δ κ = PT.map (P549.ambient→assignment δ κ)

-- =====================================================================
-- SECTION 3.  FREE BELOW κ, AND ONLY BELOW κ.
--
--   Every member of `sucʟ κ` IS a subset of κ, so the IDENTITY is an
--   assignment there and it costs nothing.  That is the whole of what
--   a producer with no coding can reach, and `sucʟ κ` is a MEMBER of
--   δ, so it never reaches δ.
-- =====================================================================

upOf : (b : S) → ⟪ fst b ⟫ → S
upOf b m = ⟪ fst b ⟫↪ m
         , isL-trans {x = fst b} {y = ⟪ fst b ⟫↪ m} (member (fst b) m) (snd b)

free-below-kappa :
    (κ : S) → IsOrd (fst κ)
  → Σ[ s ∈ (⟪ fst (sucʟ κ) ⟫ → S) ]
      ( ((k : ⟪ fst (sucʟ κ) ⟫) → ⟨ s k ⊆ˢ κ ⟩)
      × ((k k' : ⟪ fst (sucʟ κ) ⟫) → fst (s k) ≡ fst (s k') → k ≡ k') )
free-below-kappa κ oκ = upOf (sucʟ κ) , (sub , inj)
  where
  sub : (k : ⟪ fst (sucʟ κ) ⟫) → ⟨ upOf (sucʟ κ) k ⊆ˢ κ ⟩
  sub k = P549.succ-kappa-subsets κ oκ (upOf (sucʟ κ) k)
            (member (fst (sucʟ κ)) k)
  inj : (k k' : ⟪ fst (sucʟ κ) ⟫)
      → fst (upOf (sucʟ κ) k) ≡ fst (upOf (sucʟ κ) k') → k ≡ k'
  inj k k' e = ↪-inj {a = fst (sucʟ κ)} e

-- AND THE FREE PART NEVER REACHES δ.  [LJ-1.549]'s `succ-kappa-in`
-- (agents/tasks/LJ-1-549/Probe549.agda:514), cited and not rebuilt.
free-part-is-a-member :
    (δ κ : S) → IsOrd (fst δ) → IsOrd (fst κ) → IsCardinalL δ
  → ⟨ fst κ ∈ fst δ ⟩
  → (⟨ fst κ ∈ fst ωʟ ⟩ → Empty.⊥) → ((k : ℕ) → ⟨ # k ∈ fst κ ⟩)
  → ⟨ fst (sucʟ κ) ∈ fst δ ⟩
free-part-is-a-member = P549.succ-kappa-in

-- =====================================================================
-- SECTION 4.  THE RESIDUE OF THIS TASK, AND IT IS POINTWISE.
--
--   `Codes δ κ` is a family of predicates on the members of `powL κ`,
--   one per member of δ, that (i) is inhabited at every member of δ
--   and (ii) separates: no member of `powL κ` satisfies the predicate
--   of two different members of δ.
--
--   THE CHOOSING IS FREE.  Section 1b's well-order plus `leastOf`
--   (src/L/WellOrder/Base.lagda.md:158) turns (i) and (ii) into the
--   assignment with NO choice and NO extra hypothesis.  So the
--   truncation in the obligation is not the obstruction, and neither
--   is the ambient function.
-- =====================================================================

Codes : (δ κ : S) → Type (ℓ-suc ℓ)
Codes δ κ =
  Σ[ C ∈ (⟪ fst δ ⟫ → ⟪ fst (powL κ) ⟫ → hProp ℓ) ]
    ( ((k : ⟪ fst δ ⟫) → ∥ Σ[ A ∈ ⟪ fst (powL κ) ⟫ ] ⟨ C k A ⟩ ∥₁)
    × ((k k' : ⟪ fst δ ⟫) (A : ⟪ fst (powL κ) ⟫)
         → ⟨ C k A ⟩ → ⟨ C k' A ⟩ → k ≡ k') )

codes-suffice : (δ κ : S) → Codes δ κ → Assignment δ κ
codes-suffice δ κ (C , (ex , sep)) = ∣ s , (sub , inj) ∣₁
  where
  w : SWO ⟪ fst (powL κ) ⟫
  w = memSWO (powL κ)

  pick : (k : ⟪ fst δ ⟫)
       → Σ[ A ∈ ⟪ fst (powL κ) ⟫ ] IsLeast w (C k) A
  pick k = leastOf w {ℓ'' = ℓ} lem (C k) (ex k)

  s : ⟪ fst δ ⟫ → S
  s k = upOf (powL κ) (fst (pick k))

  sub : (k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩
  sub k = powL-sub κ (s k) (member (fst (powL κ)) (fst (pick k)))

  inj : (k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k'
  inj k k' e = sep k k' (fst (pick k')) here there
    where
    same : fst (pick k) ≡ fst (pick k')
    same = ↪-inj {a = fst (powL κ)} e
    here : ⟨ C k (fst (pick k')) ⟩
    here = subst (λ A → ⟨ C k A ⟩) same (fst (snd (pick k)))
    there : ⟨ C k' (fst (pick k')) ⟩
    there = fst (snd (pick k'))

-- AND THE OBLIGATION BUYS IT BACK, so the residue is EXACTLY the
-- obligation and not a weakening of it.  The predicate is "being the
-- value", which is a proposition because the carrier is a set.
codes-are-the-obligation : (δ κ : S) → Assignment δ κ → ∥ Codes δ κ ∥₁
codes-are-the-obligation δ κ = PT.map build
  where
  build : Σ[ s ∈ (⟪ fst δ ⟫ → S) ]
            ( ((k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
            × ((k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k') )
        → Codes δ κ
  build (s , (sub , inj)) = C , (ex , sep)
    where
    P : V ℓ
    P = fst (powL κ)

    isSet⟪P⟫ : isSet ⟪ P ⟫
    isSet⟪P⟫ = Embedding-into-isSet→isSet (⟪ P ⟫↪ , isEmb⟪ P ⟫↪) setIsSet

    f : ⟪ fst δ ⟫ → ⟪ P ⟫
    f k = fiber P (powL-in κ (s k) (sub k)) .fst

    fval : (k : ⟪ fst δ ⟫) → ⟪ P ⟫↪ (f k) ≡ fst (s k)
    fval k = fiber P (powL-in κ (s k) (sub k)) .snd

    C : ⟪ fst δ ⟫ → ⟪ P ⟫ → hProp ℓ
    C k A = (A ≡ f k) , isSet⟪P⟫ A (f k)

    ex : (k : ⟪ fst δ ⟫) → ∥ Σ[ A ∈ ⟪ P ⟫ ] ⟨ C k A ⟩ ∥₁
    ex k = ∣ f k , refl ∣₁

    sep : (k k' : ⟪ fst δ ⟫) (A : ⟪ P ⟫)
        → ⟨ C k A ⟩ → ⟨ C k' A ⟩ → k ≡ k'
    sep k k' A h h' =
      inj k k' (sym (fval k) ∙ cong (⟪ P ⟫↪) (sym h ∙ h') ∙ fval k')

-- =====================================================================
-- SECTION 5.  WHAT THE POINTWISE EXISTENCE WOULD NEED.
--
--   Section 4 leaves ONE thing: at a member `a` of δ with κ ∈ a, an
--   L-SET subset of κ that determines `a`.  Section 1a gives the
--   AMBIENT injection ⟪a⟫ ↪ ⟪κ⟫ and nothing turns that into a set of
--   L.  There are exactly TWO generators of a set of L in the tree and
--   BOTH take a `Formula`:
--
--     hasSeparationL  (src/L/Axioms/Full.lagda.md:144)   Formula S 1
--     hasReplacementL (src/L/Axioms/Full.lagda.md:277)   Formula S 2
--
--   `hasPowerL` (src/L/Axioms/Power.lagda.md:187) is the first one at
--   `subFo`, so it adds no third shape; and section 4 shows the only
--   other route, picking out of a set that already exists, needs the
--   existence first.
--
--   THE CLASSICAL CODING IS A WELL-ORDER OF A SUBSET OF κ CARRIED DOWN
--   BY A PAIRING, and the tree's pairing is AMBIENT:
--
--     sq              (src/L/Ordinal/SquareLaw.lagda.md:685)
--     via-col-square  (src/L/Ordinal/SquareLaw.lagda.md:960)
--     sq-trunc-closed (src/L/SquareLawClosed.lagda.md:325)
--
--   An ambient pairing carries an L-set to an ambient subset of κ, and
--   an ambient subset of κ is not a member of `powL κ`.  That is the
--   stop, and review-of-succ-assignment.md states it.
-- =====================================================================

-- One consequence of section 3 worth stating on its own, because it
-- says the free part cannot be patched onto a coded part: the two
-- would have to be told apart inside `powL κ`, and telling them apart
-- is a tag, and a tag on a subset of κ is the same pairing that is
-- missing.  So this term is the WHOLE of what is free.
free-is-all-that-is-free :
    (κ : S) → IsOrd (fst κ)
  → Σ[ s ∈ (⟪ fst (sucʟ κ) ⟫ → S) ]
      ( ((k : ⟪ fst (sucʟ κ) ⟫) → ⟨ s k ⊆ˢ κ ⟩)
      × ((k k' : ⟪ fst (sucʟ κ) ⟫) → fst (s k) ≡ fst (s k') → k ≡ k') )
free-is-all-that-is-free = free-below-kappa

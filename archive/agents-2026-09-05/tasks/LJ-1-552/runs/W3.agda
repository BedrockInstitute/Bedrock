{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.552] W3.  THE WELL-ORDER THAT PICKS A CODING.
--
-- WRITTEN FIRST AND TYPECHECKED ALONE, before any other Agda of this
-- task, exactly as the brief orders.  No hole, no postulate.
--
-- The brief names the widest unmeasured term:
--
--     -- the term in this tree that gives, for a member of delta, a
--     -- bijection to a subset of kappa, or the sentence that there is
--     -- none
--
-- THAT SPLITS IN TWO, and this slice measures both halves.
--
--   HALF 1, `member-into-kappa`.  THE COMPARISON EXISTS.  Every member
--   of delta injects into kappa, AMBIENTLY, and this is where
--   `SuccCardL`'s leastness clause (src/L/GCH.lagda.md:51-52) is
--   spent.  `[LJ-1.549]` reported the clause unused and said the whole
--   difficulty sits on the other side of it
--   (agents/tasks/LJ-1-549/lj-1.549-report.md, `## THE LEASTNESS
--   CLAUSE`).  This is that other side, and the clause pays for it.
--
--   HALF 2, `memSWO`.  THE PICKING WELL-ORDER EXISTS, at the members
--   of ANY set of L, not only at a stage.  `orderAt`
--   (src/L/Choice/Step.lagda.md:730) orders the members of a stage;
--   `stageBound` (src/L/Choice/Stage.lagda.md:366) puts every member
--   of a set of L inside one stage; `pullOrder`
--   (src/L/Choice/Step.lagda.md:242) pulls the order back.  With
--   `leastOf` (src/L/WellOrder/Base.lagda.md:158) that is a choice-free
--   selection from any non-empty family over the members of a set of L.
--
-- WHAT THIS SLICE DOES NOT MEASURE, AND THE REPORT SAYS SO: neither
-- half produces an L-SET subset of kappa.  Half 1's injection is an
-- ambient function; half 2 can only PICK from sets that already exist.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-552.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Cardinal {ℓ} lem using ( IsCardinalL; InjCode; module LeastCardInjL )
open import L.CantorBernstein {ℓ} lem using ( readL )
open import L.BoundedSubset {ℓ} lem using ( IsCardinal; _↪_; module Devlin55 )
open import L.GCH {ℓ} lem using ( SuccCardL )
open import L.Choice.Stage {ℓ} lem using ( stageBound; stage-below )
open import L.Choice.Step {ℓ} lem using ( pullOrder; stageOrder )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( SWO )

open Devlin55 using ( comp-inj; ord-emb )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SV using ( _∈ˢ_ )

-- ---------------------------------------------------------------------
-- HALF 1.  THE LEASTNESS CLAUSE, SPENT.
-- ---------------------------------------------------------------------

-- The ambient cardinality of an L-element ordinal is an ambient
-- cardinal.  `LeastCardInjL` (src/L/Cardinal.lagda.md:61) selects the
-- least ordinal the index injects into; nothing below it can be
-- injected into, or the composite would beat the selection.
card-of : (a : SL.S) (oa : IsOrd (fst a))
        → IsCardinal (fst (LeastCardInjL.κ a oa))
card-of a oa d d∈c f =
  M.κ-min-at (d , isL-trans {x = fst M.κ} {y = d} d∈c (snd M.κ)) d∈c
             (PT.map (λ g → comp-inj g f) M.κ-inj)
  where
  module M = LeastCardInjL a oa

-- The bridge, three lines ([LJ-1.528]'s section 2, re-typed:
-- agents/tasks/LJ-1-528/Probe528.agda:105-107).
ambient→internal : (a : SL.S) → IsCardinal (fst a) → IsCardinalL a
ambient→internal a c d d∈a h =
  PT.rec Empty.isProp⊥ (λ w → c (fst d) d∈a (readL a d w)) h

-- THE HALF.  Every member of delta injects into kappa, ambiently.
member-into-kappa :
    (δ κ : SL.S) → SuccCardL δ κ
  → (a : SL.S) → ⟨ fst a ∈ˢ fst δ ⟩
  → ∥ ⟪ fst a ⟫ ↪ ⟪ fst κ ⟫ ∥₁
member-into-kappa δ κ (oδ , _ , κ∈δ , least) a a∈δ =
  go (ord-tri (fst M.κ) M.oκ (fst κ) oκ)
  where
  oa : IsOrd (fst a)
  oa = mem-ord {A = fst δ} oδ (fst a) a∈δ
  oκ : IsOrd (fst κ)
  oκ = mem-ord {A = fst δ} oδ (fst κ) κ∈δ
  module M = LeastCardInjL a oa

  -- the cardinality of `a`, internally a cardinal
  cardL : IsCardinalL M.κ
  cardL = ambient→internal M.κ (card-of a oa)

  -- if kappa were BELOW it, delta would have to be below it too, and
  -- the cardinality of `a` never leaves `a`.
  -- `∈sucV-elim`'s motive lives in `Type (ℓ-suc ℓ)` and `Empty.⊥` does
  -- not, so the conclusion is the lifted empty type ([LJ-1.549] hit the
  -- same wall, agents/tasks/LJ-1-549/lj-1.549-report.md, red run 4).
  absurd : ⟨ fst κ ∈ˢ fst M.κ ⟩ → Empty.⊥* {ℓ-suc ℓ}
  absurd κ∈c = ∈sucV-elim {A = fst a} {x = fst M.κ}
                 Empty.isProp⊥* M.κ∈sα below same
    where
    a∈c : ⟨ fst a ∈ˢ fst M.κ ⟩
    a∈c = least M.κ M.oκ cardL κ∈c a a∈δ
    below : ⟨ fst M.κ ∈ˢ fst a ⟩ → Empty.⊥* {ℓ-suc ℓ}
    below c∈a = Empty.rec (∈-irrefl (fst a) (oa .fst a∈c c∈a))
    same : fst M.κ ≡ fst a → Empty.⊥* {ℓ-suc ℓ}
    same e = Empty.rec (∈-irrefl (fst a) (subst (λ v → ⟨ fst a ∈ˢ v ⟩) e a∈c))

  go : Tri (fst M.κ) (fst κ) → ∥ ⟪ fst a ⟫ ↪ ⟪ fst κ ⟫ ∥₁
  go (inl c∈κ) =
    PT.map (λ f → comp-inj f (ord-emb (fst M.κ) (fst κ) oκ c∈κ)) M.κ-inj
  go (inr (inl e)) = subst (λ v → ∥ ⟪ fst a ⟫ ↪ ⟪ v ⟫ ∥₁) e M.κ-inj
  go (inr (inr κ∈c)) = Empty.rec* (absurd κ∈c)

-- ---------------------------------------------------------------------
-- HALF 2.  THE PICKING WELL-ORDER, AT THE MEMBERS OF ANY SET OF L.
-- ---------------------------------------------------------------------

module MemOrder (b : SL.S) where

  β : V ℓ
  β = stageBound (fst b) (snd b) .fst

  oβ : IsOrd β
  oβ = stageBound (fst b) (snd b) .snd .fst

  -- every member of `b` sits in one stage
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
memSWO : (b : SL.S) → SWO ⟪ fst b ⟫
memSWO b = pullOrder ⟪ fst b ⟫ ⟪ Lset M.β ⟫ (stageOrder M.β M.oβ)
             M.into M.into-inj
  where
  module M = MemOrder b

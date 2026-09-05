{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.334 probe A.  It lands nothing.  It runs in agents/tasks/LJ-1-334/.
--
-- THE BRIEF ASKS: does `[LJ-1.321]` item 1, the pointwise-least pairing,
-- give a canonical `sq α` at a non-initial limit ordinal, and if not,
-- where exactly does it fail?
--
-- Item 1 as written (agents/tasks/LJ-1-321/lj-1.321-report.md:309-315):
-- the carrier is well-ordered, so send a pair to the LEAST value that
-- some witness takes there.  The map reads only truncations, so it is
-- canonical for free.  `[LJ-1.321]` guessed that injectivity would fail
-- and did not build it.
--
-- PART 1 builds item 1's map.  It exists and it is canonical.
-- PART 2 flips the pair.  The reachable set does not see the flip.
-- PART 3 refutes item 1.  The map is symmetric, so it is injective only
--        if the carrier is a proposition, and in the band it is not.
-- PART 4 names how wide PART 3 reaches, and stops there (C-36).
-- PART 5 answers the brief's premise about omega times two.
-- PART 6 records the negative controls.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-334.ProbeLJ1334A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Presentation {ℓ} using ( fiber )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( ω-ord )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )
open import L.Ordinal.StageArith {ℓ} lem using ( +ω; +ω-ord; +ω-mem; +ω-iter )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; IsLeast; isPropLeastOf; leastOf )

open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )

-- =====================================================================
-- PART 1.  ITEM 1'S MAP, BUILT.
--
--   THE UNTRUNCATED CONTROL COMES FIRST (C-56).  With `sq α` in hand
--   the pairing is a projection and nothing is owed.  Every later term
--   is read against this one.
-- =====================================================================

control-untruncated : (α : S) → sq α → ⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫
control-untruncated α s = s .fst

-- The reachable set at a pair: the values that some square-law witness
-- takes there.  It is a proposition, so `leastOf` applies to it.  This
-- is item 1's predicate, with the target of the composite in place of
-- `[LJ-1.321]`'s intermediate `δ₀`.
Reach : (α : S) → ⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫ → hProp ℓ
Reach α p c = ∥ Σ[ s ∈ sq α ] (s .fst p ≡ c) ∥₁ , squash₁

-- The reachable set is never empty, from the truncation alone.
reach-ne : (α : S) (t : ∥ sq α ∥₁) (p : ⟪ α ⟫ × ⟪ α ⟫)
         → ∥ Σ[ c ∈ ⟪ α ⟫ ] ⟨ Reach α p c ⟩ ∥₁
reach-ne α t p = PT.map (λ s → s .fst p , ∣ s , refl ∣₁) t

-- ITEM 1, BUILT.  The well-order on the carrier is a HYPOTHESIS here,
-- so PART 3 refutes item 1 for EVERY well-order and not only for the
-- delivered one.  `OrdSWO.ordSWO` (src/L/StageCardinal.lagda.md:258-263)
-- shows the hypothesis is inhabited at every ordinal.
item1-h : (α : S) → SWO ⟪ α ⟫ → ∥ sq α ∥₁ → ⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫
item1-h α w t p = leastOf w lem (Reach α p) (reach-ne α t p) .fst

-- ITEM 1'S OWN CLAIM, MEASURED: the map is canonical.  It reads the
-- truncation and nothing else, so two proofs of the truncation give the
-- same map.  No choice is spent.
item1-canonical : (α : S) (w : SWO ⟪ α ⟫) (t t' : ∥ sq α ∥₁)
                → (p : ⟪ α ⟫ × ⟪ α ⟫) → item1-h α w t p ≡ item1-h α w t' p
item1-canonical α w t t' p i = item1-h α w (squash₁ t t' i) p

-- WHAT ITEM 1 STILL OWES, and it is exactly one thing.  Injectivity of
-- `item1-h` closes the deliverable and nothing else is missing.  That
-- is `[LJ-1.321]`'s own diagnosis, compiled.
item1-sq : (α : S) (w : SWO ⟪ α ⟫) (t : ∥ sq α ∥₁)
         → ((u v : ⟪ α ⟫ × ⟪ α ⟫)
            → item1-h α w t u ≡ item1-h α w t v → u ≡ v)
         → sq α
item1-sq α w t hinj = item1-h α w t , hinj

-- =====================================================================
-- PART 2.  THE FLIP, AND THE COLLAPSE.
--
--   `sq α` is closed under precomposition with any permutation of the
--   pair type.  The cheapest permutation is the flip, and it is an
--   involution, so it needs no decidable equality and no order.
-- =====================================================================

swap : {A : Type ℓ} → A × A → A × A
swap (x , y) = (y , x)

flip-sq : (α : S) → sq α → sq α
flip-sq α (f , finj) = (λ p → f (swap p)) , inj
  where
  inj : (u v : ⟪ α ⟫ × ⟪ α ⟫) → f (swap u) ≡ f (swap v) → u ≡ v
  inj u v e = cong swap (finj (swap u) (swap v) e)

-- THE COLLAPSE, IN ONE LINE.  The reachable set does not see the flip,
-- because the flipped witness reaches at the flipped pair exactly what
-- the witness reaches here.
reach-flip : (α : S) (p : ⟪ α ⟫ × ⟪ α ⟫) (c : ⟪ α ⟫)
           → ⟨ Reach α p c ⟩ → ⟨ Reach α (swap p) c ⟩
reach-flip α p c = PT.map (λ { (s , e) → flip-sq α s , e })

-- Leastness transfers across a two-way implication of predicates.  No
-- univalence and no path between propositions is needed.
least-transfer : {A : Type ℓ} (w : SWO A) (P Q : A → hProp ℓ)
               → ((x : A) → ⟨ P x ⟩ → ⟨ Q x ⟩)
               → ((x : A) → ⟨ Q x ⟩ → ⟨ P x ⟩)
               → (m : A) → IsLeast w P m → IsLeast w Q m
least-transfer w P Q pq qp m (pm , mn) = pq m pm , λ b qb → mn b (qp b qb)

-- ITEM 1'S MAP IS SYMMETRIC.  This is the measurement.
item1-symmetric : (α : S) (w : SWO ⟪ α ⟫) (t : ∥ sq α ∥₁)
                → (p : ⟪ α ⟫ × ⟪ α ⟫)
                → item1-h α w t p ≡ item1-h α w t (swap p)
item1-symmetric α w t p = cong fst
  (isPropLeastOf w (Reach α (swap p))
    (lp .fst , least-transfer w (Reach α p) (Reach α (swap p))
                 (reach-flip α p) (reach-flip α (swap p))
                 (lp .fst) (lp .snd))
    (leastOf w lem (Reach α (swap p)) (reach-ne α t (swap p))))
  where
  lp = leastOf w lem (Reach α p) (reach-ne α t p)

-- =====================================================================
-- PART 3.  THE REFUTATION.
-- =====================================================================

-- A symmetric pairing is injective only if the carrier is a
-- proposition.
item1-inj→prop : (α : S) (w : SWO ⟪ α ⟫) (t : ∥ sq α ∥₁)
               → ((u v : ⟪ α ⟫ × ⟪ α ⟫)
                  → item1-h α w t u ≡ item1-h α w t v → u ≡ v)
               → (a b : ⟪ α ⟫) → a ≡ b
item1-inj→prop α w t hinj a b =
  cong fst (hinj (a , b) (b , a) (item1-symmetric α w t (a , b)))

-- The carrier of a set that has omega and the successor of omega as
-- members is not a proposition.
two-members : (α : S) → ⟨ ω ∈ˢ α ⟩ → ⟨ sucV ω ∈ˢ α ⟩
            → ((a b : ⟪ α ⟫) → a ≡ b) → Empty.⊥
two-members α ω∈α sω∈α collapse =
  ∈-irrefl ω (subst (λ z → ⟨ ω ∈ˢ z ⟩) (sym eq) (self∈sucV ω))
  where
  m = fiber α ω∈α
  n = fiber α sω∈α
  eq : ω ≡ sucV ω
  eq = sym (m .snd) ∙ cong ⟪ α ⟫↪ (collapse (m .fst) (n .fst)) ∙ n .snd

-- ITEM 1 IS REFUTED.  Its map exists, it is canonical, and it is never
-- injective where the carrier holds two ordinals.
item1-refuted : (α : S) (w : SWO ⟪ α ⟫) → ⟨ ω ∈ˢ α ⟩ → ⟨ sucV ω ∈ˢ α ⟩
              → (t : ∥ sq α ∥₁)
              → ((u v : ⟪ α ⟫ × ⟪ α ⟫)
                 → item1-h α w t u ≡ item1-h α w t v → u ≡ v)
              → Empty.⊥
item1-refuted α w ω∈α sω∈α t hinj =
  two-members α ω∈α sω∈α (item1-inj→prop α w t hinj)

-- THE SAME, WITH THE BAND'S OWN HYPOTHESES.  The band is
-- `[LJ-1.332]`'s: an ordinal above omega, closed under successors, that
-- is not `Init` (agents/tasks/LJ-1-332/ProbeLJ1332A.agda:196-204).  Its
-- first three rows already supply the two members, so the refutation
-- needs neither the fourth row nor the order type of the site.
item1-refuted-in-band : (α : S) → IsOrd α → ⟨ ω ∈ˢ α ⟩
                      → ((γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩)
                      → (w : SWO ⟪ α ⟫) (t : ∥ sq α ∥₁)
                      → ((u v : ⟪ α ⟫ × ⟪ α ⟫)
                         → item1-h α w t u ≡ item1-h α w t v → u ≡ v)
                      → Empty.⊥
item1-refuted-in-band α _ ω∈α closed w t hinj =
  item1-refuted α w ω∈α (closed ω ω∈α) t hinj

-- THE TRUNCATION IS NOT THE CAUSE (C-56).  The same collapse happens
-- with an untruncated witness in hand, so the assembly is not paying
-- for the truncation.
control-untruncated-collapses : (α : S) (w : SWO ⟪ α ⟫) (s : sq α)
                              → (p : ⟪ α ⟫ × ⟪ α ⟫)
                              → item1-h α w ∣ s ∣₁ p
                              ≡ item1-h α w ∣ s ∣₁ (swap p)
control-untruncated-collapses α w s = item1-symmetric α w ∣ s ∣₁

-- =====================================================================
-- PART 4.  HOW WIDE THIS REACHES, AND WHERE IT STOPS (C-36, C-42).
--
--   The well-order plays no part.  Every map that reads the reachable
--   set and nothing else is symmetric, and `leastOf` is one such
--   reader.  I name that family and I claim nothing outside it.
-- =====================================================================

Reader : (α : S) → Type (ℓ-suc ℓ)
Reader α = (P : ⟪ α ⟫ → hProp ℓ)
         → ∥ Σ[ c ∈ ⟪ α ⟫ ] ⟨ P c ⟩ ∥₁ → ⟪ α ⟫

Respects : (α : S) → Reader α → Type (ℓ-suc ℓ)
Respects α G = (P Q : ⟪ α ⟫ → hProp ℓ)
             → ((x : ⟪ α ⟫) → ⟨ P x ⟩ → ⟨ Q x ⟩)
             → ((x : ⟪ α ⟫) → ⟨ Q x ⟩ → ⟨ P x ⟩)
             → (np : ∥ Σ[ c ∈ ⟪ α ⟫ ] ⟨ P c ⟩ ∥₁)
             → (nq : ∥ Σ[ c ∈ ⟪ α ⟫ ] ⟨ Q c ⟩ ∥₁)
             → G P np ≡ G Q nq

reader-symmetric : (α : S) (G : Reader α) → Respects α G
                 → (t : ∥ sq α ∥₁) (p : ⟪ α ⟫ × ⟪ α ⟫)
                 → G (Reach α p) (reach-ne α t p)
                 ≡ G (Reach α (swap p)) (reach-ne α t (swap p))
reader-symmetric α G resp t p =
  resp (Reach α p) (Reach α (swap p))
    (reach-flip α p) (reach-flip α (swap p))
    (reach-ne α t p) (reach-ne α t (swap p))

reader-refuted : (α : S) (G : Reader α) → Respects α G
               → ⟨ ω ∈ˢ α ⟩ → ⟨ sucV ω ∈ˢ α ⟩ → (t : ∥ sq α ∥₁)
               → ((u v : ⟪ α ⟫ × ⟪ α ⟫)
                  → G (Reach α u) (reach-ne α t u)
                  ≡ G (Reach α v) (reach-ne α t v) → u ≡ v)
               → Empty.⊥
reader-refuted α G resp ω∈α sω∈α t hinj =
  two-members α ω∈α sω∈α
    (λ a b → cong fst
      (hinj (a , b) (b , a) (reader-symmetric α G resp t (a , b))))

-- =====================================================================
-- PART 5.  THE BRIEF'S PREMISE: OMEGA TIMES TWO.
--
--   `ω · 2` is `+ω ω` in this tree's arithmetic
--   (src/L/Ordinal/StageArith.lagda.md:40-42, and the retired route
--   used the same reading at
--   agents/tasks/archive/L3-32-T90/l3.32-t90-report.md:98).
--
--   MEASURED HERE: rows 1 and 2 of the band, and the two members that
--   PART 3 needs.  NOT MEASURED HERE: row 3 (successor closure) and row
--   4 (the failure of `Init`).  `+ω` is opaque by R-38 and its five
--   exported facts eliminate no membership, so no term of mine can
--   reach row 3 without unsealing the union.
-- =====================================================================

ω2 : S
ω2 = +ω ω

ω2-ord : IsOrd ω2
ω2-ord = +ω-ord ω ω-ord

ω∈ω2 : ⟨ ω ∈ˢ ω2 ⟩
ω∈ω2 = +ω-mem ω

sucω∈ω2 : ⟨ sucV ω ∈ˢ ω2 ⟩
sucω∈ω2 = +ω-iter 1 ω

-- ITEM 1 REFUTED AT THE DIGEST'S OWN ORDINAL, with no hypothesis about
-- the band beyond the truncated supply.
item1-refuted-at-ω2 : (w : SWO ⟪ ω2 ⟫) (t : ∥ sq ω2 ∥₁)
                    → ((u v : ⟪ ω2 ⟫ × ⟪ ω2 ⟫)
                       → item1-h ω2 w t u ≡ item1-h ω2 w t v → u ≡ v)
                    → Empty.⊥
item1-refuted-at-ω2 w t hinj = item1-refuted ω2 w ω∈ω2 sucω∈ω2 t hinj

-- =====================================================================
-- PART 6.  NEGATIVE CONTROLS.
--
--   Each control was applied, run and reverted.  Nothing typechecks
--   this file once the task closes, so each one is recorded here with
--   the error Agda printed.  The report quotes them.  ALL FIVE MEASURE.
--
-- CONTROL 1.  IS THE FLIP DOING THE WORK?  I offered the SAME witness
--   at the flipped pair, at line 120:
--       reach-flip α p c = PT.map (λ { (s , e) → s , e })
--   Agda refused in 2 s:
--       error: [MismatchedProjectionsError]
--       The projections fst and snd do not match
--       when checking that the expression e has type
--       s .fst (swap p) ≡ c
--   MEASURED: the two reachable sets are not the same by triviality.
--   `flip-sq` is what identifies them.
--
-- CONTROL 2.  WHAT DOES THE REFUTATION REST ON?  I made `swap` a
--   non-involution, `swap (x , y) = (x , x)`, at line 107.  Agda
--   refused in 2 s, inside `flip-sq`:
--       error: [MismatchedProjectionsError]
--       when checking that the expression
--       cong swap (finj (swap u) (swap v) e) has type u ≡ v
--   MEASURED: the refutation rests on `sq α` being closed under
--   precomposition with a PERMUTATION of the pair type, and on nothing
--   else.  No order and no decidable equality enter.
--
-- CONTROL 3.  ARE THE TWO MEMBERS DISTINCT TO THE MACHINE?  I offered
--   `ω∈ω2` where `⟨ sucV ω ∈ˢ ω2 ⟩` is wanted, at line 274.  Agda
--   refused in 2 s and printed the two presentations side by side:
--       error: [UnequalTerms]
--       (Lift ℕ) != (Σ ⟪ ⁅ ω , ⁅ ω ⁆s ⁆ ⟫ (λ r → ⟪ ⟪ ⁅ ω , ⁅ ω ⁆s ⁆ ⟫↪ r ⟫))
--       of type (Type ℓ)
--       when checking that the expression ω∈ω2 has type ⟨ sucV ω ∈ˢ ω2 ⟩
--   MEASURED: `ω` and `sucV ω` are two members and the refutation is
--   not vacuous.
--
-- CONTROL 4.  WHY MUST ITEM 1'S PREDICATE BE TRUNCATED?  I dropped the
--   truncation from `Reach`, at line 68.  Agda refused in 2 s:
--       error: [UnequalTerms]
--       Σ (sq α) (λ s → s .fst p ≡ c) !=< ∥ _A_36 ∥₁
--       when checking that the expression squash₁ has type
--       isOfHLevel 1 (Σ-syntax (sq α) (λ s → s .fst p ≡ c))
--   MEASURED: the untruncated reachable set is NOT a proposition, so
--   `leastOf` does not apply to it.  Item 1's canonicity comes from the
--   truncation, and the truncation is what makes the map blind to WHICH
--   witness supplied the value.  The same blindness is the flip.
--
-- CONTROL 5.  IS THE DIGEST'S RECIPE THE SAME SHAPE?  I stated the
--   greedy recipe, which reads the values already assigned, and offered
--   it as a `Reader`:
--       Greedy α = (p : ⟪ α ⟫ × ⟪ α ⟫)
--                → ((q : ⟪ α ⟫ × ⟪ α ⟫) → ⟪ α ⟫) → ⟪ α ⟫
--       greedy→reader : (α : S) → Greedy α → Reader α
--       greedy→reader α g = g
--   Agda refused in 2 s:
--       error: [UnequalTerms]
--       ⟪ α ⟫ → hProp ℓ !=< Σ ⟪ α ⟫ (λ _ → ⟪ α ⟫)
--       when checking that the expression g has type Reader α
--   MEASURED: the greedy recipe takes the PAIR first and a reader takes
--   the PREDICATE first.  They are different constructions, so the
--   digest's counterexample against the greedy one does not reach item
--   1.  THAT IS THE ESCAPE, IN ONE ERROR MESSAGE.
-- =====================================================================

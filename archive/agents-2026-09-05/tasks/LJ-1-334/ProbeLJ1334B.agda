{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.334 probe B.  It lands nothing.  It runs in agents/tasks/LJ-1-334/.
--
-- WHY THIS FILE EXISTS.  Probe A refutes item 1 when the reachable set
-- ranges over ALL of `sq α`.  `[LJ-1.321]` states item 1 over the
-- composites of ONE injection type, with the target member and the
-- inner pairing FIXED (agents/tasks/LJ-1-321/lj-1.321-report.md:309-315).
-- THAT FAMILY IS NOT CLOSED UNDER THE FLIP, and PART 1 measures it.  So
-- probe A does not reach `[LJ-1.321]`'s own reading.
--
-- THIS FILE REACHES IT.  The extra cost is one transposition, which the
-- excluded middle and `[LJ-1.319]`'s `carrier-set` supply.
--
-- PART 1 measures that probe A's flip does not act on the family.
-- PART 2 builds the transposition.
-- PART 3 refutes item 1 over any family closed under precomposition.
-- PART 4 shows `[LJ-1.321]`'s family is such a family, by `refl`.
-- PART 5 records the negative controls.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM; lowerLEM )

module LJ-1-334.ProbeLJ1334B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; isPropLeastOf; leastOf )
open import LJ-1-319.SqIsSet {ℓ} lem using ( carrier-set )
open import LJ-1-334.ProbeLJ1334A {ℓ} lem using ( swap; least-transfer; two-members )

open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )

-- =====================================================================
-- PART 1.  `[LJ-1.321]`'s FAMILY, AND THE FLIP DOES NOT ACT ON IT.
--
--   The family: an injection of the site's carrier into a fixed target,
--   composed with a fixed inner pairing `G`.  Only the injection
--   varies, which is exactly `[LJ-1.321]`'s wording 「some witness's
--   composite」.
-- =====================================================================

Inj : (α : S) (D : Type ℓ) → Type ℓ
Inj α D = Σ[ e ∈ (⟪ α ⟫ → D) ] ((x y : ⟪ α ⟫) → e x ≡ e y → x ≡ y)

compT : (α : S) (D : Type ℓ) (G : D × D → ⟪ α ⟫)
      → ((u v : D × D) → G u ≡ G v → u ≡ v)
      → Inj α D → sq α
compT α D G ginj (e , einj) = (λ p → G (e (p .fst) , e (p .snd))) , inj
  where
  inj : (u v : ⟪ α ⟫ × ⟪ α ⟫)
      → G (e (u .fst) , e (u .snd)) ≡ G (e (v .fst) , e (v .snd)) → u ≡ v
  inj u v q i =
    ( einj (u .fst) (v .fst) (cong fst r) i
    , einj (u .snd) (v .snd) (cong snd r) i )
    where
    r = ginj (e (u .fst) , e (u .snd)) (e (v .fst) , e (v .snd)) q

-- MEASURED: the family is closed under the flip only if the carrier is
-- a proposition.  So probe A's one-line argument does NOT reach
-- `[LJ-1.321]`'s reading, and this file is not redundant.
comp-not-flip-closed : (α : S) (D : Type ℓ) (G : D × D → ⟪ α ⟫)
                     → (ginj : (u v : D × D) → G u ≡ G v → u ≡ v)
                     → ((w : Inj α D) → Σ[ w' ∈ Inj α D ]
                          ((p : ⟪ α ⟫ × ⟪ α ⟫)
                           → compT α D G ginj w' .fst p
                           ≡ compT α D G ginj w .fst (swap p)))
                     → Inj α D → (a b : ⟪ α ⟫) → a ≡ b
comp-not-flip-closed α D G ginj fc w a b =
  w' .snd a b (pt a b ∙ sym (pt b b))
  where
  r = fc w
  w' = r .fst
  pt : (x y : ⟪ α ⟫) → w' .fst x ≡ w .fst y
  pt x y = cong fst (ginj (w' .fst x , w' .fst y) (w .fst y , w .fst x)
                          (r .snd (x , y)))

-- =====================================================================
-- PART 2.  THE TRANSPOSITION.
--
--   The carrier is a set (`[LJ-1.319]`, agents/tasks/LJ-1-319/SqIsSet.agda:30-32)
--   and the excluded middle lowers (src/Base/Classical.lagda.md:75-76),
--   so equality on the carrier is decidable.
-- =====================================================================

dec≡ : (α : S) (x y : ⟪ α ⟫) → (x ≡ y) ⊎ ((x ≡ y) → Empty.⊥)
dec≡ α x y = lowerLEM lem ((x ≡ y) , carrier-set α x y)

module Transp (α : S) (a b : ⟪ α ⟫) where

  τ0 : (x : ⟪ α ⟫) → (x ≡ a) ⊎ ((x ≡ a) → Empty.⊥)
     → (x ≡ b) ⊎ ((x ≡ b) → Empty.⊥) → ⟪ α ⟫
  τ0 x (inl _) _       = b
  τ0 x (inr _) (inl _) = a
  τ0 x (inr _) (inr _) = x

  τ : ⟪ α ⟫ → ⟪ α ⟫
  τ x = τ0 x (dec≡ α x a) (dec≡ α x b)

  τ0-a : (d : (a ≡ a) ⊎ ((a ≡ a) → Empty.⊥))
       → (d' : (a ≡ b) ⊎ ((a ≡ b) → Empty.⊥)) → τ0 a d d' ≡ b
  τ0-a (inl _) _ = refl
  τ0-a (inr h) _ = Empty.rec (h refl)

  τ-a : τ a ≡ b
  τ-a = τ0-a (dec≡ α a a) (dec≡ α a b)

  τ0-b : (d : (b ≡ a) ⊎ ((b ≡ a) → Empty.⊥))
       → (d' : (b ≡ b) ⊎ ((b ≡ b) → Empty.⊥)) → τ0 b d d' ≡ a
  τ0-b (inl e) _       = e
  τ0-b (inr _) (inl _) = refl
  τ0-b (inr _) (inr h) = Empty.rec (h refl)

  τ-b : τ b ≡ a
  τ-b = τ0-b (dec≡ α b a) (dec≡ α b b)

  τ0-inj : (x y : ⟪ α ⟫)
         → (dx : (x ≡ a) ⊎ ((x ≡ a) → Empty.⊥))
         → (dx' : (x ≡ b) ⊎ ((x ≡ b) → Empty.⊥))
         → (dy : (y ≡ a) ⊎ ((y ≡ a) → Empty.⊥))
         → (dy' : (y ≡ b) ⊎ ((y ≡ b) → Empty.⊥))
         → τ0 x dx dx' ≡ τ0 y dy dy' → x ≡ y
  τ0-inj x y (inl ex) _         (inl ey) _         q = ex ∙ sym ey
  τ0-inj x y (inl ex) _         (inr _)  (inl ey') q = ex ∙ sym q ∙ sym ey'
  τ0-inj x y (inl ex) _         (inr _)  (inr hy') q = Empty.rec (hy' (sym q))
  τ0-inj x y (inr _)  (inl ex') (inl ey) _         q = ex' ∙ sym q ∙ sym ey
  τ0-inj x y (inr _)  (inl ex') (inr _)  (inl ey') q = ex' ∙ sym ey'
  τ0-inj x y (inr _)  (inl ex') (inr hy) (inr _)   q = Empty.rec (hy (sym q))
  τ0-inj x y (inr _)  (inr hx') (inl ey) _         q = Empty.rec (hx' q)
  τ0-inj x y (inr hx) (inr _)   (inr _)  (inl ey') q = Empty.rec (hx q)
  τ0-inj x y (inr _)  (inr _)   (inr _)  (inr _)   q = q

  τ-inj : (x y : ⟪ α ⟫) → τ x ≡ τ y → x ≡ y
  τ-inj x y = τ0-inj x y (dec≡ α x a) (dec≡ α x b) (dec≡ α y a) (dec≡ α y b)

-- =====================================================================
-- PART 3.  ITEM 1 REFUTED OVER ANY PRECOMPOSITION-CLOSED FAMILY.
-- =====================================================================

-- The one structure the refutation needs: precomposing the witness with
-- a self-injection of the carrier stays in the family, and moves the
-- value the way the injection moves the pair.
Precomp : (α : S) (W : Type ℓ) (T : W → sq α) → Type ℓ
Precomp α W T = (σ : ⟪ α ⟫ → ⟪ α ⟫) → ((x y : ⟪ α ⟫) → σ x ≡ σ y → x ≡ y)
              → (w : W) → Σ[ w' ∈ W ]
                  ((x y : ⟪ α ⟫) → T w' .fst (x , y) ≡ T w .fst (σ x , σ y))

ReachW : (α : S) (W : Type ℓ) (T : W → sq α)
       → ⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫ → hProp ℓ
ReachW α W T p c = ∥ Σ[ w ∈ W ] (T w .fst p ≡ c) ∥₁ , squash₁

reachW-ne : (α : S) (W : Type ℓ) (T : W → sq α) → ∥ W ∥₁
          → (p : ⟪ α ⟫ × ⟪ α ⟫) → ∥ Σ[ c ∈ ⟪ α ⟫ ] ⟨ ReachW α W T p c ⟩ ∥₁
reachW-ne α W T t p = PT.map (λ w → T w .fst p , ∣ w , refl ∣₁) t

-- ITEM 1, over the family.
itemW-h : (α : S) (W : Type ℓ) (T : W → sq α) → SWO ⟪ α ⟫ → ∥ W ∥₁
        → ⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫
itemW-h α W T o t p = leastOf o lem (ReachW α W T p) (reachW-ne α W T t p) .fst

-- THE TRANSPOSITION CARRIES THE COLLAPSE.
reachW-swap : (α : S) (W : Type ℓ) (T : W → sq α) → Precomp α W T
            → (a b c : ⟪ α ⟫)
            → ⟨ ReachW α W T (b , a) c ⟩ → ⟨ ReachW α W T (a , b) c ⟩
reachW-swap α W T pc a b c = PT.map step
  where
  open Transp α a b
  r : (w : W) → Σ[ w' ∈ W ]
        ((x y : ⟪ α ⟫) → T w' .fst (x , y) ≡ T w .fst (τ x , τ y))
  r = pc τ τ-inj
  step : Σ[ w ∈ W ] (T w .fst (b , a) ≡ c)
       → Σ[ w ∈ W ] (T w .fst (a , b) ≡ c)
  step (w , e) = r w .fst ,
    (r w .snd a b ∙ cong₂ (λ u v → T w .fst (u , v)) τ-a τ-b ∙ e)

itemW-symmetric : (α : S) (W : Type ℓ) (T : W → sq α) → Precomp α W T
                → (o : SWO ⟪ α ⟫) (t : ∥ W ∥₁) (a b : ⟪ α ⟫)
                → itemW-h α W T o t (a , b) ≡ itemW-h α W T o t (b , a)
itemW-symmetric α W T pc o t a b = cong fst
  (isPropLeastOf o (ReachW α W T (b , a))
    (lp .fst , least-transfer o (ReachW α W T (a , b)) (ReachW α W T (b , a))
                 (reachW-swap α W T pc b a) (reachW-swap α W T pc a b)
                 (lp .fst) (lp .snd))
    (leastOf o lem (ReachW α W T (b , a)) (reachW-ne α W T t (b , a))))
  where
  lp = leastOf o lem (ReachW α W T (a , b)) (reachW-ne α W T t (a , b))

itemW-refuted : (α : S) (W : Type ℓ) (T : W → sq α) → Precomp α W T
              → (o : SWO ⟪ α ⟫) → ⟨ ω ∈ˢ α ⟩ → ⟨ sucV ω ∈ˢ α ⟩ → (t : ∥ W ∥₁)
              → ((u v : ⟪ α ⟫ × ⟪ α ⟫)
                 → itemW-h α W T o t u ≡ itemW-h α W T o t v → u ≡ v)
              → Empty.⊥
itemW-refuted α W T pc o ω∈α sω∈α t hinj =
  two-members α ω∈α sω∈α
    (λ a b → cong fst
      (hinj (a , b) (b , a) (itemW-symmetric α W T pc o t a b)))

-- =====================================================================
-- PART 4.  `[LJ-1.321]`'s FAMILY IS PRECOMPOSITION CLOSED, BY `refl`.
-- =====================================================================

comp-precomp : (α : S) (D : Type ℓ) (G : D × D → ⟪ α ⟫)
             → (ginj : (u v : D × D) → G u ≡ G v → u ≡ v)
             → Precomp α (Inj α D) (compT α D G ginj)
comp-precomp α D G ginj σ σinj (e , einj) =
  ( (λ x → e (σ x)) , (λ x y q → σinj x y (einj (σ x) (σ y) q)) )
  , (λ x y → refl)

-- ITEM 1 REFUTED AT `[LJ-1.321]`'s OWN READING.
item1-refuted-composites : (α : S) (D : Type ℓ) (G : D × D → ⟪ α ⟫)
  → (ginj : (u v : D × D) → G u ≡ G v → u ≡ v)
  → (o : SWO ⟪ α ⟫) → ⟨ ω ∈ˢ α ⟩ → ⟨ sucV ω ∈ˢ α ⟩ → (t : ∥ Inj α D ∥₁)
  → ((u v : ⟪ α ⟫ × ⟪ α ⟫)
     → itemW-h α (Inj α D) (compT α D G ginj) o t u
     ≡ itemW-h α (Inj α D) (compT α D G ginj) o t v → u ≡ v)
  → Empty.⊥
item1-refuted-composites α D G ginj o ω∈α sω∈α t hinj =
  itemW-refuted α (Inj α D) (compT α D G ginj)
    (comp-precomp α D G ginj) o ω∈α sω∈α t hinj

-- =====================================================================
-- PART 5.  NEGATIVE CONTROLS.
--
--   Each control was applied, run and reverted.  Nothing typechecks
--   this file once the task closes.  ALL THREE MEASURE.  The long type
--   printout in each message is the carrier's own presentation, and it
--   is cut here after the line that names the mismatch.
--
-- CONTROL 6.  IS THE TRANSPOSITION LOAD BEARING?  I kept the
--   precomposition but dropped its two facts, at line 188:
--       ... ∙ cong₂ (λ u v → T w .fst (u , v)) refl refl ∙ e
--   Agda refused in 2 s:
--       error: [UnequalTerms]
--       b != τ0 a (fromLifted lem ((a ≡ a) , carrier-set α a a) ...)
--                 (dec≡ α a b)
--   MEASURED: precomposition alone moves nothing.  `τ-a` and `τ-b` are
--   what carry the value from the flipped pair to this one.
--
-- CONTROL 7.  IS THE FAMILY FLIP CLOSED AFTER ALL?  I offered the same
--   witness at the flipped pair:
--       comp-flip-closed α D G ginj w = w , λ p → refl
--   Agda refused in 2 s:
--       error: [MismatchedProjectionsError]
--       The projections fst and snd do not match
--       when checking that the expression refl has type
--       compT α D G ginj w .fst p ≡ compT α D G ginj w .fst (swap p)
--   MEASURED, with `comp-not-flip-closed` above: probe A's flip does
--   NOT act on `[LJ-1.321]`'s family, so this file is not redundant.
--
-- CONTROL 8.  WHY MUST THE PRECOMPOSED MAP BE INJECTIVE?  I dropped
--   `σinj` from `comp-precomp`, at line 220:
--       ( (λ x → e (σ x)) , (λ x y q → einj (σ x) (σ y) q) )
--   Agda refused in 2 s:
--       error: [UnequalTerms]
--       σ x != x of type ⟪ α ⟫
--   MEASURED: the family is closed under precomposition with an
--   INJECTIVE self-map only.  A transposition is such a map, and that
--   is why the excluded middle is spent here and not in probe A.
-- =====================================================================

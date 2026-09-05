{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.330 probe A.  It lands nothing.  It runs in agents/tasks/LJ-1-330/.
--
-- THE BRIEF ASKS: is there a CANONICAL element of `sq α` at a non-initial
-- ordinal α?  Its premise is「a non-initial α has an INITIAL ordinal below it
-- of the same cardinality, and a canonical bijection to it」.
--
-- PART 1 refutes two halves of that premise by machine.
-- PART 2 corrects the transport shape: a BIJECTION is not needed.  TWO
--        injections are enough, and the back leg is free.
-- PART 3 re-derives the free back leg, `ord-emb`.
-- PART 4 builds the canonical square law at every SUCCESSOR ordinal, from
--        the delivered absorption `ShiftAbs.shift↪`.  No truncation, no
--        choice, no well-order on a function type.
-- PART 5 instantiates it at `sucV ω` and `sucV (sucV ω)`, two non-initial
--        ordinals, and refutes `Init` at the first of them.
-- PART 6 records the three negative controls and what each one named.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-330.ProbeLJ1330A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( ω-ord; suc-ord; #∈ω )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init )
open import L.InjChain {ℓ} lem using ( squareω )
open import L.Absorption {ℓ} lem using ( module ShiftAbs )
open import L.Cardinal {ℓ} lem using ( _↪_ )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV; #_ )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )

-- =====================================================================
-- PART 1.  THE BRIEF'S PREMISE, TWO HALVES REFUTED BY MACHINE.
--
--   `Init α` demands STRICT membership `⟨ ω ∈ˢ α ⟩`
--   (src/L/Ordinal/SquareLaw.lagda.md:693-699).  So `ω` is not initial,
--   and no initial ordinal sits at or below the countable band.  The
--   third row, closure under successors, refutes `Init` at every
--   successor ordinal.
-- =====================================================================

no-Init-ω : Init ω → Empty.⊥
no-Init-ω i = ∈-irrefl ω (fst (snd i))

-- Every successor ordinal fails the third row: `sucV γ ∈ˢ sucV γ`.
no-Init-suc : (γ : S) → Init (sucV γ) → Empty.⊥
no-Init-suc γ i = ∈-irrefl (sucV γ) (fst (snd (snd i)) γ (self∈sucV γ))

no-Init-sucω : Init (sucV ω) → Empty.⊥
no-Init-sucω = no-Init-suc ω

-- =====================================================================
-- PART 2.  THE TRANSPORT, AND THE BRIEF ASKS FOR TOO MUCH.
--
--   The brief asks for a bijection `⟪ α ⟫ ≃ ⟪ init α ⟫`.  The square law
--   does not need one.  Two injections, in the two directions, carry the
--   pairing function across.  This matters because ONE of the two legs
--   is free at every ordinal, so the whole obligation is a single
--   untruncated injection.
-- =====================================================================

transport-sq : (α δ : S) → ⟪ α ⟫ ↪ ⟪ δ ⟫ → ⟪ δ ⟫ ↪ ⟪ α ⟫ → sq δ → sq α
transport-sq α δ (f , finj) (g , ginj) (p , pinj) = h , hinj
  where
  h : ⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫
  h (x , y) = g (p (f x , f y))

  hinj : (u v : ⟪ α ⟫ × ⟪ α ⟫) → h u ≡ h v → u ≡ v
  hinj (x , y) (x' , y') e i = finj x x' (cong fst r) i , finj y y' (cong snd r) i
    where
    r : (f x , f y) ≡ (f x' , f y')
    r = pinj (f x , f y) (f x' , f y') (ginj (p (f x , f y)) (p (f x' , f y')) e)

-- =====================================================================
-- PART 3.  THE FREE LEG, re-derived (C-44).
--
--   `src/L/BoundedSubset.lagda.md:1370-1379`, `Devlin55.ord-emb`.  A
--   member of an ordinal embeds its index.  It is compiled here so that
--   this probe never quotes a term it did not check.
-- =====================================================================

ord-emb : (a b : S) → IsOrd b → ⟨ a ∈ˢ b ⟩ → ⟪ a ⟫ ↪ ⟪ b ⟫
ord-emb a b ob a∈b = f , inj
  where
  f : ⟪ a ⟫ → ⟪ b ⟫
  f m = fiber b {x = ⟪ a ⟫↪ m} (ob .fst (member a m) a∈b) .fst

  inj : (m n : ⟪ a ⟫) → f m ≡ f n → m ≡ n
  inj m n e = ↪-inj {a = a}
    (sym (fiber b {x = ⟪ a ⟫↪ m} (ob .fst (member a m) a∈b) .snd)
      ∙ cong (⟪ b ⟫↪) e
      ∙ fiber b {x = ⟪ a ⟫↪ n} (ob .fst (member a n) a∈b) .snd)

-- =====================================================================
-- PART 4.  THE CANONICAL SQUARE LAW AT EVERY SUCCESSOR ORDINAL.
--
--   The hard leg at a successor is DELIVERED and UNTRUNCATED:
--   `ShiftAbs.shift↪ : ⟪ sucV γ ⟫ ↪ ⟪ γ ⟫`,
--   src/L/Absorption.lagda.md:188-190.  Part 2 supplies the transport and
--   Part 3 the free back leg.  Nothing here selects, and nothing here is
--   truncated.
-- =====================================================================

sq-suc : (γ : S) → IsOrd γ → (⟨ γ ∈ˢ ω ⟩ → Empty.⊥)
       → ((k : ℕ) → ⟨ (# k) ∈ˢ γ ⟩)
       → sq γ → sq (sucV γ)
sq-suc γ oγ γ∉ω numerals s =
  transport-sq (sucV γ) γ SA.shift↪
    (ord-emb γ (sucV γ) (suc-ord oγ) (self∈sucV γ)) s
  where
  module SA = ShiftAbs γ oγ γ∉ω numerals

-- The two side conditions come from `ω ∈ˢ γ` alone, which is the
-- descent's own infinity hypothesis.
sq-suc-inf : (γ : S) → IsOrd γ → ⟨ ω ∈ˢ γ ⟩ → sq γ → sq (sucV γ)
sq-suc-inf γ oγ ω∈γ s = sq-suc γ oγ γ∉ω numerals s
  where
  γ∉ω : ⟨ γ ∈ˢ ω ⟩ → Empty.⊥
  γ∉ω γ∈ω = ∈-irrefl ω (ω-ord .fst ω∈γ γ∈ω)

  numerals : (k : ℕ) → ⟨ (# k) ∈ˢ γ ⟩
  numerals k = oγ .fst (#∈ω k) ω∈γ

-- =====================================================================
-- PART 5.  TWO NON-INITIAL SITES, WITH CANONICAL ELEMENTS.
--
--   `squareω` is the delivered canonical element at ω
--   (src/L/InjChain.lagda.md:184-185).  Two successor steps carry it to
--   two ordinals that `Init` refutes.
-- =====================================================================

-- At omega itself `sq-suc-inf` does not apply, because its infinity
-- hypothesis would read `⟨ ω ∈ˢ ω ⟩`.  The two side conditions are
-- delivered directly instead.
square-sucω : sq (sucV ω)
square-sucω = sq-suc ω ω-ord (∈-irrefl ω) #∈ω squareω

-- From the first successor upward `sq-suc-inf` applies, and the chain
-- runs to every finite successor of omega.
square-sucsucω : sq (sucV (sucV ω))
square-sucsucω =
  sq-suc-inf (sucV ω) (suc-ord ω-ord) (self∈sucV ω) square-sucω

-- =====================================================================
-- PART 6.  THE NEGATIVE CONTROLS.  Each one was applied, run and
-- reverted.  They are recorded here because nothing typechecks this file
-- once the task closes.
--
--   CONTROL 1, ON THE TRUNCATION.  Substitute the truncated injection
--   where `transport-sq` takes the honest one:
--
--     control1 : (α δ : S) → ⟪ δ ⟫ ↪ ⟪ α ⟫ → sq δ
--              → ∥ ⟪ α ⟫ ↪ ⟪ δ ⟫ ∥₁ → sq α
--     control1 α δ back s t = transport-sq α δ t back s
--
--   Agda refused:
--     error: [UnequalTerms]
--     ∥ ⟪ α ⟫ ↪ ⟪ δ ⟫ ∥₁ !=<
--     (Σ (⟪ α ⟫ → ⟪ δ ⟫) (λ f → (x y : ⟪ α ⟫) → f x ≡ f y → x ≡ y))
--     when checking that the expression t has type ⟪ α ⟫ ↪ ⟪ δ ⟫
--
--   CONTROL 2, ON THE ELIMINATION.  Try to eliminate the truncation:
--
--     control2 α δ back s t =
--       PT.rec (λ x y → refl) (λ f → transport-sq α δ f back s) t
--
--   Agda refused on the propositionality argument:
--     error: [UnequalTerms]
--     x != y of type
--     Σ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫)
--     (λ f → (x₁ y₁ : ⟪ α ⟫ × ⟪ α ⟫) → f x₁ ≡ f y₁ → x₁ ≡ y₁)
--     when checking that the expression refl has type x ≡ y
--
--   So the target is not a proposition, and the two arbitrary pairing
--   functions are what Agda names.
--
--   CONTROL 3, ON THE SUCCESSOR STEP.  Replace `SA.shift↪` by the free
--   embedding, asked for in the direction it cannot go:
--
--     control3 : (γ : S) → IsOrd γ → sq γ → sq (sucV γ)
--     control3 γ oγ s =
--       transport-sq (sucV γ) γ (ord-emb (sucV γ) γ oγ (self∈sucV γ))
--         (ord-emb γ (sucV γ) (suc-ord oγ) (self∈sucV γ)) s
--
--   Agda demanded a premise that `∈-irrefl` refutes:
--     when checking that the expression self∈sucV γ has type
--     ⟨ sucV γ ∈ˢ γ ⟩
--
--   So absorption carries the WHOLE content of the successor step.
-- =====================================================================

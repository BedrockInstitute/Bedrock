{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.169 probe A.  `powIter`, the last term with no provenance.
--
-- CRITERIA, FIXED BEFORE THE FIRST `agda` INVOCATION (D-1), and they
-- are the report's:
--   wall clock  10 minutes per agda invocation, GHCRTS="-A64m -I0 -M8g",
--               ONE process, cap NEVER raised.
--   the target  GO at or below 80 in-fence lines for `powIter` at a
--               general `δ`.  NO-GO above, or if the rank accounting
--               needs a fact nothing supplies, and then I NAME the
--               fact and price it.
--   counting    non-blank, non-comment lines, the convention
--               `[LJ-1.167]` re-derived and checked
--               (`agents/tasks/LJ-1-167/lj-1.167-report.md:30-33`).
--
-- WHAT THIS FILE MEASURES, and it is three things:
--
--   BLOCK 1  THE ASSEMBLY.  One lemma serves BOTH the finite-iterate
--            form and the ω-block form of `powIter`.  It shows the
--            gap is exactly ONE fact and gives its type.
--
--   BLOCK 2  THE OBSTRUCTION, MEASURED.  This coding's codes are
--            nested Kuratowski pairs (`src/FOL/Coding.lagda.md:124-136`,
--            `src/L/Coding/InL.lagda.md:252-253`).  The tree's only
--            pairing closure shifts the stage by TWO for ONE pair
--            (`pr∈Lset-suc`, `src/L/Axioms/Basic.lagda.md:596-599`).
--            So the stage a code needs GROWS with the code's nesting
--            depth.  This block proves that growth and proves that
--            `+ω` absorbs every depth at once.
--
--   BLOCK 3  THE GAP, NAMED AS A TYPE.  The one fact nothing supplies.
--
-- P-i [F] is obeyed: every lemma with an implicit set index applied at
-- a concrete argument gets the index EXPLICITLY.
--
-- No master is edited.  This file is a probe and lives beside the
-- report, per D-1 and `AGENTS.md`.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-169.ProbeLJ1169A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( Lset; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ-inv; Lset-mono )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Axioms.Basic {ℓ} using ( Lset-suc; pr∈Lset-suc )
open import L.Ordinal.StageArith {ℓ} lem
  using ( sucIter; +ω; +ω-iter; closedω; boundCloses )

open import Cubical.Data.Sigma using ( _,_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- BLOCK 1: THE ASSEMBLY.
--
-- `Describes σ y` is "the definable power of `y` is a definable subset
-- of the stage `Lset σ`".  It is `𝒟ₒ-intro`'s own premise
-- (`src/L/Constructible.lagda.md:301-304`) at the value `𝒟ₒ y`.
--
-- Given it, `𝒟ₒ y` is IN the tower one stage up, by the successor
-- identity `Lset-suc` (`src/L/Axioms/Basic.lagda.md:196`).  Nothing
-- about `δ`, about ordinality or about limits is used anywhere here.
-- =====================================================================

Describes : S → S → Type (ℓ-suc ℓ)
Describes σ y =
  ∥ Σ[ ψ ∈ Formula ⟪ Lset σ ⟫ 1 ] (DefOf.defSet (Lset σ) ψ ≡ 𝒟ₒ y) ∥₁

defPow-at : (σ y : S) → Describes σ y → ⟨ 𝒟ₒ y ∈ˢ Lset (sucV σ) ⟩
defPow-at σ y h = subst (λ w → ⟨ 𝒟ₒ y ∈ˢ w ⟩) (sym (Lset-suc σ))
  (𝒟ₒ-intro (Lset σ) (𝒟ₒ y) h)

-- The brief's statement, from the one fact.  `sucIter (suc k) δ` is
-- `sucV (sucIter k δ)` by the definition at
-- `src/L/Ordinal/StageArith.lagda.md:34-36`, so no arithmetic is spent.
powIter-from :
    ((δ y : S) → ⟨ y ∈ˢ Lset δ ⟩ → ∥ Σ[ k ∈ ℕ ] Describes (sucIter k δ) y ∥₁)
  → (δ y : S) → ⟨ y ∈ˢ Lset δ ⟩
  → ∥ Σ[ k ∈ ℕ ] ⟨ 𝒟ₒ y ∈ˢ Lset (sucIter k δ) ⟩ ∥₁
powIter-from h δ y hy =
  PT.map (λ { (k , d) → suc k , defPow-at (sucIter k δ) y d }) (h δ y hy)

-- The SAME fact gives the ω-block form, and this is the form the
-- delivered kit was built for
-- (`src/L/Ordinal/StageArith.lagda.md:84-85`).
powBlock-from :
    ((δ y : S) → ⟨ y ∈ˢ Lset δ ⟩ → ∥ Σ[ k ∈ ℕ ] Describes (sucIter k δ) y ∥₁)
  → (δ y : S) → ⟨ y ∈ˢ Lset δ ⟩ → ⟨ 𝒟ₒ y ∈ˢ Lset (+ω δ) ⟩
powBlock-from h δ y hy = PT.rec (snd (𝒟ₒ y ∈ˢ Lset (+ω δ)))
  (λ { (k , d) → Lset-mono {α = +ω δ} {β = sucIter (suc k) δ}
         (+ω-iter (suc k) δ) {x = 𝒟ₒ y} (defPow-at (sucIter k δ) y d) })
  (h δ y hy)

-- And the consumer `[LJ-1.167]` named, straight off the ω-block form,
-- with `StageArith`'s own climb.  This is the first consumer that
-- module has ever had.
pow-closed :
    ((δ y : S) → ⟨ y ∈ˢ Lset δ ⟩ → ∥ Σ[ k ∈ ℕ ] Describes (sucIter k δ) y ∥₁)
  → (lam : S) → closedω lam
  → (δ y : S) → ⟨ δ ∈ˢ lam ⟩ → ⟨ y ∈ˢ Lset δ ⟩ → ⟨ 𝒟ₒ y ∈ˢ Lset lam ⟩
pow-closed h lam cl δ y δ∈ hy =
  boundCloses lam δ cl δ∈ (𝒟ₒ y) (powBlock-from h δ y hy)

-- THE FORM THIS TREE CAN ACTUALLY REACH, and BLOCK 2 is why.  Every
-- code over a carrier at `δ` lies in `Lset (+ω δ)`, so the description
-- can be READ at the ω-block itself.  The conclusion is then one stage
-- above the block, and the consumer pays `closedω` AND successor
-- closure, where the finite-iterate form would have paid successor
-- closure alone.
powAtBlock : (δ y : S) → Describes (+ω δ) y
           → ⟨ 𝒟ₒ y ∈ˢ Lset (sucV (+ω δ)) ⟩
powAtBlock δ y = defPow-at (+ω δ) y

pow-closed-suc :
    ((δ y : S) → ⟨ y ∈ˢ Lset δ ⟩ → Describes (+ω δ) y)
  → (lam : S) → closedω lam
  → ((d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  → (δ y : S) → ⟨ δ ∈ˢ lam ⟩ → ⟨ y ∈ˢ Lset δ ⟩ → ⟨ 𝒟ₒ y ∈ˢ Lset lam ⟩
pow-closed-suc h lam cl succλ δ y δ∈ hy =
  Lset-mono {α = lam} {β = sucV (+ω δ)}
    (succλ (+ω δ) (cl δ δ∈)) {x = 𝒟ₒ y} (powAtBlock δ y (h δ y hy))

-- =====================================================================
-- BLOCK 2: THE OBSTRUCTION, MEASURED.
--
-- A code is a nested Kuratowski pair.  `⌜ φ ∧̇ ψ ⌝ = mkTag 2 (pr ⌜ φ ⌝ ⌜ ψ ⌝)`
-- and `mkTag k x = pr (# k) x`, so ONE formula constructor costs TWO
-- `pr` applications (`src/FOL/Coding.lagda.md:124-136`), and `key`
-- wraps the whole code in one more (`src/L/Coding/InL.lagda.md:253`).
--
-- `prTower n x` is the cheapest witness of that shape: `n` nested
-- pairs over `x`.  `dbl n` counts the stages it costs.
-- =====================================================================

dbl : ℕ → ℕ
dbl zero    = zero
dbl (suc n) = suc (suc (dbl n))

prTower : ℕ → S → S
prTower zero    x = x
prTower (suc n) x = pr (prTower n x) (prTower n x)

-- TWO stages per pair, and the count is the nesting depth doubled.
-- `pr∈Lset-suc` is the tree's ONLY pairing closure that is not pinned
-- to `Lset ω` (`[LJ-1.166]` section 4.3, MEASURED), and it SHIFTS.
prTower-level : (n : ℕ) (σ x : S) → ⟨ x ∈ˢ Lset σ ⟩
              → ⟨ prTower n x ∈ˢ Lset (sucIter (dbl n) σ) ⟩
prTower-level zero    σ x h = h
prTower-level (suc n) σ x h =
  pr∈Lset-suc (sucIter (dbl n) σ) (prTower n x) (prTower n x)
    (prTower-level n σ x h) (prTower-level n σ x h)

-- And `+ω σ` absorbs EVERY depth at once, uniformly in `n`.  This is
-- the whole reason `StageArith` exists and it is used here for the
-- first time in the project.
prTower-ω : (n : ℕ) (σ x : S) → ⟨ x ∈ˢ Lset σ ⟩
          → ⟨ prTower n x ∈ˢ Lset (+ω σ) ⟩
prTower-ω n σ x h = Lset-mono {α = +ω σ} {β = sucIter (dbl n) σ}
  (+ω-iter (dbl n) σ) {x = prTower n x} (prTower-level n σ x h)

-- The reading, stated so it cannot be mistaken.  For a FIXED finite
-- iterate `sucIter k σ`, `prTower-level` gives the membership only for
-- the depths `n` with `dbl n` at or below `k`.  Nothing here proves a
-- lower bound, and the report marks that negative INFERRED.
prTower-at-k : (k : ℕ) (σ x : S) → ⟨ x ∈ˢ Lset σ ⟩
             → ⟨ prTower k x ∈ˢ Lset (sucIter (dbl k) σ) ⟩
prTower-at-k k = prTower-level k

-- =====================================================================
-- BLOCK 3: THE GAP, NAMED AS A TYPE.
--
-- `Describes` is the one fact nothing in `src/` supplies.  Unfolded,
-- it asks for ONE object-language formula over the stage's own
-- alphabet whose inner extension in `(Lset σ, ∈)` is `𝒟ₒ y`.
--
-- The tree HAS that formula for the class `L`: `DefAt`
-- (`src/L/Coding/Powerset.lagda.md:442-443`) with `DefAt-in` `:645`
-- and `DefAt-out` `:662`.  What it does NOT have is that formula read
-- INSIDE a stage, with every witness the two existentials of `DefAt`
-- reach held below that stage.  BLOCK 2 is why: the code witness is a
-- nested pair whose depth is the formula's, so the stage that holds
-- every witness is `+ω σ` and never `sucIter k σ`.
--
-- `DescribesL` is what the delivered `DefAt` gives, for contrast: an
-- `isL` statement with NO level in it at all.
-- =====================================================================

-- The two halves of the gap, separated, so a brief can fund them apart.
--   HALF 1  the SUBSET half: every definable subset of `y` is a
--           definable subset of the stage.  This is `DefOK`
--           (`src/L/Coding/Powerset.lagda.md:445-446`) in leveled form.
--   HALF 2  the MEMBERSHIP half: the whole of `𝒟ₒ y` is carved by ONE
--           formula of the stage.  This is the one BLOCK 2 obstructs.
SubsetHalf : S → S → Type (ℓ-suc ℓ)
SubsetHalf σ y = (x : S) → ⟨ x ∈ˢ 𝒟ₒ y ⟩ → ⟨ x ∈ˢ 𝒟ₒ (Lset σ) ⟩

-- HALF 1 reads straight into the tower, one stage up, by the successor
-- identity.  So the SUBSET half needs no level arithmetic of its own.
subsetHalf-reads : (σ y : S) → SubsetHalf σ y
                 → (x : S) → ⟨ x ∈ˢ 𝒟ₒ y ⟩ → ⟨ x ∈ˢ Lset (sucV σ) ⟩
subsetHalf-reads σ y sh x hx =
  subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (Lset-suc σ)) (sh x hx)

-- HALF 1 from the formula-level fact, which is what `relativize` and
-- `Relabel.liftFo` are for
-- (`src/FOL/Manipulation/Relativize.lagda.md:48`,
--  `src/FOL/Manipulation/Bounding.lagda.md:162`).  One formula in, one
-- formula out, per definable subset.  MEASURED: this half needs no
-- quantification over codes, so BLOCK 2 does not obstruct it.
subsetHalf-from : (σ y : S)
  → ((χ : Formula ⟪ y ⟫ 1)
       → ∥ Σ[ ψ ∈ Formula ⟪ Lset σ ⟫ 1 ]
             (DefOf.defSet (Lset σ) ψ ≡ DefOf.defSet y χ) ∥₁)
  → SubsetHalf σ y
subsetHalf-from σ y h x hx = PT.rec (snd (x ∈ˢ 𝒟ₒ (Lset σ)))
  (λ { (χ , qχ) → PT.rec (snd (x ∈ˢ 𝒟ₒ (Lset σ)))
    (λ { (ψ , qψ) → 𝒟ₒ-intro (Lset σ) x ∣ ψ , (qψ ∙ qχ) ∣₁ })
    (h χ) })
  (𝒟ₒ-inv y x hx)

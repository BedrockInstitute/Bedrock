{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.410] PROBE.  The descent, with the infinity conjunct OUT of
-- the predicate.  It runs in agents/tasks/LJ-1-410/ and lands nothing
-- in src/.
--
-- W3, FIRST: `nofin-at-selected`.  State step 4 alone, with the arrow
-- as a bare hypothesis, run it, and report its code lines before
-- writing the selection.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-410.Probe410 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; Lset )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.InjChain {ℓ} lem using ( finite-excl-ω )
open import L.Choice.Step {ℓ} lem using ( Mem; orderAt )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( IsLeast; leastOf )
open import L.Cardinal {ℓ} lem
  using ( _↪_; InjCode; IsCardinalL; module SiteBound )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω )
open import Cubical.Foundations.HLevels using ( isProp× )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- W3.  Step 4 alone.  The arrow is a bare hypothesis.  Generic in `κ`
-- and `δ`.  No numeral, no named cardinal except `ω`.
-- Rebuild of [LJ-1.398]'s `no-fin-descent` (Probe398.agda:213-220).
-- Nothing of Probe398 is imported.
-- =====================================================================

-- A member of an ordinal injects its index into the ordinal
-- ([LJ-1.390]'s `mem-incl`, from `member`, `fiber`, `↪-inj`).
mem-incl : (d k : V ℓ) → IsOrd d → ⟨ k ∈ d ⟩ → ⟪ k ⟫ ↪ ⟪ d ⟫
mem-incl d k od k∈d = ι , ι-inj
  where
  raise : (m : ⟪ k ⟫) → ⟨ ⟪ k ⟫↪ m ∈ d ⟩
  raise m = fst od (member k m) k∈d

  ι : ⟪ k ⟫ → ⟪ d ⟫
  ι m = fst (fiber d (raise m))

  ι-inj : (m n : ⟪ k ⟫) → ι m ≡ ι n → m ≡ n
  ι-inj m n e = ↪-inj {a = k}
    (sym (snd (fiber d (raise m)))
     ∙ cong (⟪ d ⟫↪) e
     ∙ snd (fiber d (raise n)))

-- Composition of two ambient injections.
comp-inj : {A B C : Type ℓ} → A ↪ B → B ↪ C → A ↪ C
comp-inj (f , injf) (g , injg) =
  (λ x → g (f x)) , λ x y e → injf x y (injg (f x) (f y) e)

-- Step 4 of the obligation, stated alone.  Membership of `δ` in `κ` is
-- the selected conjunct `Good°` will return; it is a hypothesis here
-- because `mem-ord` spends it to give `IsOrd (fst δ)`.
nofin-at-selected :
    (κ : S) (oκ : IsOrd (fst κ))
  → ⟨ ω ∈ˢ fst κ ⟩
  → (δ : S)
  → ⟨ fst δ ∈ fst κ ⟩
  → (⟪ fst κ ⟫ ↪ ⟪ fst δ ⟫)
  → ⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥
nofin-at-selected κ oκ ω∈κ δ δ∈κ down δ∈ω =
  let ω↪δ : ⟪ ω ⟫ ↪ ⟪ fst δ ⟫
      ω↪δ = comp-inj (mem-incl (fst κ) ω oκ ω∈κ) down
  in finite-excl-ω (fst δ) (mem-ord {A = fst κ} oκ (fst δ) δ∈κ) δ∈ω
       (λ t → fst ω↪δ t , fst ω↪δ t)
       (λ t u e → snd ω↪δ t u (cong fst e))

-- =====================================================================
-- `Good°`, two conjuncts.  Generic in `κ`.  No numeral, no named
-- cardinal.  The infinity conjunct is not here: it is recovered after
-- selection, by `nofin-at-selected`.
-- =====================================================================

module GoodDeg (κ : S) (oκ : IsOrd (fst κ)) where

  open SiteBound κ

  Good° : Mem (Lset β) → hProp (ℓ-suc ℓ)
  Good° δ =
    ( ⟨ fst (up δ) ∈ fst κ ⟩
    × ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) κ (up δ) ∥₁ )
    , isProp× (snd (fst (up δ) ∈ fst κ)) squash₁

  gooddeg-isProp : (δ : Mem (Lset β)) → isProp ⟨ Good° δ ⟩
  gooddeg-isProp δ = snd (Good° δ)

-- The non-emptiness a caller must inhabit to discharge
-- `sel-descent-nofin`.  It is NOT proved here.
Ne° : (κ : S) (oκ : IsOrd (fst κ)) → Type (ℓ-suc ℓ)
Ne° κ oκ = ∥ Σ[ δ ∈ Mem (Lset (SiteBound.β κ)) ]
              ⟨ GoodDeg.Good° κ oκ δ ⟩ ∥₁

-- What the band recursion's negative case actually holds, and what it
-- would have to prove.  Not inhabited.  Two gaps remain, both
-- placements.  Infinity of `δ` is not among them.
CallerNe° : (κ : S) (oκ : IsOrd (fst κ)) → Type (ℓ-suc ℓ)
CallerNe° κ oκ =
    (IsCardinalL κ → Empty.⊥)
  → ⟨ ω ∈ˢ fst κ ⟩
  → Ne° κ oκ

-- =====================================================================
-- THE OBLIGATION.  One two-conjunct selection, then [LJ-1.401]'s
-- `isPropInjCode` and a second `leastOf`, then [LJ-1.402]'s readback,
-- then step 4.  The two hypotheses are taken at the types [LJ-1.403]
-- used (Probe403.agda:82 and :83).  Nothing of Probe401, Probe402 or
-- Probe403 is imported.  The selection is rebuilt because the
-- predicate changed.
-- =====================================================================

module _
  (isPropInjCode : (F a b : S) → isProp (InjCode F a b))
  (sel-arrow : (F a b : S) → InjCode F a b → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫)
  where

  sel-descent-nofin :
      (κ : S) (oκ : IsOrd (fst κ)) → ⟨ ω ∈ˢ fst κ ⟩
    → (ne : Ne° κ oκ)
    → Σ[ δ ∈ S ] ( ⟨ fst δ ∈ fst κ ⟩
                 × (⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥)
                 × (⟪ fst κ ⟫ ↪ ⟪ fst δ ⟫) )
  sel-descent-nofin κ oκ ω∈κ ne = up δ-mem , mem , nofin , arrow
    where
    open SiteBound κ
    open GoodDeg κ oκ

    least° : Σ[ δ ∈ Mem (Lset β) ] IsLeast (orderAt β oβ) Good° δ
    least° = leastOf (orderAt β oβ) lem Good° ne

    δ-mem : Mem (Lset β)
    δ-mem = fst least°

    good : ⟨ Good° δ-mem ⟩
    good = fst (snd least°)

    mem : ⟨ fst (up δ-mem) ∈ fst κ ⟩
    mem = fst good

    code-ne : ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) κ (up δ-mem) ∥₁
    code-ne = snd good

    GoodCode : Mem (Lset β) → hProp (ℓ-suc ℓ)
    GoodCode F = InjCode (up F) κ (up δ-mem)
               , isPropInjCode (up F) κ (up δ-mem)

    chosen : Σ[ F ∈ Mem (Lset β) ] IsLeast (orderAt β oβ) GoodCode F
    chosen = leastOf (orderAt β oβ) lem GoodCode code-ne

    code : InjCode (up (fst chosen)) κ (up δ-mem)
    code = fst (snd chosen)

    arrow : ⟪ fst κ ⟫ ↪ ⟪ fst (up δ-mem) ⟫
    arrow = sel-arrow (up (fst chosen)) κ (up δ-mem) code

    nofin : ⟨ fst (up δ-mem) ∈ˢ ω ⟩ → Empty.⊥
    nofin = nofin-at-selected κ oκ ω∈κ (up δ-mem) mem arrow

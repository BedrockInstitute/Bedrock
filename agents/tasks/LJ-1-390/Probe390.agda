{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.390] PROBE.  The DESCENT route to the square law, built at
-- GENERIC δ and κ, and priced against the product route's `Leg1`.
-- It runs in agents/tasks/LJ-1-390/ and lands nothing.
--
-- The route composes four arrows and forms NO product of two L-sets:
--
--     ⟪δ⟫ × ⟪δ⟫  ↪  ⟪κ⟫ × ⟪κ⟫  ↪  ⟪κ⟫  ↪  ⟪δ⟫
--
--   PART 1  THE INCLUSION ARROW, DISCHARGED HERE.  κ ∈ δ with δ an
--           ordinal gives ⟪κ⟫ ↪ ⟪δ⟫ from `member`, `fiber` and
--           `↪-inj`.  It is the fourth arrow, it costs 12 code lines,
--           and for that reason it does NOT enter the residue.
--
--   PART 2  `descent-gives-sq`.  The composite, at generic δ and κ.
--           `code-untruncates` is spent at a := δ, b := κ, which is a
--           different instance of the SAME door `[LJ-1.386]` measured.
--
--   PART 3  `descent-owes`, the residue, and `descent-closes`, which
--           spends it by `∈-induction` over membership.
--
--   PART 4  THE CONSUMER'S OWN SHAPE, and the discharge fitted to it
--           with the L-certificate produced rather than assumed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import L.Constructible using ( IsOrd )

-- α₀ and oα₀ are the consumer's own module parameters, copied from
-- src/L/StageCardinal.lagda.md:16.  Nothing below assumes more of them.
module LJ-1-390.Probe390 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; Lset; isPropIsOrd )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init; via-col-square )
open import L.InjChain {ℓ} lem using ( squareω )
open import L.Choice.Step {ℓ} lem using ( Mem )
open import L.Cardinal {ℓ} lem
  using ( _↪_; InjCode; IsCardinalL; module SiteBound )

-- The two delivered terms of [LJ-1.386], imported and not copied, so
-- this measurement rests on the green term rather than on a re-typing.
open import LJ-1-386.Probe386 {ℓ} lem using ( code-untruncates; isL-ord )

open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.Data.Sigma using ( ΣPathP )
open import Cubical.Data.Sum using ( _⊎_ )
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- PART 1.  THE INCLUSION ARROW, AND IT IS NOT OWED.
--
--   A member of an ordinal is a subset of it, so its index type maps
--   in.  This is `via-col-square`'s own `pair-inj` pattern
--   (src/L/Ordinal/SquareLaw.lagda.md:947-951) at a different site.
-- =====================================================================

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

-- =====================================================================
-- PART 2.  THE DESCENT PAYOFF, UNTRUNCATED, IN TWO HALVES.
--
--   The exact analogue of `leg1-gives-sq`
--   (agents/tasks/LJ-1-386/Probe386.agda:294-302) on the other route.
--   It composes FOUR arrows where that one composes two, and it names
--   no product of two L-sets anywhere in its type or its body.
--
--   THE SPLIT IS NOT COSMETIC AND IT IS THE MEASUREMENT OF THIS TASK.
--   `descent-core` takes the descending arrow as a VARIABLE.
--   `descent-gives-sq` applies the door once, outside it.  Written as
--   ONE term, with `code-untruncates δ κ h` bound inside the `where`
--   that the injectivity proof reads, the same mathematics costs
--   175.42 s; in these two halves it costs 1.54 s.  Both numbers were
--   measured on 2026-08-19 under `-A64m -I0 -M8g`, and PART 5 records
--   the six control runs that isolate them.
-- =====================================================================

-- The composite, with the door held OUTSIDE as a variable.
descent-core : (δ κ : S)
             → ⟪ fst κ ⟫ ↪ ⟪ fst δ ⟫
             → sq (fst κ)
             → ⟪ fst δ ⟫ ↪ ⟪ fst κ ⟫
             → sq (fst δ)
descent-core δ κ incl (g , g-inj) down = f , f-inj
  where
  f : ⟪ fst δ ⟫ × ⟪ fst δ ⟫ → ⟪ fst δ ⟫
  f (x , y) = fst incl (g (fst down x , fst down y))

  f-inj : (p q : ⟪ fst δ ⟫ × ⟪ fst δ ⟫) → f p ≡ f q → p ≡ q
  f-inj (x₁ , y₁) (x₂ , y₂) e = ΣPathP (ex , ey)
    where
    -- ARROW 4 reflected, then ARROW 3.
    step : (fst down x₁ , fst down y₁) ≡ (fst down x₂ , fst down y₂)
    step = g-inj _ _ (snd incl _ _ e)

    ex : x₁ ≡ x₂
    ex = snd down x₁ x₂ (cong fst step)

    ey : y₁ ≡ y₂
    ey = snd down y₁ y₂ (cong snd step)

-- ARROWS 1 and 2.  The SAME door `[LJ-1.386]` measured, spent here at
-- a := δ and b := κ.  No product of two L-sets is formed anywhere.
descent-gives-sq : (δ κ : S)
                 → ⟪ fst κ ⟫ ↪ ⟪ fst δ ⟫
                 → sq (fst κ)
                 → ∥ Σ[ A ∈ Mem (Lset (SiteBound.β δ)) ]
                       InjCode (SiteBound.up δ A) δ κ ∥₁
                 → sq (fst δ)
descent-gives-sq δ κ incl sqκ h =
  descent-core δ κ incl sqκ (code-untruncates δ κ h)

-- =====================================================================
-- PART 3.  THE RESIDUE, AND THE RECURSION THAT SPENDS IT.
--
--   `descent-owes` is CLOSED: it takes no parameter of
--   `descent-closes`'s telescope, and it never mentions `sq` at all.
--   Its three disjuncts are the three ways an infinite ordinal can be
--   served, and each already has a delivered supplier at some site:
--   `squareω` at ω, `via-col-square` under `Init`, and
--   `InternalLeastCard.Selected.δ-inj` for the coded descent.
-- =====================================================================

descent-owes : Type (ℓ-suc ℓ)
descent-owes =
  (a : S) → IsOrd (fst a) → (⟨ fst a ∈ ω ⟩ → Empty.⊥)
  → (fst a ≡ ω)
  ⊎ (Init (fst a)
  ⊎ (Σ[ κ ∈ S ] (⟨ fst κ ∈ fst a ⟩
               × (⟨ fst κ ∈ ω ⟩ → Empty.⊥)
               × ∥ Σ[ A ∈ Mem (Lset (SiteBound.β a)) ]
                     InjCode (SiteBound.up a A) a κ ∥₁)))

-- THE RESIDUE IS NOT VACUOUS, AND THIS IS THE CHECK.  At an ordinal
-- that is an internal cardinal, the THIRD disjunct is refuted outright
-- by `IsCardinalL` (src/L/Cardinal.lagda.md:230-233), so `descent-owes`
-- is not satisfiable by always descending.  Its hard core is the SECOND
-- disjunct at exactly those ordinals.
owes-third-refuted : (a : S) → IsCardinalL a
                   → (κ : S) → ⟨ fst κ ∈ fst a ⟩
                   → ∥ Σ[ A ∈ Mem (Lset (SiteBound.β a)) ]
                         InjCode (SiteBound.up a A) a κ ∥₁
                   → Empty.⊥
owes-third-refuted a ca κ κ∈a h =
  ca κ κ∈a (PT.map (λ Ac → SiteBound.up a (fst Ac) , snd Ac) h)

-- The recursion's motive.  `IsOrd` and infinity travel with it, because
-- both are needed at every κ the descent reaches.
Goal : V ℓ → Type (ℓ-suc ℓ)
Goal x = ⟨ isL x ⟩ → IsOrd x → (⟨ x ∈ ω ⟩ → Empty.⊥) → sq x

descent-step : descent-owes
             → (x : V ℓ) → ((y : V ℓ) → ⟨ y ∈ x ⟩ → Goal y) → Goal x
descent-step owes x ih isLx ox infx =
  Sum.rec at-ω (Sum.rec at-init by-descent) (owes (x , isLx) ox infx)
  where
  at-ω : x ≡ ω → sq x
  at-ω p = subst sq (sym p) squareω

  at-init : Init x → sq x
  at-init = via-col-square x

  by-descent : Σ[ κ ∈ S ] (⟨ fst κ ∈ x ⟩
                         × (⟨ fst κ ∈ ω ⟩ → Empty.⊥)
                         × ∥ Σ[ A ∈ Mem (Lset (SiteBound.β (x , isLx))) ]
                               InjCode (SiteBound.up (x , isLx) A)
                                       (x , isLx) κ ∥₁)
             → sq x
  by-descent (κ , κ∈x , infκ , code) =
    descent-gives-sq (x , isLx) κ
      (mem-incl x (fst κ) ox κ∈x)
      (ih (fst κ) κ∈x (snd κ) (mem-ord {A = x} ox (fst κ) κ∈x) infκ)
      code

-- The band hypothesis already carries the ordinal certificate, so
-- `descent-closes` does not have to be given one.
band-ord : (d : V ℓ) → ⟨ d ∈ sucV α₀ ⟩ → IsOrd d
band-ord d d∈ = ∈sucV-elim (isPropIsOrd d) d∈
  (λ d∈α₀ → mem-ord {A = α₀} oα₀ d d∈α₀)
  (λ d≡α₀ → subst IsOrd (sym d≡α₀) oα₀)

descent-closes : descent-owes
               → (δ : S) → ⟨ fst δ ∈ sucV α₀ ⟩
               → (⟨ fst δ ∈ ω ⟩ → Empty.⊥)
               → sq (fst δ)
descent-closes owes δ δ∈ infδ =
  ∈-induction {P = Goal} (descent-step owes)
    (fst δ) (snd δ) (band-ord (fst δ) δ∈) infδ

-- =====================================================================
-- PART 4.  THE CONSUMER'S SHAPE, WITH THE L-CERTIFICATE PRODUCED.
--
--   `descent-closes` takes δ as an L-ELEMENT, and the consumer at
--   src/L/StageCardinal.lagda.md:17-20 offers a bare `V ℓ`.  The gap
--   closes for free: a member of `sucV α₀` is an ordinal by PART 3's
--   `band-ord`, and every ordinal is an L-element.  So the descent
--   route, once `descent-owes` is paid, discharges the module
--   parameter EXACTLY as the consumer states it.
-- =====================================================================

ConsumerShape : Type (ℓ-suc ℓ)
ConsumerShape =
  (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
  → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
      ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)

plugs-in : descent-owes → ConsumerShape
plugs-in owes δ δ∈ infδ =
  descent-closes owes (δ , isL-ord δ (band-ord δ δ∈)) δ∈ infδ

-- =====================================================================
-- PART 5.  THE SIX CONTROL RUNS, AND WHAT THEY DO AND DO NOT SHOW.
--
--   MEASURED 2026-08-19, caliber `-A64m -I0 -M8g`, ONE Agda process,
--   `agda --safe agents/tasks/LJ-1-390/Probe390.agda` from the
--   repository root, every dependency warm.  Each row is this file
--   truncated or amended to hold exactly what the row names.
--
--     1  imports only, no term of this file                  1.56 s
--     2  row 1 + PART 1, `mem-incl`                          1.46 s
--     3  row 2 + PART 2 written as ONE term, with
--        `code-untruncates δ κ h` bound in the `where` that
--        the injectivity proof reads                       175.42 s
--     4  row 2 + the forward map ALONE, door still bound
--        in the `where`, no injectivity proof                1.54 s
--     5  row 2 + the door's injectivity half ALONE, at
--        generic `a` and generic `b`                         1.57 s
--     6  row 2 + PART 2 in the two halves written above      1.54 s
--
--   WHAT ROWS 3 AND 6 SHOW.  The same mathematics, at the same
--   generality, costs 175.42 s in one term and 1.54 s in two.  The
--   only difference is where `code-untruncates δ κ h` is bound.
--
--   WHAT ROWS 4 AND 5 SHOW.  It is not the door.  Applying the door
--   and spending its FORWARD half is free, and spending its
--   INJECTIVITY half at generic `a` and `b` is free.  The cost needs
--   both halves inside one term.
--
--   WHAT THIS PROBE DID NOT ISOLATE.  The trigger itself.  A seventh
--   run repeated `leg1-gives-sq` of the PRODUCT route
--   (agents/tasks/LJ-1-386/Probe386.agda:294-302) verbatim with its δ
--   made generic, so that both of its sites are variables, and it cost
--   1.56 s.  So the product route's payoff does NOT show the cost, and
--   no statement of the form "the door costs at generic sites" is
--   supported by these runs.  What is supported is the cure at THIS
--   site, and the Boundary forbids transferring it to another by
--   analogy: `[LJ-1.388]`'s consumer must re-measure at its own site.
-- =====================================================================

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.532] W3.  THE WIDEST UNMEASURED TERM: what the approximation
-- `g` is BUILT FROM, and whether anything puts it in `K`.
--
-- THE BRIEF NAMED THE TERM AS "g, as a set, at file:line, with whatever
-- puts it in K or fails to".  The answer this file measures is that `g`
-- IS BUILT FROM NOTHING.  In `LsetGraphAt w b`
-- (src/L/Coding/Sequence.lagda.md:291-292) the approximation is the
-- witness of an UNBOUNDED existential over the whole class carrier, and
-- the only thing said about it is `ApproxAt zero (suc b)`
-- (src/L/Coding/Sequence.lagda.md:286-289).  `ApproxAt` is `domAt`
-- (src/L/Coding/Model.lagda.md:278-280) and a step condition, and BOTH
-- speak only about the KURATOWSKI-PAIR members of `g`.  A member of `g`
-- that is not a pair is unconstrained.
--
-- SO THE MEASUREMENT IS A COUNTEREXAMPLE AND NOT A SEARCH.  This file
-- writes the brief's statement as a TYPE and does not inhabit it, then
-- exhibits an approximation whose single member is `ω`.  Probe532.agda
-- turns that into `¬ ApproxInK`.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-532.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset )
open import L.Ordinal {ℓ} using ( ω-ord )
open import L.Axioms.Basic {ℓ} using ( ∅∈L )
open import L.Axioms.Infinity {ℓ} lem using ( ω∈L )
open import L.Coding.InL {ℓ} using ( sgl-in; sglʟ; sglʟ-out )
open import L.Coding.Model {ℓ} using ( domAt; domAt-intro )
open import L.Coding.Sequence {ℓ} lem using ( ApproxAt; ApproxAt-in )

open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.Data.Vec using ( lookup; _∷_; [] )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; pairing-ax; ⁅_⁆s; module InfinitySet )
open InfinitySet using ( sucV; ω )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ ) using ( _^_ )

-- ---------------------------------------------------------------------
-- SECTION 1.  THE BRIEF'S STATEMENT, AS A TYPE.  IT IS NOT INHABITED
-- HERE AND IT IS NOT INHABITED ANYWHERE: Probe532.agda refutes it.
--
-- The spelling is the site's own.  `LsetGraphAt w b` puts the
-- approximation at slot `zero` of the extended environment and its
-- domain bound at `suc b` (src/L/Coding/Sequence.lagda.md:291-292), so
-- the brief's `⟨ γ ⊨ ApproxAt-at-g ⟩` is `⟨ (g ∷ γ) ⊨ ApproxAt zero
-- (suc b) ⟩` and nothing else.  Every frame fact the chain has ever
-- carried is a hypothesis here, so no reader can say the refutation
-- won by dropping one: K is a LIMIT level, the bound is an ORDINAL, and
-- the bound lies IN K.
-- ---------------------------------------------------------------------

-- Verbatim from [LJ-1.522] (agents/tasks/LJ-1-522/Probe522.agda:75-79),
-- through [LJ-1.530] (agents/tasks/LJ-1-530/Probe530.agda:77-82).
IsLimit : V ℓ → Type (ℓ-suc ℓ)
IsLimit α = IsOrd α
          × ⟨ ∅ ∈ α ⟩
          × ((β : V ℓ) → ⟨ β ∈ α ⟩ → ⟨ sucV β ∈ α ⟩)

ApproxInK : Type (ℓ-suc ℓ)
ApproxInK =
    (α : V ℓ) → IsLimit α
  → ∀ {n} (b K : Fin n) (γ : S ^ n)
  → fst (lookup K γ) ≡ Lset α
  → IsOrd (fst (lookup b γ))
  → ⟨ fst (lookup b γ) ∈ fst (lookup K γ) ⟩
  → (g : S)
  → ⟨ (g ∷ γ) ⊨ ApproxAt zero (suc b) ⟩
  → ⟨ fst g ∈ fst (lookup K γ) ⟩

-- ---------------------------------------------------------------------
-- SECTION 2.  AN ORDINAL IS NOT A KURATOWSKI PAIR.
--
-- `pr a b = ⁅ ⁅ a ⁆s , ⁅ a , b ⁆ ⁆` (src/V/Coding.lagda.md:175-176), so
-- a transitive `pr a b` pulls `a` down into itself and `∈-irrefl`
-- (src/V/Hierarchy.lagda.md:155-156) closes it.  Transitivity is
-- `IsOrd`'s first component (src/L/Constructible.lagda.md:141-142 with
-- :83).
-- ---------------------------------------------------------------------

private
  inPair : (u v x : V ℓ) → ∥ (x ≡ u) ⊎ (x ≡ v) ∥₁ → ⟨ x ∈ ⁅ u , v ⁆ ⟩
  inPair u v x h = ∈∈ₛ {a = x} {b = ⁅ u , v ⁆} .snd (pairing-ax u v x .snd h)

  outPair : (u v x : V ℓ) → ⟨ x ∈ ⁅ u , v ⁆ ⟩ → ∥ (x ≡ u) ⊎ (x ≡ v) ∥₁
  outPair u v x h = pairing-ax u v x .fst (∈∈ₛ {a = x} {b = ⁅ u , v ⁆} .fst h)

ord-not-pr : (A : V ℓ) → IsOrd A → (a b : V ℓ) → A ≡ pr a b → Empty.⊥
ord-not-pr A oA a b q = PT.rec Empty.isProp⊥ close (outPair ⁅ a ⁆s ⁅ a , b ⁆ a a∈pr)
  where
  trans-pr : {x y : V ℓ} → ⟨ y ∈ x ⟩ → ⟨ x ∈ pr a b ⟩ → ⟨ y ∈ pr a b ⟩
  trans-pr {x} {y} y∈x x∈ = subst (λ u → ⟨ y ∈ u ⟩) q
    (oA .fst y∈x (subst (λ u → ⟨ x ∈ u ⟩) (sym q) x∈))

  a∈sgl : ⟨ a ∈ ⁅ a ⁆s ⟩
  a∈sgl = sgl-in a a refl

  a∈pair : ⟨ a ∈ ⁅ a , b ⁆ ⟩
  a∈pair = inPair a b a ∣ inl refl ∣₁

  sgl∈pr : ⟨ ⁅ a ⁆s ∈ pr a b ⟩
  sgl∈pr = inPair ⁅ a ⁆s ⁅ a , b ⁆ ⁅ a ⁆s ∣ inl refl ∣₁

  a∈pr : ⟨ a ∈ pr a b ⟩
  a∈pr = trans-pr a∈sgl sgl∈pr

  close : (a ≡ ⁅ a ⁆s) ⊎ (a ≡ ⁅ a , b ⁆) → Empty.⊥
  close (inl e) = ∈-irrefl a (subst (λ u → ⟨ a ∈ u ⟩) (sym e) a∈sgl)
  close (inr e) = ∈-irrefl a (subst (λ u → ⟨ a ∈ u ⟩) (sym e) a∈pair)

-- ---------------------------------------------------------------------
-- SECTION 3.  THE MEASUREMENT.  `ApproxAt` IS BLIND TO A MEMBER THAT IS
-- NOT A PAIR.
--
-- The approximation is the singleton of `ω` and its domain bound is `∅`.
-- `domAt`'s two halves and the step condition are ALL vacuous, and each
-- is vacuous for a reason this file names: no member of `⁅ ω ⁆s` is a
-- Kuratowski pair, and no set is a member of `∅`.
-- ---------------------------------------------------------------------

∅ʟ ωʟ gʟ : S
∅ʟ = ∅ , ∅∈L
ωʟ = ω , ω∈L
gʟ = sglʟ ωʟ

γ₀ : S ^ 1
γ₀ = ∅ʟ ∷ []

no-pair-in-g : (c z : S) → ⟨ pr (fst c) (fst z) ∈ fst gʟ ⟩ → Empty.⊥
no-pair-in-g c z p = ord-not-pr ω ω-ord (fst c) (fst z)
  (sym (sglʟ-out ωʟ (pr (fst c) (fst z)) p))

dom-blind : ⟨ (gʟ ∷ γ₀) ⊨ domAt zero (suc zero) ⟩
dom-blind = domAt-intro zero (suc zero) (gʟ ∷ γ₀)
  (λ x → (λ h → PT.rec (snd (fst x ∈ ∅))
                  (λ { (y , p) → Empty.rec (no-pair-in-g x y p) }) h)
       , (λ m → Empty.rec (∅-empty (fst x) (∈∈ₛ {a = fst x} {b = ∅} .fst m))))

blind : ⟨ (gʟ ∷ γ₀) ⊨ ApproxAt zero (suc zero) ⟩
blind = ApproxAt-in zero (suc zero) (gʟ ∷ γ₀) dom-blind
  (λ c z p → Empty.rec (no-pair-in-g c z p))

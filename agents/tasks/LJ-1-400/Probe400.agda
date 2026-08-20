{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.400] PROBE.  The coded square law at a GENERIC L-cardinal.
-- It runs in agents/tasks/LJ-1-400/ and lands nothing.
--
-- W8 first: the literature does not add a side condition this tree
-- fails.  The square law is a theorem (an infinite cardinal squared
-- is itself).  Gödel pairing is a hypothesis of SZ 1.17, for a
-- surjection onto J_α, not for κ × κ ↪ κ.
--
-- W3 first in the Agda: `collapse-states` is the object-language
-- statement of the collapse, with NO proof.  Then the residue
-- `card-owes`, then `card-pair-code` from that residue.
--
-- Route A: code the ambient collapse.  Route B is the same graph
-- written without naming `col`.  The formula is the shared cost.
--
-- `[LJ-1.399]` is not in the tree.  The unit price is `IdGraph`
-- (agents/tasks/LJ-1-386/Probe386.agda:94-193).

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-400.Probe400 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; con; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset )
open import L.Choice.Step {ℓ} lem using ( Mem )
open import L.Coding.Model {ℓ} using ( prAtL; sucAtL )
open import L.Cardinal {ℓ} lem
  using ( InjCode; IsCardinalL; module SiteBound )
open import LJ-1-388.Probe388 {ℓ} lem using ( prodL )

open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Vec using ( [] )
open import Cubical.Data.FinData using ( suc; zero )
open import Cubical.Data.Nat using ( _+_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- W3.  THE OBJECT-LANGUAGE STATEMENT OF THE COLLAPSE.
--
--   No proof.  The census is in the report: src/ holds none of
--   `godAt`, `collapse-states`, or a family-union reader.  It holds
--   the atoms this block composes: `prAtL`, `sucAtL`, `appAt`,
--   `extAt` (here spelled), and the max atom already measured at
--   agents/tasks/LJ-1-327/ProbeLJ1327A.agda:132-134.
--
--   Ambient meaning, not stated as a theorem here:
--
--     (a,b) ≺ (c,d)  iff  max(a,b) ∈ max(c,d)
--                      or (max equal and a ∈ c)
--                      or (max equal and a = c and b ∈ d)
--
--     F records col on P  iff  for every p ∈ P,
--       F(p) = ⋃ { suc(F(r)) | r ∈ P and r ≺ p }.
--
--   That is `col-compute` at src/L/Ordinal/SquareLaw.lagda.md:387,
--   written as a formula.
-- =====================================================================

-- m = max(a,b) as ordinals.  Copied from
-- agents/tasks/LJ-1-327/ProbeLJ1327A.agda:132-134, which proved
-- adequacy both ways and is not in src/.
maxAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
maxAt m a b = (((var b ∈̇ var a) ∨̇ (var b ≐ var a)) ∧̇ (var m ≐ var a))
           ∨̇ ((var a ∈̇ var b) ∧̇ (var m ≐ var b))

-- Six binders: a, b, c, d, m1, m2.
private
  suc₆ : ∀ {n} → Fin n → Fin (6 + n)
  suc₆ i = suc (suc (suc (suc (suc (suc i)))))

-- The Gödel order on two coded pairs, as a formula.  NOT in src/.
-- p ≺ q, with p and q free.  Binders (innermost first): m2, m1, d, c, b, a.
godAt : ∀ {n} → Fin n → Fin n → Formula S n
godAt {n} p q =
  ∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ body)))))
  where
  a  : Fin (6 + n)
  a  = suc (suc (suc (suc (suc zero))))
  b  : Fin (6 + n)
  b  = suc (suc (suc (suc zero)))
  c  : Fin (6 + n)
  c  = suc (suc (suc zero))
  d  : Fin (6 + n)
  d  = suc (suc zero)
  m1 : Fin (6 + n)
  m1 = suc zero
  m2 : Fin (6 + n)
  m2 = zero
  rest : Formula S (6 + n)
  rest = (var a ∈̇ var c)
      ∨̇ ((var a ≐ var c) ∧̇ (var b ∈̇ var d))
  clause : Formula S (6 + n)
  clause = (var m1 ∈̇ var m2)
        ∨̇ ((var m1 ≐ var m2) ∧̇ rest)
  body : Formula S (6 + n)
  body = prAtL (suc₆ p) a b
      ∧̇ prAtL (suc₆ q) c d
      ∧̇ maxAt m1 a b
      ∧̇ maxAt m2 c d
      ∧̇ clause

-- Application against a constant graph, because `appAt` takes a
-- variable index (src/L/Coding/Model.lagda.md:160-161).
appAtCon : ∀ {n} → S → Fin n → Fin n → Formula S n
appAtCon F x y = ∃̇∈ (con F) (prAtL zero (suc x) (suc y))

-- Extensional reader, spelled here so this file does not open `extAt`.
-- Same two implications as src/L/Coding/Model.lagda.md:662-664.
extAt′ : ∀ {n} → Fin n → Formula S (suc n) → Formula S n
extAt′ y φ = ∀̇ ((var zero ∈̇ var (suc y)) ⇒̇ φ)
          ∧̇ ∀̇ (φ ⇒̇ (var zero ∈̇ var (suc y)))

-- ξ is a member of ⋃ { suc(F(r)) | r ∈ P and r ≺ p }.
-- Environment: (ξ ∷ γ ∷ p ∷ []).
private
  colElem : (P F : S) → Formula S 3
  colElem P F =
    ∃̇∈ (con P) (
         godAt zero (suc (suc (suc zero)))
      ∧̇ ∃̇ (
           appAtCon F (suc zero) zero
        ∧̇ ∃̇ (
             sucAtL (suc zero) zero
          ∧̇ (var (suc (suc (suc zero))) ∈̇ var zero))))

-- THE W3 STATEMENT.  F records the collapse on P.
-- No proof.  Environment: empty.  P and F are constants.
collapse-states : (P F : S) → Formula S 0
collapse-states P F =
  ∀̇∈ (con P) (
    ∃̇ (
         appAtCon F (suc zero) zero
      ∧̇ extAt′ zero (colElem P F)))

-- =====================================================================
-- THE RESIDUE.  What the code still needs when the construction
-- stops: a graph that satisfies the statement, that is an `InjCode`
-- out of the internal square into the cardinal, and that sits at the
-- product's own stage bound.  The door then packages it, as
-- `good-from-placement` did for the identity
-- (agents/tasks/LJ-1-386/Probe386.agda:203-214).
-- =====================================================================

card-owes : Type (ℓ-suc ℓ)
card-owes =
  (κ : S) → IsOrd (fst κ) → IsCardinalL κ → ⟨ ω ∈ fst κ ⟩
  → Σ[ F ∈ S ]
      ( ⟨ [] ⊨ collapse-states (prodL κ κ) F ⟩
      × InjCode F (prodL κ κ) κ
      × ⟨ fst F ∈ Lset (SiteBound.β (prodL κ κ)) ⟩ )

-- =====================================================================
-- THE OBLIGATION.  From the residue, the door's input.  Placement
-- transports `InjCode` along `SiteBound.up`, which changes only the
-- `isL` proof.
-- =====================================================================

card-pair-code :
    card-owes
  → (κ : S) → IsOrd (fst κ) → IsCardinalL κ → ⟨ ω ∈ fst κ ⟩
  → ∥ Σ[ A ∈ Mem (Lset (SiteBound.β (prodL κ κ))) ]
        InjCode (SiteBound.up (prodL κ κ) A) (prodL κ κ) κ ∥₁
card-pair-code owes κ oκ cκ ωκ =
  ∣ (fst F , placed) , subst (λ G → InjCode G (prodL κ κ) κ) (sym upF) code ∣₁
  where
  pack = owes κ oκ cκ ωκ
  F : S
  F = pack .fst
  code : InjCode F (prodL κ κ) κ
  code = pack .snd .snd .fst
  placed : ⟨ fst F ∈ Lset (SiteBound.β (prodL κ κ)) ⟩
  placed = pack .snd .snd .snd
  open SiteBound (prodL κ κ) using ( up )
  upF : up (fst F , placed) ≡ F
  upF = Σ≡Prop (λ v → snd (isL v)) refl

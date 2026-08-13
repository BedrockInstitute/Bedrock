{-# OPTIONS --cubical --safe --guardedness #-}

-- [L3.32-T179] D22 probe: the carried order-story's successor clause over
-- the values lex at one carrier, with its two-way decode.  Untracked probe,
-- never committed (D-1).  Gate shape: T128's (clause, formula, two-way
-- decode, one carrier).  The values lex is the delivered supplier
-- (StepGraph block 4, T170) and enters as a module parameter with its lex
-- reading at the clause's environment; the probe measures the clause.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module ProbeT179 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; _∧̇_; _⇒̇_; ∀̇_; ∃̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using
  ( IsOrd; isTransV; Lset; Lset-mono; Lset-layer; layer-trans )
open import L.Ordinal {ℓ} using ( ∅-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit-ord )
open import L.Rud.OrdBlocks {ℓ} lem using ( +ω; +ω-limit; +ω-iter )
open import L.InitialSegment {ℓ} using ( _⟷_ )
open import L.Rud.Step {ℓ} lem A using ( Op16; Fof )
open import L.Rud.Order {ℓ} lem A using ( opIx; opIx-inj )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; natSWO; pullSWO )
open import L.LevelKit {ℓ} using ( module LevelKit )
open import Cubical.Data.FinData.Base using ( Fin; zero; suc )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- The one carrier: C = Lset β₀ with β₀ = +ω a₀, a₀ = +ω ∅ (T128's).
a₀ : S
a₀ = +ω ∅

β₀ : S
β₀ = +ω a₀

a₀-ord : IsOrd a₀
a₀-ord = isLimit-ord a₀ (+ω-limit ∅ ∅-ord)

C : V ℓ
C = Lset β₀

utr : isTransV C
utr = layer-trans (Lset-layer β₀)

module K = LevelKit C utr
open K public

-- The content point: the successor index sucV a₀ lives in the carrier, so
-- a story over the carrier's domain has a successor clause with content.
sucV-a₀∈C : ⟨ sucV a₀ ∈ˢ C ⟩
sucV-a₀∈C = Lset-mono {α = β₀} {β = sucV (sucV a₀)} (+ω-iter 2 a₀)
  (ord∈Lset-suc (sucV a₀) (suc-ord a₀-ord))

x₀ : ⟪ C ⟫
x₀ = ∈-asFiber {a = sucV a₀} {b = C} sucV-a₀∈C .fst

-- The op order on the sixteen indices, pulled from the delivered natural
-- order along opIx (Order's own construction, restated for the clause).
opSWO : SWO Op16
opSWO = pullSWO natSWO opIx opIx-inj

private
  module Op = SWO opSWO

-- The meta-level lex on the codes, the successor clause's right-hand side
-- (SZ's lex): x and y are values of operations at argument pairs, compared
-- by the operation index, then by the first argument, then by the second,
-- each argument comparison read from the previous order r, the bounded
-- descent that dissolves wall 2 (R-35: memberships at the small index).
codeLex : S → S → S → Type (ℓ-suc ℓ)
codeLex r x y = ∥ Σ[ u ∈ S ] Σ[ v ∈ S ] Σ[ u' ∈ S ] Σ[ v' ∈ S ]
  (Σ[ i ∈ Op16 ] Σ[ j ∈ Op16 ]
   (x ≡ Fof i u v) × (y ≡ Fof j u' v')
   × ((i Op.<∙ j) ⊎ ((i ≡ j) × (⟨ pr u u' ∈ˢ r ⟩
       ⊎ ((u ≡ u') × ⟨ pr v v' ∈ˢ r ⟩))))) ∥₁

-- The successor clause: the successor order r' of the previous order r
-- contains exactly the pairs whose codes compare lex, pointwise (R-35).
succClause : S → S → Type (ℓ-suc ℓ)
succClause r r' = (x y : SM) → ⟨ pr (fst x) (fst y) ∈ˢ r' ⟩
                ⟷ codeLex r (fst x) (fst y)

-- The values lex, the successor step's supplier, as a module parameter:
-- the lex reading at the clause's environment (y, x, r', r, x₀), with its
-- two-way decode to the meta codeLex (r at slot 3, the values slots 1, 0).
module Succ
  (valueLexAt : Formula ⟪ C ⟫ 5)
  (valueLexAt-ok : (δ : Vec SM 5) → ⟨ δ ⊨ᵐ valueLexAt ⟩
                 ⟷ codeLex (fst (lookup (suc (suc (suc zero))) δ))
                   (fst (lookup (suc zero) δ)) (fst (lookup zero δ)))
  where

  -- The successor clause's object formula, arity 3, env (r', r, x₀): for
  -- every x and y, pr x y ∈ r' exactly when the codes compare lex.
  succForm : Formula ⟪ C ⟫ 3
  succForm = ∀̇ (∀̇ (((∃̇∈ (var (suc (suc zero)))
                       (PK.prAt zero (suc (suc zero)) (suc zero)))
                     ⇒̇ valueLexAt)
                 ∧̇ (valueLexAt
                     ⇒̇ (∃̇∈ (var (suc (suc zero)))
                         (PK.prAt zero (suc (suc zero)) (suc zero))))))

  -- The clause's two-way decode at the standing arity and the content
  -- point x₀ (the value lex reading's standing point).
  succ-ok : (r' r : SM) → ⟨ (r' ∷ r ∷ ι x₀ ∷ []) ⊨ᵐ succForm ⟩
          ⟷ succClause (fst r) (fst r')
  succ-ok r' r = (out , back)
    where
    δ₃ : Vec SM 3
    δ₃ = r' ∷ r ∷ ι x₀ ∷ []
    out : ⟨ δ₃ ⊨ᵐ succForm ⟩ → succClause (fst r) (fst r')
    out h xv yv = (fwdOut , bwdOut)
      where
      δ₅ : Vec SM 5
      δ₅ = yv ∷ xv ∷ δ₃
      fwdOut : ⟨ pr (fst xv) (fst yv) ∈ˢ fst r' ⟩
             → codeLex (fst r) (fst xv) (fst yv)
      fwdOut xy = valueLexAt-ok δ₅ .fst
        (h xv yv .fst
          (pair∈ (suc (suc zero)) (suc zero) zero δ₅ .snd xy))
      bwdOut : codeLex (fst r) (fst xv) (fst yv)
             → ⟨ pr (fst xv) (fst yv) ∈ˢ fst r' ⟩
      bwdOut cl = pair∈ (suc (suc zero)) (suc zero) zero δ₅ .fst
        (h xv yv .snd (valueLexAt-ok δ₅ .snd cl))
    back : succClause (fst r) (fst r') → ⟨ δ₃ ⊨ᵐ succForm ⟩
    back sc xv yv = (fwdIn , bwdIn)
      where
      δ₅ : Vec SM 5
      δ₅ = yv ∷ xv ∷ δ₃
      fwdIn : ⟨ (yv ∷ xv ∷ δ₃) ⊨ᵐ (∃̇∈ (var (suc (suc zero)))
               (PK.prAt zero (suc (suc zero)) (suc zero))) ⟩
           → ⟨ (yv ∷ xv ∷ δ₃) ⊨ᵐ valueLexAt ⟩
      fwdIn pair-sat = valueLexAt-ok δ₅ .snd
        (sc xv yv .fst
          (pair∈ (suc (suc zero)) (suc zero) zero δ₅ .fst pair-sat))
      bwdIn : ⟨ (yv ∷ xv ∷ δ₃) ⊨ᵐ valueLexAt ⟩
           → ⟨ (yv ∷ xv ∷ δ₃) ⊨ᵐ (∃̇∈ (var (suc (suc zero)))
               (PK.prAt zero (suc (suc zero)) (suc zero))) ⟩
      bwdIn lex-sat = pair∈ (suc (suc zero)) (suc zero) zero δ₅ .snd
        (sc xv yv .snd (valueLexAt-ok δ₅ .fst lex-sat))

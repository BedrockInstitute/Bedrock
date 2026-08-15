{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.294] PROBE.  Is an infinite internal cardinal a limit ordinal?
--
-- The target is `Init`'s THIRD component, the successor closure, at the
-- GCH use site (src/L/Ordinal/SquareLaw.lagda.md:695), where kappa
-- arrives with `IsCardinalL kappa` and `kappa` outside omega:
--
--   (gamma : S) -> gamma in kappa -> sucV gamma in kappa.
--
-- The route: if sucV gamma misses kappa, trichotomy leaves either
-- kappa below sucV gamma, refuted by irreflexivity, or kappa EQUAL to
-- sucV gamma.  In the equal case the absorption chapter's coded graph
-- `G` (a code for the shift injection sucV gamma -> gamma) refutes
-- `IsCardinalL kappa` at delta = gamma.  The InjCode-against-injection
-- gap is closed WITHOUT a bridge: the code is built inside
-- `L.Absorption.ShiftGraph` and only its four conjuncts are consumed.
--
-- Tracked; ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-294.CardinalLimit {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Ordinal {ℓ} using ( ω-ord; #∈ω; mem-ord; suc-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri; Tri )
open import L.Cardinal {ℓ} lem using ( IsCardinalL; InjCode )
open import L.InjChain {ℓ} lem using ( ω-limit )
open import L.Absorption {ℓ} lem using ( module ShiftGraph )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV; #_; ω )
import Cubical.Data.Empty as Empty
import Cubical.Data.Nat using ( ℕ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- THE LEMMA.  An internal cardinal outside omega is successor closed.
κ-limit : (κ : S) → IsOrd (fst κ) → IsCardinalL κ
        → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
        → (γ : V ℓ) → ⟨ γ ∈ˢ fst κ ⟩ → ⟨ sucV γ ∈ˢ fst κ ⟩
κ-limit κ oκ cκ nfin γ γ∈κ = at (lem (sucV γ ∈ˢ fst κ))
  where
  -- A member of a level is a level, so gamma enters the L-carrier.
  γᴸ : S
  γᴸ = γ , isL-trans γ∈κ (snd κ)

  -- A member of an ordinal is an ordinal.
  oγ : IsOrd γ
  oγ = mem-ord {A = fst κ} oκ γ γ∈κ

  at : ⟨ sucV γ ∈ˢ fst κ ⟩ ⊎ (⟨ sucV γ ∈ˢ fst κ ⟩ → Empty.⊥)
     → ⟨ sucV γ ∈ˢ fst κ ⟩
  at (inl h) = h
  at (inr ¬h) = Empty.rec (tri (ord-tri (sucV γ) (suc-ord oγ) (fst κ) oκ))
    where
    -- Below sucV gamma, kappa is a member of gamma or gamma itself.
    -- Both contradict irreflexivity, by transitivity.  The eliminator
    -- wants its motive at `Type (ℓ-suc ℓ)`, so the contradiction is
    -- lifted.
    below : ⟨ fst κ ∈ˢ sucV γ ⟩ → Empty.⊥
    below κ∈sγ = lower
      (∈sucV-elim {A = γ} {x = fst κ}
        {P = Lift {j = ℓ-suc ℓ} (Empty.⊥)}
        (λ p q → Empty.rec (lower p))
        κ∈sγ
        (λ κ∈γ → lift (∈-irrefl γ (oγ .fst γ∈κ κ∈γ)))
        (λ κ≡γ → lift (∈-irrefl γ (subst (λ w → ⟨ γ ∈ˢ w ⟩) κ≡γ γ∈κ))))

    -- The successor case.  kappa IS sucV gamma, and the absorption
    -- chapter's coded graph refutes cardinality.
    equal : sucV γ ≡ fst κ → Empty.⊥
    equal sγ≡κ =
      cκ γᴸ γ∈κ ∣ SG.G , code ∣₁
      where
      γ∉ω : ⟨ γ ∈ˢ ω ⟩ → Empty.⊥
      γ∉ω γ∈ω = nfin (subst (λ w → ⟨ w ∈ˢ ω ⟩) sγ≡κ (ω-limit γ γ∈ω))

      -- Every numeral sits in gamma: gamma is outside omega, so omega
      -- is a member of gamma or gamma is omega, by trichotomy.
      numerals : (k : ℕ) → ⟨ (# k) ∈ˢ γ ⟩
      numerals k = num (ord-tri γ oγ ω ω-ord)
        where
        num : Tri γ ω → ⟨ (# k) ∈ˢ γ ⟩
        num (inl γ∈ω)  = Empty.rec (γ∉ω γ∈ω)
        num (inr (inl γ≡ω)) = subst (λ w → ⟨ (# k) ∈ˢ w ⟩) (sym γ≡ω) (#∈ω k)
        num (inr (inr ω∈γ)) = oγ .fst (#∈ω k) ω∈γ

      module SG = ShiftGraph γᴸ oγ γ∉ω numerals

      -- The code at D, then transported along D ≡ κ.  The whole
      -- conjunct moves at once: `InjCode` is the exported predicate,
      -- so no local satisfaction alias needs naming.
      codeD : InjCode SG.G SG.D γᴸ
      codeD = SG.sv , SG.dm , SG.ij , SG.ran

      -- fst SG.D is sucV gamma by construction, so SG.D is kappa:
      -- the pair equality is first-component-only, since isL is a prop.
      D≡κ : SG.D ≡ κ
      D≡κ = Σ≡Prop (λ x → snd (isL x)) sγ≡κ

      code : InjCode SG.G κ γᴸ
      code = subst (λ a → InjCode SG.G a γᴸ) D≡κ codeD

    tri : Tri (sucV γ) (fst κ) → Empty.⊥
    tri (inl sγ∈κ)     = ¬h sγ∈κ
    tri (inr (inl e))  = equal e
    tri (inr (inr k∈s)) = below k∈s

-- ROW TWO OF THE USE-SITE TABLE, MEASURED IN ITS CORRECTED FORM.
-- From `nfin` alone the row is FALSE at kappa = omega: there
-- `omega in kappa` unfolds to `omega in omega`, refuted by
-- `∈-irrefl`.  Under the extra split the row is one trichotomy, and
-- the `omega` disjunct is exactly the base `[LJ-1.279]` rebuilt from
-- `InitialCore` rather than `via-col-square`.
ω∈κ-after-split : (κ : S) → IsOrd (fst κ)
               → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
               → ((ω ≡ fst κ) → Empty.⊥)   -- kappa is not omega
               → ⟨ ω ∈ˢ fst κ ⟩
ω∈κ-after-split κ oκ nfin ω≢κ = at (ord-tri ω ω-ord (fst κ) oκ)
  where
  at : Tri ω (fst κ) → ⟨ ω ∈ˢ fst κ ⟩
  at (inl h) = h
  at (inr (inl ω≡κ)) = Empty.rec (ω≢κ ω≡κ)
  at (inr (inr κ∈ω)) = Empty.rec (nfin κ∈ω)

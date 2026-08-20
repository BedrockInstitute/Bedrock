{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.401] PROBE.  InjCode is a proposition, so the least code is DATA.
-- Lives in agents/tasks/LJ-1-401/ and lands nothing in src/.
--
-- W3 first: clause 4 of InjCode (src/L/Cardinal.lagda.md:228) alone,
-- proved a proposition, before isPropInjCode or sel-code is written.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-401.Probe401 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset )
open import L.Choice.Step {ℓ} lem using ( Mem; orderAt )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( leastOf )
open import L.Coding.Model {ℓ} using ( svAt; domAt )
open import L.Coding.Injection {ℓ} lem using ( injAt )
open import L.Cardinal {ℓ} lem
  using ( InjCode; module SiteBound; module InternalLeastCard )

open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- W3. Clause 4 of InjCode, spelled at src/L/Cardinal.lagda.md:228, alone.
clause4 : S → S → Type (ℓ-suc ℓ)
clause4 F b =
  (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst b ⟩

clause4-isProp : (F b : S) → isProp (clause4 F b)
clause4-isProp F b =
  isPropΠ (λ x → isPropΠ (λ y → isPropΠ (λ _ → snd (fst y ∈ fst b))))

-- Generic: names no cardinal, no stage, no site. W2.
isPropInjCode : (F a b : S) → isProp (InjCode F a b)
isPropInjCode F a b =
  isProp× (snd ((F ∷ a ∷ []) ⊨ svAt zero))
    (isProp× (snd ((F ∷ a ∷ []) ⊨ domAt zero (suc zero)))
      (isProp× (snd ((F ∷ a ∷ []) ⊨ injAt zero))
        (clause4-isProp F b)))

-- Sited: one leastOf at InternalLeastCard's code, input δ-inj.
-- IsLeast half dropped: the task needs the code and its InjCode.
sel-code :
    (κ : S) (oκ : IsOrd (fst κ))
  → (nonempty : ∥ Σ[ δ ∈ Mem (Lset (SiteBound.β κ)) ]
                   ⟨ InternalLeastCard.Good κ oκ δ ⟩ ∥₁)
  → Σ[ F ∈ Mem (Lset (SiteBound.β κ)) ]
      InjCode (SiteBound.up κ F) κ
        (InternalLeastCard.Selected.δᴸ κ oκ nonempty)
sel-code κ oκ nonempty = fst got , fst (snd got)
  where
  open SiteBound κ
  open InternalLeastCard κ oκ
  open Selected nonempty
  got = leastOf (orderAt β oβ) lem
          (λ F → InjCode (up F) κ δᴸ , isPropInjCode (up F) κ δᴸ)
          δ-inj

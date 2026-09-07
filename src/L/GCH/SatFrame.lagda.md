# The graph of the uniform table

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.SatFrame {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes )
open import L.Coding.Model {ℓ} using ( container ) public
open import L.Coding.Quantification {ℓ} public
  using ( bothAll; bothAll-in; down; fillSnd; i0; i1; i2; i3; i6; i8
        ; sndS; pr-in; pr-out; sh; sndAll; sndAll-in; sndEx; sndEx-out; suc-in; suc-out
        ; useBoth; useSnd; Δ₀-bothAll; Δ₀-prAtL; Δ₀-sndAll; Δ₀-sndEx; Δ₀-sucAtL )
open import L.Coding.Tower {ℓ} lem public
  using ( nn; towerAt; Δ₀-towerAt; module Tower; module TowerHolds; module TowerRead )
open import L.Coding.CodeDomain {ℓ} lem public
  using ( Tags; codesAt; f0; f1; f2; f3; f4; f5; f6; f7; f8; f9; shN
        ; Δ₀-codesAt; module Alphabet; module CodesComplete; module CodesHolds
        ; module CodesSound )
open import L.Coding.Clauses {ℓ} lem public
  using ( tableAt; Δ₀-tableAt; module Bridge; module Frame )

open import FOL.Syntax using ( Formula )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Vec using ( _∷_; [] )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ)) using ()
open hPropStructure 𝒮ʟ using ( S )

module AbsSF = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsSF using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

```

The graph of the uniform table, as a set. The value function of
src/L/Coding/Uniform.lagda.md `Table` supplies a recursion, and
src/L/Recursion.lagda.md `Graph` makes its graph a set. Sealed where it is
built; its two readers are what the consumer holds.

```agda
open import L.Coding.Uniform {ℓ} lem using ( module Table )
open import L.Recursion {ℓ} lem using ( Recursion ) renaming ( module Graph to MapGraph )

module SatGraph (W : S) where
```

SEALED: the value at a member is a contractibility centre, and written out it
does not elaborate (src/L/Coding/Uniform.lagda.md `val-at`'s measurement). Every
use below names it by this atom.

```agda
  opaque
    valOf : (x : S) → ⟨ fst x ∈ fst (AllCodes W) ⟩ → S
    valOf x mx = Table.val W W x mx

    valOf≡ : (x : S) (mx : ⟨ fst x ∈ fst (AllCodes W) ⟩) → valOf x mx ≡ Table.val W W x mx
    valOf≡ x mx = refl

  private
    opaque
      unfolding valOf
      gr : Formula S 2
      gr = Table.graph W W

      defines' : (x : S) (mx : ⟨ fst x ∈ fst (AllCodes W) ⟩) → ⟨ (valOf x mx ∷ x ∷ []) ⊨ gr ⟩
      defines' x mx = Table.funct W W x mx .fst .snd

      only' : (x : S) (mx : ⟨ fst x ∈ fst (AllCodes W) ⟩) (y : S) → ⟨ (y ∷ x ∷ []) ⊨ gr ⟩ → y ≡ valOf x mx
      only' x mx y h = sym (Table.val-uniq W W x mx y h)

    M : Recursion
    M = record
      { dom = AllCodes W ; graph = gr
      ; funct = λ x mx → (valOf x mx , defines' x mx)
          , λ { (y , h) → Σ≡Prop (λ w → snd ((w ∷ x ∷ []) ⊨ gr)) (sym (only' x mx y h)) } }

    module G = MapGraph M using ( F; F-in; pair-out )

  opaque
    pairs : S
    pairs = G.F

    pairs-in : (x : S) (mx : ⟨ fst x ∈ fst (AllCodes W) ⟩) → ⟨ pr (fst x) (fst (valOf x mx)) ∈ fst pairs ⟩
    pairs-in = G.F-in

    pairs-out : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst pairs ⟩
              → Σ[ mx ∈ ⟨ fst x ∈ fst (AllCodes W) ⟩ ] (fst y ≡ fst (valOf x mx))
    pairs-out = G.pair-out
```

Every member is a pair.

```agda
    pairs-shape : (e : S) → ⟨ fst e ∈ fst pairs ⟩
                → ∥ Σ[ x ∈ S ] Σ[ mx ∈ ⟨ fst x ∈ fst (AllCodes W) ⟩ ] (fst e ≡ pr (fst x) (fst (valOf x mx))) ∥₁
    pairs-shape e h = MapGraph.F-out M (fst e) h
```

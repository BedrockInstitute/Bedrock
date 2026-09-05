# The cardinal faces of the L-carrier

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Cardinal {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV )
open import V.Presentation {ℓ} using ( member; fiber )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.SquareLaw {ℓ} lem using ( ordSWO )
open import L.Choice.Stage {ℓ} lem using ( stageBound )
open import L.Choice.Step {ℓ} lem using ( Mem; orderAt )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; IsLeast; leastOf; module SWO )
open import L.Coding.Model {ℓ} using ( svAt; domAt )
open import L.Coding.Injection {ℓ} lem using ( injAt )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

The ambient injection type, as the square-law chain carries it.

```agda
_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)
```

A1.  The least cardinal, in the ambient-injection form.

  The ambient square-law chain's `LeastCardInj` restated over the
  L-carrier: α is an L-element, the per-site hypothesis is the
  ordinal certificate `oα`, and the crossing `up` lifts a member of
  the tower at `sucV (fst α)` into the L-carrier.  The lift is where
  the three delivered L-lemmas surface: `ord∈Lset-suc` and `Lset→isL`
  give level-hood of the stage, `isL-trans` pushes it down.

```agda
module LeastCardInjL (α : S) (oα : IsOrd (fst α)) where

  Inj : S → Type ℓ
  Inj γ = ⟪ fst α ⟫ ↪ ⟪ fst γ ⟫

  InjP : S → hProp ℓ
  InjP γ = ∥ Inj γ ∥₁ , squash₁

  -- `⟨ isL α ⟩` alone does not give level-hood of `sucV (fst α)`;
  -- it comes from an ordinal appearing at the stage after itself,
  -- plus membership in a stage being level-hood.
  hSucα : ⟨ isL (sucV (fst α)) ⟩
  hSucα = Lset→isL (sucV (sucV (fst α))) (suc-ord (suc-ord oα)) (sucV (fst α))
            (ord∈Lset-suc (sucV (fst α)) (suc-ord oα))

  -- `isL-trans` propagates level-hood down to the members, turning a
  -- member of the tower into an L-element.
  up : ⟪ sucV (fst α) ⟫ → S
  up m = ⟪ sucV (fst α) ⟫↪ m
       , isL-trans (member (sucV (fst α)) m) hSucα

  InjP' : ⟪ sucV (fst α) ⟫ → hProp ℓ
  InjP' γ = InjP (up γ)

  -- The well-order is SEALED.  Transparent, its comparison unfolds the
  -- union representation `⟪ sucV (fst α) ⟫` once in `least` below, and
  -- again inside every conversion check that `κ-min-at` runs.  The seal
  -- makes `leastOf w` a stuck atom, so `γ-card` and `fst κ` never
  -- re-unfold, and the whole master falls from about 100 s to about 9 s.
  opaque
    w : SWO (⟪ sucV (fst α) ⟫)
    w = ordSWO (sucV (fst α)) (suc-ord oα)

  -- The one read the seal needs (R-36): the sealed comparison, in the
  -- ambient membership form, proved inside the seal.  `κ-min-at` is its
  -- only consumer, and no exported type names `w`.
  opaque
    unfolding w
    w-lt : (m n : ⟪ sucV (fst α) ⟫)
         → SWO._<∙_ w m n ≡ ⟨ ⟪ sucV (fst α) ⟫↪ m ∈ˢ ⟪ sucV (fst α) ⟫↪ n ⟩
    w-lt m n = refl

  self : ⟪ sucV (fst α) ⟫
  self = fiber (sucV (fst α)) (self∈sucV (fst α)) .fst

  self-eq : ⟪ sucV (fst α) ⟫↪ self ≡ fst α
  self-eq = fiber (sucV (fst α)) (self∈sucV (fst α)) .snd

  idInj : ⟪ fst α ⟫ ↪ ⟪ fst α ⟫
  idInj = (λ x → x) , (λ x y e → e)

  nonempty : ∥ Σ[ b ∈ ⟪ sucV (fst α) ⟫ ] ⟨ InjP' b ⟩ ∥₁
  nonempty = ∣ self , subst (λ v → ∥ ⟪ fst α ⟫ ↪ ⟪ v ⟫ ∥₁) (sym self-eq)
                ∣ idInj ∣₁ ∣₁

  least : Σ[ γ ∈ ⟪ sucV (fst α) ⟫ ] IsLeast w InjP' γ
  least = leastOf w lem InjP' nonempty

  γ-card : ⟪ sucV (fst α) ⟫
  γ-card = fst least

  κ : S
  κ = up γ-card

  oκ : IsOrd (fst κ)
  oκ = mem-ord {A = sucV (fst α)} (suc-ord oα) (fst κ)
         (member (sucV (fst α)) γ-card)

  κ∈sα : ⟨ fst κ ∈ˢ sucV (fst α) ⟩
  κ∈sα = member (sucV (fst α)) γ-card

  -- The witness, an injection, still truncated, still not an hProp.
  κ-inj : ∥ ⟪ fst α ⟫ ↪ ⟪ fst κ ⟫ ∥₁
  κ-inj = fst (snd least)

  κ-min : (b : ⟪ sucV (fst α) ⟫) → ⟨ InjP' b ⟩
        → (SWO._<∙_ w b γ-card → Empty.⊥)
  κ-min = snd (snd least)

  κ-min-at : (δ : S) → ⟨ fst δ ∈ˢ fst κ ⟩
           → ∥ ⟪ fst α ⟫ ↪ ⟪ fst δ ⟫ ∥₁ → Empty.⊥
  κ-min-at δ δ∈κ α↪δ = κ-min b bInjP b<γ
    where
    δ∈sα : ⟨ fst δ ∈ˢ sucV (fst α) ⟩
    δ∈sα = suc-ord oα .fst {x = fst κ} {y = fst δ} δ∈κ κ∈sα
    b : ⟪ sucV (fst α) ⟫
    b = fiber (sucV (fst α)) δ∈sα .fst
    bδ : ⟪ sucV (fst α) ⟫↪ b ≡ fst δ
    bδ = fiber (sucV (fst α)) δ∈sα .snd
    bInjP : ⟨ InjP' b ⟩
    bInjP = subst (λ v → ∥ ⟪ fst α ⟫ ↪ ⟪ v ⟫ ∥₁) (sym bδ) α↪δ
    b<γ : SWO._<∙_ w b γ-card
    b<γ = transport (λ i → sym (w-lt b γ-card) i)
            (subst (λ z → ⟨ z ∈ˢ fst κ ⟩) (sym bδ) δ∈κ)
```

The stage-bound device shared by the two internal faces (A3 and A4):
for an L-element, the ordinal β that `stageBound` returns, its
ordinal certificate, and the crossing `up` that lifts a member of
`Lset β` to an L-element.

```agda
module SiteBound (a : S) where

  β : V ℓ
  β = stageBound (fst a) (snd a) .fst

  oβ : IsOrd β
  oβ = stageBound (fst a) (snd a) .snd .fst

  up : Mem (Lset β) → S
  up (x , m) = x , Lset→isL β oβ x m
```

A3.  The canonical selection, β supplied by `stageBound`.

  The selection `leastOf (orderAt β oβ)` over the bare graph atoms
  (A2's `svAt`, `domAt`, `injAt`), with β and oβ PRODUCED rather than
  assumed.  The module has no β hypothesis.

```agda
module Canonical (a : S) (D : S) where

  open SiteBound a

  -- A2's predicate, over the graph carried by a member of the tower.
  Good : Mem (Lset β) → Ω
  Good A = ((up A ∷ D ∷ []) ⊨ svAt zero)
         ⊓ (((up A ∷ D ∷ []) ⊨ domAt zero (suc zero))
         ⊓  ((up A ∷ D ∷ []) ⊨ injAt zero))

  module _ (h : ∥ Σ[ A ∈ Mem (Lset β) ] ⟨ Good A ⟩ ∥₁) where

    chosen : Σ[ A ∈ Mem (Lset β) ] IsLeast (orderAt β oβ) Good A
    chosen = leastOf (orderAt β oβ) lem Good h

    F₀ : S
    F₀ = up (fst chosen)

    good : ⟨ Good (fst chosen) ⟩
    good = fst (snd chosen)

    sv : ⟨ (F₀ ∷ D ∷ []) ⊨ svAt zero ⟩
    sv = fst good

    dm : ⟨ (F₀ ∷ D ∷ []) ⊨ domAt zero (suc zero) ⟩
    dm = fst (snd good)

    ij : ⟨ (F₀ ∷ D ∷ []) ⊨ injAt zero ⟩
    ij = snd (snd good)
```

A4.  The internal cardinal, and the internal least cardinal.

  `InjCode` is A2's three conjuncts plus the value-in-b clause, the
  four pieces A2's `Small` readback consumes.  `IsCardinalL` is the
  internal cardinal: no smaller L-element admits a code.  The trophy
  statement names both; the internal least-of selects δ by the sealed
  `orderAt`, with the truncated L-element existential inside the
  predicate.

```agda
InjCode : S → S → S → Type (ℓ-suc ℓ)
InjCode F a b =
    ⟨ (F ∷ a ∷ []) ⊨ svAt zero ⟩
  × ⟨ (F ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩
  × ⟨ (F ∷ a ∷ []) ⊨ injAt zero ⟩
  × ((x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst b ⟩)

IsCardinalL : S → Type (ℓ-suc ℓ)
IsCardinalL κ =
  (δ : S) → ⟨ fst δ ∈ fst κ ⟩
          → (∥ Σ[ F ∈ S ] InjCode F κ δ ∥₁ → Empty.⊥)

module InternalLeastCard (κ : S) (oκ : IsOrd (fst κ)) where

  open SiteBound κ

  Good : Mem (Lset β) → hProp (ℓ-suc ℓ)
  Good δ = (∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) κ (up δ) ∥₁) , squash₁

  module Selected
    (nonempty : ∥ Σ[ δ ∈ Mem (Lset β) ] ⟨ Good δ ⟩ ∥₁)
    where

    least : Σ[ δ ∈ Mem (Lset β) ] IsLeast (orderAt β oβ) Good δ
    least = leastOf (orderAt β oβ) lem Good nonempty

    δ-card : Mem (Lset β)
    δ-card = fst least

    -- the internal least cardinal, as an L-element
    δᴸ : S
    δᴸ = up δ-card

    -- the witness: some L-element codes ⟪κ⟫ ↪ ⟪δᴸ⟫, still truncated
    δ-inj : ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) κ δᴸ ∥₁
    δ-inj = fst (snd least)

    -- leastness at a member of δᴸ: a smaller δ' with a code is absurd
    δ-min : (b : Mem (Lset β)) → ⟨ Good b ⟩
          → (SWO._<∙_ (orderAt β oβ) b δ-card → Empty.⊥)
    δ-min = snd (snd least)
```

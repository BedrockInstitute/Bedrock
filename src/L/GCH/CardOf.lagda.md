# Every ordinal of L has an internal cardinal

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.CardOf {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member; fiber )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; isL; isL-trans )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Cardinal {ℓ} lem using ( IsCardinalL; module LeastCardInjL )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( IsLeast; leastOf; module SWO )
open import L.GCH {ℓ} lem using ( InjL )
open import L.GCH.Assembly {ℓ} lem using ( inclusion-coded; injl-trans )

open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum using ( inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
```

The V-carrier: the ambient membership lives here.

```agda
module SV = hPropStructure 𝒮ᵥ using ( S )
```

The L-carrier: `InjL` and `IsCardinalL` live here.

```agda
module SL = hPropStructure 𝒮ʟ using ( S )
```

THE THEOREM.  Every ordinal α of L has an internal cardinal: an
ordinal L-cardinal μ ⊆ α with α and μ injecting into each other
inside L.

  Select, by `leastOf` over the ordinal well-order `w` of
  `LeastCardInjL` on ⟪ sucV α ⟫ (the order is ∈ itself, `w-lt`), the
  least member μ that α injects into internally.  The set is
  non-empty: α is a member of `sucV α` and the inclusion α ⊆ α is an
  internal injection.  μ is an ordinal because every member of
  `sucV α` is.  μ is an L-cardinal: a γ ∈ μ with μ ↪ γ gives α ↪ γ by
  composition, and γ is a member of `sucV α` below μ, against
  leastness.  μ ⊆ α because μ ∈ α or μ ≡ α, and μ ↪ α is that
  inclusion.

  The stage order `orderAt` is not used: no exported lemma relates ∈
  on ordinals to `orderAt`, so the selection runs on the ordinal
  well-order instead.

  Three measured cures, at this site.  (1) The predicate carries the
  L-element and its index equation, so no `InjL` is ever transported
  along a path in the carrier: the first draft, which did, ran 48 min
  at 8.6 GB before it was killed.  (2) The level-hood of `sucV α` is
  a sealed proof of a proposition.  (3) μ ⊆ α is read off `ord-tri`,
  not `∈sucV-elim`: with the selected member as its point, that
  eliminator alone exceeded a 120 s cap, and this whole module checks
  in about 7 s without it.

```agda
cardOf :
    (α : SL.S) → IsOrd (fst α)
  → ∥ Σ[ μ ∈ SL.S ]
       ( IsOrd (fst μ) × IsCardinalL μ
       × ((z : SV.S) → ⟨ z ∈ˢ fst μ ⟩ → ⟨ z ∈ˢ fst α ⟩)
       × InjL α μ × InjL μ α ) ∥₁
cardOf α oα = ∣ μ , oμ , cardμ , μ⊆α , α↪μ , μ↪α ∣₁
  where
  module LC = LeastCardInjL α oα using ( hSucα; self; self-eq; w; w-lt )

  T : SV.S
  T = sucV (fst α)

  oT : IsOrd T
  oT = suc-ord oα

  -- Sealed: a proof of a proposition, never to be normalised.
  opaque
    hT : ⟨ isL T ⟩
    hT = LC.hSucα

  -- The crossing from the tower at T to the L-carrier.
  upL : ⟪ T ⟫ → SL.S
  upL b = ⟪ T ⟫↪ b , isL-trans (member T b) hT

  -- The predicate: some L-element at the member's index that α injects
  -- into internally.  The index equation rides along, so the injection
  -- is never transported.
  Good : ⟪ T ⟫ → hProp (ℓ-suc ℓ)
  Good b = ∥ Σ[ δ ∈ SL.S ] ((fst δ ≡ ⟪ T ⟫↪ b) × InjL α δ) ∥₁ , squash₁

  -- α itself is a member, and the identity inclusion is coded.
  selfGood : ⟨ Good LC.self ⟩
  selfGood = ∣ α , sym LC.self-eq , inclusion-coded α α (λ z z∈α → z∈α) ∣₁

  nonempty : ∥ Σ[ b ∈ ⟪ T ⟫ ] ⟨ Good b ⟩ ∥₁
  nonempty = ∣ LC.self , selfGood ∣₁

  least : Σ[ b ∈ ⟪ T ⟫ ] IsLeast LC.w Good b
  least = leastOf LC.w lem Good nonempty

  m : ⟪ T ⟫
  m = fst least

  μ : SL.S
  μ = upL m

  μ∈T : ⟨ fst μ ∈ˢ T ⟩
  μ∈T = member T m

  oμ : IsOrd (fst μ)
  oμ = mem-ord {A = T} oT (fst μ) μ∈T

  -- The selected witness, moved to μ through the index equation by an
  -- inclusion: only memberships are substituted.
  α↪μ : InjL α μ
  α↪μ = PT.rec squash₁ from (fst (snd least))
    where
    from : Σ[ δ ∈ SL.S ] ((fst δ ≡ ⟪ T ⟫↪ m) × InjL α δ) → InjL α μ
    from (δ , e , α↪δ) =
      injl-trans α δ μ α↪δ
        (inclusion-coded δ μ (λ z z∈δ → subst (λ v → ⟨ z ∈ˢ v ⟩) e z∈δ))

  -- Leastness, read at a member of μ.
  cardμ : IsCardinalL μ
  cardμ δ δ∈μ μ↪δ = snd (snd least) b bGood b<m
    where
    δ∈T : ⟨ fst δ ∈ˢ T ⟩
    δ∈T = oT .fst {x = fst μ} {y = fst δ} δ∈μ μ∈T
    b : ⟪ T ⟫
    b = fiber T δ∈T .fst
    bδ : ⟪ T ⟫↪ b ≡ fst δ
    bδ = fiber T δ∈T .snd
    bGood : ⟨ Good b ⟩
    bGood = ∣ δ , sym bδ , injl-trans α μ δ α↪μ μ↪δ ∣₁
    b<m : SWO._<∙_ LC.w b m
    b<m = transport (λ i → sym (LC.w-lt b m) i)
            (subst (λ z → ⟨ z ∈ˢ fst μ ⟩) (sym bδ) δ∈μ)

  -- Trichotomy against α.  Below or equal, μ ⊆ α by transitivity.
  -- Above is absurd: α is itself a member of `sucV α` that α injects
  -- into, and α ∈ μ puts it below μ in `w`, against leastness.
  μ⊆α : (z : SV.S) → ⟨ z ∈ˢ fst μ ⟩ → ⟨ z ∈ˢ fst α ⟩
  μ⊆α = go (ord-tri (fst μ) oμ (fst α) oα)
    where
    go : Tri (fst μ) (fst α) → (z : SV.S) → ⟨ z ∈ˢ fst μ ⟩ → ⟨ z ∈ˢ fst α ⟩
    go (inl μ∈α)       z z∈μ = oα .fst z∈μ μ∈α
    go (inr (inl e))   z z∈μ = subst (λ v → ⟨ z ∈ˢ v ⟩) e z∈μ
    go (inr (inr α∈μ)) z z∈μ =
      Empty.rec (snd (snd least) LC.self selfGood
        (transport (λ i → sym (LC.w-lt LC.self m) i)
          (subst (λ v → ⟨ v ∈ˢ fst μ ⟩) (sym LC.self-eq) α∈μ)))

  μ↪α : InjL μ α
  μ↪α = inclusion-coded μ α μ⊆α
```

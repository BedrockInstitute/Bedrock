{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett )

module ProbeT198 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Relabelling using ( mapFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; module VCode )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒟ₒ; 𝒟ₒ-intro )
open import L.Rud.Images {ℓ} using ( F10 )
open import L.Rud.Step {ℓ} lem A using ( Sset; Sset-trans; Sset-mem; Jset-rud )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit; isLimit-ord )
open import L.Rud.OrdBlocks {ℓ} lem using ( +ω; +ω-limit; +ω-mem )
open import L.Rud.DefInJ {ℓ} lem A using ( Lsuc≡Def; defs-in-limit )
open import L.Rud.SatSets {ℓ} lem A using ( module Sat )
open import L.Rud.SatTable {ℓ} lem A
  using ( module Coded; module Pow; BlockPowLim; blockPow-suc )

open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- The gate's telescope: the successor step's own pair (δ a limit holding C).
module Gate (ζ δ : S) (ordδ : IsOrd δ) (limδ : ⟨ isLimit δ ⟩)
            (L∈ : ⟨ Lset ζ ∈ˢ Sset δ ⟩) where

  C : S
  C = Lset ζ

  γ : S
  γ = +ω δ

  limγ : ⟨ isLimit γ ⟩
  limγ = +ω-limit δ ordδ

  C∈γ : ⟨ Lset ζ ∈ˢ Sset γ ⟩
  C∈γ = Sset-trans γ {x = Sset δ} {y = Lset ζ} L∈
    (Sset-mem {α = γ} {β = δ} (+ω-mem δ))

  -- 1. The machinery assembles: given R and sr, blockPowLim is blockPow-suc
  --    at the step's own pair, read at the successor collapse.
  assembly : (R : S) → Coded.SatRelation γ limγ C R
           → ⟨ 𝒟ₒ C ∈ˢ Sset γ ⟩
  assembly R sr = subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) (Lsuc≡Def ζ)
    (blockPow-suc δ ordδ limδ ζ L∈ R sr)

  -- 2. The delivered half (DefInJ): every slice is a member of the level.
  slice∈γ : (φ : Formula ⟪ C ⟫ 1) → ⟨ DefOf.defSet C φ ∈ˢ Sset γ ⟩
  slice∈γ φ = defs-in-limit ζ γ limγ C∈γ (DefOf.defSet C φ)
    (𝒟ₒ-intro C (DefOf.defSet C φ) ∣ φ , refl ∣₁)

  -- 3. The description engine, re-derived on survivors: a set definable over
  --    a stage below γ is a member of Sset γ (the archived described∈J shape).
  described∈J : (y : S)
              → ∥ Σ[ μ ∈ S ] (⟨ μ ∈ˢ γ ⟩
                   × (Σ[ Φ ∈ Formula ⟪ Sset μ ⟫ 1 ]
                        (DefOf.defSet (Sset μ) Φ ≡ y))) ∥₁
              → ⟨ y ∈ˢ Sset γ ⟩
  described∈J y = PT.rec (snd (y ∈ˢ Sset γ)) go
    where
    go : Σ[ μ ∈ S ] (⟨ μ ∈ˢ γ ⟩
           × (Σ[ Φ ∈ Formula ⟪ Sset μ ⟫ 1 ] (DefOf.defSet (Sset μ) Φ ≡ y)))
       → ⟨ y ∈ˢ Sset γ ⟩
    go (μ , μ∈γ , Φ , q) = subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) q (defSet∈J μ μ∈γ Φ)
      where
      defSet∈J : (μ : S) → ⟨ μ ∈ˢ γ ⟩ → (Φ : Formula ⟪ Sset μ ⟫ 1)
               → ⟨ DefOf.defSet (Sset μ) Φ ∈ˢ Sset γ ⟩
      defSet∈J μ μ∈γ Φ = Sμ.defSet-InJ Φ
        where
        module Sμ = Sat (Sset μ)
          (λ x y x∈y y∈W → Sset-trans μ {x = y} {y = x} x∈y y∈W)
          (λ z → ⟨ z ∈ˢ Sset γ ⟩)
          (λ a b hb a∈b → Sset-trans γ {x = b} {y = a} a∈b hb)
          (Jset-rud γ limγ)
          (Sset-mem {α = γ} {β = μ} μ∈γ)

  -- 4. The code family, re-derived on survivors from the delivered coding.
  code : ∀ {n} → Formula ⟪ C ⟫ n → S
  code φ = VCode.⌜ mapFo ⟪ C ⟫↪ φ ⌝

  code₁ : Formula ⟪ C ⟫ 1 → S
  code₁ = code

  codeSet : ℕ → S
  codeSet k = sett (Formula ⟪ C ⟫ k) code

  code∈codeSet : (k : ℕ) (φ : Formula ⟪ C ⟫ k) → ⟨ code φ ∈ˢ codeSet k ⟩
  code∈codeSet k φ = ∣ φ , refl ∣₁

  codeSet-out : (k : ℕ) (x : S) → ⟨ x ∈ˢ codeSet k ⟩
              → ∥ Σ[ φ ∈ Formula ⟪ C ⟫ k ] (code φ ≡ x) ∥₁
  codeSet-out k x h = h

  -- 5. The covering obligation: the arity-one code set as a member of the
  --    block, reduced to one object-language description over a stage below.
  K-desc : Type (ℓ-suc ℓ)
  K-desc = ∥ Σ[ μ ∈ S ] (⟨ μ ∈ˢ γ ⟩
             × (Σ[ Φ ∈ Formula ⟪ Sset μ ⟫ 1 ]
                  (DefOf.defSet (Sset μ) Φ ≡ codeSet 1))) ∥₁

  K∈γ : K-desc → ⟨ codeSet 1 ∈ˢ Sset γ ⟩
  K∈γ = described∈J (codeSet 1)

  -- The covering half is the code set plus its membership and nothing else:
  -- the two Covers directions are the sett's own, by construction.
  cover : ⟨ codeSet 1 ∈ˢ Sset γ ⟩
        → Σ[ K ∈ S ] Σ[ cod ∈ Pow.Cod C ]
             (⟨ K ∈ˢ Sset γ ⟩ × Pow.Covers C K cod)
  cover hK = codeSet 1 , (code₁ , (hK , (code∈codeSet 1 , codeSet-out 1)))

  -- 6. The relation obligation: R as a member of the block with the slices.
  RelObl : Type (ℓ-suc ℓ)
  RelObl = Σ[ R ∈ S ] (⟨ R ∈ˢ Sset γ ⟩ × Pow.Slices C R code₁)

  -- 7. The instance from the two obligations: the machinery consumes exactly
  --    these two, and nothing else.
  instance-from : K-desc → RelObl → Σ[ R ∈ S ] Coded.SatRelation γ limγ C R
  instance-from dK (R , hR , sl) =
    R , (hR , (codeSet 1 , (code₁ , (K∈γ dK , (cover-mem , sl)))))
    where
    cover-mem : Pow.Covers C (codeSet 1) code₁
    cover-mem = (code∈codeSet 1 , codeSet-out 1)

  -- Positive control: the two halves together land the step, green.
  control : K-desc → RelObl → ⟨ 𝒟ₒ C ∈ˢ Sset γ ⟩
  control dK ro = assembly (instance-from dK ro .fst) (instance-from dK ro .snd)

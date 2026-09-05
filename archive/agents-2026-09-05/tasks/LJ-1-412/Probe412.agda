{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.412] PROBE.  The coded descent, from the case hypothesis the
-- band recursion holds.  It runs in agents/tasks/LJ-1-412/ and lands
-- nothing in src/.
--
-- W3, FIRST: `not-card-gives`.  State step 1 alone, run it, and report
-- its code lines before writing step 2.
--
-- `[LJ-1.411]`'s `code-as-data` is a MODULE HYPOTHESIS, not imported
-- and not rebuilt.  That task is not in this tree.  The type is the
-- type the brief names.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-412.Probe412 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; isL; isL-trans )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Stage {ℓ} lem using ( leastOrd )
open import L.InjChain {ℓ} lem using ( finite-excl-ω )
open import L.Cardinal {ℓ} lem using ( _↪_; InjCode; IsCardinalL )
open import L.Coding.Injection {ℓ} lem using ( module Small )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sigma using ( Σ≡Prop )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- W3.  Step 1 alone.  Generic in `κ`.  No numeral, no named cardinal.
-- One `lem` at the truncation: if the truncation is refuted, then every
-- `δ` with the membership refutes its own code existence, which is
-- `IsCardinalL κ` by definition (src/L/Cardinal.lagda.md:230-233).
-- Shape of [LJ-1.394]'s `amb-gives-merely` (Probe394.agda:144-154).
-- Nothing of Probe394 is imported.
-- =====================================================================

not-card-gives :
    (κ : S) → (IsCardinalL κ → Empty.⊥)
  → ∥ Σ[ δ ∈ S ] (⟨ fst δ ∈ˢ fst κ ⟩
                 × ∥ Σ[ F ∈ S ] InjCode F κ δ ∥₁) ∥₁
not-card-gives κ ¬card = go (lem Ex)
  where
  Ex : hProp (ℓ-suc ℓ)
  Ex = ∥ Σ[ δ ∈ S ] (⟨ fst δ ∈ˢ fst κ ⟩
                   × ∥ Σ[ F ∈ S ] InjCode F κ δ ∥₁) ∥₁
     , squash₁
  go : ⟨ Ex ⟩ ⊎ (⟨ Ex ⟩ → Empty.⊥) → ⟨ Ex ⟩
  go (inl q) = q
  go (inr nq) = Empty.rec (¬card card)
    where
    card : IsCardinalL κ
    card δ δ∈κ code = nq ∣ δ , δ∈κ , code ∣₁

-- =====================================================================
-- Step 2.  The ordinal form.  `leastOrd` selects an ordinal, so restate
-- step 1 over the AMBIENT carrier (L.Stage reads S from 𝒮ᵥ,
-- src/L/Stage.lagda.md:60).  Generic in `κ`.  Minimality is free and
-- this task does not spend it.
-- =====================================================================

Good : (κ : S) → V ℓ → Ω
Good κ d =
    ∥ Σ[ δ ∈ S ] ((fst δ ≡ d)
                 × ⟨ fst δ ∈ˢ fst κ ⟩
                 × ∥ Σ[ F ∈ S ] InjCode F κ δ ∥₁) ∥₁
  , squash₁

ord-form :
    (κ : S) (oκ : IsOrd (fst κ))
  → ∥ Σ[ δ ∈ S ] (⟨ fst δ ∈ˢ fst κ ⟩
                 × ∥ Σ[ F ∈ S ] InjCode F κ δ ∥₁) ∥₁
  → ∥ Σ[ d ∈ V ℓ ] (IsOrd d × ⟨ Good κ d ⟩) ∥₁
ord-form κ oκ = PT.map
  (λ { (δ , mem , code) →
        fst δ
      , mem-ord {A = fst κ} oκ (fst δ) mem
      , ∣ δ , refl , mem , code ∣₁ })

-- =====================================================================
-- Step 7 helpers.  Rebuild of [LJ-1.410]'s `nofin-at-selected`
-- (Probe410.agda:73-85) and of [LJ-1.398]'s `no-fin-descent`
-- (Probe398.agda:213-220).  Nothing of those probes is imported.
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

comp-inj : {A B C : Type ℓ} → A ↪ B → B ↪ C → A ↪ C
comp-inj (f , injf) (g , injg) =
  (λ x → g (f x)) , λ x y e → injf x y (injg (f x) (f y) e)

nofin-at-selected :
    (κ : S) (oκ : IsOrd (fst κ))
  → ⟨ ω ∈ˢ fst κ ⟩
  → (δ : S)
  → ⟨ fst δ ∈ fst κ ⟩
  → (⟪ fst κ ⟫ ↪ ⟪ fst δ ⟫)
  → ⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥
nofin-at-selected κ oκ ω∈κ δ δ∈κ down δ∈ω =
  let ω↪δ : ⟪ ω ⟫ ↪ ⟪ fst δ ⟫
      ω↪δ = comp-inj (mem-incl (fst κ) ω oκ ω∈κ) down
  in finite-excl-ω (fst δ) (mem-ord {A = fst κ} oκ (fst δ) δ∈κ) δ∈ω
       (λ t → fst ω↪δ t , fst ω↪δ t)
       (λ t u e → snd ω↪δ t u (cong fst e))

-- =====================================================================
-- THE OBLIGATION.  Steps 3-6 under `[LJ-1.411]`'s `code-as-data`.
-- That task is not in this tree.  The hypothesis is still the right
-- telescope.  Nothing of Probe410, Probe402 or Probe411 is imported.
-- `module Small` is opened at the three sets, two projections, as
-- [LJ-1.402] measured (Probe402.agda:81).  The band membership is not
-- in the type (Probe398.agda:206).
-- =====================================================================

module _
  (code-as-data : (a b : S) → ∥ Σ[ F ∈ S ] InjCode F a b ∥₁
               → Σ[ F ∈ S ] InjCode F a b)
  where

  coded-descent :
      (κ : S) (oκ : IsOrd (fst κ)) → ⟨ ω ∈ˢ fst κ ⟩
    → (IsCardinalL κ → Empty.⊥)
    → Σ[ δ ∈ S ] ( ⟨ fst δ ∈ˢ fst κ ⟩
                 × (⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥)
                 × (⟪ fst κ ⟫ ↪ ⟪ fst δ ⟫) )
  coded-descent κ oκ ω∈κ ¬card = δ₀ , mem , nofin , arrow
    where
    sel = leastOrd (Good κ) (ord-form κ oκ (not-card-gives κ ¬card))
    d₀ : V ℓ
    d₀ = fst sel
    pGood : ⟨ Good κ d₀ ⟩
    pGood = fst (snd (snd sel))

    mem : ⟨ d₀ ∈ˢ fst κ ⟩
    mem = PT.rec (snd (d₀ ∈ˢ fst κ))
      (λ { (δ , e , m , _) → subst (λ w → ⟨ w ∈ˢ fst κ ⟩) e m })
      pGood

    δ₀ : S
    δ₀ = d₀ , isL-trans {x = fst κ} {y = d₀} mem (snd κ)

    code-trunc : ∥ Σ[ F ∈ S ] InjCode F κ δ₀ ∥₁
    code-trunc = PT.rec squash₁
      (λ { (δ , e , _ , c) →
            subst (λ w → ∥ Σ[ F ∈ S ] InjCode F κ w ∥₁)
                  (Σ≡Prop {A = V ℓ} (λ (x : V ℓ) → snd (isL x))
                    {u = δ} {v = δ₀} e)
                  c })
      pGood

    Fcode = code-as-data κ δ₀ code-trunc

    module Sm = Small (fst Fcode) κ δ₀
                  (fst (snd Fcode))
                  (fst (snd (snd Fcode)))
                  (fst (snd (snd (snd Fcode))))
                  (snd (snd (snd (snd Fcode))))

    arrow : ⟪ fst κ ⟫ ↪ ⟪ fst δ₀ ⟫
    arrow = Sm.small , Sm.small-inj

    nofin : ⟨ fst δ₀ ∈ˢ ω ⟩ → Empty.⊥
    nofin = nofin-at-selected κ oκ ω∈κ δ₀ mem arrow

# The environment supply at the concrete site

Step 6's environment supply, landed as a new master that imports
`L.Condensation`. The block lives here, not inside the chapter, because the
chapter's own live lines were what made the same content heap-exhaust
(C-49). The env supply proves that an environment and its components stay
inside the level `Lset lam`; the tower-neutral fields and the
finite-supremum merge close the same carrier generically over `(K, Ktr)`.

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.EnvSupply {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_; ⊤̇; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset; IsOrd )
open import L.Axioms.Numerals {ℓ} using ( numeralL-fst )
open import L.Coding.Model {ℓ}
  using ( consAtL; subValAt; subValSuccAt; tmValAt; envSetAt; envOverAt )
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; pairing-ax; ∅; module InfinitySet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open InfinitySet using ( #_; sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- The names the master's own tail block imports, plus the two names that
-- `L.Condensation` DEFINES and this block consumes.
open import L.Constructible {ℓ} using ( Lset-mono )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Coding.Bound {ℓ} lem using ( module Bound )
open import L.Condensation {ℓ} lem using ( envSetB; module EnvSet )
```

```agda
-- =====================================================================
-- THE ENV SUPPLY, the tower-neutral fields, and the finite-supremum
-- merge.  The master opens hPropStructure 𝒮ʟ, so `S` is the L-carrier
-- and the ambient carrier is V ℓ with Cubical _∈_.
-- =====================================================================

open import V.Hierarchy {ℓ} using ( extensionalV )
open import L.Constructible {ℓ}
  using ( isTransV; Lset-layer; layer-trans; 𝒟ₒ; 𝒟ₒ-intro
        ; ∪-trans; isPropIsTransV )
open import L.Axioms.Basic {ℓ}
  using ( isL-Lset; finSet; Lset-suc; pair∈Lset-suc; sgl∈Lset-suc
        ; module FinOf )
open import L.Coding.Environment {ℓ} using ( env; cons )
open import L.Coding.Model {ℓ}
  using ( tmValAt-out; subValAt-adequate; subValSuccAt-adequate
        ; consAtL-adequate; extAt-out; extAt-in )
open import L.Coding.Bound {ℓ} lem using ( Lset-out′ )
open import L.Coding.Key {ℓ} lem using ( envSetNumeral∈ )
open import L.Coding.Sound {ℓ} lem using ( module NumeralFromGeneric )
open import L.Coding.EnvSet {ℓ} lem using ( envSet; module Generic )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Ordinal {ℓ} using ( suc-ord; mem-ord; ∅-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.StageArith {ℓ} lem using ( sucIter )
open import V.Model {ℓ} using ( self∈sucV )
open import Cubical.Data.Sigma using ( _,_; Σ≡Prop )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.FinData.FiniteChoice using ( choice )
open import Cubical.Data.Vec using ( Vec; lookup )
import Cubical.Data.Sum as Sum
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ⋃_; union-ax; _∪_ )
open InfinitySet using ( ω )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈-asFiber; extensionality; _⊆_; _∈ₛ_ )

-- Named Fin indices, definitionally the same `suc` chains the field
-- types write.
pattern one   = suc zero
pattern two   = suc one
pattern three = suc two
pattern four  = suc three
pattern five  = suc four
pattern six   = suc five
pattern seven = suc six
pattern eight = suc seven
pattern nine  = suc eight

-- =====================================================================
-- THE ENV SUPPLY at the concrete site ([LJ-1.254] + [LJ-1.257]).
-- K = Lset lam, carrier B₀ = LsetS gam ordγ.  The collapsed five
-- envK-* and the four envInK-* plus someEnv are the [LJ-1.257] form.
-- =====================================================================

module SupplyEnv (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  (ω∈γ : ⟨ ω ∈ sucV gam ⟩) where

  module B = Bound lam ordλ succλ ∅∈λ

  σ : V ℓ
  σ = sucV gam

  oσ : IsOrd σ
  oσ = suc-ord ordγ

  σ∈λ : ⟨ σ ∈ lam ⟩
  σ∈λ = succλ gam γ∈λ

  B₀ : S
  B₀ = LsetS gam ordγ

  B₀∈σ : ⟨ fst B₀ ∈ Lset σ ⟩
  B₀∈σ = subst (λ w → ⟨ Lset gam ∈ w ⟩) (sym (Lset-suc gam))
    (𝒟ₒ-intro (Lset gam) (Lset gam) ∣ ⊤̇ , DefA.defSet⊤≡A ∣₁)
    where
    module DefA = DefOf (Lset gam)

  genEq : (ar : S) (n : ℕ) → fst ar ≡ # n
        → fst (Generic.envSetGen B₀ ar) ≡ fst (envSet B₀ n)
  genEq ar n arNum =
    cong (λ ar' → fst (Generic.envSetGen B₀ ar'))
      (Σ≡Prop (λ x → (isL x) .snd) arNum)
    ∙ sym (NumeralFromGeneric.derived B₀ n)

  envSetK : (ar : S) (n : ℕ) → fst ar ≡ # n
          → ⟨ fst ar ∈ Lset lam ⟩
          → ⟨ fst (Generic.envSetGen B₀ ar) ∈ Lset lam ⟩
  envSetK ar n arNum ar∈λ =
    Lset-mono {α = lam} {β = sucIter 4 σ} (B.suc^∈λ 4 σ σ∈λ)
      (subst (λ w → ⟨ w ∈ Lset (sucIter 4 σ) ⟩) (sym (genEq ar n arNum))
        (envSetNumeral∈ σ oσ ω∈γ B₀ n B₀∈σ))

  union∈Lset-suc : (σ x : V ℓ) → ⟨ x ∈ Lset σ ⟩ → ⟨ ⋃ x ∈ Lset (sucV σ) ⟩
  union∈Lset-suc σ x x∈ =
    subst (λ w → ⟨ ⋃ x ∈ w ⟩) (sym (Lset-suc σ)) union∈𝒟ₒ
    where
    module DefA = DefOf (Lset σ)
    Atrans = layer-trans (Lset-layer σ)
    mₓ = ∈-asFiber {a = x} {b = Lset σ} x∈ .fst
    qₓ : ⟪ Lset σ ⟫↪ mₓ ≡ x
    qₓ = ∈-asFiber {a = x} {b = Lset σ} x∈ .snd

    φ : Formula ⟪ Lset σ ⟫ 1
    φ = ∃̇∈ (con mₓ) (var (suc zero) ∈̇ var zero)

    defSet≡ : DefA.defSet φ ≡ ⋃ x
    defSet≡ = extensionality (DefA.defSet φ) (⋃ x) (sub₁ , sub₂)
      where
      sub₁ : ⟨ DefA.defSet φ ⊆ ⋃ x ⟩
      sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ ⋃ x))
        (λ { ((m , h) , q) →
          subst (λ w → ⟨ w ∈ₛ ⋃ x ⟩) q
            (PT.rec (snd (⟪ Lset σ ⟫↪ m ∈ₛ ⋃ x))
              (λ { (v , (fstv∈mₓ , m∈fstv)) →
                union-ax x (⟪ Lset σ ⟫↪ m) .snd
                  ∣ fst v
                  , ( ∈∈ₛ {a = fst v} {b = x} .fst
                        (subst (λ w → ⟨ fst v ∈ w ⟩) qₓ fstv∈mₓ)
                    , ∈∈ₛ {a = ⟪ Lset σ ⟫↪ m} {b = fst v} .fst m∈fstv ) ∣₁ })
              (subst ⟨_⟩ (DefA.defSet-mem φ m) ∣ (m , h) , refl ∣₁)) })
        (∈∈ₛ {a = y} {b = DefA.defSet φ} .snd y∈ₛ)
      sub₂ : ⟨ ⋃ x ⊆ DefA.defSet φ ⟩
      sub₂ y y∈ₛ = PT.rec (snd (y ∈ₛ DefA.defSet φ))
        (λ { (v , (v∈ₛx , y∈ₛv)) → member v v∈ₛx y∈ₛv })
        (union-ax x y .fst y∈ₛ)
        where
        member : (v : V ℓ) → ⟨ v ∈ₛ x ⟩ → ⟨ y ∈ₛ v ⟩
               → ⟨ y ∈ₛ DefA.defSet φ ⟩
        member v v∈ₛx y∈ₛv =
          subst (λ w → ⟨ w ∈ₛ DefA.defSet φ ⟩) q'
            (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m'} {b = DefA.defSet φ} .fst
              (subst ⟨_⟩ (sym (DefA.defSet-mem φ m')) sat))
          where
          v∈x = ∈∈ₛ {a = v} {b = x} .snd v∈ₛx
          y∈v = ∈∈ₛ {a = y} {b = v} .snd y∈ₛv
          v∈A = Atrans {x = x} {y = v} v∈x x∈
          y∈A = Atrans {x = v} {y = y} y∈v v∈A
          fib = ∈-asFiber {a = y} {b = Lset σ} y∈A
          m' = fib .fst
          q' = fib .snd
          sat : ⟨ (DefA.ι m' ∷ []) DefA.⊨ᵐ φ ⟩
          sat = ∣ (v , v∈A)
                , ( subst (λ w → ⟨ v ∈ w ⟩) (sym qₓ) v∈x
                  , subst (λ w → ⟨ w ∈ v ⟩) (sym q') y∈v ) ∣₁

    union∈𝒟ₒ : ⟨ ⋃ x ∈ 𝒟ₒ (Lset σ) ⟩
    union∈𝒟ₒ = 𝒟ₒ-intro (Lset σ) (⋃ x) ∣ φ , defSet≡ ∣₁

  sucK : (a : V ℓ) → ⟨ a ∈ Lset lam ⟩ → ⟨ sucV a ∈ Lset lam ⟩
  sucK a a∈ = PT.rec (snd (sucV a ∈ Lset lam)) step (Lset-out′ lam a a∈)
    where
    step : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ lam ⟩ × ⟨ a ∈ Lset (sucV δ) ⟩)
         → ⟨ sucV a ∈ Lset lam ⟩
    step (δ , δ∈ , a∈δ₁) =
      Lset-mono {α = lam} {β = sucV δ₃}
        δ₄∈λ
        sucV∈
      where
      δ₁ = sucV δ
      δ₂ = sucV (sucV δ)
      δ₃ = sucV (sucV (sucV δ))
      δ₄∈λ : ⟨ sucV δ₃ ∈ lam ⟩
      δ₄∈λ = succλ δ₃ (succλ δ₂ (succλ δ₁ (succλ δ δ∈)))
      a∈δ₂ : ⟨ a ∈ Lset δ₂ ⟩
      a∈δ₂ = Lset-mono {α = δ₂} {β = δ₁} (self∈sucV δ₁) a∈δ₁
      sgl∈δ₂ : ⟨ ⁅ a ⁆s ∈ Lset δ₂ ⟩
      sgl∈δ₂ = sgl∈Lset-suc δ₁ a a∈δ₁
      pair∈δ₃ : ⟨ ⁅ a , ⁅ a ⁆s ⁆ ∈ Lset δ₃ ⟩
      pair∈δ₃ = pair∈Lset-suc δ₂ a ⁅ a ⁆s a∈δ₂ sgl∈δ₂
      sucV∈ : ⟨ sucV a ∈ Lset (sucV δ₃) ⟩
      sucV∈ = union∈Lset-suc δ₃ ⁅ a , ⁅ a ⁆s ⁆ pair∈δ₃

  -- A numeral arity lies in the level.
  #∈λ : (n : ℕ) → ⟨ # n ∈ Lset lam ⟩
  #∈λ n = subst (λ w → ⟨ w ∈ Lset lam ⟩) (numeralL-fst n) (B.num∈λ n)

  -- L3: a satisfaction of `envSetAt` identifies the environment slot
  -- with the generic environment set.
  envSetAt-ident : {k : ℕ} (γ : Vec S k) (Ei di bi : Fin k)
                 → ⟨ γ ⊨ envSetAt Ei di bi ⟩
                 → fst (lookup Ei γ) ≡ fst (Generic.envSetGen (lookup bi γ) (lookup di γ))
  envSetAt-ident γ Ei di bi h =
    extensionalV (λ w → ⇔toPath (fwd w) (bwd w))
    where
    module G = Generic (lookup bi γ) (lookup di γ)
    φ : Formula S (suc _)
    φ = envOverAt zero (suc di) (suc bi)
    fwd : (w : V ℓ) → ⟨ w ∈ fst (lookup Ei γ) ⟩ → ⟨ w ∈ fst (G.envSetGen) ⟩
    fwd w hw = G.envSetGen-in z
      (G.powamb-in z (G.envSubset γ di bi refl refl z h₁))
      (G.backToFo γ di bi refl refl z h₁)
      where
      z : S
      z = w , isL-trans {x = fst (lookup Ei γ)} {y = w} hw (lookup Ei γ .snd)
      h₁ : ⟨ (z ∷ γ) ⊨ φ ⟩
      h₁ = extAt-out Ei φ γ h z hw
    bwd : (w : V ℓ) → ⟨ w ∈ fst (G.envSetGen) ⟩ → ⟨ w ∈ fst (lookup Ei γ) ⟩
    bwd w hw = extAt-in Ei φ γ h z h₂
      where
      z : S
      z = w , isL-trans {x = fst (G.envSetGen)} {y = w} hw (G.envSetGen .snd)
      h₂ : ⟨ (z ∷ γ) ⊨ φ ⟩
      h₂ = G.foSat γ di bi refl refl z (G.envSetGen-out z hw)

  -- L4: a satisfaction of `envOverAt` puts the environment into the
  -- generic environment set.
  envOverAt-in : {k : ℕ} (γ : Vec S k) (di bi : Fin k)
               → (z : S) → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc di) (suc bi) ⟩
               → ⟨ fst z ∈ fst (Generic.envSetGen (lookup bi γ) (lookup di γ)) ⟩
  envOverAt-in γ di bi z h =
    G.envSetGen-in z (G.powamb-in z (G.envSubset γ di bi refl refl z h))
      (G.backToFo γ di bi refl refl z h)
    where
    module G = Generic (lookup bi γ) (lookup di γ)

  -- transK, at the concrete site: the level is transitive.
  transK : (x a : S) → ⟨ fst x ∈ fst a ⟩ → ⟨ fst a ∈ Lset lam ⟩
         → ⟨ fst x ∈ Lset lam ⟩
  transK x a hx ha = layer-trans (Lset-layer lam) hx ha

  -- envK-gen: the ONE slot-generic shell behind the five envK-*.
  envK-gen : {k : ℕ} (γ : Vec S k) (Ei di bi : Fin k)
           → lookup bi γ ≡ B₀
           → ∥ Σ[ n ∈ ℕ ] (fst (lookup di γ) ≡ # n) ∥₁
           → ⟨ γ ⊨ envSetAt Ei di bi ⟩
           → ⟨ fst (lookup Ei γ) ∈ Lset lam ⟩
  envK-gen γ Ei di bi qb arNum h =
    PT.rec (snd (fst (lookup Ei γ) ∈ Lset lam)) (λ { (n , arn) → go n arn }) arNum
    where
    go : (n : ℕ) → fst (lookup di γ) ≡ # n → ⟨ fst (lookup Ei γ) ∈ Lset lam ⟩
    go n arn = subst (λ w → ⟨ w ∈ Lset lam ⟩) (sym ident)
      (envSetK (lookup di γ) n arn (subst (λ w → ⟨ w ∈ Lset lam ⟩) (sym arn) (#∈λ n)))
      where
      ident : fst (lookup Ei γ) ≡ fst (Generic.envSetGen B₀ (lookup di γ))
      ident = subst (λ B → fst (lookup Ei γ) ≡ fst (Generic.envSetGen B (lookup di γ)))
               qb (envSetAt-ident γ Ei di bi h)

  envK-mem : (yc b a ar c E : S)
           → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ B₀ ∷ []) ⊨
               envSetAt zero (suc (suc (suc (suc zero))))
                             (suc (suc (suc (suc (suc (suc zero)))))) ⟩
           → ⟨ fst E ∈ Lset lam ⟩
  envK-mem yc b a ar c E arNum h =
    envK-gen (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ B₀ ∷ [])
      zero (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc zero))))))
      refl arNum h

  envK-neg : (ya yc a ar c E : S)
           → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ B₀ ∷ []) ⊨
               envSetAt zero (suc (suc (suc (suc zero))))
                             (suc (suc (suc (suc (suc (suc zero)))))) ⟩
           → ⟨ fst E ∈ Lset lam ⟩
  envK-neg ya yc a ar c E arNum h =
    envK-gen (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ B₀ ∷ [])
      zero (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc zero))))))
      refl arNum h

  envK-top : (yc a ar c E : S)
           → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → ⟨ (E ∷ yc ∷ a ∷ ar ∷ c ∷ B₀ ∷ []) ⊨
               envSetAt zero (suc (suc (suc zero)))
                             (suc (suc (suc (suc (suc zero))))) ⟩
           → ⟨ fst E ∈ Lset lam ⟩
  envK-top yc a ar c E arNum h =
    envK-gen (E ∷ yc ∷ a ∷ ar ∷ c ∷ B₀ ∷ [])
      zero (suc (suc (suc zero))) (suc (suc (suc (suc (suc zero)))))
      refl arNum h

  envK-imp : (E yb ya yc b a ar c : S)
           → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ B₀ ∷ []) ⊨
               envSetAt zero (suc (suc (suc (suc (suc (suc zero))))))
                             (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⟩
           → ⟨ fst E ∈ Lset lam ⟩
  envK-imp E yb ya yc b a ar c arNum h =
    envK-gen (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ B₀ ∷ [])
      zero (suc (suc (suc (suc (suc (suc zero))))))
           (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
      refl arNum h

  envK-allin : (E ya yc b a ar c : S)
             → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ B₀ ∷ []) ⊨
                 envSetAt zero (suc (suc (suc (suc (suc zero)))))
                               (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
             → ⟨ fst E ∈ Lset lam ⟩
  envK-allin E ya yc b a ar c arNum h =
    envK-gen (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ B₀ ∷ [])
      zero (suc (suc (suc (suc (suc zero)))))
           (suc (suc (suc (suc (suc (suc (suc zero)))))))
      refl arNum h

  -- envInK-*: z ∈ K from a NUMERAL arity, ar ∈ K and ⊨ envOverAt.
  envInK-gen : {k : ℕ} (γ : Vec S k) (di bi : Fin k)
             → lookup bi γ ≡ B₀
             → ∥ Σ[ n ∈ ℕ ] (fst (lookup di γ) ≡ # n) ∥₁
             → ⟨ fst (lookup di γ) ∈ Lset lam ⟩
             → (z : S) → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc di) (suc bi) ⟩
             → ⟨ fst z ∈ Lset lam ⟩
  envInK-gen γ di bi qb arNum arK z h =
    transK z (Generic.envSetGen B₀ (lookup di γ))
      (subst (λ B → ⟨ fst z ∈ fst (Generic.envSetGen B (lookup di γ)) ⟩) qb
        (envOverAt-in γ di bi z h))
      (PT.rec (snd (fst (Generic.envSetGen B₀ (lookup di γ)) ∈ Lset lam))
        (λ { (n , arn) → envSetK (lookup di γ) n arn arK }) arNum)

  envInK-mem : (yc b a ar c E : S)
             → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
             → ⟨ fst ar ∈ Lset lam ⟩
             → (z : S) → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ B₀ ∷ []) ⊨
                 envOverAt zero (suc (suc (suc (suc (suc zero)))))
                               (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
             → ⟨ fst z ∈ Lset lam ⟩
  envInK-mem yc b a ar c E arNum arK z h =
    envInK-gen (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ B₀ ∷ [])
      (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc zero))))))
      refl arNum arK z h

  envInK-neg : (ya yc a ar c E : S)
             → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
             → ⟨ fst ar ∈ Lset lam ⟩
             → (z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ B₀ ∷ []) ⊨
                 envOverAt zero (suc (suc (suc (suc (suc zero)))))
                               (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
             → ⟨ fst z ∈ Lset lam ⟩
  envInK-neg ya yc a ar c E arNum arK z h =
    envInK-gen (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ B₀ ∷ [])
      (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc zero))))))
      refl arNum arK z h

  envInK-top : (yc a ar c E : S)
             → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
             → ⟨ fst ar ∈ Lset lam ⟩
             → (z : S) → ⟨ (z ∷ E ∷ yc ∷ a ∷ ar ∷ c ∷ B₀ ∷ []) ⊨
                 envOverAt zero (suc (suc (suc (suc zero))))
                               (suc (suc (suc (suc (suc (suc zero)))))) ⟩
             → ⟨ fst z ∈ Lset lam ⟩
  envInK-top yc a ar c E arNum arK z h =
    envInK-gen (E ∷ yc ∷ a ∷ ar ∷ c ∷ B₀ ∷ [])
      (suc (suc (suc zero))) (suc (suc (suc (suc (suc zero)))))
      refl arNum arK z h

  envInK-imp : (E ya yc b a ar c : S)
             → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
             → ⟨ fst ar ∈ Lset lam ⟩
             → (z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ B₀ ∷ []) ⊨
                 envOverAt zero (suc (suc (suc (suc (suc (suc zero))))))
                               (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⟩
             → ⟨ fst z ∈ Lset lam ⟩
  envInK-imp E ya yc b a ar c arNum arK z h =
    envInK-gen (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ B₀ ∷ [])
      (suc (suc (suc (suc (suc zero)))))
      (suc (suc (suc (suc (suc (suc (suc zero)))))))
      refl arNum arK z h

  -- someEnv: an E ∈ K satisfying the BOUNDED envSetB.
  level : S
  level = LsetS lam ordλ

  someEnv : (ya yc b a ar c : S)
          → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
          → ⟨ fst ya ∈ Lset lam ⟩
          → ⟨ fst yc ∈ Lset lam ⟩
          → ⟨ fst ar ∈ Lset lam ⟩
          → Σ S (λ E → ⟨ fst E ∈ Lset lam ⟩
              × ⟨ (E ∷ ar ∷ B₀ ∷ level ∷ []) ⊨
                    envSetB zero (suc zero) (suc (suc zero)) (suc (suc (suc zero))) ⟩)
  someEnv ya yc b a ar c arNum yaK ycK arK = E , (EK , henvB)
    where
    module G = Generic B₀ ar
    E : S
    E = G.envSetGen
    γ₀ : Vec S 4
    γ₀ = E ∷ ar ∷ B₀ ∷ level ∷ []
    EK : ⟨ fst E ∈ Lset lam ⟩
    EK = PT.rec (snd (fst E ∈ Lset lam)) (λ { (n , arn) → envSetK ar n arn arK }) arNum
    arityK₀ : (N v : S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst N ∈ Lset lam ⟩
            → ⟨ fst v ∈ Lset lam ⟩
    arityK₀ N v hv hNK = transK v N hv hNK
    envInK₀ : (z : S) → ⟨ (z ∷ γ₀) ⊨ envOverAt zero (suc (suc zero)) (suc (suc (suc zero))) ⟩
            → ⟨ fst z ∈ Lset lam ⟩
    envInK₀ z hz = envInK-gen γ₀ (suc zero) (suc (suc zero)) refl arNum arK z hz
    module ES = EnvSet {4} zero (suc zero) (suc (suc zero)) (suc (suc (suc zero)))
      γ₀ arityK₀ EK arK envInK₀
    module H = G.Holds {4} γ₀ zero (suc zero) (suc (suc zero)) refl refl refl
    henvB : ⟨ γ₀ ⊨ envSetB zero (suc zero) (suc (suc zero)) (suc (suc (suc zero))) ⟩
    henvB = ES.back H.holds

-- =====================================================================
-- THE TOWER-NEUTRAL FIELDS over (K, Ktr) ([LJ-1.258] + [LJ-1.259]).
-- =====================================================================

module Fact (K : S) (Ktr : isTransV (fst K)) where

  prK : (x y : V ℓ) → ⟨ pr x y ∈ fst K ⟩ → ⟨ x ∈ fst K ⟩ × ⟨ y ∈ fst K ⟩
  prK x y h = Ktr (mem x (inl refl)) pairInK , Ktr (mem y (inr refl)) pairInK
    where
    pairInK : ⟨ ⁅ x , y ⁆ ∈ fst K ⟩
    pairInK = Ktr (∈∈ₛ {a = ⁅ x , y ⁆} {b = pr x y} .snd
                (pairing-ax ⁅ x ⁆s ⁅ x , y ⁆ ⁅ x , y ⁆ .snd ∣ inr refl ∣₁)) h
    mem : (z : V ℓ) → (z ≡ x) Sum.⊎ (z ≡ y) → ⟨ z ∈ ⁅ x , y ⁆ ⟩
    mem z e = ∈∈ₛ {a = z} {b = ⁅ x , y ⁆} .snd (pairing-ax x y z .snd ∣ e ∣₁)

  -- GROUP 1: valK, valK-un.
  valK : (C T : S) → ⟨ fst T ∈ fst K ⟩
       → (k : ℕ) (c ar a b yc : S)
       → ⟨ fst c ∈ fst C ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
       → ⟨ pr (fst c) (fst yc) ∈ fst T ⟩
       → ⟨ fst yc ∈ fst K ⟩
  valK C T TK k c ar a b yc c∈ shape hc =
    prK (fst c) (fst yc) (Ktr hc TK) .snd

  valK-un : (C T : S) → ⟨ fst T ∈ fst K ⟩
          → (k : ℕ) (c ar a yc : S)
          → ⟨ fst c ∈ fst C ⟩
          → fst c ≡ pr (fst ar) (pr (# k) (fst a))
          → ⟨ pr (fst c) (fst yc) ∈ fst T ⟩
          → ⟨ fst yc ∈ fst K ⟩
  valK-un C T TK k c ar a yc c∈ shape hc =
    prK (fst c) (fst yc) (Ktr hc TK) .snd

  -- GROUP 3: the seven subK-* fields.
  subK-gen : {n : ℕ} (γ : Vec S n) (T ar a y : Fin n)
           → ⟨ fst (lookup T γ) ∈ fst K ⟩
           → ⟨ γ ⊨ subValAt T ar a y ⟩
           → ⟨ fst (lookup y γ) ∈ fst K ⟩
  subK-gen γ T ar a y TK h =
    prK (pr (fst (lookup ar γ)) (fst (lookup a γ))) (fst (lookup y γ))
      (Ktr (subst ⟨_⟩ (subValAt-adequate T ar a y γ) h) TK) .snd

  subKSucc-gen : {n : ℕ} (γ : Vec S n) (T ar a y : Fin n)
               → ⟨ fst (lookup T γ) ∈ fst K ⟩
               → ⟨ γ ⊨ subValSuccAt T ar a y ⟩
               → ⟨ fst (lookup y γ) ∈ fst K ⟩
  subKSucc-gen γ T ar a y TK h =
    prK (pr (sucV (fst (lookup ar γ))) (fst (lookup a γ))) (fst (lookup y γ))
      (Ktr (subst ⟨_⟩ (subValSuccAt-adequate T ar a y γ) h) TK) .snd

  subK₁-and : (γ' : Vec S 2) → ⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩
            → (x y yc b a ar c : S)
            → ⟨ (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  subValAt (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                           (suc (suc (suc (suc (suc zero)))))
                           (suc (suc (suc (suc zero))))
                           (suc zero) ⟩
            → ⟨ fst y ∈ fst K ⟩
  subK₁-and γ' TK x y yc b a ar c h =
    subK-gen (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') eight five four one TK h

  subK₀-and : (γ' : Vec S 2) → ⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩
            → (y ya yc b a ar c : S)
            → ⟨ (y ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  subValAt (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                           (suc (suc (suc (suc (suc zero)))))
                           (suc (suc (suc zero)))
                           zero ⟩
            → ⟨ fst y ∈ fst K ⟩
  subK₀-and γ' TK y ya yc b a ar c h =
    subK-gen (y ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') eight five three zero TK h

  subK₁-imp : (γ' : Vec S 2) → ⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩
            → (E yb ya yc b a ar c : S)
            → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  subValAt (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                           (suc (suc (suc (suc (suc (suc zero))))))
                           (suc (suc (suc (suc (suc zero)))))
                           (suc (suc zero)) ⟩
            → ⟨ fst ya ∈ fst K ⟩
  subK₁-imp γ' TK E yb ya yc b a ar c h =
    subK-gen (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') nine six five two TK h

  subK₀-imp : (γ' : Vec S 2) → ⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩
            → (E yb ya yc b a ar c : S)
            → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  subValAt (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                           (suc (suc (suc (suc (suc (suc zero))))))
                           (suc (suc (suc (suc zero))))
                           (suc zero) ⟩
            → ⟨ fst yb ∈ fst K ⟩
  subK₀-imp γ' TK E yb ya yc b a ar c h =
    subK-gen (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') nine six four one TK h

  subK-neg : (γ' : Vec S 2) → ⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩
           → (ya yc a ar c E : S)
           → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                 subValAt (suc (suc (suc (suc (suc (suc (suc zero)))))))
                          (suc (suc (suc (suc zero))))
                          (suc (suc (suc zero)))
                          (suc zero) ⟩
           → ⟨ fst ya ∈ fst K ⟩
  subK-neg γ' TK ya yc a ar c E h =
    subK-gen (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') seven four three one TK h

  subK-un : (γ' : Vec S 2) → ⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩
          → (ya yc a ar c E : S)
          → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                subValSuccAt (suc (suc (suc (suc (suc (suc (suc zero)))))))
                             (suc (suc (suc (suc zero))))
                             (suc (suc (suc zero)))
                             (suc zero) ⟩
          → ⟨ fst ya ∈ fst K ⟩
  subK-un γ' TK ya yc a ar c E h =
    subKSucc-gen (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') seven four three one TK h

  subK-allin : (γ' : Vec S 2) → ⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩
             → (E ya yc b a ar c : S)
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                   subValSuccAt (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                                (suc (suc (suc (suc (suc zero)))))
                                (suc (suc (suc zero)))
                                (suc zero) ⟩
             → ⟨ fst ya ∈ fst K ⟩
  subK-allin γ' TK E ya yc b a ar c h =
    subKSucc-gen (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') eight five three one TK h

  -- GROUP 2: valV, valW, wKfact.
  tmValK : {n : ℕ} (γ : Vec S n) (t e v : Fin n)
         → ⟨ fst (lookup e γ) ∈ fst K ⟩
         → ⟨ fst (lookup t γ) ∈ fst K ⟩
         → ⟨ γ ⊨ tmValAt t e v ⟩
         → ⟨ fst (lookup v γ) ∈ fst K ⟩
  tmValK γ t e v eK tK h =
    PT.rec (snd (fst (lookup v γ) ∈ fst K)) (λ { (inl q) → varCase q
                                              ; (inr q) → conCase q })
      (tmValAt-out t e v γ h)
    where
    varCase : (Σ[ k ∈ S ] ((fst (lookup t γ) ≡ pr (# 1) (fst k))
                            × ⟨ pr (fst k) (fst (lookup v γ)) ∈ fst (lookup e γ) ⟩))
            → ⟨ fst (lookup v γ) ∈ fst K ⟩
    varCase (k , (_ , kv∈e)) = prK (fst k) (fst (lookup v γ)) (Ktr kv∈e eK) .snd
    conCase : fst (lookup t γ) ≡ pr (# 0) (fst (lookup v γ))
            → ⟨ fst (lookup v γ) ∈ fst K ⟩
    conCase q = prK (# 0) (fst (lookup v γ))
      (subst (λ w → ⟨ w ∈ fst K ⟩) q tK) .snd

  valV : (γ' : Vec S 2) → (E yc b a ar c z v w : S)
       → ⟨ fst z ∈ fst K ⟩ → ⟨ fst a ∈ fst K ⟩
       → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
             tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                     (suc (suc zero))
                     (suc zero) ⟩
       → ⟨ fst v ∈ fst K ⟩
  valV γ' E yc b a ar c z v w zK aK h =
    tmValK (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') six two one zK aK h

  valW : (γ' : Vec S 2) → (E yc b a ar c z v w : S)
       → ⟨ fst z ∈ fst K ⟩ → ⟨ fst b ∈ fst K ⟩
       → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
             tmValAt (suc (suc (suc (suc (suc zero)))))
                     (suc (suc zero))
                     zero ⟩
       → ⟨ fst w ∈ fst K ⟩
  valW γ' E yc b a ar c z v w zK bK h =
    tmValK (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') five two zero zK bK h

  wKfact : (γ' : Vec S 2) → (E ya yc b a ar c z w : S)
         → ⟨ fst z ∈ fst K ⟩ → ⟨ fst a ∈ fst K ⟩
         → ⟨ (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
               tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                       (suc zero)
                       zero ⟩
         → ⟨ fst w ∈ fst K ⟩
  wKfact γ' E ya yc b a ar c z w zK aK h =
    tmValK (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') six one zero zK aK h

  -- GROUP 4: consK-exist, consK-forall, consK-allin, stated over the
  -- env closure as a hypothesis ([LJ-1.258]'s honest forms).
  module ConsK
    (envConsK : {k : ℕ} (g : Fin k → V ℓ) (x : V ℓ)
              → ⟨ env g ∈ fst K ⟩ → ⟨ x ∈ fst K ⟩
              → ⟨ env (cons x g) ∈ fst K ⟩) where

    consK-forall : (γ' : Vec S 2) → (ya yc a ar c E z x e' : S)
                 → {k : ℕ} (g : Fin k → V ℓ)
                 → fst z ≡ env g
                 → ⟨ fst z ∈ fst K ⟩ → ⟨ fst x ∈ fst K ⟩
                 → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                     consAtL zero (suc zero) (suc (suc zero)) ⟩
                 → ⟨ fst e' ∈ fst K ⟩
    consK-forall γ' ya yc a ar c E z x e' g zg zK xK h =
      subst (λ w → ⟨ w ∈ fst K ⟩) (sym e'eq)
        (envConsK g (fst x) (subst (λ w → ⟨ w ∈ fst K ⟩) zg zK) xK)
      where
      e'eq : fst e' ≡ env (cons (fst x) g)
      e'eq = subst ⟨_⟩ (consAtL-adequate zero (suc zero) (suc (suc zero))
               (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') g zg) h

    consK-allin : (γ' : Vec S 2) → (E ya yc b a ar c z w x e' : S)
                → {k : ℕ} (g : Fin k → V ℓ)
                → fst z ≡ env g
                → ⟨ fst z ∈ fst K ⟩ → ⟨ fst x ∈ fst K ⟩
                → ⟨ (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                    consAtL zero (suc zero) (suc (suc (suc zero))) ⟩
                → ⟨ fst e' ∈ fst K ⟩
    consK-allin γ' E ya yc b a ar c z w x e' g zg zK xK h =
      subst (λ w → ⟨ w ∈ fst K ⟩) (sym e'eq)
        (envConsK g (fst x) (subst (λ w → ⟨ w ∈ fst K ⟩) zg zK) xK)
      where
      e'eq : fst e' ≡ env (cons (fst x) g)
      e'eq = subst ⟨_⟩ (consAtL-adequate zero (suc zero) (suc (suc (suc zero)))
               (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') g zg) h

    consK-exist : (γ' : Vec S 2) → (ya yc a ar c E z x e' : S)
                → ⟨ fst ya ∈ fst K ⟩
                → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                    consAtL zero (suc zero) (suc (suc zero))
                    ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ⟩
                → ⟨ fst e' ∈ fst K ⟩
    consK-exist γ' ya yc a ar c E z x e' yaK h =
      Ktr (h .snd) yaK

  -- THE CLOSURE ([LJ-1.259]): envConsK over (K, Ktr) plus numK0, sucK,
  -- pairK and the ONE new hypothesis finSetK.
  module EnvClosure
    (numK0 : ⟨ # 0 ∈ fst K ⟩)
    (sucK : (a : V ℓ) → ⟨ a ∈ fst K ⟩ → ⟨ sucV a ∈ fst K ⟩)
    (pairK : (a b : V ℓ) → ⟨ a ∈ fst K ⟩ → ⟨ b ∈ fst K ⟩ → ⟨ pr a b ∈ fst K ⟩)
    (finSetK : (n : ℕ) (h : Fin n → V ℓ)
             → ((i : Fin n) → ⟨ h i ∈ fst K ⟩) → ⟨ finSet n h ∈ fst K ⟩)
    where

    numK : (n : ℕ) → ⟨ # n ∈ fst K ⟩
    numK zero    = numK0
    numK (suc n) = sucK (# n) (numK n)

    env-entry : {k : ℕ} (g : Fin k → V ℓ) (i : Fin k)
              → ⟨ pr (# (toℕ i)) (g i) ∈ env g ⟩
    env-entry g i = ∣ lift i , refl ∣₁

    giK : {k : ℕ} (g : Fin k → V ℓ) (i : Fin k)
        → ⟨ env g ∈ fst K ⟩ → ⟨ g i ∈ fst K ⟩
    giK g i envgK = prK (# (toℕ i)) (g i) (Ktr (env-entry g i) envgK) .snd

    envConsK : {k : ℕ} (g : Fin k → V ℓ) (x : V ℓ)
             → ⟨ env g ∈ fst K ⟩ → ⟨ x ∈ fst K ⟩
             → ⟨ env (cons x g) ∈ fst K ⟩
    envConsK g x envgK xK =
      finSetK (suc _) (λ j → pr (# (toℕ j)) (cons x g j))
        (λ { zero    → pairK (# 0) x numK0 xK
           ; (suc i) → pairK (sucV (# (toℕ i))) (g i)
                         (sucK (# (toℕ i)) (numK (toℕ i))) (giK g i envgK) })

  -- The three consK-* honest forms, closed by envConsK.
  module ConsKClosed
    (numK0 : ⟨ # 0 ∈ fst K ⟩)
    (sucK : (a : V ℓ) → ⟨ a ∈ fst K ⟩ → ⟨ sucV a ∈ fst K ⟩)
    (pairK : (a b : V ℓ) → ⟨ a ∈ fst K ⟩ → ⟨ b ∈ fst K ⟩ → ⟨ pr a b ∈ fst K ⟩)
    (finSetK : (n : ℕ) (h : Fin n → V ℓ)
             → ((i : Fin n) → ⟨ h i ∈ fst K ⟩) → ⟨ finSet n h ∈ fst K ⟩)
    where

    open EnvClosure numK0 sucK pairK finSetK

    consK-forall : (γ' : Vec S 2) → (ya yc a ar c E z x e' : S)
                 → {k : ℕ} (g : Fin k → V ℓ)
                 → fst z ≡ env g
                 → ⟨ fst z ∈ fst K ⟩ → ⟨ fst x ∈ fst K ⟩
                 → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                     consAtL zero (suc zero) (suc (suc zero)) ⟩
                 → ⟨ fst e' ∈ fst K ⟩
    consK-forall γ' ya yc a ar c E z x e' g zg zK xK h =
      subst (λ w → ⟨ w ∈ fst K ⟩) (sym e'eq)
        (envConsK g (fst x) (subst (λ w → ⟨ w ∈ fst K ⟩) zg zK) xK)
      where
      e'eq : fst e' ≡ env (cons (fst x) g)
      e'eq = subst ⟨_⟩ (consAtL-adequate zero (suc zero) (suc (suc zero))
               (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') g zg) h

    consK-allin : (γ' : Vec S 2) → (E ya yc b a ar c z w x e' : S)
                → {k : ℕ} (g : Fin k → V ℓ)
                → fst z ≡ env g
                → ⟨ fst z ∈ fst K ⟩ → ⟨ fst x ∈ fst K ⟩
                → ⟨ (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                    consAtL zero (suc zero) (suc (suc (suc zero))) ⟩
                → ⟨ fst e' ∈ fst K ⟩
    consK-allin γ' E ya yc b a ar c z w x e' g zg zK xK h =
      subst (λ w → ⟨ w ∈ fst K ⟩) (sym e'eq)
        (envConsK g (fst x) (subst (λ w → ⟨ w ∈ fst K ⟩) zg zK) xK)
      where
      e'eq : fst e' ≡ env (cons (fst x) g)
      e'eq = subst ⟨_⟩ (consAtL-adequate zero (suc zero) (suc (suc (suc zero)))
               (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') g zg) h

    consK-exist : (γ' : Vec S 2) → (ya yc a ar c E z x e' : S)
                → ⟨ fst ya ∈ fst K ⟩
                → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                    consAtL zero (suc zero) (suc (suc zero))
                    ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ⟩
                → ⟨ fst e' ∈ fst K ⟩
    consK-exist γ' ya yc a ar c E z x e' yaK h =
      Ktr (h .snd) yaK

-- The concrete instance: K = Lset α as an element of L.
levelK : (α : V ℓ) → IsOrd α → S
levelK α o = Lset α , isL-Lset α o

module AtLevel (α : V ℓ) (o : IsOrd α) =
  Fact (levelK α o) (layer-trans (Lset-layer α))

-- =====================================================================
-- THE FINITE-SUPREMUM MERGE ([LJ-1.261]).
-- =====================================================================

Lset-fin : (σ : V ℓ) → IsOrd σ → (k : ℕ) (h : Fin k → V ℓ)
         → ((i : Fin k) → ⟨ h i ∈ Lset σ ⟩) → ⟨ finSet k h ∈ Lset (sucV σ) ⟩
Lset-fin σ oσ k h hm =
  subst (λ w → ⟨ finSet k h ∈ w ⟩) (sym (Lset-suc σ))
    (subst (λ w → ⟨ w ∈ 𝒟ₒ (Lset σ) ⟩)
      (cong (finSet k) (funExt (λ i → fib i .snd)))
      (FinOf.finSet∈𝒟ₒ σ oσ k (λ i → fib i .fst)))
  where
  fib : (i : Fin k) → Σ[ m ∈ ⟪ Lset σ ⟫ ] (⟪ Lset σ ⟫↪ m ≡ h i)
  fib i = ∈-asFiber {a = h i} {b = Lset σ} (hm i)

module SupplyMerge (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩) where

  ∈ₛ∪l : (a b x : V ℓ) → ⟨ x ∈ₛ a ⟩ → ⟨ x ∈ₛ a ∪ b ⟩
  ∈ₛ∪l a b x x∈a = union-ax ⁅ a , b ⁆ x .snd
    ∣ a , (pairing-ax a b a .snd ∣ inl refl ∣₁ , x∈a) ∣₁

  ∈ₛ∪r : (a b x : V ℓ) → ⟨ x ∈ₛ b ⟩ → ⟨ x ∈ₛ a ∪ b ⟩
  ∈ₛ∪r a b x x∈b = union-ax ⁅ a , b ⁆ x .snd
    ∣ b , (pairing-ax a b b .snd ∣ inr refl ∣₁ , x∈b) ∣₁

  ∈∪l : (a b x : V ℓ) → ⟨ x ∈ a ⟩ → ⟨ x ∈ a ∪ b ⟩
  ∈∪l a b x h = ∈∈ₛ {a = x} {b = a ∪ b} .snd
    (∈ₛ∪l a b x (∈∈ₛ {a = x} {b = a} .fst h))

  ∈∪r : (a b x : V ℓ) → ⟨ x ∈ b ⟩ → ⟨ x ∈ a ∪ b ⟩
  ∈∪r a b x h = ∈∈ₛ {a = x} {b = a ∪ b} .snd
    (∈ₛ∪r a b x (∈∈ₛ {a = x} {b = b} .fst h))

  ∪-ord : (a b : V ℓ) → IsOrd a → IsOrd b → IsOrd (a ∪ b)
  ∪-ord a b oa ob = ∪-trans (oa .fst) (ob .fst) , memTr
    where
    memTr : (x : V ℓ) → ⟨ x ∈ a ∪ b ⟩ → isTransV x
    memTr x x∈∪ = PT.rec (isPropIsTransV x)
      (λ { (v , (v∈pair , x∈v)) →
        PT.rec (isPropIsTransV x)
          (λ { (inl v≡a) → oa .snd x (∈∈ₛ {a = x} {b = a} .snd
                              (subst (λ w → ⟨ x ∈ₛ w ⟩) v≡a x∈v))
             ; (inr v≡b) → ob .snd x (∈∈ₛ {a = x} {b = b} .snd
                              (subst (λ w → ⟨ x ∈ₛ w ⟩) v≡b x∈v)) })
          (pairing-ax a b v .fst v∈pair) })
      (union-ax ⁅ a , b ⁆ x .fst (∈∈ₛ {a = x} {b = a ∪ b} .fst x∈∪))

  union-idem : (a : V ℓ) → a ∪ a ≡ a
  union-idem a = extensionality (a ∪ a) a (sub , sup)
    where
    sup : ⟨ a ⊆ a ∪ a ⟩
    sup x x∈a = ∈ₛ∪l a a x x∈a
    sub : ⟨ a ∪ a ⊆ a ⟩
    sub x x∈∪ = PT.rec (snd (x ∈ₛ a))
      (λ { (v , (v∈pair , x∈v)) →
        PT.rec (snd (x ∈ₛ a))
          (λ { (inl v≡a) → subst (λ w → ⟨ x ∈ₛ w ⟩) v≡a x∈v
             ; (inr v≡a) → subst (λ w → ⟨ x ∈ₛ w ⟩) v≡a x∈v })
          (pairing-ax a a v .fst v∈pair) })
      (union-ax ⁅ a , a ⁆ x .fst x∈∪)

  union-eq : (a b : V ℓ) → ⟨ a ⊆ b ⟩ → a ∪ b ≡ b
  union-eq a b a⊆b = extensionality (a ∪ b) b (sub , sup)
    where
    sup : ⟨ b ⊆ a ∪ b ⟩
    sup x x∈b = ∈ₛ∪r a b x x∈b
    sub : ⟨ a ∪ b ⊆ b ⟩
    sub x x∈∪ = PT.rec (snd (x ∈ₛ b))
      (λ { (v , (v∈pair , x∈v)) →
        PT.rec (snd (x ∈ₛ b))
          (λ { (inl v≡a) → a⊆b x (subst (λ w → ⟨ x ∈ₛ w ⟩) v≡a x∈v)
             ; (inr v≡b) → subst (λ w → ⟨ x ∈ₛ w ⟩) v≡b x∈v })
          (pairing-ax a b v .fst v∈pair) })
      (union-ax ⁅ a , b ⁆ x .fst x∈∪)

  ∪-comm : (a b : V ℓ) → a ∪ b ≡ b ∪ a
  ∪-comm a b = extensionality (a ∪ b) (b ∪ a) (sub , sup)
    where
    sub : ⟨ a ∪ b ⊆ b ∪ a ⟩
    sub x x∈ = PT.rec (snd (x ∈ₛ b ∪ a))
      (λ { (v , (v∈pair , x∈v)) →
        PT.rec (snd (x ∈ₛ b ∪ a))
          (λ { (inl v≡a) → ∈ₛ∪r b a x (subst (λ w → ⟨ x ∈ₛ w ⟩) v≡a x∈v)
             ; (inr v≡b) → ∈ₛ∪l b a x (subst (λ w → ⟨ x ∈ₛ w ⟩) v≡b x∈v) })
          (pairing-ax a b v .fst v∈pair) })
      (union-ax ⁅ a , b ⁆ x .fst x∈)
    sup : ⟨ b ∪ a ⊆ a ∪ b ⟩
    sup x x∈ = PT.rec (snd (x ∈ₛ a ∪ b))
      (λ { (v , (v∈pair , x∈v)) →
        PT.rec (snd (x ∈ₛ a ∪ b))
          (λ { (inl v≡b) → ∈ₛ∪r a b x (subst (λ w → ⟨ x ∈ₛ w ⟩) v≡b x∈v)
             ; (inr v≡a) → ∈ₛ∪l a b x (subst (λ w → ⟨ x ∈ₛ w ⟩) v≡a x∈v) })
          (pairing-ax b a v .fst v∈pair) })
      (union-ax ⁅ b , a ⁆ x .fst x∈)

  union2∈λ : (a b : V ℓ) → IsOrd a → IsOrd b → ⟨ a ∈ lam ⟩ → ⟨ b ∈ lam ⟩
           → ⟨ a ∪ b ∈ lam ⟩
  union2∈λ a b oa ob ma mb = go (ord-tri a oa b ob)
    where
    go : (⟨ a ∈ b ⟩ Sum.⊎ ((a ≡ b) Sum.⊎ ⟨ b ∈ a ⟩)) → ⟨ a ∪ b ∈ lam ⟩
    go (inl a∈b) = subst (λ w → ⟨ w ∈ lam ⟩) (sym (union-eq a b a⊆b')) mb
      where
      a⊆b' : ⟨ a ⊆ b ⟩
      a⊆b' x x∈a = ∈∈ₛ {a = x} {b = b} .fst
        (ob .fst {x = a} {y = x} (∈∈ₛ {a = x} {b = a} .snd x∈a) a∈b)
    go (inr (inl a≡b)) = subst (λ w → ⟨ w ∈ lam ⟩) (sym (union-idem a) ∙ cong (λ w → a ∪ w) a≡b) ma
    go (inr (inr b∈a)) = subst (λ w → ⟨ w ∈ lam ⟩) (sym (∪-comm a b ∙ union-eq b a b⊆a')) ma
      where
      b⊆a' : ⟨ b ⊆ a ⟩
      b⊆a' x x∈b = ∈∈ₛ {a = x} {b = a} .fst
        (oa .fst {x = b} {y = x} (∈∈ₛ {a = x} {b = b} .snd x∈b) b∈a)

  merge2 : (a b : V ℓ) → IsOrd a → IsOrd b → ⟨ a ∈ lam ⟩ → ⟨ b ∈ lam ⟩
         → Σ[ τ ∈ V ℓ ] (IsOrd τ × ⟨ τ ∈ lam ⟩ × ⟨ a ∈ τ ⟩ × ⟨ b ∈ τ ⟩)
  merge2 a b oa ob ma mb = τ , (oτ , τ∈ , a∈τ , b∈τ)
    where
    τ = sucV a ∪ sucV b
    oτ = ∪-ord (sucV a) (sucV b) (suc-ord oa) (suc-ord ob)
    τ∈ = union2∈λ (sucV a) (sucV b) (suc-ord oa) (suc-ord ob)
           (succλ a ma) (succλ b mb)
    a∈τ = ∈∪l (sucV a) (sucV b) a (self∈sucV a)
    b∈τ = ∈∪r (sucV a) (sucV b) b (self∈sucV b)

  finSup : (n : ℕ) (γ : Fin n → V ℓ)
         → ((i : Fin n) → IsOrd (γ i))
         → ((i : Fin n) → ⟨ γ i ∈ lam ⟩)
         → Σ[ τ ∈ V ℓ ] (IsOrd τ × ⟨ τ ∈ lam ⟩ × ((i : Fin n) → ⟨ γ i ∈ τ ⟩))
  finSup zero γ oγ mγ = ∅ , (∅-ord , ∅∈λ , λ ())
  finSup (suc n) γ oγ mγ =
    τ , (oτ , τ∈ , all)
    where
    tail = finSup n (λ j → γ (suc j)) (λ j → oγ (suc j)) (λ j → mγ (suc j))
    τt = tail .fst
    oτt = tail .snd .fst
    τt∈ = tail .snd .snd .fst
    γt∈τt = tail .snd .snd .snd
    m2 = merge2 (γ zero) τt (oγ zero) oτt (mγ zero) τt∈
    τ = m2 .fst
    oτ = m2 .snd .fst
    τ∈ = m2 .snd .snd .fst
    γ0∈τ = m2 .snd .snd .snd .fst
    τt∈τ = m2 .snd .snd .snd .snd
    all : (i : Fin (suc n)) → ⟨ γ i ∈ τ ⟩
    all zero    = γ0∈τ
    all (suc j) = oτ .fst {x = τt} {y = γ (suc j)} (γt∈τt j) τt∈τ

  finSetK : (n : ℕ) (h : Fin n → V ℓ)
          → ((i : Fin n) → ⟨ h i ∈ Lset lam ⟩)
          → ⟨ finSet n h ∈ Lset lam ⟩
  finSetK n h hm =
    PT.rec (snd (finSet n h ∈ Lset lam)) step
      (choice (λ i → Σ[ δ ∈ V ℓ ] (⟨ δ ∈ lam ⟩ × ⟨ h i ∈ Lset (sucV δ) ⟩))
        (λ i → Lset-out′ lam (h i) (hm i)))
    where
    step : ((i : Fin n) → Σ[ δ ∈ V ℓ ] (⟨ δ ∈ lam ⟩ × ⟨ h i ∈ Lset (sucV δ) ⟩))
         → ⟨ finSet n h ∈ Lset lam ⟩
    step stages =
      let
        δ : Fin n → V ℓ
        δ i = stages i .fst
        δ∈ : (i : Fin n) → ⟨ δ i ∈ lam ⟩
        δ∈ i = stages i .snd .fst
        h∈ : (i : Fin n) → ⟨ h i ∈ Lset (sucV (δ i)) ⟩
        h∈ i = stages i .snd .snd
        oδ : (i : Fin n) → IsOrd (δ i)
        oδ i = mem-ord {A = lam} ordλ (δ i) (δ∈ i)
        sup = finSup n (λ i → sucV (δ i)) (λ i → suc-ord (oδ i))
                (λ i → succλ (δ i) (δ∈ i))
        τ = sup .fst
        oτ = sup .snd .fst
        τ∈ = sup .snd .snd .fst
        sucδ∈τ = sup .snd .snd .snd
        h∈τ : (i : Fin n) → ⟨ h i ∈ Lset τ ⟩
        h∈τ i = Lset-mono {α = τ} {β = sucV (δ i)} (sucδ∈τ i) (h∈ i)
      in
      Lset-mono {α = lam} {β = sucV τ} (succλ τ τ∈)
        (Lset-fin τ oτ n h h∈τ)
```

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

module LJ-1-283.TreatedBridge {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
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
      Lset-mono {α = lam} {β = sucIter 4 δ}
        (B.suc^∈λ 4 δ δ∈)
        sucV∈
      where
      δ₁ = sucV δ
      δ₂ = sucV (sucV δ)
      δ₃ = sucV (sucV (sucV δ))
      a∈δ₂ : ⟨ a ∈ Lset δ₂ ⟩
      a∈δ₂ = Lset-mono {α = δ₂} {β = δ₁} (self∈sucV δ₁) a∈δ₁
      sgl∈δ₂ : ⟨ ⁅ a ⁆s ∈ Lset δ₂ ⟩
      sgl∈δ₂ = sgl∈Lset-suc δ₁ a a∈δ₁
      pair∈δ₃ : ⟨ ⁅ a , ⁅ a ⁆s ⁆ ∈ Lset δ₃ ⟩
      pair∈δ₃ = pair∈Lset-suc δ₂ a ⁅ a ⁆s a∈δ₂ sgl∈δ₂
      -- [LJ-1.283] THE ONE CHANGE IN THIS ARM.
      -- `--profile=definitions` on the control charges 475,710 ms of the
      -- file's 479,311 ms to this ONE definition.  The control writes the
      -- body straight into the declared type, so the conversion checker must
      -- prove `⋃ ⁅ a , ⁅ a ⁆s ⁆ ≡ sucV a` UNDER the membership head
      -- `⟨ _ ∈ Lset (sucIter 4 δ) ⟩`, which is four exposed `Lset ∘ sucV`
      -- layers (P-i class 1, the layer-cap sub-rule, and R-40).
      -- This arm states the same equation at the BARE type `V ℓ`, where no
      -- membership head and no level are in the way, and bridges with one
      -- `subst`.  P-i [A]: "bridge the concrete membership by one subst".
      -- Nothing else in the file changes.
      sucEq : ⋃ ⁅ a , ⁅ a ⁆s ⁆ ≡ sucV a
      sucEq = refl
      sucV∈ : ⟨ sucV a ∈ Lset (sucIter 4 δ) ⟩
      sucV∈ = subst (λ w → ⟨ w ∈ Lset (sucIter 4 δ) ⟩) sucEq
        (union∈Lset-suc δ₃ ⁅ a , ⁅ a ⁆s ⁆ pair∈δ₃)

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
```

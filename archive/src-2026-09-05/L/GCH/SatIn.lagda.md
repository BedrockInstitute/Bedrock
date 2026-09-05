# The satisfaction set of a carrier formula inside a closed stage

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.SatIn {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( Transitive; module hPropStructure )
open import FOL.Syntax
  using ( Formula; Term; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∃∈; δ-∀∈ )
open import FOL.Manipulation.Relabelling using ( mapTm; mapFo )
open import FOL.Manipulation.Bounding
  using ( BoundedTm; BoundedFo; BoundedTm-mono; BoundedFo-mono; module Relabel )
open import FOL.Manipulation.Relativize
  using ( relativize; Δ₀-relativize; module Correct )
import FOL.Absoluteness
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr; pr-inj; module VCode )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-elim; ∈sucV-inl )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-layer; layer-trans
        ; Lset-mono; Lset-out; Lset→isL; 𝒟ₒ; 𝒟ₒ∋⊆; 𝒟ₒ-intro )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Absoluteness {ℓ} using ( InL; liftFo; transferFo; Δ₀-liftFo )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; ω-ord; #∈ω )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.Ordinal.StageArith {ℓ} lem
  using ( sucIter; sucIter-ord; +ω; +ω-mem; +ω-iter; +ω-sup; +ω-ord; closedω )
open import L.Choice.Name {ℓ} lem using ( numeral∈limit )
open import L.Axioms.Basic {ℓ} using ( LsetS; Lset-suc; pr∈Lset-suc )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Separation {ℓ} lem using ( Below′; module AtStage )
open import L.Coding.CodeSet {ℓ} lem using ( keyS )
open import L.Coding.EnvSet {ℓ} lem using ( envSet; envSet-mem; envFo )
open import L.Coding.Key {ℓ} lem using ( envSetNumeral∈ )
open import L.Coding.Bridge {ℓ} lem using ( asConst )
open import L.Coding.Bound {ℓ} lem using ( module Bound; Lset-out′ )
open import L.Coding.Sat {ℓ} lem
  using ( Sat; cond; tmIs; tmIs-var-in; tmIs-var-out
        ; cond∈-in; cond∈-out; cond≐-in; cond≐-out
        ; cond∃-in; cond∃-out; cond∀-in; cond∀-out
        ; cond∃∈-in; cond∃∈-out; cond∀∈-in; cond∀∈-out )
open import L.Coding.Model {ℓ}
  using ( prʟ; prʟ-fst; tagAtL; prAtL
        ; appAt; appAt-adequate; consAtL; numL
        ; valuesInAt-out; pairsIn-out
        ; envOverAt; envOver-values; envOver-pairs )
open import L.Coding.Environment {ℓ}
  using ( sucAt; sgl0At; pair0At; tag0At; consAt; shiftPairAt
        ; Δ₀-sucAt; Δ₀-sgl0At; Δ₀-pair0At; Δ₀-tag0At; Δ₀-consAt; Δ₀-shiftPairAt
        ; tag0At-adequate; shiftPairAt-adequate )
open import L.Coding.Base {ℓ}
  using ( prAt; sglAt; pairAt; Δ₀-prAt; Δ₀-sglAt; Δ₀-pairAt )
open import L.GCH.Placement {ℓ} lem using ( asConst-in-carrier; module Closer )

open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Nat.Properties using ( +-comm )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Sum as Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( tt; tt* )
open import Cubical.Data.Vec using ( Vec; map; lookup )
import Cubical.Data.Empty as Empty
open import Cubical.Foundations.Equiv using ( invEq )
open import Cubical.Foundations.Function using ( _∘_ )
open import Cubical.Foundations.HLevels using ( isOfHLevelLift )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; sett; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber; _⊆_; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( #_; ω; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
-- Membership `_∈ˢ_` below is the V structure's (definitionally `_∈_`);
-- `S` is the L carrier, and the L structure's membership is `_∈ˢʟ_`.
open hPropStructure 𝒮ᵥ hiding ( S )
open hPropStructure 𝒮ʟ using ( S ) renaming ( _∈ˢ_ to _∈ˢʟ_ ; _≈ˢ_ to _≈ˢʟ_ )

private
  Lset-trans-set′ : (γ a x : V ℓ)
                  → ⟨ a ∈ x ⟩ → ⟨ x ∈ Lset γ ⟩ → ⟨ a ∈ Lset γ ⟩
  Lset-trans-set′ γ a x a∈ x∈ = PT.rec (snd (a ∈ Lset γ)) step (Lset-out γ x x∈)
    where
    step : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ γ ⟩ × ⟨ x ∈ 𝒟ₒ (Lset δ) ⟩)
         → ⟨ a ∈ Lset γ ⟩
    step (δ , (δ∈γ , x∈𝒟)) =
      Lset-mono {α = γ} {β = δ} δ∈γ {x = a}
        (𝒟ₒ∋⊆ (Lset δ) x x∈𝒟 a a∈)

-- =====================================================================
-- SECTION 7.  The satisfaction set of a carrier formula sits in a
-- closed stage (C2a).  The alphabet is the carrier-bounded one: the
-- constants of ψ name members of fst A, and A itself sits in Lset γ.
-- At the wide alphabet Formula S n the same statement is false
-- (LJ-1.736): a constant there names an arbitrary L-set, and no
-- closure absorbs it.
-- =====================================================================

toS : (A : S) {n : ℕ} → Formula ⟪ fst A ⟫ n → Formula S n
toS A ψ = mapFo (asConst A) ψ

numeralS : (k : ℕ) → S
numeralS k = # k , numL k

module
  SatBnd (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ) (ω∈γ : ⟨ ω ∈ˢ γ ⟩)
         (A : S) (hA : ⟨ fst A ∈ˢ Lset γ ⟩) where

  private
    module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
    open AbsL using () renaming ( _⊨ᵛ_ to _⊨ᵛᵥ_ )

  infixl 30 _^_
  _^_ : ∀ {ℓ''} → Type ℓ'' → ℕ → Type ℓ''
  A ^ n = Vec A n

  -- The global satisfaction at the L structure, the one `Sat` reads.
  _⊨ʟ_ : ∀ {n} → S ^ n → Formula S n → Ω
  _⊨ʟ_ = AbsL._⊨ᵐ_

  -- One ordinal in γ above ω and above the successor of A's own stage.
  module Kit (d : V ℓ) (d∈γ : ⟨ d ∈ˢ γ ⟩) (A∈𝒟d : ⟨ fst A ∈ˢ 𝒟ₒ (Lset d) ⟩) where

    γsup : (a b : V ℓ) → ⟨ a ∈ˢ γ ⟩ → ⟨ b ∈ˢ γ ⟩
        → Σ[ c ∈ V ℓ ] (⟨ c ∈ˢ γ ⟩ × ⟨ a ∈ˢ c ⟩ × ⟨ b ∈ˢ c ⟩)
    γsup a b a∈ b∈ = help (ord-tri a (mem-ord {A = γ} oγ a a∈) b
                                 (mem-ord {A = γ} oγ b b∈))
      where
      help : Tri a b
           → Σ[ c ∈ V ℓ ] (⟨ c ∈ˢ γ ⟩ × ⟨ a ∈ˢ c ⟩ × ⟨ b ∈ˢ c ⟩)
      help (inl a∈b) =
        sucV b , (Closer.suc∈γ γ oγ clγ b b∈ , ∈sucV-inl a∈b , self∈sucV b)
      help (inr (inl a≡b)) =
        sucV a , ( Closer.suc∈γ γ oγ clγ a a∈ , self∈sucV a
                 , subst (λ w → ⟨ w ∈ˢ sucV a ⟩) a≡b (self∈sucV a) )
      help (inr (inr b∈a)) =
        sucV a , (Closer.suc∈γ γ oγ clγ a a∈ , self∈sucV a , ∈sucV-inl b∈a)

    sup₁ : Σ[ c ∈ V ℓ ] (⟨ c ∈ˢ γ ⟩ × ⟨ ω ∈ˢ c ⟩ × ⟨ sucV d ∈ˢ c ⟩)
    sup₁ = γsup ω (sucV d) ω∈γ (Closer.suc∈γ γ oγ clγ d d∈γ)

    ηB : V ℓ
    ηB = sup₁ .fst
    ηB∈γ : ⟨ ηB ∈ˢ γ ⟩
    ηB∈γ = sup₁ .snd .fst
    oηB : IsOrd ηB
    oηB = mem-ord {A = γ} oγ ηB ηB∈γ
    ω∈ηB : ⟨ ω ∈ˢ ηB ⟩
    ω∈ηB = sup₁ .snd .snd .fst
    A∈LηB : ⟨ fst A ∈ˢ Lset ηB ⟩
    A∈LηB = Lset-mono {α = ηB} {β = sucV d} (sup₁ .snd .snd .snd)
              (subst (λ w → ⟨ fst A ∈ˢ w ⟩) (sym (Lset-suc d)) A∈𝒟d)

    -- The uniform stage of every environment set: independent of n.
    τ★ : V ℓ
    τ★ = sucIter 4 (+ω ηB)
    envSetAll : (m : ℕ) → ⟨ fst (envSet A m) ∈ˢ Lset τ★ ⟩
    envSetAll m = envSetNumeral∈ (+ω ηB) (+ω-ord ηB oηB) ω∈+ωηB A m A∈L+ωηB
      where
      ω∈+ωηB : ⟨ ω ∈ˢ +ω ηB ⟩
      ω∈+ωηB = (+ω-ord ηB oηB) .fst ω∈ηB (+ω-mem ηB)
      A∈L+ωηB : ⟨ fst A ∈ˢ Lset (+ω ηB) ⟩
      A∈L+ωηB = Lset-mono {α = +ω ηB} {β = ηB} (+ω-mem ηB) A∈LηB

    -- The machinery at one stage: the relativization, the separation,
    -- and the two readings of the clause.
    module Mach (nψ : ℕ) (η : V ℓ) (oη : IsOrd η) (πη : ⟨ η ∈ˢ γ ⟩)
                (ω∈η : ⟨ ω ∈ˢ η ⟩) (hAη : ⟨ fst A ∈ˢ Lset η ⟩)
                (henvη : ⟨ fst (envSet A nψ) ∈ˢ Lset η ⟩)
                (sub∈ : ∀ {m} (a : Formula ⟪ fst A ⟫ m)
                       → ⟨ fst (Sat A (toS A a)) ∈ˢ Lset η ⟩) where

      ρ : V ℓ
      ρ = +ω η
      oρ : IsOrd ρ
      oρ = +ω-ord η oη
      ρ∈γ : ⟨ ρ ∈ˢ γ ⟩
      ρ∈γ = clγ η πη
      ρ₂ : V ℓ
      ρ₂ = +ω ρ
      oρ₂ : IsOrd ρ₂
      oρ₂ = +ω-ord ρ oρ
      ρ₂∈γ : ⟨ ρ₂ ∈ˢ γ ⟩
      ρ₂∈γ = clγ ρ ρ∈γ
      cb : S
      cb = LsetS ρ₂ oρ₂
      σ : V ℓ
      σ = sucV ρ₂
      oσ : IsOrd σ
      oσ = suc-ord oρ₂

      η∈ρ : ⟨ η ∈ˢ ρ ⟩
      η∈ρ = +ω-mem η
      ρ∈ρ₂ : ⟨ ρ ∈ˢ ρ₂ ⟩
      ρ∈ρ₂ = +ω-mem ρ
      ρ₂∈σ : ⟨ ρ₂ ∈ˢ σ ⟩
      ρ₂∈σ = self∈sucV ρ₂

      Lση : {x : V ℓ} → ⟨ x ∈ˢ Lset η ⟩ → ⟨ x ∈ˢ Lset σ ⟩
      Lση x∈ = Lset-mono {α = σ} {β = ρ₂} ρ₂∈σ
                 (Lset-mono {α = ρ₂} {β = ρ} ρ∈ρ₂
                   (Lset-mono {α = ρ} {β = η} η∈ρ x∈))
      Lσρ : {x : V ℓ} → ⟨ x ∈ˢ Lset ρ ⟩ → ⟨ x ∈ˢ Lset σ ⟩
      Lσρ x∈ = Lset-mono {α = σ} {β = ρ₂} ρ₂∈σ
                 (Lset-mono {α = ρ₂} {β = ρ} ρ∈ρ₂ x∈)
      Lρ₂η : {x : V ℓ} → ⟨ x ∈ˢ Lset η ⟩ → ⟨ x ∈ˢ Lset ρ₂ ⟩
      Lρ₂η x∈ = Lset-mono {α = ρ₂} {β = ρ} ρ∈ρ₂
                  (Lset-mono {α = ρ} {β = η} η∈ρ x∈)
      Lρη : {x : V ℓ} → ⟨ x ∈ˢ Lset η ⟩ → ⟨ x ∈ˢ Lset ρ ⟩
      Lρη x∈ = Lset-mono {α = ρ} {β = η} η∈ρ x∈
      as∈ρ : (m : ⟪ fst A ⟫) → ⟨ fst (asConst A m) ∈ˢ Lset ρ ⟩
      as∈ρ m = Lρη (asConst-in-carrier η oη A hAη m)
      Lρ₂ρ : {x : V ℓ} → ⟨ x ∈ˢ Lset ρ ⟩ → ⟨ x ∈ˢ Lset ρ₂ ⟩
      Lρ₂ρ x∈ = Lset-mono {α = ρ₂} {β = ρ} ρ∈ρ₂ x∈
      mkSρ : (a : V ℓ) → ⟨ a ∈ˢ Lset ρ ⟩ → S
      mkSρ a a∈ = a , Lset→isL ρ oρ a a∈

      num∈σ : (k : ℕ) → ⟨ fst (numeralS k) ∈ˢ Lset σ ⟩
      num∈σ k = Lση (Lset-mono {α = η} {β = ω} ω∈η (numeral∈limit k))
      as∈σ : (m : ⟪ fst A ⟫) → ⟨ fst (asConst A m) ∈ˢ Lset σ ⟩
      as∈σ m = Lση (asConst-in-carrier η oη A hAη m)
      A∈σ : ⟨ fst A ∈ˢ Lset σ ⟩
      A∈σ = Lση hAη
      cb∈σ : ⟨ fst cb ∈ˢ Lset σ ⟩
      cb∈σ = subst (λ w → ⟨ Lset ρ₂ ∈ˢ w ⟩) (sym (Lset-suc ρ₂))
               (𝒟ₒ-intro (Lset ρ₂) (Lset ρ₂) ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset ρ₂) ∣₁)
      sub∈σ : ∀ {m} (a : Formula ⟪ fst A ⟫ m)
            → ⟨ fst (Sat A (toS A a)) ∈ˢ Lset σ ⟩
      sub∈σ a = Lση (sub∈ a)
      env∈σ : ⟨ fst (envSet A nψ) ∈ˢ Lset σ ⟩
      env∈σ = Lση henvη

      module RC = Correct (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ id cb

      -- The term evaluation of the same semantics instance the
      -- relativization correctness reads at.
      module RAt = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ
      module RAtS = RAt.At S id

      -- Satisfaction of a Δ₀ formula depends only on the underlying
      -- sets of the environment entries.
      abs₀-tr : ∀ {n} (χ : Formula S n) (dχ : Δ₀ χ) (δ₁ δ₂ : S ^ n)
              → map fst δ₁ ≡ map fst δ₂
              → ((δ₁ ⊨ʟ χ) ≡ (δ₂ ⊨ʟ χ))
      abs₀-tr χ dχ δ₁ δ₂ e =
          AbsL.abs₀ dχ δ₁
        ∙ cong (λ w → (w AbsL.⊨ᵛ χ)) e
        ∙ sym (AbsL.abs₀ dχ δ₂)

      -- Δ₀ formulas read the same on both sides of the relativization:
      -- the stage-bounded reading coincides with the global one.
      Δ₀ᴬ′ : (n : ℕ) {χ : Formula S n} (dχ : Δ₀ χ) (δ : S ^ n)
           → ((δ RC.⊨ᴬ χ) ≡ (δ ⊨ʟ χ))
      Δ₀ᴬ′ n δ-∈ δ = refl
      Δ₀ᴬ′ n δ-≐ δ = refl
      Δ₀ᴬ′ n (δ-∧ dχ dψ) δ = cong₂ _⊓_ (Δ₀ᴬ′ n dχ δ) (Δ₀ᴬ′ n dψ δ)
      Δ₀ᴬ′ n (δ-∨ dχ dψ) δ = cong₂ _⊔_ (Δ₀ᴬ′ n dχ δ) (Δ₀ᴬ′ n dψ δ)
      Δ₀ᴬ′ n (δ-⇒ dχ dψ) δ = cong₂ _⇒_ (Δ₀ᴬ′ n dχ δ) (Δ₀ᴬ′ n dψ δ)
      Δ₀ᴬ′ n (δ-¬ dχ) δ = cong ¬_ (Δ₀ᴬ′ n dχ δ)
      Δ₀ᴬ′ n δ-⊤ δ = refl
      Δ₀ᴬ′ n δ-⊥ δ = refl
      Δ₀ᴬ′ n (δ-∃∈ {t = t} dχ) δ = cong (⋁ S) (funExt (λ x →
        cong (λ q → (x ∈ˢʟ RAtS.⟦ t ⟧ δ) ⊓ q) (Δ₀ᴬ′ (suc n) dχ (x ∷ δ))))
      Δ₀ᴬ′ n (δ-∀∈ {t = t} dχ) δ = cong (⋀ S) (funExt (λ x →
        cong (λ q → (x ∈ˢʟ RAtS.⟦ t ⟧ δ) ⇒ q) (Δ₀ᴬ′ (suc n) dχ (x ∷ δ))))

      Δ₀ᴬ : ∀ {n} (χ : Formula S n) (dχ : Δ₀ χ) (δ : S ^ n)
          → ((δ RC.⊨ᴬ χ) ≡ (δ ⊨ʟ χ))
      Δ₀ᴬ χ dχ δ = Δ₀ᴬ′ _ dχ δ

      -- tmIs reads the same on both sides: its only unbounded
      -- quantifier pins its witness to a numeral, which sits in every
      -- stage of the ladder.
      -- Certificates of the all-variable structural readers.  Every
      -- leaf is a variable term, so every slot is trivial.
      hSgl : ∀ {n} (k i : Fin n) → BoundedFo InL (sglAt k i)
      hSgl k i = (lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt) , (lift {ℓ-zero} {ℓ-suc ℓ} tt , (lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt))
      hPair : ∀ {n} (k i j : Fin n) → BoundedFo InL (pairAt k i j)
      hPair k i j =
        (lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt)
          , ((lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt)
               , (lift {ℓ-zero} {ℓ-suc ℓ} tt , ((lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt) , (lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt))))
      hPrAt : ∀ {n} (q u v : Fin n) → BoundedFo InL (prAt q u v)
      hPrAt {n} q u v =
        (lift {ℓ-zero} {ℓ-suc ℓ} tt , hSgl {suc n} zero (suc u))
          , ( (lift {ℓ-zero} {ℓ-suc ℓ} tt , hPair {suc n} zero (suc u) (suc v))
            , (lift {ℓ-zero} {ℓ-suc ℓ} tt , (hSgl {suc n} zero (suc u) , hPair {suc n} zero (suc u) (suc v))) )
      hSucAt : ∀ {n} (i j : Fin n) → BoundedFo InL (sucAt i j)
      hSucAt i j =
        (lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt)
          , ( (lift {ℓ-zero} {ℓ-suc ℓ} tt , (lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt))
            , (lift {ℓ-zero} {ℓ-suc ℓ} tt , ((lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt) , (lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt))) )
      hShift : ∀ {n} (p' p : Fin n) → BoundedFo InL (shiftPairAt p' p)
      hShift {n} p' p =
        ( lift {ℓ-zero} {ℓ-suc ℓ} tt , ( lift {ℓ-zero} {ℓ-suc ℓ} tt , ( lift {ℓ-zero} {ℓ-suc ℓ} tt
        , ( lift {ℓ-zero} {ℓ-suc ℓ} tt , ( lift {ℓ-zero} {ℓ-suc ℓ} tt
        , ( hPrAt {suc (suc (suc (suc (suc n))))} (suc (suc (suc (suc (suc p))))) (suc (suc (suc zero))) (suc (suc zero))
          , ( hPrAt {suc (suc (suc (suc (suc n))))} (suc (suc (suc (suc (suc p'))))) zero (suc (suc zero))
            , hSucAt {suc (suc (suc (suc (suc n))))} (suc (suc (suc zero))) zero ) ) ) ) ) ) )
      hSgl0 : ∀ {n} (k : Fin n) → BoundedFo InL (sgl0At k)
      hSgl0 k = (lift {ℓ-zero} {ℓ-suc ℓ} tt , (lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt)) , (lift {ℓ-zero} {ℓ-suc ℓ} tt , (lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt))
      hPair0 : ∀ {n} (k j : Fin n) → BoundedFo InL (pair0At k j)
      hPair0 k j =
        (lift {ℓ-zero} {ℓ-suc ℓ} tt , (lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt))
          , ( (lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt)
            , ( lift {ℓ-zero} {ℓ-suc ℓ} tt , ((lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt) , (lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt)) ) )
      hTag0 : ∀ {n} (s x : Fin n) → BoundedFo InL (tag0At s x)
      hTag0 {n} s x =
        (lift {ℓ-zero} {ℓ-suc ℓ} tt , hSgl0 {suc n} zero)
          , ( (lift {ℓ-zero} {ℓ-suc ℓ} tt , hPair0 {suc n} zero (suc x))
            , (lift {ℓ-zero} {ℓ-suc ℓ} tt , (hSgl0 {suc n} zero , hPair0 {suc n} zero (suc x))) )
      -- The same certificates read at the separation stage.
      pSgl : ∀ {n} (k i : Fin n) → BoundedFo (Below′ σ) (liftFo (sglAt k i) (hSgl k i))
      pSgl k i = (lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt) , (lift {ℓ-zero} {ℓ-suc ℓ} tt , (lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt))
      pPair : ∀ {n} (k i j : Fin n) → BoundedFo (Below′ σ) (liftFo (pairAt k i j) (hPair k i j))
      pPair k i j =
        (lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt)
          , ((lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt) , (lift {ℓ-zero} {ℓ-suc ℓ} tt , ((lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt) , (lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt))))
      pPrAt : ∀ {n} (q u v : Fin n) → BoundedFo (Below′ σ) (liftFo (prAt q u v) (hPrAt q u v))
      pPrAt {n} q u v =
        (lift {ℓ-zero} {ℓ-suc ℓ} tt , pSgl {suc n} zero (suc u))
          , ( (lift {ℓ-zero} {ℓ-suc ℓ} tt , pPair {suc n} zero (suc u) (suc v))
            , (lift {ℓ-zero} {ℓ-suc ℓ} tt , (pSgl {suc n} zero (suc u) , pPair {suc n} zero (suc u) (suc v))) )
      pSucAt : ∀ {n} (i j : Fin n) → BoundedFo (Below′ σ) (liftFo (sucAt i j) (hSucAt i j))
      pSucAt i j =
        (lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt)
          , ( (lift {ℓ-zero} {ℓ-suc ℓ} tt , (lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt))
            , (lift {ℓ-zero} {ℓ-suc ℓ} tt , ((lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt) , (lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt))) )
      pShift : ∀ {n} (p' p : Fin n) → BoundedFo (Below′ σ) (liftFo (shiftPairAt p' p) (hShift p' p))
      pShift {n} p' p =
        ( lift {ℓ-zero} {ℓ-suc ℓ} tt , ( lift {ℓ-zero} {ℓ-suc ℓ} tt , ( lift {ℓ-zero} {ℓ-suc ℓ} tt
        , ( lift {ℓ-zero} {ℓ-suc ℓ} tt , ( lift {ℓ-zero} {ℓ-suc ℓ} tt
        , ( pPrAt {suc (suc (suc (suc (suc n))))} (suc (suc (suc (suc (suc p))))) (suc (suc (suc zero))) (suc (suc zero))
          , ( pPrAt {suc (suc (suc (suc (suc n))))} (suc (suc (suc (suc (suc p'))))) zero (suc (suc zero))
            , pSucAt {suc (suc (suc (suc (suc n))))} (suc (suc (suc zero))) zero ) ) ) ) ) ) )
      pSgl0 : ∀ {n} (k : Fin n) → BoundedFo (Below′ σ) (liftFo (sgl0At k) (hSgl0 k))
      pSgl0 k = (lift {ℓ-zero} {ℓ-suc ℓ} tt , (lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt)) , (lift {ℓ-zero} {ℓ-suc ℓ} tt , (lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt))
      pPair0 : ∀ {n} (k j : Fin n) → BoundedFo (Below′ σ) (liftFo (pair0At k j) (hPair0 k j))
      pPair0 k j =
        (lift {ℓ-zero} {ℓ-suc ℓ} tt , (lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt))
          , ( (lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt)
            , ( lift {ℓ-zero} {ℓ-suc ℓ} tt , ((lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt) , (lift {ℓ-zero} {ℓ-suc ℓ} tt , lift {ℓ-zero} {ℓ-suc ℓ} tt)) ) )
      pTag0 : ∀ {n} (s x : Fin n) → BoundedFo (Below′ σ) (liftFo (tag0At s x) (hTag0 s x))
      pTag0 {n} s x =
        (lift {ℓ-zero} {ℓ-suc ℓ} tt , pSgl0 {suc n} zero)
          , ( (lift {ℓ-zero} {ℓ-suc ℓ} tt , pPair0 {suc n} zero (suc x))
            , (lift {ℓ-zero} {ℓ-suc ℓ} tt , (pSgl0 {suc n} zero , pPair0 {suc n} zero (suc x))) )
      pConsAt : ∀ {n} (e' m e : Fin n) → BoundedFo (Below′ σ) (consAtL e' m e)
      pConsAt {n} e' m e =
        (lift {ℓ-zero} {ℓ-suc ℓ} tt , pTag0 {suc n} zero (suc m))
          , ( (lift {ℓ-zero} {ℓ-suc ℓ} tt , (lift {ℓ-zero} {ℓ-suc ℓ} tt , pShift {suc (suc n)} zero (suc zero)))
            , ( lift {ℓ-zero} {ℓ-suc ℓ} tt
              , ( pTag0 {suc n} zero (suc m)
                , (lift {ℓ-zero} {ℓ-suc ℓ} tt , pShift {suc (suc n)} (suc zero) zero) ) ) )

      hConsAt : ∀ {n} (e' m e : Fin n) → BoundedFo InL (consAt e' m e)
      hConsAt {n} e' m e =
        (lift {ℓ-zero} {ℓ-suc ℓ} tt , hTag0 {suc n} zero (suc m))
          , ( (lift {ℓ-zero} {ℓ-suc ℓ} tt , (lift {ℓ-zero} {ℓ-suc ℓ} tt , hShift {suc (suc n)} zero (suc zero)))
            , ( lift {ℓ-zero} {ℓ-suc ℓ} tt
              , ( hTag0 {suc n} zero (suc m)
                , (lift {ℓ-zero} {ℓ-suc ℓ} tt , hShift {suc (suc n)} (suc zero) zero) ) ) )

      appAtᴬ : ∀ {n} (f x y : Fin n) (δ : S ^ n)
             → ((δ RC.⊨ᴬ appAt f x y) ≡ (δ ⊨ʟ appAt f x y))
      appAtᴬ f x y δ = cong (⋁ S) (funExt (λ z →
        cong (λ q → (z ∈ˢʟ RAtS.⟦ var f ⟧ δ) ⊓ q)
          (Δ₀ᴬ (prAtL zero (suc x) (suc y))
             (Δ₀-liftFo (hPrAt zero (suc x) (suc y)) (Δ₀-prAt zero (suc x) (suc y)))
             (z ∷ δ))))

      num∈ρ₂ : (k : ℕ) → ⟨ fst (numeralS k) ∈ˢ Lset ρ₂ ⟩
      num∈ρ₂ k = Lρ₂η (Lset-mono {α = η} {β = ω} ω∈η (numeral∈limit k))

      tmIsᴬ : ∀ {n m} (t : Term S n) (δ : S ^ m) (v e : Fin m)
            → ((δ RC.⊨ᴬ tmIs t v e) ≡ (δ ⊨ʟ tmIs t v e))
      tmIsᴬ (con c) δ v e = refl
      tmIsᴬ (var i) δ v e = ⇔toPath fwd bwd
        where
        body : Formula S _
        body = (var zero ≐ con (numeralS (toℕ i))) ∧̇ appAt (suc e) zero (suc v)
        innerEq : (z : S)
                → (((z ∷ δ) RC.⊨ᴬ body) ≡ ((z ∷ δ) ⊨ʟ body))
        innerEq z = cong₂ _⊓_ refl (appAtᴬ (suc e) zero (suc v) (z ∷ δ))
        fwd : ⟨ δ RC.⊨ᴬ tmIs (var i) v e ⟩ → ⟨ δ ⊨ʟ tmIs (var i) v e ⟩
        fwd h = PT.rec (snd (δ ⊨ʟ tmIs (var i) v e))
          (λ { (z , (z∈ , hbody)) →
            ∣ z , (subst (λ Q → ⟨ Q ⟩) (innerEq z) hbody .fst
                 , subst (λ Q → ⟨ Q ⟩) (innerEq z) hbody .snd) ∣₁ }) h
        bwd : ⟨ δ ⊨ʟ tmIs (var i) v e ⟩ → ⟨ δ RC.⊨ᴬ tmIs (var i) v e ⟩
        bwd h = PT.rec (snd (δ RC.⊨ᴬ tmIs (var i) v e))
          (λ { (z , (h≐ , happ)) →
            ∣ numeralS (toℕ i) , (num∈ρ₂ (toℕ i)
              , ( refl
                , subst ⟨_⟩
                    (sym (appAtᴬ (suc e) zero (suc v) (numeralS (toℕ i) ∷ δ)))
                    (subst ⟨_⟩
                      (sym (appAt-adequate (suc e) zero (suc v) (numeralS (toℕ i) ∷ δ)))
                      (subst (λ w → ⟨ pr w (fst (lookup (suc v) (z ∷ δ)))
                                      ∈ fst (lookup (suc e) (z ∷ δ)) ⟩)
                        h≐
                        (subst ⟨_⟩ (appAt-adequate (suc e) zero (suc v) (z ∷ δ)) happ))) ) )
            ∣₁ }) h

      Δ₀consAtL : ∀ {n} (e' m e : Fin n) → Δ₀ (consAtL e' m e)
      Δ₀consAtL e' m e = Δ₀-liftFo (hConsAt e' m e) (Δ₀-consAt e' m e)

      -- The stage-bounded reading of a Δ₀ formula at one environment.
      L∈Lsuc : (μ : V ℓ) (oμ : IsOrd μ) → ⟨ Lset μ ∈ˢ Lset (sucV μ) ⟩
      L∈Lsuc μ oμ = subst (λ w → ⟨ Lset μ ∈ˢ w ⟩) (sym (Lset-suc μ))
                      (𝒟ₒ-intro (Lset μ) (Lset μ) ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset μ) ∣₁)

      -- Two truth values agreeing under a guard.
      ⊓under : (p q q' : Ω) → (⟨ p ⟩ → q ≡ q') → ((p ⊓ q) ≡ (p ⊓ q'))
      ⊓under p q q' h = ⇔toPath
        (λ { (hp , hq) → hp , subst {A = Ω} (λ F → ⟨ F ⟩) (h hp) hq })
        (λ { (hp , hq') → hp , subst {A = Ω} (λ F → ⟨ F ⟩) (sym (h hp)) hq' })

      ω∈ρ : ⟨ ω ∈ˢ ρ ⟩
      ω∈ρ = oρ .fst ω∈η η∈ρ
      ∅∈Lρ : ⟨ ∅ ∈ˢ Lset ρ ⟩
      ∅∈Lρ = Lset-mono {α = ρ} {β = ω} ω∈ρ (numeral∈limit zero)

      -- Every tagged pair inside a member of the environment set has
      -- its value in fst A.
      pair∈A : (x : S) → ⟨ x ∈ˢʟ envSet A nψ ⟩
             → (u w : V ℓ) → ⟨ pr u w ∈ fst x ⟩ → ⟨ w ∈ fst A ⟩
      pair∈A x x∈ u w hw = PT.rec (snd (w ∈ fst A))
        (λ { (d , r1) →
        PT.rec (snd (w ∈ fst A)) (λ { (b , (hd , (hb , hov))) →
        PT.rec (snd (w ∈ fst A))
          (λ { (p , (q , (hp∈ , (hq∈ , heq)))) →
            subst (λ a → ⟨ w ∈ a ⟩) hb
              (subst (λ z → ⟨ z ∈ fst b ⟩) (sym (pr-inj heq .snd)) hq∈) })
          (pairsIn-out {3} (suc (suc zero)) (suc zero) zero (b ∷ d ∷ x ∷ [])
            (envOver-pairs (suc (suc zero)) (suc zero) zero (b ∷ d ∷ x ∷ []) hov)
            (pr u w , isLx) hw) }) r1 })
        (subst ⟨_⟩ (envSet-mem A nψ x) x∈ .snd)
        where
        isLx : ⟨ isL (pr u w) ⟩
        isLx = isL-trans {x = fst x} {y = pr u w} hw (snd x)

      -- The value a tmIs-satisfaction pins its value slot to, as an
      -- element of Lset σ.
      tmVal : ∀ {n} (t : Term ⟪ fst A ⟫ n) {m} (γ : S ^ m) (v e : Fin m)
            → ⟨ lookup e γ ∈ˢʟ envSet A nψ ⟩
            → ⟨ γ ⊨ʟ tmIs (mapTm (asConst A) t) v e ⟩
            → Σ[ a ∈ V ℓ ] (⟨ a ∈ˢ Lset ρ ⟩ × (fst (lookup v γ) ≡ a))
      tmVal (con m) γ v e hz h = fst (asConst A m) , (as∈ρ m , h)
      tmVal (var i) γ v e hz h =
        fst (lookup v γ) , (Lρη (Lset-trans-set′ η (fst (lookup v γ)) (fst A) hv∈ hAη) , refl)
        where
        hv∈ : ⟨ fst (lookup v γ) ∈ fst A ⟩
        hv∈ = pair∈A (lookup e γ) hz (# (toℕ i)) (fst (lookup v γ)) (tmIs-var-out i γ v e h)

      -- The L element presenting a pinned value.
      mkS : (a : V ℓ) → ⟨ a ∈ˢ Lset σ ⟩ → S
      mkS a a∈ = a , Lset→isL σ oσ a a∈

      -- Element equality from underlying-set equality.
      ≡S : (a b : S) → fst a ≡ fst b → a ≡ b
      ≡S a b e = Σ≡Prop (λ z → snd (isL z)) e

      -- The two value slots of an atom pinned at once.
      pin2 : ∀ {n} (t u : Term ⟪ fst A ⟫ n) (x : S) (hx : ⟨ x ∈ˢʟ envSet A nψ ⟩)
           → (v w : S)
           → ⟨ (w ∷ v ∷ x ∷ []) ⊨ʟ tmIs (mapTm (asConst A) t) (suc zero) (suc (suc zero)) ⟩
           → ⟨ (w ∷ v ∷ x ∷ []) ⊨ʟ tmIs (mapTm (asConst A) u) zero (suc (suc zero)) ⟩
           → Σ[ vA ∈ V ℓ ] (Σ[ wA ∈ V ℓ ]
               ((⟨ vA ∈ˢ Lset ρ ⟩ × (⟨ wA ∈ˢ Lset ρ ⟩
                 × ((fst v ≡ vA) × (fst w ≡ wA))))))
      pin2 t u x hx v w ht hu =
        tmVal t (w ∷ v ∷ x ∷ []) (suc zero) (suc (suc zero)) hx ht .fst ,
          (tmVal u (w ∷ v ∷ x ∷ []) zero (suc (suc zero)) hx hu .fst ,
            ( (tmVal t (w ∷ v ∷ x ∷ []) (suc zero) (suc (suc zero)) hx ht .snd .fst)
            , ( (tmVal u (w ∷ v ∷ x ∷ []) zero (suc (suc zero)) hx hu .snd .fst)
              , ( (tmVal t (w ∷ v ∷ x ∷ []) (suc zero) (suc (suc zero)) hx ht .snd .snd)
                , (tmVal u (w ∷ v ∷ x ∷ []) zero (suc (suc zero)) hx hu .snd .snd) ) ) ))

      -- A tmIs satisfaction transports along equalities of the value
      -- and environment entries.
      reTm : ∀ {n m} (t : Term ⟪ fst A ⟫ n) (v e : Fin m)
           → (γ γ' : S ^ m)
           → lookup v γ' ≡ lookup v γ
           → lookup e γ' ≡ lookup e γ
           → ⟨ γ ⊨ʟ tmIs (mapTm (asConst A) t) v e ⟩
           → ⟨ γ' ⊨ʟ tmIs (mapTm (asConst A) t) v e ⟩
      reTm (con m) v e γ γ' e1 e2 h =
        subst (λ z → ⟨ z ≈ˢʟ asConst A m ⟩) (sym e1) h
      reTm (var i) v e γ γ' e1 e2 h =
        tmIs-var-in i γ' v e
          (subst (λ z → ⟨ pr (# (toℕ i)) z ∈ fst (lookup e γ') ⟩)
            (cong fst (sym e1))
            (subst (λ z → ⟨ pr (# (toℕ i)) (fst (lookup v γ)) ∈ z ⟩)
              (cong fst (sym e2))
              (tmIs-var-out i γ v e h)))

      -- The atom clause's body rebuilt at the pinned entries, in the
      -- stage-bounded reading.
      atomBody∈ : ∀ {n} (t u : Term ⟪ fst A ⟫ n) (x : S) (hx : ⟨ x ∈ˢʟ envSet A nψ ⟩)
               → (v w : S)
               → ⟨ (w ∷ v ∷ x ∷ []) ⊨ʟ tmIs (mapTm (asConst A) t) (suc zero) (suc (suc zero)) ⟩
               → ⟨ (w ∷ v ∷ x ∷ []) ⊨ʟ tmIs (mapTm (asConst A) u) zero (suc (suc zero)) ⟩
               → ⟨ fst v ∈ fst w ⟩
               → Σ[ vS ∈ S ] (Σ[ wS ∈ S ]
                   ((⟨ fst vS ∈ˢ Lset ρ₂ ⟩ × (⟨ fst wS ∈ˢ Lset ρ₂ ⟩
                     × ((fst vS ≡ fst v) × (fst wS ≡ fst w))))
                    × ⟨ (wS ∷ vS ∷ x ∷ []) RC.⊨ᴬ
                         (tmIs (mapTm (asConst A) t) (suc zero) (suc (suc zero))
                          ∧̇ (tmIs (mapTm (asConst A) u) zero (suc (suc zero))
                           ∧̇ (var (suc zero) ∈̇ var zero))) ⟩))
      atomBody∈ {n} t u x hx v w ht hu hvw =
        vS , wS , ((vS∈ρ₂ , (wS∈ρ₂ , (fstv , fstw))) , bodyᴬ)
        where
        pv = pin2 t u x hx v w ht hu
        vA : V ℓ
        wA : V ℓ
        vA = pv .fst
        wA = pv .snd .fst
        vS = mkSρ vA (pv .snd .snd .fst)
        wS = mkSρ wA (pv .snd .snd .snd .fst)
        vS∈ρ₂ : ⟨ fst vS ∈ˢ Lset ρ₂ ⟩
        vS∈ρ₂ = Lρ₂ρ (pv .snd .snd .fst)
        wS∈ρ₂ : ⟨ fst wS ∈ˢ Lset ρ₂ ⟩
        wS∈ρ₂ = Lρ₂ρ (pv .snd .snd .snd .fst)
        fstv : fst vS ≡ fst v
        fstv = sym (pv .snd .snd .snd .snd .fst)
        fstw : fst wS ≡ fst w
        fstw = sym (pv .snd .snd .snd .snd .snd)
        e1 : vS ≡ v
        e1 = ≡S vS v fstv
        e2 : wS ≡ w
        e2 = ≡S wS w fstw
        e3 : x ≡ x
        e3 = refl
        ht' : ⟨ (wS ∷ vS ∷ x ∷ []) ⊨ʟ tmIs (mapTm (asConst A) t) (suc zero) (suc (suc zero)) ⟩
        ht' = reTm t (suc zero) (suc (suc zero)) (w ∷ v ∷ x ∷ []) (wS ∷ vS ∷ x ∷ []) e1 e3 ht
        hu' : ⟨ (wS ∷ vS ∷ x ∷ []) ⊨ʟ tmIs (mapTm (asConst A) u) zero (suc (suc zero)) ⟩
        hu' = reTm u zero (suc (suc zero)) (w ∷ v ∷ x ∷ []) (wS ∷ vS ∷ x ∷ []) e2 e3 hu
        htᴬ : ⟨ (wS ∷ vS ∷ x ∷ []) RC.⊨ᴬ tmIs (mapTm (asConst A) t) (suc zero) (suc (suc zero)) ⟩
        htᴬ = subst (λ Q → ⟨ Q ⟩) (sym (tmIsᴬ (mapTm (asConst A) t) (wS ∷ vS ∷ x ∷ []) (suc zero) (suc (suc zero)))) ht'
        huᴬ : ⟨ (wS ∷ vS ∷ x ∷ []) RC.⊨ᴬ tmIs (mapTm (asConst A) u) zero (suc (suc zero)) ⟩
        huᴬ = subst (λ Q → ⟨ Q ⟩) (sym (tmIsᴬ (mapTm (asConst A) u) (wS ∷ vS ∷ x ∷ []) zero (suc (suc zero)))) hu'
        hvw' : ⟨ fst vS ∈ fst wS ⟩
        hvw' = subst (λ z → ⟨ z ∈ fst wS ⟩) (sym fstv)
                 (subst (λ z → ⟨ fst v ∈ z ⟩) (sym fstw) hvw)
        bodyᴬ : ⟨ (wS ∷ vS ∷ x ∷ []) RC.⊨ᴬ
                    (tmIs (mapTm (asConst A) t) (suc zero) (suc (suc zero))
                     ∧̇ (tmIs (mapTm (asConst A) u) zero (suc (suc zero))
                      ∧̇ (var (suc zero) ∈̇ var zero))) ⟩
        bodyᴬ = htᴬ , (huᴬ , hvw')

      atomBody≐ : ∀ {n} (t u : Term ⟪ fst A ⟫ n) (x : S) (hx : ⟨ x ∈ˢʟ envSet A nψ ⟩)
               → (v w : S)
               → ⟨ (w ∷ v ∷ x ∷ []) ⊨ʟ tmIs (mapTm (asConst A) t) (suc zero) (suc (suc zero)) ⟩
               → ⟨ (w ∷ v ∷ x ∷ []) ⊨ʟ tmIs (mapTm (asConst A) u) zero (suc (suc zero)) ⟩
               → fst v ≡ fst w
               → Σ[ vS ∈ S ] (Σ[ wS ∈ S ]
                   ((⟨ fst vS ∈ˢ Lset ρ₂ ⟩ × (⟨ fst wS ∈ˢ Lset ρ₂ ⟩
                     × ((fst vS ≡ fst v) × (fst wS ≡ fst w))))
                    × ⟨ (wS ∷ vS ∷ x ∷ []) RC.⊨ᴬ
                         (tmIs (mapTm (asConst A) t) (suc zero) (suc (suc zero))
                          ∧̇ (tmIs (mapTm (asConst A) u) zero (suc (suc zero))
                           ∧̇ (var (suc zero) ≐ var zero))) ⟩))
      atomBody≐ {n} t u x hx v w ht hu hvw =
        vS , wS , ((vS∈ρ₂ , (wS∈ρ₂ , (fstv , fstw))) , bodyᴬ)
        where
        pv = pin2 t u x hx v w ht hu
        vA : V ℓ
        wA : V ℓ
        vA = pv .fst
        wA = pv .snd .fst
        vS = mkSρ vA (pv .snd .snd .fst)
        wS = mkSρ wA (pv .snd .snd .snd .fst)
        vS∈ρ₂ : ⟨ fst vS ∈ˢ Lset ρ₂ ⟩
        vS∈ρ₂ = Lρ₂ρ (pv .snd .snd .fst)
        wS∈ρ₂ : ⟨ fst wS ∈ˢ Lset ρ₂ ⟩
        wS∈ρ₂ = Lρ₂ρ (pv .snd .snd .snd .fst)
        fstv : fst vS ≡ fst v
        fstv = sym (pv .snd .snd .snd .snd .fst)
        fstw : fst wS ≡ fst w
        fstw = sym (pv .snd .snd .snd .snd .snd)
        e1 : vS ≡ v
        e1 = ≡S vS v fstv
        e2 : wS ≡ w
        e2 = ≡S wS w fstw
        e3 : x ≡ x
        e3 = refl
        ht' : ⟨ (wS ∷ vS ∷ x ∷ []) ⊨ʟ tmIs (mapTm (asConst A) t) (suc zero) (suc (suc zero)) ⟩
        ht' = reTm t (suc zero) (suc (suc zero)) (w ∷ v ∷ x ∷ []) (wS ∷ vS ∷ x ∷ []) e1 e3 ht
        hu' : ⟨ (wS ∷ vS ∷ x ∷ []) ⊨ʟ tmIs (mapTm (asConst A) u) zero (suc (suc zero)) ⟩
        hu' = reTm u zero (suc (suc zero)) (w ∷ v ∷ x ∷ []) (wS ∷ vS ∷ x ∷ []) e2 e3 hu
        htᴬ : ⟨ (wS ∷ vS ∷ x ∷ []) RC.⊨ᴬ tmIs (mapTm (asConst A) t) (suc zero) (suc (suc zero)) ⟩
        htᴬ = subst (λ Q → ⟨ Q ⟩) (sym (tmIsᴬ (mapTm (asConst A) t) (wS ∷ vS ∷ x ∷ []) (suc zero) (suc (suc zero)))) ht'
        huᴬ : ⟨ (wS ∷ vS ∷ x ∷ []) RC.⊨ᴬ tmIs (mapTm (asConst A) u) zero (suc (suc zero)) ⟩
        huᴬ = subst (λ Q → ⟨ Q ⟩) (sym (tmIsᴬ (mapTm (asConst A) u) (wS ∷ vS ∷ x ∷ []) zero (suc (suc zero)))) hu'
        hvw' : fst vS ≡ fst wS
        hvw' = fstv ∙ (hvw ∙ sym fstw)
        bodyᴬ : ⟨ (wS ∷ vS ∷ x ∷ []) RC.⊨ᴬ
                    (tmIs (mapTm (asConst A) t) (suc zero) (suc (suc zero))
                     ∧̇ (tmIs (mapTm (asConst A) u) zero (suc (suc zero))
                      ∧̇ (var (suc zero) ≐ var zero))) ⟩
        bodyᴬ = htᴬ , (huᴬ , hvw')

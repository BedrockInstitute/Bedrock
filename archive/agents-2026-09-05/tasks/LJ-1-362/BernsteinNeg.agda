{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.362] stage 1 of Cantor-Bernstein over a model of ZF: the
-- generic module, the coded-map formula families, the CSB statement,
-- the Tarski separation formula, and the pair-reader adequacy against
-- the record's derived pair.
--
-- DD23: no mathematical prose until both trophies land.  This master
-- carries code and code comments only.
--
-- The parameter-free families sglAt, pairAt, prAt, appAt, svAt,
-- inDomAt, domAt, injAt, inRanAt, ranAt are duplicated from the L
-- chapters (src/L/Coding/Base.lagda.md, Model.lagda.md,
-- Injection.lagda.md), where they sit at the carrier of S_ʟ.  They
-- carry no constant, so the same trees typecheck at any carrier
-- ([LJ-1.361] part 4).  Moving them out of the L chapters is a
-- separate ruling, priced at about 125 lines with 10 consumers
-- rewiring ([LJ-1.361] part 4).  The duplication cost is measured in
-- the [LJ-1.362] report.
--
-- lem is the classical-cone parameter the stage-2 proof consumes
-- (case splits on membership in the bad set).  It sits in the
-- telescope now so stage 2 does not change the module signature.
--
-- ≈ˢ-is-path.  The readers below read the object equality ≐, whose
-- satisfaction is the structure field ≈ˢ, while the derived pair's
-- specification and extensionality speak paths.  The record
-- FOL.ZFModel does NOT force ≈ˢ to be the path equality: at the
-- structure V with ≈ˢ constantly ⊥ every field still holds, the
-- derived pair degenerates to ∅, and no pair reader can be adequate
-- against it.  So the adequacy is proved under one module hypothesis:
-- ≈ˢ is the path equality, as an equality of hProps.  Both delivered
-- instances satisfy it, at 𝒮ᵥ by refl and at 𝒮ʟ by Σ≡Prop in both
-- directions.  MEASURED in the [LJ-1.362] report.
--
-- The derived pair lives inside the record isZFModel, so the ordered
-- pair prˢ and its adequacy are model-relative: they sit in one
-- module parameterized by the model (P-h), while the pure syntax
-- below them stays at the structure level.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )

module LJ-1-362.BernsteinNeg
  {ℓ : Level} (lem : LEM ℓ) (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (≈ˢ-is-path : (x y : ZFStructure.S 𝒮)
              → (ZFStructure._≈ˢ_ 𝒮 x y)
              ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y)) where

open import FOL.Syntax
  using ( Term; var; con; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ∀̇_; ∃̇_
        ; ∀̇∈; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( _^_; module At )
import FOL.ZFModel

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮 using ( S; isSetS; _≈ˢ_; _∈ˢ_ )
open At S id using ( _⊨_; ⟦_⟧ )

module ZF = FOL.ZFModel 𝒮

import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.Functions.Logic using ( ⇔toPath )

-- =====================================================================
-- A.  The pair readers: parameter-free syntax at the abstract carrier,
--     duplicated from L.Coding.Base, which writes the same trees at V.
--     Pure syntax, no model needed.
-- =====================================================================

sglAt : ∀ {n} → Fin n → Fin n → Formula S n
sglAt k i = (var i ∈̇ var k) ∧̇ (∀̇∈ (var k) (var zero ≐ var (suc i)))

pairAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
pairAt k i j = (var i ∈̇ var k) ∧̇ ((var j ∈̇ var k)
            ∧̇ (∀̇∈ (var k) ((var zero ≐ var (suc i))
                         ∨̇ (var zero ≐ var (suc j)))))

prAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
prAt q u v = (∃̇∈ (var q) (sglAt zero (suc u)))
          ∧̇ ((∃̇∈ (var q) (pairAt zero (suc u) (suc v)))
          ∧̇ (∀̇∈ (var q) (sglAt zero (suc u) ∨̇ pairAt zero (suc u) (suc v))))

-- prMemAt reads "the pair of the values of i and j is a member of the
-- set named by t": L.Coding.Model's appAt with the code allowed to be
-- any term, so the constant codes of the Tarski formula below are the
-- same operation.  appAt is the variable-code instance.
prMemAt : ∀ {n} → Term S n → Fin n → Fin n → Formula S n
prMemAt t i j = ∃̇∈ t (prAt zero (suc i) (suc j))

appAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
appAt f x y = prMemAt (var f) x y

-- =====================================================================
-- B.  The coded-map families (duplicated from L.Coding.Model and
--     L.Coding.Injection, verbatim trees): single-valuedness, the
--     two-sided domain and range clauses, injectivity, and the
--     one-sided value-boundedness clause that replaces InjCode's
--     ambient fourth conjunct ([LJ-1.353] section 3).  Pure syntax.
-- =====================================================================

svAt : ∀ {n} → Fin n → Formula S n
svAt f = ∀̇ (∀̇ (∀̇ (
      appAt (suc (suc (suc f))) (suc (suc zero)) (suc zero)
  ⇒̇ (appAt (suc (suc (suc f))) (suc (suc zero)) zero
  ⇒̇ (var (suc zero) ≐ var zero)))))

inDomAt : ∀ {n} → Fin n → Fin n → Formula S n
inDomAt f x = ∃̇ (appAt (suc f) (suc x) zero)

domAt : ∀ {n} → Fin n → Fin n → Formula S n
domAt f d = ∀̇ ( (inDomAt (suc f) zero ⇒̇ (var zero ∈̇ var (suc d)))
             ∧̇ ((var zero ∈̇ var (suc d)) ⇒̇ inDomAt (suc f) zero) )

injAt : ∀ {n} → Fin n → Formula S n
injAt f = ∀̇ (∀̇ (∀̇ (
      appAt (suc (suc (suc f))) (suc zero) (suc (suc zero))
  ⇒̇ (appAt (suc (suc (suc f))) zero (suc (suc zero))
  ⇒̇ (var (suc zero) ≐ var zero)))))

inRanAt : ∀ {n} → Fin n → Fin n → Formula S n
inRanAt f x = ∃̇ (appAt (suc f) zero (suc x))

ranAt : ∀ {n} → Fin n → Fin n → Formula S n
ranAt f c = ∀̇ ( (inRanAt (suc f) zero ⇒̇ (var zero ∈̇ var (suc c)))
             ∧̇ ((var zero ∈̇ var (suc c)) ⇒̇ inRanAt (suc f) zero) )

-- every member of the code is a pair whose second component lies in
-- the target: for F read at (F ∷ b ∷ []), values of F lie in b
rbdAt : ∀ {n} → Fin n → Fin n → Formula S n
rbdAt f c = ∀̇∈ (var f)
  ( ∃̇ ( ∃̇ ( (prAt (suc (suc zero)) zero (suc zero))
          ∧̇ (var (suc zero) ∈̇ var (suc (suc (suc c))))) ) )

-- =====================================================================
-- C.  The statement.  A coded bijection from a to b: a code
--     single-valued, with domain exactly a, injective, with range
--     exactly b.  CSB: two coded injections, one each way, give a
--     coded bijection.  Stage 2 proves it; the type is the contract.
--     The range-bounded hypotheses read at (F ∷ b ∷ []) and
--     (G ∷ a ∷ []): the VALUE target, not the domain slot.
-- =====================================================================

BijCode : S → S → S → Type ℓ
BijCode H a b =
    ⟨ (H ∷ a ∷ []) ⊨ svAt zero ⟩
  × ⟨ (H ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩
  × ⟨ (H ∷ a ∷ []) ⊨ injAt zero ⟩
  × ⟨ (H ∷ b ∷ []) ⊨ ranAt zero (suc zero) ⟩

CSB : ZF.isZFModel → Type ℓ
CSB mod =
    (a b F G : S)
  → ⟨ (F ∷ a ∷ []) ⊨ svAt zero ⟩
  → ⟨ (F ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩
  → ⟨ (F ∷ a ∷ []) ⊨ injAt zero ⟩
  → ⟨ (F ∷ b ∷ []) ⊨ rbdAt zero (suc zero) ⟩
  → ⟨ (G ∷ b ∷ []) ⊨ svAt zero ⟩
  → ⟨ (G ∷ b ∷ []) ⊨ domAt zero (suc zero) ⟩
  → ⟨ (G ∷ b ∷ []) ⊨ injAt zero ⟩
  → ⟨ (G ∷ a ∷ []) ⊨ rbdAt zero (suc zero) ⟩
  → ∥ Σ[ H ∈ S ] BijCode H a b ∥₁

-- =====================================================================
-- D.  Adequacy, under a model.  prˢ U W = pair (pair U U) (pair U W),
--     the Kuratowski pair built from the record's derived pairing
--     operation alone.  Membership in pair a b is (x ≈ˢ a) ⊔ (x ≈ˢ b),
--     by pair-spec; ≈ˢ and paths are exchanged through ≈ˢ-is-path.
--     SglOf and PairOf are the membership shapes the readers'
--     satisfaction unfolds to.  prAt-adequate is the stage-1 target:
--     satisfaction of the reader IS "the value of q is the derived
--     pair of the values of u and v", as a path, proved by the two
--     halves of prChar in one line each, because the truth algebra's
--     ⊓ is a product, its ⋁ a truncated sum and its ≈ˢ a path
--     (through ≈ˢ-is-path), each by a definitional clause of ⊨.
-- =====================================================================

module Adequacy (mod : ZF.isZFModel) where

  open ZF.isZFModel mod using ( extensional; pair; pair-spec )

  prˢ : S → S → S
  prˢ U W = pair (pair U U) (pair U W)

  private
    ≈ˢ→≡ : {x y : S} → ⟨ x ≈ˢ y ⟩ → x ≡ y
    ≈ˢ→≡ {x} {y} h = subst ⟨_⟩ (≈ˢ-is-path x y) h

    ≡→≈ˢ : {x y : S} → x ≡ y → ⟨ x ≈ˢ y ⟩
    ≡→≈ˢ {x} {y} h = subst ⟨_⟩ (sym (≈ˢ-is-path x y)) h

    -- membership transport along the member's ≈ˢ
    ∈ˢ-mem-tr : {U x w : S} → ⟨ x ≈ˢ U ⟩ → ⟨ U ∈ˢ w ⟩ → ⟨ x ∈ˢ w ⟩
    ∈ˢ-mem-tr {U} {x} {w} e hu = subst (λ z → ⟨ z ∈ˢ w ⟩) (sym (≈ˢ→≡ e)) hu

    SglOf : S → S → Type ℓ
    SglOf U w = ⟨ U ∈ˢ w ⟩ × ((z : S) → ⟨ z ∈ˢ w ⟩ → ⟨ z ≈ˢ U ⟩)

    PairOf : S → S → S → Type ℓ
    PairOf U W w =
      ⟨ U ∈ˢ w ⟩ × (⟨ W ∈ˢ w ⟩ × ((z : S) → ⟨ z ∈ˢ w ⟩
                                      → ∥ ⟨ z ≈ˢ U ⟩ ⊎ ⟨ z ≈ˢ W ⟩ ∥₁))

    sglOf→≡ : {U w : S} → SglOf U w → w ≡ pair U U
    sglOf→≡ {U} {w} (hu , hall) = extensional (λ x → mem x)
      where
      mem : (x : S) → (x ∈ˢ w) ≡ (x ∈ˢ pair U U)
      mem x = ⇔toPath (λ m → ∣ Sum.inl (hall x m) ∣₁)
                      (λ s → PT.rec (snd (x ∈ˢ w))
                              (Sum.rec (λ e → ∈ˢ-mem-tr e hu)
                                       (λ e → ∈ˢ-mem-tr e hu))
                              s)
               ∙ sym (pair-spec U U x)

    pairOf→≡ : {U W w : S} → PairOf U W w → w ≡ pair U W
    pairOf→≡ {U} {W} {w} (hu , hv , hall) = extensional (λ x → mem x)
      where
      mem : (x : S) → (x ∈ˢ w) ≡ (x ∈ˢ pair U W)
      mem x = ⇔toPath (λ m → hall x m)
                      (λ s → PT.rec (snd (x ∈ˢ w))
                              (Sum.rec (λ e → ∈ˢ-mem-tr e hu)
                                       (λ e → ∈ˢ-mem-tr e hv))
                              s)
               ∙ sym (pair-spec U W x)

    sglOf-pair : (U : S) → SglOf U (pair U U)
    sglOf-pair U =
      ( subst ⟨_⟩ (sym (pair-spec U U U)) ∣ Sum.inl (≡→≈ˢ refl) ∣₁
      , (λ z m → PT.rec (snd (z ≈ˢ U)) (Sum.rec (λ e → e) (λ e → e))
           (subst ⟨_⟩ (pair-spec U U z) m)) )

    pairOf-pair : (U W : S) → PairOf U W (pair U W)
    pairOf-pair U W =
      ( subst ⟨_⟩ (sym (pair-spec U W U)) ∣ Sum.inl (≡→≈ˢ refl) ∣₁
      , subst ⟨_⟩ (sym (pair-spec U W W)) ∣ Sum.inr (≡→≈ˢ refl) ∣₁
      , (λ z m → subst ⟨_⟩ (pair-spec U W z) m) )

    sglOf-subst : {U w : S} → w ≡ pair U U → SglOf U w
    sglOf-subst {U} e = subst (SglOf U) (sym e) (sglOf-pair U)

    pairOf-subst : {U W w : S} → w ≡ pair U W → PairOf U W w
    pairOf-subst {U} {W} e = subst (PairOf U W) (sym e) (pairOf-pair U W)

    -- the three-clause characterization of the derived ordered pair
    prChar-fwd : (Q U W : S)
      → ∥ Σ[ w ∈ S ] (⟨ w ∈ˢ Q ⟩ × SglOf U w) ∥₁
      → ∥ Σ[ w ∈ S ] (⟨ w ∈ˢ Q ⟩ × PairOf U W w) ∥₁
      → ((y : S) → ⟨ y ∈ˢ Q ⟩ → ∥ SglOf U y ⊎ PairOf U W y ∥₁)
      → Q ≡ prˢ U W
    prChar-fwd Q U W h₁ h₂ h₃ = extensional (λ x → mem x)
      where
      pUU pUW : S
      pUU = pair U U
      pUW = pair U W

      mem : (x : S) → (x ∈ˢ Q) ≡ (x ∈ˢ prˢ U W)
      mem x = ⇔toPath fwd bwd ∙ sym (pair-spec pUU pUW x)
        where
        fwd : ⟨ x ∈ˢ Q ⟩ → ⟨ (x ≈ˢ pUU) ⊔ (x ≈ˢ pUW) ⟩
        fwd m = PT.map (λ { (Sum.inl s) → Sum.inl (≡→≈ˢ (sglOf→≡ s))
                          ; (Sum.inr p) → Sum.inr (≡→≈ˢ (pairOf→≡ p)) })
                       (h₃ x m)

        bwd : ⟨ (x ≈ˢ pUU) ⊔ (x ≈ˢ pUW) ⟩ → ⟨ x ∈ˢ Q ⟩
        bwd s = PT.rec (snd (x ∈ˢ Q))
          (Sum.rec (λ e → PT.rec (snd (x ∈ˢ Q))
                            (λ { (w , w∈Q , sg) →
                              subst (λ z → ⟨ z ∈ˢ Q ⟩)
                                (sym (≈ˢ→≡ e ∙ sym (sglOf→≡ sg))) w∈Q })
                            h₁)
                   (λ e → PT.rec (snd (x ∈ˢ Q))
                            (λ { (w , w∈Q , p) →
                              subst (λ z → ⟨ z ∈ˢ Q ⟩)
                                (sym (≈ˢ→≡ e ∙ sym (pairOf→≡ p))) w∈Q })
                            h₂))
          s

    prChar-bwd : (Q U W : S) → Q ≡ prˢ U W
      → (∥ Σ[ w ∈ S ] (⟨ w ∈ˢ Q ⟩ × SglOf U w) ∥₁)
      × ((∥ Σ[ w ∈ S ] (⟨ w ∈ˢ Q ⟩ × PairOf U W w) ∥₁)
      × ((y : S) → ⟨ y ∈ˢ Q ⟩ → ∥ SglOf U y ⊎ PairOf U W y ∥₁))
    prChar-bwd Q U W e = h₁ , h₂ , h₃
      where
      pUU pUW : S
      pUU = pair U U
      pUW = pair U W

      inQ : {z : S} → ⟨ z ∈ˢ prˢ U W ⟩ → ⟨ z ∈ˢ Q ⟩
      inQ {z} h = subst (λ z' → ⟨ z ∈ˢ z' ⟩) (sym e) h

      h₁ : ∥ Σ[ w ∈ S ] (⟨ w ∈ˢ Q ⟩ × SglOf U w) ∥₁
      h₁ = ∣ pUU , inQ (subst ⟨_⟩ (sym (pair-spec pUU pUW pUU))
                            ∣ Sum.inl (≡→≈ˢ refl) ∣₁) , sglOf-pair U ∣₁

      h₂ : ∥ Σ[ w ∈ S ] (⟨ w ∈ˢ Q ⟩ × PairOf U W w) ∥₁
      h₂ = ∣ pUW , inQ (subst ⟨_⟩ (sym (pair-spec pUU pUW pUW))
                            ∣ Sum.inr (≡→≈ˢ refl) ∣₁) , pairOf-pair U W ∣₁

      h₃ : (y : S) → ⟨ y ∈ˢ Q ⟩ → ∥ SglOf U y ⊎ PairOf U W y ∥₁
      h₃ y m = PT.map (λ { (Sum.inl q) → Sum.inl (sglOf-subst (≈ˢ→≡ q))
                         ; (Sum.inr q) → Sum.inr (pairOf-subst (≈ˢ→≡ q)) })
        (subst ⟨_⟩ (pair-spec pUU pUW y) (subst (λ z' → ⟨ y ∈ˢ z' ⟩) e m))

  prAt-adequate : ∀ {n} (q u v : Fin n) (γ : S ^ n)
    → (γ ⊨ prAt q u v)
      ≡ ((lookup q γ ≡ prˢ (lookup v γ) (lookup u γ)) , isSetS _ _)
  prAt-adequate q u v γ = ⇔toPath
    (λ { (h₁ , h₂ , h₃) →
         prChar-fwd (lookup q γ) (lookup u γ) (lookup v γ) h₁ h₂ h₃ })
    (λ p → prChar-bwd (lookup q γ) (lookup u γ) (lookup v γ) p)

  prMemAt-adequate : ∀ {n} (t : Term S n) (i j : Fin n) (γ : S ^ n)
    → (γ ⊨ prMemAt t i j)
      ≡ ((prˢ (lookup i γ) (lookup j γ)) ∈ˢ (⟦ t ⟧ γ))
  prMemAt-adequate t i j γ = ⇔toPath fwd bwd
    where
    step : (z : S)
         → ((z ∷ γ) ⊨ prAt zero (suc i) (suc j))
           ≡ ((z ≡ prˢ (lookup i γ) (lookup j γ)) , isSetS _ _)
    step z = prAt-adequate zero (suc i) (suc j) (z ∷ γ)

    fwd : ⟨ γ ⊨ prMemAt t i j ⟩
        → ⟨ (prˢ (lookup i γ) (lookup j γ)) ∈ˢ ⟦ t ⟧ γ ⟩
    fwd = PT.rec (snd ((prˢ (lookup i γ) (lookup j γ)) ∈ˢ ⟦ t ⟧ γ))
      (λ { (z , z∈ , h) →
        subst (λ w → ⟨ w ∈ˢ ⟦ t ⟧ γ ⟩) (subst ⟨_⟩ (step z) h) z∈ })

    bwd : ⟨ (prˢ (lookup i γ) (lookup j γ)) ∈ˢ ⟦ t ⟧ γ ⟩
        → ⟨ γ ⊨ prMemAt t i j ⟩
    bwd m = ∣ prˢ (lookup i γ) (lookup j γ) , m
               , subst ⟨_⟩ (sym (step _)) refl ∣₁

-- =====================================================================
-- E.  The Tarski separation.  Under a model and the four parameters,
--     the bad set is separated from a along "x lies in some closed
--     subset of a", the closed subsets collected over the members of
--     𝒫 a.  Closure: every g-preimage of a member of X has an
--     f-image inside X.  closedAt-adequate certifies the de Bruijn
--     arithmetic of the spelled formula, which typechecking alone
--     does not.  Stage 2 proves the three closure facts and the graph
--     carve from bad-spec; [LJ-1.361] MiniSep proved the container
--     green with the closure condition abstract.
-- =====================================================================

module Tarski (mod : ZF.isZFModel) (a b F G : S) where

  open ZF.isZFModel mod using ( separate; separate-spec; 𝒫 )
  open Adequacy mod using ( prˢ; prMemAt-adequate )

  -- var 0 = X the candidate subset, var 1 = x (unread by closure):
  --   ∀ m ∈ X.  ∀ u.  prˢ u m ∈ G  →  ∃ w ∈ X.  prˢ w u ∈ F
  closedAt : Formula S 2
  closedAt = ∀̇∈ (var zero)
    ( ∀̇ ( prMemAt (con G) zero (suc zero)
      ⇒̇ ∃̇∈ (var (suc (suc zero))) (prMemAt (con F) zero (suc zero)) ) )

  Closed : S → Ω
  Closed X = ⋀ S (λ m → (m ∈ˢ X) ⇒ (⋀ S (λ u → (prˢ u m ∈ˢ G)
    ⇒ (⋁ S (λ w → (w ∈ˢ X) ⊓ (prˢ w u ∈ˢ F))))))

  closedAt-adequate : (X x : S) → ((X ∷ x ∷ []) ⊨ closedAt) ≡ Closed X
  closedAt-adequate X x =
    cong (λ h → ⋀ S h) (funExt (λ m →
      cong (λ k → (m ∈ˢ X) ⇒ k) (cong (λ g → ⋀ S g) (funExt (λ u →
        cong₂ _⇒_
          (prMemAt-adequate (con G) zero (suc zero) (u ∷ m ∷ X ∷ x ∷ []))
          (wStep m u))))))
    where
    wStep : (m u : S)
      → ((u ∷ m ∷ X ∷ x ∷ [])
           ⊨ ∃̇∈ (var (suc (suc zero))) (prMemAt (con F) zero (suc zero)))
        ≡ ⋁ S (λ w → (w ∈ˢ X) ⊓ (prˢ w u ∈ˢ F))
    wStep m u = cong (λ g → ⋁ S g) (funExt (λ w →
      cong (λ Q → (w ∈ˢ X) ⊓ Q)
        (prMemAt-adequate (con F) zero (suc zero) (w ∷ u ∷ m ∷ X ∷ x ∷ []))))

  tarskiFo : Formula S 1
  tarskiFo = ∃̇∈ (con (𝒫 a)) ((var (suc zero) ∈̇ var zero) ∧̇ closedAt)

  bad : S
  bad = separate a tarskiFo

  bad-spec : (x : S) → (x ∈ˢ bad) ≡ ((x ∈ˢ a) ⊓ ((x ∷ []) ⊨ tarskiFo))
  bad-spec = separate-spec a tarskiFo

  -- the bounded collector computes to the truth algebra's sup with no
  -- translation layer ([LJ-1.361] MiniSep, closure now spelled)
  unfold : (x : S)
    → ((x ∷ []) ⊨ tarskiFo)
      ≡ ⋁ S (λ X → (X ∈ˢ 𝒫 a)
                 ⊓ ((X ∷ x ∷ []) ⊨ ((var (suc zero) ∈̇ var zero) ∧̇ closedAt)))
  unfold x = refl

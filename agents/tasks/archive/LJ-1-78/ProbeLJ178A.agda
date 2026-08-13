{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.78] probe A: does the MemAgree row's proof survive
-- conditional closure facts?
--
-- LJ-1.77 measured that the unguarded closure facts are uninhabitable:
--   innerK : (a b : S) → ⟨ fst (prʟ (numeralL 0) (prʟ a b)) ∈ K ⟩
--   pairK  : (a b : S) → ⟨ fst (prʟ a b) ∈ K ⟩
-- every set belongs to its own singleton, so each says every set
-- belongs to K, and ∈-irrefl refutes it.
--
-- The intended mathematics is Devlin's hull closure: the pair of two
-- elements already IN K is in K.  This probe makes the two facts
-- conditional for the ONE row MemAgree:
--   innerK : (a b : S) → ⟨ fst a ∈ K ⟩ → ⟨ fst b ∈ K ⟩
--           → ⟨ fst (prʟ (numeralL 0) (prʟ a b)) ∈ K ⟩
--   pairK  : (a b : S) → ⟨ fst a ∈ K ⟩ → ⟨ fst b ∈ K ⟩
--           → ⟨ fst (prʟ a b) ∈ K ⟩
-- and re-checks the row's out/back.  In back, the premises come from
-- the row's own codesK fact: from a shaped code c, codesK concludes
-- ar ∈ K × a ∈ K × b ∈ K.
--
-- The guarded BinaryShape'.in' takes the two membership witnesses as
-- explicit parameters; the row's back passes aK bK from codesK.
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ178A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
  ; ∃̇_; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈; Σ₁; σ-Δ₀; σ-∃ )
open import FOL.Manipulation.Parameters using ( countFo )
open import FOL.Manipulation.Relabelling using ( embed )
import FOL.Count
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset; IsOrd )
open import L.Absoluteness {ℓ} using ( Δ₀-liftFo )
open import L.Coding.Base {ℓ} using ( Δ₀-prAt )
open import L.Coding.Environment {ℓ} using ( Δ₀-consAt; Δ₀-sucAt )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ}
  using ( prAtL; appAt; appAt-adequate; consAtL; sucAtL; closedAt; domAt
        ; sucAtL-adequate
        ; extAt; extAt-in-both
        ; interAt; unionAt
        ; arityTagAtL; arityTagPairAtL
        ; arityTagAtL-adequate; arityTagPairAtL-adequate
        ; tagAtL; tagAtL-adequate; tagPairAtL-adequate; prAtL-adequate
        ; prʟ; prʟ-fst
        ; binShapeAt; unShapeAt; bothSameAt; oneSameAt; oneSuccAt; succSndAt
        ; binShape-out; binShape-in; unShape-out; unShape-in
        ; emptyAt; botClauseAt
        ; subValAt; subValSuccAt; binClauseAt; propRel
        ; negClauseAt; topClauseAt; forallClauseAt; existClauseAt
        ; body∀; body∃; bodyAll; bodyEx
        ; tmValAt; envSetAt; envOverAt; envOverAt-transport; implAt
        ; atomBody; memClauseAt; eqClauseAt; impClauseAt
        ; allInClauseAt; exInClauseAt
        ; svAt-in; svAt-out; domAt-intro; domAt-out; domAt-in
        ; valuesInAt-in; valuesInAt-out )
open import L.Hierarchy {ℓ} lem using ( Lset-only; Lset-defines )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Coding.Shape {ℓ}
  using ( isTmAt; shapes; binForm; unForm; bothTm; fstTm; noneB; noneU; zeroPay
        ; shapedAt )
open import L.Coding.CodeSet {ℓ} lem using ( hasWitnessAt; keyArityAtL )
open import L.Coding.Graph {ℓ} lem using ( satGraphAt; twelveAt )
open import L.Coding.Powerset {ℓ} lem using ( isCodeAt; DefBody; DefinesAt; envOneAt )
open import Cubical.Data.Vec using ( map )
open import Cubical.Data.Nat using ( _+_ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_; sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; squash₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

open import L.Condensation {ℓ} lem using
  ( arTagPairB; extAtB→extAt; extAt→extAtB
  ; module Mem; module AtomLeaf; module EnvSet )

-- =====================================================================
-- THE GUARDED BINARY SHAPE FRAME.
-- A copy of the master's BinaryShape
-- (src/L/Condensation.lagda.md:2608-2680) with the two closure facts
-- made conditional and the two membership witnesses threaded into
-- in'.  out is byte-identical to the master's: the forward direction
-- needs no closure fact.
-- =====================================================================
module BinaryShape' {m : ℕ} (tag K : Fin m) (k : ℕ) (γ : S ^ (5 + m)) where
  tagEq : Type (ℓ-suc ℓ)
  tagEq = fst (lookup (suc (suc (suc (suc (suc tag))))) γ) ≡ fst (numeralL k)

  numK : Type (ℓ-suc ℓ)
  numK = ⟨ fst (numeralL k) ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩

  -- GUARDED: the closure needs both components already in K.
  innerK : Type (ℓ-suc ℓ)
  innerK = (a b : S)
         → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩
         → ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩
         → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩

  pairK : Type (ℓ-suc ℓ)
  pairK = (a b : S)
        → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩
        → ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩
        → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩

  out : tagEq → ⟨ γ ⊨ arTagPairB tag K ⟩
      → ⟨ γ ⊨ arityTagPairAtL (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) k
                               (suc (suc zero)) (suc zero) ⟩
  out te h = transport (cong fst (sym (arityTagPairAtL-adequate (suc (suc (suc (suc zero))))
                         (suc (suc (suc zero))) k (suc (suc zero)) (suc zero) γ))) target
    where
    target : fst (lookup (suc (suc (suc (suc zero)))) γ)
           ≡ pr (fst (lookup (suc (suc (suc zero))) γ))
                (pr (# k) (pr (fst (lookup (suc (suc zero)) γ)) (fst (lookup (suc zero) γ))))
    target = PT.rec (setIsSet _ _)
      (λ { (z , (z∈ , (p , kz))) → PT.rec (setIsSet _ _)
        (λ { (t , (t∈ , (tt , kt))) → PT.rec (setIsSet _ _)
          (λ { (w , (w∈ , (zt , wb))) →
            let a₀ = fst (lookup (suc (suc zero)) γ)
                b₀ = fst (lookup (suc zero) γ)
                ar₀ = fst (lookup (suc (suc (suc zero))) γ)
                p' : fst (lookup (suc (suc (suc (suc (suc zero))))) (z ∷ γ))
                    ≡ pr (fst (lookup (suc (suc (suc (suc zero)))) (z ∷ γ)))
                         (fst (lookup zero (z ∷ γ)))
                p' = transport (cong fst (prAtL-adequate (suc (suc (suc (suc (suc zero)))))
                      (suc (suc (suc (suc zero)))) zero (z ∷ γ))) p
                zt' : fst (lookup (suc (suc zero)) (w ∷ t ∷ z ∷ γ))
                     ≡ pr (fst (lookup (suc zero) (w ∷ t ∷ z ∷ γ)))
                          (fst (lookup zero (w ∷ t ∷ z ∷ γ)))
                zt' = transport (cong fst (prAtL-adequate (suc (suc zero)) (suc zero) zero
                      (w ∷ t ∷ z ∷ γ))) zt
                wb' : fst (lookup zero (w ∷ t ∷ z ∷ γ))
                     ≡ pr (fst (lookup (suc (suc (suc (suc (suc zero))))) (w ∷ t ∷ z ∷ γ)))
                          (fst (lookup (suc (suc (suc (suc zero)))) (w ∷ t ∷ z ∷ γ)))
                wb' = transport (cong fst (prAtL-adequate zero (suc (suc (suc (suc (suc zero)))))
                      (suc (suc (suc (suc zero)))) (w ∷ t ∷ z ∷ γ))) wb
                tt' : fst (lookup (suc zero) (w ∷ t ∷ z ∷ γ))
                    ≡ fst (lookup (suc (suc (suc (suc (suc tag))))) γ)
                tt' = tt
            in p' ∙ cong (pr ar₀) (zt' ∙ cong (pr (fst (lookup (suc zero) (w ∷ t ∷ z ∷ γ)))) wb')
                 ∙ cong (λ v → pr ar₀ (pr v (pr a₀ b₀)))
                        (tt' ∙ te ∙ numeralL-fst k) })
          kt })
        kz })
      h

  in' : tagEq → numK → innerK → pairK
      → ⟨ fst (lookup (suc (suc zero)) γ) ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩
      → ⟨ fst (lookup (suc zero) γ) ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩
      → ⟨ γ ⊨ arityTagPairAtL (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) k
                               (suc (suc zero)) (suc zero) ⟩
      → ⟨ γ ⊨ arTagPairB tag K ⟩
  in' te nk ik pk a₀K b₀K h = PT.rec squash₁
    (λ { (z , (p , tz)) →
      let a₀ : S
          a₀ = lookup (suc (suc zero)) γ
          b₀ : S
          b₀ = lookup (suc zero) γ
          tz' : fst (lookup zero (z ∷ γ))
               ≡ pr (# k) (pr (fst (lookup (suc (suc (suc zero))) (z ∷ γ)))
                              (fst (lookup (suc (suc zero)) (z ∷ γ))))
          tz' = transport (cong fst (tagPairAtL-adequate zero k (suc (suc (suc zero))) (suc (suc zero)) (z ∷ γ))) tz
          zK : ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩
          zK = subst (λ w → ⟨ w ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩)
                 (sym tz')
                 (subst (λ w → ⟨ w ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩)
                   (prʟ-fst (numeralL k) (prʟ a₀ b₀)
                    ∙ cong₂ pr (numeralL-fst k) (prʟ-fst a₀ b₀))
                   (ik a₀ b₀ a₀K b₀K))
          zt : ⟨ (prʟ a₀ b₀ ∷ numeralL k ∷ z ∷ γ)
                  ⊨ prAtL (suc (suc zero)) (suc zero) zero ⟩
          zt = transport (cong fst (sym (prAtL-adequate (suc (suc zero)) (suc zero) zero
                 (prʟ a₀ b₀ ∷ numeralL k ∷ z ∷ γ))))
               (tz' ∙ cong₂ pr (sym (numeralL-fst k))
                    (sym (prʟ-fst a₀ b₀)))
          wb : ⟨ (prʟ a₀ b₀ ∷ numeralL k ∷ z ∷ γ)
                  ⊨ prAtL zero (suc (suc (suc (suc (suc zero)))))
                            (suc (suc (suc (suc zero)))) ⟩
          wb = transport (cong fst (sym (prAtL-adequate zero (suc (suc (suc (suc (suc zero)))))
                 (suc (suc (suc (suc zero))))
                 (prʟ a₀ b₀ ∷ numeralL k ∷ z ∷ γ))))
               (prʟ-fst a₀ b₀)
      in ∣ z , ( zK
               , ( p
                 , ∣ numeralL k
                   , ( nk
                     , ( sym te
                       , ∣ prʟ a₀ b₀
                         , ( pk a₀ b₀ a₀K b₀K
                           , ( zt , wb ) )
                         ∣₁ ) )
                   ∣₁ ) ) ∣₁ })
    h

-- =====================================================================
-- THE MEM ROW WITH GUARDED CLOSURE FACTS.
-- A copy of the master's MemAgree
-- (src/L/Condensation.lagda.md:4117-4210) with innerK and pairK
-- guarded, and back passing the aK bK witnesses from codesK into the
-- guarded BinaryShape'.in'.
-- =====================================================================
module MemAgree' {m : ℕ} (C T B N K t0 t1 : Fin m) (γ : S ^ m)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL 0))
  (numK : ⟨ fst (numeralL 0) ∈ fst (lookup K γ) ⟩)
  -- GUARDED: the closure needs both components already in K.
  (innerK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
             → ⟨ fst b ∈ fst (lookup K γ) ⟩
             → ⟨ fst (prʟ (numeralL 0) (prʟ a b)) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
           → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a b : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 0) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ⟨ fst b ∈ fst (lookup K γ) ⟩)
  (valK : (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 0) (pr (fst a) (fst b)))
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
  (t0eq : fst (lookup t0 γ) ≡ fst (numeralL 0))
  (t1eq : fst (lookup t1 γ) ≡ fst (numeralL 1))
  (t0K : ⟨ fst (lookup t0 γ) ∈ fst (lookup K γ) ⟩)
  (tmKeyK : (k : S) → ⟨ fst k ∈ fst (lookup K γ) ⟩)
  (num1K : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩)
  (envK : (yc b a ar c E : S) → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B)))))) ⟩
         → ⟨ fst E ∈ fst (lookup K γ) ⟩)
  (entryK : (z x y : S) → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
           → ⟨ fst x ∈ fst (lookup K γ) ⟩ × ⟨ fst y ∈ fst (lookup K γ) ⟩)
  (arSubK : (yc b a ar c x : S) → ⟨ fst x ∈ fst (lookup (suc (suc (suc zero)))
                                       (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩
           → ⟨ fst x ∈ fst (lookup K γ) ⟩)
  (envInK : (yc b a ar c E z : S) → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
           → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  (valV : (E yc b a ar c z v w : S) → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                     (suc (suc zero))
                     (suc zero) ⟩
         → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc K)))))))
                           (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (valW : (E yc b a ar c z v w : S) → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             tmValAt (suc (suc (suc (suc (suc zero)))))
                     (suc (suc zero))
                     zero ⟩
         → ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                           (v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  where
  private
    φB : Formula S m
    φB = Mem.memBndAt C T B N K t0 t1

    cmp : Formula S (9 + m)
    cmp = var (suc zero) ∈̇ var zero

  out : ⟨ γ ⊨ memClauseAt C T B ⟩ → ⟨ γ ⊨ φB ⟩
  out h = λ c c∈ ar arK a aK b bK yc ycK shB hc E EK henv →
    let shD = BinaryShape'.out {m} N K 0 (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
                tagEq shB
        module E' = EnvSet {6 + m} zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B))))))
                       (suc (suc (suc (suc (suc (suc K))))))
                       (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) entryK (arSubK yc b a ar c)
                       (envInK yc b a ar c E)
        hE' = E'.out henv
        hbM = h c c∈ ar a b yc shD hc E hE'
        module L = AtomLeaf E yc b a ar c γ t0 t1 K
                     t0eq t1eq t0K tmKeyK num1K (valV E yc b a ar c) (valW E yc b a ar c) cmp
    in extAt→extAtB (suc zero) (suc (suc (suc (suc (suc (suc K))))))
         L.bodyS L.bodyM (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) L.fwd L.bwd hbM

  back : ⟨ γ ⊨ φB ⟩ → ⟨ γ ⊨ memClauseAt C T B ⟩
  back h = λ c c∈ ar a b yc shD hc E hE →
    let shEq = transport (cong fst (arityTagPairAtL-adequate (suc (suc (suc (suc zero))))
                   (suc (suc (suc zero))) 0 (suc (suc zero)) (suc zero)
                   (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))) shD
        (arK , (aK , bK)) = codesK c ar a b c∈ shEq
        ycK = valK c ar a b yc c∈ shEq
        shB = BinaryShape'.in' {m} N K 0 (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
                tagEq numK innerK pairK aK bK shD
        EK = envK yc b a ar c E hE
        module E' = EnvSet {6 + m} zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B))))))
                       (suc (suc (suc (suc (suc (suc K))))))
                       (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) entryK (arSubK yc b a ar c)
                       (envInK yc b a ar c E)
        henv = E'.back hE
        module L = AtomLeaf E yc b a ar c γ t0 t1 K
                     t0eq t1eq t0K tmKeyK num1K (valV E yc b a ar c) (valW E yc b a ar c) cmp
        hb = h c c∈ ar arK a aK b bK yc ycK shB hc E EK henv
    in extAtB→extAt (suc zero) (suc (suc (suc (suc (suc (suc K))))))
         L.bodyS L.bodyM (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) L.fwd L.bwd
         (λ z hz → E'.memE-bnd henv z (hz .fst)) hb

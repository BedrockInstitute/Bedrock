{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.53] probe A: WALL 2, THE PARAMETER-TO-CODE RELABELLING.
--
-- The two halves of the TV/ElemDown instance at every arity:
--   1. the canonical-code relabelling f : SM -> Code with
--      val (f q) = fst q (the delivered CodeSelect least-of pattern;
--      here a module hypothesis, its instantiation is in Co),
--   2. the satisfaction transfer between the parameter-in-env and the
--      parameter-as-constant spellings: the generic `closeAt` operation
--      and its adequacy.
-- The TarskiVaught instance assembles from hull-closed through the two
-- halves, and AtM.TV-thm turns it into Elementary (hence ElemDown).
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ153A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure; _↾_ )
open import FOL.Syntax using
  ( Term; con; var; Formula
  ; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Semantics
open import FOL.Manipulation.Renaming using ( renameTm )
open import FOL.Manipulation.Relabelling using ( mapTm; mapFo; mapFo-comp )
open import FOL.Manipulation.Parameters using ( lookup-map )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; leastOf; IsLeast )
open import V.Presentation {ℓ} using ( member )
open import Cubical.Functions.Embedding using ( Embedding-into-isSet→isSet )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( isL; isL-trans; IsOrd; Lset )
open import L.Hull {ℓ} lem using ( module AtStage )

open hPropStructure 𝒮ᵥ

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.Data.Vec using ( Vec; lookup; map; _∷_; []; _++_ )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.Prelude using ( funExt; transport )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅ )

-- =====================================================================
-- THE CANONICAL CODE (wall 2, first half; the delivered CodeSelect
-- least-of pattern).  The least count index of the codes of a hull
-- member is a propositional fibre (cnt-inj), so the code extraction is
-- a truncation elimination into a proposition.
-- =====================================================================
module CanonCode (α : S) (oα : IsOrd α) (w : SWO {ℓ} ⟪ α ⟫)
  (M : S) (Code : Type ℓ) (val : Code → S)
  (mem-code : (x : S) → ⟨ x ∈ˢ M ⟩ → ∥ Σ[ c ∈ Code ] (val c ≡ x) ∥₁)
  (cnt : Code → ⟪ α ⟫) (cnt-inj : (c d : Code) → cnt c ≡ cnt d → c ≡ d) where

  cls : ⟪ M ⟫ → ⟪ α ⟫ → hProp (ℓ-suc ℓ)
  cls m y = ( ∥ Σ[ c ∈ Code ] ((val c ≡ ⟪ M ⟫↪ m) × (cnt c ≡ y)) ∥₁
            , squash₁ )

  nonempty : (m : ⟪ M ⟫) → ∥ Σ[ y ∈ ⟪ α ⟫ ] ⟨ cls m y ⟩ ∥₁
  nonempty m = PT.map (λ { (c , e) → cnt c , ∣ c , (e , refl) ∣₁ })
                      (mem-code (⟪ M ⟫↪ m) (member M m))

  isSet⟪α⟫ : isSet ⟪ α ⟫
  isSet⟪α⟫ = Embedding-into-isSet→isSet (⟪ α ⟫↪ , isEmb⟪ α ⟫↪) isSetS

  least : (m : ⟪ M ⟫) → ⟪ α ⟫
  least m = fst (leastOf w {ℓ'' = ℓ-suc ℓ} lem (cls m) (nonempty m))

  least-wit : (m : ⟪ M ⟫)
            → ∥ Σ[ c ∈ Code ] ((val c ≡ ⟪ M ⟫↪ m) × (cnt c ≡ least m)) ∥₁
  least-wit m = fst (snd (leastOf w {ℓ'' = ℓ-suc ℓ} lem (cls m) (nonempty m)))

  isPropFib : (m : ⟪ M ⟫)
            → isProp (Σ[ c ∈ Code ] ((val c ≡ ⟪ M ⟫↪ m)
                                   × (cnt c ≡ least m)))
  isPropFib m (c , e , p) (d , e' , p') =
    Σ≡Prop (λ c → isProp× (isSetS (val c) (⟪ M ⟫↪ m))
                            (isSet⟪α⟫ (cnt c) (least m)))
      (cnt-inj c d (p ∙ sym p'))

  canonical : ⟪ M ⟫ → Code
  canonical m = fst (PT.rec (isPropFib m) (λ w → w) (least-wit m))

  canonical-spec : (m : ⟪ M ⟫) → val (canonical m) ≡ ⟪ M ⟫↪ m
  canonical-spec m = fst (snd (PT.rec (isPropFib m) (λ w → w) (least-wit m)))

-- =====================================================================
-- THE GENERIC CLOSE OPERATION (syntax).  A formula of arity d + n has
-- its top n variables replaced by the constants δ: the
-- parameter-as-constant spelling.  The first d variables (the binders
-- already crossed) stay variables.  Both consumers are one recursion:
-- close keeps the witness variable free (d = 1), closeAll closes every
-- top variable (d = 0).
-- =====================================================================
module CloseSyntax where

  closeTmAt : {K : Type (ℓ-suc ℓ)} (d n : ℕ) (δ : Vec K n)
            → Term K (d + n) → Term K d
  closeTmAt d n δ (con c) = con c
  closeTmAt zero zero δ (var ())
  closeTmAt zero (suc n) δ (var zero) = con (lookup zero δ)
  closeTmAt zero (suc n) δ (var (suc i)) = con (lookup (suc i) δ)
  closeTmAt (suc d) n δ (var zero) = var zero
  closeTmAt (suc d) n δ (var (suc j)) =
    renameTm suc (closeTmAt d n δ (var j))

  closeAt : {K : Type (ℓ-suc ℓ)} (d n : ℕ) (δ : Vec K n)
          → Formula K (d + n) → Formula K d
  closeAt d n δ (t ∈̇ u) = closeTmAt d n δ t ∈̇ closeTmAt d n δ u
  closeAt d n δ (t ≐ u) = closeTmAt d n δ t ≐ closeTmAt d n δ u
  closeAt d n δ (φ ∧̇ ψ) = closeAt d n δ φ ∧̇ closeAt d n δ ψ
  closeAt d n δ (φ ∨̇ ψ) = closeAt d n δ φ ∨̇ closeAt d n δ ψ
  closeAt d n δ (φ ⇒̇ ψ) = closeAt d n δ φ ⇒̇ closeAt d n δ ψ
  closeAt d n δ (¬̇ φ) = ¬̇ closeAt d n δ φ
  closeAt d n δ ⊤̇ = ⊤̇
  closeAt d n δ ⊥̇ = ⊥̇
  closeAt d n δ (∃̇ ψ) = ∃̇ (closeAt (suc d) n δ ψ)
  closeAt d n δ (∀̇ ψ) = ∀̇ (closeAt (suc d) n δ ψ)
  closeAt d n δ (∀̇∈ t ψ) = ∀̇∈ (closeTmAt d n δ t) (closeAt (suc d) n δ ψ)
  closeAt d n δ (∃̇∈ t ψ) = ∃̇∈ (closeTmAt d n δ t) (closeAt (suc d) n δ ψ)

  -- the closure of the parameter block and the witness variable
  close : {K : Type (ℓ-suc ℓ)} (n : ℕ) (δ : Vec K n)
        → (φ : Formula K (suc n)) → Formula K 1
  close n δ φ = closeAt 1 n δ φ

  -- the full closure (no witness variable left)
  closeAll : {K : Type (ℓ-suc ℓ)} (n : ℕ) (δ : Vec K n)
           → (φ : Formula K n) → Formula K 0
  closeAll n δ φ = closeAt 0 n δ φ

  -- relabelling and closure commute: closing after relabelling is
  -- relabelling after closing
  mapTm-rename : {K K' : Type (ℓ-suc ℓ)} {n m : ℕ} (g : K → K')
               → (ρ : Fin n → Fin m) (t : Term K n)
               → mapTm g (renameTm ρ t) ≡ renameTm ρ (mapTm g t)
  mapTm-rename g ρ (con c) = refl
  mapTm-rename g ρ (var j) = refl

  mapTm-close : {K K' : Type (ℓ-suc ℓ)} (d n : ℕ) (δ : Vec K n)
              → (g : K → K') (t : Term K (d + n))
              → mapTm g (closeTmAt d n δ t)
                ≡ closeTmAt d n (map g δ) (mapTm g t)
  mapTm-close d n δ g (con c) = refl
  mapTm-close zero zero δ g (var ())
  mapTm-close zero (suc n) δ g (var zero) =
    cong con (sym (lookup-map g δ zero))
  mapTm-close zero (suc n) δ g (var (suc i)) =
    cong con (sym (lookup-map g δ (suc i)))
  mapTm-close (suc d) n δ g (var zero) = refl
  mapTm-close (suc d) n δ g (var (suc j)) =
    mapTm-rename g suc (closeTmAt d n δ (var j))
    ∙ cong (renameTm suc) (mapTm-close d n δ g (var j))

  mapFo-close : {K K' : Type (ℓ-suc ℓ)} (d n : ℕ) (δ : Vec K n)
              → (g : K → K') (φ : Formula K (d + n))
              → mapFo g (closeAt d n δ φ)
                ≡ closeAt d n (map g δ) (mapFo g φ)
  mapFo-close d n δ g (t ∈̇ u) = cong₂ _∈̇_
    (mapTm-close d n δ g t) (mapTm-close d n δ g u)
  mapFo-close d n δ g (t ≐ u) = cong₂ _≐_
    (mapTm-close d n δ g t) (mapTm-close d n δ g u)
  mapFo-close d n δ g (φ ∧̇ ψ) = cong₂ _∧̇_
    (mapFo-close d n δ g φ) (mapFo-close d n δ g ψ)
  mapFo-close d n δ g (φ ∨̇ ψ) = cong₂ _∨̇_
    (mapFo-close d n δ g φ) (mapFo-close d n δ g ψ)
  mapFo-close d n δ g (φ ⇒̇ ψ) = cong₂ _⇒̇_
    (mapFo-close d n δ g φ) (mapFo-close d n δ g ψ)
  mapFo-close d n δ g (¬̇ φ) = cong ¬̇_ (mapFo-close d n δ g φ)
  mapFo-close d n δ g ⊤̇ = refl
  mapFo-close d n δ g ⊥̇ = refl
  mapFo-close d n δ g (∃̇ ψ) = cong ∃̇_ (mapFo-close (suc d) n δ g ψ)
  mapFo-close d n δ g (∀̇ ψ) = cong ∀̇_ (mapFo-close (suc d) n δ g ψ)
  mapFo-close d n δ g (∀̇∈ t ψ) = cong₂ ∀̇∈
    (mapTm-close d n δ g t) (mapFo-close (suc d) n δ g ψ)
  mapFo-close d n δ g (∃̇∈ t ψ) = cong₂ ∃̇∈
    (mapTm-close d n δ g t) (mapFo-close (suc d) n δ g ψ)

-- =====================================================================
-- THE ADEQUACY OF THE CLOSE OPERATION (semantics).  The original
-- formula at the environment γ ++ map ι δ is the closed formula at γ.
-- =====================================================================
module CloseSem {𝒮 : ZFStructure (hPropAlgebra (ℓ-suc ℓ))}
                {K : Type (ℓ-suc ℓ)} (ι : K → ZFStructure.S 𝒮) where

  open ZFStructure 𝒮 renaming ( _∈ˢ_ to _∈ˢ𝒮_ ; _≈ˢ_ to _≈ˢ𝒮_ )
  open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
  module Sem = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮
  open Sem using ( _^_ )
  open Sem.At K ι using ( _⊨_; ⟦_⟧ )
  module Cl = CloseSyntax

  map-id : {ℓ'' : Level} {A : Type ℓ''} {n : ℕ} (v : Vec A n)
         → map (λ x → x) v ≡ v
  map-id [] = refl
  map-id (x ∷ v) = cong (x ∷_) (map-id v)

  -- a term lifted past a binder reads the tail of the environment
  renameTm-suc-sat : {d : ℕ} (X : Term K d) (y : ZFStructure.S 𝒮) (γ : ZFStructure.S 𝒮 ^ d)
                   → ⟦ renameTm suc X ⟧ (y ∷ γ) ≡ ⟦ X ⟧ γ
  renameTm-suc-sat (con c) y γ = refl
  renameTm-suc-sat (var i) y γ = refl

  -- the term-level adequacy: every clause is lookup-map or the
  -- induction hypothesis, and the kept variables are refl
  ⟦⟧-close : (d n : ℕ) (t : Term K (d + n)) (δ : Vec K n) (γ : ZFStructure.S 𝒮 ^ d)
           → ⟦ t ⟧ (γ ++ map ι δ) ≡ ⟦ Cl.closeTmAt d n δ t ⟧ γ
  ⟦⟧-close d n (con c) δ γ = refl
  ⟦⟧-close zero zero (var ()) δ γ
  ⟦⟧-close zero (suc n) (var zero) δ [] = lookup-map ι δ zero
  ⟦⟧-close zero (suc n) (var (suc i)) δ [] = lookup-map ι δ (suc i)
  ⟦⟧-close (suc d) n (var zero) δ (y ∷ γ) = refl
  ⟦⟧-close (suc d) n (var (suc j)) δ (y ∷ γ) =
    ⟦⟧-close d n (var j) δ γ
    ∙ sym (renameTm-suc-sat (Cl.closeTmAt d n δ (var j)) y γ)

  -- the formula-level adequacy: the fourteen clauses of the semantics,
  -- each a congruence, the binders pushing a value onto the env
  ⊨-close : (d n : ℕ) (φ : Formula K (d + n)) (δ : Vec K n) (γ : ZFStructure.S 𝒮 ^ d)
          → (γ ++ map ι δ) ⊨ φ ≡ γ ⊨ Cl.closeAt d n δ φ
  ⊨-close d n (t ∈̇ u) δ γ = cong₂ _∈ˢ𝒮_
    (⟦⟧-close d n t δ γ) (⟦⟧-close d n u δ γ)
  ⊨-close d n (t ≐ u) δ γ = cong₂ _≈ˢ𝒮_
    (⟦⟧-close d n t δ γ) (⟦⟧-close d n u δ γ)
  ⊨-close d n (φ ∧̇ ψ) δ γ = cong₂ _⊓_
    (⊨-close d n φ δ γ) (⊨-close d n ψ δ γ)
  ⊨-close d n (φ ∨̇ ψ) δ γ = cong₂ _⊔_
    (⊨-close d n φ δ γ) (⊨-close d n ψ δ γ)
  ⊨-close d n (φ ⇒̇ ψ) δ γ = cong₂ _⇒_
    (⊨-close d n φ δ γ) (⊨-close d n ψ δ γ)
  ⊨-close d n (¬̇ φ) δ γ = cong ¬_ (⊨-close d n φ δ γ)
  ⊨-close d n ⊤̇ δ γ = refl
  ⊨-close d n ⊥̇ δ γ = refl
  ⊨-close d n (∃̇ ψ) δ γ = cong (⋁ (ZFStructure.S 𝒮)) (funExt (λ x →
    ⊨-close (suc d) n ψ δ (x ∷ γ)))
  ⊨-close d n (∀̇ ψ) δ γ = cong (⋀ (ZFStructure.S 𝒮)) (funExt (λ x →
    ⊨-close (suc d) n ψ δ (x ∷ γ)))
  ⊨-close d n (∀̇∈ t ψ) δ γ = cong (⋀ (ZFStructure.S 𝒮)) (funExt (λ x →
    cong₂ _⇒_ (cong (x ∈ˢ𝒮_) (⟦⟧-close d n t δ γ))
      (⊨-close (suc d) n ψ δ (x ∷ γ))))
  ⊨-close d n (∃̇∈ t ψ) δ γ = cong (⋁ (ZFStructure.S 𝒮)) (funExt (λ x →
    cong₂ _⊓_ (cong (x ∈ˢ𝒮_) (⟦⟧-close d n t δ γ))
      (⊨-close (suc d) n ψ δ (x ∷ γ))))

  ⊨-close₁ : (n : ℕ) (φ : Formula K (suc n)) (δ : Vec K n) (x : ZFStructure.S 𝒮)
           → (x ∷ map ι δ) ⊨ φ ≡ (x ∷ []) ⊨ Cl.close n δ φ
  ⊨-close₁ n φ δ x = ⊨-close 1 n φ δ (x ∷ [])

  ⊨-closeAll : (n : ℕ) (φ : Formula K n) (δ : Vec K n)
             → map ι δ ⊨ φ ≡ [] ⊨ Cl.closeAll n δ φ
  ⊨-closeAll n φ δ = ⊨-close 0 n φ δ []

-- =====================================================================
-- THE HULL INSTANCE.  f is the canonical code of each hull member
-- (the delivered CodeSelect least-of pattern, instantiated in Co); the
-- probe states it as a hypothesis and proves the relabelling transfer,
-- the TarskiVaught instance at every arity, and ElemDown.
-- =====================================================================
module HullElemDown (α : S) (ordα : IsOrd α)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset α ⟩) (∅∈α : ⟨ ∅ ∈ˢ α ⟩) where

  module ASt = AtStage α ordα
  module H = ASt.Hull X X⊆L ∅∈α
  M : S
  M = H.T.Hull
  module A = ASt.AtM M H.Hull⊆L
  module Mse = A.SemM.At A.SM id
  open Mse renaming ( _⊨_ to _⊨ᴹ_ )

  module Cl = CloseSyntax
  module C = CloseSem {𝒮 = 𝒮ᵥ ↾ (λ x → x ∈ˢ M)} {K = A.SM} id
  module CS = CloseSem {𝒮 = 𝒮ᵥ ↾ (λ x → x ∈ˢ Lset α)} {K = ASt.SL} id

  module _ (f : A.SM → H.T.Code)
    (f-spec : (q : A.SM) → fst (H.T.val (f q)) ≡ fst q) where

    -- val ∘ f and inL agree pointwise, so the relabelling preserves the
    -- formula up to the interpretation
    val∘f≡inL : (q : A.SM) → H.T.val (f q) ≡ A.inL q
    val∘f≡inL q = Σ≡Prop (λ z → (z ∈ˢ Lset α) .snd) (f-spec q)

    rel : {n : ℕ} (φ : Formula A.SM n)
        → mapFo H.T.val (mapFo f φ) ≡ mapFo A.inL φ
    rel {n} φ =
      mapFo-comp f H.T.val φ
      ∙ cong (λ g → mapFo g φ) (funExt val∘f≡inL)

    -- TarskiVaught at every arity: the stage existential at the closed
    -- parameters is hull-closed, and the code formula reads back
    -- through the relabelling and the close transfer
    tv : (n : ℕ) (ψ : Formula A.SM (suc n)) (δ : Vec A.SM n)
       → ⟨ map A.inL δ ASt.AbsL.⊨ᵐ (mapFo A.inL (∃̇ ψ)) ⟩
       → ∥ Σ[ q ∈ A.SM ]
            ⟨ (A.inL q ∷ map A.inL δ) ASt.AbsL.⊨ᵐ (mapFo A.inL ψ) ⟩ ∥₁
    tv n ψ δ h = PT.rec squash₁ go (H.hull-closed ψ' h')
      where
      ψ' : Formula H.T.Code 1
      ψ' = mapFo f (Cl.close n δ ψ)

      h' : ⟨ [] ASt.AbsL.⊨ᵐ (∃̇ (mapFo H.T.val ψ')) ⟩
      h' = subst (λ ψ → ⟨ [] ASt.AbsL.⊨ᵐ ψ ⟩) p
        (subst ⟨_⟩ (CS.⊨-closeAll n (mapFo A.inL (∃̇ ψ)) (map A.inL δ)) h₁)
        where
        h₁ : fst (map (λ x → x) (map A.inL δ) ASt.AbsL.⊨ᵐ
                (mapFo A.inL (∃̇ ψ)))
        h₁ = subst (λ e → fst (e ASt.AbsL.⊨ᵐ (mapFo A.inL (∃̇ ψ))))
               (sym (CS.map-id (map A.inL δ))) h
        p1 : CS.Cl.closeAll n (map A.inL δ) (mapFo A.inL (∃̇ ψ))
           ≡ FOL.Syntax.∃̇_ (mapFo A.inL (Cl.close n δ ψ))
        p1 = cong FOL.Syntax.∃̇_
               (sym (Cl.mapFo-close 1 n δ A.inL ψ))
        p : CS.Cl.closeAll n (map A.inL δ) (mapFo A.inL (∃̇ ψ))
          ≡ FOL.Syntax.∃̇_ (mapFo H.T.val ψ')
        p = p1 ∙ cong FOL.Syntax.∃̇_ (sym (rel (Cl.close n δ ψ)))

      go : Σ[ a ∈ ASt.SL ] (⟨ fst a ∈ˢ M ⟩
                          × ⟨ (a ∷ []) ASt.AbsL.⊨ᵐ (mapFo H.T.val ψ') ⟩)
         → ∥ Σ[ q ∈ A.SM ]
              ⟨ (A.inL q ∷ map A.inL δ) ASt.AbsL.⊨ᵐ (mapFo A.inL ψ) ⟩ ∥₁
      go (a , a∈H , hsat) = PT.rec squash₁ go₂ (H.hull-member (fst a) a∈H)
        where
        go₂ : Σ[ c ∈ H.T.Code ] (fst (H.T.val c) ≡ fst a)
            → ∥ Σ[ q ∈ A.SM ]
                 ⟨ (A.inL q ∷ map A.inL δ) ASt.AbsL.⊨ᵐ (mapFo A.inL ψ) ⟩ ∥₁
        go₂ (c , e) = ∣ q , sat ∣₁
          where
          q : A.SM
          q = fst (H.T.val c) , H.val-in-Hull c
          q≡a : A.inL q ≡ a
          q≡a = Σ≡Prop (λ z → (z ∈ˢ Lset α) .snd) e
          sat : ⟨ (A.inL q ∷ map A.inL δ) ASt.AbsL.⊨ᵐ (mapFo A.inL ψ) ⟩
          sat = subst (λ e' → ⟨ (A.inL q ∷ e') ASt.AbsL.⊨ᵐ (mapFo A.inL ψ) ⟩)
                  (CS.map-id (map A.inL δ))
                  (subst ⟨_⟩
                    (sym (CS.⊨-close₁ n (mapFo A.inL ψ) (map A.inL δ) (A.inL q)))
                    sat₁)
            where
            sat₁ : ⟨ (A.inL q ∷ []) ASt.AbsL.⊨ᵐ
                       (CS.Cl.close n (map A.inL δ) (mapFo A.inL ψ)) ⟩
            sat₁ = subst (λ ψ → ⟨ (A.inL q ∷ []) ASt.AbsL.⊨ᵐ ψ ⟩)
                     (sym q-path) sat₂
              where
              q-path : CS.Cl.close n (map A.inL δ) (mapFo A.inL ψ)
                     ≡ mapFo H.T.val ψ'
              q-path = sym (Cl.mapFo-close 1 n δ A.inL ψ)
                       ∙ sym (rel (Cl.close n δ ψ))
              sat₂ : ⟨ (A.inL q ∷ []) ASt.AbsL.⊨ᵐ (mapFo H.T.val ψ') ⟩
              sat₂ = subst (λ z → ⟨ (z ∷ []) ASt.AbsL.⊨ᵐ (mapFo H.T.val ψ') ⟩)
                       (sym q≡a)
                       hsat

    elem : A.Elementary
    elem = A.TV-thm .snd tv

    elem-down : (n : ℕ) (φ : Formula A.SM n) (δ : Vec A.SM n)
              → ⟨ map A.inL δ ASt.AbsL.⊨ᵐ (mapFo A.inL φ) ⟩
              → fst (Mse._⊨_ δ φ)
    elem-down n φ δ h = subst ⟨_⟩ (sym (elem n φ δ)) h

# The six rows of the definable-powerset body, at the code set and the uniform table

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.Rows {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; Term; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.Relabelling using ( mapFo; mapTm; mapTm-comp )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′; #mono; module VCode )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ-inv )
open import L.Ordinal {ℓ} using ( ∈#-elim )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ} using
  ( prʟ; prʟ-fst; prAtL; prAtL-adequate; appAt; appAt-adequate; sucAtL; sucAtL-adequate
  ; closedAt; binSameClosed-in; unSameClosed-in; unSuccClosed-in; binSuccClosed-in
  ; tagAtL; tagAtL-adequate; numL; module LCode; codeBridgeTm
  ; andClauseAt; orClauseAt; propClause-in; interAt; unionAt; envSetAt; envOverAt
  ; negClauseAt; negClause-in; impClauseAt; impClause-in
  ; topClauseAt; topClause-in; botClauseAt; botClause-in
  ; tmValAt; memClauseAt; eqClauseAt; memRel; eqRel; atomClause-in
  ; existClauseAt; forallClauseAt; quantClause-in
  ; allInClauseAt; exInClauseAt; bndClause-in
  ; bodyAll; bodyAll-in; bodyAll-out; bodyEx; bodyEx-in; bodyEx-out
  ; body∃; body∃-in; body∃-out; body∀; body∀-in; body∀-out
  ; consAtL-transport; consAtL; consAtL-adequate
  ; atomBody; atomBody-in; atomBody-out
  ; extAt-out; extAt-in; extAt-in-both
  ; subValAt; subValAt-adequate; subValSuccAt; subValSuccAt-adequate
  ; arityTagAtL-adequate; arityTagPairAtL-adequate
  ; yc7; ya7; yb7 )
open import L.Coding.Sound {ℓ} lem using ( module Ambient; termAgree )
open import L.Coding.Shape {ℓ} using
  ( shapedAt; shaped-in; ShapeWit; isTmAt; isTmAt-in; TmWit )
open import L.Coding.InL {ℓ} using ( codeL; codeTmL )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes; AllCodes-out; key∈AllCodes; keyS )
open import L.Coding.Powerset {ℓ} lem using ( DefinesAt; DefinesAt-both; envOne )
open import L.Coding.Bridge {ℓ} lem using ( asConst; defSet-Sat )
open import L.Coding.Sat {ℓ} lem using
  ( Sat; Sat-mem; cond∈-in; cond∈-out; cond≐-in; cond≐-out
  ; cond∃-in; cond∃-out; cond∀-in; cond∀-out
  ; cond∀∈-in; cond∀∈-out; cond∃∈-in; cond∃∈-out )
open import L.Coding.Uniform {ℓ} lem using ( module Table; val-at )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Condensation {ℓ} lem using
  ( module KFactsNS; module ClosedAgree; module ShapedAgree; module DefinesAgree
  ; closedBS; shapedBS; keyArBS; DefinesBS; tagBS
  ; module EnvSet; module BinaryShape; module UnaryShape; module SubValSuccB2T
  ; extAt→extAtB; interB; unionB; subValB; arTagPairB
  ; module Mem; module Eq; module And; module Or; module Imp; module Neg
  ; module Top; module Bot; module Exist; module Forall; module AllIn; module ExIn
  ; module BotAgree; module TopAgree; module NegAgree; module ImpAgree )
open import L.GCH.Level {ℓ} lem using
  ( KC; module KC; Tags; tagsCons; down; app-in; app-out; pr-out; suc-out
  ; i0; i1; i2; i3; i4; i5; i6; sh1; sh2; sh3; sh4; sh5; sh6; sh7; sh8
  ; tmAt; module Close; memAt; allAt; twelveAt; towerAt; module Tower )
open import L.GCH.LevelRows {ℓ} lem using
  ( module Chain; module AtomLeaf′; module BndLeaf′; module ExistAgree′ )

open import Cubical.Data.Vec using ( _∷_; []; lookup )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Nat.Order using ( _<_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( tt* )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Empty using ( isProp⊥ )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.FinData.Properties using ( fromℕ'; toFromId'; toℕ<n )
open import Cubical.Foundations.Prelude using ( cong₂; subst2; J; substRefl )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- The class-carrier reading, as src/L/GCH/Complete.lagda.md:77-78.
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- The 𝒮ʟ carrier, for the syntax.  Same name as src/L/GCH/Level.lagda.md.
module CS = hPropStructure 𝒮ʟ
```

```agda
-- =====================================================================
-- SECTION 1.  THE CODE SET, READ BY SHAPE.  A member of `AllCodes A`
-- is the key of a formula over the alphabet ⟪ fst A ⟫
-- (src/L/Coding/CodeSet.lagda.md `AllCodes-out`); its outer pair is
-- the arity numeral, its inner pair the tag numeral and the payload
-- (src/FOL/Coding.lagda.md `shape`).  `decode` reads a member handed
-- over as a tagged pair back into the constructor the tag names, at
-- the alphabet: the mirror of src/L/Coding/Table.lagda.md `keyʟ-shape`
-- one alphabet up, so that the parts come back as formulas over
-- ⟪ fst A ⟫ and their keys are members again.
-- =====================================================================

module Codes (A : CS.S) where

  Ab : Type ℓ
  Ab = ⟪ fst A ⟫

  ι : Ab → V ℓ
  ι = ⟪ fst A ⟫↪

  ι∈ : (q : Ab) → ⟨ ι q ∈ fst A ⟩
  ι∈ q = ∈∈ₛ {a = ι q} {b = fst A} .snd (∈ₛ⟪ fst A ⟫↪ q)

  ιL : (q : Ab) → ⟨ isL (ι q) ⟩
  ιL q = isL-trans {x = fst A} {y = ι q} (ι∈ q) (snd A)

  -- The code of a formula, and of a term, in the hierarchy's coding.
  cd : ∀ {n} → Formula Ab n → V ℓ
  cd ψ = VCode.⌜ mapFo ι ψ ⌝

  cdS : ∀ {n} → Formula Ab n → CS.S
  cdS ψ = cd ψ , codeL ι ιL ψ

  ct : ∀ {n} → Term Ab n → V ℓ
  ct t = VCode.⌜ mapTm ι t ⌝ᵗ

  ctS : ∀ {n} → Term Ab n → CS.S
  ctS t = ct t , codeTmL ι ιL t

  nn : ℕ → CS.S
  nn k = # k , numL k

  -- The key is the arity numeral paired with the code, by definition.
  key-fst : ∀ {n} (ψ : Formula Ab n) → fst (keyS A ψ) ≡ pr (# n) (cd ψ)
  key-fst ψ = refl

  keyC : ∀ {n} (ψ : Formula Ab n) (x : V ℓ) → x ≡ pr (# n) (cd ψ)
       → ⟨ x ∈ fst (AllCodes A) ⟩
  keyC ψ x e = subst (λ u → ⟨ u ∈ fst (AllCodes A) ⟩) (sym e) (key∈AllCodes A ψ)

  -- THE MATCH AT THE ALPHABET, the twelve tags read as constructors.
  MatchA : ∀ {n} → ℕ → Formula Ab n → Type ℓ
  MatchA {n} 0  φ = Σ[ t ∈ Term Ab n ] (Σ[ u ∈ Term Ab n ] (φ ≡ (t ∈̇ u)))
  MatchA {n} 1  φ = Σ[ t ∈ Term Ab n ] (Σ[ u ∈ Term Ab n ] (φ ≡ (t ≐ u)))
  MatchA {n} 2  φ = Σ[ a ∈ Formula Ab n ] (Σ[ b ∈ Formula Ab n ] (φ ≡ (a ∧̇ b)))
  MatchA {n} 3  φ = Σ[ a ∈ Formula Ab n ] (Σ[ b ∈ Formula Ab n ] (φ ≡ (a ∨̇ b)))
  MatchA {n} 4  φ = Σ[ a ∈ Formula Ab n ] (Σ[ b ∈ Formula Ab n ] (φ ≡ (a ⇒̇ b)))
  MatchA {n} 5  φ = Σ[ a ∈ Formula Ab n ] (φ ≡ (¬̇ a))
  MatchA     6  φ = φ ≡ ⊤̇
  MatchA     7  φ = φ ≡ ⊥̇
  MatchA {n} 8  φ = Σ[ a ∈ Formula Ab (suc n) ] (φ ≡ (∃̇ a))
  MatchA {n} 9  φ = Σ[ a ∈ Formula Ab (suc n) ] (φ ≡ (∀̇ a))
  MatchA {n} 10 φ = Σ[ t ∈ Term Ab n ] (Σ[ a ∈ Formula Ab (suc n) ] (φ ≡ ∀̇∈ t a))
  MatchA {n} 11 φ = Σ[ t ∈ Term Ab n ] (Σ[ a ∈ Formula Ab (suc n) ] (φ ≡ ∃̇∈ t a))
  MatchA     _  _ = Empty.⊥*

  tagOfA : ∀ {n} → Formula Ab n → ℕ
  tagOfA ψ = VCode.tagOf (mapFo ι ψ)

  matchesA : ∀ {n} (ψ : Formula Ab n) → MatchA (tagOfA ψ) ψ
  matchesA (t ∈̇ u)  = t , (u , refl)
  matchesA (t ≐ u)  = t , (u , refl)
  matchesA (a ∧̇ b)  = a , (b , refl)
  matchesA (a ∨̇ b)  = a , (b , refl)
  matchesA (a ⇒̇ b)  = a , (b , refl)
  matchesA (¬̇ a)    = a , refl
  matchesA ⊤̇        = refl
  matchesA ⊥̇        = refl
  matchesA (∃̇ a)    = a , refl
  matchesA (∀̇ a)    = a , refl
  matchesA (∀̇∈ t a) = t , (a , refl)
  matchesA (∃̇∈ t a) = t , (a , refl)

  -- A member of the code set, handed over as a tagged pair, is the
  -- key of a formula of that constructor, at the arity the outer
  -- component names, with the payload the inner component holds.
  Decoded : (k : ℕ) (c ar p : V ℓ) → Type (ℓ-suc ℓ)
  Decoded k c ar p =
    Σ[ n ∈ ℕ ] Σ[ ψ ∈ Formula Ab n ]
      (MatchA k ψ × ((ar ≡ # n) × ((VCode.payOf (mapFo ι ψ) ≡ p) × (c ≡ pr (# n) (cd ψ)))))

  decode : (c : CS.S) → ⟨ fst c ∈ fst (AllCodes A) ⟩ → (k : ℕ) (ar p : V ℓ)
         → fst c ≡ pr ar (pr (# k) p)
         → ∥ Decoded k (fst c) ar p ∥₁
  decode c c∈ k ar p e = PT.map go (AllCodes-out A c c∈)
    where
    go : Σ[ n ∈ ℕ ] Σ[ ψ ∈ Formula Ab n ] (fst c ≡ fst (keyS A ψ)) → Decoded k (fst c) ar p
    go (n , ψ , q) =
      n , ψ , subst (λ j → MatchA j ψ) tag≡ (matchesA ψ)
      , ( sym (pr-inj e' .fst) , ( pr-inj inner .snd , q ))
      where
      e' : pr (# n) (cd ψ) ≡ pr ar (pr (# k) p)
      e' = sym q ∙ e
      inner : pr (# (tagOfA ψ)) (VCode.payOf (mapFo ι ψ)) ≡ pr (# k) p
      inner = sym (VCode.shape (mapFo ι ψ)) ∙ pr-inj e' .snd
      tag≡ : tagOfA ψ ≡ k
      tag≡ = #-inj′ (pr-inj inner .fst)

  -- The code of a formula at a transported arity is the code itself.
  cd-subst : ∀ {n n'} (e : n ≡ n') (ψ : Formula Ab n)
           → cd (subst (Formula Ab) e ψ) ≡ cd ψ
  cd-subst {n} e ψ = J (λ n' e' → cd (subst (Formula Ab) e' ψ) ≡ cd ψ)
    (cong cd (substRefl {B = Formula Ab} ψ)) e

  -- The code of a variable term whose index is read out of a numeral.
  -- Stated on its own, at a written type: elaborated inside a
  -- witness it does not finish (MEASURED: past 90 s at 7.7 GB).
  varCode : ∀ {k} (j : ℕ) (p : j < k) (x : V ℓ) → x ≡ # j
          → ct (var (fromℕ' k j p)) ≡ pr (# 1) x
  varCode {k} j p x e = cong (VCode.mkTag 1) (cong #_ (toFromId' k j p) ∙ sym e)

  varEq : ∀ {k} (j : ℕ) (p : j < k) (x T' : V ℓ) → x ≡ # j → T' ≡ pr (# 1) x
        → ct (var (fromℕ' k j p)) ≡ T'
  varEq {k} j p x T' e q = varCode j p x e ∙ sym q

  -- The witness, packed at a written type: composed at the site of
  -- its use, under the bounded row's pattern lambda, the same chain
  -- did not finish (MEASURED: past 60 s at 5.5 GB).
  varWit : ∀ {k} (j : ℕ) (p : j < k) (x T' : V ℓ) → x ≡ # j → T' ≡ pr (# 1) x
         → TmWit ι k T'
  varWit {k} j p x T' e q = var (fromℕ' k j p) , varEq j p x T' e q
```

```agda
-- =====================================================================
-- SECTION 2.  THE CODE SET IS CLOSED AND SHAPED, at the class level.
-- Closedness: the subcodes of a member are members, at the arity the
-- tag calls for (src/L/Coding/Model.lagda.md `closedAt`, through its
-- four introduction readers).  Shapedness: every member has one of
-- the twelve shapes (src/L/Coding/Shape.lagda.md `shapedAt`,
-- `shaped-in`), the walk of `closureShaped` at the whole code set.
-- Both are stated at any slot holding the set, so the consumer at
-- T ∷ C ∷ γ pays nothing to place them.
-- =====================================================================

module Closure (A : CS.S) where
  open Codes A

  module _ {n : ℕ} (C : Fin n) (γ : CS.S ^ n) (qC : fst (lookup C γ) ≡ fst (AllCodes A)) where

    private
      D : V ℓ
      D = fst (lookup C γ)

      inC : (c : CS.S) → ⟨ fst c ∈ D ⟩ → ⟨ fst c ∈ fst (AllCodes A) ⟩
      inC c c∈ = subst (λ u → ⟨ fst c ∈ u ⟩) qC c∈

      keyD : ∀ {k} (ψ : Formula Ab k) (x : V ℓ) → x ≡ pr (# k) (cd ψ) → ⟨ x ∈ D ⟩
      keyD ψ x e = subst (λ u → ⟨ x ∈ u ⟩) (sym qC) (keyC ψ x e)

      -- The four shapes of a clause, each generic in its constructor.
      bin : (k : ℕ) (op : ∀ {j} → Formula Ab j → Formula Ab j → Formula Ab j)
            (get : ∀ {j} (ψ : Formula Ab j) → MatchA k ψ
                 → Σ[ a' ∈ Formula Ab j ] (Σ[ b' ∈ Formula Ab j ] (ψ ≡ op a' b')))
            (pay : ∀ {j} (a' b' : Formula Ab j)
                 → VCode.payOf (mapFo ι (op a' b')) ≡ pr (cd a') (cd b'))
          → (c ar a b : CS.S) → ⟨ fst c ∈ D ⟩
          → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
          → ⟨ pr (fst ar) (fst a) ∈ D ⟩ × ⟨ pr (fst ar) (fst b) ∈ D ⟩
      bin k op get pay c ar a b c∈ sh =
        PT.rec (isProp× (snd (pr (fst ar) (fst a) ∈ D)) (snd (pr (fst ar) (fst b) ∈ D)))
          go (decode c (inC c c∈) k (fst ar) (pr (fst a) (fst b)) sh)
        where
        go : Decoded k (fst c) (fst ar) (pr (fst a) (fst b))
           → ⟨ pr (fst ar) (fst a) ∈ D ⟩ × ⟨ pr (fst ar) (fst b) ∈ D ⟩
        go (j , ψ , mt , (qar , (qp , _))) =
            keyD a' (pr (fst ar) (fst a)) (cong₂ pr qar (sym (pr-inj qab .fst)))
          , keyD b' (pr (fst ar) (fst b)) (cong₂ pr qar (sym (pr-inj qab .snd)))
          where
          a' = get ψ mt .fst
          b' = get ψ mt .snd .fst
          eψ = get ψ mt .snd .snd
          qab : pr (cd a') (cd b') ≡ pr (fst a) (fst b)
          qab = sym (pay a' b') ∙ cong (λ ψ' → VCode.payOf (mapFo ι ψ')) (sym eψ) ∙ qp

      un : (k : ℕ) (op : ∀ {j} → Formula Ab j → Formula Ab j)
           (get : ∀ {j} (ψ : Formula Ab j) → MatchA k ψ → Σ[ a' ∈ Formula Ab j ] (ψ ≡ op a'))
           (pay : ∀ {j} (a' : Formula Ab j) → VCode.payOf (mapFo ι (op a')) ≡ cd a')
         → (c ar a : CS.S) → ⟨ fst c ∈ D ⟩
         → fst c ≡ pr (fst ar) (pr (# k) (fst a))
         → ⟨ pr (fst ar) (fst a) ∈ D ⟩
      un k op get pay c ar a c∈ sh =
        PT.rec (snd (pr (fst ar) (fst a) ∈ D)) go (decode c (inC c c∈) k (fst ar) (fst a) sh)
        where
        go : Decoded k (fst c) (fst ar) (fst a) → ⟨ pr (fst ar) (fst a) ∈ D ⟩
        go (j , ψ , mt , (qar , (qp , _))) =
          keyD a' (pr (fst ar) (fst a)) (cong₂ pr qar (sym qa))
          where
          a' = get ψ mt .fst
          eψ = get ψ mt .snd
          qa : cd a' ≡ fst a
          qa = sym (pay a') ∙ cong (λ ψ' → VCode.payOf (mapFo ι ψ')) (sym eψ) ∙ qp

      unSucc : (k : ℕ) (op : ∀ {j} → Formula Ab (suc j) → Formula Ab j)
               (get : ∀ {j} (ψ : Formula Ab j) → MatchA k ψ → Σ[ a' ∈ Formula Ab (suc j) ] (ψ ≡ op a'))
               (pay : ∀ {j} (a' : Formula Ab (suc j)) → VCode.payOf (mapFo ι (op a')) ≡ cd a')
             → (c ar a : CS.S) → ⟨ fst c ∈ D ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (fst a))
             → ⟨ pr (sucV (fst ar)) (fst a) ∈ D ⟩
      unSucc k op get pay c ar a c∈ sh =
        PT.rec (snd (pr (sucV (fst ar)) (fst a) ∈ D)) go (decode c (inC c c∈) k (fst ar) (fst a) sh)
        where
        go : Decoded k (fst c) (fst ar) (fst a) → ⟨ pr (sucV (fst ar)) (fst a) ∈ D ⟩
        go (j , ψ , mt , (qar , (qp , _))) =
          keyD a' (pr (sucV (fst ar)) (fst a)) (cong₂ pr (cong sucV qar) (sym qa))
          where
          a' = get ψ mt .fst
          eψ = get ψ mt .snd
          qa : cd a' ≡ fst a
          qa = sym (pay a') ∙ cong (λ ψ' → VCode.payOf (mapFo ι ψ')) (sym eψ) ∙ qp

      binSucc : (k : ℕ) (op : ∀ {j} → Term Ab j → Formula Ab (suc j) → Formula Ab j)
                (get : ∀ {j} (ψ : Formula Ab j) → MatchA k ψ
                     → Σ[ t ∈ Term Ab j ] (Σ[ a' ∈ Formula Ab (suc j) ] (ψ ≡ op t a')))
                (pay : ∀ {j} (t : Term Ab j) (a' : Formula Ab (suc j))
                     → VCode.payOf (mapFo ι (op t a')) ≡ pr (ct t) (cd a'))
              → (c ar a b : CS.S) → ⟨ fst c ∈ D ⟩
              → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
              → ⟨ pr (sucV (fst ar)) (fst b) ∈ D ⟩
      binSucc k op get pay c ar a b c∈ sh =
        PT.rec (snd (pr (sucV (fst ar)) (fst b) ∈ D)) go
          (decode c (inC c c∈) k (fst ar) (pr (fst a) (fst b)) sh)
        where
        go : Decoded k (fst c) (fst ar) (pr (fst a) (fst b)) → ⟨ pr (sucV (fst ar)) (fst b) ∈ D ⟩
        go (j , ψ , mt , (qar , (qp , _))) =
          keyD a' (pr (sucV (fst ar)) (fst b)) (cong₂ pr (cong sucV qar) (sym (pr-inj qab .snd)))
          where
          t  = get ψ mt .fst
          a' = get ψ mt .snd .fst
          eψ = get ψ mt .snd .snd
          qab : pr (ct t) (cd a') ≡ pr (fst a) (fst b)
          qab = sym (pay t a') ∙ cong (λ ψ' → VCode.payOf (mapFo ι ψ')) (sym eψ) ∙ qp

    closed : ⟨ γ ⊨ closedAt C ⟩
    closed =
        binSameClosed-in C 2 γ (bin 2 _∧̇_ (λ _ m → m) (λ _ _ → refl))
      , ( binSameClosed-in C 3 γ (bin 3 _∨̇_ (λ _ m → m) (λ _ _ → refl))
      , ( binSameClosed-in C 4 γ (bin 4 _⇒̇_ (λ _ m → m) (λ _ _ → refl))
      , ( unSameClosed-in C 5 γ (un 5 ¬̇_ (λ _ m → m) (λ _ → refl))
      , ( unSuccClosed-in C 8 γ (unSucc 8 ∃̇_ (λ _ m → m) (λ _ → refl))
      , ( unSuccClosed-in C 9 γ (unSucc 9 ∀̇_ (λ _ m → m) (λ _ → refl))
      , ( binSuccClosed-in C 10 γ (binSucc 10 ∀̇∈ (λ _ m → m) (λ _ _ → refl))
      , binSuccClosed-in C 11 γ (binSucc 11 ∃̇∈ (λ _ m → m) (λ _ _ → refl)) ))))))

  -- SHAPEDNESS.  The walk of src/L/Coding/Shape.lagda.md
  -- `closureShaped`, at the whole code set and at a carrier slot.
  shaped : ∀ {n} (C Ai : Fin n) (γ : CS.S ^ n)
         → fst (lookup C γ) ≡ fst (AllCodes A) → fst (lookup Ai γ) ≡ fst A
         → ⟨ γ ⊨ shapedAt C Ai ⟩
  shaped {n} C Ai γ qC qA = shaped-in C Ai γ
    (λ c c∈ → PT.map (λ { (_ , ψ , q) → go ψ c q })
      (AllCodes-out A c (subst (λ u → ⟨ fst c ∈ u ⟩) qC c∈)))
    where
    into : (q : Ab) → ⟨ ι q ∈ fst (lookup Ai γ) ⟩
    into q = subst (λ u → ⟨ ι q ∈ u ⟩) (sym qA) (ι∈ q)

    A4 : Fin (4 + n)
    A4 = suc (suc (suc (suc Ai)))

    tw : ∀ {k} (t : Term Ab k) → TmWit ι k (fst (ctS t))
    tw t = t , refl

    tm1 : ∀ {k} (t : Term Ab k) (b c : CS.S)
        → ⟨ (b ∷ ctS t ∷ nn k ∷ c ∷ γ) ⊨ isTmAt (suc zero) (suc (suc zero)) A4 ⟩
    tm1 {k} t b c = isTmAt-in ι ιL (suc zero) (suc (suc zero)) A4
      (b ∷ ctS t ∷ nn k ∷ c ∷ γ) k refl into (tw t)

    tm0 : ∀ {k} (u : Term Ab k) (a c : CS.S)
        → ⟨ (ctS u ∷ a ∷ nn k ∷ c ∷ γ) ⊨ isTmAt zero (suc (suc zero)) A4 ⟩
    tm0 {k} u a c = isTmAt-in ι ιL zero (suc (suc zero)) A4
      (ctS u ∷ a ∷ nn k ∷ c ∷ γ) k refl into (tw u)

    go : ∀ {k} (ψ : Formula Ab k) (c : CS.S) → fst c ≡ fst (keyS A ψ) → ShapeWit Ai γ c
    go {k} (t ∈̇ u) c q =
      inl (nn k , (ctS t , (ctS u , (q , (tm1 t (ctS u) c , tm0 u (ctS t) c)))))
    go {k} (t ≐ u) c q =
      inr (inl (nn k , (ctS t , (ctS u , (q , (tm1 t (ctS u) c , tm0 u (ctS t) c))))))
    go {k} (a ∧̇ b) c q = inr (inr (inl (nn k , (cdS a , (cdS b , (q , tt*))))))
    go {k} (a ∨̇ b) c q = inr (inr (inr (inl (nn k , (cdS a , (cdS b , (q , tt*)))))))
    go {k} (a ⇒̇ b) c q = inr (inr (inr (inr (inl (nn k , (cdS a , (cdS b , (q , tt*))))))))
    go {k} (¬̇ a) c q = inr (inr (inr (inr (inr (inl (nn k , (cdS a , (q , tt*))))))))
    go {k} ⊤̇ c q =
      inr (inr (inr (inr (inr (inr (inl (nn k , (nn 0 , (q , sym (numeralL-fst 0))))))))))
    go {k} ⊥̇ c q =
      inr (inr (inr (inr (inr (inr (inr (inl (nn k , (nn 0 , (q , sym (numeralL-fst 0)))))))))))
    go {k} (∃̇ a) c q =
      inr (inr (inr (inr (inr (inr (inr (inr (inl (nn k , (cdS a , (q , tt*)))))))))))
    go {k} (∀̇ a) c q =
      inr (inr (inr (inr (inr (inr (inr (inr (inr (inl (nn k , (cdS a , (q , tt*))))))))))))
    go {k} (∀̇∈ t a) c q =
      inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inl
        (nn k , (ctS t , (cdS a , (q , tm1 t (cdS a) c))))))))))))))
    go {k} (∃̇∈ t a) c q =
      inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr
        (nn k , (ctS t , (cdS a , (q , tm1 t (cdS a) c))))))))))))))
```

```agda
-- =====================================================================
-- SECTION 3.  THE TWELVE CLAUSES HOLD AT THE UNIFORM TABLE, at the
-- class level.  src/L/Coding/Sound.lagda.md proves them for the table
-- of ONE formula; here the index set is the whole code set and the
-- table is the graph of src/L/Coding/Uniform.lagda.md `Table`.  What a
-- clause needs of the table is only the parts of an entry: the code is
-- the key of a formula of the constructor the tag names (Section 1),
-- and the value at a key is the satisfaction set of its formula
-- (`val-at`).  The bodies are Sound's, with the carrier slot tied to
-- the carrier by an equation rather than held as a constant.  The And
-- and Or clauses are not needed here: their bounded rows are read
-- directly at the site (Section 4).
-- =====================================================================

module UniformSound (A Ts : CS.S)
  (valOf : (x : CS.S) → ⟨ fst x ∈ fst (AllCodes A) ⟩ → CS.S)
  (valOf≡ : (x : CS.S) (mx : ⟨ fst x ∈ fst (AllCodes A) ⟩) → valOf x mx ≡ Table.val A A x mx)
  (pairs-out : (p : V ℓ) → ⟨ p ∈ fst Ts ⟩
             → ∥ Σ[ x ∈ CS.S ] Σ[ mx ∈ ⟨ fst x ∈ fst (AllCodes A) ⟩ ]
                  (p ≡ pr (fst x) (fst (valOf x mx))) ∥₁)
  {k : ℕ} (δ : CS.S ^ k) (Ci Ti Bi : Fin k)
  (qC : fst (lookup Ci δ) ≡ fst (AllCodes A))
  (qT : fst (lookup Ti δ) ≡ fst Ts)
  (qB : fst (lookup Bi δ) ≡ fst A) where

  open Codes A

  toS : ∀ {n} → Formula Ab n → Formula CS.S n
  toS = mapFo (asConst A)

  toT : ∀ {n} → Term Ab n → Term CS.S n
  toT = mapTm (asConst A)

  private
    ai0 : ∀ {j} → Fin (suc j)
    ai0 = zero
    ai1 : ∀ {j} → Fin (suc (suc j))
    ai1 = suc zero
    ai2 : ∀ {j} → Fin (suc (suc (suc j)))
    ai2 = suc (suc zero)
    ai5 : ∀ {j} → Fin (suc (suc (suc (suc (suc (suc j))))))
    ai5 = suc (suc (suc (suc (suc zero))))
    ai6 : ∀ {j} → Fin (suc (suc (suc (suc (suc (suc (suc j)))))))
    ai6 = suc (suc (suc (suc (suc (suc zero)))))

    inC : (c : CS.S) → ⟨ fst c ∈ fst (lookup Ci δ) ⟩ → ⟨ fst c ∈ fst (AllCodes A) ⟩
    inC c h = subst (λ u → ⟨ fst c ∈ u ⟩) qC h

    inT : (p : V ℓ) → ⟨ p ∈ fst (lookup Ti δ) ⟩ → ⟨ p ∈ fst Ts ⟩
    inT p h = subst (λ u → ⟨ p ∈ u ⟩) qT h

    -- An entry at the key of ψ has the satisfaction set of ψ as value.
    entryU : (x y : V ℓ) → ⟨ pr x y ∈ fst Ts ⟩
           → ∀ {n} (ψ : Formula Ab n) → x ≡ pr (# n) (cd ψ) → y ≡ fst (Sat A (toS ψ))
    entryU x y h ψ q = PT.rec (setIsSet y (fst (Sat A (toS ψ))))
      (λ { (x' , mx , e) →
        pr-inj e .snd
        ∙ cong fst (valOf≡ x' mx ∙ val-at A A ψ x' mx (sym (pr-inj e .fst) ∙ q)) })
      (pairs-out (pr x y) h)

    -- The two codings of a term agree (src/L/Coding/Model.lagda.md
    -- `codeBridgeTm`, as `keyBridge` uses it for a formula).
    tmBridge : ∀ {n} (t : Term Ab n) → fst LCode.⌜ toT t ⌝ᵗ ≡ ct t
    tmBridge t = codeBridgeTm (toT t) ∙ cong (λ u → VCode.⌜ u ⌝ᵗ) (mapTm-comp (asConst A) fst t)

  -- THE PARTS OF AN ENTRY, per clause shape.  The mirror of Sound's
  -- `Un`, `Bin`, `UnSucc`, `Atom`, `BinSucc` and `Const`, with the
  -- constructor read at the alphabet and carried to the model by
  -- `toS`.
  module Un (kk : ℕ) (op : ∀ {j} → Formula Ab j → Formula Ab j)
    (opS : ∀ {j} → Formula CS.S j → Formula CS.S j)
    (get : ∀ {j} (ψ : Formula Ab j) → MatchA kk ψ → Σ[ a' ∈ Formula Ab j ] (ψ ≡ op a'))
    (pay : ∀ {j} (a' : Formula Ab j) → VCode.payOf (mapFo ι (op a')) ≡ cd a')
    (opToS : ∀ {j} (a' : Formula Ab j) → toS (op a') ≡ opS (toS a'))
    where
    Parts : (ar yc ya : CS.S) → Type (ℓ-suc ℓ)
    Parts ar yc ya =
      Σ[ n ∈ ℕ ] (Σ[ a' ∈ Formula CS.S n ]
        ((# n ≡ fst ar)
         × ((fst yc ≡ fst (Sat A (opS a'))) × (fst ya ≡ fst (Sat A a')))))

    parts : (c ar a yc ya : CS.S)
          → ⟨ fst c ∈ fst (lookup Ci δ) ⟩
          → fst c ≡ pr (fst ar) (pr (# kk) (fst a))
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup Ti δ) ⟩
          → ⟨ pr (pr (fst ar) (fst a)) (fst ya) ∈ fst (lookup Ti δ) ⟩
          → ∥ Parts ar yc ya ∥₁
    parts c ar a yc ya c∈ sh hc ha = PT.map go (decode c (inC c c∈) kk (fst ar) (fst a) sh)
      where
      go : Decoded kk (fst c) (fst ar) (fst a) → Parts ar yc ya
      go (n , ψ , mt , (qar , (qp , qc))) =
        n , toS a₁ , sym qar
        , ( entryU (fst c) (fst yc) (inT _ hc) ψ qc
            ∙ cong (λ u → fst (Sat A (toS u))) eψ ∙ cong (λ u → fst (Sat A u)) (opToS a₁)
          , entryU (pr (fst ar) (fst a)) (fst ya) (inT _ ha) a₁ (cong₂ pr qar (sym qa)) )
        where
        a₁ = get ψ mt .fst
        eψ = get ψ mt .snd
        qa : cd a₁ ≡ fst a
        qa = sym (pay a₁) ∙ cong (λ u → VCode.payOf (mapFo ι u)) (sym eψ) ∙ qp

  module Bin (kk : ℕ) (op : ∀ {j} → Formula Ab j → Formula Ab j → Formula Ab j)
    (opS : ∀ {j} → Formula CS.S j → Formula CS.S j → Formula CS.S j)
    (get : ∀ {j} (ψ : Formula Ab j) → MatchA kk ψ
         → Σ[ a' ∈ Formula Ab j ] (Σ[ b' ∈ Formula Ab j ] (ψ ≡ op a' b')))
    (pay : ∀ {j} (a' b' : Formula Ab j) → VCode.payOf (mapFo ι (op a' b')) ≡ pr (cd a') (cd b'))
    (opToS : ∀ {j} (a' b' : Formula Ab j) → toS (op a' b') ≡ opS (toS a') (toS b'))
    where
    Parts : (ar yc ya yb : CS.S) → Type (ℓ-suc ℓ)
    Parts ar yc ya yb =
      Σ[ n ∈ ℕ ] (Σ[ a' ∈ Formula CS.S n ] (Σ[ b' ∈ Formula CS.S n ]
        ((# n ≡ fst ar)
         × ((fst yc ≡ fst (Sat A (opS a' b')))
            × ((fst ya ≡ fst (Sat A a')) × (fst yb ≡ fst (Sat A b')))))))

    parts : (c ar a b yc ya yb : CS.S)
          → ⟨ fst c ∈ fst (lookup Ci δ) ⟩
          → fst c ≡ pr (fst ar) (pr (# kk) (pr (fst a) (fst b)))
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup Ti δ) ⟩
          → ⟨ pr (pr (fst ar) (fst a)) (fst ya) ∈ fst (lookup Ti δ) ⟩
          → ⟨ pr (pr (fst ar) (fst b)) (fst yb) ∈ fst (lookup Ti δ) ⟩
          → ∥ Parts ar yc ya yb ∥₁
    parts c ar a b yc ya yb c∈ sh hc ha hb =
      PT.map go (decode c (inC c c∈) kk (fst ar) (pr (fst a) (fst b)) sh)
      where
      go : Decoded kk (fst c) (fst ar) (pr (fst a) (fst b)) → Parts ar yc ya yb
      go (n , ψ , mt , (qar , (qp , qc))) =
        n , toS a₁ , toS b₁ , sym qar
        , ( entryU (fst c) (fst yc) (inT _ hc) ψ qc
            ∙ cong (λ u → fst (Sat A (toS u))) eψ ∙ cong (λ u → fst (Sat A u)) (opToS a₁ b₁)
          , ( entryU (pr (fst ar) (fst a)) (fst ya) (inT _ ha) a₁ (cong₂ pr qar (sym (pr-inj qab .fst)))
            , entryU (pr (fst ar) (fst b)) (fst yb) (inT _ hb) b₁ (cong₂ pr qar (sym (pr-inj qab .snd))) ) )
        where
        a₁ = get ψ mt .fst
        b₁ = get ψ mt .snd .fst
        eψ = get ψ mt .snd .snd
        qab : pr (cd a₁) (cd b₁) ≡ pr (fst a) (fst b)
        qab = sym (pay a₁ b₁) ∙ cong (λ u → VCode.payOf (mapFo ι u)) (sym eψ) ∙ qp

  module UnSucc (kk : ℕ) (op : ∀ {j} → Formula Ab (suc j) → Formula Ab j)
    (opS : ∀ {j} → Formula CS.S (suc j) → Formula CS.S j)
    (get : ∀ {j} (ψ : Formula Ab j) → MatchA kk ψ → Σ[ a' ∈ Formula Ab (suc j) ] (ψ ≡ op a'))
    (pay : ∀ {j} (a' : Formula Ab (suc j)) → VCode.payOf (mapFo ι (op a')) ≡ cd a')
    (opToS : ∀ {j} (a' : Formula Ab (suc j)) → toS (op a') ≡ opS (toS a'))
    where
    Parts : (ar yc ya : CS.S) → Type (ℓ-suc ℓ)
    Parts ar yc ya =
      Σ[ n ∈ ℕ ] (Σ[ a' ∈ Formula CS.S (suc n) ]
        ((# n ≡ fst ar)
         × ((fst yc ≡ fst (Sat A (opS a'))) × (fst ya ≡ fst (Sat A a')))))

    parts : (c ar a yc ya : CS.S)
          → ⟨ fst c ∈ fst (lookup Ci δ) ⟩
          → fst c ≡ pr (fst ar) (pr (# kk) (fst a))
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup Ti δ) ⟩
          → ⟨ pr (pr (sucV (fst ar)) (fst a)) (fst ya) ∈ fst (lookup Ti δ) ⟩
          → ∥ Parts ar yc ya ∥₁
    parts c ar a yc ya c∈ sh hc ha = PT.map go (decode c (inC c c∈) kk (fst ar) (fst a) sh)
      where
      go : Decoded kk (fst c) (fst ar) (fst a) → Parts ar yc ya
      go (n , ψ , mt , (qar , (qp , qc))) =
        n , toS a₁ , sym qar
        , ( entryU (fst c) (fst yc) (inT _ hc) ψ qc
            ∙ cong (λ u → fst (Sat A (toS u))) eψ ∙ cong (λ u → fst (Sat A u)) (opToS a₁)
          , entryU (pr (sucV (fst ar)) (fst a)) (fst ya) (inT _ ha) a₁
              (cong₂ pr (cong sucV qar) (sym qa)) )
        where
        a₁ = get ψ mt .fst
        eψ = get ψ mt .snd
        qa : cd a₁ ≡ fst a
        qa = sym (pay a₁) ∙ cong (λ u → VCode.payOf (mapFo ι u)) (sym eψ) ∙ qp

  module Atom (kk : ℕ) (op : ∀ {j} → Term Ab j → Term Ab j → Formula Ab j)
    (opS : ∀ {j} → Term CS.S j → Term CS.S j → Formula CS.S j)
    (get : ∀ {j} (ψ : Formula Ab j) → MatchA kk ψ
         → Σ[ t ∈ Term Ab j ] (Σ[ u ∈ Term Ab j ] (ψ ≡ op t u)))
    (pay : ∀ {j} (t u : Term Ab j) → VCode.payOf (mapFo ι (op t u)) ≡ pr (ct t) (ct u))
    (opToS : ∀ {j} (t u : Term Ab j) → toS (op t u) ≡ opS (toT t) (toT u))
    where
    Parts : (ar a b yc : CS.S) → Type (ℓ-suc ℓ)
    Parts ar a b yc =
      Σ[ n ∈ ℕ ] (Σ[ t ∈ Term CS.S n ] (Σ[ u ∈ Term CS.S n ]
        ((# n ≡ fst ar)
         × ((fst a ≡ fst LCode.⌜ t ⌝ᵗ)
            × ((fst b ≡ fst LCode.⌜ u ⌝ᵗ)
               × (fst yc ≡ fst (Sat A (opS t u))))))))

    parts : (c ar a b yc : CS.S)
          → ⟨ fst c ∈ fst (lookup Ci δ) ⟩
          → fst c ≡ pr (fst ar) (pr (# kk) (pr (fst a) (fst b)))
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup Ti δ) ⟩
          → ∥ Parts ar a b yc ∥₁
    parts c ar a b yc c∈ sh hc = PT.map go (decode c (inC c c∈) kk (fst ar) (pr (fst a) (fst b)) sh)
      where
      go : Decoded kk (fst c) (fst ar) (pr (fst a) (fst b)) → Parts ar a b yc
      go (n , ψ , mt , (qar , (qp , qc))) =
        n , toT t₁ , toT u₁ , sym qar
        , ( sym (pr-inj qab .fst) ∙ sym (tmBridge t₁)
          , ( sym (pr-inj qab .snd) ∙ sym (tmBridge u₁)
            , entryU (fst c) (fst yc) (inT _ hc) ψ qc
              ∙ cong (λ u → fst (Sat A (toS u))) eψ ∙ cong (λ u → fst (Sat A u)) (opToS t₁ u₁) ) )
        where
        t₁ = get ψ mt .fst
        u₁ = get ψ mt .snd .fst
        eψ = get ψ mt .snd .snd
        qab : pr (ct t₁) (ct u₁) ≡ pr (fst a) (fst b)
        qab = sym (pay t₁ u₁) ∙ cong (λ u → VCode.payOf (mapFo ι u)) (sym eψ) ∙ qp

  module BinSucc (kk : ℕ) (op : ∀ {j} → Term Ab j → Formula Ab (suc j) → Formula Ab j)
    (opS : ∀ {j} → Term CS.S j → Formula CS.S (suc j) → Formula CS.S j)
    (get : ∀ {j} (ψ : Formula Ab j) → MatchA kk ψ
         → Σ[ t ∈ Term Ab j ] (Σ[ a' ∈ Formula Ab (suc j) ] (ψ ≡ op t a')))
    (pay : ∀ {j} (t : Term Ab j) (a' : Formula Ab (suc j))
         → VCode.payOf (mapFo ι (op t a')) ≡ pr (ct t) (cd a'))
    (opToS : ∀ {j} (t : Term Ab j) (a' : Formula Ab (suc j)) → toS (op t a') ≡ opS (toT t) (toS a'))
    where
    Parts : (ar a b yc yb : CS.S) → Type (ℓ-suc ℓ)
    Parts ar a b yc yb =
      Σ[ n ∈ ℕ ] (Σ[ t ∈ Term CS.S n ] (Σ[ a' ∈ Formula CS.S (suc n) ]
        ((# n ≡ fst ar)
         × ((fst a ≡ fst LCode.⌜ t ⌝ᵗ)
            × ((fst yc ≡ fst (Sat A (opS t a')))
               × (fst yb ≡ fst (Sat A a')))))))

    parts : (c ar a b yc yb : CS.S)
          → ⟨ fst c ∈ fst (lookup Ci δ) ⟩
          → fst c ≡ pr (fst ar) (pr (# kk) (pr (fst a) (fst b)))
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup Ti δ) ⟩
          → ⟨ pr (pr (sucV (fst ar)) (fst b)) (fst yb) ∈ fst (lookup Ti δ) ⟩
          → ∥ Parts ar a b yc yb ∥₁
    parts c ar a b yc yb c∈ sh hc hb =
      PT.map go (decode c (inC c c∈) kk (fst ar) (pr (fst a) (fst b)) sh)
      where
      go : Decoded kk (fst c) (fst ar) (pr (fst a) (fst b)) → Parts ar a b yc yb
      go (n , ψ , mt , (qar , (qp , qc))) =
        n , toT t₁ , toS a₁ , sym qar
        , ( sym (pr-inj qab .fst) ∙ sym (tmBridge t₁)
          , ( entryU (fst c) (fst yc) (inT _ hc) ψ qc
              ∙ cong (λ u → fst (Sat A (toS u))) eψ ∙ cong (λ u → fst (Sat A u)) (opToS t₁ a₁)
            , entryU (pr (sucV (fst ar)) (fst b)) (fst yb) (inT _ hb) a₁
                (cong₂ pr (cong sucV qar) (sym (pr-inj qab .snd))) ) )
        where
        t₁ = get ψ mt .fst
        a₁ = get ψ mt .snd .fst
        eψ = get ψ mt .snd .snd
        qab : pr (ct t₁) (cd a₁) ≡ pr (fst a) (fst b)
        qab = sym (pay t₁ a₁) ∙ cong (λ u → VCode.payOf (mapFo ι u)) (sym eψ) ∙ qp

  module Const (kk : ℕ) (c₀ : ∀ {j} → Formula Ab j) (c₀S : ∀ {j} → Formula CS.S j)
    (get : ∀ {j} (ψ : Formula Ab j) → MatchA kk ψ → ψ ≡ c₀)
    (opToS : ∀ {j} → toS (c₀ {j}) ≡ c₀S {j})
    where
    Parts : (ar yc : CS.S) → Type (ℓ-suc ℓ)
    Parts ar yc = Σ[ n ∈ ℕ ] ((# n ≡ fst ar) × (fst yc ≡ fst (Sat A (c₀S {n}))))

    parts : (c ar a yc : CS.S)
          → ⟨ fst c ∈ fst (lookup Ci δ) ⟩
          → fst c ≡ pr (fst ar) (pr (# kk) (fst a))
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup Ti δ) ⟩
          → ∥ Parts ar yc ∥₁
    parts c ar a yc c∈ sh hc = PT.map go (decode c (inC c c∈) kk (fst ar) (fst a) sh)
      where
      go : Decoded kk (fst c) (fst ar) (fst a) → Parts ar yc
      go (n , ψ , mt , (qar , (qp , qc))) =
        n , sym qar
        , ( entryU (fst c) (fst yc) (inT _ hc) ψ qc
            ∙ cong (λ u → fst (Sat A (toS u))) (get ψ mt) ∙ cong (λ u → fst (Sat A u)) opToS )

  -- The instances.  `opToS` is refl at every constructor: `mapFo`
  -- computes.
  module BinAnd = Bin 2 _∧̇_ _∧̇_ (λ _ m → m) (λ _ _ → refl) (λ _ _ → refl)
  module BinOr  = Bin 3 _∨̇_ _∨̇_ (λ _ m → m) (λ _ _ → refl) (λ _ _ → refl)
  module BinImp = Bin 4 _⇒̇_ _⇒̇_ (λ _ m → m) (λ _ _ → refl) (λ _ _ → refl)
  module UnNeg  = Un 5 ¬̇_ ¬̇_ (λ _ m → m) (λ _ → refl) (λ _ → refl)
  module ConstTop = Const 6 ⊤̇ ⊤̇ (λ _ m → m) refl
  module ConstBot = Const 7 ⊥̇ ⊥̇ (λ _ m → m) refl
  module UnEx  = UnSucc 8 ∃̇_ ∃̇_ (λ _ m → m) (λ _ → refl) (λ _ → refl)
  module UnAll = UnSucc 9 ∀̇_ ∀̇_ (λ _ m → m) (λ _ → refl) (λ _ → refl)
  module AtomMem = Atom 0 _∈̇_ _∈̇_ (λ _ m → m) (λ _ _ → refl) (λ _ _ → refl)
  module AtomEq  = Atom 1 _≐_ _≐_ (λ _ m → m) (λ _ _ → refl) (λ _ _ → refl)
  module BndAll = BinSucc 10 ∀̇∈ ∀̇∈ (λ _ m → m) (λ _ _ → refl) (λ _ _ → refl)
  module BndEx  = BinSucc 11 ∃̇∈ ∃̇∈ (λ _ m → m) (λ _ _ → refl) (λ _ _ → refl)

  -- THE TEN CLAUSES.  Sound's proofs, the carrier slot read through qB.
  topSound : ⟨ δ ⊨ topClauseAt Ci Ti Bi ⟩
  topSound = topClause-in Ci Ti Bi δ
    (λ c ar a yc E c∈ sh hc hE →
      let P  = ConstTop.parts c ar a yc c∈ sh hc
          δ' = E ∷ yc ∷ a ∷ ar ∷ c ∷ δ
          Ea = suc (suc (suc (suc (suc Bi))))
          ai = suc (suc (suc zero))
      in
        (λ z hz → PT.rec (snd (fst z ∈ fst E))
          (λ { (m , (qm , ec)) →
            Ambient.outof A δ' zero ai Ea m (sym qm) qB hE z
              (subst ⟨_⟩ (Sat-mem A (⊤̇ {n = m}) z)
                (subst (λ w → ⟨ fst z ∈ w ⟩) ec hz) .fst) })
          P)
      , (λ z hz → PT.rec (snd (fst z ∈ fst yc))
          (λ { (m , (qm , ec)) →
            subst (λ w → ⟨ fst z ∈ w ⟩) (sym ec)
              (subst ⟨_⟩ (sym (Sat-mem A (⊤̇ {n = m}) z))
                ( Ambient.into A δ' zero ai Ea m (sym qm) qB hE z hz
                , tt* )) })
          P))

  botSound : ⟨ δ ⊨ botClauseAt Ci Ti ⟩
  botSound = botClause-in Ci Ti δ
    (λ c ar a yc c∈ sh hc →
      let P = ConstBot.parts c ar a yc c∈ sh hc in
        (λ z hz → PT.rec isProp⊥*
          (λ { (m , (qm , ec)) →
            subst ⟨_⟩ (Sat-mem A (⊥̇ {n = m}) z)
              (subst (λ w → ⟨ fst z ∈ w ⟩) ec hz) .snd })
          P)
      , (λ z hz → Empty.rec* hz))

  allInSound : ⟨ δ ⊨ allInClauseAt Ci Ti Bi ⟩
  allInSound = bndClause-in Ci Ti Bi 10 (bodyAll Bi) δ
    (λ c ar a b yc yb E c∈ sh hc hb hE →
      let P  = BndAll.parts c ar a b yc yb c∈ sh hc hb
          δ' = E ∷ yb ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ δ
          Ea = suc (suc (suc (suc (suc (suc (suc Bi))))))
          ai = suc (suc (suc (suc (suc zero))))
      in
        (λ z hz → PT.rec (snd ((z ∷ δ') ⊨ bodyAll Bi))
          (λ { (m , t , a' , (qm , (ea , (ec , eb)))) →
            let s  = subst ⟨_⟩ (Sat-mem A (∀̇∈ t a') z)
                       (subst (λ w → ⟨ fst z ∈ w ⟩) ec hz)
                z∈ = Ambient.outof A δ' zero ai Ea m (sym qm) qB hE z (s .fst)
                ae = Ambient.asEnv A δ' zero ai Ea m (sym qm) qB hE z z∈
            in bodyAll-in Bi (z ∷ δ') z∈
                 (λ w hw x e' x∈B x∈w hcs →
                   subst (λ v → ⟨ fst e' ∈ v ⟩) (sym eb)
                     (cond∀∈-out A t a' z (s .snd) w
                       (termAgree t (w ∷ z ∷ δ') ai6 ai1 ai0
                          (w ∷ z ∷ []) ai0 ai1 ea refl refl .fst hw)
                       x e' (subst (λ u → ⟨ fst x ∈ u ⟩) qB x∈B) x∈w
                       (consAtL-transport (e' ∷ x ∷ w ∷ z ∷ δ')
                         (e' ∷ x ∷ w ∷ z ∷ []) zero (suc zero)
                         (suc (suc (suc zero))) zero (suc zero)
                         (suc (suc (suc zero)))
                         (λ i → ⟪ fst A ⟫↪ (ae .fst i)) (ae .snd)
                         refl refl refl hcs))) })
          P)
      , (λ z hz → PT.rec (snd (fst z ∈ fst yc))
          (λ { (m , t , a' , (qm , (ea , (ec , eb)))) →
            let r  = bodyAll-out Bi (z ∷ δ') hz
                ae = Ambient.asEnv A δ' zero ai Ea m (sym qm) qB hE z (r .fst)
            in subst (λ w → ⟨ fst z ∈ w ⟩) (sym ec)
                 (subst ⟨_⟩ (sym (Sat-mem A (∀̇∈ t a') z))
                   ( Ambient.into A δ' zero ai Ea m (sym qm) qB hE z (r .fst)
                   , cond∀∈-in A t a' z
                       (λ w hw x e' x∈B x∈w hcs →
                         subst (λ v → ⟨ fst e' ∈ v ⟩) eb
                           (r .snd w
                             (termAgree t (w ∷ z ∷ δ') ai6 ai1 ai0
                                (w ∷ z ∷ []) ai0 ai1 ea refl refl .snd hw)
                             x e' (subst (λ u → ⟨ fst x ∈ u ⟩) (sym qB) x∈B) x∈w
                             (consAtL-transport (e' ∷ x ∷ w ∷ z ∷ [])
                               (e' ∷ x ∷ w ∷ z ∷ δ') zero (suc zero)
                               (suc (suc (suc zero))) zero (suc zero)
                               (suc (suc (suc zero)))
                               (λ i → ⟪ fst A ⟫↪ (ae .fst i)) (ae .snd)
                               refl refl refl hcs))) )) })
          P))

  exInSound : ⟨ δ ⊨ exInClauseAt Ci Ti Bi ⟩
  exInSound = bndClause-in Ci Ti Bi 11 (bodyEx Bi) δ
    (λ c ar a b yc yb E c∈ sh hc hb hE →
      let P  = BndEx.parts c ar a b yc yb c∈ sh hc hb
          δ' = E ∷ yb ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ δ
          Ea = suc (suc (suc (suc (suc (suc (suc Bi))))))
          ai = suc (suc (suc (suc (suc zero))))
      in
        (λ z hz → PT.rec (snd ((z ∷ δ') ⊨ bodyEx Bi))
          (λ { (m , t , a' , (qm , (ea , (ec , eb)))) →
            let s  = subst ⟨_⟩ (Sat-mem A (∃̇∈ t a') z)
                       (subst (λ w → ⟨ fst z ∈ w ⟩) ec hz)
                z∈ = Ambient.outof A δ' zero ai Ea m (sym qm) qB hE z (s .fst)
                ae = Ambient.asEnv A δ' zero ai Ea m (sym qm) qB hE z z∈
            in bodyEx-in Bi (z ∷ δ') z∈
                 (PT.map (λ { (w , (hw , hx)) → w
                    , ( termAgree t (w ∷ z ∷ δ') ai6 ai1 ai0
                          (w ∷ z ∷ []) ai0 ai1 ea refl refl .snd hw
                      , PT.map (λ { (x , ((x∈B , x∈w) , (e' , (hcs , he)))) →
                          x , ((subst (λ u → ⟨ fst x ∈ u ⟩) (sym qB) x∈B , x∈w) , (e'
                          , ( consAtL-transport (e' ∷ x ∷ w ∷ z ∷ [])
                                (e' ∷ x ∷ w ∷ z ∷ δ') zero (suc zero)
                                (suc (suc (suc zero))) zero (suc zero)
                                (suc (suc (suc zero)))
                                (λ i → ⟪ fst A ⟫↪ (ae .fst i)) (ae .snd)
                                refl refl refl hcs
                            , subst (λ v → ⟨ fst e' ∈ v ⟩) (sym eb) he ))) })
                          hx ) })
                    (cond∃∈-out A t a' z (s .snd))) })
          P)
      , (λ z hz → PT.rec (snd (fst z ∈ fst yc))
          (λ { (m , t , a' , (qm , (ea , (ec , eb)))) →
            let r  = bodyEx-out Bi (z ∷ δ') hz
                ae = Ambient.asEnv A δ' zero ai Ea m (sym qm) qB hE z (r .fst)
            in subst (λ w → ⟨ fst z ∈ w ⟩) (sym ec)
                 (subst ⟨_⟩ (sym (Sat-mem A (∃̇∈ t a') z))
                   ( Ambient.into A δ' zero ai Ea m (sym qm) qB hE z (r .fst)
                   , cond∃∈-in A t a' z
                       (PT.map (λ { (w , (hw , hx)) → w
                          , ( termAgree t (w ∷ z ∷ δ') ai6 ai1 ai0
                                (w ∷ z ∷ []) ai0 ai1 ea refl refl .fst hw
                            , PT.map (λ { (x , ((x∈B , x∈w) , (e' , (hcs , he)))) →
                                x , ((subst (λ u → ⟨ fst x ∈ u ⟩) qB x∈B , x∈w) , (e'
                                , ( consAtL-transport (e' ∷ x ∷ w ∷ z ∷ δ')
                                      (e' ∷ x ∷ w ∷ z ∷ []) zero (suc zero)
                                      (suc (suc (suc zero))) zero (suc zero)
                                      (suc (suc (suc zero)))
                                      (λ i → ⟪ fst A ⟫↪ (ae .fst i)) (ae .snd)
                                      refl refl refl hcs
                                  , subst (λ v → ⟨ fst e' ∈ v ⟩) eb he ))) })
                                hx ) })
                          (r .snd)) )) })
          P))

  existSound : ⟨ δ ⊨ existClauseAt Ci Ti Bi ⟩
  existSound = quantClause-in Ci Ti Bi 8 (body∃ Bi) δ
    (λ c ar a yc ya E c∈ sh hc ha hE →
      let P  = UnEx.parts c ar a yc ya c∈ sh hc ha
          δ' = E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ δ
          Ea = suc (suc (suc (suc (suc (suc Bi)))))
          ai = suc (suc (suc (suc zero)))
      in
        (λ z hz → PT.rec (snd ((z ∷ δ') ⊨ body∃ Bi))
          (λ { (m , a' , (qm , (ec , ea))) →
            let s  = subst ⟨_⟩ (Sat-mem A (∃̇ a') z)
                       (subst (λ w → ⟨ fst z ∈ w ⟩) ec hz)
                ae = Ambient.asEnv A δ' zero ai Ea m (sym qm) qB hE z
                       (Ambient.outof A δ' zero ai Ea m (sym qm) qB hE z (s .fst))
            in body∃-in Bi (z ∷ δ')
                 (Ambient.outof A δ' zero ai Ea m (sym qm) qB hE z (s .fst))
                 (PT.map
                   (λ { (x , (x∈ , (e' , (hcs , he)))) →
                      x , subst (λ u → ⟨ fst x ∈ u ⟩) (sym qB) x∈ , e'
                      , ( consAtL-transport (e' ∷ x ∷ z ∷ []) (e' ∷ x ∷ z ∷ δ')
                            zero (suc zero) (suc (suc zero))
                            zero (suc zero) (suc (suc zero))
                            (λ i → ⟪ fst A ⟫↪ (ae .fst i)) (ae .snd)
                            refl refl refl hcs
                        , subst (λ w → ⟨ fst e' ∈ w ⟩) (sym ea) he ) })
                   (cond∃-out A a' z (s .snd))) })
          P)
      , (λ z hz → PT.rec (snd (fst z ∈ fst yc))
          (λ { (m , a' , (qm , (ec , ea))) →
            let r  = body∃-out Bi (z ∷ δ') hz
                ae = Ambient.asEnv A δ' zero ai Ea m (sym qm) qB hE z (r .fst)
            in subst (λ w → ⟨ fst z ∈ w ⟩) (sym ec)
                 (subst ⟨_⟩ (sym (Sat-mem A (∃̇ a') z))
                   ( Ambient.into A δ' zero ai Ea m (sym qm) qB hE z (r .fst)
                   , cond∃-in A a' z (PT.map
                       (λ { (x , (x∈ , (e' , (hcs , he)))) →
                          x , subst (λ u → ⟨ fst x ∈ u ⟩) qB x∈ , e'
                          , ( consAtL-transport (e' ∷ x ∷ z ∷ δ') (e' ∷ x ∷ z ∷ [])
                                zero (suc zero) (suc (suc zero))
                                zero (suc zero) (suc (suc zero))
                                (λ i → ⟪ fst A ⟫↪ (ae .fst i)) (ae .snd)
                                refl refl refl hcs
                            , subst (λ w → ⟨ fst e' ∈ w ⟩) ea he ) })
                       (r .snd)) )) })
          P))

  forallSound : ⟨ δ ⊨ forallClauseAt Ci Ti Bi ⟩
  forallSound = quantClause-in Ci Ti Bi 9 (body∀ Bi) δ
    (λ c ar a yc ya E c∈ sh hc ha hE →
      let P  = UnAll.parts c ar a yc ya c∈ sh hc ha
          δ' = E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ δ
          Ea = suc (suc (suc (suc (suc (suc Bi)))))
          ai = suc (suc (suc (suc zero)))
      in
        (λ z hz → PT.rec (snd ((z ∷ δ') ⊨ body∀ Bi))
          (λ { (m , a' , (qm , (ec , ea))) →
            let s  = subst ⟨_⟩ (Sat-mem A (∀̇ a') z)
                       (subst (λ w → ⟨ fst z ∈ w ⟩) ec hz)
                z∈ = Ambient.outof A δ' zero ai Ea m (sym qm) qB hE z (s .fst)
                ae = Ambient.asEnv A δ' zero ai Ea m (sym qm) qB hE z z∈
            in body∀-in Bi (z ∷ δ') z∈
                 (λ x e' x∈ hcs → subst (λ w → ⟨ fst e' ∈ w ⟩) (sym ea)
                   (cond∀-out A a' z (s .snd) x e' (subst (λ u → ⟨ fst x ∈ u ⟩) qB x∈)
                     (consAtL-transport (e' ∷ x ∷ z ∷ δ') (e' ∷ x ∷ z ∷ [])
                       zero (suc zero) (suc (suc zero))
                       zero (suc zero) (suc (suc zero))
                       (λ i → ⟪ fst A ⟫↪ (ae .fst i)) (ae .snd)
                       refl refl refl hcs))) })
          P)
      , (λ z hz → PT.rec (snd (fst z ∈ fst yc))
          (λ { (m , a' , (qm , (ec , ea))) →
            let r  = body∀-out Bi (z ∷ δ') hz
                ae = Ambient.asEnv A δ' zero ai Ea m (sym qm) qB hE z (r .fst)
            in subst (λ w → ⟨ fst z ∈ w ⟩) (sym ec)
                 (subst ⟨_⟩ (sym (Sat-mem A (∀̇ a') z))
                   ( Ambient.into A δ' zero ai Ea m (sym qm) qB hE z (r .fst)
                   , cond∀-in A a' z
                       (λ x e' x∈ hcs → subst (λ w → ⟨ fst e' ∈ w ⟩) ea
                         (r .snd x e' (subst (λ u → ⟨ fst x ∈ u ⟩) (sym qB) x∈)
                           (consAtL-transport (e' ∷ x ∷ z ∷ []) (e' ∷ x ∷ z ∷ δ')
                             zero (suc zero) (suc (suc zero))
                             zero (suc zero) (suc (suc zero))
                             (λ i → ⟪ fst A ⟫↪ (ae .fst i)) (ae .snd)
                             refl refl refl hcs))) )) })
          P))

  memSound : ⟨ δ ⊨ memClauseAt Ci Ti Bi ⟩
  memSound = atomClause-in Ci Ti Bi 0 memRel δ
    (λ c ar a b yc E c∈ sh hc hE →
      let P  = AtomMem.parts c ar a b yc c∈ sh hc
          δ' = E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ δ
          Ea = suc (suc (suc (suc (suc (suc Bi)))))
          ai = suc (suc (suc (suc zero)))
      in
        (λ z hz → PT.rec (snd ((z ∷ δ') ⊨ atomBody memRel))
          (λ { (m , t , u , (qm , (ea , (eb , ec)))) →
            let s = subst ⟨_⟩ (Sat-mem A (t ∈̇ u) z)
                      (subst (λ w → ⟨ fst z ∈ w ⟩) ec hz)
            in atomBody-in memRel (z ∷ δ')
                 (Ambient.outof A δ' zero ai Ea m (sym qm) qB hE z (s .fst))
                 (PT.map
                   (λ { (v , (w , (ht , (hu , hr)))) → v , w
                      , ( termAgree t (w ∷ v ∷ z ∷ δ') ai6 ai2 ai1
                            (w ∷ v ∷ z ∷ []) ai1 ai2 ea refl refl .snd ht
                        , ( termAgree u (w ∷ v ∷ z ∷ δ') ai5 ai2 ai0
                              (w ∷ v ∷ z ∷ []) ai0 ai2 eb refl refl .snd hu
                          , hr ) ) })
                   (cond∈-out A t u z (s .snd))) })
          P)
      , (λ z hz → PT.rec (snd (fst z ∈ fst yc))
          (λ { (m , t , u , (qm , (ea , (eb , ec)))) →
            let r = atomBody-out memRel (z ∷ δ') hz in
            subst (λ w → ⟨ fst z ∈ w ⟩) (sym ec)
              (subst ⟨_⟩ (sym (Sat-mem A (t ∈̇ u) z))
                ( Ambient.into A δ' zero ai Ea m (sym qm) qB hE z (r .fst)
                , cond∈-in A t u z (PT.map
                    (λ { (v , (w , (ht , (hu , hr)))) → v , w
                       , ( termAgree t (w ∷ v ∷ z ∷ δ') ai6 ai2 ai1
                             (w ∷ v ∷ z ∷ []) ai1 ai2 ea refl refl .fst ht
                         , ( termAgree u (w ∷ v ∷ z ∷ δ') ai5 ai2 ai0
                               (w ∷ v ∷ z ∷ []) ai0 ai2 eb refl refl .fst hu
                           , hr ) ) })
                    (r .snd)) )) })
          P))

  eqSound : ⟨ δ ⊨ eqClauseAt Ci Ti Bi ⟩
  eqSound = atomClause-in Ci Ti Bi 1 eqRel δ
    (λ c ar a b yc E c∈ sh hc hE →
      let P  = AtomEq.parts c ar a b yc c∈ sh hc
          δ' = E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ δ
          Ea = suc (suc (suc (suc (suc (suc Bi)))))
          ai = suc (suc (suc (suc zero)))
      in
        (λ z hz → PT.rec (snd ((z ∷ δ') ⊨ atomBody eqRel))
          (λ { (m , t , u , (qm , (ea , (eb , ec)))) →
            let s = subst ⟨_⟩ (Sat-mem A (t ≐ u) z)
                      (subst (λ w → ⟨ fst z ∈ w ⟩) ec hz)
            in atomBody-in eqRel (z ∷ δ')
                 (Ambient.outof A δ' zero ai Ea m (sym qm) qB hE z (s .fst))
                 (PT.map
                   (λ { (v , (w , (ht , (hu , hr)))) → v , w
                      , ( termAgree t (w ∷ v ∷ z ∷ δ') ai6 ai2 ai1
                            (w ∷ v ∷ z ∷ []) ai1 ai2 ea refl refl .snd ht
                        , ( termAgree u (w ∷ v ∷ z ∷ δ') ai5 ai2 ai0
                              (w ∷ v ∷ z ∷ []) ai0 ai2 eb refl refl .snd hu
                          , hr ) ) })
                   (cond≐-out A t u z (s .snd))) })
          P)
      , (λ z hz → PT.rec (snd (fst z ∈ fst yc))
          (λ { (m , t , u , (qm , (ea , (eb , ec)))) →
            let r = atomBody-out eqRel (z ∷ δ') hz in
            subst (λ w → ⟨ fst z ∈ w ⟩) (sym ec)
              (subst ⟨_⟩ (sym (Sat-mem A (t ≐ u) z))
                ( Ambient.into A δ' zero ai Ea m (sym qm) qB hE z (r .fst)
                , cond≐-in A t u z (PT.map
                    (λ { (v , (w , (ht , (hu , hr)))) → v , w
                       , ( termAgree t (w ∷ v ∷ z ∷ δ') ai6 ai2 ai1
                             (w ∷ v ∷ z ∷ []) ai1 ai2 ea refl refl .fst ht
                         , ( termAgree u (w ∷ v ∷ z ∷ δ') ai5 ai2 ai0
                               (w ∷ v ∷ z ∷ []) ai0 ai2 eb refl refl .fst hu
                           , hr ) ) })
                    (r .snd)) )) })
          P))

  impSound : ⟨ δ ⊨ impClauseAt Ci Ti Bi ⟩
  impSound = impClause-in Ci Ti Bi δ
    (λ c ar a b yc ya yb E c∈ sh hc ha hb hE →
      let P  = BinImp.parts c ar a b yc ya yb c∈ sh hc ha hb
          δ' = E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ δ
          Ea = suc (suc (suc (suc (suc (suc (suc (suc Bi)))))))
          ai = suc (suc (suc (suc (suc (suc zero)))))
      in
        (λ z hz → PT.rec
          (isProp× (snd (fst z ∈ fst E))
            (isPropΠ (λ _ → snd (fst z ∈ fst yb))))
          (λ { (m , a' , b' , (qm , (ec , (ea , eb)))) →
            let s = subst ⟨_⟩ (Sat-mem A (a' ⇒̇ b') z)
                      (subst (λ w → ⟨ fst z ∈ w ⟩) ec hz)
            in Ambient.outof A δ' zero ai Ea m (sym qm) qB hE z (s .fst)
             , (λ w → subst (λ v → ⟨ fst z ∈ v ⟩) (sym eb)
                 (s .snd (subst (λ v → ⟨ fst z ∈ v ⟩) ea w))) })
          P)
      , (λ z hz → PT.rec (snd (fst z ∈ fst yc))
          (λ { (m , a' , b' , (qm , (ec , (ea , eb)))) →
            subst (λ w → ⟨ fst z ∈ w ⟩) (sym ec)
              (subst ⟨_⟩ (sym (Sat-mem A (a' ⇒̇ b') z))
                ( Ambient.into A δ' zero ai Ea m (sym qm) qB hE z (hz .fst)
                , (λ w → subst (λ v → ⟨ fst z ∈ v ⟩) eb
                    (hz .snd (subst (λ v → ⟨ fst z ∈ v ⟩) (sym ea) w))) )) })
          P))

  negSound : ⟨ δ ⊨ negClauseAt Ci Ti Bi ⟩
  negSound = negClause-in Ci Ti Bi δ
    (λ c ar a yc ya E c∈ sh hc ha hE →
      let P = UnNeg.parts c ar a yc ya c∈ sh hc ha
          δ' = E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ δ
      in
        (λ z hz → PT.rec
          (isProp× (snd (fst z ∈ fst E)) (isPropΠ (λ _ → isProp⊥)))
          (λ { (m , a' , (qm , (ec , ea))) →
            let s = subst ⟨_⟩ (Sat-mem A (¬̇ a') z)
                      (subst (λ w → ⟨ fst z ∈ w ⟩) ec hz)
            in Ambient.outof A δ' zero (suc (suc (suc (suc zero))))
                 (suc (suc (suc (suc (suc (suc Bi))))))
                 m (sym qm) qB hE z (s .fst)
             , (λ w → s .snd (subst (λ v → ⟨ fst z ∈ v ⟩) ea w)) })
          P)
      , (λ z hz → PT.rec (snd (fst z ∈ fst yc))
          (λ { (m , a' , (qm , (ec , ea))) →
            subst (λ w → ⟨ fst z ∈ w ⟩) (sym ec)
              (subst ⟨_⟩ (sym (Sat-mem A (¬̇ a') z))
                ( Ambient.into A δ' zero (suc (suc (suc (suc zero))))
                    (suc (suc (suc (suc (suc (suc Bi)))))) m (sym qm) qB hE z
                    (hz .fst)
                , (λ w → hz .snd (subst (λ v → ⟨ fst z ∈ v ⟩) (sym ea) w)) )) })
          P))
```

```agda
-- =====================================================================
-- SECTION 4.  THE SITE.  The environment T ∷ C ∷ γ of
-- src/L/GCH/Complete.lagda.md `Rows`, with C the code set and T the
-- graph of the uniform table (src/L/Coding/Uniform.lagda.md `Table`),
-- and the closure facts of the bound K as src/L/GCH/Level.lagda.md
-- `KC` packages them.  The table arrives as its two readers, so the
-- consumer keeps its own seal on the graph.  Each row is the class-
-- level fact of Sections 1-2, or of the table, carried into its
-- bounded form by the agreement of src/L/Condensation.lagda.md with
-- the ties the bound supplies.
-- =====================================================================

open KFactsNS
open Tags

module Site {m : ℕ} (d w O K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m)
            (γ : CS.S ^ m) (A Ts : CS.S)
            (valOf : (x : CS.S) → ⟨ fst x ∈ fst (AllCodes A) ⟩ → CS.S)
            (valOf≡ : (x : CS.S) (mx : ⟨ fst x ∈ fst (AllCodes A) ⟩)
                    → valOf x mx ≡ Table.val A A x mx)
            (pairs-in : (x : CS.S) (mx : ⟨ fst x ∈ fst (AllCodes A) ⟩)
                      → ⟨ pr (fst x) (fst (valOf x mx)) ∈ fst Ts ⟩)
            (pairs-out : (p : V ℓ) → ⟨ p ∈ fst Ts ⟩
                       → ∥ Σ[ x ∈ CS.S ] Σ[ mx ∈ ⟨ fst x ∈ fst (AllCodes A) ⟩ ]
                            (p ≡ pr (fst x) (fst (valOf x mx))) ∥₁)
            (kc : KC (fst (lookup K γ)) (fst (lookup O γ)))
            (tags : Tags N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ)
            (wq : fst (lookup w γ) ≡ fst A)
            (dq : fst (lookup d γ) ≡ 𝒟ₒ (fst A))
            (wK : ⟨ fst (lookup w γ) ∈ fst (lookup K γ) ⟩)
            (CK : ⟨ fst (AllCodes A) ∈ fst (lookup K γ) ⟩)
            (TK : ⟨ fst Ts ∈ fst (lookup K γ) ⟩) where

  open Codes A

  Cs : CS.S
  Cs = AllCodes A

  E2 : CS.S ^ (2 + m)
  E2 = Ts ∷ Cs ∷ γ

  private
    Kv Ov Wv : V ℓ
    Kv = fst (lookup K γ)
    Ov = fst (lookup O γ)
    Wv = fst (lookup w γ)

    InK : V ℓ → Type (ℓ-suc ℓ)
    InK x = ⟨ x ∈ Kv ⟩

  module C = KC Kv Ov kc
  module Z = Chain Kv C.transK

  toS : ∀ {k} → Formula Ab k → Formula CS.S k
  toS = mapFo (asConst A)

  -- THE TIES.
  arityK : (N v : CS.S) → ⟨ fst v ∈ fst N ⟩ → InK (fst N) → InK (fst v)
  arityK N v h hN = C.transK (fst N) (fst v) hN h

  unK : (k : ℕ) (a : CS.S) → InK (fst a) → InK (fst (prʟ (numeralL k) a))
  unK k a ha = C.pairK (numeralL k) a (C.numK k) ha

  binK : (k : ℕ) (a b : CS.S) → InK (fst a) → InK (fst b)
       → InK (fst (prʟ (numeralL k) (prʟ a b)))
  binK k a b ha hb = C.pairK (numeralL k) (prʟ a b) (C.numK k) (C.pairK a b ha hb)

  carrierK : (u : CS.S) → ⟨ fst u ∈ Wv ⟩ → InK (fst u)
  carrierK u hu = C.transK Wv (fst u) wK hu

  tags2 : Tags {2 + m} (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
            (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11) E2
  tags2 = tagsCons _ _ _ _ _ _ _ _ _ _ _ _ (Cs ∷ γ) Ts
            (tagsCons _ _ _ _ _ _ _ _ _ _ _ _ γ Cs tags)

  -- The site-fact block of src/L/Condensation.lagda.md `KFacts`, as
  -- src/L/GCH/Level.lagda.md `DefRead.Body.facts` fills it.
  facts : KFacts {2 + m} (sh2 w) (sh2 K) (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3)
            (sh2 N4) (sh2 N5) (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11) E2
  facts = record
    { tagEq0 = tags2 .t0 ; tagEq1 = tags2 .t1 ; tagEq2 = tags2 .t2
    ; tagEq3 = tags2 .t3 ; tagEq4 = tags2 .t4 ; tagEq5 = tags2 .t5
    ; tagEq6 = tags2 .t6 ; tagEq7 = tags2 .t7 ; tagEq8 = tags2 .t8
    ; tagEq9 = tags2 .t9 ; tagEq10 = tags2 .t10 ; tagEq11 = tags2 .t11
    ; numK0 = C.numK 0 ; numK1 = C.numK 1 ; numK2 = C.numK 2 ; numK3 = C.numK 3
    ; numK4 = C.numK 4 ; numK5 = C.numK 5 ; numK6 = C.numK 6 ; numK7 = C.numK 7
    ; numK8 = C.numK 8 ; numK9 = C.numK 9 ; numK10 = C.numK 10 ; numK11 = C.numK 11
    ; innerK = unK
    ; innerPairK = binK
    ; pairK = C.pairK
    ; carrierK = carrierK
    ; arityK = arityK }

  cK : (c : CS.S) → ⟨ fst c ∈ fst Cs ⟩ → InK (fst c)
  cK c c∈ = C.transK (fst Cs) (fst c) CK c∈

  -- A code's arity is a numeral: the code is a key.
  arNum : (c ar t : CS.S) → ⟨ fst c ∈ fst Cs ⟩ → fst c ≡ pr (fst ar) (fst t)
        → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
  arNum c ar t c∈ e =
    PT.map (λ { (n , ψ , q) → n , sym (pr-inj (sym q ∙ e) .fst) }) (AllCodes-out A c c∈)

  binCodes : (k : ℕ) (c ar a b : CS.S) → ⟨ fst c ∈ fst Cs ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → InK (fst ar) × InK (fst a) × InK (fst b) × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
  binCodes k c ar a b c∈ e = arK , aK , bK , arNum c ar tS c∈ e
    where
    ck : InK (pr (fst ar) (pr (# k) (pr (fst a) (fst b))))
    ck = subst InK e (cK c c∈)
    arK : InK (fst ar)
    arK = Z.prK-fst (fst ar) (pr (# k) (pr (fst a) (fst b))) ck
    tK : InK (pr (# k) (pr (fst a) (fst b)))
    tK = Z.prK-snd (fst ar) (pr (# k) (pr (fst a) (fst b))) ck
    abK : InK (pr (fst a) (fst b))
    abK = Z.prK-snd (# k) (pr (fst a) (fst b)) tK
    aK : InK (fst a)
    aK = Z.prK-fst (fst a) (fst b) abK
    bK : InK (fst b)
    bK = Z.prK-snd (fst a) (fst b) abK
    tS : CS.S
    tS = down (lookup K γ) (pr (# k) (pr (fst a) (fst b))) tK

  unCodes : (k : ℕ) (c ar a : CS.S) → ⟨ fst c ∈ fst Cs ⟩
          → fst c ≡ pr (fst ar) (pr (# k) (fst a))
          → InK (fst ar) × InK (fst a) × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
  unCodes k c ar a c∈ e = arK , aK , arNum c ar tS c∈ e
    where
    ck : InK (pr (fst ar) (pr (# k) (fst a)))
    ck = subst InK e (cK c c∈)
    arK : InK (fst ar)
    arK = Z.prK-fst (fst ar) (pr (# k) (fst a)) ck
    tK : InK (pr (# k) (fst a))
    tK = Z.prK-snd (fst ar) (pr (# k) (fst a)) ck
    aK : InK (fst a)
    aK = Z.prK-snd (# k) (fst a) tK
    tS : CS.S
    tS = down (lookup K γ) (pr (# k) (fst a)) tK

  entryC : (x y : CS.S) → ⟨ pr (fst x) (fst y) ∈ fst Cs ⟩ → InK (fst x) × InK (fst y)
  entryC x y p = Z.fstK (fst Cs) (fst x) (fst y) CK p , Z.sndK (fst Cs) (fst x) (fst y) CK p

  entryT : (x y : CS.S) → ⟨ pr (fst x) (fst y) ∈ fst Ts ⟩ → InK (fst x) × InK (fst y)
  entryT x y p = Z.fstK (fst Ts) (fst x) (fst y) TK p , Z.sndK (fst Ts) (fst x) (fst y) TK p

  -- ROW 1.  CLOSED.
  module CA = ClosedAgree {2 + m} i1 (sh2 K) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
                (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11)
                (sh2 w) (sh2 N0) (sh2 N1) (sh2 N6) (sh2 N7) E2
                facts binCodes unCodes entryC

  closed : ⟨ E2 ⊨ closedBS i1 (sh2 K) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
                    (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11) ⟩
  closed = CA.out (Closure.closed A i1 E2 refl)

  -- ROW 2.  SHAPED.
  module SA = ShapedAgree {2 + m} i1 (sh2 w) (sh2 K)
                (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
                (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11) E2
                facts binCodes unCodes

  shaped : ⟨ E2 ⊨ shapedBS i1 (sh2 w) (sh2 K)
                    (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
                    (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11) ⟩
  shaped = SA.out (Closure.shaped A i1 (sh2 w) E2 refl wq)

  -- =================================================================
  -- ROWS 8 AND 9.  THE DEFINABLE POWERSET, BOTH POLARITIES.  A
  -- member of d is the definable subset of a formula ψ of arity one
  -- (src/L/Constructible.lagda.md `𝒟ₒ-inv`); its code is the key of
  -- ψ, in C, whose value in T is the satisfaction set of ψ
  -- (src/L/Coding/Uniform.lagda.md `val-at`), and that set cuts the
  -- subset out of the carrier (src/L/Coding/Bridge.lagda.md
  -- `defSet-Sat`).  The converse reads a code of arity one back into
  -- a formula and puts its definable subset into d.
  -- =================================================================

  private
    pr-in : ∀ {n'} (q u v : Fin n') (δ : CS.S ^ n')
          → fst (lookup q δ) ≡ pr (fst (lookup u δ)) (fst (lookup v δ))
          → ⟨ δ ⊨ prAtL q u v ⟩
    pr-in q u v δ e = subst ⟨_⟩ (sym (prAtL-adequate q u v δ)) e

    -- The value at a code that is the key of ψ is the satisfaction set of ψ.
    vq : (c : CS.S) (c∈ : ⟨ fst c ∈ fst Cs ⟩) {k : ℕ} (ψ : Formula Ab k)
       → fst c ≡ fst (keyS A ψ) → fst (valOf c c∈) ≡ fst (Sat A (toS ψ))
    vq c c∈ ψ q = cong fst (valOf≡ c c∈ ∙ val-at A A ψ c c∈ q)

    -- The machine's definable-subset condition, at an x that is the
    -- definable subset of ψ and a v that is its satisfaction set.  The
    -- mirror of src/L/GCH/Level.lagda.md `DefRead.defines-defSet`.
    definesAt : ∀ {n'} (δ : CS.S ^ n') (xi wi vi : Fin n')
              → fst (lookup wi δ) ≡ fst A
              → (ψ : Formula Ab 1)
              → fst (lookup xi δ) ≡ DefOf.defSet (fst A) ψ
              → fst (lookup vi δ) ≡ fst (Sat A (toS ψ))
              → ⟨ δ ⊨ DefinesAt xi wi vi ⟩
    definesAt δ xi wi vi qw ψ qx qv = DefinesAt-both xi wi vi δ fwd bwd
      where
      fwd : (z : CS.S) → ⟨ fst z ∈ fst (lookup xi δ) ⟩
          → ⟨ fst z ∈ fst (lookup wi δ) ⟩ × ⟨ envOne (fst z) ∈ fst (lookup vi δ) ⟩
      fwd z z∈ =
          subst (λ u → ⟨ fst z ∈ u ⟩) (sym qw) zA
        , subst (λ u → ⟨ envOne (fst z) ∈ u ⟩) (sym qv)
            (subst (λ u → ⟨ envOne u ∈ fst (Sat A (toS ψ)) ⟩) (fib .snd)
              (subst ⟨_⟩ (defSet-Sat A ψ (fib .fst))
                (subst (λ u → ⟨ u ∈ DefOf.defSet (fst A) ψ ⟩) (sym (fib .snd)) zD)))
        where
        zD : ⟨ fst z ∈ DefOf.defSet (fst A) ψ ⟩
        zD = subst (λ u → ⟨ fst z ∈ u ⟩) qx z∈
        zA : ⟨ fst z ∈ fst A ⟩
        zA = DefOf.defSet⊆A (fst A) ψ (fst z) zD
        fib : Σ[ q ∈ Ab ] (ι q ≡ fst z)
        fib = ∈-asFiber {a = fst z} {b = fst A} zA
      bwd : (z : CS.S)
          → ⟨ fst z ∈ fst (lookup wi δ) ⟩ × ⟨ envOne (fst z) ∈ fst (lookup vi δ) ⟩
          → ⟨ fst z ∈ fst (lookup xi δ) ⟩
      bwd z (zw , zv) = subst (λ u → ⟨ fst z ∈ u ⟩) (sym qx)
        (subst (λ u → ⟨ u ∈ DefOf.defSet (fst A) ψ ⟩) (fib .snd)
          (subst ⟨_⟩ (sym (defSet-Sat A ψ (fib .fst)))
            (subst (λ u → ⟨ envOne u ∈ fst (Sat A (toS ψ)) ⟩) (sym (fib .snd))
              (subst (λ u → ⟨ envOne (fst z) ∈ u ⟩) qv zv))))
        where
        zA : ⟨ fst z ∈ fst A ⟩
        zA = subst (λ u → ⟨ fst z ∈ u ⟩) qw zw
        fib : Σ[ q ∈ Ab ] (ι q ≡ fst z)
        fib = ∈-asFiber {a = fst z} {b = fst A} zA

    -- DefinesAt to DefinesBS at e0 ∷ e1 ∷ e2 ∷ E2, the carrier at w
    -- and the tag N0, with the ties src/L/Condensation.lagda.md
    -- `DefinesAgree` asks.
    module Def3 (e0 e1 e2 : CS.S) (xi vi : Fin (3 + (2 + m))) where
      module DfA = DefinesAgree {3 + (2 + m)} xi (sh3 (sh2 w)) vi (sh3 (sh2 K)) (sh3 (sh2 N0))
                     (e0 ∷ e1 ∷ e2 ∷ E2)
                     (tags .t0) (C.numK 0) C.pairK carrierK arityK
                     (λ z hz → carrierK z (hz .fst))

  mem : ⟨ E2 ⊨ memAt (sh2 d) (sh2 w) i1 i0 (sh2 K) (sh2 N0) (sh2 N1) ⟩
  mem x x∈d = PT.rec squash₁ byψ
    (𝒟ₒ-inv (fst A) (fst x) (subst (λ u → ⟨ fst x ∈ u ⟩) dq x∈d))
    where
    Goal : Type (ℓ-suc ℓ)
    Goal = ⟨ (x ∷ E2) ⊨ ∃̇∈ (var (sh1 i1)) (∃̇∈ (var (sh2 (sh2 K)))
              ( keyArBS i1 (sh3 (sh2 N1)) (sh3 (sh2 K))
              ∧̇ ( appAt (sh3 i0) i1 i0
                ∧̇ DefinesBS i2 (sh3 (sh2 w)) i0 (sh3 (sh2 K)) (sh3 (sh2 N0)) ))) ⟩
    byψ : Σ[ ψ ∈ Formula Ab 1 ] (DefOf.defSet (fst A) ψ ≡ fst x) → Goal
    byψ (ψ , qx) = ∣ c , ( c∈ , ∣ v , ( vK , ( hk , ( ha , hD ))) ∣₁ ) ∣₁
      where
      c : CS.S
      c = keyS A ψ
      c∈ : ⟨ fst c ∈ fst Cs ⟩
      c∈ = key∈AllCodes A ψ
      v : CS.S
      v = valOf c c∈
      vK : InK (fst v)
      vK = Z.sndK (fst Ts) (fst c) (fst v) TK (pairs-in c c∈)
      tK : InK (cd ψ)
      tK = Z.prK-snd (# 1) (cd ψ) (cK c c∈)
      hk : ⟨ (v ∷ c ∷ x ∷ E2) ⊨ keyArBS i1 (sh3 (sh2 N1)) (sh3 (sh2 K)) ⟩
      hk = ∣ cdS ψ , ( tK , ∣ numeralL 1 , ( C.numK 1 , ( sym (tags .t1) , hp )) ∣₁ ) ∣₁
        where
        hp : ⟨ (numeralL 1 ∷ cdS ψ ∷ v ∷ c ∷ x ∷ E2) ⊨ prAtL (suc (suc i1)) zero (suc zero) ⟩
        hp = pr-in (suc (suc i1)) zero (suc zero) (numeralL 1 ∷ cdS ψ ∷ v ∷ c ∷ x ∷ E2)
               (cong (λ u → pr u (cd ψ)) (sym (numeralL-fst 1)))
      ha : ⟨ (v ∷ c ∷ x ∷ E2) ⊨ appAt (sh3 i0) i1 i0 ⟩
      ha = app-in (sh3 i0) i1 i0 (v ∷ c ∷ x ∷ E2) (pairs-in c c∈)
      hD : ⟨ (v ∷ c ∷ x ∷ E2) ⊨ DefinesBS i2 (sh3 (sh2 w)) i0 (sh3 (sh2 K)) (sh3 (sh2 N0)) ⟩
      hD = Def3.DfA.out v c x i2 i0
             (definesAt (v ∷ c ∷ x ∷ E2) i2 (sh3 (sh2 w)) i0 wq ψ (sym qx) (vq c c∈ ψ refl))

  all : ⟨ E2 ⊨ allAt (sh2 d) (sh2 w) i1 i0 (sh2 K) (sh2 N0) (sh2 N1) ⟩
  all c c∈ hk = PT.rec squash₁ byT hk
    where
    Goal : Type (ℓ-suc ℓ)
    Goal = ⟨ (c ∷ E2) ⊨ ∃̇∈ (var (sh1 (sh2 K)))
              ( appAt (sh2 i0) i1 i0
              ∧̇ ∃̇∈ (var (sh2 (sh2 d))) (DefinesBS i0 (sh3 (sh2 w)) i1 (sh3 (sh2 K)) (sh3 (sh2 N0))) ) ⟩
    byT : Σ[ t ∈ CS.S ] (InK (fst t)
            × ⟨ (t ∷ c ∷ E2) ⊨ ∃̇∈ (var (suc (sh1 (sh2 K))))
                ((var zero ≐ var (suc (suc (sh1 (sh2 N1)))))
                 ∧̇ prAtL (suc (suc i0)) zero (suc zero)) ⟩)
        → Goal
    byT (t , (tK , har)) = PT.rec squash₁ byAr har
      where
      byAr : Σ[ ar ∈ CS.S ] (InK (fst ar)
               × ⟨ (ar ∷ t ∷ c ∷ E2) ⊨
                   ((var zero ≐ var (suc (suc (sh1 (sh2 N1)))))
                    ∧̇ prAtL (suc (suc i0)) zero (suc zero)) ⟩)
           → Goal
      byAr (ar , (arK , (ae , ap))) = PT.rec squash₁ byψ (AllCodes-out A c c∈)
        where
        ceq : fst c ≡ pr (# 1) (fst t)
        ceq = pr-out (suc (suc i0)) zero (suc zero) (ar ∷ t ∷ c ∷ E2) ap
            ∙ cong (λ u → pr u (fst t)) (ae ∙ tags .t1 ∙ numeralL-fst 1)
        byψ : Σ[ n ∈ ℕ ] Σ[ ψ ∈ Formula Ab n ] (fst c ≡ fst (keyS A ψ)) → Goal
        byψ (n , ψ , q) = ∣ v , ( vK , ( ha , ∣ xS , ( x∈d , hD ) ∣₁ )) ∣₁
          where
          n≡1 : n ≡ 1
          n≡1 = #-inj′ (pr-inj (sym q ∙ ceq) .fst)
          ψ' : Formula Ab 1
          ψ' = subst (Formula Ab) n≡1 ψ
          q' : fst c ≡ fst (keyS A ψ')
          q' = q ∙ cong₂ pr (cong #_ n≡1) (sym (cd-subst n≡1 ψ))
          v : CS.S
          v = valOf c c∈
          vK : InK (fst v)
          vK = Z.sndK (fst Ts) (fst c) (fst v) TK (pairs-in c c∈)
          ha : ⟨ (v ∷ c ∷ E2) ⊨ appAt (sh2 i0) i1 i0 ⟩
          ha = app-in (sh2 i0) i1 i0 (v ∷ c ∷ E2) (pairs-in c c∈)
          xV : V ℓ
          xV = DefOf.defSet (fst A) ψ'
          x∈d : ⟨ xV ∈ fst (lookup d γ) ⟩
          x∈d = subst (λ u → ⟨ xV ∈ u ⟩) (sym dq) (𝒟ₒ-intro (fst A) xV ∣ ψ' , refl ∣₁)
          xS : CS.S
          xS = down (lookup d γ) xV x∈d
          hD : ⟨ (xS ∷ v ∷ c ∷ E2) ⊨ DefinesBS i0 (sh3 (sh2 w)) i1 (sh3 (sh2 K)) (sh3 (sh2 N0)) ⟩
          hD = Def3.DfA.out xS v c i0 i1
                 (definesAt (xS ∷ v ∷ c ∷ E2) i0 (sh3 (sh2 w)) i1 wq ψ' refl (vq c c∈ ψ' q'))
```

```agda
  -- =================================================================
  -- ROW 4.  CLOSED UNDER THE CODE-FORMING OPERATIONS.  Each clause of
  -- src/L/GCH/Level.lagda.md `Close` hands over the parts of a code in
  -- K and O; the parts are read back into formulas over the alphabet
  -- (a code in C is a key, a term code is the code of a term, an arity
  -- in O is a numeral), the constructor is applied, and its key is the
  -- code the clause asks for, in C by `key∈AllCodes`.
  -- =================================================================

  private
    i7 : ∀ {j} → Fin (suc (suc (suc (suc (suc (suc (suc (suc j))))))))
    i7 = suc i6
    sh9 : ∀ {j} → Fin j → Fin (9 + j)
    sh9 i = suc (sh8 i)

    numOf : (ar : CS.S) → ⟨ fst ar ∈ Ov ⟩ → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
    numOf ar h = PT.map (λ { (k , q) → k , q ∙ numeralL-fst k }) (C.O-num (fst ar) h)

    nK : (Ni : Fin m) (k : ℕ) → fst (lookup Ni γ) ≡ fst (numeralL k) → InK (fst (lookup Ni γ))
    nK Ni k e = subst InK (sym e) (C.numK k)

    -- A term code over the carrier at a numeral arity, read
    -- (src/L/GCH/Level.lagda.md `tmAt`): a constant of the carrier,
    -- or a variable index below the arity.
    tmAt-out : ∀ {n'} (δ : CS.S ^ n') (s ar wi Ki N0i N1i : Fin n') (k : ℕ)
             → fst (lookup ar δ) ≡ # k → fst (lookup wi δ) ≡ fst A
             → fst (lookup N0i δ) ≡ fst (numeralL 0) → fst (lookup N1i δ) ≡ fst (numeralL 1)
             → ⟨ δ ⊨ tmAt s ar wi Ki N0i N1i ⟩ → ∥ TmWit ι k (fst (lookup s δ)) ∥₁
    tmAt-out δ s ar wi Ki N0i N1i k qar qw q0 q1 =
      PT.rec squash₁ (λ { (inl h) → byCon h ; (inr h) → byVar h })
      where
      T : V ℓ
      T = fst (lookup s δ)
      byCon : ⟨ δ ⊨ ∃̇∈ (var wi) (tagBS (sh1 s) (sh1 N0i) i0 (sh1 Ki)) ⟩ → ∥ TmWit ι k T ∥₁
      byCon = PT.rec squash₁ (λ { (x , (x∈ , ht)) → PT.rec squash₁ (λ { (nt , (_ , (te , hp))) →
        let fib = ∈-asFiber {a = fst x} {b = fst A} (subst (λ u → ⟨ fst x ∈ u ⟩) qw x∈)
            e : T ≡ pr (fst nt) (fst x)
            e = pr-out (suc (suc s)) zero (suc zero) (nt ∷ x ∷ δ) hp
        in ∣ con (fib .fst)
           , ( cong₂ pr (sym (te ∙ q0 ∙ numeralL-fst 0)) (fib .snd) ∙ sym e ) ∣₁ }) ht })
      byVar : ⟨ δ ⊨ ∃̇∈ (var ar) (tagBS (sh1 s) (sh1 N1i) i0 (sh1 Ki)) ⟩ → ∥ TmWit ι k T ∥₁
      byVar = PT.rec squash₁ (λ { (i , (i∈ , ht)) → PT.rec squash₁ (λ { (nt , (_ , (te , hp))) →
        let e : T ≡ pr (# 1) (fst i)
            e = pr-out (suc (suc s)) zero (suc zero) (nt ∷ i ∷ δ) hp
              ∙ cong (λ u → pr u (fst i)) (te ∙ q1 ∙ numeralL-fst 1)
        in PT.map (λ { (j , (j<k , ez)) → varWit j j<k (fst i) T ez e })
             (∈#-elim k (fst i) (subst (λ u → ⟨ fst i ∈ u ⟩) qar i∈)) }) ht })

    module Cl = Close {2 + m} i1 (sh2 O) (sh2 w) (sh2 K)
                  (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
                  (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11)

    -- THE SIX CLAUSE SHAPES, each generic in its constructor.
    atom : (k : ℕ) (Ni : Fin m) (op : ∀ {j} → Term Ab j → Term Ab j → Formula Ab j)
         → (∀ {j} (t u : Term Ab j) → cd (op t u) ≡ pr (# k) (pr (ct t) (ct u)))
         → fst (lookup Ni γ) ≡ fst (numeralL k)
         → ⟨ E2 ⊨ Cl.atomAt (sh2 Ni) ⟩
    atom k Ni op pay te ar ar∈O t tK u uK (ht , hu) =
      PT.rec squash₁ (λ { (n , qar) →
        PT.rec squash₁ (λ { (tm , et) →
          PT.rec squash₁ (λ { (um , eu) → at n qar tm et um eu })
            (tmAt-out δ₃ i0 i2 (sh3 (sh2 w)) (sh3 (sh2 K)) (sh3 (sh2 N0)) (sh3 (sh2 N1))
               n qar wq (tags .t0) (tags .t1) hu) })
          (tmAt-out δ₃ i1 i2 (sh3 (sh2 w)) (sh3 (sh2 K)) (sh3 (sh2 N0)) (sh3 (sh2 N1))
             n qar wq (tags .t0) (tags .t1) ht) })
        (numOf ar ar∈O)
      where
      δ₃ : CS.S ^ (3 + (2 + m))
      δ₃ = u ∷ t ∷ ar ∷ E2
      NS : CS.S
      NS = lookup Ni γ
      Goal : Type (ℓ-suc ℓ)
      Goal = ⟨ δ₃ ⊨ ∃̇∈ (var (sh3 i1)) (∃̇∈ (var (sh4 (sh2 K))) (∃̇∈ (var (sh5 (sh2 K)))
                ( prAtL i1 i4 i3 ∧̇ ( prAtL i0 (sh6 (sh2 Ni)) i1 ∧̇ prAtL i2 i5 i0 )))) ⟩
      at : (n : ℕ) → fst ar ≡ # n → (tm : Term Ab n) → ct tm ≡ fst t
         → (um : Term Ab n) → ct um ≡ fst u → Goal
      at n qar tm et um eu =
        ∣ c , ( keyC ψ (fst c) refl , ∣ q , ( qK , ∣ s , ( sK , ( e1 , ( e2 , e3 ))) ∣₁ ) ∣₁ ) ∣₁
        where
        ψ : Formula Ab n
        ψ = op tm um
        c : CS.S
        c = keyS A ψ
        q : CS.S
        q = prʟ t u
        qK : InK (fst q)
        qK = C.pairK t u tK uK
        s : CS.S
        s = prʟ NS q
        sK : InK (fst s)
        sK = C.pairK NS q (nK Ni k te) qK
        e1 : ⟨ (s ∷ q ∷ c ∷ δ₃) ⊨ prAtL i1 i4 i3 ⟩
        e1 = pr-in i1 i4 i3 (s ∷ q ∷ c ∷ δ₃) (prʟ-fst t u)
        e2 : ⟨ (s ∷ q ∷ c ∷ δ₃) ⊨ prAtL i0 (sh6 (sh2 Ni)) i1 ⟩
        e2 = pr-in i0 (sh6 (sh2 Ni)) i1 (s ∷ q ∷ c ∷ δ₃) (prʟ-fst NS q)
        e3 : ⟨ (s ∷ q ∷ c ∷ δ₃) ⊨ prAtL i2 i5 i0 ⟩
        e3 = pr-in i2 i5 i0 (s ∷ q ∷ c ∷ δ₃)
               ( cong (pr (# n)) (pay tm um)
               ∙ cong₂ pr (sym qar)
                   ( cong₂ pr (sym (te ∙ numeralL-fst k)) (cong₂ pr et eu ∙ sym (prʟ-fst t u))
                   ∙ sym (prʟ-fst NS q) ) )

    bin : (k : ℕ) (Ni : Fin m) (op : ∀ {j} → Formula Ab j → Formula Ab j → Formula Ab j)
        → (∀ {j} (a b : Formula Ab j) → cd (op a b) ≡ pr (# k) (pr (cd a) (cd b)))
        → fst (lookup Ni γ) ≡ fst (numeralL k)
        → ⟨ E2 ⊨ Cl.binAt (sh2 Ni) ⟩
    bin k Ni op pay te c₁ c₁∈ c₂ c₂∈ ar ar∈O a aK b bK (h1 , h2) =
      PT.rec squash₁ (λ { (n₁ , ψ₁ , q₁) →
        PT.rec squash₁ (λ { (n₂ , ψ₂ , q₂) → at n₁ ψ₁ q₁ n₂ ψ₂ q₂ }) (AllCodes-out A c₂ c₂∈) })
        (AllCodes-out A c₁ c₁∈)
      where
      δ₅ : CS.S ^ (5 + (2 + m))
      δ₅ = b ∷ a ∷ ar ∷ c₂ ∷ c₁ ∷ E2
      NS : CS.S
      NS = lookup Ni γ
      e₁ : fst c₁ ≡ pr (fst ar) (fst a)
      e₁ = pr-out i4 i2 i1 δ₅ h1
      e₂ : fst c₂ ≡ pr (fst ar) (fst b)
      e₂ = pr-out i3 i2 i0 δ₅ h2
      Goal : Type (ℓ-suc ℓ)
      Goal = ⟨ δ₅ ⊨ ∃̇∈ (var (sh5 i1)) (∃̇∈ (var (sh6 (sh2 K))) (∃̇∈ (var (suc (sh6 (sh2 K))))
                ( prAtL i1 i4 i3 ∧̇ ( prAtL i0 (sh8 (sh2 Ni)) i1 ∧̇ prAtL i2 i5 i0 )))) ⟩
      at : (n₁ : ℕ) (ψ₁ : Formula Ab n₁) → fst c₁ ≡ fst (keyS A ψ₁)
         → (n₂ : ℕ) (ψ₂ : Formula Ab n₂) → fst c₂ ≡ fst (keyS A ψ₂) → Goal
      at n₁ ψ₁ q₁ n₂ ψ₂ q₂ =
        ∣ c , ( keyC ψ (fst c) refl , ∣ q , ( qK , ∣ s , ( sK , ( e1 , ( e2 , e3 ))) ∣₁ ) ∣₁ ) ∣₁
        where
        ar₁ : fst ar ≡ # n₁
        ar₁ = sym (pr-inj (sym q₁ ∙ e₁) .fst)
        qa : cd ψ₁ ≡ fst a
        qa = pr-inj (sym q₁ ∙ e₁) .snd
        ar₂ : fst ar ≡ # n₂
        ar₂ = sym (pr-inj (sym q₂ ∙ e₂) .fst)
        qb : cd ψ₂ ≡ fst b
        qb = pr-inj (sym q₂ ∙ e₂) .snd
        n≡ : n₂ ≡ n₁
        n≡ = #-inj′ (sym ar₂ ∙ ar₁)
        ψ₂' : Formula Ab n₁
        ψ₂' = subst (Formula Ab) n≡ ψ₂
        ψ : Formula Ab n₁
        ψ = op ψ₁ ψ₂'
        c : CS.S
        c = keyS A ψ
        q : CS.S
        q = prʟ a b
        qK : InK (fst q)
        qK = C.pairK a b aK bK
        s : CS.S
        s = prʟ NS q
        sK : InK (fst s)
        sK = C.pairK NS q (nK Ni k te) qK
        e1 : ⟨ (s ∷ q ∷ c ∷ δ₅) ⊨ prAtL i1 i4 i3 ⟩
        e1 = pr-in i1 i4 i3 (s ∷ q ∷ c ∷ δ₅) (prʟ-fst a b)
        e2 : ⟨ (s ∷ q ∷ c ∷ δ₅) ⊨ prAtL i0 (sh8 (sh2 Ni)) i1 ⟩
        e2 = pr-in i0 (sh8 (sh2 Ni)) i1 (s ∷ q ∷ c ∷ δ₅) (prʟ-fst NS q)
        e3 : ⟨ (s ∷ q ∷ c ∷ δ₅) ⊨ prAtL i2 i5 i0 ⟩
        e3 = pr-in i2 i5 i0 (s ∷ q ∷ c ∷ δ₅)
               ( cong (pr (# n₁)) (pay ψ₁ ψ₂')
               ∙ cong₂ pr (sym ar₁)
                   ( cong₂ pr (sym (te ∙ numeralL-fst k))
                       (cong₂ pr qa (cd-subst n≡ ψ₂ ∙ qb) ∙ sym (prʟ-fst a b))
                   ∙ sym (prʟ-fst NS q) ) )

    un : (k : ℕ) (Ni : Fin m) (op : ∀ {j} → Formula Ab j → Formula Ab j)
       → (∀ {j} (a : Formula Ab j) → cd (op a) ≡ pr (# k) (cd a))
       → fst (lookup Ni γ) ≡ fst (numeralL k)
       → ⟨ E2 ⊨ Cl.unAt (sh2 Ni) ⟩
    un k Ni op pay te c₁ c₁∈ ar ar∈O a aK h = PT.rec squash₁ at (AllCodes-out A c₁ c₁∈)
      where
      δ₃ : CS.S ^ (3 + (2 + m))
      δ₃ = a ∷ ar ∷ c₁ ∷ E2
      NS : CS.S
      NS = lookup Ni γ
      e₁ : fst c₁ ≡ pr (fst ar) (fst a)
      e₁ = pr-out i2 i1 i0 δ₃ h
      Goal : Type (ℓ-suc ℓ)
      Goal = ⟨ δ₃ ⊨ ∃̇∈ (var (sh3 i1)) (∃̇∈ (var (sh4 (sh2 K)))
                ( prAtL i0 (sh5 (sh2 Ni)) i2 ∧̇ prAtL i1 i3 i0 )) ⟩
      at : Σ[ n₁ ∈ ℕ ] Σ[ ψ₁ ∈ Formula Ab n₁ ] (fst c₁ ≡ fst (keyS A ψ₁)) → Goal
      at (n₁ , ψ₁ , q₁) = ∣ c , ( keyC ψ (fst c) refl , ∣ s , ( sK , ( e1 , e2 )) ∣₁ ) ∣₁
        where
        ar₁ : fst ar ≡ # n₁
        ar₁ = sym (pr-inj (sym q₁ ∙ e₁) .fst)
        qa : cd ψ₁ ≡ fst a
        qa = pr-inj (sym q₁ ∙ e₁) .snd
        ψ : Formula Ab n₁
        ψ = op ψ₁
        c : CS.S
        c = keyS A ψ
        s : CS.S
        s = prʟ NS a
        sK : InK (fst s)
        sK = C.pairK NS a (nK Ni k te) aK
        e1 : ⟨ (s ∷ c ∷ δ₃) ⊨ prAtL i0 (sh5 (sh2 Ni)) i2 ⟩
        e1 = pr-in i0 (sh5 (sh2 Ni)) i2 (s ∷ c ∷ δ₃) (prʟ-fst NS a)
        e2 : ⟨ (s ∷ c ∷ δ₃) ⊨ prAtL i1 i3 i0 ⟩
        e2 = pr-in i1 i3 i0 (s ∷ c ∷ δ₃)
               ( cong (pr (# n₁)) (pay ψ₁)
               ∙ cong₂ pr (sym ar₁)
                   (cong₂ pr (sym (te ∙ numeralL-fst k)) qa ∙ sym (prʟ-fst NS a)) )

    con' : (k : ℕ) (Ni : Fin m) (c₀ : ∀ {j} → Formula Ab j)
         → (∀ {j} → cd (c₀ {j}) ≡ pr (# k) (# 0))
         → fst (lookup Ni γ) ≡ fst (numeralL k)
         → ⟨ E2 ⊨ Cl.conAt (sh2 Ni) ⟩
    con' k Ni c₀ pay te ar ar∈O = PT.rec squash₁ at (numOf ar ar∈O)
      where
      δ₁ : CS.S ^ (1 + (2 + m))
      δ₁ = ar ∷ E2
      NS N0S : CS.S
      NS = lookup Ni γ
      N0S = lookup N0 γ
      Goal : Type (ℓ-suc ℓ)
      Goal = ⟨ δ₁ ⊨ ∃̇∈ (var (sh1 i1)) (∃̇∈ (var (sh2 (sh2 K)))
                ( prAtL i0 (sh3 (sh2 Ni)) (sh3 (sh2 N0)) ∧̇ prAtL i1 i2 i0 )) ⟩
      at : Σ[ n ∈ ℕ ] (fst ar ≡ # n) → Goal
      at (n , qar) = ∣ c , ( keyC ψ (fst c) refl , ∣ s , ( sK , ( e1 , e2 )) ∣₁ ) ∣₁
        where
        ψ : Formula Ab n
        ψ = c₀ {n}
        c : CS.S
        c = keyS A ψ
        s : CS.S
        s = prʟ NS N0S
        sK : InK (fst s)
        sK = C.pairK NS N0S (nK Ni k te) (nK N0 0 (tags .t0))
        e1 : ⟨ (s ∷ c ∷ δ₁) ⊨ prAtL i0 (sh3 (sh2 Ni)) (sh3 (sh2 N0)) ⟩
        e1 = pr-in i0 (sh3 (sh2 Ni)) (sh3 (sh2 N0)) (s ∷ c ∷ δ₁) (prʟ-fst NS N0S)
        e2 : ⟨ (s ∷ c ∷ δ₁) ⊨ prAtL i1 i2 i0 ⟩
        e2 = pr-in i1 i2 i0 (s ∷ c ∷ δ₁)
               ( cong (pr (# n)) (pay {n})
               ∙ cong₂ pr (sym qar)
                   ( cong₂ pr (sym (te ∙ numeralL-fst k)) (sym (tags .t0 ∙ numeralL-fst 0))
                   ∙ sym (prʟ-fst NS N0S) ) )

    qu : (k : ℕ) (Ni : Fin m) (op : ∀ {j} → Formula Ab (suc j) → Formula Ab j)
       → (∀ {j} (a : Formula Ab (suc j)) → cd (op a) ≡ pr (# k) (cd a))
       → fst (lookup Ni γ) ≡ fst (numeralL k)
       → ⟨ E2 ⊨ Cl.quAt (sh2 Ni) ⟩
    qu k Ni op pay te c₁ c₁∈ ar ar∈O ar' ar'K a aK (h1 , h2) =
      PT.rec squash₁ (λ { (n , qar) → PT.rec squash₁ (at n qar) (AllCodes-out A c₁ c₁∈) })
        (numOf ar ar∈O)
      where
      δ₄ : CS.S ^ (4 + (2 + m))
      δ₄ = a ∷ ar' ∷ ar ∷ c₁ ∷ E2
      NS : CS.S
      NS = lookup Ni γ
      e₁ : fst c₁ ≡ pr (fst ar') (fst a)
      e₁ = pr-out i3 i1 i0 δ₄ h1
      e₂ : fst ar' ≡ sucV (fst ar)
      e₂ = suc-out i2 i1 δ₄ h2
      Goal : Type (ℓ-suc ℓ)
      Goal = ⟨ δ₄ ⊨ ∃̇∈ (var (sh4 i1)) (∃̇∈ (var (sh5 (sh2 K)))
                ( prAtL i0 (sh6 (sh2 Ni)) i2 ∧̇ prAtL i1 i4 i0 )) ⟩
      at : (n : ℕ) → fst ar ≡ # n
         → Σ[ n₁ ∈ ℕ ] Σ[ ψ₁ ∈ Formula Ab n₁ ] (fst c₁ ≡ fst (keyS A ψ₁)) → Goal
      at n qar (n₁ , ψ₁ , q₁) = ∣ c , ( keyC ψ (fst c) refl , ∣ s , ( sK , ( e1 , e2 )) ∣₁ ) ∣₁
        where
        ar₁ : fst ar' ≡ # n₁
        ar₁ = sym (pr-inj (sym q₁ ∙ e₁) .fst)
        qa : cd ψ₁ ≡ fst a
        qa = pr-inj (sym q₁ ∙ e₁) .snd
        n≡ : n₁ ≡ suc n
        n≡ = #-inj′ (sym ar₁ ∙ e₂ ∙ cong sucV qar)
        ψ₁' : Formula Ab (suc n)
        ψ₁' = subst (Formula Ab) n≡ ψ₁
        ψ : Formula Ab n
        ψ = op ψ₁'
        c : CS.S
        c = keyS A ψ
        s : CS.S
        s = prʟ NS a
        sK : InK (fst s)
        sK = C.pairK NS a (nK Ni k te) aK
        e1 : ⟨ (s ∷ c ∷ δ₄) ⊨ prAtL i0 (sh6 (sh2 Ni)) i2 ⟩
        e1 = pr-in i0 (sh6 (sh2 Ni)) i2 (s ∷ c ∷ δ₄) (prʟ-fst NS a)
        e2 : ⟨ (s ∷ c ∷ δ₄) ⊨ prAtL i1 i4 i0 ⟩
        e2 = pr-in i1 i4 i0 (s ∷ c ∷ δ₄)
               ( cong (pr (# n)) (pay ψ₁')
               ∙ cong₂ pr (sym qar)
                   ( cong₂ pr (sym (te ∙ numeralL-fst k)) (cd-subst n≡ ψ₁ ∙ qa)
                   ∙ sym (prʟ-fst NS a) ) )

    bq : (k : ℕ) (Ni : Fin m) (op : ∀ {j} → Term Ab j → Formula Ab (suc j) → Formula Ab j)
       → (∀ {j} (t : Term Ab j) (a : Formula Ab (suc j)) → cd (op t a) ≡ pr (# k) (pr (ct t) (cd a)))
       → fst (lookup Ni γ) ≡ fst (numeralL k)
       → ⟨ E2 ⊨ Cl.bqAt (sh2 Ni) ⟩
    bq k Ni op pay te c₁ c₁∈ ar ar∈O ar' ar'K t tK a aK (ht , (h1 , h2)) =
      PT.rec squash₁ (λ { (n , qar) →
        PT.rec squash₁ (λ { (tm , et) → PT.rec squash₁ (at n qar tm et) (AllCodes-out A c₁ c₁∈) })
          (tmAt-out δ₅ i1 i3 (sh5 (sh2 w)) (sh5 (sh2 K)) (sh5 (sh2 N0)) (sh5 (sh2 N1))
             n qar wq (tags .t0) (tags .t1) ht) })
        (numOf ar ar∈O)
      where
      δ₅ : CS.S ^ (5 + (2 + m))
      δ₅ = a ∷ t ∷ ar' ∷ ar ∷ c₁ ∷ E2
      NS : CS.S
      NS = lookup Ni γ
      e₁ : fst c₁ ≡ pr (fst ar') (fst a)
      e₁ = pr-out i4 i2 i0 δ₅ h1
      e₂ : fst ar' ≡ sucV (fst ar)
      e₂ = suc-out i3 i2 δ₅ h2
      Goal : Type (ℓ-suc ℓ)
      Goal = ⟨ δ₅ ⊨ ∃̇∈ (var (sh5 i1)) (∃̇∈ (var (sh6 (sh2 K))) (∃̇∈ (var (suc (sh6 (sh2 K))))
                ( prAtL i1 i4 i3 ∧̇ ( prAtL i0 (sh8 (sh2 Ni)) i1 ∧̇ prAtL i2 i6 i0 )))) ⟩
      at : (n : ℕ) → fst ar ≡ # n → (tm : Term Ab n) → ct tm ≡ fst t
         → Σ[ n₁ ∈ ℕ ] Σ[ ψ₁ ∈ Formula Ab n₁ ] (fst c₁ ≡ fst (keyS A ψ₁)) → Goal
      at n qar tm et (n₁ , ψ₁ , q₁) =
        ∣ c , ( keyC ψ (fst c) refl , ∣ q , ( qK , ∣ s , ( sK , ( e1 , ( e2 , e3 ))) ∣₁ ) ∣₁ ) ∣₁
        where
        ar₁ : fst ar' ≡ # n₁
        ar₁ = sym (pr-inj (sym q₁ ∙ e₁) .fst)
        qa : cd ψ₁ ≡ fst a
        qa = pr-inj (sym q₁ ∙ e₁) .snd
        n≡ : n₁ ≡ suc n
        n≡ = #-inj′ (sym ar₁ ∙ e₂ ∙ cong sucV qar)
        ψ₁' : Formula Ab (suc n)
        ψ₁' = subst (Formula Ab) n≡ ψ₁
        ψ : Formula Ab n
        ψ = op tm ψ₁'
        c : CS.S
        c = keyS A ψ
        q : CS.S
        q = prʟ t a
        qK : InK (fst q)
        qK = C.pairK t a tK aK
        s : CS.S
        s = prʟ NS q
        sK : InK (fst s)
        sK = C.pairK NS q (nK Ni k te) qK
        e1 : ⟨ (s ∷ q ∷ c ∷ δ₅) ⊨ prAtL i1 i4 i3 ⟩
        e1 = pr-in i1 i4 i3 (s ∷ q ∷ c ∷ δ₅) (prʟ-fst t a)
        e2 : ⟨ (s ∷ q ∷ c ∷ δ₅) ⊨ prAtL i0 (sh8 (sh2 Ni)) i1 ⟩
        e2 = pr-in i0 (sh8 (sh2 Ni)) i1 (s ∷ q ∷ c ∷ δ₅) (prʟ-fst NS q)
        e3 : ⟨ (s ∷ q ∷ c ∷ δ₅) ⊨ prAtL i2 i6 i0 ⟩
        e3 = pr-in i2 i6 i0 (s ∷ q ∷ c ∷ δ₅)
               ( cong (pr (# n)) (pay tm ψ₁')
               ∙ cong₂ pr (sym qar)
                   ( cong₂ pr (sym (te ∙ numeralL-fst k))
                       (cong₂ pr et (cd-subst n≡ ψ₁ ∙ qa) ∙ sym (prʟ-fst t a))
                   ∙ sym (prʟ-fst NS q) ) )

  closeR : ⟨ E2 ⊨ Cl.closeAt ⟩
  closeR =
      atom 0 N0 _∈̇_ (λ _ _ → refl) (tags .t0)
    , ( atom 1 N1 _≐_ (λ _ _ → refl) (tags .t1)
    , ( bin 2 N2 _∧̇_ (λ _ _ → refl) (tags .t2)
    , ( bin 3 N3 _∨̇_ (λ _ _ → refl) (tags .t3)
    , ( bin 4 N4 _⇒̇_ (λ _ _ → refl) (tags .t4)
    , ( un 5 N5 ¬̇_ (λ _ → refl) (tags .t5)
    , ( con' 6 N6 ⊤̇ refl (tags .t6)
    , ( con' 7 N7 ⊥̇ refl (tags .t7)
    , ( qu 8 N8 ∃̇_ (λ _ → refl) (tags .t8)
    , ( qu 9 N9 ∀̇_ (λ _ → refl) (tags .t9)
    , ( bq 10 N10 ∀̇∈ (λ _ _ → refl) (tags .t10)
    , bq 11 N11 ∃̇∈ (λ _ _ → refl) (tags .t11) ))))))))))

  -- =================================================================
  -- ROW 7.  THE TWELVE SATISFACTION ROWS.  The class-level clauses of
  -- Section 3 at T ∷ C ∷ γ, carried to their bounded rows.  The ties
  -- are the ones src/L/GCH/Level.lagda.md `DefRead.Body` supplies for
  -- the other direction: the code-set ties from the pair chain, the
  -- environment ties from the tower.  Bot, Top, Neg and Imp take
  -- src/L/Condensation.lagda.md's agreement whole; Mem, Eq, Forall,
  -- Exist, AllIn and ExIn take its machine-to-story body with the
  -- re-tied leaves of src/L/GCH/LevelRows.lagda.md (the untied leaves
  -- ask a value in K of an arbitrary set); And and Or are read
  -- straight off the table, since their agreement binds an
  -- environment set at an arbitrary arity that nothing supplies.
  -- =================================================================

  module Twelve (Ês : CS.S) (ÊK : InK (fst Ês))
                (htow : ⟨ (Ês ∷ E2) ⊨ towerAt i0 (sh3 O) (sh3 w) (sh3 K) ⟩) where

    module US = UniformSound A Ts valOf valOf≡ pairs-out E2 i1 i0 (sh2 w) refl refl wq
    module Tw = Tower {3 + m} i0 (sh3 O) (sh3 w) (sh3 K) (Ês ∷ E2) kc ÊK htow

    private
      t0K : InK (fst (lookup (sh2 N0) E2))
      t0K = subst InK (sym (tags .t0)) (C.numK 0)

      -- A recorded value lies in K.
      valK-un' : (k : ℕ) (c ar a yc : CS.S) → ⟨ fst c ∈ fst Cs ⟩
               → fst c ≡ pr (fst ar) (pr (# k) (fst a))
               → ⟨ pr (fst c) (fst yc) ∈ fst Ts ⟩ → InK (fst yc)
      valK-un' k c ar a yc _ _ hc = Z.sndK (fst Ts) (fst c) (fst yc) TK hc

      valK-bin : (k : ℕ) (c ar a b yc : CS.S) → ⟨ fst c ∈ fst Cs ⟩
               → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
               → ⟨ pr (fst c) (fst yc) ∈ fst Ts ⟩ → InK (fst yc)
      valK-bin k c ar a b yc _ _ hc = Z.sndK (fst Ts) (fst c) (fst yc) TK hc

      -- A subvalue lies in K.
      subK-of : ∀ {n'} (T' ar a y : Fin n') (δ : CS.S ^ n')
              → fst (lookup T' δ) ≡ fst Ts
              → ⟨ δ ⊨ subValAt T' ar a y ⟩ → InK (fst (lookup y δ))
      subK-of T' ar a y δ q h =
        Z.sndK (fst Ts) (pr (fst (lookup ar δ)) (fst (lookup a δ))) (fst (lookup y δ)) TK
          (subst (λ u → ⟨ pr (pr (fst (lookup ar δ)) (fst (lookup a δ))) (fst (lookup y δ)) ∈ u ⟩) q
            (subst ⟨_⟩ (subValAt-adequate T' ar a y δ) h))

      subKS-of : ∀ {n'} (T' ar a y : Fin n') (δ : CS.S ^ n')
               → fst (lookup T' δ) ≡ fst Ts
               → ⟨ δ ⊨ subValSuccAt T' ar a y ⟩ → InK (fst (lookup y δ))
      subKS-of T' ar a y δ q h =
        Z.sndK (fst Ts) (pr (sucV (fst (lookup ar δ))) (fst (lookup a δ))) (fst (lookup y δ)) TK
          (subst (λ u → ⟨ pr (pr (sucV (fst (lookup ar δ))) (fst (lookup a δ))) (fst (lookup y δ)) ∈ u ⟩) q
            (subst ⟨_⟩ (subValSuccAt-adequate T' ar a y δ) h))

      -- The environment ties, from the tower, at the row's own
      -- environment: the arity slot holds a numeral, the carrier slot w.
      envK-of : ∀ {n'} (δ : CS.S ^ n') (ar Bi : Fin n') → fst (lookup Bi δ) ≡ Wv
              → ∥ Σ[ n ∈ ℕ ] (fst (lookup ar δ) ≡ # n) ∥₁
              → (Ei : Fin n') → ⟨ δ ⊨ envSetAt Ei ar Bi ⟩ → InK (fst (lookup Ei δ))
      envK-of δ ar Bi qb arNum' Ei hE = PT.rec (snd (fst (lookup Ei δ) ∈ Kv))
        (λ { (n , q) → Tw.At.envK δ ar Bi n q qb Ei hE }) arNum'

      envInK-of : ∀ {n'} (δ : CS.S ^ n') (ar Bi : Fin n') → fst (lookup Bi δ) ≡ Wv
                → ∥ Σ[ n ∈ ℕ ] (fst (lookup ar δ) ≡ # n) ∥₁
                → (z : CS.S) → ⟨ (z ∷ δ) ⊨ envOverAt zero (suc ar) (suc Bi) ⟩ → InK (fst z)
      envInK-of δ ar Bi qb arNum' z hz = PT.rec (snd (fst z ∈ Kv))
        (λ { (n , q) → Tw.At.over-K δ ar Bi n q qb z hz }) arNum'

      -- The extended environment, at the unary and the binary frames.
      consK-un : (ya yc a ar c E : CS.S) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
               → (z x e' : CS.S)
               → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ E2) ⊨ envOverAt zero i5 (sh7 (sh2 w)) ⟩
               → ⟨ fst x ∈ Wv ⟩
               → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ E2) ⊨
                   consAtL zero (suc zero) (suc (suc zero)) ⟩
               → InK (fst e')
      consK-un ya yc a ar c E arNum' z x e' hz x∈ hc = PT.rec (snd (fst e' ∈ Kv))
        (λ { (n , q) → Tw.At.consK (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ E2) i4 (sh6 (sh2 w)) n q refl
               z x e' hz x∈
               (λ g hz' → subst ⟨_⟩ (consAtL-adequate zero (suc zero) (suc (suc zero))
                            (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ E2) g hz') hc) })
        arNum'

      consK-bin : (E ya yc b a ar c : CS.S) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
                → (z w' x e' : CS.S)
                → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ E2) ⊨ envOverAt zero i6 (sh8 (sh2 w)) ⟩
                → ⟨ fst x ∈ Wv ⟩
                → ⟨ (e' ∷ x ∷ w' ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ E2) ⊨
                    consAtL zero (suc zero) (suc (suc (suc zero))) ⟩
                → InK (fst e')
      consK-bin E ya yc b a ar c arNum' z w' x e' hz x∈ hc = PT.rec (snd (fst e' ∈ Kv))
        (λ { (n , q) → Tw.At.consK (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ E2) i5 (sh7 (sh2 w)) n q refl
               z x e' hz x∈
               (λ g hz' → subst ⟨_⟩ (consAtL-adequate zero (suc zero) (suc (suc (suc zero)))
                            (e' ∷ x ∷ w' ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ E2) g hz') hc) })
        arNum'

      -- The successor key of a subformula lies in K.
      sucKeyK : (ar a : CS.S) → InK (fst ar) → InK (fst a) → InK (pr (sucV (fst ar)) (fst a))
      sucKeyK ar a arK aK = subst InK (prʟ-fst arS a) (C.pairK arS a (C.sucK ar arK) aK)
        where
        arS : CS.S
        arS = sucV (fst ar) , isL-trans {x = Kv} {y = sucV (fst ar)} (C.sucK ar arK) (snd (lookup K γ))

    -- THE FOUR ROWS WHOSE TELESCOPES THE TIES ABOVE FILL DIRECTLY.
    module RBot = BotAgree {2 + m} i1 i0 (sh2 w) (sh2 N7) (sh2 K) E2
                    (tags2 .t7) (C.numK 7) (unK 7) (unCodes 7) (valK-un' 7)

    rowBot : ⟨ E2 ⊨ Bot.botBndAt i1 i0 (sh2 w) (sh2 N7) (sh2 K) ⟩
    rowBot = RBot.bot-out US.botSound

    module RTop = TopAgree {2 + m} i1 i0 (sh2 w) (sh2 N6) (sh2 K) E2
                    (tags2 .t6) (C.numK 6) (unK 6) arityK (unCodes 6) (valK-un' 6)
                    (λ yc a ar c E arNum' hE →
                       envK-of (E ∷ yc ∷ a ∷ ar ∷ c ∷ E2) i3 (sh5 (sh2 w)) refl arNum' zero hE)
                    (λ yc a ar c E arK arNum' z hz →
                       envInK-of (E ∷ yc ∷ a ∷ ar ∷ c ∷ E2) i3 (sh5 (sh2 w)) refl arNum' z hz)

    rowTop : ⟨ E2 ⊨ Top.topBndAt i1 i0 (sh2 w) (sh2 N6) (sh2 K) ⟩
    rowTop = RTop.out US.topSound

    module RNeg = NegAgree {2 + m} i1 i0 (sh2 w) (sh2 N5) (sh2 K) E2
                    (tags2 .t5) (C.numK 5) (unK 5) arityK (unCodes 5) (valK-un' 5)
                    (λ E ya yc a ar c arK aK →
                       subst InK (prʟ-fst ar a) (C.pairK ar a arK aK))
                    (λ ya yc a ar c E hs →
                       subK-of (sh6 i0) i4 i3 i1 (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ E2) refl hs)
                    (λ ya yc a ar c E arNum' hE →
                       envK-of (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ E2) i4 (sh6 (sh2 w)) refl arNum' zero hE)
                    (λ ya yc a ar c E arK arNum' z hz →
                       envInK-of (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ E2) i4 (sh6 (sh2 w)) refl arNum' z hz)

    rowNeg : ⟨ E2 ⊨ Neg.negBndAt i1 i0 (sh2 w) (sh2 N5) (sh2 K) ⟩
    rowNeg = RNeg.out US.negSound

    module RImp = ImpAgree {2 + m} i1 i0 (sh2 w) (sh2 N4) (sh2 K) E2
                    (tags2 .t4) (C.numK 4) (binK 4) C.pairK arityK (binCodes 4) (valK-bin 4)
                    C.pairK
                    (λ E yb ya yc b a ar c hs →
                       subK-of (sh8 i0) i6 i5 i2 (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ E2) refl hs)
                    (λ E yb ya yc b a ar c hs →
                       subK-of (sh8 i0) i6 i4 i1 (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ E2) refl hs)
                    (λ E yb ya yc b a ar c arNum' hE →
                       envK-of (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ E2) i6 (sh8 (sh2 w)) refl arNum' zero hE)
                    (λ E ya yc b a ar c arK arNum' z hz →
                       envInK-of (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ E2) i5 (sh7 (sh2 w)) refl arNum' z hz)

    rowImp : ⟨ E2 ⊨ Imp.impBndAt i1 i0 (sh2 w) (sh2 N4) (sh2 K) ⟩
    rowImp = RImp.out US.impSound

    -- THE ATOM ROWS, through the re-tied atom leaf of
    -- src/L/GCH/LevelRows.lagda.md `AtomLeaf′`: the body of
    -- src/L/Condensation.lagda.md `MemAgree.out`.
    memOut : ⟨ E2 ⊨ Mem.memBndAt i1 i0 (sh2 w) (sh2 N0) (sh2 K) (sh2 N0) (sh2 N1) ⟩
    memOut c c∈ ar arK a aK b bK yc ycK shB hc E EK henv =
      extAt→extAtB i1 (sh6 (sh2 K)) L.bodyS L.bodyM env6 L.fwd L.bwd hbM
      where
      env6 : CS.S ^ (6 + (2 + m))
      env6 = E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ E2
      shD = BinaryShape.out {2 + m} (sh2 N0) (sh2 K) 0 (yc ∷ b ∷ a ∷ ar ∷ c ∷ E2) (tags .t0) shB
      shEq : fst c ≡ pr (fst ar) (pr (# 0) (pr (fst a) (fst b)))
      shEq = transport (cong fst (arityTagPairAtL-adequate i4 i3 0 i2 i1 (yc ∷ b ∷ a ∷ ar ∷ c ∷ E2))) shD
      arNum' = binCodes 0 c ar a b c∈ shEq .snd .snd .snd
      module E' = EnvSet {6 + (2 + m)} zero i4 (sh6 (sh2 w)) (sh6 (sh2 K)) env6
                    arityK EK arK (envInK-of env6 i4 (sh6 (sh2 w)) refl arNum')
      hbM = US.memSound c c∈ ar a b yc shD hc E (E'.out henv)
      module L = AtomLeaf′ E yc b a ar c E2 (sh2 N0) (sh2 N1) (sh2 K)
                   C.transK aK bK EK (tags .t0) (tags .t1) t0K (C.numK 1)
                   (var (suc zero) ∈̇ var zero)

    eqOut : ⟨ E2 ⊨ Eq.eqBndAt i1 i0 (sh2 w) (sh2 N1) (sh2 K) (sh2 N0) (sh2 N1) ⟩
    eqOut c c∈ ar arK a aK b bK yc ycK shB hc E EK henv =
      extAt→extAtB i1 (sh6 (sh2 K)) L.bodyS L.bodyM env6 L.fwd L.bwd hbM
      where
      env6 : CS.S ^ (6 + (2 + m))
      env6 = E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ E2
      shD = BinaryShape.out {2 + m} (sh2 N1) (sh2 K) 1 (yc ∷ b ∷ a ∷ ar ∷ c ∷ E2) (tags .t1) shB
      shEq : fst c ≡ pr (fst ar) (pr (# 1) (pr (fst a) (fst b)))
      shEq = transport (cong fst (arityTagPairAtL-adequate i4 i3 1 i2 i1 (yc ∷ b ∷ a ∷ ar ∷ c ∷ E2))) shD
      arNum' = binCodes 1 c ar a b c∈ shEq .snd .snd .snd
      module E' = EnvSet {6 + (2 + m)} zero i4 (sh6 (sh2 w)) (sh6 (sh2 K)) env6
                    arityK EK arK (envInK-of env6 i4 (sh6 (sh2 w)) refl arNum')
      hbM = US.eqSound c c∈ ar a b yc shD hc E (E'.out henv)
      module L = AtomLeaf′ E yc b a ar c E2 (sh2 N0) (sh2 N1) (sh2 K)
                   C.transK aK bK EK (tags .t0) (tags .t1) t0K (C.numK 1)
                   (var (suc zero) ≐ var zero)

    -- THE QUANTIFIER ROWS: `ForallAgree.out` with the extension tie
    -- from the tower, `ExistAgree.out` with the re-tied leaf.
    forallOut : ⟨ E2 ⊨ Forall.forallBndAt i1 i0 (sh2 w) (sh2 N9) (sh2 K) ⟩
    forallOut c c∈ ar arK a aK yc ycK shB hc ya yaK E EK hsub henv =
      extAt→extAtB i2 (sh6 (sh2 K)) (Forall.bodyFφ i1 i0 (sh2 w) (sh2 N9) (sh2 K)) (body∀ (sh2 w)) env6
        (λ z hz → hz .fst
                , (λ x xB e' hc' → hz .snd x xB e'
                    (consK-un ya yc a ar c E arNum' z x e'
                      (extAt-out zero (envOverAt zero i5 (sh7 (sh2 w))) env6 hE' z (hz .fst))
                      xB hc')
                    hc'))
        (λ z hz → hz .fst , (λ x xB e' e'K → hz .snd x xB e'))
        hbM
      where
      env6 : CS.S ^ (6 + (2 + m))
      env6 = E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ E2
      shD = UnaryShape.out {2 + m} (sh2 N9) (sh2 K) 9 (yc ∷ a ∷ ar ∷ c ∷ E2) (tags .t9) shB
      shEq : fst c ≡ pr (fst ar) (pr (# 9) (fst a))
      shEq = transport (cong fst (arityTagAtL-adequate i3 i2 9 i1 (yc ∷ a ∷ ar ∷ c ∷ E2))) shD
      arNum' = unCodes 9 c ar a c∈ shEq .snd .snd
      module E' = EnvSet {6 + (2 + m)} zero i4 (sh6 (sh2 w)) (sh6 (sh2 K)) env6
                    arityK EK arK (envInK-of env6 i4 (sh6 (sh2 w)) refl arNum')
      hE' = E'.out henv
      hya' = SubValSuccB2T.back {m = 6 + (2 + m)} (sh6 i0) i4 i3 i1 (sh6 (sh2 K)) env6
               (C.sucK ar arK) (sucKeyK ar a arK aK) hsub
      hbM = US.forallSound c c∈ ar a yc shD hc ya E hya' hE'

    module RExist = ExistAgree′ {2 + m} i1 i0 (sh2 w) (sh2 N8) (sh2 K) E2
                      (tags2 .t8) (C.numK 8) (unK 8) C.pairK C.transK C.sucK (unCodes 8) (valK-un' 8)
                      (λ ya yc a ar c E hs →
                         subKS-of (sh6 i0) i4 i3 i1 (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ E2) refl hs)
                      (λ ya yc a ar c E arNum' hE →
                         envK-of (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ E2) i4 (sh6 (sh2 w)) refl arNum' zero hE)
                      (λ ya yc a ar c E arK arNum' z hz →
                         envInK-of (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ E2) i4 (sh6 (sh2 w)) refl arNum' z hz)

    existOut : ⟨ E2 ⊨ Exist.existBndAt i1 i0 (sh2 w) (sh2 N8) (sh2 K) ⟩
    existOut c c∈ ar arK a aK yc ycK shB hc ya yaK E EK hsub henv =
      extAt→extAtB i2 (sh6 (sh2 K)) (Exist.bodyE i1 i0 (sh2 w) (sh2 N8) (sh2 K)) (body∃ (sh2 w)) env6
        L.fwd L.bwd hbM
      where
      env6 : CS.S ^ (6 + (2 + m))
      env6 = E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ E2
      shD = UnaryShape.out {2 + m} (sh2 N8) (sh2 K) 8 (yc ∷ a ∷ ar ∷ c ∷ E2) (tags .t8) shB
      shEq : fst c ≡ pr (fst ar) (pr (# 8) (fst a))
      shEq = transport (cong fst (arityTagAtL-adequate i3 i2 8 i1 (yc ∷ a ∷ ar ∷ c ∷ E2))) shD
      arNum' = unCodes 8 c ar a c∈ shEq .snd .snd
      module E' = EnvSet {6 + (2 + m)} zero i4 (sh6 (sh2 w)) (sh6 (sh2 K)) env6
                    arityK EK arK (envInK-of env6 i4 (sh6 (sh2 w)) refl arNum')
      hya' = SubValSuccB2T.back {m = 6 + (2 + m)} (sh6 i0) i4 i3 i1 (sh6 (sh2 K)) env6
               (C.sucK ar arK) (sucKeyK ar a arK aK) hsub
      hbM = US.existSound c c∈ ar a yc shD hc ya E hya' (E'.out henv)
      module L = RExist.Leaf E ya yc a ar c yaK

    -- THE BOUNDED-QUANTIFIER ROWS, through the re-tied leaf
    -- `BndLeaf′`: the body of `AllInAgree.out`.
    allInOut : ⟨ E2 ⊨ AllIn.allInBndAt i1 i0 (sh2 w) (sh2 N10) (sh2 K) (sh2 N0) (sh2 N1) ⟩
    allInOut c c∈ ar arK a aK b bK yc ycK shB hc yb ybK E EK hsub henv =
      extAt→extAtB i2 (sh7 (sh2 K)) L.bodyS L.bodyM env7 L.all-fwd L.all-bwd hbM
      where
      env7 : CS.S ^ (7 + (2 + m))
      env7 = E ∷ yb ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ E2
      shD = BinaryShape.out {2 + m} (sh2 N10) (sh2 K) 10 (yc ∷ b ∷ a ∷ ar ∷ c ∷ E2) (tags .t10) shB
      shEq : fst c ≡ pr (fst ar) (pr (# 10) (pr (fst a) (fst b)))
      shEq = transport (cong fst (arityTagPairAtL-adequate i4 i3 10 i2 i1 (yc ∷ b ∷ a ∷ ar ∷ c ∷ E2))) shD
      arNum' = binCodes 10 c ar a b c∈ shEq .snd .snd .snd
      module E' = EnvSet {7 + (2 + m)} zero i5 (sh7 (sh2 w)) (sh7 (sh2 K)) env7
                    arityK EK arK (envInK-of env7 i5 (sh7 (sh2 w)) refl arNum')
      hE' = E'.out henv
      hyb' = SubValSuccB2T.back {m = 7 + (2 + m)} (sh7 i0) i5 i3 i1 (sh7 (sh2 K)) env7
               (C.sucK ar arK) (sucKeyK ar b arK bK) hsub
      hbM = US.allInSound c c∈ ar a b yc shD hc yb E hyb' hE'
      module L = BndLeaf′ (sh2 w) (sh2 N0) (sh2 N1) (sh2 K) E yb yc b a ar c E2
                   (tags .t0) (tags .t1) t0K C.transK aK EK (C.numK 1) hE'
                   (λ z w' x e' hz x∈ hc' → consK-bin E yb yc b a ar c arNum' z w' x e' hz x∈ hc')

    exInOut : ⟨ E2 ⊨ ExIn.exInBndAt i1 i0 (sh2 w) (sh2 N11) (sh2 K) (sh2 N0) (sh2 N1) ⟩
    exInOut c c∈ ar arK a aK b bK yc ycK shB hc yb ybK E EK hsub henv =
      extAt→extAtB i2 (sh7 (sh2 K)) L.bodySx L.bodyMx env7 L.ex-fwd L.ex-bwd hbM
      where
      env7 : CS.S ^ (7 + (2 + m))
      env7 = E ∷ yb ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ E2
      shD = BinaryShape.out {2 + m} (sh2 N11) (sh2 K) 11 (yc ∷ b ∷ a ∷ ar ∷ c ∷ E2) (tags .t11) shB
      shEq : fst c ≡ pr (fst ar) (pr (# 11) (pr (fst a) (fst b)))
      shEq = transport (cong fst (arityTagPairAtL-adequate i4 i3 11 i2 i1 (yc ∷ b ∷ a ∷ ar ∷ c ∷ E2))) shD
      arNum' = binCodes 11 c ar a b c∈ shEq .snd .snd .snd
      module E' = EnvSet {7 + (2 + m)} zero i5 (sh7 (sh2 w)) (sh7 (sh2 K)) env7
                    arityK EK arK (envInK-of env7 i5 (sh7 (sh2 w)) refl arNum')
      hE' = E'.out henv
      hyb' = SubValSuccB2T.back {m = 7 + (2 + m)} (sh7 i0) i5 i3 i1 (sh7 (sh2 K)) env7
               (C.sucK ar arK) (sucKeyK ar b arK bK) hsub
      hbM = US.exInSound c c∈ ar a b yc shD hc yb E hyb' hE'
      module L = BndLeaf′ (sh2 w) (sh2 N0) (sh2 N1) (sh2 K) E yb yc b a ar c E2
                   (tags .t0) (tags .t1) t0K C.transK aK EK (C.numK 1) hE'
                   (λ z w' x e' hz x∈ hc' → consK-bin E yb yc b a ar c arNum' z w' x e' hz x∈ hc')

    -- THE PROPOSITIONAL ROWS, read off the table.  The recorded value
    -- at the code is the satisfaction set of the connective, the two
    -- subvalues those of its parts (Section 3 `Bin.parts`), and the
    -- bounded operation is membership in the satisfaction set, both
    -- ways (src/L/Coding/Sat.lagda.md `Sat-mem`).
    private
      -- The three entries a propositional row hands over, read as
      -- memberships in the table.
      module PropSite (k : ℕ) (Ni : Fin m) (te : fst (lookup Ni γ) ≡ fst (numeralL k))
                      (c ar a b yc ya yb E : CS.S)
                      (c∈ : ⟨ fst c ∈ fst Cs ⟩)
                      (shB : ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ E2) ⊨ arTagPairB (sh2 Ni) (sh2 K) ⟩)
                      (hc : ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ E2) ⊨ appAt (sh5 i0) i4 i0 ⟩)
                      (hsubA : ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ E2) ⊨
                                  subValB (sh7 i0) i5 i4 i1 (sh7 (sh2 K)) ⟩)
                      (hsubB : ⟨ (yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ E2) ⊨
                                  subValB (sh8 i0) i6 i4 i0 (sh8 (sh2 K)) ⟩) where
        shD = BinaryShape.out {2 + m} (sh2 Ni) (sh2 K) k (yc ∷ b ∷ a ∷ ar ∷ c ∷ E2) te shB
        shEq : fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
        shEq = transport (cong fst (arityTagPairAtL-adequate i4 i3 k i2 i1 (yc ∷ b ∷ a ∷ ar ∷ c ∷ E2))) shD
        hc' : ⟨ pr (fst c) (fst yc) ∈ fst Ts ⟩
        hc' = app-out (sh5 i0) i4 i0 (yc ∷ b ∷ a ∷ ar ∷ c ∷ E2) hc
        ha' : ∥ ⟨ pr (pr (fst ar) (fst a)) (fst ya) ∈ fst Ts ⟩ ∥₁
        ha' = PT.map (λ { (z , (_ , (e , h))) →
                subst (λ u → ⟨ pr u (fst ya) ∈ fst Ts ⟩)
                  (pr-out zero i6 i5 (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ E2) e)
                  (app-out (sh8 i0) zero i2 (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ E2) h) })
              hsubA
        hb' : ∥ ⟨ pr (pr (fst ar) (fst b)) (fst yb) ∈ fst Ts ⟩ ∥₁
        hb' = PT.map (λ { (z , (_ , (e , h))) →
                subst (λ u → ⟨ pr u (fst yb) ∈ fst Ts ⟩)
                  (pr-out zero i7 i5 (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ E2) e)
                  (app-out (sh9 i0) zero i1 (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ E2) h) })
              hsubB

    andOut : ⟨ E2 ⊨ And.andBndAt i1 i0 (sh2 w) (sh2 N2) (sh2 K) ⟩
    andOut c c∈ ar arK a aK b bK yc ycK shB hc ya yaK E EK hsubA henv yb ybK hsubB =
      PT.rec (snd (env8 ⊨ interB i3 i2 i0 (sh8 (sh2 K))))
        (λ ha' → PT.rec (snd (env8 ⊨ interB i3 i2 i0 (sh8 (sh2 K))))
          (λ hb' → PT.rec (snd (env8 ⊨ interB i3 i2 i0 (sh8 (sh2 K)))) body
                     (US.BinAnd.parts c ar a b yc ya yb c∈ P.shEq P.hc' ha' hb'))
          P.hb')
        P.ha'
      where
      module P = PropSite 2 N2 (tags .t2) c ar a b yc ya yb E c∈ shB hc hsubA hsubB
      env8 : CS.S ^ (8 + (2 + m))
      env8 = yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ E2
      body : US.BinAnd.Parts ar yc ya yb → ⟨ env8 ⊨ interB i3 i2 i0 (sh8 (sh2 K)) ⟩
      body (n , a' , b' , (qm , (ec , (ea , eb)))) =
          (λ z hz →
            let s = subst ⟨_⟩ (Sat-mem A (a' ∧̇ b') z) (subst (λ u → ⟨ fst z ∈ u ⟩) ec hz)
            in subst (λ u → ⟨ fst z ∈ u ⟩) (sym ea) (s .snd .fst)
             , subst (λ u → ⟨ fst z ∈ u ⟩) (sym eb) (s .snd .snd))
        , (λ z zK hz →
            let za = subst (λ u → ⟨ fst z ∈ u ⟩) ea (hz .fst)
                zb = subst (λ u → ⟨ fst z ∈ u ⟩) eb (hz .snd)
            in subst (λ u → ⟨ fst z ∈ u ⟩) (sym ec)
                 (subst ⟨_⟩ (sym (Sat-mem A (a' ∧̇ b') z))
                   (subst ⟨_⟩ (Sat-mem A a' z) za .fst , (za , zb))))

    orOut : ⟨ E2 ⊨ Or.orBndAt i1 i0 (sh2 w) (sh2 N3) (sh2 K) ⟩
    orOut c c∈ ar arK a aK b bK yc ycK shB hc ya yaK E EK hsubA henv yb ybK hsubB =
      PT.rec (snd (env8 ⊨ unionB i3 i2 i0 (sh8 (sh2 K))))
        (λ ha' → PT.rec (snd (env8 ⊨ unionB i3 i2 i0 (sh8 (sh2 K))))
          (λ hb' → PT.rec (snd (env8 ⊨ unionB i3 i2 i0 (sh8 (sh2 K)))) body
                     (US.BinOr.parts c ar a b yc ya yb c∈ P.shEq P.hc' ha' hb'))
          P.hb')
        P.ha'
      where
      module P = PropSite 3 N3 (tags .t3) c ar a b yc ya yb E c∈ shB hc hsubA hsubB
      env8 : CS.S ^ (8 + (2 + m))
      env8 = yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ E2
      body : US.BinOr.Parts ar yc ya yb → ⟨ env8 ⊨ unionB i3 i2 i0 (sh8 (sh2 K)) ⟩
      body (n , a' , b' , (qm , (ec , (ea , eb)))) =
          (λ z hz → PT.map
            (λ { (inl v) → inl (subst (λ u → ⟨ fst z ∈ u ⟩) (sym ea) v)
               ; (inr v) → inr (subst (λ u → ⟨ fst z ∈ u ⟩) (sym eb) v) })
            (subst ⟨_⟩ (Sat-mem A (a' ∨̇ b') z) (subst (λ u → ⟨ fst z ∈ u ⟩) ec hz) .snd))
        , (λ z zK hz → PT.rec (snd (fst z ∈ fst yc))
            (λ { (inl v) →
                   let za = subst (λ u → ⟨ fst z ∈ u ⟩) ea v in
                   subst (λ u → ⟨ fst z ∈ u ⟩) (sym ec)
                     (subst ⟨_⟩ (sym (Sat-mem A (a' ∨̇ b') z))
                       (subst ⟨_⟩ (Sat-mem A a' z) za .fst , ∣ inl za ∣₁))
               ; (inr v) →
                   let zb = subst (λ u → ⟨ fst z ∈ u ⟩) eb v in
                   subst (λ u → ⟨ fst z ∈ u ⟩) (sym ec)
                     (subst ⟨_⟩ (sym (Sat-mem A (a' ∨̇ b') z))
                       (subst ⟨_⟩ (Sat-mem A b' z) zb .fst , ∣ inr zb ∣₁)) })
            hz)

    -- THE ROW.
    twelve : ⟨ E2 ⊨ twelveAt i1 i0 (sh2 w) (sh2 K)
                      (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
                      (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11) ⟩
    twelve = memOut , ( eqOut , ( andOut , ( orOut , ( rowImp , ( rowNeg , ( rowTop , ( rowBot
           , ( existOut , ( forallOut , ( allInOut , exInOut ))))))))))
```

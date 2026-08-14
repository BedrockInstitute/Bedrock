{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1-226] Probe A.  THE PAIRING ON ω, BUILT INTO L.
--
-- THE OBJECT.  Row 5 of A5: `pairω : ⟪ω⟫ × ⟪ω⟫ → ⟪ω⟫`, the Gödel pairing
-- `(a+b)²+a` on the numerals, built as an L-element that reads back as the
-- injection.  [LJ-1.176] priced it INFERRED at 160 lines and warned it may
-- be far too low, because the object-language arithmetic (addition and
-- multiplication on numerals) exists nowhere in the tree.
--
-- THE GATE (DD8).  Measure the widest unmeasured term.  This file IS the
-- measurement.
--
-- THE SHAPE.  Direct-equality shape (green 15.0 s in [LJ-1.217]) first.
--
-- ABORT CRITERION, fixed in the report section 1 BEFORE this file was
-- written: BUILT AT OR NEAR 160 / MATERIALLY OVER 160 / WALLS (20 min) /
-- NOT NEEDED / column square free.
--
-- Tracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-226.ProbeLJ1226A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

-- =====================================================================
-- PART 0.  THE AMBIENT PAIRING.  [LJ-1.156] ProbeLJ1156A:111-159,
-- verbatim minus `ω≃ℕ`.  This is the function the L-element must read
-- back as.  Its carrier is the HIERARCHY, so it lives in its own module
-- with `open hPropStructure 𝒮ᵥ`, BEFORE the L-side opens.
-- =====================================================================

module Ambient where

  open import FOL.ZFStructure using ( module hPropStructure )
  open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
  open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
  open hPropStructure 𝒮ᵥ

  import L.Ordinal.SquareLaw {ℓ} lem as SQ
  open SQ using ( module FiniteBase )
  import L.Ordinal {ℓ} as Ord
  open Ord using ( ω-ord; #∈ω )
  import L.Choice.Finite {ℓ} lem as LF
  open LF using ( natOrder )
  import FOL.Count {ℓ} as Count
  import V.Coding {ℓ} as VCoding
  open VCoding using ( #-inj′ )
  import Cubical.Data.Sigma as Sig
  open Sig using ( ΣPathP; Σ≡Prop )
  import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} as WOBase
  open WOBase using ( leastOf )
  import Cubical.Data.Nat as Nat
  open Nat using ( ℕ; zero; suc )
  import Cubical.Data.Nat.Properties as NatProp
  open NatProp using ( injSuc; znots; snotz )
  import Cubical.Data.Sum as Sum
  open Sum using ( _⊎_; inl; inr )
  import Cubical.Data.Empty as Empty
  import Cubical.HITs.PropositionalTruncation as PT
  open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
  import Cubical.HITs.CumulativeHierarchy.Base as CHB
  open CHB using ( setIsSet )
  import Cubical.HITs.CumulativeHierarchy.Properties as CH
  open CH using ( ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
  import Cubical.Functions.Embedding as Emb
  open Emb using ( isEmbedding→hasPropFibers; Embedding-into-isSet→isSet )
  import Cubical.HITs.CumulativeHierarchy.Constructions as CHC
  open CHC using ( module InfinitySet )
  open InfinitySet {ℓ} using ( ω; sucV; #_ )

  _↪_ : Type ℓ → Type ℓ → Type ℓ
  X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

  isSet⟪_⟫ : (a : S) → isSet ⟪ a ⟫
  isSet⟪ a ⟫ = Embedding-into-isSet→isSet (⟪ a ⟫↪ , isEmb⟪ a ⟫↪) setIsSet

  module NumeralPresentation where

    open FiniteBase

    numeralω : ℕ → ⟪ ω ⟫
    numeralω k = fiber ω {x = # k} (#∈ω k) .fst

    numeralω-inj : (k k' : ℕ) → numeralω k ≡ numeralω k' → k ≡ k'
    numeralω-inj k k' e = #-inj′ (sym (fiber ω {x = # k} (#∈ω k) .snd)
      ∙ cong (⟪ ω ⟫↪) e ∙ fiber ω {x = # k'} (#∈ω k') .snd)

    isPropNumeralWit : (δ : S) → isProp (Σ[ n ∈ ℕ ] (# n ≡ δ))
    isPropNumeralWit δ (n , p) (n' , p') =
      Σ≡Prop (λ k → isSetS (# k) δ) (#-inj′ (p ∙ sym p'))

    to-wit : (m : ⟪ ω ⟫) → Σ[ n ∈ ℕ ] (# n ≡ ⟪ ω ⟫↪ m)
    to-wit m = PT.rec (isPropNumeralWit (⟪ ω ⟫↪ m)) hit
      (ω-mem→numeral (⟪ ω ⟫↪ m)
        (∈∈ₛ {a = ⟪ ω ⟫↪ m} {b = ω} .snd (∈ₛ⟪ ω ⟫↪ m)))
      where
      hit : Σ[ n ∈ ℕ ] (⟪ ω ⟫↪ m ≡ # n) → Σ[ n ∈ ℕ ] (# n ≡ ⟪ ω ⟫↪ m)
      hit (n , p) = n , sym p

    to : ⟪ ω ⟫ → ℕ
    to m = to-wit m .fst

    to∘numeralω : (k : ℕ) → to (numeralω k) ≡ k
    to∘numeralω k = #-inj′ (to-wit (numeralω k) .snd
      ∙ fiber ω {x = # k} (#∈ω k) .snd)

    numeralω∘to : (m : ⟪ ω ⟫) → numeralω (to m) ≡ m
    numeralω∘to m = cong fst (isEmbedding→hasPropFibers isEmb⟪ ω ⟫↪ (⟪ ω ⟫↪ m)
      (numeralω (to m) , fiber ω {x = # (to m)} (#∈ω (to m)) .snd ∙ to-wit m .snd)
      (m , refl))

    to-inj : (m n : ⟪ ω ⟫) → to m ≡ to n → m ≡ n
    to-inj m n e = sym (numeralω∘to m) ∙ cong numeralω e ∙ numeralω∘to n

    pairω : ⟪ ω ⟫ × ⟪ ω ⟫ → ⟪ ω ⟫
    pairω (m , n) = numeralω (Count.pair (to m) (to n))

    pairω-inj : (x y : ⟪ ω ⟫ × ⟪ ω ⟫) → pairω x ≡ pairω y → x ≡ y
    pairω-inj (m , n) (m' , n') e =
      ΣPathP ( to-inj m m' (fst (Count.pair-inj (to m) (to n) (to m') (to n') nm))
             , to-inj n n' (snd (Count.pair-inj (to m) (to n) (to m') (to n') nm)) )
      where
      nm : Count.pair (to m) (to n) ≡ Count.pair (to m') (to n')
      nm = numeralω-inj (Count.pair (to m) (to n)) (Count.pair (to m') (to n')) e

-- =====================================================================
-- L-side imports and vocabulary.
-- =====================================================================

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; con; var; ∃̇∈; ∃̇_; ∀̇_; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_ )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Model {ℓ} using ( ∈sucV-elim; ∈sucV-inl; pair-singleton; pair-spec; union-spec )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( boundingOrd; suc-ord )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Axioms.Basic {ℓ} using ( LsetS; ∅ʟ )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Numerals {ℓ}
  using ( numeralL; numeralL-fst; numeralL-suc; sucʟ; sucʟ-fst
        ; pairʟ; pairʟ-fst; unionʟ; unionʟ-fst )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ; ω-specL; isNumeralL )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; prʟ; prʟ-fst
        ; svAt; svAt-in; domAt; domAt-intro; sucAtL; sucAtL-adequate )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪; _∈ₛ_; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ⁅_,_⁆; ⁅_⁆s; ⋃_; union-ax; pairing-ax )
open import Cubical.Data.Nat using ( ℕ; zero; suc; _+_; _·_; +-zero; +-suc )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- PART 1.  THE ARITHMETIC FORMULAS, IN THE OBJECT LANGUAGE.
--
-- Every atom is delivered: `∈̇`, `≐`, `prAtL` (pair reader), `sucAtL`
-- (von Neumann successor reader), the connectives, the bounded and full
-- quantifiers.  NOTHING here is new vocabulary; it is the description of
-- addition and multiplication on the numerals that no task had written.
--
-- De Bruijn conventions, stated once.
--   addFo : Formula S 3, env [z, b, a]  (0=z, 1=b, 2=a)  "z = a + b".
--   Inside ∃F the frame is [F, z, b, a] (0=F, 1=z, 2=b, 3=a).
-- =====================================================================

private
  -- "<var x, var y> ∈ var f", at an arbitrary frame depth.
  pairMem : {n : ℕ} → Fin n → Fin n → Fin n → Formula S n
  pairMem f x y = ∃̇∈ (var f)
    (∃̇ (∃̇ (prAtL (suc (suc zero)) (suc zero) zero
       ∧̇ (var (suc zero) ≐ var (suc (suc (suc x))))
       ∧̇ (var zero ≐ var (suc (suc (suc y)))))))

  -- "<con c, var y> ∈ var f".
  pairMemc : {n : ℕ} → Fin n → S → Fin n → Formula S n
  pairMemc f c y = ∃̇∈ (var f)
    (∃̇ (∃̇ (prAtL (suc (suc zero)) (suc zero) zero
       ∧̇ (var (suc zero) ≐ con c)
       ∧̇ (var zero ≐ var (suc (suc (suc y)))))))

  -- The clauses, in the 4-frame [F, z, b, a]  (0=F, 1=z, 2=b, 3=a).

  -- F(∅) = a  :  ⟨#0, a⟩ ∈ F.
  startAt : Formula S 4
  startAt = pairMemc zero (numeralL 0) (suc (suc (suc zero)))

  -- F(b) = z  :  ⟨b, z⟩ ∈ F.
  endAt : Formula S 4
  endAt = pairMem zero (suc (suc zero)) (suc zero)

  -- F is successor-closed below b:
  --   ∀n. (n ∈ b → ∀m. (⟨n,m⟩∈F → ∃r.∃s. (sucAtL n r ∧ sucAtL m s ∧ ⟨r,s⟩∈F))).
  closedAt : Formula S 4
  closedAt = ∀̇_
    ( (var zero ∈̇ var (suc (suc (suc zero))))            -- n ∈ b
      ⇒̇ ∀̇_                                            -- ∀m
        ( pairMem (suc (suc zero)) (suc zero) zero      -- ⟨n,m⟩ ∈ F
          ⇒̇ ∃̇_ (∃̇_                                   -- ∃r.∃s
            ( sucAtL (suc (suc (suc zero))) (suc zero)  -- r = sucV n
              ∧̇ sucAtL (suc (suc zero)) zero            -- s = sucV m
              ∧̇ pairMem (suc (suc (suc (suc zero)))) (suc zero) zero  -- ⟨r,s⟩∈F
            ))))

  -- F is single-valued on sucV(b) = b ∪ {b}:
  --   ∀n. ((n ∈ b ∨ n ≐ b) → ∀m.∀m'. (⟨n,m⟩∈F → ⟨n,m'⟩∈F → m ≐ m')).
  singleAt : Formula S 4
  singleAt = ∀̇_
    ( ( (var zero ∈̇ var (suc (suc (suc zero))))
        ∨̇ (var zero ≐ var (suc (suc (suc zero)))) )
      ⇒̇ ∀̇_ (∀̇_
        ( pairMem (suc (suc (suc zero))) (suc (suc zero)) (suc zero)
          ⇒̇ pairMem (suc (suc (suc zero))) (suc (suc zero)) zero
          ⇒̇ (var (suc zero) ≐ var zero) )))

-- The addition relation: z = a + b over the numerals.
addFo : Formula S 3
addFo = (var (suc (suc zero)) ∈̇ con ωʟ) ∧̇ (var (suc zero) ∈̇ con ωʟ)
      ∧̇ ∃̇ (startAt ∧̇ closedAt ∧̇ endAt ∧̇ singleAt)

-- =====================================================================
-- PART 2.  THE ADDITION ADEQUACY.
--
-- `addFo` says z = a + b on the numerals.  The adequacy is two
-- implications, stated over the ambient naturals:
--   add-intro : fst z ≡ # (i + j)  →  the formula holds;
--   add-elim : the formula holds   →  fst z ≡ # (i + j).
-- The witness for add-intro is the finite graph
--   addGraph i j = { <#k, #(i+k)> : k ≤ j },
-- built constructibly by recursion on the model's pairing and union.
-- =====================================================================

numeral∈ωʟ : (n : ℕ) → ⟨ numeralL n ∈ˢ ωʟ ⟩
numeral∈ωʟ n = subst ⟨_⟩ (sym (ω-specL (numeralL n))) ∣ lift n , refl ∣₁

-- the singleton {x}, and s ∪ {x}
single : S → S
single x = pairʟ x x

insert : S → S → S
insert x s = unionʟ (pairʟ (single x) s)

-- { <#k, #(i+k)> : k ≤ j }, by recursion on j.
addGraph : ℕ → ℕ → S
addGraph i zero = single (prʟ (numeralL 0) (numeralL i))
addGraph i (suc j) = insert (prʟ (numeralL (suc j)) (numeralL (i + suc j))) (addGraph i j)

private
  -- fst x ∈ fst (single x), the V-level statement.
  x∈singleV : (x : S) → ⟨ fst x ∈ fst (single x) ⟩
  x∈singleV x = subst (λ w → ⟨ fst x ∈ w ⟩) (sym (pairʟ-fst x x))
    (subst ⟨_⟩ (sym (pair-spec (fst x) (fst x) (fst x))) ∣ inl refl ∣₁)

  -- x ∈ {x}.
  singleMem : (x : S) → ⟨ x ∈ˢ single x ⟩
  singleMem x = x∈singleV x

  -- x ∈ insert x s.
  insertMem : (x s : S) → ⟨ x ∈ˢ insert x s ⟩
  insertMem x s = subst (λ w → ⟨ fst x ∈ w ⟩) (sym (unionʟ-fst (pairʟ (single x) s)))
    (subst (λ w → ⟨ fst x ∈ ⋃ w ⟩) (sym (pairʟ-fst (single x) s))
      (subst ⟨_⟩ (sym (union-spec ⁅ fst (single x) , fst s ⁆ (fst x)))
        ∣ fst (single x)
        , ( subst ⟨_⟩ (sym (pair-spec (fst (single x)) (fst s) (fst (single x)))) ∣ inl refl ∣₁
          , x∈singleV x ) ∣₁))

  -- x ∈ s  →  x ∈ insert y s.
  insertMono : (x y s : S) → ⟨ x ∈ˢ s ⟩ → ⟨ x ∈ˢ insert y s ⟩
  insertMono x y s x∈s =
    subst (λ w → ⟨ fst x ∈ w ⟩) (sym (unionʟ-fst (pairʟ (single y) s)))
      (subst (λ w → ⟨ fst x ∈ ⋃ w ⟩) (sym (pairʟ-fst (single y) s))
        (subst ⟨_⟩ (sym (union-spec ⁅ fst (single y) , fst s ⁆ (fst x)))
          ∣ fst s
          , ( subst ⟨_⟩ (sym (pair-spec (fst (single y)) (fst s) (fst s))) ∣ inr refl ∣₁
            , x∈s ) ∣₁))

  -- The top element: <#j, #(i+j)> ∈ addGraph i j.
  addGraphTop : (i j : ℕ) → ⟨ prʟ (numeralL j) (numeralL (i + j)) ∈ˢ addGraph i j ⟩
  addGraphTop i zero = subst (λ w → ⟨ prʟ (numeralL zero) (numeralL w) ∈ˢ addGraph i zero ⟩)
    (sym (+-zero i)) (singleMem (prʟ (numeralL 0) (numeralL i)))
  addGraphTop i (suc j) =
    insertMem (prʟ (numeralL (suc j)) (numeralL (i + suc j))) (addGraph i j)

  -- A member of addGraph i k survives the insertions up to addGraph i (k + j).
  addGraphBelow : (i j k : ℕ) → ⟨ prʟ (numeralL k) (numeralL (i + k)) ∈ˢ addGraph i k ⟩
               → ⟨ prʟ (numeralL k) (numeralL (i + k)) ∈ˢ addGraph i (k + j) ⟩
  addGraphBelow i j k h = go j
    where
    go : (j : ℕ) → ⟨ prʟ (numeralL k) (numeralL (i + k)) ∈ˢ addGraph i (k + j) ⟩
    go zero = subst (λ w → ⟨ prʟ (numeralL k) (numeralL (i + k)) ∈ˢ addGraph i w ⟩)
                (sym (+-zero k)) h
    go (suc j) = subst (λ w → ⟨ prʟ (numeralL k) (numeralL (i + k)) ∈ˢ addGraph i w ⟩)
                   (sym (+-suc k j))
                   (insertMono (prʟ (numeralL k) (numeralL (i + k)))
                     (prʟ (numeralL (suc (k + j))) (numeralL (i + suc (k + j))))
                     (addGraph i (k + j)) (go j))

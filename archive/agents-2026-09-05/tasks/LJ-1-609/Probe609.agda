{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.609]  FACE E AT THE SIX SLOTS: `ElemDownAt`, INHABITED.
--
-- W3 IS runs/W3.agda, written FIRST and typechecked ALONE: exit 0 at
-- 4.40 s, peak 778,125,312 bytes (runs/w3-1.out), under the brief's
-- two-minute cap.  The type is [LJ-1.606]'s face E over that probe's
-- own Frame slots (Probe606.agda:104-109, :147-148).
--
-- THE FLOOR WAS MEASURED BEFORE ANY PROOF (the owner's ruling of
-- 2026-08-23): runs/FLOOR.agda is this file's import list and frame
-- with the obligation at one designed hole; runs/floor-2.out is exit
-- 42 at that hole, 3.11 s, peak 574,324,736 bytes.  (runs/floor-1.out,
-- 9.43 s and 1,691,172,864 bytes, is the same frame with the SEVENTEEN
-- import added: the price of that import, measured and then paid only
-- in runs/SEVENTEEN.agda, where the seventeen are imported.)
--
-- WHAT THE SEVENTEEN DID, AND WHAT THIS FILE REPLACES IT WITH.
--   [LJ-1.578]'s `elem-down-taken` (Probe578.agda:413-427) delivers
--   `DR54.ElemDown` only inside the seventeen-slot telescope, where the
--   carrier is FORCED to UK.X = Lset α ∪ ⁅ x ⁆s
--   (src/L/BoundedSubset.lagda.md:1150) and the canonical-code count
--   into ⟪ α ⟫ is bought from the square law and the absorption
--   (src/L/BoundedSubset.lagda.md:1409, :1513, :1528).  At the six
--   slots none of that is in scope: `SqAt` is a campaign row and not a
--   theorem (agents/tasks/LJ-1-550/Probe550.agda:309-310).
--   THE ROUTE HERE NEEDS NO SQUARE LAW.  It counts the hull's term
--   algebra into the STAGE ITSELF, not into an ordinal's presentation:
--   each code is a Kuratowski-nested set of stage members
--   (pr, src/V/Coding.lagda.md:175-179), the limit stage is closed
--   under that nesting (pr∈Lset-suc, src/L/Axioms/Basic.lagda.md:596,
--   plus succλ), and the selection runs on the stage's own delivered
--   L-order (orderAt, src/L/Choice/Step.lagda.md:730, opened by
--   DownReflect as ASt.wL).  The consumer is the tree's own six-slot
--   converter (HullElemDown.WithCode, src/L/BoundedSubset.lagda.md:681):
--   ONE section of the code evaluation buys ElemDown outright.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-609.Probe609 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Count {ℓ} using ( code; shape-count-inj )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV )
open import V.Presentation {ℓ} using ( member; ↪-inj )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj )
open import L.Constructible {ℓ}
  using ( IsOrd; Lset; 𝒟ₒ; Lset-in; Lset-out; Lset-mono )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc; Lset-cumul )
open import L.Axioms.Basic {ℓ} using ( ∅∈𝒟ₒ; Lset-suc; pr∈Lset-suc )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; leastOf )
open import L.BoundedSubset {ℓ} lem
  using ( module HullStage; module DownReflect; module HullElemDown )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅; ∅-empty )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ )
open InfinitySet {ℓ} using ( sucV; #_ )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Vec using ( Vec; _∷_; [] )
open import Cubical.Data.Sigma using ( Σ≡Prop; ΣPathP )
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.Foundations.Prelude
  using ( J; PathP; toPathP; transportRefl; isProp→isSet )
open import Cubical.Foundations.Transport using ( substSubst⁻ )
open import Cubical.Foundations.HLevels using ( isSetΣ; isProp× )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
import LJ-1-606.Probe606 {ℓ} lem as P606

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_; isSetS )

-- =====================================================================
-- THE SIX SLOTS, AND THE TREE'S OWN MACHINERY AT THEM.
--
--   The six are [LJ-1.606]'s Frame parameters (Probe606.agda:104-109).
--   HullStage, DownReflect and HullElemDown are all stated at exactly
--   these slots (src/L/BoundedSubset.lagda.md:903, :356, :667), so
--   nothing below restates a frame: every module is the tree's own,
--   applied to the six.
-- =====================================================================

module Six (lam : SV.S) (ordλ : IsOrd lam)
           (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
           (X : SV.S)
           (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
           (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module DR = DownReflect lam ordλ X X⊆Lλ ∅∈λ
  module HED = HullElemDown lam ordλ X X⊆Lλ ∅∈λ

  Code : Type ℓ
  Code = DR.H.T.Code

  -- the stage's own L-order, delivered (orderAt,
  -- src/L/Choice/Step.lagda.md:730, through src/L/Hull.lagda.md:161)
  -- and opened by DownReflect
  wL : SWO DR.ASt.SL
  wL = DR.ASt.wL

  isSetSL : isSet DR.ASt.SL
  isSetSL = isSetΣ isSetS (λ x → isProp→isSet (snd (x ∈ˢ Lset lam)))

  -- ===================================================================
  -- SECTION 1.  THE LIMIT STAGE IS CLOSED UNDER WHAT THE ENCODING
  -- SPENDS: numerals, and Kuratowski pairs of stage members.
  --
  --   Every fact here is six-slot.  The pair closure is the two-stage
  --   lift pr∈Lset-suc (src/L/Axioms/Basic.lagda.md:596-598) read back
  --   into the limit through Lset-out, trichotomy and succλ.
  -- ===================================================================

  ∅∈Lλ : ⟨ ∅ ∈ˢ Lset lam ⟩
  ∅∈Lλ = Lset-in lam ∅ ∅ ∅∈λ (∅∈𝒟ₒ ∅)

  #∈λ : (n : ℕ) → ⟨ (# n) ∈ˢ lam ⟩
  #∈λ zero = ∅∈λ
  #∈λ (suc n) = succλ (# n) (#∈λ n)

  #∈Lλ : (n : ℕ) → ⟨ (# n) ∈ˢ Lset lam ⟩
  #∈Lλ n = Lset-cumul (# n) lam o#n ordλ (#∈λ n)
             (ord∈Lset-suc (# n) o#n)
    where
    o#n : IsOrd (# n)
    o#n = mem-ord {A = lam} ordλ (# n) (#∈λ n)

  -- two stage members sit in a common Lset γ with γ ∈ lam
  common : (a b : SV.S) → ⟨ a ∈ˢ Lset lam ⟩ → ⟨ b ∈ˢ Lset lam ⟩
         → ∥ Σ[ γ ∈ SV.S ] (⟨ γ ∈ˢ lam ⟩
              × ⟨ a ∈ˢ Lset γ ⟩ × ⟨ b ∈ˢ Lset γ ⟩) ∥₁
  common a b a∈ b∈ = PT.rec2 squash₁ go (Lset-out lam a a∈) (Lset-out lam b b∈)
    where
    go : Σ[ δ ∈ SV.S ] (⟨ δ ∈ˢ lam ⟩ × ⟨ a ∈ˢ 𝒟ₒ (Lset δ) ⟩)
       → Σ[ δ' ∈ SV.S ] (⟨ δ' ∈ˢ lam ⟩ × ⟨ b ∈ˢ 𝒟ₒ (Lset δ') ⟩)
       → ∥ Σ[ γ ∈ SV.S ] (⟨ γ ∈ˢ lam ⟩
            × ⟨ a ∈ˢ Lset γ ⟩ × ⟨ b ∈ˢ Lset γ ⟩) ∥₁
    go (δ , δ∈ , a∈𝒟) (δ' , δ'∈ , b∈𝒟) = pick
      (ord-tri (sucV δ) (suc-ord (mem-ord {A = lam} ordλ δ δ∈))
               (sucV δ') (suc-ord (mem-ord {A = lam} ordλ δ' δ'∈)))
      where
      a∈Lδ⁺ : ⟨ a ∈ˢ Lset (sucV δ) ⟩
      a∈Lδ⁺ = subst (λ w → ⟨ a ∈ˢ w ⟩) (sym (Lset-suc δ)) a∈𝒟
      b∈Lδ'⁺ : ⟨ b ∈ˢ Lset (sucV δ') ⟩
      b∈Lδ'⁺ = subst (λ w → ⟨ b ∈ˢ w ⟩) (sym (Lset-suc δ')) b∈𝒟
      pick : Tri (sucV δ) (sucV δ')
           → ∥ Σ[ γ ∈ SV.S ] (⟨ γ ∈ˢ lam ⟩
                × ⟨ a ∈ˢ Lset γ ⟩ × ⟨ b ∈ˢ Lset γ ⟩) ∥₁
      pick (inl s∈) = ∣ sucV δ' , (succλ δ' δ'∈
                        , (Lset-mono s∈ a∈Lδ⁺ , b∈Lδ'⁺)) ∣₁
      pick (inr (inl e)) = ∣ sucV δ , (succλ δ δ∈
                        , (a∈Lδ⁺
                           , subst (λ w → ⟨ b ∈ˢ Lset w ⟩) (sym e) b∈Lδ'⁺)) ∣₁
      pick (inr (inr s∈)) = ∣ sucV δ , (succλ δ δ∈
                        , (a∈Lδ⁺ , Lset-mono s∈ b∈Lδ'⁺)) ∣₁

  pr∈Lλ : (a b : SV.S) → ⟨ a ∈ˢ Lset lam ⟩ → ⟨ b ∈ˢ Lset lam ⟩
        → ⟨ pr a b ∈ˢ Lset lam ⟩
  pr∈Lλ a b a∈ b∈ = PT.rec (snd (pr a b ∈ˢ Lset lam)) go (common a b a∈ b∈)
    where
    go : Σ[ γ ∈ SV.S ] (⟨ γ ∈ˢ lam ⟩
           × ⟨ a ∈ˢ Lset γ ⟩ × ⟨ b ∈ˢ Lset γ ⟩)
       → ⟨ pr a b ∈ˢ Lset lam ⟩
    go (γ , γ∈ , a∈γ , b∈γ) =
      Lset-mono (succλ (sucV γ) (succλ γ γ∈)) (pr∈Lset-suc γ a b a∈γ b∈γ)

  -- ===================================================================
  -- SECTION 2.  THE COUNT.  Each code is encoded as a SET of the stage,
  --   base m            ↦  pr ∅ (pr ⟪X⟫↪ m ∅)
  --   wit k ψ cs        ↦  pr (sucV ∅) (pr (# k) (pr (# code ψ) (encVec cs)))
  --   encVec []         ↦  ∅
  --   encVec (c ∷ cs)   ↦  pr (sucV (sucV ∅)) (pr (enc c) (encVec cs))
  -- with the three tags # 0, # 1, # 2 kept apart by pr-inj and
  -- ∅ ≢ sucV ∅.  Injectivity of the formula slot is Count's own
  -- (shape-count-inj, src/FOL/Count.lagda.md:211-213), consumed exactly
  -- as the seventeen's CodeCount consumed it
  -- (src/L/BoundedSubset.lagda.md:1483-1500): the arity alignment is
  -- the same dance, at pr and # in place of B.pair and B.numeral.
  -- ===================================================================

  mutual
    enc : Code → SV.S
    enc (DR.H.T.base m) =
      pr ∅ (pr (⟪ X ⟫↪ m) ∅)
    enc (DR.H.T.wit k ψ cs) =
      pr (sucV ∅) (pr (# k) (pr (# code ψ) (encVec cs)))

    encVec : {k : ℕ} → Vec Code k → SV.S
    encVec [] = ∅
    encVec (c ∷ cs) = pr (sucV (sucV ∅)) (pr (enc c) (encVec cs))

  ⟪X⟫↪∈Lλ : (m : ⟪ X ⟫) → ⟨ ⟪ X ⟫↪ m ∈ˢ Lset lam ⟩
  ⟪X⟫↪∈Lλ m = X⊆Lλ (⟪ X ⟫↪ m) (member X m)

  mutual
    enc∈ : (c : Code) → ⟨ enc c ∈ˢ Lset lam ⟩
    enc∈ (DR.H.T.base m) =
      pr∈Lλ ∅ (pr (⟪ X ⟫↪ m) ∅) ∅∈Lλ
        (pr∈Lλ (⟪ X ⟫↪ m) ∅ (⟪X⟫↪∈Lλ m) ∅∈Lλ)
    enc∈ (DR.H.T.wit k ψ cs) =
      pr∈Lλ (sucV ∅) (pr (# k) (pr (# code ψ) (encVec cs)))
        (#∈Lλ 1)
        (pr∈Lλ (# k) (pr (# code ψ) (encVec cs)) (#∈Lλ k)
           (pr∈Lλ (# code ψ) (encVec cs) (#∈Lλ (code ψ)) (encVec∈ cs)))

    encVec∈ : {k : ℕ} (cs : Vec Code k) → ⟨ encVec cs ∈ˢ Lset lam ⟩
    encVec∈ [] = ∅∈Lλ
    encVec∈ (c ∷ cs) =
      pr∈Lλ (sucV (sucV ∅)) (pr (enc c) (encVec cs)) (#∈Lλ 2)
        (pr∈Lλ (enc c) (encVec cs) (enc∈ c) (encVec∈ cs))

  -- the tags are distinct, and the terminator is not a cons
  ∅≢sucV∅ : ∅ ≡ sucV ∅ → Empty.⊥
  ∅≢sucV∅ e = ∅-empty ∅ (∈∈ₛ {a = ∅} {b = ∅} .fst ∅∈∅)
    where
    ∅∈∅ : ⟨ ∅ ∈ˢ ∅ ⟩
    ∅∈∅ = subst (λ w → ⟨ ∅ ∈ˢ w ⟩) (sym e) (self∈sucV ∅)

  code-stable : (k k' : ℕ) (p : k' ≡ k) (ψ : Formula (⊥* {ℓ}) (suc k'))
              → code (subst (λ j → Formula (⊥* {ℓ}) (suc j)) p ψ) ≡ code ψ
  code-stable k k' p ψ =
    J (λ k p → code (subst (λ j → Formula (⊥* {ℓ}) (suc j)) p ψ) ≡ code ψ)
      (cong code (transportRefl ψ)) p

  encVec-stable : (k k' : ℕ) (p : k' ≡ k) (cs : Vec Code k')
                → encVec (subst (Vec Code) p cs) ≡ encVec cs
  encVec-stable k k' p cs =
    J (λ k p → encVec (subst (Vec Code) p cs) ≡ encVec cs)
      (cong encVec (transportRefl cs)) p

  mutual
    encVec-inj : (j : ℕ) (cs ds : Vec Code j)
               → encVec cs ≡ encVec ds → cs ≡ ds
    encVec-inj zero [] [] e = refl
    encVec-inj (suc j) (c ∷ cs) (d ∷ ds) e =
      cong₂ _∷_ (enc-inj c d (pr-inj (pr-inj e .snd) .fst))
        (encVec-inj j cs ds (pr-inj (pr-inj e .snd) .snd))

    enc-inj : (c d : Code) → enc c ≡ enc d → c ≡ d
    enc-inj (DR.H.T.base m) (DR.H.T.base m') e =
      cong DR.H.T.base (↪-inj {a = X} (pr-inj (pr-inj e .snd) .fst))
    enc-inj (DR.H.T.base m) (DR.H.T.wit k' ψ' cs') e =
      Empty.rec (∅≢sucV∅ (pr-inj e .fst))
    enc-inj (DR.H.T.wit k ψ cs) (DR.H.T.base m') e =
      Empty.rec (∅≢sucV∅ (sym (pr-inj e .fst)))
    enc-inj (DR.H.T.wit k ψ cs) (DR.H.T.wit k' ψ' cs') e = wit-eq
      where
      e₂ : pr (# k) (pr (# code ψ) (encVec cs))
         ≡ pr (# k') (pr (# code ψ') (encVec cs'))
      e₂ = pr-inj e .snd
      pk : k ≡ k'
      pk = #-inj k k' (pr-inj e₂ .fst)
      e₄ : pr (# code ψ) (encVec cs) ≡ pr (# code ψ') (encVec cs')
      e₄ = pr-inj e₂ .snd
      e-code : code ψ ≡ code ψ'
      e-code = #-inj (code ψ) (code ψ') (pr-inj e₄ .fst)
      e-vec : encVec cs ≡ encVec cs'
      e-vec = pr-inj e₄ .snd
      ψ₀ : Formula (⊥* {ℓ}) (suc k)
      ψ₀ = subst (λ j → Formula (⊥* {ℓ}) (suc j)) (sym pk) ψ'
      sψ : ψ ≡ ψ₀
      sψ = snd shape-count-inj {k = suc k} {φ = ψ} {ψ = ψ₀}
             (e-code ∙ sym (code-stable k k' (sym pk) ψ'))
      qψ : PathP (λ i → Formula (⊥* {ℓ}) (suc (pk i))) ψ ψ'
      qψ = toPathP (cong (subst (λ j → Formula (⊥* {ℓ}) (suc j)) pk) sψ
                     ∙ substSubst⁻ (λ j → Formula (⊥* {ℓ}) (suc j)) pk ψ')
      cs₀ : Vec Code k
      cs₀ = subst (Vec Code) (sym pk) cs'
      scs : cs ≡ cs₀
      scs = encVec-inj k cs cs₀ (e-vec ∙ sym (encVec-stable k k' (sym pk) cs'))
      qcs : PathP (λ i → Vec Code (pk i)) cs cs'
      qcs = toPathP (cong (subst (Vec Code) pk) scs
                     ∙ substSubst⁻ (Vec Code) pk cs')
      wit-eq : DR.H.T.wit k ψ cs ≡ DR.H.T.wit k' ψ' cs'
      wit-eq = cong (λ w → DR.H.T.wit (fst w) (fst (snd w)) (snd (snd w)))
        (ΣPathP {A = λ _ → ℕ}
                {B = λ i k → Formula (⊥* {ℓ}) (suc k) × Vec Code k}
                (pk , ΣPathP {A = λ i → Formula (⊥* {ℓ}) (suc (pk i))}
                            {B = λ i _ → Vec Code (pk i)}
                            (qψ , qcs)))

  -- the count, and its injectivity
  cnt : Code → DR.ASt.SL
  cnt c = enc c , enc∈ c

  cnt-inj : (c d : Code) → cnt c ≡ cnt d → c ≡ d
  cnt-inj c d e = enc-inj c d (cong fst e)

  -- ===================================================================
  -- SECTION 3.  THE SELECTION.  CanonCode's least-of-the-class pattern
  --   (src/L/BoundedSubset.lagda.md:463-507), restated at the stage's
  --   own carrier SL and its delivered L-order wL in place of the
  --   ordinal presentation ⟪ α ⟫, and canonicalising over the hull's
  --   member type directly instead of over its presentation.  The body
  --   is the tree's own shape, clause for clause.
  -- ===================================================================

  cls : DR.SM → DR.ASt.SL → hProp (ℓ-suc ℓ)
  cls q y = ( ∥ Σ[ c ∈ Code ] ((fst (DR.H.T.val c) ≡ fst q) × (cnt c ≡ y)) ∥₁
            , squash₁ )

  nonempty : (q : DR.SM) → ∥ Σ[ y ∈ DR.ASt.SL ] ⟨ cls q y ⟩ ∥₁
  nonempty q = PT.map (λ { (c , e) → cnt c , ∣ c , (e , refl) ∣₁ })
                      (DR.H.hull-member (fst q) (snd q))

  least : DR.SM → DR.ASt.SL
  least q = fst (leastOf wL lem (cls q) (nonempty q))

  least-sat : (q : DR.SM) → ⟨ cls q (least q) ⟩
  least-sat q = fst (snd (leastOf wL lem (cls q) (nonempty q)))

  isPropFib : (q : DR.SM)
            → isProp (Σ[ c ∈ Code ] ((fst (DR.H.T.val c) ≡ fst q)
                                   × (cnt c ≡ least q)))
  isPropFib q (c , e , p) (d , e' , p') =
    Σ≡Prop (λ c → isProp× (isSetS (fst (DR.H.T.val c)) (fst q))
                            (isSetSL (cnt c) (least q)))
      (cnt-inj c d (p ∙ sym p'))

  canonical : DR.SM → Code
  canonical q = fst (PT.rec (isPropFib q) (λ w → w) (least-sat q))

  canonical-spec : (q : DR.SM) → fst (DR.H.T.val (canonical q)) ≡ fst q
  canonical-spec q = fst (snd (PT.rec (isPropFib q) (λ w → w) (least-sat q)))

  -- ===================================================================
  -- SECTION 4.  THE ASSEMBLY, AND IT IS ONE LINE OF NEW MATHEMATICS.
  --   The tree's six-slot converter (HullElemDown.WithCode,
  --   src/L/BoundedSubset.lagda.md:681-682) turns the section into
  --   ElemDown; the seventeen's delivery is this same converter at the
  --   forced carrier (src/L/BoundedSubset.lagda.md:1533-1552).
  -- ===================================================================

  module HEDC = HED.WithCode canonical canonical-spec

  elem-down-at-six : DR.ElemDown
  elem-down-at-six = HEDC.elem-down

-- =====================================================================
-- THE OBLIGATION, HOISTED.  The six slots and face E in ONE telescope,
-- so the name `elem-down-at` sits at the probe's top level and the
-- witness meter's term-reference form reaches it, exactly as
-- [LJ-1.606] hoisted its own obligation (Probe606.agda:296-313).
-- =====================================================================

elem-down-at
  : (lam : SV.S) (ordλ : IsOrd lam)
    (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
    (X : SV.S)
    (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
    (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  → P606.Frame.ElemDownAt lam ordλ succλ X X⊆Lλ ∅∈λ
elem-down-at lam ordλ succλ X X⊆Lλ ∅∈λ =
  Six.elem-down-at-six lam ordλ succλ X X⊆Lλ ∅∈λ

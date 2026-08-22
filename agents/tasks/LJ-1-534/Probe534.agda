{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.534] The frame the honest forms want, and whether it is satisfiable.
--
-- THE COLLECTED FRAME IS A PRODUCT AND NOT A RECORD, AND THAT IS MEASURED.
-- Four earlier runs stated the same eight hypotheses as a `record` and every
-- one exhausted the 8 GB heap: runs/W3.agda.wall.txt (132.91 s),
-- runs/W3b.agda (116.63 s), runs/R.agda (104.43 s, the record ALONE) and
-- runs/F.agda (100.26 s, eight ONE-field records).  runs/I.agda is the same
-- import set with no type at all and is 1.04 s green; runs/T.agda is this
-- file's `HonestFrame`, token for token, and is 1.14 s green.  That is P-x
-- (src/L/Condensation/TwelveAgree.lagda.md:126-128) measured again at this
-- site: `sucV`, `pr` and `finSet` in a record FIELD type wall, and the same
-- tokens in an ordinary definition do not.
--
-- REBUILT, NOT IMPORTED.  `pr-self-not-numeral` and its three library steps
-- are `[LJ-1.507]`'s (agents/tasks/LJ-1-507/Probe507.agda:97-127) and are
-- restated here, because a probe is not importable and a measured cure does
-- not transfer by analogy (AGENTS.md:45).
--
-- Nothing is postulated.  Nothing lands in src/.
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber, set
-- on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-534.Probe534 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL-trans; IsOrd; Lset; isTransV; Lset-layer; layer-trans )
open import L.Axioms.Basic {ℓ} using ( LsetS; isL-Lset; finSet )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Ordinal {ℓ} using ( numeral-ord )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst )
open import L.Coding.EnvSet {ℓ} lem using ( module Generic )
open import L.Coding.EnvSupply {ℓ} lem
  using ( module SupplyEnv; module SupplyMerge )
open import L.Condensation {ℓ} lem using ( module KValue; module KFactsNS )
open import Cubical.Data.Nat using ( ℕ; _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅; ⁅_,_⁆; ⁅_⁆s; pairing-ax
        ; SingletonPackage; SetPackage )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open InfinitySet {ℓ} using ( #_; sucV; ω )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

-- =====================================================================
-- THE K SLOT AND THE CARRIER SLOT, at TFacts's own index convention.
--
-- `TFacts`'s `K` parameter lives in `Fin (5 + n)` and every field reads it
-- through six `suc`s over an `S ^ (11 + n)`
-- (src/L/Condensation/TwelveAgree.lagda.md:129-133).  The rows read their
-- CARRIER at slot zero of that same vector: `envK-mem`'s `bi` is
-- `suc (suc (suc (suc (suc (suc zero)))))` over `E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ'`
-- (TwelveAgree.lagda.md:186-191), which is `lookup zero γ'`.
-- =====================================================================

Kslot : {n : ℕ} → Fin (5 + n) → Vec S (11 + n) → S
Kslot K γ = lookup (suc (suc (suc (suc (suc (suc K)))))) γ

-- =====================================================================
-- THE COLLECTED FRAME.
--
-- Every conjunct is an extra hypothesis that some honest form of
-- `src/L/Coding/EnvSupply.lagda.md` takes and the matching `TFacts` field
-- does not carry.  In order:
--
--  1 Ktr       `module Fact`'s own second parameter, EnvSupply.lagda.md:450
--  2 TK        the VALUE TABLE slot's membership.  `valK` :462, `valK-un`
--              :471, `subK₁-and` :497, `subK₀-and` :508, `subK₁-imp` :519,
--              `subK₀-imp` :530, `subK-neg` :541, `subK-un` :552,
--              `subK-allin` :563.  Nine forms take it.
--  3 numK0     `EnvClosure` :673
--  4 sucK      `EnvClosure` :674
--  5 pairK     `EnvClosure` :675
--  6 finSetK   `EnvClosure` :676-677
--  7 carrier≡  `envK-gen` :278 and `envInK-gen` :352 take `lookup bi γ ≡ B₀`
--  8 envSetK   `envSetK` :140-143, PINNED to `B₀`
--
-- `ConsK`'s `envConsK` (:627-629) is NOT a ninth: `EnvClosure` :672-700
-- builds it from 3, 4, 5 and 6.
--
-- The per-application memberships (`zK`, `aK`, `bK`, `xK`, `yaK`, `eK`,
-- `tK`) are deliberately absent.  They bind a ROW's own variable, and
-- TwelveAgree.lagda.md:356-358 rules that they are the rows' binders and
-- not frame hypotheses (C-38).  A uniform version of any of them would say
-- every value of `S` lies in `K`, and would be false.
-- =====================================================================

HonestFrame : {n : ℕ} (A K : Fin (5 + n)) (γ : Vec S (11 + n))
            → Type (ℓ-suc ℓ)
HonestFrame A K γ =
    isTransV (fst (Kslot K γ))
  × ⟨ fst (lookup (suc zero) γ) ∈ fst (Kslot K γ) ⟩
  × ⟨ # 0 ∈ fst (Kslot K γ) ⟩
  × ((a : V ℓ) → ⟨ a ∈ fst (Kslot K γ) ⟩ → ⟨ sucV a ∈ fst (Kslot K γ) ⟩)
  × ((a b : V ℓ) → ⟨ a ∈ fst (Kslot K γ) ⟩ → ⟨ b ∈ fst (Kslot K γ) ⟩
       → ⟨ pr a b ∈ fst (Kslot K γ) ⟩)
  × ((m : ℕ) (h : Fin m → V ℓ)
       → ((i : Fin m) → ⟨ h i ∈ fst (Kslot K γ) ⟩)
       → ⟨ finSet m h ∈ fst (Kslot K γ) ⟩)
  × (lookup zero γ ≡ lookup (suc (suc (suc (suc (suc (suc A)))))) γ)
  × ((ar : S) (m : ℕ) → fst ar ≡ # m
       → ⟨ fst ar ∈ fst (Kslot K γ) ⟩
       → ⟨ fst (Generic.envSetGen (lookup zero γ) ar) ∈ fst (Kslot K γ) ⟩)

-- The two conjuncts the refutation below reads back out.
-- `HonestFrame` is a DEFINITION and not a record, so its arguments are not
-- recoverable by unification.  Both accessors take them explicitly.
frame-numK0 : {n : ℕ} (A K : Fin (5 + n)) (γ : Vec S (11 + n))
            → HonestFrame A K γ → ⟨ # 0 ∈ fst (Kslot K γ) ⟩
frame-numK0 A K γ hf = hf .snd .snd .fst

frame-pairK : {n : ℕ} (A K : Fin (5 + n)) (γ : Vec S (11 + n))
            → HonestFrame A K γ
            → (a b : V ℓ) → ⟨ a ∈ fst (Kslot K γ) ⟩ → ⟨ b ∈ fst (Kslot K γ) ⟩
            → ⟨ pr a b ∈ fst (Kslot K γ) ⟩
frame-pairK A K γ hf = hf .snd .snd .snd .snd .fst

-- =====================================================================
-- W3.  ONE INHABITANT, at KValue's frame.
--
-- The telescope is `KValue`'s (src/L/Condensation.lagda.md:7380-7383) plus
-- `ω∈γ`, which is `SupplyEnv`'s eighth parameter
-- (src/L/Coding/EnvSupply.lagda.md:111).  Seven of SupplyEnv's eight
-- parameters ARE KValue's telescope, term for term; `ω∈γ` is the eighth and
-- `[LJ-1.491]` already carried it into the frame
-- (agents/tasks/LJ-1-495/Probe495.agda:91, in the form `⟨ ω ∈ gam ⟩`).
-- This file takes the chapter's own weaker form, `⟨ ω ∈ sucV gam ⟩`.
-- =====================================================================

module Frame
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  (ω∈γ : ⟨ ω ∈ sucV gam ⟩) where

  module KV = KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  open KFactsNS.KFacts KV.facts using ()
    renaming ( numK0 to kNumK0 ; pairK to kPairK )

  -- `SupplyEnv.B₀` is `LsetS gam ordγ`
  -- (src/L/Coding/EnvSupply.lagda.md:124-125), so this is the same term.
  B₀ : S
  B₀ = LsetS gam ordγ

  z0 : S
  z0 = numeralL 0

  -- The six conses `[LJ-1.495]` left free
  -- (agents/tasks/LJ-1-495/Probe495.agda:166-169).  Slot zero is the rows'
  -- carrier and takes `B₀`; slot one is the value table and takes a member
  -- of the level.  The other four are read by no conjunct of the frame.
  γ₆ : Vec S 20
  γ₆ = B₀ ∷ z0 ∷ z0 ∷ z0 ∷ z0 ∷ z0 ∷ KV.Kenv

  -- The V-level pair closure, from KFacts's own S-level `pairK`.  A member
  -- of `Lset lam` is an L-set, so the two levels are interderivable here.
  pairK-V : (a b : V ℓ) → ⟨ a ∈ Lset lam ⟩ → ⟨ b ∈ Lset lam ⟩
          → ⟨ pr a b ∈ Lset lam ⟩
  pairK-V a b ha hb =
    subst (λ w → ⟨ w ∈ Lset lam ⟩) (prʟ-fst aS bS) (kPairK aS bS ha hb)
    where
    aS : S
    aS = a , isL-trans {x = Lset lam} {y = a} ha (isL-Lset lam ordλ)
    bS : S
    bS = b , isL-trans {x = Lset lam} {y = b} hb (isL-Lset lam ordλ)

  honest-frame-inhabited : HonestFrame {n = 9} KV.iA KV.iK γ₆
  honest-frame-inhabited =
      layer-trans (Lset-layer lam)
    , kNumK0
    , subst (λ w → ⟨ w ∈ Lset lam ⟩) (numeralL-fst 0) kNumK0
    , SupplyEnv.sucK lam ordλ succλ ∅∈λ gam ordγ γ∈λ ω∈γ
    , pairK-V
    , SupplyMerge.finSetK lam ordλ succλ ∅∈λ
    , refl
    , SupplyEnv.envSetK lam ordλ succλ ∅∈λ gam ordγ γ∈λ ω∈γ

-- =====================================================================
-- A SELF-PAIR IS NOT A NUMERAL.  `[LJ-1.507]`'s block
-- (agents/tasks/LJ-1-507/Probe507.agda:97-127), restated here.  `V.Coding`
-- keeps the first three `private` (src/V/Coding.lagda.md:136), so they are
-- rebuilt from `pairing-ax` and `SingletonPackage` directly.
-- =====================================================================

self∈singlV : (a : V ℓ) → ⟨ a ∈ ⁅ a ⁆s ⟩
self∈singlV a = ∈∈ₛ {a = a} {b = ⁅ a ⁆s} .snd
  (SetPackage.classification (SingletonPackage a) a .snd refl)

self∈pairV : (a b : V ℓ) → ⟨ a ∈ ⁅ a , b ⁆ ⟩
self∈pairV a b = ∈∈ₛ {a = a} {b = ⁅ a , b ⁆} .snd
  (pairing-ax a b a .snd PT.∣ Sum.inl refl ∣₁)

singl∈prV : (a b : V ℓ) → ⟨ ⁅ a ⁆s ∈ pr a b ⟩
singl∈prV a b = ∈∈ₛ {a = ⁅ a ⁆s} {b = pr a b} .snd
  (pairing-ax ⁅ a ⁆s ⁅ a , b ⁆ ⁅ a ⁆s .snd PT.∣ Sum.inl refl ∣₁)

mem-prV : (a b x : V ℓ) → ⟨ x ∈ pr a b ⟩
        → ∥ (x ≡ ⁅ a ⁆s) Sum.⊎ (x ≡ ⁅ a , b ⁆) ∥₁
mem-prV a b x h =
  pairing-ax ⁅ a ⁆s ⁅ a , b ⁆ x .fst (∈∈ₛ {a = x} {b = pr a b} .fst h)

pr-self-not-ord : (a : V ℓ) → IsOrd (pr a a) → Empty.⊥
pr-self-not-ord a (tr , _) =
  PT.rec Empty.isProp⊥
    (Sum.rec
      (λ e → ∈-irrefl a (subst (λ w → ⟨ a ∈ w ⟩) (sym e) (self∈singlV a)))
      (λ e → ∈-irrefl a (subst (λ w → ⟨ a ∈ w ⟩) (sym e) (self∈pairV a a))))
    (mem-prV a a a (tr (self∈singlV a) (singl∈prV a a)))

pr-self-not-numeral : (a : V ℓ) (m : ℕ) → pr a a ≡ (# m) → Empty.⊥
pr-self-not-numeral a m p =
  pr-self-not-ord a (subst IsOrd (sym p) (numeral-ord m))

-- =====================================================================
-- THE ONE HYPOTHESIS THAT CANNOT JOIN THE FRAME.
--
-- `SupplyEnv.someEnv` (src/L/Coding/EnvSupply.lagda.md:417-424) takes a
-- NUMERAL arity, `:418`.  The record field it would fill is
-- `someEnv : someEnvDef {n} K γ'` (TwelveAgree.lagda.md:289), and
-- `someEnvDef` (src/L/Condensation/LowerAgree.lagda.md:52-58) binds `ar`
-- with `⟨ fst ar ∈ K ⟩` and nothing else.  So filling that field asks for
-- the arity hypothesis UNIFORMLY over `K`.
--
-- That uniform form is refuted by the collected frame's OWN conjuncts 3
-- and 5.  `[LJ-1.507]` refuted the same shape at `[LJ-1.504]`'s frame with
-- `KValue.facts` in hand; the statement below needs no frame at all, only
-- the two conjuncts, so it holds at every site the collected frame does.
-- =====================================================================

ArNumUniform : {n : ℕ} (K : Fin (5 + n)) (γ : Vec S (11 + n))
             → Type (ℓ-suc ℓ)
ArNumUniform K γ = (ar : S) → ⟨ fst ar ∈ fst (Kslot K γ) ⟩
                 → ∥ Σ[ m ∈ ℕ ] (fst ar ≡ # m) ∥₁

arNum-uniform-conflicts :
    {n : ℕ} (A K : Fin (5 + n)) (γ : Vec S (11 + n))
  → HonestFrame A K γ → ArNumUniform K γ → Empty.⊥
arNum-uniform-conflicts A K γ hf arNum =
  PT.rec Empty.isProp⊥
    (λ { (m , e) → pr-self-not-numeral (# 0) m (sym chain ∙ e) })
    (arNum bad bad∈K)
  where
  z0 : S
  z0 = numeralL 0

  bad : S
  bad = prʟ z0 z0

  chain : fst bad ≡ pr (# 0) (# 0)
  chain = prʟ-fst z0 z0 ∙ cong₂ pr (numeralL-fst 0) (numeralL-fst 0)

  bad∈K : ⟨ fst bad ∈ fst (Kslot K γ) ⟩
  bad∈K = subst (λ w → ⟨ w ∈ fst (Kslot K γ) ⟩) (sym chain)
            (frame-pairK A K γ hf (# 0) (# 0)
              (frame-numK0 A K γ hf) (frame-numK0 A K γ hf))

honest-frame-inhabited = Frame.honest-frame-inhabited

# The elementarity of the hull at a counted start

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.HullElem {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Count
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL-trans; IsOrd; Lset )
open import L.Ordinal {ℓ} using ( #∈ω )
open import L.Ordinal.SquareLaw {ℓ} lem using ( ordSWO )
open import L.Cardinal {ℓ} lem using ( _↪_ )
open import L.GCH.Pairing {ℓ} lem using ( prodL; prodL-in; ω⊆ )
open import L.GCH.Hull {ℓ} lem using ( module CanonCode; module HullElemDown )

open import Cubical.Data.Nat.Properties using ( znots; snotz; injSuc )
open import Cubical.Data.Sigma using ( _×_; ΣPathP )
open import Cubical.Foundations.Prelude using ( J; toPathP; PathP; transportRefl )
open import Cubical.Foundations.Transport using ( substSubst⁻ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( #_; ω )
open import Cubical.Data.Vec using ( Vec; _∷_; [] )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- THE SITE.  A stage λ, a start X ⊆ L_λ, and an infinite L-cardinal κ
-- with the ambient pairing on κ and an ambient injection X ↪ κ.
-- Each hull member needs a
-- canonical code; `CanonCode` picks it by the
-- least count under κ's own well-order, and the count is the term
-- algebra's code count at the pairing and the injection.
--
-- One export, `elem`.  This module is instantiated once per site, so
-- the whole instantiation of `HullElemDown` sits here and the
-- consumer stores one definition.
-- =====================================================================

module Elem (κ : S) (oκ : IsOrd (fst κ)) (κ∉ω : ⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  (lam : V ℓ) (ordλ : IsOrd lam)
  (X : V ℓ) (X⊆Lλ : (x : V ℓ) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩) (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (pκ : ⟪ fst (prodL κ) ⟫ ↪ ⟪ fst κ ⟫)
  (g : ⟪ X ⟫ ↪ ⟪ fst κ ⟫) where

  num∈κ : (k : ℕ) → ⟨ # k ∈ fst κ ⟩
  num∈κ k = ω⊆ (fst κ) oκ κ∉ω (# k) (#∈ω k)

  -- The telescope of `HullElemDown`, spelled once; each application
  -- takes only the names this file reads.
  module HED = HullElemDown lam ordλ X X⊆Lλ ∅∈λ using ( M )
  module HT = HullElemDown.H.T lam ordλ X X⊆Lλ ∅∈λ using ( Code; base; wit; val )
  module HA = HullElemDown.A lam ordλ X X⊆Lλ ∅∈λ using ( SM; Elementary )
  module HH = HullElemDown.H lam ordλ X X⊆Lλ ∅∈λ using ( hull-member )

  up : ⟪ fst κ ⟫ → S
  up m = ⟪ fst κ ⟫↪ m , isL-trans {x = fst κ} {y = ⟪ fst κ ⟫↪ m} (member (fst κ) m) (snd κ)

  toProd : ⟪ fst κ ⟫ → ⟪ fst κ ⟫ → ⟪ fst (prodL κ) ⟫
  toProd a b = fiber (fst (prodL κ)) (prodL-in κ (up a) (up b) (member (fst κ) a) (member (fst κ) b)) .fst

  toProd-fst : (a b : ⟪ fst κ ⟫)
             → ⟪ fst (prodL κ) ⟫↪ (toProd a b) ≡ pr (⟪ fst κ ⟫↪ a) (⟪ fst κ ⟫↪ b)
  toProd-fst a b = fiber (fst (prodL κ)) (prodL-in κ (up a) (up b) (member (fst κ) a) (member (fst κ) b)) .snd

  pair : ⟪ fst κ ⟫ → ⟪ fst κ ⟫ → ⟪ fst κ ⟫
  pair a b = pκ .fst (toProd a b)

  pair-inj : (a b a' b' : ⟪ fst κ ⟫) → pair a b ≡ pair a' b' → (a ≡ a') × (b ≡ b')
  pair-inj a b a' b' e = ↪-inj {a = fst κ} (fst q) , ↪-inj {a = fst κ} (snd q)
    where
    q : (⟪ fst κ ⟫↪ a ≡ ⟪ fst κ ⟫↪ a') × (⟪ fst κ ⟫↪ b ≡ ⟪ fst κ ⟫↪ b')
    q = pr-inj (sym (toProd-fst a b) ∙ cong ⟪ fst (prodL κ) ⟫↪ (pκ .snd _ _ e) ∙ toProd-fst a' b')

  numeral : ℕ → ⟪ fst κ ⟫
  numeral n = fiber (fst κ) (num∈κ n) .fst

  numeral-inj : (n m : ℕ) → numeral n ≡ numeral m → n ≡ m
  numeral-inj n m e = #-inj n m
    (sym (fiber (fst κ) (num∈κ n) .snd) ∙ cong ⟪ fst κ ⟫↪ e ∙ fiber (fst κ) (num∈κ m) .snd)

  -- The code count of the term algebra, at the stage-cardinal bound.
  module CodeCount where

    Code : Type ℓ
    Code = HT.Code

    code-stable-suc : (k k' : ℕ) (p : k' ≡ k) (ψ : Formula (⊥* {ℓ}) (suc k'))
                    → FOL.Count.code (subst (λ j → Formula (⊥* {ℓ}) (suc j)) p ψ)
                      ≡ FOL.Count.code ψ
    code-stable-suc k k' p ψ =
      J (λ k p → FOL.Count.code (subst (λ j → Formula (⊥* {ℓ}) (suc j)) p ψ)
                 ≡ FOL.Count.code ψ)
        (cong FOL.Count.code (transportRefl ψ)) p

    mutual
      count : Code → ⟪ fst κ ⟫
      count (HT.base m) = pair (numeral 0) (fst g m)
      count (HT.wit k ψ cs) =
        pair (numeral (suc k))
          (pair (pair (numeral (FOL.Count.code ψ)) (numeral (suc k)))
            (tuple k cs))

      tuple : (j : ℕ) → Vec Code j → ⟪ fst κ ⟫
      tuple zero [] = numeral 0
      tuple (suc j) (c ∷ cs) = pair (count c) (tuple j cs)

      tuple-inj : (j : ℕ) (cs ds : Vec Code j) → tuple j cs ≡ tuple j ds → cs ≡ ds
      tuple-inj zero [] [] e = refl
      tuple-inj (suc j) (c ∷ cs) (d ∷ ds) e =
        cong₂ (λ (x : Code) (y : Vec Code j) → x ∷ y) hc hcs
        where
        p : (count c ≡ count d) × (tuple j cs ≡ tuple j ds)
        p = pair-inj (count c) (tuple j cs) (count d) (tuple j ds) e
        hc : c ≡ d
        hc = count-inj c d (fst p)
        hcs : cs ≡ ds
        hcs = tuple-inj j cs ds (snd p)

      tuple-stable : (j j' : ℕ) (p : j' ≡ j) (cs : Vec Code j')
                   → tuple j (subst (Vec Code) p cs) ≡ tuple j' cs
      tuple-stable j j' p cs =
        J (λ j p → tuple j (subst (Vec Code) p cs) ≡ tuple j' cs)
          (cong (tuple j') (transportRefl cs)) p

      count-inj : (c d : Code) → count c ≡ count d → c ≡ d
      count-inj (HT.base m) (HT.base m') e =
        cong HT.base (snd g m m' (pair-inj _ _ _ _ e .snd))
      count-inj (HT.base m) (HT.wit k' ψ' cs') e =
        Empty.rec (znots (numeral-inj 0 (suc k') (pair-inj _ _ _ _ e .fst)))
      count-inj (HT.wit k ψ cs) (HT.base m') e =
        Empty.rec (snotz (numeral-inj (suc k) 0 (pair-inj _ _ _ _ e .fst)))
      count-inj (HT.wit k ψ cs) (HT.wit k' ψ' cs') e = wit-eq
        where
        e-out : (numeral (suc k) ≡ numeral (suc k'))
              × (pair (pair (numeral (FOL.Count.code ψ)) (numeral (suc k))) (tuple k cs)
                ≡ pair (pair (numeral (FOL.Count.code ψ')) (numeral (suc k'))) (tuple k' cs'))
        e-out = pair-inj (numeral (suc k))
                    (pair (pair (numeral (FOL.Count.code ψ)) (numeral (suc k))) (tuple k cs))
                    (numeral (suc k'))
                    (pair (pair (numeral (FOL.Count.code ψ')) (numeral (suc k'))) (tuple k' cs'))
                    e
        psk : suc k ≡ suc k'
        psk = numeral-inj (suc k) (suc k') (fst e-out)
        pk : k ≡ k'
        pk = injSuc psk
        e-in : pair (pair (numeral (FOL.Count.code ψ)) (numeral (suc k))) (tuple k cs)
             ≡ pair (pair (numeral (FOL.Count.code ψ')) (numeral (suc k'))) (tuple k' cs')
        e-in = snd e-out
        e-fst : pair (numeral (FOL.Count.code ψ)) (numeral (suc k))
              ≡ pair (numeral (FOL.Count.code ψ')) (numeral (suc k'))
        e-fst = fst (pair-inj _ _ _ _ e-in)
        e-code : FOL.Count.code ψ ≡ FOL.Count.code ψ'
        e-code = numeral-inj (FOL.Count.code ψ) (FOL.Count.code ψ') (fst (pair-inj _ _ _ _ e-fst))
        e-tup : tuple k cs ≡ tuple k' cs'
        e-tup = snd (pair-inj _ _ _ _ e-in)
        ψ₀ : Formula (⊥* {ℓ}) (suc k)
        ψ₀ = subst (λ j → Formula (⊥* {ℓ}) (suc j)) (sym pk) ψ'
        sψ : ψ ≡ ψ₀
        sψ = snd FOL.Count.shape-count-inj {k = suc k} {φ = ψ} {ψ = ψ₀}
               (e-code ∙ sym (code-stable-suc k k' (sym pk) ψ'))
        qψ : PathP (λ i → Formula (⊥* {ℓ}) (suc (pk i))) ψ ψ'
        qψ = toPathP (cong (subst (λ j → Formula (⊥* {ℓ}) (suc j)) pk) sψ
                      ∙ substSubst⁻ (λ j → Formula (⊥* {ℓ}) (suc j)) pk ψ')
        cs₀ : Vec Code k
        cs₀ = subst (Vec Code) (sym pk) cs'
        scs : cs ≡ cs₀
        scs = tuple-inj k cs cs₀ (e-tup ∙ sym (tuple-stable k k' (sym pk) cs'))
        qcs : PathP (λ i → Vec Code (pk i)) cs cs'
        qcs = toPathP (cong (subst (Vec Code) pk) scs ∙ substSubst⁻ (Vec Code) pk cs')
        wit-eq : HT.wit k ψ cs ≡ HT.wit k' ψ' cs'
        wit-eq = cong (λ x → HT.wit (fst x) (fst (snd x)) (snd (snd x)))
          (ΣPathP {A = λ _ → ℕ} {B = λ i k → Formula (⊥* {ℓ}) (suc k) × Vec Code k}
                  (pk , ΣPathP {A = λ i → Formula (⊥* {ℓ}) (suc (pk i))}
                               {B = λ i _ → Vec Code (pk i)} (qψ , qcs)))

  module CC = CodeCount

  -- The canonical code of each hull member, and the elementarity.
  module CCn = CanonCode (fst κ) oκ (ordSWO (fst κ) oκ)
    HED.M HT.Code (λ c → fst (HT.val c)) HH.hull-member CC.count CC.count-inj
    using ( canonical; canonical-spec )

  hedF : HA.SM → HT.Code
  hedF q = CCn.canonical (fiber HED.M (snd q) .fst)

  hedF-spec : (q : HA.SM) → fst (HT.val (hedF q)) ≡ fst q
  hedF-spec q = go (fiber HED.M (snd q))
    where
    go : (f : Σ[ m ∈ ⟪ HED.M ⟫ ] (⟪ HED.M ⟫↪ m ≡ fst q))
       → fst (HT.val (CCn.canonical (f .fst))) ≡ fst q
    go f = CCn.canonical-spec (f .fst) ∙ f .snd

  elem : HA.Elementary
  elem = HullElemDown.WithCode.elem lam ordλ X X⊆Lλ ∅∈λ hedF hedF-spec
```

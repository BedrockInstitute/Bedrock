{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett; setIsSet )

module ProbeT249 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Term; con; var; Formula
        ; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.Relabelling using ( mapFo; mapTm )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import V.Coding {ℓ} using ( pr; pr-inj; #mono; module VCode )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-inl; ∈sucV-elim )
open import L.Constructible {ℓ} using ( IsOrd; Lset; isTransV )
open import L.Rank {ℓ} using ( rank; rank-mono; rank-ord )
open import L.Ordinal {ℓ} using ( ∈#-elim )
open import L.LevelKit {ℓ} using ( module LevelKit )
open import L.Rud.Ops {ℓ} using ( F0; F0-spec; F1-spec; F5-spec )
open import L.TowerKit {ℓ} lem A using ( ext-⊆ )
open import L.Rud.Step {ℓ} lem A
  using ( f0; f1; f5; f9; Fof; Fof-f0; Fof-f1; Fof-f5; Fof-f9; singl≡pair
        ; Sset; Sset-trans; Sset-mem; Jset-rud )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit )
open import L.Rud.OrdBlocks {ℓ} lem using ( +ω; +ω-limit; +ω-mem )
open import L.Rud.StepGraph {ℓ} lem A using ( module Desc )
open import L.Rud.SatSets {ℓ} lem A using ( module LimitFullSwitch )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.FinData.Properties using ( fromℕ'; toFromId'; toℕ<n )
open import Cubical.Data.Nat.Order using ( _<_; <-split; ¬-<-zero )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; ⁅_⁆s; _∪_; ⋃_; module InfinitySet )
open InfinitySet using ( sucV; #_ )
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- A sealed vocabulary of shapes: the pair, the numerals, the successor,
-- the singleton and the binary union, each with one equation.
opaque
  prS : S → S → S
  prS a b = pr a b

  numS : ℕ → S
  numS k = # k

  sucS : S → S
  sucS x = sucV x

  sglS : S → S
  sglS a = ⁅ a ⁆s

  cupS : S → S → S
  cupS a b = a ∪ b

  prS-pr : (a b : S) → prS a b ≡ pr a b
  prS-pr a b = refl

  numS-# : (k : ℕ) → numS k ≡ (# k)
  numS-# k = refl

  sucS-sucV : (x : S) → sucS x ≡ sucV x
  sucS-sucV x = refl

  sglS-sgl : (a : S) → sglS a ≡ ⁅ a ⁆s
  sglS-sgl a = refl

  cupS-cup : (a b : S) → cupS a b ≡ (a ∪ b)
  cupS-cup a b = refl

  numS-suc : (k : ℕ) → numS (suc k) ≡ sucS (numS k)
  numS-suc k = refl

  prS-inj : {a b c d : S} → prS a b ≡ prS c d → (a ≡ c) × (b ≡ d)
  prS-inj = pr-inj

-- Rank descends into a code: the three descents the recover recursion needs.
private
  pair∈ : (u v w : S) → ∥ (w ≡ u) ⊎ (w ≡ v) ∥₁ → ⟨ w ∈ˢ ⁅ u , v ⁆ ⟩
  pair∈ u v w h = F0-spec u v w .snd h

  self∈sgl : (a : S) → ⟨ a ∈ˢ ⁅ a ⁆s ⟩
  self∈sgl a = subst (λ w → ⟨ a ∈ˢ w ⟩) (sym (singl≡pair a))
    (pair∈ a a a ∣ inl refl ∣₁)

  trans≺ : (x y z : S) → ⟨ x ∈ˢ y ⟩ → ⟨ rank y ∈ˢ rank z ⟩
         → ⟨ rank x ∈ˢ rank z ⟩
  trans≺ x y z x∈y ry∈rz = rank-ord z .fst (rank-mono x y x∈y) ry∈rz

  chain4 : (x y z w v : S) → ⟨ x ∈ˢ y ⟩ → ⟨ y ∈ˢ z ⟩ → ⟨ z ∈ˢ w ⟩ → ⟨ w ∈ˢ v ⟩
         → ⟨ rank x ∈ˢ rank v ⟩
  chain4 x y z w v x∈y y∈z z∈w w∈v =
    trans≺ x y v x∈y (trans≺ y z v y∈z (trans≺ z w v z∈w (rank-mono w v w∈v)))

opaque
  unfolding prS

  payload≺ : (c z : S) → ⟨ rank z ∈ˢ rank (prS c z) ⟩
  payload≺ c z = trans≺ z ⁅ c , z ⁆ (pr c z)
    (pair∈ c z z ∣ inr refl ∣₁)
    (rank-mono ⁅ c , z ⁆ (pr c z)
      (pair∈ ⁅ c ⁆s ⁅ c , z ⁆ ⁅ c , z ⁆ ∣ inr refl ∣₁))

  leftPart : (c a b : S) → ⟨ rank a ∈ˢ rank (prS c (prS a b)) ⟩
  leftPart c a b = chain4 a ⁅ a ⁆s (pr a b) ⁅ c , pr a b ⁆ (pr c (pr a b))
    (self∈sgl a)
    (pair∈ ⁅ a ⁆s ⁅ a , b ⁆ ⁅ a ⁆s ∣ inl refl ∣₁)
    (pair∈ c (pr a b) (pr a b) ∣ inr refl ∣₁)
    (pair∈ ⁅ c ⁆s ⁅ c , pr a b ⁆ ⁅ c , pr a b ⁆ ∣ inr refl ∣₁)

  rightPart : (c a b : S) → ⟨ rank b ∈ˢ rank (prS c (prS a b)) ⟩
  rightPart c a b = chain4 b ⁅ a , b ⁆ (pr a b) ⁅ c , pr a b ⁆ (pr c (pr a b))
    (pair∈ a b b ∣ inr refl ∣₁)
    (pair∈ ⁅ a ⁆s ⁅ a , b ⁆ ⁅ a , b ⁆ ∣ inr refl ∣₁)
    (pair∈ c (pr a b) (pr a b) ∣ inr refl ∣₁)
    (pair∈ ⁅ c ⁆s ⁅ c , pr a b ⁆ ⁅ c , pr a b ⁆ ∣ inr refl ∣₁)

-- The code map and the arity-one family, over the carrier C.
module Codes (C : S) where

  ι : ⟪ C ⟫ → S
  ι = ⟪ C ⟫↪

  codeTm : ∀ {n} → Term ⟪ C ⟫ n → S
  codeTm t = VCode.⌜ mapTm ι t ⌝ᵗ

  code : ∀ {n} → Formula ⟪ C ⟫ n → S
  code φ = VCode.⌜ mapFo ι φ ⌝

  opaque
    codeSet : ℕ → S
    codeSet k = sett (Formula ⟪ C ⟫ k) code

    code∈codeSet : (k : ℕ) (φ : Formula ⟪ C ⟫ k) → ⟨ code φ ∈ˢ codeSet k ⟩
    code∈codeSet k φ = ∣ φ , refl ∣₁

    codeSet-out : (k : ℕ) (x : S) → ⟨ x ∈ˢ codeSet k ⟩
                → ∥ Σ[ φ ∈ Formula ⟪ C ⟫ k ] (code φ ≡ x) ∥₁
    codeSet-out k x h = h

-- The level arithmetic at a limit level: the pair, the empty set, the
-- successor and the numerals are members.
empty-rud : (a : S) → Fof f1 a a ≡ ∅
empty-rud a = ext-⊆ sub sup
  where
  sub : (x : S) → ⟨ x ∈ˢ Fof f1 a a ⟩ → ⟨ x ∈ˢ ∅ ⟩
  sub x h = Empty.rec (both .snd (both .fst))
    where
    both : ⟨ (x ∈ˢ a) ⊓ (¬ (x ∈ˢ a)) ⟩
    both = F1-spec a a x .fst (subst (λ w → ⟨ x ∈ˢ w ⟩) (Fof-f1 a a) h)
  sup : (x : S) → ⟨ x ∈ˢ ∅ ⟩ → ⟨ x ∈ˢ Fof f1 a a ⟩
  sup x h = Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst h))

singleton-rud : (x : S) → Fof f0 x x ≡ ⁅ x ⁆s
singleton-rud x = Fof-f0 x x ∙ sym (singl≡pair x)

sucV-rud : (x : S) → Fof f5 (Fof f0 x (Fof f0 x x)) x ≡ sucV x
sucV-rud x = Fof-f5 (Fof f0 x (Fof f0 x x)) x
  ∙ cong ⋃_ (Fof-f0 x (Fof f0 x x)
             ∙ cong (λ w → ⁅ x , w ⁆) (singleton-rud x))

module InLevel (γ : S) (limγ : ⟨ isLimit γ ⟩) where

  InJ : S → Type (ℓ-suc ℓ)
  InJ x = ⟨ x ∈ˢ Sset γ ⟩

  pr∈J : (a b : S) → InJ a → InJ b → InJ (pr a b)
  pr∈J a b ha hb = subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) (Fof-f9 a b)
    (Jset-rud γ limγ f9 a b ha hb)

  ∅∈J : (a : S) → InJ a → InJ ∅
  ∅∈J a ha = subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) (empty-rud a)
    (Jset-rud γ limγ f1 a a ha ha)

  sucV∈J : (x : S) → InJ x → InJ (sucV x)
  sucV∈J x hx = subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) (sucV-rud x)
    (Jset-rud γ limγ f5 (Fof f0 x (Fof f0 x x)) x
      (Jset-rud γ limγ f0 x (Fof f0 x x) hx
        (Jset-rud γ limγ f0 x x hx hx))
      hx)

  numeral∈J : (a : S) → InJ a → (k : ℕ) → InJ (# k)
  numeral∈J a ha zero    = ∅∈J a ha
  numeral∈J a ha (suc k) = sucV∈J (# k) (numeral∈J a ha k)

-- Every code is a member: the containment half at a limit level.
module Carrier (γ : S) (limγ : ⟨ isLimit γ ⟩)
               (C : S) (C∈ : ⟨ C ∈ˢ Sset γ ⟩) where

  open Codes C
  open InLevel γ limγ

  member∈J : (m : ⟪ C ⟫) → InJ (ι m)
  member∈J m = Sset-trans γ {x = C} {y = ι m}
    (∈∈ₛ {a = ι m} {b = C} .snd (∈ₛ⟪ C ⟫↪ m)) C∈

  numeralJ : (k : ℕ) → InJ (# k)
  numeralJ = numeral∈J C C∈

  mkTag∈J : (k : ℕ) (x : S) → InJ x → InJ (VCode.mkTag k x)
  mkTag∈J k x hx = pr∈J (# k) x (numeralJ k) hx

  codeTm∈J : ∀ {n} (t : Term ⟪ C ⟫ n) → InJ (codeTm t)
  codeTm∈J (con m) = mkTag∈J 0 (ι m) (member∈J m)
  codeTm∈J (var i) = mkTag∈J 1 (# (toℕ i)) (numeralJ (toℕ i))

  code∈J : ∀ {n} (φ : Formula ⟪ C ⟫ n) → InJ (code φ)
  code∈J (t ∈̇ u) = mkTag∈J 0 (pr (codeTm t) (codeTm u))
    (pr∈J (codeTm t) (codeTm u) (codeTm∈J t) (codeTm∈J u))
  code∈J (t ≐ u) = mkTag∈J 1 (pr (codeTm t) (codeTm u))
    (pr∈J (codeTm t) (codeTm u) (codeTm∈J t) (codeTm∈J u))
  code∈J (φ ∧̇ ψ) = mkTag∈J 2 (pr (code φ) (code ψ))
    (pr∈J (code φ) (code ψ) (code∈J φ) (code∈J ψ))
  code∈J (φ ∨̇ ψ) = mkTag∈J 3 (pr (code φ) (code ψ))
    (pr∈J (code φ) (code ψ) (code∈J φ) (code∈J ψ))
  code∈J (φ ⇒̇ ψ) = mkTag∈J 4 (pr (code φ) (code ψ))
    (pr∈J (code φ) (code ψ) (code∈J φ) (code∈J ψ))
  code∈J (¬̇ φ)    = mkTag∈J 5 (code φ) (code∈J φ)
  code∈J ⊤̇        = mkTag∈J 6 (# 0) (numeralJ 0)
  code∈J ⊥̇        = mkTag∈J 7 (# 0) (numeralJ 0)
  code∈J (∃̇ φ)    = mkTag∈J 8 (code φ) (code∈J φ)
  code∈J (∀̇ φ)    = mkTag∈J 9 (code φ) (code∈J φ)
  code∈J (∀̇∈ t φ) = mkTag∈J 10 (pr (codeTm t) (code φ))
    (pr∈J (codeTm t) (code φ) (codeTm∈J t) (code∈J φ))
  code∈J (∃̇∈ t φ) = mkTag∈J 11 (pr (codeTm t) (code φ))
    (pr∈J (codeTm t) (code φ) (codeTm∈J t) (code∈J φ))

  codeSet⊆J : (k : ℕ) (x : S) → ⟨ x ∈ˢ codeSet k ⟩ → InJ x
  codeSet⊆J k x h = PT.rec (snd (x ∈ˢ Sset γ))
    (λ { (φ , q) → subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) q (code∈J φ) })
    (codeSet-out k x h)

-- The reading frame at a transitive carrier: membership, the pair parts,
-- the inner-world point, the frame and its two decodes.
module Frame (W : S) (Wtr : isTransV W) where

  module K = LevelKit W Wtr
  open K using ( SM; _⊨ᵐ_; defSet; module PK ) public

  mem : (x y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ x ∈ˢ W ⟩ → ⟨ y ∈ˢ W ⟩
  mem x y y∈x x∈W = Wtr {x = x} {y = y} y∈x x∈W

  self∈singl : (p : S) → ⟨ p ∈ˢ ⁅ p ⁆s ⟩
  self∈singl p = subst (λ w → ⟨ p ∈ˢ w ⟩) (sym (singl≡pair p))
    (F0-spec p p p .snd ∣ inl refl ∣₁)

  prL∈ : (p q : S) → ⟨ pr p q ∈ˢ W ⟩ → ⟨ p ∈ˢ W ⟩
  prL∈ p q h = mem (⁅ p ⁆s) p (self∈singl p)
    (mem (pr p q) (⁅ p ⁆s) (F0-spec (⁅ p ⁆s) (⁅ p , q ⁆) (⁅ p ⁆s) .snd
      ∣ inl refl ∣₁) h)

  prR∈ : (p q : S) → ⟨ pr p q ∈ˢ W ⟩ → ⟨ q ∈ˢ W ⟩
  prR∈ p q h = mem (F0 p q) q (F0-spec p q q .snd ∣ inr refl ∣₁)
    (mem (pr p q) (F0 p q) (F0-spec (⁅ p ⁆s) (⁅ p , q ⁆) (⁅ p , q ⁆) .snd
      ∣ inr refl ∣₁) h)

  pt : (x : S) → ⟨ x ∈ˢ W ⟩ → SM
  pt = PK.pt

  entry∈ : {n : ℕ} (k : Fin n) (δ : Vec SM n) (z : S)
         → ⟨ z ∈ˢ fst (lookup k δ) ⟩ → ⟨ z ∈ˢ W ⟩
  entry∈ = PK.entry∈

  eqFrame : {n : ℕ} → Fin n → Formula ⟪ W ⟫ (suc n) → Formula ⟪ W ⟫ n
  eqFrame k M = (∀̇∈ (var k) M) ∧̇ (∀̇ (M ⇒̇ (var z0 ∈̇ var (suc k))))
    where
    z0 : {n : ℕ} → Fin (suc n)
    z0 = zero

  eqFrame-out : {n : ℕ} (k : Fin n) (M : Formula ⟪ W ⟫ (suc n))
                (δ : Vec SM n) (V : S)
              → ((v : S) → ⟨ v ∈ˢ V ⟩ → ⟨ v ∈ˢ W ⟩)
              → ((v : S) (v∈ : ⟨ v ∈ˢ W ⟩) → ⟨ (pt v v∈ ∷ δ) ⊨ᵐ M ⟩
                 → ⟨ v ∈ˢ V ⟩)
              → ((v : S) (v∈ : ⟨ v ∈ˢ W ⟩) → ⟨ v ∈ˢ V ⟩
                 → ⟨ (pt v v∈ ∷ δ) ⊨ᵐ M ⟩)
              → ⟨ δ ⊨ᵐ eqFrame k M ⟩ → fst (lookup k δ) ≡ V
  eqFrame-out k M δ V wsub mout min (h₁ , h₂) = ext-⊆ sub sup
    where
    sub : (x : S) → ⟨ x ∈ˢ fst (lookup k δ) ⟩ → ⟨ x ∈ˢ V ⟩
    sub x h = mout x (entry∈ k δ x h) (h₁ (pt x (entry∈ k δ x h)) h)
    sup : (x : S) → ⟨ x ∈ˢ V ⟩ → ⟨ x ∈ˢ fst (lookup k δ) ⟩
    sup x h = h₂ (pt x (wsub x h)) (min x (wsub x h) h)

  eqFrame-in : {n : ℕ} (k : Fin n) (M : Formula ⟪ W ⟫ (suc n))
               (δ : Vec SM n) (V : S)
             → ((v : S) → ⟨ v ∈ˢ V ⟩ → ⟨ v ∈ˢ W ⟩)
             → ((v : S) (v∈ : ⟨ v ∈ˢ W ⟩) → ⟨ (pt v v∈ ∷ δ) ⊨ᵐ M ⟩
                → ⟨ v ∈ˢ V ⟩)
             → ((v : S) (v∈ : ⟨ v ∈ˢ W ⟩) → ⟨ v ∈ˢ V ⟩
                → ⟨ (pt v v∈ ∷ δ) ⊨ᵐ M ⟩)
             → fst (lookup k δ) ≡ V → ⟨ δ ⊨ᵐ eqFrame k M ⟩
  eqFrame-in k M δ V wsub mout min e = (part₁ , part₂)
    where
    part₁ : (xm : SM) → ⟨ fst xm ∈ˢ fst (lookup k δ) ⟩
          → ⟨ (xm ∷ δ) ⊨ᵐ M ⟩
    part₁ xm h = min (fst xm) (snd xm)
      (subst (λ t → ⟨ fst xm ∈ˢ t ⟩) e h)
    part₂ : (xm : SM) → ⟨ (xm ∷ δ) ⊨ᵐ M ⟩
          → ⟨ fst xm ∈ˢ fst (lookup k δ) ⟩
    part₂ xm h = subst (λ t → ⟨ fst xm ∈ˢ t ⟩) (sym e)
      (mout (fst xm) (snd xm) h)

  singl-eq : (x p : S) → ⟨ x ∈ˢ ⁅ p ⁆s ⟩ → x ≡ p
  singl-eq x p h = PT.rec (setIsSet x p) (Sum.rec (λ e → e) (λ e → e))
    (F0-spec p p x .fst (subst (λ w → ⟨ x ∈ˢ w ⟩) (singl≡pair p) h))

-- The predicate at the level telescope: the carrier, the closure facts,
-- and the code map. This is the object-language predicate itself.
module Pred (W : S) (Wtr : isTransV W)
            (C : S) (C∈ : ⟨ C ∈ˢ W ⟩)
            (prIn : (a b : S) → ⟨ a ∈ˢ W ⟩ → ⟨ b ∈ˢ W ⟩ → ⟨ prS a b ∈ˢ W ⟩)
            (numIn : (k : ℕ) → ⟨ numS k ∈ˢ W ⟩)
            (sglIn : (a : S) → ⟨ a ∈ˢ W ⟩ → ⟨ sglS a ∈ˢ W ⟩)
            (cupIn : (a b : S) → ⟨ a ∈ˢ W ⟩ → ⟨ b ∈ˢ W ⟩ → ⟨ cupS a b ∈ˢ W ⟩)
            (∅∈W : ⟨ ∅ ∈ˢ W ⟩)
            (codeIn : ∀ {n} (φ : Formula ⟪ C ⟫ n) → ⟨ Codes.code C φ ∈ˢ W ⟩)
            where

  open Frame W Wtr using
    ( mem; prL∈; prR∈; pt; eqFrame; eqFrame-out; eqFrame-in; singl-eq )
  open Desc W Wtr hiding ( pair∈; ι )
  open PK using ( prAt; prAt-out; prAt-in )
  open Codes C using ( ι; codeTm; code; codeSet; codeSet-out; code∈codeSet )

  private
    v0 : {n : ℕ} → Fin (suc n)
    v0 = zero
    v1 : {n : ℕ} → Fin (suc (suc n))
    v1 = suc v0
    v2 : {n : ℕ} → Fin (suc (suc (suc n)))
    v2 = suc v1
    v3 : {n : ℕ} → Fin (suc (suc (suc (suc n))))
    v3 = suc v2
    v4 : {n : ℕ} → Fin (suc (suc (suc (suc (suc n)))))
    v4 = suc v3
    v5 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc n))))))
    v5 = suc v4
    v6 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc (suc n)))))))
    v6 = suc v5

  keyOf : ℕ → S → S
  keyOf n x = prS (numS n) x

  binKey : ℕ → S → S → S → S
  binKey t N a b = prS N (prS (numS t) (prS a b))

  unKey : ℕ → S → S → S
  unKey t N a = prS N (prS (numS t) a)

  mC : ⟪ W ⟫
  mC = ∈-asFiber {a = C} {b = W} C∈ .fst

  qC : ⟪ W ⟫↪ mC ≡ C
  qC = ∈-asFiber {a = C} {b = W} C∈ .snd

  nm : ℕ → ⟪ W ⟫
  nm k = ∈-asFiber {a = numS k} {b = W} (numIn k) .fst

  qnm : (k : ℕ) → ⟪ W ⟫↪ (nm k) ≡ numS k
  qnm k = ∈-asFiber {a = numS k} {b = W} (numIn k) .snd

  opaque
    unfolding prS

    prSIn : (a b : S) → ⟨ a ∈ˢ W ⟩ → ⟨ b ∈ˢ W ⟩ → ⟨ pr a b ∈ˢ W ⟩
    prSIn = prIn

    prParts : (p q : S) → ⟨ prS p q ∈ˢ W ⟩ → ⟨ p ∈ˢ W ⟩ × ⟨ q ∈ˢ W ⟩
    prParts p q h = prL∈ p q h , prR∈ p q h

    prAtS-out : {n : ℕ} (q u v : Fin n) (δ : Vec SM n)
              → ⟨ δ ⊨ᵐ prAt q u v ⟩
              → fst (lookup q δ) ≡ prS (fst (lookup u δ)) (fst (lookup v δ))
    prAtS-out = prAt-out

    prAtS-in : {n : ℕ} (q u v : Fin n) (δ : Vec SM n)
             → fst (lookup q δ) ≡ prS (fst (lookup u δ)) (fst (lookup v δ))
             → ⟨ δ ⊨ᵐ prAt q u v ⟩
    prAtS-in = prAt-in

  tagPr : {n : ℕ} → Fin n → ℕ → Fin n → Formula ⟪ W ⟫ n
  tagPr q t x = ∃̇ ((var v0 ≐ con (nm t)) ∧̇ prAt (suc q) v0 (suc x))

  tagPr-out : {n : ℕ} (q : Fin n) (t : ℕ) (x : Fin n) (δ : Vec SM n)
            → ⟨ δ ⊨ᵐ tagPr q t x ⟩
            → fst (lookup q δ) ≡ prS (numS t) (fst (lookup x δ))
  tagPr-out q t x δ = PT.rec (setIsSet _ _)
    (λ { (ym , (e , h)) →
      prAtS-out (suc q) v0 (suc x) (ym ∷ δ) h
      ∙ cong (λ u → prS u (fst (lookup x δ))) (e ∙ qnm t) })

  tagPr-in : {n : ℕ} (q : Fin n) (t : ℕ) (x : Fin n) (δ : Vec SM n)
           → fst (lookup q δ) ≡ prS (numS t) (fst (lookup x δ))
           → ⟨ δ ⊨ᵐ tagPr q t x ⟩
  tagPr-in q t x δ e =
    ∣ pt (numS t) (numIn t)
    , (sym (qnm t)
      , prAtS-in (suc q) v0 (suc x) (pt (numS t) (numIn t) ∷ δ) e) ∣₁

  keyPairAt : {n : ℕ} → Fin n → Fin n → ℕ → Fin n → Fin n → Formula ⟪ W ⟫ n
  keyPairAt w N t a b =
    ∃̇ (∃̇ ( prAt v1 (suc (suc a)) (suc (suc b))
          ∧̇ (tagPr v0 t v1
          ∧̇ prAt (suc (suc w)) (suc (suc N)) v0) ))

  keyPairAt-out : {n : ℕ} (w N : Fin n) (t : ℕ) (a b : Fin n) (δ : Vec SM n)
                → ⟨ δ ⊨ᵐ keyPairAt w N t a b ⟩
                → fst (lookup w δ)
                  ≡ binKey t (fst (lookup N δ)) (fst (lookup a δ))
                             (fst (lookup b δ))
  keyPairAt-out w N t a b δ = PT.rec (setIsSet _ _)
    (λ { (pm , hp) → PT.rec (setIsSet _ _)
      (λ { (qm , (e₁ , (e₂ , e₃))) →
        prAtS-out (suc (suc w)) (suc (suc N)) v0 (qm ∷ pm ∷ δ) e₃
        ∙ cong (prS (fst (lookup N δ)))
            (tagPr-out v0 t v1 (qm ∷ pm ∷ δ) e₂
             ∙ cong (prS (numS t)) (prAtS-out v1 (suc (suc a)) (suc (suc b))
                                      (qm ∷ pm ∷ δ) e₁)) })
      hp })

  keyPairAt-in : {n : ℕ} (w N : Fin n) (t : ℕ) (a b : Fin n) (δ : Vec SM n)
               → fst (lookup w δ)
                 ≡ binKey t (fst (lookup N δ)) (fst (lookup a δ))
                            (fst (lookup b δ))
               → ⟨ δ ⊨ᵐ keyPairAt w N t a b ⟩
  keyPairAt-in w N t a b δ e =
    ∣ pm
    , ∣ qm
      , ( prAtS-in v1 (suc (suc a)) (suc (suc b)) (qm ∷ pm ∷ δ) refl
        , ( tagPr-in v0 t v1 (qm ∷ pm ∷ δ) refl
          , prAtS-in (suc (suc w)) (suc (suc N)) v0 (qm ∷ pm ∷ δ) e ) ) ∣₁ ∣₁
    where
    pm : SM
    pm = pt (prS (fst (lookup a δ)) (fst (lookup b δ)))
            (prIn _ _ (snd (lookup a δ)) (snd (lookup b δ)))
    qm : SM
    qm = pt (prS (numS t) (fst pm)) (prIn _ _ (numIn t) (snd pm))

  keyUnAt : {n : ℕ} → Fin n → Fin n → ℕ → Fin n → Formula ⟪ W ⟫ n
  keyUnAt w N t a = ∃̇ ( tagPr v0 t (suc a) ∧̇ prAt (suc w) (suc N) v0 )

  keyUnAt-out : {n : ℕ} (w N : Fin n) (t : ℕ) (a : Fin n) (δ : Vec SM n)
              → ⟨ δ ⊨ᵐ keyUnAt w N t a ⟩
              → fst (lookup w δ) ≡ unKey t (fst (lookup N δ)) (fst (lookup a δ))
  keyUnAt-out w N t a δ = PT.rec (setIsSet _ _)
    (λ { (qm , (e₁ , e₂)) →
      prAtS-out (suc w) (suc N) v0 (qm ∷ δ) e₂
      ∙ cong (prS (fst (lookup N δ))) (tagPr-out v0 t (suc a) (qm ∷ δ) e₁) })

  keyUnAt-in : {n : ℕ} (w N : Fin n) (t : ℕ) (a : Fin n) (δ : Vec SM n)
             → fst (lookup w δ) ≡ unKey t (fst (lookup N δ)) (fst (lookup a δ))
             → ⟨ δ ⊨ᵐ keyUnAt w N t a ⟩
  keyUnAt-in w N t a δ e =
    ∣ qm
    , ( tagPr-in v0 t (suc a) (qm ∷ δ) refl
      , prAtS-in (suc w) (suc N) v0 (qm ∷ δ) e ) ∣₁
    where
    qm : SM
    qm = pt (prS (numS t) (fst (lookup a δ)))
            (prIn _ _ (numIn t) (snd (lookup a δ)))

  unForm : ℕ → Formula ⟪ W ⟫ 6 → Formula ⟪ W ⟫ 4
  unForm t rel = ∃̇ (∃̇ ( keyUnAt v2 v1 t v0 ∧̇ rel ))

  UnWit : ℕ → Formula ⟪ W ⟫ 6 → Vec SM 3 → SM → Type (ℓ-suc ℓ)
  UnWit t rel δ w = Σ[ N ∈ SM ] Σ[ a ∈ SM ]
    ((fst w ≡ unKey t (fst N) (fst a)) × ⟨ (a ∷ N ∷ w ∷ δ) ⊨ᵐ rel ⟩)

  unForm-out : (t : ℕ) (rel : Formula ⟪ W ⟫ 6) (δ : Vec SM 3) (w : SM)
             → ⟨ (w ∷ δ) ⊨ᵐ unForm t rel ⟩ → ∥ UnWit t rel δ w ∥₁
  unForm-out t rel δ w h = PT.rec squash₁ (λ { (N , hN) → PT.map (mk N) hN }) h
    where
    mk : (N : SM)
       → Σ[ a ∈ SM ] ⟨ (a ∷ N ∷ w ∷ δ) ⊨ᵐ (keyUnAt v2 v1 t v0 ∧̇ rel) ⟩
       → UnWit t rel δ w
    mk N (a , (hk , hr)) =
      N , a , ( keyUnAt-out v2 v1 t v0 (a ∷ N ∷ w ∷ δ) hk , hr )

  binForm : ℕ → Formula ⟪ W ⟫ 7 → Formula ⟪ W ⟫ 4
  binForm t rel = ∃̇ (∃̇ (∃̇ ( keyPairAt v3 v2 t v1 v0 ∧̇ rel )))

  BinWit : ℕ → Formula ⟪ W ⟫ 7 → Vec SM 3 → SM → Type (ℓ-suc ℓ)
  BinWit t rel δ w = Σ[ N ∈ SM ] Σ[ a ∈ SM ] Σ[ b ∈ SM ]
    ((fst w ≡ binKey t (fst N) (fst a) (fst b))
     × ⟨ (b ∷ a ∷ N ∷ w ∷ δ) ⊨ᵐ rel ⟩)

  binForm-out : (t : ℕ) (rel : Formula ⟪ W ⟫ 7) (δ : Vec SM 3) (w : SM)
              → ⟨ (w ∷ δ) ⊨ᵐ binForm t rel ⟩ → ∥ BinWit t rel δ w ∥₁
  binForm-out t rel δ w h =
    PT.rec squash₁ (λ { (N , hN) → PT.rec squash₁ (mk₂ N) hN }) h
    where
    mk₃ : (N a : SM)
        → Σ[ b ∈ SM ] ⟨ (b ∷ a ∷ N ∷ w ∷ δ) ⊨ᵐ (keyPairAt v3 v2 t v1 v0 ∧̇ rel) ⟩
        → BinWit t rel δ w
    mk₃ N a (b , (hk , hr)) =
      N , a , b , ( keyPairAt-out v3 v2 t v1 v0 (b ∷ a ∷ N ∷ w ∷ δ) hk , hr )
    mk₂ : (N : SM)
        → Σ[ a ∈ SM ] ⟨ (a ∷ N ∷ w ∷ δ)
                        ⊨ᵐ (∃̇ (keyPairAt v3 v2 t v1 v0 ∧̇ rel)) ⟩
        → ∥ BinWit t rel δ w ∥₁
    mk₂ N (a , ha) = PT.map (mk₃ N a) ha

  binForm-in : (t : ℕ) (rel : Formula ⟪ W ⟫ 7) (δ : Vec SM 3) (w : SM)
             → BinWit t rel δ w → ⟨ (w ∷ δ) ⊨ᵐ binForm t rel ⟩
  binForm-in t rel δ w (N , a , b , (e , hr)) =
    ∣ N , ∣ a , ∣ b
      , ( keyPairAt-in v3 v2 t v1 v0 (b ∷ a ∷ N ∷ w ∷ δ) e , hr ) ∣₁ ∣₁ ∣₁

  unForm-in : (t : ℕ) (rel : Formula ⟪ W ⟫ 6) (δ : Vec SM 3) (w : SM)
            → UnWit t rel δ w → ⟨ (w ∷ δ) ⊨ᵐ unForm t rel ⟩
  unForm-in t rel δ w (N , a , (e , hr)) =
    ∣ N , ∣ a , ( keyUnAt-in v2 v1 t v0 (a ∷ N ∷ w ∷ δ) e , hr ) ∣₁ ∣₁

  IsTm : S → S → Type (ℓ-suc ℓ)
  IsTm N t = ∥ (Σ[ y ∈ S ] ((t ≡ prS (numS 0) y) × ⟨ y ∈ˢ C ⟩))
             ⊎ (Σ[ y ∈ S ] ((t ≡ prS (numS 1) y) × ⟨ y ∈ˢ N ⟩)) ∥₁

  isTm : {n : ℕ} → Fin n → Fin n → Formula ⟪ W ⟫ n
  isTm t N = ∃̇ ( tagPr (suc t) 0 v0 ∧̇ (var v0 ∈̇ con mC) )
          ∨̇ ∃̇ ( tagPr (suc t) 1 v0 ∧̇ (var v0 ∈̇ var (suc N)) )

  isTm-out : {n : ℕ} (t N : Fin n) (δ : Vec SM n) → ⟨ δ ⊨ᵐ isTm t N ⟩
           → IsTm (fst (lookup N δ)) (fst (lookup t δ))
  isTm-out t N δ = PT.rec squash₁
    (λ { (inl h) → PT.map conCase h ; (inr h) → PT.map varCase h })
    where
    Goal : Type (ℓ-suc ℓ)
    Goal = (Σ[ y ∈ S ] ((fst (lookup t δ) ≡ prS (numS 0) y) × ⟨ y ∈ˢ C ⟩))
         ⊎ (Σ[ y ∈ S ] ((fst (lookup t δ) ≡ prS (numS 1) y)
                        × ⟨ y ∈ˢ fst (lookup N δ) ⟩))
    conCase : Σ[ ym ∈ SM ] (⟨ (ym ∷ δ) ⊨ᵐ tagPr (suc t) 0 v0 ⟩
                            × ⟨ fst ym ∈ˢ ⟪ W ⟫↪ mC ⟩) → Goal
    conCase (ym , (e , h∈)) = inl (fst ym
      , ( tagPr-out (suc t) 0 v0 (ym ∷ δ) e
        , subst (λ u → ⟨ fst ym ∈ˢ u ⟩) qC h∈ ))
    varCase : Σ[ ym ∈ SM ] (⟨ (ym ∷ δ) ⊨ᵐ tagPr (suc t) 1 v0 ⟩
                            × ⟨ fst ym ∈ˢ fst (lookup N δ) ⟩) → Goal
    varCase (ym , (e , h∈)) = inr (fst ym
      , ( tagPr-out (suc t) 1 v0 (ym ∷ δ) e , h∈ ))

  isTm-in : {n : ℕ} (t N : Fin n) (δ : Vec SM n)
          → IsTm (fst (lookup N δ)) (fst (lookup t δ)) → ⟨ δ ⊨ᵐ isTm t N ⟩
  isTm-in t N δ = PT.rec (snd (δ ⊨ᵐ isTm t N)) go
    where
    go : (Σ[ y ∈ S ] ((fst (lookup t δ) ≡ prS (numS 0) y) × ⟨ y ∈ˢ C ⟩))
       ⊎ (Σ[ y ∈ S ] ((fst (lookup t δ) ≡ prS (numS 1) y)
                      × ⟨ y ∈ˢ fst (lookup N δ) ⟩))
       → ⟨ δ ⊨ᵐ isTm t N ⟩
    go (inl (y , (e , y∈))) =
      ∣ inl ∣ pt y (mem C y y∈ C∈)
            , ( tagPr-in (suc t) 0 v0 (pt y (mem C y y∈ C∈) ∷ δ) e
              , subst (λ u → ⟨ y ∈ˢ u ⟩) (sym qC) y∈ ) ∣₁ ∣₁
    go (inr (y , (e , y∈))) =
      ∣ inr ∣ pt y (mem (fst (lookup N δ)) y y∈ (snd (lookup N δ)))
            , ( tagPr-in (suc t) 1 v0
                  (pt y (mem (fst (lookup N δ)) y y∈ (snd (lookup N δ))) ∷ δ) e
              , y∈ ) ∣₁ ∣₁

  subK : {n : ℕ} → Fin n → Fin n → Fin n → Formula ⟪ W ⟫ n
  subK N a D = ∃̇ ( prAt v0 (suc N) (suc a) ∧̇ (var v0 ∈̇ var (suc D)) )

  subK-out : {n : ℕ} (N a D : Fin n) (δ : Vec SM n) → ⟨ δ ⊨ᵐ subK N a D ⟩
           → ⟨ prS (fst (lookup N δ)) (fst (lookup a δ)) ∈ˢ fst (lookup D δ) ⟩
  subK-out N a D δ = PT.rec (snd (_ ∈ˢ fst (lookup D δ))) go
    where
    go : Σ[ ym ∈ SM ] (⟨ (ym ∷ δ) ⊨ᵐ prAt v0 (suc N) (suc a) ⟩
                       × ⟨ fst ym ∈ˢ fst (lookup D δ) ⟩)
       → ⟨ prS (fst (lookup N δ)) (fst (lookup a δ)) ∈ˢ fst (lookup D δ) ⟩
    go (ym , (e , h)) = subst (λ u → ⟨ u ∈ˢ fst (lookup D δ) ⟩)
      (prAtS-out v0 (suc N) (suc a) (ym ∷ δ) e) h

  subK-in : {n : ℕ} (N a D : Fin n) (δ : Vec SM n)
          → ⟨ prS (fst (lookup N δ)) (fst (lookup a δ)) ∈ˢ fst (lookup D δ) ⟩
          → ⟨ δ ⊨ᵐ subK N a D ⟩
  subK-in N a D δ h = ∣ ym , (prAtS-in v0 (suc N) (suc a) (ym ∷ δ) refl , h) ∣₁
    where
    ym : SM
    ym = pt (prS (fst (lookup N δ)) (fst (lookup a δ)))
            (prIn _ _ (snd (lookup N δ)) (snd (lookup a δ)))

  sucBody : {n : ℕ} → Fin n → Formula ⟪ W ⟫ (suc n)
  sucBody N = (var v0 ∈̇ var (suc N)) ∨̇ (var v0 ≐ var (suc N))

  succEq : {n : ℕ} → Fin n → Fin n → Formula ⟪ W ⟫ n
  succEq m N = eqFrame m (sucBody N)

  opaque
    unfolding sucS

    sucSub : {n : ℕ} (N : Fin n) (δ : Vec SM n) (v : S)
           → ⟨ v ∈ˢ sucS (fst (lookup N δ)) ⟩ → ⟨ v ∈ˢ W ⟩
    sucSub N δ v h = ∈sucV-elim {A = fst (lookup N δ)} {x = v}
      (snd (v ∈ˢ W)) h
      (λ h' → mem (fst (lookup N δ)) v h' (snd (lookup N δ)))
      (λ e → subst (λ u → ⟨ u ∈ˢ W ⟩) (sym e) (snd (lookup N δ)))

    sucMout : {n : ℕ} (N : Fin n) (δ : Vec SM n) (v : S) (v∈ : ⟨ v ∈ˢ W ⟩)
            → ⟨ (pt v v∈ ∷ δ) ⊨ᵐ sucBody N ⟩
            → ⟨ v ∈ˢ sucS (fst (lookup N δ)) ⟩
    sucMout N δ v v∈ = PT.rec (snd (v ∈ˢ sucV (fst (lookup N δ)))) go
      where
      go : ⟨ v ∈ˢ fst (lookup N δ) ⟩ ⊎ (v ≡ fst (lookup N δ))
         → ⟨ v ∈ˢ sucV (fst (lookup N δ)) ⟩
      go (inl h) = ∈sucV-inl {A = fst (lookup N δ)} {x = v} h
      go (inr e) = subst (λ u → ⟨ u ∈ˢ sucV (fst (lookup N δ)) ⟩) (sym e)
        (self∈sucV (fst (lookup N δ)))

    sucMin : {n : ℕ} (N : Fin n) (δ : Vec SM n) (v : S) (v∈ : ⟨ v ∈ˢ W ⟩)
           → ⟨ v ∈ˢ sucS (fst (lookup N δ)) ⟩
           → ⟨ (pt v v∈ ∷ δ) ⊨ᵐ sucBody N ⟩
    sucMin N δ v v∈ h = ∈sucV-elim {A = fst (lookup N δ)} {x = v}
      (snd ((pt v v∈ ∷ δ) ⊨ᵐ sucBody N)) h
      (λ h' → ∣ inl h' ∣₁) (λ e → ∣ inr e ∣₁)

  succEq-out : {n : ℕ} (m N : Fin n) (δ : Vec SM n) → ⟨ δ ⊨ᵐ succEq m N ⟩
             → fst (lookup m δ) ≡ sucS (fst (lookup N δ))
  succEq-out m N δ = eqFrame-out m (sucBody N) δ (sucS (fst (lookup N δ)))
    (sucSub N δ) (sucMout N δ) (sucMin N δ)

  succEq-in : {n : ℕ} (m N : Fin n) (δ : Vec SM n)
            → fst (lookup m δ) ≡ sucS (fst (lookup N δ))
            → ⟨ δ ⊨ᵐ succEq m N ⟩
  succEq-in m N δ = eqFrame-in m (sucBody N) δ (sucS (fst (lookup N δ)))
    (sucSub N δ) (sucMout N δ) (sucMin N δ)

  relTm relSame relBnd : Formula ⟪ W ⟫ 7
  relTm   = isTm v1 v2 ∧̇ isTm v0 v2
  relSame = subK v2 v1 v5 ∧̇ subK v2 v0 v5
  relBnd  = isTm v1 v2 ∧̇ ∃̇ ( succEq v0 v3 ∧̇ subK v0 v1 v6 )

  relOne relZero relSucc : Formula ⟪ W ⟫ 6
  relOne  = subK v1 v0 v4
  relZero = var v0 ≐ con (nm 0)
  relSucc = ∃̇ ( succEq v0 v2 ∧̇ subK v0 v1 v5 )

  relTm-out : (δ : Vec SM 3) (w N a b : SM)
            → ⟨ (b ∷ a ∷ N ∷ w ∷ δ) ⊨ᵐ relTm ⟩
            → IsTm (fst N) (fst a) × IsTm (fst N) (fst b)
  relTm-out δ w N a b (h₁ , h₂) =
      isTm-out v1 v2 (b ∷ a ∷ N ∷ w ∷ δ) h₁
    , isTm-out v0 v2 (b ∷ a ∷ N ∷ w ∷ δ) h₂

  relTm-in : (δ : Vec SM 3) (w N a b : SM)
           → IsTm (fst N) (fst a) → IsTm (fst N) (fst b)
           → ⟨ (b ∷ a ∷ N ∷ w ∷ δ) ⊨ᵐ relTm ⟩
  relTm-in δ w N a b h₁ h₂ =
      isTm-in v1 v2 (b ∷ a ∷ N ∷ w ∷ δ) h₁
    , isTm-in v0 v2 (b ∷ a ∷ N ∷ w ∷ δ) h₂

  relSame-out : (δ : Vec SM 3) (w N a b : SM)
              → ⟨ (b ∷ a ∷ N ∷ w ∷ δ) ⊨ᵐ relSame ⟩
              → ⟨ prS (fst N) (fst a) ∈ˢ fst (lookup v1 δ) ⟩
              × ⟨ prS (fst N) (fst b) ∈ˢ fst (lookup v1 δ) ⟩
  relSame-out δ w N a b (h₁ , h₂) =
      subK-out v2 v1 v5 (b ∷ a ∷ N ∷ w ∷ δ) h₁
    , subK-out v2 v0 v5 (b ∷ a ∷ N ∷ w ∷ δ) h₂

  relSame-in : (δ : Vec SM 3) (w N a b : SM)
             → ⟨ prS (fst N) (fst a) ∈ˢ fst (lookup v1 δ) ⟩
             → ⟨ prS (fst N) (fst b) ∈ˢ fst (lookup v1 δ) ⟩
             → ⟨ (b ∷ a ∷ N ∷ w ∷ δ) ⊨ᵐ relSame ⟩
  relSame-in δ w N a b h₁ h₂ =
      subK-in v2 v1 v5 (b ∷ a ∷ N ∷ w ∷ δ) h₁
    , subK-in v2 v0 v5 (b ∷ a ∷ N ∷ w ∷ δ) h₂

  relBnd-out : (δ : Vec SM 3) (w N a b : SM)
             → ⟨ (b ∷ a ∷ N ∷ w ∷ δ) ⊨ᵐ relBnd ⟩
             → IsTm (fst N) (fst a)
             × ⟨ prS (sucS (fst N)) (fst b) ∈ˢ fst (lookup v1 δ) ⟩
  relBnd-out δ w N a b (h₁ , h₂) =
    isTm-out v1 v2 (b ∷ a ∷ N ∷ w ∷ δ) h₁
    , PT.rec (snd (prS (sucS (fst N)) (fst b) ∈ˢ fst (lookup v1 δ))) go h₂
    where
    go : Σ[ Mm ∈ SM ] (⟨ (Mm ∷ b ∷ a ∷ N ∷ w ∷ δ) ⊨ᵐ succEq v0 v3 ⟩
                       × ⟨ (Mm ∷ b ∷ a ∷ N ∷ w ∷ δ) ⊨ᵐ subK v0 v1 v6 ⟩)
       → ⟨ prS (sucS (fst N)) (fst b) ∈ˢ fst (lookup v1 δ) ⟩
    go (Mm , (e , s)) =
      subst (λ u → ⟨ prS u (fst b) ∈ˢ fst (lookup v1 δ) ⟩)
        (succEq-out v0 v3 (Mm ∷ b ∷ a ∷ N ∷ w ∷ δ) e)
        (subK-out v0 v1 v6 (Mm ∷ b ∷ a ∷ N ∷ w ∷ δ) s)

  relBnd-in : (δ : Vec SM 3) (w N a b : SM) → ⟨ sucS (fst N) ∈ˢ W ⟩
            → IsTm (fst N) (fst a)
            → ⟨ prS (sucS (fst N)) (fst b) ∈ˢ fst (lookup v1 δ) ⟩
            → ⟨ (b ∷ a ∷ N ∷ w ∷ δ) ⊨ᵐ relBnd ⟩
  relBnd-in δ w N a b hs h₁ h₂ =
      isTm-in v1 v2 (b ∷ a ∷ N ∷ w ∷ δ) h₁
    , ∣ Mm , ( succEq-in v0 v3 (Mm ∷ b ∷ a ∷ N ∷ w ∷ δ) refl
             , subK-in v0 v1 v6 (Mm ∷ b ∷ a ∷ N ∷ w ∷ δ) h₂ ) ∣₁
    where
    Mm : SM
    Mm = pt (sucS (fst N)) hs

  relOne-out : (δ : Vec SM 3) (w N a : SM) → ⟨ (a ∷ N ∷ w ∷ δ) ⊨ᵐ relOne ⟩
             → ⟨ prS (fst N) (fst a) ∈ˢ fst (lookup v1 δ) ⟩
  relOne-out δ w N a = subK-out v1 v0 v4 (a ∷ N ∷ w ∷ δ)

  relOne-in : (δ : Vec SM 3) (w N a : SM)
            → ⟨ prS (fst N) (fst a) ∈ˢ fst (lookup v1 δ) ⟩
            → ⟨ (a ∷ N ∷ w ∷ δ) ⊨ᵐ relOne ⟩
  relOne-in δ w N a = subK-in v1 v0 v4 (a ∷ N ∷ w ∷ δ)

  relZero-out : (δ : Vec SM 3) (w N a : SM) → ⟨ (a ∷ N ∷ w ∷ δ) ⊨ᵐ relZero ⟩
              → fst a ≡ numS 0
  relZero-out δ w N a e = e ∙ qnm 0

  relZero-in : (δ : Vec SM 3) (w N a : SM) → fst a ≡ numS 0
             → ⟨ (a ∷ N ∷ w ∷ δ) ⊨ᵐ relZero ⟩
  relZero-in δ w N a e = e ∙ sym (qnm 0)

  relSucc-out : (δ : Vec SM 3) (w N a : SM) → ⟨ (a ∷ N ∷ w ∷ δ) ⊨ᵐ relSucc ⟩
              → ⟨ prS (sucS (fst N)) (fst a) ∈ˢ fst (lookup v1 δ) ⟩
  relSucc-out δ w N a =
    PT.rec (snd (prS (sucS (fst N)) (fst a) ∈ˢ fst (lookup v1 δ))) go
    where
    go : Σ[ Mm ∈ SM ] (⟨ (Mm ∷ a ∷ N ∷ w ∷ δ) ⊨ᵐ succEq v0 v2 ⟩
                       × ⟨ (Mm ∷ a ∷ N ∷ w ∷ δ) ⊨ᵐ subK v0 v1 v5 ⟩)
       → ⟨ prS (sucS (fst N)) (fst a) ∈ˢ fst (lookup v1 δ) ⟩
    go (Mm , (e , s)) =
      subst (λ u → ⟨ prS u (fst a) ∈ˢ fst (lookup v1 δ) ⟩)
        (succEq-out v0 v2 (Mm ∷ a ∷ N ∷ w ∷ δ) e)
        (subK-out v0 v1 v5 (Mm ∷ a ∷ N ∷ w ∷ δ) s)

  relSucc-in : (δ : Vec SM 3) (w N a : SM) → ⟨ sucS (fst N) ∈ˢ W ⟩
             → ⟨ prS (sucS (fst N)) (fst a) ∈ˢ fst (lookup v1 δ) ⟩
             → ⟨ (a ∷ N ∷ w ∷ δ) ⊨ᵐ relSucc ⟩
  relSucc-in δ w N a hs h =
    ∣ Mm , ( succEq-in v0 v2 (Mm ∷ a ∷ N ∷ w ∷ δ) refl
           , subK-in v0 v1 v5 (Mm ∷ a ∷ N ∷ w ∷ δ) h ) ∣₁
    where
    Mm : SM
    Mm = pt (sucS (fst N)) hs

  clause : ℕ → Formula ⟪ W ⟫ 4
  clause 0  = binForm 0  relTm
  clause 1  = binForm 1  relTm
  clause 2  = binForm 2  relSame
  clause 3  = binForm 3  relSame
  clause 4  = binForm 4  relSame
  clause 5  = unForm  5  relOne
  clause 6  = unForm  6  relZero
  clause 7  = unForm  7  relZero
  clause 8  = unForm  8  relSucc
  clause 9  = unForm  9  relSucc
  clause 10 = binForm 10 relBnd
  clause 11 = binForm 11 relBnd
  clause _  = ⊥̇

  TmShape SameShape BndShape : ℕ → S → S → Type (ℓ-suc ℓ)
  TmShape t D w = Σ[ N ∈ S ] Σ[ a ∈ S ] Σ[ b ∈ S ]
    ((w ≡ binKey t N a b) × (IsTm N a × IsTm N b))
  SameShape t D w = Σ[ N ∈ S ] Σ[ a ∈ S ] Σ[ b ∈ S ]
    ((w ≡ binKey t N a b) × (⟨ prS N a ∈ˢ D ⟩ × ⟨ prS N b ∈ˢ D ⟩))
  BndShape t D w = Σ[ N ∈ S ] Σ[ a ∈ S ] Σ[ b ∈ S ]
    ((w ≡ binKey t N a b) × (IsTm N a × ⟨ prS (sucS N) b ∈ˢ D ⟩))

  OneShape ZeroShape SuccShape : ℕ → S → S → Type (ℓ-suc ℓ)
  OneShape t D w = Σ[ N ∈ S ] Σ[ a ∈ S ]
    ((w ≡ unKey t N a) × ⟨ prS N a ∈ˢ D ⟩)
  ZeroShape t D w = Σ[ N ∈ S ] Σ[ a ∈ S ]
    ((w ≡ unKey t N a) × (a ≡ numS 0))
  SuccShape t D w = Σ[ N ∈ S ] Σ[ a ∈ S ]
    ((w ≡ unKey t N a) × ⟨ prS (sucS N) a ∈ˢ D ⟩)

  Shape : ℕ → S → S → Type (ℓ-suc ℓ)
  Shape 0  = TmShape 0
  Shape 1  = TmShape 1
  Shape 2  = SameShape 2
  Shape 3  = SameShape 3
  Shape 4  = SameShape 4
  Shape 5  = OneShape 5
  Shape 6  = ZeroShape 6
  Shape 7  = ZeroShape 7
  Shape 8  = SuccShape 8
  Shape 9  = SuccShape 9
  Shape 10 = BndShape 10
  Shape 11 = BndShape 11
  Shape _  = λ _ _ → ⊥*

  private
    packBin : (t : ℕ) (rel : Formula ⟪ W ⟫ 7) (δ : Vec SM 3) (w : SM)
              (N a b : S) → fst w ≡ binKey t N a b
            → ((hN : ⟨ N ∈ˢ W ⟩) (ha : ⟨ a ∈ˢ W ⟩) (hb : ⟨ b ∈ˢ W ⟩)
               → ⟨ (pt b hb ∷ pt a ha ∷ pt N hN ∷ w ∷ δ) ⊨ᵐ rel ⟩)
            → ⟨ (w ∷ δ) ⊨ᵐ binForm t rel ⟩
    packBin t rel δ w N a b e k =
      binForm-in t rel δ w
        (pt N hN , pt a ha , pt b hb , (e , k hN ha hb))
      where
      p1 = prParts N (prS (numS t) (prS a b))
             (subst (λ u → ⟨ u ∈ˢ W ⟩) e (snd w))
      p2 = prParts (numS t) (prS a b) (p1 .snd)
      p3 = prParts a b (p2 .snd)
      hN = p1 .fst
      ha = p3 .fst
      hb = p3 .snd

    packUn : (t : ℕ) (rel : Formula ⟪ W ⟫ 6) (δ : Vec SM 3) (w : SM)
             (N a : S) → fst w ≡ unKey t N a
           → ((hN : ⟨ N ∈ˢ W ⟩) (ha : ⟨ a ∈ˢ W ⟩)
              → ⟨ (pt a ha ∷ pt N hN ∷ w ∷ δ) ⊨ᵐ rel ⟩)
           → ⟨ (w ∷ δ) ⊨ᵐ unForm t rel ⟩
    packUn t rel δ w N a e k =
      unForm-in t rel δ w (pt N hN , pt a ha , (e , k hN ha))
      where
      p1 = prParts N (prS (numS t) a) (subst (λ u → ⟨ u ∈ˢ W ⟩) e (snd w))
      p2 = prParts (numS t) a (p1 .snd)
      hN = p1 .fst
      ha = p2 .snd

    sucOfKey : (N a D : S) → ⟨ D ∈ˢ W ⟩ → ⟨ prS (sucS N) a ∈ˢ D ⟩
             → ⟨ sucS N ∈ˢ W ⟩
    sucOfKey N a D hD h =
      prParts (sucS N) a (mem D (prS (sucS N) a) h hD) .fst

    outTm : (t : ℕ) (δ : Vec SM 3) (w : SM) → BinWit t relTm δ w
          → TmShape t (fst (lookup v1 δ)) (fst w)
    outTm t δ w (N , a , b , (e , hr)) =
      fst N , fst a , fst b , (e , relTm-out δ w N a b hr)

    outSame : (t : ℕ) (δ : Vec SM 3) (w : SM) → BinWit t relSame δ w
            → SameShape t (fst (lookup v1 δ)) (fst w)
    outSame t δ w (N , a , b , (e , hr)) =
      fst N , fst a , fst b , (e , relSame-out δ w N a b hr)

    outBnd : (t : ℕ) (δ : Vec SM 3) (w : SM) → BinWit t relBnd δ w
           → BndShape t (fst (lookup v1 δ)) (fst w)
    outBnd t δ w (N , a , b , (e , hr)) =
      fst N , fst a , fst b , (e , relBnd-out δ w N a b hr)

    outOne : (t : ℕ) (δ : Vec SM 3) (w : SM) → UnWit t relOne δ w
           → OneShape t (fst (lookup v1 δ)) (fst w)
    outOne t δ w (N , a , (e , hr)) =
      fst N , fst a , (e , relOne-out δ w N a hr)

    outZero : (t : ℕ) (δ : Vec SM 3) (w : SM) → UnWit t relZero δ w
            → ZeroShape t (fst (lookup v1 δ)) (fst w)
    outZero t δ w (N , a , (e , hr)) =
      fst N , fst a , (e , relZero-out δ w N a hr)

    outSucc : (t : ℕ) (δ : Vec SM 3) (w : SM) → UnWit t relSucc δ w
            → SuccShape t (fst (lookup v1 δ)) (fst w)
    outSucc t δ w (N , a , (e , hr)) =
      fst N , fst a , (e , relSucc-out δ w N a hr)

    inTm : (t : ℕ) (δ : Vec SM 3) (w : SM)
         → TmShape t (fst (lookup v1 δ)) (fst w)
         → ⟨ (w ∷ δ) ⊨ᵐ binForm t relTm ⟩
    inTm t δ w (N , a , b , (e , (h₁ , h₂))) =
      packBin t relTm δ w N a b e
        (λ hN ha hb → relTm-in δ w (pt N hN) (pt a ha) (pt b hb) h₁ h₂)

    inSame : (t : ℕ) (δ : Vec SM 3) (w : SM)
           → SameShape t (fst (lookup v1 δ)) (fst w)
           → ⟨ (w ∷ δ) ⊨ᵐ binForm t relSame ⟩
    inSame t δ w (N , a , b , (e , (h₁ , h₂))) =
      packBin t relSame δ w N a b e
        (λ hN ha hb → relSame-in δ w (pt N hN) (pt a ha) (pt b hb) h₁ h₂)

    inBnd : (t : ℕ) (δ : Vec SM 3) (w : SM)
          → BndShape t (fst (lookup v1 δ)) (fst w)
          → ⟨ (w ∷ δ) ⊨ᵐ binForm t relBnd ⟩
    inBnd t δ w (N , a , b , (e , (h₁ , h₂))) =
      packBin t relBnd δ w N a b e
        (λ hN ha hb → relBnd-in δ w (pt N hN) (pt a ha) (pt b hb)
          (sucOfKey N b (fst (lookup v1 δ)) (snd (lookup v1 δ)) h₂) h₁ h₂)

    inOne : (t : ℕ) (δ : Vec SM 3) (w : SM)
          → OneShape t (fst (lookup v1 δ)) (fst w)
          → ⟨ (w ∷ δ) ⊨ᵐ unForm t relOne ⟩
    inOne t δ w (N , a , (e , h)) =
      packUn t relOne δ w N a e
        (λ hN ha → relOne-in δ w (pt N hN) (pt a ha) h)

    inZero : (t : ℕ) (δ : Vec SM 3) (w : SM)
           → ZeroShape t (fst (lookup v1 δ)) (fst w)
           → ⟨ (w ∷ δ) ⊨ᵐ unForm t relZero ⟩
    inZero t δ w (N , a , (e , h)) =
      packUn t relZero δ w N a e
        (λ hN ha → relZero-in δ w (pt N hN) (pt a ha) h)

    inSucc : (t : ℕ) (δ : Vec SM 3) (w : SM)
           → SuccShape t (fst (lookup v1 δ)) (fst w)
           → ⟨ (w ∷ δ) ⊨ᵐ unForm t relSucc ⟩
    inSucc t δ w (N , a , (e , h)) =
      packUn t relSucc δ w N a e
        (λ hN ha → relSucc-in δ w (pt N hN) (pt a ha)
          (sucOfKey N a (fst (lookup v1 δ)) (snd (lookup v1 δ)) h) h)

  clauseOut : (t : ℕ) (δ : Vec SM 3) (w : SM) → ⟨ (w ∷ δ) ⊨ᵐ clause t ⟩
            → ∥ Shape t (fst (lookup v1 δ)) (fst w) ∥₁
  clauseOut 0  δ w h = PT.map (outTm 0 δ w) (binForm-out 0 relTm δ w h)
  clauseOut 1  δ w h = PT.map (outTm 1 δ w) (binForm-out 1 relTm δ w h)
  clauseOut 2  δ w h = PT.map (outSame 2 δ w) (binForm-out 2 relSame δ w h)
  clauseOut 3  δ w h = PT.map (outSame 3 δ w) (binForm-out 3 relSame δ w h)
  clauseOut 4  δ w h = PT.map (outSame 4 δ w) (binForm-out 4 relSame δ w h)
  clauseOut 5  δ w h = PT.map (outOne 5 δ w) (unForm-out 5 relOne δ w h)
  clauseOut 6  δ w h = PT.map (outZero 6 δ w) (unForm-out 6 relZero δ w h)
  clauseOut 7  δ w h = PT.map (outZero 7 δ w) (unForm-out 7 relZero δ w h)
  clauseOut 8  δ w h = PT.map (outSucc 8 δ w) (unForm-out 8 relSucc δ w h)
  clauseOut 9  δ w h = PT.map (outSucc 9 δ w) (unForm-out 9 relSucc δ w h)
  clauseOut 10 δ w h = PT.map (outBnd 10 δ w) (binForm-out 10 relBnd δ w h)
  clauseOut 11 δ w h = PT.map (outBnd 11 δ w) (binForm-out 11 relBnd δ w h)
  clauseOut (suc (suc (suc (suc (suc (suc (suc (suc (suc
    (suc (suc (suc t))))))))))))  δ w h = Empty.rec* h

  clauseIn : (t : ℕ) (δ : Vec SM 3) (w : SM)
           → Shape t (fst (lookup v1 δ)) (fst w) → ⟨ (w ∷ δ) ⊨ᵐ clause t ⟩
  clauseIn 0  = inTm 0
  clauseIn 1  = inTm 1
  clauseIn 2  = inSame 2
  clauseIn 3  = inSame 3
  clauseIn 4  = inSame 4
  clauseIn 5  = inOne 5
  clauseIn 6  = inZero 6
  clauseIn 7  = inZero 7
  clauseIn 8  = inSucc 8
  clauseIn 9  = inSucc 9
  clauseIn 10 = inBnd 10
  clauseIn 11 = inBnd 11
  clauseIn (suc (suc (suc (suc (suc (suc (suc (suc (suc
    (suc (suc (suc t)))))))))))) δ w s = Empty.rec* s

  orUpto : ℕ → Formula ⟪ W ⟫ 4
  orUpto zero    = ⊥̇
  orUpto (suc m) = clause m ∨̇ orUpto m

  node : Formula ⟪ W ⟫ 4
  node = orUpto 12

  orUpto-in : (m t : ℕ) → t < m → (δ : Vec SM 4) → ⟨ δ ⊨ᵐ clause t ⟩
            → ⟨ δ ⊨ᵐ orUpto m ⟩
  orUpto-in zero t lt δ h = Empty.rec (¬-<-zero lt)
  orUpto-in (suc m) t lt δ h = Sum.rec
    (λ lt' → ∣ inr (orUpto-in m t lt' δ h) ∣₁)
    (λ e → ∣ inl (subst (λ j → ⟨ δ ⊨ᵐ clause j ⟩) e h) ∣₁)
    (<-split lt)

  orUpto-out : (m : ℕ) (δ : Vec SM 4) → ⟨ δ ⊨ᵐ orUpto m ⟩
             → ∥ Σ[ t ∈ ℕ ] ⟨ δ ⊨ᵐ clause t ⟩ ∥₁
  orUpto-out zero δ h = Empty.rec* h
  orUpto-out (suc m) δ = PT.rec squash₁ go
    where
    go : ⟨ δ ⊨ᵐ clause m ⟩ ⊎ ⟨ δ ⊨ᵐ orUpto m ⟩
       → ∥ Σ[ t ∈ ℕ ] ⟨ δ ⊨ᵐ clause t ⟩ ∥₁
    go (inl h) = ∣ m , h ∣₁
    go (inr h) = orUpto-out m δ h

  private
    shapeLt : (t : ℕ) (D w : S) → Shape t D w → t < 12
    shapeLt 0  D w _ = 11 , refl
    shapeLt 1  D w _ = 10 , refl
    shapeLt 2  D w _ = 9  , refl
    shapeLt 3  D w _ = 8  , refl
    shapeLt 4  D w _ = 7  , refl
    shapeLt 5  D w _ = 6  , refl
    shapeLt 6  D w _ = 5  , refl
    shapeLt 7  D w _ = 4  , refl
    shapeLt 8  D w _ = 3  , refl
    shapeLt 9  D w _ = 2  , refl
    shapeLt 10 D w _ = 1  , refl
    shapeLt 11 D w _ = 0  , refl
    shapeLt (suc (suc (suc (suc (suc (suc (suc (suc (suc
      (suc (suc (suc t)))))))))))) D w s = Empty.rec* s

  Well : S → Type (ℓ-suc ℓ)
  Well D = (w : S) → ⟨ w ∈ˢ D ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁

  wellAt : Formula ⟪ W ⟫ 3
  wellAt = ∀̇∈ (var v1) node

  well-out : (δ : Vec SM 3) → ⟨ δ ⊨ᵐ wellAt ⟩ → Well (fst (lookup v1 δ))
  well-out δ h w w∈ = PT.rec squash₁ go (orUpto-out 12 (wm ∷ δ) (h wm w∈))
    where
    wm : SM
    wm = pt w (mem (fst (lookup v1 δ)) w w∈ (snd (lookup v1 δ)))
    go : Σ[ t ∈ ℕ ] ⟨ (wm ∷ δ) ⊨ᵐ clause t ⟩
       → ∥ Σ[ t ∈ ℕ ] Shape t (fst (lookup v1 δ)) w ∥₁
    go (t , ht) = PT.map (λ s → t , s) (clauseOut t δ wm ht)

  well-in : (δ : Vec SM 3) → Well (fst (lookup v1 δ)) → ⟨ δ ⊨ᵐ wellAt ⟩
  well-in δ hw xm x∈ = PT.rec (snd ((xm ∷ δ) ⊨ᵐ node)) go (hw (fst xm) x∈)
    where
    go : Σ[ t ∈ ℕ ] Shape t (fst (lookup v1 δ)) (fst xm)
       → ⟨ (xm ∷ δ) ⊨ᵐ node ⟩
    go (t , s) = orUpto-in 12 t (shapeLt t (fst (lookup v1 δ)) (fst xm) s)
      (xm ∷ δ) (clauseIn t δ xm s)

  Φ : ℕ → Formula ⟪ W ⟫ 1
  Φ k = ∃̇ (∃̇ ( tagPr v0 k v2 ∧̇ ((var v0 ∈̇ var v1) ∧̇ wellAt) ))

  Witness : ℕ → S → Type (ℓ-suc ℓ)
  Witness k x = Σ[ D ∈ S ] (Well D × ⟨ keyOf k x ∈ˢ D ⟩)

  Φ-out : (k : ℕ) (x : S) (x∈ : ⟨ x ∈ˢ W ⟩) → ⟨ (pt x x∈ ∷ []) ⊨ᵐ Φ k ⟩
        → ∥ Witness k x ∥₁
  Φ-out k x x∈ = PT.rec squash₁ (λ { (Dm , hD) → PT.map (go Dm) hD })
    where
    go : (Dm : SM)
       → Σ[ km ∈ SM ]
           (⟨ (km ∷ Dm ∷ pt x x∈ ∷ []) ⊨ᵐ tagPr v0 k v2 ⟩
            × (⟨ fst km ∈ˢ fst Dm ⟩
               × ⟨ (km ∷ Dm ∷ pt x x∈ ∷ []) ⊨ᵐ wellAt ⟩))
       → Witness k x
    go Dm (km , (e , (h∈ , hw))) = fst Dm
      , ( well-out (km ∷ Dm ∷ pt x x∈ ∷ []) hw
        , subst (λ u → ⟨ u ∈ˢ fst Dm ⟩)
            (tagPr-out v0 k v2 (km ∷ Dm ∷ pt x x∈ ∷ []) e) h∈ )

  Φ-in : (k : ℕ) (x : S) (x∈ : ⟨ x ∈ˢ W ⟩) (D : S) (hD : ⟨ D ∈ˢ W ⟩)
       → Well D → ⟨ keyOf k x ∈ˢ D ⟩ → ⟨ (pt x x∈ ∷ []) ⊨ᵐ Φ k ⟩
  Φ-in k x x∈ D hD hw h∈ =
    ∣ pt D hD
    , ∣ km , ( tagPr-in v0 k v2 env refl , (h∈ , well-in env hw) ) ∣₁ ∣₁
    where
    km : SM
    km = pt (keyOf k x) (prIn (numS k) x (numIn k) x∈)
    env : Vec SM 3
    env = km ∷ pt D hD ∷ pt x x∈ ∷ []

  Coded : ℕ → S → Type (ℓ-suc ℓ)
  Coded n x = ∥ Σ[ φ ∈ Formula ⟪ C ⟫ n ] (code φ ≡ x) ∥₁

  splitBin : (j t : ℕ) (z N a b : S) → keyOf j z ≡ binKey t N a b
           → (numS j ≡ N) × (z ≡ prS (numS t) (prS a b))
  splitBin j t z N a b = prS-inj

  splitUn : (j t : ℕ) (z N a : S) → keyOf j z ≡ unKey t N a
          → (numS j ≡ N) × (z ≡ prS (numS t) a)
  splitUn j t z N a = prS-inj

  opaque
    unfolding prS numS

    codeBin : (t : ℕ) (p q : S) → prS (numS t) (prS p q) ≡ VCode.mkTag t (pr p q)
    codeBin t p q = refl

    codeUn : (t : ℕ) (p : S) → prS (numS t) p ≡ VCode.mkTag t p
    codeUn t p = refl

  private
    tmOf : (j : ℕ) (a : S) → IsTm (numS j) a
         → ∥ Σ[ τ ∈ Term ⟪ C ⟫ j ] (codeTm τ ≡ a) ∥₁
    tmOf j a = PT.rec squash₁ go
      where
      go : (Σ[ y ∈ S ] ((a ≡ prS (numS 0) y) × ⟨ y ∈ˢ C ⟩))
         ⊎ (Σ[ y ∈ S ] ((a ≡ prS (numS 1) y) × ⟨ y ∈ˢ numS j ⟩))
         → ∥ Σ[ τ ∈ Term ⟪ C ⟫ j ] (codeTm τ ≡ a) ∥₁
      go (inl (y , (e , y∈))) =
        ∣ con (fib .fst)
        , ( cong (VCode.mkTag 0) (fib .snd)
            ∙ sym (codeUn 0 y) ∙ sym e ) ∣₁
        where
        fib : Σ[ m ∈ ⟪ C ⟫ ] (⟪ C ⟫↪ m ≡ y)
        fib = ∈-asFiber {a = y} {b = C} y∈
      go (inr (y , (e , y∈))) = PT.map pick
        (∈#-elim j y (subst (λ u → ⟨ y ∈ˢ u ⟩) (numS-# j) y∈))
        where
        pick : Σ[ m ∈ ℕ ] ((m < j) × (y ≡ (# m)))
             → Σ[ τ ∈ Term ⟪ C ⟫ j ] (codeTm τ ≡ a)
        pick (m , (m<j , qy)) = var (fromℕ' j m m<j)
          , ( cong (λ u → VCode.mkTag 1 (# u)) (toFromId' j m m<j)
              ∙ cong (VCode.mkTag 1) (sym qy)
              ∙ sym (codeUn 1 y) ∙ sym e )

  recover : (D : S) → Well D → (n : ℕ) (x : S) → ⟨ keyOf n x ∈ˢ D ⟩ → Coded n x
  recover D hw n x = ∈-induction step (rank x) n x refl
    where
    P : S → Type (ℓ-suc ℓ)
    P r = (j : ℕ) (z : S) → rank z ≡ r → ⟨ keyOf j z ∈ˢ D ⟩ → Coded j z

    step : (r : S) → ((y : S) → ⟨ y ∈ˢ r ⟩ → P y) → P r
    step r IH j z qr wz = PT.rec squash₁ fill (hw (keyOf j z) wz)
      where
      rec : (i : ℕ) (u : S) → ⟨ rank u ∈ˢ rank z ⟩ → ⟨ keyOf i u ∈ˢ D ⟩
          → Coded i u
      rec i u lt wu =
        IH (rank u) (subst (λ v → ⟨ rank u ∈ˢ v ⟩) qr lt) i u refl wu

      atomK : (t : ℕ)
              (op : ∀ {i} → Term ⟪ C ⟫ i → Term ⟪ C ⟫ i → Formula ⟪ C ⟫ i)
            → (∀ {i} (s u : Term ⟪ C ⟫ i)
               → code (op s u) ≡ VCode.mkTag t (pr (codeTm s) (codeTm u)))
            → TmShape t D (keyOf j z) → Coded j z
      atomK t op qop (N , a , b , (e , (ha , hb))) = PT.rec squash₁ fin (tmOf j a ha')
        where
        sp = splitBin j t z N a b e
        ha' : IsTm (numS j) a
        ha' = subst (λ u → IsTm u a) (sym (sp .fst)) ha
        hb' : IsTm (numS j) b
        hb' = subst (λ u → IsTm u b) (sym (sp .fst)) hb
        f2 : Σ[ s ∈ Term ⟪ C ⟫ j ] (codeTm s ≡ a)
           → Σ[ u ∈ Term ⟪ C ⟫ j ] (codeTm u ≡ b)
           → Σ[ φ ∈ Formula ⟪ C ⟫ j ] (code φ ≡ z)
        f2 (s , qs) (u , qu) = op s u
          , ( qop s u ∙ cong (VCode.mkTag t) (cong₂ pr qs qu)
              ∙ sym (codeBin t a b) ∙ sym (sp .snd) )
        fin : Σ[ s ∈ Term ⟪ C ⟫ j ] (codeTm s ≡ a) → Coded j z
        fin p = PT.map (f2 p) (tmOf j b hb')

      sameK : (t : ℕ)
              (op : ∀ {i} → Formula ⟪ C ⟫ i → Formula ⟪ C ⟫ i → Formula ⟪ C ⟫ i)
            → (∀ {i} (φ ψ : Formula ⟪ C ⟫ i)
               → code (op φ ψ) ≡ VCode.mkTag t (pr (code φ) (code ψ)))
            → SameShape t D (keyOf j z) → Coded j z
      sameK t op qop (N , a , b , (e , (ha , hb))) = PT.rec squash₁ fin
        (rec j a (subst (λ u → ⟨ rank a ∈ˢ rank u ⟩) (sym (sp .snd))
                   (leftPart (numS t) a b))
                 (subst (λ u → ⟨ prS u a ∈ˢ D ⟩) (sym (sp .fst)) ha))
        where
        sp = splitBin j t z N a b e
        f2 : Σ[ φ ∈ Formula ⟪ C ⟫ j ] (code φ ≡ a)
           → Σ[ ψ ∈ Formula ⟪ C ⟫ j ] (code ψ ≡ b)
           → Σ[ χ ∈ Formula ⟪ C ⟫ j ] (code χ ≡ z)
        f2 (φ , qφ) (ψ , qψ) = op φ ψ
          , ( qop φ ψ ∙ cong (VCode.mkTag t) (cong₂ pr qφ qψ)
              ∙ sym (codeBin t a b) ∙ sym (sp .snd) )
        fin : Σ[ φ ∈ Formula ⟪ C ⟫ j ] (code φ ≡ a) → Coded j z
        fin p = PT.map (f2 p)
          (rec j b (subst (λ u → ⟨ rank b ∈ˢ rank u ⟩) (sym (sp .snd))
                     (rightPart (numS t) a b))
                   (subst (λ u → ⟨ prS u b ∈ˢ D ⟩) (sym (sp .fst)) hb))

      oneK : (t : ℕ) (op : ∀ {i} → Formula ⟪ C ⟫ i → Formula ⟪ C ⟫ i)
           → (∀ {i} (φ : Formula ⟪ C ⟫ i)
              → code (op φ) ≡ VCode.mkTag t (code φ))
           → OneShape t D (keyOf j z) → Coded j z
      oneK t op qop (N , a , (e , ha)) = PT.map f
        (rec j a (subst (λ u → ⟨ rank a ∈ˢ rank u ⟩) (sym (sp .snd))
                   (payload≺ (numS t) a))
                 (subst (λ u → ⟨ prS u a ∈ˢ D ⟩) (sym (sp .fst)) ha))
        where
        sp = splitUn j t z N a e
        f : Σ[ φ ∈ Formula ⟪ C ⟫ j ] (code φ ≡ a)
          → Σ[ χ ∈ Formula ⟪ C ⟫ j ] (code χ ≡ z)
        f (φ , qφ) = op φ
          , ( qop φ ∙ cong (VCode.mkTag t) qφ
              ∙ sym (codeUn t a) ∙ sym (sp .snd) )

      zeroK : (t : ℕ) (op : ∀ {i} → Formula ⟪ C ⟫ i)
            → (∀ (i : ℕ) → code (op {i}) ≡ VCode.mkTag t (# 0))
            → ZeroShape t D (keyOf j z) → Coded j z
      zeroK t op qop (N , a , (e , ha)) = ∣ op
        , ( qop j ∙ cong (VCode.mkTag t) (sym (numS-# 0))
            ∙ sym (codeUn t (numS 0)) ∙ cong (prS (numS t)) (sym ha)
            ∙ sym (splitUn j t z N a e .snd) ) ∣₁

      succK : (t : ℕ)
              (op : ∀ {i} → Formula ⟪ C ⟫ (suc i) → Formula ⟪ C ⟫ i)
            → (∀ {i} (φ : Formula ⟪ C ⟫ (suc i))
               → code (op φ) ≡ VCode.mkTag t (code φ))
            → SuccShape t D (keyOf j z) → Coded j z
      succK t op qop (N , a , (e , ha)) = PT.map f
        (rec (suc j) a (subst (λ u → ⟨ rank a ∈ˢ rank u ⟩) (sym (sp .snd))
                         (payload≺ (numS t) a))
                       (subst (λ u → ⟨ prS u a ∈ˢ D ⟩)
                         (sym (numS-suc j ∙ cong sucS (sp .fst))) ha))
        where
        sp = splitUn j t z N a e
        f : Σ[ φ ∈ Formula ⟪ C ⟫ (suc j) ] (code φ ≡ a)
          → Σ[ χ ∈ Formula ⟪ C ⟫ j ] (code χ ≡ z)
        f (φ , qφ) = op φ
          , ( qop φ ∙ cong (VCode.mkTag t) qφ
              ∙ sym (codeUn t a) ∙ sym (sp .snd) )

      bndK : (t : ℕ)
             (op : ∀ {i} → Term ⟪ C ⟫ i → Formula ⟪ C ⟫ (suc i) → Formula ⟪ C ⟫ i)
           → (∀ {i} (s : Term ⟪ C ⟫ i) (φ : Formula ⟪ C ⟫ (suc i))
              → code (op s φ) ≡ VCode.mkTag t (pr (codeTm s) (code φ)))
           → BndShape t D (keyOf j z) → Coded j z
      bndK t op qop (N , a , b , (e , (ha , hb))) = PT.rec squash₁ fin
        (tmOf j a (subst (λ u → IsTm u a) (sym (sp .fst)) ha))
        where
        sp = splitBin j t z N a b e
        f2 : Σ[ s ∈ Term ⟪ C ⟫ j ] (codeTm s ≡ a)
           → Σ[ φ ∈ Formula ⟪ C ⟫ (suc j) ] (code φ ≡ b)
           → Σ[ χ ∈ Formula ⟪ C ⟫ j ] (code χ ≡ z)
        f2 (s , qs) (φ , qφ) = op s φ
          , ( qop s φ ∙ cong (VCode.mkTag t) (cong₂ pr qs qφ)
              ∙ sym (codeBin t a b) ∙ sym (sp .snd) )
        fin : Σ[ s ∈ Term ⟪ C ⟫ j ] (codeTm s ≡ a) → Coded j z
        fin p = PT.map (f2 p)
          (rec (suc j) b (subst (λ u → ⟨ rank b ∈ˢ rank u ⟩) (sym (sp .snd))
                           (rightPart (numS t) a b))
                         (subst (λ u → ⟨ prS u b ∈ˢ D ⟩)
                           (sym (numS-suc j ∙ cong sucS (sp .fst))) hb))

      fill : Σ[ t ∈ ℕ ] Shape t D (keyOf j z) → Coded j z
      fill (0  , s) = atomK 0  _∈̇_ (λ _ _ → refl) s
      fill (1  , s) = atomK 1  _≐_ (λ _ _ → refl) s
      fill (2  , s) = sameK 2  _∧̇_ (λ _ _ → refl) s
      fill (3  , s) = sameK 3  _∨̇_ (λ _ _ → refl) s
      fill (4  , s) = sameK 4  _⇒̇_ (λ _ _ → refl) s
      fill (5  , s) = oneK  5  ¬̇_  (λ _ → refl) s
      fill (6  , s) = zeroK 6  ⊤̇   (λ _ → refl) s
      fill (7  , s) = zeroK 7  ⊥̇   (λ _ → refl) s
      fill (8  , s) = succK 8  ∃̇_  (λ _ → refl) s
      fill (9  , s) = succK 9  ∀̇_  (λ _ → refl) s
      fill (10 , s) = bndK  10 ∀̇∈  (λ _ _ → refl) s
      fill (11 , s) = bndK  11 ∃̇∈  (λ _ _ → refl) s
      fill ((suc (suc (suc (suc (suc (suc (suc (suc (suc
        (suc (suc (suc t)))))))))))) , s) = Empty.rec* s

  key : ∀ {n} → Formula ⟪ C ⟫ n → S
  key {n} φ = keyOf n (code φ)

  opaque
    unfolding cupS sglS

    cup-inl : (a b x : S) → ⟨ x ∈ˢ a ⟩ → ⟨ x ∈ˢ cupS a b ⟩
    cup-inl a b x h = F5-spec ⁅ a , b ⁆ a x .snd
      ∣ a , (pair∈ a b a ∣ inl refl ∣₁ , h) ∣₁

    cup-inr : (a b x : S) → ⟨ x ∈ˢ b ⟩ → ⟨ x ∈ˢ cupS a b ⟩
    cup-inr a b x h = F5-spec ⁅ a , b ⁆ a x .snd
      ∣ b , (pair∈ a b b ∣ inr refl ∣₁ , h) ∣₁

    cup-out : (a b x : S) → ⟨ x ∈ˢ cupS a b ⟩
            → ∥ ⟨ x ∈ˢ a ⟩ ⊎ ⟨ x ∈ˢ b ⟩ ∥₁
    cup-out a b x h = PT.rec squash₁ pick (F5-spec ⁅ a , b ⁆ a x .fst h)
      where
      pick : Σ[ v ∈ S ] (⟨ v ∈ˢ ⁅ a , b ⁆ ⟩ × ⟨ x ∈ˢ v ⟩)
           → ∥ ⟨ x ∈ˢ a ⟩ ⊎ ⟨ x ∈ˢ b ⟩ ∥₁
      pick (v , (v∈ , x∈v)) = PT.map choose (F0-spec a b v .fst v∈)
        where
        choose : (v ≡ a) ⊎ (v ≡ b) → ⟨ x ∈ˢ a ⟩ ⊎ ⟨ x ∈ˢ b ⟩
        choose (inl e) = inl (subst (λ u → ⟨ x ∈ˢ u ⟩) e x∈v)
        choose (inr e) = inr (subst (λ u → ⟨ x ∈ˢ u ⟩) e x∈v)

    sgl-in : (a : S) → ⟨ a ∈ˢ sglS a ⟩
    sgl-in = self∈sgl

    sgl-out : (a x : S) → ⟨ x ∈ˢ sglS a ⟩ → x ≡ a
    sgl-out a x h = singl-eq x a h

  clo : ∀ {n} → Formula ⟪ C ⟫ n → S
  subclo : ∀ {n} → Formula ⟪ C ⟫ n → S

  clo φ = cupS (sglS (key φ)) (subclo φ)

  subclo (s ∈̇ u)  = ∅
  subclo (s ≐ u)  = ∅
  subclo (a ∧̇ b)  = cupS (clo a) (clo b)
  subclo (a ∨̇ b)  = cupS (clo a) (clo b)
  subclo (a ⇒̇ b)  = cupS (clo a) (clo b)
  subclo (¬̇ a)    = clo a
  subclo ⊤̇        = ∅
  subclo ⊥̇        = ∅
  subclo (∃̇ a)    = clo a
  subclo (∀̇ a)    = clo a
  subclo (∀̇∈ s a) = clo a
  subclo (∃̇∈ s a) = clo a

  key∈W : ∀ {n} (φ : Formula ⟪ C ⟫ n) → ⟨ key φ ∈ˢ W ⟩
  key∈W {n} φ = prIn (numS n) (code φ) (numIn n) (codeIn φ)

  clo∈W : ∀ {n} (φ : Formula ⟪ C ⟫ n) → ⟨ clo φ ∈ˢ W ⟩
  subclo∈W : ∀ {n} (φ : Formula ⟪ C ⟫ n) → ⟨ subclo φ ∈ˢ W ⟩

  clo∈W φ = cupIn _ _ (sglIn (key φ) (key∈W φ)) (subclo∈W φ)

  subclo∈W (s ∈̇ u)  = ∅∈W
  subclo∈W (s ≐ u)  = ∅∈W
  subclo∈W (a ∧̇ b)  = cupIn _ _ (clo∈W a) (clo∈W b)
  subclo∈W (a ∨̇ b)  = cupIn _ _ (clo∈W a) (clo∈W b)
  subclo∈W (a ⇒̇ b)  = cupIn _ _ (clo∈W a) (clo∈W b)
  subclo∈W (¬̇ a)    = clo∈W a
  subclo∈W ⊤̇        = ∅∈W
  subclo∈W ⊥̇        = ∅∈W
  subclo∈W (∃̇ a)    = clo∈W a
  subclo∈W (∀̇ a)    = clo∈W a
  subclo∈W (∀̇∈ s a) = clo∈W a
  subclo∈W (∃̇∈ s a) = clo∈W a

  key∈clo : ∀ {n} (φ : Formula ⟪ C ⟫ n) → ⟨ key φ ∈ˢ clo φ ⟩
  key∈clo φ = cup-inl (sglS (key φ)) (subclo φ) (key φ) (sgl-in (key φ))

  sub∈clo : ∀ {n} (φ : Formula ⟪ C ⟫ n) (x : S)
          → ⟨ x ∈ˢ subclo φ ⟩ → ⟨ x ∈ˢ clo φ ⟩
  sub∈clo φ = cup-inr (sglS (key φ)) (subclo φ)

  private
    tmIn : ∀ {m} (τ : Term ⟪ C ⟫ m) → IsTm (numS m) (codeTm τ)
    tmIn (con c) = ∣ inl (ι c , ( sym (codeUn 0 (ι c))
                                , ∈∈ₛ {a = ι c} {b = C} .snd (∈ₛ⟪ C ⟫↪ c) )) ∣₁
    tmIn {m} (var i) = ∣ inr ((# (toℕ i))
      , ( sym (codeUn 1 (# (toℕ i)))
        , subst (λ u → ⟨ (# (toℕ i)) ∈ˢ u ⟩) (sym (numS-# m))
            (#mono (toℕ i) m (toℕ<n i)) )) ∣₁

    binEq : ∀ {n} (t : ℕ) (φ : Formula ⟪ C ⟫ n) (p q : S)
          → code φ ≡ VCode.mkTag t (pr p q)
          → key φ ≡ binKey t (numS n) p q
    binEq {n} t φ p q e =
      cong (prS (numS n)) (e ∙ sym (codeBin t p q))

    unEq : ∀ {n} (t : ℕ) (φ : Formula ⟪ C ⟫ n) (p : S)
         → code φ ≡ VCode.mkTag t p → key φ ≡ unKey t (numS n) p
    unEq {n} t φ p e = cong (prS (numS n)) (e ∙ sym (codeUn t p))

    subIn : ∀ {n m} (φ : Formula ⟪ C ⟫ n) (a : Formula ⟪ C ⟫ m) (D : S)
          → ((x : S) → ⟨ x ∈ˢ clo φ ⟩ → ⟨ x ∈ˢ D ⟩)
          → ⟨ key a ∈ˢ clo φ ⟩ → ⟨ prS (numS m) (code a) ∈ˢ D ⟩
    subIn φ a D sub h = sub (key a) h

    sucKey : ∀ {n} (a : Formula ⟪ C ⟫ (suc n)) (D : S)
           → ⟨ prS (numS (suc n)) (code a) ∈ˢ D ⟩
           → ⟨ prS (sucS (numS n)) (code a) ∈ˢ D ⟩
    sucKey {n} a D h =
      subst (λ u → ⟨ prS u (code a) ∈ˢ D ⟩) (numS-suc n) h

  headShape : ∀ {n} (φ : Formula ⟪ C ⟫ n) (D : S)
            → ((x : S) → ⟨ x ∈ˢ clo φ ⟩ → ⟨ x ∈ˢ D ⟩)
            → Σ[ t ∈ ℕ ] Shape t D (key φ)
  headShape {n} (s ∈̇ u) D sub = 0
    , ( numS n , codeTm s , codeTm u
      , ( binEq 0 (s ∈̇ u) (codeTm s) (codeTm u) refl , (tmIn s , tmIn u) ) )
  headShape {n} (s ≐ u) D sub = 1
    , ( numS n , codeTm s , codeTm u
      , ( binEq 1 (s ≐ u) (codeTm s) (codeTm u) refl , (tmIn s , tmIn u) ) )
  headShape {n} φ@(a ∧̇ b) D sub = 2
    , ( numS n , code a , code b
      , ( binEq 2 φ (code a) (code b) refl
        , ( subIn φ a D sub
              (sub∈clo φ (key a) (cup-inl (clo a) (clo b) (key a) (key∈clo a)))
          , subIn φ b D sub
              (sub∈clo φ (key b) (cup-inr (clo a) (clo b) (key b) (key∈clo b)))
          ) ) )
  headShape {n} φ@(a ∨̇ b) D sub = 3
    , ( numS n , code a , code b
      , ( binEq 3 φ (code a) (code b) refl
        , ( subIn φ a D sub
              (sub∈clo φ (key a) (cup-inl (clo a) (clo b) (key a) (key∈clo a)))
          , subIn φ b D sub
              (sub∈clo φ (key b) (cup-inr (clo a) (clo b) (key b) (key∈clo b)))
          ) ) )
  headShape {n} φ@(a ⇒̇ b) D sub = 4
    , ( numS n , code a , code b
      , ( binEq 4 φ (code a) (code b) refl
        , ( subIn φ a D sub
              (sub∈clo φ (key a) (cup-inl (clo a) (clo b) (key a) (key∈clo a)))
          , subIn φ b D sub
              (sub∈clo φ (key b) (cup-inr (clo a) (clo b) (key b) (key∈clo b)))
          ) ) )
  headShape {n} φ@(¬̇ a) D sub = 5
    , ( numS n , code a
      , ( unEq 5 φ (code a) refl
        , subIn φ a D sub (sub∈clo φ (key a) (key∈clo a)) ) )
  headShape {n} ⊤̇ D sub = 6
    , ( numS n , numS 0
      , ( unEq 6 ⊤̇ (numS 0) (cong (VCode.mkTag 6) (sym (numS-# 0))) , refl ) )
  headShape {n} ⊥̇ D sub = 7
    , ( numS n , numS 0
      , ( unEq 7 ⊥̇ (numS 0) (cong (VCode.mkTag 7) (sym (numS-# 0))) , refl ) )
  headShape {n} φ@(∃̇ a) D sub = 8
    , ( numS n , code a
      , ( unEq 8 φ (code a) refl
        , sucKey a D (subIn φ a D sub (sub∈clo φ (key a) (key∈clo a))) ) )
  headShape {n} φ@(∀̇ a) D sub = 9
    , ( numS n , code a
      , ( unEq 9 φ (code a) refl
        , sucKey a D (subIn φ a D sub (sub∈clo φ (key a) (key∈clo a))) ) )
  headShape {n} φ@(∀̇∈ s a) D sub = 10
    , ( numS n , codeTm s , code a
      , ( binEq 10 φ (codeTm s) (code a) refl
        , ( tmIn s
          , sucKey a D (subIn φ a D sub (sub∈clo φ (key a) (key∈clo a))) ) ) )
  headShape {n} φ@(∃̇∈ s a) D sub = 11
    , ( numS n , codeTm s , code a
      , ( binEq 11 φ (codeTm s) (code a) refl
        , ( tmIn s
          , sucKey a D (subIn φ a D sub (sub∈clo φ (key a) (key∈clo a))) ) ) )

  private
    headOf : ∀ {m} (ψ : Formula ⟪ C ⟫ m) (D w : S)
           → ((x : S) → ⟨ x ∈ˢ clo ψ ⟩ → ⟨ x ∈ˢ D ⟩)
           → ⟨ w ∈ˢ sglS (key ψ) ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    headOf ψ D w sub e = ∣ subst (λ v → Σ[ t ∈ ℕ ] Shape t D v)
      (sym (sgl-out (key ψ) w e)) (headShape ψ D sub) ∣₁

    noSub : (D w : S) → ⟨ w ∈ˢ ∅ ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    noSub D w h = Empty.rec (∅-empty w (∈∈ₛ {a = w} {b = ∅} .fst h))

  cloWell : ∀ {n} (φ : Formula ⟪ C ⟫ n) (D : S)
          → ((x : S) → ⟨ x ∈ˢ clo φ ⟩ → ⟨ x ∈ˢ D ⟩)
          → (w : S) → ⟨ w ∈ˢ clo φ ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
  cloWell φ@(s ∈̇ u) D sub w hw =
    PT.rec squash₁ go (cup-out (sglS (key φ)) (subclo φ) w hw)
    where
    go : ⟨ w ∈ˢ sglS (key φ) ⟩ ⊎ ⟨ w ∈ˢ ∅ ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go (inl e) = headOf φ D w sub e
    go (inr h) = noSub D w h
  cloWell φ@(s ≐ u) D sub w hw =
    PT.rec squash₁ go (cup-out (sglS (key φ)) (subclo φ) w hw)
    where
    go : ⟨ w ∈ˢ sglS (key φ) ⟩ ⊎ ⟨ w ∈ˢ ∅ ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go (inl e) = headOf φ D w sub e
    go (inr h) = noSub D w h
  cloWell φ@⊤̇ D sub w hw =
    PT.rec squash₁ go (cup-out (sglS (key φ)) (subclo φ) w hw)
    where
    go : ⟨ w ∈ˢ sglS (key φ) ⟩ ⊎ ⟨ w ∈ˢ ∅ ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go (inl e) = headOf φ D w sub e
    go (inr h) = noSub D w h
  cloWell φ@⊥̇ D sub w hw =
    PT.rec squash₁ go (cup-out (sglS (key φ)) (subclo φ) w hw)
    where
    go : ⟨ w ∈ˢ sglS (key φ) ⟩ ⊎ ⟨ w ∈ˢ ∅ ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go (inl e) = headOf φ D w sub e
    go (inr h) = noSub D w h
  cloWell φ@(¬̇ a) D sub w hw =
    PT.rec squash₁ go (cup-out (sglS (key φ)) (subclo φ) w hw)
    where
    go : ⟨ w ∈ˢ sglS (key φ) ⟩ ⊎ ⟨ w ∈ˢ clo a ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go (inl e) = headOf φ D w sub e
    go (inr h) = cloWell a D (λ x hx → sub x (sub∈clo φ x hx)) w h
  cloWell φ@(∃̇ a) D sub w hw =
    PT.rec squash₁ go (cup-out (sglS (key φ)) (subclo φ) w hw)
    where
    go : ⟨ w ∈ˢ sglS (key φ) ⟩ ⊎ ⟨ w ∈ˢ clo a ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go (inl e) = headOf φ D w sub e
    go (inr h) = cloWell a D (λ x hx → sub x (sub∈clo φ x hx)) w h
  cloWell φ@(∀̇ a) D sub w hw =
    PT.rec squash₁ go (cup-out (sglS (key φ)) (subclo φ) w hw)
    where
    go : ⟨ w ∈ˢ sglS (key φ) ⟩ ⊎ ⟨ w ∈ˢ clo a ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go (inl e) = headOf φ D w sub e
    go (inr h) = cloWell a D (λ x hx → sub x (sub∈clo φ x hx)) w h
  cloWell φ@(∀̇∈ s a) D sub w hw =
    PT.rec squash₁ go (cup-out (sglS (key φ)) (subclo φ) w hw)
    where
    go : ⟨ w ∈ˢ sglS (key φ) ⟩ ⊎ ⟨ w ∈ˢ clo a ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go (inl e) = headOf φ D w sub e
    go (inr h) = cloWell a D (λ x hx → sub x (sub∈clo φ x hx)) w h
  cloWell φ@(∃̇∈ s a) D sub w hw =
    PT.rec squash₁ go (cup-out (sglS (key φ)) (subclo φ) w hw)
    where
    go : ⟨ w ∈ˢ sglS (key φ) ⟩ ⊎ ⟨ w ∈ˢ clo a ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go (inl e) = headOf φ D w sub e
    go (inr h) = cloWell a D (λ x hx → sub x (sub∈clo φ x hx)) w h
  cloWell φ@(a ∧̇ b) D sub w hw =
    PT.rec squash₁ go (cup-out (sglS (key φ)) (subclo φ) w hw)
    where
    go2 : ⟨ w ∈ˢ clo a ⟩ ⊎ ⟨ w ∈ˢ clo b ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go2 (inl h) = cloWell a D
      (λ x hx → sub x (sub∈clo φ x (cup-inl (clo a) (clo b) x hx))) w h
    go2 (inr h) = cloWell b D
      (λ x hx → sub x (sub∈clo φ x (cup-inr (clo a) (clo b) x hx))) w h
    go : ⟨ w ∈ˢ sglS (key φ) ⟩ ⊎ ⟨ w ∈ˢ cupS (clo a) (clo b) ⟩
       → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go (inl e) = headOf φ D w sub e
    go (inr h) = PT.rec squash₁ go2 (cup-out (clo a) (clo b) w h)
  cloWell φ@(a ∨̇ b) D sub w hw =
    PT.rec squash₁ go (cup-out (sglS (key φ)) (subclo φ) w hw)
    where
    go2 : ⟨ w ∈ˢ clo a ⟩ ⊎ ⟨ w ∈ˢ clo b ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go2 (inl h) = cloWell a D
      (λ x hx → sub x (sub∈clo φ x (cup-inl (clo a) (clo b) x hx))) w h
    go2 (inr h) = cloWell b D
      (λ x hx → sub x (sub∈clo φ x (cup-inr (clo a) (clo b) x hx))) w h
    go : ⟨ w ∈ˢ sglS (key φ) ⟩ ⊎ ⟨ w ∈ˢ cupS (clo a) (clo b) ⟩
       → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go (inl e) = headOf φ D w sub e
    go (inr h) = PT.rec squash₁ go2 (cup-out (clo a) (clo b) w h)
  cloWell φ@(a ⇒̇ b) D sub w hw =
    PT.rec squash₁ go (cup-out (sglS (key φ)) (subclo φ) w hw)
    where
    go2 : ⟨ w ∈ˢ clo a ⟩ ⊎ ⟨ w ∈ˢ clo b ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go2 (inl h) = cloWell a D
      (λ x hx → sub x (sub∈clo φ x (cup-inl (clo a) (clo b) x hx))) w h
    go2 (inr h) = cloWell b D
      (λ x hx → sub x (sub∈clo φ x (cup-inr (clo a) (clo b) x hx))) w h
    go : ⟨ w ∈ˢ sglS (key φ) ⟩ ⊎ ⟨ w ∈ˢ cupS (clo a) (clo b) ⟩
       → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go (inl e) = headOf φ D w sub e
    go (inr h) = PT.rec squash₁ go2 (cup-out (clo a) (clo b) w h)

  Well-clo : ∀ {n} (φ : Formula ⟪ C ⟫ n) → Well (clo φ)
  Well-clo φ = cloWell φ (clo φ) (λ x h → h)

  satCode : (k : ℕ) (x : S) (x∈ : ⟨ x ∈ˢ W ⟩) → ⟨ (pt x x∈ ∷ []) ⊨ᵐ Φ k ⟩
          → Coded k x
  satCode k x x∈ h = PT.rec squash₁ go (Φ-out k x x∈ h)
    where
    go : Witness k x → Coded k x
    go (D , (hw , h∈)) = recover D hw k x h∈

  codeSat : (k : ℕ) (x : S) (x∈ : ⟨ x ∈ˢ W ⟩) → Coded k x
          → ⟨ (pt x x∈ ∷ []) ⊨ᵐ Φ k ⟩
  codeSat k x x∈ = PT.rec (snd ((pt x x∈ ∷ []) ⊨ᵐ Φ k)) go
    where
    go : Σ[ φ ∈ Formula ⟪ C ⟫ k ] (code φ ≡ x) → ⟨ (pt x x∈ ∷ []) ⊨ᵐ Φ k ⟩
    go (φ , q) = Φ-in k x x∈ (clo φ) (clo∈W φ) (Well-clo φ)
      (subst (λ u → ⟨ keyOf k u ∈ˢ clo φ ⟩) q (key∈clo φ))

  codeSet-desc : (k : ℕ) → ((x : S) → ⟨ x ∈ˢ codeSet k ⟩ → ⟨ x ∈ˢ W ⟩)
               → defSet (Φ k) ≡ codeSet k
  codeSet-desc k inW = described (Φ k) (codeSet k) inW din dout
    where
    din : (v : S) (v∈ : ⟨ v ∈ˢ W ⟩) → ⟨ v ∈ˢ codeSet k ⟩
        → ⟨ (pt v v∈ ∷ []) ⊨ᵐ Φ k ⟩
    din v v∈ h = codeSat k v v∈ (codeSet-out k v h)
    dout : (v : S) (v∈ : ⟨ v ∈ˢ W ⟩) → ⟨ (pt v v∈ ∷ []) ⊨ᵐ Φ k ⟩
         → ⟨ v ∈ˢ codeSet k ⟩
    dout v v∈ h = PT.rec (snd (v ∈ˢ codeSet k)) go (satCode k v v∈ h)
      where
      go : Σ[ φ ∈ Formula ⟪ C ⟫ k ] (code φ ≡ v) → ⟨ v ∈ˢ codeSet k ⟩
      go (φ , q) = subst (λ u → ⟨ u ∈ˢ codeSet k ⟩) q (code∈codeSet k φ)

-- The discharge at the honest index: the predicate over the inner limit,
-- and the code set as a member of the outer limit.
module Part (ζ δ : S) (ordδ : IsOrd δ) (limδ : ⟨ isLimit δ ⟩)
            (L∈ : ⟨ Lset ζ ∈ˢ Sset δ ⟩) where

  C : S
  C = Lset ζ

  γ : S
  γ = +ω δ

  limγ : ⟨ isLimit γ ⟩
  limγ = +ω-limit δ ordδ

  δ∈γ : ⟨ δ ∈ˢ γ ⟩
  δ∈γ = +ω-mem δ

  C∈γ : ⟨ C ∈ˢ Sset γ ⟩
  C∈γ = Sset-trans γ {x = Sset δ} {y = C} L∈ (Sset-mem {α = γ} {β = δ} δ∈γ)

  module LFS = LimitFullSwitch γ limγ δ limδ δ∈γ

  W : S
  W = Sset δ

  module IL = InLevel δ limδ
  module CR = Carrier δ limδ C L∈

  opaque
    unfolding prS numS sglS cupS

    prJ : (a b : S) → ⟨ a ∈ˢ W ⟩ → ⟨ b ∈ˢ W ⟩ → ⟨ prS a b ∈ˢ W ⟩
    prJ = IL.pr∈J

    numJ : (k : ℕ) → ⟨ numS k ∈ˢ W ⟩
    numJ = IL.numeral∈J C L∈

    sglJ : (a : S) → ⟨ a ∈ˢ W ⟩ → ⟨ sglS a ∈ˢ W ⟩
    sglJ a ha = subst (λ u → ⟨ u ∈ˢ W ⟩)
      (Fof-f0 a a ∙ sym (singl≡pair a)) (Jset-rud δ limδ f0 a a ha ha)

    cupJ : (a b : S) → ⟨ a ∈ˢ W ⟩ → ⟨ b ∈ˢ W ⟩ → ⟨ cupS a b ∈ˢ W ⟩
    cupJ a b ha hb = subst (λ u → ⟨ u ∈ˢ W ⟩)
      (Fof-f5 (Fof f0 a b) a ∙ cong ⋃_ (Fof-f0 a b))
      (Jset-rud δ limδ f5 (Fof f0 a b) a (Jset-rud δ limδ f0 a b ha hb) ha)

  module P = Pred W (Sset-trans δ) C L∈ prJ numJ sglJ cupJ
                  (IL.∅∈J C L∈) CR.code∈J

  codeSet∈J : (k : ℕ) → ⟨ Codes.codeSet C k ∈ˢ Sset γ ⟩
  codeSet∈J k = subst (λ w → ⟨ w ∈ˢ Sset γ ⟩)
    (P.codeSet-desc k (CR.codeSet⊆J k)) (LFS.full-switch-⊇ (P.Φ k))

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.111] probe A: can the TRUNCATED sq close the chain?
--
-- The route the brief's GOAL names, checked here: the truncation
-- belongs at the TOP.  The truncated chain
--   (α : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ∥ SQ.sq α ∥₁
-- closes WITHOUT the honest injection α ↪ |α|.  The initial case is
-- the delivered via-col-truncated at an Init α built with a truncated
-- induction hypothesis (the square clause concludes ⊥, so the
-- truncation eliminates there); the non-initial case eliminates
-- κ-eqα : ∥ ⟪ κ ⟫ ≃ ⟪ α ⟫ ∥₁ and the truncated IH into the
-- proposition ∥ sq α ∥₁, and builds the honest pairing of α from the
-- honest pairing of κ through the honest equivalence.
--
-- Untracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1111A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import ProbeLJ1106A {ℓ} lem as P106
open P106 using ( module NumeralPresentation )
import ProbeLJ1107A {ℓ} lem as P107
open P107 using ( module CSB; module ShiftAbs; module Shiftω; module Incl
                ; module FiniteAtω; module LeastCard; _↪_ )
import ProbeLJ194A {ℓ} lem as P194
open P194 using ( isSet⟪⟫ )
import L.Ordinal.SquareLaw {ℓ} lem as SQ
open SQ using ( module FiniteBase; sq; Init; via-col-truncated )
import L.Constructible {ℓ} as Cons
open Cons using ( IsOrd )
import L.Ordinal {ℓ} as Ord
open Ord using ( mem-ord; suc-ord; ω-ord; #∈ω )
import L.Ordinal.Linear {ℓ} lem as Lin
open Lin using ( ord-tri )
import V.Hierarchy {ℓ} as Hier
open Hier using ( 𝒮ᵥ; ∈-irrefl; ∈-induction )
import V.Model {ℓ} as VModel
open VModel using ( ∈sucV-elim )
import V.Presentation {ℓ} as VPres
open VPres using ( fiber; member; ↪-inj )
import FOL.ZFStructure as ZF
open ZF using ( module hPropStructure )
import Cubical.HITs.CumulativeHierarchy.Properties as CH
open CH using ( ⟪_⟫; ⟪_⟫↪ )
import Cubical.HITs.CumulativeHierarchy.Constructions as CHC
open CHC using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV; #_ )
import Cubical.Foundations.Equiv as Eq
open Eq using ( _≃_; equivFun; invEq; secEq; retEq; invEquiv )
import Cubical.Data.Sigma as Sig
open Sig using ( ΣPathP )
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum.Properties as SumProp
open SumProp using ( isProp⊎ )
import Cubical.Data.Nat as Nat
open Nat using ( ℕ; zero; suc )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open hPropStructure 𝒮ᵥ

-- =====================================================================
-- The truncated chain.  Each piece mirrors [LJ-1.107] with the
-- conclusion truncated, and the truncation eliminates exactly where
-- the target is a proposition.
-- =====================================================================

-- κ = |α| is not a member of ω: the truncated equivalence to α and
-- the finite exclusion at ω.  Copied from NonInitial (ProbeLJ1107A:
-- 552-590); the injection parameter plays no role in it.
module NonInitKappaNotOmega (α : S) (oα : IsOrd α)
  (ω∈α : ⟨ ω ∈ˢ α ⟩) (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  (κ : S) (oκ : IsOrd κ) (κ-eqα : ∥ ⟪ κ ⟫ ≃ ⟪ α ⟫ ∥₁)
  (κ∈α : ⟨ κ ∈ˢ α ⟩) where

  κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥
  κ∉ω κ∈ω = PT.rec Empty.isProp⊥ go3 (FiniteBase.ω-mem→numeral κ κ∈ω)
    where
    go3 : Σ[ n ∈ ℕ ] (κ ≡ # n) → Empty.⊥
    go3 (n , q) = go4 (ord-tri ω ω-ord α oα)
      where
      eqακ : ∥ ⟪ # n ⟫ ≃ ⟪ α ⟫ ∥₁
      eqακ = subst (λ w → ∥ ⟪ w ⟫ ≃ ⟪ α ⟫ ∥₁) q κ-eqα
      emb : ⟨ ω ∈ˢ α ⟩ → ⟪ ω ⟫ ↪ ⟪ α ⟫
      emb ω∈α = (λ m → fiber α {x = ⟪ ω ⟫↪ m} (oα .fst (member ω m) ω∈α) .fst)
              , λ m n e → ↪-inj {a = ω}
                  (sym (fiber α {x = ⟪ ω ⟫↪ m} (oα .fst (member ω m) ω∈α) .snd)
                    ∙ cong (⟪ α ⟫↪) e
                    ∙ fiber α {x = ⟪ ω ⟫↪ n} (oα .fst (member ω n) ω∈α) .snd)
      id-inj : (ω ≡ α) → ⟪ ω ⟫ ↪ ⟪ α ⟫
      id-inj ω≡α = subst (λ w → _↪_ ⟪ ω ⟫ ⟪ w ⟫) ω≡α
        ((λ x → x) , (λ x y e → e))
      refute : ⟪ ω ⟫ ↪ ⟪ α ⟫ → Empty.⊥
      refute g = PT.rec Empty.isProp⊥ go5 eqακ
        where
        go5 : ⟪ # n ⟫ ≃ ⟪ α ⟫ → Empty.⊥
        go5 e = FiniteAtω.no-inj-finite-ω n (λ x → f (g .fst x) , f (g .fst x)) inj
          where
          f : ⟪ α ⟫ → ⟪ # n ⟫
          f = invEq e
          inj : (x y : ⟪ ω ⟫)
              → (f (g .fst x) , f (g .fst x)) ≡ (f (g .fst y) , f (g .fst y)) → x ≡ y
          inj x y p = g .snd x y
            (sym (secEq e (g .fst x)) ∙ cong (equivFun e) (cong fst p) ∙ secEq e (g .fst y))
      go4 : (⟨ ω ∈ˢ α ⟩ ⊎ ((ω ≡ α) ⊎ ⟨ α ∈ˢ ω ⟩)) → Empty.⊥
      go4 (inl ω∈α) = refute (emb ω∈α)
      go4 (inr (inl ω≡α)) = refute (id-inj ω≡α)
      go4 (inr (inr α∈ω)) = Empty.rec (α∉ω α∈ω)

-- The initial case |α| = α with a truncated induction hypothesis.
--   The square clause concludes Empty.⊥, a proposition, so the
--   truncated IH eliminates there; everything else is the delivered
--   InitialCase mathematics (ProbeLJ1107A:464-537).
module InitialCaseT (α : S) (oα : IsOrd α) (ω∈α : ⟨ ω ∈ˢ α ⟩)
  (leastα : (δ : S) → ⟨ δ ∈ˢ α ⟩ → ∥ ⟪ δ ⟫ ≃ ⟪ α ⟫ ∥₁ → Empty.⊥)
  (ihT : (β : S) → ⟨ β ∈ˢ α ⟩ → IsOrd β
       → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → ∥ SQ.sq β ∥₁) where

  noinj² : (β : S) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
         → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
         → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥
  noinj² β oβ β∈α ω∈β f f-inj =
    PT.rec Empty.isProp⊥ go (ihT β β∈α oβ β∉ω)
    where
    β∉ω : ⟨ β ∈ˢ ω ⟩ → Empty.⊥
    β∉ω β∈ω = ∈-irrefl ω (ω-ord .fst ω∈β β∈ω)
    go : SQ.sq β → Empty.⊥
    go sqβ = leastα β β∈α (∣ invEquiv csb ∣₁)
      where
      h : ⟪ α ⟫ → ⟪ β ⟫
      h m = sqβ .fst (f m)
      h-inj : (m n : ⟪ α ⟫) → h m ≡ h n → m ≡ n
      h-inj m n e = f-inj m n (sqβ .snd (f m) (f n) e)
      j : ⟪ β ⟫ → ⟪ α ⟫
      j m = fiber α {x = ⟪ β ⟫↪ m} (oα .fst (member β m) β∈α) .fst
      j-inj : (m n : ⟪ β ⟫) → j m ≡ j n → m ≡ n
      j-inj m n e = ↪-inj {a = β}
        (sym (fiber α {x = ⟪ β ⟫↪ m} (oα .fst (member β m) β∈α) .snd)
          ∙ cong (⟪ α ⟫↪) e
          ∙ fiber α {x = ⟪ β ⟫↪ n} (oα .fst (member β n) β∈α) .snd)
      csb : ⟪ α ⟫ ≃ ⟪ β ⟫
      csb = CSB.csb (⟪ α ⟫) (⟪ β ⟫) (isSet⟪⟫ α) (isSet⟪⟫ β) h h-inj j j-inj

  succ-closure : (γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩
  succ-closure γ γ∈α =
    go (ord-tri (sucV γ) (suc-ord (mem-ord {A = α} oα γ γ∈α)) α oα)
    where
    oγ : IsOrd γ
    oγ = mem-ord {A = α} oα γ γ∈α
    go : (⟨ sucV γ ∈ˢ α ⟩ ⊎ ((sucV γ ≡ α) ⊎ ⟨ α ∈ˢ sucV γ ⟩)) → ⟨ sucV γ ∈ˢ α ⟩
    go (inl h) = h
    go (inr (inr h)) = ∈sucV-elim {A = γ} {x = α} {P = ⟨ sucV γ ∈ˢ α ⟩}
      (snd (sucV γ ∈ˢ α)) h
      (λ α∈γ → Empty.rec (∈-irrefl α (oα .fst {x = γ} {y = α} α∈γ γ∈α)))
      (λ α≡γ → Empty.rec (∈-irrefl γ (subst (λ w → ⟨ γ ∈ˢ w ⟩) α≡γ γ∈α)))
    go (inr (inl sγ≡α)) = go2 (ord-tri γ oγ ω ω-ord)
      where
      go2 : (⟨ γ ∈ˢ ω ⟩ ⊎ ((γ ≡ ω) ⊎ ⟨ ω ∈ˢ γ ⟩)) → ⟨ sucV γ ∈ˢ α ⟩
      go2 (inl γ∈ω) = PT.rec (snd (sucV γ ∈ˢ α)) go3 (FiniteBase.ω-mem→numeral γ γ∈ω)
        where
        go3 : Σ[ n ∈ ℕ ] (γ ≡ # n) → ⟨ sucV γ ∈ˢ α ⟩
        go3 (n , q) = Empty.rec (∈-irrefl ω (ω-ord .fst ω∈α α∈ω))
          where
          α∈ω : ⟨ α ∈ˢ ω ⟩
          α∈ω = subst (λ w → ⟨ w ∈ˢ ω ⟩) (sym (cong sucV q) ∙ sγ≡α) (#∈ω (suc n))
      go2 (inr (inl γ≡ω)) = Empty.rec (leastα ω ω∈α (∣ subst (λ w → ⟪ ω ⟫ ≃ ⟪ w ⟫) (sym α≡sucω) csbω ∣₁))
        where
        module SW = Shiftω
        module IW = Incl ω ω-ord
        csbω : ⟪ ω ⟫ ≃ ⟪ sucV ω ⟫
        csbω = CSB.csb (⟪ ω ⟫) (⟪ sucV ω ⟫) (isSet⟪⟫ ω) (isSet⟪⟫ (sucV ω))
                 IW.incl IW.incl-inj SW.shift SW.shift-inj
        α≡sucω : α ≡ sucV ω
        α≡sucω = sym sγ≡α ∙ cong sucV γ≡ω
      go2 (inr (inr ω∈γ)) = Empty.rec (leastα γ γ∈α (∣ subst (λ w → ⟪ γ ⟫ ≃ ⟪ w ⟫) sγ≡α csbγ ∣₁))
        where
        γ∉ω' : ⟨ γ ∈ˢ ω ⟩ → Empty.⊥
        γ∉ω' h = ∈-irrefl ω (ω-ord .fst ω∈γ h)
        module SA = ShiftAbs γ oγ γ∉ω' (λ k → oγ .fst {x = ω} {y = # k} (#∈ω k) ω∈γ)
        module IG = Incl γ oγ
        csbγ : ⟪ γ ⟫ ≃ ⟪ sucV γ ⟫
        csbγ = CSB.csb (⟪ γ ⟫) (⟪ sucV γ ⟫) (isSet⟪⟫ γ) (isSet⟪⟫ (sucV γ))
                 IG.incl IG.incl-inj SA.shift SA.shift-inj

  initα : SQ.Init α
  initα = oα , ω∈α , succ-closure , noinj²

  sqαT : ∥ SQ.sq α ∥₁
  sqαT = SQ.via-col-truncated α initα

-- The non-initial case |α| ∈ α with only the truncated equivalence and
-- the truncated IH.  Both eliminate into the proposition ∥ sq α ∥₁;
-- inside the branch the honest equivalence transports the honest
-- pairing of κ to a pairing of α.
module NonInitialT (α : S) (oα : IsOrd α) (ω∈α : ⟨ ω ∈ˢ α ⟩)
  (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  (κ : S) (oκ : IsOrd κ) (κ-eqα : ∥ ⟪ κ ⟫ ≃ ⟪ α ⟫ ∥₁)
  (κ∈α : ⟨ κ ∈ˢ α ⟩) (κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥)
  (sqκT : ∥ SQ.sq κ ∥₁) where

  pair : (e : ⟪ κ ⟫ ≃ ⟪ α ⟫) → SQ.sq κ → ⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫
  pair e sqκ (x , y) = equivFun e (sqκ .fst (invEq e x , invEq e y))

  pair-inj : (e : ⟪ κ ⟫ ≃ ⟪ α ⟫) (sqκ : SQ.sq κ)
           → (p q : ⟪ α ⟫ × ⟪ α ⟫) → pair e sqκ p ≡ pair e sqκ q → p ≡ q
  pair-inj e sqκ (x , y) (x' , y') h = ΣPathP (x≡x' , y≡y')
    where
    hκ : sqκ .fst (invEq e x , invEq e y) ≡ sqκ .fst (invEq e x' , invEq e y')
    hκ = sym (retEq e (sqκ .fst (invEq e x , invEq e y)))
       ∙ cong (invEq e) h
       ∙ retEq e (sqκ .fst (invEq e x' , invEq e y'))
    pκ : (invEq e x , invEq e y) ≡ (invEq e x' , invEq e y')
    pκ = sqκ .snd (invEq e x , invEq e y) (invEq e x' , invEq e y') hκ
    x≡x' : x ≡ x'
    x≡x' = sym (secEq e x) ∙ cong (equivFun e) (cong fst pκ) ∙ secEq e x'
    y≡y' : y ≡ y'
    y≡y' = sym (secEq e y) ∙ cong (equivFun e) (cong snd pκ) ∙ secEq e y'

  sqαT : ∥ SQ.sq α ∥₁
  sqαT = PT.rec squash₁ (λ e → PT.rec squash₁
           (λ sqκ → ∣ pair e sqκ , pair-inj e sqκ ∣₁) sqκT) κ-eqα

-- The chain, truncated:  sq at every infinite ordinal, as a
-- proposition.  The wall of [LJ-1.107] (the honest injection α ↪ |α|)
-- is gone:  the non-initial branch needs only the truncated equivalence
-- and the truncated IH, and both eliminate into the proposition.
module TruncatedChain where

  P : S → Type (ℓ-suc ℓ)
  P α = IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ∥ SQ.sq α ∥₁

  sqωT : ∥ SQ.sq ω ∥₁
  sqωT = ∣ NumeralPresentation.pairω , NumeralPresentation.pairω-inj ∣₁

  step : (α : S) → ((β : S) → β ∈ᵗ α → P β) → P α
  step α ih oα α∉ω = go (ord-tri ω ω-ord α oα)
    where
    go : (⟨ ω ∈ˢ α ⟩ ⊎ ((ω ≡ α) ⊎ ⟨ α ∈ˢ ω ⟩)) → ∥ SQ.sq α ∥₁
    go (inr (inl ω≡α)) = subst (λ w → ∥ SQ.sq w ∥₁) ω≡α sqωT
    go (inr (inr α∈ω)) = Empty.rec (α∉ω α∈ω)
    go (inl ω∈α) = split (∈sucV-elim {A = α} {x = LC0.κ}
      {P = ⟨ LC0.κ ∈ˢ α ⟩ ⊎ (LC0.κ ≡ α)}
      (isProp⊎ (snd (LC0.κ ∈ˢ α)) (isSetS LC0.κ α)
        (λ m e → ∈-irrefl α (subst (λ w → ⟨ w ∈ˢ α ⟩) e m)))
      LC0.κ∈sα (λ q → inl q) (λ q → inr q))
      where
      module LC0 = LeastCard α oα
      ih' : (β : S) → ⟨ β ∈ˢ α ⟩ → IsOrd β → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → ∥ SQ.sq β ∥₁
      ih' β β∈α = ih β β∈α
      split : (⟨ LC0.κ ∈ˢ α ⟩ ⊎ (LC0.κ ≡ α)) → ∥ SQ.sq α ∥₁
      split (inr κ≡α) = InitialCaseT.sqαT α oα ω∈α leastα ih'
        where
        leastα : (δ : S) → ⟨ δ ∈ˢ α ⟩ → ∥ ⟪ δ ⟫ ≃ ⟪ α ⟫ ∥₁ → Empty.⊥
        leastα δ δ∈α δ≃α = LC0.κ-min-at δ δ∈κ δ≃α
          where
          δ∈κ : ⟨ δ ∈ˢ LC0.κ ⟩
          δ∈κ = subst (λ w → ⟨ δ ∈ˢ w ⟩) (sym κ≡α) δ∈α
      split (inl κ∈α) = NIT.sqαT
        where
        module NK = NonInitKappaNotOmega α oα ω∈α α∉ω LC0.κ LC0.oκ LC0.κ-eqα κ∈α
        module NIT = NonInitialT α oα ω∈α α∉ω LC0.κ LC0.oκ LC0.κ-eqα κ∈α
                       NK.κ∉ω (ih' LC0.κ κ∈α LC0.oκ NK.κ∉ω)

  theorem : (α : S) → P α
  theorem = ∈-induction step

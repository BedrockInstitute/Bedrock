{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.392] PROBE.  Two obligations at a GENERIC ordinal:
--
--   suc-absorb : the hotel shift.  An ordinal that holds omega absorbs one
--     new point: send the ordinal itself to the numeral 0 inside it, send
--     every member that lies in omega to its own successor, fix the rest.
--     BUILT, GREEN at Probe392.agda:PART 1.
--
--   amb-limit : Init's THIRD conjunct from an ambient no-injection
--     hypothesis.  REFUTED: the statement is FALSE, and the refutation is
--     built in Agda at PART 3.  The obstruction site is alpha := sucV omega,
--     gamma := omega: the ambient clause is VACUOUS there because no member
--     of sucV omega contains omega, while the conclusion demands
--     sucV omega in sucV omega.  The obligation below is left as a hole.
--
-- It runs in agents/tasks/LJ-1-392/ and lands nothing in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import L.Constructible using ( IsOrd )

module LJ-1-392.Probe392 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim; self∈sucV )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; ω-ord; ω-mem-ord; #∈ω )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.InjChain {ℓ} lem using ( ω-limit; ω∉β )
open import L.Cardinal {ℓ} lem using ( _↪_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet {ℓ} using ( sucV; #_; ω )
open import Cubical.Data.Sum as Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Nat using ( ℕ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

-- =====================================================================
-- PART 0.  THE W3 SPLIT, FIRST.  The brief names the widest unmeasured
-- term: whether the member of sucV gamma can be TAGGED as data, and at
-- which level `lem` is spent to do it.
--
-- THE ANSWER.  The tag is built from TWO lem decisions and from nothing
-- else.  `lem` is spent at hProp (ℓ-suc ℓ), on `x ∈ˢ gamma` and on
-- `x ∈ˢ omega`, both pure hProps, and the membership premise `x ∈ sucV
-- gamma` is NOT consumed by the tag at all.  No truncation is eliminated
-- on the way to data.  The membership premise is spent only inside
-- PROPOSITIONAL side conditions, through `∈sucV-elim`, which is exactly
-- the cure the tree already uses.
-- =====================================================================

data Three : Type where
  num fix top : Three

decide∈ : (x a : V ℓ) → ⟨ x ∈ˢ a ⟩ ⊎ ((⟨ x ∈ˢ a ⟩ → Empty.⊥))
decide∈ x a = lem (x ∈ˢ a)

three-way : (γ x : V ℓ) → ⟨ x ∈ˢ sucV γ ⟩ → Three
three-way γ x x∈ = pick (decide∈ x γ) (decide∈ x ω)
  where
  pick : (⟨ x ∈ˢ γ ⟩ ⊎ ((⟨ x ∈ˢ γ ⟩ → Empty.⊥)))
       → (⟨ x ∈ˢ ω ⟩ ⊎ ((⟨ x ∈ˢ ω ⟩ → Empty.⊥))) → Three
  pick (inl _) (inl _) = num
  pick (inl _) (inr _) = fix
  pick (inr _) _       = top

-- The classification, as a propositional reading of the tag's third
-- case.  `V` itself lives at Type (ℓ-suc ℓ), so a path between sets is
-- already at the eliminator's level and no lifting is needed.
sucV-class : (A x : V ℓ) → ⟨ x ∈ˢ sucV A ⟩ → (⟨ x ∈ˢ A ⟩ → x ≡ A) → x ≡ A
sucV-class A x x∈ kA =
  ∈sucV-elim {A = A} {x = x} {P = x ≡ A} (setIsSet x A) x∈ kA (λ x≡A → x≡A)

-- A member of sucV gamma outside gamma IS gamma.  This is the alignment
-- between the tag's `top` and the set, and it stays propositional.
top→≡ : (γ x : V ℓ) → (⟨ x ∈ˢ γ ⟩ → Empty.⊥) → ⟨ x ∈ˢ sucV γ ⟩ → x ≡ γ
top→≡ γ x ¬x∈γ x∈ = sucV-class γ x x∈ (λ x∈γ → Empty.rec (¬x∈γ x∈γ))

-- sucV is injective on members of omega: both sides are ordinals, the
-- two easy classification branches die on irreflexivity, the middle one
-- on the transitivity of one side's ordinalhood.  No numeral is read.
shift-inj : (x y : V ℓ) → ⟨ x ∈ˢ ω ⟩ → ⟨ y ∈ˢ ω ⟩ → sucV x ≡ sucV y → x ≡ y
shift-inj x y x∈ω y∈ω e = sucV-class y x x∈sucVy kA
  where
  x∈sucVy : ⟨ x ∈ˢ sucV y ⟩
  x∈sucVy = subst (λ z → ⟨ x ∈ˢ z ⟩) e (self∈sucV x)
  y∈sucVx : ⟨ y ∈ˢ sucV x ⟩
  y∈sucVx = subst (λ z → ⟨ y ∈ˢ z ⟩) (sym e) (self∈sucV y)
  kA : ⟨ x ∈ˢ y ⟩ → x ≡ y
  kA x∈y = sym (sucV-class x y y∈sucVx kA′)
    where
    kA′ : ⟨ y ∈ˢ x ⟩ → y ≡ x
    kA′ y∈x = Empty.rec (∈-irrefl x ((fst (ω-mem-ord x x∈ω)) x∈y y∈x))

-- =====================================================================
-- PART 1.  THE HOTEL SHIFT.  The obligation.
--
--   suc-absorb : (γ : V ℓ) → IsOrd γ → ⟨ ω ∈ γ ⟩ → ⟪ sucV γ ⟫ ↪ ⟪ γ ⟫
--
-- The image of a member x of sucV gamma, built from the two decisions:
--   x itself is gamma      ->  # 0, which lies in gamma through omega
--   x in gamma and in omega  ->  sucV x, which stays in omega, so in gamma
--   x in gamma, outside omega ->  x, fixed
--
-- The injectivity proof consumes the same decisions as ARGUMENTS, so the
-- image reduces clause by clause inside it (the [LJ-1.390] lesson: bind
-- the decision outside, never inside).  The membership premise is spent
-- only in the two clauses that need the classification, both of which
-- conclude a PATH, which is a proposition.
-- =====================================================================

suc-absorb : (γ : V ℓ) → IsOrd γ → ⟨ ω ∈ γ ⟩ → ⟪ sucV γ ⟫ ↪ ⟪ γ ⟫
suc-absorb γ oγ ω∈γ = f , f-inj
  where
  zero∈γ : ⟨ # 0 ∈ γ ⟩
  zero∈γ = (fst oγ) (#∈ω 0) ω∈γ

  img : (x : V ℓ)
      → (⟨ x ∈ˢ γ ⟩ ⊎ ((⟨ x ∈ˢ γ ⟩ → Empty.⊥)))
      → (⟨ x ∈ˢ ω ⟩ ⊎ ((⟨ x ∈ˢ ω ⟩ → Empty.⊥)))
      → Σ[ y ∈ V ℓ ] ⟨ y ∈ γ ⟩
  img x (inl x∈γ) (inl x∈ω) = sucV x , (fst oγ) (ω-limit x x∈ω) ω∈γ
  img x (inl x∈γ) (inr _)   = x , x∈γ
  img x (inr _)   _         = # 0 , zero∈γ

  f : ⟪ sucV γ ⟫ → ⟪ γ ⟫
  f m = fiber γ (snd (img (⟪ sucV γ ⟫↪ m) (decide∈ (⟪ sucV γ ⟫↪ m) γ)
                                           (decide∈ (⟪ sucV γ ⟫↪ m) ω))) .fst

  img-inj : (x y : V ℓ)
          → (dγx : ⟨ x ∈ˢ γ ⟩ ⊎ ((⟨ x ∈ˢ γ ⟩ → Empty.⊥)))
          → (dωx : ⟨ x ∈ˢ ω ⟩ ⊎ ((⟨ x ∈ˢ ω ⟩ → Empty.⊥)))
          → (dγy : ⟨ y ∈ˢ γ ⟩ ⊎ ((⟨ y ∈ˢ γ ⟩ → Empty.⊥)))
          → (dωy : ⟨ y ∈ˢ ω ⟩ ⊎ ((⟨ y ∈ˢ ω ⟩ → Empty.⊥)))
          → ⟨ x ∈ˢ sucV γ ⟩ → ⟨ y ∈ˢ sucV γ ⟩
          → (fst (img x dγx dωx) ≡ fst (img y dγy dωy))
          → x ≡ y

  -- both shifted: sucV is injective on omega-members
  img-inj x y (inl x∈γ) (inl x∈ω) (inl y∈γ) (inl y∈ω) mx my e =
    shift-inj x y x∈ω y∈ω e

  -- shifted against fixed: the fixpoint would land in omega
  img-inj x y (inl x∈γ) (inl x∈ω) (inl y∈γ) (inr ¬y∈ω) mx my e =
    Empty.rec (¬y∈ω (subst (λ z → ⟨ z ∈ˢ ω ⟩) e (ω-limit x x∈ω)))

  -- fixed against shifted: the mirror
  img-inj x y (inl x∈γ) (inr ¬x∈ω) (inl y∈γ) (inl y∈ω) mx my e =
    Empty.rec (¬x∈ω (subst (λ z → ⟨ z ∈ˢ ω ⟩) (sym e) (ω-limit y y∈ω)))

  -- both fixed: the image equation IS the goal
  img-inj x y (inl x∈γ) (inr _) (inl y∈γ) (inr _) mx my e = e

  -- shifted against the top: sucV x cannot be the empty set, for it
  -- holds x
  img-inj x y (inl x∈γ) (inl x∈ω) (inr ¬y∈γ) dωy mx my e =
    Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst
      (subst (λ z → ⟨ x ∈ˢ z ⟩) e (self∈sucV x))))

  -- fixed against the top: the numeral 0 is in omega, so the fixpoint
  -- would be in omega
  img-inj x y (inl x∈γ) (inr ¬x∈ω) (inr ¬y∈γ) dωy mx my e =
    Empty.rec (¬x∈ω (subst (λ z → ⟨ z ∈ˢ ω ⟩) (sym e) (#∈ω 0)))

  -- the top against shifted: the mirror of the empty-set clause
  img-inj x y (inr ¬x∈γ) dωx (inl y∈γ) (inl y∈ω) mx my e =
    Empty.rec (∅-empty y (∈∈ₛ {a = y} {b = ∅} .fst
      (subst (λ z → ⟨ y ∈ˢ z ⟩) (sym e) (self∈sucV y))))

  -- the top against fixed: the mirror of the numeral clause
  img-inj x y (inr ¬x∈γ) dωx (inl y∈γ) (inr ¬y∈ω) mx my e =
    Empty.rec (¬y∈ω (subst (λ z → ⟨ z ∈ˢ ω ⟩) e (#∈ω 0)))

  -- both are the top: both are gamma
  img-inj x y (inr ¬x∈γ) dωx (inr ¬y∈γ) dωy mx my e =
    top→≡ γ x ¬x∈γ mx ∙ sym (top→≡ γ y ¬y∈γ my)

  f-inj : (m n : ⟪ sucV γ ⟫) → f m ≡ f n → m ≡ n
  f-inj m n e = ↪-inj {a = sucV γ}
    (img-inj x y (decide∈ x γ) (decide∈ x ω) (decide∈ y γ) (decide∈ y ω)
      (member (sucV γ) m) (member (sucV γ) n) val-eq)
    where
    x : V ℓ
    x = ⟪ sucV γ ⟫↪ m
    y : V ℓ
    y = ⟪ sucV γ ⟫↪ n
    fibm = fiber γ (snd (img x (decide∈ x γ) (decide∈ x ω)))
    fibn = fiber γ (snd (img y (decide∈ y γ) (decide∈ y ω)))
    val-eq : fst (img x (decide∈ x γ) (decide∈ x ω))
              ≡ fst (img y (decide∈ y γ) (decide∈ y ω))
    val-eq = sym (snd fibm) ∙ cong (⟪ γ ⟫↪) e ∙ snd fibn

-- =====================================================================
-- PART 2.  THE SECOND OBLIGATION, AS THE BRIEF STATES IT.
--
-- `amb-limit` is FALSE.  The refutation is PART 3, in Agda, and the site
-- is alpha := sucV omega, gamma := omega.  The hole below is the formal
-- remainder: no term of this type exists if the ambient theory is
-- consistent, because PART 3 builds a term of its negation.
-- =====================================================================

amb-limit : (α : V ℓ) → IsOrd α → ⟨ ω ∈ α ⟩
        → ((β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩
                     → (⟪ α ⟫ ↪ ⟪ β ⟫) → Empty.⊥)
        → (γ : V ℓ) → ⟨ γ ∈ α ⟩ → ⟨ sucV γ ∈ α ⟩
amb-limit = ?

-- =====================================================================
-- PART 3.  THE REFUTATION.  Two terms, both green, both generic in
-- nothing: they name the one site.
--
-- (1) The ambient no-injection clause is VACUOUS at sucV omega.  A member
--     of sucV omega is a numeral or omega itself, no numeral contains
--     omega (`ω∉β`), and omega does not contain itself.  So the clause
--     holds at sucV omega with the injection never refuted.
-- (2) `amb-limit`, fed the vacuous clause, yields sucV omega in sucV
--     omega, which `∈-irrefl` kills.
-- =====================================================================

noinj-vacuous-sucω : (β : V ℓ) → IsOrd β → ⟨ β ∈ sucV ω ⟩ → ⟨ ω ∈ β ⟩
                   → (⟪ sucV ω ⟫ ↪ ⟪ β ⟫) → Empty.⊥
noinj-vacuous-sucω β oβ β∈ ω∈β inj = Empty.rec*
  (∈sucV-elim {A = ω} {x = β} {P = Empty.⊥* {ℓ-suc ℓ}} Empty.isProp⊥* β∈
    (λ β∈ω → lift (ω∉β β β∈ω ω∈β))
    (λ β≡ω → lift (∈-irrefl ω (subst (λ w → ⟨ ω ∈ w ⟩) β≡ω ω∈β))))

amb-limit-refuted : ((α : V ℓ) → IsOrd α → ⟨ ω ∈ α ⟩
                   → ((β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩
                                → (⟪ α ⟫ ↪ ⟪ β ⟫) → Empty.⊥)
                   → (γ : V ℓ) → ⟨ γ ∈ α ⟩ → ⟨ sucV γ ∈ α ⟩)
                  → Empty.⊥
amb-limit-refuted amb =
  ∈-irrefl (sucV ω)
    (amb (sucV ω) (suc-ord ω-ord) (self∈sucV ω) noinj-vacuous-sucω
         ω (self∈sucV ω))

-- =====================================================================
-- PART 4.  THE REPAIRED STATEMENT, GREEN.  The obstruction is EXACTLY the
-- member that does not contain omega.  Restrict the conclusion to members
-- gamma that DO contain omega, and the two `suc∈or≡` cases close: the
-- first is the goal, the second contradicts the ambient clause at
-- beta := gamma through `suc-absorb` itself.  No case split on gamma at
-- all: `suc∈or≡` delivers both cases.
-- =====================================================================

amb-limit-ω∈γ : (α : V ℓ) → IsOrd α → ⟨ ω ∈ α ⟩
  → ((β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩
               → (⟪ α ⟫ ↪ ⟪ β ⟫) → Empty.⊥)
  → (γ : V ℓ) → ⟨ γ ∈ α ⟩ → ⟨ ω ∈ γ ⟩ → ⟨ sucV γ ∈ α ⟩
amb-limit-ω∈γ α oα ω∈α noinj γ γ∈α ω∈γ =
  Sum.rec (λ s∈α → s∈α) (λ e → Empty.rec
    (noinj γ oγ γ∈α ω∈γ
      (subst (λ z → ⟪ z ⟫ ↪ ⟪ γ ⟫) e (suc-absorb γ oγ ω∈γ))))
  (suc∈or≡ γ α oγ oα γ∈α)
  where
  oγ : IsOrd γ
  oγ = mem-ord {A = α} oα γ γ∈α

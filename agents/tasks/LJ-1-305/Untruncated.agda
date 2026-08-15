{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.305] PROBE B.  Untruncate the descent of [LJ-1.301].
--
-- The join census (report section 3): the truncation of the delivered
-- descent enters at ONE irreducible join, the non-initial branch's
-- elimination of the classical existence Wat∥ into data.  Everything
-- else untruncates with tools already in the tree:
--
--   * the successor branch of [LJ-1.301] is REPLACED here by a
--     refutation: a successor is never initial, because `absorbs`
--     contradicts ambient initiality at the predecessor, and the
--     predecessor is extracted as data by `leastOf` over the ordinal's
--     own well-order, which delivers an INDEX and a PROPOSITIONAL
--     payload, never data;
--   * the initial branch delivers `via-col-square`, whose output is
--     already untruncated; its no-injection row consumes the law at
--     members under a propositional motive only.
--
-- So this file carries two descents:
--
--   SqI   no new principle.  Untruncated `sq α` at every AMBIENT-INITIAL
--         α, truncated elsewhere.  The row-4 consumption at a limit
--         initial α needs only the truncated form at members.
--   SqU   under ONE added module parameter, `InjData` below, named
--         exactly.  Fully untruncated at every gate, and the use-site
--         shape is `SqShape` (src/L/GCH.lagda.md:46-49) verbatim.
--
-- `sq-succ` of [LJ-1.301] is NOT needed: successors are handled by the
-- refutation inside the initial branch, and by transport inside the
-- non-initial branch.
--
-- Tracked probe.  ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-305.Untruncated {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; regularityV; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim; self∈sucV )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; ω-ord; #∈ω )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri; Tri )
open import L.Ordinal.SquareLaw {ℓ} lem
  using ( sq; via-col-square; ordSWO; module FiniteBase )
open import L.InjChain {ℓ} lem using ( squareω; ω-limit; ω∉β )
open import L.Absorption {ℓ} lem using ( absorbs )
open import L.Cardinal {ℓ} lem using ( _↪_ )
open import L.BoundedSubset {ℓ} lem using ( IsCardinal )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( SWO; IsLeast; leastOf )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV; #_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sigma using ( _×_; ΣPathP )
open import Cubical.Data.Nat using ( ℕ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; isPropPropTrunc )
import Cubical.Induction.WellFounded as WF

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- A member of an ordinal embeds its index.  Copied verbatim from
-- [LJ-1.301] (its landing should reuse
-- L.BoundedSubset.Devlin55.ord-emb, src/L/BoundedSubset.lagda.md:1370).
ord-mem-emb : (a b : V ℓ) → IsOrd b → ⟨ a ∈ˢ b ⟩ → ⟪ a ⟫ ↪ ⟪ b ⟫
ord-mem-emb a b ob a∈b = f , inj
  where
  f : ⟪ a ⟫ → ⟪ b ⟫
  f m = fiber b {x = ⟪ a ⟫↪ m} (ob .fst (member a m) a∈b) .fst
  inj : (m n : ⟪ a ⟫) → f m ≡ f n → m ≡ n
  inj m n e = ↪-inj {a = a}
    ( sym (fiber b {x = ⟪ a ⟫↪ m} (ob .fst (member a m) a∈b) .snd)
    ∙ cong (⟪ b ⟫↪) e
    ∙ fiber b {x = ⟪ a ⟫↪ n} (ob .fst (member a n) a∈b) .snd )

-- THE NON-INITIAL TRANSPORT.  Copied verbatim from [LJ-1.301].
sq-transport : (α δ : V ℓ) → IsOrd α → ⟨ δ ∈ˢ α ⟩
             → ⟪ α ⟫ ↪ ⟪ δ ⟫ → sq δ → sq α
sq-transport α δ oα δ∈α e (g , gi) = h , hinj
  where
  include : ⟪ δ ⟫ ↪ ⟪ α ⟫
  include = ord-mem-emb δ α oα δ∈α
  h : ⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫
  h (a , b) = include .fst (g (e .fst a , e .fst b))
  hinj : (p q : ⟪ α ⟫ × ⟪ α ⟫) → h p ≡ h q → p ≡ q
  hinj (a₁ , a₂) (b₁ , b₂) eq =
    ΣPathP ( e .snd a₁ b₁ (cong fst pq) , e .snd a₂ b₂ (cong snd pq) )
    where
    gh : g (e .fst a₁ , e .fst a₂) ≡ g (e .fst b₁ , e .fst b₂)
    gh = include .snd (g (e .fst a₁ , e .fst a₂))
                     (g (e .fst b₁ , e .fst b₂)) eq
    pq : (e .fst a₁ , e .fst a₂) ≡ (e .fst b₁ , e .fst b₂)
    pq = gi _ _ gh

-- THE CLASSICAL EXISTENCE.  Some member of α absorbs α's index.
Wat : (α : V ℓ) → Type (ℓ-suc ℓ)
Wat α = Σ[ δ ∈ V ℓ ] (⟨ δ ∈ˢ α ⟩ × (⟪ α ⟫ ↪ ⟪ δ ⟫))

-- THE PRINCIPLE, NAMED EXACTLY.  Untruncated injection selection at
-- the descent's one data-consuming site.  This is the data form of the
-- least-cardinal injection the tree records as truncated at
-- src/L/Cardinal.lagda.md:132-133.
InjData : Type (ℓ-suc ℓ)
InjData = (α : V ℓ) → IsOrd α → ⟨ ω ∈ˢ α ⟩ → ∥ Wat α ∥₁ → Wat α

-- Successor extraction by the least-element search.  `leastOf`
-- (src/L/WellOrder/Base.lagda.md:158) takes a truncated existence over
-- a well-order and returns an INDEX with a PROPOSITIONAL payload.  The
-- payload here is a negation, so nothing is lost.
NoSuc : (α : V ℓ) (m : ⟪ α ⟫) → hProp (ℓ-suc ℓ)
NoSuc α m = (⟨ sucV (⟪ α ⟫↪ m) ∈ˢ α ⟩ → Empty.⊥)
          , isPropΠ (λ _ → Empty.isProp⊥)

esc-wit : (α : V ℓ) → (oα : IsOrd α)
        → (((γ : V ℓ) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩) → Empty.⊥)
        → Σ[ m ∈ ⟪ α ⟫ ] (⟨ sucV (⟪ α ⟫↪ m) ∈ˢ α ⟩ → Empty.⊥)
esc-wit α oα ¬lim = go (lem (Q , isPropPropTrunc))
  where
  -- The order is SEALED, the medicine of `L.Cardinal`'s `LeastCardInjL`
  -- (src/L/Cardinal.lagda.md:85-92): transparent, every conversion
  -- check that `leastOf` runs re-unfolds the ordinal's union
  -- representation, and the clause exhausts an 8 GB heap.  MEASURED
  -- at this probe.
  opaque
    wα : SWO ⟪ α ⟫
    wα = ordSWO α oα

  Q : Type (ℓ-suc ℓ)
  Q = ∥ Σ[ m ∈ ⟪ α ⟫ ] (⟨ sucV (⟪ α ⟫↪ m) ∈ˢ α ⟩ → Empty.⊥) ∥₁

  go : Q ⊎ (Q → Empty.⊥)
     → Σ[ m ∈ ⟪ α ⟫ ] (⟨ sucV (⟪ α ⟫↪ m) ∈ˢ α ⟩ → Empty.⊥)
  go (inl q) = fst big , fst (snd big)
    where big = leastOf wα lem (NoSuc α) q
  go (inr ¬q) = Empty.rec (¬lim lim)
    where
    lim : (γ : V ℓ) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩
    lim γ γ∈α = dec (lem (sucV γ ∈ˢ α))
      where
      dec : ⟨ sucV γ ∈ˢ α ⟩ ⊎ (⟨ sucV γ ∈ˢ α ⟩ → Empty.⊥)
          → ⟨ sucV γ ∈ˢ α ⟩
      dec (inl h) = h
      dec (inr ¬h) = Empty.rec
        (¬q ∣ (fiber α γ∈α .fst)
             , (λ sh → ¬h (subst (λ z → ⟨ sucV z ∈ˢ α ⟩)
                            (fiber α γ∈α .snd) sh)) ∣₁)
-- The successor path, copied verbatim from [LJ-1.301].
sγ≡α : (α γ : V ℓ) → IsOrd α → ⟨ γ ∈ˢ α ⟩
     → (⟨ sucV γ ∈ˢ α ⟩ → Empty.⊥) → sucV γ ≡ α
sγ≡α α γ oα γ∈α ¬sγ =
  tri (ord-tri (sucV γ) (suc-ord (mem-ord {A = α} oα γ γ∈α)) α oα)
  where
  tri : Tri (sucV γ) α → sucV γ ≡ α
  tri (inl sγ∈α) = Empty.rec (¬sγ sγ∈α)
  tri (inr (inl e)) = e
  tri (inr (inr α∈sγ)) = Empty.rec (lower
    (∈sucV-elim {A = γ} {x = α} {P = Lift {j = ℓ-suc ℓ} (Empty.⊥)}
      (λ p q → Empty.rec (lower p))
      α∈sγ
      (λ α∈γ → lift (∈-irrefl α (oα .fst α∈γ γ∈α)))
      (λ α≡γ → lift (∈-irrefl γ
        (subst (λ w → ⟨ γ ∈ˢ w ⟩) α≡γ γ∈α)))))

-- A successor is never initial: `absorbs` contradicts ambient
-- initiality at the predecessor.  This closes the successor-inside-
-- initial branch without any truncated successor decision.
succ-not-initial : (α : V ℓ) → IsOrd α → ⟨ ω ∈ˢ α ⟩
                → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ⟨ isL α ⟩
                → (γ : V ℓ) → ⟨ γ ∈ˢ α ⟩
                → (⟨ sucV γ ∈ˢ α ⟩ → Empty.⊥) → IsCardinal α → Empty.⊥
succ-not-initial α oα ω∈α nfin isLα γ γ∈α ¬sγ card =
  card γ γ∈α
    (subst (λ z → ⟪ z ⟫ ↪ ⟪ γ ⟫) e
       (absorbs (γ , isLγ) oγ γ∉ω numerals))
  where
  e : sucV γ ≡ α
  e = sγ≡α α γ oα γ∈α ¬sγ
  oγ : IsOrd γ
  oγ = mem-ord {A = α} oα γ γ∈α
  isLγ : ⟨ isL γ ⟩
  isLγ = isL-trans γ∈α isLα
  γ∉ω : (⟨ γ ∈ˢ ω ⟩ → Empty.⊥)
  γ∉ω γ∈ω = nfin (subst (λ z → ⟨ z ∈ˢ ω ⟩) e (ω-limit γ γ∈ω))
  numerals : (k : ℕ) → ⟨ # k ∈ γ ⟩
  numerals k =
    ∈sucV-elim {A = γ} {x = ω} {P = ⟨ # k ∈ γ ⟩} (snd (# k ∈ γ))
      (subst (λ z → ⟨ ω ∈ˢ z ⟩) (sym e) ω∈α)
      (λ ω∈γ → mem-ord {A = α} oα γ γ∈α .fst (#∈ω k) ω∈γ)
      (λ ω≡γ → subst (λ z → ⟨ # k ∈ z ⟩) ω≡γ (#∈ω k))

-- =====================================================================
-- DESCENT ONE.  No new principle.  Untruncated at ambient-initial α,
-- truncated elsewhere.
-- =====================================================================

SqI : V ℓ → Type (ℓ-suc ℓ)
SqI α = IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ⟨ isL α ⟩
      → (IsCardinal α → sq α) × ∥ sq α ∥₁

stepI : (α : V ℓ) → ((β : V ℓ) → ⟨ β ∈ˢ α ⟩ → SqI β) → SqI α
stepI α IH oα nfin isLα = main (ord-tri α oα ω ω-ord)
  where
  main : Tri α ω → (IsCardinal α → sq α) × ∥ sq α ∥₁
  main (inl α∈ω) = Empty.rec (nfin α∈ω)
  main (inr (inl α≡ω)) =
    (λ _ → base) , ∣ base ∣₁
    where
    base = subst (λ z → sq z) (sym α≡ω) squareω
  main (inr (inr ω∈α)) = noninitial (lem (∥ Wat α ∥₁ , isPropPropTrunc))
    where
    card : (∥ Wat α ∥₁ → Empty.⊥) → IsCardinal α
    card ¬w δ δ∈α e = ¬w ∣ δ , δ∈α , e ∣₁

    noninitial : ∥ Wat α ∥₁ ⊎ (∥ Wat α ∥₁ → Empty.⊥)
               → (IsCardinal α → sq α) × ∥ sq α ∥₁
    noninitial (inl w) =
      (λ cardα → Empty.rec
        (PT.rec Empty.isProp⊥ (λ { (δ , δ∈α , e) → cardα δ δ∈α e }) w))
      , PT.rec isPropPropTrunc
          (λ { (δ , δ∈α , e) →
            PT.rec isPropPropTrunc
              (λ sqδ → ∣ sq-transport α δ oα δ∈α e sqδ ∣₁)
              (IH δ δ∈α (mem-ord {A = α} oα δ δ∈α)
                 (λ δ∈ω → FiniteBase.finite-excl α oα ω∈α δ
                    (mem-ord {A = α} oα δ δ∈α) δ∈ω
                    (λ x → (e .fst x , e .fst x))
                    (λ x y h → e .snd x y (cong fst h)))
                 (isL-trans δ∈α isLα) .snd) })
          w
    noninitial (inr ¬w) = limit (lem (Lim , isPropLim))
      where
      Lim : Type (ℓ-suc ℓ)
      Lim = (γ : V ℓ) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩
      isPropLim : isProp Lim
      isPropLim = isPropΠ (λ γ → isPropΠ (λ _ → snd (sucV γ ∈ˢ α)))

      limit : Lim ⊎ (Lim → Empty.⊥) → (IsCardinal α → sq α) × ∥ sq α ∥₁
      limit (inl lim) =
        (λ _ → via-col-square α (oα , ω∈α , lim , noinj))
        , ∣ via-col-square α (oα , ω∈α , lim , noinj) ∣₁
        where
        noinj : (β : V ℓ) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
              → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
              → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥
        noinj β oβ β∈α ω∈β f finj =
          PT.rec Empty.isProp⊥
            (λ sqβ → card ¬w β β∈α
              ((λ m → sqβ .fst (f m)) ,
               (λ m n h → finj m n (sqβ .snd (f m) (f n) h))))
            (IH β β∈α oβ (λ β∈ω → ω∉β β β∈ω ω∈β)
               (isL-trans β∈α isLα) .snd)
      limit (inr ¬lim) =
        (λ cardα → Empty.rec (refute cardα))
        , Empty.rec (refute (card ¬w))
        where
        refute : IsCardinal α → Empty.⊥
        refute cardα =
          succ-not-initial α oα ω∈α nfin isLα (⟪ α ⟫↪ m₀) (member α m₀)
            ¬s₀ cardα
          where
          m₀ = fst (esc-wit α oα ¬lim)
          ¬s₀ = snd (esc-wit α oα ¬lim)

sq-descentI : (α : V ℓ) → SqI α
sq-descentI = WF.WFI.induction regularityV {P = SqI} stepI

-- THE UNCONDITIONAL FRAGMENT.  The law, untruncated, at every
-- ambient-initial ordinal.  No principle beyond `lem`.
sq-initial : (α : V ℓ) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ⟨ isL α ⟩
           → IsCardinal α → sq α
sq-initial α oα nfin isLα cardα = fst (sq-descentI α oα nfin isLα) cardα

-- =====================================================================
-- DESCENT TWO.  Under the one added principle, fully untruncated.
-- =====================================================================

module WithInj (injdata : InjData) where

  SqU : V ℓ → Type (ℓ-suc ℓ)
  SqU α = IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ⟨ isL α ⟩ → sq α

  stepU : (α : V ℓ) → ((β : V ℓ) → ⟨ β ∈ˢ α ⟩ → SqU β) → SqU α
  stepU α IH oα nfin isLα = main (ord-tri α oα ω ω-ord)
    where
    main : Tri α ω → sq α
    main (inl α∈ω) = Empty.rec (nfin α∈ω)
    main (inr (inl α≡ω)) = subst (λ z → sq z) (sym α≡ω) squareω
    main (inr (inr ω∈α)) = noninitial (lem (∥ Wat α ∥₁ , isPropPropTrunc))
      where
      card : (∥ Wat α ∥₁ → Empty.⊥) → IsCardinal α
      card ¬w δ δ∈α e = ¬w ∣ δ , δ∈α , e ∣₁

      noninitial : ∥ Wat α ∥₁ ⊎ (∥ Wat α ∥₁ → Empty.⊥) → sq α
      noninitial (inl w) =
        sq-transport α δ oα δ∈α e
          (IH δ δ∈α (mem-ord {A = α} oα δ δ∈α)
             (λ δ∈ω → FiniteBase.finite-excl α oα ω∈α δ
                (mem-ord {A = α} oα δ δ∈α) δ∈ω
                (λ x → (e .fst x , e .fst x))
                (λ x y h → e .snd x y (cong fst h)))
             (isL-trans δ∈α isLα))
        where
        δ = fst (injdata α oα ω∈α w)
        δ∈α = fst (snd (injdata α oα ω∈α w))
        e = snd (snd (injdata α oα ω∈α w))
      noninitial (inr ¬w) = limit (lem (Lim , isPropLim))
        where
        Lim : Type (ℓ-suc ℓ)
        Lim = (γ : V ℓ) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩
        isPropLim : isProp Lim
        isPropLim = isPropΠ (λ γ → isPropΠ (λ _ → snd (sucV γ ∈ˢ α)))

        limit : Lim ⊎ (Lim → Empty.⊥) → sq α
        limit (inl lim) = via-col-square α (oα , ω∈α , lim , noinj)
          where
          noinj : (β : V ℓ) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
                → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
                → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥
          noinj β oβ β∈α ω∈β f finj =
            card ¬w β β∈α
              ((λ m → gβ .fst (f m)) ,
               (λ m n h → finj m n (gβ .snd (f m) (f n) h)))
            where gβ = IH β β∈α oβ (λ β∈ω → ω∉β β β∈ω ω∈β)
                            (isL-trans β∈α isLα)
        limit (inr ¬lim) = Empty.rec
          (succ-not-initial α oα ω∈α nfin isLα γ₀ γ₀∈α (snd esc) (card ¬w))
          where
          esc : Σ[ m ∈ ⟪ α ⟫ ] (⟨ sucV (⟪ α ⟫↪ m) ∈ˢ α ⟩ → Empty.⊥)
          esc = esc-wit α oα ¬lim
          γ₀ = ⟪ α ⟫↪ (fst esc)
          γ₀∈α = member α (fst esc)

  sq-descentᵘ : (α : V ℓ) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
              → ⟨ isL α ⟩ → sq α
  sq-descentᵘ = WF.WFI.induction regularityV {P = SqU} stepU

  -- THE USE-SITE SHAPE.  `SqShape` (src/L/GCH.lagda.md:46-49)
  -- verbatim: the ambient injection form is `sq` ([LJ-1.300] test 4).
  sq-shape : (α : S) → IsOrd (fst α) → (⟨ fst α ∈ˢ ω ⟩ → Empty.⊥)
           → (⟪ fst α ⟫ × ⟪ fst α ⟫) ↪ ⟪ fst α ⟫
  sq-shape α oα nfin = sq-descentᵘ (fst α) oα nfin (snd α)

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.301] PROBE.  The descent from squareomega, by well-founded
-- induction on membership.
--
-- [LJ-1.300] measured that the dependency descends: `Init`'s fourth row
-- quantifies over MEMBERS of alpha, strictly below alpha, and the base
-- `squareomega` bypasses `Init` entirely.  What was NOT delivered is the
-- recursion.  This file builds it.
--
-- The recursion principle is `WF.WFI.induction regularityV`, the same
-- one `L.Ordinal.Linear` uses at src/L/Ordinal/Linear.lagda.md:137.
-- Regularity of the ambient hierarchy makes membership well founded on
-- ALL of V, so the induction hypothesis is available at every member.
--
-- The motive gates the law on three things only: ordinal, outside
-- omega, in L.  NO cardinality gate: `Init`'s fourth row needs the law
-- at EVERY infinite member, and a cardinality gate on the motive would
-- starve it.  The step then runs one classical initiality decision and
-- four branches:
--
--   base        alpha = omega          squareomega (L.InjChain:184)
--   successor   alpha = sucV gamma      absorbs + the law at gamma
--   noninitial  some member absorbs it  transport through that member
--   initial     a limit ordinal         Init, fourth row from the IH
--
-- The conclusion is TRUNCATED.  The noninitial branch consumes a
-- classical existence whose payload is an injection, and a truncated
-- existence can only be eliminated under a propositional motive.  The
-- tree hits the same wall at `L.Cardinal`'s `kappa-inj`
-- (src/L/Cardinal.lagda.md:124-126, "still truncated, still not an
-- hProp").  So the descent delivers the law AT EACH ORDINAL as a
-- proposition; the untruncated function object `SqShape` needs the
-- noninitial transport as data, which is the least-cardinal-injection
-- debt the route already prices.
--
-- Tracked probe.  ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-301.Descent {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; regularityV; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim; self∈sucV )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; ω-ord; #∈ω )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri; Tri )
open import L.Ordinal.SquareLaw {ℓ} lem
  using ( sq; via-col-square; module FiniteBase )
open import L.InjChain {ℓ} lem using ( squareω; ω-limit; ω∉β )
open import L.Absorption {ℓ} lem using ( absorbs )
open import L.Cardinal {ℓ} lem using ( _↪_ )
open import L.BoundedSubset {ℓ} lem using ( IsCardinal )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV; #_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sigma using ( _×_; ΣPathP )
open import Cubical.Data.Nat using ( ℕ )
import Cubical.Data.Empty as Empty
import Cubical.Induction.WellFounded as WF
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; isPropPropTrunc )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- A member of an ordinal embeds its index.  The same statement and the
-- same proof as `L.BoundedSubset.Devlin55.ord-emb`
-- (src/L/BoundedSubset.lagda.md:1370), restated here so the probe does
-- not import the condensation chapter.  A landing should reuse that one.
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

-- THE SUCCESSOR STEP.  The law at `sucV gamma` from the law at
-- `gamma`: absorb the successor into gamma, pair by gamma's law, and
-- include gamma back into its successor.
sq-succ : (γ : V ℓ) → ⟨ isL γ ⟩ → IsOrd γ
        → (⟨ γ ∈ˢ ω ⟩ → Empty.⊥) → ((k : ℕ) → ⟨ # k ∈ γ ⟩)
        → sq γ → sq (sucV γ)
sq-succ γ isLγ oγ γ∉ω numerals (g , gi) = h , hinj
  where
  absorb : ⟪ sucV γ ⟫ ↪ ⟪ γ ⟫
  absorb = absorbs (γ , isLγ) oγ γ∉ω numerals
  include : ⟪ γ ⟫ ↪ ⟪ sucV γ ⟫
  include = ord-mem-emb γ (sucV γ) (suc-ord oγ) (self∈sucV γ)
  h : ⟪ sucV γ ⟫ × ⟪ sucV γ ⟫ → ⟪ sucV γ ⟫
  h (a , b) = include .fst (g (absorb .fst a , absorb .fst b))
  hinj : (p q : ⟪ sucV γ ⟫ × ⟪ sucV γ ⟫) → h p ≡ h q → p ≡ q
  hinj (a₁ , a₂) (b₁ , b₂) eq =
    ΣPathP ( absorb .snd a₁ b₁ (cong fst pq)
           , absorb .snd a₂ b₂ (cong snd pq) )
    where
    gh : g (absorb .fst a₁ , absorb .fst a₂) ≡ g (absorb .fst b₁ , absorb .fst b₂)
    gh = include .snd (g (absorb .fst a₁ , absorb .fst a₂))
                     (g (absorb .fst b₁ , absorb .fst b₂)) eq
    pq : (absorb .fst a₁ , absorb .fst a₂) ≡ (absorb .fst b₁ , absorb .fst b₂)
    pq = gi _ _ gh

-- THE NON-INITIAL STEP.  Some member `delta` of alpha absorbs alpha's
-- index.  Pair by delta's law and include delta back into alpha.
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

-- THE MOTIVE.  The law at every ordinal outside omega that lies in L,
-- as a proposition.  No cardinality gate: `Init`'s fourth row consumes
-- the law at EVERY infinite member, so a gate here would starve it.
Sq∥ : V ℓ → Type (ℓ-suc ℓ)
Sq∥ α = IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ⟨ isL α ⟩ → ∥ sq α ∥₁

-- THE STEP.  Every recursive call is at a MEMBER of alpha, so
-- `regularityV` carries the recursion.
step : (α : V ℓ) → ((β : V ℓ) → ⟨ β ∈ˢ α ⟩ → Sq∥ β) → Sq∥ α
step α IH oα nfin isLα = main (ord-tri α oα ω ω-ord)
  where
  main : Tri α ω → ∥ sq α ∥₁
  main (inl α∈ω) = Empty.rec (nfin α∈ω)
  main (inr (inl α≡ω)) = subst (λ z → ∥ sq z ∥₁) (sym α≡ω) ∣ squareω ∣₁
  main (inr (inr ω∈α)) = noninitial (lem (Wat∥ , isPropPropTrunc))
    where
    -- The classical initiality decision.  Either some member of alpha
    -- absorbs alpha's index, or alpha is initial: the negative side IS
    -- `IsCardinal`, ambient initiality, with no cardinal face named at
    -- any statement.
    Wat∥ : Type (ℓ-suc ℓ)
    Wat∥ = ∥ Σ[ δ ∈ V ℓ ] (⟨ δ ∈ˢ α ⟩ × (⟪ α ⟫ ↪ ⟪ δ ⟫)) ∥₁

    initial : (Wat∥ → Empty.⊥) → IsCardinal α
    initial ¬w δ δ∈α e = ¬w ∣ δ , δ∈α , e ∣₁

    noninitial : Wat∥ ⊎ (Wat∥ → Empty.⊥) → ∥ sq α ∥₁
    noninitial (inl w) =
      PT.rec isPropPropTrunc
        (λ { (δ , δ∈α , e) →
          PT.rec isPropPropTrunc
            (λ sqδ → ∣ sq-transport α δ oα δ∈α e sqδ ∣₁)
            (IH δ δ∈α (mem-ord {A = α} oα δ δ∈α)
               (λ δ∈ω → FiniteBase.finite-excl α oα ω∈α δ
                          (mem-ord {A = α} oα δ δ∈α) δ∈ω
                          (λ x → (e .fst x , e .fst x))
                          (λ x y h → e .snd x y (cong fst h)))
               (isL-trans δ∈α isLα)) })
        w
    noninitial (inr ¬w) = limit (lem (Lim , isPropLim))
      where
      Lim : Type (ℓ-suc ℓ)
      Lim = (γ : V ℓ) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩
      isPropLim : isProp Lim
      isPropLim = isPropΠ (λ γ → isPropΠ (λ _ → snd (sucV γ ∈ˢ α)))

      limit : Lim ⊎ (Lim → Empty.⊥) → ∥ sq α ∥₁
      limit (inl lim) = ∣ via-col-square α (oα , ω∈α , lim , noinj) ∣₁
        where
        -- THE FOURTH ROW, from the induction hypothesis: [LJ-1.300]'s
        -- `descent-step` with `SqBelow` supplied by the recursion.
        noinj : (β : V ℓ) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
              → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
              → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥
        noinj β oβ β∈α ω∈β f finj =
          PT.rec Empty.isProp⊥
            (λ sqβ → initial ¬w β β∈α
              ((λ m → sqβ .fst (f m)) ,
               (λ m n h → finj m n (sqβ .snd (f m) (f n) h))))
            (IH β β∈α oβ (λ β∈ω → ω∉β β β∈ω ω∈β) (isL-trans β∈α isLα))
      limit (inr ¬lim) = successor (lem (Succ∥ , isPropPropTrunc))
        where
        Succ∥ : Type (ℓ-suc ℓ)
        Succ∥ = ∥ Σ[ γ ∈ V ℓ ]
                 (⟨ γ ∈ˢ α ⟩ × (⟨ sucV γ ∈ˢ α ⟩ → Empty.⊥)) ∥₁

        -- From the negative side of the successor decision, `alpha` is
        -- successor closed, so the split is exhaustive.
        successor : Succ∥ ⊎ (Succ∥ → Empty.⊥) → ∥ sq α ∥₁
        successor (inl s) =
          PT.rec isPropPropTrunc
            (λ { (γ , γ∈α , ¬sγ) →
              PT.rec isPropPropTrunc
                (λ sqγ → ∣ subst (λ z → sq z) (sγ≡α γ γ∈α ¬sγ)
                                  (sq-succ γ (isL-trans γ∈α isLα)
                                    (mem-ord {A = α} oα γ γ∈α)
                                    (γ∉ω γ γ∈α ¬sγ)
                                    (numerals γ γ∈α ¬sγ) sqγ) ∣₁)
                (IH γ γ∈α (mem-ord {A = α} oα γ γ∈α) (γ∉ω γ γ∈α ¬sγ)
                   (isL-trans γ∈α isLα)) })
            s
          where
          -- `alpha` is the successor of `gamma`: the other two cases of
          -- the trichotomy contradict irreflexivity.
          sγ≡α : (γ : V ℓ) → ⟨ γ ∈ˢ α ⟩ → (⟨ sucV γ ∈ˢ α ⟩ → Empty.⊥)
               → sucV γ ≡ α
          sγ≡α γ γ∈α ¬sγ =
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

          γ∉ω : (γ : V ℓ) → ⟨ γ ∈ˢ α ⟩ → (⟨ sucV γ ∈ˢ α ⟩ → Empty.⊥)
              → ⟨ γ ∈ˢ ω ⟩ → Empty.⊥
          γ∉ω γ γ∈α ¬sγ γ∈ω =
            nfin (subst (λ z → ⟨ z ∈ˢ ω ⟩) (sγ≡α γ γ∈α ¬sγ) (ω-limit γ γ∈ω))

          -- Numerals: omega is a member of alpha, hence of sucV gamma's
          -- predecessor or equal to it.
          numerals : (γ : V ℓ) → ⟨ γ ∈ˢ α ⟩
                   → (⟨ sucV γ ∈ˢ α ⟩ → Empty.⊥) → (k : ℕ) → ⟨ # k ∈ γ ⟩
          numerals γ γ∈α ¬sγ k =
            ∈sucV-elim {A = γ} {x = ω} {P = ⟨ # k ∈ γ ⟩} (snd (# k ∈ γ))
              (subst (λ z → ⟨ ω ∈ˢ z ⟩) (sym (sγ≡α γ γ∈α ¬sγ)) ω∈α)
              (λ ω∈γ → mem-ord {A = α} oα γ γ∈α .fst (#∈ω k) ω∈γ)
              (λ ω≡γ → subst (λ z → ⟨ # k ∈ z ⟩) ω≡γ (#∈ω k))
        successor (inr ¬s) = Empty.rec (¬lim lim)
          where
          lim : Lim
          lim γ γ∈α = at (lem (sucV γ ∈ˢ α))
            where
            at : ⟨ sucV γ ∈ˢ α ⟩ ⊎ (⟨ sucV γ ∈ˢ α ⟩ → Empty.⊥)
               → ⟨ sucV γ ∈ˢ α ⟩
            at (inl h) = h
            at (inr ¬h) = Empty.rec (¬s ∣ γ , γ∈α , ¬h ∣₁)

-- THE DESCENT.
sq-descent : (α : V ℓ) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
           → ⟨ isL α ⟩ → ∥ sq α ∥₁
sq-descent = WF.WFI.induction regularityV {P = Sq∥} step

-- THE USE-SITE SHAPE.  The law at every infinite L-ordinal, as a
-- proposition.  This is `SqShape` (src/L/GCH.lagda.md:46-48) with each
-- instance truncated; `sq` and the ambient `_↪_` are the same type
-- ([LJ-1.300] test 4).
sq-shape∥ : (α : S) → IsOrd (fst α) → (⟨ fst α ∈ˢ ω ⟩ → Empty.⊥)
          → ∥ sq (fst α) ∥₁
sq-shape∥ α oα nfin = sq-descent (fst α) oα nfin (snd α)

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.92] probe A: the order-type construction at a generic carrier.
--
-- The route's step 2 needs, for a well-order R on a subset of omega:
--   * the ordinal ot R with an order isomorphism (field R, R) ≅ (ot R, ∈);
--   * uniqueness for isomorphic well-orders.
--
-- The tree already delivers the collapse-of-a-well-order pattern once,
-- pinned to one carrier: src/L/Ordinal/SquareLaw.lagda.md:373-480 (the
-- col machinery on Pair) and the archived order-type assembly at
-- archive/rud-route/src/L/Ordinal/Pairing.lagda.md:436-575.  This probe
-- re-instantiates that pattern at a generic well-order, given as an SWO
-- record (src/L/WellOrder/Base.lagda.md), and measures the recursion's
-- shape, the isomorphism's shape and uniqueness for isomorphic orders.
--
-- The carrier X : Type ℓ and the record SWO X are module parameters.
-- The adequacy lemmas that translate a V-set-of-pairs well-order into an
-- SWO record belong to route step 1 and are not built here.
--
-- Untracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth

module ProbeLJ192A {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim; self∈sucV )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( suc-ord; setUnion-ord; ∅-ord )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( SWO; Tri; lt; eq; gt; module SWO )
open import Cubical.Induction.WellFounded using ( module WFI )

import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett; seteq )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⋃_; union-ax; ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( sucV )

open hPropStructure 𝒮ᵥ

-- The order type of a strict well-order, built exactly as the delivered
-- collapse pattern (src/L/Ordinal/SquareLaw.lagda.md:373-480) but with
-- the carrier and its SWO record as module parameters instead of the
-- square of an ordinal's index.
module OrderType (X : Type ℓ) (swo : SWO X) where

  module S = SWO swo

  _≺_ : X → X → Type (ℓ-suc ℓ)
  _≺_ = S._<∙_

  -- decidability of the order falls out of trichotomy, no LEM needed
  ≺-dec : (a b : X) → (a ≺ b) ⊎ ((a ≺ b) → Empty.⊥)
  ≺-dec a b = go (S.tri∙ a b)
    where
    go : Tri (a ≺ b) (a ≡ b) (b ≺ a) → (a ≺ b) ⊎ ((a ≺ b) → Empty.⊥)
    go (lt h) = inl h
    go (eq p) = inr (λ h → S.irr∙ b (subst (λ w → w ≺ b) p h))
    go (gt h) = inr (λ h' → S.irr∙ a (S.trans∙ a b a h' h))

  colPick : (p : X) (rec : ∀ r → r ≺ p → S) (r : X)
          → (r ≺ p) ⊎ ((r ≺ p) → Empty.⊥) → S
  colPick p rec r (inl pr) = sucV (rec r pr)
  colPick p rec r (inr _)  = ∅

  colStep : (p : X) → (∀ r → r ≺ p → S) → S
  colStep p rec = ⋃ (sett X (λ r → colPick p rec r (≺-dec r p)))

  module W = WFI (S.wf∙)

  opaque
    col : X → S
    col = W.induction {P = λ _ → S} colStep

    col-compute : (p : X) → col p ≡ colStep p (λ r _ → col r)
    col-compute = W.induction-compute colStep

  col-ord : (p : X) → IsOrd (col p)
  col-ord = W.induction {P = λ p → IsOrd (col p)} step
    where
    step : (p : X) → (∀ r → r ≺ p → IsOrd (col r)) → IsOrd (col p)
    step p ih = subst IsOrd (sym (col-compute p)) (setUnion-ord X g gOrd)
      where
      g : X → S
      g r = colPick p (λ r _ → col r) r (≺-dec r p)
      gOrd : (r : X) → IsOrd (g r)
      gOrd r = go (≺-dec r p)
        where
        go : (d : (r ≺ p) ⊎ ((r ≺ p) → Empty.⊥))
           → IsOrd (colPick p (λ r _ → col r) r d)
        go (inl pr) = suc-ord (ih r pr)
        go (inr _)  = ∅-ord

  col-mono : {p q : X} → p ≺ q → ⟨ col p ∈ˢ col q ⟩
  col-mono {p} {q} pq =
    subst (λ w → ⟨ col p ∈ˢ w ⟩) (sym (col-compute q))
      (∈∈ₛ {a = col p} {b = ⋃ (sett X g)} .snd
        (union-ax (sett X g) (col p) .snd
          ∣ sucV (col p) , (w∈ₛsett , colp∈ₛsuc) ∣₁))
    where
    g : X → S
    g r = colPick q (λ r _ → col r) r (≺-dec r q)
    gq : g p ≡ sucV (col p)
    gq = go (≺-dec p q)
      where
      go : (d : (p ≺ q) ⊎ ((p ≺ q) → Empty.⊥))
         → colPick q (λ r _ → col r) p d ≡ sucV (col p)
      go (inl _) = refl
      go (inr ¬pq) = Empty.rec (¬pq pq)
    w∈ₛsett : ⟨ sucV (col p) ∈ₛ sett X g ⟩
    w∈ₛsett = ∈∈ₛ {a = sucV (col p)} {b = sett X g} .fst ∣ p , gq ∣₁
    colp∈ₛsuc : ⟨ col p ∈ₛ sucV (col p) ⟩
    colp∈ₛsuc = ∈∈ₛ {a = col p} {b = sucV (col p)} .fst (self∈sucV (col p))

  col-inj : {p q : X} → col p ≡ col q → p ≡ q
  col-inj {p} {q} e = go (S.tri∙ p q)
    where
    go : Tri (p ≺ q) (p ≡ q) (q ≺ p) → p ≡ q
    go (lt pq) = Empty.rec
      (∈-irrefl (col q) (subst (λ w → ⟨ w ∈ˢ col q ⟩) e (col-mono pq)))
    go (eq r)  = r
    go (gt qp) = Empty.rec
      (∈-irrefl (col p) (subst (λ w → ⟨ w ∈ˢ col p ⟩) (sym e) (col-mono qp)))

  col-img : (q : X) (b : S) → ⟨ b ∈ˢ col q ⟩
          → ∥ Σ[ p ∈ X ] (col p ≡ b) ∥₁
  col-img = W.induction {P = P} step
    where
    P : X → Type (ℓ-suc ℓ)
    P q = (b : S) → ⟨ b ∈ˢ col q ⟩ → ∥ Σ[ p ∈ X ] (col p ≡ b) ∥₁

    g : (q : X) → X → S
    g q r = colPick q (λ r _ → col r) r (≺-dec r q)

    g-inl : (q : X) (r : X) (pr : r ≺ q) → g q r ≡ sucV (col r)
    g-inl q r pr = go (≺-dec r q)
      where
      go : (d : (r ≺ q) ⊎ ((r ≺ q) → Empty.⊥))
         → colPick q (λ r _ → col r) r d ≡ sucV (col r)
      go (inl _) = refl
      go (inr ¬pr) = Empty.rec (¬pr pr)

    g-inr : (q : X) (r : X) (¬pr : (r ≺ q) → Empty.⊥) → g q r ≡ ∅
    g-inr q r ¬pr = go (≺-dec r q)
      where
      go : (d : (r ≺ q) ⊎ ((r ≺ q) → Empty.⊥))
         → colPick q (λ r _ → col r) r d ≡ ∅
      go (inl pr) = Empty.rec (¬pr pr)
      go (inr _) = refl

    step : (q : X) → (∀ r → r ≺ q → P r) → P q
    step q ih b b∈cq = viaUnion (subst (λ w → ⟨ b ∈ˢ w ⟩) (col-compute q) b∈cq)
      where
      U : S
      U = ⋃ (sett X (g q))

      go2 : (v : S) → ⟨ b ∈ₛ v ⟩ → Σ[ r ∈ X ] (g q r ≡ v)
          → ∥ Σ[ p ∈ X ] (col p ≡ b) ∥₁
      go2 v b∈ₛv (r , gr≡v) = decide (≺-dec r q)
        where
        b∈gr : ⟨ b ∈ₛ g q r ⟩
        b∈gr = subst (λ w → ⟨ b ∈ₛ w ⟩) (sym gr≡v) b∈ₛv

        decide : (r ≺ q) ⊎ ((r ≺ q) → Empty.⊥)
               → ∥ Σ[ p ∈ X ] (col p ≡ b) ∥₁
        decide (inl pr) = ∈sucV-elim {A = col r} {x = b} squash₁ b∈sr
          (λ b∈r → ih r pr b b∈r)
          (λ b≡r → ∣ r , sym b≡r ∣₁)
          where
          b∈sr : ⟨ b ∈ˢ sucV (col r) ⟩
          b∈sr = ∈∈ₛ {a = b} {b = sucV (col r)} .snd
            (subst (λ w → ⟨ b ∈ₛ w ⟩) (g-inl q r pr) b∈gr)
        decide (inr ¬pr) =
          Empty.rec (∅-empty b (subst (λ w → ⟨ b ∈ₛ w ⟩) (g-inr q r ¬pr) b∈gr))

      go1 : Σ[ v ∈ S ] (⟨ v ∈ₛ sett X (g q) ⟩ × ⟨ b ∈ₛ v ⟩)
          → ∥ Σ[ p ∈ X ] (col p ≡ b) ∥₁
      go1 (v , (v∈ₛsett , b∈ₛv)) = PT.rec squash₁ (go2 v b∈ₛv)
        (∈∈ₛ {a = v} {b = sett X (g q)} .snd v∈ₛsett)

      viaUnion : ⟨ b ∈ˢ U ⟩ → ∥ Σ[ p ∈ X ] (col p ≡ b) ∥₁
      viaUnion b∈ = PT.rec squash₁ go1
        (union-ax (sett X (g q)) b .fst
          (∈∈ₛ {a = b} {b = U} .fst b∈))

  -- the order type of the whole well-order: the union of the successors
  -- of the collapses (the archived order-type section, Pairing:436-575)
  τ : S
  τ = ⋃ (sett X (λ p → sucV (col p)))

  τ-ord : IsOrd τ
  τ-ord = setUnion-ord X (λ p → sucV (col p)) (λ p → suc-ord (col-ord p))

  col∈τ : (p : X) → ⟨ col p ∈ˢ τ ⟩
  col∈τ p = ∈∈ₛ {a = col p} {b = τ} .snd
    (union-ax (sett X (λ q → sucV (col q))) (col p) .snd
      ∣ sucV (col p) , (w∈ₛsett , colp∈ₛsuc) ∣₁)
    where
    w∈ₛsett : ⟨ sucV (col p) ∈ₛ sett X (λ q → sucV (col q)) ⟩
    w∈ₛsett = ∈∈ₛ {a = sucV (col p)} {b = sett X (λ q → sucV (col q))} .fst
      ∣ p , refl ∣₁
    colp∈ₛsuc : ⟨ col p ∈ₛ sucV (col p) ⟩
    colp∈ₛsuc = ∈∈ₛ {a = col p} {b = sucV (col p)} .fst (self∈sucV (col p))

  opaque
    cf : (p : X) → Σ[ m ∈ ⟪ τ ⟫ ] (⟪ τ ⟫↪ m ≡ col p)
    cf p = fiber τ (col∈τ p)

    col→τ : X → ⟪ τ ⟫
    col→τ p = cf p .fst

    col→τ-fiber : (p : X) → ⟪ τ ⟫↪ (col→τ p) ≡ col p
    col→τ-fiber p = cf p .snd

    col→τ-inj : {p q : X} → col→τ p ≡ col→τ q → p ≡ q
    col→τ-inj {p} {q} e =
      col-inj (sym (col→τ-fiber p) ∙ cong (⟪ τ ⟫↪) e ∙ col→τ-fiber q)

  col-surj : (b : S) → ⟨ b ∈ˢ τ ⟩ → ∥ Σ[ p ∈ X ] (col p ≡ b) ∥₁
  col-surj b b∈τ = PT.rec squash₁ go1
    (union-ax (sett X (λ q → sucV (col q))) b .fst
      (∈∈ₛ {a = b} {b = τ} .fst b∈τ))
    where
    go2 : (v : S) → ⟨ b ∈ₛ v ⟩ → Σ[ q ∈ X ] (sucV (col q) ≡ v)
        → ∥ Σ[ p ∈ X ] (col p ≡ b) ∥₁
    go2 v b∈ₛv (q , sq≡v) = ∈sucV-elim {A = col q} {x = b} squash₁ b∈sq
      (λ b∈q → col-img q b b∈q)
      (λ b≡q → ∣ q , sym b≡q ∣₁)
      where
      b∈sq : ⟨ b ∈ˢ sucV (col q) ⟩
      b∈sq = ∈∈ₛ {a = b} {b = sucV (col q)} .snd
        (subst (λ w → ⟨ b ∈ₛ w ⟩) (sym sq≡v) b∈ₛv)

    go1 : Σ[ v ∈ S ] (⟨ v ∈ₛ sett X (λ q → sucV (col q)) ⟩ × ⟨ b ∈ₛ v ⟩)
        → ∥ Σ[ p ∈ X ] (col p ≡ b) ∥₁
    go1 (v , (v∈ₛsett , b∈ₛv)) = PT.rec squash₁ (go2 v b∈ₛv)
      (∈∈ₛ {a = v} {b = sett X (λ q → sucV (col q))} .snd v∈ₛsett)

  col→τ-surj : (m : ⟪ τ ⟫) → ∥ Σ[ p ∈ X ] (col→τ p ≡ m) ∥₁
  col→τ-surj m = PT.map hit (col-surj (⟪ τ ⟫↪ m) (member τ m))
    where
    hit : Σ[ p ∈ X ] (col p ≡ ⟪ τ ⟫↪ m) → Σ[ p ∈ X ] (col→τ p ≡ m)
    hit (p , e) = p , ↪-inj {a = τ} (col→τ-fiber p ∙ e)

  -- the isomorphism's backward half: the delivered tree has col-mono but
  -- not its converse; trichotomy plus ordinal transitivity close it
  col∈-bwd : {p q : X} → ⟨ col p ∈ˢ col q ⟩ → p ≺ q
  col∈-bwd {p} {q} h = go (S.tri∙ p q)
    where
    go : Tri (p ≺ q) (p ≡ q) (q ≺ p) → p ≺ q
    go (lt pq) = pq
    go (eq r) = Empty.rec
      (∈-irrefl (col q) (subst (λ w → ⟨ w ∈ˢ col q ⟩) (cong col r) h))
    go (gt qp) = Empty.rec
      (∈-irrefl (col p) (col-ord p .fst {x = col q} {y = col p}
        h (col-mono {q} {p} qp)))

  iso : (p q : X)
      → (⟨ col p ∈ˢ col q ⟩ → p ≺ q) × (p ≺ q → ⟨ col p ∈ˢ col q ⟩)
  iso p q = (λ h → col∈-bwd {p} {q} h) , (λ pq → col-mono {p} {q} pq)

  -- the order embedding of the carrier into the order type's index
  emb-mono : {p q : X} → p ≺ q
           → ⟨ ⟪ τ ⟫↪ (col→τ p) ∈ˢ ⟪ τ ⟫↪ (col→τ q) ⟩
  emb-mono {p} {q} pq =
    subst (λ w → ⟨ w ∈ˢ ⟪ τ ⟫↪ (col→τ q) ⟩) (sym (col→τ-fiber p))
      (subst (λ w → ⟨ col p ∈ˢ w ⟩) (sym (col→τ-fiber q))
        (col-mono {p} {q} pq))

  emb-mono-bwd : {p q : X} → ⟨ ⟪ τ ⟫↪ (col→τ p) ∈ˢ ⟪ τ ⟫↪ (col→τ q) ⟩ → p ≺ q
  emb-mono-bwd {p} {q} h =
    col∈-bwd {p} {q}
      (subst (λ w → ⟨ col p ∈ˢ w ⟩) (col→τ-fiber q)
        (subst (λ w → ⟨ w ∈ˢ ⟪ τ ⟫↪ (col→τ q) ⟩) (col→τ-fiber p) h))

-- uniqueness: two isomorphic well-orders have equal order types.  The
-- isomorphism is a bijective order-embedding given as data (forward and
-- backward order preservation, plus surjectivity), so no choice is
-- needed.  The proof carries the collapse equality across the
-- isomorphism by well-founded induction, then lifts it to the unions.
module Unique (X Y : Type ℓ) (w : SWO X) (v : SWO Y) where

  module S₁ = SWO w
  module S₂ = SWO v

  _≺₁_ : X → X → Type (ℓ-suc ℓ)
  _≺₁_ = S₁._<∙_

  _≺₂_ : Y → Y → Type (ℓ-suc ℓ)
  _≺₂_ = S₂._<∙_

  record OrderIso : Type (ℓ-suc ℓ) where
    field
      f : X → Y
      f-mono : {a b : X} → a ≺₁ b → f a ≺₂ f b
      f-mono-bwd : {a b : X} → f a ≺₂ f b → a ≺₁ b
      f-surj : (y : Y) → ∥ Σ[ x ∈ X ] (f x ≡ y) ∥₁

  module O₁ = OrderType X w
  module O₂ = OrderType Y v

  module Uniq (iso : OrderIso) where
    open OrderIso iso

    g₁ : (x : X) → X → S
    g₁ x r = O₁.colPick x (λ r _ → O₁.col r) r (O₁.≺-dec r x)

    g₂ : (y : Y) → Y → S
    g₂ y s = O₂.colPick y (λ s _ → O₂.col s) s (O₂.≺-dec s y)

    g₁-inl : (x r : X) (pr : r ≺₁ x) → g₁ x r ≡ sucV (O₁.col r)
    g₁-inl x r pr = go (O₁.≺-dec r x)
      where
      go : (d : (O₁._≺_ r x) ⊎ ((O₁._≺_ r x) → Empty.⊥))
         → O₁.colPick x (λ r _ → O₁.col r) r d ≡ sucV (O₁.col r)
      go (inl _) = refl
      go (inr ¬pr) = Empty.rec (¬pr pr)

    g₁-inr : (x r : X) (¬pr : (r ≺₁ x) → Empty.⊥) → g₁ x r ≡ ∅
    g₁-inr x r ¬pr = go (O₁.≺-dec r x)
      where
      go : (d : (O₁._≺_ r x) ⊎ ((O₁._≺_ r x) → Empty.⊥))
         → O₁.colPick x (λ r _ → O₁.col r) r d ≡ ∅
      go (inl pr) = Empty.rec (¬pr pr)
      go (inr _) = refl

    g₂-inl : (y s : Y) (ps : s ≺₂ y) → g₂ y s ≡ sucV (O₂.col s)
    g₂-inl y s ps = go (O₂.≺-dec s y)
      where
      go : (d : (O₂._≺_ s y) ⊎ ((O₂._≺_ s y) → Empty.⊥))
         → O₂.colPick y (λ s _ → O₂.col s) s d ≡ sucV (O₂.col s)
      go (inl _) = refl
      go (inr ¬ps) = Empty.rec (¬ps ps)

    g₂-inr : (y s : Y) (¬ps : (s ≺₂ y) → Empty.⊥) → g₂ y s ≡ ∅
    g₂-inr y s ¬ps = go (O₂.≺-dec s y)
      where
      go : (d : (O₂._≺_ s y) ⊎ ((O₂._≺_ s y) → Empty.⊥))
         → O₂.colPick y (λ s _ → O₂.col s) s d ≡ ∅
      go (inl ps) = Empty.rec (¬ps ps)
      go (inr _) = refl

    step-eq : (x : X)
            → ((r : X) → r ≺₁ x → O₁.col r ≡ O₂.col (f r))
            → sett X (g₁ x) ≡ sett Y (g₂ (f x))
    step-eq x ih = seteq X Y (g₁ x) (g₂ (f x)) (fwd x ih , bwd x ih)
      where
      fwd : (x : X)
          → ((r : X) → r ≺₁ x → O₁.col r ≡ O₂.col (f r))
          → (r : X) → ∥ Σ[ s ∈ Y ] (g₂ (f x) s ≡ g₁ x r) ∥₁
      fwd x ih r = go (O₁.≺-dec r x)
        where
        go : (d : (O₁._≺_ r x) ⊎ ((O₁._≺_ r x) → Empty.⊥))
           → ∥ Σ[ s ∈ Y ] (g₂ (f x) s ≡ g₁ x r) ∥₁
        go (inl pr) =
          ∣ f r , g₂-inl (f x) (f r) (f-mono pr)
                ∙ cong sucV (sym (ih r pr)) ∙ sym (g₁-inl x r pr) ∣₁
        go (inr ¬pr) =
          ∣ f x , g₂-inr (f x) (f x) (S₂.irr∙ (f x))
                ∙ sym (g₁-inr x r ¬pr) ∣₁

      bwd : (x : X)
          → ((r : X) → r ≺₁ x → O₁.col r ≡ O₂.col (f r))
          → (s : Y) → ∥ Σ[ r' ∈ X ] (g₁ x r' ≡ g₂ (f x) s) ∥₁
      bwd x ih s = PT.rec squash₁ go (f-surj s)
        where
        go : Σ[ r ∈ X ] (f r ≡ s) → ∥ Σ[ r' ∈ X ] (g₁ x r' ≡ g₂ (f x) s) ∥₁
        go (r , e) = decide (O₂.≺-dec s (f x))
          where
          decide : (d : (O₂._≺_ s (f x)) ⊎ ((O₂._≺_ s (f x)) → Empty.⊥))
                 → ∥ Σ[ r' ∈ X ] (g₁ x r' ≡ g₂ (f x) s) ∥₁
          decide (inl ps) =
            ∣ r , g₁-inl x r r≺x ∙ cong sucV (ih r r≺x)
                  ∙ cong sucV (cong (O₂.col) e)
                  ∙ sym (g₂-inl (f x) s ps) ∣₁
            where
            r≺x : r ≺₁ x
            r≺x = f-mono-bwd (subst (λ t → t ≺₂ f x) (sym e) ps)
          decide (inr ¬ps) = decide2 (O₁.≺-dec r x)
            where
            ¬fr : (f r ≺₂ f x) → Empty.⊥
            ¬fr h = ¬ps (subst (λ t → t ≺₂ f x) e h)
            decide2 : (d : (O₁._≺_ r x) ⊎ ((O₁._≺_ r x) → Empty.⊥))
                    → ∥ Σ[ r' ∈ X ] (g₁ x r' ≡ g₂ (f x) s) ∥₁
            decide2 (inl pr) = Empty.rec (¬fr (f-mono pr))
            decide2 (inr ¬pr) =
              ∣ r , g₁-inr x r ¬pr ∙ sym (g₂-inr (f x) s ¬ps) ∣₁

    col-iso : (x : X) → O₁.col x ≡ O₂.col (f x)
    col-iso = W.induction {P = P} step
      where
      module W = WFI (S₁.wf∙)
      P : X → Type (ℓ-suc ℓ)
      P x = O₁.col x ≡ O₂.col (f x)
      step : (x : X) → ((r : X) → r ≺₁ x → P r) → P x
      step x ih = O₁.col-compute x ∙ cong (⋃_) (step-eq x ih)
                ∙ sym (O₂.col-compute (f x))

    τ-eq : O₁.τ ≡ O₂.τ
    τ-eq = cong (⋃_) (seteq X Y h₁ h₂ (fwd , bwd))
      where
      h₁ : X → S
      h₁ x = sucV (O₁.col x)
      h₂ : Y → S
      h₂ y = sucV (O₂.col y)
      fwd : (x : X) → ∥ Σ[ y ∈ Y ] (h₂ y ≡ h₁ x) ∥₁
      fwd x = ∣ f x , cong sucV (sym (col-iso x)) ∣₁
      bwd : (y : Y) → ∥ Σ[ x ∈ X ] (h₁ x ≡ h₂ y) ∥₁
      bwd y = PT.map go (f-surj y)
        where
        go : Σ[ x ∈ X ] (f x ≡ y) → Σ[ x ∈ X ] (h₁ x ≡ h₂ y)
        go (x , e) = x , cong sucV (col-iso x ∙ cong (O₂.col) e)

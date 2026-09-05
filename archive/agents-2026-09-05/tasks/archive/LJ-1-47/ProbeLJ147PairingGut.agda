{-# OPTIONS --cubical --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ147PairingGut {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; regularityV; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim; self∈sucV )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; setUnion-ord; ∅-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; Tri; lt; eq; gt; module SWO )
open import ProbeLJ117Combinators {ℓₚ = ℓ-suc ℓ}
  using ( prodSWO )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⋃_; union-ax; ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( sucV )
open import Cubical.Induction.WellFounded
  using ( Acc; acc; WellFounded; module WFI )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module _ (α : S) (oα : IsOrd α) where

  _≺₁_ : ⟪ α ⟫ → ⟪ α ⟫ → Type (ℓ-suc ℓ)
  m ≺₁ n = ⟪ α ⟫↪ m ∈ᵗ ⟪ α ⟫↪ n

  ord-inord : (m : ⟪ α ⟫) → IsOrd (⟪ α ⟫↪ m)
  ord-inord m = mem-ord {A = α} oα (⟪ α ⟫↪ m) (member α m)

  tri₁ : (m n : ⟪ α ⟫) → Tri (m ≺₁ n) (m ≡ n) (n ≺₁ m)
  tri₁ m n = go (ord-tri (⟪ α ⟫↪ m) (ord-inord m) (⟪ α ⟫↪ n) (ord-inord n))
    where
    go : (⟨ ⟪ α ⟫↪ m ∈ˢ ⟪ α ⟫↪ n ⟩
          ⊎ ((⟪ α ⟫↪ m ≡ ⟪ α ⟫↪ n) ⊎ ⟨ ⟪ α ⟫↪ n ∈ˢ ⟪ α ⟫↪ m ⟩))
       → Tri (m ≺₁ n) (m ≡ n) (n ≺₁ m)
    go (inl h)       = lt h
    go (inr (inl p)) = eq (↪-inj {a = α} p)
    go (inr (inr h)) = gt h

  irr₁ : (m : ⟪ α ⟫) → (m ≺₁ m → Empty.⊥)
  irr₁ m h = ∈-irrefl (⟪ α ⟫↪ m) h

  trans₁ : (m n k : ⟪ α ⟫) → m ≺₁ n → n ≺₁ k → m ≺₁ k
  trans₁ m n k h h' = ord-inord k .fst h h'

  acc₁ : (m : ⟪ α ⟫) → Acc _∈ᵗ_ (⟪ α ⟫↪ m) → Acc _≺₁_ m
  acc₁ m (acc r) = acc (λ n n≺m → acc₁ n (r (⟪ α ⟫↪ n) n≺m))

  wf₁ : WellFounded _≺₁_
  wf₁ m = acc₁ m (regularityV (⟪ α ⟫↪ m))

  ordSWO : SWO ⟪ α ⟫
  ordSWO = record
    { _<∙_   = _≺₁_
    ; tri∙   = tri₁
    ; irr∙   = irr₁
    ; trans∙ = trans₁
    ; wf∙    = wf₁ }
  _≤₁_ : ⟪ α ⟫ → ⟪ α ⟫ → Type (ℓ-suc ℓ)
  m ≤₁ n = (m ≺₁ n) ⊎ (m ≡ n)

  maxGo : (m n : ⟪ α ⟫) → Tri (m ≺₁ n) (m ≡ n) (n ≺₁ m) → ⟪ α ⟫
  maxGo m n (lt _) = n
  maxGo m n (eq _) = m
  maxGo m n (gt _) = m

  maxOrd : ⟪ α ⟫ → ⟪ α ⟫ → ⟪ α ⟫
  maxOrd m n = maxGo m n (tri₁ m n)

  max-spec : (m n : ⟪ α ⟫) → (m ≤₁ maxOrd m n) × (n ≤₁ maxOrd m n)
  max-spec m n = go (tri₁ m n)
    where
    go : (t : Tri (m ≺₁ n) (m ≡ n) (n ≺₁ m))
       → (m ≤₁ maxGo m n t) × (n ≤₁ maxGo m n t)
    go (lt h) = inl h , inr refl
    go (eq p) = inr refl , inr (sym p)
    go (gt h) = inr refl , inl h
  Pair : Type ℓ
  Pair = ⟪ α ⟫ × ⟪ α ⟫

  _≺_ : Pair → Pair → Type (ℓ-suc ℓ)
  (a , b) ≺ (c , d) =
    (maxOrd a b ≺₁ maxOrd c d)
      ⊎ ((maxOrd a b ≡ maxOrd c d) × ((a ≺₁ c) ⊎ ((a ≡ c) × (b ≺₁ d))))

  tri≺ : (p q : Pair) → Tri (p ≺ q) (p ≡ q) (q ≺ p)
  tri≺ (a , b) (c , d) = M-case (tri₁ (maxOrd a b) (maxOrd c d))
    where
    Y-case : (e : maxOrd a b ≡ maxOrd c d) (f : a ≡ c)
           → Tri (b ≺₁ d) (b ≡ d) (d ≺₁ b)
           → Tri ((a , b) ≺ (c , d)) ((a , b) ≡ (c , d)) ((c , d) ≺ (a , b))
    Y-case e f (lt h) = lt (inr (e , inr (f , h)))
    Y-case e f (gt h) = gt (inr (sym e , inr (sym f , h)))
    Y-case e f (eq g) = eq (cong₂ _,_ f g)

    X-case : (e : maxOrd a b ≡ maxOrd c d)
           → Tri (a ≺₁ c) (a ≡ c) (c ≺₁ a)
           → Tri ((a , b) ≺ (c , d)) ((a , b) ≡ (c , d)) ((c , d) ≺ (a , b))
    X-case e (lt h) = lt (inr (e , inl h))
    X-case e (gt h) = gt (inr (sym e , inl h))
    X-case e (eq f) = Y-case e f (tri₁ b d)

    M-case : Tri (maxOrd a b ≺₁ maxOrd c d)
                 (maxOrd a b ≡ maxOrd c d)
                 (maxOrd c d ≺₁ maxOrd a b)
           → Tri ((a , b) ≺ (c , d)) ((a , b) ≡ (c , d)) ((c , d) ≺ (a , b))
    M-case (lt h) = lt (inl h)
    M-case (gt h) = gt (inl h)
    M-case (eq e) = X-case e (tri₁ a c)

  irr≺ : (p : Pair) → (p ≺ p → Empty.⊥)
  irr≺ (a , b) (inl h)              = irr₁ (maxOrd a b) h
  irr≺ (a , b) (inr (e , inl h))    = irr₁ a h
  irr≺ (a , b) (inr (e , inr (f , h))) = irr₁ b h

  trans≺ : (p q r : Pair) → p ≺ q → q ≺ r → p ≺ r
  trans≺ (a , b) (c , d) (e , f) = goM
    where
    M₁ = maxOrd a b
    M₂ = maxOrd c d
    M₃ = maxOrd e f

    goY : (b ≺₁ d) → (d ≺₁ f) → (b ≺₁ f)
    goY = trans₁ b d f

    goX : ((a ≺₁ c) ⊎ ((a ≡ c) × (b ≺₁ d)))
        → ((c ≺₁ e) ⊎ ((c ≡ e) × (d ≺₁ f)))
        → ((a ≺₁ e) ⊎ ((a ≡ e) × (b ≺₁ f)))
    goX (inl h) (inl h') = inl (trans₁ a c e h h')
    goX (inl h) (inr (e₂ , _)) = inl (subst (λ w → a ≺₁ w) e₂ h)
    goX (inr (e₁ , _)) (inl h') = inl (subst (λ w → w ≺₁ e) (sym e₁) h')
    goX (inr (e₁ , s₁)) (inr (e₂ , s₂)) = inr (e₁ ∙ e₂ , goY s₁ s₂)

    goM : ((M₁ ≺₁ M₂) ⊎ ((M₁ ≡ M₂) × ((a ≺₁ c) ⊎ ((a ≡ c) × (b ≺₁ d)))))
        → ((M₂ ≺₁ M₃) ⊎ ((M₂ ≡ M₃) × ((c ≺₁ e) ⊎ ((c ≡ e) × (d ≺₁ f)))))
        → ((M₁ ≺₁ M₃) ⊎ ((M₁ ≡ M₃) × ((a ≺₁ e) ⊎ ((a ≡ e) × (b ≺₁ f)))))
    goM (inl h) (inl h') = inl (trans₁ M₁ M₂ M₃ h h')
    goM (inl h) (inr (e₂ , _)) = inl (subst (λ w → M₁ ≺₁ w) e₂ h)
    goM (inr (e₁ , _)) (inl h') = inl (subst (λ w → w ≺₁ M₃) (sym e₁) h')
    goM (inr (e₁ , s₁)) (inr (e₂ , s₂)) = inr (e₁ ∙ e₂ , goX s₁ s₂)

  f : Pair → ⟪ α ⟫ × (⟪ α ⟫ × ⟪ α ⟫)
  f (a , b) = maxOrd a b , (a , b)

  f-inj : {p q : Pair} → f p ≡ f q → p ≡ q
  f-inj {a , b} {c , d} e = cong snd e

  lex2 : SWO (⟪ α ⟫ × ⟪ α ⟫)
  lex2 = prodSWO ordSWO ordSWO

  lex3 : SWO (⟪ α ⟫ × (⟪ α ⟫ × ⟪ α ⟫))
  lex3 = prodSWO ordSWO lex2

  module L3 = SWO lex3

  ¬<₁ : (m : ⟪ α ⟫) {n : ⟪ α ⟫} → m ≡ n → (m ≺₁ n → Empty.⊥)
  ¬<₁ m {n} q h = irr₁ m (subst (λ w → m ≺₁ w) (sym q) h)

  subrel : {p q : Pair} → p ≺ q → f p L3.<∙ f q
  subrel {a , b} {c , d} (inl h) =
    inl h
  subrel {a , b} {c , d} (inr (e , inl h)) =
    inr (¬<₁ (maxOrd a b) e , ¬<₁ (maxOrd c d) (sym e) , inl h)
  subrel {a , b} {c , d} (inr (e , inr (f , h))) =
    inr (¬<₁ (maxOrd a b) e , ¬<₁ (maxOrd c d) (sym e)
       , inr (¬<₁ a f , ¬<₁ c (sym f) , h))

  wf≺ : WellFounded _≺_
  wf≺ p = go (L3.wf∙ (f p))
    where
    go : {q : Pair} → Acc (L3._<∙_) (f q) → Acc _≺_ q
    go {q} (acc r) = acc (λ q' q'≺q → go (r (f q') (subrel {q'} {q} q'≺q)))

  godSWO : SWO Pair
  godSWO = record
    { _<∙_   = _≺_
    ; tri∙   = tri≺
    ; irr∙   = irr≺
    ; trans∙ = trans≺
    ; wf∙    = wf≺ }
  ≺₁-dec : (m n : ⟪ α ⟫) → (m ≺₁ n) ⊎ ((m ≺₁ n) → Empty.⊥)
  ≺₁-dec m n = go (tri₁ m n)
    where
    go : Tri (m ≺₁ n) (m ≡ n) (n ≺₁ m) → (m ≺₁ n) ⊎ ((m ≺₁ n) → Empty.⊥)
    go (lt h) = inl h
    go (eq p) = inr (λ h → irr₁ n (subst (λ w → w ≺₁ n) p h))
    go (gt h) = inr (λ h' → irr₁ m (trans₁ m n m h' h))

  ≡₁-dec : (m n : ⟪ α ⟫) → (m ≡ n) ⊎ ((m ≡ n) → Empty.⊥)
  ≡₁-dec m n = go (tri₁ m n)
    where
    go : Tri (m ≺₁ n) (m ≡ n) (n ≺₁ m) → (m ≡ n) ⊎ ((m ≡ n) → Empty.⊥)
    go (lt h) = inr (λ q → irr₁ m (subst (λ w → m ≺₁ w) (sym q) h))
    go (eq p) = inl p
    go (gt h) = inr (λ q → irr₁ n (subst (λ w → n ≺₁ w) q h))

  ≺-dec : (p q : Pair) → (p ≺ q) ⊎ ((p ≺ q) → Empty.⊥)
  ≺-dec (a , b) (c , d) = goM (≺₁-dec (maxOrd a b) (maxOrd c d))
                                (≡₁-dec (maxOrd a b) (maxOrd c d))
    where
    M₁ = maxOrd a b
    M₂ = maxOrd c d

    goY : ((M₁ ≺₁ M₂) → Empty.⊥) → (M₁ ≡ M₂) → ((a ≺₁ c) → Empty.⊥) → (a ≡ c)
        → (b ≺₁ d) ⊎ ((b ≺₁ d) → Empty.⊥)
        → ((a , b) ≺ (c , d)) ⊎ (((a , b) ≺ (c , d)) → Empty.⊥)
    goY ¬h e ¬h' f (inl h'') = inl (inr (e , inr (f , h'')))
    goY ¬h e ¬h' f (inr ¬h'') = inr refuteY
      where
      refuteY : ((a , b) ≺ (c , d)) → Empty.⊥
      refuteY (inl h) = ¬h h
      refuteY (inr (e' , inl x)) = ¬h' x
      refuteY (inr (e' , inr (f' , y))) = ¬h'' y

    goX : ((M₁ ≺₁ M₂) → Empty.⊥) → (M₁ ≡ M₂)
        → (a ≺₁ c) ⊎ ((a ≺₁ c) → Empty.⊥) → (a ≡ c) ⊎ ((a ≡ c) → Empty.⊥)
        → ((a , b) ≺ (c , d)) ⊎ (((a , b) ≺ (c , d)) → Empty.⊥)
    goX ¬h e (inl h') _ = inl (inr (e , inl h'))
    goX ¬h e (inr ¬h') (inl f) = goY ¬h e ¬h' f (≺₁-dec b d)
    goX ¬h e (inr ¬h') (inr ¬f) = inr refuteX
      where
      refuteX : ((a , b) ≺ (c , d)) → Empty.⊥
      refuteX (inl h) = ¬h h
      refuteX (inr (e' , inl x)) = ¬h' x
      refuteX (inr (e' , inr (f' , _))) = ¬f f'

    goM : (M₁ ≺₁ M₂) ⊎ ((M₁ ≺₁ M₂) → Empty.⊥)
        → (M₁ ≡ M₂) ⊎ ((M₁ ≡ M₂) → Empty.⊥)
        → ((a , b) ≺ (c , d)) ⊎ (((a , b) ≺ (c , d)) → Empty.⊥)
    goM (inl h) _ = inl (inl h)
    goM (inr ¬h) (inl e) = goX ¬h e (≺₁-dec a c) (≡₁-dec a c)
    goM (inr ¬h) (inr ¬e) = inr refuteM
      where
      refuteM : ((a , b) ≺ (c , d)) → Empty.⊥
      refuteM (inl h) = ¬h h
      refuteM (inr (e' , _)) = ¬e e'
  colPick : (p : Pair) (rec : ∀ r → r ≺ p → S) (r : Pair)
          → (r ≺ p) ⊎ ((r ≺ p) → Empty.⊥) → S
  colPick p rec r (inl pr) = sucV (rec r pr)
  colPick p rec r (inr _)  = ∅

  colStep : (p : Pair) → (∀ r → r ≺ p → S) → S
  colStep p rec = ⋃ (sett Pair (λ r → colPick p rec r (≺-dec r p)))

  module W = WFI wf≺

  opaque
    col : Pair → S
    col = W.induction {P = λ _ → S} colStep

    col-compute : (p : Pair) → col p ≡ colStep p (λ r _ → col r)
    col-compute = W.induction-compute colStep

  col-ord : (p : Pair) → IsOrd (col p)
  col-ord = W.induction {P = λ p → IsOrd (col p)} step
    where
    step : (p : Pair) → (∀ r → r ≺ p → IsOrd (col r)) → IsOrd (col p)
    step p ih = subst IsOrd (sym (col-compute p)) (setUnion-ord Pair g gOrd)
      where
      g : Pair → S
      g r = colPick p (λ r _ → col r) r (≺-dec r p)
      gOrd : (r : Pair) → IsOrd (g r)
      gOrd r = go (≺-dec r p)
        where
        go : (d : (r ≺ p) ⊎ ((r ≺ p) → Empty.⊥))
           → IsOrd (colPick p (λ r _ → col r) r d)
        go (inl pr) = suc-ord (ih r pr)
        go (inr _)  = ∅-ord

  col-mono : {p q : Pair} → p ≺ q → ⟨ col p ∈ˢ col q ⟩
  col-mono {p} {q} pq =
    subst (λ w → ⟨ col p ∈ˢ w ⟩) (sym (col-compute q))
      (∈∈ₛ {a = col p} {b = ⋃ (sett Pair g)} .snd
        (union-ax (sett Pair g) (col p) .snd
          ∣ sucV (col p) , (w∈ₛsett , colp∈ₛsuc) ∣₁))
    where
    g : Pair → S
    g r = colPick q (λ r _ → col r) r (≺-dec r q)
    gq : g p ≡ sucV (col p)
    gq = go (≺-dec p q)
      where
      go : (d : (p ≺ q) ⊎ ((p ≺ q) → Empty.⊥))
         → colPick q (λ r _ → col r) p d ≡ sucV (col p)
      go (inl _) = refl
      go (inr ¬pq) = Empty.rec (¬pq pq)
    w∈ₛsett : ⟨ sucV (col p) ∈ₛ sett Pair g ⟩
    w∈ₛsett = ∈∈ₛ {a = sucV (col p)} {b = sett Pair g} .fst ∣ p , gq ∣₁
    colp∈ₛsuc : ⟨ col p ∈ₛ sucV (col p) ⟩
    colp∈ₛsuc = ∈∈ₛ {a = col p} {b = sucV (col p)} .fst (self∈sucV (col p))

  col-inj : {p q : Pair} → col p ≡ col q → p ≡ q
  col-inj {p} {q} e = go (tri≺ p q)
    where
    go : Tri (p ≺ q) (p ≡ q) (q ≺ p) → p ≡ q
    go (lt pq) = Empty.rec
      (∈-irrefl (col q) (subst (λ w → ⟨ w ∈ˢ col q ⟩) e (col-mono pq)))
    go (eq r)  = r
    go (gt qp) = Empty.rec
      (∈-irrefl (col p) (subst (λ w → ⟨ w ∈ˢ col p ⟩) (sym e) (col-mono qp)))
  τ : S
  τ = ⋃ (sett Pair (λ p → sucV (col p)))

  τ-ord : IsOrd τ
  τ-ord = setUnion-ord Pair (λ p → sucV (col p)) (λ p → suc-ord (col-ord p))

  col∈τ : (p : Pair) → ⟨ col p ∈ˢ τ ⟩
  col∈τ p = ∈∈ₛ {a = col p} {b = τ} .snd
    (union-ax (sett Pair (λ q → sucV (col q))) (col p) .snd
      ∣ sucV (col p) , (w∈ₛsett , colp∈ₛsuc) ∣₁)
    where
    w∈ₛsett : ⟨ sucV (col p) ∈ₛ sett Pair (λ q → sucV (col q)) ⟩
    w∈ₛsett = ∈∈ₛ {a = sucV (col p)} {b = sett Pair (λ q → sucV (col q))} .fst
      ∣ p , refl ∣₁
    colp∈ₛsuc : ⟨ col p ∈ₛ sucV (col p) ⟩
    colp∈ₛsuc = ∈∈ₛ {a = col p} {b = sucV (col p)} .fst (self∈sucV (col p))

  postulate
    col→τ : Pair → ⟪ τ ⟫
    col→τ-fiber : (p : Pair) → ⟪ τ ⟫↪ (col→τ p) ≡ col p
    col→τ-inj : {p q : Pair} → col→τ p ≡ col→τ q → p ≡ q
  col-img : (q : Pair) (b : S) → ⟨ b ∈ˢ col q ⟩
          → ∥ Σ[ p ∈ Pair ] (col p ≡ b) ∥₁
  col-img = W.induction {P = P} step
    where
    P : Pair → Type (ℓ-suc ℓ)
    P q = (b : S) → ⟨ b ∈ˢ col q ⟩ → ∥ Σ[ p ∈ Pair ] (col p ≡ b) ∥₁

    g : (q : Pair) → Pair → S
    g q r = colPick q (λ r _ → col r) r (≺-dec r q)

    g-inl : (q : Pair) (r : Pair) (pr : r ≺ q) → g q r ≡ sucV (col r)
    g-inl q r pr = go (≺-dec r q)
      where
      go : (d : (r ≺ q) ⊎ ((r ≺ q) → Empty.⊥))
         → colPick q (λ r _ → col r) r d ≡ sucV (col r)
      go (inl _) = refl
      go (inr ¬pr) = Empty.rec (¬pr pr)

    g-inr : (q : Pair) (r : Pair) (¬pr : (r ≺ q) → Empty.⊥) → g q r ≡ ∅
    g-inr q r ¬pr = go (≺-dec r q)
      where
      go : (d : (r ≺ q) ⊎ ((r ≺ q) → Empty.⊥))
         → colPick q (λ r _ → col r) r d ≡ ∅
      go (inl pr) = Empty.rec (¬pr pr)
      go (inr _) = refl

    step : (q : Pair) → (∀ r → r ≺ q → P r) → P q
    step q ih b b∈cq = viaUnion (subst (λ w → ⟨ b ∈ˢ w ⟩) (col-compute q) b∈cq)
      where
      U : S
      U = ⋃ (sett Pair (g q))

      go2 : (v : S) → ⟨ b ∈ₛ v ⟩ → Σ[ r ∈ Pair ] (g q r ≡ v)
          → ∥ Σ[ p ∈ Pair ] (col p ≡ b) ∥₁
      go2 v b∈ₛv (r , gr≡v) = decide (≺-dec r q)
        where
        b∈gr : ⟨ b ∈ₛ g q r ⟩
        b∈gr = subst (λ w → ⟨ b ∈ₛ w ⟩) (sym gr≡v) b∈ₛv

        decide : (r ≺ q) ⊎ ((r ≺ q) → Empty.⊥)
               → ∥ Σ[ p ∈ Pair ] (col p ≡ b) ∥₁
        decide (inl pr) = ∈sucV-elim {A = col r} {x = b} squash₁ b∈sr
          (λ b∈r → ih r pr b b∈r)
          (λ b≡r → ∣ r , sym b≡r ∣₁)
          where
          b∈sr : ⟨ b ∈ˢ sucV (col r) ⟩
          b∈sr = ∈∈ₛ {a = b} {b = sucV (col r)} .snd
            (subst (λ w → ⟨ b ∈ₛ w ⟩) (g-inl q r pr) b∈gr)
        decide (inr ¬pr) =
          Empty.rec (∅-empty b (subst (λ w → ⟨ b ∈ₛ w ⟩) (g-inr q r ¬pr) b∈gr))

      go1 : Σ[ v ∈ S ] (⟨ v ∈ₛ sett Pair (g q) ⟩ × ⟨ b ∈ₛ v ⟩)
          → ∥ Σ[ p ∈ Pair ] (col p ≡ b) ∥₁
      go1 (v , (v∈ₛsett , b∈ₛv)) = PT.rec squash₁ (go2 v b∈ₛv)
        (∈∈ₛ {a = v} {b = sett Pair (g q)} .snd v∈ₛsett)

      viaUnion : ⟨ b ∈ˢ U ⟩ → ∥ Σ[ p ∈ Pair ] (col p ≡ b) ∥₁
      viaUnion b∈ = PT.rec squash₁ go1
        (union-ax (sett Pair (g q)) b .fst
          (∈∈ₛ {a = b} {b = U} .fst b∈))

  col-surj : (b : S) → ⟨ b ∈ˢ τ ⟩ → ∥ Σ[ p ∈ Pair ] (col p ≡ b) ∥₁
  col-surj b b∈τ = PT.rec squash₁ go1
    (union-ax (sett Pair (λ q → sucV (col q))) b .fst
      (∈∈ₛ {a = b} {b = τ} .fst b∈τ))
    where
    go2 : (v : S) → ⟨ b ∈ₛ v ⟩ → Σ[ q ∈ Pair ] (sucV (col q) ≡ v)
        → ∥ Σ[ p ∈ Pair ] (col p ≡ b) ∥₁
    go2 v b∈ₛv (q , sq≡v) = ∈sucV-elim {A = col q} {x = b} squash₁ b∈sq
      (λ b∈q → col-img q b b∈q)
      (λ b≡q → ∣ q , sym b≡q ∣₁)
      where
      b∈sq : ⟨ b ∈ˢ sucV (col q) ⟩
      b∈sq = ∈∈ₛ {a = b} {b = sucV (col q)} .snd
        (subst (λ w → ⟨ b ∈ₛ w ⟩) (sym sq≡v) b∈ₛv)

    go1 : Σ[ v ∈ S ] (⟨ v ∈ₛ sett Pair (λ q → sucV (col q)) ⟩ × ⟨ b ∈ₛ v ⟩)
        → ∥ Σ[ p ∈ Pair ] (col p ≡ b) ∥₁
    go1 (v , (v∈ₛsett , b∈ₛv)) = PT.rec squash₁ (go2 v b∈ₛv)
      (∈∈ₛ {a = v} {b = sett Pair (λ q → sucV (col q))} .snd v∈ₛsett)

  col→τ-surj : (m : ⟪ τ ⟫) → ∥ Σ[ p ∈ Pair ] (col→τ p ≡ m) ∥₁
  col→τ-surj m = PT.map hit (col-surj (⟪ τ ⟫↪ m) (member τ m))
    where
    hit : Σ[ p ∈ Pair ] (col p ≡ ⟪ τ ⟫↪ m) → Σ[ p ∈ Pair ] (col→τ p ≡ m)
    hit (p , e) = p , ↪-inj {a = τ} (col→τ-fiber p ∙ e)
  module Pairing (bound : ⟪ τ ⟫ → ⟪ α ⟫)
                 (bound-inj : {m n : ⟪ τ ⟫} → bound m ≡ bound n → m ≡ n) where

    pair : ⟪ α ⟫ → ⟪ α ⟫ → ⟪ α ⟫
    pair a b = bound (col→τ (a , b))

    pair-inj : {a b c d : ⟪ α ⟫} → pair a b ≡ pair c d → (a ≡ c) × (b ≡ d)
    pair-inj {a} {b} {c} {d} e =
      (cong fst (col→τ-inj (bound-inj e)))
      , (cong snd (col→τ-inj (bound-inj e)))

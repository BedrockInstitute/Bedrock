# The ambient square law at the initial ordinals (retired 2026-09-06)

This chapter proved Devlin's cardinal arithmetic 1.1(vii) in the
injection shape: at every initial ordinal, the square of the index
injects into the index.  The route is the via-collapse construction
measured by [LJ-1.47]: the product of an ordinal's index is
well-ordered through the ordinal's own membership and regularity on V,
the collapse `col` lands inside the ordinal (the exclusion chase
refutes the two escape cases), and the pairing is the direct injection
`p ↦ fiber α (col∈α p) .fst`, injective by `col-inj`.  The order type
of the archived route is never formed.

The law is `Init`-restricted.  An ordinal is initial here when it
contains `ω` strictly, is closed under successors, and its index
injects into no infinite member's square.  The restriction is the
extraction wall recorded in the earlier archived chapter: the honest
equivalence at a non-initial ordinal needs the least-of transfer, which
this chapter does not build.

THE TREE HAD NO CONSUMER FOR ANY OF IT.  `sq`, `Init`, `Initial`,
`InitialCore`, `AbstractH₀`, `godSWO`, `≺-dec` and the whole collapse
(`col`, `col-ord`, `col-mono`, `col-inj`, `col-img`) were reached from
nothing outside this file: the only `open ... using` list that named
them, `src/L/InjChain.lagda.md`, never applied one.  The material is
KEPT HERE AS MATHEMATICS, not as a module: this file is outside the
library path and DOES NOT TYPECHECK on its own.  What it needs from
the live chapter is `connex`, the product relation `_≺×_`, `ordSWO`,
`maxOrd`, `max-spec`, `_≺_` with `tri≺`/`irr≺`/`trans≺`/`wf≺`, and
`FiniteBase`, all still in `src/L/Ordinal/SquareLaw.lagda.md`.

## The strict-well-order product, in the full `SWO` shape

The live chapter keeps only well-foundedness of the product.  The
trichotomy, irreflexivity and transitivity below had `godSWO` as their
only consumer.

```agda
module _ {ℓx ℓy : Level} {X : Type ℓx} {Y : Type ℓy} (u : SWO X) (v : SWO Y) where

  private
    module U = SWO u
    module V = SWO v

    _≺×_ : X × Y → X × Y → Type (ℓ-suc ℓ)
    (a , x) ≺× (b , y) =
      (a U.<∙ b) ⊎ (((a U.<∙ b) → Empty.⊥) × ((b U.<∙ a) → Empty.⊥) × (x V.<∙ y))

    stall : {a b : X} → a ≡ b → ((a U.<∙ b) → Empty.⊥) × ((b U.<∙ a) → Empty.⊥)
    stall {a} {b} p =
        (λ h → U.irr∙ b (subst (λ z → z U.<∙ b) p h))
      , (λ h → U.irr∙ b (subst (λ z → b U.<∙ z) p h))

    tri× : (s t : X × Y) → Tri (s ≺× t) (s ≡ t) (t ≺× s)
    tri× (a , x) (b , y) with U.tri∙ a b
    ... | lt h = lt (inl h)
    ... | gt h = gt (inl h)
    ... | eq p with V.tri∙ x y
    ... | lt h = lt (inr (fst (stall p) , snd (stall p) , h))
    ... | eq q = eq (cong₂ _,_ p q)
    ... | gt h = gt (inr (fst (stall (sym p)) , snd (stall (sym p)) , h))

    irr× : (s : X × Y) → (s ≺× s → Empty.⊥)
    irr× (a , x) (inl h) = U.irr∙ a h
    irr× (a , x) (inr (_ , _ , h)) = V.irr∙ x h

    trans× : (s t r : X × Y) → s ≺× t → t ≺× r → s ≺× r
    trans× (a , x) (b , y) (c , z) (inl h) (inl h') =
      inl (U.trans∙ a b c h h')
    trans× (a , x) (b , y) (c , z) (inl h) (inr (¬bc , ¬cb , _)) =
      inl (subst (λ z' → a U.<∙ z') (connex u b c ¬bc ¬cb) h)
    trans× (a , x) (b , y) (c , z) (inr (¬ab , ¬ba , _)) (inl h') =
      inl (subst (λ z' → z' U.<∙ c) (sym (connex u a b ¬ab ¬ba)) h')
    trans× (a , x) (b , y) (c , z) (inr (¬ab , ¬ba , h)) (inr (¬bc , ¬cb , h')) =
      inr ( (λ k → ¬bc (subst (λ z' → z' U.<∙ c) (connex u a b ¬ab ¬ba) k))
          , (λ k → ¬cb (subst (λ z' → c U.<∙ z') (connex u a b ¬ab ¬ba) k))
          , V.trans∙ x y z h h' )

    accProd : (a : X) → Acc U._<∙_ a → (x : Y) → Acc V._<∙_ x → Acc _≺×_ (a , x)
    accProd a (acc ru) = inner
      where
      inner : (x : Y) → Acc V._<∙_ x → Acc _≺×_ (a , x)
      inner x (acc rv) = acc λ where
        (b , y) (inl h) → accProd b (ru b h) y (V.wf∙ y)
        (b , y) (inr (¬ba , ¬ab , h)) →
          subst (λ z → Acc _≺×_ (z , y)) (sym (connex u b a ¬ba ¬ab))
            (inner y (rv y h))

  prodSWO : SWO (X × Y)
  prodSWO = record
    { _<∙_   = _≺×_
    ; tri∙   = tri×
    ; irr∙   = irr×
    ; trans∙ = trans×
    ; wf∙    = λ where (a , x) → accProd a (U.wf∙ a) x (V.wf∙ x) }
```

## The Godel pair order as an `SWO`, and its decision procedure

```agda
module _ (α : S) (oα : IsOrd α) where

  lex2 : SWO (⟪ α ⟫ × ⟪ α ⟫)
  lex2 = prodSWO ordSWO ordSWO

  lex3 : SWO (⟪ α ⟫ × (⟪ α ⟫ × ⟪ α ⟫))
  lex3 = prodSWO ordSWO lex2

  module L3 = SWO lex3

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

```

## The abstract injection at the successor of the maximum

```agda
module AbstractH₀ (A : Type ℓ)
                  (↪A : A → S)
                  (↪A-inj : {m n : A} → ↪A m ≡ ↪A n → m ≡ n)
                  (prec : A × A → A × A → Type (ℓ-suc ℓ))
                  (γp : A × A → S)
                  (F : S → Type ℓ)
                  (↪F : (a : S) → F a → S)
                  (fiberF : (a : S) {x : S} → ⟨ x ∈ˢ a ⟩ → Σ[ m ∈ F a ] (↪F a m ≡ x))
                  (fst∈sucmaxF : {p q : A × A} → prec p q → ⟨ ↪A (fst p) ∈ˢ sucV (γp q) ⟩)
                  (snd∈sucmaxF : {p q : A × A} → prec p q → ⟨ ↪A (snd p) ∈ˢ sucV (γp q) ⟩) where

  h₀ : (p : A × A) → (r : A × A) → prec r p → F (sucV (γp p)) × F (sucV (γp p))
  h₀ p r pr = (fiberF (sucV (γp p)) (fst∈sucmaxF {r} {p} pr) .fst
             , fiberF (sucV (γp p)) (snd∈sucmaxF {r} {p} pr) .fst)

  h₀-inj : (p : A × A) {r r' : A × A} (pr : prec r p) (pr' : prec r' p)
         → h₀ p r pr ≡ h₀ p r' pr' → r ≡ r'
  h₀-inj p {a , b} {a' , b'} pr pr' e = cong₂ _,_ ea eb
    where
    β : S
    β = sucV (γp p)
    ea : a ≡ a'
    ea = ↪A-inj (sym (fiberF β (fst∈sucmaxF {a , b} {p} pr) .snd)
      ∙ cong (↪F β) (cong fst e)
      ∙ fiberF β (fst∈sucmaxF {a' , b'} {p} pr') .snd)
    eb : b ≡ b'
    eb = ↪A-inj (sym (fiberF β (snd∈sucmaxF {a , b} {p} pr) .snd)
      ∙ cong (↪F β) (cong snd e)
      ∙ fiberF β (snd∈sucmaxF {a' , b'} {p} pr') .snd)
```

## The finite exclusion at an ordinal above omega

These lived inside `FiniteBase`, whose surviving part is in the live
chapter.  `InitialCore` and `Initial` were their only consumers.

```agda
module FiniteBase where

  module _ (α : S) (oα : IsOrd α) (ω∈α : ⟨ ω ∈ˢ α ⟩) where

    numeral-in-α : (m : ℕ) → ⟨ (# m) ∈ˢ α ⟩
    numeral-in-α m = oα .fst (#∈ω m) ω∈α

    numeral-into-α : (m : ℕ) → ⟪ # m ⟫ → ⟪ α ⟫
    numeral-into-α m i = fiber α (oα .fst (member (# m) i) (numeral-in-α m)) .fst

    numeral-into-α-inj : (m : ℕ) (i₁ i₂ : ⟪ # m ⟫)
                       → numeral-into-α m i₁ ≡ numeral-into-α m i₂ → i₁ ≡ i₂
    numeral-into-α-inj m i₁ i₂ e = ↪-inj {a = # m}
      (sym (fiber α (oα .fst (member (# m) i₁) (numeral-in-α m)) .snd)
       ∙ cong (⟪ α ⟫↪) e
       ∙ fiber α (oα .fst (member (# m) i₂) (numeral-in-α m)) .snd)

    no-inj-finite : (n : ℕ) → (f : ⟪ α ⟫ → ⟪ # n ⟫ × ⟪ # n ⟫)
                  → ((x y : ⟪ α ⟫) → f x ≡ f y → x ≡ y) → Empty.⊥
    no-inj-finite n f finj =
      AbstractChase.NoInj.no-inj
        (λ n → ⟪ # n ⟫)
        toFin toFin-inj
        fromFin fromFin-inj
        (⟪ α ⟫)
        (numeral-into-α)
        (numeral-into-α-inj)
        n f finj

  finite-excl : (α : S) (oα : IsOrd α) (ω∈α : ⟨ ω ∈ˢ α ⟩)
              → (β : S) → IsOrd β → ⟨ β ∈ˢ ω ⟩
              → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
              → ((x y : ⟪ α ⟫) → f x ≡ f y → x ≡ y) → Empty.⊥
  finite-excl α oα ω∈α β oβ β∈ω f finj =
    PT.rec Empty.isProp⊥ go (ω-mem→numeral β β∈ω)
    where
    go : Σ[ n ∈ ℕ ] (β ≡ # n) → Empty.⊥
    go (n , p) = no-inj-finite α oα ω∈α n f' finj'
      where
      e : ⟪ β ⟫ × ⟪ β ⟫ ≃ ⟪ # n ⟫ × ⟪ # n ⟫
      e = pathToEquiv (cong (λ w → ⟪ w ⟫ × ⟪ w ⟫) p)
      f' : ⟪ α ⟫ → ⟪ # n ⟫ × ⟪ # n ⟫
      f' x = equivFun e (f x)
      finj' : (x y : ⟪ α ⟫) → f' x ≡ f' y → x ≡ y
      finj' x y e' = finj x y
        (sym (retEq e (f x)) ∙ cong (invEq e) e' ∙ retEq e (f y))
```

## The square law, the `Init` restriction and the core

```agda
sq : S → Type ℓ
sq α = Σ[ f ∈ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫) ]
         ((x y : ⟪ α ⟫ × ⟪ α ⟫) → f x ≡ f y → x ≡ y)

Init : S → Type (ℓ-suc ℓ)
Init α = IsOrd α
       × ⟨ ω ∈ˢ α ⟩
       × ((γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩)
       × ((β : S) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
          → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
          → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥)

module InitialCore (α : S) (oα : IsOrd α)
  (α-limit : (γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩)
  (noinj² : (β : S) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
          → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
          → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥)
  (finite-excl : (β : S) → IsOrd β → ⟨ β ∈ˢ ω ⟩
               → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
               → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥) where

  PairA : Type ℓ
  PairA = Pair α oα

  colA : PairA → S
  colA = col α oα

  _≺'_ : PairA → PairA → Type (ℓ-suc ℓ)
  _≺'_ = _≺_ α oα

  prec1 : ⟪ α ⟫ → ⟪ α ⟫ → Type (ℓ-suc ℓ)
  prec1 = _≺₁_ α oα

  leq : ⟪ α ⟫ → ⟪ α ⟫ → Type (ℓ-suc ℓ)
  leq = _≤₁_ α oα

  max' : ⟪ α ⟫ → ⟪ α ⟫ → ⟪ α ⟫
  max' = maxOrd α oα

  trans1 : (m n k : ⟪ α ⟫) → prec1 m n → prec1 n k → prec1 m k
  trans1 = trans₁ α oα

  tri' : (p q : PairA) → Tri (p ≺' q) (p ≡ q) (q ≺' p)
  tri' = tri≺ α oα

  cm : {p q : PairA} → p ≺' q → ⟨ colA p ∈ˢ colA q ⟩
  cm = col-mono α oα

  cimg : (q : PairA) (b : S) → ⟨ b ∈ˢ colA q ⟩
       → ∥ Σ[ r ∈ PairA ] (colA r ≡ b) ∥₁
  cimg = col-img α oα

  colo : (p : PairA) → IsOrd (colA p)
  colo = col-ord α oα

  cc : (p : PairA) → colA p ≡ colStep α oα p (λ r _ → colA r)
  cc = col-compute α oα

  wf : WellFounded _≺'_
  wf = wf≺ α oα

  god : SWO PairA
  god = godSWO α oα

  ≺dec : (p q : PairA) → (p ≺' q) ⊎ ((p ≺' q) → Empty.⊥)
  ≺dec = ≺-dec α oα

  ≤₁→≺₁ : (m n k : ⟪ α ⟫) → leq m n → prec1 n k → prec1 m k
  ≤₁→≺₁ m n k (inl h) h' = trans1 m n k h h'
  ≤₁→≺₁ m n k (inr e) h' = subst (λ w → prec1 w k) (sym e) h'

  ≤₁-subst : (m n n' : ⟪ α ⟫) → leq m n → n ≡ n' → leq m n'
  ≤₁-subst m n n' (inl h) e = inl (subst (λ w → prec1 m w) e h)
  ≤₁-subst m n n' (inr q) e = inr (q ∙ e)

  ≤₁-into-suc : (m n : ⟪ α ⟫) → leq m n → ⟨ ⟪ α ⟫↪ m ∈ˢ sucV (⟪ α ⟫↪ n) ⟩
  ≤₁-into-suc m n (inl h) = ∈sucV-inl h
  ≤₁-into-suc m n (inr e) =
    subst (λ w → ⟨ ⟪ α ⟫↪ w ∈ˢ sucV (⟪ α ⟫↪ n) ⟩) (sym e) (self∈sucV (⟪ α ⟫↪ n))

  fst∈sucmax : {p q : PairA} → p ≺' q
             → ⟨ ⟪ α ⟫↪ (fst p) ∈ˢ sucV (⟪ α ⟫↪ (max' (fst q) (snd q))) ⟩
  fst∈sucmax {a , b} {c , d} (inl h) =
    ∈sucV-inl (≤₁→≺₁ a (max' a b) (max' c d) (max-spec α oα a b .fst) h)
  fst∈sucmax {a , b} {c , d} (inr (e , _)) =
    ≤₁-into-suc a (max' c d)
      (≤₁-subst a (max' a b) (max' c d) (max-spec α oα a b .fst) e)

  snd∈sucmax : {p q : PairA} → p ≺' q
             → ⟨ ⟪ α ⟫↪ (snd p) ∈ˢ sucV (⟪ α ⟫↪ (max' (fst q) (snd q))) ⟩
  snd∈sucmax {a , b} {c , d} (inl h) =
    ∈sucV-inl (≤₁→≺₁ b (max' a b) (max' c d) (max-spec α oα a b .snd) h)
  snd∈sucmax {a , b} {c , d} (inr (e , _)) =
    ≤₁-into-suc b (max' c d)
      (≤₁-subst b (max' a b) (max' c d) (max-spec α oα a b .snd) e)

  Pb : (b : S) → PairA → hProp (ℓ-suc ℓ)
  Pb b r = (colA r ≡ b) , isSetS (colA r) b

  colr≺ : {p : PairA} (b : S) → ⟨ b ∈ˢ colA p ⟩ → (r : PairA)
        → colA r ≡ b → r ≺' p
  colr≺ {p} b b∈ r e = go (tri' r p)
    where
    go : Tri (r ≺' p) (r ≡ p) (p ≺' r) → r ≺' p
    go (lt h) = h
    go (eq q) = Empty.rec
      (∈-irrefl (colA p)
        (subst (λ w → ⟨ w ∈ˢ colA p ⟩) (sym (cong colA (sym q) ∙ e)) b∈))
    go (gt h) = Empty.rec
      (∈-irrefl (colA p)
        (colo p .fst (cm h) (subst (λ w → ⟨ w ∈ˢ colA p ⟩) (sym e) b∈)))

  module WF = WFI wf

  opaque
    descent : (p : PairA) (b : S) → ⟨ b ∈ˢ colA p ⟩
            → Σ[ r ∈ PairA ] ((r ≺' p) × (colA r ≡ b))
    descent p b b∈ = fst s , (colr≺ b b∈ (fst s) (fst (snd s)) , fst (snd s))
      where
      s : Σ[ m ∈ PairA ] IsLeast god (Pb b) m
      s = leastOf god lem (Pb b) (cimg p b b∈)

    g : (p : PairA) (b : S) → ⟨ b ∈ˢ colA p ⟩ → PairA
    g p b b∈ = fst (descent p b b∈)

    g-inj : (p : PairA) {b b' : S} (hb : ⟨ b ∈ˢ colA p ⟩) (hb' : ⟨ b' ∈ˢ colA p ⟩)
          → g p b hb ≡ g p b' hb' → b ≡ b'
    g-inj p {b} {b'} hb hb' e =
      sym (snd (descent p b hb) .snd) ∙ cong colA e ∙ snd (descent p b' hb') .snd

    γp : PairA → S
    γp p = ⟪ α ⟫↪ (max' (fst p) (snd p))

    h₀ : (p : PairA) → (r : PairA) → r ≺' p → ⟪ sucV (γp p) ⟫ × ⟪ sucV (γp p) ⟫
    h₀ = AbstractH₀.h₀ (⟪ α ⟫) (⟪ α ⟫↪) (↪-inj {a = α}) _≺'_ γp (⟪_⟫) (⟪_⟫↪) fiber fst∈sucmax snd∈sucmax

    h₀-inj : (p : PairA) {r r' : PairA} (pr : r ≺' p) (pr' : r' ≺' p)
           → h₀ p r pr ≡ h₀ p r' pr' → r ≡ r'
    h₀-inj = AbstractH₀.h₀-inj (⟪ α ⟫) (⟪ α ⟫↪) (↪-inj {a = α}) _≺'_ γp (⟪_⟫) (⟪_⟫↪) fiber fst∈sucmax snd∈sucmax

    comp₀ : (p : PairA) (e : colA p ≡ α) → ⟪ α ⟫ → ⟪ sucV (γp p) ⟫ × ⟪ sucV (γp p) ⟫
    comp₀ p e m = h₀ p (g p (⟪ α ⟫↪ m) (b∈ m))
                      (snd (descent p (⟪ α ⟫↪ m) (b∈ m)) .fst)
      where
      b∈ : (m : ⟪ α ⟫) → ⟨ ⟪ α ⟫↪ m ∈ˢ colA p ⟩
      b∈ m = subst (λ w → ⟨ ⟪ α ⟫↪ m ∈ˢ w ⟩) (sym e)
        (∈∈ₛ {a = ⟪ α ⟫↪ m} {b = α} .snd (∈ₛ⟪ α ⟫↪ m))

    comp₀-inj : (p : PairA) (e : colA p ≡ α) (m n : ⟪ α ⟫)
              → comp₀ p e m ≡ comp₀ p e n → m ≡ n
    comp₀-inj p e m n e' = ↪-inj {a = α}
      (g-inj p (b∈ m) (b∈ n)
        (h₀-inj p (snd (descent p (⟪ α ⟫↪ m) (b∈ m)) .fst)
                  (snd (descent p (⟪ α ⟫↪ n) (b∈ n)) .fst) e'))
      where
      b∈ : (m : ⟪ α ⟫) → ⟨ ⟪ α ⟫↪ m ∈ˢ colA p ⟩
      b∈ m = subst (λ w → ⟨ ⟪ α ⟫↪ m ∈ˢ w ⟩) (sym e)
        (∈∈ₛ {a = ⟪ α ⟫↪ m} {b = α} .snd (∈ₛ⟪ α ⟫↪ m))

    β≠ω : (p : PairA) → sucV (γp p) ≡ ω → Empty.⊥
    β≠ω p e = PT.rec Empty.isProp⊥ go (ω-mem→numeral (γp p) γp∈ω)
      where
      γp∈ω : ⟨ γp p ∈ˢ ω ⟩
      γp∈ω = subst (λ w → ⟨ γp p ∈ˢ w ⟩) e (self∈sucV (γp p))
      go : Σ[ n ∈ ℕ ] (γp p ≡ # n) → Empty.⊥
      go (n , q) = ∈-irrefl ω
        (subst (λ w → ⟨ w ∈ˢ ω ⟩) (sym (cong sucV q) ∙ e) (#∈ω (suc n)))

    exclude : (p : PairA) → colA p ≡ α → Empty.⊥
    exclude p e = go (ord-tri β ordβ ω ω-ord)
      where
      γp∈α : ⟨ γp p ∈ˢ α ⟩
      γp∈α = ∈∈ₛ {a = γp p} {b = α} .snd (∈ₛ⟪ α ⟫↪ (max' (fst p) (snd p)))
      β : S
      β = sucV (γp p)
      ordβ : IsOrd β
      ordβ = suc-ord (mem-ord {A = α} oα (γp p) γp∈α)
      β∈α : ⟨ β ∈ˢ α ⟩
      β∈α = α-limit (γp p) γp∈α
      go : (⟨ β ∈ˢ ω ⟩ ⊎ ((β ≡ ω) ⊎ ⟨ ω ∈ˢ β ⟩)) → Empty.⊥
      go (inl β∈ω) = finite-excl β ordβ β∈ω (comp₀ p e) (comp₀-inj p e)
      go (inr (inl β≡ω)) = β≠ω p β≡ω
      go (inr (inr ω∈β)) = noinj² β ordβ β∈α ω∈β (comp₀ p e) (comp₀-inj p e)

    gₚ : (p : PairA) → PairA → S
    gₚ p r = colPick α oα p (λ r _ → colA r) r (≺dec r p)

    gₚ-inl : (p r : PairA) → (rp : r ≺' p) → gₚ p r ≡ sucV (colA r)
    gₚ-inl p r rp = go (≺dec r p)
      where
      go : (d : (r ≺' p) ⊎ ((r ≺' p) → Empty.⊥))
         → colPick α oα p (λ r _ → colA r) r d ≡ sucV (colA r)
      go (inl _) = refl
      go (inr ¬rp) = Empty.rec (¬rp rp)

    gₚ-inr : (p r : PairA) → ((r ≺' p) → Empty.⊥) → gₚ p r ≡ ∅
    gₚ-inr p r ¬rp = go (≺dec r p)
      where
      go : (d : (r ≺' p) ⊎ ((r ≺' p) → Empty.⊥))
         → colPick α oα p (λ r _ → colA r) r d ≡ ∅
      go (inl rp) = Empty.rec (¬rp rp)
      go (inr _) = refl

    colp⊆α : (p : PairA) → ((r : PairA) → r ≺' p → ⟨ colA r ∈ˢ α ⟩)
           → (x : S) → ⟨ x ∈ˢ colA p ⟩ → ⟨ x ∈ˢ α ⟩
    colp⊆α p rec x x∈ = PT.rec (snd (x ∈ˢ α)) viaUnion
      (union-ax (sett PairA (gₚ p)) x .fst
        (∈∈ₛ {a = x} {b = ⋃ (sett PairA (gₚ p))} .fst
          (subst (λ w → ⟨ x ∈ˢ w ⟩) (cc p) x∈)))
      where
      viaUnion : Σ[ v ∈ S ] (⟨ v ∈ₛ sett PairA (gₚ p) ⟩ × ⟨ x ∈ₛ v ⟩) → ⟨ x ∈ˢ α ⟩
      viaUnion (v , (v∈ₛsett , x∈ₛv)) = PT.rec (snd (x ∈ˢ α)) viaFiber
        (∈∈ₛ {a = v} {b = sett PairA (gₚ p)} .snd v∈ₛsett)
        where
        viaFiber : Σ[ r ∈ PairA ] (gₚ p r ≡ v) → ⟨ x ∈ˢ α ⟩
        viaFiber (r , gr≡v) = decide (≺dec r p)
          where
          x∈gr : ⟨ x ∈ₛ gₚ p r ⟩
          x∈gr = subst (λ w → ⟨ x ∈ₛ w ⟩) (sym gr≡v) x∈ₛv
          decide : (r ≺' p) ⊎ ((r ≺' p) → Empty.⊥) → ⟨ x ∈ˢ α ⟩
          decide (inl rp) = ∈sucV-elim {A = colA r} {x = x} (snd (x ∈ˢ α))
            (∈∈ₛ {a = x} {b = sucV (colA r)} .snd
              (subst (λ w → ⟨ x ∈ₛ w ⟩) (gₚ-inl p r rp) x∈gr))
            (λ x∈r → oα .fst x∈r (rec r rp))
            (λ x≡r → subst (λ w → ⟨ w ∈ˢ α ⟩) (sym x≡r) (rec r rp))
          decide (inr ¬rp) = Empty.rec
            (∅-empty x (subst (λ w → ⟨ x ∈ₛ w ⟩) (gₚ-inr p r ¬rp) x∈gr))

    col≤α : (p : PairA) → ((r : PairA) → r ≺' p → ⟨ colA r ∈ˢ α ⟩)
          → ⟨ colA p ∈ˢ α ⟩
    col≤α p rec = go (ord-tri (colA p) (colo p) α oα)
      where
      go : (⟨ colA p ∈ˢ α ⟩ ⊎ ((colA p ≡ α) ⊎ ⟨ α ∈ˢ colA p ⟩)) → ⟨ colA p ∈ˢ α ⟩
      go (inl h) = h
      go (inr (inl e)) = Empty.rec (exclude p e)
      go (inr (inr h)) = Empty.rec (∈-irrefl α (colp⊆α p rec α h))

    col∈α : (p : PairA) → ⟨ colA p ∈ˢ α ⟩
    col∈α = WF.induction {P = λ p → ⟨ colA p ∈ˢ α ⟩} step
      where
      step : (p : PairA) → ((r : PairA) → r ≺' p → ⟨ colA r ∈ˢ α ⟩)
           → ⟨ colA p ∈ˢ α ⟩
      step p rec = col≤α p (λ r rp → rec r rp)

module Initial (α : S) (iα : Init α) where
  module IC = InitialCore α (iα .fst) (iα .snd .snd .fst) (iα .snd .snd .snd)
                 (FiniteBase.finite-excl α (iα .fst) (iα .snd .fst))

  open IC

  pair : ⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫
  pair p = fiber α {x = colA p} (col∈α p) .fst

  pair-inj : (p q : ⟪ α ⟫ × ⟪ α ⟫) → pair p ≡ pair q → p ≡ q
  pair-inj p q e = col-inj α (iα .fst) {p = p} {q = q}
    (sym (fiber α {x = colA p} (col∈α p) .snd)
     ∙ cong (⟪ α ⟫↪) e
     ∙ fiber α {x = colA q} (col∈α q) .snd)

  square : sq α
  square = pair , pair-inj

  truncated : ∥ sq α ∥₁
  truncated = ∣ square ∣₁
```

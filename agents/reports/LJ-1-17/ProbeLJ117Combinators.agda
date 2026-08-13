{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module ProbeLJ117Combinators {ℓₚ : Level} where

open import L.WellOrder.Base {ℓₚ}
  using ( SWO; Tri; lt; eq; gt; module SWO )
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded; module WFI )
import Cubical.Data.Empty as Empty
open import Cubical.Relation.Nullary using ( ¬_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( Unit*; tt* )
open import Cubical.Data.List using ( List; []; _∷_; length )
open import Cubical.Data.Nat using ( znots; snotz; injSuc; +-suc )
open import Cubical.Data.Nat.Order
  using ( _<_; _≤_; ≤-refl; ≤-trans; suc-≤-suc; pred-≤-pred; ¬-<-zero
        ; ≤-suc; isProp≤; zero-≤; <-trans; ¬m<m; <-wellfounded; Trichotomy; _≟_ )
open Trichotomy
connex : {ℓc : Level} {A : Type ℓc} (w : SWO A) (a b : A)
       → ¬ SWO._<∙_ w a b → ¬ SWO._<∙_ w b a → a ≡ b
connex w a b ¬ab ¬ba with SWO.tri∙ w a b
... | lt h = Empty.rec (¬ab h)
... | eq p = p
... | gt h = Empty.rec (¬ba h)
unitSWO : {ℓc : Level} → SWO (Unit* {ℓc})
unitSWO = record
  { _<∙_   = λ _ _ → ⊥* {ℓₚ}
  ; tri∙   = λ a b → eq refl
  ; irr∙   = λ a h → Empty.rec* h
  ; trans∙ = λ a b c h _ → Empty.rec* h
  ; wf∙    = λ a → acc (λ b h → Empty.rec* h) }
module _ {ℓx ℓy : Level} {X : Type ℓx} {Y : Type ℓy} (u : SWO X) (v : SWO Y) where
  private
    module U = SWO u
    module V = SWO v

    _≺⊎_ : X ⊎ Y → X ⊎ Y → Type ℓₚ
    inl a ≺⊎ inl b = a U.<∙ b
    inl a ≺⊎ inr b = Unit* {ℓₚ}
    inr a ≺⊎ inl b = ⊥* {ℓₚ}
    inr a ≺⊎ inr b = a V.<∙ b

    tri⊎ : (s t : X ⊎ Y) → Tri (s ≺⊎ t) (s ≡ t) (t ≺⊎ s)
    tri⊎ (inl a) (inl b) with U.tri∙ a b
    ... | lt h = lt h
    ... | eq p = eq (cong inl p)
    ... | gt h = gt h
    tri⊎ (inl a) (inr b) = lt tt*
    tri⊎ (inr a) (inl b) = gt tt*
    tri⊎ (inr a) (inr b) with V.tri∙ a b
    ... | lt h = lt h
    ... | eq p = eq (cong inr p)
    ... | gt h = gt h

    irr⊎ : (s : X ⊎ Y) → ¬ s ≺⊎ s
    irr⊎ (inl a) h = U.irr∙ a h
    irr⊎ (inr a) h = V.irr∙ a h

    trans⊎ : (s t r : X ⊎ Y) → s ≺⊎ t → t ≺⊎ r → s ≺⊎ r
    trans⊎ (inl a) (inl b) (inl c) h h' = U.trans∙ a b c h h'
    trans⊎ (inl a) (inl b) (inr c) h h' = tt*
    trans⊎ (inl a) (inr b) (inl c) h h' = Empty.rec* h'
    trans⊎ (inl a) (inr b) (inr c) h h' = tt*
    trans⊎ (inr a) (inl b) r h h' = Empty.rec* h
    trans⊎ (inr a) (inr b) (inl c) h h' = Empty.rec* h'
    trans⊎ (inr a) (inr b) (inr c) h h' = V.trans∙ a b c h h'

    accInl : (a : X) → Acc U._<∙_ a → Acc _≺⊎_ (inl a)
    accInl a (acc r) = acc λ where
      (inl b) h → accInl b (r b h)
      (inr b) h → Empty.rec* h

    accInr : (b : Y) → Acc V._<∙_ b → Acc _≺⊎_ (inr b)
    accInr b (acc r) = acc λ where
      (inl a) h → accInl a (U.wf∙ a)
      (inr b') h → accInr b' (r b' h)

  sumSWO : SWO (X ⊎ Y)
  sumSWO = record
    { _<∙_   = _≺⊎_
    ; tri∙   = tri⊎
    ; irr∙   = irr⊎
    ; trans∙ = trans⊎
    ; wf∙    = λ where
        (inl a) → accInl a (U.wf∙ a)
        (inr b) → accInr b (V.wf∙ b) }
  private
    _≺×_ : X × Y → X × Y → Type ℓₚ
    (a , x) ≺× (b , y) =
      (a U.<∙ b) ⊎ ((¬ (a U.<∙ b)) × (¬ (b U.<∙ a)) × (x V.<∙ y))

    stall : {a b : X} → a ≡ b → (¬ (a U.<∙ b)) × (¬ (b U.<∙ a))
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

    irr× : (s : X × Y) → ¬ s ≺× s
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
module _ {ℓx : Level} {X : Type ℓx} (u : SWO X) where
  private
    module U = SWO u

    stall : {a b : X} → a ≡ b → (¬ (a U.<∙ b)) × (¬ (b U.<∙ a))
    stall {a} {b} p =
        (λ h → U.irr∙ b (subst (λ z → z U.<∙ b) p h))
      , (λ h → U.irr∙ b (subst (λ z → b U.<∙ z) p h))

    _≺ᵖ_ : List X → List X → Type ℓₚ
    [] ≺ᵖ _ = ⊥* {ℓₚ}
    (x ∷ xs) ≺ᵖ [] = ⊥* {ℓₚ}
    (x ∷ xs) ≺ᵖ (y ∷ ys) = (x U.<∙ y)
                          ⊎ ((¬ (x U.<∙ y)) × (¬ (y U.<∙ x)) × (xs ≺ᵖ ys))

    triP : (xs ys : List X) → length xs ≡ length ys
         → Tri (xs ≺ᵖ ys) (xs ≡ ys) (ys ≺ᵖ xs)
    triP [] [] _ = eq refl
    triP [] (y ∷ ys) q = Empty.rec (znots q)
    triP (x ∷ xs) [] q = Empty.rec (snotz q)
    triP (x ∷ xs) (y ∷ ys) q with U.tri∙ x y
    ... | lt h = lt (inl h)
    ... | gt h = gt (inl h)
    ... | eq e with triP xs ys (injSuc q)
    ...   | lt r = lt (inr (fst (stall e) , snd (stall e) , r))
    ...   | gt r = gt (inr (fst (stall (sym e)) , snd (stall (sym e)) , r))
    ...   | eq r = eq (cong₂ _∷_ e r)

    irrP : (xs : List X) → ¬ xs ≺ᵖ xs
    irrP [] p = Empty.rec* p
    irrP (x ∷ xs) (inl h) = U.irr∙ x h
    irrP (x ∷ xs) (inr (_ , _ , h)) = irrP xs h

    transP : (xs ys zs : List X) → xs ≺ᵖ ys → ys ≺ᵖ zs → xs ≺ᵖ zs
    transP [] ys zs p q = Empty.rec* p
    transP (x ∷ xs) [] zs p q = Empty.rec* p
    transP (x ∷ xs) (y ∷ ys) [] p q = Empty.rec* q
    transP (x ∷ xs) (y ∷ ys) (z ∷ zs) (inl p) (inl q) =
      inl (U.trans∙ x y z p q)
    transP (x ∷ xs) (y ∷ ys) (z ∷ zs) (inl p) (inr (¬yz , ¬zy , _)) =
      inl (subst (λ v → x U.<∙ v) (connex u y z ¬yz ¬zy) p)
    transP (x ∷ xs) (y ∷ ys) (z ∷ zs) (inr (¬xy , ¬yx , _)) (inl q) =
      inl (subst (λ v → v U.<∙ z) (sym (connex u x y ¬xy ¬yx)) q)
    transP (x ∷ xs) (y ∷ ys) (z ∷ zs) (inr (¬xy , ¬yx , p)) (inr (¬yz , ¬zy , q)) =
      inr ( (λ h → ¬yz (subst (λ v → v U.<∙ z) (connex u x y ¬xy ¬yx) h))
          , (λ h → ¬zy (subst (λ v → z U.<∙ v) (connex u x y ¬xy ¬yx) h))
          , transP xs ys zs p q )

    _≺ᴸ_ : List X → List X → Type ℓₚ
    xs ≺ᴸ ys = Lift {ℓ-zero} {ℓₚ} (length xs < length ys)
              ⊎ ((length xs ≡ length ys) × (xs ≺ᵖ ys))

    triL : (xs ys : List X) → Tri (xs ≺ᴸ ys) (xs ≡ ys) (ys ≺ᴸ xs)
    triL xs ys with length xs ≟ length ys
    ... | lt h = lt (inl (lift h))
    ... | gt h = gt (inl (lift h))
    ... | eq p with triP xs ys p
    ...   | lt r = lt (inr (p , r))
    ...   | eq r = eq r
    ...   | gt r = gt (inr (sym p , r))

    irrL : (xs : List X) → ¬ xs ≺ᴸ xs
    irrL xs (inl h) = ¬m<m (lower h)
    irrL xs (inr (_ , p)) = irrP xs p

    transL : (xs ys zs : List X) → xs ≺ᴸ ys → ys ≺ᴸ zs → xs ≺ᴸ zs
    transL xs ys zs (inl p) (inl q) = inl (lift (<-trans (lower p) (lower q)))
    transL xs ys zs (inl p) (inr (q , _)) =
      inl (lift (subst (λ k → length xs < k) q (lower p)))
    transL xs ys zs (inr (p , _)) (inl q) =
      inl (lift (subst (λ k → k < length zs) (sym p) (lower q)))
    transL xs ys zs (inr (p , r)) (inr (q , s)) =
      inr (p ∙ q , transP xs ys zs r s)

    <≤ : {m n : ℕ} → m < n → m ≤ n
    <≤ {zero} {n} h = zero-≤
    <≤ {suc m} {zero} h = Empty.rec (¬-<-zero h)
    <≤ {suc m} {suc n} h = suc-≤-suc (<≤ (pred-≤-pred h))

    module Class (n : ℕ) (below : (us : List X) → length us < n → Acc _≺ᴸ_ us) where

      BL : Type ℓx
      BL = Σ[ us ∈ List X ] (length us ≤ n)

      _≺ᵉ_ : BL → BL → Type ℓₚ
      p ≺ᵉ q = (length (p .fst) ≡ length (q .fst)) × (p .fst ≺ᵖ q .fst)

      tailB : (n : ℕ) (x : X) (xs : List X) → length (x ∷ xs) ≤ n → length xs ≤ n
      tailB zero    x xs (k , p) =
        Empty.rec (snotz (sym (+-suc k (length xs)) ∙ p))
      tailB (suc m) x xs (k , p) =
        ≤-suc (k , injSuc (sym (+-suc k (length xs)) ∙ p))

      accE : (k : ℕ) (p : BL) → length (p .fst) ≡ k → Acc _≺ᵉ_ p
      goE : (k : ℕ) (x : X) → Acc U._<∙_ x → (xs : List X) → length xs ≡ k
          → (b : length (x ∷ xs) ≤ n) → Acc _≺ᵉ_ (xs , tailB n x xs b)
          → Acc _≺ᵉ_ (x ∷ xs , b)

      accE zero ([] , b) q = acc λ where
        ([] , _) (le , p) → Empty.rec* p
        (y ∷ ys , _) (le , p) → Empty.rec* p
      accE zero (x ∷ xs , b) q = Empty.rec (snotz q)
      accE (suc k) ([] , b) q = acc λ where
        ([] , _) (le , p) → Empty.rec* p
        (y ∷ ys , _) (le , p) → Empty.rec* p
      accE (suc k) (x ∷ xs , b) q =
        goE k x (U.wf∙ x) xs (injSuc q) b
          (accE k (xs , tailB n x xs b) (injSuc q))

      goE k x (acc r) = inner
        where
        inner : (xs : List X) → length xs ≡ k
              → (b : length (x ∷ xs) ≤ n) → Acc _≺ᵉ_ (xs , tailB n x xs b)
              → Acc _≺ᵉ_ (x ∷ xs , b)
        inner xs lq b (acc rs) = acc (λ where
          ([] , _) (le , p) → Empty.rec* p
          (y ∷ ys , by) (le , inl x<y) →
            goE k y (r y x<y) ys (injSuc le ∙ lq) by
              (accE k (ys , tailB n y ys by) (injSuc le ∙ lq))
          (y ∷ ys , by) (le , inr (¬yx , ¬xy , tailp)) →
            let e = connex u x y ¬xy ¬yx
                by' = subst (λ z → length (z ∷ ys) ≤ n) e by
            in subst (λ q → Acc _≺ᵉ_ (y ∷ ys , q))
                 (isProp≤ by' by)
                 (subst (λ z → Acc _≺ᵉ_ (z ∷ ys , by')) e
                   (inner ys (injSuc le ∙ lq) by'
                     (rs (ys , tailB n x ys by')
                       (injSuc le , tailp)))))

      accL : (k : ℕ) (p : BL) → length (p .fst) < k → Acc _≺ᴸ_ (p .fst)
      accL zero p q = Empty.rec (¬-<-zero q)
      accL (suc k) p q = inner p (accE (length (p .fst)) p refl) q
        where
        inner : (p' : BL) → Acc _≺ᵉ_ p' → length (p' .fst) < suc k → Acc _≺ᴸ_ (p' .fst)
        inner p' (acc re) q' = acc step
          where
          step : (p'' : List X) → p'' ≺ᴸ p' .fst → Acc _≺ᴸ_ p''
          step p'' (inl len<) = below p'' (≤-trans (lower len<) (p' .snd))
          step p'' (inr (len≡ , edesc)) =
            inner (p'' , subst (λ m → m ≤ n) (sym len≡) (p' .snd))
              (re (p'' , subst (λ m → m ≤ n) (sym len≡) (p' .snd))
                 (len≡ , edesc))
              (subst (λ m → m < suc k) (sym len≡) q')

    accList : (n : ℕ) → (xs : List X) → length xs ≤ n → Acc _≺ᴸ_ xs
    accList = WFI.induction <-wellfounded outer
      where
      outer : (n : ℕ) → ((k : ℕ) → k < n → (xs : List X) → length xs ≤ k → Acc _≺ᴸ_ xs)
            → (xs : List X) → length xs ≤ n → Acc _≺ᴸ_ xs
      outer n ih xs b = C.accL (suc n) (xs , b) (suc-≤-suc b)
        where
        module C = Class n (λ us len< → ih (length us) len< us ≤-refl)

  listSWO : SWO (List X)
  listSWO = record
    { _<∙_   = _≺ᴸ_
    ; tri∙   = triL
    ; irr∙   = irrL
    ; trans∙ = transL
    ; wf∙    = λ xs → accList (length xs) xs ≤-refl }

-- Scratch addition: the archived L.WellOrder.Base's natSWO, absent from today's Base.
natSWO : SWO ℕ
natSWO = record
  { _<∙_   = _≺ᴺ_
  ; tri∙   = triᴺ
  ; irr∙   = λ m h → ¬m<m (lower h)
  ; trans∙ = λ m n k h h' → lift (<-trans (lower h) (lower h'))
  ; wf∙    = wfᴺ }
  where
  _≺ᴺ_ : ℕ → ℕ → Type ℓₚ
  m ≺ᴺ n = Lift {ℓ-zero} {ℓₚ} (m < n)

  triᴺ : (m n : ℕ) → Tri (m ≺ᴺ n) (m ≡ n) (n ≺ᴺ m)
  triᴺ m n with m ≟ n
  ... | lt h = lt (lift h)
  ... | eq p = eq p
  ... | gt h = gt (lift h)

  wfᴺ : WellFounded _≺ᴺ_
  wfᴺ n = go n (<-wellfounded n)
    where
    go : (m : ℕ) → Acc _<_ m → Acc _≺ᴺ_ m
    go m (acc r) = acc λ k h → go k (r k (lower h))

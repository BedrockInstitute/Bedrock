  private
    sh4 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc n))))
    sh4 i = suc (suc (suc (suc i)))
  
  StepBody : ∀ {n} → Fin n → Fin n → Formula S (suc (suc (suc (suc n))))
  StepBody b f = (var (suc (suc zero)) ∈̇ var (sh4 b))
               ∧̇ ( appAt (sh4 f) (suc (suc zero)) (suc zero)
                 ∧̇ ( DefAt zero (suc zero)
                   ∧̇ (var (suc (suc (suc zero))) ∈̇ var zero) ) )
  
  StepAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  StepAt v b f = extAt v (∃̇ (∃̇ (∃̇ (StepBody b f))))
  
  Records : ∀ {n} → Fin n → Fin n → S ^ n → S → S → Type (ℓ-suc ℓ)
  Records b f γ c w = ⟨ fst c ∈ fst (lookup b γ) ⟩
                    × ⟨ pr (fst c) (fst w) ∈ fst (lookup f γ) ⟩
  
  StepOf : ∀ {n} → Fin n → Fin n → S ^ n → S → Type (ℓ-suc ℓ)
  StepOf b f γ z = Σ[ c ∈ S ] Σ[ w ∈ S ]
                     (Records b f γ c w × ⟨ fst z ∈ 𝒟ₒ (fst w) ⟩)
  
  PowOK : ∀ {n} → Fin n → Fin n → S ^ n → Type (ℓ-suc ℓ)
  PowOK b f γ = (c w : S) → Records b f γ c w → ⟨ M (𝒟ₒ (fst w)) ⟩
  module _ {n : ℕ} (v b f : Fin n) (γ : S ^ n) where
    private
      Φ : Formula S (suc n)
      Φ = ∃̇ (∃̇ (∃̇ (StepBody b f)))
  
      readBody : PowOK b f γ → (z c w d : S)
               → ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ StepBody b f ⟩ → StepOf b f γ z
      readBody ok z c w d (hb , (ha , (hd , hz))) =
        c , w , rec , subst (λ X → ⟨ fst z ∈ X ⟩) qd hz
        where
        -- perf: env spelled out at both ends; via an abbreviation, 15 s per conversion
        rec : Records b f γ c w
        rec = hb , subst ⟨_⟩ (appAt-adequate
          (sh4 f) (suc (suc zero)) (suc zero) (d ∷ w ∷ c ∷ z ∷ γ)) ha
  
        qd : fst d ≡ 𝒟ₒ (fst w)
        qd = DefAt-out w zero (suc zero) (d ∷ w ∷ c ∷ z ∷ γ)
          (λ x x∈ → M-trans {x = 𝒟ₒ (fst w)} {y = x} x∈ (ok c w rec)) refl hd
  
      unfold : PowOK b f γ → (z : S)
             → ⟨ (z ∷ γ) ⊨ Φ ⟩ → ∥ StepOf b f γ z ∥₁
      unfold ok z = PT.rec squash₁ viaArg
        where
        viaPow : (c w : S)
               → Σ[ d ∈ S ] ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ StepBody b f ⟩
               → ∥ StepOf b f γ z ∥₁
        viaPow c w (d , hd) = ∣ readBody ok z c w d hd ∣₁
  
        viaVal : (c : S)
               → Σ[ w ∈ S ] ⟨ (w ∷ c ∷ z ∷ γ) ⊨ ∃̇ (StepBody b f) ⟩
               → ∥ StepOf b f γ z ∥₁
        viaVal c (w , hw) = PT.rec squash₁ (viaPow c w) hw
  
        viaArg : Σ[ c ∈ S ] ⟨ (c ∷ z ∷ γ) ⊨ ∃̇ (∃̇ (StepBody b f)) ⟩
               → ∥ StepOf b f γ z ∥₁
        viaArg (c , hc) = PT.rec squash₁ (viaVal c) hc
  
      fill : PowOK b f γ → (z : S) → StepOf b f γ z → ⟨ (z ∷ γ) ⊨ Φ ⟩
      fill ok z (c , (w , (rec , hz))) =
        ∣ c , ∣ w , ∣ D , (rec .fst , (ha , (hdef , hz))) ∣₁ ∣₁ ∣₁
        where
        -- perf: env spelled out at both ends; via an abbreviation, 15 s per conversion
        D : S
        D = 𝒟ₒ (fst w) , ok c w rec
  
        ha : ⟨ (D ∷ w ∷ c ∷ z ∷ γ) ⊨ appAt (sh4 f) (suc (suc zero)) (suc zero) ⟩
        ha = subst ⟨_⟩ (sym (appAt-adequate
          (sh4 f) (suc (suc zero)) (suc zero) (D ∷ w ∷ c ∷ z ∷ γ))) (rec .snd)
  
        hdef : ⟨ (D ∷ w ∷ c ∷ z ∷ γ) ⊨ DefAt zero (suc zero) ⟩
        hdef = DefAt-in w zero (suc zero) (D ∷ w ∷ c ∷ z ∷ γ) refl refl
  
    StepAt-out : ⟨ γ ⊨ StepAt v b f ⟩ → PowOK b f γ
               → (z : S) → ⟨ fst z ∈ fst (lookup v γ) ⟩ → ∥ StepOf b f γ z ∥₁
    StepAt-out h ok z z∈ = unfold ok z (extAt-out v Φ γ h z z∈)
  
    StepAt-back : ⟨ γ ⊨ StepAt v b f ⟩ → PowOK b f γ
                → (z : S) → StepOf b f γ z → ⟨ fst z ∈ fst (lookup v γ) ⟩
    StepAt-back h ok z s = extAt-in v Φ γ h z (fill ok z s)
  
    StepAt-in : PowOK b f γ
              → ((z : S) → ⟨ fst z ∈ fst (lookup v γ) ⟩ → ∥ StepOf b f γ z ∥₁)
              → ((z : S) → StepOf b f γ z → ⟨ fst z ∈ fst (lookup v γ) ⟩)
              → ⟨ γ ⊨ StepAt v b f ⟩
    StepAt-in ok into back = extAt-in-both v Φ γ
      (λ z z∈ → PT.rec (snd ((z ∷ γ) ⊨ Φ)) (fill ok z) (into z z∈))
      (λ z h → PT.rec (snd (fst z ∈ fst (lookup v γ))) (back z) (unfold ok z h))
  private
    sh2 : ∀ {n} → Fin n → Fin (suc (suc n))
    sh2 i = suc (suc i)
  
  module RecShape (Step : ∀ {n} → Fin n → Fin n → Fin n → Formula S n) where
  
    Domain₀ : S → V ℓ → Type (ℓ-suc ℓ)
    Domain₀ h B = (c z : S) → ⟨ pr (fst c) (fst z) ∈ fst h ⟩ → ⟨ fst c ∈ B ⟩
  
    ApproxAt : ∀ {n} → Fin n → Fin n → Formula S n
    ApproxAt f a = domAt f a
                 ∧̇ ∀̇ (∀̇ ( appAt (sh2 f) (suc zero) zero
                         ⇒̇ Step zero (suc zero) (sh2 f) ))
  
    GraphAt : ∀ {n} → Fin n → Fin n → Formula S n
    GraphAt w b = ∃̇ (ApproxAt zero (suc b) ∧̇ Step (suc w) (suc b) zero)
  
    module _ {n : ℕ} (f a : Fin n) (γ : S ^ n) where
      ApproxAt-dom : ⟨ γ ⊨ ApproxAt f a ⟩ → Domain₀ (lookup f γ) (fst (lookup a γ))
      ApproxAt-dom h = domAt-out f a γ (h .fst)
  
      ApproxAt-value : ⟨ γ ⊨ ApproxAt f a ⟩ → (c : S)
                     → ⟨ fst c ∈ fst (lookup a γ) ⟩
                     → ∥ (Σ[ z ∈ S ] ⟨ pr (fst c) (fst z) ∈ fst (lookup f γ) ⟩) ∥₁
      ApproxAt-value h = domAt-in f a γ (h .fst)
  
      ApproxAt-step : ⟨ γ ⊨ ApproxAt f a ⟩ → (c z : S)
                    → ⟨ pr (fst c) (fst z) ∈ fst (lookup f γ) ⟩
                    → ⟨ (z ∷ c ∷ γ) ⊨ Step zero (suc zero) (sh2 f) ⟩
      ApproxAt-step h c z p = h .snd c z
        (subst ⟨_⟩ (sym (appAt-adequate (sh2 f) (suc zero) zero (z ∷ c ∷ γ))) p)
  
      ApproxAt-in : ⟨ γ ⊨ domAt f a ⟩
                  → ((c z : S) → ⟨ pr (fst c) (fst z) ∈ fst (lookup f γ) ⟩
                     → ⟨ (z ∷ c ∷ γ) ⊨ Step zero (suc zero) (sh2 f) ⟩)
                  → ⟨ γ ⊨ ApproxAt f a ⟩
      ApproxAt-in hd hs = hd , λ c z p → hs c z
        (subst ⟨_⟩ (appAt-adequate (sh2 f) (suc zero) zero (z ∷ c ∷ γ)) p)
  
    module _ {n : ℕ} (w b : Fin n) (γ : S ^ n) where
      GraphOf : Type (ℓ-suc ℓ)
      GraphOf = Σ[ f ∈ S ] ( ⟨ (f ∷ γ) ⊨ ApproxAt zero (suc b) ⟩
                           × ⟨ (f ∷ γ) ⊨ Step (suc w) (suc b) zero ⟩ )
  
      Graph-in : (f : S) → ⟨ (f ∷ γ) ⊨ ApproxAt zero (suc b) ⟩
               → ⟨ (f ∷ γ) ⊨ Step (suc w) (suc b) zero ⟩ → ⟨ γ ⊨ GraphAt w b ⟩
      Graph-in f ha hs = ∣ f , (ha , hs) ∣₁
  
      Graph-out : ⟨ γ ⊨ GraphAt w b ⟩ → ∥ GraphOf ∥₁
      Graph-out h = h
  
    PairGraphAt : ∀ {n} → Fin n → Fin n → Formula S n
    PairGraphAt e c = ∃̇ (prAtL (suc e) (suc c) zero ∧̇ GraphAt zero (suc c))
  
    module _ {n : ℕ} (e c : Fin n) (γ : S ^ n)
             (φ : Formula S n) (qφ : φ ≡ PairGraphAt e c) where
      PairOf : Type (ℓ-suc ℓ)
      PairOf = Σ[ z ∈ S ] ( (fst (lookup e γ) ≡ pr (fst (lookup c γ)) (fst z))
                          × ⟨ (z ∷ γ) ⊨ GraphAt zero (suc c) ⟩ )
  
      PairGraph-in : (z : S) → fst (lookup e γ) ≡ pr (fst (lookup c γ)) (fst z)
                   → ⟨ (z ∷ γ) ⊨ GraphAt zero (suc c) ⟩ → ⟨ γ ⊨ φ ⟩
      PairGraph-in z q hg = subst (λ ψ → ⟨ γ ⊨ ψ ⟩) (sym qφ)
        ∣ z , (subst ⟨_⟩
          (sym (prAtL-adequate (suc e) (suc c) zero (z ∷ γ))) q , hg) ∣₁
  
      PairGraph-out : ⟨ γ ⊨ φ ⟩ → ∥ PairOf ∥₁
      PairGraph-out h = PT.map
        (λ { (z , (hq , hg)) →
          z , (subst ⟨_⟩ (prAtL-adequate (suc e) (suc c) zero (z ∷ γ)) hq , hg) })
        (subst (λ ψ → ⟨ γ ⊨ ψ ⟩) qφ h)
  
  open RecShape StepAt public renaming ( GraphAt to LsetGraphAt
                                       ; Graph-in to LsetGraph-in
                                       ; Graph-out to LsetGraph-out )
  
  LsetGraph : Formula S 2
  LsetGraph = LsetGraphAt zero (suc zero)

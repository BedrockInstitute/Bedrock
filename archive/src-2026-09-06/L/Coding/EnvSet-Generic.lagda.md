# Retired: `L.Coding.EnvSet.Generic`

The environment-set clause at an ARBITRARY arity set. `L.Coding.Sound` proves the
same conclusion with the arity pinned to a numeral, and that is the only form any
consumer ever took: none of the twelve importers of `L.Coding.EnvSet` named
`Generic` in its `using` list. Kept as material; outside the library path, and it
does not typecheck on its own.

```agda
module Generic (B ar : S) where
  private
    ixA : ⟪ fst ar ⟫ → S
    ixA m = ⟪ fst ar ⟫↪ m
          , isL-trans {x = fst ar} {y = ⟪ fst ar ⟫↪ m}
              (∈∈ₛ {a = ⟪ fst ar ⟫↪ m} {b = fst ar} .snd
                (∈ₛ⟪ fst ar ⟫↪ m))
              (snd ar)

    ixB : ⟪ fst B ⟫ → S
    ixB m = ⟪ fst B ⟫↪ m
          , isL-trans {x = fst B} {y = ⟪ fst B ⟫↪ m}
              (∈∈ₛ {a = ⟪ fst B ⟫↪ m} {b = fst B} .snd
                (∈ₛ⟪ fst B ⟫↪ m))
              (snd B)

    PairX : Type ℓ
    PairX = ⟪ fst ar ⟫ × ⟪ fst B ⟫

    pairS : PairX → S
    pairS p = prʟ (ixA (p .fst)) (ixB (p .snd))

    pairBound : Σ[ β ∈ V ℓ ] (IsOrd β ×
      ((p : PairX) → ⟨ fst (pairS p) ∈ Lset β ⟩))
    pairBound = stageFor PairX pairS

  amb : S
  amb = LsetS (pairBound .fst) (pairBound .snd .fst)

  pair∈amb : (u v : S) → ⟨ fst u ∈ fst ar ⟩ → ⟨ fst v ∈ fst B ⟩
           → ⟨ pr (fst u) (fst v) ∈ fst amb ⟩
  pair∈amb u v u∈ v∈ =
    subst (λ w → ⟨ w ∈ fst amb ⟩) (sym pairEq) (pairBound .snd .snd (m , n))
    where
    m : ⟪ fst ar ⟫
    m = ∈-asFiber {a = fst u} {b = fst ar} u∈ .fst
    em : ⟪ fst ar ⟫↪ m ≡ fst u
    em = ∈-asFiber {a = fst u} {b = fst ar} u∈ .snd
    n : ⟪ fst B ⟫
    n = ∈-asFiber {a = fst v} {b = fst B} v∈ .fst
    en : ⟪ fst B ⟫↪ n ≡ fst v
    en = ∈-asFiber {a = fst v} {b = fst B} v∈ .snd
    pairEq : pr (fst u) (fst v) ≡ fst (pairS (m , n))
    pairEq = cong₂ pr (sym em) (sym en) ∙ sym (prʟ-fst (ixA m) (ixB n))

  powamb : S
  powamb = hasPowerL amb .fst .fst

  powamb-spec : (x : S) → (x ∈ˢ powamb) ≡ (x ⊆ˢ amb)
  powamb-spec = hasPowerL amb .fst .snd

  powamb-in : (x : S) → ⟨ x ⊆ˢ amb ⟩ → ⟨ x ∈ˢ powamb ⟩
  powamb-in x h = subst ⟨_⟩ (sym (powamb-spec x)) h

  envFoGen : Formula S 1
  envFoGen = ∃̇ (∃̇ ( (var (suc zero) ≐ con ar)
                ∧̇ ((var zero ≐ con B)
                ∧̇ envOverAt (suc (suc zero)) (suc zero) zero) ))

  opaque
    envSetGen : S
    envSetGen = hasSeparationL powamb envFoGen .fst .fst

    envSetGen-spec : (x : S) → (x ∈ˢ envSetGen)
                   ≡ ((x ∈ˢ powamb) ⊓ ((x ∷ []) ⊨ envFoGen))
    envSetGen-spec = hasSeparationL powamb envFoGen .fst .snd

  envSetGen-in : (x : S) → ⟨ x ∈ˢ powamb ⟩ → ⟨ (x ∷ []) ⊨ envFoGen ⟩
               → ⟨ x ∈ˢ envSetGen ⟩
  envSetGen-in x hx hφ =
    subst ⟨_⟩ (sym (envSetGen-spec x)) (hx , hφ)

  envSetGen-out : (x : S) → ⟨ x ∈ˢ envSetGen ⟩
                → ⟨ (x ∷ []) ⊨ envFoGen ⟩
  envSetGen-out x hx = (subst ⟨_⟩ (envSetGen-spec x) hx) .snd

  -- An environment is a member of the power set: every member of it
  -- is one of the bounded pairs, hence lies in amb.
  envSubset : {k : ℕ} (γ : S ^ k) (di bi : Fin k)
            → fst (lookup di γ) ≡ fst ar
            → fst (lookup bi γ) ≡ fst B
            → (z : S)
            → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc di) (suc bi) ⟩
            → ⟨ z ⊆ˢ amb ⟩
  envSubset γ di bi qd qb z h w w∈ =
    PT.rec (snd (w ∈ˢ amb))
      (λ { (u , (v , (u∈ , (v∈ , eq)))) →
        subst (λ s → ⟨ s ∈ fst amb ⟩) (sym eq)
          (pair∈amb u v
            (subst (λ t → ⟨ fst u ∈ t ⟩) qd u∈)
            (subst (λ t → ⟨ fst v ∈ t ⟩) qb v∈)) })
      (pairsIn-out zero (suc di) (suc bi) (z ∷ γ)
        (envOver-pairs zero (suc di) (suc bi) (z ∷ γ) h) w w∈)

  -- The object-level description, read at a one-slot frame.
  foSat : {k : ℕ} (γ : S ^ k) (di bi : Fin k)
        → fst (lookup di γ) ≡ fst ar
        → fst (lookup bi γ) ≡ fst B
        → (z : S)
        → ⟨ (z ∷ []) ⊨ envFoGen ⟩
        → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc di) (suc bi) ⟩
  foSat γ di bi qd qb z h =
    PT.rec (snd ((z ∷ γ) ⊨ envOverAt zero (suc di) (suc bi)))
      (λ { (d , hd) → PT.rec (snd ((z ∷ γ) ⊨ envOverAt zero (suc di) (suc bi)))
        (λ { (b , (deq , (beq , ov))) →
          envOverAt-transport (b ∷ d ∷ z ∷ []) (z ∷ γ)
            (suc (suc zero)) (suc zero) zero zero (suc di) (suc bi)
            refl (deq ∙ sym qd) (beq ∙ sym qb) ov })
        hd })
      h

  backToFo : {k : ℕ} (γ : S ^ k) (di bi : Fin k)
           → fst (lookup di γ) ≡ fst ar
           → fst (lookup bi γ) ≡ fst B
           → (z : S)
           → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc di) (suc bi) ⟩
           → ⟨ (z ∷ []) ⊨ envFoGen ⟩
  backToFo γ di bi qd qb z h =
    ∣ ar , ∣ B ,
      ( refl
      , ( refl
        , envOverAt-transport (z ∷ γ) (B ∷ ar ∷ z ∷ [])
            zero (suc di) (suc bi) (suc (suc zero)) (suc zero) zero
            refl qd qb h ) ) ∣₁ ∣₁

  module Holds {k : ℕ} (γ : S ^ k) (Ei di bi : Fin k)
    (qE : fst (lookup Ei γ) ≡ fst envSetGen)
    (qd : fst (lookup di γ) ≡ fst ar)
    (qb : fst (lookup bi γ) ≡ fst B) where

    fwd : (z : S) → ⟨ fst z ∈ fst (lookup Ei γ) ⟩
        → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc di) (suc bi) ⟩
    fwd z hz =
      foSat γ di bi qd qb z
        (envSetGen-out z (subst (λ w → ⟨ fst z ∈ w ⟩) qE hz))

    bwd : (z : S) → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc di) (suc bi) ⟩
        → ⟨ fst z ∈ fst (lookup Ei γ) ⟩
    bwd z h =
      subst (λ w → ⟨ fst z ∈ w ⟩) (sym qE)
        (envSetGen-in z
          (powamb-in z (envSubset γ di bi qd qb z h))
          (backToFo γ di bi qd qb z h))

    holds : ⟨ γ ⊨ envSetAt Ei di bi ⟩
    holds = extAt-in-both Ei (envOverAt zero (suc di) (suc bi)) γ fwd bwd
```

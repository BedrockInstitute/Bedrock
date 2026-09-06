# The coded range set of an injective graph (retired 2026-09-06)

This chapter was the `private` tail of `src/L/Coding/Injection.lagda.md`.
It built, from replacement inside `L`, the range set of a coded
single-valued graph: `rangeGraph` reads the graph value-first as
`hasReplacementL` wants it, `module Range` produces the range set `C`
and its membership law, `inRanAt` and `ranAt` are the object-language
range formulas with their adequacy and their in/out pair, `module
RanHolds` shows the produced `C` satisfies `ranAt`, and `module
Injection` assembles the whole: an injection between the small index
types with the range produced rather than assumed, on `sv`, `dm` and
`ij` alone.

THE TREE HAD NO CONSUMER FOR ANY OF IT.  The block was `private`, so no
importer could name it, and nothing later in the file read it.  Every
importer of `L.Coding.Injection` takes only `injAt`, `injAt-in`,
`injAt-out`, `module Extract` and `module Small`, and each of those
stays in the live file.  The consumers that need a range supply it
themselves: `module Small` takes `C` and `ran` as hypotheses.

Restoring this needs the imports the live file no longer carries:
`con`, `_∈̇_`, `_∧̇_`, `∃̇_`, `∃̇∈` from `FOL.Syntax`, `domAt-out`,
`prAtL`, `prAtL-adequate`, `prʟ`, `prʟ-fst` from `L.Coding.Model`,
`hasReplacementL` from `L.Axioms.Full`, `SetOf` from `FOL.ZFModel`,
`_∈ˢ_` from `hPropStructure`, `⇔toPath` and `∃[∶]-syntax` from
`Cubical.Functions.Logic`, and `∣_∣₁` from propositional truncation.

The range machinery below is the master's own proof that an injective
graph has a range set, produced by replacement.  No block outside this
master names it, so it stays private; the exported surface above is what
A3, A4, A5, A6 and A7 consume.

```agda
private

  -- The graph, read value-first, as `hasReplacementL` wants it.
  rangeGraph : S → Formula S 2
  rangeGraph F = ∃̇∈ (con F) (prAtL zero (suc (suc zero)) (suc zero))

  rangeGraph-adequate : (F x y : S)
    → ((y ∷ x ∷ []) ⊨ rangeGraph F) ≡ (pr (fst x) (fst y) ∈ fst F)
  rangeGraph-adequate F x y = ⇔toPath fwd bwd
    where
    a = fst x
    b = fst y

    read : (z : S) → ⟨ (z ∷ y ∷ x ∷ []) ⊨ prAtL zero (suc (suc zero)) (suc zero) ⟩
         → fst z ≡ pr a b
    read z h = subst ⟨_⟩ (prAtL-adequate zero (suc (suc zero)) (suc zero)
                 (z ∷ y ∷ x ∷ [])) h

    fwd : ⟨ (y ∷ x ∷ []) ⊨ rangeGraph F ⟩ → ⟨ pr a b ∈ fst F ⟩
    fwd = PT.rec (snd (pr a b ∈ fst F))
      (λ { (z , (z∈F , h)) → subst (λ w → ⟨ w ∈ fst F ⟩) (read z h) z∈F })

    bwd : ⟨ pr a b ∈ fst F ⟩ → ⟨ (y ∷ x ∷ []) ⊨ rangeGraph F ⟩
    bwd h = ∣ prʟ x y
      , ( subst (λ w → ⟨ w ∈ fst F ⟩) (sym (prʟ-fst x y)) h
        , subst ⟨_⟩ (sym (prAtL-adequate zero (suc (suc zero)) (suc zero)
            (prʟ x y ∷ y ∷ x ∷ []))) (prʟ-fst x y) ) ∣₁

  -- The range set: the domain D with the graph formula, and the
  -- functionality that single-valuedness plus the domain give it.
  module Range (F D : S)
               (sv : ⟨ (F ∷ D ∷ []) ⊨ svAt zero ⟩)
               (dm : ⟨ (F ∷ D ∷ []) ⊨ domAt zero (suc zero) ⟩) where

    open Extract F D sv dm

    funct : (x : S) → ⟨ x ∈ˢ D ⟩
          → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ rangeGraph F ⟩)
    funct x x∈D = ctr , uniq
      where
      y₀ : Fib x
      y₀ = toVal x (domAt-in zero (suc zero) γ dm x x∈D)

      ctr : Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ rangeGraph F ⟩
      ctr = y₀ .fst , subst ⟨_⟩ (sym (rangeGraph-adequate F x (y₀ .fst))) (y₀ .snd)

      uniq : (r : Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ rangeGraph F ⟩) → ctr ≡ r
      uniq (y , q) = Σ≡Prop (λ w → snd ((w ∷ x ∷ []) ⊨ rangeGraph F))
        (Σ≡Prop (λ z → snd (isL z))
          (svAt-out zero γ sv x (y₀ .fst) y (y₀ .snd)
            (subst ⟨_⟩ (rangeGraph-adequate F x y) q)))

    Image : S → Ω
    Image y = ⋁ S (λ x → (x ∈ˢ D) ⊓ ((y ∷ x ∷ []) ⊨ rangeGraph F))

    rep : SetOf Image
    rep = hasReplacementL D (rangeGraph F) funct .fst

    C : S
    C = rep .fst

    C-mem : (y : S) → (y ∈ˢ C) ≡ Image y
    C-mem = rep .snd

  -- The range formula, mirroring `domAt`.
  inRanAt : ∀ {n} → Fin n → Fin n → Formula S n
  inRanAt f x = ∃̇ (appAt (suc f) zero (suc x))

  inRanAt-adequate : ∀ {n} (f x : Fin n) (γ : S ^ n)
    → (γ ⊨ inRanAt f x)
    ≡ (∃[ y ∶ S ] (pr (fst y) (fst (lookup x γ)) ∈ fst (lookup f γ)))
  inRanAt-adequate f x γ =
    cong (⋁ S) (funExt (λ y → appAt-adequate (suc f) zero (suc x) (y ∷ γ)))

  ranAt : ∀ {n} → Fin n → Fin n → Formula S n
  ranAt f c = ∀̇ ( (inRanAt (suc f) zero ⇒̇ (var zero ∈̇ var (suc c)))
               ∧̇ ((var zero ∈̇ var (suc c)) ⇒̇ inRanAt (suc f) zero) )

  module _ {n : ℕ} (f c : Fin n) (γ : S ^ n) where
    private
      step : (y : S)
           → ((y ∷ γ) ⊨ inRanAt (suc f) zero)
           ≡ (∃[ x ∶ S ] (pr (fst x) (fst y) ∈ fst (lookup f γ)))
      step y = inRanAt-adequate (suc f) zero (y ∷ γ)

    ranAt-out : ⟨ γ ⊨ ranAt f c ⟩ → (x y : S)
              → ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
              → ⟨ fst y ∈ fst (lookup c γ) ⟩
    ranAt-out h x y p = h y .fst (subst ⟨_⟩ (sym (step y)) ∣ x , p ∣₁)

    ranAt-intro : ((y : S)
                   → (⟨ ∃[ x ∶ S ] (pr (fst x) (fst y) ∈ fst (lookup f γ)) ⟩
                      → ⟨ fst y ∈ fst (lookup c γ) ⟩)
                   × (⟨ fst y ∈ fst (lookup c γ) ⟩
                      → ⟨ ∃[ x ∶ S ] (pr (fst x) (fst y) ∈ fst (lookup f γ)) ⟩))
                → ⟨ γ ⊨ ranAt f c ⟩
    ranAt-intro g y = (λ h → g y .fst (subst ⟨_⟩ (step y) h))
                    , (λ m → subst ⟨_⟩ (sym (step y)) (g y .snd m))

  -- The range set satisfies `ranAt`: the "every value lies in C"
  -- hypothesis is supplied here, by the construction above.
  module RanHolds (F D : S)
                  (sv : ⟨ (F ∷ D ∷ []) ⊨ svAt zero ⟩)
                  (dm : ⟨ (F ∷ D ∷ []) ⊨ domAt zero (suc zero) ⟩) where

    module R = Range F D sv dm

    C : S
    C = R.C

    holds : ⟨ (F ∷ C ∷ []) ⊨ ranAt zero (suc zero) ⟩
    holds = ranAt-intro zero (suc zero) (F ∷ C ∷ []) (λ y → fwd y , bwd y)
      where
      fwd : (y : S) → ⟨ ∃[ x ∶ S ] (pr (fst x) (fst y) ∈ fst F) ⟩
          → ⟨ fst y ∈ fst C ⟩
      fwd y = PT.rec (snd (fst y ∈ fst C))
        (λ { (x , p) → subst ⟨_⟩ (sym (R.C-mem y))
          ∣ x , (domAt-out zero (suc zero) (F ∷ D ∷ []) dm x y p
               , subst ⟨_⟩ (sym (rangeGraph-adequate F x y)) p) ∣₁ })

      bwd : (y : S) → ⟨ fst y ∈ fst C ⟩
          → ⟨ ∃[ x ∶ S ] (pr (fst x) (fst y) ∈ fst F) ⟩
      bwd y m = PT.map (λ { (x , (x∈D , g)) →
          x , subst ⟨_⟩ (rangeGraph-adequate F x y) g })
        (subst ⟨_⟩ (R.C-mem y) m)

  -- The whole, assembled: an injection between the small index types,
  -- with the range produced rather than assumed.  Only sv, dm and ij are
  -- hypotheses.
  module Injection (F D : S)
                   (sv : ⟨ (F ∷ D ∷ []) ⊨ svAt zero ⟩)
                   (dm : ⟨ (F ∷ D ∷ []) ⊨ domAt zero (suc zero) ⟩)
                   (ij : ⟨ (F ∷ D ∷ []) ⊨ injAt zero ⟩) where

    module H = RanHolds F D sv dm

    ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst H.C ⟩
    ran = ranAt-out zero (suc zero) (F ∷ H.C ∷ []) H.holds

    module S = Small F D H.C sv dm ij ran

    injection : ⟪ fst D ⟫ → ⟪ fst H.C ⟫
    injection = S.small

```

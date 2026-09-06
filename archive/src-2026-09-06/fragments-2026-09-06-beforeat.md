# Fragments removed 2026-09-06 (BeforeAt, confined)

## src/L/Choice/Before.lagda.md 1308-1491 (sh3, BeforeAt and its two readings)

Replaced by the confined form. `L.Choice.Limit`{.Agda}'s `Described`{.Agda} now
carries the two compared sets as members of the stage at the numeral held in the
slot, which both of its call sites (`same-in`, `same-out`) already had, so
`BeforeAt`{.Agda} is one binder and its two readings are one composition each of
`appC-adequate`, `beforeFam-in` / `beforeFam-out` and `relAt-fill` /
`relAt-rep`. The form below re-expanded the step through the maximal
predecessor, the stage graph and `PrecedesAt`{.Agda}.

    private
      sh3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
      sh3 i = suc (suc (suc i))
    opaque
      BeforeAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
      BeforeAt b x y =
        ∃̇ ( (var zero ∈̇ var (suc b))
          ∧̇ ( ∀̇∈ (var (suc b)) (¬̇ (var (suc zero) ∈̇ var zero))
            ∧̇ ∃̇ ( appC beforeFam (suc zero) zero
                 ∧̇ ∃̇ ( LsetGraphAt zero (suc (suc zero))
                      ∧̇ PrecedesAt (suc zero) zero (sh3 x) (sh3 y) ) ) ) )

    module _ {n : ℕ} (b x y : Fin n) (γ : S ^ n) (m : ℕ)
             (qb : fst (lookup b γ) ≡ # m) where
      private
        Inner : (c r A : S) → Type (ℓ-suc ℓ)
        Inner c r A =
            ⟨ (A ∷ r ∷ c ∷ γ) ⊨ LsetGraphAt zero (suc (suc zero)) ⟩
          × ⟨ (A ∷ r ∷ c ∷ γ) ⊨ PrecedesAt (suc zero) zero (sh3 x) (sh3 y) ⟩

        AtR : (c : S) → Type (ℓ-suc ℓ)
        AtR c = Σ[ r ∈ S ]
          ( ⟨ (r ∷ c ∷ γ) ⊨ appC beforeFam (suc zero) zero ⟩
          × ∥ (Σ[ A ∈ S ] Inner c r A) ∥₁ )

        AtC : Type (ℓ-suc ℓ)
        AtC = Σ[ c ∈ S ]
          ( ⟨ fst c ∈ fst (lookup b γ) ⟩
          × ( ⟨ (c ∷ γ) ⊨ ∀̇∈ (var (suc b)) (¬̇ (var (suc zero) ∈̇ var zero)) ⟩
            × ∥ AtR c ∥₁ ) )

        Goal : Type (ℓ-suc ℓ)
        Goal = ⟨ before m (fst (lookup x γ)) (fst (lookup y γ)) ⟩

        atA : (c r A : S) (j : ℕ) → fst c ≡ # j → m ≡ suc j
            → ⟨ pr (fst c) (fst r) ∈ fst beforeFam ⟩ → Inner c r A → Goal
        atA c r A j qc qm hf (hg , hprec) =
          subst (λ i → ⟨ before i (fst (lookup x γ)) (fst (lookup y γ)) ⟩) (sym qm)
            (precedes-map (Rel j) (before j) (finiteStage j)
              (fst (lookup x γ)) (fst (lookup y γ))
              (λ w t hw ht hbf → relAt-fill j w t hw ht hbf) atJ)
          where
          Rrep : (s t : S)
               → ⟨ pr (fst s) (fst t)
                   ∈ fst (lookup (suc zero) (A ∷ r ∷ c ∷ γ)) ⟩
               → ⟨ Held r (fst s) (fst t) ⟩
          Rrep s t p = p

          Rfill : (s t : S) → ⟨ Held r (fst s) (fst t) ⟩
                → ⟨ pr (fst s) (fst t)
                    ∈ fst (lookup (suc zero) (A ∷ r ∷ c ∷ γ)) ⟩
          Rfill s t p = p

          module P = Precedes (suc zero) zero (sh3 x) (sh3 y) (A ∷ r ∷ c ∷ γ)
                              (Held r) Rrep Rfill

          qA : fst A ≡ finiteStage j
          qA = Lset-only zero (suc (suc zero)) (A ∷ r ∷ c ∷ γ) hg
                 (subst IsOrd (sym qc) (numeral-ord j))
             ∙ cong Lset qc

          atJ : ⟨ precedes (Rel j) (finiteStage j)
                   (fst (lookup x γ)) (fst (lookup y γ)) ⟩
          atJ = subst (λ t → ⟨ precedes (λ s u → pr s u ∈ t) (finiteStage j)
                                (fst (lookup x γ)) (fst (lookup y γ)) ⟩)
                  (beforeFam-out c r j qc hf)
            (subst (λ t → ⟨ precedes (Held r) t
                              (fst (lookup x γ)) (fst (lookup y γ)) ⟩) qA
              (P.PrecedesAt-out hprec))

        atR : (c : S) (j : ℕ) → fst c ≡ # j → m ≡ suc j → AtR c → Goal
        atR c j qc qm (r , (happ , hA)) =
          PT.rec (snd (before m (fst (lookup x γ)) (fst (lookup y γ))))
            (λ { (A , hi) → atA c r A j qc qm hf hi }) hA
          where
          hf : ⟨ pr (fst c) (fst r) ∈ fst beforeFam ⟩
          hf = subst ⟨_⟩ (appC-adequate beforeFam (suc zero) zero (r ∷ c ∷ γ))
                 happ

        atC : AtC → Goal
        atC (c , (c∈ , (hmax , hr))) =
          PT.rec (snd (before m (fst (lookup x γ)) (fst (lookup y γ)))) named
            (∈#-elim m (fst c) (subst (λ t → ⟨ fst c ∈ t ⟩) qb c∈))
          where
          named : Σ[ j ∈ ℕ ] ((j < m) × (fst c ≡ # j)) → Goal
          named (j , (hj , qc)) =
            PT.rec (snd (before m (fst (lookup x γ)) (fst (lookup y γ))))
              (atR c j qc qm) hr
            where
            qm : m ≡ suc j
            qm = decide (suc j ≟ m)
              where
              decide : NatOrder.Trichotomy (suc j) m → m ≡ suc j
              decide (NatOrder.lt hlt) = Empty.rec
                (hmax (numS (suc j))
                  (subst (λ t → ⟨ fst (numS (suc j)) ∈ t ⟩) (sym qb)
                    (subst (λ t → ⟨ t ∈ # m ⟩) (sym (numS-fst (suc j)))
                      (#mono (suc j) m hlt)))
                  (subst (λ t → ⟨ fst c ∈ t ⟩) (sym (numS-fst (suc j)))
                    (subst (λ t → ⟨ t ∈ # (suc j) ⟩) (sym qc)
                      (#mono j (suc j) NatOrder.≤-refl))))
              decide (NatOrder.eq e) = sym e
              decide (NatOrder.gt hgt) = Empty.rec (<-asym hj (pred-≤-pred hgt))

      opaque
        unfolding BeforeAt

        BeforeAt-out : ⟨ γ ⊨ BeforeAt b x y ⟩
                     → ⟨ before m (fst (lookup x γ)) (fst (lookup y γ)) ⟩
        BeforeAt-out h =
          PT.rec (snd (before m (fst (lookup x γ)) (fst (lookup y γ)))) atC h

        BeforeAt-in : ⟨ before m (fst (lookup x γ)) (fst (lookup y γ)) ⟩
                    → ⟨ γ ⊨ BeforeAt b x y ⟩
        BeforeAt-in h =
          ∣ numS j , (c∈ , (hmax , ∣ relAt j , (happ
            , ∣ stageS j , (hg , hprec) ∣₁) ∣₁)) ∣₁
          where
          j : ℕ
          j = before-suc m (fst (lookup x γ)) (fst (lookup y γ)) h .fst

          qm : m ≡ suc j
          qm = before-suc m (fst (lookup x γ)) (fst (lookup y γ)) h .snd

          hj : j < m
          hj = subst (λ i → j < i) (sym qm) NatOrder.≤-refl

          c∈ : ⟨ fst (numS j) ∈ fst (lookup b γ) ⟩
          c∈ = subst (λ t → ⟨ fst (numS j) ∈ t ⟩) (sym qb)
            (subst (λ t → ⟨ t ∈ # m ⟩) (sym (numS-fst j)) (#mono j m hj))

          hmax : ⟨ (numS j ∷ γ)
                 ⊨ ∀̇∈ (var (suc b)) (¬̇ (var (suc zero) ∈̇ var zero)) ⟩
          hmax d hd hc = PT.rec Empty.isProp⊥ step
            (∈#-elim m (fst d) (subst (λ t → ⟨ fst d ∈ t ⟩) qb hd))
            where
            step : Σ[ i ∈ ℕ ] ((i < m) × (fst d ≡ # i)) → Empty.⊥
            step (i , (hi , qd)) =
              <-asym ji (pred-≤-pred (subst (λ t → i < t) qm hi))
              where
              ji : j < i
              ji = #∈#-elim j i
                (subst (λ t → ⟨ t ∈ # i ⟩) (numS-fst j)
                  (subst (λ t → ⟨ fst (numS j) ∈ t ⟩) qd hc))

          happ : ⟨ (relAt j ∷ numS j ∷ γ) ⊨ appC beforeFam (suc zero) zero ⟩
          happ = subst ⟨_⟩
            (sym (appC-adequate beforeFam (suc zero) zero (relAt j ∷ numS j ∷ γ)))
            (subst (λ t → ⟨ pr t (fst (relAt j)) ∈ fst beforeFam ⟩)
              (sym (numS-fst j)) (beforeFam-in j))

          hg : ⟨ (stageS j ∷ relAt j ∷ numS j ∷ γ)
               ⊨ LsetGraphAt zero (suc (suc zero)) ⟩
          hg = Lset-defines zero (suc (suc zero))
            (stageS j ∷ relAt j ∷ numS j ∷ γ)
            (subst IsOrd (sym (numS-fst j)) (numeral-ord j))
            (stageS-fst j ∙ cong Lset (sym (numS-fst j)))

          Rrep : (s t : S)
               → ⟨ pr (fst s) (fst t)
                   ∈ fst (lookup (suc zero) (stageS j ∷ relAt j ∷ numS j ∷ γ)) ⟩
               → ⟨ Held (relAt j) (fst s) (fst t) ⟩
          Rrep s t p = p

          Rfill : (s t : S) → ⟨ Held (relAt j) (fst s) (fst t) ⟩
                → ⟨ pr (fst s) (fst t)
                    ∈ fst (lookup (suc zero) (stageS j ∷ relAt j ∷ numS j ∷ γ)) ⟩
          Rfill s t p = p

          module P = Precedes (suc zero) zero (sh3 x) (sh3 y)
                              (stageS j ∷ relAt j ∷ numS j ∷ γ)
                              (Held (relAt j)) Rrep Rfill

          hprec : ⟨ (stageS j ∷ relAt j ∷ numS j ∷ γ)
                  ⊨ PrecedesAt (suc zero) zero (sh3 x) (sh3 y) ⟩
          hprec = P.PrecedesAt-in
            (subst (λ t → ⟨ precedes (Rel j) t
                             (fst (lookup x γ)) (fst (lookup y γ)) ⟩)
              (sym (stageS-fst j))
              (precedes-map (before j) (Rel j) (finiteStage j)
                (fst (lookup x γ)) (fst (lookup y γ))
                (λ w t hw ht hR → relAt-rep j w t hw ht hR)
                (subst (λ i → ⟨ before i (fst (lookup x γ)) (fst (lookup y γ)) ⟩)
                  qm h)))

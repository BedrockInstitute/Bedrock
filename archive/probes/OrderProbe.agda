{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module OrderProbe {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; #-inj′ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ}
  using ( numeralL; numeralL-fst; numeralL-zero; numeralL-suc )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; appAt; appAt-adequate )
open import L.Godel.Definable {ℓ}
  using ( interAt; interAt-out )
open import L.Godel.Operations {ℓ} using ( _∩_ )
import FOL.Absoluteness

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat.Order using ( _<_; _≤_; ≤-refl; ≤-suc; isProp≤ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; _≈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

private
  sh8 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc (suc (suc (suc n))))))))
  sh8 x = suc (suc (suc (suc (suc (suc (suc (suc x)))))))

  sh12 : ∀ {n} → Fin n
       → Fin (suc (suc (suc (suc (suc (suc (suc (suc
              (suc (suc (suc (suc n))))))))))))
  sh12 x = suc (suc (suc (suc (suc (suc (suc (suc
             (suc (suc (suc (suc x)))))))))))

-- ------------------------------------------------------------------
-- Part 1.  The first-appearance comparison atom.
--
-- The two level-number slots a and b hold level numbers as numerals.
-- The atom says the numeral at b is a member of the numeral at a, the
-- von Neumann order, i.e. the level number at b is strictly below the
-- level number at a.  Bound order: x ∷ y ∷ γ, where x is the value at
-- slot a and y the value at slot b.
-- ------------------------------------------------------------------

LevelLtAt : ∀ {n} → Fin n → Fin n → Formula S n
LevelLtAt a b = ∃̇ (∃̇ (
    (var (suc zero) ≐ var (suc (suc a)))
  ∧̇ ( (var zero ≐ var (suc (suc b)))
    ∧̇ (var zero ∈̇ var (suc zero)) )))

module _ {n : ℕ} (a b : Fin n) (γ : S ^ n) where
  -- The reader: satisfaction of the atom yields the model-level fact
  -- that the value at b is a member of the value at a, with both
  -- values pinned to the two slots.
  LevelLt-out : ⟨ γ ⊨ LevelLtAt a b ⟩
              → ∥ Σ[ x ∈ S ] Σ[ y ∈ S ]
                  ( (fst (lookup a γ) ≡ fst x)
                  × (fst (lookup b γ) ≡ fst y)
                  × ⟨ fst y ∈ fst x ⟩ ) ∥₁
  LevelLt-out =
    PT.rec PT.squash₁ (λ { (x , w₁) →
    PT.rec PT.squash₁ (λ { (y , body) →
      ∣ x , y ,
          ( sym (body .fst)
          , ( sym (body .snd .fst)
            , body .snd .snd ) ) ∣₁ }) w₁ })

-- The numeral reading: a member of a numeral is a strictly smaller
-- numeral.  This is the object-level translation of "compared as
-- numerals" back to the host natural numbers.
numeralL-mem : (p q : ℕ) → ⟨ numeralL q ∈ˢ numeralL p ⟩ → q < p
numeralL-mem zero q h = Empty.rec (numeralL-zero (numeralL q) h)
numeralL-mem (suc p) q h =
  PT.rec (isProp≤ {m = suc q} {n = suc p}) step
    (numeralL-suc p (numeralL q) .fst h)
  where
  step : ⟨ numeralL q ∈ˢ numeralL p ⟩ ⊎ ⟨ numeralL q ≈ˢ numeralL p ⟩
       → q < suc p
  step (inl h') = ≤-suc (numeralL-mem p q h')
  step (inr e) = subst (λ z → suc q ≤ z) (cong suc eq) (≤-refl {m = suc q})
    where
    eq : q ≡ p
    eq = #-inj′ (sym (numeralL-fst q) ∙ e ∙ numeralL-fst p)

-- ------------------------------------------------------------------
-- Part 2.  The least-producer condition for the intersection clause.
--
-- Slots: o = the previous-level order set (a set of Kuratowski pairs),
-- p = the previous level (a level table), x and y the two compared
-- members.  The formula says: x and y both arise at the next level by
-- the intersection clause from same-arity members of the previous
-- level, with producer triples (k, X, Y) and (k', X', Y'), the triple
-- of x lexicographically below the triple of y (k by numerals, then
-- the arguments by the previous-level order o), and each producer
-- triple least among its member's intersection producers.
--
-- Binder order (outermost to innermost): k' ∷ Y' ∷ X' ∷ z' ∷ k ∷ Y ∷ X
-- ∷ z, so the final environment is z ∷ X ∷ Y ∷ k ∷ z' ∷ X' ∷ Y' ∷ k'
-- ∷ γ, with var 0 = z, var 1 = X, var 2 = Y, var 3 = k, var 4 = z',
-- var 5 = X', var 6 = Y', var 7 = k'.  The least-ness conjuncts bind
-- four more variables on top (k'' ∷ Y'' ∷ X'' ∷ z'' for x, similarly
-- for y), reaching depth 12.
-- ------------------------------------------------------------------

-- The parts of the condition, at module level so that the formula and
-- its readers share one definition.  prodX/prodY/lt live at depth 8
-- (the environment after the eight existential binders); the
-- least-ness conjuncts quantify four more variables, reaching depth 12.
private
  prodXAt : ∀ {n} → Fin n → Fin n → Formula S
              (suc (suc (suc (suc (suc (suc (suc (suc n))))))))
  prodXAt p x = ( prAtL (sh8 x) (suc (suc (suc zero))) zero
               ∧̇ interAt zero (suc zero) (suc (suc zero))
               ∧̇ appAt (sh8 p) (suc (suc (suc zero))) (suc zero)
               ∧̇ appAt (sh8 p) (suc (suc (suc zero))) (suc (suc zero)) )

  prodYAt : ∀ {n} → Fin n → Fin n → Formula S
              (suc (suc (suc (suc (suc (suc (suc (suc n))))))))
  prodYAt p y = ( prAtL (sh8 y)
                      (suc (suc (suc (suc (suc (suc (suc zero)))))))
                      (suc (suc (suc (suc zero))))
               ∧̇ interAt (suc (suc (suc (suc zero))))
                     (suc (suc (suc (suc (suc zero)))))
                     (suc (suc (suc (suc (suc (suc zero))))))
               ∧̇ appAt (sh8 p)
                     (suc (suc (suc (suc (suc (suc (suc zero)))))))
                     (suc (suc (suc (suc (suc zero)))))
               ∧̇ appAt (sh8 p)
                     (suc (suc (suc (suc (suc (suc (suc zero)))))))
                     (suc (suc (suc (suc (suc (suc zero)))))) )

  ltAt : ∀ {n} → Fin n → Formula S
           (suc (suc (suc (suc (suc (suc (suc (suc n))))))))
  ltAt o = ( (var (suc (suc (suc zero))) ∈̇
              var (suc (suc (suc (suc (suc (suc (suc zero))))))))
           ∨̇ ( (var (suc (suc (suc zero))) ≐
                 var (suc (suc (suc (suc (suc (suc (suc zero))))))))
             ∧̇ ( appAt (sh8 o) (suc zero) (suc (suc (suc (suc (suc zero)))))
               ∨̇ ( (var (suc zero) ≐
                     var (suc (suc (suc (suc (suc zero))))))
                 ∧̇ appAt (sh8 o) (suc (suc zero))
                      (suc (suc (suc (suc (suc (suc zero)))))) ) ) ) )

  -- Depth-12 conjunct: the chosen triple of x is least among x's
  -- intersection producers.  Innermost environment (head first):
  -- z'' ∷ Y'' ∷ X'' ∷ k'' ∷ z ∷ X ∷ Y ∷ k ∷ z' ∷ X' ∷ Y' ∷ k' ∷ γ,
  -- so var 0 = z'', var 1 = Y'', var 2 = X'', var 3 = k'',
  -- var 4 = z, var 5 = X, var 6 = Y, var 7 = k.
  leastXAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S
               (suc (suc (suc (suc (suc (suc (suc (suc n))))))))
  leastXAt o p x = ∀̇ (∀̇ (∀̇ (∀̇ (
    ( ( prAtL (sh12 x) (suc (suc (suc zero))) zero
      ∧̇ interAt zero (suc (suc zero)) (suc zero)
      ∧̇ appAt (sh12 p) (suc (suc (suc zero))) (suc (suc zero))
      ∧̇ appAt (sh12 p) (suc (suc (suc zero))) (suc zero) )
    ⇒̇ ¬̇ ( (var (suc (suc (suc zero))) ∈̇ var (suc (suc (suc (suc (suc (suc (suc zero))))))))
         ∨̇ ( (var (suc (suc (suc zero))) ≐ var (suc (suc (suc (suc (suc (suc (suc zero))))))))
           ∧̇ ( appAt (sh12 o) (suc (suc zero)) (suc (suc (suc (suc (suc zero)))))
             ∨̇ ( (var (suc (suc zero)) ≐ var (suc (suc (suc (suc (suc zero))))))
               ∧̇ appAt (sh12 o) (suc zero) (suc (suc (suc (suc (suc (suc zero)))))) ) ) ) ) ) ))))

  -- Depth-12 conjunct for y: var 8 = z', var 9 = X', var 10 = Y',
  -- var 11 = k'.
  leastYAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S
               (suc (suc (suc (suc (suc (suc (suc (suc n))))))))
  leastYAt o p y = ∀̇ (∀̇ (∀̇ (∀̇ (
    ( ( prAtL (sh12 y) (suc (suc (suc zero))) zero
      ∧̇ interAt zero (suc (suc zero)) (suc zero)
      ∧̇ appAt (sh12 p) (suc (suc (suc zero))) (suc (suc zero))
      ∧̇ appAt (sh12 p) (suc (suc (suc zero))) (suc zero) )
    ⇒̇ ¬̇ ( (var (suc (suc (suc zero))) ∈̇
            var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))
         ∨̇ ( (var (suc (suc (suc zero))) ≐
               var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))
           ∧̇ ( appAt (sh12 o) (suc (suc zero))
                  (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
             ∨̇ ( (var (suc (suc zero)) ≐
                   var (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
               ∧̇ appAt (sh12 o) (suc zero)
                    (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) ) ) ) ) )))))

  bodyAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S
             (suc (suc (suc (suc (suc (suc (suc (suc n))))))))
  bodyAt o p x y = prodXAt p x ∧̇ (prodYAt p y ∧̇ (ltAt o ∧̇ (leastXAt o p x ∧̇ leastYAt o p y)))

LeastProdInterAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
LeastProdInterAt {n} o p x y = ∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (bodyAt o p x y))))))))

module _ {n : ℕ} (o p x y : Fin n) (γ : S ^ n) where
  lexRaw : (k z X Y k' z' X' Y' : S) → Type (ℓ-suc ℓ)
  lexRaw k z X Y k' z' X' Y' =
    ⟨ fst k ∈ fst k' ⟩
    ⊎ ( (fst k ≡ fst k')
      × ∥ ( ⟨ pr (fst X) (fst X') ∈ fst (lookup o γ) ⟩
          ⊎ ( (fst X ≡ fst X')
            × ⟨ pr (fst Y) (fst Y') ∈ fst (lookup o γ) ⟩ ) ) ∥₁ )

  -- The out-reader against the delivered interAt-out: satisfaction of
  -- the least-producer condition unpacks to the two producer triples
  -- with x = pr k (X ∩ Y) and y = pr k' (X' ∩ Y'), the four
  -- same-arity previous-level memberships, and the lexicographic
  -- comparison of the triples in the previous-level order o.  The
  -- least-ness conjuncts are projected away: they are inert for the
  -- reading, exactly as in the layer readers of the prior probe.
  LeastProdInter-out : ⟨ γ ⊨ LeastProdInterAt o p x y ⟩
                     → ∥ Σ[ k ∈ S ] Σ[ z ∈ S ] Σ[ X ∈ S ] Σ[ Y ∈ S ]
                           Σ[ k' ∈ S ] Σ[ z' ∈ S ] Σ[ X' ∈ S ] Σ[ Y' ∈ S ]
                           ( (fst (lookup x γ) ≡ pr (fst k) (fst z))
                           × ⟨ pr (fst k) (fst X) ∈ fst (lookup p γ) ⟩
                           × ⟨ pr (fst k) (fst Y) ∈ fst (lookup p γ) ⟩
                           × (fst z ≡ fst X ∩ fst Y)
                           × (fst (lookup y γ) ≡ pr (fst k') (fst z'))
                           × ⟨ pr (fst k') (fst X') ∈ fst (lookup p γ) ⟩
                           × ⟨ pr (fst k') (fst Y') ∈ fst (lookup p γ) ⟩
                           × (fst z' ≡ fst X' ∩ fst Y')
                           × ∥ lexRaw k z X Y k' z' X' Y' ∥₁ ) ∥₁

  LeastProdInter-out =
    PT.rec PT.squash₁ (λ { (k' , w₁) →
    PT.rec PT.squash₁ (λ { (Y' , w₂) →
    PT.rec PT.squash₁ (λ { (X' , w₃) →
    PT.rec PT.squash₁ (λ { (z' , w₄) →
    PT.rec PT.squash₁ (λ { (k , w₅) →
    PT.rec PT.squash₁ (λ { (Y , w₆) →
    PT.rec PT.squash₁ (λ { (X , w₇) →
    PT.rec PT.squash₁ (λ { (z , body) →
      ∣ k , z , X , Y , k' , z' , X' , Y' , finish k z X Y k' z' X' Y' body ∣₁
    }) w₇ }) w₆ }) w₅ }) w₄ }) w₃ }) w₂ }) w₁ })
    where
    env : (k z X Y k' z' X' Y' : S)
        → S ^ (suc (suc (suc (suc (suc (suc (suc (suc n))))))))
    env k z X Y k' z' X' Y' = z ∷ X ∷ Y ∷ k ∷ z' ∷ X' ∷ Y' ∷ k' ∷ γ

    lexRead : (k z X Y k' z' X' Y' : S)
            → ⟨ env k z X Y k' z' X' Y' ⊨
                 ( (var (suc (suc (suc zero))) ∈̇
                    var (suc (suc (suc (suc (suc (suc (suc zero))))))))
                 ∨̇ ( (var (suc (suc (suc zero))) ≐
                       var (suc (suc (suc (suc (suc (suc (suc zero))))))))
                   ∧̇ ( appAt (sh8 o) (suc zero)
                          (suc (suc (suc (suc (suc zero)))))
                     ∨̇ ( (var (suc zero) ≐
                           var (suc (suc (suc (suc (suc zero))))))
                       ∧̇ appAt (sh8 o) (suc (suc zero))
                            (suc (suc (suc (suc (suc (suc zero)))))) ) ) ) ) ⟩
            → ∥ lexRaw k z X Y k' z' X' Y' ∥₁
    lexRead k z X Y k' z' X' Y' =
      PT.map (λ { (inl h) → inl h
                ; (inr h) → inr ( h .fst
                                , PT.map (λ { (inl h') → inl (subst ⟨_⟩
                                                                (appAt-adequate (sh8 o)
                                                                  (suc zero)
                                                                  (suc (suc (suc (suc (suc zero)))))
                                                                  (env k z X Y k' z' X' Y')) h')
                                           ; (inr h') → inr ( h' .fst
                                                             , subst ⟨_⟩
                                                                 (appAt-adequate (sh8 o)
                                                                   (suc (suc zero))
                                                                   (suc (suc (suc (suc (suc (suc zero))))))
                                                                   (env k z X Y k' z' X' Y')) (h' .snd) ) })
                                         (h .snd) ) })

    finish : (k z X Y k' z' X' Y' : S)
           → ⟨ env k z X Y k' z' X' Y' ⊨ bodyAt o p x y ⟩
           → ( (fst (lookup x γ) ≡ pr (fst k) (fst z))
             × ⟨ pr (fst k) (fst X) ∈ fst (lookup p γ) ⟩
             × ⟨ pr (fst k) (fst Y) ∈ fst (lookup p γ) ⟩
             × (fst z ≡ fst X ∩ fst Y)
             × (fst (lookup y γ) ≡ pr (fst k') (fst z'))
             × ⟨ pr (fst k') (fst X') ∈ fst (lookup p γ) ⟩
             × ⟨ pr (fst k') (fst Y') ∈ fst (lookup p γ) ⟩
             × (fst z' ≡ fst X' ∩ fst Y')
             × ∥ lexRaw k z X Y k' z' X' Y' ∥₁ )
    finish k z X Y k' z' X' Y' (hpx , (hpy , (hlt , _))) =
      ( subst ⟨_⟩ (prAtL-adequate (sh8 x) (suc (suc (suc zero)))
            zero (env k z X Y k' z' X' Y')) (hpx .fst)
      , ( subst ⟨_⟩ (appAt-adequate (sh8 p) (suc (suc (suc zero)))
              (suc zero) (env k z X Y k' z' X' Y')) (hpx .snd .snd .fst)
        , ( subst ⟨_⟩ (appAt-adequate (sh8 p) (suc (suc (suc zero)))
                (suc (suc zero)) (env k z X Y k' z' X' Y')) (hpx .snd .snd .snd)
          , ( interAt-out zero (suc zero) (suc (suc zero))
                  (env k z X Y k' z' X' Y') (hpx .snd .fst)
            , ( subst ⟨_⟩ (prAtL-adequate (sh8 y)
                    (suc (suc (suc (suc (suc (suc (suc zero)))))))
                    (suc (suc (suc (suc zero))))
                    (env k z X Y k' z' X' Y'))
                    (hpy .fst)
              , ( subst ⟨_⟩ (appAt-adequate (sh8 p)
                      (suc (suc (suc (suc (suc (suc (suc zero)))))))
                      (suc (suc (suc (suc (suc zero)))))
                      (env k z X Y k' z' X' Y'))
                      (hpy .snd .snd .fst)
                , ( subst ⟨_⟩ (appAt-adequate (sh8 p)
                        (suc (suc (suc (suc (suc (suc (suc zero)))))))
                        (suc (suc (suc (suc (suc (suc zero))))))
                        (env k z X Y k' z' X' Y'))
                        (hpy .snd .snd .snd)
                  , ( interAt-out (suc (suc (suc (suc zero))))
                          (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc (suc (suc (suc zero))))))
                          (env k z X Y k' z' X' Y')
                          (hpy .snd .fst)
                  , lexRead k z X Y k' z' X' Y' hlt ) ) ) ) ) ) ) )

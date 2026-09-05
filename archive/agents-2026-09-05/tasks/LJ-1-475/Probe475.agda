{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.475]  First-order rank of an order carried as the set Q.
--
-- W3 FIRST  `fn-clause`.  f is a function whose domain is the
--            Q-predecessors of m.
-- TERM       `rank-formula`.  (Q : S) → Formula S 2.
--            Satisfaction at (z ∷ a ∷ []) says z is the pair of a
--            member of a and that member's rank in Q.
--
-- Delivered constructors, not invented:
--   prAtL, appAt, svAt, inDomAt, extAt, sucAtL
--     src/L/Coding/Model.lagda.md:122, :160, :210, :269, :662, :1395
--   InjCode spends svAt and domAt  src/L/Cardinal.lagda.md:225-227
-- Pin of Q as a constant: RelCond / appAtC shape
--     src/L/Choice/Before.lagda.md:220-226, :1302-1303
--
-- ONE Agda process per run, GHCRTS as the program set it on this pane.
-- Nothing lands in src/.  Do not import a probe.  Do not prove adequacy.
-- Do not carve.  Do not postulate.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-475.Probe475 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _≐_; _∈̇_; _∧̇_; _⇒̇_; ∀̇_; ∃̇_ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ}
  using ( prAtL; appAt; svAt; inDomAt; extAt; sucAtL )
open import Cubical.Data.FinData using ( Fin; zero; suc )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

private
  s2 : ∀ {n} → Fin n → Fin (suc (suc n))
  s2 i = suc (suc i)
  s3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  s3 i = suc (suc (suc i))
  s4 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc n))))
  s4 i = suc (suc (suc (suc i)))
  s5 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc n)))))
  s5 i = suc (suc (suc (suc (suc i))))

-- Generic in slots.  Env of the body of ∀̇ is (x ∷ original).
-- inDomAt (suc f) zero          :  x is in the domain of f
-- appAt   (suc Q) zero (suc m)  :  (x , m) belongs to Q
fnAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
fnAt f Q m =
  svAt f
  ∧̇ ∀̇ ( (inDomAt (suc f) zero ⇒̇ appAt (suc Q) zero (suc m))
      ∧̇ (appAt (suc Q) zero (suc m) ⇒̇ inDomAt (suc f) zero) )

-- f is a rank assignment on its domain, relative to order Q.
-- ∀ x. inDom(f,x) → ∃ ρ. app(f,x,ρ) ∧ ρ is the set of α that belong
-- to suc(f(y)) for some y with (y , x) ∈ Q.
--
-- Under ∀̇ then ∃̇ the env is (ρ ∷ x ∷ original).
-- extAt zero takes a formula at (α ∷ ρ ∷ x ∷ original).
assignAt : ∀ {n} → Fin n → Fin n → Formula S n
assignAt f Q =
  ∀̇ ( inDomAt (suc f) zero
    ⇒̇ ∃̇ ( appAt (s2 f) (suc zero) zero
        ∧̇ extAt zero (
            ∃̇ ( appAt (s4 Q) zero (s3 zero)
              ∧̇ ∃̇ ( appAt (s5 f) (suc zero) zero
                  ∧̇ ∃̇ ( sucAtL (suc zero) zero
                      ∧̇ (var (s3 zero) ∈̇ var zero) ) ) ) ) ) )

-- r is the set of α that belong to suc(f(y)) for some y in the domain
-- of f.  Under extAt the env of the condition is (α ∷ original).
supAt : ∀ {n} → Fin n → Fin n → Formula S n
supAt f r =
  extAt r (
    ∃̇ ( ∃̇ ( appAt (s3 f) (suc zero) zero
          ∧̇ ∃̇ ( sucAtL (suc zero) zero
              ∧̇ (var (s3 zero) ∈̇ var zero) ) ) ) )

-- =====================================================================
-- W3.  The function-as-a-set clause, Q a slot.  Env (f ∷ Q ∷ m ∷ []).
-- =====================================================================

fn-clause : Formula S 3
fn-clause = fnAt zero (suc zero) (suc (suc zero))

-- =====================================================================
-- Obligation.  Q a parameter, pinned once.  Free env (z ∷ a ∷ []).
-- After the pin and the three binders the env is
--   0 = f, 1 = r, 2 = m, 3 = Q', 4 = z, 5 = a
-- =====================================================================

rank-formula : (Q : S) → Formula S 2
rank-formula Q =
  ∃̇ ( (var zero ≐ con Q)
    ∧̇ ∃̇ ( ∃̇ (
        prAtL (s3 zero) (suc zero) zero
        ∧̇ (var (suc zero) ∈̇ var (s4 zero))
        ∧̇ ∃̇ ( fnAt zero (s3 zero) (s2 zero)
            ∧̇ assignAt zero (s3 zero)
            ∧̇ supAt zero (suc zero) ) ) ) )

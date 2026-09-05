{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.258] probe: the fifteen step-6 fields that do NOT touch
-- envSetK, supplied at a CONCRETE K.  The concrete K is the
-- constructibility level `Lset α` as an element of L; its transitivity
-- is `layer-trans (Lset-layer α)` (both delivered).  The four groups
-- are measured apart (P-l): valK/valK-un, valV/valW/wKfact, the seven
-- subK-*, and the three consK-*.
--
-- ONE agda process, GHCRTS="-A64m -I0 -M8g", cap never raised.
-- Never committed.  Written incrementally (C-22).

open import Base.Prelude
open import Base.Truth

module LJ-1-258.ProbeLJ1258 {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_ )
open import FOL.Semantics using ( _^_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; isTransV; Lset; Lset-layer; layer-trans )
open import L.Axioms.Basic {ℓ} using ( isL-Lset )
open import L.Coding.Model {ℓ}
  using ( tmValAt; tmValAt-out; subValAt; subValSuccAt
        ; subValAt-adequate; subValSuccAt-adequate; consAtL; consAtL-adequate )
open import L.Coding.Environment {ℓ} using ( env; cons )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; pairing-ax; module InfinitySet )
open InfinitySet using ( #_; sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.FinData using ( Fin )
open import Cubical.Data.Vec using ( Vec; lookup )

-- Named Fin indices, definitionally the same `suc` chains the field
-- types write.  `zero` and `suc` come from Base.Prelude (which opens
-- FinData's constructors); the patterns are named here so the bodies
-- match the types without re-writing the chains.
pattern one   = suc zero
pattern two   = suc one
pattern three = suc two
pattern four  = suc three
pattern five  = suc four
pattern six   = suc five
pattern seven = suc six
pattern eight = suc seven
pattern nine  = suc eight

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _⊨ᵐ_ )

-- ===================================================================
-- THE FOUR GROUPS, each stated over the structure (K, Ktr).  No tower
-- is named; the J tower re-instantiates Fact unchanged (DD4).
-- ===================================================================

module Fact (K : S) (Ktr : isTransV (fst K)) where

  -- A transitive set absorbs both components of a Kuratowski pair it
  -- contains.  This is the shared lemma beneath valK, valK-un and the
  -- whole subK group ([LJ-1.151] ProbeLJ1151A.agda:58-71, green).
  prK : (x y : V ℓ) → ⟨ pr x y ∈ fst K ⟩ → ⟨ x ∈ fst K ⟩ × ⟨ y ∈ fst K ⟩
  prK x y h = Ktr (mem x (inl refl)) pairInK , Ktr (mem y (inr refl)) pairInK
    where
    pairInK : ⟨ ⁅ x , y ⁆ ∈ fst K ⟩
    pairInK = Ktr (∈∈ₛ {a = ⁅ x , y ⁆} {b = pr x y} .snd
                (pairing-ax ⁅ x ⁆s ⁅ x , y ⁆ ⁅ x , y ⁆ .snd ∣ inr refl ∣₁)) h
    mem : (z : V ℓ) → (z ≡ x) Sum.⊎ (z ≡ y) → ⟨ z ∈ ⁅ x , y ⁆ ⟩
    mem z e = ∈∈ₛ {a = z} {b = ⁅ x , y ⁆} .snd (pairing-ax x y z .snd ∣ e ∣₁)

  -- ===================================================================
  -- GROUP 1: valK, valK-un.  `yc ∈ K` from the graph entry
  -- `pr c yc ∈ T`, with the site fact `T ∈ K`.  The code equation and
  -- `c ∈ C` are dead weight (MEASURED [LJ-1.151] section 1.5); the
  -- honest reader is `prK`, the graph entry closure.
  -- ===================================================================

  valK : (C T : S) → ⟨ fst T ∈ fst K ⟩
       → (k : ℕ) (c ar a b yc : S)
       → ⟨ fst c ∈ fst C ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
       → ⟨ pr (fst c) (fst yc) ∈ fst T ⟩
       → ⟨ fst yc ∈ fst K ⟩
  valK C T TK k c ar a b yc c∈ shape hc =
    prK (fst c) (fst yc) (Ktr hc TK) .snd

  valK-un : (C T : S) → ⟨ fst T ∈ fst K ⟩
          → (k : ℕ) (c ar a yc : S)
          → ⟨ fst c ∈ fst C ⟩
          → fst c ≡ pr (fst ar) (pr (# k) (fst a))
          → ⟨ pr (fst c) (fst yc) ∈ fst T ⟩
          → ⟨ fst yc ∈ fst K ⟩
  valK-un C T TK k c ar a yc c∈ shape hc =
    prK (fst c) (fst yc) (Ktr hc TK) .snd

  -- ===================================================================
  -- GROUP 3: the seven subK-* fields.  `subValAt-adequate` /
  -- `subValSuccAt-adequate` turn the satisfaction into a pair-in-table
  -- membership, and `prK` extracts the value component.  ONE proof,
  -- seven instantiations.
  -- ===================================================================

  subK-gen : {n : ℕ} (γ : Vec S n) (T ar a y : Fin n)
           → ⟨ fst (lookup T γ) ∈ fst K ⟩
           → ⟨ γ ⊨ᵐ subValAt T ar a y ⟩
           → ⟨ fst (lookup y γ) ∈ fst K ⟩
  subK-gen γ T ar a y TK h =
    prK (pr (fst (lookup ar γ)) (fst (lookup a γ))) (fst (lookup y γ))
      (Ktr (subst ⟨_⟩ (subValAt-adequate T ar a y γ) h) TK) .snd

  subKSucc-gen : {n : ℕ} (γ : Vec S n) (T ar a y : Fin n)
               → ⟨ fst (lookup T γ) ∈ fst K ⟩
               → ⟨ γ ⊨ᵐ subValSuccAt T ar a y ⟩
               → ⟨ fst (lookup y γ) ∈ fst K ⟩
  subKSucc-gen γ T ar a y TK h =
    prK (pr (sucV (fst (lookup ar γ))) (fst (lookup a γ))) (fst (lookup y γ))
      (Ktr (subst ⟨_⟩ (subValSuccAt-adequate T ar a y γ) h) TK) .snd

  -- The seven fields, at the master's own slot indices
  -- (src/L/Condensation/TwelveAgree.lagda.md), with the frame
  -- environment left as an abstract two-slot vector (carrier at 0,
  -- table T at 1) and the site fact `T ∈ K` as a premise.

  subK₁-and : (γ' : Vec S 2) → ⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩
            → (x y yc b a ar c : S)
            → ⟨ (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨ᵐ
                  subValAt (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                           (suc (suc (suc (suc (suc zero)))))
                           (suc (suc (suc (suc zero))))
                           (suc zero) ⟩
            → ⟨ fst y ∈ fst K ⟩
  subK₁-and γ' TK x y yc b a ar c h =
    subK-gen (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') eight five four one TK h

  subK₀-and : (γ' : Vec S 2) → ⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩
            → (y ya yc b a ar c : S)
            → ⟨ (y ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨ᵐ
                  subValAt (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                           (suc (suc (suc (suc (suc zero)))))
                           (suc (suc (suc zero)))
                           zero ⟩
            → ⟨ fst y ∈ fst K ⟩
  subK₀-and γ' TK y ya yc b a ar c h =
    subK-gen (y ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') eight five three zero TK h

  subK₁-imp : (γ' : Vec S 2) → ⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩
            → (E yb ya yc b a ar c : S)
            → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨ᵐ
                  subValAt (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                           (suc (suc (suc (suc (suc (suc zero))))))
                           (suc (suc (suc (suc (suc zero)))))
                           (suc (suc zero)) ⟩
            → ⟨ fst ya ∈ fst K ⟩
  subK₁-imp γ' TK E yb ya yc b a ar c h =
    subK-gen (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') nine six five two TK h

  subK₀-imp : (γ' : Vec S 2) → ⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩
            → (E yb ya yc b a ar c : S)
            → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨ᵐ
                  subValAt (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                           (suc (suc (suc (suc (suc (suc zero))))))
                           (suc (suc (suc (suc zero))))
                           (suc zero) ⟩
            → ⟨ fst yb ∈ fst K ⟩
  subK₀-imp γ' TK E yb ya yc b a ar c h =
    subK-gen (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') nine six four one TK h

  subK-neg : (γ' : Vec S 2) → ⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩
           → (ya yc a ar c E : S)
           → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨ᵐ
                 subValAt (suc (suc (suc (suc (suc (suc (suc zero)))))))
                          (suc (suc (suc (suc zero))))
                          (suc (suc (suc zero)))
                          (suc zero) ⟩
           → ⟨ fst ya ∈ fst K ⟩
  subK-neg γ' TK ya yc a ar c E h =
    subK-gen (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') seven four three one TK h

  subK-un : (γ' : Vec S 2) → ⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩
          → (ya yc a ar c E : S)
          → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨ᵐ
                subValSuccAt (suc (suc (suc (suc (suc (suc (suc zero)))))))
                             (suc (suc (suc (suc zero))))
                             (suc (suc (suc zero)))
                             (suc zero) ⟩
          → ⟨ fst ya ∈ fst K ⟩
  subK-un γ' TK ya yc a ar c E h =
    subKSucc-gen (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') seven four three one TK h

  subK-allin : (γ' : Vec S 2) → ⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩
             → (E ya yc b a ar c : S)
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨ᵐ
                   subValSuccAt (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                                (suc (suc (suc (suc (suc zero)))))
                                (suc (suc (suc zero)))
                                (suc zero) ⟩
             → ⟨ fst ya ∈ fst K ⟩
  subK-allin γ' TK E ya yc b a ar c h =
    subKSucc-gen (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') eight five three one TK h

  -- ===================================================================
  -- GROUP 2: valV, valW, wKfact.  `tmValAt-out` splits the term value
  -- into a variable (value looked up in the environment) or a constant;
  -- `prK` plus the site facts `Env ∈ K` and `T ∈ K` closes each case.
  -- ONE proof, three instantiations.
  -- ===================================================================

  tmValK : {n : ℕ} (γ : Vec S n) (t e v : Fin n)
         → ⟨ fst (lookup e γ) ∈ fst K ⟩
         → ⟨ fst (lookup t γ) ∈ fst K ⟩
         → ⟨ γ ⊨ᵐ tmValAt t e v ⟩
         → ⟨ fst (lookup v γ) ∈ fst K ⟩
  tmValK γ t e v eK tK h =
    PT.rec (snd (fst (lookup v γ) ∈ fst K)) (λ { (inl q) → varCase q
                                              ; (inr q) → conCase q })
      (tmValAt-out t e v γ h)
    where
    varCase : (Σ[ k ∈ S ] ((fst (lookup t γ) ≡ pr (# 1) (fst k))
                            × ⟨ pr (fst k) (fst (lookup v γ)) ∈ fst (lookup e γ) ⟩))
            → ⟨ fst (lookup v γ) ∈ fst K ⟩
    varCase (k , (_ , kv∈e)) = prK (fst k) (fst (lookup v γ)) (Ktr kv∈e eK) .snd
    conCase : fst (lookup t γ) ≡ pr (# 0) (fst (lookup v γ))
            → ⟨ fst (lookup v γ) ∈ fst K ⟩
    conCase q = prK (# 0) (fst (lookup v γ))
      (subst (λ w → ⟨ w ∈ fst K ⟩) q tK) .snd

  -- valV: tmValAt 6 2 1 at w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ'.
  valV : (γ' : Vec S 2) → (E yc b a ar c z v w : S)
       → ⟨ fst z ∈ fst K ⟩ → ⟨ fst a ∈ fst K ⟩
       → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨ᵐ
             tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                     (suc (suc zero))
                     (suc zero) ⟩
       → ⟨ fst v ∈ fst K ⟩
  valV γ' E yc b a ar c z v w zK aK h =
    tmValK (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') six two one zK aK h

  -- valW: tmValAt 5 2 0 at w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ'.
  valW : (γ' : Vec S 2) → (E yc b a ar c z v w : S)
       → ⟨ fst z ∈ fst K ⟩ → ⟨ fst b ∈ fst K ⟩
       → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨ᵐ
             tmValAt (suc (suc (suc (suc (suc zero)))))
                     (suc (suc zero))
                     zero ⟩
       → ⟨ fst w ∈ fst K ⟩
  valW γ' E yc b a ar c z v w zK bK h =
    tmValK (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') five two zero zK bK h

  -- wKfact: tmValAt 6 1 0 at w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ'.
  wKfact : (γ' : Vec S 2) → (E ya yc b a ar c z w : S)
         → ⟨ fst z ∈ fst K ⟩ → ⟨ fst a ∈ fst K ⟩
         → ⟨ (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨ᵐ
               tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                       (suc zero)
                       zero ⟩
         → ⟨ fst w ∈ fst K ⟩
  wKfact γ' E ya yc b a ar c z w zK aK h =
    tmValK (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') six one zero zK aK h

  -- ===================================================================
  -- GROUP 4: consK-exist, consK-forall, consK-allin.
  --
  -- `consAtL-adequate` turns the satisfaction into
  --   e' ≡ env (cons x g)   with   z ≡ env g.
  -- The remaining step is the ENV CLOSURE: env (cons x g) ∈ K from
  -- env g ∈ K and x ∈ K.  That fact is NOT delivered in src/
  -- (MEASURED: no lemma in src/ concludes `env _ ∈ ...`; the only
  -- closure lemmas are `envSetK`/`envInK` for the MACHINE's
  -- `envSetGen`, out of this task's scope — [LJ-1.257]).  It is the
  -- term each of the three needs (C-36).  The module below states it
  -- as the hypothesis and shows the three fields then build; the
  -- hypothesis itself is the term the report names.
  -- ===================================================================

  module ConsK
    (envConsK : {k : ℕ} (g : Fin k → V ℓ) (x : V ℓ)
              → ⟨ env g ∈ fst K ⟩ → ⟨ x ∈ fst K ⟩
              → ⟨ env (cons x g) ∈ fst K ⟩) where

    consK-forall : (γ' : Vec S 2) → (ya yc a ar c E z x e' : S)
                 → {k : ℕ} (g : Fin k → V ℓ)
                 → fst z ≡ env g
                 → ⟨ fst z ∈ fst K ⟩ → ⟨ fst x ∈ fst K ⟩
                 → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨ᵐ
                     consAtL zero (suc zero) (suc (suc zero)) ⟩
                 → ⟨ fst e' ∈ fst K ⟩
    consK-forall γ' ya yc a ar c E z x e' g zg zK xK h =
      subst (λ w → ⟨ w ∈ fst K ⟩) (sym e'eq)
        (envConsK g (fst x) (subst (λ w → ⟨ w ∈ fst K ⟩) zg zK) xK)
      where
      e'eq : fst e' ≡ env (cons (fst x) g)
      e'eq = subst ⟨_⟩ (consAtL-adequate zero (suc zero) (suc (suc zero))
               (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') g zg) h

    consK-allin : (γ' : Vec S 2) → (E ya yc b a ar c z w x e' : S)
                → {k : ℕ} (g : Fin k → V ℓ)
                → fst z ≡ env g
                → ⟨ fst z ∈ fst K ⟩ → ⟨ fst x ∈ fst K ⟩
                → ⟨ (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨ᵐ
                    consAtL zero (suc zero) (suc (suc (suc zero))) ⟩
                → ⟨ fst e' ∈ fst K ⟩
    consK-allin γ' E ya yc b a ar c z w x e' g zg zK xK h =
      subst (λ w → ⟨ w ∈ fst K ⟩) (sym e'eq)
        (envConsK g (fst x) (subst (λ w → ⟨ w ∈ fst K ⟩) zg zK) xK)
      where
      e'eq : fst e' ≡ env (cons (fst x) g)
      e'eq = subst ⟨_⟩ (consAtL-adequate zero (suc zero) (suc (suc (suc zero)))
               (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') g zg) h

    -- consK-exist carries the extra conjunct e' ∈ ya, so it closes from
    -- the site fact ya ∈ K by transitivity alone; its consAtL conjunct
    -- is dead weight (the same defect [LJ-1.151] measured for valK).
    consK-exist : (γ' : Vec S 2) → (ya yc a ar c E z x e' : S)
                → ⟨ fst ya ∈ fst K ⟩
                → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨ᵐ
                    consAtL zero (suc zero) (suc (suc zero))
                    ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ⟩
                → ⟨ fst e' ∈ fst K ⟩
    consK-exist γ' ya yc a ar c E z x e' yaK h =
      Ktr (h .snd) yaK

-- ===================================================================
-- The concrete instance: K = Lset α as an element of L.
-- ===================================================================

levelK : (α : V ℓ) → IsOrd α → S
levelK α o = Lset α , isL-Lset α o

module AtLevel (α : V ℓ) (o : IsOrd α) =
  Fact (levelK α o) (layer-trans (Lset-layer α))

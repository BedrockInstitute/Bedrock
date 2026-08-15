{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.269 Sketch B: an Agda macro that generates ρ : Fin 16 → Fin 16
-- from a declarative layout, so the specification stops living in a comment.
-- Runs under the tree's exact OPTIONS header.

module LJ-1-269.ProbeLJ1269B where

open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; _∷_; [])
open import Cubical.Data.FinData as FinD using (Fin; toℕ)
  renaming (zero to fz; suc to fs)
open import Cubical.Data.Vec as VecD using (Vec)

-- A visible relevant argument.
vArg : {A : Set} → A → Arg A
vArg x = arg (arg-info visible (modality relevant quantity-ω)) x

-- The term for position k : the constructor chain suc^k zero.
finTerm : ℕ → Term
finTerm k = go k (con (quote FinD.Fin.zero) [])
  where
  go : ℕ → Term → Term
  go zero t = t
  go (suc n) t = go n (con (quote FinD.Fin.suc) (vArg t ∷ []))

-- The term for a Vec of Fin positions.
vecTerm : List ℕ → Term
vecTerm []       = con (quote VecD.Vec.[]) []
vecTerm (k ∷ ks) = con (quote VecD.Vec._∷_) (vArg (finTerm k) ∷ vArg (vecTerm ks) ∷ [])

-- The macro: fills a hole of type Fin 16 → Fin 16 with λ i → lookup i table.
macro
  perm : List ℕ → Term → TC ⊤
  perm layout hole =
    unify hole
      (lam visible
        (abs "i"
          (def (quote VecD.lookup)
            (vArg (var 0 []) ∷ vArg (vecTerm layout) ∷ []))))

-- The declarative layout, source order 0=w,1=v,2=γ,3=K,4..15=δ₀..δ₁₁,
-- giving the TARGET position of each source slot:
--   w→0, v→14, γ→15, K→1, δᵢ→2+i.
layout : List ℕ
layout = 0 ∷ 14 ∷ 15 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ 11 ∷ 12 ∷ 13 ∷ []

-- The generated permutation. If this typechecks, the macro generated ρ.
ρ : Fin 16 → Fin 16
ρ = perm layout

-- CORRECTNESS of the generated term: not just well-typed, but the right map.
toℕρ : Fin 16 → ℕ
toℕρ i = toℕ (ρ i)

check0  : toℕρ fz ≡ 0   ; check0  = refl
check1  : toℕρ (fs fz) ≡ 14  ; check1  = refl
check2  : toℕρ (fs (fs fz)) ≡ 15  ; check2  = refl
check3  : toℕρ (fs (fs (fs fz))) ≡ 1  ; check3  = refl
check4  : toℕρ (fs (fs (fs (fs fz)))) ≡ 2  ; check4  = refl
check15 : toℕρ (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz))))))))))))))) ≡ 13
check15 = refl

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.703] renameFo commute for LsetGraphAt, satGraphAt unfolded.
-- Same lemma [LJ-1.685] ran as runs/RENAME3. Rewritten here so this
-- probe does not import LJ-1-685.runs.*.

open import Base.Prelude
open import Base.Classical using ( LEM )

module LJ-1-703.runs.RENAME3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Renaming using ( renameFo )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Coding.Graph {ℓ} lem using ( satGraphAt )

opaque
  unfolding satGraphAt
  rename-graph : {n m : ℕ} (ρ : Fin n → Fin m) (w b : Fin n)
               → renameFo ρ (LsetGraphAt w b) ≡ LsetGraphAt (ρ w) (ρ b)
  rename-graph ρ w b = refl

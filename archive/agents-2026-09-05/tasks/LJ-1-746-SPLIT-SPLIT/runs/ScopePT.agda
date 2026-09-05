{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module LJ-1-746-SPLIT-SPLIT.runs.ScopePT {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import LJ-1-746-SPLIT-SPLIT.runs.Amb7 {ℓ} lem
open import LJ-1-746-SPLIT-SPLIT.runs.PT {ℓ} lem

t : Type (ℓ-suc ℓ)
t = StepKilledGen

u : StepKilledGen → Type (ℓ-suc ℓ)
u gen = ApproxSlot × StepSlot

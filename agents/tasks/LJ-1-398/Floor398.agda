{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.398] PROBE.  The BAND RECURSION on the two selections, and
-- the residue it leaves.  It runs in agents/tasks/LJ-1-398/ and lands
-- nothing in src/.
--
--   TERM 1  `band-owes-2`.  The residue: the untruncated AMBIENT
--            arrow at an L-cardinal that is not its own ambient least
--            cardinal.  Every other case has a supplier.
--
--   TERM 2  `sq-band-2`.  The recursion, by `∈-induction`, split by
--            `lem` on `IsCardinalL` (a proposition), then by
--            `kappa-decides` on whether the site is its own ambient
--            least cardinal:
--
--     case                                   supplier
--     x ≡ ω                                 `squareω`, delivered
--     ¬ IsCardinalL x                       `coded-arrow`, then
--                                           `descent-core`
--     IsCardinalL x, x its own least card   `amb-card-at-kappa`,
--                                           `kappa-is-limit`,
--                                           `amb-init'`,
--                                           `via-col-square`
--     IsCardinalL x, x not its own least    `band-owes-2` (residue),
--                                           then `descent-core`
--
--   The suppliers are taken as hypotheses of a nested module, so the
--   witness meter sees a clean top-level telescope; `coded-arrow` and
--   `amb-card-at-kappa` name `L.Cardinal`'s `IsCardinalL` and
--   `LeastCardInjL.κ`, which live behind `lem` and cannot be opened
--   above the header.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω; sucV )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-398.Floor398 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀) where

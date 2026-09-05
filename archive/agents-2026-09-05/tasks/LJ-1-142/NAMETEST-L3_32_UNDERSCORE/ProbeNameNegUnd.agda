{-# OPTIONS --cubical --safe #-}

-- [LJ-1.142] Directory-name legality evidence. The DIRECTORY name is the test.
module LJ-1-142.NAMETEST-L3_32_UNDERSCORE.ProbeNameNegUnd where

open import Agda.Primitive using (Level)

shape : Level → Level
shape ℓ = ℓ

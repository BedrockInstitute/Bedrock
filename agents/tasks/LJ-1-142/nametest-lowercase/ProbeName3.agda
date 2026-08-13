{-# OPTIONS --cubical --safe #-}

-- [LJ-1.142] Directory-name legality evidence. The DIRECTORY name is the test.
module LJ-1-142.nametest-lowercase.ProbeName3 where

open import Agda.Primitive using (Level)

shape : Level → Level
shape ℓ = ℓ

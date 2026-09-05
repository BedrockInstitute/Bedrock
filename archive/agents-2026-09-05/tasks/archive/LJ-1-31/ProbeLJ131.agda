{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.31] Probe: the delivered masters carry no constants in consAtL.
-- countFo (consAtL e' m e) is 0 at the real carrier, so the delivered erase
-- accepts the real reader with no placement. The real clause forms keep
-- constants from OTHER readers (the arity tag and the term-value tags),
-- never from consAtL. All counts below are refl-verified against the
-- delivered L.Coding.Model.
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth

module ProbeLJ131 {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Manipulation.Parameters using ( countFo; constantsFo )
import FOL.Count
open import FOL.Syntax using ( Formula )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Model {ℓ}
  using ( consAtL; existClauseAt; forallClauseAt; allInClauseAt; exInClauseAt
        ; body∃; body∀; bodyAll; bodyEx; tmValAt; envSetAt; subValSuccAt
        ; envOverAt; arityTagPairAtL; tagPairAtL; tagAtL )
open import Cubical.Data.Vec using ( Vec; _∷_; []; lookup )
open import Cubical.Data.FinData using ( Fin; zero; suc )

open hPropStructure 𝒮ʟ using ( S )

-- The reader itself: count zero at the delivered carrier, every arity.
_ : countFo (consAtL {1} zero zero zero) ≡ 0
_ = refl

_ : countFo (consAtL {3} zero (suc zero) (suc (suc zero))) ≡ 0
_ = refl

_ : countFo (consAtL {11} zero (suc zero) (suc (suc (suc zero)))) ≡ 0
_ = refl

-- The delivered erase accepts the real reader: the whole-clause count is 0.
module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} S

_ : Formula (⊥* {ℓ-suc ℓ}) 1
_ = Cnt.erase (consAtL {1} zero zero zero) refl

_ : Formula (⊥* {ℓ-suc ℓ}) 3
_ = Cnt.erase (consAtL {3} zero (suc zero) (suc (suc zero))) refl

-- The real quantifier-clause bodies are constant-free.
_ : countFo (body∃ {1} zero) ≡ 0
_ = refl

_ : countFo (body∀ {1} zero) ≡ 0
_ = refl

-- The real clause forms keep constants from OTHER readers, not from
-- consAtL: the arity tag `# k` via arityTagPairAtL, and the term-value
-- tags `# 0` / `# 1` via tmValAt.
_ : countFo (existClauseAt {1} zero zero zero) ≡ 1
_ = refl

_ : countFo (forallClauseAt {1} zero zero zero) ≡ 1
_ = refl

_ : countFo (allInClauseAt {1} zero zero zero) ≡ 5
_ = refl

_ : countFo (exInClauseAt {1} zero zero zero) ≡ 5
_ = refl

Cs : Vec S 5
Cs = constantsFo (allInClauseAt {1} zero zero zero)

_ : lookup zero Cs ≡ numeralL 10
_ = refl

_ : lookup (suc zero) Cs ≡ numeralL 1
_ = refl

_ : lookup (suc (suc zero)) Cs ≡ numeralL 0
_ = refl

_ : lookup (suc (suc (suc zero))) Cs ≡ numeralL 1
_ = refl

_ : lookup (suc (suc (suc (suc zero)))) Cs ≡ numeralL 0
_ = refl

-- The residue readers, measured: the term-value tags and the arity tag
-- carry the constants; the environment-over shape readers carry none.
_ : countFo (tmValAt {1} zero zero zero) ≡ 2
_ = refl

_ : countFo (tmValAt {10} (suc (suc (suc (suc (suc (suc zero))))))
                         (suc zero) zero) ≡ 2
_ = refl

_ : countFo (arityTagPairAtL {1} zero zero 10 zero zero) ≡ 1
_ = refl

_ : countFo (tagPairAtL {1} zero 10 zero zero) ≡ 1
_ = refl

_ : countFo (tagAtL {1} zero 10 zero) ≡ 1
_ = refl

_ : countFo (subValSuccAt {1} zero zero zero zero) ≡ 0
_ = refl

_ : countFo (envSetAt {1} zero zero zero) ≡ 0
_ = refl

_ : countFo (envOverAt {1} zero zero zero) ≡ 0
_ = refl

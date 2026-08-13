{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.32] D-10: re-verify the delivered clause counts against the tree
-- as it stands, before building the ladder.  The [LJ-1.31] counts are
-- residue hours old.  Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth

module ProbeLJ132Counts {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Manipulation.Parameters using ( countFo; constantsFo )
open import FOL.Syntax using ( Formula; ⊥̇; _∧̇_ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Model {ℓ}
  using ( consAtL; existClauseAt; forallClauseAt; allInClauseAt; exInClauseAt
        ; body∃; body∀; bodyAll; bodyEx; tmValAt; tagAtL; arityTagAtL
        ; arityTagPairAtL; subValSuccAt; envSetAt; envOverAt; extAt; appAt
        ; prAtL; bndRel; binClauseAt; quantRel; unClauseAt )
open import Cubical.Data.Vec using ( Vec; _∷_; []; lookup )
open import Cubical.Data.FinData using ( Fin; zero; suc )

open hPropStructure 𝒮ʟ using ( S )

-- The reader itself: count zero at every arity (the [LJ-1.31] headline).
_ : countFo (consAtL {1} zero zero zero) ≡ 0
_ = refl

-- The delivered clause forms.
_ : countFo (existClauseAt {1} zero zero zero) ≡ 1
_ = refl

_ : countFo (forallClauseAt {1} zero zero zero) ≡ 1
_ = refl

-- The clause bodies.
_ : countFo (body∃ {1} zero) ≡ 0
_ = refl

_ : countFo (body∀ {1} zero) ≡ 0
_ = refl

_ : countFo (bodyAll {1} zero) ≡ 2
_ = refl

_ : countFo (bodyEx {1} zero) ≡ 2
_ = refl

-- The tag readers that carry the constants.
_ : countFo (tmValAt {1} zero zero zero) ≡ 2
_ = refl

CsTm : Vec S 2
CsTm = constantsFo (tmValAt {1} zero zero zero)

_ : lookup zero CsTm ≡ numeralL 1
_ = refl

_ : lookup (suc zero) CsTm ≡ numeralL 0
_ = refl

_ : countFo (tagAtL {1} zero 1 zero) ≡ 1
_ = refl

_ : countFo (tagAtL {2} (suc zero) 1 zero) ≡ 1
_ = refl

_ : countFo (appAt {2} (suc zero) zero (suc zero)) ≡ 0
_ = refl

_ : countFo (prAtL {3} (suc (suc zero)) zero (suc zero)) ≡ 0
_ = refl

_ : countFo (arityTagAtL {1} zero zero 8 zero) ≡ 1
_ = refl

_ : countFo (arityTagPairAtL {1} zero zero 11 zero zero) ≡ 1
_ = refl

_ : countFo (appAt {1} zero zero zero) ≡ 0
_ = refl

_ : countFo (prAtL {1} zero zero zero) ≡ 0
_ = refl

_ : countFo (subValSuccAt {1} zero zero zero zero) ≡ 0
_ = refl

_ : countFo (envSetAt {1} zero zero zero) ≡ 0
_ = refl

_ : countFo (envOverAt {1} zero zero zero) ≡ 0
_ = refl

_ : countFo (extAt {8} zero ⊥̇) ≡ 0
_ = refl

-- The worst case.
_ : countFo (allInClauseAt {1} zero zero zero) ≡ 5
_ = refl

_ : countFo (exInClauseAt {1} zero zero zero) ≡ 5
_ = refl

_ : countFo (subValSuccAt {8} (suc (suc (suc (suc (suc (suc (suc zero)))))))
                            (suc (suc (suc (suc (suc zero)))))
                            (suc (suc (suc zero))) (suc zero)) ≡ 0
_ = refl

_ : countFo (envSetAt {8} zero (suc (suc (suc (suc (suc zero)))))
                      (suc (suc (suc (suc (suc (suc (suc zero)))))))) ≡ 0
_ = refl

_ : countFo (extAt {8} (suc (suc zero)) (bodyEx {1} zero)) ≡ 4
_ = refl

_ : countFo (bndRel {1} zero zero (bodyEx {1} zero)) ≡ 4
_ = refl

_ : countFo (binClauseAt {1} zero zero 11 (bndRel {1} zero zero (bodyEx {1} zero))) ≡ 5
_ = refl

-- What the five constants are, in occurrence order, for exInClauseAt.
Cs : Vec S 5
Cs = constantsFo (exInClauseAt {1} zero zero zero)

_ : lookup zero Cs ≡ numeralL 11
_ = refl

_ : lookup (suc zero) Cs ≡ numeralL 1
_ = refl

_ : lookup (suc (suc zero)) Cs ≡ numeralL 0
_ = refl

_ : lookup (suc (suc (suc zero))) Cs ≡ numeralL 1
_ = refl

_ : lookup (suc (suc (suc (suc zero)))) Cs ≡ numeralL 0
_ = refl

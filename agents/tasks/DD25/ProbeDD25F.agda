{-# OPTIONS --cubical --safe --guardedness #-}
open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
module ProbeDD25F {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Parameters using ( countFo )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL )
open import FOL.ZFStructure using ( module hPropStructure )
open import L.Coding.Model {ℓ} using ( prAtL; appAt; consAtL; sucAtL; tagAtL )
open hPropStructure 𝒮ʟ

_ : countFo {K = S} (prAtL {1} zero zero zero) ≡ 0
_ = refl
_ : countFo {K = S} (appAt {1} zero zero zero) ≡ 0
_ = refl
_ : countFo {K = S} (consAtL {1} zero zero zero) ≡ 16
_ = refl
_ : countFo {K = S} (sucAtL {1} zero zero) ≡ 0
_ = refl
_ : countFo {K = S} (tagAtL {1} zero zero zero) ≡ 1
_ = refl

{-# OPTIONS --cubical --safe --guardedness #-}
module RelationalSmallFunctionAudit where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary using (¬_)
open import ModalTrees using (NN; mapNN)
open import StableRelations
open import RelationalOmega using (Boolean)
open import RelationalLargeFunctions using (product; Functions)
open import RelationalFunctionBoundary using (Natural; SmallHomPresentation;
  hom-presentation-not-subcountable)
open import SubcountableObstruction using (Subcountable; ModalAllSmallSubcountable)

open Object
open Map
open Isomorphism

module _ {e : Level} (E : Object ℓ-zero e)
  (ev : Map (product E Natural) Boolean ℓ-zero) where
  evaluation-row : Carrier E → Map Natural Boolean ℓ-zero
  graph (evaluation-row i) n b = graph ev (i , n) b
  graph-prop (evaluation-row i) n b = graph-prop ev (i , n) b
  graph-stable (evaluation-row i) n b = graph-stable ev (i , n) b
  respect (evaluation-row i) n n' b b' nn' bb' =
    respect ev (i , n) (i , n') b b' (equal-refl E i , nn') bb'
  total (evaluation-row i) n = total ev (i , n)
  unique (evaluation-row i) n = unique ev (i , n)

  module _ {r s : Level} (iso : Isomorphism E (Functions Natural Boolean) r s)
    (compatible : (i : Carrier E) (F : Map Natural Boolean ℓ-zero)
      → graph (forward iso) i F → MapEq (evaluation-row i) F) where

    small-hom-presentation : SmallHomPresentation
    SmallHomPresentation.Index small-hom-presentation = Carrier E
    SmallHomPresentation.family small-hom-presentation = evaluation-row
    SmallHomPresentation.covers small-hom-presentation F = mapNN
      (λ { (i , back , forth) → i , λ n b →
        compatible i F forth n b .snd , compatible i F forth n b .fst })
      (forward-backward iso F F .snd (map-eq-refl F))

    carrier-not-subcountable : ¬ Subcountable (Carrier E)
    carrier-not-subcountable = hom-presentation-not-subcountable small-hom-presentation

    modal-subcountability-obstruction : ¬ ModalAllSmallSubcountable
    modal-subcountability-obstruction sc = sc (Carrier E) carrier-not-subcountable

{-# OPTIONS --cubical --safe --guardedness #-}
module DeepFOLOmegaTrees where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Vec using ([])
open import FOL.Syntax using (Formula)
import ModalTrees as Trees
open Trees using (NN; unitNN; mapNN)
open import ConditionalImage using (T; emptyT; singleton; emptyT-out; singleton-in; singleton-out)
open import DeepNegativeFOL
open import DeepFOLOmega

tree-atoms : Atoms (ℓ-suc ℓ-zero)
Atoms.S tree-atoms = T
Atoms.Eq tree-atoms x y = Lift (Trees.Eq x y)
Atoms.Mem tree-atoms x y = Lift (Trees.Mem x y)
Atoms.eq-prop tree-atoms x y = isOfHLevelLift 1 (Trees.eq-prop x y)
Atoms.mem-prop tree-atoms x y = isOfHLevelLift 1 (Trees.mem-prop x y)
Atoms.eq-stable tree-atoms x y n = lift (Trees.eq-stable x y (mapNN lower n))
Atoms.mem-stable tree-atoms x y n = lift (Trees.mem-stable x y (mapNN lower n))

open Interpret tree-atoms
open Construction tree-atoms

unitT : T
unitT = singleton emptyT

truth-entry : Bool → T
truth-entry false = emptyT
truth-entry true = unitT

omegaT : T
omegaT = Trees.sup Bool truth-entry

tree-elementary-sets : ElementarySets
ElementarySets.e tree-elementary-sets = emptyT
ElementarySets.u tree-elementary-sets = unitT
ElementarySets.o tree-elementary-sets = omegaT
ElementarySets.empty-law tree-elementary-sets x m = lift (emptyT-out x (lower m))
ElementarySets.singleton-law tree-elementary-sets x =
  (λ m → lift (singleton-out emptyT x (lower m))) ,
  (λ e → lift (singleton-in emptyT x (lower e)))
ElementarySets.pair-law tree-elementary-sets x =
  (λ m → mapNN (λ { (false , e) → inl (lift e) ; (true , e) → inr (lift e) }) (lower m)) ,
  (λ n → lift (mapNN (λ { (inl e) → false , lower e ; (inr e) → true , lower e }) n))
ElementarySets.reflexive tree-elementary-sets x = lift (Trees.eq-refl x)
ElementarySets.symmetric tree-elementary-sets x y e = lift (Trees.eq-sym x y (lower e))
ElementarySets.member-left tree-elementary-sets x y a e m =
  lift (Trees.mem-left x y a (lower e) (lower m))
ElementarySets.member-right tree-elementary-sets x a b e m =
  lift (Trees.mem-right x a b (lower e) (lower m))
ElementarySets.extensional tree-elementary-sets a b f = lift (Trees.extensionality a b λ x →
  (λ m → lower (f x .fst (lift m))) , (λ m → lower (f x .snd (lift m))))

module FromDeepLEM (classical : FormulaLEM) where
  open Derived tree-elementary-sets classical public

module Unconditional = FromDeepLEM negative-formula-lem

deep-omega : Sat Unconditional.OmegaFormula []
deep-omega = Unconditional.omega-classifies-subsets-of-singleton

deep-formula-resizing : ∀ {n} (φ : Formula T n) γ
  → Sat (Unconditional.RepresentFormula φ) γ
deep-formula-resizing = Unconditional.formula-resizing

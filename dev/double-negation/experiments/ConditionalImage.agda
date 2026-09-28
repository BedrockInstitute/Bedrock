{-# OPTIONS --cubical --safe --guardedness #-}
module ConditionalImage where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)
open import ModalTrees
open import BooleanPower using (pointwise-decision)
open import SeparationBoundary using (SeparationWitness)
open import SupportedImage using (ImageWitness)

T : Type₁
T = Tree ℓ-zero

emptyT : T
emptyT = sup ⊥ Empty.rec

singleton : T → T
singleton x = sup Unit (λ _ → x)

emptyT-out : (x : T) → Mem x emptyT → ⊥
emptyT-out x m = m (λ z → z .fst)

singleton-in : (x y : T) → Eq y x → Mem y (singleton x)
singleton-in x y e = unitNN (tt , e)

singleton-out : (x y : T) → Mem y (singleton x) → Eq y x
singleton-out x y m = eq-stable y x (mapNN snd m)

Dom : T → Type
Dom (sup A _) = A

elts : (a : T) → Dom a → T
elts (sup _ f) = f

union : T → T
union (sup A f) = sup (Σ[ i ∈ A ] Dom (f i)) (λ ij → elts (f (ij .fst)) (ij .snd))

union-out : (a y : T) → Mem y (union a) → NN (Σ[ z ∈ T ] (Mem z a × Mem y z))
union-out (sup A f) y = mapNN (λ { ((i , j) , e) →
  f i , unitNN (i , eq-refl (f i)) , member (f i) j e })
  where
  member : (z : T) (j : Dom z) → Eq y (elts z j) → Mem y z
  member (sup B g) j e = unitNN (j , e)

union-in : (a y z : T) → Mem z a → Mem y z → Mem y (union a)
union-in (sup A f) y z mz my = bindNN mz λ { (i , e) →
  mapNN (λ { (j , q) → (i , j) , q })
    (flatten (f i) (mem-right y z (f i) e my)) }
  where
  flatten : (b : T) → Mem y b → NN (Σ[ j ∈ Dom b ] Eq y (elts b j))
  flatten (sup B g) m = m

module _ {ℓ : Level} (P : T → Type ℓ)
  (stable : (x : T) → NN (P x) → P x)
  (extP : (x y : T) → Eq x y → P x → P y)
  {A : Type} (f : A → T) where

  R : A → T → Type ℓ
  R i y = NN ((P (f i) × Eq y (singleton (f i))) ⊎ ((¬ P (f i)) × Eq y emptyT))

  extR : (i : A) (y z : T) → Eq y z → R i y → R i z
  extR i y z e = mapNN λ where
    (inl (p , q)) → inl (p , eq-trans z y (singleton (f i)) (eq-sym y z e) q)
    (inr (np , q)) → inr (np , eq-trans z y emptyT (eq-sym y z e) q)

  uniqueR : (i : A) (y z : T) → R i y → R i z → Eq y z
  uniqueR i y z ry rz = eq-stable y z (bindNN ry λ v → mapNN (compare v) rz)
    where
    compare : ((P (f i) × Eq y (singleton (f i))) ⊎ ((¬ P (f i)) × Eq y emptyT))
      → ((P (f i) × Eq z (singleton (f i))) ⊎ ((¬ P (f i)) × Eq z emptyT)) → Eq y z
    compare (inl (p , e)) (inl (_ , d)) =
      eq-trans y (singleton (f i)) z e (eq-sym z (singleton (f i)) d)
    compare (inl (p , _)) (inr (np , _)) = Empty.rec (np p)
    compare (inr (np , _)) (inl (p , _)) = Empty.rec (np p)
    compare (inr (_ , e)) (inr (_ , d)) = eq-trans y emptyT z e (eq-sym z emptyT d)

  totalR : (i : A) → NN (Σ[ y ∈ T ] R i y)
  totalR i = mapNN choose (pointwise-decision (P (f i)))
    where
    choose : Dec (P (f i)) → Σ[ y ∈ T ] R i y
    choose (yes p) = singleton (f i) , unitNN (inl (p , eq-refl (singleton (f i))))
    choose (no np) = emptyT , unitNN (inr (np , eq-refl emptyT))

  candidate : A ⊎ Unit → T
  candidate (inl i) = singleton (f i)
  candidate (inr _) = emptyT

  bound : T
  bound = sup (A ⊎ Unit) candidate

  boundedR : (i : A) (y : T) → R i y → Mem y bound
  boundedR i y = mapNN λ where
    (inl (_ , e)) → inl i , e
    (inr (_ , e)) → inr tt , e

  image-to-separation : ImageWitness R extR uniqueR → SeparationWitness P f
  image-to-separation (b , spec) = union b , λ x →
    (λ m → let pair = bindNN (union-out b x m) λ { (y , myb , mxy) →
                  bindNN (spec y .fst myb) λ { (i , r) → mapNN (recover x i y mxy) r } }
           in mem-stable x (sup A f) (mapNN fst pair) , stable x (mapNN snd pair)) ,
    (λ { (m , px) → mem-stable x (union b) (mapNN (λ { (i , e) →
      union-in b x (singleton (f i))
        (spec (singleton (f i)) .snd (unitNN (i , unitNN
          (inl (extP x (f i) e px , eq-refl (singleton (f i)))))))
        (singleton-in (f i) x e) }) m) })
    where
    recover : (x : T) (i : A) (y : T) → Mem x y
      → ((P (f i) × Eq y (singleton (f i))) ⊎ ((¬ P (f i)) × Eq y emptyT))
      → Mem x (sup A f) × P x
    recover x i y m (inl (p , e)) =
      let q = singleton-out (f i) x (mem-right x y (singleton (f i)) e m)
      in unitNN (i , q) , extP (f i) x (eq-sym x (f i) q) p
    recover x i y m (inr (_ , e)) = Empty.rec (emptyT-out x (mem-right x y emptyT e m))

  modal-image-to-separation : NN (ImageWitness R extR uniqueR) → NN (SeparationWitness P f)
  modal-image-to-separation = mapNN image-to-separation

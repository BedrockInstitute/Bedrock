{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.FinitePower
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮)
  (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  (seed X : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _⇒̇_; ¬̇_; ∀̇_; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import Base.Classical using ( LEM )
open import CodedVocabulary 𝒮
  using ( subsetΔ; subsetAtˢ; sepAt; sepAt-reading )
open import CardinalBridge 𝒮 using ( _↔̇_ )
open import OrdinaryProfile 𝒮 using ( iff )
open import K8.FiniteVocabulary 𝒮
  using ( finiteIn; finiteAt; emptyPred; adjoinPred; adjoinAt )
open import K8.FiniteSets 𝒮 ext paths pow sep
  using ( finite-empty; finite-adjoin; finite-induction )
open import K8.FiniteOperations 𝒮 ext paths pair un pow sep seed
  using ( insert; insert-witness; finite-join )
open import K8.FiniteSubsets 𝒮 ext paths pow sep using ( finite-subset )
import K8.GroundSets
module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
open import GroundDescription 𝒮 ext paths using ( ext-path )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sum using ( _⊎_ ) renaming ( inl to inl⊎; inr to inr⊎ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

liftPred : S → S → S → Ω
liftPred A x c = ⋁ S (λ d → (d ∈ˢ A) ⊓ adjoinPred c d x)

liftAt : Formula S 3
liftAt = ∃̇∈ (var (suc zero))
  (adjoinAt (suc zero) zero (suc (suc (suc zero))))

liftFormula : S → S → Formula S 1
liftFormula A x = sepAt liftAt (A ∷ x ∷ [])

liftFormula-reading : (A x c : S)
  → ((c ∷ []) ⊨ liftFormula A x) ≡ liftPred A x c
liftFormula-reading A x c = sepAt-reading liftAt (A ∷ x ∷ []) c

opaque
  liftSet : S → S → S
  liftSet A x = GS.separator (GS.power X) (liftFormula A x)

  liftSet-spec : (A x c : S)
    → (c ∈ˢ liftSet A x) ≡ ((c ∈ˢ GS.power X) ⊓ liftPred A x c)
  liftSet-spec A x c = GS.separator-spec (GS.power X) (liftFormula A x) c
    ∙ cong ((c ∈ˢ GS.power X) ⊓_) (liftFormula-reading A x c)

adjoin-unique : (b c a x : S) → ⟨ adjoinPred b a x ⟩
  → ⟨ adjoinPred c a x ⟩ → b ≡ c
adjoin-unique b c a x hb hc = ext-path spec
  where
  spec : (z : S) → (z ∈ˢ b) ≡ (z ∈ˢ c)
  spec z = ⇔toPath forward backward
    where
    step-forward : ⟨ z ∈ˢ a ⟩ ⊎ ⟨ z ≈ˢ x ⟩ → ⟨ z ∈ˢ c ⟩
    step-forward (inl⊎ za) = fst (snd hc) z za
    step-forward (inr⊎ zx) = subst (λ q → ⟨ q ∈ˢ c ⟩)
      (sym (GS.≈→≡ zx)) (fst hc)

    step-backward : ⟨ z ∈ˢ a ⟩ ⊎ ⟨ z ≈ˢ x ⟩ → ⟨ z ∈ˢ b ⟩
    step-backward (inl⊎ za) = fst (snd hb) z za
    step-backward (inr⊎ zx) = subst (λ q → ⟨ q ∈ˢ b ⟩)
      (sym (GS.≈→≡ zx)) (fst hb)

    forward : ⟨ z ∈ˢ b ⟩ → ⟨ z ∈ˢ c ⟩
    forward hz = PT.rec (snd (z ∈ˢ c)) step-forward (snd (snd hb) z hz)

    backward : ⟨ z ∈ˢ c ⟩ → ⟨ z ∈ˢ b ⟩
    backward hz = PT.rec (snd (z ∈ˢ b)) step-backward (snd (snd hc) z hz)

lift-in : (A x d : S) → ⟨ d ∈ˢ A ⟩ → ⟨ d ∈ˢ GS.power X ⟩
  → ⟨ x ∈ˢ X ⟩ → ⟨ insert d x ∈ˢ liftSet A x ⟩
lift-in A x d hd dsub hx = subst ⟨_⟩ (sym (liftSet-spec A x (insert d x)))
  (insert-sub , ∣ d , hd , insert-witness d x ∣₁)
  where
  insert-sub : ⟨ insert d x ∈ˢ GS.power X ⟩
  insert-sub = subst ⟨_⟩ (sym (GS.power-spec X (insert d x))) λ z hz →
    PT.rec (snd (z ∈ˢ X))
      (λ { (inl⊎ zd) → subst ⟨_⟩ (GS.power-spec X d) dsub z zd
         ; (inr⊎ zx) → subst (λ q → ⟨ q ∈ˢ X ⟩) (sym (GS.≈→≡ zx)) hx })
      (snd (snd (insert-witness d x)) z hz)

lift-adjoin : (B A d x : S) → ⟨ adjoinPred B A d ⟩
  → ⟨ d ∈ˢ GS.power X ⟩ → ⟨ x ∈ˢ X ⟩
  → ⟨ adjoinPred (liftSet B x) (liftSet A x) (insert d x) ⟩
lift-adjoin B A d x hB hd hx = lift-in B x d (fst hB) hd hx , sub , all
  where
  sub : ⟨ subsetΔ (liftSet A x) (liftSet B x) ⟩
  sub c hc = subst ⟨_⟩ (sym (liftSet-spec B x c))
    (fst dataA , PT.map (λ { (e , he , ce) → e , fst (snd hB) e he , ce }) (snd dataA))
    where
    dataA : ⟨ (c ∈ˢ GS.power X) ⊓ liftPred A x c ⟩
    dataA = subst ⟨_⟩ (liftSet-spec A x c) hc

  all : (c : S) → ⟨ c ∈ˢ liftSet B x ⟩
    → ⟨ (c ∈ˢ liftSet A x) ⊔ (c ≈ˢ insert d x) ⟩
  all c hc = PT.rec (snd ((c ∈ˢ liftSet A x) ⊔ (c ≈ˢ insert d x))) atPreimage
    (snd dataB)
    where
    dataB : ⟨ (c ∈ˢ GS.power X) ⊓ liftPred B x c ⟩
    dataB = subst ⟨_⟩ (liftSet-spec B x c) hc

    atPreimage : Σ[ e ∈ S ] (⟨ e ∈ˢ B ⟩ × ⟨ adjoinPred c e x ⟩)
      → ⟨ (c ∈ˢ liftSet A x) ⊔ (c ≈ˢ insert d x) ⟩
    atPreimage (e , he , ce) = PT.rec
      (snd ((c ∈ˢ liftSet A x) ⊔ (c ≈ˢ insert d x))) branch
      (snd (snd hB) e he)
      where
      branch : ⟨ e ∈ˢ A ⟩ ⊎ ⟨ e ≈ˢ d ⟩
        → ⟨ (c ∈ˢ liftSet A x) ⊔ (c ≈ˢ insert d x) ⟩
      branch (inl⊎ ea) = ∣ inl⊎ (subst ⟨_⟩ (sym (liftSet-spec A x c))
        (fst dataB , ∣ e , ea , ce ∣₁)) ∣₁
      branch (inr⊎ ed) = ∣ inr⊎
        (subst ⟨_⟩ (sym (paths c (insert d x)))
          (adjoin-unique c (insert d x) d x
            (subst (λ q → ⟨ adjoinPred c q x ⟩) (GS.≈→≡ ed) ce)
            (insert-witness d x))) ∣₁

liftSpec : S → S → S → Ω
liftSpec L A x = ⋀ S (λ c → iff (c ∈ˢ L)
  ((c ∈ˢ GS.power X) ⊓ liftPred A x c))

liftSpecAt : Formula S 5
liftSpecAt = ∀̇ ((var zero ∈̇ var (suc zero)) ↔̇
  ((var zero ∈̇ var (suc (suc (suc (suc (suc zero)))))) ∧̇
   (∃̇∈ (var (suc (suc zero)))
     (adjoinAt (suc zero) zero (suc (suc (suc (suc zero))))))))

liftFiniteAt : Formula S 4
liftFiniteAt = ∀̇ (liftSpecAt ⇒̇ finiteAt (suc (suc (suc (suc zero)))) zero)

liftFiniteFormula : S → Formula S 1
liftFiniteFormula x = sepAt liftFiniteAt (x ∷ X ∷ GS.power X ∷ [])

liftFinite-reading : (A x : S) → ((A ∷ []) ⊨ liftFiniteFormula x)
  ≡ ⋀ S (λ L → liftSpec L A x ⇒ finiteIn (GS.power X) L)
liftFinite-reading A x = sepAt-reading liftFiniteAt (x ∷ X ∷ GS.power X ∷ []) A

lift-witness : (A x : S) → ⟨ liftSpec (liftSet A x) A x ⟩
lift-witness A x c = subst ⟨_⟩ (liftSet-spec A x c)
  , subst ⟨_⟩ (sym (liftSet-spec A x c))

lift-unique : (L A x : S) → ⟨ liftSpec L A x ⟩ → L ≡ liftSet A x
lift-unique L A x h = ext-path λ c →
  ⇔toPath (fst (h c)) (snd (h c)) ∙ sym (liftSet-spec A x c)

finite-lift : (A x : S) → ⟨ finiteIn (GS.power X) A ⟩ → ⟨ x ∈ˢ X ⟩
  → ⟨ finiteIn (GS.power X) (liftSet A x) ⟩
finite-lift A x hA hx = subst ⟨_⟩ (liftFinite-reading A x)
  (finite-induction (GS.power X) (liftFiniteFormula x) base step A hA)
  (liftSet A x) (lift-witness A x)
  where
  base : (e : S) → ⟨ emptyPred e ⟩ → ⟨ (e ∷ []) ⊨ liftFiniteFormula x ⟩
  base e he = subst ⟨_⟩ (sym (liftFinite-reading e x)) λ L hL →
    finite-empty (GS.power X) L λ c hc → PT.rec (snd ⊥)
      (λ { (d , hd , _) → he d hd }) (snd (fst (hL c) hc))

  step : (A' B d : S) → ⟨ finiteIn (GS.power X) A' ⟩
    → ⟨ (A' ∷ []) ⊨ liftFiniteFormula x ⟩
    → ⟨ d ∈ˢ GS.power X ⟩ → ⟨ adjoinPred B A' d ⟩
    → ⟨ (B ∷ []) ⊨ liftFiniteFormula x ⟩
  step A' B d hA' ih hd hB = subst ⟨_⟩ (sym (liftFinite-reading B x)) λ L hL →
    subst (λ q → ⟨ finiteIn (GS.power X) q ⟩) (sym (lift-unique L B x hL))
      (finite-adjoin (GS.power X) (liftSet B x) (liftSet A' x) (insert d x)
        (subst ⟨_⟩ (liftFinite-reading A' x) ih (liftSet A' x) (lift-witness A' x))
        (fst (subst ⟨_⟩ (liftSet-spec B x (insert d x))
          (lift-in B x d (fst hB) hd hx)))
        (lift-adjoin B A' d x hB hd hx))

powerSpec : S → S → Ω
powerSpec p a = ⋀ S (λ c → iff (c ∈ˢ p) (subsetΔ c a))

powerSpecAt : Formula S 2
powerSpecAt = ∀̇ ((var zero ∈̇ var (suc zero)) ↔̇
  subsetAtˢ zero (suc (suc zero)))

powerFiniteAt : Formula S 3
powerFiniteAt = ∀̇
  ((∀̇ ((var zero ∈̇ var (suc zero)) ↔̇
    subsetAtˢ zero (suc (suc zero))))
   ⇒̇ finiteAt (suc (suc (suc zero))) zero)

powerFiniteFormula : Formula S 1
powerFiniteFormula = sepAt powerFiniteAt (X ∷ GS.power X ∷ [])

powerFinite-reading : (a : S) → ((a ∷ []) ⊨ powerFiniteFormula)
  ≡ ⋀ S (λ p → powerSpec p a ⇒ finiteIn (GS.power X) p)
powerFinite-reading a = sepAt-reading powerFiniteAt (X ∷ GS.power X ∷ []) a

power-witness : (a : S) → ⟨ powerSpec (GS.power a) a ⟩
power-witness a c = subst ⟨_⟩ (GS.power-spec a c)
  , subst ⟨_⟩ (sym (GS.power-spec a c))

power-unique : (p a : S) → ⟨ powerSpec p a ⟩ → p ≡ GS.power a
power-unique p a h = ext-path λ c →
  ⇔toPath (fst (h c)) (snd (h c)) ∙ sym (GS.power-spec a c)

powerset-finite : LEM ℓ → (a : S) → ⟨ finiteIn X a ⟩
  → ⟨ finiteIn (GS.power X) (GS.power a) ⟩
powerset-finite lem a ha = subst ⟨_⟩ (powerFinite-reading a)
  (finite-induction X powerFiniteFormula base step a ha)
  (GS.power a) (power-witness a)
  where
  base : (e : S) → ⟨ emptyPred e ⟩ → ⟨ (e ∷ []) ⊨ powerFiniteFormula ⟩
  base e he = subst ⟨_⟩ (sym (powerFinite-reading e)) λ p hp →
    finite-adjoin (GS.power X) p GS.empty GS.empty
      (finite-empty (GS.power X) GS.empty GS.empty-out)
      empty-subset-X (empty-adjoin p hp)
    where
    empty-subset-X : ⟨ GS.empty ∈ˢ GS.power X ⟩
    empty-subset-X = subst ⟨_⟩ (sym (GS.power-spec X GS.empty))
      (λ z hz → Empty.rec* (GS.empty-out z hz))

    empty-adjoin : (p : S) → ⟨ powerSpec p e ⟩
      → ⟨ adjoinPred p GS.empty GS.empty ⟩
    empty-adjoin p hp = inP , emptySub , all
      where
      inP : ⟨ GS.empty ∈ˢ p ⟩
      inP = snd (hp GS.empty) (λ z hz → Empty.rec* (GS.empty-out z hz))
      emptySub : ⟨ subsetΔ GS.empty p ⟩
      emptySub z hz = Empty.rec* (GS.empty-out z hz)
      all : (c : S) → ⟨ c ∈ˢ p ⟩
        → ⟨ (c ∈ˢ GS.empty) ⊔ (c ≈ˢ GS.empty) ⟩
      all c hc = ∣ inr⊎
        (subst ⟨_⟩ (sym (paths c GS.empty)) (p-empty c hc)) ∣₁
        where
        p-empty : (c : S) → ⟨ c ∈ˢ p ⟩ → c ≡ GS.empty
        p-empty c hc = ext-path λ z → ⇔toPath
          (λ hz → Empty.rec* (he z (fst (hp c) hc z hz)))
          (λ hz → Empty.rec* (GS.empty-out z hz))

  step : (a' b x : S) → ⟨ finiteIn X a' ⟩
    → ⟨ (a' ∷ []) ⊨ powerFiniteFormula ⟩
    → ⟨ x ∈ˢ X ⟩ → ⟨ adjoinPred b a' x ⟩
    → ⟨ (b ∷ []) ⊨ powerFiniteFormula ⟩
  step a' b x ha' ih hx hb = subst ⟨_⟩ (sym (powerFinite-reading b)) λ p hp →
    subst (λ q → ⟨ finiteIn (GS.power X) q ⟩) (sym (power-unique p b hp))
      (finite-subset lem (GS.power X) cover (GS.power b) coverFinite powerBelow)
    where
    paFinite : ⟨ finiteIn (GS.power X) (GS.power a') ⟩
    paFinite = subst ⟨_⟩ (powerFinite-reading a') ih
      (GS.power a') (power-witness a')

    liftedFinite : ⟨ finiteIn (GS.power X) (liftSet (GS.power a') x) ⟩
    liftedFinite = finite-lift (GS.power a') x paFinite hx

    cover : S
    cover = GS.join (GS.power a') (liftSet (GS.power a') x)

    coverFinite : ⟨ finiteIn (GS.power X) cover ⟩
    coverFinite = finite-join (GS.power X) (GS.power a')
      (liftSet (GS.power a') x) paFinite liftedFinite

    bSubX : ⟨ subsetΔ b X ⟩
    bSubX z hz = PT.rec (snd (z ∈ˢ X))
      (λ { (inl⊎ za) → fst ha' z za
         ; (inr⊎ zx) → subst (λ q → ⟨ q ∈ˢ X ⟩) (sym (GS.≈→≡ zx)) hx })
      (snd (snd hb) z hz)

    powerBelow : ⟨ subsetΔ (GS.power b) cover ⟩
    powerBelow c hc = choose (lem (x ∈ˢ c))
      where
      cSubB : ⟨ subsetΔ c b ⟩
      cSubB = subst ⟨_⟩ (GS.power-spec b c) hc

      cInPX : ⟨ c ∈ˢ GS.power X ⟩
      cInPX = subst ⟨_⟩ (sym (GS.power-spec X c)) λ z hz → bSubX z (cSubB z hz)

      left : (⟨ x ∈ˢ c ⟩ → Empty.⊥) → ⟨ c ∈ˢ cover ⟩
      left notx = subst ⟨_⟩ (sym (GS.join-spec (GS.power a')
        (liftSet (GS.power a') x) c)) ∣ inl⊎
          (subst ⟨_⟩ (sym (GS.power-spec a' c)) (λ z hz →
            PT.rec (snd (z ∈ˢ a'))
              (λ { (inl⊎ za) → za
                 ; (inr⊎ zx) → Empty.rec (notx
                     (subst (λ q → ⟨ q ∈ˢ c ⟩) (GS.≈→≡ zx) hz)) })
              (snd (snd hb) z (cSubB z hz)))) ∣₁

      opaque
        cut : S
        cut = GS.separator c (¬̇ (var zero ≐ con x))

        cut-spec : (z : S) → (z ∈ˢ cut) ≡ ((z ∈ˢ c) ⊓ ((z ≈ˢ x) ⇒ ⊥))
        cut-spec z = GS.separator-spec c (¬̇ (var zero ≐ con x)) z

      right : ⟨ x ∈ˢ c ⟩ → ⟨ c ∈ˢ cover ⟩
      right xin = subst ⟨_⟩ (sym (GS.join-spec (GS.power a')
        (liftSet (GS.power a') x) c)) ∣ inr⊎
          (subst ⟨_⟩ (sym (liftSet-spec (GS.power a') x c))
            (cInPX , ∣ cut , cutInPa , cutAdjoin ∣₁)) ∣₁
        where
        cutInPa : ⟨ cut ∈ˢ GS.power a' ⟩
        cutInPa = subst ⟨_⟩ (sym (GS.power-spec a' cut)) λ z hz →
          PT.rec (snd (z ∈ˢ a'))
            (λ { (inl⊎ za) → za
               ; (inr⊎ zx) → Empty.rec* (snd (subst ⟨_⟩ (cut-spec z) hz) zx) })
            (snd (snd hb) z (cSubB z (fst (subst ⟨_⟩ (cut-spec z) hz))))

        cutAdjoin : ⟨ adjoinPred c cut x ⟩
        cutAdjoin = xin , (λ z hz → fst (subst ⟨_⟩ (cut-spec z) hz)) , all
          where
          all : (z : S) → ⟨ z ∈ˢ c ⟩ → ⟨ (z ∈ˢ cut) ⊔ (z ≈ˢ x) ⟩
          all z hz = decide (lem (z ≈ˢ x))
            where
            decide : ⟨ z ≈ˢ x ⟩ ⊎ (⟨ z ≈ˢ x ⟩ → Empty.⊥)
              → ⟨ (z ∈ˢ cut) ⊔ (z ≈ˢ x) ⟩
            decide (inl⊎ eq) = ∣ inr⊎ eq ∣₁
            decide (inr⊎ ne) = ∣ inl⊎
              (subst ⟨_⟩ (sym (cut-spec z))
                (hz , λ eq → Empty.rec (ne eq))) ∣₁

      choose : ⟨ x ∈ˢ c ⟩ ⊎ (⟨ x ∈ˢ c ⟩ → Empty.⊥) → ⟨ c ∈ˢ cover ⟩
      choose (inl⊎ xin) = right xin
      choose (inr⊎ notx) = left notx

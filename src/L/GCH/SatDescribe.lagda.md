# The satisfaction table, described in Δ₀

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.SatDescribe {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; Term; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇∈; ∀̇∈; ∃̇_; ∀̇_ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∧ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( consAtL )
open import L.Coding.EnvSet {ℓ} lem using ( envSet )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes; AllCodes-out; key∈AllCodes; keyS; codeS )
open import L.Coding.Uniform {ℓ} lem using ( module Table; val-at )
open import L.Coding.Pinned {ℓ} lem using ( module Match ) public
open import L.Coding.Sat {ℓ} lem using ( cond∈-in; cond∈-out; cond≐-in; cond≐-out )
open import L.Coding.EnvSet {ℓ} lem using ( envS )
open import L.GCH.SatFrame {ℓ} lem using
  ( sh; i0; i1; i2; i3; i4; i5; i6; i7; i8; f0; f1; f2; f3; f4; f5; f6; f7; f8; f9; f10; f11; Tags; nn; down; fstS; sndS
  ; tmIs; extB-out; extB-in; ExtFact; ext-unique
  ; towerAt; Δ₀-towerAt; codesAt; Δ₀-codesAt; tableAt; Δ₀-tableAt
  ; module Tower; module TowerRead; module TowerHolds
  ; module CodesSound; module CodesComplete; module CodesHolds
  ; module Frame; module Clause; module Rel; module RelRead
  ; module Alphabet; module Bridge; module SatGraph )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( _∷_; []; lookup )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Foundations.HLevels using ( isPropΣ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_; sucV )
open import Cubical.Data.FinData using ( toℕ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ)) using ()
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

THE TABLE IS SOUND.  A table satisfying the twelve clauses over the
code set and the tower records, at the key of every formula, the
value the meta-level recursion built there: induction on the
formula, one clause reader and one bridge per constructor.

```agda
module SatSound {m : ℕ} (T w C E : Fin m) (N : Fin 12 → Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) (tg : Tags γ N)
  (hE : ⟨ γ ⊨ towerAt E w (N f0) ⟩) (hC : ⟨ γ ⊨ codesAt C w E N ⟩)
  (hT : ⟨ γ ⊨ tableAt T w C E N ⟩) where
  open Alphabet W
  open Bridge W
  private
    Tv = fst (lookup T γ)
    Cv = fst (lookup C γ)
    Ev = fst (lookup E γ)
    Wv = fst W

    module TR = TowerRead E w (N f0) γ W qw (tg f0) hE
    arity : (n F : S) → ⟨ pr (fst n) (fst F) ∈ Ev ⟩ → ∥ Σ[ k ∈ ℕ ] (fst n ≡ # k) ∥₁
    arity n F q∈ = PT.map (λ { (k , (qk , _)) → k , qk }) (TR.entry-out n F q∈)
    module CS = CodesSound C w E N γ W qw tg arity (hC .fst)
    module CC = CodesComplete C w E N γ W qw tg TR.entry-in (hC .snd)
    module Fr = Frame T w C E N γ tg
    module Cl = Clause T w C E N
    module R = Rel T w N

    hTot = hT .fst
    hOn = hT .snd .fst
    h12 = hT .snd .snd

    cl : (k : Fin 12) → ⟨ γ ⊨ Cl.clause k ⟩
    cl zero = h12 .fst
    cl (suc zero) = h12 .snd .fst
    cl (suc (suc zero)) = h12 .snd .snd .fst
    cl (suc (suc (suc zero))) = h12 .snd .snd .snd .fst
    cl (suc (suc (suc (suc zero)))) = h12 .snd .snd .snd .snd .fst
    cl (suc (suc (suc (suc (suc zero))))) = h12 .snd .snd .snd .snd .snd .fst
    cl (suc (suc (suc (suc (suc (suc zero)))))) = h12 .snd .snd .snd .snd .snd .snd .fst
    cl (suc (suc (suc (suc (suc (suc (suc zero))))))) = h12 .snd .snd .snd .snd .snd .snd .snd .fst
    cl (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = h12 .snd .snd .snd .snd .snd .snd .snd .snd .fst
    cl (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = h12 .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst
    cl (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) = h12 .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst
    cl (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) = h12 .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd

    -- An entry at the key of a formula, and the frame it opens.
    module Case {n : ℕ} (ψ : Formula Ab n) (k : Fin 12) (rS : S)
      (ep : cd ψ ≡ pr (# (toℕ k)) (fst rS)) (y : S) (mem : ⟨ pr (fst (keyS W ψ)) (fst y) ∈ Tv ⟩) where
      q∈ : ⟨ pr (# n) (fst (envSet W n)) ∈ Ev ⟩
      q∈ = TR.entry-in n
      c∈ : ⟨ fst (keyS W ψ) ∈ Cv ⟩
      c∈ = CC.key-in ψ
      ep' : fst (codeS W ψ) ≡ pr (fst (lookup (N k) γ)) (fst rS)
      ep' = ep ∙ cong (λ a → pr a (fst rS)) (sym (tg k))
      δ12 : S ^ (12 + m)
      δ12 = Fr.At.δ12 (nn n) (envSet W n) (keyS W ψ) (codeS W ψ) rS y q∈ refl k ep' mem
      rel : ⟨ δ12 ⊨ R.relN (toℕ k) ⟩
      rel = Fr.clause-out k (cl k) (nn n) (envSet W n) (keyS W ψ) (codeS W ψ) rS y q∈ c∈ refl ep mem
      module RR = RelRead T w N δ12

    -- The value at a subformula's key, from totality.
    sub : ∀ {n} (a : Formula Ab n) → ∥ Σ[ ya ∈ S ] ⟨ pr (fst (keyS W a)) (fst ya) ∈ Tv ⟩ ∥₁
    sub a = Fr.total-out hTot (keyS W a) (CC.key-in a)

  Pinned : ∀ {n} (ψ : Formula Ab n) → Type (ℓ-suc ℓ)
  Pinned ψ = (y : S) → ⟨ pr (fst (keyS W ψ)) (fst y) ∈ Tv ⟩ → fst y ≡ fst (SatW ψ)

  private
    isPropPinned : ∀ {n} (ψ : Formula Ab n) → isProp (Pinned ψ)
    isPropPinned ψ f g = funExt (λ y → funExt (λ h → setIsSet _ _ (f y h) (g y h)))

    -- the payload of each constructor, as an element of L
    payS : ∀ {n} (ψ : Formula Ab n) (k : ℕ) (r : V ℓ) → cd ψ ≡ pr (# k) r → S
    payS ψ k r e = sndS (codeS W ψ) (# k) r e

    -- the binary connectives share one case
    binCase : ∀ {n} (op : ∀ {j} → Formula S j → Formula S j → Formula S j)
              (opA : Formula Ab n → Formula Ab n → Formula Ab n) (k : Fin 12)
              (a b : Formula Ab n) (code : cd (opA a b) ≡ pr (# (toℕ k)) (pr (cd a) (cd b)))
              (relIs : R.relN (toℕ k) ≡ R.binRel op)
              (bridge : ∀ {j} (env : S ^ j) (ya yb : Fin j)
                      → fst (lookup ya env) ≡ fst (SatW a) → fst (lookup yb env) ≡ fst (SatW b)
                      → ExtFact (fst (SatW (opA a b))) (fst (envSet W n))
                          (λ z → ⟨ (z ∷ env) ⊨ op (var i0 ∈̇ var (suc ya)) (var i0 ∈̇ var (suc yb)) ⟩))
            → Pinned a → Pinned b → Pinned (opA a b)
    binCase {n} op opA k a b code relIs bridge ia ib y mem =
      PT.rec (setIsSet _ _) (λ { (ya , ma) → PT.rec (setIsSet _ _) (λ { (yb , mb) →
        PT.rec (setIsSet _ _)
          (λ { (s , s₁ , e₁ , s₂ , e₂ , ext) →
            let env = yb ∷ keyS W b ∷ s₂ ∷ e₂ ∷ ya ∷ keyS W a ∷ s₁ ∷ e₁ ∷ codeS W b ∷ codeS W a ∷ s ∷ K.δ12
                P : S → Type (ℓ-suc ℓ)
                P z = ⟨ (z ∷ env) ⊨ R.binBody op ⟩
            in ext-unique y (SatW (opA a b)) (envSet W n) P ext (bridge env i4 i0 (ia ya ma) (ib yb mb)) })
          (K.RR.bin-out op (subst (λ φ → ⟨ K.δ12 ⊨ φ ⟩) relIs K.rel)
             (codeS W a) (codeS W b) (keyS W a) ya (keyS W b) yb refl ma refl mb refl) })
        (sub b) })
        (sub a)
      where
      module K = Case (opA a b) k (payS (opA a b) (toℕ k) (pr (cd a) (cd b)) code) code y mem

    quCase : ∀ {n} (q : ∀ {j} → Term S j → Formula S (suc j) → Formula S j)
             (qA : Formula Ab (suc n) → Formula Ab n) (k : Fin 12)
             (a : Formula Ab (suc n)) (code : cd (qA a) ≡ pr (# (toℕ k)) (cd a))
             (relIs : R.relN (toℕ k) ≡ R.quRel q)
             (bridge : ∀ {j} (env : S ^ j) (wi yai : Fin j)
                     → fst (lookup wi env) ≡ Wv → fst (lookup yai env) ≡ fst (SatW a)
                     → ExtFact (fst (SatW (qA a))) (fst (envSet W n))
                         (λ z → ⟨ (z ∷ env) ⊨ q (var (suc wi)) (∃̇∈ (var (suc (suc yai))) (consAtL i0 i1 i2)) ⟩))
           → Pinned a → Pinned (qA a)
    quCase {n} q qA k a code relIs bridge ia y mem =
      PT.rec (setIsSet _ _) (λ { (ya , ma) →
        PT.rec (setIsSet _ _)
          (λ { (s , s' , e' , ext) →
            let env = nn (suc n) ∷ s' ∷ ya ∷ keyS W a ∷ s ∷ e' ∷ K.δ12
                P : S → Type (ℓ-suc ℓ)
                P z = ⟨ (z ∷ env) ⊨ R.quBody q ⟩
            in ext-unique y (SatW (qA a)) (envSet W n) P ext (bridge env (sh 18 w) i2 qw (ia ya ma)) })
          (K.RR.qu-out q (subst (λ φ → ⟨ K.δ12 ⊨ φ ⟩) relIs K.rel) (keyS W a) ya (nn (suc n)) ma refl refl) })
        (sub a)
      where
      module K = Case (qA a) k (payS (qA a) (toℕ k) (cd a) code) code y mem

    bqCase : ∀ {n} (q : ∀ {j} → Term S j → Formula S (suc j) → Formula S j)
             (c : ∀ {j} → Formula S j → Formula S j → Formula S j)
             (qA : Term Ab n → Formula Ab (suc n) → Formula Ab n) (k : Fin 12)
             (t : Term Ab n) (a : Formula Ab (suc n)) (code : cd (qA t a) ≡ pr (# (toℕ k)) (pr (ct t) (cd a)))
             (relIs : R.relN (toℕ k) ≡ R.bqRel q c)
             (body : ∀ {j} → Fin j → Fin j → Fin j → Fin j → Fin j → Formula S (1 + j))
             (bodyIs : ∀ {j} (wi ti yai N0i N1i : Fin j)
                     → body wi ti yai N0i N1i
                     ≡ q (var (suc wi)) (c (tmIs (suc (suc ti)) i1 i0 (suc (suc N0i)) (suc (suc N1i)))
                         (q (var (suc (suc wi))) (c (var i0 ∈̇ var i1) (∃̇∈ (var (suc (suc (suc yai)))) (consAtL i0 i1 i3))))))
             (bridge : ∀ {j} (env : S ^ j) (wi ti yai N0i N1i : Fin j)
                     → fst (lookup wi env) ≡ Wv → fst (lookup ti env) ≡ ct t → fst (lookup yai env) ≡ fst (SatW a)
                     → fst (lookup N0i env) ≡ # 0 → fst (lookup N1i env) ≡ # 1
                     → ExtFact (fst (SatW (qA t a))) (fst (envSet W n)) (λ z → ⟨ (z ∷ env) ⊨ body wi ti yai N0i N1i ⟩))
           → Pinned a → Pinned (qA t a)
    bqCase {n} q c qA k t a code relIs body bodyIs bridge ia y mem =
      PT.rec (setIsSet _ _) (λ { (ya , ma) →
        PT.rec (setIsSet _ _)
          (λ { (s , s₁ , s' , e' , ext) →
            let env = nn (suc n) ∷ s' ∷ ya ∷ keyS W a ∷ s₁ ∷ e' ∷ codeS W a ∷ tS ∷ s ∷ K.δ12
                P : S → Type (ℓ-suc ℓ)
                P z = ⟨ (z ∷ env) ⊨ R.bqBody q c ⟩
            in ext-unique y (SatW (qA t a)) (envSet W n) P ext
                 (subst (λ φ → ExtFact (fst (SatW (qA t a))) (fst (envSet W n)) (λ z → ⟨ (z ∷ env) ⊨ φ ⟩))
                    (bodyIs (sh 21 w) i7 i2 (sh 21 (N f0)) (sh 21 (N f1)))
                    (bridge env (sh 21 w) i7 i2 (sh 21 (N f0)) (sh 21 (N f1)) qw refl (ia ya ma) (tg f0) (tg f1))) })
          (K.RR.bq-out q c (subst (λ φ → ⟨ K.δ12 ⊨ φ ⟩) relIs K.rel) tS (codeS W a) (keyS W a) ya (nn (suc n)) refl ma refl refl) })
        (sub a)
      where
      rS : S
      rS = payS (qA t a) (toℕ k) (pr (ct t) (cd a)) code
      tS : S
      tS = fstS rS (ct t) (cd a) refl
      module K = Case (qA t a) k rS code y mem

    atomCase : ∀ {n} (opA : ∀ {j} → Term Ab j → Term Ab j → Formula Ab j) (k : Fin 12)
               (t u : Term Ab n) (code : cd (opA t u) ≡ pr (# (toℕ k)) (pr (ct t) (ct u)))
               (rel : Formula S (18 + m))
               (relIs : R.relN (toℕ k) ≡ R.atomRel rel)
               (bridge : ∀ (env : S ^ (15 + m)) (wi ti ui N0i N1i : Fin (15 + m))
                       → fst (lookup wi env) ≡ Wv → fst (lookup ti env) ≡ ct t → fst (lookup ui env) ≡ ct u
                       → fst (lookup N0i env) ≡ # 0 → fst (lookup N1i env) ≡ # 1
                       → ExtFact (fst (SatW (opA t u))) (fst (envSet W n)) (λ z → ⟨ (z ∷ env) ⊨ atomEx wi ti ui N0i N1i rel ⟩))
             → Pinned (opA t u)
    atomCase {n} opA k t u code rel relIs bridge y mem =
      PT.rec (setIsSet _ _)
        (λ { (s , ext) →
          let env = uS ∷ tS ∷ s ∷ K.δ12
              P : S → Type (ℓ-suc ℓ)
              P z = ⟨ (z ∷ env) ⊨ R.atomBody rel ⟩
          in ext-unique y (SatW (opA t u)) (envSet W n) P ext
               (bridge env (sh 15 w) i1 i0 (sh 15 (N f0)) (sh 15 (N f1)) qw refl refl (tg f0) (tg f1)) })
        (K.RR.atom-out rel (subst (λ φ → ⟨ K.δ12 ⊨ φ ⟩) relIs K.rel) tS uS refl)
      where
      rS : S
      rS = payS (opA t u) (toℕ k) (pr (ct t) (ct u)) code
      tS uS : S
      tS = fstS rS (ct t) (ct u) refl
      uS = sndS rS (ct t) (ct u) refl
      module K = Case (opA t u) k rS code y mem

    memAgree : ∀ {j} (env : S ^ j) (z v x : S)
             → (⟨ (x ∷ v ∷ z ∷ env) ⊨ var i1 ∈̇ var i0 ⟩ → ⟨ fst v ∈ fst x ⟩) × (⟨ fst v ∈ fst x ⟩ → ⟨ (x ∷ v ∷ z ∷ env) ⊨ var i1 ∈̇ var i0 ⟩)
    memAgree env z v x = (λ h → h) , (λ h → h)

    eqAgree : ∀ {j} (env : S ^ j) (z v x : S)
            → (⟨ (x ∷ v ∷ z ∷ env) ⊨ var i1 ≐ var i0 ⟩ → fst v ≡ fst x) × ((fst v ≡ fst x) → ⟨ (x ∷ v ∷ z ∷ env) ⊨ var i1 ≐ var i0 ⟩)
    eqAgree env z v x = (λ h → h) , (λ h → h)

  pinned : ∀ {n} (ψ : Formula Ab n) → Pinned ψ
  pinned (t ∈̇ u) = atomCase _∈̇_ f0 t u refl (var i1 ∈̇ var i0) refl
    (λ env wi ti ui N0i N1i qw' qt qu q0 q1 →
      AtomBridge.atomBridge t u env wi ti ui N0i N1i qw' qt qu q0 q1 _∈̇_ (λ v x → ⟨ fst v ∈ fst x ⟩)
        (var i1 ∈̇ var i0) (memAgree env) (cond∈-out W (toT t) (toT u)) (cond∈-in W (toT t) (toT u)))
  pinned (t ≐ u) = atomCase _≐_ f1 t u refl (var i1 ≐ var i0) refl
    (λ env wi ti ui N0i N1i qw' qt qu q0 q1 →
      AtomBridge.atomBridge t u env wi ti ui N0i N1i qw' qt qu q0 q1 _≐_ (λ v x → fst v ≡ fst x)
        (var i1 ≐ var i0) (eqAgree env) (cond≐-out W (toT t) (toT u)) (cond≐-in W (toT t) (toT u)))
  pinned (a ∧̇ b) = binCase _∧̇_ _∧̇_ f2 a b refl refl (andBridge a b) (pinned a) (pinned b)
  pinned (a ∨̇ b) = binCase _∨̇_ _∨̇_ f3 a b refl refl (orBridge a b) (pinned a) (pinned b)
  pinned (a ⇒̇ b) = binCase _⇒̇_ _⇒̇_ f4 a b refl refl (impBridge a b) (pinned a) (pinned b)
  pinned {n} (¬̇ a) y mem = PT.rec (setIsSet _ _) (λ { (ya , ma) →
    PT.rec (setIsSet _ _)
      (λ { (s , e' , ext) →
        let env = ya ∷ keyS W a ∷ s ∷ e' ∷ K.δ12
            P : S → Type (ℓ-suc ℓ)
            P z = ⟨ (z ∷ env) ⊨ R.negBody ⟩
        in ext-unique y (SatW (¬̇ a)) (envSet W n) P ext (negBridge a env i0 (pinned a ya ma)) })
      (K.RR.neg-out K.rel (keyS W a) ya ma refl) })
    (sub a)
    where
    module K = Case (¬̇ a) f5 (codeS W a) refl y mem
  pinned {n} ⊤̇ y mem = ext-unique y (SatW ⊤̇) (envSet W n) (λ z → ⟨ (z ∷ K.δ12) ⊨ ⊤̇ ⟩) (extB-out i0 i8 ⊤̇ K.δ12 K.rel) (topBridge n K.δ12)
    where
    module K = Case ⊤̇ f6 (nn 0) refl y mem
  pinned {n} ⊥̇ y mem = ext-unique y (SatW ⊥̇) (envSet W n) (λ z → ⟨ (z ∷ K.δ12) ⊨ ⊥̇ ⟩) (extB-out i0 i8 ⊥̇ K.δ12 K.rel) (botBridge n K.δ12)
    where
    module K = Case ⊥̇ f7 (nn 0) refl y mem
  pinned (∃̇ a) = quCase ∃̇∈ ∃̇_ f8 a refl refl (exBridge a) (pinned a)
  pinned (∀̇ a) = quCase ∀̇∈ ∀̇_ f9 a refl refl (allBridge a) (pinned a)
  pinned (∀̇∈ t a) = bqCase ∀̇∈ _⇒̇_ ∀̇∈ f10 t a refl refl bqAll (λ _ _ _ _ _ → refl)
    (λ env wi ti yai N0i N1i qw' qt qa q0 q1 → BqBridge.allInBridge t a env wi ti yai N0i N1i qw' qt qa q0 q1) (pinned a)
  pinned (∃̇∈ t a) = bqCase ∃̇∈ _∧̇_ ∃̇∈ f11 t a refl refl bqEx (λ _ _ _ _ _ → refl)
    (λ env wi ti yai N0i N1i qw' qt qa q0 q1 → BqBridge.exInBridge t a env wi ti yai N0i N1i qw' qt qa q0 q1) (pinned a)

  -- WHAT SOUNDNESS SAYS.  C is the code set, E the tower, and T the
  -- graph of the uniform table: every entry is at a key and records
  -- the table's value there, and every key has that entry.
  C-out : (c : S) → ⟨ fst c ∈ Cv ⟩ → ⟨ fst c ∈ fst (AllCodes W) ⟩
  C-out c c∈ = PT.rec (snd (fst c ∈ fst (AllCodes W)))
    (λ { (k , ψ , e) → subst (λ u → ⟨ u ∈ fst (AllCodes W) ⟩) (sym e) (key∈AllCodes W ψ) })
    (CS.key-out c c∈)

  C-in : (c : S) → ⟨ fst c ∈ fst (AllCodes W) ⟩ → ⟨ fst c ∈ Cv ⟩
  C-in c c∈ = PT.rec (snd (fst c ∈ Cv))
    (λ { (k , ψ , e) → subst (λ u → ⟨ u ∈ Cv ⟩) (sym e) (CC.key-in ψ) })
    (AllCodes-out W c c∈)

  E-out : (n F : S) → ⟨ pr (fst n) (fst F) ∈ Ev ⟩
        → ∥ Σ[ k ∈ ℕ ] ((fst n ≡ # k) × (fst F ≡ fst (envSet W k))) ∥₁
  E-out = TR.entry-out

  E-in : (k : ℕ) → ⟨ pr (# k) (fst (envSet W k)) ∈ Ev ⟩
  E-in = TR.entry-in

  T-out : (x y : S) → ⟨ pr (fst x) (fst y) ∈ Tv ⟩
        → Σ[ mx ∈ ⟨ fst x ∈ fst (AllCodes W) ⟩ ] (fst y ≡ fst (Table.val W W x mx))
  T-out x y h = PT.rec (isPropΣ (snd (fst x ∈ fst (AllCodes W))) (λ mx → setIsSet _ _))
    (λ { (c , yc , (ee , c∈)) → PT.rec (isPropΣ (snd (fst x ∈ fst (AllCodes W))) (λ mx → setIsSet _ _))
      (λ { (k , ψ , e) →
        let q = pr-inj ee
            qx : fst x ≡ fst (keyS W ψ)
            qx = q .fst ∙ e
            mx : ⟨ fst x ∈ fst (AllCodes W) ⟩
            mx = subst (λ u → ⟨ u ∈ fst (AllCodes W) ⟩) (sym qx) (key∈AllCodes W ψ)
        in mx , ( pinned ψ y (subst (λ u → ⟨ u ∈ Tv ⟩) (cong (λ a → pr a (fst y)) qx) h)
                ∙ sym (cong fst (val-at W W ψ x mx qx)) ) })
      (CS.key-out c c∈) })
    (Fr.onC-out hOn (down (lookup T γ) (pr (fst x) (fst y)) h) h)

  T-in : (x : S) (mx : ⟨ fst x ∈ fst (AllCodes W) ⟩) → ⟨ pr (fst x) (fst (Table.val W W x mx)) ∈ Tv ⟩
  T-in x mx = PT.rec (snd (pr (fst x) (fst (Table.val W W x mx)) ∈ Tv))
    (λ { (k , ψ , e) → PT.rec (snd (pr (fst x) (fst (Table.val W W x mx)) ∈ Tv))
      (λ { (y , my) →
        subst (λ u → ⟨ u ∈ Tv ⟩)
          (cong₂ pr (sym e) (pinned ψ y my ∙ sym (cong fst (val-at W W ψ x mx e))))
          my })
      (sub ψ) })
    (AllCodes-out W x mx)
```

THE TABLE IS COMPLETE.  The graph of the uniform table, over the
code set and the tower, satisfies the description: each clause is
read at its frame, the code is decoded, the entries are read as the
table's values, and the bridge supplies the body.

A code's constructor and payload, from its tag, are read in
src/L/Coding/Pinned.lagda.md.

```agda
module SatHolds {m : ℕ} (T w C E : Fin m) (N : Fin 12 → Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) (qT : fst (lookup T γ) ≡ fst (SatGraph.pairs W))
  (qC : fst (lookup C γ) ≡ fst (AllCodes W)) (qE : fst (lookup E γ) ≡ fst (Tower.tower W))
  (tg : Tags γ N) where
  open Alphabet W
  open Bridge W
  open Match W
  private
    Tv = fst (lookup T γ)
    Cv = fst (lookup C γ)
    Ev = fst (lookup E γ)
    Wv = fst W
    module Fr = Frame T w C E N γ tg
    module Cl = Clause T w C E N
    module R = Rel T w N

    -- an entry of T is the table's value at a key
    val≡ : ∀ {n} (ψ : Formula Ab n) (c yc : S) → fst c ≡ fst (keyS W ψ)
         → ⟨ pr (fst c) (fst yc) ∈ Tv ⟩ → fst yc ≡ fst (SatW ψ)
    val≡ ψ c yc qc h =
      let p = SatGraph.pairs-out W c yc (subst (λ u → ⟨ pr (fst c) (fst yc) ∈ u ⟩) qT h)
      in p .snd ∙ cong fst (SatGraph.valOf≡ W c (p .fst)) ∙ cong fst (val-at W W ψ c (p .fst) qc)

    -- an entry of E is (# n, envSet n)
    Arity : (ar F : S) → Type (ℓ-suc ℓ)
    Arity ar F = ∥ Σ[ n ∈ ℕ ] ((fst ar ≡ # n) × (fst F ≡ fst (envSet W n))) ∥₁

    arity : (q ar F : S) → ⟨ fst q ∈ Ev ⟩ → fst q ≡ pr (fst ar) (fst F) → Arity ar F
    arity q ar F q∈ eq = PT.map
      (λ { (n , e) → n , (pr-inj (sym eq ∙ e) .fst , pr-inj (sym eq ∙ e) .snd) })
      (Tower.tower-out W q (subst (λ u → ⟨ fst q ∈ u ⟩) qE q∈))

    -- a member of C at arity n decodes
    Dec : (n : ℕ) (z : V ℓ) → Type (ℓ-suc ℓ)
    Dec n z = ∥ Σ[ ψ ∈ Formula Ab n ] (z ≡ cd ψ) ∥₁

    decode : (c : S) → ⟨ fst c ∈ Cv ⟩ → (n : ℕ) (z : V ℓ) → fst c ≡ pr (# n) z → Dec n z
    decode c c∈ = decodeAll c (subst (λ u → ⟨ fst c ∈ u ⟩) qC c∈)

    -- the key of a formula, in C
    key∈ : ∀ {n} (ψ : Formula Ab n) → ⟨ fst (keyS W ψ) ∈ Cv ⟩
    key∈ ψ = subst (λ u → ⟨ fst (keyS W ψ) ∈ u ⟩) (sym qC) (key∈AllCodes W ψ)

    total : ⟨ γ ⊨ Cl.total ⟩
    total = Fr.total-in (λ c c∈ →
      let mx = subst (λ u → ⟨ fst c ∈ u ⟩) qC c∈
      in ∣ SatGraph.valOf W c mx , subst (λ u → ⟨ pr (fst c) (fst (SatGraph.valOf W c mx)) ∈ u ⟩) (sym qT) (SatGraph.pairs-in W c mx) ∣₁)

    onC : ⟨ γ ⊨ Cl.onC ⟩
    onC = Fr.onC-in (λ e e∈ → PT.map
      (λ { (x , mx , ee) → x , SatGraph.valOf W x mx , (ee , subst (λ u → ⟨ fst x ∈ u ⟩) (sym qC) mx) })
      (SatGraph.pairs-shape W e (subst (λ u → ⟨ fst e ∈ u ⟩) qT e∈)))

    -- THE CLAUSES.  Each is read at its frame; the data of the frame
    -- are decoded, and the relation is filled from the bridge.
    record Args (k : Fin 12) : Type (ℓ-suc ℓ) where
      field
        q ar F s c p s1 r s2 e yc s3 : S
        q∈ : ⟨ fst q ∈ Ev ⟩
        eq : fst q ≡ pr (fst ar) (fst F)
        c∈ : ⟨ fst c ∈ Cv ⟩
        ec : fst c ≡ pr (fst ar) (fst p)
        ep : fst p ≡ pr (# (toℕ k)) (fst r)
        e∈ : ⟨ fst e ∈ Tv ⟩
        ee : fst e ≡ pr (fst c) (fst yc)

    module Fill (k : Fin 12) (A : Args k) where
      open Args A

      frame : S ^ (12 + m)
      frame = yc ∷ s3 ∷ e ∷ r ∷ s2 ∷ p ∷ s1 ∷ c ∷ F ∷ ar ∷ s ∷ q ∷ γ

      module RR = RelRead T w N frame

      Goal : Type (ℓ-suc ℓ)
      Goal = ⟨ frame ⊨ R.relN (toℕ k) ⟩

      isPropGoal : isProp Goal
      isPropGoal = snd (frame ⊨ R.relN (toℕ k))

      -- the extension fact of yc over F, from the recursion's value at
      -- the formula the code decodes to
      transfer : (n : ℕ) (ψ : Formula Ab n) → fst ar ≡ # n → fst F ≡ fst (envSet W n)
               → fst p ≡ cd ψ → {j : ℕ} (env : S ^ j) (φ : Formula S (1 + j))
               → ExtFact (fst (SatW ψ)) (fst (envSet W n)) (λ z → ⟨ (z ∷ env) ⊨ φ ⟩)
               → RR.Ext env φ
      transfer n ψ qa qF qp env φ ext =
        subst2 (λ Y F' → ExtFact Y F' (λ z → ⟨ (z ∷ env) ⊨ φ ⟩))
          (sym (val≡ ψ c yc (ec ∙ cong₂ pr qa qp) (subst (λ u → ⟨ u ∈ Tv ⟩) ee e∈))) (sym qF) ext

      -- the value at a subkey
      subVal : (n : ℕ) (a : Formula Ab n) (c₁ ya e₁ : S) → fst ar ≡ # n
             → ⟨ fst e₁ ∈ Tv ⟩ → fst e₁ ≡ pr (fst c₁) (fst ya) → fst c₁ ≡ pr (fst ar) (cd a)
             → fst ya ≡ fst (SatW a)
      subVal n a c₁ ya e₁ qa e₁∈ ee₁ e₁' =
        val≡ a c₁ ya (e₁' ∙ cong (λ v → pr v (cd a)) qa) (subst (λ u → ⟨ u ∈ Tv ⟩) ee₁ e₁∈)

      subValS : (n : ℕ) (a : Formula Ab (suc n)) (c₁ ya e₁ ar' : S) → fst ar ≡ # n
              → ⟨ fst e₁ ∈ Tv ⟩ → fst e₁ ≡ pr (fst c₁) (fst ya) → fst c₁ ≡ pr (fst ar') (cd a) → fst ar' ≡ sucV (fst ar)
              → fst ya ≡ fst (SatW a)
      subValS n a c₁ ya e₁ ar' qa e₁∈ ee₁ e₁' es =
        val≡ a c₁ ya (e₁' ∙ cong (λ v → pr v (cd a)) (es ∙ cong sucV qa)) (subst (λ u → ⟨ u ∈ Tv ⟩) ee₁ e₁∈)

      -- the frame's data, decoded
      Data : Type (ℓ-suc ℓ)
      Data = Σ[ n ∈ ℕ ] ((fst ar ≡ # n) × ((fst F ≡ fst (envSet W n))
               × (Σ[ ψ ∈ Formula Ab n ] ((fst p ≡ cd ψ) × MatchN (toℕ k) ψ (fst r)))))

      data' : ∥ Data ∥₁
      data' = PT.rec squash₁
        (λ { (n , (qa , qF)) → PT.map
          (λ { (ψ , qp) → n , (qa , qF , ψ , (qp , matchAt ψ (toℕ k) (fst r) (sym qp ∙ ep))) })
          (decode c c∈ n (fst p) (ec ∙ cong (λ v → pr v (fst p)) qa)) })
        (arity q ar F q∈ eq)

      -- the binary connectives
      module BinFill (op : ∀ {j} → Formula S j → Formula S j → Formula S j)
        (opA : ∀ {j} → Formula Ab j → Formula Ab j → Formula Ab j)
        (bridge : ∀ {n} (a b : Formula Ab n) {j : ℕ} (env : S ^ j) (ya yb : Fin j)
                → fst (lookup ya env) ≡ fst (SatW a) → fst (lookup yb env) ≡ fst (SatW b)
                → ExtFact (fst (SatW (opA a b))) (fst (envSet W n))
                    (λ z → ⟨ (z ∷ env) ⊨ op (var i0 ∈̇ var (suc ya)) (var i0 ∈̇ var (suc yb)) ⟩)) where

        go : (n : ℕ) (a b ψ : Formula Ab n) → fst ar ≡ # n → fst F ≡ fst (envSet W n)
           → fst p ≡ cd ψ → ψ ≡ opA a b → fst r ≡ pr (cd a) (cd b) → ⟨ frame ⊨ R.binRel op ⟩
        go n a b ψ qa qF qp qψ qr = RR.bin-in op (λ a' b' s' c₁ ya s₁ e₁ c₂ yb s₂ e₂ er e₁∈ ee₁ e₁' e₂∈ ee₂ e₂' →
          let q' = pr-inj (sym er ∙ qr)
              ya≡ = subVal n a c₁ ya e₁ qa e₁∈ ee₁ (e₁' ∙ cong (pr (fst ar)) (q' .fst))
              yb≡ = subVal n b c₂ yb e₂ qa e₂∈ ee₂ (e₂' ∙ cong (pr (fst ar)) (q' .snd))
              env = yb ∷ c₂ ∷ s₂ ∷ e₂ ∷ ya ∷ c₁ ∷ s₁ ∷ e₁ ∷ b' ∷ a' ∷ s' ∷ frame
              P : S → Type (ℓ-suc ℓ)
              P z = ⟨ (z ∷ env) ⊨ R.binBody op ⟩
          in transfer n ψ qa qF qp env (R.binBody op)
               (subst (λ χ → ExtFact (fst (SatW χ)) (fst (envSet W n)) P) (sym qψ) (bridge a b env i4 i0 ya≡ yb≡)))

      -- the unbounded quantifiers
      module QuFill (q' : ∀ {j} → Term S j → Formula S (suc j) → Formula S j)
        (qA : ∀ {j} → Formula Ab (suc j) → Formula Ab j)
        (bridge : ∀ {n} (a : Formula Ab (suc n)) {j : ℕ} (env : S ^ j) (wi yai : Fin j)
                → fst (lookup wi env) ≡ Wv → fst (lookup yai env) ≡ fst (SatW a)
                → ExtFact (fst (SatW (qA a))) (fst (envSet W n))
                    (λ z → ⟨ (z ∷ env) ⊨ q' (var (suc wi)) (∃̇∈ (var (suc (suc yai))) (consAtL i0 i1 i2)) ⟩)) where

        go : (n : ℕ) (a : Formula Ab (suc n)) (ψ : Formula Ab n) → fst ar ≡ # n → fst F ≡ fst (envSet W n)
           → fst p ≡ cd ψ → ψ ≡ qA a → fst r ≡ cd a → ⟨ frame ⊨ R.quRel q' ⟩
        go n a ψ qa qF qp qψ qr = RR.qu-in q' (λ c₁ ya ar' s' s'' e' e'∈ ee₁ e₁' es →
          let ya≡ = subValS n a c₁ ya e' ar' qa e'∈ ee₁ (e₁' ∙ cong (pr (fst ar')) qr) es
              env = ar' ∷ s'' ∷ ya ∷ c₁ ∷ s' ∷ e' ∷ frame
              P : S → Type (ℓ-suc ℓ)
              P z = ⟨ (z ∷ env) ⊨ R.quBody q' ⟩
          in transfer n ψ qa qF qp env (R.quBody q')
               (subst (λ χ → ExtFact (fst (SatW χ)) (fst (envSet W n)) P) (sym qψ) (bridge a env (sh 18 w) i2 qw ya≡)))

      -- the bounded quantifiers
      module BqFill (q' : ∀ {j} → Term S j → Formula S (suc j) → Formula S j)
        (c' : ∀ {j} → Formula S j → Formula S j → Formula S j)
        (qA : ∀ {j} → Term Ab j → Formula Ab (suc j) → Formula Ab j)
        (body : ∀ {j} → Fin j → Fin j → Fin j → Fin j → Fin j → Formula S (1 + j))
        (bodyIs : ∀ {j} (wi ti yai N0i N1i : Fin j)
                → body wi ti yai N0i N1i
                ≡ q' (var (suc wi)) (c' (tmIs (suc (suc ti)) i1 i0 (suc (suc N0i)) (suc (suc N1i)))
                    (q' (var (suc (suc wi))) (c' (var i0 ∈̇ var i1) (∃̇∈ (var (suc (suc (suc yai)))) (consAtL i0 i1 i3))))))
        (bridge : ∀ {n} (t : Term Ab n) (a : Formula Ab (suc n)) {j : ℕ} (env : S ^ j) (wi ti yai N0i N1i : Fin j)
                → fst (lookup wi env) ≡ Wv → fst (lookup ti env) ≡ ct t → fst (lookup yai env) ≡ fst (SatW a)
                → fst (lookup N0i env) ≡ # 0 → fst (lookup N1i env) ≡ # 1
                → ExtFact (fst (SatW (qA t a))) (fst (envSet W n)) (λ z → ⟨ (z ∷ env) ⊨ body wi ti yai N0i N1i ⟩)) where

        go : (n : ℕ) (t : Term Ab n) (a : Formula Ab (suc n)) (ψ : Formula Ab n) → fst ar ≡ # n → fst F ≡ fst (envSet W n)
           → fst p ≡ cd ψ → ψ ≡ qA t a → fst r ≡ pr (ct t) (cd a) → ⟨ frame ⊨ R.bqRel q' c' ⟩
        go n t a ψ qa qF qp qψ qr = RR.bq-in q' c' (λ t' a' s' c₁ ya ar' s₁ s'' e' er e'∈ ee₁ e₁' es →
          let q'' = pr-inj (sym er ∙ qr)
              ya≡ = subValS n a c₁ ya e' ar' qa e'∈ ee₁ (e₁' ∙ cong (pr (fst ar')) (q'' .snd)) es
              env = ar' ∷ s'' ∷ ya ∷ c₁ ∷ s₁ ∷ e' ∷ a' ∷ t' ∷ s' ∷ frame
              P : S → Type (ℓ-suc ℓ)
              P z = ⟨ (z ∷ env) ⊨ R.bqBody q' c' ⟩
          in transfer n ψ qa qF qp env (R.bqBody q' c')
               (subst (λ χ → ExtFact (fst (SatW χ)) (fst (envSet W n)) P) (sym qψ)
                 (subst (λ φ → ExtFact (fst (SatW (qA t a))) (fst (envSet W n)) (λ z → ⟨ (z ∷ env) ⊨ φ ⟩))
                   (bodyIs (sh 21 w) i7 i2 (sh 21 (N f0)) (sh 21 (N f1)))
                   (bridge t a env (sh 21 w) i7 i2 (sh 21 (N f0)) (sh 21 (N f1)) qw (q'' .fst) ya≡ (tg f0) (tg f1)))))

      -- the atoms
      module AtomFill (opA : ∀ {j} → Term Ab j → Term Ab j → Formula Ab j) (rel : Formula S (18 + m))
        (bridge : ∀ {n} (t u : Term Ab n) (env : S ^ (15 + m)) (wi ti ui N0i N1i : Fin (15 + m))
                → fst (lookup wi env) ≡ Wv → fst (lookup ti env) ≡ ct t → fst (lookup ui env) ≡ ct u
                → fst (lookup N0i env) ≡ # 0 → fst (lookup N1i env) ≡ # 1
                → ExtFact (fst (SatW (opA t u))) (fst (envSet W n)) (λ z → ⟨ (z ∷ env) ⊨ atomEx wi ti ui N0i N1i rel ⟩)) where

        go : (n : ℕ) (t u : Term Ab n) (ψ : Formula Ab n) → fst ar ≡ # n → fst F ≡ fst (envSet W n)
           → fst p ≡ cd ψ → ψ ≡ opA t u → fst r ≡ pr (ct t) (ct u) → ⟨ frame ⊨ R.atomRel rel ⟩
        go n t u ψ qa qF qp qψ qr = RR.atom-in rel (λ t' u' s' er →
          let q' = pr-inj (sym er ∙ qr)
              env = u' ∷ t' ∷ s' ∷ frame
              P : S → Type (ℓ-suc ℓ)
              P z = ⟨ (z ∷ env) ⊨ R.atomBody rel ⟩
          in transfer n ψ qa qF qp env (R.atomBody rel)
               (subst (λ χ → ExtFact (fst (SatW χ)) (fst (envSet W n)) P) (sym qψ)
                 (bridge t u env (sh 15 w) i1 i0 (sh 15 (N f0)) (sh 15 (N f1)) qw (q' .fst) (q' .snd) (tg f0) (tg f1))))

      -- negation and the constants
      negGo : (n : ℕ) (a ψ : Formula Ab n) → fst ar ≡ # n → fst F ≡ fst (envSet W n)
            → fst p ≡ cd ψ → ψ ≡ ¬̇ a → fst r ≡ cd a → ⟨ frame ⊨ R.negRel ⟩
      negGo n a ψ qa qF qp qψ qr = RR.neg-in (λ c₁ ya s' e' e'∈ ee₁ e₁' →
        let ya≡ = subVal n a c₁ ya e' qa e'∈ ee₁ (e₁' ∙ cong (pr (fst ar)) qr)
            env = ya ∷ c₁ ∷ s' ∷ e' ∷ frame
            P : S → Type (ℓ-suc ℓ)
            P z = ⟨ (z ∷ env) ⊨ R.negBody ⟩
        in transfer n ψ qa qF qp env R.negBody
             (subst (λ χ → ExtFact (fst (SatW χ)) (fst (envSet W n)) P) (sym qψ) (negBridge a env i0 ya≡)))

      topGo : (n : ℕ) (ψ : Formula Ab n) → fst ar ≡ # n → fst F ≡ fst (envSet W n)
            → fst p ≡ cd ψ → ψ ≡ ⊤̇ → ⟨ frame ⊨ R.topRel ⟩
      topGo n ψ qa qF qp qψ = extB-in i0 i8 ⊤̇ frame
        (transfer n ψ qa qF qp frame ⊤̇
          (subst (λ χ → ExtFact (fst (SatW χ)) (fst (envSet W n)) (λ z → ⟨ (z ∷ frame) ⊨ ⊤̇ ⟩)) (sym qψ) (topBridge n frame)))

      botGo : (n : ℕ) (ψ : Formula Ab n) → fst ar ≡ # n → fst F ≡ fst (envSet W n)
            → fst p ≡ cd ψ → ψ ≡ ⊥̇ → ⟨ frame ⊨ R.botRel ⟩
      botGo n ψ qa qF qp qψ = extB-in i0 i8 ⊥̇ frame
        (transfer n ψ qa qF qp frame ⊥̇
          (subst (λ χ → ExtFact (fst (SatW χ)) (fst (envSet W n)) (λ z → ⟨ (z ∷ frame) ⊨ ⊥̇ ⟩)) (sym qψ) (botBridge n frame)))

    -- The dispatch on the tag, one clause each.
    fill : (k : Fin 12) (A : Args k) → Fill.Data k A → Fill.Goal k A
    fill zero A (n , (qa , qF , ψ , (qp , (t , u , (qψ , qr))))) =
      Fill.AtomFill.go zero A _∈̇_ (var i1 ∈̇ var i0)
        (λ t u env wi ti ui N0i N1i qw' qt qu q0 q1 →
          AtomBridge.atomBridge t u env wi ti ui N0i N1i qw' qt qu q0 q1 _∈̇_ (λ v x → ⟨ fst v ∈ fst x ⟩)
            (var i1 ∈̇ var i0) (λ z v x → (λ h → h) , (λ h → h)) (cond∈-out W (toT t) (toT u)) (cond∈-in W (toT t) (toT u)))
        n t u ψ qa qF qp qψ qr
    fill (suc zero) A (n , (qa , qF , ψ , (qp , (t , u , (qψ , qr))))) =
      Fill.AtomFill.go (suc zero) A _≐_ (var i1 ≐ var i0)
        (λ t u env wi ti ui N0i N1i qw' qt qu q0 q1 →
          AtomBridge.atomBridge t u env wi ti ui N0i N1i qw' qt qu q0 q1 _≐_ (λ v x → fst v ≡ fst x)
            (var i1 ≐ var i0) (λ z v x → (λ h → h) , (λ h → h)) (cond≐-out W (toT t) (toT u)) (cond≐-in W (toT t) (toT u)))
        n t u ψ qa qF qp qψ qr
    fill (suc (suc zero)) A (n , (qa , qF , ψ , (qp , (a , b , (qψ , qr))))) =
      Fill.BinFill.go (suc (suc zero)) A _∧̇_ _∧̇_ andBridge n a b ψ qa qF qp qψ qr
    fill (suc (suc (suc zero))) A (n , (qa , qF , ψ , (qp , (a , b , (qψ , qr))))) =
      Fill.BinFill.go (suc (suc (suc zero))) A _∨̇_ _∨̇_ orBridge n a b ψ qa qF qp qψ qr
    fill (suc (suc (suc (suc zero)))) A (n , (qa , qF , ψ , (qp , (a , b , (qψ , qr))))) =
      Fill.BinFill.go (suc (suc (suc (suc zero)))) A _⇒̇_ _⇒̇_ impBridge n a b ψ qa qF qp qψ qr
    fill (suc (suc (suc (suc (suc zero))))) A (n , (qa , qF , ψ , (qp , (a , (qψ , qr))))) =
      Fill.negGo (suc (suc (suc (suc (suc zero))))) A n a ψ qa qF qp qψ qr
    fill (suc (suc (suc (suc (suc (suc zero)))))) A (n , (qa , qF , ψ , (qp , (qψ , qr)))) =
      Fill.topGo (suc (suc (suc (suc (suc (suc zero)))))) A n ψ qa qF qp qψ
    fill (suc (suc (suc (suc (suc (suc (suc zero))))))) A (n , (qa , qF , ψ , (qp , (qψ , qr)))) =
      Fill.botGo (suc (suc (suc (suc (suc (suc (suc zero))))))) A n ψ qa qF qp qψ
    fill (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) A (n , (qa , qF , ψ , (qp , (a , (qψ , qr))))) =
      Fill.QuFill.go (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) A ∃̇∈ ∃̇_ exBridge n a ψ qa qF qp qψ qr
    fill (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) A (n , (qa , qF , ψ , (qp , (a , (qψ , qr))))) =
      Fill.QuFill.go (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) A ∀̇∈ ∀̇_ allBridge n a ψ qa qF qp qψ qr
    fill (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) A (n , (qa , qF , ψ , (qp , (t , a , (qψ , qr))))) =
      Fill.BqFill.go (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) A ∀̇∈ _⇒̇_ ∀̇∈ bqAll (λ _ _ _ _ _ → refl)
        (λ t a env wi ti yai N0i N1i qw' qt qa' q0 q1 → BqBridge.allInBridge t a env wi ti yai N0i N1i qw' qt qa' q0 q1)
        n t a ψ qa qF qp qψ qr
    fill (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) A (n , (qa , qF , ψ , (qp , (t , a , (qψ , qr))))) =
      Fill.BqFill.go (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) A ∃̇∈ _∧̇_ ∃̇∈ bqEx (λ _ _ _ _ _ → refl)
        (λ t a env wi ti yai N0i N1i qw' qt qa' q0 q1 → BqBridge.exInBridge t a env wi ti yai N0i N1i qw' qt qa' q0 q1)
        n t a ψ qa qF qp qψ qr

    clause : (k : Fin 12) → ⟨ γ ⊨ Cl.clause k ⟩
    clause k = Fr.clause-in k (λ q ar F s c p s1 r s2 e yc s3 q∈ eq c∈ ec ep e∈ ee →
      let A : Args k
          A = record { q = q ; ar = ar ; F = F ; s = s ; c = c ; p = p ; s1 = s1 ; r = r ; s2 = s2 ; e = e ; yc = yc ; s3 = s3
                     ; q∈ = q∈ ; eq = eq ; c∈ = c∈ ; ec = ec ; ep = ep ; e∈ = e∈ ; ee = ee }
      in PT.rec (Fill.isPropGoal k A) (fill k A) (Fill.data' k A))

    twelve : ⟨ γ ⊨ Cl.twelve ⟩
    twelve = clause f0 , (clause f1 , (clause f2 , (clause f3 , (clause f4 , (clause f5
           , (clause f6 , (clause f7 , (clause f8 , (clause f9 , (clause f10 , clause f11))))))))))

  holds : ⟨ γ ⊨ tableAt T w C E N ⟩
  holds = total , (onC , twelve)
```

THE DESCRIPTION, SEALED.  "T is the satisfaction table of w over
the code set C and the environment tower E."  The seal holds the
three conjuncts; its readers are the two projections.

```agda
opaque
  satAt : ∀ {m} → Fin m → Fin m → Fin m → Fin m → (Fin 12 → Fin m) → Formula S m
  satAt T w C E N = towerAt E w (N f0) ∧̇ (codesAt C w E N ∧̇ tableAt T w C E N)

opaque
  unfolding satAt

  Δ₀-satAt : ∀ {m} (T w C E : Fin m) (N : Fin 12 → Fin m) → Δ₀ (satAt T w C E N)
  Δ₀-satAt T w C E N = δ-∧ (Δ₀-towerAt E w (N f0)) (δ-∧ (Δ₀-codesAt C w E N) (Δ₀-tableAt T w C E N))

  satAt-out : ∀ {m} (T w C E : Fin m) (N : Fin 12 → Fin m) (γ : S ^ m)
            → ⟨ γ ⊨ satAt T w C E N ⟩
            → ⟨ γ ⊨ towerAt E w (N f0) ⟩ × (⟨ γ ⊨ codesAt C w E N ⟩ × ⟨ γ ⊨ tableAt T w C E N ⟩)
  satAt-out T w C E N γ h = h

  satAt-in : ∀ {m} (T w C E : Fin m) (N : Fin 12 → Fin m) (γ : S ^ m)
           → ⟨ γ ⊨ towerAt E w (N f0) ⟩ → ⟨ γ ⊨ codesAt C w E N ⟩ → ⟨ γ ⊨ tableAt T w C E N ⟩
           → ⟨ γ ⊨ satAt T w C E N ⟩
  satAt-in T w C E N γ hE hC hT = hE , (hC , hT)
```

THE TWO THEOREMS.  Soundness: a reading of `satAt` at (T, w, C, E)
makes T the graph of the uniform table of w, C the code set and E
the tower, each read both ways.  Completeness: the graph, the code
set and the tower satisfy `satAt`.

```agda
module SatRead {m : ℕ} (T w C E : Fin m) (N : Fin 12 → Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) (tg : Tags γ N) (h : ⟨ γ ⊨ satAt T w C E N ⟩) where
  private
    module SS = SatSound T w C E N γ W qw tg
      (satAt-out T w C E N γ h .fst) (satAt-out T w C E N γ h .snd .fst) (satAt-out T w C E N γ h .snd .snd)
  open SS public using ( C-out; C-in; E-out; E-in; T-out; T-in )

sat-sound : ∀ {m} (T w C E : Fin m) (N : Fin 12 → Fin m) (γ : S ^ m) (W : S)
          → fst (lookup w γ) ≡ fst W → Tags γ N → ⟨ γ ⊨ satAt T w C E N ⟩
          → ((x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup T γ) ⟩
               → Σ[ mx ∈ ⟨ fst x ∈ fst (AllCodes W) ⟩ ] (fst y ≡ fst (Table.val W W x mx)))
          × ((x : S) (mx : ⟨ fst x ∈ fst (AllCodes W) ⟩)
               → ⟨ pr (fst x) (fst (Table.val W W x mx)) ∈ fst (lookup T γ) ⟩)
sat-sound T w C E N γ W qw tg h = SR.T-out , SR.T-in
  where
  module SR = SatRead T w C E N γ W qw tg h

sat-complete : ∀ {m} (T w C E : Fin m) (N : Fin 12 → Fin m) (γ : S ^ m) (W : S)
             → fst (lookup w γ) ≡ fst W
             → fst (lookup T γ) ≡ fst (SatGraph.pairs W)
             → fst (lookup C γ) ≡ fst (AllCodes W)
             → fst (lookup E γ) ≡ fst (Tower.tower W)
             → Tags γ N → ⟨ γ ⊨ satAt T w C E N ⟩
sat-complete T w C E N γ W qw qT qC qE tg =
  satAt-in T w C E N γ
    (TowerHolds.holds E w (N f0) γ W qw qE (tg f0))
    (CodesHolds.holds C w E N γ W qw qC qE tg)
    (SatHolds.holds T w C E N γ W qw qT qC qE tg)
```

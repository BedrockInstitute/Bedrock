# The recursion pinned at a subcode-closed index set

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.Pinned {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; Term; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇∈; ∀̇∈; ∃̇_; ∀̇_ )
import FOL.Absoluteness
open import FOL.Manipulation.Mapping using ( mapFo; mapFo-comp )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′; module VCode )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ} using ( module LCode; prʟ-fst; codeBridge )
open import L.Coding.Expressions {ℓ} using ( consAtL )
open import L.Coding.Closure {ℓ} using ( closedAt; binShapeAt; unShapeAt; bothSameAt; oneSuccAt; succSndAt; binSameClosed-out; unSuccClosed-out; binSuccClosed-out )
open import L.Coding.EnvSet {ℓ} lem using ( envSet )
open import L.Coding.InL {ℓ} using ( sglʟ; cupʟ; tree; tree-inv )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes; AllCodes-out; keyS; codeS )
open import L.Coding.Sat {ℓ} lem using
  ( Sat )
open import L.Coding.Bridge {ℓ} lem using ( asConst )
open import L.Coding.Table {ℓ} lem using
  ( keyʟ; slot; satTable; entry-out; inSlot; ent-slot ) renaming ( total to slotTotal )
open import L.Coding.Quantification {ℓ} using ( sh; i0; i1; i2; i3; i4; i7; i8 ; fstS; sndS )
open import L.Coding.Tower {ℓ} lem using ( nn; towerAt; module TowerRead )
open import L.Coding.CodeDomain {ℓ} lem using
  ( f0; f1; f2; f3; f4; f5; f6; f7; f8; f9; Tags
  ; bigAnd-in; bigAnd-out; module Alphabet )
open import L.Coding.Clauses {ℓ} lem using
  ( tmIs; extB-out; extB-in; ExtFact; ext-unique; tableAt
  ; module Frame; module Clause; module Rel; module RelRead; module Bridge )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( _∷_; lookup )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Foundations.Prelude using ( subst2 )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_; sucV )
open import Cubical.Data.FinData using ( toℕ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ)) using ()
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

The two codings agree at a key. The hierarchy's key and the model's key of the
same formula are the same element.

```agda
module _ (A : S) where
  keyBridge : ∀ {n} (ψ : Formula ⟪ fst A ⟫ n)
            → fst (keyS A ψ) ≡ fst (keyʟ (mapFo (asConst A) ψ))
  keyBridge {n} ψ =
      cong (pr (# n))
        ( cong (λ χ → VCode.⌜ χ ⌝) (sym (mapFo-comp (asConst A) fst ψ))
        ∙ sym (codeBridge (mapFo (asConst A) ψ)) )
    ∙ cong (λ w → pr w (fst LCode.⌜ mapFo (asConst A) ψ ⌝))
        (sym (numeralL-fst n))
    ∙ sym (prʟ-fst (numeralL n) LCode.⌜ mapFo (asConst A) ψ ⌝)
```

A code's constructor and payload, from its tag.

```agda
module Match (W : S) where
  open Alphabet W

  MatchN : ∀ {n} → ℕ → Formula Ab n → V ℓ → Type (ℓ-suc ℓ)
  MatchN {n} 0 ψ r = Σ[ t ∈ Term Ab n ] Σ[ u ∈ Term Ab n ] ((ψ ≡ t ∈̇ u) × (r ≡ pr (ct t) (ct u)))
  MatchN {n} 1 ψ r = Σ[ t ∈ Term Ab n ] Σ[ u ∈ Term Ab n ] ((ψ ≡ t ≐ u) × (r ≡ pr (ct t) (ct u)))
  MatchN {n} 2 ψ r = Σ[ a ∈ Formula Ab n ] Σ[ b ∈ Formula Ab n ] ((ψ ≡ a ∧̇ b) × (r ≡ pr (cd a) (cd b)))
  MatchN {n} 3 ψ r = Σ[ a ∈ Formula Ab n ] Σ[ b ∈ Formula Ab n ] ((ψ ≡ a ∨̇ b) × (r ≡ pr (cd a) (cd b)))
  MatchN {n} 4 ψ r = Σ[ a ∈ Formula Ab n ] Σ[ b ∈ Formula Ab n ] ((ψ ≡ a ⇒̇ b) × (r ≡ pr (cd a) (cd b)))
  MatchN 5 ψ r = (ψ ≡ ⊥̇) × (r ≡ # 0)
  MatchN {n} 6 ψ r = Σ[ a ∈ Formula Ab (suc n) ] ((ψ ≡ ∃̇ a) × (r ≡ cd a))
  MatchN {n} 7 ψ r = Σ[ a ∈ Formula Ab (suc n) ] ((ψ ≡ ∀̇ a) × (r ≡ cd a))
  MatchN {n} 8 ψ r = Σ[ t ∈ Term Ab n ] Σ[ a ∈ Formula Ab (suc n) ] ((ψ ≡ ∀̇∈ t a) × (r ≡ pr (ct t) (cd a)))
  MatchN {n} 9 ψ r = Σ[ t ∈ Term Ab n ] Σ[ a ∈ Formula Ab (suc n) ] ((ψ ≡ ∃̇∈ t a) × (r ≡ pr (ct t) (cd a)))
  MatchN (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) ψ r = Empty.⊥*

  private
    at : ∀ {n} (ψ : Formula Ab n) (j k : ℕ) (r : V ℓ) → pr (# j) (cd ψ) ≡ pr (# j) (cd ψ)
       → MatchN j ψ r → (r' : V ℓ) → pr (# j) r ≡ pr (# k) r' → MatchN k ψ r'
    at ψ j k r _ mj r' e =
      subst2 (λ i x → MatchN i ψ x) (#-inj′ (pr-inj e .fst)) (pr-inj e .snd) mj

  matchAt : ∀ {n} (ψ : Formula Ab n) (k : ℕ) (r : V ℓ) → cd ψ ≡ pr (# k) r → MatchN k ψ r
  matchAt (t ∈̇ u) k r e = at (t ∈̇ u) 0 k _ refl (t , u , (refl , refl)) r e
  matchAt (t ≐ u) k r e = at (t ≐ u) 1 k _ refl (t , u , (refl , refl)) r e
  matchAt (a ∧̇ b) k r e = at (a ∧̇ b) 2 k _ refl (a , b , (refl , refl)) r e
  matchAt (a ∨̇ b) k r e = at (a ∨̇ b) 3 k _ refl (a , b , (refl , refl)) r e
  matchAt (a ⇒̇ b) k r e = at (a ⇒̇ b) 4 k _ refl (a , b , (refl , refl)) r e
  matchAt ⊥̇ k r e = at ⊥̇ 5 k _ refl (refl , refl) r e
  matchAt (∃̇ a) k r e = at (∃̇ a) 6 k _ refl (a , (refl , refl)) r e
  matchAt (∀̇ a) k r e = at (∀̇ a) 7 k _ refl (a , (refl , refl)) r e
  matchAt (∀̇∈ t a) k r e = at (∀̇∈ t a) 8 k _ refl (t , a , (refl , refl)) r e
  matchAt (∃̇∈ t a) k r e = at (∃̇∈ t a) 9 k _ refl (t , a , (refl , refl)) r e
```

A member of the code set at a stated arity decodes.

```agda
  decodeAll : (c : S) → ⟨ fst c ∈ fst (AllCodes W) ⟩ → (n : ℕ) (z : V ℓ) → fst c ≡ pr (# n) z
            → ∥ Σ[ ψ ∈ Formula Ab n ] (z ≡ cd ψ) ∥₁
  decodeAll c c∈ n z e = PT.map
    (λ { (n₁ , ψ₁ , e₁) →
      let q = pr-inj (sym e₁ ∙ e)
          nq = #-inj′ (q .fst)
      in subst (Formula Ab) nq ψ₁ , (sym (q .snd) ∙ sym (cd-subst nq ψ₁)) })
    (AllCodes-out W c c∈)
```

Probe. The uniqueness half of `SatDescribe.SatSound`, at an ARBITRARY
subcode-closed `C`: `codesAt C w E N` is replaced by `closedAt C`, and `Pinned`
is conditional on the formula's key being in `C`.

```agda
module SatSoundC {m : ℕ} (T w C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) (tg : Tags γ N)
  (hE : ⟨ γ ⊨ towerAt E w (N f0) ⟩) (hcl : ⟨ γ ⊨ closedAt C ⟩)
  (hT : ⟨ γ ⊨ tableAt T w C E N ⟩) where
  open Alphabet W
  open Bridge W
  private
    Tv = fst (lookup T γ)
    Cv = fst (lookup C γ)
    Ev = fst (lookup E γ)
    Wv = fst W

    module TR = TowerRead E w (N f0) γ W qw (tg f0) hE
    module Fr = Frame T w C E N γ tg
    module Cl = Clause T w C E N
    module R = Rel T w N

    hTot = hT .fst
    hOn = hT .snd .fst
    hTen = hT .snd .snd

    cl : (k : Fin 10) → ⟨ γ ⊨ Cl.clause k ⟩
    cl = bigAnd-out γ 9 Cl.clause hTen
```

An entry at the key of a formula, and the frame it opens.

```agda
    module Case {n : ℕ} (ψ : Formula Ab n) (k : Fin 10) (rS : S)
      (ep : cd ψ ≡ pr (# (toℕ k)) (fst rS)) (c∈ : ⟨ fst (keyS W ψ) ∈ Cv ⟩)
      (y : S) (mem : ⟨ pr (fst (keyS W ψ)) (fst y) ∈ Tv ⟩) where
      q∈ : ⟨ pr (# n) (fst (envSet W n)) ∈ Ev ⟩
      q∈ = TR.entry-in n
      ep' : fst (codeS W ψ) ≡ pr (fst (lookup (N k) γ)) (fst rS)
      ep' = ep ∙ cong (λ a → pr a (fst rS)) (sym (tg k))
      δ12 : S ^ (12 + m)
      δ12 = Fr.At.δ12 (nn n) (envSet W n) (keyS W ψ) (codeS W ψ) rS y q∈ refl k ep' mem
      rel : ⟨ δ12 ⊨ R.relN (toℕ k) ⟩
      rel = Fr.clause-out k (cl k) (nn n) (envSet W n) (keyS W ψ) (codeS W ψ) rS y q∈ c∈ refl ep mem
      module RR = RelRead T w N δ12
```

The value at a subformula's key, from totality.

```agda
    sub : ∀ {n} (a : Formula Ab n) → ⟨ fst (keyS W a) ∈ Cv ⟩
        → ∥ Σ[ ya ∈ S ] ⟨ pr (fst (keyS W a)) (fst ya) ∈ Tv ⟩ ∥₁
    sub a a∈ = Fr.total-out hTot (keyS W a) a∈

  Pinned : ∀ {n} (ψ : Formula Ab n) → Type (ℓ-suc ℓ)
  Pinned ψ = ⟨ fst (keyS W ψ) ∈ Cv ⟩
           → (y : S) → ⟨ pr (fst (keyS W ψ)) (fst y) ∈ Tv ⟩ → fst y ≡ fst (SatW ψ)

  private
```

The payload of each constructor, as an element of L.

```agda
    payS : ∀ {n} (ψ : Formula Ab n) (k : ℕ) (r : V ℓ) → cd ψ ≡ pr (# k) r → S
    payS ψ k r e = sndS (codeS W ψ) (# k) r e
```

The binary connectives share one case.

```agda
    binCase : ∀ {n} (op : ∀ {j} → Formula S j → Formula S j → Formula S j)
              (opA : Formula Ab n → Formula Ab n → Formula Ab n) (k : Fin 10)
              (a b : Formula Ab n) (code : cd (opA a b) ≡ pr (# (toℕ k)) (pr (cd a) (cd b)))
              (relIs : R.relN (toℕ k) ≡ R.binRel op)
              (bridge : ∀ {j} (env : S ^ j) (ya yb : Fin j)
                      → fst (lookup ya env) ≡ fst (SatW a) → fst (lookup yb env) ≡ fst (SatW b)
                      → ExtFact (fst (SatW (opA a b))) (fst (envSet W n))
                          (λ z → ⟨ (z ∷ env) ⊨ op (var i0 ∈̇ var (suc ya)) (var i0 ∈̇ var (suc yb)) ⟩))
            → (cl2 : ⟨ fst (keyS W (opA a b)) ∈ Cv ⟩
                   → ⟨ fst (keyS W a) ∈ Cv ⟩ × ⟨ fst (keyS W b) ∈ Cv ⟩)
            → Pinned a → Pinned b → Pinned (opA a b)
    binCase {n} op opA k a b code relIs bridge cl2 ia ib c∈ y mem =
      PT.rec (setIsSet _ _) (λ { (ya , ma) → PT.rec (setIsSet _ _) (λ { (yb , mb) →
        PT.rec (setIsSet _ _)
          (λ { (s , s₁ , e₁ , s₂ , e₂ , ext) →
            let env = yb ∷ keyS W b ∷ s₂ ∷ e₂ ∷ ya ∷ keyS W a ∷ s₁ ∷ e₁ ∷ codeS W b ∷ codeS W a ∷ s ∷ K.δ12
                P : S → Type (ℓ-suc ℓ)
                P z = ⟨ (z ∷ env) ⊨ R.binBody op ⟩
            in ext-unique y (SatW (opA a b)) (envSet W n) P ext
                 (bridge env i4 i0 (ia (cl2 c∈ .fst) ya ma) (ib (cl2 c∈ .snd) yb mb)) })
          (K.RR.bin-out op (subst (λ φ → ⟨ K.δ12 ⊨ φ ⟩) relIs K.rel)
             (codeS W a) (codeS W b) (keyS W a) ya (keyS W b) yb refl ma refl mb refl) })
        (sub b (cl2 c∈ .snd)) })
        (sub a (cl2 c∈ .fst))
      where
      module K = Case (opA a b) k (payS (opA a b) (toℕ k) (pr (cd a) (cd b)) code) code c∈ y mem

    quCase : ∀ {n} (q : ∀ {j} → Term S j → Formula S (suc j) → Formula S j)
             (qA : Formula Ab (suc n) → Formula Ab n) (k : Fin 10)
             (a : Formula Ab (suc n)) (code : cd (qA a) ≡ pr (# (toℕ k)) (cd a))
             (relIs : R.relN (toℕ k) ≡ R.quRel q)
             (bridge : ∀ {j} (env : S ^ j) (wi yai : Fin j)
                     → fst (lookup wi env) ≡ Wv → fst (lookup yai env) ≡ fst (SatW a)
                     → ExtFact (fst (SatW (qA a))) (fst (envSet W n))
                         (λ z → ⟨ (z ∷ env) ⊨ q (var (suc wi)) (∃̇∈ (var (suc (suc yai))) (consAtL i0 i1 i2)) ⟩))
           → (cl1 : ⟨ fst (keyS W (qA a)) ∈ Cv ⟩ → ⟨ fst (keyS W a) ∈ Cv ⟩)
           → Pinned a → Pinned (qA a)
    quCase {n} q qA k a code relIs bridge cl1 ia c∈ y mem =
      PT.rec (setIsSet _ _) (λ { (ya , ma) →
        PT.rec (setIsSet _ _)
          (λ { (s , s' , e' , ext) →
            let env = nn (suc n) ∷ s' ∷ ya ∷ keyS W a ∷ s ∷ e' ∷ K.δ12
                P : S → Type (ℓ-suc ℓ)
                P z = ⟨ (z ∷ env) ⊨ R.quBody q ⟩
            in ext-unique y (SatW (qA a)) (envSet W n) P ext (bridge env (sh 18 w) i2 qw (ia (cl1 c∈) ya ma)) })
          (K.RR.qu-out q (subst (λ φ → ⟨ K.δ12 ⊨ φ ⟩) relIs K.rel) (keyS W a) ya (nn (suc n)) ma refl refl) })
        (sub a (cl1 c∈))
      where
      module K = Case (qA a) k (payS (qA a) (toℕ k) (cd a) code) code c∈ y mem

    bqCase : ∀ {n} (q : ∀ {j} → Term S j → Formula S (suc j) → Formula S j)
             (c : ∀ {j} → Formula S j → Formula S j → Formula S j)
             (qA : Term Ab n → Formula Ab (suc n) → Formula Ab n) (k : Fin 10)
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
           → (cl1 : ⟨ fst (keyS W (qA t a)) ∈ Cv ⟩ → ⟨ fst (keyS W a) ∈ Cv ⟩)
           → Pinned a → Pinned (qA t a)
    bqCase {n} q c qA k t a code relIs body bodyIs bridge cl1 ia c∈ y mem =
      PT.rec (setIsSet _ _) (λ { (ya , ma) →
        PT.rec (setIsSet _ _)
          (λ { (s , s₁ , s' , e' , ext) →
            let env = nn (suc n) ∷ s' ∷ ya ∷ keyS W a ∷ s₁ ∷ e' ∷ codeS W a ∷ tS ∷ s ∷ K.δ12
                P : S → Type (ℓ-suc ℓ)
                P z = ⟨ (z ∷ env) ⊨ R.bqBody q c ⟩
            in ext-unique y (SatW (qA t a)) (envSet W n) P ext
                 (subst (λ φ → ExtFact (fst (SatW (qA t a))) (fst (envSet W n)) (λ z → ⟨ (z ∷ env) ⊨ φ ⟩))
                    (bodyIs (sh 21 w) i7 i2 (sh 21 (N f0)) (sh 21 (N f1)))
                    (bridge env (sh 21 w) i7 i2 (sh 21 (N f0)) (sh 21 (N f1)) qw refl (ia (cl1 c∈) ya ma) (tg f0) (tg f1))) })
          (K.RR.bq-out q c (subst (λ φ → ⟨ K.δ12 ⊨ φ ⟩) relIs K.rel) tS (codeS W a) (keyS W a) ya (nn (suc n)) refl ma refl refl) })
        (sub a (cl1 c∈))
      where
      rS : S
      rS = payS (qA t a) (toℕ k) (pr (ct t) (cd a)) code
      tS : S
      tS = fstS rS (ct t) (cd a) refl
      module K = Case (qA t a) k rS code c∈ y mem

    atomCase : ∀ {n} (opA : ∀ {j} → Term Ab j → Term Ab j → Formula Ab j) (k : Fin 10)
               (t u : Term Ab n) (code : cd (opA t u) ≡ pr (# (toℕ k)) (pr (ct t) (ct u)))
               (rel : Formula S (18 + m))
               (relIs : R.relN (toℕ k) ≡ R.atomRel rel)
               (bridge : ∀ (env : S ^ (15 + m)) (wi ti ui N0i N1i : Fin (15 + m))
                       → fst (lookup wi env) ≡ Wv → fst (lookup ti env) ≡ ct t → fst (lookup ui env) ≡ ct u
                       → fst (lookup N0i env) ≡ # 0 → fst (lookup N1i env) ≡ # 1
                       → ExtFact (fst (SatW (opA t u))) (fst (envSet W n)) (λ z → ⟨ (z ∷ env) ⊨ atomEx wi ti ui N0i N1i rel ⟩))
             → Pinned (opA t u)
    atomCase {n} opA k t u code rel relIs bridge c∈ y mem =
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
      module K = Case (opA t u) k rS code c∈ y mem

    memAgree : ∀ {j} (env : S ^ j) (z v x : S)
             → (⟨ (x ∷ v ∷ z ∷ env) ⊨ var i1 ∈̇ var i0 ⟩ → ⟨ fst v ∈ fst x ⟩) × (⟨ fst v ∈ fst x ⟩ → ⟨ (x ∷ v ∷ z ∷ env) ⊨ var i1 ∈̇ var i0 ⟩)
    memAgree env z v x = (λ h → h) , (λ h → h)

    eqAgree : ∀ {j} (env : S ^ j) (z v x : S)
            → (⟨ (x ∷ v ∷ z ∷ env) ⊨ var i1 ≐ var i0 ⟩ → fst v ≡ fst x) × ((fst v ≡ fst x) → ⟨ (x ∷ v ∷ z ∷ env) ⊨ var i1 ≐ var i0 ⟩)
    eqAgree env z v x = (λ h → h) , (λ h → h)
```

The three subcode readers. Each is `closedAt`'s conjunct, read at the key of the
composite formula: this is the whole of what the all-codes hypothesis used to
supply to the recursion.

```agda
    clSame : (n k : ℕ) → ⟨ γ ⊨ binShapeAt C k (bothSameAt C) ⟩
           → (ψ a b : Formula Ab n) → cd ψ ≡ pr (# k) (pr (cd a) (cd b))
           → ⟨ fst (keyS W ψ) ∈ Cv ⟩ → ⟨ fst (keyS W a) ∈ Cv ⟩ × ⟨ fst (keyS W b) ∈ Cv ⟩
    clSame n k h ψ a b e c∈ =
      binSameClosed-out C k γ h (keyS W ψ) (nn n) (codeS W a) (codeS W b) c∈ (cong (pr (# n)) e)

    clBin : (n k : ℕ) (a b : Formula Ab n)
          → ⟨ γ ⊨ binShapeAt C k (bothSameAt C) ⟩
          → (ψ : Formula Ab n) → cd ψ ≡ pr (# k) (pr (cd a) (cd b))
          → ⟨ fst (keyS W ψ) ∈ Cv ⟩ → ⟨ fst (keyS W a) ∈ Cv ⟩ × ⟨ fst (keyS W b) ∈ Cv ⟩
    clBin n k a b h ψ e = clSame n k h ψ a b e

    clQu : (n k : ℕ) (a : Formula Ab (suc n)) (ψ : Formula Ab n)
         → ⟨ γ ⊨ unShapeAt C k (oneSuccAt C) ⟩ → cd ψ ≡ pr (# k) (cd a)
         → ⟨ fst (keyS W ψ) ∈ Cv ⟩ → ⟨ fst (keyS W a) ∈ Cv ⟩
    clQu n k a ψ h e c∈ =
      unSuccClosed-out C k γ h (keyS W ψ) (nn n) (codeS W a) c∈ (cong (pr (# n)) e)

    clBq : (n k : ℕ) (t : Term Ab n) (a : Formula Ab (suc n)) (ψ : Formula Ab n)
         → ⟨ γ ⊨ binShapeAt C k (succSndAt C) ⟩ → cd ψ ≡ pr (# k) (pr (ct t) (cd a))
         → ⟨ fst (keyS W ψ) ∈ Cv ⟩ → ⟨ fst (keyS W a) ∈ Cv ⟩
    clBq n k t a ψ h e c∈ =
      binSuccClosed-out C k γ h (keyS W ψ) (nn n) tS (codeS W a) c∈ (cong (pr (# n)) e)
      where
      pS : S
      pS = sndS (codeS W ψ) (# k) (pr (ct t) (cd a)) e
      tS : S
      tS = fstS pS (ct t) (cd a) refl

  pinned : ∀ {n} (ψ : Formula Ab n) → Pinned ψ
  pinned (t ∈̇ u) = atomCase _∈̇_ f0 t u refl (var i1 ∈̇ var i0) refl
    (λ env wi ti ui N0i N1i qw' qt qu q0 q1 →
      AtomBridge.atomBridge t u env wi ti ui N0i N1i qw' qt qu q0 q1 _∈̇_ (λ v x → ⟨ v ∈ x ⟩)
        (var i1 ∈̇ var i0) (memAgree env) (λ δ h → h) (λ δ h → h))
  pinned (t ≐ u) = atomCase _≐_ f1 t u refl (var i1 ≐ var i0) refl
    (λ env wi ti ui N0i N1i qw' qt qu q0 q1 →
      AtomBridge.atomBridge t u env wi ti ui N0i N1i qw' qt qu q0 q1 _≐_ (λ v x → v ≡ x)
        (var i1 ≐ var i0) (eqAgree env) (λ δ h → h) (λ δ h → h))
  pinned {n} (a ∧̇ b) = binCase _∧̇_ _∧̇_ f2 a b refl refl (andBridge a b) (clBin n 2 a b (hcl .fst) (a ∧̇ b) refl) (pinned a) (pinned b)
  pinned {n} (a ∨̇ b) = binCase _∨̇_ _∨̇_ f3 a b refl refl (orBridge a b) (clBin n 3 a b (hcl .snd .fst) (a ∨̇ b) refl) (pinned a) (pinned b)
  pinned {n} (a ⇒̇ b) = binCase _⇒̇_ _⇒̇_ f4 a b refl refl (impBridge a b) (clBin n 4 a b (hcl .snd .snd .fst) (a ⇒̇ b) refl) (pinned a) (pinned b)
  pinned {n} ⊥̇ c∈ y mem = ext-unique y (SatW ⊥̇) (envSet W n) (λ z → ⟨ (z ∷ K.δ12) ⊨ ⊥̇ ⟩) (extB-out i0 i8 ⊥̇ K.δ12 K.rel) (botBridge n K.δ12)
    where
    module K = Case ⊥̇ f5 (nn 0) refl c∈ y mem
  pinned {n} (∃̇ a) = quCase ∃̇∈ ∃̇_ f6 a refl refl (exBridge a) (clQu n 6 a (∃̇ a) (hcl .snd .snd .snd .fst) refl) (pinned a)
  pinned {n} (∀̇ a) = quCase ∀̇∈ ∀̇_ f7 a refl refl (allBridge a) (clQu n 7 a (∀̇ a) (hcl .snd .snd .snd .snd .fst) refl) (pinned a)
  pinned {n} (∀̇∈ t a) = bqCase ∀̇∈ _⇒̇_ ∀̇∈ f8 t a refl refl bqAll (λ _ _ _ _ _ → refl)
    (λ env wi ti yai N0i N1i qw' qt qa q0 q1 → BqBridge.allInBridge t a env wi ti yai N0i N1i qw' qt qa q0 q1)
    (clBq n 8 t a (∀̇∈ t a) (hcl .snd .snd .snd .snd .snd .fst) refl) (pinned a)
  pinned {n} (∃̇∈ t a) = bqCase ∃̇∈ _∧̇_ ∃̇∈ f9 t a refl refl bqEx (λ _ _ _ _ _ → refl)
    (λ env wi ti yai N0i N1i qw' qt qa q0 q1 → BqBridge.exInBridge t a env wi ti yai N0i N1i qw' qt qa q0 q1)
    (clBq n 9 t a (∃̇∈ t a) (hcl .snd .snd .snd .snd .snd .snd) refl) (pinned a)
```

Probe. `SatHolds` of src/L/GCH/SatDescribe.lagda.md, with the four places that
named the ALL-CODES objects taken as parameters: the value at a key, the decode
of a member, and the two halves of the domain. Nothing else changes.

```agda
module _ (W : S) where
  open Alphabet W
  open Bridge W
  open Match W

  module SatHoldsC {m : ℕ} (T w C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m)
    (qw : fst (lookup w γ) ≡ fst W) (tg : Tags γ N)
    (hE : ⟨ γ ⊨ towerAt E w (N f0) ⟩)
    (val≡ : ∀ {n} (ψ : Formula Ab n) (c yc : S) → fst c ≡ fst (keyS W ψ)
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩ → fst yc ≡ fst (SatW ψ))
    (decode : (c : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩ → (n : ℕ) (z : V ℓ)
            → fst c ≡ pr (# n) z → ∥ Σ[ ψ ∈ Formula Ab n ] (z ≡ cd ψ) ∥₁)
    (tot : (c : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → ∥ Σ[ yc ∈ S ] ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩ ∥₁)
    (onc : (e : S) → ⟨ fst e ∈ fst (lookup T γ) ⟩
         → ∥ Σ[ c ∈ S ] Σ[ yc ∈ S ] ((fst e ≡ pr (fst c) (fst yc)) × ⟨ fst c ∈ fst (lookup C γ) ⟩) ∥₁)
    where
    private
      Tv = fst (lookup T γ)
      Cv = fst (lookup C γ)
      Ev = fst (lookup E γ)
      Wv = fst W
      module Fr = Frame T w C E N γ tg
      module Cl = Clause T w C E N
      module R = Rel T w N
```

An entry of `E` is `(# n, envSet n)`.

```agda
      Arity : (ar F : S) → Type (ℓ-suc ℓ)
      Arity ar F = ∥ Σ[ n ∈ ℕ ] ((fst ar ≡ # n) × (fst F ≡ fst (envSet W n))) ∥₁

      arity : (q ar F : S) → ⟨ fst q ∈ Ev ⟩ → fst q ≡ pr (fst ar) (fst F) → Arity ar F
      module TR = TowerRead E w (N f0) γ W qw (tg f0) hE

      arity q ar F q∈ eq = TR.entry-out ar F (subst (λ u → ⟨ u ∈ Ev ⟩) eq q∈)

      total : ⟨ γ ⊨ Cl.total ⟩
      total = Fr.total-in tot

      onC : ⟨ γ ⊨ Cl.onC ⟩
      onC = Fr.onC-in onc
```

THE CLAUSES. Each is read at its frame; the data of the frame are decoded, and
the relation is filled from the bridge.

```agda
      record Args (k : Fin 10) : Type (ℓ-suc ℓ) where
        field
          q ar F s c p s1 r s2 e yc s3 : S
          q∈ : ⟨ fst q ∈ Ev ⟩
          eq : fst q ≡ pr (fst ar) (fst F)
          c∈ : ⟨ fst c ∈ Cv ⟩
          ec : fst c ≡ pr (fst ar) (fst p)
          ep : fst p ≡ pr (# (toℕ k)) (fst r)
          e∈ : ⟨ fst e ∈ Tv ⟩
          ee : fst e ≡ pr (fst c) (fst yc)

      module Fill (k : Fin 10) (A : Args k) where
        open Args A

        frame : S ^ (12 + m)
        frame = yc ∷ s3 ∷ e ∷ r ∷ s2 ∷ p ∷ s1 ∷ c ∷ F ∷ ar ∷ s ∷ q ∷ γ

        module RR = RelRead T w N frame

        Goal : Type (ℓ-suc ℓ)
        Goal = ⟨ frame ⊨ R.relN (toℕ k) ⟩

        isPropGoal : isProp Goal
        isPropGoal = snd (frame ⊨ R.relN (toℕ k))
```

The extension fact of `yc` over `F`, from the recursion's value at the formula
the code decodes to.

```agda
        transfer : (n : ℕ) (ψ : Formula Ab n) → fst ar ≡ # n → fst F ≡ fst (envSet W n)
                 → fst p ≡ cd ψ → {j : ℕ} (env : S ^ j) (φ : Formula S (1 + j))
                 → ExtFact (fst (SatW ψ)) (fst (envSet W n)) (λ z → ⟨ (z ∷ env) ⊨ φ ⟩)
                 → RR.Ext env φ
        transfer n ψ qa qF qp env φ ext =
          subst2 (λ Y F' → ExtFact Y F' (λ z → ⟨ (z ∷ env) ⊨ φ ⟩))
            (sym (val≡ ψ c yc (ec ∙ cong₂ pr qa qp) (subst (λ u → ⟨ u ∈ Tv ⟩) ee e∈))) (sym qF) ext
```

The value at a subkey.

```agda
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
```

The frame's data, decoded.

```agda
        Data : Type (ℓ-suc ℓ)
        Data = Σ[ n ∈ ℕ ] ((fst ar ≡ # n) × ((fst F ≡ fst (envSet W n))
                 × (Σ[ ψ ∈ Formula Ab n ] ((fst p ≡ cd ψ) × MatchN (toℕ k) ψ (fst r)))))

        data' : ∥ Data ∥₁
        data' = PT.rec squash₁
          (λ { (n , (qa , qF)) → PT.map
            (λ { (ψ , qp) → n , (qa , qF , ψ , (qp , matchAt ψ (toℕ k) (fst r) (sym qp ∙ ep))) })
            (decode c c∈ n (fst p) (ec ∙ cong (λ v → pr v (fst p)) qa)) })
          (arity q ar F q∈ eq)
```

The binary connectives.

```agda
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
            in transfer n (opA a b) qa qF (qp ∙ cong cd qψ) env (R.binBody op)
                 (bridge a b env i4 i0 ya≡ yb≡))
```

The unbounded quantifiers.

```agda
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
            in transfer n (qA a) qa qF (qp ∙ cong cd qψ) env (R.quBody q')
                 (bridge a env (sh 18 w) i2 qw ya≡))
```

The bounded quantifiers.

```agda
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
            in transfer n (qA t a) qa qF (qp ∙ cong cd qψ) env (R.bqBody q' c')
                   (subst (λ φ → ExtFact (fst (SatW (qA t a))) (fst (envSet W n)) (λ z → ⟨ (z ∷ env) ⊨ φ ⟩))
                     (bodyIs (sh 21 w) i7 i2 (sh 21 (N f0)) (sh 21 (N f1)))
                     (bridge t a env (sh 21 w) i7 i2 (sh 21 (N f0)) (sh 21 (N f1)) qw (q'' .fst) ya≡ (tg f0) (tg f1))))
```

The atoms.

```agda
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
            in transfer n (opA t u) qa qF (qp ∙ cong cd qψ) env (R.atomBody rel)
                   (bridge t u env (sh 15 w) i1 i0 (sh 15 (N f0)) (sh 15 (N f1)) qw (q' .fst) (q' .snd) (tg f0) (tg f1)))
```

The constant.

```agda
        botGo : (n : ℕ) (ψ : Formula Ab n) → fst ar ≡ # n → fst F ≡ fst (envSet W n)
              → fst p ≡ cd ψ → ψ ≡ ⊥̇ → ⟨ frame ⊨ R.botRel ⟩
        botGo n ψ qa qF qp qψ = extB-in i0 i8 ⊥̇ frame
          (transfer n ⊥̇ qa qF (qp ∙ cong cd qψ) frame ⊥̇ (botBridge n frame))
```

The dispatch on the tag, one clause each.

```agda
      fill : (k : Fin 10) (A : Args k) → Fill.Data k A → Fill.Goal k A
      fill f0 A (n , (qa , qF , ψ , (qp , (t , u , (qψ , qr))))) =
        Fill.AtomFill.go f0 A _∈̇_ (var i1 ∈̇ var i0)
          (λ t u env wi ti ui N0i N1i qw' qt qu q0 q1 →
            AtomBridge.atomBridge t u env wi ti ui N0i N1i qw' qt qu q0 q1 _∈̇_ (λ v x → ⟨ v ∈ x ⟩)
              (var i1 ∈̇ var i0) (λ z v x → (λ h → h) , (λ h → h)) (λ δ h → h) (λ δ h → h))
          n t u ψ qa qF qp qψ qr
      fill f1 A (n , (qa , qF , ψ , (qp , (t , u , (qψ , qr))))) =
        Fill.AtomFill.go f1 A _≐_ (var i1 ≐ var i0)
          (λ t u env wi ti ui N0i N1i qw' qt qu q0 q1 →
            AtomBridge.atomBridge t u env wi ti ui N0i N1i qw' qt qu q0 q1 _≐_ (λ v x → v ≡ x)
              (var i1 ≐ var i0) (λ z v x → (λ h → h) , (λ h → h)) (λ δ h → h) (λ δ h → h))
          n t u ψ qa qF qp qψ qr
      fill f2 A (n , (qa , qF , ψ , (qp , (a , b , (qψ , qr))))) = Fill.BinFill.go f2 A _∧̇_ _∧̇_ andBridge n a b ψ qa qF qp qψ qr
      fill f3 A (n , (qa , qF , ψ , (qp , (a , b , (qψ , qr))))) = Fill.BinFill.go f3 A _∨̇_ _∨̇_ orBridge n a b ψ qa qF qp qψ qr
      fill f4 A (n , (qa , qF , ψ , (qp , (a , b , (qψ , qr))))) = Fill.BinFill.go f4 A _⇒̇_ _⇒̇_ impBridge n a b ψ qa qF qp qψ qr
      fill f5 A (n , (qa , qF , ψ , (qp , (qψ , qr)))) = Fill.botGo f5 A n ψ qa qF qp qψ
      fill f6 A (n , (qa , qF , ψ , (qp , (a , (qψ , qr))))) = Fill.QuFill.go f6 A ∃̇∈ ∃̇_ exBridge n a ψ qa qF qp qψ qr
      fill f7 A (n , (qa , qF , ψ , (qp , (a , (qψ , qr))))) = Fill.QuFill.go f7 A ∀̇∈ ∀̇_ allBridge n a ψ qa qF qp qψ qr
      fill f8 A (n , (qa , qF , ψ , (qp , (t , a , (qψ , qr))))) =
        Fill.BqFill.go f8 A ∀̇∈ _⇒̇_ ∀̇∈ bqAll (λ _ _ _ _ _ → refl)
          (λ t a env wi ti yai N0i N1i qw' qt qa' q0 q1 → BqBridge.allInBridge t a env wi ti yai N0i N1i qw' qt qa' q0 q1)
          n t a ψ qa qF qp qψ qr
      fill f9 A (n , (qa , qF , ψ , (qp , (t , a , (qψ , qr))))) =
        Fill.BqFill.go f9 A ∃̇∈ _∧̇_ ∃̇∈ bqEx (λ _ _ _ _ _ → refl)
          (λ t a env wi ti yai N0i N1i qw' qt qa' q0 q1 → BqBridge.exInBridge t a env wi ti yai N0i N1i qw' qt qa' q0 q1)
          n t a ψ qa qF qp qψ qr

      clause : (k : Fin 10) → ⟨ γ ⊨ Cl.clause k ⟩
      clause k = Fr.clause-in k (λ q ar F s c p s1 r s2 e yc s3 q∈ eq c∈ ec ep e∈ ee →
        let A : Args k
            A = record { q = q ; ar = ar ; F = F ; s = s ; c = c ; p = p ; s1 = s1 ; r = r ; s2 = s2 ; e = e ; yc = yc ; s3 = s3
                       ; q∈ = q∈ ; eq = eq ; c∈ = c∈ ; ec = ec ; ep = ep ; e∈ = e∈ ; ee = ee }
        in PT.rec (Fill.isPropGoal k A) (fill k A) (Fill.data' k A))

      ten : ⟨ γ ⊨ Cl.ten ⟩
      ten = bigAnd-in γ 9 Cl.clause clause

    holds : ⟨ γ ⊨ tableAt T w C E N ⟩
    holds = total , (onC , ten)
```

The slot instance. The four are supplied at `C` := the slot of one formula and
`T` := its table, from src/L/Coding/Table.lagda.md.

```agda
module _ (W : S) where
  open Alphabet W
  open Bridge W
```

Every member of the slot of `toS ψ` is the key of a formula over the alphabet:
relabelling preserves the slot's tree, so its existing inversion applies.

```agda
  slotAb : ∀ {n} (ψ : Formula Ab n) (x : V ℓ)
         → ⟨ x ∈ fst (slot W (toS ψ)) ⟩
         → ∥ Σ[ m ∈ ℕ ] Σ[ χ ∈ Formula Ab m ] (x ≡ fst (keyS W χ)) ∥₁
  slotAb ψ x h = PT.map
    (λ { (m , χ , e , _) → m , χ , (e ∙ sym (keyBridge W χ)) })
    (tree-inv key key ψ x (subst (λ y → ⟨ x ∈ fst y ⟩) (mapped ψ) h))
    where
    key : ∀ {n} → Formula Ab n → S
    key χ = keyʟ (toS χ)

    mapped : ∀ {n} (χ : Formula Ab n) → slot W (toS χ) ≡ tree key χ
    mapped (t ∈̇ u) = refl
    mapped (t ≐ u) = refl
    mapped ⊥̇ = refl
    mapped χ@(a ∧̇ b) = cong (cupʟ (sglʟ (key χ))) (cong₂ cupʟ (mapped a) (mapped b))
    mapped χ@(a ∨̇ b) = cong (cupʟ (sglʟ (key χ))) (cong₂ cupʟ (mapped a) (mapped b))
    mapped χ@(a ⇒̇ b) = cong (cupʟ (sglʟ (key χ))) (cong₂ cupʟ (mapped a) (mapped b))
    mapped χ@(∃̇ a) = cong (cupʟ (sglʟ (key χ))) (mapped a)
    mapped χ@(∀̇ a) = cong (cupʟ (sglʟ (key χ))) (mapped a)
    mapped χ@(∀̇∈ t a) = cong (cupʟ (sglʟ (key χ))) (mapped a)
    mapped χ@(∃̇∈ t a) = cong (cupʟ (sglʟ (key χ))) (mapped a)

  module SlotHolds {m : ℕ} (T w C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m)
    (qw : fst (lookup w γ) ≡ fst W) (tg : Tags γ N)
    (hE : ⟨ γ ⊨ towerAt E w (N f0) ⟩) {n0 : ℕ} (ψ0 : Formula Ab n0)
    (qT : fst (lookup T γ) ≡ fst (satTable W (toS ψ0)))
    (qC : fst (lookup C γ) ≡ fst (slot W (toS ψ0))) where

    private
      Tv = fst (lookup T γ)
      Cv = fst (lookup C γ)

      val≡ : ∀ {n} (ψ : Formula Ab n) (c yc : S) → fst c ≡ fst (keyS W ψ)
           → ⟨ pr (fst c) (fst yc) ∈ Tv ⟩ → fst yc ≡ fst (SatW ψ)
      val≡ ψ c yc qc h = entry-out W (toS ψ0) (toS ψ) (fst yc)
        (subst2 (λ u v → ⟨ pr u (fst yc) ∈ v ⟩) (qc ∙ keyBridge W ψ) qT h)

      decode : (c : S) → ⟨ fst c ∈ Cv ⟩ → (n : ℕ) (z : V ℓ)
             → fst c ≡ pr (# n) z → ∥ Σ[ ψ ∈ Formula Ab n ] (z ≡ cd ψ) ∥₁
      decode c c∈ n z e = PT.map
        (λ { (n₁ , ψ₁ , e₁) →
          let q = pr-inj (sym e₁ ∙ e)
              nq = #-inj′ (q .fst)
          in subst (Formula Ab) nq ψ₁ , (sym (q .snd) ∙ sym (cd-subst nq ψ₁)) })
        (slotAb ψ0 (fst c) (subst (λ u → ⟨ fst c ∈ u ⟩) qC c∈))

      tot : (c : S) → ⟨ fst c ∈ Cv ⟩ → ∥ Σ[ yc ∈ S ] ⟨ pr (fst c) (fst yc) ∈ Tv ⟩ ∥₁
      tot c c∈ = PT.map
        (λ { (y , h) → y , subst (λ u → ⟨ pr (fst c) (fst y) ∈ u ⟩) (sym qT) h })
        (slotTotal W (toS ψ0) (fst c) (subst (λ u → ⟨ fst c ∈ u ⟩) qC c∈))

      onc : (e : S) → ⟨ fst e ∈ Tv ⟩
          → ∥ Σ[ c ∈ S ] Σ[ yc ∈ S ] ((fst e ≡ pr (fst c) (fst yc)) × ⟨ fst c ∈ Cv ⟩) ∥₁
      onc e e∈ = PT.map
        (λ { (m , χ , (q , _)) →
          let ee = q ∙ prʟ-fst (keyʟ χ) (Sat W χ)
          in keyʟ χ , Sat W χ , (ee , subst (λ u → ⟨ fst (keyʟ χ) ∈ u ⟩) (sym qC)
               (inSlot W (toS ψ0) (fst (keyʟ χ)) (fst (Sat W χ))
                 (subst2 (λ u v → ⟨ u ∈ v ⟩) ee qT e∈))) })
        (ent-slot W (toS ψ0) (fst e) (subst (λ u → ⟨ fst e ∈ u ⟩) qT e∈))

      module SH = SatHoldsC W T w C E N γ qw tg hE val≡ decode tot onc

    holds : ⟨ γ ⊨ tableAt T w C E N ⟩
    holds = SH.holds
```

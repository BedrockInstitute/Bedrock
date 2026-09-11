<!--en-->
# A Δ₀ description of the constructible hierarchy

Later arguments must refer to the hierarchy from within the model. This chapter builds a bounded description of its stage table and proves that the formula recognizes exactly the intended hierarchy.
<!--zh-->
# 可构造层级的 Δ₀ 描述

后续论证需要从模型内部指称可构造层级。本章为层表构造一个有界描述，并证明该公式恰好识别预期的层级。
<!--ja-->
# 構成可能階層の Δ₀ 記述

後の議論では、モデルの内部から構成可能階層を参照する必要がある。本章では段階表の有界な記述を作り、その論理式が意図した階層をちょうど認識することを示す。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.HierarchyDescription {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ⊤̇; ⊥̇; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; checkΔ₀; δ-∧; δ-∃∈ )
open import FOL.Manipulation.ConstantOccurrences using ( countFo )
open import FOL.Manipulation.ConstantMapping using ( embed )
open import FOL.Manipulation.Relabelling using ( embed-⊨; mapΔ₀ )
import FOL.Absoluteness
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction; extensionalV )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using
  ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-in; Lset-out; Lset-mono; 𝒟ₒ )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; #∈ω )
open import L.Axioms.Basic {ℓ} using ( LsetS; Lset-suc )
open import L.Axioms.Numerals {ℓ} using ( numeralL-fst )
open import L.Coding.Expressions {ℓ} using ( sucAtL )
open import L.Coding.NumeralBound {ℓ} lem using ( module Bound )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes )
open import L.Coding.Model {ℓ} using ( container )
open import L.Coding.Quantification {ℓ} using
  ( sh; i0; i1; i2; i3; i8; f0; f1; f2; f3; f4; f5; f6; f7; f8; f9
  ; down; suc-out; suc-in; sndEx; sndAll; bothAll
  ; sndEx-out; sndAll-in; bothAll-in; fillSnd; useSnd; useBoth; sndS )
open import L.Coding.CodeDomain {ℓ} using ( Tags; shN )
open import L.Coding.EnvironmentTower {ℓ} lem using ( nn; module Tower )
open import L.Hierarchy {ℓ} lem using ( hierL-spec; IsHier; hier-out; hier-in; Values; Entries )
open import L.GCH.SkolemHull {ℓ} lem using ( module Cnt; erase-Δ₀; isOrd-at-p; Δ₀-isOrd-at-p; _⊨ₚ_ )
open import L.Coding.SatisfactionGraphSet {ℓ} lem using ( module SatGraph )
open import L.GCH.SatisfactionDescription {ℓ} lem using ( satAt; sat-complete )
open import L.GCH.DefinablePowerSetDescription {ℓ} lem using ( defAt; def-sound; def-complete )
open import L.GCH.AdequateStages {ℓ} lem using ( Adequate; module Adequate; module At; Lset∈suc )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( _∷_; []; map; lookup )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Unit using ( tt )
open import Cubical.Data.FinData using ( toℕ; weakenFin )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet {ℓ} using ( #_; sucV; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ)) using ()
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_; abs₀ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
module SemVᵃ = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
```

The rows. A hierarchy table `f` on the ordinal `p`: every `c ∈ p` has an entry,
and every entry `(c, w)` is a step: `w` holds exactly the members of the
definable power sets of the values recorded below `c`. The definable power set
of a recorded value is named through `satAt` and `defAt`, its three tables and
itself bounded by the witness `z`. The value `a` is the step at `p` from `f`.

At `d ∷ E ∷ C ∷ T ∷ δ`: `d` is the definable power set of `w`, through a
satisfaction table `T` over the code set `C` and the tower `E`, all in `z`.

```agda
defIn : ∀ {k} → Fin k → Fin k → (Fin 10 → Fin k) → Formula S (4 + k) → Formula S k
defIn w z N body =
  ∃̇∈ (var z) (∃̇∈ (var (sh 1 z)) (∃̇∈ (var (sh 2 z)) (∃̇∈ (var (sh 3 z))
    (satAt i3 (sh 4 w) i2 i1 (shN 4 N) ∧̇ (defAt i0 (sh 4 w) i3 i2 (shN 4 N) ∧̇ body)))))

```

Every `x ∈ v` lies in the definable power set of a value recorded at some
`c ∈ b`. Innermost: `d ∷ E ∷ C ∷ T ∷ w ∷ s ∷ q ∷ c ∷ x ∷ γ`.

```agda
intoAt : ∀ {m} → Fin m → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
intoAt v b f z N =
  ∀̇∈ (var v) (∃̇∈ (var (sh 1 b)) (∃̇∈ (var (sh 2 f))
    (sndEx i0 i1 (defIn i0 (sh 5 z) (shN 5 N) (var i8 ∈̇ var i0)))))
```

The definable power set of every value recorded at a `c ∈ b` lies inside `v`.
Innermost: `y ∷ d ∷ E ∷ C ∷ T ∷ w ∷ s ∷ q ∷ c ∷ γ`.

```agda
overAt : ∀ {m} → Fin m → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
overAt v b f z N =
  ∀̇∈ (var b) (∀̇∈ (var (sh 1 f))
    (sndAll i0 i1 (defIn i0 (sh 4 z) (shN 4 N) (∀̇∈ (var i0) (var i0 ∈̇ var (sh 9 v))))))

stepAt : ∀ {m} → Fin m → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
stepAt v b f z N = intoAt v b f z N ∧̇ overAt v b f z N

```

Every `c ∈ b` has an entry, and every entry `(c, w)` is the step at `c`. The
step sits at `w ∷ c ∷ s ∷ q ∷ γ`.

```agda
approxAt : ∀ {m} → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
approxAt f b z N =
    ∀̇∈ (var b) (∃̇∈ (var (sh 1 f)) (sndEx i0 i1 ⊤̇))
  ∧̇ ∀̇∈ (var f) (bothAll i0 (stepAt i0 i1 (sh 4 f) (sh 4 z) (shN 4 N)))


hierAt : ∀ {m} → Fin m → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
hierAt a p f z N = approxAt f p z N ∧̇ stepAt a p f z N

```

The tags are the numerals: the first is empty, each next is the successor of the
one before.

```agda
pins : ∀ {m} → (Fin 10 → Fin m) → Formula S m
pins N =
    ∀̇∈ (var (N f0)) ⊥̇
  ∧̇ ( sucAtL (N f0) (N f1) ∧̇ ( sucAtL (N f1) (N f2) ∧̇ ( sucAtL (N f2) (N f3)
  ∧̇ ( sucAtL (N f3) (N f4) ∧̇ ( sucAtL (N f4) (N f5) ∧̇ ( sucAtL (N f5) (N f6)
  ∧̇ ( sucAtL (N f6) (N f7) ∧̇ ( sucAtL (N f7) (N f8) ∧̇ sucAtL (N f8) (N f9) ))))))))

```

The readers: each row at a variable environment, both ways.

```agda
```

<!--en-->
## The bounded clauses of the hierarchy table

The description pins ten shared constants and combines formulas for definability, one hierarchy step, finite approximations, and the completed table. Keeping every quantifier bounded makes the eventual hierarchy description Δ₀.
<!--zh-->
## 层级表的有界子句

该描述固定十个共享常元，并组合可定义性、单步层级、有限逼近与完整表各自的公式。所有量词都保持有界，因而最终的层级描述是 Δ₀。
<!--ja-->
## 階層表を表す有界な節

この記述は十個の共有定数を固定し、定義可能性、一段階の階層、有限近似、完成した表の論理式を組み合わせる。すべての量化を有界に保つので、最終的な階層記述は Δ₀ になる。
<!--/-->

```agda
module PinsRead {m : ℕ} (N : Fin 10 → Fin m) (γ : S ^ m) where

  pins-out : ⟨ γ ⊨ pins N ⟩ → Tags γ N
  pins-out (h0 , hs) = go
    where
    q0 : fst (lookup (N f0) γ) ≡ # 0
    q0 = extensionalV (λ y → ⇔toPath
      (λ y∈ → Empty.rec* (h0 (down (lookup (N f0) γ) y y∈) y∈))
      (λ y∈ → Empty.rec (∅-empty y (∈∈ₛ {a = y} {b = ∅} .fst y∈))))

    up : (i j : Fin m) (k : ℕ) → ⟨ γ ⊨ sucAtL i j ⟩ → fst (lookup i γ) ≡ # k
       → fst (lookup j γ) ≡ # (suc k)
    up i j k h q = suc-out i j γ h ∙ cong sucV q

    q1 = up (N f0) (N f1) 0 (hs .fst) q0
    q2 = up (N f1) (N f2) 1 (hs .snd .fst) q1
    q3 = up (N f2) (N f3) 2 (hs .snd .snd .fst) q2
    q4 = up (N f3) (N f4) 3 (hs .snd .snd .snd .fst) q3
    q5 = up (N f4) (N f5) 4 (hs .snd .snd .snd .snd .fst) q4
    q6 = up (N f5) (N f6) 5 (hs .snd .snd .snd .snd .snd .fst) q5
    q7 = up (N f6) (N f7) 6 (hs .snd .snd .snd .snd .snd .snd .fst) q6
    q8 = up (N f7) (N f8) 7 (hs .snd .snd .snd .snd .snd .snd .snd .fst) q7
    q9 = up (N f8) (N f9) 8 (hs .snd .snd .snd .snd .snd .snd .snd .snd) q8

    go : Tags γ N
    go zero = q0
    go (suc zero) = q1
    go (suc (suc zero)) = q2
    go (suc (suc (suc zero))) = q3
    go (suc (suc (suc (suc zero)))) = q4
    go (suc (suc (suc (suc (suc zero))))) = q5
    go (suc (suc (suc (suc (suc (suc zero)))))) = q6
    go (suc (suc (suc (suc (suc (suc (suc zero))))))) = q7
    go (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = q8
    go (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = q9

  pins-in : Tags γ N → ⟨ γ ⊨ pins N ⟩
  pins-in tg =
      (λ x x∈ → Empty.rec (∅-empty (fst x) (∈∈ₛ {a = fst x} {b = ∅} .fst
                  (subst (λ u → ⟨ fst x ∈ u ⟩) (tg f0) x∈))))
    , ( st f0 f1 refl , ( st f1 f2 refl , ( st f2 f3 refl , ( st f3 f4 refl , ( st f4 f5 refl , ( st f5 f6 refl
    , ( st f6 f7 refl , ( st f7 f8 refl , st f8 f9 refl ))))))))
    where
    st : (j k : Fin 10) → # (toℕ k) ≡ sucV (# (toℕ j)) → ⟨ γ ⊨ sucAtL (N j) (N k) ⟩
    st j k e = suc-in (N j) (N k) γ (tg k ∙ e ∙ cong sucV (sym (tg j)))
```

The definable power set of the value at `w`, in `z`.

```agda
module DefInRead {k : ℕ} (w z : Fin k) (N : Fin 10 → Fin k) (body : Formula S (4 + k))
  (δ : S ^ k) (tg : Tags δ N) where
  private
    Wv = fst (lookup w δ)
    Zv = fst (lookup z δ)

  δ4 : (T C E d : S) → S ^ (4 + k)
  δ4 T C E d = d ∷ E ∷ C ∷ T ∷ δ

  defIn-out : ⟨ δ ⊨ defIn w z N body ⟩
            → ∥ Σ[ T ∈ S ] Σ[ C ∈ S ] Σ[ E ∈ S ] Σ[ d ∈ S ]
                (⟨ fst d ∈ Zv ⟩ × ((fst d ≡ 𝒟ₒ Wv) × ⟨ δ4 T C E d ⊨ body ⟩)) ∥₁
  defIn-out = PT.rec squash₁ (λ { (T , (T∈ , h1)) → PT.rec squash₁ (λ { (C , (C∈ , h2)) →
    PT.rec squash₁ (λ { (E , (E∈ , h3)) → PT.map (λ { (d , (d∈ , (hs , (hd , hb)))) →
      T , C , E , d , ( d∈ , ( def-sound i0 (sh 4 w) i3 i2 i1 (shN 4 N) (δ4 T C E d) (lookup w δ) refl tg hs hd
                             , hb )) })
      h3 }) h2 }) h1 })

  defIn-in : (W : S) → Wv ≡ fst W → (T C E d : S)
           → ⟨ fst T ∈ Zv ⟩ → ⟨ fst C ∈ Zv ⟩ → ⟨ fst E ∈ Zv ⟩ → ⟨ fst d ∈ Zv ⟩
           → fst T ≡ fst (SatGraph.pairs W) → fst C ≡ fst (AllCodes W) → fst E ≡ fst (Tower.tower W)
           → fst d ≡ 𝒟ₒ (fst W) → ⟨ δ4 T C E d ⊨ body ⟩ → ⟨ δ ⊨ defIn w z N body ⟩
  defIn-in W qw T C E d T∈ C∈ E∈ d∈ qT qC qE qd hb =
    ∣ T , ( T∈ , ∣ C , ( C∈ , ∣ E , ( E∈ , ∣ d , ( d∈ , ( hs
      , ( def-complete i0 (sh 4 w) i3 i2 i1 (shN 4 N) (δ4 T C E d) W qw tg hs qd , hb ))) ∣₁ ) ∣₁ ) ∣₁ ) ∣₁
    where
    hs : ⟨ δ4 T C E d ⊨ satAt i3 (sh 4 w) i2 i1 (shN 4 N) ⟩
    hs = sat-complete i3 (sh 4 w) i2 i1 (shN 4 N) (δ4 T C E d) W qw qT qC qE tg
```

The three witnesses of a carrier `Lset c` and its definable power set, all in a
bound.

```agda
Supply : (Zv : V ℓ) (c : V ℓ) → IsOrd c → Type (ℓ-suc ℓ)
Supply Zv c oc =
    ⟨ fst (SatGraph.pairs (LsetS c oc)) ∈ Zv ⟩
  × ( ⟨ fst (AllCodes (LsetS c oc)) ∈ Zv ⟩
  × ( ⟨ fst (Tower.tower (LsetS c oc)) ∈ Zv ⟩
  × ⟨ Lset (sucV c) ∈ Zv ⟩ ))
```

The step at `(v, b, f)`: `v` is the union of the definable power sets of the
values recorded below `b`.

```agda
module StepRead {m : ℕ} (v b f z : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (tg : Tags γ N) where
  private
    Vv = fst (lookup v γ)
    Bv = fst (lookup b γ)
    Fv = fst (lookup f γ)
    Zv = fst (lookup z γ)

    intoBody : Formula S (5 + m)
    intoBody = defIn i0 (sh 5 z) (shN 5 N) (var i8 ∈̇ var i0)

    overBody : Formula S (4 + m)
    overBody = defIn i0 (sh 4 z) (shN 4 N) (∀̇∈ (var i0) (var i0 ∈̇ var (sh 9 v)))

  step-out : ⟨ γ ⊨ stepAt v b f z N ⟩ → Values (lookup f γ) Bv → Entries (lookup f γ) Bv → Vv ≡ Lset Bv
  step-out (hi , ho) vals ents = extensionalV (λ x → ⇔toPath (fwd x) (bwd x))
    where
    fwd : (x : V ℓ) → ⟨ x ∈ Vv ⟩ → ⟨ x ∈ Lset Bv ⟩
    fwd x x∈ = PT.rec (snd (x ∈ Lset Bv)) (λ { (c , (c∈ , h1)) → PT.rec (snd (x ∈ Lset Bv))
      (λ { (q , (q∈ , h2)) → PT.rec (snd (x ∈ Lset Bv)) (λ { (w , s , (eq , h3)) →
        PT.rec (snd (x ∈ Lset Bv)) (λ { (T , C , E , d , (d∈ , (qd , hx))) →
          Lset-in Bv (fst c) x c∈
            (subst (λ u → ⟨ x ∈ u ⟩)
              (qd ∙ cong 𝒟ₒ (vals c w c∈ (subst (λ u → ⟨ u ∈ Fv ⟩) eq q∈))) hx) })
        (DefInRead.defIn-out i0 (sh 5 z) (shN 5 N) (var i8 ∈̇ var i0) (w ∷ s ∷ q ∷ c ∷ xS ∷ γ) tg h3) })
        (sndEx-out i0 i1 intoBody (q ∷ c ∷ xS ∷ γ) h2) })
      h1 })
      (hi xS x∈)
      where
      xS : S
      xS = down (lookup v γ) x x∈

    bwd : (x : V ℓ) → ⟨ x ∈ Lset Bv ⟩ → ⟨ x ∈ Vv ⟩
    bwd x x∈ = PT.rec (snd (x ∈ Vv)) put (Lset-out Bv x x∈)
      where
      put : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ Bv ⟩ × ⟨ x ∈ 𝒟ₒ (Lset δ) ⟩) → ⟨ x ∈ Vv ⟩
      put (δ , (δ∈ , xD)) = PT.rec (snd (x ∈ Vv))
        (λ { (T , C , E , d , (d∈ , (qd , hsub))) →
          hsub (down d x (subst (λ u → ⟨ x ∈ u ⟩) (sym qd) xD)) (subst (λ u → ⟨ x ∈ u ⟩) (sym qd) xD) })
        (DefInRead.defIn-out i0 (sh 4 z) (shN 4 N) (∀̇∈ (var i0) (var i0 ∈̇ var (sh 9 v)))
          (w ∷ container q c w refl .fst ∷ q ∷ c ∷ γ) tg
          (useSnd i0 (q ∷ c ∷ γ) c w refl overBody i1 refl (ho c δ∈ q (ents c δ∈))))
        where
        c : S
        c = down (lookup b γ) δ δ∈
        q : S
        q = down (lookup f γ) (pr δ (Lset δ)) (ents c δ∈)
        w : S
        w = sndS q δ (Lset δ) refl

  step-in : (ob : IsOrd Bv) → Vv ≡ Lset Bv → Values (lookup f γ) Bv → Entries (lookup f γ) Bv
          → ((c : V ℓ) (oc : IsOrd c) → ⟨ c ∈ Bv ⟩ → Supply Zv c oc)
          → ⟨ γ ⊨ stepAt v b f z N ⟩
  step-in ob vq vals ents sup = into , over
    where
    into : ⟨ γ ⊨ intoAt v b f z N ⟩
    into x x∈ = PT.rec squash₁ put (Lset-out Bv (fst x) (subst (λ u → ⟨ fst x ∈ u ⟩) vq x∈))
      where
      put : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ Bv ⟩ × ⟨ fst x ∈ 𝒟ₒ (Lset δ) ⟩)
          → ⟨ (x ∷ γ) ⊨ ∃̇∈ (var (sh 1 b)) (∃̇∈ (var (sh 2 f)) (sndEx i0 i1 intoBody)) ⟩
      put (δ , (δ∈ , xD)) =
        ∣ c , ( δ∈ , ∣ q , ( ents c δ∈ , fillSnd i0 (q ∷ c ∷ x ∷ γ) c w refl intoBody hb i1 refl ) ∣₁ ) ∣₁
        where
        oδ : IsOrd δ
        oδ = mem-ord {A = Bv} ob δ δ∈
        c : S
        c = down (lookup b γ) δ δ∈
        q : S
        q = down (lookup f γ) (pr δ (Lset δ)) (ents c δ∈)
        w : S
        w = LsetS δ oδ
        s = sup δ oδ δ∈
        hb : ⟨ (w ∷ container q c w refl .fst ∷ q ∷ c ∷ x ∷ γ) ⊨ intoBody ⟩
        hb = DefInRead.defIn-in i0 (sh 5 z) (shN 5 N) (var i8 ∈̇ var i0)
               (w ∷ container q c w refl .fst ∷ q ∷ c ∷ x ∷ γ) tg w refl
               (SatGraph.pairs w) (AllCodes w) (Tower.tower w) (LsetS (sucV δ) (suc-ord oδ))
               (s .fst) (s .snd .fst) (s .snd .snd .fst) (s .snd .snd .snd) refl refl refl (Lset-suc δ)
               (subst (λ u → ⟨ fst x ∈ u ⟩) (sym (Lset-suc δ)) xD)

    over : ⟨ γ ⊨ overAt v b f z N ⟩
    over c c∈ q q∈ = sndAll-in i0 i1 overBody (q ∷ c ∷ γ) (λ w s s∈ w∈ e →
      let wq : fst w ≡ Lset (fst c)
          wq = vals c w c∈ (subst (λ u → ⟨ u ∈ Fv ⟩) e q∈)
          oc : IsOrd (fst c)
          oc = mem-ord {A = Bv} ob (fst c) c∈
          W : S
          W = LsetS (fst c) oc
          s' = sup (fst c) oc c∈
      in DefInRead.defIn-in i0 (sh 4 z) (shN 4 N) (∀̇∈ (var i0) (var i0 ∈̇ var (sh 9 v)))
           (w ∷ s ∷ q ∷ c ∷ γ) tg W wq
           (SatGraph.pairs W) (AllCodes W) (Tower.tower W) (LsetS (sucV (fst c)) (suc-ord oc))
           (s' .fst) (s' .snd .fst) (s' .snd .snd .fst) (s' .snd .snd .snd) refl refl refl (Lset-suc (fst c))
           (λ y y∈d → subst (λ u → ⟨ fst y ∈ u ⟩) (sym vq)
             (Lset-in Bv (fst c) (fst y) c∈ (subst (λ u → ⟨ fst y ∈ u ⟩) (Lset-suc (fst c)) y∈d))))
```

The approximation at `(f, b)`: every value `f` records below the ordinal `b` is
the stage there, by `∈`-induction on the argument, and every argument below `b`
is recorded.

```agda
module ApproxRead {m : ℕ} (f b z : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (tg : Tags γ N) where
  private
    Fv = fst (lookup f γ)
    Bv = fst (lookup b γ)
    Zv = fst (lookup z γ)

    stepBody : Formula S (4 + m)
    stepBody = stepAt i0 i1 (sh 4 f) (sh 4 z) (shN 4 N)

  approx-out : ⟨ γ ⊨ approxAt f b z N ⟩ → IsOrd Bv → Values (lookup f γ) Bv × Entries (lookup f γ) Bv
  approx-out (hd , hs) ob = vals , ents
    where
    P : V ℓ → Type (ℓ-suc ℓ)
    P c = ⟨ c ∈ Bv ⟩ → (w : S) → ⟨ pr c (fst w) ∈ Fv ⟩ → fst w ≡ Lset c

    entryOf : (c : S) → ⟨ fst c ∈ Bv ⟩ → ∥ Σ[ w ∈ S ] ⟨ pr (fst c) (fst w) ∈ Fv ⟩ ∥₁
    entryOf c c∈ = PT.rec squash₁
      (λ { (q , (q∈ , h)) → PT.map (λ { (w , s , (e , _)) → w , subst (λ u → ⟨ u ∈ Fv ⟩) e q∈ })
                              (sndEx-out i0 i1 ⊤̇ (q ∷ c ∷ γ) h) })
      (hd c c∈)

    step : (c : V ℓ) → ((y : V ℓ) → ⟨ y ∈ c ⟩ → P y) → P c
    step c IH c∈ w rec =
      StepRead.step-out i0 i1 (sh 4 f) (sh 4 z) (shN 4 N) env tg
        (useBoth i0 (q ∷ γ) cS w refl stepBody (hs q rec)) vals' ents'
      where
      cS : S
      cS = down (lookup b γ) c c∈
      q : S
      q = down (lookup f γ) (pr c (fst w)) rec
      env : S ^ (4 + m)
      env = w ∷ cS ∷ container q cS w refl .fst ∷ q ∷ γ
      in' : (y : S) → ⟨ fst y ∈ c ⟩ → ⟨ fst y ∈ Bv ⟩
      in' y y∈ = ob .fst {x = c} {y = fst y} y∈ c∈
      vals' : Values (lookup f γ) c
      vals' y w' y∈ rec' = IH (fst y) y∈ (in' y y∈) w' rec'
      ents' : Entries (lookup f γ) c
      ents' y y∈ = PT.rec (snd (pr (fst y) (Lset (fst y)) ∈ Fv))
        (λ { (w' , rec') → subst (λ u → ⟨ pr (fst y) u ∈ Fv ⟩) (IH (fst y) y∈ (in' y y∈) w' rec') rec' })
        (entryOf y (in' y y∈))

    vals : Values (lookup f γ) Bv
    vals c w c∈ rec = ∈-induction {P = P} step (fst c) c∈ w rec

    ents : Entries (lookup f γ) Bv
    ents c c∈ = PT.rec (snd (pr (fst c) (Lset (fst c)) ∈ Fv))
      (λ { (w , rec) → subst (λ u → ⟨ pr (fst c) u ∈ Fv ⟩) (vals c w c∈ rec) rec })
      (entryOf c c∈)

  approx-in : (ob : IsOrd Bv) → IsHier Bv (lookup f γ)
            → ((c : V ℓ) (oc : IsOrd c) → ⟨ c ∈ Bv ⟩ → Supply Zv c oc)
            → ⟨ γ ⊨ approxAt f b z N ⟩
  approx-in ob sp sup = dom , steps
    where
    hout : (c w : S) → ⟨ pr (fst c) (fst w) ∈ Fv ⟩ → ⟨ fst c ∈ Bv ⟩ × (fst w ≡ Lset (fst c))
    hout = hier-out Bv ob (lookup f γ) sp

    hin : (c : S) → ⟨ fst c ∈ Bv ⟩ → ⟨ pr (fst c) (Lset (fst c)) ∈ Fv ⟩
    hin = hier-in Bv ob (lookup f γ) sp

    dom : ⟨ γ ⊨ ∀̇∈ (var b) (∃̇∈ (var (sh 1 f)) (sndEx i0 i1 ⊤̇)) ⟩
    dom c c∈ = ∣ q , ( hin c c∈ , fillSnd i0 (q ∷ c ∷ γ) c w refl ⊤̇ (λ z → z) i1 refl ) ∣₁
      where
      w : S
      w = LsetS (fst c) (mem-ord {A = Bv} ob (fst c) c∈)
      q : S
      q = down (lookup f γ) (pr (fst c) (Lset (fst c))) (hin c c∈)

    steps : ⟨ γ ⊨ ∀̇∈ (var f) (bothAll i0 stepBody) ⟩
    steps q q∈ = bothAll-in i0 stepBody (q ∷ γ) (λ c w s s∈ c∈s w∈s e →
      let rec : ⟨ pr (fst c) (fst w) ∈ Fv ⟩
          rec = subst (λ u → ⟨ u ∈ Fv ⟩) e q∈
          c∈ : ⟨ fst c ∈ Bv ⟩
          c∈ = hout c w rec .fst
          oc : IsOrd (fst c)
          oc = mem-ord {A = Bv} ob (fst c) c∈
      in StepRead.step-in i0 i1 (sh 4 f) (sh 4 z) (shN 4 N) (w ∷ c ∷ s ∷ q ∷ γ) tg oc (hout c w rec .snd)
           (λ d w' d∈ rec' → hout d w' rec' .snd)
           (λ d d∈ → hin d (ob .fst {x = fst c} {y = fst d} d∈ c∈))
           (λ d od d∈ → sup d od (ob .fst {x = fst c} {y = d} d∈ c∈)))
```

The hierarchy row at `(a, p, f)`, both ways.

```agda
module HierRead {m : ℕ} (a p f z : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (tg : Tags γ N) where
  private
    Av = fst (lookup a γ)
    Pv = fst (lookup p γ)
    Zv = fst (lookup z γ)

  hier-sound : ⟨ γ ⊨ hierAt a p f z N ⟩ → IsOrd Pv → Av ≡ Lset Pv
  hier-sound (ha , hs) op = StepRead.step-out a p f z N γ tg hs (ve .fst) (ve .snd)
    where
    ve = ApproxRead.approx-out f p z N γ tg ha op

  hier-complete : (op : IsOrd Pv) → Av ≡ Lset Pv → IsHier Pv (lookup f γ)
                → ((c : V ℓ) (oc : IsOrd c) → ⟨ c ∈ Pv ⟩ → Supply Zv c oc)
                → ⟨ γ ⊨ hierAt a p f z N ⟩
  hier-complete op aq sp sup =
      ApproxRead.approx-in f p z N γ tg op sp sup
    , StepRead.step-in a p f z N γ tg op aq
        (λ c w c∈ rec → hier-out Pv op (lookup f γ) sp c w rec .snd)
        (hier-in Pv op (lookup f γ) sp) sup
```

The three-slot form. Fourteen innermost slots: the ten tags, the table, `a`,
`p`, `z`. Eleven bounded existentials over `z`. The tags are pinned to the
numerals once, at the seal.

```agda
```

<!--en-->
## Reading approximations and the completed hierarchy

The read lemmas identify each syntactic approximation with the actual iterated level construction. Coherence of overlapping approximations then shows that the completed table records exactly the constructible hierarchy below its bound.
<!--zh-->
## 读取逼近与完整层级

诸读引理把每个语法逼近识别为实际迭代的层构造。随后证明重叠逼近彼此相容，由此得到：完整表恰好记录其界以下的可构造层级。
<!--ja-->
## 近似と完成した階層を読む

読み補題は、各構文的近似を実際に反復した階層構成と同定する。重なり合う近似の整合性から、完成した表がその上界より下の構成可能階層を正確に記録することが分かる。
<!--/-->

```agda
module Inner where

  N14 : Fin 10 → Fin 14
  N14 k = weakenFin (weakenFin (weakenFin (weakenFin k)))

  ff aa pp zz : Fin 14
  ff = sh 10 (i0 {3})
  aa = sh 11 (i0 {2})
  pp = sh 12 (i0 {1})
  zz = sh 13 (i0 {0})
```

Sealed: the row is thousands of nodes, and the eleven wraps would normalise
it eleven times. The two readers are the official unfolding.

```agda
  opaque
    inner : Formula S 14
    inner = pins N14 ∧̇ hierAt aa pp ff zz N14

  opaque
    unfolding inner satAt defAt

    Δ₀-inner : Δ₀ inner
    Δ₀-inner = checkΔ₀ inner tt

  opaque
    unfolding inner

    inner-out : (γ : S ^ 14) → ⟨ γ ⊨ inner ⟩ → ⟨ γ ⊨ pins N14 ⟩ × ⟨ γ ⊨ hierAt aa pp ff zz N14 ⟩
    inner-out γ h = h

    inner-in : (γ : S ^ 14) → ⟨ γ ⊨ pins N14 ⟩ → ⟨ γ ⊨ hierAt aa pp ff zz N14 ⟩ → ⟨ γ ⊨ inner ⟩
    inner-in γ h1 h2 = h1 , h2

  lastFin : {n : ℕ} → Fin (suc n)
  lastFin {zero} = zero
  lastFin {suc n} = suc (lastFin {n})
```

One bounded existential over the last slot.

```agda
  wrap : {n : ℕ} → Formula S (suc (suc n)) → Formula S (suc n)
  wrap {n} φ = ∃̇∈ (var (lastFin {n})) φ

  δ-wrap : {n : ℕ} {φ : Formula S (suc (suc n))} → Δ₀ φ → Δ₀ (wrap {n} φ)
  δ-wrap d = δ-∃∈ d

  s13 = wrap {12} inner
  s12 = wrap {11} s13
  s11 = wrap {10} s12
  s10 = wrap {9}  s11
  s9  = wrap {8}  s10
  s8  = wrap {7}  s9
  s7  = wrap {6}  s8
  s6  = wrap {5}  s7
  s5  = wrap {4}  s6
  s4  = wrap {3}  s5
  three : Formula S 3
  three = wrap {2} s4

  Δ₀-three : Δ₀ three
  Δ₀-three =
    δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap
      (δ-wrap (δ-wrap (δ-wrap (δ-wrap Δ₀-inner))))))))))

  opaque
    unfolding inner satAt defAt

    count-three : countFo three ≡ 0
    count-three = refl

  erased : Formula (⊥* {ℓ-suc ℓ}) 3
  erased = Cnt.erase three count-three

  Δ₀-erased : Δ₀ erased
  Δ₀-erased = erase-Δ₀ three count-three Δ₀-three
```

One bounded existential over the last slot, spent into a proposition, and
introduced.

```agda
  unwrap : {n : ℕ} (φ : Formula S (suc (suc n))) (γ : S ^ (suc n)) {P : hProp (ℓ-suc ℓ)}
         → ((x : S) → ⟨ fst x ∈ fst (lookup (lastFin {n}) γ) ⟩ → ⟨ (x ∷ γ) ⊨ φ ⟩ → ⟨ P ⟩)
         → ⟨ γ ⊨ wrap {n} φ ⟩ → ⟨ P ⟩
  unwrap φ γ {P} k h = PT.rec (snd P) (λ { (x , xz , hx) → k x xz hx }) h

  wrap-in : {n : ℕ} (φ : Formula S (suc (suc n))) (γ : S ^ (suc n)) (x : S)
          → ⟨ fst x ∈ fst (lookup (lastFin {n}) γ) ⟩ → ⟨ (x ∷ γ) ⊨ φ ⟩ → ⟨ γ ⊨ wrap {n} φ ⟩
  wrap-in φ γ x m h = ∣ x , (m , h) ∣₁
```

The level description, at the consumer's slot order `(a, p, z)`: `p` is an
ordinal, and the pinned hierarchy row holds with witness `z`.

```agda
```

<!--en-->
## A parameter-free formula for constructible levels

After abstracting the shared constants, `levelFo` says that one set is the constructible level at a given ordinal. Soundness follows from the table readings, while the conditions for an adequate stage provide every witness needed for completeness.
<!--zh-->
## 描述可构造层的无参公式

抽象掉共享常元后，`levelFo` 陈述一个集合是给定序数处的可构造层。可靠性来自表的读法，而充分层的各项条件提供完备性所需的全部见证。
<!--ja-->
## 構成可能な階層を表すパラメータなし論理式

共有定数を抽象すると、`levelFo` は一つの集合が与えられた順序数における構成可能階層であることを述べる。健全性は表の読み方から従い、十分な段階の諸条件が完全性に必要なすべての証人を与える。
<!--/-->

```agda
levelFo : Formula (⊥* {ℓ-suc ℓ}) 3
levelFo = isOrd-at-p ∧̇ Inner.erased

Δ₀-levelFo : Δ₀ levelFo
Δ₀-levelFo = δ-∧ Δ₀-isOrd-at-p Inner.Δ₀-erased
```

The two readings of a parameter-free formula. The class-carrier reading of a Δ₀
formula is its ambient reading at the underlying sets; the ordinality conjunct
at the class carrier.

```agda
read : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : S ^ n)
     → (δ ⊨ embed φ) ≡ (map fst δ ⊨ₚ φ)
read {n} {φ} dφ δ =
    AbsL.abs₀ (mapΔ₀ Empty.rec* dφ) δ
  ∙ embed-⊨ (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ {K = S} fst φ (map fst δ)
  ∙ cong (λ ι → SemVᵃ.At._⊨_ (⊥* {ℓ-suc ℓ}) ι (map fst δ) φ)
         (funExt (λ b → Empty.rec* b))

ord-out : (a p z : S) → ⟨ (a ∷ p ∷ z ∷ []) ⊨ embed isOrd-at-p ⟩ → IsOrd (fst p)
ord-out a p z h =
    ( λ {x} {y} y∈x x∈p → h .fst (down p x x∈p) x∈p (down (down p x x∈p) y y∈x) y∈x )
  , ( λ x x∈p {y} {u} u∈y y∈x →
        h .snd (down p x x∈p) x∈p (down (down p x x∈p) y y∈x) y∈x
          (down (down (down p x x∈p) y y∈x) u u∈y) u∈y )

ord-in : (a p z : S) → IsOrd (fst p) → ⟨ (a ∷ p ∷ z ∷ []) ⊨ embed isOrd-at-p ⟩
ord-in a p z op =
    (λ x x∈p y y∈x → op .fst {x = fst x} {y = fst y} y∈x x∈p)
  , (λ x x∈p y y∈x u u∈y → op .snd (fst x) x∈p {x = fst y} {y = fst u} u∈y y∈x)
```

Soundness. At three constructible sets, the level description makes `a` the
stage at `p`: the eleven existentials are spent, the tags are read as the
numerals, and the hierarchy row is read.

```agda
private
  module Sound where
    open Inner

    finish : (γ : S ^ 14) → ⟨ γ ⊨ inner ⟩ → IsOrd (fst (lookup pp γ))
           → fst (lookup aa γ) ≡ Lset (fst (lookup pp γ))
    finish γ h op = HierRead.hier-sound aa pp ff zz N14 γ tg (inner-out γ h .snd) op
      where
      tg : Tags γ N14
      tg = PinsRead.pins-out N14 γ (inner-out γ h .fst)
```

Perf: the environment is spelled out at every step and never abbreviated.

```agda
    sound-L : (a p z : S) → ⟨ (a ∷ p ∷ z ∷ []) ⊨ embed levelFo ⟩ → fst a ≡ Lset (fst p)
    sound-L a p z (ho , hφ) =
      go (subst (λ ψ → ⟨ (a ∷ p ∷ z ∷ []) ⊨ ψ ⟩) (Cnt.erase-inv three count-three) hφ)
      where
      ordp : IsOrd (fst p)
      ordp = ord-out a p z ho

      G : hProp (ℓ-suc ℓ)
      G = (fst a ≡ Lset (fst p)) , setIsSet (fst a) (Lset (fst p))

      go : ⟨ (a ∷ p ∷ z ∷ []) ⊨ three ⟩ → ⟨ G ⟩
      go =
        unwrap s4 (a ∷ p ∷ z ∷ []) {G} λ F mF →
        unwrap s5 (F ∷ a ∷ p ∷ z ∷ []) {G} λ x9 m9 →
        unwrap s6 (x9 ∷ F ∷ a ∷ p ∷ z ∷ []) {G} λ x8 m8 →
        unwrap s7 (x8 ∷ x9 ∷ F ∷ a ∷ p ∷ z ∷ []) {G} λ x7 m7 →
        unwrap s8 (x7 ∷ x8 ∷ x9 ∷ F ∷ a ∷ p ∷ z ∷ []) {G} λ x6 m6 →
        unwrap s9 (x6 ∷ x7 ∷ x8 ∷ x9 ∷ F ∷ a ∷ p ∷ z ∷ []) {G} λ x5 m5 →
        unwrap s10 (x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ F ∷ a ∷ p ∷ z ∷ []) {G} λ x4 m4 →
        unwrap s11 (x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ F ∷ a ∷ p ∷ z ∷ []) {G} λ x3 m3 →
        unwrap s12 (x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ F ∷ a ∷ p ∷ z ∷ []) {G} λ x2 m2 →
        unwrap s13 (x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ F ∷ a ∷ p ∷ z ∷ []) {G} λ x1 m1 →
        unwrap inner (x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ F ∷ a ∷ p ∷ z ∷ []) {G}
          λ x0 m0 hm →
            finish (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ F ∷ a ∷ p ∷ z ∷ []) hm ordp

```

The theorem, at three ambient sets known to be constructible.

```agda
level-sound : (a p z : V ℓ) → ⟨ isL a ⟩ → ⟨ isL p ⟩ → ⟨ isL z ⟩
            → ⟨ (a ∷ p ∷ z ∷ []) ⊨ₚ levelFo ⟩ → a ≡ Lset p
level-sound a p z la lp lz h =
  Sound.sound-L (a , la) (p , lp) (z , lz)
    (subst ⟨_⟩ (sym (read Δ₀-levelFo ((a , la) ∷ (p , lp) ∷ (z , lz) ∷ []))) h)
```

Completeness. At an adequate stage `γ` and an ordinal `p ∈ γ`, the level
description holds at `(Lset p, p, Lset γ)`: the witnesses are the numerals and
the hierarchy table on `p`, and every set the rows bound by `z` is in `Lset γ`
by adequacy.

```agda
private
  module Complete (lam : V ℓ) (ad : Adequate lam) (p : V ℓ) (op : IsOrd p) (p∈λ : ⟨ p ∈ lam ⟩) where
    open Inner
    open Adequate lam ad using ( ord; succ; ω∈; wit )

    private
      tr : (x y : V ℓ) → ⟨ x ∈ lam ⟩ → ⟨ y ∈ x ⟩ → ⟨ y ∈ lam ⟩
      tr x y x∈ y∈ = ord .fst {x = x} {y = y} y∈ x∈

      ∅∈λ : ⟨ ∅ ∈ lam ⟩
      ∅∈λ = tr ω ∅ ω∈ (#∈ω zero)

      module B = Bound lam ord succ ∅∈λ using ( num∈λ )

      K : V ℓ
      K = Lset lam

      Lset∈K : (c : V ℓ) → ⟨ c ∈ lam ⟩ → ⟨ Lset c ∈ K ⟩
      Lset∈K c c∈ = Lset-mono {α = lam} {β = sucV c} (succ c c∈) (Lset∈suc c)

      num∈K : (k : ℕ) → ⟨ # k ∈ K ⟩
      num∈K k = subst (λ u → ⟨ u ∈ K ⟩) (numeralL-fst k) (B.num∈λ k)

    aS pS zS F : S
    aS = LsetS p op
    pS = p , At.cL p op
    zS = LsetS lam ord
    F = At.hier p op

    E : S ^ 14
    E = nn 0 ∷ nn 1 ∷ nn 2 ∷ nn 3 ∷ nn 4 ∷ nn 5 ∷ nn 6 ∷ nn 7 ∷ nn 8 ∷ nn 9
      ∷ F ∷ aS ∷ pS ∷ zS ∷ []

    tg : Tags E N14
    tg zero = refl
    tg (suc zero) = refl
    tg (suc (suc zero)) = refl
    tg (suc (suc (suc zero))) = refl
    tg (suc (suc (suc (suc zero)))) = refl
    tg (suc (suc (suc (suc (suc zero))))) = refl
    tg (suc (suc (suc (suc (suc (suc zero)))))) = refl
    tg (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
    tg (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = refl
    tg (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = refl

    sup : (c : V ℓ) (oc : IsOrd c) → ⟨ c ∈ p ⟩ → Supply K c oc
    sup c oc c∈ = w .snd .snd .fst , ( w .snd .fst , ( w .snd .snd .snd , Lset∈K (sucV c) (succ c c∈λ) ))
      where
      c∈λ : ⟨ c ∈ lam ⟩
      c∈λ = tr p c p∈λ c∈
      w = wit c c∈λ oc

    hm : ⟨ E ⊨ inner ⟩
    hm = inner-in E (PinsRead.pins-in N14 E tg)
           (HierRead.hier-complete aa pp ff zz N14 E tg op refl (hierL-spec p (At.cL p op) op) sup)

    FK : ⟨ fst F ∈ K ⟩
    FK = wit p p∈λ op .fst
```

The eleven bounded existentials, spent with the table and the numerals.

```agda
    h3 : ⟨ (aS ∷ pS ∷ zS ∷ []) ⊨ three ⟩
    h3 =
      wrap-in s4 (aS ∷ pS ∷ zS ∷ []) F FK (
      wrap-in s5 (F ∷ aS ∷ pS ∷ zS ∷ []) (nn 9) (num∈K 9) (
      wrap-in s6 (nn 9 ∷ F ∷ aS ∷ pS ∷ zS ∷ []) (nn 8) (num∈K 8) (
      wrap-in s7 (nn 8 ∷ nn 9 ∷ F ∷ aS ∷ pS ∷ zS ∷ []) (nn 7) (num∈K 7) (
      wrap-in s8 (nn 7 ∷ nn 8 ∷ nn 9 ∷ F ∷ aS ∷ pS ∷ zS ∷ []) (nn 6) (num∈K 6) (
      wrap-in s9 (nn 6 ∷ nn 7 ∷ nn 8 ∷ nn 9 ∷ F ∷ aS ∷ pS ∷ zS ∷ []) (nn 5) (num∈K 5) (
      wrap-in s10 (nn 5 ∷ nn 6 ∷ nn 7 ∷ nn 8 ∷ nn 9 ∷ F ∷ aS ∷ pS ∷ zS ∷ []) (nn 4) (num∈K 4) (
      wrap-in s11 (nn 4 ∷ nn 5 ∷ nn 6 ∷ nn 7 ∷ nn 8 ∷ nn 9 ∷ F ∷ aS ∷ pS ∷ zS ∷ []) (nn 3) (num∈K 3) (
      wrap-in s12 (nn 3 ∷ nn 4 ∷ nn 5 ∷ nn 6 ∷ nn 7 ∷ nn 8 ∷ nn 9 ∷ F ∷ aS ∷ pS ∷ zS ∷ []) (nn 2) (num∈K 2) (
      wrap-in s13 (nn 2 ∷ nn 3 ∷ nn 4 ∷ nn 5 ∷ nn 6 ∷ nn 7 ∷ nn 8 ∷ nn 9 ∷ F ∷ aS ∷ pS ∷ zS ∷ []) (nn 1) (num∈K 1) (
      wrap-in inner (nn 1 ∷ nn 2 ∷ nn 3 ∷ nn 4 ∷ nn 5 ∷ nn 6 ∷ nn 7 ∷ nn 8 ∷ nn 9 ∷ F ∷ aS ∷ pS ∷ zS ∷ []) (nn 0) (num∈K 0)
        hm))))))))))

    hφ : ⟨ (aS ∷ pS ∷ zS ∷ []) ⊨ embed erased ⟩
    hφ = subst (λ ψ → ⟨ (aS ∷ pS ∷ zS ∷ []) ⊨ ψ ⟩) (sym (Cnt.erase-inv three count-three)) h3

    complete : ⟨ (Lset p ∷ p ∷ Lset lam ∷ []) ⊨ₚ levelFo ⟩
    complete = subst ⟨_⟩ (read Δ₀-levelFo (aS ∷ pS ∷ zS ∷ [])) (ord-in aS pS zS op , hφ)
```

The theorem.

```agda
level-complete : (γ : V ℓ) → Adequate γ → (p : V ℓ) → IsOrd p → ⟨ p ∈ γ ⟩
               → ⟨ (Lset p ∷ p ∷ Lset γ ∷ []) ⊨ₚ levelFo ⟩
level-complete γ ad p op p∈ = Complete.complete γ ad p op p∈
```

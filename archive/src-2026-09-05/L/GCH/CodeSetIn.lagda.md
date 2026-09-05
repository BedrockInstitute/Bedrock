# The whole code set of a carrier sits in a closed stage

<!--en-->
`AllCodes A` is cut out of a stage by separation, and nothing so far said where
that stage, or the set, sits in the tower. This chapter places the set: over a
carrier `A` born before a closed limit `γ` (with `ω` below `γ`), the whole code
set is an element of `Lset γ`.

Each individual key already lands in `Lset γ` (`keyS-in-carrier-lim`). What is
new is the set of all of them. The route is the one `envSetNumeralin` uses for
the environment sets. First a containment: every key sits at some finite iterate
of one fixed stage below `γ`, hence in the `+ω` block over it, and so does every
set the code predicate quantifies over (numerals, codes, closures). Then a
membership: a subset of a level is a member of the next level only when it is
definable there, so the chapter writes a bounded description of "this is a key",
carves the stage by it, and identifies the carve with `AllCodes A` by
extensionality. The delivered description `isCodeAny A` cannot be carved (its
existentials are unbounded), so the chapter writes the bounded form itself:
every quantifier is bounded by `ωʟ`, by the carrier `A`, or by the `+ω` stage
holding the codes, and each bounded reading is connected to the delivered one by
its own adequacy equation.
<!--zh-->
`AllCodes A` 是经分离从一个阶段里切出来的，而迄今没有话说清那个阶段、乃至这个集合本身住在塔的何处。本章安置这个集合：在闭极限 `γ` 之前诞生的载体 `A` (且 `ω` 在 `γ` 之下) 上，全码集是 `Lset γ` 的元素。

每个单独的键早已落入 `Lset γ` (`keyS-in-carrier-lim`)。新的是「它们的全体」这个集合。路线正是 `envSetNumeralin` 对诸环境集所用的那条。先作包含：每个键都落在 `γ` 之下某个固定阶段的某个有穷迭代里，因而落在其上的 `+ω` 块中，码谓词所量化的每个集合 (诸数码、诸码、诸闭包) 也是。再作隶属：一个层级的子集，唯有在其中**可定义**时才是下一层的成员，故本章亲手写出「这是一把键」的有界描述，用它雕刻该阶段，再经外延性把刻出的集合与 `AllCodes A` 认同。交付的描述 `isCodeAny A` 不能用来雕刻 (它的存在量词无界)，故本章自己写出有界形式：每个量词都以 `ωʟ`、以载体 `A`、或以装着诸码的 `+ω` 阶段为界，而每条有界读式都由它自己的适足等式接到交付的那条上。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.CodeSetIn {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import FOL.Syntax
  using ( Formula; Term; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.Bounding using ( BoundedFo )
open import FOL.LevyHierarchy
  using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-¬; δ-⊤; δ-∃∈; δ-∀∈; δ-⇒ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj; module VCode )
open import FOL.Manipulation.Relabelling using ( mapTm; mapFo )
open import V.Model {ℓ} using ( ∈sucV-inl; self∈sucV )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-layer; layer-trans
        ; Lset-mono; Lset-out; Lset→isL; 𝒟ₒ; 𝒟ₒ∋⊆; 𝒟ₒ-intro )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; ω-ord )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡; ord∈Lset-suc )
open import L.Ordinal.StageArith {ℓ} lem
  using ( sucIter; +ω; +ω-mem; +ω-iter; +ω-ord; closedω )
open import L.Choice.Name {ℓ} lem using ( numeral∈limit )
open import L.Axioms.Basic {ℓ}
  using ( LsetS; Lset-suc; pr∈Lset-suc; sgl∈Lset-suc; pair∈Lset-suc )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ; ω-specL )
open import L.Axioms.Separation {ℓ} lem using ( module AtStage )
open import L.GCH.Placement {ℓ} lem
  using ( module Closer; module Climb; sucIter-shift; pr∈iter
        ; prAtL-triv; iter-up )
open import L.Coding.Key {ℓ} lem using ( union∈Lset-suc )
open import L.Coding.CodeSet {ℓ} lem
  using ( codeS; keyS; AllCodes; AllCodes-in; AllCodes-out; IsKeyOverAny
        ; key∈AllCodes )
open import L.Coding.InL {ℓ}
  using ( key; closure; closure-inv; keyL; codeL; codeTmL; key∈closure )
open import L.Coding.Closed {ℓ} using ( clo; closureClosed )
open import L.Coding.Shape {ℓ}
  using ( shapes; shapedAt; shaped-in; shaped-out; ShapeWit
        ; bothTm; fstTm; noneB; zeroPay; noneU )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; tagAtL-adequate; tagPairAtL-adequate
        ; arityTagAtL-adequate; arityTagPairAtL-adequate
        ; appAt; appAt-adequate; sucAtL; sucAtL-adequate; tagAtL; tagPairAtL
        ; arityTagAtL; arityTagPairAtL
        ; closedAt; binShapeAt; unShapeAt
        ; bothSameAt; oneSameAt
        ; binSameClosed-in; unSameClosed-in; unSuccClosed-in; binSuccClosed-in
        ; binSameClosed-out; unSameClosed-out; unSuccClosed-out; binSuccClosed-out )
open import L.Coding.Base {ℓ} using ( Δ₀-prAt )
open import L.Coding.Environment {ℓ} using ( Δ₀-sucAt )
open import L.Absoluteness {ℓ} using ( Δ₀-liftFo )
open import L.Coding.Recover {ℓ} using ( keyOf-fst; module Decode )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum as Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Vec using ( Vec; []; _∷_; lookup )
open import Cubical.Data.FinData as FD using ( Fin; toℕ )
open import Cubical.Data.FinData.Properties using ( toℕ<n )
open import Cubical.Data.Nat.Order using ( pred-≤-pred; ≤-split; _<_ )
open import Cubical.Data.Nat.Order using ( ¬-<-zero )
open import Cubical.Data.Nat.Properties using ( +-suc; +-zero; +-comm )
open import Cubical.Data.Unit using ( tt* )
import Cubical.Data.Empty as Empty
open import Cubical.Foundations.Function using ( _∘_ )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber; _⊆_; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ⁅_⁆s; ⁅_,_⁆; _∪_; ⋃_; pairing-ax; module InfinitySet )
open InfinitySet {ℓ} using ( #_; sucV; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ hiding ( S )
open hPropStructure 𝒮ʟ using ( S ) renaming ( _∈ˢ_ to _∈ˢʟ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- SECTION 0.  Small stage-arithmetic helpers.
-- =====================================================================


-- A numeral below a numeral, by the index order.
#∈# : (a b : ℕ) → a < b → ⟨ (# a) ∈ˢ (# b) ⟩
#∈# a zero le = Empty.rec (¬-<-zero le)
#∈# a (suc b) le = step (≤-split (pred-≤-pred le))
  where
  step : (a < b) ⊎ (a ≡ b) → ⟨ (# a) ∈ˢ (# suc b) ⟩
  step (inl a<b) = ∈sucV-inl {A = # b} {x = # a} (#∈# a b a<b)
  step (inr e) = h≡ e
    where
    h≡ : a ≡ b → ⟨ (# a) ∈ˢ sucV (# b) ⟩
    h≡ e = subst (λ w → ⟨ (# a) ∈ˢ sucV w ⟩) (cong (#_) e) (self∈sucV (# a))

-- An element sits above every finite iterate of itself.
iter-self∈ : (j : ℕ) (x : V ℓ) → ⟨ x ∈ˢ sucIter (suc j) x ⟩
iter-self∈ zero    x = self∈sucV x
iter-self∈ (suc j) x =
  ∈sucV-inl {A = sucIter (suc j) x} {x = x} (iter-self∈ j x)

-- Membership is preserved along the iterate chain (sucIter-shift composed).
iter-lift : (j : ℕ) (x y : V ℓ) → ⟨ x ∈ˢ y ⟩ → ⟨ x ∈ˢ sucIter j y ⟩
iter-lift zero    x y h = h
iter-lift (suc j) x y h = ∈sucV-inl {A = sucIter j y} {x = x} (iter-lift j x y h)

-- =====================================================================
-- SECTION 1.  The carrier stage: below γ, holding A, the numerals, ω.
-- =====================================================================

module CarrierStage (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
                    (ω∈γ : ⟨ ω ∈ˢ γ ⟩)
                    (A : S) (hA : ⟨ fst A ∈ˢ Lset γ ⟩)
                    (δ : V ℓ) (δ∈γ : ⟨ δ ∈ˢ γ ⟩)
                    (A∈sδ : ⟨ fst A ∈ˢ Lset (sucV δ) ⟩) where

  open Closer γ oγ clγ

  oδ : IsOrd δ
  oδ = mem-ord {A = γ} oγ δ δ∈γ

  triωδ : Tri ω δ
  triωδ = ord-tri ω ω-ord δ oδ

  -- The merge of δ and ω, one successor up: below γ, holding everything.
  private
    σ-of : Tri ω δ → V ℓ
    σ-of (inl _)       = sucV δ
    σ-of (inr (inl _)) = sucV δ
    σ-of (inr (inr _)) = sucV ω

    o-of : (t : Tri ω δ) → IsOrd (σ-of t)
    o-of (inl _)       = suc-ord oδ
    o-of (inr (inl _)) = suc-ord oδ
    o-of (inr (inr _)) = suc-ord ω-ord

    ∈γ-of : (t : Tri ω δ) → ⟨ σ-of t ∈ˢ γ ⟩
    ∈γ-of (inl _)       = suc∈γ δ δ∈γ
    ∈γ-of (inr (inl _)) = suc∈γ δ δ∈γ
    ∈γ-of (inr (inr _)) = suc∈γ ω ω∈γ

    ω∈sδ : ⟨ ω ∈ˢ δ ⟩ → ⟨ ω ∈ˢ sucV δ ⟩
    ω∈sδ x = ∈sucV-inl {A = δ} {x = ω} x

    A-of : (t : Tri ω δ) → ⟨ fst A ∈ˢ Lset (σ-of t) ⟩
    A-of (inl _)       = A∈sδ
    A-of (inr (inl _)) = A∈sδ
    A-of (inr (inr δ∈ω)) =
      Lset-mono {α = sucV ω} {β = sucV δ} sucδ∈sucω A∈sδ
      where
      sucδ∈sucω : ⟨ sucV δ ∈ˢ sucV ω ⟩
      sucδ∈sucω = Sum.rec
        (∈sucV-inl {A = ω} {x = sucV δ})
        (λ e → subst (λ w → ⟨ sucV δ ∈ˢ sucV w ⟩) e (self∈sucV (sucV δ)))
        (suc∈or≡ δ ω oδ ω-ord δ∈ω)

    num-of : (t : Tri ω δ) (k : ℕ) → ⟨ (# k) ∈ˢ Lset (σ-of t) ⟩
    num-of (inl ω∈δ) k =
      Lset-mono {α = sucV δ} {β = ω} (ω∈sδ ω∈δ) (numeral∈limit k)
    num-of (inr (inl e)) k =
      Lset-mono {α = sucV δ} {β = ω}
        (subst (λ w → ⟨ ω ∈ˢ sucV w ⟩) e (self∈sucV ω)) (numeral∈limit k)
    num-of (inr (inr _)) k =
      Lset-mono {α = sucV ω} {β = ω} (self∈sucV ω) (numeral∈limit k)

    ω-of : (t : Tri ω δ) → ⟨ ω ∈ˢ Lset (σ-of t) ⟩
    ω-of (inl ω∈δ) =
      Lset-mono {α = sucV δ} {β = sucV ω} (sucω∈sδ ω∈δ) (ord∈Lset-suc ω ω-ord)
      where
      sucω∈sδ : ⟨ ω ∈ˢ δ ⟩ → ⟨ sucV ω ∈ˢ sucV δ ⟩
      sucω∈sδ x = Sum.rec
        (∈sucV-inl {A = δ} {x = sucV ω})
        (λ e → subst (λ w → ⟨ sucV ω ∈ˢ sucV w ⟩) e (self∈sucV (sucV ω)))
        (suc∈or≡ ω δ ω-ord oδ x)
    ω-of (inr (inl e)) =
      subst (λ w → ⟨ ω ∈ˢ Lset (sucV w) ⟩) e (ord∈Lset-suc ω ω-ord)
    ω-of (inr (inr _)) = ord∈Lset-suc ω ω-ord

  σ₀ : V ℓ
  σ₀ = σ-of triωδ

  oσ₀ : IsOrd σ₀
  oσ₀ = o-of triωδ

  σ₀∈γ : ⟨ σ₀ ∈ˢ γ ⟩
  σ₀∈γ = ∈γ-of triωδ

  A∈σ₀ : ⟨ fst A ∈ˢ Lset σ₀ ⟩
  A∈σ₀ = A-of triωδ

  num∈σ₀ : (k : ℕ) → ⟨ (# k) ∈ˢ Lset σ₀ ⟩
  num∈σ₀ = num-of triωδ

  ωL∈σ₀ : ⟨ ω ∈ˢ Lset σ₀ ⟩
  ωL∈σ₀ = ω-of triωδ

  -- ===================================================================
  -- SECTION 2.  The block λ₀, the carving stage α, the constant B*.
  -- ===================================================================

  λ₀ : V ℓ
  λ₀ = +ω σ₀

  oλ₀ : IsOrd λ₀
  oλ₀ = +ω-ord σ₀ oσ₀

  λ₀∈γ : ⟨ λ₀ ∈ˢ γ ⟩
  λ₀∈γ = clγ σ₀ σ₀∈γ

  -- The block member: two iterates up, so that pairs of its members
  -- (which climb two successors) stay inside it.
  iter-ord : (n : ℕ) → IsOrd λ₀ → IsOrd (sucIter n λ₀)
  iter-ord zero ou = ou
  iter-ord (suc n) ou = suc-ord (iter-ord n ou)

  τ : V ℓ
  τ = sucV (sucV λ₀)

  oτ : IsOrd τ
  oτ = suc-ord (suc-ord oλ₀)

  τ∈γ : ⟨ τ ∈ˢ γ ⟩
  τ∈γ = suc∈γ (sucV λ₀) (suc∈γ λ₀ λ₀∈γ)

  up : (x : V ℓ) → ⟨ x ∈ˢ Lset λ₀ ⟩ → ⟨ x ∈ˢ Lset τ ⟩
  up = iter-up λ₀ 2

  α : V ℓ
  α = sucV τ

  oα : IsOrd α
  oα = suc-ord oτ

  α∈γ : ⟨ α ∈ˢ γ ⟩
  α∈γ = suc∈γ τ τ∈γ

  B* : S
  B* = LsetS τ oτ

  -- two-iterate bump.


  B*∈Lα : ⟨ Lset τ ∈ˢ Lset α ⟩
  B*∈Lα = subst (λ w → ⟨ Lset τ ∈ˢ w ⟩) (sym (Lset-suc τ))
    (𝒟ₒ-intro (Lset τ) (Lset τ) ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset τ) ∣₁)

  ω∈Lα : ⟨ ω ∈ˢ Lset α ⟩
  ω∈Lα = Lset-mono {α = α} {β = τ} (self∈sucV τ)
    (up ω (Lset-mono {α = λ₀} {β = σ₀} (+ω-mem σ₀) ωL∈σ₀))

  A∈Lα : ⟨ fst A ∈ˢ Lset α ⟩
  A∈Lα = Lset-mono {α = α} {β = τ} (self∈sucV τ)
    (up (fst A) (Lset-mono {α = λ₀} {β = σ₀} (+ω-mem σ₀) A∈σ₀))

  num∈Lα : (k : ℕ) → ⟨ fst (numeralL k) ∈ˢ Lset α ⟩
  num∈Lα k = Lset-mono {α = α} {β = τ} (self∈sucV τ)
    (up _ (Lset-mono {α = λ₀} {β = σ₀} (+ω-mem σ₀)
      (subst (λ w → ⟨ w ∈ˢ Lset σ₀ ⟩) (sym (numeralL-fst k)) (num∈σ₀ k))))

  -- Anything placed at a finite iterate of σ₀ sits in the block.
  absorb : (n : ℕ) (x : V ℓ) → ⟨ x ∈ˢ Lset (sucIter n σ₀) ⟩ → ⟨ x ∈ˢ Lset λ₀ ⟩
  absorb n x h = Lset-mono {α = λ₀} {β = sucIter n σ₀} (+ω-iter n σ₀) h

  -- And the block sits below γ, so absorbed things sit in Lset γ.
  absorbed∈γ : (x : V ℓ) → ⟨ x ∈ˢ Lset λ₀ ⟩ → ⟨ x ∈ˢ Lset γ ⟩
  absorbed∈γ x h = Lset-mono {α = γ} {β = τ} τ∈γ (up x h)

  -- ===================================================================
  -- SECTION 3.  Codes, keys, and closures, placed at finite iterates.
  -- ===================================================================

  ι : ⟪ fst A ⟫ → V ℓ
  ι = ⟪ fst A ⟫↪

  ι∈ : (m : ⟪ fst A ⟫) → ⟨ ι m ∈ fst A ⟩
  ι∈ m = ∈∈ₛ {a = ι m} {b = fst A} .snd (∈ₛ⟪ fst A ⟫↪ m)

  ιL : (m : ⟪ fst A ⟫) → ⟨ isL (ι m) ⟩
  ιL m = isL-trans {x = fst A} {y = ι m} (ι∈ m) (snd A)

  hfc : (m : ⟪ fst A ⟫) → ⟨ ι m ∈ˢ Lset σ₀ ⟩
  hfc m = layer-trans (Lset-layer σ₀) {x = fst A} {y = ι m} (ι∈ m) A∈σ₀

  hnum : (k : ℕ) → ⟨ (# k) ∈ˢ Lset σ₀ ⟩
  hnum = num∈σ₀

  term∈iter : ∀ {n} (t : Term ⟪ fst A ⟫ n)
            → Σ[ j ∈ ℕ ] ⟨ VCode.⌜ mapTm ι t ⌝ᵗ ∈ˢ Lset (sucIter j σ₀) ⟩
  term∈iter t = T.codeTm∈iter t
    where
    module T = Climb σ₀ ι hfc hnum

  code∈iter : ∀ {n} (φ : Formula ⟪ fst A ⟫ n)
            → Σ[ j ∈ ℕ ] ⟨ VCode.⌜ mapFo ι φ ⌝ ∈ˢ Lset (sucIter j σ₀) ⟩
  code∈iter φ = C.code∈iter φ
    where
    module C = Climb σ₀ ι hfc hnum

  key∈iter : ∀ {n} (φ : Formula ⟪ fst A ⟫ n)
           → Σ[ j ∈ ℕ ] ⟨ pr (# n) (VCode.⌜ mapFo ι φ ⌝) ∈ˢ Lset (sucIter j σ₀) ⟩
  key∈iter {n} φ = _ , pr∈iter σ₀ zero j (# n) (VCode.⌜ mapFo ι φ ⌝) (hnum n) h
    where
    j = fst (code∈iter φ)
    h = snd (code∈iter φ)

  -- Singleton at an iterate stays one iterate up.
  sgl∈iter : (j : ℕ) (x : V ℓ)
           → ⟨ x ∈ˢ Lset (sucIter j σ₀) ⟩ → ⟨ ⁅ x ⁆s ∈ˢ Lset (sucIter (suc j) σ₀) ⟩
  sgl∈iter j x h = sgl∈Lset-suc (sucIter j σ₀) x h

  -- Iterates of σ₀ form a chain: sucIter ja σ₀ sits below every later
  -- iterate, so a member of an earlier stage is a member of a later one.
  iter-mono : (ja jb : ℕ) (x : V ℓ)
            → ⟨ x ∈ˢ Lset (sucIter ja σ₀) ⟩
            → ⟨ x ∈ˢ Lset (sucIter (ja + jb) σ₀) ⟩
  iter-mono ja zero x h =
    subst (λ w → ⟨ x ∈ˢ Lset w ⟩) (cong (λ w → sucIter w σ₀) (sym (+-zero ja))) h
  iter-mono ja (suc jb) x h =
    subst (λ w → ⟨ x ∈ˢ Lset w ⟩) (sym (sucIter-shift σ₀ ja (suc jb)))
      (Lset-mono {α = sucIter (suc jb) (sucIter ja σ₀)} {β = sucIter ja σ₀}
        (iter-self∈ jb (sucIter ja σ₀)) h)

  -- Union of two members of two iterates, at the merged iterate.
  cup∈iter : (ja jb : ℕ) (x y : V ℓ)
           → ⟨ x ∈ˢ Lset (sucIter ja σ₀) ⟩ → ⟨ y ∈ˢ Lset (sucIter jb σ₀) ⟩
           → ⟨ (x ∪ y) ∈ˢ Lset (sucIter (suc (suc (ja + jb))) σ₀) ⟩
  cup∈iter ja jb x y hx hy =
    union∈Lset-suc (sucIter (suc (ja + jb)) σ₀) ⁅ x , y ⁆ pair∈
    where
    hx′ : ⟨ x ∈ˢ Lset (sucIter (ja + jb) σ₀) ⟩
    hx′ = iter-mono ja jb x hx

    hy′ : ⟨ y ∈ˢ Lset (sucIter (ja + jb) σ₀) ⟩
    hy′ = subst (λ n → ⟨ y ∈ˢ Lset (sucIter n σ₀) ⟩) (+-comm jb ja)
            (iter-mono jb ja y hy)

    pair∈ : ⟨ ⁅ x , y ⁆ ∈ˢ Lset (sucIter (suc (ja + jb)) σ₀) ⟩
    pair∈ = pair∈Lset-suc (sucIter (ja + jb) σ₀) x y hx′ hy′

  private
    -- Singleton of a key, one iterate up.
    sgl-key : ∀ {n} (φ : Formula ⟪ fst A ⟫ n)
            → Σ[ j ∈ ℕ ] ⟨ ⁅ key ι ιL φ ⁆s ∈ˢ Lset (sucIter j σ₀) ⟩
    sgl-key {n} φ = suc (fst kj) , sgl∈iter (fst kj) _ (snd kj)
      where
      kj = key∈iter φ

    un-clo : ∀ {m k} (χ : Formula ⟪ fst A ⟫ m) (a : Formula ⟪ fst A ⟫ k)
           → closure ι ιL χ ≡ (⁅ key ι ιL χ ⁆s ∪ closure ι ιL a)
           → Σ[ j ∈ ℕ ] ⟨ ⁅ key ι ιL χ ⁆s ∈ˢ Lset (sucIter j σ₀) ⟩
           → Σ[ j ∈ ℕ ] ⟨ closure ι ιL a ∈ˢ Lset (sucIter j σ₀) ⟩
           → Σ[ j ∈ ℕ ] ⟨ closure ι ιL χ ∈ˢ Lset (sucIter j σ₀) ⟩
    un-clo χ a eq (jk , hk) (ja , ha) =
      suc (suc (jk + ja)) ,
      subst (λ w → ⟨ w ∈ˢ Lset (sucIter (suc (suc (jk + ja))) σ₀) ⟩) (sym eq)
        (cup∈iter jk ja ⁅ key ι ιL χ ⁆s (closure ι ιL a) hk ha)

    bin-clo : ∀ {m k} (χ : Formula ⟪ fst A ⟫ m) (a b : Formula ⟪ fst A ⟫ k)
           → closure ι ιL χ ≡ (⁅ key ι ιL χ ⁆s ∪ (closure ι ιL a ∪ closure ι ιL b))
           → Σ[ j ∈ ℕ ] ⟨ ⁅ key ι ιL χ ⁆s ∈ˢ Lset (sucIter j σ₀) ⟩
           → Σ[ j ∈ ℕ ] ⟨ closure ι ιL a ∈ˢ Lset (sucIter j σ₀) ⟩
           → Σ[ j ∈ ℕ ] ⟨ closure ι ιL b ∈ˢ Lset (sucIter j σ₀) ⟩
           → Σ[ j ∈ ℕ ] ⟨ closure ι ιL χ ∈ˢ Lset (sucIter j σ₀) ⟩
    bin-clo χ a b eq (jk , hk) (ja , ha) (jb , hb) =
      suc (suc (jk + (suc (suc (ja + jb))))) ,
      subst (λ w → ⟨ w ∈ˢ Lset
              (sucIter (suc (suc (jk + (suc (suc (ja + jb)))))) σ₀) ⟩) (sym eq)
        (cup∈iter jk (suc (suc (ja + jb))) ⁅ key ι ιL χ ⁆s
            (closure ι ιL a ∪ closure ι ιL b) hk
            (cup∈iter ja jb (closure ι ιL a) (closure ι ιL b) ha hb))

  -- The subformula closure, at SOME iterate (one per formula).
  clo∈iter : ∀ {n} (φ : Formula ⟪ fst A ⟫ n)
           → Σ[ j ∈ ℕ ] ⟨ closure ι ιL φ ∈ˢ Lset (sucIter j σ₀) ⟩
  clo∈iter φ@(t ∈̇ u)  = sgl-key φ
  clo∈iter φ@(t ≐ u)  = sgl-key φ
  clo∈iter φ@⊤̇        = sgl-key φ
  clo∈iter φ@⊥̇        = sgl-key φ
  clo∈iter φ@(a ∧̇ b)  =
    bin-clo φ a b refl (sgl-key φ) (clo∈iter a) (clo∈iter b)
  clo∈iter φ@(a ∨̇ b)  =
    bin-clo φ a b refl (sgl-key φ) (clo∈iter a) (clo∈iter b)
  clo∈iter φ@(a ⇒̇ b)  =
    bin-clo φ a b refl (sgl-key φ) (clo∈iter a) (clo∈iter b)
  clo∈iter φ@(¬̇ a)    = un-clo φ a refl (sgl-key φ) (clo∈iter a)
  clo∈iter φ@(∃̇ a)    = un-clo φ a refl (sgl-key φ) (clo∈iter a)
  clo∈iter φ@(∀̇ a)    = un-clo φ a refl (sgl-key φ) (clo∈iter a)
  clo∈iter φ@(∀̇∈ t a) = un-clo φ a refl (sgl-key φ) (clo∈iter a)
  clo∈iter φ@(∃̇∈ t a) = un-clo φ a refl (sgl-key φ) (clo∈iter a)

  -- Absorbed forms, the shape the rest of the chapter consumes.
  code∈λ₀ : ∀ {n} (φ : Formula ⟪ fst A ⟫ n)
          → ⟨ VCode.⌜ mapFo ι φ ⌝ ∈ˢ Lset λ₀ ⟩
  code∈λ₀ φ = absorb _ _ (snd (code∈iter φ))

  term∈λ₀ : ∀ {n} (t : Term ⟪ fst A ⟫ n)
          → ⟨ VCode.⌜ mapTm ι t ⌝ᵗ ∈ˢ Lset λ₀ ⟩
  term∈λ₀ t = absorb _ _ (snd (term∈iter t))

  key∈λ₀ : ∀ {n} (φ : Formula ⟪ fst A ⟫ n)
          → ⟨ pr (# n) (VCode.⌜ mapFo ι φ ⌝) ∈ˢ Lset λ₀ ⟩
  key∈λ₀ φ = absorb _ _ (snd (key∈iter φ))

  clo∈λ₀ : ∀ {n} (φ : Formula ⟪ fst A ⟫ n)
         → ⟨ closure ι ιL φ ∈ˢ Lset λ₀ ⟩
  clo∈λ₀ φ = absorb _ _ (snd (clo∈iter φ))

  f0 : ∀ {n} → Fin (suc n)
  f0 = FD.zero
  f1 : ∀ {n} → Fin (suc (suc n))
  f1 = FD.suc f0
  f2 : ∀ {n} → Fin (suc (suc (suc n)))
  f2 = FD.suc f1
  f3 : ∀ {n} → Fin (suc (suc (suc (suc n))))
  f3 = FD.suc f2

  -- ===================================================================
  -- SECTION 4.  The bounded description of "this is a key".
  --
  -- ArityK is a Formula S 1 at (u).  WitK binds the witnessing set C,
  -- so its body lives at (C ∷ u), C at slot 0, the member at slot 1.
  -- The carrier is the constant A.  The closedness frames are
  -- implications with the decoding bounded inside the guard; the shape
  -- clauses are plain existentials.  Every quantifier is bounded, so
  -- the whole description is Δ₀.  The slot constants are explicit Fin
  -- literals (FD.zero / FD.suc with the Fin-parameter supplied).
  -- ===================================================================

  -- Fin literals at arity 6 (the binary-clause environments).
  s6-0 s6-1 s6-2 s6-3 s6-4 s6-5 : Fin 6
  s6-0 = FD.zero {5}
  s6-1 = FD.suc (FD.zero {4})
  s6-2 = FD.suc (FD.suc (FD.zero {3}))
  s6-3 = FD.suc (FD.suc (FD.suc (FD.zero {2})))
  s6-4 = FD.suc (FD.suc (FD.suc (FD.suc (FD.zero {1}))))
  s6-5 = FD.suc (FD.suc (FD.suc (FD.suc (FD.suc (FD.zero {0})))))

  -- Fin literals at arity 5 (the unary-clause environments).
  s5-0 s5-1 s5-2 : Fin 5
  s5-0 = FD.zero {4}
  s5-1 = FD.suc (FD.zero {3})
  s5-2 = FD.suc (FD.suc (FD.zero {2}))

  -- Fin literals at arity 7 (the arity-raising clause environments).
  s7-0 s7-1 s7-2 s7-3 s7-5 : Fin 7
  s7-0 = FD.zero {6}
  s7-1 = FD.suc (FD.zero {5})
  s7-2 = FD.suc (FD.suc (FD.zero {4}))
  s7-3 = FD.suc (FD.suc (FD.suc (FD.zero {3})))
  s7-5 = FD.suc (FD.suc (FD.suc (FD.suc (FD.suc (FD.zero {1})))))

  -- The witness-set slot and the member slot of WitK's body.
  wit-C wit-u : Fin 2
  wit-C = FD.suc (FD.zero {0})
  wit-u = FD.zero {1}

  -- The carrier-slot constant of the unary clauses (value 0 = C).
  cC2 cC1 : Fin 2
  cC2 = FD.suc (FD.zero {0})
  cC1 = FD.zero {1}

  ArityK : Formula S 1
  ArityK = ∃̇∈ (con ωʟ) (∃̇∈ (con B*)
    (prAtL (suc (suc zero)) (suc zero) zero ∧̇ (var (suc zero) ∈̇ con ωʟ)))

  tagAtLᵦ : ∀ {n} → Fin n → ℕ → Fin n → Formula S n
  tagAtLᵦ s k x =
    ∃̇∈ (con ωʟ) ((var zero ≐ con (numeralL k)) ∧̇ prAtL (suc s) zero (suc x))

  tagPairAtLᵦ : ∀ {n} → Fin n → ℕ → Fin n → Fin n → Formula S n
  tagPairAtLᵦ s k a b =
    ∃̇∈ (con B*) (prAtL zero (suc a) (suc b) ∧̇ tagAtLᵦ (suc s) k zero)

  arityTagAtLᵦ : ∀ {n} → Fin n → Fin n → ℕ → Fin n → Formula S n
  arityTagAtLᵦ c ar k a =
    ∃̇∈ (con B*) (prAtL (suc c) (suc ar) zero ∧̇ tagAtLᵦ zero k (suc a))

  arityTagPairAtLᵦ : ∀ {n} → Fin n → Fin n → ℕ → Fin n → Fin n → Formula S n
  arityTagPairAtLᵦ c ar k a b =
    ∃̇∈ (con B*) (prAtL (suc c) (suc ar) zero ∧̇ tagPairAtLᵦ zero k (suc a) (suc b))

  isTmAtᵦ : ∀ {n} → Fin n → Fin n → Formula S n
  isTmAtᵦ t N =
    (∃̇∈ (con A) (tagAtLᵦ (suc t) 0 zero ∧̇ (var zero ∈̇ con A)))
    ∨̇ (∃̇∈ (var N) (tagAtLᵦ (suc t) 1 zero ∧̇ (var zero ∈̇ var (suc N))))

  BinFrameᵦ : ℕ → Formula S 6 → Formula S 2
  BinFrameᵦ k rel =
    ∀̇∈ (var zero) (∀̇∈ (con ωʟ) (∀̇∈ (con B*) (∀̇∈ (con B*)
      (arityTagPairAtLᵦ s6-3 s6-2 k s6-1 s6-0 ⇒̇ rel))))

  UnFrameᵦ : ℕ → Formula S 5 → Formula S 2
  UnFrameᵦ k rel =
    ∀̇∈ (var zero) (∀̇∈ (con ωʟ) (∀̇∈ (con B*) (arityTagAtLᵦ s5-2 s5-1 k s5-0 ⇒̇ rel)))

  oneSuccᵦ : Formula S 5
  oneSuccᵦ = ∃̇∈ (con ωʟ) (sucAtL s6-2 s6-0 ∧̇ appAt s6-4 s6-0 s6-1)

  succSndᵦ : Formula S 6
  succSndᵦ = ∃̇∈ (con ωʟ) (sucAtL s7-3 s7-0 ∧̇ appAt s7-5 s7-0 s7-1)

  -- The carrier-slot constant of the clauses (C at slot 0 of arity 2).

  Cldᵦ : Formula S 2
  Cldᵦ =
    BinFrameᵦ 2 (bothSameAt cC2) ∧̇
    (BinFrameᵦ 3 (bothSameAt cC2) ∧̇
    (BinFrameᵦ 4 (bothSameAt cC2) ∧̇
    (UnFrameᵦ 5 (oneSameAt cC2) ∧̇
    (UnFrameᵦ 8 (oneSuccᵦ) ∧̇
    (UnFrameᵦ 9 (oneSuccᵦ) ∧̇
    (BinFrameᵦ 10 (succSndᵦ) ∧̇ BinFrameᵦ 11 (succSndᵦ)))))))

  binFormᵦ : ℕ → Formula S 6 → Formula S 3
  binFormᵦ k rel =
    ∃̇∈ (con ωʟ) (∃̇∈ (con B*) (∃̇∈ (con B*)
      (arityTagPairAtLᵦ s6-3 s6-2 k s6-1 s6-0 ∧̇ rel)))

  unFormᵦ : ℕ → Formula S 5 → Formula S 3
  unFormᵦ k rel = ∃̇∈ (con ωʟ) (∃̇∈ (con B*) (arityTagAtLᵦ s5-2 s5-1 k s5-0 ∧̇ rel))

  bothTmᵦ fstTmᵦ : Formula S 6
  bothTmᵦ = isTmAtᵦ s6-1 s6-2 ∧̇ isTmAtᵦ s6-0 s6-2
  fstTmᵦ = isTmAtᵦ s6-1 s6-2

  shapesᵦ : Formula S 3
  shapesᵦ = binFormᵦ 0 bothTmᵦ ∨̇ (binFormᵦ 1 bothTmᵦ
          ∨̇ (binFormᵦ 2 noneB ∨̇ (binFormᵦ 3 noneB ∨̇ (binFormᵦ 4 noneB
          ∨̇ (unFormᵦ 5 noneU ∨̇ (unFormᵦ 6 zeroPay ∨̇ (unFormᵦ 7 zeroPay
          ∨̇ (unFormᵦ 8 noneU ∨̇ (unFormᵦ 9 noneU
          ∨̇ (binFormᵦ 10 fstTmᵦ ∨̇ binFormᵦ 11 fstTmᵦ))))))))))

  Shpᵦ : Formula S 2
  Shpᵦ = ∀̇∈ (var zero) shapesᵦ

  WitK : Formula S 1
  WitK = ∃̇∈ (con B*) ((var wit-C ∈̇ var wit-u) ∧̇ (Cldᵦ ∧̇ Shpᵦ))

  KF : Formula S 1
  KF = ArityK ∧̇ WitK

  -- ===================================================================
  -- SECTION 5.  The carve at α, and the certificates of KF.
  -- ===================================================================

  module AS = AtStage α oα

  -- The constants of the bounded description sit below α.
  belowω : ⟨ ω ∈ˢ Lset α ⟩
  belowω = ω∈Lα

  belowA : ⟨ fst A ∈ˢ Lset α ⟩
  belowA = A∈Lα

  belowB : ⟨ fst B* ∈ˢ Lset α ⟩
  belowB = B*∈Lα

  belowNum : (k : ℕ) → ⟨ fst (numeralL k) ∈ˢ Lset α ⟩
  belowNum = num∈Lα

  bddKF : BoundedFo AS.Below KF
  bddKF = bddArity , bddWit
    where
    bddArity : BoundedFo AS.Below ArityK
    bddArity =
      ( belowω
      , ( belowB
        , ( prAtL-triv AS.Below _ _ _ , ( tt* , belowω ) ) ) )

    bddTag : ∀ {n} (s x : Fin n) (k : ℕ) → BoundedFo AS.Below (tagAtLᵦ s k x)
    bddTag s x k =
      ( belowω
      , ( ( tt* , belowNum k ) , prAtL-triv AS.Below _ _ _ ) )

    bddTagP : ∀ {n} (s a b : Fin n) (k : ℕ)
            → BoundedFo AS.Below (tagPairAtLᵦ s k a b)
    bddTagP s a b k =
      ( belowB
      , ( prAtL-triv AS.Below _ _ _ , bddTag (suc s) zero k ) )

    bddGuardA : ∀ {n} (c ar a : Fin n) (k : ℕ)
             → BoundedFo AS.Below (arityTagAtLᵦ c ar k a)
    bddGuardA c ar a k =
      ( belowB
      , ( prAtL-triv AS.Below _ _ _ , bddTag zero (suc a) k ) )

    bddGuardP : ∀ {n} (c ar a b : Fin n) (k : ℕ)
             → BoundedFo AS.Below (arityTagPairAtLᵦ c ar k a b)
    bddGuardP c ar a b k =
      ( belowB
      , ( prAtL-triv AS.Below _ _ _ , bddTagP zero (suc a) (suc b) k ) )

    bddApp : ∀ {m} (f x y : Fin m) → BoundedFo AS.Below (appAt f x y)
    bddApp f x y = tt* , prAtL-triv AS.Below _ _ _

    -- sucAtL is an all-variable atom, so its certificate is solved.
    bddAtm : ∀ {m} (i j : Fin m) → BoundedFo AS.Below (sucAtL i j)
    bddAtm i j = _

    bddOneSucc : BoundedFo AS.Below oneSuccᵦ
    bddOneSucc = ( belowω , ( bddAtm _ _ , bddApp _ _ _ ) )

    bddSuccSnd : BoundedFo AS.Below succSndᵦ
    bddSuccSnd = ( belowω , ( bddAtm _ _ , bddApp _ _ _ ) )

    bddBinF : (k : ℕ) (r : Formula S 6)
            → BoundedFo AS.Below r → BoundedFo AS.Below (BinFrameᵦ k r)
    bddBinF k r hr =
      tt* , ( belowω , ( belowB , ( belowB
        , ( bddGuardP s6-3 s6-2 s6-1 s6-0 k , hr ) ) ) )

    bddUnF : (k : ℕ) (r : Formula S 5)
           → BoundedFo AS.Below r → BoundedFo AS.Below (UnFrameᵦ k r)
    bddUnF k r hr =
      tt* , ( belowω , ( belowB , ( bddGuardA s5-2 s5-1 s5-0 k , hr ) ) )

    bddCld : BoundedFo AS.Below Cldᵦ
    bddCld =
      bddBinF 2 (bothSameAt cC2) (bddApp _ _ _ , bddApp _ _ _)
      , ( bddBinF 3 (bothSameAt cC2) (bddApp _ _ _ , bddApp _ _ _)
      , ( bddBinF 4 (bothSameAt cC2) (bddApp _ _ _ , bddApp _ _ _)
      , ( bddUnF 5 (oneSameAt cC2) (bddApp _ _ _)
      , ( bddUnF 8 oneSuccᵦ bddOneSucc
      , ( bddUnF 9 oneSuccᵦ bddOneSucc
      , ( bddBinF 10 succSndᵦ bddSuccSnd
      , bddBinF 11 succSndᵦ bddSuccSnd ))))))

    bddIsTm : ∀ {n} (t N : Fin n) → BoundedFo AS.Below (isTmAtᵦ t N)
    bddIsTm t N =
      ( belowA , ( bddTag (suc t) zero 0 , ( tt* , belowA ) ) )
      , ( tt* , ( bddTag (suc t) zero 1 , ( tt* , tt* ) ) )

    bddBinFm : (k : ℕ) (r : Formula S 6) → BoundedFo AS.Below r
             → BoundedFo AS.Below (binFormᵦ k r)
    bddBinFm k r hr =
      belowω
      , ( belowB
        , ( belowB
            , ( ( belowB , ( prAtL-triv AS.Below _ _ _
                  , bddTagP zero (suc s6-1) (suc s6-0) k ) )
                , hr ) ) )
    bddUnFm : (k : ℕ) (r : Formula S 5) → BoundedFo AS.Below r
            → BoundedFo AS.Below (unFormᵦ k r)
    bddUnFm k r hr =
      belowω
      , ( belowB
        , ( bddGuardA s5-2 s5-1 s5-0 k , hr ) )

    bddShapes : BoundedFo AS.Below shapesᵦ
    bddShapes =
      bddBinFm 0 bothTmᵦ (bddIsTm s6-1 s6-2 , bddIsTm s6-0 s6-2)
      , ( bddBinFm 1 bothTmᵦ (bddIsTm s6-1 s6-2 , bddIsTm s6-0 s6-2)
      , ( bddBinFm 2 noneB tt*
      , ( bddBinFm 3 noneB tt*
      , ( bddBinFm 4 noneB tt*
      , ( bddUnFm 5 noneU tt*
      , ( bddUnFm 6 zeroPay ( tt* , belowNum 0 )
      , ( bddUnFm 7 zeroPay ( tt* , belowNum 0 )
      , ( bddUnFm 8 noneU tt*
      , ( bddUnFm 9 noneU tt*
      , ( bddBinFm 10 fstTmᵦ (bddIsTm s6-1 s6-2)
      , bddBinFm 11 fstTmᵦ (bddIsTm s6-1 s6-2) ))))))))))

    bddWit : BoundedFo AS.Below WitK
    bddWit =
      belowB
      , ( ( tt* , tt* ) , ( bddCld , ( tt* , bddShapes ) ) )

  Δ₀KF : Δ₀ KF
  Δ₀KF = δ-∧ dArity dWit
    where
    dPrAtL : ∀ {n} (q u v : Fin n) → Δ₀ (prAtL q u v)
    dPrAtL q u v = Δ₀-liftFo _ (Δ₀-prAt q u v)

    dTag : ∀ {n} (s x : Fin n) (k : ℕ) → Δ₀ (tagAtLᵦ s k x)
    dTag s x k = δ-∃∈ (δ-∧ δ-≐ (dPrAtL (suc s) zero (suc x)))

    dTagP : ∀ {n} (s a b : Fin n) (k : ℕ) → Δ₀ (tagPairAtLᵦ s k a b)
    dTagP s a b k =
      δ-∃∈ (δ-∧ (dPrAtL zero (suc a) (suc b)) (dTag (suc s) zero k))

    dGuardA : ∀ {n} (c ar a : Fin n) (k : ℕ) → Δ₀ (arityTagAtLᵦ c ar k a)
    dGuardA c ar a k =
      δ-∃∈ (δ-∧ (dPrAtL (suc c) (suc ar) zero) (dTag zero (suc a) k))

    dGuardP : ∀ {n} (c ar a b : Fin n) (k : ℕ) → Δ₀ (arityTagPairAtLᵦ c ar k a b)
    dGuardP c ar a b k =
      δ-∃∈ (δ-∧ (dPrAtL (suc c) (suc ar) zero) (dTagP zero (suc a) (suc b) k))

    dApp : ∀ {m} (f x y : Fin m) → Δ₀ (appAt f x y)
    dApp f x y = δ-∃∈ (dPrAtL zero (suc x) (suc y))

    dAtm : ∀ {m} (i j : Fin m) → Δ₀ (sucAtL i j)
    dAtm i j = Δ₀-liftFo _ (Δ₀-sucAt i j)

    dOneSucc : Δ₀ oneSuccᵦ
    dOneSucc = δ-∃∈ (δ-∧ (dAtm s6-2 s6-0) (dApp s6-4 s6-0 s6-1))

    dSuccSnd : Δ₀ succSndᵦ
    dSuccSnd = δ-∃∈ (δ-∧ (dAtm s7-3 s7-0) (dApp s7-5 s7-0 s7-1))
    dBinF : (k : ℕ) (r : Formula S 6) → Δ₀ r → Δ₀ (BinFrameᵦ k r)
    dBinF k r dr = δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ (dGuardP s6-3 s6-2 s6-1 s6-0 k) dr))))

    dUnF : (k : ℕ) (r : Formula S 5) → Δ₀ r → Δ₀ (UnFrameᵦ k r)
    dUnF k r dr = δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ (dGuardA s5-2 s5-1 s5-0 k) dr)))

    dArity : Δ₀ ArityK
    dArity = δ-∃∈ (δ-∃∈ (δ-∧ (dPrAtL (suc (suc zero)) (suc zero) zero)
                              δ-∈))

    dCld =
      δ-∧ (dBinF 2 (bothSameAt cC2) (δ-∧ (dApp _ _ _) (dApp _ _ _)))
        (δ-∧ (dBinF 3 (bothSameAt cC2) (δ-∧ (dApp _ _ _) (dApp _ _ _)))
          (δ-∧ (dBinF 4 (bothSameAt cC2) (δ-∧ (dApp _ _ _) (dApp _ _ _)))
            (δ-∧ (dUnF 5 (oneSameAt cC2) (dApp _ _ _))
              (δ-∧ (dUnF 8 oneSuccᵦ dOneSucc)
                (δ-∧ (dUnF 9 oneSuccᵦ dOneSucc)
                  (δ-∧ (dBinF 10 succSndᵦ dSuccSnd)
                    (dBinF 11 succSndᵦ dSuccSnd)))))))
    dIsTm : ∀ {n} (t N : Fin n) → Δ₀ (isTmAtᵦ t N)
    dIsTm t N =
      δ-∨ (δ-∃∈ (δ-∧ (dTag (suc t) zero 0) δ-∈))
        (δ-∃∈ (δ-∧ (dTag (suc t) zero 1) δ-∈))

    dBinFm : (k : ℕ) (r : Formula S 6) → Δ₀ r → Δ₀ (binFormᵦ k r)
    dBinFm k r dr = δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∧ (dGuardP s6-3 s6-2 s6-1 s6-0 k) dr)))

    dUnFm : (k : ℕ) (r : Formula S 5) → Δ₀ r → Δ₀ (unFormᵦ k r)
    dUnFm k r dr = δ-∃∈ (δ-∃∈ (δ-∧ (dGuardA s5-2 s5-1 s5-0 k) dr))

    dShapes : Δ₀ shapesᵦ
    dShapes =
      δ-∨ (dBinFm 0 bothTmᵦ (δ-∧ (dIsTm s6-1 s6-2) (dIsTm s6-0 s6-2)))
        (δ-∨ (dBinFm 1 bothTmᵦ (δ-∧ (dIsTm s6-1 s6-2) (dIsTm s6-0 s6-2)))
          (δ-∨ (dBinFm 2 noneB δ-⊤)
            (δ-∨ (dBinFm 3 noneB δ-⊤)
              (δ-∨ (dBinFm 4 noneB δ-⊤)
                (δ-∨ (dUnFm 5 noneU δ-⊤)
                  (δ-∨ (dUnFm 6 zeroPay δ-≐)
                    (δ-∨ (dUnFm 7 zeroPay δ-≐)
                      (δ-∨ (dUnFm 8 noneU δ-⊤)
                        (δ-∨ (dUnFm 9 noneU δ-⊤)
                          (δ-∨ (dBinFm 10 fstTmᵦ (dIsTm s6-1 s6-2))
                            (dBinFm 11 fstTmᵦ (dIsTm s6-1 s6-2))))))))))))

    dWit : Δ₀ WitK
    dWit = δ-∃∈ (δ-∧ δ-∈ (δ-∧ dCld (δ-∀∈ dShapes)))

  -- ===================================================================
  -- SECTION 6.  Reading the bounded readers off their adequacies.
  -- ===================================================================

  ωof≐ : ∀ {n} {k : ℕ} {γ' : S ^ n} (w : S)
       → ⟨ (w ∷ γ') ⊨ (var zero ≐ con (numeralL k)) ⟩
       → ⟨ w ∈ˢʟ ωʟ ⟩
  ωof≐ {k = k} w e =
    subst ⟨_⟩ (sym (ω-specL w)) ∣ lift k , e ∣₁


  -- tagAtLᵦ: the slot s is the numeral k tagged onto the slot x.
  tagAtᵦ-eq-eqP : ∀ {n} (s x : Fin n) (k : ℕ) (γ' : S ^ n)
    (w : S) (e : fst w ≡ fst (numeralL k)) (p : ⟨ (w ∷ γ') ⊨ prAtL (suc s) zero (suc x) ⟩)
    → fst (lookup s γ') ≡ pr (fst w) (fst (lookup x γ'))
  tagAtᵦ-eq-eqP s x k γ' w e p =
    subst ⟨_⟩ (prAtL-adequate (suc s) zero (suc x) (w ∷ γ')) p

  tagAtᵦ-eq-eq₂ : ∀ {n} (s x : Fin n) (k : ℕ) (γ' : S ^ n)
    (w : S) (e : fst w ≡ fst (numeralL k))
    → fst (lookup s γ') ≡ pr (fst w) (fst (lookup x γ'))
    → fst (lookup s γ') ≡ pr (# k) (fst (lookup x γ'))
  tagAtᵦ-eq-eq₂ s x k γ' w e q =
    q ∙ cong (λ r → pr r (fst (lookup x γ'))) (e ∙ numeralL-fst k)

  tagAtᵦ-eq : ∀ {n} (s x : Fin n) (k : ℕ) (γ' : S ^ n)
    → ⟨ γ' ⊨ tagAtLᵦ s k x ⟩
    → ∥ Σ[ w ∈ S ] ( (fst w ≡ fst (numeralL k))
        × (fst (lookup s γ') ≡ pr (# k) (fst (lookup x γ')) ) ) ∥₁
  tagAtᵦ-eq s x k γ' =
    PT.rec squash₁ (λ { (w , w∈ , e , p) →
      ∣ w , (e , tagAtᵦ-eq-eq₂ s x k γ' w e
              (tagAtᵦ-eq-eqP s x k γ' w e p)) ∣₁ })

  tagPairAtᵦ-eq-eq₁ : ∀ {n} (s a b : Fin n) (k : ℕ) (γ' : S ^ n) (w : S)
    → ⟨ (w ∷ γ') ⊨ prAtL zero (suc a) (suc b) ⟩
    → fst w ≡ pr (fst (lookup a γ')) (fst (lookup b γ'))
  tagPairAtᵦ-eq-eq₁ s a b k γ' w hp =
    subst ⟨_⟩ (prAtL-adequate zero (suc a) (suc b) (w ∷ γ')) hp

  tagPairAtᵦ-eq : ∀ {n} (s a b : Fin n) (k : ℕ) (γ' : S ^ n)
    → ⟨ γ' ⊨ tagPairAtLᵦ s k a b ⟩
    → ∥ Σ[ w ∈ S ] ( (fst w ≡ pr (fst (lookup a γ')) (fst (lookup b γ')))
        × (fst (lookup s γ') ≡ pr (# k) (fst w)) ) ∥₁
  tagPairAtᵦ-eq s a b k γ' = PT.rec squash₁ clause
    where
    clause : Σ[ w ∈ S ] (⟨ fst w ∈ˢ Lset τ ⟩
             × (⟨ (w ∷ γ') ⊨ prAtL zero (suc a) (suc b) ⟩
               × ⟨ (w ∷ γ') ⊨ tagAtLᵦ (suc s) k zero ⟩))
           → ∥ Σ[ w ∈ S ] ( (fst w ≡ pr (fst (lookup a γ')) (fst (lookup b γ')))
               × (fst (lookup s γ') ≡ pr (# k) (fst w)) ) ∥₁
    clause (w , w∈ , hp , ht) = PT.map
      (λ { (wt , e₁ , e₂) → w , (tagPairAtᵦ-eq-eq₁ s a b k γ' w hp , e₂) })
      (tagAtᵦ-eq (suc s) zero k (w ∷ γ') ht)

  guardAtᵦ-eq : ∀ {n} (c ar a : Fin n) (k : ℕ) (γ' : S ^ n)
    → ⟨ γ' ⊨ arityTagAtLᵦ c ar k a ⟩
    → ∥ Σ[ z ∈ S ] ( (fst (lookup c γ') ≡ pr (fst (lookup ar γ')) (fst z))
        × (fst z ≡ pr (# k) (fst (lookup a γ'))) ) ∥₁
  guardAtᵦ-eq c ar a k γ' = PT.rec squash₁ clause
    where
    clause : Σ[ z ∈ S ] (⟨ fst z ∈ Lset τ ⟩
             × (⟨ (z ∷ γ') ⊨ prAtL (suc c) (suc ar) zero ⟩
               × ⟨ (z ∷ γ') ⊨ tagAtLᵦ zero k (suc a) ⟩))
           → ∥ Σ[ z ∈ S ] ( (fst (lookup c γ') ≡ pr (fst (lookup ar γ')) (fst z))
               × (fst z ≡ pr (# k) (fst (lookup a γ'))) ) ∥₁
    clause (z , z∈ , hp , ht) = ∣ z , (eq₁ , e₂) ∣₁
      where
      eq₁ : fst (lookup c γ') ≡ pr (fst (lookup ar γ')) (fst z)
      eq₁ = subst ⟨_⟩ (prAtL-adequate (suc c) (suc ar) zero (z ∷ γ')) hp
      e₂ = PT.rec squash₁ (λ { (wt , (e₁ , e₂)) →
        e₂ ∙ cong (pr (# k)) e₁ }) (tagAtᵦ-eq zero (suc a) k (z ∷ γ') ht)

  guardPrᵦ-eq : ∀ {n} (c ar a b : Fin n) (k : ℕ) (γ' : S ^ n)
    → ⟨ γ' ⊨ arityTagPairAtLᵦ c ar k a b ⟩
    → ∥ Σ[ z ∈ S ] ( (fst (lookup c γ') ≡ pr (fst (lookup ar γ')) (fst z))
        × (fst z ≡ pr (# k) (pr (fst (lookup a γ')) (fst (lookup b γ')))) ) ∥₁
  guardPrᵦ-eq c ar a b k γ' = PT.rec squash₁ clause
    where
    clause : Σ[ z ∈ S ] (⟨ fst z ∈ Lset τ ⟩
             × (⟨ (z ∷ γ') ⊨ prAtL (suc c) (suc ar) zero ⟩
               × ⟨ (z ∷ γ') ⊨ tagPairAtLᵦ zero k (suc a) (suc b) ⟩))
           → ∥ Σ[ z ∈ S ] ( (fst (lookup c γ') ≡ pr (fst (lookup ar γ')) (fst z))
               × (fst z ≡ pr (# k) (pr (fst (lookup a γ')) (fst (lookup b γ')))) ) ∥₁
    clause (z , z∈ , hp , ht) = ∣ z , (eq₁ , e₂) ∣₁
      where
      eq₁ : fst (lookup c γ') ≡ pr (fst (lookup ar γ')) (fst z)
      eq₁ = subst ⟨_⟩ (prAtL-adequate (suc c) (suc ar) zero (z ∷ γ')) hp
      e₂ : fst z ≡ pr (# k) (pr (fst (lookup a γ')) (fst (lookup b γ')))
      e₂ = PT.map (λ { (w , (e₁ , e₂)) → e₂ ∙ cong (pr (# k)) e₁ })
             (tagPairAtᵦ-eq zero (suc a) (suc b) k (z ∷ γ') ht)

  -- Delivered to bounded at the tag level: the pinned numeral is in ωʟ,
  -- so this direction is unconditional.  (The pair-level delivered-to-
  -- bounded conversion is never needed: into builds its guards directly.)
  tagᵦ-bwd : ∀ {n} (s x : Fin n) (k : ℕ) (γ' : S ^ n)
           → ⟨ γ' ⊨ tagAtL s k x ⟩ → ⟨ γ' ⊨ tagAtLᵦ s k x ⟩
  tagᵦ-bwd s x k γ' = PT.map (λ { (w , (e , p)) → w , (ωof≐ w e , e , p) })

  -- The appAt demand of a clause, at either environment: both reduce to
  -- a membership of the pair in C, and the pair's components transport.
  appAt-t : ∀ {m} (f x y : Fin m) (γ₁ γ₂ : S ^ m)
    → ⟨ γ₁ ⊨ appAt f x y ⟩ → ⟨ γ₂ ⊨ appAt f x y ⟩
  appAt-t f x y γ₁ γ₂ h =
    subst ⟨_⟩ (appAt-adequate f x y γ₂) (subst ⟨_⟩ (sym (appAt-adequate f x y γ₁)) h)

  -- Transport of a membership along an equality of underlying sets.
  ∈t : (x y z : V ℓ) → x ≡ y → ⟨ x ∈ˢ z ⟩ → ⟨ y ∈ˢ z ⟩
  ∈t x y z e h = subst (λ r → ⟨ r ∈ˢ z ⟩) e h


# The bounded subset theorem, internally

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.BoundedSubset {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; regularityV )
open import V.Collapse {ℓ} using ( isExt )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono; Lset-layer; layer-trans )
open import L.Ordinal {ℓ} using ( ω-ord; #∈ω )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset→∈ )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Numerals {ℓ} using ( pairʟ )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Cardinal {ℓ} lem using ( InjCode; IsCardinalL; _↪_ )
open import L.GCH {ℓ} lem using ( InjL )
open import L.GCH.Assembly {ℓ} lem
  using ( InternalBoundedSubset; inclusion-coded; injl-trans )
open import L.GCH.Definable {ℓ} lem using ( DefinableMap; module Inj )
open import L.GCH.Hull {ℓ} lem using ( module Frame; module UnionKit; module HullStage )
open import L.GCH.HullIn {ℓ} lem using ( module PiIn; module Condense′ )
open import L.GCH.HullElem {ℓ} lem using ( module Elem )
open import L.GCH.Pairing {ℓ} lem
  using ( prodL; prodL-in; ordL; coded→ambient; ω⊆; Goal; module Step )
open import L.GCH.Complete {ℓ} lem using ( superadequate-above; Superadequate )
open import L.GCH.StageCount {ℓ} lem using ( move; stage-counted )
open import L.GCH.OmegaRec {ℓ} lem using ( pairʟ-in )
open import L.GCH.HullCount {ℓ} lem
  using ( ord⊆Lset; module Union2; tag-union; module Point; module Count; S≡ )

open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet; ⁅_⁆s )
open InfinitySet {ℓ} using ( #_; ω; sucV )
open import Cubical.Data.Vec using ( _∷_; [] )
import Cubical.Induction.WellFounded as WF
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

open hPropStructure 𝒮ʟ using ( S )

open FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using () renaming ( _⊨ᵐ_ to _⊨_ )

-- Every module application below names what it takes: a module
-- application copies every definition it brings into scope into this
-- module's interface, and the copies are what the interface stores.
module Ren = Sat (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ id using ( Agrees; ⊨-rename )

-- =====================================================================
-- THE SITE.  An infinite L-cardinal κ and a subset y of κ, both
-- elements of L.  The start X = L_κ ∪ {y} is transitive and an element
-- of L; λ is a superadequate stage above κ and above y; the Skolem hull
-- M of X in L_λ collapses to a stage L_β (src/L/GCH/HullIn.lagda.md
-- `Condense′`); y is fixed by the collapse, so y ∈ L_β; and β ⊆ L_β =
-- πX ↪ M ↪ κ, the last by src/L/GCH/HullCount.lagda.md.
-- =====================================================================

module At (κ : S) (oκ : IsOrd (fst κ)) (cκ : IsCardinalL κ)
          (κ∉ω : ⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
          (y : S) (y⊆κ : (z : V ℓ) → ⟨ z ∈ˢ fst y ⟩ → ⟨ z ∈ˢ fst κ ⟩) where

  num∈κ : (k : ℕ) → ⟨ # k ∈ fst κ ⟩
  num∈κ k = ω⊆ (fst κ) oκ κ∉ω (# k) (#∈ω k)

  Lκ : S
  Lκ = LsetS (fst κ) oκ

  -- -------------------------------------------------------------------
  -- 1.  THE STAGE λ.  α₀ is the stage of the pair {κ, y}; λ is the
  -- superadequate stage above α₀.  Sealed: every consumer wants λ as
  -- an atom.
  -- -------------------------------------------------------------------

  private
    P₀ : S
    P₀ = pairʟ κ y

    α₀ : V ℓ
    α₀ = stage (fst P₀) (snd P₀)

    oα₀ : IsOrd α₀
    oα₀ = stage-ord (fst P₀) (snd P₀)

    κ∈Lα₀ : ⟨ fst κ ∈ˢ Lset α₀ ⟩
    κ∈Lα₀ = layer-trans (Lset-layer α₀) {x = fst P₀} {y = fst κ}
      (pairʟ-in κ y κ (inl refl)) (stage-mem (fst P₀) (snd P₀))

    y∈Lα₀ : ⟨ fst y ∈ˢ Lset α₀ ⟩
    y∈Lα₀ = layer-trans (Lset-layer α₀) {x = fst P₀} {y = fst y}
      (pairʟ-in κ y y (inr refl)) (stage-mem (fst P₀) (snd P₀))

    sa = superadequate-above α₀ oα₀

  opaque
    lam : V ℓ
    lam = sa .fst

    ordλ : IsOrd lam
    ordλ = sa .snd .fst

    succλ : (d : V ℓ) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩
    succλ = sa .snd .snd .snd .fst .snd .fst

    sup : Superadequate lam
    sup = sa .snd .snd .snd .snd

    κ∈λ : ⟨ fst κ ∈ˢ lam ⟩
    κ∈λ = ordλ .fst (ord∈Lset→∈ α₀ oα₀ (fst κ) oκ κ∈Lα₀) (sa .snd .snd .fst)

    y∈Lλ : ⟨ fst y ∈ˢ Lset lam ⟩
    y∈Lλ = Lset-mono {α = lam} {β = α₀} (sa .snd .snd .fst) y∈Lα₀

  -- -------------------------------------------------------------------
  -- 2.  THE START X = L_κ ∪ {y}, transitive, an element of L.
  -- -------------------------------------------------------------------

  y⊆Lκ : (z : V ℓ) → ⟨ z ∈ˢ fst y ⟩ → ⟨ z ∈ˢ Lset (fst κ) ⟩
  y⊆Lκ z hz = ord⊆Lset (fst κ) oκ z (y⊆κ z hz)

  module UK = UnionKit (fst κ) lam (fst y) oκ ordλ κ∈λ y⊆Lκ y∈Lλ κ∉ω
    using ( X; X⊆Lλ; ∅∈λ; Lα∈X; x∈X; X-mem; sgl≡; Xtr )

  X : V ℓ
  X = UK.X

  -- X as the model's own union of L_κ and {y}.
  module Pt = Point κ (num∈κ 0) y using ( Y; Y-out; Y-in; injL )
  module U = Union2 Lκ Pt.Y using ( D; out; in₁; in₂ )

  Xʟ : S
  Xʟ = U.D

  Xʟ-eq : fst Xʟ ≡ X
  Xʟ-eq = extensionalV {a = fst Xʟ} {b = X} (λ z → ⇔toPath (fwd z) (bwd z))
    where
    fwd : (z : V ℓ) → ⟨ z ∈ˢ fst Xʟ ⟩ → ⟨ z ∈ˢ X ⟩
    fwd z h = PT.rec (snd (z ∈ˢ X)) go (U.out zS h)
      where
      zS : S
      zS = z , isL-trans {x = fst Xʟ} {y = z} h (snd Xʟ)
      go : ⟨ z ∈ˢ Lset (fst κ) ⟩ ⊎ ⟨ z ∈ˢ fst Pt.Y ⟩ → ⟨ z ∈ˢ X ⟩
      go (inl hz) = UK.Lα∈X z hz
      go (inr hz) = subst (λ w → ⟨ w ∈ˢ X ⟩) (sym (Pt.Y-out zS hz)) UK.x∈X
    bwd : (z : V ℓ) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ fst Xʟ ⟩
    bwd z h = PT.rec (snd (z ∈ˢ fst Xʟ)) go (UK.X-mem z h)
      where
      go : ⟨ z ∈ˢ Lset (fst κ) ⟩ ⊎ ⟨ z ∈ˢ ⁅ fst y ⁆s ⟩ → ⟨ z ∈ˢ fst Xʟ ⟩
      go (inl hz) = U.in₁ (z , isL-trans {x = Lset (fst κ)} {y = z} hz (snd Lκ)) hz
      go (inr hz) = subst (λ w → ⟨ w ∈ˢ fst Xʟ ⟩) (sym (UK.sgl≡ z hz)) (U.in₂ y Pt.Y-in)

  X-isL : ⟨ isL X ⟩
  X-isL = subst (λ w → ⟨ isL w ⟩) Xʟ-eq (snd Xʟ)

  XS : S
  XS = X , X-isL

  -- -------------------------------------------------------------------
  -- 3.  THE START IS COUNTED: L_κ ↪ κ and {y} ↪ κ, tagged, then paired.
  -- -------------------------------------------------------------------

  -- The pairing at κ: src/L/GCH/Pairing.lagda.md's square law.
  pairκ : InjL (prodL κ) κ
  pairκ = WF.WFI.induction regularityV {P = Goal} Step.result (fst κ) (snd κ) oκ cκ κ∉ω

  base : InjL XS κ
  base = move Xʟ XS κ κ Xʟ-eq refl
    (injl-trans Xʟ (prodL κ) κ
      (tag-union κ (num∈κ 0) (num∈κ 1) Lκ Pt.Y (stage-counted κ Lκ oκ κ∉ω refl) Pt.injL)
      pairκ)

  -- -------------------------------------------------------------------
  -- 4.  ELEMENTARITY OF THE HULL, at the ambient pairing on κ and the
  -- ambient injection X ↪ κ, both read off the internal ones
  -- (src/L/GCH/HullElem.lagda.md).
  -- -------------------------------------------------------------------

  module WithCodes (Fp : Σ[ F ∈ S ] InjCode F (prodL κ) κ)
                   (Fx : Σ[ F ∈ S ] InjCode F XS κ) where

    -- the ambient pairing on κ and the ambient injection of the start
    pκ : ⟪ fst (prodL κ) ⟫ ↪ ⟪ fst κ ⟫
    pκ = coded→ambient (prodL κ) κ Fp

    g : ⟪ X ⟫ ↪ ⟪ fst κ ⟫
    g = coded→ambient XS κ Fx

    -- The elementarity of the hull, src/L/GCH/HullElem.lagda.md.
    elem = Elem.elem κ oκ κ∉ω lam ordλ X UK.X⊆Lλ UK.∅∈λ pκ g

    -- -----------------------------------------------------------------
    -- 5.  THE HULL, ITS COLLAPSE L_β, AND ITS COUNT.
    -- -----------------------------------------------------------------

    -- Read at the source, applied to the telescope: no module
    -- application, so nothing of `Count` or `Condense′` is copied.
    hull↪κ = Count.hull↪κ lam ordλ succλ X UK.X⊆Lλ UK.∅∈λ elem sup X-isL κ oκ cκ κ∉ω base
    condenses′ = Condense′.condenses′ lam ordλ succλ X UK.X⊆Lλ UK.∅∈λ elem sup X-isL
    M-isL = Condense′.M-isL lam ordλ succλ X UK.X⊆Lλ UK.∅∈λ elem sup X-isL

    -- The hull stage, its collapse, and the collapse graph, read at the
    -- source modules `Cn` copies from.
    module HS = HullStage lam ordλ succλ X UK.X⊆Lλ UK.∅∈λ using ( M )
    module HSH = HullStage.H lam ordλ succλ X UK.X⊆Lλ UK.∅∈λ using ( X⊆M )
    module HSC = HullStage.C lam ordλ succλ X UK.X⊆Lλ UK.∅∈λ
      using ( πX; π; fixes; πX-intro; πX-member )
    module P = PiIn (HS.M , M-isL) using ( piFo; up; good-at; piFo-val )

    β : V ℓ
    β = condenses′ .fst

    oβ : IsOrd β
    oβ = condenses′ .snd .fst

    ext : HSC.πX ≡ Lset β
    ext = condenses′ .snd .snd

    Lβ : S
    Lβ = LsetS β oβ

    βL : S
    βL = ordL β oβ

    hullL : S
    hullL = Condense′.hullL lam ordλ succλ X UK.X⊆Lλ UK.∅∈λ elem sup X-isL

    M≡ : fst hullL ≡ HS.M
    M≡ = Condense′.hullL-spec lam ordλ succλ X UK.X⊆Lλ UK.∅∈λ elem sup X-isL

    Mext : isExt HS.M
    Mext = Frame.Mext lam ordλ succλ X UK.X⊆Lλ UK.∅∈λ

    module CI = HullStage.C.InjExt lam ordλ succλ X UK.X⊆Lλ UK.∅∈λ Mext using ( π-inj )

    -- -----------------------------------------------------------------
    -- 5.1  y is a member of L_β: y ∈ X ⊆ M, X is transitive, so the
    -- collapse fixes y (src/V/Collapse.lagda.md `fixes`).
    -- -----------------------------------------------------------------

    y∈M : ⟨ fst y ∈ˢ HS.M ⟩
    y∈M = HSH.X⊆M (fst y) UK.x∈X

    πy : HSC.π (fst y) ≡ fst y
    πy = HSC.fixes X
      (λ a a∈ₛX → ∈∈ₛ {a = a} {b = HS.M} .fst (HSH.X⊆M a (∈∈ₛ {a = a} {b = X} .snd a∈ₛX)))
      UK.Xtr (fst y) UK.x∈X

    y∈Lβ : ⟨ fst y ∈ˢ Lset β ⟩
    y∈Lβ = subst (λ w → ⟨ w ∈ˢ Lset β ⟩) πy
      (subst (λ w → ⟨ HSC.π (fst y) ∈ˢ w ⟩) ext (HSC.πX-intro (fst y) y∈M))

    -- -----------------------------------------------------------------
    -- 5.2  THE INVERSE COLLAPSE, L_β ↪ M, as a definable map: v ↦ the
    -- member of M collapsing to v.  The graph, over (x ∷ v ∷ []):
    -- "x ∈ M and the collapse graph holds at (v, x)", the latter being
    -- src/L/GCH/HullIn.lagda.md `PiIn.piFo` read at (v ∷ x ∷ []).
    -- -----------------------------------------------------------------

    Pre : S → Type (ℓ-suc ℓ)
    Pre v = Σ[ x ∈ V ℓ ] (⟨ x ∈ˢ HS.M ⟩ × (HSC.π x ≡ fst v))

    isPropPre : (v : S) → isProp (Pre v)
    isPropPre v (x , mx , e) (x' , mx' , e') =
      Σ≡Prop (λ x → isProp× (snd (x ∈ˢ HS.M)) (setIsSet _ _)) (CI.π-inj x x' mx mx' (e ∙ sym e'))

    Mem : S → Type (ℓ-suc ℓ)
    Mem v = ⟨ fst v ∈ˢ fst Lβ ⟩

    pre : (v : S) → Mem v → Pre v
    pre v m = PT.rec (isPropPre v) (λ w → w)
      (HSC.πX-member (fst v) (subst (λ w → ⟨ fst v ∈ˢ w ⟩) (sym ext) m))

    fn : (v : S) → Mem v → S
    fn v m = pre v m .fst
           , isL-trans {x = fst hullL} {y = pre v m .fst}
               (subst (λ w → ⟨ pre v m .fst ∈ˢ w ⟩) (sym M≡) (pre v m .snd .fst)) (snd hullL)

    ρ : Fin 2 → Fin 2
    ρ zero = suc zero
    ρ (suc zero) = zero

    private
      ag : (x v : S) → Ren.Agrees ρ (x ∷ v ∷ []) (v ∷ x ∷ [])
      ag x v zero = refl
      ag x v (suc zero) = refl

      rn : (x v : S) → ⟨ (x ∷ v ∷ []) ⊨ renameFo ρ P.piFo ⟩ ≡ ⟨ (v ∷ x ∷ []) ⊨ P.piFo ⟩
      rn x v = cong ⟨_⟩ (Ren.⊨-rename ρ P.piFo (x ∷ v ∷ []) (v ∷ x ∷ []) (ag x v))

    invFo : Formula S 2
    invFo = (var zero ∈̇ con hullL) ∧̇ renameFo ρ P.piFo

    -- the collapse graph holds at (π x, x) for x ∈ M
    π-graph : (x : S) (mx : ⟨ fst x ∈ˢ HS.M ⟩) (v : S) → HSC.π (fst x) ≡ fst v
            → ⟨ (v ∷ x ∷ []) ⊨ P.piFo ⟩
    π-graph x mx v e = PT.rec (snd ((v ∷ x ∷ []) ⊨ P.piFo)) read M-isL
      where
      read : Σ[ α ∈ V ℓ ] (IsOrd α × ⟨ HS.M ∈ˢ Lset α ⟩) → ⟨ (v ∷ x ∷ []) ⊨ P.piFo ⟩
      read (α , oα , M∈Lα) =
        subst2 (λ a b → ⟨ (a ∷ b ∷ []) ⊨ P.piFo ⟩)
          (S≡ {x = HSC.π (fst x) , G .fst} {y = v} e) (S≡ {x = P.up (fst x) mx} {y = x} refl)
          (G .snd mx)
        where
        G = P.good-at α oα (fst x) mx (layer-trans (Lset-layer α) {x = HS.M} {y = fst x} mx M∈Lα)

    defines : (v : S) (m : Mem v) → ⟨ (fn v m ∷ v ∷ []) ⊨ invFo ⟩
    defines v m =
        subst (λ w → ⟨ pre v m .fst ∈ˢ w ⟩) (sym M≡) (pre v m .snd .fst)
      , transport (sym (rn (fn v m) v)) (π-graph (fn v m) (pre v m .snd .fst) v (pre v m .snd .snd))

    only : (v : S) (m : Mem v) (x' : S) → ⟨ (x' ∷ v ∷ []) ⊨ invFo ⟩ → x' ≡ fn v m
    only v m x' (hx , hp) = S≡ (CI.π-inj (fst x') (pre v m .fst) mx' (pre v m .snd .fst)
      (sym (P.piFo-val x' mx' v (transport (rn x' v) hp)) ∙ sym (pre v m .snd .snd)))
      where
      mx' : ⟨ fst x' ∈ˢ HS.M ⟩
      mx' = subst (λ w → ⟨ fst x' ∈ˢ w ⟩) M≡ hx

    Dmap : DefinableMap
    Dmap = record
      { dom = Lβ ; cod = hullL ; fn = fn
      ; into = λ v m → subst (λ w → ⟨ pre v m .fst ∈ˢ w ⟩) (sym M≡) (pre v m .snd .fst)
      ; graph = invFo ; defines = defines ; only = only }

    inj : (v : S) (m : Mem v) (v' : S) (m' : Mem v') → fst (fn v m) ≡ fst (fn v' m') → fst v ≡ fst v'
    inj v m v' m' q = sym (pre v m .snd .snd) ∙ cong HSC.π q ∙ pre v' m' .snd .snd

    Lβ↪M : InjL Lβ hullL
    Lβ↪M = Inj.injL Dmap inj

    -- -----------------------------------------------------------------
    -- 5.3  THE CHAIN: β ⊆ L_β ↪ M ↪ κ.
    -- -----------------------------------------------------------------

    β↪κ : InjL βL κ
    β↪κ = injl-trans βL Lβ κ
      (inclusion-coded βL Lβ (λ z hz → ord⊆Lset β oβ z hz))
      (injl-trans Lβ hullL κ Lβ↪M hull↪κ)

    result : Σ[ b ∈ S ] (IsOrd (fst b) × ⟨ fst y ∈ˢ Lset (fst b) ⟩ × InjL b κ)
    result = βL , oβ , y∈Lβ , β↪κ

-- =====================================================================
-- THE THEOREM.  Hypothesis 2 of src/L/GCH/Assembly.lagda.md.
-- =====================================================================

internal-bounded-subset : InternalBoundedSubset
internal-bounded-subset κ oκ cκ κ∉ω y y⊆κ =
  PT.rec squash₁
    (λ Fp → PT.rec squash₁
      (λ Fx → ∣ At.WithCodes.result κ oκ cκ κ∉ω y y⊆κ Fp Fx ∣₁)
      (At.base κ oκ cκ κ∉ω y y⊆κ))
    (At.pairκ κ oκ cκ κ∉ω y y⊆κ)
```

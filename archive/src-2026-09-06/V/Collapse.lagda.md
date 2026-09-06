# The collapse injectivity under carrier transitivity (retired 2026-09-06)

Two blocks of `src/V/Collapse.lagda.md`, both inside `module Collapse (X : S)`.

`module Inj (Xtr : isTrans X)` proved extensional injectivity of the
collapse on a TRANSITIVE carrier: `in⊆`, `out⊆` and `step-inj` feed the
membership induction, `π-inj` is the injectivity, `π∈-bwd` reads a
collapsed membership back, and `iso` pairs it with `π∈-fwd`.  It is the
transitivity-hypothesis twin of `module InjExt (Xext : isExt X)`, which
gets the same four results from structure extensionality alone and
stays in the live file.

`Mostowski` is the packed statement, once in each of the two modules:
transitive range, injectivity on the carrier, and membership preserved
both ways.

THE TREE HAD NO CONSUMER FOR EITHER.  The only importers of
`V.Collapse` that take `module Collapse` are `src/L/GCH/HullIn.lagda.md`
(which takes `Fiber`, `π`, `π-compute`, `πX`, `πX-member`, `π∈-fwd`) and
`src/L/GCH/Hull.lagda.md`, which instantiates `InjExt` twice
(`Hull.lagda.md:566` and `:1035`) and never `Inj`.  The `Inj` and
`Mostowski` occurrences a name sweep finds elsewhere in the tree belong
to `L.GCH.Definable.Inj`, `L.GCH.OrderType`'s inner `Inj` and
`L.CardinalAbove.Mostowski`, which are unrelated definitions with the
same spelling.

  -- extensional injectivity on the carrier; the carrier's transitivity is a
  -- module parameter here and only here
  module Inj (Xtr : isTrans X) where

    P : S → Type (ℓ-suc ℓ)
    P x = (y : S) → x ∈ᵗ X → y ∈ᵗ X → π x ≡ π y → x ≡ y

    -- direction 1: move a member z of x into y; the hypothesis fires at z ∈ x
    in⊆ : (x y z : S) → x ∈ᵗ X → y ∈ᵗ X → z ∈ᵗ x → z ∈ᵗ X
        → π x ≡ π y
        → ((a : S) → a ∈ᵗ x → (b : S) → b ∈ᵗ X → π a ≡ π b → a ≡ b)
        → ⟨ z ∈ₛ y ⟩
    in⊆ x y z xu yu zx zu e ih = ∈∈ₛ {a = z} {b = y} .fst
      (PT.rec (snd (z ∈ˢ y)) step2 (subst (λ w → ⟨ π z ∈ˢ w ⟩) (π-compute y)
        (subst (λ w → ⟨ π z ∈ˢ w ⟩) e (π∈-fwd x z zx zu))))
      where
      step2 : Σ[ p ∈ Fiber y ] (π (⟪ y ⟫↪ (p .fst)) ≡ π z) → ⟨ z ∈ˢ y ⟩
      step2 (p , q) = subst (λ w → ⟨ w ∈ˢ y ⟩) (sym z≡b) by
        where
        b : S
        b = ⟪ y ⟫↪ (p .fst)
        by : ⟨ b ∈ˢ y ⟩
        by = member y (p .fst)
        bu : ⟨ b ∈ˢ X ⟩
        bu = Xtr {x = y} {y = b} by yu
        z≡b : z ≡ b
        z≡b = ih z zx b bu (sym q)

    -- direction 2: move a member z of y into x; the hypothesis fires at the
    -- witness b ∈ x extracted from the collapsed membership
    out⊆ : (x y z : S) → x ∈ᵗ X → y ∈ᵗ X → z ∈ᵗ y → z ∈ᵗ X
         → π y ≡ π x
         → ((a : S) → a ∈ᵗ x → (b : S) → b ∈ᵗ X → π a ≡ π b → a ≡ b)
         → ⟨ z ∈ₛ x ⟩
    out⊆ x y z xu yu zy zu e ih = ∈∈ₛ {a = z} {b = x} .fst
      (PT.rec (snd (z ∈ˢ x)) step2 (subst (λ w → ⟨ π z ∈ˢ w ⟩) (π-compute x)
        (subst (λ w → ⟨ π z ∈ˢ w ⟩) e (π∈-fwd y z zy zu))))
      where
      step2 : Σ[ p ∈ Fiber x ] (π (⟪ x ⟫↪ (p .fst)) ≡ π z) → ⟨ z ∈ˢ x ⟩
      step2 (p , q) = subst (λ w → ⟨ w ∈ˢ x ⟩) b≡z bx
        where
        b : S
        b = ⟪ x ⟫↪ (p .fst)
        bx : ⟨ b ∈ˢ x ⟩
        bx = member x (p .fst)
        bu : ⟨ b ∈ˢ X ⟩
        bu = Xtr {x = x} {y = b} bx xu
        b≡z : b ≡ z
        b≡z = ih b bx z zu q

    step-inj : (x : S) → ((a : S) → a ∈ᵗ x → P a) → P x
    step-inj x IH y xu yu e = extensionality x y (⊆xy , ⊆yx)
      where
      ih4 : (a : S) → a ∈ᵗ x → (b : S) → b ∈ᵗ X → π a ≡ π b → a ≡ b
      ih4 a ax b bu eq = IH a ax b (Xtr {x = x} {y = a} ax xu) bu eq
      ⊆xy : ⟨ x ⊆ y ⟩
      ⊆xy z z∈ₛx = let zx = ∈∈ₛ {a = z} {b = x} .snd z∈ₛx
                   in in⊆ x y z xu yu zx (Xtr {x = x} {y = z} zx xu) e ih4
      ⊆yx : ⟨ y ⊆ x ⟩
      ⊆yx z z∈ₛy = let zy = ∈∈ₛ {a = z} {b = y} .snd z∈ₛy
                   in out⊆ x y z xu yu zy (Xtr {x = y} {y = z} zy yu) (sym e) ih4

    -- extensional injectivity on the carrier, by ∈-induction
    π-inj : (x y : S) → x ∈ᵗ X → y ∈ᵗ X → π x ≡ π y → x ≡ y
    π-inj = ∈-induction step-inj

    -- the backward direction: a collapsed membership names a witness in the
    -- carrier member, and injectivity identifies it
    π∈-bwd : (x y : S) → x ∈ᵗ X → y ∈ᵗ X → ⟨ π y ∈ˢ π x ⟩ → y ∈ᵗ x
    π∈-bwd x y xu yu h =
      PT.rec (snd (y ∈ˢ x)) step2 (subst (λ w → ⟨ π y ∈ˢ w ⟩) (π-compute x) h)
      where
      step2 : Σ[ p ∈ Fiber x ] (π (⟪ x ⟫↪ (p .fst)) ≡ π y) → ⟨ y ∈ˢ x ⟩
      step2 (p , q) = subst (λ w → ⟨ w ∈ˢ x ⟩) c≡y cx
        where
        c : S
        c = ⟪ x ⟫↪ (p .fst)
        cx : ⟨ c ∈ˢ x ⟩
        cx = member x (p .fst)
        cu : ⟨ c ∈ˢ X ⟩
        cu = Xtr {x = x} {y = c} cx xu
        c≡y : c ≡ y
        c≡y = π-inj c y cu yu q

    -- the iso reading on the carrier, both directions
    iso : (x y : S) → x ∈ᵗ X → y ∈ᵗ X
        → (⟨ y ∈ˢ x ⟩ → ⟨ π y ∈ˢ π x ⟩) × (⟨ π y ∈ˢ π x ⟩ → ⟨ y ∈ˢ x ⟩)
    iso x y xu yu = (λ yx → π∈-fwd x y yx yu) , π∈-bwd x y xu yu

    -- the Mostowski statement for the carrier: transitive range, injectivity,
    -- and membership preserved both ways
    Mostowski : Type (ℓ-suc ℓ)
    Mostowski = isTrans πX
              × ((x y : S) → x ∈ᵗ X → y ∈ᵗ X → π x ≡ π y → x ≡ y)
              × ((x y : S) → x ∈ᵗ X → y ∈ᵗ X
               → (⟨ y ∈ˢ x ⟩ → ⟨ π y ∈ˢ π x ⟩) × (⟨ π y ∈ˢ π x ⟩ → ⟨ y ∈ˢ x ⟩))


And the same statement inside `module InjExt`:

    -- the Mostowski statement for the carrier: transitive range, injectivity,
    -- and membership preserved both ways
    Mostowski : Type (ℓ-suc ℓ)
    Mostowski = isTrans πX
              × ((x y : S) → x ∈ᵗ X → y ∈ᵗ X → π x ≡ π y → x ≡ y)
              × ((x y : S) → x ∈ᵗ X → y ∈ᵗ X
               → (⟨ y ∈ˢ x ⟩ → ⟨ π y ∈ˢ π x ⟩) × (⟨ π y ∈ˢ π x ⟩ → ⟨ y ∈ˢ x ⟩))

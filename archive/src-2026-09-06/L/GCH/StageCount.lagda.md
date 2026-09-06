# The successor step, the table and the limit step of the stage count (retired 2026-09-06)

This is the material `src/L/GCH/StageCount.lagda.md` carried until
2026-09-06 to prove `StageCountedCoded` by ∈-induction on δ: the
successor step L_{β+1} ↪ β+1 through the least names, the pinned
binder kit and the name extension it needed, the table of least
injections at a δ whose stages all inject into δ, the limit step
L_δ ↪ δ through birth stages and the pairing, and the ∈-induction
that put the three together over the base L_ω ↪ ω.

The row is now proved at a different site.  `Site` of
src/L/GCH/StageCounted.lagda.md runs the hull machinery at the start
X = δ+1 with the target μ = `cardOf` δ: the start is counted by
`Shift` alone, the hull's count `HullCount.Count.hull↪κ` gives
M ↪ μ, the condensation gives a stage L_β with πX ≡ L_β, the
collapse fixes δ because δ+1 is transitive, and the chain
L_δ ↪ L_β ↪ M ↪ μ ↪ δ is the row.  Nothing below is reached from
the live tree any more.

WHAT STAYED IN THE LIVE CHAPTER: `pinAt`/`pin-in`/`pin-out`, the
injection formula `injFo` with `InjFo`, `isPropInjCode`,
`injcode-resp`, the sequence map `seq-map`, `Lω`,
`LimitStageCounted`, `move`, and the whole of section 6, the proof
that L_ω injects into ω.  src/L/GCH/HullCount.lagda.md consumes the
first group and the base; src/L/GCH/StageCounted.lagda.md consumes
`move`.

The material is KEPT HERE AS MATHEMATICS, not as a module: this file
is outside the library path and DOES NOT TYPECHECK on its own.

<!-- section 2 prose, retired -->
SECTION 2.  THE SUCCESSOR STEP.  At an infinite ordinal β with a
coded injection E : L_β ↪ β, the stage L_{β+1} = 𝒟ₒ(L_β) injects into
β+1, internally.

  Every member x of L_{β+1} has a least name (src/L/Choice/Step.lagda.md
  `leastNameOf`): a parameter-free code s at L_ω, an arity a, and a
  parameter environment e over L_β.  Since β is infinite the code is
  itself a member of L_β, so x ↦ s :: e is a map into the finite
  sequences over L_β.  Its graph is the least-name description
  `LeastNameAt` of src/L/Choice/Internal.lagda.md, with the code
  order, the stage order, the tower, its code set and the free code
  set pinned as constants, followed by the cons.  Then seqL L_β ↪
  seqL β by section 1 and seqL β ↪ β by src/L/GCH/Sequences.lagda.md.

  Binders, outermost first: R, P, B, C, C₀ pinned, then s, a, e.
  Inside all of them: e is 0, a is 1, s is 2, C₀ is 3, C is 4, B is
  5, P is 6, R is 7, y is 8, x is 9.


<!-- section 2 body: the pinned-binder kit, the name extension, the successor step -->
Five pinned binders and three plain binders, read once for a
variable body, and sealed.  Measured at this site: the same readings
checked at the concrete body of section 2 cost about 10 s per binder.

```agda
opaque
  pin5At : ∀ {n} (c₁ c₂ c₃ c₄ c₅ : S)
         → Formula S (suc (suc (suc (suc (suc n))))) → Formula S n
  pin5At c₁ c₂ c₃ c₄ c₅ φ = pinAt c₁ (pinAt c₂ (pinAt c₃ (pinAt c₄ (pinAt c₅ φ))))

  pin5-out : ∀ {n} (c₁ c₂ c₃ c₄ c₅ : S) (φ : Formula S (suc (suc (suc (suc (suc n))))))
             (γ : S ^ n)
           → ⟨ γ ⊨ pin5At c₁ c₂ c₃ c₄ c₅ φ ⟩ → ⟨ (c₅ ∷ c₄ ∷ c₃ ∷ c₂ ∷ c₁ ∷ γ) ⊨ φ ⟩
  pin5-out c₁ c₂ c₃ c₄ c₅ φ γ h =
    pin-out c₅ φ (c₄ ∷ c₃ ∷ c₂ ∷ c₁ ∷ γ)
      (pin-out c₄ (pinAt c₅ φ) (c₃ ∷ c₂ ∷ c₁ ∷ γ)
        (pin-out c₃ (pinAt c₄ (pinAt c₅ φ)) (c₂ ∷ c₁ ∷ γ)
          (pin-out c₂ (pinAt c₃ (pinAt c₄ (pinAt c₅ φ))) (c₁ ∷ γ)
            (pin-out c₁ (pinAt c₂ (pinAt c₃ (pinAt c₄ (pinAt c₅ φ)))) γ h))))

  pin5-in : ∀ {n} (c₁ c₂ c₃ c₄ c₅ : S) (φ : Formula S (suc (suc (suc (suc (suc n))))))
            (γ : S ^ n)
          → ⟨ (c₅ ∷ c₄ ∷ c₃ ∷ c₂ ∷ c₁ ∷ γ) ⊨ φ ⟩ → ⟨ γ ⊨ pin5At c₁ c₂ c₃ c₄ c₅ φ ⟩
  pin5-in c₁ c₂ c₃ c₄ c₅ φ γ h =
    pin-in c₁ (pinAt c₂ (pinAt c₃ (pinAt c₄ (pinAt c₅ φ)))) γ
      (pin-in c₂ (pinAt c₃ (pinAt c₄ (pinAt c₅ φ))) (c₁ ∷ γ)
        (pin-in c₃ (pinAt c₄ (pinAt c₅ φ)) (c₂ ∷ c₁ ∷ γ)
          (pin-in c₄ (pinAt c₅ φ) (c₃ ∷ c₂ ∷ c₁ ∷ γ)
            (pin-in c₅ φ (c₄ ∷ c₃ ∷ c₂ ∷ c₁ ∷ γ) h))))

  ∃₃ : ∀ {n} → Formula S (suc (suc (suc n))) → Formula S n
  ∃₃ φ = ∃̇ (∃̇ (∃̇ φ))

  -- Read by named functions with stated types, one per binder: the
  -- nested pattern-lambda form of this reading did not finish in 120 s.
  ∃₃-out : ∀ {n} (φ : Formula S (suc (suc (suc n)))) (γ : S ^ n)
         → ⟨ γ ⊨ ∃₃ φ ⟩
         → ∥ Σ[ s ∈ S ] Σ[ a ∈ S ] Σ[ e ∈ S ] ⟨ (e ∷ a ∷ s ∷ γ) ⊨ φ ⟩ ∥₁
  ∃₃-out {n} φ γ = PT.rec squash₁ at₁
    where
    Out : Type (ℓ-suc ℓ)
    Out = ∥ Σ[ s ∈ S ] Σ[ a ∈ S ] Σ[ e ∈ S ] ⟨ (e ∷ a ∷ s ∷ γ) ⊨ φ ⟩ ∥₁

    at₃ : (s a : S) → Σ[ e ∈ S ] ⟨ (e ∷ a ∷ s ∷ γ) ⊨ φ ⟩ → Out
    at₃ s a (e , h) = ∣ s , a , e , h ∣₁

    at₂ : (s : S) → Σ[ a ∈ S ] ∥ Σ[ e ∈ S ] ⟨ (e ∷ a ∷ s ∷ γ) ⊨ φ ⟩ ∥₁ → Out
    at₂ s (a , h) = PT.rec squash₁ (at₃ s a) h

    at₁ : Σ[ s ∈ S ] ∥ Σ[ a ∈ S ] ∥ Σ[ e ∈ S ] ⟨ (e ∷ a ∷ s ∷ γ) ⊨ φ ⟩ ∥₁ ∥₁ → Out
    at₁ (s , h) = PT.rec squash₁ (at₂ s) h

  ∃₃-in : ∀ {n} (φ : Formula S (suc (suc (suc n)))) (γ : S ^ n)
        → (s a e : S) → ⟨ (e ∷ a ∷ s ∷ γ) ⊨ φ ⟩ → ⟨ γ ⊨ ∃₃ φ ⟩
  ∃₃-in φ γ s a e h = ∣ s , ∣ a , ∣ e , h ∣₁ ∣₁ ∣₁
```

A name is determined by its code and its parameters.  Proved once, at
variable formulas and vectors, by J: at the reflexive length no
transport remains.  Measured at this site: the same assembly written
at the concrete names of section 2 did not finish in 150 s.

```agda
NameOf : Type ℓ → Type ℓ
NameOf X = Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) (suc k) × Vec X k)

name-ext : {X : Type ℓ} {k k' : ℕ} (e : k ≡ k')
           (χ : Formula (⊥* {ℓ}) (suc k)) (χ' : Formula (⊥* {ℓ}) (suc k'))
           (p : Vec X k) (p' : Vec X k')
         → fst (limitCode χ) ≡ fst (limitCode χ')
         → ((i : Fin k) (j : Fin k') → toℕ i ≡ toℕ j → lookup i p ≡ lookup j p')
         → _≡_ {A = NameOf X} (k , χ , p) (k' , χ' , p')
name-ext {X} {k} = J Motive base
  where
  Motive : (k' : ℕ) → k ≡ k' → Type (ℓ-suc ℓ)
  Motive k' e = (χ : Formula (⊥* {ℓ}) (suc k)) (χ' : Formula (⊥* {ℓ}) (suc k'))
                (p : Vec X k) (p' : Vec X k')
              → fst (limitCode χ) ≡ fst (limitCode χ')
              → ((i : Fin k) (j : Fin k') → toℕ i ≡ toℕ j → lookup i p ≡ lookup j p')
              → _≡_ {A = NameOf X} (k , χ , p) (k' , χ' , p')
  ext : {m : ℕ} (p p' : Vec X m) → ((i : Fin m) → lookup i p ≡ lookup i p') → p ≡ p'
  ext []      []       h = refl
  ext (x ∷ p) (y ∷ p') h = cong₂ _∷_ (h zero) (ext p p' (λ i → h (suc i)))
  base : Motive k refl
  base χ χ' p p' q h = λ i → k , code-inj χ χ' q i , ext p p' (λ m → h m m refl) i

module Succ (βL : S) (oβ : IsOrd (fst βL)) (β∉ω : ⟨ fst βL ∈ˢ ω ⟩ → Empty.⊥)
            (E : S) (code : InjCode E (LsetS (fst βL) oβ) βL) where

  private
    β : V ℓ
    β = fst βL

  -- The tower, its code set, and the free code set, sealed where they
  -- are built: each reaches a slot inside a satisfaction.
  opaque
    tw : S
    tw = LsetS β oβ

    tw-eq : tw ≡ LsetS β oβ
    tw-eq = refl

    cs : S
    cs = AllCodes (LsetS β oβ)

    cs-eq : fst cs ≡ fst (AllCodes (LsetS β oβ))
    cs-eq = refl

    c0 : S
    c0 = AllCodes ∅ʟ

    c0-eq : fst c0 ≡ fst (AllCodes ∅ʟ)
    c0-eq = refl

  -- The stage order on L_β, as an element of L, and the naming frame.
  w : SWO ⟪ Lset β ⟫
  w = carry (Lset β) (orderAt β oβ)

  Ps : S
  Ps = relL β (snd βL) oβ

  module NM = Naming (Lset β) w using ( Name; arity; codeOf; denote; formula; nameOrder; params )
  module A6 = At (Lset β) (snd (LsetS β oβ)) w using ( module Least; codeEl; codeEl-fst; envEl; envEl-fst; numAt; numAt-fst )
  module L6 = A6.Least codeOrder Ps codeOrder-rep codeOrder-fill
                (ixRel-rep β oβ Ps (relL-spec β (snd βL) oβ))
                (ixRel-fill β oβ Ps (relL-spec β (snd βL) oβ))
    using ( module Min )

  open NM using ( Name; arity; formula; params; codeOf; denote )

  pfam : (t : Name) → Fin (arity t) → V ℓ
  pfam t i = ⟪ Lset β ⟫↪ (lookup i (params t))

  -- L_ω sits inside L_β, because β is infinite.
  opaque
    Lω⊆Lβ : (z : V ℓ) → ⟨ z ∈ Lset ω ⟩ → ⟨ z ∈ Lset β ⟩
    Lω⊆Lβ z = go (ord-tri ω ω-ord β oβ)
      where
      go : Tri ω β → ⟨ z ∈ Lset ω ⟩ → ⟨ z ∈ Lset β ⟩
      go (inl ω∈β)       = λ h → Lset-mono {α = β} {β = ω} ω∈β h
      go (inr (inl e))   = subst (λ v → ⟨ z ∈ Lset v ⟩) e
      go (inr (inr β∈ω)) = Empty.rec (β∉ω β∈ω)

  -- The code of a name, as a member of the tower.  Sealed: a fiber,
  -- never to meet the unifier (as section 1 measured for `f`).
  opaque
    codeM : (t : Name) → ⟪ Lset β ⟫
    codeM t = fiber (Lset β) (Lω⊆Lβ (fst (codeOf t)) (snd (codeOf t))) .fst

    codeM-eq : (t : Name) → ⟪ Lset β ⟫↪ (codeM t) ≡ fst (codeOf t)
    codeM-eq t = fiber (Lset β) (Lω⊆Lβ (fst (codeOf t)) (snd (codeOf t))) .snd

  -- The value: the code consed onto the parameters, an environment over
  -- L_β of length arity + 1.
  val : Name → V ℓ
  val t = env (cons (fst (codeOf t)) (pfam t))

  valS : Name → S
  valS t = envS (LsetS β oβ) (cons (codeM t) (λ i → lookup i (params t)))

  valS-fst : (t : Name) → fst (valS t) ≡ val t
  valS-fst t = λ i → env (funExt pt i)
    where
    pt : (i : Fin (suc (arity t)))
       → ⟪ Lset β ⟫↪ (cons (codeM t) (λ j → lookup j (params t)) i)
       ≡ cons (fst (codeOf t)) (pfam t) i
    pt zero    = codeM-eq t
    pt (suc i) = refl

  -- -------------------------------------------------------------------
  -- 2.1  The graph, and its host reading.
  -- -------------------------------------------------------------------

  γ₇ : (y x : S) → S ^ 7
  γ₇ y x = c0 ∷ cs ∷ tw ∷ Ps ∷ codeOrder ∷ y ∷ x ∷ []

  Γ : (y x s a e : S) → S ^ 10
  Γ y x s a e = e ∷ a ∷ s ∷ γ₇ y x

  -- The least-name formula at slots, sealed, and its two readings at a
  -- variable environment.  The concrete instance below is only ever
  -- compared under the seal.  Measured at this site: the same two
  -- readings stated at the concrete environment cost 7.5 s each, and
  -- the graph readings through a transparent body 9 s each.
  module LNAt {n : ℕ} (R P B C C₀ s a e d : Fin n) where
    opaque
      Fo : Formula S n
      Fo = LeastNameAt R P B C C₀ s a e d

    module Rd (γ : S ^ n)
              (qR : fst (lookup R γ) ≡ fst codeOrder)
              (qP : fst (lookup P γ) ≡ fst Ps)
              (qB : lookup B γ ≡ LsetS β oβ)
              (qC : fst (lookup C γ) ≡ fst (AllCodes (LsetS β oβ)))
              (q₀ : fst (lookup C₀ γ) ≡ fst (AllCodes ∅ʟ)) where
      open L6.Min R P B C C₀ s a e d γ qR qP qB qC q₀ public

      opaque
        unfolding Fo

        fill : (t : Name) → Least t → ⟨ γ ⊨ Fo ⟩
        fill = LeastAt-fill

        read : ⟨ γ ⊨ Fo ⟩ → ∥ Σ[ t ∈ Name ] Least t ∥₁
        read = LeastAt-read

  module LF = LNAt {10} i7 i6 i5 i4 i3 i2 i1 i0 i9 using ( Fo; module Rd )
  module Min (y x s a e : S) = LF.Rd (Γ y x s a e) refl refl tw-eq cs-eq c0-eq

  LN : (y x s a e : S) → Type (ℓ-suc ℓ)
  LN y x s a e = ⟨ Γ y x s a e ⊨ LF.Fo ⟩

  ln-fill : (y x s a e : S) (t : Name) → Min.Least y x s a e t → LN y x s a e
  ln-fill = Min.fill

  ln-read : (y x s a e : S) → LN y x s a e → ∥ Σ[ t ∈ Name ] Min.Least y x s a e t ∥₁
  ln-read = Min.read

  -- The cons formula, sealed the same way.
  opaque
    cnFo : Formula S 10
    cnFo = consAtL i8 i2 i0

    cn-fill : (y x s a e : S) {k : ℕ} (g : Fin k → V ℓ) → fst e ≡ env g
            → fst y ≡ env (cons (fst s) g) → ⟨ Γ y x s a e ⊨ cnFo ⟩
    cn-fill y x s a e g qe q =
      subst ⟨_⟩ (sym (consAtL-adequate i8 i2 i0 (Γ y x s a e) g qe)) q

    cn-read : (y x s a e : S) {k : ℕ} (g : Fin k → V ℓ) → fst e ≡ env g
            → ⟨ Γ y x s a e ⊨ cnFo ⟩ → fst y ≡ env (cons (fst s) g)
    cn-read y x s a e g qe h =
      subst ⟨_⟩ (consAtL-adequate i8 i2 i0 (Γ y x s a e) g qe) h

  CN : (y x s a e : S) → Type (ℓ-suc ℓ)
  CN y x s a e = ⟨ Γ y x s a e ⊨ cnFo ⟩

  Wit : (y x : S) → Type (ℓ-suc ℓ)
  Wit y x = ∥ Σ[ s ∈ S ] Σ[ a ∈ S ] Σ[ e ∈ S ] (LN y x s a e × CN y x s a e) ∥₁

  opaque
    body : Formula S 10
    body = LF.Fo ∧̇ cnFo

    fo : Formula S 2
    fo = pin5At codeOrder Ps tw cs c0 (∃₃ body)

    fo-out : (y x : S) → ⟨ (y ∷ x ∷ []) ⊨ fo ⟩ → Wit y x
    fo-out y x h =
      ∃₃-out body (γ₇ y x) (pin5-out codeOrder Ps tw cs c0 (∃₃ body) (y ∷ x ∷ []) h)

    fo-in : (y x : S) → Wit y x → ⟨ (y ∷ x ∷ []) ⊨ fo ⟩
    fo-in y x = PT.rec (snd ((y ∷ x ∷ []) ⊨ fo))
      (λ { (s , a , e , hb) → pin5-in codeOrder Ps tw cs c0 (∃₃ body) (y ∷ x ∷ [])
             (∃₃-in body (γ₇ y x) s a e hb) })

  -- -------------------------------------------------------------------
  -- 2.2  At a member x of L_{β+1} with least name t: the value satisfies
  --      the graph, and nothing else does.
  -- -------------------------------------------------------------------

  Mem : S → Type (ℓ-suc ℓ)
  Mem x = ⟨ fst x ∈ Lset (sucV β) ⟩

  -- The least name, sealed: a well-founded selection, never to meet
  -- the unifier.  Being a least name is sealed too, at a variable
  -- name, so that the selected name is only ever compared under the
  -- seal.  Measured at this site: compared under the transparent
  -- predicate, the name order unfolds to its level search, 17 s.
  opaque
    leastP : (x : S) → Mem x → Σ[ t ∈ Name ] IsLeastName β w t (fst x)
    leastP x m = leastNameOf β w (fst x , m)

  opaque
    IsLN : Name → S → Type (ℓ-suc ℓ)
    IsLN t x = IsLeastName β w t (fst x)

    isLN-in : (t : Name) (x : S) → IsLeastName β w t (fst x) → IsLN t x
    isLN-in t x h = h

    isLN-out : (t : Name) (x : S) → IsLN t x → IsLeastName β w t (fst x)
    isLN-out t x h = h

  opaque
    least : (x : S) → Mem x → Name
    least x m = leastP x m .fst

    least-isLN : (x : S) (m : Mem x) → IsLN (least x m) x
    least-isLN x m = isLN-in (leastP x m .fst) x (leastP x m .snd)

  least-is : (x : S) (m : Mem x) → IsLeastName β w (least x m) (fst x)
  least-is x m = isLN-out (least x m) x (least-isLN x m)

  fn : (x : S) → Mem x → S
  fn x m = valS (least x m)

  wit : (x : S) (t : Name) → IsLeastName β w t (fst x) → Wit (valS t) x
  wit x t hl = ∣ A6.codeEl t , A6.numAt (arity t) , A6.envEl t
    , ( ln-fill (valS t) x (A6.codeEl t) (A6.numAt (arity t)) (A6.envEl t) t
          ( (A6.codeEl-fst t , A6.numAt-fst (arity t) , A6.envEl-fst t , sym (hl .fst))
          , λ t' q h' → hl .snd t' (sym q) h' )
      , cn-fill (valS t) x (A6.codeEl t) (A6.numAt (arity t)) (A6.envEl t)
          (pfam t) (A6.envEl-fst t)
          (valS-fst t ∙ cong (λ c → env (cons c (pfam t))) (sym (A6.codeEl-fst t))) ) ∣₁

  only : (x : S) (t : Name) → IsLeastName β w t (fst x)
       → (y : S) → Wit y x → fst y ≡ fst (valS t)
  only x t hl y = PT.rec (setIsSet (fst y) (fst (valS t)))
    (λ { (s , a , e , (hl , hc)) → PT.rec (setIsSet (fst y) (fst (valS t)))
      (λ { (t' , ((qs , qa , qe , qd) , mt)) → Read.final s a e hc t' qs qe qd mt })
      (ln-read y x s a e hl) })
    where
    module Read (s a e : S) (hc : CN y x s a e) (t' : Name)
                (qs : fst s ≡ fst (codeOf t'))
                (qe : fst e ≡ env (pfam t'))
                (qd : fst x ≡ denote t')
                (mt : Min.IsMin y x s a e t') where
      hl' : IsLeastName β w t' (fst x)
      hl' = sym qd , λ t'' q h → mt t'' (sym q) h

      t'≡t : t' ≡ t
      t'≡t = cong fst (isPropLeastOf NM.nameOrder (denotesAt β w (fst x)) (t' , hl') (t , hl))

      final : fst y ≡ fst (valS t)
      final = cn-read y x s a e (pfam t') qe hc
            ∙ (λ i → env (cons (qs i) (pfam t')))
            ∙ (λ i → val (t'≡t i))
            ∙ sym (valS-fst t)

  -- -------------------------------------------------------------------
  -- 2.3  A name is determined by its code and its parameters: equal
  --      values have one arity, one formula and one parameter vector.
  -- -------------------------------------------------------------------

  private
    isLpar : (t : Name) (i : Fin (suc (arity t)))
           → ⟨ isL (cons (fst (codeOf t)) (pfam t) i) ⟩
    isLpar t zero    = isL-trans (snd (codeOf t)) (isL-Lset ω ω-ord)
    isLpar t (suc i) = isL-trans (member (Lset β) (lookup i (params t))) (isL-Lset β oβ)

    -- The entry of an environment at its own index.
    at : {k : ℕ} (h : Fin k → V ℓ) (j : Fin k) → ⟨ pr (# (toℕ j)) (h j) ∈ env h ⟩
    at h j = subst ⟨_⟩ (sym (lookup-spec h j (h j))) refl

  val-inj : (t t' : Name) → val t ≡ val t' → t ≡ t'
  val-inj t t' q = name-ext e (formula t) (formula t') (params t) (params t') qc pt
    where
    e : arity t ≡ arity t'
    e = injSuc (env-len (valS t) (cons (fst (codeOf t)) (pfam t))
                 (cons (fst (codeOf t')) (pfam t')) (isLpar t) (isLpar t')
                 (valS-fst t) (valS-fst t ∙ q))

    qc : fst (codeOf t) ≡ fst (codeOf t')
    qc = subst ⟨_⟩ (lookup-spec (cons (fst (codeOf t')) (pfam t')) zero (fst (codeOf t)))
           (subst (λ v → ⟨ pr (# zero) (fst (codeOf t)) ∈ v ⟩) q
             (at (cons (fst (codeOf t)) (pfam t)) zero))

    -- Entry i of the first parameter vector is entry j of the second
    -- whenever the indices agree, read through the environments.
    pt : (i : Fin (arity t)) (j : Fin (arity t')) → toℕ i ≡ toℕ j
       → lookup i (params t) ≡ lookup j (params t')
    pt i j eij = ↪-inj {a = Lset β}
      (subst ⟨_⟩ (lookup-spec (cons (fst (codeOf t')) (pfam t')) (suc j) (pfam t i))
        (subst2 (λ k v → ⟨ pr (# (suc k)) (pfam t i) ∈ v ⟩) eij q
          (at (cons (fst (codeOf t)) (pfam t)) (suc i))))

  -- 2.4  The definable map, the coded injection, and the step.
  -- -------------------------------------------------------------------

  into : (x : S) (m : Mem x) → ⟨ fst (fn x m) ∈ˢ fst (seqL (LsetS β oβ)) ⟩
  into x m = seqL-in (LsetS β oβ) (suc (arity t)) (valS t)
    (envSet-in (LsetS β oβ) (cons (codeM t) (λ i → lookup i (params t))))
    where
    t : Name
    t = least x m

  D : DefinableMap
  D = record
    { dom = LsetS (sucV β) (suc-ord oβ) ; cod = seqL (LsetS β oβ)
    ; fn = fn ; into = into ; graph = fo
    ; defines = λ x m → fo-in (fn x m) x (wit x (least x m) (least-is x m))
    ; only    = λ x m y h → Σ≡Prop (λ v → snd (isL v))
                  (only x (least x m) (least-is x m) y (fo-out y x h)) }

  inj : (x : S) (m : Mem x) (x' : S) (m' : Mem x')
      → fst (fn x m) ≡ fst (fn x' m') → fst x ≡ fst x'
  inj x m x' m' q =
      sym (least-is x m .fst)
    ∙ (λ i → denote (val-inj (least x m) (least x' m')
        (sym (valS-fst (least x m)) ∙ q ∙ valS-fst (least x' m')) i))
    ∙ least-is x' m' .fst

  names : InjL (LsetS (sucV β) (suc-ord oβ)) (seqL (LsetS β oβ))
  names = Inj.injL D inj

  -- THE STEP.  L_{β+1} ↪ seqL L_β ↪ seqL β ↪ β ⊆ β+1.
  result : InjL (LsetS (sucV β) (suc-ord oβ)) (ordL (sucV β) (suc-ord oβ))
  result = injl-trans (LsetS (sucV β) (suc-ord oβ)) (seqL (LsetS β oβ)) (ordL (sucV β) (suc-ord oβ))
    names
    (injl-trans (seqL (LsetS β oβ)) (seqL βL) (ordL (sucV β) (suc-ord oβ))
      (seq-map (LsetS β oβ) βL E code)
      (injl-trans (seqL βL) βL (ordL (sucV β) (suc-ord oβ))
        (seq-count βL oβ β∉ω)
        (inclusion-coded βL (ordL (sucV β) (suc-ord oβ))
          (λ z z∈β → suc-ord oβ .fst z∈β (self∈sucV β)))))

succ-step : (βL : S) (oβ : IsOrd (fst βL)) → (⟨ fst βL ∈ˢ ω ⟩ → Empty.⊥)
          → InjL (LsetS (fst βL) oβ) βL
          → InjL (LsetS (sucV (fst βL)) (suc-ord oβ)) (ordL (sucV (fst βL)) (suc-ord oβ))
succ-step βL oβ β∉ω = PT.rec squash₁
  (λ { (E , code) → Succ.result βL oβ β∉ω E code })
```

<!-- section 3 prose, retired -->
SECTION 3.  THE TABLE OF LEAST INJECTIONS.  At an ordinal δ such that
every stage L_β, β ∈ δ, merely injects into δ internally, the family
β ↦ e_β of the stage-order-least such injection codes is one set of
L: the graph of a definable map on δ.

  A stage γ is chosen that holds one code for every β ∈ δ: the least
  stage holding one is a function of β (src/L/Stage.lagda.md
  `leastOrd`), and γ bounds those.  The selection of e_β, its graph
  and its table are `L.GCH.Least` at γ, δ and the code predicate of
  `CodeFo`: over (e ∷ b ∷ []), "there is B, the tower at b, with e
  coding an injection of B into δ".  Inside B: B is 0, e is 1, b is 2.

<!-- the code predicate and the table of least injections -->
The code predicate at slots, sealed, with its two readings at a
variable environment: "there is B, the tower at b, with e coding an
injection of B into δ".  Inside B: B is 0 and the slots shift by one.
Measured at this site: the two readings written at the concrete
environment cost 7 s each.

```agda
module CodeFo {n : ℕ} (δL : S) (e b : Fin n) where
  opaque
    Fo : Formula S n
    Fo = ∃̇ (LsetGraphAt i0 (suc b) ∧̇ injFo δL (suc e) i0)

    read : (γ : S ^ n) (ev bv : S) → lookup e γ ≡ ev → lookup b γ ≡ bv
         → (ob : IsOrd (fst bv)) → ⟨ γ ⊨ Fo ⟩ → InjCode ev (LsetS (fst bv) ob) δL
    read γ ev bv qe qb ob = PT.rec (isPropInjCode ev (LsetS (fst bv) ob) δL) at
      where
      at : Σ[ B ∈ S ] ( ⟨ (B ∷ γ) ⊨ LsetGraphAt i0 (suc b) ⟩
                      × ⟨ (B ∷ γ) ⊨ injFo δL (suc e) i0 ⟩ )
         → InjCode ev (LsetS (fst bv) ob) δL
      at (B , hg , hi) = injcode-resp (lookup e γ) ev B (LsetS (fst bv) ob) δL (cong fst qe)
        ( Lset-only i0 (suc b) (B ∷ γ) hg (subst (λ v → IsOrd (fst v)) (sym qb) ob)
        ∙ cong (λ v → Lset (fst v)) qb )
        (InjFo.read δL (suc e) i0 (B ∷ γ) hi)

    fill : (γ : S ^ n) (ev bv : S) → lookup e γ ≡ ev → lookup b γ ≡ bv
         → (ob : IsOrd (fst bv)) → InjCode ev (LsetS (fst bv) ob) δL → ⟨ γ ⊨ Fo ⟩
    fill γ ev bv qe qb ob code =
      ∣ LsetS (fst bv) ob
      , Lset-defines i0 (suc b) (LsetS (fst bv) ob ∷ γ) (subst (λ v → IsOrd (fst v)) (sym qb) ob)
          (cong (λ v → Lset (fst v)) (sym qb))
      , InjFo.fill δL (suc e) i0 (LsetS (fst bv) ob ∷ γ)
          (injcode-resp ev (lookup e γ) (LsetS (fst bv) ob) (LsetS (fst bv) ob) δL
            (cong fst (sym qe)) refl code) ∣₁

module Table (δL : S) (oδ : IsOrd (fst δL))
             (have : (β : V ℓ) (oβ : IsOrd β) → ⟨ β ∈ fst δL ⟩ → InjL (LsetS β oβ) δL)
             where

  private
    δ : V ℓ
    δ = fst δL

  -- -------------------------------------------------------------------
  -- 3.1  The bounding stage γ.
  -- -------------------------------------------------------------------

  -- Some code at the stage σ.
  HasCode : (β : V ℓ) (oβ : IsOrd β) → V ℓ → hProp (ℓ-suc ℓ)
  HasCode β oβ σ =
    ∥ Σ[ F ∈ S ] (⟨ fst F ∈ Lset σ ⟩ × InjCode F (LsetS β oβ) δL) ∥₁ , squash₁

  -- An index with its ordinal-hood and its membership in δ.
  Ix3 : Type (ℓ-suc ℓ)
  Ix3 = Σ[ b ∈ V ℓ ] (IsOrd b × ⟨ b ∈ δ ⟩)

  -- The least stage holding a code, a function of the index.  Sealed:
  -- a well-founded selection, never to meet the unifier.
  opaque
    ls : (p : Ix3) → LeastOrd (HasCode (fst p) (fst (snd p)))
    ls (β , oβ , β∈δ) = PT.rec (isPropLeastOrd (HasCode β oβ)) from (have β oβ β∈δ)
      where
      from : Σ[ F ∈ S ] InjCode F (LsetS β oβ) δL → LeastOrd (HasCode β oβ)
      from (F , code) = leastOrd (HasCode β oβ)
        ∣ stage (fst F) (snd F) , stage-ord (fst F) (snd F)
        , ∣ F , stage-mem (fst F) (snd F) , code ∣₁ ∣₁

  private
    at : ⟪ δ ⟫ → Ix3
    at m = ⟪ δ ⟫↪ m , mem-ord {A = δ} oδ (⟪ δ ⟫↪ m) (member δ m) , member δ m

  -- The bound, sealed with its three readings.
  opaque
    γ : V ℓ
    γ = boundingOrd ⟪ δ ⟫ (λ m → ls (at m) .fst) (λ m → ls (at m) .snd .fst) .fst

    oγ : IsOrd γ
    oγ = boundingOrd ⟪ δ ⟫ (λ m → ls (at m) .fst) (λ m → ls (at m) .snd .fst) .snd .fst

    bnd-in : (m : ⟪ δ ⟫) → ⟨ ls (at m) .fst ∈ γ ⟩
    bnd-in = boundingOrd ⟪ δ ⟫ (λ m → ls (at m) .fst) (λ m → ls (at m) .snd .fst) .snd .snd

  -- Every β ∈ δ has a code in L_γ: its least stage sits below γ.
  code-at-γ : (β : V ℓ) (oβ : IsOrd β) (β∈δ : ⟨ β ∈ δ ⟩) → ⟨ HasCode β oβ γ ⟩
  code-at-γ β oβ β∈δ = PT.map raise (ls p .snd .snd .fst)
    where
    p : Ix3
    p = β , oβ , β∈δ
    m : ⟪ δ ⟫
    m = fiber δ β∈δ .fst
    -- The two indices are equal, so their least stages are.
    pth : at m ≡ p
    pth = Σ≡Prop (λ b → isProp× (isPropIsOrd b) (snd (b ∈ δ))) (fiber δ β∈δ .snd)
    σ∈γ : ⟨ ls p .fst ∈ γ ⟩
    σ∈γ = subst (λ w → ⟨ w ∈ γ ⟩) (λ i → ls (pth i) .fst) (bnd-in m)
    raise : Σ[ F ∈ S ] (⟨ fst F ∈ Lset (ls p .fst) ⟩ × InjCode F (LsetS β oβ) δL)
          → Σ[ F ∈ S ] (⟨ fst F ∈ Lset γ ⟩ × InjCode F (LsetS β oβ) δL)
    raise (F , h , code) = F , Lset-mono {α = γ} {β = ls p .fst} σ∈γ h , code

  -- -------------------------------------------------------------------
  -- 3.2  The least code at each index, and its table: `L.GCH.Least` at
  -- γ, δ and the code predicate.
  -- -------------------------------------------------------------------

  ordAt : (b : S) → ⟨ fst b ∈ δ ⟩ → IsOrd (fst b)
  ordAt b m = mem-ord {A = δ} oδ (fst b) m

  private
    module CF = CodeFo {2} δL i0 i1 using ( Fo; fill; read )

    have-γ : (b : S) (m : ⟨ fst b ∈ δ ⟩)
           → ∥ Σ[ e ∈ S ] (⟨ fst e ∈ Lset γ ⟩ × ⟨ (e ∷ b ∷ []) ⊨ CF.Fo ⟩) ∥₁
    have-γ b m = PT.map
      (λ { (F , h , code) → F , h , CF.fill (F ∷ b ∷ []) F b refl refl (ordAt b m) code })
      (code-at-γ (fst b) (ordAt b m) m)

    module Ls = Least γ oγ δL CF.Fo have-γ using ( fn; fn-holds; T; T-in; T-out )

  eS : (b : S) → ⟨ fst b ∈ δ ⟩ → S
  eS = Ls.fn

  e-code : (b : S) (m : ⟨ fst b ∈ δ ⟩) → InjCode (eS b m) (LsetS (fst b) (ordAt b m)) δL
  e-code b m = CF.read (eS b m ∷ b ∷ []) (eS b m) b refl refl (ordAt b m) (Ls.fn-holds b m)

  -- THE TABLE: the set of pairs (b, e_b), b ∈ δ.
  T : S
  T = Ls.T

  T-in : (b : S) (m : ⟨ fst b ∈ δ ⟩) → ⟨ pr (fst b) (fst (eS b m)) ∈ fst T ⟩
  T-in = Ls.T-in

  T-out : (b e : S) → ⟨ pr (fst b) (fst e) ∈ fst T ⟩
        → Σ[ m ∈ ⟨ fst b ∈ δ ⟩ ] (fst e ≡ fst (eS b m))
  T-out = Ls.T-out
```

<!-- section 4: the limit step -->
SECTION 4.  THE LIMIT STEP.  At a limit ordinal δ (closed under the
successor) such that every stage L_β, β ∈ δ, merely injects into δ
internally, L_δ injects into δ.

  x ∈ L_δ is born at some stage: b_x = birth x + 1 is the least
  ordinal with x ∈ L_{b_x}, and b_x ∈ δ because δ is a limit.  With
  the table T of section 3, x ↦ (b_x, e_{b_x}(x)) lands in prodL δ,
  and prodL δ ↪ δ by the pairing at δ.

  The graph, over (y ∷ x ∷ []): "there is b ∈ δ and e with (b, e) ∈ T
  and some v with (x, v) ∈ e and y = (b, v), and for every b' ∈ b and
  e' with (b', e') ∈ T no v' has (x, v') ∈ e'".  Binders: b, e, then
  v; the leastness clause binds b', e', then v'.  Inside b, e: e is
  0, b is 1, y is 2, x is 3; v adds one; in the leastness clause e'
  is 0, b' is 1, e is 2, b is 3, y is 4, x is 5, and v' adds one.

```agda
module Lim (δL : S) (oδ : IsOrd (fst δL)) (δ∉ω : ⟨ fst δL ∈ˢ ω ⟩ → Empty.⊥)
           (lim : (β : V ℓ) → ⟨ β ∈ fst δL ⟩ → ⟨ sucV β ∈ fst δL ⟩)
           (have : (β : V ℓ) (oβ : IsOrd β) → ⟨ β ∈ fst δL ⟩ → InjL (LsetS β oβ) δL)
           where

  private
    δ : V ℓ
    δ = fst δL

  module Tb = Table δL oδ have using ( T; T-in; T-out; e-code; eS; ordAt )
  open Tb using ( T; T-in; T-out; eS; e-code; ordAt )

  -- -------------------------------------------------------------------
  -- 4.1  The value at x: its birth successor, and the entry there.
  -- -------------------------------------------------------------------

  Mem : S → Type (ℓ-suc ℓ)
  Mem x = ⟨ fst x ∈ Lset δ ⟩

  module AtX (x : S) (m : Mem x) where

    b : V ℓ
    b = sucV (birth (fst x) (snd x))

    ob : IsOrd b
    ob = suc-ord (birth-ord (fst x) (snd x))

    b∈δ : ⟨ b ∈ δ ⟩
    b∈δ = lim (birth (fst x) (snd x)) (birth-in δ oδ (fst x) (snd x) m)

    bS : S
    bS = ordL b ob

    e : S
    e = eS bS b∈δ

    x∈Lb : ⟨ fst x ∈ Lset b ⟩
    x∈Lb = birth-mem (fst x) (snd x)

    code : InjCode e (LsetS b (ordAt bS b∈δ)) δL
    code = e-code bS b∈δ

    -- The entry, sealed with its graph: a readback, never to meet the
    -- unifier.
    opaque
      v : S
      v = Extract.toFun e (LsetS b (ordAt bS b∈δ)) (fst code) (fst (snd code)) (x , x∈Lb)

      v-graph : ⟨ pr (fst x) (fst v) ∈ fst e ⟩
      v-graph = Extract.toFun-graph e (LsetS b (ordAt bS b∈δ)) (fst code) (fst (snd code)) (x , x∈Lb)

    v∈δ : ⟨ fst v ∈ δ ⟩
    v∈δ = snd (snd (snd code)) x v v-graph

    y₀ : S
    y₀ = prʟ bS v

    -- No stage below b holds x.
    not-below : (b' : V ℓ) → IsOrd b' → ⟨ b' ∈ b ⟩ → ⟨ fst x ∈ Lset b' ⟩ → Empty.⊥
    not-below b' ob' b'∈b hx = stage-earliest (fst x) (snd x) b' ob' hx
      (subst (λ w → ⟨ b' ∈ w ⟩) (birth-suc (fst x) (snd x)) b'∈b)

  fn : (x : S) → Mem x → S
  fn x m = AtX.y₀ x m

  -- An entry (x, v') of a table value at b' puts x in L_{b'}.
  entry-stage : (b' e' : S) → ⟨ pr (fst b') (fst e') ∈ fst T ⟩
              → (x v' : S) → ⟨ pr (fst x) (fst v') ∈ fst e' ⟩
              → Σ[ m' ∈ ⟨ fst b' ∈ δ ⟩ ] ⟨ fst x ∈ Lset (fst b') ⟩
  entry-stage b' e' ht x v' hv = m' , domAt-out zero (suc zero)
      (eS b' m' ∷ LsetS (fst b') (ordAt b' m') ∷ []) (fst (snd (e-code b' m'))) x v'
      (subst (λ w → ⟨ pr (fst x) (fst v') ∈ w ⟩) (T-out b' e' ht .snd) hv)
    where
    m' = T-out b' e' ht .fst

  -- -------------------------------------------------------------------
  -- 4.2  The graph, and its host reading.
  -- -------------------------------------------------------------------

  LWit : (y x : S) → Type (ℓ-suc ℓ)
  LWit y x = ∥ Σ[ b ∈ S ] Σ[ e ∈ S ] Σ[ v ∈ S ]
      ( ⟨ fst b ∈ δ ⟩
      × ⟨ pr (fst b) (fst e) ∈ fst T ⟩
      × ⟨ pr (fst x) (fst v) ∈ fst e ⟩
      × (fst y ≡ pr (fst b) (fst v))
      × ((b' e' : S) → ⟨ fst b' ∈ fst b ⟩ → ⟨ pr (fst b') (fst e') ∈ fst T ⟩
          → (v' : S) → ⟨ pr (fst x) (fst v') ∈ fst e' ⟩ → Empty.⊥) ) ∥₁

  opaque
    private
      leastFo : Formula S 4
      leastFo = ∀̇∈ (var i1) (∀̇ (appC T i1 i0 ⇒̇ ¬̇ (∃̇ (appAt i1 i6 i0))))

      valFo : Formula S 4
      valFo = ∃̇ (appAt i1 i4 i0 ∧̇ prAtL i3 i2 i0)

      body : Formula S 4
      body = appC T i1 i0 ∧̇ valFo ∧̇ leastFo

    fo : Formula S 2
    fo = ∃̇∈ (con δL) (∃̇ body)

    private
      leastOut : (y x b e : S) → ⟨ (e ∷ b ∷ y ∷ x ∷ []) ⊨ leastFo ⟩
               → (b' e' : S) → ⟨ fst b' ∈ fst b ⟩ → ⟨ pr (fst b') (fst e') ∈ fst T ⟩
               → (v' : S) → ⟨ pr (fst x) (fst v') ∈ fst e' ⟩ → Empty.⊥
      leastOut y x b e hl b' e' hb ht v' hv =
        hl b' hb e' (subst ⟨_⟩ (sym (appC-adequate T i1 i0 (e' ∷ b' ∷ e ∷ b ∷ y ∷ x ∷ []))) ht)
          ∣ v' , subst ⟨_⟩ (sym (appAt-adequate i1 i6 i0 (v' ∷ e' ∷ b' ∷ e ∷ b ∷ y ∷ x ∷ []))) hv ∣₁

      leastIn : (y x b e : S)
              → ((b' e' : S) → ⟨ fst b' ∈ fst b ⟩ → ⟨ pr (fst b') (fst e') ∈ fst T ⟩
                  → (v' : S) → ⟨ pr (fst x) (fst v') ∈ fst e' ⟩ → Empty.⊥)
              → ⟨ (e ∷ b ∷ y ∷ x ∷ []) ⊨ leastFo ⟩
      leastIn y x b e mn b' hb e' ht = PT.rec Empty.isProp⊥
        (λ { (v' , hv) → mn b' e' hb
              (subst ⟨_⟩ (appC-adequate T i1 i0 (e' ∷ b' ∷ e ∷ b ∷ y ∷ x ∷ [])) ht) v'
              (subst ⟨_⟩ (appAt-adequate i1 i6 i0 (v' ∷ e' ∷ b' ∷ e ∷ b ∷ y ∷ x ∷ [])) hv) })

      valOut : (y x b e : S) → ⟨ (e ∷ b ∷ y ∷ x ∷ []) ⊨ valFo ⟩
             → ∥ Σ[ v ∈ S ] (⟨ pr (fst x) (fst v) ∈ fst e ⟩ × (fst y ≡ pr (fst b) (fst v))) ∥₁
      valOut y x b e = PT.map (λ { (v , (hv , hy)) →
        v , ( subst ⟨_⟩ (appAt-adequate i1 i4 i0 (v ∷ e ∷ b ∷ y ∷ x ∷ [])) hv
            , subst ⟨_⟩ (prAtL-adequate i3 i2 i0 (v ∷ e ∷ b ∷ y ∷ x ∷ [])) hy ) })

      valIn : (y x b e v : S) → ⟨ pr (fst x) (fst v) ∈ fst e ⟩ → fst y ≡ pr (fst b) (fst v)
            → ⟨ (e ∷ b ∷ y ∷ x ∷ []) ⊨ valFo ⟩
      valIn y x b e v hv hy =
        ∣ v , ( subst ⟨_⟩ (sym (appAt-adequate i1 i4 i0 (v ∷ e ∷ b ∷ y ∷ x ∷ []))) hv
              , subst ⟨_⟩ (sym (prAtL-adequate i3 i2 i0 (v ∷ e ∷ b ∷ y ∷ x ∷ []))) hy ) ∣₁

      bodyOut : (y x b e : S) → ⟨ fst b ∈ δ ⟩ → ⟨ (e ∷ b ∷ y ∷ x ∷ []) ⊨ body ⟩ → LWit y x
      bodyOut y x b e hb (ht , hv , hl) = PT.map
        (λ { (v , (hv' , hy)) →
          b , e , v
          , ( hb
            , subst ⟨_⟩ (appC-adequate T i1 i0 (e ∷ b ∷ y ∷ x ∷ [])) ht
            , hv' , hy
            , leastOut y x b e hl ) })
        (valOut y x b e hv)

    fo-out : (y x : S) → ⟨ (y ∷ x ∷ []) ⊨ fo ⟩ → LWit y x
    fo-out y x = PT.rec squash₁ (λ { (b , (hb , h)) →
      PT.rec squash₁ (λ { (e , hbody) → bodyOut y x b e hb hbody }) h })

    fo-in : (y x : S) → LWit y x → ⟨ (y ∷ x ∷ []) ⊨ fo ⟩
    fo-in y x = PT.rec (snd ((y ∷ x ∷ []) ⊨ fo))
      (λ { (b , e , v , (hb , ht , hv , hy , mn)) →
        ∣ b , ( hb
              , ∣ e , ( subst ⟨_⟩ (sym (appC-adequate T i1 i0 (e ∷ b ∷ y ∷ x ∷ []))) ht
                      , valIn y x b e v hv hy
                      , leastIn y x b e mn ) ∣₁ ) ∣₁ })

  -- -------------------------------------------------------------------
  -- 4.3  The value satisfies the graph, and nothing else does.
  -- -------------------------------------------------------------------

  wit : (x : S) (m : Mem x) → LWit (fn x m) x
  wit x m = ∣ X.bS , X.e , X.v
    , ( X.b∈δ , T-in X.bS X.b∈δ , X.v-graph , prʟ-fst X.bS X.v , mn ) ∣₁
    where
    module X = AtX x m using ( b; bS; b∈δ; code; e; not-below; ob; v; v-graph; v∈δ )
    mn : (b' e' : S) → ⟨ fst b' ∈ X.b ⟩ → ⟨ pr (fst b') (fst e') ∈ fst T ⟩
       → (v' : S) → ⟨ pr (fst x) (fst v') ∈ fst e' ⟩ → Empty.⊥
    mn b' e' hb ht v' hv = X.not-below (fst b') (ordAt b' (fst es)) hb (snd es)
      where
      es = entry-stage b' e' ht x v' hv

  only : (x : S) (m : Mem x) (y : S) → LWit y x → fst y ≡ fst (fn x m)
  only x m y = PT.rec (setIsSet (fst y) (fst (fn x m)))
    (λ { (b , e , v , (hb , ht , hv , hy , mn)) → Read.final b e v hb ht hv hy mn })
    where
    module X = AtX x m using ( b; bS; b∈δ; code; e; not-below; ob; v; v-graph; v∈δ )
    module Read (b e v : S) (hb : ⟨ fst b ∈ δ ⟩)
                (ht : ⟨ pr (fst b) (fst e) ∈ fst T ⟩)
                (hv : ⟨ pr (fst x) (fst v) ∈ fst e ⟩)
                (hy : fst y ≡ pr (fst b) (fst v))
                (mn : (b' e' : S) → ⟨ fst b' ∈ fst b ⟩ → ⟨ pr (fst b') (fst e') ∈ fst T ⟩
                    → (v' : S) → ⟨ pr (fst x) (fst v') ∈ fst e' ⟩ → Empty.⊥) where

      x∈Lb : ⟨ fst x ∈ Lset (fst b) ⟩
      x∈Lb = snd (entry-stage b e ht x v hv)

      -- b is the birth successor: below it no stage holds x, and above
      -- it the birth successor itself violates the leastness clause.
      qb : fst b ≡ X.b
      qb = go (ord-tri (fst b) (ordAt b hb) X.b X.ob)
        where
        go : Tri (fst b) X.b → fst b ≡ X.b
        go (inl b∈)       = Empty.rec (X.not-below (fst b) (ordAt b hb) b∈ x∈Lb)
        go (inr (inl q))  = q
        go (inr (inr b∋)) = Empty.rec (mn X.bS X.e b∋ (T-in X.bS X.b∈δ) X.v X.v-graph)

      -- The table value at b is the value at the birth successor.
      pth : _≡_ {A = Σ[ c ∈ S ] ⟨ fst c ∈ δ ⟩} (b , T-out b e ht .fst) (X.bS , X.b∈δ)
      pth = Σ≡Prop (λ c → snd (fst c ∈ δ)) (Σ≡Prop (λ w → snd (isL w)) qb)

      qe : fst e ≡ fst X.e
      qe = T-out b e ht .snd ∙ (λ i → fst (eS (fst (pth i)) (snd (pth i))))

      qv : fst v ≡ fst X.v
      qv = svAt-out zero (X.e ∷ LsetS X.b (ordAt X.bS X.b∈δ) ∷ []) (fst X.code) x v X.v
             (subst (λ w → ⟨ pr (fst x) (fst v) ∈ w ⟩) qe hv) X.v-graph

      final : fst y ≡ fst (fn x m)
      final = hy ∙ (λ i → pr (qb i) (qv i)) ∙ sym (prʟ-fst X.bS X.v)

  -- -------------------------------------------------------------------
  -- 4.4  The definable map, injective, hence coded; then the pairing.
  -- -------------------------------------------------------------------

  into : (x : S) (m : Mem x) → ⟨ fst (fn x m) ∈ˢ fst (prodL δL) ⟩
  into x m = subst (λ w → ⟨ w ∈ˢ fst (prodL δL) ⟩) (sym (prʟ-fst X.bS X.v))
    (prodL-in δL X.bS X.v X.b∈δ X.v∈δ)
    where module X = AtX x m

  D : DefinableMap
  D = record
    { dom = LsetS δ oδ ; cod = prodL δL ; fn = fn ; into = into ; graph = fo
    ; defines = λ x m → fo-in (fn x m) x (wit x m)
    ; only    = λ x m y h → Σ≡Prop (λ w → snd (isL w)) (only x m y (fo-out y x h)) }

  inj : (x : S) (m : Mem x) (x' : S) (m' : Mem x')
      → fst (fn x m) ≡ fst (fn x' m') → fst x ≡ fst x'
  inj x m x' m' q =
    injAt-out zero (X.e ∷ LsetS X.b (ordAt X.bS X.b∈δ) ∷ []) (fst (snd (snd X.code)))
      X.v x x' X.v-graph
      (subst2 (λ w u → ⟨ pr (fst x') w ∈ u ⟩) (sym qv) qe X'.v-graph)
    where
    module X  = AtX x m using ( b; bS; b∈δ; code; e; not-below; ob; v; v-graph; v∈δ )
    module X' = AtX x' m'
    pq : (fst X.bS ≡ fst X'.bS) × (fst X.v ≡ fst X'.v)
    pq = pr-inj (sym (prʟ-fst X.bS X.v) ∙ q ∙ prʟ-fst X'.bS X'.v)
    qv : fst X.v ≡ fst X'.v
    qv = snd pq
    -- The table value at the same index is the same value.
    to : Σ[ k ∈ ⟨ fst X.bS ∈ δ ⟩ ] (fst X'.e ≡ fst (eS X.bS k))
    to = T-out X.bS X'.e (subst (λ w → ⟨ pr w (fst X'.e) ∈ fst T ⟩) (sym (fst pq))
                           (T-in X'.bS X'.b∈δ))
    qe : fst X'.e ≡ fst X.e
    qe = to .snd ∙ (λ i → fst (eS X.bS (snd (fst X.bS ∈ δ) (to .fst) X.b∈δ i)))

  injL : InjL (LsetS δ oδ) (prodL δL)
  injL = Inj.injL D inj

  -- The pairing at δ, as src/L/GCH/Sequences.lagda.md builds it.
  pairing : InjL (prodL δL) δL
  pairing = PT.rec squash₁ build (cardOf δL oδ)
    where
    build : Σ[ μ ∈ S ]
              ( IsOrd (fst μ) × IsCardinalL μ
              × ((z : V ℓ) → ⟨ z ∈ˢ fst μ ⟩ → ⟨ z ∈ˢ fst δL ⟩)
              × InjL δL μ × InjL μ δL )
          → InjL (prodL δL) δL
    build (μ , oμ , cardμ , _ , δ↪μ , μ↪δ) =
      injl-trans (prodL δL) (prodL μ) δL (prod-inj δL μ δ↪μ)
        (injl-trans (prodL μ) μ δL
          (WF.WFI.induction regularityV {P = Goal} Step.result (fst μ) (snd μ) oμ cardμ μ∉ω)
          μ↪δ)
      where
      μ∉ω : ⟨ fst μ ∈ˢ ω ⟩ → Empty.⊥
      μ∉ω h = no-fin δL μ oδ δ∉ω oμ h δ↪μ

  result : InjL (LsetS δ oδ) δL
  result = injl-trans (LsetS δ oδ) (prodL δL) δL injL pairing
```

<!-- section 5 prose, retired -->
SECTION 5.  THE THEOREM, BY ∈-INDUCTION, FROM THE BASE L_ω ↪ ω.

  At an infinite ordinal δ: if δ = β+1 then β is infinite and the
  successor step applies to the hypothesis at β; otherwise δ is a
  limit, every β ∈ δ has L_β ↪ δ (through the hypothesis at an
  infinite β, through L_ω ↪ ω at a finite one), and the limit step
  applies.  The base at ω is the one row this chapter takes as its
  hypothesis: the code set of the names sits in L_ω and in no finite
  stage, so the successor map of section 2 has no target below ω.

<!-- the ∈-induction -->
module Induction (base : LimitStageCounted) where

  P : V ℓ → Type (ℓ-suc ℓ)
  P δ = (oδ : IsOrd δ) → (⟨ δ ∈ ω ⟩ → Empty.⊥) → InjL (LsetS δ oδ) (ordL δ oδ)

  module Ind (δ : V ℓ) (ih : (β : V ℓ) → ⟨ β ∈ δ ⟩ → P β)
              (oδ : IsOrd δ) (δ∉ω : ⟨ δ ∈ ω ⟩ → Empty.⊥) where

    δL : S
    δL = ordL δ oδ

    -- Every stage below δ injects into δ.
    have : (β : V ℓ) (oβ : IsOrd β) → ⟨ β ∈ δ ⟩ → InjL (LsetS β oβ) δL
    have β oβ β∈δ = go (lem (β ∈ ω))
      where
      go : ⟨ β ∈ ω ⟩ ⊎ (⟨ β ∈ ω ⟩ → Empty.⊥) → InjL (LsetS β oβ) δL
      go (inl β∈ω) =
        injl-trans (LsetS β oβ) Lω δL
          (inclusion-coded (LsetS β oβ) Lω (λ z hz → Lset-mono {α = ω} {β = β} β∈ω hz))
          (injl-trans Lω ωʟ δL base
            (inclusion-coded ωʟ δL (λ z hz → ω⊆ δ oδ δ∉ω z hz)))
      go (inr β∉ω) =
        injl-trans (LsetS β oβ) (ordL β oβ) δL (ih β β∈δ oβ β∉ω)
          (inclusion-coded (ordL β oβ) δL (λ z hz → oδ .fst hz β∈δ))

    IsSuc : hProp (ℓ-suc ℓ)
    IsSuc = ∥ Σ[ β ∈ V ℓ ] (IsOrd β × (sucV β ≡ δ)) ∥₁ , squash₁

    atSuc : Σ[ β ∈ V ℓ ] (IsOrd β × (sucV β ≡ δ)) → InjL (LsetS δ oδ) δL
    atSuc (β , oβ , q) =
      move (LsetS (sucV β) (suc-ord oβ)) (LsetS δ oδ) (ordL (sucV β) (suc-ord oβ)) δL
        (cong Lset q) q
        (succ-step (ordL β oβ) oβ β∉ω (ih β β∈δ oβ β∉ω))
      where
      β∈δ : ⟨ β ∈ δ ⟩
      β∈δ = subst (λ w → ⟨ β ∈ w ⟩) q (self∈sucV β)
      β∉ω : ⟨ β ∈ ω ⟩ → Empty.⊥
      β∉ω h = δ∉ω (subst (λ w → ⟨ w ∈ ω ⟩) q (ω-limit β h))

    atLim : (IsSuc .fst → Empty.⊥) → InjL (LsetS δ oδ) δL
    atLim ¬suc = Lim.result δL oδ δ∉ω lim have
      where
      lim : (β : V ℓ) → ⟨ β ∈ δ ⟩ → ⟨ sucV β ∈ δ ⟩
      lim β β∈δ = go (suc∈or≡ β δ oβ oδ β∈δ)
        where
        oβ : IsOrd β
        oβ = mem-ord {A = δ} oδ β β∈δ
        go : ⟨ sucV β ∈ δ ⟩ ⊎ (sucV β ≡ δ) → ⟨ sucV β ∈ δ ⟩
        go (inl h) = h
        go (inr q) = Empty.rec (¬suc ∣ β , oβ , q ∣₁)

    result : InjL (LsetS δ oδ) δL
    result = go (lem IsSuc)
      where
      go : IsSuc .fst ⊎ (IsSuc .fst → Empty.⊥) → InjL (LsetS δ oδ) δL
      go (inl h)  = PT.rec squash₁ atSuc h
      go (inr ¬h) = atLim ¬h

  counted : (δ : V ℓ) → P δ
  counted = WF.WFI.induction regularityV {P = P} Ind.result

<!-- the theorem from the base -->
THE THEOREM, from the base.

```agda
stage-counted-from : LimitStageCounted → StageCountedCoded
stage-counted-from base δ Lδ oδ δ∉ω q =
  move (LsetS (fst δ) oδ) Lδ (ordL (fst δ) oδ) δ (sym q) refl
    (Induction.counted base (fst δ) oδ δ∉ω)

<!-- the export -->
stage-counted : StageCountedCoded
stage-counted = stage-counted-from limit-stage-counted


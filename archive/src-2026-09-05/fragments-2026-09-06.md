# Fragments removed 2026-09-06 (E2)

## src/L/InjChain.lagda.md 122-126 (noinj²ω), 170-186 (Coreω/open Coreω/pairω/pairω-inj/squareω)
-- zero tree-wide consumers; finite-excl-ω kept (StageCount:65, Pairing:57)

    -- The vacuous infinite-member clause, in the square form.
    noinj²ω : (β : V ℓ) → IsOrd β → ⟨ β ∈ ω ⟩ → ⟨ ω ∈ β ⟩
            → (f : ⟪ ω ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
            → ((m n : ⟪ ω ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥
    noinj²ω β oβ β∈ω ω∈β f finj = ω∉β β β∈ω ω∈β
    -- The base at ω: `InitialCore` instantiated, then the direct pairing.
    module Coreω = InitialCore ω ω-ord ω-limit noinj²ω finite-excl-ω
    
    open Coreω using ( colA; col∈α )
    
    pairω : ⟪ ω ⟫ × ⟪ ω ⟫ → ⟪ ω ⟫
    pairω p = fiber ω {x = colA p} (col∈α p) .fst
    
    pairω-inj : (p q : ⟪ ω ⟫ × ⟪ ω ⟫) → pairω p ≡ pairω q → p ≡ q
    pairω-inj p q e = SQ.col-inj ω ω-ord {p = p} {q = q}
      (sym (fiber ω {x = colA p} (col∈α p) .snd)
       ∙ cong (⟪ ω ⟫↪) e
       ∙ fiber ω {x = colA q} (col∈α q) .snd)
    
    squareω : sq ω
    squareω = pairω , pairω-inj
    

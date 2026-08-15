#!/usr/bin/env python3
"""LJ-1.331: build the HALF-record arm, which bisects the twelve ties.

Arms B and D put all twelve tie hypotheses of `ForallAgree` into a record and
both exhausted 8 GB. This arm puts only the FIRST SIX into the record and
leaves the last six in the telescope. The first six state memberships and
equalities. The last six state satisfaction of a built formula, which is the
shape `dev/LESSONS.md` P-l and R-40 both name as the expensive one.

So the arm separates two candidates for the wall:
  green and fast  -> the six formula-valued ties carry it
  a wall again    -> the record indirection carries it, whatever the field is

Run it from the repository root.
"""

from pathlib import Path

ROOT = Path("/Users/alsg/Agentic/Bedrock/agents/tasks/LJ-1-331")

FIRST, LAST = 3849, 3890  # `module ForallAgree` line to its `where` line, in CondA.

NEW = r'''-- [LJ-1.331] ARM E, the bisection.  SIX of the twelve ties are a record
-- and the other six stay in the telescope.  The six in the record state
-- memberships and equalities.  The six left out state satisfaction of a
-- built formula, which is the shape P-l and R-40 name as expensive.
module ForallTiesNS where
  record ForallTies6 {m : ℕ} (C T B N K : Fin m) (γ : S ^ m) : Type (ℓ-suc ℓ) where
    field
      tagEq : fst (lookup N γ) ≡ fst (numeralL 9)
      numK : ⟨ fst (numeralL 9) ∈ fst (lookup K γ) ⟩
      innerK : (a : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
             → ⟨ fst (prʟ (numeralL 9) a) ∈ fst (lookup K γ) ⟩
      arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
             → ⟨ fst N ∈ fst (lookup K γ) ⟩
             → ⟨ fst v ∈ fst (lookup K γ) ⟩
      codesK : (c ar a : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
             → fst c ≡ pr (fst ar) (pr (# 9) (fst a))
             → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
               × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
      valK : (c ar a yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 9) (fst a))
           → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
           → ⟨ fst yc ∈ fst (lookup K γ) ⟩

module ForallAgree {m : ℕ} (C T B N K : Fin m) (γ : S ^ m)
  (ties : ForallTiesNS.ForallTies6 C T B N K γ)
  (succK : (E ya yc a ar c : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
          → succU {m} C T B N K γ E ya yc a ar c)
  (keyK : (E ya yc a ar c : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
          → ⟨ fst a ∈ fst (lookup K γ) ⟩
          → keyU {m} C T B N K γ E ya yc a ar c)
  (subK : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
             subValSuccAt (suc (suc (suc (suc (suc (suc T))))))
                          (suc (suc (suc (suc zero))))
                          (suc (suc (suc zero)))
                          (suc zero) ⟩ → ⟨ fst ya ∈ fst (lookup K γ) ⟩)
  (envK : (ya yc a ar c E : S) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
         → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B)))))) ⟩
         → ⟨ fst E ∈ fst (lookup K γ) ⟩)
  (envInK : (ya yc a ar c E : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
           → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → (z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
           → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  (consK : (ya yc a ar c E z x e' : S) → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
               consAtL zero (suc zero) (suc (suc zero)) ⟩
          → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                            (x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  where
  open ForallTiesNS.ForallTies6 ties
'''


def main() -> None:
    lines = (ROOT / "CondA.lagda.md").read_text(encoding="utf-8").splitlines(True)
    assert lines[FIRST - 1].startswith("module ForallAgree "), lines[FIRST - 1]
    assert lines[LAST - 1].rstrip() == "  where", lines[LAST - 1]
    out = lines[: FIRST - 1] + [NEW] + lines[LAST:]
    out[9] = out[9].replace("LJ-1-331.CondA", "LJ-1-331.CondE")
    (ROOT / "CondE.lagda.md").write_text("".join(out), encoding="utf-8")
    print("wrote CondE.lagda.md")


if __name__ == "__main__":
    main()

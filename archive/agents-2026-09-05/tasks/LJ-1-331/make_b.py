#!/usr/bin/env python3
"""LJ-1.331: build the record arm from the control arm.

The control arm `CondA.lagda.md` is `src/L/Condensation.lagda.md` lines 1 to
3958, verbatim, with the module name changed and the code fence closed. This
script makes `CondB.lagda.md` from it with exactly ONE change: the twelve tie
hypotheses of `ForallAgree` become the fields of a record, and the row module
takes one parameter instead of twelve. Every other byte is the same, and the
body of the row module is untouched, because `open ForallTiesNS.ForallTies
ties` puts the same twelve names back in scope.

Run it from the repository root. It rewrites `CondB.lagda.md` each time.
"""

from pathlib import Path

ROOT = Path("/Users/alsg/Agentic/Bedrock/agents/tasks/LJ-1-331")

# The telescope of `ForallAgree`, header line to `where` line, in CondA.
FIRST, LAST = 3849, 3890

NEW = r'''-- [LJ-1.331] THE ONE CHANGE OF THIS PROBE.  The twelve tie hypotheses of
-- the Forall row are stated once as a record, in the style of the file's
-- own `KFacts` block, and the row module takes ONE parameter in place of
-- twelve.  The body of the row module below is unchanged.
module ForallTiesNS where
  record ForallTies {m : ℕ} (C T B N K : Fin m) (γ : S ^ m) : Type (ℓ-suc ℓ) where
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
      succK : (E ya yc a ar c : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
            → succU {m} C T B N K γ E ya yc a ar c
      keyK : (E ya yc a ar c : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
           → ⟨ fst a ∈ fst (lookup K γ) ⟩
           → keyU {m} C T B N K γ E ya yc a ar c
      subK : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
               subValSuccAt (suc (suc (suc (suc (suc (suc T))))))
                            (suc (suc (suc (suc zero))))
                            (suc (suc (suc zero)))
                            (suc zero) ⟩ → ⟨ fst ya ∈ fst (lookup K γ) ⟩
      envK : (ya yc a ar c E : S) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envSetAt zero (suc (suc (suc (suc zero))))
                         (suc (suc (suc (suc (suc (suc B)))))) ⟩
           → ⟨ fst E ∈ fst (lookup K γ) ⟩
      envInK : (ya yc a ar c E : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
             → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
             → (z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
                 envOverAt zero (suc (suc (suc (suc (suc zero)))))
                            (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
             → ⟨ fst z ∈ fst (lookup K γ) ⟩
      consK : (ya yc a ar c E z x e' : S) → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
                 consAtL zero (suc zero) (suc (suc zero)) ⟩
            → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                              (x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩

module ForallAgree {m : ℕ} (C T B N K : Fin m) (γ : S ^ m)
  (ties : ForallTiesNS.ForallTies C T B N K γ)
  where
  open ForallTiesNS.ForallTies ties
'''


def main() -> None:
    lines = (ROOT / "CondA.lagda.md").read_text(encoding="utf-8").splitlines(True)
    head = lines[0].replace("CondA", "CondB")
    assert lines[FIRST - 1].startswith("module ForallAgree "), lines[FIRST - 1]
    assert lines[LAST - 1].rstrip() == "  where", lines[LAST - 1]
    out = lines[: FIRST - 1] + [NEW] + lines[LAST:]
    out[9] = out[9].replace("LJ-1-331.CondA", "LJ-1-331.CondB")
    (ROOT / "CondB.lagda.md").write_text("".join(out), encoding="utf-8")
    print("wrote CondB.lagda.md", len("".join(out).splitlines()), "lines", head.strip()[:0])


if __name__ == "__main__":
    main()

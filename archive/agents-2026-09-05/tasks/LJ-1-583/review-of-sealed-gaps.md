# [LJ-1.583] review of the sealed gaps: ONE OF THREE DOES NOT CLOSE

## WHAT THIS FILE IS

The task's obligation is delivered and green
(`agents/tasks/LJ-1-583/Probe583.agda:296-310`, meter `0 UNRESOLVED of 1` at
`agents/tasks/LJ-1-583/runs/witness-1.out`). **This file is not a stop on the
task.** It is the NO-GO on ONE of the three named gaps, written separately
because the brief put it in scope and because a critic must be able to read it
without reading the whole report.

**GAP B DOES NOT CLOSE.** Gaps A and C do.

## THE NO-GO, IN ONE PARAGRAPH

`CodeBounded` (`agents/tasks/LJ-1-576/Probe576.agda:239-240`) asks for
`(a b : S) → InjL a b → CodeSelect.BoundedCode a b`. **THAT TARGET IS THE WRONG
ONE AND I DID NOT ATTEMPT TO INHABIT IT.** `CodeSelect a b` opens `SiteBound a`
(`Probe576.agda:203`), so its stage β is a function of `a` ALONE. A code of an
injection `a ↪ b` is a set of pairs drawn from `a` and `b`, so its stage reads
`b`. The two are different ordinals and nothing in the tree makes them one.

## THE EVIDENCE, EACH AT `file:line`

**β IS A FUNCTION OF `a` ALONE.**

- `src/L/Cardinal.lagda.md:165-166`: `SiteBound.β = stageBound (fst a) (snd a) .fst`.
- `src/L/Choice/Stage.lagda.md:366-368`:
  `stageBound a p = bound2 ω (stage a p) ω-ord (stage-ord a p)`.
- `src/L/Ordinal.lagda.md:185-186`:
  `bound2 σ₁ σ₂ o₁ o₂ : Σ[ β ∈ S ] (IsOrd β × ⟨ σ₁ ∈ˢ β ⟩ × ⟨ σ₂ ∈ˢ β ⟩)`.
  It says β is ABOVE its two arguments and says nothing else.

**THE CODE'S BOUND READS `b`.**

- `src/L/InjChain.lagda.md:279`: `PairBound D C` indexes on
  `Ix = ⟪ fst D ⟫ × ⟪ fst C ⟫`.
- `src/L/InjChain.lagda.md:293`: that index type is what goes to `StageBound`.

**SO THE BOUND `CodeSelect` OFFERS AND THE BOUND THE CODE NEEDS ARE NOT THE SAME
ORDINAL.**

## IT DOES NOT WANT THE AMBIENT `Inj` BACK

The brief reads: "IF A GAP NEEDS THE AMBIENT `Inj` BACK, SAY SO AND STOP. That
would mean the coded restatement does not reach that projection, and the
mathematician must know which one."

**NO GAP NEEDS IT, AND I CHECKED EACH RATHER THAN ASSUMING.** Projection 4 wants
a STAGE BOUND ON THE CODE. No predicate anywhere in
`agents/tasks/LJ-1-583/Probe583.agda` reintroduces
`⟪ fst α ⟫ ↪ ⟪ fst γ ⟫`, and projection 5 still refutes only a CODED injection
(`Probe583.agda:148-152`). **The coded restatement reaches all five projections.
One of them keeps a hypothesis.**

## WHAT IS PROVED IN PLACE OF THE DISCHARGE

**THE SELECTION NEVER NEEDED `SiteBound`.** `module CodeSelectAt (β : V ℓ)
(oβ : IsOrd β) (a b : S)` (`Probe583.agda:235-256`) is `[LJ-1.576]`'s section 3
with β as a PARAMETER, and it is green. So the gap narrows from "a code at the β
that `SiteBound a` names" to "a β, computed from `a` AND `b`, holding a code":

    StageOfCode : (a b : S) → InjL a b
                → Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
                    CodeSelectAt.BoundedCodeAt β oβ a b     Probe583.agda:259-262

**NOT INHABITED.**

**AND THE GAP IS THE TRUNCATION BOUNDARY AND NOT EXISTENCE, WHICH IS MEASURED
AND NOT ARGUED.** The truncated form IS inhabited, with nothing assumed:

    stage-of-code-truncated : ... → ∥ Σ[ β ] Σ[ oβ ] BoundedCodeAt β oβ a b ∥₁
                                                            Probe583.agda:269-280

green, from `stage`, `stage-ord` and `stage-mem` (`src/L/Stage.lagda.md:185-188`).
Every code always has a stage. The Σ is not a proposition, so the stage cannot
leave the truncation, and `leastOf` needs it OUTSIDE.
`dev/literature/truncation-and-selection.md:148` reads
"index is a proposition. **A data payload does not come out.**"

**NO CHOICE PRINCIPLE WOULD PAY IT EITHER**, which matters because the brief
forbids reaching for one. `dev/literature/truncation-and-selection.md:229` reads
"So AC delivers `∥ f ∥₁` for a selection function `f`, never `f`. **If the goal"
and the sentence completes "that consumes `f` is not a proposition, AC does not
help." **I reached for none, added no axiom, and postulated nothing.**

## WHAT THE MATHEMATICIAN MUST DECIDE

1. **`StageOfCode` is the real obligation and `CodeBounded` should be retired as
   a target.** A brief that re-asks `CodeBounded` asks for a false statement's
   proof.
2. **A brief about `StageOfCode` must say which side of the truncation it
   wants.** The truncated side is already free (`Probe583.agda:269-280`), so a
   brief that asks for it asks for nothing.
3. **The archive records a rival door at this wall and I did not take it.**
   `archive/dev/LJ-dispatch-index.md:373` and `:376` name `rec→Set` rather than
   `PT.rec`. Its criterion is a weakly constant map
   (`dev/literature/truncation-and-selection.md:158`), and two different codes
   read back as two different injections, so `readL` is not weakly constant.
   **That is my reason for staying on the coded route, not a ruling.**

## WHAT IS NOT IN THIS FILE

**NO ROW IS PAID AND `SqCollectAt` IS NOT ATTEMPTED.** The brief forbids it. Gap
A and gap C are closed and their evidence is in
`agents/tasks/LJ-1-583/lj-1.583-report.md`, not here. Nothing under `src/` is
touched. No commit, no push.

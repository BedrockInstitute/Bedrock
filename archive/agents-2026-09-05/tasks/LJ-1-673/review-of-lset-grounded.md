# review-of-lset-grounded: a STATED NO-GO, with the hull formula written

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.673
obligation: agents/tasks/LJ-1-673/Probe673.agda::lset-grounded
verdict: **NO-GO on the closed term.** `lset-grounded` of type
`LsetGrounded` at `[LJ-1.667]`'s `matrix₃` is not inhabited. The
witness meter reads `1 UNRESOLVED of 1, 3.03 s, probe_red=False`
(`agents/tasks/LJ-1-673/runs/meter-obligation.out:2`). The probe is
green and carries no hole (`runs/recheck-3.out`, `TIME_EXIT=0`).
Nine other delivered names meter `0 UNRESOLVED of 9`
(`runs/meter-names.out`, last line).

**THIS IS NOT A REFUTATION OF `LsetGrounded`.** I did not build a
term of its negation. Devlin 5.2 (b) still has the stage reading
`L_α ⊨ ∃z φ` (`dev/literature/devlin-II5.md:98-99`). What is
measured is that the tree cannot fire `hull-closed` at `matrix₃`
today without a completeness fact the tree does not supply.

The critic reads this file. It does not close the task.

---

## 1. WHAT THE SEARCH TRIED

1. **The Formula Code 1 is not a second matrix.** `inBound`
   (`Probe673.agda:83-87`) is `matrix₃` mapped onto `Code` by a dummy
   slide (`count-matrix₃ = refl`, `:54-55`) and pinned at the value
   slot and the parameter slot by `≐ con`, the `inF` pattern
   (`Probe651.agda:149-150`). CloseSyntax.close cannot close at
   `Code` (`agents/tasks/LJ-1-664/runs/close-1.out:5-7`).
2. **The consumer of hull-closed is four lines.**
   `At.bound-from-stage` (`Probe673.agda:100-104`) is
   `hull-closed` at `inBound`. Meter: `0 UNRESOLVED of 9` including
   this name (`runs/meter-names.out:5`). Nothing of that search is
   rewritten (W2).
3. **Completeness is unpaid.** `BoundInStage` (`:93-95`) is the
   hypothesis `hull-closed` takes (`src/L/Hull.lagda.md:415`).
   `Completeness` (`:126-130`) is that hypothesis at hull codes of
   `Lset δ` and `δ`. Neither is inhabited. The reverse of the three
   soundness bridges `[LJ-1.667]` named
   (`agents/tasks/LJ-1-667/lj-1.667-report.md:136-148`) sits under
   this name: `SameAsGraph`, EraseTransfer, and the bound as a
   member of `Lset lam`.
4. **Convert is unpaid plumbing.** `Convert` (`:115-119`) is AbsL
   satisfaction of `inBound` to the ambient reading of `matrix₃`.
   The path is unpack of two `∃̇` and two `≐`, then
   `Frame652.AtTrans.read` at `Δ₀-matrix₃` (`Probe652.agda:114-124`).
   A term that substituted along that ambient reading was started
   as `grounded-from-complete`. `runs/p-4.out` still reads Checking
   and has no `ended` line. The next run starts at
   `runs/p-5.out:2`. That term is not in the delivered file.

The floor of the exact obligation is `runs/FLOOR.agda.txt`: exit 42
at the one designed hole (`runs/floor-1.out:9-12`), 20.20 s, peak
1,684,946,944 bytes.

## 2. D-10, THE TYPE HAS NO IsOrd

`matrix₃` contains `isOrd-at-p` (`Probe667.agda:72-73`). A witness
`z` with `⟨ (Lset δ ∷ δ ∷ z ∷ []) ⊨ₚ matrix₃ ⟩` therefore needs
the parameter to be an ordinal in the object language.
`LsetGrounded` (`Probe652.agda:260-264`) has no `IsOrd`.
Completeness at a non-ordinal hull member is false of this matrix.
The corrected target beside the original is `LsetGrounded` at
`matrix₃` given `Completeness` and `Convert`, with `IsOrd δ` on the
completeness supplier. `bound-from-stage` is the hull-membership
half of that target.

## 3. TWO UNPAID SUPPLIERS, AND EITHER ONE STOPS THE CLOSED TERM

**Supplier 1. `Completeness`.** `BoundInStage` at the codes of
`Lset δ` and `δ`. This is Devlin 5.2 (b) at `matrix₃`. The tree has
`Lset-defines` for `LsetGraphAt` at the class carrier
(`src/L/Condensation.lagda.md:427-430`). It does not have
`SameAsGraph` (`Probe520.agda:192-195`). It does not put the graph
witness in `Lset lam`.

**Supplier 2. `Convert`.** AbsL satisfaction of `inBound` to
`⟨ (Lset δ ∷ δ ∷ z ∷ []) ⊨ₚ matrix₃ ⟩`. The lemma `AtTrans.read`
is green. The substitution along the ambient reading of this
matrix is the checker `runs/p-4.out` did not finish.

Either supplier unpaid is enough. Both are unpaid.

## 4. WHAT THE NEXT BRIEF SHOULD FUND

1. **`Completeness` / `BoundInStage` at `matrix₃`.** That is
   Devlin 5.2 (b), not a second formula. It needs `SameAsGraph` at
   `[LJ-1.520]`'s Matrix, both directions, and the bound as a
   member of `Lset lam`. Carry `IsOrd` on the parameter.
2. **`Convert`, as a generic unpack at a 3-slot Δ₀ formula**, not
   as a substitution into this matrix's ambient reading. That
   substitution is the checker that `runs/p-4.out` did not finish.
3. **Do not re-dispatch the Formula Code 1.** `inBound` and
   `count-matrix₃` are green. `bound-from-stage` is green.
4. **Do not re-dispatch the syntax of the 3-slot matrix.**
   `matrix₃` and `Δ₀-matrix₃` are green (`Probe667.agda:72-76`).
5. **Do not fund `Matrix₂`.** D-10 in `[LJ-1.665]`
   (`lj-1.665-report.md:35-39`) still stands.

This file is the critic's input and it does not close the task.

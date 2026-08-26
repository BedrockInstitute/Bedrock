# review-of-bound-in-stage: a STATED NO-GO, with the bound's escape measured

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.679
obligation: agents/tasks/LJ-1-679/Probe679.agda::bound-in-stage
verdict: **NO-GO on the closed term.** `bound-in-stage` of type
`Completeness` at `[LJ-1.667]`'s `matrix₃`, with `SameAsGraph` a
hypothesis in both directions and `IsOrd` on the parameter, is not
inhabited. The witness meter reads
`1 UNRESOLVED of 1, 3.26 s, probe_red=False`
(`agents/tasks/LJ-1-679/runs/meter-obligation.out:2`). The probe is
green and carries no hole (`runs/recheck-3.out`, `EXIT=0`). Nine
other delivered names meter `0 UNRESOLVED of 9`
(`runs/meter-names.out`, last line). W3 meters
`0 UNRESOLVED of 2` (`runs/meter-w3.out`, last line).

**THIS IS NOT A REFUTATION OF `BoundInStage`.** I did not build a
term of its negation. Devlin 5.2 (b) still has the stage reading
`L_α ⊨ ∃z φ` (`dev/literature/devlin-II5.md:98-99`). What is
measured is that `SameAsGraph` at the class carrier does not put a
witness in `Lset lam`, and that the tree's one `KFacts` value is
`Lset lam` itself, which is not a member of `Lset lam`.

The critic reads this file. It does not close the task.

---

## 1. WHAT THE SEARCH TRIED

1. **`Completeness` now carries `IsOrd`.** `At.Completeness`
   (`Probe679.agda:73-78`) is `[LJ-1.673]`'s type
   (`Probe673.agda:126-130`) with `IsOrd (fst (val cp))` on the
   parameter, as the critic of `[LJ-1.673]` asked
   (`review-of-LJ-1-673-1.md:157-160`). Meter:
   `0 UNRESOLVED of 9` including this name
   (`runs/meter-names.out:4`). It is a TYPE. It is not inhabited.
2. **`SameAsGraph` is a hypothesis, not a term.** `SameHyp`
   (`Probe679.agda:48-49`) is both directions at every environment,
   the type `[LJ-1.520]` named (`Probe520.agda:192-195`). The brief
   forbids building it. `[LJ-1.672]` already closed NO-GO on the
   closed term (`lj-1.672-report.md:8-11`).
3. **W3, the bound's membership.** `kvalue-escapes`
   (`runs/W3.agda:36-37`) is `∈-irrefl` at `Lset lam`. The tree's
   one `KFacts` value is `K = Lset λ`
   (`src/L/Condensation.lagda.md:7369-7373`). That value is not a
   member of the stage. `Tags.tags-in-stage` (`runs/W3.agda:46-47`)
   is `Bound.num∈λ`. The twelve numerals ARE members of the stage.
   W2: that lemma is not rewritten. Meter: `0 UNRESOLVED of 2`
   (`runs/meter-w3.out:3`).
4. **`HierInStage` is the remaining supplier.**
   (`Probe679.agda:84-88`). `hierL` is the witness `Lset-defines`
   spends (`src/L/Hierarchy.lagda.md:656`). `BoundInStage`'s `∃̇`
   ranges over `SL` (`src/FOL/Semantics.lagda.md:100`). Re-measured
   at this stage. Not transferred from `[LJ-1.494]`. Named, not
   inhabited.
5. **`CompletenessFrom` is the corrected target.**
   (`Probe679.agda:94-95`): `SameHyp → HierInStage → Completeness`.
   Named as a type. Not inhabited. Either supplier unpaid stops
   `bound-in-stage`. The brief gives only `SameAsGraph`. That is not
   enough.

The floor of the exact obligation is `runs/FLOOR.agda.txt`: one
error, the designed hole at `FLOOR.agda:63.20-24`
(`runs/floor-3.out:4-6`), 5.66 s, peak 959,021,056 bytes. **The
obligation TYPE is well-formed.**

## 2. D-10, THE CLASS CARRIER IS NOT THE STAGE

`SameAsGraph` (`Probe520.agda:192-195`) is satisfaction at `𝒮ʟ`.
`BoundInStage` (`Probe673.agda:93-95`) is `AbsL.⊨ᵐ` of an unbounded
`∃̇` at the hull stage. The two worlds do not meet at a witness.
`Lset-defines` (`src/L/Condensation.lagda.md:427-430`) writes the
graph at the class carrier. It does not place `hierL` in `Lset lam`.

The corrected target beside the original, as D-10 asks:
`CompletenessFrom` (`Probe679.agda:94-95`).

## 3. TWO UNPAID SUPPLIERS, AND EITHER ONE STOPS THE CLOSED TERM

**Supplier 1. `SameAsGraph`.** Taken as a hypothesis. Not inhabited.
The type lives at `𝒮ʟ`. It does not mention `Lset lam`.

**Supplier 2. `HierInStage`.** A bound that is a member of
`Lset lam`. The tree's `KFacts` supply is not that member
(`kvalue-escapes`). `hierL` has no delivered stage bound.

Either supplier unpaid is enough. Both are unpaid. The Formula
Code 1 `inBound` is already paid (`Probe673.agda:83-87`). That is
the difference from `[LJ-1.664]`: `𝒟ₒ` had no Formula Code 1; the
bound has `inBound`, and the witness escapes the stage.

## 4. WHAT THE NEXT BRIEF SHOULD FUND

1. **`HierInStage` at this frame**, or an adequate `K` that is a
   member of `Lset lam` and contains the approximation. Do not use
   `KValue`'s `K = Lset λ` as that member. `kvalue-escapes` is green.
2. **Then `CompletenessFrom`**, `SameHyp` and `HierInStage` to
   `Completeness`. Do not fund `bound-in-stage` from `SameAsGraph`
   alone.
3. **Do not re-dispatch `inBound`, `count-matrix₃`, or
   `bound-from-stage`.** They are green in `[LJ-1.673]`.
4. **Do not re-dispatch the syntax of `matrix₃`.** Green in
   `[LJ-1.667]`.
5. **Do not re-dispatch pins at the numerals.** Green in
   `[LJ-1.672]`. `tags-in-stage` is `num∈λ`.
6. **Do not fund `Matrix₂`.** D-10 in `[LJ-1.665]` still stands.

This file is the critic's input and it does not close the task.

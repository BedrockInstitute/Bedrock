# review-of-witnessed-lset: a STATED NO-GO, with the witness slot written as syntax

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.667
obligation: agents/tasks/LJ-1-667/Probe667.agda::witnessed-lset
verdict: **NO-GO on the obligation. The syntax of the witness slot
is written, green and metered. The ambient reading of that syntax
does not give soundness, and it does not give a hull member.**

The obligation term is NOT written. The witness meter reads
`1 UNRESOLVED of 1, 3.36 s, probe_red=False`
(`agents/tasks/LJ-1-667/runs/meter-obligation.out:2`). The probe is
green and carries no hole (`runs/p-final-3.out`, `EXIT=0`). Eleven
other delivered names meter `0 UNRESOLVED of 11`
(`runs/meter-names.out`, last line).

**THIS IS NOT A REFUTATION OF `Witnessed Lset`.** I did not build a
term of its negation. The literature still has a Σ₀ formula with a
witness slot (`dev/literature/devlin-II5.md:95-96`). What is measured
is that the ambient V reading of the 3-slot matrix the tree can write
today does not reach `Lset-only`, and that `LsetGrounded` still asks
for a bound inside the hull.

---

## 1. WHAT THE WITNESS SLOT IS

`[LJ-1.520]`'s `Matrix` (`Probe520.agda:53-128`) is the bounded graph
with `transK` and `pins`. W3 instantiates it at fifteen slots and
binds the twelve tag slots by `∃̇∈` over the witness
(`runs/W3.agda:56-76`). Erase then sends the result to `⊥*`
(`:88-92`). `count-three = refl` (`:83-84`) says there is no constant.

`matrix₃` (`Probe667.agda:72-73`) is that erased matrix, conjoined
with ordinality of the parameter at slot 1 (`isOrd-at-p`, `:59-65`).
Slot order is Witnessed's: value, parameter, witness
(`Probe652.agda:87-91`). Δ₀ is delivered (`Δ₀-matrix₃`, `:75-76`).

That is Devlin 5.2 (a)'s Φ, at the consumer's order, as syntax.

## 2. WHAT THE AMBIENT READING DOES NOT GIVE

Witnessed's soundness (`Probe652.agda:90`) is

    (a p z : S) → ⟨ (a ∷ p ∷ z ∷ []) ⊨ₚ φ ⟩ → a ≡ Lset p

`Lset-only` (`src/L/Hierarchy.lagda.md:334-335`) gives that conclusion
from `LsetGraphAt` at 𝒮ʟ, with `IsOrd` on the parameter. Three
bridges sit between `matrix₃` and that lemma.

1. **Carrier.** `EraseTransfer` (`src/L/Condensation.lagda.md:287-305`)
   moves a Δ₀ reading UP from 𝒮ʟ to V, at a constructible environment.
   Witnessed quantifies over arbitrary `S`. The transfer does not move
   V down, and it does not apply when `a`, `p`, `z` fail `isL`.
2. **Bounded to unbounded.** `[LJ-1.520]` named `SameAsGraph`
   (`Probe520.agda:192-195`) and did not inhabit it. No module
   `GraphAgree` exists under `src/`. The leaf chain that would feed it
   is commented as unplaced (`src/L/Condensation.lagda.md:5477-5480`).
3. **`IsOrd`.** Witnessed's soundness has none. `isOrd-at-p` is in the
   formula so that, if the two bridges above close,
   `Amb.isOrdAt-out` plus `Lset-only` fire. It is not the conversion.

## 3. `LsetGrounded`, AND ELEMENTARITY

The consumer `commute-from-witnessed` (`Probe652.agda:266-268`) is
green. `LsetGrounded` (`:260-264`) still asks for a hull member `z`
such that the ambient formula holds of `(Lset δ, δ, z)`. For
`matrix₃` that `z` is a bound containing the twelve numerals and the
approximation table. Putting that bound in the hull is a hull-closure
fact. The ambient reading does not produce it.

Premise 4 of the brief: take `elem` from
`src/L/BoundedSubset.lagda.md:759` and report if it does not reach.
It does not reach `Frame652`. `elem` lives in `WithCode`
(`:681-682`, `:759`). `ElemReach.CodePair` (`Probe667.agda:139-142`)
is the pair that module asks for, restated at this frame, not
inhabited. `[LJ-1.655]` closed `elem-at-collapse-free` at the
chapter telescope (`Probe655.agda:300`), which carries κ, a cardinal,
a square and absorbs. That telescope is not `Frame652`'s.

## 4. WHAT THE NEXT BRIEF SHOULD FUND

1. **`SameAsGraph` / GraphAgree**, at `[LJ-1.520]`'s Matrix, both
   directions. Without it, `matrix₃` cannot spend `Lset-only`.
2. **The hull-membership of the bound**, which is `LsetGrounded` at
   `matrix₃`, not a second formula.
3. **The code pair at `Frame652`**, if clause (iii) is to spend
   `elem` from `:759` at this telescope rather than at the chapter's.
4. **Do not fund `Matrix₂`.** D-10 stands
   (`agents/tasks/LJ-1-665/lj-1.665-report.md:35-39`).
5. **Do not re-dispatch the syntax of the 3-slot matrix.** `matrix₃`
   and `Δ₀-matrix₃` are green.

This file is the critic's input and it does not close the task.

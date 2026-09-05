# review-of-hier-in-stage: a STATED NO-GO, with the limit assembly measured

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.697
obligation: agents/tasks/LJ-1-697/Probe697.agda::hier-in-stage
verdict: **NO-GO on the closed term.** `hier-in-stage` of type
`HierInStage` at `[LJ-1.679]`'s frame is not inhabited. The witness
meter reads `1 UNRESOLVED of 1, 3.04 s, probe_red=False`
(`agents/tasks/LJ-1-697/runs/meter-obligation.out:4`). The probe is
green and carries no hole (`runs/recheck-3.out`, `EXIT=0`). Ten other
delivered names meter `0 UNRESOLVED of 10`
(`runs/meter-names.out`, last line). W3 meters `0 UNRESOLVED of 4`
(`runs/meter-w3.out`, last line).

**THIS IS NOT A REFUTATION OF `HierInStage`.** I did not build a term
of its negation. Devlin 2.6(ii) still has the sequence
`(L_δ | δ ≤ γ) ∈ L_α` for `γ < α` at a limit
(`dev/literature/devlin-II5.md:221-222`). What is measured is that
`Lset-out`, `Lset-mono` and `succλ` assemble `HierBelow → HierInStage`
and do not place the table.

The critic reads this file. It does not close the task.

---

## 1. WHAT THE SEARCH TRIED

1. **`HierInStage` is taken, not copied.** `At.HierInStage`
   (`Probe697.agda:63-64`) is `[LJ-1.679]`'s type
   (`Probe679.agda:84-88`). Meter: `0 UNRESOLVED of 10` including this
   name (`runs/meter-names.out`). It is a TYPE. It is not inhabited.
2. **W3, three membership facts.** `Lset∈suc` (`runs/W3.agda:42-44`)
   is `𝒟ₒ-intro` at `⊤̇` and `Lset-suc`. `ordinal-in` (`:60-62`) is
   `ord∈Lset→∈`. `lset-in-stage` (`:67-73`) puts `Lset δ` in
   `Lset lam`. Meter: `0 UNRESOLVED of 4` (`runs/meter-w3.out`).
3. **`from-below` is the assembly this frame adds.**
   (`Probe697.agda:81-86`): `Below → HierInStage`, by `ordinal-in`,
   `climb 3` and `Lset-mono`. Pointwise as `from-below-at` (`:88-95`).
   Green. It CONSUMES `Below`. It does not construct it.
4. **`Below` is `[LJ-1.536]`'s `HierBelow` at this `isL` witness.**
   (`Probe697.agda:72-74`; `Probe536.agda:186-187`). Named, not
   inhabited. The door of `𝒟ₒ-intro` still wants a `Δ₀` formula
   (`agents/tasks/LJ-1-536/review-of-StageHigh.md:23-32`).
5. **`lset-in-stage` is not the missing input.** It places `Lset δ`,
   not `hierL δ`. `CompletenessFrom` (`Probe679.agda:94-95`) asks for
   `HierInStage`. A stage that is a member of a later stage is not
   the internal table.

The floor of the exact obligation is `runs/FLOOR.agda.txt`: one
error, the designed hole at `FLOOR.agda:49.19-23`
(`runs/floor-1.out:12-14`), 144.56 s, peak 1,754,939,392 bytes.
**The obligation TYPE is well-formed.**

## 2. D-10, THE LIMIT FRAME ASSEMBLES A REDUCTION, NOT THE TABLE

`Lset-out` (`src/L/Constructible.lagda.md:346-348`) on an ordinal is
weaker than `ord∈Lset→∈` (`src/L/Ordinal/Stages.lagda.md:265-268`).
I used the specialised lemma. `succλ` iterated three times
(`runs/W3.agda:55-57`) puts `δ+3` in `lam`. `Lset-mono`
(`src/L/Constructible.lagda.md:365-366`) then carries a table that
already sits in `Lset (δ+3)` up into `Lset lam`. That is
`from-below`. It does not open the door of `𝒟ₒ-intro`.

The corrected target beside the original, as D-10 asks:
`Below` (`Probe697.agda:72-74`), then `from-below` is paid.

## 3. TWO Ks, AND ONLY ONE SERVES THIS CONSUMER

**`K = Lset lam`.** Escapes. `kvalue-escapes` is green
(`agents/tasks/LJ-1-679/runs/W3.agda:36-37`). Not used.

**`K = Lset δ`.** A member of `Lset lam` (`lset-in-stage`). It does
not contain `hierL δ`. It does not inhabit `HierInStage`.

**`K = hierL δ`.** The type `HierInStage` names this membership.
Unpaid. `Below` is the named bound in terms of `δ`.

## 4. WHAT THE NEXT BRIEF SHOULD FUND

1. **`Below` / `HierBelow`**, `hierL δ ∈ Lset (δ+3)`, at this `isL`
   witness or `[LJ-1.536]`'s. `from-below` then pays `HierInStage`.
   Do not re-dispatch `from-below`, `ordinal-in`, `climb`,
   `lset-in-stage`, or `Lset∈suc`.
2. **Then `CompletenessFrom`**, `SameHyp` and `HierInStage` to
   `Completeness`. Do not fund `hier-in-stage` from `Lset-out`,
   `Lset-mono` and `succλ` alone.
3. **Do not use `KValue`'s `K = Lset λ`.** `kvalue-escapes` is green.
4. **Do not take `lset-in-stage` as `HierInStage`.** Different objects.
5. **Do not re-dispatch `inBound`, `count-matrix₃`, or
   `bound-from-stage`.** Green in `[LJ-1.673]`.
6. **Do not re-dispatch the syntax of `matrix₃`.** Green in
   `[LJ-1.667]`.
7. **Do not fund `Matrix₂`.** D-10 in `[LJ-1.665]` still stands.

This file is the critic's input and it does not close the task.

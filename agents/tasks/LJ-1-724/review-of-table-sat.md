# Review of `table-sat` — NO-GO (the stated target is false)

**The target, restated:** `table-sat : (γ) (oγ) (hγ) (x) → ⟨ x ∈ˢ γ ⟩ →
⟨ pr x (Lset x) ∈ˢ carved ⟩` at the `Carved` frame of
`agents/tasks/LJ-1-698/Probe698.agda:107-123`. The obligation is **false as
stated**. The obstruction is a rank obstruction at the A-bound, not an
induction gap: no satisfaction chain, landed or landable, can inhabit it,
because the reading it reduces to has no witness at the top entry of a
successor ordinal. This is D-10's check firing: the residue recorded by
`[LJ-1.704]` named a target, and the target is false at its stated
generality.

## The chain, all in-tree

1. `carveSat` (`src/L/Axioms/Separation.lagda.md:163-168`) equates
   `⟪ Lset σ ⟫↪ m ∈ carve (RL.liftFo φᵣ hφ)` — that is, membership of the
   pair in `carved` (`Probe698.agda:119-120`) — with the satisfaction of the
   unlifted `φᵣ` at the pair's environment.
2. `φᵣ = relativize (LsetS γ oγ) (recordedFo (γ , hγ))`
   (`Probe698.agda:108-109`). Relativization binds every raw existential at
   `con A` with `A = Lset γ` and leaves already-bounded ones untouched
   (`src/FOL/Manipulation/Relativize.lagda.md:57,60`).
3. The recording is `∃̇∈ (con γ') (PairGraphAt (suc zero) zero)`
   (`Probe698.agda:84-85`), and `PairGraphAt e c = ∃̇ (prAtL (suc e) (suc c)
   zero ∧̇ GraphAt zero (suc c))` with `GraphAt w b = ∃̇ (ApproxAt zero
   (suc b) ∧̇ Step (suc w) (suc b) zero)`
   (`src/L/Coding/Sequence.lagda.md:328-329,291`). Its raw `∃̇` over the
   approximation becomes `∃̇∈ (con A)`: **the reading demands an
   approximation `f` with `⟨ f ∈ˢ Lset γ ⟩`.**
4. `StepAt v b f = extAt v (∃̇ (∃̇ (∃̇ (StepBody b f))))`
   (`src/L/Coding/Sequence.lagda.md:119-120`): the Step conjunct says every
   `z'` in the value slot lies in `𝒟ₒ w'` for some recorded pair
   `⟨ c , w' ⟩ ∈ f` with `c` in the argument slot — and, relativized, with
   `c`, `w'`, `d` each inside `A`.

## The counterexample: γ = 2, x = 1

Let `γ = 2`, `x = 1`, so the goal is `⟨ pr 1 (Lset 1) ∈ˢ carved ⟩`, with
`A = Lset 2`. Reading the goal through step 1–4:

- The Step conjunct's value slot is `w = Lset 1 = { ∅ }`, so it must cover
  `z' = ∅`: some `c ∈ 1` (hence `c = 0`), some `w'`, some `d ≡ 𝒟ₒ w'` with
  `∅ ∈ d`, and `⟨ 0 , w' ⟩ ∈ f`.
- `∅ ∈ 𝒟ₒ w'` holds for **every** `w'` (the empty set is `⊥̇`-definable over
  any base), so nothing constrains `w'` downward — but the pair `⟨ 0 , w' ⟩`
  must be a **member of `f`**, and `⟨ 0 , w' ⟩` has rank ≥ 2 for every `w'`
  (even `w' = ∅`: `⟨ 0 , ∅ ⟩ = {{ ∅ }}`, rank 2).
- Every member of `Lset 2` has rank < 2 (`Lset-suc`,
  `src/L/Axioms/Basic.lagda.md:196`; the stages are rank-initial). So
  `⟨ 0 , w' ⟩ ∉ Lset 2`, hence no `f ∈ˢ Lset 2` can hold it, and the
  reading fails. **`pr 1 (Lset 1) ∉ carved` at `γ = 2`.**

The same argument kills the top entry `x = γ⁻` of **every successor ordinal**:
the Step conjunct at `z' = Lset c` (any `c` with `c⁺ ≤ x`) forces a
`w' ⊇ Lset c` into `f` (members of `𝒟ₒ w'` are subsets of `w'`,
`src/L/Definability.lagda.md:137`), so `f` carries pairs of rank ≥ `x + 2`,
and `f ∈ˢ Lset γ` needs `x + 2 < γ` — false exactly at `x = γ⁻`.
Independently, the `DefAt` membranes demand formula codes inside `Lset γ`
(`src/L/Coding/Powerset.lagda.md:442-452`: the code and the satisfaction
graph are existential slots of `DefAt`), which fails outright for finite `γ`
below a fixed finite bound. `[LJ-1.704]`'s model argument established the
**no-junk half** (nothing spurious enters `carved`) and is untouched; the
**coverage half** (every table entry enters) is what fails.

## Corrected scopes, for the mathematician to rule

- **Scope fix (per-entry):** add `x + 2 < γ` (all witnesses then fit: the
  approximation `T_x` has rank `x + 3`-ish, the values `Lset c` and
  `𝒟ₒ (Lset c) = Lset c⁺` sit below it) **and** `ω ≤ γ` (the finite formula
  codes enter `Lset ω`). In model terms the reading then goes through with
  `f := T_x`, the table below `x`.
- **Scope fix (frame):** re-bound the frame at a limit `λ ≥ γ + ω`
  (`A := LsetS λ`, `σ := λ`). The graph conjunct pins the value to
  `Lset a` regardless of the bound — `Lset-only`
  (`src/L/Hierarchy.lagda.md:334-335`) says nothing else satisfies the tower
  graph at an ordinal — so the junk `[LJ-1.704]`'s review warned about at
  higher stages should not enter;  but that warning was recorded against the
  earliest-stage reading and must be re-examined before the frame moves.
- **What survives either way:** the reduction of step 1 is the door; the
  probe's `dφ` (`Probe724.agda:53-56`) is its Δ₀ leg; `sgl∈Lset-suc` /
  `pr∈Lset-suc` (`src/L/Axioms/Basic.lagda.md:592-599`) supply the
  pairing-in-stage facts the fiber of the pair needs; and `hier-in` /
  `hier-out` (`src/L/Hierarchy.lagda.md:521-532`) repackage as `Values` /
  `Entries` / `Domain` for `graph-table` (`src/L/Hierarchy.lagda.md:381-399`)
  once the approximation's own stage bound is available.

## Disposition

NO-GO: the target is false as stated. Nothing is landed in `src/`. The probe
(`Probe724.agda`) is green and carries the frame wiring, the Δ₀ certificate,
and 704's stage fact re-measured; the obligation name is absent on purpose.
If the program re-queues this target, it should queue the corrected scope,
not the stated one.

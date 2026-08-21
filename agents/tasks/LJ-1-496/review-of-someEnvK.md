# Review of `someEnvK`

The brief names one new term in `src/L/Condensation.lagda.md`,
`someEnvK`, the environment `SupplyEnv` supplies at `PropAgree`'s
frame, to be used at the `:3515` call and to retire the `someEnv`
parameter and its passing sites in the same commit. This file is the
NO-GO: Repair B is not landable at this chain. The landing did not
start. `src/` is unchanged. The report is
`agents/tasks/LJ-1-496/lj-1.496-report.md`.

## THE STATEMENT

The obligation is the `someEnv` parameter of `PropAgree` at
`src/L/Condensation.lagda.md:3317-3320`, consumed at the `back` call
at `:3515`, with the term's body from `SupplyEnv.someEnv` at
`src/L/Coding/EnvSupply.lagda.md:417-444`. The predecessor
`[LJ-1.493]` is GO, verdict at
`agents/tasks/LJ-1-493/lj-1.493-report.md:70-72`, with the term
typechecked at the probe frame,
`agents/tasks/LJ-1-493/Probe493.agda:139-184`. The brief is
Repair B of `[LJ-1.488]`, `agents/tasks/LJ-1-488/lj-1.488-report.md:308`.

I did not write `someEnvK`. The construction typechecks at the probe
frame, and the chain does not carry the carrier to the frame.

## D-10, BEFORE ANY AGDA

The brief's clause: open the real frame and say at `file:line`
whether `lam`, `gam`, and the gate `⟨ ω ∈ sucV gam ⟩` can reach
`PropAgree` from where it is instantiated. If `LowerAgree:269` cannot
supply them, STOP AND SAY SO: that would mean Repair B is not
landable at this chain.

The condition is met. The three values have no source at the
instantiation site:

1. The frame of `module LowerAgree` is at
   `src/L/Condensation/LowerAgree.lagda.md:226-229`:
   `{n : ℕ} (N0 ... K : Fin (5 + n)) (γ : S ^ (11 + n))`
   `(lf : LFacts ...)`. It binds `Fin` indices and one vector. It
   binds no `V ℓ` stage, no `IsOrd`, no gate.
2. The only other source in scope at `:269` is `open LFacts lf` at
   `:232`. `LFacts` is the record at `:95`, 37 fields through
   `:224`. Every field is a proposition about the given `γ`. No
   field binds a stage or the gate.
3. The module's imports, `:21-36`, take `module AndAgree` and
   `module OrAgree` from `L.Condensation` at `:33-36`. They take no
   `KValue` and no `EnvSupply`: the census over the two chapter files
   returns no line naming either.
4. The only `lam : V ℓ` and `gam : V ℓ` binders in the three
   chapters are the parameters of `module KValue` at
   `src/L/Condensation.lagda.md:7380-7383`. `KValue` receives the
   carrier as a parameter. It does not supply it.

The upstream frame is equally generic. `LowerAgree` is instantiated
only at `src/L/Condensation/TwelveAgree.lagda.md:496` and `:503`,
inside `module AbstractFrame`, whose frame is `:337-342`. It binds
no stage and no gate. `AbstractFrame` has no application anywhere in
`src/`, and the only import of the chapter is the bare module import
at `src/Everything.lagda.md:393`.

**SAY SO:** `lam`, `gam`, and the gate do not reach `PropAgree` from
`LowerAgree:269` or `:275`. Nothing in scope at `:269` can serve as
the three new arguments. Repair B is not landable at this chain.

## W3

The W3 named term is the `PropAgree` telescope of the new arguments
reaching its two callers at `LowerAgree:269` and `:275`. The
experiment is not run. The brief's own ordering rules it: D-10 is
"BEFORE ANY AGDA", and its stop condition is met on the current
tree. When the arguments cannot reach, "the landing stops at its
cheapest point and the old code is still whole". The cheapest point
is before any edit. The tree is whole: `git status` carries only
`agents/tasks/LJ-1-496/`, untracked.

Two walls stand, and each alone is a NO-GO. Wall 1 is the D-10
census above. The experiment makes the arguments reach only by
adding them to the `LowerAgree` telescope at `:226-229` and, above
it, to the `AbstractFrame` telescope at
`src/L/Condensation/TwelveAgree.lagda.md:337-342`. Neither frame is
in the brief's five groups, and the brief binds the widening: "If a
deletion breaks a consumer this brief did not name, that consumer is
the finding: name it at `file:line` and STOP rather than widening
the edit." The threaded carrier would end at `AbstractFrame`, which
no consumer in `src/` instantiates.

Wall 2 is genericity, independent of Wall 1. The probe's body closes
the concrete bound `Lset lam` in three places: `SE.someEnv` takes
`yaK : ⟨ fst ya ∈ Lset lam ⟩` at
`src/L/Coding/EnvSupply.lagda.md:419` and returns
`⟨ fst E ∈ Lset lam ⟩` at `:422`; `SE.transK` closes
`⟨ fst x ∈ Lset lam ⟩` at `:273`; `SE.envInK-gen` closes
`⟨ fst z ∈ Lset lam ⟩` at `:356`. The `someEnv` parameter of
`PropAgree` closes the generic slot instead,
`⟨ fst ya ∈ fst (lookup K γ) ⟩` at
`src/L/Condensation.lagda.md:3317-3320`, and the call site at
`:3515` spends the result at the generic environment, `hbody` at
`:3527`. In the generic frame `{m : ℕ} (C T B N K : Fin m)`
`(γ : S ^ m)` at `:3285`, `fst (lookup K γ)` is an arbitrary `S`,
and no path from it to `Lset lam` is in scope. The probe typechecks
only because its frame is `KValue`'s `Kenv`, whose slot 1 is
definitionally `LsetS lam ordλ`
(`src/L/Condensation.lagda.md:7390`), and `LsetS β oβ = Lset β ,
isL-Lset β oβ` (`src/L/Axioms/Basic.lagda.md:161`). Re-measured at
its own site, the construction is not generic.

## WHAT IS NOT HERE

- No `someEnvK`. The term is not written.
- No edit in `src/`. The five groups stand as they were: the call at
  `:3515`, the parameter at `:3317`, `:3569`, `:3624`,
  `someEnvDef` at `LowerAgree.lagda.md:52-58`, `LFacts.someEnv` at
  `:218`, the pass-throughs at `:273` and `:279`, `TFacts.someEnv`
  at `TwelveAgree.lagda.md:289`, and its fill at `:442`.
- No Agda run. No median wall time and no peak RSS are reported,
  because no run exists. I do not fund a number the brief guessed or
  [LJ-1.493] measured at another site.

## WHAT THE NEXT BRIEF NEEDS

The choice between Repair A and Repair B re-opens. The brief's own
words: the mathematician "must re-open the choice against Repair A".

- Repair A of [LJ-1.488] states the same missing source for its
  gate: "`ω∈γ` still has no source at `someEnvDef`, at `KValue`, or
  at `PropAgree`"
  (`agents/tasks/LJ-1-488/lj-1.488-report.md:346-348`). Its gate
  still needs a source at `PropAgree`, and the frame of `someEnvDef`
  is generic in its carrier the same way `PropAgree` is.
- If the next brief wants the field retired, it must name the frame
  at which the carrier becomes a value. Either the chain is
  specialized to `KValue`, which is a new design decision and not
  Repair B as stated, or the carrier is threaded through
  `LowerAgree` and `AbstractFrame` and the genericity wall is
  answered with a named mechanism. Neither is a landing this brief
  authorized. The choice is the mathematician's.

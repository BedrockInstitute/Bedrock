# review-of-same-as-graph: a STATED NO-GO, with pins at the numerals written

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.672
obligation: agents/tasks/LJ-1-672/Probe672.agda::same-as-graph
verdict: **NO-GO on the obligation. The twelve tag witnesses
are the numerals, and pins holds of them. Neither direction of
SameAsGraph inhabits at the type [LJ-1.520] named.**

The obligation term is NOT written. The probe is green and carries
no hole (`runs/p-final-1.out`, `EXIT=0`). W3 is green
(`runs/w3-final.out`, `EXIT=0`).

**THIS IS NOT A REFUTATION OF `SameAsGraph`.** I did not build a
term of its negation. What is measured is that the type as stated,
at an arbitrary environment with no limit telescope, does not
discharge the site facts the two directions spend.

---

## 1. THE TYPE TAKEN FROM THE PREDECESSOR

`SameAsGraph` (`agents/tasks/LJ-1-520/Probe520.agda:192-195`) is

    ( ⟨ γ ⊨ fst (levelFo-Σ₁ w b) ⟩ → ⟨ γ ⊨ LsetGraphAt w b ⟩ )
  × ( ⟨ γ ⊨ LsetGraphAt w b ⟩ → ⟨ γ ⊨ fst (levelFo-Σ₁ w b) ⟩ )

`[LJ-1.520]` closed GO on `levelFo-Σ₁` and left this type uninhabited
(`agents/tasks/LJ-1-520/lj-1.520-report.md:3-6`, `:289-291`). The
report does not name the type FALSE. This task takes that type.

## 2. D-10, AT THE STATED GENERALITY

The type quantifies over an arbitrary environment. It has no `IsOrd`
and no limit `λ`.

The first conjunct consumes a `K` that the Σ₁ formula produced. That
`K` is only transitive, plus pins (`Probe520.agda:95-128`). `KFacts`
(`src/L/Condensation.lagda.md:6082-6115`) asks for numerals in `K`,
pairing-closure of `K`, and `carrierK`. pins puts the numerals in
environment slots. transK is transitivity. Neither field is a
membership of a numeral in `K`.

The tree's one `KFacts` value is `KValue`
(`src/L/Condensation.lagda.md:7369-7373`). Its bound is `Lset λ` for
a limit `λ`. Its telescope is `HullStage`'s. SameAsGraph does not
carry that telescope.

`extAtB→extAt` (`src/L/Condensation.lagda.md:2514-2518`) needs the
satisfiers-in-`K` fact. `[LJ-1.520]` already recorded that transK
does not supply it at the leaf (`lj-1.520-report.md:318-322`).
`[LJ-1.162]` named the missing `powK` (`𝒟ₒ` of a recorded value in
`K`) and measured that nothing in `src/` supplies it
(`agents/tasks/LJ-1-162/lj-1.162-report.md:141-167`). `Bound.PowIter`
still takes `powIter` as a hypothesis
(`src/L/Coding/Bound.lagda.md:147-152`).

The second conjunct must choose an adequate `K`. `+ω`
(`src/L/Ordinal/StageArith.lagda.md:41-42`) builds an ω-block above
a stage. Suc-closure of `+ω` is not delivered. `KValue` still wants
`succλ` and `∅∈λ`.

The literature names the gap. `dev/literature/level-formula-slot-roles.md:60-63`:

    Devlin's `∃w` carries the conjunct `K(w,u)`, "which says `w = K(u)`"

A bare existential states "SOME bound works". Devlin states "THE
canonical bound works". Those are different statements. The type
this brief named is the bare-existential one.

## 3. W3, WHAT DID CLOSE

pins holds of `numeralL 0` through `numeralL 11`, at `[LJ-1.520]`'s
Matrix, both at a dummy tail (`runs/W3.agda`, module `Pins`) and at
the thirteen-slot environment (`Reverse.hpins`). Green,
`runs/w3-final.out`, `EXIT=0`, 2.85 s, peak 657,522,688 bytes.

The reverse therefore has its tag witnesses. What it still needs is
a transitive adequate `K` at which `graphBndAt` holds, and then the
thirteen existentials packed. Packing did not infer through a
where-chain (unsolved `_φ` metas). That is plumbing, not a stop on
the mathematics.

## 4. WHAT THE NEXT BRIEF SHOULD FUND

1. **Do not re-dispatch pins at the numerals.** `Pins.pins` and
   `Reverse.hpins` are green.
2. **If the reverse is funded, fund an adequate `K` first.** That is
   `KValue`'s `Lset λ` at a limit above the approximation, including
   suc-closure of `+ω` or a `HullStage` telescope, plus `powIter`.
   Then `graphBndAt` from `LsetGraphAt`, then packing with an
   explicit formula argument.
3. **If the first conjunct is funded, do not expect transK and pins
   to discharge `KFacts`.** The bound must be determined, as Devlin
   writes it, or the site facts must be extra hypotheses.
4. **Do not inhabit SameAsGraph at an arbitrary environment
   without a limit.** The type as named does not carry one.

This file is the critic's input and it does not close the task.

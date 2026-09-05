# Review of `envSet-in-carrier-stage`

**NO-GO. The target is FALSE as stated.** The brief's type carries the
hypothesis `⟨ ω ∈ˢ γ ⟩` and still fails, at the successor `γ = sucV (sucV ω)`
which satisfies that hypothesis. The refutation is machine-checked:
`agents/tasks/LJ-1-730/Probe730.agda::envSet-in-carrier-stage-false`
(Probe730.agda:208, term at :204) closes `Empty.⊥` from the obligation's
conclusion instantiated at the counterexample. The file is green, EXIT=0
(`agents/tasks/LJ-1-730/runs/p-11.out`), under `--cubical --safe
--guardedness`, with no postulate and no hole.

## The stated target

The obligation of brief LJ-1.730, verbatim except that the V-level
membership is renamed `∈ˢᵥ` because the CS-level one keeps the bare `∈ˢ`
(the 725-SPLIT disambiguation):

    (γ : V ℓ) (oγ : IsOrd γ) → ⟨ ω ∈ˢᵥ γ ⟩
    → (A : S) → ⟨ fst A ∈ Lset γ ⟩
    → (n : ℕ) → ⟨ envSet A n ∈ˢ LsetS γ oγ ⟩

It is exported as a TYPE at Probe730.agda:116 with no inhabitant, the
725-SPLIT form. No term of it can be written without inconsistency.

## The counterexample

| object | value | why it satisfies the brief's hypotheses |
|---|---|---|
| `γ` | `sucV (sucV ω)` = ω+2, an ordinal (`Probe730.agda:86`) | `IsOrd` by `suc-ord (suc-ord ω-ord)` (:89) |
| hypothesis | `⟨ ω ∈ˢ γ ⟩` | `∈sucV-inl (self∈sucV ω)` (:92) |
| `A` | `Lset (sucV ω)` as an `S` (:98) | `isL-Lset` gives the certificate; `⟨ fst A ∈ Lset γ ⟩` by the sealed zeroth instance, `𝒟ₒ-intro` at `⊤̇` renamed by `Lset-suc` (:104) |
| `n` | 1 | |
| the key member | `ω ∈ˢ fst A` | `ord∈Lset-suc ω ω-ord` (:101) |

With `g : Ix A 1` the environment that maps 0 to ω, `envSet-in` (`src/L/Coding/EnvSet.lagda.md:381`) puts
`envS A g` inside `envSet A 1`, and the pair `pr (# 0) ω` sits in that
environment (the concrete `env` entry at index 0; EnvSet's own `into`
direction, re-read at Probe730.agda:165 because `into` is private).

## The refutation chain

Four `rank-mono` links (`src/L/Rank.lagda.md:117`) climb from `rank ω` to
`rank (fst (envSet A 1))`: ω into `⁅ # 0 , ω ⁆` (`pair-spec`, right
disjunct, `src/V/Model.lagda.md:91`), the pair into the Kuratowski pair
(`pr` is transparent, `src/V/Coding.lagda.md:176`), that into the
environment, the environment into `envSet A 1`. Then `rank-Lset`
(`src/L/Ordinal/Stages.lagda.md:190`) pins the last rank inside
`sucV (sucV ω)`. The two successors peel by `∈sucV-elim`
(`src/V/Model.lagda.md:218`), and each of the four descents consumes one
link by the transitivity of the ordinal ω (`ω-ord`,
`src/L/Ordinal.lagda.md:263`, first component). What remains is
`rank ω ∈ˢᵥ ω`; `rank-fix` (`src/L/Rank.lagda.md:191`) reads it as
`ω ∈ˢᵥ ω`, and `∈-irrefl` (`src/V/Hierarchy.lagda.md:155`) closes `⊥`.

## Why `ω ∈ˢ γ` cannot work

`ω ∈ˢ γ` is not a limit hypothesis. At a successor `γ = ζ+1` a member `m`
of `fst A` can sit at stage ζ, and the Kuratowski pair that records `m`
costs two successors above the stage that holds both components
(`pr∈Lset-suc`, `src/L/Axioms/Basic.lagda.md:596`), so the recording pair
and the environment that carries it leave `Lset γ`. The environment set
cannot sit below its own members: `envSet-in` is landed
(`src/L/Coding/EnvSet.lagda.md:381`), so the failure is not a defect of
this probe but of the scope. This is the same membrane class [LJ-1.724]
measured (verdict item 4, read in the 724 worktree at
`/Users/alsg/Agentic/Bedrock/.pod-state/worktrees/LJ-1-724/agents/tasks/LJ-1-724/lj-1.724-report.md`,
verdict sentence 4; the brief cites it as premise 4), now measured at the
environment set: there the corrected scope was "limit `γ ≥ ω`"; here
`ω ∈ˢ γ` alone is not that scope.

## The corrected target, for ruling

The headroom the proof needs is a fixed finite successor block above the
stages that hold `A`'s members, kept inside `γ`. Three shapes name it:

1. `γ` a limit at or above ω, the 724 corrected scope.
2. `ω`-closure of `γ`: `closedω` is landed at
   `src/L/Ordinal/StageArith.lagda.md:81`, with `boundCloses` (:86) and
   `envCloses` (:92) already lifting members of `Lset (+ω δ)` and
   `Lset (sucIter 3 δ)` into `Lset α` under exactly that closure.
3. A per-instance rank hypothesis bounding the members of `fst A`
   strictly below `γ` with finite headroom.

Which of the three is ruled is the mathematician's call, and the price
must be measured after the ruling, not before. What is measured here is
only the negative: no inhabitant exists at `ω ∈ˢ γ` alone.

## The sweep, owed before the next GO price (C-42)

This refutation measures ONE site. It says nothing about the sibling
sites the 725-SPLIT report named beside this one: `keyS-in-carrier-stage`
([LJ-1.729]) and the `Sat` bound. The same witness shape, a carrier
holding ω at `γ = ω+2`, is the first thing to price at each of them
before any brief spends on them at `ω ∈ˢ γ`. The sweep is the next
action; the cure is not.

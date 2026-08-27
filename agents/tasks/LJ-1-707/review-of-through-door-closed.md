# Review of through-door-closed

task: LJ-1.707
author: coder, 2026-08-27
verdict: **THIS FILE IS NOT A NO-GO STOP.** The meter resolves the
obligation (`runs/meter-obligation.out`: `pass exit=0`,
`probe_red=False`). It records the CONTRACT the term closes, for the
critic and for whoever queues `[LJ-1.704]` and `[LJ-1.705]`.

## What was assembled

`through-door-closed` (`agents/tasks/LJ-1-707/Probe707.agda:80-90`)
takes EXACTLY TWO undischarged inputs, at the rows `[LJ-1.698]`
corrected (`agents/tasks/LJ-1-698/lj-1.698-report.md:117-119`), and
returns `[LJ-1.693]`'s `ThroughDoor`
(`agents/tasks/LJ-1-693/Probe693.agda:135-139`) verbatim:

1. **identification** (`Probe707.agda:55-58`): for every `(γ, oγ, hγ)`,
   `At.carved γ oγ hγ ≡ fst (hierL γ hγ oγ)`, where `At.carved` is
   `[LJ-1.698]`'s carved set (`agents/tasks/LJ-1-698/Probe698.agda:123`).
   This is the type `[LJ-1.704]` aims to deliver.
2. **the-bound** (`Probe707.agda:60-64`): for every limit `α` with
   `γ ∈ α`, `⟨ At.σ γ oγ hγ ∈ α ⟩`, where `At.σ` is the stage of
   `[LJ-1.698]`'s `bound-of` (`agents/tasks/LJ-1-698/Probe698.agda:111-112`).
   This is the type `[LJ-1.705]` aims to deliver.

δ in the Σ-witness is σ itself; δ ∈ α comes from input 2;
`Door (Lset σ) carved` is `[LJ-1.698]`'s own `carved-door`
(`agents/tasks/LJ-1-698/Probe698.agda:128-129`), carried along the
identification equation by `subst`. Composed with `[LJ-1.693]`'s own
`from-door` (`agents/tasks/LJ-1-693/Probe693.agda:141-150`), the route
delivers `HierInK` end to end (`the-route`, `Probe707.agda:100-101`).

## What this proves and what it does not

It proves the two misses `[LJ-1.698]` named
(`lj-1.698-report.md:38-39`) are THE WHOLE DISTANCE between its
unidentified door and `ThroughDoor`. No third input appeared.

It does NOT prove either keystone. Both types stay undischarged here,
by design. Nothing rebuilds `adequacy-bnd`, funds DOWN, or inhabits
`ApproxInK` (`lj-1.698-report.md:41-45`). Nothing lands in `src/`.

## Contract for the keystones

Each of `[LJ-1.704]` and `[LJ-1.705]` may deliver at these types or
any WEAKER-looking sibling that still instances the telescopes here;
a WEAKER delivery still feeds the assembly, because a weaker
hypothesis keeps the term total. A delivery that needs MORE than one
of the two, or an extra premise on either side, falsifies the GO and
must come back to a critic as a new fact.

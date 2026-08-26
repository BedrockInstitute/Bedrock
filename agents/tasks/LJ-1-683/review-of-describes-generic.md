# review-of-describes-generic: a STATED NO-GO, with the subset formula

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.683
obligation: agents/tasks/LJ-1-683/Probe683.agda::describes-generic
verdict: **NO-GO on the closed term.** `describes-generic` of type
`(σ y : S) → ⟨ y ∈ˢ Lset σ ⟩ → Describes σ y` is not inhabited.
The name sits inside `module At` (`Probe683.agda:175-177`) and is
not lifted to the probe module. The witness meter reads
`1 UNRESOLVED of 1, 0.89 s, probe_red=False`
(`agents/tasks/LJ-1-683/runs/meter-obligation.out:2`). The probe is
green and carries no hole (`runs/p-final.out`, `EXIT=0`).

**THIS IS NOT A REFUTATION OF `describes-generic`.** I did not
build a term of its negation. The statement is true at every pair
the predecessors named: the tower pair (`[LJ-1.674]`), the first
non-stage singleton (`[LJ-1.677]`), and the generic singleton
(`describes-sgl`). What is measured is that the tree cannot close
the arbitrary-member case today.

The critic reads this file. It does not close the task.

---

## 1. WHAT THE SEARCH TRIED

The floor, then the generic formula, then the consumer.

1. **The floor of the exact obligation.** `runs/FLOOR.agda.txt`:
   the type `(σ y : S) → ⟨ y ∈ˢ Lset σ ⟩ → Describes σ y` and a
   hole. Exit 42 at the one designed hole. P-l holds: the type
   names no `sucV`.
2. **The generic formula is `x ⊆ y`.** `subsetFo`
   (`Probe683.agda:71-72`) is `∀̇∈ (var zero) (var zero ∈̇ con m_y)`
   over `⟪ Lset σ ⟫`, with `y` a constant from the stage. W2. It
   does not list members of `y`. It does not spend `pair∈𝒟ₒ`. It
   does not spend `⊤̇`.
3. **The consumer is paid.** `from-hyps` (`Probe683.agda:147-150`)
   delivers `Describes σ y` from `Dee⊆stage` (`:75-76`) and
   `StagePowDef` (`:79-81`). Those two hypotheses say: `𝒟ₒ y` sits
   in the stage as a collection of members, and every subset of
   `y` that already sits in the stage is definable over `y`. The
   consumer spends `subsetFo` and not a `Formula Code 1`. Meter of
   the five top-level names: `0 UNRESOLVED of 5, 0.90 s,
   probe_red=False` (`runs/meter-names.out:6`).

The closed term the brief named is not built. The name is inside
`At` so the witness at the probe module does not find it.

## 2. D-10, THE TARGET IS NOT FALSE

I did not find a cardinality or Tarskian obstruction to
`Describes σ y` at a generic member `y` of `Lset σ`.

A necessary condition is `𝒟ₒ y ⊆ Lset σ`, because `defSet⊆A`
(`src/L/Definability.lagda.md:137`). That is `Dee⊆stage`. It
holds at every pair the predecessors closed. I did not inhabit it
at a generic `y`.

The subset formula carves the members of the stage that are
subsets of `y`. That equals `𝒟ₒ y` exactly when `StagePowDef`
holds. For a finite `y` and LEM, every subset is a finite
disjunction of equalities to elements, so `StagePowDef` is the
shape `[LJ-1.677]` paid at a singleton. For a generic `y` the
elements are not listed, and `src/` has no formula that says "x
is definable over y".

The corrected target beside the original, as D-10 asks, is the
same type. It is not closed. The consumer `from-hyps` is that type
conditional on the two hypotheses.

## 3. WHAT A COUNTEREXAMPLE WOULD HAVE TO DECIDE

A pair `(σ, y)` with `y ∈ Lset σ` and no formula over
`⟪ Lset σ ⟫` whose `defSet` equals `𝒟ₒ y`.

Two routes to such a pair:

1. `𝒟ₒ y ⊈ Lset σ`. Then `defSet⊆A` forbids every formula. I did
   not find this at a hereditarily finite member. The first
   non-stage `y₀ = ⁅ sucV ∅ ⁆s` has `𝒟ₒ y₀ = ⁅ ∅ , y₀ ⁆`, both
   members of `L₃`.
2. `𝒟ₒ y ⊆ Lset σ` but `𝒟ₒ y` is not a definable subset of the
   stage. That is a Tarskian gap: the stage cannot name
   definability-over-`y`. I did not inhabit a term of this
   negation. `[LJ-1.664]` measured `DefAt` at 166 constants and
   did not transport it to `Formula ⟪ Lset σ ⟫ 1`.

The frame admits the tower pair and it admits every singleton
that sits with `∅` in the stage. Both are closed. D-26 says a
member of a definable power carries no generation data, so a
generic `y` does not carry a key that lists `𝒟ₒ y`. A refutation
has to name a specific `y`. I did not find one.

## 4. THE UNPAID ROUTE

The pairing formula carves `{∅, y}`. That equals `𝒟ₒ y` only at a
singleton (`[LJ-1.677]`). The tautology carves the whole stage.
That equals `𝒟ₒ y` only at `(sucV δ, Lset δ)` (`[LJ-1.674]`). The
subset formula carves `{ x ∈ Lset σ | x ⊆ y }`. That equals
`𝒟ₒ y` only under `Dee⊆stage` and `StagePowDef`.

Nothing in `src/` supplies those two hypotheses at a generic `y`.
A `Formula Code 1` for `𝒟ₒ` stays a second debt. `[LJ-1.664]`'s
census of `DefAt` at 166 constants still stands.

`from-hyps` shows the two hypotheses are the supplier for the
family `PowIter` needs. They are not paid.

---

The next brief should not re-dispatch `describes-generic` as a
closed term until it names a supplier for `StagePowDef` (or for a
`Formula Code 1` that carves `𝒟ₒ y` directly). Do not re-dispatch
the tower pair, the named singleton, or `describes-sgl`. The
consumer is paid. The subset formula is paid. The arbitrary
member is not.

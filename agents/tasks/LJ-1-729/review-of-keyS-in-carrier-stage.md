# Review of `keyS-in-carrier-stage`

## HEAD

task: LJ-1.729
reviewed name: agents/tasks/LJ-1-729/Probe729.agda::keyS-in-carrier-stage
verdict: **NO-GO, STATED.** The brief's type is FALSE at its stated
generality. The hypothesis `omega in^sv gamma` does not repair the
membrane: a successor gamma above omega still fails to hold the key.
The D-10 truth check below records the counterexample. The corrected
target is stated and INHABITED in the same probe, as
`keyS-in-carrier-lim`, under the additional hypothesis
`closedomega gamma` (src/L/Ordinal/StageArith.lagda.md:86). Nothing
here re-funds `stage-read`, `carved-is-hier` or `table-sat`.

## 1. Why the target is false at `omega <= gamma`

The obligation asks for `keyS A phi in^s LsetS gamma ogamma` for every
carrier `A` in `Lset gamma`, every formula `phi` over it, and every
ordinal `gamma` above `omega`.

The shape of the key decides the question. `key iota iotaL phi` is
`pr (# n) VCode.⌜ mapFo iota phi ⌝` (src/L/Coding/InL.lagda.md, the
`key` clause), and `VCode.⌜_⌝` costs one Kuratowski pairing per
constructor node with the carrier's own members nested inside
(src/FOL/Coding.lagda.md:104-136). The tree's own law
`pr∈Lset-suc` (src/L/Axioms/Basic.lagda.md:596) charges two stages per
pairing. So the stage that holds the code CLIMBS WITH THE SIZE OF
`phi`, above the stage that holds the carrier's members. A gamma that
sits only finitely many successors above the constants cannot absorb
an unbounded climb. The hypothesis `omega in^sv gamma` says nothing
about that gap: `gamma` may be a successor.

## 2. The counterexample (D-10 truth check, recorded)

All steps below are the tree's own lemmas, read externally. The tower
is opaque, and this probe does not internalize a non-membership; the
descent is a rank computation in the tree's own vocabulary.

1. Let `gamma := sucV (sucV omega)`. `IsOrd gamma` holds by `suc-ord`
   twice from `omega-ord` (src/L/Ordinal.lagda.md:263), and
   `omega in^sv gamma` holds by `self∈sucV` and `∈sucV-inl`.
2. Let the carrier be `A` with `fst A := ⁅ Lset omega ⁆s`. The set
   `Lset omega` is a definable subset of itself
   (`Lset⊆𝒟ₒ`, src/L/Constructible.lagda.md:320), so it sits at
   `Lset (sucV omega)`, and its singleton is definable over
   `Lset (sucV omega)` with `Lset omega` as a parameter. Hence
   `fst A in Lset gamma`.
3. Take `phi := (con c iṅ con c)` over the one-slot alphabet, whose
   single constant is `c := Lset omega`, and `n := 1`, so
   `key iota iotaL phi = pr (# 1) (tag0 (pr (tag0 c) (tag0 c)))` with
   `tag0 x = pr (# 0) x`.
4. Descent. For a Kuratowski pair, `pr x y in M` demands `x in M` and
   `y in M` (its members are the singletons and the pair built from
   `x` and `y`). So `key in Lset gamma` would force
   `pr (tag0 c) (tag0 c) in Lset (sucV omega)`, which forces
   `tag0 c in Lset omega`, which forces `c in Lset omega`. That last
   membership is FALSE: every member of `Lset omega` lies at a finite
   iterate of the operator over the empty stage and is hereditarily
   finite, while `Lset omega` is infinite. The chain
   `key in Lset (omega + k)` for growing `k` is exactly the climb the
   probe lands constructively, and it never enters `Lset (omega + 2)`.

So the type fails at a gamma that satisfies every hypothesis of the
brief. Any scope without closure above the carrier's stage repeats
this refutation.

## 3. The corrected target

One hypothesis repairs it: `closedomega gamma`, the closure of gamma
under the `+omega` block (src/L/Ordinal/StageArith.lagda.md:86). The
proof shape, delivered green:

1. `Lset-out` gives a witness `delta in^sv gamma` that holds the
   carrier's members (`Lset-out`, `𝒟ₒ∋⊆`).
2. `ord-tri` puts `omega` below, equal to, or above `delta`; in each
   case a common stage `sigma in^sv gamma` holds both the constants
   and the numerals.
3. The climb places the code at SOME finite iterate `sucIter j sigma`
   (an EXISTENTIAL iterate, so no weight function and no max), and
   the key two stages above it.
4. `+omega-iter` lifts `Lset (sucIter (suc (suc j)) sigma)` into
   `Lset (+omega sigma)`, and `closedomega` plus `Lset-mono` close
   into `Lset gamma`.

This is `keyS-in-carrier-lim` in the probe. At the counterexample's
gamma the hypothesis fails: `closedomega (sucV (sucV omega))` is
false, which is the honest boundary of the bound.

## 4. What the next brief needs

1. Fund the move of the climb and the absorption into `src/` (a home
   beside `L.Coding.CodeSet`), priced by the probe's verdict run, not
   by this review.
2. The spine assembly that `stage-read` needs may now consume the
   closedomega-scoped key bound. Price the spine AFTER the bound
   lands in `src/`.
3. Do not re-fund `smallAny`'s hidden stage: the corrected route
   never touches `boundingOrd`.
4. If some later chapter needs the bound at a NON-closed successor
   gamma, the scope to price is the carrier held `omega` stages BELOW
   gamma (a slack hypothesis), not the brief's `omega in^sv gamma`.

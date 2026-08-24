# review of `graph-stage-at`: the crossing's G+ slot accepts the restated face and the crossing's kit rejects the restated matrix, both measured as terms; the cheaper repair pays the face and not the crossing

## VERDICT

**THE TERM IS NOT SUPPLIED, AND THE STOP IS THE CONSUMER'S ANSWER.** The
obligation (`agents/tasks/LJ-1-614/Probe614.agda::graph-stage-at`, the type
`GraphStageAt ψ₀` of `agents/tasks/LJ-1-610/Probe610.agda:231-233` at the
guarded machine matrix `ψ₀ = guardSL ⇒̇ matrixSL` of `:241-242`) is one
import away from green (`reduction` at `Probe614.agda:194-195` IS
`[LJ-1.610]`'s `graph-stage-from-wit`), and I did not land it under a new
name, because the brief's real question -- **does the crossing accept
`GraphStageAt` in place of `GraphStage`** -- has the two-part answer this
file records, and the second part overturns the ruling the brief
dispatched under. The meter says the obligation is missing:
`agents/tasks/LJ-1-614/Probe614.agda::graph-stage-at` returns `missing
exit=42`, `[NotInScope]`, `1 UNRESOLVED of 1`, `probe_red=False`
(`agents/tasks/LJ-1-614/runs/meter-1.out`, 3.07 s). The probe itself is
green and carries no hole (`runs/p-3-final.out`, exit 0, 3.84 s, peak
831,291,392 bytes, interface deleted first).

## THE MEASUREMENT, BOTH HALVES

**HALF ONE, THE SLOT ACCEPTS.** `slot-accepts`
(`agents/tasks/LJ-1-614/Probe614.agda:129-132`) inhabits

    (ψ : Formula DR.SM 3) → GraphStageAt (mapFo DR.inL ψ) → GraphStage ψ

with ONE LINE and NO TRANSPORT: `map inL (q ∷ γ ∷ [])` is
`inL q ∷ inL γ ∷ []`, `mapFo inL (∃̇ ψ)` is `∃̇ mapFo inL ψ`
(`src/FOL/Manipulation/Relabelling.lagda.md:64`), and `fst (inL q)` is
`fst q`, all definitional. And the whole crossing then consumes the
restated face UNCHANGED: `CrossingAt` (`Probe614.agda:143-145`) is
`[LJ-1.606]`'s kit with its G+ component restated at the image matrix,
`crossing-at→crossing` (`:148-150`) converts it into `[LJ-1.606]`'s own
`Crossing` by `slot-accepts` alone, and `inner-to-ambient-at`
(`:152-154`) is `[LJ-1.606]`'s own term applied to the conversion. **At
every `inL`-image matrix, the crossing accepts the restated face, and
that acceptance cost one definitional line.**

**HALF TWO, THE KIT DOES NOT.** The crossing's demand on G+ is not the
slot but the BINDING (`[LJ-1.606]`, `agents/tasks/LJ-1-606/
Probe606.agda:178-180`): the matrix `ψ` is bound at the HULL carrier
`Formula CI.I.SM 3` with `Δ₀ ψ` as the kit's first component, and that
grade is spent at leg 4 (`Σ₁-carried CI.I.g ψ dψ`, `Probe606.agda:238`,
from `:201-204`). The restated matrix is a STAGE-carrier formula, and
`kit-rejects-ψ₀` (`Probe614.agda:173-178`) is the refutation of the
identity route:

    (ψ : Formula DR.SM 3) → mapFo DR.inL ψ ≡ ψ₀ → Δ₀ ψ → ⊥

For any such `ψ`, `mapFo-Δ₀` (`Probe606.agda:189-199`) would give
`Δ₀ ψ₀`, hence `Δ₀ matrixSL` (the `⇒̇` inversion), hence a Delta-zero
witness for `mapFo numSL (domAt zero (suc (suc zero)))` -- and `domAt`
is headed by an UNBOUNDED `∀̇` (`src/L/Coding/Model.lagda.md:278-280`,
body at `:279`), a head for which the Delta-zero datatype has NO
constructor (`src/FOL/LevyHierarchy.lagda.md:47-58`: the constructor
list stops at the bounded `δ-∀∈` and `δ-∃∈`). **No hull matrix that
relabels onto the restated matrix carries the kit's grade.** This is
`[LJ-1.610]`'s wall 3 moved from a supply statement to a refutation
term.

**AND THE MIDDLE BINDS THE SAME CARRIER.** Even with the grade waived,
the restated face's conclusion (a STAGE-carrier satisfaction of `∃̇ ψ₀`)
cannot enter the crossing's middle: face E, which `[LJ-1.609]` paid, has
type `ElemDown = (n : ℕ) (φ : Formula SM n) ...`
(`src/L/BoundedSubset.lagda.md:410-412`, spent at `Probe606.agda:230`),
and the collapse iso's transfer `iso-inv : (n : ℕ) (φ : Formula SM n)
...` (`src/L/BoundedSubset.lagda.md:195-197`, spent at
`Probe606.agda:233`) binds the same hull carrier. The middle is
hull-shaped end to end; a stage-carrier matrix has no delivered road to
the collapsed constants, because the stage-side lift `σ₁-up` moves
statements along `fst` to the AMBIENT at the UNCOLLAPSED pair
(`src/FOL/Absoluteness.lagda.md:182-183`), while the commute's decode
needs the COLLAPSED pair `(π (Lset δ), π δ)`, which only `iso-inv`
reaches -- at hull formulas.

## WHAT THIS OVERTURNS, AND WITH WHAT SCOPE

The ruling this brief carries (2026-08-24, in `LJ-1.614.md`) chose the
cheaper repair because it "is already prototyped" and does not re-open
face E. **The cheaper repair restates the FACE where the face was
cheapest and leaves the kit's demands standing where they were**: the
carrier and the grade that stopped `[LJ-1.610]` at the face's own
statement stop the crossing at the kit's binding, unchanged. The
refutation above closes the identity route by term. The non-identity
routes are not refuted here and do not need to be: a kit matrix that is
merely IMPLIED by `ψ₀` at the stage is exactly `[LJ-1.610]`'s wall 3
(no kit-grade matrix is hosted at arity three; the tree's Delta-zero
level-hood matrix carries its bound as a FOURTH slot,
`src/L/BoundedSubset.lagda.md:109-111`) plus `[LJ-1.606]`'s own
`NoDegenerate` (junk fails G- outright, `Probe606.agda:260-280`). So
the crossing has NO delivered consumption of the restated face at any
matrix: identity by this task's term, non-identity by the predecessors'
measurements.

Per the brief's own sentence, this NO-GO overturns the ruling: the
cheaper repair cannot close the crossing without one of the two things
it was chosen to avoid. Either the kit's binding moves -- the arity-4
kit with the bound as a slot, the stronger repair -- or the middle moves
to the stage carrier, which unpays `[LJ-1.609]`'s face E and, on the
reading above, still owes a NEW face to carry the statement across the
collapse `π`. Which of the two the campaign funds is not my call; what
is mine to say is that both are kit changes and neither is a face
build, which is what the brief told me to say before spending.

## WHAT IT PRICES FOR ROW 3

- Row 3's G+ is now REDUCED (to `WitStage`, `[LJ-1.610]`'s residue, wall
  1, unfunded research) and its CONSUMPTION is now REFUTED at the kit
  the crossing actually is. The blocker count did not drop from three to
  one; it crystallized into ONE structural fact: the kit is hull-bound
  and Delta-zero-bound at arity three, and the machine matrix is
  neither.
- The arity-4 repair's first price is now measurable: `levelHoodB`
  (`src/L/BoundedSubset.lagda.md:108-114`) is the delivered Delta-zero
  body; the kit's legs are arity-polymorphic as TYPES (face E at
  `src/L/BoundedSubset.lagda.md:410-412` and the iso at `:195-197` bind
  `n : ℕ`), so whether the arity change re-opens face E is a TERM
  question the campaign must now price, not assume in either direction.
- The E-side repair's hidden cost is named above: the stage-side lift
  lands at uncollapsed constants, so it owes a collapse-crossing face
  that nothing in the tree delivers.

## SCOPE

I wrote only inside `agents/tasks/LJ-1-614/`. Nothing is postulated, the
probe carries `--safe`, the delivered file is green with no hole, and
nothing lands in `src/`. No commit, no push.

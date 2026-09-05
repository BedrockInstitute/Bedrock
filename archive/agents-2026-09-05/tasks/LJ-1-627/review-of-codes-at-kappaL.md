# [LJ-1.627] stop: code data at the ambient-least ordinal is the bridge, and the bridge is false in the collapse semantics

## THE STOP

**NO-GO, stated, on `codes-at-kappaL`.** The type is the consumer's
own hypothesis shape, verbatim
(`agents/tasks/LJ-1-623/Probe623.agda:140-141`), restated at this
task's alone-checked W3 (`agents/tasks/LJ-1-627/runs/W3.agda:56-58`)
and tied by one refl (`agents/tasks/LJ-1-627/Probe627.agda:98-99`):

    Codes-at-κL = (a : S) (oa : IsOrd (fst a))
                → Σ[ F ∈ S ] InjCode F a (κL a oa)

No term of the probe carries the obligation's name, and no term of the
probe or of the tree inhabits this type as its body. Nothing was
postulated. Nothing landed in `src/`. Nothing was committed and
nothing was pushed.

**THIS STOP IS STRONGER THAN AN UNINHABITED-ON-THIS-TREE STOP: THE
TARGET IS FALSE AT ITS STATED GENERALITY.** The brief's own D-10 order
was to price the target's truth before pricing its proof. The price is
paid, and it is the same price `[LJ-1.623]` paid for
`AmbientToCoded`, plus one step.

## THE TRUTH MEASURE, AND THE ONE STEP IT ADDS

`[LJ-1.623]`'s review fixed the falsifying pair: in a classical
semantics where the ambient and the constructible cardinality of one
pair disagree (a collapse extension at `a = ℵ₁^L`, `b = ω`), "the
ambient injection exists and no code does"
(`agents/tasks/LJ-1-623/review-of-site-fiber.md:79-83`). That semantics
is a legitimate reading of this tree's ambient theory (Cubical Agda
over the HIT `V` with LEM assumed; the metatheory is recorded at
`dev/literature/digest.md:417-419`).

The step this task adds: **in that same semantics, `κL a oa` at that
`a` IS `ω`.** `κL` is the least member of the stage after `a` that
receives a TRUNCATED AMBIENT injection from `a`: the predicate is
`InjP γ = ∥ Inj γ ∥₁` (`src/L/Cardinal.lagda.md:66-67`), the search is
`leastOf w lem InjP' nonempty` over the sealed ordinal well-order
(`src/L/Cardinal.lagda.md:112-117`), and the seal is `κL`
(`src/L/SquareLawClosed.lagda.md:73-74`). The collapse ambient sees
`ℵ₁^L` countable, so `ω` is in the search's range and receives an
injection; no finite ordinal receives an injection from an infinite
ordinal in any ambient; so the search stops exactly at `ω`. Codes at
`κL a oa`, at that `a`, are codes at `ω` held as DATA, which is
strictly more than the truncated code existence the review measured
absent. **So the obligation is false at `a := ℵ₁^L` in that semantics,
and a term of the all-a shape cannot exist.**

## THE IDENTITY, MEASURED GREEN

The obligation is not merely falsified in one semantics; it is
PROVABLY the bridge's hardest instance, in both directions, by green
rows:

- `codes→bridge : Codes-at-κL → BridgeLeast`
  (`agents/tasks/LJ-1-627/Probe627.agda:162-163`), where `BridgeLeast`
  (`:157-159`) is `[LJ-1.623]`'s `AmbientToCoded`
  (`agents/tasks/LJ-1-623/Probe623.agda:157-159`) specialized to the
  pair `(a, κL a oa)`.
- `bridge→trunc : BridgeLeast → TruncCodes-at-κL`
  (`agents/tasks/LJ-1-627/Probe627.agda:165-168`), reading the tree's
  own sealed ambient injection at the least pair (`κ-injL`,
  `src/L/SquareLawClosed.lagda.md:82-84`) through the bridge.

So DATA at `κL` gives the bridge instance, and the bridge instance
gives the truncated form of the obligation. `[LJ-1.623]`'s landing row
re-derived site-free (`coded-sits-above`,
`agents/tasks/LJ-1-627/Probe627.agda:123-126`) supplies the other
side of the park: every coded target sits at or above the ambient
least. Equality of the coded-least and the ambient-least is exactly
the bridge, which is what the obligation asserts. The two reopeners
`[LJ-1.623]` listed are ONE demand, not two.

## WHY THE UNTRUNCATION IS NOT THE WALL

The brief's distinction ("data, not `∥ … ∥₁`. That distinction is the
task") is real but it is not where the wall sits. The tree's own
device turns truncated CODE existence into DATA once it may search a
stage covering the codes of one pair (`leastOf`,
`src/L/WellOrder/Base.lagda.md:158-160`; the pattern
`agents/tasks/LJ-1-623/Probe623.agda:135-139`; the canonical instance
`src/L/Cardinal.lagda.md:192-195`). The untruncation row
`Trunc→Codes` is stated TYPE ONLY at `agents/tasks/LJ-1-627/Probe627.agda:191-192`;
it wants a stage-bounded code search the tree does not have at this
grain (`isL` names no stage, `src/L/Constructible.lagda.md:376-377`),
and it is MOOT: its hypothesis is the truncated bridge instance,
falsified above. In the Kraus terms the brief orders
(`dev/literature/truncation-and-selection.md:158-159`, Theorem 16): at
the collapse pair the code type is EMPTY, its identity is a weakly
constant endomap, split support holds vacuously, and the data is still
absent. The criterion converts a SUPPLIED `∥X∥` into `X`; the missing
input is `∥X∥` itself, and that input is the bridge.

## WHAT WOULD REOPEN IT

- The owner's ruling on `AmbientToCoded` as an axiom, already carried
  to the owner by `[LJ-1.623]`
  (`agents/tasks/LJ-1-623/review-of-site-fiber.md:104-105`). This task
  measured that the first-listed reopener (codes at `κL`, as data) is
  the same demand at its hardest instance, so the axiom is the only
  route on this row that does not re-price a falsehood.
- Or a weakly constant endomap on the AMBIENT payload at the
  single-pair grain (`agents/tasks/LJ-1-623/review-of-site-fiber.md:106-110`),
  which bypasses codes entirely. This task did not touch it.

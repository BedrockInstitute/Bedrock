# review-of-step2-unconditioned: NO-GO on the obligation as stated

**THE OBLIGATION IS NOT INHABITED AND IT IS NOT MISSING BY ACCIDENT.**
`agents/tasks/LJ-1-660/Probe660.agda` carries no term named
`step2-unconditioned`. The meter records it:
`agents/tasks/LJ-1-660/runs/meter-obligation.out:2`,
`1 UNRESOLVED of 1, 7.12 s, probe_red=False`. The probe itself is GREEN
(`agents/tasks/LJ-1-660/runs/p-15.out`, `EXIT=0`), so the return is a
STATED stop and not a failed landing.

**THE ONE-SENTENCE REASON.** `PiReflectsOrd` cannot delete the `IsOrd y`
slot, because the collapse both REFLECTS and PRESERVES ordinality at a
hull member, so the fact it can be traded for is the same fact; and the
statement that remains after the trade is not a corollary of anything
built, it IS `[LJ-1.646]`'s UN-ordinal keystone.

## 1. What the brief asked for, in the three readings it admits

The brief names `<[LJ-1.647]'s hull-closed-lset as a HYPOTHESIS>` and
`<[LJ-1.462]'s step 2 WITHOUT the IsOrd y slot>`.
`[LJ-1.462]`'s step 2 is `HullClosedLset`
(`agents/tasks/LJ-1-462/Probe462.agda:136-138`), which carries no
`IsOrd` slot at all, so the conclusion is fixed. The hypothesis admits
three readings and `agents/tasks/LJ-1-660/runs/HOLES.agda.txt` states
all three:

| reading | hypothesis | line |
|---|---|---|
| (a) | `[LJ-1.647]`'s delivered CONCLUSION, `HullClosedLsetOrd` | `runs/HOLES.agda.txt:53` |
| (b) | the same, with the brief's named route applied | `runs/HOLES.agda.txt:59` |
| (c) | `[LJ-1.646]`'s KEYSTONE, with `[LJ-1.647]`'s built term applied to it | `runs/HOLES.agda.txt:65` |

**EVERY ONE OF THE THREE LEAVES EXACTLY ONE HOLE AND NO OTHER ERROR.**
`agents/tasks/LJ-1-660/runs/holes-1.out:5-9`, three
`[UnsolvedInteractionMetas]` at `53.35-40`, `59.61-66` and `65.57-62`.
Reading (c) carries strictly more than reading (a), and the hole does
not move.

## 2. The named route moves the hole; it does not close it

Reading (b) is the brief's own proposal: apply
`[LJ-1.654]`'s `PiReflectsOrd` and supply `IsOrd (C.π y)` instead of
`IsOrd y`. The hole after the trade is at
`runs/HOLES.agda.txt:59`, and it is `IsOrd (C.π y)` at the SAME
arbitrary hull member.

**THE TWO HOLES ARE ONE HOLE, AND THAT IS MEASURED.**
`[LJ-1.654]` built both directions (`pi-ord-iso`,
`agents/tasks/LJ-1-654/Probe654.agda:354-356`).
`AtSite.the-two-holes-are-one`
(`agents/tasks/LJ-1-660/Probe660.agda:135-136`) lifts the equivalence
from a member to the quantifier and is green
(`agents/tasks/LJ-1-660/runs/meter-names.out`, `0 UNRESOLVED of 15`).
So substituting the fact the brief calls "now built" is a no-op on the
debt.

## 3. What the obligation's conclusion actually is

`AtSite.the-obligation-is-the-unordinal-keystone`
(`agents/tasks/LJ-1-660/Probe660.agda:164-167`) is green and it gives
both directions between `HullClosedLset` and the truncated UN-ordinal
keystone `LsetCode∥`:

- keystone to closure is `[LJ-1.647]`'s own generic term,
  `hull-closed-op∥` (`agents/tasks/LJ-1-647/Probe647.agda:135-149`);
- closure to keystone is `hull-mem-is-code`
  (`agents/tasks/LJ-1-647/Probe647.agda:89-91`), which is `refl`.

**SO THE BRIEF'S OBLIGATION IS `[LJ-1.646]` IN THE UN-ORDINAL FORM, AND
NOT A COROLLARY OF ANYTHING GREEN.** A task that closed it would have
closed `[LJ-1.646]`'s un-ordinal variant, not composed two delivered
terms.

## 4. The gap fact is false at the theorem's own telescope

The hole as a type is `AllHullOrd`, "every hull member is an ordinal"
(`agents/tasks/LJ-1-660/Probe660.agda:106-107`). With it the obligation
is one line (`gap-fact-closes-it`, `:114-115`), so it is the whole of
the gap. Two green consequences price it:

- `AtTheorem.gap-fact-forces-x-ordinal`
  (`agents/tasks/LJ-1-660/Probe660.agda:268-269`) forces `IsOrd x`,
  where `x` is THE ARBITRARY BOUNDED SUBSET the chapter is about. Its
  telescope carries `x⊆Lα` and no ordinality:
  `src/L/StageBound.lagda.md:68-69`. The route is
  `X = Lset α ∪ ⁅ x ⁆s` (`src/L/BoundedSubset.lagda.md:1149-1150`),
  `x∈X` (`:1156`), and `X⊆M` (`src/L/Hull.lagda.md:354-355`).
- `AtTheorem.gap-fact-makes-the-stage-an-ordinal`
  (`agents/tasks/LJ-1-660/Probe660.agda:288-291`) makes `Lset α` itself
  an ordinal, because the stage is transitive
  (`layer-trans (Lset-layer α)`, `src/L/Constructible.lagda.md:183` and
  `:246`) and the gap fact makes every member of it transitive.

**I DID NOT BUILD A CLOSED `⊥`.** That needs a concrete non-transitive
member of a concrete stage, which this task did not price. The evidence
above is a derivation to two statements the chapter does not have and
cannot want, and it is enough to stop.

## 5. What the brief asked in W3, answered YES

W3 asks "whether `PiReflectsOrd`'s hypothesis `IsOrd (C.π y)` is
available where step 2 is CONSUMED". **IT IS, AT ALL FOUR SITES**, and
the answer is built and not asserted. See section 4 of
`agents/tasks/LJ-1-660/lj-1.660-report.md`.

**SO THE BRIEF'S NO-GO CLAUSE DOES NOT FIRE.** The brief says NO-GO
"earns which of the four sites cannot supply `IsOrd (C.π y)`, which
re-prices the un-ordinal keystone from preferable to mandatory". No site
fails. **The un-ordinal keystone stays PREFERABLE and does not become
MANDATORY.**

## 6. Why no term of that name was written at another type

A term named `step2-unconditioned` at any type the tree can support
would be metered as RESOLVED, and the branch table's `go` row keys on
`obligations_delta_max = -1`. That is a GO the measurement does not
support. The name is left unwritten so the return routes to
`stop-stated` and a critic reads this file.

## 7. What was delivered instead of the obligation

Two green files, eighteen green names, no hole and nothing in `src/`
(`runs/meter-names.out`, `0 UNRESOLVED of 15`, and
`runs/meter-chain.out`, `0 UNRESOLVED of 3`).

- `agents/tasks/LJ-1-660/Probe660.agda`: the measurement above, plus
  `levelin-from-keystone` (`:190-194`), which puts `[LJ-1.647]`'s step 2
  and `[LJ-1.654]`'s reflection in one file for the first time, and
  `module FeedTheSite` (`:233-239`), which hands that term to the REAL
  `src/L/BoundedSubset.lagda.md:916-918` consumer's `levelIn` slot.
- `agents/tasks/LJ-1-660/Chain660.agda`: one step further.
  `levelin-from-keystone-and-hood` stands `levelIn` on `[LJ-1.646]`'s
  keystone and ONE level-hood formula, because `[LJ-1.653]` reduced step
  4 at ordinals.

The full account is `agents/tasks/LJ-1-660/lj-1.660-report.md`.

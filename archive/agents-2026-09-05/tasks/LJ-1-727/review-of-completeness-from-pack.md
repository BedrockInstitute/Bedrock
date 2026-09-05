# LJ-1.727: NO-GO on completeness-from-pack, stated

## HEAD
head_slot: coder
machine: shared
task: LJ-1.727
target: `completeness-from-pack : SameHyp → HierInStage → Completeness`
verdict: **NO-GO.** The name is not declared in `Probe727.agda`. The
obligation type is not inhabited, and no hole is shipped: the file is
green, EXIT=0 (`agents/tasks/LJ-1-727/runs/p-1.out`), so the meter
reads the truth, MISSING.

## The menu, answered item by item

The brief asks which of pack, graph, or SameHyp still fails to reach
`inBound`. Two of the three reach as far as their types allow, and the
third stops one leg short. Precisely:

1. **pack is not the failure.** `pack-stage` is consumed at
   `[LJ-1.721]`'s export name (`agents/tasks/LJ-1-721/Probe721.agda:114`),
   and all three components fire green in the delivered file:
   `same-at-codes` and `hier-at-code` at
   `agents/tasks/LJ-1-727/Probe727.agda:99-117`, `graph-at-pair` at
   `:120-131`, and the supply term `level-at-pair` at `:138-149`. The
   floor confirmed every one of these compositions at the type level
   before any body was filled (`runs/floor-1.out`, EXIT=42 with
   exactly the four designed holes).
2. **SameHyp is not the failure.** It fires at the packed pair, the
   `[LJ-1.700]` firing (`agents/tasks/LJ-1-700/Probe700.agda:53-58`)
   taken at the export. Its levelFo direction closes the SUPPLY term
   green: SameHyp plus IsOrd plus the level equation give the
   UNBOUNDED level reading at the packed pair
   (`Probe727.agda:138-149`, top-level export at `:166`).
3. **The graph leg is the failure, and it fails at its last mile.**
   `Lset-defines` (`src/L/Hierarchy.lagda.md:646-653`) fires and
   gives the UNBOUNDED graph reading at the packed pair. `inBound`
   does not spend that reading. It spends the BOUNDED one, at a
   witness slot no hypothesis supplies. The stop is measured: the
   supply term is green, and the composition from it to
   `BoundInStage` is not written, because no inhabited term in the
   tree carries it.

## Why the last mile does not close: the two shapes do not match

**The demand is bounded, at a fixed witness.** `inBound ca cp` is
`∃̇ (∃̇ (matrix₃-Code ∧̇ ≐ ∧̇ ≐))`
(`agents/tasks/LJ-1-673/Probe673.agda:83-89`), and `matrix₃-Code` is
`mapFo slide matrix₃` where `matrix₃ = isOrd-at-p ∧̇ φ₃` and
`φ₃ = W3.erased` (`agents/tasks/LJ-1-667/Probe667.agda:72-73`).
`W3.three` is twelve `∃̇∈` wraps of `Mx.matrix`, each bounded by the
last slot, and the K slot of `Mx` IS that last slot:
`kk = suc^14 zero`, `ww = suc^12 zero`, `bb = suc^13 zero`
(`agents/tasks/LJ-1-667/runs/W3.agda:45-49`). So the demand's matrix
reading is: twelve numerals, each a member of `z`; `z` transitive;
the table itself a member of `z`
(`src/L/Condensation.lagda.md:2493`, `graphBndAt = ∃̇∈ (var K) ...`,
with K read as the witness); the bounded rows at that `z`.

**The supply is unbounded, at an existential table.** `levelFo` binds
its thirteen slots by thirteen UNBOUNDED `∃̇`
(`agents/tasks/LJ-1-520/Probe520.agda:171-185`, the prenex block), and
inside the matrix the table is `∃̇∈ (var K)` with `K` itself one of
those free existentials. The supply names no numeral-membership fact
and no witness set.

**The bridge between the two shapes is named in the tree and not
inhabited.** `[LJ-1.520]` stated `SameAsGraph` and did not inhabit it
(`agents/tasks/LJ-1-520/Probe520.agda:193-195`). `[LJ-1.667]` named
the bridge explicitly: BRIDGE 2, `graphBndAt` to `LsetGraphAt`, "No
module GraphAgree exists under src/"
(`agents/tasks/LJ-1-667/Probe667.agda:92-96`). The soundness twin of
that bridge NO-GO'd at `[LJ-1.719]` and was upheld: "I confirm the
NO-GO on independent evidence and could not overturn it"
(`agents/tasks/LJ-1-719/review-of-LJ-1-719-1.md:46-48`). My task is
the production direction of the same bridge, and nothing in the
hypothesis types carries it.

## Why no witness slot is supplied

`BoundInStage`'s existentials range over `AbsL`'s carrier, whose
elements carry `⟨ fst a ∈ˢ Lset lam ⟩`
(`src/L/Hull.lagda.md:155-156`), so any witness `z` must be a member
of the stage. The four hypotheses conclude, in full:

- `pack`'s components: `SameAsGraph` at the packed pair, and
  `⟨ fst (hierL ...) ∈ˢ Lset lam ⟩`
  (`agents/tasks/LJ-1-721/Probe721.agda:89-102`). No `z`.
- `Lset-defines`: an hProp, no data (`src/L/Hierarchy.lagda.md:646-648`).
- `SameHyp`: two satisfaction implications at a pair
  (`agents/tasks/LJ-1-520/Probe520.agda:193-195`). No `z`.
- The frame: `elem`, `ordλ`, `succλ`, `∅∈λ`, `X⊆Lλ`. None concludes
  a numeral membership, a transitivity, or a table membership at a
  chosen `z`.

At the one `z` the hypotheses DO reach, the internal table
`hierL δ`, the reading is machine-checked FALSE: `[LJ-1.716]`'s
refutation at `δ₀` (`agents/tasks/LJ-1-716/review-of-LJ-1-716-1.md:52`,
the brief's premise 2). The table's members are Kuratowski pairs and
the pins need a member-free first numeral, so no table at any ordinal
carries the reading; the any-ordinal form of that falsity is prose,
not measurement, and `[LJ-1.716]`'s review says so
(`agents/tasks/LJ-1-716/review-of-LJ-1-716-1.md:101-104`). I do not
retry that type.

## The corrected target, D-10

The brief's target may be worse than unproven. Prose analysis, flagged
as prose per the `[LJ-1.716]` ruling: at the parameter `δ = ∅` the
bounded step row (`src/L/Condensation.lagda.md:2413-2426`,
`stepBndAt = extAtB v K witB`) reads: every member of the witness set
is a member of some value the table records. At `δ₀` the table
records nothing, so the witness would have to be empty, and the pins
need a first numeral inside it. On that reading the demand fails at
EVERY witness, `BoundInStage` is false at the empty codes, and
`Completeness` itself (`agents/tasks/LJ-1-679/Probe679.agda:73-80`)
is false at those codes, with `hier` still true at them. Whether that
holds turns on whether `SameHyp` is inhabitable at the frame, which
is `[LJ-1.719]`'s open territory. **The named probe for the next
dispatch**: machine-check the vacuity at `δ₀`, that is, from the
frame hypotheses derive the negation of `BoundInStage` at the codes
of `∅` and `Lset ∅`, or show it fails. A green refutation re-routes
the campaign the way `[LJ-1.716]` did; a green failure prices the
bridge honestly instead.

## What would reopen the target

1. A production-side Bridge 2: from the unbounded graph reading at a
   pair, plus a witness `z` with numeral-membership, transitivity and
   table-membership site facts, to the bounded rows at `z`. Priced
   against `[LJ-1.719]`'s twin, this is a campaign-scale leg, not a
   160-line filler.
2. The `δ₀` vacuity probe above, either way it lands.

## Standing

The obligation name stays open, delta 0. The supply term
`level-at-pair` is delivered green at
`agents/tasks/LJ-1-727/Probe727.agda::level-at-pair` and is tracked
supply for the successor. Nothing landed in `src/`. Nothing is
postulated; the delivered file carries `--safe` and no hole
(`Probe727.agda:1`).

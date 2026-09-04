# Review of ambient-at-hier: NO-GO, and the target itself is false

Task LJ-1.716. Obligation: `agents/tasks/LJ-1-716/Probe716.agda::ambient-at-hier`.
Slot: coder. Machine: shared, wide tier. Date of run: 2026-08-27.

## Verdict

**NO-GO.** Not "not yet proved": the obligation is FALSE at a specific
constructible ordinal, and the probe machine-checks the refutation in two
green lemmas. The brief's own W3 alternative named the right horn: the 2-slot
graph and the 3-slot matrix remain distinct.

## The site, and the falsity

The obligation asks, for every `δ : CS.S` with `oδ : IsOrd (fst δ)`, for the
reading of `P667.matrix₃` at `(Lset (fst δ), fst δ, fst (hierL (fst δ) (δ .snd)
oδ))` (Probe673.agda:108-109 restates the type).

1. `matrix₃ = isOrd-at-p ∧̇ φ₃` with `φ₃ = W3.erased`
   (agents/tasks/LJ-1-667/Probe667.agda:46-48 and :70-73). `W3.erased` is the
   erased twelve-tag witnessed matrix: `three` opens twelve bounded
   existentials, EACH BOUND BY THE WITNESS SLOT `z`
   (agents/tasks/LJ-1-667/runs/W3.agda:69-79, the `wrap` chain; slot 2 of the
   resulting arity-3 environment is `kk`, the witness). So any satisfaction of
   `φ₃` at `(a, p, z)` demands twelve members of `z`, and `pins` fixes them as
   the numerals `∅` through `#11` (agents/tasks/LJ-1-520/Probe520.agda:122-135:
   `∀̇∈ (var N0) ⊥̇` says N0 has no member; the `sucAtL` chain says each next
   slot is the successor).

2. Take `δ₀ := (∅ , ∅∈L)` with `oδ := ∅-ord`. The internal hierarchy at the
   empty ordinal has NO members: `hierL-spec ∅ h0 o0 : IsHier ∅ (hierL ∅ h0
   o0)` says `fst z ∈ fst h ≡ Recorded ∅ (fst z)` for every carrier element
   (src/L/Hierarchy.lagda.md:501-503), and `Recorded B z` joins over
   `fst c ∈ B` (src/L/Hierarchy.lagda.md:494-496), which at `B := ∅` is empty.
   Probe716.agda:74-96 (`no-member-of-hierL∅`) turns this into a green term:
   any member `x` of the table lifts into the constructible carrier by
   `isL-trans` (src/L/Constructible.lagda.md:393-398), the spec puts it in
   `Recorded ∅ x`, and the join surrenders a `c` with `fst c ∈ ∅`, killed by
   `∅-empty`.

3. The descent from the ambient reading to a member of the table is green:
   Probe716.agda:100-115 (`ambient-at-hier-empty`). Bounded-existential
   satisfaction is a join (src/FOL/Semantics.lagda.md:103), so the
   truncation's own map peels the first `∃ x ∈ z` off any satisfaction of
   `matrix₃`.

So an inhabitant of the obligation at `δ₀` yields a member of a member-free
set: absurd. `zero-refutes` (Probe716.agda:118-131) states this composition;
its body is a designed hole, for a measured reason given below. The
mathematics is fully machine-checked; only the bookkeeping composition is not.

## The miss, named per the brief's menu

The brief asks NO-GO to name which of graph, erase, isOrd-at-p, or slot order
is the miss. The answer: **none of those four; the miss is the WITNESS-SLOT
CONTENT of the matrix itself.**

- The graph is not the miss: `Lset-defines` is green in the tree
  (src/L/Hierarchy.lagda.md:646-653) and gives the 2-slot graph reading at the
  table for every ordinal.
- The erase is not the miss: `W3.erased` reduces fine
  (agents/tasks/LJ-1-673/Probe673.agda:46-47 checks `countFo matrix₃ ≡ 0` by
  `refl`, so the checker sees straight through the erased formula).
- `isOrd-at-p` is not the miss: its two conjuncts are exactly `IsOrd`'s two
  components (agents/tasks/LJ-1-667/Probe667.agda:63-73 against
  src/L/Constructible.lagda.md:141-143), discharged by `oδ` directly.
- The slot order is not the miss: it is Witnessed's value-parameter-witness
  order (Probe652.agda:87-91), and the parameter slot lines up with
  `IsOrd`'s carrier.

The miss: `matrix₃` keeps the witness slot FREE and bounds the twelve
numerals BY it, and the obligation then fills that slot with the table. The
table holds only pairs `pr (fst c) (Lset (fst c))`
(src/L/Hierarchy.lagda.md:501-503), and a Kuratowski pair
`pr a b = ⁅ ⁅ a ⁆s , ⁅ a , b ⁆ ⁆` (src/V/Coding.lagda.md:175-176) is never
empty, so `∅` is not in the table at ANY ordinal, and the numeral chain
`∅, suc ∅, …` is not in it either. The literature binds the witness instead of
keeping it free: Devlin's statement is `v = L_γ ↔ ∃z Φ(z,v,γ)` with `z` at
position 0, `v` at 1, `γ` at 2 (dev/literature/level-formula-slot-roles.md,
table row 4). `matrix₃` is the Witnessed shape whose soundness half keeps `z`
free (Probe652.agda:87-91); reading it AT the table makes the table carry what
only a stage carries.

## D-10, the corrected target, recorded beside the original

The least reading that survives: `matrix₃` at `(Lset δ, δ, z)` with `z` a
stage that carries the numerals and the step witnesses, for example
`z := Lset δ′` with `δ′` past `ω`, NOT the table `hierL δ`. The 2-slot
statement that graph plus SameAsGraph plus erase does deliver is the
thirteen-existential `levelFo` reading at `(Lset δ, δ)`, whose tags are bound
by no slot (agents/tasks/LJ-1-520/Probe520.agda:171-185). Which of these two
shapes feeds Completeness and `LsetGrounded` is the next brief's call; this
probe did not price either.

## C-42 sweep, the count

The shape "tags bounded by the table" occurs at exactly ONE site: this
obligation, the first reading of `matrix₃` at `hierL δ`. The nearest
neighbour, Probe673's `inBound`, pins value and parameter but leaves its
existentials UNBOUNDED (agents/tasks/LJ-1-673/Probe673.agda:74-77), so it
does not carry the shape. `levelFo` binds all thirteen slots unboundedly
(Probe520.agda:171-185) and does not carry it. Count: 1.

## The measured wall, for the heap protocol

The final composition of the two green lemmas at the concrete `δ₀` walls the
checker. Ten restructurings were tested in this dispatch under the same 2 g
wide caliber (owner's ruling 2026-08-23; never rerunning the same shape):

- Green, 3.3 s and 0.70 to 0.85 g each: the fully generic descent
  (runs/vg-1.out, runs/va-1.out, runs/g-1.out), the ∅-vacuity lemma
  (runs/g-3a.out), the generic-application shapes (runs/g-7.out), the floor
  (runs/floor-1.out, 3.4 s, 849 MB).
- Walls at 2.6 to 2.7 g near 300 s: every composition whose conversion
  compares two pointer-distinct types that both spell `Lset ∅` in the
  environment (runs/g-4.out, runs/g-8.out, runs/vh-1.out, runs/vi-1.out,
  runs/vb-1.out, runs/p-7.out). The checker whnf's the `∈-induction` unfold
  of `Lset ∅`; environments spelled with `∅` or variables compare instantly.

The plug is one line and is written in Probe716.agda's comment at
`zero-refutes`:

```
zero-refutes h =
  ambient-at-hier-empty (∅ , ∅∈L) ∅-ord h
    (no-member-of-hierL∅ ∅∈L ∅-ord)
```

Nothing here is a stop on the mathematics. The mathematics is done and green.
The wall is a checker-conversion cost at the concrete ordinal, and the next
brief can fund it (a larger caliber, or a transport whose sides never both
spell `Lset ∅`) without reopening the NO-GO.

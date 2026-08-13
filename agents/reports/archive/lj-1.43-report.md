# LJ-1.43 report: close the six remaining row agreements and block 1

Status: COMPLETE.  Written incrementally per C-22.  ASD-STE100.

## 1. THE VERDICT

SEVEN of the seven closed, machine-checked.  The master is GREEN with
`ExistAgree`, `ClauseAgree`, `MemAgree`, `EqAgree`, `ImpAgree`,
`AllInAgree` and `ExInAgree` delivered.  `src/Everything.lagda.md`
typechecks.  The DD24 rate BREACHES the bar: whole-file 0.0139 s/line
against 0.013193, marginal 0.0459 s/line against the same bar.  The
block is closed; the rate is a measured finding, not a wall.

## 2. THE EXIST ROW AND BLOCK 1 (THE DECIDING CLAIMS)

The [LJ-1.42] wall was inferred, not measured, and the inference was
wrong.  The machine's `consAtL` and the story's `consAtL` are the SAME
formula at the SAME environment (`src/L/Coding/Model.lagda.md:1484-1485`
against `Exist.bodyE`).  No transport along the adequacy is needed: the
leaf transfer is two truncation lifts that add or drop the K-membership
of the extended environment, with written branch types (I-5).  The
`ExistAgree.out` and `ExistAgree.back` terms are delivered
(`src/L/Condensation.lagda.md`, module `ExistAgree`).

Block 1's first consumer found a real defect.  `Clause.subValBnd` read
the key `pr a ya` where the machine's `subValSuccAt` reads
`pr (sucV ar) a`, and it carried a duplicate of the successor conjunct.
The defect survived since [LJ-1.5] because the block had no consumer
(C-35).  The repair removes the duplicate and fixes the key.  After the
repair, `Clause.existBndAt` is DEFINITIONALLY `Exist.existBndAt` at the
class carrier: `shapeBnd` is `arTagB (suc N) zero`, `subValHyp` is
`Exist.subE`, `envHyp` is `envHypU (suc B) zero`, and `bodyBnd` is
`Exist.bodyE`.  So block 1's agreement IS the Exist row: `ClauseAgree`
is one instantiation of `ExistAgree`, with `out = E.out` and
`back = E.back`.

## 3. THE OTHER FIVE ROWS

All five closed with shared leaf machinery, not six ad hoc transports.

- Mem and Eq share `AtomLeaf` (the term-value leaf).  The transfer is
  two nested truncation lifts (I-5) plus the delivered `TmVal` module.
  The K-memberships of the two term values come from the site facts
  `valV` and `valW`.
- Imp uses `ImpLeaf` (the implication leaf).  The machine's relation
  lives at `E ∷ yb ∷ ya ∷ yc ...`; the story's at `E ∷ ya ∷ yc ...`
  and `yb ∷ E ∷ ya ∷ yc ...`.  The subvalue transfers are two transports
  along the adequacies; the environment-set shift is
  `envOverAt-transport`; the operation transfer is definitional, because
  both bodies compute to the same three memberships.
- AllIn and ExIn share `BndLeaf` (the bounded-quantifier leaf), with a
  universal shape and an existential shape.  The universal shape has no
  truncation; the existential shape has three nested truncations with
  written branch types.  The K-memberships of the term value and the
  extended environment come from the site facts `wKfact` and `consK`.

Every agreement takes its site facts as hypotheses, as the delivered
agreements did.  The closures are conditional on them; see section 4.

## 4. THE INHERITED OBLIGATIONS

1. `envInK` remains unproved at the class carrier.  The rows constrain
   the arity to lie in K and the code to be `pr ar (pr #k ...)`; they do
   not force the arity to be a numeral.  The machine-to-story direction
   of every env-carrying row needs `envInK` (an environment over ar with
   values in B lies in K).  The closures are conditional on it, stated
   plainly.  It holds when the arity is a numeral and K is a limit
   level; that discharge belongs to the per-tower instantiation, not to
   this block.
2. The dead scaffolding is removed.  `QuantBody` (about 110 in-fence
   lines) is deleted; the scaffolded `ExistAgree` comment is replaced by
   the delivered code.  Nothing in the file is left as dead scaffolding.
3. Line-count caliber.  `scripts/ledger.py` counts NON-BLANK lines
   inside ```agda fences.  Current working tree: 4,512.  HEAD: 2,498.
   The [LJ-1.42] report's figures (2,802 before, 3,723 after) are its
   own counter's; its before matches the [LJ-1.41] working-tree count
   (2,802-2,805 in the review), so its counter and ledger.py agree on
   that tree.  Its after-tree is not recoverable, so the marginal for
   this dispatch is +789 lines against the reported 3,723, with that
   basis stated.  The [LJ-1.42] "about 210 dead lines" were part of its
   921 marginal; 110 of them (QuantBody) are now gone, and the rest was
   the scaffold, now live code.

## 5. THE NUMBERS

- Whole-file cold: 62.55 and 63.18 user seconds (two runs, one process,
  `GHCRTS="-A64m -I0 -M8g"`, the master's interface moved aside).
- Whole-file rate: about 62.9 / 4,512 = 0.0139 s/line, 1.05 times
  DD24's 0.013193.  BREACH.
- Marginal: 62.9 minus 26.74 (the [LJ-1.42] measured final, its report)
  = 36.2 seconds over +789 lines = 0.0459 s/line, 3.5 times the bar.
  BREACH.
- Module-load cone: 1.28 user seconds, re-measured with a control probe
  that imports the dependency cone without `L.Condensation`.
- The marginal rate rests on the [LJ-1.42] baseline, which I cannot
  re-measure (its tree is gone).  The whole-file rate is measured on
  the current tree alone.

The breach is real and it has a shape: the new content is
instantiation-heavy (P-m's expensive class).  Each row agreement
instantiates `EnvSet`, the shape transfers, the subvalue transfers and
the leaf modules at concrete carriers, and the truncation lifts carry
written types at concrete slots.  I did not profile which module costs
the most.

## 6. DD4

The sharing held.  The six rows use THREE shared leaf modules:
`AtomLeaf` (Mem, Eq), `BndLeaf` (AllIn, ExIn), `ImpLeaf` (Imp alone).
Block 1 uses no leaf of its own: it IS the Exist row.  The shared layer
from [LJ-1.42] (`EnvSet`, `UnaryShape`, `BinaryShape`, `SubValB2T`,
`SubValSuccB2T`, `TmVal`, `extAtB`-`extAt`) is reused unchanged.  The
six did NOT need six different transports; the transfers group by row
family, and the rows differ only in their leaf content and frame
wiring.

D-26 in one line: the rows key on the Def syntax and `Lset` is a
definable power, so D-26's well-founded-key question bears at the
per-tower instantiation, not in these slot-generic agreements.

## 7. LITERATURE USED

`dev/literature/devlin-II5.md`, Step C only: nothing bears.  Devlin
asserts absoluteness where this block proves a decode; the book cannot
price these rows.

## 8. ARCHIVE USED

- `_build/lj-1.42-report.md`, in full.  Took the seven open rows, the
  three inherited obligations, and the measured wall to re-test.
- `_build/lj-1.41-review.md`, in full.  Took the missing-conjunct cure,
  the `EnvSet` route, and the site-fact shapes.
- `src/L/Condensation.lagda.md`, in full.  The delivered rows, the
  frame family, and the agreements.
- `src/L/Coding/Model.lagda.md`, in full.  The machine clauses and the
  adequacy lemmas.
- `dev/LESSONS.md`: C-35, C-36, C-22, D-26, D-29, D-10, P-m bind.

Key locations in the delivered file: `ExistAgree` at
`src/L/Condensation.lagda.md:3593`, `ClauseAgree` at `:3765`,
`AtomLeaf` at `:3820`, `MemAgree` at `:3983`, `ImpLeaf` at `:4084`,
`BndLeaf` at `:4354`, `AllInAgree` at `:4526`, `ExInAgree` at `:4646`,
`ImpAgree` at `:4765`, `EqAgree` at `:4854`, and the block-1 repair at
`Clause.subValBnd` `:144`.

## 9. WHAT I AM NOT SURE OF

1. The composition of the DD24 breach.  The rate is whole-file and
   marginal; I did not isolate which new module costs the most.
2. The marginal baseline.  26.74 seconds is the [LJ-1.42] report's own
   measurement on a tree I cannot re-measure.  The marginal rate rests
   on it.
3. The site facts are hypotheses; I exhibited no model instance.  This
   is the delivered state of the earlier agreements too.
4. The block-1 repair changed delivered content.  `Clause.subValHyp`
   lost its redundant duplicate conjunct and its key is corrected.  The
   agreement is machine-checked against the machine's `subValSuccAt`,
   but the repair is a change to a block that had no consumer before
   this dispatch.
5. `envInK` discharge.  Section 4: the closures are conditional until
   the per-tower instantiation supplies the numeral arity and the limit
   level.

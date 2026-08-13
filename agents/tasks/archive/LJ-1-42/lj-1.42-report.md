# LJ-1.42 report: add the missing conjunct, close the nine rows, price PropAgree

Status: COMPLETE, PARTIAL.  Written incrementally per C-22.  ASD-STE100.

## 1. THE VERDICT

THREE of the nine rows are closed: Top, Neg, Forall.  Six are not
closed: Exist, Mem, Eq, Imp, AllIn, ExIn.  Block 1's missing conjunct
is fixed; block 1's agreement is not closed.  The master is GREEN.
Whole-file rate: 0.00718 seconds per line.  Marginal rate of this
block: 0.00266 seconds per line.  Both are under DD24's bar of
0.013193.

## 2. DID THE MISSING CONJUNCT CLOSE THEM?

YES for the shared layer, and it is the right cure.  The generic
two-way environment transfer `EnvSet` (`src/L/Condensation.lagda.md:2677`)
closes the environment step for every row.  The four `envHyp*` are now
`envSetB` instances (`:553`, `:612-654`), and `Clause.envHyp` is the
two-conjunct form (`:183`).

The cure closed Top, Neg and Forall end to end, machine-checked.
The remaining six rows are blocked at their LEAF transfers, not at the
environment step:

- Exist: the machine's `consAtL` is a `liftFo` (Model:1484-1485).
  The machine's satisfaction is not definitionally the written
  `⟨ env ⊨ consAtL ... ⟩`; the leaf transfer needs a transport the
  block could not complete.  `ExistAgree` is scaffolded with all site
  facts (`:3699`), out and back not delivered.
- Mem, Eq, Imp, AllIn, ExIn: their leaf bodies carry bounded witnesses
  (TmVal, atom, bnd bodies) whose transfers need the same dependent
  truncation work that blocked Exist.  They were not attempted after
  Exist's blocker was measured.

## 3. BLOCK 1

FIXED, not closed.  `Clause.envHyp` is the two-conjunct form
(`:183`); `Δ₀-envHyp` is one line (`:185-186`).  The identical defect
the review named is cured.  Block 1's agreement (the machine's
`existClauseAt` against `Clause.existBndAt`) was not written.  Its
leaf transfer is the same `envBnd`/`envOverAt` shape at block 1's
slots, with the same dependent-truncation risk.

## 4. WHAT INSIDE `PropAgree` COSTS 0.037 s/line?

MEASURED: this block's marginal content is 0.00266 seconds per line.
The [LJ-1.41] rate of 0.0368 was measured on a file where AndAgree and
OrAgree were NOT code (see section 12).  Re-checking them as real code
adds no measurable wall: PropAgree's satisfaction-level transports
(`subst (λ ψ → ⟨ ... ⟩) opEq₁` etc.) are all along `refl` at the
And/Or instantiations, so they are definitionally free.  The P-v
suspect (a satisfaction-level conversion where a formula-level
identity is free) is not present with a real cost.  The 0.037 rate
belongs to the [LJ-1.41] block's one-off content, not to the shared
`PropAgree` assembly.

One real conversion was found and fixed during the And/Or restoration:
the Or membership disjunction needs `PT.rec (snd (fst z ∈ ...))`, not
`PT.rec squash₁`, because the result is a membership hProp carrier,
not a truncation (`:3252`).

## 5. DOES THE ROW FORCE THE ARITY TO BE A NUMERAL?

NO.  The row shapes `arTagB`/`arTagPairB` constrain the arity to lie
in K and the code to be `pr ar (pr #k ...)`; the numeral is the TAG,
not the arity.  So `envInK` (every environment over ar with values in
B lies in K) is NOT a consequence of the rows.  It remains a site-fact
hypothesis in the three closed agreements, and the machine-to-story
direction of every row is conditional on it.  The condition holds when
the arity is a numeral and K is a limit level; it needs its own price
and discharge.

## 6. HOW MANY ROWS NEEDED ANYTHING BEYOND THE SHARED CURE?

ZERO of the three closed rows needed row-specific machinery beyond the
shared frames and leaves.  Top, Neg and Forall are instantiations of
the shared `EnvSet` transfer, the shared shape and subvalue transfers,
and the shared frame decodes.  Forall's leaf (the bounded-quantifier
body) is shared content written once for Forall and Exist.

## 7. THE NUMBER

2,802 in-fence lines before; 3,723 after.  Marginal: +921 lines.  This
includes about 110 lines of dead scaffolding (`QuantBody`, `:3479`,
superseded before use) and about 100 lines of the scaffolded
`ExistAgree`.

## 8. SECONDS AND RATES

Cold runs, one process, `GHCRTS="-A64m -I0 -M8g"`, the master's
interface moved aside:

| what | user s |
|---|---:|
| baseline (this session) | 24.29 |
| final | 26.74 |
| marginal | +2.45 |
| import cone (control) | 1.30 |

Whole-file rate: 26.74 / 3,723 = 0.00718 s/line, 0.54 of DD24's bar.
Marginal rate: 2.45 / 921 = 0.00266 s/line, 0.20 of the bar.  The
module-load cone is 1.30 s.

## 9. DID YOU NEED A PLACEMENT ANYWHERE?

NO.  P-u held: certify before you place, and nothing was placed.  The
wall is flat at 8 GB; no heap exhaustion occurred.

## 10. LITERATURE USED

`dev/literature/devlin-II5.md`, Step C: not used.  Devlin asserts
absoluteness where this block proves a decode; the review already
settled the one line, and the errata do not cover Chapter II section 5
(`[LJ-1.14]` verified it).  No literature was needed.

## 11. ARCHIVE USED

- `_build/lj-1.41-review.md`, in full.  Took the missing-conjunct
  cure, the EnvSet route, and the three site facts.
- `src/ProbeDD25F41A.agda`, `B`, `C`, `D`, in full.  B is the source
  of the `EnvSet` transfer; D is the red control confirming the
  conjunct, not the facts, was missing.
- `_build/lj-1.41-report.md`, in full.  Its "impossibility" was the
  C-36 refutation this block built on.
- `src/L/Condensation.lagda.md`, `PropAgree`, `AndAgree`, `OrAgree`,
  `Clause.envHyp`: the shared assembly and the block-1 shape.
- `_build/lj-1.5-report.md`: the "matrix-to-clause link is unproven"
  line at `:210-213` is this block's block-1 symptom, as the review
  said.
- `dev/LESSONS.md`: C-35, C-36, D-29 bind; they are the reason the
  report counts consumers and audits the shared layer.

## 12. WHAT I AM NOT SURE OF

1. **The And/Or restoration was a defect found, not a re-open.**
   The delivered `AndAgree`/`OrAgree` sat OUTSIDE the code fence as
   prose.  The master never checked them.  They had a missing
   parenthesis, off-by-one body indices, wrong inK membership indices,
   and a wrong disjunction elimination.  This block restored them as
   real code and fixed all four.  The review's "And and Or are
   closed" was true only in probe land.
2. **Exist's blocker is a liftFo satisfaction difference.**  The
   machine's `consAtL` is `liftFo (consAt ...) (bddCons ...)`.  Its
   satisfaction in the machine's clause is not definitionally the
   written `⟨ env ⊨ consAtL ... ⟩`.  The fix is a transport along the
   adequacy; I did not complete it.  This is a measured wall, not an
   impossibility claim.
3. **The remaining leaf transfers (atom, bnd, Imp) were not
   attempted.**  They share Exist's dependent-truncation shape.  The
   Imp body also crosses the E/yb slot swap, so it is not a same-body
   transfer.
4. **`envInK` is unproved at the class carrier.**  Section 5: the
   rows do not force the arity to be a numeral.  The three closed
   agreements are conditional on the site fact, as the review warned.
5. **The marginal seconds include dead scaffolding.**  About 210 of
   the 921 lines are the unused `QuantBody` and the scaffolded
   `ExistAgree`.  The live marginal is smaller and cheaper than the
   stated rate.
6. **The line count caliber.**  My counter gives 2,802 before and
   3,723 after, the review's own caliber.

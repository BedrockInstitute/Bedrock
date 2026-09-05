# LJ-1.37 report: the eleven table clauses and the bounded code-set description

Status: COMPLETE. Written incrementally per C-22. No commit, no push.
The report uses ASD-STE100.

## 1. THE VERDICT

**DELIVERED.** `src/L/Condensation.lagda.md` now carries the eleven
remaining table clauses and the bounded code-set description. The master
has 2,031 in-fence non-blank lines (block 1 was 308; block 2 adds 1,723).
It checks cold in 9.06 seconds of user time, two flat runs, one process,
at `GHCRTS="-A64m -I0 -M8g"`. The rate is 0.00446 seconds per line,
which is 0.34 of DD24's bar of 0.013193. The block funds with wide room.

The eleven rows are at `src/L/Condensation.lagda.md:1078-1398` (the
formulas and witnesses), with the class-carrier transfers and certificates
at `:1709-2140` and the graph assembly at `:2145-2260`.

## 2. DID THE CODE-SET DESCRIPTION STAY INSIDE ITS SURVEY?

**YES.** The bounded code-set description, from `keyArBnum`
(`:1408`) through `Δ₀-DefBodyB` (`:2281`), is 227 in-fence non-blank
lines. The survey is 0.2 to 0.5 thousand lines. It sits at 0.45 of the
top of the survey.

The seconds are inside the survey too. The profile attributes the
description's assembly to `SatGraphB.Δ₀-twelveB` (83 ms), `twelveB`
(58 ms), `Δ₀-satGraphB` (29 ms), `satGraphB` (14 ms), `Δ₀-DefBodyB`
(13 ms) and the leaf witnesses, each below 15 ms. The description's
total is about 0.3 seconds, at most half a second, against the 1.6 to
4.0 second survey. Both halves of the stop-line hold with wide room.

## 3. DID YOU NEED A PLACEMENT ANYWHERE?

**NO.** No placement appears anywhere in block 2. No `absFo`, no
`placeFo`, no constant vector and no appended environment. Every row is
constant-free (the tag numerals are slots), so each instantiates the
delivered `EraseTransfer` template with `refl` (`:1686-1702`). The
description's certificates are built on the bounded formulas directly.
P-u holds: certify before you place, and nothing is placed.

## 4. THE ELEVEN CLAUSES

All eleven landed: `Bot` (`:1078`), `Top` (`:1087`), `Neg` (`:1100`),
`Forall` (`:1128`), `And` (`:1172`), `Or` (`:1207`), `Imp` (`:1242`),
`Mem` (`:1279`), `Eq` (`:1297`), `AllIn` (`:1315`), `ExIn` (`:1340`).
Each row is one instantiation of a shared frame, with its own Delta-0
witness, its two-way decode at the class carrier (the frame decode
composed with the erase transfer), its `EraseTransfer` instantiation and
its Sigma-1 certificate. The rows are K-generic, so the same formula
serves the class carrier (K = zero) and the graph's inner environment
(K shifted by the three graph binders).

The marginal cost of clause eleven against clause one, from the cold
profile: clause 1 of the new eleven (`Bot`) costs about 43 ms
(`BotRow.σL-out` 24 ms, `σL-in` 19 ms, the witness below the profile
threshold). Clause 11 (`ExIn`) costs about 126 ms (`ExInRow.σL-out`
66 ms, `σL-in` 49 ms, `ExIn.Δ₀-exInBndAt` 11 ms; the bounded-quantifier
bodies are shared with `AllIn`). Against the delivered clause 1 of block
1, the existential row, the comparison is starker: `Clause.Δ₀-bodyBnd`
alone is 659 ms and the whole row about 840 ms. The eleventh clause is
6.7 times cheaper than the first. Amortization holds.

## 5. THE NUMBER

`src/L/Condensation.lagda.md`: 2,031 in-fence non-blank lines at the
ledger caliber (non-blank lines inside ` ```agda ` fences). Block 1 was
308; block 2 adds 1,723. The description section is 227 of those lines.
The eleven rows, frames, atoms, decodes and transfers are about 1,496.
The catalog is untouched.

## 6. SECONDS AND RATE

Two cold runs, one Agda process each, quiet machine, at
`GHCRTS="-A64m -I0 -M8g"`, the master's own interface moved aside per
run, dependencies warm:

| run | user s | wall s |
|---|---:|---:|
| 1 | 9.06 | 10.25 |
| 2 | 9.06 | 10.20 |

The pair is flat: the delta is 0.00, under the noise rule. The cone,
measured with an imports-only control in the same session
(`src/ProbeLJ137Ctrl.agda`), is 1.03 seconds of user time. The net
content cost is about 8.0 seconds over the 1,723 block-2 lines, which is
0.00466 seconds per line.

Rate: 9.06 / 2,031 = 0.00446 seconds per line, against DD24's bar of
0.013193. The block sits at 0.34 of the bar. C-31 framing: the budget
for the GCH side is 99.6 to 147.7 seconds and the aggregate is the
judgment. This block's whole measured cost is about 9 seconds plus the
description's profile share, which is 9 percent of the budget's low end.

The meter caveat applies as `[LJ-1.35]` warned: the cone is 1.03 seconds
of the 9.06, and the per-module rate mostly measures the cone plus the
deep-leaf witnesses. The block-2 content itself checks at 0.00466
seconds per line.

## 7. IS `Δ₀ (DefBody (suc zero))` DISCHARGED?

**NO as a literal certificate, and YES as the story's need for one.**
The delivered `DefBody (suc zero)` is not Delta-0 and cannot be: its
leaves carry unbounded quantifiers (`isCodeAt`'s `keyArityAtL` is
`∃̇ (tagAtL ...)` at `src/L/Coding/CodeSet.lagda.md:135-136`,
`satGraphAt` is three `∃̇` at `src/L/Coding/Graph.lagda.md:104-112`,
`DefinesAt` has an unbounded `∃̇` at
`src/L/Coding/Powerset.lagda.md:217-219`). The `Δ₀` data has no
constructor for the unbounded existential
(`src/FOL/LevyHierarchy.lagda.md:47-57`). A certificate on the delivered
formula therefore does not exist.

What this block delivers is the replacement the story needs: the bounded
restatement `DefBodyB` (`:2237`) of the three leaves, with its Delta-0
certificate `Δ₀-DefBodyB` (`:2244`). The step clause's certificate shape
from `[LJ-1.34-R]`, `Δ₀-clause : Δ₀ (DefBody (suc zero)) → Δ₀ ClauseBB`
(`src/ProbeDD25D2.agda:172-179`), was the last place the delivered leaf
appeared; with `DefBodyB` in its place, the premise is `Δ₀ (DefBodyB ...)`
and this block supplies it. The story's certificate chain now closes
without any leaf hypothesis. That is the discharge.

## 8. WHAT THE NEXT BLOCK NEEDS

The step and graph stack: the bounded matrices for the delivered
`StepAt`, `ApproxAt` and `LsetGraphAt` readings, and the story-to-machine
agreement at L (leg D). The pieces this block measured in the archive
are now delivered: the rows, the graph frame with the twelve-row
conjunction, and the leaf description. What remains is the agreement
between the story's bounded matrices and the machine's delivered
readings, and the adequacy of the description against the machine's
leaves under the site facts (codes in K, values in K).

The next block should also confront the machine's atom-row quirk found
during this build: the delivered `atomBody` reads the second term's
value from the value slot `yc` rather than the term slot `b`
(`src/L/Coding/Model.lagda.md:1765-1770`). The story's atom rows read
the term slot. The leg-D agreement for the atom rows cannot be a
definitional equality; it needs the machine's row re-derived or its
private body fixed.

One best-effort price. The remaining step-and-graph stack and the
agreement are surveyed at 0.3 to 0.8 thousand lines
(`_build/lj-1.12-report.md:31-33`) and the measured rate for this class
is about 0.005 seconds per line, which is 1.5 to 4 seconds. The
adequacy of the description against the machine's leaves is part of the
agreement and does not re-open the description's certificate.

## 9. DD4

Template, and the amortization is measured. The shared layer is: the
bounded atoms (`:379-664`), the five row frames (`:666-895`), the frame
decodes (`:904-1075`), the environment hypotheses, and the
`EraseTransfer`/`RowTransfer` machinery (`:1686-1708`). These are generic
in the environment arity and the K slot and mention no tower. The
per-tower content is: the eleven row formulas and witnesses
(`:1078-1398`), the twelve-row conjunction and graph assembly
(`:2145-2283`), and the code-set description's leaves (`:1408-1684`).

The measured marginal cost is 0.04 to 0.13 seconds per extra clause
(section 4). The `[LJ-1.33-R]` figure of 0.08 seconds per clause
reproduces at this site. The J tower instantiates the same frames and
transfers with its own structural content; nothing in the template
mentions the Def syntax.

The one place the split does not amortize is the deep-leaf witnesses:
`Exist.Δ₀-existBndAt` (698 ms) and `Forall.Δ₀-bodyFφ` (657 ms) are the
deeper witnesses, and they are per-tower content. They match
`[LJ-1.36]`'s finding that one deep leaf, not the rows, carries the
weight.

## 10. LITERATURE USED

`dev/literature/devlin-II5.md`, Step C (`:209-256`, summary `:299-302`).
Took the requirement: bind every quantifier of the Def step by the
concrete set K(u) inside the matrix, and write the description once.
**His single-description shape is available for the twelve clauses.**
The twelve rows are a formalization artefact of the machine's
satisfaction table: the story's `satGraphB` (`:2209`) is one bounded
graph formula containing the twelve-row conjunction, exactly Devlin's
single D(v, u) with the K(u) bound. The twelve separate rows exist
because the machine's satisfaction recursion is a twelve-clause table,
not because the argument needs twelve descriptions.

`dev/literature/devlin-errata.md`. NOT read. WHY NOT: `[LJ-1.14]`
verified it does not cover Chapter II section 5, and the brief rules out
re-checking it.

## 11. ARCHIVE USED

`src/L/Condensation.lagda.md` as delivered, whole. Took the block-1
`Clause` shape, the `EraseTransfer` template and the decode pattern.
Block 1 is unchanged.

`_build/lj-1.5-report.md`, whole. Took the eleven-obligation list, the
slot-tag convention and the next-block list.

`_build/lj-1.36-report.md` and `src/ProbeLJ136.agda`, whole. Took the
row layout (K at slot zero, the twelveAt depth) and the reading-class
evidence.

`_build/lj-1.35-report.md` and `src/ProbeLJ135.agda`, whole. Took the
leaf environment `v' ∷ c' ∷ x ∷ δ` and the `keyArityBnd` restatement
shape.

`_build/lj-1.34-review.md` and `src/ProbeDD25D5.agda`, whole. Took the
one surviving premise `Δ₀ (DefBody (suc zero))` and the D5 generic-layer
shape.

`src/ProbeDD25D2.agda`, whole. Took the `StoryBB.Δ₀-clause` certificate
shape and the `extAtB` definition.

`_build/lj-1.33-review.md`, whole. Took the amortization evidence (0.08
seconds per clause) and the layer's generic shape.

`_build/lj-1.2-gate.md`, whole. Took the twelve-clause note and the
corrected 5,047-line citation at `:126-128`.

`archive/rud-route/src/L/Condensation.lagda.md`, whole, for SHAPE only.
Its story is parameter-free and structurally witnessed; no price was
taken from it, since its target is classically false (`[LJ-1.11]`).

`dev/LESSONS.md` is not archived and binds. P-l, P-m, P-n, P-t, P-u,
P-v, P-h, R-35, R-38, R-40, I-5, C-12, C-22, C-31, C-32, C-33, C-34
and D-10 were read through `scripts/rules.py --for build`. P-v decided
the machine's spelling throughout. P-u held: no placement.

## 12. WHAT I AM NOT SURE OF

1. The story's twelve rows mirror the machine's row shapes, but the
   machine's atom row reads its second term from the value slot (`yc`),
   not the term slot (`b`), in its private body. The story's atom rows
   read the term slot. If the machine's reading is a real defect, the
   leg-D agreement for the atom rows must fix or re-derive the machine's
   row; if it is a convention I misread, the agreement is definitional.
   I could not unfold the private body to settle it.
2. The description's adequacy (the bounded leaves against the machine's
   leaves under the site facts) is not built here. The certificate is
   delivered; the satisfaction-level agreement is the next block's leg-D
   work.
3. The per-clause marginal figures come from the cold profile, not from
   incremental re-checks with rows removed. The profile attributes time
   per definition; the shared where-clauses of the atom and
   bounded-quantifier bodies are counted once.
4. Cold discipline: dependencies were warm through
   `_build/2.8.0/agda/src/`; only the master's own interface was cold.
   That matches the lineage protocol.
5. The `Exist` row at the graph layout is a re-statement of block 1's
   clause with K as a parameter. Block 1's delivered `Clause` stays
   untouched; the two formulas are the same content at two layouts, but
   nothing in the master proves they are definitionally the same
   formula across the K shift.

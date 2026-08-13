# LJ-1.6 report: cardinality of a stage

Status: COMPLETE with a stop. Two masters delivered and typechecked; the
carrier-level assembly refused with both prices. No commit was made.

## 1. THE VERDICT

DELIVERED: the counting half, in two new masters under `src/L/`.

- `src/L/Count.lagda.md` (620 in-fence lines): the tower-agnostic formula
  count, `Formula K 1` injecting into the arity-indexed union of shapes,
  codes and constant tuples, generic in the constant domain `K`.
- `src/L/StageCardinal.lagda.md` (174 in-fence lines): the counting bound,
  `Formula K 1 ↪ ⟪ β ⟫` at an infinite ordinal `β` under an injection
  `K ↪ ⟪ β ⟫` and the square law at `β`, plus the lower half of the level
  size, `⟪ α ⟫ ↪ ⟪ Lset α ⟫` for every ordinal `α`.

REFUSED: the row's carrier-level statement, |Lset α| = |α| for infinite α.
The build found the plan rested on a bad premise. The carrier of a stage is
not the union index. In this hierarchy a `sett`'s carrier is the quotient
of its index by the kernel of the embedding (`sett-repr`, `Rep = X /
Kernel`, in the hierarchy properties). So `⟪ Lset α ⟫` is a quotient of
`Σ[ β ∈ α ] Formula ⟪ Lset β ⟫ 1`. Two formulas can name the same
definable set. The counting bound does not factor through that quotient.
The upper half therefore needs a canonical-name descent. The archive never
faced this. It bounded the hull's index, never its carrier. The level-size
theorem was never delivered on the retired route. Both prices for the full
statement are in section 2.

## 2. THE TWO PRICES (port against fresh write)

These prices were written before the build. Both priced the row's statement
as a theorem of the form: for every infinite α, two injections between
`⟪ Lset α ⟫` and `⟪ α ⟫`. Both left the square law standing as a module
parameter, priced separately.

Port price: `L.Count` at about 620 in-fence lines (the archived `FOL.Count`
at 588 plus `composed-count` at about 30), plus `L.StageCardinal` at about
500 to 650 (the archived `CardinalCount.Bound` at 166 plus the level-size
assembly at about 350 to 450). Total about 1,120 to 1,270.

Fresh-write price: the count re-derived at about 560 to 700, plus the same
assembly at about 500 to 650. Total about 1,060 to 1,350.

The port was cheaper on both prices: the count's arithmetic is verified
content, and a re-write spends the same lines with authoring risk. The
precedent of LJ-1.3 and LJ-1.4 holds.

THE BUILD REVISED THE PRICE. The union carrier of a stage is a quotient,
not the index Σ, and the bound does not factor through it. The corrected
full price is the delivered 794 lines, plus the square law (port about
1,540 in-fence: `SquareLaw` at 907 plus its `Pairing` dependency at 633;
fresh about 1,400 to 1,700), plus the canonical-name descent at about 250
to 450 (the least-β and a least defining formula through the delivered
well-order of a stage), plus the transfinite assembly at about 200 to 350.
Corrected totals: port about 2,784 to 3,134, fresh about 2,644 to 3,274,
in four to five masters. The square law's DD24 risk is measured. It ran 856
seconds cold on the comparable tree. It ran 61.9 seconds after a
thirteenfold cut. That is a rate of 0.068 to 0.94 seconds per line against
the 0.013193 bar. It is the archive's own separate row.

## 3. THE ARCHIVE SURVEY

`archive/rud-route/src/FOL/Count.lagda.md` (588 in-fence): PORTABLE. Pure
syntax counting over the delivered `FOL.Manipulation.Parameters`; nothing
L-specific in any type. Ported as `L.Count` with re-pointed imports. The
one split DD4 asked to find: the archived statements are generic in the
constant domain, and so are the proofs.

`archive/rud-route/src/L/CardinalCount.lagda.md` (166): PORTABLE WITH
CHANGE. The `Bound` module is generic in the constant domain and the target
ordinal, conditional on the pairing at the target. Its shape is ported into
`L.StageCardinal.Bound`; the change is the numeral source, derived from
`β ∉ ω` by trichotomy instead of from a `ω ∈ˢ β` hypothesis, so that the
bound serves the ω base as well. The hull-specific `AtHull` is not needed
by the level size.

`archive/rud-route/src/L/Cardinal.lagda.md` (299): PORTABLE WITH CHANGE,
not ported in this row. CSB, Cantor and the 5.4 equality half are 5.4
content, not 1.1(vii) content.

`archive/rud-route/src/L/CardinalPredicates.lagda.md` (399): PORTABLE WITH
CHANGE, not ported in this row. The internal predicates `HostBij` and
`HostEq` are the bijection form; the carrier-level injections come first.

None of the four modules proves |L_α| = |α|. The archive stopped at the
hull bound on the hull's index; the level-size assembly is fresh content,
and its load-bearing premise, the union carrier, is a quotient.

## 4. THE STATEMENT

The row states |L α| = |α| for infinite α, and the digest (section 5.2)
confirms the chain consumes exactly this at 5.5 and 5.6. The row's
statement is therefore the right target; no correction of the statement is
owed. What is corrected is the price: the statement at the CARRIER level is
not the index-level counting the archive delivered.

Delivered instead, in the honest injection shape:

1. The formula count: for every type `K`, `Formula K 1` injects into
   `Σ[ k ] (Formula ⊥* k × (ℕ × Vec K k))`. This is |ℒ_K| = max(|K|, ω)
   with no choice: a formula is a shape plus a tuple.
2. The counting bound: for every infinite ordinal `β` with the square law,
   and every injection `K ↪ ⟪ β ⟫`, `Formula K 1` injects into `⟪ β ⟫`.
   This is the successor-step bound and 5.4's upper half.
3. The lower half: `⟪ α ⟫ ↪ ⟪ Lset α ⟫` for every ordinal `α`, from the
   delivered stage-index theorem that the ordinals of a stage are exactly
   the members of its index.

What |L α| = |α| needs that 5.4 does not: the square law at every infinite
ordinal (5.4's bound is parameterized by it and never proves it), and the
canonical-name descent (the carrier is a quotient of the names, and the
size of a quotient needs a representative choice, here the least-β and a
least defining formula through the delivered well-order of a stage).
5.4's hull never needed the descent because its bound was stated on the
hull's index.

## 5. THE NUMBER

794 in-fence lines, ledger caliber (non-blank lines inside ```agda
fences): `src/L/Count.lagda.md` at 620, `src/L/StageCardinal.lagda.md` at
174. The ledger tool itself reads HEAD and the files are uncommitted, so
the count is the ledger algorithm applied to the working tree. The two
catalogs are excluded by DD26; neither file is a catalog.

## 6. SECONDS AND RATE

Cold per file, one process, `GHCRTS="-A64m -I0 -M8g"`, dependency
interfaces cached, three runs each. Under 0.5 s or under 5 percent is flat
by the noise rule.

`src/L/Count.lagda.md`: 0.69, 0.66, 0.63 seconds. Median about 0.66. Rate
0.0011 seconds per line. `src/L/StageCardinal.lagda.md`: 0.87, 0.90, 0.92
seconds. Median about 0.90. Rate 0.0052 seconds per line.

Both are inside the DD24 bar of 0.013193, below P-m's parameterized band.
The count is pure structural recursion and arithmetic with no satisfaction
content; its cheapness is the finding, not the absence of work.

## 7. WHAT THE J TOWER WOULD SUPPLY

`L.Count` instantiates unchanged at the J parameter domain: its only
parameter is the constant domain `K : Type ℓ`. `L.StageCardinal.Bound` is
generic in `K` and the target ordinal `β`; the J tower supplies its own
carriers, its square law at its ordinal carriers, and its stage-index
facts. The quotient descent is shared content if the J levels are `sett`-based,
and absent if the J presentation is index-native. The level-size statement
itself is Def-specific: the digest records the J analogue as |J_ρ^A| =
H_ρ^M (SZ 1.27), a different counting.

## 8. LITERATURE USED

`dev/literature/devlin-II5.md` sections 1.4 and 1.5: 5.4's one-line proof
and the 5.5 to 5.6 chain that consumes |L_α| = |α|. Section 5.2: II.1.1(vii)
as the counting half of 5.5 and 5.6. Took: the statement the chain consumes
and the counting shape. `_build/literature/dev2.txt:1357-1360` for 5.4 and
`dev2.txt:200-240` for 1.1(vii)'s proof: |Def(L_α)| ≤ |ℒ_{L_α}|, whose
type-theoretic form is the quotient descent named in section 4.
`dev/literature/j-hierarchy.md` section 4: the J analogue, why the J side
differs. Skipped with a reason: `devlin-II5.md` sections 6.5 and 6.6, the
two UNRESOLVED OCR items, do not touch the counting statement. 6.5 is
5.2's transfer subscripts in the condensation proof; 6.6 is 2.2's
definability matrix. Neither is the counting.

## 9. ARCHIVE USED

`archive/rud-route/src/FOL/Count.lagda.md` lines 43 to 917: ported as
`src/L/Count.lagda.md` code verbatim, with re-pointed imports. The pairing
at line 81, the code and `code-inj` at 145 to 301, the `Count` module at
338, the round trip at 480 to 810, and the erase boundary at 810 to 870.
`archive/rud-route/src/L/CardinalCount.lagda.md` lines 71 to 220: the
`Bound` module ported into `L.StageCardinal.Bound`, with the numeral source
changed from `ω ∈ˢ β` to the trichotomy against `ω`.
`archive/rud-route/src/L/Cardinal.lagda.md` and
`archive/rud-route/src/L/CardinalPredicates.lagda.md`: read and surveyed,
not ported (section 3).
`_build/lj-1.1-recon.md` lines 137 to 147 and 239 to 253: the PORTABLE and
ADAPTABLE verdicts and the square-law block 4d with its measured 856
seconds. `_build/lj-1.3-report.md` section 5 and `_build/lj-1.4-report.md`
section 5: the measurement convention, cached dependencies with the
module's own elaboration cold. `dev/LESSONS.md` through
`scripts/rules.py --for build`: P-h, P-l, P-m, P-k, R-35, R-38, R-40, I-5,
C-12, C-22, D-10.

## 10. WHAT I AM NOT SURE OF

1. The canonical-name descent is priced at 250 to 450 lines from the
   delivered well-order of a stage, but the well-order machinery is heavy
   and a probe should re-price it at its own site before funding.
2. The chain (LJ-1.7) may be able to consume the index-level counting
   bound instead of the carrier-level statement, which would remove the
   descent from the critical path. That is the corrected target question
   the orchestrator should settle before funding the descent.
3. The seconds figures use cached dependency interfaces. A quiet-machine
   audit should re-measure both files cold.
4. The placement of the count under `src/L/` follows the brief's write
   scope; its natural home is `src/FOL/`, and the J tower consumes it
   unchanged either way.

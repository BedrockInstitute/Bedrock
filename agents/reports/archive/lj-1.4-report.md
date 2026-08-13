# LJ-1.4 report: the Mostowski collapse

Status: COMPLETE. The chapter typechecks. No commit was made.

## 1. WHAT LANDED

The deliverable is `src/V/Collapse.lagda.md`. The collapse module
`Collapse` (line 31) takes the carrier `X` as a module parameter. The
chapter delivers these statements:

- `isTrans` (line 25) is the transitivity predicate on a set.
- `π` (line 43) is the collapse by membership recursion. `π-compute`
  (line 47) is its computation law.
- `πX` (line 66) is the range as a set. `πX-trans` (line 80) proves
  the range is transitive.
- `π∈-fwd` (line 93) proves membership forward.
- `π-inj` (line 157) proves the collapse is one-to-one on the carrier.
  The carrier transitivity is a module parameter in `Inj` (line 109).
- `π∈-bwd` (line 175) and `iso` (line 192) prove membership backward
  and the iso reading.
- `Mostowski` (line 198) and `mostowski` (line 204) package the
  statement.
- `unique` (line 208) proves the recursion equation has a unique
  solution.
- `fixes` (line 230) proves the transitive-fixing clause. `fixes-X`
  (line 272) is the carrier-level form.

## 2. PORT OR FRESH WRITE (DD13)

I chose the port. The archive is
`archive/rud-route/src/V/Collapse.lagda.md` at 181 in-fence lines. The
port price is 181 lines plus the fixing clause. The delivered chapter
measures 239 lines. The fresh write price is the same content re-derived
at 230 to 330 lines. The port is cheaper, because the content is
verified and generic. A fresh write spends the same lines and adds
authoring risk. I checked the port line by line against the archive. The
only changes are one added import, one cosmetic name, and the fixing
clause.

## 3. GENERIC OR FIXED (DD4)

Everything stays generic. The carrier `X` is a module parameter, per
P-h. The fixing clause is stated at generic `Y` and `X`. Nothing is
fixed to a concrete carrier. The chapter shares the delivered generic
machinery and adds no fixed copy. This serves the GCH wing and the later
two-tower route.

## 4. THE TRANSITIVE-FIXING CLAUSE

Delivered. `fixes` (line 230) states: for `Y ⊆ X` transitive, `π y ≡ y`
for every `y ∈ᵗ Y`. The proof is one membership induction. The two
inclusion directions make the recursion step equal to the identity
step. The clause is true at this generality, so D-10 passes. The clause
costs 58 in-fence lines, including its comments and `fixes-X`. This
matches the survey band of 50 to 150 lines. No stop was needed.

## 5. THE MEASUREMENT

The chapter has 239 non-blank in-fence lines. I measured with the
ledger counting algorithm on the working tree. The ledger tool itself
reads HEAD, and the chapter is not committed. The typecheck returned
exit code 0. The first check used one process under
`GHCRTS="-A64m -I0 -M8g"`. The wall time was 1.906 seconds. The
dependency interfaces were cached. The module's own elaboration was
cold. The ratio is 1.906 divided by 239, about 0.00798 seconds per
line. The tree baseline is 0.007693 (`dev/ledger.toml` line 2438). The
chapter sits inside the DD24 tolerance of 1.15 times the baseline.

## 6. ARCHIVE USED

`archive/rud-route/src/V/Collapse.lagda.md`, 181 in-fence lines. Took:
the full collapse code verbatim. The `Collapse` module is at line 74.
The opaque seal is at lines 99 to 103. The range lemmas are at line
162. The injectivity module is at line 227. The uniqueness proof is at
line 369. Rejected: the prose, because DD23 freezes mathematical prose.
The archive has no fixing clause, which is the gap this chapter closes.

`_build/lj-1.1-recon.md`. Took: Block 2 at line 103 and the PORTABLE
verdict at line 239. The recon prices the generic shape at 181 to 357
lines.

`archive/dev/TASKS-archived.md`. Took: T39 at line 74 and T91 at line
126. They record the delivered status and the gap.

`_build/l3.32-t91-report.md`. Took: section 1.4 at lines 112 to 126.
It records the missing transitive-fixing clause and prices it at 50 to
150 lines.

`dev/LESSONS.md`. Took: P-h at line 174, P-l at 2099, P-m at 2254,
R-36 at 794, D-10 at 1302, and C-25 at 2659. They bind the module
parameter, the check-rate class, the seal, and the truth check.

## 7. WHAT I AM NOT SURE OF

1. The seconds figure uses cached dependencies. The tree baseline is a
   whole-tree cold check. The scheduled cold run should re-measure the
   chapter.
2. The clause states `Y ⊆ X` with the small membership. A consumer may
   want the large-membership form. The transport between the forms is
   one `∈∈ₛ` step.
3. The condensation chapter may need a different statement shape. The
   current shape matches Devlin 5.2(ii).

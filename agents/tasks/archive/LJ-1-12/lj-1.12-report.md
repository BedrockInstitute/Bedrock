# LJ-1.12 report: the crossing re-targeted and priced

Status: COMPLETE. Read-only. No Agda run. No commit. No push. Written
incrementally per C-22. The report uses ASD-STE100.

## 1. THE RECOMMENDATION

**Take Route A at 3.3 thousand naive non-blank in-fence lines.** The price
re-bases `[LJ-1.10]`'s substrate band against the Sigma-1 target, and it adds
the carrier facts the digest requires. Route C is the same deep layer in
Devlin's shape at 3.2 thousand lines. The two prices differ by less than the
survey error. Route B costs 2.8 thousand lines if its commutation target is
true, and its truth is unprobed. A one-clause probe gates all three. Section 6
states the probe.

## 2. THE THREE PRICES

### 2.1 Route A: the bounded substrate over the delivered description

Price: 3.3 thousand naive non-blank in-fence lines. Band: 2.0 to 4.5
thousand. Basis: the survey band of `[LJ-1.10]` section 2.3, re-based to the
Sigma-1 target, plus two new terms. The Sigma-1 target does not shrink the
substrate. The matrix of the Sigma-1 form is Delta-0, so every quantifier
inside it must stay bounded. The bound changes where the existentials live,
not how many clauses the matrix contains.

The component table, with the measured and the estimated split:

| component | band | class |
|---|---:|---|
| bounded code-set description and adequacy | 0.2-0.5k | ESTIMATED |
| bounded twelve-clause table and adequacy | 0.7-1.6k | ESTIMATED |
| bounded step, approximation, graph and the Sigma-1 stack | 0.3-0.6k | MEASURED floor |
| equivalence against the delivered machine | 0.3-0.8k | ESTIMATED |
| transport certificate | 0.15-0.30k | ESTIMATED |
| carrier facts: the sequence and the bound inside the carrier | 0.15-0.45k | ESTIMATED |
| satisfaction iso-invariance under the collapse | 0.08-0.14k | ESTIMATED |
| limit case | 0.124k | MEASURED |

The measured floor comes from the `[LJ-1.2]` probe. The top-level clause
rewrites cost 10 to 11 lines each, and the step formula costs 23
(`_build/lj-1.2-gate.md:27-45`). The delivered cone sizes are re-verified on
today's tree (`_build/lj-1.10-reprice.md:54-67`). The limit case is measured
at 124 lines (`_build/l3.32-t261-report.md:32-47`).

The estimated layer is the twelve-clause table decode. That is the widest
unmeasured term. The archive decode rate near 40 lines per clause is the
anchor (`_build/lj-1.10-reprice.md:80-84`). The equivalence legs and the
carrier facts are surveys.

### 2.2 Route C: the fresh K(u)-shaped description

Price: 3.2 thousand naive non-blank in-fence lines. Band: 2.0 to 4.5
thousand. Basis: the same substrate as Route A, organized in Devlin's shape,
with the delivered-description equivalence replaced by the fresh formula's
own adequacy.

| component | band | class |
|---|---:|---|
| bounded code-set description and adequacy | 0.2-0.5k | ESTIMATED |
| bounded twelve-clause table and adequacy | 0.7-1.6k | ESTIMATED |
| bounded step and the Sigma-1 stack | 0.3-0.6k | MEASURED floor |
| the level-hood wrapper in the sequence shape | 0.1-0.25k | ESTIMATED |
| the fresh formula's adequacy against the tower | 0.3-0.8k | ESTIMATED |
| carrier facts: the sequence and the bound inside the carrier | 0.15-0.45k | ESTIMATED |
| satisfaction iso-invariance under the collapse | 0.08-0.14k | ESTIMATED |
| limit case | 0.124k | MEASURED |

Route C is Route A with one change. The fresh formula stands at variable
slots, so it carries no constants and no transport certificate. It pays a
fresh adequacy leg instead. The two deltas nearly cancel. The center moves by
0.1 thousand, which is inside the survey error.

### 2.3 Route B: the pi-commutation route

Price: 2.8 thousand naive non-blank in-fence lines. Band: 1.8 to 4.0
thousand. Basis: the Def-step substrate, the commutation machinery, and the
ordinal induction. This route does not escape the bounded substrate. The
successor step transfers the object-language statement "d = Def(w)" down to
the hull, and that statement needs the bounded Def-step description. The
route relocates the graph-level wrapper into the commutation lemmas.

| component | band | class |
|---|---:|---|
| bounded Def-step substrate: code set, table, step | 1.05-2.4k | ESTIMATED |
| satisfaction iso-invariance under the collapse | 0.08-0.14k | ESTIMATED |
| code-fixing under pi | 0.15-0.4k | ESTIMATED |
| Def-commutation under pi | 0.2-0.5k | ESTIMATED |
| the ordinal induction along the collapse | 0.15-0.4k | ESTIMATED |
| limit case | 0.124k | MEASURED |

The whole price is a survey except the limit case. The route carries a
truth question that no route A or C carries. Section 10 states it.

## 3. THE SHARED-TEMPLATE SPLIT

`[LJ-0.7]` section 4 is the spine. The condensation template 5.1 to 5.6 is
shared. The per-tower content is exactly two objects: the level-hood
certificate and the definable well-order. The well-order is delivered
(`orderAt`, `src/L/Choice/Step.lagda.md:740`, and the order atom in
`src/L/Hull.lagda.md:374`). The level-hood certificate is this task's
crossing.

The shared template around the crossing is booked and delivered. The hull is
372 non-blank in-fence lines (`src/L/Hull.lagda.md`). The collapse is 335
lines with the extensional carrier (`src/V/Collapse.lagda.md:220`). The
Tarski-Vaught equivalence holds at any carrier (`src/L/Hull.lagda.md:73`).
The counting and cardinal chains are booked at 2,935 to 3,950 lines. The
condensation core and the reduction are booked at 514 to 600 lines. The limit
case costs 124 measured lines. The substitution bridge costs 210 to 430
lines.

The crossing itself splits per route as follows:

| route | crossing | shared part | Def-only part |
|---|---:|---:|---:|
| A | 3.3k | 0.4k | 2.9k |
| C | 3.2k | 0.3k | 2.9k |
| B | 2.8k | 0.3k | 2.5k |

The shared part is the transfer legs, the limit case, and the transport
machinery at the certified form. The Def-only part is the substrate, the
adequacy, and the carrier facts. No route puts the crossing's core into the
template. D-26 makes the certificate per-tower content: the Def tower's
certificate is satisfaction-based, and the J tower's is structural. That is
the same verdict as `[LJ-1.11]` DEV-6.

What the J tower gets free is the technique, not the lines. The bounded
rewrite with a Sigma-1 witness is the shape the J-side op-clauses reuse. The
J-side bounded layer is priced at 470 to 610 lines plus sixteen unmeasured
op-clauses (`_build/l3.32-t84-report.md:30-31`,
`_build/l3.32-t263-fof.md`). The asymmetry is real and its magnitude is
about two to three times, not one order.

## 4. THE CONTENT CLASS AND THE DD24 RISK

The DD24 bar for the wing is 0.013193 seconds per line at the module
caliber. The wing today measures 0.0065 aggregate, which is 0.57 times the AC
side. P-m measures the two content classes: parameterized work runs at
0.010 to 0.013 seconds per line, and instantiation work runs at 0.22 to
0.297.

All three routes can land in the parameterized class. The substrate is a
formula at variable slots with a variable carrier, exactly like the delivered
cone. The cone's own measurement is the precedent: a reading at variable
slots cost 15 milliseconds, and the same reading against an alias cost 98
seconds (`src/L/Coding/Sequence.lagda.md`). The rule is to instantiate once.

The risk is the decode and adequacy legs. A decode stated at a concrete
carrier walks the satisfaction relation, which is P-n's instantiation floor.
At 0.22 seconds per line, the crossing costs about 730 seconds and blows the
bar about 17 times. At 0.013, it costs about 43 seconds and passes. The class
is the risk, not the lines.

Route B adds the worst leg. The commutation and the iso-invariance walk the
satisfaction relation by their nature. T51 calibrated the iso-invariance leg
at 0.24 to 0.42 thousand lines, which is the x3 class. Route B's DD24 risk is
higher per line than Route A's.

## 5. DOES THE ROUTE NEED THE SUBSTITUTION BRIDGE

Yes. All three routes need it. The hull's elementarity at hull parameters
feeds the Sigma-1 transfer of the level statement. The ordinals gamma and the
bound w are hull parameters, not X parameters. `hull-closed` gives the
criterion at X parameters only (`src/L/Hull.lagda.md:350`).

The bridge is the leastness encoding plus the two Devlin 5.3 consequences.
It is priced at 210 to 430 lines (`_build/lj-1.3-report.md:114-131`), and
`[LJ-1.14]` named it unprompted. It is template content: the J tower's
condensation consumes the same hull elementarity. It is not part of the
crossing prices above. It is booked as the block-1 residue.

## 6. THE PROBE

One probe gates all three routes. It prices the widest unmeasured term: the
bounded table clause at the Sigma-1 shape, with its two-way decode at a
variable carrier.

Statement 1: write the existential clause of the satisfaction table as a
Delta-0 matrix with the bound as a free variable, stack the Sigma-1
certificate, and prove the two-way decode at a variable carrier. The
existential clause is the hardest. Its witness existential is unbounded in
the delivered form.

Statement 2: prove the carrier fact. For delta below alpha at a limit alpha,
the level sequence `hierL (Lset delta)` and the chosen bound live in
`Lset alpha`. The bound must contain the codes over the carrier and the table
values.

GO: statement 1 closes at or below 40 lines, and statement 2 closes at or
below 100 lines. Then the deep layer moves from survey to measured. Route A
re-prices at the measured rate times twelve clauses plus the fixed legs.

NO-GO: the existential clause's matrix cannot decode without a new carrier
fact, or the bound cannot be placed in the carrier with the delivered closure
lemmas. Then the crossing re-prices at the substrate's full band, and
`[LJ-1.5]` stops for a re-price (DD8).

Cost: one dispatch, about 150 to 250 probe lines, one Agda process at
`GHCRTS=-M8g`. The probe is never committed.

For Route B, a second probe precedes the first: the Def-commutation lemma at
one successor step. It asks whether `pi (Def w) = Def (pi w)` holds when w
belongs to the hull and w is not transitive-embedded. GO funds Route B. NO-GO
kills Route B and Route A stands.

## 7. WHAT THE RETIRED ROUTE PAID

The retired route paid three prices for this crossing.

First, the crossing transfers at 700 to 1,720 naive lines. That price is
dead. It priced the transfers of a false target. The structural story with
its `⊤̇` step recognizes no level, by the F1 counterexample
(`_build/lj-1.11-review.md` F1). The price does not transfer.

Second, the level-story substrate and assembly at 2,488 to 2,747 naive
lines. Part survives. The six structural clauses and their Delta-0 witnesses
are the shape of the bounded matrix's structural part. The `⊤̇` assembly is
dead.

Third, the crossing-rebuild at 5,047 measured lines. That figure prices the
internalization machine rebuilt fresh (`dev/ledger.toml:824-856`). The
machine is delivered on today's tree. The price does not transfer. Adding it
to the current tree double-counts delivered content.

What transfers is the reduction. The crossing assembles from one
absoluteness obligation at the two carriers, by `ambientOnly-from` and
`crossOut-from` (`_build/l3.32-t51-report.md:52-55`). The limit case
transfers at 124 measured lines. The T130 warning transfers: the crossing
must carry the internalized definable-powerset step
(`_build/l3.32-t130-report.md:26-33`). The substrate is that step, priced.

## 8. LITERATURE USED

Read in full: `dev/literature/devlin-II5.md`. Took: section 2.3, the strength
requirements, the K(u) bound, the witness-inside-the-carrier clause; section
3, the engine list; section 4, the shared-template verdict and the two
per-tower objects; section 6, the two UNRESOLVED OCR items; section 7, the
errata scoping; section 8, the retired-route conclusions.

Read in full: `dev/literature/j-hierarchy.md`. Took: SZ 1.16 condensation,
SZ 1.10, the syntax-free S-step certificate, and the well-order. This is the
J-side comparison for section 3.

Read in full: `_build/literature/dev2.txt` at the cited lines. I verified
the two load-bearing citations myself. The K(u) bound is at
`dev2.txt:593-630`. The Sigma-1 level formula `H(x, alpha)` is at
`dev2.txt:679-686`. I also read 5.2's proof at `dev2.txt:1148-1319` and 5.3's
least-witness mechanism at `dev2.txt:1329-1356`.

The two UNRESOLVED OCR items are the carrier subscripts in 5.2's lines (c)
and (j) (`dev2.txt:1200-1203`, `dev2.txt:1245-1248`), and the displayed
matrix of 2.2's `A(v, u)` (`dev2.txt:563-590`). Neither carries a load-bearing
claim in this report.

Read: `dev/literature/digest.md` sections 1 to 5. Took: the SZ engine, the
errata scoping, and the D-26 reading of the definable power.

NOT read: `dev/literature/devlin-errata.md` in full. WHY NOT: the binding
content, the Sat failure and the internalized-layer scope, is quoted with its
citations in `devlin-II5.md` section 7 and `digest.md` section 5. This task
prices content. It does not audit the errata inventory.

NOT read: `primary-sources.md`, `BIBLIOGRAPHY.md`, `fine-structure.md`,
`rudimentary-functions.md`, `formalizations-landscape.md`, `geology.md`,
`owner-notes-rud.md`. WHY NOT: none carries content that prices the crossing.
The fetch map and the OCR caveats are summarized in `devlin-II5.md`'s header.

## 9. ARCHIVE USED

- `archive/rud-route/src/L/Condensation.lagda.md`: read the story at
  `:585-604`, the witnesses at `:768-852`, the D32 deletion and recap at
  `:857-885`. Took: what the retired crossing paid and why it is dead.
- `archive/dev/TASKS-archived.md`: rows T84 at `:119`, T130 at `:165`, T257
  at `:262`, T259 at `:266`, T263 at `:268`. Took: the retired price, the
  internalized-step warning, and the J-side comparison.
- `archive/dev/JOURNAL-archived.md`: T5 at `:1022`, T48 at `:1756-1760`.
  Took: the route decomposition survives, and 5.5 consumes condensation
  parts (i) and (ii) only.
- `archive/dev/DECISIONS-archived.md`: D31 and D32 at `:51-52`. Took: the
  deferral of the crossing.
- `_build/lj-1.2-gate.md`: sections 2, 3, and 5. Took: the NO-GO, the two
  missing facts, and the measured clause rates.
- `_build/lj-1.10-reprice.md`: sections 2, 5, 6, and 7. Took: the substrate
  band, the wing arithmetic, and the DD4 scoring.
- `_build/lj-1.11-review.md`: F1, F2, F3, and F4. Took: the false target,
  the pi-commutation alternative, and the J-side magnitude.
- `_build/lj-1.1-recon.md`: the block plan and the 8.0 to 10.8 thousand
  projection. Took: the crossing's place in the wing.
- `_build/lj-1.3-report.md` and `_build/lj-1.4-report.md`: the delivered
  hull and collapse, and the three standing pieces at 210 to 430 lines.
- `_build/l3.32-t51-report.md`: the four transfer obligations and the
  iso-invariance band. Took: the Levy content relocates.
- `_build/l3.32-t84-report.md`, `_build/l3.32-t130-report.md`,
  `_build/l3.32-t263-fof.md`: the J-side bounded layer, the warning, and the
  sixteen op-clauses.
- `_build/l3.32-t261-report.md`: the limit case at 124 measured lines.
- `dev/LESSONS.md`: D-10 at `:1302-1361`, D-26 at `:1662-1687`, P-m at
  `:2419`, P-n at `:2442`, P-l at `:2099-2158`, C-22 at `:2031`.

## 10. WHAT I AM NOT SURE OF

1. The deep layer's price. The bounded table decode is a survey, not a
   measurement. Its band of 0.7 to 1.6 thousand lines is the widest term in
   every route. The probe in section 6 is the only cure.
2. Route B's truth. The commutation `pi (Def w) = Def (pi w)` is unprobed at
   the hull's generality. The carrier w is not transitive-embedded, and the
   satisfaction iso-invariance may need witnesses outside the hull. This is a
   D-10 question, and it decides Route B before any price does.
3. The carrier facts. Whether `hierL (Lset delta)` and the bound can be
   placed in `Lset alpha` with the delivered closure lemmas is unmeasured.
   The rank analysis of the internal hierarchy could be heavier than the
   survey band. It could land in the instantiation class.
4. The Sigma-1 certificate shape. The project's `Sigma-1` stacks existentials
   over a Delta-0 core (`src/FOL/LevyHierarchy.lagda.md:73-75`). The matrix
   still needs every universal bounded by the K(u)-style witness. Whether the
   delivered bounded quantifiers over a variable bound close cleanly is
   unmeasured.
5. The wing re-baseline. The crossing replaces the dead sub-blocks 3a, 3c,
   and 3d. The derived wing band is roughly 7.2 to 11.0 thousand lines with a
   center near 9.1 thousand. That arithmetic is derived, not measured.
   `[LJ-1.9]` audits it.
6. Whether Route C's fresh adequacy leg is cheaper or more expensive than
   Route A's delivered-machine equivalence. The two centers sit inside the
   survey error either way.

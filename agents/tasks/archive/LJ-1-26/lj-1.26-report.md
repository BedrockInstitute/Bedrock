# LJ-1.26 report: gate LJ-1.5 by pricing condensation in seconds

Status: COMPLETE. Read-only. No Agda run. No commit. No push. Written
incrementally per C-22. The report uses ASD-STE100.

## 1. THE VERDICT

Condensation at route A costs about 60 seconds at the 3.3k line center.
The basis is a mixed-class split of the crossing. The parameterized
majority runs at 0.005 to 0.013 seconds per line. The concrete-carrier
minority runs at the cured transport rate. The archive's 0.395 rate does
not transfer. The probe in section 7 decides the split.

MEASURED: the hull at 0.0039 seconds per line
(`_build/lj-1.23-report.md:6-7`, `:128-134`). The
variable-slot clause decode at 0.0052 (`_build/lj-1.15-report.md:82-83`).
The transport cure at 0.019 (`_build/lj-1.24-report.md:38-43`). The floor
class at 0.22 to 0.297 (`_build/lj-1.16-review.md:22`; P-m at
`dev/LESSONS.md:2460`, P-n at `:2483`).

ESTIMATED: the crossing at 60 seconds. About 2.5k of the 3.3k lines run in
the parameterized class at 0.010. About 0.8k lines state formulas at the
concrete carriers. They run at 0.05 after the [LJ-1.24] cure. The number
is one best-effort figure with its basis named (DD8).

The two ends frame the decision. At the measured cheap rates the crossing
costs 13 to 17 seconds. At the floor class it costs 700 to 1,300 seconds.
The wing's whole seconds budget is 99.6 to 147.7
(`dev/ledger.toml:305`). The gate verdict: route A is fundable only if the
floor legs stay cured. The probe measures that condition.

## 2. DOES THE ARCHIVED 0.395 RATE TRANSFER?

No. The rate does not transfer as a price. It transfers only as a warning
about the floor class.

The rate was measured on the retired route's module. The module ran 514
non-blank in-fence lines at 203.3 seconds (`dev/LESSONS.md:2334`). The
module served the rud route. Its target is classically false. [LJ-1.11]
found that the trivial Def-step story recognizes no level
(`_build/lj-1.11-review.md`, F1). A price for false content cannot price
true content.

The rate's content class is the built-tree decode family. The module
spends 333 of its 514 lines on the structural predicates and the level
story formula with two-way decodes (fences at
`archive/rud-route/src/L/Condensation.lagda.md:330-470` and `:486-742`).
That content is P-n's floor: satisfaction of a built formula at a concrete
carrier (`dev/LESSONS.md:2483-2500`). P-t explains the cost: the
satisfaction recursion unfolds the built formula tree at every use
(`dev/LESSONS.md:2601-2630`).

The rate also includes a body-bound defect. `ambientOnly-from` cost 128.5
seconds. Gutting it moved 131.1 seconds into the lemma it called. The
total did not change (`dev/LESSONS.md:2364`). That defect inflated the
rate above the floor band. The floor band is 0.22 to 0.297. The module ran
at 0.395.

The new route's content differs in three ways. The description is the
delivered `LsetGraphAt`, not the archived structural story. The hull's
index is the term algebra `Code`, not formula-witness pairs. The bounded
substrate at variable slots measured 0.0052, forty times below the
archive's rate (`_build/lj-1.15-report.md:82-91`).

The formal cost buys what the book gets free. Devlin writes the level
formula once and asserts absoluteness. The formal proof must write the
object-language story at two carriers, prove its two-way decodes, and
prove the equivalence against the delivered machine. That difference is
the price this report estimates.

What transfers is the class test. The concrete-carrier decode is the
expensive class. [LJ-1.12] priced that risk at 730 seconds for the whole
crossing (`_build/lj-1.12-report.md:151`). The probe must re-measure
that class at this site. P-l forbids transferring even a measured rate by
analogy (`dev/LESSONS.md:2305-2330`).

## 3. BODY-BOUND OR TRANSPORT: SAME DISEASE OR DIFFERENT?

Different. The test separates them in one run. Gut the body and watch
where the seconds go. A body-bound cost moves to the called lemma. The
total stays unchanged. A transport cost disappears when the statement
stops naming the transparent construction (`dev/LESSONS.md:2368-2383`).

The archived condensation was body-bound. `ambientOnly-from` cost 128.5
seconds. The gutted body cost 0 milliseconds. The called lemma then cost
131.1 seconds. The total did not change (`dev/LESSONS.md:2364`). The
disease was a body that built a concrete application. The named cure is an
interface change. Restate the obligation so the concrete application is
not built (`dev/LESSONS.md:2365-2366`).

The [LJ-1.24] block was the transport class. The limit half named the
transparent `defSet (Lset ...)` in statement positions. Arm 1 abstracted
the source to a parameter `D`. The bodies stayed identical. The block fell
from 29.1 seconds to 2.3 seconds (`_build/lj-1.24-report.md:38-43`). The
work was removed, not moved. The report classifies it as R-38's class,
not P-n's floor (`_build/lj-1.24-report.md:50-59`).

The one sentence that matters: body-bound is a real obligation built at a
concrete argument, and its cost moves; the transport class is an
elaboration artifact named in a statement type, and its cost vanishes
when the name is abstracted. The two diseases need different cures. The
body-bound cure is an interface change. The transport cure is a statement
restatement at an abstract index.

Condensation carries both diseases. The recognition obligation is
intrinsic. The theorem states that the collapsed image is a level of the
real tower. Some concrete application cannot be avoided. The transport
statements are curable. The [LJ-1.24] cure has never been tried at
condensation's site. That is the third cure, and it is the one that can
actually remove work there.

The archive's two failed cures do not contradict this. The abstract
carrier discipline gave no movement because the carrier was not the cost
(`dev/LESSONS.md:2334`). The telescope lift made the module worse because
it was applied by resemblance, unmeasured (`dev/LESSONS.md:2337`). Both
were the wrong cure for the body-bound disease. The [LJ-1.24] cure
attacks the statement positions, which is the disease the archive's own
diagnosis named (`dev/LESSONS.md:2364`).

## 4. WHAT THE FOUR LANDINGS REMOVED

### 4.1 DD27, the hull re-index (`[LJ-1.23]`)

The hull's index is now the term algebra `Code`
(`src/L/Hull.lagda.md:58-91`). `hull-closed` gives the Tarski-Vaught
criterion at hull parameters (`src/L/Hull.lagda.md:415-426`). The old
statement took a formula over `⟪ X ⟫` and satisfied it at X parameters
(`_build/lj-1.23-report.md:13-22`). The new statement takes a formula
over `Code`.

The hull-side obstruction is gone. [LJ-1.16-R] found the obstruction was
the hull's index type, not the mathematics (`_build/lj-1.16-review.md:85-88`).
The term algebra needs only the meta well-order. Both towers have one
(`_build/lj-1.16-review.md:139-155`).

Piece one of the bridge residue is retired. The order element's stage
membership, priced at 30 to 80 lines, has no consumer
(`_build/lj-1.23-report.md:91-100`). The leastness encoding and the two
Devlin 5.3 consequences lose their reason. The block-1 residue was
booked at 210 to 430 lines (`_build/lj-1.3-report.md:114-131`,
`_build/lj-1.12-report.md:162-169`). The criterion at hull parameters
replaces its purpose.

What is left: the crossing's Sigma-1 transfer consumes elementarity at
hull parameters (`_build/lj-1.12-report.md:160-166`). The re-stated
`leastWit`, `Witnessed-small` and `hullVal` stand for the downstream
condensation API (`_build/lj-1.23-report.md:88`). The hull checks at
0.0039 seconds per line (`_build/lj-1.23-report.md:6-7`). That is
evidence that the parameterized class is reachable in this neighborhood.

### 4.2 The level size (`[LJ-1.21]`)

The upper half of `|Lset α| = |α|` is delivered at every infinite ordinal
(`src/L/StageCardinal.lagda.md:501-584`). The assembly needs `fin-inj`,
priced at 50 to 100 lines (`_build/lj-1.21-report.md:31-37`, `:216-218`).
The limit half measured 0.270 seconds per line. The profile named the
transparent `defSet (Lset ...)` in statement positions
(`_build/lj-1.21-report.md:113-125`).

This landing does not shorten LJ-1.5. It serves the 5.5 chain's level
size step at `|L_γ| = |γ|` (`dev/literature/devlin-II5.md:278-285`). That
step lands in block 5, not in the crossing.

### 4.3 The stage arithmetic (`[LJ-1.20]`)

The kit delivers `+ω`, `boundCloses` and `envCloses`
(`src/L/Ordinal/StageArith.lagda.md`). `boundCloses` puts the code-set
bound inside the carrier at a `closedω` stage. `envCloses` does the same
for the environment bound (`_build/lj-1.20-report.md:24-37`).

These are the "carrier facts" row of route A, booked at 0.15 to 0.45k
(`_build/lj-1.12-report.md:36`). The row shrinks to a site
re-derivation. P-l requires re-derivation, not copying
(`dev/LESSONS.md:2305-2330`). `+ω-ord` has no current consumer. The
crossing's limit certificates are its intended consumer
(`_build/lj-1.20-report.md:129-131`).

### 4.4 The seconds cure (`[LJ-1.24]`)

The abstract-source restatement cut a transport-heavy block from 29.1
seconds to 2.3 seconds (`_build/lj-1.24-report.md:3-8`). The cure is
about six lines. The module header gains the `D` and `inv` signatures.
Seven one-line replacements change the `defSet` mentions
(`_build/lj-1.24-report.md:77-82`).

The cure attacks the R-38 class. The transport over a transparent `sett`
index unfolds the satisfaction tower. The same transport over an abstract
index unfolds nothing (`_build/lj-1.24-report.md:57-67`). The crossing's
transport statements have the same shape. The cure can apply there. It
reduces seconds, not lines (P-q, `dev/LESSONS.md:2633-2650`).

### 4.5 Which landings reduce the work

DD27 reduces lines on the hull side. The bridge residue of 210 to 430
lines is consumed. Stage arithmetic reduces the carrier-facts row. The
cure reduces seconds. The level size reduces block-5 lines. None of the
four removes the crossing's floor risk. The equivalence legs and the
satisfaction decodes at the concrete carriers remain the open term.

## 5. IS ROUTE A STILL THE ROUTE?

Yes. Route A is the bounded substrate over the delivered description. The
crossing's content is the recognition half. It identifies the collapsed
image as a level of the real tower. The hull's index type does not enter
that content (`_build/lj-1.12-report.md:18-24`).

The route's components stand: code set, twelve-clause table, step and
graph stack, equivalence, transport certificate, carrier facts,
iso-invariance, limit case (`_build/lj-1.12-report.md:20-49`). DD27
changed the input side. The crossing consumes elementarity at hull
parameters (`_build/lj-1.12-report.md:160-166`). That input is now
delivered (`src/L/Hull.lagda.md:415-426`).

The second-order question: does DD27 shorten the chain? It does, on the
hull side. The definable well-order appears at exactly one place on the
GCH chain. That place is Devlin's proof of the hull
(`_build/lj-1.16-review.md:113-116`). The term algebra needs only the
meta well-order. The definable well-order drops out of both towers
(`_build/lj-1.23-report.md:171-195`). The per-tower content falls from
two objects to one.

That does not move the 3.3k center. The crossing never priced the
definable well-order. The fourth shape removed it before the re-price
(`_build/lj-1.16-review.md:139-155`). The line figure is stale downward
by the block-1 residue and the carrier-facts row. The residue was booked
at 210 to 430 lines outside the crossing (`_build/lj-1.12-report.md:162-169`).
The carrier-facts row was 0.15 to 0.45k (`_build/lj-1.12-report.md:36`).
The stage arithmetic delivers part of that row.

The 3.3k basis is mixed. Delivered comparables cover 1,973 lines. The
rest rests on surveys (`_build/lj-1.1-recon.md:129`, `:212`). The target
is true at the intended generality. The limit case is the only unbuilt
part, and it is standard. D-10 does not stop the funding.

The band is 2.4 to 4.3k after the [LJ-1.15-R] measurement
(`_build/lj-1.15-review.md:17-19`). The center stays near 3.3k. The line
figure is not the gate. The seconds are the gate. Section 1 prices them.

## 6. TEMPLATE VERSUS PER-TOWER, PRICED SEPARATELY (DD4)

The template is the recognition frame. It holds the statements
`Believes`, `CrossOut`, `HasLevels`, `Covered`, `SucClosed` and
`Condenses`. It holds the successor case, `level-in` and `M⊆L`. It holds
the transfer legs and the limit case. Route A books the shared part at
0.4k lines (`_build/lj-1.12-report.md:115-123`). The template runs in the
parameterized class at 0.005 to 0.013 seconds per line. Price: about 4
seconds.

The per-tower content is the level-hood certificate. Route A books the
Def-only part at 2.9k lines (`_build/lj-1.12-report.md:115-123`). The
certificate is the bounded substrate over the tower's own description.
It holds the code set, the twelve-clause table, the step and graph stack,
the equivalence, the carrier facts and the iso-invariance. Price: the
bulk of the 60 seconds in section 1.

The J tower pays for its own certificate. It does not pay for the Def
certificate. The J-side bounded layer is priced at 470 to 610 lines plus
sixteen unmeasured op-clauses (`_build/lj-1.12-report.md:130`). The J
certificate is structural. It has no Def step. The class is unmeasured.
It is likely the parameterized class.

The second per-tower object is gone. The definable well-order was needed
only for the hull. The term algebra removes it from both towers
(`_build/lj-1.23-report.md:171-195`). DD4's win is real: the well-order
is not paid twice, and the recognition frame is written once.

D-26 bears on the certificate. A stage built as a definable power carries
nothing. Its members are sets, not constructions. The only well-founded
key is the defining formula (`dev/LESSONS.md:1676-1691`). The Def tower's
certificate is that syntax. It is why the crossing carries the code-set
and table rows. The J tower's stage carries generation data. Its
certificate is structural. D-26's two branches are the two certificates.

The DD4 answer, stated once: condensation is one template frame plus two
per-tower certificates. The J tower instantiates the frame. It writes its
own certificate. The 60-second estimate prices the Def certificate. The
J certificate's price is unmeasured. The template costs about 4 seconds.

## 7. THE PROBE

The one miniature: decode one certified clause of the level story at the
concrete class carrier. The [LJ-1.15] probe measured the same content at
variable slots at 0.0052 seconds per line (`_build/lj-1.15-report.md:82-91`).
The unmeasured step is the instantiation at the real carrier. P-t says
the class follows the formula, not the carrier (`dev/LESSONS.md:2601-2630`).
The probe measures the formula's class at its real site.

The probe's statement: embed one bounded clause at `Sʟ` with `embed`.
Prove the two-way decode at the class carrier. Ride the delivered
`Lset-only` and `Lset-defines` (`src/L/Hierarchy.lagda.md:334`, `:646`).
Prove the `TransferL` shape for the clause. The clause is the measured
hardest one at 155 lines (`_build/lj-1.15-review.md:243-248`).

The expected cost is 15 to 30 minutes of wall time. The block is about
200 lines. At the floor class it checks in 45 to 60 seconds. At the
parameterized class it checks in seconds. The dispatch takes one agent
slot and one Agda process at `GHCRTS="-M8g"`. The probe is never
committed.

The gate criteria are one number each. GO: the block checks at or below
0.013 seconds per line. Route A funds at about 17 to 60 seconds. NO-GO:
the block checks at or above 0.10 seconds per line. The floor class
holds. Route A re-prices to about 700 seconds and stops for a re-route
(DD8).

Why this miniature decides the price: the crossing's open term is the
concrete-carrier decode. The archive measured that class at 0.395 with a
body-bound defect. [LJ-1.24] measured the cured class at 0.019. The probe
measures the class at this site, clean. No other leg carries the 100x
spread.

## 8. LITERATURE USED

`dev/literature/devlin-II5.md`, sections 1.5 and 2.1 to 2.8. Took the
chain's shape (`:145-170`). Took Step C's requirements: level-hood at
Sigma-1 strength with a Sigma-0 matrix, the witness inside the carrier,
and a bounded Def-step description (`:209-256`). Took Step D's order
requirement, which DD27 removed (`:257-271`). Took Step F: the GCH chain
consumes condensation parts (i) and (ii) only (`:278-285`).

`_build/literature/dev2.txt:1369-1388`. Read the statements of 5.5 and
5.6 directly. Took the cardinal arithmetic and the transitive-fixing
clause. This is the primary check that the well-order is not on the
chain.

`dev/literature/devlin-errata.md`. NOT read. WHY NOT: [LJ-1.14] verified
it does not cover Chapter II section 5 (`_build/lj-1.14-report.md:107-108`).
The brief rules out re-checking it.

`dev/literature/j-hierarchy.md`. NOT read. WHY NOT: the J certificate
enters this report only through the digest's per-tower table
(`devlin-II5.md:380`) and the [LJ-1.12] prices. Nothing in the seconds
verdict turns on the J order's shape.

## 9. ARCHIVE USED

`archive/rud-route/src/L/Condensation.lagda.md`, read in full. Took the
line split: 514 non-blank in-fence lines, 333 on the structural story and
decodes, 64 on the core, 55 on the carrier embeddings. Took the D32
deletion of the crossing obligations (`:857-861`).

`dev/LESSONS.md:2330-2370`. Took the transplant table, the three-disease
table, and the body-bound classification. Took the [T106] refutation at
`:2337`. Took the ambientOnly-from measurement at `:2364`.

`dev/LESSONS.md:2700-2720`. Took the three structural defects of the
archived story: `sndIn`, `snd∈Snd`, `limIn`.

`dev/LESSONS.md`. Also read P-l at `:2305`, P-m at `:2460`, P-n at
`:2483`, P-t at `:2601`, P-q at `:2633`, R-38 at `:829`, C-31 at
`:1855`, D-10 at `:1316`, D-26 at `:1676`. These decide the block.

`_build/lj-1.23-report.md`. Sections 2, 4, 5, 6, 7, 10. Took the
criterion at hull parameters, the re-stated API, the retired piece one,
and the 0.0039 rate.

`_build/lj-1.24-report.md`. Sections 1, 3, 6, 7. Took the cure, its
class, and its price.

`_build/lj-1.15-report.md` and `_build/lj-1.15-review.md`. Took the
measured 0.0052 rate, its variable-slot scope, and the re-priced band.

`_build/lj-1.16-review.md`. Took the fourth shape, the single place of
the well-order, and the per-tower count.

`_build/lj-1.1-recon.md`. Sections 3, 5, 6, 8. Took the block-3 split
and the probe design. The 3.3k figure's basis is mixed: delivered
comparables for 1,973 lines and surveys for the rest
(`_build/lj-1.1-recon.md:129`, `:212`).

`_build/lj-1.12-report.md`. Sections 2, 3, 4, 5. Took the route-A
components, the shared and Def-only split, and the floor-class warning.

`_build/lj-1.20-report.md`, `_build/lj-1.21-report.md`. Read in full.
Took the stage kit and the level size.

`src/V/Collapse.lagda.md`. Read in full. The collapse half is delivered.
`src/L/Hull.lagda.md`. Read `TermAlgebra`, `AtStage`, `AtM` and
`hull-closed`. `src/L/Constructible.lagda.md:221-223`. `Lset` is opaque.

`dev/PLAN.md:452`, `:462-466`. Took the LJ-1.5 row and the landings'
rows. `dev/ledger.toml:305`. Took the seconds budget.

## 10. WHAT I AM NOT SURE OF

1. The split of the crossing between the parameterized class and the
   floor class. The whole verdict rests on it. The probe decides it.
2. Whether the equivalence legs can ride the delivered graph theorems
   without walking the built story at the concrete carriers. If they can,
   the crossing lands near 17 seconds. If they cannot, the floor legs pay
   P-n's floor. The crossing lands near 280 seconds, and the whole
   crossing at the floor lands near 730.
3. Whether the [LJ-1.24] cure's 0.019 transfers to condensation's
   transport sites. P-l forbids transferring it by analogy. The probe
   measures it.
4. Whether the block-1 residue is fully consumed. [LJ-1.23] re-states
   `leastWit` and `Witnessed-small` for the downstream condensation API
   (`_build/lj-1.23-report.md:88`). Some API work may remain.
5. The J tower's certificate seconds. They are unmeasured.
6. `fin-inj` at 50 to 100 lines is owed for block 5, not for LJ-1.5.
7. The 60-second figure is ESTIMATED. The measured endpoints frame it.
   The probe narrows it to one end.

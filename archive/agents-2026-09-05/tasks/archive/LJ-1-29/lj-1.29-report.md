# LJ-1.29 report: does the crossing need one formula readable at two carriers?

Status: COMPLETE. Read-only recon. No Agda run. No commit. No push.
Written incrementally per C-22. The report uses ASD-STE100.

## 1. THE VERDICT

**NO. The crossing cannot drop the shared formula.** The restatement does
not work. Each carrier keeps its own formula, but the MEANING must still
travel between them, and the only delivered vehicle for the meaning is the
bounded story read at both carriers. Dropping the shared formula either
assumes the transport (the trap) or re-states the machine per carrier
(unmeasured and per-tower). The 31 seconds is the PLACEMENT price of the
class-carrier half, not the price of sharing. The upstream rewrite, `[LJ-1.30]`,
keeps the shared formula and removes the placement.

The arithmetic, stated once. The present shape measures at 0.110 to 0.113
seconds per line (MEASURED, `_build/lj-1.27-review.md:36-41`). At the 3.3k
line center that is about 370 seconds (ESTIMATED by the gate's own
extrapolation). The whole GCH seconds budget is 99.6 to 147.7 seconds
(`dev/ledger.toml:305`). The present shape does not fund. The direct base
variant measures at 0.0053 to 0.0114 seconds per line (MEASURED,
`_build/lj-1.27-report.md:60-69`, `_build/lj-1.27-review.md:36-41`), but
it is NOT the crossing. It is the
class-carrier local certificate without the embed and without the transfer
(`_build/lj-1.27-report.md:60-69`). The transfer is exactly the step the
crossing needs. A restatement that deletes the transfer proves a different
theorem.

The one route that funds keeps the shared formula and kills the placement.
`[LJ-1.30]` rewrites `consAtL` to be constant-free. Then the clause reaches
the parameter-free axis through the delivered `erase`
(`src/FOL/Count.lagda.md:598-611`) with no placement. `σL` becomes
`embed (erase φ refl)`. `σL-eq` becomes one `cong` through `erase-inv`
(`src/FOL/Count.lagda.md:617-637`). `σL-transfer` becomes two `cong`s plus
`abs₀` at the original clause. The return measured that `abs₀` at about 1.6
seconds (`_build/lj-1.27-report.md:95`). The block then lands near the base
rate plus a few seconds per clause. This is `[LJ-1.27-R]` section 6's
hypothesis, not a price (`_build/lj-1.27-review.md:197-230`).

The answer to the brief's stake: the direct shape does not carry the
crossing. The shared formula stays. Its placement must go. That is
`[LJ-1.30]`'s term, and it is the only route.

## 2. WHAT THE CROSSING MUST CONCLUDE

The crossing is one obligation, stated at the set carrier `M`:

```agda
CrossOut φ = (v b : Sᴹ) → IsOrd (fst b) → Believes φ v b
           → fst v ≡ Lset (fst b)
```

with `Believes φ v b = ⟨ (v ∷ b ∷ []) AbsM.⊨ᵐ φ ⟩`, the inner reading at
`M` (`archive/rud-route/src/L/Condensation.lagda.md:164-169`). The target
statement it serves is `Condenses = Σ[ β ∈ S ] (IsOrd β × (M ≡ Lset β))`
(`:186-187`).

The conclusion is an equality of VALUES in the ambient universe. `Lset` is
the opaque meta tower (`src/L/Constructible.lagda.md:221-223`). The
hypothesis is a satisfaction in the restricted structure at the transitive
set `M`. These are different kinds of fact. The whole question is how the
second produces the first.

The assembly that consumes the crossing takes only the value equality. The
successor step, `level-in` and `M⊆L` all use `co` at one place, as
`fst v ≡ Lset (fst b)` rewritten into a membership
(`archive/rud-route/src/L/Condensation.lagda.md:208-246`). No formula
comparison enters the assembly. The formula comparison lives entirely in
the proof of `CrossOut` itself.

D-10 check. The crossing's target is true content. The modern bounded
clause decodes at variable slots (`_build/lj-1.15-report.md:34-36`), and
the graph agrees with the tower in both directions
(`src/L/Hierarchy.lagda.md:334`, `:646`). No Tarskian or cardinality
obstruction appears. The retired archive's false target was the trivial
Def-step story (`[LJ-1.11]`), not this one. The question here is the shape
of the proof, not the truth of the target.

## 3. STEP BY STEP

The crossing's proof, as the delivered design assembles it, has six steps.
The set carrier `M` is transitive. The class carrier `L` is the
constructible class. Both are transitive classes of the same ambient
universe `𝒮ᵥ` (`src/FOL/Absoluteness.lagda.md:38-64`).

**Step 1. The hypothesis at `M`.** `Believes σᴹ v b` is the inner reading
of the story at `M`. The story at `M` is the same story as at `L`,
relabelled from the parameter-free axis (`archive/rud-route/src/L/
Condensation.lagda.md:754-786`; the modern class-carrier mirror is
`src/ProbeLJ127.agda:277`). Carrier: `M` only.

**Step 2. `M`'s own certificate.** `σ₁-up` at `M` moves the inner reading
to the ambient reading: `Believes σᴹ v b` implies
`⟨ (fst v ∷ fst b ∷ []) ⊨ᵛ σᴹ ⟩`
(`src/FOL/Absoluteness.lagda.md:182-185`). It needs the story's Sigma-1
witness at `M` and `M`'s transitivity. It needs no fact at `L`. The
delivered one-line shape at the class carrier measures 179 milliseconds
(`_build/lj-1.27-report.md:93-95`). This step does NOT need one formula at
two carriers. It needs `M`'s own formula and `M`'s own certificate.

**Step 3. The meeting in the ambient reading.** The relabelling theorem
`amb-agree` equates the ambient reading of the story at `M` with the
ambient reading of the story at `L` (`archive/rud-route/src/L/
Condensation.lagda.md:283-289`). It is generic in the formula and cheap.
It exists BECAUSE `σᴹ` and `σL` are one story at two carriers. This is the
shared-formula step in its purest form. If the two carriers kept different
formulas, this step would need a new meaning-equivalence theorem between
them at the ambient level. No such theorem exists in the tree. It would be
the story-to-machine agreement at the ambient level, which is per-tower
and unmeasured.

**Step 4. `L`'s own certificate.** `π₁-down` at `L` moves the ambient
reading of the story to the inner reading at `L`
(`src/FOL/Absoluteness.lagda.md:187-190`). It needs the story's Delta-0
witness at `L`. This is the class-carrier half that `[LJ-1.27]` measured.
The witness for the PLACED clause exhausts 8 GB in two formulations
(`_build/lj-1.27-review.md:59-91`). The composed route through the
unplaced form checks in 25.6 seconds (`src/ProbeDD25C.agda`,
`_build/lj-1.27-review.md:84-86`). This step needs `L`'s own formula and
`L`'s own certificate. It does NOT need `M`.

**Step 5. The story-to-machine agreement at `L`.** The story's inner
reading at `L` implies the graph's inner reading at `L`
(`_build/lj-1.28-report.md:96-104`, leg D). The delivered machine's
projections serve as the machine side
(`src/L/Coding/Sequence.lagda.md:217-229`, `:295-312`). This row is
per-tower, surveyed at 0.3 to 0.8k lines (`_build/lj-1.15-report.md:187-191`).
It needs only a value-level agreement at one carrier, `L`.

**Step 6. The tower-landing at `L`.** `Lset-only` reads the graph's inner
satisfaction at `L` and returns the tower value
(`src/L/Hierarchy.lagda.md:334-348`). The value equality
`fst v ≡ Lset (fst b)` is produced here. Delivered. It needs only a value
agreement at `L`.

**Which steps need one formula at two carriers.** Steps 2, 3 and 4 form
one transport. Step 2 is the story's absoluteness at `M`. Step 4 is the
story's absoluteness at `L`. Step 3 joins them through the relabelling.
All three are properties of the SAME story formula read at both carriers.
This transport is the part of the crossing that cannot be restated as a
value comparison.

**Which steps need only a value agreement.** Steps 5 and 6, and the whole
assembly of `Condenses` (`archive/rud-route/src/L/Condensation.lagda.md:
208-246`). These consume and produce equalities of values at one carrier.

**The step that forces the shared formula.** Step 4 exists because the
graph cannot be read at `M`. `LsetGraphAt` carries an unbounded existential
(`src/L/Coding/Sequence.lagda.md:292`), and `StepAt` carries three
(`:120`). The graph is not absolute. The `[LJ-1.2]` gate found the step
clause has no Delta-0 witness at any carrier (`_build/lj-1.2-gate.md`,
section 2). So `L`'s own formula cannot be the hypothesis at `M`. The
hypothesis at `M` must be an absolute formula with the tower's meaning.
The only such formula is the bounded story. The story must then be read at
`L`, because the value equality is produced only at `L`'s landing. One
formula, two carriers, forced.

## 4. WHAT CARRIES THE MEANING ACROSS

In the shared-formula design, the meaning travels on the story's own
absoluteness. The kit is `abs₀`, `σ₁-up` and `π₁-down`
(`src/FOL/Absoluteness.lagda.md:122`, `:182`, `:187`). Each carrier's
certificate is the story's own Delta-0 or Sigma-1 witness at that carrier
(`src/ProbeLJ115.agda:170-220`). The relabelling carries the witnesses for
free: `mapΔ₀` and `mapΣₙ` are structural recursions
(`src/FOL/Manipulation/Relabelling.lagda.md:209-242`). This is P-u's law,
measured at `[LJ-1.27-R]` (`dev/LESSONS.md:2908-2941`). The certificates
do NOT travel along a placement. The placement is where the wall lives.

In the alternative, nothing delivered carries the meaning. The value
equality is the crossing's OUTPUT, not a deliverable hypothesis. `M`'s
belief pins `v` to what `M`'s internal table says. Nothing in that fact
alone pins `v` to the real tower. The two carriers may satisfy their own
formulas and disagree. That is the brief's trap, and it is real here.

The alternative has two ways to fill the gap, and neither is delivered.
The first way assumes the transport. It reads the crossing's conclusion as
if `M`'s belief already determined the tower value. That is a hole, not a
route. The second way builds a decode-level transport: the story's decode
at `M` (with the relabelled readers and the carrier hypotheses), the
story-to-machine agreement at `M` or at the meta level, and a decode-free
tower-landing (a refactor of the satisfaction-typed landing at
`src/L/Hierarchy.lagda.md:191-348`). None of these exists in the tree. All
are per-tower. The base variant's 0.0053 to 0.0114 rate
(`_build/lj-1.27-report.md:60-69`, `_build/lj-1.27-review.md:36-41`)
measured the class-carrier local
certificate without the transport. It does not price the decode-level
stack. The decode-level design is a new per-tower machine, not a
restatement. It does not fund at the base rate.

## 5. WHAT REPLACES `σL`

Nothing replaces `σL`. The story at the class carrier stays. The crossing
needs it. What changes is how `σL` is built and certified.

The measured block is `σL = embed (absFo (Clause.existBndAt C T B))` with
its placement (`src/ProbeLJ127.agda:277-279`). The profile attributes 31.0
of 33.3 seconds to two obligations: `σL-transfer` at 24.8 seconds and
`σL-eq` at 6.2 (`_build/lj-1.27-report.md:58-69`). Both normalize the
placement over the whole clause tree. The review confirms the wall is in
building the Delta-0 witness for the placed formula, not in applying
absoluteness (`_build/lj-1.27-review.md:74-83`).

The replacement is upstream. `[LJ-1.30]` rewrites `consAtL` to be
constant-free. Then `countFo` of the clause is zero. The clause reaches the
parameter-free axis through the delivered `erase`
(`src/FOL/Count.lagda.md:598-611`), and `erase-inv`
(`:617-637`) makes `σL ≡ φ` a syntactic equality. `σL-eq` becomes one
`cong`. `σL-transfer` becomes two `cong`s plus `abs₀` at the ORIGINAL
clause. The return measured that `abs₀` at about 1.6 seconds
(`_build/lj-1.27-report.md:95`). The certificates stay on the unplaced
formula. That is P-u's prescription: certify before you place, then
compose through the unplaced form (`dev/LESSONS.md:2908-2918`).

One best-effort number per obligation, with its basis (DD8). The funded
shape's class-carrier certificate per clause: about 2 seconds. Basis: the
measured 1.6-second `abs₀` plus the measured base-variant rate for the
decodes. ESTIMATED as a whole, because the constant-free rewrite is
unmeasured. The whole crossing at 3.3k lines at the base rate: about 18 to
38 seconds (the brief's table), plus the per-clause transfers. The budget
is 99.6 to 147.7 seconds (`dev/ledger.toml:305`).

The direct shape does not replace `σL` either. It states the clause
directly at the class carrier and deletes the embed and the transfer
(`_build/lj-1.27-report.md:60-69`). It measures cheap, but it does not
carry the crossing. The crossing's hypothesis is at `M`. The value
equality is produced at `L`. The transport between them is not in the base
variant. A crossing built from the base variant alone would silently
assume the transport. That is the trap in the brief, and it is the exact
shape the base variant omits.

## 6. TEMPLATE OR PER-TOWER? (DD4)

The shared-formula crossing is TEMPLATE. One transfer frame, generic in
the story formula, serves both towers. The archive's `AtCarrier` and
`Transport` modules are generic in the formula
(`archive/rud-route/src/L/Condensation.lagda.md:120-160`, `:270-292`).
The per-tower content is the story's clauses and certificates, and the
story-to-machine agreement at `L`. This is exactly `[LJ-1.26]`'s split:
one template frame plus two per-tower certificates
(`_build/lj-1.26-report.md:239-254`). `[LJ-1.28]` keeps that split and
rides the delivered graph theorems (`_build/lj-1.28-report.md:6-10`).

The alternative is MORE per-tower. The story's decode at `M`, the
relabelled readers with their carrier hypotheses, the story-to-machine
agreement at `M`, and the tower-landing at `M` are all per-tower
re-statements of content the tree already wrote once at `L`. The J tower
would pay for the Def stack again. That is the wrong direction of DD4, and
it is the same direction the project measured as failure: the machine
stack at a variable carrier is the content class that costs
(P-m, `dev/LESSONS.md:2460`; P-n, `:2483`).

The one DD4-correct answer: keep the machine once at `L`, keep the story
shared, and fix the placement upstream. The `[LJ-1.30]` rewrite is shared
work: a constant-free `consAtL` serves both towers' stories. The J tower's
certificate is structural and does not pay the Def syntax (D-26,
`dev/LESSONS.md:1676-1691`), but it does pay the same shared frame.

## 7. LITERATURE USED

`dev/literature/devlin-II5.md`, sections 2.1 to 2.8. Took Step C's
requirement list at `:209-256`, and the transfer chain at `dev2.txt:
1186-1215` (the primary text). Devlin writes the level formula ONCE as a
Sigma-1 form with a Sigma-0 matrix (`dev2.txt:1186-1194`, from 2.7), and
reads it at `L_α`, at `X`, at the collapse `M`, and at the ambient level.
The transfers between the carriers are Sigma-1 elementarity, the collapse
isomorphism, and 1.9.15's Sigma-0 absoluteness (`dev2.txt:1200-1215`,
`:1219`).

The answer to the brief's question: Devlin NEEDS the one formula, and not
merely uses it. The elementarity and the isomorphism are truth-preservation
of that formula. A per-carrier formula would leave the two structural
connections nothing to preserve. The Sigma-1 statement is transferred BY
NAME across the carriers (`dev2.txt:1200-1215`). The book's absoluteness
is asserted through 1.9.15, where the project must prove the certificates.
That is the gap the probe prices. The book offers no support for the
per-carrier-formula alternative.

`_build/literature/dev2.txt:1369-1388`. Read the statements of 5.5 and
5.6. They consume condensation parts (i) and (ii) only. Nothing there
changes the crossing's shape.

`dev/literature/devlin-errata.md`. NOT read. WHY NOT: the brief rules it
out. `[LJ-1.14]` verified it does not cover Chapter II section 5.

`dev/literature/j-hierarchy.md`. NOT read. WHY NOT: the J tower enters
this answer only as the DD4 comparison target. Nothing in the verdict
turns on the J order's shape.

## 8. ARCHIVE USED

`_build/lj-1.27-review.md`, sections 4 to 7, read first per scope. Took
the wall at `:59-91`, the three closed routes at `:93-123`, the composed
route at `:84-86`, the `consAtL` route at `:197-230`, and the hand-off at
`:264-269`. The hand-off is the question this report answers.

`_build/lj-1.28-report.md`, in full. Took leg C (transfers), leg D
(story-to-machine, `:96-104`), leg E (the certification instance is
LJ-1.27's term, `:105-117`), and the DD4 correction at `:157-170`.

`_build/lj-1.27-report.md`, sections 4 and 9. Took the profile
(`σL-transfer` 24.8, `σL-eq` 6.2), the base variant, the 179-millisecond
`σ₁-up`, the 1.6-second `abs₀`, and the TransferL uncertainty.

`_build/lj-1.26-report.md`, sections 5 and 6. Took route A, the DD4 split,
and the probe design at `:239-310`.

`archive/rud-route/src/L/Condensation.lagda.md`. Read `AtCarrier`,
`CrossOut`, `Condenses` and `Assembly` at `:120-246`, the transport at
`:270-292`, the story at `M` at `:754-786`, and `σL = embed levelStory`
with its transfers at `:823-853`. Read for SHAPE only. Its target is
classically false (`[LJ-1.11]`), so no price was taken from it. The shape
is the one-formula design, and the assembly consumes only value
equalities.

`_build/lj-1.15-report.md`. Took the variable-slot decode at 0.0052
(`:82-91`) and the unmeasured equivalence leg at `:187-191`.

`dev/LESSONS.md`. P-l at `:2305`, P-m at `:2460`, P-n at `:2483`, P-t at
`:2601`, P-u at `:2908`, D-10 at `:1316`, D-26 at `:1676`. P-u is the law
that decides the funded shape: the witness travels by relabelling and not
by placement.

`src/L/Hierarchy.lagda.md`, `src/L/Coding/Sequence.lagda.md`,
`src/FOL/Absoluteness.lagda.md`, `src/L/Coding/Model.lagda.md`,
`src/FOL/Count.lagda.md`, `src/FOL/Manipulation/Relabelling.lagda.md`,
`src/ProbeLJ127.agda`, and the probes cited by `[LJ-1.27-R]`
(`src/ProbeDD25C.agda`, `src/ProbeDD25D.agda`, `src/ProbeDD25E.agda`).
These fix the signatures, the satisfaction relations, and the measured
classes. `dev/ledger.toml:305` fixed the seconds budget.

## 9. WHAT I AM NOT SURE OF

1. The M-side story at a variable carrier. The mirror of `σL` at `M` was
   never built. Its relabelling and its carrier hypotheses are unmeasured.
   The verdict does not depend on its price: the crossing still needs the
   L-side landing and the transport. But the M-side cost is additive, and
   it is open.

2. The decode-free tower-landing. I believe the meta-level refactor of
   `step-Lset`, `approx-val` and `Lset-only` is mathematically coherent,
   because the L-carrier membership in their types is the carrier
   discipline, not the mathematics. It does not exist in the tree, and its
   price is unmeasured. It would remove the story's reading at `L` only by
   replacing it with per-tower decodes at `M` and at the meta level. That
   re-buys the transport at a per-tower price. It does not change the
   verdict: the restatement from delivered value equalities plus local
   certificates still fails.

3. Whether the modern crossing's belief is on the Delta-0 matrix or the
   Sigma-1 certificate. The two shapes need different witnesses: `σ₁-up`
   on the certificate, `π₁-down` on the matrix. Both are the same story at
   two carriers. The choice does not change the verdict.

4. The story-to-machine agreement's stated level. `[LJ-1.28]` states leg D
   at `L`'s inner reading at variable slots. If leg D could be stated at
   the ambient level for free, the L-side landing would shrink. I found no
   such statement in the tree. The search was not exhaustive.

5. The funded shape's total. The per-clause figure of about 2 seconds is
   ESTIMATED from the measured 1.6-second `abs₀` and the measured base
   rate. The constant-free `consAtL` is unmeasured. `[LJ-1.30]` measures
   it. The verdict does not rest on the figure. It rests on the placement
   being the measured wall and the placement being removable.

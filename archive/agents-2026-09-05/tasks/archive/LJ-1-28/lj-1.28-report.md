# LJ-1.28 report: can the equivalence legs ride the delivered graph theorems?

Status: COMPLETE. Read-only recon. No Agda run. No commit. No push.
Written incrementally per C-22. The report uses ASD-STE100.

## 1. THE VERDICT

RIDE, at about 5 seconds of residue. The equivalence legs do not need to
walk the built story at the concrete carriers. The delivered graph
theorems give the tower-landing halves for free. The story-to-machine
halves must be written. Their content stands at variable slots. The
crossing lands below the 60-second center and far below 280 seconds for
this term.

The one concrete decode is the certification instance. It is one
instantiation, not the 0.3 to 0.8k row. The certification instance is
LJ-1.27's term, not this report's.

The verdict is per leg, not in aggregate. Section 3 states each leg and
its shape.

## 2. THE DELIVERED GRAPH THEOREMS

The following statements are the delivered graph theorems. The
satisfaction theorems stand at variable slots. The hierarchy theorems
stand at concrete ordinals with hypotheses. The satisfaction is the inner
reading at the class L.

1. `step-Lset` (src/L/Hierarchy.lagda.md:191). `⟨ γ ⊨ StepAt v b f ⟩
   → IsOrd (fst (lookup b γ)) → Values (lookup f γ) (fst (lookup b γ))
   → Entries (lookup f γ) (fst (lookup b γ))
   → fst (lookup v γ) ≡ Lset (fst (lookup b γ))`. It reads a satisfied
   step and returns the tower value.
2. `step-table` (src/L/Hierarchy.lagda.md:221). The converse. A correct,
   complete table and the tower identity write the step.
3. `approx-val` (src/L/Hierarchy.lagda.md:274). `⟨ γ ⊨ ApproxAt f a ⟩
   → IsOrd (fst (lookup a γ)) → (x z : S)
   → ⟨ pr (fst x) (fst z) ∈ fst (lookup f γ) ⟩ → fst z ≡ Lset (fst x)`.
   Every value an approximation records is the meta tower there.
4. `approx-uniq` (src/L/Hierarchy.lagda.md:301). Two recorded values at
   one argument are equal.
5. `Lset-only` (src/L/Hierarchy.lagda.md:334). `⟨ γ ⊨ LsetGraphAt w b ⟩
   → IsOrd (fst (lookup b γ)) → fst (lookup w γ) ≡ Lset (fst (lookup b γ))`.
   The graph determines its value.
6. `graph-table` (src/L/Hierarchy.lagda.md:382). A correct, complete,
   domain-exact table satisfies the graph.
7. `hier-out` and `hier-in` (src/L/Hierarchy.lagda.md:511, :527). The
   internal hierarchy's two-way membership decode.
8. `hierL` and `hierL-spec` (src/L/Hierarchy.lagda.md:621, :624). The
   internal hierarchy, sealed at :537.
9. `Lset-defines` (src/L/Hierarchy.lagda.md:646). `IsOrd (fst (lookup b γ))
   → fst (lookup w γ) ≡ Lset (fst (lookup b γ))
   → ⟨ γ ⊨ LsetGraphAt w b ⟩`. The tower writes the graph.

The machine's projections stand under them, also at variable slots:
`StepAt-out`, `StepAt-back`, `StepAt-in`
(src/L/Coding/Sequence.lagda.md:217-229); `ApproxAt-dom`, `ApproxAt-value`,
`ApproxAt-step`, `ApproxAt-in` (:295-312); `LsetGraph-in` and
`LsetGraph-out`, renamed from the graph's readings (:321-325, :349-351).

The satisfaction is `AbsL._⊨ᵐ_`, the inner reading at the class L
(src/FOL/Absoluteness.lagda.md:75-78, renamed at
src/L/Hierarchy.lagda.md:78-79). `S` is the constructible carrier's sort.
`Lset` is opaque (src/L/Constructible.lagda.md:221-223).

## 3. THE OBLIGATIONS A LEG STILL CARRIES

### Leg A. OUT: the graph at the collapsed image reads the tower

The statement is `Lset-only` at the collapsed image and the collapsed
ordinal. The theorem is delivered. The crossing instantiates it once.
Concrete decode forced? No. Delivered uses at concrete positions already
stand (src/L/Choice/Order.lagda.md:386, src/L/Choice/Limit.lagda.md:191).
Residue: none.

### Leg B. IN: the tower writes the graph

The statement is `Lset-defines` at the collapsed position. The theorem is
delivered. Concrete decode forced? No. Residue: none.

### Leg C. The story's transfers at M and at L

The crossing carries the inner reading at M to the ambient reading, then
to the class carrier. The template shape is delivered:
`TransferM` (archive/rud-route/src/L/Condensation.lagda.md:291),
`amb-agree` (:283), `level-transfer` (:786), `level-transfer-up` and
`level-transfer-down` (:845, :850). The kit is `abs₀`, `σ₁-up` and
`π₁-down` (src/FOL/Absoluteness.lagda.md:122, :182, :187).
The story's Δ₀ and Σ₁ certificates are per-clause content at variable
slots (src/ProbeLJ115.agda:216-220). Concrete decode forced? No. The
certificates stand at the parameter-free axis. The transfers are one-line
applications of the kit. Residue: the certificates, booked in the
per-tower rows, not in the equivalence row.

### Leg D. The story-to-machine agreement at L

This is the equivalence row. The statement is a two-way decode between
the bounded table's clause and the delivered machine's clause, at
variable slots. The delivered machine's projections serve as the machine
side (src/L/Coding/Sequence.lagda.md:217-229, :295-312). The row also
carries the bound construction and the vacuity arguments
(_build/lj-1.15-report.md:187-191). Concrete decode forced? No. The
clause-to-content half was proved at variable slots with no carrier fact
(_build/lj-1.15-report.md:34-36). The bound sub-content places the bound
in the carrier. That is a concrete position with an opaque stage. It is
not a satisfaction decode of the built story. Residue: 0.3 to 0.8k lines,
about 5 seconds. Section 4 prices it.

### Leg E. The certification instance at M and at L

The crossing names the built story's satisfaction at the concrete
carriers. The statements are the `CrossOut`-shape instance and its
mirrors. Concrete decode forced? Yes. This is the one instantiation. The
template isolates it: the template is generic in the formula, so the
statements at M do not name a transparent construction
(archive/rud-route/src/L/Condensation.lagda.md:149-186). The instance
counts a few statements, not 0.3 to 0.8k lines. Its class is LJ-1.27's
probe term.

## 4. THE RESIDUE PRICE

Leg A and Leg B: 0 lines, 0 seconds. Delivered.

Leg C: the certificates live in the per-tower rows. The transfers live in
the template. The template costs about 4 seconds
(_build/lj-1.26-report.md:242-247). Class: parameterized.

Leg D: 0.3 to 0.8k lines (survey, _build/lj-1.12-report.md:34). One
best-effort number: about 5 seconds. Basis: 0.5k lines at 0.010 seconds
per line. The measured decode at this site is 0.0052
(_build/lj-1.15-report.md:82-91). P-m's parameterized band is 0.010 to
0.013 (dev/LESSONS.md:2460). Class: variable-slot decode. The
clause-to-machine half is unmeasured. Its nearest measured cousin is the
0.085 neutral-carrier decode class (dev/ledger.toml:643). At 0.085 the
row costs about 43 to 68 seconds. The floor class is 0.22 to 0.297
(dev/LESSONS.md:2483). The floor is not forced by the content.

Leg E: a few statements. Its seconds are LJ-1.27's number. The gate is
one number each: GO at or below 0.013 seconds per line, NO-GO at or above
0.10 (_build/lj-1.26-report.md:300-303).

The content classes: MEASURED, the 0.0052 and the 0.085 rates.
ESTIMATED, the 5-second residue. The 0.3 to 0.8k line band is a survey.

D-10 check: the row's target is true. The probe proved the hardest
clause's decode at variable slots. The recorded band stands.

## 5. TEMPLATE OR PER-TOWER? (DD4)

The equivalence row is per-tower. Each tower's story differs. The Def
story is the twelve-clause table. The J story is structural. Each tower
proves its own agreement with its own machine.

LJ-1.26's split already books the equivalence in the per-tower
certificate list (_build/lj-1.26-report.md:253-254). The bucket
assignment does not need correcting.

The correction is on the J side. The J certificate price must carry its
own agreement row. The J-side bounded layer is 470 to 610 lines plus
sixteen unmeasured op-clauses (_build/lj-1.26-report.md:258-260,
_build/l3.32-t84-report.md:31). That
price covers the bounded layer, the transports and the assembly. It does
not separately measure the J story-to-machine agreement. The J agreement
is a named unmeasured item, not zero.

The transfer legs are template. LJ-1.26's placement is correct. The
tower-landing legs are delivered. They are neither template nor
per-tower. Both towers use the same theorems.

D-26 bears on the certificate, not on the legs. The Def certificate is
the syntax because the stage is a definable power
(dev/LESSONS.md:1676). That syntax is why the bound construction exists.
The legs themselves add no well-founded key.

## 6. LITERATURE USED

`dev/literature/devlin-II5.md`, sections 2.1 to 2.8. Took Step C's
requirements at :209-256. Devlin writes the level formula once as a
Sigma-1 form with a Sigma-0 matrix. He asserts absoluteness where the
formal proof must prove a decode. The book offers no structure that
removes a leg. Its machine is the level formula itself. No story-to-
machine agreement exists in the book. The project pays that row because
the delivered graph has no Delta-0 witness (dev/literature/devlin-II5.md:174).

`dev/literature/devlin-errata.md`. NOT read. WHY NOT: the brief rules out
re-checking it. LJ-1.14 verified it does not cover Chapter II section 5.

`dev/literature/j-hierarchy.md`. NOT read. WHY NOT: the J certificate
enters only through the per-tower table and the T84 price. Nothing in
the verdict turns on the J order's shape.

## 7. ARCHIVE USED

`_build/lj-1.26-report.md`, in full. Took the verdict and its classes at
:6-30, the DD4 split at :239-254, the probe at :279-310, and uncertainty
2 at :388-392.

`_build/lj-1.12-report.md`, in full. Took the component table at :20-49,
the shared and Def-only split at :115-123, the floor-class warning at
:151, and the equivalence row's survey at :34.

`archive/rud-route/src/L/Condensation.lagda.md`. Read the core at
:149-186, the transfers at :283-292, the decodes at :486-742, the story
and its transfers at :768-787 and :823-853, and the D32 deletion at
:857-885. Read for SHAPE only, never for a price.

`_build/lj-1.15-report.md`. Took the 0.0052 at :82-91 and the unmeasured
equivalence leg at :187-191. The probe files stay as evidence.

`dev/LESSONS.md`. P-l at :2305, P-m at :2460, P-n at :2483, P-t at
:2601, P-q at :2633, D-10 at :1316, D-26 at :1676, R-38 at :829, C-31 at
:1855. These decide the block.

`src/L/Hierarchy.lagda.md`, in full. `src/L/Coding/Sequence.lagda.md`.
`src/FOL/Absoluteness.lagda.md`. `src/L/Constructible.lagda.md`.
`src/ProbeLJ115.agda`. `_build/l3.32-t84-report.md`. `dev/ledger.toml`.
These fix the signatures and the measured classes.

## 8. WHAT I AM NOT SURE OF

1. The clause-to-machine half of the equivalence row. The 0.0052 rate
   measured the clause-to-content half. The machine half is unmeasured.
   The measured cousins span 0.0052 to 0.085. The row's price moves with
   that spread.
2. Whether the modern certification states the bounded story or the
   graph. No modern crossing exists in the tree. The archive's shape is
   the story. The graph cannot transfer because it has no Delta-0
   witness. The bounded story must exist for the transfer.
3. The J-side agreement's size. It is inside the J certificate price as
   an unmeasured item. It may be much smaller than the Def row.
4. The bound construction's home. LJ-1.15 says the equivalence leg needs
   it. LJ-1.12 books it in the carrier-facts row. The report does not
   double count it.
5. The certification instance's class. LJ-1.27 measures it. Its result
   moves the crossing between about 17 and about 60 seconds.

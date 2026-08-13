# LJ-1.27 report: the gate probe for condensation, one clause at the concrete carrier

Status: COMPLETE. Written incrementally per C-22. Untracked probe, no
commit, no push. ASD-STE100.

## 1. THE VERDICT

NO-GO, by the letter of the gate. The block checks at about 0.12
seconds per line, cold. The gate says NO-GO at or above 0.10 seconds
per line. Route A re-prices to about 700 seconds and stops for a
re-route under DD8.

The measured block is `src/ProbeLJ127.agda`. It checks in 32.2 to 33.3
seconds of user time on the first check. It has 283 non-blank code
lines. The rate is 0.114 to 0.118 seconds per line on user time, and
0.119 to 0.123 on wall time.

The number leans toward the floor class, but the evidence says the
cost is not intrinsic to the clause syntax. Section 4 gives the
attribution. The same content, stated as direct per-clause decodes and
a delivered-shape transfer, checks at 0.0053 seconds per line.

## 2. THE CLAUSE YOU PICKED

The clause is the [LJ-1.15] statement-1 block. It is the bounded
existential clause `existBndAt` with its Delta-0 witness, the Sigma-1
certificate, and the two-way decode. It is 155 non-blank lines at
`src/ProbeLJ115.agda:70-268`, copied verbatim into
`src/ProbeLJ127.agda:62-263`.

Evidence that it is the hardest. The [LJ-1.15] review re-counts
statement 1, the whole block, at 155 lines
(`_build/lj-1.15-review.md:243-248`). The [LJ-1.12] design names the
existential clause the hardest, because its witness existential is
unbounded in the delivered form (`_build/lj-1.12-report.md:173-182`).
No other clause of the twelve-clause table carries more content. A
soft clause would measure nothing, so this is the right pick.

D-10 was discharged. The target is the clause's check cost at the
class carrier. The clause is provable content, already closed at
variable slots in [LJ-1.15]. The probe closes it at the class carrier
with the transfer. The target is true.

## 3. COLD SECONDS AND LINES, UNCURED

The block is `src/ProbeLJ127.agda`. It has 283 non-blank code lines,
comments excluded, by the same count that gives [LJ-1.15] its 246 and
155. The line convention is calibrated against the review:
`src/ProbeLJ115.agda` counts 246, and lines 70 to 268 count 155.

The first check, with the file's own interface removed and the
dependencies warm, takes 33.27 seconds of user time and 34.83 seconds
of wall time. A second run takes 32.17 and 33.63. The noise rule says
the pair is flat: the delta is 3.3 percent, under 5 percent.

The rate is 0.114 to 0.118 seconds per line on user time, and 0.119 to
0.123 on wall time. The warm interface read takes 1.21 seconds of user
time. It is not a re-check of the body, so it is not comparable to
[LJ-1.15]'s warm figure.

The gate numbers: GO at or below 0.013. NO-GO at or above 0.10. The
block lands at about 0.12. That is NO-GO.

One Agda process ran at `GHCRTS="-A64m -I0 -M8g"` per C-12. Process
inspection was blocked in this environment for most of the run. No
sibling Agda process was observed when inspection worked.

## 4. IS THE COST INTRINSIC TO THE SYNTAX OR AN ARTEFACT OF THE STATEMENT?

The cost is an artefact of the statement. It is not intrinsic to the
clause's syntax. The evidence is the profile and the base variant.

The profile (`agda --profile=definitions`) puts the whole excess in
two obligations:

| obligation | seconds |
|---|---:|
| `ClauseDecode.σL-transfer` | 24.8 |
| `ClauseDecode.σL-eq` | 6.2 |
| all other definitions, together | about 2.3 |

`σL-eq` and `σL-transfer` apply the generic placement and absoluteness
theorems (`⊨-abs`, `embed-⊨`, `abs₀`) to the whole built clause at the
class carrier. The elaborator normalizes the whole tree: the constant
collection, the placement, and the satisfaction. That is the P-t
mechanism, the built tree unfolding at every use
(`dev/LESSONS.md:2601-2630`).

The same content, stated directly, is cheap. The base variant, the
clause with its two-way decode, the certificate, and the ride but
without the embed and the transfer, checks in 1.11 seconds over 209
lines, 0.0053 seconds per line. The two-way decode of the embedded
clause at the class carrier costs 25 and 23 milliseconds. The
certificate's one-line transfer, the delivered `σ₁-up` shape, costs
179 milliseconds. The `abs₀` step alone costs about 1.6 seconds.

The hot obligations are artifacts of how the statement names the
transparent construction. That is P-l's class
(`dev/LESSONS.md:2305-2330`). The intrinsic content, the clause at the
class carrier, checks at the parameterized rate when it is stated as
direct decodes and a delivered-shape transfer.

One caveat. The block as I built it uses the placement theorem
(`absFo`) to make the clause parameter-free before `embed`. The clause
carries the constant `numeralL 8`, so `embed` needs the placement.
Section 9 records the uncertainty this creates.

## 5. IF YOU TESTED A CURE

No cure was tested. The uncured number is the gate, and it is reported
first in section 3.

The brief allows testing the abstract-source restatement. The
attribution in section 4 already answers the question the cure would
test. The cost sits in the generic placement and absoluteness
compositions, not in the clause content. The direct-statement baseline
measures the same content at 0.0053 seconds per line. A cure would
move the block to that shape, and the profile says why.

## 6. DD4: WHAT THIS SAYS ABOUT THE J TOWER'S STRUCTURAL CERTIFICATE

The per-clause content at the class carrier is cheap when it is stated
directly. The expensive form is the generic relabelling composition.
The J tower's structural certificate has no Def step and no syntax
key. It does not need the generic composition. It can stay in the
parameterized class.

D-26 bears directly. The Def tower's certificate keys on the defining
syntax (`dev/LESSONS.md:1676-1691`). The syntax is only expensive when
generic theorems force the whole tree to unfold. The J tower's stage
carries generation data, so its certificate is structural and avoids
the syntax entirely. The two certificates split on exactly this line.

The template frame is unaffected. The template runs in the
parameterized class at 0.005 to 0.013 seconds per line
(`_build/lj-1.26-report.md:239-277`). This probe measures the Def
half, and it says: state the Def decodes directly, use the delivered
`σ₁-up` for the transfer, and do not route the certificate through
generic placement or absoluteness compositions.

## 7. LITERATURE USED

`dev/literature/devlin-II5.md`, sections 2.1 to 2.8. Read Step C's
requirement list: level-hood at Sigma-1 strength with a Sigma-0 matrix,
the witness inside the carrier, and the bounded Def-step description
(`dev/literature/devlin-II5.md:209-256`).

One-line answer to the brief's question: the book offers nothing that
shortens the formal decode work. Devlin writes the level formula once and
asserts absoluteness (Step C requirement 3 cites 1.9.15 for the Sigma-0
transfer); the formal proof pays for the two-way decodes at each carrier,
which is the gap this probe prices. Nothing in sections 2.1 to 2.8 names
a cheaper shape for the clause.

`dev/literature/devlin-errata.md`. NOT read. WHY NOT: the brief rules it
out; [LJ-1.14] verified it does not cover Chapter II section 5
(`_build/lj-1.14-report.md:107-108`).

`dev/literature/j-hierarchy.md`. NOT read. WHY NOT: the J certificate
enters this probe only as the DD4 comparison target. The measured clause
is the Def-tower half; the J side's shape is taken from the digest's
per-tower table (`dev/literature/devlin-II5.md:380`) and the [LJ-1.26]
pricing, not from the digest itself.

## 8. ARCHIVE USED

`_build/lj-1.26-report.md`, sections 2 and 7. Section 7 is this probe's
design: embed one bounded clause at `Sʟ`, decode at the class carrier,
ride `Lset-only` and `Lset-defines`, prove the TransferL shape
(`_build/lj-1.26-report.md:279-310`). Section 2 says the archived 0.395
rate does not transfer, only its floor-class warning
(`_build/lj-1.26-report.md:32-76`).

`_build/lj-1.15-report.md:82-91`. The 0.0052 rate at variable slots.
The probe re-states the same clause at the class carrier.

`_build/lj-1.15-review.md:243-248`. The 155-line hardest clause.

`_build/lj-1.12-report.md`, sections 2 to 5. Route A's components and
the floor-class warning at `_build/lj-1.12-report.md:151-156`: at 0.22
seconds per line the crossing costs about 730 seconds.

`archive/rud-route/src/L/Condensation.lagda.md:330-470` and `:486-742`.
The 333 lines of structural predicates and two-way decodes. Read for
the shape. The class-carrier section, with `σL = embed levelStory` and
the `level-transfer-up` and `level-transfer-down` shapes, was read at
`:823-853`.

`dev/LESSONS.md`. Not archived, still binds. Read P-l at :2305, P-m at
:2460, P-n at :2483, P-t at :2601, R-38 at :829, D-10 at :1316, D-26
at :1676.

## 9. WHAT I AM NOT SURE OF

The biggest uncertainty is the intended TransferL shape. The archive's
shape is a direct `σ₁-up` on the embedded story, one line
(`archive/rud-route/src/L/Condensation.lagda.md:845-853`). My block
composes the transfer through the generic placement and absoluteness
theorems, because the clause is Sigma-1 and the delivered `σ₁-up` needs
a Sigma-1 witness for the placed formula. That witness is not
delivered. The direct route, with a small Delta-0 preservation lemma
for the placement, might check near the base rate. If so, the block
would land near 0.01 seconds per line and the gate would flip. I did
not build that lemma.

The placement step is also uncertain. The brief says embed with
`embed`. The clause carries one constant, the numeral 8, so a
parameter-free embedding needs the placement first. If the intended
clause was the parameter-free form from the start, the placement
vanishes and the block shrinks.

The machine-quiet claim is weak. Process inspection was blocked for
most of the run. No sibling Agda process was observed when inspection
worked, and the profile is stable across runs.

The warm figure is an interface read. It is not comparable to the
warm figures in earlier probes.

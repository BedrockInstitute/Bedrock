# LJ-1.15 report: the one-clause probe at the Sigma-1 shape

## 1. THE VERDICT

**NO-GO, with both line counts.** Statement 1 closes at 155 non-blank lines.
The gate is 40 lines. Statement 2 does not close. Its closing pieces take 37
non-blank lines. The two headline claims of statement 2 remain unproved.
The NO-GO is on the line gates, not on possibility. The matrix is Delta-0.
It decodes at variable slots. The delivered closure lemmas cannot place the
level sequence or the bound in the carrier. The full evidence is in sections
2 and 3.

## 2. STATEMENT 1

The count is 155 non-blank lines. The gate is 40. The pieces are the matrix,
the Delta-0 witness, the certificate, and the two-way decode.

The matrix is a bounded rewrite of `existClauseAt` at variable slots C, T,
B, with the bound at slot zero (`src/ProbeLJ115.agda:70-159`). Every
quantifier is bounded. The bounds are C, B, yc, or the bound slot K. The
unbounded witness existential of the delivered clause becomes `∃ e' ∈ K`
(`src/L/Coding/Model.lagda.md:1571-1576` has the delivered unbounded `∃̇`).
The shape hypothesis bounds the code and the numeral by K. The subvalue
hypothesis bounds the two keys by K. The environment hypothesis bounds the
four environment conjuncts by K and by the environment itself. The table
lookup stays bounded by T, as delivered.

The Delta-0 witness closes (`src/ProbeLJ115.agda:170-213`). It uses the
delivered witnesses for the lifted atoms: `Δ₀-prAt`, `Δ₀-sucAt`, `Δ₀-consAt`,
and `Δ₀-liftFo` (`src/L/Absoluteness.lagda.md:93`). The certificate is one
existential over the bound (`src/ProbeLJ115.agda:216-220`). The Sigma-1
witness closes (`src/ProbeLJ115.agda:219-220`).

The two-way decode closes at variable slots (`src/ProbeLJ115.agda:229-268`).
The OUT direction reads the matrix into its layered content. The IN direction
assembles the matrix from the content. No new carrier fact enters either
direction. This answers the NO-GO condition on the decode: the matrix decodes
without a new carrier fact.

The line breakdown is matrix and witness 111, certificate 4, decode 40. The
matrix with its witness is about 2.8 times the gate. The decode adds 40
lines. The hardest clause is not a 40-line unit.

## 3. STATEMENT 2

The closing pieces take 37 non-blank lines (`src/ProbeLJ115.agda:274-321`).
The headline claims do not close. The gate is 100 lines. The missing content
is the graph as an element and the bound as an element.

The pieces that close are the following. The level appears one stage later
(`Lset∈suc`, `src/ProbeLJ115.agda:274-277`). An ordinal member of δ lives in
`Lset δ` (`ord∈Lset`, `:279-282`). The successor of a member of δ lives in
the successor (`suc∈suc`, `:284-290`). A recorded pair lives at the third
successor (`pair-stage`, `:292-306`). Every member of the level sequence
lives at that common stage (`graph-mem-stage`, `:308-321`).

The closure lemmas used are `Lset-cumul`, `ord∈Lset-suc`,
`Lset-mono`, `pr∈Lset-suc`, `Lset-suc`, `self∈sucV`, `suc∈or≡`, and
`hierL-spec` (`src/L/Ordinal/Stages.lagda.md:137-169`,
`src/L/Axioms/Basic.lagda.md:196-197,597-605`,
`src/L/Hierarchy.lagda.md:624-626`).

The graph as an element does not close. The claim is `hierL δ ∈ Lset α`.
The graph is built inside a sealed construction (`hierAt`,
`src/L/Hierarchy.lagda.md:537-538`). No delivered lemma bounds the stage of
the graph. The stage of a replacement output is internal to
`hasReplacementL` (`src/L/Axioms/Full.lagda.md:277-283`). The range set as
an element of a level is not exported. A new lemma must bound it. That is a
new carrier fact.

The bound as an element does not close. The claim is `b ∈ Lset α` for a
bound that contains the codes and the table values. The bound must contain
the environments at every arity. The environments at all arities have
unbounded stages. The natural bound has rank about δ + ω. For α the next
limit above δ, the bound is not in `Lset α`. The bound must be re-shaped
around the level sequence, whose members do have a common stage. That is the
K(u)-binding content. The survey prices it at 0.40 to 0.75k lines
(`_build/l3.32-t51-report.md:208`). It is not a 100-line fact.

## 4. SECONDS AND THE RATE

The probe is 246 non-blank lines. The warm check takes 1.26 to 1.28 seconds.
The first check takes 1.96 seconds. The rate is 0.0052 seconds per line at
the warm check.

The wing bar is 0.013193 seconds per line. The probe sits about 2.5 times
under the bar. The content stays at variable slots. It does not pay the
concrete-carrier floor.

P-n measures the same content class at a concrete carrier at 0.22 to 0.297
seconds per line. That is 42 to 57 times my measured rate. The DD24 risk is
real and directional: the variable-slot decode is cheap, and the
concrete-carrier decode is the expensive one. The probe's cheap rate is the
evidence that the variable slots survived.

## 5. DID A VARIABLE SLOT SURVIVE?

Yes. The matrix, the certificate, and the decode stand at variable slots C,
T, B, and the bound at slot zero. No concrete carrier enters any type. The
other tower can reuse the matrix shape. DD4 holds for the substrate.

The statement-2 pieces are about a concrete stage. P-l permits that. The
stage values are opaque. Their presentation does not enter the types. The
level sequence and the bound are the concrete positions of the crossing.

## 6. WHAT A NEW CARRIER FACT WOULD COST

Statement 1 needed no new carrier fact. The matrix decode closes with the
delivered lemmas.

Statement 2 needs two new facts. The first is the stage of the graph. The
sealed construction hides it. A new lemma must bound the replacement output.
The second is the K(u)-binding set over the carrier. It must contain the raw
codes, the table values, and the environments. The survey prices the second
at 0.40 to 0.75k naive lines. Both facts are new content. Neither is a
100-line addition.

One measured wall matters here. The successor closure `suc∈suc` hangs past
90 seconds when `∈sucV-inl` takes implicit arguments
(`src/ProbeLJ115b.agda:28-33`). Explicit arguments close it in 1.7 seconds.
The P-i class of the wall is the V-successor unfolding. The delivered
`limit-succ-mem` named in R-40 does not exist in this tree. The closure is
the delivered `suc∈or≡` plus explicit implicit arguments.

## 7. THE RE-PRICE

Route A priced at 3.3k lines with a band of 2.0 to 4.5k. The twelve-clause
table row carried 0.7 to 1.6k of that (`_build/lj-1.10-reprice.md:80-84`).
The row's per-clause anchor is about 40 lines. The measured hardest clause
takes 155 lines. The anchor is wrong for the hardest clause by a factor of
about four.

The twelve clauses are not uniform. The light clauses measured at 10 to 23
formula lines in `[LJ-1.2]` (`_build/lj-1.2-gate.md:27-45`). The existential
clause is the deep one. A fair table row sits between 0.7k and 1.9k. The
worst case is twelve times the hardest clause. The band top stands. The
center moves up by about 0.3 to 0.6k.

The measured rate does not rescue the survey. The probe prices the widest
unmeasured term at the top of its band. The re-price is Route A at about
3.6 to 3.9k, with the band top at 4.5k. The DD8 gate stands: the substrate
is measured now, and the measured price is above the gate's assumption.

## 8. LITERATURE USED

- `dev/literature/devlin-II5.md:209-256` (section 2.3): used. Item 2 is my
  statement 2, the witness inside the carrier. The K(u) shape guided the
  bound design.
- `_build/literature/dev2.txt:593-630`: used through the digest. Devlin
  binds every unbounded quantifier by K(u). My matrix does the same with the
  slot K.
- `dev/literature/devlin-errata.md`: skipped. The errata binds the
  satisfaction layer behind II.2.4. The probe measures the modern tree's
  coding, not the errata's content. WHY NOT: the errata states no bounded
  clause shape for this tree.

No other file under `dev/literature/` bears on the probe.

## 9. ARCHIVE USED

- `_build/lj-1.12-report.md:173-206` (section 6): the commissioning
  document. Read in full. Its two statements are the probe's gate.
- `_build/lj-1.2-gate.md:98-129` (section 5): the earlier NO-GO. It names
  the two missing bounds. My matrix bounds both by K.
- `_build/lj-1.2-gate.md:22-70` (section 2): the measured top-level rewrite
  rate. It anchors my light-clause expectation.
- `_build/lj-1.10-reprice.md:80-84`: the archive decode rate of about 40
  lines per clause. My measured hardest clause is 155 lines.
- `_build/l3.31-r2probe-report.md:153-171`: the retired route's
  level-sequence containment. The retired modules do not exist in this tree.
  WHY NOT deeper use: `L.Rud` and `LevelKit` are absent from the working
  tree.
- `_build/lj-1.12-report.md:226-232`: the T130 warning that the crossing
  must carry the internalized definable-powerset step. I accept it.
- `dev/LESSONS.md:2442-2460` (P-n) and `:2264-2320` (P-l): bind the rate
  and the variable-slot discipline.

## 10. WHAT I AM NOT SURE OF

The brief writes "hierL (Lset δ)". I read it as "hierL δ", the level
sequence below the ordinal δ. The literal reading needs `IsOrd (Lset δ)`,
which is false in general. My numbers rest on the first reading.

"Limit α" has no delivered predicate. I used the successor-closure
hypothesis plus `IsOrd α`. The closing pieces hold under that reading.

The equivalence between the certificate and the delivered clause is not
proved in the probe. The matrix's own decode closes. The equivalence leg
needs the bound construction and the vacuity arguments. I did not measure
that leg. The re-price treats it as row (c), the separate 0.3 to 0.8k
survey.

The statement-2 count of 37 lines counts only the closing pieces. The two
headline claims are unproved. Their cost is not in the count. A full
statement 2 may cost several hundred lines.

The probe files stay in `src/ProbeLJ115.agda` and `src/ProbeLJ115b.agda`.
They are untracked. I leave them as evidence.

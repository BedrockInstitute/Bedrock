# LJ-1.120 report: generic environment-set over an arbitrary arity

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100.

## 0. The verdict

The generic environment-set builds. The term is `Generic.envSetGen` at
`src/ProbeLJ1120A.agda:123`. It checks in 2.29 s cold at load 4.13.

The full `someEnv` obligation closes from the delivered companions once the
K-membership of the constructed set is supplied. The term is `wired` at
`src/ProbeLJ1120B.agda:71`. It checks in 1.94 s cold at load 4.50.

The one missing premise is still a hypothesis. `envSetK` at
`src/ProbeLJ1120B.agda:34` states it. The delivered `KFacts` record has no
field for it. Probe C measures that failure.

## 1. The numeral assumption

The delivered machine builds only over a numeral. The term is
`envSet : (n : ℕ) → S` at `src/L/Coding/EnvSet.lagda.md:183`. Its index type
is `Ix n = Fin n → ⟪ fst B ⟫` at `:122`. Its formula names the numeral `nn n`
at `:171`. The environment reader also requires the arity slot to be `# m` at
`src/L/Coding/Sound.lagda.md:262-264`.

The assumption is load-bearing for the delivered constructor. The
construction was generalized, not rebuilt from nothing. The generic index
type is `⟪ fst ar ⟫ × ⟪ fst B ⟫`, and the numeral `nn n` is replaced by the
arbitrary arity set `ar`.

## 2. The generic construction

Probe A defines `Generic (B ar : S)` at `src/ProbeLJ1120A.agda:64`.
It does three things.

First it bounds every pair of an arity member and a value member by one
stage. The term is `pairBound` at `src/ProbeLJ1120A.agda:75`.

Second it takes the power set of that stage. The term is `powamb` at
`:109`.

Third it separates the environments from that power set by the object-level
`envOverAt` description. The terms are `envFo` at `:118`, `envSetGen` at
`:123`, and `envSetGen-spec` at `:126`.

The adequacy is `Generic.Holds.holds` at `src/ProbeLJ1120A.agda:207`.
It proves the two directions of `envSetAt` for the constructed set.
This is the general version of `AmbientHolds` at
`src/L/Coding/Sound.lagda.md:262-284`.

## 3. The K-closure

The construction needs one closure of `K`. It needs the constructed set to
lie in `K` when the arity and the ambient set lie in `K`.

The telescope fact is `envSetK` at `src/ProbeLJ1120B.agda:34`. It is
conditional. It has the sound shape that `check-unbound-hyp.py` does not
flag.

`KFacts` does not supply it. The record is at
`src/L/Condensation.lagda.md:5940-5977`. Its fields close numerals, pairs,
and arity membership. It has no environment-set field. Probe C tries the
pair field and the arity field. Both fail.

The missing field is a new closure, not a derivation. The construction
uses separation and power set. `pairK` and `arityK` do not reach those.

## 4. The acceptance test

Probe B instantiates `Obligation` from `ProbeLJ1115A`. The generic
construction becomes `closure` at `src/ProbeLJ1120B.agda:47`. The
delivered `build` consumes it. The term is `wired` at `:71`.

The acceptance test passes in the exact sense the brief asks. Given
`envSetK`, the delivered `ArityK`, and the delivered `EnvInK`, `build`
produces the full `someEnv` obligation. No layout change was made.

## 5. The twenty five re-priced

Probe A has 208 total lines and checks in 2.29 s cold. Its rate is
0.0110 s per line. Probe B has 72 total lines and checks in 1.94 s cold.
Its rate is not a clean content rate because it imports Probe A.

The [LJ-1.115] report estimated the twenty-five wiring component at about
220 lines. At this probe's measured construction rate, 220 lines is about
2.4 s. That line count is not measured here. It is a projection, not a
price. The proof content of the twenty-five is still not measured.

## 6. Where this content belongs

The canonical home is `src/L/Coding/EnvSet.lagda.md`. The generic
constructor replaces the numeral constructor at `:183`. The adequacy
replaces `AmbientHolds` at `src/L/Coding/Sound.lagda.md:262`.

The K-closure belongs in the closure frame, not in `KFacts`. P-x forbids a
record field with a transparent built set. The frame shape at
`src/L/Condensation/TwelveAgree.lagda.md` is the right place.

## 7. C-39 section

One brief line blocked a route I can see.

The line "Do not edit any master" blocks the master edit that this content
needs. That is correct for this dispatch. The route stays open for the next
dispatch. The probe is the audit that the next dispatch needs.

No other brief line blocked a route.

## 8. Negatives classified

The delivered `KFacts` supplies `envSetK`: MEASURED FALSE.
`src/ProbeLJ1120C.agda:52` fails with `UnequalTerms`. The arity membership
is not the constructed-set membership.

The delivered `pairK` constructs the environment-set: MEASURED FALSE.
`src/ProbeLJ1120C.agda:51` is the attempt. It produces an L-pair, not the
separated set.

The generic construction is tower-free: MEASURED TRUE. Probe A imports no
tower-specific module beyond the L axioms. See section 9.

The full `someEnv` closes without any new hypothesis: INFERRED FALSE.
Probe B closes it with one new hypothesis. No term closes it without that
hypothesis.

## 9. DD4 answer

The generic environment-set is tower-free. It is coding machinery. The J
tower gets the whole closure family unchanged. That is the largest DD4 win
in this phase.

## 10. Measurements

One `agda` process at a time. `GHCRTS="-A64m -I0 -M8g"`. The cap was never
raised. Load is reported at each start.

| probe | result | seconds | load at start |
|---|---|---:|---:|
| A, generic construction | exit 0 | 2.29 | 4.13 |
| B, wired `someEnv` | exit 0 | 1.94 | 4.50 |
| C, K-closure refutation | exit 42 at `:52.45-48` | 1.11 | 4.30 |

`check-unbound-hyp.py` on A and B: clean. On C: clean.
`lint-agda.py` on A, B, and C: exit 0.
`check-fences.py --check`: clean, 87 masters.
`ledger.py --brief`: standing 28,432 lines over 85 masters.

No `make check` was run. No master was touched.

## ARCHIVE USED

- `_build/lj-1.115-report.md`, read WHOLE. TOOK the four properties and the
  acceptance wire.
- `_build/lj-1.113-report.md`, read WHOLE. TOOK the twenty-nine count and the
  canonical-home naming.
- `_build/lj-1.112-report.md`, read WHOLE. TOOK the frame context.
- `src/ProbeLJ1115A.agda`, read WHOLE. TOOK `EnvSetClosure` and `build`.
- `src/ProbeLJ1115B.agda`, read WHOLE. TOOK the two numeral walls.
- `src/L/Coding/EnvSet.lagda.md`, read WHOLE. TOOK the numeral construction.
- `src/L/Coding/Sound.lagda.md:100-300`, read. TOOK `AmbientHolds`.
- `src/L/Coding/Model.lagda.md:450-540, 1130-1160`, read. TOOK the readers.
- `src/L/Condensation.lagda.md:2860-3020, 5939-5980`, read. TOOK the
  transfer and `KFacts`.
- `src/ProbeLJ197A.agda`, read WHOLE. TOOK the refutation shape.
- `dev/LESSONS.md`, the rules cited in the brief, read WHOLE.
- `scripts/rules.py --for build`, read all statements.

## LITERATURE

Devlin builds the bounded satisfaction bound `K(u)` from finite sequences
over formulas, variables, and members. That is a numeral environment.
`dev/literature/devlin-II5.md:248-254`.

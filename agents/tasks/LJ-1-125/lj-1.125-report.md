# LJ-1.125 report: give envSetK a home in the frame

Status: COMPLETE. No commit, no push. ASD-STE100.

## 0. The verdict

envSetK is NOT REFUTED as I stated it. The premise barrier is MEASURED.
The non-refutation is INFERRED.

The frame is GREEN. The re-measured unsolved-meta count is 0, MEASURED,
beside 0.

## 1. Is envSetK refutable as stated

The new hypothesis is conditional. It has two premises. Each premise is a
membership of the K slot. The conclusion is a membership of the constructed
set.

The refutation attempt is in `src/ProbeLJ1125B.agda`. At B = ar = X, the two
premises are X ∈ X. The delivered `∈-irrefl` refutes that premise. The
premise barrier is MEASURED at `src/ProbeLJ1125B.agda:44-46`.

No cycle term is forced. The arbitrary frame supplies no numeral-K
membership for a second attempt. NOT REFUTED is INFERRED. It sets no
verdict.

## 2. The frame and the re-measured meta count

envSetK is a new telescope hypothesis of `TwelveAgree.AbstractFrame`. It
sits between `sucK` and `subK-un`. The statement is at
`src/L/Condensation/TwelveAgree.lagda.md:189-193`.

The import is `open import L.Coding.EnvSet {ℓ} lem using ( module Generic )`
at `src/L/Condensation/TwelveAgree.lagda.md:29`.

`LowerAgree` and `UpperAgree` do not need envSetK. They state the row facts
and `someEnv`, but they do not use the generic environment-set construction.
Only `TwelveAgree` states envSetK.

The master checks GREEN. `agda
src/L/Condensation/TwelveAgree.lagda.md` exits 0 in 27.926 s.

The instantiation probe is `src/ProbeLJ1125A.agda`. It starts from
`ProbeLJ1112A`. It adds envSetK to the extended consumer frame at
`src/ProbeLJ1125A.agda:323-327`. It supplies envSetK to the AbstractFrame
application at `src/ProbeLJ1125A.agda:440`. The application exits 0. Agda
reports no unsolved meta. The count is 0, MEASURED.

## 3. What supplies envSetK

Adding envSetK to the frame is a new obligation, not a discharge. I say so
in those words. The consumer must grow this hypothesis.

The construction that the hypothesis closes is `Generic.envSetGen` at
`src/L/Coding/EnvSet.lagda.md:456`. Its adequacy is
`AmbientHoldsGen.holds` at `src/L/Coding/Sound.lagda.md:287`.

The K-closure itself is not delivered in the tree. The supplier is a future
coding-model lemma. That lemma proves the constructed set lies in the K slot
from B ∈ K and ar ∈ K. It is not a `KFacts` field. P-x forbids that shape.
The record field wall is MEASURED at `_build/lj-1.109-report.md` section 2.

## 4. C-40 consumers

I ran the given `git grep -l` command. It lists four files. I verified the
list with `rg -n "L.Condensation.TwelveAgree|Condensation.TwelveAgree"
src/`. The two searches agree on the actual importer.

The complete set of masters that import `L.Condensation.TwelveAgree` is one
file. It is `src/Everything.lagda.md:373`. The given list also contains
`LowerAgree` and `UpperAgree`. Those two are self-matches on their own module
names. They do not import the changed master. The list is complete.

I checked every file from the given list. All are GREEN.

| consumer | import or self-match | result |
|---|---|---|
| `src/Everything.lagda.md` | `:373` import | exit 0, 4.442 s |
| `src/L/Condensation/LowerAgree.lagda.md` | self-match | exit 0, 3.161 s |
| `src/L/Condensation/UpperAgree.lagda.md` | self-match | exit 0, 2.257 s |
| `src/L/Condensation/TwelveAgree.lagda.md` | changed master | exit 0, 27.926 s |

No master applies `AbstractFrame`. `rg -n "AbstractFrame" src/` finds only
the defining file. The probe is the applier.

## 5. What check-unbound-hyp.py says

I ran `.venv/bin/python scripts/check-unbound-hyp.py --check` on the touched
master and both probes.

The master flags the two known hypotheses:

| line | name | flag |
|---|---|---|
| `src/L/Condensation/TwelveAgree.lagda.md:88` | `valK` | rule 1, `yc` |
| `src/L/Condensation/TwelveAgree.lagda.md:91` | `valK-un` | rule 1, `yc` |

envSetK is NOT flagged. It has premises. Its conclusion subject is
constrained by B and ar.

The two probes are standalone `.agda` files. The checker reads only Agda
fences. It reports clean for them, but that clean is vacuous.

## 6. C-39 section

No brief line blocked a route I used.

The P-x line forbids a `KFacts` field. That route is MEASURED as a wall at
`_build/lj-1.109-report.md` section 2. I took the open route, a telescope
fact.

The line "Do NOT run make check" did not block the C-40 consumer checks. I
checked each consumer with `agda`.

## 7. Negatives classified

envSetK is refutable as stated: INFERRED FALSE. The premise barrier is
MEASURED. No refutation term was found. This negative sets no verdict.

The frame is green: MEASURED TRUE. The exit code is 0.

The unsolved-meta count is 0: MEASURED TRUE. The exit code is 0.

The addition is a new obligation: MEASURED TRUE. The consumer grew the
hypothesis and the application supplied it.

No P-x wall occurred: MEASURED TRUE. The changed master checked in 27.926 s
with no heap event.

## 8. DD4 answer

envSetK at the frame keeps the construction tower-free. The hypothesis type
mentions `Generic.envSetGen`. That construction imports the L axioms, the L
stage, and the V hierarchy. It imports no condensation tower and no rud
tower. The J tower inherits the closure family unchanged. It instantiates
the coding closure; it does not rebuild it.

## 9. Measurements

One `agda` process at a time. `GHCRTS` is set to `-M8g`. The cap was never
raised. Load is reported at each start.

| run | exit | seconds | load at start |
|---|---:|---:|---:|
| `TwelveAgree.lagda.md` | 0 | 27.926 | 5.09 |
| `ProbeLJ1125A.agda`, warm | 0 | 3.246 | 4.81 |
| `ProbeLJ1125B.agda` | 0 | 2.236 | 4.95 |
| `Everything.lagda.md` | 0 | 4.442 | 5.73 |
| `LowerAgree.lagda.md` | 0 | 3.161 | 5.71 |
| `UpperAgree.lagda.md` | 0 | 2.257 | 5.69 |

The first `ProbeLJ1125A` run was cold. It exited 0 in 11.513 s. The load at
that start was not captured. The warm run above carries the load.

Checks:

| check | result |
|---|---|
| `check-fences.py --check` | clean, 87 masters |
| `ledger.py --brief` | standing 28,611 lines over 85 masters, measured from HEAD |
| `lint-agda.py --check` on touched files | exit 0 |
| `lint-prose.py --check` on touched files | exit 0 |
| `check-unbound-hyp.py --check` on touched files | section 5 |

No `make check` was run.

## ARCHIVE USED

- `_build/lj-1.120-report.md`, read WHOLE. TOOK `envSetK` at `:34` and the
  acceptance wire.
- `_build/lj-1.122-report.md`, read WHOLE. TOOK the landed master versions
  and the tower-free DD4 answer.
- `_build/lj-1.115-report.md`, read WHOLE. TOOK the four properties and the
  missing `envSetK`.
- `_build/lj-1.109-report.md` section 2, read. TOOK the P-x wall and the
  successor closure supplier.
- `_build/lj-1.112-report.md`, read WHOLE. TOOK the zero-meta instantiation
  and the consumer frame shape.
- `src/ProbeLJ1112A.agda`, read WHOLE. TOOK the extended consumer frame and
  the AbstractFrame application to re-point.
- `src/ProbeLJ197A.agda`, read WHOLE. TOOK the refutation shape.
- `src/L/Condensation/TwelveAgree.lagda.md`, read WHOLE. TOOK the current
  telescope.
- `src/L/Coding/EnvSet.lagda.md:396-540`, read. TOOK `Generic.envSetGen` at
  `:456`.
- `src/L/Coding/Sound.lagda.md:262-330`, read. TOOK
  `AmbientHoldsGen.holds` at `:287` and `NumeralFromGeneric.derived` at
  `:300`.
- `dev/LESSONS.md`, the cited entries read WHOLE: P-x, C-38 as extended,
  C-39, C-40, C-35, C-36, D-29, D-30, P-i, P-l, P-m, P-n, P-w, P-o, P-q,
  P-t, P-u, P-v, P-c, R-36, C-31, C-32, C-33, C-34, C-37, D-1, D-8, D-26.
- `scripts/rules.py --for build` and `--for rewrite`, read all statements.

## LITERATURE

Banked. Nothing spent.

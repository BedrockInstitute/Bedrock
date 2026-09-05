# LJ-1.115 report: probe someEnv, the K-closure family's widest term

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.115-report.md`.

## 0. The verdict

**someEnv DOES NOT BUILD from the delivered machinery.**  The
construction needs ONE closure property of K that nothing supplies:
the environment-set over an arbitrary arity `ar ∈ K`, with values in
the ambient slot, exists, satisfies the machine's `envSetAt`, and lies
in K (`EnvSetClosure`, `src/ProbeLJ1115A.agda:91-97`).  The rest of
the obligation builds: `build` at `src/ProbeLJ1115A.agda:123-134` is
GREEN, and it wires the delivered `EnvSet.back` transfer at the
And-row layout.

The term I could not write is the closure's construction.  The two
walls are measured at `src/ProbeLJ1115B.agda:64` (1.60 s, load 3.91)
and `:72` (2.63 s, load 4.48).  What the machine would have to
provide is a generic environment-set over an arbitrary arity set,
plus its K-closure statement.  Section 2 names both exactly.

The abort criterion's second case applies.  The finding is the one the
brief names as the most important: `someEnv` is the only one of the
twenty-eight that is not a closure, and its missing content is a
construction, not a closure of a given satisfier.

## 1. The term

The obligation is `someEnvDef` at
`src/L/Condensation/LowerAgree.lagda.md:51-58`; the frame carries it at
`src/L/Condensation/TwelveAgree.lagda.md:179`.  The probe states it
generically at the K slot as `Obl`
(`src/ProbeLJ1115A.agda:59-65`), with `KS = lookup (suc^6 K) γ`.

The reduction `build : EnvSetClosure → ArityK → EnvInK → Obl`
(`src/ProbeLJ1115A.agda:123-134`) is the decisive miniature.  It
decomposes the obligation into two halves:

1. The bounded half is the delivered transfer.  `envHypB2 {11+n} zero
   (suc^6 K)` unfolds to `envSetB zero (suc^5 zero) (suc^7 zero)
   (suc^13 K)` at the And-row list `E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ`.
   `EnvSet.back` (`src/L/Condensation.lagda.md:2998-3000`) proves
   `envSetAt → envSetB` under `arityK`, `E ∈ K`, `ar ∈ K`.  `build`
   instantiates that transfer at the And-row layout.
2. The construction half is `EnvSetClosure`.  It is the only piece
   with no delivered supplier.

The failed term is the closure's construction.  The delivered builder
`envSet : (n : ℕ) → S` builds over a numeral only
(`src/L/Coding/EnvSet.lagda.md:183`).  The model's `env` and `cons`
constructors are numeral-indexed too
(`src/L/Coding/Environment.lagda.md:84-85`, `:484`).  The only
delivered `envSetAt`-satisfaction supplier, `AmbientHolds`, demands
the arity slot equal `# m`
(`src/L/Coding/Sound.lagda.md:262-284`, the `qd` premise at `:264`).
The probe records both walls as complete ill-typed terms:

1. `numeralise` at `src/ProbeLJ1115B.agda:63-64`.  The premise
   `ar ∈ K` does not give `ar ≡ # m`.  Agda rejects the term with
   `UnequalTerms` at `:64.23-26`.
2. `envSet-mem` at `src/ProbeLJ1115B.agda:69-71`.  No premise states
   `envSet B 0 ∈ K`.  Agda rejects the term with `UnequalTerms` at
   `:72.25-28` in the measured run, where attempt 1 was hidden.  The
   final file fails at attempt 1 first.

What the machine would have to provide: a generic environment-set
over an arbitrary arity set, generalizing `envSet : ℕ → S`, plus the
closure `envSetK` that the result lies in K.  The closure must be a
telescope fact of the frame, not a `KFacts` field (P-x,
`dev/LESSONS.md:3564-3601`); the frame's `envK-*` facts already take
that shape (`src/L/Condensation/TwelveAgree.lagda.md:98-117`).

## 2. The closure properties of K the construction needs

The construction needs exactly four properties.  Three are supplied.
One is not.

1. **`envSetK`** (`EnvSetClosure`): K closed under the
   environment-set over an arbitrary arity in K, values in the
   ambient slot, with the machine's `envSetAt` satisfaction at the
   And-row layout.  **NOT SUPPLIED.**  The machine builds over
   numerals only (`EnvSet.lagda.md:183`); `AmbientHolds` demands the
   arity equality (`Sound.lagda.md:262-284`); the `KFacts` record has
   no environment-set field (`Condensation.lagda.md:5939-5980`); the
   frame's `envK-*` facts close a GIVEN satisfier and construct none
   (`TwelveAgree.lagda.md:98-117`).
2. **`arityK`**: the transitive closure of K.
   **SUPPLIED.**  It is a delivered `KFacts` field
   (`Condensation.lagda.md:5974-5975`), and the frame derives its own
   from `transK` (`TwelveAgree.lagda.md:152-154`, `:218-221`).
3. **`envInK`** at the And-row layout.  **SUPPLIED** as the frame's
   `envInK-imp` (`TwelveAgree.lagda.md:130-133`), which has exactly
   the And-row layout.  It is one of the twenty-five closure facts.
   The transfer itself does not use it (`Condensation.lagda.md:2998-3000`);
   the `EnvSet` module demands it as a parameter.
4. **The bounded transfer** `envSetAt → envHypB2`.  **DELIVERED** as
   `EnvSet.back` (`Condensation.lagda.md:2998-3000`), wired at the
   And-row layout by `build` (`ProbeLJ1115A.agda:123-134`).

The decision: the construction needs exactly ONE closure beyond the
twenty-five.  The family stays the twenty-five's five-to-seven shapes
(`_build/lj-1.113-report.md:140`) plus one construction closure.
**It is NOT fifteen.**

## 3. The re-priced family

The measured rate replaces the hypothesis.  Probe A is 134 in-fence
lines and checks cold in 2.57 s total (1.48 s user), load 4.08 at
start.  The rate is 0.019 s per line, inside P-m's parameterized band
(`dev/LESSONS.md:2460-2482`) and measured at this site this time.

The statement and wiring component of one lemma shape at its layout is
about 32 lines: the closure statement (7), the two companion
statements (12), and the `build` wiring (13).  The family's wiring
component is the twenty-five's five-to-seven shapes plus `someEnv`.
At the seven-shape end it is about 220 in-fence lines, about 4.2 s
cold at the measured rate.

The closure proof content is not measured here.  The abort criterion
forbids building the other twenty-five.  The twenty-five's proofs
reduce through the delivered adequacy theorems, which is still the
reading of `_build/lj-1.113-report.md:148-163`; the `envSetK`
construction is a new coding-model lemma, not a closure.  The old
250-line and 3-to-5-second figure is replaced: its wiring part is now
measured at about 220 lines and 4.2 s, and its proof part is the
unfunded content this gate was built to price.

## 4. The C-39 section

One brief line blocked a route I can see.

1. "Do not edit anything under `src/L/Coding/`, read only" blocks the
   canonical home of the missing construction.  The generic
   environment-set over an arbitrary arity, and the `envSetK` closure
   statement, live in `src/L/Coding/EnvSet.lagda.md` and
   `src/L/Coding/Model.lagda.md`, the home the previous dispatch
   already named (`_build/lj-1.113-report.md:181-184`).  The
   prohibition is right for this dispatch, which is a reading and a
   probe.  The route stays open for the build that funds it.

No other brief line blocked a route.  The write scope
(`src/ProbeLJ1115*.agda`) cost nothing.  The "do not build the other
twenty-five" line blocked nothing the task needs; the abort criterion
is followed.

## 5. Negatives classified

1. `EnvSetClosure` is derivable from the delivered `envSet`:
   **MEASURED FALSE.**  Attempt 1 at
   `src/ProbeLJ1115B.agda:64` fails with `UnequalTerms`; the
   membership premise does not give the numeral equality
   `AmbientHolds` needs.  Attempt 2 at `:72` fails with
   `UnequalTerms`; no premise states `envSet B 0 ∈ K`.
2. The delivered machinery constructs the environment-set over an
   arbitrary arity: **INFERRED FALSE.**  The two delivered routes are
   measured above.  The sweeping claim rests on the reading that no
   other construction exists in the coding model
   (`src/L/Coding/EnvSet.lagda.md:183`,
   `src/L/Coding/Sound.lagda.md:262-284`).
3. The rest of `someEnv` builds given `EnvSetClosure`, `ArityK` and
   `EnvInK`: **MEASURED TRUE.**  `build` is green at
   `src/ProbeLJ1115A.agda:123-134`.
4. `arityK` is supplied: **MEASURED TRUE** as the delivered field at
   `Condensation.lagda.md:5974-5975`.
5. `envInK` at the And-row layout is supplied: **MEASURED TRUE** as
   the frame's `envInK-imp` at `TwelveAgree.lagda.md:130-133`.  Its
   own content is one of the twenty-five and is not delivered:
   **INFERRED FALSE** by the `_build/lj-1.113-report.md:44`
   classification.
6. `someEnv` builds from the delivered machinery:
   **MEASURED FALSE** at the two walls of probe B.  The verdict
   combines the measured walls with the inferred reading of the whole
   coding model.  A negative that rests on an inference alone sets no
   verdict; this negative rests on two measured walls.

## 6. The DD4 answer

`someEnv` is the construction side, and it falls on the CODING half.
The construction is the environment-set over an arbitrary arity.  It
is coding-model content (`src/L/Coding/EnvSet.lagda.md`), and the
closure it needs (`envSetK`) is the same shape as the twenty-five's
`envK-*` closures.  The tower supplies only the concrete K slot and
the three memberships.

The closure family it prices is coding, shared by both proofs.  The J
tower repeats the instantiation, not the construction.  This sharpens
the previous split, which had put `someEnv` in the tower half
(`_build/lj-1.113-report.md:232`).  The tower half is `t0eq`, `t1eq`,
`t0K` and the memberships only.

## 7. Measurements

One `agda` process at a time, `GHCRTS="-A64m -I0 -M8g"`, the cap never
raised, each run started after the previous exited.  Load averages are
reported at each start.

| probe | file:line | result | seconds | load at start |
|---|---|---:|---:|---:|
| A, green `build` | `src/ProbeLJ1115A.agda:123-134` | exit 0 | 2.57 (1.48 user) | 4.08 |
| B, attempt 1 | `src/ProbeLJ1115B.agda:64` | exit 42, `UnequalTerms` at `:64.23-26` | 1.60 (1.45 user) | 3.91 |
| B, attempt 2 | `src/ProbeLJ1115B.agda:72` | exit 42, `UnequalTerms` at `:72.25-28` | 2.63 (1.50 user) | 4.48 |

For attempt 2's run, attempt 1 was hidden in the file.  Both attempts
are active in the final file; the final state fails at attempt 1.

No heap exhaustion, no kill, no wall.  The probes are scratch under
`src/`, gitignored by design.

`.venv/bin/python scripts/check-unbound-hyp.py --check
src/ProbeLJ1115A.agda src/ProbeLJ1115B.agda`: **clean (2 file(s))**,
exit 0.  None of the probe's hypotheses is a premise-free conclusion
(rule 1) or an unconstrained premise object (rule 2).  The closure and
its companions all carry their membership premises.

`.venv/bin/python scripts/lint-agda.py --check src/ProbeLJ1115A.agda
src/ProbeLJ1115B.agda`: exit 0.  The failing probe carries its failing
terms without interaction holes, so the lint sees no forbidden
construct.  The failures are type errors, which are the measurements.

`.venv/bin/python scripts/lint-prose.py --check
_build/lj-1.115-report.md`: exit 0.

`.venv/bin/python scripts/ledger.py --brief` (the admissible size
figure): standing 28,434 lines over 85 masters, measured from HEAD
`079c04e`; thresholds SUSPENDED per the ledger header.

No `make check` was run (brief prohibition).  No master was touched:
`src/L/Coding/`, `src/L/Condensation/`, `src/V/`,
`src/Everything.lagda.md` untouched.  No commit, no push.
The working tree carries the sibling's in-flight edit to
`src/L/BoundedSubset.lagda.md`; it predates this dispatch and is not
mine.

## ARCHIVE USED

- `_build/lj-1.113-report.md`, read WHOLE.  TOOK the 29-fact table
  (`:29-60`), the widest-term naming (`:148-163`), the 250-line price
  hypothesis (`:144-147`), and the DD4 split (`:231-244`).
- `_build/lj-1.112-report.md`, read WHOLE.  TOOK the frame context and
  the `sucK` addition.
- `src/ProbeLJ1112A.agda`, read WHOLE.  TOOK the extended frame's 29
  parameters (`:211-344`) and the `someEnv` shape at `:300`.
- `src/ProbeLJ197A.agda`, read WHOLE.  TOOK the refutation shape and
  the regularity machinery.
- `src/L/Condensation/LowerAgree.lagda.md:35-75`, read.  TOOK
  `someEnvDef` at `:51-58`.
- `src/L/Condensation/TwelveAgree.lagda.md:45-330`, read.  TOOK the
  frame's `envK-*` at `:98-117`, `envInK-imp` at `:130-133`,
  `transK` at `:152-154`, the derived `arityK` at `:218-221`, and
  `someEnv` at `:179`.
- `src/L/Condensation.lagda.md`, read `envBndGen` (`:526-543`),
  `envSetB` (`:564-566`), `envHypB2` (`:651-655`), the `EnvSet`
  module (`:2882-3018`), the row `back` site (`:3440-3480`), `KFacts`
  (`:5939-5980`), `AndAgree`/`OrAgree` (`:3488-3580`), and
  `SatGraphAgree` (`:6682-6768`).
- `src/L/Coding/Model.lagda.md`, read the environment machinery:
  `envOverAt` (`:483-486`), `envOverAt-transport` (`:517-523`),
  `envSetAt` (`:1149-1150`).
- `src/L/Coding/EnvSet.lagda.md`, read WHOLE.  TOOK the numeral-only
  construction: `envSet : (n : ℕ) → S` at `:183`, the readers at
  `:375-382`.
- `src/L/Coding/Sound.lagda.md:125-300`, read.  TOOK `AmbientHolds`
  at `:262-284` and its arity-equality premise at `:264`.
- `src/L/Coding/Environment.lagda.md:80-90, 480-490`, read.  TOOK the
  numeral-indexed `env` and `cons`.
- `src/L/Coding/Bridge.lagda.md:175-205` and
  `src/L/Coding/Sat.lagda.md:140-150`, read.  TOOK the other
  environment-set uses, both numeral-only.
- `src/L/Axioms/Full.lagda.md:140-150`, read.  TOOK
  `hasSeparationL`, the only delivered set-builder.
- `src/FOL/Manipulation/Renaming.lagda.md:50-52, 91-148`, read.
  TOOK the renaming machinery and its non-applicability to the
  And-row layout, which led to stating the closure at the consumer's
  layout in the frame's own style.
- `dev/LESSONS.md`, C-38 as extended (`:3427-3520`), C-39
  (`:3521-3563`), P-x (`:3564-3601`), P-l (`:2305-2482`), P-m
  (`:2460-2482`), D-30 (`:3332-3380`), D-1 (`:1038`), D-8 (`:1377`),
  read WHOLE.  TOOK the satisfiable-telescope standard, the
  prohibition-priority rule, the field-type wall, and the content
  class rate.
- `scripts/rules.py --for build` and `--for probe`, read all
  statements.

## LITERATURE

Banked; nothing spent.

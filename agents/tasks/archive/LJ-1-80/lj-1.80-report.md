# LJ-1.80: build a KFacts value at the hull, or write the term you cannot

Status: IN PROGRESS, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.80-report.md`.

## 0. THE VERDICT

IN PROGRESS. The candidate value typechecks in the probe
(`src/ProbeLJ180A.agda`, green at the C-12 cap, about 2.5 s warm
dependencies). It is being transplanted into
`src/L/BoundedSubset.lagda.md`. The elaboration wall found during
bisection: unannotated `Sum.rec` branch lambdas over a `suc∈or≡`
disjunction did not finish; explicit branch types fixed it (I-5's
class).

## 1. THE CANDIDATE VALUE

The record `KFactsNS.KFacts`
(`src/L/Condensation.lagda.md:5760-5768`) has 27 fields. The candidate
site is:

- `K` slot: `LsetS lam ordλ`, the limit stage as a constructible set.
- `A` slot: `LsetS α ordα`, the generator level as a constructible set.
- `Nk` slots: `numeralL k`, the twelve constructible numerals.
- `γ`: the 14-element environment `A ∷ K ∷ numeralL 0 ∷ ... ∷ numeralL 11 ∷ []`.

The candidate value lives in a new module in
`src/L/BoundedSubset.lagda.md` (the site the brief names), parameterized
by `lam`, `ordλ`, `succλ`, `α`, `ordα`, `α∈λ`, `α∉ω`.

### 1.1 Field by field

| field | supplier | status |
|---|---|---|
| `tagEq0..11` | `numFrom-spec` (the slot at `2 + k` holds `numeralL k`) | GREEN in probe |
| `numK0..11` | numerals in `Lset lam` (`ord∈Lset-suc`, `#∈ω`, `Lset-mono`) | GREEN in probe |
| `innerK`, `innerPairK`, `pairK` | stage pair closure (`pr∈Lset-suc` + `Lset-out` + trichotomy + `succλ`) | GREEN in probe |
| `carrierK` | `Lset-mono` (`α ∈ lam`) | GREEN in probe |
| `arityK` | `layer-trans (Lset-layer lam)` | GREEN in probe |

## 2. THE HULL SITE, AND THE TERM NOT YET WRITTEN

PENDING. The brief points at the Skolem hull `M` (`HullStage`,
`src/L/BoundedSubset.lagda.md:902-915`) or its collapse `C.πX`. The
slots of `KFacts` are constructible sets (`S` is the carrier of `𝒮ʟ`),
and no `isL` certificate for `M` or `πX` is delivered. That is the
candidate wall; it is being checked against the delivered tree.

## 3. DD4

PENDING. The candidate construction is generic in the stage and the
limit-ordinal machinery.

## 4. NEGATIVES AND THEIR STATUS

1. PENDING.

## 5. ARCHIVE USED

- `_build/lj-1.79-report.md`, read WHOLE. TOOK the repaired field forms
  and the supply-point table.
- `_build/lj-1.77-report.md`, read WHOLE. TOOK the refutation that no
  longer applies and the blast radius.
- `_build/lj-1.78-report.md`, read WHOLE. TOOK the guarded-shape recipe.
- `_build/lj-1.52-report.md` and `_build/lj-1.51-report.md`, read WHOLE.
  TOOK the hull's delivered properties and the surviving
  `levelIn`/`cover` obligations.
- `dev/LESSONS.md`: C-38 as extended (`:3427-3520`), C-35
  (`:3200-3242`), C-36 (`:3178-3224`), D-29 (`:3242-3284`), D-30
  (`:3332-3380`), read WHOLE.
- `archive/rud-route/`, SHAPE only. Took nothing.

## 6. LITERATURE USED

`dev/literature/devlin-II5.md` Step C and
`_build/literature/dev2.txt:1372-1385`: PENDING the one-line answer.

## 7. GATES

PENDING.

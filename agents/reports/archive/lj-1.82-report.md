# LJ-1.82: supply KFacts to the chain, at the stage

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.82-report.md`.

## 0. THE VERDICT

**The KFacts VALUE reaches the chain's first module, and the chain
blocks at that module.** `src/ProbeLJ182A.agda` instantiates
`ShapesAgree` with the stage's `kfacts` value and checks GREEN at the
C-12 cap. The instantiation receives the value at `ShapesAgree`'s
`f` parameter (`src/ProbeLJ182A.agda:117-121`).

The first unsupplied hypothesis is `ShapesAgree`'s code-set datum:
the value `C` and the facts `compK`/`unCompK`
(`src/L/Condensation.lagda.md:5816-5835`). The stage supply contains
no code set. `KFacts`' twenty-nine fields
(`src/L/Condensation.lagda.md:5737-5768`) mention only `A`, `K` and
`N0..N11`. Nothing names a code set or its decomposition. The
brief's "twenty-seven" is stale: the measured field count is
twenty-nine.

**The association mismatch is real but it is NOT the first blocker.**
The composer's `twelveB` is `p0b ∧̇ p1b`
(`src/L/Condensation/TwelveAgree.lagda.md:271`), a conjunction of two
six-row chains, while `SatGraphB.twelveB` is one right-nested chain of
twelve (`src/L/Condensation.lagda.md:2233-2256`). The chain stops at
`ShapesAgree` before it reaches the mismatch.

## 1. HOW FAR THE SUPPLY REACHED

The starting value is `kfacts` (`src/ProbeLJ180A.agda:186-226`), the
stage's `KFacts` at `K = LsetS lam`, `A = LsetS α`, with all
twenty-nine fields. `src/ProbeLJ182A.agda` imports it as
`P180.StageKFacts` (`:45-46`).

The value extends to the chain frames by `KFactsCons`
(`src/L/Condensation.lagda.md:5777-5814`). The probe builds and
checks:

| value | frame env | module whose KFacts slot it serves | probe lines |
|---|---|---|---|
| `kfacts` | 14 elements: `A ∷ K ∷` twelve numerals | the base record | `ProbeLJ180A.agda:186-226` |
| `f1` | 15 elements: `c ∷ γ` | `ShapesAgree`, `ClosedAgree`, `ShapedAgree`, `WitnessAgree` | `ProbeLJ182A.agda:67-71` |
| `f3` | 17 elements: `c3 ∷ c2 ∷ c1 ∷ γ` | `SatGraphAgree`, `LeafAgree` | `ProbeLJ182A.agda:75-101` |

`f1` and `f3` are MEASURED: the probe checks them green at the C-12
cap (section 8). The deeper modules' KFacts slots live at these
arities by their telescopes (`ClosedAgree` at
`src/L/Condensation.lagda.md:6098-6110`, `ShapedAgree` at `:6198`,
`WitnessAgree` at `:6224`, `SatGraphAgree` at `:6476-6484`,
`LeafAgree` at `:6705-6713`). MEASURED by reading.

The chain instantiation is written for the first module only:
`module First` (`src/ProbeLJ182A.agda:104-124`) applies `ShapesAgree`
with the value `f1 c` at its `f` slot (`:117-121`). `out-check`
(`:123-124`) forces the application to elaborate. The application is
genuinely checked: swapping `compK` and `unCompK` makes Agda reject
the application at `:119` (MEASURED, section 8). The four remaining
module applications are not written. The abort criterion says stop at
the first blocker, and the first blocker sits inside `ShapesAgree`.

## 2. THE FIRST UNSUPPLIED HYPOTHESIS

`ShapesAgree`'s telescope
(`src/L/Condensation.lagda.md:5815-5835`) is, in order: `C : S`, the
slots, the env, `f : KFacts`, `compK`, `unCompK`. The probe supplies
the slots, the env, and the value `f1 c` at `f`. It cannot supply `C`
or `compK`/`unCompK`.

`compK` states: for `c ∈ C` with the code shape
`c = pr N (pr #k (pr a b))`, the components `N`, `a`, `b` lie in the
K-slot (`src/L/Condensation.lagda.md:5822-5829`). `unCompK` is the
unary shape (`:5830-5835`). Their premise quantifies over `C`, and
nothing in `KFacts` or in the stage construction relates `C` to `K`.

The term that could not be written is a `compK` value at the stage.
`KFacts`' fields never mention a code set (MEASURED:
`src/L/Condensation.lagda.md:5737-5768`). The stage construction
(`src/ProbeLJ180A.agda`) builds exactly those fields. No delivered
term chooses the code set or proves its K-decomposition. That no term
builds `compK` from the stage supply is INFERRED: the stage data
constrain only `A`, `K` and the numerals, and `compK`'s conclusion
needs a `C`-to-`K` fact the supply does not contain.

This is the "something earlier" the brief invited. It is NOT the
association bridge. The bridge sits at `SatGraphAgree`/`LeafAgree`,
downstream of `ShapesAgree`.

## 3. THE ASSOCIATION MISMATCH

**Confirmed real, MEASURED by reading both formulas.**

`SatGraphB.twelveB` is one right-nested chain of twelve conjuncts
(`src/L/Condensation.lagda.md:2233-2256`).

The composer's `twelveB` is `p0b ∧̇ p1b`
(`src/L/Condensation/TwelveAgree.lagda.md:271`), where `p0b` is
`LowerAgree.sixB`, a right-nested chain of six
(`src/L/Condensation/LowerAgree.lagda.md:226-248`), and `p1b` is
`UpperAgree.sixB`, another right-nested chain of six
(`src/L/Condensation/UpperAgree.lagda.md:216-238`). As `Formula`
terms, the composed formula and `SatGraphB.twelveB` are different.

`SatGraphAgree` and `LeafAgree` take `twelve-out`/`twelve-back`
against `SatGraphB.twelveB` exactly
(`src/L/Condensation.lagda.md:6486-6493` and `:6729-6736`). The
composer's `out`/`back` target its own `twelveB`. The bridge would be
a re-pairing of the twelve conjuncts: twelve projections, eleven
pairings, both directions. The `back` direction needs the same glue
on its source.

Does the tree deliver a satisfaction-level associativity for `∧̇`?
**No named lemma.** The only `assoc` hits in `src/` are list
`++-assoc` in `src/FOL/Count.lagda.md:275-277`. `src/Base/Truth.lagda.md:32`
states the truth-algebra operations carry no associativity laws.
MEASURED by search. The glue itself is a re-association of pairs of
propositions, which cubical hProp extensionality supports
(`Cubical.Functions.Logic.⇔toPath`). It is writable by hand.
INFERRED: the chain blocked before it, so no glue was built or
measured.

The mismatch was not reached as an instantiation. The type-level
comparison above is the measurement.

## 4. THE DD4 ANSWER

**The supply is generic in the stage.** The `KFacts` construction is
parameterized by the stage data `lam`, `ordλ`, `succλ`, `α`, `ordα`,
`α∈λ`, `α∉ω` (`src/ProbeLJ180A.agda:32-38`). `KFactsCons` extends the
value to any frame arity. The chain modules and the composer are
slot-generic. A J tower with its own stage closure supplies its own
`KFacts` the same way, through the same record and the same cons
extension. The J side is INFERRED: no J tower exists in this tree.

The code-set data is NOT part of the supply. `C`, `compK`, `codesK`,
`entryK`, `witK` and the other frame facts are per-site content. The
L tower's stage does not deliver them. The J tower must supply its
own, exactly as it supplies its own `levelIn` and `cover`
(`_build/lj-1.81-report.md:123-125`).

## 5. NEGATIVES AND THEIR STATUS

1. "The KFacts value reaches the chain's first module":
   **MEASURED TRUE**. The `ShapesAgree` application receives `f1 c`
   at its `f` slot (`src/ProbeLJ182A.agda:117-121`), green at the
   C-12 cap.
2. "The value reaches the deeper modules' arities": **MEASURED
   TRUE** for the cons values `f1` and `f3`
   (`src/ProbeLJ182A.agda:67-71`, `:75-101`). The deeper module
   applications were not written, because the chain blocks first.
3. "The chain can be completed from the stage supply alone":
   **MEASURED FALSE at its first module**. `ShapesAgree` carries
   `compK`/`unCompK` beyond `KFacts`
   (`src/L/Condensation.lagda.md:5822-5835`), and `KFacts` contains no
   code-set datum (`:5737-5768`).
4. "No term builds `compK` from the stage supply": **INFERRED**. The
   stage data constrain only `A`, `K` and the numerals. This negative
   sets no verdict on its own; negative 3 carries the verdict.
5. "The association mismatch is the first blocker": **MEASURED
   FALSE**. `ShapesAgree` precedes `SatGraphAgree` in the chain and
   carries the first unsupplied hypothesis.
6. "The association mismatch exists": **MEASURED TRUE**. The
   composer's `twelveB = p0b ∧̇ p1b`
   (`src/L/Condensation/TwelveAgree.lagda.md:271`) is not
   `SatGraphB.twelveB` (`src/L/Condensation.lagda.md:2233-2256`).
7. "The tree delivers satisfaction-level `∧̇` associativity":
   **MEASURED FALSE** as a delivered lemma. The re-pairing glue is
   writable (INFERRED).

## 6. ARCHIVE USED

- `src/ProbeLJ180A.agda`, read WHOLE. TOOK `kfacts`
  (`:186-226`), the `StageKFacts` parameterization (`:32-38`) and the
  field suppliers.
- `_build/lj-1.81-report.md`, read WHOLE. TOOK the consumer chain
  and the site reading: the `K` slot is the bound, never the hull
  (`:1`), the six masters' `KFacts` parameters (`:40-53`).
- `_build/lj-1.79-report.md`, read WHOLE. TOOK the guarded field
  forms and the supply-point table (`:1`).
- `_build/lj-1.76-report.md`, read WHOLE. TOOK the three composer
  masters, the 69-fact telescope and the split shape (`:1`).
- `_build/diag-twelve-row-math.md` section 1, read WHOLE. TOOK the
  association finding: the composed formula is re-associated relative
  to `SatGraphB.twelveB` (`:1a`).
- `dev/LESSONS.md`, read C-38 (`:3427-3520`), C-35 (`:3200-3242`),
  C-36 (`:3284-3332`), P-w (`:3094-3199`), D-29 (`:3242-3284`),
  D-30 (`:3332-3380`), whole. TOOK the discharge standard, the
  untested-block law, the write-the-term rule, the copy-at-use
  amendment, and the price-what-the-consumer-needs rule.
- `archive/rud-route/`, SHAPE only. Took nothing. WHY NOT more:
  `[LJ-1.11]` ruled the retired route's condensation target
  classically false, and the brief forbids taking a price from it.

## 7. LITERATURE USED

Banked. `[LJ-1.81]` answered what Devlin's bounding set is. This
dispatch spends nothing on it.

## 8. GATES

- `scripts/check-fences.py --check`: clean, 87 masters.
- `scripts/lint-prose.py --check` on `_build/lj-1.82-report.md` and
  `src/ProbeLJ182A.agda`: exit 0.
- `scripts/lint-agda.py --check` on `src/ProbeLJ182A.agda`: exit 0.
- `src/ProbeLJ182A.agda`: GREEN at the C-12 cap
  (`GHCRTS=-M8g`), one process. 1.85 s user, 2.79 s wall on the
  final run. Load average during the runs: 4.16 to 5.05 (1 minute),
  four users. The machine was NOT quiet.
- The swap control: `compK` and `unCompK` reversed fails at
  `src/ProbeLJ182A.agda:119` with a type mismatch (exit 42),
  confirming the application is elaborated. MEASURED.
- Masters: all green or untouched. `git status` is clean; the probe
  and this report are gitignored
  (`.gitignore:2`, `.gitignore:22`). HEAD `eae5033` on
  `two-tower-bridge`, unchanged.
- No `make check`. No commit, no push.

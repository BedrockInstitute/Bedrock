# LJ-1.94: build the ambient Hartogs cardinal, and end at the consumer

tier: codex (default)

## STATUS

COMPLETE. The abort criterion's first branch fires: `cardκ` receives a
value at the [LJ-1.90] site shape. The probe is `src/ProbeLJ194A.agda`,
GREEN at the C-12 cap, one process. No master was touched. No commit,
no push. The report is `_build/lj-1.94-report.md`.

## 0. THE VERDICT

**`cardκ` receives a value at the [LJ-1.90] site.** The term is
`SiteAt.cardκ : IsCardinal SiteAt.κ` at
`src/ProbeLJ194A.agda:1196-1197`, with `SiteAt.κ` the ambient Hartogs
set at `:1192-1193` (`Hartogs.κ = sett WO ot`, where `WO` is the small
type of well-orders on subsets of `ω`). The whole probe checks GREEN:
1058 non-blank lines, 27 s cold for the file's own content at load
4.8 to 5.2, one process at the C-12 cap. The site shape of
`src/ProbeLJ190A.agda:204-211` (κ, ordκ, cardκ, κ∉ω, α = ω, ordα,
α∈κ, α∉ω, x = ∅, x⊆Lα, lam, ordλ, α∈λ, succλ, x∈Lλ) receives all
fifteen values, `cardκ` included.

**The one route deviation to report.** The brief's step 1 is "the set
`W` of well-orders on subsets of `ω`" built by separation from the
power set with an internal well-order formula and its adequacy lemmas.
I built the same content at the TYPE level instead: the small type
`WO` of well-order structures (field predicate, relation, and the four
laws), and the Hartogs set directly as `sett WO ot`. The internal
formula, power set and separation are NOT built, because nothing in
the consumer needs them: the members of `κ` are indexed by the small
structure type itself, so the decode of a member into an `SWO` is
definitional. This is the more generic shape (no definability content
at all), which is the DD4 direction the brief asks for. The cost is
the smallness classifier `Ω'` (`HPropSmallness` from the redeemed
impredicativity parameter), which keeps `WO` in `Type ℓ`.

## 1. THE PER-STEP TABLE

The seconds are the marginal cost of each module, measured by prefix
bisection: each prefix is the file cut at a module boundary, checked
with the project's persistent agda cache warm (the same basis as the
[LJ-1.92] 18.4 s figure), one process at a time. Every run at load
4.36 to 4.39 (4 users, machine NOT quiet). The full-file figure at the
foot of the table is the file's own content re-checked cold with the
import cache warm: 27 s at load 5.19 / 4.95 / 4.69.

| step | content | lines (non-blank) | cold s | load |
|---|---|---:|---:|---|
| 1 | the set `W` of well-orders on subsets of `ω`: `SmallWO` (`WO`, the decode into an `SWO`, `ot`, `ot-ord`) | 71 | about 1 | 4.39 |
| 2 | the order type of a well-order: **imported** `src/ProbeLJ192A.agda` (`OrderType`, `Unique`) | 365 (imported) | 18.4 (measured by LJ-1.92, its own cold run) | 3.3 (LJ-1.92) |
| 3 | the Hartogs set itself: `Hartogs.κ = sett WO ot`, `ω∈κ`, `κ-mem` | 62 | within the Hartogs block | |
| 4 | ordinality and countability: `OrdinalSelf` 137, `Natural` 71, `Count` 50, `InitialSegment` 280, plus the ordinality half of `Hartogs` (`member-of-ot`, `κ-trans`, `ordκ`) | 538 plus about 30 | about 20 (1 + 2 + 1 + 16) | 4.39 |
| 5 | initiality and the supply: `Hartogs.Pullback` 197, `cardκ`/`κ∉ω` 25, `SiteAt` 33 | about 255 | about 8 | 4.36 |
| whole file | all of the above plus the prologue | 1058 | **27** | 4.8 to 5.2 |

The prefix runs: imports plus `OrdSWO` 1 s; plus `SmallWO` 1 s; plus
`OrdinalSelf` 2 s; plus `Natural` 3 s; plus `Count` 3 s; plus
`InitialSegment` 19 s; plus `Hartogs` 27 s; plus `SiteAt` 27 s. The
differences are the marginals in the table. The heavy step is the
initial segment (about 16 s), the same instantiation class the brief
predicted from [LJ-1.92]'s image block.

`OrdSWO` (61 lines) is the delivered ordinal well-order shape at
`src/L/StageCardinal.lagda.md:226-258`, copied into the probe so that
the heavy stage-cardinality chapter is not imported (one process,
C-12). It is not new mathematics.

## 2. THE TERM THAT RECEIVES A VALUE

The abort criterion's first branch. At the [LJ-1.90] site shape
(`src/ProbeLJ190A.agda:204-211`, the telescope at
`src/L/BoundedSubset.lagda.md:1396-1402`):

| site hypothesis | value | where |
|---|---|---|
| `κ : S` | `Hartogs.κ = sett WO ot` | `src/ProbeLJ194A.agda:1190-1191`, `:873-874` |
| `ordκ : IsOrd κ` | `Hartogs.ordκ` | `:1193-1194`, `:919-920` |
| **`cardκ : IsCardinal κ`** | **`Hartogs.cardκ`** | **`:1196-1197`, `:1160-1174`** |
| `κ∉ω` | `Hartogs.κ∉ω` | `:1199-1200`, `:1176-1177` |
| `α = ω`, `ordα` | `ω-ord` | `:1202-1206` |
| `α∈κ` | `Hartogs.ω∈κ` | `:1207-1208`, `:876-877` |
| `α∉ω` | `∈-irrefl ω` | `:1209-1210` |
| `x = ∅`, `x⊆Lα` | `Site.x⊆Lα` | `:1212-1215` |
| `lam`, `ordλ`, `α∈λ`, `succλ`, `x∈Lλ` | the delivered generic `Site` module of the LJ-1.90 probe, instantiated at `A = Lset ω`, `α = ω` | `:1189-1190`, `:1217-1233` |

The full-file check of this value: 27 s cold at load 5.19 / 4.95 / 4.69
(one process, C-12 cap). This is the acceptance test: `cardκ` is
SUPPLIED by a value, not restated (C-38).

The full `BoundedSubsetAt` module (`src/L/BoundedSubset.lagda.md:1396`)
is not instantiated, because its enclosing `Devlin55`
(`:1361-1367`) requires the `sq` and `absorbs-subset` hypotheses, which
the tree never supplies. **MEASURED by reading**: the site shape
receives all fifteen values; the module boundary is the square-law
hypothesis, not `cardκ`.

## 3. CHOICE AND LEM

No axiom of choice is used anywhere in the chain. LEM enters in two
places, both the tree's standing form (`lem : LEM (ℓ-suc ℓ)` as the
probe's module parameter):

1. `lem→impredicativity` supplies `HPropSmallness`, the small
   classifier `Ω'` that keeps the structure type `WO` small. Without
   it, `WO` would live in `Type (ℓ-suc ℓ)` and could not index a
   `sett`.
2. `leastOf` (the delivered LEM-priced least-element search,
   `src/L/WellOrder/Base.lagda.md:158-161`) builds the reverse
   collapse in `Count`: from a member of an order type to the carrier
   element that collapses to it.

The order-type core (step 2, imported `ProbeLJ192A`) remains
choice-free and LEM-free per [LJ-1.92] section 7. **MEASURED**: the
probe's only classical parameters are `lem` and its derivations; no
choice principle appears in the imports.

## 4. DD4

**The chain is generic, MEASURED.** The probe's content names only the
ambient universe `S`, the small presentation `⟪_⟫`, injections, the
`SWO` record, `ω`, and the ordinal supply. No tower object (no `Def`,
`Lset`-beyond-the-site, no `Rud`) appears in any type of the probe's
mathematics. The order-type block is the imported generic `OrderType`
and `Unique` at an `SWO` carrier; the Hartogs assembly is about
well-orders and injections, not about definability. The J half is
**INFERRED** (no J tower exists in this tree); the ambient half is
**MEASURED by the probe's own types**.

The one step that must be named for the deviation: step 1 as built
(the type `WO`) is MORE generic than the brief's separation-set
version, because it carries no internal formula. It is not a step that
breaks the generic chain; it is the same content class as the rest.

## 5. THE NEGATIVES AND THEIR STATUS

1. "`cardκ` receives a value at the [LJ-1.90] site": **MEASURED TRUE**.
   `SiteAt.cardκ` (`src/ProbeLJ194A.agda:1196-1197`), green at the
   C-12 cap.
2. "The initial-segment step is the heavy half of the new content":
   **MEASURED TRUE**. About 16 s of the 27 s total, the same
   instantiation class as [LJ-1.92]'s image block.
3. "The full `BoundedSubsetAt` instantiation closes": **MEASURED
   FALSE** (by reading). `Devlin55`'s `sq` and `absorbs-subset`
   hypotheses (`src/L/BoundedSubset.lagda.md:1361-1367`) have no
   instance in the tree; the boundary is the square law, not `cardκ`.
4. "The internal well-order formula is needed for the Hartogs set":
   **MEASURED FALSE by the build**. The type-level `WO` supplies every
   member's `SWO` by definition, and `κ = sett WO ot` is a `V`-set;
   the formula's adequacy lemmas are never consulted.
5. "The tree supplies `IsOrd`/countability facts for the Hartogs set":
   **MEASURED TRUE**. `ordκ` via the initial segment
   (`src/ProbeLJ194A.agda:884-920`), and the reverse collapse
   (`Count`, `:491-553`).

## 6. GATES

- `src/ProbeLJ194A.agda`: GREEN at the C-12 cap, one process. The
  file's own content, checked cold with the import cache warm: 27 s at
  load 5.19 / 4.95 / 4.69, four users, machine NOT quiet. Every prefix
  run at load 4.36 to 4.39. No process was left alive; each check
  returned (C-12).
- `scripts/check-fences.py --check`: clean, 87 masters, run threshold
  3.
- `scripts/lint-prose.py --check` on the probe and this report: exit
  0.
- `scripts/lint-agda.py --check` on the probe: exit 0.
- `scripts/ledger.py --brief`: standing 28,189 lines over 85 masters,
  measured from HEAD `9b51977`.
- `git status`: clean at the end. HEAD moved during the dispatch from
  `a1f0e95` to `9b51977` (the orchestrator's LJ-1.98 commit); my work
  touched no tracked file. The probe is ignored by `.gitignore`, this
  report by `_build/`.
- Masters: none touched. DD23: no mathematical prose written or
  changed.

## 7. ARCHIVE USED

- `_build/lj-1.92-report.md`, read WHOLE. TOOK the step-2 price (365
  lines, 18.4 s cold at load 3.3), the image-block reading, and the
  measurement basis.
- `src/ProbeLJ192A.agda`, read WHOLE. TOOK `OrderType` and `Unique`,
  imported unchanged (`src/ProbeLJ194A.agda:60`).
- `_build/lj-1.91-report.md`, read WHOLE. TOOK the five-step route and
  the internal-Hartogs rejection.
- `_build/lj-1.90-report.md` and `src/ProbeLJ190A.agda`, read WHOLE.
  TOOK the site shape (`:204-211`) and the `Site` module, imported and
  instantiated (`src/ProbeLJ194A.agda:1189-1190`).
- `src/L/BoundedSubset.lagda.md`, read `:1040-1050`, `:1390-1402`,
  `:1361-1367`. TOOK `IsCardinal` (`:1045-1046`) and the telescope.
- `src/L/Ordinal/SquareLaw.lagda.md`, read the col machinery
  (`:146-496`) and `Init` (`:692-700`). TOOK the delivered pattern
  shape, re-instantiated by the imported probe.
- `src/L/WellOrder/Base.lagda.md`, read `:101-107` and `leastOf`
  (`:158-161`).
- `src/L/StageCardinal.lagda.md`, read `:205`, `:226-258`. TOOK
  `OrdSWO`, copied (`src/ProbeLJ194A.agda:80-140`).
- `src/L/Ordinal.lagda.md`, read `:77-258`. TOOK the ordinal supply.
- `src/V/Model.lagda.md`, read `:280-371`. TOOK the power set and
  separation (NOT used; the deviation, section 0).
- `src/V/Presentation.lagda.md`, read WHOLE. TOOK `member`, `fiber`,
  `↪-inj`.
- `archive/rud-route/src/L/Ordinal/Pairing.lagda.md`, read the order
  type (`:436-575`), SHAPE only.
- `dev/LESSONS.md`, read WHOLE P-l, P-m, P-i, D-1, D-8, D-30, C-35,
  C-36, C-38; and the `--for build` and `--for probe` bundles via
  `scripts/rules.py`. TOOK the discharge standard (C-38), the
  price-what-the-consumer-needs rule (D-30), and the
  conversion-explosion playbook (P-i), which guided the opaque seals
  on the isomorphism components.

## 8. LITERATURE USED

Banked. `[LJ-1.92]` settled it: Devlin assumes order types and proves
no order-type content in II.5 (`dev/literature/devlin-II5.md:145-166`).
Spent nothing.

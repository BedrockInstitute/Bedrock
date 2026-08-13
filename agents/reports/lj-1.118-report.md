# LJ-1.118: enter Devlin55 at the site

tier: codex (default)

## STATUS

STOPPED AT THE ABORT CRITERION, SECOND BRANCH. The site instance of
`absorbs-subset` is supplied and machine-checked. The module parameter is
a total function, and its `x ∉ Lset α` branch is the term this dispatch
could not write. `Devlin55` is NOT entered, so `BoundedSubsetAt` is not
entered. The report is `_build/lj-1.118-report.md`; the probe is
`src/ProbeLJ1118A.agda`, GREEN at the C-12 cap, one process. No master was
touched. No commit, no push.

## 0. THE VERDICT

**NO. `Devlin55` is not entered.** The consumer's own value of
`absorbs-subset`, the site instance at `α = ω`, `x = ∅`, IS supplied:
`Site.site-inj : ⟪ Lset ω ∪ ⁅ ∅ ⁆s ⟫ ↪ ⟪ Lset ω ⟫` at
`src/ProbeLJ1118A.agda:153-154`, machine-checked GREEN at 3.14 s (second run,
load 4.22 / 4.49 / 4.53, four users, one process at the C-12 cap). The
site block is 13 code lines against the [LJ-1.101] inferred price of 20 to
30 (`_build/lj-1.101-report.md:165`). **MEASURED.**

The module parameter is the whole function
`(α : S) → (α ∉ ω) → (x : S) → x ⊆ Lset α → ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫`
(`src/L/BoundedSubset.lagda.md:1363-1365`). The function's `x ∉ Lset α`
branch is the term that cannot be written from the delivered tree. Every
delivered-content route to it needs one of two pieces that the tree does
not deliver:

1. an injection out of the union presentation
   `⟪ Lset α ∪ ⁅ x ⁆s ⟫`, the R-35 class that `[LJ-1.101]` named as the
   widest unmeasured term (`_build/lj-1.101-report.md:168-170`), or
2. a shift of the stage presentation `⟪ Lset α ⟫ ⊎ 1 ↪ ⟪ Lset α ⟫`,
   which reduces to `stage-card-upper` at `α`, which demands honest `sq`
   at every infinite ordinal, the `[LJ-1.107]` / `[LJ-1.114]` wall
   (`src/ProbeLJ1107A.agda:630-666`, `dev/PLAN.md:594`).

The LEM case split is not the blocker: `Split` and `AbsorbsTotal`
(`src/ProbeLJ1118A.agda:163-183`) machine-check that the parameter is the
pair of the two branches, with the out-branch as exactly one parameter.
The abort criterion's second branch fires. The first blocker is
`absorbs-subset` itself, one boundary before `BoundedSubsetAt`.

## 1. THE SITE SUPPLY OF absorbs-subset

The master states (`src/L/BoundedSubset.lagda.md:1363-1365`):

```agda
(absorbs-subset : (α : S) → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
                → (x : S) → (x⊆Lα : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
                → ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
```

The consumer applies it at exactly one place:
`code-inj = comp-inj (absorbs-subset α α∉ω x x⊆Lα) (stage-card-upper ...)`
(`src/L/BoundedSubset.lagda.md:1532`), inside `BoundedSubsetAt`. At the
`[LJ-1.94]` site, `α = ω` and `x = ∅`
(`src/ProbeLJ194A.agda:1202-1218`). The site supplies `∅ ∈ Lset ω`
(`∅∈𝒟ₒ ∅` at `src/L/Axioms/Basic.lagda.md:490-491`, climbed by
`Lset-mono` through `#∈ω 1`, `src/ProbeLJ1118A.agda:145-148`), so the
union absorbs: `Lset ω ∪ ⁅ ∅ ⁆s ≡ Lset ω` by extensionality, and the
injection is transport along the equality, injective by
`transport⁻Transport`. This is exactly the `[LJ-1.101]` section 2.3
analysis, machine-checked.

The supply is written generic (DD4): `AbsorbsIn`
(`src/ProbeLJ1118A.agda:72-130`) closes at any `(α, x)` with
`x ∈ Lset α`, and `Site` (`:136-155`) instantiates it at the consumer's
own site. The measured content:

| block | where | code lines |
|---|---|---:|
| the generic absorption (`AbsorbsIn`) | `src/ProbeLJ1118A.agda:72-130` | 49 |
| the site instance (`Site`) | `:136-155` | 13 |
| the whole probe | `:1-202` | 116 |

The inferred 20 to 30 line price was for the site instance. The measured
site block is 13 lines; the generic absorption it reuses is 49. Both are
parameterized content, the cheap class of P-m. **MEASURED.**

## 2. THE TERM THAT CANNOT BE WRITTEN

The module parameter is a total function. `AbsorbsTotal`
(`src/ProbeLJ1118A.agda:175-183`) machine-checks the whole parameter
modulo exactly one branch:

```agda
out : (α : S) → (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥) → (x : S)
    → (x⊆Lα : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
    → (⟨ x ∈ˢ Lset α ⟩ → Empty.⊥) → _↪_ ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ⟪ Lset α ⟫
```

The in-branch (`x ∈ Lset α`) is `AbsorbsIn.inj`, supplied. The out-branch
(`x ∉ Lset α`) is the term this dispatch could not write. The split is
LEM on the proposition `x ∈ˢ Lset α`, applied at
`src/ProbeLJ1118A.agda:182` (`lem (x ∈ˢ Lset α)`); the LEM is the
standing module parameter, so the case split itself is not the blocker.

The reduction, machine-checked as `OutVia`
(`src/ProbeLJ1118A.agda:192-200`): the branch closes by composition IF
the tree supplied

```agda
decomp      : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ (⟪ Lset α ⟫ ⊎ 1)
stage-shift : (⟪ Lset α ⟫ ⊎ 1) ↪ ⟪ Lset α ⟫
```

Neither is delivered:

1. `decomp` is the union-presentation injection, the R-35 class
   (`dev/LESSONS.md:782`). **MEASURED by search**: no lemma of the shape
   `⟪ A ∪ B ⟫ ↪ ...` exists anywhere in `src/`; the only presentation
   injection lemmas are `ord-emb` (`src/L/BoundedSubset.lagda.md:1370-1386`)
   and `stage-card-lower` (`src/L/StageCardinal.lagda.md:207-211`), both
   membership-based, neither about a union.
2. `stage-shift` is built from `stage-card-upper` at `α`, the ordinal
   non-surjective injection (`Incl` then `ShiftAbs` on `⟪ α ⟫`), and
   `stage-card-lower`. `Incl` and `ShiftAbs.shift-inj'` are delivered
   (`src/ProbeLJ1107A.agda:441-453`, `:389-390`); `stage-card-lower` is
   delivered (`src/L/StageCardinal.lagda.md:207-211`). The missing
   component is `stage-card-upper` at `α`, whose statement demands honest
   `sq` at `α` (`src/L/StageCardinal.lagda.md:15-19`, the demand at
   `:283`). Honest `sq` at every infinite ordinal is the `[LJ-1.107]`
   chain, stated CONDITIONAL on the injection `α ↪ |α|`
   (`src/ProbeLJ1107A.agda:630-666`), and `[LJ-1.107]` measured that the
   injection cannot be written: the least-of witness is truncated and the
   injection type is not a proposition (`_build/lj-1.107-report.md`
   section 0). `[LJ-1.114]` hit the same wall at route level
   (`dev/PLAN.md:594`); `[LJ-1.111]` measured the truncated alternative
   at about 350 lines of threading (`dev/PLAN.md:591`). **MEASURED.**

What the tree would have to provide, in order of cost:

1. honest `sq` at every infinite ordinal (the `[LJ-1.107]` blocker,
   whose chain is conditional on the unwritable injection,
   `src/ProbeLJ1107A.agda:630-666`), or
2. a delivered union-presentation injection plus a stage-shift (both
   new, the first of unknown cost, the R-35 class).

The deciding claim, "the branch cannot be supplied", is **INFERRED**: the
content is true in the model (an infinite stage is Dedekind-infinite), and
no refutation exists. The claim rests on the MEASURED facts above: the
reduction is machine-checked, the absence of both pieces is measured by
search, and the `[LJ-1.107]` / `[LJ-1.114]` walls are measured. A
negative that rests on an inference sets no verdict by itself; the
MEASURED site supply and the MEASURED reduction are the report's solid
half.

## 3. HOW FAR THE ENTRY REACHED

The entry stops at `Devlin55`'s own parameter. `BoundedSubsetAt` is not
entered, so `levelIn` (`src/L/BoundedSubset.lagda.md:1411`) and `cover`
(`:1412`) are not reached; they remain hypotheses of the layer, as the
brief's stop line names them. Hypothesis by hypothesis:

| boundary | site value | where |
|---|---|---|
| `Devlin55 (absorbs-subset)` | site instance SUPPLIED (`Site.site-inj`); total function NOT SUPPLIED (section 2) | `src/ProbeLJ1118A.agda:153-154`, `:175-183` |
| `BoundedSubsetAt κ` | `Hartogs.κ` | `src/ProbeLJ194A.agda:1190-1191` |
| `ordκ` | `Hartogs.ordκ` | `:1193-1194` |
| `cardκ` | `Hartogs.cardκ` | `:1196-1197` |
| `κ∉ω` | `Hartogs.κ∉ω` | `:1199-1200` |
| `α`, `ordα` | `ω`, `ω-ord` | `:1202-1206` |
| `α∈κ` | `Hartogs.ω∈κ` | `:1208-1209` |
| `α∉ω` | `∈-irrefl ω` | `:1211-1212` |
| `sq` | `sqω` from the honest ℕ pairing | `src/ProbeLJ1117A.agda:57-74` |
| `x`, `x⊆Lα` | `∅`, vacuous | `src/ProbeLJ194A.agda:1214-1218` |
| `lam`, `ordλ`, `α∈λ`, `succλ`, `x∈Lλ` | the generic `Site` module | `:1188`, `:1220-1233` |
| `levelIn`, `cover` | NOT REACHED | `src/L/BoundedSubset.lagda.md:1411-1412` |

The first blocker is the total function at the `Devlin55` boundary, one
module boundary before `BoundedSubsetAt`. This is the same test
`[LJ-1.90]` ran one level up: there the blocker was `cardκ`; here it is
the module parameter of the enclosing module.

## 4. THE C-39 SECTION

No prohibition blocked the site supply. Prohibitions audited:

- **Do not weaken a hypothesis to make it suppliable**: respected. The
  statement was NOT weakened; it is (believed) true as stated.
- **Do not add a hypothesis to the site**: respected. `AbsorbsTotal`
  takes the out-branch as a parameter only to MEASURE the shape; nothing
  is discharged by that.
- **Do not touch `src/L/Condensation*`, `src/L/Coding/`, `src/V/`**: no
  edit. The probe imports `L.BoundedSubset` read-only.
- **Never `src/Everything.lagda.md`**: not edited, not imported.
- **Do not run `make check`**: not run.
- **One agda process, cap never raised**: every check ran one process at
  `GHCRTS="-A64m -I0 -M8g"`; every check returned; none was killed.

The door behind this wall, reported per C-39: restating `absorbs-subset`
with the premise `x ∈ Lset α` added (the shape `[LJ-1.103]` already used
for `α ∉ ω`) would make the total function provable from the delivered
absorption machinery alone, because `AbsorbsIn` is exactly that proof
(`src/ProbeLJ1118A.agda:72-130`). The brief forbids that restatement
("Do not add a hypothesis to the site"), and C-36's strengthening
license does not apply: the current statement is believed TRUE, so the
restatement would be a weakening-to-supply, not a cure for falsehood.
The restatement is the orchestrator's call, not this dispatch's. The
alternative route, honest `sq` at every infinite ordinal, is the
`[LJ-1.107]` / `[LJ-1.114]` campaign, priced and measured as blocked at
the truncation wall.

## 5. THE NEGATIVES AND THEIR STATUS

1. "The site instance of `absorbs-subset` is supplied at
   `(α = ω, x = ∅)`": **MEASURED TRUE**. `Site.site-inj`
   (`src/ProbeLJ1118A.agda:153-154`), GREEN.
2. "The site instance costs 20 to 30 lines": **MEASURED at 13 code lines
   for the site block, 49 for the generic absorption** against the
   inferred 20 to 30 (`_build/lj-1.101-report.md:165`). The price was
   for the site instance; the site block is inside the band, the generic
   form above it.
3. "`Devlin55` is entered": **MEASURED FALSE**. The instantiation needs
   a total `Absorbs` term; `AbsorbsTotal` shows the only missing piece
   is the out-branch (`src/ProbeLJ1118A.agda:175-183`).
4. "The total function is writable from the delivered tree":
   **INFERRED FALSE**, resting on the MEASURED reduction (`OutVia`,
   `:192-200`) and the MEASURED absence of both pieces (section 2). The
   content is true in the model, so no refutation exists; this negative
   sets no verdict by itself.
5. "The tree delivers honest `sq` at every infinite ordinal":
   **MEASURED FALSE**. `Chain.theorem` is conditional on the injection
   (`src/ProbeLJ1107A.agda:630-666`); `[LJ-1.107]` measured the
   injection as unwritable (`_build/lj-1.107-report.md` section 0);
   `[LJ-1.114]` hit the same wall (`dev/PLAN.md:594`).
6. "The tree delivers a union-presentation injection": **MEASURED FALSE
   by search**. No lemma of the shape `⟪ A ∪ B ⟫ ↪ ...` exists in
   `src/`.
7. "`BoundedSubsetAt` is entered and reaches `levelIn` / `cover`":
   **MEASURED FALSE**. The entry stops at the enclosing module's
   parameter (section 3).
8. "The site entry is generic for the J tower": **INFERRED** (no J tower
   in this tree). The absorption machinery names only `S`, `Lset`, the
   union and injections; a J consumer instantiates the same shape at its
   own stage (DD4, section 6).

## 6. DD4

The supplied half is generic in the site. `AbsorbsIn` takes
`(α, x, x⊆Lα, x∈Lα)` as parameters and names no concrete carrier beyond
the tower's own `Lset` (`src/ProbeLJ1118A.agda:72-130`). The J tower
enters its own by instantiating the same absorption at `Jset` with its
own membership fact. **MEASURED** for the L side by the probe's types;
**INFERRED** for J (no J tower exists in this tree).

The un-writable half is not per-tower content. The missing pieces are
the union-presentation injection and the stage shift; the stage shift
runs through `sucV` and ordinal cardinality, which is tower-independent
content (the delivered `ShiftAbs` is about ordinals, never about `Lset`,
`src/ProbeLJ1107A.agda:278-394`). The two proofs share that blocker.
**INFERRED** for J, **MEASURED** for L by the probe's reduction.

## 7. GATES

- `src/ProbeLJ1118A.agda`: GREEN at the C-12 cap, one process, exit 0.
  Runs: 3.74 s and 3.14 s (real, second run), load 4.19 / 4.56 / 4.56
  and 4.22 / 4.49 / 4.53, four users, machine NOT quiet. 116 code lines.
  Zero hits for `postulate`, `TERMINATING`; no holes.
- `scripts/check-unbound-hyp.py src/ProbeLJ1118A.agda`: clean, exit 0.
- `scripts/lint-prose.py --check` on the probe and this report: exit 0.
- `scripts/lint-agda.py --check` on the probe: exit 0.
- `scripts/check-fences.py --check`: clean, 87 masters, run threshold 3.
- `scripts/ledger.py --brief`: standing 28,434 lines over 85 masters,
  measured from HEAD `079c04e`.
- `make check` not run (forbidden). DD23: no mathematical prose changed;
  the only written prose is this report and probe comments.
- C-12: every agda invocation returned; none was left alive. The sandbox
  denies process listing; liveness is verified by each invocation
  completing with exit 0.
- Working tree: `git status --short` is empty; the probe is ignored by
  `.gitignore`, this report by `_build/`. HEAD `079c04e` unchanged. No
  commit, no push.

## 8. ARCHIVE USED

- `_build/lj-1.117-report.md`, read WHOLE. TOOK the restricted `sq`
  (`src/L/StageCardinal.lagda.md:15-19`), the `BoundedSubsetAt` boundary
  (section 3), the site probe shape.
- `src/ProbeLJ1117A.agda`, read WHOLE. TOOK `sqω` (`:57-68`) and the
  site instantiation (`:74`).
- `_build/lj-1.94-report.md`, read WHOLE, and `src/ProbeLJ194A.agda`,
  read the site block (`:1186-1233`). TOOK the fifteen site values.
- `_build/lj-1.101-report.md`, read WHOLE, section 2.3 (`:146-170`).
  TOOK the 20 to 30 line price, the general-form route, and the
  union-presentation warning.
- `_build/lj-1.103-report.md`, read WHOLE, and `src/ProbeLJ1103A.agda`,
  read WHOLE. TOOK the repaired premise, the site instance
  (`abs-site`, `:146-157`), and the `X≡Lω` pattern.
- `_build/lj-1.107-report.md`, read WHOLE, and `src/ProbeLJ1107A.agda`,
  read WHOLE. TOOK `ShiftAbs`/`shift-inj'` (`:389-390`), `Incl`
  (`:441-453`), `Chain.theorem` conditional on the injection
  (`:630-666`), and the measured truncation wall.
- `_build/lj-1.90-report.md`, read WHOLE. TOOK the entry-test shape and
  the `cardκ` precedent.
- `src/L/BoundedSubset.lagda.md`, read `:1361-1626` (Devlin55 whole) and
  `:1144-1215` (`UnionKit`). TOOK the telescope, `code-inj` (`:1532`),
  `theorem` (`:1623`), `levelIn`/`cover` (`:1411-1412`).
- `src/L/StageCardinal.lagda.md`, read `:15-19`, `:190-230`,
  `:554-566`. TOOK the `sq` parameter and `stage-card-lower`/`-upper`.
- `src/L/Axioms/Basic.lagda.md`, read `:485-495`. TOOK `∅∈𝒟ₒ`
  (`:490-491`).
- `src/V/Presentation.lagda.md`, read WHOLE. TOOK `member`, `fiber`,
  `↪-inj`.
- `dev/PLAN.md`, read the rows for LJ-1.106 to LJ-1.118 (`:585-597`).
  TOOK the `[LJ-1.107]` PARTIAL status, `[LJ-1.111]` truncated chain,
  `[LJ-1.114]` wall, `[LJ-1.117]` landing.
- `dev/LESSONS.md`, read WHOLE C-38 (`:3427`), C-39 (`:3521`), C-40
  (`:3602`), P-x (`:3564`), C-35 (`:3200`), C-36 (`:3284`), D-8
  (`:1377`), D-30 (`:3332`), D-29 (`:3242`), P-i (`:203`), P-c
  (`:71`), P-o (`:2509`), P-q (`:2633`), P-t (`:2601`), P-u (`:2908`),
  P-v (`:3037`), P-w (`:3094`), R-36 (`:808`), C-31 (`:1855`), C-32
  (`:2947`), C-33 (`:2987`), C-34 (`:3171`), C-37 (`:3381`), D-1
  (`:1038`), D-26 (`:1676`), and the `--for build` bundle via
  `scripts/rules.py`. TOOK C-38's supply standard, C-39's report-the-door
  rule, R-35's union-representation warning.

## 9. LITERATURE (DD18)

Banked. Spend nothing.

# [LJ-1.294] report: is an infinite cardinal a limit ordinal?

tier: pi (pi-subagent-mode), model `glm-5.3`. A PROBE: nothing lands, all
work in `agents/tasks/LJ-1-294/`. Written incrementally (C-22). Every
negative is MEASURED or INFERRED, in those words. ASD-STE100 applies.

## 0. LEAD

**PROVED.**

```
κ-limit : (κ : S) → IsOrd (fst κ) → IsCardinalL κ
        → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
        → (γ : V ℓ) → ⟨ γ ∈ˢ fst κ ⟩ → ⟨ sucV γ ∈ˢ fst κ ⟩
```

at `agents/tasks/LJ-1-294/CardinalLimit.agda:53-124`, **exit 0, `--safe`,
1.905 s cold at load 5.22** (own `.agdii` deleted, dependencies warm; the
project caliber). **An infinite internal cardinal is successor closed, and
the tree proves it from what it already holds.**

**The `InjCode`-against-`↪` gap costs NOTHING, because it is never
crossed.** The absorption chapter builds its injection as a CODED graph
first and reads it back second. My term consumes the code half, which is
exactly what `IsCardinalL` refutes. No ambient-to-code bridge is needed
and none exists in the tree (MEASURED by grep, section 5).

**ONE finding outside the target, MEASURED:** the brief's row 2
(`⟨ ω ∈ˢ κ ⟩` derivable by `ord-tri`) is **FALSE as stated at κ = ω**,
where it unfolds to `⟨ ω ∈ˢ ω ⟩`, refuted by `∈-irrefl`
(`src/V/Hierarchy.lagda.md:155`). It is derivable under the case split
κ ≠ ω, and the κ = ω disjunct is exactly the base `[LJ-1.279]` rebuilt
from `InitialCore` rather than `via-col-square`. Section 6. The corrected
term `ω∈κ-after-split` is green in the same file, at `:130-147`.

**`Init κ` is NOT yet fully constructible at the use site.** Rows 1 and 3
are settled, row 2 is settled under the split, **row 4 (`noinj²`) is still
owed** by the square-law chain (`agents/tasks/LJ-1-279/lj-1.279-report.md:107-113`
names its consumer as downstream and not landed). Section 7.

## 1. MACHINE AND PROCESS DISCIPLINE

ONE agda process at a time, `GHCRTS="-A64m -I0 -M8g"` on every run, cap
never raised. **MEASURED FALSE: a wall.** Longest single invocation
2.783 s. **MEASURED FALSE: a heap exhaustion.** No kill, no interrupt.

The machine was NOT quiet: a sibling task held the other Agda slot
throughout, and the 1-minute load moved between 4.56 and 8.41 during the
kept runs. Every absolute figure below carries its load. The
orchestrator committed `[LJ-1.293]` and reorganized `scripts/` into
subdirectories DURING this run; the working tree carries those writes,
which are not mine.

| run | exit | elapsed s | 1-min load |
|---|---:|---:|---:|
| first full green (both terms) | 0 | 2.783 | 4.90 |
| cold caliber, own `.agdii` deleted | **0** | **1.905** | 5.22 |

## 2. THE ABORT CRITERION, FIXED BEFORE THE RUN (D-1)

- **IT IS PROVABLE AND YOU BUILD IT.** **FIRES.** Section 0, section 3.
  The term and its lines are reported. STOP.
- **IT IS TRUE BUT NEEDS SOMETHING UNDELIVERED.** Does not fire. Every
  ingredient was delivered: `ShiftGraph` exports its code and all four
  conjuncts (`src/L/Absorption.lagda.md:410-415` and `:452-495`, opened
  public at
  `:604`).
- **IT IS ALREADY IN THE TREE.** Does not fire, but the search paid
  (section 5): the successor-closure shape appears in the tree only as a
  HYPOTHESIS (`succλ`, nine sites) or proved for ω alone
  (`ω-limit`, `src/L/InjChain.lagda.md:109`). No cardinal-is-limit lemma
  existed.
- **IT IS FALSE OR NOT PROVABLE HERE.** Does not fire. Row 2 of the brief's
  table, NOT the target lemma, is what came out false (section 6).
- **A WALL.** Does not fire. Section 1.

## 3. THE TERM AND WHY IT IS THE SHAPE IT IS

The file is `agents/tasks/LJ-1-294/CardinalLimit.agda`, 139 lines, 122
non-blank. The proof runs one classical case split and three
trichotomies:

1. **Decide** `⟨ sucV γ ∈ˢ fst κ ⟩` by `lem`. The positive case returns.
2. **Trichotomy** `sucV γ` against `fst κ` (`ord-tri`,
   `src/L/Ordinal/Linear.lagda.md:136`):
   - `κ ∈ˢ sucV γ`: `∈sucV-elim` (`src/V/Model.lagda.md:218`) splits into
     `κ ∈ˢ γ` or `κ ≡ γ`. Both yield `⟨ γ ∈ˢ γ ⟩` by transitivity
     (`oγ .fst`, the `isTransV` field, `src/L/Constructible.lagda.md:83`),
     refuted by `∈-irrefl`. The eliminator wants its motive at
     `Type (ℓ-suc ℓ)`, so the contradiction is carried in
     `Lift {j = ℓ-suc ℓ} Empty.⊥` and lowered.
   - `sucV γ ≡ fst κ`: the successor case, below.
3. **The successor case.** `κ = sucV γ` with `γ ∈ˢ κ`:
   - `γ ∉ˢ ω`: else `ω-limit` (`src/L/InjChain.lagda.md:109`) gives
     `sucV γ ∈ˢ ω`, so `fst κ ∈ˢ ω`, refuting `nfin`.
   - `numerals`: `(k : ℕ) → ⟨ (# k) ∈ˢ γ ⟩` by a second trichotomy
     `γ` against `ω`: `γ ≡ ω` transports `#∈ω`; `ω ∈ˢ γ` transits
     `#∈ω k` down; `γ ∈ˢ ω` is refuted.
   - `module SG = ShiftGraph γᴸ oγ γ∉ω numerals`
     (`src/L/Absorption.lagda.md:538-543`) hands over `G`, `D`, `C` and
     the four conjuncts `sv`, `dm`, `ij`, `ran`, with `fst D = sucV γ`
     by construction (`:544-545`) and `C = γ`.
   - `γᴸ : S` lifts `γ` into the L-carrier by `isL-trans` over
     `γ ∈ˢ fst κ` (`src/L/Constructible.lagda.md:379`), since
     `IsCardinalL` quantifies over L-elements.
   - `D ≡ κ` by `Σ≡Prop` over `sucV γ ≡ fst κ`: `isL` is a `⋁`, the
     truncated existential (`src/Base/Truth.lagda.md:125`), so a prop.
   - `codeD : InjCode SG.G SG.D γᴸ = SG.sv , SG.dm , SG.ij , SG.ran`,
     transported along `D ≡ κ`. The transport runs at the `InjCode`
     level, so no local satisfaction alias is named.
   - `cκ γᴸ γ∈κ ∣ SG.G , code ∣₁ : Empty.⊥`. Cardinality refuted.

**D-10 ANSWERED: the truth at the intended generality held, and the
standard argument transferred after one rewrite.** The rewrite: the
textbook route injects `κ ↪ γ` ambiently and wants an
ambient-to-code bridge at the end. The delivered tree runs the other way
round: `L.Absorption` carves the coded graph `G` FIRST
(`src/L/Absorption.lagda.md:403-495`) and reads it back to
`⟪ sucV γ ⟫ ↪ ⟪ γ ⟫` SECOND (`:504-507`, via `Small`). Consuming the
first half dissolves the bridge problem the brief feared.

## 4. EVERY PREMISE, VERIFIED OR REFUTED

1. **"`Init` is four parts at `src/L/Ordinal/SquareLaw.lagda.md:692-699`,
   and `:695` is the successor-closure part."** **VERIFIED.** The third
   conjunct is `(γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩` at `:695`. Note
   SquareLaw's `S` is the V-carrier, so at the use site the γ ranges over
   `V ℓ`; my lemma matches that, `(γ : V ℓ)`.
2. **"`ord-tri` at `src/L/Ordinal/Linear.lagda.md:136` compares any two
   ordinals, and LEM is already a module parameter there, so using it adds
   no new assumption."** **VERIFIED, both halves.** `ord-tri` at `:136`;
   the module parameter is `lem : LEM (ℓ-suc ℓ)` at
   `src/L/Ordinal/Linear.lagda.md:32`, the SAME instance
   `L.GCH` (`src/L/GCH.lagda.md:10`), `L.Cardinal` (`:11`), `L.Absorption`
   and `L.InjChain` carry. My probe threads one `lem` into all five and
   typechecks: MEASURED, the row is free.
3. **"`IsCardinalL` ... stated with `InjCode`, an internal coded
   injection, NOT a bare `↪`. That may be the whole difficulty."**
   **VERIFIED as a reading and REFUTED as a difficulty.** The statement
   is at `src/L/Cardinal.lagda.md:231-233`, coded. The difficulty never
   materializes: the code is what `ShiftGraph` already exports. What it
   costs to move between them: NOTHING in this direction, because the
   move is never made. The OTHER direction (code to ambient) is
   delivered as `module Small` (`src/L/Coding/Injection.lagda.md:123`)
   and is not needed here.
4. **"`sucV` facts exist: `self∈sucV` and `∈sucV-inl` are used throughout
   `src/L/Coding/EnvSupply.lagda.md`. Find their home."** **VERIFIED.**
   The home is `src/V/Model.lagda.md`: `∈sucV-elim` at `:218`,
   `∈sucV-inl` at `:230`, `self∈sucV` at `:236`. What else is there: the
   private `singl≡` at `:214` and the ZF-model chapter's remaining
   fields. My term consumes `∈sucV-elim`, the case-split device, which
   is the load-bearing one for successor reasoning.
5. **"Row 2: `⟨ ω ∈ˢ κ ⟩` DERIVABLE by `ord-tri`."** **REFUTED as
   stated, MEASURED.** Section 6.

## 5. THE SEARCH (C-44)

- **MEASURED: no cardinal-is-limit lemma in `src/`.** Grep for the
  successor-closure shape `(γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩` and
  its variants: it appears as a HYPOTHESIS at nine sites
  (`BoundedSubset:904,1394`, `Coding/Bound:51,131`, `Coding/Key:568,616`,
  `Coding/EnvSupply:108,774`, `Condensation:7265`) and as the `α-limit`
  parameter of `InitialCore` (`src/L/Ordinal/SquareLaw.lagda.md:704`).
  The only PROVEN instances are `ω-limit` for ω itself
  (`src/L/InjChain.lagda.md:109`) and the ω case inside `BoundedSubset`
  (`:980-986`).
- **MEASURED: no ambient-to-code bridge in the tree.** Grep for consumers
  of `InjCode`: only `L.Cardinal` itself and `L.GCH`'s import list. The
  only delivered bridge is code-to-ambient, `module Small`
  (`src/L/Coding/Injection.lagda.md:123`), consumed by `L.InjChain:426`
  and `L.Absorption:504`. My route needs no bridge, so its absence is not
  an obstruction.
- **MEASURED: `L.Absorption` exports what the proof needs.** `open Carve
  ... public` at `src/L/Absorption.lagda.md:604` re-exports `G` (opaque,
  `:410-415`), `sv` (`:452`), `ij` (`:466`), `dm` (`:480`) and `ran`
  (`:494`) from `ShiftGraph` (`:538`).

## 6. ROW 2, REFUTED AS STATED AND CORRECTED

**The claim: from `nfin : ⟨ fst κ ∈ˢ ω ⟩ → ⊥` alone, `⟨ ω ∈ˢ fst κ ⟩`
follows by `ord-tri`. FALSE at κ = ω, MEASURED.** `ord-tri ω ω-ord (fst κ)
oκ` yields `ω ∈ˢ fst κ ⊎ (ω ≡ fst κ ⊎ fst κ ∈ˢ ω)`. The third disjunct
dies to `nfin`. The middle disjunct at κ = ω requires `⟨ ω ∈ˢ ω ⟩`, which
`∈-irrefl` refutes (`src/V/Hierarchy.lagda.md:155`; `[LJ-1.286]` section
5.1 records the same fact). So the derivation needs the case split first.

**ω IS a live κ at the use site, INFERRED.** Nothing in `GCHStatement`
(`src/L/GCH.lagda.md:78-87`) excludes κ = ω, and ω is the first infinite
cardinal. So the `[LJ-1.8]` proof will have to split: the κ = ω base is
`squareω : sq ω` (`src/L/InjChain.lagda.md:184-185`), which is exactly
the route `[LJ-1.279]` took when it rebuilt the base from `InitialCore`
rather than calling `via-col-square`. The corrected row-2 term under the
split is green in my file at `:130-147`:

```
ω∈κ-after-split : (κ : S) → IsOrd (fst κ)
               → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
               → ((ω ≡ fst κ) → Empty.⊥)
               → ⟨ ω ∈ˢ fst κ ⟩
```

**This is the same obstruction `[LJ-1.286]` section 5.1 saw from the
domain side, now measured from the use side:** `Init` demands ω as a
MEMBER, so κ = ω can never satisfy `Init` and must be split off before
`via-col-square` is applied.

## 7. IS `Init κ` CONSTRUCTIBLE AT THE USE SITE NOW?

**NOT yet, and the remaining debt is one row.**

| `Init κ` component | status after this task |
|---|---|
| `IsOrd κ` | GIVEN by `GCHStatement` |
| `⟨ ω ∈ˢ κ ⟩` | derivable UNDER the κ ≠ ω split (section 6) |
| successor closure | **PROVED HERE**, `κ-limit`, from `IsCardinalL κ` + `nfin` |
| `noinj²` | **STILL OWED** by the square-law chain |

Row 4 is the mathematical content `via-col-square` exists to consume:
`[LJ-1.279]` section 3 names its consumer (the L-side composition
`sqβ ∘ f`) as "downstream and is not landed here". **MEASURED by grep: no
term of the fourth conjunct exists in `src/`**; the `InitialCore`
parameters `noinj²` and `finite-excl` are instantiated only at ω inside
`L.InjChain`. So `[LJ-1.8]` is unblocked for rows 1, 2 and 3, and the
square-law row 4 plus the ω-split are what remains of the `sq`
hypothesis.

## 8. THE HOME, AND DD4

**DD4: maximize the code the two proofs share, and write it generic.**
The lemma is written generic: it names no tower, no stage and no
presentation, and it quantifies over κ and γ.

**MY AXIS IS AC-AGAINST-GCH (C-46), DD4's own**, fixed in code at
`scripts/measure/ledger.py` (the `--reuse` report; the brief's
`scripts/ledger.py:50` cites the pre-reorganization path). Today's print:
AC 73 masters / 17,197 lines, GCH 51 / 9,967, SHARED 44 / 7,632, share
39.1% of 19,532.

**THE RECOMMENDED HOME IS `src/L/Absorption.lagda.md`, NOT
`src/L/Cardinal.lagda.md` and NOT `src/L/Ordinal/`.**

- **`L.Cardinal` is IMPOSSIBLE, MEASURED:** `L.Absorption` already
  imports `L.Cardinal` (`src/L/Absorption.lagda.md:37`), so the lemma
  cannot live below its own ingredient without a cycle.
- **`src/L/Ordinal/` is impossible for this PROOF, MEASURED:** the proof
  consumes `ShiftGraph` (L.Absorption) and `IsCardinalL` (L.Cardinal),
  both GCH-closure masters. A weaker ambient statement could live there,
  but it would not be the statement the use site needs, and P-k rules
  for the consumer's form.
- **`L.Absorption` has both ingredients locally**: `ShiftGraph` is
  defined there and `L.Cardinal` is already imported. The one import to
  add is `L.Ordinal.Linear` for `ord-tri`; nine masters import it today
  (`Stages:57`, `SquareLaw:37`, `StageCardinal:33`, `Choice/Faithful:49`,
  `Choice/Step:52`, `BoundedSubset:879`, `Coding/Bound:20`,
  `Coding/Key:46`, `Coding/EnvSupply:74`, `Stage:49`), so no cycle and no
  new edge class. `ω-limit` needs `L.InjChain` widened from
  `module StageBound` to include it; `L.InjChain` is already imported at
  `:36`. `mem-ord`, `suc-ord`, `ω-ord` widen the `L.Ordinal` using list
  at `:22`. `Σ≡Prop` adds one Cubical import.
- **P-k:** the consumer is the GCH statement's proof through the
  `SqShape` chain; `L.Absorption` sits directly below `L.GCH`
  (`src/Everything.lagda.md:367-368`) and `L.GCH` already imports it
  (`src/L/GCH.lagda.md:17`).

**DD4 effect on the axis, MEASURED for the boundary and INFERRED for the
figure:** landing in `L.Absorption` touches NO shared master and NO
AC-closure master, so AC stays 17,197 and SHARED stays 7,632; the GCH
closure grows by the landing. The share therefore FALLS, for the
structural reason `[LJ-1.286]` section 8 recorded: GCH-specific
mathematics is what the GCH trophy owes and none of it is AC's. A share
defended by refusing to land GCH content would be the failure the
no-gate ruling was written against. **The share figure alone will point
the wrong way at this landing too, and the SHARED row is the one to
read.** The lemma cannot raise the shared figure even in principle:
its statement names `IsCardinalL`, whose only consumers are GCH-side
(MEASURED by grep: `L.GCH:16` and `L.Absorption:37`), so every legal home
sits in the GCH closure.

**Price, one best-effort number (DD8), basis: the probe itself.** The
probe carries 122 non-blank lines, of which about 25 are the probe's own
header comments and the row-2 auxiliary. The landing in `L.Absorption`
costs **about 100 non-blank lines**, being the `κ-limit` term with its
comments plus five import-list widenings. The row-2 auxiliary belongs to
the `[LJ-1.8]` proof, not to this lemma's home.

## 9. TIMING AND SIZE (DD24, DD8)

The probe file: 139 lines total, 122 non-blank. Cold caliber 1.905 s at
load 5.22 (section 1). No master was touched; the landing price is
section 8.

## 10. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-286/lj-1.286-report.md`, read WHOLE, FIRST, as the
  brief ordered.** TAKEN: the `Init` gap table, the `∈ˢ`-against-`∈`
  identity (section 3), and the closure arithmetic (section 7). Line read
  `:212`, "Two of the three missing parts are FALSE on `SqShape`'s own
  domain, not merely unproved." **My task measured the use site that
  table's domain-side reading pointed to, and the third part flipped from
  GAP to PROVED exactly because the use site carries `IsCardinalL`.**
- **`agents/tasks/LJ-1-279/lj-1.279-report.md`, read sections 0 to 3.**
  TAKEN: why row 5 rebuilt the base at ω from `InitialCore`, and that the
  `noinj²` consumer is downstream and unlanded. Line read `:102`,
  "`squareω : sq ω`. The three hypotheses ... are the `InitialCore`
  instantiation". **That is the same obstruction my section 6 measures
  from the row-2 side: ω can never satisfy `Init`.**
- **`archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md`,
  read for shape.** Line read `:563`,
  `cardFo v = ordFo v ∧̇ (∀̇∈ (var v) (¬̇ eqFo zero (suc v)))`. TAKEN,
  SHAPE ONLY: the retired cardinal predicate says "an ordinal with no
  member equipotent to it", the BIJECTION form, and its file holds NO
  cardinal-is-limit lemma either (MEASURED by grep over both retired
  cardinal files). **WHAT WOULD NOT TRANSFER:** the bijection form
  against today's injection form (`[LJ-1.273]`'s finding, confirmed by
  the grep), and the route: nothing in the retired files prices my
  trichotomy route, which did not exist there. No price and no technique
  came from it.
- **`archive/dev/TASKS-archived.md`:** the brief's cited rows were NOT
  found by grep under the names given (MEASURED:
  `CardinalPredicates` and `cardFo` do not occur in that file; the
  live `[LJ-1.273]` row sits at `dev/PLAN.md:1105-1106` and prices the
  1,760-against-262 landing question, not `cardFo`). I read
  `dev/PLAN.md:1105-1106` instead and took the correction it carries:
  the archive's figures are about gch_root's landing, and no archived
  claim about cardinal predicates transferred.

## 11. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md`, read `:140-170` (the 5.5 to 5.8 chain),
`:275-296` (the ingredient list) and `:373-420` (the twelve-row table and
the II.1.1(vii) row).**

**DOES DEVLIN STATE CARDINAL-IS-LIMIT AS A LEMMA, ASSUME IT, OR NEVER
NEED IT? NEVER AS A LEMMA, AND HIS CHAIN NEVER NEEDS THE SPLIT FORM.**
The cardinal arithmetic 5.5 actually consumes is recorded at `:281-282`:
"the cardinal fact `|γ| = |α| < κ` with κ a cardinal implies `γ < κ`
(`dev2.txt:1372-1384`)", an initial-ordinal fact invoked as established
chapter-I arithmetic, beside `|L_α| = |α|` from II.1.1(vii) (`:411-418`,
"generic cardinal arithmetic over the level-size equation"). Row F of
the twelve-row table (`:382`) files both under "condensation (i)(ii),
`|L_α| = |α|`, initial ordinals", verdict EITHER tower.

**SO THE BRIEF'S THIRD POSSIBILITY IS THE ONE THAT HOLDS, WITH ONE
REFINEMENT.** Devlin's cardinals are initial ordinals in the standard
sense, and the property "an infinite cardinal is not an ordinal
successor" is an immediate corollary of initiality that his prose never
isolates. **The gap was never in our proofs and never in Devlin's: it
was that `[LJ-1.286]` measured `Init`'s parts against `SqShape`'s domain
instead of against `IsCardinalL` at the use site.** Our `IsCardinalL`
(`src/L/Cardinal.lagda.md:231-233`) IS the initial-ordinal definition in
the coded-injection form, so once the object is measured at the use
site, the standard argument lands. **WHY NOT the other rows:** rows A to
C6 and E are elementarity, collapse, absoluteness, bookkeeping and hull
counting; rows D and G are the definable well-order; none touches the
successor structure of a cardinal. Row F is the only cardinal-arithmetic
row, and it is where this lemma lives in the digest's classification.

## 12. WHAT I DID NOT DO

- **No master was touched.** `git status --short` over my writes shows
  exactly `agents/tasks/LJ-1-294/CardinalLimit.agda` and this report.
  The tree's other modifications and the `scripts/` reorganization are
  the orchestrator's, made in parallel during this run.
- **No term of `SqShape`, no row-4 attempt, no `src/L/GCH.lagda.md`
  edit.** The brief forbade them.
- **`make check` not run.** Checkers run on my writes:
  `lint-agda.py --check` and `lint-prose.py --check` exit 0;
  `check-probes.py` clean over 2,644 tracked files.

## 13. FOR THE ORCHESTRATOR

1. **The landing is ready to price:** section 8, about 100 non-blank
   lines into `src/L/Absorption.lagda.md`, with the import widenings
   listed there.
2. **Row 2 needs the ω-split in the `[LJ-1.8]` plan**, and the κ = ω
   base is `squareω`, already delivered. Section 6.
3. **Row 4 (`noinj²`) is now the only `Init` debt**, and `[LJ-1.279]`
   section 3 already names its consumer.
4. **`dev/ledger.toml` will need its `gch_root_why` re-read after this
   lands**, since the "nothing supplies `SqShape`" claim will then rest
   on row 4 alone rather than on rows 2, 3 and 4 together.

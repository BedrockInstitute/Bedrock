# LJ-1.280 report: land A7 as `src/L/GCH.lagda.md`

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. One Agda slot held.
A new master written. No commit, no push. Written incrementally (C-22). Every
negative is MEASURED or INFERRED, in those words. ASD-STE100 applies.

## 0. LEAD

**63 in-fence non-blank lines (47 code, 16 comment), 1.68 s cold (mean of 3),
whole-file rate 0.0266 s/line, which is 2.53x the 0.010514 bar; net of the
1.60 s import-header baseline, the 47 code lines cost 0.0016 s/line, 0.16x
the bar.** MEASURED, three cold runs, load ~6. The master is GREEN, exit 0,
`--safe`. The re-run that imports it is GREEN, exit 0.

**EXACTLY WHICH HYPOTHESES REMAIN UNSUPPLIED: the two leading parameters of
`GCHStatement`, `sq : SqShape` and `absorbs : AbsorbsShape`.** MEASURED at
`src/L/GCH.lagda.md:66-76`. Nothing in this master supplies either; both are
Π-parameters of the statement type, which is the honest conditional form
`[LJ-1.274]` section 1.5 named. The per-cardinal hypotheses
`IsCardinalL κ` and `(⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)` are also parameters of the
statement (they are the cardinal bookkeeping, supplied by the future prover,
not by A5 or A6).

The whole-file rate is over the bar because the 63-line statement sits behind
a 26-line import header whose interfaces dominate the cold seconds. This is
the header artifact `[LJ-1.236]` measured for A4, not a content-class cost:
the 47 code lines are pure type declarations (P-m's parameterized class) and
check for essentially nothing above the header. The honest figure is the net.

## 1. MACHINE AND PROCESS DISCIPLINE

ONE agda process at a time, `GHCRTS="-A64m -I0 -M8g"`, cap never raised, no
heap exhaustion, no kill, no run past 30 minutes. Machine: 16 cores, macOS,
Agda 2.8.0. Load was ~6 throughout (the sibling LJ-1-281 holds a slot; its
files under `agents/tasks/LJ-1-281/` are not mine and were not touched).

| run | exit | cold/warm | elapsed s | 1-min load |
|---|---|---|---:|---:|
| master, run 1 | 0 | cold (deleted .agdai) | 1.77 | 6.07 |
| master, run 2 | 0 | cold | 1.64 | 6.15 |
| master, run 3 | 0 | cold | 1.62 | 6.15 |
| `ReRun.agda` | 0 | cold (fresh) | 1.61 | 6.15 |
| `Baseline.agda` (import header only), mean of 3 | 0 | cold | 1.60 | ~6 |

Cold mean 1.68 s, range 1.62-1.77 s. An earlier three-run batch read
1.75/1.64/1.63 (mean 1.67); the two batches agree within noise. The baseline
(identical import header, one trivial definition) is 1.60 s mean, so A7's own
content is the 0.08 s difference.

## 2. THE ABORT CRITERION, FIXED BEFORE THE RUN (D-1)

- **IT LANDS GREEN.** This fires. STOP. The master is `--safe`, exit 0, and
  the re-run imports it and exits 0. See sections 4-6.
- **A5's LANDING LETS A7 NAME SOMETHING IT COULD NOT.** Does not fire as
  stated; the payoff is real but it is A2 + A4's, and it shows as a SMALLER
  import list, not a new A5 import. See section 3, premise 2.
- **A7 CANNOT BE STATED WITHOUT A6.** Does not fire. A7 is stated with
  `AbsorbsShape` as a hypothesis, which is exactly the point; it needs no
  import from A6. See section 3, premise 2.
- **A WALL.** Does not fire. Maximum single run 1.77 s.

## 3. PREMISES, EACH MARKED

**1. "A7 is a statement whose two hypotheses are unsupplied."** VERIFIED.
`agents/tasks/LJ-1-236/ProbeLJ1236A7.agda:147-157` defines `GCHStatement` with
`sq : SqShape` and `absorbs : AbsorbsShape` as Π-parameters; the guard at
`:165-171` builds only `hω`/`aω` and supplies neither. My master preserves
this: `src/L/GCH.lagda.md:66-76`.

**2. "A7's hypotheses are A5's and A6's conclusion types on the nose; check
what A7 can now name from a delivered master and what still has to be a
hypothesis."** VERIFIED, with one correction to `[LJ-1.268]`.

- On the nose: VERIFIED. `SqShape` (`src/L/GCH.lagda.md:42-45`) is A5's
  `Chain.theorem` conclusion `IsOrd α → (⟨α ∈ˢ ω⟩ → ⊥) → SQ.sq α` restated
  over the L-carrier; `AbsorbsShape` (`:49-53`) is A6's `ShiftAbs` readback
  `⟪sucV γ⟫ ↪ ⟪γ⟫` restated over the L-carrier, matching
  `lj-1.236-report.md` section 1.
- A5 rows 5 and 1 landed: VERIFIED. `src/L/InjChain.lagda.md` exists
  (`git status` shows it tracked, not my write) and is wired at
  `src/Everything.lagda.md:337`.
- A6 has not landed: VERIFIED. `src/L/Absorption.lagda.md` does not exist;
  `grep -rl "L.Absorption" src/` returns nothing.
- **What A7 names now, MEASURED: `_↪_` and `IsCardinalL` from `L.Cardinal`
  (A4), and NOTHING from A2 or A5.** This is the correction. `[LJ-1.268]`
  predicted A7 imports A2's `injAt` and A4's `InjCode`/`IsCardinalL`
  (`lj-1.268-report.md:173-176`). That prediction is superseded: A4's
  `L.Cardinal` absorbed `injAt` into `InjCode` and `InjCode` into
  `IsCardinalL`, so A7 imports only `IsCardinalL` (and the ambient `_↪_`)
  from `L.Cardinal`, and imports A2 not at all. A7's actual import list is a
  STRICT SUBSET of the predicted one.
- **A5's landing does not enter A7's closure.** MEASURED: A7 imports nothing
  from `L.InjChain`; `grep -rl "L.InjChain" src/` returns only
  `Everything.lagda.md` and `L.InjChain` itself, and `squareω`/`pairω` have
  no consumer in `src/`. This confirms `lj-1.279-report.md` section 4
  ("neither A6 nor A7 imports this master directly").
- **What still has to be a hypothesis:** `SqShape` and `AbsorbsShape`, both
  of them. A5's landing holds only `squareω : sq ω` (the base) and the
  composition machinery; the UNIFORM square law over all infinite L-ordinals
  (the `SqShape` inhabitant, A5's `Chain.theorem`) is not delivered.
  `L.Ordinal.SquareLaw`'s `via-col-square` is `Init`-restricted
  (`src/L/Ordinal/SquareLaw.lagda.md:960`), a narrower condition than
  `SqShape`'s "not finite". And A6 is not landed.

**3. "A7's home is `src/L/GCH.lagda.md`."** VERIFIED.
`lj-1.268-report.md:33-34` names it; I wrote it there, new.

**4. "A7 is priced at 33 lines, narrow caliber."** VERIFIED as the probe's
charge, and exceeded as the brief warned. The probe's 47 charge lines
(`lj-1.236-report.md` section 2) shrink to 47 code lines here (the inlined
`injAt`, `InjCode`, `IsCardinalL`, `_↪_` and the probe-only guard are gone,
replaced by imports), and the ledger caliber (non-blank in-fence, comments
included) is 63. I did not trim to 33.

**5. "A7 is tower-neutral on the Def-against-J axis."** VERIFIED.
`GCHStatement : ModelL.isZFModel → Type` names `S`, `∈ˢ`, `IsCardinalL` and
`_↪_`, and no `isL`, no `Lset`, no `orderAt`, no tower atom
(`src/L/GCH.lagda.md:66-76`). It takes the model as a parameter, exactly as
`ChoiceStatement` does.

## 4. WHAT THE MASTER EXPORTS

`src/L/GCH.lagda.md` exports four statement components plus one module alias:

| name | line | what it is | consumer |
|---|---|---|---|
| `SqShape` | 42 | A5's conclusion type, stated as a hypothesis type | the future `L⊨GCH` proof |
| `AbsorbsShape` | 49 | A6's conclusion type, stated as a hypothesis type | the future `L⊨GCH` proof |
| `SuccCardL` | 57 | δ is the successor cardinal of κ | the conclusion of `GCHStatement` |
| `GCHStatement` | 66 | the GCH statement, a Type over `isZFModel` | the future `L⊨GCH` proof |
| `ModelL` | 30 | `FOL.ZFModel 𝒮ʟ`, the model whose `isZFModel` the statement takes | technical; the future proof names it |

The opens (`S`, `_∈ˢ_`, `IsOrd`, `_↪_`, `IsCardinalL`, `⟪_⟫`, `ω`, `sucV`,
`#_`, `Empty.⊥`, `∥_∥₁`) are brought into scope with `using` and are NOT
re-exported; `lint-agda.py --check` exits 0, which is the import-necessity
check. `lint-prose.py --check` and `weave-i18n.py --check` both exit 0.

## 5. THE `src/Everything.lagda.md` LINE

**`import L.GCH`**, to be inserted **after line 366 (`import L.Cardinal`),
before line 367 (`import L.Choice.Internal`)**. A7's only project-master
dependency is `L.Cardinal` (line 366); every other import is `FOL.*`,
`V.Hierarchy`, `L.Constructible` or a library module, all earlier in the
catalog. I did NOT touch `Everything.lagda.md`; the orchestrator wires it.

## 6. THE RE-RUN (C-45)

**`agents/tasks/LJ-1-280/ReRun.agda`, exit 0, `--safe`, cold 1.61 s.** It
imports all four exports from `L.GCH` and uses each in a consumer-shaped
term:

- the C-38 guard, re-derived at this site: `Guard.aω : S` builds `ω` as an
  L-element from `Lset→isL`/`suc-ord`/`ω-ord`/`ord∈Lset-suc`, so the κ
  quantifier of `GCHStatement` is inhabited at a real site;
- `Concl zf κ` spells the truncated successor-cardinal conclusion with the
  master's `SuccCardL`;
- `apply` takes a hypothetical `proof : GCHStatement zf` and the two
  hypotheses `sq : SqShape`, `absorbs : AbsorbsShape`, and returns
  `Concl zf κ` by `proof sq absorbs κ cκ nfin`, which shows the master's
  statement is exactly the conditional Π-type the two hypotheses name.

`exit 0` of the master alone is not a supply; this re-run imports and applies
the master, which is the landing proof. One application detail, recorded
because it cost a fix: Agda does not reduce a term of SORT type
(`GCHStatement zf : Type (ℓ-suc ℓ)`) to its Π-form when that term is itself
applied, so the re-run applies a variable of type `GCHStatement zf` rather
than applying `GCHStatement zf` directly. The existing tree has the same
shape (`ChoiceStatement zf` is applied only through `hasChoiceL`, never
directly).

## 7. IMPORT LIST, ONE REASON PER IMPORT (THE GCH CLOSURE)

`src/L/GCH.lagda.md:6-30`, in order, with the reason each is necessary:

1. `open import Base.Prelude` (hub): `Type`, `Level`, `Σ`, `_×_`, `_→_`,
   `fst`, `snd`, `_≡_`, `ℕ`, the host vocabulary of the statement.
2. `open import Base.Truth` (hub): `TruthAlgebra`, `hPropAlgebra`, `⟨_⟩`,
   the truth-value coercion that wraps membership propositions.
3. `open import Base.Classical using (LEM)`: the module parameter `lem`,
   needed to instantiate `L.Cardinal`, which is parameterized by it.
4. `open import FOL.ZFStructure using (module hPropStructure)`: to open
   `_∈ˢ_` (over 𝒮ᵥ) and `S` (over 𝒮ʟ).
5. `import FOL.ZFModel`: `module ModelL = FOL.ZFModel 𝒮ʟ`; the statement
   quantifies over `ModelL.isZFModel` and uses its `𝒫` field.
6. `open import V.Hierarchy {ℓ} using (𝒮ᵥ)`: the ambient structure, for
   `_∈ˢ_`.
7. `open import L.Constructible {ℓ} using (𝒮ʟ; IsOrd)`: the L-carrier
   structure (for `S`) and `IsOrd`.
8. `open import L.Cardinal {ℓ} lem using (_↪_; IsCardinalL)`: the delivered
   A4, the ambient injection type and the internal cardinal.
9. `open import Cubical.HITs.CumulativeHierarchy.Base using (_∈_)`: ambient
   membership, for `⟨ fst κ ∈ fst δ ⟩` and `⟨ # k ∈ fst γ ⟩`.
10. `open import Cubical.HITs.CumulativeHierarchy.Properties using (⟪_⟫)`:
    the small index type of a set.
11. `open import Cubical.HITs.CumulativeHierarchy.Constructions using
    (module InfinitySet)` then `open InfinitySet {ℓ} using (ω; sucV; #_)`:
    `ω`, `sucV`, `#_`, for the infinity conditions and the absorption shape.
12. `import Cubical.Data.Empty as Empty`: `Empty.⊥`, the negation in
    "α is not finite".
13. `import Cubical.HITs.PropositionalTruncation as PT`; `open PT using
    (∥_∥₁)`: the truncation of the conclusion.

No import is A5 (`L.InjChain`) or A6 (nonexistent). No import is A2
(`L.Coding.Injection`) directly: it enters the closure only through
`L.Cardinal`. The transitive GCH closure is therefore the closure of
`L.Cardinal` plus the ambient masters above, and this master itself, the
same 48-master shape `[LJ-1.274]` computed, since A7's actual direct imports
are a subset of the imports that report assumed.

## 8. DD4, WITH THE AXIS

**Axis named (C-46): DD4's own axis is AC-against-GCH**, fixed in code at
`scripts/ledger.py:50`. On it this master is GCH-side content alone: it is
not reachable from `ac_root` (`src/L/Model.lagda.md:49-57`), and it is the
declared `gch_root`'s home.

**The import list above IS the GCH closure's root edge set.** Each import is
necessary (section 7); there is no edge to A5 or A6, so the closure
UNDERSTATES the eventual GCH proof, exactly as `[LJ-1.274]` section 1.4
measured.

**Which hypotheses become import edges once A6 lands, and which do not:**

- `absorbs : AbsorbsShape` **becomes an import edge** when A6 lands: the
  future `L⊨GCH` proof imports A6's absorption theorem from
  `src/L/Absorption.lagda.md` (399 lines plus A2, already in the closure), so
  `AbsorbsShape` stops being a bare hypothesis in the PROOF's closure. It
  does NOT change A7's own closure: A7 keeps it as a hypothesis by design,
  because the statement is the conditional.
- `sq : SqShape` **does not become an import edge when A6 lands.** A5's
  landing holds only the ω base (`squareω : sq ω`) and the composition
  machinery; the uniform square law over all infinite L-ordinals is not
  delivered. So `SqShape` stays a hypothesis until A5's uniform square-law
  chain lands (wave 3).

The day-one DD4 figure `[LJ-1.274]` computed (AC 73/17,197, GCH 48/8,731,
SHARED 43/7,596) is unchanged by this landing: A7's real import list is a
subset of the assumed one, so the closure is the same 48 masters, and the
understatement (hypotheses carrying no edges) is the one named above.

## 9. ARCHIVE USED (DD18)

One line read named per archived file.

- **`agents/tasks/LJ-1-236/ProbeLJ1236A7.agda`, read WHOLE.** TAKEN: the
  whole statement content. Line read `:147`, `GCHStatement : ModelL.isZFModel
  → Type (ℓ-suc ℓ)`.
- **`agents/tasks/LJ-1-236/lj-1.236-report.md`, read WHOLE.** TAKEN: the
  on-the-nose audit of section 1 and the 47-charge line count. Line read
  section 1's `SqShape`/`AbsorbsShape` block.
- **`agents/tasks/LJ-1-273/lj-1.273-report.md`, read WHOLE.** TAKEN: A7 is
  only the statement, and the chain shape. Line read section 1's verdict.
- **`agents/tasks/LJ-1-274/lj-1.274-report.md`, read WHOLE.** TAKEN: what the
  tool actually reads (`scripts/ledger.py:404-446`) and the understatement
  finding. Line read section 1.4.
- **`agents/tasks/LJ-1-279/lj-1.279-report.md`, read WHOLE.** TAKEN: A5's
  exports and the note that A7 does not import the master. Line read section
  4's "A7 needs A2's `injAt` and A4's `InjCode`/`IsCardinalL`", which this
  landing then superseded.
- **`agents/tasks/LJ-1-277/lj-1.277-report.md`, read WHOLE.** TAKEN: the
  landing method (re-run that imports the master), copied here. Line read
  section 4.
- **`archive/dev/TASKS-archived.md:72`.** TAKEN, SHAPE ONLY: `L3.32-T37`
  cardinal predicates built generally. The retired route held its internal
  predicates in one master.
- **`archive/dev/STATUS-archived.md:116`.** TAKEN, SHAPE ONLY: `L4.3`, the GCH
  endpoint is the active campaign's own, not a successor plan.
- **`archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md:582-583`.**
  TAKEN, SHAPE ONLY: `succCardFo` and the one-master predicates layout.
  **WHAT WOULD NOT TRANSFER:** the retired `cardFo` at `:562-563` is the
  BIJECTION form (`eqFo`); A-prime's `IsCardinalL` is the INJECTION form
  (`src/L/Cardinal.lagda.md`), so the archived body does not transfer, only
  the one-master shape.

## 10. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md:145-171`, read.** A7 IS Devlin's 5.6
(`:159`, "5.6 Theorem. V = L implies GCH"), the statement the twelve-row
chain funds; it is not one of the twelve steps but their conclusion.

**`dev/literature/devlin-II5.md:370-383`, read.** The twelve-row table. A7's
shape is row F's chain output (`:382`): 5.5 condensation plus
`|L_α| = |α|` plus initial ordinals, applied at κ⁺ (`:164-167`).

**Does Devlin state GCH in this shape? NO.** Devlin states GCH as the
LEVEL-containment `𝒫(κ) ⊆ L_{κ⁺}` (`:159-167`), obtained from 5.5 and
`|L_{κ⁺}| = κ⁺` (1.1(vii)). A7 states it as the successor-cardinal injection
`𝒫(κ) ↪ δ` where δ is the least cardinal above κ
(`src/L/GCH.lagda.md:66-76`). The two are equivalent only through the counting
`|L_{κ⁺}| = κ⁺`, which is exactly what A5's `sq` and A6's `absorbs` fund;
that is why A7 carries those two as hypotheses. This is the tree's own shape,
recorded at `lj-1.236-report.md` section 8.

## 11. THE NEGATIVES, CLASSIFIED

- **MEASURED FALSE. The master fails to typecheck.** exit 0, `--safe`, three
  cold runs and the re-run.
- **MEASURED FALSE. An import is not delivered.** `lint-agda.py --check`
  exits 0; every project import is a delivered master.
- **MEASURED FALSE. A wall.** Max single run 1.77 s.
- **MEASURED FALSE. I touched an existing master or `Everything.lagda.md`.**
  `git diff --stat` over tracked files is empty; only new files written.
- **MEASURED FALSE. I touched `L.Choice.Name` or `agents/tasks/LJ-1-281/`.**
  Neither appears in my writes; the sibling's files under
  `agents/tasks/LJ-1-281/` are untracked and not mine.
- **MEASURED. `[LJ-1.268]`'s predicted A7 import of A2's `injAt` is
  superseded.** A4's `L.Cardinal` absorbed it; A7 imports only
  `_↪_`/`IsCardinalL` from `L.Cardinal` and nothing from A2 or A5.
- **INFERRED. The whole-file rate over the bar is a header artifact, not a
  content cost.** The baseline measurement (1.60 s for the import header
  alone) makes the net content rate 0.16x; the content is the P-m
  parameterized class.
- **INFERRED. `absorbs` becomes an import edge when A6 lands, `sq` does not.**
  The proof-shape reading from `[LJ-1.274]` and `[LJ-1.268]`; MEASURED that
  neither A5's uniform square law nor A6 is delivered today.

## 12. WORKING TREE, AS THIS REPORT DESCRIBES IT

Four files written, all new: `src/L/GCH.lagda.md` (the master),
`agents/tasks/LJ-1-280/ReRun.agda` (the re-run),
`agents/tasks/LJ-1-280/Baseline.agda` (the import-header baseline probe), and
`agents/tasks/LJ-1-280/lj-1.280-report.md` (this file). No master, brief or
report edited. No `Everything.lagda.md` edit. No `dev/ledger.toml` edit. No
commit, no push, no `git checkout .`, stash, reset or clean. No `make check`;
the orchestrator runs it. ONE agda process at a time, cap never raised.

`scripts/lint-agda.py --check`, `scripts/lint-prose.py --check` and
`scripts/weave-i18n.py --check` all exit 0 on the master.

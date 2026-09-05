# LJ-1.412 report: the coded descent, from the case hypothesis the recursion holds

slot: `coder`. Written incrementally (C-22). No commit, no push. I wrote
only in `agents/tasks/LJ-1-412/`. Agda ran under the caliber the program
set on this pane, `GHCRTS="-A64m -I0 -M8g"`, one process. I did not set
`GHCRTS`. No heap event.

TARGET: one term `coded-descent` in
`agents/tasks/LJ-1-412/Probe412.agda`. `code-as-data` is a module
hypothesis. There is no `Ne°`, no `Good°`, no `SiteBound.β` and no
placement.

Direction file: retrieved live `dev/pod/direction.md:37` reads
`**NONE. The owner has written no direction yet.** Work to `dev/PLAN.md` section 0 and to`.
The dispatch text named one SRC collection after LJ-1, not after
`[LJ-2.5]`. This task is still LJ-1 work. No conflict with a Boundary
clause.

## VERDICT

**GO.** `coded-descent` typechecks, exit 0, one process, no heap event.
Every field of the conclusion is data. The membership field is extracted
from `Good` by `PT.rec`. The code field is `code-as-data` on that
truncated code. The arrow is `Small.small` and `Small.small-inj`. The
no-finite field is `nofin-at-selected` on the arrow.

`CallerNe°` is discharged. The placement bill of `[LJ-1.410]` is ended.
The remaining caller obligation is `code-as-data` itself. `[LJ-1.411]`
is not in this tree. The brief said to take the hypothesis anyway, and
that is what I did.

## 1. W3: `not-card-gives`, first

Stated alone in `agents/tasks/LJ-1-412/Probe412.agda` at `:53-68`. Run
before step 2 was written.

**GO.** Exit 0, real 1.66 s, same caliber, no heap event. Cone warm
(Cardinal already loaded). Not a cold price. Log:
`agents/tasks/LJ-1-412/runs/w3.out`.

**SIXTEEN non-blank code lines** for `not-card-gives` (`:53-68`). Brief
estimate: about 14. The body is one `lem` at the truncation: the `inl`
branch is the witness, the `inr` branch rebuilds `IsCardinalL κ` and
contradicts the hypothesis (`:65-68`). Shape of `[LJ-1.394]`'s
`amb-gives-merely` (`agents/tasks/LJ-1-394/Probe394.agda:144-154`).
Nothing of Probe394 is imported.

No `oκ` and no `ω`. Those enter the consumer, not this lemma.
`IsCardinalL` is the Pi at `src/L/Cardinal.lagda.md:230-233`. The code
quantifier is over all of `S`, not over a stage (`:233`).

## 2. THE OBLIGATION

`coded-descent` at `Probe412.agda:148-191`. **37 non-blank code lines**
(type plus body). Brief estimate: about 55. Comparables of shape, not of
size. Not funded against `[LJ-1.410]`.

Type (`:148-153`):

    coded-descent :
        (κ : S) (oκ : IsOrd (fst κ)) → ⟨ ω ∈ˢ fst κ ⟩
      → (IsCardinalL κ → Empty.⊥)
      → Σ[ δ ∈ S ] ( ⟨ fst δ ∈ˢ fst κ ⟩
                   × (⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥)
                   × (⟪ fst κ ⟫ ↪ ⟪ fst δ ⟫) )

No `∥ ∥₁` in the conclusion. The three fields are:

- `⟨ fst δ₀ ∈ˢ fst κ ⟩` from `PT.rec` on `⟨ Good κ d₀ ⟩` (`:162-165`)
- `⟨ fst δ₀ ∈ˢ ω ⟩ → Empty.⊥` from `nofin-at-selected` on the arrow
  (`:190-191`)
- `⟪ fst κ ⟫ ↪ ⟪ fst δ₀ ⟫` from `Small.small` and `Small.small-inj`
  (`:181-188`)

Full-file typecheck after the assembly: exit 0, real 1.67 s, cone warm,
same caliber, no heap event. Log:
`agents/tasks/LJ-1-412/runs/assembly-2.out`. A first assembly run
failed at the `Σ≡Prop` annotation (`runs/assembly.out`, exit 42, one
unsolved meta at `:174`). The cure is in section 6.

Assembly, seven steps, as the brief stated:

1. `not-card-gives` (`:53-68`). W3. Measured in section 1.
2. `Good` over the ambient carrier (`:77-82`) and `ord-form` (`:84-93`).
   `mem-ord` (`src/L/Ordinal.lagda.md:221`) gives the ordinal
   certificate. `L.Stage` reads `S` from `𝒮ᵥ`
   (`src/L/Stage.lagda.md:60`).
3. `leastOrd (Good κ)` on step 2 (`:156`, `src/L/Stage.lagda.md:149`).
   Minimality is free and this task does not spend it.
4. `δ₀ = (d₀ , isL-trans ...)` (`:167-168`). Constructibility from the
   membership and `snd κ` (`src/L/Constructible.lagda.md:379`). `isL`
   is an hProp: `PT.rec` extracts membership (`:162-165`) and the
   truncated code (`:170-177`) after `Σ≡Prop` identifies the L-element
   inside the truncation with `δ₀`. D-10: step 4 is true at this
   site. It typechecks.
5. `code-as-data κ δ₀` on step 4's truncated code (`:179`).
6. `module Small` at the three sets, two projections (`:181-188`), as
   `[LJ-1.402]` measured (`agents/tasks/LJ-1-402/Probe402.agda:81`).
   Built, not hypothesized. `module Small` is delivered at
   `src/L/Coding/Injection.lagda.md:123`.
7. `nofin-at-selected` on the arrow (`:190-191`). Rebuilt at `:120-132`.
   **THIRTEEN non-blank code lines**, same as `[LJ-1.410]`
   (`agents/tasks/LJ-1-410/lj-1.410-report.md:41`). Helpers rebuilt
   beside it: `mem-incl` (`:101-114`), `comp-inj` (`:116-118`). Nothing
   of Probe410 or Probe398 is imported.

The band membership is not in the type
(`agents/tasks/LJ-1-398/Probe398.agda:206`).

`[LJ-1.411]` is not in this worktree. I listed `agents/tasks/` and
there is no `LJ-1-411/` directory. The brief said: if that task
returned NO-GO, the hypothesis is still the right telescope. I built
against it.

## 3. THE MODULE HYPOTHESIS

`code-as-data` (`Probe412.agda:144-145`), at the type the brief names:

    (a b : S) → ∥ Σ[ F ∈ S ] InjCode F a b ∥₁
  → Σ[ F ∈ S ] InjCode F a b

Do not import Probe411. Do not rebuild it. The generic readback is not
a hypothesis: `Small` is opened in step 6.

## 4. WHAT A CALLER MUST PROVE

`code-as-data` is the hypothesis `coded-descent` takes. That is the
type the next brief is written from.

    CallerCode :
        (a b : S) → ∥ Σ[ F ∈ S ] InjCode F a b ∥₁
      → Σ[ F ∈ S ] InjCode F a b

`CallerNe°` of `[LJ-1.410]` (`agents/tasks/LJ-1-410/lj-1.410-report.md:145`)
is discharged. The two placement types of that report are not
obligations of this term:

- Gap 1, `place-δ` (`:158-162` of that report), is not asked. `δ` is
  selected over all ordinals by `leastOrd`, then rebuilt as an
  L-element by `isL-trans`. There is no `Mem (Lset (SiteBound.β κ))`.
- Gap 2, `place-F` (`:170-173` of that report), is not asked. The code
  is over all of `S`, which is the quantifier inside `IsCardinalL`
  (`src/L/Cardinal.lagda.md:233`).

Gap 3 stays retired. Infinity of `δ` is recovered from the arrow.

D-10: I did not prove `CallerCode` true. It is `[LJ-1.411]`'s
obligation. This task takes it as a module parameter.

This task does not discharge `L.StageCardinal`'s module parameter, does
not build the recursion, and does not inhabit `code-as-data`.

The band recursion's supplier `coded-arrow`
(`agents/tasks/LJ-1-398/Probe398.agda:192-193`) is a weakening of
`coded-descent`: drop `⟨ ω ∈ˢ fst κ ⟩` from the hypotheses and drop
the no-finite field from the conclusion. The recursion already holds
`⟨ ω ∈ x ⟩` in the negative case (`Probe398.agda:233`). A next brief
that wires this term into that supplier still owes `CallerCode`.

## 5. W2 (DD4)

`not-card-gives`, `Good`, `ord-form`, `nofin-at-selected` and
`coded-descent` are generic in `κ`. They name no cardinal. The only
named set is `ω`, which is the infinity hypothesis the brief writes
and the consumer's finite-exclusion target. No numeral. The module
hypothesis is generic in `a` and `b`. No fixed form was substituted
for a generic one.

## 6. WHAT RESISTED, WHAT WAS WEAKENED, WHAT DID NOT CLOSE

**Resisted.** Step 4's `Σ≡Prop`. The first assembly run left one
unsolved meta at `Probe412.agda:174` (`runs/assembly.out`, exit 42,
real 9.49 s). `λ x → snd (isL x)` did not pin `x` to the ambient
carrier while `S` from `𝒮ʟ` was in scope. The cure is an annotation,
not a truth change: `{A = V ℓ}`, `λ (x : V ℓ) → snd (isL x)`, and
`{u = δ} {v = δ₀}` (`:174-175`). After that, exit 0.

**D-10 at step 4.** `isL` is an hProp
(`src/L/Constructible.lagda.md:379-380` reads it through `PT.rec` into
`snd (isL y)`). The rebuilt `δ₀` is the selected L-element. Step 4
did not fail as a truth question.

**Weakened.** Nothing of the conclusion. The generic readback is
built from `Small`, not taken as a hypothesis.

**Did not close.** `CallerCode`. `[LJ-1.411]` is not in this tree.
`oκ` is spent by `ord-form` and by `nofin-at-selected`. The band
membership is not in this term.

## 7. RUNS

All runs: one Agda process, `GHCRTS="-A64m -I0 -M8g"` as set on the pane,
cap not raised, no heap event.

| step | file | real s | exit |
|---|---|---|---|
| W3 first, `not-card-gives` | Probe412.agda | 1.66 | 0 |
| assembly, unsolved `Σ≡Prop` | Probe412.agda | 9.49 | 42 |
| assembly, `coded-descent` | Probe412.agda | 1.67 | 0 |

The 1.66 s and 1.67 s figures are warm (Cardinal, Stage, InjChain and
Injection cones already loaded). They are the numbers this pane
measured. They are not a cold price. The 9.49 s figure is the failed
first assembly, with Injection loaded for the first time on this pane.

## ARCHIVE USED

- `archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md`. Read the
  opening. Not used. It is the retired bijection and CSB chapter, not
  the `leastOrd` selection this task assembles. Quote at
  `archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:4`:
  `The cardinal chapter's definitional layer fixed equinumerosity as the`
- `archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md`. Read
  the `isProp` packing of a truncated membership existential. Not used.
  This task does not pack `InjCode` as an hProp. Quote at
  `archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md:331`:
  `isPropPairsClause f = isPropΠ (λ p → isPropΠ (λ _ → squash₁))`
- `archive/src/2026-08-09-rud-route/L/Coding`. Listed the directory.
  Not read. Declined: the live `Small` is
  `src/L/Coding/Injection.lagda.md:123`.
- `archive/dev/JOURNAL-archived.md`. Read the opening. Not used. The
  live selection lives in `src/L/Stage.lagda.md` and
  `src/L/Cardinal.lagda.md`. Quote at
  `archive/dev/JOURNAL-archived.md:1`:
  `# Archived journal: the retired route`
- `archive/dev/TASKS-archived.md`. Read the opening. Not used. Same
  reason. Quote at `archive/dev/TASKS-archived.md:4`:
  `ruled the two-tower bridge route and then ruled that the task codes be`
- `dev/ARCHIVE.md`. Read the opening. Not used. It is the index of
  retired modules, not a descent construction. Quote at
  `dev/ARCHIVE.md:1`:
  `# ARCHIVE.md: the archive registry`

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`. Read. Used: the
  selection this assembly runs is `leastOrd` on an hProp guard `Good`.
  Quote at `dev/literature/truncation-and-selection.md:68`:
  `**The selection device is a definable well-order plus a universal guard.** The`
  The untruncation of the *code* is not that device. It is the module
  hypothesis `code-as-data`. Infinity is recovered after selection, so
  it is not part of the guard.
- `dev/literature/digest.md`. Read the opening. Not used. It is the
  rud-route digest, not this selection. Quote at
  `dev/literature/digest.md:1`:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`
- `dev/literature/terms-2026-08.md`. Read the opening. Not used. It is
  a terminology dossier, not a selection or descent fact. Quote at
  `dev/literature/terms-2026-08.md:1`:
  `# The terminology dossier: fourteen renderings for the owner's ruling`
- `dev/literature/BIBLIOGRAPHY.md`. Read the opening. Not used. It is
  the source list for the rud route, not this term. Quote at
  `dev/literature/BIBLIOGRAPHY.md:1`:
  `# Bibliography for the rud route`

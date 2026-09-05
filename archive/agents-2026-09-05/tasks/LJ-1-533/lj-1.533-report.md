# LJ-1.533 report: B9, and the code an ambient injection does not carry

## HEAD
head_slot: coder
machine: shared
verdict: NO-GO

The report was written as a skeleton before any Agda and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-533/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event. Nothing is postulated. The probe is a raw `.agda`
file, so it carries no ` ```agda ` fence, counts 0 in-fence lines, and the
ratio bar cannot fire on it.

## VERDICT

**NO-GO on `StageCountedCoded`.** The obstruction is
`agents/tasks/LJ-1-533/review-of-StageCountedCoded.md`.

**THE PROBE IS GREEN, EXIT 0, THREE RUNS.** `agents/tasks/LJ-1-533/Probe533.agda`,
`runs/full-1.out` to `runs/full-3.out`. It carries no hole and no postulate.
That is deliberate: a hole would have made every reduction in it a claim, and
green makes each one a measurement.

TWO findings, and the second was already in the tree.

1. **D-10. THE BRIEF'S TYPE IS FALSE.** It binds `IsOrd (fst δ)` and nothing
   else: no band membership, no infinitude. The delivered shadow binds BOTH.
2. **W3. NOTHING CODES AN ARBITRARY AMBIENT INJECTION, AND THIS WAS MEASURED
   TWICE BEFORE THIS TASK.** `[LJ-1.414]` refuted it generically and
   `[LJ-1.441]` refuted it at one named site. B9 is the third site of the
   same wall, not a new wall.

**WHAT THE TASK BOUGHT ANYWAY.** B9's corrected target now reduces to exactly
TWO named inputs and nothing else, both typechecked as reductions:
`Bill.reduce` (`Probe533.agda:236-241`) and `Bill.reduce-at-site`
(`:253-259`).

## WHAT CODES AN AMBIENT INJECTION

**NONE.** No term in `src/` and no term in any probe I read turns an arbitrary
ambient function into an `InjCode`.

**THE TYPE-LEVEL REASON, and it is stronger than a count.** An L-element set
is produced by exactly two generators:

- `hasSeparationL : (a : S) (φ : Formula S 1) → ...`
  (`src/L/Axioms/Full.lagda.md:144-146`)
- `hasReplacementL : (a : S) (φ : Formula S 2) → ...`
  (`src/L/Axioms/Full.lagda.md:277-280`)

**BOTH TAKE A `Formula` IN THEIR TYPE.** There is no way to call either
without one. And `_↪_` is a bare function with an injectivity proof,
`X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)`
(`src/L/Cardinal.lagda.md:47-48`). It carries no `Formula`.

**THE SWEEP (C-42), MY OWN, AT TODAY'S TREE.** Sites in `src/` that carve the
graph of a map as an L-element: **5**. With a `Formula`: **5**. Taking a bare
`_↪_`: **0**.

| site | the `Formula` | the graph |
|---|---|---|
| `src/L/InjChain.lagda.md:339` | `compFo` (`:222`) | composition |
| `src/L/InjChain.lagda.md:480` | `inclFo` (`:445`) | inclusion |
| `src/L/Absorption.lagda.md:413` | `shiftFo` (`:224`) | shift |
| `src/L/Coding/Key.lagda.md:272-273` | `envFoB` (`:246`) | environment |
| `src/L/Coding/Injection.lagda.md:212` | `rangeGraph F` (`:158`) | range of an ALREADY CODED `F` |

The last row is not a counterexample: its input `F` is already an L-element,
so it codes nothing new.

**THE DIRECTION THAT DOES EXIST IS THE CONVERSE.** `readL`
(`src/L/CantorBernstein.lagda.md:33-38`) reads an `InjCode` witness back as an
ambient injection. `coded→ambient` (`Probe533.agda:98-99`) is that, at the
truncated grade, typechecked. **Code buys ambient. Ambient buys nothing.**

**THE TWO PRIOR REFUTATIONS, NAMED SO NOBODY RE-BUYS THEM.**

- `agents/tasks/LJ-1-414/review-of-amb-to-coded.md`: the generic crossing.
  Its HALF B (`code-from-graph`) is GREEN; HALF A, the graph of an arbitrary
  ambient injection, has no producer. Two walls: an ambient function does not
  determine the members of an L-element, and the tree has no `Formula` for an
  arbitrary map.
- `agents/tasks/LJ-1-441/review-of-amb-to-coded-at-least.md`: the same wall at
  one named site, `d := κL a oa`. "So the ambient route is dead at its own
  site, not only at generality."

**WHAT THIS PRICES BEYOND B9.** Row **B10**, `SuccIntoPower`
(`agents/tasks/LJ-1-523/Probe523.agda:266-268`), concludes an `InjL` and is
the same shape: it meets this wall too.

**ROW B7 IS NOT THE SAME SHAPE, AND THE BRIEF SAYS IT IS.** `AbsorbsAt`
(`agents/tasks/LJ-1-523/Probe523.agda:234-238`) concludes
`⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫`, an AMBIENT injection. It wants no code at
all. A successor brief that priced B7 against this wall would price it against
a wall it does not meet. **So this finding blocks TWO rows, B9 and B10, not
three.**

## D-10

**I ran D-10 before any Agda, as the brief required, and it fired.**

**THE BRIEF'S TYPE (`Probe533.agda:80-83`):**

    StageCountedCodedᵀ =
        (δ Lδ : SL.S) → IsOrd (fst δ) → (fst Lδ ≡ Lset (fst δ))
      → InjL Lδ δ

**THE `Lδ` SLOT IS NOT A RESTRICTION.** `LsetS`
(`src/L/Axioms/Basic.lagda.md:160-161`) makes the stage of ANY ordinal an
L-element on the nose, so `refl` fills the third hypothesis. `stageL-fst`
(`Probe533.agda:140-141`) is that fact, typechecked.

**SO THE TYPE, SPENT, LANDS THE AMBIENT STATEMENT AT EVERY ORDINAL.**
`brief→ambient` (`Probe533.agda:145-150`) derives

    (δ : SL.S) → IsOrd (fst δ) → ∥ ⟪ Lset (fst δ) ⟫ ↪ ⟪ fst δ ⟫ ∥₁

from it by `readL`, adding NO hypothesis. `brief→ambient-at-numerals`
(`Probe533.agda:160-164`) instantiates it at every numeral `# n`.

**THE DELIVERED CHAPTER REFUSES EXACTLY THAT, IN TWO PLACES.**

1. `stage-card-upper` binds `⟨ α ∈ˢ ω ⟩ → Empty.⊥`
   (`src/L/StageCardinal.lagda.md:564-565`). The infinitude is a HYPOTHESIS of
   the shadow, and the brief's type has none.
2. At a finite δ the chapter's own branch does NOT go to δ. It goes to ω:
   `fin-inj : (δ : S) → ⟨ δ ∈ˢ ω ⟩ → ⟪ Lset δ ⟫ ↪ ⟪ ω ⟫`
   (`src/L/StageCardinal.lagda.md:488-490`), consumed at `:548` by
   `comp-inj (fin-inj δ δ∈ω) (WOEmb.ω-inj α oα infα)`. **A chapter that could
   land `⟪ Lset δ ⟫ ↪ ⟪ δ ⟫` at a finite δ would not need that branch and
   would not need `ω-inj` to carry it.**

**AND THE LITERATURE STATES THE THEOREM WITH THE INFINITUDE.**
`dev/literature/devlin-II5.md:347` records "L_α = V_α for α ≤ ω, |L_α| = |α|
for α ≥ ω", and `:281` repeats "|L_α| = |α| for infinite α". **The source of
the counting leg carries the hypothesis the brief dropped.**

**WHAT I DID NOT MEASURE, STATED AS A LIMIT AND NOT AS A RESULT.** I did not
prove `⟪ Lset δ ⟫ ↪ ⟪ δ ⟫` false in Agda at any named finite δ. Exhibiting the
members of `𝒟ₒ (Lset (# 2))` needs the definability machinery and I did not
price it. **What IS measured is that the brief's type is not reachable from the
delivered shadow, and that the shadow's own author excluded the finite case by
hypothesis.** That is a stop under the Boundary and I did not go past it.

**THE CORRECTED TARGET IS RECORDED BESIDE THE ORIGINAL**, as D-10 requires:
`StageCountedCoded′ᵀ` (`Probe533.agda:222-228`) adds both of the shadow's side
conditions back. It is not weaker than the delivered ambient statement:
`corrected→ambient` (`Probe533.agda:264-272`) recovers the ambient conclusion
from it.

## W3

**THE BRIEF NAMED THE CODING OF THE FUNCTION AS THE WIDEST UNMEASURED TERM.
IT WAS NOT UNMEASURED.** The measurement existed at
`agents/tasks/LJ-1-414/review-of-amb-to-coded.md` and
`agents/tasks/LJ-1-441/review-of-amb-to-coded-at-least.md`. I found it by
`grep -rn "amb-to-coded" .` before writing any Agda. Section
`## WHAT CODES AN AMBIENT INJECTION` is the answer.

**W3's Agda half is the pair of types in `Probe533.agda` sections 1 and 4**,
which turn the prose answer into something checkable: `AmbToCodeᵀ`
(`:111-114`) is the missing term, and `Bill.reduce` (`:236-241`) proves that it
is the ONLY missing term at this site, given the square-law family.

**COST: 0 Agda seconds for the answer** (it was a `grep` over the tree), and
the typechecked confirmation rides inside the probe's 3.4 s. The brief
estimated about 30 lines and under 45 seconds. **The estimate was for the
wrong work**: nothing had to be measured, only found.

## THE SECOND UNPAID INPUT, AND IT IS SMALLER THAN THE FIRST

`L.StageCardinal` binds an UNTRUNCATED square-law family
(`src/L/StageCardinal.lagda.md:17-19`), written out as `SqFamily`
(`Probe533.agda:183-184`). What `src/` delivers is TRUNCATED:
`sq-trunc-closed` (`src/L/SquareLawClosed.lagda.md:325-328`), re-typed and
typechecked at `Probe533.agda:190-193`. The band matches, the infinitude
matches, only the grade differs.

**THE BAND CONDITION ITSELF IS NOT A BLOCK.** `α₀` is a MODULE PARAMETER of
`L.StageCardinal` (`src/L/StageCardinal.lagda.md:16`), so at a single δ the
consumer takes `α₀ := δ` and `self∈sucV` (`src/V/Model.lagda.md:236-237`) pays
`⟨ δ ∈ˢ sucV δ ⟩`. `shadow-at-self` (`Probe533.agda:209-213`) is that,
typechecked.

## WHAT THE NEXT BRIEF SHOULD KNOW

**1. THE ROUTE THAT IS DEAD IS "BUILD AMBIENT, THEN CODE IT". THE ROUTE THAT
IS NOT PRICED IS "BUILD CODED AT THE CHAPTER'S OWN SITE".**

`stage-card-upper` is not an arbitrary ambient function in its ORIGIN. Its
counting is SYNTACTIC: `L.StageCardinal` imports
`FOL.Count using ( composed-count; code; shape-count-inj )`
(`src/L/StageCardinal.lagda.md:22`), and `Bound` builds the injection out of
`code` of a formula paired with a tuple of parameters. `formula-bound`
(`src/L/StageCardinal.lagda.md:177-185`) has DOMAIN `Formula K 1`, and
`tuple-g` (`:100-104`) carries the parameters. **The `Formula` that HALF A wants
exists at the site where the shadow is BUILT. `stage-card-upper`'s type throws
it away** by returning a bare `_↪_` (`:564-565`).

So B9 is dead THROUGH `stage-card-upper`, not dead outright. **The unpriced
question is what a coded restatement of the counting theorem costs at its own
site.** That is a mathematician's call and I did not price it: I have not read
the limit half, and `[LJ-1.523]`'s C-42 discipline forbids me pricing a cure
against a site I did not measure.

**2. AND THAT ROUTE ALSO CURES THE TRUNCATION.** `InjL a b` is itself
truncated, `∥ Σ[ F ∈ S ] InjCode F a b ∥₁` (`src/L/GCH.lagda.md:37-38`). A
coded conclusion is therefore a PROPOSITION, and
`dev/literature/truncation-and-selection.md:143` records the rule: "a
proposition-valued goal absorbs the truncation". **So a coded restatement can
spend `sq-trunc-closed` by `PT.rec` where the untruncated ambient conclusion
cannot.** Two problems, one cure.

**3. THE WARNING THAT GOES WITH IT.** `archive/dev/LJ-dispatch-index.md:190`
records `[LJ-1.114]`: "Thread the truncation from StageCardinal to Devlin55 |
WALL, ROUTE-LEVEL | Upper's h-inj needs ONE honest injection; two truncation
eliminations collide. Reverted; the cause is proved". **Somebody has already
walked into a truncation wall inside this exact module.** A brief that funds
point 2 must read that row first. I did not re-measure it and I do not know
whether the collision it names is the same one.

**4. B4 IS PAID AND STAYS PAID.** I imported `[LJ-1.528]`'s `ordL`
(`agents/tasks/LJ-1-528/Probe528.agda:93-94`) rather than rebuilding it, and
the import typechecks, so `[LJ-1.528]` is still green against today's `src/`.
The join's unpaid inputs are still SIX. **This task moved none of them, and
says so.**

**5. THE ARITHMETIC OF THE FINDING.** One missing piece, `AmbToCodeᵀ`, blocks
B9 and B10. It does NOT block B7, whatever the brief said.

## W2 AND W4, ANSWERED

**W2 (from DD4).** The probe is generic in `ℓ`, generic in the ordinal δ, and
generic in the band top `α₀`, which stays a module parameter of `Shadow`
(`Probe533.agda:196`) and `Bill` (`:229`). Nothing is written at a fixed
ordinal. `brief→ambient-at-numerals` (`:160-164`) is the one place a numeral
appears, and it is an INSTANCE of the generic `brief→ambient`, not a separate
proof. No conflict with a deadline arose.

**W4 (from DD13).** No module was retired and none is proposed for retirement.
The probe lands nothing in `src/`, so `dev/ARCHIVE.md` gains no row.

## MEASUREMENTS

Caliber `-A64m -I0 -M8g`, read off the pane, never set by me. One Agda process
at a time. No heap event and no WALL.

| run | what | real | peak RSS | rc |
|---|---|---|---|---|
| cold | first check, building `L.SquareLawClosed`, `L.Absorption`, `LJ-1-528.Probe528`, `LJ-1-526.Probe526` | 19.72 s | not captured | 0 |
| `runs/full-1.out` | `.agdai` deleted, dependencies warm | 3.48 s | 0.82 GB | 0 |
| `runs/full-2.out` | same | 3.42 s | 0.82 GB | 0 |
| `runs/full-3.out` | same | 3.39 s | 0.82 GB | 0 |
| `runs/final-1.out` | the FINAL file, after the last comment edit | 3.25 s | 0.82 GB | 0 |
| `runs/final-2.out` | same | 3.06 s | 0.82 GB | 0 |
| `runs/final-3.out` | same | 3.05 s | 0.82 GB | 0 |

`_build/2.8.0/agda/agents/tasks/LJ-1-533/Probe533.agdai` was deleted before
each of the six runs, so each measures this file's own elaboration against
warm dependencies. **`runs/full-*.out` were taken before a comment-only edit
that repaired one `file:line` citation.** `runs/final-*.out` carry the file's
`sha256` and are the record of the file as it now stands. No run reports an
error, an unsolved metavariable or a hole.

**THE FILE.** 270 lines, 235 non-blank, **111 code lines** (non-blank and not
a comment), of which 31 are the import and open block. The rest is comment,
because a NO-GO's value is in what it says about the tree.

**THE GATES, RUN INDIVIDUALLY AS THE BOUNDARY ASKS. ALL CLEAN.**
`lint-prose`, `lint-agda`, `check-probes` (5,782 tracked files, no probe
outside `agents/tasks/`), `check-closure` (102 masters), `check-fences` (102
masters), `check-spec-surface` (8 surface files), `ledger` (declaration clean,
standing 33,523 lines over 100 masters), `weave-i18n`, `check-glossary`,
`check-rule-ids`, `reuse lint`. I did not run `make typecheck`: it checks
`src/Everything.lagda.md` and this task changed no file under `src/`.

**ONE DEPARTURE, DECLARED.** `AGENTS.md:12` says to run every `python3`
command as `.venv/bin/python`. **This worktree has no `.venv`.** I used the
main checkout's pinned interpreter,
`/Users/alsg/Agentic/Bedrock/.venv/bin/python`, and ran every command with the
worktree as the working directory. I installed nothing and I created no venv
here.

## ESTIMATE AGAINST MEASURED

| item | brief's estimate | measured |
|---|---|---|
| the Agda | about 180 lines, obligation about 50 | 270 lines, 111 code lines, obligation NOT written |
| W3 | about 30 lines, under 45 s | answered by `grep`, 0 Agda seconds; confirmed inside the 3.4 s check |
| the obligation | GO turns six unpaid inputs into five | NO-GO. Six stays six |

**THE BRIEF'S COMPARABLE WAS SOUND AND THE TARGET WAS NOT.** `[LJ-1.528]`
built a cardinal statement in a comparable file, and this file is of that
shape and cost less. What the estimate could not price is that the obligation's
type was wrong.

## WHAT I DID NOT DO

- I did not inhabit `StageCountedCoded`, at the brief's type or at the
  corrected one.
- I did not weaken `InjL` to an ambient injection.
- I did not rebuild `stage-card-upper` (it is INSTANTIATED at
  `Probe533.agda:203-204`) or `ordL` (it is IMPORTED at `:71-72`).
- I did not touch B5.
- I did not postulate, and I added no axiom and no `src/` change.
  `AmbToCodeᵀ` and `SqFamily` appear ONLY as hypotheses of reductions.
- I did not prove the finite case false in Agda. See `## D-10`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ AND USED.** `:190` is
  "| LJ-1.114 | Thread the truncation from StageCardinal to Devlin55 | WALL, ROUTE-LEVEL | Upper's h-inj needs ONE honest injection; two truncation eliminations collide. Reverted; the cause is proved |",
  and it is the warning in `## WHAT THE NEXT BRIEF SHOULD KNOW` point 3.
  `:379` is
  "| LJ-1.324 | Transplant stage-card-upper | REFUTED, THE FIRST INGREDIENT IS THE GOAL. DD25 review not needed: it closes a lead and funds nothing | The generic engine survives, tower-blind |",
  a second refusal at this same module, which is why point 1 is written as an
  unpriced question and not as a recommendation.
- `archive/dev/JOURNAL-archived.md`: **DECLINED.** `:1` is
  "# Archived journal: the retired route". It records the route the owner
  replaced on 2026-08-09. B9 is on the live route. Not used.
- `archive/dev/JOURNAL.md`: **DECLINED.** `:1` is "# ARCHIVED 2026-08-20",
  and the body says the per-episode journal is retired in favour of
  `agents/tasks/<CODE>/`. The predecessor evidence this task needed was in
  those task directories and I read it there. Not used.
- `dev/ARCHIVE.md`: **DECLINED.** `:1` is "# ARCHIVE.md: the archive registry".
  It is the registry of retired MODULES. This task retires none, so it has no
  row to give and gains none. Not used.
- `archive/dev/DECISIONS-archived.md`: **DECLINED.** `:1` is
  "# Archived decisions: the D series", and the file itself says the whole `D`
  series was archived on 2026-08-09. A bare `D<n>` is not a rule in force.
  Not used.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ AND USED.** `:347` is
  "   L_α = V_α for α ≤ ω, |L_α| = |α| for α ≥ ω (`dev2.txt:109-130`,",
  and `:281` is
  "(ii), |L_α| = |α| for infinite α (1.1(vii)), and the cardinal fact".
  Both carry the infinitude hypothesis the brief's type dropped, and both are
  cited in `## D-10`.
- `dev/literature/truncation-and-selection.md`: **READ AND USED.** `:143` is
  "the reason: \"a proposition-valued goal absorbs the truncation\"", which is
  the rule behind `## WHAT THE NEXT BRIEF SHOULD KNOW` point 2: `InjL` is a
  proposition, so a coded conclusion can spend the truncated square law that
  the untruncated ambient conclusion cannot.
- `dev/literature/digest.md`: **DECLINED.** `:1` is
  "# Digest: the orthodox form of the rud route, pinned from the collected literature".
  It pins the RUD route. B9 sits on the `Def` tower's counting leg and no
  claim in this report turns on a rud fact. Not used.
- `dev/literature/rudimentary-functions.md`: **DECLINED.** `:1` is
  "# Rudimentary functions, closure, and the comprehension theorem". Same
  reason as `digest.md`: it is rud-route material and this task touches no rud
  term. Not used.
- `dev/literature/terms-2026-08.md`: **DECLINED.** `:1` is
  "# The terminology dossier: fourteen renderings for the owner's ruling".
  It is translation provenance for a glossary ruling. This report names no new
  term and adds no glossary entry. Not used.

# LJ-1.679 report: the bound is a member of the stage, Devlin 5.2 (b)

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.679
obligation: agents/tasks/LJ-1-679/Probe679.agda::bound-in-stage
verdict: **NO-GO on the closed term. GO on W3: the tree's `KFacts`
value escapes the stage, and the twelve numerals are members.**

The obligation term is not written. The witness meter reads
`1 UNRESOLVED of 1, 3.26 s, probe_red=False`
(`runs/meter-obligation.out:2`). The probe is green and carries no
hole (`runs/recheck-3.out`, `EXIT=0`). Nine other delivered names
meter `0 UNRESOLVED of 9, 40.18 s, probe_red=False`
(`runs/meter-names.out`). W3 meters `0 UNRESOLVED of 2, 1.54 s,
probe_red=False` (`runs/meter-w3.out`). The stated NO-GO is
`agents/tasks/LJ-1-679/review-of-bound-in-stage.md`. That file is the
critic's input and it does not close the task.

**THIS IS NOT A REFUTATION OF `BoundInStage`.** I did not build a
term of its negation. Devlin 5.2 (b) still has the stage reading
(`dev/literature/devlin-II5.md:98-99`).

Written as a skeleton before any Agda beyond the predecessor read
and filled as each answer landed (C-22). No commit, no push. I wrote
only inside `agents/tasks/LJ-1-679/`. Agda ran under the caliber the
program set on this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier,
ONE Agda process at a time. I did not set `GHCRTS`. Nothing is
postulated, every delivered file carries `--safe`, the delivered
probe carries no hole, and nothing lands in `src/`. The probe is a
raw `.agda` file, so it carries no ` ```agda ` fence, counts 0
in-fence lines, and the ratio bar cannot fire on it.

**NO HEAP WALL WAS MET ON THE DELIVERED SHAPE.** The highest peak of
a finished run is 1,793,654,784 bytes against the 2,147,483,648-byte
wide cap (`runs/floor-1.out`), which is 83 percent of it. No run
prints a heap event. The first FLOOR draft was a `[NotInScope]` on
`P673.P652.Frame652.A.Elementary`. The designed-hole floor is
`runs/floor-3.out`.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict.

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE
UNLESS THE ROW SAYS OTHERWISE.** `floor-1` rechecked `Probe673` and
its predecessors and is the one cold-probe row. This report does not
bound a cold-cache number for `src/`.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.673]` closed **NO-GO on the closed term `lset-grounded`** and
**GO on the Formula Code 1 and on the consumer of `hull-closed`**
(`agents/tasks/LJ-1-673/lj-1.673-report.md:8-10`). The standing coder
clause says a NO-GO predecessor is a stop. **It is not a stop here.**
The NO-GO is on inhabiting `LsetGrounded` as a closed term.
`Completeness` and `BoundInStage` are TYPES (`Probe673.agda:93-95`,
`:126-130`). The report does not name them FALSE. This task takes
those types. The critic of `[LJ-1.673]` upheld the NO-GO and asked
the next brief to carry `IsOrd` on the parameter
(`agents/tasks/LJ-1-673/review-of-LJ-1-673-1.md:157-160`).

`[LJ-1.667]` closed **NO-GO on `witnessed-lset`**. The syntax of
`matrix₃` is green (`Probe667.agda:72-76`). The report does not name
`matrix₃` FALSE. This task takes that syntax.

`[LJ-1.520]` closed **GO on `levelFo-Σ₁`**. `SameAsGraph` is a TYPE
(`Probe520.agda:192-195`). The report does not name it FALSE. This
brief takes it as a HYPOTHESIS in both directions and does not inhabit
it. `[LJ-1.672]` closed **NO-GO on `same-as-graph`**
(`agents/tasks/LJ-1-672/lj-1.672-report.md:8-11`) and does not name
the type FALSE.

`[LJ-1.494]` closed **NO-GO on `GraphSatAtStage` at W3**
(`agents/tasks/LJ-1-494/lj-1.494-report.md:125-130`). `hier-in-stage`
is a TYPE (`Probe494.agda:49-53`). The report does not name it FALSE.
I re-measure membership at this site. I do not transfer that NO-GO by
analogy.

The types I took are the types the predecessors DELIVERED:

| piece | type | site | verdict |
|---|---|---|---|
| `matrix₃` | 3-slot Δ₀, syntax | `Probe667.agda:72-76` | GO |
| `BoundInStage` | stage existential | `Probe673.agda:93-95` | TYPE, green; not inhabited |
| `Completeness` | codes of `Lset δ` and `δ` | `Probe673.agda:126-130` | TYPE, green; no `IsOrd` |
| `bound-from-stage` | consumer of `hull-closed` | `Probe673.agda:100-104` | GO |
| `SameAsGraph` | both directions, class carrier | `Probe520.agda:192-195` | TYPE, green; not inhabited |
| `KValue` | one `KFacts` at `Lset λ` | `src/L/Condensation.lagda.md:7380-7434` | GO, bound is the stage |
| `hier-in-stage` | `hierL δ` in `Lset α` | `Probe494.agda:49-53` | TYPE, green; not inhabited |
| `hull-closed` | hull's only closure rule | `src/L/Hull.lagda.md:415` | GO, in `src/` |

## 2. D-10, BEFORE ANY AGDA

The target is `BoundInStage` at `matrix₃` for hull codes of `Lset δ`
and `δ`, with `IsOrd` on `δ`. Devlin 5.2 (b)
(`dev/literature/devlin-II5.md:98-99`) states the stage reading
`(∀γ < α)(∀v)[v = L_γ ↔ v ∈ L_α ∧ L_α ⊨ ∃z φ(z,v,γ)]`. I did not find
a cardinality or Tarskian obstruction at that generality, once the
parameter is an ordinal.

What is at risk is the HYPOTHESIS that `SameAsGraph` at the class
carrier, plus `Lset-defines`, produces a witness that is a MEMBER of
`Lset lam`. `SameAsGraph` (`Probe520.agda:192-195`) is satisfaction
at `𝒮ʟ`. `BoundInStage` (`Probe673.agda:93-95`) is `AbsL.⊨ᵐ` of an
unbounded `∃̇` at the stage, so the witness ranges over `SL`
(`src/L/Hull.lagda.md:415`, `src/FOL/Semantics.lagda.md:100`). The
tree's one `KFacts` value is `K = Lset λ`
(`src/L/Condensation.lagda.md:7369-7373`). `hierL` is the witness
`Lset-defines` spends (`src/L/Hierarchy.lagda.md:656`).

The literature's bound is determined: `K(w,u)` says `w = K(u)`
(`dev/literature/level-formula-slot-roles.md:60`). `[LJ-1.520]`'s
`Matrix` closes `K` by a bare existential. Those are different
statements (`:62-63`).

The corrected target beside the original, as D-10 asks:
`At.CompletenessFrom` (`Probe679.agda:94-95`), `SameHyp → HierInStage
→ Completeness`, with `IsOrd` on the parameter
(`Probe679.agda:73-78`).

## 3. THE FLOOR, MEASURED BEFORE ANY PROOF

The standing coder clause orders a floor before a heavy object. I ran
it. `runs/FLOOR.agda.txt` is the obligation's whole type, `Probe652`,
`Probe673` and `Probe520` imported, `SameAsGraph` a hypothesis, `IsOrd`
on the parameter, and a HOLE where the term goes. It is `.agda.txt`
and not `.agda`, because conjunct 1 runs every `.agda` under this task
home (`agents/tasks/LJ-1-679/LJ-1.679.md:16-17`).

The first draft did not form. `runs/floor-1.out`: `[NotInScope]` at
`P673.P652.Frame652.A.Elementary` (`:10-12`), 138.59 s, peak
1,793,654,784 bytes. That run rechecked `Probe673` and its
predecessors. The fix is to import `Probe652` for `Elementary`, as
`[LJ-1.673]`'s own floor did.

**THE FRAME COSTS 5.66 s AND 959 MB, AND IT DOES NOT WALL.**
`runs/floor-3.out`: exit 42 at 5.66 s, peak 959,021,056 bytes, one
error and it is the designed hole (`[UnsolvedInteractionMetas]` at
`FLOOR.agda:63.20-24`, `:4-6`). **The obligation TYPE is well-formed.**
Importing `Probe673` (and through it `Probe667`, `Probe652`, `W3`,
`Probe520`) is not a wall. `SameAsGraph` as a hypothesis does not
make the type ill-formed.

The import trim is: `src/` plus `Probe652` plus `Probe673` plus
`Probe520`. That is the trim the floor measured. The delivered probe
uses the same imports plus `L.Hierarchy` for `hierL` and
`runs/W3.agda` for the membership lemmas.

## 4. W3, THE BOUND'S MEMBERSHIP IN `Lset lam`

The brief names it. Estimate 110 to 240 lines, basis
`agents/tasks/LJ-1-673/lj-1.673-report.md:1`.

**GO ON THE TWO MEMBERSHIP FACTS. NO-GO ON PUTTING THE BOUND IN THE
STAGE FROM `SameAsGraph` ALONE.**

`runs/W3.agda` proves two facts.

1. **`kvalue-escapes`** (`:36-37`). `⟨ Lset lam ∈ˢ Lset lam ⟩ → ⊥`,
   by `∈-irrefl` (`src/V/Hierarchy.lagda.md:155-156`). The tree's one
   `KFacts` value is `K = Lset λ`
   (`src/L/Condensation.lagda.md:7369-7373`). That value is not a
   member of the stage. First green run: exit 0 at 1.14 s, peak
   311,934,976 bytes (`runs/w3-2.out`). Final green run: 1.17 s, peak
   307,478,528 bytes (`runs/w3-final.out`).
2. **`Tags.tags-in-stage`** (`:46-47`). The twelve numerals ARE
   members of the stage. W2: `Bound.num∈λ`
   (`src/L/Coding/Bound.lagda.md:139-140`), not a second proof.

The estimate was 110 to 240 lines. W3 is 47 lines, 24 code. The
delivered probe is 99 lines, 46 code. Together 70 code lines. The new
mathematics is `kvalue-escapes` and the restated `Completeness` with
`IsOrd`. Completeness as a term is not in that count because it is
not written.

`SameAsGraph` lives at `𝒮ʟ`. `BoundInStage`'s `∃̇` ranges over `SL`.
A class-carrier agreement does not produce a stage member. That is
why `SameHyp` alone does not inhabit `Completeness`. `HierInStage`
(`Probe679.agda:84-88`) names the missing membership of `hierL`.
`CompletenessFrom` (`:94-95`) names the two hypotheses together.

This is the same class of fact `[LJ-1.664]` earned for `𝒟ₒ`: the
search's map is paid (`inBound`, `bound-from-stage`) and the object
that would fill the search is not a stage member. For `𝒟ₒ` the
Formula Code 1 was missing. For the bound the Formula Code 1 is
paid and the witness escapes.

## 5. W2

**Nothing is proved twice.** `[LJ-1.667]`'s `matrix₃` is imported,
not copied. `[LJ-1.673]`'s `BoundInStage` and `bound-from-stage` are
imported, not copied. `SameAsGraph` is `[LJ-1.520]`'s type, taken as
a hypothesis. `tags-in-stage` is `Bound.num∈λ`. `kvalue-escapes` is
one use of `∈-irrefl`. `Completeness` is restated with `IsOrd` on
the parameter. It is not a second proof of `[LJ-1.673]`'s type.
No deadline forced a fixed form. There is no conflict to report.

## 6. W4, AND P-l

**W4: not applicable.** No module was retired, nothing under `src/`
changed, and `dev/ARCHIVE.md` takes no row from this task. The ideal
form written fresh today is the form delivered: `Completeness` with
`IsOrd`, `SameAsGraph` a hypothesis, and a measured escape of the
tree's `KFacts` supply.

**P-l: obeyed.** No type in the probe names a stage presentation.
The statements quantify over `S`, `Lset` of a variable, and
`Frame652`'s hull. `⟪ Lset lam ⟫` appears nowhere.

## 7. THE LAWS IN THE BUNDLE

- **D-10** (`dev/LESSONS.md:1375`). Done in section 2. The recorded
  residue is `Completeness` / `BoundInStage` at `matrix₃`. The type
  with `IsOrd` is written. `SameAsGraph` and `HierInStage` are not
  inhabited. `Matrix₂` is not funded.
- **C-22** (`dev/LESSONS.md:2307`). The report was written as a
  skeleton before any Agda beyond the predecessor read and filled as
  each answer landed.
- **P-l** (`dev/LESSONS.md:2367`). Section 6.
- **D-26** (`dev/LESSONS.md:1735`). Did not bind. No well-founded key
  was built.
- **C-42** (`dev/LESSONS.md:3762`). No refutation of `BoundInStage`
  landed. `kvalue-escapes` is `∈-irrefl` at one candidate `K`, not a
  measurement that `BoundInStage` is false. The stop is that
  `SameAsGraph` at `𝒮ʟ` does not compose with `AbsL` at the stage
  without `HierInStage`. No sweep is owed.

## 8. RUNS

Caliber `-A64m -I0 -M2g`, the wide caliber, set on the pane by the
program and untouched here. One Agda process at a time. All runs from
the repository root.

| run | what | wall s | peak RSS bytes | exit |
|---|---|---:|---:|---:|
| `runs/w3-1.out` | W3, `⊥` clash and `numeralL` | 1.58 | 310,722,560 | 42 |
| `runs/w3-2.out` | W3 first green | 1.14 | 311,934,976 | 0 |
| `runs/floor-1.out` | FLOOR, `Elementary` path | 138.59 | 1,793,654,784 | 42 |
| `runs/floor-2.out` | FLOOR, `A.Code` not exported | 2.91 | 750,960,640 | 42 |
| `runs/floor-3.out` | obligation type, one hole | 5.66 | 959,021,056 | 42 |
| `runs/p-1.out` | probe, `SameAsGraph` clash | 3.19 | 789,839,872 | 42 |
| `runs/p-2.out` | probe, `At` shadowed | 3.20 | 789,856,256 | 42 |
| `runs/p-3.out` | probe, `SameHyp` universe | 3.92 | 897,138,688 | 42 |
| `runs/p-4.out` | first green probe | 6.67 | 1,345,241,088 | 0 |
| `runs/p-final.out` | after `public` re-export | 6.73 | 1,345,224,704 | 0 |
| `runs/recheck-1.out` | forced recheck | 3.18 | 654,753,792 | 0 |
| `runs/recheck-2.out` | forced recheck | 3.23 | 654,753,792 | 0 |
| `runs/recheck-3.out` | forced recheck | 3.01 | 654,737,408 | 0 |
| `runs/w3-final.out` | forced recheck of W3 | 1.17 | 307,478,528 | 0 |
| `runs/meter-obligation.out` | the obligation | 3.26 | not taken | 1 |
| `runs/meter-names.out` | 9 names | 40.18 | not taken | 0 |
| `runs/meter-w3.out` | 2 names | 1.54 | not taken | 0 |

Median of the three forced rechecks of the delivered probe **3.18 s**.
Highest peak of any finished run **1,793,654,784 bytes**
(`runs/floor-1.out`), 83 percent of the 2 GiB cap. Highest peak of a
green run **1,345,241,088 bytes** (`runs/p-4.out`), 63 percent of the
cap. No heap event. No restructuring was needed on the delivered
shape.

`w3-1` is `[AmbiguousName]` on `⊥` and a `using` miss for
`numeralL`. The fix is `Empty.⊥` and `L.Axioms.Numerals`. `p-1` is
`[ClashingDefinition]` on `SameAsGraph` with `Probe520.agda:192`.
The fix is `import` not `open import`. `p-2` is `[ShadowedModule]`
on `At`. `p-3` is `[UnequalSorts]` on `SameHyp`. All four are
plumbing.

Witness meter, one obligation: `runs/meter-obligation.out`,
`1 UNRESOLVED of 1`, `probe_red=False`. Witness meter, nine names:
`runs/meter-names.out`, `0 UNRESOLVED of 9`. Witness meter, W3:
`runs/meter-w3.out`, `0 UNRESOLVED of 2`. This worktree has no
`.venv`; the meter ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`.
I did not add a dependency and I did not create a local `.venv`.

**THE RATIO BAR CANNOT FIRE ON THIS RETURN.** The write scope holds no
`.lagda.md` and no ` ```agda ` fence, so the in-fence divisor is 0.
Nothing landed in `src/`.

## 9. PRICE

Non-blank non-comment lines counted by
`awk 'NF' file | grep -cv '^[[:space:]]*--'`.

| what | lines | code lines | at `file:line` |
|---|---:|---:|---|
| the probe, whole | 99 | 46 | `Probe679.agda` |
| W3, whole | 47 | 24 | `runs/W3.agda` |
| `kvalue-escapes` | 2 | 2 | `runs/W3.agda:36-37` |
| `tags-in-stage` | 2 | 2 | `runs/W3.agda:46-47` |
| `Completeness` with `IsOrd` | 6 | 6 | `Probe679.agda:73-78` |
| `HierInStage` | 5 | 5 | `Probe679.agda:84-88` |
| `CompletenessFrom` | 2 | 2 | `Probe679.agda:94-95` |
| floor slice | 63 | 32 | `runs/FLOOR.agda.txt` |

The brief estimated 110 to 240 lines. W3 plus the probe is 70 code
lines. Completeness as a term is not in that count.

## 10. WHAT THE SHAPE RESISTED

- **What it cost.** 70 code lines, median 3.18 s on a forced
  recheck, highest peak 1.79 GB against a 2 GB cap, no heap wall on
  the delivered shape.
- **What the shape resisted.** Four plumbing errors: `⊥` clash,
  `SameAsGraph` clash, `At` shadowing, `SameHyp` universe. The
  membership of `KValue`'s `K` compiled on the first attempt that
  got `Empty.⊥` and `numeralL` right. Completeness did not compile
  as a term because it was not written: `SameAsGraph` does not put
  a witness in `SL`.
- **What I had to weaken.** Nothing of the obligation. I did not
  inhabit `Completeness` from `SameAsGraph` alone and call it
  `bound-in-stage`. I named `HierInStage`. I did not inhabit
  `Matrix₂`.
- **What I could not close.** `bound-in-stage`, the stage
  existential at `inBound` for hull codes of `Lset δ` and `δ`,
  given only `SameAsGraph` and `IsOrd`.

## 11. WHAT THE NEXT BRIEF NEEDS

1. **FUND `HierInStage` AT THIS FRAME**, or an adequate `K` that is
   a member of `Lset lam` and contains the approximation. Do not
   use `KValue`'s `K = Lset λ` as that member. `kvalue-escapes` is
   green (`runs/W3.agda:36-37`).
2. **THEN FUND `CompletenessFrom`.** `SameHyp → HierInStage →
   Completeness` (`Probe679.agda:94-95`). Do not fund
   `bound-in-stage` from `SameAsGraph` alone. The class carrier is
   not the stage.
3. **DO NOT RE-DISPATCH `inBound`, `count-matrix₃`, OR
   `bound-from-stage`.** Green in `[LJ-1.673]`.
4. **DO NOT RE-DISPATCH THE SYNTAX OF THE 3-SLOT MATRIX.** `matrix₃`
   and `Δ₀-matrix₃` are green (`Probe667.agda:72-76`).
5. **DO NOT RE-DISPATCH PINS AT THE NUMERALS.** Green in
   `[LJ-1.672]`. `tags-in-stage` is `num∈λ`.
6. **DO NOT FUND `Matrix₂`.** D-10 in `[LJ-1.665]`
   (`lj-1.665-report.md:35-39`) still stands.
7. **THIS FRAME RUNS WIDE.** Highest peak 1.79 GB against a 2 GB cap,
   on a failed first floor that rechecked predecessors. The designed
   hole and every green run sat under 1.35 GB. The heavy tier is not
   needed.
8. This task changed nothing in `src/`.

## 12. GATES

Run individually while the work was live, as the Boundary requires:

- `scripts/gate/lint-agda.py --check`: exit 0, no output.
- `scripts/gate/check-probes.py --check`: `check-probes: clean (10492
  tracked files, no probe outside agents/tasks/ and no generated file)`.
- `scripts/gate/lint-prose.py --check`: exit 0, no output.

I did not run `make check`. I did not commit and I did not push.

**I DID write `review-of-bound-in-stage.md`, and that is a decision.**
The standing clause says a `review-of-*.md` is how a coder states a
NO-GO, and a NO-GO means the brief's type was not inhabited. The name
`bound-in-stage` is not inhabited. The two membership facts of W3
and the restated `Completeness` type with `IsOrd` are inhabited,
green and metered.

## ARCHIVE USED

- **`archive/dev/ORCHESTRATION.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# ORCHESTRATION: the orchestrator's operating rules`.
  It is the archived process document. This task measures a stage
  membership and does not consult dispatch process.
- **`archive/dev/DD-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# THE \`DD\` RULING SERIES, archived in full 2026-08-18`.
  W2 is live in the slot file. The archived DD row is not a type.
- **`archive/dev/PLAN-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# ARCHIVED 2026-08-20`. A history. The live status is
  `dev/pod/screen.toml`.
- **`archive/dev/TASKS-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# Archived task index: the \`L3.32-T\` series`. That
  series is not a predecessor of `BoundInStage`.
- **`archive/dev/STATUS-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# STATUS-archived: the goal table of the internalization route`.
  The internalization route is not this matrix.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md` READ.**
  `dev/literature/level-formula-slot-roles.md:27` reads
  `| 5 | Devlin 5.2 (b) | \`(∀γ<α)(∀v)[v = L_γ ↔ v ∈ L_α ∧ L_α ⊨ ∃z φ(z,v,γ)]\` | same | \`z\` | \`v\`, \`γ\` | **VALUE, ORDINAL** | \`_build/literature/dev2.txt:1193-1198\` |`.
  **This is `BoundInStage`.** The stage satisfies the existential.
  `hull-closed` searches that existential. The parameter role is
  ORDINAL, which is why `Completeness` now carries `IsOrd`.
  `dev/literature/level-formula-slot-roles.md:60` reads
  `Devlin's \`∃w\` carries the conjunct \`K(w,u)\`, "which says \`w = K(u)\`"`.
  The tree's `Matrix` closes `K` by a bare existential. Devlin
  determines the bound. `KValue` picks `K = Lset λ`, and that value
  is not a member of the stage.
- **`dev/literature/glossary-review-2026-08.md` DECLINED.** Not read
  beyond its first line. `:1` reads `# Glossary review: the 119 pre-protocol entries`.
  No naming question arose and this task proposes no `dev/glossary.toml`
  entry.
- **`dev/literature/BIBLIOGRAPHY.md` DECLINED.** Not read beyond its
  first line. `:1` reads `# Bibliography for the rud route`. No citation
  was added and no source was missing.
- **`dev/literature/primary-sources.md` DECLINED.** Not read beyond its
  first line. `:1` reads `# Primary sources, second round: Jensen manuscript, Devlin, Jech`.
  The slot arithmetic is in `level-formula-slot-roles.md` and the Σ₀
  shape is in `devlin-II5.md` (standing). A second round of source notes
  does not change a type.
- **`dev/literature/devlin-errata.md` DECLINED.** Not read beyond its
  first line. `:1` reads `# Devlin errata: documented error classes (do-not-repeat checklist)`.
  This task certifies no leaf as bounded and quotes no Δ₀ certificate
  from a scanned page, so the errata have nothing to bite.

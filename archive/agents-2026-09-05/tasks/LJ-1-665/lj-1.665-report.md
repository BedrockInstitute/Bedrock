# LJ-1.665 report: the certificate's remaining debt, as one type

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.665
obligation: agents/tasks/LJ-1-665/Probe665.agda::certificate-remainder
verdict: **GO on the obligation. The frames MEET. The remaining debt is
ONE function type, and it is written. [LJ-1.578]'s original `Certificate`
is NOT that type: three named bridges still sit between them, and they
are types, not prose.**

The obligation is green and metered (`runs/meter-obligation.out`,
`pass exit=0 5.69 s`, `0 UNRESOLVED of 1`, `probe_red=False`). Seventeen
names in the probe are green (`runs/meter-names.out`,
`0 UNRESOLVED of 17`).

**READ THESE FOUR SENTENCES BEFORE YOU QUEUE ANYTHING.**

1. **ONE `LevelFormula` PAYS CLAUSE (i) AT THE RULED INDEX AND CLAUSE
   (ii)'s `CodedCover`.** `Site.clause-i-from-level`
   (`Probe665.agda:114-117`) and `Site.cover-from-level` (`:121-122`)
   take the same argument. A sixth report that funds those two residues
   as two objects funds the same formula twice.
2. **CLAUSE (iii) IS A DIFFERENT FORMULA, ON A DIFFERENT ALPHABET.**
   `Matrix₂ Lset` is parameter-free, ambient, Δ₀, arity 2. `LevelFormula`
   is over hull codes, read at the stage. Nothing in this file sends one
   to the other.
3. **`[LJ-1.578]`'s `Certificate` IS NOT THIS WEEK'S TRIPLE.** The
   frames share one `HullStage` telescope (W3, `runs/W3.agda`, exit 0).
   The conclusions do not. The three bridges are `PreimageOrd`
   (`Probe665.agda:203-208`), `BridgeII` (`:215-216`) and `BridgeIII`
   (`:222-223`). `certificate-remainder` spends none of them.
4. **D-10 ON CLAUSE (iii): DO NOT FUND `Matrix₂`.** `[LJ-1.652]` already
   recorded that the literature's matrix has a witness slot
   (`lj-1.652-report.md:91-107`). `certificate-remainder-witnessed`
   (`Probe665.agda:245-259`) is the same assembly at that corrected
   shape, and it is green.

Written as a skeleton before any Agda beyond W3 and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-665/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier, ONE Agda process at a time.
I did not set `GHCRTS`. Nothing is postulated, every delivered file carries
`--safe`, the delivered probe carries no hole, and nothing lands in `src/`.
The probe is a raw `.agda` file, so it carries no ` ```agda ` fence, counts 0
in-fence lines, and the ratio bar cannot fire on it.

**NO HEAP WALL WAS MET ANYWHERE IN THIS TASK.** The highest peak of any run
is 1,465,761,792 bytes against the 2,147,483,648-byte wide cap
(`runs/p-delivered.out`), which is 68 % of it. The longest Agda run is
9.80 s (`runs/p-final.out`) against the caps I set (600 s for W3 and the
floor, 900 s for the probe). The caps are wall-clock caps enforced by a
perl alarm (`runs/run.sh` carries the mechanism), because this macOS has no
`timeout` ([LJ-1.602], [LJ-1.610]).

The standing direction (`dev/pod/direction.md:37`) says one SRC collection
after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1 work. It does not
start that collection and it does not start phase 3. No Boundary clause is
in conflict.

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE.** No
number here is a cold-cache number, and this report does not bound one.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.578]` closed **NO-GO on `cohyps-supplied`**
(`agents/tasks/LJ-1-578/lj-1.578-report.md:6`). The standing coder clause
says a NO-GO predecessor is a stop. **It is not a stop here.** The NO-GO is
on inhabiting `CoHyps`. `Certificate` is a TYPE in that green module
(`agents/tasks/LJ-1-578/Probe578.agda:525-534`), and `certificate-gives-cohyps`
is green (`:547-549`). This task takes `Certificate` as a type and inhabits
none of its three clauses. The report does not name `Certificate` FALSE.

The types I took are the types the predecessors DELIVERED:

| piece | type | site | verdict |
|---|---|---|---|
| `Certificate` | three syntactic clauses | `Probe578.agda:525-534` | TYPE, green; obligation NO-GO |
| clause (i) at the ruled index | `ClauseIAtOrd` from `Det`/`Wit` | `Probe642.agda:125-131`, `:182-184` | GO, reduced, not proved |
| clause (ii) consumer | `coded-cover-from-level : LevelFormula → CodedCover` | `Probe650.agda:385-386` | GO on the consumer; keystone STOP |
| clause (iii) `Commute` | `Matrix₂ Lset → Commute` | `Probe652.agda:305-306` | GO on `Commute`; obligation STOP |

I do not import `Probe578`. `[LJ-1.598]` measured that chain walls under the
wide cap (`agents/tasks/LJ-1-598/runs/chain-578.out`). `[LJ-1.650]`
re-measured the same wall at `LJ-1-595.Probe595` (`lj-1.650-report.md:54-67`).
Types from 578 are restated, each cited at the line they were read.

`[LJ-1.650]`, `[LJ-1.652]` and `[LJ-1.659]` each closed STOP on their own
obligation. None of those reports names `LevelFormula`, `Commute` or
`ClauseIAtOrd` FALSE. The standing clause forbids inhabiting a type a
predecessor failed to inhabit. This task takes those as hypotheses or as
already-green maps, and inhabits only the assembly.

## 2. W3, THE WIDEST UNMEASURED TERM

The brief names it: whether the three clauses' frames are compatible enough
to state in one module. Estimate 100 to 200 lines, basis `[LJ-1.649]` at
2.59 s.

**GO. THE FRAMES MEET.** `runs/W3.agda` states, in one `HullStage`
telescope, this week's three conclusions (`ClauseIAtOrd`, `CodedCover`,
`Commute`), 578's three conclusions (`DefinesLevel`, `DefinesCover`,
`DefinesLevelAcross`), `LevelFormula`, `Matrix₂`, `PreimageOrd` and the
one-liner `to-578-i`. It imports `src/` only. `runs/w3-1.out`: **exit 0 at
3.71 s, peak 701,579,264 bytes**, under the 600 s cap.

**THE INCOMPATIBILITY IS NOT THE FRAME. IT IS THE CONCLUSIONS.** W3's own
`Remainder` (`runs/W3.agda`, the last declaration) is already the one type
the brief asked for: hypotheses in, this week's triple out. It lives in
`Type (ℓ-suc (ℓ-suc ℓ))` because `Elementary` does
(`src/L/Hull.lagda.md:174`). 578's `Certificate` lives in `Type (ℓ-suc ℓ)`.
That universe gap is a fact about clause (iii)'s hypothesis, not about the
hull.

The estimate was 100 to 200 lines. W3 is 151 lines, 113 code. The delivered
probe is 259 lines, 156 code. The estimate is right about the whole file
and high about the assembly: the new mathematics is the swap and two
four-line adapters (`Probe665.agda:83-117`).

## 3. THE FLOOR, MEASURED BEFORE ANY PROOF

The standing coder clause orders a floor before a heavy object. I ran it.
`runs/FLOOR.agda.txt` is the obligation's whole type, the three this-week
probes imported, and a HOLE where the term goes. It is `.agda.txt` and not
`.agda`, because every `.agda` under a task home is a verification target
(`scripts/pod/facts.py:489`).

**THE FRAME COSTS 7.83 s AND 1.02 GB, AND IT DOES NOT WALL.**
`runs/floor-1.out`: exit 42 at 7.83 s, peak 1,017,659,392 bytes, one error
and it is the designed hole (`[UnsolvedInteractionMetas]` at
`FLOOR.agda:52.25-29`). Agda checked `Probe642`, `Probe650`, `Probe652` and
`Probe641` on the way in. **Importing the three this-week probes is not the
578-chain wall.** The 578-chain wall is why 578 itself is restated.

The import trim is: `src/` plus those three probes, and not `Probe578`.
That is the trim the floor measured.

The delivered file's first green run is 8.75 s at 1,188,216,832 bytes
(`runs/p-3.out`). The floor and the proof overlap at this caliber. The
object is frame-bound; the assembly is below the noise of the three
imports.

## 4. THE ASSEMBLY

`certificate-remainder` (`Probe665.agda:229-242`):

    certificate-remainder :
        (lam ...) (lf : LevelFormula) (elem : Elementary) (mx : Matrix₂ Lset)
      → ClauseIAtOrd × CodedCover × Commute

That is `[LJ-1.578]`'s `Certificate` assembled from every clause this week
closed, with the still-open clauses as explicit hypotheses and their types
written out. The three conjuncts are this week's types, not 578's. Section
4.2 says why.

### 4.1 What is closed, and what is spent

| conjunct | closed map spent | hypothesis still open |
|---|---|---|
| (i) `ClauseIAtOrd` | `F642.graph-gives-clause-i` (`Probe642.agda:182`) via `clause-i-from-level` (`Probe665.agda:114`) | `LevelFormula` |
| (ii) `CodedCover` | `C650.coded-cover-from-level` (`Probe650.agda:385`) | the same `LevelFormula` |
| (iii) `Commute` | `F652.Instances.commute-from-lset-formula` (`Probe652.agda:255`) | `Elementary` and `Matrix₂ Lset` |

The slot-order adapter is the only new term. `LevelFormula` is value then
index (`Probe650.agda:322-328`). `Det`/`Wit` are index then value
(`Probe642.agda:91-97`). `transpose` (`Probe665.agda:91-95`) is one
instance of `⊨-rename` (`src/FOL/Manipulation/Renaming.lagda.md:127-129`).
`det-from-level` and `wit-from-level` (`Probe665.agda:99-112`) are the two
sides. Completeness of `LevelFormula` already carries a truncated
satisfier, so `Holds` and `level-in-stage` are not spent.

### 4.2 Why 578's `Certificate` is not the conclusion

`Certificate578` (`Probe665.agda:198-199`) is restated in the same `Site`
module as the assembly. The three bridges are named there. None is
inhabited except the first, and that one only under a hypothesis
`[LJ-1.642]` deleted.

| bridge | what it asks | why `certificate-remainder` does not spend it |
|---|---|---|
| `to-578-i` (`:207-208`) | `PreimageOrd`: `IsOrd (π (val c)) → IsOrd (val c)` | `[LJ-1.642]` ruled the index to the value and deleted this supplier. Putting it back undoes the ruling. |
| `BridgeII` (`:215-216`) | `CodedCover → DefinesCover` | `CodedCover` names a code; `DefinesCover` names a formula, and asks `IsOrd (π (val d))` rather than `IsOrd (val d)`. `[LJ-1.654]` built the forward ordinal map (`Probe654.agda:337`). The formula half is not a predecessor term. Building it would be building clause (ii). |
| `BridgeIII` (`:222-223`) | `Elementary → Matrix₂ Lset → DefinesLevelAcross` | `Commute` is an equation. `DefinesLevelAcross` is a formula in the hull. Closing the equation does not produce that formula. Building it would be building clause (iii). The type lives one universe up because `Elementary` does. |

**So the campaign's remaining debt on the certificate, counted as one
type, is the type of `certificate-remainder`, not the type of
`Certificate578`.** A brief that funds the three bridges funds 578's
original. A brief that funds `LevelFormula`, `Elementary` and the
corrected (iii) hypothesis funds this week's object. They are not the
same brief.

### 4.3 D-10, the (iii) hypothesis

D-10 (`dev/LESSONS.md:1375`) asks for the truth of a recorded residue
before its proof is priced. The recorded residue for (iii) is `Matrix₂
Lset`, because that is what `[LJ-1.652]` closed `Commute` from. **The
literature says that object does not exist as Δ₀.**
`dev/literature/devlin-II5.md:95-96` gives a Σ₀ formula `Φ(z, v, γ)` with
a witness slot; the graph is `∃z Φ`, which is Σ₁.

The corrected residue is already a type in `[LJ-1.652]`: `Witnessed Lset`
and `LsetGrounded` (`Probe652.agda:87-91`, `:260-264`).
`certificate-remainder-witnessed` (`Probe665.agda:245-259`) is the
assembly at that shape, green, same (i) and (ii). I record it beside the
original, as D-10 asks. I do not inhabit `Matrix₂`. I do not inhabit
`Witnessed`. Both remain hypotheses.

## 5. W2

**Nothing is proved twice.** The three closed maps are imported, not
copied. `Probe642`, `Probe650` and `Probe652` are each `src/`-only (652
pulls 641, also `src/`-only), so the import is the honest way to take a
predecessor's term and the floor measured it under the cap.

The swap is an instance of `⊨-rename`, not a second proof of renaming.
`[LJ-1.659]` already wrote the same instance the other way
(`Probe659.agda:185-214`). Restating it here is the instantiation at
`LevelFormula`, which 659 did not feed to `Det`/`Wit`. I did not import
659: that file is a STOP on a different arrow, and the swap is four lines
of `src/` instantiated.

578's three types are restated. W2 forbids a second proof without a
reason; the reason is the measured 578-chain wall, the same reason
`[LJ-1.650]` recorded. No deadline forced a fixed form. There is no
conflict to report.

## 6. W4, AND P-l

**W4: not applicable.** No module was retired, nothing under `src/`
changed, and `dev/ARCHIVE.md` takes no row from this task. The ideal form
written fresh today is the form delivered: one function type at one hull.

**P-l: obeyed.** No type in the probe names a stage presentation. The
statements quantify over `HS.M`, `T.Code`, `Lset` of a variable, and
`C.π` of a variable. `⟪ Lset lam ⟫` appears nowhere.

## 7. THE LAWS IN THE BUNDLE

- **D-10** (`dev/LESSONS.md:1375`). Done in section 4.3. The recorded
  (iii) residue is `Matrix₂`; the corrected residue is `Witnessed` plus
  `LsetGrounded`; both assemblies are green; neither hypothesis is built.
- **C-22** (`dev/LESSONS.md:2307`). The report was written as a skeleton
  before any Agda beyond W3 and filled as each answer landed.
- **P-l** (`dev/LESSONS.md:2367`). Section 6.
- **D-26** (`dev/LESSONS.md:1735`). Did not bind. No well-founded key was
  built.
- **C-42** (`dev/LESSONS.md:3762`). No refutation landed. The
  incompatibility is that two green types do not compose without extra
  hypotheses. It is not a measurement that a named statement is false, so
  no sweep is owed.

## 8. RUNS

Caliber `-A64m -I0 -M2g`, the wide caliber, set on the pane by the program
and untouched here. One Agda process at a time. All runs from the
repository root.

| run | what | wall s | peak RSS bytes | exit |
|---|---|---:|---:|---:|
| `runs/w3-1.out` | W3, types only, `src/` only | 3.71 | 701,579,264 | 0 |
| `runs/floor-1.out` | three probes imported, one hole | 7.83 | 1,017,659,392 | 42 |
| `runs/p-1.out` | `Fin` name clash | 3.48 | 647,544,832 | 42 |
| `runs/p-2.out` | `BridgeIII` universe | 6.31 | 688,439,296 | 42 |
| `runs/p-3.out` | first green draft | 8.75 | 1,188,216,832 | 0 |
| `runs/p-final.out` | forced recheck, interface deleted | 9.80 | 854,982,656 | 0 |
| `runs/p-final-2.out` | forced recheck | 9.51 | 920,977,408 | 0 |
| `runs/p-final-3.out` | forced recheck | 8.24 | 1,180,631,040 | 0 |
| `runs/p-delivered.out` | delivered file, comment-only edit | 7.65 | 1,465,761,792 | 0 |
| `runs/meter-obligation.out` | the obligation | 5.69 | not taken | 0 |
| `runs/meter-names.out` | 17 names, grouped | 5.35 | not taken | 0 |

Median of the three forced rechecks **9.51 s**. Highest peak of any run
**1,465,761,792 bytes** (`runs/p-delivered.out`), 68 % of the 2 GiB cap.
No heap event. No restructuring was needed: the first import shape is the
delivered shape.

`p-1` is `[AmbiguousName]` on `Fin` (`Cubical.Data.Fin` against
`Base.Prelude`). The fix is deleting that import. `p-2` is
`[UnequalSorts]` on `BridgeIII`: `Elementary` is `Type (ℓ-suc (ℓ-suc ℓ))`
and I had written `Type (ℓ-suc ℓ)`. Both are plumbing. The assembly was
green on the next run.

Witness meter, one obligation: `runs/meter-obligation.out`,
`0 UNRESOLVED of 1`, `probe_red=False`. Witness meter, seventeen names:
`runs/meter-names.out`, `0 UNRESOLVED of 17`. This worktree has no
`.venv`; the meter ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`.
I did not add a dependency and I did not create a local `.venv`.

**THE RATIO BAR CANNOT FIRE ON THIS RETURN.** The write scope holds no
`.lagda.md` and no ` ```agda ` fence, so the in-fence divisor is 0.
Nothing landed in `src/`.

## 9. PRICE

Non-blank non-comment lines counted by `awk 'NF' file | grep -cv '^\s*--'`.

| what | lines | code lines | at `file:line` |
|---|---:|---:|---|
| the probe, whole | 259 | 156 | `Probe665.agda` |
| header and imports | 53 | 29 | `:1-53` |
| the assembly (swap, adapters, pack) | 103 | 67 | `:55-157` |
| 578 restated, and the three bridges | 68 | 38 | `:157-224` |
| the obligation and the D-10 sibling | 32 | 22 | `:225-259` |
| W3 slice | 151 | 113 | `runs/W3.agda` |
| floor slice | 52 | 31 | `runs/FLOOR.agda.txt` |

The brief estimated 100 to 200 lines. The delivered probe is 156 code
lines, of which 38 are the 578 restatement the assembly does not spend.

## 10. WHAT THE SHAPE RESISTED

- **What it cost.** 156 code lines, median 9.51 s on a forced recheck,
  highest peak 1.47 GB against a 2 GB cap, no heap wall.
- **What the shape resisted.** Almost nothing. Two type errors, both
  plumbing: a `Fin` import clash and a universe annotation on a bridge
  that is not inhabited. The three closed maps composed on the first
  attempt that compiled.
- **What I had to weaken.** Nothing in the assembly. I did not inhabit
  578's `Certificate`. That is the measurement in section 4.2, not a
  weakening of a proof.
- **What I could not close.** `LevelFormula`, `Elementary`, and either
  `Matrix₂ Lset` or `Witnessed Lset` plus `LsetGrounded`. Those three
  (two, under D-10) are the remaining debt. I built no clause.

## 11. WHAT THE NEXT BRIEF NEEDS

1. **FUND `LevelFormula`, ONCE.** It pays clause (i) at the ruled index
   and clause (ii)'s `CodedCover` (`Probe665.agda:114`, `:121`). Do not
   fund `Det`, `Wit`, `Holds`, `CodedCover` or `ClauseIAtOrd` as separate
   objects at this frame. `[LJ-1.659]` already named the missing pair
   `Sound` and `Complete` (`Probe659.agda:155-161`) and the arrow
   `level-from-laws` (`:199-214`). `[LJ-1.651]`'s bare `Formula Code 2`
   is not this object.
2. **FUND `Elementary` SEPARATELY.** It is not a formula, it lives one
   universe up, and clause (iii) cannot start without it. The type is
   `src/L/Hull.lagda.md:174-176`.
3. **FOR CLAUSE (iii), FUND `Witnessed Lset` AND `LsetGrounded`, NOT
   `Matrix₂`.** D-10 in section 4.3. The consumer is already green
   (`Probe652.agda:266-268`, spent at `Probe665.agda:155`).
4. **DO NOT FUND `[LJ-1.578]`'s `Certificate` AND DO NOT FUND
   `PreimageOrd`.** The ruling at `[LJ-1.642]` deleted the collapse
   index. Putting it back is a different campaign choice, and it is the
   three bridges in section 4.2, not a missing piece of this week's
   triple.
5. **THIS FRAME RUNS WIDE.** Highest peak 1.47 GB against a 2 GB cap.
   The heavy tier is not needed. Importing `Probe578` is still forbidden
   by the measured wall; importing 642/650/652 is not.
6. This task changed nothing in `src/`.

## 12. GATES

Run individually while the work was live, as the Boundary requires:

- `scripts/gate/lint-agda.py --check`: exit 0, no output.
- `scripts/gate/check-probes.py --check`: `check-probes: clean (10144 tracked
  files, no probe outside agents/tasks/ and no generated file)`.
- `scripts/gate/lint-prose.py --check`: exit 0, no output.

The probe interface was deleted after the last run, so the working tree
carries no generated file. I did not run `make check`. I did not commit
and I did not push.

**I did NOT write `review-of-certificate-remainder.md`, and that is a
decision.** The standing clause says a `review-of-*.md` is how a coder
states a NO-GO, and a NO-GO means the brief's type was not inhabited.
The name `certificate-remainder` is inhabited, green and metered. The
one thing a reader must not miss is in the HEAD block and in section
4.2: the inhabited type is this week's triple, and 578's original still
asks for three bridges.

## ARCHIVE USED

- **`archive/dev/ORCHESTRATION.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# ORCHESTRATION: the orchestrator's operating rules`.
  It is the archived process document. This task assembles types already
  delivered in live probes and does not consult dispatch process.
- **`archive/dev/PLAN-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# ARCHIVED 2026-08-20`. A history. The live status is
  `dev/pod/screen.toml`.
- **`archive/dev/DD-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# THE \`DD\` RULING SERIES, archived in full 2026-08-18`.
  W2 is live in the slot file. The archived DD row is not a type.
- **`archive/dev/STATUS-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# STATUS-archived: the goal table of the internalization route`.
  The internalization route is not this assembly.
- **`archive/dev/TASKS-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# Archived task index: the \`L3.32-T\` series`. That
  series is not a predecessor of `Certificate`.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md` READ.**
  `dev/literature/level-formula-slot-roles.md:26` reads
  `| 4 | Devlin 5.2 (a) | \`Φ(z,v,γ)\` with \`∀v∀γ [v = L_γ ↔ ∃z Φ(z,v,γ)]\` | 3 in \`Φ\`, ONE closed | \`z\` at position 0 | \`v\` at 1, \`γ\` at 2 | **VALUE, ORDINAL** | \`_build/literature/dev2.txt:1186-1191\` |`.
  **This is `LevelFormula`'s slot order**, value then index, which is why
  the swap in section 4.1 exists: `[LJ-1.642]`'s `Det`/`Wit` are index
  then value. Without this row the two-variable formula could have been
  fed to `graph-gives-clause-i` unswapped and the term would have been
  wrong in a way that still typechecks against a symmetric hypothesis.
- **`dev/literature/glossary-review-2026-08.md` DECLINED.** Not read
  beyond its first line. `:1` reads `# Glossary review: the 119 pre-protocol entries`.
  No naming question arose and this task proposes no `dev/glossary.toml`
  entry.
- **`dev/literature/primary-sources.md` DECLINED.** Not read beyond its
  first line. `:1` reads `# Primary sources, second round: Jensen manuscript, Devlin, Jech`.
  The slot arithmetic and the Σ₀ shape are already in the two files this
  task used. A second round of source notes does not change a type.
- **`dev/literature/BIBLIOGRAPHY.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# Bibliography for the rud route`. No citation was
  added and no source was missing.
- **`dev/literature/devlin-errata.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# Devlin errata: documented error classes (do-not-repeat checklist)`.
  This task certifies no leaf as bounded and quotes no Δ₀ certificate, so
  the errata have nothing to bite. The D-10 finding on `Matrix₂` is taken
  from `devlin-II5.md:95-96` (standing) and from `[LJ-1.652]`'s own
  report, not from the errata list.

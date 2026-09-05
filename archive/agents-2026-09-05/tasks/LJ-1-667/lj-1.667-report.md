# LJ-1.667 report: the witnessed matrix clause three actually wants

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.667
obligation: agents/tasks/LJ-1-667/Probe667.agda::witnessed-lset
verdict: **NO-GO on the obligation. The syntax of the witness slot
is written. The ambient reading of that syntax does not give
soundness, and it does not give a hull member.**

The obligation term is not written. The witness meter reads
`1 UNRESOLVED of 1, 3.36 s, probe_red=False`
(`runs/meter-obligation.out:2`). The probe is green and carries no
hole (`runs/p-final-3.out`, `EXIT=0`). Eleven other delivered names
meter `0 UNRESOLVED of 11, 3.78 s, probe_red=False`
(`runs/meter-names.out`). The stated NO-GO is
`agents/tasks/LJ-1-667/review-of-witnessed-lset.md`. That file is the
critic's input and it does not close the task.

**THIS IS NOT A REFUTATION OF `Witnessed Lset`.** I did not build a
term of its negation. The literature still has a Σ₀ formula with a
witness slot (`dev/literature/devlin-II5.md:95-96`).

Written as a skeleton before any Agda beyond the predecessor read
and filled as each answer landed (C-22). No commit, no push. I wrote
only inside `agents/tasks/LJ-1-667/`. Agda ran under the caliber the
program set on this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier,
ONE Agda process at a time. I did not set `GHCRTS`. Nothing is
postulated, every delivered file carries `--safe`, the delivered
probe carries no hole, and nothing lands in `src/`. The probe is a
raw `.agda` file, so it carries no ` ```agda ` fence, counts 0
in-fence lines, and the ratio bar cannot fire on it.

**NO HEAP WALL WAS MET ANYWHERE IN THIS TASK.** The highest peak of
any run is 1,499,840,512 bytes against the 2,147,483,648-byte wide
cap (`runs/w3-3.out`), which is 70 % of it. The longest Agda run is
12.06 s (`runs/p-3.out`).

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict.

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE.**
No number here is a cold-cache number, and this report does not bound
one.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.652]` closed **NO-GO on `picommute-D-from-elem`**
(`agents/tasks/LJ-1-652/lj-1.652-report.md:27-35`). The standing
coder clause says a NO-GO predecessor is a stop. **It is not a stop
here.** The NO-GO is on inhabiting `PiCommuteD` from elementarity and
a two-slot matrix. `Witnessed` is a TYPE in that green module
(`Probe652.agda:87-91`), and `LsetGrounded` is a TYPE (`:260-264`).
`commute-from-witnessed` is green (`:266-268`). This task takes those
as types. The report does not name `Witnessed` or `LsetGrounded`
FALSE.

The types I took are the types the predecessors DELIVERED:

| piece | type | site | verdict |
|---|---|---|---|
| `Witnessed` | 3-slot Δ₀, soundness only | `Probe652.agda:87-91` | TYPE, green |
| `LsetGrounded` | hull witness for that formula | `Probe652.agda:260-264` | TYPE, green; not inhabited |
| `commute-from-witnessed` | consumer | `Probe652.agda:266-268` | GO |
| `certificate-remainder-witnessed` | assembly | `Probe665.agda:245-259` | GO |
| `elem` | `A.Elementary` | `src/L/BoundedSubset.lagda.md:759` | GO, inside `WithCode` |
| `elem-at-collapse-free` | collapse-site elementarity | `Probe655.agda:300` | GO, chapter telescope |
| `lset-formula` | 2-slot Σ₁ over `Code` | `Probe651.agda:141-142` | GO; different alphabet, different grade |
| `Matrix` | bounded graph with `transK` and `pins` | `Probe520.agda:53-128` | GO, syntax |

I do not inhabit `Matrix₂`. D-10 on clause (iii) is already recorded
(`agents/tasks/LJ-1-665/lj-1.665-report.md:35-39`).

## 2. W3, THE WITNESS SLOT'S CONTENT

The brief names it. Estimate 100 to 220 lines, basis `[LJ-1.651]` at
156 lines (`agents/tasks/LJ-1-651/lj-1.651-report.md:1`).

**GO ON THE SYNTAX. NO-GO ON WHAT THE AMBIENT READING DOES WITH IT.**

`runs/W3.agda` instantiates `[LJ-1.520]`'s `Matrix` at fifteen slots
(twelve tags, value, parameter, witness) and binds the twelve tags
by `∃̇∈` over the witness (`:56-76`). `count-three = refl` (`:83-84`).
Erase sends the result to `⊥*` (`:88-92`). First green run of that
file with erase: **exit 0 at 10.01 s, peak 1,499,840,512 bytes**
(`runs/w3-3.out`). The wrap-arity error on the first attempt
(`runs/w3-1.out`, `[UnequalTerms]`, `lastFin {n}` at `Fin n`) is
plumbing: the bound term of `∃̇∈` lives in the outer environment.

`matrix₃` (`Probe667.agda:72-73`) is that erased matrix conjoined
with `isOrd-at-p` (`:59-65`), so the parameter is an ordinal in the
object language. Δ₀ is delivered (`:75-76`). Slot order is
Witnessed's: value, parameter, witness.

The estimate was 100 to 220 lines. W3 is 97 lines, 65 code. The
delivered probe is 168 lines, 62 code. Together 127 code lines, inside
the estimate. The new mathematics is the wrap and the erase. Soundness
is not in that count because it is not written.

## 3. THE FLOOR, MEASURED BEFORE ANY PROOF

The standing coder clause orders a floor before a heavy object. I ran
it. `runs/FLOOR.agda.txt` is the obligation's whole type, `Probe652`
imported, and a HOLE where the term goes. It is `.agda.txt` and not
`.agda`, because every `.agda` under a task home is a verification
target (`scripts/pod/facts.py:489`).

**THE FRAME COSTS 3.51 s AND 737 MB, AND IT DOES NOT WALL.**
`runs/floor-1.out`: exit 42 at 3.51 s, peak 736,739,328 bytes, one
error and it is the designed hole (`[UnsolvedInteractionMetas]` at
`FLOOR.agda:48`). **The obligation TYPE is well-formed.** Importing
`Probe652` (and through it `Probe641`) is not a wall.

The import trim is: `src/` plus `Probe652` plus `LJ-1-520.Probe520`
(via W3) plus `runs/W3.agda`. That is the trim the floor and W3
measured.

## 4. D-10, AND WHAT THE AMBIENT READING CANNOT GIVE

D-10 (`dev/LESSONS.md:1375`) asks for the truth of the target before
its proof is priced. The target `Witnessed Lset` is the literature's
shape (`dev/literature/devlin-II5.md:95-96`). I did not find a
cardinality or Tarskian obstruction to it. **The HYPOTHESIS that the
ambient V reading of a 3-slot Δ₀ matrix spends `Lset-only` is what
is at risk.**

`Lset-only` (`src/L/Hierarchy.lagda.md:334-335`) discharges
`a ≡ Lset p` from `LsetGraphAt` at 𝒮ʟ, with `IsOrd` on the parameter.
Three bridges sit between `matrix₃` and that lemma. None is a
predecessor term that this task may inhabit.

1. **Carrier.** `EraseTransfer`
   (`src/L/Condensation.lagda.md:287-305`) moves a Δ₀ reading UP from
   𝒮ʟ to V, at a constructible environment. Witnessed quantifies over
   arbitrary `S`. The transfer does not move V down, and it does not
   apply when `a`, `p`, `z` fail `isL`.
2. **Bounded to unbounded.** `[LJ-1.520]` named `SameAsGraph`
   (`Probe520.agda:192-195`) and did not inhabit it. No module
   `GraphAgree` exists under `src/`. The leaf chain that would feed
   it is commented as unplaced
   (`src/L/Condensation.lagda.md:5477-5480`).
3. **`IsOrd`.** Witnessed's soundness has none. `isOrd-at-p` is in
   the formula so that, if the two bridges above close,
   `Amb.isOrdAt-out` plus `Lset-only` fire. It is not the conversion.

`LsetGrounded` (`Probe652.agda:260-264`) still asks for a hull member
`z` such that the ambient formula holds of `(Lset δ, δ, z)`. For
`matrix₃` that `z` is a bound containing the twelve numerals and the
approximation table. Putting that bound in the hull is a hull-closure
fact. The ambient reading does not produce it.

## 5. ELEMENTARITY, RE-MEASURED AT THIS FRAME

Premise 4 of the brief: take `elem` from
`src/L/BoundedSubset.lagda.md:759` and report if it does not reach.
**It does not reach `Frame652`.** `elem` lives in
`HullElemDown.WithCode` (`src/L/BoundedSubset.lagda.md:681-682`,
`:759`). `ElemReach.CodePair` (`Probe667.agda:139-142`) is the pair
that module asks for, restated at this frame, not inhabited.
`[LJ-1.655]` closed `elem-at-collapse-free` at the chapter telescope
(`Probe655.agda:300`), which carries κ, a cardinal, a square and
absorbs. That telescope is not `Frame652`'s. The Boundary forbids
transferring a measured cure by analogy; the type `CodePair` is the
re-measurement at this site.

`ElementaryAt` (`Probe667.agda:130-131`) is `F.A.Elementary` at
`Type (ℓ-suc (ℓ-suc ℓ))`, the universe `[LJ-1.665]` already recorded
for `BridgeIII` (`Probe665.agda:222`).

## 6. W2

**Nothing is proved twice.** `[LJ-1.520]`'s `Matrix` is imported and
instantiated (`runs/W3.agda:49`). The wrap is one `∃̇∈` at a generic
arity (`:56-57`), applied twelve times. Erase is
`BoundedSubset.erase-Δ₀`. `isOrd-at-p` is the ordinal formula of
`src/L/BoundedSubset.lagda.md:795-798` spelled at arity 3 with the
parameter in slot 1, because `renameFo` preserves arity. It is not a
second proof of ordinal-hood. `[LJ-1.652]`'s `Witnessed` and
`LsetGrounded` are imported, not copied. No deadline forced a fixed
form. There is no conflict to report.

## 7. W4, AND P-l

**W4: not applicable.** No module was retired, nothing under `src/`
changed, and `dev/ARCHIVE.md` takes no row from this task. The ideal
form written fresh today is the form delivered: a 3-slot Δ₀ matrix
at a generic `Matrix`, erased, with the three soundness bridges named.

**P-l: obeyed.** No type in the probe names a stage presentation.
The statements quantify over `S`, `Lset` of a variable, and
`Frame652`'s hull. `⟪ Lset lam ⟫` appears nowhere.

## 8. THE LAWS IN THE BUNDLE

- **D-10** (`dev/LESSONS.md:1375`). Done in section 4. The recorded
  (iii) residue is `Witnessed` plus `LsetGrounded`. The syntax of
  `Witnessed` is written. The ambient reading does not inhabit
  soundness or `LsetGrounded`. `Matrix₂` is not funded.
- **C-22** (`dev/LESSONS.md:2307`). The report was written as a
  skeleton before any Agda beyond the predecessor read and filled as
  each answer landed.
- **P-l** (`dev/LESSONS.md:2367`). Section 7.
- **D-26** (`dev/LESSONS.md:1735`). Did not bind. No well-founded key
  was built.
- **C-42** (`dev/LESSONS.md:3762`). No refutation landed. The stop is
  that two green types do not compose without extra hypotheses. It
  is not a measurement that a named statement is false, so no sweep
  is owed.

## 9. RUNS

Caliber `-A64m -I0 -M2g`, the wide caliber, set on the pane by the
program and untouched here. One Agda process at a time. All runs from
the repository root.

The first `run.sh` used a perl alarm, copied from `[LJ-1.665]`. On
this pane that wrapper returned `time: signal: Invalid argument` and
`EXIT=1` with no Agda error (`runs/p-1.out`). The working shape is
`/usr/bin/time -l agda`. `runs/run.sh` was rewritten to that shape.
`p-1` is not a price.

| run | what | wall s | peak RSS bytes | exit |
|---|---|---:|---:|---:|
| `runs/w3-1.out` | W3, wrap arity | 2.94 | 654,622,720 | 42 |
| `runs/w3-2.out` | W3, three-slot Δ₀, no erase | 2.90 | 516,341,760 | 0 |
| `runs/w3-3.out` | W3, with erase | 10.01 | 1,499,840,512 | 0 |
| `runs/p-2.out` | probe, `CodePair` universe | 7.91 | 908,886,016 | 42 |
| `runs/p-3.out` | first green probe | 12.06 | 1,295,187,968 | 0 |
| `runs/floor-1.out` | obligation type, one hole | 3.51 | 736,739,328 | 42 |
| `runs/p-4.out` | import trim, `∅` missing | 3.52 | 592,625,664 | 42 |
| `runs/p-5.out` | probe after `∅` restored | 10.02 | 1,483,784,192 | 0 |
| `runs/p-final-1.out` | forced recheck | 9.44 | 1,489,960,960 | 0 |
| `runs/p-final-2.out` | forced recheck | 10.94 | 1,489,551,360 | 0 |
| `runs/p-final-3.out` | forced recheck | 10.58 | 1,482,178,560 | 0 |
| `runs/meter-obligation.out` | the obligation | 3.36 | not taken | 1 |
| `runs/meter-names.out` | 11 names, grouped | 3.78 | not taken | 0 |

Median of the three forced rechecks **10.58 s**. Highest peak of any
run **1,499,840,512 bytes** (`runs/w3-3.out`), 70 % of the 2 GiB cap.
No heap event. No restructuring was needed: the first import shape
that compiled is the delivered shape.

`w3-1` is `[UnequalTerms]` on `lastFin {n}` at `Fin n`. The fix is
wrapping from `suc (suc n)` to `suc n`. `p-2` is `[UnequalSorts]` on
`CodePair`: `Elementary` is `Type (ℓ-suc (ℓ-suc ℓ))` and the code
pair is `Type (ℓ-suc ℓ)`. `p-4` is `[NotInScope]` for `∅` after an
over-trim. All three are plumbing.

Witness meter, one obligation: `runs/meter-obligation.out`,
`1 UNRESOLVED of 1`, `probe_red=False`. Witness meter, eleven names:
`runs/meter-names.out`, `0 UNRESOLVED of 11`. This worktree has no
`.venv`; the meter ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`.
I did not add a dependency and I did not create a local `.venv`.

**THE RATIO BAR CANNOT FIRE ON THIS RETURN.** The write scope holds no
`.lagda.md` and no ` ```agda ` fence, so the in-fence divisor is 0.
Nothing landed in `src/`.

## 10. PRICE

Non-blank non-comment lines counted by
`awk 'NF' file | grep -cv '^[[:space:]]*--'`.

| what | lines | code lines | at `file:line` |
|---|---:|---:|---|
| the probe, whole | 168 | 62 | `Probe667.agda` |
| W3, whole | 97 | 65 | `runs/W3.agda` |
| W3 wrap and three-slot | 21 | 21 | `runs/W3.agda:56-76` |
| W3 erase | 12 | 6 | `runs/W3.agda:86-97` |
| `matrix₃` and ordinal conjunct | 31 | 16 | `Probe667.agda:46-76` |
| soundness bridges, comments | 27 | 2 | `Probe667.agda:78-109` |
| elementarity reach | 24 | 12 | `Probe667.agda:120-142` |
| `LsetGroundedAt` | 11 | 9 | `Probe667.agda:154-163` |
| floor slice | 48 | 22 | `runs/FLOOR.agda.txt` |

The brief estimated 100 to 220 lines. W3 plus the probe is 127 code
lines.

## 11. WHAT THE SHAPE RESISTED

- **What it cost.** 127 code lines, median 10.58 s on a forced
  recheck, highest peak 1.50 GB against a 2 GB cap, no heap wall.
- **What the shape resisted.** Three plumbing errors: wrap arity,
  `CodePair` universe, and an over-trim of `∅`. The syntax of the
  witness slot compiled on the first attempt that got those three
  right. Soundness did not compile because it was not written: the
  three bridges in section 4 have no delivered inhabitant.
- **What I had to weaken.** Nothing of the obligation. I did not
  weaken Witnessed's soundness to `IsOrd`, I named the bridge. I did
  not inhabit `Matrix₂`.
- **What I could not close.** `witnessed-lset`, the soundness
  conjunct of `Witnessed Lset` at `matrix₃`, `LsetGrounded` at that
  formula, and `elem` at `Frame652` from
  `src/L/BoundedSubset.lagda.md:759`.

## 12. WHAT THE NEXT BRIEF NEEDS

1. **FUND `SameAsGraph` / GraphAgree, AT `[LJ-1.520]`'s `Matrix`.**
   Both directions. Without it, `matrix₃` cannot spend `Lset-only`.
   `[LJ-1.520]` already named the type (`Probe520.agda:192-195`) and
   left it uninhabited.
2. **FUND THE HULL-MEMBERSHIP OF THE BOUND.** That is `LsetGrounded`
   at `matrix₃`, not a second formula. The consumer
   `commute-from-witnessed` (`Probe652.agda:266-268`) is already
   green.
3. **IF CLAUSE (iii) MUST SPEND `elem` FROM `:759` AT `Frame652`,
   FUND THE CODE PAIR.** `ElemReach.CodePair` (`Probe667.agda:139-142`).
   `[LJ-1.655]`'s free term is at a bigger telescope and does not
   transfer.
4. **DO NOT FUND `Matrix₂`.** D-10 in section 4. The literature's
   matrix has a witness slot
   (`dev/literature/level-formula-slot-roles.md:26`).
5. **DO NOT RE-DISPATCH THE SYNTAX OF THE 3-SLOT MATRIX.** `matrix₃`
   and `Δ₀-matrix₃` are green. `[LJ-1.651]`'s two-slot Σ₁ formula over
   `Code` is a different alphabet and a different grade, as
   `[LJ-1.665]` already said (`lj-1.665-report.md:26-29`).
6. **THIS FRAME RUNS WIDE.** Highest peak 1.50 GB against a 2 GB cap.
   The heavy tier is not needed.
7. This task changed nothing in `src/`.

## 13. GATES

Run individually while the work was live, as the Boundary requires:

- `scripts/gate/lint-agda.py --check`: exit 0, no output.
- `scripts/gate/check-probes.py --check`: `check-probes: clean (10333
  tracked files, no probe outside agents/tasks/ and no generated file)`.
- `scripts/gate/lint-prose.py --check`: exit 0, no output.

The probe interface was deleted after the last run, so the working
tree carries no generated file. I did not run `make check`. I did not
commit and I did not push.

**I DID write `review-of-witnessed-lset.md`, and that is a decision.**
The standing clause says a `review-of-*.md` is how a coder states a
NO-GO, and a NO-GO means the brief's type was not inhabited. The name
`witnessed-lset` is not inhabited. The syntax of the witness slot is
inhabited, green and metered.

## ARCHIVE USED

- **`archive/dev/ORCHESTRATION.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# ORCHESTRATION: the orchestrator's operating rules`.
  It is the archived process document. This task writes a 3-slot matrix
  from live probes and does not consult dispatch process.
- **`archive/dev/DD-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# THE \`DD\` RULING SERIES, archived in full 2026-08-18`.
  W2 is live in the slot file. The archived DD row is not a type.
- **`archive/dev/PLAN-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# ARCHIVED 2026-08-20`. A history. The live status is
  `dev/pod/screen.toml`.
- **`archive/dev/STATUS-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# STATUS-archived: the goal table of the internalization route`.
  The internalization route is not this matrix.
- **`archive/dev/TASKS-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# Archived task index: the \`L3.32-T\` series`. That
  series is not a predecessor of `Witnessed`.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md` READ.**
  `dev/literature/level-formula-slot-roles.md:26` reads
  `| 4 | Devlin 5.2 (a) | \`Φ(z,v,γ)\` with \`∀v∀γ [v = L_γ ↔ ∃z Φ(z,v,γ)]\` | 3 in \`Φ\`, ONE closed | \`z\` at position 0 | \`v\` at 1, \`γ\` at 2 | **VALUE, ORDINAL** | \`_build/literature/dev2.txt:1186-1191\` |`.
  **This is the witness slot.** Three slots in Φ, one closed. The
  consumer's order is value then parameter then witness
  (`Probe652.agda:90`). The literature's order is witness then value
  then ordinal. The wrap in W3 produces the consumer's order.
- **`dev/literature/BIBLIOGRAPHY.md` DECLINED.** Not read beyond its
  first line. `:1` reads `# Bibliography for the rud route`. No citation
  was added and no source was missing.
- **`dev/literature/primary-sources.md` DECLINED.** Not read beyond its
  first line. `:1` reads `# Primary sources, second round: Jensen manuscript, Devlin, Jech`.
  The slot arithmetic is in `level-formula-slot-roles.md` and the Σ₀
  shape is in `devlin-II5.md` (standing). A second round of source notes
  does not change a type.
- **`dev/literature/glossary-review-2026-08.md` DECLINED.** Not read
  beyond its first line. `:1` reads `# Glossary review: the 119 pre-protocol entries`.
  No naming question arose and this task proposes no `dev/glossary.toml`
  entry.
- **`dev/literature/devlin-errata.md` DECLINED.** Not read beyond its
  first line. `:1` reads `# Devlin errata: documented error classes (do-not-repeat checklist)`.
  This task certifies no leaf as bounded and quotes no Δ₀ certificate
  from a scanned page, so the errata have nothing to bite. The D-10
  finding on `Matrix₂` is taken from `devlin-II5.md:95-96` (standing)
  and from `[LJ-1.652]`'s own report.

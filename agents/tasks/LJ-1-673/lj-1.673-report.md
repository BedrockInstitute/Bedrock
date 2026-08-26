# LJ-1.673 report: the bound is a hull member

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.673
obligation: agents/tasks/LJ-1-673/Probe673.agda::lset-grounded
verdict: **NO-GO on the closed term. GO on the Formula Code 1 and
on the consumer of `hull-closed`.**

The obligation term is not written. The witness meter reads
`1 UNRESOLVED of 1, 3.03 s, probe_red=False`
(`runs/meter-obligation.out:2`). The probe is green and carries no
hole (`runs/recheck-3.out`, `TIME_EXIT=0`). Nine other delivered
names meter `0 UNRESOLVED of 9, 3.89 s, probe_red=False`
(`runs/meter-names.out`). The stated NO-GO is
`agents/tasks/LJ-1-673/review-of-lset-grounded.md`. That file is the
critic's input and it does not close the task.

**THIS IS NOT A REFUTATION OF `LsetGrounded`.** I did not build a
term of its negation. Devlin 5.2 (b) still has the stage reading
(`dev/literature/devlin-II5.md:98-99`).

Written as a skeleton before any Agda beyond the predecessor read
and filled as each answer landed (C-22). No commit, no push. I wrote
only inside `agents/tasks/LJ-1-673/`. Agda ran under the caliber the
program set on this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier,
ONE Agda process at a time. I did not set `GHCRTS`. Nothing is
postulated, every delivered file carries `--safe`, the delivered
probe carries no hole, and nothing lands in `src/`. The probe is a
raw `.agda` file, so it carries no ` ```agda ` fence, counts 0
in-fence lines, and the ratio bar cannot fire on it.

**NO HEAP WALL WAS MET ON THE DELIVERED SHAPE.** The highest peak of
a finished run is 1,684,946,944 bytes against the 2,147,483,648-byte
wide cap (`runs/floor-1.out`), which is 78 percent of it. Two later
wrapper runs ended with `time: signal: Invalid argument`
(`runs/p-2.out:23-24`, `runs/p-final.out:23`). Those are not a
`-M2g` heap wall: no run prints a heap event.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict.

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE
UNLESS THE ROW SAYS OTHERWISE.** This report does not bound a
cold-cache number.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.667]` closed **NO-GO on `witnessed-lset`**
(`agents/tasks/LJ-1-667/lj-1.667-report.md:8-10`). The standing coder
clause says a NO-GO predecessor is a stop. **It is not a stop here.**
The NO-GO is on inhabiting `Witnessed Lset` together with
`LsetGrounded`. The syntax of the witness slot is written and green
(`matrix₃`, `Probe667.agda:72-76`). `LsetGrounded` is a TYPE
(`Probe652.agda:260-264`). The report does not name `LsetGrounded`
FALSE. This task takes that type.

`[LJ-1.670]` closed **GO** on `elem-is-paid`
(`agents/tasks/LJ-1-670/lj-1.670-report.md:8-11`). Elementarity fills.
The report does not name `Elementary` FALSE.

`[LJ-1.652]` closed **NO-GO** on `picommute-D-from-elem` and **GO**
on clause (iii)'s `Commute`. `LsetGrounded` is a TYPE. The report
does not name it FALSE. The consumer `commute-from-witnessed`
(`Probe652.agda:266-268`) is GO.

The types I took are the types the predecessors DELIVERED:

| piece | type | site | verdict |
|---|---|---|---|
| `matrix₃` | 3-slot Δ₀, syntax | `Probe667.agda:72-76` | GO |
| `LsetGrounded` | hull witness for that formula | `Probe652.agda:260-264` | TYPE, green; not inhabited |
| `commute-from-witnessed` | consumer | `Probe652.agda:266-268` | GO |
| `elem-is-paid` | Elementary at this telescope | `Probe670.agda:92-96` | GO |
| `hull-closed` | hull's only closure rule | `src/L/Hull.lagda.md:415` | GO, in `src/` |
| `inF` | pin a Code slot by `≐ con` | `Probe651.agda:149-150` | GO, pattern |

## 2. D-10, BEFORE ANY AGDA

The target `LsetGrounded` at `matrix₃` is true of an elementary hull
of a limit stage that already holds `δ` and `Lset δ`, once the
parameter is an ordinal: Devlin 5.2 (b)
(`dev/literature/devlin-II5.md:98-99`). I did not find a cardinality
or Tarskian obstruction at that generality.

What is at risk is the HYPOTHESIS that the tree can fire
`hull-closed` at `matrix₃` without a completeness fact, and the
HYPOTHESIS that `LsetGrounded`'s type (no `IsOrd`) matches this
matrix. `matrix₃` contains `isOrd-at-p` (`Probe667.agda:72-73`). A
witness `z` with ambient satisfaction of `matrix₃` at `(Lset δ, δ, z)`
needs the parameter to be an ordinal in the object language.
`LsetGrounded` (`Probe652.agda:260-264`) has no `IsOrd`.

The corrected target beside the original, as D-10 asks:
`I.LsetGrounded (WitnessedAt sound)` given `Completeness` and
`Convert` (`Probe673.agda:115-138`), with `IsOrd` on the completeness
supplier. `At.bound-from-stage` (`:100-104`) is the hull-membership
half of that target.

## 3. THE FLOOR, MEASURED BEFORE ANY PROOF

The standing coder clause orders a floor before a heavy object. I ran
it. `runs/FLOOR.agda.txt` is the obligation's whole type, `Probe652`
and `Probe667` imported, and a HOLE where the term goes. It is
`.agda.txt` and not `.agda`, because conjunct 1 runs every `.agda`
under this task home (`agents/tasks/LJ-1-673/LJ-1.673.md:18-19`).

**THE FRAME COSTS 20.20 s AND 1.68 GB, AND IT DOES NOT WALL.**
`runs/floor-1.out`: exit 42 at 20.20 s, peak 1,684,946,944 bytes, one
error and it is the designed hole (`[UnsolvedInteractionMetas]` at
`FLOOR.agda:50`). **The obligation TYPE is well-formed.** Importing
`Probe667` (and through it `Probe652`, `W3`, `Probe520`) is not a
wall.

The import trim is: `src/` plus `Probe652` plus `Probe667`. That is
the trim the floor measured. The delivered probe uses the same
imports plus `FOL.Syntax` constructors for `inBound`.

## 4. W3, THE WIDEST UNMEASURED TERM

The brief names it: getting the bound into the hull without a second
formula. Estimate 80 to 180 lines, basis `[LJ-1.667]` wrote the
syntax and stopped at exactly this
(`agents/tasks/LJ-1-667/lj-1.667-report.md:1`).

**GO ON THE FORMULA CODE 1 AND ON THE CONSUMER. NO-GO ON THE CLOSED
TERM.**

`count-matrix₃ = refl` (`Probe673.agda:54-55`). `matrix₃-Code` is
`mapFo slide matrix₃` (`:76-77`), the dummy-slide of
`Probe651.agda:125-142`. `inBound` (`:83-87`) pins the value slot
and the parameter slot by `≐ con`. That is `[LJ-1.651]`'s `inF` at
three slots, not a new matrix. CloseSyntax.close cannot close at
`Code` (`agents/tasks/LJ-1-664/runs/close-1.out:5-7`).

`bound-from-stage` (`:100-104`) is `hull-closed` at `inBound`. Four
lines. Given `BoundInStage`, a bound is a hull member.

The closed `LsetGrounded` still needs `Completeness` (`:126-130`)
and `Convert` (`:115-119`). Neither is inhabited.

The estimate was 80 to 180 lines. The delivered probe is 144 lines,
71 code. W3 is the Formula Code 1 and the consumer, 21 code lines at
`:54-104`. Completeness is not in that count because it is not
written as a term.

## 5. TWO UNPAID SUPPLIERS

**Supplier 1. `Completeness`.** `BoundInStage` at the codes of
`Lset δ` and `δ`. This is Devlin 5.2 (b) at `matrix₃`. The tree has
`Lset-defines` for `LsetGraphAt` at the class carrier
(`src/L/Condensation.lagda.md:427-430`). It does not have
`SameAsGraph` (`Probe520.agda:192-195`). It does not put the graph
witness in `Lset lam`. The reverse of the three soundness bridges
`[LJ-1.667]` named (`lj-1.667-report.md:136-148`) sits under this
name.

**Supplier 2. `Convert`.** AbsL satisfaction of `inBound` to the
ambient 3-slot reading. The path is unpack of two `∃̇` and two `≐`,
then `Frame652.AtTrans.read` at `Δ₀-matrix₃`
(`Probe652.agda:114-124`), which does not use `elem`. A term that
substituted along the ambient reading of this matrix was started as
`grounded-from-complete`. `runs/p-4.out` still reads Checking and
has no `ended` line. The next run starts at `runs/p-5.out:2`. I
stopped that checker and removed the term in the same dispatch. The
delivered file keeps `Convert` as a type.

Either supplier unpaid is enough. Both are unpaid. The Formula Code 1
is paid. That is the difference from `[LJ-1.664]`: `𝒟ₒ` had no
`Formula Code 1`; the bound has `inBound`.

## 6. W2

**Nothing is proved twice.** `[LJ-1.667]`'s `matrix₃` is imported, not
copied. `inBound` is `[LJ-1.651]`'s `inF` instantiated at three slots.
`bound-from-stage` is one use of `hull-closed`. `WitnessedAt` packs
the predecessor's `matrix₃` and `Δ₀-matrix₃` with the sibling's
soundness. No deadline forced a fixed form. There is no conflict to
report.

## 7. W4, AND P-l

**W4: not applicable.** No module was retired, nothing under `src/`
changed, and `dev/ARCHIVE.md` takes no row from this task. The ideal
form written fresh today is the form delivered: a Formula Code 1 from
the matrix already written, `hull-closed` at that formula, and two
named suppliers.

**P-l: obeyed.** No type in the probe names a stage presentation.
The statements quantify over `S`, `Lset` of a variable, and
`Frame652`'s hull. `⟪ Lset lam ⟫` appears nowhere.

## 8. THE LAWS IN THE BUNDLE

- **D-10** (`dev/LESSONS.md:1375`). Done in section 2. The recorded
  residue is `LsetGrounded` at `matrix₃`. The Formula Code 1 is
  written. Completeness and Convert are not. `Matrix₂` is not funded.
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

| run | what | wall s | peak RSS bytes | exit |
|---|---|---:|---:|---:|
| `runs/floor-1.out` | obligation type, one hole | 20.20 | 1,684,946,944 | 42 |
| `runs/p-1.out` | probe, `LsetGroundedAt` clash | 4.46 | 531,906,560 | 42 |
| `runs/p-2.out` | first inhabited draft, killed | 33.25 | 1,341,603,840 | 1 |
| `runs/p-3.out` | first green of the small draft | 2.89 | 795,246,592 | 0 |
| `runs/p-4.out` | `grounded-from-complete`, stopped | no `ended` | not taken | none |
| `runs/p-5.out` | delivered shape, first green | 127.06 | 1,299,628,032 | 0 |
| `runs/recheck-1.out` | forced recheck | 3.29 | 622,264,320 | 0 |
| `runs/recheck-2.out` | forced recheck | 2.97 | 622,247,936 | 0 |
| `runs/recheck-3.out` | forced recheck | 2.86 | 622,264,320 | 0 |
| `runs/meter-obligation.out` | the obligation | 3.03 | not taken | 1 |
| `runs/meter-names.out` | 9 names, grouped | 3.89 | not taken | 0 |

Median of the three forced rechecks **2.97 s**. Highest peak of any
finished run **1,684,946,944 bytes** (`runs/floor-1.out`), 78 percent
of the 2 GiB cap. No heap event on the delivered shape.

`p-1` is `[ClashingDefinition]` on `LsetGroundedAt` with
`Probe667.agda:154`. The fix is not to reuse that name. `p-2` ended
with `time: command terminated abnormally` (`runs/p-2.out:4`) and
`EXIT=1`. `p-4` is the substitution term I stopped. After a
comment-only edit, `runs/p-final.out` ended the same way as `p-2`.
Those wrapper failures are not a price of the term. The last green
time-wrapper runs of the delivered shape are `p-5` and `recheck-1`
through `recheck-3`.

Witness meter, one obligation: `runs/meter-obligation.out`,
`1 UNRESOLVED of 1`, `probe_red=False`. Witness meter, nine names:
`runs/meter-names.out`, `0 UNRESOLVED of 9`. This worktree has no
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
| the probe, whole | 144 | 71 | `Probe673.agda` |
| `count-matrix₃` | 2 | 2 | `Probe673.agda:54-55` |
| `inBound` and `matrix₃-Code` | 12 | 8 | `Probe673.agda:76-87` |
| `bound-from-stage` | 5 | 5 | `Probe673.agda:100-104` |
| `BoundInStage`, `Completeness`, `Convert` | 20 | 14 | `Probe673.agda:93-130` |
| `WitnessedAt` | 6 | 6 | `Probe673.agda:133-138` |
| floor slice | 50 | 26 | `runs/FLOOR.agda.txt` |

The brief estimated 80 to 180 lines. The probe is 71 code lines.

## 11. WHAT THE SHAPE RESISTED

- **What it cost.** 71 code lines, median 2.97 s on a forced
  recheck, highest peak 1.68 GB against a 2 GB cap, no heap wall on
  the delivered shape.
- **What the shape resisted.** One plumbing error: a name clash with
  `[LJ-1.667]`'s `LsetGroundedAt`. The Formula Code 1 compiled on the
  first attempt that got that name right. Completeness did not
  compile because it was not written. A substitution into the
  ambient reading of `matrix₃` did not return a checker
  (`runs/p-4.out`). I removed that term in the same dispatch.
- **What I had to weaken.** Nothing of the obligation. I did not
  inhabit `LsetGrounded` under extra hypotheses as a closed term. I
  named `Completeness` and `Convert`. I did not inhabit `Matrix₂`.
- **What I could not close.** `lset-grounded`, the hull-membership
  of the bound together with the ambient 3-slot reading, as a closed
  term.

## 12. WHAT THE NEXT BRIEF NEEDS

1. **FUND `Completeness` / `BoundInStage` AT `matrix₃`.** That is
   Devlin 5.2 (b), not a second formula. It needs `SameAsGraph` at
   `[LJ-1.520]`'s Matrix, both directions, and the bound as a member
   of `Lset lam`. Carry `IsOrd` on the parameter. Without it,
   `hull-closed` has nothing to search.
2. **FUND `Convert` AS A GENERIC UNPACK AT A 3-SLOT Δ₀ FORMULA**, not
   as a substitution into this matrix's ambient reading. That
   substitution is the checker `runs/p-4.out` did not finish.
   `AtTrans.read` (`Probe652.agda:114-124`) is the Δ₀ half and does
   not use `elem`.
3. **DO NOT RE-DISPATCH THE FORMULA CODE 1.** `inBound` and
   `count-matrix₃` are green. `bound-from-stage` is green.
4. **DO NOT RE-DISPATCH THE SYNTAX OF THE 3-SLOT MATRIX.** `matrix₃`
   and `Δ₀-matrix₃` are green (`Probe667.agda:72-76`).
5. **DO NOT FUND `Matrix₂`.** D-10 in `[LJ-1.665]`
   (`lj-1.665-report.md:35-39`) still stands.
6. **THIS FRAME RUNS WIDE.** Highest peak 1.68 GB against a 2 GB cap.
   The heavy tier is not needed.
7. This task changed nothing in `src/`.

## 13. GATES

Run individually while the work was live, as the Boundary requires:

- `scripts/gate/lint-agda.py --check`: exit 0, no output.
- `scripts/gate/check-probes.py --check`: `check-probes: clean (10403
  tracked files, no probe outside agents/tasks/ and no generated file)`.
- `scripts/gate/lint-prose.py --check`: exit 0, no output.

I did not run `make check`. I did not commit and I did not push.

**I DID write `review-of-lset-grounded.md`, and that is a decision.**
The standing clause says a `review-of-*.md` is how a coder states a
NO-GO, and a NO-GO means the brief's type was not inhabited. The name
`lset-grounded` is not inhabited. The Formula Code 1 of the bound and
the consumer of `hull-closed` are inhabited, green and metered.

## ARCHIVE USED

- **`archive/dev/DD-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# THE \`DD\` RULING SERIES, archived in full 2026-08-18`.
  W2 is live in the slot file. The archived DD row is not a type.
- **`archive/dev/ORCHESTRATION.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# ORCHESTRATION: the orchestrator's operating rules`.
  It is the archived process document. This task writes a Formula Code 1
  from live probes and does not consult dispatch process.
- **`archive/dev/PLAN-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# ARCHIVED 2026-08-20`. A history. The live status is
  `dev/pod/screen.toml`.
- **`archive/dev/STATUS-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# STATUS-archived: the goal table of the internalization route`.
  The internalization route is not this matrix.
- **`archive/dev/TASKS-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# Archived task index: the \`L3.32-T\` series`. That
  series is not a predecessor of `LsetGrounded`.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md` READ.**
  `dev/literature/level-formula-slot-roles.md:26` reads
  `| 4 | Devlin 5.2 (a) | \`Φ(z,v,γ)\` with \`∀v∀γ [v = L_γ ↔ ∃z Φ(z,v,γ)]\` | 3 in \`Φ\`, ONE closed | \`z\` at position 0 | \`v\` at 1, \`γ\` at 2 | **VALUE, ORDINAL** | \`_build/literature/dev2.txt:1186-1191\` |`.
  **This is the witness slot.** Three slots in Φ, one closed. The
  consumer's order is value then parameter then witness
  (`Probe652.agda:91`). `inBound` keeps that order and pins the first
  two slots.
  `dev/literature/level-formula-slot-roles.md:27` reads
  `| 5 | Devlin 5.2 (b) | \`(∀γ<α)(∀v)[v = L_γ ↔ v ∈ L_α ∧ L_α ⊨ ∃z φ(z,v,γ)]\` | same | \`z\` | \`v\`, \`γ\` | **VALUE, ORDINAL** | \`_build/literature/dev2.txt:1193-1198\` |`.
  **This is `BoundInStage`.** The stage satisfies the existential.
  `hull-closed` searches that existential.
- **`dev/literature/glossary-review-2026-08.md` DECLINED.** Not read
  beyond its first line. `:1` reads `# Glossary review: the 119 pre-protocol entries`.
  No naming question arose and this task proposes no `dev/glossary.toml`
  entry.
- **`dev/literature/devlin-errata.md` DECLINED.** Not read beyond its
  first line. `:1` reads `# Devlin errata: documented error classes (do-not-repeat checklist)`.
  This task certifies no leaf as bounded and quotes no Δ₀ certificate
  from a scanned page, so the errata have nothing to bite.
- **`dev/literature/primary-sources.md` DECLINED.** Not read beyond its
  first line. `:1` reads `# Primary sources, second round: Jensen manuscript, Devlin, Jech`.
  The slot arithmetic is in `level-formula-slot-roles.md` and the Σ₀
  shape is in `devlin-II5.md` (standing). A second round of source notes
  does not change a type.
- **`dev/literature/BIBLIOGRAPHY.md` DECLINED.** Not read beyond its
  first line. `:1` reads `# Bibliography for the rud route`. No citation
  was added and no source was missing.

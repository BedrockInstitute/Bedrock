# LJ-1.676 report: the kernel satisfaction, once, at generic n

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.676
obligation: agents/tasks/LJ-1-676/Probe676.agda::kernel-sat
verdict: **GO. `kernel-sat` is the class-carrier Σ₁ transfer of the
chapter's `LevelHood {n}` matrix at GENERIC `n`, arity `4 + n`, with
`K` free. It is `[LJ-1.669]`'s `transfer-at-arity4` instantiated at
the chapter's own generic arity. The delivered `σ₁-up` is already
generic. This file does not rewrite it. None of the three consumer
views is built.**

The obligation is green and metered (`runs/meter-obligation.out`,
`pass exit=0 3.00 s`, `0 UNRESOLVED of 1`, `probe_red=False`). The delivered
probe is green (`runs/p-1.out`, EXIT=0, 4.13 s).

**READ THESE FIVE SENTENCES BEFORE YOU QUEUE ANYTHING.**

1. **THE TERM IS THE TRANSFER, NOT THE ADEQUACY.** `kernel-sat`
   (`Probe676.agda:120`, body at `:97-101`) takes an inner reading of
   the sealed matrix and sends it to the ambient class carrier, at
   arity `4 + n`, `K` still free. It does not prove `v ≡ Lset γ → ⟨δ ⊨
   matrix⟩`. That adequacy still needs a `graphBndAt` ↔ `LsetGraphAt`
   bridge, which `src/` does not contain
   (`agents/tasks/LJ-1-662/review-of-hoodexists.md:39-43`).
2. **W2 IS THE DELIVERED `σ₁-up`, NOT A NEW LEMMA.**
   `src/FOL/Absoluteness.lagda.md:182-184` already quantifies over `n`.
   The chapter already writes `LevelHood {n}` at arity `4 + n`
   (`src/L/BoundedSubset.lagda.md:74`, `:108`). The probe instantiates
   both. The brief's 200-to-400-line estimate was for a generalisation
   of `[LJ-1.669]`. The generalisation is five lines plus the
   telescope (`Probe676.agda:97-101`). A deadline does not force a
   fixed-`n` copy.
3. **THE THREE CONSUMER VIEWS ARE NOT IN THIS FILE.** The brief
   forbids them. The maps that build them are already green:
   `[LJ-1.651]` `twoSlot` / `lset-formula` (`Probe651.agda:100-142`)
   and `[LJ-1.662]` `hood2` / `φ₀` (`Probe662.agda:88-123`). This
   transfer plus those maps is the sharing `[LJ-1.675]` funded. The
   maps still need an inner reading to transport.
4. **THE `KFacts` WALL AT `n = 0` DOES NOT TOUCH THIS TERM.** It is a
   proof constraint on adequacy through `LeafAgree`
   (`lj-1.675-report.md:250-253`). Slot arithmetic for that route is
   recorded, not ridden: usable numeral columns in the outer
   environment, without clobbering `v`, `γ`, `K`, are `1 + n`
   (`Probe676.agda:147-154`). Twelve numerals need `n ≥ 11`.
   `[LJ-1.666]` counted `n ≥ 14` for `Fin (5 + n)` addressing
   (`review-of-sat-at-level.md:117-119`). Both counts leave `n = 0`
   short.
5. **NO PREDECESSOR NO-GO TYPE IS INHABITED.** `[LJ-1.669]` is NO-GO
   on `sound-at-arity4` and GO on `transfer-at-arity4`. This file
   takes the green type and generalises it. `[LJ-1.666]`'s
   `sat-at-level` and `[LJ-1.661]`'s `hoodsound-at-levelhood0` stay
   uninhabited.

Written as a skeleton before any Agda beyond the floor and filled as each
answer landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-676/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier, ONE Agda process at a time.
I did not set `GHCRTS`. Nothing is postulated, the delivered probe carries
`--safe` and no hole, and nothing lands in `src/`. The probe is a raw `.agda`
file, so it carries no ` ```agda ` fence, counts 0 in-fence lines, and the
ratio bar cannot fire on it.

The standing direction (`dev/pod/direction.md:37`) says one SRC collection
after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1 work. It does not
start that collection and it does not start phase 3. No Boundary clause is
in conflict. W4 does not apply: no module is retired.

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE**
(710 `.agdai` files under `_build/` at the start of the delivered run). No
number here is a cold-cache number, and this report does not bound one.

**NO HEAP WALL WAS MET ANYWHERE IN THIS TASK.** The highest peak of any run
is 692,305,920 bytes against the 2,147,483,648-byte wide cap
(`runs/floor-1.out`), which is 32 percent of it. The longest Agda run is
4.13 s (`runs/p-1.out`) against the 600 s cap. The caps are wall-clock caps
enforced by a perl alarm (`runs/run.sh`).

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

The standing coder clause says: take the type from the probe that
typechecked, and the verdict from the report. If the report is NO-GO, do
not inhabit that type.

| task | verdict | type taken | site |
|---|---|---|---|
| `[LJ-1.669]` | NO-GO on `sound-at-arity4`; GO on `transfer-at-arity4` | class-carrier Σ₁ transfer, arity 4, K free | `Probe669.agda:117-121` |
| `[LJ-1.675]` | GO on `residue-arity` | three consumer types, one kernel at generic `n` | `lj-1.675-report.md:9-12` |
| `[LJ-1.666]` | NO-GO on `sat-at-level` | do not inhabit | `Probe666.agda:87-88` |
| `[LJ-1.661]` | NO-GO on `hoodsound-at-levelhood0` | do not inhabit | `Probe661.agda:105-107` |
| `[LJ-1.662]` | STOP on `hoodexists-at-levelhood0` | `KFacts` slot count is a proof constraint | `lj-1.662-report.md:46-49` |
| `[LJ-1.651]` | GO on `lset-formula` | closure map, already green, not rebuilt | `Probe651.agda:100-142` |

None of those reports names the residue FALSE. Each NO-GO or STOP is on
inhabiting a satisfaction at a consumer, or a HoodSound-shaped lemma.
This task inhabits the green transfer, at the kernel's own generic arity.

## 2. W3, THE WIDEST UNMEASURED TERM

The brief names it: the satisfaction at generic `n` with `K` free.
Estimate 200 to 400 lines, basis `[LJ-1.669]` delivered
`transfer-at-arity4` at one fixed arity (`Probe669.agda:117`).

**GO. THE GENERIC FORM WAS ALREADY IN THE TREE.** `σ₁-up` is
`∀ {n} {φ : Formula SM n} → Σ₁ φ → ...`
(`src/FOL/Absoluteness.lagda.md:182-183`). `levelHoodB` is
`Formula CS.S (suc (suc (suc (suc n))))`
(`src/L/BoundedSubset.lagda.md:108`). `4 + n` is definitionally that
arity. The probe seals the matrix (`Probe676.agda:70-86`) and
instantiates (`:97-101`).

The estimate is void for a rewritten lemma: there is none. The
delivered probe is 157 lines, 52 code. The new mathematics is the
telescope at generic `n` and the slot-arithmetic record. The transfer
is the same five-line ascription `[LJ-1.669]` wrote at `n = 0`.

**WHAT THIS TERM IS NOT.** It is not
`v ≡ Lset γ → ⟨ δ ⊨ levelHoodB ⟩`. `[LJ-1.666]` recorded that the
bounded matrix is true at the stage and that the tree cannot close
the proof through `KFacts` at arity 2
(`lj-1.666-report.md:38-41`). This dispatch does not close that
proof at generic `n` either. The missing composition is
`graphBndAt` ↔ `LsetGraphAt`. Six lines in `src/` mention
`graphBndAt`. None of them is that bridge
(`review-of-hoodexists.md:39-43`). Building it is a new module.
The 200-to-400-line estimate would attach to that module, not to
this instantiation.

## 3. THE FLOOR, MEASURED BEFORE ANY PROOF

Coder clause, owner 2026-08-23: price the frame before the term. The
floor is `LevelHood {n}`, the sealed matrix, and a hole where
`kernel-sat` stands. It is `.agda.txt` and not `.agda`, because every
`.agda` under a task home is a verification target.

The first floor run did not reach the hole. `Pin {n} N0 ... .matrix`
is not legal module-application syntax in a type
(`runs/floor-1.out`, `[NotInScope]` `Pin` at `FLOOR.agda:57`). The
`Pin` body itself elaborated: the error is only at the outer
ascription. Peak 692,305,920 bytes, 3.17 s, EXIT=42.

The repair is the lift `[LJ-1.651]` already measured
(`Probe651.agda:152-156`): name the term inside the parameterised
module, then `kernel-sat = Pin.kernel-sat-at` (`Probe676.agda:120`).
That is a new shape, not a rerun of the floor file.

| run | file | exit | wall s | peak bytes |
|---|---|---:|---:|---:|
| `floor-1` | `runs/FLOOR.agda.txt` as `.agda`, then removed | 42 | 3.17 | 692,305,920 |
| `p-1` | delivered probe | 0 | 4.13 | 567,508,992 |
| meter | `witness.py --brief` | 0 | 3.00 | (meter does not print RSS) |

The frame is 0.69 GB and the task ceiling is 2 GB. No import trim
beyond `src/` was required. Predecessor probes were not imported: the
types they delivered are restated, each cited at the line they were
read.

P-l is observed: no type in this file names `LevelHood.levelHoodB`
outside the opaque block. The kernel in the satisfaction type is the
sealed `matrix` (`Probe676.agda:71-72`).

## 4. D-10 ON THE RESIDUE

The recorded residue is "the level-hood instantiation at the hull"
(`src/L/BoundedSubset.lagda.md:901`). `[LJ-1.675]` corrected the
*funding* target to one kernel satisfaction at generic `n`, or one
packed satisfaction at generic alphabet
(`lj-1.675-report.md:215-218`).

This dispatch prices the kernel's *transfer* at generic `n`. That
target is true: `σ₁-up` inhabits it. The adequacy target
`v ≡ Lset γ → ⟨δ ⊨ matrix⟩` is not shown false. It is not inhabited.
The corrected remaining target beside this GO is: one bounded-graph
agreement `graphBndAt` ↔ `LsetGraphAt` at generic `n ≥ 11`, with
`KFacts` in the extra slots, or one packed satisfaction at generic
alphabet that does not go through that agreement.

C-42 does not fire. This is not a refutation of a site. No false
shape was counted.

## 5. W2 ANSWER

W2: write the mathematics once at a generic carrier and instantiate it.

The chapter already does that for the kernel: `LevelHood {n}`
(`src/L/BoundedSubset.lagda.md:74`) has matrix arity `4 + n` (`:108`).
`LevelHood0` is the instance `n = 0` (`:840-849`).

The transfer already does that: `σ₁-up` quantifies over `n`
(`src/FOL/Absoluteness.lagda.md:182`). This probe instantiates it at
`levelHoodB`. Instantiation at `n = 0` recovers `[LJ-1.669]`'s
`transfer-at-arity4`. Instantiation at `n ≥ 11` is the same term, with
room for twelve numeral columns in the outer environment.

A deadline does not apply. There is no conflict with a fixed form. Do
not fund a second copy at `n = 0`. Do not fund the three consumer
views as a second kernel.

## 6. WHAT THE NEXT BRIEF NEEDS

- **If the consumer reads at `L`.** `kernel-sat` is delivered at
  generic `n`, arity `4 + n`, `K` free, no `mapΔ₀`
  (`Probe676.agda:97-101`, lifted at `:120`). The reverse at the same
  carrier is `Pin.reverse-at`, and it is Π₁ (`:108-112`).
- **If the consumer is adequacy, `v ≡ Lset γ → ⟨δ ⊨ matrix⟩`.** This
  file does not close it. The tree has `Lset-defines` for the
  unbounded graph (`src/L/Hierarchy.lagda.md:646-648`) and `LeafAgree`
  for `DefBodyB` ↔ `DefBody` (`src/L/Condensation.lagda.md:7224`). It
  has no theorem that relates `graphBndAt` to `LsetGraphAt`. That
  composition is a new module. Price it as such. Do not re-fund the
  transfer.
- **If that module is queued, the slot count is `n ≥ 11` for twelve
  numerals in the outer environment**, unused `u` plus `n` extras,
  without clobbering `v`, `γ`, `K` (`Probe676.agda:147-154`). Closing
  the surplus by `∃̇` to arity 2 loses the tag equations
  (`review-of-sat-at-level.md:117-121`). The kernel must stay at
  arity `4 + n`.
- **Do not queue a third satisfaction of this residue at a new
  arity.** `[LJ-1.675]` already compared the three consumers. The
  arities are 4 (kernel, now generic `4 + n`) and 2 (consumer).
- **The 651 and 662 maps remain the views.** Do not rebuild them.

## 7. PRICE

| item | measured |
|---|---|
| floor (imports + seal; syntax error at outer ascription) | 3.17 s, 692,305,920 bytes, EXIT=42 |
| delivered probe | 4.13 s, 567,508,992 bytes, EXIT=0 |
| witness meter | 3.00 s, 0 UNRESOLVED of 1, `probe_red=False` |
| file lines / code lines | 157 / 52 |
| brief estimate | 200 to 400 lines |
| in-fence lines | 0 (raw `.agda`) |
| caliber | `-A64m -I0 -M2g`, never set here |
| heap wall | none |
| `src/` edits | none |

The estimate was high because the generic form was already in
`σ₁-up`. The probe is the instantiation plus the slot-arithmetic
record. Nothing of 200 to 400 lines was needed for the transfer, and
nothing of that length was written.

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md:1` `# ORCHESTRATION: the orchestrator's operating rules`. Declined: not used. This dispatch instantiates a live transfer, not archived dispatch rules.
- `archive/dev/DD-archived.md:1` `# THE `DD` RULING SERIES, archived in full 2026-08-18`. Declined: not used. The live W2 home is the coder slot file, not this archive.
- `archive/dev/PLAN-archived.md:1` `# ARCHIVED 2026-08-20`. Declined: not used.
- `archive/dev/STATUS-archived.md:1` `# STATUS-archived: the goal table of the internalization route`. Declined: not used.
- `archive/dev/TASKS-archived.md:1` `# Archived task index: the `L3.32-T` series`. Declined: not used.

## LITERATURE USED

- `dev/literature/level-formula-slot-roles.md:35` `### 2.1 The free pair is the VALUE and the ORDINAL, in every source`. Read. The literature consumer is arity 2. This kernel leaves `K` free at arity `4 + n`. That is the split `[LJ-1.675]` measured.
- `dev/literature/level-formula-slot-roles.md:37` `Rows 3, 4, 5, 6, 8 and 9 agree. **A level-hood formula leaves exactly the two`. Read. Confirms that leaving `K` free is the kernel, not the literature consumer. The 651/662 maps close that slot.
- `dev/literature/devlin-errata.md:1` `# Devlin errata: documented error classes (do-not-repeat checklist)`. Declined: not used. The term is a live `σ₁-up` instantiation, not a Devlin erratum.
- `dev/literature/glossary-review-2026-08.md:1` `# Glossary review: the 119 pre-protocol entries`. Declined: not used.
- `dev/literature/primary-sources.md:1` `# Primary sources, second round: Jensen manuscript, Devlin, Jech`. Declined: not used. Slot roles already cite those sources.
- `dev/literature/BIBLIOGRAPHY.md:1` `# Bibliography for the rud route`. Declined: not used.

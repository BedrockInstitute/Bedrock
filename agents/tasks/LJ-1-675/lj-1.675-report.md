# LJ-1.675 report: which arity the chapter's residue actually has to serve

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.675
obligation: agents/tasks/LJ-1-675/Probe675.agda::residue-arity
verdict: **GO. The three consumer types are THREE. They share ONE kernel.
One lemma typed at a consumer does not serve the other two. One kernel
satisfaction, plus the closure maps `[LJ-1.651]` and `[LJ-1.662]` already
wrote, serves all three as views.**

The obligation is green and metered (`runs/meter-obligation.out`,
`pass exit=0 2.59 s`, `0 UNRESOLVED of 1`, `probe_red=False`). The delivered
probe is green (`runs/p-final.out`, EXIT=0, 2.71 s).

**READ THESE FIVE SENTENCES BEFORE YOU QUEUE ANYTHING.**

1. **THEY ARE THREE TYPES, NOT THREE KERNELS.** `c661` is arity 4, K free,
   class carrier, env `u ∷ v ∷ γ ∷ K` (`Probe675.agda:134-135`). `c663` is
   arity 2, K closed, hull `Code`, env `γ ∷ v` (`:138-139`). `c666` is
   arity 2, K closed, erased `⊥*`, env `v ∷ γ` (`:142-143`). Pairwise
   inequality is inhabited: `c661≢c663`, `c663≢c666`, `c661≢c666`
   (`:153-163`). `same-type-false` (`:180-181`) is the one-lemma-at-the-
   same-type answer: NO.
2. **THEY ARE ONE KERNEL.** `kernel-views` (`:201-202`) records that 661
   keeps K free at arity 4 and that 663 and 666 close K at arity 2. The
   maps that build those views are already green: `[LJ-1.651]`
   `twoSlot` / `lset-formula` (`Probe651.agda:100-142`) and `[LJ-1.662]`
   `hood2` / `φ₀` (`Probe662.agda:88-123`). This file does not rebuild
   them (P-l; the brief forbids a satisfaction lemma).
3. **DO NOT FUND THREE SATISFACTION LEMMAS.** `[LJ-1.665]` warned that
   funding two residues as two objects "funds the same formula twice"
   (`lj-1.665-report.md:24-25`). Fund the kernel once at generic `n`
   (the chapter already writes `LevelHood {n}`,
   `src/L/BoundedSubset.lagda.md:74-108`, arity `4 + n`). The two arity-2
   consumers are instantiations after closure and alphabet change. W2
   is that sharing, and this survey does not conflict with it.
4. **THE CHAPTER'S OWN CONSUMER IS ARITY 2 AT THE HULL.** The priced
   residue (`src/L/BoundedSubset.lagda.md:901`) is "the level-hood
   instantiation at the hull". That is `[LJ-1.663]`'s `SatAtPacked` shape
   (and `[LJ-1.650]`'s `LevelFormula`), not the open matrix. D-10: the
   arity-4 object is the KERNEL the consumer closes. It is not the
   consumer.
5. **THE `KFacts` SLOT COUNT IS A PROOF CONSTRAINT, NOT A FOURTH ARITY.**
   `[LJ-1.662]` measured that twelve numeral columns cannot come from
   five committed slots (`lj-1.662-report.md:46-49`). `[LJ-1.666]` restated
   that as a wall on `sat-at-level`. Take both as given. They constrain
   HOW a kernel satisfaction is proved. They do not add a consumer
   arity.

Written as a skeleton before any Agda beyond the floor and filled as each
answer landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-675/`. Agda ran under the caliber the program set on this
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
is 738,918,400 bytes against the 2,147,483,648-byte wide cap
(`runs/floor-1.out`), which is 34 percent of it. The longest Agda run is
2.86 s (`runs/p-2.out`) against the 600 s cap. The caps are wall-clock caps
enforced by a perl alarm (`runs/run.sh`).

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

The standing coder clause says: take the type from the probe that
typechecked, and the verdict from the report. If the report is NO-GO, do
not inhabit that type.

| task | verdict | type taken | site |
|---|---|---|---|
| `[LJ-1.661]` | NO-GO on `hoodsound-at-levelhood0` | arity-4 Δ₀ matrix, env `u ∷ v ∷ γ ∷ K` | `Probe661.agda:105-107` |
| `[LJ-1.662]` | STOP on `hoodexists-at-levelhood0` | `SatAtLevel : Formula ⊥* 2 → Type` | `Probe662.agda:284-287` |
| `[LJ-1.663]` | STOP on `level-laws` | `SatAtPacked : Formula Code 2 → Type` | `Probe663.agda:135-138` |
| `[LJ-1.665]` | GO on `certificate-remainder` | frames meet in one `HullStage` telescope | `Probe665.agda:229-242` |
| `[LJ-1.666]` | NO-GO on `sat-at-level` | arity 2, avoid `KFacts` | `Probe666.agda:87-88` |

None of those reports names the residue FALSE. Each NO-GO or STOP is on
inhabiting a satisfaction. This task inhabits none of those obligations.
It restates the demand types (`Probe675.agda:82-103`) and compares them.

`[LJ-1.662]`'s hard constraint is taken as given (brief premise 4): twelve
numeral columns cannot come from five committed slots, so `LevelHood0`
cannot carry the `KFacts` the leaf agreement needs.

## 2. W3, THE WIDEST UNMEASURED TERM

The brief names it: whether the arity-2 and arity-4 demands have a common
generalisation at this frame. Estimate 80 to 170 lines, basis `[LJ-1.665]`
compared three clause frames in one module.

**GO. THE TYPES LIVE IN ONE `HullStage` TELESCOPE.** `Frame`
(`Probe675.agda:68-103`) restates, together:

- `Kernel = Formula CS.S 4` (`:82-83`), the 661 demand.
- `SatAtPacked` (`:89-93`), the 663 demand, env `γ ∷ v`, alphabet `Code`.
  The packed value is quantified, not constructed: this survey builds no
  packed term.
- `SatAtLevel` (`:99-103`), the 666 demand, env `v ∷ γ`, alphabet `⊥*`
  then `embed`.

The floor that priced that telescope is `runs/FLOOR.agda.txt` /
`runs/floor-1.out`: EXIT=42 at 2.70 s, peak 738,918,400 bytes, one error
and it is the designed hole (`[UnsolvedInteractionMetas]` at
`FLOOR.agda:53.17-21`). No predecessor probe is imported. The trim is
`src/` only, `HullStage` and `CS` from the chapter.

The estimate was 80 to 170 lines. The delivered probe is 230 lines, 105
code. The estimate is right about the code. The new mathematics is the
discrete comparison (`Consumer`, the three records, the inequalities,
`same-type-false`, `kernel-views`). The three demand types are restatements.

**THE INCOMPATIBILITY IS NOT THE FRAME. IT IS THE TYPES.** That is the
same split `[LJ-1.665]` measured for the certificate clauses
(`lj-1.665-report.md:109-110`). A term of `SatAtPacked` does not have type
`SatAtLevel`: the formula alphabets differ (`Code` versus `⊥*`) and the
slot orders differ (`γ ∷ v` versus `v ∷ γ`). A term of `Kernel` does not
have type `SatAtPacked`: the arities differ (4 versus 2).

## 3. THE FLOOR, MEASURED BEFORE ANY PROOF

Coder clause, owner 2026-08-23: price the frame before the term. The floor
is the three demand types, the `HullStage` import, and a hole where
`residue-arity` stands. It is `.agda.txt` and not `.agda`, because every
`.agda` under a task home is a verification target.

| run | file | exit | wall s | peak bytes |
|---|---|---:|---:|---:|
| `floor-1` | `runs/FLOOR.agda.txt` as `.agda` | 42 | 2.70 | 738,918,400 |
| `p-1` | first probe, ambiguous `⊥` | 42 | 2.55 | 563,527,680 |
| `p-2` | `Empty.⊥` | 0 | 2.86 | 610,582,528 |
| `p-final` | delivered | 0 | 2.71 | 610,582,528 |
| meter | `witness.py --brief` | 0 | 2.59 | (meter does not print RSS) |

The frame is 0.69 GB and the task ceiling is 2 GB. No import trim beyond
`src/` was required. Predecessor probes were not imported: the types they
delivered are restated, each cited at the line they were read.

`p-1` failed at `Probe675.agda:145` (`[AmbiguousName]` `⊥`:
`Cubical.Data.Empty.⊥` against `TruthAlgebra.⊥`). The repair is a
qualified `Empty.⊥`. That is a name clash, not a mathematical wall. The
same code was not rerun: the type of every inequality changed.

P-l is observed: no type in this file names `LevelHood0.matrix`. `[LJ-1.662]`
measured that naming the transparent matrix in a downstream type unfolds
`GraphB` and exhausts the wide cap (`Probe662.agda:101-108`). The kernel
here is the arity-4 *type* `Formula CS.S 4`.

## 4. THE THREE CONSUMERS, AND THE ONE-LEMMA ANSWER

`residue-arity` (`Probe675.agda:212-230`) packs:

| conjunct | meaning | evidence |
|---|---|---|
| `c661`, `c663`, `c666` | each consumer as arity, K-freedom, slot order, alphabet | `:134-143` |
| `arity-of c661 ≡ 4` | 661 demand | chapter `matrix : Formula CS.S 4` at `:848-849` |
| `arity-of c663 ≡ 2` | 663 demand | `SatAtPacked` at `Probe663.agda:135-138` |
| `arity-of c666 ≡ 2` | 666 demand | `SatAtLevel` at `Probe662.agda:284-287` |
| `c661 ≡ c663 → ⊥` | different arity | `c661≢c663` |
| `c663 ≡ c666 → ⊥` | different slot order | `c663≢c666` (`γ ∷ v` versus `v ∷ γ`) |
| alphabet 663 ≢ 666 | `Code` versus `⊥*` | `c663≢c666-alphabet` |
| `c661 ≡ c666 → ⊥` | different arity | `c661≢c666` |
| `SameType → ⊥` | one lemma at one consumer type cannot serve all | `same-type-false` |
| `KernelViews` | 661 is the open kernel; 663 and 666 are its closed views | `kernel-views` |

**One lemma at a consumer type: NO.** `SameType` asks `c661 ≡ c663` and
`c663 ≡ c666`. `same-type-false` reduces the first conjunct to `4 ≡ 2`.

**One kernel, two closed views: YES.** `KernelViews` records K free at 661
and K closed at 663 and 666, with arities 4, 2, 2. W2: write the kernel
satisfaction once at `LevelHood {n}` and instantiate. The two closed views
are not a second kernel. They are also not the same formula:

- `[LJ-1.651]` closes unused `u` by unbounded `∃̇`, rotates, closes K by
  unbounded `∃̇`, swaps to `γ ∷ v`, then `mapFo` to `Code`
  (`Probe651.agda:80-142`).
- `[LJ-1.662]` renames by `ρ`, closes K by unbounded `∃̇`, closes unused
  `u` by bounded `∃̇∈ K`, then erases to `⊥*` (`Probe662.agda:88-123`).

Those two maps are different syntax. They share the kernel and they share
arity 2. A packed-satisfaction lemma written at a generic alphabet, with
slot order as a parameter, instantiates to both. That is W2 at the closed
side. It is not a third fundable kernel.

The literature table agrees with the closed consumer, not with the open
kernel. `dev/literature/level-formula-slot-roles.md:35` names the free
pair as the VALUE and the ORDINAL. Line 37: a level-hood formula leaves
exactly the two slots its conclusion uses. No source leaves a bound free.
The chapter's matrix leaves K free (`src/L/BoundedSubset.lagda.md:68-72`).
That is the kernel. The consumer closes it.

## 5. D-10 ON THE RESIDUE

The recorded residue is "the level-hood instantiation at the hull"
(`src/L/BoundedSubset.lagda.md:901`). The intended consumer of that
residue is the hull reading: arity 2, alphabet `Code`, packed pair
`(γ, Lset γ)`. That is `SatAtPacked` / `LevelFormula`. It is not the
arity-4 open matrix.

This survey does not show that target false. `[LJ-1.666]` already recorded
that the bounded matrix is satisfied at the stage and that the tree cannot
close the proof through `KFacts` (`lj-1.666-report.md:38-41`). The
corrected *funding* target beside the original is: one kernel satisfaction
at generic `n`, or one packed satisfaction at generic alphabet. Not three
consumer-level lemmas.

C-42 does not fire. This is not a refutation of a site. No false shape was
counted. The consumer count this survey compared is three, named above.

## 6. W2 ANSWER

W2: write the mathematics once at a generic carrier and instantiate it.

The chapter already does that for the kernel: `LevelHood {n}`
(`src/L/BoundedSubset.lagda.md:74`) has matrix arity `4 + n` (`:108`).
`LevelHood0` is the instance `n = 0` (`:840-849`).

The two arity-2 demands are instances after closure:

- generic alphabet `K`, formula of arity 2, packed pair, slot order as a
  parameter, then instantiate `K = Code` with `γ ∷ v` (663) and
  `K = ⊥*` with `v ∷ γ` plus `embed` (666).

A deadline does not apply. There is no conflict with a fixed form. Do not
fund the closed views as if they were a second kernel. Do not fund 661's
open matrix as if it were the hull consumer.

## 7. WHAT THE NEXT BRIEF NEEDS

- **Do not queue a third satisfaction of this residue at a new arity.**
  The arities are 4 (kernel) and 2 (consumer). There is no third.
- **If the next payment is a satisfaction, pick one of two objects, not
  three.** (A) kernel satisfaction of `levelHoodB` at generic `n`. (B)
  packed satisfaction at generic alphabet, slot order a parameter. (A)
  plus the 651/662 maps gives (B). (B) does not give (A): closing K
  loses the free bound.
- **The `KFacts` wall still sits on (A) at `n = 0`.** Premise 4 of this
  brief, measured by `[LJ-1.662]`. A proof of (A) that goes through
  `LeafAgree` needs a route that does not ask `LevelHood0`'s five slots
  to carry twelve numeral columns. This survey does not price that route.
- **663 and 666 share the closed shape and differ on alphabet and slot
  order.** Funding both as separate lemmas funds the same packed
  satisfaction twice (`lj-1.665-report.md:24-25`).
- **Nothing in this file is a satisfaction.** The brief forbade one. The
  obligation is the comparison. It is green.

## 8. PRICE

| item | measured |
|---|---|
| floor (imports + hole) | 2.70 s, 738,918,400 bytes, EXIT=42 by design |
| delivered probe | 2.71 s, 610,582,528 bytes, EXIT=0 |
| witness meter | 2.59 s, 0 UNRESOLVED of 1, `probe_red=False` |
| file lines / code lines | 230 / 105 |
| brief estimate | 80 to 170 lines |
| in-fence lines | 0 (raw `.agda`) |
| caliber | `-A64m -I0 -M2g`, never set here |
| heap wall | none |
| `src/` edits | none |

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md:1` `# ORCHESTRATION: the orchestrator's operating rules`. Declined: not used. This survey compares live task types, not archived dispatch rules.
- `archive/dev/DD-archived.md:1` `# THE `DD` RULING SERIES, archived in full 2026-08-18`. Declined: not used. The live W2 home is the coder slot file, not this archive.
- `archive/dev/PLAN-archived.md:1` `# ARCHIVED 2026-08-20`. Declined: not used.
- `archive/dev/STATUS-archived.md:1` `# STATUS-archived: the goal table of the internalization route`. Declined: not used.
- `archive/dev/TASKS-archived.md:1` `# Archived task index: the `L3.32-T` series`. Declined: not used.

## LITERATURE USED

- `dev/literature/level-formula-slot-roles.md:35` `### 2.1 The free pair is the VALUE and the ORDINAL, in every source`. Read. This is the closed consumer the hull residue has to serve.
- `dev/literature/level-formula-slot-roles.md:37` `Rows 3, 4, 5, 6, 8 and 9 agree. **A level-hood formula leaves exactly the two`. Read. Confirms that leaving K free is the kernel, not the literature consumer.
- `dev/literature/devlin-errata.md:1` `# Devlin errata: documented error classes (do-not-repeat checklist)`. Declined: not used. The survey is about Bedrock arities, not Devlin errata.
- `dev/literature/glossary-review-2026-08.md:1` `# Glossary review: the 119 pre-protocol entries`. Declined: not used.
- `dev/literature/primary-sources.md:1` `# Primary sources, second round: Jensen manuscript, Devlin, Jech`. Declined: not used. Slot roles already cite those sources.
- `dev/literature/BIBLIOGRAPHY.md:1` `# Bibliography for the rud route`. Declined: not used.

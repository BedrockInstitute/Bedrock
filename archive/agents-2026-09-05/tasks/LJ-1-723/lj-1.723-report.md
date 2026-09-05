# LJ-1.723 report: 713's chain, transcribed under its true name

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.723
obligation: agents/tasks/LJ-1-723/Probe723.agda::below-closed-via
verdict: **GO. The obligation name is now in the live tree and the
witness meter closes it.** `below-closed-via` is declared at
`Probe723.agda`'s top level, the transcription of `[LJ-1.713]`'s
frame member (`Probe713.agda:120-130`, worktree LJ-1-713), with
`CompletenessFrom` taken as the hypothesis it is and never applied.
First run EXIT 0 cold cone, 344.24 s, peak 1,609,367,552 B, 75
percent of the wide cap, no heap wall (`runs/p-1.out`); recheck EXIT
0 at 3.28 s warm (`runs/p-2.out`); witness `pass`, 0 UNRESOLVED of 1
(`runs/witness-1.out`).

Written as a skeleton before any Agda run and filled after each
answer landed (C-22; the file mtimes carry the order: probe
12:17:23, skeleton 12:17:35, first run output 12:23:24). No commit,
no push. I wrote only inside `agents/tasks/LJ-1-723/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0
-M2g"`, the WIDE tier, ONE Agda process at a time; I did not set
`GHCRTS`. Nothing is postulated, the delivered probe carries
`--safe` and no hole, and nothing lands in `src/`. The probe is a
raw `.agda` file, so it carries no fence and counts 0 in-fence
lines; the ratio bar cannot fire on it.

**NO HEAP WALL WAS MET IN THIS TASK.** Peak 1,609,367,552 B against
the 2,147,483,648-byte wide cap, 75 percent of it (`runs/p-1.out`).

The standing direction (`dev/pod/direction.md`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase
3. No Boundary clause is in conflict.

## 0. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

The standing coder clause: take the type from the probe that
typechecked, and the verdict from the report. One predecessor on
this chain returned NO-GO, and it is the one premise 4 leans on.

| piece | type | site | verdict |
|---|---|---|---|
| `below-from-place` | placement + identification to `Below` | `Probe706.agda:78` | GO. Imported, not rebuilt. |
| `Bound-in-tower` | the placement row | `Probe706.agda:65-66` | TYPE, green. Not inhabited. Hypothesis 2 of the rows. `[LJ-1.711]` is dispatched on it. |
| `Identified` | the carve equals the table | `Probe706.agda:59-60` | TYPE, green. Not inhabited. Hypothesis 3 of the rows. `[LJ-1.712]` re-aims it at the re-bounded carve. |
| `from-below` | `Below`-all to `HierInStage` | `Probe697.agda:81` | GO. Imported, not rebuilt. |
| `HierInStage` | `hierL δ` in `Lset lam` | `Probe679.agda:84-85` | TYPE, green. The assembly's waypoint. |
| `CompletenessFrom` | `SameHyp → HierInStage → Completeness` | `Probe679.agda:94-95` | **TYPE, green; NOT inhabited.** Its inhabitation is `[LJ-1.700]`'s obligation, closed NO-GO and upheld (`review-of-LJ-1-700-1.md:167`, `:174-175`). This is the stop the transcription respects. |
| `same-as-graph-both` | the union telescope to `SameAsGraph w b γ` | `Probe709.agda:67` | GO. Imported, not rebuilt. |
| `SameHyp` | all `w b γ` unconditionally | `Probe679.agda:48-49` | TYPE, green. PRODUCED here from 709's delivery by `same-hyp-of`. |

`[LJ-1.700]`'s NO-GO forbids one thing: inhabiting or applying
`CompletenessFrom`. The brief's named term is the via form, whose
type 713 delivered green, so no stop fires. The transcription takes
`cf` as an explicit hypothesis of the arrow, exactly as 713 did.

## 1. WHAT THIS TASK IS

The brief's schematic names four arrows: `CompletenessFrom`,
`Bound-in-tower-all`, `Identified-all`, and the `Completeness`
codomain. The authoritative signature is 713's delivered one at
`Probe713.agda:120-130`: after `cf` and the two rows it takes four
more supplies (`pow`, `ordb`, `up`, `down`), because the `SameHyp`
the first arrow consumes is PRODUCED from 709's delivery by
`same-hyp-of`. All seven arrows are transcribed unchanged.

One structural change was forced by the export duty. 713's term was
a member of the parameterised frame module `At713`; a top-level
declaration has no enclosing module to bind the frame, so the frame
is hoisted:

- `At723` is `At713` renamed, members byte-for-byte
  (`same-hyp-of`, `below-of`, `hier-of`, the frame-member
  `below-closed-via`).
- The top-level `below-closed-via` takes the frame as seven explicit
  leading arguments, then the seven arrows, and its body is 713's
  member consumed at its delivered address:
  `At723.below-closed-via lam ordλ succλ X X⊆Lλ ∅∈λ elem cf bound
  ident pow ordb up down`.

Two spellings were new, and both sit on measured precedents from
`[LJ-1.608]`, which used them at its own top level:

- the TYPE through a parameterised module with trailing arguments,
  `P679.At.CompletenessFrom lam ordλ succλ X X⊆Lλ ∅∈λ elem`, the
  form of `W3.Site.At.RecGraph∞ α ...` at `Probe608.agda:182`;
- the TERM discharging module parameters,
  `At723.below-closed-via lam ...`, the form of `Rows.the-graph α
  ...` at `Probe608.agda:184`.

The file's import block is 713's, byte-for-byte: each import is one
of the four arrows' addresses, and 713 already measured the cone as
their union. Nothing was trimmed because nothing is unused.

## 2. THE RUN

| run | exit | seconds | peak RSS | cache |
|---|---|---:|---:|---|
| `runs/p-1.out` | 0 | 344.24 (cold cone) | 1,609,367,552 B | worktree `_build` carried no probe interfaces |
| `runs/p-2.out` | 0 | 3.28 (warm recheck) | 680,919,040 B | interfaces from p-1 |
| `runs/witness-1.out` | pass | 4.22 | not recorded | warm |

The witness meter is what the acceptance derives the obligation
verdict from: it derives `module Target = LJ-1-723.Probe723 {ℓ} lem`
and references `Target.below-closed-via`. That run returned `pass`,
exit 0, 0 UNRESOLVED of 1, `probe_red=False`. The top-level export
does what the obligation list needs, and the four supplies after the
rows are visible in the witness's own type.

Process notes. ONE Agda process at a time; the first process was
green, so no rerun of the same code happened (the warm recheck is a
second measurement of the same bytes, 713's own p-1/p-2 pattern).
The heavy-object floor clause did not spend a hole run: no new proof
was attempted, the term was already typed at 713, and the whole-file
run priced itself and did not wall. This worktree has no `.venv`;
`check-survey-quotes.py` and `witness.py` ran under the main tree's
pinned venv by absolute path (`/Users/alsg/Agentic/Bedrock/.venv`,
Python 3.11.16). No import needed trimming (section 1).

## 3. W3, THE WIDEST UNMEASURED TERM

The brief names the probe: whether the transcribed assembly still
converts `step` at one frame. The transcription itself is that
probe, and the run measured it. `below-of`'s TARGET names
`B.Below`, 697's spelling, while its body calls
`P706.below-from-place`, whose output is 706's spelling of `Below`
(`Probe706.agda:78-79`, `Probe697.agda:81-82`). p-1 accepted that
body at that target with no coercion written: 693's `step` and W3's
`step` still convert at one frame in the live tree, cold cone,
`runs/p-1.out` EXIT 0. **GO, price 344.24 s cold / 3.28 s warm.**
The SameHyp half was measured green in the same run: the hoisted
709 delivery is accepted against 679's unconditional `SameHyp`
inside `same-hyp-of`'s body check.

## 4. W2 ANSWER

Nothing is proved twice. All four arrows are consumed at their
delivered addresses (`Probe706.agda:78`, `Probe697.agda:81`,
`Probe709.agda:67`, and `CompletenessFrom` as a type at
`Probe679.agda:94`). The new lines are the frame hoist and the
wrapper: one renamed module, one top-level signature, one
application. The mathematics is written once at the generic frame
and instantiated by nothing. No deadline forced a fixed form; no
conflict between W2 and this brief arose.

## 5. WHAT THE SHAPE RESISTED

- **What it cost.** 143 lines, 77 code. 344.24 s cold cone, 3.28 s
  warm, peak 75 percent of the cap. Green on the first process.
- **What the shape resisted.** Nothing at elaboration time. The one
  genuinely new surface, the top-level dotted-path spellings, sat on
  the 608 precedents and fired clean on the first run. No error
  survived to any run.
- **What I had to weaken.** Nothing in any delivered type.
  `CompletenessFrom` stays the explicit hypothesis it is; I did not
  apply it and did not let the schematic's four-arrow shorthand
  erase the four SameHyp supplies from the signature.
- **What I could not close.** The chain's third bill, the same one
  713 and `[LJ-1.700]` could not: `cf`'s inhabitation. The meter now
  closes `below-closed-via`, which is the assembly, not the
  inhabitation; `below-closed` without the hypothesis remains
  uninhabited in this tree.

## 6. WHAT THE NEXT BRIEF NEEDS

1. **THE ASSEMBLY'S LIVE ADDRESS IS THIS FILE.** The four names now
   exist in the live tree: `At723.same-hyp-of`, `At723.below-of`,
   `At723.hier-of`, `At723.below-closed-via`, and the top-level
   `below-closed-via`. A consumer imports
   `import LJ-1-723.Probe723 {ℓ} lem as P723` and calls with the
   seven frame arguments. Fund consumers; do not re-transcribe.
2. **THREE OPEN BILLS, NOT TWO.** The chain to `Completeness` still
   carries the two rows (`[LJ-1.711]`, `[LJ-1.712]`) and
   `CompletenessFrom`'s inhabitation (`[LJ-1.700]`, open, cure named
   and untested at `review-of-LJ-1-700-1.md:182-183`). The
   obligation closed here changes none of them.
3. **IF `[LJ-1.700]` IS RE-DISPATCHED**, start from its critic's
   handoff: the wall sits in `toL`, `same-at-codes` and
   `hier-at-code`, and the explicit codomain on `hier-at-code` is
   the first untested move (`review-of-LJ-1-700-1.md:182-183`). This
   probe's green rows carry explicit codomains throughout, a
   same-frame measurement that the narrow shapes are cheap.
4. **WHEN THE ROWS AND `cf` LAND**, the chain closes at
   `below-closed-via` with four applications, no new assembly work.

## 7. PRICE

Non-blank non-comment lines counted by
`awk 'NF' file | grep -cv '^[[:space:]]*--'`.

| what | lines | code lines | at `file:line` |
|---|---:|---:|---|
| the probe, whole | 143 | 77 | `Probe723.agda` |
| `At723` frame + members | 65 | 43 | `Probe723.agda:52-116` |
| top-level `below-closed-via` | 25 | 18 | `Probe723.agda:119-143` |

In-fence lines, the ledger's way: **0**. A raw `.agda` probe carries
no fence, so the ratio bar cannot fire on this return; it binds the
moment a `.lagda.md` master is written under `src/`.

## GATES

- **D-10** (`dev/LESSONS.md:1375`). Priced the recorded residue's
  truth before relying on it: the stop (`CompletenessFrom`
  uninhabited) was re-verified from this worktree's own files
  (`Probe679.agda:94-95`, `review-of-LJ-1-700-1.md:167`) before any
  Agda, and the delivered target is the corrected target 713 already
  recorded. Nothing rests on the brief's premise 4 being a supply.
- **C-22** (`dev/LESSONS.md:2307`). Skeleton saved before the first
  run (mtimes: probe 12:17:23, skeleton 12:17:35, `runs/p-1.out`
  12:23:24) and filled after each row landed.
- **P-l** (`dev/LESSONS.md:2367`). Obeyed. Every type names `Lset`
  stages through 679/697's opaque stage values and 697's own
  `Below`; no transparent presentation is named in a type; the
  `step` conversion lives inside `below-of`'s target check, which is
  a measurement site, not a type drag.
- **D-26** (`dev/LESSONS.md:1735`). Did not bind: no well-founded
  key was built.
- **C-42** (`dev/LESSONS.md:3762`). No refutation landed in this
  task; 713's `[CannotApply]` is not re-measured here and nothing
  new is refuted, so no sweep is due from this return.

## Return

The obligation is closed. `below-closed-via` stands at
`agents/tasks/LJ-1-723/Probe723.agda`'s top level, 713's assembly
under the name the meter reads, `CompletenessFrom` an explicit
hypothesis and never applied: first run EXIT 0 at 344.24 s cold cone
and 75 percent of the wide cap, recheck EXIT 0 at 3.28 s, witness
`pass` 0 UNRESOLVED of 1. W3 is answered GO: the transcribed
assembly still converts `step` at one frame, measured, not assumed.
The open bills are unchanged and named in section 6. Nothing is
staged, nothing is pushed, and the working tree carries only
`agents/tasks/LJ-1-723/` as changed output.

---

## ARCHIVE USED

- **`archive/dev/ORCHESTRATION.md`, declined.** Not read: this task
  is a single-probe transcription and consults no orchestration
  history.
- **`archive/dev/DD-archived.md`, declined.** Not read: no archived
  design decision bears on a transcription whose types are all taken
  from delivered probes.
- **`archive/dev/PLAN-archived.md`, declined.** Not read: no plan
  question arose; the brief names the file and the term.
- **`archive/dev/TASKS-archived.md`, declined.** Not read: the
  predecessor's record lives in the 713 worktree, not the archive.
- **`archive/dev/STATUS-archived.md`, declined.** Not read: standing
  status is `dev/pod/screen.toml`, and this return adds no status
  claim of its own.

## LITERATURE USED

- **`dev/literature/devlin-errata.md`, declined.** Not read: this
  return quotes no scanned page and no source question arose.
- **`dev/literature/BIBLIOGRAPHY.md`, declined.** Not read: no
  citation was added by this task.
- **`dev/literature/glossary-review-2026-08.md`, declined.** Not
  read: this return proposes no glossary entry.
- **`dev/literature/level-formula-slot-roles.md`, declined.** Not
  read: no level-formula role question arose; the probe's telescope
  is 713's, unchanged.
- **`dev/literature/primary-sources.md`, declined.** Not read: no
  primary-source question arose.

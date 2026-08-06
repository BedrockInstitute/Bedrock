# ARCHIVE.md: the archive registry

The registry of Bedrock's retired modules. One entry per module, written at
the moment of archival, recording what went, why, its last-green state, its
measured size, and the condition under which it would be worth consulting
again. The archive itself lives at `archive/` (repository root) and its rules
are stated in full in [archive/README.md](../archive/README.md) and in ruling
D20 ([dev/PLAN.md](../dev/PLAN.md) section 3, 2026-08-04). This file is the
index; the archive is the evidence.

## When an entry is made

An entry is written as part of the same change that moves a module into
`archive/`. It records facts as of that moment: the ruling that retired the
module, the commit at which it was last green, and its measured size.
Pre-regime deletions (made under D14 before D20 superseded it) are entered
against their deletion commits when the final archival sweep runs; git history
is their archive, so no files are restored.

## Columns

- **Module.** The module's name as it was known in the live tree, e.g.
  `L.Coding.Sequence`.
- **Original path.** The path the module held before retirement. The archive
  keeps that path under `archive/`, so the archived path is the original path
  prefixed with `archive/`.
- **Why archived.** The ruling and its date, e.g. `D17 + D20, 2026-08-04`,
  plus one line on what actually retired the module.
- **Last green.** The commit at which the module last passed the full gate
  (`make check`). This is what makes the module usable later: a revival starts
  from a known-green state. For a pre-regime deletion there is no archived
  file, so this column carries the deletion commit.
- **Measured size.** Non-blank lines inside the module's Agda code fences at
  its last-green commit, single caliber. This column is a measurement of the
  file as archived, never a projection; projections carry two calibers and do
  not belong here.
- **What this code did right.** Added 2026-08-06 under `[L3.32-F4]`, and the
  only column here that is not about retrieval. A retirement removes files; it
  should not silently remove a PRACTICE. `[L3.32-T86]` measured the retiring
  internalization subtree at **0.013 s/line over 26,483 lines** against a
  surviving trunk at 0.104, and found the cause was not sealing but that these
  chapters state at **abstract carriers and variable indices**, so nothing
  re-normalizes. Nobody knew that until a profile was run, and by then the
  newer chapters had already lost the habit. **So if an archived module did
  something measurably well, record it here in one sentence, with the
  measurement.** Leave it blank rather than filling it with praise: an
  unmeasured compliment in this column is worse than an empty cell, because it
  makes the column unreadable. This is the field the freeze's exit condition
  (D30 part 3) requires filled before the D18 archival lands.
- **Revival condition.** The concrete condition under which this module would
  be worth consulting again. A condition that becomes provably moot may be
  closed, and the module's files may then be genuinely deleted, recorded in
  the entry.

## Closing a revival condition

The archive is an index of evidence, not a landfill. When a revival condition
becomes provably moot, the entry records the closure, with the ruling or
reasoning that made the condition moot, and the module's files may then be
genuinely deleted. A revival that lands is recorded in the entry; the archived
original stays frozen unless and until the condition is closed as moot.

## Entries

| Module | Original path | Why archived (ruling, date) | Last green (commit) | Measured size | What this code did right | Revival condition |
|---|---|---|---|---|---|---|
| `L.Rud.Realize` | `src/L/Rud/Realize.lagda.md` | The realization induction over an abstract basis: for every Delta-0 formula, a realizing basis composite. It served the comprehension switch through the image-principle route. That route was superseded when the switch was discharged unconditionally in `L.Rud.SatSets` (`full-switch-⊇`), after which nothing in the ruled configuration exercised the import edge that kept this chapter alive. Retired under D17 and D20, 2026-08-04, on `[T7]`'s import analysis and `[T11]`'s compile gate. | `d31b196` | 789 code lines | Not yet assessed. `[L3.32-T86]`'s profile covered the internalization subtree, not this chapter; if the basis-neutral statement style is why it was cheap, that belongs here with the number. | If a future development needs realization over an ABSTRACT basis (this chapter's whole point was basis-neutrality, validated by a probe before the rud route was adopted), rather than the concrete sixteen-operation discharge the tree now uses. The fine-structure era's rud-A relativizations are the named candidate. |
| `L.Rud.Switch` (partial, 506 lines cut in place) | `src/L/Rud/Switch.lagda.md`, the Realize-dependent half | Six modules (`Bs`, `Ev`, `Rl`, `Closure` with its nested `Eval-J`, `WalkCon`, `LimitSwitch`) and the notation-and-spec layer consuming Realize's bounded-existential notation. `[T11]` proved by compile gate that the narrow cut (the six modules alone) does NOT compile and the widened cut does, which is why the spec layer travels with them. The surviving chapter is the reverse hops and the description side, which are what the bridge consumes. | `d31b196` | 506 code lines of the chapter's 803; the chapter now stands at 297. The cut regions are not moved to `archive/` as files, since they were interior to a surviving chapter: this commit is their archive, and `git show d31b196:src/L/Rud/Switch.lagda.md` recovers the pre-cut text | Not yet assessed, same reason as the row above. | Same as `L.Rud.Realize`: these are its consumers. Revive together or not at all. |
| `L.Rud.OpGraph` | `src/L/Rud/OpGraph.lagda.md` | The operation graphs in VARIABLES rather than constants: the constant-to-variable transfer, extensional graph closure, and five instantiations. It existed to fill a wall in the order-formula route, and **`[T63]` refuted that wall**. Retired 2026-08-06 under D17 and D20 on `[L3.32-T94]`'s architecture audit and the owner's ruling; verified at archival to have no importer inside the rud route or outside it. | `1a2fbb0` | 285 code lines, 66 obligations | **Measured 0.057 s per obligation, AT OR BELOW the retiring subtree's 0.074 benchmark**, without a single `opaque`. It states the transfer over an abstract carrier and quantifies the argument position rather than naming it, which is why nothing re-normalizes. It also **named its own gap honestly**: the four tuple operations are recorded as inexpressible, since their totalization goes through projections whose off-argument behaviour the object language cannot characterize, so the delivered shape is one-way and says so rather than papering over it. | If the order-formula route ever needs a constant-to-variable face again. `[T63]`'s refutation is the thing to re-read first: it says why this face was not needed, and a revival must say why that reasoning no longer applies. |
| `L.Rud.CodePred` | `src/L/Rud/CodePred.lagda.md` | The object-language code predicate read in a level's inner world: twelve clauses fused at the node, rank descent, two-way adequacy by construction, and the code sets discharged as level members at every arity. It served the satisfaction-internalization route, **which died with the route change ruled in D18**. Retired 2026-08-06 under D17 and D20 on `[T94]`; no importer at archival. | `1a2fbb0` | 1,186 code lines, 234 obligations | **The best per-obligation figure in this archival at 0.039 s, roughly half the 0.074 benchmark, over the largest body of the four.** Twelve fused clauses and a rank-descent argument for the price of nine seconds. Worth reading before writing any new object-language predicate: it is the standing proof in this repository that a large twelve-clause predicate need not be expensive. | If an object-language code predicate is ever needed again, most plausibly in the fine-structure era where a coded satisfaction predicate returns for a different reason than the one that died. |
| `L.Rud.CodeSet` | `src/L/Rud/CodeSet.lagda.md` | The formula codes over a carrier as one sealed family: membership definitional, decode untruncated, every code unconditionally a closure member. Consumed only by `L.Rud.CodePred`, which retires with it, so it travels with its one consumer. Retired 2026-08-06 under D17 and D20 on `[T94]`. | `1a2fbb0` | 193 code lines, 43 obligations | Not much, on the measurement: **0.423 s per obligation, 5.7x the benchmark and the worst of the four**, in the smallest body. Recorded plainly because an empty cell here would be more useful than a compliment: this one is archived for having no consumer, not for being good. | Revive only together with `L.Rud.CodePred`; it is that chapter's substrate and has no independent use. |
| `L.Rud.BaseBlock` | `src/L/Rud/BaseBlock.lagda.md` | Hereditary finiteness at the base limit: the S-side tallies, the finite-member lemma, the power obligation at a finite carrier, and the base-block stage instance. **Its content was harvested into `L.Rud.Finite` by `[T82]` and `L.Rud.HF` was re-pointed at the new home**, after which nothing imported it. Retired 2026-08-06 under D17 and D20 on `[T94]`. | `1a2fbb0` | 393 code lines, 97 obligations | 0.094 s per obligation, 1.3x the benchmark: close, and unremarkable either way. The thing worth recording is not the code but the SEQUENCE: `[T82]` rewrote what was actually needed into a generic tally module first, re-pointed the consumer, and only then was this chapter importable by nobody. That is D17 executed in the right order, and it is why this archival cost nothing. | If the first-limit tally instances are ever wanted in their original concrete form rather than as instances of `L.Rud.Finite`'s generic machinery. |

## Verification record

The gate exclusions were confirmed on 2026-08-04 by a poison-pill test rather
than by reading: a file was placed under `archive/` that violates every gate at
once (no OPTIONS header, an em dash, CJK mixed with half-width punctuation,
and Agda that does not typecheck), and `make check` passed with it in place.
The four scripts skipped it, the Agda gate never reached it, and `reuse lint`
covered it through the carve-out at full compliance. The file was then removed.
Repeat this test whenever a gate or a script's file-discovery changes.

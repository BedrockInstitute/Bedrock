# LJ-1.742-SPLIT report: `defat-fill-asConst`, the remaining walks

(This skeleton was written before the first Agda run of this dispatch and
filled as the runs landed; see C-22, `dev/LESSONS.md:2307`.)

## HEAD

head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.742-SPLIT
obligation: agents/tasks/LJ-1-742-SPLIT/Probe742Split.agda::defat-fill-asConst
verdict: **NOT DISCHARGED. PARTIAL: PARK, THE OBLIGATION STAYS OPEN.**
The delivered file is `Probe742Split.agda.txt` (1464 lines). It does not
typecheck yet: two holes stand in `remaining-goal` (line 1455: the
`satGraphAt` conjunct and the `DefinesAt` conjunct), and the checker's
last frontier is one substitution-type error in the bounded closedness
frame (Section 13). The green prefix of `[LJ-1.742]` is transcribed
verbatim (Sections 1 to 9). On top of it this dispatch WROTE the bounded
walk the brief names, as Sections 10 to 16: the Correct instance at the
bound, the two quantifier rules, the staged reader intros for every
landed reader (`prAtL`, `sucAtL`, `consAtL`, `appAt`, `tagAtL`,
`tagPairAtL`, `arityTagAtL`, `arityTagPairAtL`, `subValAt`,
`subValSuccAt`, `extAt`, `domAt`), the two clause frames, the bounded
closedness walk (four shapes, one generic `closedOfᴬ`, two instances:
closure and slot-ready), the bounded shape walk (twelve alternatives,
`shapedOfᴬ`, `shapedCloᴬ`), and conjunct 1 of the assembly
(`isCodeAtᴬ` = `keyArityᴬ` + `hasWitᴬ`, complete). Nothing lands in
`src/`. `stage-read` is not stated or inhabited. `Sat-in-carrier-lim`
appears in no code line. The staged-Sat induction was not funded.

## 0. THE PREMISES, VERIFIED AT DISPATCH

The brief's premise files (`agents/tasks/LJ-1-742/lj-1.742-report.md`,
`agents/tasks/LJ-1-740/LJ-1.740.md`) are NOT tracked in git at this
commit, so they are absent from this worktree; they were read at the
main checkout (`/Users/alsg/Agentic/Bedrock/agents/tasks/LJ-1-742/`),
same repository, same bytes the program's brief cites. The five
premises stand as written. The green prefix was transcribed from
`agents/tasks/LJ-1-742/Probe742.agda.txt` lines 1 to 523, byte-faithful
up to the module rename (`LJ-1-742-SPLIT.Probe742Split`).

## 1. WHAT WAS BUILT (all in Probe742Split.agda.txt)

1. **Sections 1-9**: the `[LJ-1.742]` prefix, transcribed. Its own
   verdict run was 4.01 s, 746,520,576 B
   (agents/tasks/LJ-1-742/runs/p-26-desc.out).
2. **Section 10, `Bnd`** (line ~566): the `Correct` instance at
   `c := LsetS γ oγ` (the obligation's own reading, since
   `𝒮ʟ = 𝒮ᵥ ↾ isL` definitionally), `Stg` (staging as
   `fst x ∈ˢᵥ Lset γ`), the transitivity step `trv`, `numStg`
   (numerals staged), `SupplyMerge` at the succ-closed limit, and the
   two quantifier rules `∃ᴬ-in` / `∀ᴬ-in` / `∀ᴬ-out`.
3. **Section 11, `Rd`** (line ~640): the bounded reader intros and
   outros. The Delta0 readers move the landed adequacy across by the D0
   transport; the existential readers build the witness staged.
4. **Section 12**: `domAtᴬ-out`, the clause frames `binClauseᴬ-in` /
   `unClauseᴬ-in` (the `∀̇∈` filter reads as the standard one; the `∀̇`
   binders arrive staged), and the bounded successor staging `sucStg`
   over `SupplyEnv.sucK`.
5. **Section 13, `ClW`** (line ~975): the four closedness shapes under
   the bounded reading (`binSameClosedᴬ-in`, `unSameClosedᴬ-in`,
   `unSuccClosedᴬ-in`, `binSuccClosedᴬ-in`). Each consumes the shape
   equation out of the bounded tag antecedent and produces the leaf
   lookups with the bounded `appAtᴬ-in`.
6. **Section 14, `ClOf`** (line ~1090): the generic `closedOfᴬ` over
   any peeling set, with `closureClosedᴬ` at the closure. The slot
   instance needs the same theorem at the L-key peel (`slot-inv`);
   it is written but not yet checker-clean.
7. **Section 15, `ShW`** (line ~1185): the bounded shape walk:
   `isTmAtᴬ-in` (both branches, constants by carrier membership,
   variables by `#mono` and `toℕ<n`), `binFormᴬ-wit` / `unFormᴬ-wit`,
   `shapedOfᴬ` (the twelve alternatives, each witness constructed
   staged: numerals by `num∈γ'`, term codes and subcodes by the passed
   `ctst` / `cdst`), and `shapedCloᴬ` at the closure.
8. **Section 16, `Walk`** (line ~1362): the assembly at the fixed
   environment. `keyArityᴬ` (the code is the witness; the tag equation
   is the `keyS`/`codeS` identification), `hasWitᴬ` (the closure is the
   witness; `closedAtᴬ` by Section 14, `shapedAtᴬ` by Section 15),
   `isCodeAtᴬ` = conjunct 1, complete. `remaining-goal` stands with two
   holes: conjunct 2 (`satGraphAt`) and conjunct 3 (`DefinesAt`).

## 2. THE MAIN TERM IS CLOSED BY ONE SUBST

`defat-fill-asConst` (last block) is `subst` along
`sym (relativize-correct (DefBody w) δ)` applied to `remaining-goal`,
as the 742 report planned. When the two holes close, the obligation
closes with no further change to the main term.

## 3. WHAT THE SHAPE RESISTED (measured, this dispatch)

1. **The Delta0 transport does not cross the constant-type change
   directly.** `Δ₀-prAt q u v` lives at `Formula (V ℓ) n` but `prAtL`
   at `Formula S n`; `Δ₀` is K-polymorphic so the witness does not
   reuse as-is. The road that works: `Δ₀-liftFo` (`L.Absoluteness`)
   with a hand-built `BoundedFo InL` certificate. Every reader here
   carries no constants, so each certificate leaf is the unit. The
   certificates for `prAt`, `sucAt`, `consAt` are Section 11's
   `bddPrAt` / `bddSucAt'` / `bddCons'` (the last mirrors the private
   `bddCons` of `L.Coding.Model`).
2. **The bounded ∃̇ needs a STAGED witness where the standard reading
   needs only a member.** Every witness is therefore built, not
   consumed: numerals (`numStg`), the model pairs (`prʟStg`, which is
   `pr∈γ'` transported along `prʟ-fst`), successors (`sucStg`, which is
   `SupplyEnv.sucK` transported along `sucʟ-fst`), and the closure /
   table sets themselves (`clo∈γ`, `slot∈γ`, `satTable∈γ` from the
   prefix). This is the law the 742 report's staging inventory named;
   the dispatch measured it as code.
3. **The ᴬ-world's `extAt` restricts BOTH its universal halves to the
   bound.** So a consumer of `envSetAtᴬ` needs the member's STAGEDNESS
   before it may read the environment description. Every clause-site
   variable arrives staged because the clause frames hand the `∀̇`
   binders over with `Stg` attached (`ab→st`).
4. **`Δ₀-prAt`-style reuse fails, `Model`'s private certificates are
   not importable, and `memb` / `negRel` / `impRel` / `topRel` are
   private.** The negation, implication and top rels are redefined
   locally at the same slots (they are one line each); the remaining
   clauses do not need them redefined because their frame intros are
   generic.
5. **The machine.** From 08:46 the box's agda-watchdog killed every
   agda process within one sweep while system swap sat at
   8726.88 MB (`vm.swapusage`; threshold 8192 MB;
   `_build/tools/agda-watchdog.log` 08:46:29, 08:46:49, 08:48:30,
   08:56:16 and after). This is the 737-SPLIT machine finding
   (`agents/tasks/LJ-1-737-SPLIT/lj-1.737-SPLIT-report.md`), met again
   at this task's own site: warm-interface checks of 2 to 9 s survived
   only in gaps between sweeps, and every run that straddled a sweep
   died (runs/w*.out through runs/wt-*.out, exit 137). The heap cap was
   never reached; the widest frontier run peaked far under the 2 g pane
   caliber. No heap wall of the term is claimed.

## 4. THE PRICE, AS FAR AS IT IS MEASURED

- The prefix alone: 4.01 s, 746,520,576 B at the wide caliber
  (742's p-26-desc).
- Sections 10-12 against warm `src/` interfaces: 2.7 to 3.9 s per
  checker run (runs/s16-s31). The full 1464-line file: not yet timed
  clean; the checker reaches Section 13 before the first error.
- Estimated remaining to GO: the slot-peel instance of `closedOfᴬ`
  (~40 lines), the bounded twelve-clause walk (~250 to 400 lines: the
  envSet consumption is Section 12's `domAtᴬ-out` plus the four
  `envOver` readers; the bodies replay `L.Coding.Sound`'s clause
  verifications with the bounded reader intros of Section 11),
  `DefinesAtᴬ` (~60 lines: `envOneOut` / `envOneIn` are written at
  Walk lines 1374-1381, the staging is `Lset-fin` + `envIsFinSet`
  (`refl`) + `envL` + the successor absorb), and the two holes.

## 5. WHAT THE NEXT BRIEF NEEDS

1. **The continuation names `remaining-goal` as the sub-obligation**
   with Sections 10 to 16 declared the frozen prefix, and the slot
   instance of `closedOfᴬ` plus the twelve-clause walk as the scope.
2. **The bounded twelve-walk is the only mathematics left.** Its data
   flow: for each clause, the Parts inversion (Table's `slot-inv` and
   `entry-out`, as in `L.Coding.Sound`'s modules) is meta and
   reusable; the ᴬ-layer is the frame intro plus the reader intros of
   Section 11; every ∃ᴬ witness is staged by descent (`trv`) or by
   `pr↓` on a staged environment's pairs (`Sat-mem` + `envSet-out`
   give the graph; `tmIs-var-out` gives the pair; `pr↓` stages the
   value). The seven ambient-set clauses consume `envSetAtᴬ` as
   Section 12's extAt pair.
3. **Do not re-fund**: Sections 10 to 15 (written; the checker frontier
   is inside Section 13, one substitution error at line ~974),
   `envL` / `𝒟ₒ→isL` (no stage), the descent package (Section 9 of the
   prefix).
4. **The machine**: any dispatch that must run Agda on this box should
   price the watchdog first (`vm.swapusage` against the 8192 MB
   threshold) and keep warm-interface runs under one sweep period.

## FILES

- agents/tasks/LJ-1-742-SPLIT/Probe742Split.agda.txt (1464 lines;
  .txt because two holes and one checker frontier error stand)
- agents/tasks/LJ-1-742-SPLIT/lj-1.742-SPLIT-report.md (this file)
- agents/tasks/LJ-1-742-SPLIT/runs/ (s1-s36, auto-1, r/t/u/v and
  lettered series: every checker run logged; rc 137 = watchdog kill,
  rc 42 = checker error frontier; each error class and its fix is
  visible as a run series)

## ARCHIVE USED

All five injected archive candidates were read at their heads and are
DECLINED, not used. This return is an assembly of live files: the
transcribed 742 prefix, the landed masters cited at `file:line` in
Sections 1 and 3, and this task's own runs.

- archive/dev/ORCHESTRATION.md:1 `# ORCHESTRATION: the orchestrator's
  operating rules`. Declined: not used. The retired dispatching rules
  play no part in a bounded-semantics walk.
- archive/dev/DD-archived.md:1 `# THE \`DD\` RULING SERIES, archived in
  full 2026-08-18`. Declined: not read beyond the head. The live clauses
  this dispatch answers to are in the slot file and the brief.
- archive/dev/PLAN-archived.md:1 `# ARCHIVED 2026-08-20`. Declined: not
  read beyond the head. The live plan is the screen and the direction.
- archive/dev/STATUS-archived.md:1 `# STATUS-archived: the goal table of
  the internalization route`. Declined: not read beyond the head. This
  task's route is the live queue's, not the archived table's.
- archive/dev/TASKS-archived.md:1 `# Archived task index: the
  \`L3.32-T\` series`. Declined: not read beyond the head. The
  predecessors this task needed (737-SPLIT, 740, 742) are live files
  cited at `file:line` in Section 0 and Section 3.

## LITERATURE USED

All five injected literature candidates were read at their heads and are
DECLINED, not used. The verdict quotes no book: every step in Sections 1
to 4 is an in-tree fact at `file:line`.

- dev/literature/glossary-review-2026-08.md:1 `# Glossary review: the
  119 pre-protocol entries`. Declined: not used. A raw `.agda.txt`
  probe and its runs carry no translation surface.
- dev/literature/devlin-errata.md:1 `# Devlin errata: documented error
  classes (do-not-repeat checklist)`. Declined: not read beyond the
  head. This dispatch cites no Devlin page; the fill is in-tree
  assembly.
- dev/literature/level-formula-slot-roles.md:1 `# The level-hood
  formula: arity, what it binds, what stays free`. Declined: not used.
  The level formula plays no part in the bounded walk.
- dev/literature/primary-sources.md:1 `# Primary sources, second round:
  Jensen manuscript, Devlin, Jech`. Declined: not used. The fetch map
  is the literature team's record; this dispatch fetches nothing.
- dev/literature/BIBLIOGRAPHY.md:1 `# Bibliography for the rud route`.
  Declined: not read beyond the head. No source beyond the tree was
  consulted for this dispatch.

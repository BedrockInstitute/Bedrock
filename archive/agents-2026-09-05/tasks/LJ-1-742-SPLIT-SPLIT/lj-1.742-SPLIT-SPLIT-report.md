# LJ-1.742-SPLIT-SPLIT report: `defat-fill-asConst`, the last two conjuncts

(Written as a skeleton before the first Agda run and filled as the runs
landed; see C-22, `dev/LESSONS.md:2307`.)

## HEAD

head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.742-SPLIT-SPLIT
obligation: agents/tasks/LJ-1-742-SPLIT-SPLIT/Probe742SplitSplit.agda::defat-fill-asConst
verdict: **NOT DISCHARGED. PARTIAL: PARK.**
The probe is delivered as `Probe742SplitSplit.agda.txt` (1948 lines; it does
not typecheck: the top-level `defat-fill-asConst` body and two deferred
level-metas stand, see runs/final-frontier.out, rc 42, 638 s at the pane
caliber). The review statement for the critic is
`review-of-defat-fill-asConst.md`.

## 0. THE PREMISES, VERIFIED AT DISPATCH

The brief's premise files (`agents/tasks/LJ-1-742-SPLIT/`,
`agents/tasks/LJ-1-740/`, `agents/tasks/LJ-1-736/`) are NOT tracked in
git at this commit, so they are absent from this worktree; they were
read at the main checkout (`/Users/alsg/Agentic/Bedrock/agents/tasks/`),
same repository, same bytes the program's brief cites. The predecessor
verdict is PARTIAL/PARK (lj-1.742-SPLIT-report.md:9), not NO-GO and not
FALSE, so the work proceeds on the type the predecessor delivered.

## 1. WHAT WAS BUILT

1. **The frozen prefix transcribed and repaired.** The 742-SPLIT probe's
   1464 lines were transcribed with the module renamed. The repairs: the
   Section 13 substitution direction (`sucStg` transports along
   `sym (sucł-fst ar)`), the clause frames' `g`-callbacks now hand the
   binders' `Stg` over and consume the shape equation at the 5-deep
   (resp. 4-deep) environment, the where-block index types pinned to
   `Fin (5 + n)` / `Fin (4 + n)`, `binFormᴰ-wit`/`unFormᴰ-wit` take the code
   as a value with the arity numeral outermost, `isTmAtᴬ-in` stated as
   slot-membership plus the slot's stagedness (the witness staged by `trv`),
   `shapedOfᴬ`/`shapedCloᴬ` carry `astg`, and `Walk`'s conjunct 1 moved to
   the `z`-carrying environment `(Sat ∗ keyS ∗ z ∗ env)`.
2. **`ClOf.closedOfᴬ` generalized to an arbitrary slot index** (frozen-
   prefix deviation, flagged): `(D) → Peel D → ∀ (δ) (i : Fin m) (p :
   fst (lookup i δ) ≡ fst D) → ⟨ δ ⪫ᴰ closedAt i ⟩`. The proofs are
   intact; the graph's closedness needs the slot at `Ci`, not at `zero`.
3. **The bounded ambient moves `Ambientᴰ` (17B), complete.** Sound's
   Ambient replayed under the bounded reading: `recᴬ` (the Recover replay:
   svAtᴬ-out, domAtᴬ-in, valuesInAtᴬ-out at staged instances; pairsInAt
   joined by the Δ₀-transport on a built certificate Δ₀-pairsIn),
   `intoᴬ`, `outofᴬ` (via Δ₀-liftFo and envOverAt-transport), `asEnvᴬ`.
4. **Staging (17A).** `envStg` (environments are definitionally finSets, so
   FiniteSup's finSetK stages them), `stgVal₀`/`stgIn`, `tmValVarᴬ-in`/
   `tmValConᴬ-in`/`tmValVarOfᴬ`/`tmValConOfᴬ` (tmValAt's two disjuncts,
   both directions), `svAtᴬ-out`, `domAtᴬ-in`, `valuesInAtᴬ-out`,
   `ovᴬ-in` (standard → bounded envOverAt), and the local copies of
   Model's private `negRel`/`impRel`/`topRel`/`memb`.
5. **The descent inventory wired.** `EnvSupply.Fact` at
   K := LsetS γ oγ (valK, tmValK, valV, valW, subKSucc-gen, ConsKClosed)
   with `Key.FiniteSup.finSetK` and `SupplyEnv.sucK` — the ∃-witness
   staging for every clause family is supplied by landed lemmas, not new
   mathematics.
6. **The Twelve module skeleton (17C)** with the graph environment
   gEnv, the slot-index constants, and the slot/table stagedness.

## 2. THE SECTION 13 FRONTIER: RESOLVED

The reported substitution error was `sucStg` transporting along
`sucł-fst ar` in the wrong direction; `sucK` delivers
`⟨ sucV (fst ar) ∈ Lset γ ⟩`, so the transport is along
`sym (sucł-fst ar)`. Behind it sat the same writing-slip class in the
frames (the shape equation consumed at the 4-deep environment while `g`'s
`sh`/`hac` are stated at the 5-deep one) and the unpinned `Fin (5 + _)`
metas — all repaired. After the repairs the checker's frontier moved to
the Fill's own new code.

## 3. WHAT THE SHAPE RESISTED (measured, this dispatch)

1. **The bounded ∃̇ is the whole cost.** Atoms, ∀̇∈/∃̇∈
   (pairsInAt entirely) and the implication frames read as the standard
   ones; every unbounded ∃̇ must be discharged staged, and every
   unbounded ∀̇ restricts to staged binders. That is exactly the
   predecessor's diagnosis, now measured as code.
2. **The ambient-set recovery cannot reuse `Recover` directly.** The
   bounded envSetAt's extAtᴬ halves give svAt/domAt/valuesInAt only at
   staged instances, and the standard envOverAt is not recoverable from
   them. `Ambientᴬ.recᴬ` replays Recover with every svAt/domAt/valuesIn
   instance at staged sets (numerals, domAtᴬ-in's witnesses, pairsIn
   witnesses descended by trv) and pairsInAt by the Δ₀-transport.
3. **`ClOf.closedOfᴬ` at index `zero` cannot sit at the graph's `Ci`.**
   Satisfaction is not invariant under permuting the environment's head
   binders, so the slot instance must be at `Ci` with the lookup path
   supplied. The generalization is mechanical (all proofs intact) but it
   touches the frozen prefix — flagged here for the owner.
4. **The machine.** Full checks of the growing file ran 590 to 640 s at the
   pane caliber; no heap wall, no watchdog kill (system swap stayed below
   the threshold throughout). Warm-interface edits are the way to work on
   this file; each frontier iteration costs ~10 minutes.

## 4. THE PRICE, AS MEASURED

- The delivered 1464-line prefix, cold: **11.2 s** (runs/f1.err, rc 42 at
  the Section 13 substitution error).
- The repaired prefix, cold: **12.2 s** (the Section 14-era frontier).
- This dispatch's 1948-line file, cold, at return: **638 s** at the wide
  pane caliber (runs/final-frontier.err), rc 42 with two deferred metas and
  the pending `defat-fill-asConst` body.
- Remaining to GO, estimated: the five clause-family bodies (the atom
  family is the widest at ~90 lines; prop ~70; neg ~50; quant ~90; bnd
  ~90; top/bot ~40), the graph assembly ~50, `DefinesAtᴬ` ~60, the final
  term ~10. Everything they consume is now in the file or in landed
  lemmas.

## 5. WHAT THE NEXT BRIEF NEEDS

1. **One continuation, same obligation name, same file.** The scope is
   only: the five clause-family bodies of Section 17C (each is Sound's
   assembly with Ambientᴬ in place of Ambient and the staged witnesses
   descended via `Fact`/`trv`/`prK`), then 17D (the graph witness:
   C := slot A phi, T := satTable A phi, b := A, all staged; the pin by
   `sym qw`; closedness by `ClI.closedOfᴬ (slot A phi) slot-inv gEnv Ci
   refl`; domAt by `domAtᴬ-in` with `Table.inSlot`; appAt by the
   entry-in transport along `keyBridge`; twelve by 17C), 17E
   (`DefinesAtᴬ` mirroring Powerset's `into`/`back` under `extAtᴬ`;
   every member of `envOne v` is definitionally staged, so the
   envOneAt-out equality survives), and the final `subst` along
   `relativize-correct`.
2. **Do not re-fund**: Ambientᴬ, the Δ₀-pairsIn certificate, the
   pointwise extractions, the staging helpers, the frames, ClOf, ShW.
3. **Watch two traps**: the `⊎`-vs-`∥∥₁` difference between the ∨̇
   value and the ∃̇ value (the ∨̇ eliminates by pattern, the
   ∃̇ needs `PT.rec`), and `snotz`/`znots` (Cubical's names are
   swapped relative to intuition: `snotz : suc n ≡ zero → ⊥`).
4. **The ratio bar.** The .agda.txt probe carries no fences, so the bar
   cannot fire; the next dispatch should keep the same form.

## FILES

- Probe742SplitSplit.agda.txt (1948 lines; cannot typecheck: the pending
  `defat-fill-asConst` body and two deferred level-metas)
- lj-1.742-SPLIT-SPLIT-report.md (this file)
- review-of-defat-fill-asConst.md (the NO-GO statement for the critic)
- runs/ (f1–f9 and final-frontier: every checker run logged; rc 42 with
  the frontier error class visible per run)

## ARCHIVE USED

All five injected archive candidates are DECLINED, not used. The work is an
assembly of live files: the transcribed 742-SPLIT prefix, the landed
chapters cited at `file:line` (Model, Sound, Slot, Table, Closed, Shape,
Graph, Powerset, EnvSet, EnvSupply, Key, InL), and this task's own runs.

- archive/dev/ORCHESTRATION.md:1 `# ORCHESTRATION: the orchestrator's
  operating rules`. Declined: not used. The retired dispatching rules play
  no part in a bounded-semantics walk.
- archive/dev/DD-archived.md:1 `# THE \`DD\` RULING SERIES, archived in
  full 2026-08-18`. Declined: not read beyond the head. The live clauses
  this dispatch answers to are in the slot file and the brief.
- archive/dev/PLAN-archived.md:1 `# ARCHIVED 2026-08-20`. Declined: not
  read beyond the head. The live plan is the screen and the direction.
- archive/dev/STATUS-archived.md:1 `# STATUS-archived: the goal table of
  the internalization route`. Declined: not read beyond the head. This
  task's route is the live queue's, not the archived table's.
- archive/dev/TASKS-archived.md:1 `# Archived task index: the \`L3.32-T\`
  series`. Declined: not read beyond the head. The predecessors this task
  needed (742-SPLIT, 740, 736) are live files cited at `file:line` in
  Section 0.

## LITERATURE USED

All five injected literature candidates are DECLINED, not used. The verdict
quotes no book: every step is an in-tree fact at `file:line`.

- dev/literature/glossary-review-2026-08.md:1 `# Glossary review: the 119
  pre-protocol entries`. Declined: not used. A raw .agda.txt probe and its
  runs carry no translation surface.
- dev/literature/devlin-errata.md:1 `# Devlin errata: documented error
  classes (do-not-repeat checklist)`. Declined: not read beyond the head.
  This dispatch cites no Devlin page; the fill is in-tree assembly.
- dev/literature/level-formula-slot-roles.md:1 `# The level-hood formula:
  arity, what it binds, what stays free`. Declined: not used. The level
  formula plays no part in the bounded walk.
- dev/literature/primary-sources.md:1 `# Primary sources, second round:
  Jensen manuscript, Devlin, Jech`. Declined: not used. The fetch map is
  the literature team's record; this dispatch fetches nothing.
- dev/literature/BIBLIOGRAPHY.md:1 `# Bibliography for the rud route`.
  Declined: not read beyond the head. No source beyond the tree was
  consulted for this dispatch.

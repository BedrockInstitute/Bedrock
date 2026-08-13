# LJ-1.116: at which alpha does Upper actually need sq?

tier: codex (default)

## STATUS

COMPLETE. The demand set is read and the omega-site check is
machine-checked. For the generic `BoundedSubsetAt` module, `sq δ` is
demanded at every infinite ordinal δ ≤ α. For the concrete consumer
site α = ω, the demand is only at ω, and the honest pairing supplies
it. The abort criterion's first branch fires for the site. The
truncation question dissolves for the site. The probe is
`src/ProbeLJ1116A.agda`, GREEN at the C-12 cap, one process. No master
was touched. No commit, no push.

## 0. THE VERDICT

**The consumer's site demands `sq` only at ω, and the honest pairing
supplies it there.** The site is the [LJ-1.94] instantiation: κ the
Hartogs cardinal, α = ω, x = ∅ (`src/ProbeLJ194A.agda:1202-1210`;
`[LJ-1.103]` records that "the consumer site runs at α = ω").

The demand trace, at `file:line`:

1. `Devlin55` applies `stage-card-upper α ordα α∉ω` at its site's own
   α (`src/L/BoundedSubset.lagda.md:1529-1530`), and `CodeCount`'s
   `Bound` is at the same α (`:1426-1427`).
2. `Upper.stage-card-upper` is `∈-induction step`
   (`src/L/StageCardinal.lagda.md:557-559`). The induction applies
   `step` at every member of the ordinal
   (`src/V/Hierarchy.lagda.md:177-180`).
3. `step α = limit-step α`, and `LimitStep`'s `Bound` instantiates
   `sq α infα` (`src/L/StageCardinal.lagda.md:281`). This is the only
   use of `sq` in the module (the parameter at `:15` and the use at
   `:281` are the only occurrences).
4. At a finite member δ ∈ ω, the premise `δ ∉ ω` is empty, so `P δ`
   closes by absurdity and `sq δ` is never demanded (`P` at
   `:528-530`). At every infinite member, the branch applies the
   induction hypothesis (`:545-553`), which descends.

So for the generic module the demand set is **every infinite ordinal
δ with ω ≤ δ ≤ α**. At the concrete site α = ω, every member of ω is
finite, the branch never descends, and the demand set is **{ω}**.

`sq ω` is honest: `NumeralPresentation.pairω` and `pairω-inj`
(`src/ProbeLJ1106A.agda:127-137`). The probe machine-checks the
omega-site instance. `Up.stage-card-upper ω ω-ord (∈-irrefl ω)` and
the `Bound` formula-count at ω both close
(`src/ProbeLJ1116A.agda:69-83`), GREEN.

The generic-module reading is the other half of the verdict. A
`BoundedSubsetAt` instantiation at an arbitrary infinite α demands
`sq` at every infinite ordinal below it. That half keeps the
truncation wall load-bearing. The chain does not instantiate it: the
site is ω.

## 1. THE DEMAND SET (question 1)

The answer: **the site's own α, and every infinite ordinal below it,
including ω.** At the concrete site, only the site's own α = ω is
demanded.

The trace is in section 0. The load-bearing lines:

- `sq` appears in `L.StageCardinal` at exactly two lines: the
  parameter (`src/L/StageCardinal.lagda.md:15`) and `LimitStep`'s
  `Bound α oα infα (sq α infα)` (`:281`).
- `limit-step` is `LimitStep.h` and `LimitStep.h-inj` at the same α
  (`:394-397`), invoked by `Upper.step` (`:554-555`).
- `Upper.stage-card-upper = ∈-induction step` (`:557-559`), and the
  induction descends into every member (`src/V/Hierarchy.lagda.md:
  177-180`).
- `Upper.branch` uses the IH at δ = ω and at every infinite member
  (`src/L/StageCardinal.lagda.md:545-553`); the finite members use
  `fin-inj` (`:544`).
- The `P δ` type has the premise `δ ∉ ω`, which is empty at finite δ
  (`:528-530`); there `P δ` is inhabited by absurdity and no `sq δ`
  application exists.

`Devlin55`'s second consumer is `CodeCount`'s `Bound α ordα α∉ω
(sq α α∉ω)` (`src/L/BoundedSubset.lagda.md:1426-1427`), again at the
site's own α.

The finite members never demand `sq` at any site. This is the
`[LJ-1.107]` case split restated at the demand level: the chain is
`ω` (pairing), initial ordinals (`Init`), non-initial ordinals
(unconstructible honest `sq`).

## 2. INIT AT THE DEMANDED ORDINALS (question 2)

**No, in general. `Init` holds at initial ordinals only.** The
demand set for a generic site includes non-initial ordinals, where
`Init` is refutable.

- `Init ω` is false: `Init`'s second conjunct is `ω ∈ ω`
  (`src/L/Ordinal/SquareLaw.lagda.md:692-698`), refuted by
  `∈-irrefl ω` (`src/V/Hierarchy.lagda.md:155`).
  Machine-checked: `Initω-false` (`src/ProbeLJ1116A.agda:62-63`,
  also `src/ProbeTowerInd2.agda:49-50`).
- `Init (sucV δ)` is false for every δ: the successor-closure clause
  at γ = δ demands `sucV δ ∈ sucV δ`, refuted by `∈-irrefl`.
  Machine-checked: `InitSuc-false`
  (`src/ProbeLJ1116A.agda:67-68`).
- Every infinite site's descent reaches ω or a successor. For the
  site ω itself, the demand is only ω. For any site above ω, the
  descent reaches ω, and a successor member for any site above a
  successor. So at every infinite site, some demanded ordinal has no
  `Init`. **MEASURED** at ω and at successors; the membership
  statement is **MEASURED by reading** (the descent reaches every
  member, section 1).
- `Init` is delivered where it holds: at the Hartogs cardinal
  (`initκ`, `src/ProbeLJ1106A.agda:573-574`) and at every initial
  ordinal (`InitialCase`, `src/ProbeLJ1107A.agda:464-537`).

The negative "`Init` holds at every demanded ordinal" is **MEASURED
FALSE** for every site: the demand set always contains ω, and `Init
ω` is machine-refuted.

## 3. STAGECARDINAL WITH INIT INSTEAD OF SQ (question 3)

**No. The consumer cannot supply `Init` at every α the induction
reaches, and at the site it cannot supply `Init ω` at all.**

- At the site α = ω: the only demand is `sq ω`, and `Init ω` is
  false. `via-col-square : (α : S) → Init α → sq α`
  (`src/L/Ordinal/SquareLaw.lagda.md:960-961`) cannot apply at ω.
  The pairing is the only honest supply. **MEASURED.**
- At a generic site: the descent reaches non-initial members where
  `Init` is refutable (section 2). The consumer would have to supply
  `Init δ` at those δ and cannot. **MEASURED** for ω and successors.
- The `[LJ-1.17-R]` alternative, the fixed-initial-target shape
  (`src/ProbeTowerInd2.agda:99-106`), takes `Init α` at the target
  only and does not descend per member. That shape is a different
  induction from the master's `Upper`, and it is a master rewrite.
  This brief forbids rewriting `StageCardinal` (C-39, section 6).

The answer to "could `StageCardinal` take `Init α` instead of `sq
α`": the parameter swap would make the site uninstantiable, because
`Init ω` is false and the site's only demand is `sq ω`. The honest
`sq ω` is the supply, not `Init`.

## 4. THE OMEGA-SITE MACHINE CHECK (question 4)

**Yes, the sq-dependent part of the site instance goes through with
`sq` demanded only at ω.** Machine-checked in
`src/ProbeLJ1116A.agda`, GREEN, one process at the C-12 cap:

| check | statement | where |
|---|---|---|
| the honest pairing at ω | `sqω : SQ.sq ω`, from `pairω`/`pairω-inj` | `:69-70` |
| the site's stage-card-upper | `up-ω : Up.stage-card-upper ω ω-ord (∈-irrefl ω)` | `:73-74` |
| the CodeCount-side count | `count-ω`, `Bound ω`'s `formula-bound` over `⟪ Lset ω ⟫` | `:80-83` |
| `Init ω` false | `Initω-false` | `:86-87` |
| `Init (sucV δ)` false | `InitSuc-false` | `:91-92` |

Whole-file warm re-check: **2.26 s** real at load 4.63 / 4.71 / 4.54,
four users, machine not quiet. The probe is 79 non-blank lines.
`scripts/lint-prose.py --check`, `scripts/lint-agda.py --check` and
`scripts/check-unbound-hyp.py` all exit 0 (section 10).

The full `BoundedSubsetAt` instance does not close today, but not
because of `sq`: `absorbs-subset` (`src/L/BoundedSubset.lagda.md:
1364-1366`), `levelIn` and `cover` (`:1408-1411`) are still
hypotheses. `[LJ-1.94]` records the same boundary
(`_build/lj-1.94-report.md` section 2). The sq-dependent part of the
site is what this dispatch measured, and it closes.

**The abort criterion's first branch fires for the site.** The
demand is only at ω, the honest `sq ω` exists, and the truncation
question dissolves for the site. The general module's demand set is
the second branch (section 1): every infinite ordinal below the site.

## 5. WHAT DEVLIN ASSUMES (LITERATURE)

Devlin 5.5 consumes `|L_α| = |α|` at the level α and the collapse γ
(`dev/literature/devlin-II5.md:154-156`). The equality is 1.1(vii),
proved by induction on α with the square law at the limit case
(`dev2.txt:200-222`). The tree formalizes it as `stage-card-upper`,
whose descent demands the pairing at every infinite level.

The 5.6 application is at the cardinal κ⁺ with α = κ
(`dev/literature/devlin-II5.md:164-166`). Both are cardinals, and
`[LJ-1.17-R]` records that the archived law's restriction to initial
ordinals reaches that consumer (`dev/ledger.toml:295-303`). That is
the classical site. The tree's concrete site is ω (section 0), a
different instantiation of the same module.

Two lines: **Devlin's 5.5/5.6 use the size equation at levels and
cardinals; the square law inside 1.1(vii) is used at every infinite
limit in the classical tower induction.** The literature does not
settle the tree's demand question, because the tree's module is
generic and its site is ω. The site does.

## 6. THE C-39 SECTION

One brief prohibition blocks a route, and the door is reported.

**"Do not rewrite `StageCardinal`"** blocks the fixed-initial-target
route: restructure `Upper` so the pairing is demanded only at the
target (`Init α`) instead of at every level of the descent
(`src/ProbeTowerInd2.agda:96-106` is the delivered shape). That
route would make `Init` the parameter at a cardinal site. It is a
master rewrite and the brief forbids it. The door: the ω-site finding
removes the need for the rewrite at the concrete site; a future
dispatch that instantiates at a cardinal site can price the
fixed-initial-target shape against this reading.

**"Do not touch `src/L/Condensation/`"** blocks importing
`L.BoundedSubset` for the exact `Devlin55` telescope, because
`L.BoundedSubset` imports `L.Condensation`
(`src/L/BoundedSubset.lagda.md:29`). The door: the probe imports
`L.StageCardinal` directly (its closure is Condensation-free,
verified by reading) and states the site shape locally. This is the
same door as `[LJ-1.106]` and `[LJ-1.107]`.

## 7. THE NEGATIVES AND THEIR STATUS

1. "At the concrete site α = ω, `sq` is demanded only at ω":
   **MEASURED** by reading at `file:line` (section 1) and by the
   GREEN omega-site instance (section 4).
2. "`sq ω` is honest": **MEASURED**. `sqω` checks
   (`src/ProbeLJ1116A.agda:69-70`), from `pairω`/`pairω-inj`
   (`src/ProbeLJ1106A.agda:127-137`).
3. "The sq-dependent part of the omega-site instance goes through":
   **MEASURED**. `up-ω` and `count-ω` check GREEN (section 4).
4. "For the generic `BoundedSubsetAt`, `sq δ` is demanded at every
   infinite δ ≤ α": **MEASURED** by reading at `file:line`
   (section 1). `sq` has exactly one use in `L.StageCardinal`, at
   `:281`, inside `limit-step`, reached at every infinite ordinal of
   the `∈-induction` descent.
5. "`Init` holds at every demanded ordinal": **MEASURED FALSE** for
   every site. The demand set always contains ω and `Init ω` is
   refuted (`src/ProbeLJ1116A.agda:86-87`); sites above ω also reach
   successors, refuted at `:91-92`.
6. "`StageCardinal` could take `Init` instead of `sq`": **MEASURED
   FALSE** at the site, where `Init ω` is false and the pairing is
   the only supply. The generic-module version of the swap is
   blocked by the same refutations at members.
7. "The whole `BoundedSubsetAt` instance closes": **INFERRED
   FALSE today** as a module instantiation: `absorbs-subset`,
   `levelIn` and `cover` are still hypotheses. The sq part is not
   the blocker; this dispatch measured that part only.
8. "The one-step unfolding equation `up-ω ≡ limit-step ω ...` closes":
   **WALLED**. The conversion check did not return. The isolated run
   was killed after 30 s with the import cache warm (load about
   4.6), and the first full-file run was killed after 510 s (cold,
   including the import compile). The check is not needed for the
   verdict; `up-ω` itself checks in 2.26 s.

## 8. DD4

The probe adds no shared code and changes no signature. The finding
is about where the consumer uses the generic parameter.

**Restricting the hypothesis would change what the J tower inherits.**
If `sq`'s parameter type were narrowed to a fixed site (ω only), the
J tower would inherit a fixed-site statement instead of the generic
one, and the two proofs would share less. The generic parameter stays
the shared surface: both towers instantiate it, and the honest supply
at the site is the ℕ pairing, which is tower-generic (no tower object
appears in `pairω`, `src/ProbeLJ1106A.agda:127-137`).

The J half is **INFERRED** (no J tower exists in this tree, same as
`[LJ-1.107]` section 7). A J consumer of the generic `Upper` would
face the same demand set: the pairing at every infinite level of the
descent. At the ω site, the demand is only `sq ω`, and the pairing
supplies it. The J tower inherits the same generic signatures
unchanged.

## 9. ARCHIVE USED

- `_build/lj-1.114-report.md`, read WHOLE. TOOK the wall, its
  measured cause (`src/ProbeLJ1114A.agda:89-94`), and the four closed
  alternatives. Did not repeat any of them.
- `src/ProbeLJ1114A.agda`, read WHOLE. TOOK the `pairω` usage pattern
  for the probe imports.
- `_build/lj-1.111-report.md` and `src/ProbeLJ1111A.agda`, read
  WHOLE. TOOK the truncated-chain result and the C-39 door at
  `L.BoundedSubset`.
- `_build/lj-1.107-report.md`, read WHOLE. TOOK the case split
  (ω / initial / non-initial) and the measured unconstructibility at
  non-initial ordinals.
- `_build/lj-1.106-report.md` and `src/ProbeLJ1106A.agda`, read
  WHOLE. TOOK `pairω`/`pairω-inj` (`:127-137`) and `initκ`
  (`:573-574`), reused by the probe.
- `_build/lj-1.94-report.md` and `src/ProbeLJ194A.agda`, read
  WHOLE. TOOK the site shape and the concrete instantiation
  (`:1202-1210`), the boundary at `BoundedSubsetAt`.
- `_build/lj-1.103-report.md`, read WHOLE. TOOK the finding that the
  consumer site runs at α = ω.
- `_build/lj-1.90-report.md` and `src/ProbeLJ190A.agda`, read WHOLE.
  TOOK the site origin (`Site0`, α = ω).
- `src/L/StageCardinal.lagda.md`, read WHOLE. TOOK the `sq`
  parameter (`:15`), `Bound` (`:62-180`), `LimitStep` (`:275-414`,
  `sq` at `:281`), `Upper` (`:496-559`), the branch's case split
  (`:532-553`).
- `src/L/BoundedSubset.lagda.md`, read `:1361-1627` (Devlin55 whole).
  TOOK `code-inj` (`:1529-1530`), `CodeCount`'s `Bound` (`:1426-1427`),
  the site telescope (`:1396-1407`), the remaining hypotheses
  (`:1364-1366`, `:1408-1411`).
- `src/L/Ordinal/SquareLaw.lagda.md`, read `:685-701` and `:938-964`.
  TOOK `Init` (`:692-698`) and `via-col-square` (`:960-961`).
- `src/ProbeTowerInd2.agda`, read WHOLE. TOOK the fixed-initial-target
  shape and `Initω-false` (`:49-50`).
- `dev/LESSONS.md`, read WHOLE D-30 (`:3332`), C-38 (`:3427`),
  C-39 (`:3521`), C-40 (`:3602`), C-36 (`:3284`), D-1 (`:1038`),
  D-8 (`:1377`), D-26 (`:1676`), P-l (`:2305`), P-x (`:3564`),
  C-35 (`:3200`), D-10 (`:1316`), D-29 (`:3242`), plus the `--for
  build` and `--for recon` bundles via `scripts/rules.py`.
- `dev/literature/devlin-II5.md`, read `:145-170`, `:270-300`,
  `:405-425`. TOOK 5.5's size-equation use, 5.6's site, and 1.1(vii)'s
  limit case.
- `dev/ledger.toml`, read `:260-310`. TOOK the `[LJ-1.17-R]`
  initial-ordinal note.
- `dev/PLAN.md`, read section 0 and the `LJ-1.90` to `LJ-1.114` rows.
  TOOK the site-at-ω record (`LJ-1.103` row).

## 10. GATES

`src/ProbeLJ1116A.agda`: GREEN at the C-12 cap, one process at a
time. Warm re-check 2.26 s at load 4.63 / 4.71 / 4.54, four users,
machine not quiet. 79 non-blank lines.

`scripts/lint-prose.py --check`: exit 0 on the probe and this report.
`scripts/lint-agda.py --check`: exit 0 on the probe.
`scripts/check-unbound-hyp.py src/ProbeLJ1116A.agda`: clean, exit 0.
`scripts/check-fences.py --check`: clean, 92 masters.
`scripts/ledger.py --brief`: standing 28,425 lines over 85 masters,
measured from HEAD.

Zero hits for `postulate`, `TERMINATING` and holes in the probe. `make
check` not run (forbidden). No master touched: `git diff` empty, `git
status` shows only the ignored probe and report. No process left
alive: every check returned or was killed and reported (section 7,
item 8). No commit, no push.

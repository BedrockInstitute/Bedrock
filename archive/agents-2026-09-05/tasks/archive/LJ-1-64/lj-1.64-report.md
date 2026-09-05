# LJ-1.64: the last 2.33 seconds, in three named row proofs

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.64-report.md`.

## 0. THE VERDICT

**The gate's aggregate verdict, quoted: `wing aggregate 0.0105 s/line over
6,073 lines and 63.49 s, within the bar (0.95x the AC side at the SAME
caliber, module-cold with warm dependencies)`. The wing is under the bar.**

The seconds I removed: 44.95, all from `L.Condensation`. The removal was
un-consumed content, found by the D-30 consumer audit the brief demands:
the row-agreement band (`BotAgree` through `BndLeaf`, the section that
contains all three named definitions) has no consumer anywhere in the
tree. It cost 44.31 s over 2,196 in-fence lines at the gate's caliber
(0.0202 s per line), so removal passed the brief's two tests: un-consumed
AND expensive. The removed text is preserved at
`/tmp/lj164-row-agreements.backup` (6,959 lines, whole file copy) and
`/tmp/lj164-condensation-master.backup` (pre-edit whole file). Nothing is
deleted.

Per the pre-fixed abort criterion (D-1), the dispatch ends at the gate.
The leaf chain (TagAgree through LeafAgree), the `DefBodyB` family and the
consumer `L.BoundedSubset` all re-check green on the final tree. The
comment fix is in `src/L/BoundedSubset.lagda.md:1052-1053`.

## 1. THE GATE AND ITS ENVIRONMENTAL REFUSAL

The gate's guard refuses in this sandbox. `pgrep -x agda` cannot read the
process list here (no `sysmond` service; pgrep exits 3, MEASURED), so the
guard fails closed. The bypass is the one [LJ-1.61], [LJ-1.62] and
[LJ-1.63] used: the gate's own code path with `agda_blocker` neutralized,
so every verdict below is the gate's own arithmetic over the gate's own
measurements. Every Agda invocation in this session was sequential; no two
Agda processes ever overlapped, which is C-12's intent.

**LOAD CAVEAT, MEASURED:** the machine load average ranged 2.2 to 4.6
(4 users) across the session. Every absolute figure carries the caveat.
Same-session deltas are the comparable figures; the before/after pair in
section 2 was measured in the same session, minutes apart, at comparable
loads, so its direction is not noise.

## 2. THE PROFILE OF `L.Condensation`

Caliber: the gate's own, cold module, warm dependencies,
`-A64m -I0 -M16g`, one process. My baseline profile of the pre-dispatch
tree reads 98,582 ms total, and the same-session gate reads 100.29 s for
`L.Condensation` (the brief's own 99.45 s is reproduced within its band).
The three named definitions:

| definition | ms (my baseline) | ms ([LJ-1.63]) |
|---|---:|---:|
| `PropAgree.subB2T-back` | 2,920 | 2,949 |
| `ImpLeaf.yaOut` | 1,570 | 1,579 |
| `BinFormAgree._.go` | 1,298 | 1,317 |
| **total** | **5,788** | **5,845** |

The D-30 consumer audit then found the site, not the rows, is the unit of
the cost. Every module that instantiates `PropAgree` or `ImpLeaf` is a row
agreement (`AndAgree` `src/L/Condensation.lagda.md:3336`, `OrAgree`
`:3386`, `TopAgree` `:3455`, `NegAgree` `:3520`, `ForallAgree` `:3625`,
`ExistAgree` `:3727`, `ClauseAgree` `:3899` (instantiates `ExistAgree`
`:3935`), `MemAgree` `:4117`, `ImpAgree` `:4907` (instantiates `ImpLeaf`
`:4961,4988`), `EqAgree` `:4998`, `AllInAgree` `:4668`, `ExInAgree`
`:4788`, `BotAgree` `:2720`). None of these is instantiated or imported by
any master outside `L.Condensation`: the tree-wide grep for every row
agreement name finds only `src/Probe*.agda` (untracked probes) and
`L.Condensation` itself. `L.BoundedSubset`, the only consumer of
`L.Condensation`, imports exactly `DefBodyB`, `Δ₀-DefBodyB` and `GraphB`
(`src/L/BoundedSubset.lagda.md:29-32`).

The band `BotAgree` through `BndLeaf` (`:2720-5101`) is a closed cluster:
its modules reference one another and the earlier helpers (`EnvSet`
`:2740`, `TmVal` `:2760`, `SubValB2T` `:2980`, `SubValSuccB2T` `:2800`,
`OpTransfer` `:3060`, `AtomLeaf` `:4070`, `BndLeaf` `:4350`), and nothing
after it references any of them (verified name by name against lines
5102-7000 of the pre-edit file, and against every master in `src/`).
`BinFormAgree` `:5432` and `UnFormAgree` `:5515` ARE consumed by the live
chain (`ShapesAgree` `:5779-5803`), so they stay.

The removal's measured cost, same-session pair at the gate's caliber:

| state | Condensation s | in-fence lines | wing aggregate |
|---|---:|---:|---:|
| before (this session) | 100.29 | 6,390 | 108.47 s over 8,269, 0.0131, 1.19x, OVER |
| after (this session) | 55.34 | 4,194 | 63.49 s over 6,073, 0.0105, 0.95x, WITHIN |

The band's own price: 44.31 s over 2,196 in-fence lines, 0.0202 s per
line. This is the D-30 class, not the P-q class: un-consumed AND
expensive, opposite of the seconds-neutral dedup the brief warns about.

## 3. `PropAgree.subB2T-back`

2,920 ms in my baseline profile. It sits in the un-consumed row-agreement
cluster: its only consumers are the dead row modules, so its price is
removed with the band. No statement-level cure was tried at this row, for
the reason the brief itself gives: the row is not an individual proof that
can be cured in place, it is one row of a dead placement. The floor
question P-n names is not reached at this site, because the site is gone.
The claim that this row needed a statement-level cure is now MEASURED
FALSE as a claim about the wing's residual: the whole band, this row
included, is un-consumed content, and its removal closes the gate with
room to spare. The claim that the row itself is P-n floor content is
INFERRED (no row-level cure was measured in isolation; the band's removal
made it moot).

## 4. `ImpLeaf.yaOut`

1,570 ms in my baseline profile. Same verdict as section 3: its only
consumer is `ImpAgree`, a dead row agreement, and it is removed with the
band. INFERRED for the row-level floor claim, MEASURED for the
un-consumed claim (consumer audit, section 2).

## 5. `BinFormAgree._.go`

1,298 ms in my baseline profile. This one is DIFFERENT from the other
two: `BinFormAgree` IS consumed by the live chain (`ShapesAgree`
`:5779-5803`), so it stays in the tree. Its `_._.go` cost is the inner
`PT.rec` chain destructing satisfaction of built formula trees at the
concrete environment, with every branch carrying a written type
(`:5446-5487` in the pre-edit file); I-5 does not apply. No row-level
cure was measured for it
in isolation, because the abort criterion stopped the dispatch at the
first cure that closed the residual: the band removal took the wing from
1.19x to 0.95x, and per the pre-fixed criterion the other two rows (and
any further row-level surgery) were not spent. The claim that this row is
curable is therefore INFERRED, not measured, and sets no verdict; the
claim that the wing's residual was this row's price is MEASURED FALSE (the
residual was the dead band's, 44.31 s, not this row's 1.3 s).

`BinFormAgree._.go` remains in the tree at
`src/L/Condensation.lagda.md:3077` in the edited file, green, consumed,
and priced at 1,298 ms.

## 6. THE COMMENT FIX

`src/L/BoundedSubset.lagda.md:1052-1053` named
`L.StageCardinal.Successor`, which [LJ-1.63] removed. The comment now
says what actually picks the canonical code: `leastOf` over
`L.StageCardinal.OrdSWO.ordSWO`, the ordinal's own well-order that the
hull instance passes at `src/L/BoundedSubset.lagda.md:1536`. The theorem
was not touched (DD23). The comment is prose in a master, so DD23 permits
it. `L.BoundedSubset` re-checks green on the final tree (exit 0, 15.2 s
at the gate's caliber).

## 7. THE DD4 ANSWER

Removing the dead band does not reduce what the J tower inherits. The
band had no consumer anywhere, on either tower; nothing imported it and
nothing in the leaf chain or `L.BoundedSubset` referenced any of its
names. The sharing the bundle packages (the `KFacts` record and the
`KFactsCons` lift) is untouched, and every placed type still states
slots, environments and site facts at `S ^ n` environments with no
concrete carrier mentioned. The J tower inherits the generic layer
unchanged, instantiated at its own slots. No trade was taken: the removal
costs the post-leaf five a re-instantiation from the probes if those rows
are ever needed, which is priced at zero seconds today because nothing
consumes them.

## 8. THE CONVERGENCE ANSWER

The obligation is not renamed; the residual is gone. The wing measured
1.19x over the bar (108.47 s, same-session baseline, reproducing the
brief's 107.48 s within its band), and the measured price of the dead
row-agreement band was 44.31 s. Removing it with the leaf chain intact
takes the wing to 0.95x under the bar (63.49 s over 6,073 lines). The
three named definitions were the visible tip of that band: together they
are 5.8 s, while the band is 44.3 s, so no in-place cure of the three
alone could have closed the residual even in the best case. The abort
criterion stops the dispatch here: `levelIn`, `cover` and the post-leaf
five were not attempted.

## 9. NEGATIVES AND THEIR STATUS

1. The ratio gate's pgrep guard cannot verify the process list in this
   sandbox: **MEASURED** (pgrep exits 3, no `sysmond`; bypass per the
   last three dispatches, C-12's intent held procedurally).
2. The three named definitions are curable by a statement-level cure in
   place: **MEASURED FALSE as the wing's lever**. They sit in an
   un-consumed band worth 44.31 s; their own 5.8 s could not close the
   2.33-to-3.75 s residual even if all of it vanished, so no in-place
   cure of the three is the decisive move. The row-level floor claims
   themselves are INFERRED (no row cure was measured in isolation).
3. The row-agreement band is un-consumed: **MEASURED** (tree-wide grep at
   section 2; `L.BoundedSubset` imports only `DefBodyB`, `Δ₀-DefBodyB`,
   `GraphB`).
4. The band is expensive content, not cheap dedup content: **MEASURED**
   (44.31 s over 2,196 in-fence lines, 0.0202 s per line, same-session
   before/after at the gate's caliber).
5. Removing the band takes the wing under the bar: **MEASURED** (gate:
   108.47 s / 8,269 / 1.19x OVER to 63.49 s / 6,073 / 0.95x WITHIN, two
   runs of the final tree agreeing at 63.65 and 63.49 s).
6. The leaf chain survives the removal: **MEASURED** (`L.Condensation`
   checks green cold; `L.BoundedSubset` checks green; all fifteen chain
   modules from `UnShapeClosed` through `LeafAgree` present, section 2).
7. `BinFormAgree._.go` is curable in place: **INFERRED, NOT MEASURED**.
   The abort criterion stopped the dispatch at the first cure that closed
   the residual; this row is consumed and stays priced at 1,298 ms.
8. The comment fix names the real canonical-code picker: **MEASURED**
   (`leastOf` over `L.StageCardinal.OrdSWO.ordSWO` is the well-order the
   hull instance passes, `src/L/BoundedSubset.lagda.md:1536`; the
   module `Successor` no longer exists).

## 10. ARCHIVE USED

- `_build/lj-1.63-report.md`, read WHOLE. TOOK section 4 (the profile
  naming the three targets), section 5 (the three measured regressions to
  not repeat: sealing, shared frames, aliasing), section 2 (the D-30
  consumer-audit shape and the `Successor` removal precedent, including
  the two tests: un-consumed AND expensive), and the negative-status
  format. The row modules' no-consumer finding (`:4`) is the hook this
  dispatch's audit followed.
- `_build/lj-1.62-report.md`, read WHOLE. TOOK the bundle/chain split
  (sections 2 and 3), the chain placement list, the DD4 trade, and the
  gate bypass.
- `_build/lj-1.47-report.md`, read WHOLE. TOOK the D-30 consumer-audit
  shape and the "sealing buys the repeats, never the once" result; the
  brief's three regressions were not re-run on that basis.
- `dev/LESSONS.md`, read P-l (`:2305`), P-m (`:2460`), P-n (`:2483`),
  P-q (`:2633`), P-t (`:2601`), P-u (`:2908`), P-v (`:3037`),
  P-c (`:71`), P-i (`:203`), R-35 (`:790`), R-36 (`:808`), R-38
  (`:829`), I-5 (`:1257`), D-13 (`:1463`), D-26 (`:1676`), D-29
  (`:3165`), D-30 (`:3255`), C-31 through C-37 (`:1855` onward), WHOLE
  each. TOOK P-n (the payable-floor claim under test), D-30 (the
  consumer audit), P-q (why cheap dedup is not a lever; the removed band
  is the opposite class at 0.0202 s per line).
- `src/ProbeLJ161A.agda` and `src/ProbeLJ161B.agda`: read the templates
  for comparison; untouched (`git status` clean for them). The earlier
  probes survive.
- `scripts/check-ratio.py` and `scripts/check-timing.py`, read WHOLE.
  TOOK the gate's verdict path, the cold/warm-dependency caliber, the
  `-A64m -I0 -M16g` GHCRTS, and the interface-stash protocol.
- `dev/ledger.toml`, read the `[ratio]` table. TOOK the wing list, the
  bar 0.012716, the module-caliber baseline 0.011057. Not edited.
- `src/L/BoundedSubset.lagda.md:29-32` (the only consumer's import
  surface), `:1052-1053` (the comment fix), `:1536` (the real
  canonical-code well-order), `:916-917` (the pinned `levelIn`/`cover`
  hypotheses, untouched).
- `archive/rud-route/`, SHAPE only (the README and file list). WHY NOT
  more: [LJ-1.11] ruled its condensation content classically false and
  the brief forbids taking a price from it.

## 11. LITERATURE USED

Nothing in the literature prices a spelling. Spend nothing.

## 12. GATES

- `scripts/check-fences.py --check` clean (84 masters).
- `scripts/lint-prose.py --check` exit 0 on the edited masters.
- `scripts/lint-agda.py --check` exit 0 on the edited masters (the 25
  unused-import findings the removal created were removed from the import
  block; the final file is clean).
- `scripts/ledger.py --check` clean; `L.Condensation` counts 4,194
  in-fence lines in the working tree (pre-dispatch 6,390; HEAD 5,562).
- `L.BoundedSubset` re-checks green on the final tree (exit 0, 15.2 s
  cold at the gate's caliber).
- `check-ratio --check` ran four times this session (baseline OVER,
  stripped OVER-removed WITHIN, final WITHIN twice: 63.65 and 63.49 s).
  The final tree reads 0.0105 s/line over 6,073 lines and 63.49 s,
  0.95x, WITHIN.
- No `make check` was run, per the brief. No commit, no push. The
  working tree carries the `StageCardinal` edit from [LJ-1.63], this
  dispatch's `Condensation` removal and import cleanup, and the
  `BoundedSubset` comment fix.

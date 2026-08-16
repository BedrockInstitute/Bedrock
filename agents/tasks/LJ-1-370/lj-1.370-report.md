# LJ-1.370 Report: retire `meet-suc`, on `[LJ-1.364]`'s fable ruling

Status: COMPLETE. Written early per C-22 and filled incrementally.

## Verdict

**RETIRES GREEN, at a real line delta of exactly 3 in-fence non-blank lines
(`src/L/Choice/Stage.lagda.md` counted 149 at HEAD, 146 after the edit),
which MATCHES the ruling's 3.** Physical delta: Stage minus 5 lines, Step
minus 1 line, `dev/ARCHIVE.md` plus 35. No consumer appeared. No abort
criterion fired. Both edited masters typecheck green (timings below, with
the empty-file floor beside them).

## Premises, re-derived before any edit (C-44)

1. **`meet-suc` has no code consumer. VERIFIED, MEASURED.** Grep over
   `src/` finds the token only in its own definition (pre-edit
   `src/L/Choice/Stage.lagda.md:277-279`) and in prose. `src/L/Choice/Step.lagda.md:55`
   imports `IsPredOf; predOf; carveAt` from `L.Choice.Stage` and nothing
   else. The structural-inability record the ruling cited stands in the
   edited paragraph (`src/L/Choice/Step.lagda.md:100` post-edit, lesson
   retained).
2. **`carveMeets` is consumed and stays. VERIFIED, MEASURED.** `thePred`
   applies it; pre-edit at `src/L/Choice/Stage.lagda.md:301`, post-edit at
   `:296` after the fence above it shrank. Its definition is untouched at
   `:271-272`.
3. **`defStage-suc` exports the successor fact. VERIFIED.** Pre-edit
   `src/L/Choice/Stage.lagda.md:313-315`, post-edit `:308-310`:
   `sucV (defStage u pu h) ≡ μ u pu h`. The chapter itself consumes it at
   `:327` (`Lset-μ`'s rewrite).
4. **"The edit sites are four, and the saving is three lines." REFUTED on
   the count, VERIFIED on the saving.** The saving is exactly 3, MEASURED
   (149 to 146). The sites are NOT four. The ruling's own grep missed a
   FIFTH site: the chapter summary named `meet-suc` in both languages, at
   pre-edit `src/L/Choice/Stage.lagda.md:389` (EN) and `:407` (ZH). MEASURED:
   `git log` shows Stage last changed in `9ddb44d` (`[LJ-1.342]`), before the
   ruling ran, so the summary was present when the ruling grepped and was
   missed by its count. This is the ruling's fourth error, in the direction
   the brief predicted. Also corrected: the catalogue lines are at
   `src/Everything.lagda.md:668` and `:998` today, not `:667` and `:997`
   (MEASURED; Everything last changed in HEAD `9ae4b04`, after the ruling
   measured; INFERRED cause: an insertion above the site in that commit).

## Edit sites and what was struck (six strikes, pure subtraction)

1. `src/L/Choice/Stage.lagda.md` section prose, EN, pre-edit `:265-266`.
   Struck the whole final sentence: "`meet-suc`{.Agda} then states the
   conclusion in the shape this chapter has always exported it in." This is
   the sunk-cost warrant the ruling quoted. The paragraph keeps the
   `carveMeets` explanation, which stays true and needed.
2. Same paragraph, ZH, pre-edit `:268`. Struck 「随后 `meet-suc`{.Agda}
   把结论陈述成本章一贯导出的那个形状。」 whole.
3. The fence, pre-edit `:276-279`. Struck the blank line and the three code
   lines. The fence now holds `carveMeets` alone.
4. Chapter summary, EN, pre-edit `:389`. Struck the attribution
   "`meet-suc`{.Agda} says" only. The successor claim and the carve reason
   stay, unattributed, because `defStage-suc` states the fact. Post-edit
   `:384`.
5. Chapter summary, ZH, pre-edit `:407`. Struck 「而 `meet-suc`{.Agda} 说」.
   Post-edit `:402`.
6. `src/L/Choice/Step.lagda.md:100-101` EN and `:112` ZH, pre-edit. Struck
   the mechanism clause "`meet-suc`{.Agda} asks for a cell that is met, and a
   single set cannot supply one, so" and its ZH counterpart
   「`meet-suc`{.Agda} 要的是一个被相交的格，而单个集合供不出来，故」.
   Kept the lesson tail: "the reuse it named was never available until the
   argument itself was written over the property." Post-edit `:100` and
   `:111`.

**Care point, flagged for audit.** The ruling said "strike the name, keep
the lesson" for Step. A name-only strike cannot parse in English: "asks for
a cell that is met" loses its subject. So the mechanism clause went with
the name, and the lesson's conclusion survives without it. DD23 was read as
forbidding composition, and no word was added anywhere.

**Left in place, with the ruling's own warrant.** The section heading "A
first appearance is a successor" / 「首次现身处是后继」. `[LJ-1.364]` ruled
"nothing becomes false either way, because `defStage-suc` still states the
successor fact at `μ`" and left the move to the lander. The lander leaves
it: the section holds `carveMeets`, and moving a heading writes prose.

No paragraph was left saying nothing. Nothing was composed. `grep -rn
"meet-suc" src/` now returns exactly the two catalogue lines the
orchestrator owns.

## The two `src/Everything.lagda.md` edits for the orchestrator

1. EN, `:668-669`. Strike "`meet-suc`{.Agda} makes that stage a
   **successor**, because a set enters the tower only by being carved out of
   the stage below, and " so the sentence reads "…sealed like
   `stage`{.Agda}; `defStage`{.Agda} is the stage it succeeds, a function
   because a successor determines what it succeeds among ordinals
   (`ord-suc-inj`{.Agda}). …" A name-only strike leaves "makes" with no
   subject, so the whole clause goes; the successor fact survives the same
   sentence through `defStage` and `ord-suc-inj`.
2. ZH, `:998`. Strike 「`meet-suc`{.Agda} 使那个阶段成为**后继**，因为集合进入塔的唯一途径是从它下面那个阶段中被雕出，而」
   leaving 「…按 `stage`{.Agda} 那样封印；`defStage`{.Agda} 是它所后继的那个阶段，…」.

## The archive row

**Ruling: no archive module file, and the honest answer is the one the
brief allowed.** `meet-suc` is a three-line fragment inside a LIVE master,
so it has no path of its own to move, and an archive copy would freeze a
slice of a living chapter. The record is a SECTION of `dev/ARCHIVE.md`
("The retirement of `meet-suc`, 2026-08-16", at `dev/ARCHIVE.md:120`),
following the registry's own non-module precedent (`archive/probes/`, and
the "What this registry does NOT index" clause). The section carries every
column the registry demands: the three lines verbatim, the ruling and why
it left, last green (`9ddb44d` through HEAD `9ae4b04`), what it did right
FROM MEASUREMENT (after `[LJ-1.342]` wrote `carveAt`/`predOf` generically,
the whole statement at an arbitrary least stage cost exactly three lines:
the DD4 re-instantiation price, measured), and the reopen condition in the
ruling's own words: re-instantiation costs the same three lines if ever
wanted. `[LJ-1.364]` itself wrote "a three-line fragment's archive is the
deletion commit and this record."

## DD4, stated and answered (C-46)

**DD4: maximize the code the two proofs share, and write it generic.** The
axis is AC against GCH, fixed at `scripts/measure/ledger.py:50`, roots
`src/L/Model.lagda.md` and `src/L/GCH.lagda.md`.

**`L.Choice.Stage` is in the AC closure AND in the shared set.** MEASURED
today by running `[LJ-1.364]`'s own probe
(`agents/tasks/LJ-1-364/probe-closure-membership.py`, which calls the
ledger's `import_graph` and `closure`): 43 shared masters, and
`src/L/Choice/Stage.lagda.md` is listed in the shared set.

**This retirement shrinks BOTH wings, by the same 3 lines.** Before, at
HEAD: AC 73 masters 17,186 lines; GCH 48 masters 8,878; SHARED 43 masters
7,585. After commit: AC 17,183; GCH 8,875; SHARED 7,582. The after-figures
are INFERRED arithmetic, not a fresh scan, and here is why: the ledger
reads `git show HEAD:` (its own comment at
`scripts/measure/ledger.py:433`), my edits are uncommitted by constraint,
so `--reuse` cannot see them. The inputs are all measured: the closure
membership is unchanged (no import was touched), the deletion is 3 lines,
and Stage is shared. This is the different DD4 fact: a shared-set
retirement, both wings down together.

**The DD4 asset survives intact:** the generic argument (`carveAt`,
`predOf`, 29 shared lines at both ends) stays, and re-instantiation stays
nearly free, which is what makes this retirement safe rather than a loss.

## ARCHIVE USED (DD18, all four corpora)

- **`archive/src/2026-08-09-rud-route/`: CITED, read.** The retired route
  HAD a first-appearance successor lemma, the same name and a bigger body:
  `archive/src/2026-08-09-rud-route/L/Choice/Stage.lagda.md:181`, quote:
  "meet-suc : (u σ : S) → IsOrd σ → ⟨ meets u σ ⟩ → isLeastOrd (meets u) σ",
  with the carve walked inline in a `where` clause below it. What became of
  it: it was consumed by that route's own `thePred` at
  `archive/src/2026-08-09-rud-route/L/Choice/Stage.lagda.md:258`, quote:
  "(meet-suc u (μ u pu h) (μ-ord u pu h) (μ-meets u pu h) (μ-earliest u pu h))",
  and it was archived with the route in the 2026-08-09 archival, never
  deleted.
  TOOK: the closest comparable. In the old route the lemma was LOAD-BEARING
  (one code consumer); `[LJ-1.342]`'s generic rewrite moved the load to
  `predOf ∘ carveMeets` directly, which is why the same name could retire
  with zero consumers today. This is also the measured fact in the archive
  row's "did right" column.
- **`archive/dev/TASKS-archived.md`: DECLINED, searched, shape taken.**
  MEASURED: grep for "meet-suc", "first appear", "successor lemma", "L2.4"
  and case-insensitive "stage" returns ZERO rows; the retired route's
  dispatches never priced its stage lemma under that vocabulary. Quote of a
  row read while searching, `:243`: "Make the limit clause carrier-generic,
  as the successor clause already is". WHY NOT: no analogue price exists to
  transfer (P-l would refuse it anyway).
- **`archive/dev/DECISIONS-archived.md`: CITED, read the D17, D20 and D21
  rows.** Quote, `:42` (D20): "Retired code is archived, never deleted."
  TOOK: the regime this retirement executes under, and D17 at `:39`, the
  rewrite-side frame DD13 absorbed.
- **`archive/dev/JOURNAL-archived.md`: DECLINED.** MEASURED: grep for
  "meet-suc" returns zero rows. WHY NOT, one line: its rows price the
  retired route's walls and failures, not a three-line corollary's
  retirement. Quote of a line read while checking, `:133`: "`opaque` does
  not cure it, the third genuinely different failure". Nothing bears on
  this task.

## LITERATURE USED (DD18)

- **`dev/literature/j-hierarchy.md`: read `:45-71`, quote `:58-59`:** "It
  is easy to see that there is only a finite jump in rank from S_α^A to
  S_{α+1}^A." VERIFIED, and the ruling's reading holds: the orthodox text
  carries the successor step as a two-line remark folded into the hierarchy
  presentation itself, and exports no standalone successor-stage lemma.
  Assessment as asked: this SUPPORTS the retirement, more than it merely
  fails to oppose it, on exactly one half. The half it supports is "no
  orthodox consumer of this interface is coming": first-appearance
  bookkeeping lives inside the level and rank definitions, so the
  interface's promised consumer class does not exist in the literature. The
  half it cannot support is the price, which was never a literature
  question: the zero rewrite price rests on the tree, measured by
  `[LJ-1.364]` and re-derived above. WHY NOT for the rest of the file: the
  J-structure and Σ1 sections bear on condensation, not on a stage export.

## Checks and timings

- `scripts/site/weave-i18n.py --check`: exit 0.
- `scripts/gate/lint-prose.py --check` on the three files written
  (`Stage`, `Step`, `dev/ARCHIVE.md`): exit 0. No em dash anywhere.
- `scripts/gate/lint-agda.py --check`: exit 0.
- Agda, all runs `GHCRTS="-A64m -I0 -M8g"`, cap never raised, slot count 0
  before every invocation (cap 2, the brief's exact command):
  `L.Choice.Stage` green, 1.764 s. `L.Choice.Step` green, 3.096 s.
  Empty-file floor (`agents/tasks/LJ-1-370/floor.agda`, module header only):
  0.253 s. So each figure sits above its floor by under two seconds; these
  are warm-cache checks of the edited modules against HEAD's interfaces,
  and the cold gate is the orchestrator's `make check`. No heap exhaustion.

## Constraints compliance

Writes: `src/L/Choice/Stage.lagda.md`, `src/L/Choice/Step.lagda.md`,
`dev/ARCHIVE.md`, `agents/tasks/LJ-1-370/` only. `src/Everything.lagda.md`
untouched; its two edits are prescribed above. `dev/PLAN.md` untouched (it
was already modified in the working tree by the orchestrator and I left it
as found). No commit, no push, no `make check`, no `git checkout`, `stash`,
`reset` or `clean`. No `[LJ-1.371]` collision: that task writes only under
`agents/tasks/LJ-1-371/`. `rules.py --for build` read in full before work,
and the full entries opened for every law acted on (DD13, DD18, DD23, DD4,
C-44, C-53, C-12, C-22, D-1). The floor file is declared here and lives
beside this report.

## Negatives, classified

- MEASURED: no code consumer of `meet-suc` anywhere in `src/`.
- MEASURED: `carveMeets` has a live consumer, so it stays.
- MEASURED: the saving is exactly 3 in-fence lines (149 to 146).
- MEASURED: the ruling's site count was wrong; a fifth prose site existed
  at Stage `:389`/`:407` pre-edit, and the catalogue sites sit at
  `:668`/`:998`, not `:667`/`:997`.
- MEASURED: `archive/dev/TASKS-archived.md` has zero rows for the retired
  route's stage machinery under every trigger tried.
- INFERRED: the after-commit closure figures are arithmetic on measured
  inputs, because the ledger reads HEAD and the edits are uncommitted.
- INFERRED: the one-line catalogue drift is attributed to HEAD's own commit
  touching `Everything.lagda.md` above the site.

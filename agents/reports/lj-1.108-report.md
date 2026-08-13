# LJ-1.108 report: delete the unused refuted hypotheses from the remaining rows

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.108-report.md`.

## 0. Verdict

**ALL NINE ROWS LOST THEIR REFUTED HYPOTHESES, and the master is
GREEN, MEASURED.** `src/L/Condensation.lagda.md` typechecks, exit 0,
one process at the C-12 cap, both after-runs. BEFORE: 139.8 s cold
at load 5.49 start (4 users). AFTER: 148.4 s cold at load 4.25 start
and 147.9 s cold at load 3.95 start (4 users). Lines by
check-timing's own counter: 6445 before, 6433 after (-12 non-blank
in-fence). Raw diff: +44 / -54 (-10).

The projected delta was +2 to +4 s ([LJ-1.105] section 2). Measured
is +8.1 to +8.6 s. The same tree measured a run-to-run spread of
8.2 s in [LJ-1.105] (140.5 s at load 7.07 against 148.7 s at load
4.34), so the lower bound of the true delta is not pinned; the
likely driver of the upper end is the BndLeaf `keyK-of` re-elaboration
at its four use sites (P-w: the copy is paid at use), in rows whose
`back`s were already the hottest definitions.

## 1. Per-row table

`entryK` and `arSubK` are deleted from all nine telescopes.
`tmKeyK` is deleted from EqAgree, AllInAgree and ExInAgree. No row
failed; no use of a deleted hypothesis remains inside the master.

| row | `entryK` | `arSubK` | `tmKeyK` | BndLeaf port |
|---|---|---|---|---|
| TopAgree (`:3613`) | deleted | deleted | - | - |
| NegAgree (`:3678`) | deleted | deleted | - | - |
| ForallAgree (`:3782`) | deleted | deleted | - | - |
| ExistAgree (`:3883`) | deleted | deleted | - | - |
| EqAgree (`:5232`) | deleted | deleted | deleted | - |
| AllInAgree (`:4903`) | deleted | deleted | deleted | `keyK-of` used |
| ExInAgree (`:5022`) | deleted | deleted | deleted | `keyK-of` used |
| ImpAgree (`:5140`) | deleted | deleted | - | - |
| ClauseAgree (`:4054`) | deleted | deleted | - | - |

The ClauseAgree application of ExistAgree (`:4090`) drops the two
deleted arguments; the row's out/back are otherwise unchanged.

## 1b. Hypotheses added, and their suppliers

Two hypotheses were added to BndLeaf's telescope; nothing else was
added. The rule's test: each must be one the consumer can supply.

| hypothesis | where | supplier |
|---|---|---|
| BndLeaf `arityK` | `src/L/Condensation.lagda.md:4697-4699` | **SUPPLIED.** A `KFacts` field in the exact shape; each row telescope holds it and passes it (`AllInAgree` `:4910-4912` telescope, applications `:4973-4974` and `:5004-5005`) |
| BndLeaf `aK` | `:4700` | **SUPPLIED.** In `AllInAgree.out`/`ExInAgree.out` by the clause binder `a aK`; in `back` by `(arK , (aK , bK)) = codesK c ar a b c∈ shEq` (`:4993`, ExIn `:5112`). The same shape AtomLeaf consumes |

`keyK-of` (`:4741-4774`) is a derivation, not a hypothesis. It is
MEASURED inhabited: the master elaborates it at four BndLeaf
instantiations (`:4973-4974`, `:5004-5005`, `:5092-5093`,
`:5123-5124`), each through `tmIn`'s key lambda (`:4834`).

## 2. Remaining-occurrence list for the eleven refuted names

The grep covers `src/L/Condensation.lagda.md` only, as briefed.
`used` means the name is consumed by a term in the master.

| name | occurrences in the master | status |
|---|---|---|
| `tmKeyK` | `:4145`, `:4738` | two prose comments only; no code occurrence remains |
| `entryK` | `:2770`, `:2875`, `:2892` (comments); `:2860`, `:2864`, `:2896`, `:2899` (ChainZ/EnvSet DERIVED tied form); `:2941-2980` (uses of the derived form inside EnvSet) | the EnvSet/ChainZ forms are the tied derivations with the `z ∈ K` premise, supplied by `arityK`; used. The row-hypothesis form is gone |
| `entryK` (unrelated family) | `:6247`, `:6261`, `:6270`, `:6284`, `:6303`, `:6310-6313`, `:6355`, `:6370`, `:6382-6383`, `:6431`, `:6450`, `:6477` | a DIFFERENT family: `entryK` over the C slot in OneSuccRel/SuccSndRel/SatGraph machinery, used; not one of the refuted K-slot shapes and never part of this repair |
| `arSubK-mem` | none | frame name only (TwelveAgree, consumers) |
| `arSubK-neg` | none | frame name only |
| `arSubK-top` | none | frame name only |
| `arSubK-imp` | none | frame name only |
| `keyK-neg` | none | frame name only |
| `succK` | `:3166`, `:3193` (SubValSuccB2T hypotheses, used); `:3796`, `:3838`, `:3871` (ForallAgree); `:3897`, `:4011`, `:4040` (ExistAgree); `:4068`, `:4090` (ClauseAgree); `:4920`, `:4982`, `:5013` (AllInAgree); `:5039`, `:5101`, `:5132` (ExInAgree) | row hypotheses of the key-fact family, USED (passed to SubValSuccB2T or to ExistAgree). NOT part of this repair: the key-fact family is priced in [LJ-1.99], and [LJ-1.105] section 2 records it as separate |
| `keyK-un` | none | frame name only |
| `succK-allin` | none | frame name only |
| `keyK-allin` | none | frame name only |

The honest state: the nine-row repair is complete. The rows still
state `succK` and `keyK` (used, key-fact family), and the frame's
untied `succK`/`keyK-un`/`keyK-neg`/`succK-allin`/`keyK-allin` are
refuted at the frame (`src/ProbeLJ197A.agda:136-137`, `:151-152`,
`:171-172`, `:186-187`, `:204-205`); their tied forms were measured
supplyable at the rows' binders in [LJ-1.99]. That repair is not
this dispatch.

## 3. Rows that could not lose a hypothesis

None. All nine rows lost their refuted hypotheses. The abort
criterion's count of failed rows is zero.

## 4. C-39 section

One brief line blocked a route I could see. "Do not touch
`src/L/Condensation/`" blocked updating the consumers
`src/L/Condensation/UpperAgree.lagda.md` and
`src/L/Condensation/LowerAgree.lagda.md`, whose row applications
still pass `entryK`, `arSubK-*` and `tmKeyK`
(`UpperAgree.lagda.md:175-180`, `:194-214`;
`LowerAgree.lagda.md:195-228`). The route was already blocked before
this dispatch: those applications also lack the `arityK` argument
`[LJ-1.105]` added, so they were red before my edit and stay red
after it. `[LJ-1.105]` section 6 item 7 records the same inference.
The unblocked route is the frame dispatch, which the orchestrator
plans next. The prohibition costs nothing this dispatch.

No other brief line blocked a route. No wall occurred; the heap cap
was never a constraint.

## 5. Negatives classified

1. All nine rows lost their refuted hypotheses: **MEASURED TRUE** by
   the diff (the deleted lines are exactly the stated hypotheses;
   no other code changed).
2. The master is green after the edit: **MEASURED TRUE**, exit 0,
   two cold runs, 148.4 s and 147.9 s.
3. No use of a deleted hypothesis remains in the master:
   **MEASURED TRUE** by grep (section 2); the only surviving names
   are EnvSet's derived tied forms, an unrelated C-slot family, and
   comments.
4. The master's cold seconds changed: **MEASURED TRUE**, 139.8 s
   before at load 5.49 to 147.9-148.4 s after at loads 3.95-4.25.
   The delta's lower bound is not pinned: [LJ-1.105] measured an
   8.2 s spread on the same tree's content.
5. The consumers under `src/L/Condensation/` do not typecheck and
   need the frame update: **INFERRED** from their applications'
   arity (they pass `entryK arSubK-*` where the rows no longer take
   them, and they lack `arityK`); not measured by a typecheck run,
   out of scope.
6. The rows' remaining `succK`/`keyK` hypotheses are refuted in
   their untied form at the row frame: **INFERRED**. The probe
   refutes the FRAME shapes (with `N` quantified) only; the row
   shapes fix the slots as parameters. The family is out of scope
   and its tied forms were MEASURED supplyable in [LJ-1.99].
7. The BndLeaf `keyK-of` port is correct at the allin layout:
   **MEASURED TRUE**, the master elaborates it at four use sites
   with the code slot at position 6 (`a`) and `aK` as its
   membership.

## 6. DD4 answer

Net lines: -12 non-blank in-fence by the same instrument as the
seconds (6445 to 6433); -10 raw. The deletions collect the saving
`[LJ-1.105]` left in the telescopes; the additions are the single
`BndLeaf` derivation that replaces the refuted `tmKeyK`.

**The `BndLeaf` `keyK-of` should live in one place rather than
two.** The AtomLeaf derivation (`:4148-4176`) and the BndLeaf copy
(`:4741-4774`) are the same derivation: same ChainZ lemmas, same
tagAtL adequacy, same pair equalities, same slot numerals (code at
slot 6, tag at `suc c`). The only differences are the frame's
environment spelling and an unused `v` binder in the AtomLeaf
signature. A generic derivation parameterized by the environment
would serve both leaves (P-h's module-parameter shape). Measured
caveat: seconds are paid at use (P-w), so one shared copy saves
about 35 lines and nothing at the wall gate; the four BndLeaf sites
pay their elaboration either way. I did not make the move: the
brief scoped this dispatch to the port, and the shared form is a
follow-up.

The `[LJ-1.105]` DD4 move (one derivation inside EnvSet instead of
nine copies) is now collected: the nine rows no longer state
`entryK` or `arSubK` at all.

## 7. Measurements

Cold seconds (check-timing protocol: module interface moved aside,
one process at a time, `GHCRTS=-M8g`):

| run | seconds | load average at start | users |
|---|---:|---:|---|
| before (`20f5704`) | 139.8 | 5.49 | 4 |
| after, run 1 | 148.4 | 4.25 | 4 |
| after, run 2 | 147.9 | 3.95 | 4 |

Delta: +8.1 to +8.6 s. Lines: 6445 before to 6433 after (-12) by
check-timing's in-fence counter; `git diff` +44/-54 raw. No agda
process was running before the after-runs (`pgrep agda` count 0),
and the sibling's slot was not touched.

`scripts/lint-prose.py --check`, `scripts/lint-agda.py --check` and
`scripts/check-fences.py --check` pass on the edited master;
check-fences reports 87 masters. `scripts/ledger.py --brief`
measures from HEAD, so it still reports standing 28,373 lines over
85 masters (the uncommitted edit is not counted).

No probe was written. The decisive check for this dispatch is the
master itself: it elaborates the new `BndLeaf` derivation at four
instantiation sites and all nine rows with their reduced telescopes
(C-35: the use sites are the audit). A standalone
`src/ProbeLJ1108*.agda` would duplicate that measurement and add no
verdict.

## ARCHIVE USED

- `_build/lj-1.105-report.md`, read WHOLE. TOOK the work list and
  the prices (section 2), the hypothesis-supply table (section 3),
  and the consumers' out-of-scope state (section 6 item 7).
- `src/ProbeLJ1104A.agda`, read WHOLE, and
  `_build/lj-1.104-report.md`, read WHOLE. TOOK the `keyK-of`
  derivation shape (`ProbeLJ1104A.agda:405-427`) and the `keyValK`
  refutation (`:118-120`), which the BndLeaf port mirrors.
- `src/ProbeLJ197A.agda`, read WHOLE. TOOK the refutations of the
  frame shapes (`:136-137`, `:151-152`, `:171-172`, `:186-187`,
  `:204-205`, `:239-240`, `:251-254`).
- `src/ProbeLJ195A.agda`, read WHOLE. TOOK the `tmKeyK` refutation
  (`:45-48` in the file's `tmKeyK-refutes`).
- `_build/lj-1.99-report.md`, read WHOLE. TOOK the site-supply
  table for the key-fact family (section 1's table), which is NOT
  part of this repair.
- `dev/LESSONS.md`, C-38 as extended (`:3427-3511`), C-39
  (`:3513-end`), C-35 (`:3200-3242`), C-36 (`:3284-3332`), D-29
  (`:3242-3284`), D-30 (`:3332-3380`), P-i (`:203-262`), P-w
  (`:3094-3164`), plus the build/rewrite bundles' cited sections,
  read WHOLE. TOOK the satisfiable-telescope standard, the
  copy-paid-at-use rule, and the prohibition-priority rule.
- `scripts/rules.py --for build` and `--for rewrite`, read all
  statements.

## LITERATURE

Banked; nothing spent.

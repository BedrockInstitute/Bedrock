# LJ-1.495 report: twenty-six of TFacts's fields may be a delivered shift

slot: `coder`. Written early as a skeleton and filled as runs land (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-495/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: one term `tfacts-shared-from-kfacts` in
`agents/tasks/LJ-1-495/Probe495.agda`. The type is the 26 fields
`TFacts` shares with `KFacts`, at `TFacts`'s own indices, filled by
six applications of `KFactsCons` to a rebuilt `KValue` frame.
Nothing lands in `src/`. I did not build a `TFacts` value. I did
not fill `someEnv`. I did not report on `[LJ-1.113]`'s 28.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection. It does not start phase 3.
No Boundary clause is in conflict.

## PREDECESSOR, READ FIRST

`[LJ-1.491]` is **GO** (`agents/tasks/LJ-1-491/lj-1.491-report.md:75`).
Quote at `:75-76`:

> **GO.** `kvalue-with-omega` typechecks
> (`agents/tasks/LJ-1-491/Probe491.agda:54-66`, exit 0, median

The delivered type is `KValue`'s telescope plus `⟨ ω ∈ gam ⟩`,
body `KValue.facts` (`Probe491.agda:54-64`). I took that telescope.
I did not stop. Audit F1: a predecessor taken as a hypothesis is the
report (`dev/pod/audit-2026-08-20.md:34-41`).

## D-10, BEFORE ANY AGDA

Counted at the cited lines, not from the brief.

`KFacts` (`src/L/Condensation.lagda.md:6079-6080`): parameters live
in `Fin n`. Environment length is `n`. The first field
(`:6082`) is `lookup N0 γ`. COUNT of `suc` on a shared-field
lookup in `KFacts`: **0**.

`TFacts` (`src/L/Condensation/TwelveAgree.lagda.md:129-131`):
parameters live in `Fin (5 + n)`. Environment length is `11 + n`.
The first field (`:133`) is
`lookup (suc (suc (suc (suc (suc (suc N0)))))) γ'`.
COUNT of `suc` on that lookup: **6**.
The same six `suc`s sit on `tagEq1` through `tagEq11` (`:134-144`),
on `numK0` through `numK11` (`:145-156`), on `innerK` (`:157-158`),
and on `pairK` (`:159-161`). COUNT of shared fields that carry a
number of `suc`s other than six: **0**.

`KFactsCons` (`src/L/Condensation.lagda.md:6122-6128`) adds one
`suc` to every index and one cons to the environment.

`KValue` (`src/L/Condensation.lagda.md:7389-7395`) instantiates
`KFacts` at `n = 14`: `Kenv : S ^ 14` and indices `Fin 14`.
Six conses give environment length `20` and indices `Fin 20`.
`TFacts` at `n = 9` has parameters `Fin (5 + 9) = Fin 14` and
environment `S ^ (11 + 9) = S ^ 20`. The six-fold shift of
`KValue`'s frame lands on `TFacts`'s lengths.

The two records do not share one `n`. `KFacts {n}` after six
conses has length `6 + n`. `TFacts {n}` has length `11 + n`.
Those fail to line up. They line up when `KFacts` starts at
`5 + n`, which is `KValue`'s `14` against `TFacts`'s `n = 9`.
The brief names that frame. The shift is exactly six. I did not
stop.

## VERDICT

**GO.** `twice` typechecks
(`agents/tasks/LJ-1-495/Probe495.agda:93-107`, exit 0, median
**2.44 s** on three forced rechecks of the W3-only file).
`tfacts-shared-from-kfacts` typechecks
(`Probe495.agda:166-199`, exit 0, median **3.17 s** on three
forced rechecks of the full file) and PASSes the program's
witness meter
(`/opt/homebrew/bin/python3.11 scripts/pod/witness.py --code LJ-1-495
--brief agents/tasks/LJ-1-495/LJ-1.495.md`, exit 0, 2.55 s, 0
UNRESOLVED of 1, `probe_red=False`, `runs/witness-1.out`).
`.venv/bin/python` is absent in this worktree. I added no
dependency.

I did not write `review-of-tfacts-shared-from-kfacts.md`. The
verdict is GO.

A GO says twenty-six of fifty-nine `TFacts` fields are a
delivered `KFactsCons` iterated six times, read off at
`TFacts`'s own indices. It does not land the shift in `src/`.
It does not inhabit the other thirty-three fields. It does
not build a `TFacts` value. It does not fill `someEnv`. It
does not touch `src/Landmarks.lagda.md`. It does not close
the campaign. It does not claim a trophy.

## 1. W2

W2 (from DD4): write the mathematics once at a generic carrier and
instantiate it.

`KFactsCons` (`src/L/Condensation.lagda.md:6122`) is the generic
one-step. `twice` instantiates it twice. `six` instantiates it
four more times on top of `twice` (`Probe495.agda:164`).
`Shared26` (`Probe495.agda:46-80`) is the 26-field block once,
at `TFacts`'s `Fin (5 + n)` and environment length `11 + n`.
The obligation instantiates it at `n = 9` against `KValue`'s
`Fin 14` (`Probe495.agda:169-170`). I did not copy a field
fill. I did not rebuild `KFacts` by hand. No site is named as
a fixed form. There is no conflict with W2.

W4 does not fire: no module was retired.

P-l did not fire: the type names `Fin`, `lookup`, and six
`suc`s on an index. It does not name a transparent `sucV`-chain
of a stage.

D-26 did not fire: this is a shift of a record, not a
well-founded key.

## 2. W3: the second application, first

**GO.** The widest unmeasured term was the second
`KFactsCons`, because `consed` is the first
(`src/L/Condensation.lagda.md:7429-7434`) and the tree has
never composed two.

`twice` (`Probe495.agda:93-107`) takes `c1 c2 : S` and a
`KFacts` at `KValue`'s indices and returns the block at
`suc (suc iA)` over `c2 ∷ c1 ∷ Kenv`. The body is one
`KFactsCons` on the result of another. Obligation omitted
in the W3-only file.

First landing of the W3-only file: 2.80 s, peak RSS
610107392 bytes, exit 0, printed `Checking`.
`runs/w3-0.out` / `w3-0.time`.

Three forced rechecks of the W3-only file, interface
deleted each time
(`_build/2.8.0/agda/agents/tasks/LJ-1-495/Probe495.agdai`),
same caliber, one Agda process, exit 0 every time, each
printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 2.51 | 610107392 |
| `runs/w3-2.out` / `w3-2.time` | 2.44 | 610107392 |
| `runs/w3-3.out` / `w3-3.time` | 2.40 | 610156544 |

Median wall **2.44 s**. Median peak RSS **610107392 bytes**.
No heap event. Two compose. Six compose the same way.

The brief's W3 estimate was about 20 lines and under 30
seconds. Measured, `twice` is 15 lines (`:93-107`). Wall
is 2.44 s. Nothing is funded against the estimate. Nothing
is funded against `consed`.

## 3. The obligation

**GO.** `tfacts-shared-from-kfacts` (`Probe495.agda:166-199`)
rebuilds `[LJ-1.491]`'s frame (`:83-90`), takes a `KFacts` at
`iA iK i0 ... i11 Kenv`, applies `six` (`:109-164`), and
fills `Shared26 {n = 9}` by projection. The top-level name
the witness reads is the alias at `:202`.

`ω∈γ` is unused. The `KFacts` argument is used. I did not
use `facts` as the body. I did not import a probe. I did
not postulate. I did not add a hypothesis to `KFacts`. I
did not weaken a field. I did not edit `src/`.

The six extra `S` values `c1 ... c6` are prefix arguments.
`TFacts`'s environment is six longer than `KValue`'s. Those
six are not determined by the frame. They do not appear in
the 26 field types, which look only under six `suc`s.

The shape that resisted was notation, not the shift.
`Base.Prelude` exports `ℕ` and `suc` and does not export
`_+_` (`src/Base/Prelude.lagda.md:181-182`). First full
check failed `[NotInScope]` on `_+_` (`runs/full-0.out`).
I imported `Cubical.Data.Nat using ( _+_ )`, as
`TwelveAgree` does (`src/L/Condensation/TwelveAgree.lagda.md:36`).
The next check failed `[NotInScope]` on `_^_`
(`runs/full-1.out`). `_^_` is `Vec` (`src/FOL/Semantics.lagda.md:50-51`:
`A ^ n = Vec A n`). I wrote `Vec S (11 + n)`
(`Probe495.agda:48`). That is the same type. It is not a
weaker statement.

`KFacts` after six conses has indices in `Fin 20`.
`TFacts {9}` has parameters in `Fin 14` and looks them up
under six `suc`s. The field types match. The record types
do not. The obligation returns `Shared26`, not a shifted
`KFacts` and not a `TFacts`.

First landing of the full file: 3.55 s, peak RSS 762724352
bytes, exit 0, printed `Checking`. `runs/full-2.out` /
`full-2.time`.

Three forced rechecks of the full file, interface deleted
each time, same caliber, one Agda process, exit 0 every
time, each printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-3.out` / `full-3.time` | 3.22 | 762724352 |
| `runs/full-4.out` / `full-4.time` | 3.13 | 762740736 |
| `runs/full-5.out` / `full-5.time` | 3.17 | 762740736 |

Median wall **3.17 s**. Median peak RSS **762740736 bytes**.
No heap event.

The brief's estimate was about 130 lines, of which the
obligation was about 55, comparables of SHAPE. Measured,
the file is 202 lines. Nothing is funded against the
estimate. Nothing is funded against W3's 2.44 s. Nothing
is funded against `[LJ-1.491]`'s 2.40 s.

`KFacts` has 29 fields (`src/L/Condensation.lagda.md:6081-6115`).
The shift carries three this task discards: `innerPairK`
(`:6108`), `carrierK` (`:6112`), `arityK` (`:6114`).
COUNT discarded: **3**. COUNT paid: **26**.

## WHAT TFACTS STILL OWES

Measured from `src/L/Condensation/TwelveAgree.lagda.md:132-332`.
COUNT of `TFacts` fields: **59**. COUNT this task pays:
**26**. COUNT this task does not pay: **33**. I do not
price the unpaid fields.

| family | fields | count | a source |
|---|---|---|---|
| codes | `codesK`, `codesK-un` | 2 | `src/L/Condensation/LowerAgree.lagda.md:116` `LFacts.codesK` |
| valK | `valK`, `valK-un` | 2 | `LowerAgree.lagda.md:127` `LFacts.valK` |
| t0/t1 | `t0eq`, `t1eq`, `t0K`, `num1K` | 4 | `LowerAgree.lagda.md:135` `LFacts.t0eq` |
| envK | `envK-mem`, `envK-neg`, `envK-top`, `envK-imp`, `envK-allin` | 5 | `TwelveAgree.lagda.md:186` `TFacts.envK-mem` |
| envInK | `envInK-mem`, `envInK-neg`, `envInK-top`, `envInK-imp` | 4 | `TwelveAgree.lagda.md:216` `TFacts.envInK-mem` |
| tmVal | `valV`, `valW`, `wKfact` | 3 | `TwelveAgree.lagda.md:244` `TFacts.valV` |
| transK | `transK` | 1 | `LowerAgree.lagda.md:191` `LFacts.transK` |
| subK | `subK₁-and`, `subK₀-and`, `subK₁-imp`, `subK₀-imp`, `subK-neg`, `subK-un`, `subK-allin` | 7 | `TwelveAgree.lagda.md:265` `TFacts.subK₁-and` |
| someEnv | `someEnv` | 1 | `LowerAgree.lagda.md:52` `someEnvDef` |
| envSetK | `envSetK` | 1 | `TwelveAgree.lagda.md:306` `TFacts.envSetK` |
| consK | `consK-exist`, `consK-forall`, `consK-allin` | 3 | `src/L/Condensation/UpperAgree.lagda.md:191` `UFacts.consK-exist` |

2+2+4+5+4+3+1+7+1+1+3 = 33.

`t0` and `t1` are `TFacts` parameters. They are not
`KFacts` parameters. The 26 shared fields do not mention
them. A later `TFacts` value still needs them.

`sucK` is a telescope hypothesis of `AbstractFrame`
(`TwelveAgree.lagda.md:340-341`). It is not a `TFacts`
field. It is not in the 33.

## 6. C-42

This return is a GO at one site: the 26 shared fields of
`TFacts` at `src/L/Condensation/TwelveAgree.lagda.md:133-161`,
filled from a six-fold `KFactsCons` on a rebuilt `KValue`
frame. It says those 26 inhabit at `TFacts`'s indices. It
does not measure a landing in `src/`. It does not measure
the other 33 fields.

COUNT of `record TFacts` in `src/`: **1**,
`TwelveAgree.lagda.md:129`.

COUNT of `KFactsCons` applications of six in `src/`: **0**.
The tree's own consumer is `consed`, one step, at
`Condensation.lagda.md:7429-7434`.

A cure of these 26 in a probe is not a measured cure of
`TFacts` in `src/`. Re-measure a landing.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX, archived 2026-08-18". Declined. The live producer is `dev/pod/queue.toml`. This task does not consult the archived dispatch rows.
- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined. The per-episode journal is retired. The product of this task lives in this directory.
- `archive/dev/JOURNAL-archived.md:1`, read: "# Archived journal: the retired route". Declined. The retired-route journal does not bear on a `KFactsCons` iteration.
- `dev/ARCHIVE.md:1`, read: "# ARCHIVE.md: the archive registry". Declined. This task does not retire a module.
- `archive/dev/DECISIONS-archived.md:1`, read: "# Archived decisions: the D series". Declined. The live rulings are `dev/pod/rulings.toml`. This task does not consult the archived D rows.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:1`, read: "# Truncation and selection: how the two literatures pick a witness". Declined. This task iterates a delivered record shift. It does not select a truncated witness from the literature.
- `dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the Condensation Lemma and the GCH in L". Declined as a source for a producer. Devlin 5.5 does not inhabit `tfacts-shared-from-kfacts`.
- `dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the rud route, pinned from the collected literature". Declined. This task measures a six-fold `KFactsCons`. It does not consult the orthodox rud digest.
- `dev/literature/geology.md:1`, read: "# Geology dossier: set-theoretic geology sources and the five questions". Declined. Geology is not at issue.
- `dev/literature/terms-2026-08.md:1`, read: "# The terminology dossier: fourteen renderings for the owner's ruling". Declined. No glossary term is at issue.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process from this slot.
- I did not write in `src/`.
- I did not import a probe.
- I did not postulate.
- I did not add a hypothesis to `KFacts`.
- I did not build a `TFacts` value.
- I did not fill `someEnv`.
- I did not inhabit `innerPairK`, `carrierK`, or `arityK`.
- I did not report on `[LJ-1.113]`'s 28.
- I did not write `review-of-tfacts-shared-from-kfacts.md`.
- I did not price the unpaid 33 fields.

## WHAT THE NEXT BRIEF NEEDS

W3 is GO: two `KFactsCons` compose at 2.44 s. The obligation
is GO: six compose, and the 26 shared fields read off at
`TFacts`'s indices at 3.17 s. Twenty-six of fifty-nine
fields are a delivered move iterated.

What a next brief can order, one at a time:

1. The unpaid 33, by family, at
   `src/L/Condensation/TwelveAgree.lagda.md`. Do not fund
   them against this 3.17 s. Re-measure each family. A
   source for each family is in `## WHAT TFACTS STILL OWES`.
2. Land the six-fold shift, or decline it. COUNT of
   six-fold `KFactsCons` in `src/` is 0. Do not fund a
   landing against this pad.
3. The six prefix `S` values. The frame does not determine
   them. A `TFacts` environment of length 20 needs a choice
   of prefix.
4. `t0` and `t1`. They are `TFacts` parameters. They are
   not in the 26. `KValue` has no `t0`/`t1` binders. A
   later value still needs them, or a brief that identifies
   them with `i0`/`i1`.
5. `sucK` on `AbstractFrame`
   (`TwelveAgree.lagda.md:340-341`). Not a `TFacts` field.
   Still a telescope hole for `twelve-out` / `twelve-back`.
6. Then `twelve-out` / `twelve-back`
   (`TwelveAgree.lagda.md:528-537`), which still need a
   `TFacts` value at a real `K`.

The condensation front is open for those briefs. It is open
for a landing in `src/` only after a brief names the prefix
and names the unpaid family it wants.

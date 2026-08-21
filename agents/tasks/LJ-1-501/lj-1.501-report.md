# [LJ-1.501] report: two tag equations that pay four fields

## VERDICT

**GO.** `tagEq-at-t` typechecks at `agents/tasks/LJ-1-501/Probe501.agda:85-91`,
exit 0, median **2.37 s** on three forced rechecks of the full file. It is
generic in the tag `k` AND generic in the index `t`, so one term serves
`tagEq0` to `tagEq11`, `t0eq` and `t1eq` alike.

All **four** fields the brief names typecheck at `KValue`'s frame:
`t0eq` (`Probe501.agda:151-157`), `t1eq` (`:161-167`), `t0K` (`:171-183`)
and `num1K` (`:188-195`). The witness meter PASSes:
`/opt/homebrew/bin/python3.11 scripts/pod/witness.py --code LJ-1-501
--brief agents/tasks/LJ-1-501/LJ-1.501.md`, exit 0, 2.20 s,
0 UNRESOLVED of 1, `probe_red=False`, `runs/witness-1.out`.
`.venv/bin/python` is absent in this worktree. I added no dependency.

I did not write `review-of-tagEq-at-t.md`. The verdict is GO.

**A GO says four of fifty-nine `TFacts` fields are paid at `KValue`'s frame.**
It does not land anything in `src/`. It does not inhabit the other
fifty-five. It does not build a `TFacts` value. It does not touch the
`envK-*` family or the code readers, which `[LJ-1.499]` and `[LJ-1.500]`
hold. It does not close the campaign. It does not claim a trophy.

**ONE FINDING IS LARGER THAN THE FOUR FIELDS AND SECTION 4 STATES IT.**

## 1. D-10, BEFORE ANY AGDA

The brief asks what determines the layout at `t0`, and whether `numeralL 0`
provably sits at slot `t0`.

**AT THE RECORD, NOTHING DETERMINES IT.** `t0` and `t1` are parameters of
`TFacts` in the same telescope as `N0` to `N11`
(`src/L/Condensation/TwelveAgree.lagda.md:130`). The record proves no tag
equation at any of them: `tagEq0` to `tagEq11` are FIELDS, of exactly the
shape the brief asks me to prove (`:132-143`). So the record's own design
already treats "the slot at a parameter index holds numeral k" as a
hypothesis. `t0eq` (`:181`) and `t1eq` (`:182`) are that same shape at `t0`
and `t1`.

`TFacts` has ONE consumer, `AbstractFrame` (`:342`), and `AbstractFrame` is
applied nowhere in `src/`. I grepped `src/` and `dev/`; the only two hits are its own
definition at `src/L/Condensation/TwelveAgree.lagda.md:337` and a comment
at `:70`. **So no frame in the
tree fixes `t0` or `t1` today.**

**AT `KValue`'S FRAME, THE LAYOUT IS FIXED, AND IT IS FIXED BY A LIST.**
`Kenv : S ^ 14` is concrete (`src/L/Condensation.lagda.md:7389-7393`):
the carrier, the bound, then `numeralL 0` to `numeralL 11` at `i0` to
`i11` (`:7395-7409`). `KValue.facts` writes `tagEq0 = refl` at `:7412`, so
the slot holds the numeral by computation and not by hypothesis.

**MEASURED, and this is W3.** `layout-at-t0` at `Probe501.agda:57-61`
typechecks by `refl` with NO hypothesis at all, through the six-fold shift.
So at `KValue`'s frame `numeralL 0` provably sits at slot `i0` after the
shift, and the tag equation there is a THEOREM.

**I DID NOT STOP.** The brief said a stop is the more valuable outcome if
nothing determines the layout. Nothing determines it AT THE RECORD, but the
frame the brief names does determine it, and the frame is where the brief
told me to build. Section 4 carries what the record-level half of that
answer costs.

## 2. THE FOUR FIELDS, ACCOUNTED

| Field | `file:line` | State |
|---|---|---|
| `t0eq` | `src/L/Condensation/TwelveAgree.lagda.md:181` | **PAID by this task.** `Probe501.agda:151-157`, from the generic obligation at `:85-91` applied to the delivered `KFacts.tagEq0`. |
| `t1eq` | `src/L/Condensation/TwelveAgree.lagda.md:182` | **PAID by this task.** `Probe501.agda:161-167`. The SAME term at the next tag, from the delivered `KFacts.tagEq1`. This is what "generic in the tag" buys. |
| `t0K` | `src/L/Condensation/TwelveAgree.lagda.md:183-184` | **FREE BY TRANSPORT**, and this task built the transport. `tagK-from-tagEq` at `Probe501.agda:97-102`, applied at `:171-183` over `t0eq` and the delivered `KFacts.numK0`. `[LJ-1.113]` measured this reduction (`agents/tasks/LJ-1-113/lj-1.113-report.md:128-131`) and never built the term. |
| `num1K` | `src/L/Condensation/TwelveAgree.lagda.md:185` | **FREE from `[LJ-1.495]`.** Its type is `TFacts.numK1`'s type at `:146`, and `numK1` is one of the twenty-six `[LJ-1.495]` delivered (`agents/tasks/LJ-1-495/Probe495.agda:187`, GO). |

**I DID NOT PRICE THE OTHER FIFTY-FIVE.**

### 2.1 `num1K` is `numK1`, decided by the elaborator

The brief asked me to confirm it. **A reading is not a confirmation, so I
did not read.** `Probe501.agda:115-125` transcribes the two types
SEPARATELY, each from its own line of the master, at `TFacts`'s own
parameter shape, then gives `num1K-is-numK1` as the identity. If the two
transcriptions were not the same type the identity would not typecheck. It
typechecks. Exit 0.

**Report this as a finding and not as a defect.** The brief said so and I
agree: `TFacts` states one type twice under two names, forty rows apart
(`:146` and `:185`). Whether that is worth curing is not my call.

### 2.2 `t0K` is the transport `[LJ-1.113]` promised

`archive/dev/LJ-dispatch-index.md:189` records `[LJ-1.113]`'s verdict as
`PROVABLE 1, NEW CONTENT 28`. `t0K` was that PROVABLE 1. It stayed a
reading for the whole interval because the term it needs, `t0eq`, had no
supplier. This task supplies `t0eq`, so the reading is now a term:
`Probe501.agda:177-183`.

I wrote the transport generically (`tagK-from-tagEq`, `:97-102`): any tag,
any slot, any key index, over `Vec S m`. So it serves `t0K` and it would
serve the same move at any other slot without a second copy.

## 3. W3, THE WIDEST UNMEASURED TERM

The brief named the layout at `t0`. I wrote it FIRST, alone in the file,
with the obligation omitted, and I typechecked it alone.

**I made it STRONGER than the brief's form.** The brief wrote
`layout-at-t0 : (what the frame gives) → ...`. I removed the hypothesis and
asked for `refl`. That is the decisive question: if the frame proves the
layout with nothing, the layout is a theorem here; if it needs a
hypothesis, the record must carry one. `refl` forms
(`Probe501.agda:57-61`).

**GO.** Exit 0, median **2.32 s**, peak RSS **611,139,584** bytes.

| Run | Real (s) | Peak RSS (bytes) |
|---|---|---|
| `runs/w3-1.time` | 2.28 | 611139584 |
| `runs/w3-2.time` | 2.32 | 611155968 |
| `runs/w3-3.time` | 2.43 | 611139584 |

`runs/w3-0.out` and `runs/w3-0.time` are the first run of the same file,
2.28 s, kept for the record.

**THE ESTIMATE AND THE MEASUREMENT.** The brief estimated about 20 lines
and under 30 seconds for W3, and told me not to fund it against
`[LJ-1.495]`'s 2.44 s. The W3 file was 64 lines, of which the term is 7
(`:57-63`); the rest is the module header and the telescope taken from
`Probe495.agda:84-91`. It ran at 2.32 s. **That number is close to
`[LJ-1.495]`'s 2.44 s, and the closeness is not evidence about slots.**
Both files import `L.Condensation` at the same telescope, and the import
is what the time measures. I report the number; I do not transfer it.

## 4. THE FINDING THAT IS LARGER THAN FOUR FIELDS

**`t0eq` IS FREE AT `KValue`'S FRAME ONLY BECAUSE THE FRAME POINTS `t0` AT
THE SAME SLOT AS `N0`.**

`Kenv` has fourteen slots (`src/L/Condensation.lagda.md:7389-7393`). Two
hold the carrier and the bound; the other twelve hold `numeralL 0` to
`numeralL 11`, one each. **There is no spare slot holding `numeralL 0`.**
So a frame over `Kenv` that needs `t0` to hold `numeralL 0` has exactly one
choice, `t0 := i0`, and `t1 := i1` likewise. `[LJ-1.495]` already
instantiated `N0 := i0` and `N1 := i1` at this frame
(`agents/tasks/LJ-1-495/Probe495.agda:169`). The identification is forced
by the list, not chosen by me.

**THIS REFINES `[LJ-1.113]` AND DOES NOT CONTRADICT IT.**
`agents/tasks/LJ-1-113/lj-1.113-report.md:122` states: "**MEASURED: `t0eq`
is not derivable from the delivered machinery.**" That stands at a FREE
`t0`, and `[LJ-1.96]`'s `N0 != t0`
(`agents/tasks/LJ-1-113/lj-1.113-report.md:120-121`) is the same
measurement. What no dispatch had asked is what a CONCRETE frame does with
`t0`, and the answer is that `KValue`'s frame has no freedom left.

**WHAT I DID NOT MEASURE, AND THE NEXT BRIEF NEEDS IT.** `t0` and `t1` are
not only fact indices. They are variable indices INSIDE the consumer's
formula `SatGraphB.twelveB`, in four of the twelve rows: `memBndAt`
(`src/L/Condensation.lagda.md:2241-2243`), `eqBndAt` (`:2244-2246`),
`allInBndAt` (`:2255-2257`) and `exInBndAt` (`:2258-2260`). Setting
`t0 := N0` makes one variable index serve two syntactic roles in that
formula. **The four facts do not forbid it. I did not measure whether the
consumer of `twelveB` survives it.** That is one question and it is cheap:
elaborate `SatGraphB.twelveB` with `t0 := N0` and `t1 := N1` and see
whether the downstream row lemmas still apply.

**IF THE ANSWER IS NO**, then `KValue`'s `Kenv` is one slot short in two
places, the cure is a sixteen-slot `Kenv`, and every field brief on this
front that assumed fourteen has to be re-read. **IF THE ANSWER IS YES**,
four fields are paid and the `t0`/`t1` pair costs the record nothing at
this frame.

**I RECOMMEND THAT QUESTION AS THE NEXT W3 ON THIS FRONT.** It is the
widest unmeasured term I met, and it is wider than the one the brief named.

## 5. W2

The obligation is written ONCE at a generic carrier and instantiated.

`tagEq-at-t` (`Probe501.agda:85-91`) takes `{n : ℕ}`, a tag `k : ℕ`, an
index `t : Fin (5 + n)` and a short environment `γ : Vec S (5 + n)`. It
names no frame, no carrier and no bound. `tagK-from-tagEq` (`:97-102`) is
generic over `Fin m` and `Vec S m`, wider still. `num1K-is-numK1`
(`:123-125`) is generic in `n`, `K` and `γ'`.

Only `module AtKValue` (`:141-195`) names `KValue`, and it contains no
mathematics: four instantiations and nothing else.

**The six sucs meet the six conses with nothing to transport.** `TFacts`
looks up at `suc^6 t` over `Vec S (11 + n)` with `t : Fin (5 + n)`
(`src/L/Condensation/TwelveAgree.lagda.md:129-131`). Six conses onto
`Vec S (5 + n)` give `Vec S (6 + (5 + n))`, and `6 + (5 + n)` and `11 + n`
have the same normal form under `Cubical.Data.Nat._+_`, which recurses on
the first argument. So the two lengths are definitionally equal and the
proof of the obligation is `h`. **No transport, no `subst`, no coercion.**

I met no deadline conflict, so W2 raised no stop.

## 6. W4

No module was retired. Nothing moved to `archive/`. No `dev/ARCHIVE.md`
row was written. The task adds one probe under `agents/tasks/` and touches
no master.

**Priced against the ideal form written fresh today:** the ideal form of
this obligation is one generic term over `Vec S (5 + n)` plus one generic
transport, which is `tagEq-at-t` at `Probe501.agda:85-91` and `tagK-from-tagEq` at `:97-102`, 7 lines and 6 lines. The chapter
I have is `TFacts` at `TwelveAgree.lagda.md:129-335`, and it states these
four fields as four separate hypotheses rather than as one generic field
over an index. **That difference is a real cost and it is not mine to
rule**: `tagEq0` to `tagEq11`, `t0eq` and `t1eq` are fourteen fields of one
shape, and a single field `tagEqAt : (k : ℕ) (t : Fin (5 + n)) → ...` would
not serve, because each of the fourteen fixes a DIFFERENT index. So the
fourteen are not redundant. `num1K` against `numK1` (section 2.1) is the
one genuine duplicate I found, and it is one row, not a module.

## 7. THE PRICE

**Full file: median 2.37 s, peak RSS 619,659,264 bytes**, three forced
rechecks, wide caliber, one Agda process per run.

| Run | Real (s) | Peak RSS (bytes) |
|---|---|---|
| `runs/full-1.time` | 2.43 | 619659264 |
| `runs/full-2.time` | 2.37 | 619659264 |
| `runs/full-3.time` | 2.28 | 619659264 |

`runs/full-0.time` is a fourth run of the same file, 2.31 s, kept for the
record. Every run above is on the FINAL file body.

**No heap wall. No rerun after a wall.** `GHCRTS` was `-A64m -I0 -M8g` on
the pane, set by the program, and I did not touch it. I started one Agda
process per run.

**THE ESTIMATE AND THE MEASUREMENT.** The brief estimated about 130 lines
in the probe, of which the obligation is about 25. The probe is **200**
lines, of which the obligation `tagEq-at-t` is **7** (`:85-91`). The
overrun is comment and the four instantiations at `KValue`, not
mathematics: 76 of the 200 lines are comment. The obligation came in far
under its 25, because it is `h`.

**THE RATIO BAR DOES NOT FIRE.** `Probe501.agda` is a raw `.agda` probe
and carries no ` ```agda ` fence, so the divisor is 0 in-fence lines and
the bar cannot bind here. Nothing landed in `src/`.

## 8. WHAT I DID NOT DO

- I did not build a `TFacts` value.
- I did not inhabit the other fifty-five fields, and I did not price them.
- I did not touch the `envK-*` family or the code readers.
  `[LJ-1.499]` and `[LJ-1.500]` hold those and are running.
- I did not land anything in `src/`.
- I did not commit and I did not push.
- I did not measure whether `SatGraphB.twelveB` survives `t0 := N0`
  (section 4). That is the recommended next W3.

## 9. STATE OF THE WORKING TREE

Four paths added, all inside this task's scope:

- `agents/tasks/LJ-1-501/Probe501.agda`, 200 lines, exit 0.
- `agents/tasks/LJ-1-501/lj-1.501-report.md`, this file.
- `agents/tasks/LJ-1-501/runs/`, eight `.time` files and nine `.out` files,
  the ninth being `witness-1.out`.

`agents/tasks/LJ-1-501/review-of-tagEq-at-t.md` was NOT written. The
verdict is GO.

`scripts/gate/check-probes.py --check` is clean: 4999 tracked files, no
probe outside `agents/tasks/` and no generated file.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`. **READ AND USED**, section 2.2.
  `archive/dev/LJ-dispatch-index.md:189` reads
  `| LJ-1.113 | Who supplies the twenty nine? | PROVABLE 1, NEW CONTENT 28 | None is refutable. Twenty five are one pattern, K closed under a machine construction; someEnv is the odd one |`
  That confirms `t0K` was `[LJ-1.113]`'s single PROVABLE verdict, which is
  the claim section 2.2 rests on.
- `archive/dev/JOURNAL.md`. **DECLINED, not read.** A journal carries
  history. The layout question is settled by the current `Kenv` list and by
  the current `TFacts` telescope, both live.
- `archive/dev/JOURNAL-archived.md`. **DECLINED, not read**, for the same
  reason.
- `dev/ARCHIVE.md`. **DECLINED, not read.** No module was retired by this
  task, so it has no row here and nothing to answer.
- `archive/dev/PLAN-archived.md`. **DECLINED, not read.** The plan does not
  fix a vector slot, and `AGENTS.md` forbids quoting a number found in a
  paragraph.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`. **DECLINED, not read.**
  This task proves a vector index holds a numeral. No truncation and no
  selection appears in the obligation or in its proof.
- `dev/literature/devlin-II5.md`. **DECLINED, not read.** It is about
  elementarity and the condensation argument. The layout of `Kenv` is a
  coding decision of this repository, not Devlin's.
- `dev/literature/terms-2026-08.md`. **DECLINED, not read.** No naming
  question arose. I added no `dev/glossary.toml` entry.
- `dev/literature/digest.md`. **DECLINED, not read.** No mathematical
  content was needed beyond the two records already in the tree.
- `dev/literature/geology.md`. **DECLINED, not read.** No stage or ordinal
  question arose.

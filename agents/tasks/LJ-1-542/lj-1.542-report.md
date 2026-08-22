# LJ-1.542 report: the twelve numK rows are already paid, and the telescope is EMPTY

slot: `coder`. Written early as a skeleton and filled as runs land (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-542/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. **No heap event.**

TARGET: one term `numK-frame-inhabited` in
`agents/tasks/LJ-1-542/Probe542.agda`, the extra hypotheses the twelve
`numK` forms take collected as one telescope, with a witness at
`KValue`'s frame. Nothing lands in `src/`. I did not build a `TFacts`
value. I did not collect any other family. I did not fill `someEnv`. I
did not edit `src/`. I did not rebuild `[LJ-1.495]`'s shift. I
postulated nothing.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict.

## VERDICT

**GO, AND THE TELESCOPE IS EMPTY. THE TWELVE COST NOTHING.**

`numK-frame-inhabited` typechecks
(`agents/tasks/LJ-1-542/Probe542.agda:150-158`, top-level alias at
`:162`), exit 0, **median 2.65 s and 649,183,232 B peak RSS** over three
forced rechecks of the final file (`runs/shift-0.time` 2.66 s,
`runs/shift-1.time` 2.65 s, `runs/shift-2.time` 2.64 s; bytes
649,183,232, 649,166,848 and 649,265,152, a spread of 98,304 B that is
the measurement's own granularity).

**REPORT THE BYTES AND NOT THE SECONDS, AND THE TREE CARRIES THE
MEASUREMENT.** I ran the identical file through two independent rounds of
three forced rechecks each. `runs/shift-*.time` gives 2.66, 2.65, 2.64
and `runs/shift-b-*.time` gives 2.66, 2.71, 2.68. **The two byte medians
are the same number, 649,183,232 B, and the second-medians differ by
0.03 s.** Inside the delivered round the effect is larger:
`runs/delivered-*.time` spans 2.87 s to 3.00 s, a 0.13 s spread, while
its bytes span 16,384 B. **So on this pane the seconds carry a tenth of a
second of load noise and the peak RSS does not.** The table below is read
by its byte column.

I also observed a 2.84 s median on a third round, taken before I
corrected two comments in the probe. **Its run files were overwritten by
the rounds above, so that number is an observation of mine and not
evidence in the tree**, and nothing in this report rests on it.

It PASSes the program's witness meter
(`/opt/homebrew/bin/python3.11 scripts/pod/witness.py --code LJ-1-542
--brief agents/tasks/LJ-1-542/LJ-1.542.md`, exit 0, 2.49 s,
**0 UNRESOLVED of 1**, `probe_red=False`, `runs/witness-final.out`; the
meter's first run on the earlier file state is `runs/witness-0.out`, also
exit 0 and also 0 UNRESOLVED of 1).
`.venv/bin/python` is absent in this worktree, as it was for
`[LJ-1.538]` (`agents/tasks/LJ-1-538/lj-1.538-report.md:34-36`),
`[LJ-1.539]` and `[LJ-1.499]`. I added no dependency.

I did not write `review-of-numK-frame.md`. The obligation is inhabited,
so the verdict on the obligation is GO.

**THE RESULT IS NOT THE WITNESS. IT IS THE TYPE.** `[LJ-1.538]`'s
obligation takes `SupplyEnv`'s eighth parameter `ω∈σ`
(`agents/tasks/LJ-1-538/Probe538.agda:164`). `[LJ-1.539]`'s takes a
slot-one subset fact (`agents/tasks/LJ-1-539/Probe539.agda:368-371`).
**`numK-frame-inhabited` takes `KValue`'s seven parameters, six free
cells, and NOTHING ELSE** (`Probe542.agda:139-158`). The brief asked for
"the extra hypotheses the TWELVE numK forms take, collected as one
telescope". **The honest collection of that telescope is the empty one,
and that is the answer.**

## D-10, BEFORE ANY AGDA

The brief asks whether `[LJ-1.495]`'s shift already delivers the twelve.
Counted at the cited lines, before any Agda ran.

`KFacts.numK0` (`src/L/Condensation.lagda.md:6094`) is

    numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup K γ) ⟩

`TFacts.numK0` (`src/L/Condensation/TwelveAgree.lagda.md:145`) is

    numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩

The two differ by SIX successors on the index and by six cons cells on
the environment. `lookup (suc i) (x ∷ xs)` reduces to `lookup i xs`
definitionally. **So at `γ' = c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv` the
two types are not two types. They are one type**, and a `KFacts` field
inhabits a `TFacts` field with no transport, no `KFactsCons` and no
conversion. COUNT of `numK` rows that carry a number of `suc`s other
than six: **0** (`TwelveAgree.lagda.md:145-156`).

`KValue.facts` (`src/L/Condensation.lagda.md:7411`) is a real value in
`src/`, and it already fills all twelve
(`:7416-7419`, `numK0 = B.num∈λ 0` through `numK11 = B.num∈λ 11`).

**SO THE ANSWER WAS READABLE OFF THE TREE BEFORE ANY AGDA RAN, AND THE
AGDA ONLY CONFIRMED IT.**

**A CORRECTION THE MATHEMATICIAN SHOULD CARRY, AND IT IS ARITHMETIC.**
The brief says sixteen of forty one are collected and "these twelve
would make twenty eight". **The twelve were already inside
`[LJ-1.495]`'s delivered `Shared26`**
(`agents/tasks/LJ-1-495/Probe495.agda:62-73` states them, `:186-197`
fills them, and that task is GO,
`agents/tasks/LJ-1-495/lj-1.495-report.md:158`). I cannot tell from
here whether the ledger of forty one counted them as outstanding. **If
it did, the count was already twenty eight before this task started and
the real gain here is zero fields plus one measurement.** I report the
arithmetic and do not settle it: the ledger is not in my scope.

## SHIFT OR FORM

**BOTH ROUTES WORK. RULE FOR THE SHIFT.** Both are built to the SAME
record at the SAME frame in the delivered probe, so the prices are like
for like and neither is an estimate.

| Route | Term | Telescope | Price |
|---|---|---|---|
| **SHIFT** | `facts .numK`k, `Probe542.agda:150-158` | `KValue`'s **seven** | **2.65 s, 649,183,232 B** (`runs/shift-*.time`) |
| FORM, `#∈λ` | `Probe542.agda:206-213` | `SupplyEnv`'s **eight** | see below |
| FORM, `num∈λ` | `Probe542.agda:219-223` | `Bound`'s **four** | see below |

The three extra terms together cost **+0.24 s and +30,490,624 B** over
the obligation alone (`runs/delivered-*.time`, median 2.89 s and
679,673,856 B, against `runs/shift-*.time`).

**THE FORM ROUTE IS A ROUND TRIP, AND THE TREE SAYS SO IN ONE LINE.**
The brief names `SupplyEnv.#∈λ` (`src/L/Coding/EnvSupply.lagda.md:229`)
as the delivered form and `numeralL-fst`
(`src/L/Axioms/Numerals.lagda.md:179`) as the transport to it. **The
arrow runs the other way.** `#∈λ` is DEFINED from `Bound.num∈λ`:

    src/L/Coding/EnvSupply.lagda.md:230
      #∈λ n = subst (λ w → ⟨ w ∈ Lset lam ⟩) (numeralL-fst n) (B.num∈λ n)

and `Bound.num∈λ` (`src/L/Coding/Bound.lagda.md:139-140`) is what the
record's `numK` rows are stated in. **So reaching `numK` through `#∈λ`
transports OUT across `numeralL-fst` and then straight back IN across
its `sym`** (`Probe542.agda:210-213`). It typechecks, because the target
is an hProp, but it buys nothing.

**AND IT COSTS AN EIGHTH HYPOTHESIS THAT NOBODY SPENDS.** `#∈λ` lives in
`SupplyEnv`, whose telescope carries `ω∈γ : ⟨ ω ∈ sucV gam ⟩`
(`src/L/Coding/EnvSupply.lagda.md:111`; **the brief cites `:112`, which
is the blank line after it**) beyond `KValue`'s seven.
`[LJ-1.538]` had to carry it (`Probe538.agda:164`). **The twelve never
consume it.** That is the trim the brief asked me to do before
collecting, and it is the whole of it: on the form route one hypothesis
is carried and never used, and on the shift route there is no hypothesis
to trim.

**THE CHEAPEST FORM ROUTE IS NEITHER OF THE TWO THE BRIEF NAMED.** It is
`Bound.num∈λ` itself (`Probe542.agda:223`), which needs only FOUR of
`KValue`'s seven parameters and no `subst`. It is also exactly what
`KValue.facts` fills the twelve with, so it is the shift route with the
record peeled off. **The shift is that route plus a name.**

**RULE FOR THE SHIFT**, for one reason that is not the price: the shift
carries no hypothesis at all, so it cannot become vacuous. A form route
through `SupplyEnv` puts `ω∈σ` between the frame and the twelve, and
`[LJ-1.507]` measured what an empty antecedent does to a chain of this
campaign (`agents/tasks/LJ-1-507/Probe507.agda:257`).

## W3, THE WIDEST UNMEASURED TERM

The brief named it: whether the shift already pays the twelve, one
numeral being enough to settle it. I wrote `numK7-at-shift`
(`runs/Probe542.w3-only.agda.txt:67-71`, top-level alias at `:73`) and typechecked it ALONE.

**GO. Exit 0, 1.98 s, 610,074,624 B** (`runs/w3-0.out`,
`runs/w3-0.time`). The body is `facts .numK7`, with no `KFactsCons`
imported and no conversion written. The brief estimated about 12 lines
and under 30 seconds; it took 6 lines of term and 1.98 s.

**`[LJ-1.539]` HAD MADE THE SAME BET ON ONE FIELD AND WON IT**
(`agents/tasks/LJ-1-539/Probe539.agda:375`, `facts .arityK` at the
shifted index with no conversion, and the warning at `:349-354` that the
file stops checking if the reduction stops being definitional).
`AGENTS.md:45` forbids carrying that cure by analogy, so this file
re-measured it on the `numK` rows at their own site. It holds there too.

**ONE STALE CITATION SURVIVES INSIDE `runs/Probe542.w3-only.agda.txt`, ON
PURPOSE.** Its comment at `:21` cites `Probe539.agda:376` and `:354-360`.
The true lines are `:375` and `:349-354`. That file is a verbatim record
of what ran at the W3 run, so I corrected the citation in the delivered
probe (`Probe542.agda:21`) and left the record as it ran. A record I
edit afterwards is not a record.

## THE PRICE, BESIDE THE OTHER TWO

Three families, three figures, one caliber (`-A64m -I0 -M8g`), one Agda
process each.

| Task | Family | Fields | Seconds | Peak RSS | Extra hypotheses |
|---|---|---|---|---|---|
| `[LJ-1.538]` | env forms | 9 | 3.56 | 722,698,240 B | 1 (`ω∈σ`) |
| `[LJ-1.539]` | `subK` | 7 | 3.49 | 749,125,632 B | 1 (`valSub`) |
| **`[LJ-1.542]`** | **`numK`** | **12** | **2.65** | **649,183,232 B** | **0** |

Sources: `agents/tasks/LJ-1-538/lj-1.538-report.md:26`,
`agents/tasks/LJ-1-539/lj-1.539-report.md:28`, and `runs/shift-*.time`
here.

**THE LARGEST FAMILY IS THE CHEAPEST, BY 73,515,008 B AGAINST
`[LJ-1.538]` (-10.2 percent) AND 99,942,400 B AGAINST `[LJ-1.539]`
(-13.3 percent).** The caliber caps the heap at 8 GiB, so this run sits
at about **7.6 percent of the cap**, and the delivered file with all
three routes in it at about **7.9 percent**.

**ONE CAVEAT ON THE COMPARISON, AND IT IS MINE TO STATE.** The two
predecessor figures were measured in their own worktrees. I did not
verify their `_build` state, and I did not re-run either probe here. The
caliber is the same and the method is the same, so I report the three
figures side by side; a critic who wants them beyond doubt should re-run
all three on one pane.

**READ THE TABLE BY THE LAST COLUMN AND NOT BY THE THIRD.** The heap does
not track the field count. It tracks the HYPOTHESES. Twelve fields with
no hypothesis are cheaper than seven fields with one. **That is the fact
the remaining rows should be planned against**, and it is not what two
clean families at near-identical cost suggested.

**WHAT IT SAYS ABOUT THE REMAINING ROWS.** Three families now sit
between 649 MB and 750 MB, a 100 MB band, against a 8,589,934,592 B cap.
`[LJ-1.534]`'s wall at sixteen hypotheses at once is therefore not a
sum of these: **three families summed would be under 2.2 GB.** So the
wall was not the field count and it was not the sum of the parts. **The
mathematician should not read this as a licence to collect the remaining
rows in one pass**, because nothing here measures what `[LJ-1.534]`
actually hit, and `AGENTS.md:45` binds. What it does license is asking
the question with a fourth family, and asking it of a family that takes
a hypothesis, since those are the ones that cost.

## W2, ANSWERED

The brief states it and this is the answer. `NumKTwelve`
(`Probe542.agda:91-105`) states the twelve ONCE at generic `K` and `γ'`,
at `TFacts`'s own indices, and is instantiated at `n = 9` against
`KValue`'s `Fin 14` (`:151`). It names only `K` and `γ'` of `TFacts`'s
fifteen index parameters, because the twelve read no other. Nothing is
written twice and no fixed form is used.

## NON-VACUITY, AND AN ARCHIVED CONVICTION THAT APPLIES

`[LJ-1.71]` convicted a commit here for exactly this
(`archive/dev/LJ-dispatch-index.md:135`). The obligation is not that
case: its witness is `KValue.facts`, a record value that already exists
in `src/` (`src/L/Condensation.lagda.md:7411-7419`), not a hypothesis
this file invented. **`numK-frame-inhabited` is vacuous only if
`KValue`'s own seven parameters are unsatisfiable**, which is a risk it
shares with `[LJ-1.538]`, `[LJ-1.539]` and `[LJ-1.495]` and does not add
to. It carries strictly less risk than either predecessor, because it
adds no antecedent of its own.

## WHAT I DID NOT DO

I did not collect another family. I did not rebuild `[LJ-1.495]`'s
shift: `KFactsCons` is not imported by `Probe542.agda` and `six` is not
rewritten. I did not land anything in `src/`. I did not postulate. I did
not commit and did not push. `scripts/gate/check-probes.py --check` is
clean (5948 tracked files) and `git status --porcelain` shows one
untracked path, `agents/tasks/LJ-1-542/`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ AND USED.** At `:135`:
  `| LJ-1.71 | Consume TwelveAgree, which nothing consumed | CONVICTS c21b417 | The telescope's tagEq is uninhabited at EVERY frame, machine-checked. The module is vacuous. The LJ-1.55 slot fix HOLDS |`
  This is why the non-vacuity section above exists and why I checked
  that the witness comes from `src/` and not from a hypothesis. Also
  read at `:133`:
  `| LJ-1.70 | The generic frame and the discharge | 24 DISCHARGED, 14.7 s | TwelveAgree takes 47 facts once and instantiates the twelve rows. The record shape heap-walled; the telescope is green |`
  which records that the RECORD shape, not the telescope, is what walled
  on this chapter before. My obligation is a record, and it did not
  wall.
- `archive/dev/JOURNAL.md`: **READ, NOT USED.** At `:1064`:
  `  [LJ-1.251] checked KValue against AbstractFrame and the comment is true`
  It is about a stale-comment dispute at `TwelveAgree:519-522`, which is
  outside the twelve `numK` rows. It changed nothing here.
- `archive/dev/JOURNAL-archived.md`: **DECLINED.** `grep -n` for
  `numK`, `KFacts`, `TwelveAgree` and `KValue` over its 4280 lines
  returns nothing, and its own header (`:6`) says
  `**Nothing here is live guidance. It is a dated record and it stays true.**`
  Not read further.
- `dev/ARCHIVE.md`: **DECLINED.** It is the registry of retired
  MODULES (`:1-3`), and this task retires no module and lands nothing in
  `src/`. The same grep returns nothing. Not used.
- `archive/dev/ORCHESTRATION.md`: **DECLINED.** It is the archived
  orchestrator operating rules, superseded by the program. Nothing in it
  bears on a `coder` obligation about `KFacts` indices. Not used.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ AND USED.** At `:248`:
  `concrete set K(u), the finite sequences over the formula set, the variables`
  This names what the twelve rows ARE. `KValue`'s own comment
  (`src/L/Condensation.lagda.md:7370-7371`) says the record is Devlin's
  `K(u)` class for class and that `numK0-11` is the formula set. **The
  formula set is the part of `K(u)` that is a fixed finite list and
  carries no closure condition**, which is the mathematical reason this
  family needs no hypothesis while `subK` and the env forms do. It is
  worth the mathematician's attention that the cheap family is the one
  Devlin's decomposition also makes trivial.
- `dev/literature/digest.md`: **READ, NOT USED.** At `:73`:
  `  false Lemma 9.3, assorted arity/reference slips, and an unprovable`
  It is an errata inventory of Devlin. No row of it touches the numeral
  memberships. Not used.
- `dev/literature/glossary-review-2026-08.md`: **READ, NOT USED.** At
  `:360`:
  `zh 数码 / ja 数項. The sense is the von Neumann numerals inside a model.`
  It settles the TRANSLATION of `numeral`. No prose is written in this
  task (`AGENTS.md:69`), so it binds nothing here.
- `dev/literature/truncation-and-selection.md`: **DECLINED.** It is
  about truncation and choice principles; the twelve `numK` rows are
  memberships in an hProp and no selection is made. Not read.
- `dev/literature/terms-2026-08.md`: **DECLINED.** A terminology
  dossier. This task writes no prose and proposes no glossary entry, and
  the Boundary forbids me choosing one. Not read.

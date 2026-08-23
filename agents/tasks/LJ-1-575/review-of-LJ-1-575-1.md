# review-of-LJ-1-575-1: the NO-GO of LJ-1.575#1 is UPHELD

## HEAD
head_slot: mathematician_adversarial
machine: shared
verdict: upheld
return under review: `agents/tasks/LJ-1-575/lj-1.575-report.md` (LJ-1.575#1, slot `coder`)
stop statement under review: `agents/tasks/LJ-1-575/review-of-tfacts-value.md`
invariant: the critic is not the author. This head did not write the return,
the stop statement, or the probe.

## WHAT THIS REVIEW DECIDES

The predecessor stopped. It built no term `tfacts-value`. It left a green
probe that proves `TFacts ... → Empty.⊥` with no extra hypothesis, and it
stated the stop in `review-of-tfacts-value.md`. I attack that return on
the three questions of this brief. Result: the verdict line and the body
agree, every load-bearing citation that carries the NO-GO resolves today,
and the tmVal census of `TFacts` is complete. Four citation defects and
two census misses are recorded below. None of them moves the verdict.
The NO-GO is UPHELD.

I attacked the return, not the task. I re-opened every load-bearing cite.
I re-ran nothing. The accept arm already re-ran the probe today.

## 0. THE INSTANCE RECORD

The worktree copy of `dev/pod/transitions/2026-08.jsonl` ends at seq 158,
task `LJ-1.399`, stamp `2026-08-19T13:31:57Z`. No line carrying
`"task": "LJ-1.575"` is in it. Model, effort and `heads_sha256` of
instance #1 are therefore not readable here. I report the absence. I
take the six facts from the accept arm, as the brief requires, and I
infer no fact that arm does not carry.

`agents/tasks/LJ-1-575/runs/accept-1.out:16-22` and the JSON facts at
`:24`:

- probe run: `agents/tasks/LJ-1-575/Probe575.agda` rc 0, 2.9 s
- `exit_code` 0
- `obligations_delta` 0
- `obligations_open` 1
- `heap_wall` false
- `lines` 0
- `error_class` null
- `agda_vacuous` false
- `unbound_vacuous` true

The obligation name is missing. The probe itself is green. That is the
machine state of a stated NO-GO, and it matches
`agents/tasks/LJ-1-575/runs/witness-1.out:2`:
`witness: 1 UNRESOLVED of 1, 2.77 s, probe_red=False`.

## 1. QUESTION ONE: DOES THE VERDICT LINE MATCH ITS OWN BODY

Yes. This is not the `[LJ-1.375]` / `[LJ-1.376]` class.

The line (`agents/tasks/LJ-1-575/lj-1.575-report.md:20`):
`**NO-GO, AND IT IS A REFUTATION AND NOT A SHORTFALL.**`

The body delivers exactly that claim, at three strengths, and they
agree with each other:

1. The obligation name has no term. The witness and the accept arm both
   say so, as section 0 records. `--safe` is on
   (`agents/tasks/LJ-1-575/Probe575.agda:1`). No postulate stands in.
2. The type itself has no term. `tfacts-absurd`
   (`Probe575.agda:170-176`) has type
   `TFacts ... → Empty.⊥` and takes no hypothesis besides the record.
   The stop statement repeats that type at
   `review-of-tfacts-value.md:17-21`.
3. The cause is named as a dropped membership on a disjunction, not as
   a missing supplier. Report points 2 and the stop statement's section
   `WHY THE FIELD IS FALSE` both point at `tmValAt`
   (`src/L/Coding/Model.lagda.md:1701-1702`) and at `Fact.tmValK`
   (`src/L/Coding/EnvSupply.lagda.md:575-592`).

Point 5 of the verdict list says W3 is GO. That does not fight the
line. The body says the four collections compose and that this does
not make the record true (`lj-1.575-report.md:47-50` and `:211-214`).
A GO on the union of extra hypotheses is compatible with a NO-GO on
`TFacts`.

I pressed the strongest counter-reading I could build: the Shape
lemmas conclude membership in a free `Ks`, while `TFacts.valV`
concludes membership in
`lookup (suc¹³ K) (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')`
(`src/L/Condensation/TwelveAgree.lagda.md:244-249`). If those types
were not the same, `Shape.valV-absurd γ' (Kat K γ') (TFacts.valV tf)`
at `Probe575.agda:175-176` would not check. It does check. `Kat`
(`Probe575.agda:61-63`) is `lookup (suc⁶ K) γ'`, and seven `suc`s of
cons recover the six-fold shift. The accept arm re-checked the file
today at rc 0. The counter-reading fails.

A second counter-reading: the brief's GO is a `TFacts` value, W3 is
green, and three of `[LJ-1.512]`'s five "no supplier" fields are now
paid, so did a GO sneak through? No. `tag-fields-collected`
(`Probe575.agda:479-486`) inhabits `TagFields`, not `TFacts`. W3
inhabits a product of extra hypotheses, not `TFacts`. The obligation
named in the brief is `Probe575.agda::tfacts-value`. That name is
absent, and the type of that name is refuted.

On DD25's four, used as the lens and not written as extra sections:
the refusal is correct on the predecessor's own numbers; the
refutation measurement is sound; the brief's wrong 54/5 count did not
cause this NO-GO, because no `TFacts` value exists at any count; and
the missed-cure question is answered in the body by `Repair.three`
(`Probe575.agda:363-386`), which the coder was not allowed to land in
`src/`.

## 2. QUESTION TWO: DOES EVERY LOAD-BEARING CLAIM RESOLVE TODAY

I opened every citation that carries the NO-GO, the three false
fields, the W3 inhabitation, the repair, the tag payment, the
predecessor counts, and the price table. All of those resolve. Four
cites are off, and one sentence overclaims a neighbour's consumers.
None of them falsifies `TFacts → Empty.⊥`.

Load-bearing claims that resolve today:

- `record TFacts` starts at `src/L/Condensation/TwelveAgree.lagda.md:129`.
  The last field ends at `:335`. Fifty-nine field names sit at
  `:133-332`.
- `valV` `:244-249`, `valW` `:250-255`, `wKfact` `:256-261`. Each
  quantifies over the tag cell and takes no `tK`. Binder order matches
  `Probe575.agda:104-157`.
- `tmValAt` is the disjunction
  `src/L/Coding/Model.lagda.md:1701-1702`. `tmValAt-con` at `:1723-1724`
  takes only `T ≡ pr (# 0) Val`.
- `Fact.tmValK` at `src/L/Coding/EnvSupply.lagda.md:575-579` takes `eK`
  and `tK`. `conCase` at `:589-592` is the one spend of `tK`.
- `∈-irrefl` at `src/V/Hierarchy.lagda.md:155-156`.
- `LFacts.valV` / `valW` at
  `src/L/Condensation/LowerAgree.lagda.md:179` and `:185`.
  `UFacts.wKfact` at `src/L/Condensation/UpperAgree.lagda.md:179`.
- The six quantified-tag parameters start at
  `src/L/Condensation.lagda.md:4446`, `:4452`, `:5064`, `:5193`,
  `:5404`, `:5410`. The tmVal token on each is the next line. I read
  each parameter. Each quantifies over the tag cell the same way the
  record fields do.
- `AtomLeaf.valK` / `valW` start at `:4219` and `:4226`. `BndLeaf.wK`
  starts at `:4811`. `aK` sits beside them at `:4213` and `:4809`.
  The tag cell is a module parameter, not a quantified binder. The
  report's split of this group from the six is correct.
- `KValue.facts` at `src/L/Condensation.lagda.md:7411-7425` delivers
  `tagEq0`, `tagEq1` and `numK0`.
- `gCodesK` / `gUnCodesK` remain parameters at `:7262-7276`.
- `SupplyEnv.envSetK` at `src/L/Coding/EnvSupply.lagda.md:140-146`
  pins the carrier to `B₀` and has no `B` binder.
- `numeralL-fst` at `src/L/Axioms/Numerals.lagda.md:179-181`.
- Predecessor counts: `[LJ-1.551]` 37 at
  `agents/tasks/LJ-1-551/lj-1.551-report.md:23`; `[LJ-1.553]` 9 at
  `agents/tasks/LJ-1-553/lj-1.553-report.md:23-27`; `[LJ-1.563]` 3
  with extras at `agents/tasks/LJ-1-563/lj-1.563-report.md:49-51`
  and the 49 + 10 arithmetic at `:339-351`. 37 + 9 + 3 + 10 = 59.
- `[LJ-1.512]`'s five with no supplier at
  `agents/tasks/LJ-1-512/lj-1.512-report.md:41-42`.
- Probe self-cites: `tfacts-absurd` `:170-176`, the six projections
  `:170-221`, W3 `:277-300`, `ThreeRepaired` `:316-345`,
  `statement-matches` `:352-361`, `Repair.three` `:363-386`,
  `RepairAtFrame` `:388-410`, `tag-statement-matches` `:457-463`,
  `tag-fields-collected` `:479-486`. Each name sits at the cited
  line.
- Price table, checked against the `.time` files on disk. Delivered
  file: 3.97, 4.04, 4.07 s and RSS 786,972,672 / 786,972,672 /
  787,005,440 B (`runs/full-0..2.time`), median RSS 786,972,672 B,
  9.16 percent of 8,589,934,592 B. Refutation: 3.42 to 3.47 s,
  median 669,237,248 B. Rerun 563: 3.83 to 3.91 s, median
  739,672,064 B. Rerun 553: 3.57 to 3.68 s, median 695,451,648 B.
  Rerun 551: 5.42 to 5.51 s, median 1,066,844,160 B. The linear
  prediction 615,867,538 B at three fields, the excess
  123,804,526 B, and the 0.91 of `[LJ-1.551]`'s band all recompute
  from those medians. `[LJ-1.551]` states the two endpoints of that
  band at `lj-1.551-report.md:302-304`; 688,062,464 − 551,796,736
  = 136,265,728.
- Archive quotes of the return, checked: `archive/dev/LJ-dispatch-index.md:135`,
  `:137`, `:142`; `archive/dev/JOURNAL.md:1063`;
  `archive/dev/JOURNAL-archived.md:4066`; `dev/ARCHIVE.md:3`.
- Literature quote of the return, checked:
  `dev/literature/truncation-and-selection.md:7`.
- `dev/pod/direction.md:37` and `AGENTS.md:45`, as cited.
- `dev/LESSONS.md:1375` (D-10), `:3752` (C-42), `:2297` (C-22).
- `archive/dev/DD-archived.md:22` (DD4), as cited for W2.

Defects, none overturning:

- **D1.** Report table row for `[LJ-1.512]` cites
  `lj-1.512-report.md:41-42` for "54 and 16, and FIVE". The five
  names are at `:41-42`. The 16 is at `:44`. The probe comment at
  `Probe575.agda:436-437` cites `:47-49` for the same five; those
  lines are the "remaining 14 are not yet refuted" sentence, not
  the five names.
- **D2.** `lj-1.575-report.md:268-270` cites
  `agents/tasks/LJ-1-563/lj-1.563-report.md:517-523` as "the four
  consuming call sites" of the repaired tmVal fields. Those lines
  name the consumers of `consK-forall`, `consK-allin` and
  `consK-exist`. They do not name the consumers of `valV`, `valW`
  or `wKfact`. The tmVal consumers are the six parameters in D-10
  of this review plus `AtomLeaf` and `BndLeaf`. The next-brief
  item that inherits this cite is pointed at the wrong four sites.
  The NO-GO does not use those sites.
- **D3.** `lj-1.575-report.md:418-419` as a cite for "the record's
  field quantifies over `B`" is `[LJ-1.551]`'s sizing sentence
  about `envSetK`. The quantification itself is
  `src/L/Condensation/TwelveAgree.lagda.md:306-310`. The claim is
  true. The cited lines are the wrong home of it.
- **D4.** `gUnCodesK`'s last conjunct sits at
  `src/L/Condensation.lagda.md:7276`. The return's range
  `:7262-7275` stops one line early. The parameter is still there.

## 3. QUESTION THREE: IS THE PREDECESSOR'S ENUMERATION COMPLETE

The enumeration that carries the NO-GO is complete. Two neighbouring
censuses are not. Neither neighbour can inhabit `TFacts`.

Complete, and I re-counted:

- Fifty-nine field positions in `TFacts`. I counted the field names
  from `TwelveAgree.lagda.md:133` to `:332`.
- The ten not collected, by name, match `[LJ-1.563]`'s list at
  `lj-1.563-report.md:345-351`: `codesK`, `codesK-un`, `t0eq`,
  `t1eq`, `t0K`, `valV`, `valW`, `wKfact`, `envSetK`,
  `consK-exist`.
- The three tmVal fields of `TFacts` are the only `tmValAt` fields
  of that record. `LFacts` has two, `UFacts` has one. Six record
  fields, all six refuted by projection onto `Shape`.
- The six quantified-tag module parameters exist at the six cited
  starts. No further `tmValAt` parameter of that shape sits in
  `src/L/Condensation.lagda.md`.
- `AtomLeaf` and `BndLeaf` are a different shape, and the report
  says so. I confirmed `aK` beside the tag cell.

Incomplete, and none of it saves the record:

- **E1.** C-42's "TWENTY declarations" is the right mention count
  in the condensation chain, imports and comments excluded. Three
  of those twenty are satisfaction aliases (`tVM` and `tWM` at
  `src/L/Condensation.lagda.md:4309-4321`, and `tVM` at `:4915-4920`).
  They do not conclude a K membership. Two are transfers (`TmVal.out`
  `:3085`, `TmVal.in'` `:3124`) and conclude a formula. Fifteen
  conclude a K membership: the six record fields, the six
  quantified-tag parameters, and the three leaf parameters. The
  report's sentence "SEVENTEEN of them conclude a K membership"
  (`lj-1.575-report.md:221-222`) is therefore false by two. Its
  own table lists 6 + 6 + 3 membership sites and two n/a
  transfers, and it omits the three aliases. The six refuted sites
  and the six unmeasured same-shape parameters are still the right
  six plus six.
- **E2.** "THREE OF THE FIFTY-NINE ARE FALSE"
  (`lj-1.575-report.md:111`) is the tmVal count, written as if it
  were the false-field count for the record. `[LJ-1.510]` already
  named `consK-exist`, `consK-forall` and `consK-allin` false at
  `KValue`'s frame
  (`agents/tasks/LJ-1-510/lj-1.510-report.md:445-447`). `[LJ-1.563]`
  later collected the last two with extras. `[LJ-1.575]` lists
  `consK-exist` as unsupplied (row 10) and does not re-open 510.
  At `KValue`'s frame the record is uninhabited for at least those
  three consK reasons as well. That makes the NO-GO stronger, not
  weaker. The new fact this return owns is the stronger one: the
  three tmVal fields are false at every frame, with `γ` and `Ks`
  free (`Probe575.agda:88-90`).

W3's enumeration of extra hypotheses is the union the brief named,
inhabited at one pinning of the five free cells. It is not a proof
that those extras hold for every quantified binder. The body says
that (`lj-1.575-report.md:211-214`). I do not ask it to be more.

W2 is answered at `lj-1.575-report.md:363-377`. `Shape`,
`ThreeRepaired` and `Repair` are stated once at a generic carrier.
W3, as amended by A21, is named in the brief and written by the
coder; I do not ask a coder's return whether it specified the
probe. W4 is answered: nothing is retired. W7 does not apply. W8
does not abort this task: the falsehood is a dropped `tK` on a
disjunction the tree already defines, not an axiom the literature
names.

The brief did not foreclose a GO that was available. Premise 2's
54/5 count is wrong, as the body says, and D-10 in the brief is
what licensed the stop. No term of `TFacts` can be written in this
tree without a `postulate`, a hole, or a statement change in
`src/`. The coder's scope forbids the third
(`agents/tasks/LJ-1-575/LJ-1.575.md:13`).

## ARCHIVE USED

- `archive/dev/JOURNAL.md`. **READ AND USED.** At
  `archive/dev/JOURNAL.md:1063` the line reads
  "- **`[LJ-1.233]:247` calls the `TwelveAgree:519-522` comment STALE. It is NOT.**"
  I used it to check the predecessor's own archive quote. The
  predecessor is right that `[LJ-1.251]` checked indices, not
  inhabitation of `TFacts`.
- `archive/dev/DD-archived.md`. **READ AND USED.** At
  `archive/dev/DD-archived.md:35` the line reads
  "The questions are: is the refusal correct on its own numbers; is the measurement sound; did the BRIEF cause the outcome; and is there a cure the return missed."
  Those four are the lens of this review. At
  `archive/dev/DD-archived.md:22` the line is DD4, which the
  predecessor cited for W2. I re-read it to confirm that cite.
- `dev/ARCHIVE.md`. **READ AND USED.** At `dev/ARCHIVE.md:3` the
  line reads
  "The registry of Bedrock's retired modules. One entry per module, written at"
  Nothing is retired by the predecessor, so the registry gains no
  row. I used the line only to confirm the predecessor's decline
  of a W4 row.
- `archive/dev/ORCHESTRATION.md`. **READ, NOT USED, DECLINED.** At
  `archive/dev/ORCHESTRATION.md:1` the line reads
  "# ORCHESTRATION: the orchestrator's operating rules"
  It is archived operating text. The three questions I must answer
  live in `dev/memos/LJ-4-pod-program-design.md:2853-2858`, not
  here.
- `archive/dev/PLAN-archived.md`. **READ, NOT USED, DECLINED.** At
  `archive/dev/PLAN-archived.md:1` the line reads
  "# ARCHIVED 2026-08-20"
  It is a frozen construction registry. It does not decide whether
  `TFacts` has a value.

## LITERATURE USED

- `dev/literature/devlin-II5.md`. **READ, NOT USED, DECLINED.** At
  `dev/literature/devlin-II5.md:1` the line reads
  "# Devlin II.5: the Condensation Lemma and the GCH in L"
  This review is of a formalisation defect: a fact-block field that
  dropped `tK` on `tmValAt`'s right disjunct. No line of Devlin II.5
  would inhabit `TFacts` or refute `tfacts-absurd`.
- `dev/literature/BIBLIOGRAPHY.md`. **READ, NOT USED, DECLINED.** At
  `dev/literature/BIBLIOGRAPHY.md:1` the line reads
  "# Bibliography for the rud route"
  No source in it is a consumer of `TFacts`.
- `dev/literature/digest.md`. **READ, NOT USED, DECLINED.** At
  `dev/literature/digest.md:1` the line reads
  "# Digest: the orthodox form of the rud route, pinned from the collected literature"
  This task does not choose a route.
- `dev/literature/geology.md`. **READ, NOT USED, DECLINED.** At
  `dev/literature/geology.md:1` the line reads
  "# Geology dossier: set-theoretic geology sources and the five questions"
  Geology is not the condensation fact-block.
- `dev/literature/devlin-errata.md`. **READ, NOT USED, DECLINED.** At
  `dev/literature/devlin-errata.md:1` the line reads
  "# Devlin errata: documented error classes (do-not-repeat checklist)"
  The dropped membership is a tree defect, not a Devlin erratum.

W8 does not fire. The literature does not name this shape as an
axiom with no condition the tree meets. The machine already has
the honest form, `Fact.tmValK`, with the two memberships the
record dropped.

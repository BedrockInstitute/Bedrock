# LJ-1.500: adversarial review of the return of LJ-1.500#1

## HEAD
head_slot: mathematician_adversarial
machine: shared
verdict: upheld

The return under attack is `agents/tasks/LJ-1-500/lj-1.500-report.md`,
the return of dispatch LJ-1.500#1. The instance record, in the main
checkout (`dev/pod/transitions/2026-08.jsonl`, seq 1950; the worktree
copy stops at LJ-1.399), reads: role `coder`, model `claude-opus-5`,
effort `xhigh`, `heads_sha256` `0a6fdffa`, attempt 0, RETURNED
2026-08-21T21:09:04Z, why `pid dead`. The digest matches the worktree
`.pod` stamp. Its verdict line is **GO**. This review upholds that
verdict. The predecessor stated a GO and not a NO-GO, so the closing row
`sys-critic-upheld-no-go` does not apply to this task.

THE INVARIANT HOLDS. The author of the return under attack is the coder
head of dispatch #1. This critic is the mathematician head of attempt 2
(seq 1962). The critic is not the author.

SCOPE NOTE. Before this review was written, this path held the return of
the attempt-2 `coder_adversarial` dispatch (RETURNED 21:19:36Z, seq
1957). The brief of this dispatch names this path as its only write, so
this review replaces that file. Every finding below was re-derived from
the artifacts, and every number below was re-measured by this review.

## WHAT THIS REVIEW READ AND RAN

- The return, the work brief `agents/tasks/LJ-1-500/LJ-1.500.md`, and
  the probe `agents/tasks/LJ-1-500/Probe500.agda` (374 lines, the only
  `.agda` file in the task directory).
- Every artifact in `agents/tasks/LJ-1-500/runs/`: `w3-0` to `w3-3`,
  `full-0` to `full-8`, `witness-1` to `witness-3`, and the two
  program-generated acceptance records `accept-1.out` and `accept-2.out`.
- The acceptance facts of dispatch #1 (`runs/accept-1.out`): probe rc 0
  in 2.09 s, obligations delta -1, obligations open 0, in-fence lines 0,
  heap_wall false, error_class `lint`, exit 1, 31 changed files, none
  foreign or refused.
- This review re-ran the probe itself, three forced rechecks, interface
  deleted each time, one Agda process, `GHCRTS=-A64m -I0 -M8g` as the
  program sets on this pane: rc 0 in 3.29, 3.23 and 3.22 s. The
  interface store is a declared `toolchain` class
  (`dev/build-manifest.toml`, entry `2.8.0/**`). No heap event.

## QUESTION 1: DOES THE VERDICT LINE MATCH ITS OWN BODY

**YES.**

The line (`lj-1.500-report.md:143-166`) rests on three claims. Each is
true and each was re-measured by this review:

- The obligation stands and typechecks. `codesK-family` is at
  `Probe500.agda:365-372`, with the top-level alias at `:374` that the
  witness meter reads. This review's three forced rechecks all exited 0.
  The return's median 3.16 s (`runs/full-6.time` to `full-8.time`:
  3.15, 3.17, 3.16) is correct. The program measured the same file
  green twice after the return (rc 0 in 2.09 s at `runs/accept-1.out`,
  2.19 s at `runs/accept-2.out`).
- The witness meter passes on the standing file. `runs/witness-3.out`
  reads "0 UNRESOLVED of 1, 2.57 s, probe_red=False", and both
  acceptance records corroborate it independently
  (`obligations_probe_red` false, `witness_seconds` 2.27 and 2.17).
- W3 is GO. `ar-is-numeral` (`Probe500.agda:78-84`) typechecks inside
  the standing file, and the `w3-1` to `w3-3` artifacts read 1.34,
  1.34, 1.35 s, so the stated median 1.34 s is correct.

The body's disclosures match the line. The two telescope hypotheses the
frame does not pay for, `C∈K` and `arNumC`, are named, kept out of the
membership module (`Probe500.agda:145-160` against `:225-229`), and
priced as one debt. The verdict paragraph lists what the GO does not do.

The brief's stop path was answered in substance, not evaded. The brief
says: if nothing supplies the numeral, STOP AND SAY SO, and report the
three memberships separately. The required section exists
(`lj-1.500-report.md:59-101`), says at `file:line` where the numeral
reading comes from, and states that nothing at the frame supplies it.
The three memberships are delivered separately, with no numeral input in
the stored type (`module Mem`, `Probe500.agda:145-215`). The fourth
conjunct is not fabricated: it is derived (`arityNumAtL-out`, `pr-inj`,
`PT.map`, `Probe500.agda:82-84`) under a named and typed hypothesis,
`arNumC`. A stop would also have been defensible. A GO with the input
named and gated is the stronger and the honest return, and the brief's
own GO economics ("A GO PAYS TWO MORE FIELDS AND NAMES THE NUMERAL
SOURCE FOR TEN", `LJ-1.500.md`) is what the return delivers.

The program's own branch table reads the six facts the same way: branch
`go` (`LJ-1.500.md:128`, condition at `:135`, obligations delta -1,
exit 0, no heap wall) matched the return. The escalation to the critic
chain came from acceptance conjunct 6, the survey form, and not from the
verdict. See Finding 1.

One wobble exists and misstates no number the verdict uses: the return
calls `runs/full-5` "the full file, in its final shape" and later says
"Only `runs/full-6` to `full-8` and `runs/witness-3` measure the file
that stands". Both hold only under a shape-versus-bytes reading. The
median is honestly taken from `full-6` to `full-8`.

## QUESTION 2: IS EVERY LOAD-BEARING CLAIM BACKED BY A file:line THAT RESOLVES TODAY

**YES.** This review opened every load-bearing citation. All resolve.

In `src/L/Condensation/TwelveAgree.lagda.md`: `codesK` at `:162-167`
with the truncation at `:167`; `codesK-un` at `:168-172` with the
truncation at `:172`; the record shape at `:129-131`; the stored-type
note at `:116-119`; `transK` at `:262`; the swapped-binder derivation at
`:347-353`; the numeral-source comment at `:303-306`; the untruncated
`envSetK` at `:306`; the pass-throughs at `:421-422` and `:462-463`.
In `src/L/Condensation.lagda.md`: `KFacts.arityK` at `:6114`; `KValue`
at `:7380`; the chain comment at `:2812-2819`; `ChainZ` at `:2820` with
the public pieces at `:2859`, `:2868`, `:2884`; `wCodesK` at
`:7239-7245` with the two-level premise. In
`src/L/Coding/CodeSet.lagda.md`: `arityNumAtL` at `:185-187`,
`arityNumAtL-out` at `:189-199`. In `src/V/Coding.lagda.md`: `pr-inj`
at `:178-179`.

Predecessors: the `[LJ-1.495]` GO quote at
`agents/tasks/LJ-1-495/lj-1.495-report.md:71` occurs verbatim; the
`arityK` discard at `:216-218`; the frame lengths at `:56-60`;
`Probe495.agda:166-199` and `:168` hold what the return says.
`[LJ-1.493]` at `agents/tasks/LJ-1-493/lj-1.493-report.md:74-76`.
`[LJ-1.483]` at `agents/tasks/LJ-1-483/lj-1.483-report.md:93-94`.
`[LJ-1.496]` at `agents/tasks/LJ-1-496/lj-1.496-report.md:76-80`.
`[LJ-1.347]`: the FALSE quote at `:8` verbatim; the wall table at
`:36-39` (1.73 s, 373.93 s heap exhausted, 406.01 s heap exhausted,
1.64 s); the countermodel at `:115-120`; the public-access record at
`:124`; the five probes at `:126-127`. The audit rule at
`dev/pod/audit-2026-08-20.md:34` (heading; body `:36-44`). The
direction line at `dev/pod/direction.md:37`. Both literature quotes
occur at their lines (`dev/literature/truncation-and-selection.md:146`
and `:289`).

Probe anchors were checked line by line and all match: `:78-84`,
`:92-105`, `:124-130`, `:145-215`, `:160-171`, `:175-195`, `:192-194`,
`:198-215`, `:213-214`, `:225-250`, `:226-228`, `:230-239`, `:237`,
`:241-250`, `:248`, `:259-265`, `:267-332`, `:334-341`, `:359-361`,
`:363`, `:365-372`, `:374`; 374 lines total; `six` is 66 lines;
`arityK-direct` is 8 lines; `Mem` is 71 and `Num` is 26 lines. The probe
names no `EnvSet`, `Generic`, `envSetAt` or `envOverAt` (this review
grepped the file: no hit).

Counts re-measured by this review, all exact:

- The truncation string occurs 87 times in `src/`: 50 in
  `src/L/Condensation.lagda.md`, 11 in
  `src/L/Condensation/TwelveAgree.lagda.md`, 10 in
  `src/L/Coding/EnvSupply.lagda.md`, 8 in
  `src/L/Condensation/LowerAgree.lagda.md`, 8 in
  `src/L/Condensation/UpperAgree.lagda.md`.
- Untruncated `fst ar ≡ # n` in a field or parameter type: 3, at
  `TwelveAgree.lagda.md:306`, `EnvSupply.lagda.md:133` and
  `EnvSupply.lagda.md:140`. The fourth raw hit
  (`TwelveAgree.lagda.md:305`) is a comment.
- Inside `TFacts` (`:132-332`): the truncation occurs at exactly 11
  lines, `:167`, `:172`, `:187`, `:193`, `:199`, `:205`, `:211`,
  `:218`, `:225`, `:232`, `:239`. That is 2 producers and 9 consumers.
- `TFacts` has 59 fields, counting also the four sub-scripted fields
  `subK₁-and`, `subK₀-and`, `subK₁-imp`, `subK₀-imp`
  (`src/L/Condensation/TwelveAgree.lagda.md:266-288`).
- The `C` slot `lookup (suc (suc zero)) γ'` appears 4 times in the
  `TFacts` block, at `:162`, `:168`, `:173`, `:177`, each a bare
  membership premise. COUNT beyond a bare membership: 0, as the return
  says.
- The 12 fed rows sit at exactly the cited lines:
  `codesK` at `LowerAgree.lagda.md:258,265,272,278,284` and
  `UpperAgree.lagda.md:283,290`; `codesK-un` at
  `LowerAgree.lagda.md:290` and `UpperAgree.lagda.md:256,262,267,275`.
- The run tables: `full-0` 2.87 s; `full-1` to `full-4` 3.03, 3.08,
  3.04, 3.01 s, median 3.04 s; `full-5` 3.32 s; `w3-0` 1.49 s with peak
  RSS 337494016; `witness-1` and `witness-2` both "0 UNRESOLVED of 1".
  All match the return's provenance paragraph.
- The decline claims hold: `codesK`, `arityNum`, `ChainZ`, `KFactsCons`
  give 0 hits in `archive/dev/JOURNAL.md`,
  `archive/dev/JOURNAL-archived.md` and `dev/ARCHIVE.md`;
  `archive/dev/DECISIONS-archived.md` is 61 lines; `.venv/bin/python`
  is absent in this worktree.

One item is not re-checkable today: the 63-line W3-only file. The full
probe overwrote it. The `w3-*.out` artifacts all read "Checking
LJ-1-500.Probe500", which fits a W3-only `Probe500.agda` at that stage,
and the return discloses the earlier file states. The GO does not rest
on the 63-line figure.

## QUESTION 3: IS THE PREDECESSOR'S ENUMERATION COMPLETE

**COMPLETE FOR THE VERDICT, WITH THREE GAPS NAMED.** None overturns the
GO.

### Finding 1. The survey-quote form failed the gate, and it will fail again

`check-survey-quotes.py LJ-1-500` fails with class `lint`:

    quote: archive/dev/LJ-dispatch-index.md:433 quotes text the file does not hold

The three quoted rows are SUBSTANTIVELY ACCURATE. This review opened the
file: the rows occur today at `archive/dev/LJ-dispatch-index.md:400`,
`:401` and `:433`. The defect is the FORM, and this review re-derived
the mechanism from the checker source (`scripts/pod/check-survey-quotes.py`,
`QUOTE` at the pattern block, `audit_quotes` and `bullets`):

- The return renders its quotes as markdown blockquotes. The checker
  reads a quote only inside double quotes, corner quotes or backticks,
  12 characters or more, so the three blockquote rows are invisible to
  it. The cites at `:400` and `:401` collect no quote.
- The same bullet ends with prose that carries short backtick terms
  (`LJ-1.350`, `arityNumAtL`, each under 12 characters). A short span
  does not match, so the checker pairs a backtick of one term with the
  backtick of the next. The text between the terms becomes phantom
  quotes. This review ran the checker's own parser on the bullet: two
  phantom phrases, " row is what sent me to " and " before I wrote any
  Agda: it says the bound is ", each bind to the nearest preceding
  cite, which is `:433`. Neither occurs at `:433`, so the gate fails.
- The two blockquotes in `LITERATURE USED` survive only because
  `dev/literature/` is live and non-frozen in the checker: a mismatch
  there is counted, never failed.

The brief did not cause this. The brief's ARCHIVE block states the duty
and the accepted quote forms; the return chose the blockquote form. The
cure belongs to future returns, since a record is never rewritten: quote
inside double quotes, 12 characters or more with a space, and keep short
backtick terms out of any bullet that carries a cite.

This review adds what the routing needs to hear: the failure is
STRUCTURAL for this task. The gate judges the pair (work brief, task
report). `report_of` in `scripts/pod/check-survey-quotes.py` takes the
file whose stem ends in `-report` or `-review`
(`scripts/agents_tree.py:72`, `REPORT_SUFFIXES`). In this task directory
that is `lj-1.500-report.md` alone; `review-LJ-1-500-1.md` and
`review-of-LJ-1-500-1.md` end in `-1`. So every future acceptance of
LJ-1.500 re-judges the frozen coder report and re-fails conjunct 6, as
`runs/accept-2.out` already shows. No writer inside this task can cure
that, and no critic return should be asked to. The exit routing is the
program's.

### Finding 2. The cure-side enumeration misses the IN direction

Section 5 of the return (`lj-1.500-report.md:434-459`) names `arNumC`
as the one remaining question and names the OUT-direction chain
(`arityNumAtL-out`, `pr-inj`). The tree also carries the IN direction,
built and public:

- `arityNumAtL-in` at `src/L/Coding/CodeSet.lagda.md:201-204`: from a
  slot equation `fst (lookup c γ) ≡ pr (# m) (fst z)` it closes the
  satisfaction.
- `isCodeAnyAt` at `src/L/Choice/Faithful.lagda.md:287-288` conjoins
  the arity conjunct into a code predicate, and `codeAnyAt-in` at
  `:291-296` establishes it for codes built by `keyS`.

These do NOT discharge `arNumC` at a free `C` slot: the hypothesis of
`arityNumAtL-in` is itself the numeral-pair shape. So the return's
claim "AT THIS FRAME, NOTHING SUPPLIES IT" stands. But once an
instantiation pins `C` to the real code set, the IN direction is the
existing tool that pays the one debt. The omission is the sharper
because the return itself quoted the archive row at
`archive/dev/LJ-dispatch-index.md:433`, whose text ends "arityNumAtL's
IN direction pays, and the upstream debt LJ-1.360 feared is GONE". The
return deployed that row as evidence and did not carry its IN half into
section 5.

### Finding 3. The one-debt price does not pay the untruncated consumer

The sweep paragraph (`lj-1.500-report.md:425-433`) says: "It is ONE
debt, at the two producers, and paying it once pays the whole family."
The family has ten sites, and the tenth is different. `envSetK`
(`src/L/Condensation/TwelveAgree.lagda.md:306`) consumes the numeral
reading UNTRUNCATED, `fst ar ≡ # n`. `arNumC`, and
`arityNumAtL-out` behind it, deliver only the truncated form, and
nothing the return names escapes it: no numeral-uniqueness lemma is
cited, and the return's own W3 section rests on the fact that the
truncation never has to be escaped. So paying `arNumC` once pays the
nine truncated consumers; the tenth site needs either an untruncated
payment at the instantiation or an escape lemma, and neither is named.
The GO does not rest on this: the paragraph ends "I price nothing
further", and the sweep table itself keeps the two forms distinct. The
next brief should hear the gap.

### Notes

1. The work brief never states W2, although slot clause W2 asks the
   brief to state it and the return to answer it. The return answers it
   anyway (`lj-1.500-report.md:168-217`), and the probe does build at a
   generic carrier: `Split`, `Mem`, `Num` at generic `m`, `CodesPair`
   at generic `n`, instantiated at `n = 9` (`Probe500.agda:365`). The
   omission is the brief's, and it caused no outcome.
2. The instance returned with why `pid dead`. The report file is
   complete on its face, the acceptance measured what it wrote, and
   both acceptance records re-ran the probe green. No action follows.
3. Section 3 of the return says `module Mem` "has four parameters, `C`,
   `K`, `γ`, `arityK` and `C∈K`": five names for "four". A prose slip;
   the stored type is checkable and is what the claim rests on.
4. The `full-5` wobble of Question 1.

## THE FOUR QUESTIONS OF SECTION 6.6, ONE LINE EACH

- Verdict correct on its own numbers: yes, and the numbers re-measure.
- Measurement sound: yes. One caliber, one process, forced rechecks,
  honest run provenance, program-side corroboration twice.
- Did the brief cause the outcome: no. The conjunct-6 failure is the
  return's form; the W2 omission caused nothing.
- A cure the return missed: the IN-direction assets of Finding 2 and
  the untruncated-consumer gap of Finding 3. Nothing else. The refusal
  to extend `[LJ-1.347]` from `wCodesK` to `codesK` is correct under
  C-42 and AGENTS.md:45: a refutation measures the site it names.

## ARCHIVE USED

- archive/dev/LJ-dispatch-index.md : READ. The return quotes three rows
  of it and the gate disputed the third. Quote at
  archive/dev/LJ-dispatch-index.md:400 : "Settle the arity-numeral
  conjunct". Quote at archive/dev/LJ-dispatch-index.md:433 :
  "arityNumAtL's IN direction pays, and the upstream debt LJ-1.360
  feared is GONE". Both occur at their lines today. The second row is
  the evidence behind Finding 2.
- archive/dev/JOURNAL.md : not read. Declined. This review searched it
  for `codesK`, `arityNum`, `ChainZ` and `KFactsCons` and measured 0
  hits, so the return's decline claim holds and no row of it bears on a
  code reader.
- archive/dev/ORCHESTRATION.md : not read. Declined. The acceptance
  path under review is live code, and no retired-route orchestration
  question arose.
- archive/dev/DD-archived.md : not read. Declined. No DD decision text
  is load-bearing in the return under review; the law codes it cites
  live in `dev/LESSONS.md`.
- archive/dev/PLAN-archived.md : not read. Declined. The plan tested
  here is the live brief of LJ-1.500, and no archived plan was
  consulted.

## LITERATURE USED

- dev/literature/truncation-and-selection.md : READ, to check the two
  quotes the return leans on. Quote at
  dev/literature/truncation-and-selection.md:289 : "Is the goal a
  proposition?". Quote at dev/literature/truncation-and-selection.md:146
  : "The constraint the route carries". Both occur at their lines, so
  the return's use of `PT.map` over a truncated goal is the form the
  digest prescribes.
- dev/literature/devlin-II5.md : not used. Declined. No source-level
  reading question is in scope. This review searched it: the `arity` and
  code-set hits concern the elementarity of the definable hull, which is
  upstream of and not load-bearing for the internal decoding under
  review.
- dev/literature/BIBLIOGRAPHY.md : not used. Declined. This review
  consulted no new source.
- dev/literature/digest.md : not read. Declined. No route choice is
  under review; the brief fixed the field and the frame.
- dev/literature/geology.md : not surveyed. Declined. The layering of
  the tree is not in question in this review.
- dev/literature/devlin-errata.md : not used. Declined. No Devlin text
  is load-bearing in the return under review.

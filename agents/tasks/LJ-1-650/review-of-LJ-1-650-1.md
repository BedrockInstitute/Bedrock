# review-of-LJ-1-650-1: the NO-GO is UPHELD

## HEAD
head_slot: mathematician_adversarial
machine: shared
task: LJ-1.650, review of LJ-1.650#1
attacked return: agents/tasks/LJ-1-650/lj-1.650-report.md with its stop
agents/tasks/LJ-1-650/review-of-coded-cover.md
verdict: **upheld**

## 1. WHAT WAS ATTACKED, AND ON WHAT RECORD

The attacked return is a stated STOP: the obligation
`agents/tasks/LJ-1-650/Probe650.agda::coded-cover-from-keystone` was not
built, the meter reads it `missing`, `1 UNRESOLVED of 1`, `probe_red=False`
(`agents/tasks/LJ-1-650/runs/meter-obligation.out`), and 18 other names are
green, `0 UNRESOLVED of 18` (`agents/tasks/LJ-1-650/runs/meter-names.out`).
I searched every `.agda` under the task home: no file defines the name. The
probe states the obligation's TYPE at
`agents/tasks/LJ-1-650/Probe650.agda:96-97` and inhabits nothing of it.

**The transitions record ends before the instance.**
`dev/pod/transitions/2026-08.jsonl` has 4177 lines. Its last line, 4177, is
this task's only line: attempt 0, `to: READY`, `heads_sha256` `cd49070c`, at
2026-08-26T01:34:12Z. It carries no `model` and no `effort` for the run under
attack, so, as this brief orders, I used the acceptance arm. Its six facts:
exit 0, obligations delta 0 with 1 open, error class None, 21 changed files
all own, in-fence lines 0, wall 2.4 s, no heap wall
(`agents/tasks/LJ-1-650/runs/accept-1.out`).

## 2. THE FOUR, APPLIED

The four are DD25's own, quoted at `archive/dev/DD-archived.md:35`: "The
questions are: is the refusal correct on its own numbers; is the measurement
sound; did the BRIEF cause the outcome; and is there a cure the return
missed."

**1. Correct on its own numbers. YES.** The obligation is absent and metered
absent (section 1). The two Agda errors are quoted word for word: the
`[UnequalTerms]` block in `review-of-coded-cover.md` section 2 occurs
identically in `runs/nokey-1.out` and `runs/nokey-2.out`, both `EXIT=42`. The
keystone's type is `Probe462.agda:118-121` and `CodedCover` is
`Probe595.agda:352-356`; both restatements in `Probe650.agda:82-96` match
them. Every run number in the report's section 6 table matches its `.out`
file, with one exception in the stop file (defect D1, section 5).

**2. Sound. YES.** All three `.agda` files typecheck under the acceptance arm
(rc 0, 2.23 to 2.40 s). The one heap wall is labeled a FRAME datum, and the
restructure is the only difference between `runs/floor-1.out` (exit 251,
63.18 s, 1,911,226,368 bytes, last line `Checking LJ-1-570.Probe570`) and
`runs/floor-2.out` (exit 0, 3.67 s, 740,179,968 bytes). The three files that
cannot typecheck are named `.agda.txt`, as the brief ordered. The W2
duplication of `[LJ-1.595]`'s section 4 and section 5 facts is priced and
excused inside the file that carries it, by that wall
(`agents/tasks/LJ-1-650/Probe650.agda:8-23`), and the report says the import
is preferred where it is affordable.

**3. Did the BRIEF cause the outcome. PARTLY, AND UPSTREAM.** Premise 3 of
the brief reads "THAT DESTINATION IS `[LJ-1.646]`'s OBLIGATION"
(`agents/tasks/LJ-1-650/LJ-1.650.md`, PREMISES). The return measured that the
destination is right and the address is wrong: the keystone is a semantic
statement and `CodedCover` needs syntax. That is a false premise in the
brief, not a failure of the worker. The brief itself priced the NO-GO branch,
so it did not foreclose the answer it asked for.

**4. A missed cure. NONE THAT OVERTURNS.** The strongest untried attack is
the constant-function reading: the obligation type is an arrow
(`Probe650.agda:96-97`), so a term may IGNORE the keystone hypothesis and
still satisfy the obligation, if `CodedCover` has tree supply. The stop
survives it: the brief's own "WHAT IS DELIVERED ALREADY" says `CodedCover`
has supply 0, and the probe's best terms toward it consume hypotheses
(`coded-cover-from-internal`, `Probe650.agda:289`;
`coded-cover-from-level`, `Probe650.agda:385`). At a non-ordinal code the
keystone gives nothing and the tree gives nothing. The cures the return did
name all stand on measurements I re-verified (section 6).

## 3. THE THREE, ANSWERED

**1. Does the verdict LINE match its own BODY? YES.** The HEAD verdict is
STOP on the obligation, W3 GO, the residue at non-ordinal values, and closure
from one formula. Each claim has its body section and its run file:
sentence 1 is section 3, sentence 2 is section 2, sentence 3 is
`Probe650.agda:235-260` with `runs/p-final.out`, sentence 4 is
`Probe650.agda:385-386`. Two blemishes, D1 and D3 below, touch wording and
one number, not the verdict.

**2. Is every load-bearing claim backed by a `file:line` that resolves
today? YES, WITH TWO NAMED FAILURES THAT DO NOT CARRY THE VERDICT.** I opened
every load-bearing citation today. Resolving: `Probe462.agda:118-121`,
`Probe595.agda:324-352` and `:352-356`, `src/L/Hull.lagda.md:72-74`, `:79-81`
(`search` at `leastOf`), `:105-107` (`val-wit`), `:120-142` (`closed`),
`lj-1.595-report.md:154-156`, `:167-169`, `:171-179`,
`runs/p-1.out` of LJ-1.595 (2,527,182,848 bytes) and its `p-final.out`
(8.68 s, 1,002,045,440 bytes), `Probe647.agda:165-167`,
`lj-1.649-report.md:190-197`, `dev/literature/devlin-II5.md:214-217` and
`:219`, `dev/literature/truncation-and-selection.md:25` and `:163-165`, and
the four archive quotes in the return's own ARCHIVE USED block. The probe is
427 lines, 249 non-blank non-comment, `skolemCode` spans 32 lines at
`:118-149`, `W3.agda` holds 63 non-blank non-comment lines, `_build/` holds
722 `.agdai` files now: all as stated. I also re-verified by search what the
return asserts: `IsOrd (Lset` and `∈ˢ Lset (Lset` occur NOWHERE in `src/`, so
the two hypotheses marked NOT IN THE TREE at `Probe650.agda:420-421` are
indeed absent. Failing: D1 and D2 below.

**3. Is the enumeration complete? IN SUBSTANCE YES, WITH ONE CASE COVERED BUT
NOT NAMED.** The return enumerates the obligation's absence, the two error
slices, the free ordinal row, the true closure, the queue correction, the
binder difference, the C-42 sweep, `skolemCode` reuse, and the heap datum.
The unnamed case is the constant-function reading of section 2 above. It is
answered in substance, because supply 0 at non-ordinal codes is measured in
the same probe, but a stop that claims "no term composes it" should name the
reading under which a term need not compose anything. This is an addition,
not an overturn.

## 4. WHY THE NO-GO STANDS

Three measured facts, each checked today:

1. The keystone applies only where `IsOrd (fst (val c))` already holds
   (`Probe462.agda:118-121`). At a non-ordinal code it supplies nothing, and
   there the tree also supplies nothing (`LJ-1.650.md`, WHAT IS DELIVERED
   ALREADY).
2. Where the keystone does apply, its route needs two facts the tree does not
   have (`Probe650.agda:420-421`, and my search of `src/`), and Agda names
   the first of them itself (`runs/nokey-2.out`).
3. That same row is free with neither fact and no keystone
   (`coded-cover-at-ordinal`, `Probe650.agda:235-260`), so the keystone adds
   nothing anywhere.

The return does not claim the obligation's TYPE is false, and says so in the
stop's section 6. That restraint is correct: `coded-cover-from-level`
(`Probe650.agda:385-386`) shows the type closes from one formula as a
hypothesis.

## 5. DEFECTS FOUND IN THE RETURN

- **D1, a wrong number in the stop file.** `review-of-coded-cover.md` says
  the probe is green "(`runs/p-final.out`, exit 0 in 2.88 s)". The file says
  `4.60 real` and `695812096 maximum resident set size`. The report's own
  section 6 table has it right. The exit and the greenness stand; the seconds
  do not.
- **D2, an off-by-one citation.** The report's section 5.4 cites
  `lj-1.649-report.md:341-346` for the advice about `pix-closed-op`. The
  advice sentence is at `:347`: "**`[LJ-1.648]` AND `[LJ-1.650]` SHOULD TAKE
  `pix-closed-op`, NOT REPROVE" and continues at `:348`. The cited range
  carries the neighboring `lset-code` advice instead. The claim is true; the
  citation does not back it.
- **D3, a wording imprecision.** The report's table gives
  `coded-cover-at-ordinal` hypothesis "none", and HEAD sentence 3 says
  "unconditional". The term's type carries `IsOrd (fst (val c))` at
  `Probe650.agda:236`. "At an ordinal value" is the restriction, and "no
  keystone, no level formula" is accurate, but "unconditional" and "none"
  overstate a row that carries the ordinality in its type.
- **D4, in the dispatch, not the return.** This review brief cites the three
  questions at `dev/memos/LJ-4-pod-program-design.md:2853-2858`. That range
  carries other text today. The list is at `:2984-2988`. Recorded for the
  program; no action from this slot.

None of D1 to D3 changes the verdict. D1 and D2 are the kind of defect the
Boundary's evidence rule exists for, and the next brief that copies those
lines inherits them.

## 6. WHAT THE QUEUE KEEPS

- The keystone task is still queued and unbuilt:
  `dev/pod/queue.toml:6210` plans LJ-1.646 as "THE KEYSTONE", and no
  `agents/tasks/LJ-1-646/` directory exists. The return's correction, to
  state the level formula as `LevelFormula` and not as `lset-code-ord`, is
  sound on what I verified: `internal-from-level` reaches `InternalCover`
  from one existential (`Probe650.agda:352-382`), `coded-cover-from-level`
  closes `CodedCover` (`:385-386`), and the other direction needs the index
  substitution LJ-1.595 recorded as an unpriced renaming
  (`lj-1.595-report.md:167-169`).
- The C-42 sweep is the next action and is a recon task. The two sites the
  return names without search both check: `Probe647.agda:165-167` takes
  `LsetCodeOrd`, and LJ-1.649 measured the fifth fact
  (`lj-1.649-report.md:190-197`). The sweep should also ask the
  constant-function question at each site: whether the consumer's target
  already has tree supply, in which case the keystone hypothesis is free
  there and the task is cheaper than it looks.

## 7. MY OWN W3 AND W4

**W3, A21 form: the mathematician names, the coder writes.** The widest
unmeasured term in THIS dispatch is the sweep count: how many sites in the
tree and the queue consume `LsetCodeOrd`, and at which of them the target
already has tree supply. The probe the coder should write is a tracked,
read-only enumeration script under the sweep task's home in
`agents/tasks/<CODE>/`, never under `src/`, never deleted: it greps
`LsetCodeOrd`, `lset-code-ord` and the consumer names over
`agents/tasks/*/Probe*.agda` and over `src/`, and writes the site list and
the count to its `runs/`. Estimate: one recon dispatch, script under 80
lines. Basis: delivered comparable, LJ-1.649's hand count of four sites
(`lj-1.649-report.md:341-342`). I wrote and touched no `.agda` file myself.

**W4.** Nothing retires in this review. No `dev/ARCHIVE.md` row is owed.

## 8. THE TREE, LEFT AS FOUND

I wrote one file, this one, and changed nothing else. No commit, no push. One
observation: `agents/tasks/LJ-1-650/review-LJ-1-650-1.md` holds a copy of
this dispatch's brief text. It is not in the acceptance arm's 21 changed
files, its time stamp is after the arm ran, and I did not create or change
it. `git status` still shows only the untracked task home.

## ARCHIVE USED

- `archive/dev/DD-archived.md`: **READ.** `archive/dev/DD-archived.md:35`
  reads "The questions are: is the refusal correct on its own numbers; is the
  measurement sound; did the BRIEF cause the outcome; and is there a cure the
  return missed." That is the four-question lens this review attacked with,
  and its home is the DD25 row.
- `archive/dev/JOURNAL.md`: **READ, to verify the attacked return's
  citation.** `archive/dev/JOURNAL.md:328` reads "**DD27 landed.** `[LJ-1.23]`
  re-indexed the hull by `Code`, 372 to 431 lines at". The return quoted this
  line for why `CodedCover` is stated over codes; the quote occurs at that
  line and the use is sound.
- `archive/dev/LJ-dispatch-index.md`: **READ, to verify the attacked return's
  citation.** `archive/dev/LJ-dispatch-index.md:74` reads "| LJ-1.16-R | DD25
  review of LJ-1.16 | OVERTURN the operative clause | The obstruction is the
  hull's INDEX TYPE, a LJ-1.3 design choice, not the mathematics. Owner's
  fork; LJ-1.18 prices it |". The return drew the parallel that its own
  obstruction is also a type question; the row is there and carries it.
- `archive/dev/ORCHESTRATION.md`: **DECLINED.** It is the archived operating
  document, superseded by `dev/memos/LJ-4-pod-program-design.md`. This review
  turns on types, runs and citations, not on how the loop is operated.
- `archive/dev/PLAN-archived.md`: **DECLINED.** It is the superseded plan;
  the live plan is the queue and the screen. This review decides one return
  and re-plans nothing.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ, to verify the attacked return's
  shape claim.** `dev/literature/devlin-II5.md:214` reads "1. Level-hood as
  Σ₁ with a Σ₀ matrix: there is a Σ₀ formula Φ(z, v, γ) of". That is the
  two-variable shape the probe states as `LevelFormula` at
  `Probe650.agda:322-328`, and the citation is sound.
- `dev/literature/devlin-errata.md`: **READ, to attack the return's Devlin
  use.** `dev/literature/devlin-errata.md:60` reads "- Levels-of-language
  ambiguity. WS p. 56-57: "There is an ambiguity over the". The erratum
  warns that Devlin's two readings of Σ0 are not equivalent in weak systems.
  It does not touch this return: `LevelFormula` is stated as a type with
  soundness and completeness as hypotheses (`Probe650.agda:322-328`), not as
  Devlin's equivalence. The attack fails and the return stands.
- `dev/literature/BIBLIOGRAPHY.md`: **DECLINED.** It is the fetch record. No
  bibliographic question arises; the return's Devlin use was checked against
  the chapter file itself.
- `dev/literature/digest.md`: **DECLINED.** It is the corpus-wide digest.
  This review needed only the two chapters the return cites, and I read both
  directly.
- `dev/literature/geology.md`: **DECLINED.** Ground models and the mantle
  bear no relation to a Skolem hull's codes or to a covering ordinal's code.

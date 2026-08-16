# LJ-1.358: the second DD18 design, on `[LJ-1.357]`'s corrected foundation

Status: COMPLETE. Tier: pi (pi-subagent-mode), model `glm-5.3`. No Agda.

## RETURN, in one line

**DD18 as written is already enforced to its mechanical maximum on the brief
side, and the return side admits exactly one small mechanical increment
beyond the heading check: a citation truth check, which today can see only 4
percent of citations.**

So A is almost empty, as the brief predicted it might be. B is where the
design lives. Both are below, separated and priced.

## A. What enforces DD18 as written today

DD18's own satisfaction clause governs the BRIEF side: "Each is satisfied by
one honest line naming the corpus and saying nothing in it bears on the task"
(`dev/PLAN.md:608`, DD18 row, enforcement paragraph). One line. Not four. R1
demanded four, and `[LJ-1.357]` was right that R1 is a new rule.

### A.1 The brief side: the maximum is already built

A checker under the one-line clause can verify three things: the section
exists, it names a corpus, and it carries a decline or a citation. All three
exist today:

- `dispatch.py:2278` (`survey_defects`) refuses a brief with no ARCHIVE
  heading and no `archive/` substring. MEASURED, by reading the function.
  Codex path only, and DD18's row says so.
- `scripts/gate/check-archive-cited.py` prints the same defect at the commit
  surface, advisory, wired as `archivecited` in `Makefile:36`.

The word "honest" is a judgment about the world. No machine can check it. The
clause gives the author a one-line escape, so a ritual line is COMPLIANT as
written. The decay `[LJ-1.157]` measured lives inside the compliant band.
**Finding: on the brief side, nothing mechanical can do more than the
heading check already does. The failure mode the owner caught is legal under
the rule as written.** That is A's answer, and it is a finding, not a gap in
effort.

### A.2 The return side: one real increment exists

DD18's return clause says the report names "what it actually read and what it
took from each item, at `file:line`" (`dev/PLAN.md:608`). That sentence
is checkable beyond its heading:

1. **Cited paths exist and cited lines are inside the file.**
2. **Quoted text occurs at the cited line.** A report that quotes words the
   file does not hold, or holds at another line, breaks the letter of "at
   `file:line`".

No checker reads reports today. `Makefile:36` lists every target in
`make check`: none opens a report for ARCHIVE USED. MEASURED, by grep: no
file under `scripts/` matches `is_report` or `ARCHIVE USED`. The heading
refusal on returns is hand-applied by the orchestrator, and DD18's row
says so.

I built the truth check as `probe_358_truthcheck.py` and ran it over 264 live
reports (0.4 s). Numbers:

- 2527 ARCHIVE USED bullets hold 111 quote-bearing citations. **Coverage is
  4.4 percent of bullets.** MEASURED. DD18 does not require quoted text, so
  most citations carry nothing the checker can verify. This is the honest
  ceiling of A.
- On frozen corpora (the four archives never change), 31 quotes were
  checkable: 20 verified, 11 flagged. I read every flag. Five to six are real
  letter defects. The rest are checker tolerance classes I fixed or counted
  (row rendering, editorial brackets, moved paths).

The decisive run. `[LJ-1.357]` found two mis-citations in `[LJ-1.356]`'s
report by hand, at maximum effort, section 7.4. The probe finds exactly those
two and nothing else:

```text
LJ-1-356: ARCHIVE USED: archive/dev/JOURNAL-archived.md:1370: quote found only in window
LJ-1-356: ARCHIVE USED: archive/dev/TASKS-archived.md:7: quote found only in window
```

Run: `.venv/bin/python agents/tasks/LJ-1-358/probe_358_truthcheck.py --task LJ-1-356`.
On `[LJ-1.357]`'s own corrected report it prints no defect: 7 quotes
verified. The careful author passes. The probe also found one defect
`[LJ-1.357]` did not report: `LJ-1.355` cites `JOURNAL-archived.md:1370` for
"surfaced twice, lost twice", and that phrase occurs nowhere in that file.
It occurs in a dispatch log,
`.claude/skills/codex-dispatch/.state/logs/LJ-1.353-20260816-084950-final.md:55`.
MEASURED, `grep -rn "surfaced twice" --include="*.md" .`.

**A's verdict: one increment exists, it is small, and it is real. As a gate
today it would be advisory-grade, because it sees 4 percent of citations. It
becomes load-bearing only under B2, where the rule requires the quote.**

### A.3 Why A.2 is presented as A and not B

The truth check demands nothing the row does not already demand: the row
requires what was ACTUALLY read, at `file:line`. A fabricated line violates
the row as written. But the row's stated enforcement point for returns is
section presence only, so wiring the check extends the named enforcement.
DD19 says a rule must name its enforcement point. I therefore present the
wiring inside B2's diff, and the owner rules on the rule, not on a checker.

## B. What DD18 would have to become, and the mechanism then

Two rule changes, one gate each, plus two prints. Each is priced. Both diffs
are proposals; nothing is landed.

### B1. The brief side: four corpora, one line each, cited or declined

This is R1 promoted from "enforcement" to what it is: a rule change. The
satisfaction clause becomes "one honest line per corpus", not one per section.

Realized price, from the only two compliant briefs in the tree:
`LJ-1.357`'s ARCHIVE section is 19 lines, `LJ-1.359`'s is 23. Today's drifted
form runs 12 to 14 lines (`LJ-1.353`, `LJ-1.356`). MEASURED, `awk` per file.
**So the delta is about 7 lines per brief.** Minutes: 3 to 5, INFERRED. The
basis is this task's own survey steps: one grep of the TASKS index for the
subject, one glance at `dev/ARCHIVE.md`, one at the DECISIONS headings, one at
the six files of `archive/src/2026-08-09-rud-route/`.

Paste-cost: four lines pasted per task kind. A process task can paste "nothing
bears" four times forever. Nothing mechanical stops it. R2's print shouts
after five repeats, and R2 cannot gate (section B3 below). **The honest
statement: B1 buys VISIBILITY, not surveys.** The DD4 precedent prices
visibility: the heading gate holds at 247 of 259 with zero new lapses since
the epoch, and the four template bullets measured in the corpus are the fate
of unpaste-guarded lines.

Worth ruling? My recommendation: yes, as a print with the gate kept at the
heading, because the enumeration is the row's own aspiration and the price is
7 lines. But the owner should rule knowing B1 is 4 pastable lines away from
ritual.

### B2. The return side: answer the brief, and quote one line per file

The rule text: a return's ARCHIVE USED names every archive path its brief
cited, took or declined, and names ONE line read per archived file, quoting
it. Literature mirrors it when the brief cites `dev/literature/`.

Prices, all MEASURED on delivered artifacts:

- The compliant form exists: `LJ-1.357`'s ARCHIVE USED is 36 lines over 6
  citations. `[LJ-1.356]`'s, without the quote duty, is 26 lines over 4. The
  quote duty costs about 2 lines per citation, and zero extra minutes, because
  the author must open the file to quote it. That is the point.
- Current miss rate under the corrected checker: 12 tasks of 256 post-epoch
  carry 16 genuinely unanswered DD18-scope citations. Command:
  `.venv/bin/python agents/tasks/LJ-1-358/probe_358_r3_fixed.py`.
- Checker cost: 0.4 s over 256 tasks, milliseconds per dispatch.

Why the quote duty matters: it converts the truth check from 4 percent
coverage to full coverage, and its minimal compliant form is task-specific BY
CONSTRUCTION. A pasted quote from another brief fails, because the cited file
does not hold it. To pass, you must copy a line that exists in the file you
cite. That is the cheapest strategy AND the honest one. This is the DD4-shape
argument applied to an enumerable that cannot be faked.

B2's false negatives, named:

- A true header line quoted without reading deeply. The ritual survives in
  truth. MEASURED: 5 of 14 TASKS-archived citations stop at line 20 or
  earlier; 9 go deeper.
- A quote from the right file, pasted without understanding. Undetectable by
  machine. Review keeps this residue, as it does today.
- Paraphrase inside quotation marks. The probe flags it (LJ-1.158,
  LJ-1.355). An author must quote verbatim. This is a cost as well as a
  catch: elisions and editorial brackets need stated conventions
  (`[...]` for insertions, `...` for cuts), and so does the EXPOSING quote:
  a report that quotes a bad quotation to refute it must set the exposed
  text in backticks, or the checker flags the exposure. My own report hit
  this and adopted the convention. MEASURED, on itself.

### B3. The prints, kept advisory

- R2 template print: unchanged from `[LJ-1.356]`, print only. It measured 4
  template bullets over 40 briefs on today's corpus.
- R4 term xref: kept with the component cure `[LJ-1.357]` upheld. I rebuilt
  it (`probe_358_r4_components.py`) with hyphen-component matching. On
  LJ-1.353's brief it now prints 4 files, and `L/Cardinal.lagda.md`, the file
  holding the proof, is one of them. MEASURED. The other 3 point away or are
  a patch file, so the print stays advisory. The refuted counterfactual is
  not re-justified: R4 still keeps zero terms from a brief that never names
  its subject.

### The proposed DD18 row diff, enforcement paragraph only

```text
**ENFORCEMENT, PROPOSED [LJ-1.358], and it binds the return, not the
decline.** `dispatch.py` keeps its heading refusal on every brief. A brief's
ARCHIVE section names each of the four corpora, one line each, cited or
declined; `scripts/gate/check-dd18-return.py` in `make check` prints a brief
that omits one and never gates it. A return's ARCHIVE USED answers every
archive path its brief cited, and quotes one line per archived file it names;
the checker refuses a return whose cited file does not hold its quoted line
at the cited line number. Relevance stays review. The truth check binds the
commit surface, both dispatch modes, and the dispatch tool refuses nothing
the row does not name.**
```

No `AGENTS.md` text is proposed. The row is the rule's one home, and
`AGENTS.md` already points to it. `[LJ-1.357]` judged the earlier
`AGENTS.md` insert dangerous, and a second surface would be canonical twice.

## The kept signals, each with three numbers

**S1, return answers brief (R3 corrected).**
Paste-cost: one echoed path per citation, and the echo passes. Per-dispatch
cost: 0.4 s machine, about 1 line per cited path. False negatives: an
unquoted echo (the truth check closes this under B2), a passing parent
mention (my first probe version had exactly this bug and LJ-1-183 escaped
it; the one-way prefix rule closes it), and a basename mention that answers
without reading. MEASURED residue today: 12 tasks of 256, 16 citations.

**S2, citation truth (new).**
Paste-cost: none that survives. A pasted quote fails unless the cited file
holds it. Per-dispatch cost: milliseconds; author cost zero beyond opening
the file. False negatives: unquoted citations (95.6 percent of bullets
today, MEASURED), true-but-shallow lines, paraphrase that happens to match.
On frozen corpora the probe read 31 quotes and flagged 11; 5 to 6 were real
after tolerance fixes. The classes I fixed to get there: table-row
rendering, editorial brackets, moved archive paths. Each fix was a defect in
my own first version, which is itself the price of this signal.

**S3, enumeration print (R1 demoted to print).**
Paste-cost: 4 lines. Per-dispatch cost: under 0.1 s machine, 7 lines and 3 to
5 minutes author. False negatives: everything pasted. MEASURED evidence that
pasted is the default fate: the SHAPE family covers 155 briefs
(`grep -liE "take SHAPE|taking SHAPE" agents/tasks/LJ-1-*/LJ-1.*.md | wc -l`),
and 4 verbatim template bullets span 40 briefs.

**S4, template print (R2).** Paste-cost: one keystroke, MEASURED twice by
`[LJ-1.357]` sections 4.4 and 4.5. Per-dispatch cost: under 0.1 s. False
negatives: any varied wording. It prints. DD4's no-metric ruling forbids it
to gate, and DD4 is the parent of that objection.

**S5, term xref print (R4 with components).** Paste-cost: cite what the
archive holds, which is the survey. Per-dispatch cost: about 25 ms per brief.
False negatives: the unnamed subject, MEASURED by `[LJ-1.357]` at zero kept
terms on `[LJ-1.107]`'s brief; the synonym beyond hyphen components; and 3
of 4 printed files on the LJ-1.353 case point away from the proof.

## What I dropped, and why

- **R1 as a gate.** Its minimal compliant form is corpus-generic, so by the
  DD4-shape principle, which `[LJ-1.357]` called the design's best
  contribution, it decays. The corpus holds the decay already measured: 155
  SHAPE briefs, 4 template bullets over 40 briefs, 6 duplicate DD4 tails over
  14 briefs, and a zero-word DD4 tail at LJ-1-303. Keeping it as a gate
  would have wired the 256-of-257 wall into `make check` for a form the
  corpus proves is pasteable.
- **R2 as a gate.** One keystroke defeats it, measured twice, and DD4 has no
  metric by the owner's ruling. It prints.
- **R3's unconditional LITERATURE USED heading.** DD18 conditions the
  literature duty on mathematics-dispatching briefs. The unconditional demand
  manufactured 51 of the 93 false failures. Conditional on the brief citing
  `dev/literature/`, the live residue is 7, all historical tasks LJ-1-103 to
  LJ-1-132. MEASURED.
- **R4's counterfactual claim.** Refuted by measurement. Not restated.
- **The "256 of 256" headline.** The corpus moved twice since; my reruns say
  257 of 259, and the number was never the point. The point was that R1
  measured path spelling, and `[LJ-1.357]` section 3.5 proved it with
  LJ-1-107's 738-character section scoring zero.

## Does the core idea survive

**Partly, and the surviving half needs a new name.**

"Gate the enumeration, not the relevance" fails as stated. Enumeration alone
is not enough, because most enumerations of a survey are corpus-generic, and
a corpus-generic minimal form is pasteable. That is not an implementation
accident. It is the shape principle itself, and I can measure its wake: every
corpus-generic gated form in this repository decayed (155 SHAPE briefs, 4
template bullets spanning 40 briefs, 6 duplicate DD4 tails). `[LJ-1.357]` upheld the label
while refuting three of four instances built on it. An idea whose every
instance fails needs its instances re-examined, and on examination the
instances that failed were corpus-defined and the instance that held,
R3, was task-defined.

The corrected principle: **gate the enumerations the task itself defines;
print the ones the corpus defines.** The task defines two: the paths its own
brief cited, and the text of the line its report quotes. Both have
task-specific minimal forms by construction, which is why S1 and S2 hold
where R1 cannot. The corpus defines the rest: corpus names, template text,
term matches. Those print.

So I disagree with `[LJ-1.357]`'s uphold in one narrow way, with the
measurement above as the warrant: the label as written is wrong, and what it
upheld was the evidence, not the sentence.

## ARCHIVE USED (DD18)

One line read per archived file, as the brief ordered.

- **`archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:7`.** Line read:
  "that definition left standing. Cantor-Schroeder-Bernstein upgrades two".
  TOOK the spelling that defeats exact-term matching, and verified the
  component cure against it: with per-component intersection, this file
  prints for "Cantor-Bernstein". Also opened `:89`, `module CSB`, to confirm
  the probe's file resolution.
- **`archive/dev/TASKS-archived.md:116`.** Line read: row L3.32-T81, "CSB
  literature survey | COMPLETE (keep ours)". TOOK the confirmation of
  `[LJ-1.357]`'s repair of the founding story: `[LJ-1.107]` surveyed and
  chose.
- **`archive/dev/DECISIONS-archived.md:42`.** Line read: D20, "Retired code
  is archived, never deleted." TOOK the spot-check the brief ordered: I
  grepped "survey" over the whole file. Four hits. Line 19 explains which
  D rows were dropped and names a memo, D22 gates funding on probes, and
  two more are the word inside other rulings. None states a survey duty.
  The negative HOLDS on my own read. MEASURED.
- **`archive/dev/JOURNAL-archived.md:1369`.** Line read: "of a BIJECTION,
  not as injections both ways, since the latter turns every equality into
  a". TOOK the line the truth check uses to catch the `:1370` mis-cites of
  LJ-1.356 and LJ-1.355. And the brief's own demand, confirmed:
  `grep -c "LJ-1\." archive/dev/JOURNAL-archived.md` returns 0. No LJ-1
  entry can exist there. I substitute nothing for it. The record the earlier
  brief demanded does not exist, and saying so is the whole answer.
- **`archive/src/2026-08-06-four-dead-modules/L/Rud/CodePred.lagda.md:228`.**
  Line read: "Writing the chapter at the telescope rather than at a stage is
  what keeps a". TOOK the evidence for a real mis-quote class: `[LJ-1.158]`
  cites `:238-246` and quotes `writing this chapter on a telescope`, which
  the file does not hold in that wording. The quote is a paraphrase in
  quotation marks, and its cited range is 10 lines off. MEASURED. My own
  first draft of this very bullet paraphrased the line, and my own probe
  flagged it. That is the signal working on its author.

WHY NOT more of `archive/src/`: the survey needed six file names and the
subject terms, both delivered by the greps above. The 845-line levelIn
comparable and the CSB chapter are priced in the record already cited.

## LITERATURE USED (DD18)

`dev/literature/` holds 16 files and no process mechanism. That negative is
checked twice, by `[LJ-1.356]` section 14 and `[LJ-1.357]` section 10, and
the brief ordered no third pass. NOT RE-OPENED. Nothing in this task used
the literature corpus, and nothing in it bears on checker or rule design.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric. Axis (C-46): AC-against-GCH. This task writes no
mathematics and lands no line, so its closure delta is zero on both ends.

The brief ordered a re-derivation before leaning on the numbers, and I ran
both: `check-dd4-stated.py` prints 247 of 259 with 12 frozen pre-epoch;
`probe_357_dd4_distinct.py` prints 6 duplicate groups over 14 briefs and a
zero-word tail at LJ-1-303. I lean on nothing `[LJ-1.357]` weakened: the DD4
precedent enters this report only as visibility (the heading held) and as
the no-metric ruling that demotes R2 to a print.

The DD4-shape principle is the load-bearing borrow: a gate holds when its
minimal compliant form forces task-specific content. This design applies it
in the direction DD4's own corpus supports and drops the count DD4's owner
refused.

## Probes written

All in `agents/tasks/LJ-1-358/`, all run today, none wired.

- `probe_358_truthcheck.py`. The citation truth check. 264 reports in 0.4 s.
  Its own first version had two defects (single-line matching, empty-line
  containment) and two over-lax rules (bullet-wide attribution, two-way
  prefix), each found by a decisive run and fixed. The defects are the
  measured price of the signal.
- `probe_358_r3_fixed.py`. R3 corrected: one-way prefix, suffix declines,
  conditional literature, DD18 scope split. 12 genuine failures of 256.
- `probe_358_r4_components.py`. R4 with hyphen-component intersection. The
  file holding the proof now prints, with 3 noise files.

## Abort criterion (D-1)

Not triggered. The design landed with A and B separated and priced. A is
nearly empty, which the brief named as a real answer, and B is two rule
changes at 7 lines and 2 lines per citation respectively. I wrote only in
`agents/tasks/LJ-1-358/`, touched no `src/`, edited no frozen directory, ran
no Agda, ran no `make check`, and committed nothing.

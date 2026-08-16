# LJ-1.363 report: DD18's amended enforcement lands, B2 gating, B1 printing

Status: COMPLETE. Tier: pi (pi-subagent-mode), model `glm-5.3`. No Agda.

## RETURN, in one line

**YES: `make dd18survey` runs green with the epoch set (exit 0, no pipe), and
my own report is the one task the gate judges live.**

I could not run the full `make check`. My brief forbids it, because
`[LJ-1.362]` holds a live Agda slot and a cold typecheck would collide. I ran
MY target alone through `make dd18survey`, and I read the exit code with no
pipe in front of it (C-59). The typecheck and the other gates are the
orchestrator's run.

## 1. What was built

- `scripts/gate/check-dd18-survey.py`, one checker, two halves. B2 gates the
  return side and never prints advisories about itself. B1 prints the brief
  side and never exits nonzero for its findings.
- One `Makefile` target `dd18survey`, wired into `check:` and `.PHONY`.
- `agents/tasks/LJ-1-363/probe_363_selftest.py`, the D-1 probe that drives
  the red paths the corpus never exercises. All 11 cases pass.

B2 checks four duties, in the row's own words (`dev/PLAN.md:608`, the
amendment dated 2026-08-16):

1. The return carries an ARCHIVE USED section.
2. Every archive path the brief's ARCHIVE section cited is named in the
   return: exactly, or by a DEEPER path (one-way), or by a relative suffix
   spelling. A written decline is compliance. `agents/tasks/archive/` is
   outside the universe, and a live `agents/tasks/` path is not a citation.
3. When the brief's LITERATURE section cites `dev/literature/`, the return
   carries a LITERATURE USED section. This is its own defect kind, never
   counted as an unanswered path.
4. Every archived file the return names as read carries a quote of twelve
   characters or more that occurs at the cited line in the cited file. A
   quote found only within three lines is a mis-cited line and fails. This is
   the `file:line` letter that `[LJ-1.357]` enforced twice by hand at section
   7.4.

## 2. B2 live defects, split by kind

**The gated set is one task: LJ-1-363, this one. Live defects: 0.** Command:
`make dd18survey`, exit 0 read without a pipe.

The corpus behind the frozen numbers, all MEASURED by the same run:

| set | tasks | unanswered | no ARCHIVE USED | no LITERATURE USED |
|---|---|---|---|---|
| gated, LJ-1-363 on | 1 | 0 | 0 | 0 |
| second epoch, LJ-1-359..362 | 3 completed, 1 live | 0 | 0 | 0 |
| pre-amendment, before LJ-1-359 | 21 | 14 | 0 | 7 |

## 3. The frozen count and the epoch's justification

**The epoch is a code boundary, not a name list: everything before LJ-1-359
is frozen, LJ-1-359..362 is a second frozen epoch, LJ-1-363 on is gated.**

Why that boundary is honest, with the evidence:

- **Before LJ-1-359: frozen.** The amendment is dated 2026-08-16 and those
  returns were written under the old one-honest-line clause. The naming half
  would fail 21 of them. The scale is written into the checker's own comment
  at `scripts/gate/check-dd18-survey.py` (`FROZEN_SCALE`), per C-59, not into
  a commit message.
- **LJ-1.359..362: a SECOND EPOCH, frozen, and this is the C-48 finding of
  this task.** These four briefs were dispatched after the ruling: their
  RETURN sections order an ARCHIVE USED "naming ONE line read per archived
  file" (`agents/tasks/LJ-1-359/LJ-1.359.md`, ARCHIVE section, line 175
  onward; `agents/tasks/LJ-1-361/LJ-1.361.md:226` names "the amended return
  clause"). But the row they were written under named
  `scripts/gate/check-dd18-survey.py` as enforcement while no such file
  existed, and their briefs said NAMING where the row says QUOTING. I
  measured the quote half on their three completed returns: all 3 fail it.
  LJ-1-359 names a line of `CardinalPredicates.lagda.md:10` with no quote.
  LJ-1-361 paraphrases `DECISIONS-archived.md:38` as "D16, genericity equals
  durability"; the file holds "asset durability equals genericity", and the
  paraphrase carries no quote marks. LJ-1-360 quotes a table row with two
  silent cuts. The divergence is the orchestrator's, between its briefs and
  the row it had just amended. Their authors followed their briefs. A record
  is never rewritten, so they are frozen the way
  `scripts/gate/check-premises-stated.py` froze its own twenty-one
  (`SECOND_EPOCH`), with the scale in the comment. The three findings are
  printed under `--verbose` and never fail the gate.
- **LJ-1-363 on: gated.** My brief quotes the amendment and this checker
  existed when my report was written. My report passes, and is the first
  return the gate has ever judged.

A report still in progress is not judged: the gate reads the status line and
waits. So a live dispatch never reddens the commit gate while its agent
works. This is C-22's early skeleton made safe.

## 4. THE HONEST RATE, re-derived from scratch

My brief put "about 15" at risk and ordered a clean re-derivation. Mine
differs, and the difference decomposes exactly:

- **14 tasks carry a genuinely unanswered citation.** `[LJ-1.357]` said
  "about 15" after discounting its 17 for sampling over-reach. I read every
  flag my checker raised for this class. LJ-1-178's report names
  `archive/dev/TASKS-archived.md` zero times (`grep -c`, MEASURED).
  LJ-1-195's brief cites `dev/ARCHIVE.md` and its report never names it.
  LJ-1-198's brief cites `dev/literature/devlin-II5.md`; its report holds
  zero "II5" strings. LJ-1-200's report names only JOURNAL. LJ-1-228's
  report names only the parent `archive/dev/`, which correctly answers
  nothing under the one-way rule. Every sampled case is real. No flag in
  this class was an over-reach, so I discount nothing: 14, not 15, and the
  two instruments agree within their own sampling error.
- **7 more tasks fail only the conditional LITERATURE USED heading**
  (LJ-1-103 through LJ-1-132). This is EXACTLY the residue `[LJ-1.358]`
  measured and printed as "7, all historical", and `[LJ-1.357]`'s corrected
  checker kept it out of its headline. Under the amended rule it is a live
  defect class, so the honest rate of the WHOLE naming half is **21, not
  about 15**. The premise was not wrong about the unanswered class. It
  excluded a class the amended rule now gates.

**So: the honest rate is 21 under the rule as amended, 14 for the unanswered
class alone, and the direction of the correction is UP, not down.** Sampled
cases above, all MEASURED.

## 5. B1's print output

From the same green run, over 264 live briefs. The corpus moved under this
measurement: LJ-1-364 was dispatched at 11:02 while I worked, so the first
runs said 263. Its brief already follows the amended form, four corpora and
the quote duty, so it will be gated when its return lands.

- Corpora not named, cited or declined: **CODE by 155, TASKS by 112, JOURNAL
  by 244, DECISIONS by 246.**
- **49 briefs name none of the four corpora. Of those, 30 cite pre-move
  `_build/` paths.** That second number exists because `[LJ-1.357]` measured
  LJ-1-107's 738-character survey scoring zero as an over-reach: a pre-move
  spelling is reported beside the zero so it never reads as "no survey".
  `dev/ARCHIVE.md` counts as CODE, fixing the other measured over-reach.
- **8 TEMPLATE clusters**, paths normalized to `<PATH>` first. Every cluster
  with its size:

| size | the template bullet, first 90 characters |
|---|---|
| 19 | `<PATH>, taking SHAPE and never a claim. Return an ARCHIVE USED section naming ONE line rea` |
| 11 | `Take SHAPE, never a claim. [LJ-1.11] ruled that route's condensation target classically FA` |
| 8 | `<PATH> Take SHAPE from the archive, never a claim. Return an ARCHIVE USED section naming O` |
| 8 | `<PATH>, read WHOLE. The target.` |
| 7 | `<PATH> Take SHAPE from the archive, never a claim. Return an ARCHIVE USED section at file:` |
| 6 | `<PATH> in full: the brief AND the report AND every probe. Read the probe, not the report's` |
| 6 | `<PATH> Take SHAPE from the archive, never a claim, and say what would NOT transfer. Return` |
| 5 | `<PATH>, read WHOLE.` |

`[LJ-1.356]` found four clusters over 40 briefs. I find eight over 70
brief-instances, because I also normalize live `agents/tasks/` paths, so a
fully drifted brief's bullets enter the comparison. That was the blindness
`[LJ-1.357]` named at section 1.5, and it is fixed: every bullet of the
ARCHIVE section is compared, with or without an archive path in it.

The two R1 over-reaches the brief ordered avoided are avoided, and the
instrument measured them first: my first draft scored LJ-1-107 at zero
with no qualifier, which is why the pre-move count exists.

## 6. Runtime

**0.6 s** for the whole corpus run: 259 completed pairs, 263 briefs, both
halves, `time make dd18survey`, MEASURED. The B1 half alone measures 0.06 s
in-process, MEASURED.

## 7. My own false negatives, named

- **MEASURED: a "WHY NOT" phrase exempts the whole bullet from the quote
  duty.** LJ-1-361's bullet for `JOURNAL-archived.md:1377` paraphrases the
  line, but the bullet also says "WHY NOT the surrounding entries", so the
  checker reads the bullet as a decline. The paraphrase escapes. I keep the
  behavior: the safe direction for a gate is to under-fail. A stricter split
  of decline wording per citation would re-open the LJ-1-168 over-reach.
- **INFERRED: the bare-directory hole.** A brief citing
  `archive/src/2026-08-09-rud-route/` and a return naming exactly that
  directory, quoting no file and declining nothing, passes. The quote duty
  binds files. I chose not to demand a decline or a quoted file for a
  directory want, because that was the over-reach shape that made R3 unfair.
- **MEASURED by `[LJ-1.358]`, inherited: a true header line quoted without
  reading deeply verifies.** The quote duty forces the file open, not
  understood. Review keeps this residue, as the row says.
- **INFERRED: B1 reads spellings.** A brief citing only
  `archive/dev/STATUS-archived.md` scores zero of four, because DD18's row
  names four corpora and STATUS is not one of them. B1 prints, so the cost is
  a wrong hint, not a refused return.
- **INFERRED: an archived file cited outside a bullet of a USED section, in
  running prose, carries no quote duty.** The audit reads bullets.
- **INFERRED: an abandoned report keeps "IN PROGRESS" forever and is never
  judged.** The audit waits for a completed return; a task that never
  completes escapes entirely. The task index catches that, not this gate.

## 8. DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker. Axis (C-46): this task writes no
mathematics, so my axis is not the two towers, said plainly.

The DD4 content that is live here is the no-metric ruling itself, and it is
the load-bearing wall of this checker: **B1's threshold of five is a count,
and it prints, never gates.** Printing escapes the objection for one line:
a count that cannot refuse anything cannot be gamed INTO anything, because
the game's prize, a green gate, is not on the table. The moment B1's count
could fail a commit, one keystroke would beat it, measured twice by
`[LJ-1.357]` at sections 4.4 and 4.5. B2 gates, and everything B2 gates on,
a quote from the cited file at the cited line, a named path, a decline, is an
act or its honest refusal, not a count.

## ARCHIVE USED

One line read per archived file, took or declined, as the amended row orders.

- **`archive/dev/DECISIONS-archived.md:42`.** Line read: "The archive
  regime, and the endpoint promotion". TOOK the settled negative: D20 governs
  retiring code, never surveying it, so no survey rule died with the retired
  route. `[LJ-1.357]` upheld it at section 8.5 and I did not re-derive it.
- **`archive/dev/TASKS-archived.md:116`.** Line read: "L3.32-T81 | CSB
  literature survey | COMPLETE (keep ours)". TOOK the corrected history:
  `[LJ-1.107]` surveyed and chose, so this task's founding story is the
  repaired one, and no checker text here repeats the old one.
- **`archive/dev/JOURNAL-archived.md`: DECLINED, and the absence re-run
  rather than inherited (C-57).** `grep -c "LJ-1\." archive/dev/JOURNAL-archived.md`
  returns 0 today, MEASURED, matching `[LJ-1.357]` section 7.3. The file is
  the retired route's journal and holds nothing about any LJ-1 task. No
  passage is substituted for the one my brief ordered declined.
- **`archive/src/2026-08-09-rud-route/`: DECLINED, naming what I checked.**
  `ls` shows `Everything.lagda.md`, `FOL/`, `L/`, `README.md`,
  `rud-route-src.patch`, `V/`. A grep for checker, gate and python over the
  route returns three files whose hits are prose about Agda gates
  (`README.md:16`, "every gate is blind to it by structure") and a
  typechecker normalizing (`Everything.lagda.md:217`). Nothing in the route
  bears on designing a survey checker. WHY NOT deeper: the route is Agda
  mathematics for a different coding scheme; the four hits above are the
  whole checker-relevant surface, MEASURED.

## LITERATURE USED

- **`dev/literature/formalizations-landscape.md:1`.** Line read:
  "Formalization landscape sweep: L, V=L, condensation". WHY NOT the rest
  of the corpus: `dev/literature/` holds no process mechanism, a negative
  measured twice already, by `[LJ-1.356]` section 14 and `[LJ-1.357]`
  section 10, and my brief ordered no third pass. The one file my brief
  named by name is answered above with one line and no more. WHY NOT that
  file deeper: it is an index of what other proof systems formalized, never
  how a project enforces a rule, exactly as `[LJ-1.357]` section 10 records.

## Probes written

- `agents/tasks/LJ-1-363/probe_363_selftest.py`. Eleven cases: five
  compliance shapes (quote at line, relative decline, deeper answer, pipe-row
  quote, ellipsis) and six defect shapes (unanswered, no heading, no
  literature heading, no quote, mis-cited line, quote not in file). It found
  one real checker defect before landing: a missing LITERATURE USED heading
  double-counted its paths as unanswered, which is fixed by reporting the
  heading as its own kind only. Run it with
  `.venv/bin/python agents/tasks/LJ-1-363/probe_363_selftest.py`.

## Abort criterion (D-1)

Not triggered. The gate lands green with the epoch set, the honest rate
re-derivation landed within reach of `[LJ-1.357]`'s estimate for its class
and above it for the amended whole, and B2 was makeable fair: its three
fairness rules (separate kinds, deeper answers, declines as compliance) each
correspond to a measured over-reach, and its live corpus judges exactly one
return, mine, which passes.

I wrote only in `agents/tasks/LJ-1-363/`, `scripts/gate/check-dd18-survey.py`
and the `Makefile` target lines. I touched no `src/`, ran no Agda, ran no
full `make check`, edited no frozen record, and committed nothing.

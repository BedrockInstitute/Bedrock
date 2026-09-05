# [LJ-1.356] A mechanism that SHOUTS when DD18 is not followed

Status: COMPLETE. Tier: pi (pi-subagent-mode). Model: glm-5.3. No Agda.

## 1. The mechanism, in one sentence

Gate the ENUMERATION, not the relevance: a checker that refuses a brief whose
ARCHIVE section does not name each of DD18's four corpora cited or declined
(R1), refuses a report that does not answer every archive path its own brief
cited (R3), shouts TEMPLATE when one bullet's reason text repeats verbatim
across five briefs (R2), and prints archived CODE that matches the brief's own
subject terms but was not cited (R4, advisory).

The prototype is `agents/tasks/LJ-1-356/probe_dd18_shout.py`. It is unwired.

## 2. What each signal is, and what it measured today

I ran the prototype over the live corpus, 256 briefs. Command:
`.venv/bin/python agents/tasks/LJ-1-356/probe_dd18_shout.py --recent`.

### R1, enumeration. The rule-bundle precedent, applied to DD18

`dispatch.py:2404` (`rule_bundle_defects`) enumerates the mandatory rule codes
from `rules.py --for <kind>` and refuses a brief missing one. It reads CONTENT,
because its universe is enumerable. The brief's question was whether DD18's
demand can be made enumerable the same way. It can, one level down: DD18 names
FOUR fixed corpora, `dev/PLAN.md:608`, "in each archive":

- `archive/src/`, the retired CODE;
- `archive/dev/TASKS-archived.md`, what each dispatch FOUND;
- `archive/dev/JOURNAL-archived.md`, WHY;
- `archive/dev/DECISIONS-archived.md`, the RULINGS.

R1 refuses a brief whose ARCHIVE section does not NAME each of the four,
cited or declined. The decline is DD18's own escape valve, per corpus. A
decline forces one written reason per corpus. That is the DD4 lesson stated by
`check-dd4-stated.py:41`: "pasting a heading is a strictly better failure than
silence, because the next author sees the rule."

MEASURED, prototype output: **256 of 256 live briefs fail R1 today.** The
eleven briefs LJ-1.344 to LJ-1.354 each name ONE of four. LJ-1.355, written
after the owner's question, names three of four. The whole corpus fails
because the rule was ruled 2026-08-09 and the corpus holds earlier briefs, so
a landed checker needs an epoch, as `check-dd4-stated.py:88` (`PRE_EPOCH`)
already models. On the eleven, R1 would have shouted at brief ONE, not brief
eleven.

### R2, the template detector

Each bullet in each brief's ARCHIVE section is normalized: the cited path
becomes `<PATH>`, whitespace collapses. One bullet text recurring verbatim
across five or more briefs is a TEMPLATE.

MEASURED: **four template bullets, sharing 40 briefs.** The largest, 19 briefs,
is `**`<PATH>`**, taking SHAPE and never a claim. **Return an ARCHIVE USED
section naming ONE ...`. A looser grep counts the ritual wider: 155 briefs
carry some "SHAPE ... never a claim" variant, from LJ-1.157 to LJ-1.355.
`[LJ-1.157]` was the adversarial review that diagnosed the FIRST decay. Its
own cure wording became the SECOND decay's boilerplate. MEASURED, `grep -liE
"take SHAPE|taking SHAPE" agents/tasks/LJ-1-*/LJ-1.*.md | wc -l`.

### R3, the return gate. The mode-proof half

The report must carry an ARCHIVE USED heading and a LITERATURE USED heading,
and every archive path cited in the BRIEF's ARCHIVE section must appear in the
report. The universe is enumerable because the brief itself defines it. This is
the answer to "a brief's demand is worth little if no report is ever read for
its answer."

MEASURED: the prototype found **93 tasks from epoch LJ-1.90 onward** whose
report does not answer its brief's citations. Most cite an archive path the
report never names again. The eleven recent reports all carry both USED
headings, so the heading form is alive. The retired-archive half is ritual:
ten of the eleven "read the header" of TASKS-archived.md, at `:1-6`, `:1-9`,
`:1-20`. MEASURED, `grep -oE "TASKS-archived\.md[^*]{0,30}"` over the
LJ-1-34x and LJ-1-35x reports.

### R4, term xref. The price made visible, mechanized

Rare subject terms are extracted from the brief: camel-case identifiers and
hyphen-joined proper names, kept when they appear twice or more in the brief
and in no more than 15 percent of the corpus (document-frequency filter,
case-folded). Each term is grepped over `archive/src/`. A hit the brief did
not cite prints as a MISSED CANDIDATE. Advisory, never a gate.

THE DECISIVE RUN: on LJ-1.353's brief, R4 keeps `Cantor-Bernstein` and
prints `archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md` and
`Everything.lagda.md` as missed candidates. That is the owner's chat
intervention, mechanized. It is what would have stopped `[LJ-1.107]`.

## 3. Where it is wired, and under which mode

Two wiring points, and the split answers the coverage inversion.

**The commit surface, both modes.** A new checker, proposed name
`scripts/gate/check-dd18-survey.py`, wired as a `make check` target beside
`dd4` and `archivecited`. `make check` is the gate before any commit,
`AGENTS.md` Commands. The orchestrator commits in both modes, so R1, R2 and
R3 fire in `pi-subagent-mode` and in `in-harness-subagent-mode` alike. An
in-harness dispatch passes through no tool, `dev/PLAN.md:607` under DD17, so
nothing can shout PRE-dispatch there. The shout lands at the next commit. The
eleven-brief run would have been caught at commit one, not at brief eleven.

**The dispatch surface, codex path only.** `dispatch.py`'s `survey_defects`
(`dispatch.py:2278`) keeps its heading refusal and adds the R1 enumeration,
so the codex path shouts BEFORE the agent is sent. This half is dead under
in-harness mode, and the design says so rather than hiding it. The mode-proof
half is R3: the report is a file in the tree under both modes, and the commit
gate reads it there.

**R4 is wired nowhere that gates.** It prints. A red gate on R4 would buy a
pasted citation, exactly as the checker's own docstring argues,
`scripts/gate/check-archive-cited.py:28-31`. R4 runs inside
the checker's output, in the dispatch tool's own pre-send print, and in the
audit.

## 4. What it costs per dispatch

MEASURED on this machine, prototype timings printed at run time:

- read 256 briefs: 0.1 s;
- R1 over the corpus: under 0.1 s;
- R2 over the corpus: under 0.1 s;
- R3 over 253 post-epoch tasks: 0.3 s;
- R4 over 12 briefs: 0.3 s, about 25 ms per brief.

One dispatch pays R1 plus R2 on one new brief: milliseconds. R3 fires once, at
the return. R4's grep cost is the only real term, and it caps at the advisory
slice. Nothing here prices in minutes.

The author's side: four per-corpus lines in the brief, one decline line each
where nothing bears. DD18 already demands this, `dev/PLAN.md:608`: "listing
what may bear on the task in each archive".

## 5. Its false negatives, named by me

A design that claims full coverage is wrong. Each row says which layer, if
any, catches it.

- **R1, the four-line paste.** An author names all four corpora with four
  boilerplate declines and no survey. R1 passes it. Caught by: R2, once the
  paste repeats, and by review. Not caught if varied. MEASURED RESISTANCE:
  the current failure names ONE of four, so R1 catches all of it today.
- **R2, cosmetic variation.** Change one word per brief and the verbatim hash
  splits. MEASURED: the corpus already holds near-variants, "Take SHAPE from
  the archive" against "taking SHAPE", which split my clusters at 40 caught
  of 155. A production version stems and drops stop-words, and each tightening
  risks flagging a legitimate repeat. A task series on one module may
  legitimately re-cite one file; its REASON text should still differ.
- **R3, the fabricated line.** A report can echo the brief's paths with
  invented `:line` refs. The checker verifies presence, never truth. Caught
  by: the audit, and spot-check. INFERRED, from the checker's design; no
  fabricated line was found in the corpus. This is the residue the rulebook
  already assigns to review, and the design does not pretend it away.
- **R3, the superseded citation.** A report drops a brief citation for a
  better source and does not name the dropped one. R3 shouts. Cost of
  compliance: one WHY-NOT line. DD18 asks for that line already.
- **R4, the synonym.** The archive names a concept differently from the brief.
  MEASURED: R4's exact-term grep on LJ-1.353 printed CardinalPredicates and
  Everything, but NOT `L/Cardinal.lagda.md` itself, because the file spells
  the theorem "Cantor-Schroeder-Bernstein" and the brief says
  "Cantor-Bernstein". A production version matches on hyphen components too.
  The catch still landed through the companion files. The synonym miss is
  real and is why R4 is advisory.
- **R4, the unnamed subject.** A brief that never names its subject precisely
  cannot be xrefed. INFERRED, not yet measured.
- **The system, adversarial compliance.** An author who writes four varied
  declines and varied citations with fabricated lines defeats R1 to R4. What
  catches that: the DD25 review where the return is negative, and the owner.
  The measured failure is DRIFT, 155 briefs of coasting, not deceit. The
  design catches drift and does not claim to catch deceit.

## 6. Can it be passed by pasting

Partly, and the design prices that honestly.

- R1 alone: yes, four pasted lines. That is why R1 is not the whole design.
- R1 plus R2: the paste itself becomes a template bullet and shouts at its
  fifth repeat. Varying the wording beats R2, at the cost of writing four
  different sentences, which is one honest glance per corpus away from the
  survey itself.
- R3: the report must echo the brief's paths with lines. Fabrication passes
  the machine and falls to the audit.
- R4: it prints what the subject terms hit. To silence it you must cite what
  the archive actually holds on your subject, which is the survey.

So the attack cost is no longer zero, and no longer one fixed line. The
cheapest strategy against all four layers is close to the compliant one. That
is the most an honest design claims. The checker's authors were right that a
relevance gate buys pasted citations. They were wrong to let that argument
cover the ENUMERABLE halves of the rule, and the decay measured in section 7
is the price of that overreach.

## 7. DD4's precedent, measured

DD4 is the same shape: statement gated by heading, substance left to review.
Has it held? MEASURED, three numbers.

1. `check-dd4-stated.py` reports **244 of 256 live briefs state DD4, 12 frozen
   pre-epoch, zero new lapses** since the epoch. The heading gate held.
2. The engagement paragraph, the text after the fixed formula, is **distinct
   in 241 of 243 briefs** carrying a DD4 section. Command: the `dd4dup.py`
   probe, hashing each section's normalized tail. Only two pairs duplicate.
   The substance held too.
3. The failure DD18 suffers, one fixed line satisfying the gate, exists in
   DD4 only as the RULE SENTENCE, which is meant to be fixed. The variable
   half never decayed.

Why the difference? MEASURED, from the samples: a DD4 section cannot be
written without answering a question about THIS task. "Maximize the code the
two proofs share" demands a sentence about this task's code, and the samples
from LJ-1.160 to LJ-1.355 each name this task's own lemmas and sites. DD18's
minimal form is a DECLARATION about a corpus, and a declaration can be
written once and pasted forever. "The retired route had cardinal arithmetic
too", LJ-1.353's brief, `agents/tasks/LJ-1-353/LJ-1.353.md`, ARCHIVE section.

So the precedent does not say "heading gates decay". It says: **a heading gate
holds when the gated form forces task-specific content, and decays when the
minimal compliant form is corpus-generic.** The fix for DD18 is to change its
gated form: four per-corpus blanks (R1) plus a report that must answer the
brief (R3). That makes DD18's gated half DD4-shaped.

## 8. Does the decay proxy hold

Partly. The orchestrator counted distinct `archive/` paths, one grep. My
re-derivation splits the survey in two, and the split changes the verdict.

**The live half did NOT decay.** MEASURED: each of the eleven briefs cites two
to four live prior-task reports, each with a task-specific reason. Each of the
eleven reports answers them with lines and verdicts: TOOK, CORRECTED,
REFUTED. Sample: `agents/tasks/LJ-1.348/lj-1.348-report.md`, ARCHIVE USED,
which corrects two conclusions of the report it read.

**The retired half decayed to ritual.** MEASURED: one verbatim bullet in 63
briefs, LJ-1.282 to LJ-1.355, `grep -c "taking SHAPE and never a claim"`.
Ten of eleven reports "read the header" of the retired index, at `:1-6` to
`:1-20`, and "TOOK SHAPE ONLY". An index of 265 dispatch rows was surveyed at
its first nine lines, eleven times, with every gate green.

So "the form survived and the substance decayed" overstates. The honest form:
**the form survived, the live-route substance survived, and the
retired-archive substance decayed to a ritual that every enforcement point
counts as compliance.** The proxy is adequate for the retired half, which is
the half DD18 was ruled for, and blind to the live half's health. Framing the
cure as "make briefs survey more" would tax the healthy half. The design
therefore aims at the retired half: R1 forces the four corpora, R4 prints
retired CODE matches.

## 9. The founding costs, verified

- `[LJ-1.107]` rebuilt the CSB. MEASURED: the archived CSB block is exactly
  **82 non-blank in-fence lines**, `archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:88-193`,
  fence opens at 88, module line 89. The count is `awk 'NR>=75 && NR<=193' |
  awk '/^```agda/{f=1;next} /^```$/{f=0;next} f && NF' | wc -l`, giving 82.
- The trap the archive records: `archive/dev/JOURNAL-archived.md:1368-1377`,
  the ruling to build equinumerosity as a bijection and the predicates
  generally, "which is the rebuild D16 exists to prevent".
- The 845-line comparable: `agents/tasks/LJ-1-157/lj-1.157-report.md:154`,
  three reports priced `levelIn` with no delivered-comparable anchor while an
  845-in-fence adaptable substrate sat in the archive.
- LJ-1.353's own report cites the archived Cardinal and CardinalPredicates
  files, `agents/tasks/LJ-1-353/lj-1.353-report.md`, ARCHIVE USED. The owner's
  chat correction reached the agent; the mechanism never did.

## 10. The three enforcement points, re-measured

1. `dispatch.py:2313`, `survey_defects`: passes on the heading OR the literal
   substring `archive/`. It reads the heading, never the content. Confirmed by
   reading the function, `dispatch.py:2278-2330`.
2. `scripts/gate/check-archive-cited.py`: advisory, wired as `archivecited`
   in `make check:36`. It printed 205 of 306 citing an archive, 84 citing
   archived CODE. It counts the ritual bullet as compliance: all eleven
   Decayed briefs pass it.
3. The return side: no checker reads a report for ARCHIVE USED. Confirmed by
   the Makefile `check:` line, `Makefile:36`, which lists every target.

## 11. Proposed diffs, NOT landed

`dev/PLAN.md` DD18 row, enforcement sentences, replace the stale "ENFORCEMENT
IS REVIEW ONLY" half with:

```text
**ENFORCEMENT, THREE LAYERS (proposed LJ-1.356).** `dispatch.py` refuses a
brief whose ARCHIVE section does not NAME each of the four corpora cited or
declined, and refuses a report-shaped return that does not answer every
archive path its brief cited. `scripts/gate/check-dd18-survey.py` in
`make check` fires the same two refusals at the commit surface, in BOTH
dispatch modes, and shouts TEMPLATE when one ARCHIVE bullet's reason text
repeats verbatim across five briefs. It prints archived CODE matching the
brief's subject terms and uncited, advisory and never a gate. Relevance stays
review, and a fabricated `:line` stays audit.**
```

`AGENTS.md`, the "Probes, gates and estimates" paragraph, after the sentence
on ARCHIVE and LITERATURE sections, add:

```text
A brief's ARCHIVE section names each of the four corpora, cited or declined
in one line. A return answers every archive path its brief cited. Both are
refused by the dispatch tool and by `make check`, and a repeated verbatim
citation line across five briefs shouts TEMPLATE.
```

Both edits need the owner's ruling. `AGENTS.md` needs the DD19 trailer.
`make check` needs a `dd18survey` target and the checker file under
`scripts/gate/`, which I did not write, per the brief's write scope.

## 12. Abort criterion

Not triggered. The design shouts, is cheap, and names its false negatives.
The honest negative does not apply: mechanical signals that correlate with a
real survey were measured, in sections 2 and 7. The rule-is-wrong criterion
does not apply either: DD18 was followed in substance for the live route
across the same eleven briefs, so the rule is followable. What failed is the
retired half, and the retired half is enumerable.

## 13. ARCHIVE USED

One line read per archived file, as the brief orders.

- `archive/dev/JOURNAL-archived.md:1370`, read the block 1368-1377 WHOLE.
  **Line read:** "define equinumerosity as the existence of a BIJECTION, not
  as injections both ways". **TOOK** it as the trap the archived CSB closes,
  and as DD18's founding cost record.
- `archive/dev/DECISIONS-archived.md:30-59`, read the ruling rows. **Line
  read:** D20 at `:42`, the archive regime, "retired code is archived, never
  deleted". **TOOK** the finding that the RETIRED route had NO archive-survey
  rule: its rows govern retiring code, not surveying it. The survey duty is
  new-route, DD18, 2026-08-09. A rule that died once was not found, because
  no rule existed to die. **WHY NOT the rest:** D2 to D39 name no survey
  duty; grepped for "archive" per row.
- `archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:89`, opened WHOLE.
  **Line read:** `module CSB (a b : S) (f : ...)` at `:89`, the module the
  eleven briefs never named. **TOOK** the measurement: 82 non-blank in-fence
  lines, `:88-193`, exactly the docstring's figure. The file names the
  theorem "Cantor-Schroeder-Bernstein" at `:7`, which is why the briefs'
  "Cantor-Bernstein" greps missed it, and why R4 must match hyphen
  components.
- `archive/dev/TASKS-archived.md:7`, the header the eleven reports read.
  **Line read:** "Nothing here is a live task. Read it for history."
  **TOOK** it as the ritual's own text: the header the decay reads, quoted
  back as evidence.

## 14. LITERATURE USED

`ls dev/literature/` lists 16 files. Nothing there bears on rule design: the
corpus is mathematics digests, `digest.md`, `j-hierarchy.md`,
`fine-structure.md`, `rudimentary-functions.md`, `devlin-errata.md`,
`primary-sources.md`, `BIBLIOGRAPHY.md`, `formalizations-landscape.md` and
kin. I checked each name against the task. WHY NOT each: no file treats
checker design, gate design or rule enforcement. The nearest is
`formalizations-landscape.md`, prior art in formalization projects, and it
holds mathematics landscapes, not process mechanisms.

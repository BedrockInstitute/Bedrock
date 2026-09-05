# LJ-1.357: DD25 adversarial review of `[LJ-1.356]`'s DD18 mechanism

**VERDICT: OVERTURN.**

Status: COMPLETE. Tier: opus, in-harness, the switch's ADVERSARIAL row. No Agda.
Agda slots at start: 0, `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`.

**What OVERTURN means here, stated so it is not read wider than it is.** The
report's central finding falls. Three of its headline measurements fall with
it. The mechanism's SHAPE survives and I say where. **A corrected design can
still go to the owner. The evidence base under it cannot go as written.**

**The four claims that fall, each MEASURED below:**

1. **Section 8 and section 12: "the live-route substance survived" and "DD18
   was followed in substance for the live route".** A live-tree citation is
   NOT DD18 compliance. The project's own delivered checker calls it the
   DRIFT.
2. **Section 2: "It is what would have stopped `[LJ-1.107]`".** I ran R4 on
   `[LJ-1.107]`'s brief with the prototype's own code. It keeps ZERO terms and
   prints NOTHING.
3. **Section 2: R3's "93 tasks ... Most cite an archive path the report never
   names again".** 51 of 92 have no unanswered path at all. 16 historical
   tasks carry a genuine one.
4. **Section 9's title, "The founding costs, verified".** `[LJ-1.107]`'s own
   report cites the retired `L.Cardinal` CSB in its ARCHIVE USED section. It
   did not rebuild in ignorance.

**What survives:** the design idea, R3's shape, the R4 synonym diagnosis, the
cost figures, the archive negative and the literature negative.

---

## 1. ATTACK 1. A live-tree citation is not DD18 compliance

**This is the attack the review was dispatched for, and it lands.**

### 1.1 What DD18 asks for

`dev/PLAN.md:608` names the corpora by path. It asks a brief to list what may
bear on the task **in each archive**, and then it enumerates them:

- `archive/`, the retired code, with `archive/src/2026-08-09-rud-route/` and
  `dev/ARCHIVE.md`;
- `archive/dev/TASKS-archived.md`, what each of 265 dispatches FOUND;
- `archive/dev/JOURNAL-archived.md`, WHY;
- `archive/dev/DECISIONS-archived.md`, the rulings.

**Every item is an archive. `agents/tasks/LJ-1-3xx/` is the LIVE tree and DD18
never names it.** MEASURED, by reading the row.

`AGENTS.md` says the same in its own words: "FOUR ARCHIVES, and surveying them
is a brief section rather than a hope."

### 1.2 The project already ruled this, in a delivered checker

`scripts/gate/check-archive-cited.py:26-27` states it in bold:

> **A section that names only live `agents/tasks/` directories is the drift,
> and it is what this prints.**

The same docstring records `[LJ-1.157]`'s measurement at `:11-17`: "the
section's meaning drifted to 'the new route's own prior tasks'". **The live
citation is not a healthy half. It is the named disease.**

So there are three independent repository sources against the reading
`[LJ-1.356]` took: DD18's own enumeration, `AGENTS.md`, and a checker wired
into `make check` as `archivecited`.

### 1.3 What that does to section 8

`[LJ-1.356]` section 8 writes: "**The live half did NOT decay.** MEASURED:
each of the eleven briefs cites two to four live prior-task reports". The
measurement is probably true. **It is a measurement of a practice DD18 does
not ask for.**

Section 12 makes the category error explicit and load-bearing:

> "The rule-is-wrong criterion does not apply either: **DD18 was followed in
> substance for the live route** across the same eleven briefs, so the rule is
> followable."

**That sentence is false, MEASURED against `dev/PLAN.md:608` and against
`scripts/gate/check-archive-cited.py:26-27`.** It is the sentence that
switches off the abort criterion, so the error is not cosmetic.

### 1.4 The honest form, and the orchestrator was closer to right

On the eleven briefs LJ-1.344 to LJ-1.354, R1 reports **1 of 4 corpora named**,
every time. The one named is `TASKS-archived.md`, read at its header. **Inside
DD18's scope there is no healthy half.** DD18's substance decayed to ritual in
11 of 11.

**So the brief's original premise, "the form survived and the substance
decayed", stands.** The correction that narrowed it was flattering and wrong.
The orchestrator's stated failure mode, accepting a well-argued correction
inside an hour, produced exactly the outcome it predicts.

### 1.5 What it does to the CURE, and here I split from the obvious conclusion

**The cure is NOT mis-aimed.** R1, R3 and R4 all aim at the archives, which is
all of DD18. The correction changed the JUSTIFICATION, not the target.

**But the design loses a real coverage hole because of it.** R2 only reads a
bullet that already contains an archive-shaped path,
`agents/tasks/LJ-1-357/probe_357_rerun.py:112`, `if CITED.search(bullet)`.
**A brief whose ARCHIVE section is 100 percent live citations therefore has
ZERO bullets in R2's universe.** The fully drifted brief, which is the case
`check-archive-cited.py` was written to print, is invisible to R2. INFERRED,
from the code; I did not construct such a brief.

**A corrected design must add the drift signal `check-archive-cited.py`
already computes, and must not treat live citations as compliance anywhere.**

---

## 2. ATTACK 2. The R4 "decisive run" is a near-miss, and its counterfactual is refuted

I copied the prototype to `agents/tasks/LJ-1-357/probe_357_rerun.py` and ran
it. Command:
`.venv/bin/python agents/tasks/LJ-1-357/probe_357_rerun.py --recent`.

### 2.1 The actual printout on LJ-1.353

```text
R4 TERM XREF over the last 12 briefs (advisory)
  LJ-1-353: MISSED CANDIDATES in archive/src:
      archive/src/2026-08-09-rud-route/Everything.lagda.md matches terms ['Cantor-Bernstein']
      archive/src/2026-08-09-rud-route/rud-route-src.patch matches terms ['Cantor-Bernstein']
      archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md matches terms ['Cantor-Bernstein']
```

**Three files print, not two.** The report says two. The third is
`rud-route-src.patch`, a patch file and not a chapter.

**`L/Cardinal.lagda.md` does not print.** That is the file with the 82-line
CSB.

### 2.2 The stated cause is CORRECT, and I confirm it

`grep -c "Cantor-Bernstein" archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md`
returns **0**. MEASURED. The file spells the theorem
"Cantor-Schroeder-Bernstein" at `:7`, `:18`, `:70` and `:72`.

I also tested the alternative cause and it is ruled out. R4 drops a path the
brief already cites. `agents/tasks/LJ-1-353/LJ-1.353.md` cites only
`archive/dev/TASKS-archived.md`, at `:146`. **So the exclusion did not hide
the file. The synonym did.** `[LJ-1.356]`'s section 5 diagnosis is right.

### 2.3 Is it a catch or a near-miss presented as a catch

**A near-miss, and the report should say so in section 2 where it says
"DECISIVE".** Section 5 is honest; section 2 is not, and section 2 is what a
reader quotes.

**Would a reader of R4's output have opened `Cardinal.lagda.md`?** The path
exists but it needs a second search with a different spelling.
`Everything.lagda.md:266` describes `L.Cardinal` as holding "the general
Cantor-Schroeder-Bernstein". The R4 hit in that file is at `:313`, inside the
`L.CardinalPredicates` entry, which says the opposite of what the reader
wants: "no consumer ever owes a Cantor-Bernstein argument".
`CardinalPredicates.lagda.md:10` says the same. **Both hits point AWAY from
the proof.** INFERRED, from reading the two matched lines as the reader would.

**This is C-57 exactly. The search did not return the answer, so the reading
cannot be blamed.**

### 2.4 The counterfactual is REFUTED, MEASURED

Section 2 claims: "It is what would have stopped `[LJ-1.107]`". **That run was
never made.** I made it, with the prototype's own functions, in
`agents/tasks/LJ-1-357/probe_357_r4_counterfactual.py`:

```text
=== LJ-1-107: /Users/alsg/Agentic/Bedrock/agents/tasks/LJ-1-107/LJ-1.107.md ===
  R1: ['names 0 of 4 corpora, absent: CODE, TASKS, JOURNAL, DECISIONS']
  ARCHIVE section length: 738 chars
  R4 kept terms: []
  R4 MISSED CANDIDATES: NONE
```

**R4 keeps zero terms and prints nothing.** The reason is simple and it is
general: `grep -n "Cantor\|Cardinal\|Bernstein" agents/tasks/LJ-1-107/LJ-1.107.md`
returns **zero hits**. **R4 extracts its terms from the brief, so a brief that
never names its subject cannot be cross-referenced.**

`[LJ-1.356]` names this false negative itself, in section 5: "**R4, the
unnamed subject.** ... INFERRED, not yet measured." **It is now MEASURED, and
it is the exact case the design's own headline claim rests on.** The report
therefore contradicts itself between section 2 and section 5, and section 2
wins in every quotation.

**R1 would have shouted at `[LJ-1.107]`, at 0 of 4.** That rescues the design
and not the sentence. **The design's one counterfactual belongs to R1, never
to R4.**

---

## 3. ATTACK 3. R1 is a NEW RULE wearing DD18's clothes

**Verdict: R1 does not enforce DD18. It tightens it. The owner must rule on it
as new.**

### 3.1 The line the report leans on

`dev/PLAN.md:608`: "listing what may bear on the task **in each archive**".
The phrase does distribute over the four corpora. **Read alone, it supports
the enumeration.**

### 3.2 The line the report did not quote, in the same row

The same row states its OWN satisfaction condition, in the 2026-08-10
enforcement paragraph:

> "`dispatch.py` REFUSES a brief that carries no ARCHIVE section, and refuses
> one that carries no LITERATURE section, on every brief regardless of kind.
> **Each is satisfied by one honest line naming the corpus and saying nothing
> in it bears on the task.**"

**"Each" is each of the two SECTIONS, and the corpus is singular. DD18's own
gate is one line per section, not four lines per section.** MEASURED, by
reading `dev/PLAN.md:608` whole.

### 3.3 So the row contains both readings, and the gate half is explicit

DD18 states the enumeration as an ASPIRATION and states one line as the
SATISFACTION. **A checker must implement the satisfaction clause, or it is a
new rule.** R1 implements the aspiration and calls it enforcement.

**That is a DD19 problem and not a small one.** `AGENTS.md` warns that "a row
claiming more than its checker delivers is false safety". The mirror defect is
a checker demanding more than its row states, and the cost is the same: an
author cannot tell the rule from the tool.

### 3.4 The "256 of 256" is suspicious in the second direction, and here is why

My run gives **256 of 257** and names the one that passes:

```text
R1 PASSING briefs: ['LJ-1-357']
```

**The only compliant brief in the corpus is the one written by the
orchestrator AFTER `[LJ-1.356]` reported the rule.** That is evidence R1 is
writable. It is also evidence that nobody wrote it that way in 257 tries.
**A rule that 256 of 257 authors never derived from the row is not the row's
plain meaning.** INFERRED, from the rate.

### 3.5 Two measured over-reaches in R1 as prototyped

- **`dev/ARCHIVE.md` fails the CODE test.** R1's CODE pattern is `archive/src/`,
  `probe_357_rerun.py:52`. DD18 names `dev/ARCHIVE.md` inside the same corpus,
  `dev/PLAN.md:608`. **A brief that surveys pre-route retirements through the
  registry DD18 names scores 0 for CODE.** MEASURED, by reading the regex.
- **A path spelling is not a survey.** `agents/tasks/LJ-1-107/LJ-1.107.md:140-157`
  carries a 738-character ARCHIVE section that cites five retired-route records
  under their pre-move `_build/` paths. **R1 scores it 0 of 4.** The epoch would
  freeze it, so this is not a live failure. **It shows what R1 measures, which
  is path spelling.**

---

## 4. ATTACK 4. The DD4 precedent, three numbers and one inference

### 4.1 Number 1 VERIFIES

`.venv/bin/python scripts/gate/check-dd4-stated.py` prints:

```text
check-dd4-stated: 245 of 257 live brief(s) state DD4, 12 frozen pre-epoch
```

The report said 244 of 256. **One brief was added since, and it states DD4.
The number is sound.**

### 4.2 Number 2 IS NOT REPRODUCIBLE, and my re-derivation disagrees

The report attributes "distinct in 241 of 243" to "the `dd4dup.py` probe".
**`ls agents/tasks/LJ-1-356/` shows `lj-1.356-report.md`, `LJ-1.356.md` and
`probe_dd18_shout.py`. There is no `dd4dup.py`.** MEASURED. **A number whose
instrument was not delivered cannot be audited**, and D-1 says a probe is
written in the task directory and kept.

I re-derived it in `agents/tasks/LJ-1-357/probe_357_dd4_distinct.py`, which
strips DD4's fixed sentences, drops inline code, and hashes the rest:

```text
briefs with a DD4 section: 245
distinct engagement tails : 237
duplicate groups          : 6
  4 share one tail: ['LJ-1-179', 'LJ-1-180', 'LJ-1-181', 'LJ-1-182']
  2 share one tail: ['LJ-1-184', 'LJ-1-185']
  2 share one tail: ['LJ-1-200', 'LJ-1-201']
  2 share one tail: ['LJ-1-335', 'LJ-1-348']
  2 share one tail: ['LJ-1-343', 'LJ-1-344']
  2 share one tail: ['LJ-1-347', 'LJ-1-351']
```

**Six duplicate groups over 14 briefs, and one group of four.** The report
says "only two pairs duplicate". My normalization is more aggressive than the
report's, so the two figures are not the same measurement. **That is the
point: the claim is normalization-dependent and the normalization was not
shipped.**

### 4.3 Number 3 is REFUTED by a counterexample

The report says the fixed-line failure "exists in DD4 only as the RULE
SENTENCE ... The variable half never decayed."

`agents/tasks/LJ-1-303/probe-rulebundle-brief.md:13-15` carries a DD4 section
whose entire content is:

> Maximize the code the two proofs share, and write it generic.

**Zero engagement words.** I state its weight honestly: it is a probe fixture,
not a dispatched brief. **But `check-dd4-stated.py` counts it as one of the
245, and `agents_tree.briefs()` returns it.** So the corpus that carries the
report's own number contains a DD4 section with no variable half at all.

### 4.4 The INFERENCE fails. Distinct is cheap, and here is the proof

The report infers task-specific substance from distinct text. **Read
`LJ-1-343` against `LJ-1-344`:**

`agents/tasks/LJ-1-343/LJ-1.343.md`, DD4 section:

> **`[LJ-1.341]` measured that the repair is CLASS-FREE, so it is written once
> and serves both ends.** **Confirm that, and report the closure**, noting
> `dev/ledger.toml:204` ...

`agents/tasks/LJ-1-344/LJ-1.344.md`, DD4 section:

> **`[LJ-1.341]` measured that the repair is class-free, so it is written once
> and serves both ends.** **Say whether your SUPPLY keeps that property**, and
> note `dev/ledger.toml:204` ...

**The two differ by the case of one word and by one verb phrase.** A
case-sensitive hash calls them distinct. A reader calls them the same
paragraph. `LJ-1-347` against `LJ-1-351` is the same shape: the second drops
the clause "which is AC-against-GCH".

**So "distinct" does not prove "task-specific".** The precedent supports LESS
than section 7 claims. **The mechanism DD4 actually demonstrates is weaker and
still useful: a heading gate keeps the rule VISIBLE. It does not keep it
answered.**

### 4.5 Is the argument fair to DD4

**Partly.** It treats DD4 as evidence rather than as background, which the
brief asked for, and it correctly identifies the shape difference: DD4's
minimal form asks about THIS task and DD18's minimal form asks about a corpus.
**That distinction is the design's best idea and I uphold it.**

**It is unfair in one way.** DD4 has NO METRIC by ruling, because a count
would be gamed the moment it gated anything. **The report then imports a
count, R2's five-brief threshold, into the same architecture.** The objection
transfers, and it is measured twice:

- The report's own section 5 records the split: "Take SHAPE from the archive"
  against "taking SHAPE", 40 caught of 155.
- My section 4.4 shows one capitalization defeating a hash.

**The gaming cost of R2 is one keystroke, MEASURED twice.** The report's
proposed `dev/PLAN.md` text wires R2 into `make check` beside two refusals,
which makes it a gate. **R2 must print and never gate, for DD4's own reason.**

---

## 5. ATTACK 5. R3's failing tasks, classified, and the headline is wrong

My run reports 92, not 93. The corpus moved by one task since. **The count is
not the problem. The composition is.**

I classified all 92. Command and code:
`agents/tasks/LJ-1-357/probe_357_rerun.py` functions, driven inline.

```text
failures whose ONLY defect is a missing LITERATURE USED heading: 51
failures with at least one unanswered path: 41
unanswered paths ANSWERED BY A DEEPER PATH (false positive): 30
unanswered paths with NOTHING under them in the report: 25
tasks with >=1 GENUINELY unanswered path: 17
```

**`[LJ-1.356]` writes: "Most cite an archive path the report never names
again." MEASURED FALSE. 51 of 92, which is 55 percent, cite no unanswered path
at all.** The report read its own tool's output and reported the opposite of
what it says. That is C-57 at the reading end.

### 5.1 Defect class A. The LITERATURE heading, 51 tasks, CHECKER OVER-REACH

R3 demands a LITERATURE USED heading from every report. **DD18 does not.**
`dev/PLAN.md:608`: "**A brief that dispatches mathematics** carries a
LITERATURE section ... and a return carries a LITERATURE USED section". **The
duty is conditional on the task kind and R3 applies it unconditionally.**
MEASURED, from DD18's wording.

The 51 run from `LJ-1-103` to `LJ-1-218` and cluster before the literature
half was added on 2026-08-10. **An epoch fixes most of this. The conditional
does not fix itself.**

### 5.2 Defect class B. The prefix false positive, 30 of 55 paths

R3 compares path strings for exact equality. **A brief that cites a DIRECTORY
and a report that cites FILES inside it fails.** Examples, all MEASURED:

| Task | Brief cited | Report cited |
|---|---|---|
| LJ-1-166 | `archive/src/2026-08-09-rud-route/L/Coding/` | `.../L/Coding/CodeSet.lagda.md` |
| LJ-1-176 | `archive/src/2026-08-09-rud-route/` | `.../L/Cardinal.lagda.md` |
| LJ-1-215 | `archive/src/2026-08-09-rud-route/` | `.../L/Ordinal/SquareLaw.lagda.md` |
| LJ-1-144 | `agents/tasks/archive/LJ-1-76/` | `.../LJ-1-76/lj-1.76-report.md` |

**These reports answered their briefs better than the brief asked.** R3 calls
each one a failure. **This is a plain bug and it is cheap to fix with a prefix
test.**

### 5.3 Five sampled genuine failures, judged one by one

After both corrections, **17 tasks carry a genuinely unanswered path, and one
of them is LJ-1-357, whose report was a stub when the probe ran. So 16 are
historical.** Five, read in full:

1. **`LJ-1-183`. REAL.** The brief cites `archive/dev/DECISIONS-archived.md`
   with a task-specific reason, `agents/tasks/LJ-1-183/LJ-1.183.md` ARCHIVE
   section: "a `D` citation resolves only there". The report's ARCHIVE USED
   names ten sources and not that one. **Non-compliance, and DD18-shaped.**
2. **`LJ-1-181`. REAL, and it is the worst of the five.** The brief says
   "`[LJ-1.107]` rebuilt 82 delivered lines because nobody looked. Take SHAPE
   from the archive". The report's ARCHIVE USED cites only live
   `agents/tasks/` paths. **The brief warned about the exact failure and the
   return committed it.**
3. **`LJ-1-231`. REAL.** Brief cites `archive/dev/TASKS-archived.md` for a
   pairing on `ω`. The report's ARCHIVE USED, `:10`, lists five live task
   paths and answers neither archive citation.
4. **`LJ-1-153`. REAL IN FORM, OUT OF DD18's SCOPE.** The unanswered path is
   `agents/tasks/archive/LJ-1-97/ProbeLJ197A.agda`. **That is the retired-task
   tree, which is NOT one of DD18's four corpora.** The report also shows the
   author knows how to decline: "`agents/tasks/LJ-1-151/LJ-1.151.md`: not
   read; its content reaches me through the report". **So R3 is enforcing
   "answer your brief", which is WIDER than DD18.**
5. **`LJ-1-168`. CHECKER OVER-REACH, and it is the class the brief named.**
   The brief cites
   `archive/src/2026-08-09-rud-route/L/LevelFormula.lagda.md`, 258 in-fence.
   **The report DECLINES it, in writing**, at
   `agents/tasks/LJ-1-168/lj-1.168-report.md:573`:

   > `L/Coding/CodeSet.lagda.md`, `L/LevelFormula.lagda.md`: **NOT read.**

   **R3 flags it because the decline spells the path relative to the archive
   root, so the exact string match fails.** MEASURED. **DD18 allows the
   decline; R3 punishes its spelling.** A production version must accept a
   basename or a suffix match.

**Judgment: R3 finds real signal, and the honest rate is about 15 tasks, not
93.** One of my five samples is over-reach, one is out of DD18's scope, and
three are real. **On that sample the false-positive rate of the surviving 16
is about one in five.** Point 4 says the rule R3 enforces is wider than DD18.
**That is a good rule. It must be proposed as one.**

---

## 6. ATTACK 6. The proposed diffs, read as an editor

### 6.1 The `AGENTS.md` insert OVERSTATES, and it is the more dangerous of the two

Proposed text, section 11:

> A brief's ARCHIVE section names each of the four corpora, cited or declined
> in one line. A return answers every archive path its brief cited. Both are
> refused by the dispatch tool and by `make check`, and a repeated verbatim
> citation line across five briefs shouts TEMPLATE.

**Three defects, in order of seriousness.**

1. **It states an enforcement that does not exist.** The report says plainly:
   "`make check` needs a `dd18survey` target and the checker file under
   `scripts/gate/`, **which I did not write**". **C-48: a policy that only a
   document states is not enforced. C-45: `exit 0` is not a supply.** If the
   insert lands before the checker, `AGENTS.md` asserts false safety, which
   its own rules table forbids.
2. **It drops the mode caveat the PLAN diff keeps.** The report's section 3 is
   honest: the dispatch half is "codex path only" and is DEAD under
   `in-harness-subagent-mode`. **The `AGENTS.md` sentence says "refused by the
   dispatch tool" with no PARTIAL marker.** The rules table tells a reader to
   "believe the enforcement column when it says PARTIAL". This one would not
   say it.
3. **It breaks the prose rules `AGENTS.md` itself states.** The third sentence
   is 22 words against a 20-word limit for an instruction, uses the passive
   ("are refused") against the active-voice rule, carries two instructions in
   one sentence, and builds the four-word noun cluster "repeated verbatim
   citation line" against a three-word limit. **A rulebook edit that breaks
   the rulebook's own style is not ready.**

**It is also inaccurate on scope.** The second sentence, "A return answers
every archive path its brief cited", is R3, and my section 5.3 point 4 shows
R3 covers `agents/tasks/archive/`, which DD18 does not name. **The sentence
is wider than DD18 and sits in DD18's paragraph.**

### 6.2 The `dev/PLAN.md` diff is better, and it still needs two changes

Credit where it is due. It is marked "(proposed LJ-1.356)", it keeps the mode
split, it keeps relevance with review, and it keeps a fabricated line with the
audit. **That is honest drafting.**

Two changes:

1. **It writes a future state in the present indicative.** "`dispatch.py`
   refuses ..." is not true today. **The row must not land before the code.**
2. **It gates R2.** "shouts TEMPLATE when one ARCHIVE bullet's reason text
   repeats verbatim across five briefs", inside a `make check` target, is a
   gate. **Section 4.5 measures the gaming cost at one keystroke. R2 prints.**

### 6.3 One factual sentence to strike

"It prints archived CODE matching the brief's subject terms and uncited" is
literally true. **The narrative around it is not**, per section 2.4. **If the
diff lands with section 2's "decisive" framing in the record, the owner rules
on a counterfactual that MEASURES as false.**

---

## 7. Findings the brief did not ask for, and one changes the history

### 7.1 `[LJ-1.107]` did NOT rebuild the CSB in ignorance. MEASURED

This is the story the whole design rests on. `scripts/gate/check-archive-cited.py:108`
prints it and `:118` repeats it: "A brief that surveys nothing is how
`[LJ-1.107]` rebuilt 82 delivered lines of ...". `[LJ-1.356]`'s brief carries
it at `:23-24`, and the report's section 9 opens with it.

**`[LJ-1.107]`'s own report contradicts it.**
`agents/tasks/LJ-1-107/lj-1.107-report.md:235-238`, in its ARCHIVE USED
section:

> `_build/l3.32-t21-report.md`, ... `_build/l3.32-t81-report.md`, read WHOLE.
> TOOK the documented extraction wall (T31 section 3 and section 5), **the CSB
> survey (T81, "keep ours", 145 lines at the retired `L.Cardinal`)**, ...

**The agent named the retired `L.Cardinal`, named its CSB, named its size, and
named the prior ruling to keep the tree's own.** The archived index confirms
the row: `archive/dev/TASKS-archived.md:116`, "`| L3.32-T81 | CSB literature
survey | COMPLETE (keep ours) |`".

**So `[LJ-1.107]` surveyed, cited, and chose.** Its own CSB is 97 lines "for
h-sets" over "the cubical Embedding fiber facts",
`agents/tasks/LJ-1-107/lj-1.107-report.md:51`. `[LJ-1.353]` later recorded why
the retired one does not transfer: "The retired carrier and its structure
instance. The retired predicates `HostBij` and `eqFo`",
`agents/tasks/LJ-1-353/lj-1.353-report.md`, "What would not transfer (DD18)".

**I do not claim the rebuild was correct. I claim the record does not support
"nobody looked".** MEASURED. **The founding cost of DD18 is misattributed in a
delivered checker, in a brief, and in the report under review.**

### 7.2 Section 9's heading says "verified" and the verification substituted a number

Section 9 verifies the SIZE of the archived block, 82 lines, which nobody
disputed. **It does not verify the attribution, which is the load-bearing
half.** That is the substitution pattern LESSONS C-39 and C-40 name.

### 7.3 The record the brief demanded does not exist, and the return did not say so

`[LJ-1.356]`'s brief, `:167-168`, orders: "`archive/dev/JOURNAL-archived.md`:
the entry for `[LJ-1.107]`, the 82 rebuilt lines. **It is DD18's founding
cost. Quote it at `file:line`.**"

**`grep -c "LJ-1\." archive/dev/JOURNAL-archived.md` returns 0.** MEASURED.
The archived journal is the RETIRED route's journal and it cannot hold an
LJ-1 entry.

`[LJ-1.356]` cited `:1368-1377` instead, a passage about the retired cardinal
chapter's rulings, and presented it as "DD18's founding cost record". **It
never reported that the record the brief demanded does not exist.** A stop is
a deliverable, and this was a small one that was available.

**This is a MEASURED instance of R3's own blindness, found inside the report
that proposes R3.** R3 checks that the report NAMES the brief's path. The
report named it. **A substituted passage passes.**

### 7.4 Two mis-cited lines in the report's own ARCHIVE USED

- **`archive/dev/TASKS-archived.md:7`.** The report quotes "Nothing here is a
  live task. Read it for history." **`grep -n` puts that line at `:8`.**
  MEASURED. The brief carried the same `:7`, so the error was inherited and
  not caught.
- **`archive/dev/JOURNAL-archived.md:1370`.** The report gives that line as
  the "Line read" for "define equinumerosity as the existence of a BIJECTION,
  not as injections both ways". **That text is at `:1368-1369`. Line 1370
  reads "per-consumer Cantor-Bernstein obligation and drags the general
  theorem into W7 anyway".** MEASURED. Its section 9 range `:1368-1377` also
  misses its own second quotation, "which is the rebuild D16 exists to
  prevent", which sits at `:1379-1380`.

**Section 5 of the report says the fabricated line is "INFERRED ... no
fabricated line was found in the corpus". That negative is now upgraded.**
Three mis-cited lines exist, all in the report that proposes the mechanism,
and all pass R3. **I call them inherited and careless rather than fabricated.
The mechanism cannot tell the difference, which is the point.**

---

## 8. What I UPHOLD, stated so the design is not thrown away

1. **"Gate the ENUMERATION, not the relevance" is the right idea**, and the
   argument from DD4's shape is the report's best contribution.
2. **R3 is the genuinely new and mode-proof half.** The brief defines the
   universe, so a content check is possible where `dispatch.py` could read
   only a heading. It finds 16 real historical misses.
3. **The R4 synonym diagnosis is correct**, section 2.2, and the cure
   (matching hyphen components) follows from it.
4. **The costs hold.** My run reproduces them: R1 and R2 under 0.1 s, R3 0.3 s,
   R4 0.4 s over 12 briefs.
5. **The DECISIONS-archived negative HOLDS.** I checked it independently.
   `archive/dev/DECISIONS-archived.md` D20 at `:42` is the archive regime,
   "Retired code is archived, never deleted", and it governs RETIRING and not
   SURVEYING. D22 at `:44` puts a probe duty in a build brief, which is the
   nearest shape and is not a survey duty. **No archive-survey rule existed on
   the retired route, so no rule died once.** MEASURED, `grep -n "survey"` over
   the file plus reading D20, D22 and D39.
6. **The LITERATURE negative HOLDS.** See section 10.
7. **The false-negative table, section 5, is honest**, and it is the part of
   the report that a corrected version should keep unchanged.

---

## 9. ARCHIVE USED (DD18)

One line read per archived file. Archived CODE first, as the brief orders.

- **`archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:7`.** Line read:
  "that definition left standing. **Cantor-Schroeder-Bernstein** upgrades
  two". **TOOK the confirmation that defeats R4's term match**, with the
  MEASURED companion `grep -c "Cantor-Bernstein" = 0` over the whole file.
  Also opened `:70`, `:72` and `:89`, the `module CSB` line, so the claim is
  not a header reading.
- **`archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md:10`.**
  Line read: "per-consumer Cantor-Bernstein obligation; and the predicates are
  built as the". **TOOK it as one of the two files R4 DID print, and read it
  as the reader would: it says no consumer owes a CSB argument, which points
  AWAY from the proof.** That is attack 2.3's evidence.
- **`archive/src/2026-08-09-rud-route/Everything.lagda.md:266`.** Line read:
  "new half, the general Cantor-Schroeder-Bernstein (which the installed
  library does not". **TOOK the one path from R4's output back to
  `L.Cardinal`**, and noted that the R4 hit in this file is at `:313`, 47
  lines away, inside a different catalog entry.
- **`archive/dev/JOURNAL-archived.md:1369`.** Line read: "of a BIJECTION, not
  as injections both ways**, since the latter turns every equality into a".
  **CORRECTED `[LJ-1.356]`'s citation of the same text at `:1370`**, and
  corrected its range `:1368-1377`, which excludes its own second quotation at
  `:1379-1380`. The quotation itself is genuine.
- **`archive/dev/DECISIONS-archived.md:42`.** Line read: row D20, "Retired
  code is archived, never deleted." **TOOK it as CONFIRMING `[LJ-1.356]`'s
  negative**: D20 governs retiring and not surveying, and no row in D1 to D39
  states a survey duty.
- **`archive/dev/TASKS-archived.md:8`.** Line read: "**Nothing here is a live
  task. Read it for history.**" **CORRECTED the `:7` that the brief and the
  report both carry.** **TOOK also `:116`, row `L3.32-T81`, "CSB literature
  survey | COMPLETE (keep ours)", which is the row that overturns the founding
  cost story in section 7.1.** That row is this review's archive find.

---

## 10. LITERATURE USED (DD18)

**`dev/literature/` holds 16 files**, MEASURED, `ls dev/literature/ | wc -l`.
The count matches `[LJ-1.356]`'s.

**Spot-check of the named nearest file, as the brief ordered.**
`dev/literature/formalizations-landscape.md`, 421 lines. **It holds NO process
mechanism.** MEASURED. The file states its own scope at `:1-12`: a landscape
sweep of Mizar, Metamath, Naproche, the AFP, Lean mathlib and Coq for
constructibility content, with a method paragraph at `:11-12` saying "every
system below was searched through its OWN index or repository". Its content
is entry names, URLs and fetch dates, for example `:182-194` on the AFP set
theory entries. **WHY NOT: it is a survey of WHAT other projects formalized,
never of HOW a project enforces a rule. It supplies no checker design, no gate
design and no brief-section design.**

**WHY NOT the other 15**, by name and by kind: `digest.md`, `j-hierarchy.md`,
`fine-structure.md`, `rudimentary-functions.md`, `devlin-II5.md`,
`devlin-errata.md`, `level-formula-slot-roles.md`, `truncation-and-selection.md`
and `geology.md` are mathematics digests. `primary-sources.md`,
`BIBLIOGRAPHY.md` and `formalizations.md` are source registers.
`glossary-review-2026-08.md` and `terms-2026-08.md` are terminology.
`owner-notes-rud.md` is route notes. **None treats rule enforcement.**
`[LJ-1.356]`'s negative HOLDS.

---

## 11. DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker. **NAME YOUR AXIS** (C-46), AC-against-GCH,
fixed at `scripts/measure/ledger.py:50`.

**This review writes no mathematics and lands no line, so its closure delta is
zero on both ends.** Its DD4 content is the one in section 4.5: **DD4's
no-metric ruling transfers to DD18, and the design imported a count anyway.**
R2's five-brief threshold is a metric on a rule whose parent forbids one, and
the gaming cost is MEASURED at one keystroke twice. **DD4 is treated fairly by
section 7's shape argument and unfairly by section 11's proposed gate.**

---

## 12. Abort criterion (D-1)

**Not triggered as a stop; triggered as an OVERTURN, which is the deliverable.**
The target was not false and the price was not wrong. **The premise the review
was sent to test IS wrong**, and the brief predicted the shape correctly.

**One rule I did not break.** I landed nothing, repaired nothing, wrote only
in `agents/tasks/LJ-1-357/`, touched no `src/`, ran no Agda, and did not
commit. The three probes I wrote are in this directory and run today.

## 13. Probes written

- `agents/tasks/LJ-1-357/probe_357_rerun.py`, a copy of the prototype, run
  unmodified for section 2 and section 5.
- `agents/tasks/LJ-1-357/probe_357_r4_counterfactual.py`, the run
  `[LJ-1.356]` did not make. **It is the file that refutes section 2's
  counterfactual.**
- `agents/tasks/LJ-1-357/probe_357_dd4_distinct.py`, the missing `dd4dup.py`,
  rebuilt for section 4.

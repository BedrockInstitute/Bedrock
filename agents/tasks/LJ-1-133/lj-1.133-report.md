# LJ-1.133 report: give the probes a lifecycle, and settle where evidence lives

Status: **DONE.** Point 1 resolved. `src/` went from 284 probes to 98. Every
checker I ran is green. Nothing is committed. Nothing is pushed.

## 1. POINT 1: the question conflates two objects, and the data separates them

**A report is the evidence for a VERDICT. A probe carries a TERM. Neither one
is the evidence for the other.**

A verdict is a sentence and copies into prose without loss. A term does not.
That is the whole answer, and it decides every file.

### The pair that settled it

I read `agents/reports/lj-1.118-report.md` against `src/ProbeLJ1118A.agda`,
now `archive/probes/ProbeLJ1118A.agda`. That report is high quality. It quotes
the type of `site-inj` at `:19`, the type of `out` at `:90-93`, and the types
of `decomp` and `stage-shift` at `:106-107`. Every VERDICT is in the report:
GREEN, 3.14 s, 13 code lines against an inferred 20 to 30.

**It does not carry one line of the proof.** At `:75` it writes:

```
| the generic absorption (`AbsorbsIn`) | `src/ProbeLJ1118A.agda:72-130` | 49 |
```

That is a location and a line count for a 49-line term. The term itself is at
`archive/probes/ProbeLJ1118A.agda:72-130` and nowhere else. **Reports quote
types. They do not quote proofs.** MEASURED across the corpus: all reports and
briefs together hold 7,937 non-blank lines inside ` ```agda ` fences, against
110,471 code lines in the probes they cite.

### So the useful split is not cited against uncited

**It is whether a document points INTO the file.** Three forms count, and I
measured each:

| Form | Example | Probes |
|---|---|---:|
| A line-number citation | `src/ProbeLJ1118A.agda:72-130` | **132** |
| Prose that sends the reader there | "in full", "diff against", "verbatim" | **20** |
| A name in a `dev/` document | `dev/LESSONS.md:3378` | **21** |

MEASURED: **986 line-number citations** of probe files exist across reports,
briefs and `dev/`. 971 of them land inside the file they name; 15 point past
its end. Only 5 probes were edited after a document cited them, so the line
numbers are 98 percent trustworthy. **These citations resolve against the file
and against nothing else.**

### The counterexample that stopped the bulk deletion

I sampled eight probes cited by NAME ONLY, with no line number, and read every
citing passage. **Two of the eight had reports that send the reader into the
file.**

- `agents/reports/archive/lj-1.39-report.md:128`: "Diff `src/ProbeLJ139V2.agda`
  against `src/ProbeLJ139.agda` for the exact edit list."
- `agents/reports/archive/lj-1.31-report.md:121`: "`src/ProbeLJ130B.agda` in
  full. It is the adequacy proof model. I ported"

Six of the eight were fully self-sufficient: `ProbeLJ1105A` is "GREEN, exit 0,
2.88 s warm", `ProbeDD25B13` is a table row "16 | 3919 | WALL | 65.27".

**So the name-only class is MIXED, and no regex settles it.** I wrote a
detector from those two counterexamples and it found 20 of 117. A regex fitted
to its own counterexamples cannot be trusted for recall. **I left that class
alone and the checker never deletes it automatically.** That is the honest
limit and I state it in the tool's docstring.

## 2. THE COUNTS, before and after

| | Before | After |
|---|---:|---:|
| Probes in `src/` | **284**, 9,300 KB | **98**, 3,348 KB |
| `archive/probes/` | 5 files, 100 KB | **160 files**, 5,336 KB |
| Tracked probes | 0 | 0, and the gate now permits 160 |

The brief's figure was 283. A sibling agent wrote `src/ProbeLJ1134A.agda`
during my run, which is the 284th. **I did not touch it.** The freshness rule
protected it with no help from me: at the archive run it read "modified 0.0h
ago, inside the 6h freshness window", and it is still on disk and still
growing.

### The four verdicts

| Verdict | Files | What I did |
|---|---:|---|
| **FRESH** | 15 | Nothing. An agent may still be writing them |
| **EVIDENCE** | **155** | Moved to `archive/probes/` |
| **NAMED** | **83** | **Nothing. A human must read the report** |
| **ORPHAN** | **31** | Deleted |

15 + 155 + 83 + 31 = 284.

### Citations rewritten: 27

| Document | Citations |
|---|---:|
| `dev/LESSONS.md` | 22 |
| `dev/ledger.toml` | 3 |
| `dev/memos/L3.30-rud-route.md` | 1 |
| `dev/memos/L3.32-below-lim-design.md` | 1 |

**Only LIVE `dev/` documents were rewritten.** Every report and every brief
keeps its old `src/Probe*.agda` path. `[LJ-1.130]` ruled that a brief and a
report are frozen records, corrected in the next one and never rewritten, and
`[LJ-1.132]` followed it. This report is that correction, and
`archive/probes/README.md` records the stale path against the new one.
MEASURED: zero `src/Probe*.agda` paths naming a moved file remain in `dev/`.

**`dev/memos/L3.30-rud-route.md:6` was already stale** before I started. It
cited `src/ProbeRudComp.agda`, which `[LJ-1.132]` moved yesterday.

## 3. THE DEFECT I FOUND, and it was live and armed

**`scripts/check-probes.py --stale --delete` would have deleted 234 probes
today, and it printed "234 probe(s) safe to delete" to say so.**

Of those 234:

- **21 are named by `dev/LESSONS.md`** as the provenance of live rules.
  `ProbeDD25F41A` through `D` are the provenance of the rule at `:3307-3330`;
  `ProbeLJ171A` and `ProbeLJ177A` are cited at line numbers at `:3458` and
  `:3489`.
- **47 carry a line-number citation from a LIVE document.**
- **119 carry a line-number citation from some document.**

MEASURED: I imported `stale_probes()`, ran it, and crossed its "safe" list
against the citation index. **This is `[LJ-1.132]`'s finding repeating: at
`dev/LESSONS.md:1012` rule I-2 cited a probe that `make clean` could take.**
The same shape, a different directory, and nobody had looked.

**The old rule was backwards.** It called a probe safe when a report NAMED it,
on the reasoning that the verdict survives. It is the naming that creates the
danger, because a name at a line number is a pointer.

## 4. HOW `scripts/check-probes.py` CHANGED, and what it now protects

### 4.1 `classify()`: one exemption, and `src/` is not weakened

`archive/probes/` is now the ONE prefix where a probe may be tracked
(`scripts/check-probes.py:57-63`). Everything else keeps the old refusal.

**Verified end-to-end, both directions:**

| Test | Result |
|---|---|
| `git add -f src/ProbeLJ1133GateTest.agda`, then `--staged` | **exit 1, REFUSED.** I then unstaged and deleted the file |
| `git add archive/probes/ProbeDD25C.agda`, then `--staged` | **exit 0, accepted** |
| `archive/probes/ProbeX.agdai` through `classify()` | **refused.** A build output is never committed, archived or not |
| `archive/src/L/Probe.agda` through `classify()` | **refused.** The exemption is the prefix, not the word |

**The second row is what unblocked `[LJ-1.132]`.** Its commit failed on this
gate today and it did not bypass it.

### 4.2 `probe_verdicts()`: four verdicts, and only two are automatic

It replaces `stale_probes()`, which nothing outside the file called. MEASURED:
the only callers are `Makefile:82` and `scripts/git-hooks/pre-commit:16`, and
both use `--check` and `--staged`.

The test order is the design. **Freshness runs first**, because a live agent's
file is never touched for any reason.

- `--archive` moves the EVIDENCE group. `--delete` removes the ORPHAN group.
- **NAMED is never automatic.** The docstring says why, in the words of
  section 1.

### 4.3 Two recall bugs I found by testing my own detector

**Range and brace shorthand.** `agents/reports/archive/lj-1.74-report.md:209`
names `src/ProbeLJ174A..F.agda` and `src/ProbeLJ174P0..P3.agda`, and
`dev/LESSONS.md:3330` names `src/ProbeDD25F41{A,B,C,D}.agda`. **A stem
substring test cannot see the members those citations name.** Three probes,
`ProbeLJ174E`, `ProbeLJ174P2` and `ProbeLJ174P3`, were in my delete list
because of it. **This is exactly the shape that bit `[LJ-1.132]` at
`agents/reports/lj-1.128-report.md:86`**, where four logs were written
`-run3.log`, `-run4.log`, `-run5.log`. The cure is deliberately blunt: a
shorthand puts its WHOLE family beyond ORPHAN. It rescued exactly those three.

**The optional `.agda`.** `agents/reports/archive/lj-1.54-report.md:43` writes
`ProbeLJ154A:61`, with no extension. Requiring `.agda` read that file as
merely NAMED. The extension is now optional. This changed no verdict today,
MEASURED, because another citation had already caught that file.

### 4.4 The `dev/` clause, added after the first archive pass

After the first `--archive` run, **six probes that `dev/LESSONS.md` names were
still in `src/`**: `ProbeDD25C`, `ProbeDD25E1`, `ProbeDD25F41B`,
`ProbeDD25F41D`, `ProbeLJ147PairingGut`, `ProbeLJ147PairingSealed`. They were
named without a line number and without pointer prose. **A `dev/` document is
a binding rule, not a frozen record, and a rule whose provenance cannot be
opened is a rule nobody can check.** The clause is now in the tool and those
six are archived.

### 4.5 `--index`: the archive table is derived, never transcribed

Once a probe leaves `src/`, `probe_verdicts()` stops seeing it, so the
citation that justified keeping it would be lost if a hand-written table were
the only record. `scripts/check-probes.py --index` regenerates the 160-row
evidence table in `archive/probes/README.md` between markers. That is
`archive/tooling/README.md`'s "derive, never transcribe", which `[LJ-1.132]`
applied to `_build/README.md`.

## 5. DID THE `[LJ-1.132]` CLASSES FIT? Yes, and the fit is exact

**A probe is `working` while its task runs and `evidence` the moment a
document points into it.** `[LJ-1.132]` wrote that transition itself:
"`working` [...] If the report cites it, it is `evidence`." **I needed no new
class and I added none.** Two regimes for one problem is worse than one
imperfect regime, and this is one regime.

**The class that caused the backlog is `evidence`, exactly as `[LJ-1.132]`
found.** Its rule is that `evidence` has NO resting place: it leaves the
moment anything cites it. **`src/` is `_build/` all over again**, and the
numbers are worse. `.gitignore:25` ignores every `.agda` under `src/`; 284
files and 9.1 MB sat there; 986 line-number citations pointed into them; and
one `git clean -xdf` took the lot.

**One refinement the `_build` regime did not need.** `[LJ-1.132]` noted its
checker cannot tell `evidence` from `exhaust` because "only the agent who ran
the command knows that". For probes the discriminator is partly mechanical:
**a citation that points into the file is visible in the citing document.**
That is why this checker can act where `check-build-manifest.py` only names.
It is only PARTLY mechanical, which is what the NAMED class records.

**`_build/` has a manifest and `src/` does not, and it does not need one.**
`src/` holds exactly two species: masters, which are `.lagda.md` and tracked,
and probes, which are `.agda` and are not. `check-probes.py` reads the species
off the shape.

## 6. THE `AGENTS.md` LINE I PROPOSE, for the owner's ruling

**I did not edit `AGENTS.md`.** DD19 needs the owner's ruling and a dated
`AGENTS-diff-approved:` trailer.

**The Never list at `AGENTS.md:49` needs NO change.** MEASURED: it already
reads "probe files (`src/Probe*.agda`)", scoped to `src/`, so the exemption is
already outside what it forbids. **This is the rule being narrower than I
expected, and I am reporting it rather than proposing an edit nobody needs.**

**One sentence at `AGENTS.md:136-138` is now false.** It reads "Nobody commits
one (`scripts/check-probes.py` enforces both halves...)". Proposed
replacement:

> A probe is thrown away once its verdict is recorded, and `src/` is where it
> may never be committed (`scripts/check-probes.py` enforces that, because
> `git add -f` walks past an ignore rule). **The exception is a probe a
> document points INTO at a `file:line`: it has become the evidence for a
> checkable claim, and it goes to `archive/probes/`.** Run
> `scripts/check-probes.py --stale` when your task closes.

That is 78 words against the 50 it replaces. **The word cap.**
`scripts/check-dev-docs.py` is green today, MEASURED, exit 0 on 6 subchecks. I
did not verify the post-edit count, because I did not make the edit.

**I DID edit `archive/README.md:26-29`**, which said the refusal "is CORRECT
until `[LJ-1.133]` teaches it the difference". That sentence is now false. It
is not `AGENTS.md` and the brief's write scope covers where I rehome.

## 7. WHAT I DID NOT DO, and what would decide it

**83 probes, about 2.5 MB, are still in `src/` as NAMED.** A document names
each one; nothing points into it. **I did not delete them and I did not move
them.**

**What would decide it: a human reading the 83 reports.** Nothing else can.
Section 1 gives the measured reason: the class is mixed at roughly one in six,
and the detector that finds them was fitted to its own counterexamples. **An
honest undecided beats a wrong deletion, and a deleted probe is
unrecoverable.**

**The cost of leaving them** is 2.5 MB of untracked files in `src/` and the
standing risk that one `git clean -xdf` takes them. It is the same risk as
before, over 29 percent of the files.

**A cheap route, if the owner wants them cleared.** Archive all 83 rather than
read 83 reports. It costs about 2.5 MB in the repository and it is reversible;
a wrong deletion is not. **I did not do it**, because the brief's default is
that an uncited probe is throwaway, and I will not commit 2.5 MB on my own
reading of a rule the owner just wrote.

## 8. EVERY NEGATIVE, MARKED

- **MEASURED.** The 31 ORPHANs are named by nothing. Two independent searches
  agree: `probe_verdicts()` over reports, briefs and `dev/`, and a
  `grep -rF <stem>` over the whole repository excluding `.git`, `_build`,
  `src` and `.venv`. **30 of 31 returned zero files.** The 31st is
  `src/ProbeDD25G2 (conflicted).agda`, a conflict copy whose 3 hits all name
  `ProbeDD25G2.agda`, a different file, 16,306 bytes against 16,196, which is
  archived and untouched.
- **MEASURED.** `check-probes.py --stale --delete` would have deleted 21
  probes that `dev/LESSONS.md` names. I imported `stale_probes()` before
  changing it and crossed its output against the citation index.
- **MEASURED.** 986 line-number citations of probe files exist. 971 land
  inside the file; 15 point past its end, all by 1 to 9 lines.
- **MEASURED.** Only 5 probes have an mtime later than a document citing them:
  `ProbeBelowLim`, `ProbeLJ155C`, `ProbeLevy`, `ProbeT126`, `ProbeT127`. All 5
  are archived, so the drift is recorded rather than fixed.
- **MEASURED.** `src/ProbeLJ1134A.agda` still exists, 12,996 bytes at my last
  check, up from 11,309. I never opened it.
- **MEASURED.** `AGENTS.md:49` scopes the probe ban to `src/Probe*.agda`. I
  read the line.
- **MEASURED.** Nothing outside `scripts/check-probes.py` called
  `stale_probes()`. I grepped `*.py`, `*.md`, `Makefile`, `*.toml`, `*.sh`.
- **INFERRED.** That the 83 NAMED probes are about one in six load-bearing.
  The rate comes from a sample of 8 and a regex over 117. **The sample is too
  small to price and the regex has unknown recall.** It is a hypothesis, not a
  price (P-l), and it is why I left the class alone.
- **INFERRED.** That the 31 deleted probes cost nothing. Nothing names them,
  MEASURED, but **I did not read their contents** and I could not have known
  what a future task might have wanted from them. `archive/README.md:23-24`
  rules this case and I followed the ruling.
- **INFERRED.** That the 15 hard-stale line numbers are off-by-a-few rather
  than genuine drift. All 15 overshoot by 1 to 9 lines, which reads like a
  range end written to the file's last line. **I did not verify one by hand.**

## 9. CHECKERS I RAN

| Command | Result |
|---|---|
| `scripts/lint-prose.py --check` | **exit 0** on all five files I wrote or edited |
| `scripts/check-probes.py --check` | exit 0, 1,320 tracked files |
| `scripts/check-probes.py --staged`, probe under `src/` | **exit 1, correctly refused** |
| `scripts/check-probes.py --staged`, `archive/probes/` | **exit 0, correctly accepted** |
| `scripts/check-tree.py --check` | exit 0, 87 masters, 7 subchecks |
| `scripts/check-rule-ids.py` | exit 0, 141 lessons, 66 decisions |
| `scripts/check-dev-docs.py` | exit 0, 6 subchecks |
| `scripts/ledger.py --check` | exit 0, standing 28,617 unchanged |
| `reuse lint` | **exit 0, 1,461 / 1,461**, up from 1,304 |

`reuse lint` covers all 155 new files through the `archive/**` carve-out in
`REUSE.toml`. **I added no `REUSE.toml` entry and none was needed.**

**I did not run `make check`. I did not run Agda.** The brief forbids both,
and 284 probes are not worth a rebuild. **I did not touch `_build/2.8.0/` or
any `src/*.lagda.md` master.**

## 10. DD4

**Nothing in this task touched a proof, so DD4 had no line to share.** The
task was a lifecycle and a checker.

Where the DD4 instinct did apply is the checker itself, and it applied twice.
**The verdict logic is written once and every mode reads it.** `--stale`,
`--archive`, `--delete` and `--index` all call `probe_verdicts()`; none
re-derives a citation test. **And the archive index is DERIVED from the
directory**, not transcribed beside it, so a 160-row table cannot drift from
the files it describes. A second hand-written copy of either would have been
the documentation equivalent of writing it fixed.

## 11. ARCHIVE USED

- `agents/reports/lj-1.132-report.md`, read whole. Took: the seven classes at
  `:247-254`, the `evidence` rule at `:250` and `:264-266`, which is the
  finding I re-instantiated; the shorthand-citation hazard at `:46-49`, which
  is what made me search for `ProbeLJ174A..F` before deleting anything; the
  `ProbeRudComp` case at `:101` and `:50-52`, which is section 4.4; the
  "derive, never transcribe" precedent at `:281-286`; and the `archive/probes/`
  conflict at `:200-216`, which the owner has now ruled on.
- `archive/README.md`, read whole. `:16-29` is the owner's ruling of
  2026-08-13, and `:23-24` decided the 31 deletions. `:45-51` (not required to
  be green), `:53-58` (frozen) and `:88-93` (licensing) govern the 155 new
  files.
- `archive/probes/README.md:1-56` as `[LJ-1.132]` left it. Took its exception
  test, "an archived report cites the probe file at a LINE NUMBER", which is
  the test I measured and then widened by two forms.
- `agents/reports/lj-1.130-report.md:118-129`, the report corpus that protects
  a probe, and the frozen-record ruling that decided which 27 citations to
  rewrite and which several hundred to leave.
- `dev/LESSONS.md` **D-1**, via `rules.py --for rewrite`, plus its 31 probe
  citations read in place at `:1012` and `:2944-3597`.
- `agents/reports/lj-1.118-report.md:1-110` against
  `src/ProbeLJ1118A.agda:66-160`. This pair is section 1.
- `agents/reports/archive/lj-1.39-report.md:128`,
  `agents/reports/archive/lj-1.31-report.md:121`,
  `agents/reports/archive/lj-1.74-report.md:209`,
  `agents/reports/archive/lj-1.54-report.md:43`. The four counterexamples.
- `dev/ARCHIVE.md:1-40`. **It indexes retired MODULES and its columns do not
  fit a probe file.** `[LJ-1.132]` recorded the same for `archive/kits/` and
  `archive/tooling/`, neither of which has a row. **I added no row**, and the
  per-directory `README.md` is the record, following that precedent.

## 12. LITERATURE

**Nothing in the literature governs a probe directory.**

## 13. STATE OF THE WORKING TREE

**Nothing committed. Nothing pushed.** Nothing staged; I verified the index is
empty after both gate tests.

Mine, modified: `scripts/check-probes.py`, `archive/README.md`,
`archive/probes/README.md`, `dev/LESSONS.md`, `dev/ledger.toml`,
`dev/memos/L3.30-rud-route.md`, `dev/memos/L3.32-below-lim-design.md`.
Mine, new: 155 files under `archive/probes/` and this report.
Mine, deleted: 31 files under `src/`, none of them tracked.

**Not mine.** `dev/PLAN.md`, `dev/build-manifest.toml`,
`src/L/Condensation.lagda.md` and `src/ProbeLJ1134A.agda` changed during my
run or before it. **I touched none of them.**

---

# LJ-1.133, second pass: the owner ruled on the 83

Status: **DONE.** `src/` holds 14 probes, all FRESH. Every other probe is
archived or deleted. Nothing committed. Nothing pushed.

## 14. THE RULING, APPLIED

The owner ruled that the NAMED class is archived, not left. **The reasoning is
the one section 1 pointed at:** the test cannot separate NAMED from EVIDENCE,
because the prose detector was fitted to its own counterexamples and its
recall is unknown. **When a test cannot separate two classes reliably, take
the recoverable side.**

### Counts

| | Before this pass | After |
|---|---:|---:|
| Probes in `src/` | 98, 3,348 KB | **14, 124 KB** |
| `archive/probes/` | 160 files | **244 files**, 8,556 KB |

**Moved: 84.** 83 NAMED plus 1 EVIDENCE, which had aged out of the freshness
window between the two passes and carried a line citation.

### The whole task, end to end

| Verdict | Files | Outcome |
|---|---:|---|
| **FRESH** | 14 | In `src/`, untouched |
| **EVIDENCE** | 156 | `archive/probes/` |
| **NAMED** | 83 | `archive/probes/`, by the ruling |
| **ORPHAN** | 31 | Deleted |

14 + 156 + 83 + 31 = 284. **`src/` went from 284 probes and 9,300 KB to 14 and
124 KB: 95 percent of the files and 99 percent of the bytes are gone from the
untracked directory.**

The generated index in `archive/probes/README.md` records the strength of each
file's claim, which is why I kept the two verdicts distinct after they became
one destination: **27 binding rule, 107 line citation, 110 named.**

## 15. `src/ProbeLJ1134A.agda`: classified by the rule, and the rule kept it

**Verdict: FRESH.** "modified 0.2h ago, inside the 6h freshness window".

**It is still in `src/` and I did not move it.** The coordinator's note says it
is finished, GREEN and reported, which under any other clause would make it
EVIDENCE or NAMED. **Freshness runs first and takes nobody's word**, and that
is deliberate: `dev/LESSONS.md` records two agents killed on 2026-08-05 by a
probe pulled out from under them, and a rule that accepts "it is done" is a
rule with a human in its critical path.

**The cost of the rule being right here is zero.** The next `--archive` run
after about 19:39 today picks it up with no decision from anyone. **I am
reporting the rule beating the instruction rather than overriding it**, which
is the outcome the freshness window exists to produce.

## 16. CITATIONS, and the shorthand bug bit the REWRITE side

**Rewritten this pass: 1.** Total for the task: **28**.

**That single citation is the finding.** `dev/LESSONS.md:3330` reads
`src/ProbeDD25F41{A,B,C,D}.agda`. My first-pass rewriter used
`src/(Probe[A-Za-z0-9]*)\.agda`, **which does not match a brace form**, so all
four members moved and the citation would have been left dangling.

**This is the same recall bug, on the other side of the move.** In pass one it
made three files look like orphans; here it made one live citation invisible
to the rewriter. **A plain stem search fails in BOTH directions**, and I have
recorded that in `archive/probes/README.md` for the next mover. The rewriter
now handles three forms: plain, brace `{A,B,C}` and range `A..F`, and it
rewrites a family only when **every** member has moved.

**MEASURED: exactly one `src/Probe*` reference remains in any live `dev/`
document**, and it did not dangle because of me:

> `dev/LESSONS.md:1642` `` `src/ProbeD10.agda` (untracked) ``

**That file does not exist and did not exist when I started.** MEASURED: it is
absent from `src/`, absent from `archive/probes/`, and absent from the
283-probe index I built before touching anything. It is not in my delete list.
**A pre-existing dangling pointer, reported and not repaired**, because
nothing can make it resolve. It is the exact failure this task exists to
prevent, left visible as its own evidence.

**Reports and briefs keep every old path**, per `[LJ-1.130]`.

## 17. VERIFICATION

| Check | Result |
|---|---|
| `check-probes.py --check` | **exit 0**, 1,479 tracked files |
| `--staged`, `src/ProbeLJ1133Retest.agda` staged with `git add -f` | **exit 1, REFUSED.** Unstaged and deleted after |
| `--staged`, `archive/probes/ProbeLJ130B.agda` and `ProbeDD25F41C.agda` | **exit 0, accepted** |
| `grep` for `src/Probe*` in live `dev/` documents | **1 hit, pre-existing, section 16** |
| `lint-prose.py --check` | **exit 0** |
| `check-tree.py --check` | exit 0, 87 masters |
| `check-rule-ids.py` | exit 0, 141 lessons, 66 decisions |
| `check-dev-docs.py` | exit 0, 6 subchecks |
| `ledger.py --check` | exit 0, standing 28,617 unchanged |
| `reuse lint` | **exit 0, 1,546 / 1,546** |

The two gate rows are the ones that matter: **the exemption still refuses
`src/` and still accepts `archive/probes/`.** The index was empty before and
after both tests.

**I did not run `make check`. I did not run Agda.**

## 18. TREE STATE

**The orchestrator committed my first pass during this one**, as
`8f55b4b [LJ-1.133][LJ-1.134]`. That is why the tracked count moved from 1,320
to 1,479 and why 160 archived probes are now tracked. **I did not commit it and
I did not push.**

Mine, uncommitted: `scripts/check-probes.py`, `archive/probes/README.md` and
`dev/LESSONS.md` modified; **84 new files under `archive/probes/`**; this
report.

**Not mine:** `dev/PLAN.md`, `agents/reports/lj-1.135-report.md`. I touched
neither.

## 19. WHAT IS STILL OPEN

- **`AGENTS.md:136-138` is still false.** "Nobody commits one" no longer holds.
  My proposed replacement is in section 6 and waits on the owner. DD19.
- **`dev/LESSONS.md:1642` points at a file that does not exist.** Section 16.
  It needs an owner or an orchestrator decision: drop the citation, or mark it
  as lost. **I did not edit a live rule's provenance line on my own reading.**
- **14 FRESH probes remain in `src/`.** They clear themselves on the next
  `--archive` run once each leaves the 6-hour window. No decision needed.

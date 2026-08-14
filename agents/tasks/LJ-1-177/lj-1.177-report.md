# LJ-1.177 report: the term was cured two dispatches ago, and the tree is red under a sibling

tier: opus (version `override`). Written incrementally (C-22). Every negative
is marked **MEASURED** or **INFERRED**.

**STATUS: STOP. TWO INDEPENDENT STOPS, EITHER ONE SUFFICIENT.** No master was
edited. Nothing was committed and nothing was pushed. I did not run
`make check`.

## 0. LEAD

**THE WING'S AGGREGATE BEFORE AND AFTER CANNOT BE MEASURED TODAY, and I say
that first because the brief asks for it first.**

| what the brief asked | what I found |
|---|---|
| the wing's aggregate BEFORE | **NOT MEASURABLE.** The run aborted; section 2 |
| the wing's aggregate AFTER | **NO CURE EXISTS TO MEASURE.** Section 1 |
| run counts | **0 kept runs.** The one attempt returned an Agda error, not a time |
| outside the band? | **NO DELTA EXISTS.** Not inside the band and not outside it |

**STOP ONE: THE BRIEF'S TERM IS ALREADY CURED.** `[LJ-1.155]` named the term,
and **`[LJ-1.158]` cured it on 2026-08-13 in commit `99498e3`**, titled 「The
wing goes 2.06x to 1.60x, and half the gap closes」. All three `*Agree` masters
carry the record at HEAD `a01ef58`. **MEASURED by reading them, and by a
telescope census. Section 1.**

**STOP TWO: ALL FOUR MASTERS ARE DIRTY AND THE TREE IS RED.** A sibling,
`[LJ-1.176]`, is editing `src/L/Condensation.lagda.md` and all three `*Agree`
masters right now. **`src/L/Condensation.lagda.md:6275` fails to typecheck.**
A second Agda process ran beside mine. **The brief's own instruction fires:
report the dirty target and stop. Section 2.**

**WHAT I DELIVER INSTEAD, and it is a measurement rather than an apology.** A
static census of every module telescope in the wing's four masters, which needs
no Agda and is therefore unaffected by the red tree. **It confirms the cure is
complete, and it prices a CEILING on the next candidate from `[LJ-1.155]`'s own
phase profile: about 5.2 s, which is NOT double figures.** Sections 3 and 5.

### 0.1 THE BRIEF WAS REVISED WHILE I WORKED, and I answer the NEW one

**MEASURED.** At the head of my task `agents/tasks/LJ-1-177/LJ-1.177.md` was
untracked. The orchestrator committed it as `142637c`, then edited it again in
the working tree: **23 insertions and 19 deletions, `git diff` at 08:33.**

**The change is the framing, not the work.** The first version led with 「a debt
of 40 to 49 seconds and DD27 rules that only a CURE can retire it」. The
current version leads with DD24 as the owner ruled it on **2026-08-14**:
**the bar was fixed when the AC trophy landed, every GCH module uses that one
number, and INTERMEDIATE DEBT IS ALLOWED because only the whole GCH side is
judged at the end.**

**So nothing here is urgent because of a running total, and I removed that
urgency from my own recommendations.** The RETURN now asks for 「the wing's gap
to the bar」 rather than 「the debt」. **Section 5 answers the new question with
the same arithmetic, because the gap and the debt are one quantity under two
names.** **I did not edit the brief. The diff is the orchestrator's.**

## 1. STOP ONE: THE TERM IS ALREADY CURED. MEASURED

**The brief says 「Find that term, cure it」. The term is
`DeadCode.DeadCodeReachable`, driven by the module telescope, and the cure is to
state the fact block as ONE record parameter.**

**MEASURED, by reading the three masters at HEAD `a01ef58`:**

| master | the record | line | fields | kept in the telescope |
|---|---|---:|---:|---|
| `src/L/Condensation/UpperAgree.lagda.md` | `record UFacts` | **:91** | 35 | `sucK`, at `:202-203` |
| `src/L/Condensation/LowerAgree.lagda.md` | `record LFacts` | **:94** | 37 | none |
| `src/L/Condensation/TwelveAgree.lagda.md` | `record TFacts` | **:128** | 59 | `sucK`, at `:323-324` |

**Each master states the cure in its own comment, with the measurement.**
`UpperAgree.lagda.md:77-90` reads 「THE FRAME'S FACT BLOCK, as ONE record rather
than 36 telescope hypotheses」 and cites `[LJ-1.158]` at 「`DeadCode` 2,652 ms to
25 ms」. `LowerAgree.lagda.md:76-93` and `TwelveAgree.lagda.md:114-127` carry
the same comment with their own figures.

**And the history says the same.** `git log --oneline -- <the three masters>`
returns `99498e3 [LJ-1.158] The wing goes 2.06x to 1.60x, and half the gap
closes`, one commit below the two `[LJ-1.173]` commits.

### 1.1 The census proves the telescopes are gone. MEASURED, no Agda needed

`agents/tasks/LJ-1-177/census_telescopes.py` reads a master, finds every
`module <Name> ... where` header by parenthesis depth, and counts the top-level
hypothesis groups. **It excludes `module X = Y`, a module APPLICATION, which
declares no telescope.**

| master | module headers | header lines | explicit hypotheses | widest header |
|---|---:|---:|---:|---|
| `TwelveAgree` | 3 | 10 | **5** | `AbstractFrame`, `:323`, **4** |
| `LowerAgree` | 3 | 10 | **7** | `LowerAgree`, `:217`, **3** |
| `UpperAgree` | 3 | 14 | **9** | `UpperAgree`, `:202`, **4** |

**`[LJ-1.158]` measured these same three headers at 60, 37 and 36 hypotheses
before its edit** (`agents/tasks/LJ-1-158/lj-1.158-report.md:100-106`). **They
are now 4, 3 and 4. The term is spent.**

### 1.2 What the cure already returned, from the primary sources

**I quote the measuring reports rather than re-deriving the figures, and I name
which report measured which.**

| | seconds | lines | s/line | ratio | source |
|---|---:|---:|---:|---:|---|
| before `[LJ-1.158]` | 219.14 | 11,635 | 0.0188 | **2.06x** | `agents/tasks/LJ-1-158/lj-1.158-report.md:243-252` |
| after `[LJ-1.158]` | 172.17 | 11,743 | 0.0147 | **1.60x** | same |
| after `[LJ-1.173]` stage zero | 164.60 | 11,825 | 0.0139 | **1.52x** | `agents/tasks/LJ-1-173/lj-1.173-report.md:1543-1552` |

**`[LJ-1.158]` deducted the machine from its own figure and I keep its
deduction: the cure is worth 42.72 s, not 46.97, because the nine untouched
wing masters moved 4.25 s on their own** (`:266-276`).

## 2. STOP TWO: THE TREE IS DIRTY AND RED, under `[LJ-1.176]`

**The brief orders this check first and orders a stop on a dirty target. I ran
it first, and it was clean. It went dirty while I measured.**

### 2.1 The tree at the head of the task. MEASURED, clean

```
 M agents/tasks/LJ-1-176/LJ-1.176.md
 M dev/PLAN.md
?? agents/tasks/LJ-1-177/
?? agents/tasks/LJ-1-178/
```

**No `src/` file was modified. I started the wing measurement on that tree.**

### 2.2 The tree four minutes later. MEASURED, dirty in all four masters

Raw: `agents/tasks/LJ-1-177/runs/collision-evidence.txt`, captured 08:25:06.

```
 M src/L/Condensation.lagda.md
 M src/L/Condensation/LowerAgree.lagda.md
 M src/L/Condensation/TwelveAgree.lagda.md
 M src/L/Condensation/UpperAgree.lagda.md
```

**`git diff --stat` at that moment: 97 insertions and 36 deletions in
`L/Condensation`, and 3 insertions in each of my three targets.**

### 2.3 What the sibling is doing, MEASURED from its diff

**The edit is `[LJ-1.173]`'s stage two, the fourth component on `codesK`.**
Each of my three targets gains one import and two field extensions:

```
+open import Cubical.HITs.PropositionalTruncation using ( ∥_∥₁ )
```
```
               × ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
+                 × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
```

**`[LJ-1.173]:1143` names this as 「a fourth component on `codesK`」 and
`:1012` prices the stage it serves.** So the orchestrator's warning was
correct in substance and wrong in the task number: **the sibling is
`[LJ-1.176]`, not `[LJ-1.178]`.** `agents/tasks/LJ-1-176/ProbeLJ1176B.agda`
appeared at 08:25 and `agents/tasks/LJ-1-176/LJ-1.176.md` was already modified
at the head of my task. **`[LJ-1.178]` builds `levelIn` and `cover`
(`agents/tasks/LJ-1-178/LJ-1.178.md:1`) and its report is an empty skeleton.**

### 2.4 THE TREE DOES NOT TYPECHECK. MEASURED

**My own measurement run caught it.** Raw:
`agents/tasks/LJ-1-177/runs/wing-before.txt`.

```
agda failed on .../src/L/Condensation.lagda.md; timing is meaningless:
/Users/alsg/Agentic/Bedrock/src/L/Condensation.lagda.md:6275.12-37: error: [UnequalTerms]
Σ ⟨ fst b ∈ fst (lookup K γ) ⟩
(λ _ → ∥ Σ-syntax ℕ (λ n₁ → fst ar ≡ (# n₁)) ∥₁)
!=< fst (fst b ∈ fst (lookup K γ)) of type Type (ℓ-suc ℓ)
```

**The sibling has widened the record field and has not yet widened every
consumer.** That is an ordinary mid-edit state and I do not report it as a
defect. **I report it because it makes every wing figure impossible: the tool's
own words are 「timing is meaningless」.**

### 2.5 TWO AGDA PROCESSES RAN AT ONCE, and I stopped mine

**MEASURED at 08:25:06, `ps -eo pid,etime,rss,command`:**

| pid | elapsed | rss | command |
|---:|---:|---:|---|
| 95469 | 01:03 | 6.4 GB | `agda src/L/Condensation.lagda.md` (**mine**, under `check-ratio.py`) |
| 95557 | 00:51 | 5.2 GB | `agda -v0 src/L/Condensation.lagda.md` (**the sibling's**) |

**`pgrep -x agda` returned 2. The 1-minute load average went from 2.50 at the
start of my run to 5.92.**

**I STOPPED MY OWN RUN rather than the sibling's**, because the sibling was
mid-build and a heap wall caused by my contention would have been my fault
(C-12). **I used the harness task stop. I did not use `git checkout`,
`git stash`, `git reset` or `git clean` at any point, and I killed no process
that was not mine.**

**MY RUN IS THE ONE THAT STARTED FIRST** (elapsed 01:03 against 00:51), so the
contention was not caused by me starting beside a live Agda. **`check-ratio.py`
fails closed beside another Agda process and it did not refuse, which confirms
the machine was quiet when I started.**

### 2.6 What this costs the measurement, stated exactly

- **The BEFORE figure is VOID.** It ran against a tree that changed under it,
  beside a second Agda process, and it ended in a type error rather than a time.
  **I report zero kept runs and I quote no number from it.**
- **The AFTER figure cannot exist.** There is no cure of mine to measure.
- **A later measurement would not compare to `[LJ-1.158]`'s or
  `[LJ-1.173]`'s either**, because `[LJ-1.176]` changes both the wing's lines
  and its seconds. **The wing is in motion and the debt cannot be re-measured
  until it settles.**

## 3. THE TERM THAT REMAINS, and its ceiling is priced from an existing profile

**`src/L/Condensation.lagda.md` is the wing's remaining cost: 113.57 s of the
wing's 164.60 s, or 69 percent** (`[LJ-1.173]:1546`). **`[LJ-1.158]:320-324`
named its own row telescopes as the widest unmeasured term and did not run the
probe.** I ran the census instead, because it needs no Agda.

### 3.1 The census. MEASURED

| | count |
|---|---:|
| module headers with a telescope | **99** |
| header lines | **1,094** |
| explicit hypotheses | **588** |
| headers with 10 or more hypotheses | **23**, holding 335 hypotheses over 833 lines |
| the widest, `PropAgree` at `:3282` | **25** hypotheses over 61 lines |

**The widest telescope in `L/Condensation` is 25 hypotheses. `TwelveAgree`'s
was 60 before the cure.** So no single header in this master is as wide as the
one that returned the largest saving.

### 3.2 THE CEILING, and it is the useful number. MEASURED as a bound

**`[LJ-1.155]` profiled this master cold with `--profile=internal` and measured
`DeadCode` at 5,297 ms of 121,115, which is 4.4 percent**
(`agents/tasks/LJ-1-155/lj-1.155-report.md:127`). **The telescope-to-record
cure collapses `DeadCode` by 99.1 percent and no more, measured three times at
factors of 105, 106 and 138.**

**So the cure's `DeadCode` lever at `L/Condensation` is capped at about
5.2 s, and the record's own fixed cost is subtracted from that.**
`[LJ-1.158]:130-134` measured the fixed cost at 790 ms for 37 fields and
1,860 ms for 59. **At 99 headers the fixed cost is paid 99 times.**

**MEASURED CONCLUSION: the telescope cure at `L/Condensation` cannot move
double figures on its `DeadCode` term, and it may cost more than it returns.**
**The brief's own bar is 「a cure worth funding here moves double figures of
seconds」. This candidate does not clear it on the lever that is measured.**
**That is the FOUND BUT DEAR verdict, and it is reached from an existing
profile rather than from a new run.**

**What is NOT capped, and it is UNMEASURED.** `[LJ-1.155]:134-139` computed
that about **21,268 ms** of this master's type-checking is billed outside every
definition, and `DeadCode` is only 5,297 ms of it. **The other 16 s is module
telescope elaboration and module-application INSTANTIATION.** The `*Agree`
probes also cut `Typing` by 36 percent and `Coverage` to zero, and
`[LJ-1.155]:300-304` refused to price either. **Whether a record reaches that
16 s is UNMEASURED, and it is the widest unmeasured term I can name (DD8).**

## 4. SHARED OR WING-LOCAL, for every candidate

**This is the column DD27 turns on, so I give it for all five and not only for
the one I would take.**

| candidate | site | SHARED or WING-LOCAL | status |
|---|---|---|---|
| the `*Agree` telescope-to-record cure | the three masters | **WING-LOCAL** | **SPENT.** `[LJ-1.158]`, 42.72 s |
| `L/Condensation`'s own 99 module headers | `src/L/Condensation.lagda.md` | **WING-LOCAL** | **`DeadCode` lever capped at about 5.2 s.** Section 3.2 |
| the 16 s billed outside definitions and outside `DeadCode` | same | **WING-LOCAL** | **UNMEASURED.** The widest term left |
| interface production | same | **WING-LOCAL** | **REFUTED twice, MEASURED.** 828 interface bytes per line against the tree's 1,229 mean |
| a seal on shared machinery, `[LJ-1.147]`'s class | `src/L/Coding/Graph.lagda.md` and its cone | **SHARED** | **REFUTED as a route, MEASURED.** It made every master faster and the ratio worse |

**WHY THE WING-LOCAL COLUMN IS SOUND HERE. MEASURED by `[LJ-1.155]`:6 with the
tool's own cone function**, not by reasoning. `src/L/Condensation.lagda.md` and
the three `*Agree` masters are **NOT** in the AC baseline cone of
`src/Landmarks.lagda.md`. **So a cure on any of them cannot move the
denominator of DD24's bar, and `[LJ-1.147]`'s sting cannot fire.**

## 5. THE DEBT, RE-MEASURED, and the range IS the instrument

**I cannot measure the wing today, so I re-derive the debt from the two most
recent measured figures and show what separates them.**

Bar `0.010514` s per line, which is `0.009143` at the 1.15x tolerance.
**Debt = wing seconds minus bar times wing lines.**

| source | seconds | lines | on-bar seconds | **debt** | ratio |
|---|---:|---:|---:|---:|---:|
| `[LJ-1.158]` after | 172.17 | 11,743 | 123.47 | **48.70 s** | 1.60x |
| `[LJ-1.173]` stage zero | 164.60 | 11,825 | 124.33 | **40.27 s** | 1.52x |

**THE BRIEF READS THESE AS A RANGE, 「40 to 49 seconds」. MEASURED: they are ONE
WING MEASURED TWICE, and the 7.57 s between them is 4.5 percent, well inside
the instrument's ±12.8 percent band.** `[LJ-1.173]:1554-1557` already says
this in its own words and declines to report its 1.52x as a correction to
1.60x. **So the honest statement is that the debt is about 44 s and the
instrument cannot say whether it is 40 or 49.**

**AND THAT SETS THE BAR FOR ANY CURE.** A cure smaller than about 21 s (12.8
percent of 164.60) cannot be separated from the noise by ONE pair of runs.
**Section 3.2's 5.2 s ceiling is a quarter of that.**

**The brief's DD27 arithmetic checks out. MEASURED:** the bar minus the
baseline is `0.010514 - 0.009143 = 0.001371` s per line, and 500 lines written
at the baseline repay `0.69 s`, which is 1.6 percent of a 44 s debt. **New work
cannot retire this debt and the brief is right about that.**

## 6. DD4

**The brief asks whether my cure has a generic form. I built no cure, so the
question is answered on the candidate instead.**

**`[LJ-1.158]:9` already gave the DD4 answer for this cure family and it is
NO for the code and YES for the law.** It counted the tower-specific names in
the three records: `numeralL` 16, 16 and 28 times, plus `prʟ`, `envSetAt`,
`envOverAt`, `tmValAt`, `subValAt`, `consAtL`. **`S` is `hPropStructure 𝒮ʟ`, so
every field names the L tower and the J tower could share none of them.**

**What transfers whole is the SHAPE**: state a frame's fact block as ONE record
parameter, and keep any field whose type names a transparent construction in
the telescope. **That is tower-free and it is now measured at four sites: three
by `[LJ-1.158]` and one by `[LJ-1.155]`.**

**`[LJ-1.159]:263`'s 8.4 factor does not apply here and I say so rather than
borrow it.** It measured generic against fixed at a NEIGHBOURING site. **P-l
forbids transferring a measured cure by analogy, and this report has no site of
its own to re-measure it at.**

**A DD4 note on my own deliverable.** `census_telescopes.py` takes a master
path and reads any Agda master. **It is not L-specific and it would census a
J-side frame unchanged.**

## 7. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| **the `*Agree` masters still carry the second term** | **MEASURED FALSE.** Three records at `:91`, `:94`, `:128`; the census reads 4, 3 and 4 hypotheses against 36, 37 and 60 |
| **my three targets were clean when I started** | **MEASURED TRUE**, and MEASURED FALSE four minutes later |
| **the sibling is `[LJ-1.178]`** | **MEASURED FALSE.** It is `[LJ-1.176]`; `[LJ-1.178]` builds `levelIn` and `cover` |
| **the tree typechecks** | **MEASURED FALSE.** `src/L/Condensation.lagda.md:6275`, `[UnequalTerms]` |
| **one Agda process ran** | **MEASURED FALSE.** Two, PIDs 95469 and 95557, both on the same master |
| **the wing's BEFORE aggregate** | **NOT MEASURED. Zero kept runs.** The attempt returned an Agda error |
| **the wing's AFTER aggregate** | **DOES NOT EXIST.** No cure was built |
| **my cure's effect is inside the band** | **NOT CLAIMED.** There is no cure and therefore no delta |
| **the `L/Condensation` telescope cure moves double figures** | **MEASURED FALSE on its `DeadCode` lever**, which is capped at about 5.2 s by `[LJ-1.155]`'s own profile |
| the other 16 s outside definitions is reachable | **UNMEASURED.** The widest term left (DD8) |
| **`40 to 49 s` is a range** | **MEASURED FALSE.** It is one wing measured twice, 4.5 percent apart, inside the ±12.8 percent band |
| a dominant DEFINITION exists in this family | **MEASURED FALSE by `[LJ-1.155]`**, largest 3.04 percent; **NOT re-measured by me** |
| I edited a master, committed, pushed, or ran `make check` | **MEASURED FALSE**, none of the four |
| I ran `git checkout`, `stash`, `reset --hard` or `clean` | **MEASURED FALSE**, none of the four |
| I raised the heap cap | **MEASURED FALSE.** `GHCRTS="-A64m -I0 -M8g"`, unchanged |

**HOW DEEP I WENT ON THE FIRST ROW, because the brief asks.** I read all three
masters WHOLE, I read the record declarations and their comments, I read the
commit that landed them, and I ran a static census that parses the module
headers by parenthesis depth. **I did NOT re-profile them with Agda, because
the tree does not typecheck.** So 「the term is cured」 is MEASURED from the
source text and the history, and NOT from a phase profile taken today.

## 8. CHECKERS

| checker | result |
|---|---|
| `scripts/lint-agda.py --check` | **exit 0** |
| `scripts/lint-prose.py --check` | **exit 0** |
| `scripts/check-probes.py` | **clean**, 1,811 tracked files |
| `agda` | **1 invocation**, aborted by me at 08:25; ONE process, cap never raised |
| `make check` | **NOT RUN.** The brief reserves it |

## 9. LITERATURE (DD18)

**Nothing in the literature governs elaboration cost.** The terms named here
are properties of Agda 2.8.0's dead-code pass and its conversion checker.

## 10. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-155/lj-1.155-report.md`, read WHOLE.** **TOOK:** the
  term at `:23-26`, `DeadCode.DeadCodeReachable` at 39.7 percent of the three
  masters, which is the term this task was sent to cure; `:127`, `DeadCode` at
  **4.4 percent** of `L/Condensation`, which is section 3.2's CEILING;
  `:134-139`, the **21,268 ms** billed outside every definition, which is the
  unmeasured 16 s; `:397-433`, the AC baseline cone computed with the tool's
  own function, which is section 4's WING-LOCAL column; `:300-304`, its refusal
  to price the `Coverage` and `Typing` savings, which I keep unpriced.
- **`agents/tasks/LJ-1-158/lj-1.158-report.md`, read WHOLE.** **TOOK:** the
  landed cure at `:100-106` and `:171-177`, the three records and their field
  counts, which section 1 verifies against the masters themselves; `:243-252`,
  the wing before and after; `:266-276`, the 42.72 s deduction, which I keep
  rather than the headline 46.97; `:320-330`, its naming of `L/Condensation`'s
  own row telescopes as the widest unmeasured term, which is section 3;
  `:130-134`, the record's own fixed cost growing with the field count, which
  is why 99 headers is a cost and not only a saving; its DD4 section, which is
  section 6.
- **`agents/tasks/LJ-1-173/lj-1.173-report.md`, PARTS FIVE onward.** **TOOK:**
  `:1543-1552`, the wing at 164.60 s over 11,825 lines, which is section 5's
  second row; `:1554-1557`, that 1.52x and 1.60x are one figure measured twice
  inside the band, which is section 5's central finding; `:1516-1530`, the
  correction that its own +6 s was INSIDE the band, which is the discipline
  this report applies to the 40-to-49 range; `:1143`, the fourth component on
  `codesK`, which identifies the sibling's edit in section 2.3.
- `agents/tasks/LJ-1-147/lj-1.147-report.md`, via `[LJ-1.155]:399-402`. **TOOK:**
  that a SHARED cure made the ratio worse, which is section 4's last row. **I
  did not re-read it whole, because no candidate here is shared.**
- `agents/tasks/LJ-1-159/lj-1.159-report.md:263` and `:50`, the 8.4 factor.
  **TOOK:** the figure, and **REFUSED** to apply it, because P-l forbids
  transferring a measured cure by analogy and I have no site to re-measure it
  at. Section 6.
- `agents/tasks/LJ-1-176/LJ-1.176.md:1-30` and
  `agents/tasks/LJ-1-178/LJ-1.178.md:1-40`. **TOOK:** the identity of the
  sibling, which corrects the brief's coordination note.
- **`archive/dev/TASKS-archived.md`: NOT USED, and I say so rather than pad
  this section.** The brief offers it for the retired route's condensation
  chapter. **This task built nothing, so there is no shape to take from it.**
- `dev/LESSONS.md`, at each entry. **P-t**, an average hides the term, which is
  why section 3.1 counts headers rather than dividing seconds by lines. **P-q**,
  lines removed do not buy seconds; **nothing was deleted.** **P-l**, twice:
  section 6 refuses the 8.4 factor, and section 3.2 marks the 16 s UNMEASURED
  rather than scaling the `*Agree` result onto it. **C-42**, a refutation
  measures the site it names; section 3.2's ceiling is stated for
  `L/Condensation` only. **C-12**, one process at the cap; section 2.5.
  **C-22**, the incremental deliverable; this file was created before the first
  measurement. **D-1**, the abort criterion fixed in advance, which the brief
  supplied and section 0 answers.
- `scripts/check-ratio.py:99-101`, the `±12.8` percent band and its provenance.
  **TOOK:** the band, which is section 5's test on the 40-to-49 range.

## 11. THE PROBES AND THE FILES

Two files, tracked, under `agents/tasks/LJ-1-177/`. **No probe went anywhere
near `src/`.**

| file | what it is |
|---|---|
| `census_telescopes.py` | the static telescope census; needs no Agda, so the red tree does not block it |
| `runs/wing-before.txt` | the aborted wing run, kept BECAUSE it holds the type error |
| `runs/collision-evidence.txt` | `git status`, `git diff --stat` and the two Agda PIDs at 08:25:06 |

## 12. WHAT I RECOMMEND, offered not taken

1. **Rule the brief's premise spent.** The `*Agree` second term is cured and
   `[LJ-1.158]` already collected its 42.72 s.
2. **Let `[LJ-1.176]` finish and land, then re-measure the wing once.** No
   figure taken before that compares to any figure taken after it.
3. **Do not fund the `L/Condensation` telescope cure on its `DeadCode` lever.**
   It is capped at about 5.2 s against a band of about 21 s.
4. **The one candidate worth a probe is the 16 s billed outside definitions and
   outside `DeadCode`**, which is module-application instantiation. **P-w is
   the law that names it and nobody has measured it at this master.**
5. **Consider whether the debt should be re-priced rather than retired.**
   Section 5 measures that the instrument cannot tell 40 s from 49 s. **A cure
   is asked to move a quantity the instrument reads with a ±21 s uncertainty.**

# [LJ-1.577] report: the V = L residue, read out of Devlin

STATUS: DONE. Written incrementally (C-22).

The probe is `agents/tasks/LJ-1-577/Probe577.agda`. It carries no ` ```agda `
fence, counts 0 in-fence lines, and the ratio bar cannot fire on it.

## WHERE 5.5 USES THE AMBIENT READING

The D-10, done before any Agda. The proof of Devlin II 5.5 is at
`dev/literature/devlin-II5.md:152-158`. One row per step, in the order the
digest prints them.

| # | Step | `file:line` | Uses "κ is a cardinal" | Reading the step needs |
|---|---|---|---|---|
| 1 | pick α < κ with x ⊆ L_α | `dev/literature/devlin-II5.md:152` | no | none |
| 2 | take a limit λ with x ∈ L_λ | `dev/literature/devlin-II5.md:153` | no | none |
| 3 | by 5.4 take M ≺ L_λ with L_α ∪ {x} ⊆ M and \|M\| = \|L_α\| | `dev/literature/devlin-II5.md:154` | no | none |
| 4 | collapse M to L_γ by condensation | `dev/literature/devlin-II5.md:154` | no | none |
| 5 | L_α ∪ {x} transitive, part (ii) fixes it, π(x) = x | `dev/literature/devlin-II5.md:155` | no | none |
| 6 | by 1.1(vii) \|L_α\| = \|α\|, \|L_γ\| = \|γ\|, so \|γ\| = \|M\| = \|α\| < κ, hence γ < κ | `dev/literature/devlin-II5.md:156` | **YES, and it is the only step that does** | see below |
| 7 | x ∈ L_γ ⊆ L_κ | `dev/literature/devlin-II5.md:157` | no | none |

The digest's own summary of the step list agrees and adds nothing:
`dev/literature/devlin-II5.md:282` reads "\|γ\| = \|α\| < κ with κ a cardinal
implies γ < κ", and it names the whole strength of the step as "parts (i) and
(ii) of condensation only, plus the level-size equation and initial-ordinal
arithmetic" (`dev/literature/devlin-II5.md:283-284`).

**ROW 6 IS THE ONLY ROW, AND THE PRINTED PAGE DOES NOT CHOOSE ITS READING.**
5.5 opens `Assume V = L` (`dev/literature/devlin-II5.md:147`). Under that
assumption the three size witnesses row 6 consumes are all elements of L: the
level-size bijection of 1.1(vii) at α and at γ, and 5.4's counting of the hull
(`dev/literature/devlin-II5.md:140-142`). So an injection of κ into α is an
element of L exactly when it exists at all, and "κ is a cardinal" is ambient
and internal at once. `[LJ-1.569]` said this and this reading confirms it.

**WHAT ROW 6 NEEDS IS NOT A READING OF THE HYPOTHESIS. IT IS A READING OF THE
INJECTION.** Row 6 refutes ONE injection: the composite of 5.4's counting, the
collapse and 1.1(vii). Devlin never asks where that injection lives, because
`Assume V = L` puts it in L for free.

### The same step in the tree

| # | Tree site | `file:line` |
|---|---|---|
| 6 | `β∈κ`, the trichotomy on β against κ | `src/L/BoundedSubset.lagda.md:1594` |
| 6a | first spend, the β ≡ κ leg | `src/L/BoundedSubset.lagda.md:1597` |
| 6b | second spend, the κ ∈ β leg | `src/L/BoundedSubset.lagda.md:1601` |
| 6c | the injection both legs refute | `src/L/BoundedSubset.lagda.md:1578-1582` |
| 6d | its lower leg, the stage-cardinality bound at β | `src/L/BoundedSubset.lagda.md:1581` |
| 6e | its upper leg `πX↪α`, the inverse collapse composed with a code selection | `src/L/BoundedSubset.lagda.md:1574-1576` |
| 6f | the code selection | `src/L/BoundedSubset.lagda.md:1518` |
| 6g | the inverse collapse | `src/L/BoundedSubset.lagda.md:1517` |

`grep -n cardκ src/L/BoundedSubset.lagda.md` gives three lines: the binder at
`:1386` and the two spends at `:1597` and `:1601`. Both spends are
`cardκ α α∈κ`. `[LJ-1.523]` measured this and this task re-measured it.

## PORT DEFECT OR REAL OBSTRUCTION

**IT IS A PORT DEFECT, AND THE DEFECT IS NOT IN THE HYPOTHESIS. IT IS IN THE
CONSTRUCTION.** The mathematician's reading was that the classical proof of 5.5
runs inside L and needs κ to be a cardinal of L only, and the literature step
above says that reading is right about the PROOF: exactly one of 5.5's seven
steps reads "κ is a cardinal", and under `Assume V = L` the three size
witnesses that step consumes are all elements of L, so the refutation may be
taken at L's own injections. But the tree does not inherit that for free,
because the tree builds the injection AMBIENTLY. `β↪α`
(`src/L/BoundedSubset.lagda.md:1578`) is the inverse collapse after a code
selection, composed with the stage-cardinality bound, and it carries no
`InjCode`. So re-ascribing `cardκ` alone does not take the demand off: it
converts it, from a statement about cardinals into a statement about ONE
injection, and `internal-plus-one-code` and `residue-gives-569` measure that
the converted demand is no cheaper. **The cure is a construction and not a
re-reading: give `β↪α` a code.** That is local, it needs no V = L, and both of
its legs are built from L-data. What this task rules out is the cheap route the
brief hoped for, and what it rules IN is a construction task with a written
interface (`gap-is-a-code`, `agents/tasks/LJ-1-577/Probe577.agda:368`).

**AND THE OBSTRUCTION IS NOT MATHEMATICAL AT THIS SITE.** Nothing measured here
says the conclusion is false under the internal reading. What is measured is
that the tree cannot take the step today.

## THE SWEEP (C-42)

A refutation measures one site. This is the count before any cure is priced.

`grep -rn "IsCardinal\b" src/ | grep -v IsCardinalL` gives SIX lines and they
fall in three groups:

| Group | `file:line` | What it is |
|---|---|---|
| the definition | `src/L/BoundedSubset.lagda.md:1046-1047` | `IsCardinal`, the ambient reading |
| the one telescope that SPENDS it | `src/L/BoundedSubset.lagda.md:1386` | `BoundedSubsetAt`'s `cardκ`, spent at `:1597` and `:1601` |
| two telescopes that PASS it | `src/L/StageBound.lagda.md:65` and `:94` | handed straight to `Devlin55.BoundedSubsetAt` at `:74` and `:114`, never applied |

`src/L/StageBound.lagda.md` also imports it at `:16`. **So the shape has ONE
origin and ONE consumer pair. It has not spread.** A cure at `β∈κ` closes every
site in the tree, and `src/L/StageBound.lagda.md`'s two telescopes follow the
head they copy.

The `InjCode` side of the sweep, re-measured here and not carried over: `src/`
has exactly two producers, `src/L/Absorption.lagda.md:614` and
`src/L/CodedShift.lagda.md:40`, and both deliver the single shape
`InjCode F (sucʟ γ) γ`.

## WHAT TYPECHECKED

One Agda process at a time, caliber `-A64m -I0 -M8g` from the pane, never set
by this task. **No heap wall.**

| Run | What | Result |
|---|---|---|
| `runs/w3-1.out` | W3 alone: SECTION 1 | GREEN, 3.01 s, 732610560 B peak RSS |
| `runs/s2-1.out` | + SECTION 2, the internal telescope | GREEN, 9.04 s, 1455439872 B |
| `runs/s3-1.out` | + SECTION 3, first attempt | EXIT 42, unsolved metas at `isL-trans` and `mem-ord` |
| `runs/s3-2.out` | after the first fix | EXIT 42, the `mem-ord` meta remained |
| `runs/s3-3.out` | both implicits given | GREEN, 9.00 s, 1602322432 B |
| `runs/s5-1.out` | + the step named as terms | GREEN, 9.05 s, 1482801152 B |
| `runs/s5-2.out` | + `injection-hypothesis-free` | **KILLED BY THE AGENT after 3 min 58 s** (started 02:28:19Z, killed 02:32:17Z), EXIT 143, no heap exhaustion |
| `runs/s5-3.out` | that term removed | GREEN, 8.50 s, 1408352256 B |
| `runs/final-1.out` | + SECTIONS 4 and 5 | GREEN, 8.98 s, 1460797440 B |
| `runs/final-2.out` | after the rename to `internal-plus-one-code` | GREEN, 9.28 s, 1460781056 B |
| `runs/final-3.out` | the file as it stands | GREEN, 8.65 s, 1460781056 B |

**W3 ANSWERED IN 3.01 SECONDS AND THE BRIEF ESTIMATED UNDER 2 MINUTES.** The
answer is positive: the module FORMS with the internal reading, and the
re-ascription is not a swap, because `IsCardinal` is stated at the ambient
carrier (`src/L/BoundedSubset.lagda.md:1046`) and `IsCardinalL` at the
L-carrier (`src/L/Cardinal.lagda.md:230`). The ordinal must be lifted first.
That is `CardHypAmbient`, `CardHypInternal` and `ReAscribedHead`
(`agents/tasks/LJ-1-577/Probe577.agda:61`, `:69`, `:76`).

**ONE MEASUREMENT WAS ATTEMPTED AND FAILED, AND IT IS REPORTED AND NOT
DROPPED.** `injection-hypothesis-free` would have shown by `refl` that
`β↪α` does not read the cardinality hypothesis. It ran 3 min 58 s without
converging and the agent killed it (`runs/s5-2.out`). `refl` across a module
application must unfold the injection, and the injection pulls the whole hull.
The four cheap `refl`s that DID land (`hull-is-hypothesis-free`,
`collapse-is-hypothesis-free`, `levelIn-is-hypothesis-free`,
`cover-is-hypothesis-free`, `agents/tasks/LJ-1-577/Probe577.agda:142-162`)
cost 9 seconds together, because `HS.M` and `HS.C.πX` carry no occurrence of
the hypothesis at all. **What stands in its place is the grep**: the binder at
`src/L/BoundedSubset.lagda.md:1386` and exactly two spends, at `:1597` and
`:1601`.

### The probe

370 lines, of which 162 are comment and 48 blank. The brief estimated about 220
lines with about 50 for the obligation. **The obligation's TYPE cost 14 lines
(`agents/tasks/LJ-1-577/Probe577.agda:260-273`) and the obligation itself is
not in the file.** The overrun is in SECTION 2: restating the telescope without
the ambient hypothesis took 90 lines, and that was not in the estimate because
nobody had measured that `UnionKit` and `HullStage` take no cardinality
parameter.

### The verdict on the obligation

NO-GO, and `agents/tasks/LJ-1-577/review-of-bounded-subset-internal.md` states
it with the step named. The obligation term is not in the probe.
`internal-plus-one-code` (`agents/tasks/LJ-1-577/Probe577.agda:279`) is the
nearest term that exists and it carries the residue to the left of its arrow.

## WHAT THE NEXT BRIEF NEEDS FROM THIS ONE

- **The route's ambient demand now has an address, not just a name.**
  `[LJ-1.569]` named it "an L-cardinal is a cardinal". This task narrows it to
  ONE injection at ONE step: `β↪α` at `src/L/BoundedSubset.lagda.md:1578`,
  refuted at `:1597` and `:1601`.
- **The interface for the cure is written and green.** `gap-is-a-code`
  (`agents/tasks/LJ-1-577/Probe577.agda:368`) says exactly what a producer must
  deliver: `⟪ fst a ⟫ ↪ ⟪ fst b ⟫ → InjL a b` at the one pair.
- **The telescope can be restated without the ambient hypothesis.** SECTION 2
  is that restatement and it is green. A cure does not have to touch the hull,
  the collapse, the count or `levelIn`/`cover`.
- **The shape has not spread.** The sweep counts one origin, one consumer pair,
  two pass-throughs.
- **What resisted:** naming `β↪α` outside its module. `Devlin55.BoundedSubsetAt`
  carries `cardκ` in its telescope, so every name inside it, including the
  injection that does not use it, is formally a function of it. That is why
  SECTION 2 rebuilds the hull from the top-level modules and why
  `injection-hypothesis-free` did not converge.
- **What I could not close:** whether `β↪α` is codeable. This task did not
  attempt it and the brief did not order it. It is the next question.

## LITERATURE USED

- `dev/literature/devlin-II5.md` **READ**, and it carries the D-10. At
  `dev/literature/devlin-II5.md:147`: "> 5.5 Lemma. Assume V = L. Let κ be a
  cardinal. If x is a bounded subset of". The proof is at `:152-157` and the
  step table above is one row per clause of it. The digest's own summary of the
  step is at `:282`: "|γ| = |α| < κ with κ a cardinal implies γ < κ
  (`dev2.txt:1372-1384`)."
- `dev/literature/devlin-errata.md` **READ, AND IT RECORDS NOTHING ABOUT 5.5.**
  At `dev/literature/devlin-errata.md:40`: "review mentioned in a previous
  section. The problems are chiefly confined to". The sentence continues
  "section 9 of Chapter I and section 1 of Chapter VI". The one Chapter II
  section, at `:125`: "### 2.3 Errors in Chapter II (WS pp. 62-63)", lists
  amenability at Devlin p. 45, the uniformity claim at p. 65 and a claim at
  p. 66. **None of the three touches II.5, and no errata item touches 5.5.** So
  nothing in the errata changes the step table.
- `dev/literature/truncation-and-selection.md` **READ IN PART**, at
  `dev/literature/truncation-and-selection.md:22`: "Lemma II.5.3, the definable
  hull. The proof verifies Tarski's criterion by". This is the pattern the
  tree's `CodeSelect` (`src/L/BoundedSubset.lagda.md:1518`) follows, and it is
  why the upper leg of `β↪α` is a definable selection rather than a choice.
  That supports the report's claim that the injection is built from L-data. It
  settles nothing about coding, so it is cited and no more.
- `dev/literature/geology.md` **NOT READ, DECLINED.** Set-theoretic geology.
  Nothing in this task touches ground models or mantles.
- `dev/literature/level-formula-slot-roles.md` **NOT READ, DECLINED.** The
  arity of the level-hood formula. This task changes no formula and reads no
  slot.
- `dev/literature/digest.md` **NOT READ, DECLINED.** The rud route's orthodox
  form. This task is inside the Def route's own chapter.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md` **READ**, at
  `archive/dev/LJ-dispatch-index.md:170`: "| LJ-1.94 | Build the ambient
  Hartogs cardinal and end at the consumer | CARDK SUPPLIED, GREEN | 1058
  lines, 27 s, no choice. But IsCardinal is stated locally, and the next
  blocker is Devlin55's sq |". This is the brief's premise 5 and it is the
  record that `[LJ-1.94]` supplied `cardκ` from the AMBIENT Hartogs cardinal at
  its own site. The brief forbade moving the site and this task did not.
- `archive/dev/JOURNAL.md` **NOT READ, DECLINED.** A journal is history, and
  the question here is what the tree states today.
- `archive/dev/JOURNAL-archived.md` **NOT READ, DECLINED.** Same reason.
- `archive/dev/DD-archived.md` **NOT READ, DECLINED.** The `DD` series is set
  aside in that form; no `DD` row was needed to read a step of 5.5.
- `archive/dev/DECISIONS-archived.md` **NOT READ, DECLINED.** No `D<n>`
  decision bears on the cardinality reading at this step.

## SCOPE TOUCHED

- `agents/tasks/LJ-1-577/Probe577.agda` (new)
- `agents/tasks/LJ-1-577/lj-1.577-report.md` (new)
- `agents/tasks/LJ-1-577/review-of-bounded-subset-internal.md` (new)
- `agents/tasks/LJ-1-577/runs/` (new: `run.sh` and eleven `.out` files)

Nothing in `src/`. Nothing postulated. No hole. Not committed, not pushed.

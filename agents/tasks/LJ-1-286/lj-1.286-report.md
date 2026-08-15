# [LJ-1.286] report: take A6's discharge of A7's `absorbs`

tier: opus (in-harness-subagent-mode). One Agda slot, one process at a time,
`GHCRTS="-A64m -I0 -M8g"`, cap never raised. No commit, no push. Written
incrementally (C-22). Every negative is MEASURED or INFERRED, in those words.
ASD-STE100 applies.

## 0. LEAD

**IT LANDS GREEN.** `src/L/GCH.lagda.md` now SUPPLIES A6's absorption and no
longer hypothesizes it. **ONE hypothesis remains: `sq : SqShape`, at
`src/L/GCH.lagda.md:80`.**

| figure | before | after |
|---|---:|---:|
| unsupplied hypotheses of `GCHStatement` | 2 | **1** |
| in-fence non-blank lines | 63 | **73** |
| cold elapsed, mean of 3, matched load | 1.527 s | **1.553 s** |
| whole-file rate against the 0.010514 bar | 2.31x | **2.02x** |
| `ledger.py --reuse` share, as PRINTED today | 41.1% | **41.1%, unchanged** |
| the same share once COMMITTED | 41.1% | **39.1% of 19,532 lines** |

**The reuse report cannot see this change yet, and that is a property of the
tool.** `import_graph` reads `head_text`, which is `git show HEAD:<path>`
(`scripts/ledger.py:378-388`). My edit is uncommitted, so `--reuse` prints the
old figure. Section 7 gives the verbatim output and the committed figure, both.

**A CONSUMER BREAKS, and it is outside my write territory.**
`agents/tasks/LJ-1-280/ReRun.agda:61` applies `proof sq absorbs κ cκ nfin` and
is now RED. Section 6 names it, prices the fix at one token, and does not make
it.

**`sq` is NOT dischargeable, and I found a sharper reason than the brief
gave.** Section 5.

## 1. MACHINE AND PROCESS DISCIPLINE

ONE agda process at a time, `GHCRTS="-A64m -I0 -M8g"` on every run, cap never
raised. One warm-up discarded per arm. The `.agdai` deleted before every kept
run, at `_build/2.8.0/agda/src/L/GCH.agdai`.

**The cold caliber is the project's own**, at `scripts/check-timing.py:203-256`:
clear THIS master's interface and leave the dependencies warm.

**THE MACHINE WAS NOT QUIET.** A sibling task held the other Agda slot for the
whole run. The 1-minute load sat between 4.35 and 7.52; the 5-minute and
15-minute averages sat between 15.9 and 28.9, because a heavy job ran before I
started. Every absolute figure below carries its 1-minute load.

**MEASURED FALSE: a wall.** The longest single invocation is 10.01 s
(`agents/tasks/LJ-1-284/ReRun.agda`). Nothing came near 30 minutes.
**MEASURED FALSE: a heap exhaustion.** No kill, no interrupt.

## 2. THE ABORT CRITERION, FIXED BEFORE THE RUN (D-1)

- **IT LANDS GREEN.** **FIRES.** Sections 4 to 7. STOP.
- **THE DISCHARGE NEEDS A `subst` OR A WRAPPER.** **Does not fire.** The supply
  is `absorbsL = absorbs`, an identity body against a written type. No `subst`,
  no eta-expansion, no adapter. Section 3.
- **A CONSUMER OF GCH BREAKS.** **FIRES.** `agents/tasks/LJ-1-280/ReRun.agda:61`.
  Section 6. The orchestrator's grep was right about `src/`, and the break is
  outside it (C-44).
- **`sq` TURNS OUT DISCHARGEABLE.** **Does not fire.** Section 5. I wrote no
  term of `SqShape`.
- **A WALL.** **Does not fire.** Section 1.

## 3. THE DISCHARGE, RE-DERIVED BEFORE THE EDIT

The brief told me to re-derive premise 1 rather than take
`[LJ-1.284]`'s word. I did that FIRST, against the UNEDITED masters.

`agents/tasks/LJ-1-286/ProbeLJ1286A.agda:30-31`:

```
mine : AbsorbsShape
mine = absorbs
```

`AbsorbsShape` comes from the then-unedited `src/L/GCH.lagda.md`, and `absorbs`
from `src/L/Absorption.lagda.md`. **exit 0, 2.64 s, load 5.74.** I later
corrected two stale line numbers in that file's closing comment and re-ran it,
exit 0 again; **the two lines above are unchanged since the first run.**

**MEASURED: the two types are one type.** The elaborator closed the identity
with no `subst`, no eta-expansion and no wrapper. The membership forms `∈ˢ` and
`∈` agree because `𝒮ᵥ`'s membership field IS `_∈_`. `[LJ-1.284]` section 5
gives the same reading at `src/V/Hierarchy.lagda.md:83`, and my probe is
independent evidence of the same fact.

## 4. WHAT CHANGED IN src/L/GCH.lagda.md

Four edits, 18 insertions and 7 deletions, in one file.

| line | what |
|---:|---|
| `:17` | ADDED `open import L.Absorption {ℓ} lem using ( absorbs )`, after `L.Cardinal` |
| `:37-40` | the A7 header comment, rewritten: A6's shape is supplied here, A5's is the one hypothesis |
| `:57-63` | ADDED `absorbsL : AbsorbsShape` and its body `absorbs`, with the C-38 note |
| `:80-81` | DELETED `→ (absorbs : AbsorbsShape)`; `(sq : SqShape)` now leads straight to `(κ : S)` |

**THE PARAMETER LINE WAS AT `:69`, AS THE BRIEF SAID.** VERIFIED before the
edit: `src/L/GCH.lagda.md:69` read `  → (absorbs : AbsorbsShape)` in the
63-line file. It is gone.

**WHY THERE IS A NAMED SUPPLY AND NOT ONLY AN IMPORT.** `GCHStatement` is a
statement TYPE and has no proof term, so the deleted parameter had ZERO uses in
the body. Nothing needed threading. That leaves two ways to write the change,
and they are not equally honest:

1. Delete the parameter and import nothing. The statement gets stronger and the
   master records NO evidence that anything can satisfy the deleted hypothesis.
   **This is precisely C-38's failure mode read backwards:** a hypothesis is
   discharged when something SUPPLIES it, never when it is deleted.
2. Delete the parameter and name the inhabitant. `absorbsL : AbsorbsShape` is
   the supply, and `make check` re-proves it at every run, for good.

**I took 2.** It also makes the import NECESSARY: with route 1 the new import
binds a name the file never uses, and `lint-agda.py`'s check C would flag it
(`scripts/lint-agda.py:313-356`). So route 1 cannot even keep the import that
DD4's report reads.

**`absorbsL` is an alias, not a wrapper.** Its body is the bare name `absorbs`.
The abort criterion asks about a `subst` or an adapter between two DIFFERENT
types; there is none, and section 3 measured that.

## 5. THE REMAINING HYPOTHESES

**ONE.**

**`sq : SqShape`, the parameter at `src/L/GCH.lagda.md:80`**, whose type is at
`src/L/GCH.lagda.md:44-47`:

```
SqShape =
  (α : S) → IsOrd (fst α) → (⟨ fst α ∈ˢ ω ⟩ → Empty.⊥)
          → ⟪ fst α ⟫ × ⟪ fst α ⟫ ↪ ⟪ fst α ⟫
```

**MEASURED: nothing in `src/` inhabits `SqShape`.** By grep over `src/`, the
name occurs only in `src/L/GCH.lagda.md` at `:40`, `:44`, `:45` and `:80`.

### 5.1 The premise is TRUE, and its evidence needed correcting

The brief said `src/L/InjChain.lagda.md` supplies only the base
`squareω : sq ω` and not the uniform law. **That is true**
(`src/L/InjChain.lagda.md:184-185`). **It is also incomplete, and the missing
piece matters to whoever prices the `sq` discharge next.**

**A uniform square law IS delivered**, at
`src/L/Ordinal/SquareLaw.lagda.md:960-961`:

```
via-col-square : (α : S) → Init α → sq α
```

**It does not supply `SqShape`, and the gap is exact.** `Init`
(`src/L/Ordinal/SquareLaw.lagda.md:692-699`) is a four-part conjunction, and
`SqShape` gives only the first part:

| `Init α` component | `SqShape` gives it? |
|---|---|
| `IsOrd α` | YES, the second argument |
| `⟨ ω ∈ˢ α ⟩`, so ω is a STRICT member | **NO** |
| successor-closed, so α is a LIMIT | **NO** |
| α's index injects into no infinite member's square | **NO** |

**Two of the three missing parts are FALSE on `SqShape`'s own domain, not
merely unproved.** `SqShape` quantifies over every ordinal outside ω. That
includes ω itself, where `⟨ ω ∈ˢ ω ⟩` is refuted by `∈-irrefl`; the tree
already records this at `src/L/InjChain.lagda.md:104`, which is WHY row 5
rebuilt the base at ω from `InitialCore` instead of calling `via-col-square`.
It also includes every successor ordinal, such as ω+1, where successor-closure
fails.

**So `sq` is NOT dischargeable today, and the obstruction is not "the uniform
law is missing".** The uniform law exists. What is missing is a route from
`IsOrd α` plus `α ∉ ω` to a square law at the successor and non-initial
ordinals, which `via-col-square` cannot reach by construction.

**MEASURED: nothing in `src/` instantiates `Init` at any α.** By grep over
`src/`, `via-col-square` and `via-col-truncated` have NO consumer, and `Init`
appears outside its own chapter only in the comment at
`src/L/InjChain.lagda.md:104`. That is a C-35 observation about a delivered
block, not a claim about this task, and I did not act on it.

**I WROTE NO TERM OF `SqShape`.** The brief forbade the attempt. The
`ProbeLJ1286A.agda` comment at `:33-40` records the same refusal in the code,
with the `via-col-square` finding beside it.

## 6. THE RE-RUNS THAT PROVE THE LANDING (C-45, C-40)

**exit 0 of a master is not a supply.** The landing is proved by files that
IMPORT `L.GCH` and use what it exports.

### 6.1 The landing proof

`agents/tasks/LJ-1-286/ReRun.agda`, **exit 0, `--safe`, 2.45 s, load 4.35**,
green on the first attempt. Three parts, each answering a different question:

- **PART 1, THE PARAMETER IS GONE.** `apply` at `:86-90` writes
  `proof sq κ cκ nfin`. **This is the test, not a reading of the source.** With
  the deleted parameter still in place, `κ : S` would land in the `absorbs`
  slot and the file would be red. It is the same shape that
  `agents/tasks/LJ-1-280/ReRun.agda:57-61` carried, with one argument removed.
- **PART 2, THE SUPPLY IS EXPORTED.** `supplied : AbsorbsShape = absorbsL` at
  `:96-97`.
- **PART 3, THE SUPPLY IS NOT VACUOUS (C-38).** At `:107-115` the supplied law
  is APPLIED at a real L-ordinal:
  `atω = absorbsL ωʟ ω-ord (∈-irrefl ω) (λ k → #∈ω k)`, and both halves of the
  resulting injection come out, `fst atω : ⟪ sucV ω ⟫ → ⟪ ω ⟫` and its
  injectivity. **A hypothesis nothing can satisfy would stop here.**

The file also carries the C-38 site guard from
`agents/tasks/LJ-1-280/ReRun.agda:38-44`, so nothing that file proved is lost
while it is red.

### 6.2 C-40: every consumer of L.GCH, re-run

**MEASURED by grep over `src/`, `agents/` and `scripts/`: four consumers, and
the orchestrator's grep of `src/` was correct.**

| consumer | exit | elapsed | load |
|---|---|---:|---:|
| `agents/tasks/LJ-1-286/ReRun.agda` (mine) | **0** | 2.45 s | 4.35 |
| `agents/tasks/LJ-1-286/ProbeLJ1286A.agda` (mine) | **0** | 1.60 s | 4.60 |
| `agents/tasks/LJ-1-286/ProbeLJ1286A.agda`, after a comment fix | **0** | 1.79 s | 5.41 |
| `agents/tasks/LJ-1-284/ReRun.agda` | **0** | 10.01 s | 5.08 |
| `agents/tasks/LJ-1-280/ReRun.agda` | **RED** | 2.46 s | 5.27 |
| `src/Everything.lagda.md:368` (the catalog line) | not run | | |

`agents/tasks/LJ-1-284/ReRun.agda` stays green because it imports only
`AbsorbsShape`, which this change keeps exported.

**I did NOT run `src/Everything.lagda.md`.** The brief forbids `make check` and
the orchestrator runs it. **MEASURED: nothing in `src/` imports `L.GCH` except
that catalog line**, so the tree-wide risk is the catalog build alone, and
`L.Absorption` is already wired at `:367`, before `L.GCH` at `:368`.

### 6.3 THE BREAK, NAMED

**`agents/tasks/LJ-1-280/ReRun.agda:61`**, the whole error:

```
agents/tasks/LJ-1-280/ReRun.agda:61.48-55: error: [UnequalTerms]
((γ : S) → IsOrd (fst γ) → (⟨ fst γ ∈ˢ ω ⟩ → Empty.⊥) →
 ((k : ℕ) → ⟨ (InfinitySet.# k) ∈ fst γ ⟩) →
 ⟪ sucV (fst γ) ⟫ ↪ ⟪ fst γ ⟫)
!=< (Σ (FOL.ZFStructure.ZFStructure.S 𝒮ᵥ) (λ x → x ∈ᶜ isL))
when checking that the expression absorbs has type S
```

That file's `apply` declares `(sq : SqShape) (absorbs : AbsorbsShape) (κ : S)`
at `:57-58` and applies `proof sq absorbs κ cκ nfin` at `:61`. **The statement
now expects the cardinal where `absorbs` sits.** The error is exactly the
intended change, observed from a consumer.

**THE FIX IS TWO DELETIONS AND I DID NOT MAKE THEM.** Delete
`(absorbs : AbsorbsShape)` from the telescope at `:58`, and delete the word
`absorbs` from the application at `:61`. **My write territory is
`src/L/GCH.lagda.md` and `agents/tasks/LJ-1-286/` only**, so that file is the
orchestrator's. **I have PROVED the fix works**: my own `ReRun.agda` PART 1 is
that file's `apply` with the argument removed, and it is green.

The stale comment at `agents/tasks/LJ-1-280/ReRun.agda:63-65` ("The two
hypotheses stay unsupplied") is now false and sits in the same file.

## 7. THE REUSE REPORT

### 7.1 Verbatim, AFTER the change

```
ledger [thresholds SUSPENDED]: AC closure 22,934 against the retired 20,000 cap, reported and NOT enforced; re-arm is LJ-2.1 measures the internalization double trophy and LJ-2.2 sets both DD5 benchmarks, then this goes false
  DD4 REUSE REPORT (evidence for a human, never a gate):
    AC closure       73 masters  17,197 lines
    GCH closure      48 masters   8,894 lines
    SHARED           43 masters   7,596 lines
    shared share of the union: 41.1% of 18,495 lines
    A high share won by fattening the shared core is the failure the no-gate
    ruling protects against. Read this beside LJ-2.3's reuse map, not instead of it.
```

**That is byte-identical to the output BEFORE my change.** I ran it at both
ends and diffed.

**WHY, and it is not a defect.** `import_graph` reads `head_text`, which is
`git show HEAD:<path>` and returns "" for a path not in HEAD
(`scripts/ledger.py:119-123`, `:378-388`). **The report measures the
REPOSITORY, never the working tree.** My edit is uncommitted, so the report
cannot see it. `[LJ-1.284]` section 9.1 met the same wall and handled it the
same way.

### 7.2 What it will print once committed

I recomputed with the tool's OWN functions, patching only `head_text` to read
the working tree, and using live line counts:

| state | AC closure | GCH closure | SHARED | union | share |
|---|---:|---:|---:|---:|---:|
| HEAD, as printed above | 73m / 17,197 | 48m / 8,894 | 43m / 7,596 | 18,495 | 41.1% |
| **live tree, once committed** | 73m / 17,197 | **51m / 9,967** | **44m / 7,632** | **19,532** | **39.1%** |

**The three masters that enter the GCH closure**, measured, not projected:

| master | lines | lands in |
|---|---:|---|
| `src/L/Absorption.lagda.md` | 525 | GCH only |
| `src/L/InjChain.lagda.md` | 502 | GCH only |
| `src/L/Axioms/Infinity.lagda.md` | 36 | **SHARED**, already in the AC closure |

**1,063 lines enter the GCH closure. 36 land in the intersection and 1,027 do
not.** `[LJ-1.284]`'s projection of 39.1% is VERIFIED. Its union figure of
19,522 is 10 lines short of my 19,532, and the 10 lines are `L.GCH`'s own
growth, which that task could not have known.

**MEASURED: the AC closure does not move.** 73 masters and 17,197 lines at both
ends, the identical set.

## 8. DD4: REUSE AGAINST RATIO

**MY AXIS IS AC-AGAINST-GCH (C-46), which is DD4's own**, fixed in code at
`scripts/ledger.py:50` and computed by `ledger.py --reuse`. I report no figure
on Devlin's Def-against-J axis here.

**THE ANSWER: this change RAISES reuse and LOWERS the ratio. They move in
OPPOSITE directions, and the printed number reports only the second.**

Reuse is what the two proofs actually share, and the report measures it in the
SHARED row. **That row goes UP: 43 masters and 7,596 lines become 44 masters
and 7,632 lines.** `src/L/Axioms/Infinity.lagda.md` was AC-only; it is now
shared. **Not one line leaves the shared set, and the AC closure is unchanged
at 17,197 lines.** By every quantity DD4's text names, the architecture
improved.

The share is a RATIO, and its denominator is the union. The GCH side was a
statement with two unsupplied hypotheses, so its closure was small; that small
denominator is what made 41.1% look good. **The old figure was high because the
GCH proof was missing, not because the two proofs shared well.** Supplying one
hypothesis pulls in 1,027 GCH-specific lines that the trophy always needed, the
denominator grows by 1,037, and the ratio falls to 39.1%.

**Could a reader six months from now tell the two apart from the number alone?
NO, and that is the finding.** The report prints four numbers: AC lines, GCH
lines, SHARED lines and the share. **A reader who reads only the share sees
41.1% fall to 39.1% and infers a regression.** A reader who reads the SHARED
row sees 7,596 rise to 7,632 and infers the opposite. Both readings come from
the same run of the same tool on the same day. **The share alone is not
sufficient to answer DD4's own question**, because the denominator moves for
reasons that have nothing to do with sharing.

**This is the first time the project has watched DD4's figure point the wrong
way, and the reason is structural rather than accidental.** The ratio will fall
again at every GCH-side landing, because GCH-specific mathematics is exactly
what the GCH trophy still owes and none of it is AC's. **A share defended by
refusing to land GCH content would be the failure the no-gate ruling was
written to prevent**, and `dev/ledger.toml:163-168` says so in the declaration
itself. The orchestrator's ruling to take the discharge is consistent with the
rule; I re-opened nothing, and I record the measured figure rather than his
projection, as instructed.

**One suggestion, and it is the orchestrator's call, not mine.** The SHARED row
is already printed. A reader is more likely to reach DD4's own question if the
report also prints the SHARED row's own movement, or if the share line names
its denominator as the union of two closures of unequal maturity. I did not
edit `scripts/ledger.py`; it is outside my territory.

## 9. EVERY PREMISE, VERIFIED OR REFUTED

1. **"`absorbs` supplies `AbsorbsShape` on the nose."** **VERIFIED**, and
   re-derived independently as the brief required.
   `agents/tasks/LJ-1-286/ProbeLJ1286A.agda:31-32`, exit 0, 2.64 s. No `subst`,
   no wrapper.
2. **"The parameter to delete is at `src/L/GCH.lagda.md:69`."** **VERIFIED.**
   The line read `  → (absorbs : AbsorbsShape)` in the 63-line file. The file
   had not moved.
3. **"`sq : SqShape` is NOT dischargeable."** **VERIFIED as a conclusion, and
   its stated EVIDENCE was incomplete.** Section 5.1. `src/L/InjChain.lagda.md`
   does supply only the base at ω, but a uniform law exists at
   `src/L/Ordinal/SquareLaw.lagda.md:960`, restricted by `Init`, and two of
   `Init`'s three extra parts are FALSE on `SqShape`'s domain. The conclusion
   holds; the reason is different and sharper.
4. **"`src/L/GCH.lagda.md` is the declared `reuse.gch_root`."** **VERIFIED**,
   `dev/ledger.toml:192`. Changing its imports changes the figure, and section
   7 measures by how much.
5. **"`src/L/Absorption.lagda.md` is 525 lines and is wired after `L.Cardinal`
   and before `L.GCH`."** **VERIFIED.** 525 lines by `ledger.py`;
   `src/Everything.lagda.md:367` sits between `L.Cardinal` at `:366` and
   `L.GCH` at `:368`. **The catalog needs no new line.**
6. **"Nothing in `src/` imports `L.GCH` today."** **VERIFIED for `src/`**, and
   **REFUTED for the tree**: two probes import it, and one of them breaks
   (section 6.3). The brief asked me to check rather than trust, and the check
   paid.

## 10. EVERY NEGATIVE, CLASSIFIED

- **MEASURED FALSE. The master fails to typecheck.** exit 0, `--safe`, one
  warm-up plus six kept cold runs.
- **MEASURED FALSE. The discharge needs a `subst`, an eta-expansion or a
  wrapper.** Section 3.
- **MEASURED FALSE. The change slows the master.** Section 11. The whole-file
  rate IMPROVED, from 2.31x to 2.02x the bar, on one machine state.
- **MEASURED FALSE. A wall or a heap exhaustion.** Longest run 10.01 s.
- **MEASURED FALSE. `SqShape` is inhabited anywhere in `src/`.** Grep over
  `src/`: four occurrences, all in `src/L/GCH.lagda.md`, none an inhabitant.
- **MEASURED FALSE. `Init` is instantiated anywhere in `src/`.** Grep over
  `src/`: one comment at `src/L/InjChain.lagda.md:104` and nothing else.
- **MEASURED FALSE. `ledger.py --reuse` moved.** Byte-identical at both ends,
  because it reads HEAD. Section 7.1.
- **MEASURED FALSE. The AC closure changed.** 73 masters and 17,197 lines at
  both ends, the identical set.
- **MEASURED TRUE. A consumer breaks.** `agents/tasks/LJ-1-280/ReRun.agda:61`,
  with the error quoted. Section 6.3.
- **MEASURED FALSE. I touched `src/Everything.lagda.md`, `dev/ledger.toml`,
  `dev/PLAN.md`, `src/L/Choice/Name.lagda.md`, `agents/tasks/LJ-1-283/` or
  `agents/tasks/LJ-1-287/`.** `git status --short` shows my writes as exactly
  `src/L/GCH.lagda.md` (modified) and `agents/tasks/LJ-1-286/` (new).
- **INFERRED. The 0.026 s cost of the edit is the L.Absorption interface plus
  the alias, and not the ten lines.** The two arms ran minutes apart at loads
  5.30 to 5.45, which is the closest match I could hold on a shared machine. I
  did not profile where the milliseconds went, so the attribution is a reading
  of the shape and not a measurement.
- **INFERRED. `src/Everything.lagda.md` still builds.** Every dependency of
  `L.Absorption` precedes it in the fence, by `[LJ-1.284]` section 7, and the
  one edited master is green with all four of its consumers checked. **I did
  not run the catalog**, so this is an inference. `make check` settles it.

## 11. TIMING AND SIZE (DD24, DD8)

**Line count, by `ledger.py`, the only admissible source: 63 to 73, plus 10.**

**Two arms, one machine state, minutes apart.** I restored the HEAD content to
the same path, measured it, and restored my version; the restore was verified
byte-identical by `diff`.

| arm | runs | mean | 1-min load |
|---|---|---:|---:|
| HEAD, 63 lines, no `L.Absorption` | 1.52, 1.52, 1.54 | **1.527 s** | 5.30 to 5.41 |
| edited, 73 lines | 1.58, 1.54, 1.54 | **1.553 s** | 5.45 |

**The whole edit costs 0.026 s.** That is 0.0026 s per added line, which is
0.25x the 0.010514 bar.

An earlier set of three kept runs on the edited file, taken at a higher and
less stable load (5.92 to 7.52), gave 1.66, 1.62, 1.49 for a mean of 1.59 s.
**I report the matched-load pair above as the price**, because a delta across
two machine states is an inference and not a measurement (P-l).

**The whole-file rate is 1.553 / 73 = 0.0213 s per line, which is 2.02x the
bar.** It IMPROVED: the same measurement on HEAD gives 1.527 / 63 = 0.0242,
which is 2.31x. **`[LJ-1.280]` already recorded why the whole-file rate is over
the bar and it is unchanged here:** a 26-line import header whose interfaces
cost about 1.60 s dominates a statement file of this size
(`agents/tasks/LJ-1-280/lj-1.280-report.md:24-27`). Ten lines at 0.0026 s per
line dilute that fixed cost, so the rate falls while the seconds rise. **The
overage is recorded plainly and not trimmed to a number (DD8).**

## 12. FOR THE ORCHESTRATOR

Three items, none of them mine to change.

1. **`agents/tasks/LJ-1-280/ReRun.agda` is RED.** Two deletions fix it
   (section 6.3), and my `ReRun.agda` PART 1 proves the fixed shape is green.
2. **`dev/ledger.toml:184` is now STALE.** It reads "`sq : SqShape` and
   `absorbs : AbsorbsShape` are Pi-parameters that nothing supplies
   (`src/L/GCH.lagda.md:66-76`)". After this change ONE parameter is
   unsupplied, and the cited range is now `:73-87`. The paragraph's conclusion
   still holds, and it holds more weakly: the closure still understates the GCH
   side, but by one hypothesis instead of two. **`gch_root_why` at
   `dev/ledger.toml:193` carries the same stale claim**, in a string that
   `--brief` can print. **I did not edit the file.**
3. **`via-col-square` has no consumer** (section 5.1). That is a C-35
   observation about delivered code, and it will matter to whoever prices the
   `sq` discharge.

## 13. ARCHIVE USED (DD18)

One line read named per file.

- **`agents/tasks/LJ-1-284/lj-1.284-report.md`, read WHOLE, FIRST.** TAKEN: the
  discharge, the DD4 arithmetic and the closure table. Line read `:259`,
  "| after `L.GCH` imports `L.Absorption` | 73m / 17,197 | 51m / 9,957 | 44m /
  7,632 | 19,522 | **39.1%** |". **I VERIFIED it rather than quoting it**, and
  measured 19,532 rather than 19,522; the difference is `L.GCH`'s own ten new
  lines.
- **`agents/tasks/LJ-1-284/ReRun.agda:92-93`, read.** TAKEN: the SHAPE of the
  one-line discharge, `absorbsShape = absorbs`. **I re-derived it in my own
  probe** rather than citing it, as the brief required.
- **`agents/tasks/LJ-1-280/lj-1.280-report.md`, read sections 0, 1 and 5.**
  TAKEN: the header-baseline reading that explains the whole-file rate, and the
  cold caliber. Line read `:43`, "| `Baseline.agda` (import header only), mean
  of 3 | 0 | cold | 1.60 | ~6 |". That figure is why section 11 does not treat
  2.02x as a content overage.
- **`agents/tasks/LJ-1-274/lj-1.274-report.md`, read for what the reuse report
  actually reads.** TAKEN: that the report needs a committed PATH and an import
  closure, never a proof term. The reading is confirmed in the live declaration
  at `dev/ledger.toml:174-177`, "It never reads a proof term, never reads a
  type and never calls Agda". **That is why section 7.1 expected the unchanged
  output instead of reporting a defect.**
- **`archive/dev/TASKS-archived.md:81`.** TAKEN, SHAPE ONLY:
  "L3.32-T46 | Cardinal chapter's counting side | DELIVERED". The retired route
  also ended these ordinal injections in a counting chapter, which is where the
  absorption is consumed. **WHAT WOULD NOT TRANSFER:** the route (Rud), its
  module layout, and every figure in that table. No price and no technique came
  from it.

## 14. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md`, read `:143-170` (the 5.5 to 5.8 chain),
`:375-395` (the twelve-row table and the DD4 verdict) and `:411-418` (the
II.1.1(vii) row).**

**WHICH ROW `absorbs` IS: ROW F**, "5.5 | condensation (i)(ii), |L_α| = |α|,
initial ordinals" (`:382`), reached through the counting half **II.1.1(vii)**,
which `:411-418` records as "BEARS, as the counting half of 5.5 and 5.6" and
calls "generic cardinal arithmetic over the level-size equation". Row F's tower
verdict is EITHER, so `absorbs` is tower-neutral and both towers get it.

**DOES DEVLIN TREAT IT AS A HYPOTHESIS OR A THEOREM? A THEOREM, and that is the
finding.** 5.6's proof at `:160` reads "By 5.5, 𝒫(κ) ⊆ L_{κ⁺} for all infinite
cardinals κ. So by 1.1(vii), ...". **1.1(vii) is INVOKED as an established
fact**, proved in chapter I and never restated as an assumption of the GCH
chain. The successor absorption is one step of that cardinal arithmetic.

**So A7's Pi-parameter was the anomaly, not the discharge.** Devlin's chain has
no hypothesis here, and `src/L/GCH.lagda.md` carried one only because A6 had
not landed. **This change makes the statement agree with the source it ports.**
The same argument does NOT extend to `sq`: `[LJ-1.284]` section 12 measured
that II.5 never writes either step explicitly, so the literature prices
neither, and only this project's own measurements are admissible for the `sq`
discharge.

**WHY NOT the other eleven rows.** Rows A, B, C3, C4, C5 and C6 are
elementarity, the collapse, Σ₀ absoluteness, the Σ₁ transfer and ordinal
bookkeeping; none consumes an injection between the small types of two
ordinals. Rows C1 and C2 are the level-hood certificate, which is the tower
engine and not cardinal arithmetic. Rows D and G are the definable well-order.
Row E is the hull counting `|ℒ_X| = max(|X|, ω)`, which is over the hull and
not over an ordinal successor.

## 15. WORKING TREE, AS THIS REPORT DESCRIBES IT

My writes, and nothing else:

- **`src/L/GCH.lagda.md`, MODIFIED.** One import at `:17`, one supply at
  `:57-63`, the parameter deleted at the old `:69`, two comments rewritten. 63
  to 73 lines.
- **`agents/tasks/LJ-1-286/`, NEW**: `LJ-1.286.md` (the pinned brief), this
  report, `ProbeLJ1286A.agda` (the re-derivation) and `ReRun.agda` (the landing
  proof).

Checkers run on what I wrote: `lint-agda.py --check`, `lint-prose.py --check`,
`weave-i18n.py --check` and `ledger.py --check` all exit 0. `check-probes.py`
is clean over 2,320 tracked files. **I did NOT touch `dev/ledger.toml`.**

No commit, no push, no `git checkout .`, no stash, no reset, no clean. No
`make check`; the orchestrator runs it.

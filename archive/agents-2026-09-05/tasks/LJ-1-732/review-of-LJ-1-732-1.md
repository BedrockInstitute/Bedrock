# LJ-1.732: adversarial review of LJ-1.732#1

## HEAD

head_slot: mathematician_adversarial
machine: shared
task: LJ-1.732
review_of: agents/tasks/LJ-1-732/lj-1.732-report.md (the newest *-report.md,
the second dispatch, written 07:33 local), with the acceptance arm
agents/tasks/LJ-1-732/runs/accept-2.out
verdict: overturned

## THE VERDICT IN ONE PARAGRAPH

The return's stop is honest and its measurements are real. I verified the
watchdog mechanism, the kill log, the timings and the RSS figures, and the
program's own two acceptance arms re-measured the wall independently
(`accept-1.out`, `accept-2.out`, conjunct 1 FAILED twice). The stop still
falls, on the return's own strongest sentence: "every proof of this
implication's vacuity must do it" is a universal claim the dispatch never
measured, and the one restructure shape that attacks it is the shape the
brief itself mandates. All five restructures keep the truncation elimination
at the concrete instance `(v ∷ u ∷ n 0 ∷ γ15)`. None moves it to a generic
carrier. W2 (DD4) binds exactly that move: write the mathematics once at the
generic carrier and instantiate it. A generic `step-killed` whose `PT.rec`
sits at a symbolic environment is a plausible under-5-second module by the
return's own floor measurements (Bisect7c elaborated the full signature in
3.44 s), and its instance call is a one-line application with syntactic
conversion. If it checks, the chain lands on THIS pane and the obligation
closes green with no owner ruling. I name that probe below and write no Agda
(A21). Overturned, with the probe named, because the price of a wrong
overturn is one dispatch and the price of a wrong uphold is a NO-GO closing
on a reading the return itself prices TRUE.

## QUESTION 1. DOES THE VERDICT LINE MATCH ITS OWN BODY?

The line says STOP ON THE CHECKING WINDOW and the body is a window story, so
the measured failure of LJ-1.375 and LJ-1.376 (a verdict line that contradicts
its own body) is absent here. Two mismatches inside the body remain.

1. The body's load-bearing universal is unmeasured. Section 1 states: "That
   is the one expensive act, and every proof of this implication's vacuity
   must do it". The evidence given covers only proofs that eliminate the
   antecedent truncation AT the instance: five restructures, all instance-side
   (`runs/Amb7a.agda` names `ApproxAt` and `MotiveEmpty` AT
   `(n 0 ∷ γ15)`; `runs/Amb7.agda` still writes the `PT.rec` inline at
   lines 33-41; Bisect7d shows the instance-side scaffolding alone exceeds
   the window). A proof whose `PT.rec` sits at a symbolic site is not covered
   by any measurement in the return. The universal is an extrapolation from
   five data points that share one hidden premise.

2. The single-killer window model is stronger than the record. The return
   says every Agda process on this pane lives inside one 20-second sweep gap,
   "effectively about 18.5 to 20 seconds". The program's own acceptance runs
   contradict the model's completeness: `accept-1.out` records Probe732
   rc -9 at 9.88 s (started 05:30:13) and `accept-2.out` records Amb7
   rc -9 at 11.53 s (started 07:34:43), yet the main watchdog log carries no
   kill between 05:30:07 and 07:04:57, and none between 07:34:38 and
   07:39:22. A second, worktree-rooted watchdog exists (pid 14720 was alive
   at review time, 10 h 49 m elapsed, per
   `_build/tools/agda-watchdog.pid` and `ps` in this worktree; its log's last
   kill is 01:28:51), and `run_agda` (`scripts/pod/facts.py:199`) cannot be
   the killer either: its deadline is `agda_deadline_s = 1800`
   (`dev/pod/heads.toml:273`), and a timeout yields rc None, not -9. So at
   least one killer of long Agda processes on this machine is unattributed in
   any log. That makes the pane WORSE than modeled, not better, so it does not
   rescue the obligation; but the return's "the body needs more than 19.9 s"
   is calibrated only against its own phase-cycled runs, and its first
   proposed cure (one pane under the swap cap settles this) assumes the
   watchdog is the only killer. State the census, then claim the cure.

The verdict word STOP is the brief's vacuity word ("STOP if the hull holds no
such codes"), and the body says the hull is NOT vacuous (`codes-exist` at
`Probe732.agda:120`). The line carries its own qualifier, so this is a
category reuse and not a contradiction. Noted, not decisive.

## QUESTION 2. IS EVERY LOAD-BEARING CLAIM BACKED BY A file:line THAT RESOLVES TODAY?

Verified and resolving. I opened each of these:

- The swap guard: `/Users/alsg/Agentic/Bedrock/scripts/ops/agda-watchdog.sh:28`
  is `SWAP_MAX_MB=$((8*1024))` and line 79 is `sleep 20`. The worktree's copy
  of this script is an older revision with no swap guard, so the return's
  "main checkout" qualifier is correct and load-bearing.
- The kill log: `/Users/alsg/Agentic/Bedrock/_build/tools/agda-watchdog.log`
  carries `swap 8742MB >= 8192MB` kills that match the return's run records
  exactly: p-10 (20.18 s, ended 23:28:54Z) against the 07:28:54 kill,
  `runs/amb7b-1.out` (20.58 s, ended 23:15:45Z) against 07:15:45,
  `runs/bisect7d.out` (16.60 s, ended 23:21:49Z) against 07:21:49. The swap
  readings sit at 8742 to 8773 MB at every sampled kill, which supports the
  "fires on stale allocation" reading.
- RSS: `runs/bisect7d.out` maximum resident set size 1707507712,
  `runs/amb7b-p-10.out` 1731690496, `runs/amb7-1.out` 1745076224. The
  "plateau 1.71 to 1.75 GB, well under the 2 g cap" claim holds.
- Floors: `runs/amb0-1.out` 3.19 s (the return says 3.18; a 0.01 s slip),
  `runs/amb7a-v3-1.out` 4.24 s, `runs/bisect7c.out` 3.44 s with the expected
  `UnsolvedInteractionMetas` at `Bisect7c.agda:47`.
- The chain: `runs/Amb7b.agda:32-39` builds the leaf locally (the return
  cites 36-37; the definition spans 32-39), `src/L/Condensation.lagda.md:2471-2477`
  carries `approxBndAt` in the quoted shape, `src/L/Coding/Model.lagda.md:160`
  is `appAt f x y = ∃̇∈ (var f) (prAtL zero (suc x) (suc y))`, and
  `src/L/Coding/Base.lagda.md:196` sits in `prAtL`'s pair-membership engine.
  `agents/tasks/LJ-1-673/Probe673.agda:93-95` is `BoundInStage`.
- The obligation text: `Probe732.agda:174-196` (definition at 174, top-level
  export at 196; the return cites 163-186, a loose span that includes the
  pins). The witness claim checks: `wZ = n 12` at `Probe732.agda:95`, the
  twelfth numeral.
- The gates: the checker output is pasted verbatim and rc 0.

Two failures.

1. `runs/amb7-1.out` is cited for "the `⟨_⟩`-bracket mismatch on
   `MotiveEmpty`". The file today holds a kill record (16.67 s, ended
   23:03:16Z) and no Agda diagnostic: the run script overwrites its `.out`,
   and a later kill replaced the evidence. The claim may be true; the cite
   does not resolve to its evidence.
2. `dev/pod/transitions/2026-08.jsonl` in this worktree carries zero lines
   for `"task": "LJ-1.732"`, as my brief anticipated. The main checkout's
   copy of the same path carries this task's lines: model `glm-5.3-flash`,
   effort blank, `heads_sha256` starting `291c2c2b`, eight lines from
   21:30:13Z to 23:40:13Z. I read them there and say so here.

Not load-bearing, and unverified by me: the green status of `Num`, `Amb1`,
`Amb3`, `Amb5`, `Amb6` rests on the first dispatch's report, which this
report overwrote. The corroboration I hold is indirect: the program's arm ran
`Amb7`, whose import cone contains all of them, and it ground for 11.53 s to
a SIGKILL rather than dying fast on an import error.

## QUESTION 3. IS THE PREDECESSOR'S ENUMERATION COMPLETE?

No. The five restructures (motive hoist, type-synonym module, lambda split,
signature/body bisect, phase-cycled launches) all keep the truncation
elimination at the concrete instance. The enumeration lacks the one
restructure its own brief mandates.

W2 says: write the mathematics once at a generic carrier and instantiate it,
so both proofs share the maximum code. The return answers W2 in its section 4
about statements and exports only, and never prices moving the ELIMINATION to
the generic carrier. The pieces were already in place:

- The falsity content is already generic. `runs/Amb7b.agda` refutes the
  antecedent with `empty-spec` from `V.Model`, a library lemma, wired through
  one `subst`. Nothing in the refutation is numeral-bound except that slot 2
  of the environment is the literal `n 0`, and the generic statement keeps
  that slot syntactic.
- The scaffolding is the measured cost, and the scaffolding is exactly what a
  generic module removes from the instance. Bisect7d measured the kill with
  the from-clause holed, so the cost is typing the `PT.rec` against the
  instance's carrier. Put the `PT.rec` in a module quantified over
  `γ : Vec S 15` and the pattern types against symbolic components; Bisect7c
  measured that signature-level elaboration at 3.44 s.
- The instance call is then an application, and conversion between the
  instance's antecedent type and the instantiated lemma domain is syntactic,
  not a re-normalization.

So the return's universal, "every proof of this implication's vacuity must do
it", is unmeasured against the one shape that denies it. I am the
mathematician family for this dispatch and write no `.agda` file (A21), so I
name the probe and stop.

**Named probe (A21): `agents/tasks/LJ-1-732/runs/Gen732.agda`.** Import
exactly what `runs/Amb7b.agda` imports, declare
`step-killed-gen : ∀ (u v : S) (γ : Vec S 15) → ⟨ u ∈ˢ n 12 ⟩ →
⟨ v ∈ˢ n 12 ⟩ → ¬ ⟨ (v ∷ u ∷ n 0 ∷ γ) P652.⊨ₚ App ⟩` with `AppC`,
`countAppC` and `App` as at `runs/Amb7b.agda:32-39`, prove it with the same
`PT.rec`, the same pattern `(pr , pr∈∅ , _)` and the same body
`Empty.rec* (subst ⟨_⟩ (empty-spec pr) pr∈∅)`, all with `γ` symbolic. Then
re-run `Amb7b` with `step-killed` replaced by the instance call
`step-killed-gen u v γ15 u∈ v∈`. Decision rule: if `Gen732` checks in about
5 s or less and the new `Amb7b` lands under the window, the wall was
shape-local; continue the chain (`Amb7` → `Amb4` → `Amb2` → `Probe732`) on
this pane, one process at a time. If `Gen732` itself walls, the return's
universal gains the measurement it lacked, and a renewed stop with that
record in hand should be upheld. Also record a full kill census first: every
rc -9 this task counts, including both acceptance arms', attributed by pid
against BOTH watchdog logs, so the next stop claim rests on a complete killer
model. The acceptance-arm kills at 9.88 s and 11.53 s have no log line today.

Two lesser gaps, priced small: the D-10 correction (the demand TRUE, the
witness `n 12`, the recorded direction backwards at the main checkout's
`agents/tasks/LJ-1-727/review-of-completeness-from-pack.md:105-121`) is
prose-level and machine-red until `Probe732` checks; the next brief should
say so beside the correction. And the kill census arithmetic in section 6 of
the return (18 kills across 12 `amb7-*.out` files) is the overwrite behavior
of `runs/run.sh`, which is why the bracket-error citation lost its evidence.

## WHAT THE NEXT BRIEF NEEDS

- The named probe above, at the wide caliber, one process at a time, with the
  decision rule stated.
- The kill census duty, both watchdog logs named.
- The estimate for `Gen732` plus the re-run of `Amb7b`: 80 to 150 lines, one
  best-effort number, basis: the delivered comparable `Bisect7c` at 3.44 s
  for signature-level elaboration and the green floor of 2.44 to 2.46 s
  re-measured by the arm itself in `accept-2.out`.
- No `src/` file, no ruling request, until `Gen732` has answered.

## RECORD FACTS

- This worktree's `dev/pod/transitions/2026-08.jsonl` ends before this
  instance and carries no `"task": "LJ-1.732"` line; per the brief I used the
  accept arm for the six facts and read the main checkout's copy of the
  transitions file for model, effort and heads, disclosed in question 2.
- The file `agents/tasks/LJ-1-732/review-LJ-1-732-1.md` (mtime 07:39) holds
  the text of this review's own brief at the wrong filename. It predates my
  first write, it is not in my scope, and I left it untouched.
- I wrote and touched no `.agda` file, including no probe and no `runs/`
  file (A21). My write scope is this file and nothing else.
- `make check` is not run: this review lands no `src/` file and commits
  nothing.

## ARCHIVE USED

- **`archive/dev/DD-archived.md` READ.** Line 35 carries DD25, the lens this
  review used; the quote at that line: "| DD25 | **A NEGATIVE RETURN IS
  ADVERSARIALLY REVIEWED AT MAXIMUM EFFORT, IMMEDIATELY, AND THE TWO ARE THEN
  READ TOGETHER. THE HEADS COME FROM THE SWITCH.**" The four questions sit in
  that row: "is the refusal correct on its own numbers; is the measurement
  sound; did the BRIEF cause the outcome; and is there a cure the return
  missed."
- **`archive/dev/ORCHESTRATION.md` DECLINED.** Not read: the dispatch process
  rules do not bear on a probe wall or a restructure enumeration.
- **`archive/dev/PLAN-archived.md` DECLINED.** Not read: the live status is
  the screen, which this review does not restate.
- **`archive/dev/measurements/README.md` DECLINED.** Not read: no archived
  measurement is cited by this review; every figure above was re-verified at
  its own live site.
- **`archive/dev/README.md` DECLINED.** Not read: the archive's own index
  answers no question this review asks.

## LITERATURE USED

- **`dev/literature/BIBLIOGRAPHY.md` DECLINED.** Not read: no source is
  quoted or surveyed here; the review judges elaborator measurements and an
  enumeration.
- **`dev/literature/devlin-errata.md` DECLINED.** Not read: no literature
  formula is under test; the formulas are the tree's own.
- **`dev/literature/primary-sources.md` DECLINED.** Not read: DD28's
  survey-first rule binds provability probes, and this dispatch reviews a
  return rather than opening one.
- **`dev/literature/level-formula-slot-roles.md` DECLINED.** Not read: the
  slot roles in play are carried by the code citations in question 2, which I
  opened directly.
- **`dev/literature/glossary-review-2026-08.md` DECLINED.** Not read: no
  glossary term is proposed here.

# LJ-1.745: step-killed, the instance call of the generic lemma

## HEAD

head_slot: coder
machine: shared
task: LJ-1.745
agda_tier: wide
pane caliber: GHCRTS=`-A64m -I0 -M2g`, set by the program; never touched here
verdict: **GO**, with one disclosed shape note: `step-killed` carries the
critic's hypothesis as its LEADING EXPLICIT ARGUMENT, not as a postulate.
`agents/tasks/LJ-1-745/Probe745.agda:64` typechecks rc 0 in 7.27 s (final
bytes, `runs/probe745-final.out`; first landing of the same shape at
10.56 s, `runs/probe745-run2.out`), under the 20 s window, and the
obligation name resolves through a replica of the meter's own derivation
(rc 0, 7.53 s).

## THE DELIVERABLE

`agents/tasks/LJ-1-745/Probe745.agda` exports one top-level name,
`step-killed` (`agents/tasks/LJ-1-745/Probe745.agda:64`). Its conclusion is
`agents/tasks/LJ-1-732/runs/Amb7b.agda:46` verbatim. Its body is the
instance call routed into the motive by the falsity eliminator
(`agents/tasks/LJ-1-745/Probe745.agda:76-77`):

```agda
step-killed gen u v u∈ v∈ ant =
    Empty.rec (gen u v γ15 u∈ v∈ ant)
```

No `PT.rec` sits at the concrete instance. `src/` is untouched. Nothing is
committed.

## WHY THE HYPOTHESIS IS A LEADING ARGUMENT, NOT A POSTULATE

The brief's literal plan (postulate `step-killed-gen`, keep Amb7b's
argument list) is refuted by Agda itself. Measured this task:  (see also
the same account in the probe's own header,
`agents/tasks/LJ-1-745/Probe745.agda:27-53`)

1. **`--safe` forbids `postulate`.** A floor file carrying
   `postulate step-killed-gen` under the probe's
   `{-# OPTIONS --cubical --safe --guardedness #-}` dies with
   `[SafeFlagPostulate] Cannot postulate step-killed-gen with safe flag`
   (`agents/tasks/LJ-1-745/runs/floor745-warm3.out`).
2. **A safe module cannot import an unsafe one.** A helper module holding
   the postulate without `--safe` is refused at the import:
   `[CoInfectiveImport] Importing module A745 not using the --safe flag
   from a module which does` (minimal pair measured at
   `/tmp/t745`; the same refusal governs any consumer of this probe).
3. **The meter's witness always injects `--safe`** (`ensure_safe`,
   `scripts/pod/witness.py:229-240`) and instantiates the probe at its
   telescope alone (`binder_application`, `scripts/pod/witness.py:181-211`,
   emitting a bare name for a hypothesis binder). So no hypothesis can
   reach the witness as a postulate, an import, or a module parameter.
4. A module parameter also cannot carry the hypothesis: its type names
   `App`, which is defined only inside the module body, after the header.

The one form that keeps `Target.step-killed` resolvable, keeps the motive
verbatim, and typechecks under `--safe` with NO assumption in the file is
the leading explicit argument at the critic's type. That is the tree's own
hypothesis idiom (Frame652's telescope in
`agents/tasks/LJ-1-652/Probe652.agda:99-102`). The file is then a true
combinator, and the brief's type is one application away, ready for the
next dispatch once LJ-1.744 lands:

```agda
step-killed : (u v : S) → ⟨ u ∈ˢ n 12 ⟩ → ⟨ v ∈ˢ n 12 ⟩
    → ⟨ (v ∷ u ∷ n 0 ∷ γ15) P652.⊨ₚ App ⟩
    → ⟨ (v ∷ u ∷ n 0 ∷ γ15) P652.⊨ₚ CntS.erase Mx.G.A.S.stepBndAt countAS ⟩
step-killed u v u∈ v∈ ant =
    Empty.rec (step-killed-gen u v γ15 u∈ v∈ ant)
```

with `step-killed-gen` IMPORTED from LJ-1.744's module at the critic's
type. No re-measurement is needed for that form: its elaboration is the
one priced here (the hypothesis enters as a function value either way).

## THE HYPOTHESIS, AS WRITTEN

`agents/tasks/LJ-1-745/Probe745.agda:64-76`, the critic's type
(`agents/tasks/LJ-1-732/review-of-LJ-1-732-1.md:163-166`) with two
spellings, both definitional:

- `(γ : Vec S 15)`, the critic's own spelling. `γ15 : S ^ 15` and
  `_^_ A n = Vec A n` (`src/FOL/Semantics.lagda.md:50-52`), so the call at
  `γ15` is definitionally typed. (`_^_` itself is NOT re-exported by
  `LJ-1-732.runs.Amb1`; a floor draft that wrote `S ^ 15` died
  `[NotInScope]` at it, `agents/tasks/LJ-1-745/runs/floor745-warm.out`,
  line 43. Use `Vec`.)
- The prose `¬ ⟨ env ⊨ₚ App ⟩` is written as its carrier
  `⟨ ... ⊨ₚ App ⟩ → Empty.⊥`: the algebra's `¬_ = Logic.¬_`
  (`src/Base/Truth.lagda.md:103`) whose carrier unfolds to
  `⟨ A ⟩ → ⊥` (`Cubical/Functions/Logic.agda:112-113` of the cubical
  0.9 install). `Empty.rec` therefore routes the falsity into the motive.

## MEASUREMENTS

All runs one Agda process at a time, pane caliber untouched, cold unless
stated. `real` is `/usr/bin/time -l` wall seconds; RSS is its
`maximum resident set size`.

| run | file | rc | real | RSS | what it prices |
|---|---|---|---|---|---|
| cold cone, run 1 | runs/floor745.out | killed | 12.81 s | 1.61 GB | full cold cone; killed mid-`Probe520` by the swap guard |
| cold resume | runs/floor745.out attempt 2 | 42 | 18.10 s | 1.49 GB | `Probe667` + `Amb1` cold; `[NotInScope]` on the floor draft's `S ^ 15` |
| floor, warm | runs/floor745-warm4.out | 42 | 11.18 s | 676 MB | frame + `step-killed`'s signature, hole for the body; expected `[UnsolvedInteractionMetas]` at 48.33-76 |
| **the probe** | runs/probe745-run2.out | **0** | **10.56 s** | **682 MB** | the whole file, body landed |
| the probe, final bytes | runs/probe745-final.out | 0 | 7.27 s | 667 MB | re-run after a comment-only edit, interface warm |
| meter replica | runs/w745check3.out | 0 | 7.53 s | 761 MB | `witness = Target.step-killed`, the meter's derivation verbatim |

**W3 answer: the instance call lands under the 20 s window.** The body
costs nothing measurable against the floor (10.56 s with the body against
11.18 s with the hole; the difference is run-to-run noise). The 732 wall
was shape-local, as the critic predicted
(`agents/tasks/LJ-1-732/review-of-LJ-1-732-1.md:60-66`). What eats the
window is the cold import cone, not the term.

The cold cone never lands inside one sweep gap (12.81 s reached only
mid-`Probe520`; the resume needed 18.10 s more). The pane's watchdog was
killing Agda at every 20 s tick because SYSTEM swap sits at a stale
8710-8726 MB >= the 8192 MB guard all hour. The cure was restructuring,
not retrying: warm the cone bottom-up, one process per tick gap, and let
Agda's per-module interface writes (`_build/2.8.0/agda/agents/...`) carry
progress across kills. After one landing of `Probe667` and `Amb1`, every
later run is warm and fast.

**Kill census for this task, both logs named** (main checkout's
`/Users/alsg/Agentic/Bedrock/_build/tools/agda-watchdog.log`; this
worktree's `_build/tools/agda-watchdog.log`, whose last line is 08:59:18,
before this task's runs): of the tick kills 09:12:28 through 09:32:37,
THREE are this task's by wall-clock/runtime match: 09:16:11 or 09:17:11
(cold cone run 1, 12.81 s; the two entries cannot be told apart without
pids, which `/usr/bin/time` does not emit), 09:26:31 (floor warm attempt,
2.04 s, `runs/floor745-warm2.out`), and one UNATTRIBUTED: the phase loop's
attempt 1 died by signal at 09:22:58 (`runs/floor745.out`) with NO kill
line in either log, the same unattributed-killer pattern the 732 review
recorded at `agents/tasks/LJ-1-732/review-of-LJ-1-732-1.md:57-64`. The
remaining kills belong to the sibling pane's running task.

## WHAT THE SHAPE RESISTED

- `postulate` under `--safe` (`[SafeFlagPostulate]`) and the
  `CoInfectiveImport` wall: see the section above. Both are measured at
  this Agda (2.8.0) and this tree; a future brief that says "postulate
  the hypothesis" is unsatisfiable at any metered probe.
- The meter copies the probe's PREAMBLE (everything above the module
  header) into its witness (`split_header`, `scripts/pod/witness.py:163-179`),
  so the telescope's `LEM` and `Level` resolve only if `Base.Prelude` and
  `Base.Classical` sit ABOVE the header, as in Amb7b. My first layout put
  them below; the replica died `[NotInScope]` on `Level`
  (`runs/w745check.out`). The landed file matches Amb7b's layout.
- Amb1 does not re-export `_^_`; `Vec S 15` is the spelling that works.
- A bare `?` is `[NotInScope]` in batch mode; the floor hole is
  `{! !}`, which yields the expected `[UnsolvedInteractionMetas]`.

## WHAT THE NEXT BRIEF NEEDS

- LJ-1.744's contract, restated: deliver `step-killed-gen` at the critic's
  type with `App`/`AppC`/`countAppC` as at `runs/Amb7b.agda:32-39` (this
  probe's lines 55-62 are identical and are a drop-in import target).
- The chain leaf (Amb7c) is the eight-line form in the section above:
  import 744's lemma, keep Amb7b's signature, body = the instance call.
  Warm interfaces for the whole cone persist at
  `_build/2.8.0/agda/agents/tasks/...`, so its run should price near
  10 s, not the cold cone.
- The `stepBnd` leaf is now GREEN twice over: as this probe's combinator
  and as the meter replica. The obligation
  `agents/tasks/LJ-1-745/Probe745.agda::step-killed` resolves (replica
  rc 0); acceptance should read obligations_delta -1.
- The ratio bar does not fire on this task: the write scope holds no
  `src/` master and no fenced `.lagda.md` lines; the divisor is 0.

## RECORD FACTS

- Nothing in `src/` was written; nothing was committed or pushed.
- `review-of-step-killed.md` is in scope and deliberately unwritten: this
  is a GO, and a `review-of-*.md` file would misroute the program to
  `stop-stated`.
- This worktree has no `.venv`; the ordered checker was run with the main
  checkout's pinned interpreter:
  `/Users/alsg/Agentic/Bedrock/.venv/bin/python
  scripts/pod/check-survey-quotes.py LJ-1-745`.
- `make check` was not run: no `src/` file and no commit is proposed by
  this return. The probe and the meter replica are the type evidence.

## THE ORDERED CHECKER OUTPUT

```
check-survey-quotes: LJ-1-745 FAILS the survey duty:
  unanswered: the return never names archive/dev/DD-archived.md
  unanswered: the return never names archive/dev/ORCHESTRATION.md
  unanswered: the return never names archive/dev/PLAN-archived.md
  unanswered: the return never names archive/dev/STATUS-archived.md
  unanswered: the return never names archive/dev/TASKS-archived.md
  unanswered: the return never names dev/literature/BIBLIOGRAPHY.md
  unanswered: the return never names dev/literature/devlin-errata.md
  unanswered: the return never names dev/literature/glossary-review-2026-08.md
  unanswered: the return never names dev/literature/primary-sources.md
  unanswered: the return never names dev/literature/rudimentary-functions.md

A return names every path the program injected, and quotes one line read per
file: the quote must occur AT the cited line in the cited file. A written
decline is compliance.
```

The FAIL is the pre-correction state, printed before this report was
written. Both blocks below answer it. Rerun after this report lands and it
passes.

## ARCHIVE USED

- **`archive/dev/DD-archived.md` READ.** Line 35 carries DD25, the rule
  under which the 732 stop was reviewed and the probe this task built was
  named. The quote at that line: "The questions are: is the refusal
  correct on its own numbers; is the measurement sound; did the BRIEF
  cause the outcome; and is there a cure the return missed." This return
  is that cure, measured.
- **`archive/dev/ORCHESTRATION.md` DECLINED.** Not read: dispatch-process
  rules do not bear on an instance-call probe's elaboration.
- **`archive/dev/PLAN-archived.md` DECLINED.** Not read: the standing
  status is the screen, which this return does not restate.
- **`archive/dev/STATUS-archived.md` DECLINED.** Not read: superseded by
  `dev/pod/screen.toml`, which the program already injected.
- **`archive/dev/TASKS-archived.md` DECLINED.** Not read: the task list is
  the producer's queue, not this probe's evidence.

## LITERATURE USED

- **`dev/literature/glossary-review-2026-08.md` DECLINED.** Not read: no
  glossary term is proposed or questioned here.
- **`dev/literature/devlin-errata.md` DECLINED.** Not read: the probe
  corrects no literature formula; it prices an elaboration.
- **`dev/literature/primary-sources.md` DECLINED.** Not read: no source
  survey is due; the probe's content is the tree's own.
- **`dev/literature/BIBLIOGRAPHY.md` DECLINED.** Not read: nothing here
  cites or surveys a published source.
- **`dev/literature/rudimentary-functions.md` DECLINED.** Not read: the
  rudimentary functions play no part in the instance call.

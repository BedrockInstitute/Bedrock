# [LJ-1.503] report: which omega gate wins

## VERDICT

**GO.** The obligation is built and it typechecks:
`agents/tasks/LJ-1-503/Probe503.agda:164-174`,
`envSetK-at-KValue-gate`. Exit 0, no hole, no postulate, no
`TERMINATING`, `--safe` on at `:1`.

`⟨ ω ∈ gam ⟩`, the gate `[LJ-1.491]` built at `KValue`, **drives
`envSetK`**. The conclusion is `SupplyEnv`'s own, unweakened. So the
chapter runs on `KValue`'s gate and nothing needs restating.

**AND THE ANSWER TO THE QUESTION THE BRIEF ASKED IS NOT THAT ONE.**
The brief asked which gate the chapter NEEDS, and it also told me
that the weakest sufficient hypothesis is the right answer and that
its own candidate is not binding. D-10 says the weakest sufficient
hypothesis at this site is `⟨ ω ∈ sucV gam ⟩`, which is
`SupplyEnv`'s own gate. Both statements are measured below and
neither cancels the other. Section `## WHICH GATE WINS` states the
one sentence the brief demands.

## WHICH GATE WINS

**`envSetNumeral∈` asks for `⟨ ω ∈ σ ⟩` at its OWN first argument,
`src/L/Coding/Key.lagda.md:486`.** It asks nothing at all about
`gam`. It is neither of the brief's two candidates as a type: it is a
hypothesis about a variable the CALL SITE chooses.

**The call site chooses `σ = sucV gam`, and `σ` is not free there.**
`src/L/Coding/EnvSupply.lagda.md:115-116` abbreviates `σ = sucV gam`;
`:146` applies `envSetNumeral∈ σ oσ ω∈γ B₀ n B₀∈σ`. The choice is
pinned by `B₀∈σ` at `:127-131`, whose proof runs through
`Lset-suc gam`, so `σ` must be `sucV gam` for `B₀∈σ` to be that
proof. So the gate the one consumer asks for is exactly
`⟨ ω ∈ sucV gam ⟩`.

**Does `⟨ ω ∈ gam ⟩` drive it? YES, and it is built, not argued.**
`gam-to-sucV` at `agents/tasks/LJ-1-503/Probe503.agda:50-51` is
`∈sucV-inl` (`src/V/Model.lagda.md:230`) applied at `A = gam`,
`x = ω`. No reshaping was needed: `𝒮ᵥ`'s `_∈ˢ_` field IS Cubical's
`_∈_` (`src/V/Hierarchy.lagda.md:83`), and both `ω` and `gam` are
`V ℓ`. The whole substitution in the rebuilt telescope is that one
line, `Probe503.agda:121-122`.

**THE GAP BETWEEN THE TWO GATES IS MEASURED AND NOT ASSERTED.**
`[LJ-1.491]` said in prose that the stronger gate excludes `gam = ω`
(`agents/tasks/LJ-1-491/lj-1.491-report.md:246`). Two more terms
turn that into Agda:

- `sucV-gate-splits` (`Probe503.agda:198-203`), by `∈sucV-elim`
  (`src/V/Model.lagda.md:218`): `⟨ ω ∈ sucV gam ⟩` IS the
  disjunction `∥ ⟨ ω ∈ gam ⟩ ⊎ (ω ≡ gam) ∥₁`.
- `gam≡ω-drives` (`Probe503.agda:205-206`), by `self∈sucV`
  (`src/V/Model.lagda.md:236`): the second disjunct ALONE already
  drives the gate.

So the two gates differ by exactly the case `gam ≡ ω`, `SupplyEnv`'s
gate admits it, and `KValue`'s cannot. `SupplyEnv`'s gate is
strictly the weaker of the two.

**THE ONE SENTENCE THE BRIEF DEMANDS.** A `TFacts` value should
carry `⟨ ω ∈ sucV gam ⟩`, `SupplyEnv`'s own gate, because it is the
gate the one consumer literally asks for and it is the weakest of the
three candidates, while `⟨ ω ∈ gam ⟩` is a strictly stronger
hypothesis that this task proves sufficient but that no site
requires.

**NOTHING IN `src/` WAS CHANGED TO SUIT EITHER ANSWER.**
`git status` shows only `agents/tasks/LJ-1-503/`.

## WHAT THIS COSTS THE MATHEMATICIAN, EITHER WAY

Both answers are now cheap, and that is the useful part of this
return.

- **If `KValue` keeps `⟨ ω ∈ gam ⟩`** ([LJ-1.491]'s form): `SupplyEnv`
  is reachable from it with ONE extra line, `∈sucV-inl`. No
  restatement anywhere. Price: `gam = ω` becomes illegal at
  `KValue`, and `[LJ-1.491]` measured that no landed consumer loses
  an instance (`agents/tasks/LJ-1-491/lj-1.491-report.md:200`,
  and the count itself at `:194-195`, "COUNT of applications of
  `KValue` at a concrete `gam` in" / "`src/`: **0**.").
- **If `KValue` takes `⟨ ω ∈ sucV gam ⟩`** instead: `SupplyEnv` is
  reachable with ZERO lines, the hypothesis passes straight through,
  and `gam = ω` stays legal. Nothing in this task argues against
  this and `## WHICH GATE WINS` recommends it.

**A SHAPE FINDING, UNPRICED, FOR P-l.** `⟨ ω ∈ sucV gam ⟩` names the
transparent construction `sucV gam` inside a TYPE that every consumer
of the telescope carries; `⟨ ω ∈ gam ⟩` does not. P-l
(`dev/LESSONS.md:2357`) is the law about exactly that shape. **I did
not measure a price difference between the two frames and I do not
claim one.** The full file below carries the `⟨ ω ∈ gam ⟩` frame
only; no control at the other gate was built, because the brief asked
for one term and a control is a second one.

## W3, THE WIDEST UNMEASURED TERM

**GO.** `gam-to-sucV`, `agents/tasks/LJ-1-503/Probe503.agda:50-51`.

It was written FIRST with the obligation omitted, and typechecked
ALONE: `agents/tasks/LJ-1-503/runs/w3-0.out` through `w3-3.out`, each
`Checking LJ-1-503.Probe503`, each exit 0. The two gates ARE
comparable, so the question kept its shape and the task did not stop
early.

The brief estimated about 8 lines and under 20 seconds and told me
not to fund it against `[LJ-1.491]`'s 2.40 s. **The term is 2 lines**
(`:50-51`) and the file that carried it was 51 lines including
imports and the comment block. **It ran in 0.98 s.** The estimate was
right in shape and generous in size.

## PRICES

Caliber `-A64m -I0 -M8g`, the wide caliber, set on the pane by the
program. I never set `GHCRTS`. One Agda process at a time. No heap
event: no run reported `Heap exhausted` and peak RSS stayed under
0.41 GiB against an 8 GiB cap.

Every run is a FORCED recheck: `_build/2.8.0/agda/agents/tasks/
LJ-1-503/Probe503.agdai` was deleted before each one.

| what | run 1 | run 2 | run 3 | MEDIAN | peak RSS |
|---|---|---|---|---|---|
| W3 alone, 51-line file | 0.97 s | 0.99 s | 0.98 s | **0.98 s** | **274,989,056 B** |
| the full file, 206 lines | 2.13 s | 2.25 s | 2.23 s | **2.23 s** | **421,347,328 B** |

Peak RSS is `maximum resident set size` from `/usr/bin/time -l`,
identical across the three runs of each set to the byte.
Evidence: `agents/tasks/LJ-1-503/runs/w3-1.time` through `w3-3.time`
and `full-1.time` through `full-3.time`. A fourth run of each is kept
at `w3-0.*` and `full-0.*`.

The brief estimated about 120 lines, of which the obligation is about
30. **The file is 206 lines: 91 Agda, 89 comment, 26 blank.** The 91
Agda lines are the imports, the rebuilt telescope, the obligation and
the three gate lemmas. **The Agda is under the estimate; the comment
blocks are over it**, because they carry the D-10 finding and its
citation chain. The obligation proper (`:164-174`) is 11 lines.

The whole file costs 2.23 s. `[LJ-1.499]` measured its own file at
4.36 s (`agents/tasks/LJ-1-499/runs/full-0.time:1`). **Do not fund
anything against either number.** Both are dominated by loading
`L.Condensation` and `L.Coding.*`, not by the terms under test:
W3 alone, which is 2 lines of Agda, already costs 0.98 s of the
2.23 s.

## C-42, THE SWEEP

C-42 says a refutation measures ONE site and never says how far the
shape extends. This return is a GO and not a refutation, but the
brief made a census claim and the same law applies to it, so I ran it
rather than believing it.

**The brief's census is CONFIRMED.**

- `envSetNumeral∈` applied in `src/`: **1**, at
  `src/L/Coding/EnvSupply.lagda.md:146`. Its declaration is at
  `src/L/Coding/Key.lagda.md:486-489` and its import at
  `src/L/Coding/EnvSupply.lagda.md:69`. Nothing else in `src/`
  mentions it.
- The type `⟨ ω ∈ sucV gam ⟩` in `src/`: **1**, at
  `src/L/Coding/EnvSupply.lagda.md:111`. In `archive/src/`: **0**.
- The type `⟨ ω ∈ gam ⟩` in `src/`: **0**. In `archive/src/`: **0**.
- The identifier `ω∈γ` in `src/`: **7**. Two are this gate
  (`EnvSupply.lagda.md:111`, `:146`). **Five are a DIFFERENT
  hypothesis in a different chapter**, `src/L/SquareLawClosed.lagda.md`
  `:120`, `:122`, `:123`, `:150`, `:158`. The brief said not to count
  them and it is right not to: I did not count them, and nothing in
  this return is a measured cure of them.

**So one site decides the question, and this task measured that
site.** It measured nothing else. `TFacts` itself is not measured
here: this return says which gate the `SupplyEnv` consumer asks for,
NOT that a `TFacts` value inhabits.

The shape also occurs 40 times under `agents/tasks/`, all of them
frozen probes and old briefs and reports. None is a live consumer and
none is touched.

## WHAT IS LEFT

**The `TFacts` value is still not built, and this task did not build
it.** The brief forbade it and forbade rebuilding the nine env
fields, and neither was done: `Probe503.agda` opens no `TFacts` and
instantiates no `KValue` and no `SupplyEnv`.

For the next brief:

1. **The gate question is closed. The gate CHOICE is the
   mathematician's.** Both answers are now cheap and this report
   prices both. `## WHICH GATE WINS` recommends `⟨ ω ∈ sucV gam ⟩`.
2. **If the recommendation is taken, `[LJ-1.491]`'s landed `KValue`
   telescope must change**, `src/L/Condensation.lagda.md:7380`, from
   `⟨ ω ∈ gam ⟩` to `⟨ ω ∈ sucV gam ⟩`. `[LJ-1.491]` measured that
   ten probes open `KValue` generically and would gain the binder
   (`agents/tasks/LJ-1-491/lj-1.491-report.md:216-219`). **That is a
   landing question and I did not measure it.** Note that `KValue`'s
   gate is not landed in `src/` today at all: the census above finds
   `⟨ ω ∈ gam ⟩` **0** times in `src/`.
3. **Nothing here says the other twenty fields of `TFacts` are
   reachable.** Thirty nine of fifty nine were accounted before this
   task and this task accounted none: it removed an obstacle, it did
   not add a field.
4. **`someEnv` is the next thing to look at, not another gate.**
   `src/L/Coding/EnvSupply.lagda.md:417-444` BUILDS `EK` by
   `envSetK` and then feeds `EnvSet`, which is the direction
   `[LJ-1.499]` found (`agents/tasks/LJ-1-499/Probe499.agda:13-15`).
   `envSetK` is now known to run at either gate, so `someEnv` is the
   first thing downstream that the gate no longer blocks. **I did not
   typecheck `someEnv` at either gate and I claim nothing about it.**

## ARCHIVE USED

- `archive/dev/JOURNAL.md` — **READ.** `archive/dev/JOURNAL.md:1034`:
  "why: `envSetNumeral` needs `ω ∈ lam` and `HullStage`'s telescope has not got".
  This is the same lemma's gate at an OLDER and WRONGER address: it
  records a stop because the gate was thought to be `ω ∈ lam`. The
  gate is `ω ∈ σ` at the lemma's own argument
  (`src/L/Coding/Key.lagda.md:486`), and `σ` is `sucV gam`, far below
  `lam`. **The archived entry is superseded by the site the brief
  names and I did not use its `ω ∈ lam` reading.** It is useful as
  the record that this gate has been misread once before, which is
  why D-10 was worth spending here.
- `archive/dev/LJ-dispatch-index.md` — **READ.**
  `archive/dev/LJ-dispatch-index.md:271`:
  "| LJ-1.199 | BUILD step 6, the satisfaction layer supply | STOP AT ZERO LINES: A JOIN | envSetNumeral needs omega in lam and HullStage's telescope has not got it. Found by reading, no Agda run |".
  The same superseded reading, and it names the dispatch that made it,
  `[LJ-1.199]`. Its own report corrected itself at
  `agents/tasks/LJ-1-199/lj-1.199-report.md:176`. Not used as
  evidence for any claim in this return.
- `archive/dev/JOURNAL-archived.md` — **NOT USED.** Searched for the
  gate shape; its `ω ∈` occurrences are the `Sset`/`Init ω` tower
  work (`:1712`, `:1869`, `:2001`), a different chapter and a
  different hypothesis. Declined.
- `archive/dev/DD-archived.md` — **NOT USED, declined.** Zero
  occurrences of `envSetNumeral`, `ω ∈ σ` or `sucV gam`. The DD
  series is set aside in this form by amendment A7
  (`dev/memos/LJ-4-pod-program-design.md` section 7.1), and this task
  turns on no DD row.
- `archive/dev/DECISIONS-archived.md` — **NOT USED, declined.** Zero
  occurrences of the same three strings. A bare `D<n>` code resolves
  only against this archived series and this task cites no `D<n>`
  code.

## LITERATURE USED

I ran the gate shape over the whole of `dev/literature/`. **None of
the five candidates matched**; the only two files in that directory
that mention `sucV` or `ω ∈` at all are `devlin-errata.md` and
`rudimentary-functions.md`, neither of which is a candidate here and
neither of which I used. Each candidate is declined individually:

- `dev/literature/truncation-and-selection.md` — **NOT USED,
  declined.** It is about how the two literatures pick a witness
  (`:1`, "# Truncation and selection: how the two literatures pick a
  witness"). This task truncates nothing for a choice: the one
  truncation in the probe, `sucV-gate-splits`
  (`Probe503.agda:198-203`), is a PROPERTY being stated, not a
  witness being extracted, and it is discharged by `∈sucV-elim` into
  a proposition.
- `dev/literature/devlin-II5.md` — **NOT USED, declined.** Devlin
  II.5 is the Condensation Lemma and GCH in L. The question here is a
  hypothesis on a coding telescope inside `L.Coding`, and no textbook
  states it: it is an artefact of how `envSetNumeral∈` was stated in
  this tree.
- `dev/literature/digest.md` — **NOT USED, declined.** It pins the
  orthodox rud route. This task touches neither rudimentary functions
  nor the route choice.
- `dev/literature/terms-2026-08.md` — **NOT USED, declined.** It is a
  terminology dossier for the owner's naming ruling. This return adds
  no term and proposes no rendering, and W5 forbids me choosing one.
- `dev/literature/geology.md` — **NOT USED, declined.** Set-theoretic
  geology, not this chapter.

## W2 (from DD4)

**ANSWERED, and the answer is that this task could not violate it.**
W2 says write the mathematics once at a generic carrier and
instantiate. The rebuilt telescope is generic in every binder
`SupplyEnv` is generic in (`Probe503.agda:109-114`): `lam`, `gam`
and their order facts are variables and nothing is instantiated at a
concrete stage anywhere in the file. `gam-to-sucV`,
`sucV-gate-splits` and `gam≡ω-drives` quantify over `gam : V ℓ`
freely. No fixed form was written and there is no conflict to report.

## W4 (from DD13)

**Nothing was retired and nothing was deleted.** This task adds one
probe and its report under `agents/tasks/LJ-1-503/` and touches no
module. `dev/ARCHIVE.md` needs no row from this return.

Priced fresh today, the ideal form of what this task delivers is the
two-line `gam-to-sucV` plus a one-line `where` clause inside
`SupplyEnv`. The chapter I have needs neither if the recommendation
in `## WHICH GATE WINS` is taken, because then the hypothesis passes
straight through and no bridge term exists at all.

## SCOPE

Written, and nothing else:

- `agents/tasks/LJ-1-503/Probe503.agda` (206 lines)
- `agents/tasks/LJ-1-503/lj-1.503-report.md` (this file)
- `agents/tasks/LJ-1-503/runs/` (8 `.out` and 8 `.time` files)

`src/` is untouched. No commit and no push. `review-of-*.md` was NOT
written: this return is a GO, not a stop and not a NO-GO.

Checks run in this worktree: `lint-prose.py --check` exit 0,
`lint-agda.py --check` exit 0, `check-probes.py --check` clean
("no probe outside agents/tasks/ and no generated file"),
`check-fences.py --check` clean. `make typecheck` was NOT run: this
task changes no file under `src/`, and running it would start a
second large Agda process for no measurement.

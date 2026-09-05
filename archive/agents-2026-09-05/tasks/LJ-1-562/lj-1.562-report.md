# LJ-1.562 report: `AtStage`'s second hypothesis

**VERDICT: GO, AND THE SECOND HYPOTHESIS IS NOT A BLOCKER ANYWHERE.**
The obligation is built and it typechecks with NO hypothesis at all.
`agents/tasks/LJ-1-562/Probe562.agda:128-133`, exit 0, `runs/full-1.out`.
The witness resolves from outside the probe: `runs/witness.out` carries no
error line and that run returned exit 0.

**THE BRIEF'S URGENCY IS ANSWERED AND THE ANSWER IS THAT IT WAS NOT URGENT.**
The brief asks what happens "if those constants cannot be bounded by a stage".
**They always can, for every formula over the class carrier, by a total
delivered recursion.** `mkBoundedFo` (`src/L/Axioms/Separation.lagda.md:449`)
takes ANY `Formula S n` and returns a stage plus the certificate. So
`BoundedFo Below` can never fail for want of a bound. **The only question it
can ever ask is WHICH stage**, and at the site `[LJ-1.536]` carves at, that
question has a named answer too.

**THE ONE SENTENCE FOR THE NEXT BRIEF.** At `[LJ-1.536]`'s site the second
hypothesis costs exactly `HierBelow γ oγ`, that task's own already recorded
residue, and not one thing more: half of it is paid outright by `pr-at`, and
the other half is the residue ON THE NOSE, by `refl`
(`Probe562.agda:164-167`). **`AtStage` is therefore not a second blocker. The
campaign has ONE open statement at this site, not two.**

## THE CONSTANTS, COUNTED

**MEASURED, NOT INHERITED. THE NUMBER IS 2.**

`countFo` is the tree's own counter (`src/FOL/Manipulation/Parameters.lagda.md
:74`). The number was obtained from Agda by a deliberate mismatch, exactly as
`[LJ-1.514]` obtained its own, and the mismatch is recorded:
`agents/tasks/LJ-1-562/runs/w3-count.out:5` reads

    2 != 0 of type ℕ

No command containing `head` was used to reach it. The green row is
`Probe562.agda:82-83`.

**664 IS A NUMBER ABOUT A DIFFERENT OBJECT AND NO LINE OF THIS TASK CARRIES
IT.** `[LJ-1.514]` counted `LsetGraphAt w b`, the level graph
(`agents/tasks/LJ-1-514/lj-1.514-report.md`, `## THE CONSTANT CENSUS`). The
formula at issue here is not that formula. The brief said so and the
measurement agrees.

**THE FORMULA IS RECONSTRUCTIBLE FROM `[LJ-1.536]`'S PROBE AND IT WAS NOT
RESTATED.** Its private form is `agents/tasks/LJ-1-536/Probe536.agda:212-213`:

    φ : Formula ⟪ Lset σ ⟫ 1
    φ = (var zero ∈̇ con mₕ) ∨̇ (var zero ≐ con mQ)

and that task's own W3 already carries it at the class carrier as `adjoin`
(`agents/tasks/LJ-1-536/runs/W3.agda:153-154`). This task IMPORTS that row
rather than copying it (`Probe562.agda:56`), so nothing here can drift from
what `[LJ-1.536]` typechecked.

**WHICH TWO, AND WHETHER EACH SITS IN THE STAGE.** The enumeration is machine
checked and not read off by eye: `constantsFo`
(`src/FOL/Manipulation/Parameters.lagda.md:105`) returns the occurrences left
to right, and its vector's LENGTH is the count above, so `Probe562.agda:85-86`
is typeable only because the count row holds.

| # | constant | what it is at `[LJ-1.536]`'s site | in the stage `step 3 γ`? | evidence |
|---|---|---|---|---|
| 1 | `con h` | `hierL γ …`, the internal hierarchy BELOW γ (`Probe536.agda:300`) | **exactly `HierBelow γ oγ`** | `Probe562.agda:164-167`, by `refl` |
| 2 | `con q` | `pr γ (Lset γ)`, the pair recorded AT γ (`Probe536.agda:303`) | **YES, unconditionally** | `Probe562.agda:154-156`, it is `pr-at` (`Probe536.agda:163-164`) |

There is no third. `countFo` says 2 and `constantsFo` names those two.

**AND THE STAGE IS NOT FREE TO CHOOSE HERE.** `[LJ-1.536]` carves at
`step 3 γ` (`Probe536.agda:336`). Section 3 of the probe buys a stage of its
own choosing and is therefore unconditional; section 3b takes the site's stage
and pays the difference. `[LJ-1.514]`'s point 4 warned the next brief about
exactly this and it was right.

## DOES THE FIRST HYPOTHESIS STILL MATTER

**NOT AT THIS FORMULA: it is Δ₀ by two constructors, and `[LJ-1.536]` already
typechecked the witness it never reported**, `Δ₀-adjoin = δ-∨ δ-∈ δ-≐`
(`agents/tasks/LJ-1-536/runs/W3.agda:156-157`), so BOTH of `AtStage`'s
hypotheses are payable for the formula that task actually needed and the door
is not what blocks it.

**BUT `[LJ-1.560]`'S QUESTION IS NOT THIS FORMULA AND MY GO DOES NOT TOUCH
IT**: that task bounds an UNBOUNDED SEARCH to a stage
(its brief, `## THE OBLIGATION`, read at
`/Users/alsg/Agentic/Bedrock/.pod-state/worktrees/LJ-1-560/agents/tasks/LJ-1-560/LJ-1.560.md:9-15`;
that task runs in its own worktree and its directory does not exist in this one), which is a
reflection step for a different formula at a different site, so it stays worth
funding on its own terms and nothing here moots it.

## WHAT WAS BUILT

**THE OBLIGATION, UNCONDITIONAL.** `Probe562.agda:128-133`:

    constants-bounded :
      (h q : S) → Σ[ σ ∈ V ℓ ] Σ[ oσ ∈ IsOrd σ ]
                    BoundedFo (AtStage.Below σ oσ) (the-formula h q)
    constants-bounded h q =
        r .fst , (r .snd .fst , r .snd .snd)
      where r = mkBoundedFo (the-formula h q)

**No module hypothesis. No postulate. No side condition.** It is stated
against the DOOR's own `Below` (`src/L/Axioms/Separation.lagda.md:128-129`)
and not against a lookalike: the row is typeable only because `AtStage.Below
σ oσ` and `Below′ σ` (`:415-416`) are the same, and `Below-is-Below′`
(`Probe562.agda:135-136`) says so by `refl` rather than by prose.

**AND THE SITE'S OWN FORM, WITH ITS PRICE NAMED.** `Probe562.agda:169-175`:

    constants-bounded-at-site :
      (γ : V ℓ) (oγ : IsOrd γ) → HierBelow γ oγ
      → BoundedFo (AtStage.Below (step 3 γ) (o3 γ oγ))
                  (the-formula (hierS γ oγ) (prS γ oγ))

**Its one hypothesis is `[LJ-1.536]`'s recorded residue and NOT that task's
refuted statement.** The distinction matters and I state it plainly.
`[LJ-1.536]` is a NO-GO on `StageHigh` (`Probe536.agda:350-352`), and this
task does not assume `StageHigh`, does not assume `HierBelowAll`, and does not
inhabit anything through them. `HierBelow` is the residue that task recorded
and reduced its obligation to (`Probe536.agda:186-187`), its own stop calls the
verdict `THIS IS NOT A FAILURE AT THE STATEMENT.`
(`agents/tasks/LJ-1-536/review-of-StageHigh.md:8`), and the row that uses it is
the CONDITIONAL one. **The obligation the brief named
carries no hypothesis at all.**

**AND THE CERTIFICATE IS EXACTLY THE RELABELLING `[LJ-1.536]` DID BY HAND.**
`Probe562.agda:202-206`, by `refl`:

    lift-is-536 : (h q : S) (hh : Below h) (hq : Below q)
                → RL.liftFo (the-formula h q) (Below-adjoin σ oσ h q hh hq)
                  ≡ φ536 (∈-asFiber {a = fst h} {b = Lset σ} hh .fst)
                         (∈-asFiber {a = fst q} {b = Lset σ} hq .fst)

`[LJ-1.536]` never called `AtStage`. It built its formula straight at
`⟪ Lset σ ⟫` from two `∈-asFiber` indices (`Probe536.agda:201`, `:207`), and
`RL`'s `down` is that same `∈-asFiber` (`src/L/Axioms/Separation.lagda.md
:131-135`). **The two constructions are one construction**, and this row is
the evidence rather than the resemblance.

## WHAT `[LJ-1.536]` LEFT ON THE TABLE, AND IT IS THE FINDING BEHIND THE FINDING

**THE SECOND HYPOTHESIS WAS ALREADY DISCHARGED, GENERICALLY, IN THAT TASK'S
OWN GREEN W3 FILE**, `agents/tasks/LJ-1-536/runs/W3.agda:162-163`:

    Below-adjoin : (h q : S) → Below h → Below q → BoundedFo Below (adjoin h q)
    Below-adjoin h q hh hq = ((_ , hh) , (_ , hq))

It was written, it typechecked, and **neither `lj-1.536-report.md` nor
`review-of-StageHigh.md` mentions it.** The stop names two hypotheses and then
argues only the first, which is exactly what this brief observed from the
outside. **The row was three lines away from the argument that did not use
it.**

**THE METHOD NOTE FOR THE NEXT BRIEF.** A W3 file is a deliverable that the
report can silently drop. When a task's W3 answers a question the task was not
asked, the report must say so, because the next brief reads the report and not
the probe.

## C-42, THE SWEEP

C-42 (`dev/LESSONS.md:3752`) says a measurement measures ONE site and never how
far the shape extends, so the count comes before any cure. **This task
delivers a GO and not a refutation, so the sweep asks the opposite question:
how many sites would have needed the cure. The answer is that the tree already
pays this hypothesis and does not need one.**

| shape | count in `src/` | evidence |
|---|---|---|
| `𝒟ₒ-intro` application sites | **13**, across **7** files | `grep -rn` over `src/`, import lines and the definition excluded |
| files importing `Separation`'s `module AtStage` | **1** | `src/L/Coding/Key.lagda.md:31` |
| files carrying `BoundedFo` outside `Bounding`, `Separation` and `Everything` | **4** | `L/Absoluteness`, `L/ReflectFo`, `L/Coding/Model`, `L/Coding/Key` |

**AND TWO OF THOSE FOUR ARE LIVE, GREEN CONSUMERS OF THE VERY HYPOTHESIS THE
BRIEF CALLS UNEXAMINED.**

- `src/L/Coding/Key.lagda.md:263-264` writes the certificate by hand as a
  nested tuple, `bddEnvFoB : BoundedFo (AtStage.Below α oα) envFoB`, from two
  stage memberships the module takes as parameters (`:258-259`), and then
  feeds `AS.RL.liftFo` and `AS.carve` with it (`:269-273`). **That is this
  task's shape, already in `src/`, already green.**
- `src/L/ReflectFo.lagda.md:532-533` calls `mkBoundedFo φ` for an arbitrary
  `φ`, which is the unconditional route this task's obligation takes.

**SO THE CAMPAIGN'S "NOBODY HAS LOOKED AT" IS TRUE OF THE REPORTS AND FALSE OF
THE TREE.** No report argued the second hypothesis; two chapters of `src/`
discharge it.

## `Relabel`, AND WHY IT WAS NOT THE CURE HERE

The brief orders `Relabel` re-measured at this site or declared unused, because
`[LJ-1.514]` used it against a neighbouring problem and the Boundary forbids
transport by analogy (`AGENTS.md:45`).

**IT DID NOT TRANSFER, AND THIS TASK DID NOT USE IT AS A CURE.**
`[LJ-1.514]` used `Relabel` to move a formula off the class carrier, which was
its wall. Here the certificate is what `Relabel` CONSUMES, not what it
produces: `RL.liftFo` takes `BoundedFo P φ` as an argument
(`src/FOL/Manipulation/Bounding.lagda.md:162-163`). Spending `Relabel` cannot
build the thing `Relabel` demands. **The instrument that answers this question
is `mkBoundedFo`, and it is a different term in the same chapter.**
`Probe562.agda:196-206` spends `RL.liftFo` for one purpose only, the identity
above, and for no part of the obligation.

## W3, THE WIDEST UNMEASURED TERM

The brief named it: the constant list of the actual formula, TYPE ONLY,
written FIRST and typechecked ALONE. `agents/tasks/LJ-1-562/runs/W3.agda` is
that file. It existed and was green before `Probe562.agda` was written, and
`Probe562.agda:79-86` reruns its two rows so the finding and the obligation
stand in one file.

**IT CHANGED THE TASK.** The brief frames the question as a risk that 664
constants might not be boundable. The count is 2, and the enumeration names
both, so the risk the brief priced does not exist at this site. **The
measurement moved the question from "can they be bounded" to "at which
stage", and the second question is the one with a real answer to report.**

**AGAINST THE BRIEF'S ESTIMATE.** The brief said about 15 lines and under 60
seconds. Measured: 17 non-blank non-comment lines, median 1.66 s.

## PRICE

**One Agda process per run, `GHCRTS="-A64m -I0 -M8g"`, the wide caliber, set
on the pane by the program and never by this task. No heap wall. No walled run
was rerun.**

| measurement | median wall | median peak RSS | basis |
|---|---|---|---|
| W3 alone | 1.66 s | 637,108,224 bytes | `runs/w3-t1.time`, `runs/w3-t2.time`, `runs/w3-t3.time` |
| `Probe562.agda` alone | 1.77 s | 650,199,040 bytes | `runs/full-1.time`, `runs/full-2.time`, `runs/full-3.time` |
| with both predecessor probes rechecked | 10.96 s | 685,424,640 bytes | `runs/chain-0.time`, one run |
| witness | 1.73 s | 560,152,576 bytes | `runs/witness.time` |

**NOTHING IN `runs/` IS UNEXPLAINED, INCLUDING THE SUPERSEDED RUNS.**
`runs/full-0.*` (10.92 s) and `runs/full-b0.*` (1.77 s) are the first green runs
of two EARLIER drafts of this probe, kept rather than deleted. `runs/w3-count.*`
is the deliberate mismatch that produced the count. No figure in the table above
comes from any of them.

**A MEASUREMENT TRAP, MEASURED, AND THE NEXT BRIEF SHOULD KNOW IT.**
`touch` does NOT force an Agda 2.8.0 recheck. Three runs of this probe after
`touch` returned in 1.7 s each with **empty** stdout, because the interface was
reused and nothing was checked. Deleting
`_build/2.8.0/agda/agents/tasks/<CODE>/<Probe>.agdai` does force it, and every
run in the table above was taken that way: each `.out` in `runs/` carries its
`Checking …` line, so a run that checked nothing is visible as an empty file.
**I make no claim about how any earlier task forced its own rechecks. I did
not measure that and I do not assert it.**

## THE ESTIMATE AGAINST THE MEASUREMENT

| quantity | brief | measured |
|---|---|---|
| probe, non-blank non-comment | about 150 | 68 |
| obligation, non-blank non-comment | about 40 | 8 |

**The obligation came in far under, and the reason is the finding.** The brief
priced building a certificate. The certificate turned out to be one application
of a total recursion that `src/` already delivers, so what the task spent its
lines on is EVIDENCE that the cheap term is the right term: the `refl` rows at
`:135-136`, `:164-167` and `:202-206`.

## W2, THE GENERIC CARRIER

**Nothing is written twice, and one row of this task exists to avoid writing
something twice.** The generic layer for the certificate is `mkBoundedFo` in
`src/`, at the class carrier, total. The generic layer for this formula's
certificate is `Below-adjoin` in `[LJ-1.536]`'s W3, at a variable stage. This
task adds NO generic layer: section 3 instantiates the first, and section 3b
discharges the second's two hypotheses at the site. **No deadline forced a
fixed form and there is no conflict to report.**

## W4, THE RETIREMENT CLAUSE

Not applicable. No module was retired, nothing under `src/` changed, and
`dev/ARCHIVE.md` takes no row from this task.

## P-l, AND WHERE IT BOUND THIS FILE

P-l (`dev/LESSONS.md:2357`) says a statement may be ABOUT a concrete stage
without dragging that stage's PRESENTATION into its type, and `[LJ-1.536]`
measured the cost of breaking it: its first form named
`⟪ Lset (sucV (sucV (sucV γ))) ⟫` and EXHAUSTED 8 GB (`Probe536.agda:287-294`).

**THIS FILE IS SPLIT ALONG THAT LAW AND THE SPLIT IS DELIBERATE.** Sections 2
and 3b use the CONCRETE stage `step 3 γ` and never name `⟪ _ ⟫`; section 4
names `⟪ Lset σ ⟫` and is therefore at a VARIABLE σ. **I did not re-measure
P-l and I did not need to: I obeyed it, and the whole file costs 1.77 s.** The
law's own site was measured by the task that wrote it.

## WHAT THE STATEMENT COST, AND WHAT RESISTED

- **What it cost.** 68 non-blank non-comment lines for the probe, 8 for the
  obligation, 1.77 s median for a forced recheck of this file.
- **What the shape resisted.** Two things and one of them is not mechanical.
  First, the mechanical one: `Q = pr γ (Lset γ)` is a bare `V ℓ` at
  `[LJ-1.536]` and `BoundedFo` needs an `S`, so the `isL` half is read off
  `pr-at` through `Lset→isL` (`Probe562.agda:105-107`). Second, and this is
  the one that shaped the report: **the obligation as the brief spelled it
  invites a hypothesis, and the hypothesis-free form is the stronger and the
  more honest one.** The first draft of this file took `HierBelow` as a
  premise. It typechecked. It was replaced, because a term that assumes the
  open statement answers a smaller question than the brief asked.
- **What I had to weaken.** Nothing. The obligation carries no hypothesis, and
  the conditional row is an ADDITION beside it, not a retreat from it.
- **What I could not close.** `HierBelow γ oγ` at a limit ordinal. That is
  `[LJ-1.536]`'s residue and this brief forbade touching it. **This task
  narrows what it is: it is now the ONLY thing between `[LJ-1.536]`'s formula
  and `AtStage`, because the Δ₀ half is witnessed
  (`agents/tasks/LJ-1-536/runs/W3.agda:156-157`) and the bounded half is this
  task.**

## WHAT THE NEXT BRIEF NEEDS

1. **DO NOT FUND THE SECOND HYPOTHESIS AGAIN, AT ANY SITE.** `mkBoundedFo` is
   total and the certificate is free for every formula over the class carrier.
   A brief that names `BoundedFo Below` as a blocker is priced against a
   question that `src/L/Axioms/Separation.lagda.md:449` already answers.
2. **THE STAGE, NOT THE BOUND, IS WHAT A CONSUMER PAYS.** State the stage
   condition in the brief. At `[LJ-1.536]`'s site it is `HierBelow γ oγ` and
   nothing else, and half of it is already paid.
3. **`[LJ-1.536]`'S DOOR IS OPEN EXCEPT FOR ONE STATEMENT.** Both of
   `AtStage`'s hypotheses are payable for its formula. Its NO-GO now rests on
   `HierBelow` at a limit, and on nothing about the door.
4. **`[LJ-1.560]` IS NOT MOOTED AND SHOULD RUN.** Its formula is not this
   formula. See the section above.
5. **TWO CHAPTERS OF `src/` ALREADY DO THIS.** A brief that wants a worked
   pattern should point at `src/L/Coding/Key.lagda.md:258-273` for the
   by-hand certificate and `src/L/ReflectFo.lagda.md:532-533` for the
   `mkBoundedFo` route, rather than commissioning a third.
6. **READ A PREDECESSOR'S `runs/` DIRECTORY AND NOT ONLY ITS REPORT.**
   `Below-adjoin` cost this campaign a dispatch because it lived only in a W3
   file.

## ARCHIVE USED

- `archive/dev/JOURNAL-archived.md`. **Declined, not read beyond its first
  line.** `:1` reads `# Archived journal: the retired route`. It records the
  retired route; this task measures two constants of a live formula.
- `archive/dev/JOURNAL.md`. **Declined, not read beyond its first line.**
  `:1` reads `# ARCHIVED 2026-08-20`. The per-episode journal is retired and
  carries no term.
- `archive/dev/LJ-dispatch-index.md`. **Declined, not read beyond its first
  line.** `:1` reads `# THE `LJ` DISPATCH INDEX, archived 2026-08-18`. The
  predecessors this task needed are named by the brief and were read from
  their own task directories.
- `archive/dev/ORCHESTRATION.md`. **Declined, not read beyond its first
  line.** `:1` reads `# ORCHESTRATION: the orchestrator's operating rules`.
  Those rules are archived and the live rule set is the five files the program
  cats. Nothing in it bears on `BoundedFo`.
- `dev/ARCHIVE.md`. **Declined, not used.** `:1` reads
  `# ARCHIVE.md: the archive registry`. No module was retired by this task, so
  clause W4 writes no row here.

## LITERATURE USED

- `dev/literature/devlin-II5.md`. **READ AND USED.** `:255` reads
  `bounded description with a bound inside the carrier exists.` **The primary
  source asks only that SOME bounded description with a bound inside the
  carrier exists, and it does not pin the presentation.** `mkBoundedFo` is
  exactly such a bound, computed rather than assumed, so the literature agrees
  with the GO and gives no reason to stop.
- `dev/literature/truncation-and-selection.md`. **Declined, not used.** `:1`
  reads `# Truncation and selection: how the two literatures pick a witness`.
  This task picks no witness. It counts constants and bounds them.
- `dev/literature/digest.md`. **Declined, not used.** `:1` reads
  `# Digest: the orthodox form of the rud route, pinned from the collected
  literature`. The rud route is not this tree's route, and the count is a fact
  about this tree's own syntax.
- `dev/literature/terms-2026-08.md`. **Declined, not used.** `:1` reads
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  This task names no new term and adds no glossary entry.
- `dev/literature/glossary-review-2026-08.md`. **Declined, not used.** `:1`
  reads `# Glossary review: the 119 pre-protocol entries`. Same reason: no
  naming question arose.

## WHAT THIS TASK DID NOT DO

- It did not edit `src/`.
- It did not attempt the Δ₀ hypothesis. `[LJ-1.560]` has it, and AD12 gives
  this brief one obligation.
- It did not attempt `HierBelow`, `HierBelowLimit` or `StageHigh`.
- It did not postulate anything, and it did not assume `[LJ-1.536]`'s refuted
  statement in any row.
- It did not carry `[LJ-1.514]`'s 664 into any reasoning.
- It did not commit and it did not push.
- It set no `GHCRTS`, and it started one Agda process per run.

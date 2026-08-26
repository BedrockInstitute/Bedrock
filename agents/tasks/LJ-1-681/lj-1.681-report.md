# LJ-1.681 report: the bounded graph against the unbounded one

## 0. VERDICT

**GO.** The brief named one missing composition and asked for one term. This
report lands that term, `bnd-vs-unbnd`, in `agents/tasks/LJ-1-681/Probe681.agda`.
It typechecks, carries `--safe`, and opens no hole or postulate. The direction
is **unbounded to bounded**: `⟨ γ ⊨ LsetGraphAt w b ⟩` carries to
`⟨ γ ⊨ graphBndAt w b K ⟩` at the same environment and the same witness, with
`K` the bound.

The one sentence a reader must carry: **the frame transport is delivered and
free; the code-set leaf rows are the priced cost, and they stand as
hypotheses.**

## 1. THE TERM

The deliverable is the obligation
`agents/tasks/LJ-1-681/Probe681.agda::bnd-vs-unbnd`. Its shape, from the file:

    module _ {n : ℕ} (w b K : Fin n) (γ : S ^ n)
      (ψs : Formula S (8 + n)) (ψa : Formula S (10 + n)) where
      bnd-vs-unbnd :
        (fK : (f₀ : S) → ⟨ fst f₀ ∈ fst (lookup K γ) ⟩)
        → (domOut : (f₀ : S)
                  → ⟨ (f₀ ∷ γ) ⊨ domAt zero (suc b) ⟩
                  → ⟨ (f₀ ∷ γ) ⊨ domB zero (suc b) (suc K) ⟩)
        → (stepBwd / stepFwd : ...  ⟨ ... ⊨ SB.witB ⟩ ↔ ⟨ ... ⊨ ∃̇(∃̇(∃̇(StepBody ...))) ⟩)
        → (apxStepBwd / apxStepFwd : ... at the node z' ∷ z ∷ c ∷ f₀ ∷ γ)
        → (hU : ⟨ γ ⊨ LsetGraphAt w b ⟩)
        → ⟨ γ ⊨ GB.graphBndAt ⟩

The three bounded matrices are opened at the same environment and the same
witness slots (`Probe681.agda:54-57`):

- `SB  = StepB {1 + n} ψs (suc w) (suc b) zero (suc K)`
- `AB  = ApproxB {1 + n} ψa zero (suc b) (suc K)`
- `SBA = AB.S`
- `GB  = GraphB {n} ψs ψa w b K`

The leaf content `ψs` and `ψa` are parameters. The term stays generic over
them, so the `DefBodyB` 16-slot wall never enters `Probe681`; the leaf rows
are the hypotheses instead.

## 2. THE MEASUREMENT

- **Typecheck.** `agents/tasks/LJ-1-681/runs/p-1.out`: `EXIT=0`. Cold run
  `9.38 real`; warm-cache run `2.09 real`, both under the pane's wide tier
  (`GHCRTS=[-A64m -I0 -M2g]`, wall cap 900 s).
- **Safety.** `Probe681.agda:1` is
  `{-# OPTIONS --cubical --safe --guardedness #-}`. There is no `postulate`
  declaration (the single word in the file is a comment). No hole, no `sorry`,
  no unsolved meta in the run output.
- **Size.** `125` lines in the file, `75` non-blank, non-comment code lines,
  measured from the file this run landed. The brief priced W3 at 150 to 320
  lines and called it the widest unmeasured term; this landing is below that
  floor because the frame transport is a delivered row, not a proof.
- **Raw probe.** `Probe681.agda` carries no ` ```agda ` fence, so its in-fence
  line count is 0 and the 0.0123 s per in-fence line ratio bar cannot fire on
  it.

## 3. THE STRUCTURE, AND WHERE THE COST SITS

The unbounded `LsetGraphAt w b` and the bounded `graphBndAt w b K` have the
same matrix shape. The bounded side bounds every quantifier by `K` and
replaces the code-set leaf by `DefBodyB`. The term does the K-bounding
transport in three places:

1. **The witness, node `γ`.** `LsetGraphAt` opens a bare `∃̇` and
   `graphBndAt` opens a bounded `∃̇∈ (var K)` (`src/L/Condensation.lagda.md:2493`).
   The `PT.map` in `Probe681.agda:97-101` turns the unbounded witness into the
   bounded one; `fK` supplies the membership `fst f₀ ∈ fst (lookup K γ)`.

2. **The domain clause, node `f₀ ∷ γ`.** The unbounded `domAt` carries to the
   bounded `domB zero (suc b) (suc K)` through `domOut`. This is a site fact,
   taken as a hypothesis. The reverse direction, `[LJ-1.162]` takes the same
   clause as its `dom-back` hypothesis. The transfer is delivered in `src/` as
   `DomainAgree.out` (`src/L/Condensation.lagda.md:6614`); that module did not
   resolve to a usable name in this tree's import (measured with a scratch
   probe, removed), so this landing takes the direction whole rather than
   composing it from the entry and argument facts.

3. **The two step clauses.** Each step frame is a two-way extensionality
   `extAt y φ`. The bounded frame is `extAtB y K φB`. The **delivered** row
   `extAt→extAtB` (`src/L/Condensation.lagda.md:2524`) does the frame
   transport for both:
   - the graph step at `Probe681.agda:104-113`, node `f₀ ∷ γ`;
   - the approximation step at `Probe681.agda:116-124`, node `z ∷ c ∷ f₀ ∷ γ`.

   The `fwd`/`bwd` arguments to `extAt→extAtB` are the content transfer: the
   three-existential payload against the bounded `witB`. These are
   `stepBwd`/`stepFwd` and `apxStepBwd`/`apxStepFwd`, the leaf rows. **This is
   the priced cost.** They are the `DefAt` against `DefBodyB` tie that
   `[LJ-1.346]` and the `LeafAgree` machinery measure separately, and which the
   KFacts wall prices at the class carrier. They are arguments, not holes.

**The unbounded approximation step is stronger.** Its `∀̇` is unbounded, so the
bounded frame's membership proofs (`cK`, `zK`) go unused in
`apxStep` (`Probe681.agda:116-124`). The frame transfer carries the strong
unbounded step to the weak bounded one directly.

## 4. HOW THIS REALIZES THE [LJ-1.684] RECIPE

The addendum to this brief fixed the shape. Point by point, this landing:

- **DOWN at one environment.** Built. One environment `γ`, one direction.
- **Do not inhabit `ApproxInK`.** Honored. No membership is proved; each is a
  hypothesis (`fK`, `domOut`, the leaf rows).
- **The corrected membership is `HierInK`, not `ApproxInK`.**
  `agents/tasks/LJ-1-532/Probe532.agda:274-277` states
  `HierInK = ... → ⟨ fst (hierL β hβ oβ) ∈ Lset α ⟩`. This is a fact about the
  **canonical** `hierL` approximation, not an arbitrary witness. `fK` is the
  witness-in-K slot the term needs; which specific fact fills it is the
  supplier's concern, and the canonical one is `HierInK`.
- **The inner frames are `[LJ-1.162]`'s `approx-up`/`step-up` and their
  reverses, plus `powK`.** `[LJ-1.162]` states these at
  `agents/tasks/LJ-1-162/ProbeLJ1162A.agda:211-216` (the `approx-up` and
  `step-up` hypotheses) and builds the **up** direction at
  `ProbeLJ1162A.agda:218-222` through `∃∈-up`. This landing is the **down**
  reverse: the same frame content, carried by the delivered `extAt→extAtB`.
  One honest note: I take the content transfer as two coarse rows
  (`stepBwd`/`stepFwd`, `apxStepBwd`/`apxStepFwd`) rather than `[LJ-1.162]`'s
  fine-grained `valK`/`powK`/`stepK` plus the `Leaf` rows. The coarse rows
  **subsume** that decomposition; the `powK` fact (the definable power in `K`)
  sits inside `stepBwd`/`stepFwd`. The frame transport is identical either way.
  If the next brief wants the cost split into `valK`/`powK`/`stepK` and the
  `Leaf` rows, that decomposition is already delivered in `[LJ-1.162]`.
- **UP is already `Graph.up`; do not rebuild it.** Honored. Only DOWN is built;
  `Graph.up` is not touched.

## 5. WHAT THE NEXT BRIEF NEEDS

- **To carry the unbounded adequacy onto the bounded graph.** Premise 4 of the
  brief: `Lset-defines` (`src/L/Hierarchy.lagda.md:646`) returns satisfaction of
  `LsetGraphAt`. Apply `bnd-vs-unbnd` with the three site facts: `fK`
  (witness-in-K), `domOut` (domain transfer), and the leaf rows. The leaf rows
  are the W3 cost; everything else is a delivered row.
- **For the `SameAsGraph` reverse.** `[LJ-1.678]` needs `powIter`, then this
  bridge, then packing. This bridge is the middle step, in the unbounded-to-
  bounded direction. If that route wants bounded-to-unbounded, `Graph.up`
  (delivered) is the other half.
- **The leaf rows are the open cost.** The one thing not discharged here is the
  `DefAt` against `DefBodyB` tie, and the witness/domain membership. Those are
  measured by the `LeafAgree` and KFacts work, not by this bridge.

## 6. GATES AND PROHIBITIONS

- One Agda process at a time, through `agents/tasks/LJ-1-681/runs/run.sh` with
  the 900 s wall cap. No `src/` change.
- Broken files are named `.agda.txt`, never `.agda`. The only `.agda` under the
  task home is `Probe681.agda`, which typechecks. The earlier floor attempt is
  `agents/tasks/LJ-1-681/runs/FLOOR.agda.txt`. A scratch import probe I used to
  settle a scope question is removed.
- `make check` is the gate before commit; I ran the individual checks the pane
  provides and the probe's own typecheck. I commit nothing and push nothing.

## 7. ARCHIVE USED

- `archive/dev/ORCHESTRATION.md` — **declined, not read.** Archived
  orchestration notes; this task is a single-term landing, not a program
  decision.
- `archive/dev/DD-archived.md` — **declined, not read.** Archived design
  decisions; no `D`-series ruling bears on building one delivered-row bridge.
- `archive/dev/PLAN-archived.md` — **declined, not read.** Archived planning;
  the standing plan lives in `dev/pod/`, read through its own channel.
- `archive/dev/STATUS-archived.md` — **declined, not read.** Archived status;
  the standing status is `dev/pod/screen.toml`.
- `archive/dev/TASKS-archived.md` — **declined, not read.** Archived task
  records; the live task records are under `agents/tasks/` and read directly.

## 8. LITERATURE USED

- `dev/literature/devlin-errata.md` — **declined, not read.** A do-not-repeat
  checklist for the rud route; this bridge uses no rud-route error class.
- `dev/literature/primary-sources.md` — **declined, not read.** Second-round
  source fetches for the rud route; the bridge is a term-level transport, not a
  sourced mathematical claim.
- `dev/literature/glossary-review-2026-08.md` — **declined, not read.** A
  glossary review; I add no `dev/glossary.toml` entry.
- `dev/literature/level-formula-slot-roles.md` — **declined, not read.**
  Thematically adjacent to the `Fin n` slot arithmetic I did, but I derived the
  slots directly from the `StepB`/`ApproxB`/`GraphB` definitions, not from this
  document.
- `dev/literature/BIBLIOGRAPHY.md` — **declined, not read.** The rud-route
  bibliography; this bridge cites no external source.

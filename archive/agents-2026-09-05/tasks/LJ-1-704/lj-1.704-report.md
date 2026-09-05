# LJ-1.704 report — `carved-is-hier` probe

**NO-GO (in-tree construction stop).** The obligation `carved ≡ fst (hierL
γ hγ oγ)` is **true in the model** and **not constructible in the tree**.
Nothing lands in `src/`. The probe is green; the obligation name is absent
on purpose; the review names the missing fact.

## Verdict, five sentences

1. The 698 frame bounds the recording at the **earliest** stage: the
   constants of `φᵣ` are `con γ` and `con (Lset γ)` (relativization bounds
   raw quantifiers at `Lset γ`; the recording is `∃̇∈ (con γ) …`), and both
   first appear at stage γ + 1 — so the frame's `σ = γ + 1`
   (`mkBoundedFo` → `mkBoundedTm (con c)` → `stage` = `theEarliest`,
   `L/Axioms/Separation.lagda.md:431-432`, `L/Stage.lagda.md:176-181`).
2. At that height `Lset (γ + 1) = 𝒟ₒ (Lset γ)` holds every element as a
   definable **subset** of `Lset γ` (`L/Definability.lagda.md:164-166,178`),
   so the A-bounded reading sees each pair element fully: `carved` is the
   table `{ ⟨x, Lset x⟩ | x ∈ γ }` exactly, in the model.
3. The junk shadow I started with — `w' = Lset x ∪ { Lset γ }`, with
   `w' ∩ Lset γ = Lset x` — only exists at stages σ ≥ γ + 3; it does not fit
   the frame. The equality is a property of the earliest stage.
4. In-tree, both inclusions wait on the same unlanded chain: the
   recording-satisfaction induction (693 `HierInK`, gated by 698
   `ThroughDoor` / 532 `ApproxInK` FALSE; 536 `HierBelow`).
5. Missing fact (review, 3 lines): recording-satisfaction `table-sat` —
   the A-bounded reading holds of `⟨x, Lset x⟩` by induction on the
   ordinal, the step consuming the entries below x.

## Deliverables

| Item | Location | Status |
|---|---|---|
| Frame + stage facts | `Probe704.agda:45-59` | **in-tree, compiles** |
| `gamma-below-sigma : ⟨ γ ∈ˢ Lset σ ⟩` | `Probe704.agda:51-52` | `hφ .fst` (698 bound as stage fact) |
| `ord-in-Lset` | `Probe704.agda:56-59` | one line on `Lset-cumul` + `ord∈Lset-suc` |
| Shadow statement (exact at σ = γ+1; junk at higher σ) | `Probe704.agda:62-85` | comments, model argument |
| Obligation `carved-is-hier` | `Probe704.agda:87-108` | **absent on purpose**, model-true |
| Missing fact `table-sat` | `Probe704.agda:97-100`, review | stated, unlanded |
| Review (NO-GO) | `review-of-carved-is-hier.md` | filed |

## Runs

| Run | Result | Notes |
|---|---|---|
| floor | `runs/floor-1.out` | GREEN (worktree import closure) |
| probe | `runs/p-4.out` | **GREEN, EXIT=0, 2.23 s, 601,423,872 bytes** |
| witness meter | `runs/meter-obligation.out` | 1 UNRESOLVED of 1, 2.25 s, `probe_red=False`; `missing exit=42`, `[NotInScope]` at the generated witness for `carved-is-hier` |

Command: `bash agents/tasks/LJ-1-704/runs/run.sh agents/tasks/LJ-1-704/Probe704.agda p-4 1800`
(GHCRTS wide caliber, set by the program, untouched).

## Key evidence

- `L/Ordinal/Stages.lagda.md:164-168` `Lset-cumul`; `:434` `ord∈Lset-suc` —
  the ordinal ladder facts the probe uses in `ord-in-Lset`.
- `L/Ordinal/Stages.lagda.md:179+` — the stage holds exactly the ordinals
  below it (both halves of the stage-ordinal theorem); pins the model
  argument.
- `L/Axioms/Basic.lagda.md:196` `Lset-suc` — `Lset (γ+1) = 𝒟ₒ (Lset γ)`.
- `L/Definability.lagda.md:164-166,178` — `Def A` is all of `A` plus its
  subsets; `defSet ⊤̇ ≡ A` — the no-junk lemma at the earliest stage.
- `L/Stage.lagda.md:176-181` — `stage = theEarliest`, the least bounding
  stage — why the frame sits on γ + 1.
- `FOL/Manipulation/Relativize.lagda.md:50,57,60` — atoms untouched; raw
  quantifiers bounded at the constant; the constants of `φᵣ`.
- `LJ-1-698/Probe698.agda:84-85,107-120` — the recording formula and the
  `Carved` frame the probe reuses.
- `LJ-1-693/Probe693.agda:59-62` `HierInK`; `Probe532.agda:206-209`
  `ApproxInK` FALSE — the unlanded chain the obligation waits on.

## Notes

- The junk-shadow framing from the brief's two-model reading was
  **correct at higher stages and wrong at the frame's**: the brief's "σ
  ≥ γ+1" leaves the height open, and the frame closes it at γ + 1.
  The review records the fragility: re-bounding `φᵣ` to a larger stage
  breaks the equality.
- Two compilation pits hit and solved this run, both world-discipline:
  `mem-ord` takes the ordinality first with an implicit `A` that does not
  solve through the opaque hProp (explicit `{γ}` required); and the
  probe's stage facts must be stated in the `𝒮ᵥ` world (`∈ˢ` over `V`)
  to line up with `L.Ordinal.Stages`' own combinators.

## ARCHIVE USED

Every file below was opened for this return. Each bullet quotes the line its
citation names and records the bearing on this NO-GO.

- `archive/dev/ORCHESTRATION.md:1` "the orchestrator's operating rules": read. It governs how work is dispatched, audited and landed. This return adjudicates a construction stop inside one probe, and no dispatch rule in it bears. Declined.
- `archive/dev/DD-archived.md:3` "Never rewritten, never deleted": read. The frozen DD rows are superseded by `dev/pod/rulings.toml`, and this return cites none of them. Declined.
- `archive/dev/PLAN-archived.md:4` "the construction registry as it stood on archival day": read. The live state is `dev/pod/screen.toml` and `dev/pod/queue.toml`; the archived registry adds nothing to this stop. Declined.
- `archive/dev/TASKS-archived.md:8` "Nothing here is a live task": read. The retired `L3.32-T` index predates the `LJ-1` series this task belongs to. Declined.
- `archive/dev/STATUS-archived.md:1` "the goal table of the internalization route": read. That route left the tree on 2026-08-09, and no claim here touches it. Declined.
- `archive/dev/measurements/README.md:3` "the raw output of a timing run": read. This return cites its run outputs directly from `agents/tasks/LJ-1-704/runs/`, so no archived measurement record is needed. Declined.
- `archive/dev/README.md:3` "Moved here 2026-08-09 by the owner's instruction": read. The directory holds the retired internalization route's records, and no file of that route bears on `carved-is-hier`. Declined.

## LITERATURE USED

Every file below was opened for this return. Each bullet quotes the line its
citation names and records the bearing on this NO-GO.

- `dev/literature/BIBLIOGRAPHY.md:3` "Every source from the raw sweep": read. It indexes the rud route's sources; this NO-GO rests on in-tree files only. Declined.
- `dev/literature/devlin-errata.md:1` "documented error classes": read. The checklist covers external accounts of constructibility, and no external account is in question here. Declined.
- `dev/literature/primary-sources.md:3` "Second fetch round": read. The fetched Jensen, Devlin and Jech texts back external claims; this return asserts none beyond the tree's own model argument. Declined.
- `dev/literature/level-formula-slot-roles.md:1` "arity, what it binds, what stays free": read. The slot roles of the authors' level formulas do not touch the in-tree pair-graph recording under review. Declined.
- `dev/literature/glossary-review-2026-08.md:3` "Review of every entry in": read. This return adds no term to `dev/glossary.toml`, so the glossary review is out of scope here. Declined.

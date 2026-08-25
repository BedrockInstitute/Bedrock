# [LJ-1.636-split] How far does the bill get at ambient omega

**GO.** `bill-at-omega` is built and green. It is one term at
`agents/tasks/LJ-1-636-SPLIT/ProbeSplit.agda:147-159`. It has no hole and
no postulate. The file declares `--safe`.

Three green runs of the final file: `runs/final-2.out` at 7.60 s,
`runs/final-3.out` at 3.19 s (cached interface), and `runs/final-4.out` at
7.92 s (fresh elaboration, warm dependencies). All `EXIT=0`, under the
caliber the program set on this pane (`-A64m -I0 -M2g`).

The pod's own meter agrees:
`witness.py agents/tasks/LJ-1-636-SPLIT/ProbeSplit.agda::bill-at-omega`
gives `pass exit=0 4.31s`, `0 UNRESOLVED of 1, probe_red=False`.

**There is no heap wall.** No wall occurred at any point in this dispatch.

Nothing landed in `src/`. `git status --porcelain` shows only
`?? agents/tasks/LJ-1-636-SPLIT/`.

## 1. THE ANSWER

**At ambient `ω` the square law costs nothing, and the free ride stops
immediately after it.**

`Devlin55.BoundedSubsetAt` has SEVENTEEN parameters
(`src/L/BoundedSubset.lagda.md:1385-1395`). Setting the ambient to `ω`
removes FOUR of them:

| # | Parameter | How it goes | Basis |
|---|---|---|---|
| 1 | `α` | FIXED to `ω` | this is the instantiation itself |
| 2 | `ordα : IsOrd α` | DISCHARGED by `ω-ord` | `src/L/Ordinal.lagda.md:263` |
| 3 | `α∉ω : ⟨ α ∈ˢ ω ⟩ → ⊥` | DISCHARGED by `∈-irrefl ω` | `src/V/Hierarchy.lagda.md:155` |
| 4 | `sq` | DISCHARGED by `param-at-ω` | `[LJ-1.636]`, re-derived at `ProbeSplit.agda:86-93` |

**THIRTEEN survive**, and `Co`'s `levelIn` and `cover` survive with them.
So the bill at ambient `ω` costs FIFTEEN hypotheses. The conclusion is the
chapter's own headline, unweakened: `⟨ x ∈ˢ Lset κ ⟩`
(`src/L/BoundedSubset.lagda.md:1737`).

The thirteen survivors are `κ`, `ordκ`, `cardκ`, `κ∉ω`, `ω∈κ`, `x`,
`x⊆Lω`, `absorbs`, `lam`, `ordλ`, `ω∈λ`, `succλ` and `x∈Lλ`. They are the
explicit telescope of `bill-at-omega` at `ProbeSplit.agda:148-154`.

## 2. W3, THE WIDEST UNMEASURED TERM: BOTH SURVIVE

The brief named `levelIn` and `cover` and asked whether they survive
instantiation at `ω`. **They both survive, and neither is even touched.**

The ambient reaches them only through `UnionKit.X = Lset α ∪ ⁅ x ⁆s`
(`src/L/BoundedSubset.lagda.md:1149-1150`). At `α := ω` that becomes
`Lset ω ∪ ⁅ x ⁆s`. `UnionKit` and `HullStage` take no `sq` parameter, so
the square law never reaches the hull, the collapse, `HS.M` or `HS.C.πX`.
The two hypotheses come through with their shape unchanged and their
subject specialised. They are `At-ω.LevelIn` and `At-ω.Cover` at
`ProbeSplit.agda:126-131`.

**This confirms a finding an earlier dispatch already made, at a new
ambient.** `archive/dev/LJ-dispatch-index.md:195` records `[LJ-1.119]` as
"the stop is levelIn and cover". That stop does not move at `ω`.

## 3. THE MEASUREMENT THAT MATTERS: THE FRAME IS THE WHOLE PRICE

I measured the floor before the proof, as the standing clause orders.
`runs/Floor.agda` instantiates `BoundedSubsetAt` at `ω` and names NO
consequence. Both numbers below are fresh elaborations with warm
dependencies, taken after I deleted the interface file:

| What | Wall | Peak RSS | Run |
|---|---|---|---|
| FLOOR: the frame alone, no conclusion | 7.48 s | 1.6525 GB | `runs/floor-4.out` |
| FULL: the frame plus `bill-at-omega` | 7.92 s | 1.6536 GB | `runs/final-4.out` |
| DELTA: the obligation's own cost | 0.44 s | 1.1 MB | |

**The obligation costs 6 percent of its own frame.** Instantiating this
chapter at any ambient is the expense; stating and proving the at-`ω`
consequence on top of it is nearly free.

**A RESOURCE WARNING FOR THE NEXT BRIEF.** The frame alone peaks at
1.65 GB against the 2 GB wide caliber. The margin is about 350 MB, and it
belongs to the FRAME, not to any term written inside it. A later task that
instantiates this chapter and then builds a real term inside it has very
little room. `[LJ-1.636]` already met one wall in this chapter's
neighbourhood and had to route around it
(`agents/tasks/LJ-1-636/lj-1.636-report.md:9-13`, sibling worktree). I
recommend the heavy tier for any follow-on that proves inside this frame.

Caching note, so the numbers are not misread: a run whose interface is
current costs about 3.2 s and elaborates nothing. `runs/floor-2.out`,
`runs/floor-3.out` and `runs/final-3.out` are such runs. `touch` does not
force a re-check, because Agda keys on content. Only deleting
`_build/2.8.0/agda/.../<name>.agdai` does.

## 4. THE BRIEF'S PREMISE 4 IS RIGHT, BUT NOT FOR THE OBVIOUS REASON

Premise 4 says this task attacks `[LJ-1.635]`'s at-`ω` half. **It does,
and the reason is worth writing down, because the chapter binds TWO
ordinals and only one of them is the `ω` that premise means.**

`BoundedSubsetAt` binds the cardinal `κ` and the ambient `α`, with
`α ∈ κ`. The bill reads `x ⊆ Lset α` (`:1391`) and returns `x ∈ Lset κ`
(`:1737`). So the ordinal whose power set the bill BOUNDS is the AMBIENT.

`[LJ-1.635]`'s at-`ω` half is `Concl zf ωʟ`, and `Concl zf κ` is
`2^κ = κ⁺` (`agents/tasks/LJ-1-635/Probe635.agda:73-76`). Its `ω` is the
ordinal being bounded. **That is this chapter's ambient, not this
chapter's `κ`.** At ambient `ω` the module's `κ` is `ω⁺`.

The literature says the same thing independently.
`dev/literature/devlin-II5.md:164` reads "The application of 5.5 in 5.6 is
at the cardinal κ⁺ with α = κ: every".

**And the other reading is impossible, not merely wrong.**
`no-ambient-at-cardinal-ω` (`ProbeSplit.agda:184-189`) proves that if the
module's own `κ` were `ω`, the telescope would admit no ambient at all,
because `α ∈ κ` and `α ∉ ω` collide. The at-`ω` half can enter this
chapter through the ambient and nowhere else.

## 5. WHAT I COULD NOT CLOSE, AND WHAT IT IS WORTH

**`absorbs` is the next real debt, and it is NOT free at `ω`.**

At ambient `ω` the hypothesis reads
`⟪ Lset ω ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset ω ⟫` (`ProbeSplit.agda:151`). This is
Devlin's counting step 5.4, which asks for a hull of size `|L_α|`
(`dev/literature/devlin-II5.md:152-154`). At `α = ω` it is the statement
that `L_ω` absorbs one more element, which is the Dedekind infinity of
`L_ω`.

I did NOT build it, and I say why rather than leave it silent:

1. The brief ordered "Instantiate. Do not build a square law", and this is
   a new construction, not an instantiation.
2. The tree's existing `absorbs` does NOT discharge it.
   `src/L/Absorption.lagda.md:635` has the type
   `⟪ sucV (fst γ) ⟫ ↪ ⟪ fst γ ⟫`. That is ordinal successor absorption, a
   different shape from the hull union above. **A grep hit on the name
   `absorbs` is not a hit on the obligation.**
3. The pieces for a real attempt do exist. `numeral∈limit` puts every
   numeral in `Lset ω` (`src/L/Choice/Name.lagda.md:120`), which is the
   countable family the shift needs, and `ShiftGraph`
   (`src/L/Absorption.lagda.md:539-640`) is the shift pattern already
   written once for ordinals.

`archive/dev/LJ-dispatch-index.md:195` records that `absorbs-subset` was
once "restricted the way sq was restricted". A dispatch that wants
`absorbs` at `ω` should read that row first.

**A price for the next brief, stated as an estimate and marked as one:**
the frame is already paid and measured at 7.48 s, the shift pattern
exists, and the decomposition of `z ∈ Lset ω ∪ ⁅ x ⁆s` needs LEM at
`ℓ-suc ℓ`, which the chapter already carries. I estimate 80 to 150 lines.
**This is an estimate and not a measurement. I did not build it.**

## 6. A PROCESS FINDING: THE BRIEF SAID "IMPORT IT" AND I COULD NOT

The brief's premise 1 gives the basis
`agents/tasks/LJ-1-636/Probe636.agda:391` and instructs
"`param-at-ω` is delivered and you import it".

**That path does not exist on this branch.** `agents/tasks/LJ-1-636/` is
absent from my worktree, from `git ls-files`, and from `git log --all`.
`[LJ-1.636]` was still LIVE while I ran: it holds its own worktree at
`/Users/alsg/Agentic/Bedrock/.pod-state/worktrees/LJ-1-636` at commit
`8518b937`, and my worktree is at `ad1e1583`.

I did what my standing clause orders for a predecessor hypothesis. I
opened that predecessor's probe and its report in the sibling worktree,
took the type from the probe that typechecked and the verdict from the
report, and confirmed the verdict is **GO** with `param-at-ω` built from
`squareω` alone, nothing postulated and nothing truncated.

Then I RE-DERIVED the two terms rather than importing them, and I say so
in the file (`ProbeSplit.agda:82-93`). They are `Probe636.agda:377-381`
and `:391-392`, verbatim up to binder names. I checked both against the
sibling worktree line by line.

**This is worth a ruling, and I do not make one.** A brief that names a
predecessor path can be built before that predecessor's work reaches the
branch. The re-derivation cost me two small terms here. It would not be
cheap for a large predecessor deliverable, and a coder who did not check
would either fail to find the file or, worse, invent a type for it.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md` **READ AND USED.**
  `archive/dev/LJ-dispatch-index.md:195` reads
  "| LJ-1.119 | Restrict absorbs-subset the way sq was restricted | ENTERED, make check PASSES | Devlin55 now has NO parameter. BoundedSubsetAt is entered at the site; the stop is levelIn and cover |".
  This is cited in sections 2 and 5. It confirms `levelIn` and `cover` as
  the standing stop and it records the earlier `absorbs-subset` work.
- `archive/dev/JOURNAL-archived.md` **NOT READ, declined.** 4280 lines,
  and the dispatch index above already carries the per-task rows for this
  chapter in a form I can cite by line.
- `archive/dev/JOURNAL.md` **NOT READ, declined.** Same reason as the
  archived journal. It is history, and the Boundary sends me to the live
  files for the standing state.
- `dev/ARCHIVE.md` **NOT READ, declined.** It records retired MODULES.
  Nothing retired here: `L.BoundedSubset` is live and I instantiated it.
- `archive/dev/DECISIONS-archived.md` **NOT READ, declined.** 61 lines of
  the archived `D<n>` series, which is not a rule in force. No mathematical
  content bears on this obligation.

## LITERATURE USED

- `dev/literature/devlin-II5.md` **READ AND USED.**
  `dev/literature/devlin-II5.md:164` reads
  "The application of 5.5 in 5.6 is at the cardinal κ⁺ with α = κ: every".
  This is the independent confirmation of section 4. I also used
  `:147-148` for the 5.5 statement and `:152-154` for the 5.4 counting
  step behind `absorbs`.
- `dev/literature/truncation-and-selection.md` **NOT READ, declined.**
  Nothing in this obligation is truncated. `param-at-ω` is untruncated,
  and `Cover`'s `∥ ∥₁` was carried through unchanged from the chapter.
- `dev/literature/digest.md` **NOT READ, declined.** A digest over the
  corpus. I had the primary note for II.5 above and cited it directly.
- `dev/literature/terms-2026-08.md` **NOT READ, declined.** Terminology
  provenance. I added no glossary entry and named no new term.
- `dev/literature/geology.md` **NOT READ, declined.** Set-theoretic
  geology is not this chapter.

## 7. FILES

- `agents/tasks/LJ-1-636-SPLIT/ProbeSplit.agda` (185 lines) the obligation
- `agents/tasks/LJ-1-636-SPLIT/runs/Floor.agda` the floor, section 3
- `agents/tasks/LJ-1-636-SPLIT/runs/run.sh` copied from `[LJ-1.636]`
- `agents/tasks/LJ-1-636-SPLIT/runs/floor-1.out` cold, built `L.BoundedSubset`
- `agents/tasks/LJ-1-636-SPLIT/runs/floor-2.out`, `floor-3.out` cached loads
- `agents/tasks/LJ-1-636-SPLIT/runs/floor-4.out` **the floor, 7.48 s**
- `agents/tasks/LJ-1-636-SPLIT/runs/final-1.out` green, pre-correction file
- `agents/tasks/LJ-1-636-SPLIT/runs/final-2.out` green, 7.60 s
- `agents/tasks/LJ-1-636-SPLIT/runs/final-3.out` cached load
- `agents/tasks/LJ-1-636-SPLIT/runs/final-4.out` **the price, 7.92 s**

`scripts/gate/check-probes.py`, `scripts/gate/lint-agda.py` and
`scripts/gate/check-fences.py` are all clean.

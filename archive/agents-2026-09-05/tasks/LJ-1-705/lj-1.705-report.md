# LJ-1.705 report: the bounding stage lies in the bridge's alpha

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.705
obligation: agents/tasks/LJ-1-705/Probe705.agda::bound-in-alpha
verdict: **NO-GO. `bound-in-alpha` is not inhabited.** The statement
is not shown false. `mkBoundedFo` is total. Its stage is the
`bound2`-tree of the stages of the formula's constants. Those
constants are `γ`, `Lset γ`, and numerals. The membership
`fst (bound-of γ oγ hγ) ∈ α` is not proved.
`agents/tasks/LJ-1-705/review-of-bound-in-alpha.md` states the stop.

The delivered probe is green (`runs/p-final.out`, EXIT=0, 2.59 s,
602,472,448 bytes). The witness meter is 1 UNRESOLVED of 1,
`probe_red=False` (`runs/meter-obligation.out`, `missing exit=42
2.64 s`, `[NotInScope]` at the generated witness for
`bound-in-alpha`).

**READ THESE FIVE SENTENCES BEFORE YOU QUEUE ANYTHING.**

1. **THE TARGET IS NOT KILLED BY `ω`.** `arityNumAtL` names `ωʟ`
   (`src/L/Coding/CodeSet.lagda.md:187`). `isCodeAt` uses
   `keyArityAtL`, not `arityNumAtL`
   (`src/L/Coding/Powerset.lagda.md:298`). This formula does not
   carry `ω` as a constant. A bound that escaped at `α = ω` would
   have been this dispatch's stop. It is not that stop.
2. **`mkBoundedFo` IS THE `bound2`-TREE OF CONSTANT STAGES.**
   `mkBoundedTm (con c)` is `stage` of that constant
   (`src/L/Axioms/Separation.lagda.md:432-433`). A branching node
   merges by `bound2` (`src/L/Ordinal.lagda.md:185-187`). Relativize
   adds `LsetS γ` at each unbounded quantifier
   (`src/FOL/Manipulation/Relativize.lagda.md:57-58`).
3. **`stage(γ)` AND `stage(Lset γ)` SIT AT OR BELOW `sucV γ`.**
   `ord∈Lset-suc` (`src/L/Ordinal/Stages.lagda.md:434-435`).
   `Lset γ ∈ 𝒟ₒ (Lset γ)` by `𝒟ₒ-intro` with `⊤̇`
   (`src/L/Axioms/Basic.lagda.md:157-158`), and `Lset-suc` (`:195`)
   identifies that with `Lset (sucV γ)`. An `IsLimit` that contains
   `γ` contains `sucV γ`.
4. **THE UNPAID LEMMA IS `bound2-in-limit`.** A limit that contains
   `σ₁` and `σ₂` must contain `bound2 σ₁ σ₂`. Under the 698 cone
   that lemma heap-walled (`runs/p-14.out`). In a trimmed frame,
   `sett (Lift Bool)` did not convert to `⁅ sucV σ₁ , sucV σ₂ ⁆`
   (`runs/p-21.out:5-12`), and `bound2`'s internal `f` did not
   convert to a local copy (`runs/p-26.out:5-8`).
5. **DO NOT RE-CHECK THAT `relativize PairGraphAt` IS `Δ₀`.** Do
   not re-run `mkBoundedFo` as the obligation. Do not inhabit
   `ThroughDoor`. Do not inhabit `ApproxInK`.

Written as a skeleton before any Agda beyond the predecessor read
and filled as each answer landed (C-22). No commit, no push. I wrote
only inside `agents/tasks/LJ-1-705/`. Agda ran under the caliber the
program set on this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier,
ONE Agda process at a time. I did not set `GHCRTS`. Nothing is
postulated, the delivered probe carries `--safe` and no hole, and
nothing lands in `src/`. The probe is a raw `.agda` file, so it
carries no fence, counts 0 in-fence lines, and the ratio bar cannot
fire on it.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict. W4 does not apply: no module is
retired.

**THE FLOOR ROW IS A COLD-CACHE NUMBER.** `runs/floor-1.out` loaded
`Probe693`, `Probe520` and `Probe698` (`runs/floor-1.out:5-7`).
`runs/p-final.out` is a later green run of the same delivered file
on a warm interface cache. No number here is reported as a price
under any caliber but the pane's.

**A HEAP WALL WAS MET AND RESTRUCTURED.** `runs/p-14.out` terminated
abnormally at 77.56 s and 1,826,455,552 bytes, peak footprint
2,012,579,856 bytes, against the 2,147,483,648-byte wide cap. The
shape was split, the 698 cone was stripped, and `bound2-in-limit`
was tested under the same cap (`runs/p-19.out` to `runs/p-27.out`).
The wall is not reported as a finding about the term. The finding
is the conversion gap at `bound2`.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

The standing coder clause says: take the type from the probe that
typechecked, and the verdict from the report. If the report is NO-GO,
or names the statement FALSE, do not inhabit that type.

| piece | type | site | verdict |
|---|---|---|---|
| `bound-of` | `Σ[ σ ∈ V ℓ ] (IsOrd σ × BoundedFo (Below′ σ) (relativize (LsetS γ oγ) (recordedFo (γ , hγ))))` | `Probe698.agda:97-101` | GO, total. Taken as the bounding stage. |
| `empty-in-limit` | `IsLimit α → ⟨ ∅ ∈ α ⟩` | `Probe698.agda:184-185` | GO. Zero case of a stage in the bound. |
| `Carved.carved-door` | `Door (Lset σ) carved` at `σ = fst (bound-of γ …)` | `Probe698.agda:128-129` | GO as a door on an unidentified set. Not rebuilt. |
| `through-door` / `ThroughDoor` | some `δ ∈ α` and `Door (Lset δ) (hierL β)` | `Probe693.agda:135-139` | TYPE, green; not inhabited. 698 is NO-GO here. Not inhabited here. |
| `ApproxInK` | every `ApproxAt` witness lies in `K` | `Probe532.agda:108-117` | **FALSE** (`:206-209`). Not inhabited. |

The 698 report is NO-GO at `through-door`, not at `bound-of`. The
second named miss is `fst (bound-of γ oγ hγ) ∈ α`
(`lj-1.698-report.md:42`). I take that unpaid row. I do not inhabit
`ThroughDoor`. I do not inhabit `ApproxInK`. I do not rebuild
`Carved`. I do not rebuild `Pin.down`. I do not rebuild `adequacy-bnd`.

## 2. D-10, BEFORE THE PROOF IS PRICED

The recorded residue is `⟨ fst (bound-of γ oγ hγ) ∈ α ⟩` for `IsLimit α`
and `γ ∈ α`.

**THE TARGET IS NOT SHOWN FALSE.** Devlin 2.6(ii) is the sequence
`(L_δ | δ ≤ γ) ∈ L_α` for `γ < α` at a limit
(`dev/literature/devlin-II5.md:221-222`). Slot roles name the same
sequence (`dev/literature/level-formula-slot-roles.md:24`). The
formula's constants are `γ`, `Lset γ`, and numerals from `tagAtL`
(`src/L/Coding/Model.lagda.md:586`). `ω` is not among them. A finite
nest of successors of `sucV γ` lies in every `IsLimit` that contains
`γ`. I did not build a term of the negation.

**THE TARGET IS NOT INHABITED.** The unpaid lemma is that `bound2` of
two members of a limit is again a member. That lemma did not close.

C-42 does not fire. This is not a refutation of `bound-in-alpha`. No
false shape was counted.

D-26: `mkBoundedFo` uses the formula's syntax. A stage built as a
definable power carries no generation data of its members. The
bounding stage is read from the constants, not from the table.

P-l is observed: types name `Lset α` and ordinals, which are opaque
(`src/L/Constructible.lagda.md:221-223`). They do not name
`sucV (sucV (sucV _))`.

## 3. THE FLOOR, MEASURED BEFORE ANY PROOF

Coder clause, owner 2026-08-23: price the frame before the term. A
hole is not available under `--safe`. The floor is the obligation
TYPE, formed, in the trimmed frame (`runs/floor-1.out`).

**THE FRAME COSTS 28.12 s AND 797 MB, AND IT DOES NOT WALL.**
`runs/floor-1.out`: exit 0 at 28.12 s, peak 797,474,816 bytes. **The
obligation TYPE is well-formed.** The cone is `Probe693`, `Probe520`
and `Probe698` (`runs/floor-1.out:5-7`).

| run | file | exit | wall s | peak bytes |
|---|---|---:|---:|---:|
| `floor-1` | type only, `bound-of` imported | 0 | 28.12 | 797,474,816 |
| `p-14` | cone plus `bound2-in-limit` and syntax fillers | 1 | 77.56 | 1,826,455,552 |
| `p-21` | trimmed `bound2-in-limit`, pairing vs sett | 42 | 1.49 | 282,050,560 |
| `p-26` | local `f` vs `L.Ordinal.f` | 42 | 1.32 | 281,853,952 |
| `p-final` | delivered probe | 0 | 2.59 | 602,472,448 |
| meter | `witness.py --brief` | 1 | 2.73 | 603,013,120 |

The meter row is `missing`, `[NotInScope]` for `bound-in-alpha`.
That is the designed absence.

## 4. W3, THE WIDEST UNMEASURED TERM

The brief names it: whether `mkBoundedFo`'s stage is bounded by the
ordinal at all, or only by the formula's syntax. Estimate 60 to 150
lines, basis `src/L/Axioms/Separation.lagda.md:449`.

**`mkBoundedFo`'S STAGE IS THE `bound2`-TREE OF THE STAGES OF THE
FORMULA'S CONSTANTS. IT IS NOT A SYNTAX-ONLY BOUND, AND IT IS NOT
SHOWN TO LIE IN `α`.**

- The constants of `relativize (LsetS γ oγ) (recordedFo (γ , hγ))`
  are `γ`, `Lset γ`, and numerals. `ω` is not among them.
- `stage(γ)` and `stage(Lset γ)` sit at or below `sucV γ`. An
  `IsLimit` that contains `γ` contains `sucV γ`.
- Numerals sit in every `IsLimit`, from `∅` by successor-closure.
- The merge `bound2 σ₁ σ₂ = ⋃ (sett (Lift Bool) (sucV ∘ f))` is the
  unpaid step. It did not convert to `⋃ ⁅ sucV σ₁ , sucV σ₂ ⁆`.

The estimate was for inhabiting the membership. The delivered probe
is 57 lines, 14 non-blank and not a comment. The new mathematics is
the type and the D-10 census. The body of `bound-in-alpha` is not
there.

**WHAT THIS TERM IS NOT.** It is not `ThroughDoor`. It is not
`HierInK`. It is not another `Δ₀` ascription. It is not a proof
that the bound escapes.

## 5. W2 ANSWER

W2: write the mathematics once at a generic carrier and instantiate it.

The generic carrier is a formula and a limit. `bound2-in-limit` is
the merge at any two ordinals in the limit. Instantiation at
`relativize (LsetS γ oγ) (recordedFo (γ , hγ))` is the obligation.
The generic lemma did not close, so the instantiation was not
reached. A deadline does not apply. There is no conflict with a
fixed form. Do not fund a second copy at `n = 0`.

## 6. WHAT THE SHAPE RESISTED

- **What it cost.** Floor 28.12 s, 797 MB, EXIT=0. Delivered
  probe 2.59 s, 602 MB. Meter 2.73 s, 603 MB. File 57 lines, 14
  code. Heap wall at the first `bound2-in-limit` shape, then
  restructured.
- **What the shape resisted.** `sett (Lift Bool) (sucV ∘ f)` did
  not convert to `⁅ sucV σ₁ , sucV σ₂ ⁆`. `bound2`'s internal `f`
  did not convert to a local copy of the same clauses.
- **What I had to weaken.** Nothing of the obligation type. I did
  not inhabit `fst (bound-of γ) ∈ α` by a postulated bound. I did
  not take `HierBelowAll` as a hypothesis and name it
  `bound-in-alpha`.
- **What I could not close.** `bound-in-alpha` itself.
  `bound2-in-limit`. The equation
  `bound2 σ₁ σ₂ o₁ o₂ .fst ≡ ⋃ ⁅ sucV σ₁ , sucV σ₂ ⁆`.

## 7. WHAT THE NEXT BRIEF NEEDS

- **If the consumer is still `bound-in-alpha`.** Split the unpaid
  lemma. First: `⋃ ⁅ sucV σ₁ , sucV σ₂ ⁆ ∈ α` for `IsLimit α` and
  `σᵢ ∈ α`, by `pairing-ax` (`src/L/Constructible.lagda.md:113`).
  Second: `bound2 σ₁ σ₂ o₁ o₂ .fst ≡ ⋃ ⁅ sucV σ₁ , sucV σ₂ ⁆`.
  Do not re-load the 698 cone into the first of those two. Do not
  re-check that `relativize PairGraphAt` is `Δ₀`.
- **If the consumer is `ThroughDoor` through 𝒟ₒ-intro.** Take
  `empty-door` (`Probe698.agda:173-177`) for the zero case. Take
  `recordedΔ₀` (`:87-88`) and `bound-of` (`:97-101`) and
  `Carved.carved-door` (`:128-129`) as the door on an unidentified
  set. The remaining rows are still
  `Carved.carved ≡ fst (hierL γ hγ oγ)` and
  `⟨ fst (bound-of γ oγ hγ) ∈ α ⟩`. This file did not pay the
  second row.
- **If the consumer is 681's bridge.** Take DOWN at one environment
  from `Pin.down` (`Probe688.agda:156-159`). Take `adequacy-bnd`
  (`Probe684.agda:77-83`). Do not rebuild them. Do not inhabit
  `ApproxInK`. Take `HierInK` as a HYPOTHESIS.
- **Do not re-dispatch this measurement.** `ω` is not a constant of
  this formula. The bound is the `bound2`-tree of `stage(γ)`,
  `stage(Lset γ)` and numeral stages. The merge is the unpaid step.
- This task changed nothing in `src/`.

## 8. PRICE

| item | measured |
|---|---|
| floor (type only, cold cone) | 28.12 s, 797,474,816 bytes, EXIT=0 |
| first wall (`p-14`) | 77.56 s, 1,826,455,552 bytes, EXIT=1 |
| pairing vs sett (`p-21`) | 1.49 s, 282,050,560 bytes, EXIT=42 |
| local `f` vs `L.Ordinal.f` (`p-26`) | 1.32 s, 281,853,952 bytes, EXIT=42 |
| delivered probe | 2.59 s, 602,472,448 bytes, EXIT=0 |
| witness meter | 2.73 s, 603,013,120 bytes, 1 UNRESOLVED of 1, `probe_red=False` |
| file lines / code lines | 57 / 14 |
| brief estimate | 60 to 150 lines |
| in-fence lines | 0 (raw `.agda`) |
| caliber | `-A64m -I0 -M2g`, never set here |
| heap wall | `p-14`, then restructured; not the finding |
| `src/` edits | none |

The estimate was for inhabiting the membership. The file is 57 lines
because it carries the type and the D-10 census. It does not carry
a body for `bound-in-alpha`.

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md:1` `# ORCHESTRATION: the orchestrator's operating rules`. Declined: not used. This dispatch measures a live `mkBoundedFo` stage against a live limit, not archived dispatch rules.
- `archive/dev/DD-archived.md:1` `# THE `DD` RULING SERIES, archived in full 2026-08-18`. Declined: not used. The live W2 home is the coder slot file, not this archive.
- `archive/dev/PLAN-archived.md:1` `# ARCHIVED 2026-08-20`. Declined: not used.
- `archive/dev/STATUS-archived.md:1` `# STATUS-archived: the goal table of the internalization route`. Declined: not used.
- `archive/dev/TASKS-archived.md:1` `# Archived task index: the `L3.32-T` series`. Declined: not used.

## LITERATURE USED

- `dev/literature/level-formula-slot-roles.md:24` `| 2 | Devlin 2.6 | `G(f,α) = ∃w[K(w, ⋃ran(f)) ∧ F(w,f,α)]`; `G` says `f = (L_γ ∣ γ ≤ α)` | 2 | `w`, ONE bound, determined | `f`, `α` | SEQUENCE, ORDINAL | `_build/literature/dev2.txt:655-659` |`. Read. The unpaid row is the bounding stage of that sequence's formula, asked to lie in the bridge's `α`.
- `dev/literature/level-formula-slot-roles.md:35` `### 2.1 The free pair is the VALUE and the ORDINAL, in every source`. Read. The bound is a stage slot, not a free pair.
- `dev/literature/devlin-II5.md:221` `live inside L_α; that is 2.6(ii), the sequence (L_δ | δ ≤ γ) ∈ L_α for`. Read. Classically the table is in `L_α`; this task asks only whether the formula's bounding stage is in `α`.
- `dev/literature/glossary-review-2026-08.md:1` `# Glossary review: the 119 pre-protocol entries`. Declined: not used.
- `dev/literature/devlin-errata.md:1` `# Devlin errata: documented error classes (do-not-repeat checklist)`. Declined: not used.
- `dev/literature/primary-sources.md:1` `# Primary sources, second round: Jensen manuscript, Devlin, Jech`. Declined: not used. Slot roles and Devlin II.5 already cite those sources.
- `dev/literature/formalizations-landscape.md:1` `# Formalization landscape sweep: L, V=L, condensation, AC-in-L, GCH-in-L, rud (OPEN item 7)`. Declined: not used. The term is a live membership of a bounding stage, not a landscape comparison.

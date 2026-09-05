# LJ-1.196 report: `DefAt`'s ambient reading, 84 lines or a chapter

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. Written incrementally
(C-22); this file was created before the first Agda line. One agda process,
`GHCRTS="-A64m -I0 -M8g"`, cap never raised. No master edited, no commit, no
push. Every negative is marked **MEASURED** or **INFERRED**.

## 0. LEAD

**NO-GO.**

The ambient port is **not 84 lines**. It is the 84-line free part of
`[LJ-1.184]` section 5.2 **plus a chapter**: an outer-carrier port of the
satisfaction coding for `DefAt-in`/`DefAt-out`. The chapter is anchored, not
priced (P-l): the class-carrier satisfaction coding is
`src/L/Coding/Model.lagda.md` **1,288** in-fence lines and
`src/L/Coding/Powerset.lagda.md` **395** in-fence lines (both MEASURED by
`[LJ-1.184]` section 5.3). I do not transfer that number to the outer instance;
I state it as the comparable the chapter is the twin of.

**The two extra hypotheses are NOT enough.** The miniature's own plan fails at
its middle step, before the constructibility question is even reached: `abs₀`
cannot be applied to `DefAt` because `DefAt` is not Δ₀.

## 1. THE MINIATURE, AND WHICH HYPOTHESES CLOSED IT OR FAILED

### 1.1 The plan the miniature prescribes, verified step by step

The plan is three tools composed:

1. `⊨-map` (`src/FOL/Manipulation/Relabelling.lagda.md:154-155`): the ambient
   reading of the pushed formula is the class OUTER reading.
2. `abs₀` (`src/FOL/Absoluteness.lagda.md:122-123`): outer to inner.
3. `DefAt-stage` (`src/L/Coding/Powerset.lagda.md:720-727`): inner reading at a
   stage to the equation.

**Step 1 is GREEN, MEASURED in `ProbeLJ1196A.agda:91-95`**:
`ambientPushed≡outer : ambient γ (mapFo emb (CP.DefAt u w)) ≡ (map fst γ) AbsL.⊨ᵛ (CP.DefAt u w)`,
one application of `⊨-map` at `f = emb`, `ι = fst`, because `fst ∘ emb = fst`
definitionally. The dead agent's first step is correct.

**Step 2 is the wall, MEASURED.** `abs₀` has type
`Δ₀ φ → (δ : SM ^ n) → (δ ⊨ᵐ φ) ≡ ((map fst δ) ⊨ᵛ φ)`
(`src/FOL/Absoluteness.lagda.md:122-123`). It needs a `Δ₀ (DefAt u w)` witness.

`DefAt u w = extAt u (∃̇ (∃̇ (DefBody w)))`
(`src/L/Coding/Powerset.lagda.md:442-443`), and
`extAt y φ = ∀̇ (...) ∧̇ ∀̇ (...)`
(`src/L/Coding/Model.lagda.md:662-663`): two **unbounded** universals. `Δ₀`
has constructors for bounded quantifiers only — `δ-∀∈`, `δ-∃∈` — and none for
`∀̇` or `∃̇` (`src/FOL/LevyHierarchy.lagda.md:42-52`, "absence is the
classification"). **So `Δ₀ (DefAt u w)` is uninhabited, and `abs₀` cannot be
applied to `DefAt` at all.**

The probe measured it directly: with the hole
`Δ₀-DefAt u w = {! !}` in place, Agda reports exactly ONE unsolved constraint,
of type `Δ₀ (CP.DefAt u w)`, and no other error. The file's only blocker is the
Δ₀ witness. **MEASURED.**

`σ₁-up` and `π₁-down` do not rescue it: they need Σ₁/Π₁ witnesses, and `DefAt`
alternates unbounded `∀̇` then `∃̇`, so it is neither. **MEASURED**, by the same
shape reading.

### 1.2 The two extra hypotheses

The miniature adds (i) the recorded value is `Lset c`, (ii) `c` is an ordinal.
They pin the `DefAt` **w** slot (the recorded value) to a stage. They do
nothing for the carrier bridge, which is where the plan dies. **They fail to
close the miniature. MEASURED.**

### 1.3 The use site: what fills `u`

`StepBody b f = (var 2 ∈̇ var (sh4 b)) ∧̇ (appAt ... ∧̇ (DefAt zero (suc zero) ∧̇ (var 3 ∈̇ var zero)))`
(`src/L/Coding/Sequence.lagda.md:114-117`). In `readBody` the `DefAt` conjunct
is spent at `(d ∷ w ∷ c ∷ z ∷ γ)` via
`DefAt-out w zero (suc zero) (d ∷ w ∷ c ∷ z ∷ γ) ...`
(`src/L/Coding/Sequence.lagda.md:181`). So `u` (slot 0) is **`d`**, the third
existential witness — the definable powerset of the recorded value — and it is
**not pinned**. The dead agent's crux is correct, and the crux does not
dissolve. **MEASURED.**

### 1.4 Why the constructibility question is now moot

Even hypothetically, `abs₀` would need a class environment `δ : (Σ isL)^n` with
`map fst δ = map fst γ`, i.e. `isL` at every slot. The two extra hypotheses give
only `isL (Lset c)` for the **w** slot. The **u** slot (`d`), the argument
`c`, the member `z`, and the outer slots `v`, `b`, `f` are not reachable —
exactly the brief's NO-GO condition on `f` and `b`, and the dead agent's crux
on `d`. **Both hold, and both are secondary**, because the Δ₀ obstruction
already kills the plan before any slot is lifted. **MEASURED** (the Δ₀
obstruction) and **MEASURED** (the slot shapes, by reading
`src/L/Coding/Sequence.lagda.md:155-230` and the generic machine in
`ProbeLJ1184A.agda`).

## 2. SUPPLY SEARCH, WHOLE TREE, BEFORE ANY LINE

| # | search | scope | result |
|---|---|---|---|
| T1 | `DefAt-out\|DefAt-stage\|DefAt-in` | whole tree (`src/ archive/ agents/ dev/`) | Class-carrier consumers only; no outer/ambient twin exists in `src/`. MEASURED |
| T2 | `Δ₀-DefAt\|Δ₀-StepAt\|Δ₀-StepBody\|Δ₀-DefBody\|Δ₀-defAt` | whole tree | **No Δ₀ witness for the delivered `DefAt`/`StepAt`.** The only hits are `L.Condensation.Δ₀-DefBodyB` — the BOUNDED restatement, not `DefBody`. MEASURED |
| T3 | `ambient.*StepAt\|StepAt.*ambient\|StepAt-out.*map fst\|StepAt.*⊨ᵛ` | `agents/ src/ archive/` | Nothing except `[LJ-1.184]`'s own reports. MEASURED |
| T4 | `mapFo emb\|Full-tr\|Σ Full` | `agents/tasks/LJ-1-184/ src/` | Only `ProbeLJ1184A.agda:312-330`. MEASURED |
| T5 | `extAt : ` and `DefAt : ` | `src/L/Coding/` | `extAt = ∀̇(...) ∧̇ ∀̇(...)` (`Model.lagda.md:662-663`); `DefAt = extAt u (∃̇(∃̇(DefBody w)))` (`Powerset.lagda.md:442-443`). MEASURED |

The decisive hits are **T2** and **T5**. T2 found that the tree's own bounded
restatement (`Δ₀-DefBodyB`) lives in `L.Condensation` — which is exactly the
"chapter" the NO-GO predicts. T5 pinned the unbounded shape.

**The file I thought I already knew, and included:**
`src/L/Coding/Powerset.lagda.md` (in T1, T5). No search excluded it.

## 3. MEASUREMENTS

Load was **NOT quiet**: 4.90 to 5.92, one user, during the runs.
`GHCRTS="-A64m -I0 -M8g"`, one agda process, cap never raised, no heap
exhaustion.

`ProbeLJ1196A.agda`, cold (interface deleted before each run), exit 0:

| run | seconds |
|---|---|
| warm-up | 4.19 |
| kept 1 | 4.08 |
| kept 2 | 4.02 |
| kept 3 | 4.00 |
| mean | **4.03** |
| no-op (interface present) | 1.41 |

The probe's own elaboration is `4.03 − 1.41 = 2.62 s`, almost all of it the
`⊨-map` chain on the concrete `DefAt` formula and the import of the heavy
`L.Coding.*` interfaces. The probe is a miniature, not a master; no DD24
judgment is drawn from it.

Lines: 117 all, 101 non-blank, **38 non-blank non-comment**. No ` ```agda `
fences (a probe has none).

Checkers: `scripts/lint-agda.py --check` **exit 0**;
`scripts/lint-prose.py --check` on this report **exit 0**. No `make check`.

## 4. DD4

The finding is syntactic and carrier-independent: the blocker is the shape of
`DefAt` (unbounded `∀̇` and `∃̇`), which is the same formula for both towers.
**So the NO-GO re-instantiates verbatim for the J tower: the ambient `DefAt`
reading is a chapter there too, and nothing of the chapter is shared beyond the
167-line generic `ReadOff` already delivered by `[LJ-1.184]`.** The satisfaction
coding itself is per-tower (`𝒟ₒ` and the `L.Coding.*` alphabet are the L
tower's); the J tower pays its own. No stop-line pushed me to write fixed; the
finding did not require writing a build.

## 5. WHAT `[LJ-1.7]` STILL NEEDS

The three named hypotheses `sl`, `sc`, `s₁` are unchanged. The residue is now
priced: **84 free lines plus one chapter**. The chapter is the outer-carrier
port of `DefAt-in`/`DefAt-out`, which runs through `codeAt-out`, `graphAt-out`,
`DefinesAt-out` and `defSet-Sat` (`src/L/Coding/Powerset.lagda.md:496-620`,
`src/L/Coding/Bridge.lagda.md:621-624`) — the satisfaction coding. The tree
already carries the BOUNDED Δ₀ restatement (`DefBodyB`, `StepAtB`,
`LeafAgree`, `src/L/Condensation.lagda.md:2333-2363`, `:7057-7196`), but at the
**class** carrier only; lifting it to the ambient carrier is the chapter.

**This re-prices `[LJ-1.7]` upward**, by one chapter-sized block instead of one
84-line block. The GO figure is refuted.

## 6. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-184/`** read WHOLE (report plus probes A, B, C). TOOK the
  obligation (`lj-1.184-report.md` section 5.4), the residue table (section
  5.2), the refused `DefAt` figure (section 5.3), and the generic module's
  `ReadOff.Machine` (`ProbeLJ1184A.agda:76-240`).
- **`agents/tasks/LJ-1-178/`** probes: TOOK the ambient residue types
  (`ProbeLJ1178A.agda` `AmbientCross`), confirmed unchanged.
- **`archive/dev/JOURNAL-archived.md:2126-2128`** read. TOOK the archived
  `AmbientOnly` stop: "an obstacle rather than a budget", blocked on the
  satisfaction decodes. **SHAPE TAKEN, CLAIM REFUSED** — the archive's blocker
  was the class-carrier equivalence; mine is the ambient carrier's non-Δ₀
  `DefAt`, a different wall.
- **`archive/dev/JOURNAL-archived.md:2197`** read. TOOK the measured bill:
  ~77 s environment conversion, ~54 s `Lset-only` content, ~56 s `Crossing`
  instantiation. The ~54 s is the chapter's actual content, measured on the
  retired route. **SHAPE TAKEN**; not transferred as a price for the ambient
  instance (P-l).
- **`src/L/Hierarchy.lagda.md:283-299` and `:334-355`** read. TOOK `step-Lset`
  and `Lset-only`: `[LJ-1.184]`'s GO-hope reads the value equation "at every
  step", but that equation is at the CLASS carrier; it does not move the
  ambient `DefAt` reading. The prediction was INFERRED and is now refuted.
- **`src/L/Coding/Sequence.lagda.md:114-230`** read. TOOK `StepBody`, `StepAt`,
  `readBody`, `StepAt-out`, and the `DefAt-out` use site at `:181`. This is the
  "what fills `u`" answer.
- **`src/L/Coding/Powerset.lagda.md:442-443, 645-727`** read. TOOK `DefAt`,
  `DefAt-in`, `DefAt-out`, `DefAt-stage` — all at the class carrier (`_⊨_` =
  `⊨ᵐ` via `open AbsL renaming (_⊨ᵐ_ to _⊨_)` at `:71`).
- **`src/FOL/LevyHierarchy.lagda.md:42-52`** read. TOOK the `Δ₀` constructors:
  no `δ-∀`, no `δ-∃`.
- **`src/FOL/Absoluteness.lagda.md:122-123`** read. TOOK `abs₀`'s `Δ₀` guard.
- **`src/FOL/Manipulation/Relabelling.lagda.md:154-155`** read. TOOK `⊨-map`.
- **`src/L/Condensation.lagda.md:2333-2363, 7057-7196`** read. TOOK the tree's
  own admission that the delivered description is not Δ₀, and the bounded
  restatement `DefBodyB`/`StepAtB`/`LeafAgree` that the chapter would have to
  mirror at the ambient carrier.

## 7. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md:93-106`** read.

**Devlin spends clause (a) at an ARBITRARY value, not at a recorded one.**
`:93-96` states (a) as `∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]`, quantifiers over the
ambient universe. `:102-106` spends it at the collapse image: "1.9.15 converts
M's satisfaction of the Σ₀ matrix into ambient Φ; (a) turns Φ into
v = L_γ". The value `v` there is the collapse image's member — ambient, not
pinned by a prior induction. **This cuts against the miniature's GO-hope that
the ambient reading is only ever spent at a recorded value.** MEASURED, by
reading `:88-113` whole.

`dev/literature/devlin-errata.md`: read the table of contents; it touches no
part of II.5 (confirms `[LJ-1.184]` section 9). MEASURED.
`dev/literature/j-hierarchy.md`: no hit for `DefAt`, `ambient`, `recorded`,
`clause (a)`. MEASURED.

## 8. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| the two extra hypotheses close the miniature | **MEASURED FALSE.** Section 1 |
| the ambient reading of the pushed `DefAt` is not the class outer reading | **MEASURED FALSE.** `ProbeLJ1196A.agda:91-95` |
| `abs₀` can be applied to `DefAt` | **MEASURED FALSE.** `DefAt` is not Δ₀ |
| `DefAt` is Δ₀ | **MEASURED FALSE.** unbounded `∀̇`/`∃̇`; `Δ₀` has no such constructor; T2 finds no witness |
| `σ₁-up`/`π₁-down` rescue the bridge | **MEASURED FALSE.** `DefAt` is neither Σ₁ nor Π₁ |
| `u`'s slot at the use site is pinned | **MEASURED FALSE.** it is `d`, the existential witness (`Sequence.lagda.md:181`) |
| the constructibility of `f`, `b` is the only blocker | **MEASURED FALSE.** it is secondary; the Δ₀ obstruction fires first |
| the ambient port is 84 lines | **MEASURED FALSE.** it is 84 lines plus a chapter |
| the chapter's size is a price | **NOT CLAIMED.** anchored comparable only (P-l, C-40) |
| `[LJ-1.184]`'s GO prediction was evidence | **MEASURED FALSE.** it was INFERRED and it is refuted |

## 9. RULES ANSWERED

- **D-1.** The abort criterion was `[LJ-1.184]`'s, fixed before the run and not
  by me. NO-GO, reported against it.
- **P-l.** I re-measured at the ambient carrier. I do not transfer the
  class-carrier coding line counts to the ambient instance; section 0 states
  them as an anchor only.
- **C-36.** Section 1 writes the term I could not write: `Δ₀ (DefAt u w)`, the
  unfillable witness, with its `file:line`.
- **C-38 as extended.** No hypothesis was discharged; the two extra hypotheses
  were shown insufficient, not supplied.
- **C-42.** The refutation measures ONE site: the `DefAt` read inside the
  ambient `StepAt-out` (`src/L/Coding/Sequence.lagda.md:181`). I did not sweep
  for other sites; T2's count of `Δ₀-DefBodyB` is the sweep's first step.
- **C-12.** One agda process, `-M8g`, never raised. Load beside every figure.
- **C-22.** This file existed as a skeleton before the first Agda line.
- **C-39, C-40.** Section 0 leads with what the free 84 lines do NOT cover.
- **DD0, DD8.** One number per claim, each with its basis; the chapter's size
  is an anchor, and section 5 says why it is not a price.
- **DD23.** No mathematical prose written; the probe carries comments only.
- **DD24.** Seconds and lines reported, nothing judged.
- **DD4.** Section 4.
- **I-5.** No `PT.rec`/`PT.map` branch in the probe.
- **D-10.** The residue `DefAt` ambient reading was priced for truth before
  proof: it is the non-Δ₀ obstruction, and section 1 states it.
- **P-k.** The probe states the ambient reading at the consumer's shape
  (`StepOutT`'s `DefAt` slot), not one layer early.

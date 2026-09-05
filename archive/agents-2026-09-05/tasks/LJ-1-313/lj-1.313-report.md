# LJ-1.313 report: Fable 5 review of `[LJ-1.312]`'s refutation

## 0. LEAD

**UPHOLD.** The refutation is sound. `φ₀`'s two free slots are the graph's
ORDINAL and the graph's machinery BOUND, and `q'` needs the VALUE and the
ORDINAL. Every hop of the role chain is verified at `file:line`. The machine
witness reproduces on this machine: `ProbeLJ1312C.agda:39.24-28`, exit 42,
`zero != suc zero of type Fin (suc (suc n))`, at 0 other Agda processes.

**And the defect is LARGER than the report states.** Two probes written for
this review measure a SECOND independent defect inside the same delivered
formula: the two leaf contents point their bound at the WRONG BINDER, and
the `[LJ-1.312]` two-line cure does not touch that. Section 3 holds the
measurement. So the report's cure price is wrong, its Form 2 premise is
refuted, and its recommendation flips. The refutation stands; the repair
grows from two lines to four.

## 1. ATTACK 1: THE BRIDGE FROM DIFFERENCE TO DEFECT

**THE BRIDGE HOLDS.** The refusal `V ≢ C` is symmetric and proves only a
difference. The asymmetry comes from three independent pieces, and each one
checks:

1. **The role measurement.** `ProbeLJ1312A.agda:171-172` pins the probe's
   copy to the delivered `src/L/BoundedSubset.lagda.md:108-111` by `refl`.
   The census refls at `:177-205` and the lookup block at `:237-277` then
   measure the delivered formula itself: OUTER slot 0 is pinned to the
   graph's value witness, slot 1 is the step index's range, slot 2 bounds
   the machinery, slot 3 bounds the value witness. Re-run for this review:
   exit 0, 2.95 s wall, 0 other Agda processes. The two negative controls
   refuse: `ProbeLJ1312B.agda:45` exit 42 at 2.45 s, `ProbeLJ1312C.agda:39`
   exit 42 at 3.12 s, both at 0 other processes. A `refl` census with a
   refusing control is a measurement, not a reading.
2. **What `q'` needs.** `agents/tasks/LJ-1-302/ProbeLJ1302A.agda:72-75`
   types `Composite` as ambient `φ₀` implies ambient
   `Graph* {2} zero (suc zero)`. The graph's roles there are explicit at
   `agents/tasks/LJ-1-244/ProbeLJ1244A.agda:111-114`: the conclusion is
   `fst (lookup zero γ) ≡ Lset (fst (lookup (suc zero) γ))`, with the
   ordinal hypothesis on slot 1. So `q'` needs (VALUE, ORDINAL) at
   (0, 1). VERIFIED by reading.
3. **The outside specification.** Devlin 2.7 clause (a), section 7 below.
   The free pair after closing `z` is (value, ordinal), in that order.

`ρ` keeps base slots 1 and 2 (`agents/tasks/LJ-1-241/ProbeLJ1241A.agda:106-111`)
and `closeN 14` closes 0 to 13 (`:140-146`). Base slots 1 and 2 are the
ORDINAL and the machinery BOUND by the measured roles. So the composite's
type asks the wrong pair. **The bridge from difference to defect holds.**

## 2. ATTACK 2: LINK 4'S FOUR HOPS

Each hop read in the syntax, comments ignored.

| hop | claim | verdict | evidence |
|---:|---|---|---|
| 1 | `GraphB {m} ψs ψa (w b K : Fin m)` | **VERIFIED** | `src/L/Condensation.lagda.md:2483-2485`, the telescope in that order |
| 2 | `module S = StepB {1 + m} ψs (suc w) (suc b) zero (suc K)` | **VERIFIED** | `:2487`. `w` lands in `StepB`'s `v`, `b` in `b`, the graph's own binder in `f`. `ProbeLJ1312A.agda:185-196` pins the instantiation arithmetic by `refl`, re-run green |
| 3 | `StepB {m} ψ (v b f K : Fin m)` and `stepBndAt = extAtB v K witB` | **VERIFIED** | `:2389-2390` and `:2415` |
| 4a | `extAtB y K φ` makes `y` the VALUE | **VERIFIED** | `:100-102`. First conjunct: everything in `y` satisfies `φ`. Second: every satisfier in `K` lies in `y`. So `y` is the set the formula describes |
| 4b | `bodyB`'s first conjunct makes `b` the ORDINAL | **VERIFIED** | `:2403`, `var (suc (suc zero)) ∈̇ var (suc (suc (suc (suc b))))`: the index `c` ranges in the set at `b`, and `appAt` at `:2404` reads `f` at `c`. The unbounded exemplar has the same shape at `src/L/Coding/Sequence.lagda.md:114` and `:119-120` |

**NO HOP FAILS.** The comment at `src/L/BoundedSubset.lagda.md:70-73` names
the roles one position off this syntax at every slot, as the brief warns.

## 3. ATTACK 3: THE SWEEP, AND IT HITS

**`StepAtB` and `SatGraphB` are CLEAN. The hits are INSIDE the audited
file, at sites `[LJ-1.312]` did not enumerate.**

### 3.1 `StepAtB`: clean, and it is the exemplar that convicts `LevelHood`

`StepAtB` instantiates `StepB {suc n} ψ (suc v) (suc b) (suc f) zero`
(`src/L/Condensation.lagda.md:2448`), so its `K` is slot zero. Its leaf
frame bound computes to `suc^4 zero` (`:2397` at `K = zero`) and its leaf
content pointer is the literal `suc^4 zero` (`:2444`). **Frame and content
name ONE slot.** Its `v b f` pass through the telescope. It has no
consumer in `src/` (grep over `src/`, definition only at `:2441`).
MEASURED, by reading and by the grep.

### 3.2 `SatGraphB`: clean, protected by a built semantic proof

`SatGraphAgree.out` and `.back` are TERMS with bodies at
`src/L/Condensation.lagda.md:7072-7095`. They decode and rebuild
`satGraphB` against the machine's `satGraphAt` slot by slot, and
`TwelveAgree` supplies `twelve-out` and `twelve-back` as proved lemmas
(`src/L/Condensation/TwelveAgree.lagda.md:527-538`). A slot mismatch
cannot hide under a built two-directional agreement. Its `w K` are
telescope parameters, never literals. MEASURED, by reading the terms.

### 3.3 THE HIT: the two leaf bound pointers, MEASURED by machine

The step frame bounds its leaf by the step's `K`
(`src/L/Condensation.lagda.md:2396-2399`). The leaf CONTENT's bound is an
argument the caller picks. `LevelHood` copies `StepAtB`'s class-carrier
literal `suc^4 zero` (`src/L/BoundedSubset.lagda.md:82` and `:90`). In
`LevelHood`'s context that slot is NOT `K`:

- **Step side, MEASURED.** `ProbeLJ1313A.agda:88-96`, `leaf-frame-s`,
  `refl`: the delivered frame bound is BODY slot 8, which is OUTER slot 2,
  the machinery bound (`g1` at `:158`). The content pointer is BODY slot
  4, which is the graph's own function binder `f` (`g2` at `:162`).
  `DefBodyB` hands that pointer to `isCodeBS` three binders deeper, where
  it still reads `f` (`g4` at `:175`).
- **Approximation side, MEASURED.** `leaf-frame-a` at `:101-109`: frame at
  ITS body slot 10, which is OUTER slot 2 (`g5`). Content pointer at slot
  4, which is the domain binder `u2` (`g6`).
- **The control refuses.** `ProbeLJ1313B.agda:44` states that the frame
  points where the content points. Exit 42,
  `suc (suc (suc (suc zero))) != zero of type Fin (suc V.m)`, 2.21 s, 0
  other Agda processes.
- **The `[LJ-1.312]` cure does not touch it. MEASURED.**
  `leaf-frame-s-cured` and `leaf-frame-a-cured`
  (`ProbeLJ1313A.agda:118-136`): the cure moves the frames to slots 9 and
  11, OUTER slot 3, and both content pointers stay at slot 4. `g3` and
  `g7` complete the arithmetic. Exit 0, 11.55 s, 0 other processes.

So the delivered `levelHoodB` bounds its code-set machinery by the
approximating FUNCTION on the step side and by a DOMAIN VARIABLE on the
approximation side. No comment, no design note and no exemplar supports
that. `StepAtB`, the design's own class-carrier instance, makes frame and
content coincide. This is the same disease as the role off-by-one: a
class-carrier literal copied into a context whose environment tail
differs.

### 3.4 A THIRD SITE BY READING: `LevelHood0.reverse`

`src/L/BoundedSubset.lagda.md:864-869` consumes `LH.levelHoodB` through
`renameFo (padRight 1)`. `padRight` keeps low indices
(`src/FOL/Manipulation/Parameters.lagda.md:150-151`), so `levelHoodB`'s
slots land unmoved in the arity-5 environment. The construction places
the ordinal certificate on the binder that the SYNTAX makes the machinery
bound, and asserts `y` a member of the slot the SYNTAX makes the ORDINAL
(`:866` and `:869` against the measured roles). Under the comment's
roles at `:861-863` every choice is right, so `reverse` was written to
the comment. INFERRED, from the MEASURED roles; no machine ran on
`reverse` itself. `[LJ-1.312]` never names `reverse`. Note the asymmetry:
the Form 1 role cure happens to align `reverse`'s intent, because the
cure moves the syntax onto the comment's roles; its leaf damage stays.

### 3.5 The extent, restated

Sites carrying the disease: the role slots at `:105` and `:111`
(`[LJ-1.312]`, MEASURED); `Σ₂` at `:855-856` (`[LJ-1.312]`, MEASURED);
the two leaf pointers at `:82` and `:90` (THIS REVIEW, MEASURED);
`reverse` at `:864-869` (THIS REVIEW, INFERRED). All five sit inside
`LevelHood` and `LevelHood0`. `StepAtB` and `SatGraphB` are clean, so the
report's INFERRED guess about the two sites it named was right, and its
enumeration inside the file it audited was short by three.

## 4. ATTACK 4: THE BLAST RADIUS, RE-CHECKED

C-40 asks for consumers a name grep misses. Checked specifically:

- **Re-export or `open public`.** `L.BoundedSubset` is imported exactly
  once, `src/Everything.lagda.md:383`, and the line is a bare `import`,
  no `open`, no `public`. A re-export path needs an import; there is
  none. MEASURED, grep over `src/` for `import L.BoundedSubset`.
- **Aliases and qualified access.** `graphBndAt` appears in `src/` only
  at its definition (`src/L/Condensation.lagda.md:2489-2493`) and inside
  `L.BoundedSubset`. `LevelHood` and `levelHood` appear in no `src/` file
  outside `L.BoundedSubset`. `GraphB` outside the two files matches only
  `SatGraphB`, a different module
  (`src/L/Condensation/TwelveAgree.lagda.md:31`). MEASURED, grep.
- **Record fields.** `GraphB`, `StepB`, `ApproxB`, `LevelHood` are
  parameterized modules, not records. No field projection path exists.
  MEASURED, by reading the definitions.

**So the claim「nothing in `src/` breaks」holds**, and the stronger form
holds too: nothing in `src/` even reaches the changed names except
`src/Everything.lagda.md:383`. The consumers that DO break are probes:
`ProbeLJ1241A.agda:85`, `ProbeLJ1241B.agda:52` and `:63`,
`ProbeLJ1239A.agda:57`, as the report says, plus `ProbeLJ1312A`'s own
copy and this review's probes, which are records and re-run on demand.

## 5. ATTACK 5: A WRONG TYPE AGAINST A FALSE STATEMENT

`[LJ-1.312]` marks「`q'` is false at the delivered `φ₀`」INFERRED. **This
review resolves it differently: the claim is UNSETTLED in truth value,
and the route is dead under BOTH truth values.**

- Under the role reading alone, `φ₀(a, b)` says「the level at ordinal `a`
  exists inside bound `b`」, which is satisfiable, and `[LJ-1.310]`'s
  empty-set-and-limit pair then falsifies the implication. `Composite`
  would be uninhabitable.
- **But the leaf measurement (section 3.3) puts `φ₀`'s satisfiability
  itself in doubt.** The machinery inside `φ₀` ranges its code sets over
  the approximating function's members. If no environment satisfies the
  delivered matrix, the implication `Composite` is VACUOUSLY inhabitable,
  and the route dies further on, where the ambient reading needs `φ₀` to
  HOLD at a real level. INFERRED, both branches; no model ran.

**Can the delivered `φ₀` serve `q'` by a different bridge? No.** The
value slot is existentially closed inside `φ₀`; no bridge recovers a slot
a formula does not have. And the leaf pointer names a BOUND variable, so
no renaming of free slots can repair it. Both statements are INFERRED
from the MEASURED syntax. **The countermodel was NOT built, and here is
the reason in D-10's terms:** the target it would refute is already
refuted twice at the syntax level by machine, its truth value forks on
the leaf question, and settling that fork means satisfaction reasoning
through a matrix the route must abandon in any case. A model build here
prices a formula nobody will keep. That work is declined, not skipped.

## 6. ATTACK 6: FORM 1 AGAINST FORM 2

**Form 2's stated premise is REFUTED by measurement.** The report says
the delivered syntax is「CONSISTENT as a formula. Its four slots are all
used and all meaningful. Only the RENAMING reads them wrongly」
(`lj-1.312-report.md:209-211`). Section 3.3 measures otherwise: the
delivered matrix mis-bounds its own machinery, and a `ρ'` permutation of
FREE slots cannot reach a defect on a BOUND variable. So Form 2 repairs
the roles and ships the broken leaf into `φ₀`. **The recommendation to
price Form 2 first does not survive.**

**Form 1, extended to FOUR lines, is the only coherent cure, and it is
PROVED in a copy.** `ProbeLJ1313C.agda` holds the copy: the two
`[LJ-1.312]` lines at `:105` and `:111`, plus the two leaf pointers
re-aimed to the slot the frame names, `suc^9 zero` at `:82` and
`suc^11 zero` at `:90`. Frame and content then coincide on both sides
(`CensusC2`, two `refl`s), and the Δ₀ and Σ₁ certificates typecheck
UNCHANGED (`ProbeLJ1313C.agda:96-121` and `:140-146`). Exit 0, 4.94 s,
0 other Agda processes. NOTHING IS LANDED; the orchestrator lands cures.

**Which form does `q'` need? The single-bound form.** Devlin's Φ carries
one auxiliary `z` and clause (a) closes it alone; the digest and the
primary both show three slots and one closure (section 7). Form 1 after
the leaf repair gives exactly that shape: one bound, closed once, value
and ordinal free. Form 2's two independent bounds have no exemplar in
the literature this project holds, and the report itself says the two
forms differ in meaning. D-10 orders the truth priced before the proof:
the attested shape is Form 1's. INFERRED for the provability of `q'`
itself, which no probe here settles.

## 7. ATTACK 1's THIRD LEG, VERIFIED: THE DEVLIN READING

The digest quotes 2.7(a) as `∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]`
(`dev/literature/devlin-II5.md:95-96`). **Checked against the primary:**
`_build/literature/dev2.txt:1186-1194`. The OCR of the (a) line itself is
DEGRADED to stray glyphs, but two anchors survive: the slot order is
legible at `:1186`,「Φ (z, ι;, γ)」, and clause (b) at `:1191-1194` is
legible enough to read `v = L_γ` against `∃z φ(z, v, γ)` with `z` the
only closed slot. **The digest is faithful enough to carry the weight it
carries here**, because the only facts used are the slot order and which
slot (a) closes, and both are visible in the primary. Bedrock copies the
closure shape at `src/L/BoundedSubset.lagda.md:142-143`, `∃̇ levelHoodB`,
closing slot 0 and keeping 1 and 2. Under the measured roles the
delivered formula closes the VALUE and frees (ORDINAL, BOUND), so it
fails the specification; under the Form 1 cure slot 0 is unused, and
(VALUE, ORDINAL) are the kept pair. VERIFIED.

## 8. ATTACK 7: THE 470 AND THE 33,200

`dev/PLAN.md:60-66` carries the 470 as four ingredient parts, and `:83`
carries the endpoint about 33,200 with standing 32,488.

- **The line counts barely move.** The full cure replaces literals on
  four existing lines of `src/L/BoundedSubset.lagda.md`; the file's line
  count does not change, so standing and the 33,200 floor are untouched
  by the cure itself. MEASURED for the cure's shape (`ProbeLJ1313C`),
  INFERRED for the zero net delta.
- **The 470 stays the right figure for its parts, with one row
  re-founded.** The parts at `:60-65` price `Agree` modules and ties that
  are parametric in the slot literals. The row「the composite's type,
  writable」now means: writable AGAINST THE CURED FORMULA. `[LJ-1.312]`
  measured that the Δ₀ and Σ₁ certificates survive the role cure, and
  `ProbeLJ1313C` measures that they survive the full cure. What the 470
  never contained, the composite's TERM, stays outside, as PLAN `:93-94`
  already says.
- **The unpriced additions this review creates:** re-deriving `φ₀` over
  the cured matrix (a re-run of `ProbeLJ1241A`'s construction, whose `ρ`
  and `pins` survive by construction), and `LevelHood0`'s own two
  statements, `Σ₂` and `reverse`, which need re-shaping, are NOT route
  blockers because `LevelHood0` has no consumer. Single-digit lines each.
  INFERRED, not built, basis: the probe comparables named above.
- **The 17 s re-check figure is a comparable and the report says so
  itself** under P-l. C-50's honesty held. The four-line cure re-checks
  the same file, so the same comparable applies: about 17 s, 1,409
  in-fence lines (`dev/ledger.toml:3126`) at 0.0121 s per line
  (`dev/ledger.toml:2749-2751`).

## 9. DD4, AND MY AXIS (C-46)

**My axis is AC-against-GCH**, DD4's own, fixed in code at
`scripts/measure/ledger.py:48-52`, the `--reuse` report. The report's DD4
claims verify: `dev/ledger.toml:2749-2751` lists `L/BoundedSubset` among
the six masters outside the Landmarks cone, reachable only through
`src/Everything.lagda.md`, and my grep in section 4 confirms it
independently. The ledger's qualification at `dev/ledger.toml:204-205`
applies as the brief says: the GCH closure is read from a statement whose
proof is not wired, so it UNDERSTATES, and `q'` is the route that would
pull `levelHoodB` inside it. So the cure lands on a file that is
GCH-bound and AC-free TODAY, and the shared gain is the FOL and
bounded-set layer under it, which both trophies use by construction. The
timescale point stands: a DD4 answer for this file is about where it WILL
sit, and the four-line cure changes no import and moves nothing across
the axis.

## 10. WHAT RAN, AND AT WHAT COST

All runs on this machine, `GHCRTS="-A64m -I0 -M8g"`, one process at a
time. The slot count `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`
ran before every invocation and returned 0 every time, so this review
never held more than one of C-12's two slots. No heap exhaustion, no
wall; the longest run is 11.55 s against the 30-minute wall bar.

| file | exit | wall | other Agda processes |
|---|---:|---:|---:|
| `ProbeLJ1312A.agda` re-run | **0** | 2.95 s | 0 |
| `ProbeLJ1312B.agda` re-run | 42, EXPECTED | 2.45 s | 0 |
| `ProbeLJ1312C.agda` re-run | 42, EXPECTED | 3.12 s | 0 |
| `ProbeLJ1313A.agda` | **0** | 11.55 s | 0 |
| `ProbeLJ1313B.agda` | 42, EXPECTED | 2.21 s | 0 |
| `ProbeLJ1313C.agda` | **0** | 4.94 s | 0 |

The sibling probes were re-run, never changed. The wall times are warm
figures over cached interfaces and are not comparable to `[LJ-1.312]`'s
cold 14.60 s.

## 11. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| No hop of link 4 fails | **MEASURED**, sections 1 and 2, probes re-run |
| `StepAtB` carries no mismatch and has no consumer | **MEASURED**, reading plus grep, section 3.1 |
| `SatGraphB` carries no unprotected mismatch | **MEASURED**, the built terms at `src/L/Condensation.lagda.md:7072-7095` |
| The leaf content pointers do not name the frame's bound | **MEASURED**, `ProbeLJ1313A` exit 0 and `ProbeLJ1313B` exit 42 |
| The `[LJ-1.312]` cure does not move the leaf pointers | **MEASURED**, `leaf-frame-s-cured` and `leaf-frame-a-cured` |
| `reverse` follows the comment's roles | **INFERRED**, reading over MEASURED roles |
| Nothing in `src/` consumes the changed names except `Everything` | **MEASURED**, section 4 greps |
| No re-export or record-field path exists | **MEASURED**, section 4 |
| The delivered `φ₀` cannot serve `q'` by another bridge | **INFERRED**, section 5 |
| `q'`'s truth value at the delivered `φ₀` is unsettled either way | **INFERRED**, section 5, and it corrects `[LJ-1.310]`'s「uninhabitable」to a fork |
| Form 2 cannot repair the leaf defect | **INFERRED** from the MEASURED bound-variable location |
| Which form `q'` can be PROVED against | **NOT SETTLED**, section 6 |
| The 33,200 floor does not move | **INFERRED**, section 8 |
| The countermodel is not worth building now | **INFERRED**, D-10 reasoning in section 5 |

## 12. ARCHIVE USED (DD18)

One line read per file.

- `agents/tasks/LJ-1-312/lj-1.312-report.md`, read WHOLE. **Line read:**
  `:209-211`,「The delivered syntax is CONSISTENT as a formula... Only
  the RENAMING reads them wrongly」. TOOK the whole return as the review
  target. REFUTED that line by `ProbeLJ1313A` and `ProbeLJ1313B`.
- `agents/tasks/LJ-1-310/lj-1.310-report.md` section 7, read whole.
  **Line read:** `:258-259`, the CLAIM marked INFERRED. TOOK the
  derivation as the reading under test; its step 5 is now MEASURED, and
  its「Composite is uninhabitable」consequence is corrected to a fork in
  section 5.
- `agents/tasks/archive/LJ-1-52/ProbeLJ152A.agda`, read `:40-84`.
  **Line read:** `:46-47`,「the bounded graph implies the machine graph
  at the value slot w (slot 1) and the index slot γ (slot 3)」. CHECKED
  the brief's claim: `GraphAgree` at `:48-53` is a `Type`, taken only as
  the hypothesis `ga` at `:58`, never proved. Against the MEASURED roles
  (value at body 0, ordinal at body 2) the asserted agreement is off by
  one in BOTH arguments. The claim VERIFIES.
- `agents/tasks/LJ-1-302/ProbeLJ1302A.agda`, read `:55-93`. **Line
  read:** `:72-75`, the `Composite` type. TOOK it as the statement under
  refutation; `comp` enters only as the module parameter at `:81`, C-45's
  shape exactly.
- `archive/dev/TASKS-archived.md`, read `:58-75`. **Line read:** `:68`,
  the `L3.32-T33` row,「Condensation crossing | DELIVERED」. TOOK SHAPE
  ONLY. **What would not transfer:** that crossing rode `q` as a
  syntactic identity at the class carrier and `[LJ-1.293]` refuted `q` by
  machine, so no term and no figure of it transfers; only the fact that a
  crossing once closed, which prices nothing here.

## 13. LITERATURE USED (DD18)

- `dev/literature/devlin-II5.md:95-96`, Devlin 2.7 clause (a). **USED**
  as the outside specification, and CHECKED against the primary at
  `_build/literature/dev2.txt:1186-1194`; section 7 states what the OCR
  does and does not show. The digest carries the weight put on it.
- `dev/literature/devlin-II5.md:99`, clause (b). **USED, one step
  further than `[LJ-1.312]`:** its primary line is the LEGIBLE witness of
  the closure shape that the degraded (a) line cannot supply alone.
- `dev/literature/devlin-II5.md:214-215`, the summary row. **NOT USED.**
  It repeats `:95-96` and adds no slot information.

## 14. PROHIBITIONS, ANSWERED

- Writes happened only inside `agents/tasks/LJ-1-313/`: this report and
  three probes. `src/`, `dev/`, `AGENTS.md`, `src/L/GCH.lagda.md` and
  every other task directory are untouched. The cures live in copies;
  NOTHING IS LANDED.
- `agents/tasks/LJ-1-312/` was read and re-run, never edited.
- No commit, no push, no `git checkout .`, no `git stash`, no
  `git reset --hard`, no `git clean`. `make check` was not run.
- One Agda process at a time under the C-12 cap, counted before every
  invocation with the brief's own command. The cap was never raised.
- `lint-prose.py --check` and `lint-agda.py --check` were run on this
  report and the three probes; both exit 0.

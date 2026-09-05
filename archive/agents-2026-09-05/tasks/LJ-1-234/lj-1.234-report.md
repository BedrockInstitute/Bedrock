# LJ-1.234 report: does `pairω` need an object-language arithmetic at all?

tier: pi (deepseek-subagent-mode). Probe task. No master edited. No commit,
no push. Written incrementally (C-22).

Every negative is marked **MEASURED** or **INFERRED**, in those words.

## 0. LEAD

**NO. Object-language arithmetic is NOT needed for `pairω`. MEASURED.**

The obligation `sq ω` is the ambient injection
`Σ[ f ∈ (⟪ ω ⟫ × ⟪ ω ⟫ → ⟪ ω ⟫) ] ((x y : …) → f x ≡ f y → x ≡ y)`
(`src/L/Ordinal/SquareLaw.lagda.md:685-687`). The current tree already
delivers the zero-arithmetic ORDER route at every INITIAL ordinal via
`via-col-square` (`:960-961`); the only gap is the base at `ω`, because
`Init ω` needs `⟨ ω ∈ˢ ω ⟩`, refuted by `∈-irrefl`. **I closed that base by
instantiating the delivered `InitialCore` at `ω` with three zero-arithmetic
hypotheses (the archive's `CoreAtω` shape), and the whole thing is GREEN:
60 charge lines, cold mean 1.19 s, exit 0, `--safe`, no wall.**

Against `[LJ-1.226]`'s 83 measured lines (addition description 36 + witness
construction 47, which is addition ALONE and not yet the injection), the
60-line order route delivers the COMPLETE injection — function and
injectivity — with zero object-language formula of any kind.

## 1. THE ABORT CRITERION, FIXED BEFORE THE RUN (D-1)

Copied from the brief and fixed before the first line of probe code:

- **NO ARITHMETIC IS NEEDED.** Build an injective `⟪ω⟫ × ⟪ω⟫ → ⟪ω⟫` into L
  by a route that never states addition or multiplication in the object
  language. Report the written lines and the seconds. STOP.
- **ARITHMETIC IS NEEDED.** Name the exact step that forces it (C-36).
- **A CHEAPER ARITHMETIC EXISTS.** Price it against the 83 measured lines.
- **THE ORDER CORE WALLS AGAIN.** Name the term and report the elapsed
  seconds.
- **A WALL.** A single `agda` invocation past 20 minutes is a wall.

**VERDICT: NO ARITHMETIC IS NEEDED.** The order route closes the base at
`ω` in 60 lines, 1.19 s cold mean, no wall. **The one wall I met was not the
order core:** the first run heap-exhausted, and it was the R-34 unpinned
`InfinitySet` level meta, cured by `module IS = InfinitySet {ℓ}` (section 3).

## 2. WHAT WAS BUILT, AND WHAT IT COSTS

`agents/tasks/LJ-1-234/ProbeLJ1234A.agda`, 146 lines whole, 91 non-comment
non-blank lines (the probe caliber of `[LJ-1.231]` section 1).

| part | non-comment non-blank lines | class |
|---|---:|---|
| OPTIONS + Base imports + module header | 5 | header, paid once by a master |
| L-side imports + `open`s | 26 | header, paid once by a master |
| **three hypotheses of `InitialCore` at `ω`** | **49** | **MEASURED, the charge** |
| **`Coreω` instantiation + `pairω` + `pairω-inj` + `squareω`** | **11** | **MEASURED, the charge** |
| whole file | 91 | green, `--safe`, exit 0 |

**The charge is 60 lines, and it is the whole deliverable:**
`squareω : sq ω` = `pairω , pairω-inj`.

The three hypotheses, all zero-arithmetic, all shaped by the archive's
`CoreAtω` (`archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:815-893`):

- `ω-limit : (γ : S) → ⟨ γ ∈ˢ ω ⟩ → ⟨ sucV γ ∈ˢ ω ⟩` — successor closure,
  one `ω-mem→numeral` case.
- `noinj²ω : … ⟨ β ∈ˢ ω ⟩ → ⟨ ω ∈ˢ β ⟩ → … → Empty.⊥` — vacuous, one line
  from `ω∉β`.
- `finite-excl-ω : … ⟨ β ∈ˢ ω ⟩ → (f : ⟪ ω ⟫ → ⟪ β ⟫ × ⟪ β ⟫) injective
  → Empty.⊥` — the finite-exclusion chase at `ω`, reusing the delivered
  `FiniteBase.AbstractChase.NoInj.no-inj` with `numeral-into-ω`, and NOT
  needing the `⟨ ω ∈ˢ ω ⟩` that `FiniteBase.finite-excl` demands.

Then the base is exactly the current tree's own `Initial` shape specialized
to `ω`:

```agda
module Coreω = InitialCore ω ω-ord ω-limit noinj²ω finite-excl-ω
pairω p = fiber ω {x = colA p} (col∈α p) .fst
pairω-inj p q e = SQ.col-inj ω ω-ord {p = p} {q = q}
  (sym (fiber ω {x = colA p} (col∈α p) .snd)
   ∙ cong (⟪ ω ⟫↪) e
   ∙ fiber ω {x = colA q} (col∈α q) .snd)
```

**No `Formula`, no `addFo`, no `multFo`, no `∈̇`/`≐`/`prAtL`/`sucAtL`
atom, no `numeralL`, no `ωʟ`.** A grep over the probe for
`hasSeparationL|hasReplacementL|stage|LsetS|Lset|𝒮ʟ|boundingOrd|numeralL|
ωʟ|prʟ|prAtL|sucAtL|pairʟ|unionʟ` returns **ZERO hits. MEASURED.**

### 2.1 Why this dissolves the object-language arithmetic

The step that APPEARED to force arithmetic was the choice of
`Count.pair a b = (a + b) · (a + b) + a` (`src/FOL/Count.lagda.md:29-30`):
its value clause is a recursion over addition and multiplication, so carving
ITS graph by separation needs object-language addition and multiplication.
**MEASURED: that is a forcing step for the `Count.pair` choice, not for the
obligation.** The obligation is "some injective function exists", and the
order route's pairing `p ↦ fiber ω (col∈ω p) .fst` has a value clause that is
the order-theoretic collapse, whose only atoms are membership and the
collapse — no arithmetic. So the forcing step the arithmetic was built for
never arises.

## 3. SECONDS AND LOAD

**Machine state.** 16 cores (`hw.ncpu`), macOS, Agda 2.8.0. ONE agda process
of mine at a time, `GHCRTS="-A64m -I0 -M8g"`, cap never raised. The sibling's
Agda slot may be running; I did not inspect it. One-minute load 4.30 to 4.36
over my timed runs (up 1 day, 2 users).

| run | cold seconds | note |
|---|---:|---|
| warm-up | — | discarded (C-12 discipline) |
| kept 1 | 1.21 | cold, interface deleted |
| kept 2 | 1.19 | cold |
| kept 3 | 1.18 | cold |
| **cold mean** | **1.19** | three kept runs, load 4.30 |

**No wall.** Exit 0 each run.

### 3.1 The one wall I met, and it is NOT the order core

**MEASURED. The first run heap-exhausted at the 8 GB cap** (clean "Heap
exhausted" exit, never OOM). I bisected before interpreting it (the brief's
rule: every cut gets the same bound as its green control):

1. The file cut at `finite-excl-ω` failed with `UnsolvedMetaVariables` at the
   `⟪ ω ⟫` in `noinj²ω`'s type — the R-34 unpinned `InfinitySet` level meta
   (`dev/LESSONS.md`, T59's table records the same class).
2. Cure: `module IS = InfinitySet {ℓ}` before the `open`, exactly T59's cure.
   After it, the hypotheses check in 2.1 s.
3. The full file then checks in 1.19 s.

**So the heap exhaustion was the level-meta churn, not the pairing. The order
core did not wall.**

### 3.2 The T59 wall did NOT transfer

**MEASURED. `agents/tasks/archive/L3-32-T59/l3.32-t59-report.md` section 3
recorded `pair-inj` walling at concrete `ω` (>3 min, three shapes) in the
ARCHIVED tree.** The archived route was `bound (col→τ …)` — an opaque
`bound-inj` applied to the union fiber of `col→τ`, which normalizes the
`τ`-collapse under the opaque spine (R-35/R-38 class).

**The current tree replaced that shape.** `src/L/Ordinal/SquareLaw.lagda.md:944-951`
builds the pairing DIRECTLY as `p ↦ fiber α (col∈α p) .fst`, with `pair-inj`
by the TRANSPARENT `col-inj` applied to the fiber equalities. `col-inj` is a
case analysis on `tri≺`; it never unfolds `col∈ω`'s body. **My probe uses that
direct shape at concrete `ω` and it checks in 1.19 s.** The archived wall does
not transfer to this tree. **MEASURED at this site.**

## 4. DD4: TOWER STATUS

**The content is tower-neutral. MEASURED by grep, and by the statement.**

- Over the whole probe, zero hits for `hasSeparationL`, `hasReplacementL`,
  `stage`, `LsetS`, `Lset`, `𝒮ʟ`, `boundingOrd`, `numeralL`, `ωʟ`, `prʟ`,
  `prAtL`, `sucAtL`, `pairʟ`, `unionʟ`. The atoms are `ω`, `sucV`, `#_`,
  `⟪_⟫`, `⟪_⟫↪`, `member`, `fiber`, `↪-inj`, `ω-ord`, `#∈ω`,
  `ω-mem→numeral` — the two towers' shared presentation of `ω` and its
  numerals, and generic V-hierarchy vocabulary.
- **The statement `sq ω` names no tower.** The delivered `InitialCore` is
  already generic over `(α, oα)`, and my three hypotheses are the `ω`
  instance of its generic clauses.

So if this content is shared, the J tower pays it once rather than twice,
and its weight in a route decision halves. **MEASURED: the content names no
tower; the halving is AVAILABLE and is not itself priced here.**

## 5. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-231/lj-1.231-report.md`, read WHOLE.** TAKEN: the
  consumer analysis (section 4), the band (2.6), the archive shape (Q4), and
  the counter-evidence recording (`l3.32-t85-report.md:110`). This brief is
  the brief within this brief.
- **`agents/tasks/LJ-1-226/lj-1.226-report.md` and `ProbeLJ1226A.agda`, read
  WHOLE.** TAKEN: the 83-line anchor (`:60-72`), the `Count.pair` forcing
  reading (section 2), and the probe's Part 0/1/2 split. **WHAT WOULD NOT
  TRANSFER: the object-language arithmetic, which this task refutes as a
  requirement.**
- **`agents/tasks/LJ-1-176/lj-1.176-report.md:192-206`, `:227-229`, `:452`.**
  TAKEN: A5's object list, that 160 was row 1's number transferred, and that
  `pairω` is A5's. **`pairω` is now priced, not charged at a comparable.**
- **`archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:815-893`,
  read WHOLE (the code).** TAKEN, **SHAPE ONLY**: `CoreAtω`'s `ω-limit`,
  `ω∉β`, `numeral-into-ω`, `numeral-into-ω-inj`, `no-inj-finite-ω`,
  `finite-excl-ω` — the zero-arithmetic base. **WHAT WOULD NOT TRANSFER: the
  line counts (P-l) and the archived tree's `bound ∘ col→τ` injectivity
  shape, which the current tree no longer uses.**
- **`agents/tasks/archive/L3-32-T85/l3.32-t85-report.md:110` and
  `agents/tasks/archive/L3-32-T59/l3.32-t59-report.md`, read WHOLE.** TAKEN:
  the T59 wall record (`pair-inj` >3 min at concrete `ω`, section 3) and the
  R-34 cure (`module IS = InfinitySet {ℓ}`). Section 3.2 of this report: the
  wall did not transfer, and the R-34 cure DID apply.
- **Delivered masters read for the obligations:**
  `src/L/Ordinal/SquareLaw.lagda.md:685-687` (`sq`), `:692-698` (`Init`),
  `:703-710` (`InitialCore`'s hypotheses), `:944-951` (`Initial.pair-inj`),
  `:960-961` (`via-col-square`); `src/L/StageCardinal.lagda.md:15-19`;
  `src/L/BoundedSubset.lagda.md:1388-1390` (`sq` hypothesis), `:1397`
  (`module SC`), `:1410` (`sq α` used at `α∉ω`). **MEASURED: `Init ω` is
  uninhabited (`ω ∈ ω` refuted), so the delivered `via-col-square` does not
  reach `ω`. **INFERRED: the consumer `sq` hypothesis ranges over `δ ∉ ω`
  inside `sucV α`, which includes `δ = ω` when `α ≥ ω`, so `sq ω` is a real
  gap; this probe fills it regardless of that inference.**

## 6. LITERATURE USED (DD18)

- **`dev/literature/rudimentary-functions.md:68`. TAKEN, and it requires NO
  object-language arithmetic.** The basis list gives `F2(x, y) = x × y` (the
  product) and `F9(x, y) = <x, y>` (the ordered pair) outright. **MEASURED
  ZERO hits in that file for a Gödel pairing or a numeral arithmetic**; its
  one use of "arithmetic" at `:19` is a paper title. The basis requires only
  the product and the ordered pair, not addition or multiplication on
  numerals.
- **`dev/literature/j-hierarchy.md:147-149`. TAKEN.** "if α is closed under
  the Gödel pairing function then `otp(<^A_α) = α`" — this is the ORDER-TYPE
  route's mathematics (the canonical well-order on the square collapses onto
  `α`), exactly the shape my probe instantiates at `ω`. **It carries no size
  and no object-language arithmetic.**
- **Does any source treat the `ω` base separately? NO. MEASURED.** The `ω`
  mentions in both files are about `ω` as a set (`ω ∈ V`, `J1 ∪ {ω}`, the
  rud closure of `{ω}`), not about a separate pairing base. The product and
  the order-type collapse are stated uniformly; no source isolates a `ω`
  arithmetic.

## 7. THE NEGATIVES, EACH CLASSIFIED

- **MEASURED. Object-language arithmetic is not needed.** `squareω : sq ω` is
  green in 60 charge lines with zero object-language formula.
- **MEASURED. The archive's zero-arithmetic shape transferred.** The three
  `CoreAtω` hypotheses instantiate the delivered `InitialCore` at `ω` and
  close the base.
- **MEASURED. The T59 pairing wall did NOT transfer.** The direct
  `p ↦ fiber ω (col∈ω p)` shape checks at concrete `ω` in 1.19 s; the
  archived `bound ∘ col→τ` shape is gone from the current tree.
- **MEASURED. The one wall I met was R-34, not the order core.** First run
  heap-exhausted on the unpinned `InfinitySet` level; cured by
  `module IS = InfinitySet {ℓ}`, after which the whole file is 1.19 s.
- **MEASURED. The content is tower-neutral.** Zero tower-specific hits by
  grep, and `sq ω` names no tower.
- **MEASURED. The forcing step for arithmetic is the `Count.pair` choice,
  not the obligation.** `Count.pair`'s value clause is a recursion; the order
  route's is not.
- **INFERRED. Row 5 of A5 dissolves to this 60-line shape or better.** The
  ambient `sq ω` was also already green in `[LJ-1.156]` via the ℕ route
  (`ProbeLJ1156A.agda:149-150`, `:522-523`); I did not re-price that route,
  and P-l binds the comparison. **The measured claim is the 60 lines here.**
- **NOT MEASURED. Whether the orchestrator prefers the order route or the
  already-green ℕ route.** Both are zero object-language arithmetic; I priced
  the order route only.

## 8. WORKING TREE, AS THIS REPORT DESCRIBES IT

One new probe and this report, both in `agents/tasks/LJ-1-234/`:

| file | state |
|---|---|
| `ProbeLJ1234A.agda` | green, `--safe`, exit 0, 91 non-comment non-blank lines whole, 60 charge, 1.19 s cold mean |
| `lj-1.234-report.md` | this file |

Three bisect scratch files were created and deleted during section 3.1's
bisection; none remains. `git status` also shows two pre-existing untracked
files not made by this dispatch (`agents/tasks/LJ-1-223/LJ-1.223.md`,
`scripts/tests/test_premises_stated.py`); I did not touch them. No master
edited. No file under `src/` edited. No
commit, no push, no `git checkout .`/stash/reset/clean. No `make check`; the
orchestrator runs it. ONE agda process of mine at a time, cap never raised.

**Checks run:** `scripts/lint-agda.py --check` on the probe (exit 0);
`scripts/lint-prose.py --check` on this report (to be run).

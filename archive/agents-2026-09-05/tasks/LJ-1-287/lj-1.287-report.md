# [LJ-1.287] report: cure `sucV∈`, 99.2 percent of the wing's most expensive master

STATUS: COMPLETE against the abort criterion's FIRST branch, a cure that
works, with a six-way bisect that names the mechanism and refutes both prior
diagnoses. Written incrementally (C-22). Every negative is marked
MEASURED or INFERRED, in those words. ASD-STE100 applies.

Machine at start: load 3.99 16.64 24.88 at 15:05, decaying from earlier work.
Zero agda processes at start, MEASURED by `ps aux | grep -c "[a]gda"`.

## LEAD

**A CURE WORKS. The master goes from a 480.25 s three-run control mean to a
4.10 s four-run treated mean, minus 476.15 s, minus 99.15 percent, and the
change is three lines.** My own control re-derives the premise: agda
Total 486,357 ms, of which `sucV∈` at
`src/L/Coding/EnvSupply.lagda.md:223-224` carries **483,058 ms, 99.32
percent**.

**THE COST IS NEITHER THE CALL NOR THE SUPPLIER. It is ONE conversion, and
nobody had named it.** A six-way bisect charges 438,043 ms to an identity
function whose only work is to convert `sucIter 4 δ` against
`sucV (sucV (sucV (sucV δ)))`. **Everything else is free**: the application
of `union∈Lset-suc` at the deep index, the `sucV a` against
`⋃ ⁅ a , ⁅ a ⁆s ⁆` equation at four exposed layers, and the same equation at
one layer are all below the profiler's reporting threshold.

**So the cure is to delete `sucIter` from the proof and climb the four
successor steps by `succλ`, which the module already carries as a
parameter.** `sucV∈` then disappears from the profile entirely and the new
climb costs 18 ms.

**AND THE SAME BISECT EXPLAINS THE PRIOR TASK'S VOID SEAL, which I replayed
and profiled.** `[LJ-1.283]`'s `TreatedSeal` needed a read lemma,
`lev4-mem d x h = h`, and that lemma IS the expensive conversion. **MEASURED:
the replay runs 467.53 s and charges 462,830 ms, 99.25 percent, to
`lev4-mem`, while `sucV∈` is not charged at all.** The seal cleared the site
and paid the same bill one line lower.

**AND THIS REFUTES BOTH PRIOR DIAGNOSES, including the one I wrote before I
measured.** `[LJ-1.283]`'s stated mechanism was the membership head over four
exposed `Lset ∘ sucV` layers; `v5` prices that at zero. R-35's and R-40's
shallow-index restatement, which the brief names as the two untried
candidates, is priced at 454,449 ms by `v3` and does NOT cure the site,
because it leaves the `sucIter` conversion behind.

Machine: load 4.65 before the control and 4.69 after; every figure below
carries its own load pair. One agda process of mine at all times.

## 0. THE CLOCK

Agda's own `--profile=definitions` Total is the figure of record. The wall
figure from `measure.sh` uses `time.time()`, the wall-clock epoch, which is
comparable across processes. `time.monotonic()` is NOT comparable on this
machine, and `[LJ-1.283]` section 8 records that defect.

## 1. THE CONTROL AND THE PROFILE, from ONE run

`ControlEnv.lagda.md` is `[LJ-1.283]`'s control with the module renamed, and
nothing else differs: `diff` after a name substitution is EMPTY. It carries
`module SupplyEnv` verbatim from the master, 390 in-fence non-blank lines.

`agda --profile=definitions`, `GHCRTS="-A64m -I0 -M8g"`, cap never raised,
one agda process of mine.

| figure | value |
|---|---|
| wall, `time.time()` | **487.46 s**, exit 0 |
| agda's own `--profile` Total | **486,357 ms** |
| load before to after | 4.65 to 4.69 |
| clock of record | agda's own `--profile` Total |

**THE TOP CHARGE. MEASURED, and it re-derives `[LJ-1.283]`'s figure.**

| definition | site | ms | share |
|---|---|---:|---:|
| **`SupplyEnv._._.sucV∈`** | `src/L/Coding/EnvSupply.lagda.md:223-224` | **483,058** | **99.32 percent** |
| Miscellaneous | | 2,569 | 0.53 percent |
| `SupplyEnv.someEnv` | `:415` | 103 | |
| `SupplyEnv._._.sub₁` | `:164` | 45 | |
| `SupplyEnv.envInK-imp` | `:398` | 37 | |
| `SupplyEnv._._.a∈δ₂` | `:217-218` | **12** | |
| `SupplyEnv.B₀∈σ` | `:127-131` | **11** | |
| `SupplyEnv._._.sgl∈δ₂` | `:219-220` | **10** | |
| `SupplyEnv._._.pair∈δ₃` | `:221-222` | **10** | |

`agents/tasks/LJ-1-287/runs/c1.out:2-34`.

**THE FOUR NEIGHBOURS ARE THE FINDING'S OTHER HALF.** `a∈δ₂`, `sgl∈δ₂` and
`pair∈δ₃` are the three lines directly above `sucV∈`. They build the SAME
successor chain at depths two and three. **They cost 12, 10 and 10 ms.** So
depth alone does not explain `sucV∈`. Something at the fourth step differs
in kind.

## 2. THE MECHANISM

### 2.1 THE READING, before the measurement

`sucV∈` sits in `sucK`'s `step` at `src/L/Coding/EnvSupply.lagda.md:223-224`.

```
      sucV∈ : ⟨ sucV a ∈ Lset (sucIter 4 δ) ⟩
      sucV∈ = union∈Lset-suc δ₃ ⁅ a , ⁅ a ⁆s ⁆ pair∈δ₃
```

The supplier's type is
`union∈Lset-suc : (σ x : V ℓ) → ⟨ x ∈ Lset σ ⟩ → ⟨ ⋃ x ∈ Lset (sucV σ) ⟩`.
So the body's type is `⟨ ⋃ ⁅ a , ⁅ a ⁆s ⁆ ∈ Lset (sucV δ₃) ⟩` and the
declared type is `⟨ sucV a ∈ Lset (sucIter 4 δ) ⟩`. The elaborator must
solve TWO conversions at the same place.

1. `sucV a` against `⋃ ⁅ a , ⁅ a ⁆s ⁆`, under the membership head.
2. `sucV δ₃` against `sucIter 4 δ`, under `Lset` and under the same head.

`δ₃ = sucV (sucV (sucV δ))` at `:216`, so the level `sucV δ₃` is a FOUR-deep
successor chain over the variable `δ`.

### 2.2 THE LIBRARY FACTS, which decide what can unfold

- `sucV N = N ∪ ⁅ N ⁆s` and `a ∪ b = ⋃ ⁅ a , b ⁆`
  (`/opt/homebrew/Cellar/agda/2.8.0-r3/share/agda/cubical/Cubical/HITs/CumulativeHierarchy/Constructions.agda:156-161`).
  So conversion 1 is two delta steps at the bare type `V ℓ`.
- `A ∈ sett X ix = ∥ Σ[ i ∈ X ] (ix i ≡ A) ∥ₚ`
  (`.../CumulativeHierarchy/Base.agda:42`). `_∈_` fires only when its SECOND
  argument reaches a `sett`.
- `Lset` is ALREADY `opaque` at `src/L/Constructible.lagda.md:221-223`, so
  `Lset β` never reaches a `sett` and `_∈_` stays stuck.
- `sucIter zero u = u`, `sucIter (suc n) u = sucV (sucIter n u)`
  (`src/L/Ordinal/StageArith.lagda.md:33-35`), so `sucIter 4 δ` delta-reduces
  to `sucV (sucV (sucV (sucV δ)))`.
- `⋃ x` is `UnionSet.UNION`, whose index type is
  `Σ[ i ∈ ⟪ x ⟫ ] ⟪ ⟪ x ⟫↪ i ⟫`
  (`.../CumulativeHierarchy/Constructions.agda:100-113`). Each `sucV` layer
  therefore adds one `⟪ _ ⟫` extraction over a `Lift Bool` pair.

**So the level's REPRESENTATION is a four-deep union nest, and R-40 names
exactly this shape.** R-40's own measurement is a super-linear curve: "depth
1 converts in 0.7 s, depth 3 in 18.9 s, depth 6 never inside 600 s"
(`dev/LESSONS.md:929-941`). A depth-4 site at 475 s lies on that curve.

**MY PRE-MEASUREMENT HYPOTHESIS, WHICH THE BISECT THEN REFUTED.** I read the
library and predicted that reaching WHNF of a four-layer chain is the cost,
because `⟪ s ⟫` is not a projection but a DEEP recursive presentation:
`⟪ s ⟫ = V-repr s .fst .fst` (`.../Properties.agda:220-221`), `V-repr` reads
`V-deeprepr` (`.../Properties.agda:190-193`), `V-deeprepr` is an `elimProp`
that recurses into every member (`.../Properties.agda:187`, and
`DeepMonicPresentation` carries `rec : ∀ x → DeepMonicPresentation (ix x)` at
`:172-175`), and `sett-repr X ix` builds a SET QUOTIENT `X / Kernel` with an
`isEmbedding` proof and a `seteq` path (`.../Properties.agda:147-171`). Four
layers branch 2^4 times and each node builds that structure. **The bisect
measured this hypothesis FALSE. See `v5` in section 2.3.**

### 2.3 THE BISECT, and it names ONE conversion

`Bisect.lagda.md` states six one-line definitions. Each isolates ONE step,
and `--profile=definitions` charges each of them separately, so one run
prices every step (P-t).

`agda --profile=definitions`, `GHCRTS="-A64m -I0 -M8g"`, cap never raised,
one agda process of mine. **Wall 895.58 s, exit 0, agda Total 894,718 ms.**
Load 4.22 before, 4.59 after. `agents/tasks/LJ-1-287/runs/b1.out`.

| name | what it isolates | ms |
|---|---|---:|
| `v1` | the APPLICATION alone, result type left at the supplier's own | **not charged** |
| `v2` | the same application at a SHALLOW index, `σ` abstract (R-35, R-40) | **not charged** |
| `v3` | `v2` instantiated at the deep index | **454,449** |
| `v4` | the `sucIter` conversion ALONE, `p = p` | **438,043** |
| `v5` | `sucV a` against `⋃ ⁅ a , ⁅ a ⁆s ⁆`, under FOUR exposed layers | **not charged** |
| `v6` | the same conversion under ONE exposed layer | **not charged** |
| Miscellaneous | | 2,226 |

**"Not charged" means the definition does not appear in the profile at all**,
so its cost falls below the profiler's own reporting threshold and inside the
2,226 ms Miscellaneous line. `agents/tasks/LJ-1-287/runs/b1.out:2-5` lists
FOUR lines in total: Total, Miscellaneous, `v3` and `v4`.

**THE ANSWER. MEASURED.** The whole cost is ONE conversion, and it is
conversion 2, not conversion 1:

```
      v4 : (δ a : V ℓ)
         → ⟨ sucV a ∈ Lset (sucV (sucV (sucV (sucV δ)))) ⟩
         → ⟨ sucV a ∈ Lset (sucIter 4 δ) ⟩
      v4 δ a p = p
```

**`sucIter 4 δ` against `sucV (sucV (sucV (sucV δ)))` costs 438,043 ms. That
is 438 seconds for an identity function.**

### 2.4 THE FOUR NEGATIVES THE BISECT BUYS

- **MEASURED FALSE. The application of `union∈Lset-suc` at a concrete deep
  index is expensive.** `v1` does exactly that and is not charged.
- **MEASURED FALSE. The `sucV a` against `⋃ ⁅ a , ⁅ a ⁆s ⁆` conversion is
  expensive.** `v5` is that conversion with FOUR successor layers standing in
  the level, and it is not charged. `v6` is the same at one layer. **So
  `[LJ-1.283]`'s stated mechanism, the membership head over four exposed
  layers, is refuted at its own site**, and its `TreatedBridge` arm was
  removing a conversion that was already free.
- **MEASURED FALSE. My own deep-presentation hypothesis in section 2.2.**
  Reaching WHNF of a four-layer chain is not the cost by itself. `v5` forces
  the same level and pays nothing.
- **MEASURED FALSE. The R-35 and R-40 shallow-index restatement cures this
  site.** `v3` IS that restatement, applied at the deep index, and it costs
  454,449 ms. **It does not cure the site, because it leaves the `sucIter`
  conversion behind.** I therefore did not spend a run on
  `TreatedShallow.lagda.md`, which I had already written; `v3` prices it.

### 2.5 WHY THE MISMATCH COSTS AND THE MATCH DOES NOT. INFERRED.

`v5` and `v4` differ in ONE way. In `v5` the two levels are written
identically, so the conversion checker sees the same term on both sides and
never has to reduce it. In `v4` the two levels are two SPELLINGS of the same
value, `sucIter 4 δ` and the explicit chain. Neither side is syntactically
the other, so the checker must reduce both, and reducing either one to WHNF
builds the deep monic presentation described in section 2.2 on BOTH sides,
with no shared subterm to short-circuit on. **INFERRED**, from the two
measured figures and the library sources; I did not read Agda's conversion
checker.

**This sharpens R-40 rather than confirming it.** R-40 says depth is the
trigger. **Here depth alone is free and the MIXED SPELLING is what costs.**
`envSetK` at `src/L/Coding/EnvSupply.lagda.md:143-146` is the control for
that claim inside the same file: it uses `sucIter 4 σ` at a depth-4 level
too, its supplier `landed` states the same `sucIter 4 σ`
(`src/L/Coding/Key.lagda.md:480`), and **it costs 11 ms.** Same depth, one
spelling, no charge.

## 3. THE TWO VOID ARMS, VERIFIED BY DIFF SO I DO NOT REBUILD ONE

I diffed both `[LJ-1.283]` arm files against its control. Command:
`diff <(sed 's/TreatedBridge/ControlEnv/' TreatedBridge.lagda.md) ControlEnv.lagda.md`.

- **`TreatedBridge.lagda.md`, 485.80 s, VOID.** It adds
  `sucEq : ⋃ ⁅ a , ⁅ a ⁆s ⁆ ≡ sucV a`, `sucEq = refl`, and rewrites the body
  as `subst (λ w → ⟨ w ∈ Lset (sucIter 4 δ) ⟩) sucEq (union∈Lset-suc ...)`.
  `agents/tasks/LJ-1-283/TreatedBridge.lagda.md:234-238`.
- **`TreatedSeal.lagda.md`, 481.28 s, VOID.** It adds an `opaque` block with
  `lev4`, `lev4-mem` and `lev4∈λ`
  (`agents/tasks/LJ-1-283/TreatedSeal.lagda.md:124-134`), moves `Lset-mono`
  onto `lev4 δ`, and splits the body into `sucV∈₄` at the level `δ₄ = sucV δ₃`
  plus a `lev4-mem` read (`:247-254`).

**WHAT THIS TOLD ME BEFORE I RAN ANYTHING.** `TreatedSeal` leaves ONE
conversion in the file that could still be heavy, and it is NOT the one its
author was attacking. That re-aimed my arm onto the conversion itself.

### 3.1 AND THE BISECT EXPLAINS WHY THE SEAL WAS VOID. MEASURED.

`TreatedSeal`'s own read lemma re-creates the expensive conversion, one line
below the seal that was supposed to remove it.

```
  opaque
    lev4 : V ℓ → V ℓ
    lev4 d = sucIter 4 d

    lev4-mem : (d x : V ℓ) → ⟨ x ∈ Lset (sucV (sucV (sucV (sucV d)))) ⟩
             → ⟨ x ∈ Lset (lev4 d) ⟩
    lev4-mem d x h = h
```

`agents/tasks/LJ-1-283/TreatedSeal.lagda.md:124-131`. **`lev4` unfolds inside
its own `opaque` block, so `lev4-mem d x h = h` is `v4` VERBATIM: the
identity function whose only work is to convert `sucIter 4 d` against
`sucV (sucV (sucV (sucV d)))`.** `v4` costs 438,043 ms.

**So the seal did not fail. It MOVED the 438 seconds from `sucV∈` into
`lev4-mem`, and `[LJ-1.283]` did not profile the arm, so nobody saw it.** I
replayed the arm as `SealReplay.lagda.md`, a copy with the module renamed and
nothing else changed, under `--profile=definitions`.

**THE REPLAY. MEASURED, and it confirms the reading exactly.**

| figure | value |
|---|---|
| wall | **467.53 s**, exit 0, load 3.81 to 6.65 |
| agda Total | **466,314 ms** |
| **`SealReplay.SupplyEnv.lev4-mem`** | **462,830 ms, 99.25 percent** |
| `SealReplay.SupplyEnv._._.sucV∈` | **not charged.** `grep -c` returns 0 |

`agents/tasks/LJ-1-287/runs/s1.out:2-4`. **The seal DID clear `sucV∈`
completely. It then paid the same 462 seconds in the read lemma it needed to
make the seal usable.** That is the whole story of `[LJ-1.283]`'s minus 0.19
percent, and it is the sharpest instance of P-y's blind spot on record: P-y
prices a seal by who must look inside, and here the ONE definition that looks
inside is the one that carries the entire cost.

## 4. THE TREATED ARM, AND IT CURES THE SITE

### 4.1 THE ONE CHANGE

`TreatedNoIter.lagda.md`. **`diff` against the control shows the module name
and THREE substantive lines, and nothing else in the file differs.** The
change deletes `sucIter` from `step` and climbs the four successor steps by
the module's own `succλ` parameter, one step per application. That is R-40's
own cure, "climb by small closures", applied to the SPELLING rather than to
the depth.

```
      Lset-mono {α = lam} {β = sucV δ₃}
        δ₄∈λ
        sucV∈
      where
      ...
      δ₄∈λ : ⟨ sucV δ₃ ∈ lam ⟩
      δ₄∈λ = succλ δ₃ (succλ δ₂ (succλ δ₁ (succλ δ δ∈)))
      ...
      sucV∈ : ⟨ sucV a ∈ Lset (sucV δ₃) ⟩
      sucV∈ = union∈Lset-suc δ₃ ⁅ a , ⁅ a ⁆s ⁆ pair∈δ₃
```

`succλ` is already a parameter of `module SupplyEnv` at
`src/L/Coding/EnvSupply.lagda.md:108`, and `B.suc^∈λ` at
`src/L/Coding/Bound.lagda.md:97-99` is itself defined by iterating `succλ`,
so the arm imports nothing new and proves nothing new. **The body of `sucV∈`
is UNCHANGED. Only its declared level changes, from `sucIter 4 δ` to
`sucV δ₃`.**

### 4.2 THE RUNS

Cycle 1 is control first, as the brief requires. Cycle 3 reverses the order.
Every arm is a cold run: `measure.sh` deletes the probe's own `.agdai` before
each one. Every figure carries its own load pair.

| cycle | run | arm | seconds | load before to after | agda Total |
|---|---|---|---:|---|---:|
| 1 | c1 | `ControlEnv` | **487.46** | 4.65 to 4.69 | 486,357 ms |
| 1 | b1 | `Bisect` | 895.58 | 4.22 to 4.59 | 894,718 ms |
| 1 | t1 | **`TreatedNoIter`** | **4.35** | 5.42 to 5.38 | 3,406 ms |
| 2 | c2 | `ControlEnv` | **476.85** | 4.11 to 5.95 | not profiled |
| 2 | t2 | **`TreatedNoIter`** | **3.74** | 5.95 to 6.19 | 3,444 ms |
| 2 | t3 | **`TreatedNoIter`** | **3.65** | 6.19 to 6.09 | not profiled |
| 3 | t4 | **`TreatedNoIter`** | **4.65** | 4.79 to 4.81 | not profiled |
| 3 | c3 | `ControlEnv` | **476.45** | 4.81 to 4.58 | not profiled |
| 4 | s1 | `SealReplay`, `[LJ-1.283]`'s void arm | **467.53** | 3.81 to 6.65 | 466,314 ms |

**THE PAIRED DELTAS. MEASURED**, exit 0 every run, `--safe --guardedness`,
no heap wall, and no run near the 30-minute wall.

| cycle | order | control | treated | delta | percent |
|---|---|---:|---:|---:|---:|
| 1 | control first | 487.46 | 4.35 | **minus 483.11** | **minus 99.11** |
| 2 | control first | 476.85 | 3.74 | **minus 473.11** | **minus 99.22** |
| 3 | **treated first** | 476.45 | 4.65 | **minus 471.80** | **minus 99.02** |

- **Control, n = 3**: 487.46, 476.85 and 476.45 s, mean **480.25 s**, spread
  **2.3 percent**. That reproduces `[LJ-1.276]`'s delivered figure of
  482.73 s (`agents/tasks/LJ-1-276/lj-1.276-report.md:84`) and
  `[LJ-1.283]`'s 482.20 s control.
- **Treated, n = 4**: 4.35, 3.74, 3.65 and 4.65 s, mean **4.10 s**, spread
  1.00 s in absolute terms.
- **THE WHOLE-SERIES FIGURE: 480.25 s to 4.10 s, MINUS 476.15 s, MINUS 99.15
  percent.**
- **THE ORDER DOES NOT MOVE IT.** Cycle 3 ran the treated arm FIRST and the
  control second, and its delta is minus 99.02 percent against minus 99.11
  and minus 99.22 in the two control-first cycles. **MEASURED: no position
  effect.**
- **THE EFFECT IS TWO ORDERS OF MAGNITUDE LARGER THAN ANY NOISE THE RECORD
  HAS MEASURED.** The widest own-file spread on record is 6.4 percent
  (`[LJ-1.152]`, `agents/tasks/LJ-1-152/lj-1.152-report.md:154`). This delta
  is 99.15 percent.

### 4.3 THE PROFILE OF THE TREATED ARM, which is the proof that the cure hit

`agents/tasks/LJ-1-287/runs/t1.out`.

| definition | control ms | treated ms |
|---|---:|---:|
| **`SupplyEnv._._.sucV∈`** | **483,058** | **not charged at all** |
| `SupplyEnv._._.δ₄∈λ`, the new climb | absent | **18** |
| `SupplyEnv.someEnv` | 103 | 104 |
| `SupplyEnv._._.sub₁` | 45 | 47 |
| `SupplyEnv.envInK-imp` | 37 | 36 |
| `SupplyEnv.B₀∈σ` | 11 | 12 |
| `SupplyEnv._._.pair∈δ₃` | 10 | 10 |
| `SupplyEnv._._.a∈δ₂` | 12 | 10 |
| Total | 486,357 | **3,406** |

**`sucV∈` does not appear in the treated profile.**
`grep -c "sucV∈" agents/tasks/LJ-1-287/runs/t1.out` returns 0, and the same
grep on `runs/t2.out` returns 0. Every other definition in the file keeps its
figure to within a few milliseconds, so nothing moved elsewhere and nothing
was traded away. **The new four-step climb costs 18 ms.** The second profiled
treated run agrees: Total 3,444 ms against 3,406 ms
(`agents/tasks/LJ-1-287/runs/t2.out:2`).

### 4.4 THE SWEEP, because a refutation measures ONE site (C-42)

**THE SHAPE IS: a `sucIter` at a NUMERAL depth on one side of a conversion,
and an explicit `sucV` chain on the other.** `grep -rn "sucIter" src/` returns
34 occurrence lines outside `src/L/Ordinal/StageArith.lagda.md`. Most are safe, because
both sides of the conversion carry the same spelling.

- `src/L/Coding/EnvSupply.lagda.md:143-146`, `envSetK`. **SAFE, MEASURED at
  11 ms.** It uses `sucIter 4 σ`, and its supplier `landed` at
  `src/L/Coding/Key.lagda.md:480` states `sucIter 4 σ` too. One spelling.
- `src/L/Coding/Bound.lagda.md:107,114,152` and
  `src/L/Coding/Key.lagda.md:95,98,101`. **SAFE by reading**: the depth is a
  VARIABLE `k`, `d` or `e`, so `sucIter` never reduces and no chain is built.
- **`src/L/Coding/Key.lagda.md:424-429` CARRIES THE SHAPE. UNMEASURED.**
  `α = sucIter 3 σ` at `:424`, and `σ∈α` at `:428-429` is proved by
  `∈sucV-inl {A = sucIter 2 σ} {x = σ} (∈sucV-inl {A = sucIter 1 σ} {x = σ}
  (self∈sucV σ))`. `self∈sucV σ : ⟨ σ ∈ sucV σ ⟩` must convert with
  `⟨ σ ∈ sucIter 1 σ ⟩`, and the outer result must convert with
  `⟨ σ ∈ sucIter 3 σ ⟩`. **That is the mixed spelling at depths 1 to 3.**
  **NOBODY HAS PROFILED `src/L/Coding/Key.lagda.md`**, so I state this as a
  CANDIDATE and not a claim. The next brief should profile that master before
  it prices anything there.

### 4.5 WHAT A BUILD BRIEF WOULD SAY, since the first abort branch fired

The landing edit is `TreatedNoIter.lagda.md`'s diff, applied to
`src/L/Coding/EnvSupply.lagda.md`. **Three lines change and two are added.**

1. `:210`, `Lset-mono {α = lam} {β = sucIter 4 δ}` becomes
   `Lset-mono {α = lam} {β = sucV δ₃}`.
2. `:211`, `(B.suc^∈λ 4 δ δ∈)` becomes `δ₄∈λ`.
3. After `:216`, add
   `δ₄∈λ : ⟨ sucV δ₃ ∈ lam ⟩` and
   `δ₄∈λ = succλ δ₃ (succλ δ₂ (succλ δ₁ (succλ δ δ∈)))`.
4. `:223`, the declared level becomes `Lset (sucV δ₃)`.

**PRICE, basis = this probe, which is the delivered content verbatim (DD8).**
The master should fall from 482.73 s to about 25 s. **That figure is a
PROJECTION and not a measurement**: my control is `module SupplyEnv` alone at
390 in-fence lines, and the master is 833 lines. `[LJ-1.275]` measured the
443 lines outside the env block at about 5 s
(`agents/tasks/LJ-1-275/lj-1.275-report.md:295-320`), and my treated control
is 4.10 s, so about 9 s of content plus the master's own fixed cost. **I round
up to 25 s because I did not run the master.** The build brief should measure
the master itself.

**WHAT THE BUILD MUST NOT ASSUME.** `B.suc^∈λ` stays in the file: `envSetK`
at `:143-146` still uses it and still costs 11 ms. **Only `sucK`'s `step`
changes.**

## 5. PREMISES, VERIFIED OR REFUTED

| the brief's premise | verdict |
|---|---|
| `sucV∈` at `:223-224` carries 99.2 percent | **VERIFIED.** My own run: 483,058 ms of 486,357 ms, **99.32 percent** |
| the file carries zero `opaque` in 833 lines | **VERIFIED.** `grep -c opaque src/L/Coding/EnvSupply.lagda.md` returns 0 |
| the layer-cap seal is measured VOID | **VERIFIED, and now EXPLAINED BY MEASUREMENT.** It cleared `sucV∈` completely and paid 462,830 ms in its own read lemma `lev4-mem`. Section 3.1 |
| the equation-bridge arm is measured VOID | **VERIFIED, and now EXPLAINED.** It removed conversion 1, which `v5` and `v6` price at zero |
| the cost may be in the SUPPLIER, not the call | **REFUTED. MEASURED.** `v1` applies `L.Coding.Key`'s already-compiled `union∈Lset-suc` at the same deep index and is not charged at all |
| R-40 is a live candidate, and its cure is to climb by small closures | **HALF VERIFIED, HALF REFUTED.** The CURE is right and it is what I ran. The stated MECHANISM, depth, is refuted: `v5` holds depth 4 and pays nothing. What costs is the mixed SPELLING |
| R-35 says state the membership at the SMALL INDEX | **REFUTED as a cure at this site. MEASURED.** `v3` is exactly that restatement and costs 454,449 ms |
| `union∈Lset-suc` landed in `src/L/Coding/Key.lagda.md:504` | **VERIFIED**, and the master does NOT import it. It carries its own 55-line duplicate at `src/L/Coding/EnvSupply.lagda.md:148-202` |

## 6. CALL OR SUPPLIER: NEITHER

**The brief offers two sites and the answer is a third. MEASURED.**

- **NOT THE SUPPLIER.** `v1` calls `L.Coding.Key`'s `union∈Lset-suc`, which
  is compiled and read from its interface, at the same concrete deep index
  and with the same concrete pair argument. **It is not charged at all.** The
  supplier's own elaboration inside the master is cheap too: `sub₁` 45 ms,
  `sub₂` 11 ms, `member` 20 ms, `sat` 19 ms.
- **NOT THE CALL either, in the sense the brief means.** The application is
  free. What costs is the conversion that the DECLARED TYPE forces after the
  application: `sucIter 4 δ` against `sucV (sucV (sucV (sucV δ)))`.
- **THE SITE IS THE SPELLING OF THE LEVEL IN `sucV∈`'s DECLARED TYPE**, at
  `src/L/Coding/EnvSupply.lagda.md:223`, and it is fixed there by
  `Lset-mono {β = sucIter 4 δ}` at `:210` and `B.suc^∈λ 4 δ δ∈` at `:211`.
  **The cure belongs in this master, not in `src/L/Coding/Key.lagda.md`.**

## 7. IS `sucV∈` AVOIDABLE ENTIRELY

**NO for the statement, YES for the shape. MEASURED by reading the consumers.**

- `sucV∈` has exactly ONE consumer, three lines above it:
  `Lset-mono {α = lam} {β = sucIter 4 δ} (B.suc^∈λ 4 δ δ∈) sucV∈` at
  `src/L/Coding/EnvSupply.lagda.md:210-212`.
- Its parent `sucK` at `:204` is a REQUIRED field. `module EnvClosure` takes
  `(sucK : (a : S) → ⟨ a ∈ K ⟩ → ⟨ sucV a ∈ K ⟩)` at
  `src/L/Coding/Key.lagda.md:568`, and `numK` at `:588` and the generic
  environment builder at `:607` both call it. `module SupplyMerge` in the
  master takes the same field at `src/L/Coding/EnvSupply.lagda.md:672` and
  `:702`. **So `sucK` cannot be dropped or weakened.**
- **HOISTING BUYS NOTHING HERE. MEASURED by counting.** `sucV∈` is a `where`
  binding of `step`, and `step` is elaborated ONCE. The file has one `sucK`
  and the profile charges one definition. There is no per-instance repeat to
  hoist out of.
- **BUT `sucK`'s STATEMENT never mentions a successor chain.** It is
  `⟨ a ∈ Lset lam ⟩ → ⟨ sucV a ∈ Lset lam ⟩` with `lam` abstract. The
  four-deep chain `sucIter 4 δ` is an artifact of the PROOF at `:210` and
  `:223`. **So the shape is free to change and nothing outside the file sees
  it.** That is what the treated arm changes, and the change is worth
  483.11 s.

**SO THE ABORT CRITERION'S FOURTH BRANCH DOES NOT FIRE, and the first one
does.** `sucV∈` cannot be dropped, weakened or hoisted. It can be RESPELLED,
and that is enough.

## 8. DD4, WITH ITS AXIS

**AXIS NAMED (C-46): DD4's own axis is AC-against-GCH**, the one
`scripts/ledger.py` computes from `reuse.ac_root` and `reuse.gch_root`.

**THE CURE DOES NOT MOVE THE RATIO, and I do not claim it does.**
`src/L/Coding/EnvSupply.lagda.md` is a LEAF. **MEASURED, re-derived today:**
`grep -rn "L.Coding.EnvSupply" src/` returns two lines, the master's own
header at `:17` and the catalog line at `src/Everything.lagda.md:382`. No
master imports it, so it sits in NEITHER trophy closure and its seconds are
outside the 41.1 percent figure entirely. `[LJ-1.276]` measured the block
NEUTRAL on this axis (`agents/tasks/LJ-1-276/lj-1.276-report.md:124-127`).

**WHAT THE CURE DOES TO REUSE, which is the question DD4 actually asks.**

- **The cure REMOVES a supplier and adds none.** It replaces
  `B.suc^∈λ 4 δ δ∈`, which is `succλ` iterated through `sucIter`
  (`src/L/Coding/Bound.lagda.md:97-99`), by four direct applications of
  `succλ`. `succλ` is already a PARAMETER of `module SupplyEnv` at
  `src/L/Coding/EnvSupply.lagda.md:108`. **So the step now rests only on the
  module's own tower-neutral parameter and on nothing that names a stage
  arithmetic.** A second tower that supplies `succλ` supplies this step
  unchanged.
- **It proves nothing new and it imports nothing new.** The body of `sucV∈`
  is byte-identical to the master's. Only the declared level changes.
- **It writes the same content GENERIC in the sense DD4 means**, because the
  climb is stated over the module's parameter rather than over a numeral
  iterate that only the Def side defines.
- **AND THE SITE CARRIES A DD4 DEFECT ALREADY, MEASURED BY GREP.**
  `union∈Lset-suc` is written TWICE: `src/L/Coding/Key.lagda.md:504-560` and
  `src/L/Coding/EnvSupply.lagda.md:148-202`, about 55 lines each, differing
  only in whether the two arguments are written `S` or `V ℓ`. The master
  imports `L.Coding.Key` at `:69` for `envSetNumeral∈` and does not take
  `union∈Lset-suc` from it. **`[LJ-1.263]` already built and ran the imported
  form**: `ReRun1254.agda`, the same probe minus its local copy, exit 0 at
  442.86 s (`agents/tasks/LJ-1-263/lj-1.263-report.md:30` and `:52-55`).
- **THE DEDUP IS A LINE LEVER, NOT A SECONDS LEVER (P-q).** The profile
  charges the local `union∈Lset-suc` family under 100 ms in total
  (`sub₁` 45 ms, `member` 20 ms, `sat` 19 ms, `sub₂` 11 ms;
  `agents/tasks/LJ-1-287/runs/c1.out`). Removing 55 duplicated lines buys
  about 55 lines and under 100 ms. **It must not be sold as a cure for the
  483 s.**

## 9. A LAW CANDIDATE, WITH ITS MEASUREMENT

I propose this as a new entry in `dev/LESSONS.md`. **The orchestrator assigns
the ID.** A law is not admitted without its measurement, so here is mine.

**Rule (proposed).** A stage iterate written with a recursive iterator at a
NUMERAL depth (`sucIter 4 δ`) and the explicit successor chain it reduces to
(`sucV (sucV (sucV (sucV δ)))`) are definitionally equal and RUINOUS to
convert against each other. Choose ONE spelling for a level and carry it
through every type in the proof; never let a supplier state one spelling and
a consumer the other. The depth itself is free when both sides agree.

**Measured (`[LJ-1.287]`, 2026-08-15).** At depth 4, the conversion alone, as
the body of an identity function, costs **438,043 ms**. The SAME depth with
both sides spelled identically is not charged by the profiler at all. At the
real site, `src/L/Coding/EnvSupply.lagda.md:223-224`, removing the mixed
spelling takes the master from a **480.25 s control mean to a 4.10 s treated
mean, minus 99.15 percent**, with three changed lines and no new proof.
Control n = 3, treated n = 4, order reversed in the third cycle.

**Relation to R-40.** R-40 says the trigger is DEPTH. **This measurement says
depth alone is free and the mixed spelling is the trigger.** R-40's CURE,
climb by small closures, is still the right cure; its stated mechanism needs
the amendment. `envSetK` at `src/L/Coding/EnvSupply.lagda.md:143-146` is the
in-file control: depth 4, one spelling, 11 ms.

**Relation to P-y.** P-y prices a seal by the definitions that must see
INSIDE it. **Here that count is 2 and the seal still bought nothing, because
one of those two insiders carried the whole cost.** The measurement adds a
line to P-y: when the sealed object is a LEVEL, its read lemma inherits the
conversion the seal was meant to stop, so price the READ LEMMA and not only
the count.

**Relation to C-50.** C-50 says profile before you cure. **This task is C-50's
second instance in two days.** Two arms were funded on a mechanism that a
one-run bisect priced at zero, and my own pre-measurement reading of the
Cubical sources reached the same wrong answer. The bisect cost ONE run.

## 10. THE ABORT CRITERION, ANSWERED BRANCH BY BRANCH

| branch fixed before the run | verdict |
|---|---|
| **A CURE WORKS** | **FIRED.** 480.25 s control mean to 4.10 s treated mean, minus 99.15 percent, three changed lines, n = 3 and n = 4. A build brief is writable |
| the cost is in `union∈Lset-suc`, not the call | **DID NOT FIRE. MEASURED FALSE** by `v1`. The cure belongs in this master |
| every cure fails, so this is a payable floor | **DID NOT FIRE.** It is not a floor |
| the two lines are avoidable entirely | **DID NOT FIRE.** `sucK` is a required field. The lines are not avoidable, they are RESPELLABLE |
| a wall | **DID NOT FIRE. MEASURED.** Longest run 895.58 s, exit 0. No heap exhaustion, cap never raised |

## ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-283/lj-1.283-report.md`, read WHOLE as the brief
  requires.** ONE line: `:235`, the `SupplyEnv._._.sucV∈` row at 475,710 ms.
  **TAKEN:** the localization, and the two arm figures I must not rebuild. I
  re-derived the charge with my own run rather than quoting it.
- **`agents/tasks/LJ-1-283/TreatedBridge.lagda.md` and
  `TreatedSeal.lagda.md`, the arm files.** ONE line:
  `TreatedSeal.lagda.md:248`, `sucEq = refl`. **TAKEN:** the diff of each arm
  against the control, which is how I know `TreatedSeal` leaves exactly one
  conversion in the file and still costs 481 s. That fact re-aimed my arm.
- **`agents/tasks/LJ-1-276/lj-1.276-report.md`.** ONE line: `:124`, "Axis 1,
  AC-against-GCH (DD4's own axis): NEUTRAL, paid once. MEASURED." **TAKEN:**
  the DD4 verdict for the master, which forbids justifying my cure by the
  ratio.
- **`agents/tasks/LJ-1-263/lj-1.263-report.md`.** ONE line: `:30`, the
  `ReRun1254.agda` row, exit 0 at 442.86 s. **TAKEN:** the fact that
  IMPORTING `union∈Lset-suc` from `L.Coding.Key` instead of duplicating it
  was already built and already measured, so I spent no run on it.
- **`dev/LESSONS.md` R-40, FULL entry at `:929-948`.** **TAKEN:** the CURE,
  "climb by small closures", which is my arm. **NOT TAKEN, and REFUTED at
  this site:** its stated mechanism, that depth is the trigger. `v5` holds
  depth 4 fixed and pays nothing. I propose the amendment in section 9.
- **`dev/LESSONS.md` R-35, FULL entry at `:782-808`.** **TAKEN as a candidate
  and then REFUTED by measurement:** "state the membership at the SMALL
  INDEX" is `v3`, and `v3` costs 454,449 ms. I wrote
  `TreatedShallow.lagda.md` for it and did not run it, because `v3` prices it
  in one sixth of the time.
- **`dev/LESSONS.md` P-i, FULL entry at `:203-300`.** **TAKEN:** class (1)
  and the layer-cap sub-rule, which `[LJ-1.283]` measured VOID here. I did
  not rebuild it.
- **`archive/dev/TASKS-archived.md`, SHAPE ONLY and never a claim.** ONE
  line: `:189`, `[L3.32-T154]`, "FOUND, one wall: the depth-6 ordinal
  witness; cured 631 s to 59 s in harness". **TAKEN AS SHAPE:** that a
  successor-depth wall is cured by restating the witness and not by sealing
  it. **WHAT WOULD NOT TRANSFER:** the 631 s and 59 s price a retired tree
  and a different depth, and P-l forbids carrying them here. I carried none.
- **The Cubical library, not the archive.**
  `.../CumulativeHierarchy/Properties.agda:187-221` and
  `.../CumulativeHierarchy/Constructions.agda:156-161`. **TAKEN:** the
  mechanism in section 2.2, that `⟪ _ ⟫` is a deep recursive presentation
  and not a projection.

## LITERATURE USED (DD18)

Nothing in the literature governs elaboration cost.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Everything I wrote is in `agents/tasks/LJ-1-287/`:

- `LJ-1.287.md`, the pinned brief, written first.
- `lj-1.287-report.md`, this file.
- `ControlEnv.lagda.md`, the control. `[LJ-1.283]`'s control with the module
  renamed and nothing else changed. GREEN, exit 0.
- `Bisect.lagda.md`, six one-line definitions that separate the steps.
  GREEN, exit 0.
- **`TreatedNoIter.lagda.md`, the cure.** GREEN, exit 0. Three substantive
  lines differ from the control.
- `TreatedShallow.lagda.md`, the R-35 and R-40 shallow-index arm. **WRITTEN
  AND NOT RUN**, because `v3` prices it at 454,449 ms. It is left in the tree
  as the record of a refuted candidate.
- `SealReplay.lagda.md`, `[LJ-1.283]`'s `TreatedSeal` with the module
  renamed and nothing else changed, profiled to locate its 481 s. GREEN,
  exit 0.
- `Min.lagda.md`, the two lines alone, held in reserve and not run.
- `measure.sh`, `series.sh`, `timings.csv`, `runs/`.

Every file that ran typechecks `--safe --guardedness`, exit 0, zero
postulates, zero holes, zero heap walls. One agda process of mine at all
times, `GHCRTS="-A64m -I0 -M8g"`, cap never raised.
`scripts/lint-prose.py --check` and `scripts/lint-agda.py --check` exit 0 on
everything I wrote.

**No master edited. No `src/` edited.** No `src/Everything.lagda.md`, no
`dev/PLAN.md`, no `dev/ledger.toml`, no `src/L/Choice/Name.lagda.md`. I did
not touch `src/L/GCH.lagda.md` or `agents/tasks/LJ-1-286/`. **I did not write
into `agents/tasks/LJ-1-283/`**: I read its files and I copied its control
and its seal arm into my own directory before I ran either. No commit, no
push, no `git checkout .`, no stash, no reset, no clean. I did not run
`make check`. `scripts/check-probes.py --check` exits 0.

`git status --porcelain` shows `agents/tasks/LJ-1-287/` as the only path I
created. It also shows `scripts/dispatch_policy.py` and
`scripts/tests/test_dispatch_clock.py` modified and
`agents/tasks/LJ-1-223/`, `agents/tasks/LJ-1-288/` and `dev/vendors.toml`
untracked. **None of those five is mine.**

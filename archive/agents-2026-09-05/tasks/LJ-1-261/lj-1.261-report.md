# LJ-1.261 report: the finite-supremum merge, the third unpriced L-row

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. One Agda slot held.
No master edited. No commit, no push. Written incrementally (C-22). Every
negative is MEASURED or INFERRED, in those words.

## 0. LEAD

**The merge builds, and `finSetK` is then SUPPLIED rather than assumed.**
MEASURED, exit 0, `ProbeLJ1261.agda`.

**The three `consK-*` close with it supplied.** MEASURED, exit 0,
`ProbeLJ1261Closure.agda`: `ConsKClosed` is instantiated with `numK0` and
`pairK` from `Bound`, `sucK` from `[LJ-1.254]` (green there), and `finSetK`
from this probe. The abort criterion IT BUILDS is met, so this report stops.

**The merge is 148 in-fence lines**, 70 of union algebra support and 78 of
the merge and its consumer. The two-ordinal merge plus the fold (`union2∈λ`,
`merge2`, `finSup`) is 48 lines, against `union∈Lset-suc`'s 52. **The first
attempt walled**; the cure is recorded in section 3.

## 1. MACHINE AND PROCESS DISCIPLINE

ONE Agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised. No run past
20 minutes except the two interrupted walls named in section 3. No heap
exhaustion. The first successful check is the discarded warm-up; three kept
runs follow.

| run | file | exit | user s | real s | load |
|---|---|---:|---:|---:|---|
| warm-up (discarded) | `ProbeLJ1261.agda` | 0 | 1.08 | 2.04 | 4.71 |
| kept 1 | `ProbeLJ1261.agda` | 0 | 1.07 | 1.21 | 4.71 |
| kept 2 | `ProbeLJ1261.agda` | 0 | 1.06 | 1.19 | 4.71 |
| kept 3 | `ProbeLJ1261.agda` | 0 | 1.09 | 1.22 | 4.65 |

Mean user time of the three kept runs: **about 1.07 s**, at load about 4.7.
The closure probe checks in **1.45 s user / 2.47 s real**.

## 2. WHAT BUILT (MEASURED, exit 0)

`agents/tasks/LJ-1-261/ProbeLJ1261.agda`, module
`Supply (lam) (ordλ) (succλ) (∅∈λ)`. Nothing names a tower (DD4).

`finSetK : (n : ℕ) (h : Fin n → V ℓ) → ((i : Fin n) → ⟨ h i ∈ Lset lam ⟩)
→ ⟨ finSet n h ∈ Lset lam ⟩`. The chain: `Lset-out′` decomposes each member
to a stage `δᵢ ∈ lam` with `h i ∈ Lset (sucV δᵢ)`; finite choice lifts the
family; `finSup` merges the successor stages into one `τ ∈ lam`; `Lset-fin`
(re-derived, `Key.lagda.md:130-135`) closes at `Lset (sucV τ)`; `succλ`
climbs once.

The new ordinal fact, named (C-36): **a successor-closed ordinal is closed
under finite binary unions of its members.** `union2∈λ : a ∪ b ∈ lam` from
`a, b ∈ lam` ordinals. It is proved by `ord-tri` and extensionality: if
`a ∈ b` then `a ∪ b = b`, if `a = b` then `a ∪ b = a`, if `b ∈ a` then
`a ∪ b = a`.

| term | what it is | body lines |
|---|---|---:|
| `union2∈λ` | the two-ordinal merge into `lam` | **16** |
| `merge2` | binary merge, direct stage `sucV a ∪ sucV b` | **10** |
| `finSup` | the n-ary fold over `Fin n` | **22** |
| `finSetK` | the supply | **30** |
| union algebra support (`∈ₛ∪l/r`, `∈∪l/r`, `∪-ord`, `union-idem`, `union-eq`, `∪-comm`) | the set-algebra the union approach needs | **70** |
| `Lset-fin` | re-derived from `FinOf.finSet∈𝒟ₒ` | **10** |

Total new content in the probe: **148 lines** in `Supply` plus 10 for the
re-derived `Lset-fin`, against `union∈Lset-suc`'s 52.

## 3. THE WALL, AND ITS CURE (P-i, MEASURED)

The first attempt built `merge2` by case analysis on `ord-tri` and returned
the merged stage as a `Σ` whose first projection is that `Sum.rec`. Projecting
`m2 .fst` and `m2 .snd` forces normalization of `ord-tri`, a double
well-founded induction. **MEASURED wall:** the full probe did not finish in
1200 s (interrupted at the 20-minute mark), and the bisected `merge2`-only
file reached about 8.7 GB RSS at 100 percent CPU before I killed it. This is
P-i class 1/3: a heavy operator welded into a returned stage.

**The cure is P-i [A]: keep every stage a DIRECT term.** `merge2`'s stage is
`sucV a ∪ sucV b`, never an `ord-tri` projection; `ord-tri` appears only in
proofs of propositions. After the cure the whole merge checks in about 1 s.

A second, separate slowness is recorded for the record: re-deriving
`union∈Lset-suc` (`[LJ-1.254]`'s copy) in this probe cost about 7 minutes
(satisfaction at a concrete carrier elaborated fresh here, P-m/P-n), so the
closure probe imports `sucK` from `[LJ-1.254]` instead of re-deriving it.
This is why the three-`consK-*` re-run is a separate file.

## 4. WAS THE MERGE ALREADY DELIVERED? (MEASURED FALSE)

Checked `src/` first. `Lset-fin` (`Key.lagda.md:130-135`) is the stage form
and lands in `Lset (sucV σ)`, never in `Lset lam`. `boundingOrd`
(`Ordinal.lagda.md:154`) and `bound2` (`:185`) bound a family by one ordinal,
but state nothing about membership in a fixed limit `lam`. No lemma in `src/`
concludes `⋃ _ ∈ lam` or `finSet n h ∈ Lset lam`. The merge-to-`lam` content
is genuinely new. MEASURED by grep and by reading the three sites.

## 5. DD4 (THE TOWER ANSWER)

**The merge stayed tower-neutral.** `finSup`, `union2∈λ` and `finSetK` are
stated over `(lam, ordλ, succλ, ∅∈λ)` from the first line and name no tower.
The J tower re-instantiates unchanged, so the L-row is paid once. An ordinal
fact about a finite supremum names no tower, as the brief expected.

## 6. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| the merge builds | **MEASURED TRUE.** `ProbeLJ1261.agda`, exit 0 |
| `finSetK` is supplied, not assumed | **MEASURED TRUE.** same file, exit 0 |
| the three `consK-*` close with `finSetK` | **MEASURED TRUE.** `ProbeLJ1261Closure.agda`, exit 0 |
| the merge was already delivered in `src/` | **MEASURED FALSE.** no `⋃ _ ∈ lam` / `finSet _ _ ∈ Lset lam` lemma |
| a new ordinal fact was needed | **MEASURED TRUE.** `union2∈λ`, named above (C-36) |
| the first attempt walled | **MEASURED TRUE.** 1200 s interrupted; bisected to `merge2` |
| the merge stayed tower-neutral | **MEASURED TRUE.** no tower named |
| a master was edited | **MEASURED FALSE.** only `agents/tasks/LJ-1-261/` written |
| `make check` run | **MEASURED FALSE.** reserved for the orchestrator |

## 7. ARCHIVE USED (DD18)

One line read named per archived file.

- `agents/tasks/LJ-1-259/lj-1.259-report.md`, read WHOLE. **Line read `:117`**,
  the merge named as `boundingOrd` plus `ord-tri`, the starting point.
- `agents/tasks/LJ-1-259/ProbeLJ1259.agda`, read WHOLE. **Line read `:118`**,
  `finSetK`'s exact type, my specification.
- `agents/tasks/LJ-1-254/ProbeLJ1254.agda`, read WHOLE. **Line read `:105`**,
  `union∈Lset-suc`, the 52-line comparable.
- `agents/tasks/LJ-1-254/lj-1.254-report.md`, read WHOLE. **Line read `:50`**,
  `union∈Lset-suc` adapted from `mkUnion`.
- `agents/tasks/LJ-1-256/lj-1.256-report.md`, read WHOLE. **Line read `:26`**,
  `sucK`'s union closure as the unpriced L-row shape.
- `src/L/Coding/Key.lagda.md`, read `:60-140`. **Line read `:130`**,
  `Lset-fin`, the delivered stage form.
- `src/L/Coding/Bound.lagda.md`, read `:30-150`. **Line read `:89`**,
  `pr∈λ`'s `ord-tri` split, the two-ordinal merge I generalized.
- `src/L/Ordinal.lagda.md`, read `:150-200`. **Line read `:154`**,
  `boundingOrd`, the bound that does NOT land in `lam`.
- `src/L/Ordinal/Linear.lagda.md`, read `:130-140`. **Line read `:136`**,
  `ord-tri`.
- `archive/dev/TASKS-archived.md`, read the header. **Line read `:10`**, the
  264 rows. **What would NOT transfer:** the retired route consumed
  `boundingOrd` only where the target was already closed under the bound; it
  never needed the bound to climb back into a fixed limit `lam`.
- `archive/src/2026-08-09-rud-route/Everything.lagda.md`, read `:288` and
  `:342`. **Line read `:288`**, `boundingOrd` in the retired route; the
  `∈ lam` closure is absent there too.

## 8. LITERATURE USED (DD18)

**Devlin takes the finite-supremum merge for granted.** His `K(u)` is the
finite sequences over the formula set; a finite union of stages below a limit
is again below that limit by the definition of a limit ordinal, and he states
no separate lemma (`dev/literature/devlin-II5.md:246-255`, read directly).
The merge is this machine's way of paying that one definitional step.

## 9. C-44: WHAT THIS BRIEF STATES THAT I DID NOT CHECK

- **"`finSetK`'s concrete discharge cost" is INFERRED in `[LJ-1.259]`.** I
  measured it: 148 lines, about 1.07 s.
- **The step-6 context carries `gam`/`ω∈γ`.** The closure probe takes them as
  parameters only because `[LJ-1.254]`'s `Supply` wraps `sucK` with them;
  `sucK` itself does not use them, and `finSetK` needs only `succλ` and
  `∅∈λ`. I did not audit the live `HullStage` telescope for this dispatch.

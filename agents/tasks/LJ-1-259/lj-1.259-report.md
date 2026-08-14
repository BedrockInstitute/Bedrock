# LJ-1.259 report: the env closure, the second unpriced L-row

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. One Agda slot held.
No master edited. No commit, no push. Written incrementally (C-22). Every
negative is MEASURED or INFERRED, in those words.

## 0. LEAD

**`envConsK` does NOT build over `(K, Ktr)`.** It builds tower-neutral over
`(K, Ktr)` plus ONE new hypothesis, the finite-gather closure `finSetK`, plus
the four closures the master already carries. **The three honest `consK-*`
close with it.** MEASURED, exit 0.

**The one new hypothesis is the second unpriced L-row, and its concrete supply
is MOSTLY DELIVERED — the sweep caught it before I reported it absent.** The
finite-gather closure at a stage is `Lset-fin`
(`src/L/Coding/Key.lagda.md:130-135`), and the env-at-stage closure is
`paramEnv∈` (`:104-111`). What remains is the finite-supremum merge to a single
stage, an ordinal fact analogous to the `union∈Lset-suc` hole `[LJ-1.256]`
priced.

## 1. MACHINE AND PROCESS DISCIPLINE

ONE Agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised. No run past
20 minutes. No heap exhaustion. No kill. The first successful check is the
discarded warm-up; three kept runs follow.

| run | file | exit | user s | real s | load |
|---|---|---:|---:|---:|---|
| warm-up (discarded) | `ProbeLJ1259.agda` | 0 | 1.23 | 2.08 | — |
| kept 1 | `ProbeLJ1259.agda` | 0 | 0.86 | 1.68 | 4.73 |
| kept 2 | `ProbeLJ1259.agda` | 0 | 0.85 | 0.98 | 4.73 |
| kept 3 | `ProbeLJ1259.agda` | 0 | 0.86 | 0.98 | 4.73 |

Mean user time of the three kept runs: **about 0.86 s**. Nothing walls. The
probe names no `π`, no collapse, no hull; the deepest object is `Lset α` under
`opaque`, exactly as `[LJ-1.258]` section 1 recorded.

## 2. WHAT BUILT (MEASURED, exit 0)

`agents/tasks/LJ-1-259/ProbeLJ1259.agda`, module
`Fact (K : S) (Ktr : isTransV (fst K))`.

The closure lives in `EnvClosure`
(`ProbeLJ1259.agda:91-123`), parameterized by `numK0`, `sucK`, `pairK` and
`finSetK`. The first three are the master's own closure facts (`numK0` is
`numeralL 0 ∈ K`; `sucK` is the telescope hypothesis; `pairK` is the `TFacts`
field). `finSetK` is the ONE new hypothesis:

```agda
finSetK : (n : ℕ) (h : Fin n → V ℓ)
        → ((i : Fin n) → ⟨ h i ∈ fst K ⟩) → ⟨ finSet n h ∈ fst K ⟩
```

From these four, `EnvClosure` derives:

- `numK : (n : ℕ) → ⟨ # n ∈ fst K ⟩` — the general numeral closure, from
  `numK0` and `sucK` by induction. The master carries only `numK0..numK11`;
  this is the general form, DERIVED, not a new hypothesis (C-38).
- `envConsK : {k} (g : Fin k → V ℓ) (x : V ℓ) → ⟨ env g ∈ fst K ⟩
  → ⟨ x ∈ fst K ⟩ → ⟨ env (cons x g) ∈ fst K ⟩`.

`envConsK`'s body is one `finSetK` application over the finite family
`λ j → pr (# (toℕ j)) (cons x g j)`, with the two index cases closed by
`pairK` plus `sucK`/`numK` (the shifted key `# (suc (toℕ i)) = sucV (# (toℕ i))`
is definitional) and `giK` (the value `g i ∈ K`, from `env g ∈ K` by
transitivity via `prK`).

**Line count:**

| term | body lines |
|---|---:|
| `envConsK` (the closure) | **5** |
| its helpers `numK`, `env-entry`, `giK` | **4** |
| `consK-forall` | **4** |
| `consK-allin` | **4** |
| `consK-exist` | **1** |

**The three fields close** (`ConsKClosed`, `ProbeLJ1259.agda:129-179`):
`consK-forall` and `consK-allin` are `[LJ-1.258]`'s honest forms with the
hypothesis replaced by the derived `envConsK`; `consK-exist` closes from
`ya ∈ K` by `Ktr` alone, confirming its second defect (section 4).

## 3. THE SECOND UNPRICED L-ROW, NAMED (C-36)

**`envConsK` over `(K, Ktr)` alone needs `finSetK`, the finite-gather closure
of the level.** MEASURED: `agents/tasks/LJ-1-259/NegProbe.agda` states
`envConsK` with only `(K, Ktr)` in scope and the body is an unsolved hole — no
term in that telescope fills it (exit 42, unsolved interaction meta at
`NegProbe.agda:38`). The conclusion `env (cons x g) ∈ fst K` is definitionally
`finSet (suc k) (λ j → pr (# (toℕ j)) (cons x g j)) ∈ fst K` — a fresh finite
`sett`, and `Ktr` (transitivity) plus `prK` construct no `sett`. The positive
probe (section 2) builds it the moment `finSetK` is added. That no term in
`src/` concludes `finSet _ _ ∈ K` at a fixed level is MEASURED by the sweep in
section 5.

**The nine-lemma table prices neither this nor the env closure.** It is the
same shape as the `sucK`/`union∈Lset-suc` hole: a level-closure fact with no L
row.

**But the concrete supply is MOSTLY DELIVERED.** MEASURED at `file:line`:

- `Lset-fin` (`src/L/Coding/Key.lagda.md:130-135`): `h i ∈ Lset σ` for all `i`
  gives `finSet k h ∈ Lset (sucV σ)` — the stage form of `finSetK`, built from
  `FinOf.finSet∈𝒟ₒ` + `Lset-suc`.
- `paramEnv∈` (`src/L/Coding/Key.lagda.md:104-111`): `h i ∈ T σ` for all `i`
  gives `env h ∈ T (sucIter 3 σ)` — the env-at-stage closure, under `ω ∈ σ`.
- `envCloses` (`src/L/Ordinal/StageArith.lagda.md:94-96`): the climb from
  `Lset (sucIter 3 δ)` to `Lset α` under the level's `ω`-closure.

**What remains is the finite-supremum merge:** from `env g ∈ Lset lam` and
`x ∈ Lset lam`, extract stages (`Lset-out′`), merge the finitely many stage
indices into one `σ ∈ lam`, then apply `paramEnv∈` and climb. The merge is an
ordinal fact (`boundingOrd` `src/L/Ordinal.lagda.md:154` plus `ord-tri`
`src/L/Ordinal/Linear.lagda.md:136`), and it is the genuinely new content. Its
line count is INFERRED, not measured: I did not build the concrete discharge.
It is the analogue of `pr∈λ`'s two-ordinal merge generalized to `Fin n`, and of
the `union∈Lset-suc` hole `[LJ-1.256]` priced at about 52 lines.

## 4. `consK-exist`'S SECOND DEFECT, CONFIRMED (MEASURED)

`consK-exist` closes from `⟨ fst ya ∈ fst K ⟩` by `Ktr (h .snd) yaK` alone
(`ProbeLJ1259.agda:179`). Its `consAtL` conjunct is dead weight; the extra
conjunct `var zero ∈̇ var (suc⁴ zero)` (`e' ∈ ya`) already forces the conclusion
through transitivity. This is `[LJ-1.151]`'s `valK` defect, named by
`[LJ-1.258]` section 3 as C-36's second defect, and it does NOT use `envConsK`.

## 5. WAS THE CLOSURE ALREADY DELIVERED?

**`envConsK` itself: MEASURED FALSE.** No lemma in `src/` concludes
`env (cons x g) ∈ K` or `env _ ∈ K`. Sweep: `grep -rn "envConsK\|env (cons.*∈" src/`
returns nothing of the closure shape; `env` and `cons` are delivered
(`src/L/Coding/Environment.lagda.md:84, :484`), the closure is not.

**The finite-gather closure: MEASURED MOSTLY DELIVERED.** `Lset-fin` and
`paramEnv∈` (section 3) are the concrete suppliers. Naming `finSetK` "absent
from the tree" without this sweep would repeat this week's repeated
check-the-tree failure; the honest statement is "absent as a fixed-level
field, present as a stage lemma."

## 6. DD4

**The closure stayed tower-neutral.** `envConsK` is stated over `(K, Ktr)`
from its first line and names no tower; its inputs `numK0`, `sucK`, `pairK`,
`finSetK` are all abstract over `(K, Ktr)`. The J tower re-instantiates
unchanged, so the L-row is paid once and the per-tower share does not rise.

**It did NOT stay `(K, Ktr)`-only.** `envConsK` is not derivable from
transitivity; it needs `finSetK`, a genuine closure hypothesis. The brief's
DD4 asked me to "write the closure over `(K, Ktr)` too, and say whether it
stayed neutral": it stayed tower-neutral, not `(K, Ktr)`-neutral.

## 7. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| `envConsK` builds over `(K, Ktr)` | **MEASURED FALSE.** `NegProbe.agda:38`, unsolved hole |
| `envConsK` builds over `(K, Ktr, numK0, sucK, pairK, finSetK)` | **MEASURED TRUE.** exit 0 |
| the three `consK-*` close with `envConsK` | **MEASURED TRUE.** exit 0 |
| `consK-exist` carries a second defect | **MEASURED TRUE.** closes from `yaK` alone |
| `envConsK` is delivered in `src/` | **MEASURED FALSE.** no `env _ ∈ K` lemma |
| the finite-gather closure is delivered | **MEASURED MOSTLY.** `Lset-fin`, `paramEnv∈` in `Key.lagda.md` |
| the finite-supremum merge is delivered | **MEASURED FALSE** as a bundled fact; INFERRED as provable from `boundingOrd`+`ord-tri` |
| the closure stayed tower-neutral | **MEASURED TRUE.** no tower named |
| the closure stayed `(K, Ktr)`-neutral | **MEASURED FALSE.** needs `finSetK` |
| a wall occurred | **MEASURED FALSE.** max 2.08 s cold |
| I edited a master | **MEASURED FALSE.** only `agents/tasks/LJ-1-259/` written |
| `make check` run | **MEASURED FALSE.** reserved for the orchestrator |

## 8. ARCHIVE USED (DD18)

One line read named per archived file.

- `agents/tasks/LJ-1-258/lj-1.258-report.md`, read WHOLE. **Line read `:45`**,
  the four-group table with the env closure named as the missing hypothesis.
- `agents/tasks/LJ-1-258/ProbeLJ1258.agda`, read WHOLE. **Line read `:288`**,
  `module ConsK`, the three honest forms, which are my specification.
- `agents/tasks/LJ-1-256/lj-1.256-report.md`, read WHOLE. **Line read `:26`**,
  the five-copies-one-observation verdict; and the `sucK`/`union∈Lset-suc`
  hole at section "THE ONE REAL OVERRUN".
- `agents/tasks/LJ-1-254/lj-1.254-report.md`, read WHOLE. **Line read `:50`**,
  `union∈Lset-suc` adapted from `mkUnion`, the unpriced L-row shape.
- `agents/tasks/LJ-1-254/ProbeLJ1254.agda`, read WHOLE. **Line read `:161`**,
  `sucK`'s body, the delivered level-closure pattern this closure matches.
- `agents/tasks/LJ-1-168/lj-1.168-report.md`, read sections 1 and 4. **Line
  read `:350`**, the 28 entries at about 1.5 lines, the row that prices no
  gather closure.
- `src/L/Coding/Environment.lagda.md`, read `:70-130, :470-620`. **Line read
  `:84`**, `env`, and `:484`, `cons`, the delivered definitions.
- `src/L/Coding/Key.lagda.md`, read `:60-135`. **Line read `:130`**, `Lset-fin`,
  the delivered finite-gather stage closure.
- `src/L/Ordinal/StageArith.lagda.md`, read `:80-100`. **Line read `:94`**,
  `envCloses`, the delivered climb.
- `archive/dev/TASKS-archived.md`, read the header. **Line read `:10`**, the
  264 rows; the retired route never bundled a fixed-level gather closure.

## 9. LITERATURE USED (DD18)

**Devlin takes the finite-gather closure for granted.** His bound `K(u)` is the
set of finite sequences over the formula set, closed under the operations that
build them; a finite environment extension is a finite sequence, and its being
inside the carrier is part of his "some bounded description" requirement, not a
separate lemma (`dev/literature/devlin-II5.md:246-255`, cited via
`[LJ-1.168]` and `[LJ-1.254]`). The env closure is this machine's way of paying
that one requirement; the literature states no separate environment-extension
fact.

## 10. C-44: WHAT THIS BRIEF STATES THAT I DID NOT CHECK

- **"`envConsK` is the only missing hypothesis"** — CONFIRMED for the three
  fields (section 2), but the closure itself needs `finSetK`, which the brief
  did not name.
- **"write the closure over `(K, Ktr)`"** — NOT ACHIEVABLE; it needs `finSetK`.
- **The `consK-exist` second defect attribution to `[LJ-1.258]` section 3** —
  I read the report's section 3; the defect is real and MEASURED here.
- **`finSetK`'s concrete discharge cost** — I did NOT build it; the
  "finite-supremum merge remains" claim is INFERRED from the delivered pieces,
  not measured.

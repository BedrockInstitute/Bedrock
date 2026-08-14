# LJ-1.258 report: the fifteen fields that do not touch `envSetK`

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. One Agda slot held.
No master edited. No commit, no push. Written incrementally (C-22). Every
negative is MEASURED or INFERRED, in those words.

## 0. LEAD

**N of fifteen built: 12.** `valK`, `valK-un`, `valV`, `valW`, `wKfact`, and
all seven `subK-*` typecheck (exit 0) at the concrete site `K = Lset α`. The
three `consK-*` do NOT build as stated: they need a MISSING HYPOTHESIS, the
env closure, and the brief's named reader for them does not reach (C-44).

**Four per-group marginal rates, in body lines per field (the signature is
already written in the `TFacts` record, so it is not the supply's cost):**

| group | fields built | shared proof (lines) | instantiation bodies | body lines/field |
|---|---|---:|---:|---:|
| `valK`, `valK-un` | 2 of 2 | `prK`, 8 | 4 | **2** |
| `valV`, `valW`, `wKfact` | 3 of 3 | `tmValK`, 18 | 3 | **1** |
| `subK-*` (7) | 7 of 7 | `subK-gen`+`subKSucc-gen`, 14 | 7 | **1** |
| `consK-*` (3) | 0 of 3 | env closure, MISSING | 3 (demonstrated) | N/A |

**One proof per group, instantiated, exactly as the brief demanded.** The four
groups are NOT four copies of one proof: groups 1 and 3 share `prK`, group 2
carries its own case split, and group 4 is a different shape (build a set, not
extract a component). This is the real sample the brief ordered.

## 1. MACHINE AND PROCESS DISCIPLINE

ONE Agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised. No run past
20 minutes. No heap exhaustion. No kill. The first (cold) check of the full
probe pulled the dependency chain and is the discarded warm-up; three kept
runs follow.

| run | file | exit | user s | real s | load |
|---|---|---:|---:|---:|---|
| warm-up (discarded) | `ProbeLJ1258.agda` | 0 | 1.60 | 1.82 | 4.8 |
| kept 1 | `ProbeLJ1258.agda` | 0 | 0.85 | 1.05 | 4.84 |
| kept 2 | `ProbeLJ1258.agda` | 0 | 0.87 | 0.98 | 4.77 |
| kept 3 | `ProbeLJ1258.agda` | 0 | 0.83 | 0.94 | 4.77 |

Mean user time of the three kept runs: **about 0.85 s**. Nothing walls. The
probe names no `π`, no collapse, no hull: the deepest object is `Lset α`
under `opaque`, so the instantiation side stays separable (the same positive
finding `[LJ-1.151]` section 0.4 recorded).

## 2. WHAT BUILT, PER GROUP

`agents/tasks/LJ-1-258/ProbeLJ1258.agda`, module `Fact (K : S)
(Ktr : isTransV (fst K))`, instantiated at `AtLevel (α) (o) = Fact (Lset α ,
isL-Lset α o) (layer-trans (Lset-layer α))`. Every field is stated over the
structure `(K, Ktr)` from its first line; no tower is named anywhere.

### Group 1: `valK`, `valK-un` (2 of 2, exit 0)

The shared proof is `prK` (`ProbeLJ1258.agda:75-83`), the `[LJ-1.151]`
lemma: a transitive set absorbs both components of a Kuratowski pair it
contains. Each field is a one-line body: `prK (fst c) (fst yc) (Ktr hc TK)
.snd`. The code equation and `c ∈ C` are dead weight, exactly as `[LJ-1.151]`
section 1.5 measured. The honest premise is the site fact `TK : T ∈ K`.

### Group 2: `valV`, `valW`, `wKfact` (3 of 3, exit 0)

The shared proof is `tmValK` (`ProbeLJ1258.agda:221-239`, 18 lines): one
`PT.rec` over `tmValAt-out`'s `Var ⊎ Con`, closing the variable case by
`prK` from `pr k v ∈ Env` and the constant case by `prK` from
`T ≡ pr (# 0) v`, each with a written branch type (I-5). The three fields
differ only in de Bruijn indices and the two site facts they take
(`Env ∈ K`, `T ∈ K`); each body is one line.

### Group 3: `subK₁-and`, `subK₀-and`, `subK₁-imp`, `subK₀-imp`, `subK-neg`,
`subK-un`, `subK-allin` (7 of 7, exit 0)

The shared proof is `subK-gen` + `subKSucc-gen`
(`ProbeLJ1258.agda:116-130`, 14 lines): `subValAt-adequate` /
`subValSuccAt-adequate` turn the satisfaction into `pr (pr ar a) y ∈ T`
(resp. `pr (pr (sucV ar) a) y ∈ T`), then `prK` extracts `y`. The seven
fields are one-line instantiations at the master's own slot indices.

### Group 4: `consK-exist`, `consK-forall`, `consK-allin` (0 of 3)

Blocked on a missing hypothesis; section 3 and section 4 name it.

## 3. UNBUILT FIELDS, TERM NEEDED EACH (C-36)

The three `consK-*` share one missing hypothesis, and `consK-exist` carries a
second, different defect. Both are MEASURED, not inferred: the probe states
the honest forms and they typecheck given the hypothesis
(`ProbeLJ1258.agda:288-337`, module `ConsK`).

- **`consK-forall`, `consK-allin` — term needed: the ENV CLOSURE.**
  `envConsK : {k} (g : Fin k → V ℓ) (x : V ℓ) → env g ∈ K → x ∈ K →
  env (cons x g) ∈ K`. `consAtL-adequate` turns the satisfaction into
  `e' ≡ env (cons x g)` with `z ≡ env g`; the last step needs
  `env (cons x g) ∈ K` from `env g ∈ K` and `x ∈ K`. MEASURED absent:
  no lemma in `src/` concludes `env _ ∈ K` (section 4).
- **`consK-exist` — term needed: `ya ∈ K`.** Its premise has the extra
  conjunct `var zero ∈̇ var (suc⁴ zero)`, i.e. `e' ∈ ya`, so it closes from
  `ya ∈ K` by `transK` alone and its `consAtL` conjunct is dead weight. This
  is the SAME defect `[LJ-1.151]` section 0.2 measured for `valK`: the
  conclusion subject is unconstrained by the stated premises. MEASURED: the
  honest form with `ya ∈ K` typechecks at `ProbeLJ1258.agda:333-337`.

**A group that fails whole vs a field that fails alone:** the three fail
WHOLE as one shape (they all conclude `e' ∈ K` from `⊨ consAtL`); `consK-exist`
additionally carries the `ya ∈ K` defect. The group is "build a set" (shape
two in `[LJ-1.151]` section 4.2), not "extract a component" (shape one).

## 4. DELIVERED READERS THAT DID NOT REACH (C-44)

Two named readers do not supply what the table says. MEASURED at `file:line`.

- **`DenoteBody-out` does not reach for the consK group.**
  `src/L/Choice/Internal.lagda.md:640-642` concludes
  `⟨ fst z ∈ fst (lookup B γ) ⟩ × ∥ DenoteOf z ∥₁` — the carrier membership
  of `z` and a denotation witness, never `e' ∈ K`. It is the wrong reader for
  `consK-exist`/`forall`/`allin`. The table above is `[LJ-1.254]`'s READING
  and it built none of these fifteen; this reader is the C-44 defect the
  brief predicted.
- **`sucK` does NOT reach the subK group — and it does not need to.** The
  brief's table gives the subK reader as `subValSuccAt-adequate` +
  `transK`/`sucK`. MEASURED: `subValSuccAt-adequate`
  (`src/L/Coding/Model.lagda.md:1409-1434`) already reduces the satisfaction
  to `pr (pr (sucV ar) a) y ∈ T`; `prK` extracts the second component `y`
  without ever needing `sucV ar ∈ K`. My `subKSucc-gen` compiles with no
  `sucK`. The brief's "the subK group is the one that uses sucK" is FALSE at
  this site for these seven fields.

The other named readers reach: `subValAt-adequate`, `subValSuccAt-adequate`,
`tmValAt-out`, `consAtL-adequate` all reduce their satisfaction to the
membership the field needs, and `transK` (`Ktr`) closes the pair chain.

## 5. THE FOUR RATES AGAINST `255 / 28 = 9.1`

**The 9.1 figure was never a per-field marginal, and these four rates are the
real sample.** MEASURED.

- Body lines per field: **2, 1, 1, N/A** for the four groups. Against 9.1,
  every built group is far UNDER, by a factor of 5 to 9.
- With the shared proof amortized over its group: **6, 7, 3** lines per
  field (groups 1, 2, 3). These sit around or under 9.1, and the shared
  proofs are the `[LJ-1.168]` nine-lemma rows L2/L5/L6 written once, not the
  entry row.
- The entry row's own estimate was **about 1.5 lines per field**
  (`[LJ-1.168]:350`). Measured here: **1 to 2 body lines per field**. The
  estimate holds. `[LJ-1.255]`'s 11-17 lines per field is REFUTED again: it
  measured one proof copied, exactly as `[LJ-1.256]` overturned it.

**The one overrun is not a field at all: it is the missing env closure**
(group 4), an L-row the nine-lemma table did not price, analogous to the
`sucK`/`union∈Lset-suc` hole `[LJ-1.256]` found.

## 6. DD4: PER-TOWER FIELDS

**None of the fifteen is per-tower. MEASURED.** Every one concludes a
K-membership from the satisfaction of a coding formula (`tmValAt`,
`subValAt`, `subValSuccAt`, `consAtL`) or from a graph entry; none names
`t0`, `t1`, a tower, or a concrete slot beyond the structure parameters. All
fifteen are stated over `(K, Ktr)` from their first line, so the J tower
re-instantiates `Fact` unchanged. The per-tower residue (`t0eq`, `t1eq`,
`someEnv`) is entirely outside these fifteen: `t0eq`/`t1eq` are zero
(`[LJ-1.255]` section 1.4) and `someEnv` is `[LJ-1.257]`'s.

## 7. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| all fifteen build | **MEASURED FALSE.** 12 of 15 |
| `valK`, `valK-un` build | **MEASURED TRUE.** exit 0 |
| `valV`, `valW`, `wKfact` build | **MEASURED TRUE.** exit 0 |
| the seven `subK-*` build | **MEASURED TRUE.** exit 0 |
| the three `consK-*` build as stated | **MEASURED FALSE.** env closure missing |
| `consK-exist` additionally carries a `ya ∈ K` defect | **MEASURED TRUE.** same shape as `[LJ-1.151]`'s valK defect |
| the env closure is delivered | **MEASURED FALSE.** no `env _ ∈ K` lemma in `src/` |
| `DenoteBody-out` reaches the consK group | **MEASURED FALSE.** it concludes `z ∈ B`, not `e' ∈ K` |
| the subK group uses `sucK` | **MEASURED FALSE.** `subKSucc-gen` compiles without it |
| the 9.1 lines/field figure is a per-field marginal | **MEASURED FALSE.** the entry rate is 1-2 body lines |
| `[LJ-1.255]`'s 11-17 lines/field | **MEASURED FALSE.** one proof copied, not a marginal |
| any of the fifteen names a tower | **MEASURED FALSE.** all coding machinery over `(K, Ktr)` |
| a wall occurred | **MEASURED FALSE.** max 1.82 s cold |
| I edited a master | **MEASURED FALSE.** only `agents/tasks/LJ-1-258/` written |
| `make check` run | **MEASURED FALSE.** reserved for the orchestrator |

## 8. ARCHIVE USED (DD18)

One line read named per archived file.

- `agents/tasks/LJ-1-254/lj-1.254-report.md`, read WHOLE. **Line read `:64`**,
  the twelve-row table that names these fifteen and their readers.
- `agents/tasks/LJ-1-255/lj-1.255-report.md`, read WHOLE. **Line read `:107`**,
  the「about 11 proof lines, a ~7x undercount」claim this probe tests.
- `agents/tasks/LJ-1-256/lj-1.256-report.md`, read WHOLE. **Line read `:26`**,
  the five-copies-one-observation verdict and the factored form.
- `agents/tasks/LJ-1-151/lj-1.151-report.md`, read WHOLE. **Line read `:184`**,
  `TK : T ∈ K` stays a hypothesis of the site — the residue this probe keeps.
- `agents/tasks/LJ-1-151/ProbeLJ1151A.agda`, read WHOLE. **Line read `:58`**,
  `prK`, the shared lemma beneath groups 1 and 3, copied green.
- `agents/tasks/LJ-1-168/lj-1.168-report.md`, read section 4. **Line read
  `:350`**, the 28 entries at about 1.5 lines, inside the 271-line table.
- `agents/tasks/LJ-1-113/lj-1.113-report.md`, read `:215-240`. **Line read
  `:219`**, the 25-against-4 split and the per-field residue table.
- `src/L/Condensation/TwelveAgree.lagda.md`, read WHOLE. **Line read `:186`**,
  the `valK` field with the graph-membership premise added since `[LJ-1.112]`.
- `src/L/Coding/Model.lagda.md`, read the reader block. **Line read `:1409`**,
  `subValSuccAt-adequate`'s conclusion, which shows `sucK` is not needed.
- `src/L/Choice/Internal.lagda.md`, read `:600-670`. **Line read `:642`**,
  `DenoteBody-out`'s conclusion `z ∈ B`, the reader that does not reach.
- `archive/dev/TASKS-archived.md`, read the header. **Line read `:10`**, the
  264 rows recording which approaches were measured on the retired route; the
  retired route never built these satisfier-in-K closures either.

## 9. LITERATURE USED (DD18)

**Devlin does not need these fifteen facts; they are an artifact of the
coding.** `dev/literature/devlin-II5.md:246-255` requires only that every
unbounded quantifier have SOME bounded description inside the carrier; the
fifteen satisfier-in-K closures are this machine's way of meeting that one
requirement, and Devlin's prose never states them separately. The genuinely
mathematical residue among the fifteen is nil; it sits in `sucK` and
`envSetK`, which are not these fifteen.

# LJ-1.199 report: BUILD step 6, the satisfaction layer supply, priced at 255

**STATUS: STOP — a join the cured fields do not close.** Written incrementally
from a skeleton (C-22). Every negative is marked **MEASURED** or **INFERRED**
(C-36).

## 0. LEAD

**What closed: NOTHING, and the reason is a join, not the budget.**
**Actual lines against 255: ZERO.** The supply stops before its first line,
because the load-bearing lemma of the layer — `envSetK`, L9 in the
nine-lemma table — cannot be supplied at the generality its record sits at.

**The term I could not write, at `file:line` (C-36):**

```agda
ω∈λ : ⟨ ω ∈ lam ⟩
```

`envSetNumeral∈` — the ONE delivered bound that supplies `envSetK` — takes
`⟨ ω ∈ σ ⟩` as a hypothesis (`src/L/Coding/Key.lagda.md:476`). To use it at
the concrete bound `K = Lset lam`, the supply must produce a `σ` with
`ω ∈ σ`, `fst B ∈ Lset σ` and `sucIter 4 σ ∈ lam`. The first of the three
is `ω ∈ lam` or `ω ∈ gam`, **and neither is in the telescope**.

**`HullStage`'s telescope is `lam, ordλ, succλ, X, X⊆L, ∅∈λ`
(`src/L/BoundedSubset.lagda.md:903-905`).** `KValue`, the step-5 analogue
whose shape the TFacts value copies, takes `∅∈λ` and NOT `ω∈λ`
(`src/L/Condensation.lagda.md:7222-7225`). **Successor-closure plus `∅∈λ`
does not give `ω ∈ lam`:** the codebase itself carries `ω ∈ α` and
successor-closure as two SEPARATE conjuncts of `Init`
(`src/L/Ordinal/SquareLaw.lagda.md:693-697`). **MEASURED, by reading all
three.**

## 1. CRITERIA, FIXED IN WRITING BEFORE THE FIRST RUN (D-1)

ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised. **30 minutes
per invocation.** Count: in-fence non-blank lines, ledger caliber. **No run
was needed and none was made** (section 3).

## 2. THE JOIN, STEP BY STEP

### 2.1 What the cured field asks for, MEASURED

`src/L/Condensation/TwelveAgree.lagda.md:302-307`:

```agda
    envSetK : (B ar : S) (n : ℕ) → fst ar ≡ # n
            → ⟨ fst B ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
            → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
            → ⟨ fst (Generic.envSetGen B ar)
                 ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
```

At the concrete bound, `lookup (6+K) γ' = Lset lam`, and `B = LsetS gam`
(the carrier slot, `src/L/Condensation.lagda.md:7232`). So the supply must
conclude `Generic.envSetGen B ar ∈ Lset lam` from `fst ar ≡ # n`,
`B ∈ Lset lam` and `ar ∈ Lset lam`.

### 2.2 The delivered bound, MEASURED

`src/L/Coding/Key.lagda.md:476-479` is the ONLY delivered fact that puts
`envSet B n` into a level:

```agda
envSetNumeral∈ : (σ : V ℓ) → IsOrd σ → ⟨ ω ∈ σ ⟩ → (B : CS.S) (n : ℕ)
               → ⟨ fst B ∈ Lset σ ⟩
               → ⟨ fst (envSet B n) ∈ Lset (sucIter 4 σ) ⟩
```

**MEASURED: it has ZERO consumers in `src/`** (`grep -rn "envSetNumeral∈"
src/` returns its own declaration only). The layer is unbuilt, exactly as
`[LJ-1.173]` section 27 left it.

The identification to `Generic.envSetGen` is the other half of L9 and it is
delivered: `NumeralFromGeneric.derived : fst (envSet B n) ≡
fst (Generic.envSetGen B (nn n))` (`src/L/Coding/Sound.lagda.md:300`).
Combined with `fst ar ≡ # n` it gives `Generic.envSetGen B ar ≡ envSet B n`.
**That half closes. The `ω ∈ σ` half does not.**

### 2.3 The discharge needs `ω ∈ σ`, MEASURED

To apply `envSetNumeral∈` at `K = Lset lam`, the supply needs a `σ` with
three properties:

| property | why | where it comes from |
|---|---|---|
| `fst B ∈ Lset σ` | the lemma's input | `B = LsetS gam`, so `σ = sucV gam` works, from `γ∈λ` |
| `sucIter 4 σ ∈ lam` | climb to `Lset lam` by `Lset-mono` | `succλ` iterated, from `σ ∈ lam` |
| **`ω ∈ σ`** | the lemma's hypothesis | **NOWHERE.** `ω ∈ σ` needs `ω ∈ gam` or `ω ≡ gam`, and neither is in the telescope |

`ω ∈ σ` is ordinal membership. `ω ∈ sucV gam` reduces to `ω ∈ gam` or
`ω ≡ gam` (successor membership). `ω ∈ lam` is the weakest fact that would
discharge it (with a two-ordinal merge below the limit, which `ord-tri`
already provides). **Neither `ω ∈ lam` nor `ω ∈ gam` is a hypothesis of
`HullStage` or `KValue`.**

### 2.4 Why `succλ + ∅∈λ` does not close it, MEASURED

`succλ` and `∅∈λ` give `# k ∈ lam` for every FINITE numeral `k`
(`BoundOver.#∈λ`, `src/L/Coding/Bound.lagda.md:52-54`). They do NOT give
`ω ∈ lam`: the ordinal `ω` is the set of all finite numerals, and `ω ∈ lam`
fails at `lam = ω`, which satisfies both hypotheses. **The codebase records
the independence:** `Init α` carries `⟨ ω ∈ˢ α ⟩` and
`(γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩` as two separate conjuncts
(`src/L/Ordinal/SquareLaw.lagda.md:693-697`).

## 3. SECONDS, LOAD, RUN COUNT

**ZERO agda invocations.** The join is a type-level gap and the read settled
it; a run would re-derive a statement I already hold at `file:line`. No
wall, no heap figure. **Load: not applicable.**

## 4. LINES AGAINST 255

**ZERO against 255.** The stop is the join, not the budget.

**What the 255 did NOT price.** `[LJ-1.173]` section 68 re-priced L9 from 45
to 25 on the claim that "`envSetNumeral∈` is DELIVERED in
`src/L/Coding/Key.lagda.md`; what remains is the `envSet` to `envSetGen`
identification." **That claim is TRUE as far as it goes, and it hides a
hypothesis.** `envSetNumeral∈` is delivered, and it is stated with
`ω ∈ σ` as an input. **The re-price counted the identification and never
counted the discharge of `ω ∈ σ`.** The join is that discharge.

## 5. WHAT THE JOIN BLOCKS, AND WHAT IT DOES NOT

**L9 `envSetK` blocks 11 of the 28 satisfaction fields** (itself, the five
`envK-*` through L3, the four `envInK-*` through L4, and `someEnv` through
L8; `[LJ-1.168]` names these consumers at its section 4.1 table). **MEASURED
as a count; INFERRED as a dependency, because I wrote no line of them.**

**The other 17 fields** (`codesK`×2, `valK`×2, `valV`/`valW`/`wKfact`×3,
`subK-*`×7, `consK-*`×3) are decode-plus-closure and their transfer
machinery is DELIVERED (`ChainZ` at `src/L/Condensation.lagda.md:2817`,
`EnvSet` at `:2926`, `TmVal` at `:3062`, `SubValB2T` at `:3172`,
`SubValSuccB2T` at `:3209`). **I did not write them, so I do not claim they
close; I name the machinery that would carry them.**

## 6. DD4

**Nothing was written, so there is no re-instantiation figure to give, and I
will not invent one.**

The intended supply is the right shape: the pair-unwinding and the
decode-plus-closure steps name no tower and sit in `ChainZ`/`EnvSet`/`TmVal`
already, over the closure facts `transK` and `pairK` alone. **The join is at
the one step that IS about the L tower** — `envSetNumeral∈`, which is stated
over `Lset` and needs `ω ∈ σ`. That is the same division `[LJ-1.168]` section
5 already priced: the statement layer re-instantiates, the coding cone is
per-tower. **The join does not change that picture; it adds a hypothesis to
the L instantiation.**

## 7. WHAT THE SATISFACTION LAYER STILL NEEDS

**One hypothesis, then the build.**

1. **Add `ω∈λ : ⟨ ω ∈ lam ⟩`** to the TFacts-value module (and to `HullStage`
   if the value must sit under it). **`ω∈gam : ⟨ ω ∈ gam ⟩` is the stronger,
   simpler alternative** that avoids the two-ordinal merge. Both are one line.
2. **A two-ordinal merge below the limit** (about 5 lines), which `ord-tri`
   already supplies, unless the `ω∈gam` form is taken.
3. **Then the 255-line build proceeds as priced**, with L9 closing as
   `envSetNumeral∈` plus `NumeralFromGeneric.derived` plus the climb.

**The price changes by the join, not by the build.** The re-price stays about
255; the discharge of `ω ∈ σ` is NEW content the 255 did not count, and it is
roughly one hypothesis plus a merge.

## 8. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| **step 6 was built** | **MEASURED FALSE. ZERO lines.** The stop is the join |
| **the 255-line price covers the whole supply** | **MEASURED FALSE in one term.** It covers the identification, not the `ω ∈ σ` discharge (section 4) |
| `envSetNumeral∈` needs `ω ∈ σ` | **MEASURED TRUE.** `src/L/Coding/Key.lagda.md:476` |
| `HullStage` carries `ω ∈ lam` | **MEASURED FALSE.** Its telescope is `lam, ordλ, succλ, X, X⊆L, ∅∈λ` (`:903-905`) |
| `KValue` carries `ω ∈ lam` | **MEASURED FALSE.** `∅∈λ` only, `src/L/Condensation.lagda.md:7222-7225` |
| `succλ + ∅∈λ` gives `ω ∈ lam` | **MEASURED FALSE.** `Init` keeps `ω ∈ α` and successor-closure separate (`src/L/Ordinal/SquareLaw.lagda.md:693-697`) |
| **`envSetK` can be supplied at `HullStage`'s generality** | **INFERRED FALSE.** The type-level gap is MEASURED (2.1-2.3); the impossibility is the assembly of those reads, and I built no Agda counterexample (C-36) |
| the cured fields are wrong | **NOT CLAIMED.** They are green and correct; the join is a MISSING hypothesis, not a false field |
| the identification half of L9 is missing | **MEASURED FALSE.** `NumeralFromGeneric.derived` is delivered (`src/L/Coding/Sound.lagda.md:300`) |
| the other 17 fields close | **NOT CLAIMED. C-36.** I did not write them |
| a wall occurred | **MEASURED FALSE.** Zero agda runs |
| `make check` was run | **MEASURED FALSE.** Reserved for the orchestrator |
| I edited `src/` | **MEASURED FALSE.** `src/` is clean; the only file is this report |

## 9. PROHIBITIONS, ANSWERED ONE BY ONE

- `src/L/Choice/Name.lagda.md`: **NEVER OPENED.**
- The 21 cured fields: **NOT TOUCHED.** `git status --porcelain src/` is empty.
- Probe location: this report is in `agents/tasks/LJ-1-199/`. **No probe was
  written** — the join is a read, not a run (D-1).
- `src/Everything.lagda.md`: **NEVER OPENED.**
- Commit, push, `checkout .`, `stash`, `reset --hard`, `clean`: **NONE.**
- `make check`: **NOT RUN.**
- Heap cap: **never invoked** (no agda process).

## 10. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-173/lj-1.173-report.md`, READ WHOLE.** TOOK the 21-field
  cure, the step-6 re-price table at section 68, and the `envSetNumeral∈`
  placement at sections 24 and 29-30. **The re-price is the claim section 4
  corrects:** it priced the identification and never priced the `ω ∈ σ`
  discharge.
- **`agents/tasks/LJ-1-172/lj-1.172-report.md`, READ WHOLE.** TOOK steps 1 to 5
  as built, the `envSetK` refutation at sections 15-19, and the six-names
  closure fact. **The refutation was about the general arity; the numeral
  cure is the field now in the tree, and my join is a further term, not a
  retraction of that cure.**
- **`agents/tasks/LJ-1-180/lj-1.180-report.md`, READ WHOLE.** TOOK the UPHELD
  verdict and the re-derived citations. **Nothing in it names `ω ∈ lam`, so
  the join is new.**
- **`agents/tasks/LJ-1-168/lj-1.168-report.md`, READ WHOLE.** TOOK the
  nine-lemma allocation (section 4.1), the decode table (1.1), and the
  `envSetK` risk (4.3). **Its L9 priced `mkReflect`, which `[LJ-1.172]`
  refuted; the surviving route is `envSetNumeral∈`, and its `ω ∈ σ` input is
  the term nobody priced.**
- **`archive/dev/TASKS-archived.md`.** Took SHAPE only: the retired route's
  `EnvSet` carried the numeral form (`[LJ-1.173]` section 14), and nothing in
  it states the set in a stage. **No claim taken** — `[LJ-1.11]` ruled that
  route's condensation target classically FALSE. **What would NOT transfer:
  the retired route's environment bound, because it never stated the SET in a
  stage and so never faced the `ω ∈ σ` discharge at all.**
- **`dev/LESSONS.md`** through `scripts/rules.py --for build` and `--for
  probe`: C-22, C-36, C-38 as extended, C-42, P-l, P-k, D-1, D-10, C-12.
  **P-l is the rule this stop turns on:** `envSetNumeral∈`'s `ω ∈ σ` is a
  hypothesis at its own site, and `[LJ-1.173]` transferred the lemma without
  its discharge, which is the same shape as a measured cure transferred by
  analogy.

## 11. LITERATURE USED (DD18)

- **`dev/literature/devlin-II5.md`, READ the K(u) passages.** **TOOK: Devlin's
  construction is at a limit `α > ω`** — `:218` ("Uniform Δ₁ at limit α > ω"),
  `:339` ("Def uniformly Δ₁^α at limit α > ω"), `:345` ("γ ↦ L_γ uniformly
  Δ₁^α for limit α > ω"). **So `ω ∈ α` is part of Devlin's own setup, and it
  is exactly the term the tree's `HullStage` does not state.**
- **THE BRIEF'S QUESTION, ANSWERED.** **Devlin's construction needs the
  general arity NOT AT ALL** — `[LJ-1.173]` section 10 measured that his
  arities are all finite, so all numeral. **What it DOES need, and what the
  tree dropped, is `α > ω`.** The numeral restriction returns the field to
  Devlin's form; the missing `ω ∈ λ` hypothesis is the one thing Devlin has
  by "limit α > ω" and the tree's telescope does not.
- `dev/literature/devlin-errata.md`: **NOT read**, on `[LJ-1.180]`'s record
  that the errata touch no part of II.5 (`agents/tasks/LJ-1-180/
  lj-1.180-report.md`, LITERATURE USED).

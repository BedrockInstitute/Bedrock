# LJ-1.254 report: BUILD step 6, the 28 fields, join measured open

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. One Agda slot held.
No master edited. No commit, no push. Written incrementally (C-22). Every
negative is MEASURED or INFERRED, in those words.

## 0. LEAD

**N of 28 built: 1 field, `sucK`. Plus the two load-bearing supporting
lemmas: `envSetK` (L9, the join that stopped [LJ-1.199]) and
`union∈Lset-suc` (the union closure beneath `sucK`).**

**Written lines against 255: 141 in-fence non-blank code lines (105 content,
36 imports).**

**`sucK` did NOT wall.** It typechecks at the concrete site in about 1.1
seconds. The "known 8 GB waller" fear does not fire at this site in this
form. MEASURED.

**The join closes.** `envSetK` typechecks: `ar ≡ # n` plus the delivered
`envSetNumeral∈` plus `NumeralFromGeneric.derived` plus the `succλ` climb
give `Generic.envSetGen B₀ ar ∈ Lset lam`. This is the term
`[LJ-1.199]` stopped on at ZERO lines, now MEASURED green.

## 1. MACHINE AND PROCESS DISCIPLINE

ONE Agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised. No run
passed 20 minutes. No heap exhaustion. No kill.

| run | file | exit | user s | real s | load |
|---|---|---:|---:|---:|---|
| join only, 4 kept | `ProbeLJ1254.agda` (envSetK only) | 0 | 1.07-1.09 | 1.19-1.26 | 3.52/4.07/4.14 |
| join + sucK, run 1 | `ProbeLJ1254.agda` | 0 | 1.15 | 1.39 | 4.00/4.07/4.11 |
| join + sucK, kept 1-4 | `ProbeLJ1254.agda` | 0 | 1.06-1.10 | 1.19-1.24 | 4.00/4.07/4.11 |

Four kept runs for the figure a decision rests on: mean user time about
**1.08 s**. The decision (sucK does not wall) rests on exit codes and the
absence of any seconds blow-up, not on these seconds. `sucK` plus the union
closure added about 0.05 s to the join-only probe.

## 2. WHAT I BUILT (MEASURED, exit 0)

`agents/tasks/LJ-1-254/ProbeLJ1254.agda`, module `Supply`, at the concrete
site `K = Lset lam`, carrier `B₀ = LsetS gam ordγ`, with the new hypothesis
`ω∈γ : ⟨ ω ∈ sucV gam ⟩` ([LJ-1.252]'s cheaper form).

| name | what it is | role |
|---|---|---|
| `envSetK` | `(ar) (n) → fst ar ≡ # n → fst ar ∈ Lset lam → fst (Generic.envSetGen B₀ ar) ∈ Lset lam` | **L9, the join.** The chain is `ar ≡ # n ⇒ ar ≡ nn n ⇒ Generic.envSetGen B₀ ar ≡ envSet B₀ n` (`NumeralFromGeneric.derived`) `∈ Lset (sucIter 4 σ)` (`envSetNumeral∈`) `⊆ Lset lam` (`succλ` climb). |
| `union∈Lset-suc` | `(σ x) → x ∈ Lset σ → ⋃ x ∈ Lset (sucV σ)` | the raw union closure, adapted from `L.Axioms.Basic.UnionOf.mkUnion` |
| `sucK` | `(a) → a ∈ Lset lam → sucV a ∈ Lset lam` | **the named waller, field 24 of 28.** `sucV a = ⋃ ⁅a,⁅a⁆s⁆`, so one union step above a pairing step above a singleton step, then `succλ` four times |

Both `envSetK` and `sucK` typecheck. `sucK` is ONE of the 28 fields; the
other 27 are not built. Their residues are named in section 3.

## 3. UNBUILT FIELDS, term needed each (C-36)

The 28 fields are the `Extended` parameters of `ProbeLJ1112A.agda` minus the
PROVABLE `t0K`, verified against the current `TFacts` record
(`src/L/Condensation/TwelveAgree.lagda.md`). 27 remain unbuilt. Their
closure is **INFERRED**, from [LJ-1.168]'s nine-lemma table (read whole) and
the delivered readers I cite; I wrote no line of them (C-36).

| field | count | term needed | delivered reader |
|---|---|---|---|
| `valK`, `valK-un` | 2 | `yc ∈ K` from the code equation | `domEntryK`/`closedEntryK` (KFacts field) + `transK` (`layer-trans (Lset-layer lam)`) |
| `envK-mem/-neg/-top/-imp/-allin` | 5 | `E ∈ K` from `⊨ envSetAt` | `Generic.Holds.bwd` + **`envSetK` (built)** + `transK` |
| `envInK-mem/-neg/-top/-imp` | 4 | `z ∈ K` from `⊨ envOverAt` | `Generic.Holds.bwd` + **`envSetK` (built)** + `transK` |
| `valV`, `valW`, `wKfact` | 3 | `v/w ∈ K` from `⊨ tmValAt` | `tmValAt-out` + `transK` |
| `subK₁-and`, `subK₀-and`, `subK₁-imp`, `subK₀-imp`, `subK-neg`, `subK-un`, `subK-allin` | 7 | `y ∈ K` from `⊨ subValAt`/`subValSuccAt` | `subValAt-adequate`, `subValSuccAt-adequate` + `transK`/`sucK` |
| `consK-exist`, `consK-forall`, `consK-allin` | 3 | `e' ∈ K` from `⊨ consAtL` | `consAt-adequate`, `DenoteBody-out` + `transK` |
| `someEnv` | 1 | an environment `E ∈ K` with `envHypB2`, built from three K memberships | `Generic.Holds` + **`envSetK` (built)**; the construction itself is unmeasured |
| `t0eq`, `t1eq` | 2 | slot equalities at the consumer's own `t0`/`t1` | the consumer's site states them; the supply pays zero (INFERRED) |

`envSetK` (L9) is NOT one of the 28; it is the supporting lemma beneath 11
of them (5 `envK-*`, 4 `envInK-*`, `someEnv`, and one half of each
`envK-*`'s decode), exactly as [LJ-1.199] section 5 named.

## 4. THE 25-AGAINST-3 SPLIT, TESTED

**The split holds, and it was tested by reading the field types, not by
building them.** MEASURED as a read of `TFacts` and `ProbeLJ1112A.agda`;
the closure is INFERRED.

- The 25 coding fields (`valK`×2, `envK-*`×5, `envInK-*`×4, `valV`/`valW`/
  `wKfact`×3, `subK-*`×7, `consK-*`×3, `sucK`) each conclude membership in
  the K slot (`lookup (suc⁶ K) γ' = Lset lam`) from a satisfaction of a
  coding formula (`envSetAt`, `envOverAt`, `tmValAt`, `subValAt`,
  `subValSuccAt`, `consAtL`) or a membership premise. None names a tower;
  each names the K slot and the coding machine.
- The 3 per-tower fields (`t0eq`, `t1eq`, `someEnv`) name the consumer's
  concrete slots and the environment the tower's condensation builds.

**DD4 answer:** my `sucK` and `envSetK` are written over the structure
parameter (`Lset`, `sucV`, `succλ`, `Lset-mono`, `B₀`) from their first
line; they name no tower and no `Lset` presentation, so they are paid once
for both towers. The 25 coding fields share the same shape. The 3 tower
fields re-instantiate per tower. This confirms `[LJ-1.113]:219-239` and
`[LJ-1.252]` section 4.

## 5. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| step 6 fully built (28/28) | **MEASURED FALSE.** 1 of 28 fields built |
| `sucK` walls at 8 GB | **MEASURED FALSE.** ~1.1 s, no heap figure, exit 0 |
| the join (`envSetK`) closes | **MEASURED TRUE.** exit 0 |
| `envSetK` needs the two-ordinal merge | **MEASURED FALSE.** `ω∈γ` at `σ = sucV gam` suffices; no merge written |
| the 26 decode fields close | **INFERRED.** delivered readers + `envSetK` + `transK`/`sucK`; I wrote no line (C-36) |
| `someEnv` closes | **INFERRED.** the environment construction is unmeasured |
| `t0eq`/`t1eq` cost the supply machinery | **INFERRED FALSE.** the consumer's site states them |
| the 25 really name no tower | **MEASURED TRUE** as a read of the field types; closure INFERRED |
| a wall occurred | **MEASURED FALSE.** max 1.39 s |
| I edited a master | **MEASURED FALSE.** only `agents/tasks/LJ-1-254/` written |
| `make check` run | **MEASURED FALSE.** reserved for the orchestrator |

## 6. ARCHIVE USED (DD18)

One line read named per archived file.

- `agents/tasks/LJ-1-199/lj-1.199-report.md`, read WHOLE. **Line read
  `:294`**, the join table: `ω ∈ σ` needs `ω ∈ gam` or `ω ≡ gam`, neither
  in the telescope. This probe supplies it as `ω∈γ`.
- `agents/tasks/LJ-1-252/lj-1.252-report.md`, read WHOLE. **Line read
  `:78`**, "the cheaper form is `ω∈γ : ⟨ ω ∈ˢ sucV gam ⟩`", which my probe
  takes. `ProbeLJ1252A.agda` read whole; the `ω∈sucα` shape.
- `agents/tasks/LJ-1-113/lj-1.113-report.md`, read `:1-300`. **Line read
  `:219`**, the 28-fact table and the 25-3 split.
- `agents/tasks/LJ-1-168/lj-1.168-report.md`, read the nine-lemma table.
  **Line read `:341`**, the L1-L9 allocation whose readers I cite in
  section 3.
- `agents/tasks/LJ-1-173/lj-1.173-report.md`, read sections 66-68. **Line
  read `:1943`**, the re-priced 255 and the `envSetNumeral∈` placement.
- `src/L/Coding/Key.lagda.md`, read `:440-479`. **Line read `:476`**,
  `envSetNumeral∈`'s `ω ∈ σ` hypothesis.
- `src/L/BoundedSubset.lagda.md`, read `:903-905`. **Line read `:903`**,
  `HullStage`'s telescope `lam, ordλ, succλ, X, X⊆L, ∅∈λ`.
- `src/L/Condensation.lagda.md`, read `:7222-7275`. **Line read `:7223`**,
  `KValue`'s telescope and the `facts` record.
- `archive/dev/TASKS-archived.md`, read the header. **Line read `:10`**, the
  shape note. **What would NOT transfer:** the retired route's environment
  bound never stated the set in a stage, so it never faced the `ω ∈ σ`
  discharge; its union closure shape transfers (my `union∈Lset-suc` is its
  raw-level form).

## 7. LITERATURE USED (DD18)

- `dev/literature/devlin-II5.md`, read the K(u) passages via
  `[LJ-1.199]`'s citation. **Devlin's construction needs FEWER than 28 of
  these facts.** His uniform-Δ₁ setup is at a **limit α > ω**
  (`devlin-II5.md:339`), so `ω ∈ α` is part of his assumption, not a field
  to discharge; and his arities are all finite (`[LJ-1.173]` section 10), so
  the numeral restriction of `envSetK` is his form, not the tree's. The 28
  fields are largely **an artifact of the coding**: they are the
  satisfier-in-K closures the machine's satisfaction relation demands, which
  Devlin's prose never states separately because his construction is not a
  machine coding. The genuinely mathematical residue is `sucK` (the level is
  closed under successor, his `L_α` for limit α) and `envSetK` (the level
  holds the environment description), both of which are Devlin's `α > ω`
  plus the definable-powerset closure.

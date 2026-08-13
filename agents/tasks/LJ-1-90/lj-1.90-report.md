# LJ-1.90: instantiate BoundedSubsetAt for the first time

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.90-report.md`.

## 0. THE VERDICT

**The first consumer's supply stops at `cardκ`. Every hypothesis the
dispatch names, including `AllCodes A ∈ Lset lam`, receives a VALUE at a
concrete site and typechecks; the first hypothesis nothing can supply is
`cardκ : IsCardinal κ` at the concrete `κ = sucV ω`. The tower must
provide a concrete initial ordinal above `α`; the tree delivers none.**

The probe is `src/ProbeLJ190A.agda`, GREEN at the C-12 cap, one process,
0.98 s user, 1.86 s wall. Load at the final run: 4.74 / 4.14 / 4.34,
four users, the machine was NOT quiet.

The dispatch's named question is answered MEASURED: **the consumer that
names `lam` CAN produce `AllCodes A ∈ Lset lam`**, at the price of naming
`lam` with room above the code set's own stage. The mechanism is
machine-checked at `src/ProbeLJ190A.agda:193-194` and instantiated at
`:199`.

## 1. HOW FAR THE INSTANTIATION REACHED

The telescope is `src/L/BoundedSubset.lagda.md:1396-1402`. Each hypothesis
and its value, at `file:line`:

| hypothesis | value | where |
|---|---|---|
| `κ : S` | `κ = sucV ω` | `src/ProbeLJ190A.agda:204-205` |
| `ordκ : IsOrd κ` | `suc-ord ω-ord` | `:207-208` |
| **`cardκ : IsCardinal κ`** | **NO VALUE. FIRST UNSUPPLIABLE** | section 1.1 |
| `α : S` | `α = ω` | `:199` (`Site0`) |
| `ordα : IsOrd α` | `ω-ord` | `:199` |
| `α∈κ` | `self∈sucV ω` | `:210-211` |
| `α∉ω` | `∈-irrefl ω` | `:199` |
| `x : S` | `x = ∅` | `:169-170` |
| `x⊆Lα` | vacuous, via `∅-empty` | `:172-173` |
| `lam : S` | the omega-limit above `bound2 α δ₀` | `:118-119` |
| `ordλ : IsOrd lam` | from `boundingOrd` | `:121-122` |
| `α∈λ` | `ordλ .fst α∈γ γ∈λ` | `:127-128` |
| `succλ` | the limit closure, via `suc∈or≡` | `:140-141` |
| `x∈Lλ` | `Lset-mono` from `# 1 ∈ lam` | `:188-189` |

The concrete site is `Site0 = Site (LsetS ω ω-ord) ω ω-ord (∈-irrefl ω)`
(`:199`), i.e. carrier `A = Lset ω`, generator stage `α = ω`, bounded set
`x = ∅`. Module `Site` (`:74`) is generic in `(A, α, ordα, α∉ω)`, so the
values above are supplied at every infinite stage, not only at `ω` (P-h,
DD4, section 4).

### 1.1 The term that cannot be written: `cardκ`

The first unsuppliable hypothesis is the telescope's third parameter:

```agda
cardκ : (δ : S) → ⟨ δ ∈ˢ κ ⟩ → (⟪ κ ⟫ ↪ ⟪ δ ⟫ → Empty.⊥)
```

with `IsCardinal` as defined at `src/L/BoundedSubset.lagda.md:1045-1046`
and `κ = sucV ω`. No term supplies it at this or any other concrete
ordinal the tree can name above `ω`:

- **MEASURED by search**: `IsCardinal` is defined in exactly two places,
  `src/L/BoundedSubset.lagda.md:1045-1046` and
  `src/ProbeLJ17.agda:746-747`; no application or instance exists
  anywhere in `src/`.
- **MEASURED by the plan record**: the tree has no cardinal chapter at
  all (`dev/PLAN.md:470`, LJ-1.46: "no cardinal chapter at all"), no
  equinumerosity notion, no initial ordinals beyond `ω`, no `κ⁺`
  (`_build/l3.31-ivprobe-report.md:536`). `SquareLaw`'s `Init`
  (`src/L/Ordinal/SquareLaw.lagda.md:692-698`) is a hypothesis, never a
  concrete supply.
- **INFERRED**: every ordinal the tree can construct beyond `ω` is a
  successor or a countable-cofinality limit, and none is initial. At
  `κ = sucV ω` the statement is FALSE: `⟪ sucV ω ⟫ ↪ ⟪ ω ⟫` exists
  because `ω` is Dedekind-infinite. This half is argued, not
  machine-checked, and sets no verdict on its own.

What the tower would have to provide: a concrete initial ordinal above
`α` with an `IsCardinal` certificate, exactly the `κ`/`κ⁺` hypotheses the
GCH chain already carries (`dev/LESSONS.md:3348`).

## 2. THE ALLCODES ANSWER

**Yes, it can: MEASURED.** The consumer that names `lam` produces
`AllCodes A ∈ Lset lam` in three machine-checked steps, all in module
`Site` (`src/ProbeLJ190A.agda:74`):

1. The code set's own stage is `δ₀ = stage (fst (AllCodes A))
   ((AllCodes A) .snd)` (`:78-79`), and `stage-mem` puts the code set in
   `Lset δ₀` (`AC∈Lδ₀`, `:84-85`). This is the delivered `AllCodes-stage`
   route of `[LJ-1.86]` (`src/ProbeLJ186A.agda:43-45`).
2. The consumer names `lam` as the omega-limit above the merge of the
   generator stage `α` and `δ₀`: `γ = bound2 α δ₀` (`:88-89`), `lam =
   boundingOrd ℕ (λ n → iter n γ)` (`:118-119`). Then `δ₀ ∈ lam` by
   `δ∈λ` (`:130-131`).
3. `Lset-mono` climbs from `Lset δ₀` to `Lset lam`:
   `AllCodes∈Lλ = Lset-mono {α = lam} {β = δ₀} δ∈λ AC∈Lδ₀` (`:193-194`).

The price is one sentence: **`lam` is not arbitrary.** It must be chosen
with room above the code set's stage. The frame's own data (`α ∈ lam`,
`succλ`, `x ∈ Lset lam`) does not imply `AllCodes A ∈ Lset lam` at an
arbitrary `lam`; the consumer supplies it by the choice of `lam`. The
telescope permits that choice, because `lam` is a free parameter.

The concrete instantiation is `Site0.AllCodes∈Lλ` via `:199`. The
premise `[LJ-1.89]`'s `witK` leaves open (`src/ProbeLJ189A.agda:267`) now
has a value at a real site.

## 3. STAGED OR DISCHARGED

**The frame hypothesis is supplied; the instantiation is not
discharged.** In the words C-38 demands: `AllCodes A ∈ Lset lam` is now
supplied, not restated, by a VALUE at a real site
(`src/ProbeLJ190A.agda:193-194`, instantiated at `:199`). That is the
first time anything supplies the layer's frame hypothesis.

The instantiation of `BoundedSubsetAt` as a whole does NOT go through:
`cardκ` receives no value (section 1.1). Nothing is discharged on a
parameter count; the telescope is staged at its third parameter. The
abort criterion's second branch fires: a hypothesis cannot be supplied,
so the report stops here and does not go on to `levelIn`, `cover` or the
post-leaf five.

## 4. THE DD4 ANSWER

**The site construction is generic in the stage, MEASURED by
construction.** Module `Site` (`src/ProbeLJ190A.agda:74`) takes the
carrier `A`, the stage `α`, its ordinality and `α∉ω` as module
parameters (P-h), and builds `lam`, `ordλ`, `succλ`, `α∈λ`, `x ∈ Lset
lam` and `AllCodes A ∈ Lset lam` as values at any infinite stage. The
concrete site is one module application (`:199`).

The per-site content is the carrier's code set (`AllCodes`), the stage
function (`L.Stage.stage`), and the bounded set `x`. A J tower would
instantiate the same module shape with its own code set and its own
stage function; the J side is **INFERRED**, since no J tower exists in
this tree.

One honesty note: `x = ∅` is the cheapest value that satisfies the
frame. A nontrivial `x` that is a set of codes over `Lset α` would not
satisfy `x⊆Lα`, because codes live above the carrier's stage. The frame
is satisfiable at `x = ∅`; the supply stops at `cardκ` regardless of
`x`.

## 5. NEGATIVES AND THEIR STATUS

1. "The consumer that names `lam` can produce `AllCodes A ∈ Lset lam`":
   **MEASURED TRUE**. The term is `Site.AllCodes∈Lλ`
   (`src/ProbeLJ190A.agda:193-194`), green at the C-12 cap, with the
   concrete instantiation at `:199`. The price is the choice of `lam`
   with room above the code set's stage.
2. "The instantiation of `BoundedSubsetAt` goes through":
   **MEASURED FALSE**. `cardκ` receives no value (section 1.1); the
   abort criterion stops the dispatch there.
3. "The tree supplies an `IsCardinal` instance at a concrete ordinal":
   **MEASURED FALSE by search**. `IsCardinal` appears only at
   `src/L/BoundedSubset.lagda.md:1045-1046` and
   `src/ProbeLJ17.agda:746-747`; no application exists in `src/`.
4. "No concrete ordinal beyond `ω` is provably initial in this tree":
   **INFERRED**. The plan record shows no cardinal chapter
   (`dev/PLAN.md:470`) and no initial ordinals beyond `ω`
   (`_build/l3.31-ivprobe-report.md:536`); at `κ = sucV ω` the statement
   is actually FALSE (an injection into `⟪ ω ⟫` exists). The inference
   sets no verdict on its own; negatives 2 and 3 carry the verdict.
5. "`succλ` can be supplied at the concrete `lam`": **MEASURED TRUE**.
   `Site.succλ` (`src/ProbeLJ190A.agda:140-141`), green, via the
   delivered shift lemma `suc∈or≡` (`src/L/Ordinal/Stages.lagda.md:137`).
6. "`x = ∅` satisfies the frame's `x` hypotheses": **MEASURED TRUE**.
   `x⊆Lα` (`:172-173`) and `x∈Lλ` (`:188-189`), green.
7. "The first `gn∈lam` attempt via `union-ax` typechecks": **MEASURED
   FALSE; it was a wall**. The `union-ax` elaboration over the concrete
   union did not return in 75 s and was killed (C-12). The delivered
   `memβ` route (`lam-info .snd .snd (lift (suc (lower n)))`) replaces
   it in one line (`:138`) and checks in under 2 s. The wall is
   reported, not current.

## 6. GATES

- `src/ProbeLJ190A.agda`: GREEN at the C-12 cap, one process.
  `GHCRTS="-A64m -I0 -M8g" agda src/ProbeLJ190A.agda`, 0.98 s user,
  1.86 s wall on the final run. Load average at run: 4.74 / 4.14 / 4.34,
  four users, the machine was NOT quiet. Earlier runs: 1.9-2.1 s wall at
  load 4.95 / 4.23 / 4.68.
- The wall: the first `gn∈lam` body (union-ax over the concrete union)
  ran past 75 s with no output and was killed with SIGINT (exit 130),
  one process at a time (C-12). No process was left alive; every later
  run returned.
- `scripts/check-fences.py --check`: clean, **87 masters**, run
  threshold 3.
- `scripts/lint-prose.py --check` on the probe and this report: exit 0.
- `scripts/lint-agda.py --check` on the probe: exit 0.
- Masters: none touched. `git status` is clean; the probe is ignored by
  `.gitignore:22` (`src/Probe*.agda`); this report by `.gitignore:2`
  (`_build/`). HEAD `e49628a` on `two-tower-bridge`, unchanged. No
  `make check`. No commit, no push.
- DD23: no mathematical prose was written or changed.

## 7. ARCHIVE USED

- `_build/lj-1.89-report.md`, read WHOLE. TOOK the verdict that `witK`
  is staged on the open premise `AllCodes A ∈ Lset lam` and that the
  consumer that names `lam` must produce it.
- `src/ProbeLJ189A.agda`, read WHOLE, focus 266-306. TOOK the frame
  shape (carrier `A`, `lam`, `ordλ`, `succλ`) and the premise's type
  (`:267`).
- `_build/lj-1.88-report.md`, read WHOLE. TOOK the finite-family route
  and the caveat that the code set's stage-fact is the instantiation's
  wiring obligation.
- `src/ProbeLJ188A.agda`, read WHOLE. TOOK `finSet-stage` and the
  stage-climb shape.
- `_build/lj-1.83-report.md`, read WHOLE. TOOK the `C = K` convenience
  verdict and the statement that it is NOT admissible as a discharge.
- `src/ProbeLJ183A.agda`, read WHOLE. TOOK the stage-frame facts and the
  chain's carrier reading (`A = Lset α`).
- `_build/lj-1.80-report.md`, read WHOLE. TOOK the stage `KFacts` value's
  parameters (`lam`, `ordλ`, `succλ`, `α`, `α∈λ`, `α∉ω`) as the frame's
  standing shape.
- `src/ProbeLJ180A.agda`, read WHOLE, focus 186-226. TOOK the `kfacts`
  value's field suppliers and the `ω∈lam` trichotomy pattern.
- `src/L/BoundedSubset.lagda.md`, read the telescope (`:1396-1402`), the
  enclosing `Devlin55` (`:1362-1367`), `IsCardinal` (`:1045-1046`), and
  the `LsetS`/`∅∈𝒟ₒ` provenance. TOOK the exact telescope order, which
  makes `cardκ` the first unsuppliable.
- `dev/LESSONS.md`, read WHOLE the sections C-38 as extended
  (`:3427-3511`), C-35 (`:3200-3241`), C-36 (`:3284-3331`), D-30
  (`:3332-3380`), D-29 (`:3242-3284`), C-37 (`:3381-3426`), and the
  `--for build` bundle via `scripts/rules.py`. TOOK the discharge
  standard, the write-the-unwritable-term discipline, and the
  price-what-the-consumer-needs rule.
- `archive/rud-route/`, SHAPE only (README). TOOK nothing; the archived
  `BelowLim` closes a general-limit stage fact of the same content class
  as the frame hypothesis, but the delivered `L.Stage.stage` route made
  it unnecessary.

## 8. LITERATURE USED

Banked: `[LJ-1.88]` settled how Devlin bounds his witness; one line,
spend nothing. This dispatch's supply question is answered by the
delivered tree alone.

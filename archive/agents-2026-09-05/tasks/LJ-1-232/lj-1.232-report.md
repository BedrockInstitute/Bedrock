# LJ-1.232 report: A1 and A3, the two cheap probes, in ONE dispatch

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. Probe only. No
master edited. No commit, no push.

The probes are `agents/tasks/LJ-1-232/ProbeLJ1232A1.agda` and
`ProbeLJ1232A3.agda`. Both typecheck green: `--safe`, exit 0.

Every negative is marked **MEASURED** (a machine result, or read at the cited
line) or **INFERRED** (my judgement). ASD-STE100 applies to this report.

## 0. LEAD: TWO VERDICTS, TWO NUMBERS

**A1: THE SITE DEMANDS MORE. MEASURED.** `LeastCardInj` restates over the
L-carrier with `⟨ isL α ⟩` per site and no global assumption, `--safe`, exit 0.
`⟨ isL α ⟩` alone does **not** suffice. The site needs three delivered L-lemmas:
`Lset→isL`, `ord∈Lset-suc`, `isL-trans` (and transitively `Lset-cumul`).
Section 3. The restated theorem is **54 non-comment code lines against the
standing 40**.

**A3: `stageBound` SUPPLIES β FOR FREE. MEASURED.** The canonical selection
`leastOf (orderAt β oβ) lem Good h` elaborates with **no β hypothesis**: β,
`IsOrd β` and `ω ∈ β` all come from `stageBound (fst a) (snd a)`. Section 4.
The selection with β production is **26 non-comment code lines against the
standing 45**.

**Both are per-tower, and neither is shared.** A1 is the level-hood
certificate, A3 is the definable well-order. Section 6.

## 1. A1: THE SITE DEMANDS MORE

**MEASURED.** `ProbeLJ1232A1.agda:74-153` restates `LeastCardInj` over the
L-carrier `𝒮ʟ`. The module is

```
module LeastCardInjL (α : S) (oα : IsOrd (fst α)) where
```

where `S = Σ[ x ∈ V ] ⟨ isL x ⟩`. There is **no** global "assume V = L"; the
per-site hypothesis is `snd α : ⟨ isL (fst α) ⟩`, carried by `α : S`.

The restatement elaborates green, `--safe`, exit 0. The three delivered
`⟨ isL α ⟩` sites (`src/L/Choice/Order.lagda.md:679`,
`src/L/Choice/Table.lagda.md:795`, `src/L/Choice/Transversal.lagda.md:75`) show
the shape this follows; none of them is the square-law chain, so this probe is
the first time one chain theorem took the per-site form.

**What `⟨ isL α ⟩` does NOT do.** The chain body uses `fst α` only; the
certificate `snd α` is never referenced in `LeastCardInjL`. The ordinal fact
the site actually needs is **`⟨ isL (sucV (fst α)) ⟩`**, which is NOT a
consequence of `⟨ isL α ⟩`: it comes from `ord∈Lset-suc` (an ordinal appears at
the stage after itself) plus `Lset→isL` (membership in a stage is level-hood).
Then `isL-trans` pushes that down to the members of `sucV (fst α)`, which is
what the crossing `up : ⟪ sucV (fst α) ⟫ → S` needs.

## 2. A3: stageBound SUPPLIES β FOR FREE

**MEASURED.** `ProbeLJ1232A3.agda:113-154` replaces `[LJ-1.134]` Part B's
fixed `(β : V ℓ) (oβ : IsOrd β)` parameters
(`agents/tasks/LJ-1-134/lj-1.134-report.md:238`) by the value `stageBound`
returns:

```
β  = stageBound (fst a) (snd a) .fst
oβ = stageBound (fst a) (snd a) .snd .fst
```

The selection `chosen = leastOf (orderAt β oβ) lem Good h` elaborates green
with **no β hypothesis**. The module takes only `(a : S) (D : S)` and the
non-emptiness `h`; β, `IsOrd β` and `ω ∈ β` are all supplied by `stageBound`,
so no site owes its own bound proof. **The crossing `up : Mem (Lset β) → S`
(`ProbeLJ1232A3.agda:122-123`) is the only thing a site adds**, and it is A2's
`Lset→isL`, not a bound proof.

The C-38 guard `Atω` (`ProbeLJ1232A3.agda:160-175`) instantiates `stageBound`
at the real ordinal ω and shows β, `IsOrd β` and `ω ∈ β` are produced, not
assumed.

## 3. A1's extra-lemma list, named (C-36)

The restated chain needs, beyond `⟨ isL α ⟩`:

| lemma | what it supplies | site |
|---|---|---|
| `Lset→isL` | `⟨ isL (sucV (fst α)) ⟩`: membership in a stage is level-hood | `src/L/Constructible.lagda.md:395` |
| `ord∈Lset-suc` | `sucV (fst α) ∈ Lset (sucV (sucV (fst α)))`: an ordinal appears at the stage after itself | `src/L/Ordinal/Stages.lagda.md:434` |
| `isL-trans` | level-hood of the members of `sucV (fst α)`, from the two above | `src/L/Constructible.lagda.md:379` |
| `Lset-cumul` (transitive) | used INSIDE `ord∈Lset-suc`, not demanded directly | `src/L/Ordinal/Stages.lagda.md:164` |

`⟨ isL (sucV α) ⟩`, `isL-trans` and `Lset-cumul` were the brief's candidates;
all three are confirmed, and `Lset→isL` is the missing fourth that carries the
first. **Every one of them is delivered in the tree** — the restatement is
possible and green, but it costs four delivered facts per site, not the one
`⟨ isL α ⟩` hypothesis.

**The line count.** The restated `LeastCardInjL` is **54 non-comment code
lines** against the standing 40. The ambient comparable is 44 lines
(`agents/tasks/LJ-1-156/lj-1.156-report.md:246`), so the L-restatement adds
about 10 lines: the `hSucα` certificate (3), the `up` crossing (3), and the
`fst` adaptations. The 54 is against 40, not against the 44-line ambient
comparable.

**Counting caliber.** `scripts/ledger.py` cannot count a probe (its scan is
scoped to `src/*.lagda.md`), so the figures are the ledger's caliber applied by
hand to a `.agda` file, as `[LJ-1.156]` and `[LJ-1.229]` did. The primary
figure is non-comment non-blank lines; the ledger caliber (non-blank, comments
included) is 62 for A1 and 29 for A3.

## 4. SECONDS, LOAD, RUN COUNT

One agda process at a time, `GHCRTS="-A64m -I0 -M8g"`, cap never raised, no
heap exhaustion, no wall. Load is the one-minute average at the start of each
run. The probe's own interface under `_build/2.8.0/agda/` was deleted before
every kept run, so the kept figures are the probe's own elaboration cost
against cached master interfaces.

| probe | runs | wall seconds | load |
|---|---:|---:|---:|
| A1 warm-up (discarded) | 1 | 100.15 | 4.61 |
| **A1 kept, cold** | 3 | **98.28, 100.62, 102.05** | 7.48, 4.42, 5.57 |
| A3 warm-up (discarded) | 1 | 2.18 | 4.63 |
| **A3 kept, cold** | 3 | **1.97, 1.23, 1.23** | 6.85 |

**A1 mean about 100.3 s** (three kept, upper 102.05 s). **A3 upper bound
1.97 s** (three kept). Both are inside the brief's "under 2 Agda minutes"
inference; A1 sits close to the line and I say so.

**A sub-finding, MEASURED, and it belongs to A1.** The L-restatement WITHOUT
`κ-min-at` (the minimality refutation) checks at **16.9 s cold** (16.70, 17.19,
16.82). Adding `κ-min-at` moves it to about 100 s. **The L-lemma machinery is
cheap; the expensive term is the ambient chain's own `κ-min-at` step, and the
L-restatement does not change it.** The 100.64 s ambient figure
(`agents/tasks/LJ-1-156/lj-1.156-report.md:216`) reproduces here. P-l: that is
a comparable, not my price.

The first A1 cold run carried load 7.48 (a transient spike; no sibling agda
was running when I checked, MEASURED by `ps`), yet its 98.28 s sits inside the
band of the other two. No verdict turns on it.

## 5. THE NEGATIVES, CLASSIFIED

- **MEASURED. A1: `⟨ isL α ⟩` alone does not suffice.** The crossing `up`
  needs `Lset→isL`, `ord∈Lset-suc` and `isL-trans`.
- **MEASURED. A1 elaborates green** (`--safe`, exit 0) with no global
  assumption, so the site CAN be restated; Route A-prime's premise stands.
- **MEASURED. A1 is 54 non-comment code lines against the standing 40.**
- **MEASURED. A3: `stageBound` supplies β for free.** The selection elaborates
  with no β hypothesis.
- **MEASURED. A3 is 26 non-comment code lines against the standing 45.**
- **MEASURED. No heap wall, no cap raise, no process past 20 minutes.**
- **INFERRED. The 54-against-40 overage is the L-restatement's honest cost.**
  The split (about 10 lines of L-machinery over the 44-line ambient body) is
  measured; that it is a fair reading of A1's standing is my judgement.
- **INFERRED. The structure-parameter form costs a telescope, not a rewrite.**
  Section 6.

## 6. DD4: NEITHER IS SHARED, AND THE PARAMETER FORM

`[LJ-1.227]` section 8 measured A1 and A3 per-tower: A1 is the level-hood
certificate, A3 is the definable well-order (`dev/literature/devlin-II5.md:387-389`).
**Neither probe shares code with the other, and that is correct.** A1's file
names `isL`, `Lset→isL`, `ord∈Lset-suc`, `isL-trans`. A3's file names
`stageBound`, `orderAt`, `leastOf`. The two probes have no module in common
except the copied A2 S1.

**Did the structure-parameter form cost anything?** I wrote both fixed to
`isL`/`𝒮ʟ` (single-tower), the natural probe form. The bodies are already
generic in everything except the tower structure:

- **A1**: the body uses only `fst`, `snd`, `⟪_⟫`, `sucV`, `ordSWO`, `leastOf`,
  plus the three named L-lemmas. The parameter form is a module telescope over
  the carrier and the three lemmas. **Cost: about 4 lines of telescope, body
  unchanged.** INFERRED, not measured: I did not write the two-tower form.
- **A3**: the body uses only `stageBound`, `orderAt`, `leastOf`, plus A2's
  predicate. The parameter form is a telescope over the bound-supplier and the
  order. **Cost: about 2 lines of telescope, body unchanged.** INFERRED.

`[LJ-1.156]` section 9 said the full two-tower form is "not measured here and a
probe is the wrong place to run it." I agree, and I record the estimate rather
than run it.

## 7. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-227/lj-1.227-report.md` sections 1, 3 and 8, read
  WHOLE.** TAKEN: A1's spec and candidates (section 1); A3's spec and the
  22-line selection (section 3); the per-tower mapping (section 8).
- **`agents/tasks/LJ-1-229/lj-1.229-report.md` and `ProbeLJ1229A.agda`, read
  WHOLE.** TAKEN: S1 (`injAt`, `injAt-out`, `injAt-in`) copied VERBATIM into
  `ProbeLJ1232A3.agda:74-105`; A2 measured at 186 with description plus
  adequacy at 27 (`lj-1.229-report.md:15-19`).
- **`agents/tasks/LJ-1-134/lj-1.134-report.md:238` and `ProbeLJ1134A.agda`,
  read WHOLE.** TAKEN: Part B's fixed β (`:238`), which A3 removes; the `up`
  crossing and `Good` predicate shapes.
- **`agents/tasks/LJ-1-136/lj-1.136-report.md:897-913`, `:12`.** TAKEN: the
  selection GO at 22 lines and 1.27 s.
- **`agents/tasks/LJ-1-156/lj-1.156-report.md:189`, `:252`.** TAKEN: the
  ambient chain at 393 lines and 133 s; `LeastCardInj` at 44 lines.
- **`src/L/Choice/Stage.lagda.md:328`, `src/L/BoundedSubset.lagda.md:56`, and
  the three sites `src/L/Choice/Order.lagda.md:679`,
  `src/L/Choice/Table.lagda.md:795`, `src/L/Choice/Transversal.lagda.md:75`.
  READ the source, never a report.** TAKEN: the `stageBound` payload, the
  ambient `open hPropStructure 𝒮ᵥ`, and the two per-site shapes (ambient
  carrier plus `⟨ isL α ⟩`, and the L-carrier direct).
- **`archive/dev/TASKS-archived.md` and
  `archive/src/2026-08-09-rud-route/`.** READ for shape. The archived
  square-law route sits over the AMBIENT carrier `𝒮ᵥ`, exactly like the live
  chain's ambient form, and carries no per-site `⟨ isL α ⟩`. **What would NOT
  transfer: the archived route never did A1's per-site L-restatement, because
  its GCH statement was reached through the rud-closure machinery that
  `[LJ-1.11]` ruled out. The `LeastCardInj` body shape transfers unchanged; the
  per-site carrier restatement does not exist there to copy.**

## 8. LITERATURE USED (DD18)

- **`dev/literature/devlin-II5.md:387-389`.** USED. The per-tower content is
  exactly two objects: the level-hood certificate (Step C) and the definable
  well-order (Steps D, G). A1 is object 1, A3 is object 2.
- **`dev/literature/devlin-II5.md:370-383`.** USED. The step table: C1/C2 and
  D/G are the PER-TOWER rows.

**Does Devlin relativize per-site or globally?** Devlin's level-hood is the
uniformly-Δ₁ formula with its Σ₁ witness, stated ONCE at the carrier and used
at every site through the witness — a per-site certificate whose ONE uniform
definition is global. That matches A1's shape: the definition of `isL` is
global and delivered; what A1 adds is the per-site consumption (`⟨ isL α ⟩`,
`⟨ isL (sucV α) ⟩`, `isL-trans`). **Does Devlin price the well-order's
selection?** He uses the canonical order's ORDER TYPE (Step G) rather than a
`leastOf` search, so he does not pay A3's selection cost at all; the selection
is A-prime's own machinery because A-prime priced order types out
(`src/L/Ordinal/SquareLaw.lagda.md:1-11`).

## 9. WORKING TREE, AS MY REPORT DESCRIBES IT

Three files added under `agents/tasks/LJ-1-232/`:

- `lj-1.232-report.md`, this report.
- `ProbeLJ1232A1.agda`, A1: `LeastCardInj` restated over the L-carrier.
- `ProbeLJ1232A3.agda`, A3: the canonical selection with β from `stageBound`.

No master edited. No commit, no push. I did not touch
`src/Everything.lagda.md`, `src/L/Choice/Name.lagda.md`,
`agents/tasks/LJ-1-230/` or `agents/tasks/LJ-1-231/`. I did not run
`make check`.

`scripts/lint-agda.py --check` exit 0 on both probes. `scripts/check-probes.py`
clean. The report was written as a skeleton in the first minutes and filled
incrementally (C-22).

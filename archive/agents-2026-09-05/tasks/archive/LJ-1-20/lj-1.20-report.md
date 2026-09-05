# LJ-1.20 report: the stage-arithmetic kit

## 1. THE VERDICT

DELIVERED. The kit is `src/L/Ordinal/StageArith.lagda.md`. It has 75
in-fence lines. The cold rate is 0.0100 seconds per line. The rate is under
the AC module baseline of 0.011472. The bucket is AC-side or shared, by
import closure.

## 2. THE THREE STATEMENTS

Statement 1 is `+ω` and its closure predicate:

```agda
+ω : S → S

closedω : S → Type (ℓ-suc ℓ)
closedω α = (d : S) → ⟨ d ∈ˢ α ⟩ → ⟨ +ω d ∈ˢ α ⟩
```

Statement 2 is the code-set bound:

```agda
boundCloses : (α δ : S) (cl : closedω α) → ⟨ δ ∈ˢ α ⟩
            → (b : S) → ⟨ b ∈ˢ Lset (+ω δ) ⟩ → ⟨ b ∈ˢ Lset α ⟩
```

Statement 3 is the environment bound:

```agda
envCloses : (α δ : S) (cl : closedω α) → ⟨ δ ∈ˢ α ⟩
          → (env : S) → ⟨ env ∈ˢ Lset (sucIter 3 δ) ⟩ → ⟨ env ∈ˢ Lset α ⟩
```

Both closing theorems go through `Lset-mono`, with no unsealing. The
supporting family is `sucIter`, `+ω-in`, `+ω-mem`, `+ω-sup`, `+ω-iter`,
`sucIter-ord` and `+ω-ord`.

## 3. THE NUMBER

The file has 75 non-blank lines inside the Agda fences. That is the ledger
caliber, comments included (`scripts/ledger.py` count rule). The non-comment
body is 64 lines.

## 4. SECONDS AND RATE

The cold check takes 0.75 seconds. The interface is absent; the dependencies
are warm. The warm check takes 0.70 seconds. One Agda process,
`GHCRTS="-A64m -I0 -M16g"`, exit 0. That is the baseline protocol's setting.

The cold rate is 0.0100 seconds per line. The warm rate is 0.0093. The AC
module baseline is 0.011472 (`dev/ledger.toml:2545`). The cold rate is 87
percent of the baseline.

The bucket is AC-side. The import closure contains only `Base`, `FOL`,
`V.*`, `L.Constructible` and `L.Ordinal`. No wing module is in the closure.
The file lives under `src/L/Ordinal/`, outside every GCH chapter. The
catalog wiring decides the final bucket.

## 5. WHAT THE J TOWER REUSES UNCHANGED

The archived J-side module `L.Rud.OrdBlocks` carried the same extension
family (`archive/rud-route/src/L/Rud/OrdBlocks.lagda.md:87-152`). The new
kit carries these definitions with unchanged statements and proofs:
`sucIter`, `+ω`, `+ω-in`, `+ω-mem`, `+ω-sup`, `+ω-iter`, `sucIter-ord` and
`+ω-ord`. The module takes the same parameters, `{ℓ}` and `lem`. A J-side
consumer opens it with the same arguments.

The kit is generic. No tower name appears in it. No `Lset` presentation
appears in a statement that does not need one (P-l). The `+ω` union body is
sealed at birth, so both towers see an atom (R-38).

## 6. DID THE J-SIDE SHAPE TRANSFER

The shape transfers; the code does not. The J side answered the
bound-in-carrier question by restricting the carrier and recording the
bound as a parameter of the meta clause
(`archive/rud-route/src/L/Rud/LevelSigma.lagda.md:203,209-213`). This kit
uses the same shape: `closedω α` and `δ ∈ˢ α` are the bound as premises.
The concrete statements are re-derived at the L site, as P-l requires.

## 7. LITERATURE USED

- `dev/literature/devlin-II5.md:222-227`. USED. Item 2 names the load
  bearing requirement: the Σ₁ witness lives inside the carrier. The two
  closing theorems serve that requirement.
- `_build/literature/dev2.txt:676-678`. USED. Devlin's bound sits at δ+4
  because he codes formulas as finite sequences. The tree codes them as
  trees, so the bound is δ+ω, and the closure kit is needed here.
- `dev/literature/devlin-II5.md:295-312`. USED. The summary restates the
  carrier-closure requirement as load bearing.
- WHY NOT `dev/literature/j-hierarchy.md`. The omega-times-alpha indexing
  does not bear on the ω-block. The probe surveyed it
  (`_build/lj-1.19-report.md:8`).
- WHY NOT `dev/literature/devlin-errata.md`. The probe verified it does not
  cover Chapter II section 5 (`_build/lj-1.19-report.md:8`).

Nothing else in `dev/literature/` bears on this kit.

## 8. ARCHIVE USED

- `archive/rud-route/src/L/Rud/LevelSigma.lagda.md:203,209-213`. The
  bound-as-parameter shape. Section 6 rests on it.
- `archive/rud-route/src/L/Rud/OrdBlocks.lagda.md:87-152`. The `+ω` family
  and its ordinality. The kit re-derives that slice.
- `_build/lj-1.19-report.md`. Read in full. Took the GO, the two gate
  answers, the kit list in section 7, and the D-10 residue.
- `_build/lj-1.15-review.md:62-66,374-381,404-406`. The review named the
  shared stage-arithmetic kit and ordered its commission.
- `dev/LESSONS.md:174` (P-h), `:2264` (P-l), `:829` (R-38), `:1316`
  (D-10). The rules this block runs on.
- `dev/ledger.toml:2475-2546`. The AC module baseline, its protocol, and
  the calibration figure.
- WHY NOT `archive/dev/*`. Nothing in the archived task and decision
  records bears beyond the review citations. The probe said the same
  (`_build/lj-1.19-report.md:9`).

## 9. WHAT I AM NOT SURE OF

1. The cold wall time depends on the OS page cache. The first run after a
   pause reads dependency interfaces from disk and takes 1.6 to 1.8
   seconds. The next run takes 0.74 to 0.85 seconds. The user time is flat
   at 0.7 seconds. The `check-ratio` protocol measures modules in
   sequence, with the cache hot. I report the hot-cache figure.
2. `+ω-out` and `+ω-limit` are not delivered. `+ω-out` doubles the cold
   time. I measured 1.73 seconds with it and 0.74 seconds without it. It
   is not in the probe's statements. The tree has no `isLimit` machinery.
   A consumer that needs either law should price it first.
3. `+ω-ord` is delivered, but no consumer in the current tree uses it. The
   crossing's limit certificates are the intended consumer.
4. The bucket claim rests on import closure. The catalog wiring decides
   the final bucket.

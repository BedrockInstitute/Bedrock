# LJ-1.30 Report: Price the upstream cure, making consAtL constant-free

## 1. THE VERDICT

GO, at about 110 lines added to two masters and zero consumer edits. The
cured clause checks at 0.0095 to 0.0104 seconds per line, cold. The gate
says GO at or below 0.013. The cure is a measured price, not a hypothesis.

The brief's named risk does not bind. The 16 constants do not need
environment slots. They are all `con (# 0)`, and `# 0` is the empty set
definitionally (`Cubical/HITs/CumulativeHierarchy/Constructions.agda:164`).
"The first component is # 0" is "the first component is empty". Emptiness
is Delta-0 with bounded quantifiers only. So the reader is constant-free
in place, with no arity change at any consumer.

Two probes measure the price. `src/ProbeLJ130A.agda` is the cured clause
with the delivered `erase`. It typechecks. `src/ProbeLJ130B.agda` proves
the new reader's adequacy. It typechecks. Both are untracked and never
committed.

## 2. THE CONSUMER COUNT

`consAtL` has 6 consumer masters and its home master, 7 in total. The
count is a grep of all masters, not an impression.

| master | use sites | where |
|---|---:|---|
| `L.Coding.Model` (home) | 20 | definition `:1490`, adequacy `:1493`, transport `:1505`, formulas `:1574` `:1578`, `:1890` `:1896`, satisfaction `:1583` `:1602` `:1610` `:1902` `:1930` `:1941` |
| `L.Coding.Sat` | 11 | import `:43`, formulas `:167` `:170` `:175` `:180`, satisfaction `:236` `:250` `:258` `:265` `:291` `:301` |
| `L.Coding.Bridge` | 17 | import `:61`, `consAtL-out` `:247`, `consAtL-in` `:256`, uses `:407` `:413` `:425` `:431` `:468` `:477` `:494` `:500` |
| `L.Coding.Sound` | 9 | import `:53`, transport uses `:685` `:706` `:734` `:757` `:790` `:807` `:833` `:849` |
| `L.Coding.Unique` | 9 | import `:52`, transport uses `:619` `:634` `:677` `:690` `:754` `:772` `:820` `:840` |
| `L.Choice.Internal` | 7 | import `:57`, formula `:590`, satisfaction `:622` `:626` `:644` `:654` `:660` |
| `L.Choice.Adequate` | 5 | imports `:43` `:48`, `consAtL-in`/`out` `:462` `:463` `:505` |

Six probes also use `consAtL`. They are untracked and outside the count.

## 3. DOES THE COUNT REACH 0?

Yes. Agda's own `countFo` verifies it at both levels.

The uncured count is 16, not 17, in the [LJ-1.27] variant. The numeral
already moved to a slot there. `ProbeDD25E.agda`'s error computes
`countFo (Clause.existBndAt C T B N) = 16`, then rejects `refl` for 0.
`ProbeDD25F.agda` verifies `consAtL {1} zero zero zero` is 16 and
`prAtL`, `appAt`, `sucAtL` are 0.

The 16 are all in `tagAt`. `consAt` calls `tagAt zero 0 (suc m)` twice.
Each `tagAt` names `con (# 0)` eight times. `shiftPairAt` contributes 0;
it is built from `prAt` and `sucAt` only. The review's "tagAt and
shiftPairAt" attribution is wrong; the count is right.

`ProbeLJ130A.agda` verifies the cured counts. `countFo (consAt0L {1}
zero zero zero) ≡ 0` holds by `refl`. `countFo (Clause.existBndAt {2}
zero (suc zero) zero zero) ≡ 0` holds by `refl`. And
`Cnt.erase (Clause.existBndAt {n} C T B N) refl` typechecks for any `n C
T B N`, which forces the whole-clause count to 0.

## 4. THE ARITY WIDENING'S COST

Zero lines, because the widening is not needed. That is the finding that
makes this route cheap.

The tag value is `# 0`, and `# 0 = ∅` definitionally
(`Constructions.agda:164`). The readers say "the first component is the
empty set". That statement is Delta-0 without any constant:

```agda
sgl0At k = (∃̇∈ (var k) (∀̇∈ (var zero) ⊥̇))
        ∧̇ (∀̇∈ (var k) (∀̇∈ (var zero) ⊥̇))
```

`pair0At` and `tag0At` follow the same shape. `consAt0` is `consAt` with
the two `tagAt zero 0 (suc m)` calls replaced by `tag0At zero (suc m)`.
The arity of `consAt0` is `n`, exactly as before.

The rewrite price is then:

| file | change | lines |
|---|---|---:|
| `L.Coding.Environment` | three readers and their Delta-0 witnesses | ~15 |
| `L.Coding.Environment` | meta machinery: `∅-uniq`, shapes, `prChar∅` | ~75 |
| `L.Coding.Environment` | `tag0At-adequate` | ~6 |
| `L.Coding.Environment` | `consAt` and `Δ₀-consAt` | ~4 changed |
| `L.Coding.Environment` | `consAt-adequate` proof | 3 changed |
| `L.Coding.Model` | `bddCons`, `consAtL` | ~8 changed |
| consumers | none | 0 |

The basis is `ProbeLJ130B.agda`, 130 non-blank lines, which contains the
whole new adequacy proof and typechecks. The statement of
`consAt-adequate` is unchanged, because `pr ∅ W` and `pr (# 0) W` are the
same type by `refl`. Its proof swaps three lemma calls only. The six
consumers keep their text unchanged.

For contrast, the slot-based widening the brief feared would cost about
200 to 300 lines across the consumers. Each of the 58 use sites gains an
environment element, a re-indexed formula or type, and a hypothesis. That
cost is avoided, so it is not paid.

## 5. WHAT THE CURED CLAUSE MEASURES

The cured block is `src/ProbeLJ130A.agda`, 289 non-blank code lines. It
is `ProbeDD25E` with the constant-free reader, so the failing `refl`
lives. The line convention calibrates: the same count gives
`ProbeLJ127.agda` 283, matching the [LJ-1.27] report.

| run | user seconds | rate |
|---|---:|---:|
| cold, first complete | 2.74 | 0.0095 |
| cold, hash-forced re-check | 3.00 | 0.0104 |
| warm (interface read) | 1.20 | 0.0042 |

The gate says GO at or below 0.013 and NO-GO at or above 0.10. The cured
block lands at 0.0095 to 0.0104. That is GO. The uncured block lands at
0.114 to 0.118 (`_build/lj-1.27-report.md:15-18`).

The body, net of the 1.20 second warm read, checks in about 1.5 to 1.8
seconds. That is the base-content rate, 0.0053 to 0.0062 seconds per
line, plus the one `abs₀` at the original clause. The mechanism the
review hypothesized is measured: the transfer is two syntactic `cong`s
and one `abs₀`, and the cost is the `abs₀` alone.

One Agda process ran at `GHCRTS="-A64m -I0 -M8g"` per C-12. No sibling
Agda process ran.

## 6. IS THE REWRITE REVERSIBLE

Yes. The rewrite touches two masters, `L.Coding.Environment` and
`L.Coding.Model`. Their upward cone is 29 masters and 28 masters
respectively, nearly the same set, 29 in the union. All 29 must
re-typecheck. Their source text does not change.

The six consumers re-check against unchanged adequacy statements. Their
proofs use `consAtL-adequate` and `consAtL-transport` only; they never
inspect the formula's syntax. Probe B proves the one new lemma the
adequacy chain needs.

Reversal is a small diff: restore `consAt`, `bddCons`, and delete the new
readers. The delivered layer is green today, so a failed landing restores
the current interface, and no consumer text is lost.

The real re-verification cost is time, not text. The 29-master cone is
the L coding and choice layer plus `L.Hierarchy` and `L.Model`. A full
`make check`-style re-typecheck is the honest gate for the landing.

## 7. DD4: DOES THE J TOWER USE consAtL

No. The J tower has no modules in this tree. It is planned at `[LJ-3.4]`
(`dev/PLAN.md:487`). `consAtL` appears only in `L.Coding.*` and
`L.Choice.*` masters.

The [LJ-1.27-R] finding stands: the J certificate avoids the syntax
entirely under D-26. So the J tower does not care about `consAtL` today.

For DD4, the constant-free shape is the shared shape. It is cleaner on
both towers, and it costs the L tower about 110 lines once. A fresh J
environment-extension clause, if one is ever written, should use the
same constant-free readers.

## 8. ARCHIVE USED

- `_build/lj-1.27-review.md:217-246` for the mechanism, the hypothesis,
  and the named risk.
- `src/ProbeDD25E.agda` and its error for the uncured count and the
  failing `refl` (re-run at this task).
- `src/ProbeDD25F.agda` for the per-reader counts (re-run at this task).
- `_build/lj-1.27-report.md:8-18` and `:70-95` for the uncured gate and
  the `abs₀` figure.
- `src/FOL/Count.lagda.md:598-611` and `:617-637` for `erase` and
  `erase-inv`.
- `src/L/Coding/Environment.lagda.md:338-343` for the constants, and
  `:353-481` for the adequacy proof.
- `src/L/Coding/Base.lagda.md:109-131` and `:181-230` for `sgl-char`,
  `pair-char`, and `prChar`.
- `src/L/Coding/Model.lagda.md:1463-1516` for `bddCons` and `consAtL`.
- `dev/LESSONS.md` P-l, P-m, P-t, P-u, D-10, D-26, read through
  `scripts/rules.py --for probe` and `--for recon`.

## 9. WHAT I AM NOT SURE OF

The rewrite itself is not built, only priced. The two probes cover the
formula, the count, the transfer, and the new adequacy lemma. The
remaining `consAt-adequate` proof body is the delivered text with three
lemma calls swapped. I did not copy and re-check it, because that is the
rewrite, not a probe. The swap is mechanical, and probe B removes the
only new risk.

The cold figure has noise. The first complete check is 2.74 seconds and
the forced re-check is 3.00 seconds, a 9 percent delta. Both land GO, so
the verdict does not depend on the exact number.

I did not profile the cured block. The body rate matches the base-content
rate, which says the crossing is nearly free, but the attribution to
`abs₀` is inference from the [LJ-1.27] profile, not a fresh profile.

The clause is one clause. The whole statement block has twelve clauses,
and each quantifier clause uses `consAtL`. The numeral-to-slot move is
per clause. I measured one clause, the hardest; the other clauses are
smaller or similar, and the same two edits apply to each.

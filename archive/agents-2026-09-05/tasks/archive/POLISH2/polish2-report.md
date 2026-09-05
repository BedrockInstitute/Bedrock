# Polish-2 report: the non-P1 rud chapters plus the three riders

Batch `[L3.31-PZ]`. Scope: the twelve masters under `src/L/Rud/` named in the
brief. `CodePred`, `CodeSet`, `SatTable` and `src/Everything.lagda.md` were
never opened for writing. No git command was run.

The headline is not the line count. It is rider 1: **`StepInL` fell from
174.7 s to 89.3 s cold, a 48.9% cut on the most expensive file in the rud
trunk**, by paying one imported invocation once instead of three times.

## 1. Totals

Non-blank lines inside ` ```agda ` fences, before and after.

| file | before | after | delta | |
|---|---:|---:|---:|---|
| `Realize.lagda.md`   |  796 |  789 |   −7 | −0.9% |
| `Step.lagda.md`      |  750 |  755 |   +5 | +0.7% (rider 1's sealed alias) |
| `Describe.lagda.md`  | 1182 | 1046 | −136 | −11.5% |
| `Order.lagda.md`     |  581 |  578 |   −3 | −0.5% |
| `Switch.lagda.md`    |  803 |  803 |    0 | untouched, see §5.1 |
| `SatSets.lagda.md`   | 1289 | 1289 |    0 | untouched, see §5.2 |
| `StepInL.lagda.md`   | 1993 | 1989 |   −4 | −0.2% (the win here is time, not lines) |
| `Bridge.lagda.md`    |  512 |  512 |    0 | untouched, see §5.3 |
| `DefInJ.lagda.md`    |  207 |  198 |   −9 | −4.3% |
| `BaseBlock.lagda.md` |  407 |  393 |  −14 | −3.4% |
| `ClassJ.lagda.md`    |   31 |   31 |    0 | already at its floor |
| `OrdBlocks.lagda.md` |  111 |  111 |    0 | untouched, see §5.4 |
| **total**            | **8662** | **8494** | **−168** | **−1.9%** |

The rate is well under the first batch's −7.2%, and deliberately so. That batch
polished four chapters that had never had a detail pass; this scope is
dominated by three files (`StepInL`, `SatSets`, `Switch`) whose density is
mandated by LESSONS entries (I-5's written branch types, Rule 8's named
continuations, R-35's small-index statements). Where the duplication was real
and the law was silent, the cut was deep: `Describe` gave up 11.5%.

Verification: all twelve typecheck green under `GHCRTS=-M12g`, one agda at a
time, re-run in dependency order after the last edit (§4). `lint-agda.py` and
`lint-prose.py` exit 0 on all seven touched files. The three FORBIDDEN
downstream consumers (`CodeSet` 20 s, `CodePred` 11 s, `SatTable` 3 s) also
typecheck green against the changed interfaces, which is the strongest
available evidence that the exports really are frozen.

## 2. The three riders

### 2.1 Rider 1: the `right-spec` invocation hotspot. Delivered, −85.4 s.

**Diagnosis first.** Rather than assume the r5a datum transferred, I profiled
`StepInL` cold (`--profile=definitions`). It did, overwhelmingly:

| definition | before |
|---|---:|
| `Frames._._._.right≡q` | 29,299 ms |
| `Frames._._._.right≡q` | 28,258 ms |
| `Reads._._._.right≡q`  | 26,101 ms |
| **the three together** | **83,658 ms of a 173,331 ms total (48%)** |
| `Slot._._.k1`          | 31,720 ms (unrelated, untouched) |
| `Slot.tupleIn`         | 25,876 ms (unrelated, untouched) |
| `values∈L`             | 15,474 ms (inside the seal, paid once by design) |

Every one of the three was the same two lines:
`right≡q = subst (λ t → right t ≡ q) (sym b≡) (right-spec p q)`.

**The fix, and why it is in `Step` and not in `StepInL`.** The brief said to
seal the alias "in the consuming chapter". There are two consuming chapters:
`Step` (one invocation) and `StepInL` (three). Putting the alias in `StepInL`
would have left `Step` still paying its own. Putting it in `Step`, which
`StepInL` already imports, makes the whole trunk pay **once**:

```agda
opaque
  -- perf: R-38's invocation half. `right-spec` costs about 26 s to invoke
  -- (`left-spec` costs 64 ms), so the trunk invokes it exactly ONCE, here,
  -- and every consumer downstream reads this equation instead.
  right-at-pair : (b p q : V ℓ) → b ≡ pr p q → right b ≡ q
  right-at-pair b p q b≡ = subst (λ t → right t ≡ q) (sym b≡) (right-spec p q)
```

The exported type is the read: it mentions `right b` and `pr p q` at variables
only, so no consumer re-fires the `sett`-over-separation tower. No separate
R-36 read lemma is needed because the sealed thing *is* an equation. `Step`
re-points its one site, `StepInL` imports `right-at-pair` and re-points all
three; `right-spec` left `StepInL`'s import list entirely.

**Measured** (cold, dependencies warm, `GHCRTS=-M12g`, one agda at a time):

| file | before | after | delta |
|---|---:|---:|---:|
| `Step`    |  27.5 s |  28.9 s | +1.4 s |
| `StepInL` | 174.7 s |  89.3 s | **−85.4 s (−48.9%)** |
| **pair**  | 202.2 s | 118.2 s | **−84.0 s (−41.5%)** |

The three `right≡q` entries are gone from the after-profile entirely. `Step`'s
+1.4 s is the seal's own overhead plus run-to-run noise; it was already paying
the single invocation before.

### 2.2 Rider 2: Step's missing `Sset-zero` export. Delivered, −14 lines.

`Sset-zero : Sset ∅ ≡ ∅` is born in `L.Rud.Hierarchy` (line 399) and was simply
absent from `Step`'s `open ConcreteS using (…) public` list, which carries the
other ten `Sset-*` facts. Added it there.

`BaseBlock` then lost **two** local re-proofs, not one:

- `Sset-zero-∅` (10 lines), the one the k1 report named. Its single use at
  `∅∈Ssetω` now reads `sym Sset-zero`. Confirmed by grep that no file outside
  `BaseBlock` referenced `Sset-zero-∅` before removal.
- `sset0-empty` (5 lines, `where`-bound inside `sTally zero`), a *second*,
  independent derivation of the same fact in the same file that the report had
  not spotted. It collapses to one `subst` along `Sset-zero`.

`Sset-out` became an unused import in `BaseBlock` as a result and was dropped
from the import list, which the agda linter would otherwise have caught.

### 2.3 Rider 3: StepInL's sealed `values∈L` layer-cap region. Verified correct; no change.

The region is already the R-36 shape, and the shape is right at every point:

1. `suc⁴` is sealed `opaque` at its birth site in `Bridge` (663-664) with a
   `-- perf:` marker naming P-i's layer cap.
2. Two read lemmas sit beside it in their own `opaque unfolding suc⁴` block,
   exactly as R-36 prescribes: `suc⁴∈` (membership of the four-fold successor
   in a limit) and `suc⁴-up` (the four-layer lift).
3. `StepInL`'s block is a third such block. It unfolds the seal only to build
   `values∈L` and exports the truncation-explicit type `ValuesInU u (suc⁴ ζ)`.

**No consumer re-derives what a read lemma should export.** `Bridge`'s `Reduce`
(778-802) binds `ζ₄ = suc⁴ ζ` and reaches its two facts through `suc⁴∈` and
`suc⁴-up`; it never opens the tower. The only outside consumer of `values∈L` is
`SatTable:427`, which passes it wholesale into `module R = Reduce …`. A grep for
`sucV (sucV (sucV` across all of `src/` finds the four-layer form only inside
`Bridge`'s own read-lemma bodies (legitimate, inside the seal); the other hits
are a *three*-layer tower in `L/Godel/InL.lagda.md`, a different chapter on a
different route.

Nothing to add, nothing to re-point. Rider 3 cost one read and no edit.

## 3. The detail pass, per file

### 3.1 `Describe.lagda.md` (1182 → 1046, −136, −11.5%)

The whole of it is two frames added to the existing `Chain` module, which every
`F*Desc` module already aliases as `Ch`. This is the brief's named target
("per-operation boilerplate a shared frame absorbs").

| change | sites | lines | why it reads better |
|---|---:|---:|---|
| new `Chain.defSet⊆`: the "definable subset ⊆ target" half of every `-defSet≡` | 8 | −52 (+12 frame) | the eight `sub₁` bodies were **byte-identical** modulo the bound variable, the formula name and the target. Each was 9 lines; each is now `sub₁ = Ch.defSet⊆ Φₙ dΦₙ (Fn a b) Fn-desc-out`. The fact that they were the same proof is now visible instead of being something a reader has to verify eight times. |
| new `Chain.⊆defSet`: the "member of A, member of the target ⇒ member of the definable subset" half | 8 | −84 (+12 frame) | the same `∈-asFiber`/`m`/`q`/`subst`/`chain`/`desc-in` chain, 13 to 18 lines, written out eight times (twice inside `PairValFrame` alone). Each site now names only what is genuinely its own: how the member gets into `A`, and how it gets into the target. |

Both frames take the formula, its `Δ₀` witness and the target **explicitly**,
which is P-i [F] ("explicit indices first") and matches how the pre-existing
`Ch.chain` was already called. The in-file precedent that this frame shape is
cheap was `PairValFrame`, which had already been doing exactly this for F11-F14;
the pass simply extends it to the seven operations that had not been framed.

Cost: none. `Describe` checks in **7.8 s after, against 8.8 s before**. It got
faster, and 136 lines shorter.

Staging followed C-10: the frames were added and typechecked *before* any site
was re-pointed, then the re-points went in as scripted exact-string swaps with a
per-swap occurrence assertion (`assert n==1`), typechecked after each batch.
Every stage was green.

### 3.2 `Realize.lagda.md` (796 → 789, −7)

The brief's other named target: the `andC`/`orC`/`notC`/`impC` sub/chr pairs.

`impC` already bound `A = eval a (map fst ws)` and `B = …`; `andC`, `orC` and
`notC` did not, and spelled the two expressions out 12, 12 and 4 times
respectively. Applying `impC`'s own idiom to its three siblings collapses every
`fwd`/`bwd` signature onto one line and makes the four connectives visibly the
same shape, which is what the prose above them claims. Line saving is modest
(−7); the readability gain is the point.

Every `fwd`/`bwd` keeps its written type (I-5), every named continuation stays
named (Rule 8). Neither region is inside an `opaque` block (the file's only seal
is the three-line `lemL`), so I-3 does not bind here.

Cost: none. **18.9 s after, against 19.2 s before.** This mattered enough to
measure explicitly, because I-4 was born in this file.

### 3.3 `BaseBlock.lagda.md` (407 → 393, −14)

Entirely rider 2; see §2.2. `10.9 s` after.

### 3.4 `DefInJ.lagda.md` (207 → 198, −9)

The fragment Σ-type was written out three times (the `DefFragment` declaration,
`fragment-from-limit`'s `go` signature, and `Discharge.defStage∈J`'s `atFrag`
signature), and the limit-fragment Σ twice. Two **private** aliases `Frag` and
`LFrag` absorb both: `go`'s twelve-line signature becomes
`go : LFrag ζ γ → Frag ζ γ`, and `atFrag`'s six-line domain becomes one line.

`Frag`/`LFrag` are `private`, so `DefInJ`'s export surface is byte-identical;
`DefFragment` and `LimitFragment` keep their names and are definitionally the
same types they were, which is why `SatTable` (which imports `DefFragment`)
still typechecks untouched.

### 3.5 `Order.lagda.md` (581 → 578, −3)

`memberStage-in` was a verbatim copy of `memberStage-least` specialized at
`γ := α`: same `PT.rec`, same pattern-lambda continuation, same `trace-exists`
call. `memberStage-least` moved above `memberStage-in` (a move **within one
` ```agda ` fence**, so no prose was crossed and no i18n marker moved), and
`memberStage-in` is now the one-line corollary it always was:

```agda
memberStage-in α ordα m = memberStage-least α ordα m α ordα (m .snd)
```

Both names, both types and the declaration count are unchanged.

## 4. Verification

Re-typechecked in dependency order after the last edit, one agda process at a
time, `GHCRTS=-M12g` throughout. No heap event, no wall event, no kill.

| file | result | recompile |
|---|---|---:|
| `Realize` | OK | warm |
| `Describe` | OK | warm (7.8 s measured at its own edit) |
| `Step` | OK | warm (28.9 s measured at its own edit) |
| `Order` | OK | 4 s |
| `ClassJ` | OK | warm |
| `OrdBlocks` | OK | warm |
| `BaseBlock` | OK | warm (10.9 s measured at its own edit) |
| `SatSets` | OK | warm |
| `Switch` | OK | 10 s |
| `DefInJ` | OK | 8 s |
| `Bridge` | OK | 44 s |
| `StepInL` | OK | 88 s |

Then, as an interface check I could run without git: the three FORBIDDEN
downstream chapters, which between them import `Sset-zero`'s host, `right-at-pair`'s
host, `values∈L` and `DefFragment`:

| file | result |
|---|---|
| `CodeSet` | OK, 20 s |
| `CodePred` | OK, 11 s |
| `SatTable` | OK, 3 s |

Linters, on the seven touched files: `scripts/lint-agda.py` exit 0,
`scripts/lint-prose.py` exit 0.

## 5. Interface deltas, and what I judged unsafe to touch

### 5.0 The complete interface delta

Exports were frozen apart from these, and nothing else changed name, type,
telescope or seal:

1. **`Step`: `+ right-at-pair`** (rider 1, additive, `opaque`).
2. **`Step`: `+ Sset-zero`** in the `open ConcreteS … public` list (rider 2,
   additive, re-export of a name born in `Hierarchy`).
3. **`BaseBlock`: `− Sset-zero-∅`** (rider 2 mandates the removal; verified by
   grep to have had no consumer outside its own file).
4. **`Describe`: `+ Chain.defSet⊆`, `+ Chain.⊆defSet`.** This is one delta
   beyond the riders and I want it flagged rather than buried. It is purely
   additive, and it is unavoidable: the brief names Describe's per-operation
   boilerplate as a target for "a shared frame", and a shared frame has to have
   a name. It cannot be `private`, because the seven `F*Desc` modules that use
   it are siblings of `Chain`, not children. No existing name or type moved.
5. `DefInJ`'s `Frag`/`LFrag` are `private` and therefore **not** an export delta.

### 5.1 `Switch` (803 lines, untouched)

The one large opportunity here is the five-copy `⋁`-flattening idiom in `Hops`
(842-915), worth about 34 lines. **Not applied.** The collapse replaces five
*named* `PT.rec` continuations with one shared combinator taking pattern
lambdas, and named continuations with spelled payloads are exactly what Rule 8
and I-5 are about; the brief's own instruction is "do not restructure proofs
whose shape a LESSONS entry mandates". This is a measured-law region, not
boilerplate. The remaining Switch items were worth 0 to 4 lines each and were
not worth a 10 s recompile plus the risk.

### 5.2 `SatSets` (1289 lines, untouched)

Three real opportunities, none of them safe enough for this batch:

- A generic `read3R` merging `In3R-read` and `Eq3R-read` (~18 lines). It needs
  the relation's hProp level pinned explicitly through a module alias or it
  meets R-34 head-on, and R-34's measured symptom is walling the *whole file*.
- Merging the `Dif2`/`Dif2'` families (~20 lines). The two `-read` lemmas
  return differently shaped tuples, so the generic needs a coordinate selector.
- A `Tᶜ n φ = F1 (Us (suc n)) (T (suc n) φ)` alias for its 23 occurrences
  (~7 lines). This is a named alias for a composite of set operations sitting in
  statement positions, which is R-38's exact hazard class ("a consumer's alias of
  a transparent imported operation is a birth site").

Each of these wants its own measured probe, which this batch was not chartered
to spend, on a 1289-line file whose baseline I never measured.

### 5.3 `Bridge` (512 lines, untouched)

`Lstep-absorb` (506-527) is provably `Lstep⊆ (Jset μ limμ)`: same hypotheses in
the same order, and `ValuesIn μ limμ ζ` is `ValuesInU (Jset μ limμ) ζ`. Worth
about 13 lines. **Not applied:** `Lstep⊆` is defined 100 lines *later* than
`Lstep-absorb`, so collapsing them requires moving a code block across two prose
sections that are each written about the block they sit under. That is a C-3
hazard (prose stating an invariant is load-bearing) and the brief says prose
stays untouched. It is a genuine simplification and worth doing in a batch
chartered to move prose with it.

A shared `Lup` for the four copies of
`up y h = Lset-mono {α = sucV ξ} {β = ξ} (self∈sucV ξ) h` is worth ~5 net lines
and is safe; it was dropped only for time, after `Bridge`'s 44 s recompile made
it a poor rate.

### 5.4 `OrdBlocks` (111 lines, untouched)

The savings here (~10 lines) are concentrated in naming
`sett (Lift {ℓ-zero} {ℓ} ℕ) F` as an `ωSet` alias. **Not applied:** that is a
named alias for a `⋃`-tower's underlying `sett`, which is simultaneously Rule 9
("a named alias in a unification position is fatal") and P-c's subject matter.
Ten lines is not worth opening that class on a file this small. The genuinely
free part (the doubled two-line `F` `where`-binding) nets −1 line after the
helper and was not worth the edit.

### 5.5 Dead exports found but deliberately left

The survey turned up a substantial amount of exported-but-unreferenced code.
All of it is **report-only** under exports-frozen, and all of it is described by
prose that would be orphaned by removal. Recorded so it is not rediscovered:

| file | name | lines |
|---|---|---:|
| `BaseBlock` | `finiteMember` | 18 |
| `Bridge` | `Lpair` → `Lpair-limit` → `Lpr-limit` (a closed dead chain) | 36 |
| `Bridge` | `matched-level∈L` | 4 |
| `Bridge` | `Bridged.level-bridge` | 3 |
| `DefInJ` | `fragment-from-limit` | 8 (after §3.4 shrank it) |
| `Order` | `old-before-new` | 10 |
| `Order` | `Jset-choice` | 5 |
| `OrdBlocks` | `_⊆_`/`ext-⊆`, `+ω-sup`, `suc-⊆` | 11 |
| `ClassJ` | `isPropIsJ`, `isJ-trans` | 7 |

Two of these carry a documentation defect worth the owner's eye:
`OrdBlocks`'s prose at line 161 claims "the successor-inclusion lemma carries
the descent", but `+ω-limit` does not call `suc-⊆` at all, so the prose is stale
(a C-3 instance). And `OrdBlocks` line 35 imports `∃[]-syntax`, which has zero
uses in the file.

### 5.6 Cross-file duplication, out of scope by construction

Six of the eight surveyed files each define their own two-to-three line `ext-⊆`,
and three define their own `Jtr u v v∈J u∈v = Sset-trans γ {x = v} {y = u} u∈v v∈J`
(`DefInJ` 175 and 261, `Bridge` 125, `SatSets` 1645). Hoisting either into
`L.Rud.Step` would save roughly 10 lines across the set, but it is a new export
on `Step` beyond the riders' authorization, so it is left for a ruling.

## 6. Lesson candidates

1. **(sharpens R-38 / the r5a datum) When an expensive imported invocation has
   consumers in more than one chapter, the single sealed invocation belongs in
   the EARLIEST consumer, not in each consuming chapter.** The r5a report's
   rule was "pay it exactly once"; this batch found that "once" has to be read
   trunk-wide, not file-wide. Putting `right-at-pair` in `Step` rather than in
   `StepInL` is what took the pair from 202.2 s to 118.2 s instead of to
   roughly 144 s. Measured: three invocations at 26-29 s each removed from
   `StepInL`, zero added anywhere.

2. **(C-14's shape, second instance) A missing export breeds more than one
   re-proof.** The k1 report recorded one local `Sset-zero-∅` in `BaseBlock`.
   The same file contained a second, independent derivation of the same fact
   (`sset0-empty`) that no report had noticed, and `Bridge` contains a third
   (its own top-level `Sset-zero`, left in place because removing it is an
   export change). When a missing export is filed, grep the fact, not the name.

3. **(craft) Profile before applying a transferred perf datum, even a trusted
   one.** The r5a datum said `right-spec` costs 25.7 s per invocation. It
   transferred exactly (26-29 s per site), but the same profile also showed that
   `Slot._._.k1` at 31.7 s and `Slot.tupleIn` at 25.9 s are a *separate* and
   larger-per-site cost in the same file that no report had attributed. One
   175 s profiling run bought both the confirmation and the map of what rider 1
   would not fix.

## 7. Residue

`StepInL` is still the trunk's most expensive file at 89.3 s, and after rider 1
its cost is concentrated in two definitions that no lesson currently covers:
`Slot._._.k1` (31.7 s) and `Slot.tupleIn` (24.9 s), 63% of what remains. Neither
was in this batch's charter. They are the obvious next perf target and they
have a fresh profile pointing at them.

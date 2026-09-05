# Polish-R report: line-by-line refinement of the four committed rud-trunk masters

Batch: QUALITY pass over `src/L/Rud/{OrdArith,Ops,Images,Hierarchy}.lagda.md`.
Exported names, exported statement types, module telescopes and every `opaque`
seal are unchanged (verified mechanically, see §5). Prose blocks untouched.

## 1. Totals

| file | code lines before | after | delta | typecheck (cold recompile) |
|---|---|---|---|---|
| `src/L/Rud/OrdArith.lagda.md`  |   98 |   87 | −11 (−11.2%) | 1.0 s |
| `src/L/Rud/Ops.lagda.md`       |  474 |  446 | −28 (−5.9%)  | 2 s |
| `src/L/Rud/Images.lagda.md`    |  298 |  267 | −31 (−10.4%) | 58 s (baseline 58 s) |
| `src/L/Rud/Hierarchy.lagda.md` |  236 |  226 | −10 (−4.2%)  | 2 s |
| **total**                      | **1106** | **1026** | **−80 (−7.2%)** | |

"Code lines" counts every line inside a ` ```agda ` fence, blank lines included
(the brief's 1,084 figure counts non-blank lines; the deltas are the same).
`Images` is the one expensive file in the scope; its cost is unchanged by this
pass (58 s before, 58 s after), which was measured explicitly because a
regression there would have been the real risk.

All four typecheck green under `GHCRTS=-M6g`, one at a time. No heap exhaustion.

## 2. Change catalog, per file

### 2.1 `OrdArith.lagda.md` (98 → 87)

| change | sites | lines | why it reads better |
|---|---|---|---|
| the symmetric pair `excl₁/excl₂` + `mem₁/mem₂` folded into one local `memOr : (u w : S) → ⟨ u ∈ˢ sucV w ⟩ → ⟨ u ∈ˢ w ⟩ ⊎ (u ≡ w)` | 1 | −7 | the proof's symmetry was written out twice with the roles swapped; now the symmetry is *visible* (`go (memOr β γ β∈) (memOr γ β γ∈)`) instead of being something the reader has to check line by line |
| `(λ p → inl p)`, `(λ p → inr p)` → `inl`, `inr` | 2 | 0 | the direct combinator instead of its eta-expansion |
| `isPropSucc` loses its own `α` parameter (it was applied only at the enclosing `α`, which it shadowed) | 1 | 0 | removes a shadowed binder; the reader no longer has to check that the inner `α` is the outer one |
| `succ-not-zero` reuses `predecessor-mem` instead of redoing its `subst` | 1 | −1 | the proof now *says* what it means: the predecessor is a member, and `∅` has none |
| single-consumer `zero-hp` inlined into its one use | 1 | −3 | `lem ((α ≡ ∅) , isSetS α ∅)` is as legible as the name was |

### 2.2 `Ops.lagda.md` (474 → 446)

| change | sites | lines | why it reads better |
|---|---|---|---|
| new private `Fibre`/`fibre`: one call yields the index *and* the path back | 13 | −20 net (+6 helper) | the old code called `∈-asFiber {a = u} {b = x} h` **twice** at every site, once for `.fst` and once for `.snd`, each behind its own restated signature: 4 lines and a duplicated computation per fibre. Now 2 lines, one call. `∈-asFiber` mentions fell from 26 to 2 (the import and the helper). |
| new private `prCond`: the F3/F4/F6 index condition pulled back along the two fibre paths | 3 | +2 net (+5 helper) | three verbatim copies of the same two-line `subst`/`cong₂` became one named fact whose name says what it does. Costs two lines, buys the de-duplication the owner's rule asks for (3 consumers ≥ 2). |
| `t≡ = subst (λ w → ⟨ t ≡ₕ w ⟩) (sym q) refl` → the path `sym q` written directly, binding dissolved | 5 | −10 | `⟨ a ≡ₕ b ⟩` *is* `a ≡ b`, so the transport was a two-line detour around a term already in hand |
| every forward `go` destructures the `sett` index in its pattern instead of projecting | 6 | −4 | this is the big one for legibility even where it is line-neutral: `p .snd .snd .fst` / `p .snd .snd .snd` chains (up to four deep in F3/F4) became named index variables `mᵤ`, `mz`, `mᵥ`, `cond` |
| `m_z` renamed `mz` | 2 | 0 | `m_z` is a mixfix name with a hole in it, which is not what was meant |

Every `where` binding inside the six `opaque` blocks keeps its type signature:
see §4, this is forced.

### 2.3 `Images.lagda.md` (298 → 267)

| change | sites | lines | why it reads better |
|---|---|---|---|
| new private `fibre` (the `∈ₛ` analogue of `Ops`'s): `h .fst` plus `equivFun identityPrinciple (h .snd)` in one call | 3 calls covering 4 former sites | −11 | four copies of the same four-line index/path pair collapse to one line each; in `⋂pair` the two copies (`sub₁`'s `n₀/q₀` and `sub₂`'s `m₀/p₀`) were *identical* and are now one shared `fs` |
| `⋂pair`'s and `rightSlice-pair`'s doubly-nested `where` flattened (the single-consumer `w≡a`/`w≡b` and `w∈⋂`/`w∈R` bindings dissolved into their one use) | 2 | −8 | removes a whole level of `where` nesting from the two hardest proofs in the chapter; the `go` continuation now sits one indent shallower |
| `sepSet-pair`'s already-declared predicate `ϕ` put to work (it was **dead code**: both uses re-spelled the lambda, and the lambda shadowed the outer `w`) | 2 | 0 | kills a shadowed binder and a 110-char line; `ϕw : ⟨ ϕ w ⟩` now says exactly what the separation clause is |
| `pair-eq-snd`'s `go`: the two identical `inr` branches merged into `go (inr vw) _ = sym vw` | 1 | −1 | a duplicated branch is a question the reader has to answer ("are these really the same?"); now there is nothing to check |
| `F11`-`F14` specs: two composed `cong`s (or a `cong₂` with a nested `cong`) → one `cong₂` each | 4 | −4 | each spec is now a single line that reads "rewrite the left slot and the right slot"; the four became visibly the same shape, which is what the prose claims |
| `F8-spec`'s two directions: `PT.rec _ (λ { (m , q) → ∣ m , q ∣₁ })` → `PT.rec _ ∣_∣₁` | 2 | −2 | the pattern lambda was the eta-expansion of `∣_∣₁` |
| `F10-spec`: `fwd` destructures the index (`((_ , h) , q)`), `bwd`'s `h'`/`p₀`/`q` chain collapsed onto the shared fibre | 2 | −4 | the backward direction is now one `subst` inside another instead of a five-name chain |
| `rightSlice-pair`'s `h1 = singl∈ refl` inlined; the single-consumer `x₀` pair-packings inlined | 3 | −3 | `singl∈ refl` needs no name |
| `cong (λ t → ⋃ t)` → `cong ⋃_` | 4 | 0 | the operator itself instead of a hand-rolled lambda around it |

### 2.4 `Hierarchy.lagda.md` (236 → 226)

| change | sites | lines | why it reads better |
|---|---|---|---|
| new private `ix∈ : (α : S) (m : ⟪ α ⟫) → ⟪ α ⟫↪ m ∈ᵗ α` | 5 | −7 net (+3 helper) | "the `m`-th member of `α` is a member of `α`" was written out four times: twice as a two-line `where`-bound `mem`, twice inline. It is one fact and now has one name. |
| `Sset-in`: the `m`/`p` restatements of `fib .fst`/`fib .snd` dropped | 1 | −3 | the file already used the `fib .fst`/`fib .snd` idiom in `Sset-limit`; now both sites read the same way |
| `Sset-out`'s `atFib` takes the fibre pair itself, so `uStep` hands it to `PT.map` directly instead of through `λ { (m , sm≡v) → atFib v x∈ₛv m sm≡v }` | 1 | −1 | removes an eta-expanding pattern lambda, and makes `Sset-out`'s `atFib` the same shape as `Sset-limit`'s |
| `Sset-limit`: the single-consumer `p` alias of `fib .snd` dropped | 1 | −2 | same idiom as above, applied consistently |

## 3. Typecheck timings

Measured under `GHCRTS=-M6g`, one Agda at a time (C-12), on the real recompile
(a `touch` does not force one: Agda 2.8 keys on the source hash, so only a
content change re-checks).

| file | after this pass | note |
|---|---|---|
| `OrdArith` | 1.0 s | |
| `Ops` | 2 s | measured after the final edit stage |
| `Images` | 58 s | committed baseline measured at 58 s for comparison; unchanged |
| `Hierarchy` | 2 s | |

One wall was hit and cleared during the batch; see §4.

## 4. The wall, and the new law it produced

**Symptom.** The first draft of `Ops` (identical mathematics, but with the
noise-only type signatures dropped from `where` bindings) ran past 600 s and was
killed. It was not a conversion blowup: the error, once the run was bounded, is
`UnsolvedConstraints` with a metavariable storm, and Agda says why:

```
warning: -W[no]MissingTypeSignatureForOpaque
Missing type signature for opaque definition fx.
Types of opaque definitions are never inferred since this would
leak information that should be opaque.
```

**Law.** *Inside an `opaque` block, every definition needs a type signature,
`where`-bound ones included.* An unascribed binding is turned into
`postulate fx : _`, and the resulting metas propagate through the whole block:
one dropped signature in `F1-spec` was enough to wall the file. This is a
cheap, deterministic, immediately-diagnosable failure, but it is invisible until
you try it, and it is the reason the six `opaque` blocks in `Ops` keep every
signature while `Images` and `Hierarchy` (whose only seal is `Sset`) could drop
the redundant ones.

Suggested LESSONS entry: a new **I-3** in the inference-trap series (or an
extension of C-11, which is the sibling layout trap). I did not edit
`dev/LESSONS.md` — out of scope for this batch.

**Method note.** The bisect cost four minutes: save the draft, restore the
committed file, reapply in three stages (helpers + F1/F2, then F3/F4, then
F6/F7) with a per-swap occurrence assertion and a typecheck after each stage
(C-10). Every stage was green in ≤ 4 s, so the wall was localized to the one
change class that the stages did not carry.

## 5. Frozen-interface verification

Compared the sorted set of every declaration at indent 0-2 (which covers both
top-level exports and the ones inside `opaque` blocks and `module F15Of`)
between `HEAD` and the working tree. The only differences are private and
`where`-local names:

- `OrdArith`: `excl₁`/`excl₂`/`mem₁`/`mem₂` → `memOr`; `isPropSucc` loses its
  own parameter; `zero-hp` gone. All `where`-bound.
- `Ops`: `Fibre`, `fibre`, `prCond` added inside the existing `private` block.
- `Images`: `fibre` added inside the existing `private` block.
- `Hierarchy`: `ix∈` added in a new `private` block; `atFib` (a `where` helper)
  changes shape; `mem`/`p` (`where`-bound) gone.

No exported name, no exported statement type, no module telescope, and no
`opaque` seal changed. `F0`-`F9` and their specs, `left`/`right`/`F8`/`F10`-`F15`
and their specs, `Sset`/`Sset-compute`/`Sset-suc`/`Sset-limit`/`Jset` and the
whole `OrdArith` API are byte-identical in signature.

`git status --porcelain` shows exactly four modified paths, all mine:

```
 M src/L/Rud/Hierarchy.lagda.md
 M src/L/Rud/Images.lagda.md
 M src/L/Rud/Ops.lagda.md
 M src/L/Rud/OrdArith.lagda.md
```

(`Describe.lagda.md`, `Realize.lagda.md`, `Step.lagda.md` and the `Realize.cut*`
files are other agents' untracked work; not touched, not opened for writing.)

Linters: `lint-prose.py` and `lint-agda.py` both exit 0 on the four files.
Everything left uncommitted.

## 6. Identified but NOT applied

These are real opportunities that need either an export rename, a cross-file
move, or a measurement this batch was not chartered to spend. Recorded for the
post-wave catalog.

1. **Hoist the six `sett` index types out of their `where` blocks** (`Ops`).
   Each forward `go` re-spells its operation's index Σ in the signature because
   `idx` lives inside `F3`'s own `where` and is invisible to `F3-spec` — 4 to 6
   lines per operation, ~28 lines in total, and the worst remaining reading
   burden in the file. Private top-level `Idx3 x y` and friends would cut each
   signature to one line. **Not applied:** it moves a definition across the
   `opaque` boundary and puts a named alias where the elaborator unifies
   (Rule 9 / R-21 hazard). It wants its own measured probe, not an opinion.

2. **One shared fibre helper instead of three.** `Ops.fibre` (over `∈`),
   `Images.fibre` (over `∈ₛ`) and `Hierarchy.ix∈` are the same idea three times.
   A small shared module (`V.Fibre`, or an addition to `V.Coding`) would carry
   all three. **Not applied:** new file / cross-file move.

3. **The `∈∈ₛ {a = _} {b = _} .fst/.snd` bridge**, ~55 remaining sites across the
   three files, every one spelling both implicits. Two private wrappers would
   shorten all of them. **Not applied:** P-i's rule [F] ("explicit indices
   first") is precisely why they are written this way; changing it is a
   measurement, not a cleanup.

4. **The `go₀`/`go₁` nested-truncation plumbing** in `Ops`: each nested `⋁`
   layer costs 3-4 lines of signature plus a one-line body (F3 and F4 pay it
   twice each), ~26 lines in the file. A `⋁`-elimination combinator would
   collapse them. **Not applied:** the named-continuation discipline (Rule 8,
   P-i [C]) is load-bearing here, and this is exactly the shape those laws were
   written about.

5. **`sucV-inj-ord` never spends its second ordinality.** Only `ordβ .fst` is
   used; `ordγ : IsOrd γ` is dead in the body. The lemma is true from
   `IsOrd β` alone. Dropping the argument is an **exported type change**, so it
   is out of scope — but it is a genuine simplification of the statement and
   worth the owner's ruling.

6. **`Hierarchy.Jset-mono` ignores both limit hypotheses**, and `Jset`/`Jset-trans`
   ignore theirs (`Jset α _ = Sset α`). That is deliberate interface shape (the
   limit-indexed subfamily), not an oversight — recorded so it is not
   "discovered" again.

7. **`Images.rightSlice`'s index type** is re-spelled in `rightSlice-pair`'s `go`
   signature (three lines, one of them 118 characters). Same class as item 1.

8. **`Hierarchy.Sset-zero`'s two `∅-empty (∈∈ₛ … .fst …)` fragments** have two
   consumers, so a merge is permitted by the rule, but it saves no lines and
   adds a name; left alone deliberately.

# R4 report: the canonical well-order and the AC endgame

Batch `[L3.31-R4]`, in-harness Opus, 2026-08-03. Deliverable:
`src/L/Rud/Order.lagda.md` (new, the only source file touched). No commits, no
edits to `Everything`, no edits to any sealed module, no edits to
`Describe.lagda.md`.

## 1. Headline

**Green.** `L.Rud.Order` typechecks cold (warm dependencies) in **2.56 s**,
**644 code lines** in **1,092 total lines**. Stop-line was 2,400 code lines: the
batch landed at **27% of it**. The well-foundedness work alone is **117 lines**
against the 1,000-line pause trigger. All four gate linters (markers, prose,
agda, glossary) exit 0.

| section | code lines |
|---|---|
| header and imports | 39 |
| Two ground orders (ordinals, operation index) | 101 |
| Producers (the tree, grounding, its propositionality) | 40 |
| The comparison (`≺`, stage monotonicity, irr/tri/trans) | 108 |
| Grounded producers, and the descent (well-foundedness, `traceSWO`) | 117 |
| The producer view, in both directions (`prod-mem`, `trace-exists`) | 64 |
| The least producer (`leastTrace`, the first LEM spend) | 26 |
| The order of a level (`memberKey`, `Sset-order`) | 21 |
| Coherence (`order-coherent`, `order-agrees`) | 16 |
| The birth stage (`memberStage` and its three readings) | 48 |
| The successor clauses (`memberStage-new`, `old-before-new`) | 39 |
| Choice, without syntax (`Jset-order`, `Sset-choice`, `Jset-choice`) | 25 |
| **total** | **644** |

Timings, in order (each is a cold check of `Order` with warm dependencies,
`GHCRTS=-A64m -I0 -M12g`, one check at a time per C-12):

| chunk | result |
|---|---|
| ground orders + producer type | 0.83 s |
| + the comparison and its three laws | 1.17 s |
| + well-foundedness and `traceSWO` | 1.35 s |
| + producer view + least producer | 1.61 s |
| + level order + coherence + birth stage + endgame | 1.72 s |
| + successor clauses (first attempt) | **WALL, >600 s** |
| after the reshape | 2.56 s |

## 2. The architectural departure, and why

The brief asked for a transfinite recursion along the tower producing an order
of `S_α` at each stage, with limits as unions of the earlier orders and a
coherence lemma proved alongside. **I did not build that recursion.** The
delivered order is the same mathematical object, obtained without any recursion
into `Type`:

- A **producer** is an inductive tree: `prod-self δ`, or
  `prod-image δ i p q`. It mirrors the sealed step's three arms exactly, with the
  membership arm leaving no node (a set merely carried up from `S_δ` is produced
  at its own earlier stage, by its own producer), and only the image arm carrying
  a triple, as the brief specified.
- `prod-value` decodes a producer into `V`; `Grounded` is the side condition the
  step supplies (an image at stage `δ` has each argument produced strictly below
  `δ`, or equal to the self producer of `δ`).
- `_≺_` compares producers by stage, then arm (self before image), then operation
  index, then first argument, then second, all by structural recursion on the two
  trees. Its trichotomy, irreflexivity, transitivity and well-foundedness are
  proved once.
- The order of the level `S_α` is `pullSWO traceSWO (memberKey α ordα) inj`,
  where `memberKey` is the **least producer** of a member.

Two things this buys, both load-bearing:

1. **Coherence is a one-liner.** `memberKey α ordα (x , xα)` does not depend on
   `α` except through the (propositional) existence hypothesis, so
   `order-coherent` is `cong (leastTrace x) (squash₁ _ _)`. Under the recursion
   the brief sketched, coherence is a transfinite induction over a recursion
   whose compute rule is only propositional, which is the expensive part of the
   whole design.
2. **The limit case disappears.** There is no union of earlier orders to take:
   the relation at a limit index is the same relation, restricted. That is
   exactly what the coherence lemma asserts, so nothing is lost.

**Why the naive tree order would have been wrong, and why `Grounded` exists.**
Before writing anything I checked whether the lexicographic order on unrestricted
producer trees is well founded. It is not: the trees of a fixed stage and
operation index are order-isomorphic to the lexicographic square of the whole
tree type, so the order type `γ` would have to satisfy `γ ≥ 1 + γ·γ`, impossible
for `γ ≥ 2`. The bound that rescues it is exactly the one the step supplies (an
image's arguments live in `S_δ ∪ {S_δ}`), which is why `Grounded` is a predicate
and the order lives on the subtype `Trace = Σ Producer Grounded`. This is the
single design fact the whole chapter turns on, and it is recorded in the prose.

**Faithfulness to SZ p. 11.** The delivered order is candidate 1 / SZ's `<^A_β`
clause for clause at a successor index, and this is now machine-checked rather
than asserted:

- clause (a), old before new: `old-before-new` (an `x ∈ S_β` precedes any
  `y ∈ S_{β+1} ∖ S_β`), resting on `memberStage-new` (a member of `S_{β+1}` that
  is not in `S_β` has birth stage exactly `β`) and `stage-below`;
- clause (b), both old: `order-agrees` read at `α := sucV β`, `β := β`;
- clause (c), both new: definitional. Both keys carry stage `β`, so `_≺_` falls
  through its stage layer to arm, index, first argument, second argument, which
  is the definition printed in the chapter.

Two riders on (c), argued but not formalized (they are about *how* the least
producer looks, not about the order, which is fixed by the key):

- The self arm is ours, not SZ's: our step is cumulative (SZ's `S(U)` is not
  self-containing in the same way), so `S_β` itself is a new element of
  `S_{β+1}`. Putting the self producer below every image at the same stage makes
  `S_β` the least new element of `S_{β+1}`, and makes the argument order on
  `S_β ∪ {S_β}` equal to `<_β` with `S_β` on top. Both are the only choices that
  keep the clause structure.
- A least producer has least sub-producers: replacing an argument's producer by
  the least producer of the same set gives a strictly smaller producer with the
  same value, and grounding survives because `≺` never raises the stage. Hence
  minimizing the tree lexicographically *is* minimizing SZ's triple `(i, u, v)`
  with `u, v` compared by `<_β`.

## 3. Where LEM was spent

Exactly twice, both on searches, both through `L.WellOrder.Base`'s `leastOf`,
and both recorded in the chapter's opening prose:

1. **`leastTraceOf`** (`leastOf traceSWO lem (valueIs x)`): choosing the least
   producer of a set. This is where the well-foundedness of the producer order is
   consumed.
2. **`Sset-choice`** (`leastOf (Sset-order α ordα) lem (isIn y)`): choosing the
   least element of a non-empty member of a set of the level, i.e. the choice
   function itself.

Nothing else is classical **in this chapter's own text**. The chapter's telescope
carries `lem` for the two searches and also passes it to `L.Ordinal.Linear`
(`ord-tri`, used to build `ordSWO`'s trichotomy) and to `L.Rud.Step` /
`L.Rud.OrdArith`; the ordinal trichotomy is a third consumer, inherited, not new.
The tree, its comparison, trichotomy, transitivity, well-foundedness, `prod-mem`,
`trace-exists`, and every coherence and birth-stage reading are constructive.

## 4. The coherence lemma, exact statements

Two exports. The primary one is about the **key**, and is stronger than the
classical form (no relation between the two levels is required):

```agda
order-coherent : (α β : S) (ordα : IsOrd α) (ordβ : IsOrd β) (x : S)
               → (xα : ⟨ x ∈ˢ Sset α ⟩) (xβ : ⟨ x ∈ˢ Sset β ⟩)
               → memberKey α ordα (x , xα) ≡ memberKey β ordβ (x , xβ)
```

and its consequence for the relation:

```agda
order-agrees : (α β : S) (ordα : IsOrd α) (ordβ : IsOrd β) (x y : S)
             → (xα : ⟨ x ∈ˢ Sset α ⟩) (yα : ⟨ y ∈ˢ Sset α ⟩)
             → (xβ : ⟨ x ∈ˢ Sset β ⟩) (yβ : ⟨ y ∈ˢ Sset β ⟩)
             → Sset-below α ordα (x , xα) (y , yα)
             ≡ Sset-below β ordβ (x , xβ) (y , yβ)
```

`Sset-below α ordα` is definitionally the relation field of `Sset-order α ordα`
(the `pullSWO` relation reduces to it), so this is a statement about the bundle's
order and not about a look-alike. The classical shape (`β ∈ α`, restrict the
later order along `Sset-mono`) is this statement with the membership at `α`
supplied by `Sset-mono`; see §6 for why the transported proof must **not** appear
in the statement.

## 5. Well-foundedness, and the combinator reuse record

Reused from `L.WellOrder.Base` **as-is**:

- `SWO`, `Tri`/`lt`/`eq`/`gt` (the bundle and its trichotomy data);
- `natSWO` and `pullSWO` for the operation index: `opSWO = pullSWO natSWO opIx
  opIx-inj`, with `opIx-inj` from the retraction `opAt`;
- `pullSWO` again for the level order: `Sset-order α ordα = pullSWO traceSWO
  (memberKey α ordα) (memberKey-inj α ordα)`. This is the single most valuable
  reuse in the batch: trichotomy, irreflexivity, transitivity and
  well-foundedness of every level order arrive free, and none is re-proved;
- `leastOf` / `IsLeast` twice, as §3 records.

**Not reused, and why.** `sumSWO`, `prodSWO`, `listSWO` and `connex` were the
expected lexicographic building blocks and none of them fits. The producer
order is *self-referential* (its innermost slots are producers again), so it
cannot be assembled from bundles on already-ordered ingredients; the kit's
combinators all take finished `SWO`s. The comparison is therefore hand-written
as a structural recursion on the two trees. Two consequences worth noting:

- The kit's "two refutations instead of an equality" discipline (`prodSWO`'s
  level workaround, with `connex` as the exchange lemma) is **not needed here**:
  the producer relation and producer paths both live at `Type (ℓ-suc ℓ)`, so the
  equality can sit in the relation directly. That removed `connex` from the
  consumer list and made transitivity a plain path-composition argument.
- `accProd`'s nested-descent shape *is* the pattern precedent, and the batch
  follows it: `accImg`'s descent is `accProd` three deep (operation index, first
  argument, second argument) wrapped inside a transfinite induction on the stage
  (`accBelow`, via `∈-induction`), with `accArg` as the escape hatch that turns
  grounding into accessibility of an argument. `accMove` (a `Σ≡Prop`-built path
  in `Trace`, then `subst (Acc _⊰_)`) does all four transports; the kit's
  `accList` uses the same `subst`-along-the-recovered-path move.

`ordSWO` (the ordinals under membership) is built by hand: `ord-tri` repackaged
as `Tri`, `∈-irrefl`, `IsOrd`'s own transitivity, and `∈-induction` for
accessibility. It is then routed through a `module Stage = SWO ordSWO` alias so
the three laws the tree order uses are the bundle's, not loose lemmas.

## 6. The wall, its diagnosis, and the cure (lesson candidate)

**Event.** Appending the successor-clause section took the check from 1.72 s to a
hard wall: killed at 600 s with no progress. C-12 protocol applied (kill, save,
deletion-bisect, one check at a time, timed runs with a 120-180 s ceiling).

**Bisect.** Three steps, each a timed run:

| variant | result |
|---|---|
| `memberStage-new` only | 35 s (included a dependency recompile of `Step`) |
| `+ old-before-new` | 10 s |
| `+ old-agrees` | still running at 120 s, killed |

The offender was a single lemma, `old-agrees`, and it stayed a wall when spelled
with all arguments explicit, so it was not an under-application or a metavariable.

**Cause.** Its statement was the classical restriction shape:

```agda
old-agrees : ... → Sset-below β ordβ (x , xβ) (y , yβ)
                 ≡ Sset-below (sucV β) (suc-ord ordβ)
                     (x , Sset-mono {α = sucV β} {β = β} (self∈sucV β) x xβ)
                     (y , Sset-mono {α = sucV β} {β = β} (self∈sucV β) y yβ)
```

The **transported membership proof** `Sset-mono … x xβ` sits *inside the type*
being compared, at the concrete index `sucV β`. Checking the body against that
type puts the proof term in a conversion position, and `Sset-mono` at `sucV β`
unfolds through `Sset-in` into `⟪ sucV β ⟫` and the union tower that `sucV`
is. That is P-c's mechanism (a `⋃`-tower in an index re-normalizes at every
concrete set former it meets) reaching the codebase through a *proof term in a
statement* rather than through an operation's index. Note the near-miss:
`order-agrees` with `α`, `β` **variables** checks in milliseconds; only the
instantiation at `sucV β` explodes, so the trap is invisible at the definition
site and fires at the consumer.

**Cure (P-i class [E], reshape the obligation).** Take the membership at the
larger level as a *variable* rather than as a transported term:

```agda
order-agrees : … (xα : ⟨ x ∈ˢ Sset α ⟩) … → Sset-below α ordα (x , xα) (y , yα)
                                          ≡ Sset-below β ordβ (x , xβ) (y , yβ)
```

Nothing in the type computes; the check is 10 s for the whole appended section
and 2.56 s for the file. The statement is also strictly stronger and strictly
more usable (any membership proof, since membership is an hProp). `old-agrees`
was then deleted outright: it is `order-agrees` at `α := sucV β`, and naming the
instance would only reintroduce `sucV β` into a type for no gain. A `-- perf:`
marker records the trigger at the site.

**Lesson candidate (proposed R-37, or an extension of P-c):**

> *A transported hypothesis in a statement is an index in disguise.* When a
> lemma's conclusion mentions a membership (or any hProp) proof built by
> transport along a concrete index (`Sset-mono … : ⟨ x ∈ˢ Sset (sucV β) ⟩`), the
> proof term enters conversion positions at every consumer and re-normalizes the
> index's `⋃`-tower. State the hypothesis as a variable of the same hProp type
> instead; the statement gets stronger, the transport moves to the call site
> where it is never compared, and the blow-up disappears. Measured, `L.Rud.Order`
> 2026-08-03: >600 s (killed) to 10 s, mathematics unchanged. Generalizes P-c
> from operation indices to statements, and is the mirror of R-36: R-36 exposes a
> sealed decomposition through a read lemma; this one keeps a transported proof
> *out* of the read lemma's type.

## 7. Missing reads (R-36 shape)

**None.** Everything the batch needed was on the delivered surface. Two near
misses worth recording for the orchestrator, both resolved without touching a
sealed module:

- `Sset-index-mono` (monotone in `⊆` of the index) is proved in
  `L.Rud.Hierarchy` but is **not** in `Step`'s `open ConcreteS using (…) public`
  re-export list. `memberStage-new` wants `Sset (sucV δ) ⊆ Sset β` from
  `δ ∈ β`. It was obtained instead from `ord-tri (sucV δ) β` plus `Sset-mono`
  (the `sucV δ ≡ β` branch is a `subst`, the `sucV δ ∈ β` branch is
  `Sset-mono`), so no re-export is needed. If a later batch wants the `⊆` form,
  adding `Sset-index-mono` to `Step`'s public list is a one-token change.
- `Sset-suc`, `Sset-zero`, `Sset-limit` are re-exported and were **not** used:
  the birth-stage analysis goes through the key's minimality
  (`stage-least`) rather than through the case equations and `ord-case` that the
  brief anticipated. `ord-case` is not imported at all.

## 8. Deliverables, item by item

1. **The producer view.** `Producer` (arm-indexed: `prod-self` / `prod-image`,
   membership arm deferring to the earlier stage), `Grounded` with
   `isPropGrounded`, `prod-value`. Realization: `prod-mem` (`step-in` realizes
   every grounded producer, via `step-in-img`, `u'-in`, `u-self-in`, `Sset-in`,
   `Sset-mem`). Totality: `trace-exists` (`step-out` gives every member a
   producer, run along `Sset-out` and `∈-induction`). Minimal selection:
   `leastTraceOf` / `leastTrace` with `leastTrace-value`, `-least`, `-irrel`,
   `-inj`. Birth stage: `stage-least`, `memberStage`, `memberStage-ord`,
   `memberStage-in`, `memberStage-first`, `memberStage-least`. The whole thing
   is stated over the sealed surface; `step` is never opened, and `Sset`/`Fof`
   are only ever applied.
2. **The order.** `_≺_` (stage, arm, index, arguments), `stage-mono`,
   `stage-below`, `_⊰_` on `Trace`, `traceSWO`, `Sset-below`, `Sset-order`. The
   successor lexicographic step is `memberStage-new` + `old-before-new` +
   `order-agrees` + the definition of `_≺_` (§2). Limits: `order-agrees` is the
   coherence lemma, exported in its own section as asked.
3. **Well-orderedness.** All four laws, via `traceSWO` and `pullSWO`. See §5.
4. **The AC endgame.** `Sset-order : (α : S) → IsOrd α → SWO (Member α)`;
   `Jset-order : (α : S) (lim : ⟨ isLimit α ⟩) → SWO (Σ[ x ∈ S ] ⟨ x ∈ˢ Jset α lim ⟩)`;
   `Sset-choice` (every set of a level has a choice function on its non-empty
   members, by least elements) and `Jset-choice`. Nothing internal is asserted,
   no satisfaction machinery is built or imported, and `⟨ isLimit α ⟩` is read
   only through `isLimit-ord`.
5. **Prose.** English and Chinese throughout, one passage per code block, opening
   and recap present, no em dash, all four linters green.

## 9. Terminology surfaced (owner decision needed)

Registered renderings **used**: `well-order` = 良序, `birth stage` = 诞生阶段
(the registered term fits `memberStage` exactly: the ordinal a set is carved
over, one below the least stage containing it), `rudimentary function` = 初步函数
(used once, in the opening).

**New load-bearing terms, chosen by meaning, not yet in `dev/glossary.toml`** (I
was scoped to `Order.lagda.md` and the report, so I did not add entries):

| en | zh chosen | note |
|---|---|---|
| producer | 生成者 | the chapter's central noun; 生成元 avoided (algebra: generator) |
| grounded (producer) | 扎根的 | deliberately **not** 良基的, which is well-founded and would drift |
| coherence (of the orders) | 相容 | 融贯 was drafted and rejected as philosophy register; 相容 is the set-theory usage |
| key (of a member) | 键 | |
| trace (the code name `Trace`) | not in prose | code-only; the prose says 扎根的生成者 |

## 10. Surprises

1. **The lexicographic tree order is not well founded without the step's bound.**
   The `γ ≥ γ·γ` argument (§2) killed the first design on paper, before any code.
   Cheap probe, large saving: it is what put `Grounded` in the type and shaped
   the entire descent.
2. **The recursion the brief asked for was avoidable, and avoiding it collapsed
   the batch's cost by roughly a factor of three** against the 1.2-2.4k
   calibration. The saving is concentrated exactly where the memo priced the
   risk: no recursion into `Type`, no propositional compute rule, no relation
   transport, no limit union, no coherence induction.
3. **The only wall was in a statement, not a proof** (§6), and it was invisible
   at the definition site: the same lemma with variable indices is free. That is
   the lesson candidate.
4. **`prodSWO`/`sumSWO`/`listSWO` went unused**, which is not a defect of the
   kit: the order is self-referential and no combinator on finished bundles can
   express it. `pullSWO` did the heavy lifting twice and is the piece that earns
   its keep.
5. **Numeric literal patterns work** for the sixteen-way operation index
   (`opAt 0 = op0` … `opAt 14 = op14`, catch-all `op15`), turning what would have
   been a 256-case injectivity proof into a 16-clause retraction plus one
   `cong`. Worth remembering for any future finite index type.

## 11. What is left for later batches

- The internal, uniformly `Σ1` face of the order sequence (SZ 1.10-1.11) is
  untouched by design, as the brief pinned. Nothing in this chapter needs to
  change to acquire it: the external order is the object the internal reading
  will have to name.
- `L.Rud.Order` is **not** in `Everything` (the orchestrator wires it); it is
  checked standalone and green.

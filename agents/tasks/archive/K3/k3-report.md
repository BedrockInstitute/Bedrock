# R5-K3: the object-language code predicate (`src/L/Rud/CodePred.lagda.md`)

The kernel's shared expensive object, built and closed in both directions. Reads done in the
mandated order (`_build/k2-report.md` in full, `L/Rud/CodeSet` as committed, `FOL/Coding` and
`V/Coding` in full, the retiring `L/Coding/{Shape,Closed,Slot,Recover,Base}` for pattern only,
`L/Rud/StepInL`'s `Desc` frame and `_build/r5d2-report.md`'s inner-world headline, and LESSONS
R-35/R-36/R-37/R-38, I-2/I-3/I-4, P-c/P-i, R-16, C-11/C-12, D-7 to D-10). Two files touched, both
mine: `src/L/Rud/CodePred.lagda.md` (new) and this report. `Everything` untouched, no commits, the
sibling `BaseBlock` neither read for code nor imported.

**Headline.** The chapter is green: **1,347 code lines, 1,782 file lines, 9.5 s cold**, all four
linters clean, `reuse lint` clean. Both adequacy directions are proved and `CodeSet`'s
`Description` entry point is discharged, so `codeSet∈J` is now a theorem at every arity. The
re-price of 730-1,120 was **low by about 20 %** and the cause is measurable and recorded. One
obstruction cost six wall events before it was located, and its cause was **not** the one the
retiring stack's shape would have predicted; the lesson is the sharpest thing this batch produced.

`allCodes∈J` is **not** discharged. It is not a gap in the method: it needs one extra object, an
object-language numeral predicate, priced at ≈135 lines in §5, and the stop-line (1,400) left 53.

---

## 1. D-10 first: the predicate's form and its recursion vehicle

**The carrier.** The predicate is `Φ k : Formula ⟪ Sset δ ⟫ 1` for `δ` **a limit level holding the
carrier `C`**, and it is read in the **inner** world of that level (`DefOf (Sset δ)`'s `⊨ᵐ`). The
carrier of the object language is therefore the level, not `C`; `C` enters only as one constant
(`mC`), and the numerals enter as constants (`nm k`). This is forced by the entry point:
`Description y` asks for a `Formula ⟪ Sset δ ⟫ 1` whose `defSet` is `y`, and `defSet` is read
inside.

**How the arity enters: fixed per instance, by a constant.** `Φ` is a **family** `ℕ → Formula`,
not one formula with an internal arity. The reason is exactly the one `CodeSet`'s prose records: a
code does not carry its arity, so "is a code" is not a property of a set at all; "is the code of an
arity-`k` formula" is. `Φ k` pins the arity by naming the numeral `# k` as a constant, and the
recursion below carries the arity as a **natural number** beside the code, raising it at a
quantifier. Nothing in the object language ever has to say "this set is a numeral", which is what
makes the arity-`k` predicate cheap and the all-arity one (§5) not.

**The exact form.**

```agda
Φ k = ∃̇D ∃̇key ( key ≐ pr (# k) x ∧̇ key ∈̇ D ∧̇ (∀̇∈ D. node) )
node = ⋁_{t<12} clause t
```

with `clause t` the frame at tag `t`, and the twelve clauses saying **shape and closure at once**:
each says "this member is `pr N (pr (# t) payload)` with the payload that tag calls for, **and** the
subkeys `pr N a` (or `pr (sucV N) a`) are members of `D`". The four term-carrying tags additionally
say the payload slots hold term codes, with a constant bounded by `C` and a variable index bounded
by `N`.

**The vehicle, and why.** Two were on the table: the tag-keyed clause implications (`Shape`/
`closedAt`) and a rank-descent table (`Descent`/`Recover`). The ruling is **both, in different
places, and neither as the retiring stack has them**:

- **In the object language: tag-keyed clauses, fused.** A first-order formula cannot recurse, so the
  recursion must be hidden behind an existential over a witness set. That forces the tag-keyed
  form. But the retiring stack splits it in two (`closedAt`, eight clauses, and `shapedAt`, twelve)
  because a second consumer wanted closedness alone. This chapter has no such consumer, so the two
  are **one twelve-clause disjunction**, which removes `Closed` (171) and `Slot` (187) from the
  price outright.
- **In the metatheory: rank descent.** The witness set gives no well-founded order by itself, so
  reading a formula out of it is a recursion on the rank of the code, three descent lemmas
  (`payload≺`, `leftPart`, `rightPart`) re-derived locally rather than imported from the retiring
  `L/Coding/Descent` (50 lines; a new rud module should not acquire a dependency on a retiring
  directory).
- **Inner-world discipline, applied.** Not one clause is Δ₀, no `Δ₀` proof appears anywhere, and no
  absoluteness lemma is used. The witness set is bound by an **unbounded** existential, which in the
  inner world is a quantifier over the level, and the level is exactly where the witness (the finite
  set of subformula keys) lives. This is r5d2's headline holding a second time, and it is what
  deletes the entire `Base`-class Δ₀ reader apparatus (187 lines) from the price: the pair reader is
  imported from `StepInL.Desc`, already inner-world and already adequate.

**The honest index, recorded before the code was written.** `Description` needs
`defSet (Sset δ) Φ ≡ codeSet k`, and `defSet (Sset δ) Φ ⊆ Sset δ`, so **`δ` must hold every code**.
K2's cofinality fact says no finite offset above `C`'s stage does; K2's containment half
(`code∈J`) says **every limit level holding `C` does**. So the index is:

> `δ` = any limit level holding `C` (least: the next limit above `C`'s stage);
> `γ` = any limit level with `δ ∈ γ`.

**Two limits, not one and not an offset.** The inner one holds the codes and carries the
quantifiers; the outer one holds the set. That pair is the honest index, and it is the module
telescope of `At` verbatim.

---

## 2. The construction's shape

Module telescope `L.Rud.CodePred {ℓ} (lem) (A)`, matching `Step`/`CodeSet`/`StepInL`.

1. **A sealed shape vocabulary** (`prS`, `numS`, `sucS`, `sglS`, `cupS`, with one equation each and
   `prS-inj`). Adopted on the `Descent` precedent (R-36/R-37/R-38): every statement below is an
   equation or membership whose two sides mention a pair inside a pair inside a pair, and the
   library's `pr` is an unsealed `sett`. See §6 for the honest status of this decision.
2. **Rank descent**, three lemmas at the sealed pair.
3. **`module Pred`**, the whole predicate at a **seven-fact telescope** (transitivity, the carrier is
   a member, closure under pair / numerals / singleton / binary union, the empty set, plus
   `codeIn`). No concrete stage appears anywhere in it. P-i [A], third instance.
4. Inside `Pred`: the tagged-pair readers (`tagPr`, `keyPairAt`, `keyUnAt`), the two frames
   (`binForm`, `unForm`) generic in their relation, the six relations, the twelve clauses with their
   meta-level `Shape`, the disjunction **as a fold over `ℕ`** (`orUpto`) rather than a right-nested
   chain of injections, the predicate `Φ`, the recursion `recover`, the closure `clo`/`subclo` with
   `Well-clo`, and `codeSet-desc`.
5. **`module At`**, the single instantiation, with the seven telescope facts discharged inside one
   `opaque unfolding` block, and `codeSet-Description` / `codeSet∈J`.

`lem` is spent nowhere in the mathematics (it only instantiates the imported modules). One new
opaque surface, the shape vocabulary. Imports from the retiring `L/Coding` tree: **none**.

---

## 3. Price table against the 730-1,120 re-price

| part | code lines | K2's line item | its estimate |
|---|---|---|---|
| header and imports | 43 | | |
| sealed shape vocabulary | 36 | (not foreseen) | |
| rank descent (3 lemmas) | 39 | part of "the decode inside the tower" | |
| telescope, notation, `prS` restatements | 70 | | |
| tagged-pair readers (`tagPr`, `keyPairAt`, `keyUnAt`) with adequacy | 80 | object-language readers | 150-250 |
| the two frames with adequacy | 50 | | |
| terms, subkeys, the next arity | 111 | | |
| the six relations with adequacy | 107 | `closedAt` + `shapedAt` + adequacy | 300-450 |
| the twelve clauses, `Shape`, `clauseOut`/`clauseIn` | 188 | | |
| the fold, `Well`, `Φ`, both directions of `Φ` | 96 | | |
| `recover` (six frames + dispatch) | 182 | the decode inside the tower | 200-300 |
| the closure, `headShape`, `cloWell` | 274 | (not foreseen) | |
| adequacy and `codeSet-desc` | 28 | the two adequacy halves | 80-120 |
| the instantiation and the discharge | 43 | | |
| **total** | **1,347** | | **730-1,120** |

**Where the estimate went wrong, by 227-617 lines.** Three items, in decreasing size:

1. **The closure was not priced at all (274 lines).** K2's re-price calibrated the "from a formula"
   direction against the retiring `CodeSet`'s own 200 lines, of which ~80 were already delivered.
   But the retiring stack gets its closure from `InL` (330 code lines), which K2 counted under "the
   decode inside the tower" together with `Recover`. Building the witness set, proving it a member
   of the level, and proving every one of its members well shaped is a **separate** twelve-clause
   induction from the decode, and it is this chapter's single largest part.
2. **Readers and frames came in cheap (130 vs 150-250), and the clause layer came in expensive
   (402 vs 300-450 for a smaller job).** The saving is real and is the inner world: `StepInL.Desc`'s
   pair kit is imported whole, so the `Base`-class Δ₀ apparatus costs zero. The overrun is that
   twelve clauses need, besides the formula, **a meta-level `Shape` per tag and a translation in
   each direction**, and that trio is 188 lines even after six frames are factored out.
3. **The sealed vocabulary (36) and the rank descent (39) were invisible to a file-level
   calibration** because in the retiring tree they are `Descent`'s 50 lines plus a seal that lives
   in `L/Rank`.

**Against the whole route.** K2 re-priced the internal-codes route at ≈2,000-2,600 with this object
as its shared expensive half. With `CodeSet` at 193 and this chapter at 1,347, the two pillars'
shared part is delivered at **1,540**, and what remains of the route is the coded-satisfaction table
that consumes it. The route's total is on track for K2's figure; the *distribution* was wrong, not
the sum.

---

## 4. The `Description` discharge, recorded

```agda
module At (γ : S) (limγ : ⟨ isLimit γ ⟩)
          (δ : S) (limδ : ⟨ isLimit δ ⟩) (δ∈γ : ⟨ δ ∈ˢ γ ⟩)
          (C : S) (C∈δ : ⟨ C ∈ˢ Sset δ ⟩) where

  codeSet-Description : (k : ℕ) → CG.Description (Codes.codeSet C k)
  codeSet∈J           : (k : ℕ) → ⟨ Codes.codeSet C k ∈ˢ Sset γ ⟩
```

The discharge is by the **equation**, not by the two-containment entry point: `codeSet-desc`
produces `defSet (Sset δ) (Φ k) ≡ codeSet k` outright, through `StepInL.Desc.described`, so
`description-write` was not needed. (`description-write` remains the right shape for a consumer who
only has containments; this one has more.)

**The honest index, as delivered.** `δ` any limit holding `C`; `γ` any limit with `δ ∈ γ`. The
telescope makes the room condition visible: the chapter cannot be instantiated at `γ` alone, and it
cannot be instantiated at a finite offset, which is K2's refutation showing up as a module telescope
rather than as a failed proof.

**What the discharge consumes from `CodeSet`**: `Codes.code`/`codeTm`/`codeSet`, `codeSet-out`,
`code∈codeSet`, `InLevel.pr∈J`/`∅∈J`/`numeral∈J`, `Carrier.code∈J`/`codeSet⊆J`, and
`Carrier.Description`/`codeSet∈J`. Nothing else, and nothing was changed there.

---

## 5. `allCodes∈J`: not discharged, priced

`allCodes` is not `codeSet k` for any `k`; its membership is "the code of a formula at **some**
arity". Written as `∃̇N`, the predicate admits junk, because nothing in the twelve clauses
constrains the arity component `N` (this is exactly what `Recover`'s prose records about
`shapedAt`, and it is why the arity is pinned **from outside** by a constant here). Discharging
`allCodes` therefore needs one more object: an object-language predicate "`N` is a numeral".

It is not hard and it is the same trick a third time: `∃̇E. N ∈̇ E ∧̇ ∀̇∈E. (var ≐ ∅ ∨̇ ∃̇p ∈̇ E. var ≐
sucV p)`, with recovery by rank descent on `N`. Priced against this chapter's measured rates:

| item | estimate |
|---|---|
| `isNum` formula, `NumShape`, out/in | 40 |
| the rank recursion recovering `N ≡ # j` | 35 |
| `Φ∀` with the arity bound, and both directions | 40 |
| `allCodes-desc` and the discharge | 20 |
| **total** | **≈135** |

The stop-line (1,400) left 53. It is one short follow-on batch, or a tail on whichever batch builds
the coded satisfaction table, and it is the **only** thing between here and `allCodes∈J`.

---

## 6. Process: one obstruction, six walls, and what it actually was

**Timings** (all `GHCRTS="-A64m -I0 -M12g"`, one check at a time, never parallel; "wall" = killed at
the 180 s line per C-12):

| # | content | result |
|---|---|---|
| 1-2 | header, imports, rank descent, readers | 1.7 s, one `UnequalTerms` (a `refl` where a reader's introduction was needed), then green |
| 3 | `4 + n` arities | `NotInScope: +` (Base.Prelude re-exports only `ℕ; zero; suc`), 1.4 s |
| 4 | + terms/subkeys/successor + frames | **wall** |
| 5 | bisect: part 1 alone | 2.3 s, `UnsolvedMetas` at `eqFrame _` |
| 6 | the successor body named (`sucBody`) | 2.0 s green |
| 7 | + frames | **wall** |
| 8-14 | seven probes (definitions only 2.1 s; destructuring only 2.1 s; reader applied with a free result type 2.2 s; concrete arity **wall**; witness type without the equation 2.2 s; depth-2 equation **wall**; trivial equation 2.1 s) | the equation in the target isolated |
| 15 | full rewrite behind the sealed shape vocabulary | **wall** |
| 16-18 | bisect v2 (vocabulary + descent 1.5 s; + telescope 1.6 s; + readers 1.8 s; + frames **wall**) | |
| 19 | probe H: the same reader applied against a **written** type, no elimination around it | 1.8 s |
| 20 | the frame's branch given a written type (`mk`) | **1.8 s green** |
| 21 | + `binForm`, terms, subkeys, successor | 2.4 s |
| 22 | + the six relations | 2.8 s |
| 23 | + twelve clauses, `Shape`, `clauseOut`/`clauseIn` | 3.7 s |
| 24 | + the fold, `Well`, `Φ` | 4.9 s |
| 25 | + `recover` | parse error, `UnequalTerms` (a `subst` direction), then 6.2 s |
| 26 | + the closure and `headShape` | 6.5 s |
| 27 | + `cloWell` and `codeSet-desc` | 8.6 s |
| 28 | + the instantiation and the discharge | 9.7 s |
| 29 | imports pruned; no-change re-run | 9.5 s / 1.4 s |

Six wall events, **one root cause**, and it is not the one the retiring stack's shape suggests. The
three-failure stop was never reached on type errors (seven in total across the batch, each fixed in
one edit); the stop that mattered is C-12's 180 s line, and it fired six times on the same thing.

**The cause, isolated by probe.** An elimination whose branch is an extended lambda has that
branch's type **inferred against the whole target**. When the target contains an equation between
iterated Kuratowski pairs, that inference does not finish. The isolating pair of probes is exact:

- `keyUnAt-out … hk` applied against a **written** type: 1.8 s.
- the same application inside `PT.map (λ { (a , (hk , hr)) → … })` with the branch's type inferred:
  does not finish in 180 s.

Nothing else changed between them. This is `Shape`'s own recorded lesson ("a branch whose type is
written is solved against that type, and a branch whose type is inferred is solved against the whole
disjunction"; ten minutes versus two seconds) firing on a **different** target class: not a
disjunction of readings but an equation between pairs. Every elimination in the chapter now carries a
named branch with a written type, and the whole file checks in 9.5 s.

**Honest status of the sealed vocabulary.** `prS`/`numS`/`sucS`/`sglS`/`cupS` were introduced as the
suspected fix and **were not the fix**: the wall survived them (run 15). They were kept because the
`Descent` precedent for sealing an iterated pair is explicit and because the derived names
(`keyOf`, `binKey`, `unKey`) are what make 1,300 lines of statement readable. Whether they are
*load-bearing* for the timings is **not measured**: after run 20 the file was never re-checked with
`pr` in statement positions. Recording this rather than claiming a win.

**Linters.** `lint-agda --check`, `lint-prose --check`, `weave-i18n --check`, `check-glossary`, and
`reuse lint`: all clean, whole repo. `Everything` untouched, so `make check` does not yet reach this
file; adding it is the owner's call.

---

## 7. Lesson candidates (IDs to be assigned by the owner)

1. **R-series, sharpened: write the branch type, and the rule is not about disjunctions.** The
   recorded form of this lesson (from `L/Coding/Shape`) attributes the blow-up to a branch solved
   "against the whole disjunction". Measured here, the trigger is narrower and more general at once:
   **any** elimination branch whose type is inferred and whose target contains an equation between
   iterated Kuratowski pairs. Six wall events, one two-second fix, and the discriminating probe pair
   is in §6. Practical rule for this development: **in the inner world, every `PT.rec`/`PT.map`
   branch gets a named `where` function with a written type.** No exceptions; the insurance is free.
2. **A wall that survives the obvious seal is a mis-diagnosis, and the seal should be reported as
   unmeasured.** Sealing `pr` was the textbook move (`Descent` records 163 s → 1.4 s for exactly
   this shape) and it was wrong here. The cost of the wrong diagnosis was one full rewrite and three
   wall events. The rule: after a seal fails to move a wall, **stop sealing and start bisecting the
   elaboration**, and when the real cause is found do not retro-fit credit to the seal.
3. **D-10 sub-rule, second instance: a re-price that omits a construction is wrong by that
   construction.** K2's re-price (itself a correction of a 3-4x mis-price) counted the retiring
   `Recover` + `InL` as one line item, "the decode inside the tower". They are two: the decode
   (182 here) and the **witness-set construction** the decode's hypothesis has to be discharged
   from (274 here). Every "both directions of adequacy" estimate should be split into the
   elimination and the introduction and priced separately, because in this development the
   introduction has been the larger half twice.
4. **The inner world's second dividend: an imported pair kit.** r5d2's headline was "Δ₀ is a
   crossing tax". The consequence realised here is stronger than "don't pay it": because
   `StepInL.Desc` already wrote the pair reader inner-world and generic in the carrier, this chapter
   imported it whole and spent **zero** lines on the `Base`-class apparatus that the retiring stack
   spends 187 on. Inner-world readers are reusable across chapters in a way Δ₀ readers were not
   (they carried an absoluteness obligation each). Worth recording as a reason to keep writing
   readers at an abstract transitive carrier.
5. **A twelve-way disjunction should be a fold over `ℕ`, not a right-nested chain of injections.**
   The retiring `Shape` writes `∣ inr ∣ inr … ∣₁ ∣₁` eleven deep, twice, and warns about the cost.
   Here the disjunction is `orUpto : ℕ → Formula` with `orUpto-in`/`orUpto-out` by induction on the
   bound (20 lines total), the clause table is `clause : ℕ → Formula` with a `⊥̇` default, and the
   dispatch is twelve one-line clauses. No truncation nests deeper than one. Cost of the twelve-way
   layer: 188 lines including both meta-level translations, against `Shape`'s 354 for the
   disjunction alone.
6. **P-i [A], third datum.** The whole predicate is stated at a seven-fact telescope and the tower
   enters in one `opaque unfolding` block of 20 lines at the very end. 1,347 lines, 9.5 s cold, no
   heap event, and the level's identity never reached conversion.
7. **R-16 datum: environments spelled out, and the rent was low.** Every reader takes its de Bruijn
   positions and its environment explicitly, and every frame is stated at a fixed concrete arity
   (4 / 6 / 7) rather than generically. Generic arities were tried first and are **not** what cost
   the walls (probe 11 vs probe 13: the concrete-arity frame walls identically), so the fixed
   arities were kept only because they read better. The rent R-16 warns about is real but it is
   paid in lines, not in seconds: roughly 60 lines of the 1,347 are environment bookkeeping.

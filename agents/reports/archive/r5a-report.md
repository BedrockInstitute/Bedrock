# R5a report: the graph calculus, and what the rud image principle actually costs

**Date:** 2026-08-03. **Files written:** `src/L/Rud/Graphs.lagda.md` (new, 731
Agda code lines / 1,048 file lines) and this report. Nothing else: no
`Everything`, no `Switch`, `Ops`, `Images`, `Step`, `Realize`, `Describe`,
`Hierarchy`, `Order`, `OrdArith`, and `LevelDesc` was never opened. No
commits, no `postulate`, no hole, no `TERMINATING`, `--safe` on. Every agda
run used `GHCRTS=-M12g`, one check at a time (C-12). No wall event, no heap
event.

**Headline.** The two obstacles the R3c scoping named are both dissolved, and
they were the cheap ones. The identity graph is built (174 lines with its
ambient set, triple space and two padded membership tests, and it is not
circular: the classical extensionality route needs only `F7`, `F3`, `F4`, the
range, and one double-negation spend), and the join of two graphs is 34 lines
of `F3`/`F4` plus intersection. **Jimg is not discharged.** It is
*reduced*, in its exact type, to a single named principle about element
relations (`elemRel→Jimg`), and six of that principle's ten clauses are
proved. The four that remain need one further tool and one restatement, both
identified precisely in section 5; neither was visible in the R3c scoping,
and together they are the real content of the residue.

---

## 1. The statement, and why it is the element relation and not the graph

The classical route strengthens the induction to the graph
`H(p) = {⟨y, F(y)⟩ : y ∈ p}` and extracts the image as `⋃ F8(H, p)`. The
delivered chapter uses the **element relation** instead:

```
EL(f, vs, p) = { ⟨y, w⟩ : y ∈ p , w ∈ evalC f (y ∷ vs) }
```

with the extraction one step shorter, since `F8` already takes slices:

```agda
img-of-rel : (R p : V ℓ) (val : V ℓ → V ℓ)
           → (fwd : ...) → (bwd : ...)
           → sett ⟪ p ⟫ (λ m → val (⟪ p ⟫↪ m)) ≡ F8 R p
```

`imgOpC f vs p` is *definitionally* `sett ⟪ p ⟫ (λ m → evalC f (⟪ p ⟫↪ m ∷ vs))`
(the R3c design record's third design), so this equation is exactly the
image, and no union is needed. The element relation is also the better
induction carrier: intersection and difference become intersection and
difference of relations, and the base case for the separated variable becomes
the membership relation `F7` rather than the identity graph. The graph form
is still needed, but only inside four clauses (section 5).

The reduction is exported at the hypothesis's own type. In
`module Kit J Jrud` (which opens `Switch.Closure J Jrud`):

```agda
IsElemRel f vs p R = (y w : V ℓ) → ⟨ y ∈ˢ p ⟩
  → (⟨ pr y w ∈ˢ R ⟩ → ⟨ w ∈ˢ evalC f (y ∷ vs) ⟩)
  × (⟨ w ∈ˢ evalC f (y ∷ vs) ⟩ → ⟨ pr y w ∈ˢ R ⟩)

ElemRel f vs p = Σ[ R ∈ V ℓ ] (InJ R × IsElemRel f vs p R)

ElemRelPrinciple = {k : ℕ} (f : Comp (suc k)) (vs : Vec (V ℓ) k) (p : V ℓ)
                 → ConIn InJ f → AllIn InJ vs → InJ p → ElemRel f vs p

elemRel→Jimg : ElemRelPrinciple
             → {k : ℕ} (f : Comp (suc k)) (vs : Vec (V ℓ) k) (p : V ℓ)
             → ConIn InJ f → AllIn InJ vs → InJ p → InJ (imgOpC f vs p)
```

The conclusion of `elemRel→Jimg` is `Switch.Closure.Eval-J`'s `Jimg`
parameter **verbatim** (same implicit `k`, same three hypotheses, same
conclusion `InJ (imgOpC f vs p)`), so discharging `ElemRelPrinciple` closes
the residue with no reshape of Switch at all. That is the sense in which this
batch reshapes nothing silently: Switch's hypothesis is untouched, and the
new interface is strictly upstream of it.

## 2. What is built, per construction

Every operation is a chain of the sixteen basis functions, sealed `opaque` at
its birth site with its specification inside the same block (R-38 applied
before the fact), and every one has a closure lemma in `module Kit` in its own
`opaque unfolding` block.

| construction | definition | reads | in J by |
|---|---|---|---|
| `cup a b` | `F5 (F0 a b) (F0 a b)` | `cup-in`, `cup-out` | `J-cup` |
| `cap a b` | `F1 a (F1 a b)` | `cap-in`, `cap-outl`, `cap-outr` | `J-cap` |
| `ranOp R` | `F5 (F8 R (F6 R R)) _` | `ran-in`, `ran-out` | `J-ran` |
| `amb p` | `cup p (F5 p p)` | `amb-self`, `amb-mem` | `J-amb` |
| `mrel q` | `F7 q q` | `mrel-in`, `mrel-out` | `J-mrel` |
| `tsp p` | `F2 (amb p) (F2 p p)` | `tsp-in` | `J-tsp` |
| `lft p` | `cap (F4 p (mrel (amb p))) (tsp p)` | `lft-in`, `lft-out` | `J-lft` |
| `rgt p` | `cap (F3 p (mrel (amb p))) (tsp p)` | `rgt-in`, `rgt-out` | `J-rgt` |
| `neq p` | `ranOp (cup (F1 lft rgt) (F1 rgt lft))` | `neq-inl/inr/out` | `J-neq` |
| **`idG p`** | `F1 (F2 p p) (neq p)` | `idG-in`, `idG-out` | `J-idG` |
| **`joinOp R S Wr Ws`** | `cap (F4 Ws R) (F3 Wr S)` | `join-in`, `join-outl/outr` | `J-join` |
| **`swp R q`** | `ranOp (cap (F4 q R) (F3 q (idG q)))` | `swp-in`, `swp-out` | `J-swp` |
| `fld R` | `amb (cup (F6 R R) (ranOp R))` | `fld-dom/ran/mem` | `J-fld` |
| **`flat R`** | `ranOp (cap (F4 (fld R) (swp R (fld R))) (F3 (fld R) (swp (mrel (fld R)) (fld R))))` | `flat-in`, `flat-out` | `J-flat` |

Plus `J-F3`, `J-F4`, `J-F8` (the three basis wrappers the switch chapter did
not carry), `slice-eq` and `img-of-rel` (the extraction), and `constRel`,
`selfRel` (the two base-case element relations).

Sizes, in Agda code lines: the header and imports 28, the small kit and the
range 67, the identity graph with its ambient set and triple space 174, the
join 34, the extraction 20, the converse 56, the field and the flattening 112,
the closure kit 116, the reduction and the six clauses 124. Total 731.

**The identity graph, in words.** `⟨a,b⟩` is kept out of `idG p` exactly when
a *witness* separates `a` from `b`: a member `c` of the ambient set
`amb p = p ∪ ⋃p` lying in one and not the other. The two padded membership
relations `lft` (`c ∈ a`) and `rgt` (`c ∈ b`) live in the same triple space
`amb p × p × p`, their symmetric difference is the witness set, its range is
the set of separated pairs, and the diagonal is `p × p` minus that. Forward it
is extensionality plus one `dne` per direction (the classical spend: "no
witness" gives `¬¬(c ∈ b)` constructively, not `c ∈ b`); backward a witness for
`⟨a,a⟩` would contradict itself. This is Devlin's `t_{x_i = x_j}` case
(VI.1.11(g)) written out at arity two.

**The converse, in words.** Slices are taken at the first coordinate and the
range strips the first coordinate, so a relation can only be read the way it
was written; turning it around is the one move padding cannot make. The
triple `⟨u,v,u⟩` whose first and last coordinates agree is
`cap (F4 q R) (F3 q (idG q))`, and its range is `{⟨v,u⟩ : ⟨u,v⟩ ∈ R}`. This
is the shortest use the identity graph has: two constraints, one range, three
coordinates.

## 3. The per-clause table of the element-relation principle

`Comp` has ten constructors. Six clauses are **proved** in `module Cases`
(each an independent lemma taking the sub-relations as arguments, so the
induction assembles with no further mathematics once the missing four are in);
four are **open**, each with its exact obstruction.

| clause | element relation | status |
|---|---|---|
| `conC x` | `F2 p x` (the product) | **done**, `elem-conC` |
| `varC zero` | `swp (mrel (amb p)) (amb p)`, the converse membership relation | **done**, `elem-varZ` |
| `varC (suc i)` | `F2 p (lookup i vs)` | **done**, `elem-varS` |
| `interC a b` | `cap Ra Rb` | **done**, `elem-interC` |
| `diffC a b` | `F1 Ra Rb` | **done**, `elem-diffC` |
| `unionC a` | `flat Ra` | **done**, `elem-unionC` |
| `pairC a b` | `cup Γa Γb`, the union of the two **graphs** | open: needs `sgraph` |
| `colC a b` | `cap Rb (co-flatten of Γa)` | open: needs `sgraph` and one more flatten |
| `chSepC a b c` | `cap Rc (F2 P W)`, `P = F6 (cap (joinOp Γa Γb _ _) (F2 p (mrel q)))` | open: needs `sgraph` |
| `eqSepC a b c` | the same with `idG q` in place of `mrel q` | open: needs `sgraph` |
| `imgC g a` | reindexing of the inner relation along `ER a` | open: needs the arity restatement |

Two remarks on that table. First, the two separation clauses are *already*
designed down to their chains, and the pieces exist: the join is built, the
membership test is `p × mrel q` (a product cut, three lines), the equality
test is `p × idG q`, and the domain projection is `F6`. Second, `colC` needs a
mirror of `flat` (membership in the other direction), which is the same
90-line shape with `mrel` where `flat` has `swp (mrel _) _`.

## 4. Jimg: reshaped how, exactly

Not discharged; **reduced verbatim**. The delivered implication is
`elemRel→Jimg` above, and the reduction itself is unconditional: it needs only
`img-of-rel` (the `F8` extraction) and `J-F8`. That the two types agree on the
nose is checked by the typechecker, not by reading: the chapter ends with

```agda
  module Discharge (principle : ElemRelPrinciple) where
    open Eval-J (elemRel→Jimg principle) public
```

which instantiates the switch chapter's own conditional module, so
`evalC-in-J` and `switch-⊇` are exported here conditioned on nothing but
`ElemRelPrinciple`. No hypothesis of Switch was
changed, no type was weakened, and nothing in the tower was assumed beyond
`Jrud` (the sixteen-function closure) that `Switch.Closure` already takes.
D-8's precedent was therefore *not* invoked: the tower supplies nothing extra
here, and nothing extra is needed. The whole residue now sits in one named
`Type`, `ElemRelPrinciple`, whose ten clauses are the table above.

For the record, three routes to the residue were weighed before building:

1. **Through the realization theorem** (definability, the way Devlin proves
   the Basis Lemma): rejected as circular. `Realize`'s walk emits `imgC` at
   the bounded-existential clause (`bexComp a e = unionC (imgC (bexFam a e)
   (conC u))`), so `evalC-in-J` on a realized composite needs `Jimg` again.
   A follow-up that wanted this route would have to re-derive an *image-free*
   realization first, which is a second copy of the `Realize` walk.
2. **Through the tower** (bound the levels of the image's members and use the
   ⊆ direction): rejected. `Switch.Closure` has only `Jrud`; and the
   subset-to-member step is residue R2 (`ImgArm`), which is not built.
3. **The graph calculus** (this batch): six clauses done, tools reusable.

## 5. The two obstacles the scoping did not name

This is the part that most changes the plan.

**N1. The slice-graph conversion, `sgraph`.** Four of the five open clauses
need the *graph* `{⟨d, EL"{d}⟩ : d ∈ p}` of a family whose element relation
is already in hand. Going the other way (graph to element relation) is
`flat`, which is built; this direction is not a flatten and not a padding. Its
chain is known: the graph is a subset of `p × F8(EL,p)` cut by two bounded
universals ("every member of `v` is `EL`-related to `d`" and "every
`EL`-relative of `d` is a member of `v`"), each of which is the complement of
a range of a triple set, exactly like the identity graph's witness set. It is
the identity graph's proof shape run twice at one coordinate more, and it
carries one `dne` spend per universal. **Estimate: 250 to 350 lines**, and it
unlocks `pairC`, `colC`, `chSepC`, `eqSepC` (another 150 to 200 lines with the
pieces already delivered).

**N2. The arity restatement, forced by `imgC`.** `ElemRelPrinciple` as stated
(one argument `p`, a *fixed* witness stack `vs`) is **not provable by
induction on `f`**. The `imgC g a` clause needs the induction hypothesis for
`g : Comp (suc (suc k))` at a stack whose head is the *varying* argument `y`,
so the hypothesis has to be uniform in `y`. The honest strengthening indexes
by an arbitrary set `D` of argument records together with a vector of
functional graphs over `D`:

```
EL(f, D, Γ⃗) = { ⟨d, w⟩ : d ∈ D , w ∈ evalC f (the values of Γ⃗ at d) }
```

with `ElemRelPrinciple` the instance `D = p × {⟨vs⟩}`, `Γ₀` the projection
graph and `Γ_{i+1}` the constant graphs. The `imgC` clause then runs at
`D' = EL(a, D, Γ⃗)` with the shifted vector (the right-projection graph in slot
zero, the old graphs composed with the left projection), and its result is
reindexed back along the left projection. This is the same phenomenon
Devlin's proof meets when it works with `f*(u) = f"u^n` over the whole
`n`-fold product rather than one argument; our `Γ⃗` formulation avoids
encoding and decoding `n`-tuples, which is the expensive way to do it.
**Estimate: 150 lines of restatement (the six done clauses port almost
verbatim, since each is per-`d` pointwise), plus 150 to 250 for the `imgC`
clause and the two projection graphs.**

So the residue's remaining cost is roughly **550 to 850 lines in two batches**
(N1 with its four clauses; N2 with `imgC` and the assembly), on top of the 731
delivered. The R3c estimate treated the whole thing as one batch, which the
two named obstacles (identity graph, join: 135 lines together, both green
first try) would have justified; the cost is in the two obstacles nobody had
looked for.

**Literature note, load-bearing.** The r3c report cites the principle as
"SZ Lemma 1.3(b)". That is not what SZ 1.3(b) says: SZ 1.3(b) is the
conditional-value lemma (`g(x̄) = f(x̄)` if `R(x̄)`, else `∅`). In SZ's
presentation the image is not a lemma at all, it is a **generating schema** of
the rud functions (Definition 1.1, the clause `f(x̄) = ⋃_{y ∈ x₁} g(⟨y, x₂,
...⟩)`); what needs proof is that the sixteen-function list generates the same
class, which SZ states without proof ("A little bit more work is necessary",
p. 10, citing Devlin). The actual theorem is **Devlin VI.1.11, the Basis
Lemma**, and its classical proof is the `t_φ` satisfaction sets over tuple
spaces, i.e. our `Realize` in the other direction. Bedrock's route (the graph
calculus) is a genuine alternative to Devlin's, chosen because `Realize` is
not reusable here (route 1 above); the report's plan should be read against
Devlin VI.1.11, not against SZ 1.3.

## 6. Timings

Every check is the module alone with dependencies warm, `GHCRTS=-M12g`, one at
a time.

| stage | wall clock |
|---|---:|
| kit (`cup`, `cap`, `ranOp`) | 1.4 s |
| + ambient set, triple space, **identity graph** | 1.7 s |
| + join, `slice-eq`, `img-of-rel` | 1.7 s |
| + **converse** | 1.9 s |
| + closure kit (`module Kit`), the Jimg reduction | 2.1 s |
| + five closing clauses | 2.4 s |
| + `fld`, **flat**, the union clause | 2.8 s |
| **final, cold (`.agdai` deleted)** | **2.8 s** |
| gates: `lint-prose`, `lint-agda`, `check-glossary`, `weave-i18n --check` | all exit 0 |

Six error cycles in the whole batch, all trivial and all caught in under two
seconds: one universe-level mismatch (`dne` is at `ℓ`, so `cap-outr` bridges
through `∈ₛ`), one missing import (`sett`), one non-export (`Comp` is
`Switch.Bs.Comp`, since `open Bs using (...)` does not re-export), two path
directions in a `pr-inj` chain, and one declaration-order slip (the `flat`
block had to move above `module Kit`). Nothing else. No wall, no bisect, no
`pkill`.

## 7. Surprises and lesson candidates

1. **(craft, and a correction to a recorded finding) "Circular" was a scoping
   artefact, not a fact.** R3c recorded that the identity graph's obvious
   routes (`p × p` cut by an equality test; the singleton image
   `S(S(p))`) are "each circular in the image operation being built". Both of
   those routes are indeed circular, and the conclusion drawn from them was
   wrong: the classical construction is neither, it is extensionality
   relativized to `p ∪ ⋃p`, and it costs 95 lines with one `dne` per
   direction. Candidate rule: when two routes to a base case are circular,
   the finding to record is "two routes are circular", never "the base case
   is circular"; the third route is often the textbook's.
2. **(design, new) Choose the induction carrier by which operations are
   homomorphic.** Carrying the graph `{⟨y, F(y)⟩}` makes intersection and
   difference *pointwise* operations, which the basis cannot do; carrying the
   element relation `{⟨y, w⟩ : w ∈ F(y)}` makes them the *same* operations one
   level up (`cap`, `F1`), and makes the extraction one `F8` with no union.
   Six of ten clauses are free in the second carrier and one in the first.
   The general shape: pick the representation in which the syntax's operations
   act by the same operations.
3. **(measured, R-38 confirmed prophylactically) Sealing at birth kept a
   731-line tower-heavy file at 2.8 s.** Every construction here is a
   `sett`-tower over another `sett`-tower (`ranOp` alone is `F5 ∘ F8 ∘ F6`,
   and `flat` nests four of them), which is precisely the class that walled
   R3c's `eval-agree` at over 400 s. Applying R-38 from the first line
   (each operation sealed with its specification inside the same block, every
   consumer reading only through the specification) meant no wall ever
   appeared: the *maximum* check in the batch was 2.8 s. This is the first
   datum where the seal discipline was applied before a wall rather than
   after one, and it is evidence that the discipline is cheap insurance, not
   a repair.
4. **(craft) The tuple calculus has exactly three moves, and naming them
   dissolved the design work.** `F3` inserts a coordinate after the first,
   `F4` appends one at the end of a pair (and, with a product as its first
   argument, appends a whole block), and `ranOp` strips the leading
   coordinate. Every construction here is "choose a coordinate order in which
   the quantified variables lead, pad each constraint into the common tuple
   space, intersect, strip". Once stated that way, `swp` fell from a
   four-coordinate design to a three-coordinate one (`⟨u,v,u⟩`), which is
   half the code.
5. **(inference trap, minor, extends I-2/I-4) `dne` is at level `ℓ`, so
   structure-level memberships must be bridged.** `Switch.dne` takes an
   `hProp ℓ`, and `∈ˢ` lands in `hProp (ℓ-suc ℓ)`; every classical step in
   this chapter therefore goes `∈s` then `dne` then `∈S`. It is a one-line
   idiom, but it is invisible until the error appears, and it is the reason
   `cap-outr` (not `cap-outl`) is the classical half.

## 8. Protocol compliance

- Files created: `src/L/Rud/Graphs.lagda.md`, `_build/r5a-report.md`. Nothing
  else touched; `git status` shows `?? src/L/Rud/Graphs.lagda.md` and
  `?? src/L/Rud/LevelDesc.lagda.md` (the sibling batch's file, never opened,
  never read by this batch), and nothing modified.
- Only the module was typechecked, never `Everything`, never `make check` in
  full; the four Python gates were run directly on the new file (C-8's blind
  spot for untracked files) and all exit 0.
- `GHCRTS=-M12g` on every run, one at a time; no heap event, no run above
  2.9 s, so the P-i playbook was never needed.
- Stop-line: 731 code lines against 1,400; the composition case never
  approached the 500-line pause threshold, because six of its clauses are
  three lines each and the rest are not built.
- Prose: en + zh, no em dash, CJK full-width punctuation, half-width parens,
  zh paragraphs on single lines; `初步函数` is the only rendering used for
  rudimentary function.

---

# R5a part 2: the residue is closed

**Date:** 2026-08-03 (same day, second dispatch). **Files written:**
`src/L/Rud/Graphs.lagda.md` (extended from 731 to **1,982** Agda code lines)
and this appendix. Nothing else: `LevelDesc.lagda.md` was read for its export
list only and never opened for edit; no `Everything`, no other trunk file, no
commit, no `postulate`, no hole, no `TERMINATING`, `--safe` on.

**Headline. The image principle is proved, and the discharge is
unconditional.** `Cases.Jimg` has exactly the type Switch's `Eval-J` takes as
its hypothesis and is proved outright from `Jrud` alone, so

```agda
  module Discharge where
    open Eval-J Jimg public
```

takes no parameters: **`evalC-in-J` and `switch-⊇` are now theorems of any set
closed under the sixteen basis functions**, with no hypothesis left anywhere in
the chain. The switch theorem's closure direction is unconditional, and the
last named mathematical debt of the rud trunk is discharged.

## 1. The completed ten-clause table

Every clause is a standalone lemma in `module Cases`, and `elemRel` is the
ten-line structural recursion that assembles them.

| clause | element relation | how |
|---|---|---|
| `conC x` | `F2 D x` | product |
| `varC i` | `flat Γᵢ` | flattening of the slot's graph |
| `interC a b` | `cap Ra Rb` | intersection of relations |
| `diffC a b` | `F1 Ra Rb` | difference of relations |
| `unionC a` | `flat Ra` | flattening |
| `pairC a b` | `cup Γa Γb` | union of the two **slice graphs** |
| `colC a b` | `cap Rb (comp (swp Γa Q) (mrel Q) D Wt)` | composition with the membership relation |
| `chSepC a b c` | `cap Rc (F2 P Wc)`, `P = testSet Γa Γb (mrel Q) …` | join, membership test, domain |
| `eqSepC a b c` | the same with `idG Q` | join, **identity-graph** test, domain |
| `imgC g a` | `comp (lproj D' X) Γ' D Ww` | reindexing along the left projection |

New machinery, all sealed at birth with its specification inside and all with
a closure lemma in `module Kit`: `comp` (relational composition, `ranOp` of a
join) with the general `join-out`; `vals` (the values of a relation) with three
readings; `sgQ`, `sgT`, `sgL`, `sgR`, `sgBad`, **`sgraph`** (the slice graph);
`lpg`, `rpg`, `lproj`, `rproj` (the projection graphs); `prL`, `prR` (sealed
aliases of the Images projections); `testSet` with `test-in`/`test-out`;
`graphOf` (the element-relation-to-graph conversion, where the slice graph is
spent); `liftGraphs`/`liftArgs` (the shifted argument vector).

## 2. The restatement, as it landed

`ElemRel f gs D` indexes by a record set `D` and a vector `gs` of argument
families, each entering through a graph `Γᵢ` (the predicate `Args gs Γs D`
carries `InJ Γᵢ` and `IsGraph gᵢ Γᵢ D` per slot). Three predictions from part
1, all confirmed:

- **The six pointwise clauses ported unchanged**, exactly as predicted: each
  is the part-1 proof with `appAt gs d` where `y ∷ vs` stood. The only real
  change is that `varC` collapsed from two clauses (`zero`, `suc i`) into one,
  because a slot's element relation is now the flattening of its graph
  whatever the slot is; the converse membership relation that part 1 used for
  `varC zero` is now only the top-level instance's `idG p`, one line.
- **The nested image is the clause that forces the restatement.** Its inner
  composite runs at `D' = cap Ra (F2 D Wt)`, the honest pairs `⟨d, t⟩` with
  `t ∈ a(d)`, with `prR` in slot zero and every old family composed with
  `prL`; the outer relation is `comp (lproj D' X) Γ'`, the composition of the
  left projection with the inner graph.
- **The top-level instance needs no tuple encoding.** `Jimg` runs the
  induction at `D = p` with `gs = (λ y → y) ∷ constFams vs` and
  `Γs = idG p ∷ constGraphs p vs`: the identity graph is the separated
  variable's graph and each constant's graph is a product. This is the fourth
  distinct use of the identity graph, and the reason it is worth its 174 lines.

**One design device worth recording:** the `imgC` clause needs its record set
to consist of honest pairs (`prL`/`prR` must behave), which the element
relation's specification does not say. Rather than adding a shape clause to
the specification and paying for it in all ten clauses, the clause *normalizes*
its record set once: `D' = cap Ra (F2 D Wt)` is `Ra` cut to `D × Wt`, which
contains every honest pair (`vals-union` supplies `t ∈ Wt`) and consists only
of pairs over `D` (`F2-read`). The specification stays four lines, and the
cut is 3.

## 3. Stop-line: exceeded, and the accounting

**The file is 1,982 code lines against the 1,700 combined stop-line, an
overrun of 282 (17%).** Reported rather than trimmed, because the work landed
complete and green; the honest accounting of where the estimate went wrong:

| item | estimated (part 1) | actual |
|---|---:|---:|
| slice graph `sgraph` with readings | 250-350 | 205 |
| the four waiting clauses | 150-200 | 415 |
| restatement, six ported clauses | 150 | 190 |
| `imgC` clause + projection graphs + `comp` | 150-250 | 440 |
| **total added** | **550-850** | **1,251** |

The slice graph came in *under* estimate. The overrun is all in the clauses:
`chSepC` and `eqSepC` are 90 lines each rather than the estimated 40 (each
needs its own ambient sets, four `InJ` derivations, and a two-directional
test), and the `imgC` clause is 300 rather than 150, because the shifted
argument vector needs `liftGraphs`/`liftArgs` (a per-slot `IsGraph` proof
through a composition, 60 lines) and both projection graphs need their own
two-directional specifications (110 lines) before the clause proper starts.
The pattern: **per-clause cost is dominated by ambient-set bookkeeping, not by
the mathematics**, and the estimate priced only the mathematics.

## 4. Timings, and one wall

| stage | wall clock |
|---|---:|
| part 1, final | 2.8 s |
| + `comp`, `join-out`, `vals`, the **slice graph** | 3.2 s |
| + closure lemmas for all of it | 3.2 s |
| + the projection graphs | 3.8 s |
| + argument records, restated statement, `graphOf`, six clauses | **29.5 s** |
| the cheap-right-projection experiment | **wall, killed past 600 s** |
| + `pairC`, `colC` | 30.3 s |
| + `chSepC` | 31.3 s |
| + `eqSepC` | 31.7 s |
| + the **`imgC` clause** | 33.4 s |
| + induction, `Jimg`, `Discharge` | 33.6 s |
| **final, cold** | **33.6 s** |
| gates: `lint-prose`, `lint-agda`, `check-glossary`, `weave-i18n --check` | all exit 0 |

**Of the 33.6 s, 25.7 s is one two-line lemma**, `prR-pair a b = right-spec a b`
(profile attribution, confirmed twice). The other 1,980 code lines check in
about 7 s. No heap event; one wall event, killed with `pkill` and not rerun
(section 5, item 2).

## 5. Surprises and lesson candidates

1. **(P series, new; sharpens R-38) The transparent Images kit has an
   invocation cost, not only a sealing hazard.** R-38 says a consumer's alias
   of a transparent imported operation is a birth site. This batch found the
   other half: `right-spec a b` costs **25.7 s to invoke even at variable
   arguments**, while its sibling `left-spec a b` costs **64 ms** (same file,
   same shape, 400x apart). `right` is a `sett` over a separation whose
   condition mentions the pair itself, `left` is `⋃ ⋂`. The cure is not
   sealing the alias (that moves the cost, measured: 25.5 s at `appAt-pair`
   before sealing, 25.4 s at `prR-pair` after) but *paying it exactly once*:
   one sealed alias with the pair equation inside, and every consumer reads
   only the equation. Rule: when an imported transparent operation is
   expensive to invoke, the alias's job is to be the single site that invokes
   it.
2. **(P-i [A], measured again) The obvious cheaper replacement is worse, and
   walls.** `right` can be replaced by `F5 (F10 (F0 x x) (prL x)) (F0 x x)`,
   which is the same set at a pair and built only from cheap sealed
   operations. Proving its pair equation needs `extensionality` at that very
   term, which puts a `sett`-over-`F10` tower in a conversion position: the
   file went from 30 s to **killed past 600 s**. This is P-i [A] exactly
   ("heavy values never sit inside extensionality"), and it is worth recording
   that the heavy value here was *my own construction built from cheap parts*,
   not an imported one.
3. **(D series, new) In this tuple calculus the identity graph is the only
   permutation primitive, and everything else is built from it.** `F3`
   inserts after the first coordinate, `F4` appends a block at the end of a
   pair, `ranOp` strips the leading coordinate: none of the three can move a
   coordinate left past another. The identity graph is what pays for every
   such move, and it is now spent in five places: the converse `swp`
   (`⟨u,v,u⟩`), both projection graphs (`⟨d,d,t⟩` and its mirror), the
   equality test of `eqSepC`, and the separated variable's graph at the top
   level. A calculus of this shape should build its diagonal first and treat
   it as the coordinate-permutation primitive, rather than reaching for it
   only where equality is visibly needed.
4. **(estimation) Per-clause cost is ambient-set bookkeeping.** Section 3's
   table: the mathematics of `chSepC` is a join, a membership test and a
   domain (about 12 lines of content), and the clause is 90. The rest is
   naming `WA`, `WB`, `Q`, `Wc`, deriving four `InJ` facts about them, and
   threading two membership proofs per value. Future estimates for this layer
   should price roughly 3 lines of bookkeeping per line of content.
5. **(craft, confirming part 1's item 2) The carrier principle held to the
   end.** The element relation stayed the right carrier through all ten
   clauses: the only four clauses that needed the graph are exactly the four
   whose operation is *not* determined by the members of its arguments
   (pairing, collection, and the two separations read the values themselves),
   and each of those calls `graphOf` and nothing more.

## 6. Protocol compliance (part 2)

- Files touched: `src/L/Rud/Graphs.lagda.md`, `_build/r5a-report.md`.
  `git status` shows `?? src/L/Rud/Graphs.lagda.md` as modified-untracked-only
  in the sense that part 1 is committed (`a34907c`) and this is its extension;
  nothing else is modified. `LevelDesc.lagda.md` was read (export list) and
  never edited.
- Only the module was typechecked, never `Everything`, never `make check` in
  full; the four Python gates were run on the file directly, all exit 0.
- `GHCRTS=-M12g` on every run, one check at a time. One wall event: killed
  with `pkill`, diagnosed by profile (P-i), the offending construction
  reverted, never rerun blind. No heap event.
- Stop-line **exceeded**: 1,982 against 1,700, reported in section 3 with the
  accounting rather than absorbed silently.
- Prose: en + zh, no em dash, CJK full-width punctuation, half-width parens,
  zh paragraphs on single lines; `初步函数` unchanged as the only rendering.

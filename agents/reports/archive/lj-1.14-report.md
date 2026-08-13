# LJ-1.14 report: Tarski-Vaught at a NON-transitive carrier

## 1. THE VERDICT

Route 1 delivered. `TV-thm` now holds at any carrier inside a stage. The
in-fence count is 372 lines. The stated result `TV-thm` is unchanged. No
commit was made.

## 2. THE TWO PRICES

These prices were written BEFORE the build. They are the first prices for
this gap. `[LJ-1.3]` section 6 does not name the gap inside piece three.

**Route 1: re-prove the equivalence at a non-transitive carrier.**
The price is 50 to 70 in-fence lines. The chapter has 343 in-fence lines at
HEAD. Route 1 lands the chapter at 393 to 413 lines.

The price rests on these parts. The inner-world satisfaction moves to a
direct `FOL.Semantics` instance at the restricted structure. That instance
needs no transitivity. The bounded-quantifier cases route through the
Tarski-Vaught criterion. Each case needs one variable-weakening step and one
membership conversion. The tree already delivers both parts.
`FOL.Manipulation.Renaming` delivers weakening with its correctness.
`hull-closed` is not touched.

The price is medium-high confidence. The classical pattern of the `∀̇` case
already exists in the chapter. The bounded cases copy that pattern.

**Route 2: Devlin 5.3's substitution route.**
The price is 210 to 430 in-fence lines. This is `[LJ-1.3]` section 6, pieces
one to three. The pieces are the order element's stage membership, the
leastness encoding, and the full elementary reading at hull parameters. The
price rests on `[LJ-1.3]` section 6. The price is medium-low confidence.

Two facts raise the price. The exact rep of the order formula is truncated.
`[LJ-1.3]` section 8.2 records that residue. The n-ary criterion needs the
environment baked into constants. The tree has renaming, not substitution.
`FOL.Manipulation.Renaming` says that design in its opening lines.

**The comparison.** Route 1 costs 50 to 70 lines and is generic. Route 2
costs 210 to 430 lines and is specific to this hull. Route 1 is cheaper and
more general. The recommendation is route 1. Section 6 gives the DD4
analysis.

## 3. WHERE `Mtr` IS SPENT

Against HEAD, `src/L/Hull.lagda.md`:

- Line 70: `Mtr : isTransV M` is a parameter of `module AtM`.
- Line 72: `FOL.Absoluteness.Single` takes `Mtr`. The definitions of `SM`
  and `⊨ᵐ` do not use it. Only `abs₀` uses it.
- Lines 151 and 176: the bounded-quantifier cases pack an outer member into
  `SM` with `Mtr`. The review's span `:142-181` matches the two bounded
  cases.

Route 1 replaces the packing step. The inner satisfaction comes from
`FOL.Semantics` at `𝒮ᵥ ↾ (λ x → x ∈ˢ M)`. That instantiation needs no
transitivity. The bounded cases call `tv` on an unbounded matrix. The matrix
is `(var zero ∈̇ renameTm suc t) ∧̇ ψ`, or the same with `¬̇ ψ`. The helpers
`renL`, `mem-ren`, and `mem-inner` move the membership across the weakening.

Final state: `AtM` takes `(M : S) (M⊆L : ...)` only. `Mtr` is gone from the
file.

## 4. THE NUMBER

In-fence, ledger caliber, before: 343. After: 372. The delta is +29. The
delivered delta is below the 50 to 70 band. The count excludes the two
catalogs by DD26.

## 5. SECONDS

Before: 1.78 s, exit 0. After: 1.53, 1.55, and 1.63 s over three runs, exit
0 each. The delta is under 0.5 s. The change is flat by the noise rule. One
process per run, under `GHCRTS="-A64m -I0 -M8g"`.

## 6. WHAT EACH ROUTE LEAVES THE J TOWER

Route 1 leaves a model-theoretic equivalence. The J tower can use it at any
carrier with a Tarski-Vaught criterion. Route 2 leaves a step that is
specific to how this hull encodes leastness. The J tower cannot reuse that
step. DD4 favors route 1. The price agrees with DD4.

What remains standing after route 1: the criterion at hull parameters.
`hull-closed` gives the criterion at X-parameters. `TV→elem` at the hull
needs the criterion at hull parameters. The bridge is the substitution step.
That is route 2's content. The price is 210 to 430 lines.

## 7. WHERE MY READING OF 5.1 AND 5.3 DIFFERS

On 5.1 I agree with the review. Devlin's 5.1 needs no transitivity of N. The
equivalence is between elementarity and witness closure. The (ii) to (i)
direction is an induction. The existential case uses the criterion. I
verified the review's file:line claims at HEAD. The bounded quantifiers are
where the old proof spent `Mtr`.

On 5.3 I agree with the mechanism. The criterion is proved at X-parameters
by the least witness. The tree's `hull-closed` is exactly that step. The
meta well-order replaces Devlin's definable well-order. The archive recorded
that decision.

The pricing difference: the substitution step is not small. The n-ary
criterion needs the environment baked into constants. The tree has renaming,
not substitution. `FOL.Manipulation.Renaming` states that design in its
opening lines. Route 2 is therefore `[LJ-1.3]` pieces one to three.

The errata file covers Chapter I section 9 and Chapter VI section 1. It does
not cover Chapter II section 5. No correction applies to 5.1 or 5.3.

## 8. LITERATURE USED

- `_build/literature/dev2.txt:1071-1107`, Devlin 5.1. Quote: "Let M be an
  amenable set, and let N be a substructure of M. The following are
  equivalent: (i) N <_n M; (ii) if A is a non-empty Sigma_n^1(N) subset of
  M, then A intersect N is non-empty." The OCR garbles the symbols. Used
  for route 1's shape: the criterion routes the induction.
- `_build/literature/dev2.txt:1329-1359`, Devlin 5.3. Quote: "Let M be the
  set of all elements of L_alpha which are definable in L_alpha from
  elements of X." The proof uses Tarski's criterion at X-parameters. Used
  for route 2's shape and the `hull-closed` match.
- `dev/literature/digest.md:345-350`, the orthodox route's hull step. Used
  for the route 2 framing.
- `dev/literature/devlin-errata.md`, checked for 5.3. WHY NOT used for a
  correction: the documented classes are Chapter I section 9 and Chapter VI
  section 1.
- `src/FOL/Manipulation/Renaming.lagda.md:50-70,91-130`, `renameTm` and its
  correctness. Used for the weakening in route 1.
- `src/FOL/Manipulation/Relativize.lagda.md:48-90`, read for route 2
  pricing. WHY NOT used in the build: the bound must be a constant of the
  domain. The hull has no stage constant.
- `src/FOL/Absoluteness.lagda.md:57-70,132-160`, `Single` spends
  transitivity only in `abs₀`. The definitions need no transitivity. Used
  for route 1's direct instantiation.
- Skipped: `dev6.txt`, the Devlin and Jech PDFs. WHY NOT: 5.1 to 5.3 are in
  `dev2.txt`. The errata file covers the known error classes.

## 9. ARCHIVE USED

- `_build/lj-1.11-review.md:393-407`, F3. Took the two routes and the
  file:line claims. Verified them against HEAD.
- `_build/lj-1.11-review.md:111`, the scoring row. Took "elementarity AT
  HULL PARAMETERS is owed".
- `_build/lj-1.3-report.md:77-79`, section 4. Took "the hull is not
  transitive" and "`AtM Hull` does not apply as delivered".
- `_build/lj-1.3-report.md:114-129`, section 6. Took the three standing
  pieces. Took the 210 to 430 band as route 2's price.
- `archive/rud-route/src/L/Hull.lagda.md:120-122,216,241`. The retired
  `TV→elem` spends `Mtr` at the same two bounded cases. Its shape does NOT
  survive at a non-transitive carrier. The generalization is new code.
- `_build/l3.32-t40-report.md:30-50`. The archived elementarity row. It
  states "at a transitive set carrier". The bounded quantifiers consume
  transitivity.
- `archive/dev/TASKS-archived.md:75`. Took the pointer to the archived hull
  report.
- `dev/LESSONS.md`, through `scripts/rules.py --for build`. Took P-h, P-l,
  P-m, P-n, R-35, R-38, R-40, I-5, C-12, C-22, and D-10.

## 10. WHAT I AM NOT SURE OF

1. The after time is lower than the before time. The delta is under the
   noise floor. A quiet machine should re-measure.
   The re-check after the sibling commits took 2.69 s. The comparison in
   section 5 holds the tree state fixed.
2. The `Mtr` parameter is removed from `AtM`. No in-tree consumer
   instantiates `AtM`. I judged the removal necessary for the deliverable.
3. The criterion at hull parameters is still standing. It is route 2's
   content.
4. The route 2 price rests on `[LJ-1.3]`'s survey. The order-atom exact-rep
   residue could move it.
5. The `mapTm-rename` commute is local. A generic commute might serve later
   consumers. I did not add one to `FOL.Manipulation`.

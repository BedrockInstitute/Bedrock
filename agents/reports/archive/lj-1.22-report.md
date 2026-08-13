# LJ-1.22 report: price the counting interaction the fork creates

## 1. THE VERDICT

NEUTRAL.

Counting `Code` needs the same cardinal arithmetic as counting
`Formula K 1`. It adds structural recursion, not a new law. The marginal
price is about 120 lines and about 2 seconds at the parameterized class.
The fork does not make the `[LJ-1.17]` failure better or worse. The
objection that the fork worsens the wing's only measured failure dies.

The arithmetic:

- The pair is 1,283 lines at 41.36 seconds, 0.0322 seconds per line, 2.44
  times the DD24 bar, 28 to 42 percent of the 99.6 to 147.7 second budget
  (`_build/lj-1.17-report.md` section 5, `dev/ledger.toml:273`).
- Both counts consume pairing at beta as a module parameter
  (`src/L/StageCardinal.lagda.md:59-66`). The fork adds no law and no
  harder instance of it.
- The marginal counting is about 2 seconds ESTIMATED, 1.4 to 2.0 percent of
  the budget, and about 20 times below the pair.
- The delivered counting half is 794 lines. It sits in the wing row at
  5.46 seconds (`_build/lj-1.17-report.md` section 5).

The fork inherits the square-law wall in both branches. It does not escape
it. The ruling must not treat the fork as a cure for `[LJ-1.17]`. The fork
and the wall are orthogonal.

## 2. DOES `shape-count-inj` ALREADY GIVE IT?

YES, the arity-indexed half.

`shape-count-inj` at `src/FOL/Count.lagda.md:211-213` is a per-arity
injection of parameter-free formulas into N with injectivity:
`Σ[ f ∈ ((k : ℕ) → Formula (⊥* {ℓ}) k → ℕ) ] (∀ {k} {φ ψ} → f k φ ≡ f k ψ
→ φ ≡ ψ)`. It is built from `code` at `:81` and `code-inj` at `:171`. It
gives every `wit` node its countable label. This is the seed `[LJ-1.18]`
section 6 named.

It does NOT give the tree part. The node label is not the code. Counting
`Code` still needs one recursive injection over the vector payload.
`codeByCount` at `:648` is the wrong instrument. It is the constant
round-trip for `Formula K 1`, and `[LJ-1.18]` section 7 showed `encode` is
off by one from `wit`. Counting `Code` does not use it.

D-10 answer: the residue is TRUE as recorded, at the intended generality.
The corrected target: `shape-count-inj` is the label half. The missing half
is the recursion over `Vec Code k`.

## 3. THE OBLIGATIONS

Counting `Code` adds four obligations that counting `Formula K 1` does not
have.

O1. A recursion scheme for `Code` over its nested payload. `wit` carries
`Vec Code k`, so the encoding needs a mutual `enc` and `encs`. The
delivered tree has no counting version. The probe delivered the same shape
for `val` and `vals` (`src/ProbeLJ118.agda:55-63`), and the termination
checker accepts that shape (F2 in `_build/lj-1.18-report.md`). Missing:
about 10 to 15 lines.

O2. A disjoint-image encoding of the two constructors. `base x` must not
collide with a `wit` image in beta. A numeral tag separates them:
`pair (numeral 0) (fst g x)` for `base`, and a `suc k` tag for `wit`. The
`Formula K 1` count needs no such tag because `composed-count` already
lands in a dependent sum with an arity tag. Missing: about 8 to 12 lines.

O3. The recursive injectivity proof, `enc-inj` and `encs-inj`, with
dependent transport over the arity. The pattern is delivered.
`count-bound-inj` at `src/L/StageCardinal.lagda.md:124-160` recovers
`k ≡ k'`, transports the shape and the tuple, and applies the per-arity
injections. The Code version adds the two-constructor split and the vector
recursion, like `tuple-g-inj` at `:100-110`. Missing: about 50 to 70
lines.

O4. The constructor recovery for `wit`. From `wit k ψ cs ≡ wit k' ψ' cs'`,
recover `k`, `ψ` and `cs`. A `parts` projection plus `cong` is the safe
route. Missing: about 10 to 15 lines.

Then the assembly, `code-bound`, mirrors `formula-bound` at
`src/L/StageCardinal.lagda.md:172-178`. Missing: about 5 to 10 lines.

Delivered and reused unchanged: `shape-count-inj`
(`src/FOL/Count.lagda.md:211-213`), `code` (`:81`), `code-inj` (`:171`),
and the whole `Bound` ordinal kit: `pair` and `pair-inj`
(`src/L/StageCardinal.lagda.md:63-67`), `numeral` and `numeral-inj`
(`:82-86`), `tuple-g` and `tuple-g-inj` (`:95-110`), `code-stable` and
`tuple-g-stable` (`:89-93`, `:112-117`).

Not needed: the `Count K` constant round-trip
(`src/FOL/Count.lagda.md:222-694`, encode, decode, erase), `composed-count`
(`:695-698`), and `countFo` and `constantsFo`. The Code node payload is
already parameter-free. The count is simpler per node. `count-bound` keeps
an `n` coordinate; the Code count does not.

No witness quotient step. The probe's hull index is `Code` itself
(`src/ProbeLJ118.agda:84-85`). Counting the index is counting `Code`. The
archive's `index↪formula` step
(`archive/rud-route/src/L/CardinalCount.lagda.md:105-108`) is not needed.

## 4. THE MARGINAL PRICE

Lines: 120 in-fence, one best-effort figure. Basis: the delivered
`count-bound-inj` block is 42 lines and `tuple-g-inj` is 8 lines. The Code
kit needs one recursive layer, two constructor cases, and two stability
lemmas. It is roughly the size of the `Bound` counting half without the
constant round-trip. Range 100 to 150. ESTIMATED, not measured.

Seconds: 2, one best-effort figure. ESTIMATED, not measured. No Agda was
run by constraint. Basis: whole-module rates of the same content class.
`src/FOL/Count.lagda.md` measured 0.0011 seconds per line.
`src/L/StageCardinal.lagda.md` measured 0.0052. The probe measured 0.0103
with a fixed cone of about 1 second (`_build/lj-1.18-report.md` section 4).
At 0.005 to 0.010 seconds per line over 120 lines, plus the cone, the
total is 1.6 to 2.2 seconds. Range 1.5 to 3. P-s is respected. These are
whole-module rates of the same family, not a slice rate divided down.

Content class: P-m parameterized, at or below the 0.01 to 0.013 band
(`dev/LESSONS.md:2419`). Everything is generic in K, beta, g and pairing.
There is no satisfaction content and no concrete carrier. It is not the
instantiation class at 0.22 to 0.297 (`dev/LESSONS.md:2442`). It is not the
square-law middle at 0.0255 to 0.0485 (`_build/lj-1.17-report.md` section
6).

The fork likely drops the 430-line constant round-trip. The net counting
cost is likely below the keep branch's 794 lines. That projection is a
survey, not a price. It is not load-bearing for the verdict.

## 5. WHICH CARDINAL LAW

The same law, at the same strength: pairing at beta, `|β × β| = |β|`, the
`Bound` module parameter at `src/L/StageCardinal.lagda.md:59-62`.
`Vec Code k` is a finite tuple. The recursive layer needs only iterated
binary pairing, exactly like `tuple-g` for `Vec K k` (`:95-110`). The
weaker law `|ℕ × A| = |A|` would suffice for the outer union over depth. It
is a corollary of pairing via the numerals (`:82-86`). No law is stronger
than the square law. The chain needs `|α × α| = |α|` at every infinite
cardinal and limit (`_build/lj-1.17-report.md` section 2). Counting `Code`
needs no more.

The union over N that `[LJ-1.18]` section 6 named is internal to the
constructor. `wit` carries its arity. The recursive encoding codes the
whole tree in one pass. The depth-union route is one option. It is not
required.

## 6. IS IT THE SAME PROBLEM IN DIFFERENT CLOTHES?

Yes, in substance.

`Formula K 1` is a finite tree with atoms from K and fixed node labels.
`Code` is a finite tree with atoms from K and node labels from a fixed
countable set, the parameter-free formulas. Both count with the same kit:
countable labels, numerals, and pairing. Devlin's object, the language
`ℒ_X`, is closer to `Formula K 1`. He counts formulas over X
(`_build/literature/dev2.txt:1357-1360`), never a meta term algebra. His
standard, `max(|X|, ω)`, is the same bound the Code count reaches.

The one real difference is Agda-side, not mathematical. `Formula K 1`
counts flat: a shape plus a constant tuple. `Code` must recurse through
the vector payload once. That recursion is new code, about 120 lines, in
the same content class as the delivered counting half. It is a different
presentation of the same counting problem, not a harder one.

## 7. DOES IT STAY TEMPLATE? (DD4)

Yes.

`Code` is generic in the carrier (`src/ProbeLJ118.agda:44-46`). The enc
kit is generic in K, beta, g and pairing. Nothing in the counting types
mentions `Lset`, a stage presentation, or a tower. The kit needs no L
import, like `FOL.Count` today. The one new dependency edge is the import
of the term algebra master for `Code`, which is itself template. Both
towers instantiate the same kit. The counting work does not force
L-specific content into `FOL.Count`.

D-26 does not bear. Counting is below the well-founded key line. It
injects the hull index into an ordinal. `Code` carries its own generation
data, so its well-founded key is its inductive structure. The count needs
no tower well-order.

P-l is satisfied by construction. The statements are about K and beta as
atoms. No presentation is dragged into the types.

## 8. UNDER `[LJ-1.17-R]`'S POSSIBLE REFRAMING

The answer does not change.

The counting of `Code` is separate content in the cheap parameterized
class. It does not depend on who pays the square law. If the pair is billed
to the project, the wing's budget improves, and the fork's 2 seconds are
even less significant. If the pair stays in the wing, the fork's 2 seconds
do not rescue or break the arithmetic. The wing already fails at 0.0155
seconds per line with zero seconds for everything else
(`_build/lj-1.17-report.md` section 5). Either way the fork is neutral on
the square-law failure.

## 9. LITERATURE USED

- `dev/literature/devlin-II5.md:134-144` (1.4, Devlin 5.4). Took: the hull
  count is a count of the language `ℒ_X`, and the proof is one line.
  Devlin's object is `Formula K 1`, not `Code`.
- `:272-277` (2.5, Step E). Took: the counting strength is cardinal
  arithmetic on a countable formula set with parameters from X. No
  level-story content. The Code count sits in the same class.
- `:411-419` (5.2, II.1.1(vii)). Took: the counting half of 5.5 and 5.6 is
  generic cardinal arithmetic, shared by both towers.
- `_build/literature/dev2.txt:1357-1360` (5.4). Took: `|M| = max(|X|, ω)`,
  the one-line standard the tree matches.
- WHY NOT: `devlin-II5.md` sections 6.1 to 6.7. `[LJ-1.17]` checked the
  OCR items, and they do not touch the counting. `j-hierarchy.md`: the
  J-side size analogue is not needed for the counting interaction.
  `devlin-errata.md`: `[LJ-1.18]` verified it does not cover Chapter II
  section 5.

## 10. ARCHIVE USED

- `_build/lj-1.18-report.md`. Read fully. Took: F2 (the `vals` termination
  shape at `src/ProbeLJ118.agda:55-63`), section 6 (the countable union,
  named and unpriced), section 7 (`encode` off by one from `wit`), section
  4 (probe 116 lines at 0.0103 seconds per line, stub cone about 1
  second).
- `_build/lj-1.17-report.md`. Read fully. Took: the pair at 41.36 seconds
  and 0.0322 seconds per line, 2.44 times the bar, 28 to 42 percent of the
  budget; the law at every infinite cardinal and limit; the content-class
  analysis.
- `_build/lj-1.6-report.md`. Read fully. Took: the delivered counting half
  at 794 lines, `FOL.Count` at 0.0011 and `StageCardinal` at 0.0052
  seconds per line, the `Bound` parameterization, the carrier-quotient
  stop.
- `_build/lj-1.6-review.md`. Read sections 1 to 2. Took: the corrected
  square-law figures (1,283 in-fence, 23.3 seconds, 18.6 seconds) and the
  least-value descent cure.
- `archive/rud-route/src/L/CardinalCount.lagda.md`. Read fully. Took: the
  retired route counted the hull's own index `Formula ⟪ X ⟫ 1` (prose
  `:8-12`), `composed-count` (`:71-83`), `index↪formula` (`:105-108`),
  `Bound` (`:155`), `count-bound` (`:204-206`) and `count-bound-inj`
  (`:209-212`). It stopped at the square law (prose `:13-17`). It never
  counted `Code` and never counted the carrier.
- `archive/rud-route/src/L/CardinalPredicates.lagda.md`. Surveyed. Took:
  it defines internal pair and bijection predicates (`ordFo`, `pairFo`,
  `oprFo`, `HostBij`, `HostEq`). WHY NOT used: it has no counting content
  for `Code` or the hull.
- `dev/LESSONS.md`. Took: P-m at `:2419`, P-n at `:2442`, P-s at `:2528`,
  D-10 at `:1316-1335`. All four bound this block.
- `dev/ledger.toml`. Took: `gch_wing_seconds_budget = [99.6, 147.7]` at
  `:273`, the DD24 caliber `ac_baseline_module_rate = 0.011472` at
  `:2545`, the 0.297 instantiation rate at `:1754`, and the 23.3 and 18.6
  second figures at `:1796` and `:1801`.

## 11. WHAT I AM NOT SURE OF

1. The termination of `enc` and `encs` is not re-checked at this site. The
   probe's `val` and `vals` shape passes (F2), and `enc` is the same
   shape. The risk is small but real. The build must confirm it.
2. The line and second figures are estimates, not measurements. No Agda
   was run by constraint. The rates come from whole modules of the same
   class.
3. The constructor recovery for `wit` may be cheaper or dearer than 10 to
   15 lines. Cubical Agda's handling of nested-inductive equality is the
   one part of the kit with no delivered precedent. `count-bound-inj` is
   the closest analogue.
4. Whether the fork build drops the 430-line constant round-trip is a
   survey. The verdict does not depend on it.
5. The hull in the probe is indexed by `Code` directly. If a later shape
   adds a witness component, the first-projection step is needed. It is
   about 8 lines and generic, per `archive/rud-route/src/L/CardinalCount.lagda.md:105-108`.

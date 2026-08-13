# Adversarial math review: the twelve-row composition

Reviewer dispatch: diag-twelve-row-math. Date: 2026-08-12.
State reviewed: commit `dd3aa13` (HEAD at review start). The working tree
carries live `LJ-1.76` edits, so all `src/` reads come from `git show
dd3aa13:<path>` unless a line says otherwise. A live agda process (LJ-1.76)
holds the machine, so this review runs NO Agda. Every claim is marked
MEASURED (read directly in the source, or checked by Agda before this
review) or INFERRED (this reviewer's reasoning).

## Verdict summary

1. **Q3, the deepest:** `TwelveAgree` is the RIGHT theorem: it is
   Devlin's II.2.4 bounding step, unrolled per constructor, and both
   directions are required by Step C's down-and-back transfer. The
   design is sound. Its HYPOTHESES are not (see 4).
2. **Q1:** the split composes the same twelve rows, term-identical
   conjuncts, correct order, sound polarity, but the composed formula
   is re-associated relative to `SatGraphB.twelveB`, which is what
   `SatGraphAgree` and `LeafAgree` consume. A content-free re-pairing
   glue is required and exists nowhere. Repair: make the composer
   target `SatGraphB.twelveB` itself.
3. **Q2:** the 43/26 fact split is sound bookkeeping and cannot have
   rerouted any row proof. But the 17 shared facts include the
   uninhabitable ones, so both halves inherit them.
4. **Q4, the heaviest finding:** the C-38 defect generalizes. At
   least `tmKeyK`, `KFacts.pairK`, `KFacts.arityK`, `KFacts.innerK`,
   `KFacts.innerPairK` are uninhabitable at EVERY environment
   (self-refutation against `∈-irrefl` / `regularityV`), and `valK` /
   `valK-un` are satisfiable only at degenerate sites. `KFacts` has
   no inhabitant, so `SatGraphAgree` and `LeafAgree` can never be
   instantiated as stated. The LJ-1.72 repair fixed `tagEq` only. The
   split being built by LJ-1.76 carries the same facts. The repair is
   to `K`-relativize every unguarded quantified variable, Devlin's own
   hull-closure form; the twelve-row shape survives it, the telescopes
   and row-proof threading do not.
5. **The number:** one measured leg of three; the halves are not
   symmetric in content; and the measured shape lacks the glue of
   item 2 and predates the repair of item 4. The mathematics says the
   274 s figure prices a statement that must change.

## 1. Is the split the same theorem?

**Verdict: the same twelve rows, the same terms, but NOT the same
proposition.** The composed statement is a re-associated conjunction.
The consumer requires the exact right-nested formula. A small glue term
closes the gap. Nobody has written it, and no report names it.

### 1a. Association and row order

The machine side `twelveAt` is a RIGHT-NESTED twelve-way conjunction in
the order mem, eq, and, or, imp, neg, top, bot, exist, forall, allIn,
exIn (`src/L/Coding/Graph.lagda.md:94-101`). MEASURED (read).

The story side the chain consumes is `SatGraphB.twelveB`, also
right-nested, same row order (`src/L/Condensation.lagda.md:2233-2254`
at `dd3aa13`). MEASURED (read). `SatGraphAgree` and `LeafAgree` take
`twelve-out` / `twelve-back` as parameters stated against EXACTLY this
formula (`src/L/Condensation.lagda.md:6770-6775` and `:7013-7018` at
`dd3aa13`). MEASURED (read).

The measured composer builds its OWN formula:
`twelveB = p0b ∧̇ (p1b ∧̇ (p2b ∧̇ p3b))`
(`src/ProbeLJ174F.agda:563-564`). The in-flight LJ-1.76 composer
does the same with two halves: `twelveB = p0b ∧̇ p1b`
(`src/L/Condensation/TwelveAgree.lagda.md:267-268`, working tree,
mid-dispatch). MEASURED (read). As a `Formula` term,
`(m0 ∧̇ (... ∧̇ m5)) ∧̇ (m6 ∧̇ (... ∧̇ m11))` is NOT
`m0 ∧̇ (m1 ∧̇ (... ∧̇ m11))`. The two satisfaction types are
differently-associated products of the SAME twelve component types.
They are isomorphic, not equal. INFERRED, from the syntax read above.

The twelve conjuncts themselves ARE term-identical to
`SatGraphB.twelveB`'s conjuncts: `LowerAgree.sixB`
(`src/L/Condensation/LowerAgree.lagda.md:223-248`) matches conjuncts
0-5, `UpperAgree.sixB` (`src/L/Condensation/UpperAgree.lagda.md:
213-238`) matches conjuncts 6-11, at the same slot shifts. MEASURED
(read, side-by-side against `:2235-2254`). The four probe partials
likewise cover rows 0-2, 3-5, 6-8, 9-11 in `twelveAt`'s order
(`src/ProbeLJ174P0.agda:6606-6628` and the same blocks in P1, P2, P3).
MEASURED (read).

**Consequence.** The composer's `out` has type
`twelveAt -> composer-twelveB`, but the chain needs
`twelveAt -> SatGraphB.twelveB`. The gap is a re-pairing of twelve
components (12 projections, 11 pairings, both directions). It has no
mathematical content. It exists nowhere: not in the probes, not in the
in-flight masters, not in any report. The `back` direction does NOT
have this gap on its target: the composer's `back` lands in the exact
`twelveAt` (`src/ProbeLJ174F.agda:845,1122-1125`;
`src/L/Condensation/TwelveAgree.lagda.md:291-315`), but its SOURCE is
the re-associated formula, so the same glue is needed there too.
INFERRED (type comparison; no Agda run, the machine is held by
LJ-1.76).

**Repair, one line of design.** Make the composer state `twelveB :=
SatGraphB.twelveB` and do the re-pairing inside its `out`/`back`
bodies. That deletes the third spelling of the bounded twelve (the
tree then has `SatGraphB.twelveB` only) and makes the composer's type
the consumable one. This is not a redesign; it is where the glue
belongs.

### 1b. The one-hypothesis question: is feeding `h` to all partials sound?

**Sound, both directions.** The partials' statements are asymmetric by
design, and the polarity is correct:

- `out : <full machine twelve> -> <own bounded rows>`. `LowerAgree.out`
  takes `⟨ γ ⊨ twelveAt ⟩` whole and projects `h .fst` through
  `h .snd^5 .fst` (`src/L/Condensation/LowerAgree.lagda.md:259-266`;
  same shape `src/ProbeLJ174P0.agda:6630-6634`). Feeding the whole
  machine hypothesis to each partial is weakening, which is sound.
  MEASURED (read).
- `back : <own bounded rows> -> <own machine rows>` (`sixB -> sixAt`,
  `src/L/Condensation/LowerAgree.lagda.md:268-275`). The hypothesis is
  the OWN six bounded rows only, so no circularity is possible: no
  machine-side fact enters a `back`. The composer feeds `h .fst` and
  `h .snd` to the two `back`s and re-pairs the twelve machine
  components in row order (`src/L/Condensation/TwelveAgree.lagda.md:
  311-315`; `src/ProbeLJ174F.agda:1122-1125`). MEASURED (read).

The brief's feared case, both sides narrowed AND the conjunction not
recomposing, does not occur: the machine-side satisfaction of
`twelveAt` is definitionally the product of the twelve row
satisfactions (HEAD is green while `TwelveAgree.out` projects
`h .fst`..`h .snd^11` from it, `src/L/Condensation.lagda.md:6720-6733`
at `dd3aa13`, so the unfolding is definitional; MEASURED), and a
product transfers component-wise. The composition of the partial
agreements IS the twelve-row agreement, up to the association gap of
1a. INFERRED (the argument), MEASURED (each read cited).

## 2. Is the fact split sound?

**Verdict: sound as a split. The 43/26 partition cannot change any
row's proof, and no hidden channel exists. But the partition
distributes the poison of section 4 into BOTH halves.**

The structure that makes it sound:

1. **The row proofs are frozen at their definition sites.** The twelve
   row modules (`MemAgree` at `src/L/Condensation.lagda.md:4117`
   through `ExInAgree` at `:4788`, ranges per
   `_build/lj-1.75-report.md` section 1) take their site facts as
   module parameters over an ABSTRACT `γ`. A partial only APPLIES
   them. Dropping 26 facts from a partial's telescope cannot reroute a
   row's proof: the row never had access to any fact outside its own
   parameter list. MEASURED (read of the applications at
   `:6594-6671`, HEAD).
2. **No indirect channel exists.** The brief's worry, dependence
   "through a module it applies, through a default, through a
   definitional unfolding", would require the row module to reach a
   site fact not in its parameters. With `γ`, `K`, `N*` abstract in
   the row module, every site-dependent assumption MUST be a
   parameter; global lemmas the rows use (`numeralL-inj`, `prʟ-fst`)
   are site-independent theorems, not site facts. INFERRED, from the
   module structure read above.
3. **What the green typecheck proves.** A 43-fact partial checking
   green proves the 43 suffice to FEED the six applications. That is
   the whole claim; sufficiency of the arguments is exactly what Agda
   checks. The "weaker path" scenario would need a row proof to
   change, and no row proof is in the partial. The LJ-1.75 table's
   per-row sets match the applications I read at HEAD (row 0 at
   `:6594-6599`: tagEq0/numK0/innerK/pairK/codesK/valK/t0eq/t1eq/t0K/
   tmKeyK/num1K/envK-mem/entryK/arSubK-mem/envInK-mem/valV/valW,
   17 facts, as tabulated). MEASURED (read); the green run is
   LJ-1.75's claim, which I did not re-run.

**The caveat that matters:** the 17 shared facts
(`_build/lj-1.75-report.md` section 1) include `tmKeyK`, `pairK`,
`valK`, `valK-un`. Sections 4a and 4c show `tmKeyK` and `pairK` are
uninhabitable and `valK` degenerate. So BOTH halves carry
uninhabitable hypotheses, and the fact split, sound as bookkeeping,
partitions a telescope that no site can ever supply. The split's
arithmetic is right; the set being split is wrong. INFERRED from
section 4.

## 3. Is `TwelveAgree` the right theorem?

**Verdict: the right theorem, wrongly hypothesized.** The OBJECT, a
two-way agreement between the unbounded machine clause table and a
`K`-bounded story restatement, is exactly the substrate Devlin's Step
C consumes. The twelve-row FORM is a defensible spelling of a
relativization schema that could also be written once, generically.
The defect is not the shape; it is the site facts (section 4).

### 3a. What Devlin does at this step

Devlin's II.5.5 uses condensation through 5.4's hull
(`_build/literature/dev2.txt:1372-1385`). The engine underneath is
Step C (`dev/literature/devlin-II5.md:209-256`): level-hood is Σ₁
with a Σ₀ matrix, and the Σ₀ matrix is built by BOUNDING every
unbounded quantifier of the Def-description by the concrete set
`K(u)` (II.2.2-2.4, `dev2.txt:593-630` as digested at
`devlin-II5.md:246-256`), then moved across transitive carriers by
Σ₀ absoluteness (1.9.15). Devlin spends one page bounding and one
citation absolutizing. He never states a per-constructor agreement;
the induction over the formula structure is inside his absoluteness
metatheorem and inside the bounding argument. MEASURED (read of the
digest and the source).

### 3b. What the tree proves instead

The tree separates the same two steps the same way. The absoluteness
half lives in `AbsL` (`FOL.Absoluteness.Single`,
`src/L/Condensation.lagda.md:70`). `TwelveAgree` is the BOUNDING
half: `twelveAt` (machine, unbounded `∃̇`) against `twelveB` (story,
`∃̇∈ K`), given closure facts saying the witnesses live in the
`K`-slot. Each row's `out`/`back` is "bounding this constructor's
clause by `K` changes nothing, because its witnesses are in `K`".
That is II.2.4's move, done per constructor. The chain then needs
BOTH directions because the Σ₁ statement travels down to the hull and
back up through the collapse (Step C item 4,
`devlin-II5.md:230-235`), so no direction can be dropped; the brief's
settled point stands and this review confirms it from the
literature. `_build/lj-1.59-report.md` section 8's record is
accurate: Devlin asserts absoluteness where the tree proves a
transfer, and the tree must prove it because its satisfaction is a
defined predicate over the HIT hierarchy, not an LST formula with a
citable metatheorem. MEASURED (reads); the necessity judgment is
INFERRED.

### 3c. Cheaper routes the coding may have foreclosed

The honest alternative is ONE relativization lemma over the `Formula`
syntax: for `φ` with a per-existential witness-closure oracle,
`⟨ γ ⊨ φ ⟩ ↔ ⟨ γ ⊨ rel K φ ⟩`, proved once by induction, then
instantiated twelve times. The framework supports formula induction
(the `Δ₀`/`Σ₁` classifiers `δ-∧`, `δ-∃∈` are exactly such inductions,
`src/L/Condensation.lagda.md:2256-2289` at `dd3aa13`), and the tree
already owns the single-quantifier version: `extAt→extAtB` /
`extAtB→extAt` are used at `:6395-6399`. So the generic spelling was
expressible; the coding did not foreclose it. What it buys is not
fewer obligations, the same closure facts appear as the oracle's
per-node inputs, but ONE proof body instead of twelve near-copies,
and a statement the J tower could instantiate instead of restating
(see section 6). What it costs is a heavier statement (an oracle
indexed by the formula's quantifier positions). This review does NOT
find the twelve-row design wrong: it is Devlin's own bounding step,
unrolled. The unrolled form was chosen and is mathematically
faithful. INFERRED throughout.

**The one place the design should move:** not the rows, the FACTS.
Devlin's closure facts are hull-relativized: "for all a, b IN K(u),
the pair is in K(u)". The tree's are absolute: "for all a, b : S"
(section 4). The twelve-row shape survives that repair unchanged; the
telescopes and the row proofs must be re-threaded with the guards.
That is the real gap between the formal route and the mathematical
one, and it was invisible in twenty dispatches because nothing ever
tried to SUPPLY the facts (C-35, `dev/LESSONS.md:3200`; C-38,
`:3427`). INFERRED.

## 4. Vacuity audit of the chain

**Verdict: the C-38 defect is NOT one module. The telescope facts that
survived the LJ-1.72 repair include at least three that are
uninhabitable at EVERY environment, and `KFacts` itself carries two of
them. The repair fixed `tagEq` and left the rest unexamined
(`_build/lj-1.71-report.md:112-115` says so plainly: INFERRED, no
verdict, not machine-checked). The 274 s shape being built right now
inherits all of them.**

The carrier `S` is the type of ALL constructible sets:
`𝒮ʟ = 𝒮ᵥ ↾ isL` (`src/L/Constructible.lagda.md:410-411`), and the
Condensation master opens its carrier (`src/L/Coding/Model.lagda.md:70`
`open hPropStructure 𝒮ʟ using ( S )`). The tree delivers
`∈-irrefl : (A : S) → ⟨ A ∈ˢ A ⟩ → ⊥` and
`regularityV : WellFounded _∈ᵗ_` (`src/V/Hierarchy.lagda.md:155,139`).
MEASURED (read). Against these:

### 4a. Facts uninhabitable at every environment

1. **`tmKeyK : (k : S) → ⟨ fst k ∈ fst (lookup K' γ) ⟩`**
   (HEAD `src/L/Condensation.lagda.md:6438`; in-flight
   `src/L/Condensation/LowerAgree.lagda.md:95` and
   `UpperAgree.lagda.md:85`). Instantiate `k := lookup K' γ`. The
   conclusion is `X ∈ X` for `X = fst (lookup K' γ)`. `∈-irrefl X`
   closes it. Two lines. The type is empty at EVERY `γ`, EVERY `K`.
   INFERRED (term recipe given; not run, the machine is held).

2. **`KFacts.arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩ →
   ⟨ fst v ∈ fst (lookup K γ) ⟩`**
   (`src/L/Condensation.lagda.md:5707-5708` at `dd3aa13`). Instantiate
   `v := lookup K γ`, `N := pairʟ v v` (the L-singleton:
   `fst (pairʟ v v) ≡ ⁅X,X⁆`, from `prʟ-fst`'s own proof,
   `src/L/Coding/Model.lagda.md:329-334`). The premise `X ∈ {X}` holds
   by pairing; the conclusion is `X ∈ X`. `∈-irrefl` closes it.
   INFERRED (same status).

3. **`KFacts.pairK : (a b : S) → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩`**
   (`src/L/Condensation.lagda.md:5704`; also a telescope fact of every
   row module, every probe partial, and both in-flight partials).
   `prʟ a b = pairʟ (pairʟ a a) (pairʟ a b)` with
   `fst (prʟ a b) ≡ pr (fst a) (fst b)` (Kuratowski,
   `src/L/Coding/Model.lagda.md:326-334`). Instantiate
   `a := b := lookup K γ`. Then `pr X X = {{X}} ∈ X`, and
   `X ∈ {X} ∈ {{X}} ∈ X` is a membership 3-cycle, refuted by
   `regularityV` (a cycle yields an infinite descending `∈ᵗ`-chain
   against `Acc`). INFERRED; needs a five-line no-cycle lemma rather
   than a one-liner.

4. **`KFacts.innerK`, `KFacts.innerPairK`**
   (`src/L/Condensation.lagda.md:5702-5703`): same 3-cycle argument
   with `a := lookup K γ` inside `prʟ (numeralL k) a`. INFERRED.

### 4b. What this makes vacuous

- **`KFacts` has NO inhabitant at any `γ`** (items 2, 3, 4 are
  fields). No code anywhere constructs one: the only `record { tagEq0 =
  ... }` in the tree is `KFactsCons`, which rebuilds from an existing
  `f` (`src/L/Condensation.lagda.md:5722-5751`). MEASURED (grep) for
  absence of a construction site; INFERRED for emptiness.
- **`SatGraphAgree` (`:6760-6769`) and `LeafAgree` (`:6989-6997`) each
  take `f : KFacts ...`.** Both are therefore uninstantiable as
  stated. Their internal implications are real mathematics, but per
  the project's own C-38 (`dev/LESSONS.md`), a hypothesis is
  discharged when something SUPPLIES it, and these can never be
  supplied. INFERRED from 4a.
- **Both in-flight partials and the composer carry `tmKeyK` and
  `pairK`** (`LowerAgree.lagda.md:95`, `UpperAgree.lagda.md:85`, fed
  through `src/L/Condensation/TwelveAgree.lagda.md:270-315`). The
  twelve-row composition now being measured is a theorem whose
  hypotheses cannot all hold. It will typecheck green. It proves
  nothing a consumer can ever use, in exactly the sense C-38 already
  names. INFERRED from 4a; presence MEASURED (read).

### 4c. Facts satisfiable only at degenerate sites

**`valK` (HEAD `:6428-6430`) concludes `⟨ fst yc ∈ K-slot ⟩` for a
`yc` that appears in NO premise.** The premises constrain only `c`.
At any site where some binary code inhabits the `C`-slot, `valK` forces
EVERY `yc : S` into the `K`-slot, and 4a's argument kills it. It is
satisfiable exactly where the `C`-slot contains no binary code, and
there the twelve-row agreement is not the lemma the proof needs.
`valK-un` (`:6431-6433`) is the same shape. This looks like a
statement bug: the honest fact would tie `yc` to `c`'s value entry.
INFERRED (read of the quantifier structure).

**Suspect, not settled:** `envK-mem`, `envK-neg`, `envK-top`,
`envK-imp`, `envK-allin` (`:6440-6459`) universally quantify the
environment components `yc b a ar c` over `S` and conclude
`E ∈ K-slot` for any `E` satisfying an `envSetAt` reading over those
arbitrary components. If a satisfying `E` exists over components of
arbitrary rank, the `K`-slot must contain sets of unbounded rank,
which no set does. Whether such `E` always exists depends on
`envSetAt`'s semantics, which this review did not unfold. Devlin's
corresponding closure facts relativize the components to the hull;
these do not. FLAGGED, not refuted. INFERRED.

### 4d. What survives the audit

`numK0..11`, `num1K`, `t0K`, `t0eq/t1eq`, `tagEq0..11` (post-repair),
`transK`, `carrierK`, and the guarded facts whose every quantified
variable is either tied to a slot lookup or bounded by a premise
(`codesK`, `codesK-un`, `entryK`-style with the pair IN a slot,
`witK`, `satK`, `keyValK`, and `LeafAgree`'s `wCodesK` family,
`:7001-7012`) are satisfiable at a hull-shaped site. MEASURED (read of
each type); the satisfiability judgment is INFERRED.

### 4e. The lesson generalized

LJ-1.71 refuted ONE fact because its consumer's frame happened to
contradict it. The facts in 4a need no frame: they self-refute against
regularity. The audit that catches them is cheap and mechanical: for
every telescope fact, every universally quantified `S`-variable must
be guarded by a premise tying it to a slot or to a bounded set. Any
unguarded positive membership conclusion about the `K`-slot is
refutable by instantiating the variable at the `K`-slot entry itself.
That audit has never been run over the 69 facts. It should gate any
further spend on this chain. INFERRED.

## 5. The number, one paragraph

The symmetry assumption is not mathematically grounded. The two
halves share a fact COUNT (43 = 43), not content: the lower half is
Mem(17) Eq(17) And(10) Or(10) Imp(12) Neg(11) and the upper half is
Top(9) Bot(5) Exist(13) Forall(13) AllIn(20) ExIn(20)
(`_build/lj-1.75-report.md` section 1), and the measured 122.45 s was
the LOWER half only (its section 2 names rows 0 to 5). AllIn and ExIn
carry the succ/key/cons/term-value machinery no lower row has, and
LJ-1.74's own ladder shows unequal per-row increments (rung 3 to 6:
+42 s; rung 6 to 9: +50 s into a wall,
`_build/lj-1.74-report.md` section 1). Equal fact count is a
coincidence of the partition, so the second 122.45 is an
analogy-transferred figure, the exact move AGENTS.md's P-l gloss
forbids pricing with, and the 28.98 s composer was measured at four
partials and without the association glue of section 1a. One term of
three is measured; the claim "worth 274 s" is a projection with one
measured leg. That is all this review says about seconds.

## 6. DD4

**The split is generic in its slots, and that genericity is the
L tower's, not shared.** The partials take `N0..N11 t0 t1 K :
Fin (5 + n)` and an abstract `γ : S ^ (11 + n)`
(`src/L/Condensation/LowerAgree.lagda.md:59-95`), so within the
L tower any frame can instantiate them. But the `suc^6` slot shifts
are baked into every statement, and the carrier `S` is 𝒮ʟ's,
opened at the file head. The row modules, the real engine, live
inside `src/L/Condensation.lagda.md` against the same carrier. The
J tower therefore inherits the SHAPE (partials plus composer, the
43/43 partition, the re-pairing) and restates the STATEMENTS,
which is the LJ-1.70/71 DD4 finding restated for the split: the
defect and the fix both multiply by two towers (D-29's point;
`_build/lj-1.71-report.md:130-133`). The split also states the 17
shared facts twice, a named DD4 cost carried forward from LJ-1.75.
The one DD4-positive move visible from here is section 3c's generic
relativization lemma: proved once over the `Formula` syntax, both
towers instantiate it, and the per-tower cost becomes the closure
facts alone, which each tower owes anyway. This review recommends
pricing that route ONLY as part of the section-4 repair, since the
telescopes must be rewritten then in any case. INFERRED.

## ARCHIVE USED

- `src/L/Condensation.lagda.md` at `dd3aa13` (read via `git show`,
  the working tree is mid-dispatch): `TwelveAgree` `:6412-6748`,
  `KFacts` `:5675-5708`, `KFactsCons` `:5715-5751`, `SatGraphB`
  `:2227-2328`, `SatGraphAgree` `:6760-6802`, `LeafAgree`
  `:6989-7056`, row applications `:6594-6671`. TOOK: every statement
  audited in sections 1 and 4.
- `src/L/Coding/Graph.lagda.md:94-101, 139-146`. TOOK: `twelveAt`'s
  nesting and row order.
- `src/L/Coding/Model.lagda.md:70, 326-334`. TOOK: the carrier `S`
  and `prʟ`/`prʟ-fst` for the cycle argument.
- `src/L/Constructible.lagda.md:410-411`; `src/V/Hierarchy.lagda.md:
  139, 155`. TOOK: `𝒮ʟ = 𝒮ᵥ ↾ isL`, `regularityV`, `∈-irrefl`, the
  refuting tools.
- `src/ProbeLJ174P0.agda:6386-6641, 6378-6384`, `ProbeLJ174P1/P2/P3`
  (partial statements), `ProbeLJ174F.agda:563-567, 845, 1122-1125`.
  TOOK: the measured split's exact types, section 1.
- In-flight LJ-1.76 masters (working tree, unmerged):
  `src/L/Condensation/LowerAgree.lagda.md:59-275`,
  `UpperAgree.lagda.md:49-266`, `TwelveAgree.lagda.md:45-315`. TOOK:
  the production split's exact types; marked in-flight everywhere.
- `_build/lj-1.75-report.md` sections 0-2. TOOK: the fact table and
  the 43/17/26 arithmetic, cross-checked against HEAD's applications.
- `_build/lj-1.74-report.md` sections 0-4. TOOK: the split shape and
  the ladder increments used in section 5.
- `_build/lj-1.71-report.md`, WHOLE. TOOK: the `tagEq` refutation and
  its items 3-4, which mark the remaining facts UNEXAMINED; section 4
  finishes that examination.
- `_build/lj-1.72-report.md` (repair scope). TOOK: the repair fixed
  `tagEq`/`numK` per-row and left the rest, confirmed by the probes.
- `_build/lj-1.55-report.md` / `_build/lj-1.54-report.md`: NOT read
  beyond LJ-1.71's citation of the slot fix. WHY NOT: LJ-1.71
  machine-checked that the slot convention holds at the graph frame,
  and no finding of this review touches the slot convention.
- `dev/LESSONS.md`: C-38 `:3427`, C-35 `:3200`, P-t `:2601`, P-w
  `:3094`. TOOK: the project's own names for what section 4 finds.
- `archive/rud-route/README.md`. TOOK: shape only, nothing
  mathematical (its condensation target was ruled false at
  `[LJ-1.11]`); its Bridge/StepStory generic-module shape is the
  same direction section 3c names, and nothing more was taken.

## LITERATURE USED

- `_build/literature/dev2.txt:1372-1385` (II.5.5). TOOK: the proof
  consumes condensation through the hull; the bounding substrate is
  upstream, in II.2.2-2.4 and Step C.
- `dev/literature/devlin-II5.md:209-256` (Step C). TOOK: the Σ₁/Σ₀
  split, the bounding of every unbounded quantifier by `K(u)`, the
  two-directional transfer along elementarity and collapse. This is
  the basis for section 3's verdict that the twelve-row agreement is
  the right object and both directions are necessary, and for the
  observation that Devlin's closure facts are hull-relativized where
  the tree's are absolute.
- The errata were NOT re-checked; `[LJ-1.14]` settled that section 5
  of Chapter II is not covered, and the brief forbids re-checking.

## Honest ledger: what this review did not check

- **No Agda was run.** LJ-1.76 holds the machine (live process,
  checked at review start), so every refutation in section 4 is
  INFERRED with an explicit term recipe, not MEASURED. The `tmKeyK`
  and `arityK` refutations are two-line instantiations of delivered
  lemmas; the `pairK`/`innerK` refutations need a small no-cycle
  lemma over `regularityV`. A probe (`src/ProbeMATH1.agda`, not
  written) can make all four MEASURED in one short file once the
  machine is free.
- **`envK-*` satisfiability is flagged, not settled** (section 4c):
  deciding it needs `envSetAt`'s semantics unfolded, which this
  review did not do.
- **The green runs of LJ-1.74/1.75 were not re-run**; their figures
  enter only section 5's one paragraph, as the other agents' claims.
- **`SatGraphAgree`/`LeafAgree` internal bodies** (`body-out`,
  `WitnessAgree` composition) were read only at their telescopes and
  types, not line-by-line: their vacuity finding does not depend on
  their bodies.
- **The J tower** was not surveyed beyond the DD4 findings quoted
  from LJ-1.70/71.

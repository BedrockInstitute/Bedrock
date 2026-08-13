# LJ-1.16-R: adversarial review of the refusal (DD25)

## 1. VERDICT

**OVERTURN the operative clause. UPHOLD two of the three refusals.**

The report refuses three shapes and then concludes that the block re-prices
`[LJ-1.5]`. The three refusals are mostly right. **The conclusion is wrong.**
A fourth shape exists. It never appears in the report, and no archive record
refuses it.

| item | report | this review |
|---|---|---|
| shape 1, full substitution | refused | UPHELD. The syntax has no function symbols |
| shape 2, constants-only substitution | refused, 100-160 lines | OVERTURNED as unnecessary. The needed face is DELIVERED |
| shape 3, leastness encoding | blocked, 1.0-3.0k lines | UPHELD in direction. The PRICE is wrong and the rate is untested |
| the rank argument | load-bearing | CORRECT in its conclusion, off by one in its numeral |
| "the block re-prices `[LJ-1.5]`" | asserted | **OVERTURNED** |

**THE ARITHMETIC, and it is the reason to overturn.**

- The report prices its blocked shape at 1.0 to 3.0k lines and 0.22 to 0.297
  seconds per line. That is 220 to 890 seconds, and 17 to 23 times the DD24
  bar of 0.013193.
- The fourth shape prices at **150 to 300 in-fence lines** at **0.005 to
  0.013 seconds per line**. That is **0.8 to 3.9 seconds**. It PASSES the
  DD24 bar. It takes under 4 percent of the wing's 99.6 to 147.7 second
  budget.
- The gap is 3 to 20 times in lines and 56 to 1100 times in seconds.
- Three in-tree sources already price the object the report refused at
  **210 to 430 lines**: `_build/lj-1.3-report.md:114-131`,
  `_build/lj-1.14-report.md:83-87`, `_build/lj-1.12-report.md:160-171`. The
  report cites all three and then takes 1.0-2.7k from a fourth document that
  prices a DIFFERENT object at a DIFFERENT carrier over code that now lives
  in `archive/`.

Both estimates here are ESTIMATED, not MEASURED. I ran no Agda (C-12).

## 2. THE RANK ARGUMENT, CHECKED AT THIS TREE

### 2.1 The claim is correct. The numeral is not

The report claims: `relL α` has rank α+1, `Lset α` holds sets of rank below
α, so the order element is not in the carrier.

CHECKED at the tree, in three steps.

1. **The pair is Kuratowski.** `pr a b = ⁅ ⁅ a ⁆s , ⁅ a , b ⁆ ⁆`
   (`src/V/Coding.lagda.md:175-176`). So `rank (pr a b)` is
   `max (rank a) (rank b) + 2`.
2. **`relL α` is a set of such pairs.** It is separated from a bound over the
   pairs of two members of the stage (`src/L/Choice/Table.lagda.md:783-796`,
   and the chapter says so at `:870-871`). Its members are `pr x y` for
   `x, y` in `Lset α`.
3. **Members of `Lset α` have rank below α.** The tower is
   `Lset α = ⋃ { 𝒟ₒ (Lset β) ∣ β ∈ α }`
   (`src/L/Constructible.lagda.md:215-228`), and `𝒟ₒ A` holds subsets of `A`
   (`src/L/Constructible.lagda.md:313-314`).

The arithmetic: for a LIMIT α the pairs stay below α and their ranks are
cofinal in α, so `rank (relL α)` is **α**, not α+1. For a successor α the
rank is α+1 or α+2. In every case the rank is at least α, and every member of
`Lset α` has rank below α. **So `relL α` is not a member of `Lset α`, and the
report's conclusion holds.** The numeral is wrong for the limit case, which
is the only case the hull uses (Devlin 5.2 asks for a limit ordinal).

### 2.2 The tree proves none of it, and the report says so

The report admits the gap at `_build/lj-1.16-report.md:176-178`. The
admission is correct: no lemma in `src/` states where the order element sits.
The tree HAS the instrument, `L.Rank` with `rank`, `rank-mono` and `rank-ord`
(`src/Everything.lagda.md:228-230`), so the fact is provable at a cost.
`[LJ-1.3]` priced the POSITIVE form, "the order element sits at a higher
stage", at 30 to 80 lines (`_build/lj-1.3-report.md:116-120`). That price
confirms the same fact from the other side.

### 2.3 What the rank argument does and does not buy

**It DOES kill one escape.** A reader may ask why the consumer does not put
the order element into the seed set `X`. The seed must satisfy
`X⊆L : X ⊆ Lset α` (`src/L/Hull.lagda.md:223`), and the rank fact says the
order element fails that test at its own stage. One extra seed element would
not change the counting, so this escape was worth checking, and it is closed.

**It does NOT carry the refusal.** The obstruction is not the rank. The
obstruction is the hull's INDEX TYPE.

### 2.4 The orchestrator's question answered: hull-expressible does NOT suffice

The brief asks whether the order must be X-expressible or only
hull-expressible. **The answer is that hull-expressibility does not help, and
the answer does not save the refusal.**

The reason is one line of the delivered code. The hull is
`Hull = sett (Σ[ φ ∈ Formula ⟪ X ⟫ 1 ] Witnessed-small φ) hullVal`
(`src/L/Hull.lagda.md:296-297`), and a membership certificate is literally an
X-formula with its witness: `a∈H = ∣ (φ , w) , refl ∣₁`
(`src/L/Hull.lagda.md:360-361`). So to place ANY set in the hull you must
produce an X-formula. A hull-expressible order produces a hull-formula, and a
hull-formula is not a certificate. The report's sentence "`hull-closed`'s
conclusion needs an X-formula index" is therefore CORRECT.

**But it is correct about the index type, not about the mathematics.** The
index type is a design choice made at `[LJ-1.3]`. Change the index and the
obstruction disappears. Section 4 changes it.

### 2.5 The second load-bearing claim, checked

The report says a hull member's definition is a formula, not a term, that the
syntax has no function symbols, and that full substitution cannot express the
replacement.

**Correct, and it kills shape 1.** It does not kill the criterion. The
replacement is expressible by existential binding, which is Devlin's own
move: `∃ȳ (φ(x, ȳ) ∧ ⋀ᵢ θᵢ(yᵢ))`. `_build/l3.32-t40-report.md:111-133`
records exactly that reduction. So the report reaches the right conclusion
about shape 1 by an argument that does not reach the criterion.

## 3. WHAT THE CONSUMER ACTUALLY NEEDS

### 3.1 Devlin 5.3 needs the internal order because of HIS hull, not the theorem

I read the primary text. `_build/literature/dev2.txt:1329-1356` states 5.3
with the hull as the set of UNIQUELY definable elements, and the proof forms
`ψ(v₀) = φ(v₀) ∧ ∀v₁(v₁ <_L v₀ → ¬φ(v₁))` to make the least witness the
unique witness. Devlin's own gloss at `dev2.txt:1327-1328` says the lemma is
"really a result about structures with definable wellorders".

So the internal order is a requirement of the ONE-STEP DEFINABLE HULL. The
digest states it that way at `dev/literature/devlin-II5.md:257-270` (Step D)
and books it as per-tower content at `:380`.

### 3.2 The GCH chain does NOT consume the internal order anywhere else

This is the decisive reading, and the digest states it plainly. Step F, the
5.5 step, consumes "parts (i) and (ii) of condensation only, plus the level
size equation and initial ordinal arithmetic. **No part (iii) content**"
(`dev/literature/devlin-II5.md:278-285`). Part (iii) is the only condensation
clause that needs `<_L` uniformly Σ₁ (`:287-295`). The counting at 5.4 needs
no order (`:272-276`). The collapse needs no order (`:197-207`).

**So on the GCH chain the definable well-order appears at exactly one place:
Devlin's proof of the hull.** If the hull is proved elementary by another
argument, the object drops out of the GCH wing entirely. The digest's
per-tower content then falls from two objects to one, the level-hood
certificate.

### 3.3 The meta well-order is delivered and is enough for the hull

`[LJ-1.3]` chose the meta well-order deliberately and recorded why. The
design note it adopted reads: the hull's "order is not a formula but the
delivered meta well-order `orderAt` at the carrier, with `leastOf` picking
witnesses" (`archive/rud-route/src/L/Hull.lagda.md:9-13`, taken at
`_build/lj-1.3-report.md:134-138`). In the live tree that is
`wL = orderAt α ordα` (`src/L/Hull.lagda.md:68-69`) feeding
`leastOf wL lem` (`:270`).

`leastOf` answers for EVERY formula at EVERY environment. Nothing about it is
per-formula or per-matrix. That is the property section 4 uses.

### 3.4 So the report's D-10 check is half right

The report says the corrected target does not serve the consumer
(`_build/lj-1.16-report.md:82-86`). Corrected reading: **the recorded target
needs the internal order AS THE HULL IS BUILT TODAY, and does not need it as
the theorem is stated.** The consumer needs `Elementary` at `M := Hull`. It
does not need the hull to be the definable hull, and it does not need the
hull to be smallest. `[LJ-1.12]` confirms the consumer at
`_build/lj-1.12-report.md:160-166`: the hull parameters are ordinals `γ` and
a bound `w` produced inside the hull, and elementarity at those parameters is
what the Σ₁ transfer eats.

## 4. THE FOURTH SHAPE, PRICED

### 4.1 The shape: put the term algebra in the META, not in the syntax

The report's own sentence points at the cure and then walks past it: "a hull
member's definition is a formula, not a term. The syntax has no function
symbols." **Correct. So do not put the terms in the object syntax. Put them
in the hull's index type.**

```agda
data Code : Type ℓ where
  base : ⟪ X ⟫ → Code
  wit  : (k : ℕ) → Formula (⊥* {ℓ}) (suc k) → Vec Code k → Code
```

`val : Code → SL` runs by structural recursion. `val (base m) = inStg m`.
`val (wit k ψ cs)` is the `wL`-least `a` with `(a ∷ vals cs) ⊨ ψ` when one
exists, and a junk value otherwise. Then `Hull = sett Code (λ c → fst (val c))`.

This is the Skolem hull as a term algebra. It is closed under witnesses BY
CONSTRUCTION, at hull parameters, at every arity, in ONE step. No iteration,
no leastness encoding, no internal order, no substitution operator.

### 4.2 Why the delivered tree makes it cheap

Four delivered pieces do most of the work.

1. **`absFo` and `⊨-abs` move constants into the environment.**
   `absFo : (φ : Formula K n) → Formula (⊥* {ℓz}) (n + countFo φ)`
   (`src/FOL/Manipulation/Parameters.lagda.md:260-261`), with
   `⊨-abs : (γ ⊨ φ) ≡ ((γ ++ map ι (constantsFo φ)) ⊨₀ absFo φ)`
   (`:421-429`). This is EXACTLY the shape `wit` wants: a parameter-free
   formula plus an environment. **The report priced the INVERSE of this
   module and never checked the forward face.** The forward face is the one
   that is needed, and it is already green.
2. **`⊨-map` transfers satisfaction across a change of constant domain**
   (`src/FOL/Manipulation/Relabelling.lagda.md:154-168`), fourteen clauses,
   delivered and generic.
3. **The tree's `fiber` returns an UNTRUNCATED index** from a membership:
   `fiber : (a : S) {x : S} → ⟨ x ∈ˢ a ⟩ → Σ[ m ∈ ⟪ a ⟫ ] (⟪ a ⟫↪ m ≡ x)`
   (`src/V/Presentation.lagda.md:34-35`, wrapping the library's
   `∈-asFiber` at
   `Cubical/HITs/CumulativeHierarchy/Properties.agda:242-247`). It is
   untruncated because the presentation is monic. The hull already uses it
   at `src/L/Hull.lagda.md:258` and `:318`. So a hull member yields its
   `Code` with no truncation problem.
4. **`lem` already sits at the right level.** `Witnessed φ : Type (ℓ-suc ℓ)`
   (`src/L/Hull.lagda.md:245-246`) and the module carries
   `lem : LEM (ℓ-suc ℓ)` (`:10`). So the junk-value split is available with
   no lifting.

**Why the junk value matters.** It keeps the witness proof OUT of the index.
That makes `Code` a plain inductive type instead of an inductive-recursive
one, so nothing new is asked of Agda. `Code : Type ℓ` because
`Formula (⊥* {ℓ}) n : Type ℓ` and `⟪ X ⟫ : Type ℓ`, so `sett` accepts it.
`Code` occurs only under `Vec`, so strict positivity holds.

### 4.3 The price

**150 to 300 in-fence lines.** ONE number, and its basis (DD8):

- The delivered index-and-search block is `src/L/Hull.lagda.md:239-363`,
  about 100 in-fence lines of the file's 372 (counted at the ledger caliber).
  The term algebra REPLACES that block.
- `absFo` and `⊨-abs` are delivered, so shape 2's 100-160 lines fall away
  entirely.
- `⊨-map` is delivered, so the relabelling proof falls away.
- The one genuinely new proof is the n-ary closure theorem. Its comparable is
  `hull-closed` plus `XInM` at about 45 in-fence lines
  (`src/L/Hull.lagda.md:317-363`), doubled for the arity and the code
  bookkeeping.

**0.005 to 0.013 seconds per line.** Basis: the report's OWN two cold
measurements, `L.Hull` at 0.0071 and `FOL.Manipulation.Parameters` at 0.0054
(`_build/lj-1.16-report.md:98-101`). The shape states no formula at a
concrete carrier and builds no satisfaction table, so P-n's floor does not
apply to it.

**0.8 to 3.9 seconds.** Under DD24's 0.013193 bar. Under 4 percent of the
wing's 99.6 to 147.7 second budget.

### 4.4 What the shape gives up, and whether the consumer minds

It gives up two clauses of Devlin 5.3.

- **"M is the definable hull."** Not consumed. 5.5 uses only `M ≺ L_λ`,
  `L_α ∪ {x} ⊆ M` and `|M| = |L_α|` (`dev2.txt:1372-1384`).
- **"M is the smallest."** Not consumed by 5.5 either. `[L3.32-T40]` books
  smallestness as a SEPARATE residue (`_build/l3.32-t40-report.md:135-146`),
  so dropping it costs nothing that the GCH chain owes.

The counting at 5.4 survives in the same SHAPE. Devlin counts `|ℒ_X|`
formulas (`dev2.txt:1357-1360`); the term algebra counts `Code`, an inductive
type over `⟪ X ⟫` plus countable data. Both are `max(|X|, ω)`.

**A sibling is building that counting kit RIGHT NOW, and its decomposition is
the fourth shape's own payload.** `src/FOL/Count.lagda.md` and
`src/L/StageCardinal.lagda.md` are untracked in the working tree and another
agent holds them. I read them and did not touch them. `FOL.Count` delivers
`code : Formula (⊥* {ℓ}) k → ℕ` with `code-inj` (`:81-93`, `:171-202`),
`shape-count-inj` (`:211-213`), and this line:

```agda
encode : Formula K 1 → Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) k × Vec K k)
```

(`src/FOL/Count.lagda.md:654`). That triple, an arity, a parameter-free
formula and a vector of constants, **is exactly `wit`'s payload**. So the kit
is aligned with the fourth shape rather than against it.

**The honest cost, stated once.** Counting a recursive term algebra needs an
induction on term height and then one countable union. Counting the
ω-iterated hull of variant A needs an induction on the stage and then one
countable union. **Neither variant escapes that step**, and the one-step hull
does escape it. That is the fourth shape's real downstream price, and
`[LJ-1.5]` or `[LJ-1.7]` pays it. I did not price it.

### 4.5 Why this is NOT what `[L3.32-T5]` refused

`[L3.32-T5]` refused an iterated hull, and the refusal is real, but it is
about a different instrument. Its reason: `ClosedFor` is per-matrix,
`Single`'s ladder is per-matrix, and `ReflectFo`'s ladder is per-formula, so
"closure is not inherited by larger stages"
(`_build/l3.32-t5-report.md:135-151`, quoting `src/L/ReflectFo.lagda.md:7-10`).

**The fourth shape uses no reflection.** It uses `leastOf` over the meta
well-order, which answers for every formula at every environment and inherits
upward by construction. The residue register confirms the piece was never
priced: "No simultaneous closure form exists; its only recorded consumer (the
iterated-Skolem hull) was replaced by the direct definable-hull (T40) ...
0 / 0 (never priced)" (`_build/l3.32-t49-report.md:53`).

**So the fourth shape is unpriced, not refused.**

### 4.6 The conservative fallback, variant A

If the term algebra fails a check, iterate the DELIVERED module instead.
`module Hull` is already parameterized by `(X , X⊆L)`
(`src/L/Hull.lagda.md:223`) and already returns `Hull` and `Hull⊆L`
(`:296-304`), so `Hₙ₊₁ = Hull Hₙ` is a recursion on `ℕ` over delivered code,
and `X⊆M` (`:347-348`) gives the monotonicity for free. `H_ω` is the union.
The extra cost is a factorization lemma, "the finitely many constants of one
formula live at one finite stage", proved into a truncation because the goal
is truncated. ESTIMATE 250 to 450 lines, and it moves a countable-union step
onto `[LJ-1.5]`'s counting. Variant A changes no delivered line. Variant B is
cheaper and cleaner. Probe B first.

### 4.7 The risks, all cheap to probe

1. Termination of `val` through `Vec Code k`. Standard, unchecked here.
2. The generalized search must keep the seal. The delivered `leastSearch` is
   `opaque` for measured reasons (`src/L/Hull.lagda.md:265-277`).
3. `module Hull` sits INSIDE `module AtM` (`src/L/Hull.lagda.md:73` against
   `:223`) although it uses nothing of `AtM`. An instantiation must pass a
   dummy `M`. This is a wiring defect, not a blocker. Fix it in the same
   block.
4. The junk value needs `∅ ∈ˢ Lset α`, which holds at every limit stage.

**Probe it (D-1).** Build `Code`, `val`, `Hull` and close the arity-one case
at hull parameters. Stop-line 120 lines. Throw it away.

## 5. THE ARCHIVE EVIDENCE, VERIFIED

Six of the report's eight cites are line-accurate and fairly used. **The
load-bearing one is not.**

### 5.1 The 1.0-2.7k cite prices a different object

`_build/l3.32-t48-report.md:236-238` reads "**1.0-2.7k naive / 3.0-7.9k
calibrated**, every unmeasured row still ×3". Verified. What it prices:

- The **face route only**, one of four routes T48 prices (`:132`, `:208`).
- The order formula written by the **sequence-witness flattening** of
  SZ 1.11(2), not a direct order formula (`:177-206`).
- Mostly at the **S-tower**, the retired carrier. The cost table row at
  `:223` reads "level-membership relation + decode (L-tower, rud/S-tower) |
  200-450 | ×3 | 600-1,350", and the adequacy target is the rud order
  `Sset-below` (`:197-198`).
- **A ×3 projection, not a build** (`:36-37`, `:219-228`).
- Over code that is now archived. `src/L/OrderFormula.lagda.md` and
  `src/L/Rud/` do not exist; both live under `archive/rud-route/`.

The report also **widened the band**. Its source says 2.7k; its own
arithmetic uses 3.0k (`_build/lj-1.16-report.md:57-58`).

The report omits three things the same document says: T48's own 400-line gate
(`:405-415`), its "cheapest decision the owner can make" scope ruling
(`:419-423`), and its headline "the cheapest route is not the one the
recorded verdict implies" (`:3-4`).

### 5.2 The tree's own price for the same object is 3 to 9 times lower

- `_build/l3.32-t40-report.md:119-120`: `σ_<` at the carrier, **0.30-0.70k
  unprobed**.
- `_build/l3.32-t44-report.md:172`: the carrier relocation, **0.30-0.70k
  unprobed**.
- `_build/lj-1.3-report.md:114-131`: the three pieces, **210 to 430** lines,
  and the sum is exact.
- `_build/lj-1.14-report.md:83-87` and `_build/lj-1.12-report.md:167-171`
  repeat 210 to 430.

So the report imported the highest number in the corpus from the least
relevant document, and did not report the four lower ones it had read.

### 5.3 The T44 and T40 cites are accurate

`_build/l3.32-t44-report.md:165-176` names three gaps and the report takes
two of them correctly. `_build/l3.32-t40-report.md:111-133` names two
residues and the report takes the first correctly. The report also correctly
records that T40's second obstruction is outdated
(`_build/lj-1.16-report.md:122-125`).

### 5.4 The JOURNAL cite is stretched

`archive/dev/JOURNAL-archived.md:3985-3990` is the `[L2.4]` route audit of
2026-07-29. The clause "parameters enter as an environment rather than by
substitution" is one item in a list of what THAT route does not need. It is
not a ruling against a substitution operator. `[L2.4]` is the AC-side
internalization whose code is LIVE in `src/L/Choice/`, so calling it "the
retired route" is wrong. The report's own better citation,
`src/FOL/Manipulation/Renaming.lagda.md:8-18`, carries the point without the
borrowed authority.

### 5.5 The report contradicts its own source on DD4

`_build/lj-1.12-report.md:167-171` classes the bridge as **template content**:
"the J tower's condensation consumes the same hull elementarity". The report's
section 6 argues the opposite without naming the disagreement.

### 5.6 Does the retired route's obstruction transfer

**Partly, and less than the report says.** What transfers: the internal order
formula at a variable carrier is genuinely absent, and both T40 and T44 say
so. What does NOT transfer: the price, the carrier, and the machinery. The
current order comes from `L.Choice`, which survived
(`src/L/Hull.lagda.md:32`, `src/L/Choice/Table.lagda.md:795-796`), while
T48's face route rests on modules that did not. **A price measured on one
tower's machinery is a hypothesis on another's** (P-l).

## 6. THE BRIEF'S SHARE

**The brief foreclosed the fourth shape. Four mechanisms, in order of
force.**

1. **It pointed shape 2 at the wrong face of a delivered module.**
   `_build/briefs/LJ-1.16.md:46-47` says "`FOL.Manipulation.Parameters`
   already moves constants into environments and back; read it before
   pricing, because **the inverse** may be most of this". The FORWARD face,
   `absFo` and `⊨-abs`, is the answer, and it is already green. The agent
   read the module and priced the inverse, as instructed.
2. **It named the refusal as a reward.** `:53` reads "If all three price
   above 430, say so; that re-prices `[LJ-1.5]` and is a full deliverable".
   A brief that names a refusal as a full deliverable, and offers a specific
   downstream consequence for it, is offering a shortcut.
3. **It pre-computed the refusal's headline number.** `:65-69` says a shape
   that forces a concrete carrier "would blow the bar about seventeen times".
   The return reports 17 to 23 times. That is anchoring, not measurement.
4. **It framed the gap as a missing SYNTAX capability.** `:30-35`, "the
   bridge is not a lemma, it is a missing capability", points every shape at
   the syntax layer. The cure is at the index-type layer, one level up.

The `RETURN` block then asks for "THE THREE PRICES" (`:192`), so the report
template had exactly three slots. "Price at least these three shapes"
(`:40`) invited more, but nothing in the return format had a place to put a
fourth.

**Credit to the agent.** It flagged the rank claim as unproven
(`_build/lj-1.16-report.md:176-178`) and it flagged the birth-decomposition
order as an unprobed alternative (`:183-186`). Both flags were right, and the
second is the standard route to the internal order.

## 7. DD4: ONE TOWER OR BOTH

**The obstruction hits BOTH towers, and the fourth shape removes it from both
at once.**

- Under shape 3 both towers pay. The digest books the definable well-order as
  per-tower content that BOTH towers carry, the Def tower's `<_L` from
  satisfaction and the J tower's `<^A` from producer triples
  (`dev/literature/devlin-II5.md:380`). So the leastness route buys a
  per-tower object twice.
- Under the fourth shape neither tower pays. The term algebra needs only a
  META well-order at the carrier. Both towers have one. The construction is
  generic in `X` and in the carrier, so it is TEMPLATE content.
- That agrees with `_build/lj-1.12-report.md:167-171`, which already classed
  the bridge as template content, and it disagrees with the report's section
  6.

**So this piece gives no evidence for or against DD2's architecture.** The
brief asked whether the block hits only the Def tower. It does not. The
honest DD4 finding is stronger and different: **the fourth shape converts a
twice-paid per-tower object into one shared construction, and it also removes
`[LJ-1.3]`'s booked residue piece one, the order element's stage membership,
worth 30 to 80 lines** (`_build/lj-1.3-report.md:116-120`).

## 8. WHAT THE ORCHESTRATOR SHOULD DO NEXT

1. **Do not re-price `[LJ-1.5]` on this return.** Correct the PLAN section 11
   row for `[LJ-1.16]`. The rank sentence in that row is true but is not the
   binding constraint, and the numeral is wrong for the limit case.
2. **Stop the 1.0-2.7k figure before it propagates.** It prices the
   sequence-witness flattening at the S-tower over archived code. Record in
   `dev/JOURNAL.md` that three in-tree sources price this object at 210 to
   430.
3. **Ask the owner for the design ruling.** The hull's index type changes.
   That is an architecture fork under `AGENTS.md` "Ask first". Recommend
   variant B with variant A as the fallback.
4. **Dispatch a D-1 probe, codex tier.** Build `Code`, `val`, `Hull` and
   close the arity-one case at hull parameters. Stop-line 120 lines. The
   gate: does the closure at hull parameters typecheck without any internal
   order. Throw the probe away.
5. **On GREEN, dispatch the rebuild at 150 to 300 lines.** Brief it at the
   forward face of `FOL.Manipulation.Parameters`, not the inverse. Name
   `absFo`, `⊨-abs`, `⊨-map` and `∈-asFiber` as the delivered inputs.
6. **On RED, fall back to variant A**, the iteration of the delivered
   module, at 250 to 450 lines.
7. **Keep shape 1 refused.** Do not fund a substitution operator. That
   refusal is correct and it should be recorded as settled.
8. **Fix the brief template.** A brief that lists N shapes should ask for
   N+1 and should say that the missing shape is the deliverable. This is the
   second DD25 review to find a cure the brief's own framing hid.
9. **Re-check the wing's per-tower content count.** If the hull stops needing
   the definable well-order, then on the GCH chain the per-tower content
   falls from two objects to one. That changes `[LJ-1.12]`'s crossing
   arithmetic and possibly `[LJ-1.1]`'s wing projection.
10. **Sequence this against the sibling holding `src/FOL/Count.lagda.md`.**
    That agent is building the counting kit, and its `encode` at `:654`
    already returns the fourth shape's payload. Land that block first. Then
    brief the hull rebuild to REUSE `code`, `code-inj` and `encode` rather
    than to write a second counting.

## 9. LITERATURE USED

- `dev/literature/devlin-II5.md`, read in full. Took section 1.3 (`:118-132`,
  5.3's statement and the leastness formula), section 2.4 (`:257-270`, Step D
  and the uniformly Δ₁ requirement), **section 2.6 (`:278-285`, Step F, which
  is the decisive line: 5.5 consumes condensation parts (i) and (ii) only)**,
  section 2.5 (`:272-276`, the counting), section 4 (`:370-394`, the
  per-tower table), and section 6.3 (`:454-460`, the OCR restoration of the
  leastness formula).
- `_build/literature/dev2.txt:1320-1362`, read directly. Took 5.3's statement
  ("a is the unique element"), Devlin's gloss that the lemma is "really a
  result about structures with definable wellorders", the leastness formula,
  and 5.4's counting proof. **This is the primary check that the internal
  order belongs to Devlin's HULL and not to the GCH chain.**
- `dev/literature/devlin-errata.md`. NOT read. WHY NOT: `[LJ-1.14]` verified
  it does not cover Chapter II section 5
  (`_build/lj-1.14-report.md:107-108`), and the brief carried that
  verification forward. Nothing in this review turns on a book erratum.
- `dev/literature/j-hierarchy.md`. NOT read. WHY NOT: the J tower's order
  enters this review only through the digest's per-tower table
  (`devlin-II5.md:380`), and the review's DD4 finding does not depend on the
  J order's shape.

## 10. ARCHIVE USED

- `_build/lj-1.14-report.md:77-87` (section 6) and `:89-108` (section 7). Took
  the commissioning residue and the 210-430 price.
- `_build/lj-1.3-report.md:114-131` and `:134-138`. Took the three pieces and
  the META well-order decision with its reason.
- `_build/lj-1.12-report.md:160-171` (section 5). Took the consumer's
  parameters and the TEMPLATE classification.
- `_build/l3.32-t40-report.md:111-146`. Took the two residues, the
  existential-binding reduction, and the 0.30-0.70k price.
- `_build/l3.32-t44-report.md:165-176`. Took the three gaps and the
  0.30-0.70k relocation price.
- `_build/l3.32-t48-report.md:3-4`, `:36-37`, `:132`, `:177-208`, `:219-238`,
  `:405-423`. Took the face route's scope, its carrier, its projection class,
  its gate and its scope ruling.
- `_build/l3.32-t5-report.md:15-18` and `:135-151`. Took the refusal of the
  iterated REFLECTION hull and its stated reason.
- `_build/l3.32-t49-report.md:53`. Took "0 / 0 (never priced)" for the
  iterated hull.
- `archive/dev/JOURNAL-archived.md:3981-3990`. Took the `[L2.4]` route audit
  and its date.
- `archive/rud-route/src/L/Hull.lagda.md:9-13` and `:418-431`. Took the
  meta-well-order design note and the two consequences with the `σ_<`
  residual.
- `dev/LESSONS.md`: P-n (the measurement is an INSTANTIATION at a concrete
  stage, and its admissible move is "keep content parameterized"), P-l, P-m,
  D-10, D-26.

## 11. WHAT I AM NOT SURE OF

1. **My 150-300 figure is an estimate from reading, not a measurement.** I
   ran no Agda (C-12). Probe it before funding it. The probe is 120 lines.
2. **Termination and positivity of `Code` and `val` are unchecked.** I argue
   them on the types. `Formula (⊥* {ℓ}) n` and `⟪ X ⟫` are both `Type ℓ`, and
   `Code` appears only under `Vec`. Agda decides, not I.
3. **The counting claim is same-shape, not free.** `|Code| = max(|X|, ω)`
   holds mathematically. Both variants add one countable union at the
   counting site and the delivered one-step hull does not. I did not price
   that step. I also read `src/FOL/Count.lagda.md` while a sibling was
   writing it, so its content may move under me.
4. **The report's 0.22 to 0.297 rate for shape 3 is a transfer by analogy,
   and I did not test it either.** P-n was measured on an INSTANTIATION at a
   CONCRETE stage. The hull's carrier is a module parameter. So the rate may
   be lower than the report says. This cuts against the report, not for it,
   and it does not change my verdict, because the fourth shape makes shape 3
   moot.
5. **I did not price the smallestness clause under the fourth shape.** I
   claim only that the GCH chain does not consume it.
6. **Variant A's factorization lemma is the piece I am least sure of.** It
   needs the constants of one formula to sit at one finite stage, proved into
   a truncation. I believe the goal is truncated at every use, but I checked
   only `TarskiVaught`'s conclusion (`src/L/Hull.lagda.md:88-91`).

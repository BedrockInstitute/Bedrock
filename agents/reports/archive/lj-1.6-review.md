# LJ-1.6-R: adversarial review of the LJ-1.6 return (DD25)

Reviewer: in-harness Opus subagent, maximum effort. Read-only on `src/`. No
Agda was run. No commit was made.

## 1. VERDICT

**UPHOLD THE STOP. OVERTURN THE REASON AND THE PRICE.**

The mathematical observation is CORRECT. A `sett`'s carrier is the quotient of
its index by the kernel of the embedding. `⟪ 𝒟 A ⟫` really is
`Formula ⟪ A ⟫ 1 / Kernel`. The counting map really does not factor through
that quotient. The report is right about the tree.

Everything the report builds on that observation is wrong.

1. **The finding is not new.** `[L3.32-T85]` found the same quotient on
   2026-08-05, verified it under D-10, and CURED it. The cure is GREEN in this
   working tree at `src/ProbeTowerInd2.agda`.
2. **The price is wrong by 2x to 3x.** The report prices a fresh
   canonical-name descent at 250 to 450 lines, plus a 200 to 350 line assembly.
   `[L3.32-T85]` MEASURED the successor half, descent included, at **52
   non-blank lines**, GREEN, 12.8 s whole-file cold. It priced the limit half
   at 150 to 220.
3. **The report asks for the wrong object.** It asks for a canonical NAME. The
   delivered route takes the least VALUE in the class. No naming theory is
   needed. `leastOf` over the ordinal's own well-order does the whole job.
4. **The square-law line figure is wrong by 257 lines.** The report says 1,540
   in-fence. The true in-fence sum is **1,283**. The report added `SquareLaw`'s
   in-fence 907 to `Pairing`'s FILE count 633, whose in-fence is 376.
5. **The square-law seconds figure is stale by two supersessions.** The report
   quotes 61.9 s. The 2026-08-09 cold profile measures `SquareLaw` at **23.3 s**
   and calls the older figure "STALE BY 41 s".

**THE BIGGEST FINDING IS NOT THE REFUSAL. IT IS DD24.** Even at the newest and
lowest measured figures the square law puts the wing OVER the bar. See section
3 for the arithmetic. Nobody has said this anywhere.

The row's target `|L α| = |α|` is CORRECT and the chain consumes it at the
CARRIER level. The report's own uncertainty item 2 closes NEGATIVE: no
index-level re-route exists. See section 4.

**What the stop was right about:** the square law is a genuine missing
dependency and this dispatch could not supply it. Stopping there was correct.
The line of work must NOT close.

### The arithmetic, in one place

| quantity | report | corrected | source |
|---|---:|---:|---|
| square-law port, in-fence | 1,540 | **1,283** | measured, section 3 |
| `SquareLaw` cold seconds | 61.9 | **23.3** | `dev/ledger.toml:1765` |
| `Pairing` cold seconds | not given | **18.6** | `dev/ledger.toml:1769` |
| descent, lines | 250-450 | **52 measured** | `_build/l3.32-t85-report.md:108` |
| descent plus assembly | 450-800 | **~220-290** | T85 :108, :245 |
| corrected port total | 2,784-3,134 | **2,300-2,900** | this review |

The corrected total spans two readings. Fix the caliber alone and it is
794 + 1,283 + 450 to 800 = **2,527 to 2,877**. Add the T85 comparable and it is
794 + 1,283 + 220 to 290 = **2,297 to 2,367**. Re-measure at this site per P-l.

## 2. THE QUOTIENT ARGUMENT

### 2.1 The claim is true, and here is the exact line

`Def A = sett (Formula ⟪ A ⟫ 1) defSet` (`src/L/Definability.lagda.md:115`).
The library sends every `sett X ix` to a monic presentation whose carrier is
`Rep = X / Kernel`, with `Kernel x y = ix x ≊ ix y`
(`/opt/homebrew/Cellar/agda/2.8.0-r3/share/agda/cubical/Cubical/HITs/CumulativeHierarchy/Properties.agda:146-153`).
`MonicPresentation` is a proposition (same file, :130), so the carrier is
determined. `⟪_⟫` reads it off (same file, :220-224).

So `⟪ Def A ⟫` IS the quotient of the formulas by "defines the same subset".
Two formulas that carve one subset are identified. The report is right.

The stage adds one more layer. `Lset α = ⋃ (sett ⟪ α ⟫ (λ m → 𝒟ₒ (Lset (⟪ α ⟫↪ m))))`
(`src/L/Constructible.lagda.md:216`). The union carries its own presentation.
So `⟪ Lset α ⟫` is a quotient of a dependent sum over stage and formula, as
the report says.

**Is the carrier a fiberwise construction where the bound survives?** No. The
carrier is equivalent to the image of the index map, hence to
`Σ[ x ∈ S ] ⟨ x ∈ˢ Lset α ⟩`. A count of names does not descend to it by
post-composition. The report's sentence "the count-bound does not factor
through it" is exactly right.

### 2.2 The conclusion drawn from it is wrong

An injection out of a quotient needs a representative. The report concludes
that a canonical NAME must be chosen, and prices a naming theory. That is the
wrong cure.

**The right cure takes the least VALUE, not the least name.** Let
`c : Formula ⟪ Lset α ⟫ 1 ↪ ⟪ α ⟫` be the counting bound. For a member `m` of
the next stage, define the predicate on `y : ⟪ α ⟫`:

> some formula `φ` defines `m`, and `c φ ≡ y`.

The predicate is merely inhabited by `𝒟ₒ-inv`. `⟪ α ⟫` carries a strict
well-order. `leastOf` returns the least such `y`, uniquely
(`src/L/WellOrder/Base.lagda.md:158-161`, with `isPropLeastOf` at :136-144).
Injectivity uses only injectivity of `c` and of the presentation embedding.
**No formula is ever canonicalized. No quotient eliminator is ever used.**

### 2.3 This tree already did it, and measured it

`src/ProbeTowerInd2.agda` is an untracked probe in this working tree. It
contains:

- `D10-good` (:61-63): the quotient identity, checked as `refl`. It is the same
  finding the report reports.
- `lower-inj` (:70-94): `⟪ α ⟫ ↪ ⟪ Lset α ⟫`, the lower half, 18 lines.
- `module Successor` (:99-149): `class-pred`, `nonempty`, `h`, `h-inj`. This IS
  the descent, by `leastOf (ordSWO α oα)`.
- `successor-step` (:155-159): `⟪ Lset α ⟫ ↪ ⟪ α ⟫` implies
  `⟪ Lset (sucV α) ⟫ ↪ ⟪ α ⟫`.

Its report, `_build/l3.32-t85-report.md`, records the measurement:

- The successor step, descent included, is **52 non-blank lines** (:108).
- The whole probe checked GREEN at **12.8 s wall cold, 2.6 s warm**, one
  process, `GHCRTS=-M8g` (:186-191).
- The limit half was NOT built. Its honest route is priced at **150 to 220
  naive lines**, with the transport-stability lemma named as the widest
  unmeasured term (:245-247).

So the report's sentence "The archive never faced this" is FALSE, and the
correction is on the record the brief told the agent to read.
`archive/dev/TASKS-archived.md:120` carries the row:
`| L3.32-T85 | Re-design the tower-induction gate | GREEN (gate re-design) |`.

**One honest qualification.** The probe imports `L.CardinalCount`,
`L.Ordinal.SquareLaw` and `L.Ordinal.Pairing`, which are now archived. The
probe does not compile against today's tree. P-l forbids transferring a
measured cure by analogy. So 52 lines is a MEASURED COMPARABLE on a comparable
tree, not a price for today. It is far better evidence than an unanchored 250
to 450, and `[LJ-1.6]` has just re-delivered the `Bound` half as
`L.StageCardinal.Bound`, which is the probe's main ingredient.

### 2.4 The live tree holds more of it than the report saw

The report never read `src/L/Choice/` or `src/L/WellOrder/`. Both are wired in
`src/Everything.lagda.md:321, :354-364`. They hold:

- `leastOf`, the generic least-element search over any `SWO`
  (`src/L/WellOrder/Base.lagda.md:158-161`).
- `stageOrder : (γ : S) → IsOrd γ → SWO ⟪ Lset γ ⟫`, an unconditional
  well-order of every stage's carrier (`src/L/Choice/Step.lagda.md:748`).
- `pullOrder`, a well-order pulled back along an injection
  (`src/L/Choice/Step.lagda.md:252`).
- `birth`, the ordinal a set was carved over, with
  `birth-in : ⟨ x ∈ˢ Lset γ ⟩ → ⟨ birth x ∈ˢ γ ⟩`
  (`src/L/Choice/Step.lagda.md:133, :189`).
- `names-complete` and `leastName`, a name for every member of a successor
  stage and the least name of a family
  (`src/L/Choice/Name.lagda.md:441-447, :812-814`).

The report says the descent goes "through the delivered well-order of a
stage", and then prices the well-order as an unpriced heavy risk in its
uncertainty item 1. That is backwards. The well-order is delivered, green and
wired. The `leastOf` route does not even need it: the ordinal's own order
suffices, which is what T85 used.

### 2.5 Does the upper half really need a descent at all?

Yes, somewhere, but only once and only at an ordinal.

The whole induction can run on SURJECTIONS. A surjection `⟪ α ⟫ ↠ ⟪ Lset α ⟫`
composes through the name sum without any representative choice. The descent
becomes necessary only when an ORDINAL must be bounded, because the final
conclusion of Devlin 5.5 is `γ < κ`. A surjection onto a well-ordered target
converts to an injection by least preimage. That is one generic lemma.

So the descent is not removable. It is only movable. T85 put it at the stage,
where it costs 52 lines. Moving it into the hull argument does not make it
cheaper.

### 2.6 DD4 judgment on the descent

The descent is TEMPLATE content, not L content. Its ingredients are `leastOf`
over an arbitrary `SWO`, a counting injection, and the step operator's
membership characterization. Only the last is per-tower, and each tower owns
its own step operator by definition.

So the refusal's DD4 worry does not hold. The upper half does NOT force
L-specific content into shared code.

## 3. THE SQUARE LAW

### 3.1 Necessity: REQUIRED, and the report is right

`|L_α| = |α|` at every infinite α needs `|α × α| = |α|` at every infinite α.
The successor step counts formulas with parameters from the stage below. It
packs a shape and a parameter tuple into one ordinal. That is the pairing.
The limit step packs a stage and a name. That is the pairing again.

The delivered `L.StageCardinal.Bound` takes `pair` and `pair-inj` as MODULE
PARAMETERS (`src/L/StageCardinal.lagda.md:51-58`). So the square law is a
hypothesis today and a debt tomorrow. Nothing weaker in the tree discharges it.
I found no cheaper route in `dev/literature/devlin-II5.md` sections 1.4, 1.5 or
5.2. Section 2.5 confirms the strength as "cardinal arithmetic on a countable
formula set with parameters from X".

### 3.2 A gap NEITHER the report NOR the recon names

The archived square law holds at INITIAL ordinals only. The archive says so in
its own prose:

> It does not give the law at the non-initial ordinals such as `ω + ω`: the
> reduction of such a site to its cardinal is the least-of transfer, which is
> the counting's own plumbing.
> (`archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md:956-963`)

`Init α` also demands `ω ∈ˢ α` (`sq` and `Init` at :970-978), so `Init ω` is
uninhabited. `[L3.32-T59]` died on exactly that, and
`src/ProbeTowerInd2.agda:49-50` proves it.

The GCH chain needs the level size at ARBITRARY infinite α and γ, not at
initial ordinals only (`dev/literature/devlin-II5.md:153-158`). So a
non-initial transfer is owed. `_build/lj-1.1-recon.md:143` prices block 4d at
the archived shape and does not name this gap. The report does not name it
either. **Price it before funding the square law.**

Credit where it is due: the report's own change to `Bound`, taking the numeral
source from trichotomy against ω instead of from `ω ∈ˢ β`, removes the ω
obstruction at the counting end. That is a real improvement over the archive.

### 3.3 DD24: the square law breaks the bar. This is the biggest finding.

**MEASURED, by me, at the ledger caliber (non-blank lines inside agda fences):**

| file | in-fence | file lines |
|---|---:|---:|
| `archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md` | 907 | 1,299 |
| `archive/rud-route/src/L/Ordinal/Pairing.lagda.md` | **376** | 633 |
| `archive/rud-route/src/FOL/Count.lagda.md` | 588 | 917 |
| `src/L/Count.lagda.md` | 620 | 708 |
| `src/L/StageCardinal.lagda.md` | 174 | 205 |

**THE REPORT'S 1,540 IS A CALIBER ERROR.** It reads
`_build/lj-1.1-recon.md:251`. That line opens with "`Pairing.lagda.md` (633
lines): ADAPTABLE" and closes with "In-fence 376". The report took the opening
number, 633. The correct in-fence sum is
907 + 376 = **1,283**. The overstatement is 257 lines, or 20 percent. The
brief ordered the ledger caliber and forbade counting by hand.

**MEASURED seconds, and the report's figure is stale.**
`dev/ledger.toml:1755-1769` records the 2026-08-09 full per-module cold
profile, the first complete distribution since 2026-08-06:

> `L.Ordinal.SquareLaw   64.4 ->  23.3   ([T103], 2026-08-06, STALE BY 41 s)`
> `L.Ordinal.Pairing 18.6` (among "five masters that were on nobody's list")

The report quotes 61.9 s, which is the same stale generation as 64.4. The
current pair is **23.3 + 18.6 = 41.9 s over 1,283 in-fence lines**, a rate of
**0.0327 s per line**, which is **2.48x** DD24's bar of 0.013193.

**THE WING ARITHMETIC.** The declared wing is
`dev/ledger.toml:2764-2768`: `V/Collapse` 239, `L/Hull` 343, `V/Presentation`
18, so 600 lines. The brief states the aggregate at 0.0065, so about 3.90 s.
ESTIMATED where marked.

| scenario | lines | seconds | s/line | against 0.013193 |
|---|---:|---:|---:|---|
| wing today | 600 | 3.90 (given) | 0.0065 | 0.49x, PASS |
| plus the delivered half | 1,394 | 5.46 | **0.0039** | 0.30x, PASS |
| plus square law at 41.9 s | 2,677 | 47.36 | **0.0177** | **1.34x, FAIL** |
| plus square law at 80.5 s (report's figures) | 2,677 | 85.96 | **0.0321** | **2.43x, FAIL** |

**A cleaner framing, and the one to give the owner.** DD24's bar over the
wing's a-priori line band `gch_wing_apriori = [7553, 11197]`
(`dev/ledger.toml:241`) sets the wing's TOTAL seconds budget at **99.6 s to
147.7 s**. The square law pair at 41.9 s consumes **28 to 42 percent of the
whole wing's seconds budget** for **11 to 17 percent of its lines**. At the
report's stale figures it consumes 55 to 81 percent.

**Two caliber warnings, because a wrong number here is worse than none.**

1. The 23.3 and 18.6 figures come from `--profile=modules` on one whole-tree
   cold run at `GHCRTS=-M8g`, on the RETIRED tree
   (`dev/ledger.toml:1755-1760`). DD24's per-module caliber is a cold module
   build with warm dependencies at `-A64m -I0 -M16g` (ratio section of
   `dev/ledger.toml`). The ledger records the slice sum at 1.45x the cone. So
   the DD24 figure is likely HIGHER than 41.9 s, not lower.
2. P-l (`dev/LESSONS.md:2264`) and P-s (:2528) both forbid transferring these
   figures. The number above is a GATE, not a decision.

**The report DID flag the DD24 risk, and deserves credit for it.** Section 2
names the risk and gives a rate. It used the wrong denominator and a stale
numerator, and it did not carry the risk into the wing aggregate. The
aggregate is where DD24 bites.

## 4. INDEX-LEVEL OR CARRIER-LEVEL FOR `[LJ-1.7]`

**CARRIER-LEVEL. Close the report's uncertainty item 2 NEGATIVE.**

Devlin 5.5 (`dev/literature/devlin-II5.md:147-158`, source at
`_build/literature/dev2.txt:1369-1384`) consumes the level size TWICE, in
opposite directions:

1. **Upper half at α.** 5.4 gives `|M| = max(|X|, ω)` with `X = L_α ∪ {x}`.
   The hull's parameter domain IS the carrier of `L_α`. To get `|M| < κ` you
   need `⟪ Lset α ⟫ ↪ ⟪ α ⟫`. This is carrier-level and it is the half the
   report refused.
2. **Lower half at γ.** The chain reads `|γ| = |L_γ| = |M| = |α| < κ` and
   concludes `γ < κ`. The step `|γ| ≤ |L_γ|` is `⟪ γ ⟫ ↪ ⟪ Lset γ ⟫`. **The
   report DELIVERED this half** as `Lower.ord-inj`
   (`src/L/StageCardinal.lagda.md:178-203`).

An index-level bound gives only a surjection onto the carrier. The final
conclusion is about an ORDINAL, γ. A surjection onto a well-ordered target
becomes an injection only by least preimage, which is the descent again. So
the descent cannot be routed away. It can only be moved into the hull
argument, where it is not cheaper.

**The archive gives no precedent, and the premise that it does is false.** The
retired route NEVER proved GCH. `dev/ledger.toml:218` states it directly:
"route never proved GCH. Phase 1 BUILDS that wing". The archive stopped at
5.4's hull bound. So this question has no archive answer and must be settled
from the literature, which answers CARRIER.

`dev/literature/devlin-II5.md:411-417` (section 5.2) agrees. It calls
II.1.1(vii) the counting half of 5.5 and 5.6, and says it bears on the
crossing only through 5.5's cardinal conclusion.

**Recommendation: do NOT fund an index-level re-route.** It would spend a
dispatch to discover that the descent moved rather than vanished.

## 5. THE DELIVERED HALF

**SOUND, HONESTLY PRICED, AND A REAL DD4 WIN.**

### 5.1 `src/L/Count.lagda.md` is fully generic. DD4 passes at full marks.

`module L.Count {ℓ : Level} where` (:23). Its imports are `Base.Prelude`,
`FOL.Syntax`, `FOL.Manipulation.Relabelling`, `FOL.Manipulation.Parameters`
and the cubical library. **There is no `L.` import at all.** No `Lset`, no
`𝒟`, no stage presentation reaches any type. P-l passes by construction, not
by care.

620 against the archived 588 is **+32**, and `composed-count` at :695-698
accounts for it. **The growth is content, not glue.** The claim checks out.

**ONE DEFECT, and it is cheap to fix NOW and expensive to fix later.** The
module has zero L content and sits at `src/L/Count.lagda.md`. The report flags
this itself in its uncertainty item 4. The per-trophy bucket split is computed
from the IMPORT CLOSURE (`dev/ledger.toml:360`). A J-tower master importing
`L.Count` will read as an L dependency. **Rename to `FOL.Count` and move to
`src/FOL/` BEFORE wiring the catalog.** After wiring, the rename costs an
import sweep and a bucket recount.

### 5.2 `src/L/StageCardinal.lagda.md` is parameterized correctly

`module Bound (β) (oβ) (infβ) (pair) (pair-inj)` (:51-58). The square law
enters as a parameter, so the module carries no square-law debt in its type.
`count-bound`, `formula-bound` and `tuple-g` are generic in `K` (:87-176). P-h
passes. The `Lower` module is L-specific by necessity, since it is about the
tower.

### 5.3 The rates check out, with one caliber note

| file | median s | in-fence | rate | report |
|---|---:|---:|---:|---:|
| `Count` | 0.66 | 620 | 0.001065 | 0.0011 |
| `StageCardinal` | 0.90 | 174 | 0.005172 | 0.0052 |

The arithmetic is correct. Both sit far inside the bar and below P-m's
parameterized band (`dev/LESSONS.md:2419`). That is the certificate the brief
asked for.

**Caliber note.** The report measured at `GHCRTS="-A64m -I0 -M8g"`, as C-12
and the brief demand. DD24's declared caliber is `-A64m -I0 -M16g`. A tighter
heap can only add collection time, so these figures are CONSERVATIVE. They are
still not the declared caliber, so `check-ratio.py` must re-measure at wiring.

### 5.4 Gates the report did not report, run by me

The brief ordered `lint-prose.py --check` and `lint-agda.py --check`. The
report never mentions them. I ran them on both files:

- `lint-prose.py --check`: exit 0.
- `lint-agda.py --check`: exit 0.
- `weave-i18n.py --check`: exit 0 (not ordered, run anyway).

So the omission is a REPORTING miss, not a defect. Both masters are clean.

## 6. THE BRIEF'S SHARE

**MODERATE. It did not cause the refusal. It inflated the refusal's price.**

**The two-master cap was NOT the defect.** The parent suspects it. The report
never cites it. The agent delivered two masters and stopped on mathematics,
not on a cap. Rejected.

**"A refusal with both prices is a SUCCESS" did NOT invite a premature
refusal.** The instruction demanded both prices and the agent gave both. The
stop is a legitimate use of it. Rejected.

**Two real defects, both about the read set.**

1. **The brief never named the live `src/L/Choice/` or `src/L/WellOrder/`.**
   SCOPE (read) named `devlin-II5.md`, the four archived modules, and
   `src/L/Hull.lagda.md`. The refusal's entire cost centre is machinery those
   two directories already hold: `leastOf`, `stageOrder`, `pullOrder`,
   `birth`, `names-complete`, `leastName`. `[LJ-0.7]` found the definable
   well-order is one of exactly two per-tower objects, so a counting brief
   should always point at it.
2. **The brief's archive table hid the square law.** It listed four modules
   totalling 1,452 lines and said "1,452 lines exist". But
   `_build/lj-1.1-recon.md:135-149` splits THIS row into seven chapters, 4a to
   4g, totalling 2,935 to 3,950, and 4c and 4d are exactly `Pairing` and
   `SquareLaw` with the seconds warning attached. The agent had to discover
   mid-build that the row carries 1,283 more lines than its brief showed.

**One miss belongs to the agent, and it is the costly one.** The brief DID name
`archive/dev/TASKS-archived.md`. That file carries the `[L3.32-T85]` row at
line 120. The agent's ARCHIVE USED section names four masters, the LJ-1.1
recon, the LJ-1.3 and LJ-1.4 reports, and LESSONS. It does not name
`TASKS-archived.md` at all. Reading it would have found the cure, the
measurement and the 52-line figure.

**A note on how the wrong number travelled.** `_build/lj-1.1-recon.md:251`
puts the file count first and the in-fence count last in one sentence. The
report took the first number. That sentence shape has now produced one 257-line
error. Consider a convention: state in-fence first, or state only in-fence.

## 7. WHAT THE ORCHESTRATOR SHOULD DO NEXT

Ordered. The first three are cheap and the fourth is the decision.

1. **ACCEPT the delivered half and wire it, but RENAME FIRST.** Move
   `src/L/Count.lagda.md` to `src/FOL/Count.lagda.md` as `FOL.Count`. It has no
   L content in any type. The rename is free today and costs an import sweep
   after wiring. Then add both masters to `ratio.gch_wing` and let
   `check-ratio.py` measure them at the declared caliber.

2. **CORRECT the record, in the LJ-1.6 audit and in the journal.** Three
   numbers are wrong and they will be re-quoted if they stand.
   - Square-law port: **1,283 in-fence**, not 1,540.
   - `SquareLaw` seconds: **23.3**, not 61.9. `Pairing`: **18.6**.
   - Corrected port total: **2,527 to 2,877** on the caliber fix alone, and
     **2,297 to 2,367** if the T85 comparable holds here. Not 2,784 to 3,134.

3. **CLOSE the report's uncertainty item 2 NEGATIVE and record why.** The chain
   consumes the carrier-level upper half. Do not fund an index-level re-route.
   Section 4 has the citations.

4. **DO NOT fund the square-law port until a seconds gate runs.** This is the
   real decision and DD24 is the reason. The port at its own newest measured
   figures puts the wing at 1.34x the bar, and the caliber mismatch points
   upward. Run a probe, not a build:
   - Port `Pairing` alone, or a decisive slice of it, and MEASURE it at
     DD24's declared caliber (`-A64m -I0 -M16g`, cold module, warm
     dependencies).
   - Report the rate. GO if the pair projects inside the wing's budget. NO-GO
     otherwise, with the rate.
   - P-l requires this. The 23.3 s figure belongs to another tree.
   - **Name the ideal-form question in the same brief (D17).** `[T98]` found
     the module presentation-bound and its abstract restatement heap-exhausted
     at `-M8g`. The rewrite side may be cheaper than the port. Price it before
     porting, not after.

5. **Send the level-size assembly as a BUILD, once the pairing lands.** Its
   brief must:
   - Name `src/ProbeTowerInd2.agda` and `_build/l3.32-t85-report.md` in SCOPE
     (read). They are the design.
   - Name `src/L/Choice/` and `src/L/WellOrder/Base.lagda.md` in SCOPE (read).
   - State the price from the measured comparable: successor half about 52
     lines, lower half delivered, limit half 150 to 220. Total about 220 to
     290, and re-measure at this site per P-l.
   - **Gate the widest term first.** T85 names it: the transport-stability
     lemma for the count across stage paths, in the union's double quotient
     (`_build/l3.32-t85-report.md:234-241`). It is R-35 and R-37 wall class.
     That is the one piece nobody has probed.

6. **Add a row for the non-initial transfer.** The archived square law holds at
   initial ordinals only, by its own prose
   (`archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md:956-963`). The chain
   needs the level size at arbitrary infinite ordinals. Neither the report nor
   the recon carries this. Price it before it becomes a surprise.

7. **Consider a LESSONS candidate, and the measurement is in this review.**
   Proposed statement: *a refusal must survey the untracked probe record and
   the archived task index, not only the archived masters.* Measurement: this
   dispatch re-derived a 2026-08-05 finding and priced its cure at 250 to 450
   lines, against a measured 52. The orchestrator assigns the ID.

## 8. LITERATURE USED

- `dev/literature/devlin-II5.md:134-143` (section 1.4, Devlin 5.4). TOOK: the
  hull count is a count of FORMULAS over the parameter set, so the parameter
  set is the CARRIER of `L_α`. This is what makes section 4's answer
  carrier-level.
- `dev/literature/devlin-II5.md:147-167` (section 1.5, 5.5 to 5.8). TOOK: the
  two directions the chain consumes, and which one the report delivered.
- `dev/literature/devlin-II5.md:272-283` (sections 2.5 and 2.6). TOOK: the
  counting needs "cardinal arithmetic on a countable formula set with
  parameters from X" and "no level-story content"; 5.5 needs the level-size
  equation plus initial-ordinal arithmetic. This confirms the square law's
  necessity in section 3.1.
- `dev/literature/devlin-II5.md:411-417` (section 5.2, II.1.1(vii)). TOOK: it
  bears as the counting half of 5.5 and 5.6, and bears on the crossing only
  through 5.5's cardinal conclusion.
- `_build/literature/dev2.txt:1357-1360` (5.4 itself) and `:1369-1384` (5.5's
  proof). TOOK: the printed chain `|γ| = |M| = |L_α| = |α| < κ`, which is the
  evidence for section 4's split into an upper and a lower use.
- **The two UNRESOLVED OCR items: I CHECKED, and the report is right.**
  `dev/literature/devlin-II5.md:447` (section 6.2) resolves 5.5's second clause
  as "α < κ", and section 6 lists the unresolved pair as 5.2's transfer
  subscripts and 2.2's definability matrix. **Neither touches the counting
  statement.** The report's section 8 says the same. Confirmed, not taken on
  trust.
- `dev/literature/j-hierarchy.md`: SKIPPED. WHY NOT: the J analogue
  `|J_ρ^A| = H_ρ^M` bears on what the J tower supplies, and no question in
  this review turns on it. The report's section 7 already answers the DD4 side,
  and section 2.6 here settles the descent's DD4 class from the tree instead.

## 9. ARCHIVE USED

- `archive/dev/TASKS-archived.md:120`: the `[L3.32-T85]` row, GREEN, pointing at
  `_build/l3.32-t85-report.md`. TOOK: the existence of the cure. **This is the
  row the return missed.** Also `:94`, the `[L3.32-T59]` RED gate that T85
  re-designed.
- `_build/l3.32-t85-report.md:8-31` (verdict), `:108-113` (the candidate table
  and the 52-line figure), `:143-165` (the design, with the least-of descent at
  item 3), `:186-194` (12.8 s cold, 2.6 s warm), `:218-251` (the limit half at
  150 to 220 naive and its named wall). TOOK: the whole of section 2.3.
- `src/ProbeTowerInd2.agda:49-50, :61-63, :70-94, :99-159`: the probe itself,
  untracked in this working tree. TOOK: the code that proves the descent is
  cheap, and the exact comment that names the route.
- `archive/dev/JOURNAL-archived.md:3463`: the entry marks the older profile
  SUPERSEDED by `[T242]`, and re-measures SquareLaw at 23.3 s against 64.4.
  TOOK: the supersession that makes the report's 61.9 stale.
- `archive/dev/STATUS-archived.md:103, :108`: the 856 s history and the
  thirteenfold cut. TOOK: the provenance of the figure the report quotes.
- `archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md:952-963, :970-978`: the
  archive's own prose that the law fails at non-initial ordinals, and the `sq`
  and `Init` definitions. TOOK: section 3.2, the unnamed gap.
- `archive/rud-route/src/L/Ordinal/Pairing.lagda.md`: MEASURED at 376 in-fence
  and 633 file lines. TOOK: the caliber correction.
- `archive/rud-route/src/FOL/Count.lagda.md`: MEASURED at 588 in-fence. TOOK:
  the baseline for the port's +32 growth.
- `archive/rud-route/src/L/Cardinal.lagda.md` (299) and
  `CardinalPredicates.lagda.md` (399): MEASURED only. Not otherwise used. The
  report's verdicts on both look right and neither bears on the refusal.
- `_build/lj-1.1-recon.md:135-149` (block 4, chapters 4a to 4g) and `:251-253`
  (the archive survey rows). TOOK: the seven-chapter split the brief's table
  omitted, and the exact sentence that produced the 633 slip.
- `_build/lj-1.3-report.md` and `_build/lj-1.4-report.md`: read for the port
  precedent. Nothing in this review turns on them. The report's use of them is
  sound.
- `dev/LESSONS.md`: D-1 (:1038), D-10 (:1316), P-l (:2264), P-m (:2419),
  P-n (:2442), P-s (:2528). P-l and P-s carry section 3.3's caliber warnings.
  P-m certifies the delivered half's class. D-10 is what T85 ran and what this
  return should have run against its own premise.

## 10. WHAT I AM NOT SURE OF

1. **The wing aggregate rests on one number I did not measure.** I took 0.0065
   for the current wing from the brief. I MEASURED the line counts. The
   scenario table's conclusion is robust: even at zero seconds for the existing
   wing, the square law alone gives 47.36 / 2,677 = 0.0177, still over the bar.
   So the FAIL verdict does not depend on that figure.

2. **The 23.3 s and 18.6 s figures are profile seconds on the retired tree.**
   DD24's caliber is different, and the ledger records the slice sum at 1.45x
   the cone. I believe the true DD24 figure is HIGHER, which strengthens the
   finding. I did not run Agda, per the constraint, so this is inference from
   recorded calibers.

3. **The 52-line descent figure comes from a probe that does not compile
   today.** Its three main imports are archived. I claim it is a measured
   comparable, not a price. P-l says the same. The re-measurement is item 5 of
   section 7.

4. **My surjection argument in section 2.5 is my own derivation.** I did not
   build it. It supports the conclusion that the descent is movable but not
   removable. The conclusion also follows from T85 alone, which IS measured, so
   nothing load-bearing rests on my derivation.

5. **I did not verify that `SWO ⟪ α ⟫` exists for a bare ordinal in today's
   tree.** `ordSWO` lives in the archived `L.Ordinal.Pairing`
   (`src/ProbeTowerInd2.agda:19`), so it returns with the pairing port.
   `stageOrder` gives the analogue for stages and is delivered. If the pairing
   port is refused, someone must re-check where `ordSWO` comes from.

6. **I did not price the non-initial transfer of section 3.2.** I only
   established that the archive names it and that neither the report nor the
   recon carries it. It could be small. It is not zero.

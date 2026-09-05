# LJ-1.327 report: the square law needs a FORMULA, not an adapter

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. Probe. It lands
nothing. Written incrementally (C-22).

## VERDICT: EXPENSIVE

**The formula IS writable. Nothing in the object language blocks it.** I found
the delivered template that turns an ambient well-founded recursion into an
L-set, and I measured two of the pieces the description needs.

**But the price is about 820 lines, and the leg it buys is not the leg the
trophy needs.** Two of the brief's premises are false and I refute both with
`file:line`.

## 1. WHAT RAN, AND THE MACHINE LOAD BESIDE EVERY FIGURE

The probe is `agents/tasks/LJ-1-327/ProbeLJ1327A.agda`. Load counted before
every invocation with the brief's command,
`ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`.
`GHCRTS="-A64m -I0 -M8g"` on every run. One process. No heap wall. No run came
near the 30-minute line.

| run | what | exit | real seconds | load before |
|---|---|---:|---:|---:|
| 1 | first check, both parts | **42** | 2.47 | 1 |
| 2 | after the `≺₁` type fix | 0 | 2.45 | 0 |
| 3 | re-check, exit code captured | **0** | 2.26 | 0 |
| 4 | NEGATIVE CONTROL, the two order atoms swapped | **42** | 1.69 | 1 |
| 5 | control reverted, re-verified | **0** | 1.67 | 1 |

**RUN 4 IS THE POINT OF THE TABLE (C-44, and `[LJ-1.326]`'s own discipline).**
I swapped `var a ∈̇ var b` to `var b ∈̇ var a` in the second disjunct of
`maxAt`. Agda refused with exit 42 at line 160, the `lt` case of `maxAt-in`,
which is exactly the case the swap breaks. **So the formula is really
elaborated and the adequacy proof really reads it.** MEASURED.

Every figure is WARM. Every interface was already built. No cold cost is
measured here.

## 2. WHAT `pairω` ACTUALLY IS, FROM ITS DEFINITION

**`pairω` is a WELL-FOUNDED RECURSION. It is not arithmetic and it is not a
case split.** MEASURED, by reading the definition chain:

- `pairω p = fiber ω {x = colA p} (col∈α p) .fst`,
  `src/L/InjChain.lagda.md:175-176`.
- `colA = col ω ω-ord`, `src/L/Ordinal/SquareLaw.lagda.md:715-716`.
- `col = W.induction {P = λ _ → S} colStep`, `:383-385`, under
  `module W = WFI wf≺` at `:381`.
- `colStep p rec = ⋃ (sett Pair (λ r → colPick p rec r (≺-dec r p)))`, `:378-379`.
- `colPick` gives `sucV (rec r pr)` when `r ≺ p`, and `∅` otherwise, `:373-376`.

**So `col p` is the ORDER COLLAPSE of the Gödel order below `p`**, that is
`col p = { col r : r ≺ p }`. The chapter says so itself at
`src/L/Ordinal/SquareLaw.lagda.md:6-11`.

**The order `≺` is the Gödel order on pairs**, `:215-218`: the maximum first,
then the first component, then the second component. **Its base relation is
MEMBERSHIP**: `m ≺₁ n = ⟪ α ⟫↪ m ∈ᵗ ⟪ α ⟫↪ n`, `:148-149`. **The maximum is
the trichotomy split `maxGo` under `tri₁`**, `:195-201`.

**THIS REFUTES `[LJ-1.325]`.** That report priced probe B at about 40 lines
because「its value map is arithmetic rather than case-defined」
(`agents/tasks/LJ-1-325/lj-1.325-report.md:113-114`). MEASURED FALSE at
`src/L/Ordinal/SquareLaw.lagda.md:373-385`. The value map is a transfinite
recursion. The 40 was priced against the wrong object.

## 3. WHAT `Carve` DEMANDS OF A CALLER

**THE BRIEF'S OWN STATEMENT IS FALSE. MEASURED.** The brief says「`Carve` and
`InclGraph` take a formula and produce an L-set with its four conjuncts」.
Neither takes a formula.

**There are TWO different `Carve` modules and each one HARD-WIRES its formula.**

| module | parameters | the formula it fixes |
|---|---|---|
| `src/L/InjChain.lagda.md:468-472` | `D C bnd`, subset witness, bound witness, `sep` | `inclFo D` at `:480` |
| `src/L/Absorption.lagda.md:385-401` | `D C γ ω z`, `sh`, four readback lemmas, `D-in-dec`, `bnd`, `below`, `sep` | `shiftFo D γ ω z` at `:412` |

**So a fourth describe-and-carve site needs a FOURTH `Carve`.** Each `Carve` is
generic in its DATA and fixed in its FORMULA. This is the correct reading of
`[LJ-1.326]`'s「`Carve` and `Comp` were written generic」: they are generic in
the sets, the bound and the separation field, not in the description.

**What a caller must supply, MEASURED at the Absorption site, which is the one
that carves an AMBIENT function:**

1. `sh : ⟪ fst D ⟫ → ⟪ fst C ⟫`, the ambient function, `:386`.
2. `shInj`, its injectivity, `:387`.
3. **THREE READBACK LEMMAS**, `shNum`, `shTop` and `shOther`, `:388-394`. Each
   one says what `sh`'s value IS, case by case, in a form the formula's matching
   case can state. **These are the DESCRIPTION.**
4. `D-in-dec`, a decision the description needs, `:395-396`.
5. `bnd` and `below`, the bound, `:397-399`.
6. `sep`, the separation field, `:400-401`.

**NO Δ₀ CERTIFICATE AND NO Σ₁ CERTIFICATE. MEASURED.**
`hasSeparationL : (a : S) (φ : Formula S 1) → isContr (SetOf ...)`,
`src/L/Axioms/Full.lagda.md:144-145`. It is FULL separation for an arbitrary
formula, because the proof reflects the formula at a stage and relativizes it
there (`:126-136`). `hasReplacementL` is delivered on the same terms
(`:350-353`). **This is the single most enabling fact I measured.**

**I re-read `src/L/BoundedSubset.lagda.md` at HEAD** as the brief ordered. Its
`sq` hypothesis is at `:1388-1391` and it takes the AMBIENT square law. The
slot-role cure does not touch the coding layer.

## 4. THE DISTANCE, AND THE MISSING PIECES AT `file:line`

The `Formula` vocabulary is RICH. `src/L/Coding/Model.lagda.md` delivers 25
atomic constructors (MEASURED by grep for the `∀ {n}` signature shape),
including `prAtL` (`:122`), `sucAtL` (`:1395`), `unionAt`
(`:687`), `interAt` (`:684`), `emptyAt` (`:696`), `sameAt` (`:693`), `svAt`
(`:210`), `domAt` (`:278`) and `appAt` (`:160`). `Formula` itself carries
unbounded `∃̇` and `∀̇` and constants from `S`, `src/FOL/Syntax.lagda.md:94-100`.

**So the distance is NOT vocabulary. Four named objects are missing.**

### M1. The domain L-set. MEASURED MISSING, then MEASURED BUILT.

`pairω : ⟪ ω ⟫ × ⟪ ω ⟫ → ⟪ ω ⟫` has a TYPE PRODUCT for a domain.
`InjCode F a b` (`src/L/Cardinal.lagda.md:223-228`) and every `Carve` demand an
L-SET for a domain. **`src/L` has no cartesian product set.** MEASURED by grep
over `src/L/*.lagda.md` and `src/FOL/ZFModel.lagda.md` for
`cartesian|prodʟ|×ʟ|product`: one hit, and it is unrelated prose at
`src/FOL/ZFModel.lagda.md:238`.

**I BUILT IT. 44 code lines, exit 0**, at
`agents/tasks/LJ-1-327/ProbeLJ1327A.agda:69-121`. `module Prod (A B : S)` gives
`P`, `P-spec`, `P-in` and `P-out`. It uses delivered parts only: `PairBound`
for the bound (`src/L/InjChain.lagda.md:276-311`, whose index type and family
are already the product's) and `hasSeparationL` for the carve. **It is generic
in both sets and it names no stage, no numeral and no tower.**

### M2. The order as a formula. MEASURED MISSING, and the ATOM is MEASURED BUILT.

No `Formula` in `src/` mentions `≺`. MEASURED by the census in section 4's first
paragraph: every delivered formula constructor is listed and none is an order.

**I BUILT THE MAXIMUM ATOM. 60 code lines, exit 0**, at
`agents/tasks/LJ-1-327/ProbeLJ1327A.agda:132-206`. `maxAt m a b` is a two-case
disjunction over `∈̇` and `≐`, and `MaxFo` proves adequacy in BOTH directions
against the ambient `maxOrd`: `maxAt-in` at `:155` and `maxAt-out` at `:165`.

**The full order `godAt` is NOT built.** It unpacks two coded pairs and two
maximum witnesses, then splits three ways. It is writable by the same means.

### M3. The recursion as an L-set. MEASURED MISSING, AND THE TEMPLATE IS DELIVERED.

This is the piece that decides the verdict.

The `into` direction of the adequacy must EXHIBIT, in L, the table of the
recursion below a point. Neither delivered `into` does anything of the sort:
`InclFo.into` (`src/L/InjChain.lagda.md:459-461`) and `ShiftFo.into`
(`src/L/Absorption.lagda.md:332-374`) both build their witness with `prʟ`,
because both values are bounded terms of the argument.

**A table cannot be separated out of a bound, because the formula that would
define it is the formula under construction.** That looks like a wall.

**IT IS NOT A WALL. `src/L/Hierarchy.lagda.md` DOES EXACTLY THIS JOB.**
MEASURED, by reading the module:

- `Recorded : V ℓ → V ℓ → Ω`, the graph condition, `:497-499`.
- `IsHier B h`, stated as a MEMBERSHIP EQUIVALENCE so the table is unique by
  extensionality, `:501-502`, with `hier-unique` at `:507-508`.
- `hierAt`, an ambient `∈-induction` that returns an L-SET at every stage,
  `:536-539`.
- **The device: `hasReplacementL A φ fc` at `:595`**, where `φ` is
  `PairGraphAt zero (suc zero)` and `fc` is the FUNCTIONALITY certificate at
  `:590-592`, supplied from the induction hypothesis through `mereFunct`.

**So the tree already turns an ambient well-founded recursion into an L-set
whose graph a formula defines.** The col recursion runs over `≺` instead of
`∈`, so the ambient half is `W.induction wf≺` instead of `∈-induction`. The
shape is the same.

### M4. A fourth `Carve`. See section 3.

## 5. THE PRICE, WITH ITS BASIS (DD8)

**ABOUT 820 LINES for the coded square law, generic in the ordinal.**

**Basis: two MEASURED parts, plus six terms each priced against ONE named
delivered comparable.** Every comparable is a non-blank line count inside
` ``agda ` fences, counted by script at HEAD.

| term | lines | basis |
|---|---:|---|
| the domain product set | **44** | **MEASURED**, `ProbeLJ1327A.agda:69-121`, exit 0 |
| the maximum atom, both directions | **60** | **MEASURED**, `ProbeLJ1327A.agda:132-206`, exit 0 |
| the Gödel order `godAt`, both directions | about 150 | `ShiftFo`, `src/L/Absorption.lagda.md:206-375`, **145 MEASURED**: three cases, two directions, one `∃̇∈` and one `∃̇` |
| the collapse table in L | about 280 | `L.Hierarchy`'s recursion block `:497-626` at **113 MEASURED**, plus its formula half `:117-465` at **164 MEASURED** |
| the value clause, `⋃` of successors | about 60 | `shiftCase1` plus `case1-val`, `src/L/Absorption.lagda.md:210-211` and `:274-280`; `unionAt` and `sucAtL` are delivered |
| a fourth `Carve` | about 127 | `src/L/Absorption.lagda.md:385-530`, **127 MEASURED**, the one that carves an ambient function |
| the L instantiation | about 52 | `ShiftGraph`, `src/L/Absorption.lagda.md:538-605`, **52 MEASURED** |
| the readback to `sq α` | about 50 | `Carve`'s `pair-out` and `pair-in` plus `Small`, `src/L/InjChain.lagda.md:494-511` |

Total 823. **I report about 820.**

**WRITE IT AT A GENERAL ORDINAL, NOT AT ω. THE ω-ONLY ROUTE IS A FALSE
ECONOMY.** `[LJ-1.325]` chose ω as「the SMALLEST site」
(`lj-1.325-report.md:111-112`). MEASURED: `col` is already generic in α
(`src/L/Ordinal/SquareLaw.lagda.md:140` opens `module _ (α : S) (oα : IsOrd α)`),
and the description does not simplify at ω. At ω one could build the table by
an ambient recursion on `ℕ`, because every segment is finite; that route
transfers to no other ordinal, and the consumers need `sq` at every infinite δ
(`src/L/BoundedSubset.lagda.md:1388-1391`). **So the ω-only saving buys a
result the leg cannot use.**

## 6. AND THE LEG IS NOT THE LEG. TWO PREMISES REFUTED.

### 6.1 The square law's two consumers are AMBIENT. A coded square law helps neither.

MEASURED, by reading both consumers:

- `L.StageCardinal.Bound` takes `pairing` and uses it as
  `pair : ⟪ β ⟫ → ⟪ β ⟫ → ⟪ β ⟫`, `src/L/StageCardinal.lagda.md:63-68`. It
  feeds the counting `f : Formula K 1 → ⟪ β ⟫` at `:178-183`.
- `L.BoundedSubset.BoundedSubsetAt` takes `sq` at `:1388-1391` and passes it
  to `L.StageCardinal` at `:1397` and to `SC.Bound` at `:1410`.

**Both want the ambient function, and both already have it.** A coded `sq` is
not consumed anywhere in `src/`. MEASURED by grep: `sq` has exactly these two
consumers.

### 6.2 THE CHAIN THAT WOULD CONSUME IT DOES NOT EXIST. MEASURED.

`[LJ-1.325]` wrote「The final injection is a chain. Its inclusion legs are
carved. Its shift leg is carved. Its composition is carved. Its pairing leg is
AMBIENT」(`lj-1.325-report.md:88-95`). **That chain is INFERRED, not delivered.**

MEASURED:

- `src/L/GCH.lagda.md` is 70 lines and it is the STATEMENT only. `InjL` is
  defined at `:37-38` and used at `:67-68`. **grep for `InjL` over `src/`
  returns five lines: those four, and `module LeastCardInjL` at
  `src/L/Cardinal.lagda.md:61`, which is a different name that contains the
  same letters. So `InjL` has NO consumer outside its own statement.**
- There is no ambient `⟪ 𝒫 κ ⟫ ↪ ⟪ δ ⟫` in `src/`. MEASURED: grep for `𝒫`
  over `src/L` returns four lines, `src/L/GCH.lagda.md:67-69` (the trophy
  statement) and `src/L/Axioms/Power.lagda.md:132` (the axiom). No consumer
  builds an injection out of a power set.
- **So the count of uncarved legs is not 1, not 3 and not any number. No chain
  is delivered to count.** That is the honest answer to C-42.

### 6.3 What the coded forward bound really needs, and the literature agrees.

INFERRED, and I mark it INFERRED. The classical route to `InjL (𝒫 κ) δ` sends
each subset to its position in the definable well-order of L. **The tree
delivers that order AMBIENTLY and SEALED, with no formula**:
`orderAt : (γ : S) → IsOrd γ → SWO (Mem (Lset γ))`,
`src/L/Choice/Step.lagda.md:739-741`, built by `∈-induction` under `opaque`.

The delivered level-size theorem is ambient too:
`stage-card-upper : (α : S) → IsOrd α → ... → ⟪ Lset α ⟫ ↪ ⟪ α ⟫`,
`src/L/StageCardinal.lagda.md:564-566`. **To code it you must describe its whole
construction, which runs through `L.Definability.DefOf` and the formula
counting.** `src/L/StageCardinal.lagda.md` is 482 agda lines. That is the honest
size of the term the square law was standing in front of.

**The digest names the same engine.** `dev/literature/devlin-II5.md:360-362`:
「The single engine II.5 leans on most is item 7: the uniformly-Δ₁ level
well-order」. And `:404-406` records that the satisfaction-internalization step
「is exactly the step `[LJ-1.2]`'s probe found blocked on the delivered tree」.

## 7. HOW MANY LEGS REMAIN UNCARVED (C-42)

**None, and all of them. Both answers are the same measurement.** No chain
exists in `src/` to have legs. What a future chain would have to carve, and
whether it is carved today:

| object | carved today? | evidence |
|---|---|---|
| the ordinal inclusion | **YES** | `OrdIncl`, `src/L/InjChain.lagda.md:604-607` |
| the successor shift | **YES** | `ShiftGraph`, `src/L/Absorption.lagda.md:538-605` |
| the composition | **YES**, and it needs no adapter | `Comp`, `src/L/InjChain.lagda.md:314-433` |
| the square law | **NO** | this task, about 820 lines |
| the level size `⟪ Lset α ⟫ ↪ ⟪ α ⟫` | **NO** | `src/L/StageCardinal.lagda.md:564-566`, 482-line master |
| the definable well-order | **NO** | `src/L/Choice/Step.lagda.md:739-741`, sealed, no formula |
| the bounded-subset lemma | **NO** | `src/L/BoundedSubset.lagda.md`, ambient throughout |

**I CONFIRMED `[LJ-1.326]`'s `Comp` finding, as the brief ordered.**
`Comp (D E C F H : S)` at `src/L/InjChain.lagda.md:314-324` takes `svF`, `dmF`,
`ijF`, `ranF`, then `svH`, `dmH`, `ijH`, `ranH`. Compared field by field with
`InjCode F a b` at `src/L/Cardinal.lagda.md:223-228`, that is `InjCode F D E`
and `InjCode H E C` written out. It returns `svK`, `dmK`, `ijK` and `ranK`
(`:380-422`), which is `InjCode K D C`. **CONFIRMED. No adapter.**

## 8. DD4

**NAME THE AXIS (C-46).** DD4's own axis is AC closure against GCH closure.
`scripts/measure/ledger.py:50-52` names it in code:「DD4's report: what the AC
and GCH closures share, in masters and lines」. Standing today: 32,474 lines
over 94 masters, from `ledger.py --brief`.

**MY TWO TERMS ARE TOWER-BLIND. Say it in one line, as the brief asks: YES.**
`Prod` is generic in two arbitrary L-sets and `MaxFo` is generic in one
ordinal. Neither names a stage, a numeral, a tower or ω. MEASURED, by reading
the module headers at `ProbeLJ1327A.agda:75` and `:136`.

**WHAT THEY ADD TO THE GCH CLOSURE: I DID NOT MEASURE IT AND I DO NOT GUESS
IT.** `[LJ-1.326]` measured its closure figures with a replication of
`ledger.py`'s own `import_graph`. My terms are not landed and their placement is
the orchestrator's call, so the import edges are not fixed. **What I can say
structurally:** `Prod` needs `L.InjChain` (for `PairBound`) and
`L.Axioms.Full`; `MaxFo` needs `L.Ordinal.SquareLaw`. Both are proof-side and
both would sit in SHARED if placed generically, because neither mentions a
tower.

**AND I PROTECTED `[LJ-1.326]`'s RESULT, as the brief asked.** Its 8-line
adapter is cheap because `Carve` is generic in its DATA. My 44-line product set
is cheap for the same reason: `PairBound` was written generic in the index type
and the family, so I reused it whole and wrote no bound. **That is the
measurement DD4 buys, twice now.**

## 9. THE ABORT CRITERION, ANSWERED ROW BY ROW

| the brief's row | outcome |
|---|---|
| **WRITABLE AND YOU WRITE IT** | not taken. 820 lines is not one session |
| **WRITABLE AND EXPENSIVE** | **TAKEN.** Section 5 prices it against eight comparables. The widest remaining term is the collapse table, about 280 |
| **IT NEEDS SOMETHING UNDELIVERED** | **PARTLY TAKEN.** Four objects are missing (section 4). I BUILT two of them. The other two are writable by a delivered template |
| **`pairω` IS NOT THE RIGHT OBJECT** | **TAKEN, AND THIS IS THE RESULT.** Section 6. Its two consumers are ambient, the chain does not exist, and the real blocker is the definable well-order as a formula |
| A WALL | not taken. Longest single invocation 2.47 s |

## 10. WHAT I DID NOT SETTLE

1. **The full order `godAt`.** I built the maximum atom only. The 150 is an
   estimate against `ShiftFo`, not a measurement.
2. **The collapse table.** I read the `L.Hierarchy` template and did not
   instantiate it. The 280 is an estimate against a delivered comparable of the
   same texture, which is what DD8 allows, and it is the widest term.
3. **The closure figures.** Not measured. Section 8 says why.
4. **A cold check cost.** Every figure is warm.
5. **Whether the definable well-order is describable at all.** I did not probe
   it. `[LJ-1.2]`'s recorded NO-GO on satisfaction internalization
   (`dev/literature/devlin-II5.md:404-406`) is a claim I read, not one I
   re-derived.

## 11. PROHIBITIONS, ANSWERED

- **Writes:** `agents/tasks/LJ-1-327/` only, two files, this report and
  `ProbeLJ1327A.agda`. Nothing in `src/`, nothing in `dev/`, no other task
  directory, no `.claude/`, no `AGENTS.md`. I READ
  `agents/tasks/LJ-1-326/ProbeLJ1326A.agda` and did not change it.
- **No commit, no push, no `make check`.** No `git checkout`, `stash`, `reset`
  or `clean`.
- **Agda:** five invocations, one at a time, load counted before each,
  `GHCRTS="-A64m -I0 -M8g"`, cap never raised.
- The backup of the negative control sits in the session scratchpad, outside the
  repository.

## 12. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-326/lj-1.326-report.md`, READ WHOLE.** Line read
  `:152-155`:「The gap is a MISSING FORMULA, not a missing adapter. Every carve
  in the tree runs through `hasSeparationL b φ` with `φ : Formula S 1`」.
  **TOOK: the statement, and I re-derived it.** It is right about the gap and
  wrong about「every carve」being one device: there are TWO `Carve` modules and
  each fixes its own formula (section 3). Its `Comp` finding at `:106-112` is
  CONFIRMED at every locator.
- **`agents/tasks/LJ-1-325/lj-1.325-report.md`, READ `:60-130` and `:400-410`.**
  Line read `:113-114`:「its value map is arithmetic rather than
  case-defined」. **TOOK: the claim, and REFUTED it** at
  `src/L/Ordinal/SquareLaw.lagda.md:373-385` (section 2).
- **`archive/dev/TASKS-archived.md`, line read `:53`** (T18, the GCH scope gate,
  NO-GO). **TOOK, SHAPE ONLY:** the retired route also gated a GCH-side price
  with one small probe before funding it. **WHAT WOULD NOT TRANSFER:** the
  retired route described its objects over the rud presentation. Every carve in
  the delivered tree runs through `hasSeparationL` and a `Formula S 1`, which
  the rud route did not have in this form, so no figure there prices a `Carve`
  site. `dev/PLAN.md:787` records that the rud-route code moved to
  `archive/src/2026-08-09-rud-route/` when the route changed.

## 13. LITERATURE USED (DD18)

- **`dev/literature/devlin-II5.md`. IT BEARS, but NOT the way the brief says.**
  READ `:145-170`, `:255-295`, `:355-365` and `:396-420`.
  **THE ONE-LINE ANSWER THE BRIEF ASKED FOR: Devlin does NEITHER. He does not
  describe the pairing's graph and he does not get it from a general
  definability lemma, because he never needs the pairing definable in L at
  all.** Line read `:160-163`: 5.6 reads「By 5.5, 𝒫(κ) ⊆ L_{κ⁺} ... So by
  1.1(vii)」. Line read `:411-419`: 1.1(vii) is「generic cardinal arithmetic
  over the level-size equation」. Devlin works under V = L, so ambient is
  internal and the pairing needs no code. **The coding demand is Bedrock's own,
  and it comes from the restated trophy.**
  **AND THE DIGEST NAMES THE REAL ENGINE.** Line read `:360-362`:「The single
  engine II.5 leans on most is item 7: the uniformly-Δ₁ level well-order」.
  **TOOK: that is the object my section 6.3 names, and it is not the square
  law.**
- **`dev/literature/truncation-and-selection.md`. IT DOES NOT BEAR ON THIS
  PROBE. WHY NOT:** my question is definability in the object language, not
  truncation. Nothing I built needs untruncation, because `Prod` and `MaxFo`
  both return propositions or paths.
- **WHY NOT re-fetched:** the digest carries locators into `dev2.txt` and I take
  only statement-level facts from it.

## 14. THE ONE-LINE RECOMMENDATION

**Do not fund the square law's formula. Fund a probe on the definable
well-order as a formula**, at `src/L/Choice/Step.lagda.md:739-741`, because
that object blocks the coded forward bound whether or not the square law is
described, and section 6 shows the square law blocks nothing that exists today.

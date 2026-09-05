# LJ-1.17-R: adversarial review of the NO SHAPE FITS return (DD25)

Reviewer: in-harness Opus subagent, maximum effort. Read-only on `src/`. No
Agda was run (C-12). No commit was made. The only write is this file.

## 1. VERDICT

**OVERTURN. KEEP THE MEASUREMENT.**

The three measured numbers are sound and they are the day's best result.
Every conclusion drawn from them is wrong. Two independent errors carry the
overturn, and each one overturns the verdict on its own.

**ERROR 1, THE ARITHMETIC. The wing PASSES DD24 with the square law inside
it.** The report divides the wing's seconds budget by the wing's line count
TODAY. The wing holds 1,394 of a projected 7,553 to 11,197 lines. The report
also cross-pairs the two ends of the budget band. Corrected, the residue must
run at **0.0093 to 0.0107 s per line**, not at the report's 0.0059 to 0.0170.
Every measured wing module runs between 0.0011 and 0.0052.

**ERROR 2, THE NECESSITY. The square law is needed at INITIAL ordinals only.**
The wing applies condensation once, at 5.6, and the digest states the
application as `κ⁺` with `α = κ` (`dev/literature/devlin-II5.md:164-166`).
Both are cardinals. The report cited `:145-158` and stopped six lines above
the answer. The tree's own probe already runs the initial-only shape
(`src/ProbeTowerInd2.agda:99-159`). So the non-initial transfer, which the
report prices at 150 to 400 lines and about 8 s, is **not owed**.

**ERROR 3, THE IDEAL FORM. The port was priced twice.** Section 3 below gives
the evidence. The report's floor claim for `SquareLaw` rests on a profile
whose own total is 64.4 s. The module measures 23.13 s today. 41 s of the
claimed floor has already gone, and nobody has profiled what is left.

### The arithmetic, in one place

MEASURED inputs: the pair at 1,283 in-fence lines and 41.36 s
(`_build/lj-1.17-report.md:127-129`). The bar is 0.011472 times 1.15, so
0.013193 (`dev/ledger.toml:2545`, `:2765`). The wing is 7,553 to 11,197 lines
(`dev/ledger.toml:241`) and its budget is 99.6 to 147.7 s (`:273`).

| quantity | report | corrected | why |
|---|---:|---:|---|
| residue lines | 6,270-9,914 | 6,270-9,914 | agreed |
| residue seconds | 58.2-106.3 | 58.2-106.3 | agreed |
| residue rate needed | 0.0059-0.0170 | **0.0093-0.0107** | the report cross-pairs the band ends |
| verdict denominator | 2,677 lines | **7,553-11,197** | the wing is 12 to 18 percent built by lines |
| non-initial transfer | 150-400 lines, 8 s | **0** | the wing's only site is initial |

**The pass, at the wing's most expensive rate for everything else.** Credit
the residue with 0.0065 s per line, the declared wing's own figure, which is
higher than every wing module measured at the caliber.

| wing end | lines | seconds | s/line | against 0.013193 |
|---|---:|---:|---:|---|
| low, 7,553 | 7,553 | 82.12 | 0.01087 | **0.82x PASS** |
| high, 11,197 | 11,197 | 105.80 | 0.00945 | **0.72x PASS** |
| low, plus the transfer the report priced | 7,553 | 88.49 | 0.01172 | **0.89x PASS** |

The wing fails only if the residue runs above 0.0093 s per line. That is 1.8
times `L/StageCardinal`'s measured 0.0052 and 8.7 times `FOL/Count`'s measured
0.0011.

**AND THE TOOL AGREES.** `scripts/check-ratio.py:38-41` states its own rule:
"THE PER-MODULE FLAG IS ADVICE; THE AGGREGATE IS THE JUDGMENT. A single module
may sit above the bar for a reason the wing as a whole pays back, which is
exactly what a shared parameterized core does for its instantiations. Only the
aggregate fails the run." The square law is that case, word for word. The
report's verdict is a per-module rate, which DD24's own instrument treats as
advice.

**WHAT SURVIVES, and it is real.** The measurement stands. Three cold runs per
module at the declared caliber, on today's tree, confirm the ledger's 18.6 and
23.3 s within one percent. That kills `[LJ-1.6-R]`'s stated worry that the
DD24 caliber would read HIGHER (`_build/lj-1.6-review.md:283-284`). The
disproportion also stands: the pair takes 28 to 42 percent of the budget for
11 to 17 percent of the lines. A disproportion is a fact. It is not a failure.

## 2. IS THE SQUARE LAW REQUIRED?

**YES at infinite CARDINALS. NO at arbitrary infinite ordinals.** The report
answers the second question and the wing asks the first.

### 2.1 What Devlin himself assumes

**Devlin proves no cardinal arithmetic at all.** His 1.1(vii) proof is nine
printed lines (`_build/literature/dev2.txt:200-215`). The limit step reads
`|L_λ| ≤ Σ_{α<λ}|L_α| ≤ Σ_{α<λ}|α| = |λ|`. The last equality is written
without proof or citation. The successor step reads "since ℒ is countable, the
set of formulas of ℒ_{L_α} is easily seen to have cardinality |L_α|"
(`dev2.txt:211-213`). "Easily seen" is the whole argument.

So ordinal and cardinal arithmetic is **background set theory** for Devlin. He
never states a square law and never uses the name. This bears directly on
route (b) of section 4: a formalization that takes the arithmetic as a module
parameter is faithful to the source, not a shortcut.

### 2.2 The wing's only application is at two cardinals

`[LJ-1.19]` established that the wing condenses exactly once, at 5.5, with a
free `λ` (`_build/lj-1.19-report.md:16-29`). The digest states that single
application:

> The application of 5.5 in 5.6 is at the cardinal κ⁺ with α = κ: every x ⊆ κ
> satisfies x ⊆ L_κ, and κ < κ⁺, so x ∈ L_{κ⁺}. 1.1(vii) gives |L_{κ⁺}| = κ⁺.
> (`dev/literature/devlin-II5.md:164-166`)

**`α` is `κ`. Both are cardinals.** The report's section 2 says "The chain
consumes |Lset α| = |α| at arbitrary infinite α" and cites `:147-158`. The
sentence that names the actual `α` is six lines below its citation.

Walk the chain at the wing's own instance, with `κ` an infinite cardinal:

1. `x ⊆ κ`, so `x ⊆ L_κ`. The hull `M` is taken over `X = L_κ ∪ {x}`.
2. `|M| = |L_κ| = κ`. This needs `⟪ Lset κ ⟫ ↪ ⟪ κ ⟫` and the formula count
   into `⟪ κ ⟫`. **Square law at `κ`, an initial ordinal.**
3. `π : M ≅ L_γ`, so `⟪ γ ⟫ ↪ ⟪ Lset γ ⟫ ≃ ⟪ M ⟫ ↪ ⟪ κ ⟫`. The first
   injection is `stage-card-lower`, **DELIVERED** at
   `src/L/StageCardinal.lagda.md:204-212`.
4. `γ < κ⁺` follows from `⟪ γ ⟫ ↪ ⟪ κ ⟫` and the definition of `κ⁺`. **No
   square law.**
5. `|L_{κ⁺}| = κ⁺` closes 5.6. **Square law at `κ⁺`, an initial ordinal.**

No step names a non-initial ordinal.

### 2.3 The induction runs with the TARGET fixed, and the tree proves it

The report's section 3 says: "The delivered `Bound` shape needs the square law
at every level ordinal β, including every non-initial ordinal." That misreads
the module.

`Bound`'s `β` is the **TARGET**, not the level. Its export is
`formula-bound : (g : K ↪ ⟪ β ⟫) → Formula K 1 ↪ ⟪ β ⟫`
(`src/L/StageCardinal.lagda.md:172-180`). `K` is free. The module's own
comment says the successor step is "this bound at K = ⟪ Lset α ⟫"
(`:52-58`). Nothing ties `K`'s level to `β`.

**The tree's own probe already separates them.** `[L3.32-T85]` wrote:

```
successor-step : (α : S) → Init α → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
              → ⟪ Lset (sucV α) ⟫ ↪ ⟪ α ⟫
```

(`src/ProbeTowerInd2.agda:155-159`). The level rises from `α` to `sucV α`. The
target stays at `α`. The square law enters once, as
`Initial.square α iα` with `Init α` (`:104`). **`Init` is the archived
initial-ordinal predicate.** The probe checked GREEN at 12.8 s cold
(`_build/lj-1.6-review.md:120-125`).

So the level-size theorem the wing needs is: *for an initial `κ`, and every
`β ≤ κ`, `⟪ Lset β ⟫ ↪ ⟪ κ ⟫`.* Every square-law call sits at `κ`. The
successor step is T85's module with its two ordinals split into two
parameters. The limit step codes the stage coordinate with `birth`, which is
delivered (`src/L/Choice/Step.lagda.md:133`, `:189`).

**This is a different theorem from Devlin's 1.1(vii), and it is weaker.** D17
asks for the ideal form of the CONTENT the chain consumes. The content is "the
hull is small" and "gamma is small". It is not "|L_α| = |α| for every α".

### 2.4 Two residual obligations, both named, neither is the transfer

1. **`Init ω` is uninhabited** (`src/ProbeTowerInd2.agda:49-50`). GCH at `ω`
   needs the square law at `ω`, which is `ℕ × ℕ ↪ ℕ`. The archived module
   cannot supply it. This is elementary content and `FOL.Count` already codes
   over `ℕ`. UNPRICED, and small.
2. **`Init κ` must be verified for each cardinal `κ`, or `Init` becomes the
   cardinal notion.** The archive names this choice itself: "at the cardinals
   themselves the counting must still verify the three initiality clauses, or
   take them as its cardinal notion"
   (`archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md:961-963`).

Neither obligation is the 150 to 400 line non-initial transfer. **The ledger's
re-arm note at `dev/ledger.toml:269-272` should be corrected.**

### 2.5 What the archive's own prose says, read in full

The report quotes the initial-only restriction and stops. The same paragraph
continues:

> It does not give the law at the non-initial ordinals such as `ω + ω`: the
> reduction of such a site to its cardinal is the least-of transfer, which is
> the counting's own plumbing (its input, the truncated equinumerosity witness
> of `Card.least`, is delivered here)
> (`archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md:958-963`)

The archive says a non-initial site reduces to its cardinal. It does not say
the chain HAS a non-initial site. Section 2.2 shows it does not.

## 3. WAS THE IDEAL FORM PRICED, OR THE PORT TWICE?

**THE PORT TWICE.** The report priced verbatim archived extractions, then
subtracted one duplication lever, then declared the remainder a floor. No
fresh write was drafted, sketched or probed.

### 3.1 The floor claim for `SquareLaw` rests on a superseded profile

The report's section 4 says: "`[T103]`'s after profile shows
`Initial.pair-inj` at 38.5 s and the two `comp₀-inj` at 6.0 s each."

`[T103]`'s after profile totals **64,401 ms** (`_build/l3.32-t103-report.md:21`,
`:79`). The report's own measurement of the same module is **23.13 s**
(`_build/lj-1.17-report.md:128`). A 38.5 s row cannot sit inside a 23.13 s
module. **41 s came off between T103 and today**, chiefly through
`[L3.32-T123]`'s Pairing seal (`dev/ledger.toml:2379`).

So the report's evidence for "a fresh write pays the same once" describes a
module that no longer exists. **Nobody has profiled the 23.13 s.** The report
does not say this and its section 11 does not flag it.

### 3.2 The floor claim for `Pairing` IS anchored, and it points the other way

The ledger records: "The residual 18.8 s is `col→τ-fiber`, the once-payment
P-l predicts: sealing buys the repeats, never the once"
(`dev/ledger.toml:2379`). `Pairing` measures 18.23 s. So **one definition
carries essentially the whole module.**

`col→τ-fiber` reads `⟪ τ ⟫↪ (col→τ p) ≡ col p`
(`archive/rud-route/src/L/Ordinal/Pairing.lagda.md:483-484`). Its cost is
diagnosed: both bodies "re-elaborate `fiber tau (col-in-tau p)` at the
transparent union" (`dev/ledger.toml:2379`). That is a **presentation**, in
P-l's exact sense: `⟪ ⟫` applied to a transparent construction
(`dev/LESSONS.md:2266-2282`).

**Sealing cannot remove a once-payment. A different construction can.** The
archived proof builds the order type as a V-set through a collapse. A fresh
form that never forms that V-set never pays that once. The report never asks
whether the order type must be a set. It asserts the floor.

### 3.3 The line saving is over-claimed and its source is marked superseded

The report claims an ideal form saves "about 230 to 280 lines" from the Core
and InitialCore mirror. The ledger's own lever records **`net_low = 150`,
`net_high = 200`** (`dev/ledger.toml:1416-1417`), and its status reads "PARTLY
SUPERSEDED 2026-08-06 by [T103] ... RE-PRICE before considering"
(`:1411`). The report cites `:1412-1413` and takes neither the net figure nor
the supersession. D-10 asks for exactly this check.

### 3.4 The one number that decides D17 is cheap and nobody ran it

The report left three probes in the tree: `src/ProbeLJ117Pairing.agda`,
`src/ProbeLJ117SquareLaw.agda` and `src/ProbeLJ117Combinators.agda`. A
definition profile on the two of them costs about 45 s of machine time on a
quiet slot.

If the 41.36 s concentrates in two to four definitions carrying a transparent
construction, then D17 is wide open and the ideal form is unpriced. If it
spreads flat over hundreds of definitions, the report's floor claim is
confirmed. **Today nobody knows which.**

### 3.5 One more transferred figure, and P-l forbids it

The report's section 5 says "The wing contains measured instantiation content"
and cites 0.297 s per line at `dev/ledger.toml:1754`. That row is
`carried_sequence_remeasured`, the RETIRED route's carried sequence, whose
cost `[T241]` located in decode content at the concrete carrier `Lset xi`
(`dev/ledger.toml:1766-1785`). **No wing module has ever measured above
0.0052.** The claim moves a measured figure from another route's archived
module into the wing by analogy, which is the exact move P-l forbids.

## 4. THE ROUTES OUT, PRICED

Ordered by cost. MEASURED and ESTIMATED are marked.

**Route 0. Correct the arithmetic and fund nothing.** Cost **zero**. The wing
passes DD24 with the port as measured, at every measured residue rate. This is
the finding, and it needs no new code. MEASURED, section 1.

**Route 1. Fix the target at an initial ordinal.** Removes the non-initial
transfer. Saving: the 150 to 400 lines and about 8 s the report priced. Cost:
split T85's two ordinals into two parameters, and add a limit step that codes
the stage with the delivered `birth`. The successor half is measured at 52
lines (`_build/lj-1.6-review.md:120-121`); the limit half is priced at 150 to
220 (`:124-126`). ESTIMATED total 200 to 280 lines, which the wing's plan
already books at block 4g, 200 to 500 (`_build/lj-1.1-recon.md:149`). **So
route 1 costs the wing nothing new and saves the transfer.**

**Route 2. Profile the two probes before pricing any rewrite.** Cost about 45
s of machine time. It decides D17 and it is the only unmeasured question that
matters. See section 3.4.

**Route 3. Take the arithmetic as a module parameter.** **ALREADY DELIVERED.**
`src/L/StageCardinal.lagda.md:14-17` takes `sq` as a module parameter, and
`Bound` takes the pairing at `:59-66`. Every wing master downstream carries no
square-law seconds in its own check. Only the discharge site pays. This is
also faithful to Devlin, who assumes the arithmetic (section 2.1). Cost zero.
**It does not lower the tree's total by one second, and nobody should say it
does.**

**Route 4. Accept the seconds, and frame it for the owner.** DD24's own row
says the wing "exists to MEASURE what GCH costs" and carries "no line cap and
no seconds cap, and the omission is deliberate" (`dev/PLAN.md:181`). 41.36 s
is what the ordinal arithmetic costs. It is a measurement. **This is the
owner's call and not mine.** I frame it and stop.

**Route 5, DO NOT TAKE. Re-derive a cheaper square law by analogy.** P-l's
table records five transplants on one day and four failures
(`dev/LESSONS.md:2286-2300`). Two of the four were transplants onto
`SquareLaw` itself. Only the root-cause-guided one worked.

## 5. THE TEMPLATE REFRAMING (DD4): WHOSE BUDGET PAYS?

**LEAD WITH THE INVARIANT. Moving the square law between buckets changes no
seconds and no lines. The tree pays 41.36 s either way.** Any argument that
starts "bill it elsewhere" is accounting unless a second consumer is real.

**Is a second consumer real today? NO.**

- **The AC side.** `L ⊨ AC` needs a definable well-order. It needs no cardinal
  arithmetic. The report's own section 11 item 5 says the AC need is not
  established, and I confirm it.
- **The J tower.** `[LJ-1.15-R]` found the J tower has no Def step and no
  carrier-indexed code set (`_build/lj-1.15-review.md:356-364`). The digest
  gives it the analogue `|J_ρ^A| = H_ρ^M`
  (`dev/literature/devlin-II5.md:411-417`), but GCH is stated once and the
  bridge transports it. No second proof of the level size is planned.

**So the square law has exactly ONE consumer today: the GCH wing's counting.
Re-bucketing it now would be word games and I refuse it.**

**The honest DD4 answer is different, and it is stronger.** The content IS
tower-agnostic: `sq` and `Init` are stated at `S`, over `V.*`, `L.Ordinal`,
`L.WellOrder` and `FOL.ZFStructure`, with no Def-tower content in any type.
`[LJ-0.7]` found the per-tower content is exactly two objects, and the digest
confirms the split: step E "counting" and step F "5.5" are marked EITHER
tower, and the per-tower content is the level-hood certificate and the
definable well-order (`dev/literature/devlin-II5.md:380-382`, `:385-397`). A square law is
neither. **It is template content by construction, and the shape the report
priced is already the shared one.**

**The mechanism to move it EXISTS and it should stay unused until it is
earned.** `dev/ledger.toml:2449-2462` holds the `gch_assign` declarations,
each guarded by a dead-declaration defect that fires the day the AC closure
reaches the module. That guard works in both directions. **Recommendation:
leave the square law in the wing bucket. Let `gch_assign` move it the day a
second consumer appears, and not before.**

**And DD24 already provides for the case without any re-bucketing.**
`scripts/check-ratio.py:38-41` says a single module may sit over the bar
"for a reason the wing as a whole pays back, which is exactly what a shared
parameterized core does for its instantiations". That sentence describes this
module. The reframing that dissolves the budget problem is not a bucket move.
It is reading the tool's own rule.

## 6. THE BRIEF'S SHARE

**LARGE, and it is the decisive share. The agent's measurement was sound. The
frame it was given was not.**

**Defect 1, and it is the whole verdict.** The brief handed the agent a
pre-computed FAIL table with the wrong denominator
(`_build/briefs/LJ-1.17.md:25-33`), told it "THE NUMBERS ARE CORRECTED, so
start from these" (`:39`), and said "I verified both myself" (`:41-42`). The
agent re-derived the same table with 41.36 in place of 41.9 and reached the
same verdict. **The cross-paired band and the today's-lines denominator are
the brief's, and they propagated verbatim.** The brief's instruction to verify
covered the lines and the seconds. It did not cover the arithmetic built on
them.

**Defect 2, the ordering made the ideal form an afterthought.** The GOAL said
"Price the IDEAL form written fresh today, do NOT port" (`:8`). Then "A CHEAP
MEASUREMENT FIRST, BEFORE ANY PRICING" ordered a port measurement (`:82-93`).
An agent given a measurable port and an unmeasurable rewrite will measure the
port and reason the rewrite from it. That is what happened.

**Defect 3, an open question was handed over as an assumed obligation.** The
brief said "The non-initial transfer is unpriced. Price it"
(`:63-68`). It never asked whether the gap is reachable by re-shaping. The
agent priced what it was told to price.

**Defect 4, the read set omitted the design.** `[LJ-1.6-R]` had already
recommended naming `src/ProbeTowerInd2.agda` and `_build/l3.32-t85-report.md`
in SCOPE (read), and called them "the design"
(`_build/lj-1.6-review.md:465-467`). The brief named neither. That probe holds
the initial-only fixed-target shape and would have prevented error 2 by
itself.

**What the brief got right.** It ordered seconds and not lines, it ordered the
declared caliber, it forbade a contended measurement, and it demanded the
class question against P-m and P-n. Those four instructions produced the
measurement, which is the return's durable result. **Keep all four.**

**One miss belongs to the agent.** The brief did name
`archive/dev/TASKS-archived.md`. The report's ARCHIVE USED cites `:119` for
T98. The T98 row is at **`:133`**; `:119` is a different row. The T85 row at
`:120` and the T59 row at `:94` are cited correctly. A one-line slip, and it
is not load-bearing.

**"A refusal is a SUCCESS" did not cause this.** The report refused on
arithmetic it was handed, not on an invitation. I reject that reading.

## 7. WHAT THE ORCHESTRATOR SHOULD DO NEXT

Ordered. The first two cost nothing and the third is one quiet slot.

1. **CORRECT THE RECORD, in three places, before anything else is quoted.**
   - `dev/ledger.toml:247-260`: the block asserts the square law FAILS the
     budget. It fails only against today's line count. State the corrected
     residue rate, 0.0093 to 0.0107, and the pass at 0.82x and 0.72x.
   - `dev/ledger.toml:269-272`: the non-initial transfer re-arm. The wing's
     only application is at `κ` and `κ⁺`, both cardinals
     (`dev/literature/devlin-II5.md:164-166`). Replace the re-arm with the two
     residuals of section 2.4.
   - `dev/PLAN.md` section 11, the `[LJ-1.17]` row: the verdict is overturned.
2. **DO NOT FUND the non-initial transfer.** It is not owed. `[LJ-1.6-R]`'s
   recommendation 6 and this row's ledger note both rest on the same misread.
3. **RUN ONE PROFILE, and it is the only measurement still owed.**
   `agda --profile=definitions` on `src/ProbeLJ117Pairing.agda` and
   `src/ProbeLJ117SquareLaw.agda`, one process, quiet machine, the declared
   caliber. About 45 s. It decides D17. Report the top ten rows and whether
   each one's TYPE carries a transparent construction.
4. **THEN decide the port, and the default is now GO.** The corrected
   arithmetic passes at every measured residue rate. Fund the port unless the
   profile in item 3 shows a cheap rewrite, in which case fund the rewrite.
5. **Send the level-size assembly with the TARGET SPLIT in its brief.** State
   the theorem as: for initial `κ` and every `β ≤ κ`, `⟪ Lset β ⟫ ↪ ⟪ κ ⟫`.
   Name `src/ProbeTowerInd2.agda:99-159` as the successor half and `birth`
   (`src/L/Choice/Step.lagda.md:133`, `:189`) as the limit coordinate. Gate the
   limit step, which is the one piece T85 did not build.
6. **Name the two residuals in that same brief:** the square law at `ω`, and
   the choice between verifying `Init κ` and adopting `Init` as the cardinal
   notion (`archive/.../SquareLaw.lagda.md:961-963`).
7. **Leave the square law in the wing bucket.** Section 5. Let `gch_assign`
   move it when a second consumer is real.
8. **A LESSONS candidate, with its measurement.** Proposed statement: *a
   seconds budget derived from a projected line count must be divided by the
   PROJECTED count, never by today's.* Measurement: this row produced a
   NO SHAPE FITS verdict at 0.0175 s per line against a 0.013193 bar, where
   the same measured seconds over the projected wing give 0.0087 to 0.0109, a
   pass at 0.72x to 0.82x. The error stood in a brief, a return and the ledger
   at once. The orchestrator assigns the ID.

## 8. LITERATURE USED

- `_build/literature/dev2.txt:200-215` (1.1(vii)'s whole proof). **USED and
  decisive.** Devlin proves no cardinal arithmetic. The limit step's
  `Σ_{α<λ}|α| = |λ|` is written bare, and the successor step's formula count
  is "easily seen". Section 2.1 rests on this.
- `_build/literature/dev2.txt:1357-1361` (5.4). USED. `|M| = max(|X|, ω)`, and
  the one-line proof by counting the formulas of `ℒ_X`.
- `_build/literature/dev2.txt:1373-1384` (5.5). **USED and decisive.** The
  printed chain `|γ| = |M| = |α| < κ`, and the `κ ≤ ω` triviality at `:1375`.
- `_build/literature/dev2.txt:1386-1391` (5.6). USED. The application is at
  `κ⁺`, and 1.1(vii) closes it.
- `dev/literature/devlin-II5.md:145-158` (1.5). USED. The digest of 5.5, which
  is the report's citation.
- `dev/literature/devlin-II5.md:164-166`. **USED and decisive, and this is the
  line the report missed.** The single application is `κ⁺` with `α = κ`. Both
  are cardinals. Error 2 rests on it.
- `dev/literature/devlin-II5.md:272-285` (2.5 and 2.6, steps E and F). USED.
  Step E is "cardinal arithmetic on a countable formula set", step F is "the
  level-size equation and initial-ordinal arithmetic". **The digest says
  INITIAL, and the report read it as arbitrary.**
- `dev/literature/devlin-II5.md:380-397` (section 4, the DD4 table). USED.
  Steps E and F are marked EITHER tower. The per-tower content is two objects.
  Section 5 rests on it.
- `dev/literature/devlin-II5.md:411-417` (5.2). USED. The J analogue
  `|J_ρ^A| = H_ρ^M`, and the note that 1.1(vii) bears only through 5.5's
  cardinal conclusion.
- `dev/literature/devlin-II5.md:346-348` (item 8). USED. The level-size
  equation is a hierarchy basic.
- `dev/literature/devlin-II5.md:420-428`. USED, through `[LJ-1.19]`. The
  wing's single condensation application.
- **SKIPPED**, with reasons. `devlin-II5.md` section 6, the OCR items: two
  earlier reviews checked both and agreed neither touches the counting
  (`_build/lj-1.6-review.md:507-512`, `_build/lj-1.15-review.md:432-437`). I
  did not re-check a question answered twice. `devlin-II5.md` 5.3 and 5.9 to
  5.11: they add no requirement beyond step C, by the digest's own words at
  `:425-432`. `dev/literature/j-hierarchy.md`: the J-side size analogue does
  not change the ordinal arithmetic underneath, and section 5 settles the DD4
  question from the tree instead. `dev/literature/devlin-errata.md`:
  `[LJ-1.14]` verified it does not cover Chapter II section 5.

## 9. ARCHIVE USED

- `archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md:936-944`: the boundary
  prose and the `Init ω` correction. `:952-963`: **the full paragraph**, whose
  second half names the least-of transfer and the cardinal-notion choice. The
  report quoted the first half. `:969-984`: `sq`, `Init` and `InitialCore`.
  TOOK: sections 2.4 and 2.5.
- `archive/rud-route/src/L/Ordinal/Pairing.lagda.md:108-109` (`ordSWO`),
  `:483-484` (`col→τ-fiber`), `:575` (`hit`). TOOK: the definition that carries
  the module's whole cost, for section 3.2.
- `archive/dev/TASKS-archived.md:133`: **the `[L3.32-T98]` row**, "Root cause:
  presentation or mathematics? COMPLETE". This is the row the brief demanded
  and the report cited one line off, at `:119`. Also `:120` (T85, GREEN) and
  `:94` (T59, RED gate). TOOK: the presentation-bound provenance.
- `_build/l3.32-t98-report.md:1-60`: the verdict "the cost is presentation, not
  mathematics", and the named falsifier. TOOK: the root-cause diagnosis behind
  section 3.2.
- `_build/l3.32-t103-report.md:21`, `:39-41`, `:79`, `:149-150`: the after
  profile totals 64,401 ms and its residual rows. **TOOK: the proof that the
  report's floor evidence is superseded**, section 3.1.
- `_build/lj-1.6-review.md:112-126` (the T85 probe contents and its 52-line
  and 12.8 s figures), `:283-284` (the caliber worry the measurement now
  kills), `:465-467` (the SCOPE recommendation the brief dropped),
  `:301-308` (the two directions of the level size). TOOK: sections 1, 2.3
  and 6.
- `_build/lj-1.6-report.md`, through the review: the delivered `Bound` and
  `Lower` halves. TOOK: the parameterization, section 4 route 3.
- `_build/lj-1.1-recon.md:135-153` (block 4, chapters 4a to 4g; 4c at `:141`,
  4d at `:143`, 4g at `:149`) and `:202-220`
  (section 6, the projection table). **TOOK: the square law's 1,283 lines sit
  INSIDE the a-priori band**, which is what makes section 1's arithmetic
  legitimate. Also 4g's 200 to 500 booking, for route 1.
- `_build/lj-1.15-review.md:356-364`: the J tower has no Def step and no
  carrier-indexed code set. `:298-308`: the crossing measured at 0.0052 s per
  line. TOOK: sections 1 and 5.
- `_build/lj-1.19-report.md:16-29`: the wing condenses exactly once, at a `λ`
  the consumer chooses freely. TOOK: section 2.2.
- `src/ProbeTowerInd2.agda:49-50` (`Init ω` refuted), `:99-153` (the successor
  module), `:155-159` (**the fixed-target signature**). **TOOK: the whole of
  section 2.3.** Untracked probe, in this working tree.
- `dev/ledger.toml:241` (a-priori lines), `:247-272` (the block that records
  the FAIL and the re-arm, both now wrong), `:273` (the budget), `:1411-1417`
  (the D-order-core lever, superseded, net 150 to 200), `:1754` (the 0.297
  figure and its true owner), `:1766-1785` ([T241]'s location of it),
  `:1796-1801` (the 23.3 and 18.6 rows), `:2379` (**the Pairing profile and the
  18.8 s once-payment**), `:2449-2462` (`gch_assign` and its dead-declaration
  guard), `:2475-2546` (the `[ratio]` block and both calibers), `:2765`
  (tolerance 1.15), `:2796-2800` (the declared wing). TOOK: every number in
  section 1 and the mechanism in section 5.
- `dev/LESSONS.md:2263-2299` (**P-l**, including the transplant table and the
  `SquareLaw` measurement at 3.424 s per obligation), `:2419-2432` (P-m),
  `:2442-2452` (P-n). TOOK: the class argument and route 5's warning.
- `dev/PLAN.md:181` (DD24's row, "no line cap and no seconds cap ... the
  omission is deliberate"), `:182` (DD25's trigger and its "a review that
  AGREES is a real result"). TOOK: route 4's framing.
- `scripts/check-ratio.py:20-24` and **`:38-41`** (the per-module flag is
  advice, the aggregate is the judgment), `:262-282` (the aggregate
  computation). **TOOK: the instrument's own rule**, section 1.
- `src/L/StageCardinal.lagda.md:14-17` (`sq` as a module parameter), `:52-58`
  (the comment naming `β` as the target), `:59-66` (`Bound`'s telescope),
  `:172-180` (`formula-bound`, generic in `K`), `:204-212` (`stage-card-lower`,
  the delivered lower half). TOOK: sections 2.2, 2.3 and 4. **CALIBER WARNING:
  a sibling was editing this file while I read it. It grew by 159 lines during
  my session, and every line number above moved by 8. Re-resolve by NAME.**
- `src/L/Choice/Step.lagda.md:133`, `:189`: `birth` and `birth-in`, through
  `_build/lj-1.6-review.md:151-153`. TOOK: the limit coordinate for route 1.

## 10. WHAT I AM NOT SURE OF

1. **The fixed-target re-shaping is my derivation plus one measured
   comparable.** The comparable is real and it is in the tree
   (`src/ProbeTowerInd2.agda:155-159`), and the digest's `α = κ` is the source
   (`dev/literature/devlin-II5.md:164-166`). **The limit step is neither built
   nor measured by anybody.** T85 priced its own limit half at 150 to 220
   lines and named the transport-stability lemma as its widest term. I did not
   re-price it. Route 1 should be gated on that step, not funded blind.
2. **I ran no Agda.** Every second in this review is somebody else's
   measurement. The three figures I lean on hardest, 41.36, 18.23 and 23.13,
   are `[LJ-1.17]`'s own and I could not re-run them. I checked them against
   the ledger's 18.6 and 23.3 and they agree within one percent.
3. **The 0.0065 residue rate is not measured at the declared caliber.**
   `[LJ-1.6-R]` took it from a brief and said so (`:559-563`). The
   caliber-measured wing rates are 0.0011 and 0.0052, both LOWER, so my pass
   is conservative. If the true wing rate is above 0.0093, the pass reverses.
   Nobody has measured a wing module above 0.0052.
4. **The wing's remaining line mix is unmeasured.** The crossing, its largest
   block, measured 0.0052 (`_build/lj-1.15-review.md:300-301`). The rest is a
   survey. My conclusion holds at every measured rate and I cannot certify the
   unmeasured mix.
5. **I did not price the ideal form either.** I show the report did not, and I
   name the 45-second profile that would settle it. **A refutation of a price
   is not a price.**
6. **The `ω` residual may be less trivial than it looks.** `ℕ × ℕ ↪ ℕ` is
   elementary, but placing it at `⟪ ω ⟫` through the tower's presentation is
   the exact shape P-l warns about. I give no number.
7. **`Init κ` verification.** I assume the wing takes `Init` as its cardinal
   notion, which the archive names as one of two options. If instead each
   `Init κ` must be proved, its fourth clause needs the square law below `κ`,
   and a non-initial site could return by that door. I did not chase it.

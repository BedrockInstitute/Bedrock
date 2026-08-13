# LJ-0.4f-R: the DD25 adversarial review of the recursion-assembly refusal

Status: COMPLETE. Read-only on `src/`. No Agda run. No commit, no push.
The one file written is this one.

## 1. VERDICT

**UPHOLD WITH A CONDITION.**

The NO-GO is correct. It is correct by a wider margin than the report
claimed. No arithmetic error moves it. The break-even gate gave the right
answer.

**The condition is that the report contains one FALSE finding, and that
finding hid a cure.** The report says `L.Choice.Before` is not a third
copy of the assembly. That is wrong. `Before` holds a full third copy of
the assembly's SHAPE half. The report read the region the T208 residue
named and did not look at the rest of the file.

The three headline numbers, ranked by what they cost:

| Rank | Finding | Status |
|---|---|---|
| 1 | The D-10 finding is FALSE. `Before` IS a third copy of the shape half, at `src/L/Choice/Before.lagda.md:714-766`, `:1213-1241` | overturned |
| 2 | A cheaper kit exists: ONE parameter, no new master, five site-instances, estimated **minus 106** | the return missed it |
| 3 | The funded third site does NOT exist. The GCH wing consumes `L.Hierarchy` and `L.Coding.Sequence` as delivered and never copies them (`_build/lj-1.1-recon.md:181`) | the refusal is right, for a stronger reason than it gave |
| 4 | The two-site net is about **plus 4**, not minus 4. The report's minus 116 for `Table` is its most optimistic estimate | the refusal survives either figure |
| 5 | The fold costs the tree **plus 1.5 cold seconds** and buys nothing. The report measured per file and never summed | the return missed it |
| 6 | The brief's write scope excluded `src/L/Coding/`, which removed the winning host | the brief's largest share |
| 7 | The kit is preserved but the WIRING is not. It lives only in volatile `/tmp` | act today |

Nothing here says land the 208-line kit. Do not land it.

## 2. THE THREE-SITE QUESTION

### 2.1 The premise fails

The report's DD4 paragraph says the GCH wing "builds a recorded-graph
assembly over a stage" (`_build/lj-0.4f-report.md:181-182`). The funded
wing plan says the opposite.

`_build/lj-1.1-recon.md:181`, the wing's own DD4 paragraph:

> It leaves the delivered machinery alone: L.Hierarchy, L.Coding.Sequence,
> L.Coding.Powerset, FOL.Absoluteness, FOL.LevyHierarchy are consumed as
> delivered, never copied.

I read all six funded blocks (`_build/lj-1.1-recon.md:91-174`). None
builds an object-language recorded-graph recursion.

| Block | What it builds | Does it need the kit |
|---|---|---|
| 1 Skolem hull | a least-witness search over the delivered order | no |
| 2 Mostowski collapse | a META `∈-recursion` over an abstract carrier (`:107`) | no |
| 3 Condensation | Levy certification and four transfer obligations | no |
| 4 Cardinal chain | counting, pairing, square law, cardinality | no |
| 5 Subsets early | one step consuming blocks 1 to 4 | no |
| 6 Assemble GCH | one sentence in the `ChoiceStatement` shape | no |

Block 2 is the only recursion, and it is a meta-language `∈-induction`
with no `domAt`, no `appAt`, no satisfaction and no replacement. The kit
is about the OBJECT-language recorded graph. It does not fit.

The wing instead RIDES the existing assembly: `_build/lj-1.1-recon.md:197`
says "riding `Lset-only` (Hierarchy.lagda.md:333) and `Lset-defines`
(Hierarchy.lagda.md:678). No re-proved graph theorem may enter."

### 2.2 The J tower is where a third site would live, and it is not funded

DD2 rules the ENDPOINT and leaves the ARCHITECTURE open
(`dev/PLAN.md:161`): "WHAT IS A CANDIDATE: the two towers and the bridge,
L plus J through rud. It is the leading architecture and the plan builds
toward it. It is not yet the binding ruling."

The ruling sits at `[LJ-2.5]` (`dev/PLAN.md:450`), which needs LJ-2.0,
2.1, 2.2 and 2.4 first. DD5 adds: "None of it is funded yet: the owner's
priority is the AC-side compression" (`dev/PLAN.md:163`).

So the third site for THIS kit is behind an unruled architecture decision.
It is a hope, not funded work.

### 2.3 The arithmetic, with the third site priced anyway

MEASURED figures are marked. ESTIMATED figures are marked.

| Term | Lines | Basis |
|---|---:|---|
| kit `L.RecAssembly` | +208 | MEASURED, `ledger.count`, I re-ran it |
| site 1 `L.Hierarchy` | -96 | MEASURED, 350 to 254, I re-ran both |
| site 2 `L.Choice.Table` | -108 | ESTIMATED by me, range -100 to -112 |
| **two-site net** | **+4** | ESTIMATED, range -12 to +12 |
| hypothetical site 3 | -105 | ESTIMATED, and unfunded |
| three-site net | -101 | ESTIMATED |

At two sites the block misses the minus 60 floor by about 64 lines. At
three sites it would clear it. **The gate is right because the third site
is not real.**

### 2.4 Does `[LJ-0.8]` 7.7 reach this case

Yes. It reaches it exactly.

`_build/lj-0.8-review.md:521-524` sets the test: "Landing a net-positive
kit now spends the campaign's own meter, and postponement costs nothing IF
the kit survives and a trigger exists. Neither condition holds today: two
kits are deleted and no trigger is registered."

Both conditions hold for LJ-0.4f. The kit survives at
`_build/kits/lj-0.4f-recassembly.lagda.md`, byte-identical to the version
that typechecked (I compared the SHA-256 against
`/tmp/lj04f-clone/src/L/RecAssembly.lagda.md`). The trigger is stated at
`_build/lj-0.4f-report.md:191`.

7.7's repair also names where a revived kit should land:
`_build/lj-0.8-review.md:537-539` says "A kit landed here counts as shared
code (DD4) and lands inside the wing's own budget, where DD5 measures it
honestly." That is the correct home for this kit if the J tower is ever
ruled.

The orchestrator asked whether B, E and G differ because they had no
funded second consumer while this one names a funded third. **The
difference does not survive the check.** This one does not name a funded
third consumer either. It names an unruled one.

### 2.5 DD4, answered as a judgment with numbers

DD4 argues FOR a shared assembly and AGAINST THIS shared assembly.

The kit shares the VALUE recursion: `P`, `uniq`, `step`, `step-back`, the
`∈-induction` over ordinals. That content has two consumers today and no
third in any funded plan.

The kit also shares the SHAPE: `ApproxAt`, `GraphAt`, the four read
lemmas, `GraphOf`, and the pair graph. That content has **five site-
instances in four files today** (section 6). DD4 points straight at it.

The literature says why the split falls there (section 8). SZ states the
hierarchy sequence and the order sequence as TWO lemmas with ONE form.
The form is shared. The value is not.

## 3. THE NUMBERS, CHECKED

### 3.1 The clone baseline is honest. I verified it

The report claims its three files are byte-identical at HEAD
(`_build/lj-0.4f-report.md:36-38`). Verified by SHA-256.

| File | main HEAD `ee58312` | clone HEAD `c6ffc94` | clone worktree |
|---|---|---|---|
| `src/L/Hierarchy.lagda.md` | `11443013` | `11443013` | `405b90d6` (wired) |
| `src/L/Choice/Table.lagda.md` | `1d3eaf8c` | `1d3eaf8c` | `1d3eaf8c` |
| `src/L/Choice/Before.lagda.md` | `9d32bfd2` | `9d32bfd2` | `9d32bfd2` |

The clone sits at an older HEAD than the tree. The three files did not
move between the two commits. The before-and-after pair ran on the same
clone. **The baseline is sound and the delta is internally consistent.**

### 3.2 The minus 96 is real and is a SAVING, not a relocation

I re-ran the ledger count with `at_head=False`.

| File | count |
|---|---:|
| `src/L/Hierarchy.lagda.md` at HEAD | 350 |
| `/tmp/lj04f-clone/src/L/Hierarchy.lagda.md` wired | 254 |
| `_build/kits/lj-0.4f-recassembly.lagda.md` | 208 |

All three match the report. The delta is minus 96.

**It is not block C's failure.** C took `Sound` from 801 in-fence lines to
seven and `Unique` from 630 to eleven. The wired `Hierarchy` keeps 254
lines and keeps its own mathematics: the `Values`/`Entries`/`Domain`
triple (`/tmp/lj04f-clone/src/L/Hierarchy.lagda.md:115-123`), the step
pair, `hier-out`, `hier-in`, the sealed `hierAt`, and `Lset-defines`. A
chapter remained a chapter.

**One relocation charge does stick, and it is small.** The kit spends 18
lines on `Values₀`, `Domain₀`, `Entries₀` and the `Assembly` aliases (kit
`:45-54` and `:101-114`). The site keeps its own triple anyway, so those
18 lines replace nothing. `Hierarchy`'s triple IS definitionally
`Values₀ P`, `Entries₀ entered` and `Domain₀`, so the site could have
aliased it and saved about 5 more lines. **The measured minus 96 is
therefore about 5 short of what this kit shape can reach. That does not
move the verdict.**

### 3.3 The minus 116 for Table is an ESTIMATE, and it is the optimistic end

The report gives two Table figures and both are projections
(`_build/lj-0.4f-report.md:69` and `:56-57`). Neither is a measurement,
and section 10 says so honestly.

I priced Table's replaceable surface by counting the actual blocks at
ledger caliber.

| Block | file:line | in-fence |
|---|---|---:|
| `ApproxAt`, `GraphAt`, four reads, `GraphOf`, `Graph-in`, `Graph-out` | `src/L/Choice/Table.lagda.md:406-446` | 31 |
| `approx-val`, `approx-uniq` | `:473-505` | 29 |
| `graph-only`, `graph-table` | `:531-580` | 45 |
| `PairGraphAt`, `PairOf`, `PairGraph-in`, `PairGraph-out` | `:601-622` | 17 |
| **gross deletable** | | **122** |

Table's instantiation is CHEAPER than Hierarchy's, because Table's
`Entries` is already the truncated existential. `Hierarchy` paid 20 lines
(`/tmp/lj04f-clone/src/L/Hierarchy.lagda.md:243-262`). Table would pay
about 16. Imports drop about 2.

So Table nets about **minus 108**, range minus 100 to minus 112. The
report's minus 116 is outside my range on the optimistic side. The
report's minus 96 is 12 too pessimistic.

**Two-site net: about plus 4.** The orchestrator's framing that "at two
sites the kit is roughly FREE today" rests on the report's best case. The
central estimate is that the kit costs about 4 lines at two sites.

Break-even by my figures is 208 divided by 102, which is **2.04 sites**.
The report's 2.17 is close. The gate fires on either number.

### 3.4 The report's module-order obstruction is not real

`_build/lj-0.4f-report.md:171-174` says Table cannot instantiate the kit
because "`Described`'s condition hypotheses are stated at the top-level
triple. The kit's `Step` parameter is defined inside `Described`. The two
cannot both be opened at the top level."

Both halves of that sentence are true and the conclusion does not follow.
Table instantiates `Assembly` INSIDE `Described`, after
`src/L/Choice/Table.lagda.md:361`, where `StepAt` exists. `Values`,
`Entries` and `Domain` are top-level at `:294-305` and are in scope there.
I checked every one of the eleven parameters against a Table witness:

| kit parameter | Table's witness | file:line |
|---|---|---|
| `P` | `IsRel` | `Table:166-167` |
| `P-prop` | `snd (Realizes c r)` | `Table:162-163` |
| `entered` | the truncated existential | `Table:299-301` |
| `entered-res` | identity, `entered` ignores `B` | `Table:299-301` |
| `uniq` | `rel-unique` | `Table:174-175` |
| `Step` | `StepAt` | `Table:361-362` |
| `step` | `step-rel` | `Table:372-375` |
| `step-back` | `step-table` | `Table:377-380` |
| `to-entered₀` | `domAt-in` under the transitivity step | `Table:497` |
| `to-entered₂` | `ApproxAt-value` | `Table:545` |
| `to-exists` | `ents c c∈`, identity | `Table:561` |

I could not typecheck this, because C-12 gives the Agda slot to LJ-0.4m.
It is a reading, not a measurement. **But the report refused on
arithmetic, not on this obstruction, so the error is a record defect and
not a wrong verdict.**

### 3.5 The seconds, summed, which the report never did

The report reports per file and stops. Sum them.

| Term | seconds | status |
|---|---:|---|
| kit `L.RecAssembly`, new module | +1.50 | MEASURED |
| `L.Hierarchy` delta | -0.27 | MEASURED, and NOISE under the rule |
| **whole-tree delta at one site** | **+1.23** | MEASURED, and positive in every reading |

The tree gains a module that costs 1.50 s and saves nothing measurable.
At one site the fold adds 112 lines AND 1.23 seconds. Both terms move the
wrong way.

The increment's rate is 1.23 divided by 112, which is **0.011 s per line**.
The AC wing's measured rate is 0.007614 s per line (`dev/PLAN.md:174`). So
the increment checks at about 1.4 times the tree's own rate. **Landing this
kit would make the AC tree slightly worse on the DD24 meter as well as on
the line meter.** That is a second independent reason to refuse, and the
report did not compute it.

The kit's own rate is 1.50 over 208, which is 0.0072 s per line. That sits
just below P-m's parameterized floor of 0.010 to 0.013
(`dev/LESSONS.md:2254`). The kit is honest parameterized content. It is
just content nobody needs twice.

### 3.6 One number in the orchestrator's own framing is stale

The prompt says the AC side stands at 17,166 and 184 lines are owed.
17,166 minus 17,000 is 166, not 184.

`.venv/bin/python scripts/ledger.py --brief` at HEAD `ee58312` reports
"AC closure 17,166". `--trophy-split` reports "ac-total 17,166". So the
measured gap at HEAD is **166**.

The tree is also moving under this review. LJ-0.4m is editing three files
right now and its report claims minus 68 more
(`_build/lj-0.4m-report.md:7-8`). If that lands, the AC side reaches
17,098 and the gap becomes **98**. Re-measure before quoting either.

## 4. THE BRIEF'S SHARE

### 4.1 The write scope removed the winning move. This is the brief's largest share

`_build/briefs/LJ-0.4f.md:210-211`: "Never `src/L/Coding/`, never
`src/L/Axioms/`, never `src/FOL/`."

`src/L/Coding/Sequence.lagda.md` holds a third live copy of the shape half
(`:281-307` and `:361-379`, 38 in-fence lines) and it is the ONLY host
that costs no new preamble. A new master costs about 26 in-fence lines
before any content: the kit's preamble is 26 (`kit:12-43`) and
`Hierarchy`'s is 27 (`Hierarchy:40-70`). Section 6's cure needs that host.

**The exclusion was correct for safety.** The brief says LJ-0.4i held
`src/L/Coding/` (`_build/briefs/LJ-0.4f.md:103`), and C-25 forbids two
writers on one file. So the brief made the right call for the wrong
outcome. The lesson is that a concurrency exclusion should be recorded as
a COST in the return, so the block can be re-run when the slot frees.

### 4.2 The break-even gate cannot be run as written

`_build/briefs/LJ-0.4f.md:72-77`: "THE BREAK-EVEN GATE, before any wiring.
Write the kit and typecheck it. Count its in-fence lines. Compute
break-even as kit lines divided by the measured saving per site."

There is no MEASURED saving per site before a site is wired. The gate
contradicts itself. The agent resolved it correctly by wiring one site and
then gating, which is the staging gate at `:78`. **Fix the wording to
"before wiring the SECOND site."** This is inherited from
`_build/lj-0.8-review.md:343-348` and it should be fixed there too.

### 4.3 The fixed floor did NOT cause the outcome

The minus 60 floor at `_build/briefs/LJ-0.4f.md:60` was fixed before any
measurement. That is right, and I would keep it.

It did not make a marginal result read as a failure. The measured and
estimated two-site net is about plus 4. The block fails at ANY negative
floor. It fails at a floor of zero. The floor's exact value is not
load-bearing here. **Fixing it in advance prevented a post-hoc
rationalization, which is exactly what it is for.**

### 4.4 Eleven parameters follow partly from the brief

Two brief clauses drove the telescope.

- `:209` allowed "at most ONE new shared module". One module for both
  halves forces one telescope covering both.
- `:51-52` said "Fold ONE pair only: `Hierarchy`'s triple onto `Table`'s".
  That framed the job as folding the TRIPLES.

The report found the triples do not share a shape and adapted correctly
(`_build/lj-0.4f-report.md:81-92`). That is a good D-10 catch and the brief
licensed it at `:197`.

**But nothing in the brief told the agent it could split the kit by
content.** The one-module clause reads as one telescope. Section 6 shows
that the cheap half needs ONE parameter and the expensive half needs
eleven, and that they should not travel together.

### 4.5 Merging LJ-0.8's two steps into one dispatch was RIGHT

`_build/lj-0.8-review.md:396-397` asked for a THROWAWAY probe: "nothing
lands, nothing is committed, the deliverable is a report with two numbers."

The merged brief produced exactly that deliverable in one dispatch AND it
preserved the kit, which a throwaway probe would have destroyed. E and G
lost their kits that way (`_build/lj-0.8-review.md:377-379`). The merge
cost nothing and gained the artifact. **Keep the merged form.**

### 4.6 Kit preservation is half done, and the missing half is volatile

`_build/kits/lj-0.4f-recassembly.lagda.md` is preserved and verified
byte-identical to the typechecked module. Good.

**The WIRING is not preserved.** The wired `Hierarchy` exists only at
`/tmp/lj04f-clone/src/L/Hierarchy.lagda.md`. That is the expensive
artifact: it is the proof that eleven parameters suffice, and it took the
dispatch to derive. `/tmp` is volatile. `_build/lj-0.8-review.md:379`
criticized block B for exactly this. Save the diff today.

## 5. THE D-10 FINDING, VERIFIED, AND WHAT IT PUTS IN DOUBT

### 5.1 Half right, and the wrong half is expensive

The report makes three D-10 claims. Two are right.

**RIGHT.** The named triples do not share a shape. `Hierarchy:116-124` is
`Values`/`Entries`/`Domain`. `Table:158-167` is `Related`/`Realizes`/
`IsRel`, which is a class predicate and not the analogue. The real
analogue is `Table:295-304`. I read all three and the report is correct.
The brief pointed at the wrong region and the report corrected it.

**RIGHT.** The pipeline below the triples does share a shape.

**WRONG.** `_build/lj-0.4f-report.md:102-106`: "`Before`'s region at
`src/L/Choice/Before.lagda.md:229-398` is a different mechanism. It is a
direct recursion over `ℕ` with separation. It has no graph, no
approximation, and no replacement. The third copy claim is false at the
mechanism level."

The region description is accurate. `relAt` at `Before:229-233` is a
direct `ℕ` recursion by `hasSeparationL`. The CONCLUSION is false.
`Before` holds a full assembly further down the same file.

| Component | file:line | in-fence |
|---|---|---:|
| `RelStepAt`, `RelStep-out/back/in` | `Before:684-712` | 25 |
| `ApproxAt`, `ApproxAt-dom/value/step/in` | `Before:714-746` | 27 |
| `RelGraphAt`, `GraphOf`, `RelGraph-in/out` | `Before:747-766` | 15 |
| `Values`, `Entries` | `Before:796-803` | 5 |
| `approx-val`, `approx-ent` | `Before:986-1014` | 24 |
| `rel-only` | `Before:1015-1026` | 12 |
| `approxSet-approx`, `relAt-graph` | `Before:1100-1190` | 80 |
| `PairRelGraphAt`, `PairOf`, `PairRelGraph-in/out` | `Before:1213-1241` | 24 |
| **total** | | **212** |

The file says so itself, in two places, in plain words.

- `Before:15-17`: "what gets described is an approximation, exactly as the
  tower and the order table were described: an approximation predicate, a
  graph quantifying over approximations, a value lemma pinning every value
  an approximation records".
- `Before:1635-1636`: "`RelStepAt`, `ApproxAt` and `RelGraphAt` follow the
  template".

**One `grep -n ApproxAt src/L/Choice/Before.lagda.md` would have found
it.** The report checked the residue's REGION and never checked the
residue's CLAIM.

### 5.2 The corrected target, which D-10 asks for and the report did not give

D-10 says "record the corrected target beside the original"
(`dev/LESSONS.md:1302-1306`). The corrected target is:

> `Hierarchy`, `Table`, `Before` and `Coding.Sequence` share the assembly's
> SHAPE half: the approximation formula, its four read lemmas, the graph
> formula, its two read lemmas, and the pair graph. They do NOT share the
> INDUCTION half: `Hierarchy` and `Table` induct over ordinals by
> `∈-induction`, while `Before` inducts over `ℕ` by `WFI.induction`
> (`Before:995`) with `Values g k = (m : ℕ) → m < k → ...`
> (`Before:797-799`).

That split is the whole finding, and section 6 turns it into arithmetic.

### 5.3 The residue itself named the wrong region

`_build/l3.32-t208-report.md:220-223` names "the `relAt`/`At` tower in
`Before` (:229-398)". The residue picked the wrong region. The report
inherited the error and stopped at "false".

The residue's SIZE figure was closer to the truth than its region. It says
Before's assembly region is "about 188" lines. The region it named
measures 160 in-fence. The real assembly measures 212.

### 5.4 What else in the T208 report should now be distrusted

The defect class is: **T208 priced levers by REGION LINE RANGES taken from
a scan, and it never verified that the range holds the mechanism it
names.** `_build/l3.32-t208-report.md:305-308` admits the class in its own
words: "The frame designs are statement changes. Their consumer lists are
unverified at the typechecker."

Distrust every T208 figure whose basis is a named line range rather than a
mechanism grep.

| Lever | T208 section | Why it is now in doubt |
|---|---|---|
| (f) recursion assembly | 3.6 | PROVED WRONG here. One of three regions was misidentified |
| (c) the `∃ⁿ`-with-`∧` frame combinator | 3.3 | Consumer list "unverified at the typechecker" by T208's own admission (`:305-307`). Measured plus 24 by LJ-0.4b, so the region survey already failed once |
| (d) frame retrofit of the pre-law chapters | 3.4 | Same basis, same admission. Refused by LJ-0.4c at minus 59 by gutting two chapters |
| (b) verbatim-repeat extraction | 3.2 | Region-based. LJ-0.8 later measured the repeat surface at ZERO 4-line blocks over 1,289 lines (`_build/lj-0.8-review.md:386-390`) |
| (g) sealed-constant dedupe | 3.7 | Region-based and never attempted |

**The one that should be re-checked, not re-refused:** lever (f) itself.
Its region survey was wrong in BOTH directions. It missed 52 lines of
assembly in `Before` and it never counted `L.Coding.Sequence` at all.

## 6. A CHEAPER KIT

**The class is NOT closed. A cheaper kit exists.** It needs ONE parameter,
not eleven. It needs NO new master. It has five site-instances in four
files today.

### 6.1 The shape

Split the assembly on the boundary the literature draws (section 8).

- **The SHAPE half is generic in `Step` alone.** Nothing in it mentions
  the recursion's value, its uniqueness, or its induction. Check the kit
  itself: `ApproxAt₀` and `GraphAt₀` at `kit:56-64` take only `Step`.
  `Domain₀` at `kit:49-50` takes nothing. The `ApproxAt-*` block at
  `kit:116-136`, the `GraphOf` block at `kit:138-148`, and the pair graph
  at `kit:235-254` use only `domAt-out`, `domAt-in`, `appAt-adequate`,
  `prAtL` and `prAtL-adequate`, all of which `L.Coding.Model` already
  exports.
- **The INDUCTION half needs the whole eleven-parameter telescope**, and
  it has two consumers. Leave it at the sites. That is what LJ-0.4f
  measured, and the measurement stands.

### 6.2 The generic module, priced

One parameter: `Step : ∀ {n} → Fin n → Fin n → Fin n → Formula S n`.

| Content | source | in-fence |
|---|---|---:|
| `Domain₀` | `kit:49-50` | 3 |
| `ApproxAt₀`, `GraphAt₀` | `kit:56-64` | 8 |
| `ApproxAt-dom/value/step/in` | `kit:116-136` | 18 |
| `GraphOf`, `Graph-in`, `Graph-out` | `kit:138-148` | 9 |
| `PairGraphAt`, `PairOf`, `PairGraph-in/out` | `kit:235-254` | 17 |
| module header | | 1 |
| **total** | | **56** |

**Host it inside `src/L/Coding/Sequence.lagda.md`**, which already holds a
copy and already pays the preamble. A new master would add about 26 lines
for nothing.

### 6.3 The sites, MEASURED

Deletable blocks, counted at ledger caliber by me today.

| File | Block | file:line | in-fence |
|---|---|---|---:|
| `L.Coding.Sequence` | `ApproxAt` and four reads | `:281-307` | 23 |
| `L.Coding.Sequence` | `LsetGraphAt`, `GraphOf`, two reads | `:361-379` | 15 |
| `L.Choice.Table` | shape block | `:406-446` | 31 |
| `L.Choice.Before` | shape block | `:714-746` | 27 |
| `L.Choice.Before` | graph block | `:747-766` | 15 |
| `L.Hierarchy` | pair graph | `:448-476` | 21 |
| `L.Choice.Table` | pair graph | `:601-622` | 17 |
| `L.Choice.Before` | pair graph | `:1213-1241` | 24 |
| **gross deletable** | | | **173** |

`L.Hierarchy` is a fourth CONSUMER of the shape half. It imports it from
`Sequence` today (`Hierarchy:57-60`), so it holds no copy of it.

### 6.4 The arithmetic

Deletions are MEASURED. Instantiation costs are ESTIMATED.

| File | deletes | pays | net |
|---|---:|---:|---:|
| `L.Coding.Sequence` hosts and re-exports | -38 | +56 +4 | **+22** |
| `L.Choice.Table` shape and pair | -48 | +3 | **-45** |
| `L.Choice.Before` shape and pair | -66 | +3 | **-63** |
| `L.Hierarchy` pair | -21 | +1 | **-20** |
| **total** | **-173** | **+67** | **-106** |

At doubled instantiation costs the net is minus 95. **It clears the minus
60 floor with room.**

### 6.5 The gate this block must pass FIRST, and it is a seconds gate

**`Before` is the site that makes it pay, and `Before` is sealed.**

Without `Before` the net is plus 22 minus 45 minus 20, which is **minus
43**. That MISSES the minus 60 floor. So the block is decided at `Before`.

`Before:684`, `:714`, `:747` and `:1224` put `RelStepAt`, `ApproxAt`,
`RelGraphAt` and `PairRelGraphAt` inside `opaque` blocks. The chapter
records what the seal is worth, measured in this file
(`src/L/Choice/Before.lagda.md:680`): unsealed the chapter runs 376
seconds, sealed it runs 3.8 seconds. That is 99 times.

Moving a sealed definition into a parameterized module and re-sealing
through a module instance is not a move this tree has measured. P-l's own
table records four of five cure transplants failing
(`dev/LESSONS.md:2120-2129`), and R-38's seal transplant measured ZERO.

**So the brief for this block orders `Before` FIRST, not last.** Wire
`Before`'s shape block, measure cold seconds, and stop on any rise. If
`Before` holds, the rest is bookkeeping. If `Before` fails, the block is a
refusal with a number and it costs one file instead of four.

### 6.6 Why this is not P-r

P-r bans a fold whose result type every consumer must UNFOLD
(`dev/LESSONS.md:2327`). This is not that shape. The consumers see
`A.ApproxAt f a`, which is the same `Formula S n` they see now, and the
read lemmas keep their types. The LJ-0.4f measurement is the evidence: a
heavier eleven-parameter fold at one site measured seconds-flat.

### 6.7 Two smaller cures the return also missed

- **Alias the site triple.** `Hierarchy` kept its own
  `Values`/`Entries`/`Domain` (`:115-123`) although they are
  definitionally `Values₀ P`, `Entries₀ entered` and `Domain₀`. Aliasing
  saves about 5 lines per site. Small, and it makes the kit's 18 lines of
  triple plumbing pay for something.
- **`Table` does not import `L.Coding.Sequence` today.** Adding it is one
  line and it is already counted above. No cycle: `L.Coding` does not
  import `L.Choice`.

## 7. WHAT THE ORCHESTRATOR SHOULD DO NEXT

Ordered. The first three cost minutes.

1. **UPHOLD the NO-GO. Do not land `L.RecAssembly`.** Record that the
   review agrees and that it found the two-site net to be about plus 4
   rather than minus 4.

2. **Save the wiring before `/tmp` clears.** One command:
   `git -C /tmp/lj04f-clone diff src/L/Hierarchy.lagda.md > _build/kits/lj-0.4f-hierarchy-wiring.diff`.
   The 20-line instantiation at
   `/tmp/lj04f-clone/src/L/Hierarchy.lagda.md:243-262` is the proof that
   eleven parameters suffice. It is the part a revival cannot re-derive
   cheaply.

3. **Correct the record.** `dev/PLAN.md:422`'s LJ-0.4f row says "D-10 cut
   the premise: Before is a direct ℕ-recursion, not a third copy." **That
   sentence is false.** Amend it to: "D-10 half cut the premise: Before's
   `relAt` region is a direct ℕ-recursion, but Before holds a full third
   copy of the assembly's SHAPE half at `:714-766` and `:1213-1241`. The
   review found it." A wrong residue verdict on the record is exactly what
   D-10 exists to stop.

4. **Dispatch the split kit as a NEW block, tier codex.** Territory
   `src/L/Coding/Sequence.lagda.md`, `src/L/Choice/Table.lagda.md`,
   `src/L/Choice/Before.lagda.md`, `src/L/Hierarchy.lagda.md`. No new
   master. Estimated minus 106, floor minus 60. **Order `Before` first and
   gate on its cold seconds**, because `Before:680` records a measured 99x
   seal. Wait for the `src/L/Coding/` slot to free.

5. **Fix the standing break-even gate's wording**, in
   `_build/lj-0.8-review.md:343-348` and in every brief that pastes it.
   "Before any wiring" cannot be run. It should read "before wiring the
   second site".

6. **Add a seventh standing gate.** "Count the SITES by grepping the
   mechanism across the whole tree, not by trusting a residue's line
   range. Report the grep and the per-site line counts before you write
   the kit." T208's lever (f) survey was wrong in both directions: it
   misread `Before` and it never counted `L.Coding.Sequence`.

7. **Also add: sum the seconds.** A new module's own check time is a cost
   the tree pays forever. LJ-0.4f measured plus 1.50 s and never added it
   to the ledger of the decision.

8. **Tell the owner the honest position.** The 208-line kit does not pay
   and the target is not reachable through it. The measured gap at HEAD is
   166, not 184. LJ-0.4m is mid-flight for another minus 68. The split kit
   is a real remaining lever at an estimated minus 106, and it is gated on
   one seconds measurement at `Before`. **That is a path, not a promise.
   Do not quote minus 106 as a measurement.**

## 8. LITERATURE USED

**Read.**

- `dev/literature/digest.md:209-262`, section 3, the hierarchy and the
  order. Taken: SZ Lemma 1.10 states the S-sequence is a member of the
  next J-level and that "x = S_γ^A" is uniformly Sigma-1 by an
  alpha-independent formula (`:216-221`). SZ Lemma 1.11 states the SAME
  two properties for the order sequence (`:238-241`).
- `dev/literature/j-hierarchy.md:118-150`, section 3, the canonical
  well-order. Taken: the verbatim SZ 1.11, "(1) For all β < α,
  `< <^A_γ ; γ < β >` ∈ J_α^A ... (2) `< <^A_γ ; γ < α >` is uniformly
  Σ_1^{J_α^A}" (`:141-145`).

**The answer to the brief's question.** The literature treats them as
**TWO objects with ONE form.** They are two lemmas, 1.10 and 1.11, over
two different recursions, and each lemma has the identical two clauses:
the sequence is an element of the next level, and its membership statement
is uniformly Sigma-1 by an alpha-independent formula.

**This decides the kit's shape, and it supports the refusal for a reason
the report never gave.** A kit generic in the VALUE unifies what SZ keeps
apart. A kit generic in the SHAPE captures exactly what SZ states twice in
one form. The cure in section 6 falls on the literature's own boundary.

**The literature also predicts the copy the report denied.** `Before` is
the order recursion at finite stages. SZ 1.11 covers the whole order
sequence, so `Before` sharing the form with `Table` is what the text
predicts. The report declared it a different mechanism and the text says
otherwise.

**Two corrections to the record.**

- `_build/lj-0.4f-report.md:211-214` says a unified type "would be a
  category error". **Correct, and only for the value.** The report drew no
  line, so it reads as banning the shape share too.
- `_build/lj-0.8-review.md:541-545` says "the literature treats the
  S-sequence recursion and its uniform internal statement as ONE object,
  which lends F's unification architectural legitimacy." **This does NOT
  contradict LJ-0.4f.** LJ-0.8 is speaking about the S-sequence and its
  own internal statement. LJ-0.4f is speaking about the hierarchy and the
  order. Both are right. Read together they look like a conflict and they
  are not.

**WHY NOT the rest of `dev/literature/`.**

- `rudimentary-functions.md`, `fine-structure.md`: the rud basis and fine
  structure. Neither speaks to whether two internal recursion descriptions
  share one shape.
- `geology.md`: set-theoretic geology, a different subject.
- `devlin-errata.md`, `primary-sources.md`, `BIBLIOGRAPHY.md`: source
  provenance and corrections, no bearing on code shape.
- `formalizations.md`, `formalizations-landscape.md`: other people's
  formalizations, no bearing on this tree's module split.
- `owner-notes-rud.md`: reconciled inside `digest.md` section 4, already
  read there.
- `glossary-review-2026-08.md`, `terms-2026-08.md`: terminology, and DD19
  forbids me settling a term anyway.

## 9. ARCHIVE USED

- `_build/lj-0.8-review.md:340-379` (7.1, the six standing gates). Took
  the break-even gate and the kit-preservation gate. Found the break-even
  gate self-contradictory at `:343-348`. See section 4.2.
- `_build/lj-0.8-review.md:393-431` (7.3, this task's origin). Took the
  throwaway-probe design and judged the orchestrator's merge of it. See
  section 4.5.
- `_build/lj-0.8-review.md:519-539` (7.7, the DD4 revival trigger). Took
  the two postponement conditions and applied them. Both hold. See section
  2.4.
- `_build/lj-0.8-review.md:541-545` (8, literature used). Took the
  S-sequence gloss and reconciled it against LJ-0.4f's. See section 8.
- `_build/lj-0.4b-report.md:9-17`. Took the one-site anchor shape: kit 43,
  one site minus 19, all sites about minus 6. The same arithmetic shape as
  here.
- `_build/lj-0.4e-report.md:16-24`. Took the refused-kit table form: kit
  31 against three wired sites for plus 19.
- `_build/l3.32-t208-report.md:215-238` (3.6) and `:316-320`. Took the
  triplication claim and the queued probe. **Found the residue's `Before`
  region wrong.** See section 5.3.
- `_build/l3.32-t208-report.md:300-310`. Took T208's own admission that
  its consumer lists are unverified. Used it to rank what else to
  distrust. See section 5.4.
- `_build/lj-1.1-recon.md:87-183` (the six blocks and the wing's DD4
  paragraph). Took the finding that the wing consumes `L.Hierarchy` and
  `L.Coding.Sequence` as delivered and never copies them. **This is what
  settles the three-site question.** See section 2.1.
- `_build/lj-1.1-recon.md:196-197`. Took "No re-proved graph theorem may
  enter."
- `_build/lj-0.4m-report.md:7-8`. Took the sibling's claimed minus 68 to
  correct the standing figure. See section 3.6.
- `dev/memos/simplification-register.md:33-38` (S13 to S18). Read. **None
  proposes this shape.** S17 is the nearest and it is a FOL syntax-walk
  calculus, gated, and additive only. I re-propose nothing from the
  register.
- `dev/LESSONS.md:1302-1345` (D-10). Took "record the corrected target
  beside the original". The report did not. See section 5.2.
- `dev/LESSONS.md:2099-2129` (P-l). Took the transplant table, four of
  five cures failed. Applied it to the `Before` seal risk. See section 6.5.
- `dev/LESSONS.md:2254-2270` (P-m). Took the parameterized rate of 0.010
  to 0.013 s per line. The kit measured 0.0072. See section 3.5.
- `dev/LESSONS.md:2327-2360` (P-r). Took the fold-unfold test and found
  this fold is not that shape. See section 6.6.
- `dev/LESSONS.md:2427-2450` (P-q). Took "a line lever is not a seconds
  lever" and used it in the opposite direction: this line lever COSTS
  seconds.
- `dev/LESSONS.md:174-196` (P-h). Took "parameterize the MODULE". Both the
  refused kit and my proposal obey it.
- `dev/PLAN.md:161` (DD2). Took that the two-tower architecture is a
  CANDIDATE ruled at `[LJ-2.5]`. See section 2.2.
- `dev/PLAN.md:163` (DD5). Took "None of it is funded yet".
- `dev/PLAN.md:174` (DD24). Took the AC wing's 0.007614 s per line and
  compared the fold's increment rate. See section 3.5.
- `dev/PLAN.md:175` (DD25). Took the review's own charter.
- `dev/PLAN.md:422,450` (section 11 rows). Took the LJ-0.4f row, which
  carries the false D-10 sentence, and the LJ-2.5 row.

**WHY NOT the four retired-route archives.** I did not open
`archive/dev/TASKS-archived.md`, `archive/dev/JOURNAL-archived.md`,
`archive/dev/DECISIONS-archived.md` or `archive/dev/STATUS-archived.md`.
The question is whether four LIVE masters share a shape and what a kit for
them costs. Every figure comes from counting today's tree. The retired rud
route holds no site and no live consumer. `_build/lj-1.1-recon.md:235-258`
already surveys the archived modules for the wing, and none is an
object-language recorded-graph assembly.

## 10. WHAT I AM NOT SURE OF

1. **I ran no Agda.** C-12 gives the slot to LJ-0.4m. Every claim about
   what typechecks is a reading of the code. The eleven-parameter Table
   witness table in section 3.4 is the largest such reading.
2. **The minus 106 is not a measurement.** Its deletions are measured line
   counts of real blocks. Its instantiation costs are my estimates,
   anchored on ONE measured comparable: `Hierarchy` paid 20 lines for an
   eleven-parameter instantiation, so a one-parameter instantiation
   costing 1 to 4 lines is a reasonable but unproved transfer. P-l says a
   cure does not transfer by analogy. **Treat minus 106 as a hypothesis
   with a gate, not a price.**
3. **The `Before` seal is the biggest unknown in section 6.** I do not
   know whether an `opaque` definition inside a parameterized module keeps
   its seal through a module instance in Agda 2.8. If it does not, the
   `Before` site may cost hundreds of seconds and the block dies there.
   This is why I put it first in the brief order.
4. **My Table estimate of minus 108 could be 10 lines out in either
   direction.** I counted the deletable blocks exactly and estimated the
   glue. It does not matter: the two-site net misses the floor by about 64
   lines at any figure in my range.
5. **The seconds in the report are not reproducible by me.** I accepted
   23.75, 23.48 and 1.50 as reported. The protocol is stated
   (`_build/lj-0.4f-report.md:114-116`) and the before-and-after pair ran
   on one clone, so the delta is internally consistent even if the
   absolutes have drifted.
6. **The tree moved under this review.** LJ-0.4m modified
   `src/FOL/ZFModel.lagda.md`, `src/L/Choice/Internal.lagda.md` and
   `src/L/Choice/Limit.lagda.md` while I read. None is a site in section
   6. All my counts come from HEAD `ee58312` or from the untouched files.
7. **I did not price whether `L.Coding.Sequence` is the right host on
   grounds other than lines.** It is in the Coding layer and the shape
   half is arguably Coding-layer content, which reads well. But an owner
   or a later reader may want a `L.Coding.Approximation` master instead,
   and that costs about 26 lines of preamble and turns minus 106 into
   about minus 80. Still passing.
8. **I did not re-verify T208's levers (b), (c), (d) and (g) myself.**
   Section 5.4 ranks them by the DEFECT CLASS I proved on lever (f). That
   is an inference about method, not a measurement of those levers.

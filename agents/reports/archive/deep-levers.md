# Deep structural levers: the Gödel route, thousand-line view

Analysis-only deliverable. Metric throughout: non-blank lines inside ` ```agda `
fences on whole masters (the same metric the L3.28 survey used, `PLAN.md:1122`).
Counts are measured at HEAD `a896bf2` except the two mid-edit files
(`L.Godel.Name`, `L.WellOrder.Base`), read via `git show HEAD:` only; their
working-tree deltas are attributed explicitly as M5a-in-flight. Whole `src/`
measured 25,460 code lines at HEAD (25,873 in the working tree). The route's
own headline numbers (28,580 whole tree, 14,245 dying gross, 15,280 surviving
basis, `PLAN.md:1123`) were taken at different measurement points and under a
"code-line" convention that is not exactly non-blank-Agda-lines (chapter-level
figures in the records mix file and code lines, and run up to ~12% above my
count); every
independent figure below is my own measurement and is stated as such. The
prior audit `_build/compression-audit.md` already covers the 30-300-line
scale; its findings are cited, not repeated.

## 1. The 10k verdict, in three sentences

No credible path exists: option C replaced a dying cluster of ~11.7-13.3k lines
with a new Gödel route that measures 7.6k today plus an unavoidable ~2.3k of
surviving choice machinery plus the 4.2k ZF cone, and the remaining M5-internal
work is priced at 0.6-1.2k even before the unpriced internalization of the
skeleton order. Every structural lever this investigation tested (one
internal-recursion framework, one derivable constructor, a formula-side order,
a definitional `𝒟ₒ`, a master closure statement) nets below 500 lines of
honest saving, moves the same mathematics into a riskier representation, or
churns the green ZF cone. The true floor is roughly 13.1-13.7k code lines on
this metric after the recommended lever set (≈14.1-14.8k in the route's
looser metric), 3.1-3.7k above the target, and the smallest lever set lands
there, not at 10k.

## 2. Bucket-by-bucket variance analysis

The memo's §4.2 bucket table (`dev/memos/L3.28-ac-route.md:106-116`) priced
landing at 8.3k-10.5k. The table below compares each bucket against what was
actually built. Measured sizes are non-blank Agda lines at HEAD.

| memo bucket | memo estimate | actual chapters realizing it | actual lines | why the estimate broke |
|---|---|---:|---|
| survives as-is | ≈540 | `Transversal` 190, `Stage` 155, `Recursion` 108, `WellOrder.Base` 55, `Absoluteness` 34 | 693 (HEAD); 836 with M5a's `Base` | Transversal/Stage/Recursion/Absoluteness landed at estimate; `WellOrder.Base` grew 55→206 (HEAD) / 349 (working tree, M5a list combinator): the memo priced only the pull-back, but the new name order is assembled from the whole combinator kit (`natSWO`/`sumSWO`/`prodSWO`/`pullSWO`, `Base` HEAD 218-381) and now the length-gated list order. Honest underestimate of the meta-order kit. |
| survives in part | ≈730 | `Step` (spine), `Coding.Model` generic infra, `Parameters`, `Sequence` | ~1,149 during coexistence; ~787 final (one Step copy + Model ~425) | Two of four items were wrong in both directions. `Step`'s whole 362-line spine survives, not ~150 (`Choice.Step.lagda.md:740-843`: `orderAt`, `famStep`, `endExtension` are all consumed); the M5 N3 ruling adds a line-for-line parallel scaffold `Godel.Step` (362) until M7 (`PLAN.md:1123`), after which one copy retires, so the final tree carries 362. `Coding.Model` survives at ~400-450 of 1,289 (the new route's import surface: `prʟ`, `prAtL`, `appAt`, `sucAtL`, `numL`, `extAt`, `envOverAt` + `svAt`/`domAt`/`valuesInAt`/`pairsInAt`, `Godel/Definable.lagda.md:45-49`; the ~700 lines of code-bridge/tag/subVal machinery die with the old cluster). `Parameters` (179) dies: its only consumer is old `Choice.Name` (import graph). `Sequence` (138) dies: its only consumers are the old cluster, and the new route's denotation recursion was built to the P2 probe pattern instead. The memo's assumption that the closure chapter would reuse Sequence's idiom never materialized. |
| dies | ≈11,950 | all of `L/Coding/` (6,441), `L/Choice/` minus survivors (4,724), `L.Hierarchy` 354, `L.WellOrder.Tree` 241, `FOL.Manipulation.Parameters` 179, `L.Godel.NormalForm` 199 | ≈12,138 gross; ≈11,663 net of Model/InL partial survivors | Right in spirit, wrong in the ledger twice: `Choice.Finite` (619) was listed as dying but survives as the `limitOrder` provider for the new skeleton key (the M5-internal collector recon, `PLAN.md:1123`; the M5a working tree imports `L.Choice.Finite` for `limitOrder`), while `Parameters`/`Sequence` die although the memo banked them as survivors. Net effect: the memo under-counts the final tree by roughly +619−179−138 ≈ +300 here. `NormalForm` (199) is dead code (see §3.6). |
| new | 2,700-4,900 | the whole `L/Godel/` route | 7,559 (HEAD: Operations 413, Tuples 153, Satisfaction 527, NormalForm 199, Terms 214, InL 1,517, Definable 1,032, Codes 172, Table 1,261, Tower 1,606, Name 103, Step 362) | The route's own tripwire accounting names the causes (`PLAN.md:1123`): "the descriptions and the bridge grew where the probes had not priced arity-generic leaf descriptions and the climb machinery" (InL 1,517 vs the 200-350 "closure" bucket; Definable 1,032 vs 200-400). Two additional design changes are visible from the code, not the record: (a) the certificate architecture for the junk-table problem is entirely new mathematics (Tower 1,606 vs the 250-400 "tower re-based" bucket); (b) the M3 Def-equivalence was re-built on `Terms.mirror`, stranding the M2 normal-form theorem (NormalForm 199, zero consumers). The scaffold copy of Step (+362) and the M5a name re-cut (+270 on Name, +143 on Base) were never in the memo's bucket table. |

The memo's §4.1 design (`L3.28-ac-route.md:71-100`) diverged from what was
built in at least these places, each priced above:

1. **Item 5/7 (closure step + tower re-based) vs `Tower`**: the memo priced a
   closure as an internal ω-recursion with a 10-clause step, and the tower
   re-proved against it. No closure chapter exists. The tower step is instead
   `StepAt b a`, the object-language sentence "the set at slot `b` is `𝒟ₒ` of
   the set at slot `a`" (`Godel/Tower.lagda.md:1906-1910`), built from a
   certificate (`CertAt`), an honesty proof, and certified denotation tables.
   The certificate exists because a naked existential over tables admits junk
   (the clause shapes are conditional on numeral-ness), and route C's codes
   embed their parameters so the old code-set bound cannot be pinned
   (`PLAN.md:1123`, "(d)'s design closed … junk-table problem"). Price:
   +1,200-1,400 over the two memo buckets it replaced.
2. **Item 8 (order meta: birth stage, term, parameters) vs M5a**: the N2
   tree-shortlex order was re-cut at M5 to skeleton/parameter split because
   "the tree-shortlex with embedded parameters would need a second collector
   on code pairs" (`PLAN.md:1123`). The skeleton key reintroduces `limitOrder`
   (which the memo's §4.1 explicitly said the new route would not need: "no
   separate finite base, no earliest-disagreement family"), making `Choice.Finite`
   (619) a survivor.
3. **M3 (Def-equivalence via a kinded closure) vs `Terms`**: the equivalence
   was delivered as `termDef≡Def` via `sound` + `mirror` + the satisfaction
   bridge (`Godel/Terms.lagda.md:336-338`), not via the kinded-constructor
   induction the M3 record designed; the M2 normal-form theorem was left
   behind with no consumer.
4. **M5 N3 (parallel scaffold)**: coexistence forces a second 362-line copy of
   the step chapter until M7; the memo's "survives in part ~150" assumed one
   merged copy.

Net landing arithmetic, memo's own numbers: pre-compression 15,850-16,450,
post-compression 15,000-15,700, central estimate 15.5-16.0k, tripwire re-set
to a post-compression 16.5k (`PLAN.md:1123`). The brief's "current measured
trajectory ~15.5-16.5k" is that figure. My independent build of the final
tree (post-M7) with my metric:

| component | lines |
|---|---:|
| ZF cone (measured, cutting the `L.Model → Transversal` edge; 37 modules) | 4,199 |
| choice-meta survivors: Transversal 190 + Stage 155 + Step 362 + Finite 619 + WellOrder.Base ~350 + Absoluteness 34 + Recursion 108 + Coding.Model ~425 + Coding.InL residue ~25 | ~2,268 |
| Gödel route, final (Operations 413, Tuples 153, Satisfaction 527, Terms 214, InL 1,517, Definable 1,032, Codes 172, Table 1,261, Tower 1,606, Name ~400 after M5a, Step 362; NormalForm 199 deleted, Tree 241 retired) | 7,657 |
| M5b/M5c/M5d + glue (memo price) | 600-1,200 |
| pre-compression total | 14,724-15,324 |
| levers (see §4) | −1,300 to −1,750 |
| post-compression total | ≈13,000-14,000 |

The skeleton-order internalization risk (not in the memo's M5 price; see §5)
would add +1,000-1,600 to the pre-compression total, moving post-compression
to ≈14,000-15,600.

## 3. The seven questions, answered from the code

### 3.1 Why do the eight term constructors exist, and what is the marginal cost?

`KT` has eight constructors (`Godel/Terms.lagda.md:75-84`): `allK`,
`selMemK i j`, `selEqK i j`, `selEqConK i a`, `interK`, `unionK`, `complK`,
`shiftK`. They exist because they mirror the primitive formula atoms and
connectives whose satisfaction sets the route must recognize internally: the
four leaves are the formula atoms (⊤; `∈`; `=`; `= con`), and the four nodes
are ∧, ∨, ¬, ∃. The formula language has twelve constructors; →, ∀, ∃∈, ∀∈
and ⊥ are already composites in this syntax (via `complK`/`interK`/`shiftK`
under LEM, `Terms.lagda.md:213-320`), so the eight is the reduced basis.

Chapters whose size scales with the constructor count, with the per-constructor
share measured from the section layout:

| chapter | scaling content | per-constructor share |
|---|---|---:|
| `Terms` 214 | 8 `sound` cases; mirror composites; `termDef≡Def` | ~15 |
| `Codes` 172 | 8 tags, 8 subterm cases, 8 unfolding equations, tag-discrimination helpers | ~15-20 |
| `Name` (M5a) ~400 | the picture `toTree`/`fromTree`/`retractK`, 8 cases each | ~30-40 |
| `Definable` 1,032 | one description per operation (11 total; leaves dominate) | ~40-60 |
| `Table` 1,261 | 8 clause layers, 8 diagonal cases, 56 off-diagonal discriminations | ~50-60 plus ~14 off-diagonal rows |
| `InL` 1,517 | 8 per-operation constructibility proofs + `denoteL`'s 8 induction cases | ~100-130 |
| `Tower` 1,606 | 8 certificate branches, 8-way dispatch, 8 honesty branches | ~90-110 |

Marginal cost per constructor across the route: roughly 340-435 lines.

Which constructors are derivable? Exactly one: `unionK` is definable from
`complK` + `interK` by De Morgan, and the route is classical (the mirror
already runs under `LEM`, `Terms.lagda.md:304`). The denotation equation for
the derived union becomes a lemma: one new classical equation
(`satSet (φ ∨̇ ψ) ≡ allTuples ∖ (allTuples ∖ satSet φ ∩ allTuples ∖ satSet ψ)`)
in the satisfaction chapter's `Classical` module, ~10-20 lines, priced against
the P-d law (a path between satisfactions of fully concrete formulas is the
measured hazard class, memo §9). The other seven are forced: `selEqConK`'s
denotation is already a three-operation composite (`Terms.lagda.md:111-113`)
but the syntax needs *some* constructor for the constant atom, and replacing
it with an `extendFamily` node is a lateral move that changes the reductions'
shape; the remaining six mirror primitive satisfaction cases. `unionK` also
has a genuinely internal role (its clause and certificate branch), so the
removal saves one clause layer, 7 diagonal + 7 off-diagonal cases, one
certificate branch, one honesty branch, one code tag, one InL induction case
and one description: ≈ −180 to −250 end to end.

**Smallest basis:** seven constructors. **Verdict: pursue after M5** (it is a
reopening of eight green chapters for a sub-500-line yield; the one decisive
reason: it is the only constructor that is a theorem rather than a primitive,
and the yield compounds through the certificate).

### 3.2 Can one internal-recursion framework serve both the denotation recursion and the order recursion?

What the two genuinely share: the approximation-family pattern (approximation
predicate, graph quantifying over approximations, value lemma, uniqueness,
`mereFunct` assembly). The old route already had exactly one such framework:
`Choice.Table`'s `module Described (Cond)(Cond₀)(cond-spec)(cond₀-spec)`
(`Choice/Table.lagda.md:341-353`) builds `StepAt`, `ApproxAt`, `GraphAt`,
`approx-val` and the relation sets generically from a described, adequate step
condition; the M5-internal recon confirms this and names Faithful as the old
Cond supplier (`PLAN.md:1123`). What is genuinely different: the index sets
(finite subterm-code set vs ordinals), the value domains (term denotations vs
relations at stages), and the step condition content (clause shapes vs the
naming comparison). The certificate is a one-time investment the order side
reuses (the memo's M5-internal price is "memo price minus expected Tower
reuse", `PLAN.md:1123`).

The honest saving of unification is not the ~2,800 lines the question gestures
at. The survey priced the recursion-assembly triplication (Hierarchy +
Choice.Table + Before, ~1,141 lines of near-identical shape) at −130 to −200
conservative, with the measured rule 13: abstraction is not the cure for the
non-locality walls (>400 s with the order as a module parameter), so only the
parts whose types do not mention the recursion's value may move
(`PLAN.md:1122`, lever (f)). The clause layers, certificates and per-operation
readings are content, not plumbing, and do not share. **Verdict: pursue after
M5, capped at ≈ −150 to −250**: build M5c inside `Described`'s parameterized
shape (or a lean copy of it) rather than a third bespoke assembly, and stop
there.

### 3.3 Does the axiom-of-choice endgame need the order materialized as per-stage relation sets at all?

The consumer is exact. `Transversal` consumes, from the route, only:
`bound-below₂` (Stage), `Mem`/`relOf` (Step), `module Bound` (Order:
`boundOrd`, `boundOrd-ord`, `boundOrder`, `orderL`, `orderL-fill`,
`orderL-rep`), `appAt`/`appAt-adequate` (Coding.Model), and
`SWO`/`IsLeast`/`isPropLeastOf`/`leastOf` (WellOrder.Base)
(`Choice/Transversal.lagda.md:58-67`; `Bound` consumed at 176-183; the two
readings spend `orderL-fill`/`orderL-rep` at 246-280). `Pick`
(`Transversal.lagda.md:116-127`) names the order only as a **constant**,
pin-bind by `var zero ≐ con r`, read by one `appAt`; the least-element search
runs on the *meta* order `boundOrder`. So the minimal internal object is: one
element of the model at the bound `β` whose membership is the meta relation
(`orderL` with `orderL-fill`/`orderL-rep`). That is a relation set, and the
old `Bound` interface is already minimal.

The formula-side alternative (one adequate formula with quantified certified
tables, in the style of `StepAt`) does not remove the collector's mathematics;
it relocates it. The order at `β` is defined by the ∈-induction `orderAt`
(`Choice/Step.lagda.md:740-746`) over every ordinal below `β`. Expressing
"`relOf (orderAt β) w z`" as one formula requires quantifying over an
approximation of the whole family below `β` — that is the collector's graph
content as a formula — and then `Pick` becomes a formula carrying coded tables
inside, which is the measured wall class the whole seal discipline exists for,
and `Transversal` (which the plan keeps verbatim, swap surface only) is
reopened. The collector is the cheap end: it turns a heavy description into a
constant plus four atoms. The honest saving of the formula route is only the
materialization half of M5c (~200-400) against a rewrite of `Transversal` and
a wall-class description. **Verdict: reject.** The minimal internal object is
one relation set at the bound, and M5c/M5d are the price of it.

### 3.4 Is `InL`'s per-operation structure forced, or is there a master closure statement?

The master statement exists: `denoteL : (A : V ℓ) → ⟨ isL A ⟩ → {n} (t : KT ⟪ A ⟫ n)
→ ⟨ isL (⟦ t ⟧ᴷ) ⟩` (`Godel/InL.lagda.md:1948`). The per-operation proofs
upstream are its induction cases, and they have no other consumers: `capL`,
`cupL`, `diffL`, `selectMemberL`, `zeroL`, `∅L` are referenced nowhere outside
`InL` itself (verified by whole-tree grep), and the downstream surface consumed
by `Definable`/`Table`/`Tower` is exactly `allTuplesL`, `selectEqualL`,
`extendFamilyL`, `shiftDownL`, `denoteL`, `valuesL`, `stageFam`, `numL` (plus
`sglL` from the old `Coding.InL`). The four-move frame (one stage from
directedness, defining formula, `defSet→isL`, close) is already factored
through `Definable`'s `Describes`/`extAt` frame (`Godel/Definable.lagda.md:108-141`);
what differs per operation is the body formula, the conversions, and the climb
machinery, which a schema cannot generate (Agda 2.8 `--safe --cubical` has no
macro system; the compression audit says this explicitly). A single-description
master closure would need a uniform operation record — which is precisely the
`OpDesc` discipline `Table` already parameterizes its binary-node clause on.

So: the per-operation structure is forced in content and already factored in
form. Reorganizing `InL` so `denoteL` is proved first saves nothing (the
cases are the chapter). The honest residue is the repeated frame ceremony,
already priced by the compression audit at ~250-330 of `InL`'s 1,517
(`compression-audit.md`, claim 1). **Verdict: reject as a structural lever**;
the answer to the question is that the per-operation proofs are the induction,
not redundant parallel chapters.

### 3.5 Would defining `𝒟ₒ` as the term-values set delete the Satisfaction/NormalForm chapters?

No, and it would churn the delivered ZF cone. The satisfaction side is
load-bearing in the green cone, not decorative: `L.Definability`'s
`defSet`/`Def` (`Definability.lagda.md:108-115`) are consumed per-formula by
the separation proof (`carveSat`, `carveSatAnd`, via `RefC.abs-defSet`,
`Axioms/Separation.lagda.md:163-176`), by the ordinal chapters
(`Ordinal/Stages.lagda.md:375-376`), and by `𝒟ₒ→isL` (`Axioms/Basic.lagda.md:98-99`).
`𝒟ₒ` itself is the sealed satisfaction-defined definable powerset
(`Constructible.lagda.md:212-222`, `Definability.lagda.md:114-115`), and every
delivered landmark names it (the trophy `L⊨ZFC` at `Landmarks.lagda.md:76-77`).
Redefining `𝒟ₒ` as `termDef` changes the definitional base of all of that
(the memo's option B, `L3.28-ac-route.md:121-127`): 4.2k lines of churn to
re-prove or transport, plus re-stating absoluteness for term values, since the
Δ₀ machinery (`abs-defSet`) is about satisfaction. What it buys is trivial:
the three `termDef≡Def` transports in Tower (`Tower.lagda.md:1999, 2041, 2097`)
and the equivalence proof itself (`Terms.lagda.md:336-338`), ~40-60 lines.

It also would not delete `Satisfaction`: `Terms.sound`/`mirror` consume its
case equations and reductions (`Terms.lagda.md:131-165, 166-320`), and the ZF
cone still needs the per-formula satisfaction semantics. `NormalForm` is dead
already, but for a different reason: `Terms.mirror` superseded it at M3
(§3.6). **Verdict: reject.** The satisfaction-side definition of `defSet` is
the delivered axioms' definitional base; the term identification is correctly
a theorem.

### 3.6 Are there whole chapters whose only real consumer is another chapter that exists only for the first (mutual-justification islands)?

One stranded leaf, no true islands. `L.Godel.NormalForm` (199 lines) has no
consumer anywhere: its import cone ends at `Everything`, and `normalForm`,
`Reach`, `reach-all`, `reach-sing` are referenced by no other module (whole-tree
grep). It is the M2 normal-form theorem, superseded when M3 built the
Def-equivalence on `Terms.mirror` + `sound` + the bridge (`PLAN.md:1123`, M3
record; the M2 record's "one direction of the equivalence is `normalForm`
composed with the bridge" was never realized as built). This is dead code, not
an island: nothing depends on it, so deleting it breaks nothing. Its status is
"never needed" (superseded), not "delete and re-prove smaller".

The old order-internalization cluster (`Choice.Name/Internal/Faithful/
Adequate/Limit/Before/Order/Table`, 4,724 lines) is a genuine mutual-support
network, but it is scheduled to retire wholesale at M7 and its survival today
is the coexistence ruling (M6), not mathematics. The rest of the Gödel route is
one spine: `Terms → Codes → Table → Tower → (M5 Cond) → Bound → Transversal`,
with `InL`/`Definable`/`Operations`/`Tuples`/`Satisfaction` feeding it. Every
chapter has a downstream consumer; `Tower` is the internal sink and it feeds
the order's internal side. `WellOrder.Tree` (241) has exactly one consumer,
`Godel.Name`, and is already slated to retire at M7 (`PLAN.md:1123`).

### 3.7 Is 10k reachable, and what is the floor?

No (section 1). The floor arithmetic is in section 2's table: post-compression
13.1-13.7k on this metric (13.0-14.0k with the full lever bank). The smallest
lever set that gets within ~1k of it is in section 4.

## 4. The levers, largest first

Scale note: under this brief's rule (drop findings at the 30-300-line scale
already audited), no single structural lever in the delivered architecture
reaches 500 lines. The honest statement is that: the ≥500-line units do not
exist as separate levers; the compression pass is the only ≥500-line unit, and
it is a bundle. Each lever below states mechanism, chapters, new work, risk,
blast radius, and a verdict.

### L1. The compression pass on the surviving route (the one ≥500-line lever, as a bundle)

- **Mechanism:** execute the banked compression levers against the *surviving*
  Gödel chapters, per the prior audit's re-pricing: InL stage-module frames
  (−250-330), Definable selection frame (−40-60), Table/Tower monotonicity
  dedupe (−95-110), the 8-way dispatch frame (−50-80), honesty continuation
  frames (−25-40), subterm-family frame (−30-50), plus deletion of the
  certificate's redundant ω-membership conjuncts (−70-110, verified unused at
  `Tower.lagda.md:1305`).
- **Chapters shrunk (measured):** InL 1,517, Definable 1,032, Table 1,261,
  Tower 1,606, Codes 172.
- **New work:** nothing new; each item is a before/after bisect per the
  route's method (no statement weakening; seals preserved per P-c; frames must
  not move recursion values per rule 13).
- **Risk:** low-moderate; the audit grades the pieces (a)-(d); the statement
  surface of `StepAt`/`nameAt` is unchanged.
- **Blast radius:** none outside the Gödel route; `Everything` recap prose only.
- **Verdict: pursue after M5** — the one decisive reason: it is the only
  ≥500-line unit available, at ≈695-935 measured (prior audit), on the
  chapters that survive.

### L2. Delete dead code: `NormalForm`, `product`/`memberGraph`, `productAt`/`memberGraphAt`

- **Mechanism:** deletion of zero-consumer modules/definitions. `NormalForm`
  (199) is superseded by `Terms.mirror`; `product`/`memberGraph`
  (`Operations.lagda.md:153-196`) and `productAt`/`memberGraphAt`
  (`Definable.lagda.md:251-385`) have had no consumer since M2 and still have
  none (the M2 record's own admission, `PLAN.md:1123`).
- **Chapters deleted (measured):** NormalForm 199; ~160 lines from Operations
  and Definable.
- **New work:** recap prose in `Everything`; no re-proving.
- **Risk:** none (pure removal, verified by grep).
- **Blast radius:** none. Distinction: "never needed" (product/memberGraph
  never consumed; NormalForm superseded before its consumer existed).
- **Verdict: pursue now** — the one decisive reason: zero-risk removal that is
  also an honest correction to the M2/M3 variance record.

### L3. Drop `unionK` from `KT` (the one derivable constructor)

- **Mechanism:** define `unionK s t` as `complK (interK (complK s) (complK t))`
  (De Morgan, classical); its denotation equation becomes a lemma (one new
  classical satisfaction equation, ~10-20 lines, in `Satisfaction`'s
  `Classical` module). Cascades: −1 tag and subterm case in `Codes`, −1
  clause layer, −7 diagonal, −7 off-diagonal in `Table`, −1 certificate
  branch, −1 honesty branch, −1 dispatch case in `Tower`, −1 induction case in
  `InL`, −1 description, −1 picture case in `Name`.
- **Chapters shrunk (measured):** Terms 214, Codes 172, Table 1,261, Tower
  1,606, InL 1,517, Definable 1,032, Name ~400.
- **New work:** the classical `sat-∨` lemma; re-run of the affected clause
  readings.
- **Risk:** moderate, specific: the new lemma is a path between satisfactions
  of fully concrete formulas — the exact P-d hazard class (386 s as a path,
  1.9 s as direction pairs, memo §9). A probe is required.
- **Blast radius:** seven green Gödel chapters reopen; `TermDef≡Def`'s proof
  shape survives.
- **Verdict: pursue after M5** — the one decisive reason: ≈ −180-250
  end-to-end, below the 500-line bar, but it is the only constructor whose
  existence is a theorem rather than a primitive.

### L4. One internal-recursion framework for the denotation and order recursions

- **Mechanism:** build M5c inside `Choice.Table.Described`'s parameterized
  shape (`Choice/Table.lagda.md:341-353`) rather than a third bespoke
  approximation/assembly; reuse Tower's certificate for the names' denotation
  tables.
- **Chapters shrunk:** M5c's collector (planned, ~400-700 otherwise);
  old `Choice.Table` 472 dies as accounted.
- **New work:** the Cond supplier (M5b) and its adequacy against the scaffold;
  the parameterized assembly, priced against rule 13 (only value-free parts
  may move).
- **Risk:** rule 13 is measured: abstraction over the recursion's value is
  not the cure (>400 s with the order a module parameter, `PLAN.md:1122`).
- **Blast radius:** none delivered-green; M5c is unbuilt.
- **Verdict: pursue after M5, capped at ≈ −150-250** — the one decisive
  reason: the framework already exists twice; unifying saves the assembly
  only, not the content.

### L5. Formula-side order (skip the collector)

- **Mechanism:** express the order at the bound as one adequate formula with
  quantified certified tables inside `Pick`; drop M5c's materialization.
- **Chapters shrunk:** M5c (~400-700 planned); Transversal 190 rewritten
  (+100-200).
- **New work:** the order-family formula (the ∈-induction `orderAt` expressed
  as one sentence quantifying an approximation), its certificate at order
  level, two new readings.
- **Risk:** high: `Pick` becomes a formula carrying coded tables, the measured
  wall class; the junk-table problem returns at order level unless a second
  certificate is built; the memo's whole §4.3 bet was that the surviving
  surface stays description-light.
- **Blast radius:** Transversal (the trophy's last chapter, currently
  verbatim-surviving) plus Bound's interface.
- **Verdict: reject** — the one decisive reason: it relocates the collector's
  mathematics into the one place the route measured to be expensive, for a
  net saving below the materialization half of M5c.

### L6. Define `𝒟ₒ` as term-values (definitional equivalence)

- **Mechanism:** make `termDef` the definition of the definable powerset.
- **Chapters shrunk:** Tower's three transports (~15) and `Terms`' equivalence
  proof (~40).
- **New work:** re-proving or transporting every delivered ZF-cone statement
  whose meaning names `Def`/`𝒟ₒ`/`𝒮ʟ` — the whole 4.2k cone
  (`Axioms/Separation.lagda.md:163-176`, `Axioms/Basic.lagda.md:98-99`,
  `Ordinal/Stages.lagda.md:375-376`).
- **Risk:** the definitional base of delivered landmarks changes (the memo's
  option B, rejected on the same grounds); absoluteness must be re-stated for
  term values.
- **Blast radius:** every green ZF chapter and the trophy signature.
- **Verdict: reject** — the one decisive reason: the satisfaction-side
  `defSet` is load-bearing in the delivered axioms, and the equivalence as a
  theorem costs ~55 lines.

### L7. Master closure statement for `InL`

- **Mechanism:** prove "every term denotation over an L-carrier is L" once and
  derive the per-operation facts.
- **Chapters shrunk:** InL 1,517.
- **New work:** none beyond reorganization: `denoteL` already is the master
  statement; the per-operation proofs are its induction cases and are consumed
  by nothing else (§3.4).
- **Risk:** the clause layers' constructibility obligations are per-operation
  in any design.
- **Blast radius:** Table/Tower clause proofs.
- **Verdict: reject** — the one decisive reason: the per-operation proofs are
  the induction, and the shared frame is already factored.

### L8. Retire the second Step copy (already planned)

- **Mechanism:** at M7's rewire, one of `Choice.Step`/`Godel.Step` (both 362)
  retires; the survivor keeps the term names.
- **Chapters deleted (measured):** one 362-line copy (currently a required
  coexistence artifact, not a lever the compression pass may take; the prior
  audit excludes it for exactly this reason).
- **New work:** none.
- **Risk:** none at M7 (M6 requires both green).
- **Verdict: pursue at M7 as planned, not before** — the one decisive reason:
  coexistence (M6) is a ruling, not a cost to compress.

## 5. Recommended combination and its landing arithmetic

Take, in order: L2 (dead-code deletion, now), then finish M5 with L4's
discipline (collector in `Described`'s parameterized shape, Tower-certificate
reuse), then at the M7 rewire take L3 (unionK drop, behind the P-d probe) and
L1 (the compression bundle, re-priced at ≈695-935 by the prior audit), with
L8 (Step copy retirement) as part of the rewire.

Arithmetic (my metric; memo-metric in parentheses):

| step | delta | running total (pre-compression base 14,724-15,324) |
|---|---:|---:|
| L2 dead code | −360 | 14,364-14,964 |
| M5 as planned | 0 (already in base) | 14,364-14,964 |
| L3 unionK (behind probe) | −180 to −250 | 14,114-14,784 |
| L8 Step copy retirement | −362 | 13,752-14,422 |
| L1 compression bundle | −695 to −935 | **13,057-13,727** |

Post-compression landing: **13.1-13.7k on this metric (≈14.1-14.8k in the
route's looser metric)**, still 3.1-3.7k above 10k. If the skeleton-order
internalization cannot be fitted inside the memo's M5 budget (§5 item 1),
add +1,000-1,600: **14.1-15.3k (≈15.2-16.5k memo-metric)**. The floor is the
first number if M5 holds, the second if it does not; 10k is not in either.

## 6. What cannot be determined without ruling or prototyping

1. **Whether M5b-M5d can internalize the skeleton order inside the memo's
   550-1,150 budget.** The skeleton key compares hereditarily finite sets by
   `limitOrder` (`Godel/Name.lagda.md:541-542`, M5a working tree; the memo's
   M5-internal design ruling, `PLAN.md:1123`). The meta order is cheap
   (`Choice.Finite.limitOrder`, `Choice/Finite.lagda.md:1114-1115`), but its
   internal description is a numerals-recursion whose values are relations:
   the old route paid `Limit`+`Before` (458 + 1,114) for exactly this
   mathematics, and the collector recon priced neither. If a fresh
   Limit/Before-class recursion is required, M5-internal is ~1,000-1,600 over
   budget and the floor moves to the second number in §5. If the Cond can be
   stated without it (e.g., the order description quantifies the finite-stage
   relations through one certificate), M5 holds. This is the decisive ruling.
2. **Whether the unionK drop's classical satisfaction equation stays in the
   cheap class.** It is a path between satisfactions of fully concrete
   formulas, the P-d hazard (386 s vs 1.9 s, memo §9); a direction-pair
   formulation is the expected cure but must be measured.
3. **Whether the certificate's ω-conjuncts can be dropped without re-wall.**
   The audit verified the honesty side needs only functionality
   (`Tower.lagda.md:1305`), but the fill side feeds the conjuncts and the
   removal must be bisected per the route's method.
4. **Whether the compression bundle survives contact.** Each item lands only
   behind a before/after bisect; the audit's re-pricing (≈695-935 vs the
   banked 650-1,050) is a projection.
5. **Whether Transversal truly stays verbatim.** The meta-side interface parity
   was proved at N3 (`PLAN.md:1123`), but the internal side's adequacy against
   the scaffold is M5b's unbuilt deliverable; `orderL`'s shape at M5d must
   match `Bound`'s expectations (`Choice/Order.lagda.md:680-702`) or
   Transversal's two readings reopen.

The one measurement that settles the largest of these is cheap and already
half-done: the old `Limit`/`Before` pair is the exact precedent for the
skeleton order's internal side, and its re-pricing against the new skeleton
code set (not the formula-code set) decides whether the floor is 13.1-13.7k
or 14.1-15.3k.

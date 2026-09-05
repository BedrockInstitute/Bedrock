# LJ-1.742 report: `defat-fill-asConst`, the bounded DefAt fill at asConst

(This skeleton was written before the first Agda run and filled as the
runs landed; see C-22, `dev/LESSONS.md:2307`. It was extended, not
rewritten, by the lint re-dispatch of the same day.)

## HEAD

head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.742
obligation: agents/tasks/LJ-1-742/Probe742.agda::defat-fill-asConst
verdict: **PARTIAL: PARK AND SPLIT, NOT A NO-GO.** The obligation's
type is stated, exported at the file's top level, and NOT inhabited:
the file is delivered as `Probe742.agda.txt` because one hole stands in
the inhabitant (runs/p-26-desc.out, EXIT=42, the only error is
[UnsolvedInteractionMetas] at the hole, 537 lines). Everything the
inhabitant stands on is BUILT AND GREEN: the three hypothesis types,
the gamma-limit package, the closed operations at gamma, the Delta0
transport, the V-side code and closure stages, the L-side slot and
table stages, and (landed by this dispatch, section 9) the DESCENT
PACKAGE the bounded walks call. All of it typechecks in 4.01 s and
746,520,576 B at the wide caliber, 34.8 percent of cap. No postulate
anywhere, nothing in `src/`, `stage-read` absent,
`Sat-in-carrier-lim` absent. The remaining work is the bounded
assembly of `DefBody w`'s conjuncts, re-priced by this dispatch's
reading of the twelve clauses (section THE TWELVE-CLAUSE CHECK): the
prior session's "domAt/appAt/twelveAt transport by d0eq" is TRUE for
appAt and FALSE for domAt and twelveAt; the bounded walk needs witness
staging, and this dispatch verified every staging move it needs is
LANDED in the tree (section THE STAGING INVENTORY: five of five, after
the first pass wrongly priced pair descent as missing; the Fact
module of EnvSupply carries it, and the probe now instantiates it as
section 9). No heap wall stands: the one heap kill met so far was
routed by replacing the mutual recursion with a single equality
induction and testing the new shape under the same cap (p-6 through
p-24). The first return of this task failed the program's accept at
conjunct 6 only (the survey duty, runs/accept-1.out, error class
lint); this dispatch repairs that failure.

## 0. THE PREDECESSOR QUESTION

| hypothesis | taken from | verdict there |
|---|---|---|
| `keyS-in-carrier-lim` | agents/tasks/LJ-1-734/Probe734.agda:192, delivered by 729 at Probe729.agda:202 | GO (lj-1.734-report.md:10) |
| `envSet-in-carrier-lim` | agents/tasks/LJ-1-735/Probe735.agda:65 | GO (lj-1.735-report.md:13) |
| `Sat-at-asConst` | reconstructed; see section THE 740 TYPE | no predecessor in the tree |

Premise 1 (738 NO-GO) verified: agents/tasks/LJ-1-738/lj-1.738-report.md:13,
the defect was the FULL alphabet of the 736 type. Premises 2, 3, 4, 5
verified as the build consumed them (Probe734.agda:192, Probe735.agda:65,
src/L/Coding/Powerset.lagda.md:500, src/FOL/Manipulation/Relativize.lagda.md:142).

## THE 740 TYPE (the one judgement this brief had to make)

`agents/tasks/LJ-1-740/` does not exist in the tree; the brief's "the
type of [LJ-1.740]" has no bytes to read. Reconstructed on the pattern
of the two landed hypotheses: `keyS-in-carrier-lim` quantifies EVERY
carrier-formula (`∀ {n} (φ : Formula ⟪ fst A ⟫ n)`), and
`envSet-in-carrier-lim` every length. The matching Sat reading is
therefore ALL-ARITY:

    → ∀ {n} (φ : Formula ⟪ fst A ⟫ n)
    → ⟨ Sat A (mapFo (asConst A) φ) ∈ˢ LsetS γ oγ ⟩

The arity-1-only reading the brief's consumption sentence suggests does
NOT reach the table's subformula leaves: `satTable A θ` is
`tree ent θ` with `ent χ = prʟ (keyʟ χ) (Sat A χ)`, and the subformulae
of an arity-1 formula have UNBOUNDED arity (each binder raises it), so
an arity-1 hypothesis leaves the table unstaged. The all-arity reading
is stronger as a hypothesis and is what the bounded fill actually
consumes. **The mathematician should rule this reading in or out**: if
it is ruled out, the staged-Sat induction sketched in section REMAINING
WORK (item 4) replaces it at roughly 150 lines.

## 1. WHAT WAS BUILT (all compiling; runs/p-24-final.out)

1. **The gamma package** (`suc∈γ`, `∅∈γ`, module `Γ`): `closedω γ`
   makes gamma successor-closed (`sucV d` sits under `+ω d` by
   `+ω-iter 1`, which sits in gamma, and ordinals are transitive), so
   Bound's package instantiates at `lam := γ` and closes pairing AT
   gamma (`pr∈λ`). No iterate, no `+ω` climb survives anywhere.
2. **OpsAt** (`sgl∈γ`, `cup∈γ`): the finite closures stay inside
   `Lset γ`; one `Lset-out′` truncation per lemma, then the
   succ-closed limit absorbs the successors. `cup∈γ` rides the landed
   `union∈Lset-suc` (Key/EnvSupply), not a fresh carve.
3. **D0** (`d0eq`, `d0`, `d0r`): for a Delta0 formula the bounded and
   standard readings are POINTWISE EQUAL: the bounded quantifiers
   keep their term filters in both semantics, so one induction gives
   the path and both transport directions read off it. The unbounded
   quantifiers are NOT covered and are each discharged by hand.
4. **VStages** (`code∈γ`, `clo∈γ`): the V-code of any relabelled
   formula, and InL's subformula closure, sit in `Lset γ` by a
   structural walk whose every step is a closed operation at gamma.
5. **LStages** (`keyʟ∈γ`, `Sat∈γ`, `ent∈γ`, `fold`, `slot∈γ`,
   `satTable∈γ`): the L-side key carries the V-side key's stage across
   the landed `keyBridge`; the Sat leaf is the hypothesis; the slot and
   the table are staged by ONE structural fold mirroring `tree`'s own
   clauses, with `sglʟ` and `cupʟ` staged through their fst equations.
6. **The goal's shape**: `relativize-correct` at `c := LsetS γ oγ`
   (the Correct instance at the identity interpretation, the same
   module instance the obligation's `⊨` lives in, since
   `𝒮ʟ = 𝒮ᵥ ↾ isL` definitionally) turns the obligation into the
   BOUNDED reading `remaining-goal`; the main term is one subst.
7. **The descent package** (section 9 of the probe, landed by the
   lint re-dispatch): module `Desc` instantiates EnvSupply's `Fact`
   (src/L/Coding/EnvSupply.lagda.md:450) at `K := LsetS γ oγ` with
   `layer-trans (Lset-layer γ)`
   (src/L/Constructible.lagda.md:183, :246) and exports, at the
   probe's own glyphs: `pr↓` (a staged pair's components are staged;
   `prK`, EnvSupply.lagda.md:453), `key↓` (the three components of a
   member key, through its arityTag shape, by three `pr↓` steps), and
   `val↓` (a table entry's value is staged; `valK`,
   EnvSupply.lagda.md:463).

## 2. WHAT THE SHAPE RESISTED

- `separateAt` cannot stage the Sat sets: `cond` has unbounded
  quantifiers, so its Δ₀ witness does not exist, and the model field's
  own carve (Full's `hasSeparationL`) sits at an internally-chosen
  reflection stage that need not lie under gamma. The route that would
  have worked (own carve at `+ω σ₀`, `mkReflect` bridge, `uniqueL`
  equation) was fully designed and is priced in REMAINING WORK item 4;
  the all-arity hypothesis made it unnecessary.
- `Lset-out′`, `union∈Lset-suc` and friends take `lem` first (file
  telescopes); `SupplyEnv`'s module application does not. Both cost a
  compile round.
- `keyBridge` only names the fst-level identity, which is exactly what
  every membership statement needs.

## 3. THE TWELVE-CLAUSE CHECK (measured by reading, this dispatch)

The prior session left one leaf unchecked: "verify twelveAt carries no
unbounded ∃̇ before trusting this". CHECKED; the answer is NO. `twelveAt`
is not a Δ₀-walkable formula, and "domAt/appAt/twelveAt transport by
d0eq" holds for appAt only:

- `appAt` IS Δ₀: `∃̇∈` (a bounded filter, identical in both readings)
  over the Δ₀ `prAtL`. It transports by `d0eq` with the landed
  `Δ₀-prAt` (src/L/Coding/Model.lagda.md:160-163).
- `domAt` is a `∀̇` frame (Model.lagda.md:279) whose body quotes
  `inDomAt = ∃̇ (appAt ...)` (Model.lagda.md:270), an unbounded ∃̇ in
  the second conjunct's CONCLUSION, so its witness must be staged into
  the bound. Stage: the witness is a member of the table T
  (`pr (fst x) (fst y) ∈ fst T`), T is staged (`satTable∈γ`), so one
  transitivity link lands it (see the inventory, item 1).
- The twelve clauses (Graph.lagda.md:94-104) each sit in a
  `∀̇∈ (var C)` frame, a bounded filter identical in both readings,
  under ∀-frames that restrict, but their relations carry unbounded
  ∃̇: the existential clause's body binds the extended environment
  (`body∃`, Model.lagda.md:1566, under `quantRel`, Model.lagda.md:1609),
  the exIn clause's body binds a term value and an extended environment
  (`bodyEx`, Model.lagda.md:1886), and two of the eight closedAt
  clauses bind a successor-code witness (`oneSuccAt`, Model.lagda.md:2091,
  `succSndAt`, Model.lagda.md:2094). NONE of these witnesses can be
  transported by `d0eq`; each must be produced INSIDE `Lset γ`.
- What saves the walk from being a construction-fest: every one of
  these witnesses is already a MEMBER of something the shell stages:
  a member of the table (through `pr c yc ∈ T`), a member of the
  env-set slot (through `envSetAt`'s identification), a member of a
  member (pair components). The staging is therefore descent and
  transitivity, not new carving (next section).

## 4. THE STAGING INVENTORY (measured by reading, this dispatch)

Every unbounded witness the bounded twelve-clause and closedAt walks
need is staged by one of these five facts. Four are already landed;
one is missing and is the only new construction left.

1. **Transitivity (LANDED).** `Lset-trans′`
   (src/L/Coding/Bound.lagda.md:127): `y ∈ˢ x`, `x ∈ˢ Lset α` gives
   `y ∈ˢ Lset α`. Stages every "member of a staged set" witness:
   table members, env-set members, carrier members (through the
   brief's own `hA`).
2. **The env-set slot (LANDED).** The clauses' environment witnesses
   e' are members of the envSet slot, and `envSetAt-ident`
   (src/L/Coding/EnvSupply.lagda.md:234) identifies that slot's value;
   the whole envSet over the carrier is staged by the brief's own
   HYPOTHESIS `envSet-in-carrier-lim` at every length. So e' needs one
   transitivity link (item 1), NO per-environment construction.
   `envSetNumeral∈` (src/L/Coding/Key.lagda.md:486) is the landed
   route Henv itself rode.
3. **The finite family (LANDED, probably not needed).** `Lset-fin`
   (src/L/Coding/EnvSupply.lagda.md:762) stages `finSet k h` at
   `sucV σ`, and `sucK` (:204) absorbs the successor at a succ-closed
   limit, so `env g` (a finSet by `envIsFinSet`,
   src/L/Coding/InL.lagda.md:177) CAN be staged directly should a
   clause site refuse the slot route. `envL`
   (src/L/Coding/InL.lagda.md:181) gives only `isL`, not a stage; do
   not reach for it.
4. **Pair descent (LANDED; first pass of this dispatch mispriced it
   as missing, corrected on the second read).** From
   `pr u v ∈ Lset γ` conclude `u ∈ Lset γ` and `v ∈ Lset γ`. The
   construction exists: EnvSupply's `Fact (K : S) (Ktr : isTransV
   (fst K))` (src/L/Coding/EnvSupply.lagda.md:450) carries `prK`
   (:453) and `valK` (:463), and `Lset γ` is a transitive V-set by
   `layer-trans (Lset-layer γ)`
   (src/L/Constructible.lagda.md:183, `Lset-layer` at :246).
   EnvSupply's own `AtLevel` module is that exact instantiation; the
   probe lands it as its section 9 with the three wrappers above.
   Needed wherever a staged pair's COMPONENT must be staged: the
   closedAt successor witnesses (`sucAtL-adequate` reads the witness
   as `sucV (fst ar)`, the second component of a pair in the staged
   C), the shapedAt arity/component witnesses (components of a member
   key), and the term-value witnesses (second components in an
   environment member). NOTE: `𝒟ₒ→isL`
   (src/L/Axioms/Basic.lagda.md:98) gives only `isL`, NOT a stage; it
   is not a shortcut for anything here. `envL`
   (src/L/Coding/InL.lagda.md:181) likewise gives only `isL`.
5. **The entry atoms (LANDED).** `appAt` by `d0eq` (section 3); the
   `extAt` frames (Model.lagda.md:663) are pure ∀-frames whose
   standard proofs restrict; the twelve `∀̇∈ (var C)` filters are
   identical in both readings, so the SIX Δ₀ clauses and
   `bodyAll`/`body∀` restrict outright.

So the inventory is FIVE OF FIVE LANDED. The bounded assembly needs no
new construction at any leaf; what remains is plumbing and frames.

## 5. W3, THE WIDEST UNMEASURED TERM (measured)

Whether the two inhabited bounds plus `Sat-at-asConst` plus
`relativize-correct` close bounded fill: **YES at the all-arity
hypothesis, at the re-priced cost.** The brief guessed 40 to 100 lines
for the composition. The probe is 537 lines with the assembly absent;
the assembly, after this dispatch's check and with the descent package
landed, is:

- keyArityAtLᴬ + the closedAt/shapedAt walks at `clo` and `slot`
  (6 restricting clauses + 2 descent clauses; twelve alternatives,
  each one binForm-in/unForm-in with descent-staged witnesses):
  120 to 180 lines;
- satGraphAtᴬ (three staged witnesses `slot`/`satTable`/`A` by the
  shell's folds; pin, appAt by d0eq; domAt by descent; twelveAt by
  the clause walk of section 3): 150 to 250 lines;
- DefinesAtᴬ (extAt restricts; the inner ∃̇ witness `envOne (fst y)`
  staged by `Lset-fin` + absorb, or by the entry reading
  Powerset.lagda.md:139): 40 to 60 lines;
- the main term: about 5 lines.

TOTAL: roughly 315 to 495 new lines against the deepest formulas in
the tree (the bndRel frames reach depth 11). The prior dispatch's
"~275 lines" underestimated because it trusted d0eq on twelveAt.

## REMAINING WORK (the next coder's brief, in order)

1. **keyArityAtLᴬ** (~15 lines): outer ∃̇ᴬ witness `codeS A ψ`; stage
   its fst through the keyS equation the 734 climb already relates to
   `code∈γ`.
2. **isCodeAtᴬ's second conjunct** (the closedAt/shapedAt walks at
   `clo`, peel `closure-inv`) and then at `slot` (peel `slot-inv`) in
   the satGraphAtᴬ step: ONE walk written once against a peel. Every
   leaf staging move is `Desc`'s `pr↓`/`key↓`/`val↓`, the transitivity
   link, or the Henv envSet slot (inventory items 1 to 5).
3. **satGraphAtᴬ** and **DefinesAtᴬ**, then **the main term** (~5
   lines): `subst` along
   `sym (CRγ.relativize-correct (DefBody w) δ)` applied to the
   conjunct-conjunction.
4. **The staged-Sat induction**, ONLY if the mathematician rules the
   all-arity 740 reading out: carve the Sat sets at an own stage
   (`AtStage.separateAt` at `+ω σ₀`, `mkReflect` bridge, `uniqueL`
   equation; the design is in section 2), roughly 150 lines.

## MEASURED TODAY

- dependents: L.Coding.Powerset => 5; supply: defat-fill-asConst => 0
  (unchanged; the obligation stays supply-0 until the assembly lands).
- floor (sections 1-2 + types, hole standing): 1.18 s, 343 MB
  (runs/p-2-floor.out).
- state at the first return: 3.85 s, 725,812,328 B, one hole, 496
  lines (runs/p-24-final.out).
- one heap kill at the 2 g wide cap, routed same-dispatch by replacing
  the mutual Delta0 walk with the equality induction and re-testing
  (owner's ruling 2026-08-23; the new shape was tested, p-6 onward).
- this dispatch (the lint re-dispatch): the twelve-clause check and
  the staging inventory are reading measurements at `file:line`
  (sections 3 and 4); the descent package landed as section 9 of the
  probe, 537 lines; delivered run p-26-desc, 4.01 s, 746,520,576 B
  (34.8 percent of the 2,147,483,648-byte wide cap), EXIT=42 with the
  hole as the only error. p-25-desc is a retained parse slip (an
  unparenthesised `# k` inside `⟨ ⟩`), fixed in one edit; the bytes
  p-26 ran are byte-identical to the delivered `.txt`.

## FILES

- agents/tasks/LJ-1-742/Probe742.agda.txt (the probe; .txt because one
  hole is open; renamed from Probe742.agda per the brief's naming rule;
  537 lines, sections 1 to 9)
- agents/tasks/LJ-1-742/lj-1.742-report.md (this file)
- agents/tasks/LJ-1-742/runs/ (p-1 through p-24, every run logged with
  GHCRTS, stamps and EXIT; accept-1.out is the failed accept; p-25-desc
  and p-26-desc are this dispatch's runs, the latter on the delivered
  bytes)

## WHAT THE NEXT BRIEF NEEDS

1. A ruling on THE 740 TYPE (all-arity vs arity-1): it decides whether
   the next dispatch carries the staged-Sat induction (+150 lines) or
   not.
2. The continuation dispatch should name this file's `remaining-goal`
   as the sub-obligation, with the four conjunct-builders as the scope
   and `Probe742.agda.txt`'s sections as the frozen prefix; sections
   1 to 9 now, section 9 (`Desc`) being the descent package the walks
   call. Split at section 3 of this report: the twelve-clause check
   is the new content the shell did not have.
3. Do not re-fund: the five inventory items (section 4) name what is
   landed, and the probe's section 9 instantiates item 4; `envL` gives
   no stage; `𝒟ₒ→isL` gives no stage.
4. Nothing in this file lands in `src/`; the assemblies are probe-local
   and stay there until the trophies' campaign re-opens the coding
   chapters.

## ARCHIVE USED

All five injected archive candidates were read at their heads and are
DECLINED, not used. This return is an assembly of live files: the
predecessor probes and reports named in section 0, the landed masters
cited at `file:line` in sections 3 and 4, and this task's own runs.

- archive/dev/ORCHESTRATION.md:1 `# ORCHESTRATION: the orchestrator's
  operating rules`. Declined: not used. The pod loop's retired
  dispatching rules play no part in a reading measurement of landed
  formulas.
- archive/dev/DD-archived.md:1 `# THE \`DD\` RULING SERIES, archived
  in full 2026-08-18`. Declined: not read beyond the head. The live
  clauses this dispatch answers to are in the slot file and the brief;
  W2 and W4 were answered in the shell dispatch and are not re-opened
  by a lint repair.
- archive/dev/PLAN-archived.md:1 `# ARCHIVED 2026-08-20`. Declined:
  not read beyond the head. The live screen is `dev/pod/screen.toml`
  and the live direction is `dev/pod/direction.md`.
- archive/dev/STATUS-archived.md:1 `# STATUS-archived: the goal table
  of the internalization route`. Declined: not read beyond the head.
  This task's route is the live queue's, not the archived table's.
- archive/dev/TASKS-archived.md:1 `# Archived task index: the
  \`L3.32-T\` series`. Declined: not read beyond the head. The
  predecessors this task needed (729, 734, 735, 736, 738) are live
  files cited at `file:line` in section 0.

## LITERATURE USED

All five injected literature candidates were read at their heads and
are DECLINED, not used. The verdict quotes no book: every step in
sections 3 to 5 is an in-tree fact at `file:line`.

- dev/literature/glossary-review-2026-08.md:1 `# Glossary review: the
  119 pre-protocol entries`. Declined: not used. A raw `.agda` probe
  and its records carry no translation surface.
- dev/literature/devlin-errata.md:1 `# Devlin errata: documented error
  classes (do-not-repeat checklist)`. Declined: not read beyond the
  head. This dispatch cites no Devlin page; the fill is in-tree
  assembly.
- dev/literature/primary-sources.md:1 `# Primary sources, second
  round: Jensen manuscript, Devlin, Jech`. Declined: not used. The
  fetch map is the literature team's record; this dispatch fetches
  nothing.
- dev/literature/level-formula-slot-roles.md:1 `# The level-hood
  formula: arity, what it binds, what stays free`. Declined: not used.
  The level formula plays no part in the bounded graph walk.
- dev/literature/BIBLIOGRAPHY.md:1 `# Bibliography for the rud
  route`. Declined: not read beyond the head. No source beyond the
  tree was consulted for this dispatch.

# LJ-1.740 report: `Sat-at-asConst`, Sat at the carrier-bounded alphabet

(Written as a skeleton before the first Agda run and filled as the runs
landed; see C-22, `dev/LESSONS.md:2307`.)

## HEAD

head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.740
obligation: agents/tasks/LJ-1-740/Probe740.agda::Sat-at-asConst
verdict: **PARKED, NOT CLOSED.** The obligation's type is priced TRUE
(D-10 below) and the full proof route is designed;  the delivered
`Probe740.agda` (555 lines) TYPECHECKS GREEN (p-104: EXIT=0, 1.82 s,
417,611,776 B, 19.4 percent of the wide cap) and carries everything up
to and including the placement core:  the stage scaffold, the placement
core `place` (the AtStage carve plus the extensional identification of
`Sat A chi` with the carved set), and the `dIs` Delta0 conversion
layer.  NOT delivered:  the bounded description `Bd` with its
per-constructor certificates and adequacy, the climb `R`, and the merge
+ `Sat-at-asConst` assembly -- those are fully designed (Section 3 of
this report and the review), partially written, and parked in
`runs/unfinished-4c-5-6.agda.txt` (a `.agda.txt` snapshot;  it does not
typecheck and is not claimed to).  The obligation name is NOT exported
as an inhabited term;  no claim of closure is made.  Nothing landed in
`src/`.  Per the brief's branch table this return is the transfer-park
shape:  exit 0, this report changed, no `review-of-LJ-*-*.md` written.

## 0. THE PREDECESSOR QUESTION

| hypothesis / input | predecessor's delivery | verdict there |
|---|---|---|
| the corrected target | agents/tasks/LJ-1-736/review-of-Sat-in-carrier-lim.md (section "Corrected targets", option 1) | 736 NO-GO on `Formula S n` at full scope; the carrier-bounded alphabet named as the first corrected target | this brief IS that ruling; the probe inhabits exactly that shape's scaffolding |
| the 736 semantic kernel | Probe736.agda:88-135, green | the atom-clause transport, both directions | reused as the reading for the atom-adequacy; not re-funded |
| the room | agents/tasks/LJ-1-735/Probe735.agda (the merge and close), green | `envSet-in-carrier-lim` GO | the merge structure (Lset-out, ord-tri, the three cases) is re-targeted here as the `WithStage` room; `envSetNumeral∈` is the supply |
| the landed carve | src/L/Axioms/Separation.lagda.md (`AtStage`: satBridge, carveIn/carveOut, carve∈𝒟ₒ, ⊨-transport) | green in tree | the whole placement route runs on it; nothing re-derived |

No predecessor NO-GO is contradicted.  The module-hypothesis clause:
`asConst-in-carrier` has no predecessor;  the brief authorizes it as a
hypothesis (supply 0) and the probe takes it as one explicit argument,
typed `(A : S) (m : ⟪ fst A ⟫) → ⟨ fst (asConst A m) ∈ˢᵥ fst A ⟩`.

## 1. WHAT WAS BUILT (all in Probe740.agda; nothing in `src/`)

1. **Stage scaffold** (`WithStage`):  given the 735 close's five facts
   (one stage `m` in γ with ω, the carrier's placement, and the
   carrier's one-up stage inside `+ω m`), it fixes `σ₀ = +ω (+ω m)`,
   the stage set `Om = LsetS σ₀ oσ₀` (the uniform witness bound), the
   `Room` record (A, envSet A k for every k, the numerals `numS k`,
   and every `asConst A m′`, all placed), `roomσ₀` (envSetNumeral∈
   lands envSet uniformly at `sucIter 4 (+ω m)`;  numeral∈limit
   lifted twice;  the hypothesis through stage transitivity), the
   successor step, the two monotone lifts, `mem-trans`, and the
   Kuratowski pair decomposition `snd∈L`.
2. **Placement core** (`SatPlace.place`, green as delivered):  for any
   `χ : Formula S n` whose bounded description `Bd` is supplied with
   its Δ₀ certificate, its `BoundedFo (BelowAt β)` certificate, and a
   pointwise adequacy against `cond A χ` (restricted to
   `z ∈ envSet A n`), it identifies `Sat A χ` with the AtStage carve
   of `(the envSet bound) ∧̇ (the lifted description)` by
   extensionality and concludes `⟨ Sat A χ ∈ˢ LsetS (sucV β) … ⟩`.
   Both directions run through the landed `carveIn`/`carveOut` and the
   Δ₀ satisfaction transport.
3. **Arithmetic** (`plus-zero`, `plus-suc`, `plus-assoc`, the bare
   order `≤ⁿ` with transitivity, `m≤ⁿ+`, `≤ⁿ-zend`, `sub≤bin`):  the
   climb's stage bookkeeping, self-contained, no library order.
4. **Delta0 helpers** (`Δ₀-prAtL`, `Δ₀-appAt`, `Δ₀-consAtL`):  the
   generic lift of the landed certificates for the unlifted atoms,
   with the bounded-fo argument solved by conversion, exactly the
   `src/L/Condensation.lagda.md` pattern.
5. **The conversion layer** (`dIs`, `dIsΔ₀`, `dIs-var-in`,
   `dIs-var-out`, `tmIs→dIs`, `dIs→tmIs`):  tmIs with the numeral
   witness bounded by the stage set;  adequacy both directions from
   the landed tmIs readers plus appAt-adequate.
6. **PARKED** (designed, partially written,
   `runs/unfinished-4c-5-6.agda.txt`):  the bounded description `Bd`
   per constructor (propositional clauses are `cond` itself, hence
   their adequacy is the identity;  atom and quantifier clauses bound
   the witnesses by the stage set and by `envSet A (suc n)`), the
   per-constructor certificates and adequacy, the cons-graph route
   (`envSet-out` + `consAtL-adequate` + `graph-envSet`), the climb
   `R` with `sizeψ` arithmetic, and the merge + assembly.  The
   witness-boundedness argument (D-10's atom pricing) is complete on
   paper:  every cond-witness (the atom escorts, the numeral witness,
   the tmIs guard) reaches the stage set through `z ∈ envSet A n` plus
   stage transitivity plus the pair decomposition;  the cons extenders
   reach `envSet A (suc n)` through the Bridge's own
   `consAtL-out`/`graph-envSet` circuit.

## 2. THE FLOOR AND THE RUNS

The floor was NOT separately run this dispatch -- a defect against the
heavy-object rule, recorded here rather than papered over.  The closest
measured evidence:  the delivered file's verdict is 1.82 s / 418 MB
(p-104), the Section-3-era file checked at 1.9 s / 581 MB (p-34), and a
bare parse-error run on the same import cone sits at 0.34 s (p-1) --
so the import cone, not the probe's own rows, carries the wall, and
there was nothing to trim.  The next dispatch should run the floor
harness first, as the rule demands.

| run | wall | peak RSS (B) | note |
|---|---|---|---|
| p-1 to p-9 | 0.34-1.5 s | 178-347 MB | import/scope defects (prAtL, Ω-clash with Base.Truth's Ω, Unit scope), the ≤ⁿ fixity defect, plus-zero/plus-suc directions |
| p-10, p-13, p-22, p-23, p-30, p-37, p-55, p-56, p-90, p-94, p-97, p-100 | artifact | - | the runner artifact (`time: signal: Invalid argument`);  each re-run of identical bytes recorded as p-NNb/p-NNc |
| p-19 | 1.45 s | 346 MB | GREEN: scaffold |
| p-26 | 2.06 s | 559 MB | GREEN: + placement core |
| p-34 | 1.9 s | 581 MB | GREEN: + kit and dIs conversions |
| p-45-era | - | - | Section 4 appended;  defect rounds (glyphs, module-param prepending, Where-scope) |
| p-52 to p-56 | - | - | Section 4c appended;  the ∃̇∈-satisfaction shape measured off the error (truncated Σ with an Ω-pair);  bnd∈ introduced |
| p-61 to p-65 | - | - | place restructured to explicit β/oβ args;  Section 4 scope errors |
| p-71 to p-81 | - | - | bddBd block moved;  the ×-nesting and glyph defects |
| p-97, p-100, p-102 | - | - | the ≤ⁿ recursion defects (sub≤bin) |
| p-103 | 4.50 s | 665 MB | GREEN: delivered bytes after the cut-back |
| p-104 (verdict) | **1.82 s** | **417,611,776 B** | **EXIT=0, green, delivered bytes, warm** |

Heap wall: none.  Peak 665 MB (p-103), 31 percent of the 2,147,483,648
-byte wide cap.  System-side kills:  from p-50 on, several runs were
SIGKILLed by the machine's agda-watchdog swap guard
(`_build/tools/agda-watchdog.log`: "swap 8758MB >= 8192MB", 05:02
through the late runs) and by the same guard's free-percentage branch;
each such run was re-run after a wait, per the 729/735/736 protocol.
Two direct re-runs (p-50b's file, p-56b, p-97b/c, p-98) were themselves
killed;  the run that landed is the recorded verdict.

## 3. WHAT THE NEXT BRIEF NEEDS

1. **The route is fully specified;  price the continuation, not the
   design.**  The parked pieces in `runs/unfinished-4c-5-6.agda.txt`
   are ~800 lines of written-but-unverified Agda:  `envSet-graph`,
   `consAt-route`, `Bd`, `bdΔ₀`, the four quantifier adequacies
   (named-helper style), `bddBd`, the climb `R`, and slots for the
   merge + assembly.  The known-open defects at park time:  the
   `NeedsAt`/`bddBd` block must move after `Bd`/`bdΔ₀` (order), the
   ∀̇∈/∃̇∈ adequacy bodies are unverified, and Section 6 (merge +
   `Sat-at-asConst`) is unwritten.  Estimated remainder:  150-250
   lines of new glue plus the defect rounds.
2. **The W3 estimate (250-450) undersold the full-machinery route.**
   The measured shape:  the placement core + scaffold alone is 555
   green lines;  the full climb as designed lands near 1,100-1,300.
   The overage is the twelve-clause adequacy and the stage
   bookkeeping -- both forced by `cond`'s own unbounded witnesses.
   A shorter route exists ONLY if a landed "bounded description of the
   cons-shape" appears;  none exists today (`bddCons` is private in
   `L.Coding.Model`, and `graph-envSet`/`consAtL-out` from the Bridge
   are the exported workaround this probe uses).
3. **Do not re-fund**:  the placement core (Probe740.agda, green), the
   AtStage carve machinery, `envSetNumeral∈`, the 735 merge, the dIs
   conversions, the Δ₀ lift helpers, `snd∈L`.
4. **D-10 answer**:  the atom `var 0 ∈̇ asConst m` was priced first and
   is TRUE at this alphabet -- the atom clause's witnesses reach the
   stage set through z's membership chain (slot-bounded/asConst-bounded
   in the probe), so the 736 defect does not fire here.
5. **The consumer**:  `src/L/Coding/Powerset.lagda.md:473-522` (`toS ψ
   = mapFo (asConst A) ψ`, the fill's second existential) is exactly
   the shape this obligation states;  a GO there consumes this GO
   directly.

## 4. PRICE

| item | value |
|---|---|
| Agda wall, verdict run | 1.82 s (`runs/p-104.out`, warm) |
| peak, verdict run | 417,611,776 B, 19.4 percent of the 2,147,483,648-byte wide cap |
| floor run | NOT RUN (defect;  see section 2) |
| runs this dispatch | p-1 to p-104 plus the b/c artifact re-runs;  12 artifact re-runs total |
| system-side kills | 5 (agda-watchdog swap guard;  log cited above) |
| heap wall | none |
| in-file / in-fence lines | 555 total / 0 (raw `.agda`;  the ratio bar cannot fire) |
| parked-but-written lines | ~800 in `runs/unfinished-4c-5-6.agda.txt` (not typechecked) |
| brief estimate (W3) | 250 to 450 lines;  the delivered-plus-parked total is ~1,350 -- the estimate undersold the adequacy plumbing |
| caliber | `-A64m -I0 -M2g`, never set here |

## 5. W2 ANSWER

The placement core, the conversion layer, and the certificate builder
are written ONCE at the generic carrier A and the generic stage β;  the
twelve constructor-cases are the only per-constructor code, and the six
propositional ones are the identity (there `Bd` is `cond` itself).  No
deadline forced a fixed form;  no conflict to report.

## 6. WHY PARKED, NOT STOPPED

The target is priced TRUE and no premise failed -- a stop would
misreport it.  The honest state is a park:  the design is complete and
its hardest third (the placement core) is machine-checked;  the
remaining third is assembly whose defect-rounds outran this dispatch
(plus the machine's swap-guard killing five agda runs late in the
dispatch).  The next dispatch resumes at `runs/unfinished-4c-5-6.agda.txt`
with the report's section 3 as the continuation plan.

## ARCHIVE USED

All five injected archive candidates are DECLINED, not used.  The
design and the park rest on landed masters and live predecessor files
cited at `file:line` above.

- archive/dev/ORCHESTRATION.md: declined, not read;  the pod loop's
  history bears on dispatching, not on a formula-alphabet placement.
- archive/dev/DD-archived.md: declined, not read;  the clauses this
  dispatch answers to live in the slot file and the brief.
- archive/dev/PLAN-archived.md: declined, not read;  retired plans name
  no Sat-bound obligation.
- archive/dev/STATUS-archived.md: declined, not read;  standing status
  is `dev/pod/screen.toml` and this task's record is its own runs
  directory.
- archive/dev/TASKS-archived.md: declined, not read;  the predecessor
  files this task needed (LJ-1.731, LJ-1.735, LJ-1.736) are live files
  named by the brief and cited in section 0.

## LITERATURE USED

All five injected literature candidates are DECLINED, not used.  The
measurement quotes no book:  every step is an in-tree lemma cited at
`file:line` in sections 1 and 3.

- dev/literature/glossary-review-2026-08.md: declined, not used;  a raw
  `.agda` probe carries no translation surface.
- dev/literature/devlin-errata.md: declined, not used;  the route this
  dispatch builds is in-tree, not a do-not-repeat checklist item.
- dev/literature/primary-sources.md: declined, not used;  no primary
  source was consulted for the placement core or the adequacy.
- dev/literature/BIBLIOGRAPHY.md: declined, not used;  no source beyond
  the tree was consulted.
- dev/literature/level-formula-slot-roles.md: declined, not used;  the
  slot census belongs to the graph tasks and plays no part here.

# LJ-1.422#1: adversarial review

## HEAD
head_slot: mathematician_adversarial. machine: shared.

The return under attack is the NO-GO of the coder slot:
`agents/tasks/LJ-1-422/lj-1.422-report.md` and its obstruction
`agents/tasks/LJ-1-422/review-of-kappa-arrow-data.md`. The author slot is
named at `agents/tasks/LJ-1-422/lj-1.422-report.md:3`. The critic is not
the author, so the invariant holds for this dispatch. No commit, no push.

## THE INSTANCE FACTS

Six facts, from the program's accept record
(`agents/tasks/LJ-1-422/runs/accept-1.out`):

- exit code 42 (`accept-1.out:22`, `# exit 42`).
- error class `other` (`accept-1.out:21`).
- no heap wall (`accept-1.out:24`, `"heap_wall": false`).
- in-fence lines 0 (`accept-1.out:18`).
- obligations delta 0 (`accept-1.out:19`).
- one Agda run, rc 42, 1.09 s, on `Probe422.agda` (`accept-1.out:16`).

`model`, `effort` and `heads_sha256` of this instance are NOT retrievable
today. `dev/pod/transitions/2026-08.jsonl` has 157 lines, and its last row
is task `LJ-1.399` at `2026-08-19T13:31:57Z`
(`dev/pod/transitions/2026-08.jsonl:157`, `"task": "LJ-1.399"`). No
`LJ-1.422` row exists. The nearest identity evidence is the pod stamp
(`agents/tasks/LJ-1-422/.pod:1`, `heads=e70397be...`). This is a gap on
the program side. It is not a defect in the return: the return cites no
transition row.

## QUESTION 1: DOES THE VERDICT LINE MATCH ITS OWN BODY

The verdict line has four claims
(`agents/tasks/LJ-1-422/lj-1.422-report.md:15-21`):

1. "The truncated arrow is delivered." Agrees with the body:
   `src/L/Cardinal.lagda.md:133` and
   `agents/tasks/LJ-1-406/Probe406.agda:88`. Both resolve.
2. "No live untruncation device covers that carrier." Agrees with the body
   FOR THE THREE DEVICES THE BRIEF NAMED. See R3 below for why this is
   narrower than the line suggests.
3. "The orthodox size proof does not name this arrow as data." Agrees with
   the body. The load-bearing citation resolves:
   `dev/literature/truncation-and-selection.md:83`.
4. "The missing device is a well-order on the injections. It is absent."
   THIS CLAIM IS STRONGER THAN THE BODY. Two defects:

**R1. The named missing device is an analysis, not a measurement.** The
body proves: no `SWO` on an ambient function type occurs in `src/`
(49 sites, six shapes), and the classical text says a canonical injection
needs a well-order on the injections
(`dev/literature/truncation-and-selection.md:335`). The body does NOT
prove that this well-order is the device THIS arrow needs, because the
body never examines the route that avoids it: re-present the choice as a
choice of GRAPHS, which are members of stages, then select the least graph
with the stage well-order, then read the function back off the graph. The
live halves of that route exist in `src/` today:

- L-pairing of members: `src/L/InjChain.lagda.md:291`
  (`pw (m , k) = prʟ (toD m) (toC k)`).
- graph carving by separation over a bounded stage:
  `src/L/InjChain.lagda.md:188` ("ROW 1.  The composition of two injection
  graphs, by separation.") and `src/L/Absorption.lagda.md:400`
  (`(sep : (b : S) (φ : Formula S 1)`), with the bound built by
  `boundingOrd` (`src/L/InjChain.lagda.md:68`, "A carve needs a set that
  already holds every pair it will keep.").
- an injective graph as an OBJECT-LANGUAGE formula:
  `src/L/Coding/Injection.lagda.md:44` (`injAt : ∀ {n} → Fin n → Formula S n`).
- untruncation of a unique fiber, so a graph yields a function as data:
  `src/L/Coding/Injection.lagda.md:98`
  (`toVal : (x : S) → ∥ Fib x ∥₁ → Fib x`) with injectivity at `:117`
  (`toFun-inj u v e = injAt-out zero γ ij ...`), packaged as
  `module Small (F D C : S)` at `:123`.
- a well-order on every stage's member type:
  `src/L/Choice/Step.lagda.md:730`
  (`orderAt : (γ : S) → IsOrd γ → SWO (Mem (Lset γ))`), lifted to the
  presentation at `src/L/Choice/Step.lagda.md:272`
  (`carry : (A : S) → SWO (Mem A) → SWO ⟪ A ⟫`).
- `leastOf` DOES return data: its output is a Sigma
  (`src/L/WellOrder/Base.lagda.md:158`,
  `leastOf : {ℓ'' : Level} → LEM ...`), consumed as data by the cardinal
  chapter itself (`src/L/Cardinal.lagda.md:116-117`,
  `least : Σ[ γ ∈ ⟪ sucV (fst α) ⟫ ] IsLeast w InjP' γ`).

The ONE link of that route with no measured support: a source for ONE
constructible graph of an injection `⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫`.
The truncated `κ-inj` cannot supply it: separation takes a
`Formula S 1` (`src/L/Absorption.lagda.md:400`), an ambient function is
not a formula parameter, and coding the ambient function as a set needs
the function as data first. That missing link is a DIFFERENT device from
"a well-order on ambient injections", and the return did not name it, so
the architecture sentence
(`agents/tasks/LJ-1-422/lj-1.422-report.md:232`, "That is an
architecture fact, not a route fact") rests on an enumeration that never
visited the route. The obstruction file repeats the same overreach
(`agents/tasks/LJ-1-422/review-of-kappa-arrow-data.md:43`, "Nothing in
this tree makes that choice.").

**R2. One certainty the evidence does not give.** The W2 section says
"the data form is not inhabited"
(`agents/tasks/LJ-1-422/lj-1.422-report.md:156-157`). The body shows that no
enumerated device DELIVERS the term. It does not show the type is empty.
Non-delivery is a statement about the tree; non-inhabitance is a statement
about the type. The Boundary forbids a certainty the evidence does not
give. The D-10 section of the report also states an "if and only if"
(`agents/tasks/LJ-1-422/lj-1.422-report.md:137-139`) that its citation
does not license: the cited theorem is about LIFTING a truncation
(`dev/literature/truncation-and-selection.md:163`, "So the question "can
this truncation be lifted" is always the question "does"), not about all
possible constructions of a canonical injection.

Verdict on QUESTION 1: PARTIAL MATCH. Claims 1 to 3 match the body. Claim
4 overclaims, in both files of the return.

## QUESTION 2: DOES EVERY LOAD-BEARING file:line RESOLVE TODAY

I opened every citation. All resolve:

- `src/L/Cardinal.lagda.md`: `:47-48` (`_↪_` as the Sigma), `:91` (sealed
  `w`), `:117` (`least = leastOf w lem InjP' nonempty`), `:132-133` (the
  "still truncated, still not an hProp" comment above `κ-inj`).
- `src/L/WellOrder/Base.lagda.md:158` (`leastOf` signature).
- `src/L/Ordinal/SquareLaw.lagda.md`: `:10-11` ("the archived route is
  never formed."), `:70`, `:77`, `:127`, `:176` (`ordSWO : SWO ⟪ α ⟫`),
  `:282`, `:285`, `:308`, `:755`.
- `src/L/Choice/Step.lagda.md`: `:220`, `:226`, `:272`, `:373`, `:429`,
  `:730`.
- `src/L/Hull.lagda.md:60`, `:158` (`wL : SWO SL`).
- `src/L/StageCardinal.lagda.md:228` (`module OrdSWO`), `:258`
  (`ordSWO : SWO ⟪ α ⟫`).
- `src/L/Choice/Name.lagda.md:804`, `src/L/Choice/Faithful.lagda.md:400`,
  `src/L/Choice/Finite.lagda.md:596`, `:884`, `:1114`.
- `agents/tasks/LJ-1-406/Probe406.agda:82`, `:85`, `:88`;
  `agents/tasks/LJ-1-406/lj-1.406-report.md:13`, `:16-17`.
- `agents/tasks/LJ-1-417/Probe417.agda:80`;
  `agents/tasks/LJ-1-417/lj-1.417-report.md:18-19`.
- `agents/tasks/LJ-1-418/lj-1.418-report.md:19-24`.
- `dev/pod/audit-2026-08-20.md:102-103` (finding F8).
- Archive: `archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:4`,
  `.../L/Ordinal/Pairing.lagda.md:4`, `.../L/CardinalCount.lagda.md:6`.
- Literature: `dev/literature/devlin-II5.md:413` and `:127-131`;
  `dev/literature/j-hierarchy.md:122-132`, `:147-149`, `:181`;
  `dev/literature/digest.md:56-63`; `dev/literature/truncation-and-selection.md`
  at `:75-86`, `:83`, `:147-148`, `:157-165`, `:332-337`.
- Probe self-citations: `agents/tasks/LJ-1-422/Probe422.agda:42-43`,
  `:49-54`, `:61-65`, `:70-74`; the error spans `:50.34-35`, `:53.37-38`,
  `:65.55-72` match `runs/w3-1.out`, `runs/w3-2.out`, `runs/w3-3.out`
  exactly, including "real 1.05" and "EXIT:42" in `runs/w3-3.out`.

One wording misfit, not verdict-changing: device 2 says "a data payload
does not come out" and cites
`dev/literature/truncation-and-selection.md:147-148`. That line is about
`leastOf` at an INDEX-valued predicate. `leastOf` itself outputs a Sigma
(`src/L/WellOrder/Base.lagda.md:158-160`), and `src/L/Cardinal.lagda.md:116`
consumes it as data. The sentence should say the PAYLOAD of a truncated
predicate is a proposition, not that no payload can come out.

Verdict on QUESTION 2: PASSES. Every load-bearing citation resolves today.

## QUESTION 3: IS THE PREDECESSOR'S ENUMERATION COMPLETE

**The count reproduces.** I re-ran the pattern `': SWO|SWO ('` over
`src/`, files `*.lagda.md` and `*.agda`: COUNT 49. The audit's F8 lesson
(`dev/pod/audit-2026-08-20.md:102-103`) is answered: the re-run survives.

**R3. The pattern is not a census, and the enumeration is not the
measurement the verdict needs.** Three gaps:

1. The pattern misses `SWO` occurrences with no `: ` before and no `(`
   after. Example: `src/L/Choice/Step.lagda.md:738`
   (`stageOrder : (γ : S) → IsOrd γ → SWO ⟪ Lset γ ⟫`), a well-order on a
   stage member type, invisible to the pattern. I scanned the escapes
   (result-position `→ SWO`, `SWO ⟪`, projection uses `SWO.irr∙`,
   `SWO._<∙_`, and the tracked probes under `agents/tasks/`): no
   occurrence is an `SWO` on a function type or on `_↪_`. So the SHAPE
   conclusion ("no delivered `SWO` sits on the injection type") survives
   my wider scan, but the reported COUNT is a pattern count and the report
   does not say so.
2. The scope is `src/` only. The tracked probes also carry `SWO` sites
   (for example `agents/tasks/LJ-1-106/ProbeLJ1106A.agda`). My scan of
   those found no function-type carrier either, so this gap does not
   change the outcome, but the report's "No delivered `SWO`" silently
   excludes them.
3. THE MATERIAL GAP: the enumeration counts carriers, not PRESENTATIONS.
   It answers "does an `SWO` sit on the ambient function type". It does
   not answer "can the choice be re-presented on a carrier the tree well-
   orders", which is the question the orthodox route actually turns on.
   The re-presentation apparatus is live and was named in R1: `prʟ`
   pairing, graph carving by separation (`Formula S 1`), the `injAt`
   graph formula, `toVal`/`Small` graph-to-function untruncation, stage
   well-orders, and `leastOf`'s Sigma output. The return's device
   checklist visits none of them, and the brief listed only three devices
   ("Ask of each device, in this order",
   `agents/tasks/LJ-1-422/LJ-1.422.md:74`), so the brief partly
   caused the outcome. The escalation to "THE missing device ... an
   architecture fact" goes past what either the brief asked or the
   enumeration measured.

Verdict on QUESTION 3: the count is sound; the enumeration is INCOMPLETE
as support for the NO-GO's missing-device sentence.

## WHAT THIS REVIEW CONCLUDES

AGREES: the NO-GO stands for what it measured. The three named devices do
not deliver the arrow at this carrier. The probe is red and its error is
reported exactly. The literature reading is correct: the sources state the
cardinal inequality truncated and never name this arrow as data. A review
that agrees is a real result, and this review agrees with all of that.

REFUTES: the architecture sentence. The return names "a well-order on the
injections" as THE missing device and calls its absence an architecture
fact for `[LJ-2.5]`. The body's enumeration cannot carry that sentence,
because it never visited the graph-presentation route whose live halves
are `src/L/InjChain.lagda.md` and `src/L/Coding/Injection.lagda.md`. The
true unmeasured term on that route is:

    constructible-graph-source

ONE constructible graph of an injection `⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫`,
as a member of a stage. Given it, the live devices plausibly deliver the
arrow as data: least graph by the stage well-order, then `Small` reads the
function off with `toVal`. Without it, the route is blocked, and the
NO-GO's conclusion may well be true. Either way, the missing device the
return names is not established as the one the architecture question
needs.

DIRECTION FOR THE NEXT BRIEF, and it is guidance: queue the measurement of
`constructible-graph-source` before `[LJ-2.5]` consumes this NO-GO as
architecture evidence. The probe the coder should write applies the
`Small`/`toVal` device at this site with the graph source as a module
hypothesis, and separately measures whether any live chapter can discharge
that hypothesis (an object-language leastness formula, or a constructible
injection from the tower). Estimate basis: the `Small` instantiation in
`src/L/InjChain.lagda.md:299` is the closest delivered comparable of shape.

## ARCHIVE USED

The five candidates of this dispatch, each answered:

- `archive/dev/JOURNAL.md`: declined, not read. It is the archived
  per-episode journal. The three review questions need live code, the
  return, and the run record, not episode history.
- `archive/dev/ORCHESTRATION.md`: declined, not read. It is the retired
  orchestration record. The loop's operation is not in scope for this
  review.
- `archive/dev/DD-archived.md`: declined, not read. It is the archived DD
  ruling series. The live rules are `AGENTS.md` and
  `dev/pod/instructions/mathematician_adversarial.md`, both already in
  front of this dispatch.
- `archive/dev/PLAN-archived.md`: declined, not read. It is the retired
  plan. The live campaign state is `dev/pod/screen.toml`, already read.
- `dev/ARCHIVE.md`: declined, not used. This review retires no module.

Additional archive files outside the candidate list, read for QUESTION 2
verification:

- `archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:4`
  "The condensation lemma is the recognition step of constructibility theory."
- `archive/src/2026-08-09-rud-route/L/Ordinal/Pairing.lagda.md:4`
  "The cardinal step of the later chapters needs one fact about ordinals that the"
- `archive/src/2026-08-09-rud-route/L/CardinalCount.lagda.md:6`
  "object is Devlin 5.4's size claim for the definable hull, |M| ="

## LITERATURE USED

The five candidates of this dispatch, each answered:

- `dev/literature/devlin-II5.md:413`
  "|L_α| = |α| for α ≥ ω (`dev2.txt:117`, `dev2.txt:200-240`) is consumed at"
  Read. Used: confirms the size theorem the return names, and that it is
  a level-index equation.
- `dev/literature/truncation-and-selection.md:83`
  "**So a proof that only needs cardinal arithmetic never needs an injection as"
  Read. Used: confirms the orthodox conclusion is truncated.
- `dev/literature/truncation-and-selection.md:148`
  "index is a proposition. **A data payload does not come out.**"
  Read. Used: the return's device-2 citation; narrow, see QUESTION 2.
- `dev/literature/truncation-and-selection.md:163`
  "**So the question "can this truncation be lifted" is always the question "does"
  Read. Used: R2. The theorem bounds LIFTING, not construction.
- `dev/literature/truncation-and-selection.md:335`
  "`ω`. **A canonical injection needs a well-order on the INJECTIONS, which is"
  Read. Used: the return's missing-device citation; it licenses the
  greedy-failure fact, not the architecture sentence.
- `dev/literature/digest.md:58`
  "- **Q4 (the canonical well-order).** Stage-first, then minimal producer"
  Read. Used: the canonical well-order is stage-first, on the level. This
  supports the graph route of R1: the orthodox device orders MEMBERS, and
  graphs are members.
- `dev/literature/BIBLIOGRAPHY.md`: declined, not read. A source index.
  No citation in the return depends on it.
- `dev/literature/geology.md`: declined, not used. Grounds and forcing
  sources. Outside all three questions.

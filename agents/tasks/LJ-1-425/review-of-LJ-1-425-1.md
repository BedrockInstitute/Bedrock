# LJ-1.425: adversarial review of the LJ-1.425#1 return

slot: `mathematician_adversarial`, machine: shared. The return under attack
is `agents/tasks/LJ-1-425/lj-1.425-report.md`, with its obstruction file
`agents/tasks/LJ-1-425/review-of-internal-nonempty.md` and its probe
`agents/tasks/LJ-1-425/Probe425.agda`. The critic is not the author: that
return was written by the `coder` head, model `grok-4.6`. Write scope of this
review: this file only. No commit, no push.

## THE INSTANCE, FROM THE RECORD

The instance record was read in the MAIN tree, not in this worktree. The
worktree's own `dev/pod/transitions/2026-08.jsonl` ends at seq 158 on
2026-08-19 and holds no LJ-1.425 row. The live record is
`/Users/alsg/Agentic/Bedrock/dev/pod/transitions/2026-08.jsonl`, seq 464 to
490.

- model `grok-4.6`, effort `high`, heads_sha256 `e70397be`, role `coder`,
  tier `wide` (seq 464).
- The six facts, from the arm record `agents/tasks/LJ-1-425/runs/accept-1.out`:
  exit_code 42, error_class `unsolved_meta`, heap_wall false,
  obligations_open 1 with obligations_delta 0, seconds 1.67, 15 changed files
  with 0 in-fence lines.
- Branch row taken: `task-lj-1-425-no-go-stated`, escalation to this slot
  (seq 489).

## QUESTION 1: DOES THE PREDECESSOR'S VERDICT LINE MATCH ITS OWN BODY?

**MATCH, on all three clauses of the line.**

- "NO-GO on `internal-nonempty`". The body reports a hole at
  `agents/tasks/LJ-1-425/Probe425.agda:92`. `runs/final-hole.out:2` reports
  `UnsolvedInteractionMetas` at `Probe425.agda:92.18-22`, and
  `runs/final-hole.time` gives 1.93 s real. The accept record gives exit 42
  and obligations_open 1. The obstruction file
  `agents/tasks/LJ-1-425/review-of-internal-nonempty.md` states the same
  verdict and the same error.
- "GO on `κ-in-site-bound`". `runs/kappa-1.out` shows a clean check and
  `runs/kappa-1.time` gives 1.47 s real and 390529024 bytes maximum resident
  set size. The term sits at `Probe425.agda:65-69` and `δκ` at
  `Probe425.agda:71-72`, exactly as the body says.
- "GO on W3's implication `graph-in-site-bound`". The line is qualified by
  the word "implication", and the body says at once that "The unconditioned
  membership is not inhabited" and that the tree delivers no fact that pays
  the premise. Section 2 answers the brief's crossing question directly:
  "The crossing fact is none." A reader of the line alone cannot misprice
  this, because the body denies the stronger reading in the same breath.

**TWO BODY DEFECTS ATTACH TO THE VERDICT. NEITHER OVERTURNS IT.**

First defect. The load-bearing D-10 sentence "The pairs do not live in
`Lset (stage κ)`" is hand mathematics, and it is stated more broadly than it
is true. The tree delivers placement only: `pr∈Lset-suc` puts `pr x y` in
`Lset (sucV (sucV σ))` when `x` and `y` are in `Lset σ`
(`src/L/Axioms/Basic.lagda.md:596-598`, conclusion at :597). The tree has no
earliest-stage lemma for pairs, so the negative is not a delivered fact. As
hand mathematics it holds at a successor ordinal κ above ω: the top member γ
sits at `stage γ`, `stage κ` is its successor, and the pair of γ first
appears exactly at β. At a limit ordinal λ the sentence fails: each member x
of λ carries its pair two stages above x's own stage, and that lands below λ,
hence inside `Lset (stage λ)`. At such κ the identity graph plausibly IS a
member of `Lset β`, and the obligation is plausibly true there. The generic
term is still impossible, because successor ordinals exist in the tree (the
ordinal chapter delivers `suc-ord`, `src/L/Ordinal.lagda.md:96`) and the
statement fails at them. So the NO-GO verdict stands, but through a sentence
that is correct only in the successor case and is written as if it held at
every κ. This paragraph is my analysis. Its tree anchors are cited; its
stage arithmetic is not a delivered fact.

Second defect. The return undersells its own refutation. It refutes the
identity witness only, and leaves "another F might work" open. But `domAt` is
a biconditional (`src/L/Coding/Model.lagda.md:278-281`), and `domAt-in`
(`src/L/Coding/Model.lagda.md:294-296`) forces every member of the domain to
have a pair in `F`. The fourth `InjCode` conjunct also quantifies over
`pr (fst x) (fst y) ∈ fst F` (`src/L/Cardinal.lagda.md:223-228`). So at a
successor ordinal κ above ω, ANY `F` with `InjCode F κ δ` must contain a pair
for the top member. A member of `Lset β` is a separated subset of
`Lset (stage κ)` along `Lset-suc` (`src/L/Axioms/Basic.lagda.md:196`), with
the separated set's spec bounded by its carrier
(`src/L/InjChain.lagda.md:482`). The top member's pair is not in
`Lset (stage κ)`. So no `F` exists at all at successor κ, and the existence
claim is false outright there, not only with the identity witness. The
corrected statement in section 5 has the right shape; it asks for
`sucV (sucV (sucV (stage κ)))`, which is sufficient and slack by one stage
against the tight bound. This is also my analysis, on the same anchors.

## QUESTION 2: IS EVERY LOAD-BEARING CLAIM BACKED BY A file:line THAT RESOLVES TODAY?

**HELD, with three named exceptions, all in the D-10 paragraph.**

Every citation was opened and resolves, and says what the report claims:

- `src/L/Cardinal.lagda.md`: :163 `module SiteBound (a : S) where`; :166
  `β = stageBound (fst a) (snd a) .fst`; :171 `up : Mem (Lset β) → S`;
  :187-190 `Canonical.Good` over `Mem (Lset β)`; :230-231 `IsCardinalL`;
  :235 `module InternalLeastCard`; :239-243 `Good` with `Selected`'s one
  hypothesis at :243; :247 `leastOf (orderAt β oβ)`; :253 `δᴸ : S`; :257
  `δ-inj`.
- `src/L/Choice/Stage.lagda.md`: :366-368 `stageBound a p = bound2 ω
  (stage a p)`; :370-373 `bound-below₂`.
- `src/L/Ordinal.lagda.md`: :185-196 `bound2` as `boundingOrd` over a
  two-element family. The union-of-successors reading of β is backed by the
  construction and the prose at :140-160.
- `src/L/Axioms/Basic.lagda.md`: :196 `Lset-suc`; :596-598 `pr∈Lset-suc`.
- `src/L/InjChain.lagda.md`: :75 `module StageBound (I : Type ℓ) (g : I → S)`;
  :82 `b = boundingOrd I stg`; :93 `bnd = LsetS β oβ`; :468 `module Carve`;
  :513 the range-conjunct comment; :518 `sv`; :525 `ij`; :532 `dm`; :544
  `ran`; :551 the 8g heap comment; :553 `module Sm = Small`; :575
  `module InclGraph`; :598 `open Carve D C SB.bnd sub bel hasSeparationL
  public`; :604-607 `module OrdIncl` with `open InclGraph` at :607.
- `src/L/Stage.lagda.md`: :188 `stage-mem`.
- The probe: :49-54, :65-69, :71-72 and :85-92 resolve as claimed.
- The numbers: w3 medians 1.55 s and 398868480 bytes check against
  `runs/w3-1.time` (1.55 real, 398868480), `runs/w3-2.time` (1.57,
  398884864) and `runs/w3-3.time` (1.49, 398786560). kappa 1.47 s and
  390529024 bytes check. final-hole 1.93 s checks. All three w3 runs print
  `Checking`, which is the observable of a forced recheck.
  `dev/pod/direction.md:37` carries the SRC-collection sentence the report
  leans on.
- The absence claims, "the tree states no comparison between those two
  bounds" and "no delivered fact pays that premise", are backed by search,
  and I re-ran the search. `stageBound` from `L.Choice.Stage` occurs in live
  `src/` only at `src/L/Choice/Order.lagda.md:53`, `:681` and `:684`, and at
  `src/L/Cardinal.lagda.md:23`, `:166` and `:169`. `src/L/InjChain.lagda.md`
  never imports it, and no lemma relates the two devices.

The three exceptions, each hand mathematics with no `file:line`:

1. "It does not contain `sucV (stage κ)`."
2. "The pairs do not live in `Lset (stage κ)`." Also overbroad; see Question 1.
3. "A pair is not a member of a member."

The Boundary makes evidence `file:line`. These sentences carry a certainty
the tree does not deliver, inside a paragraph threaded with citations that
deliver only the placements. The verdict does not rest on them alone: the
machine-checked part, the hole at :92 and W3's unprovable premise, is
independent of them.

## QUESTION 3: IS THE PREDECESSOR'S ENUMERATION COMPLETE?

**COMPLETE.**

The C-42 sweep claims COUNT 2 in `src/`, both sites in
`src/L/Cardinal.lagda.md`: `Canonical.Good` at :187-190 and
`InternalLeastCard.Good` at :239-243. I re-ran the sweep for the stated
shape, a graph or `InjCode` witness demanded as `Mem (Lset β)` with β from
`stageBound`. The near-shapes were checked and are correctly excluded:

- `src/L/GCH.lagda.md:37-38`: `InjL a b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁`.
  The witness is a bare `S`. No site-bound membership is demanded.
- `src/L/CantorBernstein.lagda.md:33`: `Σ[ F ∈ S ] InjCode F a b`. Same
  exclusion.
- `src/FOL/Bernstein.lagda.md:119-167`: `domAt`-based coding at bare `S`.
  No stage bound appears in that file.
- `src/L/Choice/Order.lagda.md:681-702`: `boundOrd = stageBound a p .fst`,
  with the order element `orderL` built from pairs. But no demand exists
  that `orderL` be a member of `Lset boundOrd`. It is held as `S` with
  representation lemmas.
- `src/L/Hull.lagda.md:440-448`: `relL` at a plain ordinal, with adequacy
  lemmas only.

So COUNT 2 stands for the stated shape. The other enumerations also check:
`Selected` has no consumer in `src/`, the name occurs only at
`src/L/Cardinal.lagda.md:242`; `InclGraph` has exactly one consumer,
`OrdIncl`, at `src/L/InjChain.lagda.md:607`; nothing else applies `Carve`
with a `stageBound`-derived bound.

One wording slip, and it is not a defect of enumeration: the report says
"`InternalLeastCard` occurs only at `src/L/Cardinal.lagda.md:235` and
`:242`". The literal string `InternalLeastCard` occurs at :235 only. Line
:242 is `module Selected`, its submodule by qualification.

## VERDICT OF THIS REVIEW

**The return STANDS.** NO-GO on `internal-nonempty` at the present β is
correct, the W3 measurement is sound as far as it goes, and the sweep is
complete. A review that agrees is a real result. Three corrections belong in
the next brief that touches this site:

1. The D-10 negatives are hand mathematics, not delivered facts, and the
   sentence "The pairs do not live in `Lset (stage κ)`" is true only at
   successor ordinals above ω. The generic refutation runs through the top
   member of a successor ordinal, and through no other argument the return
   states.
2. The refutation is stronger than the return claims: through `domAt`'s
   biconditional (`src/L/Coding/Model.lagda.md:278-281`, `:294-296`) and the
   fourth `InjCode` conjunct (`src/L/Cardinal.lagda.md:223-228`), no `F`
   exists at a successor ordinal, so the existence claim is false outright
   there and not merely with the identity witness. At a limit ordinal the
   obligation is plausibly true at the present β, which is one more reason
   the corrected statement should quantify over a stage, as section 5 does.
3. The literal-string slip at `src/L/Cardinal.lagda.md:242`.

Nothing in this review re-opens LJ-1.425 at the present β.

## ARCHIVE USED

- `archive/dev/JOURNAL.md`: read line 1, `# ARCHIVED 2026-08-20`. Not used:
  a per-episode journal of the retired route. My three questions are
  answered against the live tree and the instance's own runs.
- `archive/dev/ORCHESTRATION.md`: read line 1, `# ORCHESTRATION: the
  orchestrator's operating rules`. Declined: orchestrator operating rules
  are not evidence about a mathematical verdict, a citation or a sweep.
- `archive/dev/DD-archived.md`: read line 1, `# THE `DD` RULING SERIES,
  archived in full 2026-08-18`. Declined: the DD clauses that bind this
  review already sit in `AGENTS.md` and in the slot file, retrieved live.
- `archive/dev/PLAN-archived.md`: read line 1, `# ARCHIVED 2026-08-20`.
  Declined: retired plan. The live plan is `dev/pod/queue.toml` and
  `dev/pod/screen.toml`, and neither was needed here.
- `dev/ARCHIVE.md`: read line 1, `# ARCHIVE.md: the archive registry`.
  Declined: no module was retired by the return or by this review, so no
  registry row is in scope.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: read line 1, `# Devlin II.5: the
  Condensation Lemma and the GCH in L`. Declined: this review judges a
  verdict, its citations and its sweep. No condensation or GCH provability
  question was opened by the three questions.
- `dev/literature/BIBLIOGRAPHY.md`: read line 1, `# Bibliography for the rud
  route`. Declined: not used.
- `dev/literature/digest.md`: read line 1, `# Digest: the orthodox form of
  the rud route, pinned from the collected literature`. Declined: not used.
- `dev/literature/geology.md`: read line 1, `# Geology dossier:
  set-theoretic geology sources and the five questions`. Declined: not used.
- `dev/literature/devlin-errata.md`: read line 1, `# Devlin errata:
  documented error classes (do-not-repeat checklist)`. Declined: the
  return's error class is `unsolved_meta` on an intentional hole, which is
  not a documented prose error class.

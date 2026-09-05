# LJ-1.454 review: adversarial review of LJ-1.454#1

## HEAD
head_slot: mathematician_adversarial
machine: shared
verdict: upheld

## THE RETURN UNDER ATTACK

The return is `agents/tasks/LJ-1-454/lj-1.454-report.md`, slot `coder`,
with the obstruction file `agents/tasks/LJ-1-454/review-of-rank-graph.md`
and the probe `agents/tasks/LJ-1-454/Probe454.agda`. The verdict line
(`lj-1.454-report.md`, section VERDICT) states: STOP, W3 typechecks the
type `Formula S 2`, Internal delivers the ORDER and not the RANK,
`rank-graph` omitted. Exit 0, obligation still open
(`runs/accept-1.out`, obligations delta 0, obligations open 1). That is
a stated NO-GO with a `review-of-*.md`, so this review attacks it. The
author was the `coder` head. This review is the
`mathematician_adversarial` head. The invariant holds.

## QUESTION 1. DOES THE VERDICT LINE MATCH ITS OWN BODY

It does. Each clause of the line rests on the body and on the tree:

1. "W3 typechecks the type `Formula S 2`". The type is stated at
   `agents/tasks/LJ-1-454/Probe454.agda:42-43`. The runs
   `runs/w3-2.out`, `runs/w3-3.out`, `runs/w3-4.out` all print EXIT:0.
   I forced a recheck here (interface deleted, one process): "Checking
   LJ-1-454.Probe454", 1.52 s real, exit 0. The claim holds today.
2. "Internal delivers the ORDER and does not deliver the RANK". The
   inventory binds nine exported formulas
   (`Probe454.agda:48-72`), and all nine citations resolve:
   `InLimitAt` at `src/L/Choice/Internal.lagda.md:166`, `FreeAt` at
   `:304`, `DenoteBody` at `:587`, `NameAt` at `:597-599`, `LexAt` at
   `:731`, `≺At` at `:741-742` with eight slot indices, `LeastNameAt`
   at `:910-911`, `StepBody` and `StepAt` at `:967-975`. I re-ran the
   search: `grep -in rank src/L/Choice/Internal.lagda.md` returns no
   line. The chapter prose supports the distinction at `:22` ("runs
   **no recursion of its own**") and `:709` ("Nothing recurses,
   nothing is").
3. "I omitted `rank-graph`". No `rank-graph` definition exists in the
   probe, and no hole: exit 0, and the branch table of the brief makes
   a hole exit 42. The program matched branch `stop-stated`: exit 0,
   `review-of-*.md` changed, obligations delta 0
   (`runs/accept-1.out`).

One sentence in the obstruction file is false as written.
`review-of-rank-graph.md` says "The name does not appear in
`agents/tasks/LJ-1-454/Probe454.agda`." The name appears in the header
comment at `Probe454.agda:14`: "--   TERM      `rank-graph` is
OMITTED." The claim the sentence gestures at, that no definition and no
hole exist, is true and measured. The sentence is a defect of wording,
not a crack in the verdict.

## QUESTION 2. DOES EVERY LOAD-BEARING CLAIM RESOLVE TODAY

I opened every load-bearing citation. All resolve:

- `agents/tasks/LJ-1-416/lj-1.416-report.md:15`, verdict line "**GO.**
  The obligation typechecks. The witness meter PASSes."
- `agents/tasks/LJ-1-416/Probe416.agda:105` `swo-rank : {A : Type ℓ}
  (w : SWO A) → A → S`, `:108` `swo-rank-ord`, `:111-114`
  `swo-rank-mono`, `:67-75` the Acc recursion.
- `agents/tasks/LJ-1-417/lj-1.417-report.md:19` GO, `:23` "The rank
  is enough"; `agents/tasks/LJ-1-417/Probe417.agda:80` `swo-into-ord`.
- `agents/tasks/LJ-1-418/lj-1.418-report.md:19` GO;
  `agents/tasks/LJ-1-418/Probe418.agda:64-66` `stage-into-bound`.
- `agents/tasks/LJ-1-419/lj-1.419-report.md:15` NO-GO.
- `agents/tasks/LJ-1-414/Probe414.agda:134-138` `amb-to-coded`, whose
  telescope carries an arbitrary `_↪_`.
- `src/L/Cardinal.lagda.md:117`, a use of `leastOf`.
- `src/L/Axioms/Full.lagda.md:144` `hasSeparationL : (a : S)
  (φ : Formula S 1)`; `src/L/InjChain.lagda.md:471-472`, the Carve
  separation field over a named bound.
- `dev/LESSONS.md:3752`, C-42.

One citation fails as written, in the LITERATURE USED block of the
report: `dev/literature/truncation-and-selection.md:67` is a blank
line. The quoted sentence, "The selection device is a definable
well-order plus a universal guard.", sits at `:68`. Off by one. The
quote exists, the file is the right file, and the remark it supports is
a contrast, not a pillar of the STOP. Two further lines are loose but
resolve: `src/L/Cardinal.lagda.md:117` is a use site of `leastOf`, and
`src/L/Choice/Internal.lagda.md:514` starts `graphAt-value`, whose
body reads `satGraphAt` at `:517`.

The arithmetic on its own numbers is correct: of 2.89, 2.12, 1.79 s the
median is 2.12 s, and the peak of 381976576, 368934912, 424902656
bytes is 424902656 bytes, as the report states.

## QUESTION 3. IS THE ENUMERATION COMPLETE

Materially yes. Formally it has two gaps. I closed both, and the
completed enumeration agrees with the return.

Gap one, inside Internal. The 9-tuple omits `∃₆`
(`src/L/Choice/Internal.lagda.md:920`), which is exported and
Formula-valued. It is a six-quantifier prefix, `∃₆ φ = ∃̇ (∃̇ (∃̇ (∃̇ (∃̇
(∃̇ φ)))))`, and describes nothing. The `Body` at `:751` is private to
a module block and is not exported. Loaded into the inventory, neither
changes the count of rank formulas from zero.

Gap two, tree-wide. The C-42 sweep in the report searched names:
`rank`, `swo-rank`, `rank-formula`. Those greps are true, but a rank
formula under another name would have escaped them. I enumerated every
Formula-valued definition outside Internal: `src/FOL/Bernstein.lagda.md`
holds `sglAt` `:79`, `pairAt` `:82`, `prAt` `:87`, `prMemAt` `:96`,
`appAt` `:99`, `svAt` `:110`, `inDomAt` `:116`, `domAt` `:119`,
`injAt` `:123`, `inRanAt` `:129`, `ranAt` `:132`, `rbdAt` `:138`,
`closedAt : Formula S 2` `:360`, `tarskiFo : Formula S 1` `:385`;
`src/L/Ordinal/Stages.lagda.md:294` holds `φ-ord : Formula K 1`, the
transitivity clauses of ordinality; `src/L/Axioms/Full.lagda.md:108`
holds `swapFo`; `src/FOL/Manipulation/Bounding.lagda.md:162` holds
`liftFo`. That is the coded-map vocabulary: pairing, application,
single-valuedness, domain, range, injectivity, finiteness. Count of
those that describe the rank of a well-order: 0. The completed sweep
agrees with the return's count, and with `archive` side checked at
`dev/ARCHIVE.md:283`, where the retired well-order module is a
shortlex order and not a formula.

The strongest attack line fails too. The brief's W3 shape,
`Formula S 2` read at `(z ∷ a ∷ [])`, has no slot for `w`, and the
obligation's `w : SWO ⟪ fst a ⟫` is a parameter. So even a delivered
`Formula S 2` could not name the order it ranks under. The return did
not fall into this: its D-10 corrected target already widens to "a
formula with slots for the order as a set", and the tree's formula
language supports the widening, since `con : K → Term K n` exists
(`src/FOL/Syntax.lagda.md:43`) and `prMemAt (con G)` is in use at
`src/FOL/Bernstein.lagda.md:362`. No cure was missed. Every consumer
in the tree eats a Formula: separation at
`src/L/Axioms/Full.lagda.md:144`, the Carve at
`src/L/InjChain.lagda.md:471`, and replacement at
`src/L/Axioms/Full.lagda.md:277`, `hasReplacementL : (a : S)
(φ : Formula S 2)`. Replacement is an alternative consumer the report
does not name, but it consumes the same missing formula, so it opens no
route the STOP closed. The next action the return names, write the
formula first, is correct, and the Bernstein vocabulary is the material
the next brief should be told about.

## DID THE BRIEF CAUSE THE OUTCOME

It designed the fork, and the return took the arm the brief built for
it: "IF IT DELIVERS ONLY THE ORDER AND NOT THE RANK, SAY SO AND STOP"
(`agents/tasks/LJ-1-454/LJ-1.454.md`, section W3). The condition is
met and measured. The brief also said a NO-GO is worth as much as a
GO, and the return delivered the finding the brief priced: the gap
between a described ORDER and a described RECURSION.

## THE MEASUREMENT, RE-RUN HERE

One process, caliber `-A64m -I0 -M8g` as the pane set it, from the
repository root. Cached run: exit 0. Forced recheck after deleting
`_build/2.8.0/agda/agents/tasks/LJ-1-454/Probe454.agdai`: "Checking
LJ-1-454.Probe454", 1.52 s real, exit 0. Consistent with the return's
2.89, 2.12, 1.79 s. No heap event. The measurement is sound. The
interface path is declared by `dev/build-manifest.toml:118`, glob
`2.8.0/**`.

## THE TRANSITIONS RECORD

My brief told me to read the six facts, `model`, `effort` and
`heads_sha256` of that instance in `dev/pod/transitions/`. No row for
LJ-1.454 exists there: `dev/pod/transitions/2026-08.jsonl` stops at
seq 158, task LJ-1.399, 2026-08-19. I recovered the six facts from
`runs/accept-1.out` (exit code 0, heap wall false, lines 0,
obligations delta 0, obligations open 1, seconds 1.59) and the head
hash from `agents/tasks/LJ-1-454/.pod` (heads 2f6630d2...). This is a
defect of the dispatch input, not of the return under attack, and it
changes nothing above.

## ARCHIVE USED

- `archive/dev/JOURNAL.md:3`
  "The per-episode journal is retired. Every agent task already keeps its"
  Read to check the return's decline. Not used further. The journal is
  retired and bears nothing on the enumeration.
- `archive/dev/ORCHESTRATION.md`
  not read, declined. Orchestration history does not bear on whether
  the tree delivers a rank formula.
- `archive/dev/DD-archived.md:1`
  "# THE `DD` RULING SERIES, archived in full 2026-08-18"
  Read line 1 only, to check the return's decline. Not used further.
- `archive/dev/PLAN-archived.md`
  not read, declined. The retired plan does not bear on this review's
  three questions.
- `dev/ARCHIVE.md:283`
  "A classical well-order over finite labelled trees by shortlex"
  Read. Used in Question 3: the retired `L.WellOrder.Tree` is an
  order, not a `Formula`, so no retired module closes the rank gap
  either.

## LITERATURE USED

- `dev/literature/devlin-II5.md:259`
  "Requirement: a definable well-order of L_α, used to pick the <_L-least"
  Read. Used. The literature's definable well-order exists to SELECT a
  least witness. The rank is not a selection, so the literature names
  no rank formula, as the return claims.
- `dev/literature/BIBLIOGRAPHY.md`
  not read, declined. A bibliography index bears nothing on the three
  questions.
- `dev/literature/digest.md:235`
  "The canonical well-order (SZ p. 11): <^A_β is defined recursively; at"
  Read. Used. The canonical ORDER is defined recursively; a formula for
  the RANK of that order is a different object, and the digest does not
  give one.
- `dev/literature/geology.md`
  not read, declined. It bears nothing on whether Internal or any
  chapter delivers `rank-formula`.
- `dev/literature/devlin-errata.md`
  not read, declined. Errata to Devlin do not bear on the enumeration.

## VERDICT

Upheld. The STOP is correct on its own numbers, the measurement is
sound and re-checked here, the enumeration is materially complete and
my completed sweep agrees with its count of zero. The defects found,
one false sentence about the name in the obstruction file, one
off-by-one literature line, one sweep narrower than the shape it
names, do not move the verdict. The obligation stays open at the
formula: `rank-formula` is the next target, with the Bernstein
vocabulary and `con` constants as its material.

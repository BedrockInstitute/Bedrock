# LJ-1.623 report: SiteFiber, the last supply class-pred wants

Head slot: coder. Machine: shared. Caliber on this pane: GHCRTS
`[-A64m -I0 -M2g]`, set by the program. I did not set it at any point.
One Agda process at a time. Every run ran under a wall-clock cap I set
and report below. This report was a skeleton before any probe run
beyond W3 and was filled as each answer landed (C-22).

## VERDICT

**NO-GO, stated.** The obligation
`agents/tasks/LJ-1-623/Probe623.agda::site-fiber` is NOT in the probe,
by the `[LJ-1.605]` NO-GO idiom: no term of the file carries the
obligation's name and no term has its type as its body. The residue
`[LJ-1.618]` left is the wall, UNCHANGED at the site grain, and the
probe measures that with green rows, not with claims:

- One refl row proves the obligation's type IS `[LJ-1.618]`'s payload:
  `site-is-pairing : P621.SiteFiber α ≡ P618.PairingAt α`
  (`agents/tasks/LJ-1-623/Probe623.agda:95-96`). The site grain and
  the one-alpha grain are ONE type, so the NO-GO `[LJ-1.618]` measured
  at that payload applies verbatim.
- The residue ALONE discharges the site: `residue→site`
  (`agents/tasks/LJ-1-623/Probe623.agda:115-116`) is `[LJ-1.618]`'s
  green recursion (`pairing-from-extract`,
  `agents/tasks/LJ-1-618/Probe618.agda:210-211`) applied at this site.
- The coded route, which `[LJ-1.618]` did not survey, parks at or
  above the ambient-least cardinal (`coded-sits-above`,
  `agents/tasks/LJ-1-623/Probe623.agda:169-172`), and the bridge it
  would need (`AmbientToCoded`, `:157-159`, TYPE ONLY) is not in the
  tree and is false in the classical semantics at cardinality-divergent
  pairs.

The probe is GREEN: `runs/final-2.out` at 1.75 s, `runs/final-3.out`
at 1.55 s, `runs/final-5.out` at 1.65 s (the run that postdates the
last edit, a comment-only citation fix), all warm, and
`runs/final-4.out` COLD at 3.08 s with the task interfaces of
`[LJ-1-594]`'s W3, `[LJ-1-617]`, `[LJ-1-618]` and `[LJ-1-621]` removed
first. All exit 0. The full statement of the stop is
`agents/tasks/LJ-1-623/review-of-site-fiber.md`. Nothing was
postulated. Nothing landed in `src/`. No commit, no push. `git status`
shows only `agents/tasks/LJ-1-623/` as new.

## D-10, BEFORE ANY AGDA

The residue was read and priced BEFORE any proof was attempted, as the
brief ordered. `Inj-extract`
(`agents/tasks/LJ-1-618/Probe618.agda:151-154`) leaves open exactly one
thing: the DATA payload of the least-cardinal search. The search
(`least = leastOf w lem InjP' nonempty`,
`src/L/Cardinal.lagda.md:116-117`) runs over the truncated predicate
`InjP γ = ∥ Inj γ ∥₁` (`src/L/Cardinal.lagda.md:66-67`), so the least
INDEX is honest and the payload is truncated (`κ-inj`,
`src/L/Cardinal.lagda.md:133-134`, sealed as `κ-injL` at
`src/L/SquareLawClosed.lagda.md:82-84`). The residue asks to read one
honest ambient injection out of that truncation, at the ambient-least
ordinal.

**IS IT WHAT `[LJ-1.618]` ALREADY FAILED AT, UNCHANGED?** The type is
unchanged: no task since `[LJ-1.618]` touched `L.Cardinal` or
`L.SquareLawClosed`; the last commit over either path is `[LJ-1.445]`'s
(`ee7ef373`), which predates `[LJ-1.618]`. What IS new
since `[LJ-1.618]` is the demand-side measurement (`[LJ-1.617]`) and
the packaging (`[LJ-1.621]`), and the brief permitted a second attempt
on that basis. So this task attacked the residue through the one route
the tree holds that `[LJ-1.618]` did not survey: the coded-injection
readback. The attack is measured in Section 3 of the probe and the
answer is below, in `## THE RESIDUE, CLEARED OR NOT`.

**THE TARGET'S TRUTH, PRICED.** In the classical semantics the target
is true at every site: for an infinite ordinal the square law holds,
and the untruncation of an inhabited existential is free in classical
set theory. No Tarskian or cardinality obstruction reaches the TARGET.
The obstruction is proof-theoretic: in this ambient type theory the
truncation `∥ X ∥₁` with X a non-proposition is not eliminated by LEM
(`dne` applies to hProps only,
`src/L/StageCardinal.lagda.md:416`), and the payload IS a
non-proposition (a Sigma whose first component is a function). The
residue is a choice principle at the single-pair grain, the same grade
`[LJ-1.605]` identified at the band. The bridge the coded route would
need is one grade worse: it is FALSE in the classical semantics at
pairs where the ambient and the constructible cardinality disagree
(the graph of a generic injection is not constructible), so no proof
of it exists without an axiom the ambient theory does not carry.

## W3, THE WIDEST UNMEASURED TERM

`agents/tasks/LJ-1-623/runs/W3.agda`, written FIRST and typechecked
ALONE. It holds `[LJ-1.618]`'s `Inj-extract` re-ascribed at
`SiteFiber`'s frame (`:58-61`): the site telescope of
`[LJ-1.621]` (`agents/tasks/LJ-1-621/Probe621.agda:40-42`), word for
word, TYPE ONLY, no term of that file proves anything. The site
parameters do not occur in the type; the frame is carried so the probe
can tie the two spellings by one refl
(`agents/tasks/LJ-1-623/Probe623.agda:104-105`) and they cannot drift.
Measured, not guessed: GREEN first run, exit 0, 5.86 s, peak RSS
671,023,104 bytes (640 MiB), under the cap this task set at TWO
MINUTES per the brief (`runs/w3-1.out`). That run elaborated
`L.Absorption` and `L.SquareLawClosed` cold, which were not in this
worktree's interface set; the warm re-check after the citation fix is
1.57 s (`runs/w3-2.out`). The cap was never approached. The brief
estimated about 12 lines; the file is 61 lines, of which the type is
4 and the rest is imports and the citation record. The estimate
priced the type and did not price the record.

## THE FLOOR

Measured BEFORE the final form, per the owner's ruling of 2026-08-23:
`runs/Floor.agda` is the probe with the one load-bearing new row
(`coded-sits-above`) holed and everything else present.
`runs/floor-1.out`: exit 42 with EXACTLY ONE unsolved interaction meta
at `runs/Floor.agda:172.32-37` and no other diagnostic, 3.19 s, peak
RSS 637,108,224 bytes, under the 300 s cap this task set for every
probe run. That run elaborated the whole imported closure cold:
`[LJ-1-594]`'s W3, `[LJ-1-618]`, `[LJ-1-621]`, `[LJ-1-617]` and
`[LJ-1-621]`'s W3. Against the cold delivered run (`runs/final-4.out`,
3.08 s over the same closure), the landing row's own body costs about
0.1 s: the frame is the whole price of this task, exactly as
`[LJ-1.621]` measured for its own shape. No run approached a cap. No
run hit the heap cap, so the heap-wall clause never fired and no
restructure was needed.

## THE RUN LEDGER

| run | what | exit | price |
|---|---|---|---|
| `runs/w3-1.out` | W3 alone, cap 120 s, cold | 0 | 5.86 s, 671,023,104 B peak RSS |
| `runs/floor-1.out` | probe, landing row holed, cap 300 s, closure cold | 42 | 3.19 s, 637,108,224 B; one meta at `Floor.agda:172`, no other diagnostic |
| `runs/final-1.out` | first delivery attempt | 42 | 1.63 s; my shape error at `:189` (the delta-pair built from `γ` instead of `fst γ`), fixed at once |
| `runs/final-2.out` | delivered, warm | 0 | 1.75 s, 444,678,144 B |
| `runs/final-3.out` | delivered, warm | 0 | 1.55 s, 425,967,616 B |
| `runs/final-4.out` | delivered, COLD: the task interfaces of 594-W3, 617, 618, 621 removed first | 0 | 3.08 s, 612,515,840 B |
| `runs/w3-2.out` | W3, after the comment-only citation fix | 0 | 1.57 s, 404,078,592 B |
| `runs/final-5.out` | delivered, postdates the last edit (comment-only citation fixes; no code changed) | 0 | 1.65 s, 444,678,144 B |

Sizes: the probe is 240 lines, of which 79 are non-blank and do not
start with a comment dash (awk count). The brief estimated about 170
lines with about 45 for the obligation; the estimate priced a probe
that ATTEMPTS the fiber, and this probe instead measures the wall,
which costs less mathematics and more record. Comparables are of SHAPE
only. `runs/Floor.agda` is kept in the tree with its hole, as
`[LJ-1.613]` kept its floor files.

## THE RESIDUE, CLEARED OR NOT

**NOT CLEARED.** The residue is
`Inj-extract` at `agents/tasks/LJ-1-618/Probe618.agda:151-154`, and it
is `[LJ-1.618]`'s wall, unchanged. What this task added is the
measurement of the one route that could have cleared it since:

1. **The readback exists and is honest.** `readL`
   (`src/L/CantorBernstein.lagda.md:33-36`) turns an L-coded
   injection held as DATA into an ambient injection, untruncated
   everywhere (`coded→ambient`, `agents/tasks/LJ-1-623/Probe623.agda:
   127-129`). Re-ascribed green at this frame.
2. **Codes as data at the ambient-least clear the residue outright.**
   `codes-at-κL→residue` (`:140-143`) consumes them and the truncated
   hypothesis is discarded: codes as data are strictly stronger. So
   the residue's clearing needs exactly one thing, code DATA at
   `κL a oa`.
3. **The tree's own code-selection does not reach there.** The
   least-code selection (`chosen = leastOf (orderAt β oβ) lem Good h`,
   `src/L/Cardinal.lagda.md:194-195`) untruncates CODE existence
   because the predicate is hProp-valued, but its hypothesis is again
   a truncated CODED existence. The bridge from the truncated AMBIENT
   statement to the truncated CODED statement is
   `AmbientToCoded` (`agents/tasks/LJ-1-623/Probe623.agda:157-159`),
   TYPE ONLY, inhabited by no row of this file or of the tree.
4. **And the bridge is not merely missing, it is false in the
   classical semantics at divergent pairs.** A code for an injection
   `a ↪ b` is an L-set whose graph is constructible. An ambient
   injection can have a non-constructible graph: at a pair where the
   ambient cardinality is strictly below the constructible one (a
   collapse extension at `a = ℵ₁^L`, `b = ω`), the ambient injection
   exists and no code does. So the coded route cannot be completed
   into the residue without an axiom, and the landing row
   (`coded-sits-above`, `:169-172`) measures where it parks instead:
   every coded target sits at or above the ambient-least cardinal,
   because a code at gamma carries an ambient injection at gamma
   (`readL`) and the ambient search (`src/L/Cardinal.lagda.md:116-117`)
   then cannot stop above gamma.

Nothing cleared the residue. The stop follows the brief's own rule: a
NO-GO that shows the residue is `[LJ-1.618]`'s wall unchanged.

## IS class-pred COMPLETE

**NO. FOUR OF FIVE, AND THE FIFTH IS THE ONE THIS TASK COULD NOT
INHABIT.** The five ingredients are
`agents/tasks/LJ-1-594/review-of-pairing-suffices.md:40-44`:

| | ingredient | state | basis |
|---|---|---|---|
| (i) | `D`, the definable power set | PAID by `[LJ-1.613]`, a green term at the carrier | `agents/tasks/LJ-1-613/Probe613.agda:137-154` |
| (ii) | the least-element selection | PAID by `[LJ-1.613]` | `agents/tasks/LJ-1-613/Probe613.agda:180-192` |
| (iii) | the pairing at the site | **NOT PAID. THIS TASK'S NO-GO** | `agents/tasks/LJ-1-623/review-of-site-fiber.md` |
| (iv) | `ih m`, the injection at the stage below | PAID by `[LJ-1.601]` (base) and `[LJ-1.608]` (limit), read off their GO reports, not re-proved here | `agents/tasks/LJ-1-601/lj-1.601-report.md`, `agents/tasks/LJ-1-608/lj-1.608-report.md` |
| (v) | the coded syntax the existential ranges over | PAID by `[LJ-1.600]`, read off its GO report | `agents/tasks/LJ-1-600/lj-1.600-report.md` |

`[LJ-1.621]`'s sentence "with (i), (ii), (iv) and (v) already paid the
`class-pred` formula's supplies are complete"
(`agents/tasks/LJ-1-621/lj-1.621-report.md:329-330`) was conditional on
this task delivering (iii), and the condition failed. I do not read a
discharge into anything I did not inhabit: this task inhabits no term
of type `SiteFiber α`, and the four PAID rows above are read off their
predecessors' GO reports, not re-proved. Beyond the ingredients, the
tying `Formula` with its `defines` and `only` is still unwritten
(`agents/tasks/LJ-1-594/review-of-pairing-suffices.md:104-105`), so even
at five of five the formula chapter would remain.

## ITS HOME

**Nothing lands, so the question is answered for the term that would
have landed, and the answer is that `[LJ-1.621]`'s placement survives
this contact unchanged.** The named home was `src/L/StageCardinal.lagda.md`,
beside `Upper`, on `[LJ-1.621]`'s finding: `Bound` and `OrdSWO` sit in
that telescope, the variant reuses both, no new import edge, one edge
removed (`L.Choice.Finite`). This task adds nothing that moves that
finding: the probe imports `[LJ-1.621]`'s term and applies it, and the
wall it measured is in `L.Cardinal` and `L.SquareLawClosed`, not in
the placement. If a later task funds the fiber or the residue, the
residue's own home would be `src/L/Cardinal.lagda.md` beside
`LeastCardInjL` (it is stated at `κL`), with one consumer edge into
`L.StageCardinal` through the site fiber, and the fiber's home stays
`[LJ-1.621]`'s. The blocker is mathematical, not architectural: no
term exists to place.

## THE LITERATURE STEP

Read, in full, `dev/literature/truncation-and-selection.md` section 2.4
(`:150-165`) and section 2.3's constraint line (`:146`). The brief's
question: if clearing `Inj-extract` lifts any truncation, at which
grain does the type have a weakly constant endomap? The answer, in
Kraus, Escardó, Coquand and Altenkirch's terms (Theorem 16,
`:158`; Theorem 17's weaker hypothesis, `:161-162`):

- **The grain the endomap would have to live at:** the SINGLE PAIR
  `X_a = ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫`, one fixed `a` with its own
  ambient-least cardinal. Never the Pi over `a`: an endomap of the Pi
  would have to normalize coherently across all pairs at once, which
  is stronger than the residue and is the band object `[LJ-1.605]`
  measured as the square law itself.
- **The grain where the tree HAS one:** one step over, at the CODE
  type `Σ[ F ∈ S ] InjCode F a b`. The least-code selection
  (`src/L/Cardinal.lagda.md:194-195`) normalizes every code to the
  least one and `readL` reads that one back. That IS the least-element
  route the dossier's closing line names (`:164-165`: "normalize any
  witness to the least one"), and it is legitimate because the
  predicate is hProp-valued (`:146`).
- **What is missing between the two grains:** a bridge from an ambient
  witness to the code grain where the normalization lives. That is
  `AmbientToCoded` (`agents/tasks/LJ-1-623/Probe623.agda:157-159`),
  and this task measured it false in the classical semantics at
  divergent pairs. So the Kraus criterion does not merely fail to be
  invoked here; it localizes the wall: the endomap exists at the code
  grain, the ambient grain has none in the tree, and the implication
  that would carry one to the other is not provable.

The criterion was applied, not re-derived.

## W2 AND W4

**W2.** The mathematics was written ONCE, by `[LJ-1.618]` at the
generic carrier `{ℓ}` with `lem` as the only hypothesis, and by
`[LJ-1.617]` and `[LJ-1.621]` at the generic site telescope. This task
adds ZERO new mathematics: it imports `[LJ-1.618]`'s recursion and
`[LJ-1.621]`'s packaging and instantiates both at the site, and its
one new row (`coded-sits-above`) is stated at the generic pair
`(a, γ)`. Both trophy proofs consume the measurements unchanged. No
deadline forced a fixed form, so no conflict arose.

**W4.** No module was retired by this return; `dev/ARCHIVE.md` is
untouched and nothing moved to `archive/`. The ideal form of this
measurement written fresh today is the probe as it stands: I did not
pay for a worse shape first and then compare.

## PREMISES CHECKED

- Premise 1 HOLDS: `agents/tasks/LJ-1-621/Probe621.agda:121` names
  `SiteFiber α` in the obligation's own statement, and the report's
  verdict is DELIVERED GO at `agents/tasks/LJ-1-621/lj-1.621-report.md:
  11`.
- Premise 2 HOLDS: `agents/tasks/LJ-1-621/runs/W3.agda:47-48` states
  `Q` in full.
- Premise 3 HOLDS WITH AN OFFSET: "What the shape resisted: nothing"
  is at `agents/tasks/LJ-1-621/lj-1.621-report.md:331`, item 2 of the
  section that starts at `:320`.
- Premise 4 HOLDS: `agents/tasks/LJ-1-617/lj-1.617-report.md:1` is the
  report's head; the grain measurement is its section
  `## WHICH GRAIN THE BILL PAYS IN` (`:85-104`, the binding sentence
  at `:96`).
- Premise 5 HOLDS: the NO-GO verdict is at
  `agents/tasks/LJ-1-618/lj-1.618-report.md:11-12`, and the residue is
  at `agents/tasks/LJ-1-618/Probe618.agda:151-154`.
- Premise 6 HOLDS: `P` at `src/L/StageCardinal.lagda.md:530`.
- Premise 7 HOLDS: the band spend at `src/L/StageCardinal.lagda.md:283`.
- Premise 8 HOLDS: the Pi-bound at `src/L/BoundedSubset.lagda.md:1388`.
- Premise 9 HOLDS: `agents/tasks/LJ-1-613/Probe613.agda:137` is
  `D-carrier`'s statement line, ingredient (i)'s delivered term.
- Premise 10 HOLDS WITH AN OFFSET: section 2.4's head is at
  `dev/literature/truncation-and-selection.md:150` and Theorem 16 at
  `:158`.
- **Premise 11 HAS THE KNOWN DEFECT, re-measured here.** There is no
  R-42 in `dev/LESSONS.md` (grep count 0). `dev/LESSONS.md:4404` is a
  Related line, and the respelling rule is R-41 at `:4762`. The
  premise's figures "1.74 s against 155.02 s" appear in neither
  `dev/LESSONS.md` nor `dev/ledger.toml` (grep, zero hits each). I
  worked under R-41's substance: `SiteFiber` is IMPORTED from
  `[LJ-1.621]`, and every type this task restates is tied to its
  source by a refl row (`:95-96`, `:104-105`).
- Premise 12 HOLDS: `AGENTS.md:45` is the measured-cure bullet's head.
- Premise 13 HOLDS WITH AN OFFSET: the make-check bullet head is at
  `AGENTS.md:75`; `:74` is the tail of the one-off-instruction bullet.

## ARCHIVE USED

Candidates named in the brief's ARCHIVE block, each answered:

- **`archive/dev/LJ-dispatch-index.md` READ AND USED.** `:183`:
  "`| LJ-1.107 | sq at every infinite ordinal | PARTIAL: initial
  ordinals only | The non-initial case needs an injection the
  truncated least-of witness cannot give: the inject type is not a
  prop |`" and `:190`: "`| LJ-1.114 | Thread the truncation from
  StageCardinal to Devlin55 | WALL, ROUTE-LEVEL | Upper's h-inj needs
  ONE honest injection; two truncation eliminations collide.
  Reverted; the cause is proved |`". Both rows are the direct
  predecessors of this task's measurement: the payload this task could
  not untruncate is the one `[LJ-1.107]` named and `[LJ-1.114]` walled
  on. The index is frozen and carries no row for `[LJ-1.617]` or
  later.
- **`archive/dev/JOURNAL-archived.md` DECLINED.**
  `archive/dev/JOURNAL-archived.md:1`: "`# Archived journal: the
  retired route`". The retired route's journal does not measure the
  site grain, the residue, or the coded readback this task used; the
  live probes and reports cited above carry all of it.
- **`archive/dev/JOURNAL.md` DECLINED.**
  `archive/dev/JOURNAL.md:1`: "`# ARCHIVED 2026-08-20`". A retired
  journal; the measurements this task used are the live probes and
  reports cited above.
- **`archive/dev/ORCHESTRATION.md` DECLINED.**
  `archive/dev/ORCHESTRATION.md:1`: "`# ORCHESTRATION: the
  orchestrator's operating rules`". The rules that bind this task were
  in the standing instructions and the Boundary; no operating rule was
  needed from the retired orchestrator.
- **`archive/dev/DECISIONS-archived.md` DECLINED.**
  `archive/dev/DECISIONS-archived.md:1`: "`# Archived decisions: the
  D series`". Same reason as ORCHESTRATION.md.

## LITERATURE USED

Candidates named in the brief's LITERATURE block, each answered:

- **`dev/literature/truncation-and-selection.md` READ AND USED.**
  `:158`: "`- **Theorem 16: \"A type X has a constant endomap if and
  only if it has split`" and `:163`: "`**So the question \"can this
  truncation be lifted\" is always the question \"does`", with
  `:164-165` naming the least-element route and `:146` the hProp
  constraint. Used for the literature step above; the criterion is
  applied, not re-derived.
- **`dev/literature/devlin-II5.md` READ AND USED.** `:413`:
  "`|L_α| = |α| for α ≥ ω (`dev2.txt:117`, `dev2.txt:200-240`) is
  consumed at`". The classical level-size equation is what the
  `class-pred` formula serves, and ingredient (iii) is its counting
  half at the site: this task's stop says that ingredient stays
  unpaid, so the classical equation remains without its machine here.
- **`dev/literature/geology.md` DECLINED.**
  `dev/literature/geology.md:1`: "`# Geology dossier: set-theoretic
  geology sources and the five questions`". No layering question
  arose; the measurement is inside one chapter's parameter grain.
- **`dev/literature/digest.md` DECLINED.**
  `dev/literature/digest.md:1`: "`# Digest: the orthodox form of the
  rud route, pinned from the collected literature`". Its pairing row
  (`:241`, the surjection onto `J_α^A` under Gödel pairing) is the
  syntactic pairing of the J tower, a different object from the square
  law at an ordinal, and building a new square-law route is forbidden
  to this task.
- **`dev/literature/level-formula-slot-roles.md` DECLINED.**
  `dev/literature/level-formula-slot-roles.md:1`: "`# The level-hood
  formula: arity, what it binds, what stays free`". This task fixes no
  level slot and writes no formula chapter; the tying formula is named
  as unwritten and left to the mathematician.

## GATES

The cheap gate parts that can see this task's files:
`scripts/gate/lint-agda.py --check` exit 0; `scripts/gate/
check-probes.py --check` clean; `scripts/gate/lint-prose.py --check`
exit 0 on this report and on the review; grep for `postulate`,
`TERMINATING` and `{!` over the probe and its W3 returns nothing at
code level (`runs/Floor.agda` carries its deliberate hole as the floor
record, the `[LJ-1.613]` precedent); no em dash in any file of this
scope. `make check` not run: it is the commit gate, nothing here
commits, and no `src/` file changed (`git status`: only
`agents/tasks/LJ-1-623/` is new). The ratio bar cannot fire: no file
of this scope carries an agda fence, so the in-fence count is 0.

## WHAT THE NEXT BRIEF NEEDS

1. **The site grain is closed as a supply route, and the owner must be
   told.** `[LJ-1.617]`'s measurement (the bill pays in the site
   grain) stands as a demand-side fact, but the supply at that grain
   is the SAME TYPE `[LJ-1.618]` measured NO-GO
   (`agents/tasks/LJ-1-623/Probe623.agda:95-96` is the refl that
   proves it). The brief's own NO-GO branch applies: the site-grain
   measurement buys the campaign nothing, and the mathematician must
   say that to the owner.
2. **The funding question is now about the UNTRUNCATION, not the
   grain.** Site, one-alpha and band are one object at three
   uniforms; the missing ingredient at every grain is the same: an
   honest ambient injection out of the truncated least-cardinal
   search. The two ways to fund it this task measured: an owner-ruled
   axiom (`Inj-extract` itself, or `AmbientToCoded`), or code DATA at
   `κL` from some other route. Note the second is cheap to consume:
   `codes-at-κL→residue` (`:140-143`) turns code data at `κL` into the
   residue outright, and any future supply that produces code DATA at
   the least cardinal finishes ingredient (iii) for free.
3. **The circle is the live alternative, and it is the formula itself.**
   The definable well-order that classically supplies the canonical
   injection is what the `class-pred` formula is building, and (iii)
   is one of its own ingredients (`agents/tasks/LJ-1-594/
   review-of-pairing-suffices.md:42`). The campaign's choice is
   therefore exactly the one `[LJ-1.605]` put to the owner, now
   measured one grain down: fund the untruncation, derive it from
   `V = L`, or restructure the formula so (iii) enters differently.
   Nothing in this tree does it for free.
4. **What resisted:** one shape error in my own landing row (the
   delta-pair, `runs/final-1.out`), fixed at once; no wall, no heap
   event, no restructure. **What I weakened:** nothing; every row is
   stated at the strength the tree's own chapters give. **What I could
   not close:** the residue, and this report says at `file:line` why.

# Review of LJ-1.613#1

## HEAD
head_slot: mathematician_adversarial
machine: shared
verdict: upheld
attacked: agents/tasks/LJ-1-613/lj-1.613-report.md
brief: agents/tasks/LJ-1-613/LJ-1.613.md
stop: none. The predecessor wrote no `review-of-first-two-internal.md`.

## THE INVARIANT

The critic is not the author. The author ran as the `coder` slot. This
critic runs as `mathematician_adversarial`. This head did not write the
report, the probe, W3, the floor files, or any run artefact.

The predecessor's verdict is GO, not a NO-GO. I agree with that word.
`verdict: upheld` here means the GO stands. It does not mean a NO-GO
was found. Row `sys-critic-upheld-no-go` wants
`obligations_open_min = 1` (`dev/pod/table.toml:4321`). The accept arm
records `obligations_open: 0` (`runs/accept-1.out:25`). I do not flip
the word to make that row match.

`dev/pod/transitions/2026-08.jsonl` in this worktree carries no line
with `"task": "LJ-1.613"`. The file ends at seq 158, task `LJ-1.399`,
stamp 2026-08-19 (`dev/pod/transitions/2026-08.jsonl:157-158`). Model,
effort and `heads_sha256` are therefore not on the worktree record. The
six facts come from the accept arm. No load-bearing claim of the return
cites the transitions file.

## THE SIX FACTS OF THE INSTANCE

From `agents/tasks/LJ-1-613/runs/accept-1.out`:

- Probe613.agda rc 0, 1.63 s (`accept-1.out:16`)
- Floor.agda rc 42, 1.63 s (`:17`)
- conjunct 1 FAILED; conjuncts 2 to 6 held (`:10-15`)
- exit 42, error class `unsolved_meta` (`:23-24`)
- obligations delta -1, obligations open 0, probe not red
  (`:21`, `:25`, `obligations_probe_red: false`)
- heap wall false, in-fence lines 0, unbound_vacuous true (`:25`)
- 23 changed files, all under `agents/tasks/LJ-1-613/` (`:18`, `:25`)
- caliber `-A64m -I0 -M2g`, tier wide (`:5-6`)
- `agda slots during 2` (`:7`), `concurrency: 2` (`:25`)

`unbound_vacuous: true` here means conjunct 4 saw no `src/` master
change (`scripts/pod/accept.py:214-216`). It does not mean the
obligation name is missing. The name `first-two-internal` stands at
`Probe613.agda:283-290`.

## QUESTION 1: DOES THE VERDICT LINE MATCH THE BODY

**Yes. The word is GO, and the body inhabits the obligation.**

The line is `agents/tasks/LJ-1-613/lj-1.613-report.md:8-9`:

> **GO.** The obligation
> `agents/tasks/LJ-1-613/Probe613.agda::first-two-internal` IS in the

The same word stands at `:24-28`, in the probe header
(`Probe613.agda:6-10`), and at the binder (`Probe613.agda:283-290`).
The body carries each part of that line:

- The name `first-two-internal` is a term. The body is
  `D-carrier , inv-carrier , least-at-carrier`
  (`Probe613.agda:290`). Accept re-measured that file today: rc 0,
  1.63 s (`runs/accept-1.out:16`). The coder's own delivered runs are
  `runs/final-2.out` EXIT=0 at 28.35 s (`:5`, `:23`),
  `runs/final-3.out` EXIT=0 at 1.93 s (`:4`, `:22`),
  `runs/final-4.out` EXIT=0 at 1.71 s (`:4`, `:22`), and
  `runs/final-5.out` EXIT=0 at 22.25 s (`:5`, `:23`). Delta -1, open 0
  (`accept-1.out:21`, `:25`).
- Nothing is postulated. `--safe` is on (`Probe613.agda:1`). A search
  of `Probe613.agda` for `{!` returns none. No `src/` master changed.
- `review-of-first-two-internal.md` is absent. The report says so
  (`lj-1.613-report.md:21-22`). The brief listed that file for a stop
  (`LJ-1.613.md:45`). A GO writes no stop. Line and body agree.

**This is not the defect class the project measured on 2026-08-16.** A
line that said GO while the body left `first-two-internal` unbound, or
a line that said NO-GO while the meter closed it, would be that class.
Here the line states the inhabitant the body measures.

**The accept arm's exit 42 does not flip the word.** Conjunct 1 ran
`runs/Floor.agda` and stopped at the first failing target. Case 2 of
`verification_target` typechecks every changed `.agda` under the task
home, in path order (`scripts/pod/facts.py:440-468`). No `src/` master
changed, so the targets begin `Probe613.agda` then the files under
`runs/`. `Floor.agda:222`, `:247` and `:290` are `{! !}`
(`Floor.agda:222`, `:247`, `:290`). Exit 42 is unsolved interaction
metas (`runs/accept-1.out:24`, `error_names_all:
["UnsolvedInteractionMetas"]`). The body names that file, that exit,
and those holes (`lj-1.613-report.md:79-86`). The same arm records
Probe613.agda rc 0 and obligations delta -1. W3 was not re-run by
accept, because Floor failed first. The coder's own W3 run remains
`runs/w3-1.out` through `runs/w3-3.out`: EXIT=0, 1.29 s, 0.93 s, 0.90 s
(`w3-1.out:5`, `:23`; `w3-2.out:4`, `:22`; `w3-3.out:4`, `:22`).

The brief did not order a remaining hole in `runs/Floor.agda`. W3 is
the slice it named (`LJ-1.613.md:102-109`). The holes are the coder's
floor, not the obligation. It is the same accept-arm shape
`[LJ-1.606]` and `[LJ-1.610]` already measured: a designed hole in
`runs/` makes conjunct 1 red and does not unbind a green named term.
Here the named term is green.

The four-question lens, used to find this answer and not written as
the answer: the GO is correct on its own numbers (delta -1, Probe613
rc 0, both ingredients inhabited); the measurement is sound (W3 first
and alone, floor first, one planted error, the wall bisected); the
brief did not foreclose (it asked whether either ingredient failed);
no mathematical cure was missed. Filling `Floor.agda` after the
measurement would make row `go` match and would erase the floor the
owner ordered. That is a routing fact, not a second verdict.

## QUESTION 2: IS EVERY LOAD-BEARING CLAIM BACKED BY A FILE:LINE THAT RESOLVES TODAY

**Yes for every claim that carries the GO.** Several nearby citations
in comments sit one line off. None of those supplies the inhabitant,
and the report's own citations for the same facts resolve.

Claims that resolve today:

- Ingredient (i) is `D` plus inversion, INTERNAL in
  `[LJ-1.594]`'s table at
  `agents/tasks/LJ-1-594/review-of-pairing-suffices.md:40`. The quoted
  row names `D-at-the-site` at `Probe594.agda:227-234` and
  `src/L/StageCardinal.lagda.md:400-401`. `D-at-the-site` is at
  `Probe594.agda:227-234`. `limit-step` supplies
  `DefOf.defSet (Lset ·)` at `src/L/StageCardinal.lagda.md:400` and
  `𝒟ₒ-inv` at `:401`.
- `DefOf.defSet` is `src/L/Definability.lagda.md:111-112`. `𝒟ₒ-inv`
  is `src/L/Constructible.lagda.md:306-308`. `module DefOf (A : S)`
  is `src/L/Definability.lagda.md:78`.
- Ingredient (ii) is the least-element selection, INTERNAL in the
  same table at
  `agents/tasks/LJ-1-594/review-of-pairing-suffices.md:41`. The quoted
  row names `h-is-leastOf` at `Probe594.agda:305-317` and
  `src/L/StageCardinal.lagda.md:349-351`, `:258-264`. `h-is-leastOf`
  is at `Probe594.agda:305-317`. `h` is
  `src/L/StageCardinal.lagda.md:350-351`. `ordSWO` is `:258-264`.
- `leastOf` is `src/L/WellOrder/Base.lagda.md:158-161`. `IsLeast` is
  `:130-131`. The SWO module is `:127`. `OrdSWO` is
  `src/L/StageCardinal.lagda.md:228`. `_≺_` is `:230-231`.
- `LimitStep`'s `D` and `inv` parameters are
  `src/L/StageCardinal.lagda.md:278-280`. The site's `ih` argument
  is `:396-398`.
- Standalone (i) at this carrier: `D-carrier` at
  `Probe613.agda:137-138`, `inv-carrier` at `:152-154`, tied to W3
  by refl at `:143-144` and `:157-158`. W3 itself is
  `runs/W3.agda:58-59` and `:64-66`.
- Standalone (ii) at this carrier: `least-at-carrier` at
  `Probe613.agda:180-183`. The order equation is `:190-192`.
- The site row at the projection: `site-accepts-first-two` at
  `Probe613.agda:217-224`, `site-accepts-is-the-site` at `:239-247`.
  That is `[LJ-1.594]`'s `D-at-the-site` shape
  (`Probe594.agda:227-234`). `fst` at `_↪_` is
  `src/L/Cardinal.lagda.md:47-48`.
- The obligation: `Probe613.agda:283-290`.
- Ingredient (v) imported, not restated:
  `P600.key-at-stage` at `agents/tasks/LJ-1-600/Probe600.agda:129-130`,
  applied at `Probe613.agda:266-268`. The carrier projection
  `LsetS δ oδ .fst ≡ Lset δ` is
  `agents/tasks/LJ-1-600/runs/W3.agda:57`.
- The route line that put (i) and (ii) after (v):
  `agents/tasks/LJ-1-594/review-of-pairing-suffices.md:141-142`.
- W3 times, cap, and negative control: `runs/w3-1.out:5` 1.29 s
  EXIT=0, `runs/w3-2.out:4` 0.93 s, `runs/w3-3.out:4` 0.90 s, peak
  RSS 270909440, 265469952, 265502720 bytes (`w3-1.out:6`,
  `w3-2.out:5`, `w3-3.out:5`). Cap 120 s (`w3-1.out:1`). Planted
  arity error `runs/W3neg.agda:59`, EXIT=42 at 0.94 s
  (`w3-neg-1.out:5`, `:11`, `:29` in the full file; the error line
  is `w3-neg-1.out:5`).
- Floor before the proof: `runs/floor-1.out:13` 2.85 s, EXIT=42 at
  the holes (`:8-12`, `:31`), peak RSS 412467200 (`:14`).
  Re-measured from the delivered shape: `runs/floor-2.out:10` 1.73 s,
  EXIT=42 (`:28`).
- The wall and the bisection: `runs/final-1.out:5-7` killed at
  56.43 s, RSS 1238548480, EXIT=1. `runs/floor2-1.out:9` 2.45 s
  EXIT=42. `runs/floor3-1.out:5-7` killed at 23.69 s, RSS 977469440,
  EXIT=1. `runs/floor4-1.out:8` 2.82 s EXIT=42. The walling row is
  the full-pair equation in `runs/Floor3.agda:237-239`.
- Cold delivered memory: `runs/final-2.out:6` 1115439104 bytes
  (1.115 GB) and `runs/final-5.out:6` 1244413952 bytes (1.244 GB).
- `[LJ-1.600]` GO: `agents/tasks/LJ-1-600/lj-1.600-report.md:3`.
  `[LJ-1.601]` GO: `agents/tasks/LJ-1-601/lj-1.601-report.md:3`.
  `[LJ-1.608]` GO: `agents/tasks/LJ-1-608/lj-1.608-report.md:3`.
- Premise 6 names files that are not here: `agents/tasks/LJ-1-607/`
  does not exist. Premise 11 names R-42 at `dev/LESSONS.md:4404`.
  Line `:4404` is C-52's Related line. R-41 is
  `dev/LESSONS.md:4762`. The figures `1.74 s` and `155.02 s` occur
  in neither `dev/LESSONS.md` nor `dev/ledger.toml`.
- Premise 13's basis is `AGENTS.md:75`, not `:74`. Line `:74` is
  the one-off-instruction bullet. Line `:75` is `make check`.
- The recorded `pick-canonical` cure:
  `archive/dev/LJ-dispatch-index.md:212`.
- Devlin II.5.9: `dev/literature/devlin-II5.md:422`. The selection
  dossier: `dev/literature/truncation-and-selection.md:35`.

Claims whose named `file:line` does not resolve at that exact line,
and that do not carry the GO:

- `Probe613.agda:114` cites
  `agents/tasks/LJ-1-594/review-of-pairing-suffices.md:140-141` for
  the route sentence. The sentence
  `` `keyS` at `A := LsetS δ oδ`. Then (i) and (ii), ``
  starts at `:141`. The report cites `:141-142`
  (`lj-1.613-report.md:50-52`), which resolves.
- `Probe613.agda:253` and `runs/Floor3.agda:253` cite
  `agents/tasks/LJ-1-600/runs/W3.agda:62-64` for the carrier
  projection. Those lines do not exist. The equation is
  `agents/tasks/LJ-1-600/runs/W3.agda:57-58`. The report cites
  `:56-57` (`lj-1.613-report.md:154-155`). Line `:56` is a
  comment. Line `:57` is the type. The body `refl` is `:58`.
- `runs/W3.agda:26-27` cites
  `agents/tasks/LJ-1-600/runs/W3.agda:52-53` for the alphabet.
  Those lines are comments. The W3 obligation there is `:49-50`.

None of those three supplies `first-two-internal`. The GO does not
rest on them.

## QUESTION 3: IS THE PREDECESSOR'S ENUMERATION COMPLETE

**Yes for the obligation and for the five-ingredient count. Two
strengthenings are not measurements at this site, and they are not
needed for the GO.**

What the return enumerated, and what I checked:

1. **The obligation is inhabited.** Complete. The name is present.
   Accept records delta -1, open 0, Probe613 rc 0. No hole, no
   postulate, `--safe` on, nothing in `src/`.
2. **W3, ingredient (i) at this carrier, type only.** Complete as
   the brief wrote it (`LJ-1.613.md:102-109`). `D-at-carrier` and
   `inv-at-carrier` at `runs/W3.agda:58-66` are the two halves of
   (i), green under the two-minute cap. The delivered probe ties
   both by refl. The negative control fails at the planted arity
   and nowhere else (`W3neg.agda:59`).
3. **Both claims instantiated.** Complete at the terms the brief
   asked for. (i) is `DefOf.defSet` plus `𝒟ₒ-inv` in `LimitStep`'s
   own parameter shape. (ii) is `leastOf` over `OrdSWO.ordSWO`,
   with `IsLeast` in the result type. Each is a substitution of a
   green generic chapter (`lj-1.613-report.md:164-172`). W2 is
   answered: this task adds zero generic code.
4. **What the formula now wants.** Complete, and it does not read a
   discharge into a term this task did not inhabit
   (`lj-1.613-report.md:138-142`). (i) and (ii) paid here. (v)
   imported from `[LJ-1.600]`. (iv) read off `[LJ-1.601]` and
   `[LJ-1.608]`, not re-proved. (iii) unpaid on this tree, because
   `[LJ-1.607]` never landed. The tying `Formula` with `defines`
   and `only` is named as still wanting. That extra is honest. It
   is not a sixth ingredient. The brief's GO-earn sentence
   (`LJ-1.613.md:113-114`) said "wanting only (iii)". The return
   keeps (iii) as the one unpaid ingredient of the five.
5. **The wall.** Complete. The first final shape walls. The bisection
   isolates row 3.2 at the full `_↪_` pair (`Floor3.agda:237-239`).
   The cure is `[LJ-1.594]`'s projection. The walling file stays in
   the tree with its `.out`.
6. **Premise defects.** Complete for this task. Premise 6 and
   premise 11 are false as cited. Neither is load-bearing for (i)
   or (ii). The next brief must not cite `[LJ-1.607]` as a term
   until it is re-landed (`lj-1.613-report.md:183-185`).

What the return did not enumerate, and why that does not flip GO:

- **No `h-is-leastOf` analogue at the standalone terms.**
  `[LJ-1.594]` identified (ii) with the equation
  `Probe594.agda:305-317`: `LimitStep.h` is `leastOf` over
  `class-pred`. This return writes `least-at-carrier`, the generic
  device, and does not re-measure that equation at `D-carrier` and
  `inv-carrier`. The equation would be `refl` at the same site
  (`src/L/StageCardinal.lagda.md:350-351`). The brief asked for the
  ingredients instantiated, not for a second copy of 594's site
  reading. (ii) as a term is `leastOf`. It is inhabited.
- **Designed holes under `runs/` make conjunct 1 red.** The body
  names `Floor.agda`. It does not name that `Floor2.agda`,
  `Floor3.agda`, `Floor4.agda` and `W3neg.agda` would also fail
  conjunct 1 if Floor were not first in path order. That is the
  accept-arm shape `[LJ-1.606]` already measured. It does not unbind
  `first-two-internal`.

No cheaper inhabitant of (i) or (ii) at this carrier is in the
delivered tree. Both were already internal, and they are now terms.
The GO stands.

## ARCHIVE USED

- `archive/dev/JOURNAL.md:1`: **READ, declined as history.**
  Quote: `# ARCHIVED 2026-08-20`. The return's own numbers are
  in the task directory and the accept arm. A retired journal
  is not a source for those facts.
- `archive/dev/ORCHESTRATION.md:1`: **READ, declined.** Quote:
  `# ORCHESTRATION: the orchestrator's operating rules`. The
  live homes are `AGENTS.md` and the slot file. This review
  does not take a dispatch rule from an archived operating
  note.
- `archive/dev/DD-archived.md:35`: **READ, the four questions.**
  Quote:
  `is the refusal correct on its own numbers; is the measurement sound; did the BRIEF cause the outcome; and is there a cure the return missed.`
  Those four are the lens. The three questions above are the
  answers. TOOK only that list. No DD row is restated as a
  rule.
- `archive/dev/PLAN-archived.md:1`: **READ, declined.** Quote:
  `# ARCHIVED 2026-08-20`. The live screen is
  `dev/pod/screen.toml`. This review does not take a plan row
  from the archived construction registry.
- `dev/ARCHIVE.md:1`: **READ, declined.** Quote:
  `# ARCHIVE.md: the archive registry`. No module was retired
  and no row is owed. The critic writes no `dev/` file.

## LITERATURE USED

- `dev/literature/devlin-II5.md:422`: **READ, 5.9, to attack the
  claim that (ii) is a theorem and not a choice principle.**
  Quote:
  `5.9 (the least element of a non-empty Σ₀ predicate is Σ₁-definable from its`.
  TOOK the same reading the return took: the selection is
  definable from parameters. That is what "internal" must mean
  for ingredient (ii). The literature does not make (ii) an
  axiom with no condition this tree meets. W8 does not abort.
- `dev/literature/BIBLIOGRAPHY.md:1`: **not used.** Quote:
  `# Bibliography for the rud route`. A bibliographic list does
  not decide whether `first-two-internal` inhabits.
- `dev/literature/digest.md:1`: **not used.** Quote:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  The rud route is not the instantiation under attack.
- `dev/literature/geology.md:1`: **not used.** Quote:
  `# Geology dossier: set-theoretic geology sources and the five questions`.
  Geology has no bearing on `defSet` or `leastOf`.
- `dev/literature/devlin-errata.md:1`: **not used.** Quote:
  `# Devlin errata: documented error classes (do-not-repeat checklist)`.
  A search of this file for `5.9` and for `least element`
  returned no line, so the errata cannot attack the 5.9 reading
  at `dev/literature/devlin-II5.md:422`.

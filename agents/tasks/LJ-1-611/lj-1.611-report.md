# LJ-1.611 report: face G-, where an ambient witness pins the tower's level

## HEAD
head_slot: coder
machine: shared
verdict: NO-GO on `graph-ambient`; the face's honest supplier is the AMBIENT
determination of the level-graph matrix, the retired route built only its
REDUCTION to two undelivered factors, and no delivered reading in the live
tree reaches the ambient side of it. The stop is stated at
`agents/tasks/LJ-1-611/review-of-graph-ambient.md`.

Written as a skeleton before any Agda beyond W3 and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-611/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M2g"`, ONE Agda process at a time. I did not set
`GHCRTS`. Nothing is postulated, the probe carries `--safe`, the delivered
file is green and carries no hole, and nothing lands in `src/`. The probe is
a raw `.agda` file, so it carries no ` ```agda ` fence, counts 0 in-fence
lines, and the ratio bar cannot fire on it.

**NO HEAP WALL WAS MET ANYWHERE IN THIS TASK.** The highest peak of any run
is 672,088,064 bytes against the 2,147,483,648-byte cap (`runs/w3-1.out`),
and the longest run is 3.78 s against the caps I set (150 s for every W3
run, 300 s for every probe run). No run was killed and no run printed a
heap message.

## W3, THE WIDEST UNMEASURED TERM

**GO, AND THE TYPE IS THE CHEAP HALF.** The slice is
`agents/tasks/LJ-1-611/runs/W3.agda` (68 lines, 34 code lines), written
FIRST and typechecked ALONE: `runs/w3-2.out` is **exit 0 at 2.74 s, peak
672,088,064 bytes**, under the 150-second cap I set. `runs/w3-1.out` is the same
slice one comment-typo fix earlier, exit 0 at 3.21 s and the same peak; the
delivered file carries its own green run. The type is
`agents/tasks/LJ-1-611/runs/W3.agda:65-67`, letter for letter
`[LJ-1.606]`'s `GraphAmbient`
(`agents/tasks/LJ-1-606/Probe606.agda:168-172`). The brief estimated about
12 lines; the type is 3 and the slice that holds it is 34 code lines, most
of it the frame. **The measurement moves the weight where it belongs:** the
STATEMENT costs 2.74 s and 0.63 GiB, and the weight is in the TERM, because
the term must decode an arbitrary ambient witness.

## D-10, BEFORE ANY AGDA: `crossOut`, AND WHAT "MADE CONCRETE" ADDS

**WHAT `crossOut` PROVES: NOTHING, AND THAT IS THE POINT.**
`agents/tasks/LJ-1-160/ProbeLJ1160A.agda:71-72` states

    (crossOut : (v b : S) → ⟨ v ∈ˢ P ⟩ → ⟨ b ∈ˢ P ⟩ → IsOrd b
              → Bel v b → v ≡ Lset b)

as a HYPOTHESIS of the module `Reroute`, with `Bel` abstract. That probe
never proved it and never chose `Bel`; it derived `levelIn` and `cover` from
it plus two more hypotheses (`ProbeLJ1160A.agda:83-101`). The hypothesis
came from the archived rud route, where `CrossOut` was the crossing
obligation itself, stated at the INNER reading `Believes φ v b`
(`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:163-164`), and
was never built there either.

**WHAT "MADE CONCRETE" MUST ADD, AND THE INSTANTIATION ANSWER.** Three
things: a MATRIX `ψ` (the abstract `Bel` never chose one); the READING
(the ambient `⊨ᵛ` of the relabelled matrix at the collapse constants, where
the lineage had the inner reading at `M` or at `P`); and the STRENGTH
(face G- drops both containment hypotheses, so the values are arbitrary
ambient sets). The re-ascribed type instantiates directly, and W3 measured
that. **The TERM does not instantiate, and the reason is measured below:**
every predecessor reads the belief at an inner world, and no delivered
reading moves an ambient witness into one.

**THE TARGET IS TRUE AT THE HONEST MATRIX, SO THE REFUTATION ROUTE IS
CLOSED.** Devlin 5.2 (a) is `∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]` with `Φ` a
Σ₀ formula by 2.7 (`dev/literature/devlin-II5.md:95-97`): classically the
ambient witness of the Σ₀ matrix pins the level, so no Tarskian
obstruction exists at the adequate matrix. The corpus adds the slot law the
next supplier needs: the level formula leaves exactly the VALUE and the
ORDINAL free and binds ONE determined bound for every unbounded quantifier
(`dev/literature/level-formula-slot-roles.md:40-63`), and no formalization
in the searched corpus ever writes an object-level level-hood formula with
numbered slots (`dev/literature/level-formula-slot-roles.md:97-98`).

**THE PREMISE CHECK PASSED ON ALL THIRTEEN.** The GO and the three faces
are at `agents/tasks/LJ-1-606/lj-1.606-report.md:119` and
`Probe606.agda:168-172`; `⊤-fails-G-` at `:262` and the junk fence at
`:260-285` are the terms my port consumed; `crossOut` at
`ProbeLJ1160A.agda:71` is as quoted above; `[LJ-1.602]`'s shared root is at
`agents/tasks/LJ-1-602/lj-1.602-report.md:16`; `[LJ-1.533]`'s refutation at
`agents/tasks/LJ-1-533/lj-1.533-report.md:16`; `[LJ-1.568]`'s `weakest` at
`agents/tasks/LJ-1-568/Probe568.agda:377-381`; `defSet` reads under the
inner satisfaction (`src/L/Definability.lagda.md:146-148`);
`𝒟ₒ-intro` is the one route in (`src/L/Constructible.lagda.md:300-303`);
the three Boundary clauses are `AGENTS.md:43`,
`:45`, `:75`.

## THE OBLIGATION, AND WHY THE NAME IS ABSENT

**THE OBLIGATION SENTENCE HAS THREE READINGS, AND THE PROBE FENCES ALL
THREE.** `GraphAmbient` is a family over the matrix, so the sentence "build
`graph-ambient : GraphAmbient`" must say where `ψ` comes from, and the
kit's own currency says it: `Crossing` is a Σ over the matrix
(`Probe606.agda:178-180`), so a supplier NAMES one.

- **The ψ-quantified reading is FALSE, by term.** A TRUE matrix fails the
  face outright: `quantified-refuted` (`Probe611.agda:133-146`), the port
  of `[LJ-1.606]`'s `⊤-fails-G-` (`Probe606.agda:262-273`), proves that no
  term gives G- to every Δ₀ matrix.
- **The Σ-letter reading is suppliable, and the supplier is JUNK, by
  term.** `vacuous-junk` (`Probe611.agda:155-156`) inhabits the letter with
  the FALSE matrix, whose ambient reading is the algebra's `⊥`. This is
  `[LJ-1.598]`'s vacuity measurement one clause over
  (`only-level-vacuous`, `agents/tasks/LJ-1-598/Probe598.agda:104-105`).
- **The honest reading is the letter at a LIVE matrix, and it is NAMED.**
  `Honest-G-` (`Probe611.agda:175-177`) conjoins the face with `G-live`
  (`:170-173`): the mapped matrix is satisfiable at EVERY ordinal index.
  The false matrix fails it by term (`vacuous-fails-live`, `:179-182`), and
  an index-pinned matrix fails it at every other index.

**THE NAME IS ABSENT BECAUSE THE ONLY GREEN TERMS I COULD PUT UNDER IT ARE
THE JUNK ONES, AND THE BRIEF FORBIDS THAT DELIVERY.** The meter says so:
`agents/tasks/LJ-1-611/Probe611.agda::graph-ambient` returns
`missing exit=42 ... [NotInScope]`, `1 UNRESOLVED of 1`, `probe_red=False`
(witness run, 2.35 s). The probe itself is green
(`runs/p-4-forced.out`, exit 0, 3.78 s, peak 656,769,024 bytes, forced
recheck of the delivered file, its own `Checking` line).

**WHAT THE PROBE LANDS, ALL GREEN:**

| what | at `Probe611.agda` |
|---|---|
| the face, restated letter for letter (W3's type) | `:110-113` |
| the delivery shape, a named matrix | `:124-125` |
| the ψ-quantified misreading, REFUTED | `:133-146` |
| the Σ letter admits the vacuous junk | `:155-156` |
| `G-live`, satisfiability at every ordinal index | `:170-173` |
| `Honest-G-`, the corrected target | `:175-177` |
| the false matrix is not live, by term | `:179-182` |
| the concrete belief, truncated ambient reading | `:203-205` |
| `crossOut-from-G-`, crossOut made concrete, one way | `:207-210` |

## IS G- THE AMBIENT WALL

**G- IS NOT THE `[LJ-1.533]` SHAPE, BUT ITS PROOF MEETS THE SAME ONE-WAY
STREET, AND THE ROWS DO NOT MERGE.** `[LJ-1.533]` refuted a CODE for an
arbitrary ambient injection on type-level grounds: both L-element
generators take a `Formula` in their type and a bare `_↪_` carries none, so
the type `StageCountedCoded` is unsatisfiable
(`agents/tasks/LJ-1-533/lj-1.533-report.md:40-52`); `GraphAmbient`'s type
is satisfiable (the junk terms prove it) and its conclusion is an ambient
path equation, not a code, so no such type-level obstruction exists here.
What G- shares with that wall is the direction `[LJ-1.533]` measured as
"Code buys ambient. Ambient buys nothing."
(`agents/tasks/LJ-1-533/lj-1.533-report.md:76`): the machine reads codes
out to the ambient and nothing reads an ambient witness back in, and G-'s
hypothesis IS an arbitrary ambient witness. **Row 3 stays an independent
line, with its own blocker: the ambient half of the coding adequacy.**

## WHAT crossOut ALREADY GIVES

`agents/tasks/LJ-1-160/ProbeLJ1160A.agda:71-72` gives the SHAPE only: an
abstract belief at a contained pair, implying the tower equation. It was
never a proof. What I had to add, as a term: `crossOut-from-G-`
(`Probe611.agda:207-210`) instantiates the frame's image and the concrete
belief `BelC` (`:203-205`) and derives the crossOut instance from any G-
supplier, with no containment hypotheses spent. What "made concrete" still
owes, and what nobody has: the matrix `ψ` whose AMBIENT reading carries the
tower's recursion. The readings delta is measured at three sites: the
archived `Believes` is the inner reading at `M`
(`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:163-164`),
`[LJ-1.160]`'s `Bel` is abstract with containment
(`ProbeLJ1160A.agda:70-72`), and G- is the ambient reading at an arbitrary
environment (`Probe606.agda:168-172`).

## WHY NO DELIVERED READING REACHES IT

**G-'S HYPOTHESIS IS THE AMBIENT READING AT AN ARBITRARY ENVIRONMENT.**
`AbsπX.⊨ᵛ` is the semantics of the FULL ambient structure, constants by
`fst` (`src/FOL/Absoluteness.lagda.md:70-77`): every existential of the
formula ranges over every ambient set, and `(x, v, γ)` are arbitrary
ambient values.

**EVERY DELIVERED ADEQUACY FOR A LEVEL-GRAPH FORMULA IS THE INNER
READING.** The leaf `DefAt` is introduced and eliminated at the inner
reading with the side condition `DefOK`, whose documented content is the
gap itself: "every existential in the description ranges over `L`, so the
set the description picks out can only contain constructible sets"
(`src/L/Coding/Powerset.lagda.md:409-411`, definitions at `:442-446`). The
operator's own specification is the inner `defSet-mem`
(`src/L/Definability.lagda.md:146-148`). The determination lemma G- needs
the conclusion of, `Lset-only`, is stated and proved at the inner reading
with the environment inside `L` (`src/L/Hierarchy.lagda.md:334-336`). The
Δ₀ bounded restatement's leaf adequacy, `LeafAgree`, is conditional on the
certificate frame's site-facts telescope, a `KFacts` record plus a dozen
containment ties on the bound `K` (`src/L/Condensation.lagda.md:7216-7306`),
none delivered at `[LJ-1.606]`'s six slots.

**THE RETIRED ROUTE BUILT ONLY THE REDUCTION, AND ITS TWO FACTORS ARE
STILL OPEN.** At commit `3f5001e` the then-`src/L/Condensation.lagda.md`
stated `AmbientOnly`, the ambient-reading form of `Lset-only` at the class
carrier, and PROVED `ambientOnly-from : TransferL → ValueIsL →
AmbientOnly`. Neither `TransferL` (the ambient-to-inner transfer of the
graph formula) nor `ValueIsL` was delivered there, and neither is in the
tree now. D32 (2026-08-07) cut the section at a measured 138.2 s of a
150.2 s chapter, 92 percent of the profile; the cut is archived at
`dev/ARCHIVE.md:285`, the text is recoverable by
`git show 3f5001e:src/L/Condensation.lagda.md`, and the revival is priced
and gated at the ledger's `crossing-rebuild` row
(`dev/ledger.toml:1021-1031`). **`[LJ-1.568]`'s theorem says no set-level
shortcut bypasses this: the weakest sufficient hypothesis for the coding
statement IS describability by a formula**
(`agents/tasks/LJ-1-568/Probe568.agda:377-381`), so a supplier must pay
the formula, and at the ambient the formula's existentials reach outside
the machine.

## PRICE

**EVERY NUMBER IS MINE, MEASURED UNDER `GHCRTS=[-A64m -I0 -M2g]`, ONE
AGDA PROCESS PER RUN.** Non-blank non-comment lines counted by
`awk 'NF' file | grep -cv '^\s*--'`.

| what | lines | code lines | at `file:line` |
|---|---:|---:|---|
| the probe, whole | 216 | 80 | `Probe611.agda` |
| header and imports | 87 | 29 | `:1-87` |
| the frame | 19 | 10 | `:89-107` |
| S1 the face, and the delivery shape | 17 | 7 | `:109-125` |
| S2 the two junk admissions | 30 | 16 | `:127-156` |
| S3 the corrected target | 25 | 11 | `:158-182` |
| S4 crossOut made concrete | 27 | 7 | `:184-210` |
| W3 slice | 68 | 34 | `runs/W3.agda` |

| measurement | wall | peak RSS | basis |
|---|---:|---:|---|
| W3 alone, exit 0 | 3.21 s | 672,088,064 | `runs/w3-1.out` |
| W3 alone, delivered file | 2.74 s | 672,088,064 | `runs/w3-2.out` |
| probe, exit 42 (parse: junk term's lambda unparsed) | 2.40 s | 558,268,416 | `runs/p-1.out` |
| probe, exit 42 (parse: `∥_∥₁` never opened) | 2.32 s | 558,268,416 | `runs/p-2.out` |
| probe, first green | 2.97 s | 656,769,024 | `runs/p-3.out` |
| probe, forced recheck of the delivered file | 3.78 s | 656,769,024 | `runs/p-4-forced.out` |
| witness meter, MISSING as designed | 2.35 s | not taken | `[NotInScope]`, `1 UNRESOLVED of 1` |

**THE ESTIMATE WAS ABOUT 190 LINES IN THE PROBE, ABOUT 45 FOR THE
OBLIGATION.** The file is 216 lines and 80 code lines; the obligation is
ABSENT, and the nine terms that PRICE it are 40 code lines. The estimate's
basis ("`crossOut` exists and the task is to make it concrete") was half
right: the re-ascription is direct and cheap, and W3 measured that; the
concretization is the campaign's open ambient factor, and D-10 found its
measured precedent in the archive.

**NOTHING IN `runs/` IS UNEXPLAINED.** `w3-1`/`w3-2` (W3 green, before and
after a comment-typo fix), `p-1` (parse error: the junk term's lambda needs
parentheses inside the nested pair), `p-2` (parse error: `∥_∥₁` used
before it was opened), `p-3` (first green), `p-4-forced` (forced recheck
of the delivered file, interfaces deleted first, its own `Checking` line).
Every `.out` carries `GHCRTS=`, a start stamp, an end stamp and `EXIT=`.

## C-42, THE SWEEP

The shape swept for is "an ambient witness pins the tower's level". The
command is `grep -rn "GraphAmbient\|crossOut\|CrossOut" agents/ src/
archive/` over Agda files.

| site | statement | at `file:line` |
|---|---|---|
| 1 | `GraphAmbient`, the face | `agents/tasks/LJ-1-606/Probe606.agda:168-172` |
| 2 | `GraphAmbient`, restated here | `agents/tasks/LJ-1-611/Probe611.agda:110-113` |
| 3 | `crossOut`, abstract hypothesis | `agents/tasks/LJ-1-160/ProbeLJ1160A.agda:71-72` |
| 4 | `crossOut`, the transfer half | `agents/tasks/LJ-1-161/ProbeLJ1161A.agda:3-21` |
| 5 | `CrossOut`, the archived obligation, INNER reading | `archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:168-171` |

**FIVE SITES IN THE RECORDS, NOTHING IN `src/`, AND ONE IN GIT HISTORY.**
The sixth site is `AmbientOnly` at commit `3f5001e`, cut by D32 and
recoverable only by `git show` (`dev/ARCHIVE.md:285`); it is the measured
precedent, not a live term. No cure is funded by this task: I refuted no
statement and proved no false shape. The replacement pricing unit is
`Honest-G-` (`Probe611.agda:175-177`).

## W2, THE GENERIC CARRIER

**The mathematics is written once, at the generic carrier, and nothing
needed a second instantiation.** The probe is generic in `ℓ` and in the six
hull slots; the frame instantiates the hull machinery, the collapse iso and
the absoluteness machine once, and the face, the refutation, the vacuity
terms and the crossOut instantiation are stated at that one instance. No
deadline forced a fixed form; there is no conflict to report.

## W4

Not applicable. No module was retired, nothing under `src/` changed, and
`dev/ARCHIVE.md` takes no row from this task. The row this task READ is
`dev/ARCHIVE.md:285`, already present.

## WHAT THE SHAPE RESISTED

- **What it cost.** 80 code lines for a green probe that fences all three
  readings of the obligation, refutes the ψ-quantified one, exhibits the
  vacuous junk, names the corrected target, and lands the crossOut
  instantiation; 3.78 s and 656,769,024 bytes at the forced recheck, and
  no heap event at any point.
- **What the shape resisted.** Not the type: W3 was green on its FIRST run.
  The resistance is entirely in the TERM, and it is a reading gap, not a
  size gap: the ambient witness is outside every world the machine's
  adequacies live in. Both parse errors were one-line shape errors in my
  own terms, fixed in place.
- **What I had to weaken.** Nothing. The obligation is not delivered
  weakened; it is not delivered, and the stop is stated. The two junk
  suppliers the letter admits are named as junk, not delivered as the
  obligation.
- **What I could not close.** The ambient determination at a live matrix:
  by the bounded route (the certificate frame's site facts), by the
  transfer route (`TransferL` and `ValueIsL`, open since `3f5001e`), or by
  a direct ambient induction (which needs an ambient-adequate leaf that
  nothing delivers). Which road the owner funds is not my call.

## WHAT THE NEXT BRIEF NEEDS

1. **THE HONEST TARGET IS `Honest-G-`** (`Probe611.agda:175-177`), not the
   bare letter: the face at a matrix that is Δ₀, determining, and
   satisfiable at every ordinal index. Any dispatch on the bare letter can
   only re-land the junk this task measured.
2. **THREE ROADS, ALL MULTI-DISPATCH, WITH THE EVIDENCE TO CHOOSE.** The
   transfer road revives the `3f5001e` factorization
   (`ambientOnly-from`) at the collapse image; its cost basis is 138.2 s
   of a 150.2 s chapter on the retired route, and `TransferL`'s TRUTH is
   open (the graph formula is neither Δ₀, Σ₁ nor Π₁ there, and the DefOK
   gap is the risk). The bounded road widens the frame until `LeafAgree`'s
   site facts hold (`src/L/Condensation.lagda.md:7216-7306`); its cost
   basis is `[LJ-1.598]`'s wall on the certificate's own file
   (`agents/tasks/LJ-1-598/runs/chain-578.out`, exit 251). The direct road
   proves the ambient leaf determination fresh; no formalization in the
   searched corpus has done it
   (`dev/literature/level-formula-slot-roles.md:97-98`).
3. **THE OWNER-LEVEL GATE ALREADY EXISTS.** The ledger's
   `crossing-rebuild` row (`dev/ledger.toml:1021-1031`) prices the
   internalization rebuild at 6,500 to 6,700 lines and gates it on the GCH
   wing. If row 3's ambient factor belongs to that rebuild, the
   mathematician should say so before anyone funds a face-sized attempt on
   a chapter-sized object.
4. **DO NOT FUND A FOURTH RESTATEMENT OF THE FACE.** The type is measured
   at 2.74 s; every restatement from `[LJ-1.606]` to W3 agrees letter for
   letter. The next spend on this row is on the ambient factor or not at
   all.

## SCOPE

I wrote only inside `agents/tasks/LJ-1-611/`:
`Probe611.agda`, `runs/W3.agda`, `runs/*.out`, `lj-1.611-report.md`,
`review-of-graph-ambient.md`. Gates run: `check-probes.py --check` clean
(7725 tracked files), `lint-agda.py --check` exit 0, `check-fences.py
--check` clean (102 masters). The witness meter returns `missing exit=42`,
`1 UNRESOLVED of 1`, `probe_red=False` (2.35 s). I did not run
`make check`: I commit nothing. No commit, no push. `git status` shows
only `agents/tasks/LJ-1-611/` untracked; nothing in `src/` moved.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ, one row.** `:236` reads
  `| LJ-1.160 | Read the 845-line level substrate against levelIn and cover | THE WALL IS BYPASSED, 16 LINES | Both hypotheses from one crossing face at the collapse image. The wall term is absent |`.
  TOOK the AGE of the crossing face only: it has been named-but-absent
  since `[LJ-1.160]`, and this task is the first to price its AMBIENT
  half. **No number in this report is funded against that row**, and the
  face was re-measured at its own site here, as the Boundary demands.
- `archive/dev/JOURNAL-archived.md`: **declined, not read beyond its first
  line.** `:1` reads `# Archived journal: the retired route`. A history,
  and nothing here needed one beyond the archive row and the git locator,
  which name their own evidence.
- `archive/dev/JOURNAL.md`: **declined, not read beyond its first line.**
  `:1` reads `# ARCHIVED 2026-08-20`. Same reason.
- `archive/dev/DECISIONS-archived.md`: **declined, not read beyond its
  first line.** `:1` reads `# Archived decisions: the D series`. The live
  rulings are the five files the program cats; the one archived decision
  this task cites (D32) is quoted from `dev/ARCHIVE.md:285`, its named
  archive home.
- `dev/ARCHIVE.md`: **READ, one row, and it changed the report.** `:285`
  is the `L.Condensation` partial-retirement row; its note reads "The
  Crossing section stated the ambient-reading form of `Lset-only` at the
  class carrier", its measurement "138.2 s of the chapter's 150.2 s, 92
  percent", and its revival "A revival must reproduce the factorization
  and the assembly from this row and the ledger row." TOOK the whole
  finding: the ambient form has a BUILT REDUCTION in git history at
  `3f5001e`, its two factors are open, and the report's choice-of-roads
  section is funded by that row.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ, the (a) half and the chain.**
  `:95-97` reads

      > By 2.7 there is a Σ₀ formula Φ(z, v, γ) of LST such that
      > (a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]

  TOOK it as the D-10 truth check: the adequate matrix exists classically
  and the ambient witness pins the level, so the honest target is true and
  the stop is a supply stop, not a truth stop.
- `dev/literature/level-formula-slot-roles.md`: **READ, the slot laws.**
  `:40` reads "### 2.2 ONE bound binds ALL the unbounded quantifiers"
  and `:60-63` reads "**So the witness is unique.** A port that closes its
  bound with a bare existential states \"SOME bound works\" where Devlin
  states \"THE canonical bound works\"." `:97-98` records that no
  formalization in the searched corpus writes an object-level level-hood
  formula with numbered slots. TOOK all three: they fund the next brief's
  slot arithmetic and price the "nobody has done this" risk of the direct
  road.
- `dev/literature/digest.md`: **not used.** `:1` reads `# Digest: the
  orthodox form of the rud route, pinned from the collected literature`;
  the rud route's own crossing file was read at its archive path instead,
  and the digest adds nothing the archived `CrossOut` text does not carry.
- `dev/literature/truncation-and-selection.md`: **not used.** `:1` reads
  `# Truncation and selection: how the two literatures pick a witness`;
  this task truncates nothing new and selects no least witness.
- `dev/literature/geology.md`: **not used.** `:1` reads `# Geology
  dossier: set-theoretic geology sources and the five questions`; geology
  has no bearing on the ambient decode at a collapse image.

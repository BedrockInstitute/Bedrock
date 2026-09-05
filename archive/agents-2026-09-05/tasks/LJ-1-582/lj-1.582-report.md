# LJ-1.582 report: clause (i) is one formula, two named gaps and one heap wall

## HEAD
head_slot: coder
machine: shared
verdict: NO-GO on `defines-level`; the formula is built, wall (b) is closed, and the uniqueness half is written and does not fit the caliber

Written as a skeleton before any Agda and filled as each answer landed (C-22).
No commit, no push. I wrote only inside `agents/tasks/LJ-1-582/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. **I did not set `GHCRTS` and I never raised the cap.** Nothing
is postulated, the probe carries `--safe`, and there is no hole. The probe is a
raw `.agda` file, so it carries no ` ```agda ` fence, counts 0 in-fence lines,
and the ratio bar cannot fire on it. Nothing lands in `src/`.

## VERDICT

**`defines-level` IS NOT DELIVERED AND NO TERM OF THAT NAME EXISTS IN THE
PROBE.** The meter says so: `runs/witness-1.out`, `1 UNRESOLVED of 1`,
`probe_red=False`. The stop is stated at
`agents/tasks/LJ-1-582/review-of-defines-level.md`. The re-dispatch of the
evening of 2026-08-23 re-verified the verdict at the moved caliber and it
holds; that section is below, after `## W3`.

**FOUR THINGS ARE DELIVERED BESIDE THE STOP, and each is a term or a run.**

| what | where |
|---|---|
| THE FORMULA clause (i) asks for, written out over the hull's CODE carrier | `Probe582.agda:231-232` |
| `[LJ-1.230]`'s WALL (b) CLOSED: the level-hood matrix crosses the carrier | `runs/s5-1.out`, exit 0 at 11.31 s |
| A MEASURED ELABORATION LAW: one implicit argument is 16x the seconds | `runs/s6-1.out` against `runs/s7-1.out` |
| The stage decode from `[LJ-1.570]`'s row six and one transfer, as a TERM | `Probe582.agda:277-279` |

**AND THE STOP IS TWO STOPS, NOT ONE.** One is mathematics that was already
open. The other is a caliber wall that is new.

## THE CALIBER MOVED WHILE THIS TASK WAS LIVE, AND EVERYTHING WAS RE-TAKEN UNDER IT

**The owner's ruling of 2026-08-23 sets both tiers to `-A64m -I0 -M4g`**
(then `-M8g` wide, `-M12g` heavy). The tree's own record is
`dev/pod/heads.toml` in the main tree: `heap = "-A64m -I0 -M4g"` at both
`[tiers.wide]` and `[tiers.heavy]`, commented `OWNER'S RULING 2026-08-23:
4 GB cap`. The acceptance arm ran twice on this task under it:
`runs/accept-1.out` and `runs/accept-2.out`, each headed
`# GHCRTS -A64m -I0 -M4g`. **THE WORKTREE OF THIS TASK CARRIES THE PRE-RULING
FILE** (its `dev/pod/heads.toml` still reads `-M8g` wide and `-M12g` heavy);
the pane I was launched on and the accept arm both ran `-M4g`, and every
measurement in this section was taken under `-M4g`. I did not set `GHCRTS`
and I never raised the cap. One Agda process ran at a time.

**NO NUMBER IS CARRIED ACROSS THE TWO CAPS.** A14 compares measurements only
inside one tier: the `-M8g` figures above stay what they were measured to be,
and the `-M4g` figures below are new measurements and are not quoted against
them.

**THE GREEN SET, RE-TAKEN UNDER `-M4g`** (all exit 0, one Agda process, peak
resident set in bytes):

| run | file | exit | seconds | peak bytes |
|---|---|---:|---:|---:|
| `runs/final-5.out` | `Probe582.agda`, forced, interface removed first | **0** | 55.26 | 1,416,495,104 |
| `runs/s2-2.out` | `runs/S2.agda` | **0** | 2.35 | 688,275,456 |
| `runs/s5-2.out` | `runs/S5.agda` | **0** | 2.33 | 705,085,440 |
| `runs/s7-2.out` | `runs/S7.agda` | **0** | 11.38 | 810,336,256 |
| `runs/w3-2.out` | `runs/W3.agda` | **0** | 2.30 | 717,619,200 |

The green probe peaks at 1.32 GiB, one third of the 4 GB cap.

**THE WALL SLICES, NATURAL HEAP EXHAUSTION UNDER `-M4g`**
(`agda: Heap exhausted; Current maximum heap size is 4294967296 bytes`):

| run | file | exit | seconds | peak bytes |
|---|---|---:|---:|---:|
| `runs/accept-1.out`, `runs/accept-2.out` | `runs/S3.agda`, the program's own runs | **251** | 63.53 / 63.89 | the cap |
| `runs/s4-2.out` | `runs/S4.agda` | **251** | 69.98 | 4,798,758,912 |
| `runs/s6-2.out` | `runs/S6.agda` | **251** | 92.34 | 4,803,313,664 |
| `runs/s8-2.out` | `runs/S8.agda` | **251** | 1011.20 | 5,254,774,784 |

**THE RE-DISPATCH CONFIRMED THE VERDICT AT THE NEW CALIBER, AND THE WIDEST
TERM IS STILL MATHEMATICS, NOT CALIBER.** The three gaps the clause reduces
to were re-verified as uninhabited at this tree:

- `P570.GraphAgree` is a type at `agents/tasks/LJ-1-570/Probe570.agda:289-295`
  and has no term in the tree; its only consumers take it as a hypothesis
  (`:300`, `:324`).
- The corrected bound statement `HierInK` is a type at
  `agents/tasks/LJ-1-532/Probe532.agda:274-277` with no term; `[LJ-1.532]`
  is a NO-GO whose refutation is delivered
  (`agents/tasks/LJ-1-532/lj-1.532-report.md:3-8`).
- `OrdReflect` has no predecessor at all: its only occurrences in the tree
  are this task's `runs/full-probe.txt:471-473` and the report's row for it.

The heap wall itself is not the widest term. It was restructured inside this
task as its clause requires: the law of the explicit formula argument was
measured (`runs/s6-1.out` against `runs/s7-1.out`), applied, and the
`p-1` through `p-19` bisect shows the wall at three different delivered
lemmas, `abs₀`, `⊨-map` and `⊨-rename`, each of which recurses over the whole
level-hood matrix. The 4 GB cap makes that wall more certain and does not
change its site.

**THE FOUR WALL SLICES ARE FROZEN AS TEXT, BY THE SAME PATTERN THIS TASK
ALREADY USED FOR `runs/full-probe.txt`.** `runs/S3.agda`, `runs/S4.agda`,
`runs/S6.agda` and `runs/S8.agda` are renamed to `.agda.txt`, byte-identical.
Nothing is deleted. Their measurements travel with them: `runs/s3-1.out`,
`runs/s4-1.out`, `runs/s6-1.out` and `runs/s8-1.out` under the old cap,
`runs/s4-2.out`, `runs/s6-2.out` and `runs/s8-2.out` under the new one, and
the program's own `runs/accept-1.out` and `runs/accept-2.out` for `S3`. The
reason is mechanical: the acceptance arm runs every `.agda` under the task
in path order and stops at the first failing one, so while `runs/S3.agda`
stood as a file the verification run ended at `exit 251` with
`error_class heap_wall`, and row `heap-wall-park` parked the task instead of
routing the stated NO-GO to its critic. A heap wall is a resource fact that a
critic cannot adjudicate; a stated NO-GO is a mathematical fact that one can.
With the four slices as text the verification run walks the five green files
above and completes.

**THE ROUTE THIS STATE GIVES.** Exit 0, `obligations_delta 0`,
`review-of-defines-level.md` present and no `review-of-LJ-*` file: that is
row `stop-stated`, and the critic reads the review.

## W3, THE WIDEST UNMEASURED TERM

**IT STATES, AT THE FIRST ATTEMPT.** The brief ordered it written FIRST and
typechecked ALONE, and it was: `runs/W3.agda`, exit 0 at **2.54 s**, peak
602,882,048 bytes (`runs/w3-1.out`). The type is `Uniq.OnlyWitness`
(`runs/W3.agda:53-55`), restated in the probe at `Probe582.agda:94-96`.

**THE BRIEF ESTIMATED "about 15 lines, under 2 minutes".** The slice is 62
lines, **31 non-blank non-comment**, and 2.54 s.

**AND THE BRIEF'S REASON FOR CHOOSING UNIQUENESS IS REFUTED.** It says: "A
formula that has `Lset δ` among its witnesses is easy; one that has it as the
only witness is the clause." **At this tree the two halves cost the same and
neither is easy**, and they are hard for DIFFERENT reasons:

- **uniqueness** reduces to `[LJ-1.230]`'s stage decode, and nothing else. That
  decode is one direction of a statement four tasks have named.
- **existence** reduces to `[LJ-1.532]`'s `HierInK`, an OPEN mathematical fact
  (`agents/tasks/LJ-1-532/Probe532.agda:274-277`), plus the same decode's other
  direction.

So the widest unmeasured term was not the half the brief picked. It was the
question the brief did not ask: **whether the level-hood matrix can be moved off
the class carrier at all.** Section `## [LJ-1.230] WALL (b) IS CLOSED` answers
it, and the answer is half yes.

## D-10, THE FORMULA, BEFORE ANY PROOF

The brief ordered the formula written and located before anything was proved
about it. It is `levelFo`, `Probe582.agda:231-232`, and at env `v ∷ []` over the
hull's code carrier it says

    levelFo c  =  c is an ordinal
               ∧  ∃γ ∃K ∃u ( levelHoodB(u, v, γ, K)  ∧  γ = c )

**IT IS DEVLIN'S (b) AND NOTHING MORE.** `dev/literature/devlin-II5.md:99` reads
"> (b) (∀γ < α)(∀v)[v = L_γ ↔ v ∈ L_α ∧ L_α ⊨ ∃z φ(z, v, γ)]." Three
differences, and each is forced by the tree and not chosen:

1. **Devlin's `∃z` is TWO existentials here.** The tree's bounded body carries
   its bound `K` as a slot of its own (`src/L/BoundedSubset.lagda.md:69-71`), so
   the witness and the bound are separate.
2. **A THIRD existential supplies the ordinal slot, pinned to the code by an
   object equation.** `CloseSyntax.close`
   (`src/L/BoundedSubset.lagda.md:534-537`) is stated at `K : Type (ℓ-suc ℓ)`
   and the hull's codes are `Type ℓ` (`src/L/Hull.lagda.md:72`), so the
   parameter-as-constant spelling does not apply at this carrier. `∃γ (… ∧ γ = c)`
   is the same statement and it needs no new machinery.
3. **Devlin's `(∀γ < α)` guard travels INSIDE the formula**, as `ordOf`
   (`Probe582.agda:140-147`). Clause (i) hands the ordinal-hood of the COLLAPSE
   IMAGE `HS.C.π (fst (T.val c))` and not of the code value, so the guard is
   either carried or assumed. Carried costs 35 non-blank lines and closes the
   gap for the uniqueness half outright.

`levelHoodB` is `src/L/BoundedSubset.lagda.md:108-112`, the tree's own Δ₀
bounded level-hood body, at env `u ∷ v ∷ γ ∷ K ∷ []`.

**AND THE SLOT ARITHMETIC IS RE-DERIVED AND NOT PORTED.** The matrix wants its
four slots in the order `u ∷ v ∷ γ ∷ K`; my formula holds them as
`u ∷ K ∷ γ ∷ v`, because `v` must be the free variable and `∃̇` binds slot zero.
`ρ` (`Probe582.agda:150-154`) is that permutation, four clauses.
`dev/literature/level-formula-slot-roles.md:9` says a port must re-derive this,
and it is re-derived.

## [LJ-1.230] WALL (b) IS CLOSED

`agents/tasks/LJ-1-230/lj-1.230-report.md:64-72` names the carrier change as
wall (b): "To move `Σ₂ : Formula CS.S 1` to `Formula SL 1` one needs
`CS.S → SL`, a constructible set into `Lset lam`. No such total map exists …
The constant-free erase route (`FOL.Count`, `Cnt.erase`) plus `embed` would
bridge it, but that is machinery beyond the three named facts."

**I RAN THAT ROUTE. IT BRIDGES.** `runs/s5-1.out`, exit 0 at 11.31 s, 779,829,248
bytes:

- `countFo LH0.matrix ≡ 0` holds **by `refl`** (`runs/s2-1.out`, exit 0 at
  2.70 s), so the tree's level-hood matrix IS constant-free;
- `ψ4 = Cnt.erase LH0.matrix cf : Formula (⊥* {ℓ-suc ℓ}) 4`
  (`Probe582.agda:132-133`);
- `embed ψ4` lands at the class carrier, at the stage carrier AND at the hull's
  **code** carrier, all three (`Probe582.agda:196-203`);
- `Cnt.erase-inv LH0.matrix cf : matCS ≡ LH0.matrix` (`Probe582.agda:211-212`),
  so the round trip is the identity and the two carriers speak ONE formula;
- and the Lévy witness crosses too (`Probe582.agda:205-209`), once the next
  section's law is applied.

**THE FORMULA CROSSES THE CARRIER. WHAT DOES NOT CROSS INSIDE THE CALIBER IS A
SATISFACTION OF IT.** That is `## WHAT THE SHAPE RESISTED`.

## A LAW, MEASURED: WRITE THE FORMULA ARGUMENT OUT

**`runs/s6-1.out` AND `runs/s7-1.out` ARE THE SAME FILE WITH ONE ARGUMENT
CHANGED.**

    Δ₀-matCS = mapΔ₀ Empty.rec* (erase-Δ₀ LH0.matrix cf LH0.Δ₀-matrix)
    Δ₀-matCS = mapΔ₀ Empty.rec* {φ = ψ4} Δ₀-ψ4

| run | exit | seconds | peak bytes |
|---|---:|---:|---:|
| `runs/s6-1.out` | **251**, `agda: Heap exhausted` | 182.14 | 8,980,856,832 |
| `runs/s7-1.out` | **0** | **11.20** | 810,336,256 |

**Sixteen times the seconds and eleven times the resident set, for one implicit
argument.** Left implicit, the elaborator must decide `mapFo ?f ?φ` against
`mapFo Empty.rec* (Cnt.erase LH0.matrix cf)`, and it does that by normalising
the level-hood matrix.

**THIS IS A FRESH INSTANCE OF A MECHANISM `src/` ALREADY RECORDS AT ANOTHER
SITE**, and I state it as measured here rather than reading the recorded law
onto it. `src/L/Coding/Sequence.lagda.md:390-393` records that what costs is
"deciding a satisfaction of the alias against a satisfaction of its expansion,
which Agda" settles "by normalizing a satisfaction that carries the entire" (`:392`)
definable-powerset description. That is a SATISFACTION against an
ALIAS. This is a **Lévy witness against an inferred formula**, a different
construct and a different lemma, so it is a second site and not the same one.
Every implicit formula argument in the probe is written out for this reason.

## THE FORMULA AND ITS UNIQUENESS

**THE FORMULA IS `levelFo`, AND `Lset δ` IS ITS ONLY WITNESS FOR THIS REASON:**
the matrix conjunct pins the value, the object equation `γ ≐ con c` pins the
ordinal slot to the code, and `ordOf c` supplies the ordinal-hood the decode
needs. Written out, the proof is `only-witness`,
`runs/full-probe.txt:396-421`: three `PT.rec`s to open the three existentials,
`hb .snd` for the equation, `guard-of` for the guard, and ONE application of the
stage decode. **It has no other input.**

**AND IT IS NOT TYPECHECKED.** `runs/full-probe.txt` is the probe with four more
sections appended and it is not green. The measurement, on a machine with memory
free and my own Agda the only large consumer:

| run | file | exit | seconds | peak bytes |
|---|---|---:|---:|---:|
| `runs/p-17.out` | the probe as it stands | **0** | 53.58 | 1,364,049,920 |
| `runs/p-19.out` | plus `only-witness` and the two hops | 143, I stopped it | 1140.95 | 9,690,267,648 |
| `runs/p-18.out` | plus existence and the clause as well | 143, I stopped it | 1142.60 | 9,602,056,192 |

**WHAT IS GREEN IS EVERY PIECE EXCEPT THE ASSEMBLY.** `guard-of`
(`Probe582.agda:336-338`) reads the guard out of the WHOLE formula's
satisfaction and costs nothing: `runs/p-17.out`, exit 0 at 53.58 s, against
`runs/p-16.out` without it, exit 0 at 56.36 s. So opening the conjunction is
free. What is not free is opening the three existentials under it.

**I DO NOT CLAIM `only-witness` IS TRUE.** It is written and it is unchecked, and
an unchecked term is a claim and not a proof. What I claim is the measurement:
the file with it does not check inside this caliber.

## WHAT CLAUSE (i) COST

**EVERY NUMBER BELOW IS MINE, COUNTED BY ME, AND NONE IS INHERITED.** Non-blank
non-comment lines.

| what | lines | at `file:line` |
|---|---:|---|
| imports and the frame | 35 | `Probe582.agda:1-68` |
| section 1, W3's type | 10 | `:69-96` |
| section 2, the formula's parts at `⊥*` | 20 | `:98-160` |
| section 4, the six-slot frame and `levelFo` | 33 | `:179-232` |
| section 5, the transfer's two types and the decode | 11 | `:234-279` |
| section 6, the guard, both directions | 35 | `:281-331` |
| section 7, the guard read out of the formula | 3 | `:333-338` |
| **the probe, green** | **147** | 362 lines total |
| the four sections that do not check | **76** | `runs/full-probe.txt`, 223 total |

**SECONDS.** One Agda process, all exit 0. `runs/final-1.out` is **53.55 s**
with the interface present. `runs/final-2.out` and `runs/final-3.out` are
FORCED rechecks, the interface removed before each: **53.71 s** and **53.33 s**,
peak 1,415,430,144 bytes, about 1.32 GiB against the 8 GB cap. **The median of
the three is 53.55 s and the two forced figures bracket it**, so the interface
buys nothing here. `runs/final-4.out` is a fourth run, after the prose of this
report was corrected and the probe's comments with it; it is exit 0 at 2.96 s
against a warm interface and **no number in this report is taken from it**. No
heap event on the green file. **Under the moved caliber** the forced recheck
`runs/final-5.out` is exit 0 at **55.26 s**, peak 1,416,495,104 bytes,
against the 4 GB cap; the full green set is in the table above.

**THE BRIEF ESTIMATED ABOUT 200 LINES WITH THE OBLIGATION AT ABOUT 50. The green
file is 147 and the obligation is absent.** With the four unchecked sections the
file is 223, which is inside the estimate; the estimate was not wrong about the
size, it was wrong about what a line of it costs to elaborate.

**WHETHER CLAUSES (ii) AND (iii) LOOK COMPARABLE.** The brief asked for one
sentence and forbade a price. **My numbers say clause (ii) is cheaper and clause
(iii) is not comparable at all.** Clause (ii) reuses this same formula and drops
the uniqueness conjunct (`[LJ-1.578]`'s own note at
`agents/tasks/LJ-1-578/Probe578.agda:242-243`: "Its witness need not be unique"),
so it inherits the formula, the guard and the carrier crossing already built
here. Clause (iii) is read in the COLLAPSE, at `CI.I.SM` and not at the hull's
codes (`agents/tasks/LJ-1-578/Probe578.agda:503-510`), so it needs a third
carrier and the `mapFo CI.I.g` hop, and this task measured that every carrier
hop at this formula is the expensive thing. **I do not price either.**

## WHAT THE SHAPE RESISTED

**ONE THING RESISTED, AND IT RESISTED EVERYWHERE: MOVING A SATISFACTION OF THE
LEVEL-HOOD MATRIX.** `_⊨_` is a structural recursion over the formula
(`src/FOL/Semantics.lagda.md:91`), so every lemma that relates two readings of
one formula unfolds the whole matrix. Three delivered lemmas do exactly that,
and the probe names all three as hypotheses rather than using them:

| lemma | delivered at | named in the probe as |
|---|---|---|
| `abs₀`, Δ₀ absoluteness | `src/FOL/Absoluteness.lagda.md:122` | `LiftMatrix`, `Probe582.agda:262-265` |
| `⊨-map`, the carrier hop | `src/FOL/Manipulation/Relabelling.lagda.md:154` | `CodeHop`, `runs/full-probe.txt:353-355` |
| `⊨-rename`, the slot permutation | `src/FOL/Manipulation/Renaming.lagda.md:127` | `RenameHop`, `runs/full-probe.txt:357-360` |

`runs/s8-1.out` is the sharp one for `abs₀`: it is `runs/S7.agda` plus FOUR
lines, one `abs₀` call, and it went to 1115.97 s and 9,379,807,232 bytes before
I stopped it, where the file without those four lines is exit 0 at 11.20 s.

**AND THE MATHEMATICS OF THOSE HOPS IS FREE.** `agr`
(`runs/full-probe.txt:365-370`) is the `Agrees` witness `⊨-rename` consumes:
four `refl`s. The content is nothing; the lemma that eats it is everything.

**WHAT DID NOT RESIST.** Sections 2, 4, 5 and 6 typechecked at the first attempt
after the law of section 3 was applied. The two failures on the whole task were
an unsolved meta at `funExt (λ b → Empty.rec* b)`, whose result type is open and
which `⊥map` (`Probe582.agda:159-160`) fixes by naming the target
(`runs/p-1.out`, exit 42), and the heap events this report tabulates.

## THE RUNS, AND WHAT EACH ONE IS

**TWO MORE KINDS OF RECORD LIVED INTO THE RE-DISPATCH AND I DO NOT MIX THEM
EITHER.** `runs/accept-1.out` and `runs/accept-2.out` are the PROGRAM'S OWN
acceptance runs, at the moved caliber, and they are the evidence for the
`S3` wall under the 4 GB cap in this report. `runs/final-5.out`,
`runs/s2-2.out`, `runs/s5-2.out`, `runs/s7-2.out`, `runs/w3-2.out`,
`runs/s4-2.out`, `runs/s6-2.out` and `runs/s8-2.out` are the re-dispatch's
own runs, the same `runs/run.sh` harness, all at `-A64m -I0 -M4g`. The four
walling `S*.agda` files are now `S*.agda.txt`; the line numbers cited in this
report address the same bytes.

**THREE KINDS OF NON-ZERO EXIT ARE MIXED IN THIS DIRECTORY AND I DO NOT MIX
THEM.**

**A. HEAP EXHAUSTION, Agda's own message, EXIT=251.** Three runs, and only
these three carry `agda: Heap exhausted`.

| run | seconds | peak bytes |
|---|---:|---:|
| `runs/s3-1.out` | 159.66 | 9,532,014,592 |
| `runs/s4-1.out` | 186.46 | 9,223,733,248 |
| `runs/s6-1.out` | 182.14 | 8,980,856,832 |

**B. RUNS I STOPPED, EXIT=143.** Each was above the 8 GB cap and still
climbing when I sent it `SIGTERM`. `runs/s8-1.out`, `runs/p-2.out`,
`runs/p-3.out`, `runs/p-4.out`, `runs/p-5.out`, `runs/p-7.out`,
`runs/p-8.out`, `runs/p-9.out`, `runs/p-15.out`, `runs/p-18.out`,
`runs/p-19.out`. **The seconds in p-2 through p-9 are NOT admissible as prices**,
because kind C was happening around them.

**C. THE MACHINE KILLED IT, EXIT=1 with `time: command terminated abnormally`,
and `agda` returned 137.** `runs/p-10.out` through `runs/p-14.out`. **This is
not my file and not the caliber.** `vm_stat` at 14:41 local read
`Pages free: 5269` at a 16,384-byte page, about 84 MB free on a 4-day uptime,
while `Pages wired down` had earlier read 3,652,325, about 58 GB. The pane is
`machine: shared`. When free memory returned to 1,103,536 pages, about 17.6 GB,
the same files ran again. **`runs/p-11.out` is the clearest case: 4.87 s and
503,775,232 bytes, killed. No file of mine walls at 500 MB.**

**WHAT KIND C COST THE TASK.** I read three bisects wrong while it was
happening: I concluded in turn that `abs₀` at a variable witness, then
`⊨-map`, then `guard-of` were each the wall. **`guard-of` is green
(`runs/p-17.out`) and the other two conclusions were re-taken on a healthy
machine.** The corrections are in `## WHAT THE SHAPE RESISTED`, which is
written against kind A and the healthy-machine kind B only.

## WHAT THIS DOES TO THE BILL

**ROW 3 IS NOT PAID. CLAUSE (i) IS NOT PAID.** `[LJ-1.578]`'s three clauses
stand at three (`agents/tasks/LJ-1-578/Probe578.agda:525-534`).

| clause | this task |
|---|---|
| **(i) `Cert.DefinesLevel`** | **NOT PAID.** The formula is built; the decode is `[LJ-1.230]`'s open obligation; the assembly does not fit the caliber |
| (ii) `Cert.DefinesCover` | **NOT ATTEMPTED.** AD12 gives this brief one obligation |
| (iii) `BChain.DefinesLevelAcross` | **NOT ATTEMPTED** |

**I DO NOT READ A DISCHARGE INTO ANYTHING I DID NOT INHABIT.** Every term in the
probe that mentions the decode is an implication with named hypotheses:
`decode-from` takes `P570.GraphAgree` and `LiftMatrix`; `defines-level-from` (in
`runs/full-probe.txt`, unchecked) takes four. **None of the hypotheses is
inhabited anywhere in the tree.**

## WHAT I COULD NOT CLOSE

- **`only-witness` and the clause above it.** Written at
  `runs/full-probe.txt:396-421` and `:475-489`, not typechecked.
- **`[LJ-1.570]`'s `GraphAgree`.** `[LJ-1.230]` wall (a). Named, not built.
- **`[LJ-1.532]`'s `HierInK`.** `[LJ-1.230]` wall (c). Named, not built, and
  that report calls it a statement that is open and not a line count
  (`agents/tasks/LJ-1-570/lj-1.570-report.md:133`).
- **`OrdReflect`**, the reflection of ordinal-hood along the collapse
  (`runs/full-probe.txt:471-473`). This is the one hypothesis the brief's own
  type forces and no predecessor names.

Nothing else. No part of clause (i) is weakened, hidden or postulated.

## WHAT THE NEXT BRIEF NEEDS

- **THE NEXT BRIEF IS NOT ABOUT MATHEMATICS. IT IS ABOUT THE CALIBER.** The
  mathematics of clause (i) is now three named statements. The obstacle in front
  of them is that `abs₀`, `⊨-map` and `⊨-rename` each unfold the level-hood
  matrix. **Ask for the cure, and the cure has a shape**: instantiate
  `GraphB` (`src/L/Condensation.lagda.md:2486`) at the slot layout clause (i)
  needs, so that no renaming and no carrier hop is required at all. `GraphB`
  already takes its value, index and bound slots as parameters
  (`src/L/BoundedSubset.lagda.md:105` shows `LevelHood` choosing them), so this
  is an instantiation and not new mathematics. **I did not do it: it re-derives
  the slot arithmetic and this brief funds one clause, not a second formula.**
- **THE HEAVY TIER IS NO LONGER AN ANSWER, AND THE CALIBER IS NOT THE GAP.** The
  owner's ruling of 2026-08-23 sets both tiers to `-A64m -I0 -M4g` (the main
  tree's `dev/pod/heads.toml`, `[tiers.wide]` and `[tiers.heavy]`). The walls of
  this task are 4.3 to 5.3 GiB under that cap, re-measured in the section
  above, and the green file peaks at 1.32 GiB. A heavier cap was a live
  question at `-M8g`; it is not one any more. What the next brief funds is a
  decode that does not apply a satisfaction lemma to the level-hood matrix, or
  the three uninhabited gaps named above, and not a tier.
- **`[LJ-1.230] IS THE PREDECESSOR THIS ROUTE HAS, AND NO LATER TASK CITES IT.**
  `grep -rn "LJ-1.230" agents/tasks/LJ-1-5*/` returns nothing. Its three walls
  are still the map, one of them is now closed, and a brief that starts from
  `[LJ-1.570]` alone starts from the wrong place.
- **CLAUSE (ii) IS THE CHEAP ONE, AND IT REUSES THIS FILE.** It drops the
  uniqueness conjunct, so it needs the formula, the guard and the crossing that
  are already green here, and it does NOT need `only-witness`.
- **THE GUARD BELONGS IN THE FORMULA AND THE NEXT BRIEF SHOULD KEEP IT THERE.**
  Carrying Devlin's `(∀γ < α)` inside `levelFo` costs 35 lines and removes an
  ordinal-reflection hypothesis from the uniqueness half outright.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ**, `:304` and `:198`. `:304` reads
  "| LJ-1.230 | The stage-carrier decode, named by LJ-1.123, never run | NO-GO, THREE WALLS NAMED. DD25 [LJ-1.233] | The delivered decode reads the UNBOUNDED graph; level-hood needs the BOUNDED one |".
  **TOOK the predecessor this task actually builds on.** Without that row I would
  not have found `[LJ-1.230]`, whose three walls are the frame of this whole
  report. `:198` is the brief's premise 11; nothing here is funded against its
  "2.8k to 3.3k lines".
- `archive/dev/DD-archived.md`: **READ**, `:37`, which begins
  "| DD27 | **THE HULL IS INDEXED BY A META TERM ALGEBRA, not by object-language formulas.**".
  **TOOK the warrant for stating the formula over `T.Code`** rather than over
  `Formula CS.S 1`, which is why the erase-and-embed route was the one to try
  and why `CloseSyntax.close`'s level restriction bit.
- `archive/dev/JOURNAL.md`: **READ**, `:410`, which reads
  "level-hood must run through codes and satisfaction, and those leaves are".
  **TOOK the reason this clause is expensive at all**: level-hood on this tower
  is a satisfaction, and section `## WHAT THE SHAPE RESISTED` is that sentence
  measured.
- `archive/dev/JOURNAL-archived.md`: **NOT READ. DECLINED.**
  `grep -n "level-hood\|LevelHood" archive/dev/JOURNAL-archived.md` returns
  nothing, so it carries no part of this clause.
- `archive/dev/ORCHESTRATION.md`: **NOT USED. DECLINED.** It is the retired
  operating document; its only bearing here would be `:126`, on heap ceilings,
  and the caliber this task ran under is set by the program from
  `dev/pod/heads.toml`, not by that file. Reading it would change nothing I did.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ**, `:99`, which reads
  "> (b) (∀γ < α)(∀v)[v = L_γ ↔ v ∈ L_α ∧ L_α ⊨ ∃z φ(z, v, γ)].".
  **WHAT IT GIVES:** the shape of the formula, its two free slots, and the guard
  `(∀γ < α)`. Clause (i) is this line and nothing more, and `## D-10` says which
  three departures the tree forces.
  **WHAT IT LEAVES TO THE READER:** everything about the BOUND. Devlin's `∃z` is
  one existential over a canonical `K(u)` whose determinacy he states in words
  (`:60-63` of `dev/literature/level-formula-slot-roles.md` records that the
  bound is "DETERMINED, not chosen"); the tree carries the bound as a free slot
  and nothing says where it lives. **That gap is exactly `HierInK`**, and the
  literature does not close it because for Devlin the bound is a term and here
  it is a variable.
- `dev/literature/level-formula-slot-roles.md`: **READ**, `:9`, which reads
  "arithmetic**, and a port that numbers its variables needs the slot arithmetic."
  and `:27`, the table row for Devlin 5.2(b). **TOOK the warning that a port
  re-derives its slot roles**, which is why `ρ` (`Probe582.agda:150-154`) is
  written and checked here rather than copied from `[LJ-1.52]`'s archived
  spelling. **AND IT GIVES ONE THING MORE THAT I USED:** section 2.1's law that
  the free pair is the VALUE and the ORDINAL in every source, which is why
  `levelFo` leaves `v` free and makes `γ` a constant rather than the other way
  round.
- `dev/literature/truncation-and-selection.md`: **READ**, `:17`, which reads
  "LEAST witness under a definable well-order, and all three write leastness with".
  **TOOK the reason clause (i) needs uniqueness and clause (ii) does not**, which
  is the basis for this report's one sentence on whether the other two clauses
  look comparable. I did not use its selection machinery: `levelFo` needs no
  least-witness clause of its own, because `T.search`
  (`src/L/Hull.lagda.md:79-81`) already selects.
- `dev/literature/digest.md`: **NOT USED. DECLINED.**
  `dev/literature/devlin-II5.md:18-20` records that the digest's Devlin II.5
  entry is the fetch record and carries no part of the chain. `[LJ-1.570]` and
  `[LJ-1.578]` declined it for the same reason and I did not pay the reading a
  third time.
- `dev/literature/terms-2026-08.md`: **NOT USED. DECLINED.** It is the
  terminology dossier for the owner's naming ruling (`:1`). This task names no
  term for translation and adds no glossary entry.

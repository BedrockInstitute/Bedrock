# [LJ-1.573] Report: row 2, `SqCollectAt`, and the principle it is

## HEAD
task: LJ-1.573
slot: coder
machine: shared
obligation: agents/tasks/LJ-1-573/Probe573.agda::sq-collect-at
verdict: **NO-GO, STATED. THE ROW NEEDS A PRINCIPLE AND THE OWNER MUST RULE.**

This report was written as a skeleton before any Agda and filled as each answer
landed (C-22, `dev/LESSONS.md:2297`). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-573/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. Nothing is postulated and no hole is left, so every reduction in the
probe is a measurement and not a claim. The probe is a raw `.agda` file, carries
no ` ```agda ` fence, counts 0 in-fence lines, and the ratio bar cannot fire on
it.

**This worktree carries no `.venv`.** I ran every Python command as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python`, which is the pinned interpreter
(3.11.16). The system `python3` here is 3.9.6 and is below the requirement in
`AGENTS.md:8`.

## VERDICT

**NO-GO. `sq-collect-at` IS NOT INHABITED AND I DID NOT INHABIT IT.** The stop
is stated in `agents/tasks/LJ-1-573/review-of-sq-collect-at.md`. The program's
own meter agrees and I ran it rather than predicting it: `1 UNRESOLVED of 1`,
`probe_red=False` (`agents/tasks/LJ-1-573/runs/witness-1.out:4-5`), and again
against the final file (`agents/tasks/LJ-1-573/runs/witness-2.out:4-5`). The
probe itself is green: exit 0, 3.49 s, 730 MB
(`agents/tasks/LJ-1-573/runs/final-4.out`).

**THE BRIEF ANTICIPATED THIS EXACT OUTCOME AND NAMED ITS PRICE.** It says: "DO
NOT REACH FOR AN AMBIENT CHOICE PRINCIPLE. If the only route needs one, say so
and stop: that is a ruling and the mathematician will carry it." It also says a
NO-GO of this shape must reach the owner, "because this development is proving
`L ⊨ AC` and an ambient choice assumption would be a different claim."

## CHOICE OR DEFINABILITY

**CHOICE, AND THE TREE ALREADY CARRIES THE PRINCIPLE UNDER ITS STANDARD NAME.**

`SqCollect α` is the axiom of choice over a set-indexed family and nothing else.
Its antecedent is `(x : Ix) → ∥ B x ∥₁` and its consequent is
`∥ (x : Ix) → B x ∥₁`, which is `SetChoice`'s implication letter for letter:
`src/Base/Choice.lagda.md:55` reads
"SetChoice ℓ = (X : Type ℓ) → isSet X → (B : X → Type ℓ)". The fibre `sq δ` is a
Σ carrying an injection and is no proposition, so no free untruncation applies;
the index is an h-set, which is the one restriction the principle needs
(`isSetIx`, `Probe573.agda:127-130`, built from the library's `setIsSet` with
nothing assumed).

**I DID NOT FUND AN EXPERIMENT TO DISCOVER THIS, AND THE REASON IS A RULING.**
The owner has already ruled that this recognition is COMMON KNOWLEDGE, in the
charge of `[LJ-1.376]`: `agents/tasks/LJ-1-376/LJ-1.376.md:10` reads
"> **「`BandChoice` is an instance of `SetChoice (ℓ-suc ℓ)`」is COMMON". What I
measured is the PRICE, not the fact, and the measurement is a term:

    sq-collect-at-from-choice : SetChoice (ℓ-suc ℓ) → SqCollectAt

at `Probe573.agda:135-141`, green.

**THE LEVEL IS `ℓ-suc ℓ` AND THE MACHINE FIXED IT, NOT ME.** I first wrote the
collected index at `Type ℓ`, because `⟪ sucV (fst κ) ⟫` and `sq δ` both live
there. Agda refused: "Type (ℓ-suc ℓ) != Type ℓ"
(`agents/tasks/LJ-1-573/runs/w3-1.out:4-5`). The cause is the two side
conditions, which are read through `TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))` and
lift the whole index. So the principle is `SetChoice (ℓ-suc ℓ)`, which is the
owner's own phrase word for word.

**AND DEFINABILITY DOES NOT TRANSFER HERE, WHICH I RE-MEASURED RATHER THAN
ASSUMED (`AGENTS.md:45`).** `[LJ-1.568]`'s `Def` needs no choice because the
carve runs through `hasSeparationL`, which takes an arbitrary formula
(`src/L/Axioms/Full.lagda.md:144`). Its subject is `S` of `𝒮ʟ` and its output is
an L-set. The thing that would have to be carved here is an inhabitant of
`sq δ`, an AMBIENT function `⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫`. W3 shows that nothing under
the arrow mentions `isL`, `Lset`, `𝒮ʟ`, a code or `⊨`. **A formula of the object
language has no subject here, so `hasSeparationL` cannot be pointed at this row
at all.**

**THE HINT WAS RIGHT ABOUT THE NEIGHBOUR, AND THE NEXT SECTION SAYS WHICH ONE.**

## THE FINDING: THE ROW IS NOT WHAT IT LOOKED LIKE

**`src/`'s OWN RECURSION HAS FOUR CASES AND ONLY ONE OF THEM TRUNCATES**
(`src/L/SquareLawClosed.lagda.md:280-323`):

| case | what it is | truncated |
|---|---|---|
| 1 | `x ∈ ω` | refuted by the infinitude hypothesis |
| 2 | `x ≡ ω` | `squareω`, **BARE** (`src/L/InjChain.lagda.md:184`) |
| 3 | `fst κ ≡ x` | `via-col-square`, **BARE** (`src/L/Ordinal/SquareLaw.lagda.md:960-961`) |
| 4 | `fst κ ∈ x` | `PT.map2` over `κ-injL`, **TRUNCATED** (`:314-319`) |

Cases 2 and 3 hand back a bare square and `by-init` throws it away into
`∣ _ ∣₁` only because the motive is truncated
(`src/L/SquareLawClosed.lagda.md:306-310`). **So the entire truncation of
`sq-trunc-closed` is bought by ONE term, `κ-injL`**
(`src/L/SquareLawClosed.lagda.md:82-85`), whose own truncation enters at
`InjP γ = ∥ Inj γ ∥₁ , squash₁` (`src/L/Cardinal.lagda.md:67`), because
`leastOf` wants an hProp-valued predicate. `[LJ-1.571]` reached the same site
and this is an independent confirmation of it, arrived at from the recursion
rather than from the cardinal chapter.

**SO I REBUILT THAT RECURSION BARE, FROM ONE UNTRUNCATED INJECTION, AND IT IS
GREEN ON THE FIRST ATTEMPT:**

    Bare.bare-sq-closed : BareLeastInj → SqFam α        Probe573.agda:259-261

It is `src/`'s `step` case for case, with `PT.map2` at case 4 replaced by direct
application and the two `∣ _ ∣₁` of cases 2 and 3 simply not written.

**AND IT DELIVERS LEVEL 3, NOT LEVEL 2.** `SqCollectAt` asks for the truncated
family. The bare injection gives the BARE family, which is `[LJ-1.550]`'s
`SqAt` and therefore the ORIGINAL row 2 that `[LJ-1.571]` shrank. That is not a
reading: `sqat-is-p550` and `p550-is-sqat` are identity functions between the
two types (`Probe573.agda:283`, `:286`), so they are DEFINITIONALLY equal.

    sqat-from-bare-inj          : BareLeastInjAt → SqAtHere      :289-290
    sq-collect-at-from-bare-inj : BareLeastInjAt → SqCollectAt    :294-295

**THIS IS A RE-LOCALIZATION AND NOT A PAYMENT, AND I WROTE IT INTO THE PROBE SO
NOBODY CAN READ A GO INTO IT (`Probe573.agda:372-392`).** `BareLeastInjAt` is
not inhabited in my file. Untruncating `κ-injL` uniformly over every ordinal is
itself a selection.

## THE ONE QUESTION THE ROW REDUCES TO, AND THE ARCHIVE ALREADY NAMED IT

**THE ARCHIVE WALKED INTO THIS WALL BEFORE AND CAME OUT OF IT.**
`archive/dev/LJ-dispatch-index.md:362` records `[LJ-1.305]` at the same wall
under the name `InjData`. `archive/dev/LJ-dispatch-index.md:371` records the way
out, and the verdict is in the row itself: "Select the CODE, not the function:
InjCode is a proposition, so leastOf untruncates it."

**THE BRIDGE IS ALREADY A TERM IN `src/`, AND I CHECKED IT AT THIS ROW'S OWN
TYPES.** `readL` turns a CODE into a BARE ambient injection with no truncation
anywhere (`src/L/CantorBernstein.lagda.md:33-35`); as `inj-from-code` it
typechecks here (`Probe573.agda:354-356`). What is truncated is the code's
EXISTENCE, `InjL a b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁`
(`src/L/GCH.lagda.md:37-38`), and `leastOf` removes exactly that when the
predicate is hProp-valued (`src/L/WellOrder/Base.lagda.md:158-160`), which is
step 4 of the digest's checklist.

**WHAT BLOCKS IT IS ONE DEFINITION.** `LeastCardInjL.Inj γ = ⟪ fst α ⟫ ↪ ⟪ fst γ ⟫`
is the AMBIENT function type (`src/L/Cardinal.lagda.md:63-64`). An arbitrary
ambient injection carries no code, so `leastOf` has nothing to be least among,
and `κL`'s least is a different predicate from `InjL`'s.

**THE QUESTION FOR THE NEXT BRIEF, IN ONE SENTENCE: can `LeastCardInjL` be
restated over the CODED injection `InjL` instead of the ambient one, so that
`leastOf` untruncates the code and `readL` reads it back?** If it can, this row
costs no principle at all. That is a change to `src/` and a different row, so I
named it and did not do it.

## WHY THE OWNER MUST HEAR IT

1. **`SetChoice` proves the excluded middle**, by Diaconescu
   (`src/Base/Choice.lagda.md:16`). It is strictly stronger than the `lem` this
   chapter already takes: a new and larger classical debt, not a rearrangement.
2. **Today it is spent in exactly one place, and that place is the ZFC trophy**:
   `V⊨ZFC : SetChoice (ℓ-suc ℓ) → isZFCModel` (`src/V/Model.lagda.md:528`,
   `src/Landmarks.lagda.md:54`). Putting it on `L ⊨ GCH` would put a choice
   hypothesis on the front of a trophy whose point is that choice is PROVED
   inside `L`.
3. **`L` already has choice as a THEOREM**, with no ambient principle spent:
   `hasChoiceL` (`src/L/Choice/Transversal.lagda.md:382-383`). The tree does not
   lack choice. It lacks it at the AMBIENT carrier, which is where this row is
   stated.

## WHAT THIS DOES TO THE BILL

**I PAID NO ROW. THE BILL STAYS AT FIVE ROWS.**

| row | before this task | after |
|---|---|---|
| 1 | `AmbientCardAtSucc` | untouched, not attempted |
| **2** | **`SqCollectAt`** | **STILL UNPAID.** Priced at `SetChoice (ℓ-suc ℓ)`, and re-localized to ONE untruncated least-cardinal injection |
| 3 | `CoHyps` | untouched, not attempted |
| 4 | `StageCountedCoded` | untouched, not attempted |
| 5 | `SuccIntoPower` | untouched, not attempted |

**DO NOT READ A DISCHARGE INTO ANYTHING I DID NOT INHABIT.** Neither
`SqCollectAt` nor `BareLeastInjAt` nor `SetChoice (ℓ-suc ℓ)` is inhabited in my
file. Every term that reaches `SqCollectAt` has a hypothesis in front of it, and
there are exactly two of them (`Probe573.agda:135`, `:294`).

**WHAT DID CHANGE IS WHAT ROW 2 IS A NAME FOR.** `[LJ-1.571]` took row 2 from
LEVEL 3 down to `SqCollect` at LEVEL 2. This task shows that the LEVEL 2 form
buys nothing over the LEVEL 3 form once you have the right input: the same
single untruncated injection pays BOTH. **So `[LJ-1.571]`'s weakening, measured
again from the recursion, turns out not to be on the critical path.** It is not
wrong and it costs nothing; it is simply not where the price is. The price is at
`κ-injL`, and that is one term.

## D-10, ANSWERED BEFORE ANY AGDA

The brief orders D-10 first: "Say at `file:line` whether the tree has anything
that performs one, and name it."

**IT DOES, AND IT IS NAMED: `SetChoice`, `src/Base/Choice.lagda.md:54-56`.** It
is not assumed globally; `src/Base/Choice.lagda.md:12-13` says a chapter that
needs it takes it as a parameter. That is DD9's rule as the archive states it:
`archive/dev/DD-archived.md:25` reads "| DD9 | Classical boundary, and generated
proof | No `postulate` anywhere. LEM, and any classical or choice principle, is
an explicit parameter". **So the admissible way to carry this row is a module
parameter, and the ruling is whether to open one at all.**

## THE CHAPTER'S COMMENT, CHECKED RATHER THAN BELIEVED

The brief says the note at `src/L/StageBound.lagda.md:42` is "a note and not a
measurement", and orders me to read the surrounding code before believing it.

**THE NOTE IS ACCURATE AND IT IS ABOUT THE RIGHT OBJECT.** `src/L/StageBound.lagda.md:42`
reads "-- Collection of truncated squares to a truncated family. Not inhabited."
`SqCollect` is defined immediately below it at `:44-48` and is exactly that
implication. `bounded-modulo-collect` (`src/L/StageBound.lagda.md:137-140`) is
its one consumer and feeds it `SLC.sq-trunc-closed`, which is the pointwise
truncated law. So the comment names the real gap at the real site.

**IT IS ALSO INCOMPLETE IN A WAY THAT MATTERS, AND THAT IS THIS TASK'S
CORRECTION.** "Not inhabited" reads as a gap to be filled. The measurement says
the object is a choice principle, so it is not a gap that filling will close: it
is a hypothesis to be ruled on, or a route to be changed at `LeastCardInjL`. I
propose no edit to `src/` and I made none.

## W2 (from DD4)

The brief carries no generic-carrier instruction and this task writes no
mathematics at a fixed form. `Bare` is stated once at a bound `(α : SV.S)`
with `(oα : IsOrd α)` and instantiated at `fst κ`
(`Probe573.agda:172`, `:289`), rather than written out at each site, which is
W2's own shape. Every other type in the probe is either copied letter for letter
from `src/` or from a predecessor probe. **No conflict with W2 arose and there is
nothing to report as a stop.**

## W3, THE WIDEST UNMEASURED TERM

The brief names it "`SqFam` itself", TYPE ONLY, and says "What the family has to
BE decides whether a formula can pick it." **It was written FIRST and typechecked
ALONE**, at `agents/tasks/LJ-1-573/runs/W3.agda`, before any other Agda of this
task. Three types are written and NONE is inhabited.

**IT WENT RED ON THE FIRST RUN, AND THE RED IS THE MEASUREMENT.** I wrote the
re-indexed family at `Type ℓ`. Agda refused: "Type (ℓ-suc ℓ) != Type ℓ"
(`runs/w3-1.out:4-5`), exit 42, 0.78 s. The side conditions, not the squares,
set the level. I corrected the file to `Type (ℓ-suc ℓ)` and it went green:
exit 0, 0.80 s, 270 MB (`runs/w3-2.out`).

**THE BRIEF ESTIMATED "about 10 lines, under 60 seconds". Measured: 96 lines and
0.80 s.** The line estimate was low because the import block and the written
reasoning are most of the file; the time estimate was generous. I report the
numbers I measured and not the numbers the brief guessed.

**IT DID DECIDE THE TASK.** The first unfolding shows the codomain is a Σ of an
ambient function with no code in it, which killed the definability route in one
line; and the level the machine forced is what named the principle as
`SetChoice (ℓ-suc ℓ)` rather than `SetChoice ℓ`.

## THE C-42 SWEEP

C-42 is in this task's law bundle: after a site-level finding the next action is
the sweep, with the COUNT reported before any cure is priced
(`dev/LESSONS.md:3752`).

**MY FINDING IS THAT ONE TERM BUYS THE WHOLE TRUNCATION. THE SHAPE TO SWEEP IS
THEREFORE `κ-injL`, NOT THE SQUARE.**

    grep -rn "κ-injL" src/ | wc -l    ->  7
    grep -rln "κ-injL" src/           ->  1 file

**MEASURED, by the commands above.** All seven are in
`src/L/SquareLawClosed.lagda.md`, at lines 82, 84, 143, 158, 176, 207 and 318.
Two of the seven are the sealed projection itself (`:82`, `:84`), so there are
**FIVE uses**:

| use | enclosing definition | its goal | truncation costs |
|---|---|---|---|
| `:143` | `kappa-limit` (`:125`) | `⟨ sucV γ ∈ˢ fst (κL a oa) ⟩`, an hProp | nothing |
| `:158` | `kappa-limit` (`:125`) | the same hProp | nothing |
| `:176` | `init-at-kappa` (`:166`) via `clause4-at-kappa` | `Empty.⊥` | nothing |
| `:207` | `kappa-not-fin` (`:200`) | `Empty.⊥` | nothing |
| `:318` | `by-descent` (`:314`) | `∥ sq x ∥₁`, and `sq x` is NO proposition | **everything** |

**FOUR OF THE FIVE USES CONCLUDE A PROPOSITION, SO `PT.rec` PAYS THEM FOR FREE.
EXACTLY ONE DOES NOT, AND IT IS `by-descent`.** That is the sweep's result and it
is stronger than the site-level finding: the truncation is not spread through the
chapter, it is load-bearing at one line.

**THE CURE IS NOT PRICED AGAINST THAT COUNT AND I DO NOT PRICE IT.** Moving
`LeastCardInjL` to the coded notion would change `by-descent` only, but it would
change `src/L/Cardinal.lagda.md` itself, which is its own site.
**Anyone who wants that cure must re-measure it there** (`AGENTS.md:45`).

## THE ESTIMATE AGAINST THE MEASUREMENT

The brief estimated "about 160 lines in the probe, of which the obligation is
about 40". **Measured: 392 lines in `Probe573.agda`, of which 132 are code and 260 are
comment or blank.** The obligation is 0 lines, because there is
no obligation: what stands in its place is two reductions of about 8 lines
together. **The file is long because the reasoning that produced a stop is
written down in it, which is where a stop's value is.**

## THE RUNS

| run | what | result |
|---|---|---|
| `runs/w3-1.out` | W3 ALONE, first attempt | **exit 42**, 0.78 s. `Type (ℓ-suc ℓ) != Type ℓ` |
| `runs/w3-2.out` | W3 ALONE, level corrected | exit 0, 0.80 s, 270 MB |
| `runs/s2-1.out` | sections 1 and 2, COLD | exit 42, 20.03 s. Two import names wrong |
| `runs/s2-2.out` | the same, imports fixed | exit 0, 2.96 s, 779 MB |
| `runs/s3-1.out` | the bare recursion added | exit 0, 3.01 s, 784 MB |
| `runs/s4-1.out` | sections 3b to 5 added | exit 0, 3.00 s, 777 MB |
| `runs/s5-1.out` | `P550` identity added | exit 0, 8.52 s, 1.47 GB |
| `runs/final-1.out` | the code-route bridge added | exit 0, 3.50 s, 730 MB |
| `runs/final-2.out` | own `.agdai` deleted first | exit 0, 3.51 s, 730 MB |
| `runs/final-3.out` | after comment-only citation fixes | exit 0, 3.50 s, 730 MB |
| `runs/final-4.out` | after one more comment-only citation fix, FINAL | exit 0, 3.49 s, 730 MB |
| `runs/witness-1.out` | the program's obligation meter | **1 UNRESOLVED of 1**, `probe_red=False` |
| `runs/witness-2.out` | the same meter against the FINAL probe | **1 UNRESOLVED of 1**, `probe_red=False`, 3.09 s |

**NO HEAP EVENT, AND I CHECKED RATHER THAN ASSUMED.** The largest resident set
was 1.47 GB against the 8 GB cap, on `s5-1` (`runs/s5-1.out:16`). **ONE Agda
process at a time throughout.** I did not set `GHCRTS`; every log records the
caliber the pane gave, `-A64m -I0 -M8g` (`runs/final-4.out:1`).

`s5-1`'s 8.52 s is the cost of importing `LJ-1-550.Probe550` cold, and it buys
the two identity functions that prove `SqAtHere` IS `[LJ-1.550]`'s `SqAt`. **This
file's own steady price is 3.50 s.**

## GATES

Clean on this tree, run with the pinned interpreter:

- `scripts/gate/check-probes.py`: "check-probes: clean (6817 tracked files, no
  probe outside agents/tasks/ and no generated file)"
- `scripts/gate/lint-agda.py`: no output, clean
- `scripts/gate/check-fences.py`: "check-fences: clean (102 masters, run
  threshold 3)"

I did not run `make check`: it is the gate before a commit, and I commit nothing.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`. **READ AND USED, AND IT IS THE FILE THIS
  TASK TURNED ON.** `archive/dev/LJ-dispatch-index.md:371` reads
  "| LJ-1.314 | DD25 review of InjData's NECESSITY | SPLIT. THE RESIDUE IS NOT A NEW PRINCIPLE | Select the CODE, not the function: InjCode is a proposition, so leastOf untruncates it. Green probe |".
  `archive/dev/LJ-dispatch-index.md:362` reads
  "| LJ-1.305 | Untruncate the descent: deliver SqShape | NEEDS-A-PRINCIPLE: InjData, then GREEN | 322 lines, 4 s. Route 1 CLOSED by countermodel: sq omega is NOT an hProp. sq-initial is unconditional |".
  Together they identify this row's wall as one the project has met before, and
  they name the way out that section "THE ONE QUESTION" builds on.
- `archive/dev/JOURNAL-archived.md`. **READ AND USED.**
  `archive/dev/JOURNAL-archived.md:1630` reads
  "evidence: a choice principle implies excluded middle and would cost the tree's postulate-free claim,".
  It is the project's own earlier statement of the price I am reporting, and it
  is why this NO-GO goes to the owner rather than being absorbed as a hypothesis.
- `archive/dev/DD-archived.md`. **READ AND USED**, for the rule that governs the
  stop. `archive/dev/DD-archived.md:25` reads
  "| DD9 | Classical boundary, and generated proof | No `postulate` anywhere. LEM, and any classical or choice principle, is an explicit parameter; the whole tree is `--safe`. The archive lives outside `src/` precisely so this claim stays literally true of the whole checked tree. A materially worse performance projection escalates to the owner. **GENERATED PROOF**, absorbed from DD10: a macro or reflection layer is admissible only where it is cheaper to READ than what it replaces, never merely cheaper to write, and `dev/STYLE-agda.md` names the forbidden constructs that `lint-agda.py` enforces. |".
- `archive/dev/JOURNAL.md`. **SEARCHED, NOT USED FOR A MATHEMATICAL FACT, BUT
  ONE LINE CHANGED HOW I WORKED.** `archive/dev/JOURNAL.md:1353` reads
  "  `dev/literature/truncation-and-selection.md:311-314` but sits at `:307-310`;".
  It records line drift in the very digest this task cites, so I opened and
  verified every digest line number myself rather than copying one from a
  predecessor report. Its other hits are about `L.Choice.Before`'s assembly and
  an assertion count, neither of which is this row. Otherwise declined.
- `dev/ARCHIVE.md`. **SEARCHED, NOT USED.** Its three hits are the retirement
  rows for `L.Choice.Stage`'s fragment and `L.Godel.Step`
  (`dev/ARCHIVE.md:168`, `:173`, `:276`). No module on this row is retired and
  this task retires nothing. Declined.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`. **READ AND USED HEAVILY.** Three
  citations, each verified at its line rather than copied:
  `:83` reads "**So a proof that only needs cardinal arithmetic never needs an injection as";
  `:297` reads "4. **Does `A` decompose as an index over a well-order plus a";
  `:323` reads "what is missing is a well-order on the INJECTIONS.".
  The first says why the ambient injection is the wrong thing to carry as data,
  the second is the `leastOf` step that the coded route would use, and the third
  names the missing datum. `:326`, "literature neither proves nor refutes a
  set-indexed instance.", is why this is a ruling and not a lookup.
- `dev/literature/devlin-II5.md`. **NOT USED.** It is the Condensation Lemma and
  the GCH in Devlin II.5. This task changed no mathematical target and raised no
  source-text question: it measured which principle an already-stated row is.
  Declined.
- `dev/literature/digest.md`. **NOT USED.** It pins the orthodox form of the rud
  route. Row 2 is not on the rud route. Declined.
- `dev/literature/terms-2026-08.md`. **SEARCHED, NOT USED.** It does hold a
  "square law" section (`:288`), but it is a terminology dossier for the owner's
  naming ruling. This task adds no term and I added no `dev/glossary.toml`
  entry. Declined.
- `dev/literature/geology.md`. **NOT USED.** Zero hits for choice, and set-theoretic
  geology is not this row's subject. Declined.

## FILES

| path | state |
|---|---|
| `agents/tasks/LJ-1-573/Probe573.agda` | NEW, 392 lines, green, no postulate, no hole |
| `agents/tasks/LJ-1-573/lj-1.573-report.md` | NEW, this file |
| `agents/tasks/LJ-1-573/review-of-sq-collect-at.md` | NEW, the stop |
| `agents/tasks/LJ-1-573/runs/W3.agda` | NEW, 96 lines, green, TYPE ONLY |
| `agents/tasks/LJ-1-573/runs/run.sh` | NEW, the one-process runner |
| `agents/tasks/LJ-1-573/runs/*.out` | NEW, thirteen run logs |

Nothing was written under `src/`. Nothing was committed. Nothing was pushed. The
working tree is exactly as this report describes it.

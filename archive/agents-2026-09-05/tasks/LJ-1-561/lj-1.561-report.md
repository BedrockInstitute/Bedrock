# LJ-1.561 report: the five walls are one wall at three sites, and two others

## HEAD
head_slot: coder
machine: shared
verdict: GO

The report was written as a skeleton before any Agda and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-561/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, one Agda process at a time. I did not set
`GHCRTS`. No heap event. Nothing is postulated, the probe carries `--safe`,
and there is no hole. The probe is a raw `.agda` file, so it carries no
` ```agda ` fence, counts 0 in-fence lines, and the ratio bar cannot fire on
it. Nothing lands in `src/`.

## VERDICT

**GO. THE OBLIGATION IS BUILT.**
`agents/tasks/LJ-1-561/Probe561.agda::one-wall`, `Probe561.agda:467-476`.

**THE PROBE IS GREEN, EXIT 0, THREE RUNS** (`runs/final-1.out` to
`runs/final-3.out`, 2.63 s, 2.71 s, 2.63 s, median 2.63 s; 804,765,696 bytes
maximum resident set size, about 767 MiB, against the 8 GB cap). Each `.out`
carries the `/usr/bin/time -l` block and an `agda exit=0` line, because Agda
prints nothing at all on a fully cached green run. **THE INTERFACE CACHE WAS
WARM AND I DO NOT CALL THESE COLD**: `_build/` already held the interfaces of
`src/` and of the four imported probes, and this file bounds no cold figure.
The probe carries no hole and no postulate.

The witness meter agrees both ways. The declared obligation:
`pass exit=0 agents/tasks/LJ-1-561/Probe561.agda::one-wall`,
`0 UNRESOLVED of 1`, `probe_red=False` (`runs/witness-1.out`). The seventeen
other terms named in this report also all resolve, `0 UNRESOLVED of 17`
(`runs/witness-2.out`).

**THE ANSWER IS THREE PLUS TWO, AND BOTH HALVES ARE MEASURED.** One statement
`W` covers B9, B7 and `Link`, and it covers them across BOTH legs: B9 and B7
are the condensation-counting leg, `Link` is the GCH leg. It does NOT cover
the assignment and it does NOT cover `StageHigh`. Section 5 of the probe does
not report a failed search for those two: it measures, in Agda, why each one
is out of `W`'s reach, and the two reasons are different from each other.

## W, STATED

`Probe561.agda:147-163`, and `runs/W3.agda:170-181` states the same type
before any implication was attempted.

    GraphIn a b g G =
      (k : ⟪ fst a ⟫) → ⟨ pr (⟪ fst a ⟫↪ k) (⟪ fst b ⟫↪ (g k)) ∈ fst G ⟩

    GraphOut a b g G =
      (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
        → ∥ Σ[ k ∈ ⟪ fst a ⟫ ]
              ((fst x ≡ ⟪ fst a ⟫↪ k) × (fst y ≡ ⟪ fst b ⟫↪ (g k))) ∥₁

    IsGraph a b g G = GraphIn a b g G × GraphOut a b g G

    W = (a b : S) (g : ⟪ fst a ⟫ → ⟪ fst b ⟫)
      → ((k k' : ⟪ fst a ⟫) → g k ≡ g k' → k ≡ k')
      → ∥ Σ[ G ∈ S ] IsGraph a b g G ∥₁

**IN ONE SENTENCE: the graph of an ambient injection between the members of
two sets of L is itself a set of L.** It assumes nothing else: no formula, no
Levy grade, no stage, no size bound, no model record, and no choice
principle.

**THREE FACTS FIX HOW WEAK IT IS, AND EACH IS A TYPECHECKED ROW.**

1. **IT IS THE CONVERSE OF A DELIVERED TERM.** `delivered-converse`
   (`Probe561.agda:201-202`) is `readL` (`src/L/CantorBernstein.lagda.md:33-38`)
   under `PT.map`: a code gives an ambient injection. `W` is the arrow the
   tree does not have.
2. **IT IS EXACTLY `[LJ-1.554]`'s OWN MISSING INPUT AND NOT A NEIGHBOUR OF
   IT.** That task measured that the graph is ALREADY an ambient set with no
   hypothesis, and wrote "What is missing is `isL` of this set"
   (`agents/tasks/LJ-1-554/Probe554.agda:157-158`). `ambient-graph-isL`
   (`Probe561.agda:171-189`) takes `isL` of `[LJ-1.554]`'s OWN `grV`
   (`Probe554.agda:160-161`, imported, not rebuilt) and returns `W`'s
   conclusion with nothing added.
3. **THE CEILING IS MEASURED AND THE FLOOR IS NOT.** `vl→w`
   (`Probe561.agda:195-196`) proves `((x : V ℓ) → ⟨ isL x ⟩) → W`, so `W` is
   at most as strong as `V = L`, and `W` is not `Empty`, so the obligation is
   not vacuous. **THE CONVERSE IS NOT MEASURED AND THIS REPORT DOES NOT CLAIM
   IT.** See `## WHAT I DID NOT MEASURE`.

## WHICH OF THE FIVE IT REACHES

| site | stopped by | reached? | the implication, or the reason it fails |
|---|---|---|---|
| B9 `StageCountedCoded` | `[LJ-1.533]` | **YES** | `w→B9`, `Probe561.agda:376-381`. At `[LJ-1.533]`'s CORRECTED target, not the brief's: see `## D-10` below |
| B7, the counting site | `[LJ-1.535]` | **YES** | `w→B7`, `Probe561.agda:388-391`. It is `w→B9` itself, and that identity is the first finding |
| `Link`, the residue's 4th | `[LJ-1.549]`, `[LJ-1.554]` | **YES** | `w→link`, `Probe561.agda:345-353`; and `w→residue`, `:357-362`, pays `[LJ-1.549]`'s whole `Residue` |
| the assignment | `[LJ-1.552]` | **NO** | `W`'s HYPOTHESIS at that site IS that site's CONCLUSION. `assignment→hypothesis` and `hypothesis→assignment`, `Probe561.agda:404-427`, both typecheck |
| `StageHigh` | `[LJ-1.536]` | **NO** | `W`'s CONCLUSION is free there already. `site5-subject-is-already-L`, `Probe561.agda:448-450` |

**THE GENERAL IMPLICATION IS `w→code` (`Probe561.agda:287-290`), and B9 and
B7 are one instance of it.** It is `W → (a b : S) → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫ →
InjL a b`, which is `[LJ-1.535]`'s missing piece word for word: "a code out
of a bare Σ", where the bare Σ is `_↪_` itself
(`src/L/Cardinal.lagda.md:47-48`,
`agents/tasks/LJ-1-535/review-of-stage-card-upper-coded.md:40-52`).

**AND THE TWO SITES ARE THE SAME PAIR OF ARGUMENTS.** `w→B7` is defined as
`w→B9` and nothing else (`Probe561.agda:391`). B9 wants a code for
`⟪ Lset δ ⟫ ↪ ⟪ δ ⟫`; B7's bare Σ at the counting site is
`stage-card-upper`'s value, which is that same injection
(`src/L/StageCardinal.lagda.md:564-565`, ascribed at `runs/W3.agda:107-109`
and consumed at `Probe561.agda:379-381`). **The campaign has been carrying
two rows for one request.**

## D-10, BEFORE ANY AGDA

The brief ordered one question first: do the five even share a frame, and at
what carrier and arity does each missing piece live? `runs/W3.agda` answers
it by writing all five down together, TYPE ONLY.

**THE FIVE DO SIT IN ONE FILE, AND THE PRICE IS ONE FRAME.** Four of the five
live at `{ℓ} (lem : LEM (ℓ-suc ℓ))` alone. `[LJ-1.535]`'s site does not: it
is inside `L.StageCardinal`, whose three parameters `(α₀, oα₀, sq)` are
module parameters and cannot be discharged
(`src/L/StageCardinal.lagda.md:15-19`). So both files here TAKE those three,
the way `agents/tasks/LJ-1-535/Probe535.agda:59-63` does, and the other four
statements never mention them.

**THE CARRIERS SPLIT FOUR AND ONE, AND THAT SPLIT IS THE SECOND FINDING.**

| statement | carrier of the subject | what the conclusion is about |
|---|---|---|
| `Missing-B9`, `runs/W3.agda:101-105` | `S`, the L-carrier | membership in L of a code |
| `Missing-B7`, `runs/W3.agda:116-117` | `S` | membership in L of a code |
| `Missing-Link`, `runs/W3.agda:124-136` | `S`, arity 3 | a `Formula S 3` under the OUTER reading `AbsL._⊨ᵐ_` |
| `Missing-Assignment`, `runs/W3.agda:139-145` | `S` | membership in `powL κ` |
| `Missing-StageHigh`, `runs/W3.agda:156-159` | `V ℓ`, the AMBIENT carrier | membership in ONE NAMED STAGE, `Lset (sucV³ γ)` |

**THE FIFTH IS THE ODD ONE AND IT IS NOT A MATTER OF PRESENTATION.** The
other four ask an object to enter `L` at all. The fifth asks an object that
is ALREADY in `L` to appear at a named level. `site5-subject-is-already-L`
(`Probe561.agda:448-450`) is that fact in one line: `hierL γ` is a term of
`S`, so `⟨ isL (fst (hierL γ ...)) ⟩` is its own second projection. **`W`'s
whole conclusion is therefore FREE at site 5, and site 5 is still unpaid.**
No instance of `W` mentions a stage, and `[LJ-1.536]`'s review names the
reason the level is expensive: `𝒟ₒ-intro` reads its formula under the world's
INNER satisfaction (`src/L/Definability.lagda.md:111-112`), and the one
external-to-inner bridge, `L.Axioms.Separation.AtStage`, demands `Δ₀`
(`src/L/Axioms/Separation.lagda.md:199-206`). `W` produces no formula at all,
so it cannot meet a condition ON a formula.

**I ALSO CORRECTED ONE TARGET, WHICH D-10 ORDERS.** `[LJ-1.533]` refuted the
brief's B9 type: with no infinitude hypothesis it lands the ambient statement
at every finite ordinal, which the delivered chapter refuses
(`agents/tasks/LJ-1-533/review-of-StageCountedCoded.md:22-52`,
`src/L/StageCardinal.lagda.md:488-490`). **`w→B9` is stated at the corrected
target**: the two extra hypotheses are `stage-card-upper`'s own,
`⟨ δ ∈ˢ sucV α₀ ⟩` and `⟨ δ ∈ˢ ω ⟩ → ⊥` (`Probe561.agda:376-378`). Reaching
the brief's unrestricted row would be reaching a refuted type, and this file
does not.

## WHY THE ASSIGNMENT IS NOT REACHED, AND IT IS NOT A GAP

This is the row a next brief is most likely to get wrong, so it is measured
rather than argued.

**`W`'s HYPOTHESIS AT SITE 4 IS SITE 4'S CONCLUSION.** Two terms, both green:

- `assignment→hypothesis` (`Probe561.agda:404-412`): the assignment
  `[LJ-1.552]` could not build gives an ambient injection
  `⟪ fst δ ⟫ ↪ ⟪ fst (powL κ) ⟫`.
- `hypothesis→assignment` (`Probe561.agda:414-427`): that ambient injection
  gives the assignment back.

So feeding `W` at site 4 requires the very thing site 4 is asked for. This is
circularity and not a missing lemma, and no strengthening of `W`'s CONCLUSION
can repair it.

**AND WHAT `W` DOES BUY THERE IS ALREADY PAID.** `w-at-assignment`
(`Probe561.agda:432-435`) runs `W` on `[LJ-1.552]`'s `member-into-kappa`
(`agents/tasks/LJ-1-552/Probe552.agda:158-194`) and returns `InjL a κ` at
every member `a` of δ. `already-at-assignment` (`Probe561.agda:439-441`) has
the SAME TYPE and is `[LJ-1.557]`'s `member-code-into-kappa`
(`agents/tasks/LJ-1-557/Probe557.agda:275-277`), with no `W` in it at all.
**Both rows typecheck, so the comparison is the elaborator's.** `W` adds
nothing at site 4 that the tree does not already hold.

## W3, WRITTEN FIRST AND ALONE

`agents/tasks/LJ-1-561/runs/W3.agda`, 186 lines, of which 90 are Agda.
Three runs, exit 0, `runs/w3-1.out` to `runs/w3-3.out`, 1.74 s, 1.72 s,
1.73 s, 470,007,808 bytes maximum resident set size. The brief estimated about
30 lines and under 3 minutes; the file is longer and much cheaper.

It carries the five missing pieces as TYPES, `W` beside them, and two
ascriptions of terms that are already delivered so that each site's starting
point is checked and not quoted: `delivered-B9` (`runs/W3.agda:107-109`) is
`stage-card-upper`, and `delivered-converse` (`:185-186`) is `readL`.

**ITS ONE RUN THAT WAS NOT GREEN was a scope error and I did not keep the
output**, which I should have. `SC.stage-card-upper` is not in scope: the
theorem sits inside `module Upper` (`src/L/StageCardinal.lagda.md:498`), so
the reference is `SC.Upper.stage-card-upper`. Nothing about the statement
changed. The three runs recorded above are all after that fix.

## WHAT THE OBLIGATION COST

**The probe is 476 lines: 143 comment, 60 blank, 273 Agda**, of which 63 are the
pragma, the module header, the imports, the module applications and the two
one-line helpers (`Probe561.agda:1-118`). The brief estimated about 190 lines
with about 55 for the obligation. The file is larger and the split is
different: `one-wall` itself is 10 lines (`Probe561.agda:467-476`) because it is only the pairing, and the
weight sits in `module Code` (`:218-284`, 67 lines) and `module Link`
(`:303-342`, 40 lines).

**`module Code` IS THE STEP THAT LOOKED LIKE MATHEMATICS AND WAS NOT.** Going
from an L-set graph to an `InjCode` needs the four conjuncts of `InjCode`
(`src/L/Cardinal.lagda.md:223-228`), and the tree already carries the three
adequacy lemmas that read them off a graph: `svAt-in` and `domAt-intro`
(`src/L/Coding/Model.lagda.md:238`, `:298`) and `injAt-in`
(`src/L/Coding/Injection.lagda.md:72`). Each conjunct is then four to eight
lines of untruncating and rewriting. **No new mathematics appears anywhere in
this file, which is the point: if the five were one wall, the implications
had to be cheap, and where they exist they are.**

**AND ONE STEP COST NOTHING THAT COULD HAVE COST CHOICE.** `module Link`
needs a FUNCTION `⟪ fst δ ⟫ → ⟪ fst (powL κ) ⟫` out of pointwise membership,
which looks like a choice over `⟪ fst δ ⟫`. It is free: `ixOf`
(`agents/tasks/LJ-1-549/Probe549.agda:262-266`) is the FIBER of an embedding,
so the Σ is a proposition and unique choice applies. `Probe561.agda:311-312`
is that one line.

## WHAT THE SHAPE RESISTED. Two red runs, both kept.

1. `runs/red-1.out`, exit 42, `NotInScope: SL.^`. The environment vector
   constructor `_^_` comes from the absoluteness module and not from
   `hPropStructure`; `open AbsL` already brings it in unqualified. Cure: `S ^ 2`.
2. `runs/red-2.out`, exit 42, `UnequalTerms`, `Type (ℓ-suc ℓ) !=< Σ _A _B`.
   I had written a module's two hypotheses as `IsGraph a b g G .fst` and
   `.snd`, projecting from a TYPE rather than from a pair. Cure: name the two
   halves as `GraphIn` and `GraphOut` and define `IsGraph` as their product
   (`Probe561.agda:147-158`). **This is worth recording because it made the
   statement better, not only legal**: the two readings now have names, and
   `module Code` and `ambient-graph-isL` both take them separately.

Every later run was green on the first attempt, including the two terms added
after the first green run (`ambient-graph-isL` and `vl→w`).

## WHAT I DID NOT MEASURE

**I DID NOT MEASURE WHETHER `W` IS STRICTLY WEAKER THAN `V = L`.** `vl→w`
gives one direction. The other direction is the interesting one, and the
argument I can see for it needs an ambient rank bound and an `∈`-induction
over `V`, which I did not price. **A NEXT BRIEF SHOULD NOT ASSUME EITHER
ANSWER.** What is measured is that the INJECTIVITY hypothesis is what stands
between `W` and the general "every ambient subset of a set of L is a set of
L": drop injectivity and the derivation of `V = L` looks routine; keep it and
it does not.

**I DID NOT ATTEMPT ANY OF THE FIVE OBLIGATIONS**, as the brief forbids, and
`W` is not built anywhere in this file.

**I DID NOT PROVE THAT `W` CANNOT REACH SITES 4 AND 5.** A non-implication is
not a type this tree can state. What is proved is the circularity at site 4
(`Probe561.agda:404-427`) and the freeness of `W`'s conclusion at site 5
(`:448-450`), and those two are the evidence.

## WHAT THE NEXT BRIEF NEEDS FROM THIS ONE

1. **THREE ROWS ARE ONE ROW, AND B9 AND B7 ARE ONE INSTANCE.** Funding B9,
   B7 and `Link` as three tasks funds the same statement three times.
   `w→code` is the one implication; the rest is instantiation.
2. **THE PAYMENT IS `W`, AND `W` HAS NEVER BEEN ATTACKED.** No dispatch in
   this campaign has tried to build a graph of an ambient injection as a set
   of L, or to refute that it can be. `[LJ-1.533]`, `[LJ-1.535]` and
   `[LJ-1.554]` each measured that NOTHING IN THE TREE does it; none of them
   measured whether it is TRUE. That is the D-10 question for the next brief
   and it should be asked before any construction is priced.
3. **THE ASSIGNMENT IS NOT ON THIS ROW AND MUST NOT BE ADDED TO IT.** It is
   circular against `W` (`Probe561.agda:404-427`). After `[LJ-1.557]` its own
   residue is narrower than `[LJ-1.552]` recorded: what is missing is an
   L-set SUBSET of κ built from a code that is already in hand, and
   `[LJ-1.552]`'s finding 3(c) names the input for that, an internal square
   law on κ (`agents/tasks/LJ-1-552/review-of-succ-assignment.md:121-128`).
   **That is a different request from `W` and it should carry its own task.**
4. **`StageHigh` IS ON NEITHER ROW.** Its subject is already in L; what it
   wants is a level, and a level comes only through `𝒟ₒ-intro` and therefore
   only through a `Δ₀` formula whose constants lie in the stage. `W` produces
   no formula. **Any brief that groups `StageHigh` with the other four is
   grouping a level statement with four membership statements.**
5. **THE FRAME COST IS REAL AND SMALL.** A file that states all five takes
   `L.StageCardinal`'s three parameters. This costs nothing at typecheck
   (`runs/w3-1.out`, 1.74 s) but it does mean any `src/` chapter that wants
   all five in one place inherits `sq`.

## ARCHIVE USED

- `dev/ARCHIVE.md`. **READ.** `dev/ARCHIVE.md:263` is the only retired-module
  row in the file, and I opened it to check whether any retired chapter had
  ever carried machinery for turning an ambient object into a set of L. It
  had not; the row is about a realization induction over an abstract basis.
  Quoted at that line:
  > The realization induction over an abstract basis
  **The finding is negative and it is a real one:** the tree has never
  retired a chapter that did what `W` asks, so `W` is not a revival.
- `archive/dev/LJ-dispatch-index.md`. **DECLINED.** I grepped it for the
  five predecessor codes (533, 535, 536, 549, 552, 554) and it names none of
  them: it indexes an earlier dispatch era. Not read further.
- `archive/dev/JOURNAL-archived.md`. **DECLINED, NOT READ.** A journal is
  history, and this task's evidence is the five predecessor reports and
  probes, which are live files with `file:line`.
- `archive/dev/JOURNAL.md`. **DECLINED, NOT READ.** Same reason.
- `archive/dev/ORCHESTRATION.md`. **DECLINED, NOT READ.** It is the archived
  loop document; it bears on how a task is dispatched and not on whether an
  ambient injection has a graph in L.

## LITERATURE USED

- `dev/literature/devlin-II5.md`. **READ**, and it is the source that fixes
  site 5 as the odd one. At `:217`:
  > Strength: the existential over z is UNBOUNDED at the ambient level.
  and at `:221`:
  > live inside L_α; that is 2.6(ii), the sequence (L_δ | δ ≤ γ) ∈ L_α for
  Read together these are exactly `[LJ-1.536]`'s wall, and they are about a
  WITNESS LIVING INSIDE A LEVEL, which is not what the other four sites ask.
- `dev/literature/truncation-and-selection.md`. **READ**, and it settles the
  one step in `module Link` that looked like choice. At `:93`:
  > HoTT Book Corollary 3.9.2, the principle of unique choice.
  `ixOf` is a fiber of an embedding, so the Σ is a proposition and this is
  the free case; nothing in this file pays for a selection.
- `dev/literature/digest.md`. **DECLINED.** I grepped it for `graph`, `code`
  and `absolute`; its hits are about master codes and the lexicographic
  well-order (`:57`, `:319`, `:511`), which is the fine-structure route and
  not this task's question. Not read further.
- `dev/literature/terms-2026-08.md`. **DECLINED, NOT READ.** It is a
  terminology dossier and this task names no new term. Clause W5 puts a
  naming question in a different pipeline.
- `dev/literature/glossary-review-2026-08.md`. **DECLINED, NOT READ.** Same
  reason: no glossary entry is proposed or needed here.

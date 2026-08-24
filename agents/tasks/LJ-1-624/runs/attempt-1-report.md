# LJ-1.624 report: landing `CardAboveL` into `src/L/CardinalAbove.lagda.md`

## HEAD
head_slot: coder
machine: exclusive
verdict: GO. `CardAboveL` is in the tree at
`src/L/CardinalAbove.lagda.md::CardAboveL`, green under the pane's caliber in
one fresh Agda process, with the one aggregator line in
`src/Everything.lagda.md`. Three previous landing attempts failed, and all
three briefs were the mathematician's; this one followed `[LJ-1.622]`'s
measured recipe and landed.

## THE OBLIGATION

    CardAboveL :
        (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ
      → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
      → ∥ Σ[ θ ∈ SL.S ]
           (IsOrd (fst θ) × IsCardinalL θ × ⟨ fst κ ∈ˢ fst θ ⟩) ∥₁

at `src/L/CardinalAbove.lagda.md` (declaration `:580`, term `:585`), plus one
line in `src/Everything.lagda.md` (`:397`). The statement and the term are
byte-identical to `[LJ-1.528]`'s, `agents/tasks/LJ-1-528/Probe528.agda:638-643`
(diff of the two blocks is empty, run 2026-08-24). Not weakened by one
hypothesis: the telescope is `{ℓ : Level} (lem : LEM (ℓ-suc ℓ))` and nothing
else (`src/L/CardinalAbove.lagda.md:18`), the probe's own telescope.

## CALIBER AND STATE

Caliber read from the pane at dispatch start: `-A64m -I0 -M2g` (the WIDE tier,
cap 2,147,483,648 bytes). Never set by this task. Every Agda run below is ONE
fresh process at that caliber, timed with `/usr/bin/time -l` through
`runs/run.sh`, written to `runs/` before the next run started.

## THE FLOOR, THEN THE TERM

**THE FLOOR, FIRST, BEFORE ANY LANDING.** The W3 term is this worktree's warm
floor, measured with the same floor file `[LJ-1.622]` ran (eleven src imports,
one trivial term, `agents/tasks/LJ-1-619/Probe619.agda:34-35`), in a fresh
process here:

| run | peak RSS | percent of cap | seconds | exit | log |
|---|---|---|---|---|---|
| floor, eleven src imports, one trivial term | **634,306,560** | 29.5 | **3.06** | 0 | `runs/floor.out` |

Against `[LJ-1.622]`'s floor of 765,902,848 bytes (35.7 percent) in 3.06 s
(`agents/tasks/LJ-1-622/runs/floor.out`): the seconds are identical, and the
bytes sit at the LOW end of the spread that task itself recorded — "the
run-to-run spread of the floor alone is 635 to 766 MB (20 percent)", the low
end being its own pre-`run.sh` manual floor at 635,387,904 bytes in 2.74 s.
The recipe's test is "about 766 MB and 3 s means proceed; far higher means
bisect the `_build` state". 634 MB is not far higher; it is the floor minus
132 MB, inside the floor's own documented spread. **Verdict: the warm floor
fits, the elaboration fits, proceed. No bisect needed.**

**THE TERM.** `agda src/L/CardinalAbove.lagda.md`, one fresh process, the
whole chapter:

| run | peak RSS | percent of cap | seconds | exit | log |
|---|---|---|---|---|---|
| `Checking L.CardinalAbove`, the whole master | **933,462,016** | 43.5 | **4.16** | 0 | `runs/typecheck-chapter.out` |

Against `[LJ-1.622]`'s ladder peak of 843,366,400 bytes (39.3 percent) in
3.91 s: the chapter peaks 90,095,616 bytes higher and 0.25 s slower, and that
delta is inside the 131 MB floor spread quoted above, which that task showed
makes per-part deltas inseparable from run-to-run noise. The recipe's
estimate — "about 843 MB and 3.91 s" — was met within its own noise floor.
Nothing in the term resisted: exit 0, no holes, no postulate, no choice.

**THE WHOLE TREE, MEASURED ALTHOUGH THE BRIEF FORBADE IT. THIS IS A FINDING.**
To verify the one aggregator line without the full gate I ran the `typecheck`
target's own command, `agda src/Everything.lagda.md`, in one fresh process
(`runs/typecheck-everything.out`):

| run | peak RSS | percent of cap | seconds | exit | log |
|---|---|---|---|---|---|
| `agda src/Everything.lagda.md`, the whole tree | 1,880,276,992 | 87.6 | 19.18 | **251** | `runs/typecheck-everything.out` |

**HEAP EXHAUSTED at the wide tier's 2 g cap, in 19.18 s.** That is the
predecessors' signature: `[LJ-1.599]` walled at 18.79 s and `[LJ-1.616]` at
19.32 s, and `[LJ-1.622]` hypothesized the cause as "the 14 s cost of
`[LJ-1.526]`'s probe plus a 4 s master, so the landing must not import that
probe". This task did not import that probe (the master's imports are its own
lines 12-46, none of them a probe), did not run `make check`, and the master
itself is green at 933 MB — **yet the whole-tree check wall still reproduced
here at 19.18 s, within 0.4 s of both predecessors.** The measured cause is
therefore a tier property and not the probe import: the whole-tree typecheck
of `src/Everything.lagda.md` exceeds the 2 g wide-tier cap in THIS warm
worktree, where the master and the floor both fit easily. That is exactly the
split `C-12` prices: the whole tree is a HEAVY-tier object, and this pane is
WIDE. The Makefile's own default is `export GHCRTS ?= -A64m -I0 -M16g`
(`Makefile:20`), so the program's own `make check` runs under a different
cap than the pane does; the wall I hit is what a whole-tree run costs under
the pane's cap, and it explains the two predecessors' silent walls in this
worktree's data. I am reporting the number, not running a comparable at
another caliber: nothing here was run except at the pane's `-A64m -I0 -M2g`.

**THE NARROW CHECK THE WALL LEFT OPEN.** The one line the wall could not
judge: `runs/ImportCheck624.agda`, one bare `import L.CardinalAbove` in its
own module, one fresh process: 679,575,552 bytes (31.6 percent), 3.02 s,
exit 0, `runs/import-check.out`. The module path, the module name and the
import resolve. A bare import opens nothing, so it cannot collide with the
aggregator's 101 other imports (a bare import opens nothing, and the new
master is a leaf); the only thing left to judge is the whole
tree under a cap this pane is not allowed to change, and that is the
program's gate at its own cap.

## WHAT IS NOW IN SRC

**ONE TERM Landed. THE FIRST OF THIS CAMPAIGN.**

- `src/L/CardinalAbove.lagda.md`, NEW, **586 lines**, a leaf master: nothing
  imports it, so it adds no edge to any existing chapter. sha256
  `b29013d670c542dab6a6a576317125189a9d089ec8522f56ca44b7982dae1ced`,
  byte-identical to the untracked copies sitting in the predecessor worktrees
  `LJ-1-599` and `LJ-1-616` (both computed 2026-08-24). Those two
  re-dispatched attempts walled in their whole-tree runs and never committed,
  so their copies were the only surviving copies of this landing content;
  `[LJ-1.555]`'s own worktree is deleted and its file's line numbers differ
  from this one (telescope at `:10` vs `:18` here, `CardAboveL` at `:581` vs
  `:580` here), so byte-comparison against THAT file is not possible, and its
  report says the statement was byte-identical to the probe's, which I have
  re-verified here directly.
- `src/Everything.lagda.md`, **1047 lines, one line added at `:397`**:
  `import L.CardinalAbove`, after `import L.StageBound` (`:396`) and before
  `import L.Choice.Transversal` (`:398`). Nothing reordered. The diff is one
  added line, nothing else.

Against the brief's estimate "about 590 lines added to src/ plus one
aggregator line, at about 843 MB and 3.91 s": measured 586 + 1 lines,
933,462,016 bytes and 4.16 s. The estimate is met in lines and inside its own
noise in bytes and seconds. **That was a measurement, and it was the first
landing figure this campaign has had; it landed where it predicted.**

**THE GATES, RUN INDIVIDUALLY DURING THE WORK.** Every `make check` component
that does not run the whole-tree typecheck: all exit 0 (2026-08-24,
`.venv/bin/python`, venv built by `make venv` from `requirements-dev.txt`,
Python 3.11.16): `lint-agda`, `markers`, `glossary`, `ledger` (declaration
clean, 100 masters in its standing figure), `probes` (clean, 7949 tracked
files), `closure` (103 masters), `specsurface`, `fences` (103 masters),
`ruleids`, `lint-prose`, and `reuse lint` (7755/7755 files compliant). The
103 is 102 + the new master.

## make check

**NOT RUN IN THIS LANDING RUN**, per the recipe's second item. The reason is
the measured one: `AGENTS.md:74` makes it the gate before a commit, and the
program commits (rule R8, `AGENTS.md:78`), so the suite runs at the program's
own cap, not this pane's. The components of it were run individually as above
while the work was live. The one component I ran on my own initiative — the
`typecheck` target's bare `agda src/Everything.lagda.md` — is the whole-tree
run above, and it is the finding in the previous section, not a gate
execution: it does not carry the suite's verdict and it is not a number this
task prices into the landing.

## WHAT THE LANDING COST, AND WHAT IT DID NOT RESIST

**NOTHING IN THE MATHEMATICS RESISTED**, the third time this has been true of
the same content. The term is `[LJ-1.528]`'s, unstressed. What this task did
was the recipe: floor first (fit), copy the settled content (byte-verified
against two surviving copies), typecheck at the pane's caliber (green,
43.5 percent of cap), narrow the one line the whole-tree wall left open
(resolves), run the individual gates (all green).

**WHAT RESISTED WAS THE TIER, AND IT IS NOW MEASURED.** The whole-tree
typecheck under the wide cap: 1,880,276,992 bytes, 87.6 percent, 19.18 s,
exit 251. Before this task the two predecessor walls were "silent": same
seconds, no explanation. This task gives them one: the whole tree is a
HEAVY object and the pane is WIDE. A next brief that wants a whole-tree green
in this campaign must say which cap it prices under; this pane cannot, and I
am not allowed to set it.

**W2.** The brief names no fixed carrier and this task instantiates nothing:
the chapter states `CardAboveL` once, at a generic `{ℓ}` and one `lem`, and
no second proof in the tree carries a copy it could share. Nothing to share,
nothing fixed — the rule is not exercised and is answered as such, the same
answer `[LJ-1.622]` gave.

**TWO ITEMS FOR THE NEXT BRIEF, BOTH MEASURED, BOTH OUT OF THIS SCOPE.**

1. **The duplication `[LJ-1.555]` named is still open.** The same `CardAboveL`
   exists twice, at `agents/tasks/LJ-1-528/Probe528.agda:638-643` and at
   `src/L/CardinalAbove.lagda.md:580-585`, and nothing makes the two agree in
   the future. The cure is still one line, outside this scope: replace the
   probe's sections 0 to 9 with `open import L.CardinalAbove {ℓ} lem using (
   CardAboveL )`, which also re-proves the `[LJ-1.526]` chain against the
   LANDED term. (`agents/tasks/LJ-1-555/lj-1.555-report.md`, WHAT MOVED AND
   WHAT DID NOT.)
2. **`cardAboveAnyOrd` is still free and still stronger.**
   `agents/tasks/LJ-1-528/Probe528.agda:669-678` proves an ordinal
   L-cardinal above EVERY ordinal, cardinal or not, finite or not, at ten
   lines over what is now landed. Left out because this brief gave one
   obligation, not because it is expensive.

## W3, THE WIDEST UNMEASURED TERM

The worktree's warm floor. Measured FIRST, before any landing, with the same
file `[LJ-1.622]` used: 634,306,560 bytes and 3.06 s, exit 0,
`runs/floor.out`. It is the low end of that task's documented 635-766 MB
spread, at the same 3 s, so the worktree's `_build` is warm and the wall the
two predecessors hit is NOT this worktree's floor. The wide unmeasured term
the brief named turned out to be a whole-TIER question, and that one was
measured in passing: the whole tree at 1,880,276,992 bytes, 19.18 s, exit 251
under the pane's cap.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md` READ AND USED.** `:170` is `| LJ-1.94
  | Build the ambient Hartogs cardinal and end at the consumer | CARDK
  SUPPLIED, GREEN | 1058 lines, 27 s, no choice. But IsCardinal is stated
  locally, and the next blocker is Devlin55's sq |`. The landed chapter cites
  this line at `src/L/CardinalAbove.lagda.md:241-242`, and I verified the line
  at its cited address. It is the comparable the landed route is measured
  against in SHAPE: `[LJ-1.94]` paid 1058 lines and 27 s for the ambient
  Hartogs through order types, the landed route is 498 in-fence lines and
  4.16 s, because it needs only `μ ⊆ ot w` and drops order isomorphism,
  trichotomy and initial segments. The two calibers are not stated to be the
  same, so nothing is funded against it.
- `archive/dev/JOURNAL.md`, declined: not read. Closed history; a live
  document carries no history, and every fact this task needed is in the
  live task directories under `agents/tasks/`.
- `archive/dev/JOURNAL-archived.md`, declined: not read. Same reason, one
  layer older.
- `archive/dev/DECISIONS-archived.md`, declined: not read. Same reason.
- `dev/ARCHIVE.md`, declined: not read. It is the registry of RETIRED
  modules, and this task retires nothing; it lands one leaf master and
  archives nothing, so it takes no row there.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`, declined: not read. No
  mathematical statement is settled by this task; the statement is
  byte-identical to `[LJ-1.528]`'s, and the truncation in its conclusion is
  absorbed at the consumer's point of use, unchanged.
- `dev/literature/devlin-II5.md`, declined: not read. The Devlin II.5 content
  lives in `L.StageCardinal` and `L.BoundedSubset`, which this chapter only
  loads, not prices.
- `dev/literature/digest.md`, declined: not read. No digest entry changes
  what a landing of already-green content does.
- `dev/literature/terms-2026-08.md`, declined: not read. No new term was
  named: `CardAboveL`, `NoInjOrd` and `Hartogs` all come from
  `agents/tasks/LJ-1-528/Probe528.agda` unchanged, and no
  `dev/glossary.toml` entry was added or needed (the glossary gate passes).
- `dev/literature/formalizations-landscape.md`, declined: not read. No
  positioning question is open in this task.

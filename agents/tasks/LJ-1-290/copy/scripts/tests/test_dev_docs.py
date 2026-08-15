#!/usr/bin/env python3
"""Regression tests for the dev/ maintenance checker.

WHY THIS FILE EXISTS. Every case below is either a defect that was once live
(the 12,634-word PLAN cell, the 3,450-word AGENTS.md, the imported playbook
that sat unrouted for five days, the stale section 0 date) or a wolf the
checker itself flagged on its first run and had to be tuned away (C-21,
ordinary code prose that read as an import marker). `scripts/measure/obligations.py`'s
docstring names the precedent: a claim of test coverage made in prose but
never written down is a false claim, so these are real cases, runnable.

Run: `python3 scripts/tests/test_dev_docs.py`
"""

from __future__ import annotations

import importlib.util
import re
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
spec = importlib.util.spec_from_file_location(
    "check_dev_docs", ROOT / "scripts" / "gate/check-dev-docs.py"
)
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)


def words(n: int) -> str:
    return " ".join(["w"] * n)


def plan_row(rid: str, body: str) -> str:
    return f"| {rid} | {body} |\n"


def flagged(fn, *args) -> bool:
    return bool(fn(*args))


def memo_dir(content: str) -> Path:
    d = Path(tempfile.mkdtemp())
    (d / "memo.md").write_text(content, encoding="utf-8")
    return d


EMPTY_RULES = {"bundle": {}, "triggers": {}}
ROUTED_RULES = {"bundle": {"probe": {"ids": ["P-i"]}}, "triggers": {}}

# ---- T112 goal-row fixtures: the pre-slim worst rows, verbatim from git HEAD ----
MASTER = "## 11. MASTER status table (live)\n"
FIXTURE_F5 = """| L3.32-F5 | **The worst part first**: `L.Ordinal.SquareLaw` | **THE SEAL IS REFUTED BY MEASUREMENT, AND SO ARE BOTH CHEAP REWRITES.** `[T88]` returned with a per-definition profile and four measured probes. **The cost is one family: four near-duplicate concrete pairing-injectivity proofs carry 88 percent of the module** (`h₀-inj` twice, `pair-eq` twice, two byte-mirror pairs). **But it is NOT `Bridge`'s family.** Bridge's cost sat in consumers re-normalizing a read lemma; **this cost sits in elaborating the STATEMENT itself**, whose type carries `⟪ sucV (γp p) ⟫`, a stuck concrete tower. The decisive probe: with the body reduced to a one-line application of a generic lemma that is itself free, `h₀-inj` **still pays its 190 s** (813.7 s against an 810.7 s control). **Sealing it is actively HARMFUL**: the exact Bridge shape ran past 26:06 clean before interruption, at least 1.9x slower. **And the abstract-carrier restatement, the discipline this whole campaign is built on, HEAP EXHAUSTED at `-M8g` twice** (10:26 with instantiations, 26:10 alone). So `[T93]`'s discipline is measured NOT to transfer to this theorem, which is the most important negative result of the campaign: **0.074 is known reachable by one tree, not by any given theorem.** What remains is an R-35 statement reshaping of the `h₀`/`comp₀` chain, an internal-interface restructure far over the 60-line seal line, **unpriced**; the measured floor if the four rows vanished is about 100 s. **F5's earlier rewrite-side price of 17 to 52 s is WITHDRAWN**: it assumed the benchmark was reachable here, and the one experiment that tested that assumption exhausted the heap. **The module is 250 obligations, not the 191 this row carried** (`[T95]` D5: 191 was `Bridge`'s count, substituted in by error), so the rate is **3.42 s per obligation, 46x**, not 3.14 and 50x. **THE DECISION, from `[T98]`: BURN THE BOATS, gated on ONE probe**, per D22 and the funding rule that a build whose widest term is unmeasured is not fundable when a probe can measure it. **The probe:** restate `SquareLaw`'s counting chase against an abstract finite-enumeration interface `(E : ℕ → Type ℓ)` with the count's four operations as hypotheses, and no `⟪ # m ⟫` anywhere in the telescope, then instantiate at `E n := ⟪ # n ⟫`. **Green at `-M8g`: burn the boats. Heap-exhausted: the chase is presentation-bound, the root cause flips to mathematics FOR THIS MODULE, and its 856 s is a standing tax until a tower reformulation is separately gated.** `[T97]` adds the discriminating diagnostic that explains why the `Bridge` fix could never have transferred: **`Bridge`'s profile rows named OTHER modules (consumer-side disease); `SquareLaw`'s four hot rows are its own definitions (definition-side disease)**, and the playbook's own rule says the two take different cures. **`Bridge` itself is now understood and mostly closed:** of its residual 199 s, **149.5 s is a ONE-TIME tower computation floor** (`γ-compute-full` 94.9 s plus `towerStep≡+ωU` 54.6 s), irreducible by more sealing because the tower's computation rule must relate `γ α` to its body at least once; the remaining ~50 s is the R-38 alias tail, worth 6 to 12 lines. **THE GATE IS GREEN.** `[T99]` restated `SquareLaw`'s counting chase against an abstract finite-enumeration interface with `⟪ # m ⟫` kept OUT of the telescope. **The exact gate that heap-exhausted `[T88]`'s probe 2a at `-M8g` after 26 minutes 10 seconds now passes in 1.28 seconds, exit 0.** Both instantiations at `E n := ⟪ # n ⟫` land, no postulate, no hole, no termination pragma. **The chase term goes from 350.8 s to about 1.5 s, a saving of roughly 349 seconds, for 61 new lines against 77 removed: line-neutral.** It confirms `[T98]`'s root cause exactly, and P-l's mechanism exactly: the statement is still ABOUT `⟪ # n ⟫`, the instantiation signatures carry the concrete numerals, but the elaboration never sees the presentation because `E` is neutral in the generic body. **SCOPE, STATED BECAUSE IT IS HALF THE MODULE:** the chase is the `pair-eq` pair. The `h₀-inj` pair is a **separate hot family at 360.6 s** whose statements carry `⟪ sucV (γp p) ⟫`, and `[T99]` did not build it. So this gate lands `SquareLaw` at about **507 s, not 42**; the `h₀`/`comp₀` chain reshape is the remaining measured term, priced by `[T98]` and not re-measured. **The rewrite is FUNDED at the 1.3x class on its widest term, per D22.** The one discipline the rewrite must not undo: keep `⟪ # m ⟫` out of the generic telescope, which is the recorded poison. **RULED 2026-08-06 BY THE OWNER: BURN THE BOATS. The rewrite is under way.** Dispatch 1 is `[T101]`, landing `[T99]`'s measured design in the master: the two concrete counting chases replaced by one generic chase at an abstract finite-enumeration interface plus two one-line instantiations, target **350.8 s to about 1.5 s, line-neutral**, exports frozen. Dispatch 2 is the `h₀`/`comp₀` chain reshape for the remaining 360.6 s, held back deliberately so the two families move separately and each result stays attributable. **The brief's load-bearing constraint, in capitals, is P-l's mechanism: `⟪ # m ⟫` must not appear anywhere in the generic telescope.** That single difference is 8 GB and 26 minutes against 1.28 seconds on the same theorem.  **DISPATCH 1 LANDED, BRANCH A, AND IT BEAT ITS OWN PREDICTION.** `[T101]` measured `SquareLaw` at **859.0 s before and 465.5 s after: minus 393 seconds, 45.8 percent, for a net MINUS ONE LINE.** The route memo predicted 507 s; it landed at 465.5. **The two `pair-eq` rows no longer exist as definitions**: the generic chase and both instantiations each sit below the profile display threshold, exactly as `[T99]`'s scratch measurement said. **Every exported type is unchanged**, verified independently by a full signature diff against HEAD: 250 signatures before, 245 after, and the only movement is the two chases' `where`-locals collapsing into one generic set. **The poison rule held**, verified by grep: zero occurrences of the concrete numeral presentation anywhere in the generic telescope (`src/L/Ordinal/SquareLaw.lagda.md:135-143`). **The tree goes 1,956 s to 1,563 s.** What remains in this module is the `h₀-inj` pair at 389.3 s, now **84 percent of it**, which is dispatch 2 and is probed before it is built.  **DISPATCH 2b LANDED. `SquareLaw` IS CLOSED: 856 s to 64.4 s in one day, a 13x reduction on the tree's most expensive module, for NET ZERO LINES across the two dispatches.** `[T103]` measured 470.6 s to 64.4 s, with the `h₀-inj` pair going **393.4 s to 71 ms**. Verified independently rather than taken on trust: a full signature diff shows **no exported signature lost**, with `Core.h₀`/`h₀-inj` (`:421`, `:424`) and `InitialCore`'s (`:1115`, `:1118`) all still declared at byte-identical concrete types, and the only movement being `where`-locals collapsing from two copies to one (`ea` 2 to 1, `eb` 2 to 1, `β` 6 to 3). **The tree goes 1,956 s to 1,162 s.** |"""
FIXTURE_F2 = """| L3.32-F2 | Cool `Condensation` while repairing it | **DEFECTS FIXED, COOLING REFUTED.** `[T89]` returned. **The repair landed and is by construction:** the equality-reading atom `snd∈Snd` is DELETED (zero occurrences), so defect 2 cannot be restated; the limit clause has no binder over a singleton member at all, so defect 3 cannot be restated; and **a fourth defect of the same class was found and machine-refuted**, the delivered `domForm` bound its variables in the singleton member and so did not read the delivered `exactDom` at all. +161 lines against a 400 stop-line. **THE COOLING IS REFUTED, and it is a real measurement against `[T86]`'s diagnosis: 203.3 s after against 203.5 s before, unchanged within noise.** The clauses WERE written at variable indices, the exact discipline the campaign rests on, and the module did not move. `[T89]`'s own explanation is the valuable part: **`Condensation`'s heat was never in the structural-story formulas, which were already variable-indexed; it is in the `σᴹ`/`σL` transports and the absoluteness applications at concrete tower positions**, which this dispatch did not touch. **So one untested cheap lever remains on this module and it is named**: the `Bridge`-style read-lemma restatement of the transports, not the story's index shape. D5 is not unblocked, but its content-level obstructions are gone and what remains is the clause decode suite, priced. **`[T96]` MEASURED IT AND FOUND A THIRD DISEASE.** Not `Bridge`'s consumer-bound and not `SquareLaw`'s statement-bound: **body-bound.** The gutted-body experiment settles it in one run: `ambientOnly-from` drops from 128.5 s to **0 ms** and 131.1 s appears in the lemma its one-line body now calls, with the module total unchanged. A statement-bound cost survives gutting, as `SquareLaw`'s 190 s did; this one MOVES. The three type synonyms carrying the concrete formula have **no profile rows at all**, under 20 ms each. **The bill of materials for the 183 s of hot rows, each priced:** ~77 s is an environment conversion between `AmbientOnly`'s unprojected premise and `TransferL`'s projected one, definitionally equal but walking the whole satisfaction tree of the concrete formula; ~54 s is the delivered `Lset-only` application, **the chapter's actual content, with no cheaper body of the same type**; ~56 s is the `Transport`/`amb-agree` instantiation inside `Crossing.crossOut-from`. **So about 133 of the 183 s IS removable and 54 s is content**, but every removal changes an exported statement, which is beyond a seal. **This is a priced refusal, which is exactly what D30's exit condition (2) asks for**, and it notes one cheap fact for later: `Crossing` has no tree consumer today, so parameterizing it on the formula costs nothing outside the module.  **`[T104]` RE-OPENED `[T96]`'s REFUSAL AND OVERTURNED IT IN DIRECTION.** `[T96]` concluded **"no export-preserving combination exists: every lever touches an exported statement"**. But it had priced only one move, RESTATING the exported obligations. `[T102]` then cured `SquareLaw`'s `h₀` family with every signature byte-identical, by **lifting the concrete applications into a module telescope** where they are checked once at a neutral position, and `[T104]` finds **all three `Condensation` pieces liftable the same way**: the ~77 s environment conversion, the ~56 s `Crossing` piece which **was never blocked at all** since `[T96]` itself conceded no tree consumer exists, and even the ~54 s `Lset-only` application that `[T96]` called irreducible content, on the argument from `[T96]`'s own `loLset3` figure that the cost is the concrete-index POSITION rather than the content. **So up to 183 of the module's 203 s may be reachable with no export change.** `[T104]` typechecked nothing and says so; `[T106]` is the gate that measures it before anything is built, per P-l's transplant law, and piece 3 is the one to be sceptical of.  **`[T106]` MEASURED IT AND REFUTED `[T104]`. `[T96]`'s ORIGINAL VERDICT STANDS.** Piece 1's lift makes the module **worse**, 204.7 s to 308.8 s. Piece 3's cost **moves** into the new telescope row rather than going away, and `ambientOnly-from` gets worse with it. Piece 2 is green **only in the export-CHANGING form**: the export-preserving wrapper re-pays the walk at 69.1 s, worse than the control's 55.2. **So no export-preserving combination exists, exactly as `[T96]` said, and the orchestrator backed the wrong reading.** This is the fourth transplant failure of the day and the first the orchestrator personally endorsed: `[T104]` reasoned from `[T102]`'s cure by resemblance and ran nothing, which is precisely what P-l's transplant table forbids. **THE PRICED REFUSAL IS ITSELF THE DELIVERABLE**, and it closes D30's exit condition (2) for this module. **One lever stays open and needs the owner's word:** `[T106]`'s B1, the export-changing `Crossing` parameterization, **minus 61.3 s for plus 5 lines**, with every other signature byte-identical and **zero tree consumers** of any crossing name confirmed by `rg`. It needs a ruling only because the changed statement is what D5 and W1' will later consume. |"""
FIXTURE_F6_0 = """| L3.32-F6.0 | **What should `L.Rud` CONTAIN at all**: the architecture question, before any batch | **RULED 2026-08-06 by the owner, and it corrects the row below.** The instruction: do not rewrite item by item; first ask what the items even ARE, whether they can be simplified, and start from the top-level module design. **The row below violated exactly that**: it sorted the existing 22 modules by seconds and funded them in that order, which takes the current decomposition as given and is item-by-item rewriting by another name. **THE MEASUREMENT THAT MAKES THE QUESTION URGENT.** `L.Rud` holds **2,884 obligations over 12,147 lines**, and the rest of the tree consumes **41 imported names from 5 of its 22 modules, and at least 46 actual names**: `[T94]` corrected 38 to 41 (a second `Step` using-block at `src/L/OrderFormula.lagda.md:366`), and `[T95]` then found `module Sat` is not one name but a module instantiated to at least six (`:380-413`), while two imported names (`_⊰_`, `_≺_`) are never used in the body at all. So **imported and consumed are different numbers and this row previously conflated them**: about **63 obligations per consumed name**. Five modules (`BaseBlock`, `CodePred`, `HF`, `OpGraph`, `SatTable`) are imported by nobody at all, inside the route or outside it. **THE CAVEAT THAT DECIDES HOW THAT IS READ, and it must be in the brief:** this route is mid-campaign, so `Bridge`, `HF` and `Finite` have no external consumer YET because their consumer is the bridge landing that D30 froze. **Unconsumed is not unneeded**, and a recon that confuses the two produces a catastrophically wrong answer. **WHAT THIS ROW MUST ANSWER:** what the route must deliver, counting the frozen consumers; how many of the 2,884 obligations are genuinely distinct mathematics against how many are instances of one pattern written repeatedly (D29, and `[T79]` already measured 700 to 850 standing lines written twice); which modules exist for a route that has since changed rather than for their content; and the ideal top-level decomposition designed BACKWARD from the deliverables (D17, priced from the rewrite side, D-19's port rates not quotable). **It gates B1.** **ANSWERED 2026-08-06 by `[T94]`, and the answer is a STOP: the current decomposition is close to ideal, so the wholesale rewrite is NOT the move.** Designing backward from the deliverables it returns **18 KEEP, 4 RETIRE, 1 REWRITE**, against 22 standing. **The four retirements are the real prize and none of them is a rewrite:** `BaseBlock` (content already harvested into `Finite` by `[T82]`, `HF` re-pointed), `CodeSet` (consumed only by `CodePred`, which retires), `CodePred` (the satisfaction-internalization cone died with the route change), and `OpGraph` (**the wall it filled was refuted by `[T63]`; this is a NEW retirement and needs the owner's ruling**). Together **-440 signatures, -2,057 lines, -40 s**, at the price of an archival rather than a rewrite. **The one REWRITE it names is `StepInL`, which the ledger already owed** for W3 at 1.24 to 1.73k naive, so the architecture question adds no new rewrite work at all. It also names three compression levers inside kept modules, all of them `[T79]`'s already-measured duplication rather than new findings: the `Describe` per-op shells behind one generic wrapper, and the `Fof-f0..f15` and `JF0..JF10` families collapsed to one indexed lemma. **So the owner's question has paid for itself in the opposite direction from the one expected**: asking what the route should CONTAIN found 2,057 lines that should not exist at all, which no per-module seconds ranking would ever have surfaced, and simultaneously refuted the case for rewriting the other 10,090. |"""
FIXTURE_F6 = """| L3.32-F6 | The `L.Rud` rewrite, batched: **what the CURRENT decomposition would cost, superseded by F6.0** | **PARTLY SUPERSEDED 2026-08-06.** The exit condition and the funding rule stand; **the batch ORDER does not**, because it takes the existing 22 modules as given, which the owner ruled against (see `[L3.32-F6.0]`). Read the batches below as a floor on the prize under the current architecture, not as the plan. **THE RULED NUMBER MOVED, 0.063 to 0.074, and the ruling did not.** The owner ruled the exit condition to be *the retiring subtree's measured rate*; that rate was then re-measured after two parser defects were found in the counter (comment lines read as signatures, `let z : A` scored twice), and it is 0.074. The ratio between the trees did not move at all, because the defects inflated both alike, which is the clearest evidence available that the RATIO is robust and the ABSOLUTE figures are not. **RULED 2026-08-06 by the owner**: the retiring subtree's measured rate is the exit condition, and the rewrite runs in batches. **THE EXIT CONDITION SELECTS THE BATCHES BY ITSELF, WHICH IS THE FINDING: 13 of `L.Rud`'s 22 modules are ALREADY at or below the line and need no rewrite at all, and of the 9 above it, 4 are worth 14 seconds COMBINED.** `L.Rud` stands at 12,147 lines, 2,884 obligations, 458 s, **0.159 s per obligation**; at the exit condition it is 212 s, so the whole programme is worth **246 seconds**, and it concentrates hard. **B1 `Bridge`, 185 s, 75 percent of the entire prize** in one 833-line module, and it doubles as the METHOD GATE: it is already sealed, so it isolates what a rewrite buys BEYOND sealing, and if a rewritten `Bridge` does not approach 21 s then the benchmark is not reachable by rewriting and every batch below re-prices. **B2 `StepInL`, 54 s** over 1,989 lines, and it is nearly free because the ledger already owes a re-scope of this module for W3: the two merge. **B3 `Images`, `CodeSet`, `Step`, about 71 s** over 1,289 lines. **AND THE PROGRAMME STOPS THERE**: the remaining 4 modules above the line (`HF`, `DefInJ`, `BaseBlock`, `SatTable`) are worth **14 seconds combined over 1,223 lines**, which is a rewrite that costs more than it buys in both dimensions. They are recorded as above the line and left alone, and that is the exit condition doing its job rather than being overridden. **THE LINE DIMENSION, which cuts against the programme and is recorded rather than buried:** `L.Rud` already writes **3.8 lines per obligation against the benchmark's 4.9**, so it is denser than the tree it is being measured against. This is a SECONDS programme, not a lines programme, and each batch is gated on not inflating lines. **FUNDING RULE:** B1 is dispatched on its own merit and gates B2 and B3; no batch is funded at the 3x class once B1 has measured the real rate. |"""
FIXTURE_F0 = """| L3.32-F0 | **Settle the caliber**, before any threshold is argued | **DONE 2026-08-06, and CORRECTED the same day, which is itself the entry's lesson.** The owner's ruling: how much of the cost is really mathematics is a per-OBLIGATION question, not a per-line one, and pinning that caliber comes before arguing any exit condition. `scripts/measure/obligations.py` counts obligations mechanically. **THE FIRST ANSWER WAS WRONG AND IS WITHDRAWN.** It counted only column-0 signatures and reported 2.1x per top-level obligation with the retiring tree writing 56.5 lines per obligation against the trunk's 22.4. Both figures are artifacts: **the cheap tree writes everything inside `module _ (A : V ℓ) where` blocks, so every result it has is INDENTED**, and `L.Godel.Closure` scores zero top-level obligations over 3,490 lines. A top-level-only count measures module-parameterization style and punishes the very discipline that makes the code cheap. **THE CORRECTED RESULT, counting obligations at any depth:** the two trees write **4.9 against 3.9 lines per obligation**, which is nearly the same density, and cost **0.074 against 0.277 s per obligation, a real 4.2x**. So the conclusion reverses: the per-line comparison was not unfair and the gap is not an artifact. **It is real, and the fair caliber confirms it rather than dissolving it.** The controlled per-module experiment (`Bridge`, 4.7x, mathematics held fixed) remains the sharper instrument because no caliber has to be agreed on for it to mean something, but the cross-tree ratio is a genuine signal and is NOT dropped. **The lesson, and the reason the owner was right to demand this first: the caliber was wrong twice in one day, in both directions, and each time it silently changed what the plan concluded.** **ADVERSARIALLY REVIEWED 2026-08-06 by `[T95]`, dispatched by the owner precisely because the author of a measurement is its worst reviewer. It found seven defects and they are fixed.** The worst was not in the caliber at all: **an anchored string-slice edit destroyed five data blocks from `dev/ledger.toml`** (`timing`, `hot`, `tree_cost`, `owed`, `lever`), which silently killed BOTH gates in `check-timing.py`, since each reads a block that no longer existed. Restored block-wise from `1194b98`. **The second worst was a false claim in a document**: the ledger said the parser fixes were covered by regression tests and there were none, so they now exist at `scripts/tests/test_obligations.py`, seventeen cases. **And the defence given for the ratio's stability was wrong**: the defects did not inflate both trees alike (comments hit the trunk 1.14x harder, `let` hit the retiring tree about 16x harder), they happened to CANCEL to within 0.6 percent. Stability by coincidence, not by theorem. A fourth asymmetric class was then measured: signature-less definitions, 421 retiring against 216 surviving, which would move the ratio 4.20 to 4.38 and the benchmark 0.074 to 0.068. **All of it is recorded in the ledger's `[caliber]` block rather than resolved, because resolving it quietly is exactly how this went wrong three times.** |"""

EXEMPLAR_L3_32_ROW = """| L3.32 | The L-trophy build (the ruled configuration) | **RULED AND ACTIVE 2026-08-04** by D18. The Def tower keeps the trophy; the wing rides a fresh-generic Sigma-1 face; the reindexed bridge lands at wing tail as a corollary; choice re-homes through it; the internalization cone, the choice tree, the Goedel trees and the coded cluster retire. Wave 1 (the R4 corrective stop, the face probe, the choice re-home probe, the retirement design recon, the W7 scoping) has returned; wave 2 builds the face chapter, then W2, then W3 and W5 in parallel, then the bridge, the re-home, the retirement surgery and W7. The check-cost campaign (D30's freeze, and the work that lifts it) and the current gates run in the `[L3.32-F*]` rows below. **The retirement surgery ARCHIVES rather than deletes** (D20, in force from 2026-08-04) and builds the archive infrastructure on its first use. Standing and endpoint figures are in section 0. Execution record, with the wave-by-wave measurements: `dev/JOURNAL.md`. |"""

def goal_row_of(chars: int) -> str:
    """A MASTER goal row of exactly `chars` characters (rstripped)."""
    base = len("| L3.32-F5 |  |")
    return "## 11.\n" + f"| L3.32-F5 | {'x' * (chars - base)} |"


CASES = [
    # --- the historical failure states must fire ---
    (lambda: flagged(check.check_agents_size, words(3450)),
     "AGENTS.md at the pre-slim 3,450 words must be over the cap"),
    (lambda: flagged(check.check_plan_cells, plan_row("L3.32", words(12634))),
     "the 12,634-word L3.32 cell must be over the cell cap"),
    (lambda: flagged(check.check_section0_date,
                     "## 0. Where the work stands (2026-08-04)\n\n"
                     "in flight (2026-08-06)\n"),
     "a section 0 heading older than its own body must fire"),
    (lambda: flagged(check.check_imported_routing,
                     "### P-i. The conversion-explosion playbook (imported "
                     "from the source project)\n", EMPTY_RULES),
     "an imported entry with no routing must fire"),

    # --- the boundary: at the cap is clean, one over fires ---
    (lambda: not flagged(check.check_agents_size, words(check.AGENTS_WORD_CAP)),
     "AGENTS.md at exactly the cap is clean"),
    (lambda: flagged(check.check_agents_size, words(check.AGENTS_WORD_CAP + 1)),
     "AGENTS.md one word over the cap fires"),
    (lambda: not flagged(check.check_plan_cells, plan_row("D28", words(1600))),
     "a cell at exactly 1,600 words is clean"),
    (lambda: flagged(check.check_plan_cells, plan_row("D28", words(1601))),
     "a cell one word over 1,600 fires"),

    # --- the current tree's shapes must stay clean (no wolves) ---
    (lambda: not flagged(check.check_agents_size, words(1784)),
     "the current 1,784-word AGENTS.md is clean"),
    (lambda: not flagged(check.check_plan_cells,
                         plan_row("L3.32-F5", words(1125))),
     "a 1,125-word cell outside the MASTER table is clean under the word cap (the T110 largest-cell shape)"),
    (lambda: not flagged(check.check_section0_date,
                         "## 0. Where the work stands (2026-08-06)\n\n"
                         "ruled 2026-08-04\n"),
     "a heading as new as its body is clean"),
    (lambda: not flagged(check.check_imported_routing,
                         "### C-21. Telescope types may only use level-generic "
                         "imported names\n", EMPTY_RULES),
     "C-21's 'imported names' is code prose, not an import marker "
     "(the first-version wolf)"),
    (lambda: not flagged(check.check_imported_routing,
                         "### P-i. The conversion-explosion playbook (imported "
                         "from the source project)\n", ROUTED_RULES),
     "an imported entry that IS routed is clean"),
    (lambda: flagged(check.check_section0_date, "## 1. No section zero\n"),
     "PLAN with no section 0 is a finding, not a crash"),

    # --- memo status form ---
    (lambda: not flagged(check.check_memo_status, memo_dir(
        "> **STATUS: the diagnosis below is WRONG and the mechanism is NOT "
        "BUILT.**\n")),
     "a STATUS header stating a verdict is clean"),
    (lambda: flagged(check.check_memo_status,
                     memo_dir("> **STATUS: see the follow-up report.**\n")),
     "a STATUS header with no verdict word fires"),
    (lambda: not flagged(check.check_memo_status, memo_dir("plain memo\n")),
     "a memo with no STATUS header is untouched (form-when-present)"),

    # --- AGENTS enforcement table names real scripts ---
    (lambda: not flagged(check.check_agents_enforcers,
                         "| x | `scripts/measure/ledger.py` |\n"),
     "a named enforcer that exists is clean"),
    (lambda: flagged(check.check_agents_enforcers,
                     "| x | `scripts/nope.py` |\n"),
     "a named enforcer that does not exist fires"),

    # --- the goal-row character cap (T112): the pre-slim worst rows fire ---
    (lambda: flagged(check.check_plan_cells, MASTER + FIXTURE_F5),
     "the pre-slim L3.32-F5 row (6,966 chars) fires the goal-row cap"),
    (lambda: flagged(check.check_plan_cells, MASTER + FIXTURE_F2),
     "the pre-slim L3.32-F2 row (5,131 chars) fires the goal-row cap"),
    (lambda: flagged(check.check_plan_cells, MASTER + FIXTURE_F6_0),
     "the pre-slim L3.32-F6.0 row (3,704 chars) fires the goal-row cap"),
    (lambda: flagged(check.check_plan_cells, MASTER + FIXTURE_F6),
     "the pre-slim L3.32-F6 row (2,836 chars) fires the goal-row cap"),
    (lambda: flagged(check.check_plan_cells, MASTER + FIXTURE_F0),
     "the pre-slim L3.32-F0 row (3,106 chars) fires the goal-row cap"),
    (lambda: not flagged(check.check_plan_cells, goal_row_of(check.PLAN_GOAL_ROW_CHAR_CAP)),
     "a goal row at exactly the 1,200-character cap is clean"),
    (lambda: flagged(check.check_plan_cells, goal_row_of(check.PLAN_GOAL_ROW_CHAR_CAP + 1)),
     "a goal row one character over the cap fires"),
    (lambda: not flagged(check.check_plan_cells, MASTER + EXEMPLAR_L3_32_ROW),
     "the post-slim L3.32 row, the register exemplar, is clean"),
    # --- the sweep's pure pieces ---
    (lambda: bool(re.search(r"(?<![\w-])" + check._cite_pattern("D-2") +
                            r"(?![\w-])", "PLAN cites D2 here")),
     "the D-2 citation pattern also matches the PLAN-style D2"),
    (lambda: not re.search(r"(?<![\w-])" + check._cite_pattern("D-2") +
                           r"(?![\w-])", "decision D-20 is a different thing"),
     "the D-2 pattern does not match inside D-20"),
    (lambda: bool(check.sweep_cells("## 11.\n" +
                                    plan_row("L3.32-F5", words(700)))),
     "a section 11 cell over 600 words is listed by the sweep"),
    (lambda: not check.sweep_cells("## 11.\n" +
                                   plan_row("L3.32-F5", words(500))),
     "a section 11 cell under 600 words is not listed"),
]


def main() -> int:
    failures = 0
    for run, why in CASES:
        try:
            ok = run()
        except Exception as exc:  # a crash is a failure, reported plainly
            ok, why = False, f"{why} (crashed: {exc})"
        failures += not ok
        print(f"  {'ok  ' if ok else 'FAIL'}  {why}")
    print(f"\n{len(CASES) - failures}/{len(CASES)} passed")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())

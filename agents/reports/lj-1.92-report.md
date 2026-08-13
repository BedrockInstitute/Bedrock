# LJ-1.92: probe the order-type module, the cardinal route's widest term

tier: codex (default)

## STATUS

COMPLETE. The miniature checks. No master was touched. No commit, no push.
The report is `_build/lj-1.92-report.md`.

## 0. THE VERDICT

**The tree delivers the collapse-of-a-well-order pattern once, pinned to one
carrier, and the archived order-type assembly. The miniature re-instantiates
the pattern at a generic SWO carrier and checks. Step 2 measures at 365
non-blank lines and 18.4 s cold at this load. The hard half is the image
block, not the recursion and not the isomorphism.**

The probe is `src/ProbeLJ192A.agda`, GREEN at the C-12 cap, one process,
365 non-blank lines. Three cold runs: 18.42 s / 18.40 s / 19.76 s wall,
18.12 / 18.10 / 18.56 s user. Loads at the runs: 3.27 / 3.60 / 3.92,
3.42 / 3.61 / 3.91 and 3.41 / 3.57 / 3.84, four users, the machine was NOT
quiet.

`src/V/Collapse.lagda.md` does NOT carry step 2. It is a collapse of the
membership relation of the hierarchy, not of an arbitrary well-order. Its
recursion is over the hierarchy's own `∈` (`src/V/Collapse.lagda.md:40-72`).
The reusable pattern is the `col` machinery at
`src/L/Ordinal/SquareLaw.lagda.md:373-496`, which is pinned to the square of
an ordinal's index, and the archived order-type assembly at
`archive/rud-route/src/L/Ordinal/Pairing.lagda.md:436-575`.

## 1. WHAT THE TREE ALREADY DELIVERS

- The generic well-order record `SWO` with trichotomy, irreflexivity,
  transitivity and well-foundedness: `src/L/WellOrder/Base.lagda.md:101-107`.
  It is level-generic and independent of both towers.
- The collapse-of-a-well-order core, delivered once at the square carrier:
  `colPick` and `colStep` (`src/L/Ordinal/SquareLaw.lagda.md:373-379`), the
  well-founded recursion `col` with its computation law
  (`:383-388`), ordinal-hood `col-ord` (`:390`), monotonicity `col-mono`
  (`:406`), injectivity `col-inj` (`:427`), image-surjectivity `col-img`
  (`:437-496`).
- The archived order-type assembly, the shape of the isomorphism half:
  `τ` and `τ-ord` (`archive/rud-route/src/L/Ordinal/Pairing.lagda.md:457-461`),
  `col∈τ` (`:463`), the index embedding `col→τ` with injectivity
  (`:477-488`), `col-img` (`:490`), `col-surj` (`:551`), `col→τ-surj`
  (`:571`).
- The ordinal supply: `∅-ord` (`src/L/Ordinal.lagda.md:77`), `suc-ord`
  (`:96`), `setUnion-ord` (`:125`), `mem-ord` (`:221`).
- The V-set kit: `∈sucV-elim` and `self∈sucV`
  (`src/V/Model.lagda.md:218`, `:236`), `member`, `fiber`, `↪-inj`
  (`src/V/Presentation.lagda.md:31-37`).

The delivered core is not generic. Every definition names the square
carrier `Pair` and its order. A fresh carrier needs the same block again.
That re-instantiation is what the probe measures.

## 2. THE MINIATURE

`src/ProbeLJ192A.agda` re-instantiates the delivered pattern at a module
parameter `(X : Type ℓ) (swo : SWO X)`. The content, with the delivered
source each piece mirrors:

| piece | probe lines | delivered shape |
|---|---:|---|
| order decidability from trichotomy, `colPick`, `colStep`, `col`, `col-ord`, `col-mono`, `col-inj` | 64-133 | SquareLaw `:373-435` |
| `col-img`, `τ`, `τ-ord`, `col∈τ`, `col→τ`, `col→τ-fiber`, `col→τ-inj`, `col-surj`, `col→τ-surj` | 136-252 | SquareLaw `:437-496`, Pairing `:457-575` |
| the isomorphism's backward half `col∈-bwd`, `iso`, the index embedding `emb-mono`, `emb-mono-bwd` | 258-285 | NEW; the tree has `col-mono` but not its converse |
| uniqueness: `OrderIso`, `col-iso`, `τ-eq` for isomorphic well-orders | 292-423 | NEW |

`col∈-bwd` closes with trichotomy plus ordinal transitivity
(`src/ProbeLJ192A.agda:258-266`). `OrderIso` is a bijective order-embedding
given as data: forward and backward order preservation plus surjectivity
(`src/ProbeLJ192A.agda:303-308`). `col-iso` carries the collapse equality
across the isomorphism by well-founded induction
(`:400-408`), and `τ-eq` lifts it to the unions (`:410-423`).

## 3. THE MEASUREMENT, AND THE HARD HALF

Four cold checks, one process each, at the C-12 cap, `GHCRTS="-A64m -I0 -M8g"`.
The machine had four users at every run.

| stage | content | wall |
|---|---:|---:|
| 1 | recursion shape: `≺-dec` through `col-inj` | 1.62 s |
| 2 | + image block: `col-img`, `τ`, `col∈τ`, `col→τ` trio, `col-surj`, `col→τ-surj` | 18.87 s |
| 3 | + `col∈-bwd`, `iso`, `emb-mono`, `emb-mono-bwd` | 18.36 s |
| 4 | + uniqueness: `OrderIso`, `col-iso`, `τ-eq` | 18.91 s |

Stage 1 ran at load 4.88 / 4.42 / 4.49; the final three runs at load 3.3
to 3.4 measured 18.42 s, 18.40 s and 19.76 s wall. The intermediate stages
were not load-logged; every run had four users. The qualitative reading is
stable across the load difference.

**The hard half is the image block.** `col-img` and `col-surj` are the
expense: about 17 s of the 18.4 s total. The recursion shape is cheap
(1.6 s). The isomorphism's backward half and the uniqueness theorem add
about 0.5 s together. The image block elaborates the cumulative-hierarchy
union and successor machinery at concrete V-sets, which is the instantiation
class of P-m, not the parameterized class.

## 4. THE PRICE FOR STEP 2

**One best-effort figure: 365 lines, about 18 to 20 s cold at this load,
with the machine not quiet. The basis is the miniature itself:
`src/ProbeLJ192A.agda`, 365 non-blank lines, checked at the C-12 cap in
18.42 s, 18.40 s and 19.76 s wall at load 3.3 to 3.4, four users.**

The miniature covers the full step-2 content named in the brief: the
recursion's shape, the isomorphism's shape, and uniqueness for isomorphic
well-orders. The consumer-side adequacy, which turns the well-order formula
on a V-set of pairs into an `SWO` record, is route step 1's content per the
1.91 routing (`_build/lj-1.91-report.md` section 2, step 1) and is not
measured here.

The 1.91 seconds estimate is REFUTED at this carrier. It was INFERRED at
0.0107 s per line, 6 to 8 s for the block. The measured rate is 0.050 s per
line, 4.7x the inferred rate. The 1.91 line band, 300 to 500, is confirmed:
365 measured.

## 5. NEGATIVES AND THEIR STATUS

1. "The order-type core re-instantiates at a generic SWO carrier":
   **MEASURED TRUE**. The probe checks green.
2. "The image block is the hard half": **MEASURED**. 17 s of 18.4 s is
   `col-img` and `col-surj` content (section 3).
3. "The 1.91 seconds estimate, 6 to 8 s": **MEASURED FALSE** at this
   carrier. 18.4 s cold at load 3.3. The estimate was INFERRED in 1.91 and
   this dispatch is the measurement it called for.
4. "The 1.91 line band, 300 to 500": **MEASURED TRUE**. 365 non-blank lines.
5. "`V.Collapse` carries most of step 2": **MEASURED FALSE by reading**. It
   collapses the hierarchy's membership, not an arbitrary well-order
   (`src/V/Collapse.lagda.md:40-72`). The col pattern is the tool.
6. "Uniqueness for isomorphic well-orders needs choice": **MEASURED FALSE**.
   The `Unique` module checks with the isomorphism as data and no choice.
7. "A quiet machine checks the block faster than 18.4 s": **INFERRED**.
   Every run had four users. This inference sets no verdict.

## 6. DD4

**The order-type block is generic and the J tower inherits it unchanged:
INFERRED, with a measured half.** The measured half: the probe's module
depends only on the `SWO` record, the V-set kit, and the ordinal supply over
`𝒮ᵥ`; no Def tower object appears in any type. The J half is INFERRED, since
no J tower exists in this tree. The 1.91 report classified the cardinal
content of Devlin 5.5 as EITHER-tower (`dev/literature/devlin-II5.md:382-387`),
and this block is the same content class.

## 7. CHOICE

No axiom of choice and no excluded middle is used. Order decidability falls
out of trichotomy (`src/ProbeLJ192A.agda:64-69`). The uniqueness theorem
takes the isomorphism as data (`:303-308`). The probe module has no LEM in
its telescope. The route's ZF model still needs LEM through its
impredicativity parameter, per the 1.91 report section 8; the order-type
core itself is choice-free and LEM-free.

## 8. ARCHIVE USED

- `_build/lj-1.91-report.md`, read WHOLE. TOOK the five-step route, the
  step-2 price claim (300 to 500 lines, 6 to 8 s inferred), and the probe
  shape (`col` recursion plus the iso at the C-12 cap).
- `_build/lj-1.90-report.md` and `src/ProbeLJ190A.agda`, read WHOLE. TOOK
  the consumer site: `cardκ : IsCardinal κ` is the first unsuppliable
  hypothesis (`_build/lj-1.90-report.md` section 1.1).
- `src/V/Collapse.lagda.md`, read WHOLE. TOOK the verdict that it is a
  membership collapse, not an order-type tool (`:40-72`).
- `src/V/Model.lagda.md`, read the power set (`:280-329`) and separation
  (`:361-371`). TOOK the route's step-1 supply, not used by the probe.
- `src/L/Ordinal/SquareLaw.lagda.md`, read the col machinery
  (`:146-496`) and `Init` (`:692-700`). TOOK the delivered pattern the probe
  re-instantiates.
- `src/L/Ordinal/`, read the ordinal supply (`src/L/Ordinal.lagda.md:77-258`).
- `src/L/StageCardinal.lagda.md`, read `OrdSWO` (`:226-258`) and
  `stage-card-lower` (`:205`). TOOK the delivered ordinal well-order shape.
- `dev/LESSONS.md`, read WHOLE D-8 (`:1377`), D-1 (`:1038`), D-30 (`:3332`),
  P-l (`:2305`), C-36 (`:3284`), and the `--for build` and `--for probe`
  bundles via `scripts/rules.py`.
- `archive/rud-route/`, SHAPE only. TOOK the order-type assembly at
  `archive/rud-route/src/L/Ordinal/Pairing.lagda.md:436-575`.

## 9. LITERATURE USED

Devlin II.5 assumes the initial-ordinal facts and proves no order-type
content in the chapter (`dev/literature/devlin-II5.md:145-166`); the order
type belongs to Chapter I ZF background (`dev2.txt:1369-1388`). Two lines:
Devlin assumes order types, he does not prove them in II.5.

## 10. GATES

- `src/ProbeLJ192A.agda`: GREEN at the C-12 cap, one process, three cold
  runs of 18.42 s, 18.40 s and 19.76 s wall. Loads at the runs:
  3.27 / 3.60 / 3.92, 3.42 / 3.61 / 3.91 and 3.41 / 3.57 / 3.84, four
  users, machine NOT quiet. No process was left alive.
- `scripts/check-fences.py --check`: clean, 87 masters, run threshold 3.
- `scripts/lint-prose.py --check` on the probe and this report: exit 0.
- `scripts/lint-agda.py --check` on the probe: exit 0.
- `scripts/ledger.py --brief`: standing 28,189 lines over 85 masters,
  measured from HEAD `a1f0e95`.
- `git status`: `dev/PLAN.md` modified (the orchestrator's dispatch rows for
  LJ-1.92 and LJ-1.93, present before this dispatch; untouched). The probe
  and the report are ignored by `.gitignore`. No commit, no push, no
  `make check`.
- Masters: none touched. DD23: no mathematical prose was written.

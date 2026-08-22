# LJ-1.570 report: `levelIn` and `cover`, re-priced at today's tree

## HEAD
head_slot: coder
machine: shared
verdict: obligation INHABITED; `CoHyps` NOT SUPPLIED

Written as a skeleton before any Agda and filled as each answer landed (C-22).
No commit, no push. I wrote only inside `agents/tasks/LJ-1-570/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. I did not set `GHCRTS`. No heap event. Nothing is postulated,
the probe carries `--safe`, and there is no hole. The probe is a raw `.agda`
file, so it carries no ` ```agda ` fence, counts 0 in-fence lines, and the ratio
bar cannot fire on it. Nothing lands in `src/`.

## VERDICT

**THE OBLIGATION IS INHABITED, IN THE SECOND FORM THE BRIEF PERMITS.**
`agents/tasks/LJ-1-570/Probe570.agda::cohyps-at-today`, `Probe570.agda:188-195`,
exit 0. The witness meter agrees: `0 UNRESOLVED of 1`, `probe_red=False`
(`runs/witness-1.out`). The six other terms this report names also all
resolve, `0 UNRESOLVED of 6` (`runs/witness-2.out`).

**AND `CoHyps` ITSELF IS NOT SUPPLIED. THE BILL IS STILL FIVE ROWS.**
`agents/tasks/LJ-1-570/review-of-cohyps.md` states the stop.

**WHAT THE OBLIGATION SAYS.** `cohyps-at-today : HullCondensation → CoHyps`.
`CoHyps` is stated over the bounded subset theorem's SEVENTEEN-slot telescope
(`agents/tasks/LJ-1-550/Probe550.agda:215-230`). `HullCondensation`
(`Probe570.agda:168-176`) is the same two hypotheses at SIX slots, and the six
are exactly `HullStage`'s own (`src/L/BoundedSubset.lagda.md:903-905`).
**ELEVEN OF THE SEVENTEEN SLOTS ARE DEAD WEIGHT FOR THE STATEMENT**, and the
elaborator says so, not this report: `gch-from-five-at-the-hull`
(`Probe570.agda:199-206`) is `[LJ-1.564]`'s bill with row 3 replaced by the
six-slot form, at the same target.

**THAT IS A SUFFICIENT CONDITION AND NOT AN EQUIVALENT ONE, and the difference
matters to whoever writes the next brief.** Section 4 of the probe measures why:
the tree's own down-reflection lives at the seventeen-slot frame, because its
code selection needs `α`'s well-order and the hull's code count
(`src/L/BoundedSubset.lagda.md:1515-1545`). A supplier that wants `elem-down`
must take the wider frame. A supplier that does not, need not.

## WHAT EACH ASKS FOR TODAY

### `levelIn` — NOT SUPPLIED, and not suppliable today

`levelIn` is `Co`'s first parameter, `src/L/BoundedSubset.lagda.md:1555-1556`:
for every ordinal `δ` of the collapse `HS.C.πX`, the stage `Lset δ` is also in
the collapse. Restated at the theorem's telescope as `Tele.LevelIn`
(`agents/tasks/LJ-1-550/Probe550.agda:104-106`), and W3 re-ascribes it at the
frame `gch-from-five` calls it (`Probe570.agda:68-79`, and `runs/W3.agda`
alone, exit 0). **What it asks for is Devlin's chain (c) to (q)**
(`dev/literature/devlin-II5.md:100-106`): the Σ₁ level-hood statement at the
parameter index, transferred from `Lset λ` down into the hull and across the
collapse. `[LJ-1.52]` named three survivors for it
(`agents/tasks/archive/LJ-1-52/lj-1.52-report.md:17`) and three for `cover`
(`:18`). **ONE OF THE SIX IS A TERM AT THE SITE TODAY**, and it is the
down-reflection, which `[LJ-1.52]` asked for at arity ONE and the tree now
delivers at ANY arity (`elem-down-at-the-site`, `Probe570.agda:233-249`;
`src/L/BoundedSubset.lagda.md:1547-1548`, whose `ElemDown` quantifies over
`n` at `:410-411`). **Two more have their machinery in `src/` and no term at the
site**: the hull's Skolem closure (`src/L/Hull.lagda.md:120`) and the collapse
iso (`src/L/BoundedSubset.lagda.md:152`, `:321`). **THE OTHER THREE ARE NOT
BUILT ANYWHERE.**

**AND IT IS STATED STRONGER THAN ITS ONLY CONSUMER ASKS.** MEASURED by
`grep -n "levelIn" src/L/BoundedSubset.lagda.md`, which returns four lines. Two
are the declarations (`:917`, `:1555`) and one passes the parameter along
(`:1560`). **`levelIn` is APPLIED at exactly one place, `:1020`, inside
`Lβ⊆πX`, and there its argument is `sucV δ` and nothing else.**
`LevelInSuccOnly` (`Probe570.agda:360-362`) is everything `src/` spends;
`strong-gives-weak` (`Probe570.agda:364-365`) is the direction that holds
today. **The direction a supplier would want is the other one, and it needs
`Co`'s parameter weakened in `src/`.** This brief does not fund that edit and I
did not make it.

### `cover` — NOT SUPPLIED, and not suppliable today

`cover` is `Co`'s second parameter, `src/L/BoundedSubset.lagda.md:1557-1558`:
every member of the hull `HS.M` has its collapse image inside `Lset γ` for some
ordinal `γ` of the collapse. Restated as `Tele.Cover`
(`agents/tasks/LJ-1-550/Probe550.agda:108-113`) and re-ascribed at the frame as
`CoverAt` (`Probe570.agda:84-96`); `halves-are-cohyps` (`Probe570.agda:100-106`)
proves the two halves ARE `CoHyps`. **What it asks for is the SAME adequacy as
`levelIn`, on the level-MEMBERSHIP relation, plus a least-witness selection in
the hull** (`agents/tasks/archive/LJ-1-52/lj-1.52-report.md:18`;
`dev/literature/truncation-and-selection.md:17`). **Unlike `levelIn` it is
general at every consumer**: three sites, `:967`, `:1002` and `:1606`, and none
of them restricts the argument.

### The three items that are missing

| # | what | where it is stated | status |
|---|---|---|---|
| 1 | `GraphAgree`, one direction of row six | `Probe570.agda:289-294` | parts are TERMS in five tracked probes, NONE in `src/` |
| 2 | `HierInK`, `hierL β ∈ Lset α` | `agents/tasks/LJ-1-532/Probe532.agda:274-277` | ONE open mathematical fact, four tasks stopped on it |
| 3 | the hull re-basing, the `Adeq` application, the collapse transfer | `agents/tasks/archive/LJ-1-52/lj-1.52-report.md:17-18` | NOT BUILT anywhere |

Item 1 is MEASURED absent from `src/`:
`grep -rn "leaf-unbounds\|body-unbounds\|step-agree\|approx-agree" src/` returns
nothing. Item 2 is Devlin 2.6(ii) (`dev/literature/devlin-II5.md:221`), and
`[LJ-1.517]` measured that the witness wants two membership steps of headroom,
which a limit always has (`agents/tasks/LJ-1-517/lj-1.517-report.md:88-90`).

## THE PRICE I MEASURED

**THE ONE NUMBER I MEASURED IS 41 LINES, AND IT PRICES `[LJ-1.304]`'s LAST
UNPRICED TERM.** Section 5 of the probe re-lands `[LJ-1.52]`'s
`matrix-decode` and `adeq-decode`
(`agents/tasks/archive/LJ-1-52/ProbeLJ152A.agda:58-96`) at today's tree:
41 non-blank non-comment lines, counted by me over `Probe570.agda:251-337`.
`[LJ-1.304]` INFERRED it at "about 40 lines"
(`agents/tasks/LJ-1-304/lj-1.304-report.md:332-335`). **MY MEASUREMENT AGREES
WITH THAT INFERENCE.**

**AND THE PORT IS NOT A COPY.** `[LJ-1.52]` read the graph's value at slot 1 of
the inner environment (`ProbeLJ152A.agda:52-54`). Today `LevelHood`
instantiates `GraphB` at `zero (suc (suc (suc zero))) (suc (suc (suc (suc
zero))))` (`src/L/BoundedSubset.lagda.md:104`), so the value slot is 0, slot 0
of the outer environment is unused (`:69-71`), and the value is reached only
through the `≐` conjunct. **The archived spelling does not typecheck today**
and the correction is in the file. This is what
`dev/literature/level-formula-slot-roles.md:9` says a port must re-derive.

### What the whole of row 3 costs, and what I did NOT measure

| item | figure | basis |
|---|---:|---|
| the assembly, re-landed | **41 lines** | MEASURED, this probe |
| row six's parts, already written | **852 lines** | MEASURED by me over five tracked probes, headers included: `LJ-1-525/Probe525.agda` 142, `LJ-1-527/Probe527.agda` 123, `LJ-1-530/Probe530.agda` 143, `LJ-1-304/ProbeLJ1304A.agda` 268, `LJ-1-124/ProbeLJ1124A.agda` 176 |
| the graph composition itself | **2 lines** | MEASURED, `agents/tasks/LJ-1-124/ProbeLJ1124A.agda:199-202` |
| `HierInK` | **NOT MEASURED** | it is a statement that is open, not a line count |
| the hull re-basing | **NOT MEASURED** | nothing to count: no term exists |

**AGAINST THE ARCHIVE'S TWO NUMBERS, PLAINLY.**

- `[LJ-1.121]`'s "2.8k to 3.3k lines" (`archive/dev/LJ-dispatch-index.md:198`)
  is **SUPERSEDED, and it was superseded before this task**, by `[LJ-1.123]`
  (`:199`), which the tree's own record carries.
- `[LJ-1.146]`'s "about 1.0k lines" (`:222`) **I DID NOT RE-MEASURE, and I do
  not confirm or refute it.** What I measured is that its COMPOSITION has
  changed. At `[LJ-1.146]` the chain was unwritten. Today rows one to five of
  it are written, in five tracked probes carrying 852 lines between them, and
  what is left is one open fact plus a hull re-basing that has no term at all.
  **So a brief funded against 1.0k lines would fund a build that stops where
  `[LJ-1.536]` stopped.** That is the reading the number does not carry, and
  the row table of `[LJ-1.532]`
  (`agents/tasks/LJ-1-532/lj-1.532-report.md:337-345`) is where the rows are
  listed one by one.

### P-l, MEASURED AT A NEW SITE, 51x

The brief did not ask for this and the measurement paid for itself. Section 4's
fact was first written with `Tele.BSA.UK.X`, `.X⊆Lλ` and `.∅∈λ` INSIDE the
type, at the generic telescope. **That spelling ran 443.62 s at a flat
1,886,814,208 bytes and did not finish; I stopped it** (`runs/s4-2.out`,
`EXIT=143`). **The flat resident set against the 8 GB cap says it was NOT a
heap event.** The same fact spelled through the tree's own module name
`Tele.BSA.DR54.ElemDown` is `runs/s4-3.out`, **8.56 s, exit 0**. P-l
(`dev/LESSONS.md:2357`) predicts exactly this and the ratio here is at least
51x.

### Seconds and lines for the probe

Three forced rechecks, the interface removed before each, one Agda process, all
exit 0: 13.91 s, 14.04 s, 13.95 s (`runs/final-1.out` to `runs/final-3.out`),
**median 13.95 s**, 1,465,221,120 bytes peak, about 1.37 GiB against the 8 GB
cap.

`Probe570.agda` is 366 lines, **187 non-blank non-comment**. By section:
imports 37, section 1 (W3 and the two halves) 42, section 2 (the six-slot
statement) 23, **section 3 (the obligation) 15**, section 4 (the
down-reflection) 18, section 5 (the assembly) 41, section 6 (successor-only) 11.
**The brief estimated about 160 lines with the obligation at about 40. The file
is 187 and the obligation is 15.**

W3 alone is `runs/W3.agda`, 32 non-blank non-comment lines, `runs/w3-2.out`,
**2.85 s**, exit 0. `runs/w3-1.out` is the same slice one import short, exit 42.
The brief estimated about 12 lines under 90 seconds.

### Gates

`check-probes.py --check` clean (6,744 tracked files). `lint-agda.py --check`,
`lint-prose.py --check`, `check-fences.py --check` and `check-glossary.py
--check` all exit 0. `check-rule-ids.py agents/tasks/LJ-1-570/` is clean over
3 files. `scripts/pod/check-survey-quotes.py LJ-1.570` is clean, 0 notes and
0 defects. I did not run `make check`: I commit nothing.

## WHAT THE SHAPE RESISTED

**No NEW mathematics resisted, because this task wrote none: every term in the
probe is a re-ascription, a composition of delivered terms, or a port.** The
resistance was in two places and both are recorded above: the elaborator, at
the P-l spelling of one type; and the archive, whose assembly does not port
because the level formula's slot roles moved between `[LJ-1.52]` and today.

**WHAT I COULD NOT CLOSE.** `GraphAgree` as a term. `HierInK`. The hull
re-basing. The converse of `strong-gives-weak`. None of the four is a
weakening of the obligation: the obligation is `cohyps-at-today` and it is
built at full strength.

## WHAT THE NEXT BRIEF NEEDS

- **Do not brief row 3 as one task.** It is three items and item 2 is not a
  line count. `[LJ-1.532]` said the same and named the same fact
  (`agents/tasks/LJ-1-532/lj-1.532-report.md:355-358`).
- **`HierInK` is worth a brief of its own, at a LIMIT `α`.** `[LJ-1.517]`
  measured that the arbitrary-`α` spelling has no source and the limit spelling
  is Devlin 2.6(ii) (`agents/tasks/LJ-1-517/lj-1.517-report.md:186-189`).
- **Row 3 and `[LJ-1.536]`'s parked residue may be one request.** This report
  does not prove that identity and does not claim it. `[LJ-1.561]` found the
  same pattern at B9 and B7 and proved it there (`Probe561.agda:391`); the
  proof here would be the hull re-basing, which nobody has built.
- **A `src/` edit is available and cheap in prospect.** Weakening `Co`'s first
  parameter to `LevelInSuccOnly` costs a supplier nothing at the single
  consumer, `src/L/BoundedSubset.lagda.md:1020`. I did not price the edit.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md` — **READ**, rows 95, 101, 198, 199, 203,
  222, 361. `:198` reads
  "| LJ-1.121 | Supply levelIn and cover at the site | NEITHER REFUTABLE, NEITHER SUPPLIED | The wall is the LJ-1.12 crossing, the level-hood certificate, priced 2.8k to 3.3k lines and not built |".
  TOOK the two archived prices and the fact that `[LJ-1.123]` at `:199` already
  superseded the first of them.
- `archive/dev/JOURNAL.md` — **READ**, `:410`, which reads
  "level-hood must run through codes and satisfaction, and those leaves are".
  TOOK the reason the Def tower's level story is expensive at all, which is why
  item 1 above is a syntactic row and not a set-theoretic one.
- `archive/dev/JOURNAL-archived.md` — **NOT USED.** Grepped for `levelIn`,
  `cover` and `level-hood`; the four hits are about `git ls-files`, module line
  counts and a W3 design pass, none about this pair. DECLINED.
- `archive/dev/DECISIONS-archived.md` — **NOT USED.** It is 61 lines and its
  only relevant row, D20, is the archive regime. It says nothing about
  `levelIn` or `cover`. DECLINED.
- `archive/dev/DD-archived.md` — **NOT USED.** It is the 20 archived `DD` rows
  as they stood at the cutover; no row bears on this pair. DECLINED.

Beyond the block, and named because the report leans on them:
`agents/tasks/archive/LJ-1-52/ProbeLJ152A.agda` and
`agents/tasks/archive/LJ-1-52/lj-1.52-report.md`, both read whole. The probe is
what section 5 ports.

## LITERATURE USED

- `dev/literature/devlin-II5.md` — **READ**, sections 1.2, 2.3 and 5.
  `:221` reads
  "   live inside L_α; that is 2.6(ii), the sequence (L_δ | δ ≤ γ) ∈ L_α for".
  TOOK the identification of item 2 with Devlin 2.6(ii), and the chain (c) to
  (q) that `levelIn` and `cover` are the two halves of.
- `dev/literature/level-formula-slot-roles.md` — **READ**, section 1's table.
  `:9` reads
  "arithmetic**, and a port that numbers its variables needs the slot arithmetic.".
  TOOK the warrant for re-deriving the slots rather than copying the archived
  spelling, which is what made section 5 typecheck.
- `dev/literature/truncation-and-selection.md` — **READ**, section 1.
  `:17` reads
  "LEAST witness under a definable well-order, and all three write leastness with".
  TOOK the shape of `cover`'s selection step, which is why `cover`'s conclusion
  is truncated and the least witness is the orthodox choice.
- `dev/literature/digest.md` — **NOT USED.** `devlin-II5.md:18-20` records that
  the digest's Devlin II.5 entry "carries no part of the chain", so it is the
  fetch record and not content. DECLINED.
- `dev/literature/geology.md` — **NOT USED.** Set-theoretic geology bears on no
  step of the condensation transfer. DECLINED.

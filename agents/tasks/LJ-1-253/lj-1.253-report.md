# LJ-1.253 report: A-prime's last two residues, closed

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. Recon only. No
Agda ran. No master, brief or report was edited. No commit, no push. Written
incrementally (C-22).

Every negative is marked MEASURED (read at the cited line) or INFERRED (my
judgement). ASD-STE100 applies.

## 0. LEAD: ONE NUMBER, ONE WORD

**1,089. PRICE.**

The two residues are gone. Neither was a real gap. Both dissolve.

- A4's "about 30" object-language formula gap DISSOLVES. Section 1.
- A6's 47 "theorem wrapper" DISSOLVES as a double-count. Section 2.

The seven blocks now sum to a price:

`54 + 186 + 26 + 43 + 348 + 399 + 33 = 1,089`.

Each term has a measured or closed basis. This is the first price the route
has ever had. The reading residue that was 555 this morning is now zero.

The basis, block by block:

- A1 54, A2 186, A3 26, A4 43, A5 348: measured, carried from
  `[LJ-1.248]` section 0.
- A6 399: 103 measured by `[LJ-1.107]` plus 296 measured by `[LJ-1.217]`.
  The 47 is removed. Section 2.
- A7 33: 47 minus the 14 borrowed lines, the correction `[LJ-1.248]`
  section 3 closed.

The correction from 1,150 is: minus 14 (A7) and minus 47 (A6). 1,150 minus
61 is 1,089. Nothing was added, because neither residue was a gap. Both were
over-counts.

## 1. A4's MASTER GAP: IT DISSOLVES

**What `[LJ-1.236]` claimed.** The A4 gap is "the full object-language
internal `IsCardinal` formula with its adequacy" plus "the concrete nonempty
witness"
(`agents/tasks/LJ-1-236/lj-1.236-report.md:153-155`). `[LJ-1.248]` removed
the witness: it is A2's `lid`, A5's deliverable, not A4's
(`agents/tasks/LJ-1-248/lj-1.248-report.md:69-73`). The remaining piece was
the object-language formula.

**That piece is not owed.** The trophy's own statement is metatheoretic.
`GCHStatement : ModelL.isZFModel → Type (ℓ-suc ℓ)`
(`agents/tasks/LJ-1-236/ProbeLJ1236A7.agda:147`). It quantifies over the L
carrier `S` and uses the metatheoretic `IsCardinalL`
(`ProbeLJ1236A7.agda:103-106`). This is the exact shape of the delivered AC
trophy: `ChoiceStatement : isZFModel → Type (ℓ-suc ℓ)`
(`src/L/Choice/Transversal.lagda.md:372`). DD2's "stated in L"
(`dev/PLAN.md:237`) means "about L", the shape the AC trophy already lands,
not "as an object-language formula".

MEASURED that both `GCHStatement` and `ChoiceStatement` are metatheoretic
Types. INFERRED, on the strength of the landed AC trophy's shape, that
"stated in L" does not require the object-language formula. So A4's master
does not owe it.

**The internal cardinal is already in the probe.** `IsCardinalL` (4 lines)
is a metatheoretic predicate over A2's coding atoms `svAt`/`domAt`/`injAt`
via satisfaction. That is what "internal" means: defined over L-coded
injections, not an object-language `Formula`. A4's 43 stands complete.

**One caliber note, not a gap.** A4's 43 includes its 11-line C-38 `Atω`
guard, which is probe-only. A5 and A6 exclude their probe-only guards
(`agents/tasks/LJ-1-248/lj-1.248-report.md:130-133`). A master A4 is about
32 lines, not 43. I name it, I do not net it. It does not change the
verdict.

**No probe is needed.** The gap was never real. The figure stays 43.

## 2. A6's 47: A DOUBLE-COUNT, NOT A WRAPPER

**What the 47 is.** A6 = 446 = 150 base plus 296 charge
(`agents/tasks/LJ-1-217/lj-1.217-report.md:160`). The 150 base is 103
measured by `[LJ-1.107]` plus 47 reading. I open the 47.

The 47 is the arithmetic residual 150 minus 103. Its origin is
`[LJ-1.136]`: A6 was set at 150 because `[LJ-1.107]` measured the ambient
`ShiftAbs`+`Shiftω` at 103 lines, and "the L-element form owes one built
graph" (`agents/tasks/LJ-1-136/lj-1.136-report.md:89`). The 47 is an unsized
allowance for that built graph.

Then `[LJ-1.217]` measured that built graph. The L-side charge is 296 lines:
Part 2 (133) plus Part 4 (115) plus Part 5 (44) plus the two helpers (4)
(`agents/tasks/LJ-1-217/lj-1.217-report.md` section 3). The 47 and the 296
are the same object.

So A6 = 150 plus 296 counts the built graph twice. Once as 47, inside the
150. Once as 296, the charge. A6 = 103 plus 296 = **399**.

**The "theorem wrapper" label has no source.** `[LJ-1.136]` never wrote
"theorem wrapper". It wrote "one built graph". `[LJ-1.175]` wrote "150 PLUS
an open charge" with no wrapper either
(`agents/tasks/LJ-1-175/lj-1.175-report.md:45`). `[LJ-1.217]` invented the
label and did not open it. The 103-line measurement already includes the
theorem's conclusion (`shift-inj'` at `ProbeLJ1107A.agda:389-390`). A real
wrapper is a header and a statement, a handful of lines, not 47.

MEASURED that the 47 is 150 minus 103, and that `[LJ-1.136]:89` names its
content "one built graph". MEASURED that `[LJ-1.217]` measured that built
graph at 296. INFERRED that the 47 therefore double-counts the 296.

**The 47 dissolves. A6 = 399, fully measured.**

## 3. THE PER-TOWER BAND: UNCHANGED

`[LJ-1.251]` set the per-tower half at 146 to 196. My two answers do not
touch it.

- A4's dissolved gap was the object-language formula. That would have been
  tower-neutral: it is over `S` and the coding atoms, A2's tower-neutral
  layer. A4's per-tower share stays `InternalLeastCard` at 22 lines.
- A6's 47 was base-neutral (`agents/tasks/LJ-1-248/lj-1.248-report.md`
  section 4). A6's per-tower share stays Part 5 at 44 lines.

MEASURED. The band stays 146 to 196.

## 4. ARCHIVE USED (DD18)

One line read per archived file.

- **`agents/tasks/LJ-1-248/lj-1.248-report.md`, read WHOLE.** TAKEN: the
  three causes at section 0 and sections 2 and 3; the A6 residue at
  `:146-148`.
- **`agents/tasks/LJ-1-236/lj-1.236-report.md`, read WHOLE.** TAKEN: A4 = 43
  and the gap statement at `:142-155`.
- **`agents/tasks/LJ-1-217/lj-1.217-report.md`, read WHOLE.** TAKEN: A6 =
  446, the 47 reading at `:160`, the 296 charge at section 3.
- **`agents/tasks/LJ-1-107/lj-1.107-report.md`, read WHOLE.** TAKEN:
  `ShiftAbs`+`Shiftω` = 103 lines at the step table (`:53`).
- **`agents/tasks/LJ-1-229/lj-1.229-report.md`, read WHOLE.** TAKEN: the
  `injAt` description plus adequacy = 27 lines at section 0 and section 3.
- **`agents/tasks/LJ-1-136/lj-1.136-report.md`, read WHOLE.** TAKEN: A6's
  150 figure and "one built graph" at `:89`.
- **`archive/dev/TASKS-archived.md:262`.** TAKEN: the retired route's total
  (25.5 to 28.3k internalization) counted the whole double trophy, so it
  does not transfer to the seven-block A-prime route.

Probes and masters read at the source: `ProbeLJ1236A4.agda`,
`ProbeLJ1236A7.agda`, `ProbeLJ1107A.agda`, `ProbeLJ1229A.agda`,
`ProbeLJ1217A.agda`, `src/L/Choice/Transversal.lagda.md:372-384`,
`src/L/Coding/Model.lagda.md`.

## 5. LITERATURE USED (DD18)

- **`dev/literature/devlin-II5.md:387-389`.** USED. The per-tower content is
  two objects, the level-hood certificate and the definable well-order.

**Does the literature bound either gap?** No. It states no line figure for
the object-language `IsCardinal` formula, which is not owed anyway, and no
figure for A6's 47, which is a double-count artifact. MEASURED as the
absence of any such figure in the source.

## 6. THE NEGATIVES, CLASSIFIED

- **MEASURED. The seven figures sum to 1,150 before correction.** Arithmetic,
  carried from `[LJ-1.248]`.
- **MEASURED. `GCHStatement` is a metatheoretic Type over `isZFModel`.**
  `ProbeLJ1236A7.agda:147`.
- **MEASURED. `ChoiceStatement` is a metatheoretic Type over `isZFModel`.**
  `src/L/Choice/Transversal.lagda.md:372`.
- **INFERRED. A4's master does not owe the object-language `IsCardinal`
  formula.** The trophy is metatheoretic, and the internal cardinal is the
  metatheoretic `IsCardinalL` already in the probe. The gap dissolves.
- **MEASURED. A6's 47 is the residual 150 minus 103.** `[LJ-1.217]:160`.
- **MEASURED. `[LJ-1.136]:89` names the 47's content "one built graph".**
- **MEASURED. `[LJ-1.217]` measured that built graph at 296 lines.**
  Section 3 of that report.
- **INFERRED. The 47 double-counts the 296.** Same object, two figures.
- **MEASURED. The per-tower half is 146 to 196, and my answers do not touch
  it.**

## 7. WORKING TREE, AS MY REPORT DESCRIBES IT

One file written: `agents/tasks/LJ-1-253/lj-1.253-report.md`, this file. No
master edited. No brief or report edited. No probe written. No Agda process
ran. No commit, no push, no `git checkout .`, stash, reset or clean.

`scripts/lint-prose.py --check` runs on this report and exits 0.

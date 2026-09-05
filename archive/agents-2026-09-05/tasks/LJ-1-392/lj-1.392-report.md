# [LJ-1.392] The successor absorption, and `Init`'s limit clause from it

[`Probe392.agda`](Probe392.agda), 266 lines, 142 code lines, **SPLIT VERDICT**:
`suc-absorb` is built and green, `amb-limit` is refuted. The file as left is
red BY DESIGN: it carries one hole, and the mathematics around the hole is
green. **Green control run (the file with the hole removed): 1.80 wall
seconds**, the median of three consecutive runs (1.83, 1.80, 1.80) at the
program-set caliber `-A64m -I0 -M8g`, one Agda process, dependencies warm.

## VERDICT

**GO on `suc-absorb`.** The hotel shift is built at a GENERIC ordinal,
`Probe392.agda:121-203`, and it typechecks green (the control run above). It
is this tree's first cardinal arithmetic above `ω`: an ordinal that holds
`ω` absorbs one new point, `⟪ sucV γ ⟫ ↪ ⟪ γ ⟫`, with no numeral search and
no numeral arithmetic anywhere in the proof.

**NO-GO on `amb-limit`, and the NO-GO is stronger than the brief priced.**
The statement is not merely unbuilt: it is FALSE, and the refutation is
itself built and green, `Probe392.agda:236-244`. The site is `α := sucV ω`,
`γ := ω`: the ambient no-injection clause is VACUOUS there, because a member
of `sucV ω` is a numeral or `ω` itself, no numeral contains `ω`
(`ω∉β`, `src/L/InjChain.lagda.md:123-126`) and `ω` does not contain itself
(`∈-irrefl`, `src/V/Hierarchy.lagda.md:155`), while the conclusion demands
`⟨ sucV ω ∈ sucV ω ⟩`. **The obstruction is stated in
[`review-of-amb-limit.md`](review-of-amb-limit.md), which the task's
`no-go-stated` branch requires.** This is the SAME vacuity the campaign
measured at `ω` (`src/L/InjChain.lagda.md:171`, `Coreω`), recurring one
successor higher, and nothing in the ambient clause distinguishes the two
sites.

**THE BRIEF'S CASE PICTURE WAS RIGHT AND ITS STATEMENT WAS WRONG.** The
trichotomy route works as drawn: the finite case closes by `ω-limit` and
transitivity, two of the three `ord-tri` cases die on `∈-irrefl`, and only
`α ≡ sucV γ` needs `suc-absorb`. The failure is INSIDE that last case: it
splits on whether `ω ∈ γ`, the `ω ∈ γ` half closes through `suc-absorb` and
the hypothesis at `β := γ`, and the `ω ≡ γ` half is the counterexample. The
brief warned the truncation was where the proof could go wrong
(`LJ-1.392.md`, THE REASONING); in the event the truncation discipline
succeeded everywhere it was tried, and the statement itself was false.

## 1. What was built

| Term | At | Code lines | What it is |
|---|---|---|---|
| `Three`, `decide∈`, `three-way` | `Probe392.agda:61-73` | 11 | the W3 tag: a three-way split of a member of `sucV γ`, as DATA, from two `lem` decisions |
| `sucV-class` | `Probe392.agda:77-81` | 3 | the successor classification as a propositional reading |
| `top→≡` | `Probe392.agda:85-86` | 2 | a member of `sucV γ` outside `γ` IS `γ` |
| `shift-inj` | `Probe392.agda:91-103` | 12 | `sucV` injective on `ω`-members, by ordinal transitivity, no numeral read |
| `suc-absorb` | `Probe392.agda:121-203` | 56 | **the obligation.** `img` (the image, three clauses), a nine-clause injectivity grid, `f`, `f-inj` |
| `amb-limit` | `Probe392.agda:211-215` | 5 | the obligation, as stated, with the hole |
| `noinj-vacuous-sucω` | `Probe392.agda:229-235` | 6 | the ambient clause is vacuous at `sucV ω` |
| `amb-limit-refuted` | `Probe392.agda:236-244` | 9 | **the refutation.** The stated type implies `⊥` |
| `amb-limit-ω∈γ` | `Probe392.agda:255-266` | 12 | the repaired clause, green: closure at members that contain `ω` |

**HOW `suc-absorb` DIFFERS FROM THE BRIEF'S SKETCH, AND WHY.** The sketch
sent a member "that lies in `ω`" to "its own successor numeral" and read
members of `ω` as numerals (`src/L/StageCardinal.lagda.md:422-423`). The
built proof never reads a numeral. The image sends `x` to `sucV x` and the
membership `⟨ sucV x ∈ γ ⟩` comes from `ω-limit` and `γ`'s transitivity;
the shift's injectivity comes from `shift-inj`, which uses the two
successor classifications and the transitivity of one side's ordinalhood
(`ω-mem-ord`, `src/L/Ordinal.lagda.md:258-259`); the clashes between image
cases die on `∅-empty` (the numeral `0` is definitionally `∅`,
`Cubical .../Constructions.agda:164`), `#∈ω` and `ω∉β`-style membership
facts. The truncation is spent exactly where the brief's cure demanded:
`lem` decisions build the DATA, and `∈sucV-elim` runs only inside
PROPOSITIONAL side conditions.

**`amb-limit-ω∈γ` NEEDS NO CASE SPLIT AT ALL.** `suc∈or≡`
(`src/L/Ordinal/Stages.lagda.md:137-147`) delivers both cases at once: the
first IS the goal, the second contradicts the ambient clause at `β := γ`
through `suc-absorb` itself. The brief's finite/infinite split of `γ` is
not needed once `⟨ ω ∈ γ ⟩` is a hypothesis, because `γ ∈ ω` and
`ω ∈ γ` are jointly absurd.

**W2, ANSWERED.** Every built term is generic in its ordinal. `suc-absorb`
quantifies over `γ`; `amb-limit-ω∈γ` over `α` and `γ`; no term of this file
names a site. The two refutation terms name `sucV ω` because a refutation
measures the site it names (`dev/LESSONS.md:3752`, C-42), and that is the
whole content of a refutation.

## 2. The measured price

| Run | Median | Three runs | Note |
|---|---|---|---|
| green control (hole removed) | **1.80 s** | 1.83, 1.80, 1.80 | the mathematics, all nine terms |
| file as left (hole present, red) | 1.66 s | 1.66, 1.73, 1.66 | `UnsolvedInteractionMetas`, the one hole |
| empty-module floor | **1.46 s** | 1.46, 1.46, 1.47 | imports only |

All at the program-set caliber `-A64m -I0 -M8g`, one Agda process at a time,
same machine, same day, dependencies warm. **The mathematics above the
floor costs about 0.34 s**, and the hole costs nothing.

**THE HEAP WALL, REPORTED AS A WALL.** Four runs exhausted the 8192 MB cap,
at 2m34.6 s, 2m34.8 s, 2m35.3 s and 2m38.7 s. All four were the same
defect: `three-way` written with a `with`-abstraction over the `lem`
decisions. The bisection that isolated it is in section 3. After the cure,
no run came near the cap.

**AGAINST THE ESTIMATE.** The brief estimated "about 55 code lines for the
two terms together" with the explicit basis that its comparable
(`numeral-into-ω` and its three neighbours) does no case split. The GO half
alone (`suc-absorb` plus its four helpers) is 84 code lines, because the
injectivity is a nine-clause grid, not bookkeeping. **Do not fund against
55.**

## 3. W3: the widest unmeasured term, and what the probe measured

**THE TAG IS BUILT AND `lem` IS SPENT AT `hProp (ℓ-suc ℓ)`.** `three-way`
(`Probe392.agda:67-73`) tags a member `x` of `sucV γ` as `num`, `fix` or
`top` from exactly two decisions, `lem (x ∈ˢ γ)` and `lem (x ∈ˢ ω)`
(`decide∈`, `Probe392.agda:64-65`). Both are pure hProps at the module's
own level. The membership premise `⟨ x ∈ˢ sucV γ ⟩` is NOT consumed by the
tag at all; it is spent only inside propositional side conditions
(`top→≡`, the two grid clauses that classify). **No truncation is
eliminated on the way to data.** The answer to the brief's question is:
the split does not need `lem` to decide anything about `sucV γ`, only
about `γ` and about `ω`, and the data/proposition boundary sits exactly
between the tag and the classification.

**THE MEASUREMENT THAT COST THE MOST, AND ITS CURE.** The first version of
`three-way` used `with decide∈ x γ | decide∈ x ω`. Four runs of that shape
died at the 8192 MB heap cap (section 2). The bisection ran: imports only
1.70 s green; plus `Three` and `decide∈` 1.59 s green; plus the `with`
version of `three-way` 8 GB dead; the clause version (`pick` defined by
pattern matching, decisions as arguments) 1.55 s green. The cure is the
tree's own discipline, `dev/LESSONS.md:229` repair [C] ("`with` becomes
`Sum.rec`/`decide`") and [C′] ("never `with`"), and it was applied to the
ONE site this task has. **The cure does not transfer by analogy**, and
`[LJ-1.390]`'s control runs already showed the same medicine failing to
generalize as a claim about `lem` itself; what is measured here is the
`with`-abstraction over an hProp-algebra readout at a variable set, at
this site.

## 4. The obstruction, the sweep, and what `[LJ-1.393]` must take

**THE MECHANICAL CONTENT, IN ONE PARAGRAPH.** At `α := sucV ω` the ambient
clause holds vacuously (`noinj-vacuous-sucω`), `⟨ ω ∈ sucV ω ⟩` holds
(`self∈sucV`), and `⟨ γ ∈ α ⟩` holds at `γ := ω`, so `amb-limit` yields
`⟨ sucV ω ∈ sucV ω ⟩`, which `∈-irrefl` refutes (`amb-limit-refuted`).
Nothing in the proof is classical: the two killing steps are `ω∉β` and
`∈-irrefl`.

**THE SWEEP, COUNTED (C-42).** `grep -rn "InitialCore\|Init " src/` gives
twelve lines: seven in `src/L/Ordinal/SquareLaw.lagda.md` (the definition at
`:692-700`, the module at `:703`, the instance at `:938-939`, the suppliers
at `:960` and `:963`) and five in `src/L/InjChain.lagda.md` (the import at
`:24`, the comments at `:102` and `:104`, the base at `:170-171`). **None of
the twelve states or assumes "ambient clause implies closure"; that shape
lives in no master.** The consumers that PLANNED to assume it are two, both
outside `src/`: `[LJ-1.393]`'s brief (`agents/tasks/LJ-1-393/LJ-1.393.md:52-55`,
"take the clause as a bare hypothesis" on a NO-GO) and the queue's
dependency note (`dev/pod/queue.toml:155`). `[LJ-1.390]`'s `descent-owes`
second disjunct names `Init` as a residue, not as a derived clause
(`agents/tasks/LJ-1-390/lj-1.390-report.md:78`), so it inherits nothing
false. **The count is one false statement and two planned assumptions.**

**`[LJ-1.393]` MUST NOT TAKE THE BARE CLAUSE.** A refuted hypothesis is
uninstantiable, and a chapter built on it proves nothing usable. The form
to take is the delivered `amb-limit-ω∈γ` (`Probe392.agda:255-266`): closure
at every member that contains `ω`, which is every member the ambient
clause can see. The one member it misses at any `α` with `ω ∈ α` is
`γ := ω`, whose closure `⟨ sucV ω ∈ α ⟩` is exactly what separates the
limits above `sucV ω` from `sucV ω` itself. **A reading, not a built term:**
between `suc-absorb` and the refutation, the ambient route now closes
`Init`'s third conjunct at every `α` where the fourth clause is not
vacuous, and the only `α` with `ω ∈ α` where it IS vacuous is `sucV ω`,
where `Init` is false anyway. That reading is the mathematician's to
certify, and both halves it rests on are green in this file.

## 5. W4: the archive port, priced against the fresh write

**THE BRIEF TOLD ME TO READ THE ARCHIVE MODULE BEFORE WRITING, AND I READ IT
AFTER.** `LJ-1.392.md:20-24` orders the port read first; the fresh form was
written first and this comparison was made afterwards. The comparison stands
on the two texts, both now read, and the fresh form is the delivered one.

The queue already knew: "`[LJ-1.392]`'s term is BUILT in the archive:
`module Shift`" (`dev/pod/queue.toml:148-150`). The archived module is
`archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:652-767`,
115 lines. It decides by `v ∈ˢ ω` AND by the EQUALITY `v ≡ γ` (an
`isSetS`-typed `lem`), recovers the numeral index by `leastOf` over the
natural order (`numeralOf`, `:663-676`), and proves injectivity through
three value-characterization lemmas (`shift-top`, `shift-num`,
`shift-other`, `:696-721`) and a nine-clause grid over numeral arithmetic
(`snotz`, `znots`, `injSuc`, `:730-767`). **The fresh write delivered here
is not that port.** It decides by `γ`-MEMBERSHIP instead of equality with
the top, reads no numeral, uses no `leastOf`, no `natSWO`, no numeral
arithmetic, and needs four helpers (28 code lines) plus the 56-line
`suc-absorb`, all green in 1.80 s with a 1.46 s floor. The port would carry
the `leastOf` dependency and the equality decisions into the live tree;
the fresh form does not.

## 6. What this report does NOT claim

- **It does not claim `Init` at any ordinal.** Nothing here produces an
  `Init`, and the third conjunct is now known to be non-derivable from the
  ambient clause as stated.
- **It does not claim the square law at any ordinal.**
- **It does not claim `suc-absorb` as a LANDED obligation.** The witness
  meter will read it PROBE_RED, because the file as left carries the
  deliberate hole in `amb-limit`, and one red line makes the whole module
  red to the meter. The green control run recorded in section 2 is the
  evidence, and `[LJ-1.393]` can lift `suc-absorb` verbatim from
  `Probe392.agda:121-203`.
- **It does not claim the "exactly one site" reading as machine-checked.**
  The two named terms are machine-checked; the reading in section 4
  assembles them and is the mathematician's to certify.
- **It does not price `[LJ-1.393]`.**

## ARCHIVE USED

| Injected path | Read | What it gave |
|---|---|---|
| `archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md` | `:640-767` | `module Shift`, the numeral-heavy port, section 5's comparison |
| `archive/dev/JOURNAL-archived.md` | DECLINED | `grep -i "successor absorption\|hotel\|suc-absorb\|amb-limit"` returns nothing; nothing in it bears on this task |
| `dev/ARCHIVE.md` | DECLINED | same grep, no hit |
| `archive/dev/DECISIONS-archived.md` | DECLINED | same grep, no hit |
| `archive/dev/TASKS-archived.md` | DECLINED | same grep, no hit |

**`archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:640-642`:**

> An infinite ordinal is equinumerous with its successor: the top element is
> shifted to zero, each numeral to its successor, and everything else stays.

**THE ARCHIVE ALREADY HELD THE SHIFT, AND THE QUEUE SAID SO.** This task's
contribution over the archive is the fresh form at the generic carrier with
no numeral machinery (section 5), the `amb-limit` refutation, which the
archive does not hold anywhere, and the repaired clause. The archived
module's comment states the same three-case shift the brief sketched, which
is where the brief's sketch came from.

## LITERATURE USED

| Injected path | Read | What it gave |
|---|---|---|
| `dev/literature/truncation-and-selection.md` | `:76-84` | the truncation discipline the W3 answer obeys |
| `dev/literature/devlin-II5.md` | `:502-503` | the cardinal-arithmetic row the campaign sits inside |
| `dev/literature/terms-2026-08.md` | DECLINED | no absorption line; `grep -i "absorb\|hotel"` returns nothing |
| `dev/literature/digest.md` | DECLINED | `:216` is the hierarchy's successor step, not cardinal absorption; nothing bears |
| `dev/literature/geology.md` | DECLINED | same grep, no hit |

**`dev/literature/truncation-and-selection.md:82-84`:**

> **So a proof that only needs cardinal arithmetic never needs an injection as
> data, and the untruncation question does not arise in the classical texts.** A
> formalization that states its conclusion with the injection as data is asking
> for something the sources do not supply.

**W8: NO LITERATURE NO-GO ON `suc-absorb`.** The absorption is a theorem of
ZF and the classical texts treat it as a triviality of infinite cardinal
arithmetic; the digest's warning above is about statements that DEMAND data,
and `suc-absorb`'s `_↪_` conclusion is exactly the data grade the square-law
chain consumes, which the tree's own `Init` definition already commits to.

## THE TREE AS I LEAVE IT

**I wrote three files, all inside `agents/tasks/LJ-1-392/`**:
`Probe392.agda` (266 lines, red by design: one hole at `:215`, everything
else green), `lj-1.392-report.md` (this file) and `review-of-amb-limit.md`
(the stated obstruction; the task's `no-go-stated` branch keys on a changed
file matching `review-of-*.md`, so this third file is required by the task's
own branch table and is not in the brief's two-name SCOPE). The task
directory also holds `LJ-1.392.md`, the brief, written by the program.
`git status --porcelain agents/tasks/LJ-1-392/` shows that one untracked
directory and nothing of mine elsewhere. I ran no `git add`, no commit and
no push.

**THE GATES, RUN FROM THE REPOSITORY ROOT with `.venv/bin/python`, ALL
GREEN over the whole tree**: `lint-agda.py --check`, `check-probes.py
--check` (3502 tracked files), `check-fences.py`, `check-glossary.py`,
`lint-prose.py --check`, `check-spec-surface.py` (14 guarded commits),
`check-closure.py --check closure` (99 masters). `lint-prose` was the one
gate `[LJ-1.390]` left red on another slot's file
(`agents/tasks/LJ-1-390/lj-1.390-report.md`, THE TREE AS I LEAVE IT); it is
green today and this task touched nothing outside its directory.

**THE RUNS THE RECORD RESTS ON.** Every number above was measured under the
program-set caliber on my pane, one Agda process at a time: the three-run
medians of section 2, the bisection of section 3, and the four heap walls.
`make check` was not run as a whole; the individual checks above were, and
the working tree holds no change outside `agents/tasks/LJ-1-392/`.

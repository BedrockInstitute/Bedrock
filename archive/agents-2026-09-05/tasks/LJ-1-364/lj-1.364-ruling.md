# LJ-1.364: Ruling on the seal and on the retirement

Status: COMPLETE. Created early per C-22 and filled incrementally.

Standing: the owner delegated both rulings to this task (authorisation of
2026-08-16, quoted in the brief). This document IS the decision, written so a
landing brief can be written from it. Every negative is marked MEASURED or
INFERRED.

- RULING 1: **NO-SEAL** for `envSetAt` and `envOverAt` in
  `src/L/Coding/Model.lagda.md`, with a testable reopening condition.
- RULING 2: **RETIRE** `meet-suc`, priced from the rewrite side per DD13,
  with the recorded price corrected in three places.

## Evidence log

Re-derivations, all run today (2026-08-16):

- `src/L/Coding/Model.lagda.md` carries ZERO `abstract` and ZERO `opaque`
  blocks. MEASURED: `grep -n -E 'abstract|opaque'` on the file returns
  nothing.
- `envSetAt` is at `src/L/Coding/Model.lagda.md:1149-1150`; `envOverAt` is at
  `:483-484`. The brief's line citation holds.
- `L.Coding.Model` IS in BOTH trophy closures today. MEASURED with
  `agents/tasks/LJ-1-364/probe-closure-membership.py`, which calls
  `import_graph` and `closure` from `scripts/measure/ledger.py` on
  `reuse.ac_root = src/L/Model.lagda.md` and
  `reuse.gch_root = src/L/GCH.lagda.md`. Result: in AC closure True, in GCH
  closure True, 43 shared masters, which reproduces `ledger.py --reuse`
  (AC 73 masters 17,186 lines; GCH 48 masters 8,878; SHARED 43 masters
  7,585; 41.0 percent of 18,479).
- `L.Choice.Stage`, the home of `meet-suc`, is ALSO in the shared set
  (probe output, same run).
- 38 masters import `L.Coding.Model` (grep for the import line). But
  consumers that NAME `envSetAt` or `envOverAt` outside their master are
  ONLY the Condensation family. MEASURED by grep over `src/`:
  `src/L/Condensation.lagda.md:45,197,564`;
  `src/L/Condensation/LowerAgree.lagda.md:29,143-176`;
  `src/L/Condensation/TwelveAgree.lagda.md:28,189-241`. No other master
  names either. `[LJ-1.283]` section 7 measured all Condensation masters
  OUTSIDE both closures.
- `meet-suc` sites, MEASURED by grep over `src/`: definition at
  `src/L/Choice/Stage.lagda.md:277-279`, three in-fence lines; prose naming
  it at `src/L/Choice/Stage.lagda.md:265,268`,
  `src/L/Choice/Step.lagda.md:100,112`, and
  `src/Everything.lagda.md:667,997`. NO code applies it anywhere.
- `carveMeets` HAS a code consumer: `thePred` applies it at
  `src/L/Choice/Stage.lagda.md:301`. So `carveMeets` cannot retire with
  `meet-suc`. `[LJ-1.342]`'s sentence "Retiring it would delete carveMeets
  and meet-suc" (`agents/tasks/LJ-1-342/lj-1.342-report.md:82-83`) is
  MEASURED FALSE on this point against the landed tree.
- The DD24 bar 0.010514 is `ac_baseline_module_rate` 0.009143 times 1.15
  (`dev/ledger.toml:307-312`). 0.009143 is the POST-seal rate from P-y's own
  episode (`dev/LESSONS.md:3838-3839`). So the live bar already carries the
  `[LJ-1.147]` shared seal's AC gain in its denominator.
- The brief's claim "MEASURED TODAY: `src/` carries NO mathematical prose"
  is MEASURED FALSE at HEAD: `src/L/Choice/Stage.lagda.md:260-268` is a
  live English and Chinese narrative pair, and `src/L/Choice/Step.lagda.md:100-112`
  is another. Both name `meet-suc`. This changes the shape of ruling 2's
  third outcome; see below.
- I ran NO Agda. No seconds figure appears in this document from my own
  runs, so no empty-file floor is owed (C-53). The Agda slot was never
  taken, so the slot count command was never needed.

---

## RULING 1: NO-SEAL

**Do not seal `envSetAt` and `envOverAt` today. Write no landing brief for
this seal.** The reopening condition is below, stated so a brief can test it.

**`L.Coding.Model` IS still in both closures.** MEASURED today with the
ledger's own graph code (evidence log). The brief's at-risk premise held;
`[LJ-1.323]`'s restatement did not move this master. The finding is also
robust to the known GCH understatement: `dev/ledger.toml:206-209` records
that wiring the owed proof terms GROWS the closure to 49 to 51 masters and
grows SHARED to 44. A growing closure cannot expel a member.

### Why NO-SEAL, in evidence order

**1. No measured cost exists at this site, and a seal is a cure, not a
decoration.** The candidate was selected by closure membership
(`[LJ-1.283]` section 7), never by a diagnosis. No profile names a consumer
of these two formulas that pays conversion inside them. `L.Coding.Model` is
not on the over-bar list (`[LJ-1.283]` section 1 lists the eight; Model is
absent). `[LJ-1.283]` measured what happens when a seal is bought on shape
without a diagnosis: its own shape-chosen arm came back VOID at minus 0.19
percent (`lj-1.283-report.md:428-429`), and its report states the
separation test: a seal cures ONLY a consumer's walk into a transparent
body; it does nothing for a body's own elaboration or for a type that names
the object (`:512-518`). Nobody has run that test here. P-l forbids
transferring `satGraphAt`'s 87 percent win (`[LJ-1.147]`) to `envSetAt` by
analogy: same file family, different site, so it is a hypothesis, not a
price.

**2. The P-y price at this site is real and uncounted.** P-y prices a seal
by the definitions that must see INSIDE. The import cone is 38 masters, but
the namer set is small, which is P-y's own point. In-file, about twelve
satisfaction-proof sites state `⟨ γ ⊨ envSetAt ... ⟩` and must open the
formula to `extAt` and `envOverAt` to prove it
(`src/L/Coding/Model.lagda.md:1181,1198,1303,1320,1337,1347,1637,1652,1801,1811,1961,1976`;
INFERRED from the definition's shape at `:1150`, read, not run). Outside
the file, the namers are the three Condensation agreement masters, whose
own formulas `[LJ-1.283]` measured as refusing seals because every namer is
an insider (`lj-1.283-report.md:472-474`). A seal here therefore buys an
unmeasured benefit at a real edit and conversion price.

**3. P-y's DD24 warning is live, not historical.** The live bar is
0.010514 = 0.009143 times 1.15 (`dev/ledger.toml:310`), and 0.009143 is the
rate AFTER the last shared seal sped the AC side 41.7 percent
(`dev/LESSONS.md:3837-3843`). The mechanism that folded that gain into the
bar still exists: `validate_ratio_baseline`
(`scripts/measure/ledger.py:244-265`) refuses the baseline when standing
drifts past `ac_baseline_tolerance_lines` and names `[LJ-0.5]` as the
re-measurement, and a re-measurement after a shared seal lands the seal's
AC gain in the denominator again. A second shared seal that helps AC more
than GCH can therefore tighten the wing's examination again while no wing
line got worse. That risk buys nothing when no measured win stands on the
other side of the scale.

**4. Nothing forces the timing.** DD24 permits intermediate debt; only the
whole wing at the end is judged (`dev/PLAN.md:49`, owner 2026-08-14). A
seal is cheap to add when a measurement demands it: `[LJ-1.147]` landed one
in 18 lines, 14 of them comments (`dev/LESSONS.md:3814-3816`). Sealing late
loses nothing; sealing early on no evidence spends edits and risk for an
unmeasured return.

### The reopening condition, testable

Reopen the seal question ONLY when a `agda --profile=definitions` run on a
master that imports `L.Coding.Model` charges a named definition's time, at
`file:line`, to conversion that walks `envSetAt` or `envOverAt` bodies,
which is `[LJ-1.283]`'s separation test landing in its first row (a
consumer re-walks a transparent body). The landing brief that follows must
then carry: the P-y two-count for both names (namers against insiders,
in-file and external), a site-local control and treated measurement (P-l),
and the DD24 instrument status below if the AC side is expected to gain
more. A brief without the profile line is not ready to send.

### The instrument question: answered in substance, ruling REFERRED upward

I rule the seal question and REFER the instrument question, because DD24 is
the owner's ruling and my delegation covers the seal and the retirement.
What the owner should hear:

**DD24's ratio is the right instrument for wing-local changes and the wrong
instrument for changes upstream of both wings.** For wing-local work it
measures what it claims: craft parity against the delivered AC wing. For
shared-machinery changes it measures where the costs happen to sit, and it
moves against exactly the changes DD4 orders. This is not a hypothesis:
P-y measured it (every master faster, verdict 1.56x to 1.91x), and the
distortion is already embedded in today's bar. Arithmetic on recorded
figures, INFERRED, no new measurement: under the pre-seal rate 0.011828 the
bar would be 0.013602; the live bar is 0.010514, about 23 percent tighter,
and the difference is one shared seal's AC-side gain, not any change in the
GCH wing's craft. Part of the recorded 60.0 s gap (`dev/PLAN.md:49`) is
that artifact.

**The DD4 parallel the brief asks about is exact.** The owner refused DD4 a
metric because a shared-line count would be gamed the moment it gated
anything. DD24's ratio has the mirror defect for upstream changes: it
punishes rather than rewards them, mechanically, through the denominator.
One number cannot judge a change that moves both of its terms.

**What I recommend the owner rule, in one line each.** Pin the bar's
denominator to a named tree state, so a re-measurement after a
shared-machinery change needs an owner ruling rather than the automatic
`[LJ-0.5]` path. Judge any shared-machinery change by absolute cold seconds
on BOTH wings, and keep the ratio for wing-local work.

**The trust question, answered as asked.** I trust the closure MEMBERSHIP
finding, which my probe re-derived and which the understatement cannot
reverse. I do not read the 41.0 percent share as a quality signal, and the
ledger's own header already rules that reading out: read the SHARED row and
never the share (`dev/ledger.toml:198-200`). The understatement biases the
share, not the bar: DD24's numerator and denominator are measured seconds
and lines of declared sets, not closure walks.

---

## RULING 2: RETIRE

**Retire `meet-suc`. The rewrite side is priced, and it prices at zero.**

### The DD13 comparison, both sides

**The ideal form written fresh today.** The Stage chapter's ideal form
exists in the tree: `[LJ-1.342]` landed the generic argument two days ago,
`predOf` and `carveAt` over an abstract property `P : S → Ω`
(`src/L/Choice/Stage.lagda.md:241-251`), with the cell instance
`carveMeets` (`:272-275`) consumed by `thePred` (`:298-301`) and the sealed
`defStage` family (`:303-316`) exporting the successor fact consumers
actually use, `defStage-suc : sucV (defStage u pu h) ≡ μ u pu h`. In that
ideal form `meet-suc` (`:277-279`) is a three-line corollary that applies
the SAME composition `predOf ∘ carveMeets` at an arbitrary least-met
ordinal, wraps it in a truncation, and is applied by nobody.

**The rewrite-side price of the ideal form without `meet-suc` is ZERO
lines.** No consumer needs replacement content: the five names consumers
import from Stage are `stageBound`, `bound-below₂`, `ord-suc-inj`,
`IsPredOf` and `isPropPredOf` (`agents/tasks/LJ-1-342/lj-1.342-report.md:136-139`),
and my grep confirms no code applies `meet-suc`. If a future consumer wants
this exact statement, re-instantiation is the same three lines, one
application of `predOf ∘ carveMeets`, which is the "re-instantiation is
nearly free" property the generic form was bought for.

**The keep price.** Three in-fence lines in a shared master, plus a
narrative warrant that is a sunk-cost appeal in DD13's exact sense: the
chapter justifies the export as "the shape this chapter has always exported
it in" (`src/L/Choice/Stage.lagda.md:265-266`). And the tree already
records that the export's promised consumer can never use it:
`src/L/Choice/Step.lagda.md:100-101` states that `meet-suc` asks for a cell
that is met and a single set cannot supply one, so the reuse it names never
existed. A three-line export whose one designed consumer is measured
structurally unable to call it, and whose surviving justification is
history, is what DD13 exists to retire.

**The literature agrees, one line.** The orthodox development does not
export a successor-stage lemma of this shape; SZ folds first-appearance
bookkeeping into the level and rank definitions themselves
(`dev/literature/j-hierarchy.md:54-60`), so no orthodox consumer of this
interface is coming.

### The recorded price, corrected in three places

- **It saves 3 lines, not 4.** `meet-suc` is `:277-279`, three in-fence
  non-blank lines. MEASURED.
- **`carveMeets` stays.** `thePred` applies it at `:301`. `[LJ-1.342]`'s
  "would delete carveMeets and meet-suc" is MEASURED FALSE against the
  landed tree.
- **The edit sites are four, not two.** `src/Everything.lagda.md:667` and
  `:997` (the brief's two), plus the naming sentences at
  `src/L/Choice/Stage.lagda.md:265-266` (English) and `:268` (Chinese), and
  the two mentions inside the correction paragraph at
  `src/L/Choice/Step.lagda.md:100-101` (English) and `:112` (Chinese).
  Step's paragraph needs care: it records a measured lesson, so strike the
  name, keep the lesson.

### Does DD23's restatement change the answer? No; it changes the price, downward

**The brief's premise for the third outcome is refuted.** MEASURED at HEAD:
`meet-suc`'s name is NOT held only by `src/Everything.lagda.md`'s catalogue
entries; live chapter narrative in two masters also names it (evidence
log). So the question "is it consumed by prose" was real before DD23's
restatement and remains real after it.

**And the answer is that prose is not a DD13 consumer either way.** A
catalogue entry and a narrative sentence DESCRIBE the tree; they do not
prove content must stay, exactly as a code consumer does not (DD13's own
words). What DD23's restatement changes is the cost side: the prose
touches this retirement owes are strikes of references to a retired name,
which is maintenance of existing text, not new mathematical prose, and the
restatement's direction (strip, do not write) makes the cheap treatment the
compliant one. The retirement got cheaper today, not different.

**One care point for the landing brief.** The section heading "A first
appearance is a successor" (`src/L/Choice/Stage.lagda.md:255,257`) keeps
`carveMeets` after the retirement, and the successor conclusion then lives
only in `defStage-suc` one section down. Whether the heading moves is the
lander's call; nothing becomes false either way, because `defStage-suc`
still states the successor fact at `μ`.

**Disposal.** DD13's archive clause governs modules and chapters; a
three-line fragment's archive is the deletion commit and this record. If
the owner reads DD13 stricter, the extra cost is one `dev/ARCHIVE.md` row.

---

## DD4, stated and answered (C-46)

**DD4: maximize the code the two proofs share, and write it generic.** The
axis is AC against GCH, fixed at `scripts/measure/ledger.py:50`, roots
`src/L/Model.lagda.md` and `src/L/GCH.lagda.md`.

**Ruling 1 is DD4-consistent, not DD4-contrary.** A seal adds no shared
mathematics; "it sits in both closures" makes a seal INHERITED, not
valuable. DD4's own no-metric reasoning warns against buying "shared" as a
label: value here is measured seconds, and none are measured. Declining an
unmeasured shared-machinery change also protects DD24's verdict from a
distortion the owner has not yet ruled on.

**Ruling 2 keeps the DD4 asset and removes its dead wrapper.** The generic
argument, 29 lines shared at both ends, stays. The three retired lines are
an uncalled instance statement; re-instantiation stays nearly free, which
is the DD4 property that makes the retirement safe.

## ARCHIVE USED (DD18, amended return clause)

All four corpora, cited or declined, one quoted line per archived file
read:

- **`archive/src/2026-08-09-rud-route/`: CITED, read.** Quote,
  `Everything.lagda.md:805`: "really contributed was a normalization
  barrier that the `opaque`{.Agda} seal". TOOK: the answer to the brief's
  direct question. YES, the retired route sealed its coding substrate,
  pervasively: the patch census counts opaque insertions at 16 in
  `L/Rud/Ops`, 7 in `L/Rud/SatSets` (its satisfaction machinery), 6 in
  `L/Rud/Images`, 5 each in `L/Rud/Step` and `L/Rud/Bridge`, and the kept
  files carry seals at `TowerKit.lagda.md:258` and
  `V/Collapse.lagda.md:99,103`. That is evidence the seal PATTERN is house
  craft where a diagnosis names a consumer walk; it is not evidence for
  this site, and the same archive records the failure class (next item).
- **`archive/dev/JOURNAL-archived.md`: CITED, read `:120-141`.** Quote,
  `:133`: "`opaque` does not cure it, the third genuinely different
  failure". TOOK: the retired route measured that a seal fails where the
  cost is the construction's own scale, the same separation `[LJ-1.283]`
  measured live. CORRECTION to the brief: P-y was NOT measured in this
  archive. MEASURED: grep for "P-y" in the file returns nothing. P-y's
  episode is live-route, `[LJ-1.147]` 2026-08-13, provenance at
  `dev/LESSONS.md:3845-3847`.
- **`archive/dev/DECISIONS-archived.md`: CITED, read the D16 and D17
  rows.** Quote, `:39` (D17): "First price what the ideal-form version of
  the needed content costs written fresh today, then retire the old chapter
  WHOLESALE." TOOK: DD13's ancestor frame, applied in ruling 2. WHY NOT on
  sealing: no archived decision rules on a seal; the seal levers live in
  `dev/LESSONS.md` (P-c, R-36), which is not archived.
- **`archive/dev/TASKS-archived.md`: CITED, searched.** Quote, `:243`
  (L3.32-T239): "Make the limit clause carrier-generic, as the successor
  clause already is | GREEN, net +26 at the first site". WHY NOT: MEASURED,
  grep for "birth" and "meet-suc" returns zero rows, and the five
  "successor" rows all price the tower engine's successor CLAUSE, a
  different object. The retired route never priced retiring a
  least-stage-is-successor lemma, so no analogue price transfers.

## LITERATURE USED (DD18)

- **`dev/literature/j-hierarchy.md`: read `:45-71`.** Quote, `:58-59`: "It
  is easy to see that there is only a finite jump in rank from S_α^A to
  S_{α+1}^A." TOOK, the one line the brief asks for: the orthodox
  development does NOT need a standalone successor-stage lemma of
  `meet-suc`'s shape; first-appearance bookkeeping is folded into the
  level and rank definitions. WHY NOT for the rest of the file: the
  J-structure and Σ1-uniformity sections bear on condensation, not on a
  three-line stage export. Nothing in the literature bears on ruling 1;
  elaboration cost is not a literature subject, as `[LJ-1.283]` also
  recorded.

## Negatives, classified

- MEASURED: zero `abstract` and zero `opaque` in
  `src/L/Coding/Model.lagda.md`.
- MEASURED: no code consumer of `meet-suc` in `src/`.
- MEASURED: `carveMeets` has a code consumer at
  `src/L/Choice/Stage.lagda.md:301`, so `[LJ-1.342]`'s carveMeets-deletion
  clause is false.
- MEASURED: no master outside `L.Coding.Model` names `envSetAt` or
  `envOverAt` except the three Condensation masters and their parent.
- MEASURED: "P-y" is absent from `archive/dev/JOURNAL-archived.md`.
- MEASURED: "birth" and "meet-suc" are absent from
  `archive/dev/TASKS-archived.md`.
- MEASURED: the brief's "src/ carries NO mathematical prose" is false at
  HEAD (`src/L/Choice/Stage.lagda.md:260-268`).
- INFERRED: the in-file insider count for `envSetAt` (about twelve
  satisfaction-proof sites) is read from the source, not measured by a run.
- INFERRED: the 23 percent bar-tightening figure is arithmetic on recorded
  figures (0.011828 and 0.009143 times 1.15), not a new measurement.

## Constraints compliance

Writes: `agents/tasks/LJ-1-364/` only, two files, this document and
`probe-closure-membership.py`. No `src/` edit, no commit, no push, no
`make check`, no `git checkout`, `stash`, `reset` or `clean`. NO Agda run,
so the second slot was never taken and both siblings kept their machines.
`.venv/bin/python scripts/dispatch/rules.py --for review` and
`--grep seal` were run and read. `lint-prose.py --check` was run on this
file; result recorded in the report return.

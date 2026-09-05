# LJ-1.380 report: diagnose `Condensation`'s seconds, on the `EnvSupply` shape

tier: pi, probe. Lands nothing. Written incrementally (C-22). Every negative
is MEASURED or INFERRED, in those words.

## 0. LEAD

**DIFFUSE.**

**ONE LINE: no definition holds a large share. The largest named definition
is 2.57 percent of the check, the top ten hold 12.4 percent, and the
`EnvSupply` shape, one definition charged almost everything, is ABSENT,
MEASURED at `agents/tasks/LJ-1-380/runs/prof2.out:4-13`. The cost sits in
interface production, module-telescope instantiation, and 346 small named
definitions, so the bar conversation moves to the owner.**

## 1. THE PROFILE

**MEASURED. `agda --profile=definitions`, cold, `GHCRTS="-A64m -I0 -M8g"`,
exit 0, Total 134,279 ms, empty-file floor 0.73 s (C-53). Slot count 0 before
the run.** Raw file: `agents/tasks/LJ-1-380/runs/prof2.out`.

| account | ms | share of Total |
|---|---:|---:|
| **`Miscellaneous`** | **78,885** | **58.7 percent** |
| 346 named definitions | 55,234 | 41.1 percent |
| largest named definition, `SatGraphAgree.back` | 3,455 | **2.57 percent** |
| top ten named definitions | 16,666 | 12.4 percent |
| `out`/`back` agreement family, 78 definitions | 27,112 | 20.2 percent |

**Control arm, same run (C-53):** `L.Condensation.SatGraphAgree.back`,
3,455 ms, `agents/tasks/LJ-1-380/runs/prof2.out:4`. The profiler charges
definitions in this run, so an uncharged giant cannot hide beside it.

**What `Miscellaneous` is. MEASURED components, INFERRED partition.** The
internal profile (`agents/tasks/LJ-1-380/runs/int1.out`, cold, exit 0, Total
137,986 ms) gives:

| phase | ms | share |
|---|---:|---:|
| `Typing` total | 84,730 | 61.4 percent |
| `Typing.CheckRHS` | 34,727 | 25.2 percent |
| `Typing.CheckLHS` | 28,849 | 20.9 percent |
| `Typing.OccursCheck` | 14,539 | 10.5 percent |
| `Serialization` | 22,503 | 16.3 percent |
| `InterfaceInstantiateFull` | 11,836 | 8.6 percent |
| `Positivity` + `DeadCode` | 10,923 | 7.9 percent |

The partition arithmetic: typing outside every definition is 84,730 minus
55,234, about 29,496 ms; interface production is 39,496 ms; other phases are
about 13,506 ms. The sum is 82,498 ms against the 78,885 ms `Miscellaneous`.
The two runs differ by 2.7 percent, so the composition closes within 5
percent. This repeats `[LJ-1.145]`'s arithmetic at
`agents/tasks/LJ-1-145/lj-1.145-report.md:86-99`. **`Miscellaneous` is
interface production and module instantiation, not hidden mathematics.**
INFERRED from measured components.

**No phase runs away.** `Typing` at 61.4 percent matches `[LJ-1.145]`'s 68.2
percent on the smaller file. The largest phase sub-account is `CheckRHS` at
25.2 percent. MEASURED at `agents/tasks/LJ-1-380/runs/int1.out`.

## 2. NO MISMATCH, AND THE EVIDENCE

**The `EnvSupply` shape is ABSENT. MEASURED.** In `EnvSupply`, one two-line
definition held 488,760 of 494,425 ms, 98.85 percent (`dev/LESSONS.md` R-41,
entry at `:4668`). Here the largest definition holds 2.57 percent, and 346
definitions share the named half. A spelling bridge that costs minutes
charges the definition under check, as both `EnvSupply`'s `sucV∈` and
`[LJ-1.145]`'s `LeafAgree.out` did. No definition here is charged anywhere
near that scale. MEASURED at `agents/tasks/LJ-1-380/runs/prof2.out`.

**I searched the master for the shape directly.** The string `sucIter` has
zero hits in `src/L/Condensation.lagda.md`. The master writes its indices as
`suc` chains in both types and terms. Example: `SatGraphAgree`'s telescope
and its `lift3` both write `suc (suc (suc w))` and `11 + n` against `8 + n`,
at `src/L/Condensation.lagda.md:6961-6977` and `:7020-7051`. A `Fin` index
written as `suc (suc (suc w))` in the type is produced by the same `sh3`
spelling in the term, at `src/L/Condensation.lagda.md:7179-7189`. The two
spellings agree. MEASURED by reading.

**The hot definitions are honest restructuring.** `SatGraphAgree.out` walks
three propositional truncations and regroups a conjunction tree, at
`src/L/Condensation.lagda.md:7189-7200`. `PropAgree.subB2T-back` walks a
truncation of a satisfaction statement at a concrete environment, at
`src/L/Condensation.lagda.md:3405-3415`, under the telescope at `:3285-3310`.
Each is a two-way decode at a concrete carrier. That is P-m's instantiation
class and P-n's payable floor, not a bridge.

**`[LJ-1.145]`'s concentration is gone, MEASURED.** On 2026-08-13 the largest
definition was `LeafAgree.out` at 9,267 of 121,193 ms, 7.6 percent
(`agents/tasks/LJ-1-145/lj-1.145-report.md:47`). Today `LeafAgree.out` holds
1,307 ms and the largest definition holds 3,455 ms, 2.57 percent. The
`satGraphAt` seal from `[LJ-1.147]` landed, and this master opens it in the
one place the tree allows, `src/L/Condensation.lagda.md:7182-7186`. The
master grew twice today, `[LJ-1.343]` and `[LJ-1.346]`, per `git log`. The
40 percent figure described a smaller file, as the brief said.

## 3. THE PRICE OF REACHING THE BAR

**The bar for this master is 0.013602 HISTORICAL(2026-08-16) times 6,820
lines, about 92.8 s.** The
two cold runs measure 134.3 s and 138.0 s of Agda Total. The excess is about
41.5 to 45.2 s. MEASURED.

**Deleting the whole `out`/`back` family would not reach the bar. INFERRED
from the profile.** The family holds 27,112 ms. The remaining check is about
107.2 s, still 1.16 times the bar. The family is also the chapter's content,
so the deletion is not a real edit. It bounds every cure aimed at one family:
no family inside this master carries the 41.5 s excess.

**The two big `Miscellaneous` components are caliber costs, not defects.**
Interface production, about 39.5 s, follows the interface size, 5,636,026
bytes at `_build/2.8.0/agda/src/L/Condensation.agdai`. Module instantiation,
about 29.5 s, follows the 101 module headers and the parameterized agreement
modules the master applies about a hundred times. MEASURED components at
`agents/tasks/LJ-1-380/runs/int1.out`; INFERRED attribution.

**No smallest edit is proposed.** The abort criterion for the diffuse case
says the master is honestly expensive and the bar conversation moves to the
owner. That is my finding, with the outside numbers below.

**Outside number one, the retired twin. MEASURED from the archive.** The
retired route's condensation chapter holds 514 in-fence lines and cost 203.3
s against a 203.5 s control, `archive/dev/JOURNAL-archived.md:2183`. That is
0.396 s per line. Today's master holds 6,820 lines at 0.0197 to 0.0205 s per
line. The current craft stands at about one twentieth of the retired twin's
rate, at thirteen times the lines. The retired twin's cost was concentrated:
`ambientOnly-from` held 92 percent and deletion cured it,
`archive/dev/TASKS-archived.md:179`. Today's master has no such site.
MEASURED absence at `agents/tasks/LJ-1-380/runs/prof2.out`.

**Outside number two, the literature.** See section 7.

## 4. THE 113 QUEUED INSERTIONS

The insertions land in this master: 28 repaired telescopes, the substrate
restatement, and the back leg, `agents/tasks/LJ-1.379/lj-1.379-report.md:171-181`.
They land beside the `out`/`back` family, whose mean charge is 347 ms per
definition, 27,112 over 78, MEASURED at `agents/tasks/LJ-1-380/runs/prof2.out`.
At the master's own rate, 113 lines add about 2.2 s and the rate ratio barely
moves. INFERRED, and P-m forbids a projection from line count without the
class: the lines are instantiation class. **The insertions do not amplify any
bridge, because no bridge exists today.** MEASURED absence, section 2.

## 5. DD4, THE CLOSURES, AND P-y

**The master is in NEITHER closure at HEAD. MEASURED.** I re-computed both
import closures over `git show HEAD:<path>`, with the roots at
`dev/ledger.toml:170` (`ac_root = "src/L/Model.lagda.md"`) and
`gch_root = "src/L/GCH.lagda.md"`. My computation reproduces `ledger.py
--reuse`'s printed aggregates exactly: AC 73 masters and 17,183 lines, GCH 48
and 8,875, shared 43. `src/L/Condensation.lagda.md` is in neither set. The
GCH root imports nothing that reaches it, `src/L/GCH.lagda.md:6-18`.
**So a cure here is upstream of neither wing's endpoint closure at HEAD, and
P-y's burn case, a cure upstream of both wings, does not apply to this
master.** The route plans this chapter for the GCH wing, and `Everything`
imports it at `src/Everything.lagda.md:388-391`, but the declared root's
closure does not reach it today. The GCH root is a statement, not a proof,
per `dev/ledger.toml`'s own `[reuse]` comment.

**Axis: fixed at `scripts/measure/ledger.py:50`, in-fence non-blank lines.**
Counted at 6,820 for this master, MEASURED.

## 6. RUN LEDGER

One agda process at a time, `GHCRTS="-A64m -I0 -M8g"`, cap never raised. No
heap wall. Machine load before each run is in `agents/tasks/LJ-1-380/timings.csv`.

| label | content | wall s | exit | slots before | verdict |
|---|---|---:|---:|---:|---|
| floor1 | empty file, module name error | 0.63 | 42 | 0 | VOID, my error |
| floor2 | empty file, `LJ-1-380.Floor` | 0.73 | 0 | 0 | **the empty-file floor** |
| prof1 | definitions profile | 3.26 | 0 | 0 | VOID: my harness removed the wrong path, the stale interface loaded and nothing was checked |
| prof2 | definitions profile | 137.45 | 0 | 0 | **cold run 1** |
| int1 | internal profile | 139.87 | 0 | 0 | **cold run 2** |

Two valid cold runs on the master, both beside slot count 0.

**My re-measure of the rate.** 134,279 ms Total over 6,820 lines is 0.01969
s per line, 1.45 times the bar. The wall figures give 1.48x and 1.51x. The
brief's 150.37 s, 1.62x, is one draw of the same distribution:
between-series uncertainty is 12.8 percent, `dev/ledger.toml:2852`. All draws
sit over the bar. MEASURED.

## 7. LITERATURE USED

`dev/literature/j-hierarchy.md:94`: "So condensation lives at the
Sigma_1 level in SZ." The proof rests on the machinery that makes it
expensive to formalize: SZ 1.14, the uniform Sigma_1 satisfaction relation,
at `dev/literature/j-hierarchy.md:105`, and SZ 1.15, the Sigma_1 Skolem
function, at `:107`.
**One line: the orthodox development builds condensation ON the satisfaction
relation, so a chapter that proves two-way satisfaction decodes for every
clause kind is structurally large.** This supports the honest-expense
verdict beside the profile.

## 8. ARCHIVE USED

One line per corpus, as the gate requires.

- **`archive/src/2026-08-09-rud-route/`**: read. The retired route has a
  condensation chapter, 514 in-fence lines. Quote,
  `archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:5`: "Devlin
  states it for an elementary substructure of a level: the substructure". Its
  203.3 s figure is the only outside comparable, used in section 3.
- **`archive/dev/JOURNAL-archived.md`**: read. Quote, `:2183`: "`Condensation`
  `[T89]`: the variable-index shape was written and the module **did not move
  at all**, 203.3 s against 203.5." The retired route already measured this
  subject honestly expensive, and measured a telescope lift that made it
  WORSE, 204.7 to 308.8 s, `:2199`. No identity-conversion shape is recorded under
  another name.
- **`archive/dev/TASKS-archived.md`**: read. Quote, `:179`: "DELETED, 86
  lines, docs shipped. Condensation fell 150.2 to 11.5 s: ambientOnly-from
  was 92 percent". Taken as SHAPE: the retired twin's cost was concentrated
  and curable by deletion. Today's master shows no such concentration.
- **`archive/dev/DECISIONS-archived.md`**: read. Quote, `:52` (D32):
  "`L.Condensation`'s two crossing imports and its Crossing section are
  DELETED, not re-homed." D31 and D32 rule the retirement, and D32's measured
  upside flag is the `ambientOnly-from` concentration. No ruling bears on
  sealing THIS master, and none was needed: the seal that mattered, on
  `satGraphAt`, is landed and this master opens it once.

## 9. PREMISES

1. **"150.37 s over 6,820 lines, 1.62x the bar"**. The 6,820 lines are
   VERIFIED, counted by me. The seconds are VERIFIED IN SUBSTANCE, REFUTED IN
   FIGURE: my two cold runs measure 134.3 s and 138.0 s of Agda Total, 1.45x
   to 1.51x the bar, `agents/tasks/LJ-1-380/runs/prof2.out:2` and
   `int1.out`. The 150.37 s draw sits inside the 12.8 percent between-series
   band, `dev/ledger.toml:2852`. The master is over the bar in every draw.
2. **"the bar is `ac_baseline_module_rate` times `tolerance`, computed at
   `scripts/measure/check-ratio.py:477`"**. VERIFIED: `dev/ledger.toml:2854`
   holds 0.011828 HISTORICAL(2026-08-16), `:3116` holds `tolerance = 1.15`, and
   `scripts/measure/check-ratio.py:478` computes `bar = judged * tolerance`.
   My product is 0.0136022.
3. **"113 insertions are queued into this family"**. VERIFIED at
   `agents/tasks/LJ-1.379/lj-1.379-report.md:14` and the table at `:171-181`.
   They land in this master.
4. **"`EnvSupply` fell 488.59 s for five inserted lines, at
   `dev/PLAN.md:163-165`"**. VERIFIED at `dev/PLAN.md:158-159`: the lines
   carry "495.23 s to 6.65 s, minus 488.59 s, for FIVE inserted lines and
   three deleted". The brief's `:163-165` is off by a few lines; those lines
   carry the same episode's spelling prose, so the premise holds.

## 10. THE PREMISE MOST LIKELY WRONG

**The brief's own flag: "the `EnvSupply` shape recurs here". REFUTED,
MEASURED.** The analogy does not transfer, exactly as P-l warns. `EnvSupply`
was 56.5 times the bar with 98.85 percent of its check in one definition.
This master is 1.45 to 1.51 times the bar with 2.57 percent in its largest
definition. The regime differs by an order of magnitude in concentration.
Expect no mismatch here, and none was found.

## 11. WHAT I WOULD TELL THE OWNER

The master is over the bar by content, not by craft. Three facts carry the
claim. First, no definition, family, or phase holds the excess. Second, the
two biggest accounts are interface production and module instantiation, and
both follow size and shape the chapter needs. Third, the retired twin ran at
twenty times today's rate on one thirteenth of the lines, and its cure was to
delete a concentrated crossing that today's master does not have. The 113
queued insertions add single-digit seconds, INFERRED, and change no verdict.

# [LJ-1.670] report: is elementarity already discharged at the clause-three site

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.670
obligation: agents/tasks/LJ-1-670/Probe670.agda::elem-is-paid
verdict: **GO. `[LJ-1.665]`'s `Elementary` slot fills from `[LJ-1.655]`'s
`WithCode.elem`. The two frames share one `HullStage` telescope. The
types agree by `refl`. Elementarity is not proved again.**

The obligation is green and metered (`runs/meter-obligation.out`,
`pass exit=0 3.51 s`, `0 UNRESOLVED of 1`, `probe_red=False`). Five
names in the probe are green (`runs/meter-names.out`,
`0 UNRESOLVED of 5`).

**READ THESE THREE SENTENCES BEFORE YOU QUEUE ANYTHING.**

1. **STOP FUNDING `Elementary` AS A SEPARATE OBJECT.** `elem-is-paid`
   (`Probe670.agda:92-96`, exported at `:100`) inhabits
   `P652.Frame652.A.Elementary` from `P655.AtCollapse.WithCode.elem`.
   `[LJ-1.665]`'s remaining triple loses that slot.
2. **THE REMAINING PRICE AT THE HULLSTAGE FRAME IS THE CODE PAIR
   `[LJ-1.655]` NAMED, AND NOTHING ELSE.** `f : SM → Code` and
   `f-spec` (`Probe670.agda:93-94`). That pair is a selection problem.
   The chapter already spends it at `BoundedSubsetAt`
   (`Probe655.agda:283-293`; `src/L/BoundedSubset.lagda.md:1648-1660`).
3. **DO NOT FILL THIS SLOT WITH `elem-at-collapse`.** That name
   (`Probe655.agda:153-158`) is `elem` composed with iso-invariance.
   `[LJ-1.665]`'s slot is `A.Elementary` (`src/L/Hull.lagda.md:174-176`),
   which is what `Probe652.agda:155` spends. The types are not the same.

Written as a skeleton before the first Agda run and filled as each
answer landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-670/`. Agda ran under the caliber the program set on
this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier, ONE Agda process at
a time. I did not set `GHCRTS`. Nothing is postulated, the delivered
probe carries `--safe` and no hole, and nothing lands in `src/`. The
probe is a raw `.agda` file, so it carries no ` ```agda ` fence, counts
0 in-fence lines, and the ratio bar cannot fire on it.

**NO HEAP WALL WAS MET ON THE DELIVERED SHAPE.** The first inhabited
draft (`runs/p-1.out`) elaborated a `BoundedSubsetAt` spend of `hedF`
and peaked at 2,169,536,512 bytes RSS against the 2,147,483,648-byte
wide cap. EXIT was 0 (the RTS did not abort). I dropped that spend in
the same dispatch: `[LJ-1.655]` already spent the pair at
`Probe655.agda:283-300`, and `elem-type-agree` (`Probe670.agda:74-75`)
is generic in the `HullStage` arguments, so the consumer instance is
not a new type fact. The delivered file's highest peak is
1,500,758,016 bytes (`runs/p-cold.out`), 70 percent of the cap.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict.

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE.**
No number here is a cold-cache number, and this report does not bound
one.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.665]` closed **GO** on `certificate-remainder`
(`agents/tasks/LJ-1-665/lj-1.665-report.md:8-12`). The Elementary slot
that predecessor delivered is

    elem : P652.Frame652.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ
    (`Probe665.agda:236`)

The report does not name `Elementary` FALSE.

`[LJ-1.655]` closed **GO** on `elem-at-collapse`
(`agents/tasks/LJ-1-655/lj-1.655-report.md:1-3`). The chapter's own
`elem` that predecessor delivered is

    elem : HED.A.Elementary
    (`Probe655.agda:144-145`, inside `AtCollapse.WithCode`)

The report does not name `Elementary` FALSE. The standing coder clause
does not stop this task. I take both types from the probes that
typechecked, and both verdicts from the reports.

`elem-at-collapse` is a different type from `A.Elementary`. Section 4
records that fact. I inhabit `A.Elementary`. I do not inhabit
`elem-at-collapse` again.

## 2. W3, THE WIDEST UNMEASURED TERM

The brief names it: whether `[LJ-1.655]`'s pair and `[LJ-1.665]`'s
frame share a telescope. The brief estimated 50 to 120 lines.

**GO. THE FRAMES MEET.** `At665` (`Probe670.agda:58-62`) instantiates
`P652.Frame652` and `P655.AtCollapse` at the same six `HullStage`
arguments `[LJ-1.665]` assembled (`Probe665.agda:65-69`;
`src/L/BoundedSubset.lagda.md:903-914`). Three agreements, all `refl`:

    hull-agree       : AC.HED.M ≡ F.HS.M                      (`:67-68`)
    code-agree       : AC.HED.H.T.Code ≡ F.HS.H.T.Code        (`:70-71`)
    elem-type-agree  : AC.HED.A.Elementary ≡ F.A.Elementary   (`:74-75`)

`HullElemDown` takes that telescope minus `succλ`
(`src/L/BoundedSubset.lagda.md:667-668`; `Probe655.agda:96-100`).
`AtCollapse` still takes `succλ`. The extra argument does not reach
`M`, `Code`, or `Elementary`. That is why the three equalities are
`refl` and not transport.

The estimate of 50 to 120 lines was high: the join is three signatures
and one four-line adapter. The delivered probe is 100 lines, 35 code.

## 3. THE FLOOR, MEASURED BEFORE ANY PROOF

The standing coder clause orders a floor before a heavy object. I ran
it. `runs/FLOOR.agda.txt` is the obligation's type, `Probe652` and
`Probe655` imported, and a HOLE where the term goes. It is `.agda.txt`
and not `.agda`, because every `.agda` under a task home is a
verification target (`scripts/pod/facts.py:489`).

**THE FRAME COSTS 12.11 s AND 1.30 GB, AND IT DOES NOT WALL.**
`runs/floor-1.out`: exit 42 at 12.11 s, peak 1,298,661,376 bytes, one
error and it is the designed hole (`[UnsolvedInteractionMetas]` at
`FLOOR.agda:49.18-22`). Agda checked `Probe652`, `Probe641` and
`Probe655` on the way in. Importing those two this-week probes is not
the 578-chain wall.

The import trim is: `src/` plus `Probe652` and `Probe655`. That is the
trim the floor measured. The delivered file uses the same imports.

## 4. THE OBLIGATION

`elem-is-paid` (`Probe670.agda:92-96`):

    elem-is-paid :
        (f : AC.HED.A.SM → AC.H.T.Code)
        (f-spec : (q : AC.HED.A.SM) → fst (AC.H.T.val (f q)) ≡ fst q)
      → F.A.Elementary
    elem-is-paid f f-spec = AC.WithCode.elem f f-spec

That is `[LJ-1.665]`'s Elementary hypothesis, filled from
`[LJ-1.655]`'s delivered `elem`, at the `HullStage` frame `[LJ-1.665]`
assembled. The term is one application. Elementarity is not proved in
this file.

**`elem-at-collapse` CANNOT FILL THIS SLOT.** Its type
(`Probe655.agda:153-158`) is a pair of implications between the
collapse reading and the stage reading, after `iso-inv`.
`A.Elementary` (`src/L/Hull.lagda.md:174-176`) is a definitional
equality between the hull reading and the stage reading. Clause (iii)
spends the equality (`Probe652.agda:174`: `elem n (embed φ) δ`). A
brief that feeds `elem-at-collapse` to `certificate-remainder`'s
`elem` argument asks Agda to inhabit the wrong type.

**THE CHAPTER ALREADY PAYS `(f, f-spec)` AT ITS OWN CONSUMER.** That is
`[LJ-1.655]`'s measurement (`lj-1.655-report.md:94-99`), cited by name
at `Probe655.agda:251-256` so the citation goes red if the names move.
A first draft of this probe re-spent `hedF` at `BoundedSubsetAt` to
show `W.elem : F.A.Elementary` at `UnionKit.X`. That elaboration
peaked at 2,169,536,512 bytes (`runs/p-1.out`). I dropped it:
`elem-type-agree` is already generic, so the consumer instance is the
same `refl`. Re-elaborating `hedF` here does not delete a further
object from the debt.

## 5. W2

**Nothing is proved twice.** `Probe652` and `Probe655` are imported,
not copied. `elem-is-paid` is an instance of 655's `WithCode.elem` at
665's `Frame652` arguments. The three `refl`s are definitional
agreements, not a second proof of `TV-thm`.

The chapter's `elem` (`src/L/BoundedSubset.lagda.md:759-760`) is the
same term 655 exported inside `WithCode`. I take it from 655, which is
the predecessor that delivered it at the collapse site.

No deadline forced a fixed form. There is no conflict to report.

## 6. W4, AND P-l

**W4: not applicable.** No module was retired, nothing under `src/`
changed, and `dev/ARCHIVE.md` takes no row from this task. The ideal
form written fresh today is the form delivered: one adapter at one
hull.

**P-l: obeyed.** No type in the probe names a stage presentation. The
statements quantify over `HED.M`, `H.T.Code`, and `A.Elementary`.
`⟪ Lset lam ⟫` appears nowhere.

## 7. THE LAWS IN THE BUNDLE

- **D-10** (`dev/LESSONS.md:1375`). The recorded residue for clause
  (iii)'s first hypothesis is `Elementary`. It is true at the
  `HullStage` frame: `elem-is-paid` inhabits it from the code pair.
  The corrected remaining residue beside it is that pair, which
  `[LJ-1.655]` already recorded (`lj-1.655-report.md:84-85`). I do
  not inhabit the pair. I do not inhabit `Matrix₂`.
- **C-22** (`dev/LESSONS.md:2307`). The report was written as a
  skeleton before the first Agda run and filled as each answer landed.
- **P-l** (`dev/LESSONS.md:2367`). Section 6.
- **D-26** (`dev/LESSONS.md:1735`). Did not bind. No well-founded key
  was built.
- **C-42** (`dev/LESSONS.md:3762`). No refutation landed. The
  measurement is that two green types compose. It is not a measurement
  that a named statement is false, so no sweep is owed.

## 8. RUNS

Caliber `-A64m -I0 -M2g`, the wide caliber, set on the pane by the
program and untouched here. One Agda process at a time. All runs from
the repository root.

| run | what | wall s | peak RSS bytes | exit |
|---|---|---:|---:|---:|
| `runs/floor-1.out` | 652+655 imported, one hole | 12.11 | 1,298,661,376 | 42 |
| `runs/p-1.out` | first green, with `hedF` spend (dropped) | 13.85 | 2,169,536,512 | 0 |
| `runs/p-2.out` | warm recheck of that draft | 2.45 | 766,951,424 | 0 |
| `runs/p-3.out` | delivered shape, own interface deleted | 5.70 | 1,109,327,872 | 0 |
| `runs/p-cold.out` | delivered, 641/652/655/670 interfaces deleted | 12.37 | 1,500,758,016 | 0 |
| `runs/p-final-1.out` | forced recheck | 5.52 | 1,109,344,256 | 0 |
| `runs/p-final-2.out` | forced recheck | 5.62 | 1,109,344,256 | 0 |
| `runs/meter-obligation.out` | the obligation | 3.51 | not taken | 0 |
| `runs/meter-names.out` | 5 names, grouped | 3.57 | not taken | 0 |

Median of the three delivered forced rechecks (`p-3`, `p-final-1`,
`p-final-2`) **5.62 s**. Highest peak of the delivered shape
**1,500,758,016 bytes** (`runs/p-cold.out`). Highest peak of any run
**2,169,536,512 bytes** (`runs/p-1.out`), the dropped `hedF` spend.
No heap abort. The delivered shape did not need a second restructure:
dropping PART 2 was the one restructure this dispatch made.

Witness meter, one obligation: `runs/meter-obligation.out`,
`0 UNRESOLVED of 1`, `probe_red=False`. Witness meter, five names:
`runs/meter-names.out`, `0 UNRESOLVED of 5`. This worktree has no
`.venv`; the meter ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`.
I did not add a dependency and I did not create a local `.venv`.

**THE RATIO BAR CANNOT FIRE ON THIS RETURN.** The write scope holds no
`.lagda.md` and no ` ```agda ` fence, so the in-fence divisor is 0.
Nothing landed in `src/`.

## 9. PRICE

Non-blank non-comment lines counted by `awk 'NF' file | grep -cv '^\s*--'`.

| what | lines | code lines | at `file:line` |
|---|---:|---:|---|
| the probe, whole | 100 | 35 | `Probe670.agda` |
| header and imports | 46 | 16 | `:1-46` |
| W3 agreements | 28 | 13 | `:48-75` |
| the obligation | 24 | 6 | `:77-100` |
| floor slice | 51 | 29 | `runs/FLOOR.agda.txt` |

The brief estimated 50 to 120 lines. The delivered probe is 35 code
lines. The extra lines in the estimate were not spent: the join is
definitional.

## 10. WHAT THE SHAPE RESISTED

- **What it cost.** 35 code lines, median 5.62 s on a forced recheck
  of the delivered file, highest delivered peak 1.50 GB against a
  2 GB cap, no heap wall on the delivered shape.
- **What the shape resisted.** Almost nothing at the HullStage join.
  Three `refl`s and one application compiled on the first attempt that
  stated them. The `BoundedSubsetAt` spend of `hedF` is what peaked
  above the 2 GB RSS figure, and dropping it was the restructure, not
  a second run of the same code.
- **What I had to weaken.** Nothing. I did not inhabit `Elementary` by
  a weaker statement. I inhabited the type `[LJ-1.665]` wrote, from
  the term `[LJ-1.655]` delivered.
- **What I could not close.** `(f, f-spec)` at a generic `HullStage`.
  I built no code function. `[LJ-1.655]` already recorded that the
  chapter pays that pair at `BoundedSubsetAt`, and I did not re-spend
  it.

## 11. WHAT THE NEXT BRIEF NEEDS

1. **STOP FUNDING `Elementary`.** `elem-is-paid` (`Probe670.agda:100`)
   fills `[LJ-1.665]`'s slot from `[LJ-1.655]`'s `WithCode.elem`. A
   sixth report that prices `A.Elementary` as an open object funds a
   cleared blocker.
2. **AT THE HULLSTAGE FRAME THE REMAINING ADAPTER IS `(f, f-spec)`.**
   Type at `Probe670.agda:93-94`. At `Devlin55.BoundedSubsetAt` that
   adapter is `hedF` / `hedF-spec`
   (`src/L/BoundedSubset.lagda.md:1648-1657`), already green. A brief
   that works at the chapter's own consumer does not fund the pair
   either.
3. **STILL FUND `LevelFormula` ONCE, AND STILL FUND `Witnessed Lset`
   PLUS `LsetGrounded`, NOT `Matrix₂`.** Those two (one formula, one
   corrected (iii) hypothesis) are the remaining debt of
   `certificate-remainder` after this dispatch. `[LJ-1.665]` named
   them at `lj-1.665-report.md:330-336` and `:340-342`. Item 2 at
   `:337-339` is the object this task deletes. This task does not
   touch the other two.
4. **DO NOT FEED `elem-at-collapse` TO CLAUSE (iii).** Section 4. The
   name to spend is `elem` / `elem-is-paid`.
5. **THIS FRAME RUNS WIDE.** Highest delivered peak 1.50 GB against a
   2 GB cap. Do not re-elaborate `hedF` inside a join of 652 and 655:
   that was `runs/p-1.out`. Importing `Probe578` is still forbidden by
   the measured wall.
6. This task changed nothing in `src/`.

## 12. GATES

Run individually while the work was live, as the Boundary requires:

- `scripts/gate/lint-agda.py --check`: exit 0, no output.
- `scripts/gate/check-probes.py --check`: `check-probes: clean (10333 tracked
  files, no probe outside agents/tasks/ and no generated file)`.
- `scripts/gate/lint-prose.py --check`: exit 0, no output.

The probe interface was deleted after the last run, so the working
tree carries no generated file. `runs/FLOOR.agda` was renamed to
`runs/FLOOR.agda.txt` before the return (conjunct 1 runs every
`.agda` under the task home). I did not run `make check`. I did not
commit and I did not push.

**I did NOT write `review-of-elem-is-paid.md`, and that is a
decision.** The standing clause says a `review-of-*.md` is how a
coder states a NO-GO, and a NO-GO means the brief's type was not
inhabited. The name `elem-is-paid` is inhabited, green and metered.

## ARCHIVE USED

- **`archive/dev/ORCHESTRATION.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# ORCHESTRATION: the orchestrator's operating rules`.
  It is the archived process document. This task joins two live probe
  types and does not consult dispatch process.
- **`archive/dev/DD-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# THE \`DD\` RULING SERIES, archived in full 2026-08-18`.
  W2 is live in the slot file. The archived DD row is not a type.
- **`archive/dev/PLAN-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# ARCHIVED 2026-08-20`. A history. The live status is
  `dev/pod/screen.toml`.
- **`archive/dev/STATUS-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# STATUS-archived: the goal table of the internalization route`.
  The internalization route is not this join.
- **`archive/dev/TASKS-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# Archived task index: the \`L3.32-T\` series`. That
  series is not a predecessor of `Elementary`.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md` DECLINED.** Not read
  beyond its first line. `:1` reads `# The level-hood formula: arity, what it binds, what stays free`.
  This task fills `Elementary`, not a level-hood formula, and does not
  move a slot.
- **`dev/literature/fine-structure.md` DECLINED.** Not read beyond its
  first line. `:1` reads `# Fine structure: projecta, standard codes, the reductions, and their dependencies`.
  Jensen `rΣ` elementarity is not `Hull.AtM.Elementary`. A grep for
  `elementary` in that file names the fine-structure maps, which this
  join does not use.
- **`dev/literature/glossary-review-2026-08.md` DECLINED.** Not read
  beyond its first line. `:1` reads `# Glossary review: the 119 pre-protocol entries`.
  No naming question arose and this task proposes no `dev/glossary.toml`
  entry.
- **`dev/literature/BIBLIOGRAPHY.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# Bibliography for the rud route`. No citation was
  added and no source was missing.
- **`dev/literature/devlin-errata.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# Devlin errata: documented error classes (do-not-repeat checklist)`.
  This task certifies no leaf as bounded and quotes no Δ₀ certificate.

# LJ-1.538 report: the nine env forms collect at one frame, and the heap did not move

slot: `coder`. Written early as a skeleton and filled as runs land (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-538/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. **No heap event.**

TARGET: one term `envK-frame-inhabited` in
`agents/tasks/LJ-1-538/Probe538.agda`, the NINE `envK-*` and `envInK-*`
forms collected as one record at `KValue`'s frame. Nothing lands in
`src/`. I did not build a `TFacts` value. I did not collect the other
seven forms. I did not fill `someEnv`. I did not edit `src/` and I did
not replace `TFacts`. I postulated nothing.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict.

## VERDICT

**GO. NINE COLLECT, AND THE COLLECTION IS CHEAP.**

`envK-frame-inhabited` typechecks
(`agents/tasks/LJ-1-538/Probe538.agda:199-246`, top-level alias at
`:250`), exit 0, **3.56 s cold and 722,698,240 B peak RSS**
(`runs/full-final.time`). The caliber caps the heap at 8 GiB, so the
run sits at about **8 percent of the cap**.

It PASSes the program's witness meter
(`/opt/homebrew/bin/python3.11 scripts/pod/witness.py --code LJ-1-538
--brief agents/tasks/LJ-1-538/LJ-1.538.md`, exit 0, 2.26 s,
**0 UNRESOLVED of 1**, `probe_red=False`, `runs/witness-0.out`).
`.venv/bin/python` is absent in this worktree, as it was for
`[LJ-1.499]` (`agents/tasks/LJ-1-499/lj-1.499-report.md:28`). I added no
dependency.

I did not write `review-of-envK-frame.md`. The obligation is inhabited,
so the verdict on the obligation is GO.

**THE WITNESS IS THE DELIVERABLE AND IT IS THERE.** `[LJ-1.507]` proved
a chain of this campaign rested on an empty antecedent
(`agents/tasks/LJ-1-507/Probe507.agda:257`,
`gap-is-false : someEnvDef-gap → Empty.⊥`). The record `EnvNine`
(`Probe538.agda:69-129`) is stated AND inhabited, so it is not that.

**ONE CITATION IN THE BRIEF I COULD NOT CHECK, and it changes nothing.**
The brief dates `[LJ-1.534]`'s four heap walls to
`dev/pod/transitions/2026-08.jsonl`, 10:34Z to 11:13Z, exit 251 each.
**The tracked copy in this worktree ends at seq 158, task `LJ-1.399`,
ts `2026-08-19T13:31:57Z`, and `grep -c 'LJ-1-534'` over it gives 0.**
I repeat the wall as the brief's claim, not as a measurement of mine.
The half I CAN confirm is that no `agents/tasks/LJ-1-534/` directory
exists in this tree, so that task left no report and no probe. My
obligation does not rest on either half: it is GO on its own run.

## D-10, BEFORE ANY AGDA

The brief asks which of `SupplyEnv`'s telescope the NINE forms actually
use. Counted at the cited lines, before any Agda ran.

`module SupplyEnv` takes EIGHT parameters
(`src/L/Coding/EnvSupply.lagda.md:107-111`):

```
module SupplyEnv (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  (ω∈γ : ⟨ ω ∈ sucV gam ⟩) where
```

**SEVEN OF THE EIGHT ARE `KValue`'S TELESCOPE, WORD FOR WORD**
(`src/L/Condensation.lagda.md:7380-7383`). The eighth is `ω∈γ`, and it
is the one hypothesis `KValue` does not carry. This is exactly the open
step `[LJ-1.499]` handed forward
(`agents/tasks/LJ-1-499/lj-1.499-report.md:283-286`).

**ONE OF THE EIGHT IS CARRIED AND NEVER CONSUMED: `ordλ`.** Traced:

- `ordλ` reaches the nine only through `module B = Bound lam ordλ succλ ∅∈λ`
  (`src/L/Coding/EnvSupply.lagda.md:113`).
- The only `B` members on the nine's path are `#∈λ` and `suc^∈λ`, through
  `#∈λ` at `src/L/Coding/EnvSupply.lagda.md:229-230` and `envSetK` at
  `:140-146`.
- `BoundOver.#∈λ` is by `∅∈λ` and `succλ` alone
  (`src/L/Coding/Bound.lagda.md:55-57`; the comment at `:54` states it:
  `-- Every numeral is an ordinal of the limit, by the two parameters alone.`).
  `suc^∈λ` is by `succλ` alone (`:97-99`).
- `ordλ` IS needed to STATE the frame, because `KV.Kenv`'s bound slot is
  `LsetS lam ordλ` (`src/L/Condensation.lagda.md:7390`). But
  `LsetS β oβ = Lset β , isL-Lset β oβ`
  (`src/L/Axioms/Basic.lagda.md:161`) puts it in the `snd`, and every one
  of the nine reads the slot by `fst`.

**So the collected frame carries eight and the nine consume seven.** The
brief warned that an unused hypothesis makes the frame larger than it
needs to be. This one cannot be dropped, because the record's own target
names the slot; it costs a parameter and no elaboration.

**`module EnvSet` is not in this file at all.** `[LJ-1.499]` measured
that it CONSUMES the goal rather than supplying it
(`agents/tasks/LJ-1-499/lj-1.499-report.md:52-60`), and its point 2
asks every successor to describe it that way (`:280-282`). This report
does.

## THE NINE, AND WHAT THEY COST

**THE COLLECTED TELESCOPE AS A TYPE.** These are the parameters of
`module Frame` (`agents/tasks/LJ-1-538/Probe538.agda:159-164`), so the
projected name `Frame.envK-frame-inhabited` IS "telescope → witness",
and the top-level alias at `:250` carries it unchanged:

```
module Frame
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  (ω∈σ : ⟨ ω ∈ sucV gam ⟩) where
```

then, per term, the five free environment slots:

```
envK-frame-inhabited : (g1 g2 g3 g4 g5 : S)
                     → EnvNine {n = 9} KV.iK (gam' g1 g2 g3 g4 g5)
```

**EVERY HYPOTHESIS, AT ITS `file:line`, AND WHERE IT COMES FROM.**

| # | hypothesis | stated at | where it comes from |
|---|---|---|---|
| 1 | `lam : V ℓ` | `src/L/Coding/EnvSupply.lagda.md:107` | supplied by `KValue` (`src/L/Condensation.lagda.md:7380`) |
| 2 | `ordλ : IsOrd lam` | `src/L/Coding/EnvSupply.lagda.md:107` | supplied by `KValue` (`src/L/Condensation.lagda.md:7380`). **Carried, never consumed by the nine** (D-10 above) |
| 3 | `succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩` | `src/L/Coding/EnvSupply.lagda.md:108` | supplied by `KValue` (`src/L/Condensation.lagda.md:7381`) |
| 4 | `∅∈λ : ⟨ ∅ ∈ lam ⟩` | `src/L/Coding/EnvSupply.lagda.md:109` | supplied by `KValue` (`src/L/Condensation.lagda.md:7382`) |
| 5 | `gam : V ℓ` | `src/L/Coding/EnvSupply.lagda.md:110` | supplied by `KValue` (`src/L/Condensation.lagda.md:7383`) |
| 6 | `ordγ : IsOrd gam` | `src/L/Coding/EnvSupply.lagda.md:110` | supplied by `KValue` (`src/L/Condensation.lagda.md:7383`) |
| 7 | `γ∈λ : ⟨ gam ∈ lam ⟩` | `src/L/Coding/EnvSupply.lagda.md:110` | supplied by `KValue` (`src/L/Condensation.lagda.md:7383`) |
| 8 | `ω∈σ : ⟨ ω ∈ sucV gam ⟩` | `src/L/Coding/EnvSupply.lagda.md:111` | **NEW.** `KValue` has none |
| 9 | `g1 g2 g3 g4 g5 : S` | `agents/tasks/LJ-1-538/Probe538.agda:199` | **NEW, and free.** The five unfilled slots of `γ'` |

**`[LJ-1.495]`'S SHIFT SUPPLIES NONE OF THEM, AND THAT IS NOT A GAP.**
`[LJ-1.495]` delivers `Shared26` (`agents/tasks/LJ-1-495/Probe495.agda:46-78`)
and `tfacts-shared-from-kfacts` (`:166-199`), which move the **26 shared**
`TFacts` fields off `KValue.facts` through six `KFactsCons`. **None of
the nine env fields is among the 26**: the shift's record ends at
`pairK` (`:199`) and `TFacts`'s env block starts at
`src/L/Condensation/TwelveAgree.lagda.md:186`. The nine are not shifted
from `KValue.facts` at all. **They are supplied direct from
`SupplyEnv`**, and the frame is what makes that legal.

**WHAT EACH OF THE NINE COSTS: ONE APPLICATION, AND ONE `refl`.**
No field needed a second step, a `subst`, or a weakening.

| field | supplier | `di`, `bi` | the tie discharged |
|---|---|---|---|
| `envK-mem` | `SupplyEnv.envK-gen` (`src/L/Coding/EnvSupply.lagda.md:277`) | 4, 6 | `refl` |
| `envK-neg` | `envK-gen` | 4, 6 | `refl` |
| `envK-top` | `envK-gen` | 3, 5 | `refl` |
| `envK-imp` | `envK-gen` | 6, 8 | `refl` |
| `envK-allin` | `envK-gen` | 5, 7 | `refl` |
| `envInK-mem` | `SupplyEnv.envInK-gen` (`src/L/Coding/EnvSupply.lagda.md:351`) | 4, 6 | `refl` |
| `envInK-neg` | `envInK-gen` | 4, 6 | `refl` |
| `envInK-top` | `envInK-gen` | 3, 5 | `refl` |
| `envInK-imp` | `envInK-gen` | 5, 7 | `refl` |

The `di` and `bi` numerals are the ones the delivered forms already use
(`src/L/Coding/EnvSupply.lagda.md:301`, `:312`, `:323`, `:334`, `:346`,
`:373`, `:385`, `:397`, `:409`), and the nine `refl`s sit at `:302`,
`:313`, `:324`, `:336`, `:348`, `:374`, `:386`, `:398`, `:411`. **The
frame moves only the TAIL of the vector**, from `B₀ ∷ []` to `γ'`, and
`B₀` keeps its index, because slot 0 of `gam'` is `SE.B₀`
(`Probe538.agda:177-178`). That is `[LJ-1.499]`'s `gam'`
(`agents/tasks/LJ-1-499/Probe499.agda:83-84`) unchanged.

**ONE ARGUMENT ORDER IS SWAPPED, and the record wins.** The four
`envInK-*` fields take `arK` BEFORE `arNum`
(`src/L/Condensation/TwelveAgree.lagda.md:217-218`); `envInK-gen` takes
them the other way round (`src/L/Coding/EnvSupply.lagda.md:353-354`).
The swap is in the four applications
(`Probe538.agda:227`, `:232`, `:237`, `:242`). `[LJ-1.499]` had already
met it at the one `envInK-mem` it did (`Probe499.agda:94-96`, `:106`).

**THE PEAK RSS, BECAUSE THE NEXT FAMILY IS PRICED AGAINST IT.**
Cold to cold, same import block, same caliber, ONE Agda process:

| what | real | max RSS | exit | run |
|---|---|---|---|---|
| the nine STATED, no witness (W3) | 2.83 s | 662,634,496 B | 0 | `runs/w3-0.time` |
| the nine STATED AND INHABITED | 3.56 s | 722,698,240 B | 0 | `runs/full-final.time` |
| **the nine witnesses alone** | **+0.73 s** | **+60,063,744 B (57 MiB)** | | difference |

**THE POINT IS NOT THE MiB PER FIELD: IT IS THAT THE FIGURE IS FLAT.**
57 MiB for nine witnesses is about 6.4 MiB each. `[LJ-1.499]` delivered
SIX of these nine at the same frame, five collected in `EnvK5` plus one
loose `envInK-at-frame` (`agents/tasks/LJ-1-499/Probe499.agda:91-106`,
`:164-191`), and measured 722,763,776 B at 4.36 s
(`agents/tasks/LJ-1-499/runs/full-0.time`). **This task delivers nine,
all collected, and the peak RSS moved by 65,536 B, downward.** Both
runs are on the wide caliber `-A64m -I0 -M8g`. I did not run
`[LJ-1.499]`'s file myself and I cannot confirm the cache state behind
its number, so treat the pair as a strong indication and not as one
controlled measurement. **Within THIS task, where I control both runs,
the cold pair in the table is controlled.**

Forced-recheck runs (a warm `.agdai` present, `touch` to force) sit
LOWER and are reported for completeness, not as the price:
`runs/w3-1.time` and `runs/w3-2.time` at 678,871,040 B / 2.17 s and
2.18 s; `runs/full-1.time`, `runs/full-2.time`, `runs/full-3.time` at
556,204,032 B / 556,187,648 B / 556,220,416 B and 2.21 s / 2.12 s /
2.13 s. **The cold pair is the comparable pair** and it is the one in
the table above.

## W3, THE WIDEST UNMEASURED TERM

The brief named the heap, and its probe as: "the nine hypotheses as one
telescope, stated and typechecked, no witness".

**GO.** That is the record `EnvNine` (`Probe538.agda:69-129` in the
delivered file), written FIRST and typechecked ALONE, with the final
import block so the two numbers are comparable. At the W3 runs the
record sat at `:66-123`: its text is byte for byte the text delivered,
and only the header comment above it grew afterwards, when I corrected
the `[LJ-1.534]` citation I could not check.

| run | real | max RSS | exit |
|---|---|---|---|
| `runs/w3-0.time` (cold, no `.agdai`) | 2.83 s | 662,634,496 B | 0 |
| `runs/w3-1.time` (forced recheck) | 2.17 s | 678,871,040 B | 0 |
| `runs/w3-2.time` (forced recheck) | 2.18 s | 678,871,040 B | 0 |

**No heap event, at 8 percent of an 8 GiB cap.** The brief estimated
about 30 lines and under 60 seconds; the record is 61 lines and the
cold run is 2.83 s.

**NINE DO NOT WALL.** The brief asked for that answer at once if it went
the other way. It did not. What the mathematician needs, in the brief's
own words "the number that does fit", is therefore not a number below
nine: **nine fits with room, and the collection cost 57 MiB.**

## ESTIMATE AGAINST ACTUAL

The brief estimated about 160 lines in the probe, of which the
obligation about 50, on a SHAPE comparable from `[LJ-1.499]`.

**Actual: 250 lines in the probe, of which the obligation is 48**
(`Probe538.agda:199-246`), against about 50 estimated. The overrun is
prose and statement: 92 lines of the file are comment, 14 are blank,
and 61 are the record `EnvNine`, which the estimate did not separate
from the obligation.

## LAWS

**D-10.** Fired, and it is the section above. The telescope was read at
`file:line` and the unused parameter was found BEFORE any Agda ran.

**C-22.** Followed. The report was written as a skeleton with seven
`PENDING` sections before the first Agda run, and each section was
filled as its run landed.

**P-l did not fire.** The types name `Fin`, `lookup`, `envSetAt`,
`envOverAt` and `suc` chains on indices. `sucV` appears in ONE place,
the frame's `ω∈σ` hypothesis (`Probe538.agda:164`), where it is
`SupplyEnv`'s own written form (`src/L/Coding/EnvSupply.lagda.md:111`)
and not a stage presentation inside a statement. No stage is unfolded.
This is the same reading `[LJ-1.499]` made at the same hypothesis
(`agents/tasks/LJ-1-499/lj-1.499-report.md:257-261`).

**D-26 did not fire.** These are memberships under a satisfaction
hypothesis. There is no well-founded key and no tower ordering.

**C-42.** No refutation landed on this task, so the sweep C-42 demands
has no site to start from. The one refutation in this neighbourhood is
`archive/dev/LJ-dispatch-index.md:396`, and `[LJ-1.499]` already swept
it (`agents/tasks/LJ-1-499/lj-1.499-report.md:266-267`). **A measured
cure does not transfer by analogy** (`AGENTS.md:45`), so I re-read that
row at its own site rather than carry the earlier count forward: it is
why every one of the nine carries `arNum`, and all nine in this file do.

**W2.** Answered. `EnvNine` is stated ONCE, generic in `K : Fin (5 + n)`
and `γ' : Vec S (11 + n)` (`Probe538.agda:69-70`), and instantiated once
at `n = 9` against `KValue`'s `Fin 14` (`:200`). The fixed form was not
written.

**W4 did not fire.** No module was retired. `dev/ARCHIVE.md` gets no row
from this task.

**THE RATIO BAR CANNOT FIRE ON THIS TASK.** The write scope is one
`.agda` probe, one report and one `runs/` directory. A raw `.agda` probe
carries no ` ```agda ` fence, so the in-fence line count of this task's
write scope is 0 and the bar's divisor is 0. Nothing landed in `src/`.

## WHAT THE NEXT BRIEF NEEDS

1. **THE FRAME IS ONE HYPOTHESIS WIDER THAN `KValue`, AND THAT IS THE
   WHOLE COST.** Seven of `SupplyEnv`'s eight are `KValue`'s telescope
   word for word; the eighth is `ω∈σ : ⟨ ω ∈ sucV gam ⟩`
   (`src/L/Coding/EnvSupply.lagda.md:111`). **This is still the open
   step `[LJ-1.499]` named** (`lj-1.499-report.md:283-286`): `KValue`
   has none, `[LJ-1.491]` added `⟨ ω ∈ gam ⟩`, `SupplyEnv` wants
   `⟨ ω ∈ sucV gam ⟩`. **This task did not settle it; it took
   `SupplyEnv`'s form, because `SupplyEnv` is the module that delivers
   the nine.** One of the two must win before a `TFacts` value exists,
   and that is the mathematician's call.
2. **NINE COLLECT FOR 57 MiB AND 0.73 s.** The next family can be
   priced against that number instead of a guess. It is a REAL number
   from a cold-to-cold pair on the wide caliber, and it is the first
   such number on this front.
3. **THE COLLECTION DID NOT GROW FROM FIVE TO NINE.** `[LJ-1.499]`'s
   five cost 722,763,776 B; this task's nine cost 722,698,240 B. **So
   whatever killed `[LJ-1.534]` is not the count of collected env
   fields, at least not up to nine.**
4. **I CANNOT SAY WHICH SIXTEEN `[LJ-1.534]` TOOK, and no worker can:
   it left no report and no probe.** The brief's "not all sixteen" is
   therefore a number I can repeat and not one I can resolve to a field
   list. What I CAN give is the count of what is collected and what is
   not, read at `src/L/Condensation/TwelveAgree.lagda.md:133-332`:
   **`TFacts` has 59 fields.** 26 are the shared block `[LJ-1.495]`
   shifts (`:133-161`). 9 are collected here (`:186-243`). **24 remain
   uncollected**, and `[LJ-1.512]`'s "57 of 59 have a delivered honest
   form somewhere" is about where the FORMS live, not about whether
   they collect.
5. **THE NEXT SUSPECT IS `valV`, `valW` AND `wKfact`, AND IT IS
   UNMEASURED.** Their types prepend NINE slots to `γ'`
   (`src/L/Condensation/TwelveAgree.lagda.md:244-249` for `valV`;
   `:250` and `:256`) and name `tmValAt`, where the nine collected here
   prepend six or seven and name `envSetAt` or `envOverAt`. **That is a
   shape difference the nine do not carry**, and a brief that takes the
   next family should take those three ALONE and expect a number
   unlike this one. `AGENTS.md:45` forbids transferring this task's
   57 MiB to them by analogy.
6. **THE FIVE FREE SLOTS OF `γ'` ARE STILL UNSPECIFIED.** `[LJ-1.499]`
   said so (`lj-1.499-report.md:287-290`) and it is still true. The `B`
   slot is settled; `g1` to `g5` are free in this term too
   (`Probe538.agda:199`). Nothing in the nine constrains them.
7. **`module EnvSet` is a CONSUMER.** Restated here as
   `[LJ-1.499]` point 2 asks (`lj-1.499-report.md:280-282`). It is not
   in this file.
8. **THE TRANSITIONS RECORD IN A WORKTREE IS THREE DAYS BEHIND.** A
   brief that cites `dev/pod/transitions/2026-08.jsonl` for a recent
   event cannot be checked by the worker it is given to: the tracked
   copy here ends at seq 158, `LJ-1.399`, `2026-08-19T13:31:57Z`. This
   is a program observation, not a mathematical one, and it costs a
   worker an unverifiable premise every time.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md`. READ.** `:326` reads:
  `| LJ-1.257 | The four envInK fields and someEnv | 5 OF 5. COLLAPSE IS 67 AGAINST 85 | Bodies shrink 55 to 30. The numeral premise is a MASTER change, priced at 40 to 60 mechanical lines |`
  This is the row that produced the four `envInK-*` forms this task
  collects, and it names the collapse `src/L/Coding/EnvSupply.lagda.md:102-104`
  records in its own header comment. `:396` reads:
  `| LJ-1.341 | Are envK and defPairK TRUE | FALSE, THE TYPES ARE EMPTY. DD25 [LJ-1.345] | Instantiate z with the bound itself and regularity refutes the cycle. The repair's hypothesis is FREE |`
  This is why all nine fields in `EnvNine` carry `arNum` and why the
  four `envInK-*` carry `arK` as well. An untied form is a refutation
  candidate, and none of the nine here is untied.
- **`archive/dev/JOURNAL.md`. DECLINED.** `grep -c` gives 0 for each of
  `envK`, `envInK`, `SupplyEnv` and `TFacts`. It carries nothing about
  this front. Not read.
- **`archive/dev/JOURNAL-archived.md`. DECLINED.** The same four counts,
  0 each. Not read.
- **`dev/ARCHIVE.md`. DECLINED.** The same four counts, 0 each. W4 did
  not fire on this task, so there was no row to write and no retirement
  to check. Not used.
- **`archive/dev/PLAN-archived.md`. DECLINED.** The same four counts, 0
  each. A closed plan carries no rule that binds this task, and the live
  rule set governs here. Not read.

## LITERATURE USED

**NO HIT, and each candidate is declined in writing.** This task is a
module instantiation and a record collection inside the tree. It states
no new mathematics, so no source stands behind it. The Boundary also
freezes mathematical prose until both trophies land (`AGENTS.md:69`).

- **`dev/literature/digest.md`. DECLINED.** `grep -ci 'envK'` gives 0
  and `grep -ci 'envset\|envsupply'` gives 0. Its two `heap` hits are
  the word `cheap` (`:414`, `:518`), not a heap measurement. Not read.
- **`dev/literature/devlin-II5.md`. DECLINED.** The same two counts, 0
  each; its two `heap` hits are `cheap` at `:420` and `:426`. The `K(u)`
  bound it stands behind is already landed as `KValue` and this task
  adds nothing to it. Not read.
- **`dev/literature/truncation-and-selection.md`. DECLINED.** `grep -ci`
  gives 0 for `envK`, `envset`, `heap` and `telescope`. Not read.
- **`dev/literature/geology.md`. DECLINED.** The same four counts, 0
  each. Not read.
- **`dev/literature/terms-2026-08.md`. DECLINED.** The same four counts,
  0 each. No term of this task went to the naming pipeline: every name
  in the probe is the tree's own. Not read.

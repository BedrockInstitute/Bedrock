# LJ-1.499 report: the envK family lands, and EnvSet is not its supplier

slot: `coder`. Written early as a skeleton and filled as runs land (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-499/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: one term `envK-family` in `agents/tasks/LJ-1-499/Probe499.agda`,
the five `envK-*` fields of `TFacts` at `KValue`'s frame. Nothing lands
in `src/`. I did not build a `TFacts` value. I did not fill `someEnv`.
I did not thread a stage through `LowerAgree` or `AbstractFrame`.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection. It does not start phase 3.
No Boundary clause is in conflict.

## VERDICT

**GO, AND THE BRIEF'S ROUTE IS REPLACED.**

`envK-family` typechecks (`agents/tasks/LJ-1-499/Probe499.agda:164-191`,
exit 0, median **4.38 s** over three forced rechecks of the full file)
and PASSes the program's witness meter
(`/opt/homebrew/bin/python3.11 scripts/pod/witness.py --code LJ-1-499
--brief agents/tasks/LJ-1-499/LJ-1.499.md`, exit 0, 3.41 s,
0 UNRESOLVED of 1, `probe_red=False`, `runs/witness-1.out`).
`.venv/bin/python` is absent in this worktree. I added no dependency.

**The five fields are NOT built from `module EnvSet`, because they
cannot be.** They are built from `SupplyEnv.envK-gen`
(`src/L/Coding/EnvSupply.lagda.md:277`), which is the tree's own
supplier and which already delivers the same five at a shorter frame
(`src/L/Coding/EnvSupply.lagda.md:293-348`).

I did not write `review-of-envK-family.md`. The obligation is
inhabited, so the verdict on the obligation is GO. The correction is a
correction of the ROUTE, not a stop on the target.

## D-10, BEFORE ANY AGDA

The brief asks where each of `EnvSet`'s four arguments comes from at
`KValue`'s frame. Counted at the cited lines, not from the brief.

`module EnvSet` (`src/L/Condensation.lagda.md:2929-2937`) takes
`arityK`, then `E∈K`, then `ar∈K`, then `envInK`.

**1. `arityK`. AVAILABLE.** `KValue.facts` supplies it directly
(`src/L/Condensation.lagda.md:7425`, the `arityK` field, `B.trans∈λ`),
and `[LJ-1.495]`'s six-fold shift carries it to `TFacts`'s indices.

**2. `E∈K`. NOT AVAILABLE, AND THIS IS THE CIRCULARITY.**
`EnvSet`'s third argument is
`E∈K : ⟨ fst (lookup E γ) ∈ fst (lookup K γ) ⟩`
(`src/L/Condensation.lagda.md:2933`).
Every `envK-*` field CONCLUDES exactly that:
`→ ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩`
(`src/L/Condensation/TwelveAgree.lagda.md:191`, and the same last line
at `:197`, `:203`, `:209`, `:215`).
**`EnvSet` consumes the goal.** Its four outputs are `out`, `back`,
`memE-bnd` and `memE-at` (`src/L/Condensation.lagda.md:3039`, `:3045`,
`:3052`, `:3058`).
`memE-at` gives `z ∈ E → z ∈ K`, which is membership of the MEMBERS of
`E`. It never gives `E ∈ K`.

**3. `ar∈K`. NOT AVAILABLE AT THE envK FRAME.** `TFacts`'s five
`envK-*` fields carry `arNum` and do NOT carry `arK`
(`src/L/Condensation/TwelveAgree.lagda.md:186-215`). The delivered
route derives `ar∈K` from `arNum` at the concrete site, by `#∈λ`
(`src/L/Coding/EnvSupply.lagda.md:287`).

**4. `envInK`. AVAILABLE, AND NOT CIRCULAR.** The brief named this one
as the one to check first. It is the one argument of the four that is
sound. `SupplyEnv.envInK-gen` (`src/L/Coding/EnvSupply.lagda.md:351`)
delivers it with no `TFacts` value anywhere, under two ties: `arNum`
and `arK`. `TFacts`'s own `envInK-*` fields state BOTH ties
(`src/L/Condensation/TwelveAgree.lagda.md:216-222`), so the record and
the supplier agree. The brief's W3 type omits both ties; the tied form
is the record's own form and I measured that one.

**THE ANSWER TO THE BRIEF'S STOP TEST.** The brief said: if the
dependency is circular, the `envK-*` and `envInK-*` families cannot
both come from `EnvSet` and the mathematician must split them. The
measurement says something stronger and simpler: **NEITHER family comes
from `EnvSet`. `EnvSet` is downstream of both.**

`someEnv` (`src/L/Coding/EnvSupply.lagda.md:417-444`) shows the true
direction. It BUILDS `EK` by `envSetK` (`:433`), it BUILDS `envInK₀`
by `envInK-gen` (`:439`), and only then does it FEED `module EnvSet`
with the two (`:440-441`). This is the one `EnvSet`
application in the tree that constructs its own supply, and it
constructs it the way this probe does.

## THE SWEEP (C-42)

C-42 says a finding measures the site it names and never how far the
shape extends, so the next action is the sweep and the COUNT.

- **19** applications of `module EnvSet` in `src/`. 18 are the row
  transfers in `src/L/Condensation.lagda.md` (`:3707`, `:3726`,
  `:3790`, `:3817`, `:3907`, `:3940`, `:4090`, `:4119`, `:4474`,
  `:4496`, `:5087`, `:5118`, `:5216`, `:5247`, `:5328`, `:5355`,
  `:5432`, `:5454`). 1 is `someEnv`
  (`src/L/Coding/EnvSupply.lagda.md:440`).
- **10** row modules of `src/L/Condensation.lagda.md` state `envK` as a
  TELESCOPE HYPOTHESIS: `:3682`, `:3765`, `:3878`, `:3990`, `:4172`,
  `:4435`, `:5049`, `:5178`, `:5300`, `:5393`. Every one has the shape
  of a `TFacts.envK-*` field.
- **0** sites in `src/` derive an `envK` from `EnvSet`.

`src/L/Condensation.lagda.md:3707-3710` is the whole picture in four
lines: `EnvSet` is applied to `EK` and `arK`, and twenty lines later
the `back` direction writes `EK = envK yc a ar c E arNum hE`
(`:3725`), that is, it reads `EK` OUT of the row's `envK` hypothesis.
The tree has treated `envK` as a supply into `EnvSet` at every site
since those rows landed.

## WHAT THE FAMILY COST

Line counts inside `agents/tasks/LJ-1-499/Probe499.agda`.

| field | body lines | site |
|---|---|---|
| `envK-mem` (first) | 5 | `:167-171` |
| `envK-neg` | 5 | `:172-176` |
| `envK-top` | 5 | `:177-181` |
| `envK-imp` | 5 | `:182-186` |
| `envK-allin` | 5 | `:187-191` |

**THE PATTERN REPEATED EXACTLY.** Every field is one application of
`SE.envK-gen` with `Ei = zero`, `refl` for `qb`, and the field's own
`arNum` and `h` passed straight through. Only the environment prefix
and the two slot indices differ, which is what the brief predicted.
The first field did not cost more than a quarter of the budget: the
five landed together, exit 0, on the first typecheck, with no repair.

The obligation's type block `EnvK5` is 33 lines (`:117-149`), six lines
per field type, copied verbatim from
`src/L/Condensation/TwelveAgree.lagda.md:186-215`.

Whole-file price: **4.38 s** median, peak RSS **722,747,392 B**, from
`runs/full-1.time`, `runs/full-2.time` and `runs/full-3.time`. Against
the **3.04 s** of the W3-only file that is **+1.34 s** for the `EnvK5`
record plus the five fields. **TREAT THAT DIFFERENCE AS APPROXIMATE**:
the two medians come from two batches minutes apart on the same pane
and the same caliber, not from one interleaved batch. The W3-only file
no longer exists, because W3 and the obligation share one probe.

The brief estimated about 200 lines in the probe, of which the
obligation is about 70. The probe is 194 lines. The obligation is 28
lines of term (`:164-191`) plus the 33-line type block.

**I do not price the remaining fields.** The brief forbids it and I
have no measurement of them.

## W3, MEASURED FIRST AND ALONE

**GO.** `envInK-at-frame` typechecks (`Probe499.agda:91-106`, 16 lines,
exit 0), median **3.04 s** over three forced rechecks of the W3-only
file, peak RSS **648,888,320 B** (`runs/w3-1.time`, `runs/w3-2.time`,
`runs/w3-3.time`).

The brief estimated about 35 lines and under 45 seconds. Measured: 16
lines and 3.04 s. I did not fund it against `[LJ-1.495]`'s 2.44 s.

**ONE CORRECTION TO THE W3 TYPE, AND IT IS NOT A WEAKENING.** The
brief writes W3 with no arity hypothesis:

    envInK-at-frame : (z : S) → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc ar) (suc B) ⟩
                    → ⟨ fst z ∈ fst (lookup K γ) ⟩

That is `EnvSet`'s own argument type (`src/L/Condensation.lagda.md
:2935-2936`). It is NOT the type `TFacts` states. `TFacts.envInK-mem`
carries `⟨ fst ar ∈ fst (lookup ... K ... ) γ' ⟩` and
`∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` ahead of the `(z : S)`
(`src/L/Condensation/TwelveAgree.lagda.md:216-222`), and
`SupplyEnv.envInK-gen` asks for the same two
(`src/L/Coding/EnvSupply.lagda.md:351-356`). I measured the record's
form.

**I DID NOT MEASURE WHETHER THE UNTIED FORM IS FALSE, AND I DO NOT
CLAIM IT IS.** What I measured is that no module in `src/` delivers it
and that the record does not state it. The archive says the shape has
been refuted once before at a neighbouring site
(`archive/dev/LJ-dispatch-index.md:396`), so the question is worth a
brief of its own. That refutation is the next measurement on this
front, and it is not this task's.

## THE FRAME, AND ITS ONE CONSTRAINT

`Probe499.agda:68-75` takes `KValue`'s telescope plus
`ω∈σ : ⟨ ω ∈ sucV gam ⟩`. That is `SupplyEnv`'s telescope exactly
(`src/L/Coding/EnvSupply.lagda.md:107-111`).

`[LJ-1.491]` is **GO** (`agents/tasks/LJ-1-491/lj-1.491-report.md:76`)
and its delivered type is `KValue`'s telescope plus `⟨ ω ∈ gam ⟩`
(`agents/tasks/LJ-1-491/Probe491.agda:59`). My slot's clause says a
module hypothesis taken from a predecessor is the type that predecessor
delivered, and `dev/pod/audit-2026-08-20.md:34-45` is the F1 measurement
behind it. **This frame does NOT
take `[LJ-1.491]`'s hypothesis. It takes `SupplyEnv`'s**, which is one
successor out. The reason is that `SupplyEnv` is the module that
supplies the family, and its own type is the one it delivers. I did not
convert between the two forms and I did not measure whether
`⟨ ω ∈ gam ⟩` gives `⟨ ω ∈ sucV gam ⟩` on this coding. **The next
brief must settle that one step**, because a `TFacts` value at
`KValue`'s frame will want ONE ω hypothesis and not two.

`Probe499.agda:83-84` fixes slot 0 of `γ'` to `SE.B₀`, which is
`LsetS gam ordγ` (`src/L/Coding/EnvSupply.lagda.md:124-125`). That is
the ONE constraint the frame carries, and it is not a convenience.
Slot 0 of `γ'` is the `B` slot of all five `envK-*` fields and of all
four `envInK-*` fields: the index is `suc^6 zero` at the six-slot
frames and `suc^8 zero` at `envK-imp`'s eight-slot frame, and each
lands on `γ'` position 0. `envK-gen` asks for it as `qb`
(`src/L/Coding/EnvSupply.lagda.md:278`), and the delivered five
discharge it by `refl` at their own frame
(`src/L/Coding/EnvSupply.lagda.md:302`, `:313`, `:324`, `:336`, `:348`). Here `refl` discharges it
too. The other five prepended slots stay universally quantified.

`TFacts` has NO value anywhere in `src/`: the only occurrences are its
own declaration and one parameter (`grep -rn "TFacts" src/` gives
`src/L/Condensation/TwelveAgree.lagda.md:129`, `:342`, `:345`). So
nothing in the tree constrains those five free slots today, and nothing
is overridden by fixing slot 0.

## 1. W2

W2 (from DD4): write the mathematics once at a generic carrier and
instantiate it.

`SupplyEnv.envK-gen` (`src/L/Coding/EnvSupply.lagda.md:277-291`) is the
one slot-generic shell. It is `{k : ℕ} (γ : Vec S k) (Ei di bi : Fin k)`,
so it is generic in the frame length and in all three slot positions.
All five fields instantiate that ONE shell. I copied no proof body. I
wrote `EnvK5` once (`Probe499.agda:117-149`) at `TFacts`'s own
`Fin (5 + n)` and `Vec S (11 + n)`, and instantiated it once at
`n = 9` against `KValue`'s `Fin 14` (`Probe499.agda:164-165`). No site
is named as a fixed form. There is no conflict with W2.

**W2 IS ALSO THE ARGUMENT FOR THE ROUTE.** The brief's route would
have written a new derivation of `E ∈ K` beside one the tree already
holds. `envK-gen` is that generic carrier and it was already written.

W4 does not fire: no module was retired, and nothing moved to
`archive/`.

## 2. LAWS

**D-10.** Answered above, before any Agda. The recorded target was
true and the recorded ROUTE was false. The corrected target is beside
the original in this report.

**C-22.** The report was a skeleton before the first Agda run, and it
was rewritten when W3 landed and again when the obligation landed.

**P-l did not fire.** The types name `Fin`, `lookup`, `envSetAt`,
`envOverAt` and `suc` chains on indices. `sucV` appears in ONE place,
the frame's `ω∈σ` hypothesis (`Probe499.agda:75`), where it is
`SupplyEnv`'s own written form and not a stage presentation inside a
statement. No stage is unfolded.

**D-26 did not fire.** This is a membership under a satisfaction
hypothesis. There is no well-founded key and no tower ordering.

**C-42.** Fired, and the sweep is above. Count reported before any
cure was priced.

**THE RATIO BAR CANNOT FIRE ON THIS TASK.** The write scope is one
`.agda` probe, one report and one `runs/` directory. A raw `.agda`
probe carries no agda fence, so the in-fence line count of this task's
write scope is 0 and the divisor is 0. Nothing landed in `src/`.

## 3. WHAT THE NEXT BRIEF NEEDS

1. **The `envK-*` and `envInK-*` families are DONE as mathematics.**
   `src/L/Coding/EnvSupply.lagda.md:293-411` holds all nine. This
   probe shows they reach `TFacts`'s frame with one `refl` each. A
   brief that asks for them again is asking for work that exists.
2. **`module EnvSet` must be described as a CONSUMER**, in this brief's
   successors and in any note about the front. Ten row telescopes and
   one `someEnv` already treat it that way.
3. **The ω hypothesis is the one open step at this frame.**
   `KValue` has none, `[LJ-1.491]` added `⟨ ω ∈ gam ⟩`, and
   `SupplyEnv` wants `⟨ ω ∈ sucV gam ⟩`. One of these must win before a
   `TFacts` value is built. This is small and it is unmeasured.
4. **The five free slots of `γ'` are still unspecified.** No `TFacts`
   value exists, so nothing has chosen them. The `B` slot is settled by
   this probe; the other five are the next frame decision and they
   belong to the mathematician.
5. **The untied `envInK` is a refutation candidate**, not a gap. See
   the W3 section and `archive/dev/LJ-dispatch-index.md:396`.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md`. READ.** `:396` reads:
  `| LJ-1.341 | Are envK and defPairK TRUE | FALSE, THE TYPES ARE EMPTY. DD25 [LJ-1.345] | Instantiate z with the bound itself and regularity refutes the cycle. The repair's hypothesis is FREE |`
  This is why `TFacts`'s `envK-*` carry `arNum` and why the untied
  `envInK` is a refutation candidate rather than a gap. `:175` reads:
  `| LJ-1.99 | Does transitivity of K close entryK? | YES, MEASURED GREEN | Four arityK steps close entryK; arSubK is one step. The rows supply every tie; EnvSet's own telescope does not |`
  The last clause of that row states the D-10 finding of this report,
  measured before this task existed.
- **`archive/dev/JOURNAL.md`. DECLINED.** `grep -c 'envK'` gives 0 and
  `grep -c 'EnvSet'` gives 0. It carries nothing about this front.
- **`archive/dev/JOURNAL-archived.md`. DECLINED.** Same two counts, 0
  and 0. Not read.
- **`dev/ARCHIVE.md`. DECLINED.** `grep -c 'envK'` gives 0 and
  `grep -c 'EnvSet'` gives 0. W4 did not fire on this task, so there
  was no row to write and no retirement to check. Not used.
- **`archive/dev/DECISIONS-archived.md`. DECLINED.** `grep -c 'envK'`
  gives 0 and `grep -c 'EnvSet'` gives 0. The live rule set governs
  here, and a bare `D<n>` resolves only against that archived series.
  Not read.

## LITERATURE USED

**NO HIT, and each candidate is declined in writing.** This task is a
record-shift and a module instantiation inside the tree. It states no
new mathematics.

- **`dev/literature/truncation-and-selection.md`. DECLINED.** `grep -ci
  'envset'` gives 0. Not read.
- **`dev/literature/digest.md`. DECLINED.** `grep -ci 'envset'` gives
  0. Not read.
- **`dev/literature/devlin-II5.md`. DECLINED.** `grep -ci 'envset'`
  gives 0. The `K(u)` bound it stands behind is already landed as
  `KValue` and this task adds nothing to it. Not read.
- **`dev/literature/geology.md`. DECLINED.** `grep -ci 'envset'` gives
  0. Not read.
- **`dev/literature/glossary-review-2026-08.md`. DECLINED.** `grep -ci
  'envset'` gives 0. I added no `dev/glossary.toml` entry and I named
  no new term. Not read.

## FILES

Written, all inside the task's write scope:

- `agents/tasks/LJ-1-499/Probe499.agda` (194 lines)
- `agents/tasks/LJ-1-499/lj-1.499-report.md` (this file)
- `agents/tasks/LJ-1-499/runs/w3-0..3.out`, `w3-0..3.time`
- `agents/tasks/LJ-1-499/runs/full-0..3.out`, `full-0..3.time`
- `agents/tasks/LJ-1-499/runs/witness-1.out`

`review-of-envK-family.md` was NOT written. The obligation is
inhabited.

Nothing in `src/`. No commit. No push.

# LJ-1.551 report: the clean set is 37 and not 38, and 37 fields cost LESS than 28

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22,
`dev/LESSONS.md:2297`). No commit, no push. I wrote only in
`agents/tasks/LJ-1-551/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. **No heap event, no WALL.**

TARGET: one term `clean-forms-collected` in
`agents/tasks/LJ-1-551/Probe551.agda`, the `TFacts` fields whose honest form
asks for nothing the record does not give, collected as ONE value with a
witness at `KValue`'s frame. Nothing lands in `src/`. I did not collect the 16
that ask for more. I did not build a `TFacts` value. I did not trim the
telescope. I did not edit `src/`. I postulated nothing.

The standing direction (`dev/pod/direction.md:37`) says one SRC collection
after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1 work. It does not
start that collection and it does not start phase 3. No Boundary clause is in
conflict.

## VERDICT

**GO, AND THE COUNT IS 37, NOT 38.**

1. **`clean-forms-collected` typechecks** (`Probe551.agda:341-409`, top-level
   alias at `:411`), `--safe` at `:1`, exit 0, no hole, no postulate, no
   `TERMINATING`, no warning on any run (`runs/full-0.out`). It typechecked on
   its FIRST run (`runs/first.time`, 9.34 s, before the citation corrections), and nothing had to be weakened.

2. It PASSes the program's witness meter:
   `/opt/homebrew/bin/python3.11 scripts/pod/witness.py --code LJ-1-551
   --brief agents/tasks/LJ-1-551/LJ-1.551.md`, exit 0, 9.05 s,
   **0 UNRESOLVED of 1**, `probe_red=False` (`runs/witness-1.out`, re-run
   against the delivered file after the last edit; the first run, at 2.89 s
   against a warm interface, is `runs/witness-0.out`).
   `.venv/bin/python` is absent in this worktree, as `[LJ-1.512]` and
   `[LJ-1.545]` both found. I added no dependency.
   `/opt/homebrew/bin/python3.11 scripts/gate/check-probes.py --check` is clean
   (`runs/check-probes.out`, 6182 tracked files, no probe outside
   `agents/tasks/`).

3. **W3 IS GO AND IT RAN FIRST, ALONE.** The clean set's frame is inhabited at
   `KValue`'s frame with no `subst` and no transport
   (`Probe551.agda:115-126`). The `[LJ-1.71]` failure the brief warns about is
   caught by conjunct (a) and it does not happen here.

4. **THE COUNT THE BRIEF GAVE IS 38 AND THE CENSUS SAYS 37.** The brief tells
   me to take the census where it differs, and it does. Section `D-10` gives
   the arithmetic and the one field the subtraction mis-sorts.

5. **THE FIFTH CURVE POINT REFUTES THE LINEAR READING OF THE FIELD COUNT.**
   37 fields cost **1,067,859,968 B**, and `[LJ-1.545]`'s own 28-field file
   re-run on THIS pane costs **1,072,087,040 B**. **Nine more fields cost
   4,227,072 B LESS.** Section `THE FIFTH POINT`.

I did not write `review-of-clean-forms.md`. The obligation is inhabited, so
the verdict on the obligation is GO. The correction in D-10 is a correction of
a count, not a stop on the target.

**A NOTE ON THE RATIO BAR.** My write scope is one raw `.agda` probe and one
`.md` file. A raw `.agda` file carries no ` ```agda ` fence, so the in-fence
divisor is 0 and the bar cannot fire on this return, as my role section states.

## 0. THE PREDECESSORS, TAKEN FROM THEIR REPORTS

Audit F1 (`dev/pod/audit-2026-08-20.md`) says a module hypothesis taken from a
predecessor is the type that predecessor DELIVERED, read from its report and
its probe. I opened both for both.

- **`[LJ-1.512]` is GO** (`agents/tasks/LJ-1-512/lj-1.512-report.md:25`, which
  reads `**GO on the obligation, and the census is LARGE.**`). Its census is
  this task's list, and I re-verified every figure I use from it against
  `src/` first-hand: see D-10.
- **`[LJ-1.545]` is GO** (`agents/tasks/LJ-1-545/lj-1.545-report.md:24`, which
  reads `**GO. THE 28 JOIN, AND THEY COST 12.5 PERCENT OF THE CAP.**`). I take
  its union telescope from `agents/tasks/LJ-1-545/Probe545.agda:405-411`
  together with the obligation's own signature at `:440-443`, and its pinned
  environment from `:415-416`, and I re-state both in my own file rather than
  importing its probe.

Neither is a NO-GO on a statement I inhabit here, so no stop is owed on that
account.

## D-10, BEFORE ANY AGDA: THE LIST, AND THE COUNT IS 37

**FIRST, THE 59 FIELDS REPRODUCE.** Command, over the record body
`src/L/Condensation/TwelveAgree.lagda.md:129-336`:

```
awk 'NR>=129 && NR<=336' src/L/Condensation/TwelveAgree.lagda.md \
  | grep -cE '^    [A-Za-z][A-Za-z0-9₀₁₂-]*[[:space:]]*:'
```

**59.** Every field line number `[LJ-1.512]` prints reproduces character for
character. `record TFacts` is at `src/L/Condensation/TwelveAgree.lagda.md:129`,
which is the brief's premise 5.

**THE CLEAN FIELDS, BY NAME AND AT `file:line`. THERE ARE 37.**

| # | field | `TwelveAgree.lagda.md` line | honest form |
|---:|---|---:|---|
| 1-12 | `tagEq0` .. `tagEq11` | 133-144 | `KFacts.tagEq0..11` `src/L/Condensation.lagda.md:6082-6093`, inhabited by `refl` at `:7413-7415` |
| 13-24 | `numK0` .. `numK11` | 145-156 | `KFacts.numK0..11` `:6094-6105`, inhabited by `B.num∈λ k` at `:7416-7419` |
| 25 | `innerK` | 157 | `KFacts.innerK` `:6106-6107`, inhabited `:7420` |
| 26 | `pairK` | 159 | `KFacts.pairK` `:6110-6111`, inhabited `:7423` |
| 27 | `num1K` | 185 | `KFacts.numK1` `:6095`, inhabited `:7416`; it is the DUPLICATE of this record's own `numK1` (`:146`) |
| 28-32 | `envK-mem`, `envK-neg`, `envK-top`, `envK-imp`, `envK-allin` | 186, 192, 198, 204, 210 | `SupplyEnv.envK-mem` .. `envK-allin` `src/L/Coding/EnvSupply.lagda.md:293-348`, all five through `SupplyEnv.envK-gen` `src/L/Coding/EnvSupply.lagda.md:277-291` |
| 33-36 | `envInK-mem`, `envInK-neg`, `envInK-top`, `envInK-imp` | 216, 223, 230, 237 | `SupplyEnv.envInK-*` `src/L/Coding/EnvSupply.lagda.md:364-411` |
| 37 | `transK` | 262 | `SupplyEnv.transK` `src/L/Coding/EnvSupply.lagda.md:272-274`; at this frame it is `KFacts.arityK` `src/L/Condensation.lagda.md:6114-6115` with the binders swapped, which is the master's own move (`src/L/Condensation/TwelveAgree.lagda.md:347-352`) |

**THE SUBTRACTION IS RIGHT AND THE BUCKET IS WRONG, AND THAT IS THE WHOLE
CORRECTION.** `[LJ-1.512]` counts 54 honest forms and 16 that ask for more, so
54 - 16 = 38. But that census sorts the 54 into **THREE** buckets and not two
(`agents/tasks/LJ-1-512/lj-1.512-report.md`, the table under `HOW MANY
DIFFER`): **37 match exactly, 16 ask for MORE, and one, `envSetK`, asks for
LESS and delivers less.** 37 + 16 + 1 = 54, and 54 + 5 with no honest form at
all = 59. The subtraction silently counts `envSetK` as clean.

**IT IS NOT CLEAN, AND I CHECKED IT AT SOURCE RATHER THAN TAKING THE CENSUS'S
WORD.** The record's field
(`src/L/Condensation/TwelveAgree.lagda.md:306-307`) reads

```
    envSetK : (B ar : S) (n : ℕ) → fst ar ≡ # n
            → ⟨ fst B ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
```

and the honest form (`src/L/Coding/EnvSupply.lagda.md:140-142`) reads

```
  envSetK : (ar : S) (n : ℕ) → fst ar ≡ # n
          → ⟨ fst ar ∈ Lset lam ⟩
          → ⟨ fst (Generic.envSetGen B₀ ar) ∈ Lset lam ⟩
```

**The honest form has no `B` binder at all**: it PINS the carrier to `B₀`, the
module's own `LsetS gam ordγ` (`src/L/Coding/EnvSupply.lagda.md:124-125`). So
it cannot fill the record's generic-`B` field, whatever frame it is read at.
It belongs in neither bucket, and the clean set is **37**.

**I USE 37 AND THE PROBE COLLECTS 37**, as the brief instructs when the census
names a different figure.

## W3, THE WIDEST UNMEASURED TERM

**GO. THE CLEAN SET'S FRAME IS INHABITED, AND `tagEq` IS INHABITED AT IT.**

The brief names W3 as whether the clean set's hypotheses can hold together at
one frame, and says the collection is refuted if they cannot. **The clean set
by construction adds no PER-FIELD hypothesis: that is what makes it clean. So
the live question is not a hypothesis, it is the FRAME**, and it is sharp,
because the clean set spans TWO suppliers that were never read at one `γ'`:

- **27 rows come from `KValue.facts`**, a `KFacts` value at `KV.Kenv`
  (`src/L/Condensation.lagda.md:7411-7425`);
- **10 rows come from `SupplyEnv`**, which pins the environment's cell 0 to
  `B₀` (`src/L/Coding/EnvSupply.lagda.md:124-125`) and states its conclusions
  at `Lset lam` and not at a slot.

The record states both at ONE `γ'` and ONE `K`, six successors above the tag
indices.

**THE ARCHIVE MAKES THIS EXACTLY THE RIGHT GUARD, AND THE COINCIDENCE IS NOT
A COINCIDENCE.** `archive/dev/LJ-dispatch-index.md:135` reads

> `| LJ-1.71 | Consume TwelveAgree, which nothing consumed | CONVICTS c21b417 | The telescope's tagEq is uninhabited at EVERY frame, machine-checked. The module is vacuous. The LJ-1.55 slot fix HOLDS |`

**The field `[LJ-1.71]` found uninhabited at every frame is `tagEq`, and
`tagEq0` .. `tagEq11` are 12 of my 37.** So conjunct (a) below is not a
formality: it is the very statement the archive records as having been vacuous
once already.

`clean-frame-inhabited` (`Probe551.agda:115-126`, top-level alias `:128`) is
ONE value with three conjuncts, at one frame:

- **(a) `TagAtFrame`** (`Probe551.agda:89-93`), the tag equality read at the
  record's SIX-FOLD SHIFTED index over the pinned 20-cell environment. It is
  `KV.facts .tagEq0` and nothing else.
- **(b) `TransAtFrame`** (`:95-99`), the record's `transK` from
  `KFacts.arityK` with the binder roles swapped.
- **(c) `EnvAtFrame`** (`:105-113`), THE DECISIVE ONE: an `EnvSupply`
  conclusion, stated at `Lset lam`, read at the record's `K` SLOT. It holds
  because `Kenv`'s slot `iK` IS `LsetS lam ordλ`
  (`src/L/Condensation.lagda.md:7389-7390`, with `iK = suc zero` at `:7397`) and `lookup (suc^6 iK) γ‡` reduces
  to it. **If that stops being definitional, this file stops checking.**

W3 alone, three forced rechecks with the interface deleted before each
(`runs/w3-0.time` to `runs/w3-2.time`; the file at that run is
`runs/Probe551.w3-only.agda.txt`, 128 lines): **2.86 s on all three runs, median
peak RSS 684,654,592 B, 7.97 percent of the 8 GiB cap.** Exit 0 on the first run.
The brief estimated about 20 lines and under 30 seconds; it was 128 lines
(most of them the import header the file needs anyway) and 3 seconds.

**SO THE COLLECTION WAS NOT REFUTED, and the `[LJ-1.71]` failure was checked
for and did not recur.**

## THE OBLIGATION

`CleanForms` (`Probe551.agda:153-247`) states the 37 fields ONCE at a generic
`K`, generic `N0` .. `N11` and generic `γ'`, at `TFacts`'s own indices, and is
instantiated at `n = 9` against `KValue`'s `Fin 14` (`:341-345`).

**EVERY FIELD TYPE IS COPIED VERBATIM OUT OF THE MASTER.** The three blocks are
`src/L/Condensation/TwelveAgree.lagda.md:133-161`, `:185-243` and `:262-264`,
extracted with `sed` and not retyped.

`statement-matches` (`Probe551.agda:257-286`) is Agda's word that all 37 types
ARE `TFacts`'s own: every field is read off a `TFacts` value by projection,
with no coercion, no `subst` and no re-association. **It is not part of the
obligation and the obligation never calls it**, which is why the two figures
below are separate. It is `[LJ-1.545]`'s device
(`agents/tasks/LJ-1-545/Probe545.agda:268-295`) at 37 fields instead of 28.

**EVERY ONE OF THE 37 IS ONE APPLICATION AND NOTHING ELSE.** 27 are
`KV.facts .<field>` read at the shifted index with no conversion; 9 are
`SE.envK-gen` / `SE.envInK-gen`; `transK` is `KV.facts .arityK` with two
arguments swapped. **No `subst` was added at any field.** `num1K` is
`KV.facts .numK1`, which is the duplicate `[LJ-1.512]` measured.

**THE UNION TELESCOPE IS `[LJ-1.545]`'s WITH `valSub` REMOVED.** `KValue`'s
seven parameters (`src/L/Condensation.lagda.md:7380-7383`), then `ω∈σ`
(`src/L/Coding/EnvSupply.lagda.md:111`), then the five free cells with cell 0
pinned to `SE.B₀`. `valSub` was the seven `subK` rows' price and no `subK` row
is clean, so it is gone. **The clean set's telescope is NARROWER than
`[LJ-1.545]`'s while carrying nine more fields.**

**WHAT RESISTED: NOTHING IN THE MATHEMATICS.** The obligation typechecked on
its first run (`runs/first.time`). No weakening was needed, no hypothesis was
added beyond the frame W3 predicted, and no field needed a bridge that its own
supplier had not already built. **The brief asked what the shape resisted, and
the honest answer is that the clean set is clean in the strong sense: once the
frame holds, every field is a projection.**

**WHAT RESISTED: THE MEASUREMENT.** Two things, both in the two sections below.

## THE FIFTH POINT

**FIVE ROWS. THE FIFTH IS MINE, AND THE 28-FIELD ROW WAS RE-RUN HERE RATHER
THAN IMPORTED.**

`[LJ-1.545]`'s four rows are its own measurements at the wide caliber. To make
my row like-for-like I copied its `runs/Probe545.obligation-only.agda.txt`,
renamed the module line to `LJ-1-551.Probe551`, and ran it on THIS pane
(`runs/Probe551.rerun545-obl.agda.txt`, `runs/rerun545-obl-0..2.time`). **It
reproduces `[LJ-1.545]`'s figure to within 2,154,496 B, 0.2 percent**, so the
two panes are comparable and its four rows stand.

| fields | task | seconds | peak RSS (median) | of the 8 GiB cap | run |
|---:|---|---|---:|---:|---|
| 7 | `[LJ-1.539]` | 3.74 to 3.76 | 749,109,248 B | 8.72 % | `[LJ-1.545]`'s `runs/rerun-539-*.time` |
| 9 | `[LJ-1.538]` | 3.97 to 3.98 | 722,698,240 B | 8.41 % | `[LJ-1.545]`'s `runs/rerun-538-*.time` |
| 12 | `[LJ-1.542]` | 2.94 to 2.95 | 679,690,240 B | 7.91 % | `[LJ-1.545]`'s `runs/rerun-542-*.time` |
| 28 | `[LJ-1.545]` | 5.01 to 5.69 | 1,069,932,544 B | 12.46 % | `[LJ-1.545]`'s `runs/obl-*.time` |
| 28 | the same file, HERE | 5.64 to 5.76 | 1,072,087,040 B | 12.48 % | `runs/rerun545-obl-0..2.time` |
| **37** | **`[LJ-1.551]`** | **5.12 to 5.27** | **1,067,859,968 B** | **12.43 %** | `runs/obl-0..2.time` |

**THE ONE SENTENCE THE BRIEF ASKS FOR, ABOUT NUMBERS I MEASURED MYSELF: THE
LINEAR READING DOES NOT HOLD AT THIS POINT, BECAUSE 37 FIELDS COST 4,227,072 B
LESS AND HALF A SECOND LESS THAN 28 FIELDS RUN ON THE SAME PANE.**

**AND THE REASON IS THE ONE `[LJ-1.545]` ALREADY NAMED, NOT A NEW ONE.** That
report says the per-field constant is a property of the FAMILY. My 37 and its
28 are not nested: they share 21 rows (the nine env forms and the twelve
`numK`), it carries 7 `subK` that I do not, and I carry 16 that it does not.
**I dropped the dearest family it measured and added the cheapest kind of row
there is.** So the field count moved from 28 to 37 while the content moved the
other way, and the total followed the content.

**AN INFERENCE, MARKED AS ONE.** Taking `[LJ-1.545]`'s own `subK` family cost
of 159,612,928 B, my 16 new rows cost
1,067,859,968 - (1,072,087,040 - 159,612,928) = **155,385,856 B, which is
9,711,616 B a field**, and its cheapest measured family, `numK`, costs
9,626,965 B a field. Within 0.9 percent. **THIS IS AN INFERENCE AND NOT A
MEASUREMENT**: it rests on subtracting a baseline, and the next section is why
I do not trust a baseline subtraction on this machine today.

**THE DELIVERED FILE, WHICH IS NOT THE CURVE'S ROW.** The delivered file adds
W3 and `statement-matches` to the obligation: three forced rechecks give
**8.73 to 8.82 s and median peak RSS 1,578,582,016 B, 18.38 percent of the
cap** (`runs/full-0..2.time`). That is 510,722,048 B for the two extra terms,
and it is `[LJ-1.545]`'s "a second heavy term in one file costs more than it
costs alone" measured again at a new site rather than transferred.

**AGAINST THE BRIEF'S ESTIMATE.** The brief estimated about 260 lines with a
60-line obligation and under 10 seconds of Agda. Delivered: **411 lines**, of
which the obligation block is `:327-411`, **85 lines**; **5.1 to 5.3 s** for the
obligation-only file and **8.7 to 8.8 s** for the delivered one. The line estimate
was low because the 37 field types are copied verbatim and are 95 lines by
themselves (`:153-247`).

**AND THE BRIEF'S SAFETY ARGUMENT HELD.** It said 38 fields is under a 1.4
times step from 28 and the cap is not the risk. Measured: the step was not
1.4 times, it was 0.996 times. No heap event at any Agda run of this task.

### THE ONE MEASUREMENT I CANNOT EXPLAIN, AND IT IS A WARNING ABOUT BASELINES

**PEAK RSS FOR A TERM-FREE IMPORT HEADER IS BIMODAL IN TWO BANDS ABOUT 136 MB
APART, AND WHICH BAND A FILE LANDS IN IS NOT DETERMINED BY THE CODE IT
ELABORATES.**

I measured my own import header alone as a baseline, the way `[LJ-1.545]` did.
It came out **688,062,464 B median over three runs** (`runs/base-0..2.time`),
while `[LJ-1.545]`'s baseline file re-run on this same pane came out
**551,796,736 B median over three runs** (`runs/rerun545-base-0..2.time`),
which reproduces its own reported 546,078,720 B to within 1.0 percent. **My
header imports strictly FEWER names than its.**

What I did to isolate it, all at the wide caliber, all with the interface
deleted before each run, and every file kept in `runs/` so any row can be
re-run:

1. **Narrowing `[LJ-1.545]`'s import list one line at a time moves nothing.**
   Five variants, each dropping one of the five things my header does not
   import: all five sit at 551,747,584 to 551,780,352 B
   (`runs/Probe551.bisect-B.agda.txt` .. `.bisect-F.agda.txt`,
   `runs/bisect-B.time` .. `runs/bisect-F.time`).
2. **Applying all five at once gives a file whose code is byte-identical to
   mine** after stripping comments and blank lines and removing whitespace:
   both normalise to the hash `0c1f70771134e063b4cb75b6eaec336b`, against
   `7869d1e3bc5215a6d2d2ad2b45519264` for the two wide-import files.
3. **AND THE TWO FILES WITH THAT SAME HASH SIT IN DIFFERENT BANDS.** The 2 by
   2 below is the whole result. The only variables are the import list, which
   does not change the elaborated code across a row, and the number of COMMENT
   lines in the header, which changes nothing at all.

| import list | header | normalised code | peak RSS, two runs | band | runs |
|---|---:|---|---|---|---|
| wide, `[LJ-1.545]`'s | 40 lines | `7869d1e3` | 551,780,352 / 551,780,352 | LOW | `band-A0`, `band-A1` |
| wide, `[LJ-1.545]`'s | 34 lines | `7869d1e3` | 551,780,352 / 551,747,584 | LOW | `band-C0`, `band-C1` |
| narrow, mine | 40 lines | `0c1f7077` | 551,747,584 / 551,780,352 | LOW | `band-D0`, `band-D1` |
| narrow, mine | 34 lines | `0c1f7077` | 688,062,464 / 688,078,848 | **HIGH** | `band-E0`, `band-E1` |
| narrow, mine, my own comments | 34 lines | `0c1f7077` | 688,062,464 / 688,095,232 | **HIGH** | `band-B0`, `band-B1` |

The five files are `runs/Probe551.rerun545-base.agda.txt`,
`runs/Probe551.band-cut6.agda.txt`, `runs/Probe551.bisect-ALL.agda.txt`,
`runs/Probe551.band-narrowcut6.agda.txt` and `runs/Probe551.base.agda.txt`,
in that order.

**A CLAIM I MADE EARLIER IN THIS TASK AND THEN FALSIFIED, RECORDED BECAUSE THE
NEXT BRIEF SHOULD NOT REPEAT IT.** From the first three runs it looked as
though deleting six comment lines moved a file into the high band. It does
not: row 2 of the table is that same deletion on the wide-import file and it
stays LOW. **Neither the import narrowing alone nor the comment cut alone
moves a file. Only the two together do.**

**SO IT IS A THRESHOLD AND NOT A COST.** The two bands differ by about
136 MB, and 136 MB is about 2.03 times the 64 MiB allocation area that
`-A64m` sets. **INFERRED, and offered only as the shape that fits:** two files
whose elaboration work differs by a hair land on opposite sides of a collector
boundary. **I did not measure that mechanism and I do not claim it.**

**WHAT THE NEXT BRIEF SHOULD TAKE FROM IT.** `[LJ-1.545]` warned that peak RSS
stops being reproducible above about 1 GB and said to plan against the maximum.
**This is the same warning one band lower and it bites harder, because it
attacks a SUBTRACTION.** A per-field rate computed as
(whole file - baseline) / fields can be wrong by a whole band, 136 MB, which
at 16 fields is 8.5 MB a field, which is the size of the cheapest family's
whole rate. **Price a collection against WHOLE-FILE totals measured on one
pane, not against a baseline subtraction.** Every row of my curve table is a
whole-file total for that reason. Within a single file the figure is sharp:
my three obligation-only runs agree to the byte.

## WHAT THE 16 WOULD COST

**THEY ASK FOR THREE THINGS, NOT SIXTEEN, AND 13 OF THE 16 ASK FOR THE SAME
KIND OF THING: A MEMBERSHIP IN `K`.** I read all sixteen at
`src/L/Coding/EnvSupply.lagda.md` first-hand rather than taking the census's
summary.

**THE MOST COMMON ONE, AND IT IS NINE ROWS**, is that the graph slot is a
member of `K`. Seven state it character for character as
`⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩`: `subK₁-and` (`:497`), `subK₀-and`
(`:508`), `subK₁-imp` (`:519`), `subK₀-imp` (`:530`), `subK-neg` (`:541`),
`subK-un` (`:552`) and `subK-allin` (`:563`). Two more name the same slot as a
fresh binder instead, `(C T : S) → ⟨ fst T ∈ fst K ⟩`: `valK` (`:462`) and
`valK-un` (`:471`). **The remaining four of the thirteen are memberships in
`K` at other binders**: `valV` `⟨ fst z ∈ fst K ⟩` and `⟨ fst a ∈ fst K ⟩`
(`:594-595`), `valW` the same with `b` (`:604-605`), `wKfact` the same with
`a` (`:614-615`), and `consK-exist` `⟨ fst ya ∈ fst K ⟩` (`:661-662`).

**THE OTHER THREE ARE THE TWO THAT ARE DIFFERENT IN KIND, PLUS ONE ODD ONE.**
`consK-forall` (`:631-634`) and `consK-allin` (`:646-649`) each take
`{k : ℕ} (g : Fin k → V ℓ)` with `fst z ≡ env g`, an environment WITNESS and
not a membership, and two `K` memberships on top. `someEnv` (`:417-418`) takes
the truncated numeral arity `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁`, which is the one
hypothesis of the sixteen that the nine clean env rows ALREADY carry and pay.

**SO THE SIZING SENTENCE FOR THE NEXT BRIEF IS: nine rows are ONE debt at the
slot, four more are the same debt at other binders, two need an environment
witness that is a different construction, and one is already paid elsewhere in
the record.** `[LJ-1.508]` priced the slot debt at the frame and reports that
paying it once pays all of them
(`agents/tasks/LJ-1-508/lj-1.508-report.md:381-382`). I did not build any of
the sixteen and I measured none of them: this is a reading of their
declarations, and C-42 (`dev/LESSONS.md:3752`) says a count is not a cure.

## W2 AND W4, ANSWERED

**W2.** `CleanForms` (`Probe551.agda:153-247`) states the 37 ONCE at a generic
`K`, generic `N0` .. `N11` and generic `γ'`, and is instantiated at `n = 9` in
exactly one place (`:341-345`). W3's three conjuncts are stated generically in
the five free cells too (`:89-113`). **No block in this file is written twice,
and nothing is stated in a fixed form that could have been stated
generically.** No deadline pushed me toward a fixed form, so there is no
conflict to report. DD4's core constraint is at `archive/dev/DD-archived.md:22`.

**W4.** Nothing is retired by this task and nothing moves to `archive/`, so
`dev/ARCHIVE.md` gains no row. The clause's second half asks me to price the
ideal form written fresh today against the chapter I have. **For the clean 37
the ideal form written fresh today IS `KFacts` plus `SupplyEnv`, and this
probe is the proof that it fits at one frame with no glue at all**: 37 fields,
zero `subst`, one application each. **The record's 37 declarations are pure
re-declaration.** I propose no move, because a record redesign is not a module
retirement and because the redesign is the mathematician's call under AD3.

## WHAT THE NEXT BRIEF NEEDS

1. **THE COUNT IS 37 AND ANY BRIEF THAT SAYS 38 IS COUNTING `envSetK`.** That
   field runs the other way and needs a decision, not a proof.
2. **THE CLEAN SET IS FREE ONCE THE FRAME HOLDS.** 37 fields, no `subst`, one
   application each, and a telescope NARROWER than `[LJ-1.545]`'s. Anything
   left in `TFacts` that is expensive is expensive because of the 16 or the 5,
   not because of the collection.
3. **THE 22 NOT COLLECTED ARE 16 + 5 + `envSetK`.** The 16 are three kinds of
   ask, priced above. The 5 (`codesK`, `codesK-un`, `t0eq`, `t1eq`, `t0K`)
   have no supplier at all, which `[LJ-1.512]` measured and I did not re-open.
4. **PRICE THE NEXT COLLECTION IN FAMILIES, NOT IN FIELDS.** My fifth point is
   the counterexample: nine more fields, less heap and less time.
5. **DO NOT PRICE ANYTHING WITH A BASELINE SUBTRACTION ON THIS MACHINE.** The
   136 MB band is reproducible and its cause is not isolated.
6. **A GREEN COLLECTION STILL DOES NOT PREDICT A GREEN APPLICATION.**
   `archive/dev/LJ-dispatch-index.md:137` records a union frame that checked
   green while the APPLICATION heap-walled at the 8 GB cap. **I measured a
   value being BUILT. I did not apply it to anything, and I claim nothing
   about applying it.**

## THE WORKING TREE

Files I created, all inside my write scope:

- `agents/tasks/LJ-1-551/Probe551.agda` (411 lines)
- `agents/tasks/LJ-1-551/lj-1.551-report.md` (this file)
- `agents/tasks/LJ-1-551/runs/` (the `.out` and `.time` pairs for every run
  named above, plus the file variants below)

I did not create `agents/tasks/LJ-1-551/review-of-clean-forms.md`. I did not
touch `src/`. `git status --porcelain` shows `?? agents/tasks/LJ-1-551/` and
nothing else. I did not commit and I did not push.

Agda wrote interface files under `_build/2.8.0/agda/`, which
`dev/build-manifest.toml:117-120` declares `class = "toolchain"`, so no new
lifecycle declaration is owed.

Every file variant I measured is kept beside its runs, so a critic can re-run
any row of any table above. The delivered file is byte-identical to
`runs/Probe551.delivered.agda.txt` (`diff -q`, checked after the last run).

| file | what it is |
|---|---|
| `runs/Probe551.w3-only.agda.txt` | the file at the W3 runs, 128 lines |
| `runs/Probe551.base.agda.txt` | my import header alone |
| `runs/Probe551.obligation-only.agda.txt` | the obligation without W3 or `statement-matches`: the curve's fifth row |
| `runs/Probe551.delivered.agda.txt` | the delivered file |
| `runs/Probe551.rerun545-obl.agda.txt` | `[LJ-1.545]`'s obligation-only file, module renamed |
| `runs/Probe551.rerun545-base.agda.txt` | `[LJ-1.545]`'s baseline file, module renamed |
| `runs/Probe551.bisect-B.agda.txt` .. `.bisect-F.agda.txt` | `[LJ-1.545]`'s baseline with ONE import narrowed, five variants |
| `runs/Probe551.bisect-ALL.agda.txt` | the same with all five narrowed at once |
| `runs/Probe551.band-cut6.agda.txt` | `[LJ-1.545]`'s baseline minus six comment lines |
| `runs/Probe551.band-narrowcut6.agda.txt` | `.bisect-ALL` minus the same six comment lines |

I read `agents/tasks/LJ-1-545/` and `agents/tasks/LJ-1-512/` and wrote nothing
in either.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md`: READ AND USED.** `:135` reads

  > `| LJ-1.71 | Consume TwelveAgree, which nothing consumed | CONVICTS c21b417 | The telescope's tagEq is uninhabited at EVERY frame, machine-checked. The module is vacuous. The LJ-1.55 slot fix HOLDS |`

  This is the whole reason W3 ran first and why conjunct (a) is a `tagEq`:
  the field that was vacuous is 12 of my 37. `:137` reads

  > `| LJ-1.72 | Repair TwelveAgree, then consume it | STATEMENT FIXED, APPLICATION WALLS | The per-row telescope and the union frame both check green. The application heap-walls at the 8 GB cap |`

  which is why item 6 of `WHAT THE NEXT BRIEF NEEDS` says I claim nothing
  about applying this value. `:142` reads

  > `| LJ-1.75 | Give each partial only the facts its rows use | 43 of 69; 122.45 s | Better than proportional: 41.6 pc cheaper for a 37.7 pc smaller telescope. Two partials plus composer, 273.88 s |`

  I read it and did NOT act on it: the brief forbids trimming the telescope,
  and I trimmed nothing. It is cited only to say so.
- **`archive/dev/JOURNAL.md`: NOT READ, declined.** `grep -c` for `TFacts`,
  `KFacts`, `EnvSupply` and `tagEq` returns 0, 0, 0 and 0 over its 1378 lines.
  It carries nothing about this record.
- **`archive/dev/JOURNAL-archived.md`: NOT READ, declined.** The same four
  counts over its 4280 lines are 0, 0, 0 and 0.
- **`archive/dev/DECISIONS-archived.md`: NOT READ, declined.** 61 lines, the
  same four counts are 0. It resolves bare `D<n>` codes and this task cites
  none.
- **`dev/ARCHIVE.md`: NOT USED, declined.** The same four counts over its 299
  lines are 0. This task retires no module, so W4 has no row to write there.

## LITERATURE USED

- **`dev/literature/truncation-and-selection.md`: READ AND USED.** `:92` reads

  > `HoTT Book Lemma 3.9.1: if `P` is a mere proposition then `P ≃ ∥P∥`.`

  Relevant because the truncated numeral arity
  `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` is a hypothesis in nine of my 37 rows (the
  five `envK-*` and the four `envInK-*`,
  `src/L/Condensation/TwelveAgree.lagda.md:187, 193, 199, 205, 211, 218, 225,
  232, 239`), and the lemma is why that truncation is harmless where the
  conclusion is itself a proposition, which is the case at all nine: each
  concludes `⟨ _ ∈ _ ⟩`.
- **`dev/literature/level-formula-slot-roles.md`: NOT USED, declined.** It is
  the outside view of how the LITERATURE numbers a level-hood formula's slots.
  My slot arithmetic is the tree's own and I read it out of
  `src/L/Condensation.lagda.md:7387-7409`: no source bears on whether
  `lookup (suc^6 iK) γ‡` reduces.
- **`dev/literature/devlin-II5.md`: NOT USED, declined.** It is the
  Condensation Lemma and the GCH in L, the mathematics BEHIND `KFacts`. This
  task changes no statement and re-derives none.
- **`dev/literature/digest.md`: NOT USED, declined.** It pins the orthodox
  form of the rud route, which is `[LJ-2]` territory. This task touches no rud
  construction.
- **`dev/literature/glossary-review-2026-08.md`: NOT USED, declined.** I added
  no glossary entry and named no new term.

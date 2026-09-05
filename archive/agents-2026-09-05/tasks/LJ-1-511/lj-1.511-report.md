# LJ-1.511 report: someEnvDef with the truncation in its own type

slot: `coder`. Written early as a skeleton and filled as runs land (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-511/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event in any
run.

TARGET: one term `someEnv-at-corrected-def` in
`agents/tasks/LJ-1-511/Probe511.agda`. Nothing landed in `src/`. I did
not edit `src/`. I did not add `gam` to `someEnvDef'`. I did not
postulate the truncation. I did not cite `[LJ-1.504]`'s `gap-suffices`
as sufficiency, and no term of `[LJ-1.504]` is used in this file.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is LJ-1 work. It
does not start that collection and it does not start phase 3. No
Boundary clause is in conflict.

## VERDICT

**GO. The corrected type is non-vacuous, and it is inhabited.**

`someEnv-at-corrected-def` is built at
`agents/tasks/LJ-1-511/Probe511.agda:195-198`. Exit 0, `runs/final.out`,
under `--safe` at `:1`, no hole, no postulate, no `TERMINATING`. The
witness meter agrees:
`/opt/homebrew/bin/python3.11 scripts/pod/witness.py --code LJ-1-511
--brief agents/tasks/LJ-1-511/LJ-1.511.md`, exit 0, 3.72 s,
**0 UNRESOLVED of 1, `probe_red=False`** (`runs/witness-1.out`).
`.venv/bin/python` is absent in this worktree, as `[LJ-1.499]`,
`[LJ-1.504]` and `[LJ-1.507]` also found. I added no dependency.

**THE ROUTE `[LJ-1.507]` NAMED IS OPEN, AND IT IS ONE APPLICATION
WIDE.** The body of the obligation is `SE.someEnv ya yc b a ar c arNum
yaK ycK arK` and nothing else. The eight dispatches did not build a
chain that failed. They built every part of a chain that had one hole in
its TYPE, and this task closed the hole.

**AND THE LANDING IS CHEAPER THAN THE PROBE.** Section
`## WHAT THE LANDING WOULD COST` measures five sites. Four take one
added line each. The fifth takes one added argument whose name is
ALREADY BOUND and currently UNUSED at the call
(`src/L/Condensation.lagda.md:3509`, the binding; `:3515`, the call).
**No site in `src/` acquires a new proof obligation.**

## D-10, BEFORE ANY AGDA

The brief asked what I copied and what I added, at `file:line`, and then
asked the question `[LJ-1.507]` proved decisive: is the corrected
statement non-vacuous at this frame?

### What I copied and what I added

**COPIED: `src/L/Condensation/LowerAgree.lagda.md:52-58`, whole.** That
is `someEnvDef`, signature and body, seven lines. Line 52 reads
`someEnvDef : {n : ℕ} (K : Fin (5 + n)) (γ : S ^ (11 + n)) → Type (ℓ-suc ℓ)`.
The copy is `agents/tasks/LJ-1-511/Probe511.agda:74-81`.

**ADDED: ONE line, `Probe511.agda:79`**, the fourth hypothesis
`∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁`, marked `-- ADDED` in the file. It is
the numeral truncation `SupplyEnv.someEnv` asks for at
`src/L/Coding/EnvSupply.lagda.md:418`, which reads
`          → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁`. It sits after the three
memberships and before the `Σ`, so every copied line keeps its position.

**NOT ADDED: `gam`, and the gate `⟨ ω ∈ sucV gam ⟩`.** `[LJ-1.488]`
measured that the gate cannot be stated there without adding `gam` as a
parameter (`agents/tasks/LJ-1-488/lj-1.488-report.md:277-279`), and P-l
forbids a presentation of the ambient tower in a tower-generic type. The
gate stays where `SupplyEnv` states it, by `[LJ-1.503]`.

**AND THE COPY IS CHECKED, NOT ASSERTED.** `corrected-is-weaker`
(`Probe511.agda:96-100`) imports the master's own `someEnvDef` and
builds `someEnvDef {n} K γ → someEnvDef' {n} K γ` by dropping the added
hypothesis and passing the other nine arguments through unchanged. If
any other line of my transcription had drifted, that term would not
elaborate. **So the master drives the check.** It also fixes the
direction of the correction: the corrected type is strictly WEAKER.

### Is the corrected statement non-vacuous

**YES. Section `## IS THE CORRECTED TYPE NON-VACUOUS` gives the
witness.** The short reason is that `[LJ-1.507]` refuted a Pi-STATEMENT
and this task states an ANTECEDENT, and those are different questions. A
universally quantified claim over K can be false while the same formula,
read as a hypothesis, is satisfiable. `[LJ-1.507]` proved the first. It
says nothing about the second, and the second is what a hypothesis
needs.

## IS THE CORRECTED TYPE NON-VACUOUS

**YES. ONE INHABITANT OF ITS ANTECEDENTS, EXHIBITED AT THIS FRAME.**

Take every one of the six set arguments to be `numeralL 0`, written `z`
at `Probe511.agda:127-128`. Then:

| hypothesis | witness | evidence |
|---|---|---|
| `⟨ fst ya ∈ fst (lookup K6 (gam' …)) ⟩` | `KV.facts .numK0` | `src/L/Condensation.lagda.md:7416`, the `KValue` record value |
| `⟨ fst yc ∈ fst (lookup K6 (gam' …)) ⟩` | `KV.facts .numK0` | same |
| `⟨ fst ar ∈ fst (lookup K6 (gam' …)) ⟩` | `KV.facts .numK0` | same |
| `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` | `PT.∣ 0 , numeralL-fst 0 ∣₁` | `src/L/Axioms/Numerals.lagda.md:179` |

Two terms carry this, and the second is the one that cannot go stale.

1. **`witness-tuple` (`Probe511.agda:145-155`)** is the raw exhibit: the
   six sets and the four proofs, as one tuple.
2. **`antecedents-inhabited` (`Probe511.agda:166-175`)** is the decisive
   form. It takes an ASSUMED inhabitant of `someEnvDef'` at this frame,
   FEEDS it the tuple, and returns the conclusion. It reads the
   antecedents off the definition BY NAME, so it cannot drift from the
   definition, and it elaborates only if every one of the four
   hypotheses is inhabited at those arguments.

Both are green. Exit 0, `runs/w3-1.out` through `runs/w3-3.out`, W3
staged ALONE with the obligation absent from the file
(`runs/Probe511.w3-only.agda.txt` is that file, kept).

**THE GREEN IS NOT A VACUITY, AND THE NEGATIVE CONTROL SAYS SO.**
`runs/w3-control.out`, exit 42. The control puts `prʟ z z` at the `ar`
slot and offers the same numeral witness. Agda refuses at the added slot
and at nothing else, `runs/w3-control.out:3-9`:

```
when checking that the expression numeralL-fst 0 has type
fst (prʟ z z) ≡ (# 0)
```

So the elaborator does check the fourth hypothesis. **The control also
proves the second half: `prʟ z z` WAS accepted at the `ar ∈ K` slot**,
by `pairK` on `numK0` twice. That term is kept in the file as
`non-numeral-in-K` (`Probe511.agda:209-213`). With `[LJ-1.507]`'s
`pr-self-not-numeral` (`agents/tasks/LJ-1-507/Probe507.agda:124-130`),
it says the added hypothesis is NOT derivable from the three
memberships. **The correction is not cosmetic. It changes what the type
demands.**

## W3

W3 was `antecedents-inhabited`, and it was written FIRST and typechecked
ALONE, as the brief required. It landed on the first attempt: no failed
run precedes `runs/w3-0.out`, exit 0.

**W3 GO.** Prices are in the `PRICES` section below.

The brief said not to fund W3 against `[LJ-1.507]`'s refutation, because
that built a counterexample and this builds a witness. The estimate was
about 25 lines and under 40 seconds. **Measured: 21 code lines for the
two W3 terms (`Probe511.agda:145-155` and `:166-175`, non-blank and
non-comment), and 3.19 s median.** The whole W3 stage file was 158 lines,
72 of them code. Both numbers are inside the estimate.

## THE OBLIGATION

```agda
someEnv-at-corrected-def :
    (g1 g2 g3 g4 g5 : S) → someEnvDef' {9} KV.iK (gam' g1 g2 g3 g4 g5)
someEnv-at-corrected-def g1 g2 g3 g4 g5 ya yc b a ar c yaK ycK arK arNum =
  SE.someEnv ya yc b a ar c arNum yaK ycK arK
```

`Probe511.agda:195-198`. Four lines. The body is ONE application of the
delivered supplier at `src/L/Coding/EnvSupply.lagda.md:417-425`.

**WHAT THIS DISCHARGES.** `[LJ-1.504]` measured three differences
between the record's field and the supplier
(`agents/tasks/LJ-1-504/lj-1.504-report.md:44-46`). This one application
closes all three at once: the membership form, the `envSetB` to
`envHypB2` layout, and the truncation. The first two were already
CLOSED by `[LJ-1.504]`. The third is no longer a gap to be paid. **It is
paid by the type.**

**WHAT IT COST.** Nothing beyond the application. No lemma, no
transport, no re-derivation. The brief estimated about 45 lines for the
obligation. It took four, plus its comment block. **The estimate was
sound about the SHAPE and wrong about the size, and the reason is that
`[LJ-1.504]` had already paid the two hard differences.** A future brief
pricing a term whose predecessors closed two of three differences should
expect the third to be small when it is a hypothesis rather than a
proof.

**WHAT RESISTED. NOTHING.** Every stage was green on its first run.
That is unusual in this field and I say so plainly rather than claiming
work I did not do. The reason is visible in the record: eight dispatches
measured this one field, and what they delivered was correct. Only the
TYPE was wrong.

**WHAT I HAD TO WEAKEN.** Nothing in the probe. The correction itself
IS a weakening of `someEnvDef`, which is the ruling this brief carried,
and `corrected-is-weaker` (`Probe511.agda:96-100`) states the direction
in the tree rather than in prose.

**WHAT I COULD NOT CLOSE.** The landing. The brief forbids it and I did
not do it. The next section prices it.

## C-42, THE SWEEP

C-42 says a refutation measures ONE site and never says how far the
shape extends, so the next action is the sweep and the COUNT comes
before the cure. `[LJ-1.507]` refuted one site. Here is the count.

**THE SHAPE: a statement over `ar ∈ K` whose consumer needs `ar` to be a
numeral, stated WITHOUT the numeral truncation.**

**87 sites in `src/` CARRY the truncation.** Command:
`grep -rc '∥ Σ\[ n ∈ ℕ \] (fst ar ≡ # n) ∥₁' src/`. By file:
`src/L/Condensation.lagda.md` 50, `src/L/Condensation/TwelveAgree.lagda.md`
11, `src/L/Coding/EnvSupply.lagda.md` 10,
`src/L/Condensation/UpperAgree.lagda.md` 8,
`src/L/Condensation/LowerAgree.lagda.md` 8.

**4 SITES OMIT IT, AND ALL FOUR ARE THE SAME STATEMENT.** They are
`someEnvDef` and the three telescope copies of it:

| # | site | form |
|---|---|---|
| 1 | `src/L/Condensation/LowerAgree.lagda.md:52-58` | `someEnvDef`, the named definition |
| 2 | `src/L/Condensation.lagda.md:3317-3320` | `PropAgree`'s telescope hypothesis, longhand |
| 3 | `src/L/Condensation.lagda.md:3569-3573` | `AndAgree`'s telescope hypothesis, longhand |
| 4 | `src/L/Condensation.lagda.md:3624-3628` | `OrAgree`'s telescope hypothesis, longhand |

**THE SWEEP'S ANSWER: the shape does NOT extend. `someEnvDef` is the one
member of a family of 87 that omits the hypothesis its siblings carry.**
Every `envK-*`, `envInK-*`, `codesK` and `codesK-un` in the same records
carries it. So the cure is not a pattern to be applied N times. It is
one statement written four times.

**AND THE TREE ALREADY DIAGNOSED THIS DISEASE ONCE, AT THE SIBLING
FIELD.** `src/L/Condensation/TwelveAgree.lagda.md:296-306` records it in
the master's own comment: `envSetK` was RESTRICTED to a numeral arity by
`[LJ-1.173]` because `[LJ-1.172]` refuted the general-arity form.
`:302` reads: `    -- The restriction costs the consumers nothing, because the arity at`
and the sentence continues that every consuming site's arity IS a
numeral, through `codesK`, `arityNumAtL` and `pr-inj`. The same
statement is at the root, `src/L/Coding/Key.lagda.md:170-174`.

**THAT IS THE STRONGEST THING THIS SWEEP FOUND.** The exact cure this
brief carries was already ruled, measured and landed for `envSetK`.
`someEnvDef` is the field of the same family that did not get it. This
is not an analogy transferred against AGENTS.md:45: the section below
re-measures the consumers at `someEnvDef`'s own sites, and the
measurement agrees with what `[LJ-1.173]` found at `envSetK`'s.

**WHAT THE SWEEP DID NOT COVER.** It searched for the numeral-arity
truncation only. It did not search for other hypotheses a K-member
statement might silently need, and it did not search `archive/`.

## WHAT THE LANDING WOULD COST

**FIVE SITES. FOUR TYPES AND ONE CALL. DO NOT LAND IT: this is the
price, not the landing.**

| # | site | type or call | what changes |
|---|---|---|---|
| 1 | `src/L/Condensation/LowerAgree.lagda.md:52-58` | **TYPE** | ONE added line in `someEnvDef`, exactly `Probe511.agda:79`. |
| 2 | `src/L/Condensation.lagda.md:3317-3320` | **TYPE** | ONE added line in `PropAgree`'s longhand telescope copy. |
| 3 | `src/L/Condensation.lagda.md:3569-3573` | **TYPE** | ONE added line in `AndAgree`'s longhand telescope copy. |
| 4 | `src/L/Condensation.lagda.md:3624-3628` | **TYPE** | ONE added line in `OrAgree`'s longhand telescope copy. |
| 5 | `src/L/Condensation.lagda.md:3515` | **CALL** | ONE added argument, `arNum`, in `PropAgree.back`. |

**SITE 5 IS THE WHOLE REASON THIS IS CHEAP, AND IT IS MEASURED.**
`src/L/Condensation.lagda.md:3509` reads
`        (arK , (aK , (bK , arNum))) = codesK c ar a b c∈ shEq`.
The fourth component of `codesK` IS the truncation
(`src/L/Condensation.lagda.md:3292-3296`), it is bound to `arNum` at
`:3509`, and `arNum` is **not used again anywhere in that `back`**:
`sed -n '3520,3556p' src/L/Condensation.lagda.md | grep arNum` returns
nothing. **The one consumer already has the hypothesis in scope and
discards it today.** This is the same fact `[LJ-1.173]` recorded for
`envSetK`, re-measured here at `someEnv`'s own site as AGENTS.md:45
requires.

**FOUR MORE SITES CHANGE TYPE BUT NEED NO EDIT.** They name
`someEnvDef` or pass the field through, so they follow the definition:

- `src/L/Condensation/LowerAgree.lagda.md:218`, the field
  `someEnv : someEnvDef {n} K γ` of `LFacts`.
- `src/L/Condensation/TwelveAgree.lagda.md:289`, the field
  `someEnv : someEnvDef {n} K γ'` of `TFacts`.
- `src/L/Condensation/LowerAgree.lagda.md:273` and `:279`, which pass
  `someEnv` into `AndAgree` and `OrAgree`.
- `src/L/Condensation/TwelveAgree.lagda.md:442`, `; someEnv = someEnv`
  in the `LFacts` record `AbstractFrame` builds.

**AND NO SITE IN `src/` ACQUIRES A NEW PROOF OBLIGATION.** `TFacts` is
never constructed in `src/`: `grep -rn "TFacts" src/` returns three
lines, the record at `TwelveAgree.lagda.md:129`, the hypothesis at
`:342` and the `open` at `:345`. `AbstractFrame` has no consumer in
`src/` either. So the field is an OPEN hypothesis today, and adding a
hypothesis to an open hypothesis costs its suppliers nothing, because it
has none yet. This agrees with `[LJ-1.496]`, which measured that the
whole `PropAgree` to `AbstractFrame` chain binds no `V ℓ` stage
(`agents/tasks/LJ-1-496/lj-1.496-report.md:78-82`).

**WHAT THE LANDING BUYS.** `TFacts.someEnv` becomes inhabitable at
`KValue`'s frame from the delivered supplier, in one application. That
is `someEnv-at-corrected-def`, and it is the term this task built.

**WHAT I DID NOT MEASURE.** I did not typecheck any edited master, so I
give no seconds and no heap figure for the landing. Four added type
lines in `L.Condensation` and `L.Condensation.LowerAgree` are a
re-elaboration risk that only a real run can price, and
`LowerAgree.lagda.md:49-51` records that `someEnv`'s type has walled the
heap once before, at `[LJ-1.72]`. **A landing brief should fund one
timed run of `L.Condensation` and one of `L.Condensation.LowerAgree`
before it funds anything else.**

**I did NOT price this against `[LJ-1.260]`.** That row landed the
numeral premise in three records at net +42 lines
(`archive/dev/LJ-dispatch-index.md:327`). It is a comparable of SHAPE
only and nothing here is funded against it.

## PRICES

**METHOD, AND IT IS NOT THE OBVIOUS ONE. `touch` DOES NOT FORCE A
RECHECK UNDER AGDA 2.8.** My first six timed runs used `touch` and five
of them printed nothing, which is Agda loading the interface instead of
rechecking. Those numbers were wrong and I discarded them. **Every run
below deleted
`_build/2.8.0/agda/agents/tasks/LJ-1-511/Probe511.agdai` first**, and
every `.out` below starts with `Checking LJ-1-511.Probe511`, which is
the proof that the run did the work. One Agda process,
`GHCRTS="-A64m -I0 -M8g"`.

| stage | runs (s) | **median wall** | peak RSS (bytes) | **median peak RSS** |
|---|---|---|---|---|
| W3 alone, obligation absent | 3.19 / 3.00 / 3.19 | **3.19 s** | 662,700,032 / 662,716,416 / 662,716,416 | **662,716,416** (632.0 MiB) |
| full file | 3.38 / 3.18 / 3.34 | **3.34 s** | 670,072,832 / 670,072,832 / 670,056,448 | **670,072,832** (639.0 MiB) |

Sources: `runs/w3-1.time` to `runs/w3-3.time`, `runs/full-1.time` to
`runs/full-3.time`. `runs/w3-0.out` is the first-attempt W3 run, a real
recheck at 3.24 s, and it is not in the medians. `runs/full-0.out` was
untimed.

**MARGINAL COST OF THE OBLIGATION AND THE THREE TERMS ADDED WITH IT:
0.15 s and 7,356,416 bytes (7.0 MiB) of peak RSS.** The W3 stage file
was 158 lines and the full file is 218.

The witness meter, on a cold interface: exit 0, 3.72 s, 0 UNRESOLVED of
1 (`runs/witness-1.out`).

No heap event. No WALL. The `-M8g` cap was never approached: the highest
peak in any run is 670 MB, 7.8 percent of the cap.

**AND THE SAME METHOD DEFECT IS VISIBLE IN A PREDECESSOR'S RUN LOGS.**
`agents/tasks/LJ-1-504/runs/full-1.out`, `full-2.out` and `full-3.out`
are all EMPTY, so those three runs loaded the interface and did not
recheck. `[LJ-1.504]`'s full-file median of 2.92 s
(`agents/tasks/LJ-1-504/lj-1.504-report.md:200`) is therefore a load
figure. I do not say what its true recheck time was, because I did not
measure it. **`[LJ-1.507]` is CLEAN**: every one of its thirteen `.out`
files starts with `Checking`, so its 3.25 s and 3.42 s medians
(`agents/tasks/LJ-1-507/lj-1.507-report.md:257`, `:268`) are sound.

**FILE SIZE.** 218 lines total, 199 non-blank, 89 non-blank and
non-comment. The brief estimated about 190 lines with about 45 for the
obligation. **Measured: 218 and 4.** The comment blocks are the
difference, and the obligation is one order of magnitude under its
estimate for the reason given in `## THE OBLIGATION`.

**THE RATIO BAR CANNOT FIRE, AND I CHECKED THE CODE RATHER THAN THE
BRIEF.** `scripts/pod/accept.py:294` reads
`        if not rel.endswith(".lagda.md") or rel in led.UNCOUNTED:`, so
`in_fence_lines` counts `.lagda.md` files and nothing else. This task's
write scope is one `.agda` probe and two `.md` files. The divisor is 0
and the bar does not apply. The ` ```agda ` fence in
`## THE OBLIGATION` above is inside a plain `.md` file and adds
nothing to it.

## WHAT THE NEXT BRIEF NEEDS

1. **The correction is proved landable and priced at five sites.** The
   mathematician can now write a landing brief with a real site list
   rather than an estimate. It is above.
2. **Fund a timed run before anything else.** Four added type lines in
   `L.Condensation` are the only unmeasured risk, and that file has
   walled once at this very type (`LowerAgree.lagda.md:49-51`,
   `[LJ-1.72]`).
3. **`someEnvDef` is the LAST of four differences, and it is the last of
   its family.** The sweep found no second site with the shape. After
   this lands, the field that has cost eight dispatches is supplied.
4. **The open question this task does NOT answer: is the UNCORRECTED
   `someEnvDef` false?** `[LJ-1.507]` proved that the truncation ROUTE
   to it is empty. It did not prove the statement itself false, and
   neither did I. `non-numeral-in-K` shows only that the supplier cannot
   reach it at `ar = prʟ z z`. If the mathematician wants that settled,
   it is a separate and cheap probe, and it is not needed for the
   landing.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ.** `:327` reads
  `| LJ-1.260 | Land the numeral premise in the three records | LANDED. ALL FOUR MASTERS GREEN, NET +42 | Inside the inferred 40 to 60. No new proof: the out directions reuse the delivered decode |`.
  Used in `## WHAT THE LANDING WOULD COST` as a comparable of SHAPE
  only, and explicitly NOT as funding. Also read `:326` for
  `[LJ-1.257]`'s "The numeral premise is a MASTER change".
- `archive/dev/JOURNAL.md`: **not read.** `grep -n "someEnv\|EnvSupply"`
  returns nothing, so it holds no record of this field.
- `archive/dev/JOURNAL-archived.md`: **not read.** Same grep, no hit.
- `archive/dev/DECISIONS-archived.md`: **declined.** `grep -n
  "someEnv\|truncation"` returns nothing, and the `D<n>` series it
  carries is not a rule in force.
- `dev/ARCHIVE.md`: **not used.** `grep -n
  "someEnv\|EnvSupply\|LowerAgree"` returns nothing. No module in this
  task's path is retired, and this task retires none.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: **READ.** `:7` reads
  ``` `∥ A ∥₁`, and then the proof may not take it. **This file records what each```.
  It is why the correction is a HYPOTHESIS and not a derivation: the
  digest's criterion at `:163`,
  `**So the question "can this truncation be lifted" is always the question "does`,
  says a truncation lifts only when the goal is a proposition or the map
  is weakly constant. `someEnvDef`'s conclusion is a `Σ` carrying data,
  so neither holds and the truncation cannot be lifted at the record. It
  has to be carried. That is the whole content of this task's ruling.
- `dev/literature/digest.md`: **not used.** `grep -n
  "truncation\|numeral"` returns nothing.
- `dev/literature/devlin-II5.md`: **declined.** It is about
  Sigma-1 elementarity and the collapse. This task is a type-level
  hypothesis placement inside delivered coding machinery and reaches no
  elementarity step.
- `dev/literature/geology.md`: **declined.** Set-theoretic geology,
  grounds and mantles. Nothing in this task touches it.
- `dev/literature/glossary-review-2026-08.md`: **declined.** A review
  of `dev/glossary.toml` entries. This task adds no term and writes no
  mathematical prose (AGENTS.md:69).

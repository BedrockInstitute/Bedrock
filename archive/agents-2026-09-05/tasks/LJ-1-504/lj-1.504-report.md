# LJ-1.504 report: how far SupplyEnv's own someEnv reaches toward someEnvDef

slot: `coder`. Written early as a skeleton and filled as runs land (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-504/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: one term `someEnv-reaches` in
`agents/tasks/LJ-1-504/Probe504.agda`, `TFacts.someEnv` at `KValue`'s
frame, from `SupplyEnv.someEnv`. Nothing lands in `src/`. I did not
build a `TFacts` value. I did not edit `someEnvDef` and I did not weaken
it. I did not re-derive the nine env fields and I did not re-open the
gate.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is LJ-1 work. It
does not start that collection and it does not start phase 3. No
Boundary clause is in conflict.

## VERDICT

**STOP, STATED. The obligation is NOT inhabited, and the gap is a type.**

The probe is GREEN (exit 0, `runs/full-1.out`) and the obligation name
`someEnv-reaches` is DELIBERATELY ABSENT from it. The witness meter
agrees and reads the intended state:
`/opt/homebrew/bin/python3.11 scripts/pod/witness.py --code LJ-1-504
--brief agents/tasks/LJ-1-504/LJ-1.504.md`, exit 1, 3.01 s,
**1 UNRESOLVED of 1, `probe_red=False`** (`runs/witness-1.out`).
`.venv/bin/python` is absent in this worktree, as `[LJ-1.499]` also
found; I added no dependency.

The stop is written at `agents/tasks/LJ-1-504/review-of-someEnv-reaches.md`.

**The brief said a stop here is a good outcome and must not be avoided.
This is that stop, and it is not a failure to build: two of the three
differences CLOSED, and the third is now a checked type instead of a
suspicion.**

## THE THREE DIFFERENCES, RESOLVED OR NOT

| # | difference | resolved? | evidence |
|---|---|---|---|
| 1 | memberships in `lookup (suc⁶ K) γ` against memberships in `Lset lam` | **CLOSED** | `agents/tasks/LJ-1-504/Probe504.agda:91-92` sets `K6`, and `lookup K6 (gam' …)` is `gam'[7] = KV.Kenv[1] = LsetS lam ordλ` (`src/L/Condensation.lagda.md:7389-7390`, `:7397`). `someEnv-gated` (`Probe504.agda:102-112`) states the record's membership form and its body is one application of the supplier, which states the `Lset lam` form. Exit 0. |
| 2 | `envSetB` at a FOUR element environment against `envHypB2` at a `7 + (11 + n)` element environment | **CLOSED, AND IT IS NOT A RENAMING. IT IS A DEFINITIONAL IDENTITY.** | `envHypB2 {m} B K = envSetB zero (suc⁵ zero) (suc⁷ B) (suc⁷ K)` (`src/L/Condensation.lagda.md:654-658`). W3, `envSetB-to-envHypB2` (`Probe504.agda:80-87`), carries one to the other with the term `h`. Exit 0. |
| 3 | the supplier asks `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁`, the record does not carry it | **NOT CLOSED. IT IS THE WHOLE REMAINING DISTANCE.** | `src/L/Coding/EnvSupply.lagda.md:418` asks it; `src/L/Condensation/LowerAgree.lagda.md:52-58` does not carry it. `someEnvDef-gap` (`Probe504.agda:120-126`) states it, and `gap-suffices` (`:133-138`) PROVES it sufficient. Exit 0. |

**IN ONE SENTENCE: `TFacts.someEnv` is NOT reachable from the delivered
supplier today, and the only thing between them is the numeral
truncation.**

## D-10, BEFORE ANY AGDA

The brief said difference 2 is the whole risk and asked, at `file:line`,
what each formula asserts and whether one is the other under a renaming.

**They are the same formula constructor at two layouts, and the master
says so in its own comment.**
`src/L/Condensation.lagda.md:618-623` reads: "The environment
hypotheses, one per frame layout. Each is the two-conjunct `envSetB` at
its layout … The `E` slot is always zero; the `ar`, `B` and `K` slots are
the layout's own."

`envHypB2 {m} B K = envSetB zero (suc⁵ zero) (suc⁷ B) (suc⁷ K)`
(`src/L/Condensation.lagda.md:654-658`), and
`envSetB E ar B K = extAtB E K (envBndGen zero (suc E) (suc E) (suc ar) (suc K) (suc B))`
(`src/L/Condensation.lagda.md:567-569`). `envBndGen`'s own comment says
the same thing at `:526-528`: "The six slot positions are parameters, so
one formula serves every frame layout."

**So the D-10 question resolves to four slot lookups**, and at this
frame they hit the same four values:

| slot | record side, env `E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ gam'` | supplier side, env `E ∷ ar ∷ B₀ ∷ level ∷ []` |
|---|---|---|
| `E` | `zero` -> `E` | `zero` -> `E` |
| `ar` | `suc⁵ zero` = 5 -> `ar` | `suc zero` -> `ar` |
| `B` | `suc⁷ zero` = 7 -> `gam'[0]` = `SE.B₀` | `suc² zero` -> `B₀` |
| `K` | `suc⁷ (suc⁶ iK)` = 14 -> `gam'[7]` = `LsetS lam ordλ` | `suc³ zero` -> `level` = `LsetS lam ordλ` |

`SE.level = LsetS lam ordλ` at `src/L/Coding/EnvSupply.lagda.md:414-415`.
`KV.Kenv[1] = LsetS lam ordλ` at `src/L/Condensation.lagda.md:7390`.
`gam'` is `[LJ-1.499]`'s own vector, unchanged
(`agents/tasks/LJ-1-499/Probe499.agda:83-84`).

**The prediction from D-10 was that no lemma is needed, and the
measurement confirmed it at the cheapest point.** The brief's estimate
for W3 was about 30 lines and under 45 seconds; measured, W3 is **8
lines** (`Probe504.agda:80-87`) and **2.83 s**. I did not fund it
against `[LJ-1.499]`'s 3.04 s.

## W3, MEASURED FIRST AND ALONE

**GO, ON THE FIRST TYPECHECK, WITH THE IDENTITY.**

`envSetB-to-envHypB2` (`Probe504.agda:80-87`) has the body `h`. The two
satisfaction types are the SAME TYPE to Agda's conversion checker; the
renaming the brief feared does not exist because there is nothing to
rename.

The W3-only file is kept at
`agents/tasks/LJ-1-504/runs/Probe504.w3-only.agda.txt`. It is the file
the `w3-*` runs measured, saved with a `.txt` tail so it is not a second
module in the include path.

**NEGATIVE CONTROL, BECAUSE AN IDENTITY TERM PROVES NOTHING ON ITS OWN.**
I swapped the supplier's `B` and `K` slots
(`SE.B₀ ∷ SE.level` to `SE.level ∷ SE.B₀`) and reran. Exit **42**,
`error: [UnequalTerms]`, `lam != gam of type V ℓ`
(`runs/w3-control.out:2-3`). The conversion checker does resolve the
slots and does compare the values, so the green run is a real
measurement and not a vacuity.

## THE OBLIGATION, ATTEMPTED AND RECORDED

`runs/attempt-0.out`, exit 42. The attempt is

```agda
someEnv-reaches g1 g2 g3 g4 g5 ya yc b a ar c yaK ycK arK =
  SE.someEnv ya yc b a ar c yaK ycK arK
```

and Agda's answer is an ARITY report, not a shape report:

```
⟨ fst ar ∈ L.Constructible.Lset lam ⟩ →
Σ S (λ E → …)
!=<
Σ S (λ E → …)
```

The supplier still wants ONE more argument after the record's three
memberships are spent. That is difference 3 and there is nothing else in
the error.

## THE SWEEP (C-42)

C-42 says a refutation measures the site it names and never how far the
shape extends, so the count comes before any price.

`someEnvDef` and `someEnv` across `src/`, counted at the cited lines:

- **1** declaration: `src/L/Condensation/LowerAgree.lagda.md:52`.
- **2** record fields: `src/L/Condensation/LowerAgree.lagda.md:218`
  (`LFacts.someEnv`) and `src/L/Condensation/TwelveAgree.lagda.md:289`
  (`TFacts.someEnv`).
- **1** record fill: `src/L/Condensation/TwelveAgree.lagda.md:442`.
- **3** module parameters: `src/L/Condensation.lagda.md:3317`
  (`PropAgree`), `:3569`, `:3624`.
- **4** pass-throughs: `src/L/Condensation.lagda.md:3576`, `:3631`, and
  `src/L/Condensation/LowerAgree.lagda.md:273`, `:279`.
- **1** APPLICATION in the whole tree: `src/L/Condensation.lagda.md:3515`.
- **1** supplier: `src/L/Coding/EnvSupply.lagda.md:417`.

**THE ONE APPLICATION SITE ALREADY BINDS THE MISSING HYPOTHESIS SIX
LINES ABOVE THE CALL.** `src/L/Condensation.lagda.md:3509` reads
`(arK , (aK , (bK , arNum))) = codesK c ar a b c∈ shEq`, and `:3515`
reads `(E , (EK , henvE)) = someEnv ya yc b a ar c yaK ycK arK`. So the
threading has NO consumer that must find a new proof. `[LJ-1.488]`
reported the same two lines (`agents/tasks/LJ-1-488/lj-1.488-report.md
:280-283`) and I re-derived them at the working tree rather than
carrying the number.

**I DO NOT PRICE THE THREAD.** That is 12 sites of type change and I
have measured none of them.

## WHAT THIS ADDS TO `[LJ-1.488]`

`[LJ-1.488]`'s Repair A asked for **two** additions to `someEnvDef`:
the truncation AND a `gam` binder plus `ω∈γ`
(`agents/tasks/LJ-1-488/lj-1.488-report.md:288-292`). `[LJ-1.503]`
settled the gate and the mathematician ruled that a `TFacts` value
carries it, and this probe takes the gate from the frame
(`Probe504.agda:47-54`, `[LJ-1.499]`'s telescope) rather than from
`someEnvDef`. **So Repair A's second half is off the list, and what this
task measures is that the FIRST half is now the only half.**

## THE PRICE

Three forced rechecks each, one Agda process, wide caliber, same pane.

W3 alone (`runs/w3-1.time`, `w3-2.time`, `w3-3.time`):

| run | wall s | peak RSS bytes |
|---|---|---|
| `w3-1` | 3.05 | 553533440 |
| `w3-2` | 2.82 | 521601024 |
| `w3-3` | 2.83 | 521617408 |

Median wall **2.83 s**, median peak RSS **521,617,408 B**.

Full file (`runs/full-1.time`, `full-2.time`, `full-3.time`):

| run | wall s | peak RSS bytes |
|---|---|---|
| `full-1` | 3.00 | 533118976 |
| `full-2` | 2.92 | 533102592 |
| `full-3` | 2.91 | 533135360 |

Median wall **2.92 s**, median peak RSS **533,118,976 B**. No heap event
in any run.

**The difference between the two medians is 0.09 s and I do not report
it as the price of the gated form.** The two batches ran minutes apart
on the same pane, not interleaved, and 0.09 s is inside the spread of
the W3 batch itself (3.05 against 2.82).

The brief estimated about 160 lines in the probe, of which the
obligation is about 45. Measured: the file is 142 lines, **70** of them
non-blank and non-comment. The three terms are 8, 11 and 6 lines. **The
estimate is not funded against and nothing here was sized by it.**

The ratio bar does not fire: the write scope carries no ` ```agda `
fence, so the divisor is 0 in-fence lines and the bar binds nothing on
this task.

## WHAT THE MATHEMATICIAN NEEDS NEXT

Three things, in the order they decide the route.

1. **The field type is the question, not the supplier.** The supplier is
   right and complete. `someEnvDef` is the term that omits an input its
   own only supplier needs.
2. **`[LJ-1.172]`'s refutation sits one step away and NOBODY HAS
   MEASURED WHETHER IT REACHES `someEnvDef`.**
   `src/L/Condensation/TwelveAgree.lagda.md:296-301` records that the
   unrestricted `envSetK` is FALSE at this bound, and `envSetK` is the
   term `SupplyEnv.someEnv` uses to build `E ∈ K`
   (`src/L/Coding/EnvSupply.lagda.md:433`). If that reaches
   `someEnvDef`, the field's type is not merely under-supplied: it is
   FALSE, and the thread is mandatory rather than convenient.
   **I did not measure this and I do not claim it** (`AGENTS.md:45`).
   It is the next measurement on this front, and it is a mathematician's
   brief, not a coder's.
3. **If the thread is ruled, it is 12 sites of type change and no new
   mathematics**, and the archive already priced its shape:
   `archive/dev/LJ-dispatch-index.md:326` records `[LJ-1.257]` saying
   "The numeral premise is a MASTER change, priced at 40 to 60
   mechanical lines". That is an OLD price at an OLD tree and I do not
   carry it as this task's number.

## THE ACCOUNT

**`someEnv` is still NOT accounted.** The account stands at THIRTY NINE
of fifty nine at one frame, unchanged by this task: twenty six from
`[LJ-1.495]`, four from `[LJ-1.501]`, nine from `[LJ-1.499]`, as the
brief states. This task moved no field. It moved the question.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md`: READ AND USED.**
  `archive/dev/LJ-dispatch-index.md:326` reads
  `| LJ-1.257 | The four envInK fields and someEnv | 5 OF 5. COLLAPSE IS 67 AGAINST 85 | Bodies shrink 55 to 30. The numeral premise is a MASTER change, priced at 40 to 60 mechanical lines |`.
  It is the earliest record that the numeral premise is a MASTER change,
  and it is cited above under "WHAT THE MATHEMATICIAN NEEDS NEXT".
  `:248` reads
  `| LJ-1.172 | BUILD the supply | 1 TO 5 BUILT; 6 REFUTED AT THE JOIN. DD25 review [LJ-1.180] UPHELD | envSetK asks a level to hold a function space. Six names, one fact, no supplier |`,
  which pins the refutation this report names but does not transfer.
- **`archive/dev/JOURNAL-archived.md`: DECLINED.** `grep -c someEnv`
  returns **0**. Nothing in it bears on this field.
- **`archive/dev/JOURNAL.md`: DECLINED.** `grep -c someEnv` returns
  **0**. Same reason.
- **`archive/dev/DECISIONS-archived.md`: DECLINED.** `grep -c someEnv`
  returns **0**. The `D<n>` series resolves against it, and this task
  cites no `D<n>` code.
- **`archive/dev/DD-archived.md`: DECLINED.** `grep -c someEnv` returns
  **0**. The `DD` series is set aside in that form and this task cites
  no `DD` row.

## LITERATURE USED

- **`dev/literature/truncation-and-selection.md`: READ, AND IT DOES NOT
  CLOSE THE GAP.** `dev/literature/truncation-and-selection.md:113`
  reads `> ∥ Σ(n:ℕ) P(n) ∥ → Σ(n:ℕ) P(n).` That is the untruncation a
  reader would reach for here, and it does not apply: the supplier never
  needs to EXIT the truncation (it eliminates into a proposition at
  `src/L/Coding/EnvSupply.lagda.md:433`, `PT.rec`). What is missing is
  the truncated statement ITSELF, which no selection principle supplies.
  Reading this file is what let me say the gap is not a selection
  problem.
- **`dev/literature/devlin-II5.md`: DECLINED.** Its subject is the
  Condensation Lemma and the GCH (`:1`). This task compares two Agda
  signatures at one frame and reaches no mathematical content Devlin
  covers.
- **`dev/literature/digest.md`: DECLINED.** Its subject is the orthodox
  `rud` route (`:1`). This task touches no tower choice.
- **`dev/literature/geology.md`: DECLINED.** Its subject is
  set-theoretic geology (`:1`). No bearing on an env-set field type.
- **`dev/literature/terms-2026-08.md`: DECLINED.** It is a terminology
  dossier (`:1`). This task names no new term and adds no glossary
  entry.

## WHAT I DID NOT DO

- I did not edit or weaken `someEnvDef`.
- I did not build a term named `someEnv-reaches`, so the obligation
  reads UNRESOLVED by design.
- I did not re-derive the nine env fields (`[LJ-1.499]` forbids it).
- I did not re-open the gate (`[LJ-1.503]` settled it).
- I did not price the 12-site thread and I did not price the remaining
  nineteen `TFacts` fields.
- I did not measure whether `[LJ-1.172]`'s refutation reaches
  `someEnvDef`, and I do not claim it does.
- Nothing landed in `src/`. No commit. No push.

# LJ-1.505 review-of-1: adversarial review of the LJ-1.505#1 return

## HEAD
head_slot: mathematician_adversarial
machine: shared
verdict: upheld

## WHAT I ATTACKED, AND ONE MISSING RECORD

The return under attack is the work of the `coder` slot: the report
`agents/tasks/LJ-1-505/lj-1.505-report.md`, the probe
`agents/tasks/LJ-1-505/Probe505.agda`, and the transcripts under
`agents/tasks/LJ-1-505/runs/`. I read them against the brief
`agents/tasks/LJ-1-505/LJ-1.505.md`. The critic is not the author. The
invariant holds.

One record the brief told me to read does not exist in this worktree.
`dev/pod/transitions/2026-08.jsonl` ends at seq 158, task `LJ-1.399`,
stamp 2026-08-19. No line carrying `"task": "LJ-1.505"` is in it. The
six facts are recoverable from
`agents/tasks/LJ-1-505/runs/accept-24.out:16-23`
(`# run agents/tasks/LJ-1-505/Probe505.agda rc 0 seconds 3.07`,
`# run agents/tasks/LJ-1-505/runs/ProbeW3.agda rc 0 seconds 2.35`,
`# obligations delta 0`, `# wall seconds 2.35`, `# error class None`,
`# exit 0`) and the JSON facts at `accept-24.out:25`
(`exit_code 0`, `obligations_delta 0`, `obligations_open 1`,
`heap_wall false`, `seconds 2.35`, `lines 0`). The heads hash is at
`agents/tasks/LJ-1-505/.pod:1`. Model and effort are not in these
records. I report the absence. It is a program gap. It is not a defect
of the return.

The predecessor's verdict is GO, not a stated NO-GO. Agreement with GO
is a real result. It does not close the task through
`sys-critic-upheld-no-go`.

## QUESTION 1. DOES THE VERDICT LINE MATCH THE BODY

Yes. The verdict line is `agents/tasks/LJ-1-505/lj-1.505-report.md:7`:
`**GO.**` The body carries each part of that line.

- The probe typechecks. `Probe505.agda` is 176 lines. The obligation
  term stands at `:113-114`. Accept conjunct 1 held
  (`accept-24.out:10`). The three forced full rechecks exit 0
  (`runs/final-0.out:1`, `final-1.out:1`, `final-2.out:1`).
- W3 is green. `lengthCheck` is at `Probe505.agda:64-65` and in the
  split file `runs/ProbeW3.agda:63-64`. `11 + 9` and `6 + 14` agree
  at this frame: the term `j ∷ j ∷ j ∷ j ∷ j ∷ j ∷ KV.Kenv` elaborates
  at type `S ^ (11 + 9)`. Three forced rechecks exit 0
  (`runs/w3-0.out:1`, `w3-1.out:1`, `w3-2.out:1`).
- No `TFacts` value was built. No `src/` path is in fact 4
  (`accept-24.out:25`).
- The twenty-slot table is at `lj-1.505-report.md:32-52`. Three of
  those rows say UNCONSTRAINED. That is the answer the brief asked
  for at `LJ-1.505.md:84-88`, not a silent fill.
- Section 6 at `lj-1.505-report.md:273-275` says there is no stop
  and that the named statement is supported. That agrees with GO.

This is not the `[LJ-1.373]` defect class. The line and the body
agree on GO. The brief's own GO sentence at `LJ-1.505.md:130-132`
is the evidence for the frame decision. That evidence is the table
and the vector. Both are in the return.

The program's `go` branch at `LJ-1.505.md:141-149` also keys on
`obligations_delta_max = -1`. Accept records `obligations_delta 0`
and `obligations_open 1`. That is a packaging fact about the
witness name. It is not a second verdict in the body. Question 3
records it.

## QUESTION 2. IS EVERY LOAD-BEARING CLAIM BACKED BY A FILE:LINE THAT RESOLVES TODAY

The census, the occupants, the pin, and the wall times resolve.
Four citations are off, and one sentence overclaims. None of them
falsifies GO.

Load-bearing claims that resolve today:

- `TFacts` over `γ' : S ^ (11 + n)` with six `suc`s:
  `src/L/Condensation/TwelveAgree.lagda.md:129-133`.
- Consumer `f ∷ e ∷ d ∷ γ` with `γ : S ^ (8 + n)`:
  `src/L/Condensation.lagda.md:6971`.
- `satGraphOn` at `src/L/Coding/Graph.lagda.md:104-111`.
- `witK`'s pin `var zero ≐ var (suc (suc (suc (suc (suc (suc w))))))`
  at `src/L/Condensation.lagda.md:7010`. `appAt` in the same clause
  at `:7013-7014`. `appAt f x y` at
  `src/L/Coding/Model.lagda.md:160-161`.
- `Kenv` and the fourteen indices:
  `src/L/Condensation.lagda.md:7389-7398`. Slot 6 is `LsetS gam ordγ`
  on `:7390`. Slot 7 is `LsetS lam ordλ` on `:7390`. Slots 8 to 19
  are `numeralL 0` to `numeralL 11` on `:7391-7393`.
- `KFacts`'s first parameter is the carrier:
  `src/L/Condensation.lagda.md:6079`.
- `[LJ-1.495]` instantiates `KFacts` at `iA`:
  `agents/tasks/LJ-1-495/Probe495.agda:168`.
- Slot 0 as `SE.B₀`: `src/L/Coding/EnvSupply.lagda.md:124-125`,
  and `[LJ-1.499]` at `agents/tasks/LJ-1-499/Probe499.agda:83-84`
  and `agents/tasks/LJ-1-499/lj-1.499-report.md:209-219`.
- The ω gate: `src/L/Coding/EnvSupply.lagda.md:111`.
- `tagEq0` to `tagEq11` at
  `src/L/Condensation/TwelveAgree.lagda.md:133-144`.
  `t0eq` and `t1eq` at `:181-182`.
- Nine `envK-*` / `envInK-*` field heads at `:186`, `:192`, `:198`,
  `:204`, `:210`, `:216`, `:223`, `:230`, `:237`.
- Slot 1 lookups at `:173` and `:177`. Slot 1 formula-args at
  `:265`, `:271`, `:277`, `:283`, `:290`, `:311`, `:326`.
  `subValAt`'s first argument is the graph:
  `src/L/Coding/Model.lagda.md:817-818`.
- Slot 2 lookups at `:162`, `:168`, `:173`, `:177`.
- LeafAgree's uses of the outer front: `DefinesAgree` is
  `(x w v K N0)` at `src/L/Condensation.lagda.md:6882`, instantiated
  at `:7323-7324` so `v` is `zero` (γ' slot 3) and `x` is
  `suc (suc zero)` (γ' slot 5). `WitnessAgree`'s `x` is `suc zero`
  at `:7307` (γ' slot 4). `KeyAgree`'s `c` is `suc zero` at `:7316`
  (γ' slot 4).
- `AllCodes` at `src/L/Coding/CodeSet.lagda.md:440`,
  `IsKeyOverAny` at `:434-437`, `key∈AllCodes` at `:443`.
- `Sat` at `src/L/Coding/Sat.lagda.md:142`.
- The 59-field count. I re-ran `runs/census.py` and
  `runs/census-slots345.py`. Both reproduce the tracked outputs:
  slot 0 has 9, slot 1 has 9, slot 2 has 4, slots 3, 4 and 5 have 0
  under every prefix depth. `someEnvDef` at
  `src/L/Condensation/LowerAgree.lagda.md:52-58` names only
  `suc^6 K`. It does not name slots 3, 4 or 5.
- Full-file wall times: `final-0.time:1` is 3.11, `final-1.time:1`
  is 3.08, `final-2.time:1` is 3.04. Median 3.08 s. Peak RSS
  653164544 bytes on all three (`final-0.time:2`, `final-1.time:2`,
  `final-2.time:2`).
- W3 wall times: `w3-0.time:1` is 2.32, `w3-1.time:1` is 2.29,
  `w3-2.time:1` is 2.18. Median 2.29 s.

Four citations that do not resolve as written:

1. `lj-1.505-report.md:195` cites
   `agents/tasks/LJ-1-495/Probe495.agda:169` for the `iA`
   instantiation. Line 169 is `Shared26` with `i0` first. The
   `KFacts iA` line is `:168`. The claim is true at the adjacent
   line.
2. `lj-1.505-report.md:195` cites
   `src/L/Condensation.lagda.md:6680-6682` as `KFacts`'s first
   parameter. Those lines are `WitnessAgree`. The record is at
   `:6079`. The claim is true at the right site.
3. `lj-1.505-report.md:14` and `:221-223` call 611041280 the W3
   peak RSS. That figure is `w3-0.time:2` and `w3-2.time:2`. The
   peak of the three runs is 611074048 at `w3-1.time:2`. The
   reported figure is the median RSS, not the peak.
4. `lj-1.505-report.md:275` says the statement is discharged.
   The named obligation is
   `agents/tasks/LJ-1-505/Probe505.agda::gammaPrime`
   (`LJ-1.505.md:41`). I ran the witness meter on that string.
   The derived line is `witness = Target.gammaPrime`. The result
   is `missing`, exit 42, `[NotInScope]`, `probe_red=False`,
   2.44 s. Accept already recorded `obligations_open 1`. The
   term that typechecks is `Frame.gammaPrime` at
   `Probe505.agda:113-114`, inside `module Frame` at `:77`.
   I ran the same meter on
   `agents/tasks/LJ-1-505/Probe505.agda::Frame.gammaPrime`.
   It is `pass`, exit 0, 2.45 s. The vector exists. The brief's
   dotted name does not.

The measurement of the census is sound. I did not transfer a
cure by analogy. The slot-1 claim that no named `S`-valued
satisfaction graph exists is still true under a check of
`src/L/Coding/`: `satGraph` at
`src/L/Coding/Graph.lagda.md:238` is `Formula S 2`, and
`graph` at `src/L/Coding/Bridge.lagda.md:168` is `V ℓ`.

## QUESTION 3. IS THE PREDECESSOR'S ENUMERATION COMPLETE

No. Three gaps. None of them moves GO.

**F1. The return does not report that the named obligation is
unresolved.** The table, the vector and W3 are complete as
evidence for the frame. The witness name is not. The brief
wrote `::gammaPrime` and the term sits in `module Frame`.
`Target.gammaPrime` is out of scope. `Target.Frame.gammaPrime`
is in scope. The missed cure is one of two lifts: name
`Frame.gammaPrime` in the obligation, or put Frame's telescope
on the top-level module so `gammaPrime` is visible after the
header `{ℓ} (lem : LEM (ℓ-suc ℓ))`. The first lift is a brief
edit. The second was available to this return. The brief
caused the trap: it demanded `gammaPrime : S ^ (11 + 9)` at a
frame that needs `KValue` and `SupplyEnv`, and it kept the
standard two-binder header. It did not foreclose GO. It
foreclosed the `go` branch as written.

**F2. W3 peak RSS is the median RSS.** See question 2, item 3.
The median wall time 2.29 s is correct.

**F3. Two predecessor citations are off by a line or a module.**
See question 2, items 1 and 2. The pin still holds:
`pin-holds` is `refl` at `Probe505.agda:135-136`, and slot 0
equals slot 6 because `SE.B₀` is `LsetS gam ordγ`.

The six-front-slot split in the table is complete. Slot 0 is
pinned. Slots 1 and 2 are role-named and object-free. Slots 3,
4 and 5 are unread by `TFacts` and used by `LeafAgree`. The
return did not invent a requirement to fill them
(`LJ-1.505.md:84`). W2 is answered at
`lj-1.505-report.md:254-258`. W3 named the length and the
probe `lengthCheck`; the coder wrote that probe. W4 does not
fire. W8 does not fire: this is not a provability axiom.

The brief did not cause a false GO. Length holds. The census
holds. The unconstrained rows are the honest answer.

## ARCHIVE USED

- **`archive/dev/JOURNAL.md`. Not read.** Declined. The attack
  is of a live census, a live probe and a live witness meter.
- **`archive/dev/ORCHESTRATION.md`. Not read.** Declined. The
  three questions and the four-question lens have live homes.
- **`archive/dev/DD-archived.md`. READ.** `:35` reads:
  `is the refusal correct on its own numbers`
  That is the first of the four questions I used as the lens.
- **`archive/dev/PLAN-archived.md`. Not read.** Declined. The
  construction registry is not a rule in force on this review.
- **`dev/ARCHIVE.md`. Not read.** Declined. W4 does not fire:
  no module was retired.

## LITERATURE USED

- **`dev/literature/devlin-II5.md`. Not read.** Declined. This
  review attacks a slot census of an existing port, not II.5.
- **`dev/literature/BIBLIOGRAPHY.md`. Not read.** Declined. No
  source list was in question.
- **`dev/literature/digest.md`. Not read.** Declined. The
  orthodox rud route is not the object of the return.
- **`dev/literature/geology.md`. Not read.** Declined. Geology
  is not this frame.
- **`dev/literature/devlin-errata.md`. Not read.** Declined. No
  Devlin error class is at issue.

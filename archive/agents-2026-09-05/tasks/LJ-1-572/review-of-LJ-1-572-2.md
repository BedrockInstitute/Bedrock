# review-of-LJ-1-572-2: adversarial review of the LJ-1.572#2 return

## HEAD
head_slot: coder_adversarial
machine: shared
verdict: upheld

The return under attack is `agents/tasks/LJ-1-572/lj-1.572-report.md` with
its NO-GO statement `agents/tasks/LJ-1-572/review-of-b9-g-definable.md`.
I attacked the return, not the task. I re-opened the load-bearing cites.
I started one Agda process, on the narrowed file, at the pane caliber.
I did not set `GHCRTS`. The NO-GO stands.

## 0. THE INSTANCE RECORD

`dev/pod/transitions/2026-08.jsonl` in this worktree has 157 lines and
carries no `"task": "LJ-1.572"` row. The worktree copy ends before this
instance. I take no `model`, `effort`, or `heads_sha256` from it. The
six facts are the newest accept arm,
`agents/tasks/LJ-1-572/runs/accept-3.out`. The earlier arms
`accept-1.out` and `accept-2.out` are the same check, earlier.

Newest arm (`accept-3.out`):

- caliber `-A64m -I0 -M8g`, tier `wide` (`accept-3.out:5-6`)
- `run agents/tasks/LJ-1-572/Probe572.agda rc 0 seconds 3.32`
  (`accept-3.out:16`)
- `run agents/tasks/LJ-1-572/runs/Frame.agda rc None seconds 1800.01`
  (`accept-3.out:17`)
- conjunct 1 FAILED; conjuncts 2 to 6 held (`accept-3.out:10-15`)
- `error_class` `timeout`, `exit_code` null, `heap_wall` false
  (`accept-3.out:22-23`, JSON on `:25`)
- `agda slots during 4`, load before
  `(3.28271484375, 3.16748046875, 3.15576171875)` (`accept-3.out:7-8`)
- `obligations_delta` 0, `obligations_open` 1 (`accept-3.out:20`, JSON)
- `unbound_vacuous` true, `agda_vacuous` false (JSON on `:25`)
- `changed files 18` (`accept-3.out:18`). The JSON list includes
  `agents/tasks/LJ-1-572/review-of-LJ-1-572-1.md`. A critic file that
  already UPHELD this NO-GO was in the write set. The timeout still
  fired on `Frame.agda`.

Earlier arms, same target:

| arm | Probe572 | Frame.agda | concurrency | load before | critic file in write set |
|---|---|---|---|---|---|
| `accept-1.out:16-17` | 2.88 s, rc 0 | 1800.01 s, rc null | 3 (`:7`) | `(4.32275390625, 3.73486328125, 3.33984375)` (`:8`) | no (`:18`, 17 files) |
| `accept-2.out:16-17` | 3.49 s, rc 0 | 1800.02 s, rc null | 4 (`:7`) | `(4.53173828125, 4.41015625, 5.95068359375)` (`:8`) | yes (`:18`, 18 files) |
| `accept-3.out:16-17` | 3.32 s, rc 0 | 1800.01 s, rc null | 4 (`:7`) | `(3.28271484375, 3.16748046875, 3.15576171875)` (`:8`) | yes (`:18`, 18 files) |

`dev/pod/heads.toml:264` sets `agda_deadline_s = 1800`.
`scripts/pod/facts.py:116-117` writes class `timeout` when that deadline
fires. That is the program measurement this review was sent to attack.

## WHY THIS ESCALATED: THE ACCEPTANCE CHECK ITSELF TIMED OUT

The brief of this review orders three answers on the timeout. They are
below. They are not a claim the predecessor made. They are the
measurement on `accept-3.out`, and they are the same measurement on
`accept-1.out` and `accept-2.out`.

### Why the check did not finish in time

The check that ran past the deadline is
`agents/tasks/LJ-1-572/runs/Frame.agda`, not
`agents/tasks/LJ-1-572/Probe572.agda`.

`scripts/pod/facts.py:463-466` puts every changed `.agda` file under the
task home into the conjunct-1 target list, in path order. The accept
arm lists four such files (`accept-3.out:25`): `Probe572.agda`,
`runs/Frame.agda`, `runs/Frame2.agda`, `runs/W3.agda`. Path order puts
`Probe572.agda` first and `runs/Frame.agda` second.
`scripts/pod/accept.py:165-166` stops at the first target whose `rc` is
not 0. `Probe572.agda` returned `rc 0` in 3.32 s. `Frame.agda` then ran
until `agda_deadline_s`. `Frame2.agda` and `W3.agda` were never started
by the runner.

The terms that do not finish are the two applications at
`agents/tasks/LJ-1-572/runs/Frame.agda:132-136` (`p566-at-B9-a`) and
`:143-149` (`p566-at-B9-b`). Each applies `P566.injcode-assembled` at
`LsetS δ oδ` under a hypothesized `IsOrd (fst (LsetS δ oδ))`. The same
file without those two applications is `runs/Frame2.agda`. That file
keeps the type ascription `p566-frame` (`Frame2.agda:123-126`) and the
carrier identity `B9-a-carrier` (`Frame2.agda:139-140`).

The hang is runaway elaboration, not a heap wall and not contention as
the cause.

- Not a heap wall. `accept-3.out:25` records `heap_wall` false. The
  author's cold run of the same file had RSS static at 2,314,080 KB
  against the `-M8g` cap, exit 143, 1360.52 s
  (`agents/tasks/LJ-1-572/runs/frame-1.out:8,26-30`). CPU time there
  equalled elapsed time (1357.50 user + 3.23 sys against 1360.52 real).
- Not contention as the cause. Accept-1 had concurrency 3 and a higher
  load (`accept-1.out:7-8`). Accept-3 had concurrency 4 and a lower
  load (`accept-3.out:7-8`). Both hit the same 1800 s deadline on the
  same file. The author's own live snapshot of the same file shows the
  Frame process at 100.0 % CPU
  (`agents/tasks/LJ-1-572/runs/contention-1.out:4`) and
  `frame-1.out:29` records CPU time equal to elapsed time. The process
  held one core. Other writers on the shared machine did not produce
  the hang. Accept-3 is the cleanest of the three arms on this point:
  its load before is the lowest, and `Frame.agda` still ran to the
  deadline.
- The obligation file is not the hang. `Probe572.agda` does not apply
  `injcode-assembled` at B9's `a`. It ascribes the delivered signature
  (`Probe572.agda:185-188`) and identifies the carrier by `refl`
  (`Probe572.agda:197-198`). That is why conjunct 1's first run was
  3.32 s and exit 0, on every arm.

The predecessor already knew the file did not finish. The report table
records the cold kill and the warm kill (`lj-1.572-report.md:37`). The
stop file says the file "does not typecheck in bounded time"
(`review-of-b9-g-definable.md:159-160`). The author still left
`Frame.agda` in the write scope. Conjunct 1 then re-ran it against a
deadline of 1800 s, three times. That is why this review exists, and
it is why a prior critic file did not close the task.

### Whether the same check terminates

I did not re-run `Frame.agda`. The slot clause permits one Agda process.
Five measurements of the same file already exist:

| run | interfaces | wall | result | record |
|---|---|---|---|---|
| author, cold | cold chain | 1360.52 s | killed, exit 143 | `runs/frame-1.out:8,26` |
| author, warm | warm | past 300 s | killed | `runs/frame-2.out:2` |
| acceptance, first | after `Probe572.agda` at 2.88 s | 1800.01 s | `rc` null, timeout | `accept-1.out:17` |
| acceptance, second | after `Probe572.agda` at 3.49 s | 1800.02 s | `rc` null, timeout | `accept-2.out:17` |
| acceptance, newest | after `Probe572.agda` at 3.32 s | 1800.01 s | `rc` null, timeout | `accept-3.out:17` |

Accept-3 is already "the same check, re-run" and already "more time"
than either author kill. It is also the second re-run after a critic
file existed. It still did not decide. I do not know whether the term
typechecks at all. A sixth run under the same caliber would not become
comparable by being longer than the program's own deadline. I do not
give the check more time. I narrow it.

### Whether the term can be narrowed

Yes. `runs/Frame2.agda` is that narrowing. It is the same D-10 slice
with the two applications removed (`Frame2.agda:128-132`). The
frame-mismatch question that the brief asked, "IF `[LJ-1.566]`'s FRAME
IS NOT B9's FRAME, SAY SO AND STOP" (`LJ-1.572.md:81-83`), is a
type-level fact:

- `injcode-assembled` demands `IsOrd (fst a)` and returns
  `InjCode (Carve.G a oa) a (Carve.C a oa)`
  (`agents/tasks/LJ-1-566/Probe566.agda:492-494`).
- B9's `a` is `LsetS δ oδ`, and `fst (LsetS δ oδ) ≡ Lset δ` holds by
  `refl` (`Probe572.agda:197-198`;
  `src/L/Axioms/Basic.lagda.md:160-161` is `LsetS β oβ = Lset β , …`).
- B9's `b` is `ordS δ oδ` (`agents/tasks/LJ-1-568/Probe568.agda:102-103`),
  given. `[LJ-1.566]`'s `b` is `Carve.C`, an output
  (`Probe566.agda:323-324`).

That question does not need the applications. I typechecked
`Frame2.agda` once, alone, at the pane caliber `-A64m -I0 -M8g`, which
I did not set. At start, no other Agda typechecker was live: the
watchdog was the only `agda` match besides this process. Result:
1.65 s real, 1.48 s user, exit 0, RSS 415,498,240 bytes. The author's
warm figure on the same file was 1.83 s, exit 0 (`runs/frame2-1.out:2,20`).
The two numbers compare inside one caliber.

**Verdict on the timeout: the check should be narrowed.** The
underlying term in `Frame.agda` is not known to fail, and it is not
known to succeed. It does not finish in 1800 s, three times. The
narrowed file answers the same frame question in under two seconds.

P-l is the better reading of the hang than the predecessor's sentence
"the carve at a non-ordinal carrier does not reduce"
(`lj-1.572-report.md:241`). `p566-at-B9-a` names `LsetS δ oδ` in its
TYPE (`Frame.agda:134-135`). `Lset` is a transparent construction.
`dev/LESSONS.md:2360` states the cost: "transparent construction in a
statement's TYPE is." The hypothesized `h : IsOrd (fst (LsetS δ oδ))`
means the elaborator treats the carrier as an ordinal. The predecessor
did not apply `injcode-assembled` at a real ordinal as a control, so
the ascription "non-ordinal" is not measured. I did not write that
control: this review's write scope is this file only. The hang of the
applications remains a fact. It is not required for the NO-GO. Defect
D2 below.

The cure the return missed for THIS timeout is mechanical: after the
hang was recorded in `runs/frame-1.out`, keep `Frame2.agda` and do not
leave the two applications in a changed `.agda` file. Conjunct 1 would
then have run `Probe572.agda`, `Frame2.agda`, and `W3.agda`, all of
which the author already had green. That cure does not inhabit
`b9-g-is-definable`. It would have let acceptance finish.

It would also have let the close-row fire. `sys-critic-upheld-no-go`
(`dev/pod/table.toml:4307-4321`) needs `exit_code = 0` (`:4318`). A
timeout writes `exit_code` null (`accept-3.out:23`). The close row
therefore does not match. `sys-timeout-escalate`
(`dev/pod/table.toml:71-82`) matches `error_class = timeout` (`:82`)
and escalates here again. Accept-3 is that loop, measured after a
critic file already existed: `review-of-LJ-1-572-1.md` is in
`changed_files` (`accept-3.out:25`) and conjunct 1 still died on
`Frame.agda`. This review cannot remove that file. The write scope is
this review only. If conjunct 1 still sees `Frame.agda` after this
file lands, the same timeout row will match a fourth time.

## 1. QUESTION ONE: DOES THE VERDICT LINE MATCH THE BODY?

Yes. The HEAD line is `verdict: NO-GO` (`lj-1.572-report.md:6`). The
body delivers that: `Probe572.agda` binds no term named
`b9-g-is-definable` (`Probe572.agda:10-13`; a search of the task
directory finds the name only in comments, in the brief, and in the
stop file). `--safe` is on (`Probe572.agda:1`). No postulate and no
hole stand in. `review-of-b9-g-definable.md` is the stop
(`review-of-b9-g-definable.md:5-8`). `obligations_delta` 0 and
`obligations_open` 1 on the accept arm agree.

The three reasons in the stop file are the body of the line, and each
one is a type-level fact in a file that typechecks:

1. `InjCode` has type `S → S → S → Type _` (`src/L/Cardinal.lagda.md:223`).
   Both halves of `Def` mention `g` (`agents/tasks/LJ-1-554/Probe554.agda:83-86`).
   `injcode-names-no-function = InjCode` (`Probe572.agda:162-163`)
   checks the arity. Neither direction is supplied.
2. The frame of `injcode-assembled` is not B9's frame. The signature
   is checked (`Probe572.agda:185-188`). The carrier of B9's `a` is
   `Lset δ` (`Probe572.agda:197-198`). `IsOrd (Lset δ)` is not
   supplied. The `b` of `[LJ-1.566]` is an output. The brief ordered
   a stop on a named frame mismatch (`LJ-1.572.md:81-83`).
3. `InjL a b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁` (`src/L/GCH.lagda.md:37-38`).
   `B9-obligation-unfolds` checks that identity by `refl`
   (`Probe572.agda:241-245`). An `InjCode` at B9's pair is B9's
   obligation, not material for `Def`.

I pressed the strongest counter-reading: the accept arm timed out, so
perhaps the NO-GO is an unread live record of the `[LJ-1.376]` class,
or a line that the body cannot back because `Frame.agda` never
finished. It fails. The obligation file is green at 3.32 s on the
newest arm. The stop does not depend on `Frame.agda` finishing. The
narrowed file, which I re-ran, is green at 1.65 s. The timeout is a
process fact about a side file the author left in the write scope. It
is not a disagreement between the verdict line and the body.

One sentence of the report overclaims, and it is not on the verdict
path. Report `:28` says "three files that typecheck and one that does
not." `Frame.agda` was killed and then timed out, three times. It was
not observed to produce a type error. The stop file is the accurate
form: "does not typecheck in bounded time"
(`review-of-b9-g-definable.md:159-160`). That is defect D1. It does
not move the line.

On the `[LJ-1.375]` / `[LJ-1.376]` failure class: the line matches the
body. The live record of the timeout is the accept arm, and this
review reads the newest one.

## 2. QUESTION TWO: IS EVERY LOAD-BEARING CLAIM BACKED BY A `file:line` THAT RESOLVES TODAY?

Yes on the verdict path. I re-opened the cites the NO-GO stands on.
Each one resolves at the named line today.

| claim | cite | today |
|---|---|---|
| `Def a b g` is `LinkAt a (val a b g)` | `Probe568.agda:189-190` | yes, `Def a b g = P554.LinkAt a (val a b g)` |
| `LinkAt` is a `Formula S 3` with both directions | `Probe554.agda:81-86` | yes, Σ over `Formula S 3`, both halves mention the map |
| `svAt` arity-polymorphic | `src/L/Coding/Model.lagda.md:210` | yes, `svAt : ∀ {n} → Fin n → Formula S n` |
| `domAt` arity-polymorphic | `src/L/Coding/Model.lagda.md:278` | yes, `domAt : ∀ {n} → Fin n → Fin n → Formula S n` |
| `injAt` arity-polymorphic | `src/L/Coding/Injection.lagda.md:44` | yes, `injAt : ∀ {n} → Fin n → Formula S n` |
| `InjCode` used at `(F ∷ a ∷ [])` | `src/L/Cardinal.lagda.md:225-227` | yes |
| `InjCode` takes three sets | `src/L/Cardinal.lagda.md:223` | yes |
| `InjL` unfolds to truncated `InjCode` | `src/L/GCH.lagda.md:37-38` | yes |
| B9 from `W` at `stage-card-upper` | `Probe561.agda:376-381` | yes |
| `injcode-assembled` signature | `Probe566.agda:492-494` | yes |
| carve runs on `OrdSWO∈ₛ.w` | `Probe566.agda:129-130` | yes |
| carve `C` is produced | `Probe566.agda:323-324` | yes, `C = B.C` |
| `ordS` | `Probe568.agda:102-103` | yes |
| `B9-g` is `stage-card-upper` | `Probe568.agda:144-147` | yes |
| `graph→def` | `Probe568.agda:368-371` | yes |
| `W` concludes a graph L-set | `Probe561.agda:160-163` | yes |
| `restrict→B9` | `Probe568.agda:285-291` | yes |
| `def-restricted` / `Def∥` | `Probe568.agda:252-262` | yes |
| `no-free-lunch-at-B9` | `Probe568.agda:454-463` | yes |
| `B9-any-g` | `Probe568.agda:490-495` | yes |
| `hasSeparationL` takes an arbitrary formula | `src/L/Axioms/Full.lagda.md:144-145` | yes |
| `sq` is a module parameter | `src/L/StageCardinal.lagda.md:17-19` | yes |
| `stage-card-upper = ∈-induction step` | `src/L/StageCardinal.lagda.md:564-566` | yes |
| `step` is `limit-step` at the branch | `src/L/StageCardinal.lagda.md:561-562` | yes |
| `Bound` uses `sq` | `src/L/StageCardinal.lagda.md:283` | yes |
| `SqFam` | `src/L/StageBound.lagda.md:36-40` | yes |
| `SqCollect` "Not inhabited" | `src/L/StageBound.lagda.md:42` | yes |
| `SqAt` is bill row 2 | `Probe550.agda:309-310` | yes |
| bill `gch-from-five` | `Probe564.agda:456-464` | yes |
| `StageCountedCoded` has no `sucV`/`ω` side condition | `Probe564.agda:127-130` | yes |

The arity rows `svAt₃`, `domAt₃`, `injAt₃` in `Probe572.agda:140-147`
are green in a file acceptance typechecked in 3.32 s. I did not
re-price them. The pane caliber is the accept caliber, and a second
Agda process is forbidden.

Two ascriptions are slightly loose and do not carry the verdict:

- Report `:218` says the warm `Frame.agda` run was killed "past 300 s".
  `runs/frame-2.out:2` is the note `# KILLED AT 300 s, WARM INTERFACES.`
  The file carries no `/usr/bin/time` line. The "past 300 s" is the
  author's kill note, not a measured wall. The 1360.52 s, 1800.01 s,
  1800.02 s and 1800.01 s figures are measured.
- `Frame.agda:88` cites `Probe554.agda:83-88` for the two halves. The
  halves end at `:86`. The report cites `:83-86`, which resolves.

## 3. QUESTION THREE: IS THE PREDECESSOR'S ENUMERATION COMPLETE?

The mathematical enumeration of the stop is complete for the obligation
this brief named. The process enumeration is not.

**Complete, and it is why the NO-GO stands.**

- D-10 first: the arity is free. Measured at `Probe572.agda:140-147`.
  The brief called this "the whole risk in this task" (`LJ-1.572.md:73`).
  The return answers that sentence and does not hide it.
- D-10 second: `InjCode` supplies neither direction. Measured at
  `Probe572.agda:162-163` against `Probe554.agda:83-86`.
- Frame mismatch on `a` and on `b`. Measured at `Probe572.agda:185-188`
  and `:197-198`, from `Probe566.agda:492-494` and `:323-324`.
- Dependency inversion: `InjCode` at B9's pair is `InjL`, which is B9.
  Measured at `Probe572.agda:241-245` against `src/L/GCH.lagda.md:37-38`.
- The obligation, taken as a hypothesis, pays B9 at the corrected
  target. Measured at `Probe572.agda:327-334`.
- W3 unfolds `g` to `sq`. Measured at `Probe572.agda:265-275` and
  `runs/W3.agda`, green in `runs/w3-2.out:2` at 421.37 s cold.
- `sq` has type `SqFam α₀`. Measured at `Probe572.agda:309-311`.
- Bill: no row paid. `StageCountedCoded` as the bill states it is
  stronger than B9 at the corrected target (`Probe564.agda:127-130`
  against `Probe561.agda:376-381`). The return does not read a
  discharge into a type it did not inhabit.
- Rows 1, 2, 3 and 5 were not attempted. AD12 held.
- Nothing landed in `src/`. No postulate. No commit.

**Incomplete, and none of it inhabits the obligation.**

1. The author did not enumerate that a known-runaway `.agda` file in
   `runs/` is a conjunct-1 target (`scripts/pod/facts.py:463-466`).
   That omission is what sent this review. The mathematical stop was
   already in `Probe572.agda`, `Frame2.agda`, and `W3.agda`. Accept-3
   shows the omission still binds after a critic file exists: the
   timeout row matches, the upheld-close row does not, because
   `exit_code` is null.
2. The author did not apply `injcode-assembled` at a real ordinal. The
   sentence "at a carrier that is not an ordinal the carve has nothing
   to reduce against" (`lj-1.572-report.md:240-241`) is therefore an
   ascription, not a bisect. Defect D2. The type-level mismatch does
   not need that ascription.
3. The return does not answer W2 by name. The work that exists is
   generic: `injcode-assembled` is imported, not rebuilt
   (`Probe572.agda:188`). The conflict the rule names did not arise.
   A named answer is still owed. Defect D3.

**Did the brief cause the outcome?** The mathematical NO-GO, yes. The
brief's premise that the assembled `InjCode` formulas are the way to
define B9's `g` inverts the dependency, and the brief itself ordered
a stop on a frame mismatch. The timeout, no: the brief's write scope
includes `runs/`, but the author chose to leave the two applications
in a file conjunct 1 must re-run after measuring that they do not
finish.

**Is there a cure the return missed for the obligation?** No. A
definable `sq` would make `Def` true at this `g`, and the return
states that limit (`lj-1.572-report.md:65-68`). The classical
`<ʟ`-least witness map is a different `g`
(`Probe568.agda:485-489`; `dev/literature/devlin-II5.md:259-270`).
AD12 gives this brief one obligation. Building that map would have
been a different task. I do not treat it as a missed cure of this
return.

W2 on this review: I write no Agda. There is no carrier to instantiate.
W4: no module moved.

## DEFECTS (none moves the verdict)

- **D1.** Report `:28` says `Frame.agda` "does not typecheck". The
  measured fact is that it does not finish in 1800 s. The stop file
  already has the accurate form.
- **D2.** The hang of `p566-at-B9-a` / `p566-at-B9-b` is real. The
  cause-ascription "non-ordinal carrier" is not measured. P-l plus
  `Lset` in the type is the reading that the tree already names.
- **D3.** W2 is not answered by name.

**Verdict: upheld.** The NO-GO of LJ-1.572#2 stands. `b9-g-is-definable`
is not delivered. The acceptance timeout is a runaway elaboration of
two applications in `runs/Frame.agda`. The same question, narrowed to
`runs/Frame2.agda`, typechecks in 1.65 s at the pane caliber. The
check should be narrowed. It should not be given more time.

## ARCHIVE USED

Five CANDIDATE paths. One used. Four declined.

- `dev/ARCHIVE.md`: read at `dev/ARCHIVE.md:1`. Quote: `# ARCHIVE.md: the archive registry`.
  **DECLINED, not used.** W4 did not fire. No module moved. The
  registry of retired modules does not bear on a timeout of
  `Frame.agda` or on a NO-GO that lands nothing in `src/`.
- `archive/dev/JOURNAL.md`: read at `archive/dev/JOURNAL.md:1`. Quote: `# ARCHIVED 2026-08-20`.
  **DECLINED, not used.** The per-episode journal is retired. The
  facts of this instance are the accept arm, which this worktree
  holds.
- `archive/dev/ORCHESTRATION.md`: read at `archive/dev/ORCHESTRATION.md:1`. Quote: `# ORCHESTRATION: the orchestrator's operating rules`.
  **DECLINED, not used.** The live acceptance rule that selected
  `Frame.agda` is `scripts/pod/facts.py:463-466`, not this archived
  operating text.
- `archive/dev/DD-archived.md`: **READ AND USED.** Read at `archive/dev/DD-archived.md:35`.
  Quote: `The questions are: is the refusal correct on its own numbers; is the measurement sound; did the BRIEF cause the outcome; and is there a cure the return missed.`
  Used: these four are the lens this slot attacks with. They are not
  the three questions this file writes. The timeout investigation
  above is the measurement-soundness question applied to the accept
  arm, not to a claim in the report.
- `archive/dev/PLAN-archived.md`: read at `archive/dev/PLAN-archived.md:1`. Quote: `# ARCHIVED 2026-08-20`.
  **DECLINED, not used.** The retired construction registry does not
  bind this review.

## LITERATURE USED

Five CANDIDATE paths. One used. Four declined.

- `dev/literature/devlin-II5.md`: **READ AND USED.** Read at `dev/literature/devlin-II5.md:259`.
  Quote: `Requirement: a definable well-order of L_α, used to pick the <_L-least`.
  Used: this is the object the predecessor named as a different `g`
  and a different task (`lj-1.572-report.md:305-312`;
  `Probe568.agda:485-489`). I checked the cite. It resolves. It is
  not a missed cure of this obligation.
- `dev/literature/level-formula-slot-roles.md`: read at `dev/literature/level-formula-slot-roles.md:1`. Quote:
  `# The level-hood formula: arity, what it binds, what stays free`.
  **DECLINED, not used.** Slot arithmetic of the level-hood formula
  is not the arity this task measured. This task's arity is
  `Formula S 3` against `svAt` / `domAt` / `injAt`.
- `dev/literature/BIBLIOGRAPHY.md`: read at `dev/literature/BIBLIOGRAPHY.md:1`. Quote: `# Bibliography for the rud route`.
  **DECLINED, not used.** No new source was fetched. The Devlin cite
  was verified in `devlin-II5.md` directly.
- `dev/literature/digest.md`: read at `dev/literature/digest.md:1`. Quote: `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  **DECLINED, not used.** It pins the rud route. This site is the
  `defSet` tower and `Def`.
- `dev/literature/geology.md`: read at `dev/literature/geology.md:1`. Quote: `# Geology dossier: set-theoretic geology sources and the five questions`.
  **DECLINED, not used.** Set-theoretic geology does not bear on
  `Def` at B9's `g`, and campaign `[L6]` is not open.

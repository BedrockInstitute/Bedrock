# LJ-1.483: adversarial review of LJ-1.483#1

## HEAD
head_slot: mathematician_adversarial
machine: shared
verdict: upheld

## WHAT WAS ATTACKED

The return of LJ-1.483#1: the coder instance `grok-4.6`, effort
`high`, `heads_sha256 5f213519`, recorded at
`dev/pod/transitions/2026-08.jsonl` seq 1577, 1599 and 1602. Its
deliverables are `agents/tasks/LJ-1-483/lj-1.483-report.md`, the
probe `agents/tasks/LJ-1-483/Probe483.agda`, the stop file
`agents/tasks/LJ-1-483/review-of-someEnv-at-codesK.md`, and eight
run records under `agents/tasks/LJ-1-483/runs/`. The acceptance
facts are in `agents/tasks/LJ-1-483/runs/accept-1.out`: exit 0,
seconds 2.74, obligations delta 0, obligations open 1, changed
files 19, heap wall false, row `task-lj-1-483-stop-stated`.

The verdict under attack is STOP, with the claim that the work
forces Reading 1. The critic is not the author: the coder ran as
pid 6026; this review is a separate dispatch, pid 20454.

Every check below was made by me on this tree today. I wrote no
Agda and I changed no file except this one.

## Q1. DOES THE VERDICT LINE MATCH ITS OWN BODY? YES

The verdict line, at `agents/tasks/LJ-1-483/lj-1.483-report.md`
under `## VERDICT`, states five things. Each is backed by the body
of the same report, and each backing is true in the tree:

1. "W3 is GO: `no-code` typechecks". The term is at
   `agents/tasks/LJ-1-483/Probe483.agda:90-96`. The runs
   `w3-1.out` through `w3-4.out` all print `Checking` and the
   `.time` files all record a completed process. The chain is
   sound: `C-slot = refl` at `:86-87` fixes
   `lookup C Kenv' = numeralL 0`;
   `numeralL-fst : (n : ℕ) → fst (numeralL n) ≡ # n` at
   `src/L/Axioms/Numerals.lagda.md:179`; `∅-empty` closes. Agda
   accepted it, exit 0, four times.
2. "`arNum-from-codesK` typechecks". At
   `Probe483.agda:109-114`, the third projection of the module
   hypothesis `codesK` at `:100-106`. Same runs, same file.
3. "The domain of `codesK` at this frame is empty". Backed by
   D-10 and by `no-code`: C is `suc (suc zero)` at `:79-80`, the
   pad's slot 2 is `numeralL 0` at `:70-73`, so the C-membership
   premise of `codesK` is refuted for every `c`. The C index is
   AbstractFrame's own, at `src/L/Condensation/TwelveAgree.lagda.md:494`
   and `src/L/Condensation/LowerAgree.lagda.md:255`.
4. "The named obligation was not written". True. The string
   `someEnv-at-codesK` occurs in no probe line that declares a
   term, and the acceptance record reports obligations delta 0
   with obligations open 1.
5. "The work forces Reading 1". Backed by section 3 and by the
   site table: `someEnvDef` at
   `src/L/Condensation/LowerAgree.lagda.md:52-58` takes three
   memberships and nothing else; `SupplyEnv.someEnv` at
   `src/L/Coding/EnvSupply.lagda.md:417-424` demands the
   truncation at `:418`; `codesK` at
   `src/L/Condensation.lagda.md:2782-2786` yields that truncation
   only after a C-membership (`:2782`) and a shape equation
   (`:2783`); `[LJ-1.480]` refuted the truncation from
   K-membership
   (`agents/tasks/LJ-1-480/lj-1.480-report.md:66-75`). No other
   source exists at the field. The body says this with the same
   numbers.

The body contains no statement that contradicts the verdict line.
The sharpest body claim, that the truncation has a source at the
clause lambdas and not at the field, is not a contradiction: the
report states plainly that a local at `PropAgree.back` would
inhabit the call, not the `TFacts` field, and that
`AbstractFrame` takes `TFacts` as a whole
(`TwelveAgree.lagda.md:337-343`).

## Q2. DOES EVERY LOAD-BEARING CLAIM RESOLVE TODAY? YES

I opened every cited site. All resolve, and all say what the
report says they say:

- `src/L/Condensation.lagda.md:2782-2786`: the `codesK` telescope,
  with the truncation as third component at `:2785`.
- `src/L/Condensation.lagda.md:2806`: the consuming site spends
  the third component as `arNum`.
- `src/L/Condensation.lagda.md:2801-2806`: `BotAgree.bot-in`.
  Its telescope at `:2777-2789` takes no `someEnv`.
- `src/L/Condensation.lagda.md:3505-3515`: `PropAgree.back`.
  `c∈` is bound in the lambda at `:3505`, `shEq` is derived at
  `:3506-3508`, `arNum` is extracted at `:3509`, and `someEnv` is
  called at `:3515` without it.
- `src/L/Condensation.lagda.md:3317`, `:3569`, `:3624`: the three
  ungated `someEnv` parameters. `:7380`: the one `module KValue`.
  `:6971-6976`: the unsupplied `twelve-out` and `twelve-back`
  parameters.
- `src/L/Coding/EnvSupply.lagda.md:417-424`: the supplier, with
  `arNum` at `:418`.
- `src/L/Condensation/LowerAgree.lagda.md:52-58`, `:116`,
  `:218`, `:255`: the ungated field type, `LFacts.codesK` with C
  at `suc (suc zero)`, `LFacts.someEnv`, and the `MemAgree`
  instantiation.
- `src/L/Condensation/TwelveAgree.lagda.md:186-187`, `:289`,
  `:337-343`, `:494`, `:527-537`: `envK-mem` takes the truncation,
  `TFacts.someEnv` does not, `AbstractFrame` takes `TFacts` whole,
  C is `suc (suc zero)`, and the two bridge lemmas.
- `agents/tasks/LJ-1-473/Probe473.agda:61-67`: the pad, identical
  to `Probe483.agda:70-84`.
- `agents/tasks/LJ-1-480/lj-1.480-report.md:66`,
  `agents/tasks/LJ-1-473/lj-1.473-report.md:112`,
  `agents/tasks/LJ-1-457/lj-1.457-report.md:87`,
  `agents/tasks/LJ-1-463/review-of-someEnv-at-K.md:109-118`,
  `agents/tasks/LJ-1-113/lj-1.113-report.md:135-147`,
  `dev/LESSONS.md:3752`, `dev/pod/audit-2026-08-20.md:34`,
  `dev/pod/direction.md:37`: all resolve with the content claimed.

The report's own numbers reproduce from the run records. W3
rechecks: 2.28, 2.37, 2.32 s, median 2.32 s; peak RSS 605044736,
573358080, 595394560 bytes, median 595394560. First landing 3.01 s
and 569393152 bytes. Full-file rechecks: 2.17, 2.48, 2.60 s,
median 2.48 s; median RSS 605028352 bytes; first landing 2.16 s
and 605044736 bytes. All eight `.time` files match the report
line for line.

The probe's line counts are exact. I counted 61 non-blank
non-comment lines in `Probe483.agda`; the `W3` module holds 39 of
them; `no-code` is 7; `arNum-from-codesK` is 6.

One claim is derivable and not run-backed: "The type
`someEnvDef {9} iK' Kenv'` forms". The green file defines
`iK' : Fin (5 + 9)` and `Kenv' : Vec S (11 + 9)`, and
`someEnvDef` at `LowerAgree.lagda.md:52` consumes exactly those
two shapes, so the application is well formed by construction.
This claim does not carry the STOP. The STOP rests on the missing
body. No defect.

## Q3. IS THE ENUMERATION COMPLETE? YES

I redid every count in section 6 of the report with my own
searches, on this tree today:

- `someEnvDef` in `src/`: 5 occurrences,
  `LowerAgree.lagda.md:52`, `:53`, `:218`,
  `TwelveAgree.lagda.md:33`, `:289`. Typed sites: `:52`, `:218`,
  `:289`. In `archive/src/`: 0. Matches 5 raw, 3 typed.
- `SupplyEnv.someEnv`: 1, `EnvSupply.lagda.md:417`, with the
  truncation at `:418`. Matches.
- Ungated `someEnv` parameters: 3, `Condensation.lagda.md:3317`,
  `:3569`, `:3624`. The one call that discards `arNum` is at
  `:3515`. Matches.
- `module KValue`: 1, `Condensation.lagda.md:7380`. Matches.
- The truncation string: 87 in `src/`; 50 in
  `Condensation.lagda.md`, 10 in `EnvSupply.lagda.md`, 8 in
  `LowerAgree.lagda.md`, 8 in `UpperAgree.lagda.md`, 11 in
  `TwelveAgree.lagda.md`; 0 in `archive/src/`. Matches, including
  the split.
- `codesK c ar` applications: 21, all in `Condensation.lagda.md`,
  none inside `someEnvDef`. Matches.

I also checked the report's strongest sweep claim: that all 87
truncation occurrences are hypotheses or `codesK` conjuncts, and
never a consequence of membership in `K`. Every one of the 87
lines puts the truncation after a hypothesis arrow or inside a
`×`-conjunct of a `codesK`-shaped telescope. None is a conclusion
of a lemma whose hypotheses are memberships alone. The claim
holds.

No cure is missed. The report names five routes for the next
brief: the gated type, with `[LJ-1.463]`'s form at
`review-of-someEnv-at-K.md:109-118`; a local at
`PropAgree.back:3515`, with the `TFacts`-split caveat; a code
class in pad slot 2, at a new frame and re-measured; the closure
lemmas, unfunded; and the `TFacts` record once the other fields
have suppliers. I looked for a sixth route and found none that
the tree admits:

- A vacuous field. The three hypotheses of `someEnvDef` are
  satisfiable at this pad: the K row is
  `lookup (suc (suc (suc (suc (suc (suc iK')))))) Kenv'`, which is
  `Kenv` slot 1, the bound `LsetS lam ordλ`, at
  `Condensation.lagda.md:7390` and `:7397` (`iK = suc zero`), and
  `[LJ-1.480]` itself put a witness in that slot. No contradiction
  is available, so no vacuity proof exists.
- `arNum` from the three memberships. Refuted by `[LJ-1.480]`:
  a Kuratowski pair of two copies of `numeralL 0` is in the slot
  and is not a numeral.
- Classical logic. The truncation is a positive existence
  statement. `LEM`, which the probe already carries, does not
  produce a numeral witness from a membership.
- A different `n` or `K`. The truncation is missing from the
  telescope at every `n`. Changing `n` moves nothing.

## THE BRIEF'S PART IN THE OUTCOME

The brief fixed the frame: "Build the frame with the carrier in
slot 0, as `[LJ-1.473]` measured". That pad carries
`numeralL 0` in slot 2, so the C-membership premise of `codesK`
was refutable before any Agda ran, and the STOP was certain at
that frame. But the same brief ordered this exact outcome: "If
those inputs have no source at this frame, name them and STOP",
and priced it as a full return. The brief did not foreclose the
answer. It sanctioned the finding.

One clause of the brief is false, and the return did not copy the
error. The brief's W3 escape says that if the two inputs have no
source at this frame, "the field is not inhabitable at the
consumer either and both readings fail". The tree refutes the
first half: the consumer, `PropAgree.back`, binds `c∈` at
`Condensation.lagda.md:3505` and derives `shEq` at `:3506-3508`.
Both inputs have a source at the consumer. What fails at the
consumer is the field, because `TFacts.someEnv` at
`TwelveAgree.lagda.md:289` is the ungated `someEnvDef`, and a
local at `:3515` is not a record field. The return's site table
says exactly this. The next brief must not inherit the brief's
"both readings fail" clause: Reading 2 fails at the field, and
the gate or the split is the live route.

## VERDICT

**UPHELD.** The STOP is correct on its own numbers, every
load-bearing citation resolves today, and the enumeration is
complete. The obligation `Probe483.agda::someEnv-at-codesK`
stays open. Per the standing instruction, this file plus exit 0
closes the task under row `sys-critic-upheld-no-go`. I write no
table row.

## ARCHIVE USED

- `dev/ARCHIVE.md`: not used. This review retires no module and
  writes no registry row. The sweep under review counted
  `archive/src/` at 0 and needed no registry.
- `archive/dev/JOURNAL.md`: not read. The retired journal carries
  no rule that bears on whether `codesK` applies at a pad whose
  slot 2 is `numeralL 0`.
- `archive/dev/ORCHESTRATION.md`: not read. The orchestration
  history does not change a type-level source check at
  `file:line`.
- `archive/dev/DD-archived.md`: not read. The live rulings are in
  `dev/pod/rulings.toml`. The return under review cites no
  archived DD row.
- `archive/dev/PLAN-archived.md`: not read. The retired plan does
  not bear on the domain of `codesK` at this frame.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: not used. The question under
  review is a source check inside this tree. No Devlin text can
  change what `lookup C Kenv'` is at this pad, and the verdict
  rests on that alone.
- `dev/literature/BIBLIOGRAPHY.md`: not used. No source was
  checked against the bibliography in this review.
- `dev/literature/digest.md`: not used. The digest pins the rud
  route. This review checks no rud argument.
- `dev/literature/geology.md`: not used. No strata question is
  at issue in this review.
- `dev/literature/devlin-errata.md`: not used. No Devlin text
  was used, so no erratum can change this review.

Clause W8 did not bind: this review wrote no Agda and decided no
provability question against the literature.

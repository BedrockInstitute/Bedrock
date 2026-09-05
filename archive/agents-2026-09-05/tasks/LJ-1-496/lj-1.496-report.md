# LJ-1.496 report: Repair B at the real chain

slot: `coder`. Written early as a skeleton and filled as the check lands
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-496/`.
I ran no Agda process, because the brief's D-10 clause stops the landing
before any Agda and the stop condition is met, section 1. `GHCRTS` was
set on the pane by the program, `-A64m -I0 -M8g`, the wide caliber. I
never set it. No heap event, because no run. `.venv/bin/python` is
absent in this worktree, the fact [LJ-1.493] recorded, so `make check`
as one target cannot run here; the individual gates ran on system
`python3.11` and are green, section 8.

**VERDICT: NO-GO.** D-10 fires before any Agda. `lam`, `gam`, and the
gate `⟨ ω ∈ sucV gam ⟩` cannot reach `PropAgree` from where it is
instantiated. The brief pre-rules the case: "If `LowerAgree:269` cannot
supply them, STOP AND SAY SO: that would mean Repair B is not landable
at this chain." I stop and say so. Repair B is not claimed. `src/` is
unchanged at `87fbae4`.

## TARGET

One new term `someEnvK` in `src/L/Condensation.lagda.md`, the
environment `SupplyEnv` supplies at `PropAgree`'s frame, used at the
`:3515` call, with the `someEnv` parameter and its passing sites
retired in the same commit. The predecessor `[LJ-1.493]` is GO, verdict
at `agents/tasks/LJ-1-493/lj-1.493-report.md:70-72`, and its term
typechecks at the probe frame,
`agents/tasks/LJ-1-493/Probe493.agda:139-184`. I took the verdict from
the report and the construction from the probe, the binding of premise
14 and of audit F1 at `dev/pod/audit-2026-08-20.md:34`. The
construction is sound at the probe frame. This task measured the
chain, and the chain is the obstruction.

## 1. D-10, BEFORE ANY AGDA

The brief's clause: open the real frame and say at `file:line` whether
`lam`, `gam`, and the gate can reach `PropAgree` from where it is
instantiated. The instantiation chain is five frames. I open each.

1. `PropAgree` is instantiated at `src/L/Condensation.lagda.md:3575`
   (by `AndAgree`) and `:3630` (by `OrAgree`), with the positional
   arguments forwarded at `:3576` and `:3631`. `AndAgree` and `OrAgree`
   are generic in their frame: `src/L/Condensation.lagda.md:3537` and
   `:3592`, both `{m : ℕ} (C T B N K : Fin m) (γ : S ^ m)`.

2. `AndAgree` and `OrAgree` are instantiated only at
   `src/L/Condensation/LowerAgree.lagda.md:269` (`module A`) and `:275`
   (`module O`), inside `module LowerAgree`, whose frame is `:226-229`:
   `{n : ℕ} (N0 ... K : Fin (5 + n)) (γ : S ^ (11 + n))`
   `(lf : LFacts ...)`.

3. The scope at `:269` is the frame, `open LFacts lf` at `:232`, and
   the module's imports at `:21-36`. Census:
   - The frame binds `Fin` indices and one vector. It binds no `V ℓ`
     stage, no `IsOrd`, no gate.
   - `LFacts` is the record at `:95`, 37 fields through `:224`. Every
     field is a proposition about the given `γ`. No field binds a
     stage or the gate `⟨ ω ∈ sucV gam ⟩`.
   - The imports take `module AndAgree` and `module OrAgree` from
     `L.Condensation` at `:33-36`. They take no `KValue` and no
     `EnvSupply`.
   - The only `lam : V ℓ` and `gam : V ℓ` binders in the three
     chapters are the parameters of `module KValue` at
     `src/L/Condensation.lagda.md:7380-7383`. `KValue` receives the
     carrier as a parameter. It does not supply it.

4. The upstream frame is equally generic. `LowerAgree` is instantiated
   only at `src/L/Condensation/TwelveAgree.lagda.md:496` and `:503`,
   inside `module AbstractFrame`, whose frame is `:337-342`:
   `{n : ℕ} (N0 ... K : Fin (5 + n)) (γ' : S ^ (11 + n)) (sucK ...)`
   `(tf : TFacts ...)`. It binds no stage and no gate. `AbstractFrame`
   has no application anywhere in `src/`: the census over `src/`
   returns the comment at `TwelveAgree.lagda.md:70` and nothing else,
   and the only import of the chapter is the bare module import at
   `src/Everything.lagda.md:393`.

**ANSWER AT `file:line`:** `lam`, `gam`, and the gate do not reach
`PropAgree` from `LowerAgree:269` or `:275`. Nothing in scope at
`:269` can serve as the three new arguments, and no frame above
`:269` supplies them either. The brief's stop condition is met. The
task stops here. The stopping is stated in
`agents/tasks/LJ-1-496/review-of-someEnvK.md`.

## 2. W3: the chain, and why the experiment is not run

The W3 named term is the `PropAgree` telescope of the new arguments
reaching its two callers at `LowerAgree:269` and `:275`.

The experiment the brief names, telescope added, old parameter kept,
two chapters typechecked, is not run. The brief's own ordering rules
it: D-10 is "BEFORE ANY AGDA", and its stop condition is met on the
current tree, section 1. The W3 paragraph says that when the arguments
cannot reach, "the landing stops at its cheapest point and the old
code is still whole". The cheapest point is before any edit. The tree
is still whole: `git status` carries only `agents/tasks/LJ-1-496/`,
untracked, and nothing in `src/` moved. No median wall time and no
peak RSS are reported for W3, because no W3 run exists. I do not fund
a number the brief guessed or [LJ-1.493] measured at another site.

The experiment would not have decided the verdict. Two walls stand,
and each alone is a NO-GO.

**WALL 1, REACHABILITY.** This is the D-10 census of section 1. The
experiment makes the arguments reach only by adding them to the
`LowerAgree` telescope at `LowerAgree.lagda.md:226-229` and, above
it, to the `AbstractFrame` telescope at
`TwelveAgree.lagda.md:337-342`. Neither frame is in the brief's five
groups, and the brief's rule binds the widening: "If a deletion breaks
a consumer this brief did not name, that consumer is the finding: name
it at `file:line` and STOP rather than widening the edit." The
threaded carrier would end at `AbstractFrame`, which no consumer in
`src/` instantiates, so it would meet no real `K` and close no call
site. The 493 report states the same open end at
`agents/tasks/LJ-1-493/lj-1.493-report.md:270-272`: `twelve-out` and
`twelve-back` "still need a `TFacts` value at a real `K`".

**WALL 2, GENERICITY.** This wall is independent of Wall 1. It makes
the landing false even with the carrier threaded. The probe's body
closes the concrete bound `Lset lam` in three places:

- `SE.someEnv` at `src/L/Coding/EnvSupply.lagda.md:417-424` takes
  `yaK : ⟨ fst ya ∈ Lset lam ⟩` at `:419` and returns
  `⟨ fst E ∈ Lset lam ⟩` at `:422`.
- `SE.transK` at `:272-274` closes `⟨ fst x ∈ Lset lam ⟩` at `:273`.
- `SE.envInK-gen` at `:351-356` closes `⟨ fst z ∈ Lset lam ⟩` at
  `:356`.

The `someEnv` parameter of `PropAgree` closes the generic slot
instead: `⟨ fst ya ∈ fst (lookup K γ) ⟩` at
`src/L/Condensation.lagda.md:3317-3320`, and the call site at `:3515`
feeds those generic memberships in and spends the result at the generic
environment, `hbody` at `:3527`. In the generic frame `{m : ℕ} (C T B
N K : Fin m) (γ : S ^ m)` at `:3285`, `fst (lookup K γ)` is an
arbitrary `S`, and no path from it to `Lset lam` is in scope. The
probe typechecks at median 4.53 s only because its frame is
`KValue`'s `Kenv`, whose slot 1 is definitionally `LsetS lam ordλ`
(`src/L/Condensation.lagda.md:7390`), and `LsetS β oβ = Lset β ,
isL-Lset β oβ` (`src/L/Axioms/Basic.lagda.md:161`). A measured cure does not
transfer by analogy. Re-measured at its own site, the construction is
not generic, and `someEnvK` cannot be written at `PropAgree`'s frame
with the old parameter's type.

## 3. WHAT THE PREDECESSOR DELIVERED, AND WHAT THIS TASK MEASURES

`[LJ-1.493]` measured the construction at a REBUILT frame. The probe
rebuilds `:3509` at `KValue`'s `Kenv` with the length fixed: `module
At (C T : Fin 14)` at `agents/tasks/LJ-1-493/Probe493.agda:114`, and
the environment is the fixed vector `Kenv` at
`src/L/Condensation.lagda.md:7389-7390`. The probe never measured the
chain: `AndAgree` and `OrAgree` at the `LowerAgree` frame, and
`PropAgree` with `m` generic and `γ` arbitrary. This task measured
the chain. The construction is GO at one fixed carrier, and the chain
is generic in its carrier. The two facts together are the NO-GO.

## THE FIVE GROUPS, LANDED.

**NONE landed.** The landing stopped at D-10, before any edit.
Repair B is not claimed.

| group | site | final state | line delta |
|---|---|---|---|
| 1 | `src/L/Condensation.lagda.md:3515` | unchanged; the `back` proof still calls the `someEnv` parameter at `:3515` | 0 |
| 2 | `src/L/Condensation.lagda.md:3285-3320` | unchanged; `PropAgree` takes no `KValue` telescope and opens no `SupplyEnv` | 0 |
| 3 | `src/L/Condensation.lagda.md:3317`, `:3569`, `:3624` | unchanged; the three `someEnv` parameters stand | 0 |
| 4 | `src/L/Condensation/LowerAgree.lagda.md:52-58`, `:218`, `:273`, `:279` | unchanged; `someEnvDef`, `LFacts.someEnv`, and the two pass-throughs at the `A` and `O` instantiations stand | 0 |
| 5 | `src/L/Condensation/TwelveAgree.lagda.md:289`, `:442` | unchanged; `TFacts.someEnv` and its record fill stand | 0 |

Reason per group: the term they would retire cannot be written at
their frame. Wall 1: the carrier does not reach the frame. Wall 2:
the construction does not typecheck in the frame. Group 2 is the
gate: `PropAgree` cannot open `SupplyEnv` without the carrier values
in its telescope, and the term it would define cannot close the
generic slot. Groups 1 and 3 follow group 2. Groups 4 and 5 follow
the retirement of the field, which did not happen.

## WHAT TFACTS OWES NOW.

Measured: `TFacts` has **59** fields. The record stands at
`src/L/Condensation/TwelveAgree.lagda.md:129`, its body runs to
`:335`, and the 59 field declarations were counted from the record
body. `someEnv` is **not** gone. It stands at `:289`, is filled at
`:442` in `AbstractFrame`'s `lf` record, and is read through
`LFacts.someEnv` at `src/L/Condensation/LowerAgree.lagda.md:218`,
passed at `:273` and `:279`, and consumed at
`src/L/Condensation.lagda.md:3317`. The next pass owes the record its
59 fields. I do not price the remaining fields.

## 6. W2

W2 (from DD4): write the mathematics once at a generic carrier and
instantiate it, so both proofs share the maximum code. The rule is
stated in the brief's obligation, and answered here.

The mathematics of this repair is written once, at the concrete
carrier `B₀ = LsetS gam ordγ` of `SupplyEnv`
(`src/L/Coding/EnvSupply.lagda.md:124-125`), in the one `someEnv` at
`:417-444`. The landing would have instantiated it at `PropAgree`'s
frame. The NO-GO is not a W2 failure: nothing is duplicated, and
`someEnvDef` at `LowerAgree.lagda.md:52-58` is already the generic
form the rows share. The obstacle is that the instantiation point is
generic in its carrier while the construction is concrete in its
carrier, and no rule of W2 licenses closing that gap at `PropAgree`
without the carrier's values in scope. No deadline forced a fixed
form, and nothing was weakened.

## 7. W4

W4 does not fire. No module is retired. Nothing moves to `archive/`.
Nothing is deleted. The dead-fragment clause does not reach, because
nothing died: the field stands, section 5.

## 8. THE GATES

`make check` as one target cannot run in this worktree. `venv-check`
requires `.venv/bin/python`, which is absent, the fact
[LJ-1.493] recorded. The individual gates of the precommit set and the
spec surface ran on system `python3.11`, one process each,
sequential:

| gate | result |
|---|---|
| `scripts/gate/lint-agda.py --check` | exit 0 |
| `scripts/gate/lint-prose.py --check` | exit 0 |
| `scripts/gate/check-glossary.py --check` | exit 0 |
| `scripts/gate/check-fences.py --check` | exit 0, "clean (102 masters, run threshold 3)" |
| `scripts/gate/check-probes.py --check` | exit 0, "clean (4959 tracked files)" |
| `scripts/site/weave-i18n.py --check` | exit 0 |
| `scripts/pod/check-spec-surface.py --check` | exit 0, "clean (8 surface file(s), 201 declaration(s))" |
| `scripts/pod/check-survey-quotes.py LJ-1.496` | exit 0, "clean (0 note(s), 0 defect(s))" |

The standing size, the one admissible figure: `scripts/measure/
ledger.py --brief` reports 33,523 lines over 100 masters, measured
from HEAD. `src/` is unchanged at `87fbae4`, so the standing is the
campaign's standing.

## 9. THE SURVEY GATE, AFTER THE REPORT

`scripts/pod/check-survey-quotes.py LJ-1.496` was re-run after this
report landed, and its exit 0 is recorded in section 8's table:
clean, 0 notes, 0 defects. The quotes in `## ARCHIVE USED` and
`## LITERATURE USED` sit at the cited lines, and every injected
candidate path is answered below.

## 10. PREMISES

Premises 1 to 14 all hold as stated. Premise 1: the GO verdict at
`agents/tasks/LJ-1-493/lj-1.493-report.md:70`. Premise 2:
`Probe493.agda:169` calls `SE.someEnv`. Premise 3: `c∈` is the binder
at `src/L/Condensation.lagda.md:3505`, and `C` is a parameter of the
frame at `:3285`. Premises 4-6: the five groups and the `:3515` call
are at the named lines, section 5. Premise 7: `PropAgree` at `:3285`.
Premises 8-9: the `PropAgree` calls at `:3575` and `:3630`. Premise
10: the `LowerAgree` instantiations at `:269` and `:275`, and the
`AbstractFrame` census of section 1 names no other. Premise 11: the
gate is declared at `src/L/Coding/EnvSupply.lagda.md:111`. Premise
12: `TFacts.someEnv` at `TwelveAgree.lagda.md:289`. Premise 13:
`make check` is the gate; section 8 states what ran and what could
not. Premise 14: the predecessor is taken as the report plus its
probe, per audit F1 at `dev/pod/audit-2026-08-20.md:34`.

Premises 1 to 3 are measurements of the CONSTRUCTION. The
construction is not the chain. This task measured the chain, and the
brief's D-10 clause binds the reading: the stop condition is met.

## 11. WHAT THE NEXT BRIEF NEEDS

The choice between Repair A and Repair B re-opens. The brief's own
words: the mathematician "must re-open the choice against Repair A".
Facts the next brief can take, each at `file:line`:

- The carrier reaches no frame of the chain. Sections 1 and 2, wall 1.
- Repair A of [LJ-1.488] states the same missing source for its gate:
  "`ω∈γ` still has no source at `someEnvDef`, at `KValue`, or at
  `PropAgree`"
  (`agents/tasks/LJ-1-488/lj-1.488-report.md:346-348`). Repair A puts
  the gate in the field's type, at 7 site groups against Repair B's 5
  (`agents/tasks/LJ-1-488/lj-1.488-report.md:336`). Its gate still
  needs a source at `PropAgree`, and the frame of `someEnvDef` is
  generic in its carrier the same way `PropAgree` is.
- If the next brief wants the field retired, the brief must name the
  frame at which the carrier becomes a value. Either the chain is
  specialized to `KValue`, which is a new design decision and not
  Repair B as stated, or the carrier is threaded through `LowerAgree`
  and `AbstractFrame` and wall 2 is answered with a named mechanism.
  Neither is a landing this brief authorized. The choice is the
  mathematician's.

## C-42

This return is a NO-GO at the chain, not a measurement of the
construction. It says: the carrier values of `SupplyEnv` (`lam`,
`gam`, `⟨ ω ∈ sucV gam ⟩`) have no source at any frame between the
`:3515` call and any value that supplies them, and the construction
itself closes the concrete bound in a frame that is generic in its
carrier. It does not say: `someEnvK` is false, Repair A is false, the
field is unretirable, or either trophy moves.

COUNT of `someEnvK` in `src/`: **0**. In `archive/src/`: **0**.

COUNT of `module KValue` in `src/`: **1**,
`src/L/Condensation.lagda.md:7380`. In `archive/src/`: **0**.

COUNT of the `someEnv` parameter in `src/`: **3**,
`src/L/Condensation.lagda.md:3317`, `:3569`, `:3624`. In
`archive/src/`: **0**.

COUNT of `someEnvDef` in `src/`: **5** raw, **3** typed, the same
census [LJ-1.493] gave. In `archive/src/`: **0**.

## STATE OF THE TREE

- `src/` is unchanged at HEAD `87fbae4`.
- Untracked: `agents/tasks/LJ-1-496/lj-1.496-report.md` and
  `agents/tasks/LJ-1-496/review-of-someEnvK.md`. Nothing else.
- No commit, no push. The program commits by explicit path.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX, archived 2026-08-18". Declined. The live producer is `dev/pod/queue.toml`, and the stop of this task reads the live chain in `src/`, not the archived dispatch rows.
- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined. The per-episode journal is retired, and the product of this task lives in this directory.
- `archive/dev/JOURNAL-archived.md:1`, read: "# Archived journal: the retired route". Declined. The retired route does not bear on whether `lam`, `gam`, and the gate reach `PropAgree` from `LowerAgree:269`.
- `archive/dev/PLAN-archived.md:1`, read: "# ARCHIVED 2026-08-20". Declined. The live plan is the campaign's, and this task does not consult the archived plan.
- `archive/dev/DECISIONS-archived.md:1`, read: "# Archived decisions: the D series". Declined. The live rulings are `dev/pod/rulings.toml`, and D-10 of this task is the brief's own clause, not an archived D row.
- `dev/ARCHIVE.md:1`, read: "# ARCHIVE.md: the archive registry". Declined. This task retires no module, so the registry is not consulted.

## LITERATURE USED

- `dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the Condensation Lemma and the GCH in L". Declined. Devlin II.5 does not decide whether a carrier value reaches a generic frame.
- `dev/literature/truncation-and-selection.md:1`, read: "# Truncation and selection: how the two literatures pick a witness". Declined. The truncation of `codesK`'s fourth component is already bound at `src/L/Condensation.lagda.md:3509`. The work is a source census, not a witness selection.
- `dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the rud route, pinned from the collected literature". Declined. The rud route is retired, and this term does not walk it.
- `dev/literature/terms-2026-08.md:1`, read: "# The terminology dossier: fourteen renderings for the owner's ruling". Declined. No glossary term is at issue.
- `dev/literature/geology.md:1`, read: "# Geology dossier: set-theoretic geology sources and the five questions". Declined. Geology does not reach the `LowerAgree` frame.

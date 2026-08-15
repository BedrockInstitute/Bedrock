# LJ-1.273 Report

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. No Agda ran. No
slot held. No master, brief or report edited except this one. Written
incrementally (C-22). Every negative is MEASURED or INFERRED, in those
words.

## 0. ONE-SENTENCE ANSWER

A7 is only the statement, not the GCH endpoint.

## 1. WHAT `gch_root` MUST NAME

`ac_root` names `src/L/Model.lagda.md`. Its endpoint is `L⊨ZFC` at
`src/L/Model.lagda.md:98-99`. That endpoint is a proof term. It has type
`isZFCModel`. It is not a type. The `ac_root` comment in `dev/ledger.toml` is
correct.

`gch_root` must name `src/L/GCH.lagda.md`. The theorem in it must be a proof
term. I call it `L⊨GCH`. Its type must be `GCHStatement L⊨ZF`.

A7's probe defines `GCHStatement` at
`agents/tasks/LJ-1-236/ProbeLJ1236A7.agda:147`. That is a `Type (ℓ-suc ℓ)`.
Its guard at `:165-171` builds one inhabited site `aω`. It does not supply the
two hypotheses `sq` and `absorbs`. `exit 0` is not a supply (C-45).

`src/L/GCH.lagda.md` is the A7 home named by `[LJ-1.268]` at
`agents/tasks/LJ-1-268/lj-1.268-report.md:33-34`. The same report says the
file will hold the proof later at `:170-171`. So the path is right. Only the
theorem is missing.

## 2. THE CHAIN

The chain has three parts. Part 1 is Route A-prime. Part 2 is the `[LJ-1.7]`
residue. Part 3 is the final assembly.

### 2.1 Route A-prime

The seven-block price is 1,089 lines at
`agents/tasks/LJ-1-253/lj-1.253-report.md:12-21`. The landing order is at
`agents/tasks/LJ-1-268/lj-1.268-report.md:23-38`.

| link | status | evidence | what it still owes |
|---|---|---|---|
| A2 coding injection | BUILT, not SUPPLIED | `lj-1.268-report.md:23-24` | land `src/L/Coding/Injection.lagda.md`, 186 lines |
| A1 least-cardinal restatement | BUILT, not SUPPLIED | `lj-1.268-report.md:25` | land `src/L/Cardinal.lagda.md`, 54 lines |
| A3 internal least selection | BUILT, not SUPPLIED | `lj-1.268-report.md:29-30` | land into `src/L/Cardinal.lagda.md`, 26 lines |
| A4 internal cardinal | BUILT, not SUPPLIED | `lj-1.268-report.md:30`; `lj-1.253-report.md:21` | land into `src/L/Cardinal.lagda.md`, 43 probe lines |
| A5 square-law chain | MIXED: rows 5 and 1 BUILT, row 3 OPEN | `lj-1.268-report.md:23-38` | land `src/L/InjChain.lagda.md`; row 3 needs a re-sited probe |
| A6 absorption | BUILT, not SUPPLIED, stale import | `lj-1.268-report.md:37-38`; `ProbeLJ1217A.agda:239` | re-site onto landed A2; land `src/L/Absorption.lagda.md`, 399 lines |
| A7 GCH statement | BUILT, not SUPPLIED, statement only | `ProbeLJ1236A7.agda:147` | land `src/L/GCH.lagda.md`, 33 lines |

Every A-prime link is a probe, not a delivered master. The statuses follow
C-38 as extended. A green probe is not a supply.

### 2.2 The `[LJ-1.7]` residue

`[LJ-1.267]` re-derived the seven parameters of `module Whole` at
`agents/tasks/LJ-1-178/ProbeLJ1178A.agda:489-493`. I checked that report and
kept its statuses.

| link | status | evidence | what it still owes |
|---|---|---|---|
| `el` | SUPPLIED | `src/L/BoundedSubset.lagda.md:759-760` | nothing |
| `fwd`, `bwd` | SUPPLIED | `src/L/BoundedSubset.lagda.md:195-318`, `:780` | nothing |
| `sl`, `sc` | BUILT, not SUPPLIED | `ProbeLJ1237A.agda:178-181`, `:191-201`, `:205-246` | a supplied `lh` and `succα` |
| `s₁` | BUILT in shape, not SUPPLIED | `src/L/BoundedSubset.lagda.md:145-146` | the missing `Σ₁ φ₀` |
| `amb` | OPEN | `ProbeLJ1184B.agda:112`; `ProbeLJ1184C.agda:83` | a real discharge of `q` |
| `lh` supply, step 6 | OPEN, partly built | `dev/PLAN.md:47`, `:56`; `src/L/Condensation/TwelveAgree.lagda.md:337-342` | the remaining 28-field supply |

The seven parameters build `levelIn` and `cover` at
`agents/tasks/LJ-1-178/ProbeLJ1178A.agda:500-505`. The delivered theorem still
takes those two as hypotheses at `src/L/BoundedSubset.lagda.md:1621`. Until the
seven parameters are supplied, the theorem is not an endpoint.

### 2.3 The final assembly

The final assembly is OPEN. No probe or master writes a term of type
`GCHStatement L⊨ZF`. A7 writes only the type.

The archived route priced this block at 150 to 350 survey lines at
`agents/tasks/archive/LJ-1-1/lj-1.1-recon.md:165-171`. The current route has
not re-priced it.

## 3. THE ARCHIVE'S 399-LINE `CardinalPredicates`

The retired route's `CardinalPredicates` is beside this chain. It is not a
link. Its `cardFo` is the bijection form. Current `IsCardinalL` is the
injection form. That difference is measured at
`agents/tasks/LJ-1-236/lj-1.236-report.md:240-245`. The archive gives the
one-master shape only. The code does not transfer.

## 4. THE PRICE AND ITS BASIS

One best-effort number: **about 1,760 lines**. The band is **1,660 to 1,960
lines**.

The band has three parts.

| part | figure | basis |
|---|---:|---|
| Route A-prime landing | 1,089 lines | probe, measured by `[LJ-1.253]` |
| `[LJ-1.7]` residue | 450 to 550 lines | comparable plus survey, with a measured +50 overrun |
| final `L⊨GCH` assembly | 120 to 320 lines | survey, less A7's measured 33 lines |

The point 1,760 is 1,089 plus 450 plus 220.

The `[LJ-1.7]` figure starts at about 400 from `dev/PLAN.md:47`. Step 6 moved
from 255 to about 305 at `dev/PLAN.md:56`. So the 400 moves to about 450. The
tail is unpriced. It holds 14 site facts, `SF`, and the `ω ∈ σ` term. That
tail makes the band. Mark this part INFERRED.

The final assembly is a survey from `lj-1.1-recon.md:171`. I subtract A7's 33
lines because A7 is now a separate block. The subtraction is INFERRED.

## 5. DD4 ON THE AC-AGAINST-GCH AXIS

DD4's own axis is the AC closure against the GCH closure. The code fixes that
axis at `scripts/ledger.py:50` and `:404-407`. `dev/ledger.toml:169-178`
declares the two roots.

Most of the priced chain is GCH-only on that axis. The five new A-prime
masters are not imported by `ac_root`. The AC root imports only the modules at
`src/L/Model.lagda.md:49-57`. It does not import the new masters. The
`[LJ-1.7]` edits touch masters that are also not imported by the AC root. The
landing order says no existing master is extended at
`agents/tasks/LJ-1-268/lj-1.268-report.md:45-48`.

So the new lines will raise the GCH closure. They will not raise the shared
intersection. The shared intersection on declaration day will be the AC
closure that the GCH root imports. This judgement is INFERRED. I did not
compute the closures.

This is DD4's own axis. It is not Def-against-J and not L-against-ambient.
A7 is tower-neutral on the Def-against-J axis at
`ProbeLJ1236A7.agda:147` and `:103-106`. That fact does not make A7 shared on
the AC-against-GCH axis.

## 6. ARCHIVE USED

One line read named per archived file.

- `agents/tasks/LJ-1-272/lj-1.272-report.md:259`, the two-tower route makes
  per-tower content a DD4 cost on the two-tower axis.
- `agents/tasks/LJ-1-267/lj-1.267-report.md:13-19`, the seven parameter
  statuses.
- `agents/tasks/LJ-1-268/lj-1.268-report.md:23-38`, the A-prime landing
  order.
- `agents/tasks/LJ-1-253/lj-1.253-report.md:12-21`, the 1,089 price.
- `agents/tasks/LJ-1-236/lj-1.236-report.md:240-245`, the archive bijection
  form against the current injection form.
- `archive/dev/TASKS-archived.md:72`, `L3.32-T37` built cardinal predicates
  generally.
- `archive/dev/STATUS-archived.md:116`, the GCH endpoint is the active
  campaign, not a successor plan.
- `archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md:34`, the
  module header. Shape only.
- `agents/tasks/archive/LJ-1-1/lj-1.1-recon.md:171`, the final assembly survey
  band 150 to 350 lines.

## 7. LITERATURE USED

`dev/literature/devlin-II5.md:370-384`, read whole. The endpoint chain needs
these rows:

| row | what the chain needs | status |
|---|---|---|
| B | collapse | SUPPLIED by `fwd` and `bwd` |
| C1 | level-hood certificate | OPEN in the `[LJ-1.7]` residue |
| C4 | transfer along the collapse | SUPPLIED by `el` |
| D | definable well-order | delivered by the `L.Choice` and `L.WellOrder` stack |
| E | counting | delivered comparable in `L.Ordinal.SquareLaw` and `L.StageCardinal` |
| F | condensation and `|L_α| = |α|` | partly in `[LJ-1.7]`, partly in A5 and A6 |
| G | uniform well-order | delivered by the same well-order stack |

No needed row has no delivered counterpart. The one object with no delivered
counterpart is the final `L⊨GCH` proof term. That object is not a Devlin row.
This mapping is INFERRED. The C1 open status is MEASURED at
`agents/tasks/LJ-1-267/lj-1.267-report.md:16-19`.

`dev/literature/devlin-II5.md:145-171` states GCH as level containment. A7
uses the injection form. That difference is the tree's own, recorded at
`agents/tasks/LJ-1-236/lj-1.236-report.md:251-258`.

`dev/literature/devlin-II5.md:246-255` says the bound may have any shape. The
numeral restriction is this machine's way to meet that requirement.

## 8. WORKING TREE

One file written: `agents/tasks/LJ-1-273/lj-1.273-report.md`. No master, brief
or report edited. No `dev/ledger.toml` edit. No Agda ran. No commit, no push,
no reset, stash or clean.

`scripts/lint-prose.py --check` exits 0.

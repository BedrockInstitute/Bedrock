# LJ-1.279 report: land A5 rows 5 and 1 as `src/L/InjChain.lagda.md`

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. One Agda slot held.
A new master written. No commit, no push. Written incrementally (C-22). Every
negative is MEASURED or INFERRED, in those words. ASD-STE100 applies.

## 0. LEAD

**343 in-fence non-blank lines, 3.05 s cold (mean of 3), rate 0.0089 s/line,
which is 0.85x the 0.010514 bar.** Both rows land green, exit 0, `--safe`.
The re-run that imports the master is green, exit 0. This is a landing, not a
copy (C-45).

| figure | value |
|---|---:|
| in-fence non-blank lines (ledger caliber, live) | 343 |
| cold elapsed (mean of 3, final file) | 3.05 s |
| cold range | 3.02-3.10 s |
| rate | 0.0089 s/line |
| bar | 0.010514 s/line |
| rate as a share of the bar | 0.85x |

The delivered size is more than the named 160 + 60, as the brief warned. The
343 breaks as: row 1's section 216 (the named 160 charge, `appC` 20 +
`compFo` 41 + `Comp` 99 per `[LJ-1.264]`, plus `PairBound` 38 kept whole
because the shared `StageBound` is NOT delivered, plus section comments),
row 5's section 75 (the named 60 charge per `[LJ-1.234]` plus comments),
the once-paid header/imports/opens 49, and the row-3 marker 3.

## 1. MACHINE AND PROCESS DISCIPLINE

ONE agda process at a time, `GHCRTS="-A64m -I0 -M8g"`, cap never raised, no
heap exhaustion, no kill, no run past 30 minutes. The sibling LJ-1-278 was
live, so the load is elevated; the figure is an upper bound in the loaded
sense and still clears the bar.

| run | exit | cold/warm | elapsed s | 1-min load |
|---|---|---|---:|---:|
| master, run 1 | 0 | cold | 3.10 | 11.24 |
| master, run 2 | 0 | cold | 3.02 | 11.24 |
| master, run 3 | 0 | cold | 3.03 | 10.90 |
| `ReRun.agda` | 0 | cold (fresh) | 3.98 | 9.59 |

An earlier three-run set on the code-identical file (before a prose-only edit
outside the fence) read 3.26 / 3.19 / 3.06 s at load 8.0-8.4, mean 3.17 s.
Both sets agree within noise; the final-file figure above is reported.

## 2. THE ABORT CRITERION, FIXED BEFORE THE RUN (D-1)

- **BOTH ROWS LAND GREEN.** This fires. STOP. The master is `--safe`, exit 0,
  and the re-run imports it and exits 0.
- **ROW 1 NEEDS SOMETHING A2 KEPT PRIVATE.** Does not fire. See section 3.
- **ROW 1 IS NOT NEEDED.** Does not fire. Row 1 is needed, per `[LJ-1.264]`.
- **AN IMPORT IS NOT DELIVERED.** Does not fire. `lint-agda.py --check`
  exits 0, which is the import-necessity check.
- **A WALL.** Does not fire. Maximum single run 3.98 s.

## 3. PREMISES, EACH MARKED

**1. "Row 1 is 160 lines and NEEDED" (`[LJ-1.264]`).** VERIFIED.
`lj-1.264-report.md` read WHOLE. Its section 2 shows `noinj²` is a live
hypothesis of the delivered `InitialCore`
(`src/L/Ordinal/SquareLaw.lagda.md:705-707`), and its proof composes
`sqβ ∘ f`; the L-side composition is what supplies that site. My master
carries the same 160-line charge (`appC` + `compFo` + `Comp`).

**2. "Row 5 is delivered as a green probe" (`[LJ-1.234]`).** VERIFIED.
`ProbeLJ1234A.agda` read WHOLE; green, `--safe`. Its 60 charge lines land
verbatim into the master (with the ambient carrier written as `V ℓ`/`_∈_`,
see section 3's note).

**3. "Row 1's only undelivered import was A2" (`[LJ-1.268]:31`).** VERIFIED
FIRST against the landed master. Row 1 needs exactly four names from
`src/L/Coding/Injection.lagda.md`: `injAt`, `injAt-out`, `injAt-in`,
`module Small`. All four are EXPORTED (they sit before the `private` block at
`Injection.lagda.md:200`; the private range machinery begins at `:205`).
MEASURED by reading the master whole. **Nothing A2 kept private is needed.**
The `Extract` module is not even imported: `Small` already wraps it inside A2.

**4. "Rows 2 and 4 dissolved" (`[LJ-1.247]`).** VERIFIED.
`lj-1.247-report.md` read WHOLE. I did not rebuild either.

**5. "Prices in the NARROW caliber; expect more than 160 plus row 5."**
VERIFIED. Delivered 343 (ledger caliber, DD5), against a named charge of
220. The overage is the once-paid header plus `PairBound` (kept at 38 because
`StageBound` is not delivered; it is the "—" shared device, landing with row 3).

**6. "A2's master exports less than its probe did (P-k boundary)."** VERIFIED.
`lj-1.277-report.md` read WHOLE, section 2. I copied the method and checked
the boundary (premise 3 above).

## 4. WHAT THE MASTER EXPORTS, PER ROW, WITH CONSUMERS

**The order inside the file: row 5 first, then row 1.** Row 5 is wave 0 and
depends only on `L.Ordinal.SquareLaw`/`L.Ordinal` (ambient, no L-carrier).
Row 1 is wave 1 and depends on A2 (`L.Coding.Injection`) and the L axioms.
P-k: each row's read lemmas are stated at the form its consumer uses; the
two rows share no read lemma, so nothing is moved across them.

**Row 5 exports** `pairω : ⟪ ω ⟫ × ⟪ ω ⟫ → ⟪ ω ⟫`, `pairω-inj`, and
`squareω : sq ω`. The three hypotheses (`ω-limit`, `noinj²ω`,
`finite-excl-ω`) and the helper lemmas are also top-level but are the
`InitialCore` instantiation, not the consumer surface. **Consumer:** the
uniform square law `SqShape` (the A5 conclusion), whose base at `ω` this is.
A7 takes `SqShape` as the `sq` hypothesis of `GCHStatement`
(`ProbeLJ1236A7.agda:113-119`, `:149`), so A7 consumes `squareω` through
that chain, not by import.

**Row 1 exports** `appC`/`appC-adequate` (the constant-graph reader),
`compFo` + `module CompFo` (the composite condition and its two readings),
`module PairBound` (the stage bound), and `module Comp` with `K`, `K-spec`,
`K-out`, `K-in`, `svK`, `ijK`, `dmK`, `ranK`, `compFun`, `compFun-inj`.
**Consumer:** the `noinj²` proof (the L-side composition `sqβ ∘ f` that
refutes an injection into a member's square), a hypothesis of `InitialCore`.
That proof is downstream and is not landed here.

**What A6 and A7 each need, MEASURED from their probes.** A6 needs A2's
`injAt`/`injAt-in`/`module Small` (its `ProbeLJ1217A.agda:239` imports the
stale `ProbeLJ1134A` for exactly these) plus the shared `StageBound` (it
defines its own at `ProbeLJ1217A.agda:451`). A6 names NOTHING from row 1 or
row 5. A7 needs A2's `injAt` and A4's `InjCode`/`IsCardinalL` by import, and
takes `SqShape` and `AbsorbsShape` as HYPOTHESES, not imports
(`ProbeLJ1236A7.agda:113-126`). So neither A6 nor A7 imports this master
directly today; both consume its rows through the square-law chain's proof.

**Row 3's place.** It lands at the end of this file, where the closing
comment marks it. It stays out because its only probe imports the stale
`ProbeLJ1134A` (`[LJ-1.268]:2`), and it carries the shared `StageBound`
device, which is why `PairBound` here is kept at 38 lines rather than folded
into a bound that does not exist yet.

## 5. THE `src/Everything.lagda.md` LINE

**`import L.InjChain`**, to be inserted **after line 336
(`import L.Coding.Injection`), before line 337 (`import L.Coding.InL`)**.
The master's direct dependencies are all earlier in the fence:
`L.Constructible` (317), `L.Ordinal` (318), `L.Ordinal.SquareLaw` (323),
`L.Stage` (328), `L.Axioms.Basic` (329), `L.Axioms.Full` (332),
`L.Coding.Model` (335), `L.Coding.Injection` (336). I did NOT touch
`Everything.lagda.md`; the orchestrator wires it after audit.

## 6. THE RE-RUN (C-45)

**`agents/tasks/LJ-1-279/ReRun.agda`, exit 0, `--safe`, cold.** It imports
`module Comp; pairω; pairω-inj; squareω` from `L.InjChain` and uses each in
a consumer-shaped term:

- the C-38 guard, re-derived at this site: `Concrete` builds the
  non-degenerate graph `{⟨a,a⟩}` over `{a}` from `[LJ-1.134]`, `Witness`
  composes it WITH ITSELF through `Comp`, and `inK : ⟨ pr (fst a) (fst a) ∈
  fst Co.K ⟩` shows the composite is INHABITED, so nothing above is vacuous;
  `theComposite`/`theComposite-inj` show it runs as an honest injection;
- `WitnessZero = Witness (numeralL 0)` is the fully concrete instance;
- row 5 is re-asserted as `squareω-again : sq ω`, `pairω-runs`,
  `pairω-inj-again`.

`exit 0` of the master alone is not a supply; this re-run imports and
instantiates the master, which is the landing proof.

## 7. EVERY EXISTING MASTER I DID NOT EDIT

**MEASURED: zero tracked files modified.** `git diff --stat` over tracked
files is empty; `git status --short` shows no ` M` entry. The four
over-the-bar Condensation masters are untouched
(`src/L/Condensation.lagda.md`, `.../LowerAgree.lagda.md`,
`.../UpperAgree.lagda.md`, `.../TwelveAgree.lagda.md`), and so are
`src/L/Coding/Injection.lagda.md` (A2, today) and
`src/L/Coding/EnvSupply.lagda.md` (the sibling's). My writes are the new
master plus `agents/tasks/LJ-1-279/`. The sibling's `src/L/Cardinal.lagda.md`
and `agents/tasks/LJ-1-278/` are not mine and were not touched.

## 8. DD4, PER ROW, WITH THE AXIS

**Axis named (C-46): Def-against-J** (`dev/literature/devlin-II5.md:375`,
`:387-389`), the phase's proxy axis on which per-tower vs tower-neutral is
decided. DD4's OWN axis is AC-against-GCH (fixed in code at
`scripts/ledger.py:50`); it reports on import closures, and I state that
separately below.

- **Row 5 (`pairω`): TOWER-NEUTRAL on the Def-against-J axis.** MEASURED by
  `[LJ-1.234]` section 4: zero hits over the probe for `hasSeparationL`,
  `hasReplacementL`, `stage`, `LsetS`, `𝒮ʟ`, `boundingOrd`, `numeralL`,
  `prAtL`, `pairʟ`. The statement `sq ω` names no tower. The J tower
  re-instantiates it for free.
- **Row 1 (`Comp`): TOWER-NEUTRAL IN SHAPE on the Def-against-J axis, modulo
  two parameterized names.** The composite's statement names no tower atom;
  its L-internalization carries exactly `hasSeparationL` (one call) and the
  stage-bound device (`stage`/`boundingOrd`/`LsetS`, inside `PairBound`),
  both of which are module parameters, so the J tower re-instantiates the
  160 lines rather than rewriting them (`[LJ-1.264]` section 4). On the
  L-against-ambient axis it is NOT neutral (it is L content); that is not the
  axis the DD4 question lives on.

**On DD4's own AC-against-GCH axis:** this master is GCH-side content.
MEASURED: `grep -rl "L.InjChain" src/` returns only the master itself, so no
existing master imports it and the AC closure excludes it by construction;
the AC root `src/L/Model.lagda.md` has zero hits for it. It enters the GCH
closure the day the GCH endpoint lands, exactly as A2 did (`[LJ-1.277]`
section 6).

## 9. ARCHIVE USED (DD18)

One line read named per archived file.

- **`agents/tasks/LJ-1-234/ProbeLJ1234A.agda`, read WHOLE.** TAKEN: the whole
  row-5 content. Line read `:169`, `pairω p = fiber ω {x = colA p}
  (col∈α p) .fst`.
- **`agents/tasks/LJ-1-264/ProbeLJ1264A.agda`, read WHOLE.** TAKEN: the whole
  row-1 content. Line read `:460`, `K = fst (fst (hasSeparationL PB.bnd
  (compFo F H)))`, the separation that carries it.
- **`agents/tasks/LJ-1-264/lj-1.264-report.md`, read WHOLE.** TAKEN: why row
  1 is needed and where `noinj²` survives. Line read section 2, "the
  composition survives through a site the two dissolutions did not touch".
- **`agents/tasks/LJ-1-247/lj-1.247-report.md`, read WHOLE.** TAKEN: rows 2
  and 4 dissolving, and A5 = 348. Line read section 5's row table.
- **`agents/tasks/LJ-1-268/lj-1.268-report.md:23-48`, read.** TAKEN: the
  landing order and the three-wave split. Line read `:26`, "A5 row 5 (pairω)
  -> src/L/InjChain.lagda.md (new)".
- **`agents/tasks/LJ-1-277/lj-1.277-report.md`, read WHOLE.** TAKEN: how A2
  was landed and proved today, and the P-k boundary it chose; I copied the
  re-run method and checked the boundary. Line read section 2's export table.
- **`archive/dev/TASKS-archived.md:82`.** TAKEN, SHAPE ONLY: "L3.32-T47
  Truncated square law at initial ordinals — DELIVERED". The retired route
  built injection chains too.
- **`archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:470-480`.** 
  TAKEN, SHAPE ONLY: `comp m = k (comp₀ p e m)` with
  `k = fst (ih β ...)`, the same site-B composition `sqβ ∘ f`. **WHAT WOULD
  NOT TRANSFER: the line counts (P-l) and the internalization route, which
  the seven-block A-prime route replaced.**

## 10. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md:365-395`, read directly.** TAKEN: the
twelve-row step table (A, B, C1-C6, D, E, F, G) and the verdict at `:387-389`
that the per-tower content is exactly two objects.

**Which rows A5's two rows serve: row F** (5.5-5.6, "subsets appear early",
the counting with `|L_α| = |α|` and initial ordinals). Row 5's `squareω` is
the base of the square law `sq α`, and row 1's `Comp` supplies the `noinj²`
clause that makes `Init α` say "initial"; both are the initial-ordinal
machinery row F's cardinal argument consumes.

**Does the literature compose injections at all? NO.** Devlin II.5 states the
cardinal comparison by subset containment and level size, never by an
internal composition of injections. The composition `sqβ ∘ f` is a
metatheoretic operation in the literature's proof; A-prime's L-internalized
`Comp` is the project's own route machinery, not a step Devlin writes.
MEASURED as the absence of any injection-composition step in the digest's
section 1 spine (5.1-5.8).

## 11. THE NEGATIVES, CLASSIFIED

- **MEASURED FALSE. The master fails to typecheck.** exit 0, `--safe`, three
  cold runs and the re-run.
- **MEASURED FALSE. Row 1 needs something A2 kept private.** The four names
  it needs are all exported (`Injection.lagda.md:200` vs `:205`).
- **MEASURED FALSE. An import is not delivered.** `lint-agda.py --check`
  exits 0; every import is a delivered master.
- **MEASURED FALSE. A wall.** Max single run 3.98 s.
- **MEASURED FALSE. I touched an existing master or `Everything.lagda.md`.**
  `git diff --stat` empty; only new files written.
- **MEASURED FALSE. I touched `L.Choice.Name` or `agents/tasks/LJ-1-278/`.**
  Neither appears in my writes.
- **INFERRED. `PairBound` stays at 38 lines rather than the 16-line
  `StageBound`.** The shared device is not delivered; folding it here would
  mean landing row 3's content, which the brief forbids.
- **INFERRED. A6 and A7 consume these rows only through the square-law chain.**
  Their probes name no export of this master directly (MEASURED); that the
  chain's proof is the consumer is the reading from `[LJ-1.264]` section 2.

## 12. WORKING TREE, AS THIS REPORT DESCRIBES IT

Two files written plus this report, all new: `src/L/InjChain.lagda.md` (the
master), `agents/tasks/LJ-1-279/ReRun.agda` (the re-run), and
`agents/tasks/LJ-1-279/lj-1.279-report.md` (this file). No master, brief or
report edited. No commit, no push, no `git checkout .`, stash, reset or clean.
No `make check`; the orchestrator runs it. ONE agda process at a time, cap
never raised.

`scripts/lint-agda.py --check`, `scripts/lint-prose.py --check` and
`scripts/weave-i18n.py --check` all exit 0 on the master.

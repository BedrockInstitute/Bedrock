# LJ-1.355 report: the ambient `csb` port and the corollary

Written incrementally from the first five minutes (C-22). Every Agda run used
one process with `GHCRTS="-A64m -I0 -M8g"`. The cap was never raised. The
slot count was read before every invocation with the brief's exact command
and was 0 every time (C-12). The empty-file floor was measured beside every
seconds figure (C-53 as extended).

## VERDICT

**THE PORT LANDS GREEN at 82 non-blank code lines against the archived 80
(the brief's "105" counts blanks), and the corollary lands green at 21 more,
in the same master.** Both pieces are in one new master,
`src/V/CantorBernstein.lagda.md`, and nothing else in `src/` was touched.
The corollary's instantiation at the trophy's own `InjL` is green in a probe
at 15 code lines, and THAT wiring is the one edit this task's write scope
forbids: it belongs under `src/L/`, and I did not make it. Section 4 gives
the recipe.

The premise at risk, "about 100 lines", was slightly HIGH for the port alone
and right for the whole master. P-l held: the archived carrier is not this
one, and the delta is MEASURED at +2 lines (the set-ness hypothesis threaded
as a module parameter and two explicit type arguments), because the
construction was abstracted to arbitrary types for free.

## 1. The port

`src/V/CantorBernstein.lagda.md` holds four code blocks:

| Block | Lines | What |
|---|---|---|
| Header and imports | 15 | OPTIONS, `Base.Prelude`, `Base.Classical`, cubical |
| `module Bernstein` | 71 | the construction, at two ABSTRACT types |
| `small-set` + `cantor-bernstein` | 11 | the set form, at `V ℓ` |
| `module MutualInj` | 21 | the corollary, generic |

The construction is the archived chain proof re-derived line by line
(DD18, C-44), stated at `{A B : Type ℓ}` with ONE set-ness hypothesis
`setA : isSet A` and nothing else that mentions sets. That is the DD4
generic form: every consumer, ambient or internal, reads the theorem at its
own pair of types. The proof body is the miniature's body verbatim with
`A`/`B` for `⟪ a ⟫`/`⟪ b ⟫` and `lem` for `lowerLEM lem`; `[LJ-1.353]`'s
miniature already measured that body green on this tree, and the master
checked green on its first run.

The chapter parameter is `(lem : LEM ℓ)`, the WEAKEST dose: the hProps the
proof decides live at `ℓ`. Every L chapter holds `LEM (ℓ-suc ℓ)`, which
covers `LEM ℓ` through `lowerLEM`, so the probe instantiates with
`V.CantorBernstein (lowerLEM lem)` and nothing is lost.

Cold check of the new master: 1.72 s wall, one process. Final re-check:
1.38 s. Empty-file floor, measured the same day, same flags:
0.62 s (`agents/tasks/LJ-1-355/Floor.agda`). The master's own content is
about 0.8 s past the floor. All three gates are green on the whole tree:
`lint-prose.py --check`, `lint-agda.py --check`, `weave-i18n.py --check`.

## 2. The corollary

`module MutualInj` takes a carrier `C`, a small-type assignment `P`, an
injection notion `R : (a b : C) → Type ℓ₂`, set-ness `setP`, and a readback
`read : (a b : C) → R a b → Σ[ f ∈ (P a → P b) ] injective`. It returns:

- `mutual→bijection : R a b → R b a → Σ[ h ∈ (P a → P b) ] (injective ×
  truncated surjective)` for consumers holding witnesses as data;
- `∃bijection : ∥ R a b ∥₁ → ∥ R b a ∥₁ → ∥ the same Σ ∥₁` for notions that
  arrive truncated.

The second form exists because the trophy's `InjL` IS a truncation
(`src/L/GCH.lagda.md:38`), and a truncation cannot be eliminated into the
data a function is; negative control B measures that this is forced, not a
stylistic choice. The truncated conclusion matches the grade of the
hypotheses: the set-theorist's "there is a bijection" is exactly a
truncated existential, and the HoTT Book DEFINES cardinal inequality as one
(LITERATURE USED).

## 3. What did NOT transfer (DD18)

- **The retired carrier.** The archived block stated `csb` at `S` of the
  retired route's own structure instance. The live master states it at
  `V ℓ`, exactly the edit `[LJ-1.353]`'s miniature made
  (`agents/tasks/LJ-1-353/AmbCsb.agda:20`).
- **The `Graph`, `hostBij`, `csb-eq` block** (the bijection packaged as a
  set of Kuratowski pairs upgrading to `HostBij`/`HostEq`,
  `archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:193-282` region).
  It exists to feed the retired scope gate's ruling that equinumerosity IS
  "there exists a bijection". Porting it would re-open the ruling the brief
  forbids re-opening: `[LJ-1.323]` ruled the live packaging
  mutual-injections, and the corollary's job is the ambient reading of THAT
  statement, between the small types, which `cantor-bernstein` and
  `∃bijection` give directly.
- **The retired names.** `csb` and `module CSB` stay retired and still
  resolve at their archived home (C-41). The live names follow STYLE-agda
  §3: `cantor-bernstein` is a kebab theorem name, `Bernstein` a PascalCase
  module, and `csb` would be an unregistered abbreviation.
- **The rest of the archived chapter** (Cantor's theorem, the 5.4 hull
  lower bound and bijection form) belongs to the retired route's hull story
  and is out of scope.
- **The LEM level.** `lowerLEM lem` at `ℓ-suc ℓ` became plain `lem` at
  `ℓ`; this is a weakening, and the probe pays the one `lowerLEM` at its
  own import.

## 4. Consumers, and the ONE edit I did not make

In `src/`, the master currently has ZERO consumers: it is new, and nothing
imports it. Three consumers are pending, all outside this task's write
scope, all named here BEFORE any edit is made (the brief's channel):

1. **`src/Everything.lagda.md`**: the import and the reading-catalog entry.
   I never touch it (working rules). `lint`-level wiring, no mathematics.
2. **`src/README.md`**: the module-list entry and the symbol-table rows
   (`cantor-bernstein`, `∃bijection`, `small-set`). Same status.
3. **The L-side instantiation**, about 15 code lines, MEASURED green in
   `agents/tasks/LJ-1-355/InstProbe.agda` (1.45 s, floor 0.62 s). The
   recipe, verbatim from the probe: `setPL` (2 lines, via the exported
   `small-set`), `readL` (6 lines, the delivered `Small` readback applied
   to the four `InjCode` conjuncts, `src/L/Coding/Injection.lagda.md:103`),
   one `module MI = MutualInj ...` application (2 lines), and
   `csb-corollary = MI.∃bijection` (5 lines of statement). It consumes
   `InjL` from `src/L/GCH.lagda.md:38` WITHOUT editing that file. Placing
   it inside `src/V/` would invert the layering (no V master imports L,
   MEASURED: `grep -rn "import L\." src/V/` is empty), so it belongs in a
   new `src/L/` master or the tail of an existing one. That is the
   orchestrator's ruling to make.

The trophies: the GCH trophy consumes through item 3; the AC trophy
inherits the same substrate piece unchanged. `Small` itself gets its first
consumer outside its own master (`[LJ-1.353]` section 1 recorded it
delivered but unconsumed).

## 5. The closure for both ends (DD4)

**Axis (C-46), fixed at `scripts/measure/ledger.py:50`: what the AC and GCH
closures share.** `[LJ-1.353]` claimed both pieces are tower-free. CONFIRMED
by structure, MEASURED at the import list: the master imports `Base.Prelude`,
`Base.Classical` and cubical library modules ONLY. No `FOL`, no `V.*`
chapter, no `L.*`. It is pure substrate, one level above the hubs, so either
tower can import it without dragging anything but the hubs.

The ledger's reuse report on the surviving tree today: AC closure 73 masters
17,186 lines, GCH closure 48 masters 8,788 lines, SHARED 43 masters 7,585
lines, 41.0 percent of the 18,479-line union. My master is in NEITHER
closure yet, because nothing imports it; the wiring in section 4 puts it in
the GCH closure (118 non-blank lines) the moment it lands. Read beside
`dev/ledger.toml:200-206`: the GCH closure is computed from a statement
whose proof is not wired, so it UNDERSTATES by about 1,027 lines, and the
two chapters the proof needs most sit outside it. An honest closure count
for the trophy therefore already exceeds the ledger's; my master adds to
the shared core, not to either tower's private part, which is the direction
the no-gate ruling protects.

## 6. Negative controls (both MEASURED)

- **Control A, the construction is not vacuous.**
  `agents/tasks/LJ-1-355/NegA.agda` is the green miniature verbatim with ONE
  corruption: `h-inj` branch 1 proves `x ≡ x'` by `refl` instead of `fi`.
  Rejected: `[UnequalTerms] ... refl has type... error`, at
  `NegA.agda:114.37-41`, exit 42. The injectivity content of the green run
  is real.
- **Control B, the corollary's truncation is forced.**
  `agents/tasks/LJ-1-355/NegB.agda` claims the corollary's conclusion
  UNtruncated from the same truncated hypotheses. Rejected:
  `[UnequalTerms]`, at `NegB.agda:50.7-20`, exit 42. A truncation cannot be
  eliminated into function data, so the truncated conclusion is the honest
  strongest form.

## ARCHIVE USED

One line read per archived file, code cited (C-44):

- `archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:89-190`, read whole:
  the `module CSB` construction and the `csb` signature the port re-derives;
  the header at `:7-11` records that the installed library does not provide
  it.
- `archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md:10` and
  `:23`: the scope gate's ruling, equinumerosity as "there exists a
  bijection" to avoid a per-consumer CSB obligation. KEPT, not re-opened.
- `archive/dev/JOURNAL-archived.md:1370` and `:1377`: the trap that ruling
  avoided, and the "surfaced twice, lost twice" history.
- `archive/dev/TASKS-archived.md:106`: row `L3.32-T71` delivered Cantor and
  the ambient CSB on the retired route, taking SHAPE only.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:74-85`: HoTT Book Definition
  10.2.7, `card(A) ≤ card(B) :≡ ∥ inj(A,B) ∥`. TOOK, in one line as the
  brief asks: the corollary's surjectivity being truncated does NOT matter
  to the set-theorist reading, because the classical cardinal statements
  are themselves truncated existentials; the untruncated
  `mutual→bijection` is the grade the sources do NOT supply, kept for
  consumers holding witnesses as data. WHY NOT the rest: the file's
  untruncation machinery (unique choice, sections) prices extracting data
  FROM truncations, which this task never does.

## Term renderings (DD19)

No new rendering was chosen. 单射, 双射, 满射, 截断, 纤维, 原像, 排中律,
推论 and 交替 all appear in delivered `src/` zh prose (for example
`src/V/Coding.lagda.md:23`, `src/L/Axioms/Power.lagda:124`,
`src/L/Choice/Finite.lagda.md:116`, `src/FOL/LevyHierarchy.lagda.md:95`).
「坏」元素 and 坏集 are REUSED from the archived master's own zh block; they
are not in `dev/glossary.toml`. Flagged for the owner: route them through
the DD19 pipeline if they should become canonical. I did not stop the task
over this word because the rendering is reused from an in-repo corpus, not
newly decided.

## Measurements

| Item | Value | Basis |
|---|---|---|
| Port, non-blank in fences | 82 lines (`Bernstein` 71 + set form 11) | MEASURED |
| Archived `csb` block | 80 non-blank, 102 with blanks | MEASURED, `[LJ-1.353]` |
| Corollary `MutualInj` | 21 non-blank | MEASURED |
| Whole master in fences | 118 non-blank | MEASURED |
| Master cold check | 1.72 s, one process | MEASURED |
| Master final re-check | 1.38 s | MEASURED |
| Empty-file floor | 0.62 s | MEASURED, `Floor.agda` |
| Instantiation probe | 15 code lines, 1.45 s, exit 0 | MEASURED, `InstProbe.agda` |
| Negative control A | rejected at `NegA.agda:114`, exit 42 | MEASURED |
| Negative control B | rejected at `NegB.agda:50`, exit 42 | MEASURED |
| Slot count before every run | 0, every time | MEASURED |
| `make check` | NOT RUN, per the brief | rule |

## STATUS

- [x] Archive read: the CSB block whole, the scope gate, the journal rows.
- [x] Live tree surveyed: the readback `Small` is delivered.
- [x] `src/V/` master written and green.
- [x] Corollary written and green, plus the truncated form.
- [x] Negative controls run, both MEASURED rejections.
- [x] Consumers and DD4 closure reported; the one forbidden edit named.

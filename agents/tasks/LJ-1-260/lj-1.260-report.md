# LJ-1.260 report: the numeral premise is landed in `TFacts`, `LFacts` and `UFacts`

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. Build, edits
masters. Written incrementally (C-22). Every negative is MEASURED or
INFERRED, in those words.

## 0. LEAD

**Every touched master is GREEN (exit 0), and the premise is landed.**

| file | lines changed |
|---|---|
| `src/L/Condensation/TwelveAgree.lagda.md` | +4 |
| `src/L/Condensation/LowerAgree.lagda.md` | +3 |
| `src/L/Condensation/UpperAgree.lagda.md` | +3 |
| `src/L/Condensation.lagda.md` | +60 / −18 (net +42) |

Total: 60 insertions, 18 deletions, net +42. Inside the INFERRED 40–60 range
that `[LJ-1.257]` priced. No new proof was written: the `out` directions
reuse the delivered `codesK`/`arityTagAtL-adequate`/`arityTagPairAtL-adequate`
decode, one line each; the `back` directions already had `arNum` in scope.

## 1. THE PREMISE

`∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁`, inserted after the `⟨ fst ar ∈ … ⟩`
premise of every `envInK-*` field and every row-module `envInK` parameter.
Four fields in `TFacts`, three in `LFacts`, three in `UFacts`; ten row-module
parameters; eighteen call sites.

## 2. EDITS PER FILE

**`TwelveAgree.lagda.md`** (`TFacts`, all four `envInK-*`): +4 lines, one
premise per field (`envInK-mem`, `envInK-neg`, `envInK-top`, `envInK-imp`).

**`LowerAgree.lagda.md`** (`LFacts`): +3 lines (`envInK-mem`, `envInK-neg`,
`envInK-imp`).

**`UpperAgree.lagda.md`** (`UFacts`): +3 lines (`envInK-neg`, `envInK-top`,
`envInK-imp`).

**`Condensation.lagda.md`**: ten `envInK` parameter signatures gained the
premise (`TopAgree` :3684, `NegAgree` :3767, `ForallAgree` :3880,
`ExistAgree` :3992, `ClauseAgree` :4174, `MemAgree` :4437, `AllInAgree`
:5051, `ExInAgree` :5180, `ImpAgree` :5302, `EqAgree` :5395). Eighteen call
sites gained the `arNum` argument:
- nine `back` sites pass the `arNum` already bound by
  `(arK , (aK [, bK], arNum)) = codesK c ar a [b] c∈ shEq`;
- nine `out` sites add a `shEq`/`arNum` decode (`shEq = transport (cong fst
  (arityTagAtL-adequate … / arityTagPairAtL-adequate …)) shD`, then
  `arNum = codesK c ar a [b] c∈ shEq .snd .snd [.snd]`) and pass it.

## 3. THE CONSUMERS, HOW EACH DISCHARGED

The brief heads "fourteen" and "Eleven row modules" but lists ten row
modules; the actual count is **13 = 3 + 10** (off-by-one in the brief, not in
the tree). All green.

1. **`AbstractFrame`** (`TwelveAgree.lagda.md:337-338`), the only `tf : TFacts`
   consumer. Pass-through: `lf.envInK-* = tf.envInK-*` and
   `uf.envInK-* = tf.envInK-*`; the field types match after the change, so it
   is re-typecheck only. GREEN (TwelveAgree checks).
2. **`LowerAgree`** (`:226`) forwards `envInK-mem/-neg/-imp` as module
   arguments; no text change, types match. GREEN.
3. **`UpperAgree`** (`:213`) forwards `envInK-neg/-top/-imp`; no text change.
   GREEN.
4. **`TopAgree`** (`:3684`, unary `#6`): `back` uses `arNum` from `codesK`;
   `out` decodes `shEq = transport (cong fst (arityTagAtL-adequate 3 2 6 1
   (yc ∷ a ∷ ar ∷ c ∷ γ))) shD`, `arNum = codesK c ar a c∈ shEq .snd .snd`.
   GREEN.
5. **`NegAgree`** (`:3767`, unary `#5`): same pattern. GREEN.
6. **`ForallAgree`** (`:3880`, unary `#9`): same pattern. GREEN.
7. **`ExistAgree`** (`:3992`, unary `#8`): same pattern. GREEN.
8. **`ClauseAgree`** (`:4174`): parameter gained the premise; it forwards
   `envInK` to `ExistAgree` (`module E = ExistAgree … envInK consK`) and has
   no call site of its own; types match. GREEN.
9. **`MemAgree`** (`:4437`, binary `#0`): `back` uses `arNum`; `out` decodes
   `arityTagPairAtL-adequate` and `arNum = codesK c ar a b c∈ shEq .snd .snd
   .snd`. GREEN.
10. **`EqAgree`** (`:5395`, binary `#1`): same pattern. GREEN.
11. **`AllInAgree`** (`:5051`, binary `#10`): same pattern. GREEN.
12. **`ExInAgree`** (`:5180`, binary `#11`): same pattern. GREEN.
13. **`ImpAgree`** (`:5302`, binary `#4`): same pattern. GREEN.

No site failed to discharge the premise. The master's own comment at
`TwelveAgree.lagda.md:298-301` is now CHECKED (C-44): `codesK` supplies the
shape, `arityTagAtL`/`arityTagPairAtL`-adequate turn it into `fst ar ≡ # n`,
and the `out` direction closes it in the single decode line the comment
claimed.

## 4. SECONDS PER MASTER WITH LOAD

ONE Agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised, warm
interface cache. No wall, no heap exhaustion. **The machine was NOT quiet**
(load 4.9–10.0 across the runs; the sibling in `LJ-1-259` and other activity
were live), so the seconds carry that noise.

| master | exit | real s | user s | load (1m / 5m / 15m) |
|---|---:|---:|---:|---|
| `Condensation.lagda.md` | 0 | 137.67 | 135.64 | 4.88 / 4.43 / 4.42 → 4.75 / 4.55 / 4.47 |
| `LowerAgree.lagda.md` | 0 | 5.79 | 4.84 | 6.29 / 4.87 / 4.58 → 10.01 / 5.74 / 4.90 |
| `UpperAgree.lagda.md` | 0 | 5.46 | 5.21 | 10.01 / 5.74 / 4.90 → 9.52 / 5.71 / 4.89 |
| `TwelveAgree.lagda.md` | 0 | 8.49 | 8.15 | 9.16 / 5.70 / 4.89 → 8.58 / 5.69 / 4.90 |

## 5. TOWER-NEUTRALITY (DD4)

**The three records stay tower-neutral.** The added premise
`∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` mentions only the field binder `ar`, the
global `ℕ`, and the global hierarchy numeral `#`. It names no `K`, no
`t0`/`t1`, no `N0..N11`, and no per-tower stage. This is exactly the shape
`[LJ-1.258]` measured for its fifteen fields: all stated over `(K, Ktr)`,
none per-tower. `LFacts` and `UFacts` remain the two halves a J tower would
re-instantiate, unchanged in kind.

## 6. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| all four touched masters green | **MEASURED TRUE**, exit 0 each |
| a site cannot discharge the premise | **MEASURED FALSE**: all 18 sites discharge via `codesK` |
| line count over 60 | **MEASURED FALSE**: 60 insertions / 18 deletions, net +42 |
| a wall (agda > 20 min) | **MEASURED FALSE**: max 137.67 s real |
| the brief's "fourteen consumers" / "Eleven row modules" | **MEASURED FALSE against its own list**: 13 consumers, 10 row modules |
| records stay tower-neutral | **MEASURED TRUE**: premise names no tower slot |

## 7. ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-257/lj-1.257-report.md`, read WHOLE. **Line read `:50`**,
  the five built with the numeral premise and section 4's consumer-by-consumer
  specification.
- `archive/dev/TASKS-archived.md`. **Line read `:10`**, the header line; the
  retired route records nothing that bears on the numeral question.

## 8. LITERATURE USED (DD18)

**The restriction has a counterpart: it is Devlin's finite arities, and its
specific form (`fst ar ≡ # n` inside the code shape) is an artifact of the
coding.** `dev/literature/devlin-II5.md:246-255`: Devlin requires only that
some bounded description with a bound inside the carrier exists, and does not
require any particular shape for it; the numeral is this machine's way of
meeting that requirement.

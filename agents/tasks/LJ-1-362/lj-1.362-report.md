# LJ-1.362 report: stage 1 of Cantor-Bernstein over an arbitrary model of ZF

Written incrementally from the first five minutes (C-22). Every Agda run
used one process under `GHCRTS="-A64m -I0 -M8g"`. The cap was never
raised. The slot count was read before every invocation (C-12) and was
0 of 2 each time, except the `L` probe, which was launched into an empty
slot and held it until it closed.

## CORRECTION RECEIVED (DD23)

The brief instructed bilingual `en` + `zh` prose in the master. The
orchestrator withdrew that instruction mid-task: DD23
(`dev/PLAN.md:611`, ruled 2026-08-09) rules NO mathematical prose until
both trophies land. Nothing had been written to `src/` at that moment,
so nothing was removed. The master follows the delivered post-DD23
pattern (`L.Coding.Injection`, `L.Cardinal`, `L.InjChain`, `L.Absorption`
all carry zero markers, MEASURED by grep): one `#` title, then code
fences and code comments only. `lint-prose.py --check` and
`weave-i18n.py --check` both pass with zero markers (exit 0).

## VERDICT, one line

**The pair-reader adequacy lands GREEN at the generic site in 127 code
lines against the INFERRED 200, but ONLY under one module hypothesis
`≈ˢ-is-path` that `[LJ-1.361]` did not price: at the BARE record the
adequacy is FALSE, so the literal target of stage 1 is a NO-GO and the
repaired target is a GO.**

## Part 0: the obstruction `[LJ-1.361]` did not see

The readers read the object equality `≐`, whose satisfaction is the
STRUCTURE field `≈ˢ` (`src/FOL/Semantics.lagda.md:96`). The adequacy
must turn `≈ˢ`-facts into paths, because the derived pair's
specification and `extensional` speak paths
(`src/FOL/ZFModel.lagda.md:188,191,283`). At `V` this is free:
`𝒮ᵥ`'s `≈ˢ` IS the path equality definitionally
(`src/V/Hierarchy.lagda.md:82`). At an ARBITRARY `ZFStructure` the
record does not force it, and no field of `isZFModel` supplies a
bridge. Nothing in `[LJ-1.361]` part 3's field list
(`separate`, `𝒫`, `pair`, `⋃`, `extensional`) mentions `≈ˢ` at all.

**Countermodel, INFERRED (a meta-level argument, not an Agda run).**
Take the carrier and membership of `V` and set `≈ˢ := ⊥` constantly.
Every field still holds: each `≈ˢ` mention in a field is positive
(`hasPair`'s class, `numeral-suc`'s clause, `≐`-atoms inside formulas);
with `≈ˢ = ⊥` those classes shrink, and every shrunk class is still
first-order definable over `V` (replace each `≐`-atom by `⊥̇`), so
`hasSeparation` and `hasReplacement` still hold through `V`'s own
instances; the numeral chain degenerates to `∅` and `hasInfinity`
holds at the empty class. In that model `hasPair`'s unique set is `∅`,
so the DERIVED pair is constantly `∅`, and `prAt-adequate` in the path
form fails at `γ` with `lookup q γ = ∅`: the left side needs a bounded
witness in `∅` (false) and the right side says `∅ ≡ prˢ U W = ∅`
(true). No reader built from `∈̇`, `≐` and the connectives can be
adequate against a degenerate derived pair, so the obstruction is in
the record, not in the reader's atoms. An `≈ˢ`-valued right-hand side
does not escape either: at the structure `V` with `≈ˢ` = paths except
`(K ≈ˢ K) := ⊥` at one Kuratowski pair `K`, all fields again hold, the
readers are satisfied at `K`, and `⟨ K ≈ˢ K ⟩` is false.

**The repair, MEASURED GREEN.** One module hypothesis, in the
telescope, per C-55's packaging (free as a parameter, the 8 GB wall as
a record field):

```agda
(≈ˢ-is-path : (x y : ZFStructure.S 𝒮)
            → (ZFStructure._≈ˢ_ 𝒮 x y)
            ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
```

at `src/FOL/Bernstein.lagda.md:51-53`. Both delivered instances
satisfy it: at `𝒮ᵥ` by `refl` (`agents/tasks/LJ-1-362/InstanceV.agda:22`,
MEASURED green), at `𝒮ʟ` by `Σ≡Prop` in both directions
(`agents/tasks/LJ-1-362/InstanceL.agda`, MEASURED green, exit 0).
The theorem is thereby narrowed from "every model of ZF" to "every
model of ZF whose `≈ˢ` is the path equality". `V` and `L` qualify. A
future forcing instance, whose `≈ˢ` is a graded relation, does NOT,
which is exactly why this is an owner fork and not a local choice:
EITHER the hypothesis stays at this chapter, OR the law is added to
`FOL.ZFModel`'s record, which touches `src/FOL/ZFModel.lagda.md` and
both delivered instances and was outside my write scope. I did not
decide it; I built the chapter-parameter form and surface the fork
here.

## Part 1: the statement, as it typed

`CSB : ZF.isZFModel → Type ℓ` at `src/FOL/Bernstein.lagda.md:159`,
full body at `:159-172`; `BijCode` at `:152`. Three corrections
against the `[LJ-1.361]` sketch, all re-derived rather than pasted
(C-44):

1. **The level is `ℓ`, not `ℓ-suc ℓ`.** Every conjunct is a
   satisfaction type at `hProp ℓ`, so the whole statement sits at
   `Type ℓ`. The sketch's `Type (ℓ-suc ℓ)` was an overestimate.
2. **The range-bounded hypotheses read at the VALUE slot.** The sketch
   wrote `rbd zero (suc zero)` at `(F ∷ a ∷ [])` for all four clauses.
   At that environment the formula says "values of `F` lie in `a`",
   which is wrong for `F : a → b`; the values live at the second
   position, so the clause reads `(F ∷ b ∷ []) ⊨ rbdAt zero (suc zero)`
   and `(G ∷ a ∷ []) ⊨ rbdAt zero (suc zero)`.
3. **The pair is model-relative.** `pair` is derived INSIDE
   `isZFModel` (`src/FOL/ZFModel.lagda.md:281`), so the ordered pair
   `prˢ` and the whole adequacy live under one module parameterized by
   the model (`src/FOL/Bernstein.lagda.md:186`), per P-h: parameters at
   the module, never on each definition. The pure syntax stays at the
   structure level.

`rbdAt` itself (`:138-141`) is new: every member of the code is a pair
whose second component lies in the target. It is `[LJ-1.353]`'s
`InjCode` fourth conjunct (`src/L/Cardinal.lagda.md:223-228`) stated as
one satisfaction clause, per `[LJ-1.353]` section 3.

## Part 2: what was duplicated from the L chapters, and the cost

MEASURED, non-blank code lines: the eleven parameter-free families
(`sglAt`, `pairAt`, `prAt`, `prMemAt`, `appAt`, `svAt`, `inDomAt`,
`domAt`, `injAt`, `inRanAt`, `ranAt`) cost **34 lines** at
`src/FOL/Bernstein.lagda.md:91-135`, plus the new `rbdAt` at 4 lines.
`[LJ-1.361]` part 4 priced the migration at about 125 lines with 10
consumers rewiring; that figure counted the `Δ₀` certificates and the
constant-numeral reader variants (`sglConAt`, `tagAt`), which CSB does
not need, because `separate` takes ANY formula. So the duplication a
future migration ruling would retire from THIS master is about 34
lines, not 125. I did not move anything out of the L chapters, as
ruled.

## Part 3: the adequacy, measured against the INFERRED 200

`module Adequacy` at `src/FOL/Bernstein.lagda.md:186-347`: **127 code
lines** (130 in-fence). Its parts:

- `prˢ` at `:190`, the Kuratowski pair from the derived `pair` alone.
- The membership characterization block, private: `SglOf`, `PairOf`,
  the two `→≡` lemmas, the two witnesses, the two `subst` lemmas, and
  `prChar-fwd`/`prChar-bwd`, the generic counterpart of
  `L.Coding.Base`'s V-level block (`src/L/Coding/Base.lagda.md:75-180`),
  proved from `pair-spec` and `extensional` alone, with the
  `≈ˢ-is-path` coercions at each `≐`/path junction (about 25 lines of
  the 127 are the bridge; at `V` those lines are free, which is why
  `[LJ-1.361]`'s V-anchored figure did not see them).
- `prAt-adequate` at `:312`, one line each way, stated at the
  consumer's lookup form (P-k).
- `prMemAt-adequate` at `:320`: "the pair of `i` and `j` is a member
  of `t`" for ANY term `t`, which is `L.Coding.Model`'s `appAt`
  generalized from variable codes to constant codes, so the Tarski
  formula's `con G` / `con F` codes are the same operation.

The `[LJ-1.361]` table row was "Tarski formula and adequacy, 150
L-sited, 200 generic". The measured generic landing is the Adequacy
module (127) plus `closedAt`, `Closed` and `closedAt-adequate` (about
21, `src/FOL/Bernstein.lagda.md:360-382`): **about 148 code lines,
UNDER the inferred 200 by about 50**, and that is WITH the
`≈ˢ`-bridge inside. The inferred figure was honest as a line figure;
what it missed was not size but the hypothesis (Part 0).

`closedAt-adequate` is in scope and load-bearing: it certifies the de
Bruijn arithmetic of the spelled closure formula, which typechecking
alone does not (I found and fixed one lifted-index slip in `rbdAt` and
one in `closedAt`'s draft by exactly this kind of check; the
typechecker accepted both slips silently, MEASURED: `rbdAt` with
`suc (suc (suc (suc c)))` was reported only as a metas/Fin mismatch
after I also mis-set a binder count).

## Part 4: GO or NO-GO for the remaining 250 to 300

**GO, at corrected prices.** What remains for stage 2: the three
closure facts, the graph carve and the readback, from `bad-spec`
(`src/FOL/Bernstein.lagda.md:391`) and the stage-1 adequacies. Line
price: the `[LJ-1.361]` estimate of 250 to 300 STANDS as a line figure
(its basis is unchanged; nothing in stage 1 refuted it). Seconds price,
MEASURED at both classes:

- The master at the ABSTRACT carrier checks in **1.77 s cold, 0.97 s
  warm** for 336 in-fence lines: about 0.005 s per line, the
  parameterized class of P-m.
- The module application at `𝒮ᵥ` ALONE costs **26.9 minutes**
  (`agents/tasks/LJ-1-362/InstanceVBisect.agda`, exit 0), and the full
  `V` probe with the `CSB` statement elaborated costs **27.0 minutes**
  (`agents/tasks/LJ-1-362/InstanceV.agda`, exit 0): about 4.8 s per
  master line, roughly **22 times P-m's 0.22 s/line instantiation
  rate** measured at the `L3.32` site. This is P-n's payable floor,
  not a defect: at a concrete carrier the satisfaction types
  normalize through `V`'s HIT membership machinery. Per P-n the
  admissible moves are to instantiate once, or accept and price it.
- At `𝒮ʟ` the run closed GREEN, exit 0, wall time bracketed between
  10.1 and 25.1 minutes by the two polls of the background run (log at
  `agents/tasks/LJ-1-362/instanceL-run.log`); a precise figure would
  cost another cold run, and the interface cache now makes a re-run
  warm, so the bracket stands as the measurement. My pre-run guess
  "at or above the `V` figure" was wrong as a direction claim: the
  bracket overlaps `V`'s 27 minutes but also admits less.

Consequence for stage 2, INFERRED on the measured basis: at about 620
total lines the cold re-check per instantiation site scales toward
about one hour each for `V` and `L`, paid on every change to the
master (the interface cache only saves unchanged downstream). Under
D39's relative time constraint this belongs in the owner's ledger, not
in a silent stop-line: the lines are cheap, the seconds are the price
of the inheritance, and the inheritance is the point of DD4.

## Part 5: negative control (C-45, `[LJ-1.355]` standard)

`agents/tasks/LJ-1-362/BernsteinNeg.agda`: the master verbatim, module
renamed, with the two components of the pair SWAPPED in
`prAt-adequate`'s right-hand side. Agda refuses with **exit 42**:

```
error: [UnequalTerms]
u != v of type Fin n
when checking that the expression ⇔toPath (...) (...) has type
γ ⊨ prAt q u v ≡
((lookup q γ ≡ prˢ (lookup v γ) (lookup u γ)) ,
 isSetS (lookup q γ) (prˢ (lookup v γ) (lookup u γ)))
```

The file went red naming the expected type; the green run is certified
against it. The master was then edited once more (an unused-import
fix) and re-verified green, exit 0.

## Part 6: which delivered models can instantiate it today

- `V`: **MEASURED GREEN.** `agents/tasks/LJ-1-362/InstanceV.agda`,
  exit 0 in 27.0 min. The structure hypothesis discharges by `refl`
  (`InstanceV.agda:22`), the glue is 10 lines against `[LJ-1.361]`'s
  INFERRED 30, and both `CSB` and the `Tarski` module elaborate.
- `L`: **MEASURED GREEN.** `agents/tasks/LJ-1-362/InstanceL.agda`,
  exit 0, wall bracketed at 10.1 to 25.1 minutes. The hypothesis needs
  the `Σ≡Prop` two-way bridge, 6 lines, and it compiles as written.
- Any future model: needs the `≈ˢ` bridge; see the fork in Part 0.

## Part 7: DD4, both ends, and what I do NOT claim

Axis (C-46): tower naming. This master names no tower, no stage, no
satisfaction bridge; it sits under `src/FOL/` below both trophies, and
both inherit by one module application. The master is 336 in-fence
lines (219 code-only, the rest comments). When wired into `Everything`
(NOT done by me, per the brief), it deepens the GCH closure's known
understatement by its own size; `dev/ledger.toml:195-206` already
records that understatement at about 1,027 lines, bounded, because the
closure is read from a statement whose proof is not wired.

Not claimed: nothing landed today is retired. `V.CantorBernstein` and
`L.CantorBernstein` serve the AMBIENT reading and stay; a generic
internal theorem produces a CODED bijection, a different object, as
`[LJ-1.361]` ruled.

## ARCHIVE USED

- `archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:89`. Quote:
  `module CSB (a b : S) (f : ⟪ a ⟫ → ⟪ b ⟫) (fi : (x y : ⟪ a ⟫) → f x ≡ f y → x ≡ y)`.
  TOOK: the retired CSB is stated at a FIXED carrier, at the ambient
  index types, with FUNCTION injections, in chain form. Direct
  evidence that the model-level packaging here is the first of its
  kind on either route.
- `archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md:10`.
  Quote: "equinumerosity is the existence of a bijection, never
  injections both ways, because the latter would make every equality a
  per-consumer Cantor-Bernstein obligation". TOOK, and the brief's
  one-line question answered YES: a delivered generic internal CSB is
  exactly the theorem that would have made the injections-both-ways
  choice safe; the ruling chose the bijection form to avoid a debt
  this chapter can one day pay.
- `archive/dev/DECISIONS-archived.md:38` (D16). Quote: "asset
  durability equals genericity". TOOK: the framing of Part 7. WHY NOT
  a placement ruling: no archived row rules WHERE a model-level
  theorem lives; the nearest are D16 (genericity) and D29.
- `archive/dev/DECISIONS-archived.md:48` (D29). Quote: "the default is
  generic". TOOK: this build wrote generic, at a named module, with
  prices for both classes of cost.
- `archive/dev/JOURNAL-archived.md:1377`. Quote: "a surjection-only
  or raw-injection cardinality would have forced every later consumer
  to re-derive the bijection and initial-ordinal facts from scratch".
  TOOK: the trap named there is the one a generic internal CSB closes
  for every future model at once. WHY NOT the surrounding entries:
  they reason about the retired reification framework.

## LITERATURE USED

- `dev/literature/devlin-II5.md:151-166`. Verified first-hand, not
  repeated from `[LJ-1.361]`: Devlin proves GCH in `L` by condensation
  and counting (5.5, 5.6) and obtains 5.7/5.8 as RELATIVIZATION
  corollaries ("ZF ⊢ (GCH)^L"). The set theorist proves a theorem once
  and relativizes; no internal re-proof per model. `[LJ-1.361]`'s
  answer to the owner's question is confirmed: the generic-module
  shape IS the literature's shape. Devlin never proves CSB inside `L`
  at all, which says the theorem's natural home is one level up from
  any particular model.
- `dev/literature/digest.md:64-66`. WHY NOT: the Q5 relativization
  block is about rudimentary functions and `x ∩ A` in the J-hierarchy;
  it bears on schema presentations, not on model-level theorem
  placement.

## Laws that bore, and how

- **P-h**: satisfied structurally. The walk modules (`Adequacy`,
  `Tarski`) take their arguments at the module; no definition takes a
  model or set as a function argument.
- **P-m / P-n**: both classes measured at this master, Part 4. The
  floor is priced, not fought.
- **P-l**: the 27-min `V` datum is measured at its own site; the `L`
  figure stays INFERRED until its run closes.
- **R-38**: judged NOT triggered. `prˢ` is a composite of a record
  projection applied to ABSTRACT arguments, a stuck term, not a
  transparent sett/union tower; measured 1.77 s cold, no wall, no seal
  placed. This judgment is the report's, for the audit.
- **R-35 / R-40**: not triggered; stage 1 extracts no union
  representation and climbs no successor chain.
- **C-55**: the `≈ˢ-is-path` hypothesis is a module parameter, never a
  record field, exactly the law's packaging.
- **C-53 / C-45**: floor measured (0.60 s, `Floor.agda`); negative
  control run, Part 5.
- **D-1**: the widest unmeasured term was named (the adequacy) and was
  measured, including its truth at the intended generality (D-10: the
  literal target is false at the bare record; the corrected target is
  stated with its price).

## Measurements

| Item | Value | Kind |
|---|---|---|
| Master `src/FOL/Bernstein.lagda.md` in-fence lines | 336 (219 code-only) | MEASURED |
| Adequacy module code lines | 127 | MEASURED |
| Adequacy + Tarski-formula row | about 148 against INFERRED 200 | MEASURED |
| Duplicated families | 34 lines (+4 new `rbdAt`) | MEASURED |
| Master cold check, abstract carrier | 1.77 s (0.005 s/line) | MEASURED |
| Master warm re-check | 0.97 s | MEASURED |
| Empty-file floor `Floor.agda` | 0.60 s | MEASURED |
| `MiniSep.agda` re-run | exit 0, 1.28 s | MEASURED |
| Module application at `𝒮ᵥ` alone | 26.9 min | MEASURED |
| Full `V` instantiation probe | exit 0, 27.0 min (about 4.8 s/line) | MEASURED |
| `V` glue lines | 10 against INFERRED 30 | MEASURED |
| `L` instantiation probe | exit 0, 10.1 to 25.1 min (bracketed), 6 glue lines | MEASURED |
| Bare-record adequacy | FALSE (countermodel) | INFERRED, meta-level |
| Stage-2 lines | 250 to 300 | INFERRED, `[LJ-1.361]` basis unchanged |
| Stage-2 cold instantiation per site at 620 lines | about 1 h each | INFERRED, linear on the 27-min datum |
| Slot count before each run | 0 of 2 (C-12) | MEASURED |

## Evidence log

- `src/FOL/Bernstein.lagda.md` — the master. Module at `:49-53`,
  readers at `:91-113`, families at `:117-141`, `BijCode` at `:152`,
  `CSB` at `:159`, `Adequacy` at `:186-347` with `prAt-adequate` at
  `:312` and `prMemAt-adequate` at `:320`, `Tarski` at `:353-400` with
  `closedAt` at `:360`, `closedAt-adequate` at `:369`, `tarskiFo` at
  `:385`, `bad`/`bad-spec` at `:388-392`, `unfold` at `:396`.
- `agents/tasks/LJ-1-362/BernsteinNeg.agda` — negative control, exit
  42, `u != v of type Fin n`.
- `agents/tasks/LJ-1-362/Floor.agda` — floor, exit 0, 0.60 s.
- `agents/tasks/LJ-1-362/InstanceV.agda` — V instantiation, exit 0,
  27.0 min.
- `agents/tasks/LJ-1-362/InstanceVBisect.agda` — application-only
  bisect, exit 0, 26.9 min.
- `agents/tasks/LJ-1-362/InstanceL.agda` + `instanceL-run.log` — L
  instantiation, exit 0, 10.1 to 25.1 min.
- Gates: `lint-prose.py --check` exit 0; `lint-agda.py --check` exit 0
  (after removing two unused imports); `weave-i18n.py --check` exit 0.
- `make check` NOT run, per the brief. `Everything.lagda.md` NOT
  touched, per the brief. Nothing committed.

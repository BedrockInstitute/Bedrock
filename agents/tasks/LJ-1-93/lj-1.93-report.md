# LJ-1.93: be the first consumer of the three split masters

Status: ABORTED at the pre-fixed criterion, per D-1. No commit, no push.
ASD-STE100. This report is `_build/lj-1.93-report.md`.

## 0. THE VERDICT

**The twelve conjuncts are the same formulas, index for index. The
association differs. The pack cannot be supplied: 39 of the composer's
69 hypotheses have no supplier in the consumer's telescope. Per the
abort criterion, STOP here. `twelve-out` and `twelve-back` are NOT
discharged.**

The deciding negative is MEASURED: the instantiation attempt
(`src/ProbeLJ193B.agda`) leaves exactly 39 unsolved metas at the 39
named argument positions, exit 42; two representative mismatches are
machine-checked in `src/ProbeLJ193C.agda`; the consumer's full
telescope and the composer's full telescope are both quoted at
`file:line` below. The association half is green and generic
(`src/ProbeLJ193A.agda`, both directions).

The term I could not write is `valK` at the consumer's frame (section
4). What must provide it, and the other 38, is named there. Nothing is
written into a master. Every master is untouched.

## 1. THE TWELVE CONJUNCTS, INDEX FOR INDEX

**All twelve conjuncts are literally the same formulas on both sides,
index for index.** The consumer's `SatGraphB.twelveB`
(`src/L/Condensation.lagda.md:2233-2254`) is one right-nested chain
`C₀ ∧̇ (C₁ ∧̇ (... C₁₁))`. The composer's `twelveB` is
`p0b ∧̇ p1b` (`src/L/Condensation/TwelveAgree.lagda.md:270-271`), where
`p0b = LowerAgree.sixB` (`.lagda.md:248-257`) and
`p1b = UpperAgree.sixB` (`.lagda.md:259-268`). The sixes are the same
conjuncts as the consumer's chain, in the same order, with the
consumer's private `K' = suc⁶ K` (`src/L/Condensation.lagda.md:2230-2231`)
spelled as `suc⁶ K` in the sixes.

| index | consumer conjunct (`Condensation.lagda.md`) | composer conjunct | same |
|---|---|---|---|
| 0 | `Mem.memBndAt` `:2235-2237` | `LowerAgree.sixB` `:228-232` | yes |
| 1 | `Eq.eqBndAt` `:2238-2240` | `LowerAgree.sixB` `:233-237` | yes |
| 2 | `And.andBndAt` `:2241` | `LowerAgree.sixB` `:238-240` | yes |
| 3 | `Or.orBndAt` `:2242` | `LowerAgree.sixB` `:241-243` | yes |
| 4 | `Imp.impBndAt` `:2243` | `LowerAgree.sixB` `:244-246` | yes |
| 5 | `Neg.negBndAt` `:2244` | `LowerAgree.sixB` `:247-249` | yes |
| 6 | `Top.topBndAt` `:2245` | `UpperAgree.sixB` `:218-220` | yes |
| 7 | `Bot.botBndAt` `:2246` | `UpperAgree.sixB` `:221-223` | yes |
| 8 | `Exist.existBndAt` `:2247` | `UpperAgree.sixB` `:224-226` | yes |
| 9 | `Forall.forallBndAt` `:2248` | `UpperAgree.sixB` `:227-229` | yes |
| 10 | `AllIn.allInBndAt` `:2249-2251` | `UpperAgree.sixB` `:230-234` | yes |
| 11 | `ExIn.exInBndAt` `:2252-2254` | `UpperAgree.sixB` `:235-239` | yes |

The machine check of the consumer half: `consumerIsRight` proves
`SatGraphB.twelveB ≡ C₀ ∧̇ (C₁ ∧̇ (... C₁₁))` by `refl`
(`src/ProbeLJ193A.agda:176-179`), where `C₀..C₁₁` are the twelve texts
written out at `:104-166`. The composer half is the source text at the
lines above; the bridge instantiation in section 2 closes the loop at
the satisfaction level.

The association is the ONLY difference: the consumer's outer `∧̇` has
`Mem.memBndAt` on its left; the composer's outer `∧̇` has the six-fold
left component `p0b` on its left. The abort criterion "a conjunct
differs" does NOT fire.

## 2. THE ASSOCIATION BRIDGE

The bridge is pure logic and it is generic in the conjuncts.
Satisfaction of a conjunction is definitionally the product of the
satisfactions: `γ ⊨ (φ ∧̇ ψ)` is `(γ ⊨ φ) ⊓ (γ ⊨ ψ)`, and `⟨ A ⊓ B ⟩`
is `⟨ A ⟩ × ⟨ B ⟩` in the hProp algebra. So the twelve-way
re-association is product re-association, stated once over any twelve
formulas at any environment:

- `AssocBridge.to-left` and `AssocBridge.to-right`,
  `src/ProbeLJ193A.agda:57-97`. The module names no conjunct and no
  carrier. The J tower gets it unchanged: INFERRED, no J-site exists;
  the statement transfers by construction because it quantifies over
  arbitrary formulas.
- Instantiated at the consumer's environment:
  `ConsumerJoin.to-consumer` / `from-consumer`,
  `src/ProbeLJ193A.agda:194-215`. Green.

The bridge was NOT written into a master. The join cannot physically
live in `src/L/Condensation.lagda.md`: `TwelveAgree.lagda.md:31`
imports the master, so the master importing `TwelveAgree` back is a
cyclic module dependency, which Agda rejects (verified with a minimal
repro in `/tmp/lj193-cyc/`, error `[CyclicModuleDependency]`). A
bridge with no consumer in a master would be dead weight (D-30). The
bridge lives in the probe, green, at the lines above.

## 3. THE HYPOTHESIS PACK TABLE

The consumer is `SatGraphAgree`, `src/L/Condensation.lagda.md:6476-6696`.
Its telescope is: the slots `w K N0..N11 t0 t1` (`:6476-6477`), the
environment `γ : S ^ (8 + n)` (`:6478`), one `KFacts` record `f`
(`:6479-6485`; the record itself is `:5734-5770`, 29 fields, ending at
the `arityK` field `:5769-5770`), the two join hypotheses
(`:6486-6491`), and six site facts: `codesK` `:6492-6496`, `unCodesK`
`:6497-6500`, `closedEntryK` `:6501-6503`, `domEntryK` `:6504-6506`,
`domK` `:6507-6508`, `witK` `:6509-6513`. `LeafAgree` (`:6705-6823`)
states the same two join hypotheses at `:6729-6734` and passes them to
`SatGraphAgree` at `:6786`; its own telescope adds no supplier for the
composer's facts.

The composer is `TwelveAgree.AbstractFrame`,
`src/L/Condensation/TwelveAgree.lagda.md:45-243`, 69 hypotheses. The
table below says, for each, what supplies it. The supplied 30 are
machine-checked: they are exactly the arguments that typecheck in the
probe-B application. The missing 39 are machine-checked as unsolved
metas at the same application (section 4).

| # | hypothesis | supplier |
|---|---|---|
| 1-12 | `tagEq0`..`tagEq11` | `KFacts` via `lift3 d e f` (`Condensation.lagda.md:6520-6575`), fields `:5737-5748` |
| 13-24 | `numK0`..`numK11` | `KFacts` via `lift3`, fields `:5749-5760` |
| 25 | `innerK` | `KFacts.innerK` (`:5761-5762`) |
| 26 | `pairK` | `KFacts.pairK` (`:5765-5766`) |
| 27 | `codesK` | consumer `codesK d e f` (`:6492-6496`), same type at `γ' = f ∷ e ∷ d ∷ γ` |
| 28 | `codesK-un` | consumer `unCodesK d e f` (`:6497-6500`) |
| 29 | `valK` | NOTHING |
| 30 | `valK-un` | NOTHING |
| 31 | `t0eq` | NOTHING |
| 32 | `t1eq` | NOTHING |
| 33 | `t0K` | NOTHING |
| 34 | `tmKeyK` | NOTHING |
| 35 | `num1K` | `KFacts.numK1` (same type) |
| 36 | `envK-mem` | NOTHING |
| 37 | `envK-neg` | NOTHING |
| 38 | `envK-top` | NOTHING |
| 39 | `envK-imp` | NOTHING |
| 40 | `envK-allin` | NOTHING |
| 41 | `entryK` | NOTHING (consumer's `closedEntryK` is the code-slot instance, not the z-general statement) |
| 42-45 | `arSubK-mem`..`arSubK-imp` | NOTHING |
| 46-49 | `envInK-mem`..`envInK-imp` | NOTHING |
| 50 | `valV` | NOTHING |
| 51 | `valW` | NOTHING |
| 52 | `wKfact` | NOTHING |
| 53 | `transK` | `KFacts.arityK` by a binder swap: `λ x a hxa haK → arityK a x hxa haK` (machine-checked in probe B) |
| 54-57 | `subK₁-and`..`subK₀-imp` | NOTHING |
| 58 | `someEnv` | NOTHING |
| 59 | `subK-neg` | NOTHING |
| 60 | `keyK-neg` | NOTHING |
| 61 | `succK` | NOTHING |
| 62 | `keyK-un` | NOTHING |
| 63 | `subK-un` | NOTHING |
| 64-65 | `consK-exist`, `consK-forall` | NOTHING |
| 66-69 | `succK-allin`, `keyK-allin`, `subK-allin`, `consK-allin` | NOTHING |

Count: 27 from `KFacts`, 1 from `KFacts` by binder swap, 2 from the
consumer's site facts, 39 from NOTHING. 27 + 1 + 2 + 39 = 69.

The classification of the "NOTHING" rows: the source listing is
MEASURED (every consumer parameter type is at the lines cited above,
and none is the needed type). The instantiation failure at the 39
positions is MEASURED (`src/ProbeLJ193B.agda`, exit 42, 39 unsolved
metas). The claim that no clever derivation of any single one exists
is INFERRED except where a concrete candidate is machine-checked;
the verdict rests on the measured instantiation failure plus the
measured listing, not on those inferences.

## 4. THE TERMS THAT COULD NOT BE SUPPLIED

The term I could not write, first in telescope order
(`src/L/Condensation/TwelveAgree.lagda.md:86-88`):

```agda
valK : (k : ℕ) (c ar a b yc : S)
     → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ') ⟩
     → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
     → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
```

The conclusion is `yc ∈ K-slot` for an ARBITRARY `yc` with no premise
tying `yc` to the code. The consumer holds no fact with that shape:
`KFacts` concludes memberships of the pair/`prʟ`/arity components of
its own arguments (`:5761-5770`), the site facts conclude memberships
of `ar a b` (codesK), `x y` (closedEntryK, domEntryK), `x` from the
code slot (domK), and `d e f` from the graph body (witK). None can
conclude `yc ∈ K-slot` for a fresh `yc`. MEASURED: the probe-B
application leaves `valK` as the first unsolved meta.

The other 38 unsuppliable terms, in one line each at their source
lines: `valK-un` `:89-91`, `t0eq` `:92`, `t1eq` `:93`, `t0K` `:94-95`,
`tmKeyK` `:96`, `envK-mem` `:98-101`, `envK-neg` `:102-105`,
`envK-top` `:106-109`, `envK-imp` `:110-113`, `envK-allin`
`:114-117`, `entryK` `:118-120`, `arSubK-mem` `:121-123`,
`arSubK-neg` `:124-126`, `arSubK-top` `:127-129`, `arSubK-imp`
`:130-132`, `envInK-mem` `:133-136`, `envInK-neg` `:137-140`,
`envInK-top` `:141-144`, `envInK-imp` `:145-148`, `valV` `:149-154`,
`valW` `:155-160`, `wKfact` `:161-166`, `subK₁-and` `:170-175`,
`subK₀-and` `:176-181`, `subK₁-imp` `:182-187`, `subK₀-imp`
`:188-193`, `someEnv` `:194`, `subK-neg` `:195-200`, `keyK-neg`
`:201-204`, `succK` `:205-206`, `keyK-un` `:207-208`, `subK-un`
`:209-214`, `consK-exist` `:215-219`, `consK-forall` `:220-223`,
`succK-allin` `:224-228`, `keyK-allin` `:229-235`, `subK-allin`
`:236-241`, `consK-allin` `:242-243`.

Two representative mismatches are machine-checked
(`src/ProbeLJ193C.agda`, both exit 42):

1. `t0eq` from `kf .tagEq0`: error `N0 != t0 of type Fin (suc (suc (suc (suc (suc n)))))`
   (`:67.20-30`). The consumer's `KFacts` states `tagEq0` about the
   `N0` slot and nothing about the `t0` slot.
2. `entryK` from `closedEntryK d e f`: the consumer's fact is pinned
   to the code slot, the composer's is quantified over every `z`
   (`:69.22-40`). The types differ.

What must provide the 39: a frame at which the composer's telescope is
stated, that is, the 69-fact frame the composer was built for
(`_build/lj-1.76-report.md:158-165`). The consumer-side supply needs
either (a) the composer re-stated at the consumer's 29-field `KFacts`
frame, or (b) a new supply layer that derives the 39 from `KFacts` and
the six site facts. Option (b) cannot exist for several of them:
`t0eq` needs a fact about the `t0` slot, which `KFacts` never states;
`valK`, `tmKeyK` need universal-`K` conclusions; `envK-*`, `subK-*`,
`succK`, `consK-*` are satisfaction-premise facts the consumer does
not hold. Per the brief, adding them as consumer hypotheses is
forbidden ("do not add a hypothesis to the consumer"). The abort
criterion fires: STOP.

## 5. LINES ADDED AND COLD SECONDS

No master was touched. In-fence lines added: 0.

Probes (all untracked, gitignored):

| file | result | seconds (total) | seconds (user) | load (start/end) |
|---|---|---|---:|---:|
| `src/ProbeLJ193A.agda` | GREEN, exit 0 | 10.97 first cold; 2.67 warm re-check | 1.60 warm | 6.39 / 6.39 |
| `src/ProbeLJ193B.agda` | exit 42 as designed, 39 unsolved metas | 3.11 | 2.82 | 6.19 / 6.42 |
| `src/ProbeLJ193C.agda` | exit 42 as designed, mismatch | 1.68 | 1.52 | 6.42 / 7.35 |

Line counts: A 214, B 221, C 76, total 511. The machine was NOT quiet
(four users, load 4.1 to 7.4). Every absolute figure carries that
caveat. No master seconds exist because no master was touched.

## 6. THE DD4 ANSWER

The association bridge is generic in the conjuncts: `AssocBridge`
quantifies over twelve arbitrary formulas and an arbitrary
environment, and its proofs are pure product re-association
(`src/ProbeLJ193A.agda:57-97`). The J tower gets it unchanged:
INFERRED, no J-site exists, and the statement transfers by
construction because it never names a conjunct.

The pack finding is a DD4-negative at the frame level. The split
masters maximize sharing at the 43/43/69-fact frame
(`_build/lj-1.76-report.md:158-165`), but the consumer's shared
`KFacts` layer is the 29-field frame (`Condensation.lagda.md:5734-5770`).
The two frames do not meet: 39 facts live only on the composer's side.
Sharing is only free when the shared frame is the frame the consumer
actually holds. The composer as built cannot be consumed by this
consumer; that is the C-35/C-38 audit's finding, and it is MEASURED.

## 7. ARCHIVE USED

- `_build/lj-1.76-report.md`, read WHOLE. TOOK the 69-fact frame, the
  `p0b ∧̇ p1b` choice, the "delivered-and-unconsumed" verdict. The
  frame mismatch this dispatch measured was predicted there as
  "generic in the 69 facts", never as consumable from `KFacts`.
- `_build/lj-1.77-report.md`, read WHOLE. TOOK the `KFacts` field
  census and the C-12 invocation line.
- `_build/lj-1.79-report.md`, read WHOLE. TOOK the guarded `KFacts`
  forms (the record this dispatch audits) and the
  "refuted is not inhabited" discipline.
- `_build/lj-1.78-report.md` and `_build/lj-1.71-report.md`, read.
  TOOK the probe shape and the C-38 instantiation standard.
- `src/L/Condensation.lagda.md:2227-2385`, read. TOOK the whole
  `SatGraphB` module; `twelveB` is `:2233-2254`.
- `src/L/Condensation.lagda.md:5734-5770`, read. TOOK the `KFacts`
  record: 29 fields, ends at the `arityK` field `:5769-5770`.
- `dev/LESSONS.md`, read WHOLE of C-38 as extended (`:3427-3511`),
  C-35 (`:3200-3242`), C-36 (`:3284-3332`), D-30 (`:3332-3380`), P-w
  (`:3094-3170`), P-i (`:203-301`), C-37 (`:3382-3424`), C-32
  (`:2947-2987`), C-33 (`:2987-3037`), D-1 (`:1038-1195`), D-8
  (`:1377-1397`), D-26 (`:1676-1854`), D-29 (`:3242-3284`), P-c
  (`:71-173`), R-36 (`:808-829`), P-o (`:2509-2600`), C-31
  (`:1855-2074`). TOOK the discharge standard, the
  inference-vs-measured discipline, and the module-application cost
  law.
- `dev/PLAN.md` section 11 rows `LJ-1.72` to `LJ-1.93` (`:540-572`),
  read. TOOK the dispatch history: every prior "discharged" claim in
  this line was overturned at first consumption; this dispatch is the
  same audit one step later.
- `archive/rud-route/`, SHAPE only. Took nothing.

## 8. LITERATURE USED

Nothing in the literature prices a spelling. This is a wiring task
inside our own encoding and no source speaks to it. One line, nothing
spent.

## 9. GATES

- `scripts/check-fences.py --check`: clean, 87 masters.
- `scripts/lint-prose.py --check` on this report and the three probes:
  exit 0.
- `scripts/lint-agda.py --check`: exit 0.
- `scripts/ledger.py --brief`: standing 28,189 lines over 85 masters,
  measured from HEAD. The probes and this report are gitignored and do
  not move the standing.
- `scripts/check-ratio.py` refused on this machine in earlier
  dispatches (its pgrep guard cannot verify the process list); it was
  not needed here because no master was touched.
- No `make check`. No commit, no push.

Working tree: `src/ProbeLJ193A.agda` (green), `src/ProbeLJ193B.agda`
and `src/ProbeLJ193C.agda` (failing as designed), this report, and the
pre-existing `dev/PLAN.md` modification that was present at the start.
No master under `src/` was edited; `src/Everything.lagda.md`,
`src/L/Coding/` and `src/V/` are untouched.

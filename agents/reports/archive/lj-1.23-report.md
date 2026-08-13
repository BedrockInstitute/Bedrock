# LJ-1.23 report: the hull on the meta term algebra (DD27)

## 1. THE VERDICT

DELIVERED. The hull is re-indexed by the meta term algebra `Code`.
`src/L/Hull.lagda.md` is 431 in-fence lines, up from 372, and checks cold in
about 1.7 seconds at 0.0039 seconds per line. The rate is below the
0.013193 bar. `hull-closed` gives the criterion at hull parameters. The
whole-tree consumer check passed with exit 0. Section 6 records it.

## 2. DOES `hull-closed` NOW GIVE THE CRITERION AT HULL PARAMETERS?

YES. `hull-closed` at `src/L/Hull.lagda.md:415-426` takes a formula over
`Code`, the hull's own index set, and relabels it into the stage's inner
world with `val`:

```agda
hull-closed : (φ : Formula Code 1) → ⟨ [] AbsL.⊨ᵐ (∃̇ (mapFo val φ)) ⟩
            → ∥ Σ[ a ∈ SL ] (⟨ fst a ∈ˢ Hull ⟩
                           × ⟨ (a ∷ []) AbsL.⊨ᵐ (mapFo val φ) ⟩) ∥₁
```

The old statement took `φ : Formula ⟪ X ⟫ 1` and satisfied it at X
parameters. The new statement takes `φ : Formula Code 1`. The base codes
carry X into the hull, so the X-parameter case is included. The witness `a`
must lie in the hull. This is the Tarski-Vaught criterion at hull
parameters.

## 3. THE THREE FOLLOW-ONS

1. **The junk lemma.** `∅∈Lsetα` at
   `src/L/Hull.lagda.md:317-318` is two lines:
   `Lset-in α ∅ ∅ ∅∈α (∅∈𝒟ₒ ∅)`. Both ingredients were delivered:
   `∅∈𝒟ₒ` at `src/L/Axioms/Basic.lagda.md:490-491` and `Lset-in` at
   `src/L/Constructible.lagda.md:319-320`. The probe's estimate of 10 to
   15 lines priced the whole argument; the tree already carried it. The
   Hull module now takes `∅∈α : ⟨ ∅ ∈ˢ α ⟩` as its third parameter. The
   master builds the junk from `∅` and the lemma. `∅ ∈ˢ α` holds at
   every limit ordinal. The tree has no `isLimit` type, so the master
   states the nonempty-stage hypothesis directly.
2. **The hand-rolled recursion.** The mutual `vals`/`val` at
   `src/L/Hull.lagda.md:83-91` costs four lines. The library `Vec.map`
   is rejected by the termination checker. The hand-rolled recursion
   passes. This matches the probe's finding F2.
3. **The junk split lemma.** `sum-stuck` and `val-wit` at
   `src/L/Hull.lagda.md:99-107` cost six lines. The junk split makes
   `val (wit ...)` opaque. `val-wit` identifies it with the least search
   when a witness exists. The closure needs this equality. This matches
   the probe's finding F3.

## 4. WHAT WAS RE-STATED OVER `Code`

The re-stated statements live in `AtStage.Hull` at
`src/L/Hull.lagda.md:359-413`. Each takes the wit payload
`(k : ℕ) (ψ : Formula (⊥*) (suc k)) (cs : Vec Code k)` where the old
statement took `φ : Formula ⟪ X ⟫ 1`:

- `Witnessed-small`, the small witness in `⟪ Lset α ⟫`.
- `small→big`, the small witness to the big witness in `SL`.
- `big→small`, the reverse.
- `SatAt-h`, the satisfaction predicate the search minimizes.
- `leastSearch`, sealed opaque with `leastSearch-spec` beside it (R-36).
- `leastWit` and `leastWit-spec`, the search value and its leastness.
- `hullVal : Code → S`, the hull's indexing map.

`val : Code → SL` is the code-level least witness. It is total because
the junk value covers the unwitnessed cases.

What had no consumer after the re-index:

- `SatAt`, `SatAt-h` and `Witnessed` over `Formula ⟪ X ⟫ 1`. The closure
  routes through `T.Sat` and `T._⊨₀_` instead.
- `leastVal` and `leastVal-spec`. They were projections of `leastWit`
  with no consumer.
- `Small`, `eL`, `InnerSmall` and `⊨ᵐ-small`. The smallness dressing
  existed to keep the index at `Type ℓ`. The `Code` index is small by
  construction, so the dressing has no consumer.
- `leastWit-in-Hull`. Its role is served by `val-in-Hull`, which is
  `inHull` by construction.
- `XInM`'s formula membership (`φₓ`, `xWit`, `xLeast`, `wₓ`). The base
  code carries `x` in directly, one `subst` over the fiber equality.
- The old `hull-closed` at X parameters. It is re-stated at hull
  parameters.

`small→big` feeds `leastSearch`, and `SatAt-h` is the predicate the search
minimizes. `big→small`, `leastWit`, `leastWit-spec`, `hullVal` and
`Witnessed-small` have no consumer inside the file. The closure uses
`T.closed`, and `X⊆M` uses `inHull`. They are re-stated for the downstream
condensation API, which is what DD27's list demands.

## 5. WHAT `[LJ-1.3]`'s PIECE ONE RETIREMENT ACTUALLY REMOVED

`[LJ-1.3]` booked three standing pieces (`_build/lj-1.3-report.md`
section 6). Piece one was the order element's stage membership:
`⟨ fst (relL β ...) ∈ˢ Lset γ ⟩`, priced at 30 to 80 lines. The old hull
needed it to express the leastness of a witness as an X-formula. The
meta-index hull has no such need. `leastSearch` and `val` pick the least
witness with the meta well-order `orderAt α ordα` directly. No `relL`
element enters the hull's closure. The 30 to 80 line obligation has no
consumer. Nothing delivered was deleted. `OrderAt`, `OrderAtStage`, `φ<`
and `Σ₁-φ<` stand unchanged for the downstream transfers.

## 6. THE NUMBER

The ledger caliber is non-blank lines inside ```agda fences over
git-tracked masters under `src/`. DD26 excludes the two catalogs.

| file | before | after | delta |
|---|---:|---:|---:|
| `src/L/Hull.lagda.md` | 372 | 431 | +59 |

The generic `TermAlgebra` module is 75 in-fence lines. The new hull block
is 93 in-fence lines. They replace the old 109-line index block. The net
is plus 59. DD27's whole-move estimate was about 270 lines: 116 measured
probe, about 30 named follow-ons, about 120 counting. The counting block
is not mine, so the hull side of the estimate was about 146 lines. The
delivered hull side is 168 gross. The net against the replaced block is
plus 59.

The whole-tree consumer check ran `agda src/Everything.lagda.md`, one
process, under the C-12 cap. It re-checked `L.Hull` from scratch and the
whole tree exited 0. No consumer broke.

## 7. SECONDS AND RATE

Protocol: one process, `GHCRTS="-A64m -I0 -M8g"`, cold interface for the
file, warm dependency interfaces, `/usr/bin/time -p`. The first-ever-cold
run measured 3.58 seconds. Three stable runs measured 1.56, 1.66 and 1.69
seconds. One contended run measured 2.50 seconds. The sibling `[LJ-1.21]`
holds the other slot, so the spread is likely contention.

| figure | seconds | rate |
|---|---:|---:|
| stable median | 1.69 | 0.0039 |
| first-cold | 3.58 | 0.0083 |

The bar is 0.013193 seconds per line. Both readings are under it. The
module rate sits between `StageCardinal` at 0.0052 and `FOL.Count` at
0.0011, and better than the old `Hull` at 0.0064.

C-31 framing: the wing's seconds budget is 99.6 to 147.7 seconds over the
PROJECTED 7,553 to 11,197 lines. A per-module flag is advice. The
aggregate is the judgment. This module does not approach the bar on
either reading, so it cannot flip the aggregate.

## 8. IS THE JUNK VALUE FAITHFUL

YES, for the role the internal order played in Devlin's proof. Devlin
forms `ψ(v₀) = φ(v₀) ∧ ∀v₁(v₁ <_L v₀ → ¬φ(v₁))` to make the least witness
the UNIQUE witness (`_build/literature/dev2.txt:1340-1350`). His hull is
the set of uniquely definable elements. The meta-index hull does not need
uniqueness. Its index is the code, not the definable element. The code is
the certificate, so no uniqueness encoding is needed.

## 9. DID YOU MAKE THE COUNTING HARDER

NO. `Code` is the probe's measured shape, unchanged:

```agda
data Code : Type ℓ where
  base : K → Code
  wit  : (k : ℕ) → Formula (⊥* {ℓ}) (suc k) → Vec Code k → Code
```

`wit` carries its arity. The union over the naturals stays internal to
the constructor. `[LJ-1.22]` priced the counting at about 120 lines and
about 2 seconds, with obligations O1 to O4. All four stand as priced.
Nothing in this build changes the cardinal law. The counting block lands
after `[LJ-1.21]` frees `StageCardinal`, exactly as planned.

## 10. DD4: WHAT THE J TOWER SUPPLIES

The generic `TermAlgebra` module at `src/L/Hull.lagda.md:58-142` is the
template. It is parameterized by the structure, the carrier embedding,
the meta well-order, the junk value and the parameter embedding. No type
in the module mentions `Lset`, a stage presentation, or any L content.
That is P-h and P-l as written.

The J tower supplies five things at instantiation:

- its restricted structure, in place of `AbsL.𝒮M`;
- its meta well-order on its stage carrier, in place of `orderAt α ordα`;
- its junk element, the analogue of `∅ ∈ˢ Lset α` at its limit stages;
- `lem`, which every tower already carries;
- its parameter embedding, in place of `inStg`.

`absFo`, `⊨-abs` and `⊨-map` are already structure-generic. The closure
theorem is written once and instantiated twice. The one per-tower leaf is
the junk membership lemma. Each tower proves its own. This is the DD4
move: template content bought once, and the definable well-order drops
out of both towers.

One placement note: the generic module lives inside `L.Hull`. The J
tower will import `L.Hull`'s import cone when it instantiates the
template. The cone is L-heavy. If the J tower needs a lean cone, the
orchestrator can re-home the generic module into its own master. The
brief allowed one new master. I chose none, so the catalog wiring stays
with the orchestrator.

## 11. LITERATURE USED

- `dev/literature/devlin-II5.md:118-132` (section 1.3). Took the
  least-witness role that the junk value replaces. Devlin makes the least
  witness the unique witness with
  `ψ(v₀) = φ(v₀) ∧ ∀v₁(v₁ <_L v₀ → ¬φ(v₁))`.
- `dev/literature/devlin-II5.md:257-270` (section 2.4, Step D). Took that
  the order is required only to pick the least witness. The meta
  well-order answers for that.
- `_build/literature/dev2.txt:1329-1356`. Took Devlin's uniqueness role
  and the "really a result about structures with definable wellorders"
  gloss at `:1327-1328`. Section 8 answers whether the replacement is
  faithful.
- `dev/literature/devlin-errata.md`. NOT read. WHY NOT: `[LJ-1.14]`
  verified it does not cover Chapter II section 5, and the brief rules
  out re-checking it.

## 12. ARCHIVE USED

- `_build/lj-1.18-report.md:32-43` (F2, the termination finding),
  `:106-114` (F3, `sum-stuck`), `:222-229` (F1, the junk lemma),
  `:57-84` (the rate method). Took the shape and the three follow-ons.
  Re-derived, not copied.
- `_build/lj-1.16-review.md:119-171` (section 3) and `:173-240`
  (section 4). Took the fourth shape and why the internal order is not
  needed on the GCH chain.
- `_build/lj-1.16-report.md:23-60` (the three refused shapes) and
  `:92-101` (the rate basis). The meta-index route is the measured
  alternative.
- `_build/lj-1.22-report.md:51-101` (obligations O1 to O4) and
  `:102-129` (the marginal price). Section 9 answers the interaction.
- `_build/lj-1.3-report.md:106-131` (section 6, the three standing
  pieces). Piece one is retired; sections 2, 4 and 5 name what happened.
- `dev/LESSONS.md`, through `scripts/rules.py --for build`. Took P-h at
  `:174`, P-l at `:2305`, P-n at `:2483`, R-35 at `:782`, R-38 at `:829`,
  C-31 at `:1855` and D-10 at `:1316`. R-35 and P-n do not fire: the
  hull's membership certificates are codes, and nothing instantiates at a
  concrete carrier in the hot path.

## 13. WHAT I AM NOT SURE OF

1. The `∅∈α` hypothesis. The Hull module needs a nonempty stage to build
   the junk. The tree has no `isLimit` type, so the master states
   `∅ ∈ˢ α` directly. At every limit ordinal this is dischargeable by the
   standard `ord-tri` argument. A reviewer should confirm the consumer
   accepts this shape.
2. `Witnessed-small` is now `Type (ℓ-suc ℓ)`. The old statement was
   `Type ℓ` because the sett index demanded it. Over `Code` the index is
   `Code` itself, so the level does not matter to the construction. No
   consumer needs the old level. A reviewer should confirm.
3. The re-stated `leastWit`, `leastWit-spec`, `Witnessed-small`,
   `big→small` and `hullVal` have no in-file consumer. They are stated
   at the wit payload. The condensation block may prefer code-level
   forms. `val` is the code-level least witness, so the content is
   present either way.
4. The measurement spread is 1.56 to 3.58 seconds. The sibling
   `[LJ-1.21]` runs Agda on the same machine. The rate is under the bar
   on every reading.
5. The whole-tree check passed with exit 0. Section 6 records it.
6. The catalog prose in `src/Everything.lagda.md:910` and `:983`
   describes the old hull. The description is now stale. I may not touch
   the catalog. The orchestrator rewires it after the audit.

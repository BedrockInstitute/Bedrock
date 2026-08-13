# [L3.31-P2R] The routing fork: is Reduce's `p2` true?

**Verdict: `p2` is FALSE.** Not open, not unproved: false, at an instance whose premises are
satisfied, and the falsity is *stated outright in the corpus* by Devlin. The refutation does not
stop at `p2`. It propagates up to `Reduce`'s first hypothesis `defStage∈J`, up to `DefInJ`'s
`DefFragment`, and all the way to **`Matching` itself** (`Bridge:448-449`), the chapter's named
open hypothesis and the object the whole rud route is aimed at. The per-member reshape the brief
hoped for (R2) is false too, one instance further along.

What survives is substantial and should not be lost in the noise: `p4`/`RudBelow` (the rud tower
inside the constructible tower) is **true and classical**, the class-level statement
`isL x ⟺ isJ x` is **true**, and `BlockPowLim` — P1's corrected target — turns out to be
**exactly the successor step of the only true route**.

**Blast radius, stated first because it is the good news.** `Matching` is *nowhere discharged* in
the tree. It exists only as `Landing.matching` (`SatTable:429`), inside `module Landing`, which is
**instantiated nowhere in `src/`** — the only reference outside its own chapter is a prose comment
in an untracked probe. `StepInL` imports `Bridge` for helpers only (`StepInL:60-61`), never for
`Matching`/`Bridged`/`Reduce`. So **no theorem currently in the tree rests on the false
hypothesis.** What is damaged is the campaign's *target* and the chapter's *prose*, not its
delivered results. An earlier draft of this report said consumers were "proving theorems from ⊥";
that was wrong, and the census (§3) is the correction.

Read-only run. No file under `src/` touched, no Agda invoked, no chapter opened for edit.

**C-1 note on citations.** All `src/` line numbers are against the working tree as read during this
recon. A concurrent polish batch modified `BaseBlock`, `Describe`, `Step`, `StepInL` before it
started and added `DefInJ`, `OrdBlocks`, `Order`, `Realize` to the modified set while it ran, so
line numbers in those files may have drifted since; the named exports are stable and are the
reliable anchor. Nothing here was written outside `_build/`.

---

## 0. The dictionary (repo index ↔ classical index)

Everything below depends on reading the repo's indices correctly, so they are pinned first.

| repo | definition | classical |
|---|---|---|
| `step u` | `⋃ ⁅ u' u , values u ⁆` = `u ∪ {u} ∪ {Fᵢ(a,b)}` (`Step:338-339`) | Jensen/SZ `S(U)`, **one** application of the 16-function basis |
| `Sset (sucV β)` | `≡ step (Sset β)` (`Hierarchy:410`) | `S_{β+1} = S(S_β)` |
| `Sset γ`, `γ` limit | `⋃_{δ∈γ} step (Sset δ)` (`Hierarchy:320`, `Sset-out`) | `S_γ`; and `Jset γ limγ` is this level with `Jset-rud` (`Step:954-957`), i.e. **`J`** |
| `𝒟ₒ A` | `sett (Formula ⟪A⟫ 1) defSet` (`Constructible:212-216`, `Definability:78-115`) | `Def(A)`: **full** first-order definability with a constant per member (parameters), *not* Δ₀ |
| `Lset` | union over `β ∈ α` of `𝒟ₒ (Lset β)` (`Constructible:216`) | Gödel's `L_α` |
| `+ω u` | `⋃ₙ sucIter n u` (`OrdBlocks:91`), a limit (`:172`) | `u + ω` |

So `Sset` is the S-hierarchy on the nose, `Sset` at a limit is a J-level, and `Lset` is Gödel's L.
The literature's dictionary is then fixed by SZ Def. 1.6 (`j-hierarchy.md:19-25`,
`sz-full.txt:216-222`): `J_{α+ω} = rud(J_α ∪ {J_α})`, `J_α = S_α` for limit `α` (SZ I.1,
`j-hierarchy.md:56`), and Devlin VI.2.2 (`dev6.txt:1552-1565`): `J_α = S_{ωα}`,
`J_{α+1} = S_{ωα+ω}`. In Devlin's `α`-indexing our `Sset (ω·2)` is his `J₂`, our `Sset ω` is his
`J₁ = H_ω = L_ω` (`dev6.txt:1577-1578`).

`p2` (`Bridge:742`) therefore reads, at its smallest doubtful instance `β = ω+1`, `γ = ω·2`:

> **`L_{ω+1} ∈ J₂`.**

Both `ω·2 = +ω (+ω ∅)` and its limit certificate are expressible in delivered vocabulary
(`OrdBlocks:91,172`), so the instance is not exotic — it is the second block of the tower.

---

## 1. Question 1 — the crux, settled

### 1.1 The corpus settles it, in one sentence, against the route

Devlin, `_build/literature/dev6.txt:1577-1582`, verbatim (OCR as-is):

> `Will, we have Jo = Lo = 0, of course. And it is easily seen that J1 = Hω = L ω .`
> `In view of these two facts, and our knowledge that J α n On = ωoc and`
> `L α n On = α for all α, one might be tempted into thinking that Ja = L ω α for all`
> `α. This is not the case, however. (The proof that the above equality is false makes`
> `a good little exercise for the reader.) Nevertheless, we do have J α = L α whenever`
> `ωα = α .`

`J_α = L_{ωα}` **is the repo's `Matching`**: at limit `γ = ω·α`, `Lset γ ≡ Jset γ`. Devlin names
it as the tempting error, declares it false, and gives the exact repair — equality holds **iff
`ωα = α`**, i.e. only at ω-fixed points (VI.2.4(ii), `dev6.txt:1689-1695`):

> `2.4 Lemma.` / `(i) L α c : J α ^ L ω α .` / `(ii) J α = L α` `#f ωα = α.` / `(iii) L= U 4`

Read: **`L_α ⊆ J_α ⊆ L_{ωα}`**, equality exactly at ω-fixed points, and `L = ⋃ J_α`. The
sandwich is the truth; the level identity is not.

The corpus's *only* L-into-J membership theorem, Devlin VI.2.3 (`dev6.txt:1583`), is

> `2.3 Lemma. For all α, La c J α and L α , (Lβ | β &lt; α) e Ja+1.`

i.e. `L_α ⊆ J_α` and `L_α, ⟨L_β|β≤α⟩ ∈ J_{α+1}` — membership always **one J-block up**, never at
the same level. Instantiated at `α = ω+1` it gives `L_{ω+1} ∈ J_{ω+2} = S_{ω·(ω+1)+ω}`, which is
above `ω²`, not `ω·2`. No text anywhere in the corpus states `L_β ∈ J_α` for `β > α`; Jensen
explicitly declines the whole L-vs-J question (`jensen-book_sec_2_3.txt:39-48`), SZ never defines
an L-level, Jech has no J-hierarchy.

### 1.2 The paper proof at the smallest instance (mine, from cited ingredients)

Devlin leaves the falsity as an exercise, so here it is done, pinned at `γ = ω·2`. Ingredients,
all cited:

1. `J₂ = rud(J₁ ∪ {J₁})`, `J₁ = S_ω = L_ω = H_ω` — Devlin VI.2.2 (`dev6.txt:1552-1565`), prose
   (`dev6.txt:1577-1578`), SZ Def. 1.6 (`sz-full.txt:216-222`).
2. `rud(U) ∩ 𝒫(U) = Def(U)` for transitive `U` — Devlin VI.1.17 (`dev6.txt:1154-1157`), Jensen
   2.2.14 (`jensen-book_sec_2_2.txt:295`), Jech Cor. 13.8 (`jech13.txt:288-290`), SZ 1.7
   (`sz-full.txt:236-240`). Hence **`J₂ ∩ 𝒫(L_ω) = Def(L_ω) = L_{ω+1}`**.
3. `u ∈ J_α ⟹ Def(u) ⊆ J_α` — Devlin's (\*), `dev6.txt:1614-1620`.
4. Finite truncations of satisfaction **are** members: `f_n^N ∈ M` for each `n < ω` — SZ Prop.
   1.12 (`sz-full.txt:430-436`); Jech, "For any particular `n`, the satisfaction relation `⊨n`
   restricted to `Σn` formulas is formalizable" (`jech13.txt:531-534`).
5. Tarski: full satisfaction for a structure is not definable over it — Jech
   (`jech13.txt:531-534`).

**Claim. `L_{ω+1} ∉ J₂`; equivalently `p2` fails at `β = ω+1`, `γ = ω·2`.**

*Proof.* Suppose `L_{ω+1} ∈ J₂`. `J₂` is rud closed and transitive, so by (3)
`L_{ω+2} = Def(L_{ω+1}) ⊆ J₂`. Let `T = {⌜φ⌝ : (L_ω,∈) ⊨ φ}`, a subset of `ω ⊆ L_ω`. By (4)
every finite truncation `Sat_n` is a member of `Def(L_ω) = L_{ω+1}`, so

  `T = { a ∈ L_ω : ∃Y ∈ L_{ω+1} (Y is a satisfaction class covering a ∧ a ∈ Y) }`

is Σ₁ over `L_{ω+1}` with parameter `L_ω ∈ L_{ω+1}`; all its inner quantifiers are bounded by
`L_ω`. Hence `T ∈ Def(L_{ω+1}) = L_{ω+2} ⊆ J₂`. But `T ⊆ L_ω`, so by (2)
`T ∈ J₂ ∩ 𝒫(L_ω) = Def(L_ω)`: the truth set of `(L_ω,∈)` is definable over `(L_ω,∈)`,
contradicting (5). ∎

Two remarks, both adversarial:

- **The very fact that kills the brief's option (b) is what powers the refutation.** The brief's
  hope was a uniform rud satisfaction making `Def(u)` a single rud image at a fixed offset. The
  corpus is unanimous that satisfaction exists as a *member* only in finite truncations (SZ 1.12
  `sz-full.txt:430-436`; Jensen 2.2.17 witness `g` on `C(t)`, `jensen-book_sec_2_2.txt:653-663`;
  Devlin VI.1.14's build-sequence, `dev6.txt:1054-1063` — in all three the **witness size grows
  with the code**), and full satisfaction is only Δ₁/Σ₁ (`sz-full.txt:480-495`,
  `jensen-book_sec_2_2.txt:577-580`). Those same finite truncations, being members of `L_{ω+1}`,
  are exactly what lets `T` appear at `L_{ω+2}` and refute the level identity. Option (b) is not
  merely unavailable; its unavailability is the mechanism of the refutation.
- **Corroboration.** Devlin's own "the definable subsets appear in a hierarchy **stretched** …
  to ω levels of rank" (`dev6.txt:1532-1537`); `rud(U) = ⋃ₙ Sⁿ(U)` as an essential ω-union in
  every text (`dev6.txt:1361-1365`, `jensen-book_sec_2_3.txt:120-132`, `sz-full.txt:244-258`,
  `jech13.txt:288-290`); Jech's "the number of Gödel-operation steps grows with `φ`"
  (`jech13.txt:279-281`); Devlin's placement of `Def` on the **primitive recursive** side of the
  recursion-schema line (`dev2.txt:2334-2346`, `:2194-2218`); and Mathias WS 14.5 as recorded in
  the project notes, `J_α ∉ rud cl(J_α ∪ {ωα})` (`dev/literature/rudimentary-functions.md:248-250`)
  — a non-membership of precisely this shape.

### 1.3 What else the same instance kills

The refutation is not confined to `p2`. Walking the route's own suppliers downward:

| object | site | instance | status |
|---|---|---|---|
| `Matching` | `Bridge:448-449` | `γ = ω·2`: `L_{ω·2} ≡ J₂` | **FALSE** — Devlin `dev6.txt:1577-1582` verbatim |
| `p2` | `Bridge:742` | `β = ω+1, γ = ω·2` | **FALSE** — §1.2 |
| `defStage∈J` | `Bridge:688-689`, `DefInJ:343-344` | `ζ = ω, γ = ω·2` | **FALSE**, premises satisfied: `L_ω = S_ω ∈ S_{ω+1} ⊆ S_{ω·2}` and `ω ∈ ω·2`, conclusion `L_{ω+1} ∈ S_{ω·2}` refuted by §1.2 |
| `DefFragment` | `DefInJ:308-314` | same `ζ = ω, γ = ω·2` | **FALSE** — `Discharge` (`DefInJ:341-369`) derives `defStage∈J` from it by Δ₀ separation inside the level |
| brief's R2 per-member form (`Lset β ⊆ Sset γ`) | proposed | `β = ω+2, γ = ω·2` | **FALSE** — `T ∈ L_{ω+2} ∖ J₂` by §1.2 |

`defStage∈J` is the sharpest statement of the finding: **its smallest non-vacuous instance is
`ζ = ω`, and it is false there.** Everything above it in `Reduce` inherits that.

Note the ordering: `Matching` is *true* at `γ = ω` (`L_ω = S_ω = H_ω`, `dev6.txt:1577-1578`) and
true at every ω-fixed point (VI.2.4(ii)). It fails first at `γ = ω·2` — the second block. The route
does not run out of road in some exotic region; it runs out one block in.

### 1.4 One correction to the record

`k4-report.md:87-93` exhibits `γ = ω·2`, `ζ = ω+3` as the instance with no limit `δ ∈ γ` holding
`Lset ζ`, and justifies the premises with "under the matching the batch is meant to prove,
`Sset (ω·2) = Lset (ω·2) ∋ Lset (ω+3)`". Since the matching is false, **that instance is vacuous
as stated** — its premise `Lset (ω+3) ∈ Sset (ω·2)` is itself false. K4's finding survives intact
with `ζ := ω`: `L_ω ∈ S_{ω·2}` is true, and no limit `δ ∈ ω·2` holds `L_ω` (the only limit below
is `ω`, and `L_ω = S_ω ∉ S_ω`). The dossier's instance should be re-pointed accordingly; K4's
conclusion (the two-limit index is not derivable from `DefFragment`'s premises) is unaffected, and
its own §1.3(a) remark, "the index the route needs is refuted by the theorem the route is meant to
establish", was closer to the truth than it knew.

### 1.5 What survives, and it is not nothing

- **`p4` / `RudBelow`** (`Bridge:699-711`, `:760-827`): `Sset β ⊆ Lset γ` and `Sset β ∈ Lset γ`
  for `β ∈ γ`, `γ` limit. This is Devlin's `P(α)` verbatim — "if `ν < ωα` then `S_ν, ⟨S_τ|τ≤ν⟩ ∈
  L_{ωα}`" (`dev6.txt:1725-1726`), with the per-step arithmetic `u ∈ L_α ⟹ S(u) ∈ L_{α+5}`
  (`dev6.txt:1700-1713`). **TRUE.** Its suppliers `stepSet∈L`, `values∈L`, `slot∈L`
  (`Bridge:690-696`) and `Lstage₂` survive untouched. The route's `Sset`-side half is sound.
- **`Ldef→J`** (`Bridge:117-131`) and **`defs-in-limit`** (`DefInJ:254-267`): `Lset β ∈ Sset γ ⟹
  𝒟ₒ(Lset β) ⊆ Sset γ`. This is Devlin's (\*) (`dev6.txt:1614-1620`). **TRUE**, and it is the
  engine of every repair below.
- **The class statement** `isL x ⟺ isJ x`: **TRUE** (`L = ⋃ J_α`, VI.2.4(iii),
  `dev6.txt:1689-1695`). Only the level-by-level route to it is false. `bridge-isJ→isL`
  (`Bridge:464-469`) is already available from `p4` without `Matching` at all.
- **`BlockPowLim`** (P1 §3, `l3.31-p1-report.md:184-190`): `IsOrd δ → isLimit δ → Lset ζ ∈ Sset δ
  → 𝒟ₒ(Lset ζ) ∈ Sset (+ω δ)`. This is Devlin VI.2.3's successor step
  (`dev6.txt:1622-1628`, `:1643-1652`), and it is **the successor step of the only true route**
  (§2, R2′). P1's positive half is worth more after this report than before it.

---

## 2. Question 2 — the repairs, designed and priced

### 2.0 The one true statement, and where the price lives

Every honest repair is a route to Devlin VI.2.3. Written in repo vocabulary, the minimal
statement the bridge's live direction needs is

```
Q : (β : S) → IsOrd β → ∥ Σ[ γ ∈ S ] (⟨ isLimit γ ⟩ × ⟨ Lset β ∈ˢ Sset γ ⟩) ∥₁
```

*existentially quantified in `γ`* — no arbitrary `γ`, no `∀`-over-limits. `Q` suffices:
`isL x` gives `x ∈ 𝒟ₒ (Lset β)` for some `β` (`Lset-out`), and `Ldef→J` then lands `x` in the
`Sset γ` that `Q β` supplies. `Q`'s induction splits:

- **zero:** free (`∅∈Sset`, used at `Bridge:746-748`).
- **successor:** `Q ζ` gives a limit `γ` with `Lset ζ ∈ Sset γ`; **`BlockPowLim` gives
  `𝒟ₒ (Lset ζ) = Lset (sucV ζ) ∈ Sset (+ω γ)`**, and `+ω γ` is a limit (`OrdBlocks:172`). Done.
  This step is *exactly* P1's corrected target and needs nothing beyond P2's `SatRelation`.
- **limit:** the wall. `Lset λ = ⋃_{ζ<λ} Lset ζ ⊆ Sset (sup γ_ζ)` is easy; **membership** is not.
  It needs `⟨Lset ζ : ζ ≤ λ⟩` as a *member* of a rud level, which is Devlin's carried sequence
  (`dev6.txt:1583`), and his limit step gets it only from `L_α ∈ Def(J_α)` (`dev6.txt:1670-1678`)
  — i.e. from the **internal definability of the L-hierarchy over a J-level**. Rud levels are
  closed under the sixteen operations, not under the ambient replacement, so the ambient theory
  cannot supply the collection; and the truncation in `Q` must be dropped (a function `β ↦ γ(β)`
  is needed to take the sup), which forces an explicit index tower `ω·β`.

That is the whole price map. Three checks that no cheaper limit case exists were run and all
failed: (i) taking `γ` bigger does not help, the sequence still must be a definable subset of a
level below; (ii) carrying the sequence moves the problem one level up unchanged; (iii) restricting
to ω-fixed points makes the limit case free *there* but still needs `Q` at every `β` below.

**But the limit case is not virgin ground, and this is the report's second surprise.** The tree
already owns most of the pieces, on the *other* side of the house:

- `L/Coding/Sequence.lagda.md:361-364` — **`LsetGraph : Formula S 2`**, the L-hierarchy's graph as
  an **object-language formula** (`∃̇` an approximation defined on the members of the argument,
  each recorded value the `𝒟ₒ` step), with readings `LsetGraph-in/out` (`:372`, `:378`). 138 agda
  lines, delivered.
- `L/Hierarchy.lagda.md` (354 lines) — that formula proved correct against the real tower:
  `Lset-only` (`:333`), `Lset-defines` (`:678`); and **the sequence as a single set**,
  `hierL : (α) → isL α → IsOrd α → S` (`:653`) with `hierL-spec` (`:656`), `IsHier` (`:528`),
  `hier-unique` (`:534`).

So "the L-sequence is definable" is *delivered*; what is not delivered is that it is definable
**over the right carrier**. `LsetGraph` is interpreted at `𝒮ʟ` (`Coding/Sequence:59,61-62`), whose
carrier is the class `L`; the limit case needs it interpreted at `⟪ Sset γ(λ) ⟫`, a rud level. That
is a **localization/absoluteness** obligation, not a new construction — and it looks discharge-able,
because the witnesses the formula existentially quantifies over (the approximations, i.e. `hierL β`
for `β < λ`) satisfy `hierL β ∈ Lset (β+1) ⊆ Lset λ ⊆ Sset γ(λ)` by `q1`, so they are present in
the smaller carrier. That is exactly the shape `L/Absoluteness.lagda.md` and `L/Reflect*` exist for.

**Decisive mini-probe (names the whole R2′ price):** *does `LsetGraph` localize from `𝒮ʟ` to the
carrier `⟪ Sset γ ⟫`, i.e. is `hierL λ` a `DefOf.defSet` over `Sset γ(λ)`?* One statement, against
delivered exports (`hierL-spec`, `LsetGraph-in/out`, `defs-in-limit`), no new chapter. It converts
R2′'s widest band (the limit case) into a number, and it is a day's work.

### 2.1 The table

| # | repair | design | band (non-blank agda) | risk class | buys | kills |
|---|---|---|---|---|---|---|
| **R1** | uniform-Sat / parameter-free `H_ω` codes | recode `Formula ⟪C⟫` to parameter-free `H_ω` codes with a separate evaluation, aiming at `Def(u)` as one rud image at fixed offset | — | — | nothing | **BURIED.** Refuted twice: `p2` is false so no coding reaches it (P1 §1 already showed coding-independence); and the corpus has no uniform rud Sat — witness size grows with the code in all three architectures (`sz-full.txt:487-495`, `jensen-book_sec_2_2.txt:653-663`, `dev6.txt:1054-1063`), `Def` is p.r.-not-rud (`dev2.txt:2334-2346`) |
| **R2** | per-member invariant at the same arbitrary limit (`Lset β ⊆ Sset γ`) | replace level-as-member `p2` by per-member containment, keep `γ` universally quantified | — | — | nothing | **BURIED.** False at `β = ω+2, γ = ω·2` (§1.3). It is `L_{ωα} ⊆ J_α`, the wrong half of Devlin's sandwich (`dev6.txt:1689-1695`) |
| **R2′** | **the reindexed bridge** (mine; the only true route) | drop `Matching`; carry `Q` above with an explicit index tower `γ(β)` (`γ(0)=ω`, `γ(β+1)=+ω γ(β)`, `γ(λ)=⋃`); successor = `BlockPowLim`; limit = localize `LsetGraph` to the rud carrier so `hierL λ` is a `defSet` over `Sset γ(λ)`, then `⋃` (= `F5`) lands `Lset λ` | **naive 1.0–2.4k**: index tower 0.15–0.35k (`+ω` block is 41 lines / 85 with ordinality; this needs `∈-induction` + `⋃`-of-family, both idiomatic — `Constructible:216`, `Ordinal:126`); `Reduce` reshape 0.15–0.3k (against **139** delivered); `DefInJ`/`SatTable` re-type 0.1–0.2k; **limit case 0.6–1.5k** (localization + absoluteness over 492 delivered lines of `Coding/Sequence` + `L/Hierarchy`, *not* a new chapter). **Calibrated 3.0–7.2k** at the project's own measured ×3 (`PLAN.md:848`: the L3.30 trunk estimate is recorded as predating "the probe-price-times-3 calibration this project measured") | **HIGH, and the risk is concentrated in one place.** D-16 (the crossing tax: `𝒮ʟ` → `⟪ Sset γ ⟫` localization is precisely an inner-semantics crossing, and the campaign has stalled at crossings twice), D-15 (the reduction's equivalence test must be re-run at the new index), D-21 (the approximation's target *is* the witness). Note K4's `allCodes∈J`/key-set wall (`k4-report.md` §1.2) is **not** in this path: the limit case reuses `LsetGraph`, not an internal satisfaction table | the unconditional bridge, both directions, at the true index; promotes `BlockPowLim`/P2 from residue to load-bearing step; and cashes `Coding/Sequence` + `L/Hierarchy`, currently used only by the choice chapters | the "no ordinal arithmetic enters" property of `Reduce` (`Bridge:642-644`), a deliberate design virtue |
| **R3** | `BlockPowLim`-threading (level-as-member only where a limit stage sits below holding the carrier) | restrict what `defStage∈J`'s consumers may ask | — | — | nothing **as a repair of `Matching`** | **Not a repair — but not buried either.** `Matching` is false, so a restricted `p2` cannot prove it; R3 correctly refuses to prove a falsehood and therefore delivers nothing at `γ = ω·2`. Its *shape* is right and survives **as a component of R2′**: under the index tower, `γ(β)` is by construction a limit below `γ(β+1)` holding `Lset β`, so R3's side condition is discharged for free. Record it as absorbed, not killed |
| **R4** | **the corrective stop** | (a) state in `Bridge` that `Matching` is false, with the citation and the counter-instance; (b) replace it with the true sandwich `Lset α ⊆ Sset (ω·α) ⊆ Lset (ω·α)` as a *recorded* classical fact; (c) retire `module Bridged`'s dependence on `Matching`, keeping `bridge-isJ→isL` which `p4` already supplies unconditionally; (d) keep `p3`/`p4` and re-export `p4` as the delivered half | **0.15–0.4k**, almost all prose + one re-typing; **negative** on the agda side if `Matching`-dependent code is retired | **LOW.** C-6 applies to the re-typing only | honesty; removes a false hypothesis from the tree; keeps every true asset; releases the P2 dispatch from the critical path | the unconditional `isL → isJ` direction, until a later campaign runs R2′ |
| **R5** | **re-found on `isJ`** (mine, surfaced for completeness) | define the trunk's constructible universe as the J-union (`isJ`), prove ZFC/GCH there, demote the L-vs-J identification to a wing theorem to be proved later by R2′ | not priced here (requires a consumer census of `isL` across `L/Axioms`, `L/Godel`, `L/Choice`) | **MEDIUM-HIGH**, but it is architecture, not mathematics: nothing false is involved | removes the bridge from the critical path entirely, which is where the falsity bites | Gödel-facing pedagogy; the `isL`-shaped statements already delivered would need re-pointing (though `isJ → isL` is free from `p4`, so one direction of every transfer is already paid) |

### 2.2 Why R1 cannot be rescued by the `codeBound` dissolution

The brief notes that `codeBound` (P1's probe) only refutes *codeSet-with-parameters as a block
member*, and that `H_ω` codes sit at offset zero from `ω` up, dissolving it. That is correct and it
does not help: with `p2` false, the target the recoding was aiming at is not merely unreachable by
this coding, it is untrue. P1 already proved the coding-independence (`l3.31-p1-report.md:74-77`);
this report supplies the missing half — the target itself. The two together close R1 permanently.

---

## 3. Question 3 — collateral on the ledger

**The matching target itself.** Not "still true if `p2` is false" — it is the *same* falsehood.
`Matching` at limit `γ` is `J_α = L_{ωα}`, which Devlin names and refutes (`dev6.txt:1577-1582`).
It holds at `γ = ω` and at ω-fixed points only (VI.2.4(ii)). The union-level reading the brief
asked me to verify does **not** save it: at `γ = ω·2` the union `L_{ω·2} = ⋃ₙ L_{ω+n}` contains the
arithmetic truth set `T`, and `J₂ ∩ 𝒫(L_ω) = Def(L_ω)` excludes it. The inclusion that *is* true is
one-directional: `Sset γ ⊆ Lset γ`, which is exactly `p4`'s first component, already delivered.

**P2's `SatRelation` object.** Unchanged under every repair, and *upgraded* under R2′: it is no
longer a residue hanging off a refuted target but the successor step of the only true induction
(`BlockPowLim` = Devlin VI.2.3 successor case). Under R4 it goes idle — still true, still
deliverable, but off the critical path until the bridge is resumed. P1's recommendation 4 ("P2 can
proceed now") stands on the mathematics; whether it should proceed *now* is a scheduling call that
depends on the R2′/R4 fork, not on the object's validity.

**The consumer census (the blast radius, exactly).** `L.Rud.Bridge` is imported in two places plus
the index. `SatTable:68` takes `Matching; module Reduce; ∅∈Lset` and instantiates
`module R = Reduce defStage∈J stepSet∈L values∈L slot∈L` at `SatTable:427`, re-exporting
`matching` (`:429`), `bridge-isL→isJ` (`:432`), `bridge-isJ→isL` (`:435`), `bridge-level` (`:438`)
— **all inside `module Landing (gp : GeneralPow) (slot∈L : …)`** (`SatTable:421-422`), and
`Landing` is instantiated **nowhere** in `src/`. `StepInL:60-61` takes only helpers
(`𝒟ₒ⊆Lsuc; Ltr; Lpair; ValuesInU; suc⁴; empty-⊆; ext-⊆`) and nothing bridge-related.
`Everything:1233` imports for the index. Of `Reduce`'s four hypotheses, `stepSet∈L`
(`StepInL:2419`) and `values∈L` (`StepInL:370`) are **unconditional and true**; `slot∈L` is a
`Landing` parameter discharged by `slot-empty` (`SatTable:390`) when `A ≡ ∅`; only `defStage∈J`
(via `DefInJ:341` `Discharge`, fed `fragment gp`) is the false one. So the falsity is confined to
one hypothesis of one uninstantiated module. **Nothing needs to be un-proved; a target needs to be
re-aimed.**

**The retirement chain (Godel / Coding / Choice).** Nothing in the chain is refuted: those
retirements are against the delivered rud route's replacements, and the delivered replacements at
issue here (`p4`, `Ldef→J`, `Step`, `OrdBlocks`, `SatSets`) are all true. What changes is the
*sequencing*: any retirement that was scheduled on the strength of the bridge closing must be held
until the R2′/R4 fork is ruled, because a retirement justified by a false hypothesis is a
retirement justified by nothing. Concretely: hold any retirement whose stated warrant cites
`Matching`, `p2`, `defStage∈J` or `DefFragment`; proceed with any whose warrant cites `p4`,
`Ldef→J` or the Step/Ops/Images layer.

**The extended-trophy band.** P1 moved the levered GCH band to **18.6–22.4k** by removing the L2
lever's 1.3k phantom saving (`l3.31-p1-report.md:282-291`), against the **21.5k** tripwire. Adding
each repair:

| path | delta | band | vs 21.5k tripwire |
|---|---|---|---|
| R4 (corrective stop) | +0.15 to +0.4k, prose-dominated | **18.8–22.8k** | breaches only at the pessimistic end — unchanged in character from today |
| R2′ naive | +1.0 to +2.4k | **19.6–24.8k** | clears at the optimistic end, breaches from roughly the median up |
| **R2′ at the project's own ×3 calibration** | +3.0 to +7.2k | **21.6–29.6k** | **breaches across the entire band** |
| R5 (re-found on `isJ`) | not priced; an `isL` consumer census is the prerequisite | — | the only path that could *reduce* the band, by deleting the bridge from the critical path |

The arithmetic is the ruling's centre of gravity, and it turns on one number: **the naive R2′ band
is survivable, the calibrated one is not.** That is precisely what the mini-probe in §2.0 decides —
it collapses the limit case's 0.6–1.5k (the widest term, and the one the ×3 is really about) into a
measurement. **Do not fund R2′ before that probe; do not refuse it before that probe either.**

---

## 4. Recommendation

**Primary: R4 now, unconditionally; then the §2.0 probe; then rule on R2′.**

*R4 first, and it is not optional.* The tree carries a **false** named hypothesis presented to the
reader as the chapter's one honest debt ("the identification is the one thing this chapter does not
prove: it is taken here as a hypothesis", `Bridge:432-434`), and the prose teaches exactly the
inference Devlin warns against (`dev6.txt:1577-1582`). Nothing rests on it (§3 census), so this is
cheap and purely corrective: state the falsity with the citation and the `ζ = ω, γ = ω·2`
counter-instance, replace `Matching` with the true sandwich `Lset α ⊆ Sset (ω·α) ⊆ Lset (ω·α)` as a
recorded classical fact, and re-export `bridge-isJ→isL` from `p4` where it belongs — that direction
never needed `Matching` at all. 0.15–0.4k, prose-dominated, low risk. It also *keeps* every true
asset: `p3`, `p4`, `Ldef→J`, `defs-in-limit`, `stepSet∈L`, `values∈L`, the `Step`/`Ops`/`Images`
layer, and P1's `BlockPowLim`.

*Then the probe, before any funding decision.* "Does `LsetGraph` localize from `𝒮ʟ` to
`⟪ Sset γ ⟫`, i.e. is `hierL λ` a `defSet` over `Sset γ(λ)`?" One statement over delivered
exports, a day. It decides the only wide term in R2′'s band, and therefore decides whether the
unconditional bridge is a 1k continuation or a 7k tripwire event. Running R2′ without it would
repeat exactly the mistake this report is about: funding a route before pricing the truth at its
load-bearing step (D-10).

*Then R2′ if the probe is green.* It is the only true route to `isL → isJ`; its successor step is
already mechanized modulo P2's `SatRelation`; and it would convert the campaign's largest liability
into its cleanest theorem while cashing `Coding/Sequence` + `L/Hierarchy`, 492 delivered lines
currently used only by the choice chapters.

**Runner-up: R5 — re-found the trunk on `isJ`.** If the probe is red, or if the owner will not
spend a tripwire on a bridge, the cheapest true campaign is to stop bridging: define the
constructible universe as the J-union, prove ZFC/GCH there, and demote the L-vs-J identification to
a wing theorem. `isJ → isL` is already free from `p4`, so one direction of every transfer is
paid. This is an architecture fork, not a mathematics fork; it is surfaced with a recommendation
against picking it *first*, because it should not be chosen while the probe can still make R2′
cheap. Its prerequisite is an `isL` consumer census across `L/Axioms`, `L/Godel`, `L/Choice`, which
this recon did not run.

**Do not** dispatch R1 or R2 in any form. Both are refuted here. R3 should be recorded as absorbed
into R2′ rather than buried: its side condition is precisely what R2′'s index tower discharges for
free.

**Do not** dispatch R1 or R2 in any form. Both are refuted here, and R3 should be recorded as
absorbed into R2′ rather than buried, since its side condition is what R2′'s index tower
discharges for free.

---

## 5. Method notes and lesson candidates

1. **D-10 fired one level higher than P1 ran it, and caught more.** P1 priced the truth of
   `BlockPow` (the residue) and corrected it to `BlockPowLim`. It did not price the truth of the
   *consumer* — `p2` — nor of the chapter's own named hypothesis, `Matching`. The rule wants
   extending: **when a residue is corrected, re-run the truth check on everything downstream of it
   that was never itself checked**, up to and including the chapter's stated goal. Cost of not
   doing so here: the K2/K3/K4/P1 sequence — four batches — all worked on suppliers for a
   consumer that was false from the start. Every one of those batches' negative findings is, in
   hindsight, a symptom: K2's cofinality, K4's missing two-limit index, P1's refuted absorption.
   **A route that keeps failing to supply an index should be suspected of aiming at a false
   statement.** That is the lesson candidate with the highest value in this report.
2. **The literature check must be run against the goal, not only against the residue.** P1's §2
   asked "is `BlockPow` a theorem anybody has?" — exactly the right question, one object too late.
   Asking it of `Matching` would have surfaced `dev6.txt:1577-1582` in one grep. Rule:
   **before a chapter records a hypothesis it cannot prove, grep the corpus for the hypothesis
   itself.**
3. **A false hypothesis is not a conditional result.** The chapter's framing ("taken here as a
   hypothesis, named once") is exemplary practice *when the hypothesis is true and merely
   unproved*. It has no defence when the hypothesis is false, and nothing in the surrounding
   process distinguishes the two cases. Candidate rule: **a named unproved hypothesis carries a
   corpus citation for its truth, or an explicit "truth unverified" marker, at the site.**
4. **Vacuous refuting instances.** K4's `ζ = ω+3` instance was justified by the very theorem under
   construction, and is vacuous now that the theorem is false (§1.4). Rule: **a refuting instance
   must have its premises witnessed independently of the target**, or it proves nothing.
5. **C-6 was not needed and not used**: no Agda was run. The refutation is classical and its
   mechanization would require Tarski undefinability, which is far outside any sane probe price.
   Recording that honestly matters: **this verdict is a paper verdict, checked against four texts,
   not a machine-checked one.** The one machine-checked half already exists — `Reduce` itself
   derives `Matching` from `defStage∈J`, so the tree already contains the implication whose
   conclusion Devlin refutes.

# LJ-1.401 report: `InjCode` is a proposition, so the least code is DATA

slot: `coder`. Written incrementally (C-22). No commit, no push. I wrote
only in `agents/tasks/LJ-1-401/`. Agda ran under the caliber the program
set on this pane, `GHCRTS="-A64m -I0 -M8g"`, one process at a time, no
heap event.

TARGET: two terms in `agents/tasks/LJ-1-401/Probe401.agda`,
`isPropInjCode` and `sel-code`. W3 names `clause4-isProp` as the widest
unmeasured term and requires it first.

Direction: none. Work was to the brief.

## VERDICT

**GO.** Both obligations typecheck. Exit 0. One Agda process per run.
No heap wall. `IsLeast` was dropped: it is free as `snd got` and the
brief forbids spending a line on it.

- `isPropInjCode` at `Probe401.agda:48-53`
- `sel-code` at `Probe401.agda:57-71`

`sel-code` is one `leastOf` at the code. The truncated input is
`InternalLeastCard.Selected.δ-inj`
(`src/L/Cardinal.lagda.md:257`). The predicate is
`λ F → InjCode (up F) κ δᴸ , isPropInjCode (up F) κ δᴸ`. Nothing is
adapted and nothing is transported.

This gives a CODE as data. It does not give an ambient injection.

## W3. `clause4-isProp`

GO. Clause 4 is a proposition. This ran, and its line count was
recorded, before `isPropInjCode` or `sel-code` was written.

- Term: `Probe401.agda:43-45`
- Type of the clause: `Probe401.agda:39-41`, spelled as
  `src/L/Cardinal.lagda.md:228`
- Exit 0. 0.88 s real. `agents/tasks/LJ-1-401/runs/clause4.out:2`
- Caliber: `GHCRTS="-A64m -I0 -M8g"` (`clause4.out:6`)

Code lines, counted before the two obligations were added:

| term | lines | site |
|---|---|---|
| `clause4` | 3 | `Probe401.agda:39-41` |
| `clause4-isProp` | 3 | `Probe401.agda:43-45` |
| total W3 | 6 | |

The proof is three `isPropΠ` and `snd` of the membership
`fst y ∈ fst b`. `_∈_` is an `hProp`
(`Cubical.HITs.CumulativeHierarchy.Base`), so its `snd` is the
propositionality of the conclusion. The premise
`⟨ pr (fst x) (fst y) ∈ fst F ⟩` does not need its own `isProp`:
`isPropΠ` closes a Π into a proposition for any domain.

Clauses 1 to 3 of `InjCode` are `⟨ _ ⟩` of an hProp by construction
(`src/L/Cardinal.lagda.md:225-227`). Their `isProp` is each conjunct's
`snd`. Clause 4 was the only conjunct whose propositionality had to be
built.

## 1. `isPropInjCode`

Generic. Parameters are `F a b : S`. The term names no cardinal, no
stage and no site.

```agda
isPropInjCode : (F a b : S) → isProp (InjCode F a b)
isPropInjCode F a b =
  isProp× (snd ((F ∷ a ∷ []) ⊨ svAt zero))
    (isProp× (snd ((F ∷ a ∷ []) ⊨ domAt zero (suc zero)))
      (isProp× (snd ((F ∷ a ∷ []) ⊨ injAt zero))
        (clause4-isProp F b)))
```

Site: `Probe401.agda:48-53`. Six code lines. The shape is `isProp×`
three times, then `clause4-isProp`. That is the same three-move product
as `isPropIsLeast` at `src/L/WellOrder/Base.lagda.md:133-134`.

`InjCode` is four conjuncts at `src/L/Cardinal.lagda.md:223-228`. A
product of propositions is a proposition.

## 2. `sel-code`

Sited. It opens `InternalLeastCard` and `SiteBound`. It does not
restate them. The `nonempty` argument is the `Selected` module's own
hypothesis, at its own type
(`src/L/Cardinal.lagda.md:242-243`):

```
∥ Σ[ δ ∈ Mem (Lset β) ] ⟨ Good δ ⟩ ∥₁
```

with `β = SiteBound.β κ` and `Good = InternalLeastCard.Good κ oκ`.

The body is one `leastOf` (`src/L/WellOrder/Base.lagda.md:158-160`):

```agda
got = leastOf (orderAt β oβ) lem
        (λ F → InjCode (up F) κ δᴸ , isPropInjCode (up F) κ δᴸ)
        δ-inj
```

Site: `Probe401.agda:69-71`. The types match:

- `δ-inj` at `src/L/Cardinal.lagda.md:257` is
  `∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) κ δᴸ ∥₁`
- `leastOf`'s input at `src/L/WellOrder/Base.lagda.md:160` is
  `∥ Σ[ a ∈ A ] ⟨ P a ⟩ ∥₁`

`⟨ P F ⟩` is `InjCode (up F) κ δᴸ` because `P F` is that type packed
with `isPropInjCode`.

Return: `fst got , fst (snd got)`. That is the member of
`Mem (Lset β)` and its `InjCode`. The `IsLeast` half is
`snd got` (`src/L/WellOrder/Base.lagda.md:130-131`). It is free. It is
not in the returned type.

## 3. PRICE

Full file, both obligations, exit 0: 1.76 s real.
`agents/tasks/LJ-1-401/runs/full.out:2`. Caliber
`GHCRTS="-A64m -I0 -M8g"` (`full.out:6`). This run was WARM: the
clause-4 run had already built the Constructible cone, and `L.Cardinal`
had a compiled interface.

Code lines of the two obligations:

| term | lines | site |
|---|---|---|
| `isPropInjCode` | 6 | `Probe401.agda:48-53` |
| `sel-code` | 15 | `Probe401.agda:57-71` |
| both | 21 | |

The brief estimated about 20 code lines. The measured count is 21.
Neither `isPropIsLeast` (2 lines at
`src/L/WellOrder/Base.lagda.md:133-134`) nor `nonempty` plus `least`
(5 lines at `src/L/Cardinal.lagda.md:113-117`) is a comparable of size.

What resisted: nothing. The types matched. No weakening.

What the next brief needs: this file does not read the code back to an
ambient injection. That is `[LJ-1.402]`.

Prior measurement, not this task's comparable of size:
`agents/tasks/LJ-1-314/CodeUntrunc.agda:81-86` already has
`isPropInjCode`, and `:99-104` already untruncates a generic coded
existence. `agents/tasks/LJ-1-386/Probe386.agda:253-257` has the same
`isProp`. This task's new term is the sited `sel-code` against
`Selected.δ-inj`.

## W2 (DD4)

`isPropInjCode` is generic. `clause4-isProp` is generic. `sel-code` is
sited: it names `InternalLeastCard`, `SiteBound.β` and `δᴸ`. The sited
term instantiates the generic `isProp` as the `hProp` packing that
`leastOf` demands.

## THE OTHER SITE

NO. The ambient selection at `src/L/Cardinal.lagda.md:117` is not
reachable by the same device.

Reason, at the chapter's own lines:

- The payload of that `leastOf` is `InjP'`, which is
  `∥ ⟪ fst α ⟫ ↪ ⟪ fst γ ⟫ ∥₁` (`src/L/Cardinal.lagda.md:63-67` and
  `:82-83`). The untruncated payload is an injection, a function type.
- The chapter says so: `src/L/Cardinal.lagda.md:132`
  quotes:   -- The witness, an injection, still truncated, still not an hProp.
- `κ-inj` at `:133-134` is that truncated injection, taken as
  `fst (snd least)`.
- `leastOf` demands `P : A → hProp`
  (`src/L/WellOrder/Base.lagda.md:159`). An injection is not an hProp,
  so the ambient site must truncate to enter, and the witness stays
  truncated.

This is a reading of one site (`LeastCardInjL`). It says nothing about
any other site (C-42). No Agda was written for the ambient site.

## ARCHIVE USED

- `archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md`
  Read. `archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md:34`
  quotes: module L.CardinalPredicates {ℓ : Level} where
  Declined: this is the retired bijection-predicate chapter. It does
  not define `InjCode` and it does not run `leastOf`.
- `archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md`
  Read. `archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:4`
  quotes: The cardinal chapter's definitional layer fixed equinumerosity as the
  Declined: this is the retired CSB / Cantor chapter. The live site is
  `src/L/Cardinal.lagda.md:223-258`.
- `archive/dev/JOURNAL-archived.md`
  Read. `archive/dev/JOURNAL-archived.md:1`
  quotes: # Archived journal: the retired route
  Declined: not used. The live obligation is at
  `src/L/Cardinal.lagda.md:223-258`.
- `archive/dev/TASKS-archived.md`
  Read. `archive/dev/TASKS-archived.md:1`
  quotes: # Archived task index: the `L3.32-T` series
  Declined: not used. This task is `LJ-1.401`, not an `L3.32-T` row.
- `dev/ARCHIVE.md`
  Read. `dev/ARCHIVE.md:1`
  quotes: # ARCHIVE.md: the archive registry
  Declined: not used. No module was retired. W4 does not apply.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`
  Used. `dev/literature/truncation-and-selection.md:146`
  quotes: **The constraint the route carries: `P` must be `hProp`-valued.** So `leastOf`
  and `dev/literature/truncation-and-selection.md:148`
  quotes: index is a proposition. **A data payload does not come out.**
  This is why the coded site works and the ambient site does not:
  `InjCode` is an hProp payload, so `leastOf` returns the code as data.
  An injection is a data payload, so it does not come out.
- `dev/literature/devlin-II5.md`
  Read. `dev/literature/devlin-II5.md:129`
  quotes: ψ(v₀) = φ(v₀) ∧ ∀v₁(v₁ <_L v₀ → ¬φ(v₁))
  Used as the classical least-witness guard. `leastOf` is that guard
  (`src/L/WellOrder/Base.lagda.md:158-160`).
  `dev/literature/truncation-and-selection.md:140`
  quotes: (`src/L/WellOrder/Base.lagda.md:131`). **That is Devlin's `ψ` and Jech's
  That line continues at `:141`. It is the identification of `leastOf`
  with Devlin's guard.
- `dev/literature/terms-2026-08.md`
  Read. `dev/literature/terms-2026-08.md:1`
  quotes: # The terminology dossier: fourteen renderings for the owner's ruling
  Declined: translation terms. This task writes no glossary entry.
- `dev/literature/digest.md`
  Read. `dev/literature/digest.md:1`
  quotes: # Digest: the orthodox form of the rud route, pinned from the collected literature
  Declined: the rud-route digest. This probe does not touch rud.

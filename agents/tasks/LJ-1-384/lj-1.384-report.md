# LJ-1.384 report: adversarial review of「every cheap escape is closed」

tier: fable (pi-subagent-mode), the EMERGENCY tier, the owner's one-off
instruction of 2026-08-16 (DD0). Review at MAXIMUM effort (DD25). It lands
nothing. Written incrementally (C-22). No commit, no push. I wrote only in
`agents/tasks/LJ-1-384/`. Agda ran under `GHCRTS="-A64m -I0 -M8g"`, one
process, and I counted the slots with the brief's exact command before every
invocation. The count read 1 before every run (a sibling holds one slot), the
cap is TWO, so I never waited.

TARGET: the orchestrator's sentence, recorded at `dev/PLAN.md:116-117` as
「**Four dispatches on 2026-08-16 closed every cheap escape**」, inside the
debt paragraph that reads「its conclusion is `∥ sq α ∥₁` where `SqShape`
wants the function object」. The target is the SENTENCE, not any one report.

## VERDICT

**ESCAPE-OPEN.**

**One candidate escape stands that none of the five legs covers, that no
dispatch has aimed at, and whose only recorded closure is one INFERRED
sentence that delivered code refutes.** Section 1 names it: the CODED-WITNESS
route. Two of its three legs already sit green in `src/` today
(`Canonical` at `src/L/Cardinal.lagda.md:182-204`, `Small` at
`src/L/Coding/Injection.lagda.md:123-147`). Its third leg is unpriced.
**I am NOT claiming the route works (C-36): I am claiming nobody has looked,
so the word「closed」is unearned.** 「Every cheap escape that a dispatch
AIMED AT is closed」is true and earned. The universal is not.

Two stale letters travel with the verdict, and neither reverses it:

- **`SqShape` is in ZERO files under `src/`. MEASURED**: `grep -rn "SqShape"
  src/` returns no hits; commit `ffb0811` (`[LJ-1.323]`, 2026-08-16) removed
  it. The debt paragraph at `dev/PLAN.md:116` and the brief's THE DEBT both
  still name it. The demander of the function object is the consumer chain
  (`src/L/StageCardinal.lagda.md:396-398`,
  `src/L/BoundedSubset.lagda.md:1388-1391`), not any statement-level shape.
  The debt's SUBSTANCE survives this correction (section 5, premise 1).
- **The brief's「it is weeks old」about `[LJ-1.333]` is FALSE. MEASURED**:
  `[LJ-1.333]` was committed 2026-08-16 (commit `6bd5e26`, today), and
  `src/L/Ordinal/SquareLaw.lagda.md` last changed 2026-08-11 (commit
  `f7314af`). No drift separates the finding from the chapter. Section 4.

## 1. IS THE ENUMERATION OF FIVE COMPLETE? NO

**The claim I make: I NAME an escape none of the five covers. I do not claim
the space is exhausted, and I do not claim the escape works.** Section 1.5
states exactly what my search covered, so the reader can tell「I found one
gap」from「there are no others」.

### 1.1 The unaimed candidate: the coded-witness route

The five legs all fight the truncation at the AMBIENT level: eliminate it
(legs 1 and 5), select through it (legs 2, 3 and 4). **Nobody has asked
whether the witness can be selected as a CODE, by leastness in the sealed
internal order, and read out to ambient data.** The route has three legs:

1. **Internal existence** of a good pairing graph at a band ordinal δ:
   `∥ Σ[ A ∈ Mem (Lset β) ] Good A ∥₁` for a `Good` that codes an injection
   of the square into δ.
2. **Canonical selection of the least code.** DELIVERED. `module Canonical`,
   `src/L/Cardinal.lagda.md:182-204`: from exactly such a mere existence,
   `chosen = leastOf (orderAt β oβ) lem Good h` (`:194-195`) returns the
   least witness AS DATA, with no choice principle. The guard is
   proposition-valued, so `leastOf` applies (`src/L/WellOrder/Base.lagda.md:158-160`).
3. **Ambient read-out of the code.** DELIVERED. `module Small`,
   `src/L/Coding/Injection.lagda.md:123-147`, turns the four `InjCode`
   conjuncts into an ambient function `small : ⟪ fst D ⟫ → ⟪ fst C ⟫`
   (`:144`) with ambient injectivity `small-inj` (`:147`). The probe shape
   is already green in a sibling: `readback : Σ[ F ∈ S ] InjCode F κ δ →
   ⟪ fst κ ⟫ ↪ ⟪ fst δ ⟫`, `agents/tasks/LJ-1-299/NoInj2.agda:107-110`.

**Only leg 1 is missing.** It is internal cardinal arithmetic at the band:
the model's own statement that δ carries a pairing. That is the classical
content of Godel pairing run INSIDE the model, and nothing in the tree states
it today.

### 1.2 The recorded closure of this route is one INFERRED sentence, and it fails

`[LJ-1.375]` section 3.4 is the only place in the five-leg record that names
an internal supply for the band. It closes the door in one sentence, marked
INFERRED and unmeasured (`agents/tasks/LJ-1-375/lj-1.375-report.md:346-349`):
an internal choice set「would still need an external read-out, which is the
same untruncation」.

**The delivered tree refutes the inference at `file:line`.** The read-out of
a coded injection is NOT「the same untruncation」: it is `Small`, delivered
at `src/L/Coding/Injection.lagda.md:123-147`, consumed today by
`L.Absorption:504`, `L.InjChain:426`, `L.CantorBernstein:38`. A coded graph
is single-valued by its `svAt` conjunct, so its read-out is the unique-choice
shape, the digest's ONLY free case
(`dev/literature/truncation-and-selection.md:92-95`, checklist step 2 at
`:291-292`). The obstruction the five legs measured, a DATA payload under a
truncation with no canonical reader, does not apply to a payload whose
witness is unique.

**The literature line the record uses to CLOSE the well-order door is the
same line that names this one.** `dev/literature/truncation-and-selection.md:335-337`:
a canonical injection needs a well-order on the INJECTIONS,「which is what
`<_L` supplies classically and what an ambient function type does not
have」. The five legs read the first half at the ambient carrier
(`[LJ-1.329]`: 35 SWO instances, no function carrier) and stopped. The
second half names the classical supplier, `<_L` on codes, and the tree HAS
it: `phi-less` is delivered and wired (`dev/PLAN.md:1260`, row LJ-1.328),
and `orderAt` is what `Canonical` already selects with. The digest's own
step 6 (`:318-326`) says the missing datum is a symmetry-breaking one on the
WITNESSES: a well-order on codes is exactly that, and `[LJ-1.334]`'s
symmetry refutation of ambient readers does not reach it, because codes are
rigid where carriers are symmetric.

### 1.3 Why no leg covers it

- Leg 1 (wrap) and leg 5 (eliminators) attack ELIMINATION of `∥ sq δ ∥₁`.
  This route never eliminates it: it constructs `sq δ` fresh, from codes.
- Legs 2, 3, 4 attack SELECTION principles (`BandChoice`, `SetChoice`).
  This route assumes none: `leastOf` under LEM is delivered and choice-free.
- The complement finding blocks the delivered canonicalizer, whose
  hypothesis is `Init`'s row 4. This route never touches `Init`.
- The owner's `[LJ-1.369]` ruling refuses an ASSUMPTION. This route adds no
  assumption.

### 1.4 The price, honestly, and the gate probe (D-1, DD8)

**I give no line figure, because no basis exists.** The nearest recorded
price, `[LJ-1.327]`'s「Describe the square law's pairing as a FORMULA,
EXPENSIVE, ABOUT 820, AND DO NOT FUND IT」(`dev/PLAN.md:1259`), priced a
DIFFERENT object: coding `pairomega`'s well-founded recursion. This route
does not code the pairing; it needs internal EXISTENCE, by whatever internal
argument is cheapest, plus leastness. P-l forbids transferring the 820.
**Note also that LJ-1.327's row rests on「a coded square law is consumed by
NOTHING today」, and that premise is stale: the band, `Canonical` and
`Small` together are now a consumer.**

**The widest unmeasured term is leg 1, and its gate probe is:** state, at
ONE band ordinal (the tree's named candidate `+ω ω`,
`src/L/Ordinal/StageArith.lagda.md:41-42`), the internal existence
`∥ Σ[ A ∈ Mem (Lset β) ] Good-pair A ∥₁`, and measure whether the delivered
internal machinery (`orderAt`, `phi-less`, replacement) can produce it, GO
or NO-GO. If NO-GO, this review's candidate dies for one measured reason and
the sentence becomes earned. If GO, the untruncation has a second door with
no new axiom. Either outcome repairs `[LJ-1.375]` section 3.4's INFERRED
sentence into a measurement.

### 1.5 What I searched, and the brief's own candidates

- **Restating `SqShape`: DEAD, MEASURED.** The object left `src/` with
  `[LJ-1.323]` (commit `ffb0811`); the trophy statement carries no `sq`
  hypothesis (`src/L/GCH.lagda.md:54-69`, its comment at `:57-58`). There is
  nothing left to restate. `[LJ-1.365]` section 5: the drop「removed the
  last way to pay it by rewording the statement」.
- **Changing the DESCENT so its conclusion is data: reduces to known-closed
  ground, MEASURED at the suppliers.** The non-initial branch consumes
  `∥ ⟪α⟫ ↪ ⟪δ⟫ ∥₁` as its engine
  (`agents/tasks/LJ-1-301/lj-1.301-report.md:137-141`); every supplier at
  that band offers a truncation (`[LJ-1.332]` control 1). The least-δ device
  returns the least INDEX and never the function payload (digest `:148`;
  `[LJ-1.329]`). INFERRED at the generality: no term proves no OTHER descent
  exists. **The coded route of section 1.1 is exactly the unexamined way to
  make this branch's payload canonical.**
- **A different AMBIENT canonicalizer: NOT CLOSABLE, and the record says
  so.** `[LJ-1.319]`'s ruling records that no in-theory term can refute the
  door (cited at `agents/tasks/LJ-1-333/lj-1.333-report.md:199-201`). Here
  「closed」can never mean more than「none is known」.
- **A decidable or finite property: CLOSED, VERIFIED.** The band's index is
  a telescope at `Type (ℓ-suc ℓ)` (`agents/tasks/LJ-1-375/Probe375.agda:79-82`),
  not `ℕ`, so Exercise 3.19 (digest `:110-113`) does not apply, and `recFin`
  is finite-index only (`[LJ-1.368]`'s library inventory).
- **The supplier-change cure attributed to the archive: the archive itself
  contradicts the attribution.** Section 6, first bullet. The retired route
  did not dissolve the non-initial sites; it left them named and open.
- **Theorem 17 as a weakening: CLOSED at the universal level, MEASURED this
  session.** Section 2.2.

## 2. LEG 2: IS POINTWISE SPLIT SUPPORT PROVABLE HERE?

### 2.1 Proving it IS paying the debt. MEASURED

`pointwise-split-untruncates`, `agents/tasks/LJ-1-384/Probe384.agda:55-58`,
exit 0:

```agda
pointwise-split-untruncates : ((δ : S) → ∥ sq δ ∥₁ → sq δ)
                            → LimitBandT → LimitBand
```

The hypothesis of `[LJ-1.375]`'s `bandchoice-from-pointwise-split`
(`Probe375.agda:142-144`) does not only give `BandChoice`. It gives the FULL
untruncation, the exact debt `[LJ-1.332]` left open. **So leg 2 cannot
reopen as a theorem that is CHEAPER than the front door: the theorem in
question IS the front door.** If pointwise split support is ever proved, the
owner's `[LJ-1.369]` ruling is not circumvented; the debt is simply paid and
`BandChoice` is moot. The brief's fear was structurally right and
economically empty.

Is it provable? By Kraus et al. Theorem 16 (digest `:156-160`), split
support per fiber IS a weakly constant endomap per fiber. The delivered
canonicalizer is refuted on the band by definition (section 4), so the only
routes are a NEW canonicalizer, and the one unexamined canonicalizer is
section 1's coded route. **The two open questions of this review are one
question.** `[LJ-1.383]` is live on a different residue (`dev/PLAN.md:1304`,
the `[LJ-1.338]` ties); nothing here duplicates it.

### 2.2 The Theorem 17 flag, closed. MEASURED

The digest line `:161`,「Theorem 17: a MERELY weakly constant endomap is
enough」, is the line `[LJ-1.373]` skipped and `[LJ-1.375]` flagged
UNMEASURED. I measured its only usable reading shut.

`merely-hasconst-free`, `Probe384.agda:65-67`, exit 0: every merely
inhabited type merely has a weakly constant endomap, by `PT.map` of the
constant map. `universal-split-if-merely-suffices`, `Probe384.agda:69-73`,
exit 0: therefore, if a merely weakly constant endomap sufficed for split
support, EVERY type would have split support. The digest's own section 2.6
records the refutation of that universal form (`:214-221`, on the HoTT
Book's own taboo, whose witness `𝟚` is a set). **So the digested line
cannot weaken the band's supplier obligation for any type: as read, it is
inconsistent with the digest's own section 2.6.** Either the paper's
Theorem 17 carries a hypothesis the one-line digest dropped, or the digest
is wrong at `:161`. **A dispatch funded on that line must re-fetch
arXiv:1610.03346 first. The digest has now misled two tasks and needs its
line 161 annotated** (a repair I do not make: review only).

## 3. `[LJ-1.368]`'s INFERRED UNIVERSAL, ATTACKED

The universal (`agents/tasks/LJ-1-368/lj-1.368-report.md:171-175`):
「INFERRED, and C-36 binds: every path must pass the band's Pi of
truncations, because that Pi is where `sq` enters the delivered chain at
non-initial limits, and `[LJ-1.332]` delivers no other supplier there.」

**At its own scope it survives, and I re-derived it.** In `src/` the
untruncated suppliers of `sq` are exactly `squareω`
(`src/L/InjChain.lagda.md:184`), `Initial.square`
(`src/L/Ordinal/SquareLaw.lagda.md:953`) and `via-col-square` (`:960`),
MEASURED by `grep -rn "→ sq |: sq " src/` excluding `∥` lines; the filter is
literal and a differently spelled supplier would escape it. The truncated
suppliers are exactly two, `:956` and `:963`, both under `Init`, MEASURED by
`grep -rn "∥ sq" src/`. At a non-initial limit the delivered tree supplies
NOTHING, and the only built supplier anywhere is `limit-truncated`
(`agents/tasks/LJ-1-332/ProbeLJ1332A.agda:196-204`), truncated, inside the
Pi. `MustFail368B.agda:42-45` (EXPECTED RED, untouched) marks the goal.

**The defect is the quantifier's domain.** 「Every path」ranges over
assemblies of the DELIVERED chain, and the supporting clause is「delivers no
other supplier」. The step from「no supplier is delivered」to「no path
avoids the truncation」forecloses supplier CONSTRUCTION, which is exactly
where section 1's candidate lives: a coded supplier crosses the band's Pi of
DATA and never meets the truncation. **So the universal is sound where
`[LJ-1.368]` stated it and unsound where the sentence spends it.** The
sentence borrowed a chain-local invariant as a space-exhaustion claim. That
is the same synthesis defect `[LJ-1.375]` and `[LJ-1.376]` measured on the
orchestrator twice today, at a third site.

## 4. `[LJ-1.333]`'s COMPLEMENT FINDING, RE-DERIVED. IT HOLDS

Re-derived against the live chapter, which is UNCHANGED since 2026-08-11
(commit `f7314af`; `[LJ-1.333]` ran 2026-08-16, so「the chapters have
drifted」is FALSE for this file, MEASURED by `git log`):

- `sq` at `src/L/Ordinal/SquareLaw.lagda.md:685-687`. VERIFIED.
- `Init`'s fourth row at `:696-698`. VERIFIED. (`[LJ-1.373]`'s `:697-699`
  is off by one, as `[LJ-1.375]` reported; `[LJ-1.333]`'s citation is
  exact.)
- `InitialCore` takes `noinj²` at `:705-707`, row four verbatim. VERIFIED.
- `exclude` spends `noinj²` at `:876`. `col≤α` spends `exclude` at `:928`.
  `col∈α` closes the collapse at `:931-932`. `via-col-square` demands
  `Init α` at `:960-961`. ALL VERIFIED in the current file.
- The band negates `Init`: `LimitBandT` carries `(Init δ → Empty.⊥)`
  (`agents/tasks/LJ-1-368/Probe368.agda:195`). VERIFIED.
- The machine half re-ran fresh TODAY: `ProbeLJ1333A.agda` re-checked
  against the current interface graph, exit 0, 1.9 s (it holds
  `band-kills-row4` and the four recorded controls).

Semantics of「exact complement」, restated: on the class of infinite
successor-closed ordinals, `Init` and the band differ in row four alone, so
the delivered canonicalizer's domain and the band are disjoint BY
DEFINITION. What the finding never gave, and `[LJ-1.333]` marked so: any
statement about canonicalizers not yet written. Legs 3 and 5 stand on it
soundly. The sentence stands on it one step too far (section 3).

## 5. THE PREMISES, EACH MARKED

1. 「The descent is built and its conclusion is truncated」
   (`agents/tasks/LJ-1-301/lj-1.301-report.md:1`). **VERIFIED.**
   `sq-descent : ... → ∥ sq α ∥₁` read at `Descent.agda:261-263`, and
   re-run under my own hand against today's tree: exit and seconds in
   section 7. `SqShape`, which the debt paragraph still names, is gone from
   `src/` (VERDICT, first bullet).
2. 「The band is the exact complement of the only canonicalizer」
   (`agents/tasks/LJ-1-333/lj-1.333-report.md:1`). **VERIFIED**, section 4,
   with the「only」bounded by its literal grep filter.
3. 「`closes-from-choice` is green」
   (`agents/tasks/LJ-1-368/Probe368.agda:229-236`). **VERIFIED.** Read at
   those lines; exit 0 this session; my own `Probe384` imports `Probe368`
   and checked fresh today, which re-validates its interface transitively.
4. 「`bandchoice-from-pointwise-split` is green」
   (`agents/tasks/LJ-1-375/Probe375.agda:142-144`). **VERIFIED.** Read at
   those lines; exit 0 this session; and STRENGTHENED: its hypothesis gives
   the full untruncation (section 2.1).
5. 「`SetChoice` occurs in zero files under `src/L/`」
   (`agents/tasks/LJ-1-374/lj-1.374-report.md:1`). **VERIFIED FRESH**:
   `grep -rln "SetChoice" src/L/` returns nothing, exit 1, today.

## 6. ARCHIVE USED (DD18)

- **`archive/src/2026-08-09-rud-route/`: READ, two files, and it OVERTURNS
  one recorded reading.** The brief asked how the retired route obtained its
  square law and whether it faced a truncated one. **It faced the SAME
  truncation and retired with the band OPEN.**
  `archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:926`:
  「returns only the truncation `∥ ⟪ α ⟫ ≃ ⟪ κ ⟫ ∥₁`, so the law at the」
  (non-initial ordinals stays named). Its cure delivered the honest bound at
  `Init` ordinals only, with the truncated law as projection, and the
  reduction of non-initial sites to their cardinals stalled on the truncated
  equinumerosity witness.

- archive/src/2026-08-09-rud-route/L/CardinalCount.lagda.md:134:
  「truncation, and a truncated witness cannot supply a function.」

- CONTINUING the bullet above.
  **So `[LJ-1.365]` section 6's reading, that the retired route paid by
  changing the supplier with honest data at initial ordinals and never a
  demand at non-initial ones, is wrong in its second half: the non-initial demand
  remained, undelivered, at retirement.** The archive is not evidence FOR a
  live supplier-change cure; it is evidence the same wall stood there. The
  live tree already inherited the half that worked (`noinj²` is `Init`'s
  row 4).
- **`archive/dev/JOURNAL-archived.md`: READ around `:1630`, and it bears on
  ASSUMING, not on PROVING.** `:1630`:「evidence: a choice principle implies
  excluded middle and would cost the tree's postulate-free claim,」. The
  sentence prices ADDING a parameter; nothing in it claims a selection is
  unprovable, so it does not touch section 1's route, which assumes nothing.
  I also read the T47 record, `:1724`:「and it is FALSE as priced**: to
  CONSUME the truncated hypothesis one must still PROVIDE it at every」.
  That is the retired route hitting the provision-over-a-family wall, the
  live band one route earlier.
- **`archive/dev/DECISIONS-archived.md`: READ row D2, and no truncation
  ruling exists there** (`grep -c "truncat"` returns 0, MEASURED, confirming
  `[LJ-1.368]`). `:30`:「No `postulate` anywhere. LEM (and any
  classical/choice principle) is an explicit parameter; the whole tree is
  `--safe`.」 D2 constrains the FORM of any future spend; it rules nothing
  about proving.
- **`archive/dev/TASKS-archived.md`: READ the square-law rows (`:56`, `:66`,
  `:78`, `:82`), shape only.** `:66`:「| L3.32-T31 | Square law, discharged
  | DELIVERED (transfer blocked) | `_build/l3.32-t31-report.md` |」. The
  retired series delivered under a hypothesis with the transfer blocked,
  which is the shape the live chain now carries; its figures live in
  `_build/` and are not readable today, so I take none.

## 7. RUNS, FLOOR, SLOTS (C-53, C-12)

Empty-file floor: `Floor384.agda`, exit 0, **0.08 s**. Every figure is WARM
(the whole interface chain was already built); P-l forbids pricing any
landing from them. The machine was NOT quiet: 1-minute load 4.09 at the
first run. I measure no check time as a price, so the load damages no
figure. Slot count read 1 before every invocation; cap TWO; one process
mine; cap never raised; no heap exhaustion.

| run | file | exit | real s |
|---|---|---:|---:|
| 1 | `LJ-1-384/Floor384.agda`, the floor | 0 | 0.08 |
| 2 | `LJ-1-384/Probe384.agda`, mine, **GREEN** | **0** | 1.83 |
| 3 | `LJ-1-368/Probe368.agda`, premise 3 | 0 | 1.90 |
| 4 | `LJ-1-375/Probe375.agda`, premise 4 | 0 | 1.75 |
| 5 | `LJ-1-333/ProbeLJ1333A.agda`, re-checked fresh | 0 | 1.91 |
| 6 | `LJ-1-301/Descent.agda`, premise 1, re-checked FRESH | **0** | **260.1** |

### 7.1 The descent re-run

`Descent.agda` re-checked from scratch against today's tree
(「Checking LJ-1-301.Descent」in the log): exit 0, 260.1 s wall at about
99 percent of one CPU, dependencies warm. `[LJ-1.301]` reported 241.9 s cold
at its own load; the two figures are consistent and neither is a landing
price (P-l). The file imports no retired name (`meet-suc` does not occur in
it, MEASURED by grep, against today's retirement commit `d57f392`). **So the
descent premise survives today's `src/` motion, MEASURED.**

## LITERATURE USED (DD18)

`dev/literature/truncation-and-selection.md`, read WHOLE, 363 lines, myself,
as the brief ordered.

USED:

- `:92-95` and `:291-292` (unique choice, the only free case): the read-out
  of a single-valued coded graph is this case, which is why `[LJ-1.375]`
  section 3.4's inference fails (section 1.2).
- `:156-161` (Theorem 16; the Theorem 17 line): section 2. Theorem 16 makes
  leg 2 and the canonicalizer question one question; the `:161` line is
  measured unusable as digested (section 2.2).
- `:214-221` (the universal taboo and its reach): the refutation my
  `universal-split-if-merely-suffices` composes against.
- `:318-326` (step 6, the symmetry the canonical map must break): the coded
  route breaks it with a well-order on WITNESSES, which is what the step
  itself demands.
- `:333-337` (「A canonical injection needs a well-order on the
  INJECTIONS, which is what `<_L` supplies classically」): the digest's own
  naming of section 1's route.
- `:110-113` (Exercise 3.19): the decidable-family candidate, closed.
- `:145-148` (`leastOf` delivers no data payload): why the least-δ device
  cannot cure the descent branch, section 1.5.

WHY NOT the rest: section 1 (the set-theory selection device) is subsumed
here by its Agda form `leastOf`, which I cite directly; section 3.1
(Paulson) cannot state the question; section 3.2 (Matthews and Rathjen)
warns about a constructive L and this tree spends LEM; section 6 told me
which labels are citable. `dev/literature/devlin-II5.md`: NOT re-read; WHY
NOT: `[LJ-1.332]` section 12 and `[LJ-1.333]` section 12 measured its
bearing (Devlin reduces by cardinal arithmetic and never owes the
untruncation), and my question, whether the tree can mimic him INTERNALLY,
is a question about the tree, which sections 1.1 and 1.4 state as a probe.
Kraus et al. arXiv:1610.03346: NOT fetched; WHY NOT: network access is not
assumed here and the decisive fact, that the digest's `:161` reading is
inconsistent with `:214-221`, is measurable from disk, and was (section
2.2); the re-fetch is named as the FIRST step of any dispatch on that line.

## DD4

**Maximize the code the two proofs share, and write it generic.** The axis
(C-46), fixed at `scripts/measure/ledger.py:50`: the AC closure against the
GCH closure. This review lands nothing, so it moves no shared line. Its DD4
content is the judgment the brief asked for on any escape found:

- The `SetChoice` spend would give the two trophies different bills for the
  first time (`[LJ-1.375]`'s DD4 finding, re-confirmed by premise 5). The
  untruncation keeps the bills equal.
- **Section 1's coded route also keeps the bills equal (no new axiom), and
  it CONSUMES shared machinery instead of forking it**: `Small` and the
  coding chapters already serve both wings (`L.CantorBernstein:38`, generic
  over any ZF model since commit `9ae4b04`), and `Canonical`'s `leastOf`
  device is the same device the AC wing's transversal construction rests on.
  On the DD4 axis the coded route is the best-shaped escape yet named: it
  would put the band's cure INSIDE code the two proofs share.
- `[LJ-1.337]`'s empty consumer diff is untouched by everything here.

## WHAT I DID NOT DO

I built no part of the coded route and I refuted no part of it (C-36 binds
both directions). I did not touch `src/`, any sibling's files, or any
EXPECTED RED probe; `MustFail368B.agda` and its siblings stay red and
unedited. I ran no `make` target, no commit, no push, no checkout, no stash,
no reset, no clean. I did not run `make check`.

## GATES RUN ON MY FILES

- `.venv/bin/python scripts/gate/lint-prose.py --check
  agents/tasks/LJ-1-384/lj-1.384-report.md`: recorded below.
- `.venv/bin/python scripts/gate/lint-agda.py --check` on `Probe384.agda`
  and `Floor384.agda`: recorded below.
- No em dash in any file I wrote (grep, 0 hits). ASD-STE100 applies to this
  report; the owner-facing verdict sentence is the orchestrator's to
  translate.

## ORCHESTRATOR NOTE, 2026-08-16

**QUOTE BINDING CORRECTED IN PLACE 2026-08-16 BY THE ORCHESTRATOR, and
only the binding.** `check-dd18-survey.py` binds a quote to the nearest
citation before it, so a second quoted span in the CardinalCount bullet
bound to that citation and failed there. The span quoted `[LJ-1.365]`,
not the archived file. It is now written without quote marks. The
orchestrator's first attempt made this worse by substituting double
quotes, which that regex also matches. **The archived quote is exact and
verified at its line; no word of the review is changed.**

# LJ-1.335 report: where the `sq` band terms land, and the re-plumbing cost

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. Recon. It lands
nothing. Written incrementally (C-22).

## THE ANSWER: NO

**NO. The three untruncated bands CANNOT be supplied to that parameter today.**
**And the brief's premise is FALSE for a reason it did not consider: only TWO of
the three untruncated bands are suppliers. The successor band is a STEP.**

`sq-suc` reads `sq γ` and returns `sq (sucV γ)`
(`agents/tasks/LJ-1-330/ProbeLJ1330A.agda:120-127`). The predecessor `γ` can be
a non-initial limit. **So the successor band consumes the band that is
truncated.** MEASURED, from the type.

**But the narrowing the brief wants IS available, and it costs NO signature
change.** It is a new supplier lemma outside both delivered chapters. Section 4
gives it. **It is not free: its assembly is unbuilt, and one piece of that
assembly does not exist in `src/`.** Section 4.2 names it.

## 0. WHAT THE PARAMETER IS, AND WHERE IT IS SPENT

**The `sq` family has exactly TWO sites in `src/`, and both are unsupplied
module parameters.** MEASURED. The search is
`grep -rn "⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫\|⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫" src/`, which finds the
shape and not the name.

| site | what it is |
|---|---|
| `src/L/StageCardinal.lagda.md:17-19` | the chapter's own module parameter |
| `src/L/BoundedSubset.lagda.md:1388-1391` | `BoundedSubsetAt`'s parameter |

**The second passes the WHOLE family to the first**, at
`src/L/BoundedSubset.lagda.md:1397`, and applies it at `α` alone at `:1410`.

**The family is spent POINTWISE at every infinite ordinal in the descent. This
is the fact that kills a partial supply.** `stage-card-upper` is
`∈-induction step` (`src/L/StageCardinal.lagda.md:565`). `step` calls
`LimitStep` (`:561-562`), and `LimitStep` spends `sq α α∈suc infα` at ITS OWN α
(`:283`). **So the descent needs `sq δ` at every infinite δ in `sucV α₀`, and
`δ` is never restricted to a band.**

**MEASURED: nothing in `src/` consumes either site.**
`grep -rn "BoundedSubsetAt" src/` returns one line, the declaration itself.
`grep -rn "L.StageCardinal" src/` returns the module line, the `Everything`
import, and `BoundedSubset.lagda.md:882` and `:1397`. **So the chain is
`BoundedSubsetAt` to `L.StageCardinal` and it stops.** `[LJ-1.330]`'s
measurement stands unchanged at HEAD.

## 1. THE HOME, PER TERM

**P-k puts a read lemma where its consumers use it. The consumers are the
assembly of section 4, so the homes are chosen for the assembly.**

### 1.1 The transports: `L.Ordinal.SquareLaw`

**Terms:** `transport-sq` (`ProbeLJ1330A.agda:78-88`), `ord-emb`
(`:98-108`), `member-inj→sq` (`agents/tasks/LJ-1-332/ProbeLJ1332A.agda:145-148`)
and `member-inj→sq-ih` (`:152-155`).

**Home: `src/L/Ordinal/SquareLaw.lagda.md`, after `sq` at `:685-687`.**

**Why.** The chapter DEFINES `sq` (`:685`) and `Init` (`:692-699`). It already
imports every name these terms use: `member`, `fiber` and `↪-inj` at `:32`,
`IsOrd` at `:33`, `mem-ord` and `suc-ord` at `:34`, `ord-tri` at `:38`.
**MEASURED: the landing adds ZERO import edges.**

**ONE REWRITE IS REQUIRED, and I state it rather than hide it.** The probes
spell the transports with `_↪_` from `L.Cardinal`. **`L.Cardinal` imports
`L.Ordinal.SquareLaw` at `src/L/Cardinal.lagda.md:22`, so the reverse import is
a cycle.** The cure is free: state the transports with the raw Σ shape that `sq`
itself uses at `:686-687`. No mathematics changes.

**A DEDUPLICATION THIS UNCOVERS, and I did not go looking for it (C-42).**
`ord-emb` exists in `src/` TWICE already, with the same body:
`src/L/BoundedSubset.lagda.md:1370-1379` and
`src/L/StageCardinal.lagda.md:506-515` (`Upper.Emb.emb`). **A landed `ord-emb`
in `SquareLaw` could serve the second one, because `L.StageCardinal` does not
import `SquareLaw` today and would then need one edge. `BoundedSubset` also does
not import it.** MEASURED. **I priced no such move and I do not propose it.**
`_↪_` is defined three times as well: `src/L/Cardinal.lagda.md:47`,
`src/L/StageCardinal.lagda.md:221` and `src/L/BoundedSubset.lagda.md:1043`.

### 1.2 The limit kit: `L.Ordinal.SquareLaw`

**Terms:** `Row4`, `Witness`, `notRow4→merely`, `witness→sq` and
`limit-truncated` (`ProbeLJ1332A.agda:175-204`).

**Home: `src/L/Ordinal/SquareLaw.lagda.md`, after `via-col-truncated` at
`:963-964`.**

**Why.** `Row4` IS the fourth row of the chapter's own `Init` (`:697-699`).
`limit-truncated` states what the chapter's header at `:16-18` calls the
extraction wall. The chapter takes `lem` at `:27`, which `notRow4→merely` needs,
and imports `PT` at `:48`. **MEASURED: the landing adds ZERO import edges.**

**AND I SAY THE HONEST HALF: this term supplies nothing (C-45).** It is
truncated, so it can never discharge the parameter of section 0. It lands as the
exact statement of the residue, and as the target of the untruncation. **If the
orchestrator wants only terms that supply, this one waits.**

### 1.3 The successor step and the assembly: a NEW master

**Terms:** `sq-suc` and `sq-suc-inf` (`ProbeLJ1330A.agda:120-138`), plus the
assembly `sq-below` of section 4, which is UNBUILT.

**Home: a new master, `src/L/Ordinal/SquareBands.lagda.md`.**

**Why it cannot be `SquareLaw`.** `sq-suc` reads `ShiftAbs.shift↪`
(`src/L/Absorption.lagda.md:188-190`), and `L.Absorption` imports
`L.Ordinal.SquareLaw` at `:23` and `L.InjChain` at `:36`. **A cycle. MEASURED**,
and `[LJ-1.330]:253-255` measured it first.

**Why a new master and not `L.Absorption` itself.** `L.Absorption` already
imports everything the assembly needs, so that home costs ZERO new masters
against the new master's ONE. **The argument for the new master is subject and
not size:** `L.Absorption`'s header at `:63-71` says its part 1 builds no
element of L and its later parts internalize the shift. **The band assembly is
ordinal arithmetic and it internalizes nothing.** The argument for
`L.Absorption` is the one master saved. **This is a placement call with a
measured price on both sides, so I give both and take neither** (section 2).

**A THIRD OPTION EXISTS AND IT IS WORSE.** `L.InjChain` holds `squareω`
(`:184-185`) but not `shift↪`, so it would need a new edge to `L.Absorption`,
and `L.Absorption` imports `L.InjChain` already. **A cycle. MEASURED.**

## 2. THE CLOSURE DELTA, PER HOME

**Measured with `ledger.py`'s own `import_graph` and `closure`, re-run with
extra roots.** The script is `agents/tasks/LJ-1-335/probe-closure.py`. It runs
no Agda. The baseline agrees with `ledger.py --reuse` line for line.

**BASELINE, MEASURED at HEAD:** AC closure 73 masters and 17,197 lines. GCH
closure 48 masters and 8,889 lines. SHARED 43 masters and 7,596 lines.

**WHERE THE CHAPTERS SIT TODAY. MEASURED:**

| master | AC closure | GCH closure |
|---|---|---|
| `src/L/Ordinal/SquareLaw.lagda.md` | NO | **YES** |
| `src/L/Absorption.lagda.md` | NO | NO |
| `src/L/InjChain.lagda.md` | NO | NO |
| `src/L/StageCardinal.lagda.md` | NO | NO |
| `src/L/BoundedSubset.lagda.md` | NO | NO |

**HOME 1.1 AND 1.2, `L.Ordinal.SquareLaw`: ZERO masters and ZERO shared lines.**
The master is in the GCH closure already, so the only delta is the term's own
lines: about 32 for the limit kit and about 16 for the transports, from the two
probes' own counts. **SHARED does not move, because `SquareLaw` is outside the
AC closure.**

**HOME 1.3, `L.Absorption` or a new master: ZERO today, and 3 masters and 1,064
lines the day the GCH proof reaches it.** MEASURED, by adding the home as a
second root:

| closure | masters | lines |
|---|---:|---:|
| GCH today | 48 | 8,889 |
| GCH that also reaches `L.InjChain` | 49 | 9,391 |
| **GCH that also reaches `L.Absorption`** | **51** | **9,953** |

**SHARED goes 43 and 7,596 to 44 and 7,632.** The three masters that enter are
`L.Absorption` at 526 lines, `L.InjChain` at 502 and `L.Axioms.Infinity` at 36.

**SO `[LJ-1.326]`'s BOUND IS CONFIRMED AND NOT REFUTED.** `dev/ledger.toml:206-211`
records 51 masters, 9,953 lines, SHARED 44 and 7,632, share 39.1 percent. **I
reproduce all four figures.** The share arithmetic also reproduces: 7,632 over
the union 19,518 is 39.1 percent, against 7,596 over 18,490, which is 41.1
percent today.

**A new master adds ONE master on top of that, at its own line count.** So home
1.3 in `L.Absorption` reads 51 and 9,953, and in a new master 52 and about
9,953 plus 60.

**THE FIGURE THAT DWARFS ALL OF THEM, AND THE PROJECT SHOULD SEE IT.** The
chapter this whole leg serves is outside both closures. **A GCH closure that
reaches `src/L/BoundedSubset.lagda.md` is 84 masters and 28,463 lines, and
SHARED is 71 masters and 16,972 lines.** That is 36 masters and 19,574 lines
above today, of which `L.Condensation` alone is 6,718. **So the 1,064 lines of
`L.Absorption` are 5 percent of what the GCH side owes at this one edge.**
`dev/ledger.toml:204` says the closure understates. **MEASURED: at this edge it
understates by about 19,574 lines and not by about 1,028.**

## 3. THE CONSUMER, AND WHY A PARTIAL SUPPLY FAILS

### 3.1 The parameter is a Π, and Agda accepts no part of a Π

**The parameter at `src/L/BoundedSubset.lagda.md:1388-1391` is one Π over δ.**
There is no `Init δ`, no successor hypothesis and no limit hypothesis in it.
`[LJ-1.332]:107-118` measured the same. **A caller supplies a total function or
supplies nothing. There is no third state.**

### 3.2 The successor band is a STEP and not a supplier. MEASURED

**This is the brief's premise, and it is FALSE.**

| band | delivered or built term | is it a supplier? |
|---|---|---|
| δ ≡ ω | `squareω : sq ω`, `src/L/InjChain.lagda.md:184-185` | **YES**, and it is delivered |
| `Init δ` | `via-col-square : (α : S) → Init α → sq α`, `src/L/Ordinal/SquareLaw.lagda.md:960-961` | **YES**, and it is delivered |
| successor δ | `sq-suc : ... → sq γ → sq (sucV γ)`, `ProbeLJ1330A.agda:120-127` | **NO. It CONSUMES `sq γ`** |
| non-initial limit δ | `limit-truncated : ... → ∥ sq α ∥₁`, `ProbeLJ1332A.agda:196-204` | **NO. It is truncated** |

**So the count is two suppliers, one step and one truncation, and not three
suppliers and one gap.** The two suppliers are BOTH already in `src/`. **Landing
them changes nothing, because they are landed.**

**AND THE STEP DEPENDS ON THE TRUNCATED BAND.** `sq-suc` at `sucV γ` needs
`sq γ`. A general γ is a non-initial limit as often as not. **The only supplier
there is truncated. So the successor band cannot be closed while the limit band
is open.** MEASURED, from the two types.

### 3.3 A four-band induction returns the TRUNCATED family, not the family

**Assemble the four bands by `∈-induction` and the result is `∥ sq δ ∥₁`,
because one branch is truncated.** `[LJ-1.332]` built that branch and measured
its cost: `noninit-branch`, recorded at `ProbeLJ1332A.agda:253-279`, ran 400
seconds and was interrupted, against 2 seconds for the same mathematics under
an untruncated hypothesis (`[LJ-1.332]` section 4.1).

**And a pointwise-truncated family does not close the consumer.**
`[LJ-1.333]` fed the delivered module exactly that and Agda named `sq` itself:
`∥ sq δ ∥₁ !=< (Σ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ...)`
(`agents/tasks/LJ-1-333/lj-1.333-report.md`, section 2.3). **The route from the
truncated family to the honest one is a choice principle over the site's
members, stated as `ACBranch` at `ProbeLJ1333A.agda:109-111` and never
assumed.**

### 3.4 What the consumer needs re-plumbed: NOTHING

**MEASURED: the consumer needs no re-plumbing at all for the route this report
recommends.** The parameter stays a Π. The supply comes from a lemma OUTSIDE
both chapters. **The diff to `src/L/BoundedSubset.lagda.md` and
`src/L/StageCardinal.lagda.md` is EMPTY.**

## 4. THE SHAPE OF A PARTIAL SUPPLY

### 4.1 The lemma that turns a family into a band

**This is the narrowing the brief asked for, and it is real.** It is a supplier
whose only open hypothesis is the limit band.

```agda
-- in a NEW master, src/L/Ordinal/SquareBands.lagda.md
SqBelow : S → Type (ℓ-suc ℓ)
SqBelow α = (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → sq δ

-- the ONE band that stays open, stated in the descent form the probe used
LimitBand : Type (ℓ-suc ℓ)
LimitBand = (δ : S) → IsOrd δ → ⟨ ω ∈ˢ δ ⟩
          → ((γ : S) → ⟨ γ ∈ˢ δ ⟩ → ⟨ sucV γ ∈ˢ δ ⟩)
          → (Init δ → Empty.⊥)
          → ((β : S) → ⟨ β ∈ˢ δ ⟩ → IsOrd β → ⟨ ω ∈ˢ β ⟩ → sq β)
          → sq δ

sq-below : (α : S) → IsOrd α → LimitBand → SqBelow α
```

**The caller writes `L.StageCardinal {ℓ} lem α ordα (sq-below α ordα ???)` and
the `???` is ONE band and not a family.** That is「one unsupplied family」to
「one unsupplied BAND」, and it touches no delivered signature.

**`LimitBand` is `limit-truncated` with the truncation removed**
(`ProbeLJ1332A.agda:196-204`). So the open obligation after this lands is
exactly the untruncation `[LJ-1.332]` isolated, and nothing else.

### 4.2 What `sq-below` costs, and the one piece `src/` does not have

**The assembly is `∈-induction` over δ with four branches.** Three ingredients
are delivered or built:

- `∈-induction`, `src/V/Hierarchy.lagda.md:177-180`, universe polymorphic.
- trichotomy against ω, `ord-tri`, used for the same purpose by the delivered
  descent at `src/L/StageCardinal.lagda.md:537` and `:544-546`.
- the four band terms of section 3.2.

**THE PIECE THAT IS MISSING: a successor-or-limit dichotomy on ordinals.**
**MEASURED ABSENT.** The searches are
`grep -rn "IsLimit\|isLimit\|IsSucc\|isSucc\|limit-or\|suc-or-lim\|Split" src/`,
`grep -rn "≡ sucV\|pred\b\|predecessor" src/` and
`grep -rni "limit ordinal" src/`. **Every hit is a different subject:**
`L.Choice.Limit`'s `Split` is a satisfaction predicate at `:479-480`,
`StageCardinal`'s `class-pred` at `:319-320` is a class, and `L.Absorption`'s
`≡ sucV` lines at `:232` and `:274` are the shift graph. **The filter is
literal and it would miss a differently spelled statement.**

**`[LJ-1.332]` said the same from its own side:「`Split` at
`ProbeLJ1332A.agda:234-236` is a HYPOTHESIS in my file, not a theorem」**
(section 6).

**AND THE DELIVERED DESCENT NEVER NEEDED IT, which is why nobody built it.**
`src/L/StageCardinal.lagda.md:493-497` says so:「The union step is generic, so
one step serves both successor and limit ordinals」. **The `sq` assembly cannot
copy that, because its three suppliers are band-specific.**

**Two smaller pieces are also absent. MEASURED**, by
`grep -rn "isPropInit\|sucV-inj\|sucV-injective" src/`, which returns nothing:
`isProp (Init δ)`, which `lem` needs to decide the `Init` branch, and the
injectivity of `sucV`, which the dichotomy needs to read the predecessor out of
a truncation. `isPropIsOrd` exists at `src/L/Constructible.lagda.md:144`, so
`isProp (Init δ)` is a short assembly of delivered parts.

**THE ESTIMATE, ONE NUMBER WITH ITS BASIS (DD8): about 120 code lines.** The
basis is a delivered comparable plus two probe measurements. The comparable is
`Upper` at `src/L/StageCardinal.lagda.md:498-566`, which is the SAME shape, an
`∈-induction` over a family in `sucV α₀` with a per-member branch: **59
non-blank non-comment lines, MEASURED.** The two probe terms are 25 and 32 code
lines, measured by their own authors. So 59 plus 57 is 116, and I round to 120.

**WHAT THE ESTIMATE DOES NOT COVER, and P-l is why I say it.** The dichotomy has
NO comparable in `src/`, so no measured cure transfers to it. **Its lines are
NOT in the 120.** The check TIME is not priced either. **I ran no Agda in this
task, so I measured no second of it.** `[LJ-1.332]` measured 400 seconds for the
truncated variant of this same assembly, and 2 seconds for the untruncated one.
**The recommended shape is the untruncated one, so the 400 seconds is not its
price, but nothing here proves the assembly is cheap.**

### 4.3 The band-split parameter, priced, and I STOP

**A band-split PARAMETER is the other shape, and it touches TWO delivered
signatures. That is the orchestrator's call and not mine, so I price it and
stop.**

It would replace the Π at `src/L/BoundedSubset.lagda.md:1388-1391` and the Π at
`src/L/StageCardinal.lagda.md:17-19` with `LimitBand`. **Both, because the
second is where the family is spent** (`:283`).

**THE PRICE, MEASURED:**

1. **`L.StageCardinal` would have to reconstruct `sq` from the band, so it would
   import `L.Absorption`. Its closure goes 30 masters and 4,533 lines to 52 and
   10,997. That is plus 22 masters and plus 6,464 lines**, and it puts the whole
   L-internal absorption machinery inside the stage-size chapter.
2. **The reconstruction is the same `sq-below` of section 4.1.** So the shape
   buys nothing that section 4.1 does not, and it pays a signature change and a
   closure jump for it.
3. Two delivered chapters change signature, and `BoundedSubsetAt` has no
   consumer to validate the change against.

**RECOMMENDATION: section 4.1, not this. And the decision is not mine.**

## 5. THE ABORT CRITERION, ANSWERED ROW BY ROW (D-1)

| the brief's row | outcome |
|---|---|
| **A HOME EXISTS FOR EACH TERM AND YOU NAME IT** | **TAKEN.** Section 1 names three homes, section 2 prices each, section 3.4 says the re-plumbing is empty. **I landed nothing** |
| **THE CONSUMER CANNOT TAKE A PARTIAL SUPPLY** | **TAKEN, at `src/L/BoundedSubset.lagda.md:1388-1391` and `src/L/StageCardinal.lagda.md:283`.** The parameter is a Π spent pointwise across the descent. **And the deeper reason is section 3.2: the successor band consumes the truncated band** |
| **THERE IS NO CONSUMER AT ALL** | **TAKEN, and unchanged from `[LJ-1.330]`.** `BoundedSubsetAt` has no consumer in `src/`, MEASURED. **This is a DD13 question and section 6 states it** |
| **THE RESTATEMENT MOVED THE TARGET** | **NOT TAKEN.** `src/L/GCH.lagda.md` is a statement of 70 lines and it names no `sq`, so it neither wants nor refuses these terms. `grep -rn "SqShape" src/` returns nothing. **The consumer that wants them is `L.StageCardinal`, and its parameter is unchanged** |

## 6. THE DD13 QUESTION, STATED AND NOT ANSWERED

**`src/L/BoundedSubset.lagda.md` is 1,409 code lines with no consumer in `src/`,
and `L.StageCardinal` is 482 more whose only consumer is that chapter.**
MEASURED. **Landing all four bands would give the chapter a supply that still
nothing consumes** (C-45).

**I do not propose retiring anything.** DD13 says to price the ideal form
written fresh today, and that is a rewrite-side question with a real budget. **I
name it because the brief's third abort row ordered me to say so if the chapter
is unreached, and it is.**

## 7. DD4, STATED AND ANSWERED, WITH MY AXIS (C-46)

**DD4: maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker. DD4's axis is AC against GCH, fixed at
`scripts/measure/ledger.py:50`.

**MY AXIS: does the LANDING keep the terms tower-blind, and which closure pays?**

**Answer: every home keeps the terms tower-blind. MEASURED, from the homes' own
import lists.**

- `L.Ordinal.SquareLaw` names no `Lset`, no `Formula` and no `⊨`. Its `L.`
  imports are `L.Constructible` for `IsOrd` (`:33`), `L.Ordinal` (`:34`),
  `L.Ordinal.Linear` (`:38`), `L.Choice.Finite` (`:39`) and `L.WellOrder.Base`
  (`:40`). **So homes 1.1 and 1.2 keep the property their authors measured.**
- The new master of home 1.3 would name `ShiftAbs` and `squareω` only. Its own
  statements name `S`, `IsOrd`, `ω`, `sucV`, `sq` and `Init`. **The TERMS stay
  tower-blind. The CHAPTER they read does not:** `L.Absorption` is a chapter
  about elements of L. **So the term is generic and its supplier is not, and
  that is the honest reading.**

**WHICH CLOSURE PAYS: the GCH side pays, and the shared core barely moves.**
SHARED goes 43 masters and 7,596 lines to 44 and 7,632, which is one master and
36 lines, and that master is `L.Axioms.Infinity`. **The share FALLS 41.1 to 39.1
percent while SHARED RISES. Read the SHARED row and never the share**
(`dev/ledger.toml:198-200`).

**AND THE UNDERSTATEMENT IS LARGER THAN THE LEDGER'S NOTE SAYS.**
`dev/ledger.toml:204` says the GCH closure is read from a statement whose proof
is not wired. **MEASURED at this edge: reaching `L.BoundedSubset` costs 36
masters and 19,574 lines, against the 1,028 the note bounds.** The note's bound
is correct for the two debt terms it measured. **It is not the bound for the
chapter.**

## 8. WHAT I DID NOT SETTLE

I name these rather than guess.

1. **Whether a UNIFORM step exists that avoids the dichotomy.** The delivered
   `Upper` has one (`src/L/StageCardinal.lagda.md:493-497`). **I did not look for
   one for `sq` and I did not refute one. C-36 binds.**
2. **The dichotomy's own price.** No comparable exists in `src/`, so P-l forbids
   an estimate by analogy and I give none.
3. **Any check time.** **I ran no Agda.** Every second in this report is quoted
   from a sibling's table and is theirs, not mine.
4. **The `ord-emb` deduplication.** I measured three copies. I priced no move.
5. **The sweep (C-42).** I swept for the `sq` SHAPE and found two sites. **I did
   not sweep `src/` for other unsupplied Π-indexed module parameters, and I claim
   no count.**
6. **Whether the orchestrator should land `limit-truncated` at all.** It supplies
   nothing. Section 1.2 gives both readings.

## 9. THE PROPOSED DIFF, WHICH I DID NOT APPLY

**Three files change. `src/L/BoundedSubset.lagda.md` and
`src/L/StageCardinal.lagda.md` do NOT.**

**A. `src/L/Ordinal/SquareLaw.lagda.md`, after `sq` at `:687`.** Add
`transport-sq`, `ord-emb` and `member-inj→sq`, from
`ProbeLJ1330A.agda:78-108` and `ProbeLJ1332A.agda:145-155`, **restated with the
raw Σ shape of `:686-687` in place of `_↪_`** (section 1.1). No import changes.

**B. `src/L/Ordinal/SquareLaw.lagda.md`, after `via-col-truncated` at `:964`.**
Add `Row4`, `Witness`, `notRow4→merely`, `witness→sq` and `limit-truncated`,
from `ProbeLJ1332A.agda:175-204`. No import changes.

**C. `src/L/Ordinal/SquareBands.lagda.md`, NEW.** Header
`module L.Ordinal.SquareBands {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where`. Imports:
`L.Ordinal.SquareLaw {ℓ} lem` for `sq`, `Init`, `via-col-square` and the
transports; `L.InjChain {ℓ} lem` for `squareω`; `L.Absorption {ℓ} lem` for
`module ShiftAbs`; `L.Ordinal {ℓ}` for `ω-ord`, `suc-ord` and `#∈ω`;
`L.Ordinal.Linear {ℓ} lem` for `ord-tri`; `V.Hierarchy {ℓ}` for `∈-induction`
and `∈-irrefl`; `V.Model {ℓ}` for `self∈sucV`. Contents: `sq-suc` and
`sq-suc-inf` from `ProbeLJ1330A.agda:120-138`, then `SqBelow`, `LimitBand` and
`sq-below` from section 4.1. **`sq-below` is UNBUILT and it is the funded work.**

**D. `src/Everything.lagda.md`.** One import line for the new master, with its
catalog entry. **The orchestrator wires it. I never touch that file.**

**Option: replace C by an addition to `src/L/Absorption.lagda.md`.** It saves one
master and mixes two subjects. Section 1.3 gives both sides.

## 10. PROHIBITIONS, ANSWERED

- **Writes: `agents/tasks/LJ-1-335/` only**, two files, this report and
  `probe-closure.py`. Nothing in `src/`, nothing in `dev/`, no other task
  directory, no `.claude/`, no `AGENTS.md`.
- **I read the sibling probes and reports and changed no line of them.**
- **No Agda.** The brief preferred none and none was needed. **So I counted no
  slots, because I started no process.**
- **No commit, no push, no `make check`.** No `git checkout`, `stash`, `reset`
  or `clean`. I ran `git log` and `grep` only.
- `.venv/bin/python scripts/gate/check-probes.py`: clean, 3,154 tracked files.
- `.venv/bin/python scripts/dispatch/rules.py --for recon`: run, every statement
  read. I opened the full `dev/LESSONS.md` entries for the laws I acted on.
- MEASURED: no em dash in either file I wrote.

## 11. ARCHIVE USED (DD18), ONE LINE READ PER FILE

- **`agents/tasks/LJ-1-330/lj-1.330-report.md`, READ WHOLE.** Line read
  `:253-255`:「`sq-suc` reads `L.Absorption`. `L.Absorption` imports
  `L.Ordinal.SquareLaw` at `:25` and `L.InjChain` at `:36`. So `sq-suc` cannot
  live in `L.Ordinal.SquareLaw`」. **TOOK: the cycle, and I re-verified it at
  `src/L/Absorption.lagda.md:23` and `:36`.** The line numbers moved by two and
  the fact holds.
- **`agents/tasks/LJ-1-332/lj-1.332-report.md`, READ WHOLE.** Line read
  `:383-385`:「The successor-or-limit dichotomy. `Split` at
  `ProbeLJ1332A.agda:234-236` is a HYPOTHESIS in my file, not a theorem. The
  full four-band assembly needs it」. **TOOK: the missing piece, and I measured
  that `src/` does not have it either.** That is section 4.2.
- **`agents/tasks/LJ-1-333/lj-1.333-report.md`, READ section 2 whole.** Line
  read, section 2.4:「The blocker is not the shape of the conclusion. It is the
  shape of the DESCENT. A propositional conclusion untruncates a FIXED number of
  data points. It does not untruncate a family indexed by the site」. **TOOK:
  the reason a truncated family cannot close the consumer**, which is section
  3.3.
- **`archive/dev/TASKS-archived.md`, SHAPE ONLY, never a claim.** Line read
  `:78` (L3.32-T43):「Where counting calls the square law | RED (wall
  confirmed)」. **TOOK, SHAPE ONLY: the retired route also spent a dispatch on
  the placement of the square law and returned RED. WHAT WOULD NOT TRANSFER:**
  that route's modules are under `archive/src/`, and its report lives in
  `_build/`, so no figure of it is readable today and I quote none.

## 12. LITERATURE USED (DD18)

**No mathematical literature bears on where a delivered lemma is placed.** This
task measured an import graph and a module parameter, and a type checker or a
graph settles both. **NOT READ, and WHY NOT: `dev/literature/devlin-II5.md` and
`dev/literature/truncation-and-selection.md`.** `[LJ-1.330]` and `[LJ-1.332]`
already spent the first on the mathematics of the bands, and the second bears on
the untruncation, which is not this task.

## 13. THE RULES THIS CHAIN EARNED, ANSWERED

- **C-44. The brief warned about its own premise.** **The premise is FALSE and
  section 3.2 refutes it from the types.** The successor band is a step, so only
  two of the three untruncated bands are suppliers, and both are already
  delivered.
- **D-10. Price the truth of a recorded residue before pricing its proof.** I
  priced the truth of「three bands can be supplied」first. It is false. **Then I
  priced the shape that IS true, in section 4.1.**
- **C-40. Verify the CONSUMERS of a changed file, never the file alone.** I
  measured both consumers of the family, at `:1397` and at `:283`, and the fact
  that the second spends it pointwise. **A reading of `BoundedSubsetAt:1410`
  alone would have said the family is used once at α, which is FALSE.**
- **C-42. A refutation measures the site it names.** I swept for the `sq` shape
  and found two sites. **I did not sweep for other unsupplied families and I
  claim no count.**
- **P-l. A measured cure does not transfer by analogy.** Section 4.2 marks the
  400 seconds as the truncated variant's price and not the recommended shape's,
  and it leaves the dichotomy unpriced because no comparable exists.
- **C-45. `exit 0` is not a supply.** Section 1.2 and section 6 say plainly that
  the landed terms supply a hypothesis that nothing consumes.
- **D-1.** The abort criterion was fixed before the run and section 5 answers it
  row by row.

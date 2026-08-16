# LJ-1.374 report: does the delivered tree depend on `SetChoice`, and does the L side?

tier: pi (pi-subagent-mode), model `glm-5.3`. RECON. It lands nothing.
Written incrementally (C-22). No commit, no push. I wrote no file outside
`agents/tasks/LJ-1-374/`. I ran Agda only under `GHCRTS="-A64m -I0 -M8g"`,
one process per run, and I counted the slots before every run.

## FINDING

**L-DOES-NOT.**

The L side takes `SetChoice` nowhere, MEASURED two ways: no L chapter names it
or imports its chapter, and no L chapter supplies a choice instance through any
other door. The L tower takes `LEM (ℓ-suc ℓ)` as its one classical parameter
and PROVES its choice field. The V side takes `SetChoice (ℓ-suc ℓ)` at exactly
one site, `V ⊨ ZFC`, and the tree prices that assumption in the open. So the
two towers differ on exactly this interface, and the owner has a clean
question. `[LJ-1.373]`'s instance claim is confirmed by my own re-derivation,
GREEN.

## 1. The L side: every site

**Direct use: NONE. MEASURED.** `grep -rn "SetChoice\|Base.Choice\|ChoiceLemma"
src/L/` returns zero hits, exit 1. The whole L closure of 71 masters was
enumerated by `find` and grepped. No L chapter imports `Base.Choice`, names
`SetChoice`, or names `ChoiceLemma`.

**The L tower's one classical parameter is LEM. MEASURED.** All twelve
`src/L/Choice/` module headers take exactly `{ℓ : Level} (lem : LEM (ℓ-suc ℓ))`
and nothing else: `Adequate:29`, `Before:45`, `Faithful:39`, `Finite:61`,
`Internal:39`, `Limit:40`, `Name:35`, `Order:42`, `Stage:42`, `Step:44`,
`Table:41`, `Transversal:50`. The root does the same:
`src/L/Model.lagda.md:45`, `module L.Model {ℓ : Level} (lem : LEM (ℓ-suc ℓ))`.
The GCH statement chapter does the same: `src/L/GCH.lagda.md:10`.

**The L tower PROVES choice, it does not assume it. MEASURED.**
`src/L/Model.lagda.md:98-99` assembles `L⊨ZFC = record { zf = L⊨ZF ; hasChoice
= hasChoiceL L⊨ZF }`, and `hasChoiceL : (zf : isZFModel) → ChoiceStatement zf`
is a proved term, the transversal construction, at
`src/L/Choice/Transversal.lagda.md:382-383`. The chapter's own recap records
the status, `src/L/Model.lagda.md:109`: "The root stands, and it stands
unconditionally: `L⊨ZFC`, the constructible structure models ZFC, from the
excluded-middle interface and nothing else. **Every field of ZFC is a theorem
rather than a hypothesis**, choice included."

**The one subtlety, read rather than discarded (C-57).** Twenty-one L chapters
import `V.Model`, for named V lemmas only (`∈sucV-elim`, `self∈sucV`,
`pair-singleton`, `module Power`; full list from grep, sites
`src/L/Axioms/Basic.lagda.md:45` through `src/L/Condensation.lagda.md:24`).
`V.Model` imports `Base.Choice` at `src/V/Model.lagda.md:28`, so the chapter
`Base.Choice` IS inside the L tower's transitive import closure. This is code
organization, not logical dependence:

- `V.Model` is parameter-free, `src/V/Model.lagda.md:24`.
- The only consumers of a `SetChoice` value in the whole tree are
  `ChoiceLemma`'s module parameter, `src/V/Model.lagda.md:453`, and `V⊨ZFC`'s
  function argument, `src/V/Model.lagda.md:528`. MEASURED: `grep` finds
  `ChoiceLemma` nowhere outside `src/V/Model.lagda.md`, and `V⊨ZFC` nowhere
  outside `src/V/Model.lagda.md` and `src/Landmarks.lagda.md:54-55`.
- `open import ... using (...)` does not re-export, so `SetChoice` is not even
  in scope inside the importing L chapters.

INFERRED, from that import structure and no deletion test, because `src/` is
forbidden: every L proof would typecheck with the choice half of `V.Model`
deleted. No `SetChoice` instance is ever supplied, anywhere in `src/`, for any
proof. MEASURED: the string `SetChoice` occurs in `src/` only in
`Base/Choice.lagda.md` (definition and use), `V/Model.lagda.md` (import and
the two parameter sites), `Landmarks.lagda.md` (re-export), and prose in
`Everything.lagda.md` and `README.md`.

## 2. What status the tree gives `V ⊨ ZFC`

**It is a trophy, and it is delivered conditionally. Both, at once.**

- TROPHY: `V⊨ZFC` stands in the trophy case, `src/Landmarks.lagda.md:54`, whose
  preamble says each landmark "restates a milestone theorem of the book in one
  self-contained signature, with its full bill of assumptions on display"
  (`:6-9`). A paper can cite it.
- CONDITIONAL: the signature is `V⊨ZFC : ∀ {ℓ : Level} → SetChoice (ℓ-suc ℓ) →
  isZFCModel (𝒮ᵥ {ℓ})`. The assumption is the trophy's displayed price, and
  the tree says so in three places: `src/V/Model.lagda.md:426-427`, "The
  excluded middle does not prove choice, so upgrading to ZFC costs a genuinely
  new assumption: the choice chapter's `SetChoice`" (the brief's "a real new
  assumption" quote); `src/V/Model.lagda.md:521-524`, "One choice, at the
  model's own truth level, is the entire price of `V ⊨ ZFC`"; and
  `src/Base/Choice.lagda.md` intro prose, "choice is never assumed globally: a
  chapter that needs it takes it as a parameter, and the first to do so is
  Part 3's summit".

So, plainly: yes, `V ⊨ ZFC` is delivered as a function of `SetChoice
(ℓ-suc ℓ)`. The project's headline is NOT `V ⊨ ZFC`, though. The first goal,
`README.md:22-27`, is `L ⊨ GCH`, "a semantic theorem internal to the host",
and the charter endpoint, `archive/dev/DECISIONS-archived.md:29` (D1), is
Con(ZF) → Con(ZFC + GCH) under one relativization. Every classical landmark in
the case is conditional on something: `V⊨ZF` on `LEM (ℓ-suc ℓ)`
(`src/Landmarks.lagda.md:48`), `V⊨ZFC` on `SetChoice (ℓ-suc ℓ)` (`:54`),
`L⊨ZFC` on `LEM (ℓ-suc ℓ)` alone (`:76`). The case holds exactly one
choice-priced trophy today, and it is V's.

## 3. `SetChoice`, and `BandChoice` as an instance

The interface, `src/Base/Choice.lagda.md:54-56`:

```agda
SetChoice : ∀ ℓ → Type (ℓ-suc ℓ)
SetChoice ℓ = (X : Type ℓ) → isSet X → (B : X → Type ℓ)
            → ((x : X) → ∥ B x ∥₁) → ∥ ((x : X) → B x) ∥₁
```

The band, `agents/tasks/LJ-1-368/Probe368.agda:226-227`:
`BandChoice = LimitBandT → ∥ LimitBand ∥₁`, a selection from a truncated
family.

**Re-derived by me, GREEN.** `agents/tasks/LJ-1-374/Probe374.agda`, exit 0,
2.97 s, floor 0.72 s, slots 0 before the run:

```agda
band-is-instance : SetChoice (ℓ-suc ℓ) → BandChoice
band-is-instance sc t =
  PT.map secAt (sc BandTel tel-set fiberAt (inhAt t))
```

The spelling is mine, not `[LJ-1.373]`'s, and it is pinned twice: `inhAt`
must match `LimitBandT`'s telescope and `secAt` must match `LimitBand`'s
(`Probe374.agda`, PART 1 pinning sites), so a wrong telescope refuses. I also
re-ran `[LJ-1.373]`'s own artifact today: `Probe373.agda`, exit 0, 1.65 s.
Both greens agree with `[LJ-1.373]`'s measurement.

**What the green measures.** `SetChoice (ℓ-suc ℓ)` gives `BandChoice`. The
whole distance is one `isSet` proof on the band's index telescope plus two
universe lifts. No other mathematical content separates the band from the
interface. **What it does not measure (C-36, and `[LJ-1.373]` marked the
same):** the converse. Nothing proves `BandChoice` is AS STRONG as `SetChoice
(ℓ-suc ℓ)`. So "an exact instance" is true in the measured direction:
sufficiency, with no residue. The literature standing behind this, per
`[LJ-1.373]`'s whole-file survey of `dev/literature/truncation-and-selection.md`,
`:219-221`: a principle of this shape "is therefore not refuted by the
standard taboo, and it is also not proved. **It must be ruled on.**"

So the premise chain holds: the band bottoms out at the same interface, at the
same level, that `V ⊨ ZFC` already spends. `[LJ-1.373]` said it,
`dev/PLAN.md:1263`: "The band bottoms out at the interface the tree prices for
V to ZFC."

## 4. The GCH trophy's statement, if it took the same interface

The delivered statement, `src/L/GCH.lagda.md:59-70`, carries no hypothesis
beyond the model and κ itself; the file's own comment at `:57` reads "No
hypothesis remains beyond κ itself". The ruled capstone, `[LJ-1.323]` section
1.3, is `L⊨GCH : GCHStatement L⊨ZF`.

Two forms, both TYPECHECKED as types, no inhabitant built or claimed
(`Probe374.agda`, PART 2, same green run):

```agda
-- Form A: the LEM bill stays, the choice bill is added beside it.
L⊨GCH-form-A = SetChoice (ℓ-suc ℓ) → GCHStatement (L.Model.L⊨ZF lem)

-- Form B: V⊨ZFC's own pattern.  One instance pays both bills.
L⊨GCH-form-B = (sc : SetChoice (ℓ-suc ℓ))
             → GCHStatement (L.Model.L⊨ZF (choice→lem sc))
```

Form B mirrors `V⊨ZFC` exactly, `src/V/Model.lagda.md:528-531`, where
`base = V⊨ZF (choice→lem ac)`: one choice instance pays the LEM bill through
the proved `choice→lem` (`src/Base/Choice.lagda.md:285`) and the selection
bill through the interface itself. Form B is the cleaner spelling: the
hypothesis list of the trophy SHRINKS to one entry, and that entry is the same
entry, at the same level, that `V⊨ZFC` takes.

**What it costs the reader.** The reader who cites the GCH landmark must now
supply one choice instance at the model's truth level, where today the reader
supplies one LEM instance. Choice is strictly stronger in reach:
`choice→lem` is proved, and the tree's own boundary prose records that the
excluded middle "does not return the favour" (`src/V/Model.lagda.md:426`,
`src/Base/Choice.lagda.md` closing prose). So yes, honestly: this puts an
unsupplied hypothesis back on a trophy, which is the exact thing
`[LJ-1.323]` section 7.2 ruled against, "A trophy with an undischarged
hypothesis claims a conditional Goedel's theorem, which is less than the
project's endpoint", and it is the event class `[LJ-1.323]` section 6.3 names
as the only thing that would return `sq` to the statement. The owner's
standing ruling on the band form of the same cost, `[LJ-1.369]`,
`dev/PLAN.md:1262`: "BandChoice is admissible only if PROVED; an undischarged
hypothesis stays off the trophy". `[LJ-1.373]` added its own warning: assuming
the interface that implies `BandChoice` "is the same cost under a wider name".

**The fact this recon adds to that ruling:** the precedent already stands in
the same trophy case, at the same level and the same interface, by design and
priced in the open: `V⊨ZFC` at `src/Landmarks.lagda.md:54`. Taking the
interface for GCH would make L's trophy the second consumer of one public
price, not the first assumption of its kind in the tree. Whether that
admissibility transfers from V to L is the owner's call, not mine.

## PREMISES CHECK

1. "`V⊨ZFC` takes `SetChoice (ℓ-suc ℓ)`, at `src/Landmarks.lagda.md:54`."
   VERIFIED, `src/Landmarks.lagda.md:54` and `src/V/Model.lagda.md:528`.
2. "`BandChoice` is an exact instance of it, per `[LJ-1.373]`." VERIFIED by my
   own re-derivation, `Probe374.agda:band-is-instance`, exit 0, and by
   `[LJ-1.373]`'s artifact re-run green. Exact in the sufficiency direction;
   the converse is not measured (C-36).
3. "The L towers prove `L ⊨ AC` rather than assuming choice." VERIFIED,
   `src/L/Model.lagda.md:98-99` with `src/L/Choice/Transversal.lagda.md:382-383`,
   and the recap prose at `src/L/Model.lagda.md:109`.
4. The premise the orchestrator flagged as most at risk, "the L side takes
   `SetChoice` nowhere": TRUE as to assumption, MEASURED. Refined, not
   refuted: `Base.Choice` sits in the L tower's transitive import closure
   through `V.Model`, with no instance ever supplied. Section 1 gives both
   layers at `file:line`.

## ARCHIVE USED

- `archive/src/2026-08-09-rud-route/`: GREPPED for an ambient choice
  principle. MEASURED: no archived chapter imports `Base.Choice` or names
  `SetChoice` in code, exit 1; the only mentions are prose in its
  `Everything.lagda.md:67`, quoted: "- `Base.Choice`{.Agda}: the boundary's
  second interface: set-level choice". Its own `L/Choice/Transversal.lagda.md`
  also PROVED the choice field. TOOK: the retired route made the same fork the
  delivered tree makes, so the V-with-choice, L-without split is not an
  accident of the current route.
- `archive/dev/JOURNAL-archived.md:1630`: the retired reason for refusing
  choice, quoted: "evidence: a choice principle implies excluded middle and
  would cost the tree's postulate-free claim,". TOOK: the refusal was about
  the postulate-free claim, and the delivered tree keeps that claim by pricing
  choice as a parameter, which is exactly what `V⊨ZFC` does.
- `archive/dev/DECISIONS-archived.md:30` (D2), quoted: "No `postulate`
  anywhere. LEM (and any classical/choice principle) is an explicit parameter;
  the whole tree is `--safe`." TOOK: the standing ruling on ambient choice,
  and it is satisfied by both towers today. Also read `:29` (D1) for the
  endpoint's wording.
- `archive/dev/TASKS-archived.md`: SHAPE ONLY, `:78`, the T43 row, "RED (wall
  confirmed)". TOOK: the retired series recorded one status row per dispatch.
  No claim taken.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: NOT re-surveyed, per the
  brief. `[LJ-1.373]` read it whole, 363 lines, and measured that a selection
  of this shape is an axiom, not a theorem, digest `:219-221`, which I read
  myself for the quote in section 3. TOOK: the standing verdict only. WHY NOT
  a fresh survey: DD28 rules the survey belongs to the provability probe that
  already ran, and this task asks what the tree does, which is a grep and a
  read.

## DD4

Stated: maximize the code the two proofs share, and write it generic. **The
axis is the selection interface itself, `Base.Choice`, upstream of both
towers** (C-46).

Today the sharing is asymmetric: V consumes the interface (`V⊨ZFC`,
`ChoiceLemma`), and L consumes nothing from the chapter, MEASURED. So
"`Base.Choice` is upstream of everything, so whatever it supplies is shared by
construction" is shared only in the weak sense: one generic statement exists,
and one proof uses it.

If the GCH trophy took the interface, the sharing would become real but
bounded. The wrap idiom, `PT.map section (sc index index-set fiber inh)`, and
the levelling `lowerSetChoice` are generic today and would serve both
consumers verbatim, one generic wrap, two instantiations, zero per-tower code.
That is a DD4 win at the glue level. The mathematical cores stay different:
V's `ChoiceLemma` is choice sets via `∩` and extensionality, the band is a
selection over a telescope, and no code is shared there. The assumption,
though, is spent twice at the same level, and a shared axiom is a shared COST,
not a shared proof. Verdict: a real but small DD4 win at the interface and its
glue, and a shared cost at the assumption level. Nothing here is a reason to
prefer either form of section 4; the owner prices that.

## Machine and process discipline

- Slot count before every run, by the brief's exact command: 0 of 2, three
  times. One Agda process per run. `GHCRTS="-A64m -I0 -M8g"`, cap never
  raised. No heap exhaustion. MEASURED.
- Floor, `Floor374.agda`: exit 0, 0.72 s. Probe, `Probe374.agda`: exit 0,
  2.97 s after one failed first run, 10.30 s, whose only error was my own
  Part 2 spelling, `[NoSuchModule] No module L.Model in scope` at a `let
  module`; Part 1 was already green in that run. `[LJ-1.373]` re-run,
  `Probe373.agda`: exit 0, 1.65 s.
- Writes: `lj-1.374-report.md`, `Floor374.agda`, `Probe374.agda`, all in
  `agents/tasks/LJ-1-374/`. Agda wrote interface files into `_build/2.8.0/`
  under the declared class. No edit outside the directory. No commit, no
  push, no `make check`, no worktree command. `agents/tasks/LJ-1-375/` was
  read for existence only and written nowhere.
- Lint: `.venv/bin/python scripts/gate/lint-prose.py --check` on the report,
  exit 0; `.venv/bin/python scripts/gate/lint-agda.py --check` on both Agda
  files, exit 0. No em dash in any written file.

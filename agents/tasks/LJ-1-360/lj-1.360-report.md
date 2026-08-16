# LJ-1.360 report: the `hasWitnessAt` restatement, priced

tier: pi (pi-subagent-mode), model `glm-5.3`. PROBE, lands nothing. Written
incrementally (C-22). Every negative is MEASURED or INFERRED, in those words.

## 0. LEAD

**ONE LINE: the honest restatement SUPPLIES the bound, at about 8 insertions
at the coding substrate, 2 edited lines at the chain's `out` and about 3 at
the bounded mirror, and the 43 SURVIVES as the telescope share of a repair
that now totals about 54 to 56, with ONE unmeasured term left under it: the
BACK direction at the chain, whose closest candidate the bounded form offers
was refused, `MustFail360.agda`, EXPECTED RED, exit 42.**

**THE RESTATED PREDICATE IS `hasWitnessAt+` (`agents/tasks/LJ-1-360/Probe360.agda:96-99`),
the delivered body right-extended with ONE conjunct: every member of the
witness is a key with a numeral arity, `∀̇∈ (var zero) (arityNumAtL zero)`.**
That is Devlin's bounded-quantifier doctrine ported onto the one existential
the port itself added, and it is the SAME conjunct the chapter already states
for single elements (`arityNumAtL`, `src/L/Coding/CodeSet.lagda.md:185-187`).

**THE SUPPLY IS MEASURED, NOT ARGUED.** `Probe360.agda:109-115`, **exit 0 in
3.60 s**: from `⟨ γ ⊨ hasWitnessAt+ A x ⟩` the site's destructuring yields the
witness with the arity bound in the fourth slot, which is exactly the type
`[LJ-1.350]`'s `MustFail350.agda` measured UNSUPPLIED from the old three
(`no-supplier`, exit 42 there). `Probe360.agda:136-142` then composes it with
`[LJ-1.350]`'s five-line cure and produces the 28 telescopes' LAST CONJUNCT at
every member of the witness. **The miniature answers the brief's third question
YES, and the yes is a green file.**

**THE SUPPLIER IS MEASURED TOO, AND IT IS CHEAP.** The closure still satisfies
the restated predicate: the new conjunct costs **5 lines**
(`Probe360.agda:179-183`), the mirror of `closureShaped`'s map over
`closure-inv` (`src/L/Coding/Shape.lagda.md:646-649`), which walks the same
members and asks more of them. `witnessAt-in`'s restatement is ONE more tuple
slot.

**THE CONSUMER DIFF IS EMPTY AT BOTH NAME-LEVEL CONSUMERS, MEASURED BY READING
EVERY ONE.** `Powerset.lagda.md` and `Faithful.lagda.md` consume
`hasWitnessAt` only through `witnessAt-in` and `witnessAt-out` by name, and
those keep their signatures. Zero lines change in either file. This is the
third empty consumer diff on this chain, after `[LJ-1.337]` and `[LJ-1.342]`.

**AND THE PRICE HAS A SECOND HALF THE BRIEF DID NOT FORESEE.** The chain's
`WitnessAgree.back` produces `hasWitnessAt` FROM the bounded form, and under
the restatement it must produce the new conjunct too. The bounded form's own
facts do not supply it: `agents/tasks/LJ-1-360/MustFail360.agda`, **EXPECTED
RED, exit 42 in 2.45 s**, refused at `MustFail360.agda:65.18`, and the error names
the gap exactly, the twelve-fold `shapesBS` disjunction against the
`arityNumAtL` body with `∈̇ con ωʟ`. **So the bounded form needs the mirrored
conjunct, about 3 lines, and whoever supplies the bounded form then owes the
mirrored conjunct's supply. That supplier is outside this probe's fence and is
the widest unmeasured term left under the 56.**

**COST.** Fourteen agda invocations, longest 3.60 s. No wall. No heap
exhaustion. The cap was never raised. Nothing landed in `src/`.

## 1. THE ANSWER TABLE

| claim | verdict | basis |
|---|---|---|
| the restated predicate supplies the arity bound at every member | **YES, MEASURED** | `Probe360.agda:109-115`, exit 0 |
| the supply plus the cure gives the telescopes' last conjunct | **YES, MEASURED** | `Probe360.agda:136-142`, exit 0 |
| the closure still satisfies the restated predicate | **YES, MEASURED** | `Probe360.agda:188-196`, exit 0 |
| the new conjunct costs five lines at the producer | **YES, MEASURED** | `Probe360.agda:179-183` |
| the restated predicate is inhabited at a real point | **YES, MEASURED** | `Probe360.agda:288-289`, closed term |
| the Powerset consumer changes | **MEASURED FALSE** | section 3, zero lines |
| the Faithful consumer changes | **MEASURED FALSE** | section 3, zero lines |
| the chain's `out` changes | 2 edited lines | section 3, `Condensation.lagda.md:6713-6716` |
| the chain's `back` can produce the new conjunct from the bounded form's own facts | **MEASURED FALSE** | `MustFail360.agda`, exit 42 |
| the cheap candidate supplies the arity bound | **MEASURED FALSE** | it supplies a carrier membership of `w` only, section 2.3 |
| the 43 survives | **YES** | it prices the telescopes; the restatement is a separate item, section 5 |
| `[LJ-1.350]`'s quoted line numbers are current | **PARTIAL: two off by one at the tail** | section 6 |
| Devlin states the witness as the bounded set itself | **NOT IN SO MANY WORDS** | digest read, section 10 |
| the retired route restated the witness step this way | **MEASURED FALSE** | it carried `hasWitnessAt` unchanged and stopped at the shape machinery, section 9 |
| anything landed in `src/` | **MEASURED FALSE** | `git status --short`, section 12 |
| a run hit a wall | **MEASURED FALSE** | longest 3.60 s, section 7 |

## 2. QUESTION 1: WHAT `hasWitnessAt` SAYS TODAY, AND WHAT THE CANDIDATES SAY

**All line numbers below were re-derived today (C-44).**

### 2.1 Today

`src/L/Coding/CodeSet.lagda.md:240-242`:

```agda
hasWitnessAt : ∀ {n} → Fin n → Fin n → Formula S n
hasWitnessAt A x = ∃̇ ((var (suc x) ∈̇ var zero)
                      ∧̇ (closedAt zero ∧̇ shapedAt zero (suc A)))
```

The witness is an UNBOUNDED existential: any set `w` with the argument inside,
`w` closed, `w` shaped at the carrier. The chapter's own prose says this is
deliberate at the class model (`CodeSet.lagda.md:14-19`, quoted by
`[LJ-1.348]` section 2.1).

### 2.2 Candidate 1, the honest restatement, as a type

`Probe360.agda:96-99`, and the form I price for landing:

```agda
hasWitnessAt+ : ∀ {n} → Fin n → Fin n → Formula S n
hasWitnessAt+ A x = ∃̇ ((var (suc x) ∈̇ var zero)
                        ∧̇ ((closedAt zero ∧̇ shapedAt zero (suc A))
                           ∧̇ ∀̇∈ (var zero) (arityNumAtL zero)))
```

The witness is no longer any set carrying the body: its EVERY MEMBER is a key
whose arity component is a numeral. The body is right-extended, so every
delivered destructuring pattern gains one slot at the right end and nothing
else moves. Two renderings were considered and one is unavailable:

- **Naming the concrete bounded set as a constant**, the literal reading of
  「the witness IS the bounded set」: the carrier-dependent constant cannot be
  spoken under the carrier-slot binder, which is the chapter's own recorded
  reason the carrier is a slot (`CodeSet.lagda.md:29-33`). **MEASURED FALSE as
  an option by reading the chapter's own prose; no term was built.**
- **Binding the member quantifier**, the rendering above: speakable at a slot,
  and its supplier is `closure-inv` plus `arityNumAtL-in`, both delivered.

### 2.3 Candidate 2, the cheap restatement, as a type, and why it is the control

`agents/tasks/LJ-1-348/Refute348.agda:338-346`, verified verbatim today:

```agda
  witK-bounded : (u : S) → ⟨ fst u ∈ fst (lookup A γ) ⟩
               → ⟨ (u ∷ γ) ⊨ ((var (suc xi) ∈̇ var zero)
                    ∧̇ (closedAt zero ∧̇ shapedAt zero (suc A))) ⟩
               → ⟨ fst u ∈ fst (lookup Ki γ) ⟩
```

It adds a CARRIER MEMBERSHIP of the witness to `witK`'s telescope. It
typechecks there and `[LJ-1.348]` measured it has NO supplier at the site
(`MustFail348.agda`, exit 42). **It also supplies NOTHING for the arity bound,
and that is measurable by reading what it adds: a membership of `w` itself
says nothing about the MEMBERS of `w`.** `[LJ-1.350]`'s countermodel already
measures the separation: its container is in the bound and shaped, and its
member's arity is refuted at the same code (`Cure350.agda:126-130`). **So the
cheap candidate does not meet the 28 telescopes' need, and I price it as the
control only, exactly as the brief orders.**

## 3. QUESTION 2: THE COST, IN LINES AND IN CONSUMERS

**The sweep. `grep -rn "hasWitnessAt" src/` returns 19 hits. I read every one,
plus every hit of the spelled body text `(var (suc x) ∈̇ var zero)` and
`closedAt zero ∧̇ shapedAt` over `src/`, so the sweep is by NAME and by TEXT.**

| file, site | line | kind | change under candidate 1 |
|---|---|---|---|
| `CodeSet.lagda.md`, `hasWitnessAt` | `:240-242` | the definition | **+1 line** (the conjunct) |
| `CodeSet.lagda.md`, `witnessAt-in` | `:365-373` | producer | **+1 tuple slot + 5-line `clo-arity`, MEASURED** (`Probe360.agda:179-183`) |
| `CodeSet.lagda.md`, `witnessAt-out` | `:375-397` | decode consumer | 1 line edited (the spelled body in `viaSlot`'s type, `:393`); the decode term unchanged, more hypotheses never hurt it |
| `CodeSet.lagda.md`, `witness-in`/`witness-out` | `:401-415` | pinned pair | `witness-in` unchanged; `witness-out`'s `viaCarrier` type line, `:412`, spells the body, 1 line edited |
| `Powerset.lagda.md`, `isCodeAt`, `codeAt-in`, `codeAt-out`, `fill` | `:59`, `:298`, `:306`, `:319`, `:506-508` | name-level consumer | **ZERO lines. MEASURED** by reading all five |
| `Faithful.lagda.md`, `isCodeAnyAt`, `codeAnyAt-in`, `codeAnyAt-out`, `CodesAt` | `:64`, `:288`, `:295`, `:309`, `:335-372` | name-level consumer | **ZERO lines. MEASURED** by reading all five |
| `Condensation.lagda.md`, `WitnessAgree.out.go` | `:6709-6732` | the chain site | **2 lines edited** (the spelled body at `:6713-6714`, the pattern at `:6716`), and the site GAINS `har`, the supply the 28 telescopes need |
| `Condensation.lagda.md`, `WitnessAgree.back.go` | `:6734-6752` | the chain back | must now PRODUCE the conjunct; the bounded form's own facts refuse, section 4.3 |
| `Condensation.lagda.md`, `witK` premises | `:6683-6684`, `:7233-7234` | the false tie's premise | not priced: `witK` is FALSE and fenced by the brief |
| `Limit.lagda.md:149` and `:175`, `Faithful.lagda.md:165` | | NOT consumers | they spell `LevelAt`/`BirthAt`, other predicates sharing only the membership atom. MEASURED by reading both blocks |

**HOW MANY CHANGE, HOW MANY DO NOT. Ten producer and consumer sites in four
files. Five do not change at all (all of Powerset, all of Faithful), three are
edited lines with no new mathematics (`witnessAt-out`, `witness-out`,
`out.go`), two take real insertions (the definition, `witnessAt-in`). The
consumer diff at BOTH name-level consumers is EMPTY.**

**THE PRICE AT THE SUBSTRATE, one number: about 8 insertions and 3 edited lines
in `CodeSet.lagda.md`.** Basis: the measured miniature, not a comparable
elsewhere (DD8, P-l honoured: I built the terms rather than transferring
`[LJ-1.343]`'s per-site rate).

**THE PRICE AT THE CHAIN: 2 edited lines at `out`, and the BACK direction,
section 4.3.**

## 4. QUESTION 3: DOES IT SUPPLY THE BOUND. THE MINIATURE

`agents/tasks/LJ-1-360/Probe360.agda`, **exit 0 in 3.60 s**, one file, four
parts.

### 4.1 The supply, `Probe360.agda:109-115`

```agda
supply : ∀ {n} (A x : Fin n) (γ : S ^ n)
       → ⟨ γ ⊨ hasWitnessAt+ A x ⟩
       → ∥ Σ[ w ∈ S ] ( ⟨ fst (lookup x γ) ∈ fst w ⟩
          × ((cc : S) → ⟨ fst cc ∈ fst w ⟩
                → ⟨ (cc ∷ w ∷ γ) ⊨ arityNumAtL zero ⟩)) ∥₁
```

The conclusion is `MustFail350.agda`'s `no-supplier` type with the witness
beside it. The old site's three facts could not supply the second component;
the restated predicate hands it over in the fourth destructuring slot.
Generic in `n` and in the environment, so one copy serves every site of the
family, both towers.

### 4.2 The composition, `Probe360.agda:136-142`

The supply composed with `[LJ-1.350]`'s five-line cure (`Cure350.agda:81-88`,
restated inline at `Tie`, `Probe360.agda:126-133`) produces, at every member
`cc` of the witness, with no hypothesis beyond the telescope's own membership
and equation:

```agda
∥ Σ[ m ∈ ℕ ] (fst N ≡ # m) ∥₁
```

That is the repaired `compK`'s last conjunct, running on the destructed site.
**This is the term the brief asked for: the smallest term that takes the
restated `hasWitnessAt` and produces the conjunct the 28 telescopes need.**

### 4.3 What does NOT supply: the back direction, MEASURED

`WitnessAgree.back` (`src/L/Condensation.lagda.md:6734-6752`) produces
`hasWitnessAt` from the bounded form `hasWitnessBS` (`:1715-1726`), which
binds the witness BY THE STAGE and carries `closedBS` and `shapedBS`. Under
the restatement, `back` owes the new conjunct at the witness. The closest
candidate the bounded form has is its per-member shapedness, and Agda refuses
it: `agents/tasks/LJ-1-360/MustFail360.agda`, **EXPECTED RED, exit 42 in
2.45 s**, refused at `MustFail360.agda:65.18`, the error showing the
twelve-fold `shapesBS` disjunction against the `arityNumAtL` body with
`∈̇ con ωʟ`. **EXPECTED RED. DO NOT REPAIR THAT FILE.**

**WHAT THIS MEANS FOR THE PRICE.** The restatement forces ONE of two repairs
at the chain, and the choice is the orchestrator's (DD23):

1. The bounded form gains the mirrored conjunct, about 3 lines in its
   definition, and `back` passes it through, 1 line. **Then whoever supplies
   `hasWitnessBS` owes the mirrored conjunct's supply, and that supplier is
   the reflection side, outside this probe's fence. It is the widest
   unmeasured term left under the repair.**
2. A new tie one level up, from stage membership to member arity. `[LJ-1.348]`
   section 6 warned the CHEAP candidate would buy exactly this shape of debt;
   the honest candidate meets it on the back leg, not the out leg.

**I priced neither choice. I measured that the need is real.**

## 5. DOES THE 43 SURVIVE

**YES, AS THE TELESCOPE SHARE OF A LARGER NUMBER.** `[LJ-1.350]`'s 43 bought
the repaired telescopes (15 shared cure + 28 telescope lines) CONDITIONAL on
「the witness step supplies the bound」. This probe removes the condition at
the out leg and prices the witness step:

| item | insertions | basis |
|---|---:|---|
| the 28 repaired telescopes | about 43 | `[LJ-1.350]` section 5.1, one measured site |
| the restatement at the substrate | about 8 | section 3, MEASURED at the miniature |
| the bounded mirror and `back` pass-through | about 3 | INFERRED, a definition line and a pass-through, not built |
| **total, out leg complete** | **about 54 to 56** | |

**THE FLOOR UNDER THE 43 IS GONE: the premise 「the restatement supplies the
bound」 is now MEASURED TRUE at the out leg.** What remains unmeasured is the
back leg's supply (section 4.3), which sits UNDER the bounded form's own
supplier, not under the 43.

**AND THE 15-LINE CURE STAYS.** The restatement supplies the telescopes'
HYPOTHESIS; the cure turns it into the CONCLUSION. Neither absorbs the other.

## 6. THE BRIEF'S LINE NUMBERS, RE-DERIVED (C-44)

- `arityNumAtL`: the brief (and `[LJ-1.350]`) say `:185-188`. **Today it is
  `:185-187`**, the definition and its two body lines. Off by one at the tail.
- `arityNumAtL-out` at `:189-197`: **correct today.**
- `arityNumAtL-in` at `:201-207`: **correct today.**
- `hasWitnessAt` at `:240-242`: correct, re-derived.
- `Refute348.agda:338-346` for the cheap candidate: **correct today**, read
  verbatim.
- `Cure350.agda:81-88`: correct, reused as the inline cure's basis.

## 7. NEGATIVE CONTROLS AND NON-VACUITY

**CONTROL A, `[LJ-1.350]`'s STANDARD: ONE ARGUMENT APART, ONE FILE.**
`Probe360.agda:247-263`, inside the green file:

- `member-holds` (`:247`) exhibits the conjunct HOLDING at the member whose
  arity is `numeralL 1`.
- `member-fails` (`:254`) refutes it at the member whose arity is
  `sglS (numeralL 1)`, the same member ONE ARGUMENT apart, by
  `arityNumAtL-out`, `pr-inj` and `sgl1-not-numeral`.

**AND AT THE WITNESS-SET LEVEL the refutation is not vacuous**
(`Probe360.agda:266-268`): the bad WITNESS SET `W-bad`, the singleton of the
bad member, really meets the meet's domain at that member (`cS∈W`,
`:240`), so `conjunct-fails` refutes the conjunct AS STATED at a witness set,
not merely unmet. MEASURED.

**CONTROL B, EXPECTED RED, section 4.3:** `MustFail360.agda`, exit 42 at
`:65.18`, the refusal naming the gap between `shapesBS` and `arityNumAtL`.

**NON-VACUITY, THREE LAYERS.**

1. **The restated predicate is INHABITED at a real point**, as a CLOSED term:
   `Live.inhabited`, `Probe360.agda:288-289`, at the carrier `numeralL 0`,
   the formula `⊤̇` at arity one, and the closure as the witness. No
   hypothesis is assumed (C-45).
2. **The new conjunct's supplier is the delivered closure machinery**: every
   component of `witnessAt-in+` (`Probe360.agda:188-196`) is a delivered
   term, `key∈closure`, `closureClosed`, `closureShaped`, and the new
   `clo-arity` walks `closure-inv` exactly as `closureShaped` already does.
3. **The supply and the composition are GENERIC in the environment**, so they
   are not vacuous at one frame: `supply` and `supply-tie` quantify over
   `n` and `γ`.

## 8. DD4, WITH THE AXIS NAMED (C-46)

**THE AXIS IS AC-AGAINST-GCH, fixed at `scripts/measure/ledger.py:50`,
re-derived today.**

**EVERY TERM I WROTE IS CLASS-FREE.** MEASURED, by reading `Probe360.agda`
whole: it names `fst`, `∈`, `lookup`, `pr`, `pr-inj`, `prʟ`, `numeralL`,
`ωʟ` (inside `arityNumAtL`), `closedAt`, `shapedAt`, `arityNumAtL`,
`∀̇∈`, `∃̇`, `clo`, `closure-inv`, `key∈closure`, `closureClosed`,
`closureShaped`, `codeS`, `keyS` and `ChainZ`'s two pair facts. **Not one
mentions AC, GCH, a well-ordering or a cardinal.**

**AND THE RESTATEMENT IS A DD4 WIN, AND THE IMPORT LIST SAYS SO.** The change
sits in `L.Coding.CodeSet`, which both towers read, and it adds ONE generic
conjunct consumed identically from both ends: the same `har` feeds the arity
hypothesis at every one of the 28 telescopes, in `LowerAgree`, `UpperAgree`
and the chapter, at both carriers. **The import list of the miniature is the
evidence: nothing in it names either tower, so the term is written ONCE for
`L ⊨ AC` and `L ⊨ GCH`, not once each.**

**THE BACK-LEG MIRROR IS WHERE DD4 COULD BREAK, AND IT DOES NOT TODAY.** The
mirrored conjunct in `hasWitnessBS` names only the same generic vocabulary,
and `hasWitnessBS` is itself shared by both towers. The open question is its
SUPPLY, not its shape.

## 9. ARCHIVE USED (DD18)

One line read per archived file, as the brief orders, with archived CODE cited
beside the records.

- **`archive/src/2026-08-09-rud-route/L/Coding/CodeSet.lagda.md:250-252`,
  read the `hasWitnessAt` block whole.** **Line read:** the retired route's
  `hasWitnessAt` is the SAME unbounded body, character for character, with
  `arityNumAtL` at its `:193-212`. **TOOK the finding that the coding
  substrate is one lineage carried across the route change, so the question is
  new on the live route, not inherited: the retired route never restated the
  witness step.** WHY NOT more: its `Condensation` answered boundedness
  structurally, per-clause, not by a witness-set predicate (next line).
- **`archive/src/2026-08-09-rud-route/L/Choice/Faithful.lagda.md:288`, read
  the block.** **Line read:** `isCodeAnyAt c w = arityNumAtL c ∧̇
  hasWitnessAt w c`, the same composition as the live tree. **TOOK it as the
  measured proof that the EMPTY consumer diff is not luck: the name-level
  consumption pattern predates the route change.**
- **`archive/dev/JOURNAL-archived.md:2411-2417`, read the `[T136]` entry.**
  **Line read:** 「`hasWitnessAt` stops because its text needs the twelve-clause
  shape machinery」. **TOOK the boundary reading: on the retired route too,
  the witness step's cost concentrated in the shape machinery, not in the
  witness existential. My restatement leaves the shape conjunct untouched and
  adds a five-line arity conjunct, which agrees with that boundary.** WHY NOT
  `Sequence.lagda.md`: I opened it and it is the TOWER-as-approximation
  chapter, not Devlin's finite-sequence hull; the name is a coincidence and
  nothing there bears on a witness-set predicate.
- **`archive/dev/DECISIONS-archived.md`, read the D31 row, `:51`.** **Line
  read:** 「Option E, keeping `L.Coding` minus Base and `L.Hierarchy` alive,
  costs nothing today and would have overridden D18.」 **TOOK the shape only:
  the coding substrate survived the route ruling, which is why archived
  `CodeSet` and live `CodeSet` agree. WHY NOT a ruling on the witness
  predicate's form: `grep -n "hasWitness" DECISIONS-archived.md` returns one
  TASKS-INDEX-adjacent row and no ruling; there is none to cite.**
- **`archive/dev/TASKS-archived.md:171`, read the row.** **Line read:**
  「`L3.32-T136` Build A text block: PARTIAL. 179 lines; `hasWitnessAt` stops
  at the table boundary.」 **TOOK SHAPE ONLY:** the retired route's own
  dispatch record names `hasWitnessAt` as an unfinished boundary. **REJECTED
  every figure:** different carrier, different frame, and the task died with
  the route.

## 10. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md:246-249`, re-read today.**

**THE BRIEF'S PREMISE AT RISK, ANSWERED: Devlin does NOT state the witness as
the bounded set itself, in those words, because Devlin never states a
witness-set existential at all.** The digest says 2.2 to 2.4 write
`D(v, u) = "v = Def(u)"` as Σ₁ and then 「bind every unbounded quantifier by
the concrete set `K(u)`, the finite sequences over the formula set, the
variables and the members of `u`」, and 「The Σ₀ matrix `C(w, v, u)` with
`w = K(u)` is the bounded satisfaction substrate」. His `w` is a parameter
FIXED to `K(u)`; the bounded-quantifier doctrine is stated for the quantifiers
INSIDE the matrix.

**SO THE NAME 「DEVIN'S OWN」 SURVIVES AS A DOCTRINE PORT, NOT A QUOTATION.**
Our `hasWitnessAt`'s witness existential is the port's own addition, forced by
the slot-carrier design the same chapter records. Restating it so that the
witness's MEMBERS all lie in the key class is the bounded-quantifier doctrine
applied to the one quantifier the port added, and `arityNumAtL` IS the port of
what Devlin's `K(u)` gives for free: `[LJ-1.350]` section 11 already measured
that reading against the same line, and I re-read the line and concur. **The
chain's own comment agrees at `src/L/Condensation.lagda.md:7370-7372`: the
stage `lam` with its `KFacts` closure 「is Devlin's `K(u)` on this coding,
class for class」.**

**WHY NOT the rest of the digest.** `:238-244` is the `[LJ-1.12]` Δ₀
question, settled. `:258` onward is Step D, the definable well-order, which no
term of this family reaches, and C-46 forbids using Devlin's tower axis as
DD4's.

## 11. SECONDS, LOAD, RUNS

One agda process at a time, always `GHCRTS="-A64m -I0 -M8g"`, **cap NEVER
raised**. `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l` run before
every invocation: **0 every time**, fourteen counts, fourteen invocations.

**FLOOR (C-53).** `agents/tasks/LJ-1-360/Floor360.agda`, an empty module:
**0.61 s**. **My floor sits between `[LJ-1.348]`'s 0.07 s and
`[LJ-1.350]`'s 0.72 s, and I offer no comparison with either, as all three
tasks declared the same incompatibility.**

| run | exit | seconds |
|---|---:|---:|
| `Probe360.agda` (name slip, `∈ₛ⟪_⟫↪_`) | 42 | 2.60 |
| `Probe360.agda` (scope slip, `isL`) | 42 | 2.53 |
| `Probe360.agda` (pattern slip, `supply-tie`) | 42 | 2.67 |
| `Probe360.agda` (tuple slip, producer) | 42 | 1.99 |
| `Probe360.agda` (subst direction) | 42 | 3.13 |
| `Probe360.agda` (subst direction, implicits named) | 42 | 2.94 |
| `Probe360.agda` (unsolved metas) | 42 | 3.56 |
| `Probe360.agda` (unsolved metas, named) | 42 | 2.97 |
| `Probe360.agda` (frame slip, `Live`) | 42 | about 2.9 |
| `Probe360.agda` | **0** | **3.60** |
| `Probe360.agda` (confirm) | **0** | 1.67 |
| `Floor360.agda` | 0 | **0.61** |
| `MustFail360.agda` (arg-count scope slip) | 42 | 1.85 |
| `MustFail360.agda` (**EXPECTED RED**) | **42** | **2.45** |

**NO INVOCATION CAME NEAR ANY WALL; the longest was 3.60 s. NO heap
exhaustion. Nothing was interrupted. The cap was never raised. C-58 was never
needed: no numeral pattern split was written; the eliminator forms were
imported (`sgl1-not-numeral`, `arityNumAtL-out`).**

**A CACHE WARNING, inherited from the siblings.** My files load
`L.Coding.CodeSet`, `L.Coding.Shape`, `L.Coding.Closed`, `L.Coding.InL` and
`L.Condensation` from their committed interfaces. **No figure here is a cold
check of any chapter, and none is offered as one.** I ran no whole-chapter
check, because nothing was landed.

## 12. PROHIBITIONS, ANSWERED

I wrote only inside `agents/tasks/LJ-1-360/`: this report, `Probe360.agda`,
`Floor360.agda` and `MustFail360.agda`. **`git status --short` shows, beside
those four and the brief `LJ-1.360.md`, only a live sibling's work that is NOT
mine and that I did not open: `agents/tasks/LJ-1-358/`, `agents/tasks/LJ-1-359/`,
`agents/tasks/LJ-1-361/`, `dev/PLAN.md`, `src/Everything.lagda.md` and
`src/L/CantorBernstein.lagda.md`. `src/` holds no probe of mine
and I opened no file under `src/` for writing.** I READ `src/L/Coding/`
(`CodeSet`, `Powerset`, `InL`, `Closed`, `Shape`, `Model` imports),
`src/L/Choice/Faithful.lagda.md`, `src/L/Choice/Limit.lagda.md`,
`src/L/Condensation.lagda.md`, `src/L/Condensation/TwelveAgree.lagda.md`,
`src/FOL/` (`Syntax`, `Semantics`, `ZFStructure`), `src/Base/Truth.lagda.md`,
`src/V/Coding.lagda.md` and `dev/literature/devlin-II5.md`. **I READ and
IMPORTED `agents/tasks/LJ-1-347/Elim347.agda` and edited that directory NOT AT
ALL.** I did not open `LJ-1-344/Supply344.agda`, `LJ-1-348/MustFail348.agda`
or `LJ-1-350/MustFail350.agda` for repair; the two MustFail files are EXPECTED
RED and remain so, and `MustFail360.agda` joins them. **I did not edit
another task's directory. `[LJ-1.358]` was not touched.** I did not open
`src/Everything.lagda.md`, `dev/`, `AGENTS.md` or `.claude/` for writing. No
commit, no push, no `git checkout`, `stash`, `reset` or `clean`. **No
`make check`.** No em dash in any language.

## 13. WHAT I DID NOT SETTLE

- **The back leg's supply (section 4.3).** MEASURED that the bounded form's
  own facts refuse; NOT priced which of the two repairs the orchestrator
  chooses, and NOT measured who supplies the mirrored conjunct at the bounded
  form's own supplier.
- **The landing itself.** Nothing landed; the 8-insertion figure is measured
  at the miniature's shape, not at a landed chapter, and no chapter was
  re-checked.
- **The other 27 telescope lines.** `[LJ-1.350]` measured one; the 28-line
  share remains its INFERRED extension, unchanged by this probe.
- **`witK` and `graphWitK`.** Fenced by the brief as false and partially
  false; the restatement does not repair either, and I built nothing there.
- **The `TwelveAgree` and `EnvSupply` occurrences of the telescope text**
  (11 and 12, counted by `[LJ-1.350]` section 5.3). Not read here; the
  restatement's effect on them is INFERRED to be nil, because they consume
  the telescopes' conclusions, not `hasWitnessAt`. My sweep found no
  `hasWitnessAt` hit in either file, MEASURED by grep.
- **A countermodel for the back leg.** INFERRED available, `[LJ-1.348]`
  section 5.3's shape, about 120 lines, not built; the MustFail control
  measures the type-level gap, which is what the price needed.

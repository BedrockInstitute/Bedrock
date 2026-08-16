# LJ-1.379 report: the BACK direction at the chain, measured

tier: pi (pi-subagent-mode), model `glm-5.3`. PROBE, lands nothing. Written
incrementally (C-22). Every negative is MEASURED or INFERRED, in those words.

## 0. LEAD

**SUPPLIED.**

**ONE LINE: the back direction at the chain SUPPLIES from facts already in
the site's own telescope, at 62 non-blank lines MEASURED at the miniature
(`Back379.agda`, exit 0 in 5.24 s), the two-directional adequacy of
`arityNumAtL` PAYS through its IN direction, and the 54 to 56 floor becomes a
PRICE at about 113 insertions, with the upstream debt `[LJ-1.360]` feared
GONE: the bounded form needs NO mirrored conjunct, so its supplier owes
nothing new.**

**THE TERM.** `har`, `agents/tasks/LJ-1-379/Back379.agda:173-203`, plus the
two generic handlers `bin-arity`/`un-arity` (`:147-171`) and two pairing
equations (`:139-150`). The chain of supply: `ShapedAgree.back` (delivered,
`src/L/Condensation.lagda.md:6689-6693`) walks the bounded shapedness into
the unbounded one at the witness; `shaped-out` (delivered,
`src/L/Coding/Shape.lagda.md:242-244`) flattens the twelve clauses into
`ShapeWit` (`:234-241`, a plain sum under one truncation); each branch feeds
the member equation to the telescope's own `codesK`/`unCodesK`
(`src/L/Condensation.lagda.md:6687-6709`), whose FOURTH component returns
`∥ Σ[ m ∈ ℕ ] (fst ar ≡ # m) ∥₁`; `arityNumAtL-in` (delivered,
`src/L/Coding/CodeSet.lagda.md:201-207`) closes each member. **The
flat-witness equations `BinWit` and `UnWit` carry
(`src/L/Coding/Shape.lagda.md:206-215`) are CHARACTER FOR CHARACTER the
hypotheses `codesK` and `unCodesK` take. That is the whole bridge, and the
tree already held both ends.**

**THE LANDED SHAPE IS GREEN TOO.** `back+`, `Back379.agda:209-236`: from
`⟨ γ ⊨ hasWitnessBS A x K ... ⟩` to `⟨ γ ⊨ hasWitnessAt+ A x ⟩`, the old
three components the delivered terms unchanged (`CA.back hcl , SA.back hsh`)
and the fourth `H.har`. The site restates `WitnessAgree.back`'s telescope
VERBATIM except that **`witK` is DELETED** (`Back379.agda:102-130`): the back
leg never calls it, so the `[LJ-1.348]` objection, "`witK` is FALSE and
threading a hypothesis out of a false parameter buys nothing", DOES NOT REACH
the back leg. MEASURED by the green: the file typechecks without the
parameter.

**AND THE `[LJ-1.360]` CHOICE 1 IS DEAD, WHICH IS THE ROUTE-LEVEL
FINDING.** `[LJ-1.360]` section 4.3 said the restatement forces one of two
repairs: mirror the conjunct into `hasWitnessBS` (about 3 lines, with an
UNMEASURED supply owed upstream at the reflection side), or a new tie one
level up. **A third repair exists and neither price nor debt: `back` supplies
the conjunct itself, from `hsh`, `f`, `codesK` and `unCodesK`, all already in
the delivered telescope.** No mirrored conjunct, no pass-through, no upstream
term. The repair is priced END TO END.

## 1. THE ANSWER TABLE

| claim | verdict | basis |
|---|---|---|
| the bounded form's own candidate fails, and as predicted | **YES, MEASURED** | re-run, exit 42 in 1.81 s, section 2 |
| the refusal is the one `[LJ-1.360]` predicted | **YES, MEASURED** | same site `:65.18`, same gap, section 2 |
| another candidate exists | **YES, MEASURED** | `Back379.agda`, exit 0 in 5.24 s, section 3 |
| `arityNumAtL`'s two directions pay at the back | **YES, MEASURED** | the IN direction closes all twelve branches, section 3 |
| the walk needs `codesK`'s numeral component | **YES, MEASURED** | `MustFail379.agda`, exit 42, `fst N != # k`, section 5 |
| the back leg needs `witK` | **MEASURED FALSE** | the green site omits the parameter, section 0 |
| the conclusion type is refutable, not squash-collapsed | **YES, MEASURED** | `member-fails`/`conjunct-fails`, copied and green, section 5 |
| the back-leg price is about 3 lines | **MEASURED FALSE** | 62 non-blank lines at the miniature, section 4 |
| the upstream mirrored-conjunct debt is real | **MEASURED FALSE** | no mirroring is needed, section 4 |
| the 54 to 56 was a floor | **YES** | its last term is now measured; it is a price, section 4 |
| anything landed in `src/` | **MEASURED FALSE** | `git status --short`, section 10 |
| a run hit a wall | **MEASURED FALSE** | longest 5.24 s, section 9 |

### THE PREMISES, EACH MARKED

- **「The `hasWitnessAt` restatement supplies the bound at 8 insertions, at
  `agents/tasks/LJ-1-360/Probe360.agda:109-115`.」** VERIFIED: the supply sits
  at `:109-115`, read today, and its file re-ran green, exit 0 in 1.75 s
  (section 9). The 8-insertion substrate figure is `[LJ-1.360]`'s measured
  miniature (`Probe360.agda:179-183`), read today; I did not re-measure it,
  and my price keeps it as its basis.
- **「The BACK direction is the one term left unmeasured, at
  `agents/tasks/LJ-1-360/lj-1.360-report.md:11-13`.」** VERIFIED: the lead
  paragraph, read today, says exactly that, with the widest term being the
  upstream mirrored supply, now GONE (section 4).
- **「Its closest candidate was refused, at
  `agents/tasks/LJ-1-360/MustFail360.agda:1`, exit 42.」** VERIFIED by
  re-run: exit 42 in 1.81 s, same site `:65.18`, section 2.
- **「`arityNumAtL` has BOTH adequacy directions delivered, at
  `src/L/Coding/CodeSet.lagda.md:189-197` and `:201-207`.」** VERIFIED by
  reading today: `arityNumAtL-out` at `:189-197`, `arityNumAtL-in` at
  `:201-207`, the definition at `:185-187`.
- **THE PREMISE AT RISK, 「the two-directional adequacy should pay at the
  BACK direction」.** VERIFIED AT MY SITE, not inherited: the IN direction
  closes all twelve branches of the built term, `Back379.agda:158-160` and
  `:167-169`, exit 0. `[LJ-1.350]`'s site judgement was not transferred
  (P-l).

## 2. QUESTION 1: WHY THE BOUNDED FORM'S CANDIDATE FAILS

**Re-run today (C-44): `MustFail360.agda`, exit 42 in 1.81 s, refused at
`MustFail360.agda:65.18`, the site `[LJ-1.360]` recorded.**

**AGDA'S OWN TYPE, quoted from the re-run** (elided only in the middle of the
twelve-fold disjunction):

```
⟨ (c ∷ w ∷ γ) ⊨ binFormBS (suc N0) (suc K) (bothTmBS ...) ∨̇ ...
  (twelve binFormBS/unFormBS clauses at slots N0 to N11) ... ⟩
!=<
Σ (S 𝒮M) (λ x → ⟨ (x ∷ c ∷ w ∷ γ) ⊨ (∃̇ (prAtL (suc (suc zero)) (suc zero) zero
  ∧̇ (var (suc zero) ∈̇ con ωʟ))) ⟩)
when checking that the expression hshBS c hc has type
⟨ (c ∷ w ∷ γ) ⊨ arityNumAtL zero ⟩
```

**WHY, IN ONE PARAGRAPH.** The shapedness binds the member into a twelve-fold
DISJUNCTION of tagged clause frames. In every frame the arity position is an
EXISTENTIAL over K: `arTagPairBS` says the member is `pr (ar , pr (tag , pr (a
, b)))` with `ar`, `tag`, `a`, `b` all in K, and NOTHING says `ar` is a
numeral (`src/L/Condensation.lagda.md:1497-1505`, `:1525-1545`).
`arityNumAtL` says the member is a pair whose FIRST component is a numeral in
`ωʟ` (`src/L/Coding/CodeSet.lagda.md:185-187`). K-membership is not
numeral-hood, and no clause of the disjunction states a numeral fact about the
first component. So the refusal is exactly the gap `[LJ-1.360]` predicted: a
disjunction of shapes against a pair equation plus `ω`-membership.

**IS THE FAILURE THE PREDICTED ONE? YES.** `[LJ-1.360]` marked the file
EXPECTED RED and named "the twelve-fold `shapesBS` disjunction against the
`arityNumAtL` body with `∈̇ con ωʟ`" (`lj-1.360-report.md`, section 4.3). The
re-run reproduces that type at the same position. The prediction was correct.

## 3. QUESTION 2: `arityNumAtL`'s TWO DIRECTIONS PAY. THE TERM

**THE PREMISE AT RISK, ANSWERED AT MY SITE (P-l honoured: I built the term,
I did not transfer `[LJ-1.350]`'s judgement).** The two-directional adequacy
does pay, and the BACK direction is where the IN direction pays:

- `arityNumAtL-in` (`src/L/Coding/CodeSet.lagda.md:201-207`) closes EVERY
  branch of the walk, twelve times, from one equation plus one numeral.
  `Back379.agda:158-160` and `:167-169`.
- `arityNumAtL-out` is NOT used at the back leg. It is the decode side, and
  `[LJ-1.360]`'s `supply-tie` already used it at the OUT leg
  (`Probe360.agda:126-142`). The two directions each have their leg. That is
  the sense in which the adequacy is two-directional: BOTH legs of the
  repair now consume it.

**WHY THE BRIDGE WAS ALREADY IN THE TREE.** Three facts, each delivered:

1. `BinWit k rel γ c` carries `fst c ≡ pr (fst N) (pr (# k) (pr (fst a)
   (fst b)))` and `UnWit` the unary equation
   (`src/L/Coding/Shape.lagda.md:206-215`). `codesK`/`unCodesK` in
   `WitnessAgree`'s telescope take EXACTLY those equations and return the
   numeral arity in the fourth component
   (`src/L/Condensation.lagda.md:6687-6709`). The flat witness and the
   telescope fact were written for each other, one chapter apart.
2. `ShapedAgree.back` already walks bounded shapedness into unbounded
   shapedness at the witness frame, per member
   (`src/L/Condensation.lagda.md:6689-6693`).
3. `shaped-out` already flattens the unbounded disjunction into `ShapeWit`
   (`src/L/Coding/Shape.lagda.md:242-244`).

The new work is only the WALK from `∥ ShapeWit ∥₁` through the handlers:
one `PT.rec`, twelve plain sum branches, each one handler call
(`Back379.agda:173-203`). No numeral pattern split anywhere, so C-58 never
applied.

**ONE DETAIL WORTH RECORDING FOR THE LANDING.** The tag slots carry numerals
by hypothesis: `KFacts` holds `tagEq0` to `tagEq11`, `fst (lookup N_i γ) ≡ fst
(numeralL i)` (`src/L/Condensation.lagda.md:6082-6093`). My term never touches
them, because `ShapedAgree.back` consumes the tag equations on its own side
and hands the walk NUMERAL tags (`binForm 0` to `binForm 11`,
`src/L/Coding/Shape.lagda.md:182-188`). The landing inherits that for free.

## 4. QUESTION 3: WHAT THE 54 TO 56 BECOMES

**A PRICE.** Every term is now measured:

| item | insertions | basis |
|---|---:|---|
| the 28 repaired telescopes | about 43 | `[LJ-1.350]` section 5.1, one measured site |
| the restatement at the substrate | about 8 | `[LJ-1.360]` section 3, MEASURED at its miniature |
| the back leg, `har` and its handlers | **about 62** | **THIS PROBE, MEASURED** at `Back379.agda` |
| edited lines beside | about 4 | 2 at `out` (`[LJ-1.360]`), 1 tuple line at `back` (this probe), 1 at `witnessAt-out` (`[LJ-1.360]`) |
| **total** | **about 113** | |

**HOW THE 62 IS COUNTED.** The `Har` block of `Back379.agda` holds 68
non-blank lines, of which 6 are the `SA` instantiation the chapter's
`back.go` already computes (`src/L/Condensation.lagda.md:6751-6756`), so 62
are new, plus one edited tuple line at `go`'s conclusion. Basis: this
miniature, not a comparable elsewhere (DD8). No compression beyond the shared
`SA` was measured; none is claimed.

**THE `[LJ-1.360]` "about 3" IS MEASURED FALSE, IN BOTH HALVES.** Its
inferred figure priced a mirrored conjunct in `hasWitnessBS` plus a
pass-through. The mirror is not needed, and the real term is twenty times
the inferred figure. **The floor's missing term was never cheap; it was
unmeasured.**

**AND THE WIDEST FEARED TERM IS GONE.** `[LJ-1.360]` section 4.3: "whoever
supplies `hasWitnessBS` owes the mirrored conjunct's supply, and that supplier
is the reflection side, outside this probe's fence. It is the widest
unmeasured term left under the repair." Under this repair there is no
mirrored conjunct, so NOTHING is owed upstream. The orchestrator may still
prefer the mirror route (DD23 is the ruling that choices like this belong to
the owner), but its upstream term remains unmeasured and outside every fence;
this route is closed end to end.

**THE `witK` OBJECTION, ANSWERED WHERE IT WAS ASKED.** It does not reach the
back leg: the site is green without the parameter. It still reaches the OUT
leg, where `out.go` computes `wK = witK w ...` (`src/L/Condensation.lagda.md:
6721-6722`); that is `[LJ-1.348]`'s recorded finding and this probe changes
nothing there.

## 5. THE NEGATIVE CONTROL

**THREE PRONGS, ALL MEASURING.**

1. **THE NAIVE CANDIDATE FAILS, RE-RUN.** `MustFail360.agda`, exit 42 in
   1.81 s, section 2. The gap is real: shapedness is not arity.
2. **THE WALK WITHOUT `codesK`'s NUMERAL FAILS.** `MustFail379.agda`,
   **EXPECTED RED, exit 42 in 2.02 s**, refused at `MustFail379.agda:60.8`,
   Agda's type: `fst N != # k of type V ℓ`, when checking `e ∙ cong (...)
   refl` against `fst (lookup zero (c ∷ w ∷ γ)) ≡ pr (# k) (fst (prʟ
   (numeralL k) (prʟ a b)))`. This is the tag-as-arity confusion: without the
   fourth component, the only numeral the flat witness carries is the TAG,
   and offering it where the arity belongs does not typecheck. **So the
   green's load-bearing input is measured: the supply is not free.**
3. **THE CONCLUSION TYPE IS REFUTABLE.** `[LJ-1.360]`'s member-level control,
   copied verbatim into `Back379.agda` PART 3 (`:248-305`) and green in the
   same file as the supply: `member-fails` refutes `arityNumAtL` at the
   member whose arity is `sglS (numeralL 1)`, one argument from the good
   `numeralL 1`, by `arityNumAtL-out`, `pr-inj` and `sgl1-not-numeral`; and
   `conjunct-fails` refutes the conjunct AS STATED at a witness set, at a
   member that set really holds (`cS∈W`).

**WHY THIS IS NOT THE `[LJ-1.368]` TAUTOLOGY.** That lesson was a green whose
motive met `squash₁` after unfolding, so the content collapsed. Here the
`PT.rec` motives are `snd` of the goal, which is the legitimate elimination
into a proposition, and prongs 2 and 3 measure that the content does not
collapse: the goal type is REFUTED at a real point (prong 3), and the term
does not typecheck without its numeral input (prong 2). A tautology would
survive both. This term does not get the chance.

## 6. DD4, WITH THE AXIS NAMED (C-46)

**THE AXIS IS AC-AGAINST-GCH, fixed at `scripts/measure/ledger.py:50`,
re-derived today: the line names DD4's report as "what the AC and GCH
closures share".**

**EVERY TERM I WROTE IS CLASS-FREE.** MEASURED, by reading `Back379.agda` and
`MustFail379.agda` whole. They name `pr`, `pr-inj`, `prʟ`, `prʟ-fst`,
`numeralL`, `numeralL-fst`, `#_`, `arityNumAtL`, `arityNumAtL-in`,
`arityNumAtL-out`, `shapedAt`, `shaped-out`, `ShapeWit`, `ShapedAgree`,
`ClosedAgree`, `KFactsNS.KFacts`, `KFactsCons`, `hasWitnessBS`, `shapedBS`,
`closedBS`, `ChainZ`, `sgl1-not-numeral`, `inl`, `inr`, the formula
constructors, and the path algebra. **Not one mentions AC, GCH, a
well-ordering or a cardinal.** This is the fourth class-free term on this
chain, after `[LJ-1.348]`, `[LJ-1.350]` and `[LJ-1.360]`.

**AND THE TERM IS A DD4 WIN, NOT A FORMALITY.** `har` lands in
`L.Condensation`, the chapter both towers' agreement chapters read
(`LowerAgree.lagda.md:33-36`, `UpperAgree.lagda.md:33-36` import its
modules), and it is generic in `n`, in the environment and in the twelve
slots. One copy serves `L ⊨ AC` and `L ⊨ GCH`. The import list is the
evidence again: nothing in it names either tower.

## 7. ARCHIVE USED (DD18)

One line per corpus, each archived file read quoted at its real line number.
**`check-dd18-survey.py` today exits 1 on one gated return, `LJ-1.378`, a
live sibling whose return names neither the archive directory nor its two
digests. My return is not named by the checker: this report names all four
corpora and the digest above.**

- **`archive/src/2026-08-09-rud-route/L/Coding/CodeSet.lagda.md`, read the
  arity block whole.** **Line read:** `keyArityAtL-out : ∀ {n} (c : Fin n)
  (k : ℕ) (γ : S ^ n)` at `:146`, with `keyArityAtL-in` at `:153` and the
  definition at `:143-144`. **TOOK the shape only: the retired route's arity
  predicate ALSO had both directions, so closing a member by the adequacy's
  IN direction is this lineage's own move, not a novelty this repair
  introduces.** WHY NOT more: its arity is a FIXED `k` at `tagAtL`, the live
  one an `ωʟ` membership at `prAtL`, different coding schemes, so no term
  transfers. MEASURED by reading both. **And the retired route has NO back
  site at all: `grep -c hasWitness archive/src/2026-08-09-rud-route/L/
  Condensation.lagda.md` returns 0, and the predicate appears there only as
  a module PARAMETER in the patch (`rud-route-src.patch:26002`). So nothing
  transfers, and that is measured, not assumed.**
- **`archive/dev/JOURNAL-archived.md:2411-2417`, read the `[T136]` entry.**
  **Line read:** "`hasWitnessAt` stops because its text needs the
  twelve-clause shape machinery." **TOOK the boundary reading: on the retired
  route too, the witness step's cost lived in the twelve-clause machinery,
  and my measured 62 is exactly a twelve-clause walk. The price agrees with
  the boundary the archive already recorded.** WHY NOT more: nothing else in
  the entry bears on a live-route adequacy term.
- **`archive/dev/DECISIONS-archived.md:51`, read the D31 row.** **Line
  read:** "Option E, keeping `L.Coding` minus Base and `L.Hierarchy` alive,
  costs nothing today and would have overridden D18." **TOOK the shape only:
  the coding substrate survived the route ruling, which is why archived
  `CodeSet` and live `CodeSet` are one lineage.** WHY NOT a ruling on the
  witness predicate's form: `grep -c hasWitness DECISIONS-archived.md`
  returns 0, MEASURED. There is none to cite.
- **`archive/dev/TASKS-archived.md:171`, read the row.** **Line read:**
  "PARTIAL. 179 lines; hasWitnessAt stops at the table boundary." **TOOK
  SHAPE ONLY, and no figure: different carrier, different frame, and the
  task died with the route.**

## 8. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md:240-252`, re-read today.**

**THE BRIEF'S ONE-LINE QUESTION: does the BACK direction have any counterpart
in the text? NO.** For Devlin the bounded form is not a second predicate to
be tied to a first: `w = K(u)` is FIXED and the Σ₀ matrix `C(w, v, u)` IS the
satisfaction substrate, so there is no transfer to state. Our back leg exists
because the port added the unbounded witness existential
(`[LJ-1.360]` section 10's finding, which I re-read at the same lines and
concur with). The bounded-quantifier doctrine COVERS the conjunct my term
produces, members in the key class, but the transfer term itself is the
port's own leg and has no counterpart in the text. **So `[LJ-1.348]`'s "Devlin's
own" survives for the CONJUNCT, and my term is the port's own for the
TRANSFER.** WHY NOT the rest of the digest: `:238-244` is the settled `[LJ-1.12]`
Δ₀ question, and `:258` onward is Step D, which no term of this family
reaches.

## 9. SECONDS, LOAD, RUNS

One agda process at a time, always `GHCRTS="-A64m -I0 -M8g"`, **cap NEVER
raised**. `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l` run before
every invocation: **0 every time**, thirteen counts, thirteen invocations.

**FLOOR (C-53).** `agents/tasks/LJ-1-379/Floor379.agda`, an empty module:
**0.08 s**. No comparison is offered with any sibling's floor; the three
siblings declared the same incompatibility.

| run | exit | seconds |
|---|---:|---:|
| `Floor379.agda` (first, untimed) | 0 | instant |
| `Floor379.agda` (timed) | 0 | **0.08** |
| `Back379.agda` (parse slip, nested pattern) | 42 | 0.43 |
| `Back379.agda` (module export slip, `KFacts`) | 42 | 2.98 |
| `Back379.agda` (scope slip, `_+_`) | 42 | 1.84 |
| `Back379.agda` (three further pattern and arity slips) | 42 | 2.1 to 2.8 |
| `Back379.agda` | **0** | **5.24** |
| `Back379.agda` (confirm) | **0** | 1.77 |
| `MustFail379.agda` (**EXPECTED RED**) | **42** | **2.02** |
| `MustFail360.agda` (re-run, C-44, EXPECTED RED) | **42** | **1.81** |
| `Probe360.agda` (re-run, C-44) | **0** | **1.75** |

**NO WALL. NO heap exhaustion. Nothing was interrupted. The cap was never
raised. C-58 was never needed: no numeral pattern split was written; the walk
splits a plain sum, and the eliminator forms were imported
(`arityNumAtL-in`, `arityNumAtL-out`, `sgl1-not-numeral`).**

**A CACHE WARNING, inherited from the siblings.** My files load
`L.Coding.Shape`, `L.Coding.CodeSet` and `L.Condensation` from their
committed interfaces. No figure here is a cold check of any chapter, and none
is offered as one.

## 10. PROHIBITIONS, ANSWERED

I wrote only inside `agents/tasks/LJ-1-379/`: this report, `Back379.agda`,
`MustFail379.agda` and `Floor379.agda`. **`git status --short` shows, beside
those four, work that is NOT mine and that I did not open: `Makefile`,
`dev/PLAN.md`, `dev/vendors.toml`, `scripts/gate/check-live-record-claims.py`,
`agents/tasks/LJ-1-377/` and `agents/tasks/LJ-1-378/`. `src/` holds no file of
mine and I opened no file under `src/` for writing.** I READ `src/L/Coding/`
(`CodeSet`, `Shape`, `Model`), `src/L/Condensation.lagda.md`,
`src/L/Condensation/LowerAgree.lagda.md` and `UpperAgree.lagda.md` (import
lines only), `src/FOL/Semantics.lagda.md`, `dev/literature/devlin-II5.md` and
the four archive corpora. **I READ and RE-RAN `agents/tasks/LJ-1-360/`'s
`Probe360.agda` and `MustFail360.agda` and edited that directory NOT AT ALL;
`MustFail360.agda` remains EXPECTED RED. `MustFail379.agda` joins it.** I did
not open any other task's directory. I did not open `src/Everything.lagda.md`
or `dev/` for writing. No commit, no push, no `git checkout`, `stash`,
`reset` or `clean`. **No `make check`.** Both linters pass:
`lint-prose.py --check` and `lint-agda.py --check`, exit 0 each. No em dash
in any language.

## 11. WHAT I DID NOT SETTLE

- **The landing itself.** Nothing landed; the 62 is measured at the
  miniature's shape, not at a landed chapter, and no chapter was re-checked.
- **Compression below 62.** The handlers are generic in `k` and the twelve
  branches are one line each; a leaner packing may exist, but none was
  measured and none is claimed.
- **The mirror route's upstream term.** If the orchestrator still prefers
  `[LJ-1.360]`'s choice 1 (DD23), its reflection-side supply remains
  unmeasured and outside my fence. This probe makes it OPTIONAL, not
  required.
- **The other 27 telescope lines.** `[LJ-1.350]` measured one; the 28-line
  share remains its INFERRED extension, unchanged by this probe.
- **`witK` and `graphWitK` at the OUT leg.** `[LJ-1.348]`'s findings stand;
  I built nothing there and the back leg does not need them.
- **A countermodel for the bounded form itself.** Not needed: the back leg
  is a CONDITIONAL supply, from the bounded form's satisfaction to the
  restated one, and whether the bounded form is inhabited at a real stage is
  the reflection side's question, not the chain's.

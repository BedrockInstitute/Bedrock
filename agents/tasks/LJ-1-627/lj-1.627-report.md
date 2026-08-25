# [LJ-1.627] report: code DATA at the ambient-least ordinal, and the truth of the target

Head slot: coder. Machine: shared. Caliber on this pane: GHCRTS
`[-A64m -I0 -M2g]`, set by the program. I did not set it. One Agda
process at a time, every run capped and recorded under `runs/`.

## VERDICT

**NO-GO, stated as a stop: the target is FALSE at its stated
generality.** The obligation `codes-at-kappaL` asks for code DATA at
the ambient-least ordinal, for EVERY ambient ordinal `a` at once. The
consumer's exact shape (`agents/tasks/LJ-1-623/Probe623.agda:140-141`)
is `(a : S) (oa : IsOrd (fst a)) → Σ[ F ∈ S ] InjCode F a (κL a oa)`,
and that shape is falsified by the same collapse semantics
`[LJ-1.623]` used to falsify `AmbientToCoded`
(`agents/tasks/LJ-1-623/review-of-site-fiber.md:79-83`), by one further
step: in that semantics the ambient-least ordinal of `ℵ₁^L` IS `ω`, so
the obligation delivers, at `a := ℵ₁^L`, exactly the code at `ω` that
the review measured does not exist there. The full statement of the
stop is `agents/tasks/LJ-1-627/review-of-codes-at-kappaL.md`. Nothing
was postulated. Nothing landed in `src/`. Nothing was committed and
nothing was pushed. No term of `Probe627.agda` carries the obligation
name, so the program's witness reads the obligation as undelivered,
which is the truth of this return.

## WHAT THE CONSUMER CONSUMES (D-10, answered before any Agda)

`agents/tasks/LJ-1-623/Probe623.agda:140-141`:

    codes-at-κL→residue : ((a : S) (oa : IsOrd (fst a))
                           → Σ[ F ∈ S ] InjCode F a (κL a oa))

One pair per ambient ordinal `a`: an L-element `F`, held as DATA, with
`InjCode F a (κL a oa)`, the four conjuncts of
`src/L/Cardinal.lagda.md:223-228`. No site parameter occurs in the
shape, which is why `Probe627` takes only `lem`. The probe states this
type VERBATIM (`agents/tasks/LJ-1-627/Probe627.agda:93-95`) and ties
it to the alone-typechecked W3 (`agents/tasks/LJ-1-627/runs/W3.agda:56-58`)
by one refl (`Probe627.agda:98-99`), so the two cannot drift.

## WHAT LEASTNESS BUYS

**A comparison discipline, and nothing else.** What the leastness of
`κL` gives, in one green row, is the landing discipline
(`agents/tasks/LJ-1-627/Probe627.agda:123-126`): every coded target
`γ` satisfies `κL(a) ≤ γ`. The reason is that a code carries an
ambient injection (`readL`, `src/L/CantorBernstein.lagda.md:33-36`),
and the ambient search (`src/L/Cardinal.lagda.md:116-117`) cannot stop
above an ordinal that receives one.

What leastness does NOT give is any code, and the reason is where the
code lives in `κL`'s own selection. `κL` is least for the predicate
`InjP γ = ∥ Inj γ ∥₁` (`src/L/Cardinal.lagda.md:66-67`): the TRUNCATED
AMBIENT injection. Its leastness normalizes ambient witnesses and
says nothing about codes. Codes AT `κL(a)` say that the coded-least
cardinal EQUALS the ambient-least cardinal, and the green pair
`codes→bridge` / `bridge→trunc`
(`agents/tasks/LJ-1-627/Probe627.agda:162-168`) measures that this
equality IS `[LJ-1.623]`'s `AmbientToCoded` at its hardest instance,
in both directions. The two reopeners of
`agents/tasks/LJ-1-623/review-of-site-fiber.md:101-105` are one
demand, not two.

**The difference from an arbitrary site, stated plainly.** At an
arbitrary site the truncated ambient supply exists
(`κ-injL`, `src/L/SquareLawClosed.lagda.md:82-84`, holds at `κL`
itself) and the wall is the untruncation of the ambient payload:
`[LJ-1.618]`'s residue. At `κL` that same wall stands, and the CODE
obligation is strictly stronger than the residue: it needs the bridge
instance, which the collapse semantics falsifies
(`review-of-codes-at-kappaL.md`, THE TRUTH MEASURE). So the answer to
the brief's question is: leastness buys nothing toward a code. The
brief said that answer makes this `[LJ-1.618]`'s wall under another
name; the measurement says the wall at `κL` is WORSE than that wall.
`[LJ-1.618]`'s wall is an untruncation that nobody has built. This
wall is a target that is false in one legitimate reading of the
ambient theory. A stop was ordered either way, and the stop is
delivered with the stronger evidence.

## DOES (iii) CLOSE

**NO.** Nothing was inhabited, so nothing was discharged, and this
task adds a stronger fact: the "for free" route itself is closed as
false. Ingredient (iii) is the pairing
(`agents/tasks/LJ-1.613/lj-1.613-report.md:130-137` lists the five;
after `[LJ-1.613]` and `[LJ-1.625]`, (i), (ii), (iv) and (v) are paid
and (iii) alone is wanting). The chain that would have closed it is
green and stands: codes at `κL` give the residue
(`[LJ-1.623]`, `agents/tasks/LJ-1-623/Probe623.agda:140-143`), the
residue gives the site (`:115-116`), `[LJ-1.618]`'s recursion gives
the pairing payload from the residue
(`agents/tasks/LJ-1-618/Probe618.agda:210-211`). But the first link of
that chain is now measured FALSE at the all-a shape, so no supply of
code data at `κL` can exist to feed it. What remains on this row: the
owner's ruling on `AmbientToCoded` as an axiom, already with the owner
(`agents/tasks/LJ-1-623/review-of-site-fiber.md:104-105`), or the
third reopener, a weakly constant endomap on the AMBIENT payload at
the single-pair grain (`:106-110`), which bypasses codes entirely and
which this task did not touch. I did not read a discharge of (iii)
into anything here: the probe inhabits no row of the chain.

## WHAT I BUILT AND WHAT IT COST

`agents/tasks/LJ-1-627/Probe627.agda`, 229 file lines, three sections
of content plus the truth measure in prose:

- Section 0: the obligation's type, verbatim consumer shape, tied to
  W3 by one refl (`:93-99`).
- Section 1, WHAT LEASTNESS BUYS: `codes→ambient`, the readback at the
  least pair (`:111-114`); `coded-sits-above`, `[LJ-1.623]`'s landing
  row re-derived site-free (`:123-152`); `BridgeLeast` with
  `codes→bridge` and `bridge→trunc`, the identity with the bridge's
  hardest instance (`:157-168`).
- Section 2, the untruncation, TYPE ONLY: `TruncCodes-at-κL` and
  `Trunc→Codes` (`:187-192`), with the comment naming what the row
  needs (a stage covering the codes of one pair; `isL` names no stage,
  `src/L/Constructible.lagda.md:376-377`) and why it is moot.
- Section 3, the truth measure and the literature answer in prose with
  file:line (`:195-228`).

Prices, all under the program's caliber and the caps this task set:

| run | cap | result |
|---|---|---|
| W3 alone, first text (`runs/w3-1.out`) | 120 s | green, 1.75 s, peak 357,598,024 bytes |
| W3 alone, final text (`runs/w3-2.out`) | 120 s | green, 1.45 s, peak 356,549,448 bytes |
| floor, landing row holed (`runs/floor-1.out`) | 300 s | exit 42, 1.52 s, peak 359,400,264 bytes, the only error is the deliberate hole (`[UnsolvedInteractionMetas]` at `runs/Floor.agda:126`) |
| final 1, 2, 3 (`runs/final-1..3.out`) | 300 s | green, 1.52 s, 1.46 s, 1.45 s, peak 359,678,792 bytes |
| final 4, after the citation fixes (`runs/final-4.out`) | 300 s | green, 1.51 s, peak 359,678,792 bytes |
| final 5, after the last comment fix (`runs/final-5.out`) | 300 s | green, 1.53 s, peak 359,662,408 bytes |

The highest peak of the task is 359,678,792 bytes, 16.8 percent of the
2g caliber. No wall was met and no restructuring was needed. The floor
ran BEFORE the final form, per the heavy-object rule, and the floor
and the final agree to within 0.07 s: the frame is the whole price
here, the rows are cheap, and the imports were trimmed to what the
rows use (no `L.Ordinal.Stages`, no `L.Choice.*`, no site chapters).

The brief estimated about 170 probe lines with about 45 for the
obligation. Actual: 229 lines, of which the obligation's type and tie
are 7 code lines and the four green rows are 20 more. The estimate's
SHAPE held; the overage is comments that carry the truth measure,
which the brief's estimate did not price. No deadline occurred.

## THE LITERATURE STEP, ANSWERED IN THE CRITERION'S OWN TERMS

The brief orders the question answered as: does the code type at `κL`
have a weakly constant endomap? Kraus, Escardó, Coquand and
Altenkirch, Theorem 16: a type has a constant endemap IFF it has split
support, `∥X∥ → X`
(`dev/literature/truncation-and-selection.md:158-159`).

**The answer is that the question does not sit where the wall is, and
the criterion itself says so.** Theorem 16 converts a SUPPLIED `∥X∥`
into `X`. At the collapse pair the code type `X` is EMPTY: the
identity is a weakly constant endomap, split support holds vacuously,
and the data is still absent. So at exactly the pair that falsifies
the obligation, the criterion's two sides both hold and the target is
still false. The missing input is `∥X∥` itself, the truncated coded
existence at `κL`, and that input is the bridge instance
(`review-of-codes-at-kappaL.md`, THE IDENTITY). Where the codes of one
pair ARE stage-bounded, the tree's least-code selection is the
normalization the criterion wants (`leastOf`,
`src/L/WellOrder/Base.lagda.md:158-160`; the canonical instance
`src/L/Cardinal.lagda.md:192-195`), so the endomap exists there; the
selection's constraint is the one the literature file records, "a data
payload does not come out" of an hProp-valued `leastOf`
(`dev/literature/truncation-and-selection.md:146-148`), which is why
the fibers' being propositions
(`isPropInjCode`, `agents/tasks/LJ-1-576/Probe576.agda:77`) does not
by itself deliver `F`. In the criterion's own vocabulary: the
untruncation question "can this truncation be lifted" is, as the file
says, always the endomap question
(`dev/literature/truncation-and-selection.md:163`), but this
obligation is not an untruncation problem. It is a supply problem at
the truncated level, and the supply is the bridge.

## WHERE THE TERM BELONGS, IF IT HOLDS

**Not at `L.Choice.Faithful`.** The brief's candidate hosts ingredient
(v), and `[LJ-1.625]` sited (v) there because the CodeSet names were
already in its `using` (`src/L/Choice/Faithful.lagda.md:63-65`). This
term spells `κL`, `InjCode` and `readL`: `L.SquareLawClosed`,
`L.Cardinal` and `L.CantorBernstein`. Faithful's import block
(`src/L/Choice/Faithful.lagda.md:45-66`) carries none of the three, so
landing there costs three new edges into a master whose topic is the
choice table. A measured cure does not transfer by analogy, and this
is the measured difference. The natural home, if the term ever held,
is `L.SquareLawClosed`: it seals `κL` and its projections there
(`src/L/SquareLawClosed.lagda.md:73-89`) and already imports
`L.Cardinal` (`:37`), so the spelling costs one `using` widening
(`InjCode`) and no new edge. The question is moot on this stop, and I
record it as conditional, not as a landing plan.

## W2, ANSWERED

Zero generic code was written and none was needed: every row of the
probe applies a chapter that already exists at a generic carrier.
`readL` is generic over the pair (`src/L/CantorBernstein.lagda.md:33-36`),
`leastOf` over an arbitrary strict well-order
(`src/L/WellOrder/Base.lagda.md:158-160`), `ord-tri` over arbitrary
ordinals (`src/L/Ordinal/Linear.lagda.md:136-137`). Both trophies
share these pieces exactly as the chapters do. No deadline pressure
occurred.

## PREMISE DEFECTS, TWO, MINOR AND NOT LOAD-BEARING

1. **Premise 11 names a rule that does not exist.** There is no R-42
   in `dev/LESSONS.md` (0 hits). `dev/LESSONS.md:4404` is C-52's
   Related line. This is the same defect `[LJ-1.613]` reported in its
   premise 11 (`agents/tasks/LJ-1.613/lj-1.613-report.md:186-192`).
   The respelling substance, R-41, was obeyed where it binds: the
   obligation's type is spelled once, in the consumer's own spelling,
   and every row of the probe uses it.
2. **Premise 13's basis is off by one line.** The make-check clause is
   `AGENTS.md:75`, not `:74` (`:74` is the one-off-instruction
   bullet). The clause itself is real. I ran no commit, so the gate
   did not bind this task.

All other premises checked at their cited lines: 1
(`review-of-site-fiber.md:99`), 2 (`Probe623.agda:140`), 3 (`:85`), 4
(`src/L/Ordinal/SquareLaw.lagda.md:960-961`), 5 and 6 (both report
files exist), 7 (`src/L/Choice/Faithful.lagda.md:63-65`), 8
(`dev/literature/truncation-and-selection.md:150`), 9
(`agents/tasks/LJ-1-576/Probe576.agda:77`), 10
(`agents/tasks/LJ-1-613/Probe613.agda:137`), 12 (`AGENTS.md:43`).

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: READ and used.
  `archive/dev/LJ-dispatch-index.md:183` records, for `[LJ-1.107]`,
  "The non-initial case needs an injection the truncated least-of
  witness cannot give: the inject type is not a prop", which is the
  tree's own measured ancestor of the truncated-payload problem this
  task's Section 2 and the criterion discussion rest on.
- `archive/dev/JOURNAL-archived.md`: not read, declined. The stop's
  evidence chain is `[LJ-1.623]`'s review and live-tree rows; no
  question of this task sent me to a journal entry.
- `archive/dev/JOURNAL.md`: not read, declined, same reason.
- `dev/ARCHIVE.md`: not used, declined. A search for Cardinal,
  SquareLaw and `κ` rows over it returned nothing at this task's
  grain.
- `archive/dev/DECISIONS-archived.md`: not read, declined. No decision
  record bears on the truth of a target this young; the ruling that
  does bear, on `AmbientToCoded`, is with the owner and cited from the
  review.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: READ and used, the
  brief's ordered step. Section 2.4 at `:150`; Theorem 16 at
  `dev/literature/truncation-and-selection.md:158-159`, "A type X has
  a constant endomap if and only if it has split support in the sense
  that ∥X∥ → X"; the criterion's reading rule at `:163`, "So the
  question \"can this truncation be lifted\" is always the question
  \"does this type have a weakly constant endomap\""; the `leastOf`
  constraint at `:146-148`, "The constraint the route carries: `P`
  must be `hProp`-valued" and "A data payload does not come out".
- `dev/literature/digest.md`: READ and used, one line.
  `dev/literature/digest.md:417`, "can prove. Our ambient metatheory
  (Cubical Agda over the HIT V with LEM", with `:418`, "assumed) is
  not weak in that sense", is the record of what the ambient theory
  is, which the collapse-semantics truth measure addresses.
- `dev/literature/devlin-II5.md`: not used, declined. Its ambient
  rows (`:105`, `:215-217`) are about the Σ₀ matrix and LST
  absoluteness for the condensation route, not about the ambient least
  cardinal or the code notion.
- `dev/literature/terms-2026-08.md`: not used, declined. Its ambient
  rows (`:161-162`) are terminology for condensation's inner-to-outer
  crossing; no term of this task needed a glossary decision.
- `dev/literature/geology.md`: not used, declined. Its forcing rows
  (`:426-427`) are about grounds and bedrocks of the set-theoretic
  universe, not about this tree's ambient carrier.

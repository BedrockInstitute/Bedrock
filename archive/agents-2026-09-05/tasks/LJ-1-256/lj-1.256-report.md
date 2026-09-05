# LJ-1.256: DD25 review of `[LJ-1.255]`

tier: opus (deepseek-subagent-mode), the ADVERSARIAL row. **No Agda ran.** No
master, brief or other report was edited. No commit, no push. Written
incrementally (C-22). Every negative is MEASURED or INFERRED, in those words.

## VERDICT

**OVERTURNED.**

**Both halves of the brief's OVERTURNED grade hold. The rate does not
generalize, because it measures one proof copied five times. And the 255
counted something else: it is about 213 lines of NINE shape lemmas plus 42
lines of 28 entries, so `255 / 28 = 9.1` is a figure no source ever wrote.**

**Step 6 costs about 255 in-fence lines, and this chain moved it by about +50,
not by a factor: about 213 for nine shape lemmas, of which three rows are now
MEASURED at or under budget, plus about 42 for the 28 entries, plus one
MEASURED hole of about 52 lines for `sucK`'s union closure that no row in the
table prices.**

## Q1. IS THE MARGINAL RATE REAL?

**The rate is real as a measurement and false as a marginal. MEASURED.**

**The five `envK-*` proof bodies are ONE proof written five times.** Read them
side by side at `agents/tasks/LJ-1-255/ProbeLJ1255.agda:260-270`, `:278-288`,
`:296-306`, `:314-324` and `:332-342`. Each body has the same five steps in the
same order: `PT.rec`, `go`, `subst`, `envSetK`, `#∈λ`. Each `where` block holds
one application of `envSetAt-ident`. **Two of the five are identical except for
the NAMES of unused variables:** `envK-mem` (`:260`) and `envK-neg` (`:278`)
carry the same vector length 7 and the same three indices `zero`, `suc⁴ zero`
and `suc⁶ zero`. **Only the vector and the two `Fin` indices change across all
five.**

**All five report exactly 17 lines**
(`agents/tasks/LJ-1-255/lj-1.255-report.md:37-41`). A group of five whose
measured value has zero variance is one observation, not five.

**The brief asked whether the other 23 share more or share less. They share the
same way, and the record said so before the probe ran.**
`agents/tasks/LJ-1-168/lj-1.168-report.md:356-360` states it as a measurement:
the 28 fields fall into 6 proof shapes plus 2 singletons; Group C's nine fields
differ only in de Bruijn index arithmetic; Group E's ten differ only in which of
two adequacy equalities they call. **The five `envK-*` sit inside Group C's
nine.** So the other 23 are not a new population.

**The copies are avoidable, and the tree already proves it. MEASURED.**
`src/L/Condensation.lagda.md:2926` declares
`module EnvSet {n : ℕ} (E ar B K : Fin n) (γ : S ^ n)`. Its own comment at
`:2917-2925` says the four arguments are slot positions at the frame, so **one
copy serves every frame layout and both towers**. That module is delivered and
green. **The probe's own `envSetAt-ident` has the same slot-generic shape**
(`ProbeLJ1255.agda:199-201`, `{k : ℕ} (γ : Vec CS.S k) (Ei di bi : Fin k)`), and
it is inside the exit-0 probe. **So the pattern that removes the five copies is
MEASURED green at this very site, for the harder half of the proof.**

**What the factored form would cost is INFERRED, not MEASURED**, because I may
not run Agda. The shell varies only in the vector and two indices, so one
`envK-gen` lemma of about 11 lines plus five applications of 2 to 3 lines is the
expected form. **The probe that settles it is one declaration**, with
`envSetAt-ident`'s exact signature shape plus a `lookup bi γ ≡ B₀` premise, then
five one-line applications. GO if all five close.

**P-l applies, and it bites the direction the brief did not expect.** The rate
generalizes as a per-SHAPE cost. It does not generalize as a per-FIELD cost,
because the thing measured is a copy, and a copy is not a marginal.

## Q2. WAS THE 255 REALLY BUILT ON 1.5 LINES PER ENTRY?

**Yes. And the comparison against it is a category error. MEASURED.**

**The 255's provenance is `agents/tasks/LJ-1-173/lj-1.173-report.md:1946-1960`**,
which revises `[LJ-1.168]`'s 271. `[LJ-1.168]`'s table is at
`agents/tasks/LJ-1-168/lj-1.168-report.md:338-351`. It has two kinds of row:

| row | what it prices | lines |
|---|---|---:|
| L1 to L9 | NINE supporting lemmas, one per proof shape | **229** |
| the last row | 28 field entries at about 1.5 lines | **42** |
| | the priced figure | **271** |

**The 1.5 is the price of an INSTANTIATION, not of a proof.** The report says so
in the next paragraph: a field entry is an instantiation, not a proof
(`:359-360`). **229 of the 271 lines, 85 percent, are shape lemmas. The entry
row is 15 percent.** `[LJ-1.173]:1959` carries the 42 forward unchanged.

**`[LJ-1.255]` measured the unfactored form and compared it to the factored
budget.** Its 11 proof lines per field are the shape lemma written again at each
field. The budget writes the shape lemma once, as L3 at 30 lines, then pays 1.5
per field.

**Three of the nine budget rows now have measurements. All three came in at or
under budget. MEASURED.**

| budget row | 255 gives | measured | at |
|---|---:|---:|---|
| L3, `⊨ envSetAt → E ≡ envSetGen` | 30 | **25** | `ProbeLJ1255.agda:199-223` |
| L4, `⊨ envOverAt → z ∈ K` | 12 | **11** | `:227-234` plus `:237-239` |
| L9, `envSetK` | 25 | **13** | `:90-95` plus `:97-103` |

**`[LJ-1.255]` never compared its measurements to the L1-L9 rows.** It attacked
the 15 percent row with a form the table does not use, and it left the 85
percent unexamined. **The 85 percent is confirmed where it has been tested.**

**The refutation's arithmetic double counts.** The report gives 297 to 459 for
the remaining 27 (`lj-1.255-report.md:114-115`), which is 27 x 11 and 27 x 17.
**The 17 includes the field SIGNATURE, and the same report says at `:43-45` that
the signature is already written in the `TFacts` record.** It is:
`src/L/Condensation/TwelveAgree.lagda.md:186-191` and `:192-197` hold `envK-mem`
and `envK-neg` in full. **So 459 counts lines the tree already holds.**

**And the band is stated「before shared lemmas」against a figure that IS shared
lemmas.** 297 to 459 plus L1 to L9 is 526 to 688. `dev/PLAN.md:807` now reads
「step 6 is 297 to 459 before shared lemmas, not 255」. **That compares a
marginal-only figure against a figure that is 85 percent shared lemmas.**

**One arithmetic note on the 255 itself, offered and not load-bearing.**
`[LJ-1.173]:1952-1960` sums 25 + 12 + 25 + 15 + 154 + 42, which is 273, and
prints 255. Its own section 38.2 at `:1017-1023` uses 181 for the last two rows,
which is correct, so the「other six lemmas」row should read 139 and not 154. **The
figure reproduces as 258 from its own deltas.** The 3-line gap changes no
decision.

## Q3. ARE THE FOUR `envInK-*` BLOCKED, AND IS THE POWER CLOSURE ABSENT?

### 3.1 The blockage is real, and its cause is a defect in `[LJ-1.173]`'s cure table

**Re-derived at the source, as the brief asked. MEASURED.**
`src/L/Condensation/TwelveAgree.lagda.md:217`, `:223`, `:229` and `:235` each
give the premise `⟨ fst ar ∈ fst (lookup (suc⁶ K) γ') ⟩`. **No numeral equation
appears in any of the four telescopes.** The five `envK-*` at `:187`, `:193`,
`:199`, `:205` and `:211` do carry `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁`. **So the
report's reading is correct.**

**The cause is at `agents/tasks/LJ-1-173/lj-1.173-report.md:843-846`.** That
cure table has two rows. Row 1 assigns the four `envInK-*` the hypothesis
`ar ∈ K`. Row 2 assigns the five `envK-*` the numeral equation. **Row 2 is the
row that makes the join usable, and the four `envInK-*` did not get it.**
`[LJ-1.173]:1974` records the sweep as complete for 21 fields, so the wrong cure
reached the master. **`[LJ-1.255]` found a real defect and it should be kept.**

**But BLOCKED overstates it, and the master says why.**
`src/L/Condensation/TwelveAgree.lagda.md:298-301` states that the numeral
restriction costs the consumers nothing, and it names the supply chain:
`codesK` gives the code's shape, `arityNumAtL` gives the numeral, `pr-inj`
closes both into `fst ar ≡ # n`. **That chain is DELIVERED**, at
`src/L/Coding/CodeSet.lagda.md:185-204` (`arityNumAtL` and `arityNumAtL-out`),
and `codesK` is a sibling field at `src/L/Condensation/TwelveAgree.lagda.md:162`.
**So the fix is the telescope edit `[LJ-1.173]` already made to `envSetK`
itself, applied to four more fields.** `[LJ-1.255]` could not make it because
its own brief forbade master edits (`agents/tasks/LJ-1-255/LJ-1.255.md:73`).
**The four are blocked by the task's scope, not by mathematics. MEASURED.**

### 3.2 The general-arity power closure is not hiding. It is REFUTED

**MEASURED, and it is stronger than the report's negative.**
`src/L/Condensation/TwelveAgree.lagda.md:292-297` says in the master's own
comment that at an unrestricted `ar` the field asks a LEVEL to hold the full
constructible function space, that a successor-closed limit does not, and that
**the general form is FALSE at the bound `HullStage` gives**. The witness is
`agents/tasks/LJ-1-172/lj-1.172-report.md:758-772`, a rank counterexample at
`lam = +ω ω` with `B = ar = Lset ω`, and that report marks it INFERRED, not
built in Agda (C-36).

**A sweep of every archive found no supplier. MEASURED, and the filters are
named.** `grep -rn "envSetGen" archive/ dev/` returns nothing, including inside
the 1.6 MB `archive/src/2026-08-09-rud-route/rud-route-src.patch`. A
`(n : ℕ)`-signature filter against `∈ Lset|Jset|Sset|𝒟ₒ|InJ` conclusions over
`src/`, all eight directories under `archive/src/`, `archive/dev/`, `dev/` and
`agents/` found no statement of the wanted shape. **The only statement of that
shape in live `src/` is the `TFacts` field at `:302-306`, which is a hypothesis
and not a lemma, and which carries the numeral premise.**

**The archive DOES hold a general-arity power closure of a different shape, and
the brief was right to ask.**
`archive/src/2026-08-09-rud-route/L/Rud/SatSets.lagda.md:270-272` proves
`hUs : (n : ℕ) → InJ (Us n)` in two lines by induction on `n`, where `Us n` is
the n-fold power of the carrier. **It is not a supplier here:** `Us n` is a
right-nested tuple space, not `envSetGen`'s function graph with domain exactly
`ar`. **I report it because a later dispatch will otherwise re-ask this
question.**

### 3.3 The qualifier the report dropped

**「NOT delivered」understates a refutation, and the report's own brief says to
carry a claim's qualifier or carry neither**
(`agents/tasks/LJ-1-255/LJ-1.255.md:101`). `lj-1.255-report.md:69` and
`ProbeLJ1255.agda:354-355` both write「NOT delivered」. **A reader takes that as
work to fund. The master at `:292-297` says the statement is false.**

**A second ambiguity, worth one line.** In this tree `# n` is a numeral-shaped
set built from a free `(n : ℕ)`. **The numeral restriction does not pin the
arity to 0, 1, 2 or 3.** `src/L/Coding/Key.lagda.md:475-478` delivers
`envSetNumeral∈` at fully general `n : ℕ` with a bound of `sucIter 4 σ` uniform
in `n`. **So「general-arity」in the report means「set-level `ar` with no numeral
equation」, and it should say so.**

### 3.4 `someEnv`'s second blocker is DELIVERED, and this is the review's largest correction

**`lj-1.255-report.md:84-86` prices `E ⊨ envSetB` as「the adequacy join
`[LJ-1.173]` section 3.4 priced at about 120 lines」. MEASURED FALSE.**

**The transfer is delivered, green, in the live master, and it is four lines.**
`src/L/Condensation.lagda.md:3042-3045`:

```agda
  back : ⟨ γ ⊨ envSetAt E ar B ⟩ → ⟨ γ ⊨ envSetB E ar B K ⟩
```

The `out` direction sits beside it at `:3036-3039`. Both live in
`module EnvSet` (`:2926`), whose comment at `:2917-2925` says it gives BOTH
directions of the bounded `envSetB` against the machine's `envSetAt`. **The
120-line figure at `agents/tasks/LJ-1-173/lj-1.173-report.md:156-165` prices a
DIFFERENT join, and `[LJ-1.173]:871` records that its expensive half is now
DELIVERED in `src/L/Coding/Key.lagda.md`.** `adequate` is at
`src/L/Coding/Key.lagda.md:400-403`, both directions.

**So `someEnv` is not blocked twice. It is blocked once**, on the same numeral
question as the four `envInK-*`, and its environment CONSTRUCTION remains
UNMEASURED, exactly as `[LJ-1.254]:72` said. **This is the third time this week
that a delivered term was reported absent, and this time it was the live master
and not the archive.**

## Q4. DID YOUR BRIEF CAUSE IT?

**Partly. MEASURED from the brief's own text.**

**The framing asked for a rate and named no form.**
`agents/tasks/LJ-1-255/LJ-1.255.md:43-45` says the number that matters is the
marginal cost per field, and asks for the eleven fields' lines apart from any
shared setup. **「Apart from shared setup」is the phrase that did the damage.** It
tells the agent to subtract the shared lemmas and report what is left. **Under
DD4 the correct answer is to MOVE the repeated shell into the shared lemma and
report a near-zero remainder.** The brief's phrasing rewards the opposite.

**`[LJ-1.255]` did not choose the cheapest group. It built what the brief
named.** The brief's table at `:20-23` lists the five `envK-*` first, and
`:36` says to start from `ProbeLJ1254.agda`. The five are the group whose
supporting lemma `envSetK` was already green. **So the selection was the
brief's, not the agent's.**

**The bias direction: the rate is biased UP, not down. MEASURED.** The five
`envK-*` are the group with the most sharing, so a per-shape rate taken here is
the cheapest available. **But the reported figure is a per-FIELD rate on
unfactored code, and that is the most expensive way to write the cheapest
group.** The two biases do not cancel, and the second is the larger.

**One more brief effect.** `[LJ-1.255]`'s brief forbade master edits at `:73`.
Three of its four blocked items need one telescope edit each. **The brief made
its own BLOCKED verdict.**

## THE ONE REAL OVERRUN, which neither report named

**`sucK` is the measured hole, and it was measured a day before the refutation.
MEASURED.**

`sucK` is one of the 28 obligations (`agents/tasks/LJ-1-254/lj-1.254-report.md:51`
and `dev/PLAN.md:47`), though it is a module telescope parameter and not a
`TFacts` field (`src/L/Condensation/TwelveAgree.lagda.md:126-128` and `:336`).
It is a singleton: **no L row in the nine-lemma table prices it.**

| item | budget | measured | at |
|---|---:|---:|---|
| `sucK`'s entry | 1.5 | **about 20** | `ProbeLJ1255.agda:161-181` |
| `union∈Lset-suc`, its supporting lemma | **no row** | **about 52** | `:105-159` |

**So one entry of the 28 consumed about 72 lines against a 1.5-line allowance,
and 52 of those lines have no row at all.** That is the largest measured
departure from the 255 anywhere in this chain, and it is about +50 after the
three under-budget rows are netted off.

**One thing could remove it, and it is INFERRED.** `[LJ-1.254]:50` says
`union∈Lset-suc` was adapted from `L.Axioms.Basic.UnionOf.mkUnion`, which is
delivered at `src/L/Axioms/Basic.lagda.md:661-662`. **Its shape differs**: it
returns a `SetOf Q` and not `⟨ ⋃ x ∈ Lset (sucV σ) ⟩`. **Whether the master's
supply can call it directly is INFERRED and one probe settles it.**

## C-42 BOTH DIRECTIONS

**FURTHER: does the entry-estimate claim reach `[LJ-1.168]`'s other figures?
NO. MEASURED.** The claim is overturned, so it reaches nothing. **And the
nine-lemma table gains support rather than losing it:** three of its nine rows
now have measurements and all three came in at or under budget (Q2's table).
**The one row under real pressure is the 42-line entry row, and only through
`sucK`, which is a singleton the table never gave a lemma.** The nine-lemma
table is cited across this layer and it stands.

**LESS FAR: does any of this reach the green work? NO. MEASURED.**
`[LJ-1.254]`'s `envSetK` and `sucK` and `[LJ-1.255]`'s five `envK-*` all exit 0
and no finding here touches a typechecked term. **The dispute is about a price
and about how the same proof should be written, never about whether it closes.**
`[LJ-1.255]`'s section 4 DD4 correction is also CORRECT and stands: the probe's
`envSetK` is B₀-fixed (`ProbeLJ1255.agda:97-99` takes no `B` and no `B ∈ K`),
and the shareable form is the general `TFacts` field at
`src/L/Condensation/TwelveAgree.lagda.md:302-306`, still unbuilt.

**`t0eq` and `t1eq` at zero also stands. MEASURED.**
`src/L/Condensation.lagda.md:3063-3067` defines both as `Type`-level premises at
the consumer's own site, exactly as `[LJ-1.255]:91-100` reports.

## PER-TOWER FIGURE (DD4)

**The per-tower share does NOT rise, because the marginal rate that would have
raised it is overturned. It falls slightly.**

`[LJ-1.113]:219-239` splits 29 facts into 25 coding and 4 per-tower (`t0eq`,
`t1eq`, `t0K`, `someEnv`). `[LJ-1.254]:58` removes `t0K` as provable, leaving 3
per-tower of 28.

**What the 3 now cost: about 25 lines, and two of the three are MEASURED zero.**

| per-tower field | cost | class |
|---|---|---|
| `t0eq` | **0** | MEASURED, `src/L/Condensation.lagda.md:3063-3067` |
| `t1eq` | **0** | MEASURED, the same lines |
| `someEnv` | **about 25**, L8's row, with the `envSetB` half DELIVERED | the environment construction is UNMEASURED |

**So the J tower's re-payment for `[LJ-1.7]`'s residue is about 25 lines of
about 290, near 9 percent.** `dev/PLAN.md:47` carries「about 28 lines, about 7
percent」. **The line figure holds. The percentage moves only because the
denominator moved.** `[LJ-1.248]`'s 146 to 196 for A-prime is untouched by
anything here.

## EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| the 255 implies 9.1 lines per field | **MEASURED FALSE.** It is 213 shape lemmas plus 42 entries, `[LJ-1.168]:338-351` |
| the 17-line rate is a marginal | **MEASURED FALSE.** Five copies of one proof, `ProbeLJ1255.agda:260-342` |
| the other 23 fields share less | **MEASURED FALSE.** 6 shapes plus 2 singletons, `[LJ-1.168]:356-360` |
| the 1.5-line entry estimate is real | **MEASURED TRUE.** `[LJ-1.168]:350`, carried at `[LJ-1.173]:1959` |
| the entry estimate is a sevenfold undercount | **MEASURED FALSE as stated.** 11 against 1.5 compares unfactored code to a factored budget |
| the four `envInK-*` lack the numeral premise | **MEASURED TRUE.** `TwelveAgree.lagda.md:217, :223, :229, :235` |
| the four are BLOCKED | **MEASURED FALSE.** The supplier chain is delivered at `CodeSet.lagda.md:185-204`; the block is the brief's no-master-edit rule |
| a general-arity power closure is「NOT delivered」 | **MEASURED TRUE but under-qualified.** It is REFUTED, `TwelveAgree.lagda.md:292-297` |
| the archive holds a supplier | **MEASURED FALSE** for `envSetGen`; zero hits in `archive/` and `dev/` |
| `someEnv` needs a 120-line adequacy | **MEASURED FALSE.** `back` is four lines at `src/L/Condensation.lagda.md:3042` |
| the five `envK-*` are green | **MEASURED TRUE.** exit 0, unchanged by this review |
| `t0eq`/`t1eq` cost zero | **MEASURED TRUE.** `src/L/Condensation.lagda.md:3063-3067` |
| the factored `envK-gen` closes | **INFERRED.** I did not run Agda; one declaration settles it |
| `mkUnion` removes the 52 lines | **INFERRED.** The shapes differ at `Basic.lagda.md:661` |
| I ran Agda, edited a master, or committed | **MEASURED FALSE.** Only `agents/tasks/LJ-1-256/lj-1.256-report.md` was written |

## C-44: WHAT THIS BRIEF STATES THAT I DID NOT CHECK

- **`[LJ-1.251]` confirmed the 255 two dispatches ago.** I did not open
  `agents/tasks/LJ-1-251/`. **Treat that attribution as unproven here.**
- **The brief's「about 400」is 255 plus a 147-line comparable
  (`dev/PLAN.md:47`).** I checked the 255 half only.
- **The brief glosses P-l as the analogy rule.** CONFIRMED at
  `dev/LESSONS.md:2345`. **Note that `scripts/rules.py --for review` prints only
  P-l's heading and first paragraph, which are about stage presentation, and it
  truncates before line 2345.** An agent that reads only the tool output will
  miss the clause the brief cites.

## ARCHIVE USED (DD18)

One line read named per file.

- `agents/tasks/LJ-1-255/lj-1.255-report.md`, read WHOLE. **Line read `:107`**,
  the「about 11 proof lines, a ~7x undercount」claim this review tests.
- `agents/tasks/LJ-1-255/ProbeLJ1255.agda`, read WHOLE. **Line read `:264`**,
  `envK-mem`'s `go` body, which `:282`, `:300`, `:318` and `:336` repeat.
- `agents/tasks/LJ-1-168/lj-1.168-report.md`, read section 4. **Line read
  `:350`**, the 28 entries at about 1.5 lines, inside a 271-line table.
- `agents/tasks/LJ-1-254/lj-1.254-report.md`, read WHOLE. **Line read `:50`**,
  `union∈Lset-suc` adapted from `mkUnion`, the lemma with no budget row.
- `agents/tasks/LJ-1-173/lj-1.173-report.md`, read sections 3.4, 31, 32, 38 and
  68. **Line read `:846`**, the cure table row that gave the five `envK-*` the
  numeral and left the four `envInK-*` without it.
- `agents/tasks/LJ-1-113/lj-1.113-report.md`, read `:215-240`. **Line read
  `:219`**, the 25-against-4 split before `t0K` was removed.
- `agents/tasks/LJ-1-172/lj-1.172-report.md`, read `:752-772` through the sweep.
  **Line read `:758`**, the rank counterexample that refutes the general form.
- `src/L/Condensation/TwelveAgree.lagda.md`, read `:120-320`. **Line read
  `:292`**, the master's own note that the general form is FALSE.
- `src/L/Condensation.lagda.md`, read `:2917-3080`. **Line read `:3042`**,
  `back`, the four-line transfer the report priced at 120.
- `archive/dev/TASKS-archived.md`, read the header. **Line read `:10`**, the 264
  rows recording which approaches were measured on the retired route.
- `archive/src/2026-08-09-rud-route/`, 74 files surveyed. **Line read
  `L/Rud/SatSets.lagda.md:271`**, `hUs`, a general-arity power closure at a
  tuple space, which does not supply `envSetGen`.

## LITERATURE USED (DD18)

**The literature does NOT bound the number of environment facts, and 28 is an
artifact of the coding. MEASURED as a read.** `dev/literature/devlin-II5.md:246-255`
says Devlin binds every unbounded quantifier by the concrete set `K(u)`, the
finite sequences over the formula set, and that **the argument does not require
them to have any particular shape, only that some bounded description with a
bound inside the carrier exists**. **One bounded description is the requirement;
28 satisfier-in-K closures is this machine's way of meeting it.** The finite
sequences at `:248` are also why the numeral restriction is Devlin's form and
not a defect, which agrees with `[LJ-1.254]:152` and `[LJ-1.255]:194-202`.

**WHY NOT the rest.** I read no other source. The question is a line count in
this tree, and no text prices Agda lines.

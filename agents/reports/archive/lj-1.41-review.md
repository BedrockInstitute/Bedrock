# LJ-1.41 review (DD25): the nine unclosed rows

Status: COMPLETE. Written incrementally per C-22. ASD-STE100.
Probes: `src/ProbeDD25F41A.agda` to `src/ProbeDD25F41D.agda`, untracked,
never committed. No master was touched. No commit, no push.

## 1. THE VERDICT

**OVERTURN.**

The return's COUNT is correct: nine rows do not close as delivered.
The return's REASON is wrong, and the wrong reason is the part that
stops the phase.

The return says this (`_build/lj-1.41-report.md:48-51`):

> The bounded quantifiers cannot be lifted to the unbounded ones by
> any site fact, and a Delta-0 witness does not exist for the
> unbounded `envSetAt` ... so the rows cannot be made equivalent
> within the Delta-0 constraint.

Both halves are refuted, machine-checked, at 8 GB and one process:

| probe | what it does | user s, two cold runs | result |
|---|---|---:|---|
| `src/ProbeDD25F41A.agda` | a Delta-0 witness for a two-way K-bounded environment-set condition | 1.50, 1.45 | **GREEN** |
| `src/ProbeDD25F41B.agda` | BOTH directions between that condition and the machine's `envSetAt` | 1.70, 1.67 | **GREEN** |
| `src/ProbeDD25F41C.agda` | the same at the Top row's own frame, and `envHypT` is its first conjunct | 1.55, 1.55 | **GREEN** |
| `src/ProbeDD25F41D.agda` | the delivered `envHypT` plus ALL THREE site facts against `envSetAt` | 1.48 | **RED**, as designed |

The import cone is 1.37 seconds (`src/ProbeLJ141Ctrl.agda`,
re-measured). So the whole cure's environment machinery costs about
0.22 seconds.

The Delta-0 witness the return says cannot exist is one line:

```agda
envSetB E ar B K =
  extAtB E K (envBndGen zero (suc E) (suc E) (suc ar) (suc K) (suc B))

Δ₀-envSetB E ar B K =
  Δ₀-extAtB E K _ (Δ₀-envBndGen zero (suc E) (suc E) (suc ar) (suc K) (suc B))
```

Both parts are delivered. `extAtB` and `Δ₀-extAtB` are at
`src/L/Condensation.lagda.md:82-92`. `envBndGen` and `Δ₀-envBndGen`
are at `:506-537`.

**The return asked the wrong question.** It asked for a Delta-0
witness of the machine's UNBOUNDED formula. Nothing in this file ever
needs one. Every leaf here is a K-BOUNDED Delta-0 restatement that
reaches the machine's unbounded form under site facts. `subValB`
reaches `subValAt` (`:2787-2804`). `subValSuccB` reaches
`subValSuccAt` (`:2806-2832`). `tmValB` reaches `tmValAt`
(`:2686-2785`). `extAtB` reaches `extAt` (`:2834-2841`). The
environment condition is not different in kind, and the same block
built three of those four transfers.

**The real defect is smaller, and it is the SAME defect `[LJ-1.40]`
already cured one layer down.** The machine's `extAt` is a PAIR of
implications (`src/L/Coding/Model.lagda.md:662-664`). The story wrote
the first and stopped. `[LJ-1.40]` found exactly that at the value
frame and cured it with `extAtB`; it did not ask the same question at
the environment frame.

**And the same defect is in BLOCK 1, since `[LJ-1.5]`.**
`Clause.envHyp` (`src/L/Condensation.lagda.md:175-176`) is one
conjunct where the machine's `existClauseAt` wants two
(`src/L/Coding/Model.lagda.md:1607-1615`). See section 6.5. The next
brief must cover block 1 as well as the nine rows.

## 2. DOES THE Δ₀ CERTIFICATE NEED TO COVER THE ENVIRONMENT CONDITION?

**YES, it does. The save does not work. But the save is not needed,
because the environment condition HAS a Delta-0 form.**

Two facts close the question.

**First: the environment condition is inside the object-language
formula, not beside it.** All four row frames put `env` in as an
antecedent:

- `unFullAt` (`src/L/Condensation.lagda.md:651-670`) ends
  `sub ⇒̇ (env ⇒̇ body)`;
- `unEnvAt` (`:672-689`), `binFullAt` (`:708-728`) and `binEnvAt`
  (`:730-751`) do the same.

The row's Delta-0 certificate is therefore built THROUGH the
environment certificate. `Top.Δ₀-topBndAt` calls `Δ₀-envHypT`
(`:1109-1112`), and every other row does the same. There is no seam
where the condition could be an Agda-level hypothesis instead.

It could not be one anyway. The row is the DEFINITION of the
satisfaction table's clause. If the environment condition moved out of
the formula, the formula would assert the row's body for EVERY E in K,
which is false. That is the same failure mode as the vacuity defect
`[LJ-1.38-R]` refuted.

**Second: the Σ₁ certificate buys one binder and nothing else.** The
row certificates are `∃̇ φ` with `σ-∃ (σ-Δ₀ d)`, where the one
existential binds the class carrier K itself: `topCertAt`
(`:1794-1796`), `existCertAt` (`:246-252`), and nine more of the same
shape. `Σ₁` has one base and one step
(`src/FOL/LevyHierarchy.lagda.md:73-75`), so a Σ₁ certificate is a
stack of unbounded existentials on a Delta-0 matrix. `[LJ-1.34-R]`
settled this and said so: "The Σ₁ relaxation buys one binder at the
root and nothing else. This line of attack fails"
(`_build/lj-1.34-review.md:180-181`).

So `[LJ-1.5]`'s two certificates split as follows. The Δ₀ witness
covers the WHOLE matrix, environment condition included. The Σ₁
certificate covers ONE outer existential over K. The environment
condition sits deep inside the matrix and gets no relief from the
outer layer.

**The save fails, and it did not need to succeed.** A Delta-0 form of
the environment-SET condition exists. `ProbeDD25F41A` builds it and
`ProbeDD25F41C` proves it is Delta-0 at the Top row's own frame.

## 3. IS THE BLOCKER REAL AS STATED?

**The blocker is REAL. The impossibility claim attached to it is NOT.
The probe the return cites proves the first and not the second.**

I re-ran `src/ProbeLJ141C.agda` at `GHCRTS="-A64m -I0 -M8g"`. It is
RED, in 1.44 seconds of user time. So the return's measurement stands.

**But read what the probe asks.** Its body is `try B K γ E henv =
henv` (`src/ProbeLJ141C.agda:46`). It hands one hypothesis to a
different type, unchanged. Agda answers that the two types are not the
same type. Agda was never asked whether one IMPLIES the other, and
Agda cannot answer that by refusing a coercion.

The error text is the useful part, and it names the real defect:

```
(x : S) → ⟨ x ∈ ⟦var zero⟧ ⇒ ((x ∷ E ∷ γ) ⊨ envBndGen ...) ⟩
  !=<
Σ ⟨ (E ∷ γ) ⊨ ∀̇ ((var zero ∈̇ var (suc zero)) ⇒̇ envOverAt ...) ⟩
  (λ _ → ⟨ (E ∷ γ) ⊨ ∀̇ (envOverAt ... ⇒̇ (var zero ∈̇ var (suc zero))) ⟩)
```

A Π on the left; a Σ of two Π on the right. The story supplies ONE of
the machine's TWO components. **The gap is a missing conjunct.** It is
not a gap between bounded and unbounded quantifiers, which is what the
return concluded from it.

`src/ProbeDD25F41D.agda` is my control for the same claim, and it is
stronger. It hands the delivered `envHypT` to the machine's `envSetAt`
WITH all three site facts in scope, through a transfer that is known
to work. Agda still refuses, and its message shows `envHypT` sitting
in the first slot of the pair with the second slot empty. So the site
facts are not what is missing. The conjunct is.

**A failed substitution is not a proof of impossibility, and this one
was read as if it were.** D-1's abort criterion must be fixed before
the probe runs; `ProbeLJ141C`'s header sets the expectation ("EXPECTED:
a type error") but never states what a type error would license. The
report then licensed a phase-stopping conclusion from it.

## 4. IS `envSetAt` DERIVABLE FROM WHAT THE ROWS CARRY?

**Not from what they carry today. YES from what they carry plus one
conjunct and three site facts, and `src/ProbeDD25F41B.agda` builds
it.**

The probe proves both directions:

```agda
out  : ⟨ γ ⊨ envSetB E ar B K ⟩ → ⟨ γ ⊨ envSetAt E ar B ⟩
back : ⟨ γ ⊨ envSetAt E ar B ⟩ → ⟨ γ ⊨ envSetB E ar B K ⟩
```

`out` is `extAtB→extAt`, `back` is `extAt→extAtB`, both delivered at
`src/L/Condensation.lagda.md:2398-2416`. The leaf pair they need is
`bnd→over` and `over→bnd`, which the probe writes generically in about
50 lines of Agda. `over→bnd` is the delivered `EnvB2T.over→bnd`
(`:2647-2682`) made generic in the slots; `bnd→over` is new.

**The three site facts.**

1. `entryK`: the two components of an entry of a candidate environment
   lie in K.
2. `arSubK`: the arity's members lie in K.
3. `envInK`: every environment over `ar` with values in `B` lies in K.

`envInK` is the only one that binds new work, and it is **not a new
species of fact**. `[LJ-1.35]` already enumerated exactly this fact
for `extAtB`: "the bounded ext's second conjunct needs every satisfier
of the body inside K" (`_build/lj-1.35-report.md:46`, from
`src/ProbeDD25D2.agda:121-123`). My `envInK` is that same fact with
the environment body in place of the value body. The block that
introduced `extAtB` registered the obligation; the environment
instance of it was never registered.

`entryK` and `arSubK` follow from K's transitivity plus `pairsInAt`,
which every candidate environment already satisfies as conjunct four
of `envBndGen` (`:534-537`). K's transitivity is already in the
delivered hypothesis bundle (`PropAgree`'s `transK`,
`src/L/Condensation.lagda.md:2870-2871`).

**So the return's sentence "no site fact does it" is false twice.** A
site fact of exactly the registered shape does it, and the machinery
that consumes it was written by this same block.

## 5. DID THE BRIEF CAUSE IT?

**NO. Your brief did not lock the shape, and it named the cure.**

The `envHyp*` shape predates `[LJ-1.37]`. It was born in `[LJ-1.5]`,
block 1, as `envHyp = ∀̇∈ (var zero) envBnd`
(`src/L/Condensation.lagda.md:175-176`, unchanged since commit
`f48ffd7`). `[LJ-1.37]` only generalized that one formula into the
four-layout family. No document from `[LJ-1.5]`, `[LJ-1.37]` or
`[LJ-1.40]` records a decision to drop the second direction. It was
never written down, and never argued for.

**Your brief pointed at the cure and the agent looked past it.**
`_build/briefs/LJ-1.41.md:29-31` says the environment transfer exists
for the ATOM layout only and that the other three layouts need their
own instances, and calls it "the one piece of genuinely new
machinery". The return then says it did not use `EnvB2T` at all and
questions whether it is needed (`_build/lj-1.41-report.md:209-213`).

**One line of the brief deserves a note, though it did not cause the
outcome.** `_build/briefs/LJ-1.41.md:73` says "do not weaken the
statement to make it close". That is right. It has no matching line
saying a row may be STRENGTHENED to make it close, and the cure here
is a strengthening: `envSetB`'s first conjunct is `envHypT`, proved at
`src/ProbeDD25F41C.agda`'s `keeps-envHypT`. An agent that reads only
the "do not change the statement" side has no licence to add the
conjunct. **Add the other half to the next brief:** a row that is too
weak against the machine must be strengthened, and only a weakening is
forbidden.

`[LJ-1.40]` is where the miss belongs. It found this exact defect at
the value frame, named it in the same words, and cured it with
`extAtB` (`_build/lj-1.40-report.md:121-133`: "The story's defect was
writing only one direction and bounding it by the value itself instead
of by K"). It did not run the same test on the environment frame. That
is D-29's second face, and the file's D-29 entry came from this file.

## 6. THE REAL WAY OUT, AND WHAT IT COSTS

**The way out is to write the conjunct the story never wrote.** Do not
re-lay the environment layer. Do not accept a one-way bridge.

### 6.1 The change

Replace each `envHyp*` by `extAtB E K envBndGen`, which is the same
formula with the second conjunct added. Four definitions and four
Delta-0 certificates at `src/L/Condensation.lagda.md:584-650`. The
Delta-0 certificate stays one line per layout. **Every consumer of
`envHyp*` keeps working through `.fst`**, machine-checked at
`src/ProbeDD25F41C.agda`.

Then add ONE generic leaf transfer, both ways, and ONE generic
environment-set transfer. `src/ProbeDD25F41B.agda` is that code. It
is 98 lines of Agda and it is written generic in the slots, so ONE
copy serves all four frame layouts and both towers. `EnvB2T`
(`:2647-2682`) is its `over→bnd` half at one layout, and it is
superseded by the generic form.

### 6.2 The price of the environment half, MEASURED HERE (P-l)

| file | Agda lines | cold user s | s per line |
|---|---:|---:|---:|
| `src/ProbeDD25F41A.agda` | 9 | 1.45 | cone-dominated |
| `src/ProbeDD25F41B.agda` | 98 | 1.67 | n/a |
| marginal, B over A | 89 | **0.22** | **0.0025** |

The import cone is 1.37 seconds, re-measured with
`src/ProbeLJ141Ctrl.agda` in this session. So the environment
machinery costs **about 0.22 seconds for about 100 lines**, one fifth
of DD24's bar. **The environment half of the cure is cheap.**

### 6.3 The price of the nine agreements, and a WARNING

This block's own marginal rate is the basis, and it is not cheap.

- HEAD `6ff213a`: 2,498 in-fence lines, 12.79 seconds cold (the
  brief's own re-measurement, `_build/briefs/LJ-1.41.md:19`).
- Working tree: 2,805 in-fence lines. **I re-measured it cold at 24.09
  seconds of user time, and it is GREEN.** The return's 23.93 stands.
- Marginal: 11.30 seconds for 307 lines = **0.0368 seconds per line**,
  which is 2.8 times DD24's bar of 0.013193.

Three of the four frame layouts still need their shared agreement
module, and `PropAgree` (`:2857`) should serve the `binFullAt` layout
for Imp, AllIn and ExIn without a new module. So the remaining work is
about three shared modules at `PropAgree`'s caliber, nine
instantiations at `AndAgree`'s caliber, and the environment machinery:

    3 x 240 + 9 x 48 + 140  =  about 1,290 lines

At 0.0368 seconds per line that is **+47 seconds**, giving about 71
seconds over about 4,100 lines, or **0.0175 seconds per line: a DD24
breach by about one third**.

**State this once and act on it** (DD8). The projection rests on one
marginal measurement of one block. It disagrees by 15 times with my
own measurement of the environment machinery (0.0025) and by 5 times
with `[LJ-1.34-R]`'s agreement content (0.0072,
`_build/lj-1.34-review.md:8-13`). **The widest unmeasured term for the
next block is therefore not the environment condition. It is what
inside `PropAgree` costs 0.037 seconds per line**, and P-v names the
suspect: a satisfaction-level conversion that a transport would
replace. **Measure that before funding three more modules of the same
shape.**

### 6.4 The one new site fact, and why it is not new

`envInK` says every environment over `ar` with values in `B` lies in
K. It is needed for the machine-to-story direction only. The
story-to-machine direction needs no site fact beyond `E in K`, which
the bundle already has.

`[LJ-1.35]` registered this fact when `extAtB` was introduced: "the
bounded ext's second conjunct needs every satisfier of the body inside
K" (`_build/lj-1.35-report.md:46`). The environment instance is the
same fact at a different body.

**And it is the mathematics, not an accident.** The bounded condition
says E is the environment set AS K SEES IT. The machine's condition
says E is the environment set. The two agree exactly when K is closed
under the environments. A condensation argument needs that closure
anyway.

### 6.5 THE DEFECT IS ALSO IN BLOCK 1, AND IT HAS BEEN SINCE `[LJ-1.5]`

I checked this because the shape looked familiar. It is the same
shape.

- `Clause.envHyp = ∀̇∈ (var zero) envBnd`
  (`src/L/Condensation.lagda.md:175-176`). ONE conjunct. `envBnd`
  (`:111-134`) is the same four-conjunct bounded environment condition
  as `envBndGen`.
- `Clause.existBndAt` (`:187-195`) consumes it as `envHyp ⇒̇ extBnd`.
- The machine's `existClauseAt` (`src/L/Coding/Model.lagda.md:1614`)
  is `unClauseAt C T 8 (quantRel T B (body∃ B))`, and `quantRel`
  (`:1607-1611`) consumes `envSetAt E6' ar6' (sh6' B)`. TWO conjuncts.

So block 1's bounded matrix is weaker than the clause it restates, in
exactly the way the nine rows are. **`[LJ-1.5]`'s own report recorded
the symptom and nobody read it as this:** "The matrix-to-clause link
is unproven. Nothing shows the bounded matrix says what the delivered
`existClauseAt` says" (`_build/lj-1.5-report.md:210-213`).

**Consequence for the orchestrator.** Block 1 has no consumer that
tests it against the machine, so C-35 applies to it. The cure of 6.1
covers it: `Clause.envHyp` takes the same second conjunct, and its
Delta-0 certificate stays one line. Add block 1 to the next brief's
scope; do not let it ride as delivered.

### 6.6 What NOT to do

**Do not take the return's option two** (a one-way bridge,
`_build/lj-1.41-report.md:137-140`). C-35 makes the agreement the
row's only consumer. A row whose machine-to-story direction is missing
is a row nobody has tested against the machine, and this file has now
shipped two false theorems for exactly that reason (`[LJ-1.38-R]`,
C-35).

**Do not re-lay the environment layer** (the return's option one, as
the return reads it). The delivered `envHyp*` is correct as far as it
goes; it is conjunct one. Nothing about it must be rewritten.

## 7. WHAT I AM NOT SURE OF

1. **`envInK`'s truth at the class carrier is the load-bearing open
   question, and I did not settle it.** It holds when the arity is a
   numeral and K is a limit level, because the environments are then
   finite functions. I did not check that the row forces the arity to
   be a numeral, and `arTagB` (`:426-440`) may not. **If the arity can
   be infinite, `envInK` is false and the machine-to-story direction
   stays blocked**, for a precise and dischargeable reason, and not
   for the return's reason. Price this first.
2. **The strengthened row can go vacuous, and `someEnv` must be
   upgraded.** `PropAgree`'s `someEnv` (`:2885-2889`) produces an E in
   K satisfying `envHypB2`. With the cure it must produce an E
   satisfying both conjuncts. If no such E exists in K, the row is
   vacuously true and untested, which is the `[LJ-1.38-R]` failure
   again. I did not check that the upgraded `someEnv` is provable.
3. **I did not build a row agreement end to end.** I proved the
   environment step at the Top row's own frame and both directions of
   the transfer. The rest of each row is `BotAgree`'s and
   `PropAgree`'s worked pattern, and I am inferring that it composes.
   That inference is exactly the kind `[LJ-1.38]`'s review got wrong,
   so treat the nine rows as unproved until one is built.
4. **My site facts are hypotheses and I did not exhibit a model.** The
   three are jointly satisfiable by inspection (any large transitive
   K), but I did not build an instance, so a hidden inconsistency
   would make my probes vacuous. The RED control `ProbeDD25F41D`
   argues against vacuity: under the SAME three hypotheses Agda still
   refuses the one-conjunct version.
5. **The DD24 projection rests on one block's marginal rate.** See
   6.3. It could be off by a factor of five in either direction.
6. **The line count.** My in-fence counter gives 2,802 for the working
   tree against the return's 2,805. HEAD matches exactly at 2,498. The
   three-line gap is my counter's caliber, not a finding.
7. **Block 1 is settled, not uncertain.** See 6.5. I read both sides
   and they differ by the same conjunct. What I did NOT do is
   machine-check block 1's mismatch with a probe, as I did for the Top
   row. The evidence is two definitions read side by side.
8. **I did not re-measure the HEAD baseline myself.** 12.79 comes from
   your brief (`_build/briefs/LJ-1.41.md:19`) and 12.39 from the
   return. I measured only the working tree, at 24.09. Re-checking
   HEAD needs a second worktree and I judged the cost not worth it,
   because the two independent baselines agree to 3 percent.

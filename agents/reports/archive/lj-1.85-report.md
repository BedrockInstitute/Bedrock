# LJ-1.85: repair witK with a premise its consumer can supply

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.85-report.md`.

## 0. THE VERDICT

**The premise is `w ⊆ AllCodes A`. It kills the refutation (MEASURED),
and the closure supplies it at the consumer's witness (MEASURED). It
does NOT by itself make `witK` true at every admissible stage
(INFERRED). The making-true form needs the stage condition
`AllCodes A ∈ Lset lam`, which the tree does not deliver and no
consumer supplies (INFERRED absence). STOP per D-1: the chain is not
carried further.**

The two checked halves of the brief are machine-checked. Half 1: the
LJ-1.84 refuting witness fails the new premise, so the refutation
cannot be assembled; the red control `src/ProbeLJ185C.agda` shows the
adaptation literally does not typecheck. Half 2: the real witness of
`hasWitnessAt`, the subformula closure at
`src/L/Coding/CodeSet.lagda.md:365-373`, lies in `AllCodes A`, member
by member, machine-checked in `src/ProbeLJ185B.agda:58-68`.

The distinction the brief demands is kept: "the refutation fails" is
not "an inhabitant exists". No inhabitant of the repaired `witK` is
exhibited. The truth of the repaired statement at every admissible
stage rests on a stage condition that is a named absence.

## 1. THE PREMISE AND WHY

**The premise: every member of the witness `w` is a key of a formula
over the carrier `A` at some arity, i.e. `w ⊆ AllCodes A`.**
`AllCodes A` is the set of keys of formulas over the carrier at every
arity (`IsKeyOverAny`, `src/L/Coding/CodeSet.lagda.md:434-437`;
`AllCodes`, `:440-441`; `key∈AllCodes`, `:443-444`).

Why this premise. The LJ-1.84 junk member
`c₀ = pr K₀ (pr (# 6) (numeralL 0))` escapes shapedness because its
ARITY slot is the stage bound itself, and `shapes` puts no condition
on the arity slot (`src/L/Coding/Shape.lagda.md:104-105`, `:178-179`).
A key of a formula has a numeral as its arity slot:
`key {n} φ = pr (# n) VCode.⌜ mapFo f φ ⌝`
(`src/L/Coding/InL.lagda.md:252-253`). So a set whose members are all
formula keys cannot contain the junk member: its arity slot is a
numeral, and the stage bound is not a numeral at the chain's stages.
The premise pins exactly the slot `shapedness` leaves free.

The premise is not invented. The tree's own code-set predicate
already carries it as the conjunct that separates `isCodeAny` from
`hasWitness`: `isCodeAny A = arityNumAtL zero ∧̇ hasWitness A`
(`src/L/Coding/CodeSet.lagda.md:247-248`). The debt was recorded where
it was incurred: "Shapedness binds the arity existentially and puts no
condition on it" (`:24`), and the predicate "says, from outside, that
`x` is a pair whose first component is a numeral" (`:28-30`). The
premise is that conjunct, moved from the elimination predicate onto
the witness.

Only the premise changes. The conclusion of `witK`
(`src/L/Condensation.lagda.md:6227-6229`) is untouched, and nothing
under `src/L/Coding/` or `src/V/` is touched.

## 2. THE REFUTATION DIES

The adapted refutation must supply the new premise for the extended
witness `w = D ∪ {c₀}`. That needs `c₀ ∈ AllCodes A₀`. At the chain's
stage it is false, machine-checked:

- `c₀∉All` (`src/ProbeLJ185A.agda:107-112`): a member of
  `AllCodes A₀` peels via `AllCodes-out` to a key of a formula, so its
  arity slot is a numeral; `pr-inj` on the junk member's arity forces
  `fst K₀ ≡ # n`; `notNumeral` (`:89-92`) refutes it.
- `notNumeral`: `Lset lam ≡ # n` would put `Lset lam ∈ ω`
  (`#∈ω`), and transitivity of the stage
  (`layer-trans (Lset-layer lam)`) with `ω ∈ Lset lam` puts
  `Lset lam` inside itself, refuted by `∈-irrefl`
  (`src/V/Hierarchy.lagda.md:155-156`). `ω ∈ lam` is the LJ-1.80
  trichotomy route from `α∉ω`, `α∈λ` (`src/ProbeLJ185A.agda:75-82`);
  `ω ∈ Lset lam` is `Lset-cumul` plus `ord∈Lset-suc`
  (`:84-85`).

- The red control `src/ProbeLJ185C.agda:62-63` shows the adaptation
  literally does not typecheck: the premise term for the junk member
  cannot be written. Agda rejects `c₀∈All = key∈AllCodes A₀ (⊤̇ {n =
  zero})` with `UnequalTerms`: the key of `⊤̇` at arity zero has first
  component `# zero`, the junk member has first component `K₀`
  (the full error text is in the file's run output).

Both runs at the C-12 cap: `ProbeLJ185A` GREEN, 1.96 s cold then
1.79 s warm; `ProbeLJ185C` RED as intended, 1.81 s. The deciding
negative is **MEASURED**: the refuting witness fails the repaired
premise at the stage.

## 3. THE CONSUMER SUPPLIES IT

The real witness of `hasWitnessAt A x` is the subformula closure.
`witnessAt-in` produces `∣ clo ι ιL φ , (key∈closure ι ιL φ,
closureClosed ι ιL φ γ, closureShaped ι ιL φ b γ ...) ∣₁`
(`src/L/Coding/CodeSet.lagda.md:365-373`, witness at `:369`).

The premise is available there, at any carrier. Two delivered lemmas
compose:

1. `closure-inv` (`src/L/Coding/InL.lagda.md:445-457`): every member
   `x` of the closure satisfies `x ≡ key ι ιL ψ` for some formula
   `ψ` over the carrier at some arity.
2. `key∈AllCodes` (`src/L/Coding/CodeSet.lagda.md:443-444`): every
   such key lies in `AllCodes A`.

The composition is machine-checked in `src/ProbeLJ185B.agda:58-68`
(`clo⊆All`, GREEN at the C-12 cap, 2.07 s first run, 0.99 s warm):
`closure-inv` peels, and `key∈AllCodes` absorbs the peeled key. So the
premise is supplied at
the consumer's witness, at `file:line`: `CodeSet.lagda.md:369` for the
witness, `InL.lagda.md:445` and `CodeSet.lagda.md:443` for the
premise.

A structural caveat, **MEASURED by reading**: `WitnessAgree.out`'s
`go` receives only `(w , (hxw , (hcl , hsh)))` from the existential
(`src/L/Condensation.lagda.md:6247-6249`) and applies
`witK w (hxw , (hcl , hsh))`. A per-w premise `P w` is not among those
three, and the three do not imply it (the junk witnesses satisfy all
three and fail any defect-fixing premise). So the premise is available
where the witness is PRODUCED (the closure) but cannot be derived at
the TRANSFER for an arbitrary existential witness; the chain modules
would need the premise threaded as an extra parameter, which the tower
cannot supply for every `w`. This is recorded; the brief says not to
carry the chain further.

## 4. THE DISTINCTION, AND THE TRUTH CAVEAT

"The refutation fails" is not "an inhabitant exists". The repaired
statement is never proved here. This section prices its truth per
D-10.

With the premise, the junk member is excluded, so the refutation
mechanism is gone. The sufficiency is a rank statement. A key over
`A = Lset α` is a finite nesting of pairs over members of `A` (rank
below `α`) and numerals, so every key has rank below `α+ω`, and any
`w ⊆ AllCodes A` has rank at most `α+ω`. For `w ∈ Lset lam` one needs
`rank w < lam`; that holds when `lam > α+ω`.

At the knife-edge stage `lam = α+ω`, the closed shaped set
`AllCodes A` itself satisfies the full premise: it is closed
(subcodes of keys are keys of subformulas), shaped over `A` (every key
decodes over the alphabet, whose constants are members of `A`), it
contains the formula key, and it is trivially `⊆` itself. Its members'
ranks are cofinal below `α+ω`, so `AllCodes A ∉ Lset (α+ω)`.
`lam = α+ω` is admissible for the chain (`α ∈ lam`, `lam` a limit
ordinal, `α ∉ ω`, the LJ-1.80 parameters). So the premise alone does
not make `witK` true at every admissible stage. This counterexample is
**INFERRED**: it is a mathematical argument, not machine-checked, and
per the brief's classification rule it sets no verdict.

The making-true form is the premise plus the stage condition
`AllCodes A ∈ Lset lam` (equivalently `rank (AllCodes A) < lam`).
That condition is not delivered: `smallDom` returns `LsetS β oβ` for
the bounding ordinal `β` of the key family
(`src/L/Recursion.lagda.md:133-134`), and no delivered lemma relates
`β` to `lam`. The absence is **INFERRED** (named in
`_build/lj-1.84-report.md` section 2, not machine-checked) and sets no
verdict.

So the honest finding, per D-1 and C-38: the suppliable premise is
found and both halves check (MEASURED); the statement's truth is not
settled; the missing stage condition is the obligation that would have
to move to the tower's rank machinery, the same class as the tower's
`x∈Lλ` hypothesis (`src/L/BoundedSubset.lagda.md:1145-1146`). The
term that could not be written is `witK` with premise
`w ⊆ AllCodes A` at `lam = α+ω` (no inhabitant, INFERRED), and its
making-true variant needs the stage condition no consumer supplies.

## 5. NEGATIVES AND THEIR STATUS

1. "The refuting witness fails the repaired premise at the stage":
   **MEASURED TRUE**. `c₀∉All` (`src/ProbeLJ185A.agda:107-112`)
   checks green at the C-12 cap.
2. "The adaptation of the LJ-1.84 refutation does not typecheck":
   **MEASURED TRUE**. `src/ProbeLJ185C.agda:62-63` is rejected with
   `UnequalTerms` (arity slot `K₀` against `# zero`).
3. "The consumer's witness satisfies the premise":
   **MEASURED TRUE**. `clo⊆All` (`src/ProbeLJ185B.agda:58-68`) checks
   green; the witness is the closure at `CodeSet.lagda.md:369`.
4. "`w ⊆ AllCodes A` alone makes `witK` true at every admissible
   stage": **INFERRED FALSE**. The `AllCodes A` counterexample at
   `lam = α+ω` is argued, not machine-checked. Sets no verdict by
   itself.
5. "The stage condition `AllCodes A ∈ Lset lam` is not delivered":
   **INFERRED**. Absence by search; named in the LJ-1.84 report.
   Sets no verdict by itself.
6. "A per-w premise can be derived at the transfer for an arbitrary
   existential witness": **MEASURED FALSE** by reading.
   `go` at `src/L/Condensation.lagda.md:6247-6249` holds only
   `hxw`, `hcl`, `hsh`.

## 6. DEVLIN'S BOUND

Devlin's witness for "v = L_γ" is the level sequence
`(L_δ | δ ≤ γ)`, and what bounds it is membership inside the carrier:
the sequence is an element of `L_α` for every `γ < α` by 2.6(ii)
(`dev/literature/devlin-II5.md` section 2.3 Step C;
`_build/literature/dev2.txt:1191-1194`); his Σ₀ matrix binds its
quantifiers by the finite-sequence set `K(u)`, which lies inside the
carrier (`dev2.txt:593-630`).

The tree's `AllCodes` is NOT the analogue. `AllCodes` pins each
member's arity to a numeral, a shape bound; Devlin's bound is the
witness's rank, membership in the carrier stage. The analogue of
Devlin's bound is the conclusion `fst w ∈ fst K`, the very conjunct
the premise cannot supply. The missing stage condition of section 4 is
Devlin's bound.

## 7. THE DD4 ANSWER

The repaired premise is generic in SHAPE and per-tower in CONTENT.
The shape "the witness is a subset of the tower's code set over the
carrier" is shareable, and the junk mechanism it kills is shared
content: both towers' shapedness predicates leave the arity slot free
(`unForm`/`zeroPay`). The object `AllCodes A` is the L-side code set
(satisfaction-based, `src/L/Coding/CodeSet.lagda.md`); the J tower
would state the same shape against its own code set and supply its own
closure-inclusion, so the L supply (`closure-inv` plus `key∈AllCodes`)
does not transfer literally. The J side is **INFERRED**: no J tower
exists in this tree. This matches the LJ-1.82 verdict: the code-set
data is per-site content.

## 8. ARCHIVE USED

- `_build/lj-1.84-report.md`, read WHOLE. TOOK the refutation
  mechanism (junk member `pr K₀ (pr (# 6) (numeralL 0))`, `:106-110`),
  the arity-freedom cause, and the recorded missing stage condition
  (section 2, "the tree delivers no such lemma").
- `src/ProbeLJ184A.agda`, read WHOLE. TOOK the junk construction, the
  `fstC₀` equation (`:113-115`), the stage-refute parameters, and the
  import set.
- `_build/lj-1.83-report.md` and `src/ProbeLJ183A.agda`, read WHOLE.
  TOOK the chain's stop at `WitnessAgree.witK` and the "per-site
  content" reading of the code-set facts.
- `_build/lj-1.80-report.md` and `src/ProbeLJ180A.agda`, read WHOLE.
  TOOK the stage parameters (`lam`, `α`, `α∈λ`, `α∉ω`), the `ω∈lam`
  trichotomy route (`ProbeLJ180A.agda:64-76`), and `numeral-in-stage`.
- `src/L/Coding/CodeSet.lagda.md`, read WHOLE. Read-only. TOOK
  `hasWitnessAt` (`:240-241`), `isCodeAny` (`:247-248`),
  `AllCodes` (`:440-441`), `key∈AllCodes` (`:443-444`),
  `witnessAt-in` (`:365-373`), and the arity-debt prose (`:24-30`).
- `dev/LESSONS.md`, C-38 as extended (`:3427-3511`), C-35
  (`:3200-3241`), C-36 (`:3284-3331`), D-30 (`:3332-3380`), read
  WHOLE. TOOK the discharge standard (a hypothesis is discharged when
  something supplies it) and the strengthen-may-be-the-cure reading of
  C-36.
- `archive/rud-route/`, SHAPE only. Read the README and the file list;
  took nothing. The route's `BelowLim` closes `Sset γ ∈ Lset (γ+1)`
  at a general limit, which is the same content class as the missing
  stage condition, but nothing here re-uses it.

## 9. LITERATURE USED

- `dev/literature/devlin-II5.md`, read Step C (section 2.3) and the
  II.2.4-2.7 chain. TOOK the two-line bound of section 6 and the
  reading that `AllCodes` is not Devlin's analogue.
- `_build/literature/dev2.txt:1191-1194` and `:593-630`, via the
  digest. TOOK the 2.6(ii) membership bound and the `K(u)` bound.

## 10. GATES

- `scripts/check-fences.py --check`: clean, **87 masters**.
- `scripts/lint-prose.py --check` on the three probes and this report:
  exit 0.
- `scripts/lint-agda.py --check` on the three probes: exit 0.
- `src/ProbeLJ185A.agda`: GREEN at the C-12 cap, one process at a
  time. 1.96 s cold, 1.79 s warm.
- `src/ProbeLJ185B.agda`: GREEN at the C-12 cap. 2.07 s after the fix,
  0.99 s warm. First run walled: **~340 s, killed per C-12**; the
  cause was an unsolved metavariable in the branch type (`× _` in the
  `go` type, I-5's class); writing the second component type removed
  it.
- `src/ProbeLJ185C.agda`: RED as intended at `:62-63`, 1.81 s.
  `UnequalTerms` at the premise term.
- Load averages during the runs: 2.57 / 4.66 / 13.08 then 3.61 /
  4.14 / 9.68 then 3.25 / 3.91 / 8.92 (1, 5, 15 minutes), four users.
  The machine was NOT quiet, so every absolute figure carries the
  caveat.
- Masters: all green or untouched. `git status` is clean; HEAD
  `9669576` on `two-tower-bridge`, unchanged. Probes and this report
  are gitignored.
- No `make check`. No commit, no push.

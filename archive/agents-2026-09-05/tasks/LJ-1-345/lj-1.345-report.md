# LJ-1.345 report: DD25 adversarial review of `[LJ-1.341]`'s vacuity claim

tier: pi (in-harness-subagent-mode), the switch's ADVERSARIAL row (`herdr` /
`pi` / `glm-5.3`). Written incrementally (C-22). Every negative is MEASURED or
INFERRED, in those words.

## 0. VERDICT

**UPHOLD.**

**The refutation holds, at both index forms, and I rebuilt it myself.** The
instantiation `z := the bound itself` is admissible, the premises are
inhabited at the refutation's own witnesses, and the landed repair is green,
cold, in 132.93 s. **The chapter was edited on a TRUE premise. Nothing must be
reverted.**

**The attack that came closest is attack 3, the repaired statement.** It did
not break anything, but it produced the only basis corrections this review
found: the closure figure `[LJ-1.343]` quoted was its own tree minus its own
edit, and the chapter's green is reproducible today only through a verbatim
copy, because the committed interface cache answers a plain run in 2.35 s.

**Attack 4 corrected a claim of the BRIEF's, not the target's (C-44).** The
premise that one of the two sweeps was narrow is MEASURED FALSE. Both counts
reproduce exactly, because they counted different objects.

| claim under test | verdict | basis |
|---|---|---|
| `z := the bound` is admissible in both pre-repair telescopes | **YES, MEASURED** | git diff `26d25a7`; my `Refute345.agda`, exit 0 |
| the two hypothesis types were EMPTY at every slot and environment | **YES, MEASURED** | `Refute345.agda` (mine), `ProbeTies341.agda` re-run, both exit 0 |
| both premises are inhabited, so the ties are FALSE and not merely unusable | **YES, MEASURED** | non-vacuity terms in both files, green |
| the landed repair typechecks, cold | **YES, MEASURED** | verbatim copy `CondCold345.lagda.md`, exit 0, 132.93 s |
| the repaired statement is what the call sites need | **YES** | three grounds, section 3 |
| the count of fatal ties inside the seven modules is TWO | **YES, MEASURED** | every quantified tie in all seven read, section 4 |
| Devlin's step has no unbounded quantifier | **YES, MEASURED** | primary source `_build/literature/dev2.txt:593-630`, section 5 |
| one of the two prior sweeps was narrow | **MEASURED FALSE** | both counts reproduce, section 4 |

## 1. ATTACK 1: IS `z := b` REALLY ADMISSIBLE?

**ADMISSIBLE, MEASURED, four independent ways.**

**1. The pre-repair telescope, read from git and not from the target's files.**
Commit `26d25a7` shows the original parameters at `DefinesAgree`:
`(envK : (E z : S) → ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
→ ⟨ fst E ∈ fst (lookup K γ) ⟩)` and the same shape for `pairK`, plus the
`LeafAgree` index form. `E`, `z`, `w'` are the hypothesis type's OWN first
binders. The earlier telescope entries `N0eq` and `numK` name the slots `N0`
and `K`. **Nothing before the satisfaction premise mentions `z`, and nothing
after it constrains the instantiation.** The module `Refute` in the target's
probe quantifies over `Ki` and `γ`, which covers both index forms because
`lookup (suc (suc (suc K))) γ` is one instance of `lookup Ki γ`.

**2. Scope identity, checked name by name.** The decisive risk was that
`ControlA341` restates the types in ITS OWN scope, so a different `⊨` or `∈`
would make it refute a look-alike. It does not:

- `⊨`: the chapter has `module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans`
  and opens it with the `_⊨ᵐ_` to `_⊨_` renaming
  (`src/L/Condensation.lagda.md:72-74`); the control renames the very same
  module from `GM.AbsL` (`ControlA341.agda:36-37`).
- `∈`: both take `_∈_` from `Cubical.HITs.CumulativeHierarchy.Base`
  (chapter `:62`, probe `:53`).
- `S`: both from `hPropStructure 𝒮ʟ`. `⟨_⟩` from `Base.Truth` in both.

**3. Re-runs.** `ProbeTies341.agda` exit 0 in 2.14 s. `ControlA341.agda`
exit 0 in 1.30 s. `MustFail341.agda` exit 42 in 0.90 s with the expected
error, which names the missing carrier hypothesis at `MustFail341.agda:54`.
The gate is live: the same two record fields that prove the bounded form
refuse the unbounded one.

**4. MY OWN WITNESS.** I wrote `agents/tasks/LJ-1-345/Refute345.agda`: the two
pre-repair types transcribed from the commit diff, importing NOTHING from
`LJ-1-341/`, both non-vacuity premises included. **Exit 0 in 1.55 s, and
`lint-agda.py --check` exit 0.** The refutation no longer rests on the
target's transcription at all.

The mathematics itself is four lines each: `b ∈ ⁅#0,b⁆ ∈ pr (#0) b ∈ b` and
the same cycle one link longer, discharged by accessibility recursion on
`regularityV`, confirmed at `src/V/Hierarchy.lagda.md:139-144`.

## 2. ATTACK 2: NON-VACUITY, RE-CHECKED

**BOTH PREMISES ARE INHABITED, MEASURED.** The target answered this twice and
both answers survive.

- The `defPairK` premise at the witnesses `E := B`, `z := B`,
  `w' := prʟ (numeralL 0) B` is a one-line transport through
  `tagAtL-adequate`, because the tag premise is exactly the set equation
  `fst w' ≡ pr (# 0) b`. The term elaborates in both my re-run and my own
  file.
- The `envK` premise at `E := pairʟ W W`, `z := B` is built through
  `extAt-in-both`, and I verified `extAt-in-both f g = f , g` is a
  definitional pair over the conjunction `extAt`
  (`src/L/Coding/Model.lagda.md:662-678`). The premise is genuinely
  satisfied, not assumed.

**So the hypotheses are FALSE, not unusable-by-empty-premise.** The
distinction the brief asked me to keep is kept: the universal quantifier is
non-trivially false, `[LJ-1.338]`'s residues 5 and 6 priced a falsehood and
not a vacuity, and the repair fixes a false statement.

## 3. ATTACK 3: THE LANDED REPAIRED STATEMENT

**THE CHAPTER IS GREEN, MEASURED COLD, BY A ROUTE `[LJ-1.343]` DID NOT NEED.**
A plain `agda src/L/Condensation.lagda.md` returns in 2.35 s with no
`Checking` line today: the committed interface is fresher than the source, so
the root loads from cache. I did NOT touch the toolchain-owned interface
(`dev/build-manifest.toml` class `toolchain`, "never touched by hand").
Instead I copied the chapter verbatim into my task directory, renamed only the
module declaration (the diff is empty except that name), and checked the copy:
**exit 0 in 132.93 s** against the 2.37 s empty-file floor `[LJ-1.343]`
measured. Their 133.96 s is reproduced within noise. This makes their figure
reproducible but also shows a reader must work for it.

**THE IDENTITY TEST RE-RUNS GREEN.** `ProbeScope343.agda`, exit 0 in 1.27 s.
`hz-is-member z hz = hz` and `member-is-hz z hz = hz` both elaborate, so the
satisfaction type of `hz` and the set type of the new hypothesis are ONE type,
definitionally. I also checked the probe's `bodyM` restatement against the
chapter's own `:6801-6803`: the first conjunct is `var zero ∈̇ var (suc w)` in
both, and the three feed sites `:6819`, `:6828`, `:6834` pass `hz` and nothing
else. The `LeafAgree` pass-through at `:7220-7222` hands the two ties to `DA`
positionally under `w := suc (suc (suc w))`, `K := suc (suc (suc K))`, which
is exactly the repaired index form.

**IS IT WHAT THE CALL SITES NEED, OR MERELY WHAT TYPECHECKS? It is what they
need, on three grounds.**

1. The sites consume only the ties' CONCLUSIONS, and the conclusions are
   unchanged. Each application gained one argument that was already in scope.
2. **No meetable statement can avoid a bound on `z`.** The unbounded form is
   empty at EVERY environment, so no instantiation world could ever supply
   what the sites used before the repair. A tie the chapter could really have
   used did not exist; the repair is forced, not chosen.
3. The repaired ties are TRUE: `ProbeTies341.agda`'s `Repair` and `RepairEnv`
   are terms from `KFacts.pairK`, `numK0` and two `BoundOver` lemmas, so the
   telescope is meetable, which it never was. I re-measured the one gap:
   `src/L/Coding/Bound.lagda.md` carries `pr∈λ` (`:69`), `trans∈λ` (`:93`),
   `num∈λ` (`:139`) and `prʟ∈λ` (`:142`) and NO singleton closure, and
   `KFacts` (`:6091-6100`) carries the numeral memberships and no singleton
   field. **The next task's first line stands as written.**

**THE C-45 CAVEAT STANDS.** `LeafAgree` has zero consumers in `src/`
(MEASURED, re-grepped today), so the chapter's green is still a
parameters-green. The repair makes the parameters inhabited; it does not
supply them. `[LJ-1.343]` said this itself and it remains true.

**ONE BASIS CORRECTION.** `[LJ-1.343]` reported the chapter `gch_only` at
6,718 lines. I ran `ledger.py --trophy-files` today: **`gch_only` at 6,731**.
Their figure was the tree BEFORE their own +13 lines landed. The class is
right; the line figure was stale on arrival. See section 6.

## 4. ATTACK 4: THE EXTENT, RE-RUN

**THE SEVEN MODULES are TagAgree, EnvOneAgree, DefinesAgree, WitnessAgree,
KeyAgree, SatGraphAgree and LeafAgree** (the leaf branch's tie telescopes, as
composed at `src/L/Condensation.lagda.md:7204-7222`). **I read every
quantified tie in all seven. The count of fatal-shape ties is TWO, and they
are the two already refuted and repaired.** MEASURED, by reading:

| module | quantified ties | why each survives |
|---|---|---|
| TagAgree `:6670` | none | `tagEq`, `numK` quantify over nothing |
| KeyAgree `:6699` | `keyValK` | the tag pins `t` against the FIXED slot `suc c`; see below |
| EnvOneAgree `:6748` | `pairK` | pins `z` against the fixed slot 2; a term, the target's Control 4 |
| DefinesAgree `:6778` | `envK`, `pairK`, `satK` | the two FATAL ones; `satK` binds `z` by its formula's membership conjunct |
| WitnessAgree `:6576` | `witK`, `codesK`, `unCodesK`, `entryK` | `witK` names `w` in its conclusion and its premise is a conjunction; the other three bound `w` by an up-front hypothesis |
| SatGraphAgree `:6852` | 7 ties | `twelve-out`/`back` are formula-to-formula; the other five carry an up-front `fst d ∈ bound` or `fst e ∈ bound`; `witK` here names `d`, `e`, `f` in its conclusion |
| LeafAgree `:7115` | 15 ties | the same thirteen, passed through, plus the two repaired |

**ONE BASIS CORRECTION to the target's sweep, not its verdict.** Its reason
for `keyValK` was「concludes about the SAME variable the tag reads, so no
cycle arises」. The mechanism is imprecise: instantiating `t := B` would give
`b ∈ b` directly, a two-step cycle. The correct reason `keyValK` survives is
that its premise EQUATES `t` against a FIXED slot's content, so the
countermodel needs a special environment, and the type is not empty at the
intended one. The chapter itself records this family rule at
`src/L/Condensation.lagda.md:3069-3072`: the tag「pins the key, so the
unconditional form is refuted at the abstract frame ([LJ-1.97]) and this is
the honest shape」. The target's conclusion was right; its stated mechanism
was the wrong one of the two available.

**THE BRIEF'S OWN PREMISE IS MEASURED FALSE (C-44).** It said one of the two
sweeps was narrow because `[LJ-1.343]` found 38 where `[LJ-1.341]` said two.
I re-ran both:

- The seven-module tie sweep: TWO fatal. Above.
- The stale-signature sweep: `grep -rl` for the unbounded `envK` signature
  over `agents/`, `src/`, `archive/` returns **exactly 38 files**, all under
  `agents/tasks/`, **zero under `src/`**.

**They counted different objects and both are right about their own.**
`[LJ-1.341]` counted TIE TELESCOPES in seven modules of `src/`.
`[LJ-1.343]` counted FILES carrying the stale SIGNATURE TEXT anywhere. A
frozen probe copy of a refuted type is not a second false tie. Neither agent
undercounted.

**NOT SETTLED BY THIS REVIEW, and outside both sweeps.** The wider
`subK`/`consK`/`valV`/`wKfact`/`envInK` families in the chapter
(`:2932`, `:3076`, `:3757`, `:3870` and the four masters) carry clause-reader
premises that pin their subjects against other slots, fixed or quantified,
and several carry up-front bounds. I read their telescopes and did NOT
adjudicate their truth. Nothing in this review confirms or denies them, and
`[LJ-1.338]`'s sites 1 and 2 priced them as supplied.

## 5. ATTACK 5: THE DEVLIN READING

**CONFIRMED AGAINST THE PRIMARY SOURCE, not just the digest.** The digest
(`dev/literature/devlin-II5.md:245-250`) says 2.2 to 2.4 write
`D(v, u) = "v = Def(u)"` as Σ₁ and「bind every unbounded quantifier by the
concrete set K(u) ... and the members of u」. I opened the source it cites,
`_build/literature/dev2.txt:593-630`:

> 「Let C(w, v, u) be the formula obtained from B(v, u) by binding all
> unbounded quantifiers by w.」 ... K(u) is built from the finite sequences
> over 「the set 𝔗 ∪ {v_i | i ∈ ω} ∪ {x | x ∈ u}」 ... 「If we now let
> D(v, u) be the formula ∃W[K(W,U) ∧ C(W,V,U)]」

**So Devlin's step literally has NO unbounded quantifier: every one is bound
by the concrete K(u), whose building material includes the members of u.**
Our pre-repair telescope quantified `z` with no bound at all. The repair's
`⟨ fst z ∈ fst (lookup w γ) ⟩` is the port of「x ∈ u」at the carrier slot.
The digest's closing line, that the argument needs only「some bounded
description with a bound inside the carrier」, names the carrier, which is
the slot the repair chose. **The port-artefact reading is right, and the
primary source is the strongest evidence the repair is the right one.**
`[LJ-1.343]`'s refinement, that the binder returns as a hypothesis rather
than a conjunct and that both shapes are legitimate, is consistent with the
digest's closing line and with the chapter's own two conventions (`satK`
binds by formula, `KFacts.carrierK` by hypothesis).

## 6. DD4, WITH THE AXIS NAMED (C-46)

**THE AXIS IS AC-AGAINST-GCH, fixed at `scripts/measure/ledger.py:50`.**

- **`[LJ-1.341]`'s closure claim is MEASURED FALSE.** It said the chapter is
  in neither trophy closure.
- **`[LJ-1.343]`'s CLASS is right and its LINE FIGURE was stale on arrival.**
  `ledger.py --trophy-files` today: `gch_only` at **6,731** lines, not 6,718;
  their +13 was already landed when they quoted the pre-edit figure. The
  three `src/L/Condensation/*Agree` masters are `shared` AMBIGUOUS, as they
  said.
- **The GCH figure UNDERSTATES**, as the brief notes:
  `dev/ledger.toml:204-213` records the construction `[LJ-1.326]` measured,
  about 1,028 GCH lines and 36 shared outside the closure the statement
  reaches.
- **The repair's text is class-free**, confirmed by reading both new
  hypothesis types: they name `fst`, `∈`, `lookup` and a slot index. So on
  DD4's own axis the four changed code lines land GCH-side, and when the tie
  supply is finally written it is written once for both ends.

## 7. C-57: THE HITS I READ AND THE ONES I REJECTED

| search | hits | read | rejected, and why |
|---|---:|---:|---|
| stale-signature `grep -rl` over `agents/ src/ archive/` | 38 | 2 whole (`LJ-1-341/`, `LJ-1-343/` probes were already on my archive list) | the other 36 rejected as testimony: frozen copies of the refuted text are the OBJECT of the count, not evidence about truth |
| quantified-tie grep across the seven modules | 46 tie lines | all 46, plus the seven telescopes whole | none rejected unread; the two fatal ones were the finding |
| wider-chapter tie candidates `:2512`, `:2932`, `:3076`, `:3260` | 4 | 4 | `:2512`/`:3260` rejected: generic `φ` parameters of transfer lemmas, not tie telescopes; `:2932` rejected: premise pins `z` against fixed slots; `:3076` rejected: pinned, and the chapter's own comment cites `[LJ-1.97]` |
| `L3.32-T` archive rows | header + index | shape only | every figure rejected: different carrier, different coding, no `KFacts` |

**The one I nearly discarded and should not have:** the plain `agda
src/L/Condensation.lagda.md` run that returned in 2.35 s. It looked like a
green and it was a cache hit. The honest chapter check needed the verbatim
copy, and a reader who trusts the fast run is measuring the interface
registry, not the repair.

## 8. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| any earlier parameter constrains `z` before the premise | **MEASURED FALSE.** git diff: `N0eq`/`numK` name other slots |
| the restated types differ from the chapter's in scope | **MEASURED FALSE.** `⊨`, `∈`, `S`, `⟨_⟩` all resolve the same |
| either refutation premise is empty | **MEASURED FALSE.** Terms in two independent files |
| the ties are unusable rather than false | **MEASURED FALSE.** Premises inhabited, conclusions refuted |
| the landed repair fails to typecheck | **MEASURED FALSE.** Cold, verbatim copy, exit 0, 132.93 s |
| `hz` needs a transport at the sites | **MEASURED FALSE.** Identity both ways, re-run green |
| the repaired ties are false or unmeetable | **MEASURED FALSE.** Terms from `KFacts` fields plus two `BoundOver` lines |
| the sites could have used an unbounded tie | **MEASURED FALSE.** Its type is empty at every environment |
| a consumer of the chapter breaks | **MEASURED FALSE (inherited and spot-checked).** `Key.lagda.md` mentions the chapter in prose only; the five masters' `using` lists name none of the changed modules, and the cold copy re-elaborates the chapter itself |
| the fatal-tie count inside the seven is more than two | **MEASURED FALSE.** All 46 quantified tie lines read |
| `[LJ-1.341]`'s or `[LJ-1.343]`'s sweep was narrow | **MEASURED FALSE.** Both counts reproduce exactly on their own objects |
| Devlin leaves any quantifier unbounded at this step | **MEASURED FALSE.** Primary source, `dev2.txt:593-630` |
| the chapter is in neither trophy closure | **MEASURED FALSE.** `gch_only`, 6,731 today |
| `[LJ-1.343]`'s 6,718-line figure is current | **MEASURED FALSE.** 6,731 with its own edit landed |
| the wider `subK`/`consK` families are safe | **INFERRED, NOT CLAIMED.** Outside both sweeps; truth not adjudicated here |
| the four surviving residues are affected | **INFERRED FALSE.** Not re-priced, as in both prior returns |
| a run hit a wall | **MEASURED FALSE.** Longest 132.93 s, under the 30-minute wall |

## 9. SECONDS, LOAD, RUNS

One agda process at a time, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised. Slot
count `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l` run before every
invocation: **0 every time**. Machine quiet. **Empty-file floor: 2.37 s**
(`[LJ-1.343]`'s `FloorEmpty343.agda`, same import block; my cache-hit floor
run sits in the same class).

| run | exit | seconds |
|---|---:|---:|
| `agents/tasks/LJ-1-341/ProbeTies341.agda` | 0 | 2.14 |
| `agents/tasks/LJ-1-341/ControlA341.agda` | 0 | 1.30 |
| `agents/tasks/LJ-1-341/MustFail341.agda` (EXPECTED RED) | 42 | 0.90 |
| `agents/tasks/LJ-1-343/ProbeScope343.agda` | 0 | 1.27 |
| `agda src/L/Condensation.lagda.md` (cache hit, no `Checking` line) | 0 | 2.35 |
| `agents/tasks/LJ-1-345/Refute345.agda`, first attempt (scope error, mine) | 42 | 2.14 |
| `agents/tasks/LJ-1-345/Refute345.agda` | 0 | 1.55 |
| `agents/tasks/LJ-1-345/CondCold345.lagda.md` (chapter, verbatim, cold) | 0 | 132.93 |

## 10. ARCHIVE USED (DD18)

One line read per archived file, as the brief orders.

- **`agents/tasks/LJ-1-341/lj-1.341-report.md`, read WHOLE.** **Line read:**
  its section 2,「Take `E := B`, `z := B`, `w' := prʟ (numeralL 0) B`. The
  premise holds ... The conclusion is then `pr (# 0) b ∈ b`」. **TOOK** it as
  the claim under test and rebuilt it independently. **CONFIRMED** every
  load-bearing figure. **CORRECTED one basis**, not one verdict: its
  `keyValK` reasoning in section 6 (section 4 above).
- **`agents/tasks/LJ-1-343/lj-1.343-report.md`, read WHOLE.** **Line read:**
  its section 1,「THEY ARE ONE TYPE. MEASURED. ... passes `hz` through the
  identity function in BOTH directions」. **TOOK** the repair's premise as
  attack 3's object and re-ran it. **CORRECTED one figure:** the 6,718-line
  closure count was pre-its-own-edit; 6,731 today.
- **`agents/tasks/LJ-1-338/lj-1.338-report.md`, read the residue table and
  the D-10 warning, `:188-213`.** **Line read:** `:205-213`,「RESIDUES 5 AND
  6 MAY BE FALSE AS STATED ... INFERRED, by reading `:7183-7186`. I did not
  build the counterexample」. **TOOK** it as the chain's origin: the task that
  priced the ties before anyone asked whether they were true, and said so.
- **`archive/dev/TASKS-archived.md`, read the header and index shape.**
  **TOOK SHAPE ONLY:** a retired route's dispatch history. **REJECTED every
  figure:** different carrier, different coding, no `KFacts` record, so no
  count or seconds figure from it prices anything here.

## 11. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md`, read `:238-256`, and the primary source it
cites, `_build/literature/dev2.txt:593-630`, read whole.**

**The line that carries attack 5:** `:246-249`,「then bind every unbounded
quantifier by the concrete set K(u), the finite sequences over the formula
set, the variables and the members of u」, confirmed verbatim against
`dev2.txt:593` (「binding all unbounded quantifiers by w」) and `dev2.txt:610`
(the K(u) construction over 「{x | x ∈ u}」). **TOOK** it as the strongest
evidence the repair restores the source's own binding. **WHY NOT the rest of
the digest:** `:243-244` is the `[LJ-1.12]` Δ₀ question, settled and not
reopened; `:258` onward is Step D, the hull with least witnesses, which no
tie of `LeafAgree` reaches; the cardinality halves of 5.5 and 5.6 are another
step, and C-46 forbids using Devlin's tower axis as DD4's.

## 12. WHAT I DID NOT SETTLE

- **The truth of the wider `subK`/`consK`/`valV`/`wKfact` families** in the
  chapter and the four masters. Outside both sweeps; flagged in section 4.
- **The four surviving residues** of `[LJ-1.338]`. Not re-priced.
- **The tie supply itself.** `LeafAgree` still has zero consumers; the
  singleton closure is still two lines away in `BoundOver`.
- **A same-session baseline of the UNREPAIRED chapter.** The pre-repair text
  lives only in git now; a cold figure for it would need a second verbatim
  copy at `26d25a7^`, which I judged outside this review's scope and budget.

## 13. PROHIBITIONS, ANSWERED

I wrote only inside `agents/tasks/LJ-1-345/`: this report,
`Refute345.agda` and `CondCold345.lagda.md` (a verbatim copy of the committed
chapter with the module renamed, made to force a cold check without touching
toolchain-owned interfaces). `git status --short` shows those three files and
nothing else of mine. **I landed nothing, reverted nothing, and opened
nothing under `src/` for writing.** I read and re-ran probes in `LJ-1-341/`
and `LJ-1-343/` and changed neither directory. I did not open
`src/Everything.lagda.md`, `dev/PLAN.md`, `dev/LESSONS.md` or `AGENTS.md` for
writing. No commit, no push, no `git checkout`, `stash`, `reset` or `clean`.
No `make check`. No em dash in any language.

`.venv/bin/python scripts/gate/lint-prose.py --check` and
`.venv/bin/python scripts/gate/lint-agda.py --check` exit 0 on
`Refute345.agda` and on this report.

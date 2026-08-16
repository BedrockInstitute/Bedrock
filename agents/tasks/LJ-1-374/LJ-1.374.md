# LJ-1.374: does the delivered tree already depend on `SetChoice`, and does the L side?

tier: pi (pi-subagent-mode), model `glm-5.3`. **I ran
`scripts/dispatch/dispatch_policy.py` before writing this line and took the
head it gave.** Agda. **RECON. Price it; do not build it.**

## WHY THIS EXISTS, and it may dissolve an owner ruling

**`[LJ-1.373]` measured that `BandChoice` is an INSTANCE of
`SetChoice (ℓ-suc ℓ)`, exactly and with no residue.** That interface is
`src/Base/Choice.lagda.md:54-55`.

**MEASURED by me before writing this brief, and it is the whole reason for
this task:**

```agda
V⊨ZFC : ∀ {ℓ : Level} → SetChoice (ℓ-suc ℓ) → isZFCModel (𝒮ᵥ {ℓ})
```

`src/Landmarks.lagda.md:54`, with `V.Model.lagda.md:528` and the
`ChoiceLemma` module at `:453`. **So `V ⊨ ZFC` is ALREADY a function of
exactly the interface, at exactly the level, that the band wants.**

**The owner ruled 2026-08-16 「do not assume it」 for `BandChoice`.** **If the
delivered tree already assumes the same thing for `V ⊨ ZFC`, then taking it at
the band adds NO NEW assumption, and the ruling may already be satisfied.**
**That is the owner's call and NOT yours. Your job is the FACTS it rests on.**

## THE QUESTION, in four parts

**1. DOES THE L SIDE TAKE `SetChoice` ANYWHERE?** **This is the decisive
one.** `L ⊨ AC` is a trophy that PROVES choice, so the L tower taking ambient
choice would be a very different fact from `V ⊨ ZFC` taking it. **Grep the
whole L closure and read every hit.** **Report YES or NO with every site.**

**2. IS `V ⊨ ZFC` A TROPHY OR A LEMMA HERE?** **`src/V/Model.lagda.md:427`
says in English that upgrading to ZFC costs「a real new assumption」.** **Read
that prose whole and say what status the tree gives it.** **If `V ⊨ ZFC` is
delivered CONDITIONALLY, say so plainly: the project's headline may already be
a conditional.**

**3. WHAT EXACTLY IS `SetChoice`, and is `BandChoice` really an instance?**
**Re-derive `[LJ-1.373]`'s claim yourself at
`src/Base/Choice.lagda.md:54-55`.** **If it is not an exact instance, this
task collapses and so does its finding.**

**4. WHAT WOULD THE GCH TROPHY'S STATEMENT LOOK LIKE if it took the same
interface?** **Do not change it. Write the type and say what it costs the
reader.** **`[LJ-1.323]` restated the trophy so it carries no unsupplied
hypothesis; say honestly whether this would put one back.**

## THE ABORT CRITERION (D-1)

- **THE L SIDE TAKES IT NOWHERE, AND V TAKES IT.** **Then the two towers
  differ on exactly this, and the owner has a clean question.** Report both
  sides at `file:line`.
- **THE L SIDE ALREADY TAKES IT.** **Then the band's demand is not new at all
  and the ruling is already satisfied. Say where, and STOP: that is a full
  return.**
- **`BandChoice` IS NOT AN INSTANCE.** **Then `[LJ-1.373]` is wrong and the
  chain goes back to the untruncation. Say so with the types.**

## CONSTRAINTS

- **LAND NOTHING. `src/` is forbidden** (I-5). Write only in
  `agents/tasks/LJ-1-374/`.
- **`[LJ-1.375]` is live and writes only in `agents/tasks/LJ-1-375/`.**
- **COUNT THE AGDA SLOTS** before every invocation, exactly:
  `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`. Cap is TWO.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the empty-file floor beside any seconds figure** (C-53).
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-374/lj-1.374-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `lint-agda.py --check`. **No em dash.** ASD-STE100. Evidence is `file:line`.
  Mark every negative **MEASURED** or **INFERRED**.

## PREMISES

- **`V⊨ZFC` takes `SetChoice (ℓ-suc ℓ)`**, at `src/Landmarks.lagda.md:54`.
- **`BandChoice` is an exact instance of it**, per `[LJ-1.373]`.
- **The L towers prove `L ⊨ AC` rather than assuming choice.**

**Mark each VERIFIED or REFUTED at `file:line`.**

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Eleven of my last thirty-eight briefs carried a claim an agent measured
FALSE.** **The one at risk: 「the L side takes `SetChoice` nowhere」.** **I
grepped `src/` and saw hits only in `Base`, `V/Model`, `Landmarks`,
`Everything` and `README`, and I did NOT read the L closure.** **If an L
chapter takes it, my whole framing of this question is wrong.**

## THE RULES

**DD28, ruled TODAY: a provability probe surveys the literature FIRST, and
this task is NOT one: it asks what the tree DOES, which is a grep and a
read.** **C-57: the search that finds it and the reading that discards it are
two different failures.** **C-44, C-45, D-10, C-42, C-53, P-l, P-k.**
**C-12, C-22, C-32, C-36, C-39, C-40.** I-5. **D-1, D-26.**
**DD0, DD4, DD5, DD18, DD23, DD24, DD25.**

Run `.venv/bin/python scripts/dispatch/rules.py --for recon` and read every
statement.

## DD4

**Maximize the code the two proofs share, and write it generic.** **NAME YOUR
AXIS** (C-46). **`Base.Choice` is upstream of everything, so whatever it
supplies is shared by construction. Say whether that makes this a DD4 win or
merely a shared cost.**

## ARCHIVE (DD18)

**`scripts/gate/check-dd18-survey.py` GATES your return: name each of the four
corpora, cited or declined in ONE line, and QUOTE one line per archived file
you read, at its real line number.**

- **`archive/src/2026-08-09-rud-route/`**: **did the retired route take an
  ambient choice principle anywhere? Grep it.**
- **`archive/dev/JOURNAL-archived.md:1630`**: the retired reason for refusing
  choice. **Quote it.**
- **`archive/dev/DECISIONS-archived.md`**: any ruling on ambient choice.
  **WHY NOT in one line if none.**
- **`archive/dev/TASKS-archived.md`**: taking SHAPE and never a claim.

## LITERATURE (DD18)

**`dev/literature/truncation-and-selection.md`.** **`[LJ-1.373]` read it whole
and measured that this shape is an AXIOM. Cite that finding and do not repeat
the survey.** Return a **LITERATURE USED** section.

## SCOPE (read)

`src/V/Model.lagda.md:420-460` FIRST: it holds the English prose calling this
a real new assumption, and the `ChoiceLemma` module.

## SCOPE (write)

`agents/tasks/LJ-1-374/` only.

## RETURN

**Lead with ONE word: L-TAKES-IT, L-DOES-NOT, or NOT-AN-INSTANCE.** Then every
site on both sides. Then what status the tree gives `V ⊨ ZFC`. Then the GCH
statement's type if it took the interface, and what it costs the reader.
**Mark every negative MEASURED or INFERRED.**

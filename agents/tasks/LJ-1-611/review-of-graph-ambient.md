# review of `graph-ambient`: the face's honest supplier is the ambient adequacy of the level-graph matrix, and the tree has no ambient side to read it on

## VERDICT

**THE TERM IS NOT SUPPLIED, AND I DID NOT INHABIT THE FACE AT A DISHONEST
MATRIX.** The obligation is ONE term, `graph-ambient : GraphAmbient`, face G-
of `[LJ-1.606]`'s `Crossing` (`agents/tasks/LJ-1-606/Probe606.agda:168-172`).
The meter says so: `agents/tasks/LJ-1-611/Probe611.agda::graph-ambient`
returns `missing exit=42 ... [NotInScope]`, `1 UNRESOLVED of 1`,
`probe_red=False` (witness run, 2.35 s). The probe itself is GREEN and
carries no hole (`agents/tasks/LJ-1-611/runs/p-4-forced.out`, exit 0, 3.78 s,
peak 656,769,024 bytes, forced recheck of the delivered file).

**THE FACE'S LETTER ALONE IS TRIVIALLY SUPPLIABLE, AND THAT IS NOT A
DELIVERY.** Two junk admissions are terms in the probe:

- the psi-quantified misreading is FALSE: a TRUE matrix fails the face
  outright (`quantified-refuted`, `Probe611.agda:133-146`, the port of
  `[LJ-1.606]`'s `⊤-fails-G-`, `Probe606.agda:262-273`);
- the Sigma-shaped letter is satisfied VACUOUSLY by the FALSE matrix
  (`vacuous-junk`, `Probe611.agda:155-156`), the same measurement
  `[LJ-1.598]` made one clause over (`only-level-vacuous`,
  `agents/tasks/LJ-1-598/Probe598.agda:104`).

The kit's own G+ face refutes both fillings (`⊥-fails-G+`,
`Probe606.agda:275-285`), and the brief forbids exactly that delivery. The
honest target is therefore the face at a LIVE matrix, and it is NAMED in the
probe:

    Honest-G- = Σ[ ψ ∈ Formula CI.I.SM 3 ]
                  (Δ₀ ψ × GraphAmbient ψ × G-live ψ)

with `G-live ψ` the satisfiability of the mapped matrix at EVERY ordinal
index (`Probe611.agda:170-177`). The false matrix fails it by term
(`vacuous-fails-live`, `:179-182`); an index-pinned matrix (one that names
the level by constants) fails it at every other index. `Honest-G-` is
exactly the soundness half of the level-graph adequacy, clause (i)'s own
residue, which `[LJ-1.598]` priced NO-GO on the formula side
(`agents/tasks/LJ-1-598/lj-1.598-report.md`, VERDICT).

## WHY NO DELIVERED READING REACHES IT

**G-'s HYPOTHESIS IS THE AMBIENT READING AT AN ARBITRARY ENVIRONMENT.** The
satisfaction `AbsπX.⊨ᵛ` is the semantics of the FULL ambient structure
`𝒮ᵥ` (`FOL.Absoluteness.Single`'s `SemV` and its `At SM fst` opening,
`src/FOL/Absoluteness.lagda.md:70-77`): every existential of the formula
ranges over every ambient set, and the environment `(x, v, γ)` is three
arbitrary ambient values, not three members of the image.

**EVERY DELIVERED ADEQUACY FOR A LEVEL-GRAPH FORMULA IS THE INNER READING.**
The coding chapters read their formulas at `S = 𝒮ʟ.S`, where the
object-language existentials range over `L` only:

- the definable-powerset leaf `DefAt` is introduced and eliminated at the
  inner reading with the side condition `DefOK`, whose documented content is
  exactly this gap: "every existential in the description ranges over `L`,
  so the set the description picks out can only contain constructible sets"
  (`src/L/Coding/Powerset.lagda.md:409-411`, definitions at `:442-446`;
  the operator's own
  specification is the inner `defSet-mem`,
  `src/L/Definability.lagda.md:146-148`);
- the determination lemma `Lset-only`, the soundness half G- needs, is
  stated and proved at the inner reading with the environment inside `L`
  (`src/L/Hierarchy.lagda.md:334-337`);
- the Delta-zero bounded restatement's leaf adequacy, `LeafAgree`, is
  conditional on the certificate frame's site-facts telescope: a `KFacts`
  record plus a dozen containment ties on the bound `K`
  (`src/L/Condensation.lagda.md:7216-7306`), none of which is delivered at
  `[LJ-1.606]`'s six-slot frame.

At the ambient these readings differ exactly where it hurts: an ambient
existential witness need not be in `L`, so the inner determination cannot be
applied to it, and the bounded description's rigidity at the ambient is
precisely the unbuilt half. `[LJ-1.598]` measured the frame cost on the
INNER side of this neighbourhood: the certificate's own statement file
walls under the wide cap (`agents/tasks/LJ-1-598/runs/chain-578.out`, exit
251). The ambient side is strictly stronger than what walled.

## THE MEASURED PRECEDENT, CUT AND RECOVERABLE

**THE AMBIENT FORM WAS BUILT ONCE, ON THE RETIRED ROUTE, AND ONLY REDUCED.**
At commit `3f5001e` the then-`src/L/Condensation.lagda.md` stated

    AmbientOnly = (v b : S) → IsOrd b
                → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵛ LsetGraphAt {2} zero (suc zero) ⟩
                → v ≡ Lset b

("The ambient-reading form of `Lset-only`, at the class carrier. The
delivered theorem is stated at the inner reading only"), and PROVED the
factorization `ambientOnly-from : TransferL → ValueIsL → AmbientOnly`:
the ambient form follows from an ambient-to-inner transfer of the graph
formula at `L` plus the value's constructibility. **Neither factor was
delivered there** ("Neither `TransferM` nor `AmbientOnly` is delivered",
the chapter's own recap at that commit), **and neither is in the tree
now**. The section was deleted by ruling D32 (2026-08-07); the cut is
the archive (`dev/ARCHIVE.md:285`), the text is recoverable by
`git show 3f5001e:src/L/Condensation.lagda.md`, its measured cost was
138.2 s of the chapter's 150.2 s (92 percent of the profile), and the
revival is priced and gated at the ledger's `crossing-rebuild` row
(`dev/ledger.toml:1021-1031`, resumes with the GCH wing per D30(F) and
D32). So the wall G- meets is not new: it is the retired route's own
open factor, now met from the ambient side at the collapse image.

## WHAT THIS PRICES FOR ROW 3

Row 3 does NOT thereby join the B-row ambient-injection wall as one
type-level obstruction: `GraphAmbient`'s type is satisfiable (by junk) and
its conclusion is an ambient path equation, not a code. What G- shares with
that wall is the one-way street `[LJ-1.533]` measured
(`agents/tasks/LJ-1-533/lj-1.533-report.md`, "WHAT CODES AN AMBIENT
INJECTION"): the machine reads code to ambient, and nothing reads ambient
back to code. G- needs the second direction for the WITNESS, not for the
conclusion. The next supplier of `Honest-G-` must build the ambient half of
the coding adequacy, or widen the frame until the bounded leaf's site facts
are deliverable and the ambient and inner readings meet at the image.

## SCOPE

I wrote only inside `agents/tasks/LJ-1-611/`. Nothing is postulated, the
probe carries `--safe`, the delivered file is green with no hole, and
nothing lands in `src/`. No commit, no push.

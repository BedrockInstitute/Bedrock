# LJ-1.450 review 2: the upheld NO-GO of review 1 survives the attack

## HEAD
head_slot: mathematician_adversarial
machine: shared
verdict: upheld

Provenance, one line only: this is the attempt 3 write of the
program-named file. The return under attack is
`agents/tasks/LJ-1-450/review-of-LJ-1-450-1.md`, the attempt 2 write
(model `glm-5.3`, dispatched at live transitions c-1084 seq 1083,
checked at c-1105). The critic is not the author: instance 2 reviewed
instance 1, the coder (model `grok-4.6`, c-966 seq 965), and this head
wrote neither return.

## WHAT WAS ATTACKED

The return of LJ-1.450#2 in full: `review-of-LJ-1-450-1.md`, every
section. Its inputs, all read: `lj-1.450-report.md` (303 lines),
`review-of-someEnv-at-K.md`, `Probe450.agda` (116 lines), the twelve
files under `runs/`, the work brief `LJ-1.450.md`.

The machine record of instance 2 (c-1105, live
`dev/pod/transitions/2026-08.jsonl`): `exit_code` 0, `error_class`
null, `heap_wall` false, `lines` 0, `obligations_delta` 0,
`obligations_open` 1, `seconds` 0.0, `model` `glm-5.3`, `effort`
empty, `heads_sha256` `2f6630d2`. Row `task-lj-1-450-stop-stated`,
an escalate. The R3 REJECT at c-1106 and c-1118 confirms what the
return's MACHINE NOTE claims: the close would have moved two corpus
records (c-1082 and c-1105) into `sys-critic-upheld-no-go/done`. The
note's diagnosis, task branch rows outranking the system row, is what
the program itself printed.

## QUESTION 1: DOES THE VERDICT LINE MATCH THE BODY

The line under attack has two parts: `verdict: upheld` in HEAD, and
the closing line "The NO-GO of LJ-1.450#1 is UPHELD." The body must
sustain an upheld NO-GO, so I re-ran both NO-GOs under this head
instead of trusting either earlier head.

My runs, one Agda process at a time, caliber `GHCRTS="-A64m -I0 -M8g"`,
probe interface deleted before and after each run, outputs kept
outside the tree at `/tmp/attack-full-1.out` and `/tmp/attack-w3-1.out`:

1. The full probe as kept: exit 42, one error, at
   `Probe450.agda:47.33-35`, `[UnequalTerms]`, "14 != 8 of type ℕ",
   "when checking that the expression iK has type
   Fin (5 Agda.Builtin.Nat.+ 3)". Wall 2.00 s, peak RSS 620052480
   bytes. Same site, same text, numbers within noise of the kept
   medians (1.95 s, 619020288 bytes, `runs/full-recheck-{1,2,3}.out`).
2. The W3-only variant, rebuilt by the exact recipe the return states:
   delete the five-line obligation block, lines 45 to 49 of
   `Probe450.agda`, run, restore. Exit 42, one error, at exactly
   `83.18-37`, with the error text of `runs/w3-1.out` word for word,
   down to "lookup N0 (numeralL 4 ∷ ... ∷ numeralL 11 ∷ [])". Wall
   2.19 s, peak RSS 640368640 bytes. The probe was restored
   byte-identical (diff against a saved copy is empty). This closes
   the second defect review 1 named against itself: the unkept
   variant now reproduces at the recorded line and column under a
   second head.
3. The arithmetic, with no machine, from the sources:
   `Fin (5 + n) = Fin 14` forces n = 9, then `S ^ 20` against
   `Kenv : S ^ 14`. `11 + n = 14` forces n = 3, then `Fin 8` against
   `iK : Fin 14` (`src/L/Condensation/LowerAgree.lagda.md:52`,
   `src/L/Condensation.lagda.md:7389`, `:7397`). No n solves both. At
   n = 3 the `suc^6` lookup reads Kenv slots 6 to 13, which hold
   `numeralL 4` through `numeralL 11` (`src/L/Condensation.lagda.md:7390-7393`);
   the bound `LsetS lam ordλ` is slot 1; `6 + k` is at least 6, so no
   `Fin 8` index lands on the bound.

The body of review 1 keeps every number inside what it measured. The
medians it quotes recompute from the kept files: 2.48, 2.45, 2.14
gives 2.45 s and 640401408 bytes in all three
(`runs/w3-{1,2,3}.out`); 1.96, 1.94, 1.95 gives 1.95 s and the RSS
median 619020288 (`runs/full-recheck-{1,2,3}.out`). The witness claim
matches `runs/witness-1.out` line for line. The body separates the
layout NO-GO from `[LJ-1.113]`'s INFERRED FALSE, and the separation
is correct: `agents/tasks/LJ-1-113/lj-1.113-report.md:207-210` says
INFERRED FALSE about provability from delivered machinery, and `:52`
rows `someEnv` as NEEDS NEW CONTENT. No section of the coder's report
or of review 1 claims the `someEnv` statement is false, and none
claims a GO or a trophy. The verdict line matches the body.

## QUESTION 2: DOES EVERY LOAD-BEARING CLAIM RESOLVE TODAY

I opened every load-bearing cite of review 1 in this worktree, today.
All resolve:

- `src/L/Condensation/LowerAgree.lagda.md:52-58`: `someEnvDef` as
  quoted, with `Fin (5 + n)`, `S ^ (11 + n)` and the `suc^6` lookups.
- `src/L/Condensation.lagda.md`: `module KValue` at `:7380`, `module
  B = Bound` at `:7385`, `Kenv : S ^ 14` at `:7389`, the fourteen
  slots at `:7390-7393`, `iK = suc zero` at `:7397`, the fourteen
  index names ending `i11` at `:7409`, `facts` at `:7411` with the
  `refl` and `B.num∈λ` fields at `:7413-7419`, `KFactsCons` at
  `:6122`, `consed` at `:7429-7434`, the `KFacts` convention at
  `:6079-6080`, the `S ^ (8 + n)` sites at `:6963` and `:7225`, and
  the consumer parameters at `:6963-6971`.
- `src/L/Condensation/TwelveAgree.lagda.md`: `record TFacts` at
  `:129-131` with the fields from `:133`, the `someEnv` field at
  `:289`, the `tf : TFacts` parameter at `:342`, `twelve-out` at
  `:527`, `twelve-back` at `:533`. The file is 538 lines.
- `agents/tasks/LJ-1-113/lj-1.113-report.md`: `:8`, `:52`, `:61-66`,
  `:135-146`, `:207-210`, all as quoted.
- `dev/LESSONS.md:3752` is the C-42 heading. `dev/pod/direction.md:37`
  is the standing direction. The audit findings the return leans on
  exist: F1 at `dev/pod/audit-2026-08-20.md:34`, F3 at `:57`, F9 at
  `:110`.
- Probe anchors: the obligation at `Probe450.agda:47-48`, `TagNum`
  at `:52`, `frame-sigma` at `:86` closing at `:111`, `IndexCheck`
  at `:114`, 116 lines. Report anchors: the verdict line at
  `lj-1.450-report.md:76`, `:113`, `:121-132`, `:134-152`, `:165-185`,
  `:199-212`, `:230`, `:235`.
- The live-tree claims: worktree HEAD is `bfd918c`; the worktree's
  own `dev/pod/transitions/2026-08.jsonl` stops at 157 lines with no
  LJ-1.450 row; the live rows sit at lines 966, 1036, 1083 and 1084
  with the seqs the return names. A file named
  `review-of-LJ-1-450-1.md` already appears in c-1082's changed list
  at 03:06:36Z, while the surviving file's mtime is 03:18:54Z, inside
  attempt 2's window. The provenance note of review 1 is consistent
  with the machine record on every point I can check.

The three defects review 1 filed against the coder's report are real
and none is load-bearing: `TagNum` runs to `Probe450.agda:78`, so the
report's `:52-74` tail is short by four lines; the W3-only variant was
not kept (my rebuild above now closes it); and the one wording it
flags is the same wording class I sharpen in Question 3.

## QUESTION 3: IS THE ENUMERATION COMPLETE

I re-measured every count in review 1's census today, in this worktree:

- `S ^ (11 + n)` in `src/`: 7. `LowerAgree.lagda.md:52`, `:97`,
  `:228`; `TwelveAgree.lagda.md:131`, `:339`; `UpperAgree.lagda.md:94`,
  `:213`. Same seven.
- `Kenv : S ^ 14` in `src/`: 1, `src/L/Condensation.lagda.md:7389`.
- `S ^ (8 + n)` in Condensation: 2, `:6963` and `:7225`; plus the six
  Model sites review 1 adds, `src/L/Coding/Model.lagda.md:1310`,
  `:1893`, `:1899`, `:1909`, `:1919`, `:1930`. Addition A is correct.

Addition B is sound machinery, not a fourth cure: `KFactsCons`
(`src/L/Condensation.lagda.md:6122`) and `consed` (`:7429-7434`)
shift every index by `suc` and cons one value, and the KFacts side of
the twenty-slot padded frame is six applications away. The consumer
closure holds: `SatGraphAgree` takes a `KFacts {8 + n}` plus
`twelve-out` and `twelve-back` as parameters
(`src/L/Condensation.lagda.md:6963-6971`), and TwelveAgree produces
`twelve-out` and `twelve-back` only inside a module that takes
`tf : TFacts` (`TwelveAgree.lagda.md:342`, `:527`, `:533`).

One sharpening this attack adds, for the next brief that prices cure
1. Review 1 states: "every pad with c less than 6 moves the numeral
indices off `KValue`'s own `i_j = j + 2`, so the `KFacts.tagEq`
fields stop transferring unchanged." Read alone, that sentence can be
taken to mean no pad below six conses transfers the 24 fields at all.
That reading is false. A five-cons pad at n = 8, with the TFacts
indices re-declared as `N_j = j + 1` and `K = zero`, reads Kenv slot
`j + 2` for every `tagEq_j` and slot 1, the bound, for every
`numK_j`; the KFacts field types then match judgmentally. Review 1
itself concedes the family ("a c-cons pad with c at least 5 can reach
the bound slot") and scopes its uniqueness claim to zero re-indexing,
so this is not an error in review 1. The fact the next brief needs
is: the pad height is not intrinsically six. Six is the height that
keeps `KValue`'s own index names, and any c from 5 up works if the
indices are re-declared. The verdict does not move: the pinned type
`someEnvDef {3} iK Kenv` does not form at any pad, and every pad is
still cure 1, a re-layout the brief forbade this task to write.

Did the brief cause the outcome? No. The D-10 split is independent of
n, the brief named this stop as an authorized outcome and priced a
NO-GO above the GO, and W3 was named as the risk. The A21 channel
held: the brief named the term and the probe, and the coder wrote and
ran the probe. W4 does not fire.

## DEFECTS FOUND BY THIS REVIEW

1. The wording risk in the sentence quoted above. Non-load-bearing:
   review 1's own restatement, "the six-cons pad is the unique
   adapter that keeps `KValue`'s own index names and its facts record
   unchanged", is exact, and my Question 3 check confirms it.
2. No other defect. Every number review 1 quotes recomputes from the
   kept files, and both of its own re-runs reproduce under this head.

## VERDICT

**The NO-GO is UPHELD.** The return of LJ-1.450#2 is correct on its
own numbers, its measurement is sound and reproduces under a second
head, every load-bearing cite resolves today, and its enumeration is
complete at its stated scope. The obligation
`agents/tasks/LJ-1-450/Probe450.agda::someEnv-at-K` stays open
(`obligations_open` 1, c-1105). Under the standing instruction, this
file plus exit 0 closes the task under row `sys-critic-upheld-no-go`.

What a next brief needs, if the owner reopens this front: the three
cures of `lj-1.450-report.md:235-238` stand; price the pad against
`consed`; and know that a five-cons pad with re-declared indices is
also a live shape, so the choice of six is a pricing decision and not
a mathematical necessity. The 25 closures stay unmeasured and the
250-line figure stays a hypothesis.

## ARCHIVE USED

- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined.
  The retired episode journal has no row on the two index conventions.
  The live record is this task's `runs/` directory and the live
  transitions file.
- `archive/dev/ORCHESTRATION.md:1`, read: "# ORCHESTRATION: the
  orchestrator's operating rules". Declined. Those rules are retired
  and the pod program is the live operator. They bear nothing on
  index arithmetic.
- `archive/dev/DD-archived.md:1`, read: "# THE `DD` RULING SERIES,
  archived in full 2026-08-18". Declined. The W laws that bind this
  review come from the standing instruction, and the live sweep rule
  is C-42 at `dev/LESSONS.md:3752`.
- `archive/dev/LJ-dispatch-index.md:421`, read: "| LJ-1.375 | DD25
  review of LJ-1.373's BLOCKED-OTHERWISE | SPLIT. NO RESIDUE IS FALSE
  AND THE DIRECTION IS UNMEASURED |". Used, with `:422`: the two
  2026-08-16 episodes my brief names in Question 1 are real archived
  rows, so the failure class I was sent to check for has a recorded
  history. Neither row changes any check above; both were checked
  directly against the artifacts.
- `archive/dev/PLAN-archived.md:1`, read: "# ARCHIVED 2026-08-20".
  Declined. The retired plan bears nothing on the layout of
  `LowerAgree`, `TwelveAgree` and `KValue`.

## LITERATURE USED

- `dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the
  Condensation Lemma and the GCH in L". Declined as evidence. The
  dossier carries the paper mathematics and numbers no Agda `Fin`
  slot. No provability claim is before me: the machine decides that
  the pinned type does not form, so W8 does not stop this task.
- `dev/literature/BIBLIOGRAPHY.md:1`, read: "# Bibliography for the
  rud route". Declined. No source question is at issue.
- `dev/literature/digest.md:1`, read: "# Digest: the orthodox form of
  the rud route, pinned from the collected literature". Declined. No
  rud-route question is at issue.
- `dev/literature/geology.md:1`, read: "# Geology dossier:
  set-theoretic geology sources and the five questions". Declined.
  Geology is not the condensation frame.
- `dev/literature/devlin-errata.md:1`, read: "# Devlin errata:
  documented error classes (do-not-repeat checklist)". Declined. The
  error class here is an Agda index mismatch, not a documented Devlin
  error class.

# Shelve follow-up, 2026-08-28, after the owner-five-case

**TO:** maintainer, owner
**LOOP:** re-stop, seq 5095, 6 parked (713, 715-SPLIT-SPLIT, 717, 719, 720, 722)

A30 fires one `[shelve]` table per tick. The live request is `LJ-1.713`. The other three are drop-ins. After each fire, copy the next file onto `dev/pod/shelve-request.toml` and resume. Order: 713 (live), then 720, then 717, then 722.

## 1. LJ-1.713, delivered-elsewhere

Live: `dev/pod/shelve-request.toml`. Staged copy: `agents/tasks/POD-MATH/shelve-LJ-1-713.toml`.

723 closed GO on `below-closed-via` (`accept-1.out:20`, delta -1, open 0, status DONE). That is the object 713 produced (`Probe713.agda:120`). 713's briefed name `below-closed` was NO-GO: CompletenessFrom is a type.

## 2. LJ-1.720, delivered-elsewhere

Drop-in: `agents/tasks/POD-MATH/shelve-LJ-1-720.toml`.

721 closed GO on `pack-stage` (`accept-1.out:20`, delta -1, open 0, status DONE). Same obligation name as 720. 720's term sat inside `module Spend`.

## 3-4. LJ-1.717 and LJ-1.722, proven-futile. No third generation of this shape.

Drop-ins: `agents/tasks/POD-MATH/shelve-LJ-1-717.toml`, `agents/tasks/POD-MATH/shelve-LJ-1-722.toml`.

Both briefs name `completeness-from-ambient`. Neither closed. 717 isolated the amb-to-atL bridge: every shape with it walls at 2 GB; stage8 (bridge alone) 198.20 s, 2.55 GB. 722 transcribed that shape and measured the bare bridge at heavy: EXIT=251, 790.94 s, 4 GB (`b2-bridgebare.out:4`). The term is in the worktrees as `.agda.txt`. Rule (a3) keeps those trees.

I do not queue a third generation of this shape. Superheavy is not a task tier. Backlog 43b: the watchdog kills at ~6.8 GiB RSS, so an 8 GB RTS run is not reachable until the owner picks (a), (b) or (c). Reopen for both is 717's option 3: an AbsL-side ambient hypothesis that deletes the `atL` bridge. That is a new brief, not a 722-SPLIT. I will write it on refill when the queue drains.

## 5. LJ-1.719, ask the owner for `--retry`

`soundness-at-SL` still wants a run. Attempt 1 (`state.json` attempt 1, seq 5090) died pid-dead at 33 min, `record` null, park `no-change`. Rule (a2) never reopens that. Please pass to the owner: `pod resume --retry LJ-1.719`.

After the four shelves and that retry, parked is `LJ-1.715-SPLIT-SPLIT` alone.

## 6. 43b, superheavy

I withdraw the hand-run ask from the 715-SPLIT-SPLIT park note until the owner rules the backstop. Two measured kills at rss ~7,119,xxx KB, both inside `L.Condensation`, are already the cap question at 6g. I do not ask you to run the script again against a backstop that forbids the tier.

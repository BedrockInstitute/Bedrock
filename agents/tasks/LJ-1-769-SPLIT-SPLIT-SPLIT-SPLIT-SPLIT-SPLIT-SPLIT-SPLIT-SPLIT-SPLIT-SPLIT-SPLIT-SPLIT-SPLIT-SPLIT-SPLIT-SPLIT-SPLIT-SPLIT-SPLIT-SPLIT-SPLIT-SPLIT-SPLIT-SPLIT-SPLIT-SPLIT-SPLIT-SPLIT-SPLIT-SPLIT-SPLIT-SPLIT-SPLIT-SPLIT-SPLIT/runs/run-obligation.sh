#!/bin/sh
# The obligation rests at Probe769S36.agda, delivered by transcription
# under the gate (this task's brief ordered the transcription even if
# the gate fired), so the name is the brief's and not an earned
# EXIT=0.  GATE FIRST: read sysctl vm.swapusage and run nothing while
# swap used is at or above 8192 MB; that kill is the box's watchdog,
# not a wall.  Then run the file IN PLACE: one Agda process, caliber
# from the pane, never set here, 1800 s cap.  On EXIT=0 the name is
# earned.  On any other exit the file is demoted to
# Probe769S36.agda.txt so no unverified .agda is trusted.
ROOT=agents/tasks/LJ-1-769-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT
"$ROOT/runs/run.sh" "$ROOT/Probe769S36.agda" probe769s36-1
rc=$(grep -h '^EXIT=' "$ROOT/runs/probe769s36-1.out" | tail -1)
echo "$rc" > "$ROOT/runs/.obligation-rc"
[ "$rc" = "EXIT=0" ] || mv "$ROOT/Probe769S36.agda" "$ROOT/Probe769S36.agda.txt"

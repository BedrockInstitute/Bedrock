#!/bin/sh
# The obligation rests at Probe769S5.agda.txt (naming rule: it has
# not typechecked).  A temporary same-stem .agda copy runs it; on
# EXIT=0 the copy is PROMOTED (the name is earned), on any other exit
# the copy is deleted at once (the predecessor's script deleted a
# mistyped stem here; this copy deletes the right one).  One Agda
# process, caliber from the pane, never set here.  GATE FIRST: read
# sysctl vm.swapusage and run nothing while swap used is at or above
# 8192 MB; that kill is the box's watchdog, not a wall.
ROOT=agents/tasks/LJ-1-769-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT
cp "$ROOT/Probe769S5.agda.txt" "$ROOT/Probe769S5.agda"
"$ROOT/runs/run.sh" "$ROOT/Probe769S5.agda" probe769s5-1
rc=$(grep -h '^EXIT=' "$ROOT/runs/probe769s5-1.out" | tail -1)
echo "$rc" > "$ROOT/runs/.obligation-rc"
[ "$rc" = "EXIT=0" ] || rm -f "$ROOT/Probe769S5.agda"

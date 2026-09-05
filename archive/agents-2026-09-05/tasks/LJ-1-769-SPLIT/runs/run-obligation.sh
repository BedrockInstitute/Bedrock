#!/bin/sh
# The obligation rests at Probe769Split.agda.txt (naming rule: it had
# not typechecked).  A temporary same-stem .agda copy runs it; on
# EXIT=0 the copy is PROMOTED (the name is earned), on any other exit
# the copy is deleted at once.  One Agda process, caliber from the
# pane, never set here.
ROOT=agents/tasks/LJ-1-769-SPLIT
cp "$ROOT/Probe769Split.agda.txt" "$ROOT/Probe769Split.agda"
"$ROOT/runs/run.sh" "$ROOT/Probe769Split.agda" probe769split-3
rc=$(grep -h '^EXIT=' "$ROOT/runs/probe769split-3.out" | tail -1)
echo "$rc" > "$ROOT/runs/.obligation-rc"
[ "$rc" = "EXIT=0" ] || rm -f "$ROOT/Probe769Split.agda"

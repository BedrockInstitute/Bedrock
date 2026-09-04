#!/bin/sh
# patient retry: one agda at a time, caliber from the pane, never set here
cd /Users/alsg/Agentic/Bedrock/.pod-state/worktrees/LJ-1-732
i=0
while [ $i -lt 6 ]; do
  i=$((i+1))
  ./agents/tasks/LJ-1-732/runs/run.sh agents/tasks/LJ-1-732/Probe732.agda retry-$i
  if grep -q "^EXIT=0" agents/tasks/LJ-1-732/runs/retry-$i.out; then
    echo "GREEN on retry-$i"; break
  fi
  sleep 240
done

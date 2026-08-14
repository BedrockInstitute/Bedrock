#!/bin/bash
# LJ-1.214: SERIES 1, the decisive 3-arm paired series.
# Arms: ProbeDelete (revert c8a628b only), ProbePlain (master), ProbeMinusArNum
# (revert a01ef58 + c8a628b).  Rotation order, 3 kept runs each.  ONE agda
# process at a time.
cd /Users/alsg/Agentic/Bedrock
for i in 1 2 3; do
  bash agents/tasks/LJ-1-214/run_one.sh ProbeDelete    "d$i"
  bash agents/tasks/LJ-1-214/run_one.sh ProbePlain     "p$i"
  bash agents/tasks/LJ-1-214/run_one.sh ProbeMinusArNum "m$i"
done
echo "SERIES 1 DONE"

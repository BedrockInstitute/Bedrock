#!/bin/bash
# LJ-1.214: SERIES 2, the reversed-order series to cancel drift.
# Same three arms, order reversed from series 1.  ONE agda process at a time.
cd /Users/alsg/Agentic/Bedrock
for i in 1 2 3; do
  bash agents/tasks/LJ-1-214/run_one.sh ProbeMinusArNum "m$i"
  bash agents/tasks/LJ-1-214/run_one.sh ProbePlain     "p$i"
  bash agents/tasks/LJ-1-214/run_one.sh ProbeDelete    "d$i"
done
echo "SERIES 2 DONE"

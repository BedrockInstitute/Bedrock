#!/bin/bash
# LJ-1.209: the PAIRED within-series measurement.
# One series, one machine state, the two arms alternating, three kept runs
# each.  ONE agda process at a time.  The `validate` run of ProbeSeal is the
# discarded warm-up.
cd /Users/alsg/Agentic/Bedrock
for i in 1 2 3; do
  bash agents/tasks/LJ-1-209/run_one.sh ProbePlain "p$i"
  bash agents/tasks/LJ-1-209/run_one.sh ProbeSeal "s$i"
done
echo "SERIES DONE"

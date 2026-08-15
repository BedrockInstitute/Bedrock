#!/bin/zsh
# LJ-1.289 cold-run harness. ONE agda process from this agent.
# Usage: measure.sh <label> [extra agda flags...]
# The target is always the MASTER src/L/Coding/EnvSupply.lagda.md.
# The master's own .agdai is deleted before each run, so the run is cold in
# the module and warm in its dependencies. This is [LJ-1.287]'s harness with
# the probe path replaced by the master path.
# CLOCK: time.time() is the wall-clock epoch and is comparable across
# processes ([LJ-1.283] section 8). When the run carries --profile, agda's
# own Total is the figure of record and this wall figure is the cross-check.
set -u
ROOT=/Users/alsg/Agentic/Bedrock
LABEL=$1; shift
FILE=src/L/Coding/EnvSupply.lagda.md
IFACE=$ROOT/_build/2.8.0/agda/src/L/Coding/EnvSupply.agdai
cd $ROOT
rm -f "$IFACE"
LB=$(uptime | sed 's/.*load averages: //')
S=$(python3 -c 'import time;print(time.time())')
GHCRTS="-A64m -I0 -M8g" agda "$@" "$FILE" > agents/tasks/LJ-1-289/runs/${LABEL}.out 2>&1
RC=$?
E=$(python3 -c "import time;print('%.2f'%(time.time()-$S))")
LA=$(uptime | sed 's/.*load averages: //')
echo "${LABEL},${RC},${E},${LB},${LA}" | tee -a agents/tasks/LJ-1-289/timings.csv

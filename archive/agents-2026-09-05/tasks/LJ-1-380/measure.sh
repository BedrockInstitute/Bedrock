#!/bin/zsh
# LJ-1.380 cold-run harness. ONE agda process from this agent.
# Usage: measure.sh <file-path-rel-to-root> <label> [extra agda flags...]
# Clears the module's own .agdai before the run, so the run is cold in the
# module and warm in its dependencies. Agda 2.8.0 writes interfaces to
# _build/2.8.0/agda/<path>.agdai by the _build convention.
# CLOCK: wall-clock epoch, comparable across processes ([LJ-1.283] section 8).
# When the run carries --profile, agda's own Total is the figure of record
# and this wall figure is the cross-check.
set -u
ROOT=/Users/alsg/Agentic/Bedrock
FILE=$1; shift
LABEL=$1; shift
cd $ROOT
STEM=${FILE%%.lagda.md}
IFACE=_build/2.8.0/agda/${STEM}.agdai
rm -f "$IFACE"
LB=$(uptime | sed 's/.*load averages: //')
SLOTS=$(ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l | tr -d ' ')
S=$(python3 -c 'import time;print(time.time())')
mkdir -p agents/tasks/LJ-1-380/runs
GHCRTS="-A64m -I0 -M8g" agda "$@" "$FILE" > agents/tasks/LJ-1-380/runs/${LABEL}.out 2>&1
RC=$?
E=$(python3 -c "import time;print('%.2f'%(time.time()-$S))")
LA=$(uptime | sed 's/.*load averages: //')
echo "${LABEL},${RC},${E},${SLOTS},${LB},${LA}" | tee -a agents/tasks/LJ-1-380/timings.csv

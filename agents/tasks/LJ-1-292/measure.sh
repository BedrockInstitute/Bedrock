#!/bin/zsh
# LJ-1.292 cold-run harness. ONE agda process from this agent.
# Usage: measure.sh <ProbeBaseName> <label> [extra agda flags...]
# Clears the probe's own .agdai before the run, so the run is cold in the
# module and warm in its dependencies.
# CLOCK: time.time() is the wall-clock epoch and is comparable across
# processes. time.monotonic() is NOT on this machine: its reference point is
# the calling process's start ([LJ-1.283] section 8). When the run carries
# --profile, agda's own Total is the figure of record and this wall figure is
# the cross-check.
set -u
ROOT=/Users/alsg/Agentic/Bedrock
BASE=$1; shift
LABEL=$1; shift
FILE=agents/tasks/LJ-1-292/${BASE}.lagda.md
IFACE=$ROOT/_build/2.8.0/agda/agents/tasks/LJ-1-292/${BASE}.agdai
cd $ROOT
rm -f "$IFACE"
LB=$(uptime | sed 's/.*load averages: //')
S=$(python3 -c 'import time;print(time.time())')
GHCRTS="-A64m -I0 -M8g" agda "$@" "$FILE" > agents/tasks/LJ-1-292/runs/${LABEL}.out 2>&1
RC=$?
E=$(python3 -c "import time;print('%.2f'%(time.time()-$S))")
LA=$(uptime | sed 's/.*load averages: //')
echo "${LABEL},${BASE},${RC},${E},${LB},${LA}" | tee -a agents/tasks/LJ-1-292/timings.csv

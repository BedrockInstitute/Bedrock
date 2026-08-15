#!/bin/zsh
# LJ-1.322 run harness. ONE agda process from this agent (C-12).
# Usage: measure.sh <label> [extra agda flags...]
#
# The run is COLD IN THE MODULE and WARM IN ITS DEPENDENCIES, which is how
# `scripts/measure/check-timing.py:232-291` measures and how the ledger's
# `[[hot]]` rows were taken. It removes the module's own interface, times the
# run, and writes the raw agda output to runs/<label>.out. The raw file is the
# evidence (C-53); this script quotes nothing.
#
# The caliber is `-A64m -I0 -M8g`, which is the brief's, and the cap is never
# raised.
set -u
ROOT=/Users/alsg/Agentic/Bedrock
LABEL=$1; shift
FILE=src/L/Condensation.lagda.md
IFACE=$ROOT/_build/2.8.0/agda/src/L/Condensation.agdai
cd $ROOT
SB=$(ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l | tr -d ' ')
LB=$(uptime | sed 's/.*load averages: //')
rm -f "$IFACE"
# time.time() is the WALL CLOCK epoch and is comparable across processes.
S=$(python3 -c 'import time;print(time.time())')
GHCRTS="-A64m -I0 -M8g" agda "$@" "$FILE" > agents/tasks/LJ-1-322/runs/${LABEL}.out 2>&1
RC=$?
E=$(python3 -c "import time;print('%.2f'%(time.time()-$S))")
LA=$(uptime | sed 's/.*load averages: //')
SA=$(ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l | tr -d ' ')
echo "${LABEL},${RC},${E},${SB},${SA},${LB},${LA}" | tee -a agents/tasks/LJ-1-322/timings.csv

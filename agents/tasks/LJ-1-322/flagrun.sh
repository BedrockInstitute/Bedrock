#!/bin/zsh
# LJ-1.322 isolated-flag harness. ONE agda process from this agent (C-12).
# Usage: flagrun.sh <label> [pragma-flags...]
#
# WHY THIS EXISTS. A flag on the COMMAND LINE applies to the whole run, and
# `--no-syntactic-equality` is an interface-reloading option, so a command-line
# run re-elaborates the entire dependency closure, including the cubical
# library. MEASURED by this task's run b1. A flag in the FILE's own OPTIONS
# pragma applies to that file alone, because neither flag is infective or
# coinfective (2.8.0 options page).
#
# So this harness writes the flags into `CondProbe.lagda.md`'s OPTIONS line,
# runs the file cold with its dependencies warm, and restores the base line.
# `CondProbe.lagda.md` is `src/L/Condensation.lagda.md` with ONE line changed,
# the module name. `diff` returns 4 lines against the master.
#
# The caliber is `-A64m -I0 -M8g` and the cap is never raised.
set -u
ROOT=/Users/alsg/Agentic/Bedrock
LABEL=$1; shift
BASE='{-# OPTIONS --cubical --safe --guardedness #-}'
FILE=agents/tasks/LJ-1-322/CondProbe.lagda.md
IFACE=$ROOT/_build/2.8.0/agda/agents/tasks/LJ-1-322/CondProbe.agdai
cd $ROOT
if [ $# -gt 0 ]; then
  NEW="{-# OPTIONS --cubical --safe --guardedness $* #-}"
else
  NEW=$BASE
fi
python3 - "$FILE" "$NEW" <<'PY'
import sys, pathlib
p, new = pathlib.Path(sys.argv[1]), sys.argv[2]
lines = p.read_text().split("\n")
for i, l in enumerate(lines):
    if l.startswith("{-# OPTIONS"):
        lines[i] = new
        break
p.write_text("\n".join(lines))
PY
SB=$(ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l | tr -d ' ')
LB=$(uptime | sed 's/.*load averages: //')
rm -f "$IFACE"
S=$(python3 -c 'import time;print(time.time())')
GHCRTS="-A64m -I0 -M8g" agda "$FILE" > agents/tasks/LJ-1-322/runs/${LABEL}.out 2>&1
RC=$?
E=$(python3 -c "import time;print('%.2f'%(time.time()-$S))")
LA=$(uptime | sed 's/.*load averages: //')
SA=$(ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l | tr -d ' ')
# Restore the base OPTIONS line, so the committed probe carries the master's
# header and never a flag from the last run.
python3 - "$FILE" "$BASE" <<'PY'
import sys, pathlib
p, new = pathlib.Path(sys.argv[1]), sys.argv[2]
lines = p.read_text().split("\n")
for i, l in enumerate(lines):
    if l.startswith("{-# OPTIONS"):
        lines[i] = new
        break
p.write_text("\n".join(lines))
PY
echo "${LABEL},${RC},${E},${SB},${SA},${LB},${LA}" | tee -a agents/tasks/LJ-1-322/timings.csv

#!/bin/bash
# LJ-1.275, CURE B section 5.3: re-run [LJ-1.214]'s ProbePlain arm TODAY.
#
# C-32 says a cure invalidates every downstream measurement.  Two commits
# landed on the chapter and its upstream after [LJ-1.214] measured the 8.2 s
# Deserialization term, and that term was never re-run.  This script re-runs
# it.  It READS agents/tasks/LJ-1-214/ and writes ONLY into
# agents/tasks/LJ-1-275/runs/, because LJ-1-214 is a frozen record.
cd /Users/alsg/Agentic/Bedrock || exit 1
P=ProbePlain
OUT=agents/tasks/LJ-1-275/runs/probeplain.rerun.txt
mkdir -p agents/tasks/LJ-1-275/runs
find _build -name "${P}.agdai" -delete 2>/dev/null
{
  echo "# module agents/tasks/LJ-1-214/$P.agda, re-run by [LJ-1.275]"
  echo "# GHCRTS -A64m -I0 -M8g"
  echo "# command agda --profile=internal agents/tasks/LJ-1-214/$P.agda"
  echo "# load before $(uptime | sed 's/.*load averages\?://')"
  echo "# started $(date '+%Y-%m-%d %H:%M:%S')"
  START=$(.venv/bin/python -c 'import time; print(time.time())')
  GHCRTS="-A64m -I0 -M8g" agda --profile=internal "agents/tasks/LJ-1-214/$P.agda" 2>&1
  RC=$?
  END=$(.venv/bin/python -c 'import time; print(time.time())')
  echo "# wall seconds $(.venv/bin/python -c "print(f'{$END - $START:.2f}')")"
  echo "# exit $RC"
  echo "# load after $(uptime | sed 's/.*load averages\?://')"
} > "$OUT"
grep -E "^# exit|^# wall|Deserialization|^Total" "$OUT" | head -8
echo "-> $OUT"

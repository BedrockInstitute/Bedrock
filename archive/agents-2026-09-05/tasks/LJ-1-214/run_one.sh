#!/bin/bash
# LJ-1.214: one cold `--profile=internal` run of one probe arm.
# Usage: run_one.sh <ProbeName> <tag>
cd /Users/alsg/Agentic/Bedrock
P=$1
TAG=$2
OUT=agents/tasks/LJ-1-214/runs/${P}.${TAG}.txt
mkdir -p agents/tasks/LJ-1-214/runs
find _build -name "${P}.agdai" -delete 2>/dev/null
{
  echo "# module agents/tasks/LJ-1-214/$P.agda"
  echo "# GHCRTS -A64m -I0 -M8g"
  echo "# command agda --profile=internal agents/tasks/LJ-1-214/$P.agda"
  echo "# load before $(uptime | sed 's/.*load averages\?://')"
  echo "# started $(date '+%Y-%m-%d %H:%M:%S')"
  START=$(.venv/bin/python -c 'import time; print(time.time())')
  GHCRTS="-A64m -I0 -M8g" agda --profile=internal agents/tasks/LJ-1-214/$P.agda 2>&1
  RC=$?
  END=$(.venv/bin/python -c 'import time; print(time.time())')
  echo "# wall seconds $(.venv/bin/python -c "print(f'{$END - $START:.2f}')")"
  echo "# exit $RC"
  echo "# load after $(uptime | sed 's/.*load averages\?://')"
} > "$OUT"
grep -E "^# exit|^# wall|Deserialization|^Total" "$OUT" | head -8
echo "-> $OUT"

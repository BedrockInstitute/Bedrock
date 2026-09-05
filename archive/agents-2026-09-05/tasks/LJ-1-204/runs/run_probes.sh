#!/bin/bash
# LJ-1.204: cold profile of the two isolation probes.
cd /Users/alsg/Agentic/Bedrock
for p in ProbeMinusArNum ProbeMinusBound; do
  OUT=agents/tasks/LJ-1-204/runs/${p}.int1.txt
  {
    echo "# module agents/tasks/LJ-1-204/$p.agda"
    echo "# GHCRTS -A64m -I0 -M8g"
    echo "# command agda --profile=internal agents/tasks/LJ-1-204/$p.agda"
    echo "# load before $(uptime | sed 's/.*load averages\?://')"
    echo "# started $(date '+%Y-%m-%d %H:%M:%S')"
    START=$(python3 -c 'import time; print(time.time())')
    GHCRTS="-A64m -I0 -M8g" agda --profile=internal agents/tasks/LJ-1-204/$p.agda 2>&1
    RC=$?
    END=$(python3 -c 'import time; print(time.time())')
    echo "# wall seconds $(python3 -c "print(f'{$END - $START:.2f}')")"
    echo "# exit $RC"
    echo "# load after $(uptime | sed 's/.*load averages\?://')"
  } > "$OUT"
  echo "$p done rc=$RC -> $OUT"
done
echo "ALL PROBES DONE"

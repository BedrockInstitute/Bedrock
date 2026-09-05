#!/bin/bash
# LJ-1.204 today-measurement: Deserialization at current tree.
cd /Users/alsg/Agentic/Bedrock
OUT=agents/tasks/LJ-1-204/runs/src_L_Condensation.today.int1.txt
LINES=$(awk '/^```agda/{f=1;next} /^```/{f=0} f&&NF' src/L/Condensation.lagda.md | wc -l | tr -d ' ')
{
  echo "# module src/L/Condensation.lagda.md"
  echo "# in-fence lines $LINES"
  echo "# GHCRTS -A64m -I0 -M8g"
  echo "# command agda --profile=internal src/L/Condensation.lagda.md"
  echo "# load before $(uptime | sed 's/.*load averages\?://')"
  echo "# started $(date '+%Y-%m-%d %H:%M:%S')"
  START=$(python3 -c 'import time; print(time.time())')
  GHCRTS="-A64m -I0 -M8g" agda --profile=internal src/L/Condensation.lagda.md 2>&1
  RC=$?
  END=$(python3 -c 'import time; print(time.time())')
  echo "# wall seconds $(python3 -c "print(f'{$END - $START:.2f}')")"
  echo "# exit $RC"
  echo "# load after $(uptime | sed 's/.*load averages\?://')"
} > "$OUT"
echo "done rc=$RC out=$OUT"

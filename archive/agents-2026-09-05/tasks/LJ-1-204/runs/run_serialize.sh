#!/bin/bash
cd /Users/alsg/Agentic/Bedrock
IFACE=_build/2.8.0/agda/src/L/Condensation.agdai
OUT=agents/tasks/LJ-1-204/runs/src_L_Condensation.serialize1.txt
if [ -f "$IFACE" ]; then mv "$IFACE" "$IFACE.lj204-stash"; STASHED=1; else STASHED=0; fi
{
  echo "# command agda --profile=serialize src/L/Condensation.lagda.md"
  echo "# load before $(uptime | sed 's/.*load averages\?://')"
  START=$(python3 -c 'import time; print(time.time())')
  GHCRTS="-A64m -I0 -M8g" agda --profile=serialize src/L/Condensation.lagda.md 2>&1
  RC=$?
  END=$(python3 -c 'import time; print(time.time())')
  echo "# wall seconds $(python3 -c "print(f'{$END - $START:.2f}')")"
  echo "# exit $RC"
  echo "# load after $(uptime | sed 's/.*load averages\?://')"
} > "$OUT"
if [ "$STASHED" = "1" ]; then rm -f "$IFACE"; mv "$IFACE.lj204-stash" "$IFACE"; fi
echo "done rc=$RC -> $OUT"

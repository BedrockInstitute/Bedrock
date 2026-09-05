#!/bin/bash
# LJ-1.204: COLD measurement of Deserialization, 3 runs, interface stashed each run.
cd /Users/alsg/Agentic/Bedrock
IFACE=_build/2.8.0/agda/src/L/Condensation.agdai
LINES=$(awk '/^```agda/{f=1;next} /^```/{f=0} f&&NF' src/L/Condensation.lagda.md | wc -l | tr -d ' ')
for i in 1 2 3; do
  OUT=agents/tasks/LJ-1-204/runs/src_L_Condensation.today.int$i.txt
  # stash the target interface (cold)
  if [ -f "$IFACE" ]; then mv "$IFACE" "$IFACE.lj204-stash"; STASHED=1; else STASHED=0; fi
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
  if [ "$STASHED" = "1" ]; then
    # keep the fresh interface? restore stash so tree state matches report
    rm -f "$IFACE"; mv "$IFACE.lj204-stash" "$IFACE"
  fi
  echo "run $i done rc=$RC -> $OUT"
done
echo "ALL DONE"

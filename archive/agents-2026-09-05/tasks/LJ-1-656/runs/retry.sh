#!/bin/sh
# Wait for system memory headroom, then run one Agda process.  The
# machine is SHARED and `omlx-server` held 15.7 GB while system-wide
# free memory read 3 to 4 percent; at that pressure macOS SIGKILLs Agda
# (EXIT=137) at a footprint the 2 GB caliber never reaches.  This waits
# instead of retrying blind: rerunning the SAME code hoping for a
# different result is forbidden, and this is not that -- the code is
# fixed and the RESOURCE is what changes.
# usage: retry.sh <file.agda> <out-name> <min-free-pct> <max-waits>
f="$1"; out="agents/tasks/LJ-1-656/runs/$2.out"; want="$3"; n="${4:-40}"
i=0
while [ "$i" -lt "$n" ]; do
  free=$(memory_pressure -Q 2>/dev/null | sed -n 's/.*free percentage: \([0-9]*\)%.*/\1/p')
  [ -z "$free" ] && free=0
  if [ "$free" -ge "$want" ]; then
    {
      echo "GHCRTS=[$GHCRTS]"
      echo "free=${free}% at start, waited ${i} polls of 30 s"
      echo "started $(date -u +%Y-%m-%dT%H:%M:%SZ)"
    } > "$out"
    /usr/bin/time -l agda "$f" >> "$out" 2>&1
    rc=$?
    echo "EXIT=$rc" >> "$out"
    echo "ended $(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$out"
    [ "$rc" -ne 137 ] && exit 0
    echo "SIGKILL at free=${free}%, waiting again" >> "$out"
  fi
  i=$((i+1))
  sleep 30
done
echo "GAVE UP after $n polls" >> "$out"
exit 2

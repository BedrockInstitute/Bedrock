#!/bin/bash
# One Agda process per run, wide caliber read from the pane, never set here.
# usage: run.sh <file.agda> <tag>
F="$1"; T="$2"
{ echo "GHCRTS=[$GHCRTS]"; echo "cap 600s (perl alarm)"; echo "started $(date -u +%Y-%m-%dT%H:%M:%SZ)";
  perl -e 'alarm 600; exec @ARGV' /usr/bin/time -l agda "$F" 2>&1; echo "EXIT=$?"; } > "agents/tasks/LJ-1-740/runs/$T.out" 2>&1
tail -3 "agents/tasks/LJ-1-740/runs/$T.out"

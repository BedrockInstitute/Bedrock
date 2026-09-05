#!/bin/sh
# [LJ-1.634] run wrapper. One agda process at a time. Wall cap via perl
# alarm: SIGALRM kills the exec'd agda past the cap. THE PROGRAM SET
# GHCRTS ON THIS PANE (-A64m -I0 -M4g, HEAVY); this wrapper does not
# touch it. Same mechanism as [LJ-1.630]'s runs/run.sh.
#
# usage: sh runs/run.sh <out-file> <cap-seconds> <agda-file>
out=$1
cap=$2
file=$3
{
  echo "wallcap=${cap}s (perl alarm; SIGALRM kills agda past the cap)"
  echo "GHCRTS=[$GHCRTS]"
  date -u +"started %Y-%m-%dT%H:%M:%SZ"
  /usr/bin/time -l perl -e 'alarm shift; exec @ARGV' "$cap" agda "$file"
  echo "EXIT=$?"
  date -u +"ended %Y-%m-%dT%H:%M:%SZ"
} > "$out" 2>&1

#!/bin/sh
# [LJ-1.629] run wrapper.  One agda process at a time.  The wall cap is
# perl's alarm: SIGALRM kills the exec'd agda, so a hung typecheck exits
# instead of running to the machine's end.  The cap is an argument, in
# seconds, and every .out records it.  THE PROGRAM SET GHCRTS ON THIS
# PANE; this wrapper does not touch it.  Same mechanism as [LJ-1.627]'s
# (agents/tasks/LJ-1-627/runs/run.sh, measured 2026-08-23).
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

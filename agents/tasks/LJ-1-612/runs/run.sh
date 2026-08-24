#!/bin/sh
# [LJ-1.612] run wrapper.  One agda process at a time.  The wall cap is
# perl's alarm: SIGALRM kills the exec'd agda, so a hung typecheck exits
# instead of running to the machine's end.  The cap is an argument, in
# seconds, and every .out records it.  THE PROGRAM SET GHCRTS ON THIS
# PANE; this wrapper does not touch it.
#
# Taken from [LJ-1.605] via [LJ-1.607]'s runs/run.sh, with one change:
# every argument after <out-file> <cap-seconds> is passed through to
# agda, so a run can add the -i include roots the flag cure needs.
#
# usage: sh runs/run.sh <out-file> <cap-seconds> <agda-arg>...
out=$1; shift
cap=$1; shift
file=$1; shift
{
  echo "wallcap=${cap}s (perl alarm; SIGALRM kills agda past the cap)"
  echo "GHCRTS=[$GHCRTS]"
  date -u +"started %Y-%m-%dT%H:%M:%SZ"
  /usr/bin/time -l perl -e 'alarm shift; exec @ARGV' "$cap" agda "$file" "$@"
  echo "EXIT=$?"
  date -u +"ended %Y-%m-%dT%H:%M:%SZ"
} > "$out" 2>&1

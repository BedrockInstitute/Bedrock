#!/bin/bash
# [LJ-1.709] DIAGNOSTIC wrapper ONLY.  Never a priced number.
# Runs agda in bash's foreground so wait(1) yields the exact code
# (128+N names the signal), and samples all agda RSS once a second.
# usage: sh runs/run-diag.sh <out-file> <cap-seconds> <agda-file>
out=$1
cap=$2
file=$3
{
  echo "diag wallcap=${cap}s GHCRTS=[$GHCRTS]"
  date -u +"started %Y-%m-%dT%H:%M:%SZ"
  perl -e 'alarm shift; exec @ARGV' "$cap" agda "$file" &
  apid=$!
  (
    for i in $(seq 1 120); do
      ps axo pid,rss,comm | awk '$3 ~ /[Aa]gda$/ {print strftime("%H:%M:%S"), $1, $2}' 
      sleep 1
    done
  ) &
  spid=$!
  wait "$apid"
  echo "AGDA-WAIT-RC=$?  (128+N => killed by signal N)"
  kill "$spid" 2>/dev/null
  date -u +"ended %Y-%m-%dT%H:%M:%SZ"
} > "$out" 2>&1
tail -5 "$out"

#!/bin/zsh
set -u
for m in UpperAgree LowerAgree TwelveAgree; do
  rm -f _build/2.8.0/agda/src/L/Condensation/$m.agdai
done
for m in UpperAgree LowerAgree TwelveAgree; do
  s=$(date +%s.%N)
  agda src/L/Condensation/$m.lagda.md > /tmp/lj158.$m.txt 2>&1
  e=$?
  f=$(date +%s.%N)
  echo "$m: exit $e, $(echo "$f - $s" | bc) s"
  [ $e -ne 0 ] && tail -25 /tmp/lj158.$m.txt
done

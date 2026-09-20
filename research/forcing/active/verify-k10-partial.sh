#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p K10/logs
for k10_source in K10/*.agda; do
  k10_processes=$(ps -axo comm) || exit 1
  k10_active=$(printf '%s\n' "$k10_processes" | awk '$0 ~ /(^|\/)agda$/ {n++} END {print n+0}')
  if [ "$k10_active" -ge 2 ]; then
    printf 'Agda slots full before %s.\n' "$k10_source"
    exit 1
  fi
  k10_name=${k10_source##*/}
  k10_exit=0
  GHCRTS='-A64m -I0 -M8g' agda "$k10_source" > "K10/logs/$k10_name.log" 2>&1 || k10_exit=$?
  printf '\nEXIT=%s\n' "$k10_exit" >> "K10/logs/$k10_name.log"
  printf '%-32s exit=%s\n' "$k10_name" "$k10_exit"
  if [ "$k10_exit" -ne 0 ]; then
    sed -n '1,100p' "K10/logs/$k10_name.log"
    exit "$k10_exit"
  fi
done
printf 'K10 PARTIAL MODULES VERIFIED; this is not the K10 acceptance gate.\n'

#!/bin/sh
set -u
cd "$(dirname "$0")" || exit 1
mkdir -p K9/logs
for k9_source in K9/*.agda; do
  k9_active=$(ps -axo comm | awk '$0 ~ /(^|\/)agda$/ {n++} END {print n+0}')
  if [ "$k9_active" -ge 2 ]; then
    printf 'Agda slots full before %s; retry when a slot is free.\n' "$k9_source"
    exit 1
  fi
  k9_name=${k9_source##*/}
  k9_started=$(date +%s)
  GHCRTS='-A64m -I0 -M8g' agda "$k9_source" > "K9/logs/$k9_name.log" 2>&1
  k9_exit=$?
  k9_finished=$(date +%s)
  printf '\nEXIT=%s\n' "$k9_exit" >> "K9/logs/$k9_name.log"
  printf '%-28s exit=%s %ss\n' "$k9_name" "$k9_exit" "$((k9_finished - k9_started))"
  if [ "$k9_exit" -ne 0 ]; then
    sed -n '1,100p' "K9/logs/$k9_name.log"
    exit "$k9_exit"
  fi
done
printf 'K9 ALL MODULES VERIFIED\n'

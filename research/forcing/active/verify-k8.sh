#!/bin/sh
set -u
cd "$(dirname "$0")" || exit 1
mkdir -p K8/logs
for k8_source in K8/*.agda; do
  k8_active=$(ps -axo comm | awk '$0 ~ /(^|\/)agda$/ {n++} END {print n+0}')
  if [ "$k8_active" -ge 2 ]; then
    printf 'Agda slots full before %s; retry when a slot is free.\n' "$k8_source"
    exit 1
  fi
  k8_name=${k8_source##*/}
  k8_started=$(date +%s)
  GHCRTS='-A64m -I0 -M8g' agda "$k8_source" > "K8/logs/$k8_name.log" 2>&1
  k8_exit=$?
  k8_finished=$(date +%s)
  printf '\nEXIT=%s\n' "$k8_exit" >> "K8/logs/$k8_name.log"
  printf '%-28s exit=%s %ss\n' "$k8_name" "$k8_exit" "$((k8_finished - k8_started))"
  if [ "$k8_exit" -ne 0 ]; then
    sed -n '1,100p' "K8/logs/$k8_name.log"
    exit "$k8_exit"
  fi
done
printf 'K8 ALL MODULES VERIFIED\n'

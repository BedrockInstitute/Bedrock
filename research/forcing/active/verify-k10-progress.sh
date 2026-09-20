#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p progress-logs

check_slots() {
  progress_processes=$(ps -axo comm) || exit 1
  progress_active=$(printf '%s\n' "$progress_processes" | awk '$0 ~ /(^|\/)agda$/ {n++} END {print n+0}')
  if [ "$progress_active" -ge 2 ]; then
    printf 'Agda slots full. Retry when a slot is free.\n'
    exit 1
  fi
}

progress_count=0
for progress_source in K7/*.agda K8/*.agda K9/*.agda K10/*.agda; do
  check_slots
  progress_name=$(printf '%s' "$progress_source" | tr '/' '_')
  progress_exit=0
  GHCRTS='-A64m -I0 -M8g' agda "$progress_source" > "progress-logs/$progress_name.log" 2>&1 || progress_exit=$?
  printf '\nEXIT=%s\n' "$progress_exit" >> "progress-logs/$progress_name.log"
  printf '%-40s exit=%s\n' "$progress_source" "$progress_exit"
  if [ "$progress_exit" -ne 0 ]; then
    sed -n '1,100p' "progress-logs/$progress_name.log"
    exit "$progress_exit"
  fi
  progress_count=$((progress_count + 1))
done

check_slots
progress_exit=0
GHCRTS='-A64m -I0 -M8g' agda Controls/Negative/MissingFunction.agda > progress-logs/MissingFunction.log 2>&1 || progress_exit=$?
printf '\nEXIT=%s\n' "$progress_exit" >> progress-logs/MissingFunction.log
if [ "$progress_exit" -ne 42 ] || ! rg -q 'IsFunctionφ' progress-logs/MissingFunction.log || ! rg -q 'PB.countable-from-ccc₂' progress-logs/MissingFunction.log; then
  sed -n '1,100p' progress-logs/MissingFunction.log
  printf 'Missing-function negative control did not fail as expected.\n'
  exit 1
fi
printf '%s positive modules verified; missing-function control rejected (expected exit 42).\n' "$progress_count"
printf 'K10 progress checkpoint verified. Full K10 acceptance remains open.\n'

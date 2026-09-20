#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p repair-logs

check_slots() {
  repair_processes=$(ps -axo comm) || exit 1
  repair_active=$(printf '%s\n' "$repair_processes" | awk '$0 ~ /(^|\/)agda$/ {n++} END {print n+0}')
  if [ "$repair_active" -ge 2 ]; then
    printf 'Agda slots full. Retry when a slot is free.\n'
    exit 1
  fi
}

repair_count=0
for repair_source in K7/*.agda K8/*.agda K9/*.agda K10/*.agda; do
  check_slots
  repair_name=$(printf '%s' "$repair_source" | tr '/' '_')
  repair_exit=0
  GHCRTS='-A64m -I0 -M8g' agda "$repair_source" > "repair-logs/$repair_name.log" 2>&1 || repair_exit=$?
  printf '\nEXIT=%s\n' "$repair_exit" >> "repair-logs/$repair_name.log"
  printf '%-40s exit=%s\n' "$repair_source" "$repair_exit"
  if [ "$repair_exit" -ne 0 ]; then
    sed -n '1,100p' "repair-logs/$repair_name.log"
    exit "$repair_exit"
  fi
  repair_count=$((repair_count + 1))
done

check_slots
repair_exit=0
GHCRTS='-A64m -I0 -M8g' agda Controls/Negative/MissingFunction.agda > repair-logs/MissingFunction.log 2>&1 || repair_exit=$?
printf '\nEXIT=%s\n' "$repair_exit" >> repair-logs/MissingFunction.log
if [ "$repair_exit" -ne 42 ] || ! rg -q 'IsFunctionφ' repair-logs/MissingFunction.log || ! rg -q 'PB.countable-from-ccc₂' repair-logs/MissingFunction.log; then
  sed -n '1,100p' repair-logs/MissingFunction.log
  printf 'Missing-function negative control did not fail as expected.\n'
  exit 1
fi
printf '%s positive modules verified; missing-function control rejected (expected exit 42).\n' "$repair_count"
printf 'K7 local-interface repair verified. Full K10 acceptance is separate.\n'

#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p generic-logs

check_slots() {
  generic_processes=$(ps -axo comm) || exit 1
  generic_active=$(printf '%s\n' "$generic_processes" | awk '$0 ~ /(^|\/)agda$/ {n++} END {print n+0}')
  if [ "$generic_active" -ge 2 ]; then
    printf 'Agda slots full. Retry when a slot is free.\n'
    exit 1
  fi
}

generic_count=0
for generic_source in K7/*.agda K8/*.agda K9/*.agda K10/*.agda K11/*.agda; do
  check_slots
  generic_name=$(printf '%s' "$generic_source" | tr '/' '_')
  generic_exit=0
  GHCRTS='-A64m -I0 -M8g' agda "$generic_source" > "generic-logs/$generic_name.log" 2>&1 || generic_exit=$?
  printf '\nEXIT=%s\n' "$generic_exit" >> "generic-logs/$generic_name.log"
  printf '%-42s exit=%s\n' "$generic_source" "$generic_exit"
  if [ "$generic_exit" -ne 0 ]; then
    sed -n '1,100p' "generic-logs/$generic_name.log"
    exit "$generic_exit"
  fi
  generic_count=$((generic_count + 1))
done

check_negative() {
  check_slots
  generic_fixture=$1
  generic_pattern=$2
  generic_exit=0
  GHCRTS='-A64m -I0 -M8g' agda "Controls/Negative/$generic_fixture.agda" > "generic-logs/$generic_fixture.log" 2>&1 || generic_exit=$?
  printf '\nEXIT=%s\n' "$generic_exit" >> "generic-logs/$generic_fixture.log"
  if [ "$generic_exit" -ne 42 ] || ! rg -q "$generic_pattern" "generic-logs/$generic_fixture.log" || ! rg -q '\[UnequalTerms\]' "generic-logs/$generic_fixture.log"; then
    sed -n '1,100p' "generic-logs/$generic_fixture.log"
    printf 'Negative control %s did not fail as expected.\n' "$generic_fixture"
    exit 1
  fi
  printf '%s: expected exit 42 and type error verified.\n' "$generic_fixture"
}

check_negative MissingFunction 'PB.countable-from-ccc₂'
check_negative MissingValueFunction 'Proof.functionFo'
check_negative MissingCheckReading 'chkFo'
check_negative MissingOnto 'OrderType.Onto'
printf '%s positive modules and four expected-failure controls verified.\n' "$generic_count"
printf 'Generic-constructor regression verified; full K10 and K11 remain separate.\n'

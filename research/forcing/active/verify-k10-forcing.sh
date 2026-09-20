#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p forcing-logs

check_slots() {
  forcing_processes=$(ps -axo comm) || exit 1
  forcing_active=$(printf '%s\n' "$forcing_processes" | awk '$0 ~ /(^|\/)agda$/ {n++} END {print n+0}')
  if [ "$forcing_active" -ge 2 ]; then
    printf 'Agda slots full. Retry when a slot is free.\n'
    exit 1
  fi
}

forcing_count=0
for forcing_source in K7/*.agda K8/*.agda K9/*.agda K10/*.agda; do
  check_slots
  forcing_name=$(printf '%s' "$forcing_source" | tr '/' '_')
  forcing_exit=0
  GHCRTS='-A64m -I0 -M8g' agda "$forcing_source" > "forcing-logs/$forcing_name.log" 2>&1 || forcing_exit=$?
  printf '\nEXIT=%s\n' "$forcing_exit" >> "forcing-logs/$forcing_name.log"
  printf '%-42s exit=%s\n' "$forcing_source" "$forcing_exit"
  if [ "$forcing_exit" -ne 0 ]; then
    sed -n '1,100p' "forcing-logs/$forcing_name.log"
    exit "$forcing_exit"
  fi
  forcing_count=$((forcing_count + 1))
done

check_negative() {
  check_slots
  forcing_fixture=$1
  forcing_pattern=$2
  forcing_exit=0
  GHCRTS='-A64m -I0 -M8g' agda "Controls/Negative/$forcing_fixture.agda" > "forcing-logs/$forcing_fixture.log" 2>&1 || forcing_exit=$?
  printf '\nEXIT=%s\n' "$forcing_exit" >> "forcing-logs/$forcing_fixture.log"
  if [ "$forcing_exit" -ne 42 ] || ! rg -q "$forcing_pattern" "forcing-logs/$forcing_fixture.log" || ! rg -q '\[UnequalTerms\]' "forcing-logs/$forcing_fixture.log"; then
    sed -n '1,100p' "forcing-logs/$forcing_fixture.log"
    printf 'Negative control %s did not fail as expected.\n' "$forcing_fixture"
    exit 1
  fi
  printf '%s: expected exit 42 and type error verified.\n' "$forcing_fixture"
}

check_negative MissingFunction 'PB.countable-from-ccc₂'
check_negative MissingValueFunction 'Proof.functionFo'
printf '%s positive modules and two expected-failure controls verified.\n' "$forcing_count"
printf 'All-condition function-value checkpoint verified; full K10 remains separate.\n'

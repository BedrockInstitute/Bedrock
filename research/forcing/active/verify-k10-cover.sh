#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p cover-logs

check_slots() {
  cover_processes=$(ps -axo comm) || exit 1
  cover_active=$(printf '%s\n' "$cover_processes" | awk '$0 ~ /(^|\/)agda$/ {n++} END {print n+0}')
  if [ "$cover_active" -ge 2 ]; then
    printf 'Agda slots full. Retry when a slot is free.\n'
    exit 1
  fi
}

cover_count=0
for cover_source in K7/*.agda K8/*.agda K9/*.agda K10/*.agda; do
  check_slots
  cover_name=$(printf '%s' "$cover_source" | tr '/' '_')
  cover_exit=0
  GHCRTS='-A64m -I0 -M8g' agda "$cover_source" > "cover-logs/$cover_name.log" 2>&1 || cover_exit=$?
  printf '\nEXIT=%s\n' "$cover_exit" >> "cover-logs/$cover_name.log"
  printf '%-42s exit=%s\n' "$cover_source" "$cover_exit"
  if [ "$cover_exit" -ne 0 ]; then
    sed -n '1,100p' "cover-logs/$cover_name.log"
    exit "$cover_exit"
  fi
  cover_count=$((cover_count + 1))
done

check_negative() {
  check_slots
  cover_fixture=$1
  cover_pattern=$2
  cover_exit=0
  GHCRTS='-A64m -I0 -M8g' agda "Controls/Negative/$cover_fixture.agda" > "cover-logs/$cover_fixture.log" 2>&1 || cover_exit=$?
  printf '\nEXIT=%s\n' "$cover_exit" >> "cover-logs/$cover_fixture.log"
  if [ "$cover_exit" -ne 42 ] || ! rg -q "$cover_pattern" "cover-logs/$cover_fixture.log" || ! rg -q '\[UnequalTerms\]' "cover-logs/$cover_fixture.log"; then
    sed -n '1,100p' "cover-logs/$cover_fixture.log"
    printf 'Negative control %s did not fail as expected.\n' "$cover_fixture"
    exit 1
  fi
  printf '%s: expected exit 42 and type error verified.\n' "$cover_fixture"
}

check_negative MissingFunction 'PB.countable-from-ccc₂'
check_negative MissingValueFunction 'Proof.functionFo'
check_negative MissingCheckReading 'chkFo'
printf '%s positive modules and three expected-failure controls verified.\n' "$cover_count"
printf 'Cover and definable-family checkpoint verified; full K10 remains separate.\n'

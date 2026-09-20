#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p rank-logs

check_slots() {
  rank_processes=$(ps -axo comm) || exit 1
  rank_active=$(printf '%s\n' "$rank_processes" | awk '$0 ~ /(^|\/)agda$/ {n++} END {print n+0}')
  if [ "$rank_active" -ge 2 ]; then
    printf 'Agda slots full. Retry when a slot is free.\n'
    exit 1
  fi
}

rank_count=0
for rank_source in K7/*.agda K8/*.agda K9/*.agda K10/*.agda; do
  check_slots
  rank_name=$(printf '%s' "$rank_source" | tr '/' '_')
  rank_exit=0
  GHCRTS='-A64m -I0 -M8g' agda "$rank_source" > "rank-logs/$rank_name.log" 2>&1 || rank_exit=$?
  printf '\nEXIT=%s\n' "$rank_exit" >> "rank-logs/$rank_name.log"
  printf '%-42s exit=%s\n' "$rank_source" "$rank_exit"
  if [ "$rank_exit" -ne 0 ]; then
    sed -n '1,100p' "rank-logs/$rank_name.log"
    exit "$rank_exit"
  fi
  rank_count=$((rank_count + 1))
done

check_negative() {
  check_slots
  rank_fixture=$1
  rank_pattern=$2
  rank_exit=0
  GHCRTS='-A64m -I0 -M8g' agda "Controls/Negative/$rank_fixture.agda" > "rank-logs/$rank_fixture.log" 2>&1 || rank_exit=$?
  printf '\nEXIT=%s\n' "$rank_exit" >> "rank-logs/$rank_fixture.log"
  if [ "$rank_exit" -ne 42 ] || ! rg -q "$rank_pattern" "rank-logs/$rank_fixture.log" || ! rg -q '\[UnequalTerms\]' "rank-logs/$rank_fixture.log"; then
    sed -n '1,100p' "rank-logs/$rank_fixture.log"
    printf 'Negative control %s did not fail as expected.\n' "$rank_fixture"
    exit 1
  fi
  printf '%s: expected exit 42 and type error verified.\n' "$rank_fixture"
}

check_negative MissingFunction 'PB.countable-from-ccc₂'
check_negative MissingValueFunction 'Proof.functionFo'
check_negative MissingCheckReading 'chkFo'
check_negative MissingOnto 'OrderType.Onto'
printf '%s positive modules and four expected-failure controls verified.\n' "$rank_count"
printf 'Internal rank checkpoint verified; full K10 remains separate.\n'

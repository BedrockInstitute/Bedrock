#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p order-logs

check_slots() {
  order_processes=$(ps -axo comm) || exit 1
  order_active=$(printf '%s\n' "$order_processes" | awk '$0 ~ /(^|\/)agda$/ {n++} END {print n+0}')
  if [ "$order_active" -ge 2 ]; then
    printf 'Agda slots full. Retry when a slot is free.\n'
    exit 1
  fi
}

order_count=0
for order_source in K7/*.agda K8/*.agda K9/*.agda K10/*.agda; do
  check_slots
  order_name=$(printf '%s' "$order_source" | tr '/' '_')
  order_exit=0
  GHCRTS='-A64m -I0 -M8g' agda "$order_source" > "order-logs/$order_name.log" 2>&1 || order_exit=$?
  printf '\nEXIT=%s\n' "$order_exit" >> "order-logs/$order_name.log"
  printf '%-42s exit=%s\n' "$order_source" "$order_exit"
  if [ "$order_exit" -ne 0 ]; then
    sed -n '1,100p' "order-logs/$order_name.log"
    exit "$order_exit"
  fi
  order_count=$((order_count + 1))
done

check_negative() {
  check_slots
  order_fixture=$1
  order_pattern=$2
  order_exit=0
  GHCRTS='-A64m -I0 -M8g' agda "Controls/Negative/$order_fixture.agda" > "order-logs/$order_fixture.log" 2>&1 || order_exit=$?
  printf '\nEXIT=%s\n' "$order_exit" >> "order-logs/$order_fixture.log"
  if [ "$order_exit" -ne 42 ] || ! rg -q "$order_pattern" "order-logs/$order_fixture.log" || ! rg -q '\[UnequalTerms\]' "order-logs/$order_fixture.log"; then
    sed -n '1,100p' "order-logs/$order_fixture.log"
    printf 'Negative control %s did not fail as expected.\n' "$order_fixture"
    exit 1
  fi
  printf '%s: expected exit 42 and type error verified.\n' "$order_fixture"
}

check_negative MissingFunction 'PB.countable-from-ccc₂'
check_negative MissingValueFunction 'Proof.functionFo'
check_negative MissingCheckReading 'chkFo'
check_negative MissingOnto 'OrderType.Onto'
printf '%s positive modules and four expected-failure controls verified.\n' "$order_count"
printf 'Diagonal order and concrete Cohen checkpoint verified; full K10 remains incomplete.\n'

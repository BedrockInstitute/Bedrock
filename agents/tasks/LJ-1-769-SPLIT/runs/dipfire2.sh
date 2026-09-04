#!/bin/sh
# dipfire2: the promotion protocol over the resting .txt stems.
#
# Every unmeasured stem rests at `.agda.txt` (naming rule).  For each
# row: copy to the same-stem `.agda`, run it (ONE Agda process at a
# time, caliber from the pane, never set here, 1800 s cap), then
# PROMOTE the copy on EXIT=0 (the name is earned) or delete the copy
# on every other exit.  Rows fire only inside a swap dip (used <
# 8150; the watchdog's spiral branch kills at >= 8192 and every one of
# this task's kills carries that format with its log line).  A row is
# fired once per .done marker; clear the marker to re-arm a row killed
# young.
ROOT=agents/tasks/LJ-1-769-SPLIT
LOG=$ROOT/runs/dipfire.log
RUN=$ROOT/runs/run.sh
FIRE=8150

swap_mb() {
  sysctl -n vm.swapusage | awk '{gsub(/M/,"",$6); print int($6)}'
}

log() { echo "$(date '+%F %T') $*" >> "$LOG"; }

row() {
  # row <stem> <outsuffix> <label>   (stem relative to $ROOT/runs)
  stem="$1"; suf="$2"; name="$3"
  [ -f "$ROOT/runs/.done-$suf" ] && return 0
  while :; do
    s=$(swap_mb)
    if [ "$s" -lt "$FIRE" ]; then
      log "FIRE $name (swap ${s}MB)"
      cp "$ROOT/runs/$stem.agda.txt" "$ROOT/runs/$stem.agda"
      "$RUN" "$ROOT/runs/$stem.agda" "$suf" >> "$LOG" 2>&1
      rc=$(grep -h '^EXIT=' "$ROOT/runs/$suf.out" | tail -1)
      log "LANDED $name $rc"
      if [ "$rc" = "EXIT=0" ]; then
        log "PROMOTED $stem.agda (typechecked at the pane caliber)"
      else
        rm -f "$ROOT/runs/$stem.agda"
      fi
      touch "$ROOT/runs/.done-$suf"
      return 0
    fi
    sleep 20
  done
}

log "dipfire2 watcher started pid=\$$ FIRE<${FIRE}MB swap=$(swap_mb)MB"
row RawOnly769Split rawonly769split-3 RawOnly
row Raw769Split raw769split-3 Raw
row Probe769Split probe769split-4 OBLIGATION
row ConvOnly769Split convonly769split-5 ConvOnly
log "dipfire2 watcher: all rows done"

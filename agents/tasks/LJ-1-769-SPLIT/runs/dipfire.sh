#!/bin/sh
# dipfire: fire the decisive rows inside a swap dip.
#
# The box's agda watchdog (main checkout's uncommitted 2026-08-28 edit,
# running as pid 1964 since 2026-08-31 16:21) kills the biggest agda
# every 20 s tick whenever vm.swapusage used >= 8192 MB, whatever the
# process's own size (measured: a 640 MB canary killed at exec,
# runs/canary-frame-2.out; the accept arm's ConvOnly killed at 1.58 s,
# runs/accept-1.out).  Kills are environment, not prices.
#
# So: poll swap used; when it dips below FIRE (8100 MB, a 42 MB margin
# under the watchdog's 8192), fire the next row.  ONE Agda process at a
# time, caliber from the pane, never set here, 1800 s cap (run.sh).
# Rows are fired once per .done marker; the dispatch clears a marker to
# re-arm a row that died young to an environment kill.
ROOT=agents/tasks/LJ-1-769-SPLIT
LOG=$ROOT/runs/dipfire.log
RUN=$ROOT/runs/run.sh
FIRE=8150

swap_mb() {
  sysctl -n vm.swapusage | awk '{gsub(/M/,"",$6); print int($6)}'
}

log() { echo "$(date '+%F %T') $*" >> "$LOG"; }

row() {
  # row <file> <outstem> <label>
  f="$1"; out="$2"; name="$3"
  [ -f "$ROOT/runs/.done-$out" ] && return 0
  while :; do
    s=$(swap_mb)
    if [ "$s" -lt "$FIRE" ]; then
      log "FIRE $name (swap ${s}MB)"
      "$RUN" "$f" "$out" >> "$LOG" 2>&1
      log "LANDED $name $(grep -h '^EXIT=' "$ROOT/runs/$out.out" | tail -1)"
      touch "$ROOT/runs/.done-$out"
      return 0
    fi
    sleep 20
  done
}

log "dipfire watcher started pid=\$$ FIRE<${FIRE}MB swap=$(swap_mb)MB"
row "$ROOT/Probe769Split.agda" probe769split-2 OBLIGATION
row "$ROOT/runs/ConvOnly769Split.agda" convonly769split-4 ConvOnly
row "$ROOT/runs/RawOnly769Split.agda" rawonly769split-2 RawOnly
row "$ROOT/runs/Raw769Split.agda" raw769split-2 Raw
log "dipfire watcher: all rows done"

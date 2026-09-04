#!/bin/zsh
# agda-watchdog: kills runaway agda before it OOMs the machine.
# Born 2026-08-02 after four unguarded parallel writers crashed the 64GB box.
# Primary guard is GHCRTS=-M2g (WIDE) or -M4g (HEAVY) per agent agda run. The worst
# live mix is up to two WIDE writers AT ONCE, or one HEAVY, or one of EACH together
# (OWNER'S RULING 2026-08-23; dev/pod/heads.toml [tiers]; WIDE's second slot raced
# pod.py's own process census against its registry one for one hour before the
# proper fix, see pod.py:agda_slots() and agda_registry_slots()).
# This is the backstop, sized to HEAVY's cap, the larger of the two.
ROOT="$(cd "$(dirname "$0")" && pwd)"
while [ ! -e "$ROOT/.git" ]; do
	[ "$ROOT" = "/" ] && { echo "agda-watchdog: no .git above; refusing to guess" >&2; exit 1; }
	ROOT="$(dirname "$ROOT")"
done
mkdir -p "$ROOT/_build/tools"
LOG="$ROOT/_build/tools/agda-watchdog.log"
LIMIT_KB=$((9*1024*1024))    # 9 GB per-process backstop, dev/pod/heads.toml
                              # [tiers.shared].per_process_backstop_gb = 9 (2026-08-28,
                              # option a of item 43b: the -M8g superheavy tier needs a
                              # backstop ABOVE it; was 6g, which killed both real 8g
                              # runs). The two must agree, watchdog_backstop_note()
                              # in scripts/pod/pod.py names any drift.
FREE_MIN=8                   # system free-percentage floor
TOTAL_MAX_KB=$((12*1024*1024))  # 12 GB across ALL agda together: two heavy writers
                                # stack past the per-process backstop without either
                                # crossing it (measured 2026-08-28: 6.8g x1 killed,
                                # machine still seized later). Kill the biggest.
SWAP_MAX_MB=$((8*1024))         # 8 GB swap in use = the death spiral; macOS free%%
                                # counts purgeable pages and reads healthy while the
                                # machine thrashes (measured 2026-08-28: no floor
                                # kill before the seizure + hard reboot).
PRESS_MIN=3                  # kern.memorystatus_vm_pressure_level >= 3 (critical)
LOCK="$ROOT/_build/tools/agda-watchdog.pid"

# SINGLE INSTANCE: a second copy would double-kill and double-log. A stale pid
# whose process is gone is taken over. Without this, KeepAlive (launchd) and a
# loop restart would race.
if [ -f "$LOCK" ] && kill -0 "$(cat "$LOCK")" 2>/dev/null; then
	echo "agda-watchdog: already running pid=$(cat "$LOCK"), exiting" >&2
	exit 0
fi
echo $$ > "$LOCK"
trap 'rm -f "$LOCK"' EXIT INT TERM

echo "$(date '+%F %T') watchdog started pid=$$" >> "$LOG"
while true; do
  ps ax -o pid=,rss=,comm= | awk -v lim=$LIMIT_KB '$3 ~ /agda$/ && $2 > lim {print $1, $2}' | \
  while read -r pid rss; do
    kill -9 "$pid" 2>/dev/null && echo "$(date '+%F %T') KILLED agda pid=$pid rss=${rss}KB (6g backstop cap)" >> "$LOG"
  done
  total=$(ps ax -o rss=,comm= | awk '$3 ~ /agda$/ {s+=$1} END {print s+0}')
  if [ -n "$total" ] && [ "$total" -gt "$TOTAL_MAX_KB" ] 2>/dev/null; then
    big=$(ps ax -o pid=,rss=,comm= | awk '$3 ~ /agda$/ {print $2, $1}' | sort -rn | head -1 | awk '{print $2}')
    if [ -n "$big" ]; then
      kill -9 "$big" 2>/dev/null && echo "$(date '+%F %T') KILLED agda pid=$big rss=${big}KB (total agda rss ${total}KB > ${TOTAL_MAX_KB}KB)" >> "$LOG"
    fi
  fi
  spiral=0; why=""
  swap_mb=$(sysctl -n vm.swapusage 2>/dev/null | awk '{gsub(/M/,"",$6); print int($6)}')
  press=$(sysctl -n kern.memorystatus_vm_pressure_level 2>/dev/null)
  if [ -n "$swap_mb" ] && [ "$swap_mb" -ge "$SWAP_MAX_MB" ]; then
    spiral=1; why="swap ${swap_mb}MB >= ${SWAP_MAX_MB}MB"
  elif [ -n "$press" ] && [ "$press" -ge "$PRESS_MIN" ]; then
    spiral=1; why="mem pressure level ${press} >= ${PRESS_MIN}"
  fi
  if [ "$spiral" = 1 ]; then
    big=$(ps ax -o pid=,rss=,comm= | awk '$3 ~ /agda$/ {print $2, $1}' | sort -rn | head -1 | awk '{print $2}')
    if [ -n "$big" ]; then
      kill -9 "$big" 2>/dev/null && echo "$(date '+%F %T') KILLED agda pid=$big (${why})" >> "$LOG"
    fi
  fi
  free=$(memory_pressure -Q 2>/dev/null | awk -F': ' '/free percentage/{gsub(/%/,"",$2); print int($2)}')
  if [ -n "$free" ] && [ "$free" -lt "$FREE_MIN" ]; then
    big=$(ps ax -o pid=,rss=,comm= | awk '$3 ~ /agda$/ {print $2, $1}' | sort -rn | head -1 | awk '{print $2}')
    if [ -n "$big" ]; then
      kill -9 "$big" 2>/dev/null && echo "$(date '+%F %T') KILLED agda pid=$big (free ${free}% < ${FREE_MIN}%)" >> "$LOG"
    fi
  fi
  sleep 20
done

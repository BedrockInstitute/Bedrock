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
LIMIT_KB=$((6*1024*1024))    # 6 GB per-process backstop, dev/pod/heads.toml
                              # [tiers.shared].per_process_backstop_gb -- the two must
                              # agree, watchdog_backstop_note() in scripts/pod/pod.py names
                              # any drift
FREE_MIN=8                   # system free-percentage floor
echo "$(date '+%F %T') watchdog started pid=$$" >> "$LOG"
while true; do
  ps ax -o pid=,rss=,comm= | awk -v lim=$LIMIT_KB '$3 ~ /agda$/ && $2 > lim {print $1, $2}' | \
  while read -r pid rss; do
    kill -9 "$pid" 2>/dev/null && echo "$(date '+%F %T') KILLED agda pid=$pid rss=${rss}KB (6g backstop cap)" >> "$LOG"
  done
  free=$(memory_pressure -Q 2>/dev/null | awk -F': ' '/free percentage/{gsub(/%/,"",$2); print int($2)}')
  if [ -n "$free" ] && [ "$free" -lt "$FREE_MIN" ]; then
    big=$(ps ax -o pid=,rss=,comm= | awk '$3 ~ /agda$/ {print $2, $1}' | sort -rn | head -1 | awk '{print $2}')
    if [ -n "$big" ]; then
      kill -9 "$big" 2>/dev/null && echo "$(date '+%F %T') KILLED agda pid=$big (free ${free}% < ${FREE_MIN}%)" >> "$LOG"
    fi
  fi
  sleep 20
done

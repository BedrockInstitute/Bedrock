#!/bin/zsh
# agda-watchdog: kills runaway agda before it OOMs the machine.
# Born 2026-08-02 after four unguarded parallel writers crashed the 64GB box.
# Primary guard is GHCRTS=-M10g on every agent agda run; this is the backstop.
ROOT="$(cd "$(dirname "$0")" && pwd)"
while [ ! -e "$ROOT/.git" ]; do
	[ "$ROOT" = "/" ] && { echo "agda-watchdog: no .git above; refusing to guess" >&2; exit 1; }
	ROOT="$(dirname "$ROOT")"
done
mkdir -p "$ROOT/_build/tools"
LOG="$ROOT/_build/tools/agda-watchdog.log"
LIMIT_KB=$((14*1024*1024))   # 14 GB per-process backstop
FREE_MIN=8                   # system free-percentage floor
echo "$(date '+%F %T') watchdog started pid=$$" >> "$LOG"
while true; do
  ps ax -o pid=,rss=,comm= | awk -v lim=$LIMIT_KB '$3 ~ /agda$/ && $2 > lim {print $1, $2}' | \
  while read -r pid rss; do
    kill -9 "$pid" 2>/dev/null && echo "$(date '+%F %T') KILLED agda pid=$pid rss=${rss}KB (14g cap)" >> "$LOG"
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

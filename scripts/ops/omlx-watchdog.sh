#!/bin/zsh
# omlx-watchdog: restarts oMLX.app before its memory drift takes qwen's usable context
# below what one POD task needs, and brings the app back when `omlx-server` is gone.
# Born 2026-08-24 after seven of thirteen qwen dispatches died on a hard HTTP 400 inside
# one fourteen hour window. A 400 of that class carries `stopReason: error` and
# `usage.totalTokens: 0`: the WHOLE session's work is lost and `pi` does not retry. Those
# are the `fallback:Qwen3.8-27B-oQ4e-mtp` parks in `dev/pod/transitions/2026-08.jsonl`.
#
# THE MECHANISM. `omlx-server` does not return its MLX buffer pools to the OS, so its idle
# memory footprint rises with uptime. That footprint is subtracted from the 56 GB
# `iogpu.wired_limit_mb` cap, and what is left is qwen's usable context:
#
#     usable context ceiling = (56 GB - idle footprint) / 218,372 bytes per token
#
# where 218,372 = 65,536 KV snapshot resident + 65,536 full copy on first append + 87,300
# SDPA transient. Three points confirm the formula to within 0.2 GB: 17.45 GB gives
# 176,500 tokens, measured right after a restart; 21.64 GB gives 157,300, and the failures
# of 2026-08-23 fell at 158K to 171K; 34.04 GB gives 100,500, and all seven overnight
# failures fell at 98K to 103K.
#
# THE CURE IS ONE RESTART OF THE WHOLE APP. MEASURED 2026-08-24 11:20: the footprint fell
# from 41.41 GiB to 16.25 GiB, 25.16 GiB freed, in under 30 seconds end to end.
#
# WHAT THIS SCRIPT MUST NEVER DO. Each line is a measured failure, not a caution.
#   1. It never kills `omlx-server` alone. The process tree is oMLX (the menu bar app),
#      then `omlx-server`, then `python3`. MEASURED 2026-08-24 11:16: a `kill -9` of
#      `omlx-server` was NOT answered by the parent for five minutes, and `open -a oMLX`
#      did nothing because the app was already running. The service was down about seven
#      minutes. `killall oMLX` is the only kill in this file.
#      A DEAD SERVICE IS THE ONE CASE THAT STILL NEEDS `killall`, because the parent does
#      not respawn the child: the revive branch in `pass_once()` calls the same restart.
#   2. It never restarts A LIVE SERVICE while a `pi` agent is working. That gives the agent
#      a `Connection error` and the run is a total loss. `pi_busy()` is the gate and every
#      unreadable answer counts as BUSY. THE REVIVE BRANCH IS CARVED OUT of this rule and
#      it is the only thing that is: with no `omlx-server` there is nothing a `pi` agent
#      can be using, so the loss this rule prevents has already happened. See the branch
#      for the whole argument.
#   3. It never writes `~/.omlx/model_settings.json`. It reads three fields to confirm
#      they did not move. Re-enabling `dflash_ssd_cache` is pure write amplification
#      (measured `l2_hits=0 / l2_misses=513` over one night, root cause is the
#      `min_token_len=matched_len` gate in `dflash_mlx/cache/store.py`), and shrinking the
#      13 GiB L1 buys nothing (at the moment of failure L1 held 11.2 to 11.3 GB of its
#      13 GB budget, so one gigabyte less would have displaced nothing).
#   4. It never touches `iogpu.wired_limit_mb`. 56 GB is the owner's negotiated tradeoff
#      and it is fixed in `/etc/sysctl.conf`. This file calls no `sysctl`.
#
# START AND STOP ARE IN `dev/pod/README.md`, under "The oMLX watchdog". Nothing in
# `scripts/pod/pod.py` starts this or refuses a dispatch without it, and that section says
# why.
#
#   scripts/ops/omlx-watchdog.sh                     # the loop
#   scripts/ops/omlx-watchdog.sh --once --dry-run    # one pass. It decides and restarts nothing

emulate -L zsh
set -u

ROOT="$(cd "$(dirname "$0")" && pwd)"
while [ ! -e "$ROOT/.git" ]; do
	[ "$ROOT" = "/" ] && { echo "omlx-watchdog: no .git above; refusing to guess" >&2; exit 1; }
	ROOT="$(dirname "$ROOT")"
done
mkdir -p "$ROOT/_build/tools"
LOG="$ROOT/_build/tools/omlx-watchdog.log"
PIDFILE="$ROOT/_build/tools/omlx-watchdog.pid"
CLOCK="$ROOT/_build/tools/omlx-watchdog.clock"
PY="$ROOT/.venv/bin/python"

# ---------------------------------------------------------------- the numbers

# THE TRIGGER. Restart when the IDLE footprint is at or above this. The number is the
# handoff's own derivation and it is not re-derived here: at `contextWindow = 150,000` a
# task's context settles near 146,000 tokens, which is 146,000 * 218,372 = 31.88 GB, so
# the baseline must stay at or under 56 - 31.88 = 24.12 GB.
# IT IS COUPLED TO `contextWindow` AND THE SCRIPT SAYS SO AT START. At 135,000 the context
# settles near 131,000, the peak is 46.06 GB and a baseline up to 27.39 GB is tolerable, so
# 24 is conservative there and stays correct. Above 150,000 it is NOT correct any more,
# which is why `context_window_note()` reads the live value and warns.
TRIGGER_GB=24

# THE TIME BACKSTOP, in hours of ACTIVE qwen dispatch since the last restart. It fires when
# no clean idle reading was ever taken, so the footprint trigger never got its chance.
#
# WHY ACTIVE HOURS AND NOT WALL HOURS. Idle uptime does not move the footprint; generation
# does. Wall clock since the last restart was the simpler proxy and it is rejected here:
# it fires after a quiet night that cost nothing, and it under-counts a busy afternoon.
# `dev/pod/transitions/` already records every dispatch with its model, so the true figure
# is a read and not a guess. `qwen_active_hours()` sums the RUNNING to RETURNED spans whose
# model is qwen, unions them so a concurrent pair cannot count twice, and clips them to the
# window since the last restart.
#
# WHY 3.5 AND NOT THE HANDOFF'S 7 TO 8. The handoff states its rule in ACTIVE hours and
# derives its rate from WALL hours: 12.4 GB over 14 hours is 0.9 GB per wall hour, and
# 6.7 GB of margin over that rate is 7.4 hours. RE-MEASURED AT ITS OWN SITE, 2026-08-24,
# against the transition log for the same window (the 14 hours before the 11:20 restart):
# 12 qwen dispatches and 6.84 ACTIVE hours, so the drift was 1.81 GB per active hour. The
# margin from a fresh 17.45 GB baseline to the 24 GB trigger is 6.55 GB, which is 3.6
# active hours. 3.5 is that figure, rounded DOWN, because rounding up puts the baseline
# past 24.12 GB, which is the wall itself.
# THE FIGURE IS AN UPPER BOUND ON THE RATE and therefore a lower bound on the runway: the
# transition log sees only the POD's own dispatches, so any qwen use outside the POD is
# counted as drift with no active hour beside it. Erring short is the safe direction, and a
# restart costs 10 to 30 seconds inside a window that is already idle.
BACKSTOP_ACTIVE_H=3.5

TICK_S=60              # one decision pass per minute. The idle gate costs 7 ms and the
                       # footprint read 167 ms, both MEASURED 2026-08-24, so a short idle
                       # window between two dispatches is still caught.
SILENCE_S=90           # the server log must be untouched this long before a reading counts
RECHECK_S=30           # and the idle gate is asked a second time after this
POLL_TRIES=40          # recovery poll: 40 tries at 5 s is 200 s. MEASURED: 5 s.
POLL_S=5
WARMUP_TIMEOUT=900     # the pinned model auto-preloads. MEASURED warm answer: 1.4 s.
FRESH_MAX_GB=20        # a restart that worked lands at 16 to 18 GiB. Over this is reported.
COOLDOWN_S=600         # NO SECOND ATTEMPT INSIDE THIS WINDOW. A restart that cures the
                       # footprint disarms the trigger by itself, so this only ever binds
                       # the case where the restart did NOT cure it. Without it that case
                       # is a thrash: one kill of a live server every 90 seconds forever.
                       # Ten minutes makes it one report per ten minutes instead.

RES="/Applications/oMLX.app/Contents/Resources"
APP="oMLX"                                       # the killall target, and the ONLY one
SERVER="omlx-server"                             # read for its pid; never killed
SERVER_LOG="$HOME/Library/Application Support/oMLX/logs/server.log"
MODEL_SETTINGS="$HOME/.omlx/model_settings.json"
PI_MODELS="$HOME/.pi/agent/models.json"
ENDPOINT="http://127.0.0.1:8010"
MODEL="Qwen3.8-27B-oQ4e-mtp"
TRANSITIONS="$ROOT/dev/pod/transitions"

DRY_RUN=0
ONCE=0
for arg in "$@"; do
	case "$arg" in
		--dry-run) DRY_RUN=1 ;;
		--once)    ONCE=1 ;;
		*) echo "omlx-watchdog: unknown option $arg (--dry-run, --once)" >&2; exit 2 ;;
	esac
done

log() { echo "$(date '+%F %T') $*" >> "$LOG" }

# ONE LINE PER CHANGE OF REASON, NEVER ONE A TICK. `watchdog_tick()` in
# scripts/pod/pod.py learned this in numbers: at a 30 s tick a per-tick line is 2,880 lines
# a day. A skip that repeats writes its line once and stays silent until the reason moves.
LAST_SKIP=""
skip() {
	[ "$1" = "$LAST_SKIP" ] || { LAST_SKIP="$1"; log "skip: $1" }
}

#: The epoch of the newest restart ATTEMPT, cured or not. `COOLDOWN_S` reads it.
LAST_ATTEMPT=0

# ---------------------------------------------------------------- the readings

server_pid() { pgrep -x "$SERVER" 2>/dev/null | head -1 }

# The idle footprint of `omlx-server`, in GiB, or nothing.
# IT USES THE APP'S OWN INTERPRETER AND NOT `.venv/bin/python`, which is the one exception
# to the repository's rule. `omlx.utils.proc_memory` ships inside `oMLX.app` and no other
# interpreter can import it. The call reads one process's phys_footprint and writes nothing.
# MEASURE ONLY WHEN NOTHING GENERATES. During generation the footprint spikes past 50 GB,
# which is not the baseline. Every caller here is behind `pi_busy()` and `log_quiet()`.
footprint_gb() {
	local pid; pid="$(server_pid)"
	[ -n "$pid" ] || return 1
	PYTHONPATH="$RES/Python/framework-mlx-base/lib/python3.11/site-packages:$RES" \
		"$RES/Python/cpython-3.11/bin/python3" -c "
import sys; sys.path.insert(0,'$RES')
from omlx.utils.proc_memory import get_phys_footprint
print(round(get_phys_footprint(int(sys.argv[1]))/1024**3, 2))" "$pid" 2>/dev/null
}

# 0 when no `pi` agent is working, 1 when one is or when the answer cannot be read.
# EVERY EXCEPTION COUNTS AS BUSY. A restart under a live agent is a total loss of that run,
# so an unreadable state must never open the gate.
# `pgrep -f "pi --mode json"` DOES NOT WORK: `pi` runs inside a herdr pane and is invisible
# that way. herdr's own `agent_status` is the only source.
pi_busy() {
	herdr pane list 2>/dev/null | "$PY" -c "
import sys, json
try:
    panes = json.load(sys.stdin)['result']['panes']
except Exception:
    print(1); raise SystemExit
print(1 if any(p.get('agent')=='pi' and p.get('agent_status')=='working' for p in panes) else 0)"
}

# True when the server log has been untouched for SILENCE_S. A missing or unreadable log
# reads as NOT quiet, the same safe direction as `pi_busy()`.
log_quiet() {
	local m now
	m="$(stat -f %m "$SERVER_LOG" 2>/dev/null)" || return 1
	[ -n "$m" ] || return 1
	now="$(date +%s)"
	[ "$((now - m))" -ge "$SILENCE_S" ]
}

# Hours of ACTIVE qwen dispatch since the epoch given, from the transition log.
qwen_active_hours() {
	"$PY" - "$1" "$TRANSITIONS" "$MODEL" <<'PY' 2>/dev/null
import glob, json, os, sys, time
from datetime import datetime, timezone

since, tdir, model = float(sys.argv[1]), sys.argv[2], sys.argv[3]
now = time.time()


def epoch(ts):
    """The record's own stamp, or None. ONE BAD STAMP SKIPS ONE RECORD and never the
    file: a raise here would empty the whole figure and disarm the backstop in silence."""
    try:
        return datetime.strptime(ts, "%Y-%m-%dT%H:%M:%SZ").replace(
            tzinfo=timezone.utc).timestamp()
    except (TypeError, ValueError):
        return None


# The log is one file per month, so the newest two cover any window this asks about.
open_at, spans = {}, []
for path in sorted(glob.glob(os.path.join(tdir, "*.jsonl")))[-2:]:
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            try:
                r = json.loads(line)
            except ValueError:
                continue
            if r.get("model") != model:
                continue
            task, at = r.get("task"), epoch(r.get("ts"))
            if at is None:
                continue
            if r.get("to") == "RUNNING":
                open_at[task] = at
            elif r.get("from") == "RUNNING" and task in open_at:
                spans.append((open_at.pop(task), at))
for start in open_at.values():
    spans.append((start, now))            # still RUNNING, so still burning

total, end_prev = 0.0, since
for a, b in sorted(spans):
    a, b = max(a, since), min(b, now)
    if b <= a:
        continue
    a = max(a, end_prev)                  # union, so a concurrent pair counts once
    if b > a:
        total += b - a
        end_prev = b
print(round(total / 3600.0, 2))
PY
}

# The epoch the backstop clock runs from: the last completed restart, or the first start of
# this watchdog. Losing the file only DELAYS a restart, and the footprint trigger is
# unaffected, so a `make clean` cannot make this unsafe.
clock_origin() {
	local v
	v="$(cat "$CLOCK" 2>/dev/null)"
	if [ -z "$v" ]; then
		v="$(date +%s)"
		echo "$v" > "$CLOCK"        # never restarted yet, so the clock starts now
	fi
	echo "$v"
}

# `contextWindow` for qwen, read from pi's own file. The TRIGGER_GB derivation assumes
# 150,000; a larger value makes 24 GB too loose and the operator must know at once.
context_window_note() {
	"$PY" -c "
import json, sys
try:
    d = json.load(open('$PI_MODELS'))['providers']['omlx']['models']
except Exception as e:
    print('contextWindow UNREADABLE (%s)' % type(e).__name__); raise SystemExit
for m in d:
    if m.get('id') == '$MODEL':
        cw = m.get('contextWindow')
        if cw is None:
            print('contextWindow ABSENT')
        elif cw > 150000:
            print('contextWindow=%s ABOVE 150000: the %s GB trigger is DERIVED for '
                  '150000 and is too loose here' % (cw, $TRIGGER_GB))
        else:
            print('contextWindow=%s' % cw)
        raise SystemExit
print('contextWindow: no row for $MODEL')" 2>/dev/null
}

# ---------------------------------------------------------------- the restart

# THE RESTART, and it is the only place this file kills anything. `killall oMLX` names the
# menu bar app. It cannot match `omlx-server`, whose name differs, so trap 1 above is
# closed by construction and not by care.
restart_omlx() {
	local why="$1" i code
	LAST_ATTEMPT="$(date +%s)"
	log "RESTART begin: $why"
	if [ "$DRY_RUN" -eq 1 ]; then
		log "RESTART dry-run: would run 'killall $APP; sleep 3; open -a $APP', then poll $ENDPOINT/v1/models and warm the model. Nothing was killed."
		return 0
	fi
	killall "$APP" 2>/dev/null || log "RESTART note: killall $APP found nothing to kill"
	sleep 3
	open -a "$APP" || { log "RESTART FAILED: open -a $APP returned non-zero"; return 1 }
	for i in $(seq 1 $POLL_TRIES); do
		sleep $POLL_S
		code="$(curl -s -o /dev/null -w '%{http_code}' -m 5 "$ENDPOINT/v1/models" 2>/dev/null)"
		if [ "$code" = "200" ]; then
			log "RESTART service back after $((i * POLL_S))s"
			break
		fi
	done
	if [ "$code" != "200" ]; then
		log "RESTART FAILED: no 200 from $ENDPOINT/v1/models after $((POLL_TRIES * POLL_S))s"
		return 1
	fi
	# The pinned model auto-preloads. This confirms it actually answers.
	local warm
	warm="$(curl -s -m $WARMUP_TIMEOUT "$ENDPOINT/v1/chat/completions" \
		-H 'Content-Type: application/json' \
		-d "{\"model\":\"$MODEL\",\"messages\":[{\"role\":\"user\",\"content\":\"hi\"}],\"max_tokens\":4}" \
		-o /dev/null -w 'HTTP %{http_code} %{time_total}s' 2>/dev/null)"
	log "RESTART warmup $warm"
	case "$warm" in
		"HTTP 200 "*) ;;
		*) log "RESTART WARMUP FAILED: $warm" ;;
	esac
	date +%s > "$CLOCK"                 # the backstop clock restarts here, and only here
	log "RESTART complete"
	return 0
}

# WHAT TO VERIFY AFTERWARD. Three reads, all of them read only. A failure is NEVER silent:
# it is logged and the loop goes on, because this script owns none of the three files and
# a refusal here would leave the cure outside its reach.
verify_after() {
	local fp stats tag=""
	# A dry run restarted nothing, so all three reads describe the OLD process. The lines
	# are still written, because they are how the reader confirms the three reads work, but
	# they carry the tag so nobody takes them for a verdict on a restart.
	[ "$DRY_RUN" -eq 1 ] && tag="(dry-run, nothing was restarted) "
	fp="$(footprint_gb)"
	if [ -z "$fp" ]; then
		log "${tag}VERIFY footprint UNREADABLE (no $SERVER process yet)"
	elif (( fp > FRESH_MAX_GB )); then
		log "${tag}VERIFY footprint=${fp} GiB UNEXPECTED: a restart lands at 16 to 18 GiB"
	else
		log "${tag}VERIFY footprint=${fp} GiB ok"
	fi
	stats="$(grep 'prefix-cache-stats' "$SERVER_LOG" 2>/dev/null | tail -1)"
	if [ -z "$stats" ]; then
		log "${tag}VERIFY prefix-cache-stats ABSENT from the server log"
	else
		case "$stats" in
			*"entries=0/"*) log "${tag}VERIFY prefix-cache reset: ${stats##*prefix-cache-stats}" ;;
			*) log "${tag}VERIFY prefix-cache NOT reset: ${stats##*prefix-cache-stats}" ;;
		esac
	fi
	log "${tag}VERIFY $("$PY" -c "
import json
try:
    d = json.load(open('$MODEL_SETTINGS'))['models']['$MODEL']
except Exception as e:
    print('model_settings UNREADABLE (%s)' % type(e).__name__); raise SystemExit
want = {'dflash_enabled': True, 'dflash_ssd_cache': False,
        'dflash_in_memory_cache_max_bytes': 13 * 1024 ** 3}
bad = [k for k, v in want.items() if d.get(k) != v]
print('config unchanged (dflash_enabled=True, dflash_ssd_cache=False, L1=13 GiB)'
      if not bad else 'config MOVED: ' + ', '.join(
          '%s=%s' % (k, d.get(k)) for k in bad))" 2>/dev/null)"
}

# ---------------------------------------------------------------- one decision pass

# The order is the order of cost and of safety. The idle gate is first because a busy
# machine ends the pass with no readings at all, and because the footprint is only a
# baseline while nothing generates.
pass_once() {
	local busy fp origin hours since_try why=""

	# REVIVE, AND IT IS THE ONE PATH THAT DOES NOT ASK `pi_busy()`.
	# MEASURED 2026-08-26: `omlx-server` went down at 08:41:49 and stayed down 63 minutes.
	# `LJ-1.644` was mid-run and `LJ-1.642` was dispatched into the hole; both spent their
	# whole run on `Connection error` and both parked `fallback:Qwen3.8-27B-oQ4e-mtp`.
	# This function watched the outage and wrote `no omlx-server process, so there is
	# nothing to restart`, which is true of a RESTART and wrong about the machine: a dead
	# service is the plainest thing a watchdog exists for.
	# WHY TRAP 2 DOES NOT BIND HERE. With no `omlx-server` there is nothing a `pi` agent
	# can be using. One on qwen is already taking `Connection error`, so the loss the trap
	# prevents has already happened; one on a cloud model never sees `killall oMLX`, which
	# names the menu bar app alone. Asking `pi_busy()` here would hand the outage the
	# length of the longest CLOUD run on the machine, which is the failure being fixed.
	if [ -z "$(server_pid)" ]; then
		since_try=$(( $(date +%s) - LAST_ATTEMPT ))
		if [ "$LAST_ATTEMPT" -ne 0 ] && [ "$since_try" -lt "$COOLDOWN_S" ]; then
			skip "no $SERVER process, but the last attempt was ${since_try}s ago and the cooldown is ${COOLDOWN_S}s"
			return 0
		fi
		# THE SECOND ASK, for the same reason the trigger path has one. A service still
		# coming up has no pid yet either, and killing the app mid-launch is the only way
		# this branch can do harm. `open -a` reaches a 200 in about 5 s, MEASURED
		# 2026-08-26 across four restarts, so RECHECK_S is a wide margin.
		log "REVIVE candidate: no $SERVER process; re-checking in ${RECHECK_S}s"
		sleep $RECHECK_S
		if [ -n "$(server_pid)" ]; then
			log "REVIVE stood down: $SERVER appeared inside the ${RECHECK_S}s recheck"
			LAST_SKIP=""
			return 0
		fi
		LAST_SKIP=""
		restart_omlx "no $SERVER process; reviving a dead service" && verify_after
		return 0
	fi

	busy="$(pi_busy)"
	if [ "$busy" != "0" ]; then
		skip "a pi agent is working, or herdr could not be read"
		return 0
	fi
	if ! log_quiet; then
		skip "the server log moved inside the last ${SILENCE_S}s"
		return 0
	fi
	fp="$(footprint_gb)"
	if [ -z "$fp" ]; then
		# The missing-pid case left this branch when revive took it. What is left is a pid
		# that exists and a reading that did not come back, which is the app's own
		# interpreter failing. NO READING IS NEVER A TRIGGER: an unreadable footprint must
		# not be read as a small one, or as a large one.
		skip "the $SERVER footprint could not be read"
		return 0
	fi
	origin="$(clock_origin)"
	hours="$(qwen_active_hours "$origin")"
	[ -n "$hours" ] || hours=0

	if (( fp >= TRIGGER_GB )); then
		why="footprint ${fp} GiB at or above the ${TRIGGER_GB} GB trigger"
	elif (( hours >= BACKSTOP_ACTIVE_H )); then
		why="${hours}h of active qwen dispatch since the last restart, at or above the ${BACKSTOP_ACTIVE_H}h backstop"
	fi
	if [ -z "$why" ]; then
		skip "idle at ${fp} GiB after ${hours}h active qwen; under both triggers"
		return 0
	fi
	since_try=$(( $(date +%s) - LAST_ATTEMPT ))
	if [ "$LAST_ATTEMPT" -ne 0 ] && [ "$since_try" -lt "$COOLDOWN_S" ]; then
		skip "$why, but the last attempt was ${since_try}s ago and the cooldown is ${COOLDOWN_S}s"
		return 0
	fi

	# THE SECOND ASK. The first one was taken before the footprint read, which costs about
	# 170 ms, and a dispatch can start inside any gap. This one is taken RECHECK_S later and
	# immediately before the kill, so the window between the gate and the kill is as short
	# as the procedure allows.
	log "TRIGGER $why; re-checking idle in ${RECHECK_S}s"
	sleep $RECHECK_S
	busy="$(pi_busy)"
	if [ "$busy" != "0" ]; then
		log "TRIGGER stood down: a pi agent started working inside the ${RECHECK_S}s recheck"
		LAST_SKIP=""
		return 0
	fi
	LAST_SKIP=""
	restart_omlx "$why" "$fp" && verify_after
	return 0
}

# ---------------------------------------------------------------- the loop

if [ ! -d "$RES" ]; then
	echo "omlx-watchdog: $RES is not a directory; oMLX.app is not installed here" >&2
	exit 1
fi
if [ ! -x "$PY" ]; then
	echo "omlx-watchdog: $PY is missing; the repository venv is the required interpreter" >&2
	exit 1
fi
if [ -f "$PIDFILE" ]; then
	other="$(cat "$PIDFILE" 2>/dev/null)"
	if [ -n "$other" ] && kill -0 "$other" 2>/dev/null; then
		echo "omlx-watchdog: pid $other already holds $PIDFILE; refusing a second copy" >&2
		exit 1
	fi
fi
echo $$ > "$PIDFILE"

log "watchdog started pid=$$ dry_run=$DRY_RUN once=$ONCE trigger=${TRIGGER_GB}GB backstop=${BACKSTOP_ACTIVE_H}h-active"
log "watchdog $(context_window_note)"

if [ "$ONCE" -eq 1 ]; then
	pass_once
	log "watchdog finished one pass"
	exit 0
fi

while true; do
	pass_once
	sleep $TICK_S
done

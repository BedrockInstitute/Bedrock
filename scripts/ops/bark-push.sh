#!/usr/bin/env bash
# The POD stop push, section 8.4 of dev/memos/LJ-4-pod-program-design.md.
#
# WHY THIS FILE EXISTS. The loop has exactly TWO stops: rule (d), when the parked count
# reaches 3, and apply(), when a `stop_loop` row matched. Both push immediately and
# neither waits for the digest. `notify_owner()` at scripts/pod/pod.py:1462 is the only
# caller.
#
# THE CHANNEL IS REUSED AND THE SCRIPT IS NOT. The Stop hook that owns this channel
# derives its body from a Claude Code transcript alone, and no environment variable sets
# that body. This copy reads `BARK_BODY` instead, so a program can say what happened.
# The transcript chain below still fills an EMPTY body, so the hook behaviour is
# unchanged and one script serves both callers.
#
# BOTH SECRETS COME FROM THE ENVIRONMENT AND THIS FILE HOLDS NEITHER. `BARK_AES_KEY` and
# `BARK_KEY_URL` are deployment secrets. The script REFUSES to run when either is unset,
# because a default in a tracked file is a committed secret.
#
# THE ENCRYPTION IS AES-256-GCM. GCM is the one authenticated mode of the three the Bark
# app offers, so it resists tampering and needs no padding. Its one fatal case is a
# repeated nonce, so this script generates a fresh random 12-byte IV per push and sends
# it as the `iv` parameter. A short IV read means the random source failed: the script
# then pushes NOTHING rather than reusing a fixed IV.
#
# IT WRITES NO LOG. The plaintext, the IV and the ciphertext exist in memory only.
#
# EVERY FAILURE IS LOUD, AND THAT IS THE ONE BEHAVIOUR THIS COPY CHANGES. The Stop hook
# ran beside a human who could see that no push arrived. This copy is the ONLY channel
# that tells the owner an unattended loop stopped, and the hook exited 0 on a failed
# encryption, on a failed random read and on a failed HTTP request alike. A stop that
# nobody hears is the exact failure this file exists to prevent, so each of those now
# writes one line to stderr and exits non-zero. IT STILL NEVER FALLS BACK: not to a
# plaintext push, and not to a fixed IV.
#
# EXIT STATUS, and each code means one thing:
#   0   the push was accepted by the Bark endpoint.
#   1   a real failure. The random source, the encryption or the request failed, and
#       the message names which. NOTHING was pushed.
#   2   an environment error: a required variable is unset, the key is the wrong length,
#       the mode is unknown, or a required tool is missing.
#
# ENVIRONMENT:
#   BARK_KEY_URL   required. The Bark device endpoint.
#   BARK_AES_KEY   required. 32 characters, which is AES-256. It must equal the key in
#                  the phone app.
#   BARK_BODY      the push body. The transcript chain fills an empty one.
#   BARK_TITLE     the push title.
#   BARK_GROUP     the push group.
#   BARK_MODE      gcm (default) or cbc. CBC needs a 16-byte IV and adds pkcs7 padding.
#
# Example:
#   BARK_TITLE="POD 已停止" BARK_GROUP="Bedrock POD" \
#   BARK_BODY="3 个任务停放，循环停止。最新：LJ-1.392 preflight:P8" \
#     scripts/ops/bark-push.sh </dev/null

# THIS SCRIPT IS BASH AND A CALLER MAY START IT WITH `sh`. `notify_owner()` at
# scripts/pod/pod.py:1476 runs `sh <path>`, and where /bin/sh is dash every `[[` below is
# a syntax error and `set -o pipefail` is an illegal option. Re-exec under bash rather
# than die on line one with a message about a bracket.
if [ -z "${BASH_VERSION:-}" ]; then
  if ! command -v bash >/dev/null 2>&1; then
    echo "bark-push: bash is required and is not on PATH; refusing to push" >&2
    exit 2
  fi
  exec bash "$0" "$@"
fi

set -uo pipefail

BARK_KEY_URL="${BARK_KEY_URL:-}"
BARK_AES_KEY="${BARK_AES_KEY:-}"
BARK_PLACEHOLDER="${BARK_PLACEHOLDER:-推送加密}"
BARK_TITLE="${BARK_TITLE:-POD 已停止}"
BARK_GROUP="${BARK_GROUP:-Bedrock POD}"
BARK_MODE="${BARK_MODE:-gcm}"

# The refusal names the variable and never its value.
if [[ -z "$BARK_KEY_URL" ]]; then
  echo "bark-push: BARK_KEY_URL is not set; refusing to push" >&2
  exit 2
fi
if [[ -z "$BARK_AES_KEY" ]]; then
  echo "bark-push: BARK_AES_KEY is not set; refusing to push" >&2
  exit 2
fi

# AES-256 TAKES A 32-BYTE KEY AND NOTHING ELSE. Both back ends throw on any other
# length, and the throw used to reach the silent branch below: the script exited 0 and
# the owner learned nothing. The length is checked here, where it can be named.
if [[ ${#BARK_AES_KEY} -ne 32 ]]; then
  echo "bark-push: BARK_AES_KEY is ${#BARK_AES_KEY} characters and AES-256 needs 32;" \
       "refusing to push" >&2
  exit 2
fi

if [[ "$BARK_MODE" != "gcm" && "$BARK_MODE" != "cbc" ]]; then
  echo "bark-push: BARK_MODE is '$BARK_MODE'; it must be gcm or cbc" >&2
  exit 2
fi

# THE TWO TOOLS ARE NAMED WHEN THEY ARE MISSING. `jq` builds the plaintext JSON and the
# URL encoding, so without it the plaintext is EMPTY and the script would encrypt and
# push nothing at all, with exit 0.
for tool in jq curl; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "bark-push: $tool is not on PATH; refusing to push" >&2
    exit 2
  fi
done

MAX_LEN=140

# ---------- 1. the body ----------

# STDIN IS READ ONLY WHEN IT IS NOT A TERMINAL. The Stop hook pipes its JSON in, and the
# POD passes /dev/null. Run by hand with neither, `cat` waits for end of file for ever,
# and a stop push that hangs is a stop push nobody gets.
if [[ -t 0 ]]; then
  payload=""
else
  payload="$(cat)"
fi
transcript="$(printf '%s' "$payload" | jq -r '.transcript_path // empty' 2>/dev/null)"

# Stop hook 触发时，本轮最终回复往往刚写入 transcript 仅 16~100ms，存在读到上一轮内容的
# 竞态。先等文件大小连续两次不变（约 300ms），确认写入已落定再读。
settle_transcript() {
  local prev="" cur stable=0 i
  for ((i = 0; i < 20; i++)); do
    cur="$(stat -f%z "$transcript" 2>/dev/null || wc -c <"$transcript" 2>/dev/null || echo 0)"
    if [[ "$cur" == "$prev" ]]; then
      stable=$((stable + 1))
      ((stable >= 2)) && return 0
    else
      stable=0
    fi
    prev="$cur"
    sleep 0.1
  done
}

session_title=""; last_msg=""; last_prompt=""
if [[ -n "$transcript" && -f "$transcript" ]]; then
  settle_transcript

  # 会话标题 / 最后一次用户提问：整文件 grep 出对应行再解析，避免解析全量 JSON
  session_title="$(grep -F '"type":"ai-title"' "$transcript" 2>/dev/null | tail -1 \
    | jq -r '.aiTitle // empty' 2>/dev/null)"
  last_prompt="$(grep -F '"type":"last-prompt"' "$transcript" 2>/dev/null | tail -1 \
    | jq -r '(.lastPrompt // "") | gsub("\\s+"; " ")' 2>/dev/null)"

  # 本轮最终回复：只取「最后一条用户提问之后」的助手文本，避免取到上一轮内容。
  # 排除 toolUseResult（工具结果也是 user 类型）与 isMeta（系统注入），只认真实提问。
  # 仅解析末尾 400 行，长会话下也是常数开销；窗口内找不到提问则退化为取窗口内最后一条。
  last_msg="$(tail -n 400 "$transcript" 2>/dev/null | jq -s -r '
      . as $all
      | ([range(0; ($all | length)) | select(
            $all[.].type == "user"
            and ($all[.].isMeta != true)
            and ($all[.].isSidechain != true)
            and ($all[.].toolUseResult == null))] | last // -1) as $u
      | [ range(($u + 1); ($all | length)) | $all[.]
          | select(.type == "assistant" and (.isSidechain != true))
          | (.message.content // [])[] | select(.type == "text") | .text
          | gsub("\\s+"; " ") | sub("^ +"; "") | select(length > 0) ]
      | last // ""
    ' 2>/dev/null)"
fi

# THE ONE AMENDMENT OF SECTION 8.4, AND IT REPLACES RATHER THAN INSERTS. The line below
# read `body=""` in the Stop hook. An inserted line ahead of it would be overwritten at
# once and BARK_BODY discarded.
body="${BARK_BODY:-}"
# THE TITLE FILLS AN EMPTY BODY AND NEVER REPLACES ONE. This read
# `[[ -n "$session_title" ]] && body="$session_title"`, which DISCARDED a BARK_BODY the
# caller had set whenever a transcript also carried a title. For the Stop hook the
# behaviour is identical, because that caller sets no BARK_BODY and the body is empty
# here. For the POD it is the difference between the stop reason and a session title.
[[ -z "$body" ]] && body="$session_title"
if [[ -n "$last_msg" ]]; then
  [[ -n "$body" ]] && body="$body · $last_msg" || body="$last_msg"
fi
[[ -z "$body" ]] && body="$last_prompt"
[[ -z "$body" ]] && body="任务已完成"

# 按字符（非字节）截断，避免截断多字节汉字
body="$(jq -rn --arg s "$body" --argjson n "$MAX_LEN" '
  $s | if (length > $n) then .[0:($n - 1)] + "…" else . end')"

# 明文即 Bark 参数的 JSON 字符串
plaintext="$(jq -cn --arg t "$BARK_TITLE" --arg b "$body" --arg g "$BARK_GROUP" \
  '{title: $t, body: $b, group: $g}')"

# ---------- 2. encrypt ----------

# 每次推送生成新的随机 IV：GCM 下 nonce 复用会同时摧毁机密性与认证性
iv_len=12
[[ "$BARK_MODE" == "cbc" ]] && iv_len=16
iv="$(LC_ALL=C tr -dc 'A-Za-z0-9' </dev/urandom | head -c "$iv_len")"
# 长度不足说明取随机数失败。此时宁可不推送，也不退回固定 IV（GCM 下即 nonce 复用）。
# 退出码为 1 而不是 0：不推送是对的，静默是错的。
if [[ ${#iv} -ne $iv_len ]]; then
  echo "bark-push: the random source gave ${#iv} of $iv_len bytes; nothing was pushed" >&2
  exit 1
fi

# node 优先（内置 crypto，零依赖），找不到再退回 python3 + cryptography
node_bin="$(command -v node 2>/dev/null)"
if [[ -z "$node_bin" ]]; then
  for p in /usr/local/bin/node /opt/homebrew/bin/node "$HOME"/.nvm/versions/node/*/bin/node; do
    [[ -x "$p" ]] && { node_bin="$p"; break; }
  done
fi

ciphertext=""
if [[ -n "$node_bin" ]]; then
  ciphertext="$(BK_KEY="$BARK_AES_KEY" BK_IV="$iv" BK_MODE="$BARK_MODE" BK_PT="$plaintext" \
    "$node_bin" -e '
      const c = require("crypto");
      const key = Buffer.from(process.env.BK_KEY, "utf8");
      const iv  = Buffer.from(process.env.BK_IV,  "utf8");
      const pt  = Buffer.from(process.env.BK_PT,  "utf8");
      if (process.env.BK_MODE === "cbc") {
        const e = c.createCipheriv("aes-256-cbc", key, iv);   // pkcs7 为 node 默认
        process.stdout.write(Buffer.concat([e.update(pt), e.final()]).toString("base64"));
      } else {
        const e = c.createCipheriv("aes-256-gcm", key, iv);
        const ct = Buffer.concat([e.update(pt), e.final()]);
        // CryptoSwift GCM .combined = 密文 ‖ 认证标签
        process.stdout.write(Buffer.concat([ct, e.getAuthTag()]).toString("base64"));
      }
    ' 2>/dev/null)"
fi

if [[ -z "$ciphertext" ]]; then
  ciphertext="$(BK_KEY="$BARK_AES_KEY" BK_IV="$iv" BK_MODE="$BARK_MODE" BK_PT="$plaintext" \
    python3 -c '
import base64, os, sys
key = os.environ["BK_KEY"].encode(); iv = os.environ["BK_IV"].encode()
pt  = os.environ["BK_PT"].encode()
if os.environ["BK_MODE"] == "cbc":
    from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
    from cryptography.hazmat.primitives import padding
    p = padding.PKCS7(128).padder(); pt = p.update(pt) + p.finalize()
    e = Cipher(algorithms.AES(key), modes.CBC(iv)).encryptor()
    out = e.update(pt) + e.finalize()
else:
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    out = AESGCM(key).encrypt(iv, pt, None)   # 返回值即 密文‖标签
sys.stdout.write(base64.b64encode(out).decode())
' 2>/dev/null)"
fi

# 加密失败则放弃推送，绝不退回明文。失败要说出来：这条通道存在的唯一理由，
# 就是在无人值守时把「循环已停止」送到所有者手上。
if [[ -z "$ciphertext" ]]; then
  echo "bark-push: both back ends failed to encrypt in $BARK_MODE mode;" \
       "nothing was pushed" >&2
  exit 1
fi

# ---------- 3. push ----------

# base64 含 + / =，必须 URL 编码，否则 + 会被解成空格
enc() { jq -rn --arg s "$1" '$s | @uri'; }
url="${BARK_KEY_URL%/}/$(enc "$BARK_PLACEHOLDER")?ciphertext=$(enc "$ciphertext")&iv=$(enc "$iv")"

# THE STATUS IS READ AND THE URL IS NEVER PRINTED, because the URL carries the device
# key. A refused or unreachable endpoint used to exit 0 exactly like a delivered push.
http="$(curl -s -o /dev/null -m 8 -w '%{http_code}' "$url")"
rc=$?
if [[ $rc -ne 0 ]]; then
  echo "bark-push: curl exited $rc; the push did not complete" >&2
  exit 1
fi
if [[ ! "$http" =~ ^2 ]]; then
  echo "bark-push: the endpoint answered HTTP $http; the push was not accepted" >&2
  exit 1
fi

exit 0

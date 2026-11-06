#!/usr/bin/env bash
#
# Check Claude Max subscription usage via OAuth endpoint.
#
# Usage:
#   bash scripts/exp/usage.sh              # JSON output
#   bash scripts/exp/usage.sh --check 80   # exit 1 if any window > 80%
#
# Profile selection (first match wins):
#   CLAUDE_CREDENTIALS   — explicit path to credentials.json
#   CLAUDE_CONFIG_DIR    — config dir (reads $CLAUDE_CONFIG_DIR/.credentials.json)
#   CLAUDE_ALIAS         — alias name (reads $HOME/.<alias>/.credentials.json;
#                          "claude" maps to the default $HOME/.claude)
#   default              — $HOME/.claude/.credentials.json
#
# On macOS the credentials live in the login Keychain rather than in a file, so
# when the resolved file does not exist the profile's Keychain item is read
# instead (set CLAUDE_CREDENTIALS to force a file and skip the Keychain).
#
# Exit codes:
#   0  ok (or under threshold in --check mode)
#   1  over threshold (--check mode)
#   2  fetch failed (auth error, network, etc.)

set -euo pipefail

if [[ -n "${CLAUDE_CREDENTIALS:-}" ]]; then
  CREDENTIALS="$CLAUDE_CREDENTIALS"
elif [[ -n "${CLAUDE_CONFIG_DIR:-}" ]]; then
  CREDENTIALS="$CLAUDE_CONFIG_DIR/.credentials.json"
elif [[ -n "${CLAUDE_ALIAS:-}" && "$CLAUDE_ALIAS" != "claude" ]]; then
  CREDENTIALS="$HOME/.${CLAUDE_ALIAS}/.credentials.json"
else
  CREDENTIALS="$HOME/.claude/.credentials.json"
fi

# Base name of Claude Code's Keychain item.
KEYCHAIN_SERVICE="${CLAUDE_KEYCHAIN_SERVICE:-Claude Code-credentials}"

die() { echo "error: $*" >&2; exit 2; }

# Keychain items to try, in order. Claude Code names its item
# "<base>-<h>", h being the first 8 hex digits of sha256(config dir), whenever
# CLAUDE_CONFIG_DIR is set (even to ~/.claude), and plain "<base>" otherwise.
# Specula's adapter always sets it, so the suffixed item comes first; the plain
# item is only ever the default profile's, so no other profile may fall back to it.
keychain_services() {
  [[ "$(uname -s)" == "Darwin" ]] || return 1
  [[ -z "${CLAUDE_CREDENTIALS:-}" ]] || return 1
  local hash
  hash="$(python3 -c '
import hashlib, sys, unicodedata
print(hashlib.sha256(unicodedata.normalize("NFC", sys.argv[1]).encode()).hexdigest()[:8])
' "${CREDENTIALS%/.credentials.json}")" || return 1
  printf '%s\n' "$KEYCHAIN_SERVICE-$hash"
  if [[ -z "${CLAUDE_CONFIG_DIR:-}" && "$CREDENTIALS" == "$HOME/.claude/.credentials.json" ]]; then
    printf '%s\n' "$KEYCHAIN_SERVICE"
  fi
}

# An existing file always wins, so file-based profiles are unaffected.
credentials_json() {
  if [[ -f "$CREDENTIALS" ]]; then
    cat "$CREDENTIALS"
    return 0
  fi
  local service json
  while IFS= read -r service; do
    if json="$(security find-generic-password -s "$service" -w 2>/dev/null)" && [[ -n "$json" ]]; then
      printf '%s' "$json"
      return 0
    fi
  done < <(keychain_services)
  return 1
}

fetch_usage() {
  local credentials token tried nl=$'\n'
  if ! credentials="$(credentials_json)" || [[ -z "$credentials" ]]; then
    tried="$(keychain_services || true)"
    if [[ -n "$tried" ]]; then
      die "credentials not found at $CREDENTIALS, and no Keychain item named ${tried//$nl/ or } (run: claude /login)"
    fi
    die "credentials not found at $CREDENTIALS"
  fi
  token="$(printf '%s' "$credentials" | python3 -c "
import json, sys
d = json.load(sys.stdin)
token = d.get('claudeAiOauth', d).get('accessToken', '')
if not token:
    sys.exit(1)
print(token)
")" || die "failed to read access token"

  curl -sf "https://api.anthropic.com/api/oauth/usage" \
    -H "Authorization: Bearer $token" \
    -H "anthropic-beta: oauth-2025-04-20" \
    -H "Content-Type: application/json" \
    || die "API request failed (token expired? run: claude login)"
}

check_threshold() {
  python3 -c "
import json, sys
d = json.loads(sys.stdin.read())
threshold = float($1)
over = []
for name, key in [('5h', 'five_hour'), ('7d', 'seven_day'), ('7d_opus', 'seven_day_opus'), ('7d_sonnet', 'seven_day_sonnet')]:
    obj = d.get(key)
    if obj is None:
        continue
    util = obj.get('utilization')
    if util is not None and util > threshold:
        over.append((name, util, obj.get('resets_at', '')))
if over:
    for name, util, reset in over:
        print(f'{name}={util}% resets_at={reset}')
    sys.exit(1)
print('ok')
"
}

case "${1:-}" in
  --check) fetch_usage | check_threshold "${2:-80}" ;;
  *)       fetch_usage ;;
esac

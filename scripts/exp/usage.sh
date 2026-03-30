#!/usr/bin/env bash
#
# Check Claude Max subscription usage via OAuth endpoint.
#
# Usage:
#   bash scripts/exp/usage.sh              # JSON output
#   bash scripts/exp/usage.sh --check 80   # exit 1 if any window > 80%
#
# Exit codes:
#   0  ok (or under threshold in --check mode)
#   1  over threshold (--check mode)
#   2  fetch failed (auth error, network, etc.)

set -euo pipefail

CREDENTIALS="${CLAUDE_CREDENTIALS:-$HOME/.claude/.credentials.json}"

die() { echo "error: $*" >&2; exit 2; }

fetch_usage() {
  [[ -f "$CREDENTIALS" ]] || die "credentials not found at $CREDENTIALS"
  local token
  token="$(python3 -c "
import json, sys
with open('$CREDENTIALS') as f:
    d = json.load(f)
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

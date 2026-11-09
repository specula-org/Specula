#!/usr/bin/env bash
# Fixture quota endpoint: over the 5h threshold while adapters/quota-over exists.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")/../launch/adapters" && pwd)"
if [ -f "$here/quota-over" ]; then
  printf '{"five_hour":{"utilization":99,"resets_at":"2000-01-01T00:00:00Z"}}\n'
else
  printf '{"five_hour":{"utilization":1},"seven_day":{"utilization":1}}\n'
fi

#!/bin/bash
# Run all stage-2 jobs one at a time until every one has results, surviving usage limits.
# Safe to restart at any time: finished runs are skipped, an interrupted run starts over.
#   nohup setsid ./queue.sh >> "$LEDGER_WORK/queue.log" 2>&1 &
cd "$(dirname "$0")"
REPS=${REPS:-1}
for pass in $(seq 1 200); do
  echo "=== pass $pass $(date -Is)"
  python3 run_ledger.py run --reps "$REPS"
  left=$(python3 run_ledger.py plan --reps "$REPS" | grep -c 'todo$')
  echo "=== pass $pass done, $left left $(date -Is)"
  [ "$left" -eq 0 ] && exit 0
  sleep 1800  # a non-limit API failure (overload, crash): wait and try the missing runs again
done
exit 1
